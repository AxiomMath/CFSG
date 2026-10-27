module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFacts
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

@[expose] def GGSpCentralizerCoreInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 2 ≤ n → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ A : Subgroup (StatedSp n F), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ∃ (β : Type) (S : β → Subgroup (StatedSp n F)),
        (∀ b, S b ≤ Subgroup.centralizer (A : Set (StatedSp n F))) ∧
        (∀ b, ∀ c ∈ Subgroup.centralizer (A : Set (StatedSp n F)), ∀ s ∈ S b,
          c * s * c⁻¹ ∈ S b) ∧
        (∀ b, CFSG.IsQuasisimple (S b)) ∧
        (∃ k, LayerFacts.ggDer (Subgroup.centralizer (A : Set (StatedSp n F))) k ≤ ⨆ b, S b) ∧
        ∀ z ∈ ⨆ b, S b, (∀ y ∈ ⨆ b, S b, z * y = y * z) → z ^ 2 = 1 → z = 1

namespace LayerFacts

section Pairs

variable {L : Type*} [Group L] {G : Type*} [Group G]

@[expose] def ggConjPairs (ψ : L →* G) : Subgroup (G × L) where
  carrier := {q | ∀ u, ψ (q.2 * u * q.2⁻¹) = q.1 * ψ u * q.1⁻¹}
  one_mem' u := by simp
  mul_mem' {a b} ha hb u := by
    have h := ha (b.2 * u * b.2⁻¹)
    rw [hb u] at h
    show ψ (a.2 * b.2 * u * (a.2 * b.2)⁻¹) = a.1 * b.1 * ψ u * (a.1 * b.1)⁻¹
    calc ψ (a.2 * b.2 * u * (a.2 * b.2)⁻¹) = ψ (a.2 * (b.2 * u * b.2⁻¹) * a.2⁻¹) := by
          congr 1
          group
      _ = a.1 * (b.1 * ψ u * b.1⁻¹) * a.1⁻¹ := h
      _ = a.1 * b.1 * ψ u * (a.1 * b.1)⁻¹ := by group
  inv_mem' {a} ha u := by
    have h := ha (a.2⁻¹ * u * a.2)
    have e1 : a.2 * (a.2⁻¹ * u * a.2) * a.2⁻¹ = u := by group
    rw [e1] at h
    show ψ (a.2⁻¹ * u * a.2⁻¹⁻¹) = a.1⁻¹ * ψ u * a.1⁻¹⁻¹
    rw [inv_inv, inv_inv, h]
    group

theorem mem_ggConjPairs {ψ : L →* G} {x : G} {g : L} :
    (x, g) ∈ ggConjPairs ψ ↔ ∀ u, ψ (g * u * g⁻¹) = x * ψ u * x⁻¹ :=
  Iff.rfl

variable (ψ : L →* G) in
@[expose] def ggConjLifts (E : Subgroup G) : Subgroup L :=
  ((E.prod ⊤) ⊓ ggConjPairs ψ).map (MonoidHom.snd G L)

theorem mem_ggConjLifts {ψ : L →* G} {E : Subgroup G} {t : L} :
    t ∈ ggConjLifts ψ E ↔ ∃ e ∈ E, (e, t) ∈ ggConjPairs ψ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, (Subgroup.mem_prod.mp (Subgroup.mem_inf.mp hx).1).1, (Subgroup.mem_inf.mp hx).2⟩
  · rintro ⟨e, he, h⟩
    exact ⟨(e, t), Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨he, Subgroup.mem_top t⟩, h⟩, rfl⟩

theorem mem_center_of_mem_ggConjPairs_one {ψ : L →* G} (hψ : Function.Injective ψ) {g : L}
    (h : ((1 : G), g) ∈ ggConjPairs ψ) : g ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff]
  intro u
  have h1 := h u
  rw [one_mul, inv_one, mul_one] at h1
  have h2 := hψ h1
  calc u * g = g * u * g⁻¹ * g := by rw [h2]
    _ = g * u := by group

end Pairs

section Sp

variable {F : Type} [Field F] {n : ℕ} {G : Type*} [Group G]

theorem ggLayer_sp [Finite F] [CharP F 2] (hcore : GGSpCentralizerCoreInput) (hn : 2 ≤ n)
    {ψ : StatedSp n F →* G} (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsPGroup p E)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (Symplectic.rootDatum n F) ψ e) :
    Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G))))) ∧
      ∀ X : Subgroup G, X ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := F) n).le
  have hZ1 : ∀ g : StatedSp n F, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hinj hg
    rwa [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot, Subgroup.mem_bot] at h
  set A := ggConjLifts ψ E with hA
  have hlift : ∀ e ∈ E, ∃ t, (e, t) ∈ ggConjPairs ψ := by
    intro e he
    obtain ⟨g, ⟨s, rfl⟩, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer hn ψ hker (hdiag e he)
    refine ⟨s⁻¹, fun u => ?_⟩
    have h := Subgroup.mem_centralizer_iff.mp hcg (ψ (s⁻¹ * u * s)) ⟨_, rfl⟩
    have h2 : ψ (s⁻¹ * u * s) * e * ψ s = e * ψ u * ψ s := by
      calc ψ (s⁻¹ * u * s) * e * ψ s = ψ (s⁻¹ * u * s) * (e * ψ s) := by group
        _ = e * ψ s * ψ (s⁻¹ * u * s) := h
        _ = e * ψ (s * (s⁻¹ * u * s)) := by rw [map_mul ψ s]; group
        _ = e * ψ u * ψ s := by rw [show s * (s⁻¹ * u * s) = u * s by group, map_mul]; group
    rw [inv_inv]
    calc ψ (s⁻¹ * u * s) = ψ (s⁻¹ * u * s) * e * ψ s * (ψ s)⁻¹ * e⁻¹ := by group
      _ = e * ψ u * ψ s * (ψ s)⁻¹ * e⁻¹ := by rw [h2]
      _ = e * ψ u * e⁻¹ := by group
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨e, he, hea⟩ := mem_ggConjLifts.mp ha
    obtain ⟨e', he', heb⟩ := mem_ggConjLifts.mp hb
    have h1 := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hea heb)
      ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).mul_mem heb hea))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hcomm e he e' he',
      mul_inv_cancel] at h1
    exact mul_inv_eq_one.mp (hZ1 _ h1)
  have hAp : IsPGroup p A := by
    intro t
    obtain ⟨e, he, het⟩ := mem_ggConjLifts.mp t.2
    obtain ⟨k, hk⟩ := hE ⟨e, he⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hek : e ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 := (ggConjPairs ψ).pow_mem het (p ^ k)
    rw [Prod.pow_mk, hek] at h1
    simpa using hZ1 _ h1
  have hH : ψ.range ⊓ Subgroup.centralizer (E : Set G) =
      (Subgroup.centralizer (A : Set (StatedSp n F))).map ψ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨u, rfl⟩, hu⟩ := Subgroup.mem_inf.mp hx
      refine ⟨u, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_, rfl⟩
      obtain ⟨e, he, het⟩ := mem_ggConjLifts.mp ht
      have h2 : e * ψ u * e⁻¹ = ψ u := by
        rw [Subgroup.mem_centralizer_iff.mp hu e he]
        group
      have h3 := hinj ((het u).trans h2)
      calc t * u = t * u * t⁻¹ * t := by group
        _ = u * t := by rw [h3]
    · rintro _ ⟨u, hu, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
      obtain ⟨t, het⟩ := hlift e he
      have htA : t ∈ A := mem_ggConjLifts.mpr ⟨e, he, het⟩
      have h1 := het u
      have h2 : t * u * t⁻¹ = u := by
        rw [Subgroup.mem_centralizer_iff.mp hu t htA]
        group
      rw [h2] at h1
      calc e * ψ u = e * ψ u * e⁻¹ * e := by group
        _ = ψ u * e := by rw [← h1]
  obtain ⟨β, S, hSC, hSn, hSq, hder, hZ⟩ := hcore F n hn p hp hp2 A hAp hAcomm
  rw [hH]
  refine (ggLayer_of_core ψ hker le_rfl ?_ (ggCommutator_self_le _) S hSC hSn hSq hder hZ).2
  rw [Subgroup.subgroupOf_self]
  infer_instance

end Sp

end LayerFacts

section Tags

theorem ggLayerTags_PSp_of_core (hcore : GGSpCentralizerCoreInput) :
    GGLayerCentreOddTag .PSp ∧ GGLayerPerfectTag .PSp := by
  refine ⟨fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_,
    fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_⟩ <;>
  · obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    rw [← hrange]
    first
    | exact (LayerFacts.ggLayer_sp (F := GaloisField 2 f) hcore hrk hker hp hp2 hE hcomm hdiag).1
    | exact (LayerFacts.ggLayer_sp (F := GaloisField 2 f) hcore hrk hker hp hp2 hE hcomm hdiag).2

theorem ggLayerInputs_of_remaining_sp
    (hPSU : GGLayerCentreOddTag .PSU ∧ GGLayerPerfectTag .PSU)
    (hSp : GGSpCentralizerCoreInput)
    (hPlus : GGLayerCentreOddTag .POmegaPlus ∧ GGLayerPerfectTag .POmegaPlus)
    (hMinus : GGLayerCentreOddTag .POmegaMinus ∧ GGLayerPerfectTag .POmegaMinus)
    (hF4 : GGLayerCentreOddTag .F4 ∧ GGLayerPerfectTag .F4)
    (hE6 : GGLayerCentreOddTag .E6 ∧ GGLayerPerfectTag .E6)
    (hE7 : GGLayerCentreOddTag .E7 ∧ GGLayerPerfectTag .E7)
    (hE8 : GGLayerCentreOddTag .E8 ∧ GGLayerPerfectTag .E8)
    (hTwE6 : GGLayerCentreOddTag .twistedE6 ∧ GGLayerPerfectTag .twistedE6) :
    GGLayerCentreOddInput ∧ GGLayerPerfectInput :=
  ggLayerInputs_of_remaining hPSU (ggLayerTags_PSp_of_core hSp) hPlus hMinus hF4 hE6 hE7 hE8 hTwE6

end Tags

end CFSG.StandardType
