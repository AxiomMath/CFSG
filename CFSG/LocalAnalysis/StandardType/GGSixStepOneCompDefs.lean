module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneNine
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoDefs
public import CFSG.LieType.CurtisTits.Recognition

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open scoped commutatorElement

section Layer

variable {G : Type} [Group G]

theorem le_largeEvenLayer {K H : Subgroup G} (hK : IsComponentOf K H) : K ≤ LargeEvenLayer H :=
  le_sSup hK

theorem largeEvenLayer_le_normalizer [Finite G] {K H : Subgroup G} (hK : IsComponentOf K H) :
    LargeEvenLayer H ≤ Subgroup.normalizer (K : Set G) := by
  refine sSup_le fun K' hK' => ?_
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK' hK with h | h
  · rw [h]
    exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
      (Subgroup.centralizer_le_normalizer _)

theorem ggCommutatorElement_mem_left {K : Subgroup G} {k g : G} (hk : k ∈ K)
    (hg : g ∈ Subgroup.normalizer (K : Set G)) : ⁅k, g⁆ ∈ K := by
  rw [commutatorElement_def]
  have h1 : g * k⁻¹ * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg _).mp (K.inv_mem hk)
  have := K.mul_mem hk h1
  simpa [mul_assoc] using this

theorem ggCommutatorElement_mem_right {N : Subgroup G} {k n : G} (hn : n ∈ N)
    (hk : k ∈ Subgroup.normalizer (N : Set G)) : ⁅k, n⁆ ∈ N := by
  rw [commutatorElement_def]
  have h1 : k * n * k⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hk _).mp hn
  exact N.mul_mem h1 (N.inv_mem hn)

theorem ggCommutator_eq_bot_of_abelian {K N : Subgroup G} (hK : CFSG.Assembly.IsQuasisimple ↥K)
    (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hNK : N ≤ Subgroup.normalizer (K : Set G)) :
    ⁅K, N⁆ = ⊥ := by
  have hle : ⁅K, N⁆ ≤ K ⊓ N := Subgroup.commutator_le.mpr fun k hk n hn =>
    Subgroup.mem_inf.mpr ⟨ggCommutatorElement_mem_left hk (hNK hn),
      ggCommutatorElement_mem_right hn (hKN hk)⟩
  set A : Subgroup ↥K := (K ⊓ N).subgroupOf K with hA
  have hAn : A.Normal := by
    refine ⟨fun a ha k => ?_⟩
    rw [hA, Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨haK, haN⟩ := Subgroup.mem_inf.mp ha
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem k.2 haK) (K.inv_mem k.2)
    · exact (Subgroup.mem_normalizer_iff.mp (hKN k.2) _).mp haN
  have hnat := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hK
  have hcen : A ≤ Subgroup.center ↥K := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hnat A with h | h
    · exact h
    · exfalso
      have hKab : ∀ a b : ↥K, a * b = b * a := by
        intro a b
        have ha : (a : G) ∈ N := by
          have : a ∈ A := h ▸ Subgroup.mem_top a
          exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2
        have hb : (b : G) ∈ N := by
          have : b ∈ A := h ▸ Subgroup.mem_top b
          exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp this)).2
        exact Subtype.ext (hN _ ha _ hb)
      obtain ⟨⟨hperf⟩, hsimple, a, b, hab⟩ := hnat
      apply hab
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hKab a b]
  have hKN1 : ⁅⁅K, N⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hcA : (⟨c, (hle hc).1⟩ : ↥K) ∈ A := by
      rw [hA, Subgroup.mem_subgroupOf]
      exact hle hc
    have := Subgroup.mem_center_iff.mp (hcen hcA) ⟨k, hk⟩
    exact (congrArg Subtype.val this)
  have hKN2 : ⁅⁅N, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm N K]; exact hKN1
  have h3 : ⁅⁅K, K⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hKN1 hKN2
  rwa [commutator_self_eq_of_commutator_eq_top hK.1] at h3

theorem ggMem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) :
      Set G) := by
  apply mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hH, map_conj_eq_of_mem_normalizer hK]

theorem ggLe_center_or_eq_of_normalized {K X : Subgroup G} (hK : CFSG.Assembly.IsQuasisimple ↥K)
    (hXK : X ≤ K) (hKX : K ≤ Subgroup.normalizer (X : Set G)) :
    X ≤ Subgroup.centralizer (K : Set G) ∨ X = K := by
  have hnat := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hK
  have hn : (X.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hnat (X.subgroupOf K) with
    h | h
  · left
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hc := Subgroup.mem_center_iff.mp (h (Subgroup.mem_subgroupOf.mpr ha :
      (⟨a, hXK ha⟩ : ↥K) ∈ X.subgroupOf K)) ⟨k, hk⟩
    exact (congrArg Subtype.val hc)
  · right
    refine le_antisymm hXK fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ X.subgroupOf K := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

abbrev ggCenterOf (X : Subgroup G) : Subgroup G := (Subgroup.center ↥X).map X.subtype

theorem ggCenterOf_comm (X : Subgroup G) :
    ∀ a ∈ ggCenterOf X, ∀ b ∈ ggCenterOf X, a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, -, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha b).symm

theorem ggConj_mem_centerOf {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    {x : G} (hx : x ∈ ggCenterOf X) : g * x * g⁻¹ ∈ ggCenterOf X := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hgz : g * (z : G) * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hg _).mp z.2
  rw [SetLike.mem_coe] at hz
  refine ⟨⟨_, hgz⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro w
  have hw : g⁻¹ * (w : G) * g ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) (w : G)).mp w.2
    simpa using this
  have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨_, hw⟩)
  apply Subtype.ext
  simp only [Subgroup.coe_mul] at hc ⊢
  calc (w : G) * (g * z * g⁻¹) = g * ((g⁻¹ * w * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * w := by group

theorem normalizer_le_normalizer_ggCenterOf (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (ggCenterOf X : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨ggConj_mem_centerOf hg, fun hx => ?_⟩
  have := ggConj_mem_centerOf (Subgroup.inv_mem _ hg) hx
  simpa [mul_assoc] using this

theorem ggCenterOf_le_centralizer_layer [Finite G] {H X : Subgroup G}
    (hXE : X ≤ LargeEvenLayer H) (hEX : LargeEvenLayer H ≤ Subgroup.normalizer (X : Set G)) :
    ggCenterOf X ≤ Subgroup.centralizer (LargeEvenLayer H : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  refine sSup_le fun K hK => ?_
  have hc := ggCommutator_eq_bot_of_abelian hK.2.2 (ggCenterOf_comm X)
    ((le_largeEvenLayer hK).trans (hEX.trans (normalizer_le_normalizer_ggCenterOf X)))
    (((Subgroup.map_subtype_le _).trans hXE).trans (largeEvenLayer_le_normalizer hK))
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc

theorem odd_card_center_of_le_layer [Finite G] {H X : Subgroup G}
    (hXE : X ≤ LargeEvenLayer H) (hEX : LargeEvenLayer H ≤ Subgroup.normalizer (X : Set G))
    (hodd : Odd (Nat.card (Subgroup.center ↥(LargeEvenLayer H)))) :
    Odd (Nat.card (Subgroup.center ↥X)) := by
  have hle : ggCenterOf X ≤ ggCenterOf (LargeEvenLayer H) := by
    intro z hz
    have hzE : z ∈ LargeEvenLayer H := hXE ((Subgroup.map_subtype_le _) hz)
    refine ⟨⟨z, hzE⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (ggCenterOf_le_centralizer_layer hXE hEX hz) w w.2
  have hcard := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective X.subtype_injective,
    Subgroup.card_map_of_injective (LargeEvenLayer H).subtype_injective] at hcard
  exact Odd.of_dvd_nat hodd hcard

end Layer

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.x_mem_d (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) : x ∈ D :=
  h.stdSub.1.2.2.2.1

theorem GGSixCtxV2.j_isComponentOf_centralizer (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    IsComponentOf J (Subgroup.centralizer (D : Set G)) := by
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := h.sstar.2.2.2.1
  have hDx : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.x_mem_d)
  have h1 : IsSubnormal (L ⊓ Subgroup.centralizer (D : Set G))
      (Subgroup.centralizer (D : Set G)) := by
    have := ggIsSubnormal_inf hL.2.1 (Subgroup.centralizer (D : Set G))
    rwa [inf_eq_right.mpr hDx] at this
  exact ⟨h.j_comp.1.trans inf_le_right, ggIsSubnormal_trans h.j_comp.2.1 h1, h.j_comp.2.2⟩

theorem GGSixCtxV2.j_isComponentOf_inf (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    IsComponentOf J (ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G)) := by
  have hJ := h.j_isComponentOf_centralizer
  exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hJ (le_inf h.le_ggG0 hJ.1)
    inf_le_right

end Ctx

section Kd

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
  {d : G}

theorem ggKd_le_layer (hJ : J ≤ LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {d})) :
    ggKd p B x L D J d ≤ LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) := by
  refine iSup₂_le fun a ha => ?_
  rintro _ ⟨j, hj, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha (hJ hj)) (Subgroup.inv_mem _ ha)

theorem layer_le_normalizer_ggKd :
    LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) ≤
      Subgroup.normalizer (ggKd p B x L D J d : Set G) := by
  intro b hb
  have key : ∀ c ∈ LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}),
      (ggKd p B x L D J d).map (MulAut.conj c).toMonoidHom ≤ ggKd p B x L D J d := by
    intro c hc
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun a ha => ?_
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map]
    have hca : (MulAut.conj c).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
        (MulAut.conj (c * a)).toMonoidHom := by
      ext g
      simp [MulAut.conj_apply, mul_assoc]
    rw [hca]
    exact le_iSup₂ (f := fun (a : G)
      (_ : a ∈ LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {d})) =>
        J.map (MulAut.conj a).toMonoidHom) (c * a) (Subgroup.mul_mem _ hc ha)
  exact CFSG.LocalAnalysis.ComponentInitial.mem_normalizer_of_conjSub_le (key b hb)
    (key b⁻¹ (Subgroup.inv_mem _ hb))

end Kd

end CFSG.StandardType
