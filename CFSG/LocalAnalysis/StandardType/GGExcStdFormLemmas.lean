module

public import CFSG.LocalAnalysis.StandardType.GGExcStdForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Lemmas

theorem latChar_smul_add {N : ℕ} (p : ℕ) (a c : ZMod p) (f₁ f₂ : Fin N → ZMod p)
    (α : Fin N → ℤ) :
    latChar p (a • f₁ + c • f₂) α = a * latChar p f₁ α + c * latChar p f₂ α := by
  simp only [latChar]
  trans ∑ i, (a * ((α i : ZMod p) * f₁ i) + c * ((α i : ZMod p) * f₂ i))
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

section Plane

private noncomputable def latCorootMap {U' : Type} [Group U'] (Δ : UniversalRootDatum U')
    (p : ℕ) : (Fin Δ.rank → ZMod p) →ₗ[ZMod p] (Fin Δ.rank → ZMod p) where
  toFun v := fun i => ∑ j, v j * (Δ.cartan j i : ZMod p)
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    rw [Finset.mul_sum]

private theorem latCorootSpan_eq_range {U' : Type} [Group U'] (Δ : UniversalRootDatum U')
    (p : ℕ) : LatCorootSpan Δ p = Set.range (latCorootMap Δ p) := by
  ext f
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun j => (c j : ZMod p), ?_⟩
    funext i
    rw [hc i]
    rfl
  · rintro ⟨v, rfl⟩
    refine ⟨fun j => (ZMod.intCast_surjective (v j)).choose, ?_⟩
    intro i
    change (∑ j, v j * (Δ.cartan j i : ZMod p)) =
      ∑ j, ((ZMod.intCast_surjective (v j)).choose : ZMod p) * (Δ.cartan j i : ZMod p)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(ZMod.intCast_surjective (v j)).choose_spec]

private theorem latCorootSpan_add_smul {U' : Type} [Group U'] (Δ : UniversalRootDatum U')
    (p : ℕ) (a c : ZMod p) {f₁ f₂ : Fin Δ.rank → ZMod p}
    (h₁ : f₁ ∈ LatCorootSpan Δ p) (h₂ : f₂ ∈ LatCorootSpan Δ p) :
    a • f₁ + c • f₂ ∈ LatCorootSpan Δ p := by
  rw [latCorootSpan_eq_range] at h₁ h₂ ⊢
  obtain ⟨v₁, rfl⟩ := h₁
  obtain ⟨v₂, rfl⟩ := h₂
  refine ⟨a • v₁ + c • v₂, ?_⟩
  rw [map_add, map_smul, map_smul]

end Plane

variable {G : Type} [Group G] {U' : Type} [Group U']

theorem GGStdForm.exists_plane_subgroup {p : ℕ} (hp : p.Prime) {Bs G₀ : Subgroup G}
    (hBs : IsElemAbelian p Bs) {Δ : UniversalRootDatum U'}
    {S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ} {π : Equiv.Perm (Fin Δ.rank)} {f : ℕ}
    (F : GGStdForm p Bs G₀ Δ S π f) (f₁ f₂ : Fin Δ.rank → ZMod p)
    (h1π : ∀ i, f₁ (π i) = f₁ i) (h2π : ∀ i, f₂ (π i) = f₂ i)
    (h1 : f₁ ∈ LatCorootSpan Δ p) (h2 : f₂ ∈ LatCorootSpan Δ p)
    (hind : ∀ a b : ZMod p, a • f₁ + b • f₂ = 0 → a = 0 ∧ b = 0) :
    ∃ E : Subgroup G, E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ e ∈ E, ∃ he : e ∈ Bs, ∃ a c : ZMod p,
        Multiplicative.toAdd (F.coord ⟨e, he⟩) = a • f₁ + c • f₂ ∧ (e ≠ 1 → a ≠ 0 ∨ c ≠ 0) := by
  classical
  let ψ : (ZMod p × ZMod p) →ₗ[ZMod p] (Fin Δ.rank → ZMod p) :=
    { toFun := fun v => v.1 • f₁ + v.2 • f₂
      map_add' := by
        intro v w
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add, smul_eq_mul, add_mul]
        ring
      map_smul' := by
        intro r v
        funext i
        simp only [Pi.smul_apply, Pi.add_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          RingHom.id_apply]
        ring }
  have hψ_inj : Function.Injective ψ := by
    intro v w hvw
    have hzero : ψ (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    obtain ⟨h1', h2'⟩ := hind (v - w).1 (v - w).2 hzero
    have h0 : v - w = 0 := Prod.ext h1' h2'
    exact sub_eq_zero.mp h0
  let W : Submodule (ZMod p) (Fin Δ.rank → ZMod p) := LinearMap.range ψ
  let E₀ : Subgroup Bs := (W.toAddSubgroup.toSubgroup).comap F.coord
  let E : Subgroup G := E₀.map Bs.subtype
  have hcardW : Nat.card W = p ^ 2 := by
    have e : W ≃ (ZMod p × ZMod p) :=
      (Set.equivOfEq (LinearMap.coe_range ψ)).trans (Equiv.ofInjective ψ hψ_inj).symm
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod]
    ring
  have hWle : ∀ w : W, ∃ b : Bs, F.coord b = Multiplicative.ofAdd w.1 := by
    intro w
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp w.2
    have hmem : (v.1 • f₁ + v.2 • f₂) ∈ LatCorootSpan Δ p :=
      latCorootSpan_add_smul Δ p v.1 v.2 h1 h2
    have hfix : ∀ i, (v.1 • f₁ + v.2 • f₂) (π i) = (v.1 • f₁ + v.2 • f₂) i := by
      intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1π i, h2π i]
    obtain ⟨b, hb⟩ := F.coord_surj (v.1 • f₁ + v.2 • f₂) hmem hfix
    refine ⟨b, ?_⟩
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (F.coord b) = w.1
    rw [hb]
    exact hv
  let g : E₀ → W := fun x =>
    ⟨Multiplicative.toAdd (F.coord x.1),
      (Submodule.mem_toAddSubgroup (p := W)).mp
        ((Multiplicative.mem_toSubgroup W.toAddSubgroup (F.coord x.1)).mp
          (Subgroup.mem_comap.mp x.2))⟩
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have h1 : Multiplicative.toAdd (F.coord x.1) = Multiplicative.toAdd (F.coord y.1) :=
      congrArg Subtype.val hxy
    have h2 : F.coord x.1 = F.coord y.1 := Multiplicative.toAdd.injective h1
    have h3 : x.1 = y.1 := F.coord_inj h2
    exact Subtype.ext h3
  have hg_surj : Function.Surjective g := by
    intro w
    obtain ⟨b, hb⟩ := hWle w
    refine ⟨⟨b, Subgroup.mem_comap.mpr ?_⟩, ?_⟩
    · change F.coord b ∈ W.toAddSubgroup.toSubgroup
      rw [hb]
      exact (Multiplicative.mem_toSubgroup W.toAddSubgroup (Multiplicative.ofAdd w.1)).mpr
        ((Submodule.mem_toAddSubgroup (p := W)).mpr (by simpa using w.2))
    · exact Subtype.ext (by
        change Multiplicative.toAdd (F.coord b) = w.1
        simpa using congrArg Multiplicative.toAdd hb)
  have hcardE₀ : Nat.card E₀ = Nat.card W :=
    Nat.card_congr (Equiv.ofBijective g ⟨hg_inj, hg_surj⟩)
  have hcardE : Nat.card E = Nat.card E₀ := Subgroup.card_subtype Bs E₀
  have hcard : Nat.card E = p ^ 2 := by rw [hcardE, hcardE₀, hcardW]
  have hEB : E ≤ Bs := Subgroup.map_subtype_le E₀
  have hEab : IsElemAbelian p E := by
    refine ⟨?_, ?_⟩
    · refine ⟨⟨fun x y => ?_⟩⟩
      exact Subtype.ext (congrArg (fun z : Bs => (z : G))
        (hBs.1.is_comm.comm (⟨x.1, hEB x.2⟩ : Bs) (⟨y.1, hEB y.2⟩ : Bs)))
    · intro x hx
      simpa using hBs.2 x (hEB hx)
  have hEmem : ∀ e ∈ E, ∃ he : e ∈ Bs, ∃ a c : ZMod p,
      Multiplicative.toAdd (F.coord ⟨e, he⟩) = a • f₁ + c • f₂ ∧
        (e ≠ 1 → a ≠ 0 ∨ c ≠ 0) := by
    intro e heE
    obtain ⟨b, hbE₀, hbe⟩ := Subgroup.mem_map.mp heE
    have heB : e ∈ Bs := hbe ▸ b.2
    have hbW : Multiplicative.toAdd (F.coord b) ∈ W :=
      (Submodule.mem_toAddSubgroup (p := W)).mp
        ((Multiplicative.mem_toSubgroup W.toAddSubgroup (F.coord b)).mp
          (Subgroup.mem_comap.mp hbE₀))
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hbW
    refine ⟨heB, v.1, v.2, ?_, ?_⟩
    · have hb_eq : (⟨e, heB⟩ : Bs) = b := Subtype.ext hbe.symm
      rw [hb_eq]
      exact hv.symm
    · intro hne
      by_contra hzero
      simp only [not_or, not_not] at hzero
      have hcoord0 : Multiplicative.toAdd (F.coord b) = 0 := by
        rw [show Multiplicative.toAdd (F.coord b) = v.1 • f₁ + v.2 • f₂ from hv.symm,
          hzero.1, hzero.2, zero_smul, zero_smul, add_zero]
      have hb1 : b = 1 := by
        apply F.coord_inj
        rw [map_one]
        apply Multiplicative.toAdd.injective
        simpa using hcoord0
      exact hne (by
        rw [← hbe, hb1]
        rfl)
  exact ⟨E, hEB, hEab, hcard, hEmem⟩

theorem GGStdForm.card_inf_centralizer_le {p : ℕ} (hp : p.Prime) {Bs G₀ : Subgroup G}
    {Δ : UniversalRootDatum U'} {S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ}
    {π : Equiv.Perm (Fin Δ.rank)} {f : ℕ} (F : GGStdForm p Bs G₀ Δ S π f) (L₁ : Subgroup G)
    (O : Set (Fin Δ.rank → ℤ))
    (hL : ∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L₁ : Set G) ↔
      ∀ α ∈ O, latChar p (Multiplicative.toAdd (F.coord b')) α = 0)
    (hcard : Nat.card {g : Fin Δ.rank → ZMod p //
      (∀ i, g (π i) = g i) ∧ ∀ β ∈ O, latChar p g β = 0} ≤ p ^ 2) :
    Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let g : (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) →
      {g : Fin Δ.rank → ZMod p //
        (∀ i, g (π i) = g i) ∧ ∀ β ∈ O, latChar p g β = 0} :=
    fun b => ⟨Multiplicative.toAdd (F.coord ⟨b.1, b.2.1⟩), F.coord_fixed ⟨b.1, b.2.1⟩,
      (hL ⟨b.1, b.2.1⟩).mp b.2.2⟩
  have hg : Function.Injective g := by
    intro x y hxy
    have h1 : Multiplicative.toAdd (F.coord ⟨x.1, x.2.1⟩) =
        Multiplicative.toAdd (F.coord ⟨y.1, y.2.1⟩) := congrArg Subtype.val hxy
    have h2 : F.coord ⟨x.1, x.2.1⟩ = F.coord ⟨y.1, y.2.1⟩ :=
      Multiplicative.toAdd.injective h1
    have h3 : (⟨x.1, x.2.1⟩ : Bs) = ⟨y.1, y.2.1⟩ := F.coord_inj h2
    exact Subtype.ext (congrArg (fun z : Bs => (z : G)) h3)
  exact le_trans (Nat.card_le_card_of_injective g hg) hcard

end Lemmas

end CFSG.StandardType
