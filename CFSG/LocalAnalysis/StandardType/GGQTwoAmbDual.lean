module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModelBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

namespace GGQTwoAmbModel

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
  {L H : Subgroup G}

theorem eq_zero_of_root_eq_zero (M : GGQTwoAmbModel p Bs x y L H) (hbas : GGQTwoAmbBasis M)
    (hnd : ((M.cartan.det : ℤ) : ZMod p) ≠ 0) {v : M.V} (hv : ∀ k, M.root k v = 0) : v = 0 := by
  classical
  have : Nonempty M.ι := ⟨M.a⟩
  have htop : Submodule.span (ZMod p) (Set.range M.coroot) = ⊤ :=
    hbas.1.span_eq_top_of_card_eq_finrank hbas.2
  have hvmem : v ∈ Submodule.span (ZMod p) (Set.range M.coroot) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod p)).mp hvmem
  let Cp : Matrix M.ι M.ι (ZMod p) := Matrix.of fun i k => (M.cartan i k : ZMod p)
  have hdetCp : Cp.det ≠ 0 := by
    have hmap : Cp = (Int.castRingHom (ZMod p)).mapMatrix M.cartan := rfl
    rw [hmap, ← RingHom.map_det]
    exact hnd
  have hvec : Matrix.mulVec Cp d = 0 := by
    funext k
    have h := hv k
    rw [← hd, map_sum] at h
    simp only [map_smul, smul_eq_mul, M.pairing] at h
    simpa [Matrix.mulVec, dotProduct, Cp, mul_comm] using h
  have hd0 : d = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdetCp hvec
  rw [← hd, hd0]
  simp

theorem exists_fixedLine_b (hp : p = 3) (M : GGQTwoAmbModel p Bs x y L H) (hbas : GGQTwoAmbBasis M)
    (hnd : ((M.cartan.det : ℤ) : ZMod p) ≠ 0) :
    ∃ y' : M.V, y' ≠ 0 ∧ ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.b}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {y'} := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    have : CharP (ZMod p) 3 := by rw [← hp]; infer_instance
    exact QTwoLin.two_ne_zero_of_charP_three
  let Cp : Matrix M.ι M.ι (ZMod p) := Matrix.of fun i k => (M.cartan i k : ZMod p)
  have hdetCp : Cp.det ≠ 0 := by
    have hmap : Cp = (Int.castRingHom (ZMod p)).mapMatrix M.cartan := rfl
    rw [hmap, ← RingHom.map_det]
    exact hnd
  have hunit : IsUnit Cp.det := hdetCp.isUnit
  let s : M.ι → ZMod p := Pi.single M.b 1
  let c : M.ι → ZMod p := Matrix.mulVec Cp⁻¹ s
  let y' : M.V := ∑ j, c j • M.coroot j
  have hroot : ∀ k, M.root k y' = s k := by
    intro k
    have hsum : M.root k y' = ∑ j, c j * (M.cartan k j : ZMod p) := by
      change M.root k (∑ j, c j • M.coroot j) = ∑ j, c j * (M.cartan k j : ZMod p)
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, M.pairing]
    rw [hsum]
    have hmul : Matrix.mulVec Cp c = s := by
      show Matrix.mulVec Cp (Matrix.mulVec Cp⁻¹ s) = s
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Cp hunit, Matrix.one_mulVec]
    have hk := congrFun hmul k
    simpa [Matrix.mulVec, dotProduct, Cp, mul_comm] using hk
  have hy'b : M.root M.b y' = 1 := by
    rw [hroot M.b]
    exact Pi.single_eq_same M.b 1
  have hy'0 : ∀ k, k ≠ M.b → M.root k y' = 0 := by
    intro k hk
    rw [hroot k]
    exact Pi.single_eq_of_ne hk 1
  have hy'ne : y' ≠ 0 := by
    intro h
    have h1 : (1 : ZMod p) = 0 := by rw [← hy'b, h, map_zero]
    exact one_ne_zero h1
  refine ⟨y', hy'ne, fun v : M.V => ?_⟩
  change (∀ g ∈ M.parabL {k | k ≠ M.b}, g v = v) ↔ v ∈ Submodule.span (ZMod p) {y'}
  have hfix_iff : (∀ g ∈ M.parabL {k | k ≠ M.b}, g v = v) ↔
      v ∈ ggFixedSubmodule (p := p) M.model (Subgroup.closure (M.simple '' {k | k ≠ M.b})) := by
    rw [M.parabL_eq_map, mem_ggFixedSubmodule_iff]
    constructor
    · intro h φ hφ
      exact h _ (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩)
    · rintro h g hg
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
      exact h φ hφ
  have hy'fix : y' ∈ ggFixedSubmodule (p := p) M.model
      (Subgroup.closure (M.simple '' {k | k ≠ M.b})) := by
    rw [mem_ggFixedSubmodule_iff]
    intro φ hφ
    refine Subgroup.closure_induction (p := fun φ _ => ggLin (p := p) M.model φ y' = y')
      ?_ ?_ ?_ ?_ hφ
    · rintro t ⟨k, hk, rfl⟩
      rw [M.simple_apply, hy'0 k hk, zero_smul, sub_zero]
    · rw [map_one]; rfl
    · intro a b _ _ ha hb
      rw [map_mul, LinearEquiv.mul_apply, hb, ha]
    · intro a _ ha
      rw [map_inv]
      have h1 : (ggLin (p := p) M.model a)⁻¹ ((ggLin (p := p) M.model a) y') =
          (ggLin (p := p) M.model a)⁻¹ y' :=
        congrArg (fun z => (ggLin (p := p) M.model a)⁻¹ z) ha
      rw [← LinearEquiv.mul_apply, inv_mul_cancel] at h1
      exact h1.symm
  have hle1 : Submodule.span (ZMod p) {y'} ≤ ggFixedSubmodule (p := p) M.model
      (Subgroup.closure (M.simple '' {k | k ≠ M.b})) :=
    Submodule.span_le.mpr (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hy'fix)
  have hle2 : ggFixedSubmodule (p := p) M.model
      (Subgroup.closure (M.simple '' {k | k ≠ M.b})) ≤ Submodule.span (ZMod p) {y'} := by
    intro w hw
    rw [mem_ggFixedSubmodule_iff] at hw
    have hgen : ∀ k, k ≠ M.b → M.root k w = 0 := by
      intro k hk
      have hcne : M.coroot k ≠ 0 := by
        intro hc
        apply h2
        have h2' : M.root k (M.coroot k) = 2 := by
          rw [M.pairing, M.isCartan.1]
          norm_num
        rw [hc, map_zero] at h2'
        exact h2'.symm
      have hgenk : ggLin (p := p) M.model (M.simple k) w = w :=
        hw (M.simple k) (Subgroup.subset_closure ⟨k, hk, rfl⟩)
      rw [M.simple_apply, sub_eq_self] at hgenk
      exact (smul_eq_zero.mp hgenk).resolve_right hcne
    have hw0 : w - M.root M.b w • y' = 0 := by
      apply eq_zero_of_root_eq_zero M hbas hnd
      intro k
      by_cases hk : k = M.b
      · subst hk
        rw [map_sub, map_smul, hy'b, smul_eq_mul, mul_one]
        exact sub_self _
      · rw [map_sub, map_smul, hgen k hk, hy'0 k hk, smul_zero]
        exact sub_self 0
    rw [sub_eq_zero.mp hw0]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y')
  rw [hfix_iff, le_antisymm hle2 hle1]

end GGQTwoAmbModel

end CFSG.StandardType

end
