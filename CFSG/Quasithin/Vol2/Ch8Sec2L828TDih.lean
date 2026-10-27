module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.L828Dih

variable {G : Type*} [Group G]

private theorem r_involution_828 (ψ : DihedralGroup 5 →* DihedralGroup 5)
    (hψ : ∀ d, ψ (ψ d) = d) (j : ZMod 5) :
    ψ (DihedralGroup.r j) = DihedralGroup.r j ∨ ψ (DihedralGroup.r j) = DihedralGroup.r (-j) := by
  have hsr : ∀ b : ZMod 5, (DihedralGroup.sr b : DihedralGroup 5) ^ 5 ≠ 1 := by decide
  have h5 : (DihedralGroup.r 1 : DihedralGroup 5) ^ 5 = 1 := by decide
  obtain ⟨k, hk⟩ : ∃ k : ZMod 5, ψ (DihedralGroup.r 1) = DihedralGroup.r k := by
    rcases hr : ψ (DihedralGroup.r 1) with k | b
    · exact ⟨k, rfl⟩
    · exfalso
      apply hsr b
      rw [← hr, ← map_pow ψ, h5, map_one]
  have hpow : ∀ n : ℕ, ψ (DihedralGroup.r (n : ZMod 5)) = DihedralGroup.r (k * (n : ZMod 5)) := by
    intro n
    rw [← DihedralGroup.r_one_pow, map_pow, hk, DihedralGroup.r_pow]
  have hj : ∀ i : ZMod 5, ψ (DihedralGroup.r i) = DihedralGroup.r (k * i) := by
    intro i
    have h := hpow i.val
    rwa [ZMod.natCast_zmod_val] at h
  have hkk : k * k = 1 := by
    have h := hψ (DihedralGroup.r 1)
    rw [hk, hj k] at h
    exact DihedralGroup.r.inj h
  have hk1 : ∀ c : ZMod 5, c * c = 1 → c = 1 ∨ c = -1 := by decide
  rcases hk1 k hkk with rfl | rfl
  · left
    rw [hj j, one_mul]
  · right
    rw [hj j, neg_one_mul]

private theorem two_pow_ne_zero_828 (n : ℕ) : (2 : ZMod 5) ^ n ≠ 0 := by
  have key : ∀ x : ZMod 5, x ≠ 0 → x * 2 ≠ 0 := by decide
  induction n with
  | zero => decide
  | succ m ih => rw [pow_succ]; exact key _ ih

theorem exists_five_elt {I P : Subgroup G} [(P.subgroupOf I).Normal] (hP : IsPGroup 2 ↥P)
    (e : ↥I ⧸ P.subgroupOf I ≃* DihedralGroup 5) :
    ∃ y : ↥I, y ^ 5 = 1 ∧ ∃ j : ZMod 5, j ≠ 0 ∧
      e (QuotientGroup.mk y) = DihedralGroup.r j := by
  obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (e.symm (DihedralGroup.r 1))
  have h5 : (QuotientGroup.mk (z ^ 5) : ↥I ⧸ P.subgroupOf I) = 1 := by
    rw [QuotientGroup.mk_pow, hz, ← map_pow e.symm,
      (by decide : (DihedralGroup.r 1 : DihedralGroup 5) ^ 5 = 1), map_one]
  have hmem : ((z ^ 5 : ↥I) : G) ∈ P :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h5)
  obtain ⟨n, hn⟩ := hP ⟨((z ^ 5 : ↥I) : G), hmem⟩
  have hn' : (z ^ 5) ^ (2 ^ n) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hn
    simpa using this
  refine ⟨z ^ (2 ^ n), ?_, (2 : ZMod 5) ^ n, two_pow_ne_zero_828 n, ?_⟩
  · calc (z ^ 2 ^ n) ^ 5 = (z ^ 5) ^ 2 ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := hn'
  · rw [QuotientGroup.mk_pow, map_pow, hz, MulEquiv.apply_symm_apply, DihedralGroup.r_one_pow]
    push_cast
    rfl

theorem dihedral_conj {I P : Subgroup G} [(P.subgroupOf I).Normal]
    (e : ↥I ⧸ P.subgroupOf I ≃* DihedralGroup 5) {t : G}
    (htI : t ∈ Subgroup.normalizer (I : Set G)) (htP : t ∈ Subgroup.normalizer (P : Set G))
    (ht2 : t ^ 2 = 1) {y : ↥I} {j : ZMod 5} (hj : j ≠ 0)
    (hy : e (QuotientGroup.mk y) = DihedralGroup.r j) :
    t * (y : G) * t⁻¹ * (y : G)⁻¹ ∈ P ∨ t * (y : G) * t⁻¹ * (y : G) ∈ P := by
  have ht_mul : t * t = 1 := by rw [← pow_two]; exact ht2
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_mul
  have hcI : ∀ x : G, x ∈ I → t * x * t⁻¹ ∈ I := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htI x).mp hx
  have hcP : ∀ x : G, x ∈ P → t * x * t⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htP x).mp hx
  obtain ⟨c, hc⟩ : ∃ c : ↥I →* ↥I, ∀ x : ↥I, (c x : G) = t * (x : G) * t⁻¹ :=
    ⟨{ toFun := fun x => ⟨t * (x : G) * t⁻¹, hcI _ x.2⟩
       map_one' := Subtype.ext (by simp)
       map_mul' := fun x x' => Subtype.ext (by simp [mul_assoc]) }, fun x => rfl⟩
  have hcc : ∀ x : ↥I, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hc, hc, ht']
    calc t * (t * (x : G) * t) * t = (t * t) * (x : G) * (t * t) := by group
      _ = (x : G) := by rw [ht_mul, one_mul, mul_one]
  have hN : P.subgroupOf I ≤ (P.subgroupOf I).comap c := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hc]
    exact hcP _ (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨α, hα⟩ : ∃ α : ↥I ⧸ P.subgroupOf I →* ↥I ⧸ P.subgroupOf I,
      ∀ x : ↥I, α (QuotientGroup.mk x) = QuotientGroup.mk (c x) :=
    ⟨QuotientGroup.map (P.subgroupOf I) (P.subgroupOf I) c hN, fun x => rfl⟩
  have hαα : ∀ q : ↥I ⧸ P.subgroupOf I, α (α q) = q := by
    intro q
    refine QuotientGroup.induction_on q (fun x => ?_)
    rw [hα, hα, hcc]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : DihedralGroup 5 →* DihedralGroup 5,
      ∀ d, ψ d = e (α (e.symm d)) :=
    ⟨e.toMonoidHom.comp (α.comp e.symm.toMonoidHom), fun d => rfl⟩
  have hψψ : ∀ d, ψ (ψ d) = d := by
    intro d
    rw [hψ, hψ, MulEquiv.symm_apply_apply, hαα, MulEquiv.apply_symm_apply]
  have hsy : e.symm (DihedralGroup.r j) = QuotientGroup.mk y := by
    rw [← hy, MulEquiv.symm_apply_apply]
  have hψr : ψ (DihedralGroup.r j) = e (QuotientGroup.mk (c y)) := by
    rw [hψ, hsy, hα]
  rcases r_involution_828 ψ hψψ j with h | h
  · left
    rw [hψr, ← hy] at h
    have h1 : (QuotientGroup.mk (c y) : ↥I ⧸ P.subgroupOf I) = QuotientGroup.mk y :=
      e.injective h
    have h2 : (QuotientGroup.mk (c y * y⁻¹) : ↥I ⧸ P.subgroupOf I) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1, mul_inv_cancel]
    have h4 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, hc] at h4
  · right
    rw [hψr] at h
    have h1 : (QuotientGroup.mk (c y) : ↥I ⧸ P.subgroupOf I) = (QuotientGroup.mk y)⁻¹ :=
      e.injective (h.trans (by rw [map_inv, hy, DihedralGroup.inv_r]))
    have h2 : (QuotientGroup.mk (c y * y) : ↥I ⧸ P.subgroupOf I) = 1 := by
      rw [QuotientGroup.mk_mul, h1, inv_mul_cancel]
    have h4 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    rwa [Subgroup.coe_mul, hc] at h4

theorem sup_eq_of_dihedral {I P X V : Subgroup G} [(P.subgroupOf I).Normal]
    (e : ↥I ⧸ P.subgroupOf I ≃* DihedralGroup 5) (hXI : X ≤ I) (hVI : V ≤ I)
    (hPXV : P ≤ X ⊔ V) {y : ↥I} {j : ZMod 5} (hj : j ≠ 0)
    (hy : e (QuotientGroup.mk y) = DihedralGroup.r j) (hyX : (y : G) ∈ X)
    {v : ↥I} (hv : (v : G) ∈ V) (hvP : (v : G) ∉ P) (hv2 : (v : G) ^ 2 = 1) :
    X ⊔ V = I := by
  refine le_antisymm (sup_le hXI hVI) (fun x hx => ?_)
  have hyY : (y : G) ∈ X ⊔ V := Subgroup.mem_sup_left hyX
  have hvY : (v : G) ∈ X ⊔ V := Subgroup.mem_sup_right hv
  have hsolve : ∀ a b : ZMod 5, b ≠ 0 → ∃ m : ZMod 5, m * b = a := by decide
  have hsr : ∀ d : DihedralGroup 5, d ≠ 1 → d ^ 2 = 1 → ∃ b : ZMod 5, d = DihedralGroup.sr b := by
    decide
  rcases h : e (QuotientGroup.mk (⟨x, hx⟩ : ↥I)) with a | a
  ·
    obtain ⟨m, hm⟩ := hsolve a j hj
    have hmk : (QuotientGroup.mk (⟨x, hx⟩ : ↥I) : ↥I ⧸ P.subgroupOf I) =
        QuotientGroup.mk (y ^ m.val) := by
      apply e.injective
      rw [h, QuotientGroup.mk_pow, map_pow, hy, DihedralGroup.r_pow, ZMod.natCast_zmod_val,
        mul_comm, hm]
    have hp := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hmk)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at hp
    have hx' : x = (y : G) ^ m.val * (x⁻¹ * (y : G) ^ m.val)⁻¹ := by group
    rw [hx']
    exact mul_mem (pow_mem hyY _) (inv_mem (hPXV hp))
  ·
    have hv2I : v ^ 2 = 1 := Subtype.ext (by simpa using hv2)
    have hvne : e (QuotientGroup.mk v) ≠ 1 := by
      intro h1
      apply hvP
      have h2 : (QuotientGroup.mk v : ↥I ⧸ P.subgroupOf I) = 1 :=
        e.injective (h1.trans (map_one e).symm)
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
    have hvsq : e (QuotientGroup.mk v) ^ 2 = 1 := by
      rw [← map_pow e, ← QuotientGroup.mk_pow, hv2I, QuotientGroup.mk_one, map_one]
    obtain ⟨b, hb⟩ := hsr _ hvne hvsq
    obtain ⟨m, hm⟩ := hsolve (a - b) j hj
    have hmk : (QuotientGroup.mk (⟨x, hx⟩ : ↥I) : ↥I ⧸ P.subgroupOf I) =
        QuotientGroup.mk (v * y ^ m.val) := by
      apply e.injective
      rw [h, QuotientGroup.mk_mul, QuotientGroup.mk_pow, map_mul, map_pow, hb, hy,
        DihedralGroup.r_pow, ZMod.natCast_zmod_val, DihedralGroup.sr_mul_r]
      congr 1
      rw [mul_comm, hm]
      ring
    have hp := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hmk)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at hp
    have hx' : x = (v : G) * (y : G) ^ m.val * (x⁻¹ * ((v : G) * (y : G) ^ m.val))⁻¹ := by
      group
    rw [hx']
    exact mul_mem (mul_mem hvY (pow_mem hyY _)) (inv_mem (hPXV hp))

end CFSG.Quasithin.H13.L828Dih
