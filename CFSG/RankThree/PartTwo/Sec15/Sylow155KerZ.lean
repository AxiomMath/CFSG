module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155Ker
import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement

namespace Sylow155KZ

section Generic

variable {p : ℕ} [Fact p.Prime] {U Q : Type*} [Group U] [Finite U] [Group Q] {f : U →* Q}
  {Z W : Subgroup U}

private theorem mk_mem_center_of_forall {u : U}
    (hu : ∀ v : U, u * v * u⁻¹ * v⁻¹ ∈ pPrimeCore p U) :
    (QuotientGroup.mk u : U ⧸ pPrimeCore p U) ∈ Subgroup.center (U ⧸ pPrimeCore p U) := by
  rw [Subgroup.mem_center_iff]
  intro q
  induction q using QuotientGroup.induction_on with
  | H v =>
    have h1 : QuotientGroup.mk' (pPrimeCore p U) ⁅u, v⁆ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, commutatorElement_def]
      exact hu v
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

private theorem mk_mem_center_of_pow (hZW : ∀ b ∈ oPrimeResidual p U, ∃ z ∈ Z, ∃ w ∈ W, b = z * w)
    (hZ : ∀ z ∈ Z, ∀ u : U, z * u * z⁻¹ * u⁻¹ ∈ pPrimeCore p U) (hZf : ∀ z ∈ Z, f z = 1)
    (hWf : ∀ w ∈ W, f w = 1 → ∀ u : U, w * u * w⁻¹ * u⁻¹ ∈ pPrimeCore p U) {x : U}
    (hx : f x = 1) {b : ℕ} (hxb : x ^ p ^ b = 1) :
    (QuotientGroup.mk x : U ⧸ pPrimeCore p U) ∈ Subgroup.center (U ⧸ pPrimeCore p U) := by
  obtain ⟨z, hz, w, hw, rfl⟩ := hZW x (Subgroup.subset_closure ⟨b, hxb⟩)
  have hfw : f w = 1 := by
    rw [map_mul, hZf z hz, one_mul] at hx
    exact hx
  rw [QuotientGroup.mk_mul]
  exact Subgroup.mul_mem _ (mk_mem_center_of_forall (hZ z hz))
    (mk_mem_center_of_forall (hWf w hw hfw))

private theorem mem_center_of_mem_map_ker
    (hZW : ∀ b ∈ oPrimeResidual p U, ∃ z ∈ Z, ∃ w ∈ W, b = z * w)
    (hZ : ∀ z ∈ Z, ∀ u : U, z * u * z⁻¹ * u⁻¹ ∈ pPrimeCore p U) (hZf : ∀ z ∈ Z, f z = 1)
    (hWf : ∀ w ∈ W, f w = 1 → ∀ u : U, w * u * w⁻¹ * u⁻¹ ∈ pPrimeCore p U)
    {y : U ⧸ pPrimeCore p U} (hy : y ∈ f.ker.map (QuotientGroup.mk' (pPrimeCore p U))) {b : ℕ}
    (hyb : y ^ p ^ b = 1) : y ∈ Subgroup.center (U ⧸ pPrimeCore p U) := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  rw [MonoidHom.mem_ker] at hx
  obtain ⟨a, m, hm, hxo⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p
    (Fact.out : p.Prime).one_lt.ne'
  have hx' : (x ^ m) ^ p ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hxo, pow_orderOf_eq_one]
  have hfx' : f (x ^ m) = 1 := by rw [map_pow, hx, one_pow]
  have hc : QuotientGroup.mk' (pPrimeCore p U) x ^ m ∈ Subgroup.center (U ⧸ pPrimeCore p U) := by
    rw [← map_pow]
    exact mk_mem_center_of_pow hZW hZ hZf hWf hfx' hx'
  have hcop : Nat.Coprime m (orderOf (QuotientGroup.mk' (pPrimeCore p U) x)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hyb)
      (Nat.Coprime.pow_right b ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm).symm)
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hn]
  exact Subgroup.pow_mem _ hc n

private theorem isPGroup_map_ker
    (hZW : ∀ b ∈ oPrimeResidual p U, ∃ z ∈ Z, ∃ w ∈ W, b = z * w)
    (hZ : ∀ z ∈ Z, ∀ u : U, z * u * z⁻¹ * u⁻¹ ∈ pPrimeCore p U) (hZf : ∀ z ∈ Z, f z = 1)
    (hWf : ∀ w ∈ W, f w = 1 → ∀ u : U, w * u * w⁻¹ * u⁻¹ ∈ pPrimeCore p U) :
    IsPGroup p ↥(f.ker.map (QuotientGroup.mk' (pPrimeCore p U))) := by
  set C := f.ker.map (QuotientGroup.mk' (pPrimeCore p U)) with hCdef
  haveI : C.Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective (pPrimeCore p U))
  have hQ : pPrimeCore p ↥C = ⊥ := by
    have h := CFSG.pPrimeCore_map_subtype_le_pPrimeCore_of_normal p C
    rw [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p, le_bot_iff,
      Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at h
    exact h
  haveI := CFSG.GH74.GLS.Stage1.Thm6.Prod.oPrimeResidual_normal p ↥C
  refine Sylow155C3.isPGroup_of_le_center hQ (Sylow155C3.not_dvd_index_oPrimeResidual p ↥C) ?_
  rw [oPrimeResidual, Subgroup.closure_le]
  rintro c ⟨b, hcb⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro d
  have hcb' : (c : U ⧸ pPrimeCore p U) ^ p ^ b = 1 := by
    have h := congrArg Subtype.val hcb
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  have hc := mem_center_of_mem_map_ker hZW hZ hZf hWf c.2 hcb'
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc d)

theorem ker_central_of_central (hZW : ∀ b ∈ oPrimeResidual p U, ∃ z ∈ Z, ∃ w ∈ W, b = z * w)
    (hZ : ∀ z ∈ Z, ∀ u : U, z * u * z⁻¹ * u⁻¹ ∈ pPrimeCore p U) (hZf : ∀ z ∈ Z, f z = 1)
    (hWf : ∀ w ∈ W, f w = 1 → ∀ u : U, w * u * w⁻¹ * u⁻¹ ∈ pPrimeCore p U) {k : U}
    (hk : f k = 1) :
    (∀ u : U, k * u * k⁻¹ * u⁻¹ ∈ pPrimeCore p U) ∧ ∃ m : ℕ, k ^ p ^ m ∈ pPrimeCore p U := by
  have hkC : QuotientGroup.mk' (pPrimeCore p U) k ∈
      f.ker.map (QuotientGroup.mk' (pPrimeCore p U)) :=
    Subgroup.mem_map_of_mem _ hk
  obtain ⟨m, hm⟩ := isPGroup_map_ker hZW hZ hZf hWf ⟨_, hkC⟩
  have hm' : QuotientGroup.mk' (pPrimeCore p U) k ^ p ^ m = 1 := by
    have h := congrArg Subtype.val hm
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
  have hcen := mem_center_of_mem_map_ker hZW hZ hZf hWf hkC hm'
  refine ⟨fun u => ?_, m, ?_⟩
  · have h1 : QuotientGroup.mk' (pPrimeCore p U) ⁅k, u⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hcen _).symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, commutatorElement_def] at h1
    exact h1
  · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm'
    exact hm'

end Generic

variable {G : Type} [Group G] [Finite G]

theorem ker_central_u155_of_central {A M X : Subgroup G} (hBXW : b155 A M X ≤ X ⊔ w155 A M X)
    {Q : Type*} [Group Q] (f : ↥(u155 A M X) →* Q)
    (hXf : ∀ (x : G) (hx : x ∈ X) (hxU : x ∈ u155 A M X), f ⟨x, hxU⟩ = 1)
    (hWf : ∀ (w : G) (hw : w ∈ w155 A M X), f ⟨w, Proof155Wx.w155_le_u155 A M X hw⟩ = 1 →
      ∀ u ∈ u155 A M X, w * u * w⁻¹ * u⁻¹ ∈ pPrimeCoreOf 3 (u155 A M X))
    {k : G} (hk : k ∈ u155 A M X) (hkf : f ⟨k, hk⟩ = 1) :
    (∀ u ∈ u155 A M X, k * u * k⁻¹ * u⁻¹ ∈ pPrimeCoreOf 3 (u155 A M X)) ∧
      ∃ m : ℕ, k ^ 3 ^ m ∈ pPrimeCoreOf 3 (u155 A M X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUC : u155 A M X ≤ centralizerSection X (CFSG.Open.pCoreOf 2 X) := inf_le_right
  have hWX : w155 A M X ≤ Subgroup.normalizer (X : Set G) := fun w hw =>
    (hUC (Proof155Wx.w155_le_u155 A M X hw)).1
  have hmem : ∀ {y : G} (hy : y ∈ u155 A M X), y ∈ pPrimeCoreOf 3 (u155 A M X) →
      (⟨y, hy⟩ : ↥(u155 A M X)) ∈ pPrimeCore 3 ↥(u155 A M X) := by
    intro y hy h
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp h
    have e : y' = ⟨y, hy⟩ := Subtype.ext hyy'
    rw [← e]
    exact hy'
  have hZW : ∀ b ∈ oPrimeResidual 3 ↥(u155 A M X), ∃ z ∈ X.subgroupOf (u155 A M X),
      ∃ w ∈ (w155 A M X).subgroupOf (u155 A M X), b = z * w := by
    intro b hb
    have hbG : (b : G) ∈ b155 A M X := Subgroup.mem_map_of_mem _ hb
    have hmem' : (b : G) ∈ ((X ⊔ w155 A M X : Subgroup G) : Set G) := hBXW hbG
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X (w155 A M X) hWX] at hmem'
    obtain ⟨x, hx, w, hw, hxw⟩ := Set.mem_mul.mp hmem'
    have hwU := Proof155Wx.w155_le_u155 A M X hw
    have hxU : x ∈ u155 A M X := by
      rw [eq_mul_inv_of_mul_eq hxw]
      exact (u155 A M X).mul_mem b.2 ((u155 A M X).inv_mem hwU)
    exact ⟨⟨x, hxU⟩, Subgroup.mem_subgroupOf.mpr hx, ⟨w, hwU⟩, Subgroup.mem_subgroupOf.mpr hw,
      Subtype.ext hxw.symm⟩
  have hZ : ∀ z ∈ X.subgroupOf (u155 A M X), ∀ u : ↥(u155 A M X),
      z * u * z⁻¹ * u⁻¹ ∈ pPrimeCore 3 ↥(u155 A M X) := by
    intro z hz u
    apply Sylow155K.pCoreOf_subgroupOf_le A M X
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨-, -, hu⟩ := hUC u.2
    simpa [commutatorElement_def] using hu z (Subgroup.mem_subgroupOf.mp hz)
  have hZf : ∀ z ∈ X.subgroupOf (u155 A M X), f z = 1 := fun z hz =>
    hXf z (Subgroup.mem_subgroupOf.mp hz) z.2
  have hWf' : ∀ w ∈ (w155 A M X).subgroupOf (u155 A M X), f w = 1 →
      ∀ u : ↥(u155 A M X), w * u * w⁻¹ * u⁻¹ ∈ pPrimeCore 3 ↥(u155 A M X) := by
    intro w hw hfw u
    have h := hWf w (Subgroup.mem_subgroupOf.mp hw) hfw u u.2
    exact hmem ((u155 A M X).mul_mem ((u155 A M X).mul_mem ((u155 A M X).mul_mem w.2 u.2)
      ((u155 A M X).inv_mem w.2)) ((u155 A M X).inv_mem u.2)) h
  obtain ⟨h1, m, h2⟩ := ker_central_of_central hZW hZ hZf hWf' hkf
  refine ⟨fun u hu => ?_, m, ?_⟩
  · exact Subgroup.mem_map_of_mem (u155 A M X).subtype (h1 ⟨u, hu⟩)
  · exact Subgroup.mem_map_of_mem (u155 A M X).subtype h2

end Sylow155KZ

end CFSG.RankThree.PartTwo.Sec15
