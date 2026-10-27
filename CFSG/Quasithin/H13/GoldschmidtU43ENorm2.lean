module

public import CFSG.Quasithin.H13.GoldschmidtU43ENorm1
public import CFSG.Quasithin.H13.GoldschmidtU43EQGen
public import CFSG.CharacterTheory.Semidihedral.Local.ProperSubgroupFormsSupport

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem u43_eq_one_of_odd_dvd_eight {n : ℕ} (hodd : Odd n) (hdvd : n ∣ 8) : n = 1 := by
  have hmem : n ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact h
  all_goals (rw [h] at hodd; exact absurd hodd (by decide))

theorem u43_center_dihedral_four : ∀ a : DihedralGroup 4, (∀ b : DihedralGroup 4, a * b = b * a) →
    a = 1 ∨ a = DihedralGroup.r 2 := by
  decide

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

omit [Finite G] in
theorem orderOf_v : orderOf S.v = 4 := by
  have hz2 : zK z * zK z = 1 := zK_mul_zK S.hyp
  have h4 : S.v ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num]
    calc S.v ^ 4 = (S.v * S.v) * (S.v * S.v) := u43_pow_four S.v
      _ = 1 := by rw [S.vv, hz2]
  have h2 : ¬ S.v ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, S.vv]
    exact zK_ne_one S.hyp
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := S.v) h2 h4
  simpa using this

theorem u_not_mem_zpowers_v : S.u ∉ Subgroup.zpowers S.v := by
  intro hmem
  have hz2 : zK z * zK z = 1 := zK_mul_zK S.hyp
  have h4 : S.v ^ 4 = 1 := by
    calc S.v ^ 4 = (S.v * S.v) * (S.v * S.v) := u43_pow_four S.v
      _ = 1 := by rw [S.vv, hz2]
  have hzi : (zK z)⁻¹ = zK z := inv_eq_of_mul_eq_one_right hz2
  rcases u43_mem_zpowers_of_pow_four h4 hmem with h | h | h | h
  · exact S.u_ne_one (by rw [h]; rfl)
  · have := S.uu
    rw [h, S.vv] at this
    exact zK_ne_one S.hyp this
  · apply S.u_ne_z
    rw [h, S.vv]
    rfl
  · have := S.uu
    rw [h] at this
    have e : S.v⁻¹ * S.v⁻¹ = zK z := by
      calc S.v⁻¹ * S.v⁻¹ = (S.v * S.v)⁻¹ := by group
        _ = zK z := by rw [S.vv, hzi]
    rw [e] at this
    exact zK_ne_one S.hyp this

omit [Finite G] in
theorem u_conj_v : S.u * S.v * S.u⁻¹ = S.v⁻¹ := by
  have h := S.jw.r13
  rw [S.ui] at h ⊢
  exact h

abbrev Dg : Subgroup G := Subgroup.closure ({(S.v : G), (S.u : G)} : Set G)

theorem exists_dihedral_Dg : ∃ e : DihedralGroup 4 ≃* S.Dg, (e (DihedralGroup.r 1) : G) = S.v ∧
    (e (DihedralGroup.sr 0) : G) = S.u := by
  set x : G := (S.v : G) with hx
  set y : G := (S.u : G) with hy
  have hxD : x ∈ S.Dg := Subgroup.subset_closure (Or.inl rfl)
  have hyD : y ∈ S.Dg := Subgroup.subset_closure (Or.inr rfl)
  have hgen : Subgroup.closure ({⟨x, hxD⟩, ⟨y, hyD⟩} : Set S.Dg) = ⊤ := by
    convert Subgroup.closure_closure_coe_preimage (k := ({x, y} : Set G)) using 2
    ext g
    simp [Subtype.ext_iff]
  have hord : orderOf (⟨x, hxD⟩ : S.Dg) = 4 := by
    have h := Subgroup.orderOf_mk x hxD
    have h4 : orderOf x = 4 := (Subgroup.orderOf_coe S.v).trans S.orderOf_v
    omega
  have hnot : (⟨y, hyD⟩ : S.Dg) ∉ Subgroup.zpowers (⟨x, hxD⟩ : S.Dg) := by
    intro hmem
    apply S.u_not_mem_zpowers_v
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hy2 : (⟨y, hyD⟩ : S.Dg) ^ 2 = 1 := Subtype.ext (by
    have := congrArg Subtype.val S.uu
    simpa [pow_two] using this)
  have hyx : (⟨y, hyD⟩ : S.Dg) * ⟨x, hxD⟩ * (⟨y, hyD⟩ : S.Dg)⁻¹ = (⟨x, hxD⟩ : S.Dg)⁻¹ :=
    Subtype.ext (by simpa using congrArg Subtype.val S.u_conj_v)
  obtain ⟨e, he1, he2⟩ := CFSG.Semidihedral.Local.dihedral_normal_form hgen hord hnot hy2 hyx
  exact ⟨e, by rw [he1], by rw [he2]⟩

theorem card_Dg : Nat.card S.Dg = 8 := by
  obtain ⟨e, -, -⟩ := S.exists_dihedral_Dg
  rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

omit [Finite G] in
theorem Dg_le_Hz : S.Dg ≤ Hz z := by
  rw [Dg, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact (S.v : ↥(Hz z)).2
  · exact (S.u : ↥(Hz z)).2

theorem Dg_le_Ng : S.Dg ≤ S.Ng := by
  rw [Dg, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact S.v_mem_Ng
  · exact S.u_mem_Ng

omit [Finite G] in
theorem z_mem_Dg : z ∈ S.Dg := by
  have hv : (S.v : G) ∈ S.Dg := Subgroup.subset_closure (Or.inl rfl)
  have := mul_mem hv hv
  rwa [S.v_sq] at this

omit [Finite G] in
theorem u_mem_Dg : (S.u : G) ∈ S.Dg := Subgroup.subset_closure (Or.inr rfl)

omit [Finite G] in
theorem v_mem_Dg : (S.v : G) ∈ S.Dg := Subgroup.subset_closure (Or.inl rfl)

theorem Dg_inf_Mg {x : G} (hD : x ∈ S.Dg) (hM : x ∈ S.Mg) : x = 1 := by
  have hdvd : orderOf x ∣ 8 := by
    have := orderOf_dvd_natCard (⟨x, hD⟩ : S.Dg)
    rwa [Subgroup.orderOf_mk, S.card_Dg] at this
  exact orderOf_eq_one_iff.mp
    (u43_eq_one_of_odd_dvd_eight ((S.mem_Mg).1 hM).2 hdvd)

theorem center_Dg {d : G} (hd : d ∈ S.Dg) (hc : ∀ d' ∈ S.Dg, d * d' = d' * d) : d = 1 ∨ d = z := by
  obtain ⟨e, he1, -⟩ := S.exists_dihedral_Dg
  obtain ⟨a, ha⟩ := e.surjective ⟨d, hd⟩
  have hca : ∀ b : DihedralGroup 4, a * b = b * a := by
    intro b
    apply e.injective
    apply Subtype.ext
    have := hc (e b) (e b).2
    rw [map_mul, map_mul]
    simpa [ha] using this
  have hr2 : e (DihedralGroup.r 2) = ⟨z, S.z_mem_Dg⟩ := by
    have : (DihedralGroup.r 2 : DihedralGroup 4) = DihedralGroup.r 1 * DihedralGroup.r 1 := by
      decide
    rw [this, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, he1, S.v_sq]
  rcases u43_center_dihedral_four a hca with h | h
  · left
    have : e a = 1 := by rw [h, map_one]
    rw [ha] at this
    exact congrArg Subtype.val this
  · right
    rw [h, hr2] at ha
    exact (congrArg Subtype.val ha).symm

end JWSetup

end CFSG.Quasithin.H13.U43
