module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldOrders
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSLTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item419Res3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU projSp)
open Matrix

section Types


theorem four_dvd_card_isType419 {K : Type} [Group K] (h : IsType419 K) : 4 ∣ Nat.card K := by
  rcases Res419Two.card_cases h with h6 | hU | ⟨h8, -⟩
  · obtain ⟨e⟩ := h6
    rw [Nat.card_congr e.toEquiv, Res4Three419.card_alternatingGroup_six]
    norm_num
  · obtain ⟨e⟩ := hU
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSU_three_three]
    norm_num
  · exact (pow_dvd_pow 2 (by norm_num : 2 ≤ 8)).trans h8

theorem card_ne_small_isType419 {K : Type} [Group K] (h : IsType419 K) {c : ℕ}
    (hc : c = 12 ∨ c = 24 ∨ c = 60) : Nat.card K ≠ c := by
  intro hK
  rcases Res419Two.card_cases h with h6 | hU | ⟨h8, -⟩
  · obtain ⟨e⟩ := h6
    rw [Nat.card_congr e.toEquiv, Res4Three419.card_alternatingGroup_six] at hK
    omega
  · obtain ⟨e⟩ := hU
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projSU_three_three] at hK
    omega
  · rw [hK] at h8
    have := Nat.le_of_dvd (by omega) h8
    omega

theorem not_isSolvable_isType419 {K : Type} [Group K] (h : IsType419 K) (hs : IsSimpleGroup K)
    (hZ : Subgroup.center K = ⊥) : ¬ Group.IsSolvable K := by
  intro hsol
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := K)).mpr hsol
  have h4 := four_dvd_card_isType419 h
  have htriv : Nat.card K = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
    have ha : a ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      exact fun g => hcomm g a
    have hb : b ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      exact fun g => hcomm g b
    rw [hZ, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  rw [htriv] at h4
  omega

theorem exists_noncommuting_isType419 {K : Type} [Group K] (h : IsType419 K)
    (hZ : Subgroup.center K = ⊥) : ∃ a b : K, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have h4 := four_dvd_card_isType419 h
  have htriv : Nat.card K = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
    have ha : a ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      exact fun g => hcon g a
    have hb : b ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      exact fun g => hcon g b
    rw [hZ, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  rw [htriv] at h4
  omega

end Types

theorem isSolvable_of_normal_sup_cyclic {H : Type} [Group H] (N C : Subgroup H) [N.Normal]
    (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) [IsCyclic C] (hsup : N ⊔ C = ⊤) :
    Group.IsSolvable H := by
  have hNs : Group.IsSolvable N :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hN a a.2 b b.2)
  have hq : IsCyclic (H ⧸ N) := by
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      have hx : x ∈ N ⊔ C := hsup ▸ Subgroup.mem_top x
      obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      refine ⟨⟨c, hc⟩, ?_⟩
      change (QuotientGroup.mk (c : H) : H ⧸ N) = QuotientGroup.mk (n * c)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    exact isCyclic_of_surjective _ hsurj
  have hqs : Group.IsSolvable (H ⧸ N) :=
    Group.isSolvable_of_comm fun a b => (IsCyclic.commGroup (α := H ⧸ N)).mul_comm a b
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])


theorem not_isType419_of_injective_slTwo {E : Type} [Field E] [Finite E] [CharP E 2]
    {K : Type} [Group K] (hK : IsType419 K) (hs : IsSimpleGroup K)
    (hZ : Subgroup.center K = ⊥) (f : K →* SpecialLinearGroup (Fin 2) E)
    (hf : Function.Injective f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : Subgroup.center (SpecialLinearGroup (Fin 2) E) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec14.Item148Res8.center_slTwo_eq_bot
  set φ := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) E)) with hφdef
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφdef, QuotientGroup.ker_mk', hc2]
  set g : K →* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup E := φ.comp f with hgdef
  have hg : Function.Injective g := hφ.comp hf
  set H := g.range with hHdef
  set eKH : K ≃* H := MonoidHom.ofInjective hg with heKH
  have hcardH : Nat.card H = Nat.card K := (Nat.card_congr eKH.toEquiv).symm
  have hsolK : Group.IsSolvable H → False := fun hH =>
    not_isSolvable_isType419 hK hs hZ
      (Group.isSolvable_of_isSolvable_injective (f := eKH.toMonoidHom) eKH.injective)
  have h4 := four_dvd_card_isType419 hK
  have hcommK : (∀ a b : H, a * b = b * a) → False := fun hc => hsolK
    (Group.isSolvable_of_comm hc)
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨n, -, hn⟩ := FiniteField.card E 2
  have hEcard : Nat.card E = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
    hEcard H with hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hzc, -⟩ | ⟨-, ⟨e4⟩⟩ | ⟨-, ⟨e4⟩⟩ |
      ⟨-, ⟨e5⟩⟩ | ⟨m, t, -, -, N, C, hNn, hNe, -, hCcyc, -, -, hsup⟩ | ⟨m, hm, -, ⟨e⟩⟩ |
      ⟨m, hm, -, ⟨e⟩⟩
  · exact hcommK fun a b =>
      (IsElementaryAbelian.toIsMulCommutative (p := 2) (G := H)).is_comm.comm a b
  · exact hcommK fun a b => (IsCyclic.commGroup (α := H)).mul_comm a b
  ·
    have hodd3 : Odd (2 ^ (n : ℕ) - 1) := by
      simpa using odd_two_pow_pow_sub_one (j := 1) hn1 le_rfl
    have hg1 : Nat.gcd (2 ^ (n : ℕ) - 1) 2 = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hodd3)
    rw [hEcard, hg1, Nat.div_one, Nat.div_one] at hz
    have hzodd : Odd z := by
      rcases hz with hz | hz
      · exact Odd.of_dvd_nat hodd3 hz
      · exact Odd.of_dvd_nat (by simpa using odd_two_pow_pow_add_one (j := 1) hn1 le_rfl) hz
    rw [← hcardH, hzc] at h4
    obtain ⟨k, hk⟩ := hzodd
    omega
  · exact card_ne_small_isType419 hK (Or.inl rfl) (by
      rw [← hcardH, Nat.card_congr e4.toEquiv, nat_card_alternatingGroup]
      simp
      decide)
  · exact card_ne_small_isType419 hK (Or.inr (Or.inl rfl)) (by
      rw [← hcardH, Nat.card_congr e4.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
      decide)
  · exact card_ne_small_isType419 hK (Or.inr (Or.inr rfl)) (by
      rw [← hcardH, Nat.card_congr e5.toEquiv, nat_card_alternatingGroup]
      simp
      decide)
  ·
    have : IsCyclic C := hCcyc
    have : IsMulCommutative N := IsElementaryAbelian.toIsMulCommutative (p := 2) (G := N)
    exact hsolK (isSolvable_of_normal_sup_cyclic N C
      (fun a ha b hb => congrArg Subtype.val
        ((IsElementaryAbelian.toIsMulCommutative (p := 2) (G := N)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      hsup)
  ·
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hcard' : Nat.card H = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.RankThree.PartTwo.Sec14.Item148Res8.card_psl2_charTwo, GaloisField.card 2 m hm]
    exact card_ne_sl2_general hK hm1 (hcardH ▸ hcard')
  ·
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hcard' : Nat.card H = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField hm,
        ← pow_mul, mul_comm m 2]
    exact card_ne_sl2_general hK hm1 (hcardH ▸ hcard')

theorem slTwo_central_of_sq_eq_one {E : Type} [Field E] (h2 : (2 : E) ≠ 0)
    (M : SpecialLinearGroup (Fin 2) E) (hM : M * M = 1) :
    M ∈ Subgroup.center (SpecialLinearGroup (Fin 2) E) := by
  have hMM : (M : Matrix (Fin 2) (Fin 2) E) * (M : Matrix (Fin 2) (Fin 2) E) = 1 := by
    have := congrArg (fun X : SpecialLinearGroup (Fin 2) E => (X : Matrix (Fin 2) (Fin 2) E)) hM
    simpa using this
  have hdet : (M : Matrix (Fin 2) (Fin 2) E).det = 1 := M.2
  set a := (M : Matrix (Fin 2) (Fin 2) E) 0 0 with ha
  set b := (M : Matrix (Fin 2) (Fin 2) E) 0 1 with hb
  set c := (M : Matrix (Fin 2) (Fin 2) E) 1 0 with hc
  set d := (M : Matrix (Fin 2) (Fin 2) E) 1 1 with hd
  have e00 : a * a + b * c = 1 := by
    have := congrFun (congrFun hMM 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc, hd] using this
  have e01 : a * b + b * d = 0 := by
    have := congrFun (congrFun hMM 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc, hd] using this
  have e10 : c * a + d * c = 0 := by
    have := congrFun (congrFun hMM 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc, hd] using this
  have e11 : c * b + d * d = 1 := by
    have := congrFun (congrFun hMM 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, ha, hb, hc, hd] using this
  have edet : a * d - b * c = 1 := by
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  rcases eq_or_ne (a + d) 0 with hs | hs
  · exfalso
    have hd' : d = -a := by linear_combination hs
    rw [hd'] at edet
    apply h2
    linear_combination -edet - e00
  · have hb0 : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc0 : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    rw [hb0, hc0] at e00 e11 edet
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0] at e00
      simp at e00
    have had : a = d := by
      have : a * (a - d) = 0 := by linear_combination e00 - edet
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨a, ?_, ?_⟩
    · simp only [Fintype.card_fin]
      linear_combination e00
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, Matrix.diagonal_apply, ha, hb, hc, hd, hb0, hc0, had] <;>
        simp_all

theorem not_isType419_of_injective_slTwo_odd {E : Type} [Field E] [Finite E]
    (h2 : (2 : E) ≠ 0) {K : Type} [Group K] (hK : IsType419 K) (hZ : Subgroup.center K = ⊥)
    (f : K →* SpecialLinearGroup (Fin 2) E) (hf : Function.Injective f) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K := Finite.of_injective f hf
  have h4 := four_dvd_card_isType419 hK
  have h2dvd : 2 ∣ Nat.card K := (show (2 : ℕ) ∣ 4 by norm_num).trans h4
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have hfu : f u * f u = 1 := by rw [← map_mul, ← sq, hu2, map_one]
  have hcen := slTwo_central_of_sq_eq_one h2 (f u) hfu
  have hu_cen : u ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply hf
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hcen (f k))
  rw [hZ, Subgroup.mem_bot] at hu_cen
  rw [hu_cen, orderOf_one] at hu
  omega

theorem not_isType419_of_injective_slTwo_field {E : Type} [Field E] [Finite E]
    {K : Type} [Group K] (hK : IsType419 K) (hs : IsSimpleGroup K)
    (hZ : Subgroup.center K = ⊥) (f : K →* SpecialLinearGroup (Fin 2) E)
    (hf : Function.Injective f) : False := by
  by_cases h2 : (2 : E) = 0
  · haveI : CharP E 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact not_isType419_of_injective_slTwo hK hs hZ f hf
  · exact not_isType419_of_injective_slTwo_odd h2 hK hZ f hf

end CFSG.RankThree.PartTwo.Sec4.Item419Res3
