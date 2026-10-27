module

public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofField
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofChoice
import CFSG.RankThree.PartTwo.Sec4.Item413Orders

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements


@[expose] def Gap1117NotActX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
        g * x * g⁻¹ ∉ Subgroup.zpowers x

@[expose] def Gap1117Symmetry : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      g * x * g⁻¹ * x⁻¹ ∈ A → g * x * g⁻¹ * x⁻¹ ∉ Subgroup.closure {c, d} →
        ∃ a' ∈ Subgroup.closure ({g * x * g⁻¹ * x⁻¹, d} : Set G),
          a' ∉ Subgroup.zpowers d ∧ YNotField c L a'

@[expose] def KFact1117Cube : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      ((((∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
                Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
                  (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
              ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
                Nonempty (sec11YA a Y A ≃* Multiplicative (ZMod 3) ×
                  (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
            Nonempty (Sec4.autIn Y A ≃* DihedralGroup 6)) ∨
          ((Sec8.IsZ3LThreePi (sec11YA a Y A) ∨ Sec8.IsZ3PGLThreePi (sec11YA a Y A)) ∧
            Nonempty (Sec4.autIn Y A ≃* Equiv.Perm (Fin 3)))) →
      9 < orderOf x →
        g * x ^ 3 * g⁻¹ ∉ Subgroup.zpowers (x ^ 3)

end Statements

namespace Item1117Proof

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem false_of_card_L32 (h : Sec11Data G A c L a R Y d x s r g) (hx9 : 9 < orderOf x)
    (e : sec11K L a ⧸ aschbacherSolvableCore 3 (sec11K L a) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 1)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := sec11K L a with hK
  set y : K := ⟨x ^ 3, x_cube_mem_sec11K h⟩ with hy
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hq
  obtain ⟨k, hk⟩ := x_pow_eq_one h
  have hyk : y ^ 3 ^ k = 1 := Subtype.ext (by
    simp only [hy, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← pow_mul, mul_comm, pow_mul, hk, one_pow])
  have hq3 : (q y) ^ 3 ≠ 1 := by
    intro h1
    rw [← map_pow, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : (y ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hyk, one_pow]
    have h3 := eq_one_of_mem_theta_of_pow_eq_one h1 h2
    have hx9' : x ^ 9 = 1 := by
      have := congrArg Subtype.val h3
      simp only [hy, SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      rw [← pow_mul] at this
      exact this
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx9')
    omega
  have hqk : (q y) ^ 3 ^ k = 1 := by rw [← map_pow, hyk, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hqk)
  have hj2 : 2 ≤ j := by
    by_contra hj2
    apply hq3
    rw [← orderOf_dvd_iff_pow_eq_one, hj]
    calc 3 ^ j ∣ 3 ^ 1 := pow_dvd_pow 3 (by omega)
      _ = 3 := pow_one 3
  have h9 : 9 ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K) := by
    have h1 : 9 ∣ orderOf (q y) := by
      rw [hj]
      exact (pow_dvd_pow 3 hj2 : 3 ^ 2 ∣ 3 ^ j)
    exact h1.trans (orderOf_dvd_natCard _)
  rw [Nat.card_congr e.toEquiv] at h9
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have h1 := h9.trans (Sec4.card_projSL_dvd 3 (GaloisField 2 1))
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)] at h1
  norm_num [Fin.prod_univ_succ] at h1

theorem false_of_not_field (h119 : Item119) (hND : KFact1117Cube)
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hnf : ¬ KFacts.InducesStdKind Y c .field) (hx9 : 9 < orderOf x) : False := by
  rcases h119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq with
    ⟨hf, -⟩ | h2 | h3 | ⟨-, ⟨e⟩, -⟩
  · exact hnf hf
  · exact hND G A c L a R Y d x s r g h hsc hrs (Or.inl h2) hx9 (conj_pow_three_mem h hsc hrs)
  · exact hND G A c L a R Y d x s r g h hsc hrs (Or.inr h3) hx9 (conj_pow_three_mem h hsc hrs)
  · exact false_of_card_L32 h hx9 e

theorem R_eq_closure_of_mem (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {a' : G}
    (ha'A : a' ∈ A) (ha'cd : a' ∉ Subgroup.closure ({c, d} : Set G)) :
    R = Subgroup.closure {a', x, s} := by
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha'A ha'cd
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  set T := Subgroup.closure ({a', x, s} : Set G) with hT
  have hxT : x ∈ T := Subgroup.subset_closure (by simp)
  have hsT : s ∈ T := Subgroup.subset_closure (by simp)
  have hcT : c ∈ T := Subgroup.zpowers_le.mpr hsT h.c_mem_zpowers_s
  have hAT : A ≤ T := by
    rw [hA', Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact hcT
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.zpowers_le.mpr hxT (d_mem_zpowers_x h)
  apply le_antisymm
  · rw [R_eq_closure h hsc hrs, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact hAT h.a_mem
    · exact hxT
    · exact hcT
  · rw [hT, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact le_R_of_hyp91 h.toHyp91 ha'A
    · exact hxR
    · exact hsR

theorem conj_g_x_cube (h117 : Item117) (h118 : Item118) (h119 : Item119)
    (h82 : Sec8.Item82One) (hND : KFact1117Cube) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    g * x ^ 3 * g⁻¹ = x ^ 3 := by
  have h9 : 9 ≤ orderOf x := Nat.le_of_dvd (orderOf_pos_iff.mpr (isOfFinOrder_of_finite x))
    (nine_dvd_orderOf_x h)
  by_cases hx9 : orderOf x = 9
  · have hx3d : x ^ 3 ∈ Subgroup.zpowers d :=
      mem_zpowers_of_pow_three_eq_one (d_mem_zpowers_x h) (orderOf_d h)
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 3)
        (by rw [← pow_mul, show 3 * 3 = orderOf x by omega, pow_orderOf_eq_one])
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx3d
    rw [← hi, ← conj_zpow, conj_g_d h117 h]
  · by_cases hf : KFacts.InducesStdKind Y c .field
    · exact conj_g_x_cube_of_field h82 h118 h hsc hrs hf
    · exact (false_of_not_field h119 hND h hsc hrs hf (by omega)).elim

end Data

end Item1117Proof

section Main


open Item1117Proof in
theorem rank3II_11_17 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) (h118 : Item118)
    (h119 : Item119) (h82 : Sec8.Item82One) (hNA : Gap1117NotActX) (hNC : Gap1117Symmetry)
    (hND : KFact1117Cube) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g) (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    (∃ a' ∈ A, a' ∉ Subgroup.closure {c, d} ∧
        ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {a', d} ∧ YNotField c L a') ∧
      orderOf x = 9 := by
  have hdA := d_mem_A h
  have hcd : c * d = d * c := commute_of_mem_A h h.mem_A hdA
  have hc3 := pow_three_of_mem_A h h.mem_A
  have hd3 := pow_three_of_mem_A h hdA
  have h9 : 9 ≤ orderOf x := Nat.le_of_dvd (orderOf_pos_iff.mpr (isOfFinOrder_of_finite x))
    (nine_dvd_orderOf_x h)
  have hgx3 := conj_g_x_cube h117 h118 h119 h82 hND h hsc hrs
  set e := g * x * g⁻¹ * x⁻¹ with he_def
  have heA : e ∈ A := commutator_g_x_mem h hsc hrs hgx3
  have hPP := commutator_eq_closure h117 h hsc hrs heA
  have hed3 := pow_three_of_mem_A h heA
  have hedc : e * d = d * e := commute_of_mem_A h heA hdA
  have hed : e ∉ Subgroup.zpowers d := by
    intro hed
    apply hNA G A c L a R Y d x s r g h hsc hrs
    have e1 : g * x * g⁻¹ = e * x := by rw [he_def]; group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.zpowers_le.mpr (d_mem_zpowers_x h) hed)
      (Subgroup.mem_zpowers x)
  have hecd : e ∉ Subgroup.closure ({c, d} : Set G) := by
    intro hecd
    apply false_of_commutator_eq_closure_c_d h45 h113 h117 h hsc hrs
    rw [hPP, closure_pair_eq_of_mem hcd hc3 hd3 hecd hed]
  obtain ⟨a', ha'e, ha'd, hnf⟩ := hNC G A c L a R Y d x s r g h hsc hrs heA hecd
  have hclos : Subgroup.closure ({a', d} : Set G) = Subgroup.closure {e, d} :=
    closure_pair_eq_of_mem hedc hed3 hd3 ha'e ha'd
  have ha'A : a' ∈ A := by
    have hle : Subgroup.closure ({e, d} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact heA
      · exact hdA
    exact hle ha'e
  have ha'cd : a' ∉ Subgroup.closure ({c, d} : Set G) := by
    intro ha'cd
    apply hecd
    rw [← closure_pair_eq_of_mem hcd hc3 hd3 ha'cd ha'd, hclos]
    exact Subgroup.subset_closure (by simp)
  refine ⟨⟨a', ha'A, ha'cd, by rw [hPP, hclos], hnf⟩, ?_⟩
  by_contra hx9
  have hx9' : 9 < orderOf x := lt_of_le_of_ne h9 (Ne.symm hx9)
  obtain ⟨Ye, hYe, hKYe, hnfe⟩ := hnf
  have hstd := h.toSec11Std.change_a h45 h.inf_eq h.closure_eq ha'A ha'cd hYe hKYe
  have hA' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha'A ha'cd
  obtain ⟨a'', Y'', g'', hstd'', ha''A, ha''cd, hg3, hgYW, hgR, hgH, hgc, hnf''⟩ :=
    exists_choice_g_not_field h45 h113 h117 h119 hstd h.inf_eq hA' hnfe
  have hA'' := h.toSec11Std.closure_eq_of_not_mem h.inf_eq h.closure_eq ha''A ha''cd
  have hdata : Sec11Data G A c L a'' R Y'' d x s a'' g'' :=
    { toSec11Std := hstd''
      inf_eq := h.inf_eq
      closure_eq := hA''
      inf_L_eq := h.inf_L_eq
      inf_centralizer_eq := h.inf_centralizer_eq
      R_eq := R_eq_closure_of_mem h hsc hrs ha''A ha''cd
      a_mem_closure := Subgroup.subset_closure (by simp)
      pow_eq_one := hg3
      g_mem := hgYW
      g_mem_normalizer := hgR
      g_not_mem := hgH
      conj_mem := hgc }
  exact false_of_not_field h119 hND hdata hsc rfl hnf'' hx9'

theorem item1117_of (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) (h118 : Item118)
    (h119 : Item119) (h82 : Sec8.Item82One) (hNA : Gap1117NotActX) (hNC : Gap1117Symmetry)
    (hND : KFact1117Cube) : Item1117 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hsc hrs =>
    rank3II_11_17 h45 h113 h117 h118 h119 h82 hNA hNC hND h hsc hrs

end Main

end CFSG.RankThree.PartTwo.Sec11
