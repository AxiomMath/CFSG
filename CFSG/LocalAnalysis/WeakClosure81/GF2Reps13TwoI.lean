module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoD2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoT

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {t : MulAut W} {P : Subgroup (MulAut W)}

private theorem w16g_conj_pow_inv {A : Type*} [Group A] {u x : A}
    (hu : u * x * u⁻¹ = x⁻¹) (m : ℕ) : u * x ^ m * u⁻¹ = (x ^ m)⁻¹ := by
  have hconj : MulAut.conj u x = x⁻¹ := by rw [MulAut.conj_apply, hu]
  calc u * x ^ m * u⁻¹ = MulAut.conj u (x ^ m) := (MulAut.conj_apply u (x ^ m)).symm
    _ = (MulAut.conj u x) ^ m := map_pow (MulAut.conj u) x m
    _ = (x⁻¹) ^ m := by rw [hconj]
    _ = (x ^ m)⁻¹ := inv_pow x m

private theorem w16g_conj_conj_eq_self (htt : t * t = 1) (x : MulAut W) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  rw [htinv]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [htt]; group

private theorem w16g_conj_mem_central (h : Cfg132 t P) {c : MulAut W}
    (hcP : c ∈ P) (hcC : ∀ y ∈ P, y * c = c * y) :
    ∀ y ∈ P, y * (t * c * t⁻¹) = (t * c * t⁻¹) * y := by
  intro y hy
  have htt : t * t = 1 := by
    have h2 := pow_orderOf_eq_one t
    rwa [h.ht, pow_two] at h2
  have hy'P : t * y * t⁻¹ ∈ P := h.hn y hy
  have hcomm : MulAut.conj t y * c = c * MulAut.conj t y := by
    rw [MulAut.conj_apply]
    exact hcC (t * y * t⁻¹) hy'P
  have hconj : MulAut.conj t (MulAut.conj t y) = y := by
    rw [MulAut.conj_apply, MulAut.conj_apply]
    exact w16g_conj_conj_eq_self htt y
  have hmul := congrArg (MulAut.conj t) hcomm
  simp only [map_mul] at hmul
  rw [hconj, MulAut.conj_apply] at hmul
  exact hmul

theorem w16h_central_dichotomy (h : Cfg132 t P) :
    (∃ z : MulAut W, z ∈ P ∧ orderOf z = 3 ∧ (∀ y ∈ P, y * z = z * y) ∧ t * z * t⁻¹ = z⁻¹) ∨
      (∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z) := by
  classical
  by_cases hZ : ∀ z ∈ P, (∀ y ∈ P, y * z = z * y) → t * z * t⁻¹ = z
  · exact Or.inr hZ
  · push Not at hZ
    obtain ⟨c, hcP, hcC, hcne⟩ := hZ
    have htt : t * t = 1 := by
      have h2 := pow_orderOf_eq_one t
      rwa [h.ht, pow_two] at h2
    have hc'P : t * c * t⁻¹ ∈ P := h.hn c hcP
    have hc'C : ∀ y ∈ P, y * (t * c * t⁻¹) = (t * c * t⁻¹) * y :=
      w16g_conj_mem_central h hcP hcC
    let y : MulAut W := c⁻¹ * (t * c * t⁻¹)
    have hyP : y ∈ P := P.mul_mem (P.inv_mem hcP) hc'P
    have hyC : ∀ a ∈ P, a * y = y * a := by
      intro a ha
      have hca : Commute a c := hcC a ha
      have hca' : Commute a (t * c * t⁻¹) := hc'C a ha
      exact ((hca.inv_right).mul_right hca').eq
    have hyinv : t * y * t⁻¹ = y⁻¹ := by
      have hconj2 : MulAut.conj t (MulAut.conj t c) = c := by
        rw [MulAut.conj_apply, MulAut.conj_apply]
        exact w16g_conj_conj_eq_self htt c
      have hy_eq : y = c⁻¹ * MulAut.conj t c := by
        rw [MulAut.conj_apply]
      rw [show t * y * t⁻¹ = MulAut.conj t y from (MulAut.conj_apply t y).symm]
      rw [hy_eq, map_mul, map_inv, hconj2, mul_inv_rev, inv_inv]
    have hyne : y ≠ 1 := by
      intro hy1
      apply hcne
      calc t * c * t⁻¹ = c * (c⁻¹ * (t * c * t⁻¹)) := by group
        _ = c * y := rfl
        _ = c * 1 := by rw [hy1]
        _ = c := by simp
    obtain ⟨k, hk⟩ := h.hP.exists_orderOf_eq_pow (⟨y, hyP⟩ : ↥P)
    have hyord : orderOf y = 3 ^ k := by
      rw [← Subgroup.orderOf_mk y hyP]
      exact hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hyord
      exact hyne (orderOf_eq_one_iff.mp hyord)
    have hdvd : 3 ∣ orderOf y := by
      rw [hyord]
      exact dvd_pow_self 3 hk0
    have hyne0 : orderOf y ≠ 0 := by
      rw [hyord]
      exact pow_ne_zero k (by norm_num)
    let z : MulAut W := y ^ (orderOf y / 3)
    have hzP : z ∈ P := P.pow_mem hyP _
    have hz3 : orderOf z = 3 := by
      dsimp only [z]
      exact orderOf_pow_orderOf_div hyne0 hdvd
    have hzC : ∀ a ∈ P, a * z = z * a := by
      intro a ha
      have hcomm : Commute a y := hyC a ha
      exact (hcomm.pow_right (orderOf y / 3)).eq
    have hzinv : t * z * t⁻¹ = z⁻¹ := by
      dsimp only [z]
      exact w16g_conj_pow_inv hyinv _
    exact Or.inl ⟨z, hzP, hz3, hzC, hzinv⟩

private theorem w16g_minLe_mono {m n : ℕ} (hmn : m ≤ n) (h : W4Lem13_2MinLe n) :
    W4Lem13_2MinLe m := by
  intro W instCG instFin hW t ht hrk p P hp hP hne hn hc hcard hmin
  exact h W hW t ht hrk p P hp hP hne hn hc (le_trans hcard hmn) hmin

private theorem w16g_shapeLe_mono {m n : ℕ} (hmn : m ≤ n) (h : W4Lem13_2ShapeLe n) :
    W4Lem13_2ShapeLe m := by
  intro W instCG instFin hW t ht hrk p P hp hP hne hn hc hcard
  exact h W hW t ht hrk p P hp hP hne hn hc (le_trans hcard hmn)

theorem w16h_prime_three (n : ℕ) (hIH : W4Lem13_2ShapeLe n)
    (hMin : 27 < Nat.card P → W4Lem13_2MinLe 27) (h131 : W4Lem13_1) (h : Cfg132 t P)
    (hmin : MinFaith132 t P) (hcard : Nat.card P ≤ n + 1) : Concl132Min t P := by
  classical
  by_cases hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x
  · rcases w16h_abelian h hab with hcyc | habel
    · exact Or.inl hcyc
    · exact Or.inr (Or.inl habel)
  · have hnab : ¬ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := hab
    have hpos : 0 < Nat.card P := Nat.card_pos
    have hIH' : W4Lem13_2ShapeLe (Nat.card P - 1) :=
      w16g_shapeLe_mono (by omega) hIH
    by_cases hdec : ∃ U U' : Subgroup W,
        StableUnder (P ⊔ Subgroup.zpowers t) U ∧
        StableUnder (P ⊔ Subgroup.zpowers t) U' ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = ⊤ ∧
        U ≠ ⊤ ∧ U' ≠ ⊤
    · obtain ⟨U, U', hU, hU', hd, hs, hU1, hU2⟩ := hdec
      have hdec' := w16h_decomp hIH' hMin h131 h hmin hnab hU hU' hd hs hU1 hU2
      exact Or.inr (Or.inr (Or.inr ⟨Or.inl hdec'.1, hdec'.2.1, hdec'.2.2⟩))
    · have hind : NoDecomp132 t P := by
        intro U U' hU hU' hd hs
        by_contra hcon
        push Not at hcon
        exact hdec ⟨U, U', hU, hU', hd, hs, hcon.1, hcon.2⟩
      rcases w16h_central_dichotomy h with ⟨z, hzP, hz3, hzc, hzi⟩ | hZ
      · have hinv := w16h_inverted h hind hnab hzP hz3 hzc hzi
        exact Or.inr (Or.inr (Or.inr ⟨Or.inr hinv.1, hinv.2.1, hinv.2.2⟩))
      · have hcen := w16h_central h hind hZ
        exact Or.inr (Or.inr (Or.inl hcen))

theorem w16h_minLe (h131 : W4Lem13_1) (n : ℕ) : W4Lem13_2MinLe n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W instCG instFin hW t ht hrk p P hp hP hne hn hc hcard hmin
    have h131' := h131 W hW t ht hrk p P hp hP hne hn hc
    by_cases hgood : 3 < p ∨ InducesTransvection t ⊤
    · have hcardp : Nat.card P = p := h131'.2 hgood
      haveI : Fact p.Prime := ⟨hp⟩
      have hcyc : IsCyclic ↥P := isCyclic_of_prime_card hcardp
      exact Or.inl ⟨hcyc, by rw [hcardp]; omega⟩
    · have hp3 : p = 3 := by
        have hp_le : p ≤ 3 := by omega
        have hpne2 : p ≠ 2 := by
          intro hp2
          have htt : t * t = 1 := by
            have h2 := pow_orderOf_eq_one t
            rwa [ht, pow_two] at h2
          have hP2 : IsPGroup 2 ↥P := by rwa [hp2] at hP
          exact hne (eq_bot_of_isPGroup_two_of_comm_eq_self htt hP2 hn hc)
        have hp2le := hp.two_le
        omega
      have hP3 : IsPGroup 3 ↥P := by rwa [hp3] at hP
      let h132 : Cfg132 t P :=
        { hW := hW, ht := ht, hrk := hrk, hP := hP3, hne := hne, hn := hn, hc := hc }
      have hcard2 : 2 ≤ Nat.card P := (Subgroup.one_lt_card_iff_ne_bot P).mpr hne
      have hn1 : 1 ≤ n := by omega
      have hlt : n - 1 < n := by omega
      have hIHmin : W4Lem13_2MinLe (n - 1) := ih (n - 1) hlt
      have hIHshape : W4Lem13_2ShapeLe (n - 1) :=
        w4Lem13_2Shape_of_minLe (n - 1) hIHmin
      have hMin : 27 < Nat.card P → W4Lem13_2MinLe 27 := by
        intro h27
        have h27le : 27 ≤ n - 1 := by omega
        exact w16g_minLe_mono h27le hIHmin
      have hcard' : Nat.card P ≤ (n - 1) + 1 := by omega
      exact w16h_prime_three (n - 1) hIHshape hMin h131 h132 hmin hcard'

end CFSG.LocalAnalysis.WeakClosure81
