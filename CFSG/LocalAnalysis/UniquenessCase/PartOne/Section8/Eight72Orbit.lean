module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6S898c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2 calC)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem eight72_map_mul {H : Subgroup G} {f g : MulAut G} :
    (H.map g.toMonoidHom).map f.toMonoidHom = H.map (f * g).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

omit [Finite G] in
private theorem eight72_map_one {H : Subgroup G} : H.map (1 : MulAut G).toMonoidHom = H :=
  Subgroup.map_id H

omit [Finite G] in
private theorem eight72_map_conj_mul {H : Subgroup G} (a b : G) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom
      = H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [eight72_map_mul, ← map_mul]

omit [Finite G] in
private theorem r872_map_inv_of_map_eq_self {H : Subgroup G} {f : MulAut G}
    (h : H.map f.toMonoidHom = H) : H.map f⁻¹.toMonoidHom = H := by
  have h1 : (H.map f.toMonoidHom).map f⁻¹.toMonoidHom = H.map f⁻¹.toMonoidHom := by rw [h]
  rw [eight72_map_mul, inv_mul_cancel, eight72_map_one] at h1
  exact h1.symm

omit [Finite G] in
private theorem r872_eq_of_map_eq_self (K₁ K₂ : Subgroup G) (f : MulAut G)
    (hfix : K₁.map f.toMonoidHom = K₁) (h : K₁ = K₂.map f.toMonoidHom) : K₂ = K₁ := by
  have hinv : K₁.map f⁻¹.toMonoidHom = K₁ := r872_map_inv_of_map_eq_self hfix
  have hh : K₂ = K₁.map f⁻¹.toMonoidHom := by
    have h' := congrArg (fun S : Subgroup G => S.map f⁻¹.toMonoidHom) h
    rw [eight72_map_mul, inv_mul_cancel, eight72_map_one] at h'
    exact h'.symm
  rw [hh, hinv]

private theorem eight72_injective_four {α : Type*} {a b c d : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem eight72_four_le_pRank {M : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (K : Fin 4 → Subgroup G) (hK : ∀ i, K i ∈ calC M) (hinj : Function.Injective K)
    (X : Fin 4 → Subgroup G) (hXK : ∀ i, X i ≤ K i) (hXc : ∀ i, Nat.card (X i) = r)
    (hZ : ∀ i, ¬ r ∣ Nat.card (center (Bar2 (K i)))) : 4 ≤ CFSG.Open.pRank r M := by
  classical
  have hKM : ∀ i, K i ≤ M := fun i => (hK i).1.le
  have hXM : ∀ i, X i ≤ M := fun i => (hXK i).trans (hKM i)
  have hcalC := fun i => UC6S846.calC_subgroupOf (hK i)
  obtain ⟨W, hWel, hWcard⟩ := UC6S898.rank_sum_of_family (Y := ↥M) (ι := Fin 4)
    (A := fun i => (K i).subgroupOf M) (E := fun i => (X i).subgroupOf M) (q := r)
    (a := fun _ => 1) hr hr2
    (fun i => (hcalC i).1) (fun i => (hcalC i).2.1) (fun i => (hcalC i).2.2.1)
    (fun i j hij => by
      have hmap := congrArg (Subgroup.map M.subtype) hij
      rw [Subgroup.map_subgroupOf_eq_of_le (hKM i),
        Subgroup.map_subgroupOf_eq_of_le (hKM j)] at hmap
      exact hinj hmap)
    (fun i => by rw [(hcalC i).2.2.2]; exact hZ i)
    (fun i => Subgroup.subgroupOf_mono M (hXK i))
    (fun i => (UC6S898.isElemAbelian_of_card_prime hr (hXc i)).subgroupOf M)
    (fun i => by
      show Nat.card ((X i).subgroupOf M) = r ^ 1
      rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hXM i)).toEquiv, hXc i])
    Finset.univ
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin 4)), (fun _ : Fin 4 => 1) i) = 4 := by simp
  rw [hsum] at hWcard
  exact UC6S846.le_pRank' hr (E := W.map M.subtype) (H := M) (Subgroup.map_subtype_le W)
    (hWel.map _) (by rw [Subgroup.card_map_of_injective M.subtype_injective, hWcard])

theorem eight72_mem_normalizer_of_coprime_six {M K : Subgroup G} (hK : K ∈ calC M) {y : G}
    (hy : y ∈ M) (hy6 : Nat.Coprime (orderOf y) 6) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X : Subgroup G} (hXK : X ≤ K) (hXc : Nat.card X = r)
    (hZ : ¬ r ∣ Nat.card (center (Bar2 K))) (hrank : CFSG.Open.pRank r M ≤ 3) :
    y ∈ normalizer (K : Set G) := by
  classical
  by_contra hyn
  let f : ℕ → MulAut G := fun i => MulAut.conj (y ^ i)
  have hM : ∀ i, M.map (f i).toMonoidHom = M := fun i =>
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer (M.pow_mem hy i))
  have hKi : ∀ i, K.map (f i).toMonoidHom ∈ calC M := fun i =>
    UC6S846.calC_map M (f i) (hM i) hK
  have hdist : ∀ i j : ℕ, i < j → j < 4 →
      K.map (f i).toMonoidHom ≠ K.map (f j).toMonoidHom := by
    intro i j hij hj4 heq
    have hcomp : f j = f i * f (j - i) := by
      show MulAut.conj (y ^ j) = MulAut.conj (y ^ i) * MulAut.conj (y ^ (j - i))
      rw [← map_mul, ← pow_add]
      congr 2
      omega
    have h1 : K.map (f j).toMonoidHom =
        (K.map (f (j - i)).toMonoidHom).map (f i).toMonoidHom := by
      rw [hcomp, Subgroup.map_map]
      rfl
    rw [h1] at heq
    have h2 : K = K.map (f (j - i)).toMonoidHom :=
      Subgroup.map_injective (f i).injective heq
    have hk : y ^ (j - i) ∈ normalizer (K : Set G) :=
      UC6S846.mem_normalizer_iff_map_conj.2 h2.symm
    have hk3 : 0 < j - i ∧ j - i < 4 := by omega
    have hcop : Nat.Coprime (j - i) (orderOf y) := by
      have h3 : j - i = 1 ∨ j - i = 2 ∨ j - i = 3 := by omega
      rcases h3 with h | h | h <;> rw [h] <;>
        exact (hy6.coprime_dvd_right (by norm_num)).symm
    obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime (x := y) (n := j - i) hcop
    apply hyn
    rw [show y = (y ^ (j - i)) ^ t from ht.symm]
    exact (Subgroup.normalizer (K : Set G)).pow_mem hk t
  have hfour := eight72_four_le_pRank (M := M) hr hr2
    (fun i : Fin 4 => K.map (f (i : ℕ)).toMonoidHom)
    (fun i => hKi (i : ℕ))
    (by
      intro i j hij
      by_contra hne
      have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
      · exact hdist i j hlt j.2 hij
      · exact hdist j i hgt i.2 hij.symm)
    (fun i : Fin 4 => X.map (f (i : ℕ)).toMonoidHom)
    (fun i => Subgroup.map_mono hXK)
    (fun i => by rw [Subgroup.card_map_of_injective (f (i : ℕ)).injective, hXc])
    (fun i => by rw [UC6S846.card_center_bar2_map]; exact hZ)
  omega

theorem eight72_mem_normalizer_of_odd {M K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ calC M)
    (h₂ : K₂ ∈ calC M) (hne : K₁ ≠ K₂) {y : G} (hy : y ∈ M) (hyo : Odd (orderOf y))
    (hy₁ : y ∈ normalizer (K₁ : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X₁ X₂ : Subgroup G} (hX₁ : X₁ ≤ K₁) (hX₂ : X₂ ≤ K₂) (hX₁c : Nat.card X₁ = r)
    (hX₂c : Nat.card X₂ = r) (hZ₁ : ¬ r ∣ Nat.card (center (Bar2 K₁)))
    (hZ₂ : ¬ r ∣ Nat.card (center (Bar2 K₂))) (hrank : CFSG.Open.pRank r M ≤ 3) :
    y ∈ normalizer (K₂ : Set G) := by
  classical
  by_contra hyn
  have hMy : M.map (MulAut.conj y).toMonoidHom = M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hy)
  have hMy2 : M.map (MulAut.conj (y ^ 2)).toMonoidHom = M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer (M.pow_mem hy 2))
  have hfix₁ : K₁.map (MulAut.conj y).toMonoidHom = K₁ :=
    UC6S846.mem_normalizer_iff_map_conj.1 hy₁
  have hfix₁' : K₁.map (MulAut.conj (y ^ 2)).toMonoidHom = K₁ :=
    UC6S846.mem_normalizer_iff_map_conj.1 ((Subgroup.normalizer (K₁ : Set G)).pow_mem hy₁ 2)
  have hKy : K₂.map (MulAut.conj y).toMonoidHom ∈ calC M :=
    UC6S846.calC_map M (MulAut.conj y) hMy h₂
  have hKy2 : K₂.map (MulAut.conj (y ^ 2)).toMonoidHom ∈ calC M :=
    UC6S846.calC_map M (MulAut.conj (y ^ 2)) hMy2 h₂
  have h2y : K₂.map (MulAut.conj y).toMonoidHom ≠ K₂ := fun h =>
    hyn (UC6S846.mem_normalizer_iff_map_conj.2 h)
  have h2y2 : K₂.map (MulAut.conj (y ^ 2)).toMonoidHom ≠ K₂ := by
    intro h
    apply hyn
    have hN : y ^ 2 ∈ normalizer (K₂ : Set G) := UC6S846.mem_normalizer_iff_map_conj.2 h
    obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime (x := y) (n := 2)
      (Nat.coprime_two_left.mpr hyo)
    rw [show y = (y ^ 2) ^ t from ht.symm]
    exact (Subgroup.normalizer (K₂ : Set G)).pow_mem hN t
  have hy2y : K₂.map (MulAut.conj (y ^ 2)).toMonoidHom
      ≠ K₂.map (MulAut.conj y).toMonoidHom := by
    intro h
    apply h2y
    have h' := congrArg (fun S : Subgroup G => S.map (MulAut.conj y⁻¹).toMonoidHom) h
    rw [eight72_map_conj_mul, eight72_map_conj_mul] at h'
    rw [show y⁻¹ * y ^ 2 = y by group, show y⁻¹ * y = 1 by group,
      show MulAut.conj (1 : G) = 1 from map_one MulAut.conj, eight72_map_one] at h'
    exact h'
  have h1y : K₁ ≠ K₂.map (MulAut.conj y).toMonoidHom :=
    fun h => hne (r872_eq_of_map_eq_self K₁ K₂ (MulAut.conj y) hfix₁ h).symm
  have h1y2 : K₁ ≠ K₂.map (MulAut.conj (y ^ 2)).toMonoidHom :=
    fun h => hne (r872_eq_of_map_eq_self K₁ K₂ (MulAut.conj (y ^ 2)) hfix₁' h).symm
  let Kf : Fin 4 → Subgroup G :=
    ![K₁, K₂, K₂.map (MulAut.conj y).toMonoidHom,
      K₂.map (MulAut.conj (y ^ 2)).toMonoidHom]
  let Xf : Fin 4 → Subgroup G :=
    ![X₁, X₂, X₂.map (MulAut.conj y).toMonoidHom,
      X₂.map (MulAut.conj (y ^ 2)).toMonoidHom]
  have hKf : ∀ i, Kf i ∈ calC M := by
    intro i
    fin_cases i
    · exact h₁
    · exact h₂
    · exact hKy
    · exact hKy2
  have hXK : ∀ i, Xf i ≤ Kf i := by
    intro i
    fin_cases i
    · exact hX₁
    · exact hX₂
    · exact Subgroup.map_mono hX₂
    · exact Subgroup.map_mono hX₂
  have hXc : ∀ i, Nat.card (Xf i) = r := by
    intro i
    fin_cases i
    · exact hX₁c
    · exact hX₂c
    · show Nat.card (X₂.map (MulAut.conj y).toMonoidHom) = r
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hX₂c]
    · show Nat.card (X₂.map (MulAut.conj (y ^ 2)).toMonoidHom) = r
      rw [Subgroup.card_map_of_injective (MulAut.conj (y ^ 2)).injective, hX₂c]
  have hZ : ∀ i, ¬ r ∣ Nat.card (center (Bar2 (Kf i))) := by
    intro i
    fin_cases i
    · exact hZ₁
    · exact hZ₂
    · show ¬ r ∣ Nat.card (center (Bar2 (K₂.map (MulAut.conj y).toMonoidHom)))
      rw [UC6S846.card_center_bar2_map]; exact hZ₂
    · show ¬ r ∣ Nat.card (center (Bar2 (K₂.map (MulAut.conj (y ^ 2)).toMonoidHom)))
      rw [UC6S846.card_center_bar2_map]; exact hZ₂
  have hinj : Function.Injective Kf := by
    have h := eight72_injective_four (a := K₁) (b := K₂)
      (c := K₂.map (MulAut.conj y).toMonoidHom)
      (d := K₂.map (MulAut.conj (y ^ 2)).toMonoidHom)
      hne h1y h1y2 h2y.symm h2y2.symm hy2y.symm
    simpa [Kf] using h
  have hfour := eight72_four_le_pRank (M := M) hr hr2 Kf hKf hinj Xf hXK hXc hZ
  omega

theorem eight72_card_le_three_mul {M K A : Subgroup G} (hK : K ∈ calC M) (hAM : A ≤ M)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {X : Subgroup G}
    (hXK : X ≤ K) (hXc : Nat.card X = r) (hZ : ¬ r ∣ Nat.card (center (Bar2 K)))
    (hrank : CFSG.Open.pRank r M ≤ 3) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓ normalizer (K : Set G)) := by
  classical
  by_cases hle : A ≤ normalizer (K : Set G)
  · have hinf : A ⊓ normalizer (K : Set G) = A := inf_eq_left.2 hle
    rw [hinf]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  · have hex : ∃ a, a ∈ A ∧ a ∉ normalizer (K : Set G) := by
      by_contra hcon
      exact hle fun x hx => by
        by_contra hxN
        exact hcon ⟨x, hx, hxN⟩
    obtain ⟨a, haA, haN⟩ := hex
    have haM : a ∈ M := hAM haA
    have ha3 : a ^ 3 = 1 := hA3 a haA
    have h4 : a ^ (2 * 2) = a := by
      have h5 : a ^ (2 * 2) = a ^ 3 * a := by rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ]
      rw [h5, ha3, one_mul]
    have haa : a = (a ^ 2) ^ 2 := by rw [← pow_mul, h4]
    have ha2N : a ^ 2 ∉ normalizer (K : Set G) := by
      intro h
      exact haN (by rw [haa]; exact (Subgroup.normalizer (K : Set G)).pow_mem h 2)
    have hMa : M.map (MulAut.conj a).toMonoidHom = M :=
      UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer haM)
    have hMa2 : M.map (MulAut.conj (a ^ 2)).toMonoidHom = M :=
      UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer (M.pow_mem haM 2))
    have hKa : K.map (MulAut.conj a).toMonoidHom ≠ K := fun h =>
      haN (UC6S846.mem_normalizer_iff_map_conj.2 h)
    have hKa2 : K.map (MulAut.conj (a ^ 2)).toMonoidHom ≠ K := fun h =>
      ha2N (UC6S846.mem_normalizer_iff_map_conj.2 h)
    have ha2a : K.map (MulAut.conj (a ^ 2)).toMonoidHom
        ≠ K.map (MulAut.conj a).toMonoidHom := by
      intro h
      apply hKa
      have h' := congrArg (fun S : Subgroup G => S.map (MulAut.conj a⁻¹).toMonoidHom) h
      rw [eight72_map_conj_mul, eight72_map_conj_mul] at h'
      rw [show a⁻¹ * a ^ 2 = a by group, show a⁻¹ * a = 1 by group,
        show MulAut.conj (1 : G) = 1 from map_one MulAut.conj, eight72_map_one] at h'
      exact h'
    have hkey : ∀ b ∈ A, ∃ i : Fin 3, (a ^ (i : ℕ))⁻¹ * b ∈ normalizer (K : Set G) := by
      intro b hbA
      by_contra hb
      push Not at hb
      have hbM : b ∈ M := hAM hbA
      have hMb : M.map (MulAut.conj b).toMonoidHom = M :=
        UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hbM)
      have hKb : K.map (MulAut.conj b).toMonoidHom ≠ K := by
        intro h
        exact (hb 0) (by simpa using UC6S846.mem_normalizer_iff_map_conj.2 h)
      have hb1 : a⁻¹ * b ∉ normalizer (K : Set G) := by simpa using hb 1
      have hb2 : (a ^ 2)⁻¹ * b ∉ normalizer (K : Set G) := by simpa using hb 2
      have hab : K.map (MulAut.conj a).toMonoidHom ≠ K.map (MulAut.conj b).toMonoidHom := by
        intro h
        apply hb1
        have h' := congrArg (fun S : Subgroup G => S.map (MulAut.conj a⁻¹).toMonoidHom) h
        rw [eight72_map_conj_mul, eight72_map_conj_mul] at h'
        rw [show a⁻¹ * a = 1 by group, show MulAut.conj (1 : G) = 1 from map_one MulAut.conj,
          eight72_map_one] at h'
        exact UC6S846.mem_normalizer_iff_map_conj.2 h'.symm
      have ha2b : K.map (MulAut.conj (a ^ 2)).toMonoidHom
          ≠ K.map (MulAut.conj b).toMonoidHom := by
        intro h
        apply hb2
        have h' := congrArg (fun S : Subgroup G =>
          S.map (MulAut.conj (a ^ 2)⁻¹).toMonoidHom) h
        rw [eight72_map_conj_mul, eight72_map_conj_mul] at h'
        rw [show (a ^ 2)⁻¹ * a ^ 2 = 1 by group,
          show MulAut.conj (1 : G) = 1 from map_one MulAut.conj, eight72_map_one] at h'
        exact UC6S846.mem_normalizer_iff_map_conj.2 h'.symm
      let Kf : Fin 4 → Subgroup G :=
        ![K, K.map (MulAut.conj a).toMonoidHom, K.map (MulAut.conj (a ^ 2)).toMonoidHom,
          K.map (MulAut.conj b).toMonoidHom]
      let Xf : Fin 4 → Subgroup G :=
        ![X, X.map (MulAut.conj a).toMonoidHom, X.map (MulAut.conj (a ^ 2)).toMonoidHom,
          X.map (MulAut.conj b).toMonoidHom]
      have hKf : ∀ i, Kf i ∈ calC M := by
        intro i
        fin_cases i
        · exact hK
        · exact UC6S846.calC_map M (MulAut.conj a) hMa hK
        · exact UC6S846.calC_map M (MulAut.conj (a ^ 2)) hMa2 hK
        · exact UC6S846.calC_map M (MulAut.conj b) hMb hK
      have hXKs : ∀ i, Xf i ≤ Kf i := by
        intro i
        fin_cases i
        · exact hXK
        · exact Subgroup.map_mono hXK
        · exact Subgroup.map_mono hXK
        · exact Subgroup.map_mono hXK
      have hXcs : ∀ i, Nat.card (Xf i) = r := by
        intro i
        fin_cases i
        · exact hXc
        · show Nat.card (X.map (MulAut.conj a).toMonoidHom) = r
          rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, hXc]
        · show Nat.card (X.map (MulAut.conj (a ^ 2)).toMonoidHom) = r
          rw [Subgroup.card_map_of_injective (MulAut.conj (a ^ 2)).injective, hXc]
        · show Nat.card (X.map (MulAut.conj b).toMonoidHom) = r
          rw [Subgroup.card_map_of_injective (MulAut.conj b).injective, hXc]
      have hZs : ∀ i, ¬ r ∣ Nat.card (center (Bar2 (Kf i))) := by
        intro i
        fin_cases i
        · exact hZ
        · show ¬ r ∣ Nat.card (center (Bar2 (K.map (MulAut.conj a).toMonoidHom)))
          rw [UC6S846.card_center_bar2_map]; exact hZ
        · show ¬ r ∣ Nat.card (center (Bar2 (K.map (MulAut.conj (a ^ 2)).toMonoidHom)))
          rw [UC6S846.card_center_bar2_map]; exact hZ
        · show ¬ r ∣ Nat.card (center (Bar2 (K.map (MulAut.conj b).toMonoidHom)))
          rw [UC6S846.card_center_bar2_map]; exact hZ
      have hinj : Function.Injective Kf := by
        have h := eight72_injective_four (a := K) (b := K.map (MulAut.conj a).toMonoidHom)
          (c := K.map (MulAut.conj (a ^ 2)).toMonoidHom) (d := K.map (MulAut.conj b).toMonoidHom)
          hKa.symm hKa2.symm hKb.symm ha2a.symm hab ha2b
        simpa [Kf] using h
      have hfour := eight72_four_le_pRank (M := M) hr hr2 Kf hKf hinj Xf hXKs hXcs hZs
      omega
    have hsurj : Function.Surjective (fun p : Fin 3 × ↥(A ⊓ normalizer (K : Set G)) =>
        (⟨a ^ (p.1 : ℕ) * (p.2 : G), by
          exact A.mul_mem (A.pow_mem haA _) p.2.2.1⟩ : ↥A)) := by
      rintro ⟨b, hbA⟩
      obtain ⟨i, hi⟩ := hkey b hbA
      refine ⟨⟨i, ⟨(a ^ (i : ℕ))⁻¹ * b, ?_, hi⟩⟩, ?_⟩
      · exact A.mul_mem (A.inv_mem (A.pow_mem haA _)) hbA
      · apply Subtype.ext
        show a ^ (i : ℕ) * ((a ^ (i : ℕ))⁻¹ * b) = b
        group
    have hcard := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, Nat.card_fin] at hcard
    exact hcard

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
