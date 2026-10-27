module

public import CFSG.Quasithin.EmptyFaithful.S151ZL
public import CFSG.Quasithin.EmptyFaithful.S151ZN
public import CFSG.Quasithin.EmptyFaithful.S151ZO
public import CFSG.Quasithin.EmptyFaithful.S151ZQ
public import CFSG.Quasithin.EmptyFaithful.S151ZI

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {A : Type} [Group A]

theorem smin_shape [Finite A] {L S B P : Subgroup A} {n : ℕ} (hBdef : B = S ⊓ L) (hn3 : 3 ≤ n)
    (D : SurjBorel n L B) (hSN : S ≤ Subgroup.normalizer (L : Set A))
    (hk : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (L : Set A), ∀ x : ↥L, D.e x = 1 →
      D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1)
    (hP : SMin L S P) :
    ∃ i, IsNode n i ∧ (D.cutsOf P = nodeSet n \ {i} ∨
      ∃ j, IsNode n j ∧ i < j ∧ D.cutsOf P = nodeSet n \ {i, j}) := by
  classical
  have hBL : B ≤ L := hBdef ▸ inf_le_right
  have hSB : ∀ s ∈ S, s ∈ Subgroup.normalizer (B : Set A) := fun s hs => by
    rw [hBdef]
    exact zb_mem_normalizer_inf (Subgroup.le_normalizer hs) (hSN hs)
  have hdich : ∀ s ∈ S,
      (∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = D.cutsOf K) ∨
      (∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = flipNodes n (D.cutsOf K)) :=
    fun s hs => D.cutsOf_conj_dichotomy hn3 s (hSN hs) (hk s hs _) (hk s⁻¹ (S.inv_mem hs) _)
      (zl_conjSub_eq (hSB s hs))
  have hinv : ∀ K : Subgroup A, B ≤ K → K ≤ L → ∀ s ∈ S,
      D.cutsOf (conjSub s K) = D.cutsOf K → s ∈ Subgroup.normalizer (K : Set A) := by
    intro K hBK hKL s hs hcut
    apply zl_mem_normalizer
    exact D.eq_of_cutsOf_eq (zl_le_conj (zl_conjSub_eq (hSB s hs)) hBK)
      (zl_conj_le (hSN hs) hKL) hBK hKL hcut
  have hBP : B ≤ P := hBdef ▸ hP.sl
  have hPL : P ≤ L := hP.le
  have hPB : P ≠ B := fun h => hP.ne (by rw [← hBdef]; exact h.symm)
  obtain ⟨i₀, hi₀, hi₀P⟩ : ∃ i, IsNode n i ∧ i ∉ D.cutsOf P := by
    by_contra hcon
    push Not at hcon
    apply hPB
    apply D.eq_of_cutsOf_eq hBP hPL le_rfl hBL
    rw [D.cutsOf_B]
    exact Set.Subset.antisymm (fun x hx => D.isNode_of_mem_cutsOf hx) (fun x hx => hcon x hx)
  have hmin : ∀ (O : Set ℕ), i₀ ∈ O → (∀ x ∈ O, x ∉ D.cutsOf P) →
      (∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf K = nodeSet n \ O →
        S ≤ Subgroup.normalizer (K : Set A)) →
      D.cutsOf P = nodeSet n \ O := by
    intro O hi₀O hOP hKS
    obtain ⟨K, hBK, hKL, hKc⟩ := D.exists_cutsOf_eq (I := nodeSet n \ O) (fun x hx => hx.1)
    have hKP : K ≤ P := by
      rw [D.cutsOf_le_iff hBK hKL hBP, hKc]
      intro x hx
      exact ⟨D.isNode_of_mem_cutsOf hx, fun hxO => hOP x hxO hx⟩
    rcases hP.minimal K (hKS K hBK hKL hKc) (hBdef ▸ hBK) hKP with hKB | hKP'
    · exfalso
      have h1 : D.cutsOf K = nodeSet n := by
        rw [show K = B from hKB.trans hBdef.symm, D.cutsOf_B]
        rfl
      rw [hKc] at h1
      have h2 : i₀ ∈ nodeSet n := hi₀
      rw [← h1] at h2
      exact h2.2 hi₀O
    · rw [← hKP', hKc]
  by_cases hfl : ∃ s ∈ S,
      ∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = flipNodes n (D.cutsOf K)
  ·
    obtain ⟨s₀, hs₀, hfl₀⟩ := hfl
    have hflipP : flipNodes n (D.cutsOf P) = D.cutsOf P := by
      have h1 : conjSub s₀ P = P := zl_conjSub_eq (hP.sP hs₀)
      have h2 := hfl₀ P hBP hPL
      rw [h1] at h2
      exact h2.symm
    have hfi : IsNode n (n - i₀) := isNode_flip hi₀
    have hni : n - i₀ ∉ D.cutsOf P := by
      intro h
      have : i₀ ∈ flipNodes n (D.cutsOf P) := ⟨n - i₀, h, by have := hi₀.2; omega⟩
      rw [hflipP] at this
      exact hi₀P this
    have hc : D.cutsOf P = nodeSet n \ {i₀, n - i₀} := by
      apply hmin {i₀, n - i₀} (Set.mem_insert _ _)
      · rintro x (rfl | rfl)
        · exact hi₀P
        · exact hni
      · intro K hBK hKL hKc s hs
        apply hinv K hBK hKL s hs
        rcases hdich s hs with htr | hfl'
        · exact htr K hBK hKL
        · rw [hfl' K hBK hKL, hKc]
          exact flip_diff_pair hi₀
    rcases lt_trichotomy i₀ (n - i₀) with hlt | heq | hgt
    · exact ⟨i₀, hi₀, Or.inr ⟨n - i₀, hfi, hlt, hc⟩⟩
    · refine ⟨i₀, hi₀, Or.inl ?_⟩
      rw [hc, ← heq]
      simp
    · exact ⟨n - i₀, hfi, Or.inr ⟨i₀, hi₀, hgt, by rw [hc, Set.pair_comm]⟩⟩
  ·
    push Not at hfl
    have htriv : ∀ s ∈ S, ∀ K : Subgroup A, B ≤ K → K ≤ L → D.cutsOf (conjSub s K) = D.cutsOf K := by
      intro s hs
      rcases hdich s hs with htr | hfl'
      · exact htr
      · exfalso
        obtain ⟨K, hBK, hKL, hne⟩ := hfl s hs
        exact hne (hfl' K hBK hKL)
    refine ⟨i₀, hi₀, Or.inl ?_⟩
    apply hmin {i₀} (Set.mem_singleton _)
    · rintro x rfl
      exact hi₀P
    · intro K hBK hKL _ s hs
      exact hinv K hBK hKL s hs (htriv s hs K hBK hKL)

theorem zr_relIndex_eq {L B : Subgroup A} {n : ℕ} (D : SurjBorel n L B) {P : Subgroup A}
    (hBP : B ≤ P) (hPL : P ≤ L) : B.relIndex P = (Ut n).relIndex (D.model P) := by
  have hker : D.e.ker ≤ B.subgroupOf L := D.ker_le
  have hHK : B.subgroupOf L ≤ P.subgroupOf L := fun x hx => hBP hx
  have h1 : (Ut n).relIndex (D.model P) =
      ((B.subgroupOf L).map D.e).relIndex ((P.subgroupOf L).map D.e) := by
    rw [D.hB]
    rfl
  rw [h1, Subgroup.relIndex_map_map, sup_eq_left.mpr hker, sup_eq_left.mpr (hker.trans hHK)]
  exact (Subgroup.relIndex_subgroupOf hPL).symm

theorem smin_relIndex_S [Finite A] {L S P : Subgroup A} (hP : SMin L S P) :
    S.relIndex (P ⊔ S) = (S ⊓ L).relIndex P := by
  have e1 := zb_relIndex_sup hP.sP
  have e2 := Subgroup.relIndex_mul_relIndex (S ⊓ L) P (P ⊔ S) hP.sl le_sup_left
  have e3 := Subgroup.relIndex_mul_relIndex (S ⊓ L) S (P ⊔ S) inf_le_left le_sup_right
  have e4 : (S ⊓ L).relIndex S = P.relIndex S := by
    rw [← hP.inf_eq]
    exact Subgroup.inf_relIndex_right P S
  have hr : P.relIndex S ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card P S
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := ↥S)).ne' h1.symm
  rw [e1] at e2
  rw [e4] at e3
  have : (S ⊓ L).relIndex P * P.relIndex S = P.relIndex S * S.relIndex (P ⊔ S) := by
    rw [e2, e3]
  rw [mul_comm (P.relIndex S)] at this
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hr) this).symm

theorem smin_card_sup [Finite A] {L S P : Subgroup A} (hP : SMin L S P) :
    Nat.card ↥(P ⊔ S) = Nat.card ↥S * (S ⊓ L).relIndex P := by
  have h1 := Subgroup.relIndex_mul_card S (P ⊔ S)
  rw [inf_of_le_left le_sup_right, smin_relIndex_S hP] at h1
  rw [← h1, mul_comm]

theorem input15122L45No3_holds : Input15122L45No3 := by
  intro G _ _ L S P hchar htype hS2 hSN hsyl hP
  obtain ⟨n, hn, hnp⟩ : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      IsPSL n 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases htype with h | h
    · exact ⟨4, Or.inl rfl, h⟩
    · exact ⟨5, Or.inr rfl, h⟩
  obtain ⟨D, hker⟩ := exists_surjBorel (n := n) (by omega) hnp hsyl
  have hk : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (L : Set G), ∀ x : ↥L, D.e x = 1 →
      D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1 := by
    intro s hs hsN x hx
    have hxK : x ∈ CFSG.pCore 2 ↥L := by
      rw [← hker]
      exact hx
    have h := zl_theta_mem_pCore hsN hxK
    rw [← hker] at h
    exact h
  obtain ⟨i, hi, hshape⟩ := smin_shape rfl (by omega) D hSN hk hP
  have hBP : S ⊓ L ≤ P := hP.sl
  have hPL : P ≤ L := hP.le
  have hmodel : D.model P = QI n (D.cutsOf P) := eq_QI_cuts (D.Ut_le_model hBP)
  have hidx : (S ⊓ L).relIndex P = (Ut n).relIndex (QI n (D.cutsOf P)) := by
    rw [← hmodel]
    exact zr_relIndex_eq D hBP hPL
  obtain ⟨a, ha, hd⟩ : ∃ a, a ∈ D.cutsOf P ∧
      ((S ⊓ L).relIndex P ∣ 21 ∨ (S ⊓ L).relIndex P ∣ 9) := by
    rcases hshape with hc | ⟨j, hj, hij, hc⟩
    · refine ⟨if i = 1 then 2 else 1, ?_, Or.inl ?_⟩
      · rw [hc]
        refine ⟨⟨by split_ifs <;> omega, by split_ifs <;> omega⟩, ?_⟩
        simp only [Set.mem_singleton_iff]
        split_ifs with h <;> omega
      · rw [hidx, hc, index_single hi]
        norm_num
    · refine ⟨if i = 1 ∨ j = 1 then (if i = 2 ∨ j = 2 then 3 else 2) else 1, ?_, ?_⟩
      · rw [hc]
        have hn4 : 4 ≤ n := by omega
        refine ⟨⟨by split_ifs <;> omega, by split_ifs <;> omega⟩, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        split_ifs <;> omega
      · rw [hidx, hc]
        rcases index_double hi hj hij with h | h
        · exact Or.inr (by rw [h])
        · exact Or.inl (by rw [h])
  have hbig : ParBig L P := parBig_of_cut D hker hBP hPL ha
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hS2
  have hcard : Nat.card ↥(P ⊔ S) = 2 ^ m * (S ⊓ L).relIndex P := by
    rw [smin_card_sup hP, hm]
  have hdiv : Nat.card ↥(P ⊔ S) ∣ 2 ^ m * 21 ∨ Nat.card ↥(P ⊔ S) ∣ 2 ^ m * 9 := by
    rw [hcard]
    rcases hd with hd | hd
    · exact Or.inl (mul_dvd_mul_left _ hd)
    · exact Or.inr (mul_dvd_mul_left _ hd)
  have hA3 : ∀ K : Subgroup G, IsChi0Block (P ⊔ S) K → IsAltType K 3 :=
    fun K hK => chi0_isAltType_three hK hdiv
  exact not_C126Third_of_parBig hS2 hP.sP hsyl hPL hBP hchar hbig hA3

theorem input15122L45Block'_holds
    (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    Input15122L45Block' :=
  input15122L45Block_of h118 h126 h37 h38 l45NotA38Type_holds input15122L45Gen_holds
    input15122L45No3_holds

end CFSG.Quasithin
