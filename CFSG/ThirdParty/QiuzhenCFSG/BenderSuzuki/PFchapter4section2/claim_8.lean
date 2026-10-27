module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_7

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (8) -/

private theorem claim_8_upper_sum_of_product_eq_succ
    (m n q b : ℕ) (hn : n * m = q + 1) (hb : b ∈ Finset.Icc 1 n) :
    Finset.sum (Finset.Icc 1 n) (fun j => (if j = b then m - 1 else m)) = q := by
  obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
  have hn_pos : 1 ≤ n := hb1.trans hb2
  have hm_pos : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    rw [hm0', mul_zero] at hn
    omega
  have hsum_one : Finset.sum (Finset.Icc 1 n) (fun j => (if j = b then 1 else 0)) = 1 := by
    simp [hb]
  have hsum_m : Finset.sum (Finset.Icc 1 n) (fun _ : ℕ => m) = n * m := by
    simp
  have h_eq : Finset.sum (Finset.Icc 1 n) (fun j => (if j = b then m - 1 else m)) + 1 = n * m := by
    calc
      Finset.sum (Finset.Icc 1 n) (fun j => (if j = b then m - 1 else m)) + 1 =
          Finset.sum (Finset.Icc 1 n) (fun j => (if j = b then m - 1 else m)) +
          Finset.sum (Finset.Icc 1 n) (fun j => (if j = b then 1 else 0)) := by rw [hsum_one]
      _ = Finset.sum (Finset.Icc 1 n) (fun j => (if j = b then m - 1 else m) + (if j = b then 1 else 0)) :=
        by rw [Finset.sum_add_distrib]
      _ = Finset.sum (Finset.Icc 1 n) (fun _ : ℕ => m) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        by_cases hj_eq : j = b
        · subst j; simp [Nat.sub_add_cancel hm_pos]
        · simp [hj_eq]
      _ = n * m := hsum_m
  omega

public theorem claim_8
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s omega₁ : G) (f g h : G → G)
    (m n b i : ℕ) (omega : ℕ → G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W)
    (hWorder : m = Nat.card W)
    (hn : n * m = Nat.card Q0 + 1)
    (hb : 1 ≤ b ∧ b ≤ n)
    (hi : 1 ≤ i ∧ i ≤ n)
    (horbit_representatives :
      (∀ j : ℕ, 1 ≤ j → j ≤ n → omega j ∈ Q ∧ omega j ∉ Q0) ∧
      (∀ x : G, x ∈ Q → x ∉ Q0 →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
          ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
            x = rightConjugateElem (omega j) d * q0) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          omega j = rightConjugateElem (omega k) d * q0) → j = k))
    (homega₁ : omega₁ = omega b) :
    Nat.card {x : G // x ∈ Q0 ∧
      (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
        f (omega₁ * x) = rightConjugateElem (omega i) d * q0)} =
      (if i = b then m - 1 else m) := by
  classical
  rcases horbit_representatives with ⟨hreps, hcomplete, _hdistinct⟩
  have hsec2 := hsection3.1
  have homega₁_data : omega₁ ∈ Q ∧ omega₁ ∉ Q0 := by
    rw [homega₁]
    exact hreps b hb.1 hb.2
  have homega₁1 : omega₁ ≠ 1 := fun h =>
    homega₁_data.2 (h ▸ Q0.one_mem)
  have hV_le_D : V ≤ D := by
    rw [hsec2.V_eq]
    exact inf_le_left
  have hW_le_D : W ≤ D := hsec2.W_le_V.trans hV_le_D
  have hKW_le_D : KW ≤ D := by
    rw [hKW]
    exact sup_le hsec2.K_le_D hW_le_D
  have hW_centralizes_K : W ≤ Subgroup.centralizer (K : Set G) := by
    intro w hwW
    rw [hsec2.W_eq] at hwW
    exact hwW.2
  have hW_normalizes_K : W ≤ Subgroup.normalizer (K : Set G) := by
    exact hW_centralizes_K.trans (centralizer_le_normalizer K)
  have hKW_decomp : ∀ d : G, d ∈ KW →
      ∃ k w : G, k ∈ K ∧ w ∈ W ∧ d = k * w := by
    intro d hdKW
    have hdSup : d ∈ K ⊔ W := by simpa [hKW] using hdKW
    change d ∈ ((K ⊔ W : Subgroup G) : Set G) at hdSup
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K W hW_normalizes_K] at hdSup
    rcases Set.mem_mul.mp hdSup with ⟨k, hkK, w, hwW, hkw⟩
    exact ⟨k, w, hkK, hwW, hkw.symm⟩
  have hQ0_conj_D : ∀ q a : G, q ∈ Q0 → a ∈ D →
      rightConjugateElem q a ∈ Q0 := by
    intro q a hqQ0 haD
    have haH := PFchapter4section1.rankOneSplit_D_le_M hD_eq haD
    rcases (hsec2.Q0_def q).1 hqQ0 with rfl | ⟨hqH, hqI⟩
    · simp [rightConjugateElem]
    · exact (hsec2.Q0_def _).2 (Or.inr
        ⟨H.mul_mem (H.mul_mem (H.inv_mem haH) hqH) haH,
          isInvolution_rightConjugateElem hqI⟩)
  have hK_forbidden : ∀ x y a : G,
      x ∈ Q0 → y ∈ Q0 → a ∈ D → a ∈ K →
      f (omega₁ * x) = rightConjugateElem (omega₁ * y) a → False := by
    intro x y a hxQ0 hyQ0 haD haK heq
    have hxQ : omega₁ * x ∈ Q :=
      Q.mul_mem homega₁_data.1 (hsec2.Q0_le_Q hxQ0)
    have hyQ : omega₁ * y ∈ Q :=
      Q.mul_mem homega₁_data.1 (hsec2.Q0_le_Q hyQ0)
    have hx1 : omega₁ * x ≠ 1 := by
      intro hxone
      apply homega₁_data.2
      have homega_eq : omega₁ = (omega₁ * x) * x⁻¹ := by simp [mul_assoc]
      rw [homega_eq, hxone]
      simpa using Q0.inv_mem hxQ0
    have hy1 : omega₁ * y ≠ 1 := by
      intro hyone
      apply homega₁_data.2
      have homega_eq : omega₁ = (omega₁ * y) * y⁻¹ := by simp [mul_assoc]
      rw [homega_eq, hyone]
      simpa using Q0.inv_mem hyQ0
    have hx0 : omega₁ * x ∉ Q0 := by
      intro hxprod
      apply homega₁_data.2
      have homega_eq : omega₁ = (omega₁ * x) * x⁻¹ := by simp [mul_assoc]
      rw [homega_eq]
      exact Q0.mul_mem hxprod (Q0.inv_mem hxQ0)
    have ha_t : rightConjugateElem a t = a⁻¹ := ((hsec2.K_def a).mp haK).2
    have hdouble := PFchapter4section1.claim_H2 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omega₁ * x) hxQ hx1
    have htransport := PFchapter4section1.claim_H3 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omega₁ * y) a hyQ hy1 haD
    have hz_eq : omega₁ * x =
        rightConjugateElem (f (omega₁ * y)) a⁻¹ := by
      calc
        omega₁ * x = f (f (omega₁ * x)) := hdouble.symm
        _ = f (rightConjugateElem (omega₁ * y) a) := by rw [← heq]
        _ = rightConjugateElem (f (omega₁ * y))
            (rightConjugateElem a t) := htransport
        _ = rightConjugateElem (f (omega₁ * y)) a⁻¹ := by rw [ha_t]
    have hreverse : f (omega₁ * y) =
        rightConjugateElem (omega₁ * x) a := by
      have hconj := congrArg (fun z : G => rightConjugateElem z a) hz_eq
      simpa [rightConjugateElem, mul_assoc] using hconj.symm
    by_cases hxy : x = y
    · subst y
      exact (claim_5_a H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        (omega₁ * x) 1 a hxQ hx0 Q0.one_mem haD (by simpa using heq)) rfl
    · have hnot := claim_7 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        omega₁ omega₁ x y y x a a
        homega₁_data.1 homega₁_data.2 homega₁_data.1 homega₁_data.2
        hxQ0 hyQ0 hyQ0 hxQ0 haD haD hxy heq hreverse
      exact hnot ⟨1, K.one_mem, by simp⟩
  let Fiber (j : ℕ) := {x : G // x ∈ Q0 ∧
    (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
      f (omega₁ * x) = rightConjugateElem (omega j) d * q0)}
  have hupper : ∀ j : ℕ, 1 ≤ j → j ≤ n →
      Nat.card (Fiber j) ≤ (if j = b then m - 1 else m) := by
    intro j hj1 hjn
    have homegaj := hreps j hj1 hjn
    let Data (u : Fiber j) := {p : G × G × G //
      p.1 ∈ K ∧ p.2.1 ∈ W ∧ p.2.2 ∈ Q0 ∧
        f (omega₁ * (u : G)) =
          rightConjugateElem (omega j * p.2.2) (p.1 * p.2.1)}
    have hdata_nonempty : ∀ u : Fiber j, Nonempty (Data u) := by
      intro u
      rcases u.property.2 with ⟨d, q0, hdKW, hq0, hu⟩
      rcases hKW_decomp d hdKW with ⟨k, w, hkK, hwW, rfl⟩
      let y := rightConjugateElem q0 (k * w)⁻¹
      have hkwD : k * w ∈ D :=
        D.mul_mem (hsec2.K_le_D hkK) (hW_le_D hwW)
      have hyQ0 : y ∈ Q0 := hQ0_conj_D q0 (k * w)⁻¹ hq0 (D.inv_mem hkwD)
      refine ⟨⟨(k, w, y), hkK, hwW, hyQ0, ?_⟩⟩
      calc
        f (omega₁ * (u : G)) =
            rightConjugateElem (omega j) (k * w) * q0 := hu
        _ = rightConjugateElem (omega j * y) (k * w) := by
          simp [y, rightConjugateElem, mul_assoc]
    let data (u : Fiber j) : Data u := Classical.choice (hdata_nonempty u)
    let kOf (u : Fiber j) : G := (data u).val.1
    let wOf (u : Fiber j) : G := (data u).val.2.1
    let qOf (u : Fiber j) : G := (data u).val.2.2
    have hkOf (u : Fiber j) : kOf u ∈ K := (data u).property.1
    have hwOf (u : Fiber j) : wOf u ∈ W := (data u).property.2.1
    have hqOf (u : Fiber j) : qOf u ∈ Q0 := (data u).property.2.2.1
    have heqOf (u : Fiber j) :
        f (omega₁ * (u : G)) =
          rightConjugateElem (omega j * qOf u) (kOf u * wOf u) :=
      (data u).property.2.2.2
    let phi : Fiber j → W := fun u => ⟨wOf u, hwOf u⟩
    have hphi_inj : Function.Injective phi := by
      intro u v huv
      by_contra huv_ne
      have huv_val : (u : G) ≠ (v : G) := fun huv_val =>
        huv_ne (Subtype.ext huv_val)
      have hw_eq : wOf u = wOf v := congrArg Subtype.val huv
      have hkdiff : (kOf u)⁻¹ * kOf v ∈ K :=
        K.mul_mem (K.inv_mem (hkOf u)) (hkOf v)
      have hcomm : ((kOf u)⁻¹ * kOf v) * wOf u =
          wOf u * ((kOf u)⁻¹ * kOf v) :=
        Subgroup.mem_centralizer_iff.mp (hW_centralizes_K (hwOf u))
          ((kOf u)⁻¹ * kOf v) hkdiff
      have hdcos : kOf v * wOf v =
          (kOf u * wOf u) * ((kOf u)⁻¹ * kOf v) := by
        rw [← hw_eq]
        calc
          kOf v * wOf u = kOf u * ((kOf u)⁻¹ * kOf v) * wOf u := by group
          _ = kOf u * (wOf u * ((kOf u)⁻¹ * kOf v)) := by
            rw [← hcomm]
            group
          _ = (kOf u * wOf u) * ((kOf u)⁻¹ * kOf v) := by group
      have hd_u : kOf u * wOf u ∈ D :=
        D.mul_mem (hsec2.K_le_D (hkOf u)) (hW_le_D (hwOf u))
      have hd_v : kOf v * wOf v ∈ D :=
        D.mul_mem (hsec2.K_le_D (hkOf v)) (hW_le_D (hwOf v))
      have hnot := claim_7 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        omega₁ (omega j) (u : G) (v : G) (qOf u) (qOf v)
        (kOf u * wOf u) (kOf v * wOf v)
        homega₁_data.1 homega₁_data.2 homegaj.1 homegaj.2
        u.property.1 v.property.1 (hqOf u) (hqOf v) hd_u hd_v huv_val
        (heqOf u) (heqOf v)
      exact hnot ⟨(kOf u)⁻¹ * kOf v, hkdiff, hdcos⟩
    by_cases hj_eq : j = b
    · have hphi_ne_one : ∀ u : Fiber j, phi u ≠ 1 := by
        intro u hphi_one
        have hw_one : wOf u = 1 := congrArg Subtype.val hphi_one
        have hdK : kOf u * wOf u ∈ K := by simpa [hw_one] using hkOf u
        have hdD : kOf u * wOf u ∈ D := hsec2.K_le_D hdK
        have heq_u :
            f (omega₁ * (u : G)) =
              rightConjugateElem (omega₁ * qOf u) (kOf u * wOf u) := by
          simpa [hj_eq, ← homega₁] using heqOf u
        exact hK_forbidden (u : G) (qOf u) (kOf u * wOf u)
          u.property.1 (hqOf u) hdD hdK heq_u
      let phi0 : Fiber j → {w : W // w ≠ 1} := fun u =>
        ⟨phi u, hphi_ne_one u⟩
      have hphi0_inj : Function.Injective phi0 := fun u v huv =>
        hphi_inj (congrArg Subtype.val huv)
      have hcardWne : Nat.card {w : W // w ≠ 1} = Nat.card W - 1 := by
        letI := Fintype.ofFinite W
        calc
          Nat.card {w : W // w ≠ 1} = Fintype.card {w : W // w ≠ 1} := by simp
          _ = Fintype.card W - 1 := by
            simp
          _ = Nat.card W - 1 := by simp
      have hle := Nat.card_le_card_of_injective phi0 hphi0_inj
      simpa [Fiber, hj_eq, hWorder, hcardWne] using hle
    · have hle := Nat.card_le_card_of_injective phi hphi_inj
      simpa [hj_eq, hWorder] using hle
  let J := {j : ℕ // j ∈ Finset.Icc 1 n}
  let AllFib := Σ j : J, Fiber j
  let CoverData (q : Q0) := {p : ℕ × G × G //
    p.1 ∈ Finset.Icc 1 n ∧ p.2.1 ∈ KW ∧ p.2.2 ∈ Q0 ∧
      f (omega₁ * (q : G)) =
        rightConjugateElem (omega p.1) p.2.1 * p.2.2}
  have hcover_nonempty : ∀ q : Q0, Nonempty (CoverData q) := by
    intro q
    have hprodQ : omega₁ * (q : G) ∈ Q :=
      Q.mul_mem homega₁_data.1 (hsec2.Q0_le_Q q.property)
    have hprod1 : omega₁ * (q : G) ≠ 1 := by
      intro hprod
      apply homega₁_data.2
      have homega_eq : omega₁ = (q : G)⁻¹ := eq_inv_of_mul_eq_one_left hprod
      rw [homega_eq]
      exact Q0.inv_mem q.property
    have hfprodQ := (hf_mem _ hprodQ hprod1).1
    have hfprod0 : f (omega₁ * (q : G)) ∉ Q0 := by
      intro hfprodQ0
      exact homega₁_data.2 <| by
        have hprodQ0 :=
          (claim_4_f_mem_Q0_iff H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
            htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
            hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
            (omega₁ * (q : G)) hprodQ hprod1).1 hfprodQ0
        have homega_eq : omega₁ = (omega₁ * (q : G)) * (q : G)⁻¹ := by simp [mul_assoc]
        rw [homega_eq]
        exact Q0.mul_mem hprodQ0 (Q0.inv_mem q.property)
    rcases hcomplete _ hfprodQ hfprod0 with
      ⟨j, hj1, hjn, d, q0, hdKW, hq0, heq⟩
    exact ⟨⟨(j, d, q0), Finset.mem_Icc.mpr ⟨hj1, hjn⟩, hdKW, hq0, heq⟩⟩
  let cover (q : Q0) : CoverData q := Classical.choice (hcover_nonempty q)
  let embed : Q0 → AllFib := fun q =>
    ⟨⟨(cover q).val.1, (cover q).property.1⟩,
      ⟨q, q.property,
        ⟨(cover q).val.2.1, (cover q).val.2.2,
          (cover q).property.2.1, (cover q).property.2.2.1,
          (cover q).property.2.2.2⟩⟩⟩
  let forget : AllFib → Q0 := fun p => ⟨p.2, p.2.property.1⟩
  letI : Fintype J := by
    dsimp [J]
    infer_instance
  letI : Finite AllFib := by
    dsimp [AllFib]
    infer_instance
  have hleft : Function.LeftInverse forget embed := by
    intro q
    apply Subtype.ext
    rfl
  have hcard_lower : Nat.card Q0 ≤ Nat.card AllFib :=
    Nat.card_le_card_of_injective embed hleft.injective
  have hsigma_sum : Nat.card AllFib =
      Finset.sum (Finset.Icc 1 n) (fun j => Nat.card (Fiber j)) := by
    dsimp [AllFib]
    rw [Nat.card_sigma]
    symm
    exact Finset.sum_subtype (Finset.Icc 1 n) (fun _ => Iff.rfl)
      (fun j => Nat.card (Fiber j))
  have hpointwise : ∀ j ∈ Finset.Icc 1 n,
      Nat.card (Fiber j) ≤ (if j = b then m - 1 else m) := by
    intro j hj
    exact hupper j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  have hsum_le := Finset.sum_le_sum hpointwise
  have hupper_sum :
      Finset.sum (Finset.Icc 1 n) (fun j => (if j = b then m - 1 else m)) =
        Nat.card Q0 := claim_8_upper_sum_of_product_eq_succ m n (Nat.card Q0) b hn
          (Finset.mem_Icc.mpr hb)
  have hsum_eq :
      Finset.sum (Finset.Icc 1 n) (fun j => Nat.card (Fiber j)) = Nat.card Q0 := by
    apply le_antisymm
    · simpa [hupper_sum] using hsum_le
    · rw [← hsigma_sum]
      exact hcard_lower
  have hsums_eq :
      Finset.sum (Finset.Icc 1 n) (fun j => Nat.card (Fiber j)) =
        Finset.sum (Finset.Icc 1 n) (fun j => (if j = b then m - 1 else m)) :=
    hsum_eq.trans hupper_sum.symm
  have hall_eq := (Finset.sum_eq_sum_iff_of_le hpointwise).1 hsums_eq
  change Nat.card (Fiber i) = (if i = b then m - 1 else m)
  exact hall_eq i (Finset.mem_Icc.mpr hi)

/-- For two distinct orbit representatives, the full Claim (8) fiber contains
a crossing whose conjugating element lies in `K`.  This is the construction
used immediately before Claim (19) in the source. -/
public theorem claim_8_exists_crossing_in_K
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s omega₁ : G) (f g h : G → G)
    (m n b i : ℕ) (omega : ℕ → G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W)
    (hWorder : m = Nat.card W)
    (hn : n * m = Nat.card Q0 + 1)
    (hb : 1 ≤ b ∧ b ≤ n)
    (hi : 1 ≤ i ∧ i ≤ n)
    (hbi : i ≠ b)
    (horbit_representatives :
      (∀ j : ℕ, 1 ≤ j → j ≤ n → omega j ∈ Q ∧ omega j ∉ Q0) ∧
      (∀ x : G, x ∈ Q → x ∉ Q0 →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
          ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
            x = rightConjugateElem (omega j) d * q0) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          omega j = rightConjugateElem (omega k) d * q0) → j = k))
    (homega₁ : omega₁ = omega b) :
    ∃ x y k : G, x ∈ Q0 ∧ y ∈ Q0 ∧ k ∈ K ∧
      f (omega₁ * x) = rightConjugateElem (omega i * y) k := by
  classical
  have hsec2 := hsection3.1
  have homega₁_data : omega₁ ∈ Q ∧ omega₁ ∉ Q0 := by
    rw [homega₁]
    exact horbit_representatives.1 b hb.1 hb.2
  have homegai := horbit_representatives.1 i hi.1 hi.2
  have hV_le_D : V ≤ D := by
    rw [hsec2.V_eq]
    exact inf_le_left
  have hW_le_D : W ≤ D := hsec2.W_le_V.trans hV_le_D
  have hW_centralizes_K : W ≤ Subgroup.centralizer (K : Set G) := by
    intro w hwW
    rw [hsec2.W_eq] at hwW
    exact hwW.2
  have hW_normalizes_K : W ≤ Subgroup.normalizer (K : Set G) :=
    hW_centralizes_K.trans (centralizer_le_normalizer K)
  have hKW_decomp : ∀ d : G, d ∈ KW →
      ∃ k w : G, k ∈ K ∧ w ∈ W ∧ d = k * w := by
    intro d hdKW
    have hdSup : d ∈ K ⊔ W := by simpa [hKW] using hdKW
    change d ∈ ((K ⊔ W : Subgroup G) : Set G) at hdSup
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K W hW_normalizes_K] at hdSup
    rcases Set.mem_mul.mp hdSup with ⟨k, hkK, w, hwW, hkw⟩
    exact ⟨k, w, hkK, hwW, hkw.symm⟩
  have hQ0_conj_D : ∀ q a : G, q ∈ Q0 → a ∈ D →
      rightConjugateElem q a ∈ Q0 := by
    intro q a hqQ0 haD
    have haH := PFchapter4section1.rankOneSplit_D_le_M hD_eq haD
    rcases (hsec2.Q0_def q).1 hqQ0 with rfl | ⟨hqH, hqI⟩
    · simp [rightConjugateElem]
    · exact (hsec2.Q0_def _).2 (Or.inr
        ⟨H.mul_mem (H.mul_mem (H.inv_mem haH) hqH) haH,
          isInvolution_rightConjugateElem hqI⟩)
  let Fiber := {x : G // x ∈ Q0 ∧
    (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
      f (omega₁ * x) = rightConjugateElem (omega i) d * q0)}
  have hcardFiber : Nat.card Fiber = m := by
    have hcard := claim_8 H D Q K V W Q0 S Q1 KW t s omega₁ f g h
      m n b i omega hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer
      ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D
      hf_mem hg_mem hh_mem hcanonical_eq hKW hWorder hn hb hi
      horbit_representatives homega₁
    simpa [Fiber, hbi] using hcard
  let Data (u : Fiber) := {p : G × G × G //
    p.1 ∈ K ∧ p.2.1 ∈ W ∧ p.2.2 ∈ Q0 ∧
      f (omega₁ * (u : G)) =
        rightConjugateElem (omega i * p.2.2) (p.1 * p.2.1)}
  have hdata_nonempty : ∀ u : Fiber, Nonempty (Data u) := by
    intro u
    rcases u.property.2 with ⟨d, q0, hdKW, hq0, hu⟩
    rcases hKW_decomp d hdKW with ⟨k, w, hkK, hwW, rfl⟩
    let y := rightConjugateElem q0 (k * w)⁻¹
    have hkwD : k * w ∈ D :=
      D.mul_mem (hsec2.K_le_D hkK) (hW_le_D hwW)
    have hyQ0 : y ∈ Q0 := hQ0_conj_D q0 (k * w)⁻¹ hq0 (D.inv_mem hkwD)
    refine ⟨⟨(k, w, y), hkK, hwW, hyQ0, ?_⟩⟩
    calc
      f (omega₁ * (u : G)) =
          rightConjugateElem (omega i) (k * w) * q0 := hu
      _ = rightConjugateElem (omega i * y) (k * w) := by
        simp [y, rightConjugateElem, mul_assoc]
  let data (u : Fiber) : Data u := Classical.choice (hdata_nonempty u)
  let kOf (u : Fiber) : G := (data u).val.1
  let wOf (u : Fiber) : G := (data u).val.2.1
  let qOf (u : Fiber) : G := (data u).val.2.2
  have hkOf (u : Fiber) : kOf u ∈ K := (data u).property.1
  have hwOf (u : Fiber) : wOf u ∈ W := (data u).property.2.1
  have hqOf (u : Fiber) : qOf u ∈ Q0 := (data u).property.2.2.1
  have heqOf (u : Fiber) :
      f (omega₁ * (u : G)) =
        rightConjugateElem (omega i * qOf u) (kOf u * wOf u) :=
    (data u).property.2.2.2
  let phi : Fiber → W := fun u => ⟨wOf u, hwOf u⟩
  have hphi_inj : Function.Injective phi := by
    intro u v huv
    by_contra huv_ne
    have huv_val : (u : G) ≠ (v : G) := fun huv_val =>
      huv_ne (Subtype.ext huv_val)
    have hw_eq : wOf u = wOf v := congrArg Subtype.val huv
    have hkdiff : (kOf u)⁻¹ * kOf v ∈ K :=
      K.mul_mem (K.inv_mem (hkOf u)) (hkOf v)
    have hcomm : ((kOf u)⁻¹ * kOf v) * wOf u =
        wOf u * ((kOf u)⁻¹ * kOf v) :=
      Subgroup.mem_centralizer_iff.mp (hW_centralizes_K (hwOf u))
        ((kOf u)⁻¹ * kOf v) hkdiff
    have hdcos : kOf v * wOf v =
        (kOf u * wOf u) * ((kOf u)⁻¹ * kOf v) := by
      rw [← hw_eq]
      calc
        kOf v * wOf u = kOf u * ((kOf u)⁻¹ * kOf v) * wOf u := by group
        _ = kOf u * (wOf u * ((kOf u)⁻¹ * kOf v)) := by
          rw [← hcomm]
          group
        _ = (kOf u * wOf u) * ((kOf u)⁻¹ * kOf v) := by group
    have hd_u : kOf u * wOf u ∈ D :=
      D.mul_mem (hsec2.K_le_D (hkOf u)) (hW_le_D (hwOf u))
    have hd_v : kOf v * wOf v ∈ D :=
      D.mul_mem (hsec2.K_le_D (hkOf v)) (hW_le_D (hwOf v))
    have hnot := claim_7 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      omega₁ (omega i) (u : G) (v : G) (qOf u) (qOf v)
      (kOf u * wOf u) (kOf v * wOf v)
      homega₁_data.1 homega₁_data.2 homegai.1 homegai.2
      u.property.1 v.property.1 (hqOf u) (hqOf v) hd_u hd_v huv_val
      (heqOf u) (heqOf v)
    exact hnot ⟨(kOf u)⁻¹ * kOf v, hkdiff, hdcos⟩
  letI := Fintype.ofFinite Fiber
  letI := Fintype.ofFinite W
  have hphi_bij : Function.Bijective phi :=
    (Fintype.bijective_iff_injective_and_card phi).2 ⟨hphi_inj, by
      simpa [Nat.card_eq_fintype_card] using hcardFiber.trans hWorder⟩
  rcases hphi_bij.2 (1 : W) with ⟨u, hu⟩
  have hw_one : wOf u = 1 := congrArg Subtype.val hu
  exact ⟨u, qOf u, kOf u, u.property.1, hqOf u, hkOf u, by
    simpa [hw_one] using heqOf u⟩

end PFchapter4section2
end CFSG.BenderSuzuki
