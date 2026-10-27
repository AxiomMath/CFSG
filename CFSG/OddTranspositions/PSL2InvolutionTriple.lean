module

public import CFSG.OddTranspositions.SevenWreathInstantiate

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.BenderSuzuki CFSG.BenderSuzuki.External CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem odd_orderOf_mul_of_centralizer_inf_bot {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (han : a ≠ 1) (hbn : b ≠ 1)
    {Q Q' : Subgroup G}
    (hca : Subgroup.centralizer ({a} : Set G) = Q)
    (hcb : Subgroup.centralizer ({b} : Set G) = Q')
    (hinf : Q ⊓ Q' = ⊥) (hnc : ¬ Commute a b) :
    Odd (orderOf (a * b)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨k, hk⟩ := hodd
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hba : b * a = (a * b)⁻¹ := by
    rw [mul_inv_rev, hai, hbi]
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hk
    have := orderOf_pos (a * b)
    omega
  set z : G := (a * b) ^ k with hz
  have hz2 : z * z = 1 := by
    rw [hz, ← pow_two, ← pow_mul, show k * 2 = k + k by omega, ← hk]
    exact pow_orderOf_eq_one _
  have hz1 : z ≠ 1 := by
    intro h1
    have hord : orderOf z = 2 := by
      rw [hz, orderOf_pow, hk]
      have hgcd : Nat.gcd (k + k) k = k := Nat.gcd_eq_right ⟨2, by ring⟩
      rw [hgcd, show k + k = k * 2 by ring,
        Nat.mul_div_cancel_left 2 (Nat.pos_of_ne_zero hk0)]
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hza : Commute z a := by
    rw [commute_iff_eq]
    have hconj : a * z * a = z := by
      rw [hz]
      have h1 : a * (a * b) ^ k * a = (b * a) ^ k := by
        have h := conj_pow (a := a) (b := a * b) (i := k)
        rw [hai] at h
        rw [← h]
        congr 1
        calc a * (a * b) * a = (a * a) * (b * a) := by group
          _ = b * a := by rw [ha, one_mul]
      rw [h1]
      have h2 : (b * a) ^ k = ((a * b) ^ k)⁻¹ := by
        rw [hba, ← inv_pow]
      rw [h2]
      exact inv_eq_of_mul_eq_one_right hz2
    calc z * a = (a * a) * z * a := by rw [ha, one_mul]
      _ = a * (a * z * a) := by group
      _ = a * z := by rw [hconj]
  have hzb : Commute z b := by
    rw [commute_iff_eq]
    have hconj : b * z * b = z := by
      rw [hz]
      have h1 : b * (a * b) ^ k * b = (b * a) ^ k := by
        have h := conj_pow (a := b) (b := a * b) (i := k)
        rw [hbi] at h
        rw [← h]
        congr 1
        calc b * (a * b) * b = b * a * (b * b) := by group
          _ = b * a := by rw [hb, mul_one]
      rw [h1]
      have h2 : (b * a) ^ k = ((a * b) ^ k)⁻¹ := by
        rw [hba, ← inv_pow]
      rw [h2]
      exact inv_eq_of_mul_eq_one_right hz2
    calc z * b = (b * b) * z * b := by rw [hb, one_mul]
      _ = b * (b * z * b) := by group
      _ = b * z := by rw [hconj]
  have hzQ : z ∈ Q := by
    rw [← hca, Subgroup.mem_centralizer_singleton_iff]
    exact hza.eq
  have hzQ' : z ∈ Q' := by
    rw [← hcb, Subgroup.mem_centralizer_singleton_iff]
    exact hzb.eq
  have : z ∈ Q ⊓ Q' := ⟨hzQ, hzQ'⟩
  rw [hinf] at this
  exact hz1 (by simpa using this)

open CFSG.CGT.Timmesfeld75 in
theorem exists_involution_triple_psl2 {m : ℕ} (hm : 2 ≤ m) :
    ∃ s₁ s₂ s₃ : PSL2Model m,
      s₁ * s₁ = 1 ∧ s₂ * s₂ = 1 ∧ s₃ * s₃ = 1 ∧
      s₁ ≠ s₂ ∧ Commute s₁ s₂ ∧
      ¬ Commute s₁ s₃ ∧ ¬ Commute s₂ s₃ ∧
      Odd (orderOf (s₁ * s₃)) ∧ 1 < orderOf (s₁ * s₃) ∧
      Odd (orderOf (s₂ * s₃)) ∧ 1 < orderOf (s₂ * s₃) ∧
      Odd (orderOf (s₁ * s₂ * s₃)) ∧ 1 < orderOf (s₁ * s₂ * s₃) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hev : Even (2 ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  have hq4 : 4 ≤ 2 ^ m := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hoddq1 : Odd (2 ^ m + 1) := hev.add_one
  have hoddm1 : Odd (2 ^ m - 1) := Nat.Even.sub_odd (by omega) hev odd_one
  have hgcd : Nat.gcd (2 ^ m - 1) 2 = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_right.mpr hoddm1)
  obtain ⟨T, w, hTcyc, hTcard, hwN, hwT, hw2, hwinv, -, -⟩ :=
    huppert_II_8_4_nonsplit_torus_reflection_data (F := GaloisField 2 m) hF
  rw [hF, hgcd, Nat.div_one] at hTcard
  haveI : IsCyclic T := hTcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  have hgo : orderOf (g : PSL2Model m) = 2 ^ m + 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hTcard]
  have hw1 : w ≠ 1 := fun h => hwT (h ▸ T.one_mem)
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwg : w * (g : PSL2Model m) * w = (g : PSL2Model m)⁻¹ := by
    have := hwinv g g.2
    rwa [hwi] at this
  have hgw : (g : PSL2Model m) * w = w * (g : PSL2Model m)⁻¹ := by
    calc (g : PSL2Model m) * w = (w * w) * ((g : PSL2Model m) * w) := by
          rw [hw2, one_mul]
      _ = w * (w * (g : PSL2Model m) * w) := by group
      _ = w * (g : PSL2Model m)⁻¹ := by rw [hwg]
  have hs3sq : (w * g) * (w * g) = 1 := by
    calc (w * g) * (w * g) = w * ((g : PSL2Model m) * w) * g := by group
      _ = w * (w * (g : PSL2Model m)⁻¹) * g := by rw [hgw]
      _ = (w * w) * ((g : PSL2Model m)⁻¹ * g) := by group
      _ = 1 := by rw [hw2, inv_mul_cancel, mul_one]
  have h13 : w * (w * g) = (g : PSL2Model m) := by rw [← mul_assoc, hw2, one_mul]
  have hg1 : (g : PSL2Model m) ≠ 1 := by
    intro h
    have : orderOf (g : PSL2Model m) = 1 := by rw [h, orderOf_one]
    rw [hgo] at this
    omega
  have hs3ne1 : w * g ≠ 1 := by
    intro h
    apply hwT
    have hw_eq : w = (g : PSL2Model m)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [hw_eq]
    exact T.inv_mem g.2
  have hnc13 : ¬ Commute w (w * g) := by
    intro hc
    have hgeq : (g : PSL2Model m) = (g : PSL2Model m)⁻¹ := by
      calc (g : PSL2Model m) = w * (w * g) := h13.symm
        _ = (w * g) * w := hc.eq
        _ = (g : PSL2Model m)⁻¹ := hwg
    have hg2 : (g : PSL2Model m) * g = 1 := by
      nth_rewrite 2 [hgeq]
      exact mul_inv_cancel _
    have hdvd : orderOf (g : PSL2Model m) ∣ 2 := by
      have hg2' : (g : PSL2Model m) ^ 2 = 1 := by rw [pow_two]; exact hg2
      exact orderOf_dvd_of_pow_eq_one hg2'
    rw [hgo] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
    · omega
    · rw [h] at hoddq1
      obtain ⟨k, hk⟩ := hoddq1
      omega
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  have hP0 : IsPGroup 2 (Subgroup.zpowers w) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hwo]
    norm_num
  obtain ⟨P, hPle⟩ := hP0.exists_le_sylow
  have hwP : w ∈ (P : Subgroup (PSL2Model m)) := hPle (Subgroup.mem_zpowers w)
  have hL2P : IsL2Pair (PSL2Model m) (P : Subgroup (PSL2Model m)) (2 ^ m) :=
    IsL2Pair.of_psl_sylow (by omega) ⟨MulEquiv.refl _⟩ P
  have hcardP : Nat.card (P : Subgroup (PSL2Model m)) = 2 ^ m := by
    simpa using hL2P.card_eq
  have hPhab : IsElemAbelian 2 (P : Subgroup (PSL2Model m)) := hL2P.isElemAbelian
  have hs3o : orderOf (w * g) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hs3sq) hs3ne1
  have hP'0 : IsPGroup 2 (Subgroup.zpowers (w * g)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hs3o]
    norm_num
  obtain ⟨P', hP'le⟩ := hP'0.exists_le_sylow
  have hs3P' : (w * g) ∈ (P' : Subgroup (PSL2Model m)) :=
    hP'le (Subgroup.mem_zpowers _)
  have hPP' : (P : Subgroup (PSL2Model m)) ≠ (P' : Subgroup (PSL2Model m)) := by
    intro hEq
    have hmem : (w * g) ∈ (P : Subgroup (PSL2Model m)) := hEq ▸ hs3P'
    have hcomm : Commute w (w * g) :=
      (commute_iff_eq _ _).mpr (elemAbelian_mul_comm hPhab hwP hmem)
    exact hnc13 hcomm
  obtain ⟨c, hc⟩ := hL2P.exists_conj_eq_sylow P'
  have hcN : c ∉ Subgroup.normalizer ((P : Subgroup (PSL2Model m)) : Set _) := by
    intro hmem
    apply hPP'
    have hfix : conjSubgroup c (P : Subgroup (PSL2Model m)) = (P : Subgroup (PSL2Model m)) :=
      mem_normalizer_iff_conjSubgroup_eq.mp hmem
    exact hfix.symm.trans hc
  have hinf : (P : Subgroup (PSL2Model m)) ⊓ (P' : Subgroup (PSL2Model m)) = ⊥ := by
    have := hL2P.inf_conj_eq_bot hcN
    rwa [hc] at this
  have hca_w : Subgroup.centralizer ({w} : Set (PSL2Model m)) = (P : Subgroup (PSL2Model m)) :=
    hL2P.centralizer_eq hwP hw1
  have hca_s3 : Subgroup.centralizer ({(w * g)} : Set (PSL2Model m)) = (P' : Subgroup (PSL2Model m)) := by
    have h := hL2P.centralizer_eq_conj (g := c) (x := w * g) (by rw [hc]; exact hs3P') hs3ne1
    rwa [hc] at h
  have hex : ∃ s₂ ∈ (P : Subgroup (PSL2Model m)), s₂ ≠ 1 ∧ s₂ ≠ w := by
    by_contra h
    push_neg at h
    have hsurj : Function.Surjective
        (fun b : Bool => (if b then (⟨w, hwP⟩ : (P : Subgroup (PSL2Model m))) else 1)) := by
      intro x
      by_cases hx1 : x = 1
      · refine ⟨false, ?_⟩
        apply Subtype.ext
        simpa using congrArg (fun y : (P : Subgroup (PSL2Model m)) => (y : PSL2Model m)) hx1.symm
      · have hx1' : (x : PSL2Model m) ≠ 1 := fun h => hx1 (Subtype.ext h)
        have hxw : (x : PSL2Model m) = w := h x x.2 hx1'
        refine ⟨true, ?_⟩
        apply Subtype.ext
        simpa using hxw.symm
    have hle : Nat.card (P : Subgroup (PSL2Model m)) ≤ 2 := by
      simpa using Nat.card_le_card_of_surjective _ hsurj
    rw [hcardP] at hle
    omega
  obtain ⟨s₂, hs2P, hs2ne1, hs2new⟩ := hex
  have hs2sq : s₂ * s₂ = 1 := by
    have h := hPhab.2 s₂ hs2P
    rwa [pow_two] at h
  have hs12 : Commute w s₂ :=
    (commute_iff_eq _ _).mpr (elemAbelian_mul_comm hPhab hwP hs2P)
  have hne12 : w ≠ s₂ := fun h => hs2new h.symm
  have hs3notP : (w * g) ∉ (P : Subgroup (PSL2Model m)) := by
    intro hmem
    have hmem' : (w * g) ∈ (P : Subgroup (PSL2Model m)) ⊓ (P' : Subgroup (PSL2Model m)) := ⟨hmem, hs3P'⟩
    rw [hinf] at hmem'
    exact hs3ne1 (by simpa using hmem')
  have hnc23 : ¬ Commute s₂ (w * g) := by
    intro hc2
    have hmem : s₂ ∈ (P' : Subgroup (PSL2Model m)) := by
      rw [← hca_s3, Subgroup.mem_centralizer_singleton_iff]
      exact hc2.eq
    have hmem' : s₂ ∈ (P : Subgroup (PSL2Model m)) ⊓ (P' : Subgroup (PSL2Model m)) := ⟨hs2P, hmem⟩
    rw [hinf] at hmem'
    exact hs2ne1 (by simpa using hmem')
  have hca_s2 : Subgroup.centralizer ({s₂} : Set (PSL2Model m)) = (P : Subgroup (PSL2Model m)) :=
    hL2P.centralizer_eq hs2P hs2ne1
  have hodd23 : Odd (orderOf (s₂ * (w * g))) :=
    odd_orderOf_mul_of_centralizer_inf_bot hs2sq hs3sq hs2ne1 hs3ne1 hca_s2 hca_s3 hinf hnc23
  have h23gt : 1 < orderOf (s₂ * (w * g)) := by
    have hne : s₂ * (w * g) ≠ 1 := by
      intro h
      have hs2eq : s₂ = (w * g) := by
        have h' : s₂ = ((w * g))⁻¹ := eq_inv_of_mul_eq_one_left h
        rwa [inv_eq_of_mul_eq_one_right hs3sq] at h'
      exact hs3notP (hs2eq ▸ hs2P)
    have hpos : 0 < orderOf (s₂ * (w * g)) := orderOf_pos _
    have hne1 : orderOf (s₂ * (w * g)) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    omega
  have ha_sq : (w * s₂) * (w * s₂) = 1 := by
    rw [commute_iff_eq] at hs12
    calc (w * s₂) * (w * s₂) = w * (s₂ * w) * s₂ := by group
      _ = w * (w * s₂) * s₂ := by rw [← hs12]
      _ = (w * w) * (s₂ * s₂) := by group
      _ = 1 := by rw [hw2, hs2sq, mul_one]
  have haP : (w * s₂) ∈ (P : Subgroup (PSL2Model m)) := P.mul_mem hwP hs2P
  have ha_ne1 : w * s₂ ≠ 1 := by
    intro h
    apply hs2new
    have h' : w = s₂ := by
      have := eq_inv_of_mul_eq_one_left h
      rwa [inv_eq_of_mul_eq_one_right hs2sq] at this
    exact h'.symm
  have ha_notP' : (w * s₂) ∉ (P' : Subgroup (PSL2Model m)) := by
    intro hmem
    have hmem' : (w * s₂) ∈ (P : Subgroup (PSL2Model m)) ⊓ (P' : Subgroup (PSL2Model m)) := ⟨haP, hmem⟩
    rw [hinf] at hmem'
    exact ha_ne1 (by simpa using hmem')
  have hca_a : Subgroup.centralizer ({(w * s₂)} : Set (PSL2Model m)) = (P : Subgroup (PSL2Model m)) :=
    hL2P.centralizer_eq haP ha_ne1
  have hnc_a3 : ¬ Commute (w * s₂) (w * g) := by
    intro hc3
    apply ha_notP'
    rw [← hca_s3, Subgroup.mem_centralizer_singleton_iff]
    exact hc3.eq
  have hoddg : Odd (orderOf ((w * s₂) * (w * g))) :=
    odd_orderOf_mul_of_centralizer_inf_bot ha_sq hs3sq ha_ne1 hs3ne1 hca_a hca_s3 hinf hnc_a3
  have hgtg : 1 < orderOf ((w * s₂) * (w * g)) := by
    have hne : (w * s₂) * (w * g) ≠ 1 := by
      intro h
      have heq : w * s₂ = w * g := by
        have h' : w * s₂ = ((w * g))⁻¹ := eq_inv_of_mul_eq_one_left h
        rwa [inv_eq_of_mul_eq_one_right hs3sq] at h'
      exact ha_notP' (heq ▸ hs3P')
    have hpos : 0 < orderOf ((w * s₂) * (w * g)) := orderOf_pos _
    have hne1 : orderOf ((w * s₂) * (w * g)) ≠ 1 :=
      fun h => hne (orderOf_eq_one_iff.mp h)
    omega
  refine ⟨w, s₂, w * g, hw2, hs2sq, hs3sq, hne12, hs12, hnc13, hnc23,
    ?_, ?_, hodd23, h23gt, hoddg, hgtg⟩
  · rw [h13, hgo]
    exact hoddq1
  · rw [h13, hgo]
    omega

theorem exists_involution_triple_of_mulEquiv {L : Type} [Group L] [Finite L] {m : ℕ}
    (hm : 2 ≤ m) (e : L ≃* PSL2Model m) :
    ∃ s₁ s₂ s₃ : L,
      s₁ * s₁ = 1 ∧ s₂ * s₂ = 1 ∧ s₃ * s₃ = 1 ∧
      s₁ ≠ s₂ ∧ Commute s₁ s₂ ∧
      ¬ Commute s₁ s₃ ∧ ¬ Commute s₂ s₃ ∧
      Odd (orderOf (s₁ * s₃)) ∧ 1 < orderOf (s₁ * s₃) ∧
      Odd (orderOf (s₂ * s₃)) ∧ 1 < orderOf (s₂ * s₃) ∧
      Odd (orderOf (s₁ * s₂ * s₃)) ∧ 1 < orderOf (s₁ * s₂ * s₃) := by
  obtain ⟨a₁, a₂, a₃, h1, h2, h3, hne, hc, hnc1, hnc2, ho1, hg1, ho2, hg2, ho3, hg3⟩ :=
    exists_involution_triple_psl2 hm
  refine ⟨e.symm a₁, e.symm a₂, e.symm a₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg (fun x => e.symm x) h1
  · simpa using congrArg (fun x => e.symm x) h2
  · simpa using congrArg (fun x => e.symm x) h3
  · intro h
    exact hne (e.symm.injective h)
  · exact hc.map e.symm
  · intro h
    exact hnc1 (by simpa using h.map e)
  · intro h
    exact hnc2 (by simpa using h.map e)
  · have hord : orderOf (e.symm a₁ * e.symm a₃) = orderOf (a₁ * a₃) := by
      rw [← map_mul, MulEquiv.orderOf_eq]
    rw [hord]
    exact ho1
  · have hord : orderOf (e.symm a₁ * e.symm a₃) = orderOf (a₁ * a₃) := by
      rw [← map_mul, MulEquiv.orderOf_eq]
    rw [hord]
    exact hg1
  · have hord : orderOf (e.symm a₂ * e.symm a₃) = orderOf (a₂ * a₃) := by
      rw [← map_mul, MulEquiv.orderOf_eq]
    rw [hord]
    exact ho2
  · have hord : orderOf (e.symm a₂ * e.symm a₃) = orderOf (a₂ * a₃) := by
      rw [← map_mul, MulEquiv.orderOf_eq]
    rw [hord]
    exact hg2
  · have hord : orderOf (e.symm a₁ * e.symm a₂ * e.symm a₃) = orderOf (a₁ * a₂ * a₃) := by
      rw [← map_mul, ← map_mul, MulEquiv.orderOf_eq]
    rw [hord]
    exact ho3
  · have hord : orderOf (e.symm a₁ * e.symm a₂ * e.symm a₃) = orderOf (a₁ * a₂ * a₃) := by
      rw [← map_mul, ← map_mul, MulEquiv.orderOf_eq]
    rw [hord]
    exact hg3

theorem localSecond_fails_of_wreathData {D : Set G}
    (hS : Setup G D) {M : Subgroup G}
    (W : WreathData G D M) : ¬ LocalSecond D := by
  obtain ⟨u, hu⟩ := hS.nonempty
  obtain ⟨i, j, hij, hπ, -⟩ := W.swap u hu
  obtain ⟨f, hf, ⟨e⟩⟩ :=
    wreathData_factor_psl2 hS W i
  obtain ⟨a₁, a₂, a₃, h1, h2, h3, hne, hc, hnc1, hnc2, ho1, hg1, ho2, hg2, ho3, hg3⟩ :=
    exists_involution_triple_of_mulEquiv hf e
  let t₁ : G := (a₁ : W.S i)
  let t₂ : G := (a₂ : W.S i)
  let t₃ : G := (a₃ : W.S i)
  have ht1 : t₁ ∈ W.S i := a₁.2
  have ht2 : t₂ ∈ W.S i := a₂.2
  have ht3 : t₃ ∈ W.S i := a₃.2
  have ht1sq : t₁ * t₁ = 1 := by
    simpa [t₁] using congrArg (fun x : W.S i => (x : G)) h1
  have ht2sq : t₂ * t₂ = 1 := by
    simpa [t₂] using congrArg (fun x : W.S i => (x : G)) h2
  have ht3sq : t₃ * t₃ = 1 := by
    simpa [t₃] using congrArg (fun x : W.S i => (x : G)) h3
  have ht12 : Commute t₁ t₂ := hc.map (W.S i).subtype
  have htne : t₁ ≠ t₂ := by
    intro h
    exact hne (Subtype.ext h)
  have htnc1 : ¬ Commute t₁ t₃ := by
    intro h
    apply hnc1
    exact (commute_iff_eq _ _).mpr (Subtype.ext (by simpa [t₁, t₃] using h.eq))
  have htnc2 : ¬ Commute t₂ t₃ := by
    intro h
    apply hnc2
    exact (commute_iff_eq _ _).mpr (Subtype.ext (by simpa [t₂, t₃] using h.eq))
  have hto1 : Odd (orderOf (t₁ * t₃)) := by
    have hord : orderOf (t₁ * t₃) = orderOf (a₁ * a₃) := by
      simpa [t₁, t₃] using Subgroup.orderOf_coe (a₁ * a₃)
    rw [hord]
    exact ho1
  have htg1 : 1 < orderOf (t₁ * t₃) := by
    have hord : orderOf (t₁ * t₃) = orderOf (a₁ * a₃) := by
      simpa [t₁, t₃] using Subgroup.orderOf_coe (a₁ * a₃)
    rw [hord]
    exact hg1
  have hto2 : Odd (orderOf (t₂ * t₃)) := by
    have hord : orderOf (t₂ * t₃) = orderOf (a₂ * a₃) := by
      simpa [t₂, t₃] using Subgroup.orderOf_coe (a₂ * a₃)
    rw [hord]
    exact ho2
  have htg2 : 1 < orderOf (t₂ * t₃) := by
    have hord : orderOf (t₂ * t₃) = orderOf (a₂ * a₃) := by
      simpa [t₂, t₃] using Subgroup.orderOf_coe (a₂ * a₃)
    rw [hord]
    exact hg2
  have hto3 : Odd (orderOf (t₁ * t₂ * t₃)) := by
    have hord : orderOf (t₁ * t₂ * t₃) = orderOf (a₁ * a₂ * a₃) := by
      simpa [t₁, t₂, t₃] using Subgroup.orderOf_coe (a₁ * a₂ * a₃)
    rw [hord]
    exact ho3
  have htg3 : 1 < orderOf (t₁ * t₂ * t₃) := by
    have hord : orderOf (t₁ * t₂ * t₃) = orderOf (a₁ * a₂ * a₃) := by
      simpa [t₁, t₂, t₃] using Subgroup.orderOf_coe (a₁ * a₂ * a₃)
    rw [hord]
    exact hg3
  exact not_localSecond_of_wreathData hS W hu hij hπ ht1 ht2 ht3 ht1sq ht2sq ht3sq
    ht12 htne hto1 htg1 hto2 htg2 hto3 htg3

end CFSG.OddTranspositions



