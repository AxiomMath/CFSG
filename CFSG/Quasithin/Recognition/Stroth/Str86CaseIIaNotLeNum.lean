module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNatZ1
public import CFSG.Quasithin.MS93.S512GHolds
public import CFSG.Quasithin.H13.U3G2
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNotLeBasic
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaEquality

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_caseIIa_notLe_numerics
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ : ¬ Z1 L1 L2 S ≤ Q2 L1 L2 S) (hQ1 : Q1 L1 L2 S = Z1 L1 L2 S)
    {g : G} (hg : g ∈ u3H L1 L2 S)
    (hW : (2 ^ m) ^ 2 ≤ (Z1 L1 L2 S ⊓ conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S).relIndex
      ((Z1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ (conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S))) :
    m = k ∧
      (Z1 L1 L2 S ⊓ Q2 L1 L2 S).relIndex (Z1 L1 L2 S) = 2 ^ k ∧
      (Z1 L1 L2 S ⊓ conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S).relIndex
        (Z1 L1 L2 S ⊓ Q2 L1 L2 S) = 2 ^ k ∧
      (Z1 L1 L2 S ⊓ conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S).relIndex
        (conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S) = 2 ^ k ∧
      IsChiefSeriesFrom (L1 ⊔ S) (Z1 L1 L2 S) (Z1 L1 L2 S) 1 ∧
      ∀ t ∈ conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S,
        t ∉ Z1 L1 L2 S ⊓ conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S →
        Z1 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G) =
          Z1 L1 L2 S ⊓ conjSubgroup (Z1 L1 L2 S) g ⊓ Q2 L1 L2 S := by
  classical
  set Z : Subgroup G := Z1 L1 L2 S with hZdef
  set Q : Subgroup G := Q2 L1 L2 S with hQdef
  set Zg : Subgroup G := conjSubgroup Z g with hZgdef
  set X : Subgroup G := Z ⊓ Q with hXdef
  set X' : Subgroup G := Zg ⊓ Q with hX'def
  set Y : Subgroup G := Z ⊓ Zg ⊓ Q with hYdef
  set W : Subgroup G := X ⊔ X' with hWdef
  obtain ⟨hZQ, hXZ⟩ := str86_z1_sup_q2_of_not_le hF hSB hB2 hm hZ
  have hZQ' : Z ⊔ Q = S := by simpa [hZdef, hQdef] using hZQ
  have hXZ' : X.relIndex Z = 2 ^ m := by simpa [hXdef, hZdef, hQdef] using hXZ
  have hQS : Q ≤ S := by rw [← hZQ']; exact le_sup_right
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hZQ1 : Z ≤ Q1 L1 L2 S := by
    simpa [hZdef] using omegaOneCenterOf_le (Q1 L1 L2 S)
  have hZS : Z ≤ S := hZQ1.trans hQ1S
  have hZe : IsElemAbelian 2 Z := by
    simpa [hZdef] using SmithC27.isElemAbelian_omegaOneCenterOf (Q1 L1 L2 S)
  have hZge : IsElemAbelian 2 Zg := by
    simpa [hZgdef] using E3.isElemAbelian_conjSubgroup hZe g
  have hgH2 : g ∈ L2 ⊔ S := by
    have hle : u3H L1 L2 S ≤ L2 ⊔ S := sup_le le_sup_left (hQS.trans le_sup_right)
    exact hle hg
  have hgNQ : g ∈ Subgroup.normalizer (Q : Set G) := by
    have h := str86_l2sup_le_normalizer_q2 (L1 := L1) (L2 := L2) (S := S) hgH2
    simpa [hQdef] using h
  have hQconj : conjSubgroup Q g = Q :=
    (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer).mpr hgNQ
  have hX'conj : X' = conjSubgroup X g := by
    rw [hX'def, hXdef, hZgdef, E3.conjSubgroup_inf, hQconj]
  have hcardXX' : Nat.card X = Nat.card X' := by
    rw [hX'conj, E3.card_conjSubgroup]
  have hY_eq : Y = X ⊓ X' := by
    ext x
    rw [hYdef, hXdef, hX'def]
    simp only [Subgroup.mem_inf]
    tauto
  have hYX : Y ≤ X := hY_eq.le.trans inf_le_left
  have hYX' : Y ≤ X' := hY_eq.le.trans inf_le_right
  have hYZ : Y ≤ Z := by rw [hYdef]; exact inf_le_left.trans inf_le_left
  have hXZle : X ≤ Z := inf_le_left
  have hXQ : X ≤ Q := inf_le_right
  have hX'Zg : X' ≤ Zg := inf_le_left
  have hX'ZS : X' ≤ S := (inf_le_right : X' ≤ Q).trans hQS
  have hSZ : S ≤ Subgroup.normalizer (Z : Set G) := by
    intro s hs
    have h := str86_sup_normalizes_z1 hF hSB hk hFc hU3 (le_sup_right (a := L1) (b := S) hs)
    simpa [hZdef] using h
  have hSQ : S ≤ Subgroup.normalizer (Q : Set G) := by
    intro s hs
    have h := str86_l2sup_le_normalizer_q2 (L1 := L1) (L2 := L2) (S := S)
      (le_sup_right (a := L2) (b := S) hs)
    simpa [hQdef] using h
  have hSNX : S ≤ Subgroup.normalizer (X : Set G) := by
    intro s hs
    simpa [hXdef] using A4.mem_normalizer_inf (hSZ hs) (hSQ hs)
  have hX'NX : X' ≤ Subgroup.normalizer (X : Set G) :=
    ((inf_le_right : X' ≤ Q).trans hQS).trans hSNX
  have hX'Xsym : X'.relIndex X = X.relIndex X' :=
    CFSG.Quasithin.MS93.S512G.relIndex_comm_of_card_eq
      (Nat.card_pos (α := ↥X)).ne' hcardXX'.symm
  have hYrelX : Y.relIndex X = X'.relIndex X := by
    rw [hY_eq]
    exact Subgroup.inf_relIndex_left X X'
  have hYrelX' : Y.relIndex X' = X.relIndex X' := by
    rw [hY_eq]
    exact Subgroup.inf_relIndex_right X X'
  set s : ℕ := Y.relIndex X' with hsdef
  have hs : s = Y.relIndex X' := hsdef
  have hsX : Y.relIndex X = s := by
    rw [hYrelX, hX'Xsym, ← hYrelX', hs]
  have hXW : X.relIndex W = s := by
    have h := CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer
      (A := X') (B := X) hX'NX
    rw [show X' ⊔ X = W by rw [hWdef, sup_comm]] at h
    rw [h]
    rw [← hYrelX']
  have hX'W : X'.relIndex W = s := by
    have h := CFSG.Quasithin.H13.U3.relIndex_eq_of_card_eq
      (H₁ := X) (H₂ := X') (K := W) (le_sup_left : X ≤ W) (le_sup_right : X' ≤ W)
      hcardXX'
    rw [← h]
    exact hXW
  have hYW : Y.relIndex W = s * s := by
    have h := Subgroup.relIndex_mul_relIndex Y X' W hYX' (le_sup_right : X' ≤ W)
    rw [show Y.relIndex X' = s from hs.symm, hX'W] at h
    exact h.symm
  have hW' : (2 ^ m) ^ 2 ≤ Y.relIndex W := by
    simpa [hYdef, hWdef, hXdef, hX'def, hZdef, hZgdef, hQdef] using hW
  have hWb : (2 ^ m) ^ 2 ≤ s * s := by simpa [hYW] using hW'
  have hrm_le_s : 2 ^ m ≤ s :=
    (Nat.pow_le_pow_iff_left (show (2 : ℕ) ≠ 0 by norm_num)).mp (by simpa [pow_two] using hWb)
  have hm2 : 2 ≤ m := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  have hr_ge : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hs_ge : 1 < s := lt_of_lt_of_le (by norm_num) (hr_ge.trans hrm_le_s)
  have hq1 : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
    str86_isSzU3Quot_of_statedSU hk hFc hU3
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB
      (Or.inr (Or.inl (str86_vU3Big_of_stated hk hFc hU3)))
  have hU1 : (X' ⊓ Q1 L1 L2 S).relIndex X' ≤ 2 ^ k := by
    refine relIndex_inf_q1_le hF.1 hS1 hq1 hX'ZS (fun a ha => ?_)
    rw [hZge.2 a (hX'Zg ha)]
    exact (Q1 L1 L2 S).one_mem
  have hX'Q1 : X' ⊓ Q1 L1 L2 S = Y := by
    ext x
    rw [hX'def, hYdef, hQ1]
    simp only [Subgroup.mem_inf]
    tauto
  have hs_le_q : s ≤ 2 ^ k := by
    rw [hX'Q1, show Y.relIndex X' = s from hs.symm] at hU1
    exact hU1
  have hHZ : L1 ⊔ S ≤ Subgroup.normalizer (Z : Set G) := by
    intro x hx
    have h := str86_sup_normalizes_z1 hF hSB hk hFc hU3 hx
    simpa [hZdef] using h
  have hNI : IsNormalIn (L1 ⊔ S) Z Z :=
    ⟨le_rfl, fun x hx z hz => (Subgroup.mem_normalizer_iff.mp (hHZ hx) z).mp hz⟩
  obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom (H := L1 ⊔ S) (U := Z) Z hNI
  have hne0 : c ≠ 0 := by
    intro hc0
    have hcomm : ⁅Z, oTwoUpper (L1 ⊔ S)⁆ = ⊥ :=
      D14.commutator_eq_bot_of_zero hZe.isPGroup hser hc0
    have hO2C : oTwoUpper (L1 ⊔ S) ≤ Subgroup.centralizer (Z : Set G) := by
      have hcomm' : ⁅oTwoUpper (L1 ⊔ S), Z⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hcomm
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
    have hQ1C : Q1 L1 L2 S ≤ Subgroup.centralizer (Z : Set G) := by
      simpa [hZdef] using Q1_le_centralizer_Z1 L1 L2 S
    have hHleC : L1 ⊔ S ≤ Subgroup.centralizer (Z : Set G) := by
      rw [← str86_oTwoUpper_sup_q1 hF hSB hk hFc hU3]
      exact sup_le hO2C hQ1C
    have hHleC' : L1 ⊔ Q1 L1 L2 S ≤
        Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
      rwa [str86_sup_s_eq_q1 hF hSB hk hFc hU3, hZdef] at hHleC
    exact hII hHleC'
  have hex : ∃ t : G, t ∈ X' ∧ t ∉ Y := by
    by_contra hcon
    push Not at hcon
    have hle : X' ≤ Y := hcon
    have h1 : Y.relIndex X' = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [show Y.relIndex X' = s from hs.symm] at h1
    omega
  obtain ⟨t, htX', htY⟩ := hex
  have htX'Q : t ∈ Zg ⊓ Q := hX'def ▸ htX'
  have htZg : t ∈ Zg := (Subgroup.mem_inf.mp htX'Q).1
  have htQ : t ∈ Q := (Subgroup.mem_inf.mp htX'Q).2
  have htS : t ∈ S := hQS htQ
  have htH : t ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) htS
  have ht2 : t * t = 1 := by
    have h := hZge.2 t htZg
    simpa [pow_two] using h
  have hZ_le_H : Z ≤ L1 ⊔ S := hZS.trans (le_sup_right : S ≤ L1 ⊔ S)
  have ht2Q : t * t ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [str86_pCoreOf_sup_s_eq_q1 hF hSB hk hFc hU3, ht2]
    exact (Q1 L1 L2 S).one_mem
  have htO : t ∉ pCoreOf 2 (L1 ⊔ S) := by
    intro hmem
    rw [str86_pCoreOf_sup_s_eq_q1 hF hSB hk hFc hU3, hQ1] at hmem
    have htZ : t ∈ Z := by simpa [hZdef] using hmem
    exact htY (by
      rw [hYdef]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨htZ, htZg⟩, htQ⟩)
  have hYC : Y ≤ Subgroup.centralizer ({t} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (hZge.comm (hX'Zg (hYX' hy)) htZg).symm
  have hqS : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) :=
    str86_isSzU3Quot_sup hF hSB hk hFc hU3
  have hpow : ((2 ^ k) ^ 2) ^ c ≤
      (Subgroup.centralizer ({t} : Set G)).relIndex Z := by
    have h := pow_sq_le_relIndex_centralizer (H := L1 ⊔ S) (U := Z) (q := 2 ^ k)
      (c := c) hqS hZe.isPGroup hZ_le_H hser htH ht2Q htO
    simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using h
  have hC_le_YZ : (Subgroup.centralizer ({t} : Set G)).relIndex Z ≤ Y.relIndex Z := by
    have h := Subgroup.relIndex_le_of_le_left (L := Z) (le_inf hYZ hYC)
      (D15Proof.relIndex_ne_zero Y Z)
    rwa [show Z ⊓ Subgroup.centralizer ({t} : Set G) =
        Subgroup.centralizer ({t} : Set G) ⊓ Z from inf_comm Z _,
      Subgroup.inf_relIndex_right] at h
  have hYZmul : Y.relIndex Z = s * 2 ^ m := by
    rw [← Subgroup.relIndex_mul_relIndex Y X Z hYX hXZle, hsX, hXZ']
  have hrs_le : s * 2 ^ m ≤ (2 ^ k) ^ 2 := by
    calc s * 2 ^ m ≤ s * s := Nat.mul_le_mul_left s hrm_le_s
      _ ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul hs_le_q hs_le_q
      _ = (2 ^ k) ^ 2 := by ring
  have hpow2 : ((2 ^ k) ^ 2) ^ c ≤ (2 ^ k) ^ 2 := by
    have h := hpow.trans hC_le_YZ
    rw [hYZmul] at h
    exact h.trans hrs_le
  have hcle : c ≤ 1 := by
    have hb : 1 < (2 ^ k) ^ 2 := by
      rw [← pow_mul]
      exact Nat.one_lt_pow (by omega) (by norm_num)
    refine (pow_le_pow_iff_right₀ hb).mp ?_
    simpa using hpow2
  have hc1 : c = 1 := by omega
  have hser1 : IsChiefSeriesFrom (L1 ⊔ S) Z Z 1 := by rwa [hc1] at hser
  have hq2_le_rs : (2 ^ k) ^ 2 ≤ s * 2 ^ m := by
    have h : (2 ^ k) ^ 2 ≤ (Subgroup.centralizer ({t} : Set G)).relIndex Z := by
      have h' := hpow
      rw [hc1] at h'
      simpa [pow_one] using h'
    exact (h.trans hC_le_YZ).trans_eq hYZmul
  have hrs : s * 2 ^ m = (2 ^ k) ^ 2 := le_antisymm hrs_le hq2_le_rs
  have hqpos : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hr_le_q : 2 ^ m ≤ 2 ^ k := hrm_le_s.trans hs_le_q
  have hq_le_r : 2 ^ k ≤ 2 ^ m := by
    have h1 : 2 ^ k * 2 ^ k ≤ 2 ^ k * 2 ^ m := by
      calc 2 ^ k * 2 ^ k = (2 ^ k) ^ 2 := by ring
        _ = s * 2 ^ m := hrs.symm
        _ ≤ 2 ^ k * 2 ^ m := Nat.mul_le_mul hs_le_q le_rfl
    exact Nat.le_of_mul_le_mul_left h1 hqpos
  have hrq : 2 ^ m = 2 ^ k := le_antisymm hr_le_q hq_le_r
  have hmk : m = k := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hrq
  have hsq : s = 2 ^ k := by
    have h2 : s * 2 ^ m = 2 ^ k * 2 ^ m := by
      rw [hrs, hrq]
      ring
    exact Nat.mul_right_cancel (pow_pos (by norm_num) m) h2
  have hXZk : X.relIndex Z = 2 ^ k := by rw [hXZ', hmk]
  have hYXk : Y.relIndex X = 2 ^ k := by rw [hsX, hsq]
  have hYX'k : Y.relIndex X' = 2 ^ k := by rw [hs.symm, hsq]
  have hcent : ∀ u ∈ X', u ∉ Y → Z ⊓ Subgroup.centralizer ({u} : Set G) = Y := by
    intro u huX' huY
    have huX'Q : u ∈ Zg ⊓ Q := hX'def ▸ huX'
    have huZg : u ∈ Zg := (Subgroup.mem_inf.mp huX'Q).1
    have huQ : u ∈ Q := (Subgroup.mem_inf.mp huX'Q).2
    have huS : u ∈ S := hQS huQ
    have huH : u ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) huS
    have hu2 : u * u = 1 := by
      have h := hZge.2 u huZg
      simpa [pow_two] using h
    have hu2Q : u * u ∈ pCoreOf 2 (L1 ⊔ S) := by
      rw [str86_pCoreOf_sup_s_eq_q1 hF hSB hk hFc hU3, hu2]
      exact (Q1 L1 L2 S).one_mem
    have huO : u ∉ pCoreOf 2 (L1 ⊔ S) := by
      intro hmem
      rw [str86_pCoreOf_sup_s_eq_q1 hF hSB hk hFc hU3, hQ1] at hmem
      have huZ : u ∈ Z := by simpa [hZdef] using hmem
      exact huY (by
        rw [hYdef]
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨huZ, huZg⟩, huQ⟩)
    have huC : Y ≤ Subgroup.centralizer ({u} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (hZge.comm (hX'Zg (hYX' hy)) huZg).symm
    have hu_le : (Subgroup.centralizer ({u} : Set G)).relIndex Z ≤ (2 ^ k) ^ 2 := by
      have h := Subgroup.relIndex_le_of_le_left (L := Z) (le_inf hYZ huC)
        (D15Proof.relIndex_ne_zero Y Z)
      rw [show Z ⊓ Subgroup.centralizer ({u} : Set G) =
          Subgroup.centralizer ({u} : Set G) ⊓ Z from inf_comm Z _,
        Subgroup.inf_relIndex_right, hYZmul, hrs] at h
      exact h
    have hu_ge : (2 ^ k) ^ 2 ≤ (Subgroup.centralizer ({u} : Set G)).relIndex Z := by
      have h := pow_sq_le_relIndex_centralizer (H := L1 ⊔ S) (U := Z) (q := 2 ^ k)
        (c := c) hqS hZe.isPGroup hZ_le_H hser huH hu2Q huO
      simpa [hc1, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using h
    have hu_eq : (Subgroup.centralizer ({u} : Set G)).relIndex Z = (2 ^ k) ^ 2 :=
      le_antisymm hu_le hu_ge
    have hZC : (Z ⊓ Subgroup.centralizer ({u} : Set G)).relIndex Z = (2 ^ k) ^ 2 := by
      rw [show Z ⊓ Subgroup.centralizer ({u} : Set G) =
          Subgroup.centralizer ({u} : Set G) ⊓ Z from inf_comm Z _,
        Subgroup.inf_relIndex_right, hu_eq]
    have hYle : Y ≤ Z ⊓ Subgroup.centralizer ({u} : Set G) := le_inf hYZ huC
    have hmul := Subgroup.relIndex_mul_relIndex Y
      (Z ⊓ Subgroup.centralizer ({u} : Set G)) Z hYle
      (inf_le_left : Z ⊓ Subgroup.centralizer ({u} : Set G) ≤ Z)
    rw [hZC, hYZmul, hrs] at hmul
    have hone : Y.relIndex (Z ⊓ Subgroup.centralizer ({u} : Set G)) = 1 := by
      have hmul' : Y.relIndex (Z ⊓ Subgroup.centralizer ({u} : Set G)) * (2 ^ k) ^ 2 =
          1 * (2 ^ k) ^ 2 := by simpa using hmul
      exact Nat.mul_right_cancel (by positivity) hmul'
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hYle
  refine ⟨hmk, hXZk, hYXk, hYX'k, hser1, ?_⟩
  intro u huX' huY
  exact hcent u huX' huY

end CFSG.Quasithin.Stroth

end

