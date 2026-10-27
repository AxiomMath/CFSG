module

public import CFSG.Quasithin.EmptyFaithful.S151WD
public import CFSG.Quasithin.EmptyFaithful.S151WB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {A : Type} [Group A]

theorem that_conj [Finite A] {L B P : Subgroup A} {n : ℕ} (D : SurjBorel n L B) (hBP : B ≤ P)
    (hPL : P ≤ L) {c : ℕ} (hc : c ∈ D.cutsOf P) {T : Subgroup A}
    (hT : ∀ y : ↥L, (y : A) ∈ T ↔ D.e y ∈ Tgrp n c) (hTP : T ≤ P) :
    ∀ p ∈ P, ∀ y ∈ T, p * y * p⁻¹ ∈ T := by
  classical
  have hmodP : D.model P = QI n (cuts (D.model P)) := eq_QI_cuts (D.Ut_le_model hBP)
  have hstab : ∀ g ∈ D.model P, g ∈ stabilizer (flagSpace n (ZMod 2) c) := by
    intro g hg
    rw [hmodP] at hg
    exact (mem_flagStabilizer.mp hg) c hc
  intro p hp y hy
  have hpL : p ∈ L := hPL hp
  have hyL : y ∈ L := hPL (hTP hy)
  have hy' : D.e ⟨y, hyL⟩ ∈ Tgrp n c := (hT ⟨y, hyL⟩).1 hy
  have hp₁ : D.e ⟨p, hpL⟩ ∈ D.model P := (D.mem_model hBP _).2 hp
  have hbp := bcond_of_mem_stabilizer (hstab _ hp₁)
  have hbp' := bcond_of_mem_stabilizer (hstab _ (Subgroup.inv_mem _ hp₁))
  have hconj := Tgrp_conj hbp (by simpa using hbp') hy'
  have e : p * y * p⁻¹ = ((⟨p, hpL⟩ * ⟨y, hyL⟩ * ⟨p, hpL⟩⁻¹ : ↥L) : A) := by simp
  rw [e, hT, map_mul, map_mul, map_inv]
  exact hconj

theorem e_ne_one_of_order_three [Finite A] {L B : Subgroup A} {n : ℕ} (D : SurjBorel n L B)
    (hker : D.e.ker ≤ CFSG.pCore 2 ↥L) {x : A} (hxL : x ∈ L) (hx3 : orderOf x = 3) :
    D.e ⟨x, hxL⟩ ≠ 1 := by
  intro h
  have h1 : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := hker h
  have h2 : x ∈ pCoreOf 2 L := zn_mem_pCoreOf.mpr ⟨hxL, h1⟩
  exact zb_not_mem_of_orderOf_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) h2 hx3

theorem zb_commutator_not_small [Finite A] {L B P : Subgroup A} {n : ℕ} (D : SurjBorel n L B)
    (hker : D.e.ker ≤ CFSG.pCore 2 ↥L) (hBP : B ≤ P) (hPL : P ≤ L) {a b : ℕ}
    (ha : a ∈ D.cutsOf P) (hb : b ∈ D.cutsOf P) (hab : a < b) {x : A} (hxP : x ∈ P)
    (hx3 : orderOf x = 3) (hcard : Nat.card ↥⁅pCoreOf 2 P, Subgroup.zpowers x⁆ ≤ 4)
    (hdisj : ⁅pCoreOf 2 P, Subgroup.zpowers x⁆ ⊓
      Subgroup.centralizer (Subgroup.zpowers x : Set A) = ⊥) : False := by
  classical
  obtain ⟨ha1, ha2⟩ := D.isNode_of_mem_cutsOf ha
  obtain ⟨hb1, hb2⟩ := D.isNode_of_mem_cutsOf hb
  obtain ⟨Ta, hTaX, hTa⟩ := exists_That D hker hBP hPL ha
  obtain ⟨Tb, hTbX, hTb⟩ := exists_That D hker hBP hPL hb
  set X : Subgroup A := pCoreOf 2 P with hXdef
  set Px : Subgroup A := Subgroup.zpowers x with hPxdef
  have hXp : IsPGroup 2 ↥X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hXP : X ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hxL : x ∈ L := hPL hxP
  set x₀ : ↥L := ⟨x, hxL⟩ with hx₀
  have hmodP : D.model P = QI n (cuts (D.model P)) := eq_QI_cuts (D.Ut_le_model hBP)
  have hstab : ∀ c ∈ D.cutsOf P, ∀ g ∈ D.model P, g ∈ stabilizer (flagSpace n (ZMod 2) c) := by
    intro c hc g hg
    rw [hmodP] at hg
    exact (mem_flagStabilizer.mp hg) c hc
  have hex : D.e x₀ ∈ D.model P := (D.mem_model hBP x₀).2 hxP
  have hx3' : x ^ 3 = 1 := by simpa [hx3] using pow_orderOf_eq_one x
  have he3 : D.e x₀ ^ 3 = 1 := by
    have h1 : x * x * x = 1 := by
      rw [← pow_two, ← pow_succ]
      exact hx3'
    have h2 : x₀ * x₀ * x₀ = 1 := Subtype.ext h1
    have h3 : D.e x₀ * D.e x₀ * D.e x₀ = 1 := by
      rw [← map_mul, ← map_mul, h2, map_one]
    rw [pow_succ, pow_two]
    exact h3
  have hne1 : D.e x₀ ≠ 1 := e_ne_one_of_order_three D hker hxL hx3
  have key : ∀ c : ℕ, c ∈ D.cutsOf P → 1 ≤ c → c < n → ∀ T : Subgroup A, T ≤ X →
      (∀ y : ↥L, (y : A) ∈ T ↔ D.e y ∈ Tgrp n c) → ⁅T, Px⁆ = ⁅X, Px⁆ ∧ ⁅T, Px⁆ ≤ T := by
    intro c hc hc1 hc2 T hTX hT
    have hTP : T ≤ P := hTX.trans hXP
    have hxN : x ∈ Subgroup.normalizer (T : Set A) :=
      zn_le_normalizer (that_conj D hBP hPL hc hT hTP) hxP
    have hPxN : Px ≤ Subgroup.normalizer (T : Set A) := Subgroup.zpowers_le.mpr hxN
    have hle : ⁅T, Px⁆ ≤ T := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPxN
    have h1 : ⁅T, Px⁆ ≤ ⁅X, Px⁆ := Subgroup.commutator_mono hTX le_rfl
    have h3 : x ∈ Subgroup.normalizer ((⁅T, Px⁆ : Subgroup A) : Set A) :=
      CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPxN (Subgroup.mem_zpowers x)
    have hMp : IsPGroup 2 ↥(⁅T, Px⁆ : Subgroup A) := hXp.to_le (hle.trans hTX)
    have h2 : ⁅T, Px⁆ ≠ ⊥ := by
      intro hbot
      have hcomm : ∀ t ∈ Tgrp n c, D.e x₀ * t = t * D.e x₀ := by
        intro t ht
        obtain ⟨y, rfl⟩ := D.surj t
        have hyT : (y : A) ∈ T := (hT y).2 ht
        have hc' : ⁅(y : A), x⁆ ∈ ⁅T, Px⁆ :=
          Subgroup.commutator_mem_commutator hyT (Subgroup.mem_zpowers x)
        rw [hbot] at hc'
        have h0 : (y : A) * x = x * y :=
          commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hc')
        have h00 : y * x₀ = x₀ * y := Subtype.ext h0
        have h01 := congrArg D.e h00
        rw [map_mul, map_mul] at h01
        exact h01.symm
      have hTc := mem_Tgrp_of_commute hc1 hc2 hcomm
      have hsq := Tgrp_sq hTc
      apply hne1
      calc D.e x₀ = (D.e x₀ * D.e x₀) * D.e x₀ := by rw [hsq, one_mul]
        _ = D.e x₀ ^ 3 := by rw [pow_succ, pow_two]
        _ = 1 := he3
    have h5 : ⁅T, Px⁆ ⊓ Subgroup.centralizer (Px : Set A) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right _ h1).trans hdisj.le)
    have h6 : 4 ≤ Nat.card ↥(⁅T, Px⁆ : Subgroup A) := zb_card_ge_four hMp h3 h2 h5
    exact ⟨Subgroup.eq_of_le_of_card_ge h1 (hcard.trans h6), hle⟩
  obtain ⟨hMa, hlea⟩ := key a ha ha1 ha2 Ta hTaX hTa
  obtain ⟨hMb, hleb⟩ := key b hb hb1 hb2 Tb hTbX hTb
  have hab' : ⁅Ta, Px⁆ = ⁅Tb, Px⁆ := hMa.trans hMb.symm
  have hga := hstab a ha _ hex
  have hgb := hstab b hb _ hex
  have hA : ∀ t ∈ Tgrp n a, ⁅t, D.e x₀⁆ ∈ Tgrp n b := by
    intro t ht
    obtain ⟨y, rfl⟩ := D.surj t
    have hyT : (y : A) ∈ Ta := (hTa y).2 ht
    have hc : ⁅(y : A), x⁆ ∈ ⁅Ta, Px⁆ :=
      Subgroup.commutator_mem_commutator hyT (Subgroup.mem_zpowers x)
    rw [hab'] at hc
    have hcT : ⁅(y : A), x⁆ ∈ Tb := hleb hc
    have hcoe : ⁅(y : A), x⁆ = ((⁅y, x₀⁆ : ↥L) : A) := by
      simp only [commutatorElement_def]
      rfl
    rw [hcoe, hTb, map_commutatorElement] at hcT
    exact hcT
  have hB : ∀ t ∈ Tgrp n b, ⁅t, D.e x₀⁆ ∈ Tgrp n a := by
    intro t ht
    obtain ⟨y, rfl⟩ := D.surj t
    have hyT : (y : A) ∈ Tb := (hTb y).2 ht
    have hc : ⁅(y : A), x⁆ ∈ ⁅Tb, Px⁆ :=
      Subgroup.commutator_mem_commutator hyT (Subgroup.mem_zpowers x)
    rw [← hab'] at hc
    have hcT : ⁅(y : A), x⁆ ∈ Ta := hlea hc
    have hcoe : ⁅(y : A), x⁆ = ((⁅y, x₀⁆ : ↥L) : A) := by
      simp only [commutatorElement_def]
      rfl
    rw [hcoe, hTa, map_commutatorElement] at hcT
    exact hcT
  exact hne1 (wd_eq_one_of_comm_mem ha1 hab hb2 hga hgb hA hB he3)

theorem smin_shape_triv [Finite A] {L S B P : Subgroup A} {n : ℕ} (hBdef : B = S ⊓ L)
    (hn3 : 3 ≤ n) (D : SurjBorel n L B) (hSN : S ≤ Subgroup.normalizer (L : Set A))
    (hk : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (L : Set A), ∀ x : ↥L, D.e x = 1 →
      D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1)
    (htriv : ∀ K : Subgroup A, B ≤ K → K ≤ L → S ≤ Subgroup.normalizer (K : Set A))
    (hP : SMin L S P) : ∃ i, IsNode n i ∧ D.cutsOf P = nodeSet n \ {i} := by
  classical
  obtain ⟨i, hi, hshape⟩ := smin_shape hBdef hn3 D hSN hk hP
  rcases hshape with hc | ⟨j, hj, hij, hc⟩
  · exact ⟨i, hi, hc⟩
  · exfalso
    have hBP : B ≤ P := hBdef ▸ hP.sl
    obtain ⟨K, hBK, hKL, hKc⟩ := D.exists_cutsOf_eq (I := nodeSet n \ {i}) (fun x hx => hx.1)
    have hKP : K ≤ P := by
      rw [D.cutsOf_le_iff hBK hKL hBP, hKc, hc]
      intro x hx
      exact ⟨hx.1, fun hxi => hx.2 (Or.inl hxi)⟩
    rcases hP.minimal K (htriv K hBK hKL) (hBdef ▸ hBK) hKP with hKB | hKP'
    · have h1 : D.cutsOf K = nodeSet n := by
        rw [show K = B from hKB.trans hBdef.symm, D.cutsOf_B]
        rfl
      rw [hKc] at h1
      have h2 : i ∈ nodeSet n := hi
      rw [← h1] at h2
      exact h2.2 rfl
    · rw [← hKP', hKc] at hc
      have h3 : j ∈ nodeSet n \ {i} := ⟨hj, by simp only [Set.mem_singleton_iff]; omega⟩
      rw [hc] at h3
      exact h3.2 (Or.inr rfl)

theorem not_C126Third_of_commutator_not_small [Finite A] {S P : Subgroup A} (hS2 : IsPGroup 2 ↥S)
    (hSP : S ≤ Subgroup.normalizer (P : Set A))
    (hA3 : ∀ K : Subgroup A, IsChi0Block (P ⊔ S) K → IsAltType K 3)
    (hbig : ∀ x ∈ P, orderOf x = 3 → Nat.card ↥⁅pCoreOf 2 P, Subgroup.zpowers x⁆ ≤ 4 →
      ⁅pCoreOf 2 P, Subgroup.zpowers x⁆ ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set A) = ⊥ →
        False) :
    ¬ C126Third (P ⊔ S) S := by
  rintro ⟨r, K, hr, hK, -, hres, -, -⟩
  have hHN : P ⊔ S ≤ Subgroup.normalizer (P : Set A) := sup_le Subgroup.le_normalizer hSP
  have hTR : twoResidual (P ⊔ S) ≤ P :=
    twoResidual_le_of_isTwoQuotient le_sup_left hHN (zb_two_pow hSP hS2)
  have hK₀ := hK ⟨0, hr⟩
  set K₀ : Subgroup A := K ⟨0, hr⟩ with hK₀def
  have hA3₀ : IsAltType K₀ 3 := hA3 K₀ hK₀.1
  have hshort : IsShort2 K₀ := hK₀.1.1.1
  have hresK : K₀ ≤ twoResidual (P ⊔ S) :=
    calc K₀ ≤ ⨆ j, K j := le_iSup K _
      _ = twoResidual (P ⊔ S) := hres.symm
  obtain ⟨x, hxK, hx3⟩ := zb_exists_orderOf_three hA3₀
  have hxP : x ∈ P := hTR (hresK hxK)
  have hKP : K₀ ≤ P := hresK.trans hTR
  set X : Subgroup A := pCoreOf 2 P with hXdef
  have hXp : IsPGroup 2 ↥X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hXP : X ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hHX : P ⊔ S ≤ Subgroup.normalizer (X : Set A) := by
    refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P) ?_
    exact fun s hs => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (hSP hs)
  have hKU : K₀ ≤ Subgroup.normalizer (X : Set A) := hKP.trans (le_sup_left.trans hHX)
  have hXH : X ≤ pCoreOf 2 (P ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hXP.trans le_sup_left) hHX hXp
  have hUK : X ≤ Subgroup.normalizer (K₀ : Set A) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact fun hk => C1Pack.conj_mem_block_of_mem_pCoreOf hK₀.1.1 (hXH hy) hk
    · intro hk
      have := C1Pack.conj_mem_block_of_mem_pCoreOf hK₀.1.1 (hXH (X.inv_mem hy)) hk
      simpa [mul_assoc] using this
  obtain ⟨hcard, hdisj⟩ := zb_commutator_card_le hXp hKU hUK hshort hA3₀ hxK hx3
  set Px : Subgroup A := Subgroup.zpowers x with hPx
  have hPxK : Px ≤ K₀ := by rw [hPx, Subgroup.zpowers_le]; exact hxK
  have hPxN : Px ≤ Subgroup.normalizer (X : Set A) := hPxK.trans hKU
  have hcop : Nat.Coprime (Nat.card ↥Px) (Nat.card ↥X) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
    rw [hPx, Nat.card_zpowers, hx3, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hXsolv : Group.IsSolvable ↥X := by
    have hnil : Group.IsNilpotent ↥X := hXp.isNilpotent
    infer_instance
  have e1 : ⁅⁅X, Px⁆, Px⁆ = ⁅X, Px⁆ := zb_commutator_double_eq_self Px X hPxN hcop hXsolv
  have hW : ⁅⁅⁅X, Px⁆, Px⁆, Px⁆ = ⁅X, Px⁆ := by rw [e1, e1]
  rw [hW] at hcard hdisj
  exact hbig x hxP hx3 hcard hdisj

theorem noflip_single {n i : ℕ} (hn4 : 4 ≤ n) :
    ∃ a b : ℕ, a < b ∧ IsNode n a ∧ IsNode n b ∧ a ≠ i ∧ b ≠ i :=
  ⟨if i = 1 then 2 else 1, if i = 1 ∨ i = 2 then 3 else 2, by split_ifs <;> omega,
    ⟨by split_ifs <;> omega, by split_ifs <;> omega⟩, ⟨by split_ifs <;> omega, by split_ifs <;> omega⟩,
    by split_ifs <;> omega, by split_ifs <;> omega⟩

theorem noflip_double {i j : ℕ} (hi : IsNode 5 i) (hj : IsNode 5 j) (hij : i < j) :
    ∃ a b : ℕ, a < b ∧ IsNode 5 a ∧ IsNode 5 b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j := by
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨hj1, hj2⟩ := hj
  have key : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5, 1 ≤ i → 1 ≤ j → i < j →
      ∃ a ∈ Finset.range 5, ∃ b ∈ Finset.range 5,
        a < b ∧ 1 ≤ a ∧ 1 ≤ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j := by decide
  obtain ⟨a, ha, b, hb, hab, ha1, hb1, hai, haj, hbi, hbj⟩ :=
    key i (Finset.mem_range.mpr hi2) j (Finset.mem_range.mpr hj2) hi1 hj1 hij
  exact ⟨a, b, hab, ⟨ha1, Finset.mem_range.mp ha⟩, ⟨hb1, Finset.mem_range.mp hb⟩, hai, haj, hbi, hbj⟩

theorem noflip_core [Finite A] {L S P : Subgroup A} {n : ℕ}
    (hn : n = 5 ∨ (n = 4 ∧ SActsTrivially L S)) (e₀ : ↥L ≃* SLt n) (hS2 : IsPGroup 2 ↥S)
    (hSN : S ≤ Subgroup.normalizer (L : Set A)) (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hP : SMin L S P) : ¬ C126Third (P ⊔ S) S := by
  have hn45 : n = 4 ∨ n = 5 := by rcases hn with h | ⟨h, -⟩ <;> omega
  obtain ⟨D'⟩ := exists_borelIso (by omega) hsyl e₀
  let D : SurjBorel n L (S ⊓ L) := borelIso_toSurjBorel D' hsyl.1
  have hker : D.e.ker ≤ CFSG.pCore 2 ↥L := by
    have : D.e.ker = ⊥ := MonoidHom.ker_eq_bot_iff _ |>.mpr D'.e.injective
    rw [this]
    exact bot_le
  have hk : ∀ s ∈ S, ∀ hs : s ∈ Subgroup.normalizer (L : Set A), ∀ x : ↥L, D.e x = 1 →
      D.e (L.normalizerMonoidHom ⟨s, hs⟩ x) = 1 := by
    intro s hs hsN x hx
    have hx' : D'.e x = 1 := hx
    have : x = 1 := (MulEquiv.map_eq_one_iff D'.e).mp hx'
    subst this
    rw [map_one, map_one]
  have hBP : S ⊓ L ≤ P := hP.sl
  have hPL : P ≤ L := hP.le
  have hmodel : D.model P = QI n (D.cutsOf P) := eq_QI_cuts (D.Ut_le_model hBP)
  have hidx : (S ⊓ L).relIndex P = (Ut n).relIndex (QI n (D.cutsOf P)) := by
    rw [← hmodel]
    exact zr_relIndex_eq D hBP hPL
  obtain ⟨a, b, ha, hb, hab, hd⟩ : ∃ a b : ℕ, a ∈ D.cutsOf P ∧ b ∈ D.cutsOf P ∧ a < b ∧
      ((S ⊓ L).relIndex P ∣ 21 ∨ (S ⊓ L).relIndex P ∣ 9) := by
    have single : ∀ i, IsNode n i → D.cutsOf P = nodeSet n \ {i} → ∃ a b : ℕ, a ∈ D.cutsOf P ∧
        b ∈ D.cutsOf P ∧ a < b ∧ ((S ⊓ L).relIndex P ∣ 21 ∨ (S ⊓ L).relIndex P ∣ 9) := by
      intro i hi hc
      obtain ⟨a, b, hab, ha, hb, hai, hbi⟩ := noflip_single (n := n) (i := i) (by omega)
      refine ⟨a, b, ?_, ?_, hab, Or.inl ?_⟩
      · rw [hc]
        exact ⟨ha, fun h => hai h⟩
      · rw [hc]
        exact ⟨hb, fun h => hbi h⟩
      · rw [hidx, hc, index_single hi]
        norm_num
    rcases hn with rfl | ⟨rfl, htr⟩
    · obtain ⟨i, hi, hshape⟩ := smin_shape rfl (by norm_num) D hSN hk hP
      rcases hshape with hc | ⟨j, hj, hij, hc⟩
      · exact single i hi hc
      · obtain ⟨a, b, hab, ha, hb, hai, haj, hbi, hbj⟩ := noflip_double hi hj hij
        refine ⟨a, b, ?_, ?_, hab, ?_⟩
        · rw [hc]
          exact ⟨ha, fun h => h.elim hai haj⟩
        · rw [hc]
          exact ⟨hb, fun h => h.elim hbi hbj⟩
        · rw [hidx, hc]
          rcases index_double hi hj hij with h | h
          · exact Or.inr (by rw [h])
          · exact Or.inl (by rw [h])
    · obtain ⟨i, hi, hc⟩ := smin_shape_triv rfl (by norm_num) D hSN hk htr hP
      exact single i hi hc
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hS2
  have hcard : Nat.card ↥(P ⊔ S) = 2 ^ m * (S ⊓ L).relIndex P := by
    rw [smin_card_sup hP, hm]
  have hdiv : Nat.card ↥(P ⊔ S) ∣ 2 ^ m * 21 ∨ Nat.card ↥(P ⊔ S) ∣ 2 ^ m * 9 := by
    rw [hcard]
    rcases hd with hd | hd
    · exact Or.inl (mul_dvd_mul_left _ hd)
    · exact Or.inr (mul_dvd_mul_left _ hd)
  have hA3 : ∀ K : Subgroup A, IsChi0Block (P ⊔ S) K → IsAltType K 3 :=
    fun K hK => chi0_isAltType_three hK hdiv
  exact not_C126Third_of_commutator_not_small hS2 hP.sP hA3
    (fun x hxP hx3 hcard' hdisj => zb_commutator_not_small D hker hBP hPL ha hb hab hxP hx3 hcard'
      hdisj)

theorem input15122ThreeENoFlip_holds : Input15122ThreeENoFlip := by
  intro G _ _ L S P hcase hS2 hSN hsyl hP
  rcases hcase with h5 | ⟨h4, htr⟩
  · obtain ⟨e₀⟩ := nonempty_equiv_SLt_of_isPSL h5
    exact noflip_core (Or.inl rfl) e₀ hS2 hSN hsyl hP
  · obtain ⟨e₀⟩ := nonempty_equiv_SLt_of_isPSL h4
    exact noflip_core (Or.inr ⟨rfl, htr⟩) e₀ hS2 hSN hsyl hP

end CFSG.Quasithin
