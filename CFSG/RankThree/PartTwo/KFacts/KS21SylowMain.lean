module

public import CFSG.RankThree.PartTwo.KFacts.KS21AutThree
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowL44
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowSp64
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowU58
public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.Timmesfeld.Transvection.PresSp

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21

open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem center_projSL : Subgroup.center (projSL 4 (GaloisField 2 2)) = ⊥ :=
  center_eq_bot_of_mulEquiv L44.equivSL.symm L44.center_M

theorem center_projSp : Subgroup.center (projSp 3 (GaloisField 2 2)) = ⊥ :=
  center_eq_bot_of_mulEquiv Sp64.equivSp.symm
    (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num))

theorem center_eq_bot_of_isSimpleGroup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h3 : 3 ∣ Nat.card X) (hne : Nat.card X ≠ 3) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
      have ha : a ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
    have hnorm : (Subgroup.zpowers x).Normal :=
      ⟨fun a _ g => by rwa [hcomm g a, mul_inv_cancel_right]⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h' | h'
    · rw [Subgroup.zpowers_eq_bot] at h'
      rw [h', orderOf_one] at hx
      omega
    · apply hne
      rw [← hx, ← Nat.card_zpowers, h', Subgroup.card_top]

theorem center_projSU : Subgroup.center (projSU 5 2 3) = ⊥ := by
  have := CFSG.RankThree.PartTwo.Sec21.isSimpleGroup_projSU (m := 5) (n := 3) (by norm_num)
    (by norm_num)
  have hcard : Nat.card (projSU 5 2 3) = 3 ^ (8 + 1) * 236583028271349760 := by
    rw [Nat.card_congr U58.equivSUI.toEquiv, U58.card_SUI]
  exact center_eq_bot_of_isSimpleGroup (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)

@[expose] def conjAutOf {G : Type} [Group G] {I : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (I : Set G)) : MulAut I where
  toFun i := ⟨y * i * y⁻¹, (Subgroup.mem_normalizer_iff.mp hy i).mp i.2⟩
  invFun i := ⟨y⁻¹ * i * y, by
    apply (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * i * y)).mpr
    simp [mul_assoc]⟩
  left_inv i := Subtype.ext (by simp [mul_assoc])
  right_inv i := Subtype.ext (by simp [mul_assoc])
  map_mul' i j := Subtype.ext (by simp [mul_assoc])

theorem coe_conjAutOf {G : Type} [Group G] {I : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (I : Set G)) (i : I) :
    ((conjAutOf hy i : I) : G) = y * i * y⁻¹ := rfl

@[expose] def conjAutHom {G : Type} [Group G] (I : Subgroup G) :
    Subgroup.normalizer (I : Set G) →* MulAut I where
  toFun y := conjAutOf y.2
  map_one' := by
    ext i
    simp [coe_conjAutOf]
  map_mul' y z := by
    ext i
    simp [coe_conjAutOf, mul_assoc]

theorem exists_sylow_eq_of_autThree {G : Type} [Group G] [Finite G] {I N A : Subgroup G}
    (hIN : I ≤ N) (hN : N ≤ Subgroup.normalizer (I : Set G)) (hAI : A ≤ I)
    (hA : IsElemAbelian 3 A) {n : ℕ} (hcard : Nat.card A = 3 ^ n)
    (hcent : ∀ x ∈ N, x ∈ Subgroup.centralizer (A : Set G) → orderOf x = 3 → x ∈ A)
    (hZ : Subgroup.center I = ⊥) (haut : AutThree I n) (P : Sylow 3 I)
    (hAP : A ≤ (P : Subgroup I).map I.subtype) :
    ∃ Q : Sylow 3 N, (Q : Subgroup N).map N.subtype = (P : Subgroup I).map I.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P' := (P : Subgroup I).map I.subtype with hP'def
  have hP'I : P' ≤ I := Subgroup.map_subtype_le _
  have hP'p : IsPGroup 3 P' := P.isPGroup'.map I.subtype
  have hinP : ∀ i : I, (i : G) ∈ P' → i ∈ (P : Subgroup I) := by
    intro i hi
    obtain ⟨j, hj, hji⟩ := hi
    rw [← Subtype.ext hji]
    exact hj
  have key : ∀ y ∈ N, (∃ k : ℕ, y ^ 3 ^ k = 1) → (∀ q ∈ P', y * q * y⁻¹ ∈ P') → y ∈ P' := by
    intro y hyN ⟨k, hyk⟩ hyP
    set α := conjAutHom I ⟨y, hN hyN⟩ with hαdef
    have hα : ∃ k : ℕ, α ^ 3 ^ k = 1 := ⟨k, by
      rw [hαdef, ← map_pow]
      convert map_one (conjAutHom I)
      exact Subtype.ext hyk⟩
    have hαP : (P : Subgroup I).map α.toMonoidHom = P := by
      have hle : (P : Subgroup I).map α.toMonoidHom ≤ P := by
        rintro _ ⟨i, hi, rfl⟩
        apply hinP
        exact hyP _ ⟨i, hi, rfl⟩
      exact Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective α.injective).ge
    have hAIP : A.subgroupOf I ≤ P := fun a ha => hinP a (hAP ha)
    have hAIEA : IsElemAbelian 3 (A.subgroupOf I) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => Subtype.ext (hA.2 _ hx)⟩
      apply Subtype.ext
      apply Subtype.ext
      show ((a : I) : G) * ((b : I) : G) = ((b : I) : G) * ((a : I) : G)
      exact congrArg Subtype.val (hA.1.is_comm.comm ⟨((a : I) : G), a.2⟩ ⟨((b : I) : G), b.2⟩)
    have hAIcard : Nat.card (A.subgroupOf I) = 3 ^ n := by
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv
    obtain ⟨p, hpP, φ, hφ3, hφA, hαφ⟩ := haut P _ hAIP hAIEA hAIcard α hα hαP
    set x := ((p : I) : G)⁻¹ * y with hxdef
    have hxconj : ∀ i : I, x * i * x⁻¹ = ((φ i : I) : G) := by
      intro i
      have h1 : y * i * y⁻¹ = (p : G) * ((φ i : I) : G) * (p : G)⁻¹ := by
        have := congrArg (fun β : MulAut I => ((β i : I) : G)) hαφ
        simpa [hαdef, conjAutHom, coe_conjAutOf, MulAut.conj_apply] using this
      calc x * i * x⁻¹ = (p : G)⁻¹ * (y * i * y⁻¹) * (p : G) := by
            simp only [hxdef, mul_inv_rev, inv_inv, mul_assoc]
        _ = ((φ i : I) : G) := by rw [h1]; group
    have hpN : ((p : I) : G) ∈ N := hIN p.2
    have hxN : x ∈ N := N.mul_mem (N.inv_mem hpN) hyN
    have hxA : x ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 := hxconj ⟨a, hAI ha⟩
      rw [hφA _ ha] at h1
      calc a * x = x * a * x⁻¹ * x := by rw [h1]
        _ = x * a := by rw [inv_mul_cancel_right]
    have hx3 : ∀ i ∈ I, Commute (x ^ 3) i := by
      intro i hi
      have h1 : ∀ j : I, x * j = ((φ j : I) : G) * x := fun j => by
        rw [← hxconj j, inv_mul_cancel_right]
      have hφ3i : φ (φ (φ ⟨i, hi⟩)) = ⟨i, hi⟩ := by
        have := congrArg (fun β : MulAut I => β ⟨i, hi⟩) hφ3
        simpa [pow_succ, MulAut.mul_apply] using this
      show x ^ 3 * ((⟨i, hi⟩ : I) : G) = ((⟨i, hi⟩ : I) : G) * x ^ 3
      calc x ^ 3 * ((⟨i, hi⟩ : I) : G) = x * (x * (x * ((⟨i, hi⟩ : I) : G))) := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = x * (x * (((φ ⟨i, hi⟩ : I) : G) * x)) := by rw [h1 ⟨i, hi⟩]
        _ = x * ((x * ((φ ⟨i, hi⟩ : I) : G)) * x) := by simp only [mul_assoc]
        _ = x * ((((φ (φ ⟨i, hi⟩)) : I) : G) * x * x) := by rw [h1 (φ ⟨i, hi⟩)]
        _ = (x * (((φ (φ ⟨i, hi⟩)) : I) : G)) * (x * x) := by simp only [mul_assoc]
        _ = (((φ (φ (φ ⟨i, hi⟩))) : I) : G) * x * (x * x) := by rw [h1 (φ (φ ⟨i, hi⟩))]
        _ = (((φ (φ (φ ⟨i, hi⟩))) : I) : G) * x ^ 3 := by
            simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = ((⟨i, hi⟩ : I) : G) * x ^ 3 := by rw [hφ3i]
    have hyNP : Subgroup.zpowers y ≤ Subgroup.normalizer (P' : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_normalizer_fintype hyP
    have hyp : IsPGroup 3 (Subgroup.zpowers y) := by
      intro z
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp z.2
      refine ⟨k, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, ← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hyk, one_zpow, Subgroup.coe_one]
    have hsup := IsPGroup.to_sup_of_normal_left' hP'p hyp hyNP
    have hxsup : x ∈ P' ⊔ Subgroup.zpowers y :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (P'.inv_mem ⟨p, hpP, rfl⟩))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    obtain ⟨m, hm⟩ := hsup ⟨x, hxsup⟩
    have hxm : x ^ 3 ^ m = 1 := congrArg Subtype.val hm
    have hc1 : x ^ 3 = 1 := by
      by_contra hc
      have hcm : (x ^ 3) ^ 3 ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
      obtain ⟨j, hj, hjord⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (orderOf_dvd_of_pow_eq_one hcm)
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hjord
        exact hc hjord
      set c := (x ^ 3) ^ 3 ^ (j - 1) with hcdef
      have hdvd : 3 ^ (j - 1) ∣ orderOf (x ^ 3) := by
        rw [hjord]
        exact pow_dvd_pow 3 (Nat.sub_le j 1)
      have hcord : orderOf c = 3 := by
        rw [hcdef, orderOf_pow_of_dvd (by positivity) hdvd, hjord,
          Nat.pow_div (Nat.sub_le j 1) (by norm_num),
          Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hj0), pow_one]
      have hcN : c ∈ N := N.pow_mem (N.pow_mem hxN 3) _
      have hcI : ∀ i ∈ I, Commute c i := fun i hi => (hx3 i hi).pow_left _
      have hcA : c ∈ Subgroup.centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact (hcI a (hAI ha)).eq.symm
      have hcAmem := hcent c hcN hcA hcord
      have hcZ : (⟨c, hAI hcAmem⟩ : I) ∈ Subgroup.center I := by
        rw [Subgroup.mem_center_iff]
        intro i
        exact Subtype.ext (hcI i i.2).eq.symm
      rw [hZ, Subgroup.mem_bot] at hcZ
      have : c = 1 := congrArg Subtype.val hcZ
      rw [this, orderOf_one] at hcord
      omega
    have hxP' : x ∈ P' := by
      rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _
        (orderOf_dvd_of_pow_eq_one hc1)) with h1 | h3
      · rw [orderOf_eq_one_iff.mp h1]
        exact P'.one_mem
      · exact hAP (hcent x hxN hxA h3)
    have : y = (p : G) * x := by rw [hxdef, mul_inv_cancel_left]
    rw [this]
    exact P'.mul_mem ⟨p, hpP, rfl⟩ hxP'
  have hP'N : P' ≤ N := hP'I.trans hIN
  have hPNp : IsPGroup 3 (P'.subgroupOf N) :=
    hP'p.of_equiv (Subgroup.subgroupOfEquivOfLe hP'N).symm
  obtain ⟨Q, hQ⟩ := hPNp.exists_le_sylow
  have hQeq : (Q : Subgroup N) = P'.subgroupOf N := by
    by_contra hne
    have hlt : P'.subgroupOf N < Q := lt_of_le_of_ne hQ (Ne.symm hne)
    set H := (P'.subgroupOf N).subgroupOf (Q : Subgroup N) with hHdef
    have hHtop : H < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hne ?_
      apply le_antisymm _ hQ
      intro q hq
      have : (⟨q, hq⟩ : (Q : Subgroup N)) ∈ H := by rw [htop]; exact Subgroup.mem_top _
      exact this
    have hnil : Group.IsNilpotent (Q : Subgroup N) := Q.isPGroup'.isNilpotent
    obtain ⟨z, hz, hzH⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent H hHtop)
    obtain ⟨k, hk⟩ := Q.isPGroup' z
    have hzk : (((z : N) : G)) ^ 3 ^ k = 1 := by
      have := congrArg (fun w : (Q : Subgroup N) => ((w : N) : G)) hk
      simpa using this
    have hzP : ∀ q ∈ P', ((z : N) : G) * q * ((z : N) : G)⁻¹ ∈ P' := by
      intro q hq
      have hqQ : (⟨q, hP'N hq⟩ : N) ∈ (Q : Subgroup N) := hQ hq
      have hqH : (⟨⟨q, hP'N hq⟩, hqQ⟩ : (Q : Subgroup N)) ∈ H := hq
      have := (Subgroup.mem_normalizer_iff.mp hz _).mp hqH
      exact this
    have hzmem := key _ (z : N).2 ⟨k, hzk⟩ hzP
    exact hzH hzmem
  refine ⟨Q, ?_⟩
  rw [hQeq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP'N]

theorem terminalSylowThree_of_autThree (h : TerminalAutThree) : TerminalSylowThree := by
  intro G _ _ I N A hIN hN hAI hA hcase hcent P hAP
  rcases hcase with ⟨he, hcard⟩ | ⟨he, hcard⟩ | ⟨he, hcard⟩ <;> obtain ⟨e⟩ := he
  · exact ⟨Or.inr ((U58.sylowModel_projSU.of_mulEquiv e.symm).nonempty_mulEquiv P),
      elemThompson_eq_of_maxEA (U58.maxEA_projSU.of_mulEquiv e.symm) P hA hAP hcard,
      exists_sylow_eq_of_autThree hIN hN hAI hA hcard hcent
        (center_eq_bot_of_mulEquiv e.symm center_projSU) (h.1.of_mulEquiv e.symm) P hAP⟩
  · exact ⟨Or.inl ((L44.sylowModel_projSL.of_mulEquiv e.symm).nonempty_mulEquiv P),
      elemThompson_eq_of_maxEA (L44.maxEA_projSL.of_mulEquiv e.symm) P hA hAP hcard,
      exists_sylow_eq_of_autThree hIN hN hAI hA hcard hcent
        (center_eq_bot_of_mulEquiv e.symm center_projSL) (h.2.1.of_mulEquiv e.symm) P hAP⟩
  · exact ⟨Or.inl ((Sp64.sylowModel_projSp.of_mulEquiv e.symm).nonempty_mulEquiv P),
      elemThompson_eq_of_maxEA (Sp64.maxEA_projSp.of_mulEquiv e.symm) P hA hAP hcard,
      exists_sylow_eq_of_autThree hIN hN hAI hA hcard hcent
        (center_eq_bot_of_mulEquiv e.symm center_projSp) (h.2.2.of_mulEquiv e.symm) P hAP⟩

end CFSG.RankThree.PartTwo.KFacts.KS21
