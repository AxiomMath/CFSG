module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPStep

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (IsL2 IsSz IsL3 IsU3 IsSp4 IsU4 IsU5 IsOmega8m Is3D4 IsAlt IsSL3 Bar2 OInf Opp)

variable {Q : Type} [Group Q] [Finite Q] {T A B R L₀ : Subgroup Q}

private theorem wc813pbor_eq_of_isSylowIn_ge {H P K : Subgroup Q} (hP : IsSylowIn 2 P H)
    (hKH : K ≤ H) (hK : IsPGroup 2 K) (hPK : P ≤ K) : K = P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Subgroup.eq_of_le_of_card_ge hPK ?_).symm
  rw [hP.card_eq]
  obtain ⟨j, hj⟩ := hK.exists_card_eq
  rw [hj]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have hdvd : 2 ^ j ∣ Nat.card H := by
    rw [← hj]
    exact Subgroup.card_dvd_of_le hKH
  exact (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos (α := ↥H)).ne').mp hdvd

private theorem wc813pbor_isSylowIn_sup_of_commute {L L' P R : Subgroup Q}
    (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) (hodd : Odd (Nat.card (L ⊓ L' : Subgroup Q)))
    (hP : IsSylowIn 2 P L) (hR : IsSylowIn 2 R L') :
    IsSylowIn 2 (P ⊔ R) (L ⊔ L') := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPRcomm : ∀ a ∈ P, ∀ b ∈ R, a * b = b * a :=
    fun a ha b hb => hcomm a (hP.le ha) b (hR.le hb)
  have hPRbot : P ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxP, -⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk⟩ := hP.isPGroup ⟨x, hxP⟩
    have hx2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx2)
    have hxLL' : x ∈ L ⊓ L' :=
      Subgroup.mem_inf.mpr ⟨hP.le hxP, hR.le (Subgroup.mem_inf.mp hx).2⟩
    have hxodd : Odd (orderOf x) :=
      hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard (L ⊓ L') hxLL')
    rw [hj] at hxodd
    have hj0 : j = 0 := by
      rcases j with _ | j
      · rfl
      · exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩)
          (Nat.not_even_iff_odd.mpr hxodd)
    rw [hj0, pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  have hcardPR : Nat.card (P ⊔ R : Subgroup Q) = Nat.card P * Nat.card R := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P R hPRcomm).1
    rw [hPRbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hcardLL' : Nat.card (L ⊔ L' : Subgroup Q) * Nat.card (L ⊓ L' : Subgroup Q) =
      Nat.card L * Nat.card L' :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L L' hcomm).1
  have hfact : (Nat.card (L ⊔ L' : Subgroup Q)).factorization 2 =
      (Nat.card L).factorization 2 + (Nat.card L').factorization 2 := by
    have hL : (Nat.card (L ⊔ L' : Subgroup Q) * Nat.card (L ⊓ L' : Subgroup Q)).factorization 2 =
        (Nat.card (L ⊔ L' : Subgroup Q)).factorization 2 := by
      rw [Nat.factorization_mul (Nat.card_pos (α := ↥(L ⊔ L'))).ne'
        (Nat.card_pos (α := ↥(L ⊓ L'))).ne', Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]
    have hR : (Nat.card L * Nat.card L').factorization 2 =
        (Nat.card L).factorization 2 + (Nat.card L').factorization 2 := by
      rw [Nat.factorization_mul (Nat.card_pos (α := ↥L)).ne' (Nat.card_pos (α := ↥L')).ne',
        Finsupp.add_apply]
    have h := congrArg (fun n => n.factorization 2) hcardLL'
    rw [hL, hR] at h
    exact h
  refine isSylowIn_of_card_eq (sup_le (hP.le.trans le_sup_left) (hR.le.trans le_sup_right)) ?_
  rw [hcardPR, hP.card_eq, hR.card_eq, ← pow_add, ← hfact]

private theorem wc813pbor_sylow_sup_components (h : Cfg813 T A B R L₀)
    (s : Finset {J : Subgroup Q // IsComponentOf J ⊤}) :
    IsSylowIn 2 (T ⊓ s.sup (fun J => J.1)) (s.sup (fun J => J.1)) ∧
      T ⊓ s.sup (fun J => J.1) = s.sup (fun J => T ⊓ J.1) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · simp only [Finset.sup_empty, inf_bot_eq]
      exact isSylowIn_of_card_eq le_rfl (by
        rw [Subgroup.card_bot, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 1),
          pow_zero])
    · simp only [Finset.sup_empty, inf_bot_eq]
  | insert a s' ha ih =>
    obtain ⟨hIs, hEq⟩ := ih
    rw [Finset.sup_insert, Finset.sup_insert]
    have hEs : s'.sup (fun J => J.1) ≤ Subgroup.centralizer (a.1 : Set Q) := by
      refine Finset.sup_le fun J hJ => ?_
      have hne : J.1 ≠ a.1 := by
        intro heq
        exact ha (by rw [← Subtype.ext heq]; exact hJ)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne J.1 a.1 J.2 a.2 hne)
    have hcomm : ∀ x ∈ a.1, ∀ y ∈ s'.sup (fun J => J.1), x * y = y * x :=
      fun x hx y hy => Subgroup.mem_centralizer_iff.mp (hEs hy) x hx
    have hodd : Odd (Nat.card (a.1 ⊓ s'.sup (fun J => J.1) : Subgroup Q)) := by
      have hleZ : a.1 ⊓ s'.sup (fun J => J.1) ≤
          (Subgroup.center ↥a.1).map a.1.subtype := by
        intro x hx
        obtain ⟨hxJ, hxE⟩ := Subgroup.mem_inf.mp hx
        refine Subgroup.mem_map.mpr ⟨⟨x, hxJ⟩, ?_, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEs hxE) y y.2)
      have hoddMap : Odd (Nat.card ((Subgroup.center ↥a.1).map a.1.subtype)) := by
        rw [Subgroup.card_map_of_injective a.1.subtype_injective]
        exact h.center_odd a.2
      exact hoddMap.of_dvd_nat (Subgroup.card_dvd_of_le hleZ)
    have hsyl₀ : IsSylowIn 2 (T ⊓ a.1) a.1 := h.isSylowIn_inf_component a.2
    have hsyl : IsSylowIn 2 ((T ⊓ a.1) ⊔ (T ⊓ s'.sup (fun J => J.1)))
        (a.1 ⊔ s'.sup (fun J => J.1)) :=
      wc813pbor_isSylowIn_sup_of_commute hcomm hodd hsyl₀ hIs
    have hle : (T ⊓ a.1) ⊔ (T ⊓ s'.sup (fun J => J.1)) ≤
        T ⊓ (a.1 ⊔ s'.sup (fun J => J.1)) :=
      le_inf (sup_le inf_le_left inf_le_left)
        (sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right))
    have h2 : IsPGroup 2 (T ⊓ (a.1 ⊔ s'.sup (fun J => J.1)) : Subgroup Q) :=
      h.sylow.isPGroup.to_le inf_le_left
    have heq : T ⊓ (a.1 ⊔ s'.sup (fun J => J.1)) =
        (T ⊓ a.1) ⊔ (T ⊓ s'.sup (fun J => J.1)) :=
      wc813pbor_eq_of_isSylowIn_ge hsyl inf_le_right h2 hle
    exact ⟨by rw [heq]; exact hsyl, by rw [heq, hEq]⟩

theorem Cfg813.inf_layer_le_iSup (h : Cfg813 T A B R L₀) :
    T ⊓ genFittingLayer Q ≤ ⨆ (J : Subgroup Q) (_ : IsComponentOf J ⊤), T ⊓ J := by
  classical
  let idx := {J : Subgroup Q // IsComponentOf J ⊤}
  haveI : Fintype idx := Fintype.ofFinite idx
  have hmain := (wc813pbor_sylow_sup_components h (Finset.univ : Finset idx)).2
  have hE : (Finset.univ : Finset idx).sup (fun J => J.1) = genFittingLayer Q := by
    have hrange : Set.range (fun J : idx => J.1) = {L : Subgroup Q | IsComponentOf L ⊤} := by
      ext L
      constructor
      · rintro ⟨J, rfl⟩
        exact J.2
      · intro hL
        exact ⟨⟨L, hL⟩, rfl⟩
    rw [Finset.sup_univ_eq_iSup, genFittingLayer.eq_sSup, ← sSup_range, hrange]
  rw [hE] at hmain
  rw [hmain, Finset.sup_univ_eq_iSup]
  exact le_of_eq (iSup_subtype (p := fun J : Subgroup Q => IsComponentOf J ⊤)
    (f := fun J : idx => T ⊓ J.1))

private theorem wc813pbor_mem_normalizer_iSup {ι : Sort*} {U : ι → Subgroup Q} {g : Q}
    (h : ∀ i, g ∈ Subgroup.normalizer (U i : Set Q)) :
    g ∈ Subgroup.normalizer ((⨆ i, U i : Subgroup Q) : Set Q) := by
  have key : ∀ g' : Q, (∀ i, g' ∈ Subgroup.normalizer (U i : Set Q)) →
      ∀ x ∈ ⨆ i, U i, g' * x * g'⁻¹ ∈ ⨆ i, U i := by
    intro g' hg' x hx
    have hle : (⨆ i, U i) ≤ (⨆ i, U i).comap (MulAut.conj g').toMonoidHom :=
      iSup_le fun i y hy => Subgroup.mem_iSup_of_mem i
        (((Subgroup.mem_normalizer_iff).mp (hg' i) y).mp hy)
    exact hle hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key g h x, fun hx => by
    have := key g⁻¹ (fun i => Subgroup.inv_mem _ (h i)) _ hx
    simpa [mul_assoc] using this⟩

theorem Cfg813.normalizer_component_le (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hS : T ⊓ J ≠ ⊥) :
    J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ≤ B := by
  classical
  haveI hEnorm : (genFittingLayer Q).Normal := CFSG.ComponentClassification.Layer.normal Q
  set T₀ : Subgroup Q := T ⊓ genFittingLayer Q with hT₀
  have hSle : T ⊓ J ≤ T₀ := by
    rw [hT₀]
    exact inf_le_inf_left T (CFSG.ComponentClassification.Layer.component_le hJ)
  have hT₀ne : T₀ ≠ ⊥ := by
    intro hbot
    exact hS (le_bot_iff.mp (hSle.trans (le_of_eq hbot)))
  have hTle : T ≤ Subgroup.normalizer (T₀ : Set Q) := by
    rw [hT₀]
    exact (le_inf Subgroup.le_normalizer
      (Subgroup.le_normalizer_of_normal (H := genFittingLayer Q))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hT₀notNormal : ¬ T₀.Normal := by
    intro hnorm
    exact hT₀ne (h.no_normal_two T₀ hnorm (h.sylow.isPGroup.to_le (by rw [hT₀]; exact inf_le_left)))
  have hNlt : Subgroup.normalizer (T₀ : Set Q) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hT₀notNormal (Subgroup.normalizer_eq_top_iff.mp htop)
  have hNB : Subgroup.normalizer (T₀ : Set Q) ≤ B := by
    obtain ⟨X, hXmem, hNX⟩ :=
      exists_mem_calNIn_of_lt (H := (⊤ : Subgroup Q)) hTle hNlt
    have hXB : X = B := by
      have hmem := hXmem
      rw [h.maxT] at hmem
      exact Set.mem_singleton_iff.mp hmem
    rwa [hXB] at hNX
  intro n hn
  obtain ⟨hnJ, hnN⟩ := Subgroup.mem_inf.mp hn
  have hNT₀ : n ∈ Subgroup.normalizer (T₀ : Set Q) := by
    have hEq : T₀ = ⨆ (J' : Subgroup Q) (_ : IsComponentOf J' ⊤), T ⊓ J' := by
      rw [hT₀]
      refine le_antisymm h.inf_layer_le_iSup ?_
      refine iSup_le fun J' => iSup_le fun hJ' => ?_
      exact le_inf inf_le_left
        (inf_le_right.trans (CFSG.ComponentClassification.Layer.component_le hJ'))
    rw [hEq]
    rw [show (⨆ (J' : Subgroup Q) (_ : IsComponentOf J' ⊤), T ⊓ J') =
        ⨆ (J' : {K : Subgroup Q // IsComponentOf K ⊤}), T ⊓ J'.1 from
      (iSup_subtype (p := fun J' : Subgroup Q => IsComponentOf J' ⊤)
        (f := fun J' : {K : Subgroup Q // IsComponentOf K ⊤} => T ⊓ J'.1)).symm]
    refine wc813pbor_mem_normalizer_iSup fun J' => ?_
    by_cases hJ' : J'.1 = J
    · rw [hJ']
      exact hnN
    · have hle : J'.1 ≤ Subgroup.centralizer (J : Set Q) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne J'.1 J J'.2 hJ hJ')
      have hcomm : n ∈ Subgroup.centralizer (J'.1 : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subgroup.mem_centralizer_iff.mp (hle hy) n hnJ).symm
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le (fun x hx => (Subgroup.mem_inf.mp hx).2) hcomm)
  exact hNB hNT₀

theorem Cfg813.inf_component_ne_top (h : Cfg813 T A B R L₀) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) : B ⊓ J ≠ J := by
  intro hBJ
  have hBmem : B ∈ calNIn (⊤ : Subgroup Q) T := by
    rw [h.maxT]
    exact Set.mem_singleton B
  have hTB : T ≤ B := hBmem.1
  have hBlt : B < ⊤ := hBmem.2.1
  have hJB : J ≤ B := by
    rw [← hBJ]
    exact inf_le_left
  obtain ⟨t, htT, hcover⟩ := h.component_cover J hJ
  have ht : t ∈ B := hTB htT
  have hconj : conjSubgroup L₀ t ≤ B := by
    rw [← hcover]
    exact sup_le hJB h.R_le_B
  have hconjB : ∀ {X : Subgroup Q} {g : Q}, g ∈ B → X ≤ B → conjSubgroup X g ≤ B := by
    intro X g hg hX
    have hmap : B.map (MulAut.conj g⁻¹).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (B.inv_mem hg))
    calc conjSubgroup X g = X.map (MulAut.conj g⁻¹).toMonoidHom := rfl
      _ ≤ B.map (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono hX
      _ = B := hmap
  have hL₀B : L₀ ≤ B := by
    have hh := hconjB (X := conjSubgroup L₀ t) (g := t⁻¹) (B.inv_mem ht) hconj
    rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at hh
  have hQle : (⊤ : Subgroup Q) ≤ B := by
    rw [← h.L₀_sup]
    exact sup_le hL₀B hTB
  exact hBlt.ne' (le_antisymm hQle le_top)

private theorem wc813pbor_normalizer_conjSubgroup (X : Subgroup Q) (g : Q) :
    Subgroup.normalizer ((conjSubgroup X g : Subgroup Q) : Set Q) =
      conjSubgroup (Subgroup.normalizer (X : Set Q)) g := by
  rw [conjSubgroup, conjSubgroup]
  exact (Subgroup.map_equiv_normalizer_eq X (MulAut.conj g⁻¹)).symm

private theorem wc813pbor_conjSubgroup_lt_conjSubgroup {A B : Subgroup Q} {g : Q} :
    conjSubgroup A g < conjSubgroup B g ↔ A < B :=
  Subgroup.map_lt_map_iff_of_injective (MulAut.conj g⁻¹).injective

private theorem wc813pbor_conjSubgroup_le_conjSubgroup {A B : Subgroup Q} {g : Q} :
    conjSubgroup A g ≤ conjSubgroup B g ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective

private theorem wc813pbor_conjSubgroup_max {L P : Subgroup Q} {g : Q}
    (hg : g ∈ Subgroup.normalizer (L : Set Q))
    (hmax : ∀ Y, P < Y → Y ≤ L → Y = L)
    {Y : Subgroup Q} (hY : conjSubgroup P g < Y) (hYL : Y ≤ L) : Y = L := by
  have h1 : P < conjSubgroup Y g⁻¹ := by
    have h2 : conjSubgroup (conjSubgroup P g) g⁻¹ < conjSubgroup Y g⁻¹ :=
      wc813pbor_conjSubgroup_lt_conjSubgroup.mpr hY
    rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h2
  have h2 : conjSubgroup Y g⁻¹ ≤ L := by
    have hL : conjSubgroup L g⁻¹ = L := by
      simpa [conjSubgroup] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    exact (wc813pbor_conjSubgroup_le_conjSubgroup.mpr hYL).trans (le_of_eq hL)
  have h3 := hmax (conjSubgroup Y g⁻¹) h1 h2
  have hYeq : Y = conjSubgroup (conjSubgroup Y g⁻¹) g := by
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  rw [hYeq, h3, conjSubgroup]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hg)

private theorem wc813pbor_dynkin_contra (hF0 : OddSchurMultiplierFact)
    (h : Cfg813 T A B R L₀) {J : Subgroup Q} (hJ : IsComponentOf J ⊤) (hr : RankTwoShape J)
    {Pi Pj P : Subgroup Q}
    (hPi : IsMaxParabolicMod (⊥ : Subgroup Q) J Pi)
    (hPj : IsMaxParabolicMod (⊥ : Subgroup Q) J Pj)
    (hNPi : J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ≤ Pi)
    (hNPj : J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ≤ Pj)
    (hPiPj : Pi ≠ Pj)
    (hcover : ∀ P', J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ≤ P' → P' ≤ J →
      P' = J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ∨ P' = Pi ∨ P' = Pj ∨ P' = J)
    (hP : P = B ⊓ J) (hPle : P ≤ J) (hPbad : P = Pi) : False := by
  classical
  set N : Subgroup Q := J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) with hN
  have hNPi' : N ≤ Pi := by rw [hN]; exact hNPi
  have hNPj' : N ≤ Pj := by rw [hN]; exact hNPj
  have hNnePi : N ≠ Pi := by
    intro heq
    rcases eq_or_lt_of_le hNPj' with h | h
    · exact hPiPj (heq.symm.trans h)
    · exact hPj.2.1.ne (hPi.2.2.1 Pj (by rw [heq] at h; exact h) hPj.2.1.le)
  have hNltPi : N < Pi := lt_of_le_of_ne hNPi' hNnePi
  obtain ⟨t, ht, hDyn⟩ := h.dynkin_component hF0 hJ hr
  obtain ⟨htT, htNJ⟩ := Subgroup.mem_inf.mp ht
  have hBmem : B ∈ calNIn (⊤ : Subgroup Q) T := by rw [h.maxT]; exact Set.mem_singleton B
  have htB : t ∈ B := hBmem.1 htT
  have htNS : t ∈ Subgroup.normalizer ((T ⊓ J : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_inf _ _ _ (MulAut.conj t).injective]
    congr 1
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htT)
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp htNJ
  have htNN : t ∈ Subgroup.normalizer (N : Set Q) := by
    rw [hN, Subgroup.mem_normalizer_iff_map_conj_eq,
      Subgroup.map_inf _ _ _ (MulAut.conj t).injective]
    congr 1
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp htNJ
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htNS)
  have htNP : t ∈ Subgroup.normalizer (P : Set Q) := by
    rw [hP, Subgroup.mem_normalizer_iff_map_conj_eq,
      Subgroup.map_inf _ _ _ (MulAut.conj t).injective]
    congr 1
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htB)
    · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp htNJ
  have htNPi : t ∈ Subgroup.normalizer (Pi : Set Q) := by
    rw [hPbad] at htNP
    exact htNP
  have htPiConj_inv : conjSubgroup Pi t⁻¹ = Pi := by
    simpa [conjSubgroup] using Subgroup.mem_normalizer_iff_map_conj_eq.mp htNPi
  have htNPj : t ∈ Subgroup.normalizer (Pj : Set Q) := by
    have hJt : conjSubgroup J t = J := by
      rw [conjSubgroup]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ htNJ)
    have hPjConjLt : conjSubgroup Pj t < J := by
      rw [← hJt]
      exact wc813pbor_conjSubgroup_lt_conjSubgroup.mpr hPj.2.1
    have hmax : ∀ Y, conjSubgroup Pj t < Y → Y ≤ J → Y = J :=
      fun Y => wc813pbor_conjSubgroup_max (Y := Y) htNJ hPj.2.2.1
    have hNconj : conjSubgroup N t = N := by
      rw [conjSubgroup]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ htNN)
    have hNleConj : N ≤ conjSubgroup Pj t := by
      have := (wc813pbor_conjSubgroup_le_conjSubgroup (A := N) (B := Pj) (g := t)).mpr hNPj'
      rwa [hNconj] at this
    rcases hcover (conjSubgroup Pj t) hNleConj hPjConjLt.le with h | h | h | h
    · exact (hPi.2.1.ne (hmax Pi (by rw [h]; exact hNltPi) hPi.2.1.le)).elim
    · exfalso
      have hc := congrArg (fun X => conjSubgroup X t⁻¹) h
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one, htPiConj_inv] at hc
      exact hPiPj hc.symm
    · exact Subgroup.mem_normalizer_iff.mpr fun x => by rw [← mem_conjSubgroup_iff, h]
    · exact (hPjConjLt.ne h).elim
  obtain ⟨Pstar, hPstarMax, hPstarNonfix⟩ := hDyn.2
  have hPstarLt : Pstar < J := hPstarMax.2.1
  have hPstarMax' : ∀ Y, Pstar < Y → Y ≤ J → Y = J := hPstarMax.2.2.1
  obtain ⟨Sstar, -, hSstarJ, hSstar2, hSstarOdd, hSstarN⟩ := hPstarMax.2.2.2
  have hSstarSyl : IsSylowIn 2 Sstar J := by
    refine ⟨hSstarJ, ?_, hSstarOdd⟩
    intro s
    obtain ⟨k, hk⟩ := hSstar2 s.1 s.2
    exact ⟨k, Subtype.ext (by simpa using Subgroup.mem_bot.mp hk)⟩
  obtain ⟨l, hlJ, hl⟩ :=
    Ch1Sec3.exists_conj_of_isSylowIn (h.isSylowIn_inf_component hJ) hSstarSyl
  have hqJ : l⁻¹ ∈ J := J.inv_mem hlJ
  have hSstareq : Sstar = conjSubgroup (T ⊓ J) l⁻¹ := by
    ext x
    rw [mem_conjSubgroup_iff]
    simpa using hl x
  have hJNSstar : J ⊓ Subgroup.normalizer (Sstar : Set Q) = conjSubgroup N l⁻¹ := by
    have hJl : conjSubgroup J l⁻¹ = J := by
      rw [conjSubgroup]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (J.inv_mem hqJ))
    have hmapinf : conjSubgroup (J ⊓ Subgroup.normalizer ((T ⊓ J : Subgroup Q) : Set Q)) l⁻¹ =
        conjSubgroup J l⁻¹ ⊓
          conjSubgroup (Subgroup.normalizer ((T ⊓ J : Subgroup Q) : Set Q)) l⁻¹ := by
      rw [conjSubgroup, Subgroup.map_inf _ _ _ (MulAut.conj (l⁻¹)⁻¹).injective]
      rfl
    calc J ⊓ Subgroup.normalizer (Sstar : Set Q)
        = J ⊓ conjSubgroup (Subgroup.normalizer ((T ⊓ J : Subgroup Q) : Set Q)) l⁻¹ := by
          rw [hSstareq, wc813pbor_normalizer_conjSubgroup]
      _ = conjSubgroup J l⁻¹ ⊓
            conjSubgroup (Subgroup.normalizer ((T ⊓ J : Subgroup Q) : Set Q)) l⁻¹ := by
          rw [hJl]
      _ = conjSubgroup (J ⊓ Subgroup.normalizer ((T ⊓ J : Subgroup Q) : Set Q)) l⁻¹ :=
          hmapinf.symm
      _ = conjSubgroup N l⁻¹ := by rw [← hN]
  have hNleConj : N ≤ conjSubgroup Pstar l := by
    have h1 : conjSubgroup N l⁻¹ ≤ Pstar := by rw [← hJNSstar]; exact hSstarN
    have h2 : conjSubgroup (conjSubgroup N l⁻¹) l ≤ conjSubgroup Pstar l :=
      wc813pbor_conjSubgroup_le_conjSubgroup.mpr h1
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h2
  have hconjLt : conjSubgroup Pstar l < J := by
    have hJl : conjSubgroup J l = J := by
      rw [conjSubgroup]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (J.inv_mem hlJ))
    rw [← hJl]
    exact wc813pbor_conjSubgroup_lt_conjSubgroup.mpr hPstarLt
  have hconjMax : ∀ Y, conjSubgroup Pstar l < Y → Y ≤ J → Y = J :=
    fun Y => wc813pbor_conjSubgroup_max (Y := Y) (Subgroup.le_normalizer hlJ) hPstarMax'
  have hconjNeN : conjSubgroup Pstar l ≠ N := by
    intro heq
    exact (hPi.2.1.ne (hconjMax Pi (by rw [heq]; exact hNltPi) hPi.2.1.le)).elim
  rcases hcover (conjSubgroup Pstar l) hNleConj hconjLt.le with h | h | h | h
  · exact hconjNeN h
  · have hQ : Pstar = conjSubgroup Pi l⁻¹ := by
      have hc := congrArg (fun X => conjSubgroup X l⁻¹) h
      rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at hc
    have htlt : t * l⁻¹ * t⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp htNJ l⁻¹).mp hqJ
    have hmJ : (t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹ ∈ J := J.mul_mem (J.inv_mem htlt) hqJ
    have hfix : conjSubgroup Pstar (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹)) = Pstar := by
      have hm : l⁻¹ * (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹)) = t⁻¹ * l⁻¹ := by group
      calc conjSubgroup Pstar (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹))
          = conjSubgroup (conjSubgroup Pi l⁻¹) (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹)) := by rw [hQ]
        _ = conjSubgroup Pi (l⁻¹ * (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹))) :=
            conjSubgroup_conjSubgroup Pi l⁻¹ _
        _ = conjSubgroup Pi (t⁻¹ * l⁻¹) := by rw [hm]
        _ = conjSubgroup (conjSubgroup Pi t⁻¹) l⁻¹ := (conjSubgroup_conjSubgroup Pi t⁻¹ l⁻¹).symm
        _ = conjSubgroup Pi l⁻¹ := by rw [htPiConj_inv]
        _ = Pstar := hQ.symm
    exact hPstarNonfix ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹) hmJ hfix
  · have hQ : Pstar = conjSubgroup Pj l⁻¹ := by
      have hc := congrArg (fun X => conjSubgroup X l⁻¹) h
      rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at hc
    have htPjConj_inv : conjSubgroup Pj t⁻¹ = Pj := by
      simpa [conjSubgroup] using Subgroup.mem_normalizer_iff_map_conj_eq.mp htNPj
    have htlt : t * l⁻¹ * t⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp htNJ l⁻¹).mp hqJ
    have hmJ : (t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹ ∈ J := J.mul_mem (J.inv_mem htlt) hqJ
    have hfix : conjSubgroup Pstar (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹)) = Pstar := by
      have hm : l⁻¹ * (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹)) = t⁻¹ * l⁻¹ := by group
      calc conjSubgroup Pstar (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹))
          = conjSubgroup (conjSubgroup Pj l⁻¹) (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹)) := by rw [hQ]
        _ = conjSubgroup Pj (l⁻¹ * (t⁻¹ * ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹))) :=
            conjSubgroup_conjSubgroup Pj l⁻¹ _
        _ = conjSubgroup Pj (t⁻¹ * l⁻¹) := by rw [hm]
        _ = conjSubgroup (conjSubgroup Pj t⁻¹) l⁻¹ := (conjSubgroup_conjSubgroup Pj t⁻¹ l⁻¹).symm
        _ = conjSubgroup Pj l⁻¹ := by rw [htPjConj_inv]
        _ = Pstar := hQ.symm
    exact hPstarNonfix ((t * l⁻¹ * t⁻¹)⁻¹ * l⁻¹) hmJ hfix
  · exact hconjLt.ne h

theorem Cfg813.inf_component_eq (hF0 : OddSchurMultiplierFact) (hF3 : BorelOvergroupFact)
    (h : Cfg813 T A B R L₀) {J : Subgroup Q} (hJ : IsComponentOf J ⊤) (hS : T ⊓ J ≠ ⊥) :
    B ⊓ J = J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) := by
  classical
  have hshape : OddShape5 J := h.oddShape5 hF0 hJ
  have hsyl : IsSylowIn 2 (T ⊓ J) J := h.isSylowIn_inf_component hJ
  have hNle : J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ≤ B ⊓ J :=
    le_inf (h.normalizer_component_le hJ hS) inf_le_left
  refine le_antisymm ?_ hNle
  set P : Subgroup Q := B ⊓ J with hP
  have hNleP : J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ≤ P := by rw [hP]; exact hNle
  have hPle : P ≤ J := by rw [hP]; exact inf_le_right
  have hPne : P ≠ J := by rw [hP]; exact h.inf_component_ne_top hJ
  have hF3' := hF3 Q J (T ⊓ J) hshape hsyl
  by_cases hrank1 : IsL2 ↥J 2 ∨ IsU3 ↥J 2
  · rcases hF3'.1 hrank1 P hNleP hPle with hPN | hPJ
    · rw [← hPN]
    · exact absurd hPJ hPne
  · have hrt : RankTwoShape J := by
      rcases hshape.2.2 with h | h | h | h | h
      · exact absurd (Or.inl h) hrank1
      · exact absurd (Or.inr h) hrank1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    obtain ⟨P₁, P₂, hP₁, hP₂, hNP₁, hNP₂, hnc, hcover⟩ := hF3'.2 hrt
    have hPiPj : P₁ ≠ P₂ := by
      intro heq
      exact hnc 1 J.one_mem (by rw [conjSubgroup_one]; exact heq)
    rcases hcover P hNleP hPle with hPN | hPP₁ | hPP₂ | hPJ
    · rw [← hPN]
    · exfalso
      exact wc813pbor_dynkin_contra hF0 h hJ hrt hP₁ hP₂ hNP₁ hNP₂ hPiPj hcover hP hPle hPP₁
    · exfalso
      have hPiPj' : P₂ ≠ P₁ := fun heq => hPiPj heq.symm
      have hcover' : ∀ P', J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ≤ P' → P' ≤ J →
          P' = J ⊓ normalizer ((T ⊓ J : Subgroup Q) : Set Q) ∨ P' = P₂ ∨ P' = P₁ ∨ P' = J := by
        intro P' h1 h2
        rcases hcover P' h1 h2 with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
      exact wc813pbor_dynkin_contra hF0 h hJ hrt hP₂ hP₁ hNP₂ hNP₁ hPiPj' hcover' hP hPle hPP₂
    · exact absurd hPJ hPne

private theorem wc813pbor_mem_of_mem_normalizer_of_isSylowIn {S' H T : Subgroup Q} {ℓ : Q}
    (hS' : IsSylowIn 2 S' H) (hℓH : ℓ ∈ H) (hℓN : ℓ ∈ Subgroup.normalizer (S' : Set Q))
    (hT2 : IsPGroup 2 T) (hℓT : ℓ ∈ T) : ℓ ∈ S' := by
  have h2 : IsPGroup 2 (S' ⊔ Subgroup.zpowers ℓ : Subgroup Q) :=
    hS'.isPGroup.to_sup_of_normal_left' (hT2.to_le (Subgroup.zpowers_le.mpr hℓT))
      (Subgroup.zpowers_le.mpr hℓN)
  have heq := wc813pbor_eq_of_isSylowIn_ge hS'
    (sup_le hS'.le (Subgroup.zpowers_le.mpr hℓH)) h2 le_sup_left
  exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers ℓ)

private theorem wc813pbor_eq_one_of_odd_of_two {O T : Subgroup Q} (hO : Odd (Nat.card O))
    {ℓ : Q} (hℓO : ℓ ∈ O) (hT2 : IsPGroup 2 T) (hℓT : ℓ ∈ T) : ℓ = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT2 ⟨ℓ, hℓT⟩
  have hk2 : ℓ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk2)
  have hℓodd : Odd (orderOf ℓ) := hO.of_dvd_nat (Subgroup.orderOf_dvd_natCard O hℓO)
  rw [hj] at hℓodd
  have hj0 : j = 0 := by
    rcases j with _ | j
    · rfl
    · exact absurd (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩)
        (Nat.not_even_iff_odd.mpr hℓodd)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

theorem Cfg813.tis_astar (hF0 : OddSchurMultiplierFact) (hF1 : InvolutionCentralizerFact)
    (hF2 : FourGroupInnerFact) (hF3 : BorelOvergroupFact) (h : Cfg813 T A B R L₀)
    {J : Subgroup Q} (hJ : IsComponentOf J ⊤) (hne : ¬ A ≤ centralizer (J : Set Q)) :
    TISIn J (Astar T J A) := by
  classical
  obtain ⟨hAstarTJ, -, hAstarCard, hdecomp⟩ := h.astar_facts hF0 hF1 hF2 hJ hne
  have hSne : T ⊓ J ≠ ⊥ := by
    intro hbot
    have hAstarBot : Astar T J A = ⊥ := le_bot_iff.mp (hAstarTJ.trans (le_of_eq hbot))
    have : Nat.card (Astar T J A) = 1 := by rw [hAstarBot, Subgroup.card_bot]
    omega
  have hTB : T ≤ B := by
    have hBmem : B ∈ calNIn (⊤ : Subgroup Q) T := by
      rw [h.maxT]
      exact Set.mem_singleton B
    exact hBmem.1
  have hinf := h.inf_component_eq hF0 hF3 hJ hSne
  intro S' hS'
  have hS : IsSylowIn 2 (T ⊓ J) J := h.isSylowIn_inf_component hJ
  obtain ⟨q₀, hq₀J, hq₀⟩ := Ch1Sec3.exists_conj_of_isSylowIn hS hS'
  have hqJ : q₀⁻¹ ∈ J := J.inv_mem hq₀J
  have hS'eq : S' = conjSubgroup (T ⊓ J) q₀⁻¹ := by
    ext x
    rw [mem_conjSubgroup_iff]
    simpa using hq₀ x
  have hJBq : conjSubgroup B q₀⁻¹ ⊓ J = J ⊓ Subgroup.normalizer (S' : Set Q) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxBq, hxJ⟩ := Subgroup.mem_inf.mp hx
      have hqxB : q₀⁻¹ * x * (q₀⁻¹)⁻¹ ∈ B := mem_conjSubgroup_iff.mp hxBq
      have hqxJ : q₀⁻¹ * x * (q₀⁻¹)⁻¹ ∈ J :=
        J.mul_mem (J.mul_mem hqJ hxJ) (J.inv_mem hqJ)
      have hqxN : q₀⁻¹ * x * (q₀⁻¹)⁻¹ ∈ Subgroup.normalizer (T ⊓ J : Subgroup Q) :=
        (Subgroup.mem_inf.mp (le_of_eq hinf (Subgroup.mem_inf.mpr ⟨hqxB, hqxJ⟩))).2
      refine Subgroup.mem_inf.mpr ⟨hxJ, ?_⟩
      rw [hS'eq, wc813pbor_normalizer_conjSubgroup]
      exact mem_conjSubgroup_iff.mpr hqxN
    · intro x hx
      obtain ⟨hxJ, hxN⟩ := Subgroup.mem_inf.mp hx
      rw [hS'eq, wc813pbor_normalizer_conjSubgroup] at hxN
      have hqxN : q₀⁻¹ * x * (q₀⁻¹)⁻¹ ∈ Subgroup.normalizer (T ⊓ J : Subgroup Q) :=
        mem_conjSubgroup_iff.mp hxN
      have hqxJ : q₀⁻¹ * x * (q₀⁻¹)⁻¹ ∈ J :=
        J.mul_mem (J.mul_mem hqJ hxJ) (J.inv_mem hqJ)
      have hqxB : q₀⁻¹ * x * (q₀⁻¹)⁻¹ ∈ B :=
        (Subgroup.mem_inf.mp (le_of_eq hinf.symm (Subgroup.mem_inf.mpr ⟨hqxJ, hqxN⟩))).1
      exact Subgroup.mem_inf.mpr ⟨mem_conjSubgroup_iff.mpr hqxB, hxJ⟩
  have hkey : ∀ ℓ ∈ Astar T J A, (ℓ ∈ conjSubgroup B q₀⁻¹ ↔ ℓ ∈ S') := by
    intro ℓ hℓ
    have hℓJ : ℓ ∈ J := (hAstarTJ hℓ).2
    have hℓT : ℓ ∈ T := (hAstarTJ hℓ).1
    have hiff : ℓ ∈ conjSubgroup B q₀⁻¹ ↔ ℓ ∈ Subgroup.normalizer (S' : Set Q) := by
      have hmem : ℓ ∈ conjSubgroup B q₀⁻¹ ↔ ℓ ∈ conjSubgroup B q₀⁻¹ ⊓ J :=
        ⟨fun h => Subgroup.mem_inf.mpr ⟨h, hℓJ⟩, fun h => (Subgroup.mem_inf.mp h).1⟩
      rw [hmem, hJBq]
      exact ⟨fun h => (Subgroup.mem_inf.mp h).2, fun h => Subgroup.mem_inf.mpr ⟨hℓJ, h⟩⟩
    rw [hiff]
    exact ⟨fun hN => wc813pbor_mem_of_mem_normalizer_of_isSylowIn hS' hℓJ hN h.sylow.isPGroup hℓT,
      fun hS'ℓ => Subgroup.le_normalizer hS'ℓ⟩
  have hcBq_of : ∀ c ∈ T ⊓ Subgroup.centralizer (J : Set Q), c ∈ conjSubgroup B q₀⁻¹ := by
    intro c hc
    have hcB : c ∈ B := hTB (Subgroup.mem_inf.mp hc).1
    have hcq : q₀⁻¹ * c * (q₀⁻¹)⁻¹ = c := by
      have hcomm := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 q₀⁻¹ hqJ
      rw [hcomm]
      group
    rw [mem_conjSubgroup_iff, hcq]
    exact hcB
  rcases h.TIS q₀⁻¹ with hTISbot | hTISle
  · left
    rw [eq_bot_iff]
    intro ℓ hℓ
    rw [Subgroup.mem_bot]
    obtain ⟨hℓA, hℓS'⟩ := Subgroup.mem_inf.mp hℓ
    obtain ⟨c, hc, hℓcA⟩ := (mem_Astar.mp hℓA).2
    have hℓBq : ℓ ∈ conjSubgroup B q₀⁻¹ := (hkey ℓ hℓA).mpr hℓS'
    have hcBq : c ∈ conjSubgroup B q₀⁻¹ := hcBq_of c hc
    have hmem : ℓ * c ∈ A ⊓ conjSubgroup B q₀⁻¹ :=
      Subgroup.mem_inf.mpr ⟨hℓcA, (conjSubgroup B q₀⁻¹).mul_mem hℓBq hcBq⟩
    rw [hTISbot] at hmem
    have hlc1 : ℓ * c = 1 := Subgroup.mem_bot.mp hmem
    have hℓc_inv : ℓ = c⁻¹ := by
      calc ℓ = ℓ * c * c⁻¹ := by group
        _ = 1 * c⁻¹ := by rw [hlc1]
        _ = c⁻¹ := one_mul _
    have hℓC : ℓ ∈ Subgroup.centralizer (J : Set Q) := by
      rw [hℓc_inv]
      exact Subgroup.inv_mem _ (Subgroup.mem_inf.mp hc).2
    have hℓJ : ℓ ∈ J := (hAstarTJ hℓA).2
    have hℓZ : ℓ ∈ (Subgroup.center ↥J).map J.subtype := by
      refine Subgroup.mem_map.mpr ⟨⟨ℓ, hℓJ⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hℓC y y.2)
    have hoddZ : Odd (Nat.card ((Subgroup.center ↥J).map J.subtype)) := by
      rw [Subgroup.card_map_of_injective J.subtype_injective]
      exact h.center_odd hJ
    exact wc813pbor_eq_one_of_odd_of_two hoddZ hℓZ h.sylow.isPGroup (hAstarTJ hℓA).1
  · right
    intro ℓ hℓ
    obtain ⟨c, hc, hℓcA⟩ := (mem_Astar.mp hℓ).2
    have hcBq : c ∈ conjSubgroup B q₀⁻¹ := hcBq_of c hc
    have hℓBq : ℓ ∈ conjSubgroup B q₀⁻¹ := by
      have hmem : (ℓ * c) * c⁻¹ ∈ conjSubgroup B q₀⁻¹ :=
        (conjSubgroup B q₀⁻¹).mul_mem (hTISle hℓcA) ((conjSubgroup B q₀⁻¹).inv_mem hcBq)
      simpa [mul_assoc] using hmem
    exact (hkey ℓ hℓ).mp hℓBq

end CFSG.LocalAnalysis.WeakClosure81

end
