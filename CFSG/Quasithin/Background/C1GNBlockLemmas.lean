
module

public import CFSG.Quasithin.Background.A1a
public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.EmptyFaithful.S14111

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace C1GN

section Subgroups

variable {G : Type} [Group G] [Finite G]

theorem charTwo_of_le {X T U : Subgroup G} (hF : CharTwo X) (hT : IsSylowTwoOf T X)
    (hTU : T ≤ U) (hUX : U ≤ X) : CharTwo U :=
  centralizer_pCoreOf_le_of_sylow (p := 2) hUX hT.2.1 hTU hT.2.2 hF

omit [Finite G] in
theorem isSylowTwoOf_of_le {X T U : Subgroup G} (hT : IsSylowTwoOf T X) (hTU : T ≤ U)
    (hUX : U ≤ X) : IsSylowTwoOf T U := by
  refine ⟨hTU, hT.2.1, fun h => hT.2.2 ?_⟩
  have h1 : T.relIndex U * U.relIndex X = T.relIndex X :=
    Subgroup.relIndex_mul_relIndex T U X hTU hUX
  exact h.trans (Dvd.intro _ h1)

theorem kGroup_of_injective {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (hB : CFSG.SectionRank.IsKGroupCat B) :
    CFSG.SectionRank.IsKGroupCat A :=
  (hB.subgroup f.range).of_mulEquiv (MonoidHom.ofInjective hf)

theorem IsSQTKTC.mono {X U : Subgroup G} (hUX : U ≤ X) (hX : IsSQTKTC X) : IsSQTKTC U := by
  obtain ⟨hK, hS⟩ := hX
  refine ⟨kGroup_of_injective (Subgroup.inclusion hUX) (Subgroup.inclusion_injective hUX) hK, ?_⟩
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup ↥X) ≤ 2 := hS p hp hp2
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥U) = CFSG.Open.pRank p U :=
    pRank_top_subtype (p := p) U
  have h2 : CFSG.Open.pRank p U ≤ CFSG.Open.pRank p X :=
    CFSG.SectionRank.pRank_mono hp.one_lt hUX
  have h4 : CFSG.Open.pRank p (⊤ : Subgroup ↥X) = CFSG.Open.pRank p X :=
    pRank_top_subtype (p := p) X
  show CFSG.Open.pRank p (⊤ : Subgroup ↥U) ≤ 2
  omega

end Subgroups

section Quasisimple

theorem commutator_top_le_of_decomp {Y : Type*} [Group Y] (A : Subgroup Y) [A.Normal]
    (hdec : ∀ y : Y, ∃ a ∈ A, ∃ z ∈ Subgroup.center Y, y = a * z) :
    ⁅(⊤ : Subgroup Y), ⊤⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hdec x
  obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := hdec y
  rw [← QuotientGroup.eq_one_iff (N := A)]
  have h := map_commutatorElement (QuotientGroup.mk' A) (a₁ * z₁) (a₂ * z₂)
  have hA1 : (QuotientGroup.mk' A) a₁ = 1 := (QuotientGroup.eq_one_iff (N := A) a₁).2 ha₁
  have hA2 : (QuotientGroup.mk' A) a₂ = 1 := (QuotientGroup.eq_one_iff (N := A) a₂).2 ha₂
  have e1 : (QuotientGroup.mk' A) (a₁ * z₁) = (QuotientGroup.mk' A) z₁ := by
    rw [map_mul, hA1, one_mul]
  have e2 : (QuotientGroup.mk' A) (a₂ * z₂) = (QuotientGroup.mk' A) z₂ := by
    rw [map_mul, hA2, one_mul]
  rw [e1, e2] at h
  have hc : (QuotientGroup.mk' A) z₁ * (QuotientGroup.mk' A) z₂ =
      (QuotientGroup.mk' A) z₂ * (QuotientGroup.mk' A) z₁ := by
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz₂ z₁)]
  have h2 : ⁅(QuotientGroup.mk' A) z₁, (QuotientGroup.mk' A) z₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 hc
  rw [h2] at h
  exact h

theorem le_center_of_ne_top {Y : Type*} [Group Y] (hY : CFSG.IsQuasisimple Y ∨ Nat.card Y = 3)
    (B : Subgroup Y) [B.Normal] (hB : B ≠ ⊤) : B ≤ Subgroup.center Y := by
  rcases hY with ⟨hperf, hsimple, -⟩ | h3
  · have hc : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = (⊤ : Subgroup Y) := by
      rw [← _root_.commutator_def]; exact hperf.commutator_eq_top
    have hnorm : (B.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases hsimple.eq_bot_or_eq_top_of_normal (B.map (QuotientGroup.mk' (Subgroup.center Y))) with
      h | h
    · intro b hb
      have h1 : QuotientGroup.mk' (Subgroup.center Y) b ∈
          B.map (QuotientGroup.mk' (Subgroup.center Y)) := ⟨b, hb, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff b).1 h1
    · exfalso
      apply hB
      have hBZtop : ∀ y : Y, ∃ b ∈ B, ∃ z ∈ Subgroup.center Y, y = b * z := by
        intro y
        have h1 : QuotientGroup.mk' (Subgroup.center Y) y ∈
            B.map (QuotientGroup.mk' (Subgroup.center Y)) := by rw [h]; trivial
        obtain ⟨b, hb, hby⟩ := h1
        refine ⟨b, hb, b⁻¹ * y, ?_, by group⟩
        rw [← QuotientGroup.ker_mk' (Subgroup.center Y), MonoidHom.mem_ker, map_mul, map_inv, hby,
          inv_mul_cancel]
      have hcomm := commutator_top_le_of_decomp B hBZtop
      rw [hc] at hcomm
      exact top_le_iff.1 hcomm
  · have : Fact (Nat.card Y).Prime := ⟨by rw [h3]; exact Nat.prime_three⟩
    rw [(Subgroup.eq_bot_or_eq_top_of_prime_card B).resolve_right hB]
    exact bot_le

theorem eq_top_or_eq_top_of_sup_eq_top {Y : Type*} [Group Y]
    (hY : CFSG.IsQuasisimple Y ∨ Nat.card Y = 3) (A B : Subgroup Y) [A.Normal] [B.Normal]
    (hAB : A ⊔ B = ⊤) : A = ⊤ ∨ B = ⊤ := by
  by_cases hB : B = ⊤
  · exact Or.inr hB
  · left
    rcases hY with hq | h3
    · have hBZ := le_center_of_ne_top (Or.inl hq) B hB
      have hdec : ∀ y : Y, ∃ a ∈ A, ∃ z ∈ Subgroup.center Y, y = a * z := by
        intro y
        have : y ∈ A ⊔ B := hAB ▸ Subgroup.mem_top y
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 this
        exact ⟨a, ha, b, hBZ hb, rfl⟩
      have hcomm := commutator_top_le_of_decomp A hdec
      have hc : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = (⊤ : Subgroup Y) := by
        rw [← _root_.commutator_def]; exact hq.1.commutator_eq_top
      rw [hc] at hcomm
      exact top_le_iff.1 hcomm
    · have : Fact (Nat.card Y).Prime := ⟨by rw [h3]; exact Nat.prime_three⟩
      have hBbot : B = ⊥ := (Subgroup.eq_bot_or_eq_top_of_prime_card B).resolve_right hB
      rw [hBbot, sup_bot_eq] at hAB
      exact hAB

end Quasisimple

section Short

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isShort2_eq_top_of_sup_pCore {L : Subgroup G} (hL : IsShort2 L) (N : Subgroup ↥L)
    [N.Normal] (h : N ⊔ CFSG.pCore 2 ↥L = ⊤) : N = ⊤ := by
  refine hL.1 N ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hx : x ∈ N ⊔ CFSG.pCore 2 ↥L := h ▸ Subgroup.mem_top x
    obtain ⟨n, hn, p, hp, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨p, hp⟩
    refine ⟨k, ?_⟩
    have hpk : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hn1 : (QuotientGroup.mk n : ↥L ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [QuotientGroup.mk_mul, hn1, one_mul, ← QuotientGroup.mk_pow, hpk, QuotientGroup.mk_one]

omit [Finite G] in
theorem isShort2_eq_top_or_eq_top_of_sup {L : Subgroup G} (hL : IsShort2 L) (A B : Subgroup ↥L)
    [A.Normal] [B.Normal] (h : A ⊔ B = ⊤) : A = ⊤ ∨ B = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hAn : (A.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  have hBn : (B.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  have hAB : A.map π ⊔ B.map π = ⊤ := by
    rw [← Subgroup.map_sup, h, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 hπ
  have key : ∀ (N : Subgroup ↥L) [N.Normal], N.map π = ⊤ → N = ⊤ := by
    intro N _ hN
    apply isShort2_eq_top_of_sup_pCore hL N
    have := Subgroup.comap_map_eq π N
    rw [hN, Subgroup.comap_top] at this
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]
    exact this.symm
  rcases eq_top_or_eq_top_of_sup_eq_top hL.2.2.2.1 (A.map π) (B.map π) hAB with h1 | h1
  · exact Or.inl (key A h1)
  · exact Or.inr (key B h1)

omit [Finite G] in
theorem isShort2_perfect_of_perfect_quotient {L : Subgroup G} (hL : IsShort2 L)
    (hQ : commutator (↥L ⧸ CFSG.pCore 2 ↥L) = ⊤) : ⁅L, L⁆ = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hmap : (commutator ↥L).map π = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact hQ
  apply isShort2_eq_top_of_sup_pCore hL
  have := Subgroup.comap_map_eq π (commutator ↥L)
  rw [hmap, Subgroup.comap_top] at this
  rw [QuotientGroup.ker_mk'] at this
  exact this.symm

theorem isShort2_eq_bot_of_perfect_le_proper_normal {L K P : Subgroup G} (hL : IsShort2 L) (hPL : P ≤ L)
    (hPn : (P.subgroupOf L).Normal) (hPne : P ≠ L) (hKP : K ≤ P) (hK : ⁅K, K⁆ = K) :
    K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hPn' : (P.subgroupOf L).Normal := hPn
  have hPm : ((P.subgroupOf L).map π).Normal := Subgroup.Normal.map inferInstance π hπ
  have hP1 : P.subgroupOf L ≠ ⊤ := fun h => hPne (le_antisymm hPL (Subgroup.subgroupOf_eq_top.1 h))
  have hP2 : (P.subgroupOf L).map π ≠ ⊤ := by
    intro hP
    apply hP1
    apply isShort2_eq_top_of_sup_pCore hL
    have := Subgroup.comap_map_eq π (P.subgroupOf L)
    rw [hP, Subgroup.comap_top] at this
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]
    exact this.symm
  have hcen := le_center_of_ne_top hL.2.2.2.1 _ hP2
  have hKQ : K ≤ pCoreOf 2 L := by
    rw [← hK]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    set a' : ↥L := ⟨a, hPL (hKP ha)⟩
    set b' : ↥L := ⟨b, hPL (hKP hb)⟩
    have ha' : π a' ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
      hcen ⟨a', hKP ha, rfl⟩
    have h1 : ⁅π a', π b'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 ((Subgroup.mem_center_iff.1 ha' (π b')).symm)
    have h2 : π ⁅a', b'⁆ = 1 := by rw [map_commutatorElement, h1]
    have h3 : ⁅a', b'⁆ ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).1 h2
    exact ⟨⁅a', b'⁆, h3, rfl⟩
  have hKp : IsPGroup 2 K := (pCoreOf_isPGroup 2 L).to_le hKQ
  have hnil : Group.IsNilpotent ↥K := hKp.isNilpotent
  have hsolv : Group.IsSolvable ↥K := inferInstance
  by_contra hKne
  have hnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hKne
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K)
  have hperf : commutator ↥K = ⊤ := (Subgroup.isPerfect_iff.2 hK).commutator_eq_top
  exact absurd hperf hlt.ne

omit [Finite G] in
theorem blockU_le_self (L : Subgroup G) : blockU L ≤ L := by
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have haL : a ∈ L := pCoreOf_le 2 L ha
  rw [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem haL hb) (L.inv_mem haL)) (L.inv_mem hb)

omit [Finite G] in
theorem isShort2_ne_bot {L : Subgroup G} (hL : IsShort2 L) : L ≠ ⊥ := by
  intro h
  have h1 : blockZ L < blockU L := hL.2.2.2.2.1
  have h2 : blockU L ≤ ⊥ := h ▸ blockU_le_self L
  exact absurd (lt_of_lt_of_le h1 h2) (not_lt_of_ge bot_le)

theorem mem_cComp_of_short {L Y : Subgroup G} (hL : IsShort2 L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hsub : IsSubnormal L Y) :
    L ∈ cComp Y := by
  have hperf : ⁅L, L⁆ = L := isShort2_perfect_of_perfect_quotient hL hq.1.commutator_eq_top
  refine ⟨isShort2_ne_bot hL, hperf, hsub, fun K hKL hKne hKperf hKsub => ?_⟩
  have hKL' : IsSubnormal K L := A3.subnormal_of_le_of_le hKsub hKL.le (A3.subnormal_le hsub)
  obtain ⟨P, hPL, hPn, hKP⟩ := A3.subnormal_exists_normal_of_lt hKL' hKL
  exact hKne (isShort2_eq_bot_of_perfect_le_proper_normal hL hPL.le hPn hPL.ne hKP hKperf)

end Short

section Alternating

variable {G : Type} [Group G] [Finite G]

theorem isSimpleGroup_alternating_of_odd {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    IsSimpleGroup (alternatingGroup (Fin m)) := by
  by_cases h3 : m = 3
  · subst h3
    refine isSimpleGroup_of_prime_card (p := 3) ?_
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  · have h5 : 5 ≤ Nat.card (Fin m) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      obtain ⟨k, rfl⟩ := hm
      omega
    exact alternatingGroup.isSimpleGroup h5

theorem three_dvd_card_alternating {m : ℕ} (hm : 3 ≤ m) :
    3 ∣ Nat.card (alternatingGroup (Fin m)) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  have h1 : 3 ∣ m.factorial := Nat.dvd_factorial (by norm_num) hm
  have h2 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  obtain ⟨c, hc⟩ := h2
  rw [hc, Nat.mul_div_cancel_left c (by norm_num)]
  rw [hc] at h1
  exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h1

theorem three_dvd_card_sl2 (F : Type) [Field F] :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  let A : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two_of]⟩
  have h3 : A ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  have hne : A ≠ 1 := by
    intro h
    have := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp [A] at this
  have hord : orderOf A = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h3 hne
  rw [← hord]
  exact orderOf_dvd_natCard A

omit [Finite G] in
theorem three_dvd_card_of_isChiBlock {X L : Subgroup G} (h : IsChiBlock X L) :
    3 ∣ Nat.card L := by
  rcases h.2 with ⟨n, hn, F, hF, hFt, hcard, α, hα, -⟩ | ⟨m, hm, hm3, α, hα, -⟩
  · exact (three_dvd_card_sl2 F).trans (Subgroup.card_dvd_of_surjective hα)
  · exact (three_dvd_card_alternating hm3).trans (Subgroup.card_dvd_of_surjective hα)

omit [Finite G] in
theorem not_le_of_isAltQuotient {K C : Subgroup G} {n : ℕ} (h : IsAltQuotient K C n) (hn : 3 ≤ n) :
    ¬ K ≤ C := by
  obtain ⟨φ, hφ, hker⟩ := h
  intro hKC
  have h1 : φ.ker = ⊤ := by rw [hker]; exact Subgroup.subgroupOf_eq_top.2 hKC
  have hsub : Subsingleton (alternatingGroup (Fin n)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    have hx : φ x = 1 := MonoidHom.mem_ker.1 (h1 ▸ Subgroup.mem_top x)
    have hy : φ y = 1 := MonoidHom.mem_ker.1 (h1 ▸ Subgroup.mem_top y)
    rw [hx, hy]
  have h2 := three_dvd_card_alternating hn
  rw [Nat.card_of_subsingleton (1 : alternatingGroup (Fin n))] at h2
  omega

omit [Finite G] in
theorem isShort2_eq_of_isAltQuotient {L C N : Subgroup G} (hL : IsShort2 L) {m : ℕ}
    (hm : Odd m) (hm3 : 3 ≤ m) (hq : IsAltQuotient L C m) (hNL : N ≤ L)
    (hNnorm : L ≤ Subgroup.normalizer (N : Set G)) (hNC : ¬ N ≤ C) : N = L := by
  obtain ⟨φ, hφ, hker⟩ := hq
  have hNn : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2 hNnorm
  have hsimple := isSimpleGroup_alternating_of_odd hm hm3
  have hmapn : ((N.subgroupOf L).map φ).Normal := Subgroup.Normal.map hNn φ hφ
  have hne : (N.subgroupOf L).map φ ≠ ⊥ := by
    intro h
    apply hNC
    intro x hx
    have hxL : x ∈ L := hNL hx
    have h1 : φ ⟨x, hxL⟩ ∈ (N.subgroupOf L).map φ :=
      ⟨⟨x, hxL⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 : (⟨x, hxL⟩ : ↥L) ∈ φ.ker := h1
    rw [hker] at h2
    exact Subgroup.mem_subgroupOf.1 h2
  have htop : (N.subgroupOf L).map φ = ⊤ :=
    (@IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hmapn).resolve_left hne
  have hsup : N.subgroupOf L ⊔ φ.ker = ⊤ := by
    rw [eq_top_iff]
    intro l _
    obtain ⟨n, hn, hnl⟩ : φ l ∈ (N.subgroupOf L).map φ := htop ▸ Subgroup.mem_top _
    have hker' : n⁻¹ * l ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnl, inv_mul_cancel]
    have := Subgroup.mul_mem_sup hn hker'
    simpa using this
  rcases isShort2_eq_top_or_eq_top_of_sup hL (N.subgroupOf L) φ.ker hsup with h | h
  · exact le_antisymm hNL (Subgroup.subgroupOf_eq_top.1 h)
  · exfalso
    apply hNC
    rw [hker] at h
    exact hNL.trans (Subgroup.subgroupOf_eq_top.1 h)

omit [Finite G] in
theorem isQuasisimple_of_isExceptionalA7Block {L : Subgroup G} (h : IsExcA7Block L) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨hshort, ⟨α, hα, hker⟩, -⟩ := h
  rcases hshort.2.2.2.1 with hq | h3
  · exact hq
  · exfalso
    have e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ α.ker) :=
      QuotientGroup.quotientMulEquivOfEq hker.symm
    have e2 := QuotientGroup.quotientKerEquivOfSurjective α hα
    have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (alternatingGroup (Fin 7)) :=
      Nat.card_congr (e1.trans e2).toEquiv
    rw [h3, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hcard
    revert hcard
    decide

end Alternating

section Rank

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_three_pow {ι : Type*} [DecidableEq ι] (B : ι → Subgroup G)
    (S : Finset ι) (hB2 : ∀ i ∈ S, CharTwo (B i)) (hB3 : ∀ i ∈ S, 3 ∣ Nat.card (B i))
    (hcomm : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ⁅B i, B j⁆ = ⊥) :
    ∃ E : Subgroup G, E ≤ ⨆ i ∈ S, B i ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ S.card := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⊥, by simp, ⟨inferInstance, fun x hx => ?_⟩, by simp⟩
    rw [(Subgroup.mem_bot.1 hx), one_pow]
  | insert a S ha ih =>
    obtain ⟨E, hES, hE, hcard⟩ := ih (fun i hi => hB2 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hB3 i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hcomm i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(B a)) 3
      (hB3 a (Finset.mem_insert_self a S))
    have hy' : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
    have hle : (⨆ i ∈ S, B i) ≤ Subgroup.centralizer (B a : Set G) :=
      iSup₂_le fun i hi => Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (hcomm i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a S)
          (fun h => ha (h ▸ hi)))
    have hcommE : ∀ e ∈ E, Commute e (y : G) := fun e he =>
      (Subgroup.mem_centralizer_iff.1 (hle (hES he)) (y : G) y.2).symm
    have hyE : (y : G) ∉ E := by
      intro hyE
      have hyc : (y : G) ∈ Subgroup.centralizer (B a : Set G) := hle (hES hyE)
      have hyO : (y : G) ∈ pCoreOf 2 (B a) := by
        refine hB2 a (Finset.mem_insert_self a S) ⟨y.2, ?_⟩
        show (y : G) ∈ Subgroup.centralizer (pCoreOf 2 (B a) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact Subgroup.mem_centralizer_iff.1 hyc h (pCoreOf_le 2 (B a) hh)
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (B a)) ⟨(y : G), hyO⟩
      have hk' : (y : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hdvd : orderOf (y : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      rw [hy'] at hdvd
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
      omega
    obtain ⟨hE', hcard'⟩ := exists_elemAbelian_sup_zpowers hE hy' hcommE hyE
    refine ⟨E ⊔ Subgroup.zpowers (y : G), sup_le ?_ ?_, hE', ?_⟩
    · exact hES.trans (biSup_mono (Finset.subset_insert a S))
    · exact (Subgroup.zpowers_le.2 y.2).trans
        (le_iSup₂_of_le a (Finset.mem_insert_self a S) le_rfl)
    · rw [hcard', hcard, Finset.card_insert_of_notMem ha, pow_succ]

theorem three_blocks_false {X A B C : Subgroup G} (hX : IsSQTKTC X)
    (hAX : A ≤ X) (hBX : B ≤ X) (hCX : C ≤ X)
    (h2 : CharTwo A ∧ CharTwo B ∧ CharTwo C)
    (h3 : 3 ∣ Nat.card A ∧ 3 ∣ Nat.card B ∧ 3 ∣ Nat.card C)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hc : ⁅A, B⁆ = ⊥ ∧ ⁅A, C⁆ = ⊥ ∧ ⁅B, C⁆ = ⊥) : False := by
  classical
  obtain ⟨hcAB, hcAC, hcBC⟩ := hc
  have hcard : ({A, B, C} : Finset (Subgroup G)).card = 3 :=
    Finset.card_eq_three.2 ⟨A, B, C, hAB, hAC, hBC, rfl⟩
  obtain ⟨E, hEle, hE, hEcard⟩ := exists_elemAbelian_three_pow (fun K : Subgroup G => K)
    {A, B, C}
    (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      exacts [h2.1, h2.2.1, h2.2.2])
    (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      exacts [h3.1, h3.2.1, h3.2.2])
    (by
      intro i hi j hj hij
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hij
        | assumption
        | (rwa [Subgroup.commutator_comm]))
  have hEX : E ≤ X := by
    refine hEle.trans (iSup₂_le fun i hi => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    exacts [hAX, hBX, hCX]
  rw [hcard] at hEcard
  have hrank : 3 ≤ CFSG.Open.pRank 3 X := le_pRank Nat.prime_three hEX hE hEcard
  have hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) ≤ 2 := hX.2 3 Nat.prime_three (by norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X) = CFSG.Open.pRank 3 X :=
    pRank_top_subtype (p := 3) X
  omega

end Rank

end C1GN

end CFSG.Quasithin
