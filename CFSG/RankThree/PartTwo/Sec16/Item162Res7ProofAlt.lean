module

public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Subgroup MulAction Equiv Equiv.Perm
open scoped Pointwise

namespace Res162Seven

theorem no_small_index_of_card_20160 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 20160)
    (hnA : ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω], 5 ≤ Fintype.card Ω →
      IsEmpty (Y ≃* alternatingGroup Ω))
    (M : Subgroup Y) (hM : M ≠ ⊤) : 11 < M.index := by
  classical
  obtain ⟨M1, hM1, hMM1⟩ := (eq_top_or_exists_le_coatom M).resolve_left hM
  have hidx : M1.index ≤ M.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hMM1)
  suffices h : 11 < M1.index from lt_of_lt_of_le h hidx
  by_contra hle
  push Not at hle
  have hM1top : M1 ≠ ⊤ := hM1.1
  have hm1 : M1.index ≠ 1 := fun h => hM1top (Subgroup.index_eq_one.mp h)
  have hm0 : M1.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  let Ω := Y ⧸ M1
  have : Fintype Ω := Fintype.ofFinite Ω
  have hΩ' : Nat.card Ω = M1.index := rfl
  have hΩcard : Fintype.card Ω = M1.index := by rw [← hΩ', Nat.card_eq_fintype_card]
  have hnt : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have hpre : IsPreprimitive Y Ω := by
    rw [← isCoatom_stabilizer_iff_preprimitive Y ((1 : Y) : Ω), MulAction.stabilizer_quotient]
    exact hM1
  let φ : Y →* Perm Ω := MulAction.toPermHom Y Ω
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker φ) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
      obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y a b
      have hyk : y ∈ MonoidHom.ker φ := h ▸ mem_top y
      have h1 : φ y = 1 := hyk
      have h2 : y • a = a := by
        have := congrArg (fun f : Perm Ω => f a) h1
        simpa [φ] using this
      exact hab (h2.symm.trans hy)
  let R : Subgroup (Perm Ω) := φ.range
  have hRcard : Nat.card R = 20160 := by
    rw [← hcard]; exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hprimR : IsPreprimitive R Ω := by
    have := hpre
    exact IsPreprimitive.of_surjective (M := Y) (N := R) (α := Ω) (β := Ω) (φ := φ.rangeRestrict)
      (f := ⟨id, fun y a => rfl⟩) Function.surjective_id
  have hdvd : 20160 ∣ (M1.index).factorial := by
    have h1 : Nat.card R ∣ Nat.card (Perm Ω) := Subgroup.card_subgroup_dvd_card R
    rw [hRcard, Nat.card_perm, hΩ'] at h1
    exact h1
  have hm8 : 8 ≤ M1.index := by
    by_contra h8
    push Not at h8
    generalize M1.index = m at hdvd hm0 hm1 h8
    interval_cases m
    all_goals first | exact absurd rfl hm1 | exact absurd rfl hm0 | (revert hdvd; decide)
  have hJordan : ∀ p : ℕ, p.Prime → p ∣ 20160 → 2 * p > M1.index → p + 3 ≤ M1.index →
      alternatingGroup Ω ≤ R := by
    intro p hp hpd hlarge hsmall
    have : Fact p.Prime := ⟨hp⟩
    have hd : p ∣ Nat.card R := by rw [hRcard]; exact hpd
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := R) p hd
    have hg : orderOf (u : Perm Ω) = p := (Subgroup.orderOf_coe u).trans hu
    have hc : (u : Perm Ω).IsCycle := Equiv.Perm.isCycle_of_prime_order
      (by rw [hg]; exact hp) (by
        have hs' := Finset.card_le_univ (u : Perm Ω).support
        rw [hg]; omega)
    have hs : (u : Perm Ω).support.card = p := hc.orderOf.symm.trans hg
    exact
      CFSG.FiveTransitive.OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
      hprimR hp (by rw [hΩ']; omega) hc hs u.property
  have hAle : alternatingGroup Ω ≤ R := by
    by_cases h10 : 10 ≤ M1.index
    · exact hJordan 7 (by decide) (by norm_num) (by omega) (by omega)
    · exact hJordan 5 (by decide) (by norm_num) (by omega) (by omega)
  have hle2 : Nat.card (alternatingGroup Ω) ≤ 20160 := hRcard ▸ Subgroup.card_le_of_le hAle
  have h2 : 2 * Nat.card (alternatingGroup Ω) = Nat.card (Perm Ω) :=
    two_mul_nat_card_alternatingGroup
  rw [Nat.card_perm, hΩ'] at h2
  have hm8' : M1.index = 8 := by
    by_contra hne
    have h9 : 9 ≤ M1.index := by omega
    have : Nat.factorial 9 ≤ Nat.factorial M1.index := Nat.factorial_le h9
    have h9' : Nat.factorial 9 = 362880 := by decide
    omega
  have hAeq : alternatingGroup Ω = R := by
    apply Subgroup.eq_of_le_of_card_ge hAle
    rw [hRcard]
    rw [hm8'] at h2
    have h8' : Nat.factorial 8 = 40320 := by decide
    omega
  have hΩ8 : 5 ≤ Fintype.card Ω := by rw [hΩcard]; omega
  exact (hnA Ω hΩ8).false
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hAeq.symm))

theorem lt_index_of_mulEquiv_l34 {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (e : Y ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))
    (M : Subgroup Y) (hM : M ≠ ⊤) : 11 < M.index := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩
  have hSt : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 3 2 2 :=
    ⟨hadm, GaloisField 2 2, inferInstance, inferInstance, by
      rw [KFacts.L34.card_galoisField_two_two]
      norm_num, ⟨e.trans (KFacts.KS44.projSLEquivStatedProj _)⟩⟩
  obtain ⟨hcard, -, hnA⟩ :=
    CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated Y hSt
  exact no_small_index_of_card_20160 hcard (fun Ω _ _ h5 => hnA Ω h5) M hM

theorem card_range_eq_mul {J K : Type*} [Group J] [Group K] [Finite J] (F : J →* K)
    (P : Subgroup J) [P.Normal] (hkerP : F.ker ≤ P) :
    Nat.card F.range = Nat.card (J ⧸ P) * Nat.card (P.map F) := by
  have h1 : Nat.card F.ker * Nat.card F.range = Nat.card J := by
    rw [← Subgroup.index_ker F]
    exact Subgroup.card_mul_index F.ker
  have h2 : Nat.card (J ⧸ P) * Nat.card P = Nat.card J := by
    rw [← Subgroup.index_eq_card, mul_comm]
    exact Subgroup.card_mul_index P
  have h3 : Nat.card F.ker * Nat.card (P.map F) = Nat.card P := by
    have h := Subgroup.card_mul_index (F.domRestrict P).ker
    rw [Subgroup.index_ker, MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h
    rw [← h]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerP).toEquiv).symm
  have hk : 0 < Nat.card F.ker := Nat.card_pos
  have h4 : Nat.card F.ker * Nat.card F.range =
      Nat.card F.ker * (Nat.card (J ⧸ P) * Nat.card (P.map F)) := by
    rw [h1, ← h2, ← h3]
    ring
  exact Nat.eq_of_mul_eq_mul_left hk h4

theorem sq_apply_eq_of_ncard_le_two {α : Type*} {O : Set α} (hO : O.Finite) (h2 : O.ncard ≤ 2)
    {g : Equiv.Perm α} {x : α} (hx : x ∈ O) (hgx : g x ∈ O) (hggx : g (g x) ∈ O) :
    g (g x) = x := by
  by_contra hne
  by_cases h1 : g x = x
  · rw [h1, h1] at hne
    exact hne rfl
  · have h3 : g (g x) ≠ g x := fun h => h1 (g.injective h)
    have hsub : ({x, g x, g (g x)} : Set α) ⊆ O := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact hx
      · exact hgx
      · exact hggx
    have hx' : x ∉ ({g x, g (g x)} : Set α) := by
      rintro (h | h)
      · exact h1 h.symm
      · exact hne h.symm
    have hcard : ({x, g x, g (g x)} : Set α).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem hx', Set.ncard_pair h3.symm]
    have := Set.ncard_le_ncard hsub hO
    omega

theorem false_of_perm_ten {J : Type} [Group J] [Finite J]
    (F : J →* Equiv.Perm (Fin 10)) (hFA : F.range ≤ alternatingGroup (Fin 10))
    (P : Subgroup J) [P.Normal] (hP2 : IsPGroup 2 P) (hkerP : F.ker ≤ P)
    [IsSimpleGroup (J ⧸ P)] (e : J ⧸ P ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) :
    False := by
  classical
  have hcard := card_range_eq_mul F P hkerP
  have hJP : Nat.card (J ⧸ P) = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    exact KFacts.L34.card_projSL
  have hA10 : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 10)
    rw [Nat.card_perm] at h
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h ⊢
    have h10 : Nat.factorial 10 = 3628800 := by decide
    omega
  have hdvd : Nat.card F.range ∣ 1814400 := hA10 ▸ Subgroup.card_dvd_of_le hFA
  have hFPle : Nat.card (P.map F) ≤ 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP2.map F)
    rw [hcard, hJP, show (1814400 : ℕ) = 20160 * 90 by norm_num] at hdvd
    have h90 : Nat.card (P.map F) ∣ 90 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    rw [hk] at h90 ⊢
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h4.trans h90
      norm_num at this
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := by norm_num
  have hstab : ∀ (x : Fin 10) (j : J), ∃ p ∈ P, F j x = F p x := by
    intro x j
    let _ : MulAction J (Fin 10) := MulAction.compHom (Fin 10) F
    have hsmul : ∀ (j : J) (y : Fin 10), j • y = F j y := fun _ _ => rfl
    set S := MulAction.stabilizer J x with hS
    have hidx : S.index ≤ 10 := by
      rw [hS, MulAction.index_stabilizer]
      calc Nat.card (MulAction.orbit J x) ≤ Nat.card (Fin 10) :=
            Finite.card_subtype_le (fun y => y ∈ MulAction.orbit J x)
        _ = 10 := by simp
    have himg : S.map (QuotientGroup.mk' P) = ⊤ := by
      by_contra hne
      have h11 := lt_index_of_mulEquiv_l34 e _ hne
      have hd := Subgroup.index_map_dvd (H := S) (QuotientGroup.mk'_surjective P)
      have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      have := Nat.le_of_dvd hpos hd
      omega
    have hsup : P ⊔ S = ⊤ := by
      have h := Subgroup.comap_map_eq (QuotientGroup.mk' P) S
      rw [himg, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
      rw [h, sup_comm]
    have hj : j ∈ ((P : Set J) * (S : Set J)) := by
      rw [← Subgroup.normal_mul, hsup]
      exact Subgroup.mem_top j
    obtain ⟨p, hp, s, hs, rfl⟩ := hj
    refine ⟨p, hp, ?_⟩
    have hsx : F s x = x := by
      have := MulAction.mem_stabilizer_iff.mp hs
      rwa [hsmul] at this
    rw [map_mul, Equiv.Perm.mul_apply, hsx]
  have hsq : ∀ j : J, F j ^ 2 = 1 := by
    intro j
    refine Equiv.ext fun x => ?_
    set O := Set.range fun q : P.map F => (q : Equiv.Perm (Fin 10)) x with hO
    have hOcard : O.ncard ≤ 2 := by
      rw [← Nat.card_coe_set_eq]
      exact (Finite.card_range_le _).trans hFPle
    have hmem : ∀ p ∈ P, F p x ∈ O := fun p hp => ⟨⟨F p, Subgroup.mem_map_of_mem F hp⟩, rfl⟩
    have hxO : x ∈ O := by
      have := hmem 1 (one_mem P)
      rwa [map_one, Equiv.Perm.one_apply] at this
    have hgx : F j x ∈ O := by
      obtain ⟨p, hp, h⟩ := hstab x j
      rw [h]
      exact hmem p hp
    have hggx : F j (F j x) ∈ O := by
      obtain ⟨p, hp, h⟩ := hstab x (j * j)
      rw [map_mul, Equiv.Perm.mul_apply] at h
      rw [h]
      exact hmem p hp
    rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact sq_apply_eq_of_ncard_le_two (Set.toFinite O) hOcard hxO hgx hggx
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : 7 ∣ Nat.card F.range := by
    rw [hcard, hJP]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h7
  obtain ⟨j, hj⟩ := g.2
  have hg2 : (g : Equiv.Perm (Fin 10)) ^ 2 = 1 := by
    rw [← hj]
    exact hsq j
  have h72 := orderOf_dvd_of_pow_eq_one hg2
  rw [Subgroup.orderOf_coe, hg] at h72
  norm_num at h72

theorem two_pow_dvd_card_of_isoLThreePi {Y : Type} [Group Y] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec4.IsoLThreePi Y 2 n) : (2 ^ n) ^ 3 ∣ Nat.card Y := by
  have hcop : ∀ x : ℕ, Nat.Coprime ((2 ^ n) ^ 3) (Nat.gcd 3 x) := fun x =>
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 x)
      (Nat.Coprime.pow_left 3 (Nat.Coprime.pow_left n (by norm_num)))
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
    rw [GaloisField.card 2 n (by omega), ← Nat.card_congr φ.toEquiv] at hc
    exact (hcop _).dvd_of_dvd_mul_right (Dvd.intro _ hc.symm)
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
    rw [← Nat.card_congr φ.toEquiv] at hc
    exact (hcop _).dvd_of_dvd_mul_right (Dvd.intro _ hc.symm)

theorem card_of_isoLThreePi_one {Y : Type} [Group Y] (h : Sec4.IsoLThreePi Y 2 1) :
    Nat.card Y = 72 := by
  rcases h with ⟨h3, -⟩ | ⟨-, ⟨φ⟩⟩
  · norm_num at h3
  · have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
    rw [← Nat.card_congr φ.toEquiv] at hc
    norm_num at hc
    omega

theorem false_of_alt {G : Type} [Group G] [Finite G]
    {I J : Subgroup G} (hJI : J ≤ I) {m : ℕ}
    (ψ : ↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin m)) (hm : m = 7 ∨ m = 10)
    (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) {n : ℕ} (hn : 1 ≤ n)
    (hiso : Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F : ↥J →* Equiv.Perm (Fin m) := (alternatingGroup (Fin m)).subtype.comp
    (ψ.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥I)).comp (Subgroup.inclusion hJI)))
    with hF
  have hFA : F.range ≤ alternatingGroup (Fin m) := by
    rintro _ ⟨k, rfl⟩
    exact (ψ _).2
  have hP2 : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
  have hker : ∀ k : ↥J, F k = 1 → Subgroup.inclusion hJI k ∈ CFSG.pCore 2 ↥I := by
    intro k hk
    have h1 : ψ (QuotientGroup.mk' (CFSG.pCore 2 ↥I) (Subgroup.inclusion hJI k)) = 1 := by
      apply Subtype.ext
      simpa [hF] using hk
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hker2 : IsPGroup 2 F.ker := by
    intro k
    obtain ⟨r, hr⟩ :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥I)) ⟨_, hker k (MonoidHom.mem_ker.mp k.2)⟩
    refine ⟨r, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg (fun z : ↥(CFSG.pCore 2 ↥I) => ((z : ↥I) : G)) hr
    simpa using h1
  have hkerP : F.ker ≤ CFSG.pCore 2 ↥J := le_sSup ⟨inferInstance, hker2⟩
  obtain ⟨hsimp, -, h20160, -⟩ := Sec13.typeFacts135_isoLThreePi hn hq hiso
  have hcard := card_range_eq_mul F (CFSG.pCore 2 ↥J) hkerP
  have hdvdA : Nat.card F.range ∣ Nat.card (alternatingGroup (Fin m)) :=
    Subgroup.card_dvd_of_le hFA
  have hYdvd : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) ∣ Nat.card (alternatingGroup (Fin m)) :=
    (Dvd.intro _ hcard.symm).trans hdvdA
  rcases hm with rfl | rfl
  ·
    have hAm : 2 * Nat.card (alternatingGroup (Fin 7)) = Nat.factorial 7 := by
      have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
      rw [Nat.card_perm] at h
      simpa using h
    have h7 : Nat.factorial 7 = 5040 := by decide
    have hle := Nat.le_of_dvd (by omega) hYdvd
    omega
  ·
    have hAm : 2 * Nat.card (alternatingGroup (Fin 10)) = Nat.factorial 10 := by
      have h := two_mul_nat_card_alternatingGroup (α := Fin 10)
      rw [Nat.card_perm] at h
      simpa using h
    have h10 : Nat.factorial 10 = 3628800 := by decide
    have hA : Nat.card (alternatingGroup (Fin 10)) = 1814400 := by omega
    rw [hA] at hYdvd
    have h2n := (two_pow_dvd_card_of_isoLThreePi hn hiso).trans hYdvd
    have hn2 : n ≤ 2 := by
      by_contra hn3
      have h9 : 2 ^ 9 ∣ (2 ^ n) ^ 3 := by
        rw [← pow_mul]
        exact pow_dvd_pow 2 (by omega)
      have := h9.trans h2n
      norm_num at this
    rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
    · have h72 := card_of_isoLThreePi_one hiso
      omega
    · rcases hiso with ⟨-, ⟨e⟩⟩ | ⟨h3, -⟩
      · exact false_of_perm_ten F hFA (CFSG.pCore 2 ↥J) hP2 hkerP e
      · norm_num at h3

end Res162Seven

open Res162Seven in
theorem ks162AltNoL3Two :
    ∀ (G : Type) [Group G] [Finite G] (I J : Subgroup G), J ≤ I →
      (Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 10))) →
      CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) →
      ∀ n : ℕ, 1 ≤ n → ¬ Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n := by
  intro G _ _ I J hJI hI hq n hn hiso
  rcases hI with ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
  · exact false_of_alt hJI ψ (Or.inl rfl) hq hn hiso
  · exact false_of_alt hJI ψ (Or.inr rfl) hq hn hiso

end CFSG.RankThree.PartTwo.Sec16
