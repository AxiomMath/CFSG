module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHTh
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusRu
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Gen
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1Rows

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec6.BThreeCensus
  (suzukiOrder five_dvd_suzukiOrder card_eq_suzukiOrder eq_one_of_suzukiOrder_dvd_ru)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

open CFSG.HardMathSupport.Dickson.I271
  (thS thZ thU th_census thEps th_letters_spec leaf_closure_of_six)
open CFSG.Sporadic.Th (J thEquivJ)

open CFSG.GH74.QTGen4.Recog.G23 (SatisfiesG23Words)

@[expose] def NoSuzPerfect {G : Type} [Group G] (C : Subgroup G) : Prop :=
  ∀ Y : Subgroup G, Y ≤ C → Group.IsPerfect Y → ∀ a : ℕ, 1 ≤ a → ¬ suzukiOrder a ∣ Nat.card Y

theorem nosuz_of_mulEquiv_centralizer {S T : Type} [Group S] [Group T] (f : S ≃* T) {x : S}
    (h : NoSuzPerfect (Subgroup.centralizer ({f x} : Set T))) :
    NoSuzPerfect (Subgroup.centralizer ({x} : Set S)) := by
  intro Y hY hYp a ha hdvd
  have hmap : Y.map f.toMonoidHom ≤ Subgroup.centralizer ({f x} : Set T) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp (hY hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show f y * f x = f x * f y
    rw [← map_mul, ← map_mul, hy']
  haveI : Group.IsPerfect (Y.map f.toMonoidHom) := Group.IsPerfect.map _
  have hcard : Nat.card (Y.map f.toMonoidHom) = Nat.card Y :=
    Subgroup.card_map_of_injective f.injective
  exact h _ hmap inferInstance a ha (by rw [hcard]; exact hdvd)

theorem nosuz_centralizer_conj {G : Type} [Group G] {x : G} (c : G)
    (h : NoSuzPerfect (Subgroup.centralizer ({x} : Set G))) :
    NoSuzPerfect (Subgroup.centralizer ({c * x * c⁻¹} : Set G)) := by
  have hfix : (MulAut.conj c⁻¹ : G ≃* G) (c * x * c⁻¹) = x := by
    rw [MulAut.conj_apply]
    group
  exact nosuz_of_mulEquiv_centralizer (MulAut.conj c⁻¹ : G ≃* G) (x := c * x * c⁻¹)
    (by rw [hfix]; exact h)

theorem nosuz_of_pow_three_conj {G : Type} [Group G] {c : G} (hc : c ^ 3 = 1) {e : ℕ}
    (he : e = 1 ∨ e = 2) (h : NoSuzPerfect (Subgroup.centralizer ({c} : Set G))) (k : G) :
    NoSuzPerfect (Subgroup.centralizer ({k * c ^ e * k⁻¹} : Set G)) := by
  have h' : NoSuzPerfect (Subgroup.centralizer ({c ^ e} : Set G)) := by
    rw [centralizer_pow_of_pow_three hc he]
    exact h
  exact nosuz_centralizer_conj k h'

theorem pow_six_dvd_suzukiOrder {a : ℕ} (ha : 1 ≤ a) : 2 ^ 6 ∣ suzukiOrder a := by
  unfold suzukiOrder
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
  rw [← pow_mul]
  exact pow_dvd_pow 2 (by omega)

theorem noSuz_of_not_two_pow_six_dvd {N : ℕ} (h2 : ¬ 2 ^ 6 ∣ N) {a : ℕ} (ha : 1 ≤ a) :
    ¬ suzukiOrder a ∣ N :=
  fun h => h2 ((pow_six_dvd_suzukiOrder ha).trans h)

theorem perfect_le_of_simple_small_index {G : Type} [Group G] [Finite G] {C E : Subgroup G}
    (hEC : E ≤ C) [hEs : IsSimpleGroup E] (hCm : Nat.card C ≤ 14 * Nat.card E)
    (hdvd : ¬ Nat.card E ∣ Nat.factorial 14) {K : Subgroup G} (hKC : K ≤ C)
    [hKp : Group.IsPerfect K] : K ≤ E := by
  set E' : Subgroup C := E.subgroupOf C with hE'def
  have eE : E' ≃* E := Subgroup.subgroupOfEquivOfLe hEC
  haveI : IsSimpleGroup E' := eE.isSimpleGroup
  have hE'card : Nat.card E' = Nat.card E := Nat.card_congr eE.toEquiv
  have hidx : E'.index ≤ 14 := by
    have hmul := Subgroup.card_mul_index E'
    rw [hE'card] at hmul
    have hE0 : 0 < Nat.card E := Nat.card_pos
    by_contra hlt
    have hlt' : 14 + 1 ≤ E'.index := by omega
    have : Nat.card E * (14 + 1) ≤ Nat.card E * E'.index := Nat.mul_le_mul_left _ hlt'
    nlinarith
  have hpos : 0 < E'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  set N := E'.normalCore with hNdef
  have hNE : N ≤ E' := E'.normalCore_le
  have hNnormal : (N.subgroupOf E').Normal := Subgroup.normal_subgroupOf
  have hNcases := hNnormal.eq_bot_or_eq_top
  have hNeq : N = E' := by
    rcases hNcases with h | h
    · exfalso
      rw [Subgroup.subgroupOf_eq_bot] at h
      have hN1 : N = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hx (hNE hx))
      have hdiv : N.index ∣ E'.index.factorial := E'.index_normalCore_dvd_factorial_index
      rw [hN1, Subgroup.index_bot] at hdiv
      apply hdvd
      calc Nat.card E ∣ Nat.card C := Subgroup.card_dvd_of_le hEC
        _ ∣ E'.index.factorial := hdiv
        _ ∣ Nat.factorial 14 := Nat.factorial_dvd_factorial hidx
    · exact le_antisymm hNE (Subgroup.subgroupOf_eq_top.mp h)
  haveI hE'n : E'.Normal := hNeq ▸ E'.normalCore_normal
  set K' : Subgroup C := K.subgroupOf C with hK'def
  haveI : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  haveI : Group.IsPerfect (K'.map (QuotientGroup.mk' E')) := Group.IsPerfect.map _
  have hpf : (Nat.card (K'.map (QuotientGroup.mk' E'))).primeFactors.card ≤ 2 := by
    have hd : Nat.card (K'.map (QuotientGroup.mk' E')) ∣ E'.index :=
      Subgroup.card_subgroup_dvd_card _
    have h1 : E'.index.primeFactors.card ≤ 2 := by
      interval_cases h : E'.index <;> exact primeFactors_card_le_two_of_twoPrimeOK (by decide)
    exact (Finset.card_le_card (Nat.primeFactors_mono hd (by omega))).trans h1
  haveI := subsingleton_of_isPerfect_of_card_primeFactors hpf
  have hbot : K'.map (QuotientGroup.mk' E') = ⊥ := Subgroup.eq_bot_of_subsingleton _
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro k hk
  exact hbot (show (⟨k, hKC hk⟩ : C) ∈ K.subgroupOf C from hk)

theorem mulAut_inner_of_card_outer_eq_one {X : Type} [Group X] (h : Nat.card (Outer X) = 1)
    (φ : MulAut X) : ∃ g : X, φ = MulAut.conj g := by
  have h' : (CFSG.ComponentClassification.OuterAutomorphisms.inner X).index = 1 := h
  have htop : CFSG.ComponentClassification.OuterAutomorphisms.inner X = ⊤ :=
    Subgroup.index_eq_one.mp h'
  have hφ : φ ∈ (MulAut.conj : X →* MulAut X).range := by
    have : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
      rw [htop]
      exact Subgroup.mem_top φ
    exact this
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hφ
  exact ⟨g, hg.symm⟩

theorem row143_of_inner_kgroup {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a)
    (hOut : ∀ P : Subgroup (MulAut S), IsKGroup ↥P → Group.IsPerfect ↥P → ¬ 3 ∣ Nat.card ↥P →
      P ≤ (MulAut.conj : S →* MulAut S).range)
    (hNoSz : ∀ β : MulAut S, β ^ 3 = 1 → ∀ Y : Subgroup S, Y ≤ Sec4.autFix β →
      (Y.subgroupOf (Sec4.autFix β)).IsSubnormal → IsKGroup ↥Y → Group.IsPerfect ↥Y →
      ¬ 3 ∣ Nat.card ↥Y → Y = ⊥) :
    Row143 S := by
  unfold Row143
  intro β hβ3 _ D hDfix hDnorm hDpow P hPK hPcent hPnorm hPperf hP3
  have hPle : P ≤ (MulAut.conj : S →* MulAut S).range := hOut P hPK hPperf hP3
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_isSimpleGroup hS hnc
  set Y : Subgroup S := P.comap (MulAut.conj : S →* MulAut S) with hYdef
  have hYmap : Y.map (MulAut.conj : S →* MulAut S) = P := by
    rw [hYdef, Subgroup.map_comap_eq, inf_eq_right.mpr hPle]
  let e : Y ≃* P :=
    (Y.equivMapOfInjective (MulAut.conj : S →* MulAut S) hinj).trans (MulEquiv.subgroupCongr hYmap)
  have hcard : Nat.card Y = Nat.card P := Nat.card_congr e.toEquiv
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hcard]
    exact hP3
  have hYperf : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hYK : IsKGroup Y := hPK.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hYfix : Y ≤ Sec4.autFix β := by
    intro y hy
    have hyP : MulAut.conj y ∈ P := hy
    have hcent : MulAut.conj y * β = β * MulAut.conj y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPcent hyP)
    have h2 : MulAut.conj (β y) * β = MulAut.conj y * β :=
      (mulAut_conj_comm_apply β y).trans hcent.symm
    have h3 : MulAut.conj (β y) = MulAut.conj y := mul_right_cancel h2
    exact Sec4.mem_autFix.mpr (hinj h3)
  have hYnorm : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y := by
    intro d hd y hy
    have hyP : MulAut.conj y ∈ P := hy
    have hn := (Subgroup.mem_set_normalizer_iff.mp (hPnorm d hd) (MulAut.conj y)).mp hyP
    show MulAut.conj (d * y * d⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hn
  have hYD : Y ≤ D := by
    intro y hy
    obtain ⟨n, hn⟩ := hDpow y (hYfix hy)
    have hcop : Nat.Coprime (3 ^ n) (orderOf y) := by
      refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
      intro h
      exact hY3 (h.trans (Subgroup.orderOf_dvd_natCard Y hy))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hmem : (y ^ 3 ^ n) ^ m ∈ D := D.pow_mem hn m
    rwa [hm] at hmem
  have hYsub : (Y.subgroupOf (Sec4.autFix β)).IsSubnormal :=
    isSubnormal_subgroupOf_of_normalizes hYD hDnorm hYnorm
  have hYbot : Y = ⊥ := hNoSz β hβ3 Y hYfix hYsub hYK hYperf hY3
  rw [eq_bot_iff]
  intro p hp
  obtain ⟨y, rfl⟩ := hPle hp
  have hyY : y ∈ Y := hp
  rw [hYbot, Subgroup.mem_bot] at hyY
  rw [Subgroup.mem_bot, hyY, map_one]

theorem nosuz_forall_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : ∀ x : T', orderOf x = 3 → NoSuzPerfect (Subgroup.centralizer ({x} : Set T'))) :
    ∀ x : T, orderOf x = 3 → NoSuzPerfect (Subgroup.centralizer ({x} : Set T)) :=
  fun x hx => nosuz_of_mulEquiv_centralizer e (h (e x) ((MulEquiv.orderOf_eq e x).trans hx))

section Certs

theorem hNoSz_of_centralizers {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (h3 : 3 ∣ Nat.card S)
    (hinner : ∀ φ : MulAut S, ∃ g : S, φ = MulAut.conj g)
    (hC : ∀ x : S, orderOf x = 3 → NoSuzPerfect (Subgroup.centralizer ({x} : Set S))) :
    ∀ β : MulAut S, β ^ 3 = 1 → ∀ Y : Subgroup S, Y ≤ Sec4.autFix β →
      (Y.subgroupOf (Sec4.autFix β)).IsSubnormal → IsKGroup ↥Y → Group.IsPerfect ↥Y →
      ¬ 3 ∣ Nat.card ↥Y → Y = ⊥ := by
  intro β hβ Y hYfix hYsub hYK hYperf hY3
  by_cases hβ1 : β = 1
  ·
    subst hβ1
    have hA : Sec4.autFix (1 : MulAut S) = ⊤ := by
      ext x
      simp [Sec4.mem_autFix]
    have hsimp : IsSimpleGroup ↥(Sec4.autFix (1 : MulAut S)) :=
      ((MulEquiv.subgroupCongr hA).trans Subgroup.topEquiv).isSimpleGroup
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimp hYsub with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      rw [eq_bot_iff]
      intro y hy
      have hyA : y ∈ Sec4.autFix (1 : MulAut S) := by
        rw [hA]
        exact Subgroup.mem_top y
      exact Subgroup.mem_bot.mpr (Subgroup.disjoint_def.mp h hy hyA)
    · rw [Subgroup.subgroupOf_eq_top] at h
      exfalso
      apply hY3
      have htop : (⊤ : Subgroup S) ≤ Y := by
        rw [← hA]
        exact h
      have hYtop : Y = ⊤ := eq_top_iff.mpr htop
      rw [hYtop, Subgroup.card_top]
      exact h3
  ·
    obtain ⟨g, rfl⟩ := hinner β
    have hg3 : g ^ 3 = 1 := by
      have h1 : MulAut.conj (g ^ 3) = MulAut.conj (1 : S) := by
        rw [map_pow, map_one]
        exact hβ
      exact conj_injective_of_isSimpleGroup hS hnc h1
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hβ1 (by rw [map_one])
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hgo : orderOf g = 3 := orderOf_eq_prime hg3 hg1
    rw [autFix_conj] at hYfix
    by_contra hYne
    haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
    obtain ⟨N, _, f, hf⟩ := exists_suzuki_section_of_isPerfect hYK hYperf hY3 inferInstance
    obtain ⟨a, ha, hcard⟩ := card_eq_suzukiOrder hf
    have hdvd : suzukiOrder a ∣ Nat.card ↥Y := by
      rw [← hcard]
      exact Subgroup.card_quotient_dvd_card N
    exact hC g hgo Y hYfix hYperf a ha hdvd

theorem row143_of_centralizers {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (h3 : 3 ∣ Nat.card S)
    (hinner : ∀ φ : MulAut S, ∃ g : S, φ = MulAut.conj g)
    (hC : ∀ x : S, orderOf x = 3 → NoSuzPerfect (Subgroup.centralizer ({x} : Set S))) :
    Row143 S :=
  row143_of_inner_kgroup hS hnc
    (fun P _ _ _ => by
      intro φ _
      obtain ⟨g, hg⟩ := hinner φ
      exact ⟨g, hg.symm⟩)
    (hNoSz_of_centralizers hS hnc h3 hinner hC)

section ThCerts

theorem nosuz_thS : NoSuzPerfect (Subgroup.centralizer ({thS} : Set ↥J)) := by
  haveI : Finite ↥J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  obtain ⟨hrel, hcomm, hne⟩ := th_letters_spec
  have hε : SatisfiesG23Words thEps := fun r hr =>
    (CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.lift_mk_eq_evalW _ r).trans
      (hrel r hr)
  obtain ⟨-, hsimp, -, hcard⟩ := leaf_closure_of_six thEps hε hne
  haveI := hsimp
  have hEC : Subgroup.closure (Set.range thEps) ≤ Subgroup.centralizer ({thS} : Set ↥J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i).symm
  have hC : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤ 63685439 :=
    CFSG.HardMathSupport.Dickson.Sec6.th3_facts.2.2.2.2.2
  have hsmall : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤
      14 * Nat.card ↥(Subgroup.closure (Set.range thEps)) := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEC
    rw [hcard] at hk ⊢
    omega
  have hndvd : ¬ Nat.card ↥(Subgroup.closure (Set.range thEps)) ∣ Nat.factorial 14 := by
    rw [hcard]
    decide
  intro Y hY _ a _ hdvd
  have hYE : Y ≤ Subgroup.closure (Set.range thEps) :=
    perfect_le_of_simple_small_index hEC hsmall hndvd hY
  have hd : Nat.card Y ∣ 4245696 := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hYE
  exact (by norm_num : ¬ 5 ∣ 4245696) ((five_dvd_suzukiOrder a).trans (hdvd.trans hd))

theorem nosuz_thZ : NoSuzPerfect (Subgroup.centralizer ({thZ} : Set ↥J)) := by
  haveI : Finite ↥J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  intro Y hY _ a _ hdvd
  have hd : Nat.card Y ∣ 2 ^ 3 * 3 ^ 10 :=
    (Subgroup.card_dvd_of_le hY).trans CFSG.HardMathSupport.Dickson.I271.card_centralizer_zJ_dvd
  exact (by norm_num : ¬ 5 ∣ 2 ^ 3 * 3 ^ 10) ((five_dvd_suzukiOrder a).trans (hdvd.trans hd))

theorem nosuz_thU : NoSuzPerfect (Subgroup.centralizer ({thU} : Set ↥J)) := by
  haveI : Finite ↥J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  intro Y hY _ a ha hdvd
  have hC : Nat.card ↥(Subgroup.centralizer ({thU} : Set ↥J)) = 174960 :=
    CFSG.RankThree.PartTwo.Sec4.RonanK432.th_card_centralizer_U
  have hd : Nat.card Y ∣ 174960 := by
    rw [← hC]
    exact Subgroup.card_dvd_of_le hY
  exact (noSuz_of_not_two_pow_six_dvd (N := 174960) (by norm_num) ha) (hdvd.trans hd)

theorem nosuz_J (y : ↥J) (hy : orderOf y = 3) :
    NoSuzPerfect (Subgroup.centralizer ({y} : Set ↥J)) := by
  obtain ⟨k, c, hc, e, he, rfl⟩ := th_census y hy
  obtain ⟨hs3, hz3, hu3⟩ := th_reps_pow_three
  rcases hc with rfl | rfl | rfl
  · exact nosuz_of_pow_three_conj hs3 he nosuz_thS k
  · exact nosuz_of_pow_three_conj hz3 he nosuz_thZ k
  · exact nosuz_of_pow_three_conj hu3 he nosuz_thU k

theorem row143_of_thJ {S T : Type} [Group S] [Finite S] [Group T] (f : S ≃* T)
    (hOut : Nat.card (Outer S) = 1)
    (hT : ∀ y : T, orderOf y = 3 → NoSuzPerfect (Subgroup.centralizer ({y} : Set T)))
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a) (h3 : 3 ∣ Nat.card S) : Row143 S := by
  refine row143_of_centralizers hS hnc h3 (mulAut_inner_of_card_outer_eq_one hOut) (fun x hx => ?_)
  exact nosuz_of_mulEquiv_centralizer f (hT (f x) ((MulEquiv.orderOf_eq f x).trans hx))

theorem rowOf143_spor_th : RowOf143 (Spor .Th) := by
  intro S _ _ hS hnc ⟨e⟩ h3
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have e' : S ≃* Blueprint.NativeSporadic.Carrier .Th := e.trans b.symm
  have hTh : Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) = 1 :=
    CFSG.RankThree.PartOne.SPOR.card_outer_Th_native
  have hOut : Nat.card (Outer S) = 1 := by
    rw [Nat.card_congr (equivalence e').toEquiv, hTh]
  have hT : ∀ y : Blueprint.NativeSporadic.Th, orderOf y = 3 →
      NoSuzPerfect (Subgroup.centralizer ({y} : Set Blueprint.NativeSporadic.Th)) :=
    @nosuz_forall_of_mulEquiv Blueprint.NativeSporadic.Th ↥J Units.instGroup _ thEquivJ
      (fun y hy => nosuz_J y hy)
  exact row143_of_thJ (T := Blueprint.NativeSporadic.Th) e' hOut hT hS hnc h3

end ThCerts

section RuCerts

theorem row143_of_ruP {S : Type} [Group S] [Finite S]
    (f : S ≃* CFSG.Sporadic.RuSchreier.ruP) (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (h3 : 3 ∣ Nat.card S) : Row143 S := by
  have hcard : Nat.card S = 145926144000 := by
    rw [Nat.card_congr f.toEquiv, CFSG.Sporadic.RuSchreier.card_ruP']
  have hinner : ∀ φ : MulAut S, ∃ g : S, φ = MulAut.conj g := by
    intro φ
    obtain ⟨g, hg⟩ := CFSG.Sporadic.RuSchreier.mulAut_inner (MulAut.congr f φ)
    refine ⟨f.symm g, ?_⟩
    apply (MulAut.congr f).injective
    rw [hg, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, f.apply_symm_apply]
  have hno7 : ∀ x y : S, orderOf x = 3 → orderOf y = 7 → x * y ≠ y * x := by
    intro x y hx hy hxy
    have hfx : orderOf ((f x : ↥CFSG.Sporadic.RuSchreier.ruP) : Equiv.Perm (Fin 4060)) = 3 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
    have hfy : orderOf ((f y : ↥CFSG.Sporadic.RuSchreier.ruP) : Equiv.Perm (Fin 4060)) = 7 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
    have hcom : ((f x : ↥CFSG.Sporadic.RuSchreier.ruP) : Equiv.Perm (Fin 4060)) *
        ((f y : ↥CFSG.Sporadic.RuSchreier.ruP) : Equiv.Perm (Fin 4060)) =
        ((f y : ↥CFSG.Sporadic.RuSchreier.ruP) : Equiv.Perm (Fin 4060)) *
        ((f x : ↥CFSG.Sporadic.RuSchreier.ruP) : Equiv.Perm (Fin 4060)) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hxy]
    exact CFSG.RankThree.PartTwo.Sec6.BThreeCensus.false_of_commute (f x).2 (f y).2 hfx hfy hcom
  have hC : ∀ x : S, orderOf x = 3 → NoSuzPerfect (Subgroup.centralizer ({x} : Set S)) := by
    intro x hx Y hY hYp a ha hdvd
    haveI := hYp
    have hdvdS : suzukiOrder a ∣ 145926144000 := by
      rw [← hcard]
      exact hdvd.trans (Subgroup.card_subgroup_dvd_card Y)
    obtain rfl : a = 1 := eq_one_of_suzukiOrder_dvd_ru ha hdvdS
    have h7 : 7 ∣ Nat.card ↥Y := (show 7 ∣ suzukiOrder 1 by decide).trans hdvd
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy7⟩ := exists_prime_orderOf_dvd_card' 7 h7
    have hyC : (y : S) ∈ Subgroup.centralizer ({x} : Set S) := hY y.2
    have hord : orderOf (y : S) = 7 := by
      rw [Subgroup.orderOf_coe]
      exact hy7
    exact hno7 x (y : S) hx hord (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
  exact row143_of_centralizers hS hnc h3 hinner hC

theorem rowOf143_spor_ru : RowOf143 (Spor .Ru) := by
  intro S _ _ hS hnc ⟨e⟩ h3
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  exact row143_of_ruP ((e.trans b.symm).trans CFSG.Sporadic.RuSchreier.ruEquivP) hS hnc h3

end RuCerts

end Certs

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
