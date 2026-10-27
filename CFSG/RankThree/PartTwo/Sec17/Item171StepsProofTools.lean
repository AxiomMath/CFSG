module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof171Steps

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.GH74.GLS
open scoped commutatorElement Pointwise

section Residual

variable {X : Type*} [Group X]

theorem oPrimeResidual_three_normal' : (oPrimeResidual 3 X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  unfold oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    exact Subgroup.subset_closure ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact inv_mem hx

theorem mem_oPrimeResidual_of_pow {x : X} {k : ℕ} (hx : x ^ 3 ^ k = 1) :
    x ∈ oPrimeResidual 3 X :=
  Subgroup.subset_closure ⟨k, hx⟩

omit [Group X] in
theorem exists_lift_three_element {Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (x₀ : X) {j : ℕ} (hy : f x₀ ^ (3 ^ j) = 1) :
    ∃ (x : X) (i : ℕ), x ^ (3 ^ i) = 1 ∧ f x = f x₀ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn : orderOf x₀ ≠ 0 := (orderOf_pos x₀).ne'
  obtain ⟨a, m, hmp, hnm⟩ : ∃ a m : ℕ, Nat.Coprime 3 m ∧ 3 ^ a * m = orderOf x₀ :=
    ⟨_, _, Nat.coprime_ordCompl hp hn, Nat.ordProj_mul_ordCompl_eq_self _ _⟩
  obtain ⟨b, hb, hdb⟩ : ∃ b ≤ j, orderOf (f x₀) = 3 ^ b :=
    (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hy)
  have hcop2 : Nat.Coprime (orderOf (f x₀)) m := by
    rw [hdb]; exact Nat.Coprime.pow_left _ hmp
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop2 1 0
  refine ⟨x₀ ^ (k : ℕ), a, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := Nat.modEq_zero_iff_dvd.1 hk2
    have : (k : ℕ) * 3 ^ a = orderOf x₀ * c := by rw [hc, ← hnm]; ring
    rw [← pow_mul, this, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, (pow_eq_pow_iff_modEq (x := f x₀) (n := k) (m := 1)).2 hk1, pow_one]

omit [Group X] in
theorem map_oPrimeResidual_three {Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    (hf : Function.Surjective f) : (oPrimeResidual 3 X).map f = oPrimeResidual 3 Y := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨k, hk⟩
    apply Subgroup.subset_closure
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨k, hk⟩
    obtain ⟨x₀, rfl⟩ := hf y
    obtain ⟨x, i, hx, hfx⟩ := exists_lift_three_element f x₀ hk
    exact ⟨x, Subgroup.subset_closure ⟨i, hx⟩, hfx⟩

theorem not_three_dvd_of_oPrimeResidual_eq_bot [Finite X] (h : oPrimeResidual 3 X = ⊥) :
    ¬ 3 ∣ Nat.card X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hmem : x ∈ oPrimeResidual 3 X :=
    mem_oPrimeResidual_of_pow (k := 1) (by rw [pow_one, ← hx, pow_orderOf_eq_one])
  rw [h, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hx
  norm_num at hx

theorem oPrimeResidual_eq_top_of_isSimpleGroup [Finite X] [IsSimpleGroup X]
    (h3 : 3 ∣ Nat.card X) : oPrimeResidual 3 X = ⊤ := by
  have := oPrimeResidual_three_normal' (X := X)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oPrimeResidual 3 X) with hb | ht
  · exact absurd h3 (not_three_dvd_of_oPrimeResidual_eq_bot hb)
  · exact ht

theorem oPrimeResidual_eq_top_of_isQuasisimple [Finite X] (hq : CFSG.IsQuasisimple X)
    (hz : Subgroup.center X = ⊥) (h3 : 3 ∣ Nat.card X) : oPrimeResidual 3 X = ⊤ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (oPrimeResidual_three_normal' (X := X))
    with h | h
  · exact h
  · rw [hz, le_bot_iff] at h
    exact absurd h3 (not_three_dvd_of_oPrimeResidual_eq_bot h)

theorem oPrimeResidual_eq_top_of_mulEquiv {Y : Type*} [Group Y] [Finite Y] (e : X ≃* Y)
    (h : oPrimeResidual 3 Y = ⊤) : oPrimeResidual 3 X = ⊤ := by
  have hmap := map_oPrimeResidual_three e.symm.toMonoidHom e.symm.surjective
  rw [h, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.symm.surjective] at hmap
  exact hmap.symm

theorem oPrimeResidual_eq_top_of_isTripleCover {S : Type*} [Group S] [Finite X] [Finite S]
    (h : Sec4.IsTripleCover X S) (hS : oPrimeResidual 3 S = ⊤) : oPrimeResidual 3 X = ⊤ := by
  obtain ⟨hz, ⟨φ⟩⟩ := h
  set Zc := Subgroup.center X with hZc
  have h1 : (oPrimeResidual 3 X).map (QuotientGroup.mk' Zc) = ⊤ := by
    rw [map_oPrimeResidual_three (QuotientGroup.mk' Zc) (QuotientGroup.mk'_surjective _)]
    exact oPrimeResidual_eq_top_of_mulEquiv φ hS
  have h2 : Zc ≤ oPrimeResidual 3 X := by
    intro z hz'
    refine mem_oPrimeResidual_of_pow (k := 1) ?_
    have hdvd : orderOf (⟨z, hz'⟩ : Zc) ∣ 3 := hz ▸ orderOf_dvd_natCard _
    rw [pow_one]
    have := pow_orderOf_eq_one (⟨z, hz'⟩ : Zc)
    obtain ⟨m, hm⟩ := hdvd
    have h3 : (⟨z, hz'⟩ : Zc) ^ 3 = 1 := by rw [hm, pow_mul, this, one_pow]
    simpa using congrArg Subtype.val h3
  rw [eq_top_iff]
  intro x _
  have hx : QuotientGroup.mk' Zc x ∈ (oPrimeResidual 3 X).map (QuotientGroup.mk' Zc) :=
    h1 ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y⁻¹ * x ∈ Zc := QuotientGroup.eq.mp hyx
  have := mul_mem hy (h2 hyx')
  rwa [mul_inv_cancel_left] at this

theorem oPrimeResidual_alternatingGroup_six : oPrimeResidual 3 (alternatingGroup (Fin 6)) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  refine oPrimeResidual_eq_top_of_isSimpleGroup ?_
  have h2 := two_mul_card_alternatingGroup (α := Fin 6)
  rw [Fintype.card_perm, Fintype.card_fin] at h2
  rw [Nat.card_eq_fintype_card]
  have : Fintype.card (alternatingGroup (Fin 6)) = 360 := by
    have : Nat.factorial 6 = 720 := by decide
    omega
  rw [this]
  norm_num

theorem map_oPrimeResidual_subtype_le (U : Subgroup X) :
    (oPrimeResidual 3 U).map U.subtype ≤ oPrimeResidual 3 X := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  obtain ⟨k, hk⟩ := hu
  exact mem_oPrimeResidual_of_pow (k := k) (by rw [← map_pow, hk, map_one])

theorem oPrimeResidual_eq_top_of_isCentralProductA6Covers [Finite X]
    (h : Sec14.IsCentralProductA6Covers X) : oPrimeResidual 3 X = ⊤ := by
  obtain ⟨U, V, -, -, hUV, -, -, hU, hV⟩ := h
  have hU' := oPrimeResidual_eq_top_of_isTripleCover hU oPrimeResidual_alternatingGroup_six
  have hV' := oPrimeResidual_eq_top_of_isTripleCover hV oPrimeResidual_alternatingGroup_six
  have hUle : U ≤ oPrimeResidual 3 X := by
    have h := map_oPrimeResidual_subtype_le U
    rwa [hU', ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hVle : V ≤ oPrimeResidual 3 X := by
    have h := map_oPrimeResidual_subtype_le V
    rwa [hV', ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rw [eq_top_iff, ← hUV]
  exact sup_le hUle hVle

end Residual

section Perfect

variable {G : Type*} [Group G] [Finite G]

theorem eq_oPrimeResidualOf_of_hom {T : Type*} [Group T] {X : Subgroup G}
    (hXp : Group.IsPerfect ↥X) (f : ↥X →* T) (hker : Group.IsSolvable ↥f.ker)
    (h : oPrimeResidual 3 ↥f.range = ⊤) : X = oPrimeResidualOf 3 X := by
  set N := oPrimeResidual 3 ↥X with hNdef
  have hNn : N.Normal := oPrimeResidual_three_normal'
  set f' : ↥X →* ↥f.range := f.rangeRestrict with hf'
  have hsurj' : Function.Surjective f' := MonoidHom.rangeRestrict_surjective f
  have hsup : N ⊔ f.ker = ⊤ := by
    have h1 := map_oPrimeResidual_three f' hsurj'
    rw [h] at h1
    have h2 := Subgroup.comap_map_eq f' (oPrimeResidual 3 ↥X)
    rw [h1, Subgroup.comap_top, MonoidHom.ker_rangeRestrict] at h2
    exact h2.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp f.ker.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ N ⊔ f.ker := hsup ▸ Subgroup.mem_top x
    rw [Subgroup.mem_sup_of_normal_left] at hx
    obtain ⟨n, hn, t, ht, rfl⟩ := hx
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have hsolv : Group.IsSolvable (↥X ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hperf : Group.IsPerfect (↥X ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hNtop : N = ⊤ := by
    by_contra hne
    have : Nontrivial (↥X ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isSolvable (↥X ⧸ N) hsolv
  rw [oPrimeResidualOf, ← hNdef, hNtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem eq_oPrimeResidualOf_of_quot {X : Subgroup G} (hXp : Group.IsPerfect ↥X)
    (h : oPrimeResidual 3 (↥X ⧸ aschbacherSolvableCore 3 ↥X) = ⊤) :
    X = oPrimeResidualOf 3 X := by
  set θ := aschbacherSolvableCore 3 ↥X with hθ
  have hθs : Group.IsSolvable ↥θ :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
  refine eq_oPrimeResidualOf_of_hom hXp (QuotientGroup.mk' θ) ?_ ?_
  · rw [QuotientGroup.ker_mk']
    exact hθs
  · rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective θ)]
    exact oPrimeResidual_eq_top_of_mulEquiv Subgroup.topEquiv h

omit [Finite G] in
theorem le_of_isPerfect_of_le_sup {X Y S K : Subgroup G} (hXp : Group.IsPerfect ↥X)
    (hYX : Y ≤ X) (hXS : X ≤ Subgroup.normalizer (S : Set G)) (hS : Group.IsSolvable ↥S)
    (hSX : S ≤ X) (hXYS : X ≤ Y ⊔ S) (hYK : Y ≤ K)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) : X ≤ K := by
  set M : Subgroup ↥X := (K ⊓ X).subgroupOf X with hM
  have hMn : M.Normal := by
    rw [hM]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      (le_inf hXK Subgroup.le_normalizer |>.trans (Subgroup.inf_normalizer_le_normalizer_inf))
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp (Subgroup.inclusion hSX)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
    have hx : (x : G) ∈ ((Y : Set G) * (S : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y S (hYX.trans hXS)]
      exact hXYS x.2
    obtain ⟨y, hy, s, hs, hys⟩ := hx
    refine ⟨⟨s, hs⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
    have hyM : (⟨y, hYX hy⟩ : ↥X) ∈ M := by
      rw [hM, Subgroup.mem_subgroupOf]
      exact ⟨hYK hy, hYX hy⟩
    have hxe : x = ⟨y, hYX hy⟩ * Subgroup.inclusion hSX ⟨s, hs⟩ := Subtype.ext hys.symm
    rw [hxe, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hyM, one_mul]
  have hsolv : Group.IsSolvable (↥X ⧸ M) := Group.isSolvable_of_surjective hsurj
  have hperf : Group.IsPerfect (↥X ⧸ M) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)
  have hMtop : M = ⊤ := by
    by_contra hne
    have : Nontrivial (↥X ⧸ M) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isSolvable (↥X ⧸ M) hsolv
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥X) ∈ M := hMtop ▸ Subgroup.mem_top _
  rw [hM, Subgroup.mem_subgroupOf] at hmem
  exact hmem.1

omit [Finite G] in
theorem isPerfect_sSup {S : Set (Subgroup G)} (h : ∀ M ∈ S, Group.IsPerfect ↥M) :
    Group.IsPerfect ↥(sSup S) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm ?_ (sSup_le fun M hM => ?_)
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · calc M = ⁅M, M⁆ := ((Subgroup.isPerfect_iff).mp (h M hM)).symm
      _ ≤ ⁅sSup S, sSup S⁆ := Subgroup.commutator_mono (le_sSup hM) (le_sSup hM)

end Perfect

section Commutator

variable {G : Type*} [Group G]

theorem map_conj_eq_of_mem_normalizer' {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa [mul_assoc] using this

theorem mem_normalizer_of_map_conj_eq'' {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]

theorem le_normalizer_sup' {A H K : Subgroup G} (hH : A ≤ Subgroup.normalizer (H : Set G))
    (hK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := fun a ha =>
  mem_normalizer_of_map_conj_eq'' (by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer' (hH ha),
      map_conj_eq_of_mem_normalizer' (hK ha)])

theorem le_commutator_sup_of_le {Q A O K C : Subgroup G} (hQ : Q = ⁅Q, A⁆)
    (hQle : Q ≤ K ⊔ O ⊔ C) (hOK : O ≤ Subgroup.normalizer (K : Set G))
    (hCK : C ≤ Subgroup.normalizer (K : Set G)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hCO : C ≤ Subgroup.normalizer (O : Set G)) (hCA : C ≤ Subgroup.centralizer (A : Set G)) :
    Q ≤ ⁅O, A⁆ ⊔ K := by
  set N := ⁅O, A⁆ ⊔ K with hN
  have hKN : K ≤ Subgroup.normalizer (N : Set G) :=
    (le_sup_right : K ≤ N).trans Subgroup.le_normalizer
  have hON : O ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_sup' (Subgroup.normalizer_commutator_ge_left O A) hOK
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := by
    refine le_normalizer_sup' (fun c hc => ?_) hCK
    refine mem_normalizer_of_map_conj_eq'' ?_
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer' (hCO hc),
      map_conj_eq_of_mem_normalizer'
        (Subgroup.centralizer_le_normalizer (A : Set G) (hCA hc))]
  have hMN : K ⊔ O ⊔ C ≤ Subgroup.normalizer (N : Set G) := sup_le (sup_le hKN hON) hCN
  have hM : K ⊔ O ⊔ C = Subgroup.closure ((K : Set G) ∪ (O : Set G) ∪ (C : Set G)) := by
    rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
      Subgroup.closure_eq]
  have key : ∀ x ∈ K ⊔ O ⊔ C, ∀ α ∈ A, ⁅x, α⁆ ∈ N := by
    intro x hx
    rw [hM] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      intro α hα
      rcases hy with (hy | hy) | hy
      · refine Subgroup.mem_sup_right ?_
        have hyα : ⁅y, α⁆ = y * (α * y⁻¹ * α⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [hyα]
        exact mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hAK hα) _).mp (inv_mem hy))
      · exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hy hα)
      · have hc : y * α = α * y := (Subgroup.mem_centralizer_iff.mp (hCA hy) α hα).symm
        rw [commutatorElement_def, hc]
        simp
    | one =>
      intro α _
      simp
    | mul y z hy _ ihy ihz =>
      intro α hα
      have hyM : y ∈ K ⊔ O ⊔ C := hM ▸ hy
      have hyz : ⁅y * z, α⁆ = (y * ⁅z, α⁆ * y⁻¹) * ⁅y, α⁆ := by
        simp only [commutatorElement_def]
        group
      rw [hyz]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hMN hyM) _).mp (ihz α hα)) (ihy α hα)
    | inv y hy ihy =>
      intro α hα
      have hyM : y ∈ K ⊔ O ⊔ C := hM ▸ hy
      have hy' : ⁅y⁻¹, α⁆ = y⁻¹ * ⁅y, α⁆⁻¹ * y⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [hy']
      exact (Subgroup.mem_normalizer_iff.mp (inv_mem (hMN hyM)) _).mp (inv_mem (ihy α hα))
  rw [hQ]
  refine (Subgroup.commutator_mono hQle le_rfl).trans ?_
  rw [Subgroup.commutator_le]
  exact key

end Commutator

end CFSG.RankThree.PartTwo.Sec17.Proof171Steps
