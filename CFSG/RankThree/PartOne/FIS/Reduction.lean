module

public import CFSG.Fischer.Classification.Basic.Trichotomy
public import CFSG.Fischer.Classification.Basic.Covering
public import CFSG.RankThree.PartOne.FIS.Basic

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7
open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

theorem tt_of_pair {X : Type} [Group X] {E : Set X} (hP : Pair X E) : IsThreeTranspositions E := by
  have hle : ∀ x ∈ E, ∀ y ∈ E, orderOf (x * y) ≤ 3 := fun x hx y hy => by
    rcases Pair.orderOf_mul_mem hP hx hy with h | h | h <;> rw [h] <;> norm_num
  exact ⟨⟨fun g x hx => Pair.conj_mem hP hx g, fun x hx => Pair.orderOf_eq_two hP hx,
    Pair.closure_eq hP, fun x hx y hy => by have := hle x hx y hy; omega,
    fun x hx y hy h4 => by have := hle x hx y hy; omega⟩, hle⟩

theorem pair_of_tt {X : Type} [Group X] [Finite X] {E : Set X} (hD : IsThreeTranspositions E)
    (htr : ∀ d ∈ E, ∀ e ∈ E, ∃ g : X, g * d * g⁻¹ = e) {d₀ : X} (hd₀ : d₀ ∈ E) :
    Pair X E := by
  refine ⟨inferInstance, ⟨d₀, ?_⟩, hD.1.2.1, ?_, hD.1.2.2.1⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨g, hg⟩ := htr d₀ hd₀ x hx
      exact isConj_iff.2 ⟨g, hg⟩
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      rw [← hc]
      exact tt_conj_mem hD hd₀ c
  · intro e he f hf
    have hpos : 0 < orderOf (e * f) := orderOf_pos _
    have hle := hD.2 e he f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

theorem mk_eq_of_comm_of_normal {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N)
    (hNbot : N ≠ ⊥) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a * b = b * a) :
    a⁻¹ * b ∈ N := by
  have := hNn
  by_contra hne
  have hNZ : ¬ N ≤ Subgroup.center X := fun h => hNbot (by rw [← le_bot_iff, ← hZ]; exact h)
  refine hNZ (Pair.normal_le_center_of_commute hP hNn hNs ha hb hab fun n hn => ?_)
  by_contra hc
  apply hne
  have hb' := Pair.conj_mem hP hb n
  have h1 := Pair.mul_conj_left_eq hP ha hb' hc
  have hπ : (QuotientGroup.mk (n * b * n⁻¹) : X ⧸ N) = QuotientGroup.mk b := by
    rw [QuotientGroup.eq]
    have := mul_mem hn (hNn.conj_mem _ (inv_mem hn) b⁻¹)
    convert this using 1
    group
  generalize n * b * n⁻¹ = b' at h1 hπ
  have key : (QuotientGroup.mk b : X ⧸ N) = QuotientGroup.mk a := by
    rw [← hπ]
    conv_lhs => rw [← h1]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hπ]
    have hab' : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a := by
      rw [← QuotientGroup.mk_mul, hab, QuotientGroup.mk_mul]
    calc (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b * QuotientGroup.mk a *
          (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹
        = QuotientGroup.mk a * (QuotientGroup.mk b * QuotientGroup.mk a) *
          (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹ := by group
      _ = QuotientGroup.mk a := by rw [← hab']; group
  exact QuotientGroup.eq.1 key.symm

theorem exists_conj_of_mul_mem {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) {N : Subgroup X} (hNn : N.Normal) {d x : X} (hd : d ∈ E)
    (hx : x ∈ E) (hxd : x * d ∈ N) : ∃ n ∈ N, x = n * d * n⁻¹ := by
  have hT := tt_of_pair hP
  have := Pair.finite hP
  by_cases hxd' : x = d
  · exact ⟨1, one_mem _, by simp [hxd']⟩
  by_cases hc : x * d = d * x
  · obtain ⟨a, haE, hda, hxa⟩ : ∃ a ∈ E, a * d ≠ d * a ∧ a * x ≠ x * a := by
      by_contra hcon
      push Not at hcon
      have hcov := Pair.eq_top_or_eq_top_of_cover hP (Subgroup.centralizer {d})
        (Subgroup.centralizer {x}) (fun e he => by
          by_cases h : e * d = d * e
          · exact Or.inl (Subgroup.mem_centralizer_singleton_iff.2 h)
          · exact Or.inr (Subgroup.mem_centralizer_singleton_iff.2 (hcon e he h)))
      rcases hcov with h | h
      · have hdc : d ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 fun e he => by
          have : e ∈ Subgroup.centralizer ({d} : Set X) := by rw [h]; trivial
          exact Subgroup.mem_centralizer_singleton_iff.1 this
        rw [hZ, Subgroup.mem_bot] at hdc
        exact Pair.ne_one hP hd hdc
      · have hxc : x ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 fun e he => by
          have : e ∈ Subgroup.centralizer ({x} : Set X) := by rw [h]; trivial
          exact Subgroup.mem_centralizer_singleton_iff.1 this
        rw [hZ, Subgroup.mem_bot] at hxc
        exact Pair.ne_one hP hx hxc
    have hs := tt_sigma4_conj hT haE hd hx hc.symm (Ne.symm hda) (Ne.symm hxa)
    have hdx : d * x ∈ N := by rw [← hc]; exact hxd
    have hmem : a * d * x * a ∈ N := by
      have := Subgroup.Normal.conj_mem hNn _ hdx a
      rw [tt_inv_eq hT haE] at this
      simpa only [mul_assoc] using this
    exact ⟨a * d * x * a, hmem, hs.symm⟩
  · refine ⟨(x * d)⁻¹, inv_mem hxd, ?_⟩
    rw [inv_inv]
    exact (tt_conj_eq_of_noncomm hT hx hd hc).symm

theorem conjOrbit_subset {X : Type} [Group X] {E : Set X} (hP : Pair X E) {N : Subgroup X}
    {d : X} (hd : d ∈ E) : conjOrbit N d ⊆ E := by
  rintro _ ⟨n, _, rfl⟩
  exact Pair.conj_mem hP hd n

theorem normal_le_closure_conjOrbit {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N)
    (hNbot : N ≠ ⊥) {d : X} (hd : d ∈ E) : N ≤ Subgroup.closure (conjOrbit N d) := by
  have := hNn
  have hT := tt_of_pair hP
  set C : Subgroup X := Subgroup.closure {g | ∃ n ∈ N, g = n * d * n⁻¹ * d⁻¹} with hC
  have hCN : C ≤ N := by
    rw [hC, Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    have : n * d * n⁻¹ * d⁻¹ = n * (d * n⁻¹ * d⁻¹) := by group
    rw [this]
    exact mul_mem hn (Subgroup.Normal.conj_mem hNn _ (inv_mem hn) d)
  have hCE : C ≤ Subgroup.closure (conjOrbit N d) := by
    rw [hC, Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    have hdi : d⁻¹ = d := tt_inv_eq hT hd
    rw [hdi]
    exact mul_mem (Subgroup.subset_closure ⟨n, hn, rfl⟩)
      (Subgroup.subset_closure ⟨1, one_mem _, by simp⟩)
  have key : ∀ x ∈ C, ∀ m : X, m ∈ N → m * x * m⁻¹ ∈ C := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨n, hn, rfl⟩ := hg
      intro m hm
      have h1 : (m * n) * d * (m * n)⁻¹ * d⁻¹ ∈ C :=
        Subgroup.subset_closure ⟨m * n, mul_mem hm hn, rfl⟩
      have h2 : m * d * m⁻¹ * d⁻¹ ∈ C := Subgroup.subset_closure ⟨m, hm, rfl⟩
      have := mul_mem h1 (inv_mem h2)
      convert this using 1
      group
    | one => intro m _; simp
    | mul x y _ _ hx hy =>
      intro m hm
      rw [show m * (x * y) * m⁻¹ = m * x * m⁻¹ * (m * y * m⁻¹) by group]
      exact mul_mem (hx m hm) (hy m hm)
    | inv x _ hx =>
      intro m hm
      rw [show m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ by group]
      exact inv_mem (hx m hm)
  have hCnorm : (C.subgroupOf N).Normal := ⟨fun c hc m => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    exact key _ hc m m.2⟩
  rcases hNs.eq_bot_or_eq_top_of_normal (C.subgroupOf N) with hbot | htop
  · exfalso
    have hdN : ∀ n ∈ N, n * d = d * n := by
      intro n hn
      have hmem : n * d * n⁻¹ * d⁻¹ ∈ C := Subgroup.subset_closure ⟨n, hn, rfl⟩
      have h1 : (⟨n * d * n⁻¹ * d⁻¹, hCN hmem⟩ : N) ∈ C.subgroupOf N :=
        Subgroup.mem_subgroupOf.2 hmem
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : n * d * n⁻¹ * d⁻¹ = 1 := congrArg Subtype.val h1
      calc n * d = n * d * n⁻¹ * d⁻¹ * (d * n) := by group
        _ = d * n := by rw [h2, one_mul]
    apply hNbot
    rw [eq_bot_iff, ← hZ]
    intro n hn
    refine (Pair.mem_center_iff hP).2 fun e he => ?_
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hd he)
    have hn' : g⁻¹ * n * g ∈ N := by simpa using Subgroup.Normal.conj_mem hNn n hn g⁻¹
    have h := hdN _ hn'
    calc g * d * g⁻¹ * n = g * (d * (g⁻¹ * n * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * n * g) * d) * g⁻¹ := by rw [h]
      _ = n * (g * d * g⁻¹) := by group
  · intro n hn
    have : (⟨n, hn⟩ : N) ∈ C.subgroupOf N := htop ▸ Subgroup.mem_top _
    exact hCE (Subgroup.mem_subgroupOf.1 this)

theorem closure_conjOrbit_eq {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N)
    (hNbot : N ≠ ⊥) {d : X} (hd : d ∈ E) :
    Subgroup.closure (conjOrbit N d) = N ⊔ Subgroup.zpowers d := by
  refine le_antisymm ?_ (sup_le (normal_le_closure_conjOrbit hP hZ hNn hNs hNbot hd) ?_)
  · rw [Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    have h : n * d * n⁻¹ = (n * (d * n⁻¹ * d⁻¹)) * d := by group
    rw [h]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem hn
      (Subgroup.Normal.conj_mem hNn _ (inv_mem hn) d)))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure ⟨1, one_mem _, by simp⟩

theorem centralizer_eq_bot_of_minimal {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) {N : Subgroup X}
    (hNn : N.Normal) (hNbot : N ≠ ⊥) (hmin : ∀ K : Subgroup X, K.Normal → K ≤ N → K ≠ ⊥ → K = N) :
    Subgroup.centralizer (N : Set X) = ⊥ := by
  have := Pair.finite hP
  have hNs := Pair.isSimpleGroup_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have hNsol := Pair.not_isSolvable_of_minimal hP hZ h2 h3 hNn hNbot hmin
  by_contra hCbot
  have hCn : (Subgroup.centralizer (N : Set X)).Normal := ⟨fun c hc g => by
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro n hn
    have hn' : g⁻¹ * n * g ∈ N := by simpa using Subgroup.Normal.conj_mem hNn n hn g⁻¹
    have := (conj_comm_iff g (g⁻¹ * n * g) c).2 (hc _ hn')
    rw [show g * (g⁻¹ * n * g) * g⁻¹ = n by group] at this
    exact this⟩
  obtain ⟨M, hMn, hMC, hMbot, hMmin⟩ := CFSG.exists_minimal_normal_le _ hCn hCbot
  have hMs := Pair.isSimpleGroup_of_minimal hP hZ h2 h3 hMn hMbot hMmin
  have hcenter : Subgroup.center N = ⊥ := by
    rcases hNs.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
    · exact h
    · exfalso
      apply hNsol
      refine Group.isSolvable_of_comm fun a b => ?_
      have : b ∈ Subgroup.center N := by rw [h]; trivial
      exact Subgroup.mem_center_iff.1 this a
  have hinf : N ⊓ M = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyN, hyM⟩
    have hyC := Subgroup.mem_centralizer_iff.1 (hMC hyM)
    have : (⟨y, hyN⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hyC g g.2)
    rw [hcenter, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨a, ha, b, hb, hab, habc⟩ := Pair.exists_ne_commute_of_three hP hZ h3
  have h1 := mk_eq_of_comm_of_normal hP hZ hNn hNs hNbot ha hb habc
  have h2' := mk_eq_of_comm_of_normal hP hZ hMn hMs hMbot ha hb habc
  have hmem : a⁻¹ * b ∈ N ⊓ M := ⟨h1, h2'⟩
  rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hab hmem

@[expose] def Kgrp {X : Type} [Group X] (N : Subgroup X) (d : X) : Subgroup X :=
  Subgroup.closure (conjOrbit N d)

theorem mem_Kgrp_self {X : Type} [Group X] (N : Subgroup X) (d : X) : d ∈ Kgrp N d :=
  Subgroup.subset_closure ⟨1, one_mem _, by simp⟩

theorem conjOrbit_subset_Kgrp {X : Type} [Group X] (N : Subgroup X) (d : X) :
    conjOrbit N d ⊆ Kgrp N d := Subgroup.subset_closure

theorem pair_Kgrp {X : Type} [Group X] {E : Set X} (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N) (hNbot : N ≠ ⊥) {d : X}
    (hd : d ∈ E) : Pair ↥(Kgrp N d) (Subtype.val ⁻¹' conjOrbit N d) := by
  have := Pair.finite hP
  have hdK : d ∈ Kgrp N d := mem_Kgrp_self N d
  have hNK : N ≤ Kgrp N d := normal_le_closure_conjOrbit hP hZ hNn hNs hNbot hd
  have hKeq : Kgrp N d = N ⊔ Subgroup.zpowers d := closure_conjOrbit_eq hP hZ hNn hNs hNbot hd
  refine ⟨inferInstance, ⟨⟨d, hdK⟩, ?_⟩, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨n, hn, hx⟩
      refine isConj_iff.2 ⟨⟨n, hNK hn⟩, Subtype.ext ?_⟩
      simpa using hx.symm
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      have hcx : (x : X) = c.1 * d * c.1⁻¹ := by rw [← hc]; rfl
      have hcmem : c.1 ∈ N ⊔ Subgroup.zpowers d := hKeq ▸ c.2
      have := hNn
      obtain ⟨n, hn, z, hz, hnz⟩ := Subgroup.mem_sup_of_normal_left.1 hcmem
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      refine ⟨n, hn, ?_⟩
      rw [hcx, ← hnz]
      group
  · intro e he
    rw [← Subgroup.orderOf_coe]
    exact Pair.orderOf_eq_two hP (conjOrbit_subset hP hd he)
  · intro e he f hf
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact Pair.orderOf_mul_mem hP (conjOrbit_subset hP hd he) (conjOrbit_subset hP hd hf)
  · exact Subgroup.closure_closure_coe_preimage

theorem center_Kgrp {X : Type} [Group X] {E : Set X} (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N) (hNbot : N ≠ ⊥) {d : X}
    (hd : d ∈ E) (hcent : Subgroup.centralizer (N : Set X) = ⊥) :
    Subgroup.center ↥(Kgrp N d) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hNK : N ≤ Kgrp N d := normal_le_closure_conjOrbit hP hZ hNn hNs hNbot hd
  have hzC : (z : X) ∈ Subgroup.centralizer (N : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz) ⟨n, hNK hn⟩)
  rw [hcent, Subgroup.mem_bot] at hzC
  exact Subgroup.mem_bot.2 (Subtype.ext hzC)

open scoped commutatorElement in
theorem commutator_eq_top_of_simple {N : Type} [Group N] (hNs : IsSimpleGroup N)
    (hNsol : ¬ Group.IsSolvable N) : commutator N = ⊤ := by
  rcases hNs.eq_bot_or_eq_top_of_normal (commutator N) with h | h
  · exfalso
    apply hNsol
    refine Group.isSolvable_of_comm fun a b => ?_
    have hc : ⁅a, b⁆ ∈ commutator N := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

open scoped commutatorElement in
theorem commutator_Kgrp {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N)
    (hNsol : ¬ Group.IsSolvable N) (hNbot : N ≠ ⊥) {d : X} (hd : d ∈ E) :
    ⁅Kgrp N d, Kgrp N d⁆ = N := by
  have := hNn
  have hNK : N ≤ Kgrp N d := normal_le_closure_conjOrbit hP hZ hNn hNs hNbot hd
  have hKeq : Kgrp N d = N ⊔ Subgroup.zpowers d := closure_conjOrbit_eq hP hZ hNn hNs hNbot hd
  have hperf : ⁅N, N⁆ = N := by
    rw [← Subgroup.map_subtype_commutator, commutator_eq_top_of_simple hNs hNsol,
      Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm ?_ (calc N = ⁅N, N⁆ := hperf.symm
    _ ≤ ⁅Kgrp N d, Kgrp N d⁆ := Subgroup.commutator_mono hNK hNK)
  rw [Subgroup.commutator_le]
  intro g1 h1 g2 h2
  have hq : ∀ g ∈ Kgrp N d, ∃ k : ℤ,
      (QuotientGroup.mk g : X ⧸ N) = (QuotientGroup.mk d : X ⧸ N) ^ k := by
    intro g hg
    rw [hKeq] at hg
    obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ⟨k, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul, QuotientGroup.mk_zpow]
  obtain ⟨k1, hk1⟩ := hq g1 h1
  obtain ⟨k2, hk2⟩ := hq g2 h2
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hk1, hk2,
    commutatorElement_eq_one_iff_mul_comm]
  exact (Commute.zpow_zpow_self _ k1 k2).eq

theorem isSimpleGroup_commutator_Kgrp {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) {N : Subgroup X} (hNn : N.Normal) (hNs : IsSimpleGroup N)
    (hNsol : ¬ Group.IsSolvable N) (hNbot : N ≠ ⊥) {d : X} (hd : d ∈ E) :
    IsSimpleGroup ↥(commutator ↥(Kgrp N d)) ∧
      ∃ a b : commutator ↥(Kgrp N d), a * b ≠ b * a := by
  have hKN := commutator_Kgrp hP hZ hNn hNs hNsol hNbot hd
  have hmap : (commutator ↥(Kgrp N d)).map (Kgrp N d).subtype = N :=
    (Subgroup.map_subtype_commutator _).trans hKN
  let e : ↥(commutator ↥(Kgrp N d)) ≃* ↥N :=
    (Subgroup.equivMapOfInjective _ (Kgrp N d).subtype (Kgrp N d).subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  refine ⟨e.isSimpleGroup, ?_⟩
  by_contra hcomm
  push Not at hcomm
  apply hNsol
  refine Group.isSolvable_of_comm fun x y => ?_
  have := hcomm (e.symm x) (e.symm y)
  have h2 := congrArg e this
  simpa using h2

end CFSG.RankThree.PartOne.FIS
