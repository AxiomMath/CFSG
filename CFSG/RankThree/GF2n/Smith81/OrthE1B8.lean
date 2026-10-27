module

public import CFSG.RankThree.GF2n.Smith81.OrthE1B8Core
public import CFSG.RankThree.GF2n.Smith81.OrthE1KFacts2
public import CFSG.RankThree.GF2n.Smith81.OrthE1B2
public import CFSG.Walter.Statement

public section

open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

namespace B8

section Transport

variable {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
  [(Q.subgroupOf M).Normal]

omit [Finite G] in
theorem comm_bar {S T : Subgroup G} (hSM : S ≤ M) (hTM : T ≤ M)
    (h : ∀ a ∈ S, ∀ b ∈ T, ⁅a, b⁆ ∈ Q) :
    ∀ x ∈ bar M Q S, ∀ y ∈ bar M Q T, x * y = y * x := by
  intro x hx y hy
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
  rw [← map_mul, ← map_mul]
  apply QuotientGroup.eq.mpr
  have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have ht' : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
  have h1 : ⁅(s : G)⁻¹, (t : G)⁻¹⁆ ∈ Q := h _ (S.inv_mem hs') _ (T.inv_mem ht')
  have e : (((s * t)⁻¹ * (t * s) : M) : G) = ⁅(t : G)⁻¹, (s : G)⁻¹⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  show (((s * t)⁻¹ * (t * s) : M) : G) ∈ Q
  rw [e, ← commutatorElement_inv]
  exact Q.inv_mem h1

omit [Finite G] in
theorem bar_sup {S T : Subgroup G} (hS : S ≤ M) (hT : T ≤ M) :
    bar M Q (S ⊔ T) = bar M Q S ⊔ bar M Q T := by
  unfold bar
  rw [Subgroup.subgroupOf_sup hS hT, Subgroup.map_sup]

omit [Finite G] in
theorem isPerfect_quot (hQM : Q ≤ M) (h : ⁅M, M⁆ ⊔ Q = M) :
    Group.IsPerfect (↥M ⧸ Q.subgroupOf M) := by
  have hmapTop : Subgroup.map M.subtype (⊤ : Subgroup ↥M) = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hperfL : ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ ⊔ Q.subgroupOf M = ⊤ := by
    apply Subgroup.map_injective (f := M.subtype) (Subgroup.subtype_injective M)
    rw [Subgroup.map_sup, Subgroup.map_commutator, hmapTop, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hQM]
    exact h
  let p : ↥M →* ↥M ⧸ Q.subgroupOf M := QuotientGroup.mk' (Q.subgroupOf M)
  have hsurj : Function.Surjective p := QuotientGroup.mk'_surjective _
  refine ⟨?_⟩
  have htop : Subgroup.map p (⊤ : Subgroup ↥M) = ⊤ := Subgroup.map_top_of_surjective p hsurj
  have hcomm : Subgroup.map p ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ =
      ⁅(⊤ : Subgroup (↥M ⧸ Q.subgroupOf M)), (⊤ : Subgroup (↥M ⧸ Q.subgroupOf M))⁆ := by
    rw [Subgroup.map_commutator, htop]
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨l, rfl⟩ := hsurj x
  have hl : l ∈ ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ ⊔ Q.subgroupOf M := by
    rw [hperfL]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hl
  have hq1 : p q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
  have hmem : p a ∈ Subgroup.map p ⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆ :=
    Subgroup.mem_map_of_mem p ha
  rw [hcomm] at hmem
  rw [map_mul, hq1, mul_one]
  exact hmem

theorem bar_simple_nonab {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) {q n : ℕ}
    (hS : QuotSat S Q (IsSLModel 2 q)) (hq : q = 2 ^ n) (h4 : 4 ≤ q) :
    IsSimpleGroup ↥(bar M Q S) ∧ ∃ x ∈ bar M Q S, ∃ y ∈ bar M Q S, x * y ≠ y * x := by
  obtain ⟨hN, hX⟩ := hS
  haveI := hN
  obtain ⟨hcard, hsimp, hcen⟩ := b2_sl_facts hX hq h4
  obtain ⟨hN', ⟨e⟩⟩ := quotMulEquivBar (M := M) hQS hSM
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mp hsimp, ?_⟩
  by_contra hcon
  push Not at hcon
  have hall : ∀ x : ↥S ⧸ Q.subgroupOf S, x = 1 := by
    intro x
    refine hcen x fun y => ?_
    apply e.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (hcon _ (e x).2 _ (e y).2)
  have h1 : Nat.card (↥S ⧸ Q.subgroupOf S) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
  rw [hcard] at h1
  have : 4 * 15 ≤ q * (q ^ 2 - 1) := by
    have : 16 ≤ q ^ 2 := by nlinarith
    have h' : 15 ≤ q ^ 2 - 1 := by omega
    exact Nat.mul_le_mul h4 h'
  omega


omit [Finite G] in
theorem mk_mem_normalizer_bar {S : Subgroup G} (hQS : Q ≤ S) {n : ↥M}
    (hn : (n : G) ∈ Subgroup.normalizer (S : Set G)) :
    QuotientGroup.mk' (Q.subgroupOf M) n ∈
      Subgroup.normalizer (bar M Q S : Set (Mbar M Q)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) y
  rw [← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQS, mk_mem_bar_iff_sec4 hQS]
  have := (Subgroup.mem_normalizer_iff.mp hn) (y' : G)
  simpa using this

omit [Finite G] in
theorem mem_normalizer_of_mk_mem {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) (n : ↥M)
    (hn : QuotientGroup.mk' (Q.subgroupOf M) n ∈
      Subgroup.normalizer (bar M Q S : Set (Mbar M Q))) :
    (n : G) ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  by_cases hz : z ∈ M
  · have := (Subgroup.mem_normalizer_iff.mp hn) (QuotientGroup.mk' (Q.subgroupOf M) ⟨z, hz⟩)
    rw [← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQS, mk_mem_bar_iff_sec4 hQS]
      at this
    simpa using this
  · have hz' : z ∉ S := fun h => hz (hSM h)
    have hz'' : (n : G) * z * (n : G)⁻¹ ∉ S := fun h => by
      apply hz
      have h1 : (n : G)⁻¹ * ((n : G) * z * (n : G)⁻¹) * (n : G) ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem n.2) (hSM h)) n.2
      have e : (n : G)⁻¹ * ((n : G) * z * (n : G)⁻¹) * (n : G) = z := by group
      rwa [e] at h1
    exact iff_of_false hz' hz''

theorem fitting_bar (hF : M1FittingTrivialStatement) {M Q Z B : Subgroup G} {t : G}
    (hH : E1Hyp M Q Z B t) [(Q.subgroupOf (Lgen M (LB M Q B))).Normal]
    (A : Subgroup (Mbar (Lgen M (LB M Q B)) Q)) (hAn : A.Normal)
    (hAnil : Group.IsNilpotent ↥A) : A = ⊥ := by
  set L : Subgroup G := Lgen M (LB M Q B) with hL
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hQL : Q ≤ L := hQLB.trans (le_Lgen _)
  let p : ↥L →* Mbar L Q := QuotientGroup.mk' (Q.subgroupOf L)
  have hpsurj : Function.Surjective p := QuotientGroup.mk'_surjective _
  let A' : Subgroup G := (A.comap p).map L.subtype
  have hmemA' : ∀ x : G, x ∈ A' ↔ ∃ h : x ∈ L, p ⟨x, h⟩ ∈ A := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  have hQA' : Q ≤ A' := fun x hx => (hmemA' x).mpr ⟨hQL hx, by
    have h1 : p ⟨x, hQL hx⟩ = 1 :=
      (QuotientGroup.eq_one_iff (N := Q.subgroupOf L) _).mpr (Subgroup.mem_subgroupOf.mpr hx)
    rw [h1]
    exact A.one_mem⟩
  have hA'L : A' ≤ L := Subgroup.map_subtype_le _
  have hconj : ∀ s ∈ L, ∀ x ∈ A', s * x * s⁻¹ ∈ A' := by
    intro s hs x hx
    obtain ⟨hxL, hpx⟩ := (hmemA' x).mp hx
    refine (hmemA' _).mpr ⟨L.mul_mem (L.mul_mem hs hxL) (L.inv_mem hs), ?_⟩
    have e : p ⟨s * x * s⁻¹, L.mul_mem (L.mul_mem hs hxL) (L.inv_mem hs)⟩ =
        p ⟨s, hs⟩ * p ⟨x, hxL⟩ * (p ⟨s, hs⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact hAn.conj_mem _ hpx _
  have hnorm : ∀ s ∈ L, conjSubgroup s A' = A' := fun s hs => by
    refine conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_iff.mpr fun x => ?_)
    refine ⟨hconj s hs x, fun h => ?_⟩
    have := hconj s⁻¹ (L.inv_mem hs) _ h
    have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
    rwa [e] at this
  have hbar : bar L Q A' = A := by
    ext z
    obtain ⟨y, rfl⟩ := hpsurj z
    rw [mk_mem_bar_iff_sec4 hQA']
    constructor
    · intro hy
      obtain ⟨h, hpy⟩ := (hmemA' _).mp hy
      exact hpy
    · intro hy
      exact (hmemA' _).mpr ⟨y.2, hy⟩
  have hnil : QuotSat A' Q (fun W _ => Group.IsNilpotent W) := by
    obtain ⟨hN, ⟨e⟩⟩ := quotMulEquivBar (M := L) hQA' hA'L
    refine ⟨hN, ?_⟩
    haveI := hAnil
    exact Group.nilpotent_of_mulEquiv (e.trans (MulEquiv.subgroupCongr hbar)).symm
  have hA'Q := hF G M Q Z B t hH A' hQA' hA'L hnorm hnil
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨y, rfl⟩ := hpsurj a
  have hyA' : (y : G) ∈ A' := (hmemA' _).mpr ⟨y.2, ha⟩
  rw [hA'Q] at hyA'
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hyA')

omit [Finite G] in
theorem bar_mono_le {S T : Subgroup G} (h : S ≤ T) : bar M Q S ≤ bar M Q T :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

end Transport

end B8

section Main


theorem b8_of (hW : CFSG.Walter.WalterModelsForm) (hWL : KFacts.WalterListLargeSylowStatement)
    (hF : M1FittingTrivialStatement) (hSplit : RtSplitStatement) (hB6 : B6Statement)
    (hB7a : B7aStatement) : B8Statement := by
  intro G _ _ M Q Z B t hH D hS
  have hc : Ctx M Q Z B := hH.ctx
  set Lb : Subgroup G := LB M Q B with hLb
  set Lg : Subgroup G := Lgen M Lb with hLg
  have hQLb : Q ≤ Lb := le_sup_left
  have hLbLg : Lb ≤ Lg := le_Lgen Lb
  have hLbM : Lb ≤ M := hc.LB_le_M
  have hLgM : Lg ≤ M := Lgen_le hLbM
  have hQLg : Q ≤ Lg := hQLb.trans hLbLg
  have hQnorm : Lg ≤ Subgroup.normalizer (Q : Set G) :=
    fun s hs => hc.hyp.Q_normal.2 (hLgM hs)
  haveI hQN : (Q.subgroupOf Lg).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQLg).mpr hQnorm
  obtain ⟨hLE, hE0Lg, hNormE, -⟩ := hB6 G M Q Z B t hH D
  have hperf : ⁅Lg, Lg⁆ ⊔ Q = Lg := hB7a G M Q Z B t hH ⟨D⟩
  obtain ⟨hQFb, hQFc, -, -, -, -, hcbc, hSb, hSc⟩ := D.two
  obtain ⟨hQY, -, -, -, -, -, hcYFc, hSY, -⟩ := D.two'
  have hcYFb : ∀ a ∈ D.Y, ∀ b ∈ D.Fb, ⁅a, b⁆ ∈ Q := D.YFb.2
  have hYLg : D.Y ≤ Lg := (le_sup_left.trans le_sup_left).trans hE0Lg
  have hFbLg : D.Fb ≤ Lg := (le_sup_right.trans le_sup_left).trans hE0Lg
  have hFcLg : D.Fc ≤ Lg := le_sup_right.trans hE0Lg
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨n2, -, hn2, -⟩ := hc.hyp.cp
  let F : Fin 3 → Subgroup (Mbar Lg Q) := ![bar Lg Q D.Y, bar Lg Q D.Fb, bar Lg Q D.Fc]
  have hfac := fun {S : Subgroup G} (hQS : Q ≤ S) (hSL : S ≤ Lg)
      (hS' : QuotSat S Q (IsSLModel 2 (Nat.card Z))) =>
    B8.bar_simple_nonab (M := Lg) hQS hSL hS' hn2 hq4
  have hs : ∀ i, IsSimpleGroup ↥(F i) := by
    intro i
    fin_cases i
    · exact (hfac hQY hYLg hSY).1
    · exact (hfac hQFb hFbLg hSb).1
    · exact (hfac hQFc hFcLg hSc).1
  have hn : ∀ i, ∃ x ∈ F i, ∃ y ∈ F i, x * y ≠ y * x := by
    intro i
    fin_cases i
    · exact (hfac hQY hYLg hSY).2
    · exact (hfac hQFb hFbLg hSb).2
    · exact (hfac hQFc hFcLg hSc).2
  have hcF : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, x * y = y * x := by
    intro i j hij x hx y hy
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact B8.comm_bar hYLg hFbLg hcYFb x hx y hy
    · exact B8.comm_bar hYLg hFcLg hcYFc x hx y hy
    · exact (B8.comm_bar hYLg hFbLg hcYFb y hy x hx).symm
    · exact absurd rfl hij
    · exact B8.comm_bar hFbLg hFcLg hcbc x hx y hy
    · exact (B8.comm_bar hYLg hFcLg hcYFc y hy x hx).symm
    · exact (B8.comm_bar hFbLg hFcLg hcbc y hy x hx).symm
    · exact absurd rfl hij
  have hsupF : F 0 ⊔ F 1 ⊔ F 2 = bar Lg Q (D.Y ⊔ D.Fb ⊔ D.Fc) := by
    show bar Lg Q D.Y ⊔ bar Lg Q D.Fb ⊔ bar Lg Q D.Fc = _
    rw [B8.bar_sup (sup_le hYLg hFbLg) hFcLg, B8.bar_sup hYLg hFbLg]
  have hLE' : bar Lg Q Lb ≤ F 0 ⊔ F 1 ⊔ F 2 := by
    rw [hsupF]
    exact B8.bar_mono_le hLE
  have hQE0 : Q ≤ D.Y ⊔ D.Fb ⊔ D.Fc := hQY.trans (le_sup_left.trans le_sup_left)
  have hNorm : ∀ n ∈ Subgroup.normalizer (bar Lg Q Lb : Set (Mbar Lg Q)),
      ∀ x ∈ F 0 ⊔ F 1 ⊔ F 2, n * x * n⁻¹ ∈ F 0 ⊔ F 1 ⊔ F 2 := by
    intro n hn x hx
    rw [hsupF] at hx ⊢
    obtain ⟨n', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf Lg) n
    obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf Lg) x
    have hn' := B8.mem_normalizer_of_mk_mem hQLb hLbLg n' hn
    have hconj := hNormE n' n'.2 hn'
    rw [← map_inv, ← map_mul, ← map_mul, mk_mem_bar_iff_sec4 hQE0]
    rw [mk_mem_bar_iff_sec4 hQE0] at hx
    have : (n' : G) * x' * (n' : G)⁻¹ ∈ conjSubgroup (n' : G) (D.Y ⊔ D.Fb ⊔ D.Fc) := by
      rw [mem_conjSubgroup]
      have e : (n' : G)⁻¹ * ((n' : G) * x' * (n' : G)⁻¹) * (n' : G) = x' := by group
      rw [e]
      exact hx
    rw [hconj] at this
    simpa using this
  obtain ⟨hgLg, hgN, hgNLb, hgne⟩ := D.hg
  have hS2 : ¬ 2 ∣ Lb.relIndex Lg := hS.2.2.2
  have hLi : ¬ 2 ∣ (bar Lg Q Lb).index := fun h =>
    hS2 (h.trans (Subgroup.index_map_dvd (f := QuotientGroup.mk' (Q.subgroupOf Lg))
      (Lb.subgroupOf Lg) (QuotientGroup.mk'_surjective _)))
  obtain ⟨hNLb, hNQ, -, -, -, -, hcard7, -, -⟩ := hSplit G M Q Z B t hH
  have hQN' : Q ≤ Nt M Lb t := by
    rw [← hNQ]
    exact inf_le_left
  have hL16 : 16 ≤ Nat.card ↥(bar Lg Q Lb) := by
    have h1 := bar_card_mul_card_of_le (M := Lg) hQLb hLbLg
    have h2 : Nat.card ↥(Lb ⊓ E1Xpre M Q B t) ≤ Nat.card ↥Lb :=
      Subgroup.card_le_of_le inf_le_left
    have h3 : 16 ≤ Nat.card Z ^ 2 := by nlinarith
    rw [hcard7, ← h1] at h2
    have h4 : Nat.card Q * 16 ≤ Nat.card Q * Nat.card ↥(bar Lg Q Lb) := by
      calc Nat.card Q * 16 ≤ Nat.card Q * Nat.card Z ^ 2 := Nat.mul_le_mul_left _ h3
        _ ≤ Nat.card ↥(bar Lg Q Lb) * Nat.card Q := h2
        _ = Nat.card Q * Nat.card ↥(bar Lg Q Lb) := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h4 Nat.card_pos
  have hLab : ∀ x ∈ bar Lg Q Lb, ∀ y ∈ bar Lg Q Lb, x * y = y * x :=
    B8.comm_bar hLbLg hLbLg fun a ha b hb =>
      hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator ha hb)
  have hLsq : ∀ x ∈ bar Lg Q Lb, x * x = 1 := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul]
    refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have := hc.sq_mem_Q_of_mem_LB (Subgroup.mem_subgroupOf.mp hs)
    simpa [pow_two] using this
  have hgQ : D.g ∈ Subgroup.normalizer (Q : Set G) := hQnorm hgLg
  have hex : ∃ n ∈ Nt M Lb t, D.g * n * D.g⁻¹ ∉ Q := by
    by_contra hcon
    push Not at hcon
    apply hgne
    have hle : conjSubgroup D.g (Nt M Lb t) ≤ Nt M Lb t := by
      intro x hx
      rw [mem_conjSubgroup] at hx
      have := hcon _ hx
      have e : D.g * (D.g⁻¹ * x * D.g) * D.g⁻¹ = x := by group
      rw [e] at this
      exact hQN' this
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  obtain ⟨n, hnN, hngQ⟩ := hex
  have hnQ : n ∉ Q := fun h => hngQ ((Subgroup.mem_normalizer_iff.mp hgQ n).mp h)
  have hnY : n ∈ D.Y := D.N_le_Y hnN
  have hnLb : n ∈ Lb := hNLb hnN
  have hnLg : n ∈ Lg := hLbLg hnLb
  have hgnFb : D.g * n * D.g⁻¹ ∈ D.Fb := by
    refine D.N'_le_Fb ?_
    rw [mem_conjSubgroup]
    have e : D.g⁻¹ * (D.g * n * D.g⁻¹) * D.g = n := by group
    rw [e]
    exact hnN
  have hWalter : ∀ (D : Type) [Group D] [Finite D] [IsSimpleGroup D],
      (∃ a b : D, a * b ≠ b * a) → ∀ P : Sylow 2 D, IsMulCommutative ↥P → 16 ≤ Nat.card ↥P →
        ∀ i : D, i * i = 1 → i ≠ 1 →
          IsPGroup 2 ↥(Subgroup.centralizer ({i} : Set D)) :=
    fun D _ _ _ hnab P hPc h16 i hi hi1 => hWL D (hW D hnab P hPc) P h16 i hi hi1
  refine B8.core hWalter (B8.isPerfect_quot hQLg hperf)
    (fun A hA hnil => B8.fitting_bar hF hH A hA hnil) (bar Lg Q Lb) hLi hL16 hLab hLsq F hs hn
    hcF hLE' hNorm (QuotientGroup.mk' (Q.subgroupOf Lg) ⟨D.g, hgLg⟩)
    (QuotientGroup.mk' (Q.subgroupOf Lg) ⟨n, hnLg⟩) ?_ ?_ ?_ ?_ ?_
  · exact B8.mk_mem_normalizer_bar hQLb (n := ⟨D.g, hgLg⟩) hgN
  · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hnLb)
  · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hnY)
  · intro h
    exact hnQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  · rw [← map_inv, ← map_mul, ← map_mul]
    exact (mk_mem_bar_iff_sec4 hQFb _).mpr hgnFb

end Main

end CFSG.RankThree.GF2n.Smith81.Smith23E1
