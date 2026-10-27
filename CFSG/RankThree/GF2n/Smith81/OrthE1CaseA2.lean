module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
public import CFSG.RankThree.GF2n.Smith81.ERecursion
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCorBList
public import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

theorem listGroup_isSimpleGroup {X : Type} [Group X]
    (h : ListGroup X) : IsSimpleGroup X := by
  rcases h with h | h | h | h | h | h | h
  · obtain ⟨m, s, hm, hs, hcl⟩ := h
    obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hcl
    dsimp only [StatedLieAdmissible] at hadm
    obtain ⟨-, -, -, h22, h23⟩ := hadm
    haveI : IsSimpleGroup (StatedProj (StatedSL m K)) := by
      refine CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K hm ?_ ?_
      · by_cases hm2 : m = 2
        · right
          intro hc
          apply h22
          have h1 : 2 ^ s = 2 := hK.symm.trans hc
          rw [hm2, h1]
        · left
          exact hm2
      · by_cases hm2 : m = 2
        · right
          intro hc
          have h2 : 2 ∣ Nat.card K := hK ▸ dvd_pow_self 2 (by omega)
          rw [hc] at h2
          omega
        · left
          exact hm2
    exact e.isSimpleGroup
  · obtain ⟨s, hs, hcl⟩ := h
    exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 2 s hcl).2
  · obtain ⟨s, hs, hs3, hl⟩ := h
    obtain ⟨-, a, ha, K, _, _, hs', hK, ⟨φ⟩⟩ := lieModel_twistedB2_iff.1 hl
    haveI := (CFSG.LieType.Ree.suzuki_simple (a := a) (K := K) ha (hK.trans (by rw [hs']))).2.2
    exact φ.isSimpleGroup
  · obtain ⟨k, hk6, hk9, ⟨φ⟩⟩ := h
    have hk : Nat.card (Fin k) = k := by simp
    haveI : IsSimpleGroup (alternatingGroup (Fin k)) :=
      alternatingGroup.isSimpleGroup (by rw [hk]; omega)
    exact φ.isSimpleGroup
  · obtain ⟨φ⟩ := h
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact φ.isSimpleGroup
  · obtain ⟨φ⟩ := h
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M23) :=
      CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    exact φ.isSimpleGroup
  · obtain ⟨φ⟩ := h
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
      CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    exact φ.isSimpleGroup

section Bar

variable {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem caseA2_mem_bar {S : Subgroup G} (hQS : Q ≤ S) (y : M) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q S ↔ (y : G) ∈ S := by
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
    have h1 : s⁻¹ * y ∈ Q.subgroupOf M := QuotientGroup.eq.mp hsy
    have h2 : (s : G)⁻¹ * y ∈ S := hQS h1
    have e : (y : G) = s * ((s : G)⁻¹ * y) := by group
    rw [e]
    exact S.mul_mem (Subgroup.mem_subgroupOf.mp hs) h2
  · intro hy
    exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem caseA2_mem_conj_bar {S : Subgroup G} (hQS : Q ≤ S) (m y : M) :
    QuotientGroup.mk' (Q.subgroupOf M) y ∈
        conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q S) ↔
      (y : G) ∈ conjSubgroup (m : G) S := by
  rw [mem_conjSubgroup, mem_conjSubgroup, ← map_inv, ← map_mul, ← map_mul,
    caseA2_mem_bar hQS]
  rfl

theorem caseA2_Q_le_conj {S : Subgroup G} (hQM : Q ≤ M) (hQS : Q ≤ S) (m : M) :
    Q ≤ conjSubgroup (m : G) S := by
  intro q hq
  rw [mem_conjSubgroup]
  have hn : (⟨q, hQM hq⟩ : M) ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.mpr hq
  have h := (inferInstance : (Q.subgroupOf M).Normal).conj_mem _ hn m⁻¹
  exact hQS (by simpa using Subgroup.mem_subgroupOf.mp h)

theorem caseA2_bar_conj {S : Subgroup G} (hQM : Q ≤ M) (hQS : Q ≤ S) (m : M) :
    bar M Q (conjSubgroup (m : G) S) =
      conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q S) := by
  ext z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) z
  rw [caseA2_mem_conj_bar hQS, caseA2_mem_bar (caseA2_Q_le_conj hQM hQS m)]

theorem caseA2_bar_mono {S T : Subgroup G} (h : S ≤ T) : bar M Q S ≤ bar M Q T :=
  Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

theorem caseA2_bar_self : bar M Q Q = ⊥ := by
  ext z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) z
  rw [caseA2_mem_bar le_rfl, Subgroup.mem_bot]
  exact ⟨fun h => (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr h),
    fun h => Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y).mp h)⟩

@[expose] def caseA2_lift (X : Subgroup (Mbar M Q)) : Subgroup G :=
  (X.comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype

theorem caseA2_subgroupOf_lift (X : Subgroup (Mbar M Q)) :
    (caseA2_lift X).subgroupOf M = X.comap (QuotientGroup.mk' (Q.subgroupOf M)) :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

theorem caseA2_bar_lift (X : Subgroup (Mbar M Q)) : bar M Q (caseA2_lift X) = X := by
  unfold bar
  rw [caseA2_subgroupOf_lift,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem caseA2_mem_lift (X : Subgroup (Mbar M Q)) (y : M) :
    (y : G) ∈ caseA2_lift X ↔ QuotientGroup.mk' (Q.subgroupOf M) y ∈ X := by
  rw [← Subgroup.mem_subgroupOf, caseA2_subgroupOf_lift]
  rfl

theorem caseA2_rep {S : Subgroup G} {x : Mbar M Q} (hx : x ∈ bar M Q S) :
    ∃ m : M, (m : G) ∈ S ∧ QuotientGroup.mk' (Q.subgroupOf M) m = x := by
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hx
  exact ⟨m, Subgroup.mem_subgroupOf.mp hm, hmx⟩

theorem caseA2_commute_iff (x y : M) :
    Commute (QuotientGroup.mk' (Q.subgroupOf M) x) (QuotientGroup.mk' (Q.subgroupOf M) y) ↔
      ⁅(x : G), (y : G)⁆ ∈ Q := by
  have h := map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) x y
  rw [Commute, SemiconjBy, ← commutatorElement_eq_one_iff_mul_comm, ← h]
  exact ⟨fun h1 => Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1),
    fun h1 => (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h1)⟩

theorem caseA2_conj_le {L N : Subgroup G} (hNL : N ≤ L) {g : G} (hg : g ∈ L) :
    conjSubgroup g N ≤ L := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h := L.mul_mem (L.mul_mem hg (hNL hx)) (L.inv_mem hg)
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e] at h
  exact h

theorem caseA2_conj_bar_le {S : Subgroup G} (hQM : Q ≤ M) (hQS : Q ≤ S) (m : M)
    (h : conjSubgroup (m : G) S ≤ S) :
    conjSubgroup (QuotientGroup.mk' (Q.subgroupOf M) m) (bar M Q S) ≤ bar M Q S := by
  rw [← caseA2_bar_conj hQM hQS m]
  exact caseA2_bar_mono h

end Bar

section Core

variable {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem caseA2_nilp_bot {L : Subgroup G} (hQM : Q ≤ M) (hQL : Q ≤ L) (hLM : L ≤ M)
    (hFL : ∀ A : Subgroup G, Q ≤ A → A ≤ L → (∀ s ∈ L, conjSubgroup s A = A) →
      QuotSat A Q (fun W _ => Group.IsNilpotent W) → A = Q)
    (A : Subgroup ↥(bar M Q L)) (hA : A.Normal) (hnil : Group.IsNilpotent ↥A) : A = ⊥ := by
  haveI := hA
  set Ab : Subgroup (Mbar M Q) := A.map (bar M Q L).subtype with hAb
  have hAb_le : Ab ≤ bar M Q L := Subgroup.map_subtype_le A
  have hAb_norm : ∀ g ∈ bar M Q L, ∀ a ∈ Ab, g * a * g⁻¹ ∈ Ab := by
    intro g hg a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    have hc := A.mul_mem (A.mul_mem (Subgroup.Normal.conj_mem inferInstance y hy ⟨g, hg⟩)
      (A.one_mem)) (A.one_mem)
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance y hy ⟨g, hg⟩
  set Ah : Subgroup G := caseA2_lift Ab with hAh
  have hbarAh : bar M Q Ah = Ab := caseA2_bar_lift Ab
  have hQAh : Q ≤ Ah := by
    intro q hq
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨q, hQM hq⟩ : M) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hq)
    have h2 : QuotientGroup.mk' (Q.subgroupOf M) (⟨q, hQM hq⟩ : M) ∈ Ab := by
      rw [h1]
      exact Ab.one_mem
    exact (caseA2_mem_lift Ab ⟨q, hQM hq⟩).mpr h2
  have hAhM : Ah ≤ M := Subgroup.map_subtype_le _
  have hAhL : Ah ≤ L := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hu' : QuotientGroup.mk' (Q.subgroupOf M) u ∈ Ab := hu
    obtain ⟨l, hlL, hlu⟩ := caseA2_rep (hAb_le hu')
    have h1 : l⁻¹ * u ∈ Q.subgroupOf M := QuotientGroup.eq.mp hlu
    have h2 : (l : G)⁻¹ * (u : G) ∈ Q := Subgroup.mem_subgroupOf.mp h1
    have e : (u : G) = (l : G) * ((l : G)⁻¹ * (u : G)) := by group
    show (u : G) ∈ L
    rw [e]
    exact L.mul_mem hlL (hQL h2)
  have hkey : ∀ s ∈ L, ∀ x ∈ Ah, s * x * s⁻¹ ∈ Ah := by
    intro s hs x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hu' : QuotientGroup.mk' (Q.subgroupOf M) u ∈ Ab := hu
    have hsM : s ∈ M := hLM hs
    have hwmem : QuotientGroup.mk' (Q.subgroupOf M)
        ((⟨s, hsM⟩ : M) * u * (⟨s, hsM⟩ : M)⁻¹) ∈ Ab := by
      rw [map_mul, map_mul, map_inv]
      exact hAb_norm _ ((caseA2_mem_bar hQL ⟨s, hsM⟩).mpr hs) _ hu'
    exact (caseA2_mem_lift Ab _).mpr hwmem
  have hconj : ∀ s ∈ L, conjSubgroup s Ah = Ah := by
    intro s hs
    ext x
    rw [mem_conjSubgroup]
    constructor
    · intro h
      have h2 := hkey s hs _ h
      have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
      rw [e] at h2
      exact h2
    · intro h
      have h2 := hkey s⁻¹ (L.inv_mem hs) x h
      rw [inv_inv] at h2
      exact h2
  have hQN : QuotSat Ah Q (fun W _ => Group.IsNilpotent W) := by
    refine quotSat_of_bar (P := fun W _ => Group.IsNilpotent W) ?_ hQAh hAhM ?_
    · intro X Y _ _ e hX
      haveI := hX
      exact Group.nilpotent_of_mulEquiv e
    · rw [hbarAh]
      haveI := hnil
      exact Group.nilpotent_of_mulEquiv (A.equivMapOfInjective _ (bar M Q L).subtype_injective)
  have hAh_eq : Ah = Q := hFL Ah hQAh hAhL hconj hQN
  have hAb_bot : Ab = ⊥ := by
    rw [← hbarAh, hAh_eq, caseA2_bar_self]
  exact (Subgroup.map_eq_bot_iff_of_injective _ (bar M Q L).subtype_injective).1 hAb_bot

theorem caseA2_solv_bot {L : Subgroup G}
    (hnil : ∀ A : Subgroup ↥(bar M Q L), A.Normal → Group.IsNilpotent ↥A → A = ⊥)
    (P : Subgroup ↥(bar M Q L)) [P.Normal] (hs : Group.IsSolvable ↥P) : P = ⊥ := by
  classical
  by_contra hP
  have hex : ∃ n, derivedSeries ↥P n = ⊥ := hs.solvable
  have hk : derivedSeries ↥P (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hk
    apply hP
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥P) ∈ (⊤ : Subgroup ↥P) := Subgroup.mem_top _
    rw [hk, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hx'
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [hj] at hk
  have hjne : derivedSeries ↥P j ≠ ⊥ := Nat.find_min hex (show j < Nat.find hex by omega)
  have h1 : ⁅derivedSeries ↥P j, derivedSeries ↥P j⁆ = ⊥ := by
    rw [← derivedSeries_succ]
    exact hk
  haveI hcomm : IsMulCommutative ↥(derivedSeries ↥P j) := Subgroup.commutator_self_eq_bot_iff.mp h1
  haveI : ((derivedSeries ↥P j).map P.subtype).Normal := inferInstance
  have hBnil : Group.IsNilpotent ↥((derivedSeries ↥P j).map P.subtype) :=
    Group.nilpotent_of_mulEquiv
      ((derivedSeries ↥P j).equivMapOfInjective P.subtype P.subtype_injective)
  have hB := hnil _ inferInstance hBnil
  exact hjne ((Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 hB)

end Core

section KorollarB

variable {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem caseA2_corBHyp {L N : Subgroup G} (hQN : Q ≤ N) (hNL : N ≤ L) (hLM : L ≤ M)
    (hEA : (∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ Q) ∧ ∀ x ∈ N, x ^ 2 ∈ Q)
    (hTI : ∀ m ∈ L, N ⊓ conjSubgroup (m : G) N = Q ∨ conjSubgroup (m : G) N = N)
    (hA1 : ∀ m ∈ L, ((∀ x ∈ N, ∀ y ∈ conjSubgroup (m : G) N, ⁅x, y⁆ ∈ Q) ↔
      conjSubgroup (m : G) N = N)) :
    CorBHyp ((bar M Q N).subgroupOf (bar M Q L)) := by
  have hQM : Q ≤ M := hQN.trans (hNL.trans hLM)
  have hQL : Q ≤ L := hQN.trans hNL
  have hNM : N ≤ M := hNL.trans hLM
  set T : Subgroup ↥(bar M Q L) := (bar M Q N).subgroupOf (bar M Q L) with hT
  have hTmem : ∀ y : ↥(bar M Q L), y ∈ T ↔ (y : Mbar M Q) ∈ bar M Q N := fun y => Iff.rfl
  have hconjmem : ∀ g y : ↥(bar M Q L), y ∈ conjSubgroup g T ↔
      (y : Mbar M Q) ∈ conjSubgroup (g : Mbar M Q) (bar M Q N) := by
    intro g y
    rw [mem_conjSubgroup, hTmem, mem_conjSubgroup]
    rfl
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    obtain ⟨x, hx, hxa⟩ := caseA2_rep ((hTmem a.1).mp a.2)
    obtain ⟨y, hy, hyb⟩ := caseA2_rep ((hTmem b.1).mp b.2)
    show (a.1 : Mbar M Q) * (b.1 : Mbar M Q) = (b.1 : Mbar M Q) * (a.1 : Mbar M Q)
    rw [← hxa, ← hyb]
    exact (caseA2_commute_iff x y).mpr (hEA.1 x hx y hy)
  · intro x hx
    obtain ⟨n, hn, hnx⟩ := caseA2_rep ((hTmem x).mp hx)
    apply Subtype.ext
    show (x : Mbar M Q) ^ 2 = 1
    rw [← hnx, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (hEA.2 n hn))
  · intro g
    obtain ⟨m, hmL, hmg⟩ := caseA2_rep g.2
    rcases hTI (m : G) hmL with h | h
    · left
      rw [eq_bot_iff]
      rintro y ⟨hyT, hyC⟩
      rw [Subgroup.mem_bot]
      obtain ⟨k, hkN, hky⟩ := caseA2_rep ((hTmem y).mp hyT)
      have hC := (hconjmem g y).mp hyC
      rw [← hmg, ← hky, caseA2_mem_conj_bar hQN] at hC
      have hkQ : (k : G) ∈ Q := by
        have hmem : (k : G) ∈ N ⊓ conjSubgroup (m : G) N := ⟨hkN, hC⟩
        rw [h] at hmem
        exact hmem
      apply Subtype.ext
      rw [← hky]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hkQ)
    · right
      refine le_antisymm inf_le_left (le_inf le_rfl ?_)
      intro y hyT
      obtain ⟨k, hkN, hky⟩ := caseA2_rep ((hTmem y).mp hyT)
      refine (hconjmem g y).mpr ?_
      rw [← hmg, ← hky, caseA2_mem_conj_bar hQN, h]
      exact hkN
  · intro g
    obtain ⟨m, hmL, hmg⟩ := caseA2_rep g.2
    have key1 : (∀ x ∈ T, ∀ y ∈ conjSubgroup g T, Commute x y) ↔
        (∀ x ∈ N, ∀ y ∈ conjSubgroup (m : G) N, ⁅x, y⁆ ∈ Q) := by
      constructor
      · intro h x hx y hy
        have hyL : y ∈ L := caseA2_conj_le hNL hmL hy
        have hxL : QuotientGroup.mk' (Q.subgroupOf M) (⟨x, hNM hx⟩ : M) ∈ bar M Q L :=
          (caseA2_mem_bar hQL _).mpr (hNL hx)
        have hyL' : QuotientGroup.mk' (Q.subgroupOf M) (⟨y, hLM hyL⟩ : M) ∈ bar M Q L :=
          (caseA2_mem_bar hQL _).mpr hyL
        have hxT : (⟨_, hxL⟩ : ↥(bar M Q L)) ∈ T :=
          (hTmem _).mpr ((caseA2_mem_bar hQN _).mpr hx)
        have hyT : (⟨_, hyL'⟩ : ↥(bar M Q L)) ∈ conjSubgroup g T := by
          rw [hconjmem]
          show QuotientGroup.mk' (Q.subgroupOf M) (⟨y, hLM hyL⟩ : M) ∈
            conjSubgroup (g : Mbar M Q) (bar M Q N)
          rw [← hmg]
          exact (caseA2_mem_conj_bar hQN m ⟨y, hLM hyL⟩).mpr hy
        have hc : (⟨_, hxL⟩ : ↥(bar M Q L)) * ⟨_, hyL'⟩ = ⟨_, hyL'⟩ * ⟨_, hxL⟩ :=
          h _ hxT _ hyT
        exact (caseA2_commute_iff ⟨x, hNM hx⟩ ⟨y, hLM hyL⟩).mp (congrArg Subtype.val hc)
      · intro h x hx y hy
        obtain ⟨k, hkN, hkx⟩ := caseA2_rep ((hTmem x).mp hx)
        obtain ⟨l, hlL, hly⟩ := caseA2_rep y.2
        have hyC : (l : G) ∈ conjSubgroup (m : G) N := by
          have h1 := (hconjmem g y).mp hy
          rw [← hmg, ← hly] at h1
          exact (caseA2_mem_conj_bar hQN m l).mp h1
        have hc := h k hkN l hyC
        show x * y = y * x
        apply Subtype.ext
        show (x : Mbar M Q) * (y : Mbar M Q) = (y : Mbar M Q) * (x : Mbar M Q)
        rw [← hkx, ← hly]
        exact (caseA2_commute_iff k l).mpr hc
    have lemA : conjSubgroup g T = T ↔
        conjSubgroup (g : Mbar M Q) (bar M Q N) = bar M Q N := by
      constructor
      · intro h
        ext z
        constructor
        · intro hzC
          have hzL : z ∈ bar M Q L := by
            have h1 : (g : Mbar M Q)⁻¹ * z * (g : Mbar M Q) ∈ bar M Q N :=
              mem_conjSubgroup.mp hzC
            have h2 : (g : Mbar M Q)⁻¹ * z * (g : Mbar M Q) ∈ bar M Q L :=
              caseA2_bar_mono hNL h1
            have e : z = (g : Mbar M Q) * ((g : Mbar M Q)⁻¹ * z * (g : Mbar M Q)) *
                (g : Mbar M Q)⁻¹ := by group
            rw [e]
            exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 h2) (Subgroup.inv_mem _ g.2)
          have hz' : (⟨z, hzL⟩ : ↥(bar M Q L)) ∈ conjSubgroup g T := (hconjmem g _).mpr hzC
          rw [h] at hz'
          exact (hTmem _).mp hz'
        · intro hzN
          have hzL : z ∈ bar M Q L := caseA2_bar_mono hNL hzN
          have hz' : (⟨z, hzL⟩ : ↥(bar M Q L)) ∈ T := (hTmem _).mpr hzN
          rw [← h] at hz'
          exact (hconjmem g _).mp hz'
      · intro h
        ext y
        rw [hconjmem, hTmem, h]
    have lemB : conjSubgroup (g : Mbar M Q) (bar M Q N) = bar M Q N ↔
        conjSubgroup (m : G) N = N := by
      rw [← hmg, ← caseA2_bar_conj hQM hQN m]
      constructor
      · intro h
        exact eq_of_bar_eq (caseA2_Q_le_conj hQM hQN m) (caseA2_conj_le hNM m.2) hQN hNM h
      · intro h
        rw [h]
    exact key1.trans ((hA1 (m : G) hmL).trans (lemA.trans lemB).symm)

theorem caseA2_T_ne_bot {L N : Subgroup G} (hQN : Q ≤ N) (hNL : N ≤ L) (hNM : N ≤ M)
    (hQL : Q ≤ L) (hNe : N ≠ Q) : (bar M Q N).subgroupOf (bar M Q L) ≠ ⊥ := by
  intro hbot
  apply hNe
  refine le_antisymm (fun n hn => ?_) hQN
  have hmem : (⟨QuotientGroup.mk' (Q.subgroupOf M) (⟨n, hNM hn⟩ : M),
      (caseA2_mem_bar hQL (⟨n, hNM hn⟩ : M)).mpr (hNL hn)⟩ : ↥(bar M Q L)) ∈
        (bar M Q N).subgroupOf (bar M Q L) :=
    Subgroup.mem_subgroupOf.mpr ((caseA2_mem_bar hQN (⟨n, hNM hn⟩ : M)).mpr hn)
  rw [hbot, Subgroup.mem_bot] at hmem
  have h2 : QuotientGroup.mk' (Q.subgroupOf M) (⟨n, hNM hn⟩ : M) = 1 :=
    congrArg Subtype.val hmem
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)

end KorollarB

section DJoin

variable {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
  [(Q.subgroupOf M).Normal]

@[expose] def caseA2_D (L N : Subgroup G) : Subgroup G := ⨆ g ∈ L, conjSubgroup g N

theorem caseA2_D_le {L N : Subgroup G} (hNL : N ≤ L) : caseA2_D L N ≤ L :=
  iSup₂_le fun _ hg => caseA2_conj_le hNL hg

theorem caseA2_le_D {L N : Subgroup G} (hL : (1 : G) ∈ L) : N ≤ caseA2_D L N := by
  have h := le_iSup₂ (f := fun g (_ : g ∈ L) => conjSubgroup g N) (1 : G) hL
  rw [conjSubgroup_one] at h
  exact h

theorem caseA2_D_normal {L N : Subgroup G} {s : G} (hs : s ∈ L) :
    conjSubgroup s (caseA2_D L N) ≤ caseA2_D L N := by
  have h : caseA2_D L N ≤ (caseA2_D L N).comap (MulAut.conj s).toMonoidHom := by
    unfold caseA2_D
    refine iSup₂_le fun g hg => ?_
    intro x hx
    show (MulAut.conj s).toMonoidHom x ∈ caseA2_D L N
    have hx' : s * x * s⁻¹ ∈ conjSubgroup (s * g) N := by
      rw [mem_conjSubgroup] at hx ⊢
      have e : (s * g)⁻¹ * (s * x * s⁻¹) * (s * g) = g⁻¹ * x * g := by group
      rw [e]
      exact hx
    exact le_iSup₂ (f := fun g (_ : g ∈ L) => conjSubgroup g N) (s * g) (L.mul_mem hs hg) hx'
  exact Subgroup.map_le_iff_le_comap.mpr h

theorem caseA2_normalClosure_map {L N : Subgroup G} (hQM : Q ≤ M) (hQN : Q ≤ N)
    (hNL : N ≤ L) (hLM : L ≤ M) (hQL : Q ≤ L) :
    (Subgroup.normalClosure
        (((bar M Q N).subgroupOf (bar M Q L) : Subgroup ↥(bar M Q L)) :
          Set ↥(bar M Q L))).map (bar M Q L).subtype =
      bar M Q (caseA2_D L N) := by
  have hNM : N ≤ M := hNL.trans hLM
  have hDL : caseA2_D L N ≤ L := caseA2_D_le hNL
  have hDM : caseA2_D L N ≤ M := hDL.trans hLM
  have hND : N ≤ caseA2_D L N := caseA2_le_D L.one_mem
  have hQD : Q ≤ caseA2_D L N := hQN.trans hND
  have hDsub : ((bar M Q (caseA2_D L N)).subgroupOf (bar M Q L)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨l, hlL, hlg⟩ := caseA2_rep g.2
    have hconj : conjSubgroup (g : Mbar M Q) (bar M Q (caseA2_D L N)) ≤
        bar M Q (caseA2_D L N) := by
      rw [← hlg]
      exact caseA2_conj_bar_le hQM hQD l (caseA2_D_normal hlL)
    have hmem : (g : Mbar M Q) * (n : Mbar M Q) * (g : Mbar M Q)⁻¹ ∈
        conjSubgroup (g : Mbar M Q) (bar M Q (caseA2_D L N)) := by
      rw [mem_conjSubgroup]
      have e : (g : Mbar M Q)⁻¹ * ((g : Mbar M Q) * (n : Mbar M Q) * (g : Mbar M Q)⁻¹) *
          (g : Mbar M Q) = (n : Mbar M Q) := by group
      rw [e]
      exact hn
    exact hconj hmem
  haveI := hDsub
  set K := Subgroup.normalClosure
    (((bar M Q N).subgroupOf (bar M Q L) : Subgroup ↥(bar M Q L)) : Set ↥(bar M Q L)) with hK
  have hTD : (((bar M Q N).subgroupOf (bar M Q L) : Subgroup ↥(bar M Q L)) :
      Set ↥(bar M Q L)) ⊆ (bar M Q (caseA2_D L N)).subgroupOf (bar M Q L) := by
    intro t ht
    have ht' : t ∈ (bar M Q N).subgroupOf (bar M Q L) := ht
    exact Subgroup.mem_subgroupOf.mpr
      (caseA2_bar_mono hND (Subgroup.mem_subgroupOf.mp ht'))
  have hKD : K ≤ (bar M Q (caseA2_D L N)).subgroupOf (bar M Q L) :=
    Subgroup.normalClosure_le_normal hTD
  have h1 : K.map (bar M Q L).subtype ≤ bar M Q (caseA2_D L N) := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_subgroupOf.mp (hKD hk)
  have hDlift : caseA2_D L N ≤ caseA2_lift (K.map (bar M Q L).subtype) := by
    unfold caseA2_D
    refine iSup₂_le fun g hg => ?_
    intro x hx
    have hxL : x ∈ L := caseA2_conj_le hNL hg hx
    have hxM : x ∈ M := hLM hxL
    refine (caseA2_mem_lift _ ⟨x, hxM⟩).mpr ?_
    have hnN : g⁻¹ * x * g ∈ N := mem_conjSubgroup.mp hx
    have hgM : g ∈ M := hLM hg
    have hnM : g⁻¹ * x * g ∈ M := hNM hnN
    have hnbarL : QuotientGroup.mk' (Q.subgroupOf M) (⟨g⁻¹ * x * g, hnM⟩ : M) ∈ bar M Q L :=
      (caseA2_mem_bar hQL _).mpr (hNL hnN)
    have hnT : (⟨_, hnbarL⟩ : ↥(bar M Q L)) ∈ (bar M Q N).subgroupOf (bar M Q L) :=
      Subgroup.mem_subgroupOf.mpr ((caseA2_mem_bar hQN _).mpr hnN)
    have hnK : (⟨_, hnbarL⟩ : ↥(bar M Q L)) ∈ K := Subgroup.subset_normalClosure hnT
    have hgbar : QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M) ∈ bar M Q L :=
      (caseA2_mem_bar hQL _).mpr hg
    have hcon := Subgroup.Normal.conj_mem inferInstance _ hnK (⟨_, hgbar⟩ : ↥(bar M Q L))
    refine Subgroup.mem_map.mpr ⟨_, hcon, ?_⟩
    have e : (⟨x, hxM⟩ : M) = (⟨g, hgM⟩ : M) * ⟨g⁻¹ * x * g, hnM⟩ * (⟨g, hgM⟩ : M)⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    show (QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M) : Mbar M Q) *
        QuotientGroup.mk' (Q.subgroupOf M) ⟨g⁻¹ * x * g, hnM⟩ *
        (QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hgM⟩ : M))⁻¹ =
      QuotientGroup.mk' (Q.subgroupOf M) (⟨x, hxM⟩ : M)
    rw [e, map_mul, map_mul, map_inv]
  have h2 : bar M Q (caseA2_D L N) ≤ K.map (bar M Q L).subtype :=
    (caseA2_bar_mono hDlift).trans (le_of_eq (caseA2_bar_lift _))
  exact le_antisymm h1 h2

end DJoin

section CaseA2


theorem caseA2_of
    (hCorB : CorollaryBStmt) (hA1 : CaseA1Statement) (hTI : NtTIStatement)
    (hEA : NtElemAbelianStatement) (hF : M1FittingTrivialStatement) : CaseA2Statement := by
  intro G _ _ M Q Z B t hH hA
  have hc : Ctx M Q Z B := hH.ctx
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have hQM : Q ≤ M := hc.hyp.Q_normal.1
  have hLM : Lgen M (LB M Q B) ≤ M := Lgen_le_M hc
  have hLH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  have hQL : Q ≤ Lgen M (LB M Q B) := Q_le_Lgen M Q B
  have hNL : Nt M (LB M Q B) t ≤ Lgen M (LB M Q B) :=
    (Subgroup.map_subtype_le _).trans (Rt_le_Lgen M (LB M Q B) t)
  have hQN : Q ≤ Nt M (LB M Q B) t := Q_le_Nt hc hH.mem
  have hNM : Nt M (LB M Q B) t ≤ M := hNL.trans hLM
  have hNQ : Nt M (LB M Q B) t ≠ Q := by
    intro h
    have hcard := hH.case.2.1
    rw [h] at hcard
    have hZ := hc.hyp.q4
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    have h1 : Nat.card Q * Nat.card Z = Nat.card Q * 1 := by
      rw [mul_one]
      exact hcard.symm
    have h2 := Nat.eq_of_mul_eq_mul_left hQpos h1
    omega
  have hEA' := hEA G M Q Z B t hH
  have hTI' : ∀ m ∈ Lgen M (LB M Q B),
      Nt M (LB M Q B) t ⊓ conjSubgroup m (Nt M (LB M Q B) t) = Q ∨
        conjSubgroup m (Nt M (LB M Q B) t) = Nt M (LB M Q B) t :=
    fun m hm => hTI G M Q Z B t hH m (hLH hm)
  have hA1' : ∀ m ∈ Lgen M (LB M Q B),
      ((∀ x ∈ Nt M (LB M Q B) t, ∀ y ∈ conjSubgroup m (Nt M (LB M Q B) t), ⁅x, y⁆ ∈ Q) ↔
        conjSubgroup m (Nt M (LB M Q B) t) = Nt M (LB M Q B) t) :=
    fun m hm => hA1 G M Q Z B t hH hA m hm
  have hFL : ∀ A : Subgroup G, Q ≤ A → A ≤ Lgen M (LB M Q B) →
      (∀ s ∈ Lgen M (LB M Q B), conjSubgroup s A = A) →
        QuotSat A Q (fun W _ => Group.IsNilpotent W) → A = Q :=
    fun A h1 h2 h3 h4 => hF G M Q Z B t hH A h1 h2 h3 h4
  have hCorBT := caseA2_corBHyp hQN hNL hLM hEA' hTI' hA1'
  have hT := caseA2_T_ne_bot hQN hNL hNM hQL hNQ
  have hnil : ∀ A : Subgroup ↥(bar M Q (Lgen M (LB M Q B))), A.Normal →
      Group.IsNilpotent ↥A → A = ⊥ :=
    fun A hA' hA'' => caseA2_nilp_bot hQM hQL hLM hFL A hA' hA''
  have hO2 : ∀ P : Subgroup ↥(bar M Q (Lgen M (LB M Q B))), P.Normal → IsPGroup 2 P → P = ⊥ := by
    intro P hP hp
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hnil P hP hp.isNilpotent
  have hO : ∀ P : Subgroup ↥(bar M Q (Lgen M (LB M Q B))), P.Normal →
      Odd (Nat.card P) → P = ⊥ := by
    intro P hP hodd
    exact caseA2_solv_bot hnil P (CFSG.FeitThompson.isSolvable_of_odd_natCard ↥P hodd)
  have hTp := corB_isPGroup_of_isElemAbelian _ hCorBT.1
  have hThm := hCorB _ _ hCorBT
  have hList := corB_listGroup hT hTp hThm hO2 hO
  have hmap := caseA2_normalClosure_map hQM hQN hNL hLM hQL
  have hLD : ListGroup ↥(bar M Q (caseA2_D (Lgen M (LB M Q B)) (Nt M (LB M Q B) t))) := by
    rw [← hmap]
    exact ListGroup.of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (bar M Q (Lgen M (LB M Q B))).subtype_injective) hList
  have hsimple := listGroup_isSimpleGroup hLD
  have hQD : Q ≤ caseA2_D (Lgen M (LB M Q B)) (Nt M (LB M Q B) t) :=
    hQN.trans (caseA2_le_D (Lgen M (LB M Q B)).one_mem)
  have hDM : caseA2_D (Lgen M (LB M Q B)) (Nt M (LB M Q B) t) ≤ M :=
    (caseA2_D_le hNL).trans hLM
  have hiso : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y →
      (IsSimpleGroup X ∧ ListGroup X) → (IsSimpleGroup Y ∧ ListGroup Y) :=
    fun X Y _ _ e h => ⟨(MulEquiv.isSimpleGroup_congr e).1 h.1, ListGroup.of_mulEquiv e h.2⟩
  exact quotSat_of_bar (P := fun W _ => IsSimpleGroup W ∧ ListGroup W) hiso hQD hDM
    ⟨hsimple, hLD⟩

end CaseA2

end CFSG.RankThree.GF2n.Smith81.Smith23E1
