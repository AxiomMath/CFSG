module

public import CFSG.Quasithin.Vol2.KGFactJ4M3KL
public import CFSG.Quasithin.Vol2.KGFactJ4M3Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Def
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.Row17Gen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc
  CFSG.Quasithin.F134.J4E9 CFSG.Quasithin.KGC31 CFSG.Quasithin.Special2 CFSG.Quasithin.J4Fam
  CFSG.Quasithin.J4Rad CFSG.Quasithin.J4M3
open scoped commutatorElement

namespace Stellmacher.CD.L3YC.R17

section M3

theorem Q_le_of_normQ {Y : Subgroup J} (hYM : Y ≤ M3)
    (hY : Qg ≤ Subgroup.normalizer (Y : Set J)) {y : J} (hy : y ∈ Y) (hyx : y⁻¹ * xM ∈ Qg) :
    Qg ≤ Y := by
  obtain ⟨q₀, hq₀, hx⟩ : ∃ q₀ ∈ Qg, xM = y * q₀ := ⟨y⁻¹ * xM, hyx, by group⟩
  have hdec : ∀ i : Fin 12, ∃ a ∈ Y, ∃ b ∈ V0, qF i = a * b := by
    intro i
    have hp : pJ i ∈ Qg := pJ_mem_Q i.2
    refine ⟨⁅pJ i, y⁆, ?_, y * ⁅pJ i, q₀⁆ * y⁻¹, ?_, ?_⟩
    · rw [commutatorElement_def]
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY hp) y).mp hy) (Y.inv_mem hy)
    · have hc : ⁅pJ i, q₀⁆ ∈ V0 := by
        rw [← eSub_v0]
        exact qTable.comm_mem hp q₀ hq₀
      exact (Subgroup.mem_normalizer_iff.mp (hYM hy) _).mp hc
    · show qJ i = _
      rw [qJ, hx, commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
  choose a ha b hb hab using hdec
  have haQ : ∀ i, a i ∈ Qg := fun i => by
    have e : a i = qF i * (b i)⁻¹ := by rw [hab i]; group
    rw [e]
    exact Qg.mul_mem (mem_tabGroup i) (Qg.inv_mem (V0_le_Q (hb i)))
  have hcomm : ∀ i j, ⁅qF i, qF j⁆ ∈ Y := by
    intro i j
    rw [hab i, hab j, commutatorElement_mul_V0 (haQ i) (hb i) (haQ j) (hb j),
      commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem (ha i) (ha j)) (Y.inv_mem (ha i))) (Y.inv_mem (ha j))
  have hV0 : eSub hv0 ≤ Y := by
    rw [eSub_eq_closure, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨i, j, e⟩ := v0_comm k
    rw [e]
    exact hcomm i j
  have hV0' : V0 ≤ Y := eSub_v0 ▸ hV0
  refine sup_le ((Subgroup.closure_le _).mpr ?_) hV0
  rintro _ ⟨i, rfl⟩
  rw [hab i]
  exact Y.mul_mem (ha i) (hV0' (hb i))

theorem M3_le_normalizer_Qg : M3 ≤ Subgroup.normalizer (Qg : Set J) := by
  intro m hm
  have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M3 hm
  rwa [pCoreOf_M3_eq] at this

theorem isSylowTwoOf_P0_M3 (hP0M : P0 ≤ M3) : IsSylowTwoOf P0 M3 := by
  have hM := j4Facts.mat
  have hP0 : Nat.card P0 = 2097152 := by
    have := CFSG.Sporadic.J4.QT.card_P0 hM j4Facts
    rw [this]
    norm_num
  refine ⟨hP0M, IsPGroup.of_card (n := 21) (by rw [hP0]; norm_num), ?_⟩
  have h1 := Subgroup.index_mul_card (P0.subgroupOf M3)
  have h2 : Nat.card (P0.subgroupOf M3) = 2097152 := by
    rw [← hP0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP0M).toEquiv
  rw [h2, card_M3 j4Facts] at h1
  generalize (P0.subgroupOf M3).index = i at h1 ⊢
  have : i = 315 := by omega
  rw [this]
  norm_num

local notation "eM3" => E16.eNHom hv0 M3_le_eNorm

theorem m3_structure [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup J} (hperf : ⁅B, B⁆ = B)
    (hN : P0 ≤ Subgroup.normalizer (B : Set J)) (hBM : B ⊔ P0 ≤ M3)
    (hq : IsPSL 3 2 1 (↥B ⧸ CFSG.pCore 2 ↥B)) :
    B = KL ∧ (CFSG.pCore 2 ↥B).map B.subtype = Qg ∧ Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 15 := by
  classical
  have hM := j4Facts.mat
  have hs : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hq).2
  have hc168' : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 168 :=
    CFSG.Quasithin.SBc11.card_of_isPSL_three_two hq
  have hnsolv : ¬ Group.IsSolvable ↥B := by
    intro hsolv
    have hsq : Group.IsSolvable (↥B ⧸ CFSG.pCore 2 ↥B) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥B))
    obtain ⟨a, b, hab⟩ := nonabelian_of_card168 hc168'
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := ↥B ⧸ CFSG.pCore 2 ↥B)).2 hsq a b)
  have hBle : B ≤ M3 := le_sup_left.trans hBM
  have hP0M : P0 ≤ M3 := le_sup_right.trans hBM
  have hperfB : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.mpr hperf
  let incl : ↥B →* ↥M3 := Subgroup.inclusion hBle
  have hρ : ((rho3 j4Facts).comp incl).range = ⊥ := by
    haveI := hperfB
    have hRρ : Group.IsPerfect ((rho3 j4Facts).comp incl).range := Group.IsPerfect.range _
    rcases isPerfect_perm_five hRρ with h | h
    · exact h
    · exfalso
      have hmem : ∀ x, ((rho3 j4Facts).comp incl) x ∈ alternatingGroup (Fin 5) := fun x => by
        rw [← h]; exact ⟨x, rfl⟩
      let ρ' : ↥B →* alternatingGroup (Fin 5) := ((rho3 j4Facts).comp incl).codRestrict _ hmem
      have hρ's : Function.Surjective ρ' := by
        intro y
        have : (y : Equiv.Perm (Fin 5)) ∈ ((rho3 j4Facts).comp incl).range := by rw [h]; exact y.2
        obtain ⟨x, hx⟩ := this
        exact ⟨x, Subtype.ext hx⟩
      exact false_of_alt5_quotient hq ρ' hρ's
  have hBKL : B ≤ KL := by
    intro b hb
    have h1 : (rho3 j4Facts) ⟨b, hBle hb⟩ = 1 := by
      have : ((rho3 j4Facts).comp incl) ⟨b, hb⟩ ∈ ((rho3 j4Facts).comp incl).range := ⟨_, rfl⟩
      rw [hρ, Subgroup.mem_bot] at this
      exact this
    exact (rho3_eq_one_iff ⟨b, hBle hb⟩).mp h1
  haveI := E8.isSimpleGroup_statedSL3
  have hc168 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 := E8.card_statedSL3
  have hQ2 : IsPGroup 2 ↥Qg := IsPGroup.of_card (n := 15) card_Q
  have htop : (B.subgroupOf M3).map eM3 = ⊤ := by
    haveI := hperfB
    have hR : Group.IsPerfect ((MonoidHom.comp eM3 incl).range) := Group.IsPerfect.range _
    have hrange : (MonoidHom.comp eM3 incl).range = (B.subgroupOf M3).map eM3 := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rcases eq_bot_or_top_of_isPerfect (fun H hH => solvable_of_ne_top_card168 hc168 hH) hR with
      h | h
    · exfalso
      have hBQ : B ≤ Qg := by
        intro b hb
        have h1 : eM3 ⟨b, hBle hb⟩ = 1 := by
          have : (MonoidHom.comp eM3 incl) ⟨b, hb⟩ ∈ (MonoidHom.comp eM3 incl).range := ⟨_, rfl⟩
          rw [h, Subgroup.mem_bot] at this
          exact this
        have h2 := (eM3_eq_one_iff ⟨b, hBle hb⟩).mp h1
        have h3 : b ∈ KL ⊓ Subgroup.centralizer (V0 : Set J) :=
          Subgroup.mem_inf.mpr ⟨hBKL hb, h2⟩
        rw [KL_inf_centralizer_eq_K3, K3_eq_Q] at h3
        exact h3
      have hB2 : IsPGroup 2 ↥B := hQ2.to_le hBQ
      have := hB2.isNilpotent
      exact hnsolv inferInstance
    · rw [← hrange]; exact h
  have hP0Syl : IsSylowTwoOf P0 M3 := isSylowTwoOf_P0_M3 hP0M
  have hQP0 : Qg ≤ P0 := pCoreOf_M3_eq ▸ hP0Syl.pCoreOf_le
  have hQNB : Qg ≤ Subgroup.normalizer (B : Set J) := fun q hq => hN (hQP0 hq)
  obtain ⟨y, hy, hyx⟩ := exists_inv_mul_mem_Q hBKL htop xM_mem_KL
  have hQB : Qg ≤ B := Q_le_of_normQ hBle hQNB hy hyx
  have hBeq : B = KL := by
    refine le_antisymm hBKL (fun k hk => ?_)
    obtain ⟨l, hl, hlq⟩ := exists_inv_mul_mem_Q hBKL htop hk
    have : k = l * (l⁻¹ * k) := by group
    rw [this]
    exact B.mul_mem hl (hQB hlq)
  have hcardB : Nat.card ↥B = 2 ^ 15 * 168 := by rw [hBeq]; exact card_KL
  have hpc : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 15 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B)
    rw [CFSG.Quasithin.SBc11.card_of_isPSL_three_two hq, hcardB] at h1
    omega
  have hQcardB : Nat.card (Qg.subgroupOf B) = 2 ^ 15 := by
    rw [← card_Q]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQB).toEquiv
  have hQnormB : (Qg.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQB]
    exact hBle.trans M3_le_normalizer_Qg
  have hQpB : IsPGroup 2 ↥(Qg.subgroupOf B) := IsPGroup.of_card hQcardB
  have hle : Qg.subgroupOf B ≤ CFSG.pCore 2 ↥B := by
    unfold CFSG.pCore
    exact le_sSup ⟨hQnormB, hQpB⟩
  have hpceq : Qg.subgroupOf B = CFSG.pCore 2 ↥B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hpc, hQcardB])
  have hmap : (CFSG.pCore 2 ↥B).map B.subtype = Qg := by
    rw [← hpceq, Subgroup.map_subgroupOf_eq_of_le hQB]
  exact ⟨hBeq, hmap, hpc⟩

end M3

end Stellmacher.CD.L3YC.R17

end CFSG.Quasithin
