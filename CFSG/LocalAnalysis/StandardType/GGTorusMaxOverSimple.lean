module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxWielandt
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxNormalP
public import CFSG.Walter.J1.Tools
public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeFixedSylow
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHWeakCoreMinimalNormalFactors
import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl
public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockCharTwo
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHWeakCoreSylowTwoCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.GroupTheory.SteinbergCDRankOneAutPrimes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.FrameRoute

open Multiplicative CFSG.Open
open scoped Pointwise

structure TmOverData (G : Type) [Group G] [Finite G] (E : Subgroup G) (m N₀ : ℕ) : Prop where
  one_le : 1 ≤ m
  elem : IsElemAbelian 3 E
  card : Nat.card E = 3 ^ m
  cent : ∀ g ∈ Subgroup.normalizer (E : Set G), (∀ e ∈ E, g * e = e * g) → g ∈ E
  irr : ∀ F : Subgroup G, F ≤ E →
    (∀ g ∈ Subgroup.normalizer (E : Set G), ∀ f ∈ F, g * f * g⁻¹ ∈ F) → F = ⊥ ∨ F = E
  syl : ∃ P : Sylow 3 G, (P : Subgroup G) ≤ Subgroup.normalizer (E : Set G)
  frame : ∃ φ : E ≃* Multiplicative (Fin m → ZMod 3),
    (∀ X : Set E, (∀ g : Subgroup.normalizer (E : Set G), ∀ x ∈ X, E.normalizerMonoidHom g x ∈ X) →
        ∀ x ∈ X, x ≠ 1 → N₀ ≤ X.ncard) ∧
    (∀ P : Subgroup E → Prop, (∀ g : Subgroup.normalizer (E : Set G), ∀ K, P K →
        P (K.map (E.normalizerMonoidHom g).toMonoidHom)) →
      ∀ c, c ≠ 0 → P (tmKer φ c) → N₀ ≤ {c | c ≠ 0 ∧ P (tmKer φ c)}.ncard)
  idx : ∀ q, q ∣ Nat.card G / Nat.card (Subgroup.normalizer (E : Set G)) →
    (Odd q ∨ ∃ a, q = 2 ^ a) → q < 2 ^ N₀
  idx3 : ¬ 3 ∣ Nat.card G / Nat.card (Subgroup.normalizer (E : Set G))
  dec : ∀ k d, 2 ≤ k → d * k ≤ m → k * (3 ^ d - 1) < N₀

section General

variable {G : Type} [Group G] [Finite G]

theorem tmOver_card_mul_dvd {N K : Subgroup G} (hK : K ≤ Subgroup.normalizer (N : Set G))
    (hNK : N ⊓ K = ⊥) : Nat.card N * Nat.card K ∣ Nat.card G := by
  have hset : ((N ⊔ K : Subgroup G) : Set G) = (N : Set G) * K :=
    Subgroup.coe_mul_of_right_le_normalizer_left N K hK
  have hinj := Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hNK)
  have hmem : ∀ g : N × K, (g.1 : G) * g.2 ∈ (N ⊔ K : Subgroup G) := fun g => by
    rw [← SetLike.mem_coe, hset]
    exact Set.mul_mem_mul g.1.2 g.2.2
  have hbij : Function.Bijective fun g : N × K => (⟨(g.1 : G) * g.2, hmem g⟩ : ↥(N ⊔ K)) := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun y => ?_⟩
    have hy : (y : G) ∈ (N : Set G) * K := by rw [← hset]; exact y.2
    obtain ⟨n, hn, k, hk, hnk⟩ := hy
    exact ⟨(⟨n, hn⟩, ⟨k, hk⟩), Subtype.ext hnk⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective _ hbij)]
  exact Subgroup.card_subgroup_dvd_card _

theorem tmOver_four_pow_le {E V : Subgroup G} (hEV : E ≤ Subgroup.normalizer (V : Set G)) {m : ℕ}
    (φ : E ≃* Multiplicative (Fin m → ZMod 3)) (hm : 1 ≤ m)
    (hcop : Nat.Coprime (Nat.card V) (Nat.card E)) (hsolv : Group.IsSolvable V)
    (hfix : V ⊓ Subgroup.centralizer (E : Set G) = ⊥) :
    4 ^ (Finset.univ.filter fun c : Fin m → ZMod 3 => c ≠ 0 ∧
        Nat.card (V ⊓ Subgroup.centralizer (((tmKer φ c).map E.subtype : Subgroup G) : Set G) :
          Subgroup G) ≠ 1).card ≤ Nat.card V ^ 2 := by
  letI := CFSG.Walter.J1.conjAct E V hEV
  have hcard : ∀ S : Subgroup E, tmFixCard V S =
      Nat.card (V ⊓ Subgroup.centralizer ((S.map E.subtype : Subgroup G) : Set G) : Subgroup G) :=
    fun S => CFSG.Walter.J1.card_fixedPointSubgroup_conjAct E V hEV S
  have htop : tmFixCard V (⊤ : Subgroup E) = 1 := by
    rw [hcard, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hfix, Subgroup.card_bot]
  have h := tmWielandt_four_pow_le (J := V) φ hm hcop hsolv htop
  simp only [hcard] at h
  exact h

theorem tmOver_exists_ne_one {E V : Subgroup G} (hEV : E ≤ Subgroup.normalizer (V : Set G))
    {m : ℕ} (φ : E ≃* Multiplicative (Fin m → ZMod 3)) (hm : 1 ≤ m)
    (hcop : Nat.Coprime (Nat.card V) (Nat.card E)) (hsolv : Group.IsSolvable V)
    (hfix : V ⊓ Subgroup.centralizer (E : Set G) = ⊥) (hV : V ≠ ⊥) :
    ∃ c : Fin m → ZMod 3, c ≠ 0 ∧
      Nat.card (V ⊓ Subgroup.centralizer (((tmKer φ c).map E.subtype : Subgroup G) : Set G) :
        Subgroup G) ≠ 1 := by
  letI := CFSG.Walter.J1.conjAct E V hEV
  have hcard : ∀ S : Subgroup E, tmFixCard V S =
      Nat.card (V ⊓ Subgroup.centralizer ((S.map E.subtype : Subgroup G) : Set G) : Subgroup G) :=
    fun S => CFSG.Walter.J1.card_fixedPointSubgroup_conjAct E V hEV S
  have htop : tmFixCard V (⊤ : Subgroup E) = 1 := by
    rw [hcard, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hfix, Subgroup.card_bot]
  have h := tmWielandt_card_sq (J := V) φ hm hcop hsolv htop
  by_contra hno
  push Not at hno
  rw [Finset.prod_eq_one fun c hc => by
    rw [hcard]; exact hno c (Finset.mem_filter.mp hc).2] at h
  have h1 : Nat.card V = 1 := by
    rcases Nat.lt_or_ge (Nat.card V) 2 with h2 | h2
    · have := (Nat.card_pos : 0 < Nat.card V); omega
    · have := Nat.pow_le_pow_left h2 2; omega
  exact hV (Subgroup.card_eq_one.mp h1)

theorem tmOver_card_conj {N S : Subgroup G} {g : G} (hg : ∀ x, x ∈ N ↔ g * x * g⁻¹ ∈ N) :
    Nat.card (N ⊓ Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) :
      Set G) : Subgroup G) = Nat.card (N ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) := by
  have h : N ⊓ Subgroup.centralizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (N ⊓ Subgroup.centralizer (S : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_map, SetLike.mem_coe,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    constructor
    · rintro ⟨hyN, hyS⟩
      refine ⟨g⁻¹ * y * g, ⟨(hg _).mpr (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]),
        fun s hs => ?_⟩, by group⟩
      have h1 := hyS s hs
      calc s * (g⁻¹ * y * g) = g⁻¹ * ((g * s * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * s * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * y * g * s := by group
    · rintro ⟨x, ⟨hxN, hxS⟩, rfl⟩
      refine ⟨(hg x).mp hxN, fun s hs => ?_⟩
      calc g * s * g⁻¹ * (g * x * g⁻¹) = g * (s * x) * g⁻¹ := by group
        _ = g * (x * s) * g⁻¹ := by rw [hxS s hs]
        _ = g * x * g⁻¹ * (g * s * g⁻¹) := by group
  rw [h, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem tmOver_map_normalizerMonoidHom {E : Subgroup G} (g : Subgroup.normalizer (E : Set G))
    (K : Subgroup E) :
    (K.map (E.normalizerMonoidHom g).toMonoidHom).map E.subtype =
      (K.map E.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem tmOver_le_normalizer {H N : Subgroup G} (hNn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) :
    H ≤ Subgroup.normalizer (N : Set G) := fun g hg => by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hNn g hg x
  · intro hx
    have h1 := hNn g⁻¹ (H.inv_mem hg) _ hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

theorem tmOver_map_conj_eq {H N : Subgroup G} (hNn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) {h : G}
    (hh : h ∈ H) : N.map (MulAut.conj h).toMonoidHom = N := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hNn h hh x hx
  · intro hy
    refine ⟨h⁻¹ * y * h, ?_, by group⟩
    have h1 := hNn h⁻¹ (H.inv_mem hh) y hy
    rwa [inv_inv] at h1

theorem tmOver_comm_of_solvable {H N : Subgroup G} (hNn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N)
    (hN1 : N ≠ ⊥)
    (hmin : ∀ N' : Subgroup G, N' ≤ N → (∀ h ∈ H, ∀ x ∈ N', h * x * h⁻¹ ∈ N') → N' = ⊥ ∨ N' = N)
    (hsolv : Group.IsSolvable N) : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
  have hle : ⁅N, N⁆ ≤ N := Subgroup.commutator_le.mpr fun a ha b hb =>
    N.mul_mem (N.mul_mem (N.mul_mem ha hb) (N.inv_mem ha)) (N.inv_mem hb)
  have hinv : ∀ h ∈ H, ∀ x ∈ ⁅N, N⁆, h * x * h⁻¹ ∈ ⁅N, N⁆ := by
    intro h hh x hx
    have h1 : ⁅N, N⁆.map (MulAut.conj h).toMonoidHom = ⁅N, N⁆ := by
      rw [Subgroup.map_commutator, tmOver_map_conj_eq hNn hh]
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  rcases hmin _ hle hinv with h | h
  · have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (h1 hx) y hy).symm
  · exfalso
    have htop : commutator N = ⊤ := by
      apply Subgroup.map_injective N.subtype_injective
      rw [Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hds : ∀ n, derivedSeries N n = ⊤ := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [derivedSeries_succ, ih]; exact htop
    obtain ⟨n, hn⟩ := hsolv.solvable
    rw [hds] at hn
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx⟩ : N) ∈ (⊤ : Subgroup N) := Subgroup.mem_top _
    rw [hn, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h1

theorem tmOver_sylow_fixed_ne_one {E N : Subgroup G} (hEN : E ≤ Subgroup.normalizer (N : Set G))
    (hE3 : IsPGroup 3 E) (h3N : ¬ 3 ∣ Nat.card N) (P : Sylow 2 N)
    (hPinv : ∀ e ∈ E, ∀ x ∈ (P : Subgroup N).map N.subtype,
      e * x * e⁻¹ ∈ (P : Subgroup N).map N.subtype)
    (K : Subgroup E)
    (h2 : 2 ∣ Nat.card (N ⊓ Subgroup.centralizer ((K.map E.subtype : Subgroup G) : Set G) :
      Subgroup G)) :
    Nat.card ((P : Subgroup N).map N.subtype ⊓
      Subgroup.centralizer ((K.map E.subtype : Subgroup G) : Set G) : Subgroup G) ≠ 1 := by
  classical
  letI := CFSG.Walter.J1.conjAct E N hEN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := CFSG.Walter.J1.card_fixedPointSubgroup_conjAct E N hEN K
  have hK3 : IsPGroup 3 K := hE3.to_subgroup K
  have hPK : CFSG.DisconnectedInvolutionGraph.Helpers.InvariantSubgroup (A := K)
      (P : Subgroup N) := by
    intro k x hx
    have h1 := hPinv (k : G) (k : E).2 x ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = k • x := Subtype.ext hyx
    rw [← this]
    exact hy
  obtain ⟨S, hS⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_fixed_sylow
    (A := K) (G := N) 3 2 hK3 h3N P hPK
  have hS1 : (S : Subgroup (FixedPoints.subgroup K N)) ≠ ⊥ := S.ne_bot_of_dvd_card (by
    change 2 ∣ Nat.card (fixedPointSubgroup K N)
    rw [hF]
    exact h2)
  rw [hS] at hS1
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS1
  intro hcard
  have hbot := Subgroup.card_eq_one.mp hcard
  have hmem : (((y : FixedPoints.subgroup K N) : N) : G) ∈
      (P : Subgroup N).map N.subtype ⊓
        Subgroup.centralizer ((K.map E.subtype : Subgroup G) : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨⟨_, Subgroup.mem_subgroupOf.mp hy, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    have hfix := (FixedPoints.mem_subgroup K N _).mp (y : FixedPoints.subgroup K N).2 ⟨k, hk⟩
    have h3 := congrArg Subtype.val hfix
    change (k : G) * ((y : N) : G) * (k : G)⁻¹ = ((y : N) : G) at h3
    calc E.subtype k * ((y : N) : G) = (k : G) * ((y : N) : G) * (k : G)⁻¹ * k := by
          simp [mul_assoc]
      _ = ((y : N) : G) * E.subtype k := by rw [h3]; rfl
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hy1
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact hmem

theorem tmOver_iSup_le_normalizer {r : ℕ} {T : Fin r → Subgroup G}
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ T i → y ∈ T j → Commute x y) (j : Fin r) :
    (⨆ i, T i) ≤ Subgroup.normalizer (T j : Set G) := by
  refine iSup_le fun k => ?_
  by_cases hkj : k = j
  · subst hkj
    exact Subgroup.le_normalizer
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxy : ∀ y ∈ T j, x * y * x⁻¹ = y := fun y hy => by
      rw [(hcomm hkj x y hx hy).eq, mul_inv_cancel_right]
    constructor
    · intro hy
      rw [hxy y hy]
      exact hy
    · intro hy
      have hc := (hcomm hkj x _ hx hy).eq
      have h2 : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [hc]
          _ = x * y * x⁻¹ := by group
      rw [h2]
      exact hy

theorem tmOver_commute_of_inf_eq_bot {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (h : A ⊓ B = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := by
    refine ⟨?_, ?_⟩
    · have := A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hBA hb) a⁻¹).mp (A.inv_mem ha))
      rwa [show a * (b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ by group] at this
    · exact B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAB ha) b).mp hb) (B.inv_mem hb)
  rw [h, Subgroup.mem_bot] at h1
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem tmOver_eq_bot_or_eq_of_simple {T X : Subgroup G} [IsSimpleGroup T] (hXT : X ≤ T)
    (hX : T ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ ∨ X = T := by
  haveI hn : (X.subgroupOf T).Normal := ⟨fun x hx t => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hX t.2) x).mp hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.subgroupOf T) with h | h
  · left
    rw [← Subgroup.map_subgroupOf_eq_of_le hXT, h, Subgroup.map_bot]
  · right
    rw [← Subgroup.map_subgroupOf_eq_of_le hXT, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem tmOver_eq_factor {r : ℕ} {T : Fin r → Subgroup G}
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ T i → y ∈ T j → Commute x y)
    (hsimp : ∀ i, IsSimpleGroup (T i)) {S : Subgroup G} [IsSimpleGroup S]
    (hSN : S ≤ ⨆ i, T i) (hNS : (⨆ i, T i) ≤ Subgroup.normalizer (S : Set G))
    (hnab : ¬ ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : ∃ j, S = T j := by
  by_contra hno
  push Not at hno
  apply hnab
  have hbot : ∀ j, S ⊓ T j = ⊥ := by
    intro j
    haveI := hsimp j
    have hTj : T j ≤ ⨆ i, T i := le_iSup T j
    rcases tmOver_eq_bot_or_eq_of_simple (T := T j) (X := S ⊓ T j) inf_le_right (fun t ht => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨hyS, hyT⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hNS (hTj ht)) y).mp hyS,
          T j |>.mul_mem (T j |>.mul_mem ht hyT) (T j |>.inv_mem ht)⟩
      · rintro ⟨hyS, hyT⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hNS (hTj ht)) y).mpr hyS, ?_⟩
        have := T j |>.mul_mem (T j |>.mul_mem (T j |>.inv_mem ht) hyT) ht
        rwa [show t⁻¹ * (t * y * t⁻¹) * t = y by group] at this) with h | h
    · exact h
    ·
      exfalso
      have hTS : T j ≤ S := h ▸ inf_le_left
      rcases tmOver_eq_bot_or_eq_of_simple (T := S) (X := T j) hTS (fun s hs =>
        tmOver_iSup_le_normalizer hcomm j (hSN hs)) with h' | h'
      · haveI := hsimp j
        obtain ⟨a, b, hab⟩ := exists_pair_ne (T j)
        apply hab
        have ha1 : (a : G) = 1 := Subgroup.mem_bot.mp (h'.le a.2)
        have hb1 : (b : G) = 1 := Subgroup.mem_bot.mp (h'.le b.2)
        exact Subtype.ext (ha1.trans hb1.symm)
      · exact hno j h'.symm
  have hcen : ∀ j, ∀ x ∈ S, ∀ y ∈ T j, x * y = y * x := fun j =>
    tmOver_commute_of_inf_eq_bot (fun s hs => tmOver_iSup_le_normalizer hcomm j (hSN hs))
      (fun t ht => hNS (le_iSup T j ht)) (hbot j)
  have hS : (⨆ i, T i) ≤ Subgroup.centralizer (S : Set G) := iSup_le fun j y hy =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hcen j x hx y hy
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hS (hSN hy)) x hx)

theorem tmOver_comp_commute {r : ℕ} {T : Fin r → Subgroup G}
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ T i → y ∈ T j → Commute x y)
    {x y : (i : Fin r) → T i} (hxy : x * y = y * x) (i : Fin r) :
    (x i : G) * Subgroup.noncommPiCoprod hcomm y = Subgroup.noncommPiCoprod hcomm y * x i := by
  classical
  have h : Pi.mulSingle i (x i) * y = y * Pi.mulSingle i (x i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.mul_apply, Pi.mulSingle_eq_same]
      exact congrFun hxy j
    · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj]
  have h1 := congrArg (Subgroup.noncommPiCoprod hcomm) h
  simp only [map_mul, Subgroup.noncommPiCoprod_mulSingle] at h1
  exact h1

theorem tmOver_commute_of_comp_one {r : ℕ} {T : Fin r → Subgroup G}
    (hcomm : Pairwise fun i j => ∀ x y : G, x ∈ T i → y ∈ T j → Commute x y)
    {x : (i : Fin r) → T i} {i : Fin r} (hx : x i = 1) {t : G} (ht : t ∈ T i) :
    Subgroup.noncommPiCoprod hcomm x * t = t * Subgroup.noncommPiCoprod hcomm x := by
  classical
  have h : x * Pi.mulSingle i ⟨t, ht⟩ = Pi.mulSingle i ⟨t, ht⟩ * x := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Pi.mul_apply, Pi.mulSingle_eq_same, hx]
    · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj]
  have h1 := congrArg (Subgroup.noncommPiCoprod hcomm) h
  simp only [map_mul, Subgroup.noncommPiCoprod_mulSingle] at h1
  exact h1

theorem tmOver_exists_minNormal {H : Subgroup G} (hH : H ≠ ⊥) :
    ∃ N : Subgroup G, N ≤ H ∧ (∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) ∧ N ≠ ⊥ ∧
      ∀ N' : Subgroup G, N' ≤ N → (∀ h ∈ H, ∀ x ∈ N', h * x * h⁻¹ ∈ N') → N' = ⊥ ∨ N' = N := by
  classical
  obtain ⟨N, ⟨hNH, hNn, hN1⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {N | N ≤ H ∧ (∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) ∧ N ≠ ⊥}
    ⟨H, le_rfl, fun h hh x hx => H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh), hH⟩
  refine ⟨N, hNH, hNn, hN1, fun N' hN'N hN'n => ?_⟩
  by_cases h : N' = ⊥
  · exact Or.inl h
  · right
    by_contra hne
    exact hmin N' ⟨hN'N.trans hNH, hN'n, h⟩ (lt_of_le_of_ne hN'N hne)

end General

namespace TmOverData

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {m N₀ : ℕ}

theorem mem_of_commute (hD : TmOverData G E m N₀) {g : G} (hg : ∀ e ∈ E, g * e = e * g) :
    g ∈ E := by
  refine hD.cent g ?_ hg
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    rw [hg e he, mul_inv_cancel_right]
    exact he
  · intro he
    have h := hg _ he
    have h2 : g * (g * e * g⁻¹) = g * e := by rw [h]; group
    have h3 : g * e * g⁻¹ = e := mul_left_cancel h2
    rw [h3] at he
    exact he

theorem centralizer_le (hD : TmOverData G E m N₀) : Subgroup.centralizer (E : Set G) ≤ E :=
  fun g hg => hD.mem_of_commute fun e he => (Subgroup.mem_centralizer_iff.mp hg e he).symm

theorem ne_bot (hD : TmOverData G E m N₀) : E ≠ ⊥ := fun h => by
  have := hD.card
  rw [h, Subgroup.card_bot] at this
  have h1 : 3 ≤ 3 ^ m := Nat.le_self_pow (by have := hD.one_le; omega) 3
  omega

theorem isPGroup (hD : TmOverData G E m N₀) : IsPGroup 3 E := fun x =>
  ⟨1, Subtype.ext (by simpa using hD.elem.2 x x.2)⟩

theorem comm (hD : TmOverData G E m N₀) : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (hD.elem.1.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)

theorem eq_bot_of_inf_eq_bot (hD : TmOverData G E m N₀) {X : Subgroup G}
    (hXM : X ≤ Subgroup.normalizer (E : Set G))
    (hXn : ∀ g ∈ Subgroup.normalizer (E : Set G), ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hXE : X ⊓ E = ⊥) :
    X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxE : x ∈ E := by
    refine hD.cent x (hXM hx) fun e he => ?_
    have hc1 : x * e * x⁻¹ * e⁻¹ ∈ X := by
      have h1 := hXn e (Subgroup.le_normalizer he) x⁻¹ (X.inv_mem hx)
      have h := X.mul_mem hx h1
      rwa [show x * (e * x⁻¹ * e⁻¹) = x * e * x⁻¹ * e⁻¹ by group] at h
    have hc2 : x * e * x⁻¹ * e⁻¹ ∈ E :=
      E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXM hx) e).mp he) (E.inv_mem he)
    have hc : x * e * x⁻¹ * e⁻¹ = 1 := by
      have h : x * e * x⁻¹ * e⁻¹ ∈ X ⊓ E := ⟨hc1, hc2⟩
      rwa [hXE, Subgroup.mem_bot] at h
    calc x * e = x * e * x⁻¹ * e⁻¹ * (e * x) := by group
      _ = e * x := by rw [hc, one_mul]
  have h : x ∈ X ⊓ E := ⟨hx, hxE⟩
  rwa [hXE] at h

theorem not_abelian (hD : TmOverData G E m N₀) {H N : Subgroup G}
    (hMH : Subgroup.normalizer (E : Set G) < H) (hNH : N ≤ H)
    (hNn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) (hN1 : N ≠ ⊥)
    (hmin : ∀ N' : Subgroup G, N' ≤ N → (∀ h ∈ H, ∀ x ∈ N', h * x * h⁻¹ ∈ N') → N' = ⊥ ∨ N' = N)
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : False := by
  classical
  have hcard1 : Nat.card N ≠ 1 := fun h => hN1 (Subgroup.card_eq_one.mp h)
  set p := (Nat.card N).minFac with hp
  have hpp : p.Prime := Nat.minFac_prime hcard1
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := N) p (Nat.minFac_dvd _)
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ N ∧ x ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨N.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hab a ha.1 b hb.1) p), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨N.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩN : Ω ≤ N := fun x hx => hx.1
  have hΩn : ∀ h ∈ H, ∀ x ∈ Ω, h * x * h⁻¹ ∈ Ω := fun h hh x hx =>
    ⟨hNn h hh x hx.1, by rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩
  have hΩ1 : Ω ≠ ⊥ := by
    intro h
    have hmem : (x₀ : G) ∈ Ω := ⟨x₀.2, by
      have h1 := pow_orderOf_eq_one x₀
      rw [hx₀] at h1
      simpa using congrArg Subtype.val h1⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : x₀ = 1 := Subtype.ext hmem
    rw [h1, orderOf_one] at hx₀
    exact hpp.ne_one hx₀.symm
  have hΩeq : Ω = N := (hmin Ω hΩN hΩn).resolve_left hΩ1
  have hexp : ∀ x ∈ N, x ^ p = 1 := fun x hx => (hΩeq ▸ hx : x ∈ Ω).2
  have hNp : IsPGroup p N := fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  by_cases hp3 : p = 3
  ·
    have hHM := tmNormP_overgroup_le_normalizer 3 E hD.isPGroup hD.ne_bot hD.comm hD.cent hD.irr
      hD.syl H N hMH.le hNH hNn (hp3 ▸ hNp) hN1
    exact lt_irrefl _ (lt_of_lt_of_le hMH hHM)
  · have hcop3 : Nat.Coprime p 3 := (Nat.coprime_primes hpp Nat.prime_three).mpr hp3
    have hNE : N ⊓ E = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hexp x hx.1)
      have h2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hD.elem.2 x hx.2)
      have h3 := Nat.dvd_gcd h1 h2
      rw [Nat.Coprime.gcd_eq_one hcop3, Nat.dvd_one] at h3
      exact orderOf_eq_one_iff.mp h3
    have hMN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (N : Set G) := fun g hg => by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact hNn g (hMH.le hg) x
      · intro hx
        have h1 := hNn g⁻¹ (H.inv_mem (hMH.le hg)) _ hx
        rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
    have hNM : N ⊓ Subgroup.normalizer (E : Set G) = ⊥ := by
      refine hD.eq_bot_of_inf_eq_bot inf_le_right
        (fun g hg x hx => ⟨hNn g (hMH.le hg) x hx.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx.2)
          (Subgroup.inv_mem _ hg)⟩) ?_
      rw [inf_assoc, inf_eq_right.mpr (Subgroup.le_normalizer : E ≤ _), hNE]
    have hdvd : Nat.card N ∣ Nat.card G / Nat.card (Subgroup.normalizer (E : Set G)) :=
      Nat.dvd_div_of_mul_dvd (by rw [mul_comm]; exact tmOver_card_mul_dvd hMN hNM)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hNp
    have hlt : Nat.card N < 2 ^ N₀ := hD.idx _ hdvd (by
      rcases hpp.eq_two_or_odd' with h2 | hodd
      · right; exact ⟨k, by rw [hk, h2]⟩
      · left; rw [hk]; exact hodd.pow)
    obtain ⟨φ, -, hfun⟩ := hD.frame
    have hEV : E ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer.trans hMN
    have hcopNE : Nat.Coprime (Nat.card N) (Nat.card E) := by
      rw [hk, hD.card]; exact Nat.Coprime.pow _ _ hcop3
    have hsolv : Group.IsSolvable N := by
      haveI : IsMulCommutative N := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
      infer_instance
    have hfix : N ⊓ Subgroup.centralizer (E : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : x ∈ N ⊓ E := ⟨hx.1, hD.centralizer_le hx.2⟩
      rwa [hNE] at h1
    let P : Subgroup E → Prop := fun K =>
      Nat.card (N ⊓ Subgroup.centralizer ((K.map E.subtype : Subgroup G) : Set G) :
        Subgroup G) ≠ 1
    have hPinv : ∀ g : Subgroup.normalizer (E : Set G), ∀ K, P K →
        P (K.map (E.normalizerMonoidHom g).toMonoidHom) := by
      intro g K hK
      change Nat.card (N ⊓ Subgroup.centralizer
        (((K.map (E.normalizerMonoidHom g).toMonoidHom).map E.subtype : Subgroup G) : Set G) :
          Subgroup G) ≠ 1
      rw [tmOver_map_normalizerMonoidHom, tmOver_card_conj fun x =>
        Subgroup.mem_normalizer_iff.mp (hMN g.2) x]
      exact hK
    obtain ⟨c, hc0, hPc⟩ := tmOver_exists_ne_one hEV φ hD.one_le hcopNE hsolv hfix hN1
    have hcnt := hfun P hPinv c hc0 hPc
    have h4 := tmOver_four_pow_le hEV φ hD.one_le hcopNE hsolv hfix
    have hset : {c | c ≠ 0 ∧ P (tmKer φ c)} =
        ↑(Finset.univ.filter fun c : Fin m → ZMod 3 => c ≠ 0 ∧ P (tmKer φ c)) := by
      ext c
      simp
    rw [hset, Set.ncard_coe_finset] at hcnt
    have h5 : (2 ^ N₀) ^ 2 ≤ Nat.card N ^ 2 := by
      calc (2 ^ N₀) ^ 2 = 4 ^ N₀ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 4 ^ (Finset.univ.filter fun c : Fin m → ZMod 3 => c ≠ 0 ∧ P (tmKer φ c)).card :=
          Nat.pow_le_pow_right (by norm_num) hcnt
        _ ≤ Nat.card N ^ 2 := h4
    have h6 : 2 ^ N₀ ≤ Nat.card N := (Nat.pow_le_pow_iff_left (by norm_num)).mp h5
    omega

theorem inf_ne_bot (hD : TmOverData G E m N₀) {H N : Subgroup G}
    (hMH : Subgroup.normalizer (E : Set G) < H) (hNH : N ≤ H)
    (hNn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) (hN1 : N ≠ ⊥)
    (hmin : ∀ N' : Subgroup G, N' ≤ N → (∀ h ∈ H, ∀ x ∈ N', h * x * h⁻¹ ∈ N') → N' = ⊥ ∨ N' = N)
    (hnab : ¬ ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : N ⊓ E ≠ ⊥ := by
  intro hNE
  classical
  have hMN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (N : Set G) :=
    hMH.le.trans (tmOver_le_normalizer hNn)
  have hNM : N ⊓ Subgroup.normalizer (E : Set G) = ⊥ := by
    refine hD.eq_bot_of_inf_eq_bot inf_le_right
      (fun g hg x hx => ⟨hNn g (hMH.le hg) x hx.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx.2)
        (Subgroup.inv_mem _ hg)⟩) ?_
    rw [inf_assoc, inf_eq_right.mpr (Subgroup.le_normalizer : E ≤ _), hNE]
  have hdvd : Nat.card N ∣ Nat.card G / Nat.card (Subgroup.normalizer (E : Set G)) :=
    Nat.dvd_div_of_mul_dvd (by rw [mul_comm]; exact tmOver_card_mul_dvd hMN hNM)
  have h3N : ¬ 3 ∣ Nat.card N := fun h => hD.idx3 (h.trans hdvd)
  have hfix : N ⊓ Subgroup.centralizer (E : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ N ⊓ E := ⟨hx.1, hD.centralizer_le hx.2⟩
    rwa [hNE] at h1
  have h2N : 2 ∣ Nat.card N := by
    by_contra h2
    exact hnab (tmOver_comm_of_solvable hNn hN1 hmin
      (CFSG.FeitThompson.isSolvable_of_odd_natCard N (Nat.odd_iff.mpr (by omega))))
  have hEN : E ≤ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer.trans hMN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPinv⟩ := by
    letI := CFSG.Walter.J1.conjAct E N hEN
    exact CFSG.DisconnectedInvolutionGraph.Helpers.coprime_pgroup_exists_invariant_sylow
      (A := E) (G := N) 3 2 hD.isPGroup h3N
  set Q : Subgroup G := (P : Subgroup N).map N.subtype with hQ
  have hQN : Q ≤ N := Subgroup.map_subtype_le _
  have key : ∀ e ∈ E, ∀ x ∈ Q, e * x * e⁻¹ ∈ Q := by
    rintro e he _ ⟨y, hy, rfl⟩
    exact ⟨_, hPinv ⟨e, he⟩ y hy, rfl⟩
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key e he x
    · intro hx
      have h1 := key e⁻¹ (E.inv_mem he) _ hx
      rwa [show e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x by group] at h1
  have hQ2 : IsPGroup 2 Q := P.isPGroup'.map N.subtype
  have hQ1 : Q ≠ ⊥ := by
    intro h
    apply P.ne_bot_of_dvd_card h2N
    rw [eq_bot_iff]
    intro y hy
    have h1 : (y : G) ∈ Q := ⟨y, hy, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  have hQsolv : Group.IsSolvable Q := by
    haveI := hQ2.isNilpotent
    infer_instance
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQ2
  have hcopQE : Nat.Coprime (Nat.card Q) (Nat.card E) := by
    rw [ha, hD.card]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have hfixQ : Q ⊓ Subgroup.centralizer (E : Set G) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hQN).trans hfix.le)
  have hQlt : Nat.card Q < 2 ^ N₀ :=
    hD.idx _ ((Subgroup.card_dvd_of_le hQN).trans hdvd) (Or.inr ⟨a, ha⟩)
  obtain ⟨φ, -, hfun⟩ := hD.frame
  let Pr : Subgroup E → Prop := fun K =>
    2 ∣ Nat.card (N ⊓ Subgroup.centralizer ((K.map E.subtype : Subgroup G) : Set G) : Subgroup G)
  have hPrinv : ∀ g : Subgroup.normalizer (E : Set G), ∀ K, Pr K →
      Pr (K.map (E.normalizerMonoidHom g).toMonoidHom) := by
    intro g K hK
    change 2 ∣ Nat.card (N ⊓ Subgroup.centralizer
      (((K.map (E.normalizerMonoidHom g).toMonoidHom).map E.subtype : Subgroup G) : Set G) :
        Subgroup G)
    rw [tmOver_map_normalizerMonoidHom, tmOver_card_conj fun x =>
      Subgroup.mem_normalizer_iff.mp (hMN g.2) x]
    exact hK
  obtain ⟨c, hc0, hQc⟩ := tmOver_exists_ne_one hEQ φ hD.one_le hcopQE hQsolv hfixQ hQ1
  have hPrc : Pr (tmKer φ c) := by
    have hle : Q ⊓ Subgroup.centralizer (((tmKer φ c).map E.subtype : Subgroup G) : Set G) ≤
        N ⊓ Subgroup.centralizer (((tmKer φ c).map E.subtype : Subgroup G) : Set G) :=
      inf_le_inf_right _ hQN
    have hp : IsPGroup 2 (Q ⊓ Subgroup.centralizer
        (((tmKer φ c).map E.subtype : Subgroup G) : Set G) : Subgroup G) :=
      hQ2.to_le inf_le_left
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hp
    have h2' : 2 ∣ Nat.card (Q ⊓ Subgroup.centralizer
        (((tmKer φ c).map E.subtype : Subgroup G) : Set G) : Subgroup G) := by
      rw [hb] at hQc ⊢
      rcases b with _ | b
      · exact absurd rfl hQc
      · exact dvd_pow_self 2 (Nat.succ_ne_zero b)
    exact h2'.trans (Subgroup.card_dvd_of_le hle)
  have hcnt := hfun Pr hPrinv c hc0 hPrc
  have hincl : ∀ c : Fin m → ZMod 3, Pr (tmKer φ c) →
      Nat.card (Q ⊓ Subgroup.centralizer (((tmKer φ c).map E.subtype : Subgroup G) : Set G) :
        Subgroup G) ≠ 1 := fun c hc =>
    tmOver_sylow_fixed_ne_one hEN hD.isPGroup h3N P key (tmKer φ c) hc
  have h4 := tmOver_four_pow_le hEQ φ hD.one_le hcopQE hQsolv hfixQ
  have hsub : (Finset.univ.filter fun c : Fin m → ZMod 3 => c ≠ 0 ∧ Pr (tmKer φ c)) ⊆
      (Finset.univ.filter fun c : Fin m → ZMod 3 => c ≠ 0 ∧
        Nat.card (Q ⊓ Subgroup.centralizer (((tmKer φ c).map E.subtype : Subgroup G) : Set G) :
          Subgroup G) ≠ 1) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hc.1, hincl c hc.2⟩
  have hset : {c | c ≠ 0 ∧ Pr (tmKer φ c)} =
      ↑(Finset.univ.filter fun c : Fin m → ZMod 3 => c ≠ 0 ∧ Pr (tmKer φ c)) := by
    ext c
    simp
  rw [hset, Set.ncard_coe_finset] at hcnt
  have h5 : (2 ^ N₀) ^ 2 ≤ Nat.card Q ^ 2 := by
    calc (2 ^ N₀) ^ 2 = 4 ^ N₀ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ 4 ^ (Finset.univ.filter fun c : Fin m → ZMod 3 => c ≠ 0 ∧ Pr (tmKer φ c)).card :=
        Nat.pow_le_pow_right (by norm_num) hcnt
      _ ≤ 4 ^ (Finset.univ.filter fun c : Fin m → ZMod 3 => c ≠ 0 ∧
          Nat.card (Q ⊓ Subgroup.centralizer (((tmKer φ c).map E.subtype : Subgroup G) : Set G) :
            Subgroup G) ≠ 1).card :=
        Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card hsub)
      _ ≤ Nat.card Q ^ 2 := h4
  have h6 : 2 ^ N₀ ≤ Nat.card Q := (Nat.pow_le_pow_iff_left (by norm_num)).mp h5
  omega

theorem isSimpleGroup_of_le (hD : TmOverData G E m N₀) {H N : Subgroup G}
    (hMH : Subgroup.normalizer (E : Set G) < H) (hNH : N ≤ H)
    (hNn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) (hN1 : N ≠ ⊥)
    (hmin : ∀ N' : Subgroup G, N' ≤ N → (∀ h ∈ H, ∀ x ∈ N', h * x * h⁻¹ ∈ N') → N' = ⊥ ∨ N' = N)
    (hnab : ¬ ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hEN : E ≤ N) : IsSimpleGroup N := by
  classical
  set M := Subgroup.normalizer (E : Set G) with hM
  have hNsub : (N.subgroupOf H).Normal := ⟨fun x hx h => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hNn h h.2 x hx⟩
  have hminsub : ∀ M' : Subgroup G, M' ≤ N → (M'.subgroupOf H).Normal → M' = ⊥ ∨ M' = N := by
    intro M' hM'N hM'n
    refine hmin M' hM'N fun h hh x hx => ?_
    have h1 := hM'n.conj_mem ⟨x, hNH (hM'N hx)⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨h, hh⟩
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨r, T, hr, hsup, hcomm, hind, hsimp, hconj, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.SteinbergCH.minimal_normal_subgroupOf_factors hNH hNsub hN1
      hminsub
  by_cases hr1 : r = 1
  · subst hr1
    have hN : N = T 0 := by rw [← hsup, iSup_unique]; rfl
    rw [hN]
    exact hsimp 0
  exfalso
  have hr2 : 2 ≤ r := by omega
  let Φ := Subgroup.noncommPiCoprod hcomm
  have hΦinj : Function.Injective Φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hΦrange : Φ.range = N := by rw [Subgroup.noncommPiCoprod_range, hsup]
  have hdecomp : ∀ e ∈ E, ∃ x, Φ x = e := fun e he => by
    have h1 : e ∈ Φ.range := hΦrange ▸ hEN he
    exact h1
  have hcompE : ∀ x, Φ x ∈ E → ∀ i, ((x i : T i) : G) ∈ E := by
    intro x hx i
    refine hD.mem_of_commute fun e' he' => ?_
    obtain ⟨y, rfl⟩ := hdecomp e' he'
    have hxy : x * y = y * x := hΦinj (by rw [map_mul, map_mul]; exact hD.comm _ hx _ he')
    exact tmOver_comp_commute hcomm hxy i
  have hTne : ∀ i, T i ≠ ⊥ := fun i h => by
    haveI := hsimp i
    obtain ⟨a, b, hab⟩ := exists_pair_ne (T i)
    exact hab (Subtype.ext ((Subgroup.mem_bot.mp (h.le a.2)).trans
      (Subgroup.mem_bot.mp (h.le b.2)).symm))
  have hEi : ∀ i, E ⊓ T i ≠ ⊥ := by
    intro i h
    apply hTne i
    have hTC : T i ≤ Subgroup.centralizer (E : Set G) := fun t ht => by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      obtain ⟨x, rfl⟩ := hdecomp e he
      have hxi : x i = 1 := by
        have h1 : ((x i : T i) : G) ∈ E ⊓ T i := ⟨hcompE x he i, (x i).2⟩
        rw [h, Subgroup.mem_bot] at h1
        exact Subtype.ext h1
      exact tmOver_commute_of_comp_one hcomm hxi ht
    rw [eq_bot_iff]
    intro t ht
    have h1 : t ∈ E ⊓ T i := ⟨hD.centralizer_le (hTC ht), ht⟩
    rwa [h] at h1
  have hTnab : ∀ i, ¬ ∀ x ∈ T i, ∀ y ∈ T i, x * y = y * x := by
    intro i hab
    apply hnab
    have hall : ∀ j, ∀ x ∈ T j, ∀ y ∈ T j, x * y = y * x := by
      intro j
      obtain ⟨g, -, hg⟩ := hconj i j
      rw [hg]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (x * y) * g⁻¹⁻¹ by group, hab x hx y hy]
      group
    have hle : ∀ j, (⨆ k, T k) ≤ Subgroup.centralizer (T j : Set G) := fun j =>
      iSup_le fun k t ht =>
        Subgroup.mem_centralizer_iff.mpr fun s hs => by
          by_cases hkj : k = j
          · subst hkj
            exact hall k s hs t ht
          · exact ((hcomm hkj t s ht hs).eq).symm
    have hNC : N ≤ Subgroup.centralizer (N : Set G) := by
      rw [← hsup]
      exact iSup_le fun j => (Subgroup.le_centralizer_iff.mpr (hle j))
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hNC hy) x hx)
  have hMN : M ≤ Subgroup.normalizer (N : Set G) := hMH.le.trans (tmOver_le_normalizer hNn)
  have hperm : ∀ g ∈ M, ∀ i, ∃ j, (T i).map (MulAut.conj g).toMonoidHom = T j := by
    intro g hg i
    haveI := hsimp i
    haveI : IsSimpleGroup ((T i).map (MulAut.conj g).toMonoidHom) :=
      ((T i).equivMapOfInjective _ (MulAut.conj g).injective).symm.isSimpleGroup
    refine tmOver_eq_factor hcomm hsimp ?_ ?_ ?_
    · rw [hsup]
      rintro _ ⟨t, ht, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hMN hg) t).mp (hsup ▸ le_iSup T i ht)
    · rw [hsup]
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hgn : g⁻¹ * n * g ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (hMN (M.inv_mem hg)) n).mp hn
        rwa [inv_inv] at this
      have hTi := tmOver_iSup_le_normalizer hcomm i (hsup.symm ▸ hgn)
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨(g⁻¹ * n * g) * t * (g⁻¹ * n * g)⁻¹,
          (Subgroup.mem_normalizer_iff.mp hTi t).mp ht, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨t, ht, hty⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hty
        refine ⟨(g⁻¹ * n * g)⁻¹ * t * (g⁻¹ * n * g)⁻¹⁻¹, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp ((tmOver_iSup_le_normalizer hcomm i)
            (hsup.symm ▸ N.inv_mem hgn)) t).mp ht
          exact this
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [show y = n⁻¹ * (n * y * n⁻¹) * n by group, ← hty]
          group
    · rintro hab
      apply hTnab i
      intro x hx y hy
      have h1 := hab _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      have h2 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group, h1]
        group
      simpa using h2
  set i₀ : Fin r := ⟨0, hr⟩
  set O : Finset (Fin r) :=
    Finset.univ.filter fun j => ∃ g ∈ M, (T i₀).map (MulAut.conj g).toMonoidHom = T j with hO
  have hi₀O : i₀ ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ _, 1, M.one_mem, by
    rw [map_one]; exact Subgroup.map_id _⟩
  have hOtrans : ∀ g ∈ M, ∀ j ∈ O, ∃ j' ∈ O, (T j).map (MulAut.conj g).toMonoidHom = T j' := by
    intro g hg j hj
    obtain ⟨j', hj'⟩ := hperm g hg j
    refine ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj'⟩
    obtain ⟨g₀, hg₀, hgj⟩ := (Finset.mem_filter.mp hj).2
    refine ⟨g * g₀, M.mul_mem hg hg₀, ?_⟩
    rw [← hj', ← hgj, Subgroup.map_map, map_mul]
    rfl
  have hEmap : ∀ g ∈ M, E.map (MulAut.conj g).toMonoidHom = E := fun g hg =>
    tmOver_map_conj_eq (H := M) (fun h hh x hx => (Subgroup.mem_normalizer_iff.mp hh x).mp hx) hg
  let X : Set E := {e | e ≠ 1 ∧ ∃ j ∈ O, (e : G) ∈ T j}
  have hXinv : ∀ g : Subgroup.normalizer (E : Set G), ∀ x ∈ X, E.normalizerMonoidHom g x ∈ X := by
    rintro g x ⟨hx1, j, hj, hxj⟩
    refine ⟨fun h => hx1 ((E.normalizerMonoidHom g).injective (h.trans (map_one _).symm)), ?_⟩
    obtain ⟨j', hj', hjj'⟩ := hOtrans g g.2 j hj
    refine ⟨j', hj', ?_⟩
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ← hjj']
    exact ⟨x, hxj, rfl⟩
  obtain ⟨φ, hvec, -⟩ := hD.frame
  obtain ⟨⟨e₀, he₀⟩, he₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hEi i₀)
  have he₀ne : e₀ ≠ 1 := fun h => he₀1 (Subtype.ext h)
  have he₀X : (⟨e₀, he₀.1⟩ : E) ∈ X := ⟨fun h => he₀ne (congrArg Subtype.val h),
    i₀, hi₀O, he₀.2⟩
  have hXlow := hvec X hXinv _ he₀X fun h => he₀ne (congrArg Subtype.val h)
  have hcardO : ∀ j ∈ O, Nat.card (E ⊓ T j : Subgroup G) = Nat.card (E ⊓ T i₀ : Subgroup G) := by
    intro j hj
    obtain ⟨g, hg, hgj⟩ := (Finset.mem_filter.mp hj).2
    have h1 : E ⊓ T j = (E ⊓ T i₀).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hEmap g hg, hgj]
    rw [h1, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  obtain ⟨d, hd⟩ : ∃ d, Nat.card (E ⊓ T i₀ : Subgroup G) = 3 ^ d := by
    have h1 : Nat.card (E ⊓ T i₀ : Subgroup G) ∣ 3 ^ m :=
      hD.card ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    exact ⟨d, hd⟩
  have hXup : X.ncard ≤ O.card * (3 ^ d - 1) := by
    let Y : Fin r → Set E := fun j => (((E ⊓ T j).subgroupOf E : Subgroup E) : Set E) \ {1}
    have hXY : X ⊆ ⋃ j ∈ O, Y j := by
      rintro x ⟨hx1, j, hj, hxj⟩
      exact Set.mem_biUnion hj ⟨Subgroup.mem_subgroupOf.mpr ⟨x.2, hxj⟩, hx1⟩
    have hY : ∀ j ∈ O, (Y j).ncard = 3 ^ d - 1 := by
      intro j hj
      have h1 : (((E ⊓ T j).subgroupOf E : Subgroup E) : Set E).ncard = 3 ^ d := by
        rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, ← hd, ← hcardO j hj,
          ← Subgroup.card_map_of_injective E.subtype_injective, Subgroup.subgroupOf_map_subtype,
          inf_assoc, inf_comm (T j) E, ← inf_assoc, inf_idem]
      rw [Set.ncard_diff_singleton_of_mem ((E ⊓ T j).subgroupOf E).one_mem, h1]
    calc X.ncard ≤ (⋃ j ∈ O, Y j).ncard := Set.ncard_le_ncard hXY (Set.toFinite _)
      _ ≤ ∑ j ∈ O, (Y j).ncard := Finset.set_ncard_biUnion_le O Y
      _ = ∑ j ∈ O, (3 ^ d - 1) := Finset.sum_congr rfl hY
      _ = O.card * (3 ^ d - 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hdO : d * O.card ≤ m := by
    have hcomm' : Pairwise fun i j => ∀ x y : G, x ∈ (E ⊓ T i : Subgroup G) →
        y ∈ (E ⊓ T j : Subgroup G) → Commute x y :=
      fun i j hij x y hx hy => hcomm hij x y hx.2 hy.2
    have hind' : iSupIndep fun j => (E ⊓ T j : Subgroup G) :=
      hind.mono fun j => inf_le_right
    have hinj' := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm') hind'
    have hrange : (Subgroup.noncommPiCoprod hcomm').range ≤ E := by
      rw [Subgroup.noncommPiCoprod_range]
      exact iSup_le fun j => inf_le_left
    have h1 : ∏ j, Nat.card (E ⊓ T j : Subgroup G) ≤ 3 ^ m := by
      rw [← hD.card, ← Nat.card_pi]
      calc Nat.card ((j : Fin r) → (E ⊓ T j : Subgroup G))
          = Nat.card (Subgroup.noncommPiCoprod hcomm').range :=
            Nat.card_congr (Equiv.ofInjective _ hinj')
        _ ≤ Nat.card E := Subgroup.card_le_of_le hrange
    have h2 : (3 ^ d) ^ O.card ≤ ∏ j, Nat.card (E ⊓ T j : Subgroup G) := by
      calc (3 ^ d) ^ O.card = ∏ j ∈ O, Nat.card (E ⊓ T j : Subgroup G) := by
            rw [Finset.prod_congr rfl fun j hj => by rw [hcardO j hj, hd], Finset.prod_const]
        _ ≤ ∏ j, Nat.card (E ⊓ T j : Subgroup G) :=
            Finset.prod_le_prod_of_subset_of_one_le' (Finset.subset_univ O)
              fun j _ _ => Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    rw [← pow_mul] at h2
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h2.trans h1)
  have hO2 : 2 ≤ O.card := by
    by_contra hlt
    have hO1 : O = {i₀} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hi₀O, fun j hj => by
        by_contra hne
        have : ({i₀, j} : Finset (Fin r)) ⊆ O := by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hi₀O
          · exact hj
        have h2 := Finset.card_le_card this
        rw [Finset.card_pair (Ne.symm hne)] at h2
        omega⟩
    have hinv : ∀ g ∈ M, ∀ f ∈ E ⊓ T i₀, g * f * g⁻¹ ∈ E ⊓ T i₀ := by
      intro g hg f hf
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg f).mp hf.1, ?_⟩
      obtain ⟨j', hj', hjj'⟩ := hOtrans g hg i₀ hi₀O
      rw [hO1, Finset.mem_singleton] at hj'
      rw [← hj', ← hjj']
      exact ⟨f, hf.2, rfl⟩
    rcases hD.irr _ inf_le_left hinv with h | h
    · exact hEi i₀ h
    · have hET : E ≤ T i₀ := h ▸ inf_le_right
      obtain ⟨j₁, hj₁⟩ : ∃ j₁ : Fin r, j₁ ≠ i₀ := ⟨⟨1, by omega⟩, by
        intro h; simp [i₀, Fin.ext_iff] at h⟩
      apply hEi j₁
      have hdis := hind.pairwiseDisjoint hj₁
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.disjoint_def.mp hdis) hx.2 (hET hx.1)
  have := hD.dec O.card d hO2 hdO
  omega

theorem exists_simple_normal (hD : TmOverData G E m N₀) {H : Subgroup G}
    (hMH : Subgroup.normalizer (E : Set G) < H) :
    ∃ J : Subgroup G, J ≤ H ∧ (J.subgroupOf H).Normal ∧ IsSimpleGroup J ∧
      (∃ a b : J, a * b ≠ b * a) ∧ ∀ h ∈ H, (∀ j ∈ J, h * j = j * h) → h = 1 := by
  have hH : H ≠ ⊥ := fun h => hD.ne_bot (eq_bot_iff.mpr
    ((Subgroup.le_normalizer).trans (h ▸ hMH.le)))
  obtain ⟨N, hNH, hNn, hN1, hmin⟩ := tmOver_exists_minNormal hH
  have hnab : ¬ ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun hab =>
    hD.not_abelian hMH hNH hNn hN1 hmin hab
  have hEN : E ≤ N := by
    rcases hD.irr (N ⊓ E) inf_le_right (fun g hg x hx =>
      ⟨hNn g (hMH.le hg) x hx.1, (Subgroup.mem_normalizer_iff.mp hg x).mp hx.2⟩) with h | h
    · exact absurd h (hD.inf_ne_bot hMH hNH hNn hN1 hmin hnab)
    · exact h ▸ inf_le_left
  haveI hsimp := hD.isSimpleGroup_of_le hMH hNH hNn hN1 hmin hnab hEN
  refine ⟨N, hNH, ⟨fun x hx h => ?_⟩, hsimp, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hNn h h.2 x hx
  · by_contra hno
    push Not at hno
    exact hnab fun x hx y hy => congrArg Subtype.val (hno ⟨x, hx⟩ ⟨y, hy⟩)
  · intro h hh hc
    let C : Subgroup G := H ⊓ Subgroup.centralizer (N : Set G)
    have hCE : C ≤ E := fun c hc => hD.mem_of_commute fun e he =>
      ((Subgroup.mem_centralizer_iff.mp hc.2) e (hEN he)).symm
    have hCn : ∀ h' ∈ H, ∀ x ∈ C, h' * x * h'⁻¹ ∈ C := by
      intro h' hh' x hx
      refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh' hx.1) (H.inv_mem hh'), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hn' : h'⁻¹ * n * h' ∈ N := by
        have := hNn h'⁻¹ (H.inv_mem hh') n hn
        rwa [inv_inv] at this
      have hx' := (Subgroup.mem_centralizer_iff.mp hx.2) _ hn'
      calc n * (h' * x * h'⁻¹) = h' * ((h'⁻¹ * n * h') * x) * h'⁻¹ := by group
        _ = h' * (x * (h'⁻¹ * n * h')) * h'⁻¹ := by rw [hx']
        _ = h' * x * h'⁻¹ * n := by group
    have hC3 : IsPGroup 3 C := hD.isPGroup.to_le hCE
    by_contra hh1
    have hC1 : C ≠ ⊥ := fun hC => hh1 (by
      have hmem : h ∈ C := ⟨hh, Subgroup.mem_centralizer_iff.mpr fun j hj => (hc j hj).symm⟩
      rw [hC] at hmem
      exact hmem)
    have hHM := tmNormP_overgroup_le_normalizer 3 E hD.isPGroup hD.ne_bot hD.comm hD.cent hD.irr
      hD.syl H C hMH.le inf_le_left hCn hC3 hC1
    exact lt_irrefl _ (lt_of_lt_of_le hMH hHM)

end TmOverData

end CFSG.StandardType.FrameRoute

end
