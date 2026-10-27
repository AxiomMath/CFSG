module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCLie
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCNotStrong
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63General
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 KStrongEmbedded72)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R72 R76Sig)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (R6_14 R6_38)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
  (SigmaStd not_solvable_of_mem_calC sp_of_mem_sig le_pRank')

@[expose] def LieOutCyclicInput : Prop :=
  (∀ (K : Type) [Group K] [Finite K] (p f : ℕ), LieModel K .G2 0 p f → p ≠ 3 →
      IsCyclic (Outer K)) ∧
    (∀ (K : Type) [Group K] [Finite K] (p f : ℕ), LieModel K .trialityD4 0 p f →
      IsCyclic (Outer K)) ∧
    (∀ (K : Type) [Group K] [Finite K] (f : ℕ), LieModel K .twistedF4 0 2 f →
      IsCyclic (Outer K))

theorem normalizer_le_of_r858_of_isSimpleGroup {G : Type} [Group G] [Finite G] {D : Data G}
    (h858 : R858 D) {L Q P : Subgroup G} (hc : Cex856 D L Q P) (hS : IsSimpleGroup (Bar2 L)) :
    D.M ≤ normalizer (L : Set G) := by
  rcases h858 L Q P hc with h | ⟨-, hcl⟩
  · exact h
  · exfalso
    obtain ⟨hq, h3⟩ : IsQuasisimple (Bar2 L) ∧ Nat.card (Subgroup.center (Bar2 L)) = 3 := by
      rcases hcl with ⟨hq, h3, -⟩ | ⟨hq, h3, -⟩ | ⟨hq, h3, -⟩ <;> exact ⟨hq, h3⟩
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center (Bar2 L)) with h | h
    · rw [h, Subgroup.card_bot] at h3
      omega
    · obtain ⟨-, hsimple, -⟩ := hq
      have := hsimple.toNontrivial
      have hsub : Subsingleton (Bar2 L ⧸ Subgroup.center (Bar2 L)) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton _ hsub

theorem exists_sigma_prime_pRank_le_one {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (h72 : R72 D) (hKF7 : KStrongEmbedded72)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L)
    (hS : IsSimpleGroup (Bar2 L)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∈ D.sig ∧ IsStronglyPEmbedded p D.M ∧
      3 ≤ CFSG.Open.pRank p D.M ∧ CFSG.Open.pRank p L ≤ 1 := by
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hpr := D.sig_prime p hp
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hX.cex.mem
  have hsp : IsStronglyPEmbedded p D.M := sp_of_mem_sig hSg hns hp
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hX.cex.notStrong hsp
  have hp3' : 3 < p := by
    have := hpr.1.two_le
    omega
  refine ⟨p, hpr.1, hp3', hp, hsp, hSg.three_le p hp, ?_⟩
  by_contra h
  exact not_stronglyEmbedded_of_choiceX_of_leaves h72 hKF7 hX hLX hS hpr.1 hp3' (by omega) hsp

private theorem k1471t1_center_eq_bot {K : Type} [Group K] (hS : IsSimpleGroup K)
    (hperf : commutator K = ⊤) : Subgroup.center K = ⊥ := by
  rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : K, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a
    have : Group.IsSolvable K := Group.isSolvable_of_comm hc
    have := hS.toNontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial K).ne hperf

private theorem k1471t1_conj_injective {K : Type} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  have hmem : a ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := DFunLike.congr_fun ha g
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rw [hZ] at hmem
  exact hmem

private theorem k1471t1_coprime_orderOf {G H : Type} [Group G] [Group H] [IsMulCommutative H]
    {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hOp : UC22.F10.OpRes p M = M) (φ : ↥M →* H)
    {g : G} (hg : g ∈ M) : Nat.Coprime (orderOf (φ ⟨g, hg⟩)) p := by
  have hg' : g ∈ Subgroup.closure {x : G | x ∈ M ∧ ¬ p ∣ orderOf x} := by
    have h : g ∈ UC22.F10.OpRes p M := by
      rw [hOp]
      exact hg
    exact h
  have key : ∃ hgM : g ∈ M, Nat.Coprime (orderOf (φ ⟨g, hgM⟩)) p := by
    refine Subgroup.closure_induction
      (p := fun g _ => ∃ hgM : g ∈ M, Nat.Coprime (orderOf (φ ⟨g, hgM⟩)) p) ?_ ?_ ?_ ?_ hg'
    · rintro x ⟨hxM, hxp⟩
      refine ⟨hxM, ?_⟩
      have h1 : orderOf (φ ⟨x, hxM⟩) ∣ orderOf x := by
        have h := orderOf_map_dvd φ ⟨x, hxM⟩
        rwa [Subgroup.orderOf_mk] at h
      exact Nat.Coprime.coprime_dvd_left h1 (hp.coprime_iff_not_dvd.2 hxp).symm
    · refine ⟨M.one_mem, ?_⟩
      rw [show (⟨1, M.one_mem⟩ : ↥M) = 1 from rfl, map_one, orderOf_one]
      exact Nat.coprime_one_left p
    · rintro x y - - ⟨hxM, hx⟩ ⟨hyM, hy⟩
      refine ⟨M.mul_mem hxM hyM, ?_⟩
      have h : φ ⟨x * y, M.mul_mem hxM hyM⟩ = φ ⟨x, hxM⟩ * φ ⟨y, hyM⟩ := by
        rw [← map_mul]
        rfl
      rw [h]
      exact Nat.Coprime.coprime_dvd_left
        (Commute.orderOf_mul_dvd_mul_orderOf (mul_comm' (φ ⟨x, hxM⟩) (φ ⟨y, hyM⟩)))
        (Nat.Coprime.mul_left hx hy)
    · rintro x - ⟨hxM, hx⟩
      refine ⟨M.inv_mem hxM, ?_⟩
      have h : φ ⟨x⁻¹, M.inv_mem hxM⟩ = (φ ⟨x, hxM⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [h, orderOf_inv]
      exact hx
  obtain ⟨_, h⟩ := key
  exact h

private theorem k1471t1_hom_eq_one {G H : Type} [Group G] [Group H] [IsMulCommutative H]
    {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hOp : UC22.F10.OpRes p M = M) (φ : ↥M →* H)
    {x : G} (hx : x ∈ M) (hxp : x ^ p = 1) : φ ⟨x, hx⟩ = 1 := by
  have h1 : (φ ⟨x, hx⟩) ^ p = 1 := by
    rw [← map_pow]
    have h : (⟨x, hx⟩ : ↥M) ^ p = 1 := Subtype.ext hxp
    rw [h, map_one]
  exact orderOf_eq_one_iff.mp
    ((k1471t1_coprime_orderOf hp hOp φ hx).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one h1))

private theorem k1471t1_mem_inner {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hMN : M ≤ normalizer (L : Set G)) {p : ℕ} (hp : p.Prime)
    (hOp : UC22.F10.OpRes p M = M) (hOut : IsCyclic (Outer (Bar2 L))) {x : G} (hx : x ∈ M)
    (hxp : x ^ p = 1) :
    barAction L ⟨x, hMN hx⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) := by
  have := hOut
  let φ : ↥M →* Outer (Bar2 L) :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
      ((barAction L).comp (Subgroup.inclusion hMN))
  exact (QuotientGroup.eq_one_iff _).mp (k1471t1_hom_eq_one hp hOp φ hx hxp)

open scoped commutatorElement in
private theorem k1471t1_commutator_mem {G : Type} [Group G] {L : Subgroup G} {b : G}
    (hb : b ∈ normalizer (L : Set G)) (h1 : barAction L ⟨b, hb⟩ = 1) {y : G} (hy : y ∈ L) :
    ⁅b, y⁆ ∈ pCoreOf 2 L := by
  have h2 : barAction L ⟨b, hb⟩ (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨y, hy⟩ := by
    rw [h1]
    rfl
  rw [barAction_mk, QuotientGroup.eq_iff_div_mem, ← CFSG.mem_openPCoreOf_iff] at h2
  simpa [commutatorElement_def, Subgroup.coe_div, div_eq_mul_inv] using h2

private theorem k1471t1_card_ker_ge {A K : Type} [Group A] [Group K] [Finite A] [Finite K]
    {p : ℕ} (hp : p.Prime) (hAcomm : IsMulCommutative A) (hAexp : ∀ a : A, a ^ p = 1)
    (hAcard : Nat.card A = p ^ 3) (hconj : Function.Injective (MulAut.conj : K →* MulAut K))
    (ψ : A →* MulAut K) (hψ : ∀ a, ψ a ∈ (MulAut.conj : K →* MulAut K).range)
    (hK : ∀ E : Subgroup K, IsElemAbelian p E → ∀ k : ℕ, Nat.card E = p ^ k → k ≤ 1) :
    p ^ 2 ≤ Nat.card ψ.ker := by
  let c : K →* MulAut K := MulAut.conj
  let E : Subgroup K := ψ.range.comap c
  have hrange : ψ.range ≤ c.range := by
    rintro _ ⟨a, rfl⟩
    exact hψ a
  have hEcard : Nat.card E = Nat.card ψ.range := by
    rw [← Subgroup.card_map_of_injective hconj (K := E), Subgroup.map_comap_eq,
      inf_of_le_right hrange]
  have hEmem : ∀ x ∈ E, ∃ a : A, ψ a = c x := fun x hx =>
    MonoidHom.mem_range.mp (Subgroup.mem_comap.mp hx)
  have hEel : IsElemAbelian p E := by
    refine ⟨isMulCommutative_iff.mpr fun x y => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := hEmem x.1 x.2
      obtain ⟨b, hb⟩ := hEmem y.1 y.2
      apply Subtype.ext
      apply hconj
      show c ((x : K) * y) = c ((y : K) * x)
      rw [map_mul, map_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm' a b]
    · obtain ⟨a, ha⟩ := hEmem x hx
      apply hconj
      rw [map_pow, ← ha, ← map_pow, hAexp a, map_one, map_one]
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).1
    (hAcard ▸ Subgroup.card_range_dvd ψ : Nat.card ψ.range ∣ p ^ 3)
  have hk1 : k ≤ 1 := hK E hEel k (hEcard.trans hk)
  have hle : Nat.card ψ.range ≤ p := by
    rw [hk]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  have h3 : Nat.card ψ.ker * Nat.card ψ.range = p ^ 3 :=
    (Subgroup.card_ker_mul_card_range ψ).trans hAcard
  have h4 : p * p ^ 2 ≤ p * Nat.card ψ.ker :=
    calc p * p ^ 2 = p ^ 3 := by ring
      _ = Nat.card ψ.ker * Nat.card ψ.range := h3.symm
      _ ≤ Nat.card ψ.ker * p := Nat.mul_le_mul_left _ hle
      _ = p * Nat.card ψ.ker := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left h4 hp.pos

theorem exists_elemAbelian_sq_acting_trivially {G : Type} [Group G] [Finite G] {D : Data G}
    (h638 : R6_38 D) (h858 : R858 D) {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X)
    (hS : IsSimpleGroup (Bar2 L)) (hOut : IsCyclic (Outer (Bar2 L))) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpσ : p ∈ D.sig) (hrk : 3 ≤ CFSG.Open.pRank p D.M)
    (hL1 : CFSG.Open.pRank p L ≤ 1) :
    ∃ B : Subgroup G, B ≤ D.M ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 2 ∧
      ⁅L, B⁆ ≤ pCoreOf 2 L := by
  have hMN : D.M ≤ normalizer (L : Set G) :=
    normalizer_le_of_r858_of_isSimpleGroup h858 hX.cex hS
  have hOp : UC22.F10.OpRes p D.M = D.M := h638 p hp (by omega) (Or.inl hpσ)
  have hZ : Subgroup.center (Bar2 L) = ⊥ := k1471t1_center_eq_bot hS hX.cex.mem.2.2.1
  obtain ⟨A, hAM, hAel, hAcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hp (k := 3) hrk
  let ψ : ↥A →* MulAut (Bar2 L) := (barAction L).comp (Subgroup.inclusion (hAM.trans hMN))
  have hψ : ∀ a : ↥A, ψ a ∈ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := fun a =>
    k1471t1_mem_inner hMN hp hOp hOut (hAM a.2) (hAel.2 a a.2)
  have hK : ∀ E : Subgroup (Bar2 L), IsElemAbelian p E → ∀ k : ℕ, Nat.card E = p ^ k → k ≤ 1 := by
    intro E hE k hk
    have h1 := le_pRank' hp (le_top : E ≤ ⊤) hE hk
    have h2 := UC22.pRank_bar2_eq_of_odd (Y := L) hp (by omega : p ≠ 2)
    omega
  have hker : p ^ 2 ≤ Nat.card ψ.ker :=
    k1471t1_card_ker_ge hp hAel.1 (fun a => Subtype.ext (hAel.2 a a.2)) hAcard
      (k1471t1_conj_injective hZ) ψ hψ hK
  have hAkle : ψ.ker.map A.subtype ≤ A := Subgroup.map_subtype_le _
  obtain ⟨B, hBAk, hBel, hBcard⟩ := UC6S846.exists_card_p_sq hp (hAel.mono hAkle)
    (by rw [Subgroup.card_map_of_injective A.subtype_injective]; exact hker)
  have hBM : B ≤ D.M := hBAk.trans (hAkle.trans hAM)
  refine ⟨B, hBM, hBel, hBcard, ?_⟩
  rw [← le_centralizerBar_iff hBM]
  intro b hb
  obtain ⟨a, ha, rfl⟩ := hBAk hb
  exact mem_centralizerBar_iff.2 ⟨hAM a.2, fun y hy =>
    k1471t1_commutator_mem (hMN (hAM a.2)) ha hy⟩

private theorem k1471t2_not_dvd_relIndex {G : Type} [Group G] [Finite G] {C L : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hL : L = C ⊔ pCoreOf 2 L) (hCL : C ≤ L) :
    ¬ r ∣ C.relIndex L := by
  have hOL : pCoreOf 2 L ≤ L := CFSG.openPCoreOf_le 2 L
  have hN : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := CFSG.openPCoreOf_subgroupOf 2 L
  have htop : (CFSG.pCore 2 ↥L) ⊔ C.subgroupOf L = ⊤ := by
    rw [← hN, sup_comm, ← Subgroup.subgroupOf_sup hCL hOL, ← hL, Subgroup.subgroupOf_self]
  have hidx : C.relIndex L = (C.subgroupOf L).relIndex (CFSG.pCore 2 ↥L) := by
    have h := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (CFSG.pCore 2 ↥L)
      (C.subgroupOf L)
    rwa [htop, Subgroup.relIndex_top_right] at h
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).index
    ((C.subgroupOf L).subgroupOf (CFSG.pCore 2 ↥L))
  intro h
  rw [hidx] at h
  have h2 : r ∣ 2 ^ n := by
    rw [← hn]
    exact h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))

private theorem k1471t2_isSylowOf_of_eq_sup {G : Type} [Group G] [Finite G] {C L : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hL : L = C ⊔ pCoreOf 2 L) (hCL : C ≤ L)
    {T : Subgroup G} (hT : IsSylowOf r T C) : IsSylowOf r T L := by
  have : Fact r.Prime := ⟨hr⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT ⊢
  obtain ⟨hTC, hTr, hdvd⟩ := hT
  refine ⟨hTC.trans hCL, hTr, fun h => ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T C L hTC hCL] at h
  rcases hr.dvd_mul.1 h with h | h
  · exact hdvd h
  · exact k1471t2_not_dvd_relIndex hr hr2 hL hCL h

private theorem k1471t2_exists_sylowOf_ge {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    {r : ℕ} (hTM : T ≤ M) (hT : IsPGroup r T) :
    ∃ S : Subgroup G, IsSylowOf r S M ∧ T ≤ S := by
  obtain ⟨R, hR⟩ := (hT.comap_subtype : IsPGroup r (T.subgroupOf M)).exists_le_sylow
  exact ⟨(R : Subgroup ↥M).map M.subtype, ⟨R, rfl⟩,
    fun x hx => ⟨⟨x, hTM hx⟩, hR (Subgroup.mem_subgroupOf.2 hx), rfl⟩⟩

theorem exists_sylow_inf_le_centralizer_of_eq_sup {G : Type} [Group G] [Finite G]
    {M L B : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hLM : L ≤ M)
    (hL : L = (centralizer (B : Set G) ⊓ L) ⊔ pCoreOf 2 L) :
    ∃ S : Subgroup G, IsSylowOf r S M ∧ S ⊓ L ≤ centralizer (B : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf r (centralizer (B : Set G) ⊓ L)
  have hTL : IsSylowOf r T L := k1471t2_isSylowOf_of_eq_sup hr hr2 hL inf_le_right hT
  obtain ⟨S, hS, hTS⟩ := k1471t2_exists_sylowOf_ge (hTL.le.trans hLM) hTL.isPGroup
  refine ⟨S, hS, ?_⟩
  have h : S ⊓ L = T := hTL.eq_of_le (le_inf hTS hTL.le) inf_le_right
    (hS.isPGroup.to_inf_left)
  rw [h]
  exact hT.le.trans inf_le_left

theorem exists_sigma_ep2_centralizing_sylow_inf {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (h638 : R6_38 D) (h858 : R858 D) (h72 : R72 D) (hKF7 : KStrongEmbedded72)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L)
    (hS : IsSimpleGroup (Bar2 L)) (hOut : IsCyclic (Outer (Bar2 L))) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) :
    ∃ (S B : Subgroup G) (p : ℕ), IsSylowOf r S D.M ∧ p.Prime ∧ p ∈ D.sig ∧ B ≤ D.M ∧
      IsElemAbelian p B ∧ Nat.card B = p ^ 2 ∧ S ⊓ L ≤ centralizer (B : Set G) := by
  obtain ⟨p, hp, hp3, hpσ, -, hrk, hL1⟩ :=
    exists_sigma_prime_pRank_le_one hSg h72 hKF7 hX hLX hS
  obtain ⟨B, hBM, hBel, hBcard, hBL⟩ :=
    exists_elemAbelian_sq_acting_trivially h638 h858 hX hS hOut hp hp3 hpσ hrk hL1
  have : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := IsPGroup.of_card hBcard
  have hL := eq_inf_centralizer_sup_pCore_of_commutator_le hp (by omega) hBp hBL
  obtain ⟨S, hSyl, hle⟩ :=
    exists_sylow_inf_le_centralizer_of_eq_sup hr hr2 hX.cex.mem.1.le hL
  exact ⟨S, B, p, hSyl, hp, hpσ, hBM, hBel, hBcard, hle⟩

private theorem k1471t3_injective {G : Type} [Group G] {L Q : Subgroup G} (hQL : Q ≤ L)
    (hQO2 : Q ⊓ pCoreOf 2 L = ⊥) :
    Function.Injective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hQL)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hq
  have h : (q : G) ∈ Q ⊓ pCoreOf 2 L :=
    ⟨q.2, (CFSG.mem_openPCoreOf_iff (Subgroup.inclusion hQL q)).2 hq⟩
  rw [hQO2, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

private theorem k1471t3_nonempty_mulEquiv {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    {r : ℕ} [Fact r.Prime] (hQ : IsSylowOf r Q L) (hQO2 : Q ⊓ pCoreOf 2 L = ⊥)
    (S' : Sylow r (Bar2 L)) : Nonempty (↥Q ≃* ↥(S' : Subgroup (Bar2 L))) := by
  obtain ⟨P, hP⟩ := hQ.exists_sylow_eq_subgroupOf
  let f : ↥Q →* Bar2 L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hQ.le)
  let Pb : Sylow r (Bar2 L) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L)) P
  have hrange : f.range = (Pb : Subgroup (Bar2 L)) := by
    rw [Sylow.coe_mapSurjective, hP, MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ⟨((MonoidHom.ofInjective (k1471t3_injective hQ.le hQO2)).trans
    (MulEquiv.subgroupCongr hrange)).trans (Sylow.equiv Pb S')⟩

private theorem k1471t3_transport {G K : Type} [Group G] [Group K] {A : Subgroup G}
    {P E' : Subgroup K} {r : ℕ} (e : ↥A ≃* ↥P) (hP : IsMulCommutative ↥P) (hE'P : E' ≤ P)
    (hE'exp : ∀ x ∈ E', x ^ r = 1) (hE'card : Nat.card E' = r ^ 2) :
    (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have h : (⟨x, hx⟩ * ⟨y, hy⟩ : ↥A) = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      apply e.injective
      rw [map_mul, map_mul, mul_comm' (e ⟨x, hx⟩) (e ⟨y, hy⟩)]
    exact congrArg Subtype.val h
  refine ⟨hAc, ((E'.subgroupOf P).map e.symm.toMonoidHom).map A.subtype,
    Subgroup.map_subtype_le _, ⟨?_, ?_⟩, ?_⟩
  · exact isMulCommutative_iff.mpr fun x y =>
      Subtype.ext (hAc x.1 (Subgroup.map_subtype_le _ x.2) y.1 (Subgroup.map_subtype_le _ y.2))
  · rintro _ ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    have hb' : b ^ r = 1 := Subtype.ext (hE'exp b hb)
    change ((e.symm b : ↥A) : G) ^ r = 1
    rw [← Subgroup.coe_pow, ← map_pow, hb', map_one, Subgroup.coe_one]
  · rw [Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'P).toEquiv, hE'card]

theorem starWitness_transport {G : Type} [Group G] [Finite G] {M L S : Subgroup G} {r : ℕ}
    (hLM : L ≤ M) (hLnorm : (L.subgroupOf M).Normal) (hS : IsSylowOf r S M)
    (hStar : StarWitness (Bar2 L) r) :
    S ≤ (S ⊓ L) ⊔ centralizerBar S L ∧ (∀ x ∈ S ⊓ L, ∀ y ∈ S ⊓ L, x * y = y * x) ∧
      S ⊓ L ⊓ pCoreOf 2 L = ⊥ ∧
      ∃ E : Subgroup G, E ≤ S ⊓ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  obtain ⟨hr, hr5, hOut, S', hS'ab, E', hE'S', hE'exp, hE'card⟩ := hStar
  have : Fact r.Prime := ⟨hr⟩
  have hMN : M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLnorm
  have hA : IsSylowOf r (S ⊓ L) L := hS.inf_of_le_normalizer hLM hMN
  have hAO : S ⊓ L ⊓ pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne r 2 (by omega) _ _ hA.isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)).eq_bot
  obtain ⟨e⟩ := k1471t3_nonempty_mulEquiv hA hAO S'
  obtain ⟨hab, E, hEA, hEel, hEcard⟩ := k1471t3_transport e hS'ab hE'S' hE'exp hE'card
  refine ⟨?_, hab, hAO, E, hEA, hEel, hEcard⟩
  have hSn : S ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hs) h)
      (Subgroup.mem_normalizer_iff.mp (hS.le.trans hMN hs) h)
  exact le_sup_centralizerBar_of_inner_prime inf_le_left inf_le_right rfl
    ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hSn) hA hS.isPGroup
    (hS.le.trans hMN) le_rfl fun x hx =>
      exists_conj_of_not_dvd_outer x (hMN (hS.le hx))
        (hS.isPGroup.to_le (Subgroup.zpowers_le.2 hx)) hOut

theorem false_of_starWitness_of_choiceX {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (hsig4 : SigmaIsRankFour D) (h614 : R6_14 D) (h638 : R6_38 D)
    (h858 : R858 D) (h72 : R72 D) (h76 : R76Sig D) (hKF7 : KStrongEmbedded72)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L)
    (hS : IsSimpleGroup (Bar2 L)) (hOut : IsCyclic (Outer (Bar2 L))) {r : ℕ}
    (hStar : StarWitness (Bar2 L) r) : False := by
  have hr : r.Prime := hStar.1
  have hr5 : 5 ≤ r := hStar.2.1
  obtain ⟨S, B, p, hSyl, hp, hpσ, hBM, hBel, hBcard, hcent⟩ :=
    exists_sigma_ep2_centralizing_sylow_inf hSg h638 h858 h72 hKF7 hX hLX hS hOut hr (by omega)
  have hLM : L ≤ D.M := hX.cex.mem.1.le
  have hLnorm : (L.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr
      (normalizer_le_of_r858_of_isSimpleGroup h858 hX.cex hS)
  obtain ⟨hdec, hab, hSL, E, hEle, hEel, hEcard⟩ := starWitness_transport hLM hLnorm hSyl hStar
  have hEL : E ≤ L := hEle.trans inf_le_right
  have hEM : E ≤ D.M := (hEle.trans inf_le_left).trans hSyl.le
  have h1 : 1 < CFSG.Open.pRank r L := by
    have := le_pRank' hr hEL hEel hEcard
    omega
  have hnot : ¬ IsStronglyPEmbedded r D.M :=
    not_stronglyEmbedded_of_choiceX_of_leaves h72 hKF7 hX hLX hS hr (by omega) h1
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hX.cex.mem
  obtain ⟨h614', hsub, hrsig⟩ := family_hyps_of_r6_14 hSg hsig4 hns h614 hnot
  have hBE : B ≤ centralizer (E : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact ((Subgroup.mem_centralizer_iff.1 (hcent (hEle he))) b hb).symm
  have hpr := D.sig_prime p hpσ
  have hΓ : rankThreeGamma 1 r E ≤ D.M := by
    refine h76 p hpσ hpr.2 (sp_of_mem_sig hSg hns hpσ) r hr E hEM hEel hEcard ?_ ?_
    · have := le_pRank' hpr.1 (le_inf hBM hBE) hBel hBcard
      omega
    · intro Y hYE _
      have hBY : B ≤ D.M ⊓ normalizer (Y : Set G) :=
        le_inf hBM (hBE.trans ((Subgroup.centralizer_le hYE).trans
          (Subgroup.centralizer_le_normalizer (Y : Set G))))
      have := le_pRank' hpr.1 hBY hBel hBcard
      omega
  exact false_of_abelian_sylow_of_bar h614' hsub hr (by omega) hrsig hnot hLM hLnorm hSyl hdec
    hab hSL hEle hEel hEcard hΓ

theorem false_of_lie_families_of_choiceX
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hNS : G2NonsplitSylowInput) (hTri : TrialityTorusSylowInput) (hOutC : LieOutCyclicInput)
    (hSg : SigmaStd D) (hsig4 : SigmaIsRankFour D) (h614 : R6_14 D) (h638 : R6_38 D)
    (h858 : R858 D) (h72 : R72 D) (h76 : R76Sig D) (hKF7 : KStrongEmbedded72)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L)
    (hS : IsSimpleGroup (Bar2 L))
    (h : (∃ p f : ℕ, LieModel (Bar2 L) .G2 0 p f ∧ p.Prime ∧ p ≠ 3 ∧ 1 ≤ f ∧ 3 ≤ p ^ f ∧
          p ^ f ≠ 5 ∧ p ^ f ≠ 7 ∧ p ^ f ≠ 17) ∨
        (∃ p f : ℕ, LieModel (Bar2 L) .trialityD4 0 p f ∧ p.Prime ∧ 1 ≤ f) ∨
        (∃ f : ℕ, LieModel (Bar2 L) .twistedF4 0 2 f ∧ 3 ≤ f ∧ Odd f)) : False := by
  obtain ⟨r, hStar⟩ := exists_starWitness_of_lie_families hNS hTri h
  have hOut : IsCyclic (Outer (Bar2 L)) := by
    rcases h with ⟨p, f, hK, -, hp3, -⟩ | ⟨p, f, hK, -⟩ | ⟨f, hK, -⟩
    · exact hOutC.1 _ p f hK hp3
    · exact hOutC.2.1 _ p f hK
    · exact hOutC.2.2 _ f hK
  exact false_of_starWitness_of_choiceX hSg hsig4 h614 h638 h858 h72 h76 hKF7 hX hLX hS hOut hStar

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
