module

public import CFSG.Quasithin.SteinbergCCPrimeWitness
public import CFSG.Quasithin.SteinbergCCPerfectCentralization
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Quasithin.SteinbergCC

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

theorem eq_bot_of_isPerfect_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K : Subgroup G} (hK : Group.IsPerfect K) (hKp : IsPGroup p K) : K = ⊥ := by
  have : Group.IsNilpotent K := hKp.isNilpotent
  by_contra hne
  have : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hne
  exact Group.IsPerfect.not_isNilpotent K ‹_›

variable {H : Type*} [Group H] [Finite H]

theorem sylow_core_normalizer_perfect_residual_retains_original_prime_witness
    {L : Subgroup H} [L.Normal] (hL : Group.IsPerfect L) (T : Sylow 2 H)
    (hLT : L ⊔ (T : Subgroup H) = ⊤) {p : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2)
    {X : Subgroup H} [X.Normal] (hXL : X ≤ L)
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (_hP : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (_hW : frattini (X ⧸ CFSG.pCore 2 X) ≠ ⊤)
    (hirr : ∀ U : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ l ∈ L, ∀ u ∈ U, frattiniQuotConj X l u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hnt : ∃ l ∈ L, ∃ w, frattiniQuotConj X l w ≠ w) :
    let Q := (CFSG.pCore 2 X).map X.subtype
    let R := (CFSG.pCore 2 (X ⊔ (T : Subgroup H) : Subgroup H)).map
      (X ⊔ (T : Subgroup H)).subtype
    let A := L ⊓ normalizer (R : Set H)
    let Y := (CFSG.perfectResidual A).map A.subtype
    ((coreQuotConj X).ker : Set H) = {h | ∀ x ∈ X, ⁅x, h⁆ ∈ Q} ∧
      R = (T : Subgroup H) ⊓ (coreQuotConj X).ker ∧ IsSylowOf 2 R (coreQuotConj X).ker ∧
      (coreQuotConj X).ker ⊔ normalizer (R : Set H) = ⊤ ∧
      normalizer (R : Set H) = A ⊔ (T : Subgroup H) ∧
      (Y.subgroupOf A).Characteristic ∧ Group.IsPerfect Y ∧
      Y ≤ normalizer (R : Set H) ∧ normalizer (R : Set H) ≤ normalizer (Y : Set H) ∧
      Y.map (coreQuotConj X) = A.map (coreQuotConj X) ∧
      A.map (coreQuotConj X) = L.map (coreQuotConj X) ∧
      Y.map (frattiniQuotConj X) = L.map (frattiniQuotConj X) ∧
      ⁅X, Y⁆ = X ∧ X ≤ Y ∧ Y ≤ A ∧ A ≤ L ∧ (T : Subgroup H) ≤ normalizer (Y : Set H) := by
  intro Q R A Y
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : Q.Normal := ConjAct.normal_of_characteristic_of_normal
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map X.subtype
  have hQT : Q ≤ T := hQ2.le_sylow_of_normal T
  have hmemQ : ∀ x : X, (x : H) ∈ Q ↔ x ∈ CFSG.pCore 2 X := fun x =>
    mem_map_iff_mem (subtype_injective X)
  have hker : ∀ h : H, h ∈ (coreQuotConj X).ker ↔ ∀ x ∈ X, ⁅x, h⁆ ∈ Q := by
    intro h
    change MulAut.conjNormal h ∈ (CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 X)).ker ↔ _
    rw [CFSG.SectionRank.Ccomm.mem_ker_autQuotient]
    constructor
    · intro hh x hx
      have h1 := (hmemQ _).mpr (hh ⟨x⁻¹, inv_mem hx⟩)
      have e : (((⟨x⁻¹, inv_mem hx⟩ : X)⁻¹ * MulAut.conjNormal h ⟨x⁻¹, inv_mem hx⟩ : X) : H) =
          ⁅x, h⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def]
        group
      rwa [e] at h1
    · intro hh x
      apply (hmemQ _).mp
      have e : ((x⁻¹ * MulAut.conjNormal h x : X) : H) = ⁅(x : H)⁻¹, h⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def,
          inv_inv]
        group
      rw [e]
      exact hh _ (inv_mem x.2)
  have hQC : Q ≤ (coreQuotConj X).ker := fun q hq => (hker q).mpr fun x _ => by
    rw [commutatorElement_def]
    exact mul_mem (hQn.conj_mem q hq x) (inv_mem hq)
  have hRXT : R ≤ X ⊔ (T : Subgroup H) := map_subtype_le _
  have hR2 : IsPGroup 2 R := CFSG.pCore_isPGroup.map _
  have hRsub : R.subgroupOf (X ⊔ (T : Subgroup H)) =
      CFSG.pCore 2 (X ⊔ (T : Subgroup H) : Subgroup H) := by
    exact comap_map_eq_self_of_injective (subtype_injective _) _
  have hXTR : X ⊔ (T : Subgroup H) ≤ normalizer (R : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hRXT).mp (by rw [hRsub]; infer_instance)
  have hTN : (T : Subgroup H) ≤ normalizer (R : Set H) := le_sup_right.trans hXTR
  have hXN : X ≤ normalizer (R : Set H) := le_sup_left.trans hXTR
  have hXS : ∀ x ∈ X, ∀ s ∈ (T : Subgroup H) ⊓ (coreQuotConj X).ker,
      x * s * x⁻¹ ∈ (T : Subgroup H) ⊓ (coreQuotConj X).ker := by
    intro x hx s hs
    have hc : ⁅x, s⁆ ∈ Q := (hker s).mp (mem_inf.mp hs).2 x hx
    have e : x * s * x⁻¹ = ⁅x, s⁆ * s := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (mem_inf.mpr ⟨hQT hc, hQC hc⟩) hs
  have hTS : ∀ t ∈ (T : Subgroup H), ∀ s ∈ (T : Subgroup H) ⊓ (coreQuotConj X).ker,
      t * s * t⁻¹ ∈ (T : Subgroup H) ⊓ (coreQuotConj X).ker := fun t ht s hs =>
    mem_inf.mpr ⟨mul_mem (mul_mem ht (mem_inf.mp hs).1) (inv_mem ht),
      (inferInstance : (coreQuotConj X).ker.Normal).conj_mem s (mem_inf.mp hs).2 t⟩
  have hSR : (T : Subgroup H) ⊓ (coreQuotConj X).ker ≤ R := by
    have hSXT : (T : Subgroup H) ⊓ (coreQuotConj X).ker ≤ X ⊔ (T : Subgroup H) :=
      inf_le_left.trans le_sup_right
    have hSn : (((T : Subgroup H) ⊓ (coreQuotConj X).ker).subgroupOf
        (X ⊔ (T : Subgroup H))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hSXT).mpr
        (sup_le (le_normalizer_of_conj_mem hXS) (le_normalizer_of_conj_mem hTS))
    have hS2 : IsPGroup 2 (((T : Subgroup H) ⊓ (coreQuotConj X).ker).subgroupOf
        (X ⊔ (T : Subgroup H))) :=
      (T.isPGroup'.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe hSXT).symm
    have h1 := le_pCore_of_normal_of_isPGroup hSn hS2
    intro s hs
    exact ⟨⟨s, hSXT hs⟩, h1 (mem_subgroupOf.mpr hs), rfl⟩
  have hXRQ : X ⊓ R ≤ Q := by
    have hn : ((X ⊓ R).subgroupOf X).Normal :=
      (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        (le_normalizer_of_conj_mem fun g hg z hz => mem_inf.mpr
          ⟨mul_mem (mul_mem hg (mem_inf.mp hz).1) (inv_mem hg),
            (mem_normalizer_iff.mp (hXN hg) z).mp (mem_inf.mp hz).2⟩)
    have h2 : IsPGroup 2 ((X ⊓ R).subgroupOf X) :=
      (hR2.to_le inf_le_right).of_equiv (subgroupOfEquivOfLe inf_le_left).symm
    have h3 := le_pCore_of_normal_of_isPGroup hn h2
    intro z hz
    exact ⟨⟨z, (mem_inf.mp hz).1⟩, h3 (mem_subgroupOf.mpr hz), rfl⟩
  have hRC : R ≤ (coreQuotConj X).ker := by
    intro r hr
    rw [hker]
    intro x hx
    refine hXRQ (mem_inf.mpr ⟨?_, ?_⟩)
    · rw [commutatorElement_def, mul_assoc x r, mul_assoc x]
      exact mul_mem hx ((inferInstance : X.Normal).conj_mem _ (inv_mem hx) r)
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp (hXN hx) r).mp hr) (inv_mem hr)
  have hRT : R ≤ T := by
    have h := T.is_maximal' (T.isPGroup'.to_sup_of_normal_right' hR2 hTN) le_sup_left
    rw [← h]
    exact le_sup_right
  have hRS : R = (T : Subgroup H) ⊓ (coreQuotConj X).ker := le_antisymm (le_inf hRT hRC) hSR
  have hTsyl : IsSylowOf 2 (T : Subgroup H) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, T.isPGroup', T.not_dvd_index⟩
  have hRsyl : IsSylowOf 2 R (coreQuotConj X).ker := by
    rw [hRS]
    exact hTsyl.inf_of_le_normalizer le_top (by rw [normalizer_eq_top])
  have hFrat : (coreQuotConj X).ker ⊔ normalizer (R : Set H) = ⊤ := by
    obtain ⟨P, hP⟩ := hRsyl
    have h := Sylow.normalizer_sup_eq_top P
    rwa [hP, sup_comm] at h
  have hAN : A ≤ normalizer (R : Set H) := inf_le_right
  have hAL : A ≤ L := inf_le_left
  have hNAT : normalizer (R : Set H) = A ⊔ (T : Subgroup H) := by
    refine le_antisymm (fun n hn => ?_) (sup_le hAN hTN)
    have hn' : n ∈ (↑(L ⊔ (T : Subgroup H)) : Set H) := by
      rw [hLT]
      exact mem_top n
    rw [normal_mul] at hn'
    obtain ⟨l, hl, t, ht, hlt⟩ := hn'
    have hlt : l * t = n := hlt
    subst hlt
    have hlN : l ∈ normalizer (R : Set H) := by
      have h1 := mul_mem hn (inv_mem (hTN ht))
      rwa [mul_inv_cancel_right] at h1
    exact mul_mem_sup (mem_inf.mpr ⟨hl, hlN⟩) ht
  have hNA : ∀ n ∈ normalizer (R : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A := fun n hn a ha =>
    mem_inf.mpr ⟨(inferInstance : L.Normal).conj_mem a (mem_inf.mp ha).1 n,
      mul_mem (mul_mem hn (mem_inf.mp ha).2) (inv_mem hn)⟩
  have hTA : (T : Subgroup H) ≤ normalizer (A : Set H) :=
    le_normalizer_of_conj_mem fun t ht a ha => hNA t (hTN ht) a ha
  have hdecomp : ∀ h : H, ∃ c ∈ (coreQuotConj X).ker, ∃ a ∈ A, ∃ t ∈ (T : Subgroup H),
      c * (a * t) = h := by
    intro h
    have hh : h ∈ (↑((coreQuotConj X).ker ⊔ normalizer (R : Set H)) : Set H) := by
      rw [hFrat]
      exact mem_top h
    rw [normal_mul] at hh
    obtain ⟨c, hc, n, hn, hcn⟩ := hh
    have hn' : n ∈ (↑(A ⊔ (T : Subgroup H)) : Set H) := by
      rw [← hNAT]
      exact hn
    rw [coe_mul_of_right_le_normalizer_left A T hTA] at hn'
    obtain ⟨a, ha, t, ht, hat⟩ := hn'
    exact ⟨c, hc, a, ha, t, ht, by rw [show a * t = n from hat]; exact hcn⟩
  have hρAL : A.map (coreQuotConj X) = L.map (coreQuotConj X) := by
    refine le_antisymm (map_mono hAL) ?_
    have hMn : ((A.map (coreQuotConj X)).comap (coreQuotConj X)).Normal := ⟨fun m hm h => by
      obtain ⟨c, hc, a, ha, t, ht, rfl⟩ := hdecomp h
      obtain ⟨a', ha', hma⟩ := hm
      rw [mem_comap]
      refine ⟨(a * t) * a' * (a * t)⁻¹, hNA _ (mul_mem (hAN ha) (hTN ht)) a' ha', ?_⟩
      simp only [map_mul, map_inv, hma, MonoidHom.mem_ker.mp hc, one_mul]⟩
    have hM2 : IsPGroup 2 (H ⧸ (A.map (coreQuotConj X)).comap (coreQuotConj X)) := by
      refine T.isPGroup'.of_surjective
        ((QuotientGroup.mk' _).comp (T : Subgroup H).subtype) ?_
      intro v
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ v
      obtain ⟨c, hc, a, ha, t, ht, rfl⟩ := hdecomp h
      have hcM : c ∈ (A.map (coreQuotConj X)).comap (coreQuotConj X) := by
        rw [mem_comap, MonoidHom.mem_ker.mp hc]
        exact one_mem _
      have haM : a ∈ (A.map (coreQuotConj X)).comap (coreQuotConj X) :=
        mem_comap.mpr (mem_map_of_mem _ ha)
      refine ⟨⟨t, ht⟩, ?_⟩
      change (t : H ⧸ (A.map (coreQuotConj X)).comap (coreQuotConj X)) =
        ((c * (a * t) : H) : H ⧸ (A.map (coreQuotConj X)).comap (coreQuotConj X))
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).mpr hcM,
        (QuotientGroup.eq_one_iff a).mpr haM, one_mul, one_mul]
    have hLM : L ≤ (A.map (coreQuotConj X)).comap (coreQuotConj X) := by
      have : Group.IsPerfect L := hL
      have h := eq_bot_of_isPerfect_of_isPGroup
        (Group.IsPerfect.map (H := L) (QuotientGroup.mk' _)) (hM2.to_subgroup _)
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    rintro _ ⟨l, hl, rfl⟩
    exact hLM hl
  obtain ⟨-, hYchar, hYperf, -, -, -⟩ := CFSG.perfect_residual_characterization (G := A)
  have hYsub : Y.subgroupOf A = CFSG.perfectResidual A :=
    comap_map_eq_self_of_injective (subtype_injective A) _
  have hYA : Y ≤ A := map_subtype_le _
  have hYperf' : Group.IsPerfect Y := by
    have := hYperf
    exact Group.IsPerfect.map A.subtype
  have hNY : normalizer (R : Set H) ≤ normalizer (Y : Set H) := by
    have hNA' : normalizer (R : Set H) ≤ normalizer (A : Set H) := le_normalizer_of_conj_mem hNA
    refine le_normalizer_of_conj_mem fun n hn y hy => ?_
    obtain ⟨a, ha, rfl⟩ := hy
    have h1 := characteristic_iff_map_eq.mp hYchar (A.normalizerMonoidHom ⟨n, hNA' hn⟩)
    refine ⟨A.normalizerMonoidHom ⟨n, hNA' hn⟩ a, ?_, rfl⟩
    rw [← h1]
    exact mem_map_of_mem _ ha
  have hρYA : Y.map (coreQuotConj X) = A.map (coreQuotConj X) := by
    obtain ⟨h1, -, -⟩ := CFSG.perfect_residual_transport ((coreQuotConj X).comp A.subtype)
    have hrange : ((coreQuotConj X).comp A.subtype).range = A.map (coreQuotConj X) := by
      rw [MonoidHom.range_comp, range_subtype]
    have hperf : Group.IsPerfect ((coreQuotConj X).comp A.subtype).range := by
      rw [isPerfect_iff, hrange, hρAL, ← map_commutator, isPerfect_iff.mp hL]
    obtain ⟨-, -, h3⟩ := CFSG.perfect_residual_transport
      (MonoidHom.id ((coreQuotConj X).comp A.subtype).range)
    have htop := h3 ⊤ (Group.IsPerfect.top_iff.mpr hperf)
    rw [top_le_iff] at htop
    rw [htop, ← MonoidHom.range_eq_map, range_subtype, hrange, ← map_map] at h1
    exact h1
  have hρWY : Y.map (frattiniQuotConj X) = L.map (frattiniQuotConj X) := by
    change Y.map ((CFSG.SectionRank.Ccomm.autQuotient _).comp (coreQuotConj X)) =
      L.map ((CFSG.SectionRank.Ccomm.autQuotient _).comp (coreQuotConj X))
    rw [← map_map, ← map_map, hρYA, hρAL]
  have hXA : X ≤ A := le_inf hXL hXN
  have hXY : ⁅X, Y⁆ = X := by
    have hmemY : ∀ l ∈ L, ∃ y ∈ Y, frattiniQuotConj X y = frattiniQuotConj X l := by
      intro l hl
      have h1 : frattiniQuotConj X l ∈ Y.map (frattiniQuotConj X) := by
        rw [hρWY]
        exact mem_map_of_mem _ hl
      obtain ⟨y, hy, hyl⟩ := h1
      exact ⟨y, hy, hyl⟩
    refine commutator_eq_of_irreducible_frattini X Y hX2
      (fun U hU => hirr U fun l hl u hu => ?_) ?_
    · obtain ⟨y, hy, hyl⟩ := hmemY l hl
      rw [← hyl]
      exact hU y hy u hu
    · obtain ⟨l, hl, w, hw⟩ := hnt
      obtain ⟨y, hy, hyl⟩ := hmemY l hl
      exact ⟨y, hy, w, by rw [hyl]; exact hw⟩
  have hXYle : X ≤ Y := by
    calc X = ⁅X, Y⁆ := hXY.symm
      _ ≤ Y := by
        rw [commutator_le]
        intro x hx y hy
        rw [commutatorElement_def]
        exact mul_mem ((mem_normalizer_iff.mp (hNY (hXN hx)) y).mp hy) (inv_mem hy)
  refine ⟨Set.ext hker, hRS, hRsyl, hFrat, hNAT, by rw [hYsub]; exact hYchar, hYperf',
    hYA.trans hAN, hNY, hρYA, hρAL, hρWY, hXY, hXYle, hYA, hAL, hTN.trans hNY⟩

end CFSG.Quasithin.SteinbergCC
