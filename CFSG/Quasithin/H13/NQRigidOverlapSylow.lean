module

public import CFSG.Quasithin.H13.NQBlockOriginalSupplements
public import CFSG.Quasithin.SteinbergCCOddNilpotentDerived
public import CFSG.Quasithin.SteinbergCDPrimePlaneSylowNormalizer

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.SteinbergCC (powOneClosure)
open scoped commutatorElement

section Plane

variable {Λ : Type*} [Group Λ] [Finite Λ]

theorem mem_pCore_of_mem_fitting {X : Type*} [Group X] [Finite X] {q : ℕ} [Fact q.Prime] {y : X}
    (hy : y ∈ CFSG.fittingSubgroup X) {k : ℕ} (hk : orderOf y = q ^ k) : y ∈ CFSG.pCore q X := by
  set F := CFSG.fittingSubgroup X
  have hk' : (⟨y, hy⟩ : F) ^ (q ^ k) = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hk]
    exact pow_orderOf_eq_one y)
  have hpg : IsPGroup q (Subgroup.zpowers (⟨y, hy⟩ : F)) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change ((⟨y, hy⟩ : F) ^ n) ^ (q ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk', one_zpow]
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  have hmem : y ∈ (P : Subgroup F).map F.subtype :=
    ⟨⟨y, hy⟩, hP (Subgroup.mem_zpowers _), rfl⟩
  exact Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent q P hmem

theorem irreducible_canonical_plane [Group.IsPerfect Λ]
    (hSQT' : CFSG.IsStronglyQuasithin (Λ ⧸ CFSG.pCore 2 Λ))
    (hO2' : CFSG.pCore 2 (Λ ⧸ CFSG.pCore 2 Λ) = ⊥)
    (hLC' : CFSG.IsCComponent (⊤ : Subgroup (Λ ⧸ CFSG.pCore 2 Λ)))
    (hq : ¬ CFSG.IsQuasisimple (Λ ⧸ CFSG.pCore 2 Λ)) {q : ℕ} [Fact q.Prime]
    (hqF : q ∈ (Nat.card (CFSG.fittingSubgroup (Λ ⧸ CFSG.pCore 2 Λ))).primeFactors)
    (S : Sylow 2 Λ) (M₁ : Subgroup (Λ ⧸ CFSG.pCore 2 Λ))
    (hΦM : (frattini (powOneClosure (CFSG.pCore q (Λ ⧸ CFSG.pCore 2 Λ)) q)).map
      (powOneClosure (CFSG.pCore q (Λ ⧸ CFSG.pCore 2 Λ)) q).subtype ≤ M₁)
    (hMD : M₁ ≤ powOneClosure (CFSG.pCore q (Λ ⧸ CFSG.pCore 2 Λ)) q)
    (hMS : ∀ s ∈ (S : Subgroup Λ), ∀ m ∈ M₁,
      (s : Λ ⧸ CFSG.pCore 2 Λ) * m * (s : Λ ⧸ CFSG.pCore 2 Λ)⁻¹ ∈ M₁) :
    M₁ = (frattini (powOneClosure (CFSG.pCore q (Λ ⧸ CFSG.pCore 2 Λ)) q)).map
        (powOneClosure (CFSG.pCore q (Λ ⧸ CFSG.pCore 2 Λ)) q).subtype ∨
      M₁ = powOneClosure (CFSG.pCore q (Λ ⧸ CFSG.pCore 2 Λ)) q := by
  classical
  set D := powOneClosure (CFSG.pCore q (Λ ⧸ CFSG.pCore 2 Λ)) q with hD
  obtain ⟨hq5, hDc, -, hDexp, -, -, hDW, -, -, hDnt, -⟩ :=
    NQBlock.canonical_prime_data hSQT' hO2' hLC' hq hqF D rfl
  have hDn : D.Normal := inferInstance
  set β : Λ →* MulAut (D ⧸ frattini D) :=
    (NQBlock.wholeFrattiniAction D).comp (QuotientGroup.mk' (CFSG.pCore 2 Λ)) with hβ
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hDnt
    refine MonoidHom.ext fun g => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 Λ) g
    exact DFunLike.congr_fun h1 x
  have hWp : ∀ w : D ⧸ frattini D, w ^ q = 1 := by
    intro w
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_pow]
    have hd : d ^ q = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hDexp d d.2)
    rw [hd, QuotientGroup.mk_one]
  have : IsMulCommutative (D ⧸ frattini D) := IsPGroup.isMulCommutative_of_card_eq_prime_sq hDW
  set M' : Subgroup (D ⧸ frattini D) := (M₁.subgroupOf D).map (QuotientGroup.mk' (frattini D))
    with hM'
  have hM'S : ∀ s ∈ (S : Subgroup Λ), ∀ w ∈ M', β s w ∈ M' := by
    rintro s hs _ ⟨d, hd, rfl⟩
    refine ⟨MulAut.conjNormal ((s : Λ ⧸ CFSG.pCore 2 Λ)) d, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, MulAut.conjNormal_apply]
    exact hMS s hs _ (mem_subgroupOf.mp hd)
  rcases SteinbergCD.perfect_sylow_two_irreducible_of_card_eq_sq hq5 hWp hDW β hβ1 S M' hM'S
    with h0 | h0
  · left
    refine le_antisymm (fun m hm => ?_) hΦM
    have hmD : m ∈ D := hMD hm
    have h1 : QuotientGroup.mk' (frattini D) (⟨m, hmD⟩ : D) ∈ M' :=
      ⟨⟨m, hmD⟩, mem_subgroupOf.mpr hm, rfl⟩
    rw [h0, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨m, hmD⟩, h1, rfl⟩
  · right
    refine le_antisymm hMD fun d hd => ?_
    have h1 : M₁.subgroupOf D ⊔ frattini D = ⊤ := by
      have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (frattini D)) (M₁.subgroupOf D)
      rw [← hM', h0, comap_top, QuotientGroup.ker_mk'] at h2
      exact h2.symm
    have h3 := frattini_nongenerating h1
    have h4 : (⟨d, hd⟩ : D) ∈ M₁.subgroupOf D := h3 ▸ mem_top _
    exact mem_subgroupOf.mp h4

theorem inf_fitting_le_commutator [Group.IsPerfect Λ]
    (hSQT' : CFSG.IsStronglyQuasithin (Λ ⧸ CFSG.pCore 2 Λ))
    (hO2' : CFSG.pCore 2 (Λ ⧸ CFSG.pCore 2 Λ) = ⊥)
    (hLC' : CFSG.IsCComponent (⊤ : Subgroup (Λ ⧸ CFSG.pCore 2 Λ)))
    (hq : ¬ CFSG.IsQuasisimple (Λ ⧸ CFSG.pCore 2 Λ)) (S : Sylow 2 Λ)
    {J : Subgroup (Λ ⧸ CFSG.pCore 2 Λ)}
    (hJ : ∀ s ∈ (S : Subgroup Λ), ∀ j ∈ J,
      (s : Λ ⧸ CFSG.pCore 2 Λ) * j * (s : Λ ⧸ CFSG.pCore 2 Λ)⁻¹ ∈ J)
    (hDJ : ∀ q : ℕ, q.Prime →
      q ∈ (Nat.card (CFSG.fittingSubgroup (Λ ⧸ CFSG.pCore 2 Λ))).primeFactors →
      ¬ powOneClosure (CFSG.pCore q (Λ ⧸ CFSG.pCore 2 Λ)) q ≤ J) :
    J ⊓ CFSG.fittingSubgroup (Λ ⧸ CFSG.pCore 2 Λ) ≤
      ⁅CFSG.fittingSubgroup (Λ ⧸ CFSG.pCore 2 Λ), CFSG.fittingSubgroup (Λ ⧸ CFSG.pCore 2 Λ)⁆ := by
  classical
  set Lb := Λ ⧸ CFSG.pCore 2 Λ
  set F := CFSG.fittingSubgroup Lb
  intro y hy
  refine SteinbergCC.mem_of_forall_primary_pow_mem _ y fun z hz hzq => ?_
  obtain ⟨q, k, hqp, hzk⟩ := hzq
  have hzJF : z ∈ J ⊓ F := (zpowers_le.mpr hy) hz
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hzk
    rw [hzk]
    exact one_mem _
  have : Fact q.Prime := ⟨hqp⟩
  have hzP : z ∈ CFSG.pCore q Lb := mem_pCore_of_mem_fitting (mem_inf.mp hzJF).2 hzk
  have hqF : q ∈ (Nat.card F).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hqp, ?_, Nat.card_pos.ne'⟩
    have h1 : orderOf (⟨z, (mem_inf.mp hzJF).2⟩ : F) = q ^ (k + 1) := by
      rw [Subgroup.orderOf_mk, hzk]
    have h2 : q ∣ orderOf (⟨z, (mem_inf.mp hzJF).2⟩ : F) := by
      rw [h1]
      exact dvd_pow_self q (Nat.succ_ne_zero k)
    exact h2.trans (orderOf_dvd_natCard _)
  set P := CFSG.pCore q Lb with hP
  have : P.Characteristic := CFSG.pCore_characteristic
  set φ : ↥(S : Subgroup Λ) →* MulAut Lb :=
    MulAut.conj.comp ((QuotientGroup.mk' (CFSG.pCore 2 Λ)).comp (S : Subgroup Λ).subtype) with hφ
  have hirr : ∀ M₁ : Subgroup Lb,
      (frattini (powOneClosure P q)).map (powOneClosure P q).subtype ≤ M₁ →
      M₁ ≤ powOneClosure P q → (∀ a : ↥(S : Subgroup Λ), ∀ m ∈ M₁, φ a m ∈ M₁) →
      M₁ = (frattini (powOneClosure P q)).map (powOneClosure P q).subtype ∨
        M₁ = powOneClosure P q :=
    fun M₁ h1 h2 h3 => irreducible_canonical_plane hSQT' hO2' hLC' hq hqF S M₁ h1 h2
      fun s hs m hm => h3 ⟨s, hs⟩ m hm
  have hJ' : ∀ a : ↥(S : Subgroup Λ), ∀ j ∈ J, φ a j ∈ J := fun a j hj => hJ a a.2 j hj
  obtain ⟨-, -, -, -, -, -, -, hshape, -⟩ :=
    NQBlock.canonical_prime_data hSQT' hO2' hLC' hq hqF (powOneClosure P q) rfl
  rcases hshape with ⟨⟨hPab⟩, -, -, -⟩ | ⟨-, hPnc, hP3, hPexp⟩
  · have hPab' : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hPab.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have h0 := SteinbergCC.inf_eq_bot_of_abelian_sylow φ CFSG.pCore_isPGroup hPab' hirr hJ'
      (hDJ q hqp hqF)
    have h1 : z ∈ J ⊓ P := mem_inf.mpr ⟨(mem_inf.mp hzJF).1, hzP⟩
    rw [h0, mem_bot] at h1
    rw [h1]
    exact one_mem _
  · have hnc : ∃ a b : P, a * b ≠ b * a := by
      by_contra hall
      push Not at hall
      exact hPnc ⟨⟨hall⟩⟩
    have h1 := SteinbergCC.inf_le_commutator_of_cube_sylow φ hnc hP3 hPexp hirr hJ'
      (hDJ q hqp hqF)
    exact commutator_mono (CFSG.pCore_le_fitting _ q) (CFSG.pCore_le_fitting _ q)
      (h1 (mem_inf.mpr ⟨(mem_inf.mp hzJF).1, hzP⟩))

end Plane

section Normalize

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

omit [Finite G] in
theorem coe_mem_normalizer_map {S : Subgroup ↥L} {x : ↥L} (hx : x ∈ normalizer (S : Set ↥L)) :
    (x : G) ∈ normalizer ((S.map L.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hx ⊢
  intro g
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨x * s * x⁻¹, (hx s).mp hs, by simp⟩
  · rintro ⟨s, hs, hsg⟩
    refine ⟨x⁻¹ * s * x, (hx _).mpr (by simpa [mul_assoc] using hs), ?_⟩
    have hsg' : (s : G) = x * g * (x : G)⁻¹ := hsg
    simp only [coe_subtype, coe_mul, coe_inv, hsg']
    group

omit [Finite G] in
theorem conj_mem_zpowers_iff {X : Type*} [Group X] {a t w : X} (h : a * t = t * a) :
    a * w * a⁻¹ ∈ zpowers t ↔ w ∈ zpowers t := by
  have hc : Commute a t := h
  constructor
  · intro hw
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hw
    refine mem_zpowers_iff.mpr ⟨n, ?_⟩
    have e : w = a⁻¹ * (a * w * a⁻¹) * a := by group
    rw [e, ← hn, ((hc.inv_left).zpow_right n).eq, inv_mul_cancel_right]
  · intro hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
    refine mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [(hc.zpow_right n).eq, mul_inv_cancel_right]

theorem radical_inf_le_normalizer_sylow (h : QTNQ T L M)
    {H : Subgroup G} (hTH : T ≤ H)
    (hesc : ∀ q : ℕ, q.Prime → 5 ≤ q → ∀ X₀ : Subgroup ↥L, NQBlock.IsOddResidualWitness q X₀ →
      ¬ X₀.map L.subtype ≤ H) :
    H ⊓ (CFSG.solvableRadical L).map L.subtype ≤
      normalizer ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSQT := NQBlock.isStronglyQuasithin_L_of_qtnq h
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  have hq := h.not_quasisimple
  obtain ⟨hSQT', hO2', hLC'⟩ := NQBlock.quotient_two_core_setup hSQT hLC
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr (by
    rw [commutator_def]
    exact hLC.2.1)
  set Q₀ := CFSG.pCore 2 ↥L with hQ₀
  set π := QuotientGroup.mk' Q₀ with hπ
  set N₀ := CFSG.solvableRadical ↥L with hN₀
  have hNL : N₀.map L.subtype ≤ L := map_subtype_le _
  have hRadc := CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization ↥L
  have hN₀n : N₀.Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hQ₀n : Q₀.Normal := CFSG.pCore_normal
  have hTM : IsSylowOf 2 T M := CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨h.t_le, h.sylow.1, fun h2 => h.sylow.2 (h2.trans (relIndex_dvd_index_of_le h.t_le))⟩
  obtain ⟨T0, hT0⟩ := hTM.inf_of_le_normalizer h.l_le h.eq_normalizer.le
  have hT0' : (T0 : Subgroup ↥L) = T.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hT0, subgroupOf_map_subtype]
  have hMN : M ≤ normalizer ((N₀.map L.subtype : Subgroup G) : Set G) := by
    rw [h.eq_normalizer]
    exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hTN : IsSylowOf 2 (T ⊓ N₀.map L.subtype) (N₀.map L.subtype) :=
    hTM.inf_of_le_normalizer (hNL.trans h.l_le) hMN
  set S₀ := T.subgroupOf L ⊓ N₀ with hS₀
  have hS₀map : S₀.map L.subtype = T ⊓ N₀.map L.subtype := by
    rw [map_inf_eq _ _ _ L.subtype_injective, subgroupOf_map_subtype, inf_assoc,
      inf_eq_right.mpr hNL]
  have hS₀syl : IsSylowOf 2 S₀ N₀ :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L).mp (by rw [hS₀map]; exact hTN)
  have hQ₀N : Q₀ ≤ N₀ := hRadc.2.2.1 Q₀ hQ₀n (by
    have := (CFSG.pCore_isPGroup : IsPGroup 2 Q₀).isNilpotent
    infer_instance)
  have hQ₀T : Q₀ ≤ T.subgroupOf L := hT0' ▸ CFSG.pCore_isPGroup.le_sylow_of_normal T0
  have hQ₀S : Q₀ ≤ S₀ := le_inf hQ₀T hQ₀N
  set J₀ := H.subgroupOf L ⊓ N₀ with hJ₀
  have hS₀J : S₀ ≤ J₀ := inf_le_inf_right _ fun x hx => hTH hx
  set Jb := J₀.map π with hJb
  obtain ⟨-, -, -, hSt⟩ :=
    NQBlock.two_core_free_radical_Sylow_involution_has_central_radical_centralizer hSQT' hO2'
      hLC' hq
  have hNbar : N₀.map π = CFSG.solvableRadical (↥L ⧸ Q₀) :=
    CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.map_solvableRadical
      (QuotientGroup.mk'_surjective Q₀) (by
        rw [QuotientGroup.ker_mk']
        have := (CFSG.pCore_isPGroup : IsPGroup 2 Q₀).isNilpotent
        infer_instance)
  have hSbar : IsSylowOf 2 (S₀.map π) (CFSG.solvableRadical (↥L ⧸ Q₀)) :=
    hNbar ▸ NQBlock.isSylowOf_map' hS₀syl π
  obtain ⟨hcard2, hSt'⟩ := hSt _ hSbar
  obtain ⟨t, htS, ht1⟩ : ∃ t ∈ S₀.map π, t ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : S₀.map π = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (hall x hx)
    rw [h1, card_bot] at hcard2
    exact absurd hcard2 (by norm_num)
  obtain ⟨hSz, hRad, -, hFC, -⟩ := hSt' t htS ht1
  have hJ : ∀ s ∈ (T0 : Subgroup ↥L), ∀ j ∈ Jb,
      (s : ↥L ⧸ Q₀) * j * (s : ↥L ⧸ Q₀)⁻¹ ∈ Jb := by
    rintro s hs _ ⟨x, hx, rfl⟩
    refine ⟨s * x * s⁻¹, mem_inf.mpr ⟨?_, hN₀n.conj_mem x (mem_inf.mp hx).2 s⟩, ?_⟩
    · have hsH : (s : G) ∈ H := by
        rw [hT0'] at hs
        exact hTH (mem_subgroupOf.mp hs)
      have hxH : (x : G) ∈ H := mem_subgroupOf.mp (mem_inf.mp hx).1
      rw [mem_subgroupOf, coe_mul, coe_mul, coe_inv]
      exact mul_mem (mul_mem hsH hxH) (inv_mem hsH)
    · rw [map_mul, map_mul, map_inv]
      rfl
  have hDJ : ∀ q : ℕ, q.Prime →
      q ∈ (Nat.card (CFSG.fittingSubgroup (↥L ⧸ Q₀))).primeFactors →
      ¬ powOneClosure (CFSG.pCore q (↥L ⧸ Q₀)) q ≤ Jb := by
    intro q hqp hqF hle
    have : Fact q.Prime := ⟨hqp⟩
    obtain ⟨hq5, -, hWq, -⟩ := NQBlock.canonical_prime_witness hSQT hLC hq hqF
      (CFSG.pCore q (↥L ⧸ Q₀)) (powOneClosure (CFSG.pCore q (↥L ⧸ Q₀)) q)
      ((powOneClosure (CFSG.pCore q (↥L ⧸ Q₀)) q).comap π)
      (closure {e | e ∈ (powOneClosure (CFSG.pCore q (↥L ⧸ Q₀)) q).comap π ∧ Odd (orderOf e)})
      rfl rfl rfl rfl
    apply hesc q hqp hq5 _ hWq
    have h1 : closure {e | e ∈ (powOneClosure (CFSG.pCore q (↥L ⧸ Q₀)) q).comap π ∧
        Odd (orderOf e)} ≤ H.subgroupOf L := by
      rw [closure_le]
      rintro e ⟨he, -⟩
      have he' : e ∈ Jb.comap π := comap_mono hle he
      rw [hJb, comap_map_eq, QuotientGroup.ker_mk'] at he'
      exact (sup_le inf_le_left (hQ₀S.trans (hS₀J.trans inf_le_left))) he'
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact mem_subgroupOf.mp (h1 hx)
  have hJF := inf_fitting_le_commutator hSQT' hO2' hLC' hq T0 hJ hDJ
  have hcomm : ∀ x ∈ J₀, π x * t = t * π x := by
    intro x hx
    have hxR : π x ∈ CFSG.solvableRadical (↥L ⧸ Q₀) := hNbar ▸ mem_map_of_mem π (mem_inf.mp hx).2
    rw [hRad] at hxR
    have hFn : (S₀.map π) ≤ normalizer ((CFSG.fittingSubgroup (↥L ⧸ Q₀) : Subgroup _) : Set _) := by
      rw [normalizer_eq_top_iff.mpr CFSG.fittingSubgroup_normal]
      exact le_top
    have hxR' : π x ∈ ((CFSG.fittingSubgroup (↥L ⧸ Q₀) ⊔ S₀.map π : Subgroup _) : Set _) := hxR
    rw [coe_mul_of_right_le_normalizer_left _ _ hFn] at hxR'
    obtain ⟨f, hf, s, hs, hfs⟩ := hxR'
    have hsJ : s ∈ Jb := map_mono hS₀J hs
    have hxJ : π x ∈ Jb := mem_map_of_mem π hx
    have hfJ : f ∈ Jb := by
      have e : f = π x * s⁻¹ := by rw [← hfs, mul_inv_cancel_right]
      rw [e]
      exact mul_mem hxJ (inv_mem hsJ)
    have hfC : f ∈ CFSG.fittingSubgroup (↥L ⧸ Q₀) ⊓ centralizer ({t} : Set _) := by
      rw [hFC]
      exact hJF (mem_inf.mpr ⟨hfJ, hf⟩)
    have hft : f * t = t * f := mem_centralizer_singleton_iff.mp (mem_inf.mp hfC).2
    have hst : s * t = t * s := by
      rw [hSz] at hs
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
      exact (Commute.zpow_left (Commute.refl t) n).eq
    rw [← hfs]
    calc f * s * t = f * (t * s) := by rw [mul_assoc, hst]
      _ = t * (f * s) := by rw [← mul_assoc, hft, mul_assoc]
  have hS₀eq : S₀ = (zpowers t).comap π := by
    rw [← hSz, comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hQ₀S]
  have hJN : ∀ x ∈ J₀, x ∈ normalizer (S₀ : Set ↥L) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    rw [hS₀eq, mem_comap, mem_comap, map_mul, map_mul, map_inv]
    exact (conj_mem_zpowers_iff (hcomm x hx)).symm
  rintro g ⟨hgH, n, hn, rfl⟩
  have hnJ : n ∈ J₀ := mem_inf.mpr ⟨mem_subgroupOf.mpr hgH, hn⟩
  have h1 := coe_mem_normalizer_map (hJN n hnJ)
  rwa [hS₀map] at h1

end Normalize

end CFSG.Quasithin.H13.NQRigid
