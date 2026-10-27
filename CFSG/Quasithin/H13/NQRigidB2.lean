module

public import CFSG.Quasithin.H13.NQRigidResidualBridge
public import CFSG.Quasithin.SteinbergBTRankSaturatingInner
public import CFSG.Quasithin.H13.NQRigidAsmPairData
public import CFSG.Quasithin.H13.NQRigidFitting3
public import CFSG.Quasithin.H13.NQTermComponentPair
public import CFSG.Quasithin.SteinbergBTResidualImageRankDichotomy

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {H : Type*} [Group H] [Finite H]

theorem ker_conj_eq_center (J : Type*) [Group J] :
    (MulAut.conj : J →* MulAut J).ker = center J := by
  ext g
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : MulAut J => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← h x]
    group

theorem pRank_inner_eq {J : Type*} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (center J)) : CFSG.pRank p (inner J) = CFSG.pRank p J := by
  have : Fact p.Prime := ⟨hp⟩
  let e : J ⧸ center J ≃* inner J :=
    (QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center J).symm).trans
      (QuotientGroup.quotientKerEquivRange _)
  rw [← pRank_congr hp.one_lt e, CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_quotient_eq _ hZ, ← CFSG.SectionRank.pRank_eq_open_pRank_top]

theorem prime_dvd_card_of_pRank_pos {J : Type*} [Group J] [Finite J] {p : ℕ} (hp : p.Prime)
    (h : 1 ≤ CFSG.pRank p J) : p ∣ Nat.card J := by
  obtain ⟨E, -, hEcard⟩ := SteinbergBM.exists_card_eq_pow_pRank (X := J) hp.one_lt
  have h1 : p ^ CFSG.pRank p J ∣ Nat.card J := by
    rw [← hEcard]
    exact card_subgroup_dvd_card E
  exact (dvd_pow_self p (by omega : CFSG.pRank p J ≠ 0)).trans h1

theorem le_normalizer_inf_of_normal {H : Type*} [Group H] {Y N : Subgroup H} (hN : N.Normal) :
    Y ≤ normalizer ((Y ⊓ N : Subgroup H) : Set H) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Y.mul_mem (Y.mul_mem hy h1) (Y.inv_mem hy), hN.conj_mem h h2 y⟩
  · rintro ⟨h1, h2⟩
    have h3 : h = y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ := by group
    rw [h3]
    exact ⟨Y.mul_mem (Y.mul_mem (Y.inv_mem hy) h1) (Y.inv_mem (Y.inv_mem hy)),
      hN.conj_mem _ h2 y⁻¹⟩

theorem isPGroup_coreQuot_of_pow_mem {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (Q : Subgroup X) [Q.Normal] (hQ2 : IsPGroup 2 Q) (hpow : ∀ x : X, x ^ p ∈ Q) :
    IsPGroup p (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQO : Q ≤ CFSG.pCore 2 X := SteinbergCC.le_pCore_of_normal_of_isPGroup inferInstance hQ2
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨1, ?_⟩
  rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hQO (hpow x)

theorem irreducible_component_normalizer_outer_rank_forces_containment {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpH : CFSG.pRank p H ≤ 2) (C : Subgroup H) [C.Normal] (hC : IsPGroup 2 C)
    {K : Subgroup H} (hK : CFSG.IsCComponent K)
    (hJ : CFSG.IsComponent (K.map (QuotientGroup.mk' C)))
    (hZ : ¬ p ∣ Nat.card (center (K.map (QuotientGroup.mk' C))))
    (hOut : CFSG.pRank p (Outer (K.map (QuotientGroup.mk' C))) ≤ 1)
    {X A : Subgroup H} (Q : Subgroup X) [Q.Normal] (hXA : X ≤ A)
    (hAK : A ≤ normalizer (K : Set H))
    (hAQ : A ≤ normalizer ((Q.map X.subtype : Subgroup H) : Set H))
    (hAX : A ≤ normalizer (X : Set H)) (hQ2 : IsPGroup 2 Q) (hpow : ∀ x : X, x ^ p ∈ Q)
    (hX2 : NoPQuotient 2 X) (hdim : p ^ 2 ≤ Nat.card ((X ⧸ Q) ⧸ frattini (X ⧸ Q)))
    (hlat : IsFrattiniLatticeIrreducible X A Q)
    (hJX : ⁅K.map (QuotientGroup.mk' C), X.map (QuotientGroup.mk' C)⁆ ≠ ⊥) :
    (∀ x ∈ X.map (QuotientGroup.mk' C), ∃ j ∈ K.map (QuotientGroup.mk' C),
        ∀ y ∈ K.map (QuotientGroup.mk' C), x * y * x⁻¹ = j * y * j⁻¹) ∧
      CFSG.pRank p (K.map (QuotientGroup.mk' C)) = 2 ∧ K.Normal ∧ X ≤ K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' C with hπ
  set J := K.map π with hJdef
  have hCsolv : Group.IsSolvable C := by
    have : Group.IsNilpotent C := hC.isNilpotent
    infer_instance
  have hAJ : ∀ a : A, π a ∈ normalizer (J : Set (H ⧸ C)) := fun a =>
    le_normalizer_map π ⟨a, hAK a.2, rfl⟩
  set α₀ : A →* normalizer (J : Set (H ⧸ C)) := (π.comp A.subtype).codRestrict _ hAJ with hα₀
  set α : A →* MulAut J := J.normalizerMonoidHom.comp α₀ with hα
  have hαapp : ∀ (a : A) (y : J), ((α a y : J) : H ⧸ C) = π a * y * (π a)⁻¹ := fun _ _ => rfl
  have : (resQ A Q).Normal := resQ_normal Q hXA hAQ
  have : (X.subgroupOf A).Normal := resX_normal hXA hAX
  have hW' : p ^ 2 ≤ Nat.card ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)) ⧸
      frattini ((X.subgroupOf A).map (QuotientGroup.mk' (resQ A Q)))) := by
    rw [card_frattini_resBar Q hXA]
    exact hdim
  have hOutA := (SteinbergBT.irreducible_two_prime_residual_image_rank_dichotomy hp hp2
    (resQ A Q) (X.subgroupOf A) (resQ_le_resX Q) (isPGroup_resQ Q hQ2)
    (pow_eq_one_resBar Q hpow) (noPQuotient_resX hXA hX2) hW' (irreducible_resBar Q hXA hlat)
    ((QuotientGroup.mk' (inner J)).comp α)).2 hOut
  have hinnerA : ∀ x : A, x ∈ X.subgroupOf A → α x ∈ inner J := by
    intro x hx
    have h1 : ((QuotientGroup.mk' (inner J)).comp α) x ∈
        (X.subgroupOf A).map ((QuotientGroup.mk' (inner J)).comp α) := ⟨x, hx, rfl⟩
    rw [hOutA, mem_bot, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  have hinner : ∀ x ∈ X.map π, ∃ j ∈ J, ∀ y ∈ J, x * y * x⁻¹ = j * y * j⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := hinnerA ⟨x, hXA hx⟩ (mem_subgroupOf.mpr hx)
    refine ⟨j, j.2, fun y hy => ?_⟩
    have h1 : ((MulAut.conj j ⟨y, hy⟩ : J) : H ⧸ C) =
        ((α ⟨x, hXA hx⟩ ⟨y, hy⟩ : J) : H ⧸ C) := by
      rw [hj]
    exact (hαapp _ _).symm.trans h1.symm
  have hαX : (X.subgroupOf A).map α ≠ ⊥ := by
    intro h0
    apply hJX
    rw [commutator_eq_bot_iff_le_centralizer]
    intro j hj
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : α ⟨x, hXA hx⟩ ∈ (X.subgroupOf A).map α := ⟨_, mem_subgroupOf.mpr hx, rfl⟩
    rw [h0, mem_bot] at h1
    have h2 := congrArg (fun φ : MulAut J => ((φ ⟨j, hj⟩ : J) : H ⧸ C)) h1
    simp only [MulAut.one_apply] at h2
    rw [hαapp] at h2
    calc π x * j = π x * j * (π x)⁻¹ * π x := by group
      _ = j * π x := by rw [show π x * j * (π x)⁻¹ = j from h2]
  have hrkα : 2 ≤ CFSG.pRank p ((X.subgroupOf A).map α) :=
    (SteinbergBT.irreducible_two_prime_residual_image_rank_dichotomy hp hp2
      (resQ A Q) (X.subgroupOf A) (resQ_le_resX Q) (isPGroup_resQ Q hQ2)
      (pow_eq_one_resBar Q hpow) (noPQuotient_resX hXA hX2) hW' (irreducible_resBar Q hXA hlat)
      α).1.resolve_left hαX
  have hαinner : (X.subgroupOf A).map α ≤ inner J := by
    rintro _ ⟨x, hx, rfl⟩
    exact hinnerA x hx
  have hrkJ2 : 2 ≤ CFSG.pRank p J := by
    rw [← pRank_inner_eq hp hZ]
    have h1 : CFSG.pRank p ((X.subgroupOf A).map α) ≤ CFSG.pRank p (inner J) := by
      have h2 := pRank_le_of_subgroup p hp.one_lt (((X.subgroupOf A).map α).subgroupOf (inner J))
      rwa [pRank_congr hp.one_lt (subgroupOfEquivOfLe hαinner)] at h2
    omega
  have hrkE : CFSG.pRank p (H ⧸ C) = CFSG.pRank p H :=
    pRank_quotient_of_isPGroup_two C hC hp hp2
  have hrkJE : CFSG.pRank p J ≤ CFSG.pRank p (H ⧸ C) := pRank_le_of_subgroup p hp.one_lt J
  have hrkJ : CFSG.pRank p J = 2 := by omega
  have hsat : CFSG.pRank p J = CFSG.pRank p (H ⧸ C) := by omega
  obtain ⟨hcen, hinc⟩ := SteinbergBT.rank_saturating_prime_centralizer_and_inner_containment hp J
    hZ hsat
  have hpJ : p ∣ Nat.card J := prime_dvd_card_of_pRank_pos hp (by omega)
  have hJconj : ∀ e : H ⧸ C, CFSG.conjugate J e = J := by
    intro e
    by_contra hne
    have hJe := NQTerm.isComponent_conjugate hJ e
    rcases CFSG.LocalCores.distinct_components_commute hJ hJe with h1 | h1
    · exact hne h1.symm
    · apply hcen
      have h2 : CFSG.conjugate J e ≤ centralizer (J : Set (H ⧸ C)) := by
        rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
        exact h1
      have h3 : Nat.card (CFSG.conjugate J e) = Nat.card J :=
        card_map_of_injective (MulAut.conj e⁻¹).injective
      have h4 : p ∣ Nat.card (CFSG.conjugate J e) := by
        rw [h3]
        exact hpJ
      exact h4.trans (card_dvd_of_le h2)
  have hJn : J.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 := hJconj g⁻¹
    rw [CFSG.conjugate, inv_inv] at h1
    rw [← h1]
    exact ⟨n, hn, rfl⟩
  have hKn : K.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : CFSG.conjugate K g⁻¹ = K := by
      apply eq_of_map_eq_of_isCComponent hCsolv (isCComponent_conjugate hK g⁻¹) hK
      rw [map_conjugate_hom]
      exact hJconj _
    rw [CFSG.conjugate, inv_inv] at h1
    rw [← h1]
    exact ⟨n, hn, rfl⟩
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := isPGroup_coreQuot_of_pow_mem Q hQ2 hpow
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p X))
  set P : Subgroup H := (P₀ : Subgroup X).map X.subtype with hP
  have hPX : P ≤ X := map_subtype_le _
  have hPp : IsPGroup p (P.map π) := (P₀.isPGroup'.map X.subtype).map π
  have hPJ : P.map π ≤ J := by
    refine hinc (P.map π) hPp ?_ ?_
    · rw [normalizer_eq_top_iff.mpr hJn]
      exact le_top
    · exact fun x hx => hinner x (map_mono hPX hx)
  have hPKC : P ≤ K ⊔ C := by
    intro x hx
    have h1 : π x ∈ J := hPJ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := h1
    have h2 : k⁻¹ * x ∈ C := by
      rw [← QuotientGroup.eq]
      exact hkx
    have h4 := mul_mem (mem_sup_left hk : k ∈ K ⊔ C) (mem_sup_right h2 : k⁻¹ * x ∈ K ⊔ C)
    rwa [mul_inv_cancel_left] at h4
  have hKCn : (K ⊔ C).Normal := inferInstance
  have hXKC : X ≤ K ⊔ C := by
    have h1 : X ≤ X ⊓ (K ⊔ C) := by
      refine le_of_noPQuotient_two hX2 le_rfl inf_le_left (le_normalizer_inf_of_normal hKCn) ?_
      · have hPN : (P₀ : Subgroup X) ≤ (X ⊓ (K ⊔ C)).subgroupOf X := by
          intro y hy
          rw [mem_subgroupOf]
          exact ⟨y.2, hPKC ⟨y, hy, rfl⟩⟩
        obtain ⟨k, hk⟩ := index_dvd_two_pow_of_sylow_le hp2 hXp P₀ hPN
        exact ⟨k, hk⟩
    exact h1.trans inf_le_right
  refine ⟨hinner, hrkJ, hKn, ?_⟩
  refine le_of_noPQuotient_two hX2 hXKC le_sup_left ?_ ?_
  · rw [normalizer_eq_top_iff.mpr hKn]
    exact le_top
  · obtain ⟨k, hk⟩ := hC.exists_card_eq
    refine ⟨k, ?_⟩
    rw [sup_comm, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal C K, ← hk]
    exact relIndex_dvd_card K C

theorem stmtOuterRankContainment_holds : StmtOuterRankContainment :=
  fun _ _ _ _ hp hp2 hpH C _ hC _ hK hJ hZ hOut _ _ Q _ hXA hAK hAQ hAX hQ2 hpow hX2 hdim hlat
      hJX =>
    irreducible_component_normalizer_outer_rank_forces_containment hp hp2 hpH C hC hK hJ hZ hOut
      Q hXA hAK hAQ hAX hQ2 hpow hX2 hdim hlat hJX

end CFSG.Quasithin.H13.NQRigid
