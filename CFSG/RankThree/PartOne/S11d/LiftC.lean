module

public import CFSG.RankThree.PartOne.S11d.FivePlusC
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace S11d

variable {G : Type} [Group G] [Finite G]

theorem ambient_two_commutator_lift_c {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A L N M R : Subgroup G} {c : G} (hA : IsPGroup p A)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hcA : c ∈ A)
    (hAL : A ≤ normalizer (L : Set G))
    (hNL : N ≤ L) (hNn : (N.subgroupOf L).Normal) (hAN : A ≤ normalizer (N : Set G))
    (hpN : ¬ p ∣ Nat.card N) (hML : M ≤ L) (hAM : A ≤ normalizer (M : Set G))
    (hLMN : L = M ⊔ N) (hRL : R ≤ L) (hR1 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hAR : A ≤ normalizer (R : Set G)) (hRc : ⁅R, zpowers c⁆ = R) (hRN : ⁅R ⊓ N, A⁆ = ⊥) :
    ∃ T : Subgroup G, T ≤ M ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ normalizer (T : Set G) ∧
      ⁅T, zpowers c⁆ = T := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hzA : zpowers c ≤ A := zpowers_le.mpr hcA
  have hzL : zpowers c ≤ normalizer (L : Set G) := hzA.trans hAL
  let _ : MulDistribMulAction A L := conjActionOn hAL
  let _ : MulDistribMulAction (zpowers c) L := conjActionOn hzL
  have hsmul : ∀ (a : A) (l : L), ((a • l : L) : G) = (a : G) * l * (a : G)⁻¹ := fun _ _ => rfl
  have hsmulC : ∀ (a : zpowers c) (l : L), ((a • l : L) : G) = (a : G) * l * (a : G)⁻¹ :=
    fun _ _ => rfl
  set N' := N.subgroupOf L with hN'
  have : N'.Normal := hNn
  have : CFSG.IsInvariant A L N' := ⟨fun a g => by
    rw [hN', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hsmul]
    exact Subgroup.mem_normalizer_iff.mp (hAN a.2) g⟩
  have : CFSG.IsInvariant (zpowers c) L N' := ⟨fun a g => by
    rw [hN', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hsmulC]
    exact Subgroup.mem_normalizer_iff.mp (hAN (hzA a.2)) g⟩
  have hpN' : ¬ p ∣ Nat.card N' := by
    rwa [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv]
  have h2C : ¬ 2 ∣ Nat.card (zpowers c) := not_two_dvd_card_zpowers hp hp2 hA hcA
  set M' := M.subgroupOf L with hM'
  have hMinv : ∀ a : A, ∀ x ∈ M', a • x ∈ M' := fun a x hx => by
    rw [hM', Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hAM a.2) x).mp hx
  have hLMN' : M' ⊔ N' = ⊤ := by
    rw [hM', hN', ← Subgroup.subgroupOf_sup hML hNL, ← hLMN, Subgroup.subgroupOf_self]
  set R' := R.subgroupOf L with hR'
  have hπA : ∀ (a : A) (l : L), (QuotientGroup.mk' N') (a • l) = a • (QuotientGroup.mk' N') l :=
    fun a l => (MulAction.Quotient.smul_mk (H := N') a l).symm
  have hπC : ∀ (a : zpowers c) (l : L),
      (QuotientGroup.mk' N') (a • l) = a • (QuotientGroup.mk' N') l :=
    fun a l => (MulAction.Quotient.smul_mk (H := N') a l).symm
  have hRinv : ∀ a : A, ∀ x ∈ R', a • x ∈ R' := fun a x hx => by
    rw [hR', Subgroup.mem_subgroupOf] at hx ⊢
    rw [hsmul]
    exact (Subgroup.mem_normalizer_iff.mp (hAR a.2) x).mp hx
  have hRinvC : ∀ a : zpowers c, ∀ x ∈ R', a • x ∈ R' := fun a x hx =>
    hRinv ⟨(a : G), hzA a.2⟩ x hx
  have hR'c : actionCommutator (zpowers c) R' = R' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [SteinbergBM.map_actionCommutator_conj hzL R', hR', Subgroup.map_subgroupOf_eq_of_le hRL,
      hRc]
  set E := R'.map (QuotientGroup.mk' N') with hE
  have hE1 : E ≠ ⊥ := by
    intro hE0
    have hle : R ≤ N := by
      intro r hr
      have hrL : r ∈ L := hRL hr
      have : (QuotientGroup.mk' N') ⟨r, hrL⟩ ∈ E := Subgroup.mem_map_of_mem _ (by
        rw [hR', Subgroup.mem_subgroupOf]; exact hr)
      rw [hE0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    apply hR1
    rw [← hRc, ← inf_eq_left.mpr hle]
    exact le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hzA).trans hRN.le)
  have hE2 : IsPGroup 2 E := (hR2.comap_subtype).map _
  have hEinv : ∀ a : A, ∀ x ∈ E, a • x ∈ E := by
    rintro a _ ⟨r, hr, rfl⟩
    exact ⟨a • r, hRinv a r hr, hπA a r⟩
  have hEC : actionCommutator (zpowers c) E = E := by
    rw [← SteinbergBM.map_actionCommutator (QuotientGroup.mk' N') hπC R', hR'c]
  have hcA' : ∀ (a : zpowers c) (x : L ⧸ N'), a • x = (⟨(a : G), hzA a.2⟩ : A) • x := by
    intro a x
    induction x using QuotientGroup.induction_on with
    | H l => rfl
  have hEA : actionCommutator A E = E := by
    refine le_antisymm (SteinbergBM.actionCommutator_le_of_invariant hEinv) ?_
    refine hEC.symm.le.trans ((closure_le _).2 ?_)
    rintro _ ⟨h, hh, a, rfl⟩
    rw [hcA']
    exact gen_mem_actionCommutator (A := A) hh ⟨(a : G), hzA a.2⟩
  obtain ⟨T', hT'M, hT'1, hT'2, hT'inv, hT'A, hT'π⟩ :=
    SteinbergBM.coprime_two_commutator_lifts_through_invariant_supplement hp hp2 hA N' hpN' M'
      hMinv hLMN' E hE1 hE2 hEinv hEA
  have hT'invC : ∀ a : zpowers c, ∀ x ∈ T', a • x ∈ T' := fun a x hx =>
    hT'inv ⟨(a : G), hzA a.2⟩ x hx
  have hBCL : ∀ (b : A) (a : zpowers c) (x : L), b • (a • x) = a • (b • x) := by
    intro b a x
    apply Subtype.ext
    have hbc : (b : G) * (a : G) = (a : G) * (b : G) := hAcomm b b.2 a (hzA a.2)
    change (b : G) * ((a : G) * x * (a : G)⁻¹) * (b : G)⁻¹ =
      (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
    calc (b : G) * ((a : G) * x * (a : G)⁻¹) * (b : G)⁻¹
        = ((b : G) * (a : G)) * x * ((b : G) * (a : G))⁻¹ := by group
      _ = ((a : G) * (b : G)) * x * ((a : G) * (b : G))⁻¹ := by rw [hbc]
      _ = (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹ := by group
  set T'c : Subgroup L := actionCommutator (zpowers c) T' with hT'c
  have hT'cle : T'c ≤ T' := SteinbergBM.actionCommutator_le_of_invariant hT'invC
  have hT'cinv : ∀ b : A, ∀ x ∈ T'c, b • x ∈ T'c := fun b x hx =>
    smul_mem_actionCommutator_of_comm hBCL hT'inv b hx
  have hmapT : T'c.map (QuotientGroup.mk' N') = E := by
    rw [hT'c, SteinbergBM.map_actionCommutator (QuotientGroup.mk' N') hπC T', hT'π, hEC]
  have hT'c1 : T'c ≠ ⊥ := by
    intro h
    rw [h, Subgroup.map_bot] at hmapT
    exact hE1 hmapT.symm
  have hT'c2 : IsPGroup 2 T'c := hT'2.to_le hT'cle
  have hT'cc : actionCommutator (zpowers c) T'c = T'c :=
    SteinbergBM.actionCommutator_actionCommutator_of_isPGroup Nat.prime_two hT'2 h2C hT'invC
  set T := T'c.map L.subtype with hT
  have hfwd : ∀ a ∈ A, ∀ g ∈ T, a * g * a⁻¹ ∈ T := by
    rintro a ha _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map.mpr ⟨((⟨a, ha⟩ : A) • x), hT'cinv ⟨a, ha⟩ x hx, rfl⟩
  refine ⟨T, ?_, ?_, hT'c2.map _, le_normalizer_of_conj_mem_forall hfwd, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hT'M (hT'cle hx))
  · intro h
    exact hT'c1 ((Subgroup.map_eq_bot_iff_of_injective T'c L.subtype_injective).mp h)
  · rw [← SteinbergBM.map_actionCommutator_conj hzL T'c, hT'cc]

end S11d

end CFSG.RankThree.PartOne
