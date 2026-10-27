module

public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsMaxParabolicOver)
open CFSG.Blueprint (LieModel)

section Sp4

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.CatalogueBSymplecticTwo

theorem isMaxParabolicOver_top_of_isCoatom {Y : Type} [Group Y] {S P : Subgroup Y}
    (hP : IsCoatom P) (hN : normalizer (S : Set Y) ≤ P) :
    IsMaxParabolicOver (⊤ : Subgroup Y) S P := by
  refine ⟨le_top, fun x hx => hN hx.2, hP.1, fun Q hPQ _ => ?_⟩
  rcases eq_or_ne Q P with h | h
  · exact Or.inl h
  · exact Or.inr (hP.2 Q (lt_of_le_of_ne hPQ (Ne.symm h)))

theorem psp4_mem_inner_of_mem_typeKernel {K : Type} [Field K] [Finite K] {n : ℕ}
    (hodd : Odd n) (hK : Nat.card K = 2 ^ n) {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : α ∈ typeKernel K) (hpow : ∃ k : ℕ, α ^ 2 ^ k = 1) :
    α ∈ inner (StatedProj (StatedSp 2 K)) := by
  classical
  obtain ⟨k, hk⟩ := hpow
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hodd.pos hK
  obtain ⟨-, hgen, -, -⟩ := kernel_generation (K := K)
  obtain ⟨A, σ, rfl⟩ := hgen α hα
  have hA : conjAut 2 K A ∈ inner (StatedProj (StatedSp 2 K)) :=
    conjAut_mem_inner_of_isSquare
      (FiniteField.isSquare_of_char_two (ringChar.eq_iff.mpr hchar) _)
  have hσ : σ ^ n = 1 := by
    have h1 : σ ^ Nat.card (RingAut K) = 1 := pow_card_eq_one'
    rwa [(card_ringAut_and_isCyclic Nat.prime_two K hK).1] at h1
  set a : Outer (StatedProj (StatedSp 2 K)) :=
    QuotientGroup.mk (conjAut 2 K A * fieldAut 2 K σ) with ha
  have ha' : a = QuotientGroup.mk (fieldAut 2 K σ) := by
    rw [ha, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hA, one_mul]
  have han : a ^ n = 1 := by
    rw [ha', ← QuotientGroup.mk_pow, ← map_pow, hσ, map_one, QuotientGroup.mk_one]
  have hak : a ^ 2 ^ k = 1 := by
    rw [ha, ← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (2 ^ k) n := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1 : orderOf a = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hak)
      (orderOf_dvd_of_pow_eq_one han)
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1)

theorem exists_spMaximalParabolics_normalizer_le {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {S : Subgroup (StatedProj (StatedSp 2 K))}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ P ∈ spMaximalParabolics 2 K 2, normalizer (S : Set (StatedProj (StatedSp 2 K))) ≤ P := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  obtain ⟨hEM, hEXY, -, hptne, -, -, -, -⟩ :=
    @extremal_parabolics K _ _ 2 hfact hchar (2 ^ n) hK
  have hidx : ¬ 2 ∣ S.index := by
    have h2 := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at h2
  have hNne : normalizer (S : Set (StatedProj (StatedSp 2 K))) ≠ ⊤ := by
    intro htop
    obtain ⟨M, hM⟩ := hptne
    have hMmax : M ∈ spMaximalParabolics 2 K 2 := by
      rw [← hEM, hEXY]
      exact Or.inl hM
    obtain ⟨hMco, B₀, ⟨T, hT⟩, hB₀M⟩ := hMmax
    have hn : ((hS.2.1.toSylow hidx : Sylow 2 (StatedProj (StatedSp 2 K))) :
        Subgroup (StatedProj (StatedSp 2 K))).Normal := by
      rw [IsPGroup.toSylow_coe]
      exact Subgroup.normalizer_eq_top_iff.mp htop
    have hTT : T = hS.2.1.toSylow hidx := by
      have huniq := @Sylow.unique_of_normal _ _ 2 hfact _ _ hn
      exact (huniq.uniq T).trans (huniq.uniq _).symm
    have hB₀ : B₀ = ⊤ := by
      rw [← hT, hTT, IsPGroup.toSylow_coe]
      exact htop
    exact hMco.1 (eq_top_iff.mpr (hB₀ ▸ hB₀M))
  obtain ⟨P, hPco, hNP⟩ := (IsCoatomic.eq_top_or_exists_le_coatom
    (normalizer (S : Set (StatedProj (StatedSp 2 K))))).resolve_left hNne
  exact ⟨P, ⟨hPco, normalizer (S : Set (StatedProj (StatedSp 2 K))),
    ⟨hS.2.1.toSylow hidx, rfl⟩, hNP⟩, hNP⟩

theorem mem_typeKernel_of_map_eq {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {α : MulAut (StatedProj (StatedSp 2 K))}
    {P : Subgroup (StatedProj (StatedSp 2 K))} (hP : P ∈ spMaximalParabolics 2 K 2)
    (hαP : P.map α.toMonoidHom = P) : α ∈ typeKernel K := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
  obtain ⟨hEM, hEXY, hdisj, -, -, -, -, -⟩ :=
    @extremal_parabolics K _ _ 2 hfact hchar (2 ^ n) hK
  obtain ⟨hdich, -, -, -⟩ := @type_kernel K _ _ 2 hfact hchar
  have hPXY : P ∈ pointParabolics K ∪ planeParabolics K := by
    rw [← hEXY, hEM]
    exact hP
  obtain ⟨-, -, hcase⟩ := hdich α
  rcases hcase with ⟨hpt, -⟩ | ⟨hpt, hpl⟩
  · exact mem_typeKernel.mpr hpt
  · exfalso
    rcases hPXY with hp | hp
    · have hmem : P ∈ (fun M => M.map α.toMonoidHom) '' pointParabolics K := ⟨P, hp, hαP⟩
      rw [hpt] at hmem
      exact Set.disjoint_left.mp hdisj hp hmem
    · have hmem : P ∈ (fun M => M.map α.toMonoidHom) '' planeParabolics K := ⟨P, hp, hαP⟩
      rw [hpl] at hmem
      exact Set.disjoint_left.mp hdisj hmem hp

theorem sp4_twoAut_inner {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hodd : Odd n)
    (hSp : IsSp4 Y n) {S : Subgroup Y} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤)
    {α : MulAut Y} (hpow : ∃ k : ℕ, α ^ 2 ^ k = 1)
    (hfix : ∀ P : Subgroup Y, IsMaxParabolicOver (⊤ : Subgroup Y) S P →
      P.map α.toMonoidHom = P) :
    α ∈ inner Y := by
  classical
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hSp (by decide)
  have hmem : ∀ y : Y, e y ∈ S.map e.toMonoidHom ↔ y ∈ S := fun y =>
    ⟨fun ⟨z, hz, hzy⟩ => (e.injective hzy) ▸ hz, fun hy => ⟨y, hy, rfl⟩⟩
  obtain ⟨P', hP', hNP'⟩ := exists_spMaximalParabolics_normalizer_le hodd.pos hK
    (CFSG.Quasithin.A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hS)
  have hPco : IsCoatom (P'.map e.symm.toMonoidHom) := by
    have h1 := (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e.symm) P').mpr hP'.1
    rwa [MulEquiv.coe_mapSubgroup] at h1
  have hNP : normalizer (S : Set Y) ≤ P'.map e.symm.toMonoidHom := by
    intro x hx
    refine ⟨e x, hNP' ?_, e.symm_apply_apply x⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [hmem, ← map_inv e x, ← map_mul e x w, ← map_mul e (x * w) x⁻¹, hmem]
    exact Subgroup.mem_normalizer_iff.mp hx w
  have hαP := hfix _ (isMaxParabolicOver_top_of_isCoatom hPco hNP)
  have hα'P' : P'.map (MulAut.congr e α).toMonoidHom = P' := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨w, hw, rfl⟩
      have h1 : α (e.symm w) ∈ P'.map e.symm.toMonoidHom := by
        rw [← hαP]
        exact ⟨e.symm w, ⟨w, hw, rfl⟩, rfl⟩
      obtain ⟨w', hw', hw'eq⟩ := h1
      change e (α (e.symm w)) ∈ P'
      rw [← hw'eq]
      change e (e.symm w') ∈ P'
      rw [MulEquiv.apply_symm_apply]
      exact hw'
    · rw [Subgroup.card_map_of_injective (f := (MulAut.congr e α).toMonoidHom)
        (MulAut.congr e α).injective]
  obtain ⟨k, hk⟩ := hpow
  have hin := psp4_mem_inner_of_mem_typeKernel hodd hK
    (mem_typeKernel_of_map_eq hodd.pos hK hP' hα'P') ⟨k, by rw [← map_pow, hk, map_one]⟩
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at hin
  obtain ⟨β, hβ, hβα⟩ := hin
  have hβα' : β = α := (MulAut.congr e).injective hβα
  rw [← hβα']
  exact hβ

end Sp4

private theorem card_outer_of_mulEquiv_adjoint_G2
    {K : Type} [fieldK : Field K] [finiteK : Finite K] {Y : Type} [Group Y] {n : ℕ}
    (h1 : 1 < n) (hK : Nat.card K = 2 ^ n)
    (e : Y ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :
    Nat.card (Outer Y) = n := by
  obtain ⟨-, Θ, -, hs, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
      (f := n) (by omega : 2 ≤ n) K hK
  have hker' : Θ.ker = inner (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := hker
  have hcardC : Nat.card (Outer (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) = n :=
    (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hs)).toEquiv).trans
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  exact (Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv).trans hcardC

theorem g2_twoAut_inner
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hodd : Odd n) (h1 : 1 < n)
    (hG2 : IsG2 Y n) (α : MulAut Y) (hα : ∃ k : ℕ, α ^ 2 ^ k = 1) :
    α ∈ inner Y := by
  classical
  obtain ⟨k, hk⟩ := hα
  have hcheb : CFSG.Blueprint.ChevalleyExceptionalModel Y .G2 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
  have hU : CFSG.Blueprint.UntwistedChevalleyModel Y .G2 (2 ^ n) := by
    simpa [CFSG.Blueprint.ChevalleyExceptionalModel] using hcheb.2
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) (q := 2 ^ n) hU
  have hcardY : Nat.card (Outer Y) = n :=
    card_outer_of_mulEquiv_adjoint_G2 (fieldK := hKf) (finiteK := hKfin) h1 hKcard e
  set a : Outer Y := QuotientGroup.mk α
  have ha1 : a ^ 2 ^ k = 1 := by rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Outer Y)) := by
    rw [hcardY]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h1' : orderOf a = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha1) (orderOf_dvd_natCard a)
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
