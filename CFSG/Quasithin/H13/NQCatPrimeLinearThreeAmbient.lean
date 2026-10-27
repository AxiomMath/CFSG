module

public import CFSG.Quasithin.H13.NQCatPrimeLinearThreeAffine
public import CFSG.Quasithin.H13.NQCatExcludesSmallMatrix
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup Module CFSG.Quasithin CFSG.Wreathed.OddLinearThreeCentralizerCore
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar

@[expose] noncomputable def ambientMap {K : Type*} [Group K] {F : Type*} [Field F]
    {D : Subgroup (SL3 F)} [D.Normal] (α : K ⧸ CFSG.pCore 2 K ≃* SL3 F ⧸ D) :
    K →* SL3 F ⧸ D :=
  α.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 K))

theorem isElementaryAbelian_of_mulEquiv {G H : Type*} [Group G] [Group H] {p : ℕ} (e : G ≃* H)
    (hH : IsElementaryAbelian p H) : IsElementaryAbelian p G :=
  CFSG.IsElementaryAbelian.of_mulEquiv e.symm hH

theorem exists_elementaryAbelian_of_pRank {P : Type*} [Group P] [Finite P] {p r : ℕ}
    (hp : 1 < p) (hr : CFSG.pRank p P = r) (hr0 : r ≠ 0) :
    ∃ E : Subgroup P, IsElementaryAbelian p E ∧ Nat.card E = p ^ r := by
  set s : Set ℕ := {r : ℕ | ∃ E : Subgroup P, IsElementaryAbelian p E ∧ Nat.card E = p ^ r}
    with hs
  have hne : s.Nonempty := by
    rcases Set.eq_empty_or_nonempty s with h | h
    · exfalso
      apply hr0
      rw [← hr]
      change sSup s = 0
      rw [h, csSup_empty]
      rfl
    · exact h
  have hbdd : BddAbove s := by
    refine ⟨Nat.card P, fun n hn => ?_⟩
    obtain ⟨E, -, hE⟩ := hn
    have h1 : p ^ n ≤ Nat.card P := hE ▸ Subgroup.card_le_card_group E
    exact ((Nat.lt_pow_self hp).trans_le h1).le
  have hmem : CFSG.pRank p P ∈ s := Nat.sSup_mem hne hbdd
  rw [hr] at hmem
  exact hmem

variable {F : Type} [Field F] [Finite F]

theorem prime_linear_three_ambient_model_identifies_original_witness_with_actual_unipotent_plane
    (hI : OddLinearThreeInvolutionSylowStructure F) {K : Type}
    [Group K] [Finite K] {q : ℕ} [hq : Fact q.Prime] (hFq : Nat.card F = q) (hq5 : 5 ≤ q)
    (D : Subgroup (SL3 F)) [D.Normal] (hD : D ≤ scalars 3 F) (α : K ⧸ CFSG.pCore 2 K ≃* SL3 F ⧸ D)
    (S : Sylow 2 K) {A : Subgroup K} (hA : A ∈ cComp (A ⊔ (S : Subgroup K)))
    (hAq : ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A)) {p : ℕ} [hp : Fact p.Prime]
    (_hp2 : p ≠ 2) {X : Subgroup K} (hXA : X ≤ A) (hXn : (X.subgroupOf A).Normal)
    (hX2 : ∀ (Y : Subgroup ↥X) [Y.Normal], IsPGroup 2 (↥X ⧸ Y) → Y = ⊤)
    (hXp : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X)) (hXr : CFSG.pRank p (↥X ⧸ CFSG.pCore 2 ↥X) = 2) :
    p = q ∧ ∃ V : Submodule F (Fin 3 → F), (finrank F V = 1 ∨ finrank F V = 2) ∧
      (A ⊔ (S : Subgroup K)).map (ambientMap α) ≤ (stabilizer V).map (QuotientGroup.mk' D) ∧
      A.map (ambientMap α) = (CFSG.perfectResidual ↥((stabilizer V).map (QuotientGroup.mk' D))).map
        ((stabilizer V).map (QuotientGroup.mk' D)).subtype ∧
      X.map (ambientMap α) = (radU F V).map (QuotientGroup.mk' D) ∧
      A ⊓ CFSG.pCore 2 K = (CFSG.pCore 2 ↥A).map A.subtype ∧
      X ⊓ CFSG.pCore 2 K = (CFSG.pCore 2 ↥X).map X.subtype ∧
      (∃ e : ↥A ⧸ CFSG.pCore 2 ↥A ≃* ↥(A.map (ambientMap α)),
        ∀ a : ↥A, (e (QuotientGroup.mk a) : SL3 F ⧸ D) = ambientMap α a) ∧
      (∃ e : ↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥(X.map (ambientMap α)),
        (∀ x : ↥X, (e (QuotientGroup.mk x) : SL3 F ⧸ D) = ambientMap α x) ∧
        ∀ (a : ↥A) (x y : ↥X), (y : K) = a * x * (a : K)⁻¹ →
          (e (QuotientGroup.mk y) : SL3 F ⧸ D) =
            ambientMap α a * e (QuotientGroup.mk x) * (ambientMap α a)⁻¹) ∧
      IsElementaryAbelian p (↥X ⧸ CFSG.pCore 2 ↥X) ∧ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) = p ^ 2 ∧
      (finrank F V = 2 → ∃ s : SL3 F, (flagSpace 3 F 2).map (Matrix.mulVecLin s.val) = V ∧
        Function.Injective ((QuotientGroup.mk' D).comp (natTheta F s)) ∧
        ((QuotientGroup.mk' D).comp (natTheta F s)).range = A.map (ambientMap α) ∧
        (((QuotientGroup.mk' D).comp (natTheta F s)).comp SemidirectProduct.inl).range =
          X.map (ambientMap α) ∧
        ∀ (y : Multiplicative (Matrix (Fin 2) (Fin 1) F) ⋊[phiL F (Fin 1)]
            Matrix.SpecialLinearGroup (Fin 2) F) (Z : Multiplicative (Matrix (Fin 2) (Fin 1) F)),
          QuotientGroup.mk' D (natTheta F s y) *
              QuotientGroup.mk' D (natTheta F s (SemidirectProduct.inl Z)) *
              (QuotientGroup.mk' D (natTheta F s y))⁻¹ =
            QuotientGroup.mk' D (natTheta F s (SemidirectProduct.inl
              (Multiplicative.ofAdd (y.right.val * Multiplicative.toAdd Z))))) ∧
      (finrank F V = 1 → ∃ s : SL3 F, (flagSpace 3 F 1).map (Matrix.mulVecLin s.val) = V ∧
        Function.Injective ((QuotientGroup.mk' D).comp (dualTheta F s)) ∧
        ((QuotientGroup.mk' D).comp (dualTheta F s)).range = A.map (ambientMap α) ∧
        (((QuotientGroup.mk' D).comp (dualTheta F s)).comp SemidirectProduct.inl).range =
          X.map (ambientMap α) ∧
        ∀ (y : Multiplicative (Matrix (Fin 1) (Fin 2) F) ⋊[phiR F (Fin 1)]
            Matrix.SpecialLinearGroup (Fin 2) F) (Z : Multiplicative (Matrix (Fin 1) (Fin 2) F)),
          QuotientGroup.mk' D (dualTheta F s y) *
              QuotientGroup.mk' D (dualTheta F s (SemidirectProduct.inl Z)) *
              (QuotientGroup.mk' D (dualTheta F s y))⁻¹ =
            QuotientGroup.mk' D (dualTheta F s (SemidirectProduct.inl
              (Multiplicative.ofAdd (Multiplicative.toAdd Z * (y.right⁻¹).val))))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup K := CFSG.pCore 2 K with hN
  have hN2 : IsPGroup 2 ↥N := CFSG.pCore_isPGroup
  set ψ : K →* SL3 F ⧸ D := ambientMap α with hψ
  have hψs : Function.Surjective ψ := α.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ∀ x : K, ψ x = 1 ↔ x ∈ N := fun x => by
    rw [hψ, ambientMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hkerψ : ψ.ker = N := by
    ext x
    exact hψker x
  have hkerS : Group.IsSolvable ↥ψ.ker := by
    rw [hkerψ]
    have := hN2.isNilpotent
    infer_instance
  set T : Sylow 2 (SL3 F ⧸ D) := S.mapSurjective hψs with hT
  have hTcoe : (T : Subgroup (SL3 F ⧸ D)) = (S : Subgroup K).map ψ := Sylow.coe_mapSurjective _ _
  have hB : A.map ψ ∈ cComp (A.map ψ ⊔ (T : Subgroup (SL3 F ⧸ D))) := by
    rw [hTcoe, ← Subgroup.map_sup]
    exact LocDbl.map_mem_cComp_of_ker ψ hkerS hA
  have hker2 : IsPGroup 2 ↥(ψ.subgroupMap A).ker := by
    intro x
    have hxN : ((x : ↥A) : K) ∈ N :=
      (hψker ((x : ↥A) : K)).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp x.2))
    obtain ⟨n, hn⟩ := hN2 ⟨_, hxN⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have h2 := congrArg Subtype.val hn
    simpa using h2
  have hBq : ¬ CFSG.IsQuasisimple ↥(A.map ψ) := by
    intro hq
    apply hAq
    obtain ⟨e⟩ := quotient_pCore_mulEquiv_of_surjective (ψ.subgroupMap A)
      (ψ.subgroupMap_surjective A) hker2
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2
      (isQuasisimple_quotient_pCore_of_isQuasisimple hq)
  obtain ⟨hO2M, V, hVdim, hMP, hBres, hUle, hUel, hUcard, ⟨lam, hlams, hlamker⟩, hnat, hdual⟩ :=
    prime_linear_three_nonquasisimple_local_actual_affine_production hI hFq hq5 D hD T hBq hB
  have hMP' : (A ⊔ (S : Subgroup K)).map ψ ≤ (stabilizer V).map (QuotientGroup.mk' D) := by
    rw [Subgroup.map_sup, ← hTcoe]
    exact hMP
  have hO2B : CFSG.pCore 2 ↥(A.map ψ) = ⊥ := by
    have hBMs := (mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hB)).2.2.1
    have h1 := map_pCore_le_pCore_of_isSubnormal' (p := 2) hBMs
    rw [hO2M, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (subtype_injective _)] at h1
    have h2 := CFSG.LieType.SteinbergBR.pCore_map_equiv 2
      (subgroupOfEquivOfLe (le_sup_left : A.map ψ ≤ A.map ψ ⊔ (T : Subgroup (SL3 F ⧸ D))))
    rw [h1, Subgroup.map_bot] at h2
    exact h2.symm
  have h4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four_of_le (by omega)
  have hSLq := isQuasisimple_SL2_of_four h4
  have hXB : X.map ψ ≤ A.map ψ := map_mono hXA
  let μ : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F :=
    lam.comp ((Subgroup.inclusion hXB).comp (ψ.subgroupMap X))
  have hXsolv : Group.IsSolvable ↥X := by
    have : Group.IsSolvable ↥(CFSG.pCore 2 ↥X) := by
      have := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).isNilpotent
      infer_instance
    have : Group.IsSolvable (↥X ⧸ CFSG.pCore 2 ↥X) := by
      have := hXp.isNilpotent
      infer_instance
    exact Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥X).subtype
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
      ((QuotientGroup.ker_mk' _).le.trans (range_subtype _).ge)
  have hμnorm : μ.range.Normal := by
    refine ⟨fun m hm g => ?_⟩
    obtain ⟨x, rfl⟩ := hm
    obtain ⟨b, rfl⟩ := hlams g
    obtain ⟨a, ha, hab⟩ := b.2
    have hy : (a : K) * x * a⁻¹ ∈ X := by
      have := hXn.conj_mem ⟨x, hXA x.2⟩ (mem_subgroupOf.mpr x.2) ⟨a, ha⟩
      exact mem_subgroupOf.mp this
    refine ⟨⟨_, hy⟩, ?_⟩
    have hb : b = ⟨ψ a, a, ha, rfl⟩ := Subtype.ext hab.symm
    subst hb
    change lam (Subgroup.inclusion hXB (ψ.subgroupMap X ⟨_, hy⟩)) =
      lam ⟨ψ a, a, ha, rfl⟩ * lam (Subgroup.inclusion hXB (ψ.subgroupMap X x)) *
        (lam ⟨ψ a, a, ha, rfl⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [map_mul, map_inv]
  have hμcen : μ.range ≤ center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hSLq hμnorm with htop | hc
    · exfalso
      apply not_isSolvable_of_isQuasisimple hSLq
      have : Group.IsSolvable ↥μ.range :=
        Group.isSolvable_of_surjective μ.rangeRestrict_surjective
      have h1 : Group.IsSolvable ↥(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
        htop ▸ this
      exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup _).subtype)
        fun g => ⟨⟨g, mem_top g⟩, rfl⟩
    · exact hc
  have hμ2 : IsPGroup 2 ↥μ.range := by
    intro m
    obtain ⟨r, hr, hrm⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hμcen m.2)
    rw [Fintype.card_fin] at hr
    have hm2 : (m : Matrix.SpecialLinearGroup (Fin 2) F) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, ← hrm, ← map_pow,
        hr, map_one]
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hm2, Subgroup.coe_one])⟩
  have hμker : μ.ker = ⊤ := hX2 μ.ker (hμ2.of_equiv (QuotientGroup.quotientKerEquivRange μ).symm)
  have hXU : X.map ψ ≤ (radU F V).map (QuotientGroup.mk' D) := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : μ ⟨x, hx⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hμker]
      exact mem_top _
    have h2 : (⟨ψ x, x, hXA hx, rfl⟩ : ↥(A.map ψ)) ∈ lam.ker := h1
    rw [hlamker, mem_subgroupOf] at h2
    exact h2
  have hUq : IsPGroup q ↥((radU F V).map (QuotientGroup.mk' D)) := by
    have := hUel
    exact IsElementaryAbelian.isPGroup q _
  have hq2 : (2 : ℕ) ≠ q := by omega
  have hXN : X ⊓ N = (CFSG.pCore 2 ↥X).map X.subtype := by
    apply le_antisymm
    · rintro y ⟨hyX, hyN⟩
      refine ⟨⟨y, hyX⟩, ?_, rfl⟩
      have hle : N.subgroupOf X ≤ CFSG.pCore 2 ↥X := by
        apply le_sSup
        refine ⟨inferInstance, fun z => ?_⟩
        obtain ⟨n, hn⟩ := hN2 ⟨_, mem_subgroupOf.mp z.2⟩
        refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
        have h2 := congrArg Subtype.val hn
        simpa using h2
      exact hle (mem_subgroupOf.mpr hyN)
    · rintro _ ⟨o, ho, rfl⟩
      refine ⟨o.2, (hψker _).mp ?_⟩
      have hdisj := IsPGroup.disjoint_of_ne 2 q hq2 ((CFSG.pCore 2 ↥X).map (ψ.comp X.subtype))
        ((radU F V).map (QuotientGroup.mk' D)) (CFSG.pCore_isPGroup.map _) hUq
      have h1 : ψ o ∈ (CFSG.pCore 2 ↥X).map (ψ.comp X.subtype) := ⟨o, ho, rfl⟩
      have h2 : ψ o ∈ (radU F V).map (QuotientGroup.mk' D) := hXU ⟨o, o.2, rfl⟩
      exact (Subgroup.disjoint_def.mp hdisj) h1 h2
  have hAN : A ⊓ N = (CFSG.pCore 2 ↥A).map A.subtype := by
    apply le_antisymm
    · rintro y ⟨hyA, hyN⟩
      refine ⟨⟨y, hyA⟩, ?_, rfl⟩
      have hle : N.subgroupOf A ≤ CFSG.pCore 2 ↥A := by
        apply le_sSup
        refine ⟨inferInstance, fun z => ?_⟩
        obtain ⟨n, hn⟩ := hN2 ⟨_, mem_subgroupOf.mp z.2⟩
        refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
        have h2 := congrArg Subtype.val hn
        simpa using h2
      exact hle (mem_subgroupOf.mpr hyN)
    · rintro _ ⟨o, ho, rfl⟩
      refine ⟨o.2, (hψker _).mp ?_⟩
      have hle : (CFSG.pCore 2 ↥A).map (ψ.subgroupMap A) ≤ CFSG.pCore 2 ↥(A.map ψ) := by
        have : (CFSG.pCore 2 ↥A).Normal := CFSG.pCore_normal
        exact le_sSup ⟨this.map _ (ψ.subgroupMap_surjective A), CFSG.pCore_isPGroup.map _⟩
      have h1 := hle ⟨o, ho, rfl⟩
      rw [hO2B, mem_bot] at h1
      exact congrArg Subtype.val h1
  have hkerA : (ψ.subgroupMap A).ker = CFSG.pCore 2 ↥A := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      have h1 : (a : K) ∈ A ⊓ N := ⟨a.2, (hψker _).mp (congrArg Subtype.val ha)⟩
      rw [hAN] at h1
      obtain ⟨b, hb, hba⟩ := h1
      exact (Subtype.ext hba : b = a) ▸ hb
    · intro ha
      have h1 : (a : K) ∈ A ⊓ N := by
        rw [hAN]
        exact ⟨a, ha, rfl⟩
      exact Subtype.ext ((hψker _).mpr h1.2)
  have hkerX : (ψ.subgroupMap X).ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (x : K) ∈ X ⊓ N := ⟨x.2, (hψker _).mp (congrArg Subtype.val hx)⟩
      rw [hXN] at h1
      obtain ⟨b, hb, hbx⟩ := h1
      exact (Subtype.ext hbx : b = x) ▸ hb
    · intro hx
      have h1 : (x : K) ∈ X ⊓ N := by
        rw [hXN]
        exact ⟨x, hx, rfl⟩
      exact Subtype.ext ((hψker _).mpr h1.2)
  let eA : ↥A ⧸ CFSG.pCore 2 ↥A ≃* ↥(A.map ψ) :=
    (QuotientGroup.quotientMulEquivOfEq hkerA.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (ψ.subgroupMap_surjective A))
  let eX : ↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥(X.map ψ) :=
    (QuotientGroup.quotientMulEquivOfEq hkerX.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (ψ.subgroupMap_surjective X))
  have heX : ∀ x : ↥X, (eX (QuotientGroup.mk x) : SL3 F ⧸ D) = ψ x := fun _ => rfl
  obtain ⟨E, -, hEcard⟩ := exists_elementaryAbelian_of_pRank hp.out.one_lt hXr (by norm_num)
  have hPcard : p ^ 2 ≤ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rw [← hEcard]
    exact Subgroup.card_le_card_group E
  have hcardX : Nat.card ↥(X.map ψ) = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) :=
    (Nat.card_congr eX.toEquiv).symm
  have hpq : p = q := by
    by_contra hpq
    have h1 : IsPGroup p ↥(X.map ψ) := hXp.of_equiv eX
    have h2 : IsPGroup q ↥(X.map ψ) := hUq.to_le hXU
    have hbot : X.map ψ = ⊥ := disjoint_self.mp (IsPGroup.disjoint_of_ne p q hpq _ _ h1 h2)
    have h3 : Nat.card ↥(X.map ψ) = 1 := by rw [hbot, card_bot]
    have h4 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.out.one_lt
    omega
  subst hpq
  have hXeq : X.map ψ = (radU F V).map (QuotientGroup.mk' D) := by
    refine Subgroup.eq_of_le_of_card_ge hXU ?_
    rw [hUcard, hcardX]
    exact hPcard
  refine ⟨rfl, V, hVdim, hMP', hBres, hXeq, hAN, hXN, ⟨eA, fun _ => rfl⟩,
    ⟨eX, heX, fun a x y hy => ?_⟩, ?_, ?_, fun hV2 => ?_, fun hV1 => ?_⟩
  · rw [heX, heX, hy, map_mul, map_mul, map_inv]
  · exact isElementaryAbelian_of_mulEquiv eX (hXeq ▸ hUel)
  · rw [← hcardX, hXeq, hUcard]
  · obtain ⟨s, hs, hinj, hrange, hU, -⟩ := hnat hV2
    refine ⟨s, hs, hinj, hrange, ?_, fun y Z => ?_⟩
    · rw [MonoidHom.comp_assoc, MonoidHom.range_comp, hU, hXeq]
    · have h := congrArg ((QuotientGroup.mk' D).comp (natTheta F s)) (conj_inl_eq y Z)
      simp only [map_mul, map_inv, MonoidHom.comp_apply] at h
      exact h
  · obtain ⟨s, hs, hinj, hrange, hU, -⟩ := hdual hV1
    refine ⟨s, hs, hinj, hrange, ?_, fun y Z => ?_⟩
    · rw [MonoidHom.comp_assoc, MonoidHom.range_comp, hU, hXeq]
    · have h := congrArg ((QuotientGroup.mk' D).comp (dualTheta F s)) (conj_inl_eq y Z)
      simp only [map_mul, map_inv, MonoidHom.comp_apply] at h
      exact h

end CFSG.Quasithin.H13.NQCat
