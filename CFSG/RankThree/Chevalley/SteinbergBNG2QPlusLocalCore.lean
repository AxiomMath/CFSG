module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusCentralizers

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog
open Subgroup
open scoped Pointwise commutatorElement

namespace SteinbergBN

theorem map_centralizer_singleton_of_injective {C M : Type*} [Group C] [Group M] (F : C →* M)
    (hF : Function.Injective F) (x : C) :
    (centralizer ({x} : Set C)).map F = F.range ⊓ centralizer ({F x} : Set M) := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hc]
  · rintro ⟨⟨c, rfl⟩, hc⟩
    refine ⟨c, mem_centralizer_singleton_iff.2 (hF ?_), rfl⟩
    rw [map_mul, map_mul]
    exact mem_centralizer_singleton_iff.1 hc

theorem exists_injective_of_map_le_torusGroup {C : Type*} [Group C] {L : Type} [Field L]
    (F : C →* ModGL .G2 L) (hF : Function.Injective F) {X : Subgroup C}
    (hX : X.map F ≤ torusGroup .G2 L) :
    ∃ φ : X →* (Fin Tag.G2.rank → Lˣ), Function.Injective φ := by
  obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) L
  have hmem : ∀ y : X, (F.comp X.subtype) y ∈ torusGroup .G2 L := fun y => hX ⟨y, y.2, rfl⟩
  refine ⟨e.symm.toMonoidHom.comp ((F.comp X.subtype).codRestrict _ hmem), ?_⟩
  refine e.symm.injective.comp fun y w h => Subtype.ext (hF ?_)
  exact congrArg (fun v : torusGroup .G2 L => (v : ModGL .G2 L)) h

theorem derived_centralizer_data_of_map {C : Type*} [Group C] {L : Type} [Field L]
    (F : C →* ModGL .G2 L) (hF : Function.Injective F) {x : C} {D Q : Subgroup (ModGL .G2 L)}
    (hmap : (centralizer ({x} : Set C)).map F = D) (hcomm : ⁅D, D⁆ = Q)
    (hQq : CFSG.IsQuasisimple Q)
    (hZ : D ⊓ centralizer (Q : Set (ModGL .G2 L)) = (center D).map D.subtype)
    (hZH : (center D).map D.subtype ≤ torusGroup .G2 L) :
    (⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ : Subgroup C).map F = Q ∧
      CFSG.IsQuasisimple (⁅centralizer ({x} : Set C), centralizer ({x} : Set C)⁆ :
        Subgroup C) ∧
      ∃ φ : (centralizer ({x} : Set C) ⊓ centralizer ((⁅centralizer ({x} : Set C),
          centralizer ({x} : Set C)⁆ : Subgroup C) : Set C) : Subgroup C) →*
            (Fin Tag.G2.rank → Lˣ), Function.Injective φ := by
  set Y := centralizer ({x} : Set C) with hY
  have hRmap : (⁅Y, Y⁆ : Subgroup C).map F = Q := by
    rw [Subgroup.map_commutator, hmap, hcomm]
  have eR : (⁅Y, Y⁆ : Subgroup C) ≃* Q :=
    (Subgroup.equivMapOfInjective _ F hF).trans (MulEquiv.subgroupCongr hRmap)
  refine ⟨hRmap, CFSG.LocalCores.isQuasisimple_of_mulEquiv eR.symm hQq,
    exists_injective_of_map_le_torusGroup F hF ?_⟩
  rintro _ ⟨z, ⟨hzY, hzR⟩, rfl⟩
  refine hZH (hZ ▸ Subgroup.mem_inf.2 ⟨hmap ▸ ⟨z, hzY, rfl⟩,
    Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩)
  rw [← hRmap] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hzR r hr]

theorem exists_quadratic_frobenius {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) :
    ∃ (K₂ : Type) (_ : Field K₂) (_ : Algebra K K₂), Module.finrank K K₂ = 2 ∧
      ∃ σ : K₂ ≃+* K₂, ∀ c, σ c = c ^ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨δ, hδ⟩ := FiniteField.exists_nonsquare hK2
  set P : Polynomial K := Polynomial.X ^ 2 - Polynomial.C δ with hP
  have hirr : Irreducible P := by
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro c hc
    exact hδ ⟨c, by rw [← hc, sq]⟩
  have : Fact (Irreducible P) := ⟨hirr⟩
  set pb := AdjoinRoot.powerBasis hirr.ne_zero with hpb
  have hdim : pb.dim = 2 := by
    rw [hpb, AdjoinRoot.powerBasis_dim, hP, Polynomial.natDegree_X_pow_sub_C]
  have : Module.Finite K (AdjoinRoot P) := pb.finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, by rw [pb.finrank, hdim],
    (FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot P)).toRingEquiv, fun c => ?_⟩
  rw [Nat.card_eq_fintype_card]
  change FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot P) c = c ^ Fintype.card K
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]

end SteinbergBN

open SteinbergBN

theorem odd_card_commutator_qplus_inner {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1) (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (t : B) (htE : t ∈ E) (ht1 : t ≠ 1)
    (htinn : (t : MulAut (adjointGroup .G2 K)) ∈
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ :
      Subgroup B)) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  set R := (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range with hR
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨-, Θ, -, -, hΘker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2 (Or.inr ⟨rfl, hℓ3⟩)
  obtain ⟨φ₀, -, -, hφgen, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ₀, hφgen⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius hK2
  obtain ⟨g, z, -, -, -, -, -, -, -, ⟨S₀, hS₀T⟩, -, hroot, hTuniq, hcases⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers K hKodd hp hp3 hpq K₂ hdeg σ hσ
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have hfin : Finite K₂ := Module.finite_of_finite K
  set ψ : ModGL .G2 K →* ModGL .G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂)) with hψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K K₂))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    (adjointGroup .G2 K).equivMapOfInjective ψ hψinj
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  obtain ⟨x, hx⟩ := htinn
  have htx : t = ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
  subst htx
  have htp : orderOf (⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B) = p := orderOf_eq_prime (hEpow _ htE) ht1
  have hxp : orderOf x = p := by
    rw [← orderOf_injective _ hinj x, ← htp, Subgroup.orderOf_mk]
  have hPx : IsPGroup p (Subgroup.zpowers (ε x)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, MulEquiv.orderOf_eq ε x, hxp, pow_one])
  obtain ⟨Q', hQ'⟩ := hPx.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (conjEntrywiseImage K g) Q' S₀
  have hux : MulAut.conj u • ε x ∈ (S₀ : Subgroup (conjEntrywiseImage K g)) := by
    have h1 : MulAut.conj u • ε x ∈ MulAut.conj u • (Q' : Subgroup (conjEntrywiseImage K g)) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' (Subgroup.mem_zpowers _))
    rwa [← Sylow.coe_subgroup_smul, hu] at h1
  set F : adjointGroup .G2 K →* ModGL .G2 K₂ := (conjEntrywiseImage K g).subtype.comp
    ((MulAut.conj u).toMonoidHom.comp ε.toMonoidHom) with hFdef
  have hF : Function.Injective F := (conjEntrywiseImage K g).subtype_injective.comp
    ((MulAut.conj u).injective.comp ε.injective)
  have hFT : F x ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g :=
    Subgroup.mem_subgroupOf.1 (hS₀T hux)
  obtain ⟨a, ha, -⟩ := hTuniq _ hFT
  have hFrange : F.range = conjEntrywiseImage K g := by
    rw [hFdef, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      ((MulAut.conj u).surjective.comp ε.surjective), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hmapF : (centralizer ({x} : Set (adjointGroup .G2 K))).map F =
      conjEntrywiseImage K g ⊓ centralizer {rootDiagUnit .G2 a} := by
    rw [map_centralizer_singleton_of_injective F hF x, hFrange, ← ha]
  have hTa : rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g := ha ▸ hFT
  have hao : orderOf (rootDiagUnit .G2 a) = p := by
    rw [ha, orderOf_injective F hF x, hxp]
  set b : B := ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ with hb
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set B)) with hS
  have hSM : S ≤ centralizer ({b} : Set B) := Subgroup.map_subtype_le _
  have hEM : E ≤ centralizer ({b} : Set B) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val
      (hE.is_comm.comm (⟨b, htE⟩ : E) ⟨e, he⟩)).symm
  have hfixM : ∀ m ∈ centralizer ({b} : Set B), (m : MulAut (adjointGroup .G2 K)) x = x :=
    fun m hm => apply_eq_of_commute_conj hinj
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hm))
  have hgenY : ∀ s ∈ S, ∀ e ∈ E, ∃ c ∈ centralizer ({x} : Set (adjointGroup .G2 K)),
      MulAut.conj c = ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) := by
    intro s hs e he
    have hct : ⁅s, e⁆ ∈ centralizer ({b} : Set B) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hSM hs) (hEM he)) (inv_mem (hSM hs))) (inv_mem (hEM he))
    have hΘ : ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) ∈ R := by
      rw [hR, ← hΘker, MonoidHom.mem_ker, show ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) =
        ⁅(s : MulAut (adjointGroup .G2 K)), (e : MulAut (adjointGroup .G2 K))⁆ from
          map_commutatorElement B.subtype s e, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact IsMulCommutative.is_comm.comm _ _
    obtain ⟨c, hc⟩ := hΘ
    refine ⟨c, Subgroup.mem_centralizer_singleton_iff.2 (hinj ?_), hc⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hct)
    simp only [Subgroup.coe_mul] at h1
    rw [map_mul, map_mul, hc]
    exact h1
  by_cases hkerE : rootCharKernel a = ∅
  ·
    obtain ⟨hDT, -, -⟩ := (hcases a hTa hao).1 hkerE
    obtain ⟨φ, hφ⟩ := exists_injective_of_map_le_torusGroup F hF
      (X := centralizer ({x} : Set (adjointGroup .G2 K))) (by
        rw [hmapF, hDT]
        exact inf_le_left)
    refine odd_card_commutator_of_invariant hinj hB x le_rfl
      (fun η hη z hz => apply_mem_centralizer_of_apply_eq hη hz) φ hφ hp hp3
      (IsElementaryAbelian.isPGroup p E) hEM hSM ?_
    rw [Subgroup.commutator_le]
    intro s hs e he
    obtain ⟨c, hc, hce⟩ := hgenY s hs e he
    exact ⟨c, hc, hce⟩
  ·
    obtain ⟨α, hα, -, hcomm, hZ, hZH, -⟩ := (hcases a hTa hao).2 hkerE
    obtain ⟨_, -, hQq⟩ := hroot α hα
    obtain ⟨-, hRq, φ, hφ⟩ := derived_centralizer_data_of_map F hF hmapF hcomm hQq hZ hZH
    have hRY : (⁅centralizer ({x} : Set (adjointGroup .G2 K)),
        centralizer ({x} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ≤
        centralizer ({x} : Set (adjointGroup .G2 K)) :=
      Subgroup.commutator_le.2 fun u hu v hv => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hu hv) (inv_mem hu)) (inv_mem hv)
    have hfixR := aschbacherSolvableCore_fixes_quasisimple hinj hp hB x hRY
      (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hRq
    refine odd_card_commutator_of_invariant hinj hB x inf_le_left
      (fun η hη z hz => apply_mem_centralizer_derived_of_apply_eq hη hz) φ hφ hp hp3
      (IsElementaryAbelian.isPGroup p E) hEM hSM ?_
    rw [Subgroup.commutator_le]
    intro s hs e he
    obtain ⟨c, hc, hce⟩ := hgenY s hs e he
    refine ⟨c, Subgroup.mem_inf.2 ⟨hc, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩, hce⟩
    have he' : ((e : B) : MulAut (adjointGroup .G2 K))⁻¹ x = x := by
      nth_rewrite 1 [← hfixM e (hEM he)]
      exact MulAut.inv_apply_self _ _ _
    have h1 : (MulAut.conj c) r = r := by
      rw [hce, show ((⁅s, e⁆ : B) : MulAut (adjointGroup .G2 K)) =
        ⁅(s : MulAut (adjointGroup .G2 K)), (e : MulAut (adjointGroup .G2 K))⁆ from
          map_commutatorElement B.subtype s e]
      exact commutatorElement_apply_of_fixed (hfixR s hs r hr)
        (hfixR s hs _ (apply_mem_commutator_centralizer_of_apply_eq he' hr))
    rw [MulAut.conj_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm

end CFSG.RankThree.Chevalley

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.QuadraticSL2
  CFSG.RankThree.Classical
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups

namespace SteinbergBN

theorem exists_eq_pow_prime_pow {K : Type} [Field K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (σ' : K ≃+* K) : ∃ j : ℕ, ∀ c, σ' c = c ^ (ℓ ^ j) := by
  obtain ⟨φ₀, hφ₀, hord, hgen, -, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have hfin : IsOfFinOrder φ₀ := orderOf_pos_iff.mp (by rw [hord]; omega)
  have key : ∀ n : ℕ, ∀ c, (φ₀ ^ n) c = c ^ (ℓ ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro c
      rw [pow_succ φ₀ n]
      change (φ₀ ^ n) (φ₀ c) = _
      rw [hφ₀, ih, ← pow_mul, ← pow_succ']
  obtain ⟨j, hj⟩ := hfin.mem_powers_iff_mem_zpowers.mpr (hgen ▸ Subgroup.mem_top σ')
  refine ⟨j, fun c => ?_⟩
  rw [← hj]
  exact key j c

theorem exists_ringEquiv_eq_pow_prime_pow {L : Type} [Field L] {ℓ n : ℕ} (hℓ : ℓ.Prime)
    (hn : 1 ≤ n) (hL : Nat.card L = ℓ ^ n) (j : ℕ) : ∃ σ₂ : L ≃+* L, ∀ c, σ₂ c = c ^ (ℓ ^ j) := by
  obtain ⟨φ, hφ, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hn hL
  refine ⟨φ ^ j, ?_⟩
  induction j with
  | zero => simp
  | succ j ih =>
    intro c
    rw [pow_succ φ j]
    change (φ ^ j) (φ c) = _
    rw [hφ, ih, ← pow_mul, ← pow_succ']

theorem baseChangeGL_entrywise_comm {τ : Tag} {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]
    (σ' : K ≃+* K) (σ₂ : K₂ ≃+* K₂)
    (hcomm : ∀ c, σ₂ (algebraMap K K₂ c) = algebraMap K K₂ (σ' c)) (h : ModGL τ K) :
    baseChangeGL (algebraMap K K₂) (Units.map (entrywiseHom σ'.toRingHom) h) =
      Units.map (entrywiseHom (σ₂ : K₂ →+* K₂)) (baseChangeGL (algebraMap K K₂) h) := by
  have e : (algebraMap K K₂).comp σ'.toRingHom = (σ₂ : K₂ →+* K₂).comp (algebraMap K K₂) :=
    RingHom.ext fun c => (hcomm c).symm
  rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, e]

theorem units_map_entrywiseHom_mem_adjointGroup {τ : Tag} {L : Type} [Field L] (σ : L →+* L)
    {x : ModGL τ L} (hx : x ∈ adjointGroup τ L) :
    Units.map (entrywiseHom σ) x ∈ adjointGroup τ L := by
  rw [units_map_entrywiseHom_eq_baseChangeGL_self]
  exact baseChangeGL_mem_adjointGroup σ hx

theorem trace_semilinearConj {L : Type} [Field L] (M : GL (Fin 2) L) (σ : L ≃+* L)
    (X : SL(2, L)) :
    Matrix.trace (semilinearConj M σ X : Matrix (Fin 2) (Fin 2) L) =
      σ (Matrix.trace (X : Matrix (Fin 2) (Fin 2) L)) := by
  change Matrix.trace ((M : Matrix (Fin 2) (Fin 2) L) *
    (Matrix.SpecialLinearGroup.map (σ : L →+* L) X : Matrix (Fin 2) (Fin 2) L) *
      (↑M⁻¹ : Matrix (Fin 2) (Fin 2) L)) = _
  rw [Matrix.trace_units_conj, Matrix.trace_fin_two, Matrix.trace_fin_two, map_add]
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem exists_trace_eq_algebraMap {K K₂ : Type} [Field K] [Field K₂] [Algebra K K₂]
    (P : GL (Fin 2) K₂) (c : K) :
    ∃ X ∈ (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P),
      Matrix.trace (X : Matrix (Fin 2) (Fin 2) K₂) = algebraMap K K₂ c := by
  let X₀ : SL(2, K) := ⟨!![c, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  refine ⟨conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K K₂) X₀),
    ⟨_, ⟨X₀, rfl⟩, rfl⟩, ?_⟩
  rw [coe_conjSL, Matrix.trace_units_conj, Matrix.trace_fin_two,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.map_apply]
  simp [X₀]

end SteinbergBN

end CFSG.RankThree.Chevalley

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.QuadraticSL2
  CFSG.RankThree.Classical
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
open SteinbergBN

theorem thetaT_eq_bot_qplus_of_normalizer {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1)
    (hnorm : ∀ (L : Type) [Field L] [Finite L], Odd (Nat.card L) → p ∣ Nat.card L - 1 →
      ∀ v ∈ adjointGroup .G2 L, ∀ m : ℕ, (∀ x ∈ torusTorsion L p, v * x * v⁻¹ = x ^ m) →
        v ∈ torusGroup .G2 L ∨ ∃ hv : v ∈ monomialSubgroup .G2 L,
          ∀ w : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 L ⟨v, hv⟩ • w = -w)
    (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    thetaT p E = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hℓ.odd_of_ne_two hℓ2).pow
  set R := (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range with hR
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hNF0 := (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
    (Or.inr ⟨rfl, hℓ3⟩)).1
  have hNF := conj_normalForm_of_pointwise hNF0
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  by_cases hEinn : E.map B.subtype ≤ R
  swap
  ·
    obtain ⟨b, hbE, hbinn⟩ : ∃ b ∈ E, (b : MulAut (adjointGroup .G2 K)) ∉ R := by
      by_contra h
      push Not at h
      exact hEinn (by rintro _ ⟨b, hb, rfl⟩; exact h b hb)
    have hb1 : b ≠ 1 := fun h => hbinn (by rw [h]; exact one_mem _)
    have hbp : orderOf b = p := orderOf_eq_prime (hEpow b hbE) hb1
    obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF b
    have hcore := (odd_Chevalley_inner_field_noninner_prime_local_core_trivial .G2 hℓ hℓ2 hf K hK
      hNF hp B hB b hbinn hbp x σ hxσ).2.2.2
    refine eq_bot_iff.2 (iInf_le_of_le b (iInf_le_of_le hbE (iInf_le_of_le hb1 ?_)))
    rw [inSubgroup, hcore, Subgroup.map_bot]
  set P : Subgroup (adjointGroup .G2 K) := (E.map B.subtype).comap MulAut.conj with hPdef
  have hPmap : P.map MulAut.conj = E.map B.subtype := Subgroup.map_comap_eq_self hEinn
  have eP : E ≃* P := (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective).trans
    ((MulEquiv.subgroupCongr hPmap.symm).trans (Subgroup.equivMapOfInjective P _ hinj).symm)
  have hPcard : Nat.card P = p ^ 2 := by rw [← Nat.card_congr eP.toEquiv, hEcard]
  have hPp : IsPGroup p P := (IsElementaryAbelian.isPGroup p E).of_equiv eP
  have hPpow : ∀ u ∈ P, u ^ p = 1 := fun u hu => by
    obtain ⟨e, he, hee⟩ := hu
    apply hinj
    rw [map_pow, ← hee, map_one]
    exact congrArg Subtype.val (hEpow e he)
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius hK2
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have : Finite K₂ := Module.finite_of_finite K
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hK₂odd : Odd (Nat.card K₂) := by
    rw [hq2]
    exact hKodd.pow
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpq₂ : p ∣ Nat.card K₂ - 1 := by
    refine hpq.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  obtain ⟨g, z, hg, -, hzdef, ⟨hzN, hw⟩, hΓfix, -, -, ⟨S₀, hS₀T⟩, ⟨V, hV, -, hVcard, -, -⟩,
    hroot, -, hcases⟩ :=
    odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers K hKodd hp hp3 hpq K₂ hdeg σ hσ
  have hVt : V = torusTorsion K₂ p := Subgroup.ext fun h => (hV h).trans mem_torusTorsion_iff.symm
  set ψ : ModGL .G2 K →* ModGL .G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂)) with hψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K K₂))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    (adjointGroup .G2 K).equivMapOfInjective ψ hψinj
  obtain ⟨u, hu⟩ : ∃ u : conjEntrywiseImage K g,
      (P.map ε.toMonoidHom).map (MulAut.conj u).toMonoidHom ≤ S₀ := by
    obtain ⟨Q', hQ'⟩ := (hPp.map ε.toMonoidHom).exists_le_sylow
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (conjEntrywiseImage K g) Q' S₀
    refine ⟨u, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 : MulAut.conj u • y ∈ MulAut.conj u • (Q' : Subgroup (conjEntrywiseImage K g)) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' hy)
    rwa [← Sylow.coe_subgroup_smul, hu] at h1
  set F : adjointGroup .G2 K →* ModGL .G2 K₂ := (conjEntrywiseImage K g).subtype.comp
    ((MulAut.conj u).toMonoidHom.comp ε.toMonoidHom) with hFdef
  have hF : Function.Injective F := (conjEntrywiseImage K g).subtype_injective.comp
    ((MulAut.conj u).injective.comp ε.injective)
  have hFrange : F.range = conjEntrywiseImage K g := by
    rw [hFdef, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      ((MulAut.conj u).surjective.comp ε.surjective), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hFapp : ∀ h : adjointGroup .G2 K, F h = (u : ModGL .G2 K₂) *
      (g * baseChangeGL (algebraMap K K₂) (h : ModGL .G2 K) * g⁻¹) * (u : ModGL .G2 K₂)⁻¹ :=
    fun h => rfl
  have hFP : P.map F = torusTorsion K₂ p := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_torusTorsion_iff]
      refine ⟨(Subgroup.mem_subgroupOf.1 (hS₀T (hu ⟨ε y, ⟨y, hy, rfl⟩, rfl⟩))).1, ?_⟩
      rw [← map_pow, hPpow y hy, map_one]
    · rw [← hVt, hVcard, Subgroup.card_map_of_injective hF, hPcard]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := K₂ˣ) p
    (by rw [Nat.card_units]; exact hpq₂)
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have key : ∀ i : Fin Tag.G2.rank, ∃ ui ∈ P, ui ≠ 1 ∧ ∃ α : Fin Tag.G2.rank → ℤ,
      IsRoot .G2 α ∧ (α = Pi.single i 1 ∨ α = -Pi.single i 1) ∧
      (⁅centralizer ({ui} : Set (adjointGroup .G2 K)),
          centralizer ({ui} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)).map F =
        rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g ∧
      CFSG.IsQuasisimple (⁅centralizer ({ui} : Set (adjointGroup .G2 K)),
        centralizer ({ui} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ∧
      ∀ y ∈ centralizer ({ui} : Set (adjointGroup .G2 K)),
        (∀ r ∈ (⁅centralizer ({ui} : Set (adjointGroup .G2 K)),
          centralizer ({ui} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)),
            y * r = r * y) → F y ∈ torusGroup .G2 K₂ := by
    intro i
    obtain ⟨j, hji⟩ : ∃ j : Fin Tag.G2.rank, j ≠ i := by
      rcases fin_G2_cases i with rfl | rfl
      · exact ⟨g2ir, by decide⟩
      · exact ⟨g2ia, by decide⟩
    set c : Fin Tag.G2.rank → K₂ˣ := fun k => if k = i then 1 else ζ with hc
    have hcp : c ^ p = 1 := funext fun k => by
      by_cases hk : k = i <;> simp [hc, hk, hζp]
    have hc1 : c ≠ 1 := fun h => hζ1 (by simpa [hc, hji] using congrFun h j)
    have hci : c i = 1 := by simp [hc]
    have hdc : rootDiagUnit .G2 c ∈ P.map F := by
      rw [hFP]
      exact (rootDiagUnit_mem_torusTorsion_iff p c).2 hcp
    obtain ⟨ui, hui, hdu⟩ := hdc
    have hui1 : ui ≠ 1 := fun h => hc1 (rootDiagUnit_injective (by
      rw [← hdu, h, map_one, rootDiagUnit_one]))
    have hTc : rootDiagUnit .G2 c ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g :=
      ⟨rootDiagUnit_mem_torusGroup_G2 c, hFrange ▸ ⟨ui, hdu⟩⟩
    have hco : orderOf c = p := orderOf_eq_prime hcp hc1
    have hao : orderOf (rootDiagUnit .G2 c) = p := by rw [orderOf_rootDiagUnit, hco]
    have hiker : (Pi.single i 1 : Fin Tag.G2.rank → ℤ) ∈ rootCharKernel c :=
      ⟨isRoot_single .G2 i, by rw [rootChar_pi_single, hci]⟩
    have hne : rootCharKernel c ≠ ∅ := fun h => by
      rw [h] at hiker
      exact Set.notMem_empty _ hiker
    obtain ⟨α, hα, hkerα, hcomm, hZ, hZH, -⟩ := (hcases c hTc hao).2 hne
    obtain ⟨_, -, hQq⟩ := hroot α hα
    have hmapF : (centralizer ({ui} : Set (adjointGroup .G2 K))).map F =
        conjEntrywiseImage K g ⊓ centralizer {rootDiagUnit .G2 c} := by
      rw [map_centralizer_singleton_of_injective F hF ui, hFrange, hdu]
    obtain ⟨hRmap, hRq, -⟩ := derived_centralizer_data_of_map F hF hmapF hcomm hQq hZ hZH
    refine ⟨ui, hui, hui1, α, hα, ?_, hRmap, hRq, fun y hy hyR => ?_⟩
    · rw [hkerα] at hiker
      rcases hiker with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [show (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = -α from h, neg_neg])
    · refine hZH (hZ ▸ Subgroup.mem_inf.2 ⟨hmapF ▸ ⟨y, hy, rfl⟩,
        Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩)
      rw [← hRmap] at hw
      obtain ⟨r, hr, rfl⟩ := hw
      rw [← map_mul, ← map_mul, hyR r hr]
  obtain ⟨u₁, hu₁, hu₁1, α₁, hα₁, hα₁e, hR₁, hq₁, hZ₁⟩ := key g2ia
  obtain ⟨u₂, hu₂, hu₂1, α₂, hα₂, hα₂e, hR₂, hq₂, hZ₂⟩ := key g2ir
  have hbE : ∀ u ∈ P, (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ∈ E := fun u hu => by
    obtain ⟨e, he, hee⟩ := hu
    rwa [show (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) = e from Subtype.ext hee.symm]
  have hb1 : ∀ u : adjointGroup .G2 K, u ≠ 1 → (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ≠ 1 :=
    fun u hu h => hu (hinj (congrArg Subtype.val h))
  have hRY : ∀ u : adjointGroup .G2 K, (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
      centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ≤
      centralizer ({u} : Set (adjointGroup .G2 K)) := fun u =>
    Subgroup.commutator_le.2 fun v hv w hw => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hv hw) (inv_mem hv)) (inv_mem hw)
  have hfix₁ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₁ (hRY u₁)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₁
  have hfix₂ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₂ (hRY u₂)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₂
  rw [eq_bot_iff]
  intro s hs
  have hmem : ∀ a ∈ E, a ≠ 1 → s ∈ inSubgroup (aschbacherSolvableCore p)
      (centralizer ({a} : Set B)) := by
    simp only [thetaT, Subgroup.mem_iInf] at hs
    exact hs
  have hsR₁ := hfix₁ s (hmem _ (hbE u₁ hu₁) (hb1 u₁ hu₁1))
  have hsR₂ := hfix₂ s (hmem _ (hbE u₂ hu₂) (hb1 u₂ hu₂1))
  have hsP : ∀ u' ∈ P, (s : MulAut (adjointGroup .G2 K)) u' = u' := by
    intro u' hu'
    by_cases h1 : u' = 1
    · rw [h1, map_one]
    · have hsC := Subgroup.map_subtype_le _ (hmem _ (hbE u' hu') (hb1 u' h1))
      exact apply_eq_of_commute_conj hinj
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hsC))
  obtain ⟨⟨y, σ'⟩, hyσ, -⟩ := hNF0 (s : MulAut (adjointGroup .G2 K))
  obtain ⟨j, hj⟩ := exists_eq_pow_prime_pow hℓ hf hK σ'
  have hK₂card : Nat.card K₂ = ℓ ^ (2 * f) := by rw [hq2, hK, ← pow_mul, mul_comm]
  obtain ⟨σ₂, hσ₂⟩ := exists_ringEquiv_eq_pow_prime_pow hℓ (by omega : 1 ≤ 2 * f) hK₂card j
  have hcomm₂ : ∀ c, σ₂ (algebraMap K K₂ c) = algebraMap K K₂ (σ' c) := fun c => by
    rw [hσ₂, hj, map_pow]
  have huC : (u : ModGL .G2 K₂) ∈ adjointGroup .G2 K₂ := (hΓfix.le u.2).1
  obtain ⟨v, hvdef⟩ : ∃ v : ModGL .G2 K₂, v = (u : ModGL .G2 K₂) * g *
      baseChangeGL (algebraMap K K₂) (y : ModGL .G2 K) *
      (Units.map (entrywiseHom (σ₂ : K₂ →+* K₂)) g)⁻¹ *
      (Units.map (entrywiseHom (σ₂ : K₂ →+* K₂)) (u : ModGL .G2 K₂))⁻¹ := ⟨_, rfl⟩
  have hvC : v ∈ adjointGroup .G2 K₂ := by
    rw [hvdef]
    exact mul_mem (mul_mem (mul_mem (mul_mem huC hg) (baseChangeGL_mem_adjointGroup _ y.2))
      (inv_mem (units_map_entrywiseHom_mem_adjointGroup _ hg)))
      (inv_mem (units_map_entrywiseHom_mem_adjointGroup _ huC))
  have hFs : ∀ h : adjointGroup .G2 K, F ((s : MulAut (adjointGroup .G2 K)) h) =
      twistedEntrywise v (σ₂ : K₂ →+* K₂) (F h) := by
    intro h
    rw [hFapp, hFapp, hyσ h, map_mul, map_mul, map_inv, baseChangeGL_entrywise_comm σ' σ₂ hcomm₂,
      twistedEntrywise_apply, hvdef]
    simp only [map_mul, map_inv]
    group
  have hvV : ∀ x ∈ torusTorsion K₂ p, v⁻¹ * x * v⁻¹⁻¹ = x ^ (ℓ ^ j) := by
    intro x hx
    rw [← hFP] at hx
    obtain ⟨u', hu', rfl⟩ := hx
    have hxH : F u' ∈ torusGroup .G2 K₂ :=
      (mem_torusTorsion_iff.1 (hFP ▸ Subgroup.mem_map_of_mem F hu')).1
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxH
    have h1 := hFs u'
    rw [hsP u' hu', twistedEntrywise_apply, hc,
      entrywise_frob_rootDiagUnit (σ₂ : K₂ →+* K₂) hσ₂ c] at h1
    have h2 : rootDiagUnit .G2 (c ^ ℓ ^ j) = rootDiagUnit .G2 c ^ ℓ ^ j :=
      map_pow (rootDiagUnitHom .G2 K₂) c _
    rw [hc, ← h2]
    calc v⁻¹ * rootDiagUnit .G2 c * v⁻¹⁻¹ =
        v⁻¹ * (v * rootDiagUnit .G2 (c ^ ℓ ^ j) * v⁻¹) * v := by rw [← h1, inv_inv]
      _ = rootDiagUnit .G2 (c ^ ℓ ^ j) := by group
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin 2) K₂, ∀ A, rootSL2 .G2 K₂ α₁ (semilinearConj M σ₂ A) =
      twistedEntrywise v (σ₂ : K₂ →+* K₂) (rootSL2 .G2 K₂ α₁ A) := by
    rcases hnorm K₂ hK₂odd hpq₂ v⁻¹ (inv_mem hvC) (ℓ ^ j) hvV with hvH | ⟨hvN, hvw⟩
    · have hvH' : v ∈ torusGroup .G2 K₂ := by simpa using inv_mem hvH
      obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hvH'
      refine ⟨diagUnitOne (rootChar c α₁), fun A => ?_⟩
      rw [twistedEntrywise_apply, entrywise_rootSL2_of_field, hc, rootDiagUnit_conj_rootSL2 c hα₁]
      rfl
    · have hvN' : v ∈ monomialSubgroup .G2 K₂ := by simpa using inv_mem hvN
      have hvw' : ∀ w : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨v, hvN'⟩ • w = -w := by
        intro w
        have e : (⟨v, hvN'⟩ : monomialSubgroup .G2 K₂) = (⟨v⁻¹, hvN⟩)⁻¹ :=
          Subtype.ext (by simp)
        have h1 := hvw (-w)
        rw [neg_neg] at h1
        rw [e, map_inv]
        calc (weylQuotientHom .G2 K₂ ⟨v⁻¹, hvN⟩)⁻¹ • w =
            (weylQuotientHom .G2 K₂ ⟨v⁻¹, hvN⟩)⁻¹ • (weylQuotientHom .G2 K₂ ⟨v⁻¹, hvN⟩ • -w) := by
              rw [h1]
          _ = -w := inv_smul_smul _ _
      exact exists_semilinearConj_rootSL2 hvN' hvw' σ₂ hα₁
  obtain ⟨P₁, hP₁, -⟩ := hroot α₁ hα₁
  have hfixK : ∀ c : K, σ₂ (algebraMap K K₂ c) = algebraMap K K₂ c := by
    intro c
    obtain ⟨X, hX, htr⟩ := exists_trace_eq_algebraMap P₁ c
    rw [← hP₁, Subgroup.mem_comap, ← hR₁] at hX
    obtain ⟨r, hr, hrX⟩ := hX
    have h1 : twistedEntrywise v (σ₂ : K₂ →+* K₂) (rootSL2 .G2 K₂ α₁ X) =
        rootSL2 .G2 K₂ α₁ X := by
      rw [← hrX, ← hFs r, hsR₁ r hr]
    have h2 : semilinearConj M σ₂ X = X := rootSL2_injective_of_field α₁ (by rw [hM, h1])
    have h3 := congrArg (fun Y : SL(2, K₂) => Matrix.trace (Y : Matrix (Fin 2) (Fin 2) K₂)) h2
    rwa [trace_semilinearConj, htr] at h3
  have hσ'1 : σ' = 1 := RingEquiv.ext fun c => (algebraMap K K₂).injective (by
    rw [← hcomm₂, hfixK]
    rfl)
  have hsy : ∀ h : adjointGroup .G2 K, (s : MulAut (adjointGroup .G2 K)) h = y * h * y⁻¹ := by
    intro h
    apply Subtype.ext
    rw [hyσ h, hσ'1]
    have e : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL .G2 K) = h :=
      Units.ext (entrywise_id _)
    rw [e]
    rfl
  have hcommy : ∀ r : adjointGroup .G2 K, (s : MulAut (adjointGroup .G2 K)) r = r →
      y * r = r * y := fun r hr => by
    rw [hsy] at hr
    calc y * r = y * r * y⁻¹ * y := by group
      _ = r * y := by rw [hr]
  have hyu₁ : y ∈ centralizer ({u₁} : Set (adjointGroup .G2 K)) :=
    mem_centralizer_singleton_iff.2 (hcommy u₁ (hsP u₁ hu₁))
  have hFyH : F y ∈ torusGroup .G2 K₂ := hZ₁ y hyu₁ fun r hr => hcommy r (hsR₁ r hr)
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hFyH
  have hχ : ∀ (α : Fin Tag.G2.rank → ℤ), IsRoot .G2 α → ∀ R' : Subgroup (adjointGroup .G2 K),
      R'.map F = rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g →
      (∀ r ∈ R', (s : MulAut (adjointGroup .G2 K)) r = r) → rootChar c α = 1 := by
    intro α hα R' hR' hsR'
    obtain ⟨_, -, hcent⟩ := rootSL2_comap_fixed_eq hKodd hdeg σ hσ hg hzdef hzN hw hα
    have hcomm := commute_rootSL2_of_commute_fixed hα hcent (y := F y)
      ⟨F y, hFyH, 1, one_mem _, mul_one _⟩ (fun A hA => by
        rw [Subgroup.mem_comap, ← hR'] at hA
        obtain ⟨r, hr, hrA⟩ := hA
        rw [← hrA, ← map_mul, ← map_mul, hcommy r (hsR' r hr)]) (uSL 1)
    have h1 : rootSL2 .G2 K₂ α (conjSL (diagUnitOne (rootChar c α)) (uSL 1)) =
        rootSL2 .G2 K₂ α (uSL 1) := by
      rw [← rootDiagUnit_conj_rootSL2 c hα, ← hc, hcomm, mul_inv_cancel_right]
    have h2 : sl2Upper K₂ ((rootChar c α : K₂) * 1) = sl2Upper K₂ 1 := by
      rw [← conjSL_sl2Upper]
      exact rootSL2_injective_of_field α h1
    have h3 := congrArg (fun Y : SL(2, K₂) => (Y : Matrix (Fin 2) (Fin 2) K₂) 0 1) h2
    simp [sl2Upper] at h3
    exact h3
  have hci : ∀ (i : Fin Tag.G2.rank) (α : Fin Tag.G2.rank → ℤ),
      (α = Pi.single i 1 ∨ α = -Pi.single i 1) → rootChar c α = 1 → c i = 1 := by
    intro i α hαe hcα
    rw [← rootChar_pi_single c i]
    rcases hαe with rfl | rfl
    · exact hcα
    · rw [rootChar_neg'] at hcα
      exact inv_eq_one.mp hcα
  have hc1 : c = 1 := funext fun i => by
    rcases fin_G2_cases i with rfl | rfl
    · exact hci _ _ hα₁e (hχ α₁ hα₁ _ hR₁ hsR₁)
    · exact hci _ _ hα₂e (hχ α₂ hα₂ _ hR₂ hsR₂)
  have hy1 : y = 1 := hF (by rw [hc, hc1, rootDiagUnit_one, map_one])
  rw [Subgroup.mem_bot]
  exact Subtype.ext (MulEquiv.ext fun h => by rw [hsy h, hy1, one_mul, inv_one, mul_one]; rfl)

end CFSG.RankThree.Chevalley
