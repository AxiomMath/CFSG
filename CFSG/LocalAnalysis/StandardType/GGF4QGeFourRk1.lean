module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGPos
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinMinus

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.CurtisTits (rankOne)

private lemma rootGroup_map_conj_weylLift' {K G : Type} [Group K] [Group G]
    (D : UniversalRootDatum K) (ν : GGWeyl D →* K)
    (hν : GGWeylLift D ν) (ψ : K →* G) (u : GGWeyl D) (γ : Fin D.rank → ℤ)
    (hγ : γ ∈ D.roots) :
    (D.rootGroup (weylAction D.isFiniteType u γ)).map ψ =
      (D.rootGroup γ).map ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨(ν u)⁻¹ * y * ν u, ?_, ?_⟩
    · have h := hν.conj_mem (u⁻¹) (weylAction D.isFiniteType u γ)
        (weylAction_mem_roots D.isFiniteType u hγ) y hy
      rw [map_inv ν u, inv_inv, weylAction_inv_apply_apply] at h
      exact h
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv]
      group
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨ν u * z * (ν u)⁻¹, hν.conj_mem u γ hγ z hz, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

theorem ggRootLevi_map_conj_weylLift' {K G : Type} [Group K] [Group G]
    (D : UniversalRootDatum K) (ν : GGWeyl D →* K)
    (hν : GGWeylLift D ν) (ψ : K →* G) (u : GGWeyl D) (i : Fin D.rank) :
    (ggRootLevi D (weylAction D.isFiniteType u (Pi.single i 1))).map ψ =
      ((ggRootLevi D (Pi.single i 1 : Fin D.rank → ℤ)).map ψ).map
        (MulAut.conj (ψ (ν u))).toMonoidHom := by
  have hsingle : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (isCTRootSystem D.isFiniteType D.divisible).single_mem i
  have h1 := rootGroup_map_conj_weylLift' D ν hν ψ u (Pi.single i 1) hsingle
  have hsingle' : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hsingle
  have h2 := rootGroup_map_conj_weylLift' D ν hν ψ u (-(Pi.single i 1)) hsingle'
  change (D.rootGroup (weylAction D.isFiniteType u (Pi.single i 1)) ⊔
      D.rootGroup (-(weylAction D.isFiniteType u (Pi.single i 1)))).map ψ =
    ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-(Pi.single i 1))).map ψ).map
      (MulAut.conj (ψ (ν u))).toMonoidHom
  rw [← map_neg (weylAction D.isFiniteType u) (Pi.single i 1)]
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map,
    h1, h2]

private theorem exists_sl2_of_tableBPos_node
    {G : Type} [Group G] {Bs X : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    (hlift : GGHasWeylLift (ggU t n f).D) {P : Fin (ggU t n f).D.rank → ℕ → Prop}
    (hnode : ∀ k : Fin (ggU t n f).D.rank, ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (φ : Matrix.SpecialLinearGroup (Fin 2) F →* (ggU t n f).K), CharP F 2 ∧
        Function.Injective φ ∧ φ.range = rankOne (ggU t n f).D.rootGroup k ∧ P k (Nat.card F))
    {ψ : (ggU t n f).K →* G} (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    {ε : (coxeterMatrix (ggU t n f).D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs)}
    (hlev : ∀ (w : (coxeterMatrix (ggU t n f).D.isFiniteType).Group) (i : Fin (ggU t n f).D.rank),
      ggRankOneIn X Bs
        ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (ggRootLevi (ggU t n f).D
          (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ)
    (w : (coxeterMatrix (ggU t n f).D.isFiniteType).Group) (k : Fin (ggU t n f).D.rank) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G),
      CharP F 2 ∧ Function.Injective θ ∧
        θ.range = ggRankOneIn X Bs
          ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple k * w⁻¹) :
            ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∧ P k (Nat.card F) := by
  obtain ⟨ν, hν⟩ := hlift
  obtain ⟨F, hF, hFfin, φ, hchar, hφinj, hφrange, hP⟩ := hnode k
  refine ⟨F, hF, hFfin, (MulAut.conj (ψ (ν w))).toMonoidHom.comp (ψ.comp φ), hchar, ?_, ?_, hP⟩
  · exact (MulAut.conj (ψ (ν w))).injective.comp
      (PsiDiag.injective_comp_of_ker_le_center φ hφinj ψ hker)
  · rw [hlev w k, ggRootLevi_map_conj_weylLift' _ ν hν ψ w k, MonoidHom.range_comp,
      MonoidHom.range_comp, hφrange]
    rfl

private theorem exists_node_of_tableBPos
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {t : StatedLieTag} {n f : ℕ}
    (hW : GGIsWeylMatrix (coxeterMatrix (ggU t n f).D.isFiniteType))
    (hG2 : ¬ ∃ e : Fin 2 ≃ Fin (ggU t n f).D.rank,
      coxeterMatrix (ggU t n f).D.isFiniteType = CoxeterMatrix.G₂.reindex e)
    {ε : (coxeterMatrix (ggU t n f).D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs)}
    (hεrefl : ∀ i, GGIsReflection p
      ((ε ((coxeterMatrix (ggU t n f).D.isFiniteType).simple i) : ↥(ggAutomizer X Bs)) :
        MulAut ↥Bs))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    ∃ (k : Fin (ggU t n f).D.rank) (w : (coxeterMatrix (ggU t n f).D.isFiniteType).Group),
      r = ((ε (w * (coxeterMatrix (ggU t n f).D.isFiniteType).simple k * w⁻¹) :
        ↥(ggAutomizer X Bs)) : MulAut ↥Bs) := by
  have hAind : ggAutomizer X Bs ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  obtain ⟨k, w, hkw⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hp hp2 hEl hNT _
    hAind _ _ hW hG2 ε hεrefl ⟨r, hrA⟩ hr
  exact ⟨k, w, congrArg Subtype.val hkw⟩

private theorem exists_sl2_of_tableBPos
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {t : StatedLieTag} {n f : ℕ}
    (hW : GGIsWeylMatrix (coxeterMatrix (ggU t n f).D.isFiniteType))
    (hG2 : ¬ ∃ e : Fin 2 ≃ Fin (ggU t n f).D.rank,
      coxeterMatrix (ggU t n f).D.isFiniteType = CoxeterMatrix.G₂.reindex e)
    (hlift : GGHasWeylLift (ggU t n f).D) {P : ℕ → Prop}
    (hnode : ∀ k : Fin (ggU t n f).D.rank, ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (φ : Matrix.SpecialLinearGroup (Fin 2) F →* (ggU t n f).K), CharP F 2 ∧
        Function.Injective φ ∧ φ.range = rankOne (ggU t n f).D.rootGroup k ∧ P (Nat.card F))
    {ψ : (ggU t n f).K →* G} (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    (hpos : GGTableBPos p Bs X t n f ψ) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G),
      CharP F 2 ∧ Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧ P (Nat.card F) := by
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  obtain ⟨k, w, rfl⟩ := exists_node_of_tableBPos hp hp2 hEl hNT hW hG2 hεrefl hrA hr
  exact exists_sl2_of_tableBPos_node (P := fun _ => P) hlift hnode hker hεlevi w k

theorem cartanC_eq_cartanMatrixB (n : ℕ) : Symplectic.cartanC n = CartanMatrix.B n := by
  ext i j
  simp only [Symplectic.cartanC, CartanMatrix.B, Matrix.of_apply]
  split_ifs <;> omega

private theorem ggIsWeylMatrix_B {n : ℕ} (hn : 2 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.B n) :=
  Or.inl ⟨n, Equiv.refl _, by omega, Or.inr (Or.inl ⟨hn, (ggCoxeterMatrix_reindex_refl _).symm⟩)⟩

private theorem ggIsWeylMatrix_cartanC {n : ℕ} (hn : 2 ≤ n) :
    GGIsWeylMatrix (coxeterMatrix (Symplectic.isFiniteType_cartanC n)) := by
  have hC : GGIntCartan (CoxeterMatrix.B n) (Symplectic.cartanC n) := by
    rw [cartanC_eq_cartanMatrixB]
    exact ggIntCartan_B n
  rw [coxeterMatrix_eq_of_ggIntCartan _ hC]
  exact ggIsWeylMatrix_B hn

private theorem ggIsWeylMatrix_cartanB {n : ℕ} (hn : 2 ≤ n) :
    GGIsWeylMatrix (coxeterMatrix (Spin.isFiniteType_cartanB n)) := by
  have hC : GGIntCartan (CoxeterMatrix.B n) (Spin.cartanB n) := by
    rw [Spin.cartanB_eq]
    exact ggIntCartan_C n
  rw [coxeterMatrix_eq_of_ggIntCartan _ hC]
  exact ggIsWeylMatrix_B hn

private theorem not_G₂_of_rank {r : ℕ} (hr : r ≠ 2) (M : CoxeterMatrix (Fin r)) :
    ¬ ∃ e : Fin 2 ≃ Fin r, M = CoxeterMatrix.G₂.reindex e := by
  rintro ⟨e, -⟩
  have h := Fintype.card_congr e
  simp only [Fintype.card_fin] at h
  omega

private theorem nodes_PSp
    {f : ℕ} (hf : 1 ≤ f) (k : Fin (ggU .PSp 3 f).D.rank) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F)
      (φ : Matrix.SpecialLinearGroup (Fin 2) F →* (ggU .PSp 3 f).K), CharP F 2 ∧
        Function.Injective φ ∧ φ.range = rankOne (ggU .PSp 3 f).D.rootGroup k ∧
          Nat.card F = 2 ^ f := by
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, ?_⟩
  change Fin 3 at k
  by_cases hk : k.val + 1 < 3
  · exact ⟨CFSG.ClassicalInvolution.Models.SymplecticPairs.shortBlock (GaloisField 2 f)
      (Symplectic.SpExtras.ne_succ' hk), inferInstance,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.shortBlock_injective _,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.range_shortBlock_eq_rankOne hk,
      GaloisField.card 2 f (by omega)⟩
  · exact ⟨CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock (GaloisField 2 f) 3 k,
      inferInstance, CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_injective k,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.range_longBlock_eq_rankOne hk,
      GaloisField.card 2 f (by omega)⟩

private theorem nodes_spinMinus {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (k : Fin (Spin.Twisted.minusDatum n hirr).rank) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E)
      (φ : Matrix.SpecialLinearGroup (Fin 2) E →* ↥(spinGroup (Spin.quadMinus n F b c))),
        CharP E 2 ∧ Function.Injective φ ∧
          φ.range = rankOne (Spin.Twisted.minusDatum n hirr).rootGroup k ∧
          Nat.card E = if k.val + 1 < n - 1 then Nat.card F else Nat.card F ^ 2 := by
  change Fin (n - 1) at k
  by_cases hk : k.val + 1 < n - 1
  · exact ⟨F, inferInstance, inferInstance, _, inferInstance,
      CFSG.LieType.Steinberg.SpinFrame.longSL2_injective _ (Spin.Twisted.succ_ne_of_lt n hk) true
        false, (Spin.Twisted.rankOne_minusRootGroup_of_lt n hirr hk).symm, (if_pos hk).symm⟩
  · have := Spin.Twisted.fact_shortField hirr
    have := Spin.Twisted.finite_shortField (b := b) (c := c)
    have : CharP (Spin.Twisted.ShortField b c) 2 :=
      charP_of_injective_algebraMap (algebraMap F (Spin.Twisted.ShortField b c)).injective 2
    have h4 : 4 ≤ Nat.card (Spin.Twisted.ShortField b c) := by
      rw [CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.card_shortField]
      have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left h2 2
    obtain ⟨φ, hx, hy⟩ :=
      CFSG.AGLEmbeddingD2.HeisSpinMinus.exists_hom_of_rankOneRels' (Spin.Twisted.shortRels n hirr k)
    have hS := CFSG.AGLEmbedding.ParabPrime.sl2_isSimpleGroup (k := Spin.Twisted.ShortField b c) h4
    have hx0 : (Spin.Twisted.shortRels n hirr k).x 0 = 1 :=
      CFSG.LieType.Steinberg.RankOneRels.x_zero _
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
      · exact hb
      · exfalso
        have hmem : CFSG.LieType.Steinberg.sl2Upper (1 : Spin.Twisted.ShortField b c) ∈ φ.ker := by
          rw [ht]
          exact Subgroup.mem_top _
        have h1 : φ (CFSG.LieType.Steinberg.sl2Upper (1 : Spin.Twisted.ShortField b c)) = 1 :=
          MonoidHom.mem_ker.1 hmem
        rw [hx] at h1
        exact one_ne_zero
          (CFSG.LieType.Steinberg.shortRels_x_injective hirr k (h1.trans hx0.symm))
    have hr : rankOne (Spin.Twisted.minusDatum n hirr).rootGroup k = φ.range := by
      refine le_antisymm (sup_le (fun g hg => ?_) (fun g hg => ?_)) ?_
      · obtain ⟨t, rfl⟩ := (CFSG.LieType.Steinberg.mem_minusRootGroup_single_iff hirr hk g).1 hg
        exact ⟨CFSG.LieType.Steinberg.sl2Upper t, hx t⟩
      · obtain ⟨t, rfl⟩ :=
          (CFSG.LieType.Steinberg.mem_minusRootGroup_neg_single_iff hirr hk g).1 hg
        exact ⟨CFSG.LieType.Steinberg.sl2Lower t, hy t⟩
      · rintro _ ⟨A, rfl⟩
        have hle : Subgroup.closure (Set.range (CFSG.LieType.Steinberg.sl2Upper
              (k := Spin.Twisted.ShortField b c)) ∪
            Set.range CFSG.LieType.Steinberg.sl2Lower) ≤
            (rankOne (Spin.Twisted.minusDatum n hirr).rootGroup k).comap φ := by
          rw [Subgroup.closure_le]
          rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
          · exact le_sup_left (a := (Spin.Twisted.minusDatum n hirr).rootGroup (Pi.single k 1))
              ((CFSG.LieType.Steinberg.mem_minusRootGroup_single_iff hirr hk _).2 ⟨t, (hx t).symm⟩)
          · exact le_sup_right (b := (Spin.Twisted.minusDatum n hirr).rootGroup (-Pi.single k 1))
              ((CFSG.LieType.Steinberg.mem_minusRootGroup_neg_single_iff hirr hk _).2
                ⟨t, (hy t).symm⟩)
        exact hle (CFSG.LieType.Steinberg.Sp.mem_closure_sl2 A)
    exact ⟨Spin.Twisted.ShortField b c, inferInstance, inferInstance, φ, inferInstance, hinj,
      hr.symm, by
        rw [if_neg hk]
        exact CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.card_shortField⟩

private theorem nodes_POmegaMinus
    {f : ℕ} (hf : 1 ≤ f) (k : Fin (ggU .POmegaMinus 4 f).D.rank) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E)
      (φ : Matrix.SpecialLinearGroup (Fin 2) E →* (ggU .POmegaMinus 4 f).K), CharP E 2 ∧
        Function.Injective φ ∧ φ.range = rankOne (ggU .POmegaMinus 4 f).D.rootGroup k ∧
          Nat.card E = 2 ^ (if k.val < 2 then f else 2 * f) := by
  obtain ⟨E, hE, hEfin, φ, hchar, hinj, hrange, hcard⟩ := nodes_spinMinus (n := 4)
    (minusCoeffs_irr 2 f) k
  refine ⟨E, hE, hEfin, φ, hchar, hinj, hrange, ?_⟩
  rw [hcard, GaloisField.card 2 f (by omega)]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by omega)
  · exact absurd h2 (by omega)
  · rw [← pow_mul, mul_comm]

private theorem range_subtype_comp_symm' {K M : Type*} [Group K] [Group M] {L : Subgroup K}
    (e : ↥L ≃* M) : (L.subtype.comp e.symm.toMonoidHom).range = L := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, Subgroup.map_top,
    Subgroup.range_subtype]

private theorem nodes_SU {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (he : Even n) (k : Fin (n / 2)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (φ : Matrix.SpecialLinearGroup (Fin 2) E →*
        ↥(Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)), CharP E 2 ∧
      Function.Injective φ ∧ φ.range = rankOne (Unitary.rootDatum hF n).rootGroup k ∧
        Nat.card E = if k.val + 1 < n / 2 then 2 ^ (2 * f) else 2 ^ f := by
  have hσ := CFSG.LieType.BorelTits.unitaryInvolution_involutive hF
  by_cases hk : k.val + 1 < n / 2
  · let e := CFSG.LieType.Steinberg.rankOneShortEquiv (hσ := hσ) hk
    refine ⟨F, inferInstance, inferInstance,
      (rankOne (Unitary.rootGroup _ hσ n) k).subtype.comp e.symm.toMonoidHom, inferInstance,
      Subtype.val_injective.comp e.symm.injective,
      range_subtype_comp_symm' e, ?_⟩
    rw [if_pos hk, hF, ← pow_mul, mul_comm]
  · obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hF
    let e := (CFSG.LieType.Steinberg.rankOneLastEvenEquiv hF he hk).trans
      (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).symm
    exact ⟨CFSG.LieType.Steinberg.fixedSubfield F 2 f, inferInstance, inferInstance,
      (rankOne (Unitary.rootGroup _ hσ n) k).subtype.comp e.symm.toMonoidHom, inferInstance,
      Subtype.val_injective.comp e.symm.injective,
      range_subtype_comp_symm' e,
      by rw [if_neg hk]; exact CFSG.LieType.Steinberg.card_fixedSubfield hF⟩

private theorem ggU_PSU_eq
    {n f : ℕ} (hf : 1 ≤ f) :
    ggU .PSU n f =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
  simp only [ggU, lieUniversal, hf, ↓reduceDIte]

private theorem nodes_PSU
    {f : ℕ} (hf : 1 ≤ f) : ∀ k : Fin (ggU .PSU 6 f).D.rank,
    ∃ (E : Type) (_ : Field E) (_ : Finite E)
      (φ : Matrix.SpecialLinearGroup (Fin 2) E →* (ggU .PSU 6 f).K), CharP E 2 ∧
        Function.Injective φ ∧ φ.range = rankOne (ggU .PSU 6 f).D.rootGroup k ∧
          Nat.card E = 2 ^ (if k.val < 2 then 2 * f else f) := by
  rw [ggU_PSU_eq hf]
  intro k
  obtain ⟨E, hE, hEfin, φ, hchar, hinj, hrange, hcard⟩ :=
    nodes_SU (card_galoisField_two_mul 2 f hf) (by decide) k
  refine ⟨E, hE, hEfin, φ, hchar, hinj, hrange, ?_⟩
  rw [hcard]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (by omega)
  · exact absurd h2 (by omega)
  · rfl

private theorem ggIsWeylMatrix_PSU
    {f : ℕ} (hf : 1 ≤ f) :
    GGIsWeylMatrix (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType) ∧
      (ggU .PSU 6 f).D.rank ≠ 2 := by
  rw [ggU_PSU_eq hf]
  refine ⟨?_, by show 6 / 2 ≠ 2; decide⟩
  show GGIsWeylMatrix (coxeterMatrix (Unitary.isFiniteType_cartan 6))
  have hC : GGIntCartan (CoxeterMatrix.B (6 / 2)) (Unitary.cartan 6) := by
    rw [show Unitary.cartan 6 = Symplectic.cartanC (6 / 2) from if_pos (by decide),
      cartanC_eq_cartanMatrixB]
    exact ggIntCartan_B _
  rw [coxeterMatrix_eq_of_ggIntCartan _ hC]
  exact ggIsWeylMatrix_B (by norm_num)

theorem exists_sl2_ggRankOneIn_of_tableBPosImage_PSp
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {f : ℕ} (hf1 : 1 ≤ f)
    (hX : GGTableBPosImage p Bs .PSp 3 f X) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G),
      CharP F 2 ∧ Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧ Nat.card F = 2 ^ f := by
  have hadm : StatedLieAdmissible .PSp 3 2 f := ⟨Nat.prime_two, hf1, by omega, by simp⟩
  obtain ⟨ψ, hker, -, hposX⟩ := hX
  exact exists_sl2_of_tableBPos (t := .PSp) (n := 3) (f := f) (P := fun c => c = 2 ^ f) hp hp2
    hEl hNT (ggIsWeylMatrix_cartanC (n := 3) (by norm_num))
    (not_G₂_of_rank (by show 3 ≠ 2; decide) _)
    (ggTagFacts_PSp hadm (by decide)).2.1 (nodes_PSp hf1) hker hposX hrA hr

theorem exists_sl2_ggRankOneIn_node_POmegaMinus
    {G : Type} [Group G] {Bs X : Subgroup G} {f : ℕ} (hf1 : 1 ≤ f)
    {ψ : (ggU .POmegaMinus 4 f).K →* G} (hker : ψ.ker ≤ Subgroup.center (ggU .POmegaMinus 4 f).K)
    {ε : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs)}
    (hlev : ∀ (w : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).Group)
      (i : Fin (ggU .POmegaMinus 4 f).D.rank),
      ggRankOneIn X Bs
        ((ε (w * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (ggRootLevi (ggU .POmegaMinus 4 f).D
          (weylAction (ggU .POmegaMinus 4 f).D.isFiniteType w (Pi.single i 1))).map ψ)
    (w : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).Group)
    (k : Fin (ggU .POmegaMinus 4 f).D.rank) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G),
      CharP F 2 ∧ Function.Injective θ ∧
        θ.range = ggRankOneIn X Bs
          ((ε (w * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple k * w⁻¹) :
            ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∧
        Nat.card F = 2 ^ (if k.val < 2 then f else 2 * f) := by
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 f := ⟨Nat.prime_two, hf1, le_rfl⟩
  exact exists_sl2_of_tableBPos_node (P := fun k c => c = 2 ^ (if k.val < 2 then f else 2 * f))
    (ggTagFacts_POmegaMinus hadm (by decide)).2.1 (nodes_POmegaMinus hf1) hker hlev w k

theorem exists_sl2_ggRankOneIn_node_PSU
    {G : Type} [Group G] {Bs X : Subgroup G} {f : ℕ} (hf1 : 1 ≤ f)
    {ψ : (ggU .PSU 6 f).K →* G} (hker : ψ.ker ≤ Subgroup.center (ggU .PSU 6 f).K)
    {ε : (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs)}
    (hlev : ∀ (w : (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).Group)
      (i : Fin (ggU .PSU 6 f).D.rank),
      ggRankOneIn X Bs
        ((ε (w * (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple i * w⁻¹) :
          ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
        (ggRootLevi (ggU .PSU 6 f).D
          (weylAction (ggU .PSU 6 f).D.isFiniteType w (Pi.single i 1))).map ψ)
    (w : (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).Group)
    (k : Fin (ggU .PSU 6 f).D.rank) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G),
      CharP F 2 ∧ Function.Injective θ ∧
        θ.range = ggRankOneIn X Bs
          ((ε (w * (coxeterMatrix (ggU .PSU 6 f).D.isFiniteType).simple k * w⁻¹) :
            ↥(ggAutomizer X Bs)) : MulAut ↥Bs) ∧
        Nat.card F = 2 ^ (if k.val < 2 then 2 * f else f) := by
  have hadm : StatedLieAdmissible .PSU 6 2 f := ⟨Nat.prime_two, hf1, by omega, by simp⟩
  exact exists_sl2_of_tableBPos_node (P := fun k c => c = 2 ^ (if k.val < 2 then 2 * f else f))
    (ggTagFacts_PSU hadm (by decide)).2.1 (nodes_PSU hf1) hker hlev w k

theorem exists_node_of_tableBPos_POmegaMinus
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {f : ℕ}
    {ε : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).Group ≃* ↥(ggAutomizer X Bs)}
    (hεrefl : ∀ i, GGIsReflection p
      ((ε ((coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple i) :
        ↥(ggAutomizer X Bs)) : MulAut ↥Bs))
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    ∃ (k : Fin (ggU .POmegaMinus 4 f).D.rank)
      (w : (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).Group),
      r = ((ε (w * (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType).simple k * w⁻¹) :
        ↥(ggAutomizer X Bs)) : MulAut ↥Bs) :=
  exists_node_of_tableBPos (t := .POmegaMinus) (n := 4) (f := f) hp hp2 hEl hNT
    (ggIsWeylMatrix_cartanB (n := 3) (by norm_num)) (not_G₂_of_rank (by show 4 - 1 ≠ 2; decide) _)
    hεrefl hrA hr

theorem exists_sl2_ggRankOneIn_of_tableBPosImage_POmegaMinus
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {f : ℕ} (hf1 : 1 ≤ f)
    (hX : GGTableBPosImage p Bs .POmegaMinus 4 f X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G),
      CharP F 2 ∧ Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
        (Nat.card F = 2 ^ f ∨ Nat.card F = 2 ^ (2 * f)) := by
  obtain ⟨ψ, hker, -, ε, hεrefl, hlev, -⟩ := hX
  obtain ⟨k, w, rfl⟩ := exists_node_of_tableBPos_POmegaMinus hp hp2 hEl hNT hεrefl hrA hr
  obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, hc⟩ :=
    exists_sl2_ggRankOneIn_node_POmegaMinus hf1 hker hlev w k
  refine ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, ?_⟩
  rw [hc]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem exists_sl2_ggRankOneIn_of_tableBPosImage_PSU
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {f : ℕ} (hf1 : 1 ≤ f)
    (hX : GGTableBPosImage p Bs .PSU 6 f X) {r : MulAut ↥Bs}
    (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G),
      CharP F 2 ∧ Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
        (Nat.card F = 2 ^ f ∨ Nat.card F = 2 ^ (2 * f)) := by
  obtain ⟨ψ, hker, -, ε, hεrefl, hlev, -⟩ := hX
  obtain ⟨hW, hrk⟩ := ggIsWeylMatrix_PSU hf1
  obtain ⟨k, w, rfl⟩ := exists_node_of_tableBPos hp hp2 hEl hNT hW (not_G₂_of_rank hrk _) hεrefl
    hrA hr
  obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, hc⟩ :=
    exists_sl2_ggRankOneIn_node_PSU hf1 hker hlev w k
  refine ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, ?_⟩
  rw [hc]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem ggF4QGeFourRk1Input_of_kgPos
    (row : GGF4QGeFourRow) (hKG : GGF4QGeFourKGPosInput row) : GGF4QGeFourRk1Input row := by
  intro G _ _ p B Bs x L D J y K hcfg e hpres f hf hp hrow X hX r hrA hrC
  have hr : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  have hr2 : r * r = 1 := by simpa [pow_two] using hr.1
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hf1 : 1 ≤ f := by omega
  have hpos := hKG G p B Bs x L D J y K hcfg ⟨e, hpres.2⟩ f hf hp hrow
  obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, hcard⟩ : ∃ (F : Type) (_ : Field F)
      (_ : Finite F) (θ : Matrix.SpecialLinearGroup (Fin 2) F →* G), CharP F 2 ∧
        Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
          (row = .S1 → Nat.card F = 2 ^ f) ∧
          (row = .S2 → Nat.card F = 2 ^ f ∨ Nat.card F = 2 ^ (2 * f)) := by
    cases row with
    | S1 =>
      have hXpos : GGTableBPosImage p Bs .PSp 3 f X := by
        rcases hX with rfl | rfl
        · exact hpos.1
        · exact hpos.2
      obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, hc⟩ :=
        exists_sl2_ggRankOneIn_of_tableBPosImage_PSp hpp hp2 hEl hNT hf1 hXpos hrA hr
      exact ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, fun _ => hc, fun h => nomatch h⟩
    | S2 =>
      have hXpos : GGTableBPosImage p Bs .POmegaMinus 4 f X ∨
          GGTableBPosImage p Bs .PSU 6 f X := by
        rcases hX with rfl | rfl
        · exact Or.inl hpos.1
        · exact Or.symm hpos.2
      rcases hXpos with hXpos | hXpos
      · obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, hc⟩ :=
          exists_sl2_ggRankOneIn_of_tableBPosImage_POmegaMinus hpp hp2 hEl hNT hf1 hXpos hrA hr
        exact ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, (fun h => nomatch h), fun _ => hc⟩
      · obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, hc⟩ :=
          exists_sl2_ggRankOneIn_of_tableBPosImage_PSU hpp hp2 hEl hNT hf1 hXpos hrA hr
        exact ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, (fun h => nomatch h), fun _ => hc⟩
  exact ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, ggExists_weylElt_of_mem_ggAutomizer hrA hr2,
    hcard⟩

theorem ggF4QGeFourSysF4Input_of_kgPos
    (hL1 : GGF4QGeFourL1Input .S1) (hKG : GGF4QGeFourKGPosInput .S1)
    (hOrb : GGF4QGeFourOrbInput .S1) (hRk2 : GGF4QGeFourRk2Input .S1)
    (hRk2c : GGF4QGeFourRk2CrossInput .S1) (hJoin : GGF4QGeFourJoinInput .S1) :
    GGF4QGeFourSysF4Input :=
  ggF4QGeFourSysF4Input_of_twins hL1 (ggF4QGeFourRk1Input_of_kgPos .S1 hKG)
    (ggF4QGeFourGenInput_of_kgPos .S1 hKG) hOrb hRk2 hRk2c hJoin

theorem ggF4QGeFourSysTwE6Input_of_kgPos
    (hL1 : GGF4QGeFourL1Input .S2) (hKG : GGF4QGeFourKGPosInput .S2)
    (hOrb : GGF4QGeFourOrbInput .S2) (hRk2 : GGF4QGeFourRk2Input .S2)
    (hRk2c : GGF4QGeFourRk2CrossInput .S2) (hJoin : GGF4QGeFourJoinInput .S2) :
    GGF4QGeFourSysTwE6Input :=
  ggF4QGeFourSysTwE6Input_of_twins hL1 (ggF4QGeFourRk1Input_of_kgPos .S2 hKG)
    (ggF4QGeFourGenInput_of_kgPos .S2 hKG) hOrb hRk2 hRk2c hJoin

end CFSG.StandardType

end
