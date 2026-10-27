module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLieKnownPosDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootLong
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.LinearAlgebra.RootGroupSL.NormalizerX
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect

public section

namespace CFSG.StandardType.LieKnownR2.PSL

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LinearAlgebra.RootGroupSL Matrix
open scoped commutatorElement

theorem rootGroup_isPGroup_PSL
    {m f : ℕ}
    {β : Fin (ggU .PSL (m + 1) f).D.rank → ℤ} (hβ : β ∈ (ggU .PSL (m + 1) f).D.roots)
    (u : (ggU .PSL (m + 1) f).K) {Rr : Subgroup (ggU .PSL (m + 1) f).K}
    (hRr : Rr = ggRootSub (ggU .PSL (m + 1) f).D (MonoidHom.id (ggU .PSL (m + 1) f).K) β u) :
    IsPGroup 2 Rr := by
  subst hRr
  exact (CFSG.LieType.Steinberg.isPGroup_of_isParametrization
    (CFSG.LieType.Steinberg.SL.isParametrization (m := m) (F := GaloisField 2 f))
    hβ).map (MulAut.conj u).toMonoidHom |>.map (MonoidHom.id _)

private theorem lr2c1_eq_maxHeight_PSL {m f : ℕ} (hm : 0 < m)
    {r γ₀ : Fin m → ℤ}
    (hr : CFSG.LieType.HighestRoot.IsHighestRoot
      (SpecialLinear.rootDatum m (GaloisField 2 f)) r)
    (hγ₀ : γ₀ ∈ (SpecialLinear.rootDatum m (GaloisField 2 f)).roots)
    (hmax : ∀ δ ∈ (SpecialLinear.rootDatum m (GaloisField 2 f)).roots,
      CFSG.LieType.Steinberg.ht δ ≤ CFSG.LieType.Steinberg.ht γ₀) :
    γ₀ = r := by
  have hv : (fun _ : Fin m => (1 : ℤ)) ∈
      (SpecialLinear.rootDatum m (GaloisField 2 f)).roots := by
    show (fun _ : Fin m => (1 : ℤ)) ∈ roots (SpecialLinear.isFiniteType_A m) ∅
    rw [SpecialLinear.roots_eq]
    refine ⟨0, Fin.last m, ?_, ?_⟩
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at this
      omega
    · have h0last : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_zero, Fin.val_last] at this
        omega
      funext a
      simp only [SpecialLinear.toStd, Pi.sub_apply, Pi.single_apply]
      by_cases h0 : a = 0
      · subst h0
        simp [h0last, hm]
      · by_cases hl : a = Fin.last m
        · subst hl
          simp [h0last, hm.ne']
        · have ha0 : 0 < a.val := by
            by_contra h
            have : a.val = 0 := by omega
            exact h0 (Fin.ext this)
          have ham : a.val < m := by
            by_contra h
            have : a.val = m := by
              have := a.isLt
              omega
            exact hl (Fin.ext this)
          simp [h0, hl, ha0, ham]
  have htv : CFSG.LieType.Steinberg.ht (fun _ : Fin m => (1 : ℤ)) = (m : ℤ) := by
    simp [CFSG.LieType.Steinberg.ht]
  let i₀ : Fin (m + 1) := (SpecialLinear.idx m γ₀).1
  let j₀ : Fin (m + 1) := (SpecialLinear.idx m γ₀).2
  have hstd₀ : SpecialLinear.toStd m γ₀ = Pi.single i₀ 1 - Pi.single j₀ 1 :=
    (SpecialLinear.idx_spec m hγ₀).2
  have ht₀ : CFSG.LieType.Steinberg.ht γ₀ = (j₀ : ℤ) - (i₀ : ℤ) :=
    SpecialLinear.ht_eq m hstd₀
  have hsum₀ : (j₀ : ℤ) - (i₀ : ℤ) = (m : ℤ) := by
    rw [← ht₀]
    exact le_antisymm (by
      rw [ht₀]
      have := j₀.isLt
      have := i₀.isLt
      omega) (by
      rw [← htv]
      exact hmax _ hv)
  let i₁ : Fin (m + 1) := (SpecialLinear.idx m r).1
  let j₁ : Fin (m + 1) := (SpecialLinear.idx m r).2
  have hstd₁ : SpecialLinear.toStd m r = Pi.single i₁ 1 - Pi.single j₁ 1 :=
    (SpecialLinear.idx_spec m hr.mem_roots).2
  have ht₁ : CFSG.LieType.Steinberg.ht r = (j₁ : ℤ) - (i₁ : ℤ) :=
    SpecialLinear.ht_eq m hstd₁
  have hsum₁ : (j₁ : ℤ) - (i₁ : ℤ) = (m : ℤ) := by
    rw [← ht₁]
    exact le_antisymm (by
      rw [ht₁]
      have := j₁.isLt
      have := i₁.isLt
      omega) (by
      rw [← htv]
      exact hr.height_le _ hv)
  have hi₀ : i₀ = 0 := by
    apply Fin.ext
    show i₀.val = 0
    have := i₀.isLt
    have := j₀.isLt
    omega
  have hj₀ : j₀ = Fin.last m := by
    apply Fin.ext
    show j₀.val = m
    have := i₀.isLt
    have := j₀.isLt
    omega
  have hi₁ : i₁ = 0 := by
    apply Fin.ext
    show i₁.val = 0
    have := i₁.isLt
    have := j₁.isLt
    omega
  have hj₁ : j₁ = Fin.last m := by
    apply Fin.ext
    show j₁.val = m
    have := i₁.isLt
    have := j₁.isLt
    omega
  apply SpecialLinear.toStd_injective m
  simpa only [hstd₀, hstd₁, hi₀, hj₀, hi₁, hj₁]

theorem ggLongRoot_of_mem_roots {m : ℕ} (hm : 0 < m) {F : Type} [Field F]
    {β : Fin m → ℤ} (hβ : β ∈ (SpecialLinear.rootDatum m F).roots) :
    GGLongRoot (SpecialLinear.rootDatum m F) β := by
  obtain ⟨r, hr⟩ := CFSG.LieType.HighestRoot.exists_isHighestRoot
    (D := SpecialLinear.rootDatum m F)
    (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_A hm) rfl hm
  have hβlong : CFSG.ClassicalInvolution.ModelFacts.IsLongest
      (SpecialLinear.isFiniteType_A m) ∅ β := by
    rcases hβ with ⟨w, k, rfl⟩ | ⟨w, k, hk, rfl⟩
    · exact (CFSG.ClassicalInvolution.ModelFacts.isLongest_single_A hm rfl
        (SpecialLinear.isFiniteType_A m) k).map_weylAction w
    · exact absurd hk (Set.notMem_empty k)
  have hrlong : CFSG.ClassicalInvolution.ModelFacts.IsLongest
      (SpecialLinear.isFiniteType_A m) ∅ r :=
    ⟨hr.mem_roots, fun δ hδ => hr.longest δ hδ⟩
  obtain ⟨w, hw⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_weylAction_eq_of_isLongest
    (SpecialLinear.isFiniteType_A m)
    (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_A hm) (D := ∅)
    (fun i hi => absurd hi (by simp)) hrlong hβlong
  exact ⟨w, r, hr.mem_roots, fun δ hδ => hr.height_le δ hδ, hw.symm⟩

theorem coreOne_PSL
    {m f : ℕ}
    {β : Fin (ggU .PSL (m + 1) f).D.rank → ℤ} (hβ : β ∈ (ggU .PSL (m + 1) f).D.roots)
    (u : (ggU .PSL (m + 1) f).K) {Rr Rm Q : Subgroup (ggU .PSL (m + 1) f).K}
    (hRr : Rr = ggRootSub (ggU .PSL (m + 1) f).D (MonoidHom.id (ggU .PSL (m + 1) f).K) β u)
    (hRm : Rm = ggRootSub (ggU .PSL (m + 1) f).D (MonoidHom.id (ggU .PSL (m + 1) f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .PSL (m + 1) f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  by_cases hm : m = 0
  · subst hm
    exfalso
    have hβ' : β ∈ roots (SpecialLinear.isFiniteType_A 0) ∅ := hβ
    rw [SpecialLinear.roots_eq] at hβ'
    obtain ⟨i, j, hij, -⟩ := hβ'
    exact hij (Fin.ext (by omega))
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    obtain ⟨r, hr⟩ := CFSG.LieType.HighestRoot.exists_isHighestRoot
      (D := (ggU .PSL (m + 1) f).D)
      (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_A hmpos)
      rfl hmpos
    exact coreOne_long_of
      (SpecialLinear.isCTGroupDatum m (GaloisField 2 f))
      (SpecialLinear.steinbergExtras m (GaloisField 2 f))
      rfl
      (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_A hmpos)
      (fun γ hγ => CFSG.LieType.Steinberg.isPGroup_of_isParametrization
        (CFSG.LieType.Steinberg.SL.isParametrization (m := m) (F := GaloisField 2 f)) hγ)
      hr
      (fun γ₀ hγ₀ hmax => lr2c1_eq_maxHeight_PSL hmpos hr hγ₀ hmax)
      (ggLongRoot_of_mem_roots hmpos hβ)
      u hRr hRm hQ

private theorem lr2c2_eq_mulLeft_apply_one {k : Type} [Field k] (f : k →ₗ[k] k) :
    f = LinearMap.mulLeft k (f 1) := by
  apply LinearMap.ext
  intro s
  have := f.map_smul s 1
  simpa [mul_comm] using this

private theorem lr2c2_unipElt_inv {k E X : Type} [Field k] [Field E] [Algebra k E]
    [AddCommGroup X] [Module k X] (a : X →ₗ[k] E) (b : E →ₗ[k] X) (c : E →ₗ[k] E) :
    (unipElt a b c)⁻¹ = unipElt (-a) (-b) (-c + a ∘ₗ b) := by
  apply inv_eq_of_mul_eq_one_right
  rw [unipElt_mul, ← unipElt_zero, unipElt_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> simp <;> abel

private theorem lr2c2_unipElt_commutator {k E X : Type} [Field k] [Field E] [Algebra k E]
    [AddCommGroup X] [Module k X] (φ φ' : X →ₗ[k] E) (χ χ' : E →ₗ[k] X)
    (ψ ψ' : E →ₗ[k] E) :
    unipElt φ χ ψ * unipElt φ' χ' ψ' * (unipElt φ χ ψ)⁻¹ * (unipElt φ' χ' ψ')⁻¹ =
      unipElt (0 : X →ₗ[k] E) (0 : E →ₗ[k] X) (φ ∘ₗ χ' - φ' ∘ₗ χ) := by
  rw [lr2c2_unipElt_inv, lr2c2_unipElt_inv]
  simp only [unipElt_mul]
  rw [unipElt_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ext x <;> simp <;> abel

theorem commutator_QK_le_rootSL {k X : Type} [Field k] [AddCommGroup X] [Module k X] :
    ⁅QK k k X, QK k k X⁆ ≤ rootSL k k X := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  obtain ⟨φ, χ, ψ, hgeq⟩ := exists_unipElt_of_mem_unipRad (mem_QK_iff.mp hg)
  obtain ⟨φ', χ', ψ', hheq⟩ := exists_unipElt_of_mem_unipRad (mem_QK_iff.mp hh)
  rw [mem_rootSL_iff]
  refine ⟨(φ ∘ₗ χ' - φ' ∘ₗ χ) 1, ?_⟩
  have hcomm : ((⁅g, h⁆ : SpecialLinearGroup k (DSpace k X)) :
      DSpace k X ≃ₗ[k] DSpace k X) =
      unipElt φ χ ψ * unipElt φ' χ' ψ' * (unipElt φ χ ψ)⁻¹ *
        (unipElt φ' χ' ψ')⁻¹ := by
    simp only [commutatorElement_def, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv]
    rw [hgeq, hheq]
  rw [hcomm, lr2c2_unipElt_commutator]
  conv_lhs => rw [lr2c2_eq_mulLeft_apply_one (φ ∘ₗ χ' - φ' ∘ₗ χ)]
  rw [rootEquiv, shearE_eq_unipElt]

theorem coreFour_PSL
    {m f : ℕ}
    {β : Fin (ggU .PSL (m + 1) f).D.rank → ℤ} (hβ : β ∈ (ggU .PSL (m + 1) f).D.roots)
    (u : (ggU .PSL (m + 1) f).K) {Rr Q : Subgroup (ggU .PSL (m + 1) f).K}
    (hRr : Rr = ggRootSub (ggU .PSL (m + 1) f).D (MonoidHom.id (ggU .PSL (m + 1) f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .PSL (m + 1) f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .PSL (m + 1) f).K) := by
  let F := GaloisField 2 f
  let K := (ggU .PSL (m + 1) f).K
  let σ : K ≃* K := MulAut.conj u
  let X : Subgroup K := SpecialLinear.rootSubgroup m F (SpecialLinear.idx_spec m hβ).1
  have hroot : (ggU .PSL (m + 1) f).D.rootGroup β = X :=
    SpecialLinear.rootGroup_eq_idx m F hβ
  have hRr_eq : Rr = X.map σ.toMonoidHom := by
    rw [hRr]
    unfold ggRootSub
    rw [Subgroup.map_id, hroot]
  obtain ⟨X', _, _, _, e, he, hdim⟩ :=
    CFSG.StandardType.LieKnownR2.SpecialLinearNC.exists_mulEquiv_rootSubgroup_eq_rootSL
      (F := F) (SpecialLinear.idx_spec m hβ).1
  let eK : K ≃* SpecialLinearGroup F (DSpace F X') := e
  have he' : X.map eK.toMonoidHom = rootSL F F X' := he
  let e' : K ≃* SpecialLinearGroup F (DSpace F X') := σ.symm.trans eK
  have hRr_map : Rr.map e'.toMonoidHom = rootSL F F X' := by
    rw [hRr_eq, Subgroup.map_map]
    have hcomp : e'.toMonoidHom.comp σ.toMonoidHom = eK.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change (σ.symm.trans eK) (σ x) = eK x
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hcomp, he']
  have hQmap : Q.map e'.toMonoidHom ≤ QK F F X' := by
    by_cases hX : 0 < Module.finrank F X'
    · have hQeq : Q.map e'.toMonoidHom = QK F F X' := by
        rw [hQ, map_pCoreOf_normalizer_mulEquiv e' Rr, hRr_map]
        exact pCoreOf_normalizer_rootSL (k := F) (E := F) (X := X') hX
      exact hQeq.le
    · have hm1 : m = 1 := by
        have : Module.finrank F X' = 0 := by omega
        omega
      obtain rfl : m = 1 := hm1
      have hXle : pCoreOf 2 (Subgroup.normalizer (X : Set K)) ≤ X :=
        CFSG.StandardType.LieKnownR2.SpecialLinearNC.pCoreOf_normalizer_rootSubgroup_le
          (SpecialLinear.idx_spec 1 hβ).1
      have hQeq : Q = (pCoreOf 2 (Subgroup.normalizer (X : Set K))).map σ.toMonoidHom := by
        rw [hQ, hRr_eq]
        exact (map_pCoreOf_normalizer_mulEquiv σ X).symm
      have hQle : Q ≤ Rr := by
        rw [hQeq, hRr_eq]
        exact Subgroup.map_mono hXle
      calc Q.map e'.toMonoidHom ≤ Rr.map e'.toMonoidHom := Subgroup.map_mono hQle
        _ = rootSL F F X' := hRr_map
        _ ≤ QK F F X' := rootSL_le_QK (k := F) (E := F) (X := X')
  constructor
  · have hmap : (⁅Q, Q⁆).map e'.toMonoidHom ≤ Rr.map e'.toMonoidHom := by
      rw [Subgroup.map_commutator, hRr_map]
      exact (Subgroup.commutator_mono hQmap hQmap).trans
        (commutator_QK_le_rootSL (k := F) (X := X'))
    exact (Subgroup.map_le_map_iff_of_injective e'.injective).mp hmap
  · intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    apply e'.injective
    have hqK : e' q ∈ QK F F X' := hQmap (Subgroup.mem_map_of_mem e'.toMonoidHom hq)
    have hrK : e' r ∈ rootSL F F X' := by
      rw [← hRr_map]
      exact Subgroup.mem_map_of_mem e'.toMonoidHom hr
    have hcent := (Subgroup.mem_centralizer_iff.mp
      (QK_le_centralizer_rootSL (k := F) (E := F) (X := X') hqK)) (e' r) hrK
    simp only [map_mul]
    exact hcent

private lemma lr2c3_map_ne_bot_of_isPGroup_two_of_odd_ker
    {U X : Type} [Group U] [Group X] {ψ : U →* X} (hodd : Odd (Nat.card ψ.ker))
    {S : Subgroup U} (hS : IsPGroup 2 S) (hSne : S ≠ ⊥) : S.map ψ ≠ ⊥ := by
  intro hbot
  rw [Subgroup.map_eq_bot_iff] at hbot
  have hdisj : S ⊓ ψ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxS, hxK⟩ := hx
    obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp hS) ⟨x, hxS⟩
    rw [Subgroup.orderOf_mk] at hk
    have hdvd : orderOf x ∣ Nat.card ψ.ker := Subgroup.orderOf_dvd_natCard ψ.ker hxK
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left k) hk hdvd)
  have hle : S ≤ ⊥ := by
    rw [← hdisj]
    exact fun x hx => ⟨hx, hbot hx⟩
  exact hSne (le_bot_iff.mp hle)

theorem ggSixLieKnown_of_pos_PSL
    (h : GGSixLieKnownPos .PSL) : GGSixLieKnown .PSL := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB
    hcardD hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3
    hE6c hA6 hField hN hE
  have hadm : StatedLieAdmissible .PSL n 2 f := hmodel.admissible
  have hf1 : 1 ≤ f := hadm.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hdiv : Nat.card ψ.ker ∣ Nat.gcd (m + 1) (Nat.card (GaloisField 2 f) - 1) :=
    (Subgroup.card_dvd_of_le hker).trans
      (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by omega : 1 ≤ m + 1)
        (GaloisField 2 f))
  have hoddker : Odd (Nat.card ψ.ker) := by
    have hoddgcd : Odd (Nat.gcd (m + 1) (Nat.card (GaloisField 2 f) - 1)) := by
      rw [GaloisField.card 2 f (by omega : f ≠ 0)]
      exact Odd.of_dvd_nat
        (Nat.Even.sub_odd (Nat.one_le_pow f 2 (by norm_num))
          (Even.pow_of_ne_zero even_two (by omega : f ≠ 0)) odd_one)
        (Nat.gcd_dvd_right _ _)
    exact Odd.of_dvd_nat hoddgcd hdiv
  obtain ⟨R, Rm, hRJ, hRmJ, hpos, h2, h3⟩ :=
    h X (m + 1) f ψ p G₀ B₁ D J L x hψ hker hmodel hoddG0 hp hp2 hB₁G₀ hinner hab hcardB hDB
      hcardD hB₁J hB₁centJ hJcomp hoddJ hxD hxne hLG₀ hLcomp hJL hDnotCL hLEM1 hB₁L hLEM2 hA3
      hE6c hA6 hField hN hE
  obtain ⟨β, hβ, _, u, hR, hRm⟩ := hpos
  have hRleG₀ : R ≤ G₀ := hRJ.trans (hJL.trans hLG₀)
  have hRmap : R =
      (ggRootSub (ggU .PSL (m + 1) f).D (MonoidHom.id (ggU .PSL (m + 1) f).K) β u).map ψ :=
    hR.trans (Short.ggRootSub_eq_map _ _ _ _)
  have hRmmap : Rm =
      (ggRootSub (ggU .PSL (m + 1) f).D (MonoidHom.id (ggU .PSL (m + 1) f).K) (-β) u).map ψ :=
    hRm.trans (Short.ggRootSub_eq_map _ _ _ _)
  have hRp : IsPGroup 2 R := by
    rw [hRmap]
    exact (rootGroup_isPGroup_PSL hβ u rfl).map ψ
  have hSne :
      ggRootSub (ggU .PSL (m + 1) f).D (MonoidHom.id (ggU .PSL (m + 1) f).K) β u ≠ ⊥ := by
    intro hbot
    have hroot : (ggU .PSL (m + 1) f).D.rootGroup β ≠ ⊥ :=
      (CFSG.LieType.Universal.SpecialLinear.steinbergExtras (m := m)
        (F := GaloisField 2 f)).ne_bot β hβ
    apply hroot
    rw [ggRootSub] at hbot
    simp only [Subgroup.map_id] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj u).injective).mp hbot
  have hRne : R ≠ ⊥ := by
    rw [hRmap]
    exact lr2c3_map_ne_bot_of_isPGroup_two_of_odd_ker hoddker
      (rootGroup_isPGroup_PSL hβ u rfl) hSne
  have hbase : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ (R ⊔ Rm) = G₀ := by
    have h1 := Short.itemOne_of_core hker hoddker (rootGroup_isPGroup_PSL hβ u rfl)
      (coreOne_PSL hβ u rfl rfl rfl)
    rw [hψ, ← hRmap, ← hRmmap] at h1
    exact h1
  have hRle_pcore : R ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) :=
    GGRootNorm.le_pCoreOf_of_normalized
      (fun r hr => ⟨hRleG₀ hr, Subgroup.le_normalizer hr⟩)
      hRp
      (Subgroup.le_normalizer_iff.mp inf_le_right)
  have hitem1 : pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ⊔ Rm = G₀ := by
    rw [← sup_assoc, sup_eq_left.mpr hRle_pcore] at hbase
    exact hbase
  have hitem4 : (⁅pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)),
        pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))⁆ ≤ R ∧
      pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) ≤
        Subgroup.centralizer (R : Set X)) ∨
      ∀ V : Subgroup X,
        ggCenterOf (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))) ≤ V →
        V ≤ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
        V ≠ ggCenterOf (pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X))) →
        V ≠ pCoreOf 2 (G₀ ⊓ Subgroup.normalizer (R : Set X)) →
        G₀ ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (V : Set X) →
        J ⊔ V = G₀ := by
    have hcore := coreFour_PSL hβ u rfl rfl
    have h1 := Short.itemFour_of_core hker hoddker (rootGroup_isPGroup_PSL hβ u rfl)
      hcore.1 hcore.2
    rw [hψ, ← hRmap] at h1
    exact Or.inl h1
  exact ⟨R, Rm, hRJ, hRne, hRp, hRmJ, hitem1, h2, h3, hitem4⟩

end CFSG.StandardType.LieKnownR2.PSL
