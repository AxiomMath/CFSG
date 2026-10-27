module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitExcl
import CFSG.LocalAnalysis.StandardType.GGNbrLSideLinLift
import CFSG.LocalAnalysis.StandardType.GGNbrLSideLinBlock
import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitSL3CK
import CFSG.LocalAnalysis.StandardType.GGNbrLSideUniType
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.Assembly.GL83StatedBridge
import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaOuter
import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin (conjSL)

private theorem ldich_two_eq_zero {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : (2 : K) = 0 := by
  haveI := Fintype.ofFinite K
  obtain ⟨q, hq, m, hqp, hqcard⟩ := FiniteField.card' K
  rw [Nat.card_eq_fintype_card, hqcard] at hK
  have hdvd : q ∣ 2 ^ n := by
    rw [← hK]
    exact dvd_pow_self q (PNat.ne_zero m)
  have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
  subst hq2
  exact_mod_cast CharP.cast_eq_zero K 2

private theorem ldich_mu_cube {K : Type} [Field K] {d : ℕ} (hd : 1 ≤ d) {A B : GL (Fin d) K}
    (hA3 : ∃ c : K, ((A ^ 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      c • (1 : Matrix (Fin d) (Fin d) K))
    {μ : Kˣ} (hBA : B * A * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) μ * A) :
    μ ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := hA3
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hc0 : c ≠ 0 := by
    intro h0
    have hu : ((A ^ 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        (((A ^ 3)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv (A ^ 3)
    rw [hc, h0, zero_smul, zero_mul] at hu
    exact one_ne_zero hu.symm
  let z : Kˣ := Units.mk0 c hc0
  have hz : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) z := by
    apply Units.ext
    rw [CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl]
    exact hc
  have h1 : B * A ^ 3 * B⁻¹ = A ^ 3 := by
    rw [hz, ← Matrix.GeneralLinearGroup.scalar_commute z B, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : B * A ^ 3 * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) μ ^ 3 * A ^ 3 := by
    rw [← conj_pow, hBA]
    exact (Commute.mul_pow (Matrix.GeneralLinearGroup.scalar_commute μ A) 3)
  have h3 : Matrix.GeneralLinearGroup.scalar (Fin d) (μ ^ 3) = 1 := by
    rw [map_pow]
    exact mul_eq_right.mp (h1.symm.trans h2).symm
  have h4 : ((Matrix.GeneralLinearGroup.scalar (Fin d) (μ ^ 3) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = 1 := by rw [h3]; rfl
  rw [CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl] at h4
  have h5 := congrFun (congrFun h4 ⟨0, hd⟩) ⟨0, hd⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h5
  exact Units.ext (by simpa using h5)

private theorem ldich_main (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) (lab : LargeEvenLabel)
    {K : Type} [Field K] [Finite K] {n d : ℕ} (hK : Nat.card K = 2 ^ n)
    (hlab : Even n → 9 ≤ d → GGNbrLSideLargeRank lab) :
    GGNbrLSideDich lab (LargeEvenMatConjImage
      (LargeEvenProjMk (StatedSL d K)) Set.univ) := by
  classical
  intro φ hφI ψ hψI hφ1 hφ3 hψ3 hcomm J hJ Q hQ4 hQ3 hF α hα
  obtain ⟨A, -, hA⟩ := hφI
  obtain ⟨B, -, hB⟩ := hψI
  obtain ⟨F, hFfld, hFfin, hFcard, ⟨eJ⟩⟩ := hF
  have h2 : (2 : K) = 0 := ldich_two_eq_zero hK
  have h3J : 3 ∣ Nat.card ↥J := by
    have h1 := CFSG.HardMathSupport.Solomon.Coordinator.three_dvd_card_projectiveSL F
    have h2' : Nat.card (↥J ⧸ Subgroup.center ↥J) = Nat.card (projectiveSL 3 F) :=
      Nat.card_congr eJ.toEquiv
    have h3 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ↥J :=
      Subgroup.index_dvd_card (Subgroup.center ↥J)
    rw [← h2'] at h1
    exact h1.trans h3
  have hJ3 : GLAPComponent 3 (fixSubgroup φ) J :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf hJ h3J
  have hA' : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      φ (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h' := hA
  have hB' : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = B * (h : GL (Fin d) K) * B⁻¹ →
      ψ (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h' := hB
  have hA3 := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.isScalar_of_pow_trivial h2 A 3 φ hA' hφ3
  obtain ⟨μ, hμ⟩ := ggNbrLSideLin_commScalar h2 hA' hB' hcomm
  obtain ⟨M₀, hM₀J, hM₀comp⟩ := ggNbrLSideLin_lift h2 A φ hA' hφ3 hJ3
  have hinj : Function.Injective (StatedSL d K).subtype := Subtype.val_injective
  let eMap : ↥M₀ ≃* ↥(M₀.map (StatedSL d K).subtype) :=
    Subgroup.equivMapOfInjective M₀ (StatedSL d K).subtype hinj
  have hqM : CFSG.IsQuasisimple ↥(M₀.map (StatedSL d K).subtype) :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).2 hM₀comp.2.2
  have hq₀ : CFSG.IsQuasisimple ↥M₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eMap.symm hqM
  have hperf₀ : commutator ↥M₀ = ⊤ := (Group.isPerfect_def.mp hq₀.1)
  have hS : ⁅M₀, M₀⁆ = M₀ := by
    rw [← Subgroup.map_subtype_commutator, hperf₀, Subgroup.map_top, Subgroup.range_subtype]
  have hmemJ : ∀ x : ↥M₀, LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) ∈ J := fun x => by
    rw [← hM₀J]
    exact Subgroup.mem_map_of_mem _ x.2
  have hBM₀ : ∀ s ∈ M₀, conjSL B s ∈ M₀ := by
    refine ggNbrLSideLin_map_le_of_perfect hS
      (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center (K := K) (d := d))
      (conjSL B) ?_
    intro s hs
    have hπ : LargeEvenProjMk (StatedSL d K) (conjSL B s) =
        ψ (LargeEvenProjMk (StatedSL d K) s) := (hB' s (conjSL B s) rfl).symm
    have hψJ : ψ (LargeEvenProjMk (StatedSL d K) s) ∈ J :=
      ggNbrLSideInduces_mem hα ⟨_, hmemJ ⟨s, hs⟩⟩
    rw [← hM₀J] at hψJ
    obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp hψJ
    refine ⟨t, ht, t⁻¹ * conjSL B s, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hts, hπ, inv_mul_cancel]
  have hBM : ∀ m ∈ M₀.map (StatedSL d K).subtype, B * m * B⁻¹ ∈ M₀.map (StatedSL d K).subtype := by
    intro m hm
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hm
    exact Subgroup.mem_map.mpr ⟨conjSL B s, hBM₀ s hs, rfl⟩
  obtain ⟨a, E, hEf, hEalg, hEfin, e, ha2, hdim, hμ1, hμ2⟩ :=
    ggNbrLSideLin_block h2 hA3 hμ hM₀comp hBM
  letI := hEf
  letI := hEalg
  haveI := hEfin
  haveI : Module.Finite K E := Module.Finite.of_finite
  have hn1 : 1 ≤ n := by
    by_contra hn0
    obtain rfl : n = 0 := by omega
    have h1 := Finite.one_lt_card (α := K)
    rw [hK] at h1
    simp at h1
  have hfr : 0 < Module.finrank K E := Module.finrank_pos
  have hEcard : Nat.card E = 2 ^ (n * Module.finrank K E) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := E), hK, ← pow_mul]
  have hf : 1 ≤ n * Module.finrank K E := Nat.mul_pos hn1 hfr
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : ↥M₀ ≃* ↥(StatedSL a E), ∀ m, e₀ m = e (eMap m) :=
    ⟨eMap.trans e, fun _ => rfl⟩
  have hmodel := ggNbrLSideUni_typeSL hf hEcard e₀ hq₀
  let fJ : ↥M₀ →* ↥J :=
    MonoidHom.codRestrict ((LargeEvenProjMk (StatedSL d K)).comp M₀.subtype) J hmemJ
  have hfJ : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [← hM₀J] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  have hkerπ : ∀ x : ↥M₀, LargeEvenProjMk (StatedSL d K) (x : ↥(StatedSL d K)) = 1 →
      x ∈ Subgroup.center ↥M₀ := by
    intro x hx
    have hxc : (x : ↥(StatedSL d K)) ∈ Subgroup.center ↥(StatedSL d K) :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center (MonoidHom.mem_ker.mpr hx)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hxc _
  have hkerJ : fJ.ker ≤ Subgroup.center ↥M₀ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact hkerπ x (congrArg Subtype.val hx)
  obtain ⟨eQ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective hperf₀ fJ hfJ hkerJ
  have hmodelJ := CFSG.Blueprint.LieModel.of_mulEquiv eQ.symm hmodel
  have hF4 : 4 ≤ Nat.card F := by rw [hFcard]; exact hQ4
  obtain ⟨-, ha3, hFE⟩ := ggNbrLSideExcl hDet hO hF4 eJ hmodelJ
  subst ha3
  by_cases hμne : μ = 1
  ·
    obtain ⟨N, hN⟩ := hμ1 hμne
    let ψ' : ↥(StatedSL 3 E) →* LargeEvenProj (StatedSL d K) :=
      (LargeEvenProjMk (StatedSL d K)).comp (M₀.subtype.comp e₀.symm.toMonoidHom)
    have hψ'val : ∀ s, ψ' s =
        LargeEvenProjMk (StatedSL d K) ((e₀.symm s : ↥M₀) : ↥(StatedSL d K)) := fun s => rfl
    have hker : ψ'.ker ≤ Subgroup.center ↥(StatedSL 3 E) := by
      intro s hs
      rw [MonoidHom.mem_ker, hψ'val] at hs
      have hx := hkerπ _ hs
      have h1 : e₀ (e₀.symm s) ∈ Subgroup.center ↥(StatedSL 3 E) := by
        rw [← Subgroup.map_center_eq e₀]
        exact Subgroup.mem_map_of_mem _ hx
      simpa using h1
    have hβ : ∀ s s' : ↥(StatedSL 3 E), (s' : GL (Fin 3) E) = N * s * N⁻¹ →
        ψ (ψ' s) = ψ' s' := by
      intro s s' hss'
      rw [hψ'val, hψ'val]
      have hx : e (eMap (e₀.symm s)) = s := by rw [← he₀, e₀.apply_symm_apply]
      have hx' : e (eMap (e₀.symm s')) = s' := by rw [← he₀, e₀.apply_symm_apply]
      have h1 := hN (eMap (e₀.symm s))
      rw [hx] at h1
      have h2 : e ⟨B * ((eMap (e₀.symm s) : ↥(M₀.map (StatedSL d K).subtype)) : GL (Fin d) K) *
          B⁻¹, hBM _ (eMap (e₀.symm s)).2⟩ = s' := Subtype.ext (h1.trans hss'.symm)
      have h3 : (⟨B * ((eMap (e₀.symm s) : ↥(M₀.map (StatedSL d K).subtype)) : GL (Fin d) K) *
          B⁻¹, hBM _ (eMap (e₀.symm s)).2⟩ : ↥(M₀.map (StatedSL d K).subtype)) =
          eMap (e₀.symm s') := by
        apply e.injective
        rw [h2, hx']
      have h4 : B * ((e₀.symm s : ↥M₀) : GL (Fin d) K) * B⁻¹ =
          ((e₀.symm s' : ↥M₀) : GL (Fin d) K) := congrArg Subtype.val h3
      exact hB' _ _ h4.symm
    have hJ' : ψ'.range = J := by
      ext y
      constructor
      · rintro ⟨s, rfl⟩
        exact hmemJ _
      · intro hy
        rw [← hM₀J] at hy
        obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨e₀ ⟨m, hm⟩, by rw [hψ'val, e₀.symm_apply_apply]⟩
    have hres := ggNbrLSideSL3WitnessCK ψ' hker ψ N hβ hJ' α hα
    have hQE : Q = Nat.card E := by rw [← hFcard, hFE, hEcard]
    left
    rw [hQE]
    exact hres
  ·
    right
    have h3 := hμ2 hμne
    have hd9 : 9 ≤ d := by
      obtain ⟨t, ht⟩ := h3
      rw [ht] at hdim hfr
      omega
    have hμ3 : μ ^ 3 = 1 := ldich_mu_cube (by omega) hA3 hμ
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf μ = 3 := orderOf_eq_prime hμ3 hμne
    have h3dvd : 3 ∣ 2 ^ n - 1 := by
      have h1 : 3 ∣ Nat.card Kˣ := hord ▸ orderOf_dvd_natCard μ
      rwa [Nat.card_units, hK] at h1
    exact hlab ((ggNbrLSide_three_dvd_two_pow_sub_one_iff n).mp h3dvd) hd9

theorem ggNbrLSideLin_dich (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) (lab : LargeEvenLabel)
    {K : Type} [Field K] [Finite K] {n d : ℕ} (hK : Nat.card K = 2 ^ n)
    (hlab : Even n → 9 ≤ d → GGNbrLSideLargeRank lab) :
    GGNbrLSideDich lab (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  have key : ∀ H : Subgroup (GL (Fin d) K), H = StatedSL d K →
      GGNbrLSideDich lab (LargeEvenMatConjImage (LargeEvenProjMk H) Set.univ) := by
    intro H hH
    subst hH
    exact ldich_main hDet hO lab hK hlab
  exact key _ (largeEvenSLGroup_eq_statedSL d)

end CFSG.StandardType

end
