module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaUniBlock
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniCore
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagSUPPD
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LieType.SemisimpleCentralizers.HeldUCD

theorem tcjUniEnnola_component_psu_fixed (hScal : UniScalar) {K : Type} [Field K] [Finite K]
    {Q d : ℕ} {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (hK : Nat.card K = Q ^ 2) (hQ : ∃ j : ℕ, Q = 2 ^ j) (hd : 3 ≤ d) (hdQ : (d, Q) ≠ (3, 2))
    (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpQ : p ∣ Q + 1) (u : MulAut (LargeEvenProj (StatedSU d Q K)))
    (hu : ∀ h h' : ↥(StatedSU d Q K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d Q K) h) = LargeEvenProjMk (StatedSU d Q K) h')
    (hpow : u ^ p = 1) (J : Subgroup (LargeEvenProj (StatedSU d Q K)))
    (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup u)) :
    ∃ (a dd : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E)
        (hτ' : ∀ x, τ' (τ' x) = x),
        2 ≤ a ∧ dd ∣ p ∧ (∀ x : E, τ' x = x ^ (Q ^ dd)) ∧ Nat.card E = (Q ^ dd) ^ 2 ∧
        Nonempty (J ⧸ Subgroup.center J ≃*
          heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ')) := by
  have hH : heldSU d K τ hτ = StatedSU d Q K := hct_heldSU_eq_statedSU (a := d) hτQ
  have hnorm : ∀ g : GL (Fin d) K, g ∈ heldGU d K τ hτ → ∀ x ∈ StatedSU d Q K,
      g * x * g⁻¹ ∈ StatedSU d Q K := by
    intro g hg x hx
    rw [← hH] at hx ⊢
    exact heldSU_normal_in_heldGU hτ g hg x hx
  let cA : MulAut ↥(StatedSU d Q K) :=
    uniConjSub (StatedSU d Q K) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))
  have hpowk : ∀ (k : ℕ) (h h' : ↥(StatedSU d Q K)),
      (h' : GL (Fin d) K) = A ^ k * (h : GL (Fin d) K) * (A ^ k)⁻¹ →
      (u ^ k) (LargeEvenProjMk (StatedSU d Q K) h) = LargeEvenProjMk (StatedSU d Q K) h' := by
    intro k
    induction k with
    | zero =>
      intro h h' hk
      have : h' = h := by
        apply Subtype.ext
        simpa using hk
      subst this
      simp
    | succ k ih =>
      intro h h' hk
      have step1 : u (LargeEvenProjMk (StatedSU d Q K) h) =
          LargeEvenProjMk (StatedSU d Q K) (cA h) :=
        hu h (cA h) rfl
      have step2 := ih (cA h) h' (by
        rw [hk, uniConjSub_apply_val, pow_succ]
        group)
      rw [pow_succ, MulAut.mul_apply, step1, step2]
  have hAp : A ^ p ∈ heldGU d K τ hτ := pow_mem hA p
  have hconjB : ∀ g : GL (Fin d) K, g ∈ StatedSU d Q K → ∃ c : K,
      ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
        (((A ^ p)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          c • (g : Matrix (Fin d) (Fin d) K) := by
    intro g hg
    let h : ↥(StatedSU d Q K) := ⟨g, hg⟩
    let h' : ↥(StatedSU d Q K) := ⟨A ^ p * g * (A ^ p)⁻¹, hnorm (A ^ p) hAp g hg⟩
    have hk : (h' : GL (Fin d) K) = A ^ p * (h : GL (Fin d) K) * (A ^ p)⁻¹ := rfl
    have hmk : LargeEvenProjMk (StatedSU d Q K) h' = LargeEvenProjMk (StatedSU d Q K) h := by
      have h1 := hpowk p h h' hk
      rw [hpow] at h1
      simpa using h1.symm
    obtain ⟨c, hc⟩ := (projMk_eq_iff_uni (StatedSU d Q K) h' h).mp hmk
    have hh' : (h' : GL (Fin d) K) = (h : GL (Fin d) K) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := by
      rw [hc]
      group
    have hGL : A ^ p * g * (A ^ p)⁻¹ = g * (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ := hh'
    refine ⟨(c : K)⁻¹, ?_⟩
    have hM := congrArg (fun X : GL (Fin d) K => (X : Matrix (Fin d) (Fin d) K)) hGL
    simp only [Units.val_mul] at hM
    rw [hM, ← map_inv, CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.val_scalar_gl,
      Units.val_inv_eq_inv_val, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨c0, hc0⟩ := hScal K Q d τ hτ hτQ hK hd hdQ (A ^ p) hconjB
  have hAN : A ^ (Q ^ p + 1) = 1 := by
    have hGU : adjM τ ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((A ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := mem_heldGU.mp hAp
    rw [hc0, adjM_smul, adjM_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hGU
    have hc1 : τ c0 * c0 = 1 := by
      have h00 := congrFun (congrFun hGU ⟨0, by omega⟩) ⟨0, by omega⟩
      simpa using h00
    have hc2 : c0 ^ (Q + 1) = 1 := by rw [pow_succ, ← hτQ]; exact hc1
    have hApQ : A ^ (p * (Q + 1)) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_mul, ← Units.val_pow_eq_pow_val, hc0, _root_.smul_pow, hc2,
        one_pow, one_smul, Units.val_one]
    obtain ⟨k, hk⟩ := CFSG.StandardType.OrdPOutSU.mul_dvd_pow_add_one hp hp2 hpQ
    rw [hk, pow_mul, hApQ, one_pow]
  obtain ⟨M, hM, hMJ⟩ := tcjLin_component_lift (LargeEvenProjMk (StatedSU d Q K))
    (QuotientGroup.mk_surjective) (ker_projMk_uni_le_center (StatedSU d Q K)) cA u
    (fun k => (hu k (cA k) rfl).symm) hJ
  have hMinj : Function.Injective (StatedSU d Q K).subtype := Subtype.val_injective
  have hM' : CFSG.Assembly.IsComponentOf (M.map (StatedSU d Q K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSU d Q K) := by
    rw [← map_fixSubgroup_uniConjSub (StatedSU d Q K) A (hnorm A hA) (hnorm A⁻¹ (inv_mem hA))]
    exact ⟨Subgroup.map_mono hM.1, hM.2.1.map (StatedSU d Q K).subtype,
      CFSG.Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective M (StatedSU d Q K).subtype hMinj).symm hM.2.2⟩
  have hcomp : CFSG.Open.IsComponentOf (M.map (StatedSU d Q K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSU d Q K) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hM'
  have hcompH : CFSG.Open.IsComponentOf (M.map (StatedSU d Q K).subtype)
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ heldSU d K τ hτ) := by
    rw [hH]
    exact hcomp
  have hcompGU := isComponentOf_centralizer_gu_of_su hτ A hcompH
  have hsized := k1419ClsUniEnnola hτ hτQ hK hQ (hp.odd_of_ne_two hp2) A hA hAN
    (M.map (StatedSU d Q K).subtype) hcompGU
  have hperf : commutator ↥(M.map (StatedSU d Q K).subtype) = ⊤ := hcomp.2.2.1
  have hmemJ : ∀ x : ↥M, LargeEvenProjMk (StatedSU d Q K) (x : ↥(StatedSU d Q K)) ∈ J := fun x => by
    rw [← hMJ]
    exact Subgroup.mem_map_of_mem _ x.2
  let fJ : ↥M →* ↥J :=
    MonoidHom.codRestrict ((LargeEvenProjMk (StatedSU d Q K)).comp M.subtype) J hmemJ
  have hfJ : Function.Surjective fJ := by
    rintro ⟨y, hy⟩
    rw [← hMJ] at hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, rfl⟩
  have hkerJ : fJ.ker ≤ Subgroup.center ↥M := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hπ : LargeEvenProjMk (StatedSU d Q K) (x : ↥(StatedSU d Q K)) = 1 :=
      congrArg Subtype.val hx
    have hxc : (x : ↥(StatedSU d Q K)) ∈ Subgroup.center ↥(StatedSU d Q K) :=
      ker_projMk_uni_le_center (StatedSU d Q K) (MonoidHom.mem_ker.mpr hπ)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hxc _
  let e : ↥M ≃* ↥(M.map (StatedSU d Q K).subtype) := Subgroup.equivMapOfInjective M _ hMinj
  let f' : ↥(M.map (StatedSU d Q K).subtype) →* ↥J := fJ.comp e.symm.toMonoidHom
  have hsurj' : Function.Surjective f' := hfJ.comp e.symm.surjective
  have hker' : f'.ker ≤ Subgroup.center ↥(M.map (StatedSU d Q K).subtype) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hw : (e.symm x : ↥M) ∈ fJ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx
    have hwc := hkerJ hw
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    have hx' : x = e (e.symm x) := (e.apply_symm_apply x).symm
    rw [hx', ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp hwc z
  obtain ⟨φ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hperf f' hsurj' hker'
  obtain ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hdd, hτ'Q, hcardE, ⟨eM⟩⟩ := hsized
  exact ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hdd, hτ'Q, hcardE, ⟨φ.trans
    (QuotientGroup.congr (Subgroup.center ↥(M.map (StatedSU d Q K).subtype))
      (Subgroup.center (heldSU a E τ' hτ')) eM (Subgroup.map_center_eq eM))⟩⟩

end CFSG.StandardType.TCJ

end
