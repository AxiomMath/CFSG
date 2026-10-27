module

public import CFSG.LocalAnalysis.StandardType.GGTCJDivDefs
public import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GNegBCLab

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GField
  CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni
open CFSG.LocalAnalysis.GLTheoremA (canonLabel)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held
open scoped commutatorElement

theorem tcjUni_component_psu_fixed (hScal : UniScalar) {K : Type} [Field K] [Finite K] {Q d : ℕ}
    {τ : K ≃+* K} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q) (hK : Nat.card K = Q ^ 2)
    (h2 : (2 : K) = 0) (hd : 3 ≤ d) (hdQ : (d, Q) ≠ (3, 2))
    (A : GL (Fin d) K) (hA : A ∈ heldGU d K τ hτ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (u : MulAut (LargeEvenProj (StatedSU d Q K)))
    (hu : ∀ h h' : ↥(StatedSU d Q K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      u (LargeEvenProjMk (StatedSU d Q K) h) = LargeEvenProjMk (StatedSU d Q K) h')
    (hpow : u ^ p = 1) (J : Subgroup (LargeEvenProj (StatedSU d Q K)))
    (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup u)) :
    (∃ (a dd : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ' : E ≃+* E)
        (hτ' : ∀ x, τ' (τ' x) = x),
        2 ≤ a ∧ (∀ x : E, τ' x = x ^ (Q ^ dd)) ∧ Nat.card E = (Q ^ dd) ^ 2 ∧
        Nonempty (J ⧸ Subgroup.center J ≃*
          heldSU a E τ' hτ' ⧸ Subgroup.center (heldSU a E τ' hτ'))) ∨
    (∃ (b e : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ b ∧ Nat.card E = Q ^ (2 * e) ∧
        Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL b E))) := by
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
  have hodd : Odd (orderOf A) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 (by omega) A
      (hp.odd_of_ne_two hp2) hc0
  have hord : ((orderOf A : ℕ) : K) ≠ 0 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
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
  have hsized := held_unitary_components_gu_sized SUComponentsTrivial_holds
    SLComponentsTrivial_holds hτ hτQ hK A hA hord (M.map (StatedSU d Q K).subtype) hcompGU
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
  rcases hsized with ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hτ'Q, hcardE, ⟨eM⟩⟩ |
    ⟨b, e', E, hE, hEfin, ha2, hcardE, ⟨eM⟩⟩
  · exact Or.inl ⟨a, dd, E, hE, hEfin, τ', hτ', ha2, hτ'Q, hcardE, ⟨φ.trans eM⟩⟩
  · exact Or.inr ⟨b, e', E, hE, hEfin, ha2, hcardE, ⟨φ.trans eM⟩⟩

theorem tcjUni_quotCenter_cases_of_innDiag (hScal : UniScalar)
    {S : Type} [Group S] [Finite S] {p : ℕ}
    {α : MulAut S} {J : Subgroup S} {labK : GLALabel}
    (hFam : FamUni labK) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labK α)
    (hα : α ^ p = 1)
    (hJ : CFSG.Assembly.IsComponentOf J (fixSubgroup α)) :
    (∃ (a m : ℕ) (E : Type) (_ : Field E) (_ : Finite E)
        (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x),
      2 ≤ a ∧ labK.n ∣ m ∧
      (∀ x : E, τ x = x ^ (2 ^ m)) ∧ Nat.card E = (2 ^ m) ^ 2 ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃*
        (↥(heldSU a E τ hτ) ⧸ Subgroup.center ↥(heldSU a E τ hτ)))) ∨
    (∃ (b m : ℕ) (E : Type) (_ : Field E) (_ : Finite E),
      2 ≤ b ∧ labK.n ∣ m ∧ Nat.card E = 2 ^ m ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* StatedProj (StatedSL b E))) := by
  obtain ⟨K, hK, hKf, d, τ, hτ, hτq, hcard, hd3, hd3n, A, u, e, hA, hαu, hgraph⟩ :=
    innDiag_unitary_data hcen hFam hin
  have h2 : (2 : K) = 0 := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.two_eq_zero_of_card hcard
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ p = 1 := by
    rw [← hMEq, ← map_pow, hα, map_one]
  have hJ' : CFSG.Assembly.IsComponentOf (J.map e.toMonoidHom) (fixSubgroup u) := by
    rw [← hMEq]
    exact tcjLin_component_transport e α hJ
  have hdQ : (d, 2 ^ labK.n) ≠ (3, 2) := by
    intro h
    obtain ⟨hd, hQ⟩ := Prod.mk.inj h
    have h2n : 2 ≤ labK.n := hd3n hd
    have : 2 ^ 2 ≤ 2 ^ labK.n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  let eJ : ↥J ≃* ↥(J.map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
  let eJZ : (↥J ⧸ Subgroup.center ↥J) ≃*
      (↥(J.map e.toMonoidHom) ⧸ Subgroup.center ↥(J.map e.toMonoidHom)) :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥(J.map e.toMonoidHom)) eJ
      (Subgroup.map_center_eq eJ)
  rcases tcjUni_component_psu_fixed hScal hτ hτq hcard h2 (by omega) hdQ A hA hp hp2 u hgraph
      hpow (J.map e.toMonoidHom) hJ' with
    ⟨a, dd, E, hE, hEf, τ', hτ', ha2, hτ'Q, hcardE, ⟨φ⟩⟩ |
    ⟨b, ee, E, hE, hEf, hb2, hcardE, ⟨φ⟩⟩
  ·
    letI : Field E := hE
    letI : Finite E := hEf
    have hτ'm : ∀ x : E, τ' x = x ^ (2 ^ (labK.n * dd)) := by
      intro x
      rw [pow_mul]
      exact hτ'Q x
    have hcardm : Nat.card E = (2 ^ (labK.n * dd)) ^ 2 := by
      rw [pow_mul]
      exact hcardE
    exact Or.inl ⟨a, labK.n * dd, E, hE, hEf, τ', hτ', ha2, Dvd.intro dd rfl,
      hτ'm, hcardm, ⟨eJZ.trans φ⟩⟩
  ·
    letI : Field E := hE
    letI : Finite E := hEf
    have hcardm : Nat.card E = 2 ^ (labK.n * (2 * ee)) := by
      rw [pow_mul]
      exact hcardE
    exact Or.inr ⟨b, labK.n * (2 * ee), E, hE, hEf, hb2, Dvd.intro (2 * ee) rfl,
      hcardm, ⟨eJZ.trans φ⟩⟩

theorem tcjUni_innDiagAllUni_of_pieces (hScal : UniScalar) (hP2 : LinLabelDict)
    (hP3 : UniLabelDict) : InnDiagAllOn FamUni := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hα hlabJ hJ
  have hcanK : (canonLabel labK).n = labK.n := by
    rcases hFam with ht | ⟨ht, hr⟩
    · simp [canonLabel, ht]
    · simp [canonLabel, ht, hr]
  rcases tcjUni_quotCenter_cases_of_innDiag hScal hFam hp hp2 hcen hin hα hJ with
    ⟨a, m, E, hE, hEf, τ', hτ', ha2, hdvd, hτ'm, hcardm, ⟨φ⟩⟩ |
    ⟨b, m, E, hE, hEf, hb2, hdvd, hcardm, ⟨φ⟩⟩
  ·
    letI : Field E := hE
    letI : Finite E := hEf
    have hlab : (canonLabel labJ).n = m :=
      hP3 ↥J labJ a m E τ' hτ' ha2 hτ'm hcardm hlabJ ⟨φ⟩
    show (canonLabel labK).n ∣ (canonLabel labJ).n
    rw [hcanK, hlab]
    exact hdvd
  ·
    letI : Field E := hE
    letI : Finite E := hEf
    have hcanon := hP2 ↥J labJ b m E hb2 hcardm hlabJ ⟨φ⟩
    have hlab : (canonLabel labJ).n = m := by
      rw [hcanon]
    show (canonLabel labK).n ∣ (canonLabel labJ).n
    rw [hcanK, hlab]
    exact hdvd

theorem innDiagAllUni :
    InnDiagAllOn FamUni :=
  tcjUni_innDiagAllUni_of_pieces uniScalar_holds linLabelDict_holds uniLabelDict_holds

end CFSG.StandardType.TCJ

end
