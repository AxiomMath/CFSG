module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypePerm
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13Unitary
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13UnitaryDvdGen
public import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
public import CFSG.LocalAnalysis.StandardType.GGResIICell

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LineU CFSG.StandardType.UnitTB

private theorem ggWTU1_permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a b : α) :
    Equiv.permCongrHom e (Equiv.swap a b) = Equiv.swap (e a) (e b) := by
  ext x
  rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply]
  by_cases hxa : x = e a
  · subst hxa
    simp
  · by_cases hxb : x = e b
    · subst hxb
      simp
    · have ha : e.symm x ≠ a := fun h => hxa (by rw [← h, Equiv.apply_symm_apply])
      have hb : e.symm x ≠ b := fun h => hxb (by rw [← h, Equiv.apply_symm_apply])
      rw [Equiv.swap_apply_of_ne_of_ne ha hb, Equiv.swap_apply_of_ne_of_ne hxa hxb,
        Equiv.apply_symm_apply]

theorem ggWTU1_recipeUnitary_weylTypeW
    {d n p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2))
    (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have := (TableBU.unitaryFieldData_of_card hK hn).charP
  exact ⟨0, TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (by omega)),
    ggTorusWeylTypeW_of_permEltSC hp hp2 (TableBUE.center_proj_eq_bot hK hd hdq)
      (fun φ hφ hφp => InndiagSU.ggOutdiagPrime_unitary hK hn hd hdq hp hpq hpd φ hφ hφp)
      (StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 hpd)
      (UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd)⟩

private theorem ggWTU1_ggTorusWeylTypeW_unitary_dvd
    {n d p : ℕ} {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    GGTorusWeylTypeW p (ggUnitaryTorusRank p d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAab, hAI, hr, h3, hsc⟩ := hA
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hrank : ggUnitaryTorusRank p d = d - 3 := by simp [ggUnitaryTorusRank, hpd]
  rw [hrank] at hr
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := card_ge_of_dvd hp hp2 hd hpd hnd hr h3
  have hdnd : (d, n) ≠ (6, 1) := by
    rintro ⟨rfl, rfl⟩
    have h3' : p ∣ 3 := by simpa using hpq
    exact hnd ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel hK hn hd hp hpq hpd
    (unitaryUniversalCover_holds n d K hK hd hdnd) hψ hker hperf hAab hAI hcard
  have hM : UnitTB.Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  have hd3 : 3 ≤ d := by omega
  have hN : ∀ σ, MulAut.conj (φ (permSU hM.field σ)) ∈
      Subgroup.normalizer (A : Set (MulAut L')) :=
    fun σ => unitDvd_conj_perm_mem_normalizer hM hp hpq hd3 hAab.2 hsc hdiag σ
  let ρ : Equiv.Perm (Fin d) →* MulAut ↥A :=
    { toFun := fun σ => ggConjAut A (hN σ)
      map_one' := by
        refine MulEquiv.ext fun b => Subtype.ext ?_
        simp [ggConjAut_apply, UnitAct.permSU_one]
      map_mul' := by
        intro σ τ
        refine MulEquiv.ext fun b => Subtype.ext ?_
        simp only [ggConjAut_apply, MulAut.mul_apply, UnitAct.permSU_mul, map_mul]
        group }
  have hrange : ρ.range = ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    refine le_antisymm ?_ ?_
    · rintro v ⟨σ, rfl⟩
      exact ggConjAut_mem_ggAutomizer
        (MonoidHom.mem_range.mpr ⟨φ (permSU hM.field σ), rfl⟩) (hN σ)
    · intro v hv
      obtain ⟨c, ⟨m, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
      obtain ⟨w, ⟨π, rfl⟩, hfix⟩ :=
        UnitAct.exists_weyl_fix hM hK hp hp2 hpq (by omega) hAab hsc hdiag hcN
      obtain ⟨u, hu⟩ : ∃ u : L', u = m * (φ (permSU hM.field π))⁻¹ := ⟨_, rfl⟩
      have hfixu : ∀ a ∈ A, a u = u := fun a ha => by
        rw [hu]
        exact hfix a ha
      have hm : m = u * φ (permSU hM.field π) := by rw [hu]; group
      have hcomm : ∀ b' ∈ A, MulAut.conj u * b' = b' * MulAut.conj u := by
        intro b' hb'
        ext x
        have h := hfixu b' hb'
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h]
      have hv' : v = ggConjAut A (hN π) := by
        refine MulEquiv.ext fun b => Subtype.ext ?_
        rw [hvc b, ggConjAut_apply, hm, map_mul]
        have hb' : MulAut.conj (φ (permSU hM.field π)) * (b : MulAut L') *
            (MulAut.conj (φ (permSU hM.field π)))⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp (hN π) b).mp b.2
        calc MulAut.conj u * MulAut.conj (φ (permSU hM.field π)) * (b : MulAut L') *
              (MulAut.conj u * MulAut.conj (φ (permSU hM.field π)))⁻¹
            = MulAut.conj u * (MulAut.conj (φ (permSU hM.field π)) * (b : MulAut L') *
                (MulAut.conj (φ (permSU hM.field π)))⁻¹) * (MulAut.conj u)⁻¹ := by group
          _ = (MulAut.conj (φ (permSU hM.field π)) * (b : MulAut L') *
                (MulAut.conj (φ (permSU hM.field π)))⁻¹) * MulAut.conj u *
                (MulAut.conj u)⁻¹ := by
              rw [hcomm _ hb']
          _ = _ := mul_inv_cancel_right _ _
      rw [hv']
      exact MonoidHom.mem_range.mpr ⟨π, rfl⟩
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    by_contra hne
    let i0 : Fin d := ⟨0, by omega⟩
    let i1 : Fin d := ⟨1, by omega⟩
    let i2 : Fin d := ⟨2, by omega⟩
    let i3 : Fin d := ⟨3, by omega⟩
    have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
    have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
    have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
    have h20 : i2 ≠ i0 := h02.symm
    have h21 : i2 ≠ i1 := h12.symm
    have h30 : i3 ≠ i0 := by simp [i0, i3, Fin.ext_iff]
    have h31 : i3 ≠ i1 := by simp [i1, i3, Fin.ext_iff]
    have h32 : i3 ≠ i2 := by simp [i2, i3, Fin.ext_iff]
    let c : Equiv.Perm (Fin d) := Equiv.swap i0 i1 * Equiv.swap i1 i2
    have hcA : c ∈ alternatingGroup (Fin d) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      change Equiv.Perm.sign (Equiv.swap i0 i1 * Equiv.swap i1 i2) = 1
      rw [map_mul, Equiv.Perm.sign_swap h01, Equiv.Perm.sign_swap h12]
      norm_num
    have hker : Nontrivial ρ.ker := by
      rw [Subgroup.nontrivial_iff_exists_ne_one]
      exact ⟨σ, MonoidHom.mem_ker.mpr hσ, hne⟩
    have hAle := Equiv.Perm.alternatingGroup_le_of_normal (N := ρ.ker)
      (by simpa using hd : 5 ≤ Nat.card (Fin d)) hker
    have hmem : ρ c = 1 := MonoidHom.mem_ker.mp (hAle hcA)
    obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
    have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
    obtain ⟨D, hD⟩ := exists_diagSU hM.field hpq (u := TypeA.rootT ζ i0 i1)
      (fun k => TypeA.rootT_pow hζ.pow_eq_one i0 i1 k) (TypeA.prod_rootT hζ0 h01)
    have ha : MulAut.conj (φ D) ∈ A :=
      conj_mem_of_selfCent hsc hdiag hD (TypeA.rootT_pow hζ.pow_eq_one i0 i1)
    have hact : ActsDiagU φ (MulAut.conj (φ D)) (TypeA.rootT ζ i0 i1) := actsDiagU_conj hD
    have hfixA : ggConjAut A (hN c) ⟨MulAut.conj (φ D), ha⟩ =
        ⟨MulAut.conj (φ D), ha⟩ := by
      have h := congrArg (fun f : MulAut ↥A => f ⟨MulAut.conj (φ D), ha⟩) hmem
      simpa [ρ] using h
    have hfix : MulAut.conj (φ (permSU hM.field c)) * MulAut.conj (φ D) *
        (MulAut.conj (φ (permSU hM.field c)))⁻¹ = MulAut.conj (φ D) := by
      have h := congrArg (fun b : ↥A => (b : MulAut L')) hfixA
      simpa only [ggConjAut_apply] using h
    have hconj := ActsDiagU.conj_perm hM.field hact c
    rw [hfix] at hconj
    have hratio := hconj.ratio_eq hM.field hd3 hM.ker hact i0 i3
    have hcinv : c⁻¹ = Equiv.swap i1 i2 * Equiv.swap i0 i1 := by
      simp [c, _root_.mul_inv_rev, Equiv.swap_inv]
    have hc0 : c⁻¹ i0 = i2 := by
      rw [hcinv]
      simp [Equiv.Perm.mul_def, Equiv.swap_apply_left]
    have hc3 : c⁻¹ i3 = i3 := by
      rw [hcinv]
      simp only [Equiv.Perm.mul_def, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h30 h31,
        Equiv.swap_apply_of_ne_of_ne h31 h32]
    rw [hc0, hc3] at hratio
    rw [TypeA.rootT_other ζ h20 h21, TypeA.rootT_left,
      TypeA.rootT_other ζ h30 h31] at hratio
    exact hζ1 (by simpa using hratio.symm)
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm (d - 1)
  let hc : (d - 1) + 1 = d := by omega
  let pc : Equiv.Perm (Fin ((d - 1) + 1)) ≃* Equiv.Perm (Fin d) :=
    Equiv.permCongrHom (finCongr hc)
  let eσ : Equiv.Perm (Fin d) ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hrange)
  let f : (CoxeterMatrix.A (d - 1)).Group ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    e0.trans (pc.trans eσ)
  have heσ : ∀ σ : Equiv.Perm (Fin d),
      ((eσ σ : ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) : MulAut ↥A) = ρ σ := by
    intro σ
    simp [eσ, MonoidHom.ofInjective_apply]
  have hcard : Nat.card ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≠ 12 := by
    have hfac : Nat.card ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) =
        Nat.factorial d := by
      rw [← Nat.card_congr eσ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
    have h120 : 120 ≤ Nat.factorial d := by
      have h := Nat.factorial_le (by omega : 5 ≤ d)
      norm_num at h ⊢
      exact h
    omega
  refine ⟨Fin (d - 1), CoxeterMatrix.A (d - 1), f, ggResII_isWeyl_A (by omega), hcard, ?_⟩
  intro k
  have hpc : pc (Equiv.swap k.castSucc k.succ) =
      Equiv.swap (finCongr hc k.castSucc) (finCongr hc k.succ) :=
    ggWTU1_permCongr_swap (finCongr hc) k.castSucc k.succ
  have hfin : finCongr hc k.castSucc ≠ finCongr hc k.succ := fun h =>
    ne_of_lt (Fin.castSucc_lt_succ (i := k)) ((finCongr hc).injective h)
  have hsimple : ((f ((CoxeterMatrix.A (d - 1)).simple k) :
        ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) : MulAut ↥A) =
      ggConjAut A (hN (Equiv.swap (finCongr hc k.castSucc) (finCongr hc k.succ))) := by
    simp only [f, MulEquiv.trans_apply, he0, hpc, heσ]
    rfl
  rw [hsimple]
  exact unitDvd_swap_mem_reflSet hM hp hp2 hpq hd3 hAab hsc hdiag hN hfin

theorem ggWTU1_recipeUnitary_dvd_weylTypeW
    {d n p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hd : 5 ≤ d) (hpd : p ∣ d)
    (hnd : ¬ (d = 6 ∧ p = 3)) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ GGTorusLift p (ggUnitaryTorusRank p d) R ∧
        GGTorusWeylTypeW p (ggUnitaryTorusRank p d) R I := by
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusLift_unitary hK hn (by omega) hdq hp hpq,
    ggWTU1_ggTorusWeylTypeW_unitary_dvd hK hn hd hp hpq hpd hnd⟩

end CFSG.StandardType

end
