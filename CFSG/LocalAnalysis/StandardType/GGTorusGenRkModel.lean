module

public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitAutModel
public import CFSG.LocalAnalysis.StandardType.GGWPlusPositionRk
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGL45TGSU

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

private theorem ggrk_div_add_two_le_sub_two {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 5 ≤ d)
    (hpd : p ∣ d) : d / p + 2 ≤ d - 2 := by
  obtain ⟨k, rfl⟩ := hpd
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hk1 : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact absurd hd (by norm_num)
  rw [Nat.mul_div_cancel_left k hp.pos]
  rcases lt_or_ge k 2 with hk2 | hk2
  · have hk : k = 1 := by omega
    subst hk
    simp at hd
    omega
  · have h4 : k + 4 ≤ p * k := by nlinarith [hp3, hk2]
    omega

private theorem ggrk_mem_center_of_scalar {n d : ℕ} {K : Type} [Field K]
    {x : ↥(unitarySU 2 n K d)} {c : K}
    (hc : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (fun _ => c)) :
    x ∈ Subgroup.center ↥(unitarySU 2 n K d) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hc, ← Matrix.scalar_apply]
  exact (Matrix.scalar_comm c (fun r' => mul_comm c r')
    (((y : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).symm

private theorem ggrk_mem_center_of_commutator_mem_center {G : Type*} [Group G]
    (hG : commutator G = ⊤) {g : G} (hc : ∀ x : G, ⁅g, x⁆ ∈ Subgroup.center G) :
    g ∈ Subgroup.center G := by
  have hmul : ∀ x y : G, ⁅g, x * y⁆ = ⁅g, x⁆ * ⁅g, y⁆ := by
    intro x y
    have hxc : x * ⁅g, y⁆ = ⁅g, y⁆ * x := Subgroup.mem_center_iff.mp (hc y) x
    have hcx : ⁅g, y⁆ * x⁻¹ = x⁻¹ * ⁅g, y⁆ := by
      calc ⁅g, y⁆ * x⁻¹ = x⁻¹ * (x * ⁅g, y⁆) * x⁻¹ := by group
        _ = x⁻¹ * (⁅g, y⁆ * x) * x⁻¹ := by rw [hxc]
        _ = x⁻¹ * ⁅g, y⁆ := by group
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc g * (x * y) * g⁻¹ * (x * y)⁻¹
        = g * x * (g⁻¹ * (g * y * g⁻¹ * y⁻¹)) * x⁻¹ := by group
      _ = g * x * g⁻¹ * (⁅g, y⁆ * x⁻¹) := by rw [commutatorElement_def]; group
      _ = g * x * g⁻¹ * (x⁻¹ * ⁅g, y⁆) := by rw [hcx]
      _ = g * x * g⁻¹ * x⁻¹ * (g * y * g⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  have hinv : ∀ u : G, ⁅g, u⁻¹⁆ * ⁅g, u⁆ = 1 := by
    intro u
    have h := hmul u⁻¹ u
    rw [inv_mul_cancel, commutatorElement_one_right] at h
    exact h.symm
  have hpow : ∀ x : G, ⁅g, x⁆ = 1 := by
    intro x
    have hx : x ∈ commutator G := by rw [hG]; exact Subgroup.mem_top x
    change x ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ at hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, -, b, -, rfl⟩ := hw
      have hp : ⁅g, a⁆ * ⁅g, b⁆ = ⁅g, b⁆ * ⁅g, a⁆ :=
        Subgroup.mem_center_iff.mp (hc b) _
      have hpi : ⁅g, a⁻¹⁆ = ⁅g, a⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv a)
      have hqi : ⁅g, b⁻¹⁆ = ⁅g, b⁆⁻¹ := eq_inv_of_mul_eq_one_left (hinv b)
      rw [commutatorElement_def a b, hmul, hmul, hmul, hpi, hqi]
      calc ⁅g, a⁆ * ⁅g, b⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹
          = ⁅g, b⁆ * ⁅g, a⁆ * ⁅g, a⁆⁻¹ * ⁅g, b⁆⁻¹ := by rw [hp]
        _ = 1 := by group
    | one => simp
    | mul x y _ _ hx hy => rw [hmul, hx, hy, one_mul]
    | inv x _ hx =>
      have := hinv x
      rw [hx, mul_one] at this
      exact this
  refine Subgroup.mem_center_iff.mpr fun x => ?_
  exact (commutatorElement_eq_one_iff_mul_comm.mp (hpow x)).symm

theorem exists_model_of_position_rowA
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (h61 : (d, n) ≠ (6, 1))
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) θ hE)
    (hr : p ^ (d - 1) ≤ Nat.card E) :
    ∃ φ : ↥(unitarySU 2 n K d) →* L', UnitTB.Model φ ∧
      ∀ e : E, ∃ t : Fin d → K, ActsDiagU φ (L'.normalizerMonoidHom ⟨e, hE e.2⟩) t := by
  classical
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hperf : commutator L' = ⊤ := hpos.1
  set A : Subgroup (MulAut L') := (ggGamma L' hE).range with hAdef
  have hAab : CFSG.Open.IsElemAbelian p A := by
    rw [hAdef]
    exact TableBBridge.isElemAbelian_range_gamma hpos
  have hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l : L', x (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro a ⟨b, rfl⟩
    exact ⟨ggLAut L' θ ⟨b, hE b.2⟩, hpos.2.2.2.1 b,
      fun l => ggBeta_ggQuotHom L' hE θ b l⟩
  have hA2 : p ^ (d - 2) ≤ Nat.card A := by
    have h := TableBBridge.pow_pred_le_card_range hpos hp (r := d - 1) (by simpa using hr)
    simpa [hAdef, show d - 1 - 1 = d - 2 by omega] using h
  have hcard : p ^ (d / p + 2) ≤ Nat.card A :=
    le_trans (Nat.pow_le_pow_right hp.pos (ggrk_div_add_two_le_sub_two hp hp2 hd hpd)) hA2
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    LineU.exists_diagModel hK hn hd hp hpq hpd
      (LineU.unitaryUniversalCover_holds n d K hK hd h61)
      (ggQuotHom_surjective θ) (ker_ggQuotHom θ).le hperf hAab hAI hcard
  refine ⟨φ, ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩, ?_⟩
  intro e
  obtain ⟨t, ht⟩ := hdiag (ggGamma L' hE e) ⟨e, rfl⟩
  exact ⟨t, ht⟩

theorem centralizes_center_pElts_rowA
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (h61 : (d, n) ≠ (6, 1))
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {θ : L' ⧸ Subgroup.center L' ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)}
    (hpos : GGTableBPosition p L' E
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) θ hE)
    (hr : p ^ (d - 1) ≤ Nat.card E) :
    ∀ z ∈ L' ⊓ Subgroup.centralizer (L' : Set M), z ^ p = 1 →
      z ∈ Subgroup.centralizer (E : Set M) := by
  classical
  intro z hz _
  obtain ⟨hzL, hzC⟩ := hz
  obtain ⟨φ, hmodel, hdiagE⟩ :=
    exists_model_of_position_rowA hK hn hd hp hpq hpd h61 hpos hr
  have hφs := hmodel.surj
  have hφker := hmodel.ker
  have hzcent : (⟨z, hzL⟩ : L') ∈ Subgroup.center L' := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC l l.2
  obtain ⟨u, hu⟩ := hφs ⟨z, hzL⟩
  have hucen : u ∈ Subgroup.center ↥(unitarySU 2 n K d) := by
    refine ggrk_mem_center_of_commutator_mem_center (G := ↥(unitarySU 2 n K d)) ?_ fun v => ?_
    · exact (LineU.unitaryUniversalCover_holds n d K hK hd h61).1
    · have h1 : φ ⁅u, v⁆ = 1 := by
        rw [map_commutatorElement, hu, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hzcent (φ v)).symm
      obtain ⟨c, hc⟩ := hφker ⁅u, v⁆ h1
      exact ggrk_mem_center_of_scalar hc
  have hcommSU : ∀ g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n),
      Commute (u : GL (Fin d) K) g := by
    intro g hg
    have hcntr := Subgroup.mem_center_iff.mp hucen (⟨g, hg⟩ : ↥(unitarySU 2 n K d))
    exact (congrArg Subtype.val hcntr).symm
  have hscal : (u : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
    GGL45TG.SU.mem_scalars_of_commute_su (TableBU.unitaryFieldData_of_card hK hn) (by omega)
      (u : GL (Fin d) K) hcommSU
  rw [largeEvenScalars_def] at hscal
  obtain ⟨cu, hcu⟩ := hscal
  have hconj : ∀ (D : GL (Fin d) K)
      (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))),
      conjN D hD u = u := by
    intro D hD
    apply Subtype.ext
    have hDcomm : D * (u : GL (Fin d) K) = (u : GL (Fin d) K) * D := by
      rw [← hcu]
      exact (Matrix.GeneralLinearGroup.scalar_commute cu D).symm
    show D * (u : GL (Fin d) K) * D⁻¹ = (u : GL (Fin d) K)
    rw [hDcomm]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  obtain ⟨t, ht⟩ := hdiagE ⟨e, he⟩
  obtain ⟨D, hD, -, hact⟩ := ht
  have hfix : (L'.normalizerMonoidHom ⟨e, hE he⟩) (⟨z, hzL⟩ : L') = ⟨z, hzL⟩ := by
    have h := hact u
    rw [hu] at h
    rw [hconj D hD, hu] at h
    exact h
  have hfixM : e * z * e⁻¹ = z := by
    have h := congrArg Subtype.val hfix
    rw [normalizerMonoidHom_coe] at h
    simpa using h
  calc e * z = e * z * e⁻¹ * e := by group
    _ = z * e := by rw [hfixM]

end CFSG.StandardType
