module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.KBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.Comp
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.Orbit
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.PartA

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G X J : Subgroup Γ}

omit [Finite Γ] in
theorem mem_normalizer_inf_orbitClosure_of_mem (hX : IsDAInvariant A G X) {a : Γ} (ha : a ∈ A) :
    a ∈ Subgroup.normalizer ((X ⊓ orbitClosure J A : Subgroup Γ) : Set Γ) :=
  mem_normalizer_inf (hX.2.2 ha) (mem_normalizer_orbitClosure ha)

theorem mem_normalizer_inf_orbitClosure_of_mem_smear (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) (hX : IsDAInvariant A G X) {c : Γ}
    (hc : c ∈ smear J A) :
    c ∈ Subgroup.normalizer ((X ⊓ orbitClosure J A : Subgroup Γ) : Set Γ) :=
  mem_normalizer_inf (mem_normalizer_of_mem_smear hAG hsol hJ hX.2.1 hc)
    (Subgroup.le_normalizer (smear_le_orbitClosure J A hc))

theorem sol_inf_orbitClosure_eq_bot
    (h : KSetting p A G) (hX : IsDAInvariant A G X)
    (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A) : sol (X ⊓ orbitClosure J A) = ⊥ := by
  have hAG := h.normalizes
  have hsolL := sol_orbitClosure_eq_bot hAG hsol hJ.1
  have hDA : IsDAInvariant A (orbitClosure J A) (sol (X ⊓ orbitClosure J A)) := by
    refine ⟨(sol_le _).trans inf_le_right, fun g hg => ?_, fun a ha => ?_⟩
    · exact SolQuot.normalizer_le_nrm_sol _
        (mem_normalizer_inf_orbitClosure_of_mem_smear hAG hsol hJ.1 hX hg)
    · exact SolQuot.normalizer_le_nrm_sol _ (mem_normalizer_inf_orbitClosure_of_mem hX ha)
  have hle := le_kDown_of_sol_eq_bot (kSetting_orbitClosure h hsol hJ.1) hDA hsolL
    (isSolvable_of_le inf_le_left (isSolvable_sol _))
  have hcl := orbitClosure_le_kUp (kSetting_orbitClosure h hsol hJ.1).normalizes hsolL
    (mem_lcalA_orbitClosure hAG hsol hJ)
  refine eq_bot_iff.mpr fun s hs => ?_
  have h1 : s ∈ orbitClosure J A ⊓ Subgroup.centralizer (orbitClosure J A : Set Γ) := by
    refine Subgroup.mem_inf.mpr ⟨(sol_le _).trans inf_le_right hs, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (mul_comm_of_mem_kDown hsolL (hle hs) (hcl hl)).symm
  rwa [orbitClosure_inf_centralizer_eq_bot hAG hsol hJ.1] at h1

theorem fitting_smear_le_kOf_inf
    (h : KSetting p A G) (hX : IsDAInvariant A G X)
    (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hF : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ X) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ kOf (X ⊓ orbitClosure J A) := by
  have hAG := h.normalizes
  have hsolL := sol_orbitClosure_eq_bot hAG hsol hJ.1
  have hDA : IsDAInvariant A (orbitClosure J A) (kOf (X ⊓ orbitClosure J A)) := by
    refine ⟨(kOf_le _).trans inf_le_right, fun g hg => ?_, fun a ha => ?_⟩
    · exact mem_normalizer_kOf_of_mem_normalizer
        (mem_normalizer_inf_orbitClosure_of_mem_smear hAG hsol hJ.1 hX hg)
    · exact mem_normalizer_kOf_of_mem_normalizer (mem_normalizer_inf_orbitClosure_of_mem hX ha)
  rcases lemma_5_14 (kSetting_orbitClosure h hsol hJ.1) hDA hsolL
    (mem_lcalA_orbitClosure hAG hsol hJ) with hF1 | hC
  · exact hF1
  · exfalso
    have hcent : orbitClosure J A ≤ Subgroup.centralizer (kOf (X ⊓ orbitClosure J A) : Set Γ) := by
      refine orbitClosure_le fun a ha => ?_
      rintro _ ⟨j, hj, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : a⁻¹ * x * a ∈ kOf (X ⊓ orbitClosure J A) := by
        have := (Subgroup.mem_normalizer_iff.mp (hDA.2.2 (inv_mem ha)) x).mp hx
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp (hC hx') j hj
      have e : (MulEquiv.toMonoidHom (MulAut.conj a)) j = a * j * a⁻¹ := rfl
      rw [e]
      calc x * (a * j * a⁻¹) = a * ((a⁻¹ * x * a) * j) * a⁻¹ := by group
        _ = a * (j * (a⁻¹ * x * a)) * a⁻¹ := by rw [← h1]
        _ = a * j * a⁻¹ * x := by group
    have hbot : kOf (X ⊓ orbitClosure J A) = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      have hxC : x ∈ Subgroup.centralizer (orbitClosure J A : Set Γ) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact (Subgroup.mem_centralizer_iff.mp (hcent hl) x hx).symm
      have := orbitClosure_inf_centralizer_eq_bot hAG hsol hJ.1
      exact this.le (Subgroup.mem_inf.mpr ⟨hDA.1 hx, hxC⟩)
    have hY : X ⊓ orbitClosure J A = ⊥ := (kOf_eq_bot_iff _).mp hbot
    refine fitting_smear_ne_bot h hJ (eq_bot_iff.mpr fun f hf => ?_)
    rw [← hY]
    exact Subgroup.mem_inf.mpr ⟨hF hf, (Subgroup.map_subtype_le _).trans
      (smear_le_orbitClosure J A) hf⟩

theorem mul_comm_of_mem_sol
    (h : KSetting p A G) (hX : IsDAInvariant A G X) (hsol : sol G = ⊥)
    (hJ : J ∈ lcalA G A) {s : Γ} (hs : s ∈ sol X) {l : Γ} (hl : l ∈ orbitClosure J A) :
    s * l = l * s := by
  have hS : IsDAInvariant A G (sol X) :=
    ⟨(sol_le X).trans hX.1, fun g hg => SolQuot.normalizer_le_nrm_sol X (hX.2.1 hg),
      fun a ha => SolQuot.normalizer_le_nrm_sol X (hX.2.2 ha)⟩
  have hle := le_kDown_of_sol_eq_bot h hS hsol (isSolvable_of_le inf_le_left (isSolvable_sol X))
  exact mul_comm_of_mem_kDown hsol (hle hs) (orbitClosure_le_kUp h.normalizes hsol hJ hl)

omit [Finite Γ] in
theorem isSubnormal_of_normal_chain {D M Y : Subgroup Γ} (hDM : D ≤ M) (hMY : M ≤ Y)
    (hD : (D.subgroupOf M).Normal) (hM : (M.subgroupOf Y).Normal) :
    (D.subgroupOf Y).IsSubnormal := by
  have hDY : D.subgroupOf Y ≤ M.subgroupOf Y := fun x hx => hDM hx
  refine Subgroup.IsSubnormal.trans hDY ?_ hM.isSubnormal
  let e := Subgroup.subgroupOfEquivOfLe hMY
  have heq : (D.subgroupOf Y).subgroupOf (M.subgroupOf Y) =
      (D.subgroupOf M).comap e.toMonoidHom := by
    ext x
    rfl
  rw [heq]
  exact (hD.comap e.toMonoidHom).isSubnormal

theorem isSubnormal_inf_orbitClosure (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) (hXG : X ≤ G) :
    ((X ⊓ orbitClosure J A).subgroupOf X).IsSubnormal := by
  have hDM : X ⊓ orbitClosure J A ≤ X ⊓ kOf G :=
    inf_le_inf_left X (orbitClosure_le_kOf hAG hsol hJ)
  refine isSubnormal_of_normal_chain hDM inf_le_left ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff hDM]
    intro d k hd hk
    obtain ⟨hkX, hkK⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨hdX, hdL⟩ := Subgroup.mem_inf.mp hd
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hkX hdX) (inv_mem hkX),
      (Subgroup.mem_normalizer_iff.mp (kOf_le_normalizer_orbitClosure hAG hsol hJ hkK) d).mp hdL⟩
  · rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro m x hm hx
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hx (Subgroup.mem_inf.mp hm).1) (inv_mem hx),
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_kOf hsol
        (Subgroup.le_normalizer (hXG hx))) m).mp (Subgroup.mem_inf.mp hm).2⟩

theorem mem_normalizer_of_mem_lcal_inf
    (h : KSetting p A G) (hX : IsDAInvariant A G X)
    (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hF : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ X) (hK : khat X = X)
    {C : Subgroup Γ} (hC : C ∈ lcal (X ⊓ orbitClosure J A)) {x : Γ} (hx : x ∈ X) :
    x ∈ Subgroup.normalizer (C : Set Γ) := by
  have hCX : C ∈ lcal X := mem_lcal_of_isSubnormal hC inf_le_left
    (isSubnormal_inf_orbitClosure h.normalizes hsol hJ.1 hX.1)
  have hX' : ¬ Group.IsSolvable X := by
    intro hs
    obtain ⟨hsF, hnc⟩ := smear_fitting_isSimple h hJ
    exact not_isSolvable_of_not_isMulCommutative hnc (isSolvable_of_le hF hs)
  refine mem_normalizer_of_mem_khat_of_mem_lcal hX' hCX (fun s hs c hc => ?_)
    (by rw [hK]; exact hx)
  exact mul_comm_of_mem_sol h hX hsol hJ hs ((hC.1.trans inf_le_right) hc)

theorem mem_normalizer_kOf_inf
    (h : KSetting p A G) (hX : IsDAInvariant A G X)
    (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hF : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ X) (hK : khat X = X)
    {x : Γ} (hx : x ∈ X) :
    x ∈ Subgroup.normalizer (kOf (X ⊓ orbitClosure J A) : Set Γ) := by
  have hK' := isDirectProduct_lcal_kOf (sol_inf_orbitClosure_eq_bot h hX hsol hJ)
  rw [← hK'.sSup_eq]
  have hn : ∀ C ∈ lcal (X ⊓ orbitClosure J A), x ∈ Subgroup.normalizer (C : Set Γ) :=
    fun C hC => mem_normalizer_of_mem_lcal_inf h hX hsol hJ hF hK hC hx
  refine mem_normalizer_sSup (fun C hC => ?_) (fun C hC => ?_)
  · rw [map_conj_eq_of_mem_normalizer (hn C hC)]
    exact hC
  · rw [map_conj_eq_of_mem_normalizer (inv_mem (hn C hC))]
    exact hC

theorem normalizer_of_sol_eq_bot
    (h : KSetting p A G) (hX : IsDAInvariant A G X)
    (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A) (hK : khat X = X) :
    X ≤ Subgroup.normalizer (J : Set Γ) := by
  rcases lemma_5_14 h hX hsol hJ with hF | hC
  swap
  · exact hC.trans (Subgroup.centralizer_le_normalizer _)
  have hAG := h.normalizes
  have hFX₁ := fitting_smear_le_kOf_inf h hX hsol hJ hF
  have hX₁L : kOf (X ⊓ orbitClosure J A) ≤ orbitClosure J A := (kOf_le _).trans inf_le_right
  have hXN : ∀ x ∈ X, x ∈ Subgroup.normalizer (kOf (X ⊓ orbitClosure J A) : Set Γ) :=
    fun x hx => mem_normalizer_kOf_inf h hX hsol hJ hF hK hx
  have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (kOf (X ⊓ orbitClosure J A) : Set Γ) :=
    fun a ha => mem_normalizer_kOf_of_mem_normalizer (mem_normalizer_inf_orbitClosure_of_mem hX ha)
  have hchar : ∀ E ∈ lcal G, E ∈ conjOrbit A J ↔
      ¬ kOf (X ⊓ orbitClosure J A) ≤ Subgroup.centralizer (E : Set Γ) := by
    intro E hE
    constructor
    · intro hEΩ hcE
      exact fitting_smear_ne_bot h hJ (eq_bot_of_le_centralizer_of_mem_conjOrbit hAG hJ.1 hEΩ
        (Subgroup.map_subtype_le _) (hFX₁.trans hcE))
    · intro hnc
      by_contra hnot
      apply hnc
      have hEM : E ≤ outsideOrbit G A J := le_sSup ⟨hE, hnot⟩
      have hMC := outsideOrbit_le_centralizer hAG hsol hJ.1
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_centralizer_iff.mp (hMC (hEM he)) y (hX₁L hy)).symm
  have hstable : ∀ g ∈ Subgroup.normalizer (G : Set Γ),
      g ∈ Subgroup.normalizer (kOf (X ⊓ orbitClosure J A) : Set Γ) →
        ∀ E ∈ conjOrbit A J, E.map (MulAut.conj g).toMonoidHom ∈ conjOrbit A J := by
    intro g hgG hgX E hE
    have hEl := conjOrbit_subset_lcal hAG hJ.1 hE
    have hE' := (hchar E hEl).mp hE
    refine (hchar _ (map_conj_mem_lcal hEl hgG)).mpr fun hc => hE' ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hy' : g * y * g⁻¹ ∈ kOf (X ⊓ orbitClosure J A) :=
      (Subgroup.mem_normalizer_iff.mp hgX y).mp hy
    have h1 := Subgroup.mem_centralizer_iff.mp (hc hy') (g * e * g⁻¹) ⟨e, he, rfl⟩
    have h2 : g * (e * y) * g⁻¹ = g * (y * e) * g⁻¹ := by
      calc g * (e * y) * g⁻¹ = (g * e * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * e * g⁻¹) := h1
        _ = g * (y * e) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hXA : X ⊔ A ≤ Subgroup.normalizer (G : Set Γ) ⊓
      Subgroup.normalizer (kOf (X ⊓ orbitClosure J A) : Set Γ) :=
    sup_le (fun x hx => ⟨Subgroup.le_normalizer (hX.1 hx), hXN x hx⟩)
      (fun a ha => ⟨hAG ha, hAN a ha⟩)
  have hcop : Nat.Coprime p (Nat.card X) :=
    h.hypB.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le hX.1)
  intro x hx
  exact normalizes_of_isPGroup_transitive_conj h.prime (isPGroup_of_isElemAbelian h.elemAbelian)
    hcop hX.2.2 (fun g hg E hE => hstable g (hXA hg).1 (hXA hg).2 E hE)
    (fun E hE E' hE' => exists_conj_of_mem_conjOrbit hE hE') x hx J (self_mem_conjOrbit A J)

theorem normalizer_of_mem_mcalA
    (h : KSetting p A G) (hX : IsDAInvariant A G X)
    (hJ : J ∈ mcalA G A) (hK : khat X = X) : X ≤ Subgroup.normalizer (J : Set Γ) := by
  rw [← SolQuot.qimg_le_normalizer_iff_sol hJ.1 hX.1]
  refine normalizer_of_sol_eq_bot (SolQuot.kSetting_qimg_sol h)
    (SolQuot.isDAInvariant_qimg_sol h hX) (SolQuot.sol_qimg_sol G)
    ((SolQuot.mem_mcalA_iff_qimg_mem_lcalA h hJ.1).mp hJ) ?_
  rw [SolQuot.khat_qimg_sol hX.1, hK]

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab
