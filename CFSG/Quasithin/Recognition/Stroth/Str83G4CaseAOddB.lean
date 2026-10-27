module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAA1
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAA3
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAOmegaS
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAV2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R

open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

@[expose] noncomputable def caseAOddN2 {L1 L2 S : Subgroup G} (b : ℕ)
    (x : GPath (f112Amalgam L1 L2 S).graphHat b) : Subgroup (f112Amalgam L1 L2 S).Ghat :=
  caseAN (x 1) ⊓ CosetGeom.Qy (x (b - 2))

@[expose] noncomputable def caseAOddE {L1 L2 S : Subgroup G} (b : ℕ)
    (x : GPath (f112Amalgam L1 L2 S).graphHat b) : Subgroup (f112Amalgam L1 L2 S).Ghat :=
  caseAOddN2 b x ⊓ CosetGeom.Qy (x (b - 1))

theorem caseA_odd_N_le_Qy {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hb : 5 ≤ b) : caseAN (x 1) ≤ CosetGeom.Qy (x (b - 3)) := by
  have hvt1 : CosetGeom.vtype (x 1) = false :=
    (hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)
  have hd1 : CosetGeom.dist (x 1) (x (b - 3)) = b - 4 := by
    rw [hx.dist_eq (i := 1) (j := b - 3) (by omega) (by omega)]
    omega
  unfold caseAN
  refine iSup₂_le fun w hw => ?_
  have hwv : CosetGeom.vtype w = false := by
    have hv : CosetGeom.vtype (x 1) = CosetGeom.vtype w :=
      (CosetGeom.vtype_eq_iff_even_dist rfl (x 1) w).mpr (by rw [hw]; norm_num)
    rw [hvt1] at hv
    exact hv.symm
  refine caseA_X_le_Qy hx.ball hwv ?_
  have htri : CosetGeom.dist w (x (b - 3)) ≤
      CosetGeom.dist w (x 1) + CosetGeom.dist (x 1) (x (b - 3)) :=
    CosetGeom.dist_triangle rfl w (x 1) (x (b - 3))
  have hw1 : CosetGeom.dist w (x 1) = 2 := by rw [CosetGeom.dist_comm]; exact hw
  omega

theorem caseA_odd_relIndex_N_N2_le
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbo : Odd b) (hb : 5 ≤ b) :
    (caseAOddN2 b x).relIndex (caseAN (x 1)) ≤ 2 ^ (2 * a + 1) := by
  have hvt1 : CosetGeom.vtype (x 1) = false :=
    (hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)
  have hvtb2 : CosetGeom.vtype (x (b - 2)) = false := by
    have hd : CosetGeom.dist (x 1) (x (b - 2)) = b - 3 := by
      rw [hx.dist_eq (i := 1) (j := b - 2) (by omega) (by omega)]
      omega
    have hv : CosetGeom.vtype (x 1) = CosetGeom.vtype (x (b - 2)) :=
      (CosetGeom.vtype_eq_iff_even_dist rfl (x 1) (x (b - 2))).mpr
        (by rw [hd]; exact Nat.Odd.sub_odd hbo (by norm_num : Odd 3))
    rw [hvt1] at hv
    exact hv.symm
  have hτ : x (b - 3) ∈ CosetGeom.nbrs (x (b - 2)) := by
    show (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (x (b - 3))
    simpa [show (b - 3) + 1 = b - 2 by omega] using (x.adj (b - 3) (by omega)).symm
  have hNAS : caseAN (x 1) ≤ caseAS (x (b - 2)) (x (b - 3)) := by
    have h2 : caseAN (x 1) ≤ caseAS (x (b - 3)) (x (b - 2)) :=
      (caseA_odd_N_le_Qy hx hb).trans (caseA_Qy_le_caseAS hfr (by
        show (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 3)) (x (b - 2))
        simpa [show (b - 3) + 1 = b - 2 by omega] using x.adj (b - 3) (by omega)))
    rwa [caseAS_comm] at h2
  have hAclosure : caseAN (x 1) ≤
      Subgroup.closure {t | t ∈ caseAS (x (b - 2)) (x (b - 3)) ∧ t * t = 1} := by
    unfold caseAN
    refine iSup₂_le fun w hw => ?_
    have hwv : CosetGeom.vtype w = false := by
      have hv : CosetGeom.vtype (x 1) = CosetGeom.vtype w :=
        (CosetGeom.vtype_eq_iff_even_dist rfl (x 1) w).mpr (by rw [hw]; norm_num)
      rw [hvt1] at hv
      exact hv.symm
    have hAel := caseA_isElemAbelian_X hfr hwv
    intro t ht
    exact Subgroup.subset_closure
      ⟨hNAS (le_iSup₂ (f := fun w (_ : CosetGeom.dist (x 1) w = 2) => caseAX w) w hw ht),
        by simpa [pow_two] using hAel.2 t ht⟩
  have hmain := caseA_relIndex_inf_Qy_le_type1_of_involutions hfr hvtb2 hτ hAclosure
  simpa [caseAOddN2] using hmain

theorem caseA_odd_relIndex_N2_E_le
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbo : Odd b) (hb : 5 ≤ b) :
    (caseAOddE b x).relIndex (caseAOddN2 b x) ≤ 2 ^ (2 * a + 1) := by
  have hvt1 : CosetGeom.vtype (x 1) = false :=
    (hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)
  have hvtb1 : CosetGeom.vtype (x (b - 1)) = true := by
    have hd : CosetGeom.dist (x 1) (x (b - 1)) = b - 2 := by
      rw [hx.dist_eq (i := 1) (j := b - 1) (by omega) (by omega)]
      omega
    have hodd : Odd (b - 2) :=
      Nat.Odd.sub_even (show 2 ≤ b by omega) hbo (by norm_num : Even 2)
    have hne : CosetGeom.vtype (x 1) ≠ CosetGeom.vtype (x (b - 1)) := by
      intro h
      have he : Even (CosetGeom.dist (x 1) (x (b - 1))) :=
        (CosetGeom.vtype_eq_iff_even_dist rfl (x 1) (x (b - 1))).mp h
      rw [hd] at he
      exact (Nat.not_even_iff_odd.mpr hodd) he
    rw [hvt1] at hne
    cases hv : CosetGeom.vtype (x (b - 1)) <;> simp_all
  have hα : x (b - 2) ∈ CosetGeom.nbrs (x (b - 1)) := by
    show (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 1)) (x (b - 2))
    simpa [show (b - 2) + 1 = b - 1 by omega] using (x.adj (b - 2) (by omega)).symm
  have hA : caseAOddN2 b x ≤ caseAS (x (b - 1)) (x (b - 2)) := by
    rw [caseAOddN2]
    refine inf_le_right.trans ?_
    have hq := caseA_Qy_le_caseAS hfr (v := x (b - 2)) (w := x (b - 1)) (by
      show (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (x (b - 1))
      simpa [show (b - 2) + 1 = b - 1 by omega] using x.adj (b - 2) (by omega))
    rwa [caseAS_comm] at hq
  have hmain := caseA_relIndex_inf_Qy_le_type2 hfr hvtb1 hα hA
  simpa [caseAOddE] using hmain

theorem caseA_odd_X_le_E
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) :
    caseAX (x 1) ≤ caseAOddE b x := by
  have hvt1 : CosetGeom.vtype (x 1) = false :=
    (hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)
  have hXN : caseAX (x 1) ≤ caseAN (x 1) := caseA_X_le_N hfr hvt1
  have hXb2 : caseAX (x 1) ≤ CosetGeom.Qy (x (b - 2)) := by
    refine caseA_X_le_Qy hx.ball hvt1 ?_
    have hd : CosetGeom.dist (x 1) (x (b - 2)) = b - 3 := by
      rw [hx.dist_eq (i := 1) (j := b - 2) (by omega) (by omega)]
      omega
    omega
  have hXb1 : caseAX (x 1) ≤ CosetGeom.Qy (x (b - 1)) := caseA_X_le_Qy_pred hx hbo hb
  show caseAX (x 1) ≤
    (caseAN (x 1) ⊓ CosetGeom.Qy (x (b - 2))) ⊓ CosetGeom.Qy (x (b - 1))
  exact le_inf (le_inf hXN hXb2) hXb1

theorem caseA_odd_E_le_caseAS {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hb : 5 ≤ b) :
    caseAOddE b x ≤ caseAS (x b) (x (b - 1)) := by
  intro t ht
  have htE : t ∈ caseAOddN2 b x ⊓ CosetGeom.Qy (x (b - 1)) := by
    simpa [caseAOddE] using ht
  have htQ : t ∈ CosetGeom.Qy (x (b - 1)) := (Subgroup.mem_inf.mp htE).2
  have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 1)) (x b) := by
    simpa [show (b - 1) + 1 = b by omega] using x.adj (b - 1) (by omega)
  have hmem : t ∈ caseAS (x (b - 1)) (x b) :=
    caseA_Qy_le_caseAS hfr (by simpa [CosetGeom.nbrs] using hadj) htQ
  rwa [caseAS_comm] at hmem

theorem caseA_odd_E_le_centralizer
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) :
    caseAOddE b x ≤ Subgroup.centralizer (caseAX (x 1) : Set (f112Amalgam L1 L2 S).Ghat) := by
  have hvt1 : CosetGeom.vtype (x 1) = false :=
    (hx.vtype_eq_false_iff_odd (i := 1) (by omega)).mpr (by norm_num)
  intro t ht
  have htE : t ∈ caseAOddN2 b x ⊓ CosetGeom.Qy (x (b - 1)) := by
    simpa [caseAOddE] using ht
  have htN2 : t ∈ caseAOddN2 b x := (Subgroup.mem_inf.mp htE).1
  have htN : t ∈ caseAN (x 1) :=
    (Subgroup.mem_inf.mp (by simpa [caseAOddN2] using htN2)).1
  have hY : t ∈ caseAY (x 1) := caseA_N_le_Y hfr hA hvt1 htN
  exact (Subgroup.mem_inf.mp (by simpa [caseAY] using hY)).2

private theorem oddbb_commutator_zpowers_mem {G : Type*} [Group G] {H : Subgroup G} {t x : G}
    (ht2 : t * t = 1) (h : x * t * x⁻¹ * t⁻¹ ∈ H) :
    ∀ u ∈ Subgroup.zpowers t, x * u * x⁻¹ * u⁻¹ ∈ H := by
  intro u hu
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have h2 : t ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]
    exact ht2
  rw [zpow_eq_zpow_emod k (n := (2 : ℤ)) h2]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simpa using h

private theorem oddbb_finite_of_le_stab {v : f112Gamma L1 L2 S}
    {H : Subgroup (f112Amalgam L1 L2 S).Ghat} (hH : H ≤ CosetGeom.stab v) : Finite ↥H := by
  haveI : Finite ↥(CosetGeom.stab v) := caseA_finite_stab L1 L2 S v
  exact Finite.of_injective (fun h : ↥H => (⟨h.1, hH h.2⟩ : ↥(CosetGeom.stab v)))
    (fun a b hab => Subtype.ext
      (congrArg (fun x : ↥(CosetGeom.stab v) => (x : (f112Amalgam L1 L2 S).Ghat)) hab))

theorem caseA_odd_E_eq_sup
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) :
    caseAOddE b x = caseAX (x 1) ⊔ (caseAOddE b x ⊓ CosetGeom.Qy (x b)) := by
  have hα : CosetGeom.vtype (x b) = false :=
    (hx.vtype_eq_false_iff_odd (i := b) le_rfl).mpr hbo
  have hb1 : 1 ≤ b := by omega
  have hτ : x (b - 1) ∈ CosetGeom.nbrs (x b) := by
    have h := x.adj (b - 1) (by omega)
    rw [Nat.sub_add_cancel hb1] at h
    simpa [CosetGeom.nbrs] using h.symm
  have hv1 : CosetGeom.vtype (x 1) = false := by
    have h := CosetGeom.vtype_ne_of_adj (x.adj 0 (by omega))
    rw [hx.type_two] at h
    cases hv : CosetGeom.vtype (x 1) <;> simp_all
  have hAS : caseAX (x 1) ≤ caseAS (x b) (x (b - 1)) := by
    have hQy : CosetGeom.Qy (x (b - 1)) ≤ caseAS (x (b - 1)) (x b) :=
      caseA_Qy_le_caseAS hfr (v := x (b - 1)) (w := x b) (by
        have h := x.adj (b - 1) (by omega)
        rw [Nat.sub_add_cancel hb1] at h
        simpa [CosetGeom.nbrs] using h)
    rw [caseAS_comm] at hQy
    exact (caseA_X_le_Qy_pred hx hbo hb).trans hQy
  have hAel : IsElemAbelian 2 (caseAX (x 1)) := caseA_isElemAbelian_X hfr hv1
  have hAidx := caseA_relIndex_X_inf_Qy_end hfr hx hbo hb
  have hquad : ⁅caseAX (x b), caseAX (x 1)⁆ ≤ caseAX (x 1) := by
    rw [Subgroup.commutator_comm]
    exact (caseA_commutator_X_le_inf hfr hx hbo hb).trans inf_le_left
  have hEcent := caseA_odd_E_le_centralizer hfr hA hx hbo hb
  have hEA : ∀ e ∈ caseAOddE b x, ∀ y ∈ caseAX (x 1), e * y = y * e := by
    intro e he y hy
    exact (Subgroup.mem_centralizer_iff.mp (hEcent he) y hy).symm
  have hle : caseAOddE b x ≤ caseAX (x 1) ⊔ CosetGeom.Qy (x b) :=
    caseA_le_sup_Qy_of_commute hfr hα hτ hAS (caseA_odd_E_le_caseAS hfr hx hb) hAel hAidx
      hquad hEA
  have hXE : caseAX (x 1) ≤ caseAOddE b x := caseA_odd_X_le_E hfr hA hx hbo hb
  have hXstab : caseAX (x 1) ≤ CosetGeom.stab (x b) := by
    refine (caseA_X_le_Qy_pred hx hbo hb).trans ?_
    refine (caseA_Qy_le_caseAS hfr (v := x (b - 1)) (w := x b) (by
      have h := x.adj (b - 1) (by omega)
      rw [Nat.sub_add_cancel hb1] at h
      simpa [CosetGeom.nbrs] using h)).trans ?_
    exact caseAS_le_stab_right (x (b - 1)) (x b)
  have hXN : caseAX (x 1) ≤
      Subgroup.normalizer (CosetGeom.Qy (x b) : Set (f112Amalgam L1 L2 S).Ghat) :=
    hXstab.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (CosetGeom.stab (x b)))
  have hXEN : caseAX (x 1) ≤
      Subgroup.normalizer (caseAOddE b x : Set (f112Amalgam L1 L2 S).Ghat) :=
    ((Subgroup.le_centralizer_iff).mp hEcent).trans
      (Subgroup.centralizer_le_normalizer (caseAOddE b x : Set (f112Amalgam L1 L2 S).Ghat))
  have hXEQ : caseAX (x 1) ≤
      Subgroup.normalizer (caseAOddE b x ⊓ CosetGeom.Qy (x b) :
        Set (f112Amalgam L1 L2 S).Ghat) :=
    (le_inf hXEN hXN).trans Subgroup.inf_normalizer_le_normalizer_inf
  refine le_antisymm ?_ (sup_le hXE inf_le_left)
  intro e he
  have heXQ : e ∈ caseAX (x 1) ⊔ CosetGeom.Qy (x b) := hle he
  have hXQset : (↑(caseAX (x 1) ⊔ CosetGeom.Qy (x b)) : Set (f112Amalgam L1 L2 S).Ghat) =
      (caseAX (x 1) : Set (f112Amalgam L1 L2 S).Ghat) *
        (CosetGeom.Qy (x b) : Set (f112Amalgam L1 L2 S).Ghat) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (caseAX (x 1)) (CosetGeom.Qy (x b)) hXN
  have heXQ' : e ∈ (caseAX (x 1) : Set (f112Amalgam L1 L2 S).Ghat) *
      (CosetGeom.Qy (x b) : Set (f112Amalgam L1 L2 S).Ghat) := by
    rw [← hXQset]
    exact heXQ
  obtain ⟨y, hyX, z, hzQ, hyz⟩ := Set.mem_mul.mp heXQ' 
  have hzE : z ∈ caseAOddE b x := by
    have hzeq : z = y⁻¹ * e := by
      calc z = y⁻¹ * (y * z) := (inv_mul_cancel_left y z).symm
        _ = y⁻¹ * e := by rw [hyz]
    rw [hzeq]
    exact (caseAOddE b x).mul_mem ((caseAOddE b x).inv_mem (hXE hyX)) he
  have hmem : e ∈ (caseAX (x 1) : Set (f112Amalgam L1 L2 S).Ghat) *
      (((caseAOddE b x ⊓ CosetGeom.Qy (x b) : Subgroup (f112Amalgam L1 L2 S).Ghat) :
        Subgroup (f112Amalgam L1 L2 S).Ghat) : Set (f112Amalgam L1 L2 S).Ghat) :=
    Set.mem_mul.mpr ⟨y, hyX, z, ⟨hzE, hzQ⟩, hyz⟩
  rw [← Subgroup.coe_mul_of_left_le_normalizer_right (caseAX (x 1))
    (caseAOddE b x ⊓ CosetGeom.Qy (x b)) hXEQ] at hmem
  exact hmem

private theorem oddbb_mem_E_exists_mul
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) {e : (f112Amalgam L1 L2 S).Ghat} (he : e ∈ caseAOddE b x) :
    ∃ y ∈ caseAX (x 1), ∃ z ∈ CosetGeom.Qy (x b) ⊓ caseAOddE b x, y * z = e := by
  have hb1 : 1 ≤ b := by omega
  have hXE : caseAX (x 1) ≤ caseAOddE b x := caseA_odd_X_le_E hfr hA hx hbo hb
  have hXstab : caseAX (x 1) ≤ CosetGeom.stab (x b) := by
    refine (caseA_X_le_Qy_pred hx hbo hb).trans ?_
    refine (caseA_Qy_le_caseAS hfr (v := x (b - 1)) (w := x b) (by
      have h := x.adj (b - 1) (by omega)
      rw [Nat.sub_add_cancel hb1] at h
      simpa [CosetGeom.nbrs] using h)).trans ?_
    exact caseAS_le_stab_right (x (b - 1)) (x b)
  have hXN : caseAX (x 1) ≤
      Subgroup.normalizer (CosetGeom.Qy (x b) : Set (f112Amalgam L1 L2 S).Ghat) :=
    hXstab.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (CosetGeom.stab (x b)))
  have hle : caseAOddE b x ≤ caseAX (x 1) ⊔ CosetGeom.Qy (x b) := by
    rw [caseA_odd_E_eq_sup hfr hA hx hbo hb]
    exact sup_le le_sup_left (inf_le_right.trans le_sup_right)
  have hXQ : (caseAX (x 1) : Set (f112Amalgam L1 L2 S).Ghat) *
      (CosetGeom.Qy (x b) : Set (f112Amalgam L1 L2 S).Ghat) =
      (↑(caseAX (x 1) ⊔ CosetGeom.Qy (x b)) : Set (f112Amalgam L1 L2 S).Ghat) :=
    (Subgroup.coe_mul_of_left_le_normalizer_right (caseAX (x 1)) (CosetGeom.Qy (x b)) hXN).symm
  have hset : (↑(caseAOddE b x) : Set (f112Amalgam L1 L2 S).Ghat) =
      (caseAX (x 1) : Set (f112Amalgam L1 L2 S).Ghat) *
        (((CosetGeom.Qy (x b) ⊓ caseAOddE b x : Subgroup (f112Amalgam L1 L2 S).Ghat) :
          Subgroup (f112Amalgam L1 L2 S).Ghat) : Set (f112Amalgam L1 L2 S).Ghat) := by
    have hmul := Subgroup.mul_inf_assoc (caseAX (x 1)) (CosetGeom.Qy (x b)) (caseAOddE b x) hXE
    rw [hXQ, Set.inter_eq_right.mpr (fun e he' => hle he')] at hmul
    exact hmul.symm
  have he' : e ∈ (caseAX (x 1) : Set (f112Amalgam L1 L2 S).Ghat) *
      (((CosetGeom.Qy (x b) ⊓ caseAOddE b x : Subgroup (f112Amalgam L1 L2 S).Ghat) :
        Subgroup (f112Amalgam L1 L2 S).Ghat) : Set (f112Amalgam L1 L2 S).Ghat) := by
    rw [← hset]; exact he
  exact Set.mem_mul.mp he'

theorem caseA_odd_exists_involution
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) :
    ∃ t : (f112Amalgam L1 L2 S).Ghat, t ∈ caseAS (x 1) (x 2) ∧ t * t = 1 ∧
      t ∉ CosetGeom.Qy (x 1) ∧ ∀ e ∈ caseAOddE b x, e * t * e⁻¹ * t⁻¹ ∈ caseAX (x 1) := by
  have hδ : CosetGeom.vtype (x b) = false :=
    (hx.vtype_eq_false_iff_odd (i := b) le_rfl).mpr hbo
  have hb1 : 1 ≤ b := by omega
  have hnot := caseA_not_X_end_le_Qy_one hfr hx hbo hb
  obtain ⟨t, htXδ, htQ1⟩ : ∃ t, t ∈ caseAX (x b) ∧ t ∉ CosetGeom.Qy (x 1) := by
    by_contra h
    exact hnot fun t ht => by
      by_contra htQ
      exact h ⟨t, ht, htQ⟩
  have hQ2 : t ∈ CosetGeom.Qy (x 2) := caseA_X_end_le_Qy_two hx hbo hb htXδ
  have htS : t ∈ caseAS (x 1) (x 2) := by
    have hQy : CosetGeom.Qy (x 2) ≤ caseAS (x 2) (x 1) :=
      caseA_Qy_le_caseAS hfr (v := x 2) (w := x 1) (by
        simpa [CosetGeom.nbrs] using (x.adj 1 (by omega)).symm)
    rw [caseAS_comm] at hQy
    exact hQy hQ2
  have ht2 : t * t = 1 := by
    have h2 := (caseA_isElemAbelian_X hfr hδ).2 t htXδ
    rwa [pow_two] at h2
  refine ⟨t, htS, ht2, htQ1, ?_⟩
  intro e he
  obtain ⟨y, hyX, z, hz, hyz⟩ := oddbb_mem_E_exists_mul hfr hA hx hbo hb he
  have hzQ : z ∈ CosetGeom.Qy (x b) := (Subgroup.mem_inf.mp hz).1
  have hzt : ⁅z, t⁆ ∈ caseAX (x 1) := by
    have h1 : ⁅z, t⁆ ∈ ⁅CosetGeom.Qy (x b), caseAX (x b)⁆ :=
      Subgroup.commutator_mem_commutator hzQ htXδ
    have h2 : ⁅z, t⁆ ∈ ⁅caseAX (x b), CosetGeom.Qy (x b)⁆ := by
      rwa [Subgroup.commutator_comm] at h1
    exact ((caseA_commutator_X_Qy_le_Z hfr hδ).trans
      ((caseA_Z_end_le_X hfr hx hbo hb).trans inf_le_left)) h2
  have hyt : ⁅y, t⁆ ∈ caseAX (x 1) := by
    have htstab : t ∈ CosetGeom.stab (x 1) := caseAS_le_stab_left (x 1) (x 2) htS
    have htN : t ∈ Subgroup.normalizer (caseAX (x 1) : Set (f112Amalgam L1 L2 S).Ghat) :=
      caseA_stab_le_normalizer_X (x 1) htstab
    have hty : t * y⁻¹ * t⁻¹ ∈ caseAX (x 1) :=
      (Subgroup.mem_normalizer_iff.mp htN y⁻¹).mp ((caseAX (x 1)).inv_mem hyX)
    rw [commutatorElement_def]
    simpa only [mul_assoc] using (caseAX (x 1)).mul_mem hyX hty
  rw [← hyz, ← commutatorElement_def, commutatorElement_mul_left_eq_conj_mul]
  exact (caseAX (x 1)).mul_mem
    ((caseAX (x 1)).mul_mem ((caseAX (x 1)).mul_mem hyX hzt) ((caseAX (x 1)).inv_mem hyX)) hyt

private theorem oddbb_relIndex_E_N_eq
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) :
    (caseAOddE b x).relIndex (caseAN (x 1)) = (2 ^ (2 * a + 1)) ^ 2 := by
  obtain ⟨t, htS, ht2, htQ, htcomm⟩ := caseA_odd_exists_involution hfr hA hx hbo hb
  have hv1 : CosetGeom.vtype (x 1) = false := by
    have h := CosetGeom.vtype_ne_of_adj (x.adj 0 (by omega))
    rw [hx.type_two] at h
    cases hv : CosetGeom.vtype (x 1) <;> simp_all
  have hτ : x 2 ∈ CosetGeom.nbrs (x 1) := by
    simpa [CosetGeom.nbrs] using x.adj 1 (by omega)
  have hEN : caseAOddE b x ≤ caseAN (x 1) :=
    (show caseAOddE b x ≤ caseAOddN2 b x from inf_le_left).trans
      (show caseAOddN2 b x ≤ caseAN (x 1) from inf_le_left)
  have hEstab : caseAOddE b x ≤ CosetGeom.stab (x 1) :=
    hEN.trans (((caseA_N_le_Y hfr hA hv1).trans inf_le_left).trans (caseA_Qy_le_stab (x 1)))
  have hEC : caseAOddE b x ≤ centralizerMod (caseAX (x 1)) (caseAN (x 1))
      (Subgroup.zpowers t) := by
    intro e he
    rw [mem_centralizerMod]
    exact ⟨hEN he, caseA_stab_le_normalizer_X (x 1) (hEstab he),
      oddbb_commutator_zpowers_mem ht2 (htcomm e he)⟩
  haveI : Finite ↥(caseAN (x 1)) :=
    oddbb_finite_of_le_stab (H := caseAN (x 1))
      (((caseA_N_le_Y hfr hA hv1).trans inf_le_left).trans (caseA_Qy_le_stab (x 1)))
  have hErel : (caseAOddE b x).relIndex (caseAN (x 1)) ≠ 0 := by
    haveI : (caseAOddE b x).IsFiniteRelIndex (caseAN (x 1)) :=
      Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr
        (inferInstance : ((caseAOddE b x).subgroupOf (caseAN (x 1))).FiniteIndex)
    exact Subgroup.relIndex_ne_zero
  have hmono : (centralizerMod (caseAX (x 1)) (caseAN (x 1)) (Subgroup.zpowers t)).relIndex
      (caseAN (x 1)) ≤ (caseAOddE b x).relIndex (caseAN (x 1)) :=
    Subgroup.relIndex_le_of_le_left hEC hErel
  have hM7 := caseA_sq_le_relIndex_centralizerMod_N hfr hA hv1 hτ htS ht2 htQ
  have hEN2 : caseAOddE b x ≤ caseAOddN2 b x := inf_le_left
  have hN2N : caseAOddN2 b x ≤ caseAN (x 1) := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (H := caseAOddE b x) (K := caseAOddN2 b x)
    (L := caseAN (x 1)) hEN2 hN2N
  have hle1 := caseA_odd_relIndex_N2_E_le hfr hx hbo hb
  have hle2 := caseA_odd_relIndex_N_N2_le hfr hx hbo hb
  have hupper : (caseAOddE b x).relIndex (caseAN (x 1)) ≤ (2 ^ (2 * a + 1)) ^ 2 := by
    calc (caseAOddE b x).relIndex (caseAN (x 1))
        = (caseAOddE b x).relIndex (caseAOddN2 b x) *
            (caseAOddN2 b x).relIndex (caseAN (x 1)) := hmul.symm
      _ ≤ 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := Nat.mul_le_mul hle1 hle2
      _ = (2 ^ (2 * a + 1)) ^ 2 := (pow_two _).symm
  exact le_antisymm hupper (hM7.trans hmono)

private theorem oddbb_relIndex_split
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b)
    (hEN : (caseAOddE b x).relIndex (caseAN (x 1)) = (2 ^ (2 * a + 1)) ^ 2) :
    (caseAOddN2 b x).relIndex (caseAN (x 1)) = 2 ^ (2 * a + 1) ∧
      (caseAOddE b x).relIndex (caseAOddN2 b x) = 2 ^ (2 * a + 1) := by
  have hEN2 : caseAOddE b x ≤ caseAOddN2 b x := inf_le_left
  have hN2N : caseAOddN2 b x ≤ caseAN (x 1) := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (H := caseAOddE b x) (K := caseAOddN2 b x)
    (L := caseAN (x 1)) hEN2 hN2N
  have hprod : (caseAOddE b x).relIndex (caseAOddN2 b x) *
      (caseAOddN2 b x).relIndex (caseAN (x 1)) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hmul, hEN]
  have hle1 := caseA_odd_relIndex_N2_E_le hfr hx hbo hb
  have hle2 := caseA_odd_relIndex_N_N2_le hfr hx hbo hb
  have hq : 0 < 2 ^ (2 * a + 1) := pow_pos (by norm_num) _
  have hBq : (caseAOddN2 b x).relIndex (caseAN (x 1)) = 2 ^ (2 * a + 1) := by
    apply le_antisymm hle2
    have h1 : (2 ^ (2 * a + 1)) ^ 2 ≤
        2 ^ (2 * a + 1) * (caseAOddN2 b x).relIndex (caseAN (x 1)) := by
      rw [← hprod]
      exact Nat.mul_le_mul_right _ hle1
    rw [pow_two] at h1
    exact Nat.le_of_mul_le_mul_left h1 hq
  have hAq : (caseAOddE b x).relIndex (caseAOddN2 b x) = 2 ^ (2 * a + 1) := by
    have h2 : (caseAOddE b x).relIndex (caseAOddN2 b x) * 2 ^ (2 * a + 1) =
        (2 ^ (2 * a + 1)) ^ 2 := by
      rw [← hprod, hBq]
    rw [pow_two] at h2
    exact Nat.eq_of_mul_eq_mul_right hq h2
  exact ⟨hBq, hAq⟩

theorem caseA_odd_relIndex_N2_E_eq
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) :
    (caseAOddE b x).relIndex (caseAOddN2 b x) = 2 ^ (2 * a + 1) := by
  exact (oddbb_relIndex_split hfr hA hx hbo hb
    (oddbb_relIndex_E_N_eq hfr hA hx hbo hb)).2

theorem caseA_odd_N2_sup_eq
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) :
    caseAOddN2 b x ⊔ CosetGeom.Qy (x (b - 1)) = caseAS (x (b - 1)) (x (b - 2)) := by
  have hb2 : 2 ≤ b := by omega
  have hdist21 : CosetGeom.dist (x (b - 2)) (x (b - 1)) ≤ 1 :=
    (CosetGeom.dist_eq_one_iff_adj.mpr (by
      simpa [show b - 2 + 1 = b - 1 by omega] using x.adj (b - 2) (by omega))).le
  have hN2stab : caseAOddN2 b x ≤ CosetGeom.stab (x (b - 1)) :=
    (inf_le_right : caseAOddN2 b x ≤ CosetGeom.Qy (x (b - 2))).trans
      ((caseA_Qy_le_ballStab_one hfr (x (b - 2))).trans
        (CosetGeom.ballStab_le_stab_of_dist_le hdist21))
  have hN2S : caseAOddN2 b x ≤ caseAS (x (b - 1)) (x (b - 2)) := by
    have h := caseA_Qy_le_caseAS hfr (v := x (b - 2)) (w := x (b - 1)) (by
      change (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 2)) (x (b - 1))
      simpa [show b - 2 + 1 = b - 1 by omega] using x.adj (b - 2) (by omega))
    rw [caseAS_comm] at h
    exact (inf_le_right : caseAOddN2 b x ≤ CosetGeom.Qy (x (b - 2))).trans h
  have hQS : CosetGeom.Qy (x (b - 1)) ≤ caseAS (x (b - 1)) (x (b - 2)) :=
    caseA_Qy_le_caseAS hfr (v := x (b - 1)) (w := x (b - 2)) (by
      change (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 1)) (x (b - 2))
      simpa [show b - 2 + 1 = b - 1 by omega] using (x.adj (b - 2) (by omega)).symm)
  have hle : caseAOddN2 b x ⊔ CosetGeom.Qy (x (b - 1)) ≤
      caseAS (x (b - 1)) (x (b - 2)) := sup_le hN2S hQS
  have hβ2 : CosetGeom.vtype (x (b - 1)) = true := by
    have hev : Even (b - 1) := by
      obtain ⟨k, hk⟩ := hbo
      exact ⟨k, by omega⟩
    exact (hx.vtype_eq_true_iff_even (by omega)).mpr hev
  have hα2 : x (b - 2) ∈ CosetGeom.nbrs (x (b - 1)) := by
    change (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 1)) (x (b - 2))
    simpa [show b - 2 + 1 = b - 1 by omega] using (x.adj (b - 2) (by omega)).symm
  have hnorm : caseAOddN2 b x ≤
      Subgroup.normalizer (CosetGeom.Qy (x (b - 1)) : Set (f112Amalgam L1 L2 S).Ghat) :=
    hN2stab.trans (caseA_stab_le_normalizer_Qy (x (b - 1)))
  have hEeq := caseA_odd_relIndex_N2_E_eq hfr hA hx hbo hb
  have h1 : (CosetGeom.Qy (x (b - 1))).relIndex
      (caseAOddN2 b x ⊔ CosetGeom.Qy (x (b - 1))) = 2 ^ (2 * a + 1) := by
    rw [CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hnorm,
      ← Subgroup.inf_relIndex_left (caseAOddN2 b x) (CosetGeom.Qy (x (b - 1)))]
    exact hEeq
  have h2 : (CosetGeom.Qy (x (b - 1))).relIndex
      (caseAS (x (b - 1)) (x (b - 2))) = 2 ^ (2 * a + 1) :=
    caseA_relIndex_Qy_caseAS_type2 hfr hβ2 hα2
  have hcardL := Subgroup.relIndex_mul_card (H := CosetGeom.Qy (x (b - 1)))
    (K := caseAOddN2 b x ⊔ CosetGeom.Qy (x (b - 1)))
  rw [inf_eq_left.mpr le_sup_right] at hcardL
  have hcardS := Subgroup.relIndex_mul_card (H := CosetGeom.Qy (x (b - 1)))
    (K := caseAS (x (b - 1)) (x (b - 2)))
  rw [inf_eq_left.mpr hQS] at hcardS
  have hcard : Nat.card (caseAOddN2 b x ⊔ CosetGeom.Qy (x (b - 1)) :
        Subgroup (f112Amalgam L1 L2 S).Ghat) =
      Nat.card (caseAS (x (b - 1)) (x (b - 2)) :
        Subgroup (f112Amalgam L1 L2 S).Ghat) := by
    rw [← hcardL, ← hcardS, h1, h2]
  haveI : Finite ↥(caseAS (x (b - 1)) (x (b - 2))) :=
    oddbb_finite_of_le_stab (H := caseAS (x (b - 1)) (x (b - 2))) (v := x (b - 1))
      (caseAS_le_stab_left (x (b - 1)) (x (b - 2)))
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)

theorem caseA_odd_Z_end_le_centralizer
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) :
    caseAZ (x b) ≤
      Subgroup.centralizer (caseAS (x (b - 1)) (x (b - 2)) : Set (f112Amalgam L1 L2 S).Ghat) := by
  have hδ : CosetGeom.vtype (x b) = false :=
    (hx.vtype_eq_false_iff_odd (i := b) le_rfl).mpr hbo
  have hadj : (f112Amalgam L1 L2 S).graphHat.Adj (x b) (x (b - 1)) := by
    simpa [show b - 1 + 1 = b by omega] using (x.adj (b - 1) (by omega)).symm
  have hv1 : CosetGeom.vtype (x 1) = false := by
    have h := CosetGeom.vtype_ne_of_adj (x.adj 0 (by omega))
    rw [hx.type_two] at h
    cases h' : CosetGeom.vtype (x 1) <;> simp_all
  have hsup := caseA_odd_N2_sup_eq hfr hA hx hbo hb
  have hN2C : caseAOddN2 b x ≤
      Subgroup.centralizer (caseAZ (x b) : Set (f112Amalgam L1 L2 S).Ghat) := by
    have hN_le_Y : caseAN (x 1) ≤ caseAY (x 1) := caseA_N_le_Y hfr hA hv1
    have hN_le_CX : caseAN (x 1) ≤
        Subgroup.centralizer (caseAX (x 1) : Set (f112Amalgam L1 L2 S).Ghat) :=
      hN_le_Y.trans inf_le_right
    have hX_le_CN : caseAX (x 1) ≤
        Subgroup.centralizer (caseAN (x 1) : Set (f112Amalgam L1 L2 S).Ghat) :=
      (Subgroup.le_centralizer_iff).mp hN_le_CX
    have hZ_le_X : caseAZ (x b) ≤ caseAX (x 1) :=
      (caseA_Z_end_le_X hfr hx hbo hb).trans inf_le_left
    have hZ_le_CN : caseAZ (x b) ≤
        Subgroup.centralizer (caseAN (x 1) : Set (f112Amalgam L1 L2 S).Ghat) :=
      hZ_le_X.trans hX_le_CN
    have hN_le_CZ : caseAN (x 1) ≤
        Subgroup.centralizer (caseAZ (x b) : Set (f112Amalgam L1 L2 S).Ghat) :=
      (Subgroup.le_centralizer_iff).mp hZ_le_CN
    exact (inf_le_left : caseAOddN2 b x ≤ caseAN (x 1)).trans hN_le_CZ
  have hQC : CosetGeom.Qy (x (b - 1)) ≤
      Subgroup.centralizer (caseAZ (x b) : Set (f112Amalgam L1 L2 S).Ghat) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hZle : z ∈ caseAZ (x (b - 1)) :=
      caseA_Z_le_Z_of_adj hfr hδ (by
        simpa [show b - 1 + 1 = b by omega] using (x.adj (b - 1) (by omega)).symm) hz
    exact caseA_Z_commute_Qy (x (b - 1)) hZle hy
  have hSC : caseAS (x (b - 1)) (x (b - 2)) ≤
      Subgroup.centralizer (caseAZ (x b) : Set (f112Amalgam L1 L2 S).Ghat) := by
    rw [← hsup]
    exact sup_le hN2C hQC
  exact (Subgroup.le_centralizer_iff).mpr hSC

theorem caseA_odd_false
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbo : Odd b)
    (hb : 5 ≤ b) :
    False := by
  have hδ : CosetGeom.vtype (x b) = false :=
    (hx.vtype_eq_false_iff_odd (i := b) le_rfl).mpr hbo
  have hβ2 : CosetGeom.vtype (x (b - 1)) = true := by
    have hev : Even (b - 1) := by
      obtain ⟨k, hk⟩ := hbo
      exact ⟨k, by omega⟩
    exact (hx.vtype_eq_true_iff_even (by omega)).mpr hev
  have hadj1 : x b ∈ CosetGeom.nbrs (x (b - 1)) := by
    change (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 1)) (x b)
    simpa [show b - 1 + 1 = b by omega] using x.adj (b - 1) (by omega)
  have hadj2 : x (b - 2) ∈ CosetGeom.nbrs (x (b - 1)) := by
    change (f112Amalgam L1 L2 S).graphHat.Adj (x (b - 1)) (x (b - 2))
    simpa [show b - 2 + 1 = b - 1 by omega] using (x.adj (b - 2) (by omega)).symm
  have hZleZ : caseAZ (x b) ≤ caseAZ (x (b - 1)) :=
    caseA_Z_le_Z_of_adj hfr hδ (by
      simpa [show b - 1 + 1 = b by omega] using (x.adj (b - 1) (by omega)).symm)
  have hZleC : caseAZ (x b) ≤
      Subgroup.centralizer (caseAS (x (b - 1)) (x (b - 2)) :
        Set (f112Amalgam L1 L2 S).Ghat) :=
    caseA_odd_Z_end_le_centralizer hfr hA hx hbo hb
  have hcenter := caseA_Z_inf_centralizer_caseAS hfr hβ2 hadj2
  have hleZ2 : caseAZ (x b) ≤ caseAZ (x (b - 2)) := by
    rw [← hcenter]
    exact le_inf hZleZ hZleC
  have hnoBack : x.NoBack :=
    GPath.noBack_of_dist_eq (CosetGeom.connected rfl) x hx.geodesic
  have hne : x b ≠ x (b - 2) := by
    have h := hnoBack (b - 2) (by omega)
    rw [show b - 2 + 2 = b by omega] at h
    exact h.symm
  have hbot : caseAZ (x b) ⊓ caseAZ (x (b - 2)) = ⊥ :=
    caseA_Z_inf_Z_eq_bot hfr hβ2 hadj1 hadj2 hne
  have hbotZ : caseAZ (x b) = ⊥ :=
    (inf_eq_left.mpr hleZ2).symm.trans hbot
  exact caseA_Z_ne_bot hfr (x b) hbotZ

end CFSG.Quasithin.Stroth

end
