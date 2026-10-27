module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAEvenB
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAOmegaS
import CFSG.GroupTheory.DedekindNormalizer
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CaseAA1

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise

variable {G : Type} [Group G] {L1 L2 S : Subgroup G}

@[expose] noncomputable def caseAEvenN1 (b : ℕ) (x : GPath (f112Amalgam L1 L2 S).graphHat b) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  caseAN (x (b - 1)) ⊓ CosetGeom.Qy (x 1)

@[expose] noncomputable def caseAEvenN0 (b : ℕ) (x : GPath (f112Amalgam L1 L2 S).graphHat b) :
    Subgroup (f112Amalgam L1 L2 S).Ghat :=
  caseAEvenN1 b x ⊓ CosetGeom.Qy (x 0)

@[expose] noncomputable def caseAEvenN00 (b : ℕ) (x : GPath (f112Amalgam L1 L2 S).graphHat b)
    (l : f112Gamma L1 L2 S) : Subgroup (f112Amalgam L1 L2 S).Ghat :=
  caseAEvenN0 b x ⊓ CosetGeom.Qy l

variable [Finite G]

private theorem evencb_not_even_sub_one {b : ℕ} (hb : 1 ≤ b) (hbe : Even b) : ¬ Even (b - 1) := by
  intro hev
  have hodd : Odd b := by
    have h1 : Odd ((b - 1) + 1) := hev.add_one
    rwa [Nat.sub_add_cancel hb] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) hbe

theorem caseA_even_relIndex_N_N1
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    (caseAEvenN1 b x).relIndex (caseAN (x (b - 1))) ≤ 2 ^ (2 * a + 1) := by
  have hb1 : 1 ≤ b := by omega
  have hp_false : CosetGeom.vtype (x (b - 1)) = false :=
    (hx.vtype_eq_false_iff_odd (i := b - 1) (by omega)).mpr
      (Nat.not_even_iff_odd.mp (evencb_not_even_sub_one hb1 hbe))
  have hα1 : CosetGeom.vtype (x 1) = false := by
    have hiff := hx.vtype_eq_true_iff_even (show 1 ≤ b by omega)
    cases hv : CosetGeom.vtype (x 1) with
    | false => rfl
    | true => exact absurd (hiff.mp hv) Nat.not_even_one
  have hadj12 : (f112Amalgam L1 L2 S).graphHat.Adj (x 1) (x 2) := x.adj 1 (by omega)
  have h12 : x 2 ∈ CosetGeom.nbrs (x 1) := by simpa [CosetGeom.nbrs] using hadj12
  have h21 : x 1 ∈ CosetGeom.nbrs (x 2) := by simpa [CosetGeom.nbrs] using hadj12.symm
  have hNQ2 : caseAN (x (b - 1)) ≤ CosetGeom.Qy (x 2) :=
    caseA_N_le_Qy_symm hfr hx hbe hb
  have hQ2AS : CosetGeom.Qy (x 2) ≤ caseAS (x 1) (x 2) := by
    have h := caseA_Qy_le_caseAS (v := x 2) (w := x 1) hfr h21
    rwa [caseAS_comm] at h
  have hNAS : caseAN (x (b - 1)) ≤ caseAS (x 1) (x 2) := hNQ2.trans hQ2AS
  have hinv : caseAN (x (b - 1)) ≤
      Subgroup.closure {t | t ∈ caseAS (x 1) (x 2) ∧ t * t = 1} := by
    refine iSup₂_le fun w hw => ?_
    intro t ht
    have hwv : CosetGeom.vtype w = false := by
      have hsame : CosetGeom.vtype w = CosetGeom.vtype (x (b - 1)) :=
        ((CosetGeom.vtype_eq_iff_even_dist rfl (x (b - 1)) w).mpr
          (by rw [hw]; exact ⟨1, rfl⟩)).symm
      rw [hsame, hp_false]
    have ht2 : t * t = 1 := by
      have := (caseA_isElemAbelian_X hfr hwv).2 t ht
      simpa [pow_two] using this
    have htN : t ∈ caseAN (x (b - 1)) :=
      le_iSup₂ (f := fun w (_ : CosetGeom.dist (x (b - 1)) w = 2) => caseAX w) w hw ht
    exact Subgroup.subset_closure ⟨hNAS htN, ht2⟩
  simpa only [caseAEvenN1] using
    caseA_relIndex_inf_Qy_le_type1_of_involutions hfr hα1 h12 hinv

theorem caseA_even_relIndex_N1_N0 {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) :
    (caseAEvenN0 b x).relIndex (caseAEvenN1 b x) ≤ 2 ^ (2 * a + 1) := by
  have hb1 : 1 ≤ b := by
    by_contra h
    have hb0 : b = 0 := by omega
    subst b
    exact hx.not_le (caseA_Z_le_Qy (x 0))
  have h01 : x 1 ∈ CosetGeom.nbrs (x 0) := by
    simpa [CosetGeom.nbrs] using x.adj 0 (by omega)
  have h10 : x 0 ∈ CosetGeom.nbrs (x 1) := by
    simpa [CosetGeom.nbrs] using (x.adj 0 (by omega)).symm
  have hQ : CosetGeom.Qy (x 1) ≤ caseAS (x 0) (x 1) := by
    have h := caseA_Qy_le_caseAS (v := x 1) (w := x 0) hfr h10
    rwa [caseAS_comm] at h
  have hA : caseAEvenN1 b x ≤ caseAS (x 0) (x 1) := inf_le_right.trans hQ
  have := caseA_relIndex_inf_Qy_le_type2 hfr hx.type_two h01 hA
  simpa only [caseAEvenN0] using this

theorem caseA_even_XInf_le_N0
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) {b : ℕ} {x : GPath (f112Amalgam L1 L2 S).graphHat b}
    (hx : caseACritPath L1 L2 S b x) (hbe : Even b) (hb : 5 ≤ b) :
    caseAEvenXInf b x ≤ caseAEvenN0 b x := by
  have hb1 : 1 ≤ b := by omega
  have hp_false : CosetGeom.vtype (x (b - 1)) = false :=
    (hx.vtype_eq_false_iff_odd (i := b - 1) (by omega)).mpr
      (Nat.not_even_iff_odd.mp (evencb_not_even_sub_one hb1 hbe))
  have hconn : (f112Amalgam L1 L2 S).graphHat.Connected := CosetGeom.connected rfl
  have hdist : CosetGeom.dist (x (b - 1)) (x 1) + 1 ≤ b - 1 := by
    have hle : CosetGeom.dist (x 1) (x (b - 1)) ≤ (b - 1) - 1 :=
      GPath.dist_le_sub hconn x (i := 1) (j := b - 1) (by omega) (by omega)
    rw [CosetGeom.dist_comm]
    omega
  have hXN : caseAX (x (b - 1)) ≤ caseAN (x (b - 1)) := caseA_X_le_N hfr hp_false
  have hXQ1 : caseAX (x (b - 1)) ≤ CosetGeom.Qy (x 1) :=
    caseA_X_le_Qy (k := b - 1) hx.ball hp_false hdist
  have hX : caseAX (x (b - 1)) ≤ caseAEvenN1 b x := le_inf hXN hXQ1
  unfold caseAEvenXInf caseAEvenN0
  exact inf_le_inf hX le_rfl

private theorem evenca_XInf_le_normalizer_Qy
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) :
    caseAEvenXInf b x ≤ Subgroup.normalizer (CosetGeom.Qy l : Set _) := by
  have hXleN0 : caseAEvenXInf b x ≤ caseAEvenN0 b x :=
    caseA_even_XInf_le_N0 hfr hx hbe hb
  have h1 : caseAEvenXInf b x ≤ CosetGeom.stab l :=
    (hXleN0.trans inf_le_right).trans
      ((caseA_Qy_le_caseAS hfr hl).trans (caseAS_le_stab_right (x 0) l))
  have h2 : CosetGeom.stab l ≤ Subgroup.normalizer (CosetGeom.Qy l : Set _) := by
    simpa only [CosetGeom.Qy] using
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (CosetGeom.stab l)
  exact h1.trans h2

theorem caseA_even_N0_eq_sup
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1) :
    caseAEvenN0 b x = caseAEvenXInf b x ⊔ caseAEvenN00 b x l := by
  have hb1 : 1 ≤ b := by omega
  have hp_false : CosetGeom.vtype (x (b - 1)) = false :=
    (hx.vtype_eq_false_iff_odd (i := b - 1) (by omega)).mpr
      (Nat.not_even_iff_odd.mp (evencb_not_even_sub_one hb1 hbe))
  have hαl : CosetGeom.vtype l = false := by
    have hne := CosetGeom.vtype_ne_of_adj hl
    rw [hx.type_two] at hne
    cases hv : CosetGeom.vtype l <;> simp_all
  have hl' : (f112Amalgam L1 L2 S).graphHat.Adj (x 0) l := hl
  have hτ : x 0 ∈ CosetGeom.nbrs l := by simpa [CosetGeom.nbrs] using hl'.symm
  have hQ0 : CosetGeom.Qy (x 0) ≤ caseAS l (x 0) := by
    have h := caseA_Qy_le_caseAS (v := x 0) (w := l) hfr hl
    rwa [caseAS_comm] at h
  have hAS : caseAEvenXInf b x ≤ caseAS l (x 0) := inf_le_right.trans hQ0
  have hES : caseAEvenN0 b x ≤ caseAS l (x 0) := inf_le_right.trans hQ0
  have hAel : IsElemAbelian 2 (caseAEvenXInf b x) :=
    (caseA_isElemAbelian_X hfr hp_false).mono inf_le_left
  have hAidx : (caseAEvenXInf b x ⊓ CosetGeom.Qy l).relIndex (caseAEvenXInf b x) =
      2 ^ (2 * a + 1) := by
    simpa only [caseAEvenF] using caseA_even_relIndex_F hfr hA hx hbe hb hl hl1
  have hquad : ⁅caseAX l, caseAEvenXInf b x⁆ ≤ caseAEvenXInf b x :=
    caseA_even_commutator_X_le hfr hA hx hbe hb hl
  have hEA : ∀ e ∈ caseAEvenN0 b x, ∀ y ∈ caseAEvenXInf b x, e * y = y * e := by
    intro e he y hy
    have heN1 : e ∈ caseAEvenN1 b x :=
      (show caseAEvenN0 b x ≤ caseAEvenN1 b x from inf_le_left) he
    have heN : e ∈ caseAN (x (b - 1)) :=
      (show caseAEvenN1 b x ≤ caseAN (x (b - 1)) from inf_le_left) heN1
    have heAY : e ∈ caseAY (x (b - 1)) := caseA_N_le_Y hfr hA hp_false heN
    have hecent : e ∈ Subgroup.centralizer (caseAX (x (b - 1)) : Set _) :=
      (Subgroup.mem_inf.mp heAY).2
    have hyX : y ∈ caseAX (x (b - 1)) :=
      (show caseAEvenXInf b x ≤ caseAX (x (b - 1)) from inf_le_left) hy
    exact ((Subgroup.mem_centralizer_iff.mp hecent) y hyX).symm
  have hsup : caseAEvenN0 b x ≤ caseAEvenXInf b x ⊔ CosetGeom.Qy l :=
    caseA_le_sup_Qy_of_commute hfr hαl hτ hAS hES hAel hAidx hquad hEA
  have hXleN0 : caseAEvenXInf b x ≤ caseAEvenN0 b x :=
    caseA_even_XInf_le_N0 hfr hx hbe hb
  have hN0le : caseAEvenN0 b x ≤ caseAEvenXInf b x ⊔ caseAEvenN00 b x l := by
    have h2 : caseAEvenN0 b x ≤
        (caseAEvenXInf b x ⊔ CosetGeom.Qy l) ⊓ caseAEvenN0 b x := le_inf hsup le_rfl
    rw [inf_comm, CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer hXleN0
      (evenca_XInf_le_normalizer_Qy hfr hx hbe hb hl)] at h2
    exact h2
  exact le_antisymm hN0le (sup_le hXleN0 inf_le_left)

theorem caseA_even_relIndex_N00
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1) :
    (caseAEvenN00 b x l).relIndex (caseAEvenN0 b x) = 2 ^ (2 * a + 1) := by
  have hsup := caseA_even_N0_eq_sup hfr hA hx hbe hb hl hl1
  have hXleN0 : caseAEvenXInf b x ≤ caseAEvenN0 b x :=
    caseA_even_XInf_le_N0 hfr hx hbe hb
  have hQl : caseAEvenXInf b x ≤ Subgroup.normalizer (CosetGeom.Qy l : Set _) :=
    evenca_XInf_le_normalizer_Qy hfr hx hbe hb hl
  have hcN0 : ⁅caseAEvenXInf b x, caseAEvenN0 b x⁆ ≤ caseAEvenN0 b x :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp
      (hXleN0.trans Subgroup.le_normalizer)
  have hcQl : ⁅caseAEvenXInf b x, CosetGeom.Qy l⁆ ≤ CosetGeom.Qy l :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hQl
  have hnorm : caseAEvenXInf b x ≤ Subgroup.normalizer (caseAEvenN00 b x l : Set _) := by
    refine (Subgroup.le_normalizer_iff_commutator_le_right).mpr ?_
    have hc : ⁅caseAEvenXInf b x, caseAEvenN0 b x ⊓ CosetGeom.Qy l⁆ ≤
        caseAEvenN0 b x ⊓ CosetGeom.Qy l :=
      le_inf ((Subgroup.commutator_mono le_rfl inf_le_left).trans hcN0)
             ((Subgroup.commutator_mono le_rfl inf_le_right).trans hcQl)
    simpa only [caseAEvenN00] using hc
  have hF : caseAEvenXInf b x ⊓ caseAEvenN00 b x l = caseAEvenF b x l := by
    have hX : caseAEvenXInf b x ⊓ caseAEvenN0 b x = caseAEvenXInf b x :=
      inf_eq_left.mpr hXleN0
    unfold caseAEvenN00 caseAEvenF
    rw [← inf_assoc, hX]
  rw [hsup]
  rw [CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer hnorm]
  rw [← Subgroup.inf_relIndex_left (caseAEvenXInf b x) (caseAEvenN00 b x l), hF]
  exact caseA_even_relIndex_F hfr hA hx hbe hb hl hl1

private theorem evencb_caseAY_le_Qy (v : f112Gamma L1 L2 S) : caseAY v ≤ CosetGeom.Qy v := by
  unfold caseAY
  exact inf_le_left

private theorem evencb_caseAY_le_centralizer (v : f112Gamma L1 L2 S) :
    caseAY v ≤ Subgroup.centralizer (caseAX v : Set (f112Amalgam L1 L2 S).Ghat) := by
  unfold caseAY
  exact inf_le_right

private theorem evencb_relIndex_centralizer_le_card_commutator {H : Type*} [Group H]
    (Q : Subgroup H) (z : H) [Finite ↥⁅Q, Subgroup.zpowers z⁆] :
    (Subgroup.centralizer ({z} : Set H)).relIndex Q ≤ Nat.card ↥⁅Q, Subgroup.zpowers z⁆ := by
  classical
  let φ : ↥Q ⧸ (Subgroup.centralizer ({z} : Set H)).subgroupOf Q → ↥⁅Q, Subgroup.zpowers z⁆ :=
    Quotient.lift (fun q : ↥Q =>
      (⟨(q : H) * z * (q : H)⁻¹ * z⁻¹,
        Subgroup.commutator_mem_commutator q.2 (Subgroup.mem_zpowers z)⟩ :
        ↥⁅Q, Subgroup.zpowers z⁆)) (by
      intro a b hab
      have hab := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hab
      apply Subtype.ext
      change (a : H) * z * (a : H)⁻¹ * z⁻¹ = (b : H) * z * (b : H)⁻¹ * z⁻¹
      have hab' : ((a : H)⁻¹ * b) * z = z * ((a : H)⁻¹ * b) := by
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hab
      calc (a : H) * z * (a : H)⁻¹ * z⁻¹
          = (a : H) * (z * ((a : H)⁻¹ * b)) * ((a : H)⁻¹ * b)⁻¹ * (a : H)⁻¹ * z⁻¹ := by group
        _ = (a : H) * (((a : H)⁻¹ * b) * z) * ((a : H)⁻¹ * b)⁻¹ * (a : H)⁻¹ * z⁻¹ := by
          rw [hab']
        _ = (b : H) * z * (b : H)⁻¹ * z⁻¹ := by group)
  have hφ : Function.Injective φ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    have h := congrArg Subtype.val hab
    change (a : H) * z * (a : H)⁻¹ * z⁻¹ = (b : H) * z * (b : H)⁻¹ * z⁻¹ at h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have h' : (a : H) * z * (a : H)⁻¹ = (b : H) * z * (b : H)⁻¹ := mul_right_cancel h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (a : H)⁻¹ * b * z = (a : H)⁻¹ * ((b : H) * z * (b : H)⁻¹) * b := by group
      _ = (a : H)⁻¹ * ((a : H) * z * (a : H)⁻¹) * b := by rw [h']
      _ = z * ((a : H)⁻¹ * b) := by group
  exact Nat.card_le_card_of_injective φ hφ

private theorem evencb_relIndex_mul_le_relIndex {V₁ W U B : Subgroup (f112Amalgam L1 L2 S).Ghat}
    [Finite ↥U] (hV₁W : V₁ ≤ W) (hWU : W ≤ U)
    (hUW : U ≤ Subgroup.normalizer (W : Set (f112Amalgam L1 L2 S).Ghat))
    (hBW : B ≤ Subgroup.normalizer (W : Set (f112Amalgam L1 L2 S).Ghat)) :
    (centralizerMod V₁ W B).relIndex W * (centralizerMod W U B).relIndex U ≤
      (centralizerMod V₁ U B).relIndex U := by
  have hCC₂ : centralizerMod V₁ U B ≤ centralizerMod W U B := fun x hx =>
    ⟨hx.1, hUW hx.1, fun b hb => hV₁W (hx.2.2 b hb)⟩
  have hWC₂ : W ≤ centralizerMod W U B := fun w hw => by
    refine ⟨hWU hw, Subgroup.le_normalizer hw, fun b hb => ?_⟩
    have h1 : b * w⁻¹ * b⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hBW hb) w⁻¹).mp (W.inv_mem hw)
    have e : w * b * w⁻¹ * b⁻¹ = w * (b * w⁻¹ * b⁻¹) := by group
    rw [e]
    exact W.mul_mem hw h1
  have hmul := Subgroup.relIndex_mul_relIndex (centralizerMod V₁ U B) (centralizerMod W U B) U
    hCC₂ (centralizerMod_le_left _ _ _)
  have e : centralizerMod V₁ W B = centralizerMod V₁ U B ⊓ W := by
    ext x
    constructor
    · rintro ⟨hxW, hxN, hx⟩
      exact ⟨⟨hWU hxW, hxN, hx⟩, hxW⟩
    · rintro ⟨⟨-, hxN, hx⟩, hxW⟩
      exact ⟨hxW, hxN, hx⟩
  have hne : (centralizerMod V₁ U B).relIndex (centralizerMod W U B) ≠ 0 := by
    have hfin : Finite ↥(centralizerMod W U B) :=
      Finite.of_injective (Subgroup.inclusion (centralizerMod_le_left W U B))
        (Subgroup.inclusion_injective _)
    haveI := hfin
    show ((centralizerMod V₁ U B).subgroupOf (centralizerMod W U B)).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  rw [e, Subgroup.inf_relIndex_right, ← hmul]
  exact Nat.mul_le_mul_right _ (Subgroup.relIndex_le_of_le_right hWC₂ hne)

private theorem evencb_relIndex_N_centralizer_le_mul
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1)
    {u : (f112Amalgam L1 L2 S).Ghat} :
    (caseAN (x (b - 1)) ⊓ Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
        (caseAN (x (b - 1))) ≤
      (2 ^ (2 * a + 1)) ^ 3 *
        (caseAEvenN00 b x l ⊓
          Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
          (caseAEvenN00 b x l) := by
  set C : Subgroup (f112Amalgam L1 L2 S).Ghat :=
    Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat) with hC
  have hα : CosetGeom.vtype (x (b - 1)) = false :=
    (hx.vtype_eq_false_iff_odd (i := b - 1) (by omega)).mpr
      (Nat.not_even_iff_odd.mp (evencb_not_even_sub_one (by omega) hbe))
  haveI : Finite ↥(CosetGeom.stab (x (b - 1))) := caseA_finite_stab L1 L2 S (x (b - 1))
  have hNstab : caseAN (x (b - 1)) ≤ CosetGeom.stab (x (b - 1)) :=
    (caseA_N_le_Y hfr hA hα).trans
      ((evencb_caseAY_le_Qy (x (b - 1))).trans (caseA_Qy_le_stab (x (b - 1))))
  have hstep : ∀ {A B : Subgroup (f112Amalgam L1 L2 S).Ghat},
      A ≤ CosetGeom.stab (x (b - 1)) → B ≤ A →
      (A ⊓ C).relIndex A ≤ B.relIndex A * (B ⊓ C).relIndex B := by
    intro A B hAstab hBA
    haveI : Finite ↥A :=
      Finite.of_injective (Subgroup.inclusion hAstab) (Subgroup.inclusion_injective hAstab)
    have hne : (B ⊓ C).relIndex A ≠ 0 := by
      haveI : Finite (↥A ⧸ ((B ⊓ C).subgroupOf A)) := inferInstance
      show ((B ⊓ C).subgroupOf A).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    calc (A ⊓ C).relIndex A ≤ (B ⊓ C).relIndex A :=
          Subgroup.relIndex_le_of_le_left (le_inf (inf_le_left.trans hBA) inf_le_right) hne
      _ = B.relIndex A * (B ⊓ C).relIndex B := by
          rw [← Subgroup.relIndex_mul_relIndex (B ⊓ C) B A inf_le_left hBA]
          exact Nat.mul_comm _ _
  have h1 := hstep (A := caseAN (x (b - 1))) (B := caseAEvenN1 b x) hNstab
    (show caseAEvenN1 b x ≤ caseAN (x (b - 1)) from inf_le_left)
  have h2 := hstep (A := caseAEvenN1 b x) (B := caseAEvenN0 b x)
    ((show caseAEvenN1 b x ≤ caseAN (x (b - 1)) from inf_le_left).trans hNstab)
    (show caseAEvenN0 b x ≤ caseAEvenN1 b x from inf_le_left)
  have h3 := hstep (A := caseAEvenN0 b x) (B := caseAEvenN00 b x l)
    ((show caseAEvenN0 b x ≤ caseAEvenN1 b x from inf_le_left).trans
      ((show caseAEvenN1 b x ≤ caseAN (x (b - 1)) from inf_le_left).trans hNstab))
    (show caseAEvenN00 b x l ≤ caseAEvenN0 b x from inf_le_left)
  have e1 : (caseAEvenN1 b x).relIndex (caseAN (x (b - 1))) ≤ 2 ^ (2 * a + 1) :=
    caseA_even_relIndex_N_N1 hfr hx hbe hb
  have e2 : (caseAEvenN0 b x).relIndex (caseAEvenN1 b x) ≤ 2 ^ (2 * a + 1) :=
    caseA_even_relIndex_N1_N0 hfr hx
  have e3 : (caseAEvenN00 b x l).relIndex (caseAEvenN0 b x) = 2 ^ (2 * a + 1) :=
    caseA_even_relIndex_N00 hfr hA hx hbe hb hl hl1
  calc (caseAN (x (b - 1)) ⊓ C).relIndex (caseAN (x (b - 1)))
      ≤ (caseAEvenN1 b x).relIndex (caseAN (x (b - 1))) *
          ((caseAEvenN1 b x) ⊓ C).relIndex (caseAEvenN1 b x) := h1
    _ ≤ (2 ^ (2 * a + 1)) * ((caseAEvenN1 b x) ⊓ C).relIndex (caseAEvenN1 b x) :=
        Nat.mul_le_mul_right _ e1
    _ ≤ (2 ^ (2 * a + 1)) *
          ((2 ^ (2 * a + 1)) * ((caseAEvenN0 b x) ⊓ C).relIndex (caseAEvenN0 b x)) := by
        refine Nat.mul_le_mul_left _ ?_
        exact h2.trans (Nat.mul_le_mul_right _ e2)
    _ ≤ (2 ^ (2 * a + 1)) *
          ((2 ^ (2 * a + 1)) *
            ((2 ^ (2 * a + 1)) * ((caseAEvenN00 b x l) ⊓ C).relIndex (caseAEvenN00 b x l))) := by
        refine Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ?_)
        exact h3.trans (Nat.mul_le_mul_right _ (le_of_eq e3))
    _ = (2 ^ (2 * a + 1)) ^ 3 * ((caseAEvenN00 b x l) ⊓ C).relIndex (caseAEvenN00 b x l) := by
        ring

theorem caseA_relIndex_centralizer_le_of_le_Qy
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {α : f112Gamma L1 L2 S}
    (hα : CosetGeom.vtype α = false) {B : Subgroup (f112Amalgam L1 L2 S).Ghat}
    (hB : B ≤ CosetGeom.Qy α) {u : (f112Amalgam L1 L2 S).Ghat} (hu : u ∈ caseAX α) :
    (B ⊓ Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex B ≤
      2 ^ (2 * a + 1) := by
  haveI : Finite ↥(CosetGeom.stab α) := caseA_finite_stab L1 L2 S α
  haveI : Finite ↥(caseAZ α) :=
    Finite.of_injective (Subgroup.inclusion ((caseA_Z_le_Qy α).trans (caseA_Qy_le_stab α)))
      (Subgroup.inclusion_injective _)
  refine (caseA_relIndex_centralizer_le_card_of_comm_mem (B := B) (Z := caseAZ α) (u := u)
    ?_ ?_).trans (le_of_eq (caseA_card_Z_type1 hfr hα))
  · intro z hz b hb
    exact caseA_Z_commute_Qy α hz (hB hb)
  · intro b hb
    have hbu : b * u * b⁻¹ * u⁻¹ ∈ ⁅CosetGeom.Qy α, caseAX α⁆ :=
      Subgroup.commutator_mem_commutator (hB hb) hu
    rw [Subgroup.commutator_comm] at hbu
    exact caseA_commutator_X_Qy_le_Z hfr hα hbu

theorem caseA_even_le_relIndex_N_centralizer
    {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1)
    {u : (f112Amalgam L1 L2 S).Ghat} (hu : u ∈ caseAX l) (huQ : u ∉ CosetGeom.Qy (x (b - 1))) :
    (2 ^ (2 * a + 1)) ^ 4 ≤
      (caseAN (x (b - 1)) ⊓ Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
        (caseAN (x (b - 1))) := by
  have hα : CosetGeom.vtype (x (b - 1)) = false :=
    (hx.vtype_eq_false_iff_odd (i := b - 1) (by omega)).mpr
      (Nat.not_even_iff_odd.mp (evencb_not_even_sub_one (by omega) hbe))
  have hτ : x (b - 2) ∈ CosetGeom.nbrs (x (b - 1)) := by
    have hb1 : (b - 2) + 1 = b - 1 := by omega
    simpa [CosetGeom.nbrs, hb1] using (x.adj (b - 2) (by omega)).symm
  have hmem := caseA_even_mem_caseAS hfr hx hbe hb hl hu
  have htu : u ∈ caseAS (x (b - 1)) (x (b - 2)) := hmem.1
  have ht2 : u * u = 1 := hmem.2
  have hM7X := caseA_sq_le_relIndex_centralizerMod_X hfr hα hτ htu ht2 huQ
  have hM7N := caseA_sq_le_relIndex_centralizerMod_N hfr hA hα hτ htu ht2 huQ
  have hVW : caseAZ (x (b - 1)) ≤ caseAX (x (b - 1)) := caseA_Z_le_X hfr hα
  have hWU : caseAX (x (b - 1)) ≤ caseAN (x (b - 1)) := caseA_X_le_N hfr hα
  have hNY : caseAN (x (b - 1)) ≤ caseAY (x (b - 1)) := caseA_N_le_Y hfr hA hα
  have hUW : caseAN (x (b - 1)) ≤
      Subgroup.normalizer (caseAX (x (b - 1)) : Set (f112Amalgam L1 L2 S).Ghat) :=
    hNY.trans ((evencb_caseAY_le_centralizer (x (b - 1))).trans
      (Subgroup.centralizer_le_normalizer _))
  have huStab : u ∈ CosetGeom.stab (x (b - 1)) :=
    caseAS_le_stab_left (x (b - 1)) (x (b - 2)) htu
  have hBW : Subgroup.zpowers u ≤
      Subgroup.normalizer (caseAX (x (b - 1)) : Set (f112Amalgam L1 L2 S).Ghat) :=
    Subgroup.zpowers_le.mpr (caseA_stab_le_normalizer_X (x (b - 1)) huStab)
  haveI : Finite ↥(CosetGeom.stab (x (b - 1))) := caseA_finite_stab L1 L2 S (x (b - 1))
  have hNstab : caseAN (x (b - 1)) ≤ CosetGeom.stab (x (b - 1)) :=
    hNY.trans ((evencb_caseAY_le_Qy (x (b - 1))).trans (caseA_Qy_le_stab (x (b - 1))))
  haveI : Finite ↥(caseAN (x (b - 1))) :=
    Finite.of_injective (Subgroup.inclusion hNstab) (Subgroup.inclusion_injective hNstab)
  have hprod := evencb_relIndex_mul_le_relIndex hVW hWU hUW hBW
  have hNz : caseAN (x (b - 1)) ≤
      Subgroup.normalizer (caseAZ (x (b - 1)) : Set (f112Amalgam L1 L2 S).Ghat) :=
    hNstab.trans (caseA_stab_le_normalizer_Z (x (b - 1)))
  have hIX8 := caseA_relIndex_centralizerMod_le_relIndex_centralizer
    (Z := caseAZ (x (b - 1))) (N := caseAN (x (b - 1))) (u := u) hNz
  calc (2 ^ (2 * a + 1)) ^ 4
      = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1)) ^ 2 := by ring
    _ ≤ (centralizerMod (caseAZ (x (b - 1))) (caseAX (x (b - 1)))
            (Subgroup.zpowers u)).relIndex (caseAX (x (b - 1))) *
          (centralizerMod (caseAX (x (b - 1))) (caseAN (x (b - 1)))
            (Subgroup.zpowers u)).relIndex (caseAN (x (b - 1))) :=
        Nat.mul_le_mul hM7X hM7N
    _ ≤ (centralizerMod (caseAZ (x (b - 1))) (caseAN (x (b - 1)))
            (Subgroup.zpowers u)).relIndex (caseAN (x (b - 1))) := hprod
    _ ≤ (caseAN (x (b - 1)) ⊓
          Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
          (caseAN (x (b - 1))) := hIX8

theorem caseA_even_commutator_N00_eq
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1)
    {u : (f112Amalgam L1 L2 S).Ghat} (hu : u ∈ caseAX l) (huQ : u ∉ CosetGeom.Qy (x (b - 1))) :
    ⁅caseAEvenN00 b x l, Subgroup.zpowers u⁆ = caseAZ l := by
  have hl_false : CosetGeom.vtype l = false :=
    CosetGeom.vtype_eq_false_of_adj (by simpa [CosetGeom.nbrs] using hl) hx.type_two
  have hchain := evencb_relIndex_N_centralizer_le_mul hfr hA hx hbe hb hl hl1 (u := u)
  have h4 := caseA_even_le_relIndex_N_centralizer hfr hA hx hbe hb hl hl1 hu huQ
  have hstep2 : (caseAEvenN00 b x l ⊓
      Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
      (caseAEvenN00 b x l) ≤ 2 ^ (2 * a + 1) :=
    caseA_relIndex_centralizer_le_of_le_Qy hfr hl_false inf_le_right hu
  have hEq : (2 ^ (2 * a + 1)) ^ 3 *
      ((caseAEvenN00 b x l ⊓
        Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
        (caseAEvenN00 b x l)) =
      (2 ^ (2 * a + 1)) ^ 3 * (2 ^ (2 * a + 1)) :=
    le_antisymm (Nat.mul_le_mul_left _ hstep2) (by
      calc (2 ^ (2 * a + 1)) ^ 3 * (2 ^ (2 * a + 1))
          = (2 ^ (2 * a + 1)) ^ 4 := by ring
        _ ≤ (caseAN (x (b - 1)) ⊓
              Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
              (caseAN (x (b - 1))) := h4
        _ ≤ (2 ^ (2 * a + 1)) ^ 3 *
              ((caseAEvenN00 b x l ⊓
                Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
                (caseAEvenN00 b x l)) := hchain)
  have hN00 : (caseAEvenN00 b x l ⊓
      Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
      (caseAEvenN00 b x l) = 2 ^ (2 * a + 1) :=
    (Nat.mul_left_cancel_iff (by positivity : 0 < ((2 : ℕ) ^ (2 * a + 1)) ^ 3)).mp hEq
  have hcommidx : (Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat)).relIndex
      (caseAEvenN00 b x l) = 2 ^ (2 * a + 1) := by
    rw [← Subgroup.inf_relIndex_right
      (H := Subgroup.centralizer ({u} : Set (f112Amalgam L1 L2 S).Ghat))
      (K := caseAEvenN00 b x l)]
    simpa [inf_comm] using hN00
  have hcomm_le : ⁅caseAEvenN00 b x l, Subgroup.zpowers u⁆ ≤ caseAZ l :=
    (Subgroup.commutator_mono inf_le_right (Subgroup.zpowers_le.mpr hu)).trans
      ((Subgroup.commutator_comm (CosetGeom.Qy l) (caseAX l)).le.trans
        (caseA_commutator_X_Qy_le_Z hfr hl_false))
  have hZstab : caseAZ l ≤ CosetGeom.stab l :=
    (caseA_Z_le_Qy l).trans (caseA_Qy_le_stab l)
  haveI : Finite ↥(CosetGeom.stab l) := caseA_finite_stab L1 L2 S l
  haveI : Finite ↥(caseAZ l) :=
    Finite.of_injective (Subgroup.inclusion hZstab) (Subgroup.inclusion_injective hZstab)
  haveI : Finite ↥⁅caseAEvenN00 b x l, Subgroup.zpowers u⁆ :=
    Finite.of_injective (Subgroup.inclusion hcomm_le) (Subgroup.inclusion_injective hcomm_le)
  have hcard_lower : 2 ^ (2 * a + 1) ≤
      Nat.card ↥⁅caseAEvenN00 b x l, Subgroup.zpowers u⁆ := by
    rw [← hcommidx]
    exact evencb_relIndex_centralizer_le_card_commutator (caseAEvenN00 b x l) u
  have hZcard : Nat.card (caseAZ l) = 2 ^ (2 * a + 1) := caseA_card_Z_type1 hfr hl_false
  exact Subgroup.eq_of_le_of_card_ge hcomm_le (by rw [hZcard]; exact hcard_lower)

theorem caseA_even_Z_le_N
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) {l : f112Gamma L1 L2 S} (hl : l ∈ CosetGeom.nbrs (x 0)) (hl1 : l ≠ x 1) :
    caseAZ l ≤ caseAN (x (b - 1)) := by
  obtain ⟨u, hu, huQ⟩ := SetLike.not_le_iff_exists.mp
    (caseA_even_not_X_le_Qy_pred hfr hx hbe hb hl hl1)
  have hcomm := caseA_even_commutator_N00_eq hfr hA hx hbe hb hl hl1 hu huQ
  rw [← hcomm]
  have hN00N : caseAEvenN00 b x l ≤ caseAN (x (b - 1)) :=
    (show caseAEvenN00 b x l ≤ caseAEvenN0 b x from inf_le_left).trans
      ((show caseAEvenN0 b x ≤ caseAEvenN1 b x from inf_le_left).trans
        (show caseAEvenN1 b x ≤ caseAN (x (b - 1)) from inf_le_left))
  have hmemAS := caseA_even_mem_caseAS hfr hx hbe hb hl hu
  have huStab : u ∈ CosetGeom.stab (x (b - 1)) :=
    caseAS_le_stab_left (x (b - 1)) (x (b - 2)) hmemAS.1
  have hzuN : Subgroup.zpowers u ≤
      Subgroup.normalizer (caseAN (x (b - 1)) : Set (f112Amalgam L1 L2 S).Ghat) :=
    Subgroup.zpowers_le.mpr (caseA_stab_le_normalizer_N (x (b - 1)) huStab)
  refine Subgroup.commutator_le.mpr fun a ha n hn => ?_
  have haN : a ∈ caseAN (x (b - 1)) := hN00N ha
  have hnN : n ∈ Subgroup.normalizer (caseAN (x (b - 1)) : Set (f112Amalgam L1 L2 S).Ghat) :=
    hzuN hn
  have h1 : n * a⁻¹ * n⁻¹ ∈ caseAN (x (b - 1)) :=
    (Subgroup.mem_normalizer_iff.mp hnN a⁻¹).mp (Subgroup.inv_mem _ haN)
  change a * n * a⁻¹ * n⁻¹ ∈ caseAN (x (b - 1))
  have he : a * n * a⁻¹ * n⁻¹ = a * (n * a⁻¹ * n⁻¹) := by group
  rw [he]
  exact Subgroup.mul_mem _ haN h1

theorem caseA_even_false
    {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (hA : str83R L1 L2 S ≤ Q1 L1 L2 S) {b : ℕ}
    {x : GPath (f112Amalgam L1 L2 S).graphHat b} (hx : caseACritPath L1 L2 S b x) (hbe : Even b)
    (hb : 5 ≤ b) :
    False := by
  obtain ⟨l, hl, -, hl1⟩ := caseA_exists_nbr_ne hfr hx.type_two (x 0) (x 1)
  have hl_false : CosetGeom.vtype l = false :=
    CosetGeom.vtype_eq_false_of_adj (by simpa [CosetGeom.nbrs] using hl) hx.type_two
  have hα : CosetGeom.vtype (x (b - 1)) = false :=
    (hx.vtype_eq_false_iff_odd (i := b - 1) (by omega)).mpr
      (Nat.not_even_iff_odd.mp (evencb_not_even_sub_one (by omega) hbe))
  have hZlN : caseAZ l ≤ caseAN (x (b - 1)) := caseA_even_Z_le_N hfr hA hx hbe hb hl hl1
  have hAdj0 : (f112Amalgam L1 L2 S).graphHat.Adj (x 0) l := by
    simpa [CosetGeom.nbrs] using hl
  have hZlZ0 : caseAZ l ≤ caseAZ (x 0) := caseA_Z_le_Z_of_adj hfr hl_false hAdj0.symm
  have hNY : caseAN (x (b - 1)) ≤ caseAY (x (b - 1)) := caseA_N_le_Y hfr hA hα
  have hNC : caseAN (x (b - 1)) ≤
      Subgroup.centralizer (caseAX (x (b - 1)) : Set (f112Amalgam L1 L2 S).Ghat) :=
    hNY.trans (evencb_caseAY_le_centralizer (x (b - 1)))
  have hZbX : caseAZ (x b) ≤ caseAX (x (b - 1)) := by
    unfold caseAX
    refine le_iSup₂ (f := fun w (_ : w ∈ CosetGeom.nbrs (x (b - 1))) => caseAZ w) (x b) ?_
    have hb1 : (b - 1) + 1 = b := by omega
    simpa [CosetGeom.nbrs, hb1] using x.adj (b - 1) (by omega)
  have hZlC : caseAZ l ≤
      Subgroup.centralizer (caseAZ (x b) : Set (f112Amalgam L1 L2 S).Ghat) :=
    hZlN.trans (hNC.trans (Subgroup.centralizer_le hZbX))
  have hZlZ1 : caseAZ l ≤ caseAZ (x 1) :=
    (le_inf hZlZ0 hZlC).trans (caseA_even_centralizer_Z_le hfr hx hbe hb)
  have hinf : caseAZ l ⊓ caseAZ (x 1) = ⊥ :=
    caseA_Z_inf_Z_eq_bot hfr hx.type_two hl
      (by simpa [CosetGeom.nbrs] using x.adj 0 (by omega)) hl1
  have hle : caseAZ l ≤ caseAZ l ⊓ caseAZ (x 1) := le_inf le_rfl hZlZ1
  rw [hinf] at hle
  exact caseA_Z_ne_bot hfr l (le_bot_iff.mp hle)

end CFSG.Quasithin.Stroth

end
