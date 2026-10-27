module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34C3b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

omit [Finite G] in
theorem bl12_stab_le_normalizer_Cb (δ : Geo H M) :
    stab δ ≤ Subgroup.normalizer (Cb δ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hg) x
  have h2 := Subgroup.mem_normalizer_iff.mp
    (normalizer_le_normalizer_centralizer _ (le_normalizer_oTwoRes _ hg)) x
  constructor
  · intro hx
    exact ⟨h1.mp hx.1, h2.mp hx.2⟩
  · intro hx
    exact ⟨h1.mpr hx.1, h2.mpr hx.2⟩

omit [Finite G] in
theorem relIndex_sup_le_of_comm {A C Z : Subgroup G} (hA : IsMulCommutative A) (hC : C ≤ A)
    (hZ : Z ≤ A) : C.relIndex (Z ⊔ C) ≤ (Z ⊓ C).relIndex Z := by
  have := normal_subgroupOf_of_comm hA C
  have h1 := Subgroup.relIndex_sup_right (H := Z.subgroupOf A) (K := C.subgroupOf A)
  rw [← Subgroup.subgroupOf_sup hZ hC, Subgroup.relIndex_subgroupOf (sup_le hZ hC),
    Subgroup.relIndex_subgroupOf hZ] at h1
  rw [h1, inf_comm, Subgroup.inf_relIndex_right]

omit [Finite G] in
theorem comm_mem_sup_of_comm {A P Q Z : Subgroup G} {y : G} (hA : IsMulCommutative A)
    (hP : P ≤ A) (hQ : Q ≤ A) (hZ : Z ≤ A) (hP' : ∀ a ∈ P, y * a * y⁻¹ * a⁻¹ ∈ Z)
    (hQ' : ∀ a ∈ Q, y * a * y⁻¹ * a⁻¹ ∈ Z) :
    ∀ a ∈ P ⊔ Q, y * a * y⁻¹ * a⁻¹ ∈ Z := by
  have hcomm : ∀ x ∈ A, ∀ w ∈ Z, x * w = w * x := fun x hx w hw =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : A) ⟨w, hZ hw⟩)
  intro a ha
  rw [Subgroup.sup_eq_closure] at ha
  have key : a ∈ A ∧ y * a * y⁻¹ * a⁻¹ ∈ Z := by
    refine Subgroup.closure_induction (p := fun a _ => a ∈ A ∧ y * a * y⁻¹ * a⁻¹ ∈ Z) ?_ ?_ ?_ ?_ ha
    · rintro x (hx | hx)
      · exact ⟨hP hx, hP' x hx⟩
      · exact ⟨hQ hx, hQ' x hx⟩
    · exact ⟨A.one_mem, by simp⟩
    · rintro x x' - - ⟨hxA, hx⟩ ⟨hx'A, hx'⟩
      refine ⟨A.mul_mem hxA hx'A, ?_⟩
      have e : y * (x * x') * y⁻¹ * (x * x')⁻¹ =
          (y * x * y⁻¹ * x⁻¹) * (x * (y * x' * y⁻¹ * x'⁻¹) * x⁻¹) := by group
      rw [e, hcomm x hxA _ hx', mul_inv_cancel_right]
      exact Z.mul_mem hx hx'
    · rintro x - ⟨hxA, hx⟩
      refine ⟨A.inv_mem hxA, ?_⟩
      have e : y * x⁻¹ * y⁻¹ * x⁻¹⁻¹ = x⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ * x := by group
      rw [e, hcomm x⁻¹ (A.inv_mem hxA) _ (Z.inv_mem hx), inv_mul_cancel_right]
      exact Z.inv_mem hx
  exact key.2

omit [Finite G] in
theorem bl12_Zv_le_Vn_of_nbr {δ μ : Geo H M} (hμ : μ ∈ nbrs δ) : Zv μ ≤ Vn δ :=
  le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs δ) => Zv ν) μ hμ le_rfl

theorem bad_block (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ')
    {μ ν : Geo H M} (hμ : μ ∈ nbrs δ) (hν : ν ∈ nbrs δ) (hb : SameBlock δ μ ν)
    (hbad : ¬ Zv μ ≤ Qv δ') : ¬ Zv ν ≤ Qv δ' := by
  intro hgood
  obtain ⟨-, hB, -⟩ := case3_data hG hirr h15 hng hp
  obtain ⟨hZ'A, -, -, -⟩ := c3_comm_eq hG hirr h15 hng hp
  obtain ⟨hidx, -⟩ := c3_idx_two hG hirr h15 hng hp
  obtain ⟨-, hE⟩ := c3_E_le_two hG hirr h15 hng hp
  have hfix : Zv μ ⊔ Cb δ = Zv ν ⊔ Cb δ :=
    (c3_fix_eq hG hirr h15 hng hp hμ).symm.trans
      ((c3_fix_block hG hirr h15 hng hp hμ hν hb).trans (c3_fix_eq hG hirr h15 hng hp hν))
  have hνA₀ : Zv ν ≤ Vn δ ⊓ Qv δ' := le_inf (bl12_Zv_le_Vn_of_nbr hν) hgood
  have hC : ¬ Cb δ ≤ Vn δ ⊓ Qv δ' := fun hC =>
    hbad ((le_sup_left.trans hfix.le).trans (sup_le hνA₀ hC) |>.trans inf_le_right)
  have hsup : (Vn δ ⊓ Qv δ') ⊔ Cb δ = Vn δ := by
    have hle : (Vn δ ⊓ Qv δ') ⊔ Cb δ ≤ Vn δ := sup_le inf_le_left (Cb_le_Vn δ)
    have hmul := Subgroup.relIndex_mul_relIndex (Vn δ ⊓ Qv δ') ((Vn δ ⊓ Qv δ') ⊔ Cb δ) (Vn δ)
      le_sup_left hle
    rw [hidx] at hmul
    have h1 : ((Vn δ ⊓ Qv δ').relIndex ((Vn δ ⊓ Qv δ') ⊔ Cb δ)) ≠ 1 := fun h =>
      hC (le_sup_right.trans (Subgroup.relIndex_eq_one.mp h))
    have h0 : ((Vn δ ⊓ Qv δ').relIndex ((Vn δ ⊓ Qv δ') ⊔ Cb δ)) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have h2 : (((Vn δ ⊓ Qv δ') ⊔ Cb δ).relIndex (Vn δ)) = 1 := by
      have h3 : (((Vn δ ⊓ Qv δ') ⊔ Cb δ).relIndex (Vn δ)) ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      generalize (Vn δ ⊓ Qv δ').relIndex ((Vn δ ⊓ Qv δ') ⊔ Cb δ) = a at *
      generalize (((Vn δ ⊓ Qv δ') ⊔ Cb δ).relIndex (Vn δ)) = b at *
      by_contra h4
      have : 2 ≤ a := by omega
      have : 2 ≤ b := by omega
      nlinarith
    exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h2)
  obtain ⟨y, hyB, hyQ⟩ := IsConcreteLE.not_le_iff_exists.mp hB
  have hys : y ∈ stab δ := (pd_Vn_le_stab hG hp).2 hyB
  have hAc := isElemAbelian_Vn' hG δ
  have hZle : Zv δ' ⊔ Cb δ ≤ Vn δ := sup_le hZ'A (Cb_le_Vn δ)
  have hyC := bl12_stab_le_normalizer_Cb δ hys
  have h := secIdx_le_of_comm (V := Vn δ) (C := Cb δ) (A₀ := Vn δ) (Z := Zv δ' ⊔ Cb δ)
    (y := y) hAc (stab_le_normalizer_Vn δ hys) hyC (Cb_le_Vn δ) le_rfl hZle (fun a ha => by
      rw [← hsup] at ha
      refine comm_mem_sup_of_comm hAc.1 inf_le_left (Cb_le_Vn δ) hZle (fun a ha => ?_)
        (fun c hc => ?_) a ha
      · exact le_sup_left (a := Zv δ') (b := Cb δ) <|
          comm_Vn_Qv_le hG hp.vδ' (Subgroup.commutator_mem_commutator hyB ha.2)
      · refine le_sup_right (a := Zv δ') (b := Cb δ) ?_
        have h1 := (Subgroup.mem_normalizer_iff.mp hyC c).mp hc
        have e : y * c * y⁻¹ * c⁻¹ = (y * c * y⁻¹) * c⁻¹ := rfl
        rw [e]
        exact (Cb δ).mul_mem h1 ((Cb δ).inv_mem hc))
  have hr : rk δ y ≤ 2 := by
    unfold rk
    refine h.trans ?_
    rw [Subgroup.relIndex_self, one_mul, inf_eq_right.mpr le_sup_right]
    refine (relIndex_sup_le_of_comm hAc.1 (Cb_le_Vn δ) hZ'A).trans (le_trans ?_ hE)
    have hle : Zv δ ⊓ Zv δ' ≤ Zv δ' ⊓ Cb δ :=
      le_inf inf_le_right (inf_le_left.trans (Zv_le_Cb hG hp.vδ))
    exact Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
  have h4 := NG.four_le_rk hG h15 hng hp.vδ hys hyQ
  omega

theorem bad_not_fixed (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ')
    {μ : Geo H M} (hμ : μ ∈ nbrs δ) (hbad : ¬ Zv μ ≤ Qv δ') : ¬ Vn δ' ≤ stab μ := by
  intro hfix
  obtain ⟨-, hZB, -, -⟩ := c3_comm_eq hG hirr h15 hng hp
  obtain ⟨hE, -⟩ := c3_E_le_two hG hirr h15 hng hp
  obtain ⟨z, hzμ, hzQ⟩ := IsConcreteLE.not_le_iff_exists.mp hbad
  have hzs : z ∈ stab δ' := (pd_Vn_le_stab hG hp).1 (bl12_Zv_le_Vn_of_nbr hμ hzμ)
  have hBc := isElemAbelian_Vn' hG δ'
  have h := secIdx_le_of_comm (V := Vn δ') (C := Cb δ') (A₀ := Vn δ') (Z := Zv δ)
    (y := z) hBc (stab_le_normalizer_Vn δ' hzs) (bl12_stab_le_normalizer_Cb δ' hzs)
    (Cb_le_Vn δ') le_rfl hZB (fun a ha => by
      have hag : a ∈ stab μ ⊓ stab δ := ⟨hfix ha, (pd_Vn_le_stab hG hp).2 ha⟩
      have hc : z * a * z⁻¹ * a⁻¹ ∈ ⁅Zv μ, Subgroup.zpowers a⁆ :=
        Subgroup.commutator_mem_commutator hzμ (Subgroup.mem_zpowers a)
      by_cases haQ : a ∈ Qv μ
      · rw [(aon_edge hG hp.vδ hμ hag).1 haQ] at hc
        rw [Subgroup.mem_bot.mp hc]
        exact (Zv δ).one_mem
      · rw [(aon_edge hG hp.vδ hμ hag).2 haQ] at hc
        exact hc)
  have hr : rk δ' z ≤ 2 := by
    unfold rk
    refine h.trans ?_
    rw [Subgroup.relIndex_self, one_mul]
    refine le_trans ?_ hE
    have hle : Zv δ ⊓ Zv δ' ≤ Zv δ ⊓ Cb δ' :=
      inf_le_inf_left _ (Zv_le_Cb hG hp.vδ')
    exact Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
  have h4 := NG.four_le_rk hG h15 hng hp.vδ' hzs hzQ
  omega

end S34

end F53.Stellmacher

end CFSG.Quasithin
