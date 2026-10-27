module

public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeCore
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

theorem mul_mul_eq_of_orderOf_mul {G : Type*} [Group G] {d e : G} (hd : d * d = 1)
    (he : e * e = 1) (h3 : orderOf (d * e) = 3) : d * e * d = e * d * e := by
  have hd' : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hc : (d * e) ^ 3 = 1 := by
    rw [← h3]
    exact pow_orderOf_eq_one _
  have h : d * e * d * (e * d * e) = 1 := by
    rw [← hc, pow_three]
    group
  calc d * e * d = (e * d * e)⁻¹ := eq_inv_of_mul_eq_one_left h
    _ = e⁻¹ * d⁻¹ * e⁻¹ := by group
    _ = e * d * e := by rw [hd', he']

theorem eq_of_mul_mul_self {G : Type*} [Group G] {d e : G} (hd : d * d = 1)
    (h : d * e * d = d) : e = d := by
  calc e = d⁻¹ * (d * e * d) * d⁻¹ := by group
    _ = d⁻¹ * d * d⁻¹ := by rw [h]
    _ = d⁻¹ := by group
    _ = d := inv_eq_of_mul_eq_one_right hd

@[expose] def cvPerm :
    Shat →* Equiv.Perm CVert where
  toFun y :=
    { toFun := fun x => cvMul x y⁻¹
      invFun := fun x => cvMul x y
      left_inv := fun x => cvMul_inv_cancel' x y
      right_inv := fun x => cvMul_inv_cancel x y }
  map_one' := Equiv.ext fun x => by
    show cvMul x 1⁻¹ = x
    rw [inv_one, cvMul_one]
  map_mul' y z := Equiv.ext fun x => by
    show cvMul x (y * z)⁻¹ = cvMul (cvMul x z⁻¹) y⁻¹
    rw [mul_inv_rev, cvMul_mul]

theorem cvPerm_apply
    (y : Shat) (x : CVert) : cvPerm y x = cvMul x y⁻¹ := rfl

theorem sphereThree_cvMul
    {v w : CVert} (hw : w ∈ sphereThree v) (s : Shat) :
    cvMul w s ∈ sphereThree (cvMul v s) :=
  ⟨dist_eq_two_cvMul hw.1 s, (labelThree_cvMul v w s).2 hw.2⟩

theorem mem_sphereThree_comm
    {v w : CVert} : w ∈ sphereThree v ↔ v ∈ sphereThree w := by
  have h : ∀ a b : CVert, LabelThree a b → LabelThree b a := fun a b h => by
    have e : orderOf (clabel b * clabel a) = orderOf (clabel a * clabel b) := by
      have e1 : clabel b * clabel a = MulAut.conj (clabel a)⁻¹ (clabel a * clabel b) := by
        rw [MulAut.conj_apply, inv_inv]
        group
      rw [e1, MulEquiv.orderOf_eq]
    show orderOf (clabel b * clabel a) = 3 ∨ orderOf (clabel b * clabel a) = 6
    rw [e]
    exact h
  exact ⟨fun hw => ⟨SimpleGraph.dist_comm.trans hw.1, h v w hw.2⟩,
    fun hv => ⟨SimpleGraph.dist_comm.trans hv.1, h w v hv.2⟩⟩

section Triple

variable (H : ∀ x : CVert, LocalHom x)
include H

theorem clabel_mul_self (v : CVert) : clabel v * clabel v = 1 := by
  rw [← sq, ← (H v).orderOf_clabel, pow_orderOf_eq_one]

theorem clabelS_mul_self (v : CVert) : clabelS v * clabelS v = 1 :=
  Subtype.ext (clabel_mul_self H v)

theorem orderOf_clabel_mul_eq_three
    {v w : CVert} (hw : w ∈ sphereThree v) :
    orderOf (clabel v * clabel w) = 3 := by
  obtain ⟨hvw, hna, u, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 hw.1
  have hu : u ∈ cgraph.commonNeighbors v w := ⟨hvu, huw.symm⟩
  have hcube : ∀ x ∈ cgraph.commonNeighbors v w,
      (clabel v * clabel w) ^ 3 ∈ Subgroup.zpowers (clabel x) := by
    intro x hx
    have hvx : v ∈ cgraph.neighborSet x := ((cgraph.mem_commonNeighbors).1 hx).1.symm
    have hwx : w ∈ cgraph.neighborSet x := ((cgraph.mem_commonNeighbors).1 hx).2.symm
    have hne : (⟨v, hvx⟩ : cgraph.neighborSet x) ≠ ⟨w, hwx⟩ := fun h =>
      hvw (congrArg Subtype.val h)
    have h3 := orderOf_pt_mul_pt_eq_three H hne hna hw.2
    have hy : (H x).rho ((⟨clabelS v, clabelS_mem_stab H hvx⟩ *
        ⟨clabelS w, clabelS_mem_stab H hwx⟩) ^ 3) = 1 := by
      rw [map_pow, map_mul, rho_clabelS H hvx, rho_clabelS H hwx, ← h3, pow_orderOf_eq_one]
    exact (H x).mem_zpowers_of_rho_eq_one hy
  rcases hw.2 with h | h
  · exact h
  · exfalso
    have hne1 : (clabel v * clabel w) ^ 3 ≠ 1 :=
      pow_ne_one_of_lt_orderOf (by decide)
        (by rw [show orderOf (clabel v * clabel w) = 6 from h]; decide)
    obtain ⟨u', hu', hne, -⟩ := exists_commonNeighbor_adj H hvw hna hw.2 hu
    have e1 := (eq_one_or_eq_of_mem_zpowers_of_orderOf (H u).orderOf_clabel
      (hcube u hu)).resolve_left hne1
    have e2 := (eq_one_or_eq_of_mem_zpowers_of_orderOf (H u').orderOf_clabel
      (hcube u' hu')).resolve_left hne1
    exact hne (clabel_injOn_neighborSet v hu'.1 hu.1 (e2.symm.trans e1))

theorem order_three_triple
    {v w : CVert} (hw : w ∈ sphereThree v) :
    ∃ r : CVert, r = cvMul w (clabelS v) ∧ r = cvMul v (clabelS w) ∧ r ≠ v ∧ r ≠ w ∧
      cvMul v (clabelS v) = v ∧ cvMul r (clabelS v) = w ∧
      cvMul w (clabelS w) = w ∧ cvMul r (clabelS w) = v ∧
      clabel r = clabel v * clabel w * clabel v ∧ clabel r = clabel w * clabel v * clabel w := by
  obtain ⟨-, -, u, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 hw.1
  have hvx : v ∈ cgraph.neighborSet u := hvu.symm
  have hwx : w ∈ cgraph.neighborSet u := huw
  have h3 := orderOf_clabel_mul_eq_three H hw
  have hd := clabel_mul_self H v
  have he := clabel_mul_self H w
  have hbraid := mul_mul_eq_of_orderOf_mul hd he h3
  have hlab1 : clabel (cvMul w (clabelS v)) = clabel v * clabel w * clabel v := by
    rw [clabel_cvMul, coe_clabelS, inv_eq_of_mul_eq_one_right hd]
  have hlab2 : clabel (cvMul v (clabelS w)) = clabel w * clabel v * clabel w := by
    rw [clabel_cvMul, coe_clabelS, inv_eq_of_mul_eq_one_right he]
  have hwdu : cvMul w (clabelS v) ∈ cgraph.neighborSet u :=
    (H u).cvMul_mem ⟨clabelS v, clabelS_mem_stab H hvx⟩ hwx
  have hveu : cvMul v (clabelS w) ∈ cgraph.neighborSet u :=
    (H u).cvMul_mem ⟨clabelS w, clabelS_mem_stab H hwx⟩ hvx
  have hr : cvMul w (clabelS v) = cvMul v (clabelS w) :=
    clabel_injOn_neighborSet u hwdu hveu (by rw [hlab1, hlab2, hbraid])
  refine ⟨_, rfl, hr, fun h => ?_, fun h => ?_, cvMul_clabelS_self H v, ?_,
    cvMul_clabelS_self H w, ?_, hlab1, hlab1.trans hbraid⟩
  · have e : clabel v * clabel w * clabel v = clabel v := by rw [← hlab1, h]
    have e2 : orderOf (clabel v * clabel w) = 1 := by
      rw [eq_of_mul_mul_self hd e, hd, orderOf_one]
    rw [h3] at e2
    exact absurd e2 (by decide)
  · have e : clabel w * clabel v * clabel w = clabel w := by rw [← hlab2, ← hr, h]
    have e2 : orderOf (clabel v * clabel w) = 1 := by
      rw [eq_of_mul_mul_self he e, he, orderOf_one]
    rw [h3] at e2
    exact absurd e2 (by decide)
  · rw [← cvMul_mul, clabelS_mul_self H v, cvMul_one]
  · rw [hr, ← cvMul_mul, clabelS_mul_self H w, cvMul_one]

theorem commonNeighbors_cvMul_clabelS (v w : CVert) :
    cgraph.commonNeighbors v (cvMul w (clabelS v)) = cgraph.commonNeighbors v w := by
  have h := commonNeighbors_cvMul v w (clabelS v)
  rw [cvMul_clabelS_self H v] at h
  rw [h]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show cvMul y (clabelS v) ∈ cgraph.commonNeighbors v w
    rw [cvMul_clabelS_of_mem H hy.1]
    exact hy
  · intro hx
    exact ⟨x, hx, cvMul_clabelS_of_mem H hx.1⟩

theorem commonNeighbors_cvMul_clabelS' (v w : CVert) :
    cgraph.commonNeighbors (cvMul v (clabelS w)) w = cgraph.commonNeighbors v w := by
  have h := commonNeighbors_cvMul v w (clabelS w)
  rw [cvMul_clabelS_self H w] at h
  rw [h]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show cvMul y (clabelS w) ∈ cgraph.commonNeighbors v w
    rw [cvMul_clabelS_of_mem H hy.2]
    exact hy
  · intro hx
    exact ⟨x, hx, cvMul_clabelS_of_mem H hx.2⟩

theorem closure_clabelS_fix (v w : CVert) :
    ∀ y ∈ Subgroup.closure ({clabelS v, clabelS w} : Set Shat),
      ∀ x ∈ cgraph.commonNeighbors v w, cvMul x y = x := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl
    · exact fun x hx => cvMul_clabelS_of_mem H hx.1
    · exact fun x hx => cvMul_clabelS_of_mem H hx.2
  | one => exact fun x _ => cvMul_one x
  | mul y z _ _ hy hz => exact fun x hx => by rw [cvMul_mul, hy x hx, hz x hx]
  | inv y _ hy =>
    intro x hx
    calc cvMul x y⁻¹ = cvMul (cvMul x y) y⁻¹ := by rw [hy x hx]
      _ = x := cvMul_inv_cancel x y

theorem exists_closure_equiv_perm
    {v w : CVert} (hw : w ∈ sphereThree v) {r : CVert}
    (hrd : r = cvMul w (clabelS v)) (hre : r = cvMul v (clabelS w)) (hrv : r ≠ v)
    (hrw : r ≠ w) :
    ∃ π : Subgroup.closure ({clabelS v, clabelS w} : Set Shat) ≃*
        Equiv.Perm ({v, w, r} : Set CVert),
      ∀ y x, ((π y x : ({v, w, r} : Set CVert)) : CVert) = cvMul x (y : Shat)⁻¹ := by
  classical
  obtain ⟨hvw, hna, u, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 hw.1
  have hC : (cgraph.commonNeighbors v w).Nonempty := ⟨u, hvu, huw.symm⟩
  have hfaith := (order_three_common H hvw hna hw.2 hC).2
  set D : Set Shat := {clabelS v, clabelS w} with hD
  set T3 : Set CVert := {v, w, r} with hT3
  have hsq : ∀ s ∈ D, s * s = 1 := by
    rintro s (rfl | rfl)
    · exact clabelS_mul_self H v
    · exact clabelS_mul_self H w
  have hinv : ∀ s ∈ D, s⁻¹ = s := fun s hs => inv_eq_of_mul_eq_one_right (hsq s hs)
  have hrdd : cvMul r (clabelS v) = w := by
    rw [hrd, ← cvMul_mul, clabelS_mul_self H v, cvMul_one]
  have hree : cvMul r (clabelS w) = v := by
    rw [hre, ← cvMul_mul, clabelS_mul_self H w, cvMul_one]
  have hgen : ∀ s ∈ D, ∀ x ∈ T3, cvMul x s ∈ T3 := by
    rintro s (rfl | rfl) x (hx | hx | hx) <;> rw [hx]
    · rw [cvMul_clabelS_self H v]
      exact Or.inl rfl
    · rw [← hrd]
      exact Or.inr (Or.inr rfl)
    · rw [hrdd]
      exact Or.inr (Or.inl rfl)
    · rw [← hre]
      exact Or.inr (Or.inr rfl)
    · rw [cvMul_clabelS_self H w]
      exact Or.inr (Or.inl rfl)
    · rw [hree]
      exact Or.inl rfl
  let K : Subgroup Shat :=
    { carrier := {y | ∀ x, cvPerm y x ∈ T3 ↔ x ∈ T3}
      mul_mem' := fun {y z} hy hz x => by
        rw [map_mul, Equiv.Perm.mul_apply]
        exact (hy _).trans (hz x)
      one_mem' := fun x => by rw [map_one, Equiv.Perm.one_apply]
      inv_mem' := fun {y} hy x => by
        have h := hy (cvPerm y⁻¹ x)
        rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Equiv.Perm.one_apply] at h
        exact h.symm }
  have hDK : Subgroup.closure D ≤ K := by
    rw [Subgroup.closure_le]
    intro s hs x
    rw [cvPerm_apply, hinv s hs]
    refine ⟨fun h => ?_, hgen s hs x⟩
    have h2 := hgen s hs _ h
    rwa [← cvMul_mul, hsq s hs, cvMul_one] at h2
  let π : Subgroup.closure D →* Equiv.Perm T3 :=
    { toFun := fun y => (cvPerm y).subtypePerm (hDK y.2)
      map_one' := Equiv.ext fun x => Subtype.ext (by
        show cvPerm 1 x = x
        rw [map_one, Equiv.Perm.one_apply])
      map_mul' := fun y z => Equiv.ext fun x => Subtype.ext (by
        show cvPerm ((y : Shat) * z) x = cvPerm y (cvPerm z x)
        rw [map_mul, Equiv.Perm.mul_apply]) }
  have hπ : ∀ y x, ((π y x : T3) : CVert) = cvMul x (y : Shat)⁻¹ := fun _ _ => rfl
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hfix : ∀ x ∈ T3, cvMul x (y : Shat)⁻¹ = x := fun x hx =>
      congrArg (fun σ : Equiv.Perm T3 => ((σ ⟨x, hx⟩ : T3) : CVert)) hy
    have h1 : ((y : Shat))⁻¹ = 1 := hfaith _ (hfix v (Or.inl rfl)) (hfix w (Or.inr (Or.inl rfl)))
      (closure_clabelS_fix H v w _ (Subgroup.inv_mem _ y.2))
    exact Subtype.ext (inv_eq_one.1 h1)
  have hT3card : Nat.card T3 = 3 := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_three]
    exact ⟨v, w, r, hvw, hrv.symm, hrw.symm, rfl⟩
  have hle : Nat.card (Subgroup.closure D) ≤ 6 := by
    have h := Nat.card_le_card_of_injective π hπinj
    rwa [Nat.card_perm, hT3card] at h
  have hdvd : 6 ∣ Nat.card (Subgroup.closure D) := by
    have h2 : orderOf (⟨clabelS v, Subgroup.subset_closure (Or.inl rfl)⟩ :
        Subgroup.closure D) = 2 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact (H v).orderOf_clabel
    have h3 : orderOf ((⟨clabelS v, Subgroup.subset_closure (Or.inl rfl)⟩ :
        Subgroup.closure D) * ⟨clabelS w, Subgroup.subset_closure (Or.inr rfl)⟩) = 3 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact orderOf_clabel_mul_eq_three H hw
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) (h2 ▸ orderOf_dvd_natCard _)
      (h3 ▸ orderOf_dvd_natCard _)
  have hcard : Nat.card (Subgroup.closure D) = 6 :=
    le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  have hbij : Function.Bijective π := hπinj.bijective_of_nat_card_le (by
    rw [Nat.card_perm, hT3card, hcard]
    decide)
  exact ⟨MulEquiv.ofBijective π hbij, hπ⟩

theorem sphereThree_pairing
    {v w : CVert} (hw : w ∈ sphereThree v) :
    cvMul w (clabelS v) ∈ sphereThree v ∧ cvMul w (clabelS v) ≠ w ∧
      cvMul (cvMul w (clabelS v)) (clabelS v) = w := by
  obtain ⟨_, rfl, -, -, hrw, -, hrd, -⟩ := order_three_triple H hw
  refine ⟨?_, hrw, hrd⟩
  have h := sphereThree_cvMul hw (clabelS v)
  rwa [cvMul_clabelS_self H v] at h

theorem even_ncard_sphereThree
    (v : CVert) : Even (sphereThree v).ncard := by
  classical
  have : Fintype (sphereThree v) := Fintype.ofFinite _
  let σ : Equiv.Perm (sphereThree v) :=
    { toFun := fun w => ⟨cvMul w (clabelS v), (sphereThree_pairing H w.2).1⟩
      invFun := fun w => ⟨cvMul w (clabelS v), (sphereThree_pairing H w.2).1⟩
      left_inv := fun w => Subtype.ext (sphereThree_pairing H w.2).2.2
      right_inv := fun w => Subtype.ext (sphereThree_pairing H w.2).2.2 }
  have hσ2 : σ ^ 2 = 1 := by
    ext w
    rw [sq, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact (sphereThree_pairing H w.2).2.2
  have hsupp : σ.support = Finset.univ := Finset.eq_univ_iff_forall.2 fun w =>
    Equiv.Perm.mem_support.2 fun h => (sphereThree_pairing H w.2).2.1 (congrArg Subtype.val h)
  have h2 := Equiv.Perm.two_dvd_card_support hσ2
  rw [hsupp, Finset.card_univ, Set.fintypeCard_eq_ncard] at h2
  exact even_iff_two_dvd.2 h2

end Triple

end CFSG.Monster.B.TwoA.Amalgam
