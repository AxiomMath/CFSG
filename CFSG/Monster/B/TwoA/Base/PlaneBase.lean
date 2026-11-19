
module

public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.Co2.Simple
public import CFSG.Monster.B.TwoA.Base.TwoPair

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert

private theorem zmod2_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

def sW :
    Wv v0 := pairW 2 3 offPair23 0

def Uplane :
    Submodule (ZMod 2) (Wv v0) := Submodule.span (ZMod 2) {wFr, sW}

theorem sW_ne_zero :
    sW ≠ 0 := pairW_ne_zero offPair23 0

theorem sW_ne_wFr :
    sW ≠ wFr := pairW_ne_wFr offPair23 0

theorem two_smul_W
    (x : Wv v0) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

theorem add_eq_zero_iff_W
    {x y : Wv v0} : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· + y) h
    simpa [add_assoc, two_smul_W] using this
  · rintro rfl
    exact two_smul_W x

theorem mem_Uplane_iff
    (x : Wv v0) :
    x ∈ Uplane ↔ x = 0 ∨ x = wFr ∨ x = sW ∨ x = wFr + sW := by
  rw [Uplane, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem wFr_mem_Uplane :
    wFr ∈ Uplane := (mem_Uplane_iff _).2 (.inr (.inl rfl))

theorem sW_mem_Uplane :
    sW ∈ Uplane := (mem_Uplane_iff _).2 (.inr (.inr (.inl rfl)))

theorem linearIndependent_wFr_sW :
    LinearIndependent (ZMod 2) ![wFr, sW] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp at h; exact absurd h sW_ne_zero
  · simp at h; exact absurd h wFr_ne_zero
  · simp only [one_smul] at h
    exact absurd (add_eq_zero_iff_W.1 h).symm sW_ne_wFr

theorem range_wFr_sW :
    Set.range ![wFr, sW] = {wFr, sW} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union]

theorem finrank_Uplane :
    Module.finrank (ZMod 2) Uplane = 2 := by
  have h := finrank_span_eq_card linearIndependent_wFr_sW
  rw [range_wFr_sW, Fintype.card_fin] at h
  exact h

def uBasis :
    Module.Basis (Fin 2) (ZMod 2) Uplane :=
  (Module.Basis.span linearIndependent_wFr_sW).map
    (LinearEquiv.ofEq _ _ (by rw [range_wFr_sW]; rfl))

def NU :
    Subgroup (Kstab v0) := wSetStab Uplane

def CU :
    Subgroup (Kstab v0) := wFix (Uplane : Set (Wv v0))

theorem mem_NU_of
    {k : Kstab v0} (hw : wAct v0 k wFr ∈ Uplane) (hs : wAct v0 k sW ∈ Uplane) :
    k ∈ NU := by
  intro x hx
  rcases (mem_Uplane_iff x).1 hx with rfl | rfl | rfl | rfl
  · rw [map_zero]; exact Uplane.zero_mem
  · exact hw
  · exact hs
  · rw [map_add]; exact Uplane.add_mem hw hs

theorem mem_CU_of
    {k : Kstab v0} (hw : wAct v0 k wFr = wFr) (hs : wAct v0 k sW = sW) :
    k ∈ CU := by
  rw [CU, mem_wFix]
  intro x hx
  rcases (mem_Uplane_iff x).1 hx with rfl | rfl | rfl | rfl
  · rw [map_zero]
  · exact hw
  · exact hs
  · rw [map_add, hw, hs]

theorem CU_le_NU :
    CU ≤ NU := fun _ hk x hx => by
  rw [(mem_wFix.1 hk) x hx]
  exact hx

theorem CU_le_Mfr :
    CU ≤ Mfr := fun _ hk => (mem_wFix.1 hk) wFr wFr_mem_Uplane

def Cboth : Submodule (ZMod 2) (Fin 24 → ZMod 2) := Ceq ⊓ coordEq 2 3

theorem mem_Cboth {x : Fin 24 → ZMod 2} : x ∈ Cboth ↔ x ∈ C ∧ x 0 = x 1 ∧ x 2 = x 3 := by
  rw [Cboth, Submodule.mem_inf, mem_Ceq, mem_coordEq, and_assoc]

theorem Ftwo_le_Ppair : Ftwo ≤ Ppair := inf_le_left

theorem ceqFtwoHyp : MonoHyp Ceq Ftwo :=
  ⟨ceqHyp.le_C, ceqHyp.Ω_mem, fun p hp => ceqHyp.preserves p (Ftwo_le_Ppair hp)⟩

theorem cbothFtwoHyp : MonoHyp Cboth Ftwo where
  le_C := fun x hx => (mem_Cboth.1 hx).1
  Ω_mem := mem_Cboth.2 ⟨Ω_mem_C, rfl, rfl⟩
  preserves p hp a ha := by
    rw [mem_Cboth] at ha ⊢
    refine ⟨permWord_mem_of_mem_AutPerm p.2 ha.1, ?_, ?_⟩
    · have h := ceqHyp.preserves p (Ftwo_le_Ppair hp) a (mem_Ceq.2 ⟨ha.1, ha.2.1⟩)
      exact (mem_Ceq.1 h).2
    · rw [permWord_apply', permWord_apply']
      have hp' := Ftwo.inv_mem hp
      rcases ((mem_Ftwo_iff p⁻¹).1 hp').2 with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · rw [← coe_inv_autPerm, h2, h3]; exact ha.2.2
      · rw [← coe_inv_autPerm, h2, h3]; exact ha.2.2.symm

theorem mk_mem_Kstab_of_Ftwo
    {a : C} (ha : (a : Fin 24 → ZMod 2) ∈ Ceq) {p : AutPerm}
    (hp : p ∈ Ftwo) : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 :=
  (mk_mem_Kstab_iff_monomial a p).2 ⟨Ftwo_le_Ppair hp, ha⟩

theorem wAct_monomial_sW
    {a : C} {p : AutPerm}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) :
    wAct v0 ⟨_, hk⟩ sW = pairW _ _ (offPair23.perm ((mk_mem_Kstab_iff_monomial a p).1 hk).1)
      ((a : Fin 24 → ZMod 2) 2 + (a : Fin 24 → ZMod 2) 3) := by
  rw [sW, wAct_monomial_pairW hk offPair23 0, zero_add]

theorem wFr_add_sW :
    wFr + sW = pairW 2 3 offPair23 1 := by
  rw [pairW_one, add_comm]
  rfl

theorem pairs_eq_iff_stab (p : AutPerm) :
    (((p : Equiv.Perm (Fin 24)) 2 = 2 ∧ (p : Equiv.Perm (Fin 24)) 3 = 3) ∨
      ((p : Equiv.Perm (Fin 24)) 2 = 3 ∧ (p : Equiv.Perm (Fin 24)) 3 = 2)) ↔
      p ∈ MulAction.stabilizer AutPerm pair23 :=
  (mem_stabilizer_pair23_iff p).symm

theorem add_eq_zero_iff_eq' : ∀ s t : ZMod 2, s + t = 0 ↔ s = t := by decide

theorem monomial_sW_mem_iff
    {a : C} {p : AutPerm}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) :
    wAct v0 ⟨_, hk⟩ sW ∈ Uplane ↔ p ∈ Ftwo := by
  have hp := ((mk_mem_Kstab_iff_monomial a p).1 hk).1
  rw [wAct_monomial_sW, mem_Uplane_iff, wFr_add_sW, Ftwo, Subgroup.mem_inf,
    ← pairs_eq_iff_stab]
  simp only [sW, pairW_eq_iff, pairW_ne_zero, pairW_ne_wFr, false_or]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact ⟨hp, h⟩
    · exact ⟨hp, h⟩
  · rintro ⟨-, h⟩
    rcases zmod2_cases ((a : Fin 24 → ZMod 2) 2 + (a : Fin 24 → ZMod 2) 3) with hc | hc
    · exact .inl ⟨h, hc⟩
    · exact .inr ⟨h, hc⟩

theorem monomial_sW_eq_iff
    {a : C} {p : AutPerm}
    (hk : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0) :
    wAct v0 ⟨_, hk⟩ sW = sW ↔ p ∈ Ftwo ∧ (a : Fin 24 → ZMod 2) 2 = (a : Fin 24 → ZMod 2) 3 := by
  have hp := ((mk_mem_Kstab_iff_monomial a p).1 hk).1
  rw [wAct_monomial_sW, sW, pairW_eq_iff, Ftwo, Subgroup.mem_inf, ← pairs_eq_iff_stab,
    add_eq_zero_iff_eq']
  exact ⟨fun h => ⟨⟨hp, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩

theorem mem_NUw_iff
    (k : Kstab v0) : k ∈ NU ⊓ Mfr ↔ (k : OLq) ∈ monoSub ceqFtwoHyp := by
  constructor
  · rintro ⟨hN, hM⟩
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff ceqHyp).1 ((mem_Mfr_iff k).1 hM)
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    have hs := hN sW sW_mem_Uplane
    rw [e, monomial_sW_mem_iff hk'] at hs
    rw [hk]
    exact mk_mem_monoSub ceqFtwoHyp ha hs
  · intro h
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff ceqFtwoHyp).1 h
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    have hM : k ∈ Mfr := (mem_Mfr_iff k).2 (hk ▸ mk_mem_monoSub ceqHyp ha (Ftwo_le_Ppair hp))
    refine ⟨mem_NU_of ?_ ?_, hM⟩
    · rw [show wAct v0 k wFr = wFr from hM]
      exact wFr_mem_Uplane
    · rw [e, monomial_sW_mem_iff hk']
      exact hp

theorem mem_CU_iff
    (k : Kstab v0) : k ∈ CU ↔ (k : OLq) ∈ monoSub cbothFtwoHyp := by
  constructor
  · intro hC
    have hM := CU_le_Mfr hC
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff ceqHyp).1 ((mem_Mfr_iff k).1 hM)
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    have hs := (mem_wFix.1 hC) sW sW_mem_Uplane
    rw [e, monomial_sW_eq_iff hk'] at hs
    rw [hk]
    exact mk_mem_monoSub cbothFtwoHyp (mem_Cboth.2 ⟨(mem_Ceq.1 ha).1, (mem_Ceq.1 ha).2, hs.2⟩)
      hs.1
  · intro h
    obtain ⟨a, ha, p, hp, hk⟩ := (mem_monoSub_iff cbothFtwoHyp).1 h
    have ha' : (a : Fin 24 → ZMod 2) ∈ Ceq := mem_Ceq.2 ⟨(mem_Cboth.1 ha).1, (mem_Cboth.1 ha).2.1⟩
    have hk' : (QuotientGroup.mk (gO a * PO p) : OLq) ∈ Kstab v0 := hk ▸ k.2
    have e : k = ⟨_, hk'⟩ := Subtype.ext hk
    have hM : k ∈ Mfr := (mem_Mfr_iff k).2 (hk ▸ mk_mem_monoSub ceqHyp ha' (Ftwo_le_Ppair hp))
    refine mem_CU_of hM ?_
    rw [e, monomial_sW_eq_iff hk']
    exact ⟨hp, (mem_Cboth.1 ha).2.2⟩

def cbothForm : Ceq →ₗ[ZMod 2] ZMod 2 :=
  ((LinearMap.proj 2 : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2) - LinearMap.proj 3).comp Ceq.subtype

theorem B07_mem_Ceq : B 0 + B 7 ∈ Ceq :=
  mem_Ceq.2 ⟨C.add_mem (B_mem_C 0) (B_mem_C 7), by decide⟩

theorem cbothForm_surjective : Function.Surjective cbothForm := by
  intro t
  refine ⟨t • ⟨B 0 + B 7, B07_mem_Ceq⟩, ?_⟩
  rw [map_smul]
  have h : cbothForm ⟨B 0 + B 7, B07_mem_Ceq⟩ = (B 0 + B 7) 2 - (B 0 + B 7) 3 := rfl
  rw [h, show (B 0 + B 7) 2 - (B 0 + B 7) 3 = 1 by decide, smul_eq_mul, mul_one]

theorem comap_Cboth : Cboth.comap Ceq.subtype = LinearMap.ker cbothForm := by
  ext c
  simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, cbothForm,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero, Cboth,
    Submodule.mem_inf, mem_coordEq]
  exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩

theorem finrank_Cboth : Module.finrank (ZMod 2) Cboth = 10 := by
  have h := LinearMap.finrank_range_add_finrank_ker cbothForm
  rw [LinearMap.range_eq_top.2 cbothForm_surjective, finrank_top, Module.finrank_self,
    finrank_Ceq, ← comap_Cboth] at h
  have e := (Submodule.comapSubtypeEquivOfLe (p := Cboth) (q := Ceq) inf_le_left).finrank_eq
  omega

def sgnC : C := ⟨B 0 + B 7, C.add_mem (B_mem_C 0) (B_mem_C 7)⟩

theorem sgnK_mem :
    (QuotientGroup.mk (gO sgnC * PO 1) : OLq) ∈ Kstab v0 :=
  (mk_mem_Kstab_iff_monomial _ _).2 ⟨Ppair.one_mem, B07_mem_Ceq⟩

def sgnK :
    Kstab v0 := ⟨_, sgnK_mem⟩

theorem sgnK_mem_Mfr :
    sgnK ∈ Mfr :=
  (mem_Mfr_iff sgnK).2 (mk_mem_monoSub (a := sgnC) (p := 1) ceqHyp B07_mem_Ceq Ppair.one_mem)

theorem sgnK_wFr :
    wAct v0 sgnK wFr = wFr := sgnK_mem_Mfr

theorem sgnK_sW :
    wAct v0 sgnK sW = wFr + sW := by
  rw [sgnK, wAct_monomial_sW sgnK_mem, wFr_add_sW]
  rfl

theorem sgnK_mem_NU :
    sgnK ∈ NU :=
  mem_NU_of (by rw [sgnK_wFr]; exact wFr_mem_Uplane)
    (by rw [sgnK_sW]; exact Uplane.add_mem wFr_mem_Uplane sW_mem_Uplane)

def resEnd
    (k : NU) : Module.End (ZMod 2) Uplane :=
  (wAct v0 ((k : Kstab v0)⁻¹)).restrict fun x hx => (NU.inv_mem k.2) x hx

theorem coe_resEnd
    (k : NU) (x : Uplane) :
    ((resEnd k x : Uplane) : Wv v0) = wAct v0 ((k : Kstab v0)⁻¹) x := rfl

theorem resEnd_mul
    (k k' : NU) : resEnd (k * k') = resEnd k * resEnd k' := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [coe_resEnd, Module.End.mul_apply, coe_resEnd, coe_resEnd, Subgroup.coe_mul, mul_inv_rev,
    wAct_mul, Module.End.mul_apply]

theorem resEnd_one :
    resEnd 1 = 1 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [coe_resEnd, Module.End.one_apply, OneMemClass.coe_one, inv_one, wAct_one,
    Module.End.one_apply]

def resEndHom :
    NU →* Module.End (ZMod 2) Uplane where
  toFun := resEnd
  map_one' := resEnd_one
  map_mul' := resEnd_mul

def resU :
    NU →* (Module.End (ZMod 2) Uplane)ˣ := resEndHom.toHomUnits

theorem coe_resU_apply
    (k : NU) (x : Uplane) :
    (((resU k : Module.End (ZMod 2) Uplane) x : Uplane) : Wv v0) =
      wAct v0 ((k : Kstab v0)⁻¹) x := rfl

theorem resU_eq_one_iff
    (k : NU) :
    resU k = 1 ↔ ∀ x ∈ Uplane, wAct v0 ((k : Kstab v0)⁻¹) x = x := by
  constructor
  · intro h x hx
    have := congrArg (fun u : (Module.End (ZMod 2) Uplane)ˣ =>
      (((u : Module.End (ZMod 2) Uplane) ⟨x, hx⟩ : Uplane) : Wv v0)) h
    exact this
  · intro h
    refine Units.ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact h x x.2

theorem fix_inv_iff (k : Kstab v0) (x : Wv v0) : wAct v0 k⁻¹ x = x ↔ wAct v0 k x = x := by
  constructor
  · intro h
    conv_lhs => rw [← h]
    exact wAct_apply_inv k x
  · intro h
    conv_lhs => rw [← h]
    exact wAct_inv_apply k x

theorem ker_resU :
    resU.ker = CU.subgroupOf NU := by
  ext k
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, resU_eq_one_iff]
  constructor
  · intro h
    exact mem_wFix.2 fun x hx => (fix_inv_iff _ x).1 (h x hx)
  · intro h x hx
    exact (fix_inv_iff _ x).2 (mem_wFix.1 h x hx)

def glUEquiv :
    (Module.End (ZMod 2) Uplane)ˣ ≃* GL (Fin 2) (ZMod 2) :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv uBasis).toMulEquiv

theorem natCard_GL2 : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two]
  rfl

theorem natCard_glU :
    Nat.card (Module.End (ZMod 2) Uplane)ˣ = 6 := by
  rw [Nat.card_congr glUEquiv.toEquiv, natCard_GL2]

theorem coe_resU_inv_apply
    (k : NU) (x : Uplane) :
    (((resU k⁻¹ : Module.End (ZMod 2) Uplane) x : Uplane) : Wv v0) = wAct v0 (k : Kstab v0) x := by
  rw [coe_resU_apply]
  congr 1
  rw [Subgroup.coe_inv, inv_inv]

def sgnN :
    NU := ⟨sgnK, sgnK_mem_NU⟩

theorem T1_ne_one :
    resU sgnN⁻¹ ≠ 1 := by
  intro h
  have := congrArg (fun u : (Module.End (ZMod 2) Uplane)ˣ =>
    (((u : Module.End (ZMod 2) Uplane) ⟨sW, sW_mem_Uplane⟩ : Uplane) : Wv v0)) h
  simp only [coe_resU_inv_apply, Units.val_one, Module.End.one_apply] at this
  change wAct v0 sgnK sW = sW at this
  rw [sgnK_sW] at this
  exact wFr_ne_zero (by simpa using this)

theorem T1_sq :
    resU sgnN⁻¹ * resU sgnN⁻¹ = 1 := by
  rw [← map_mul, resU_eq_one_iff]
  intro x hx
  rw [Subgroup.coe_mul, Subgroup.coe_inv, ← mul_inv_rev, inv_inv]
  change wAct v0 (sgnK * sgnK) x = x
  rw [wAct_mul, Module.End.mul_apply]
  rcases (mem_Uplane_iff x).1 hx with rfl | rfl | rfl | rfl
  · rw [map_zero, map_zero]
  · rw [sgnK_wFr, sgnK_wFr]
  · rw [sgnK_sW, map_add, sgnK_wFr, sgnK_sW, ← add_assoc, two_smul_W, zero_add]
  · rw [map_add, sgnK_wFr, sgnK_sW, map_add, sgnK_wFr, map_add, sgnK_wFr, sgnK_sW,
      ← add_assoc, ← add_assoc, two_smul_W, zero_add]

instance finite_glU :
    Finite (Module.End (ZMod 2) Uplane)ˣ :=
  Nat.finite_of_card_ne_zero (by rw [natCard_glU]; norm_num)

theorem orderOf_T1 :
    orderOf (resU sgnN⁻¹) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact T1_sq) T1_ne_one

theorem two_dvd_range :
    2 ∣ Nat.card resU.range := by
  have h := Subgroup.orderOf_dvd_natCard resU.range (x := resU sgnN⁻¹) ⟨_, rfl⟩
  rwa [orderOf_T1] at h

theorem T1_mem_range :
    resU sgnN⁻¹ ∈ resU.range := ⟨_, rfl⟩

theorem range_dvd_six :
    Nat.card resU.range ∣ 6 := by
  have h := Subgroup.card_subgroup_dvd_card resU.range
  rwa [natCard_glU] at h

instance CU_subgroupOf_normal :
    (CU.subgroupOf NU).Normal := ker_resU ▸ resU.normal_ker

theorem monoSub_ceqFtwo_le_Kstab :
    monoSub ceqFtwoHyp ≤ Kstab v0 :=
  (monoSub_mono ceqFtwoHyp ceqHyp le_rfl Ftwo_le_Ppair).trans monoSub_ceq_le_Kstab

theorem monoSub_cbothFtwo_le_Kstab :
    monoSub cbothFtwoHyp ≤ Kstab v0 :=
  (monoSub_mono cbothFtwoHyp ceqHyp inf_le_left Ftwo_le_Ppair).trans monoSub_ceq_le_Kstab

theorem map_NUw :
    (NU ⊓ Mfr).map (Kstab v0).subtype = monoSub ceqFtwoHyp := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (mem_NUw_iff k).1 hk
  · intro hx
    exact ⟨⟨x, monoSub_ceqFtwo_le_Kstab hx⟩, (mem_NUw_iff _).2 hx, rfl⟩

theorem map_CU :
    CU.map (Kstab v0).subtype = monoSub cbothFtwoHyp := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (mem_CU_iff k).1 hk
  · intro hx
    exact ⟨⟨x, monoSub_cbothFtwo_le_Kstab hx⟩, (mem_CU_iff _).2 hx, rfl⟩

noncomputable def nuwEquivMono :
    ↥(NU ⊓ Mfr) ≃* monoSub ceqFtwoHyp :=
  ((NU ⊓ Mfr).equivMapOfInjective (Kstab v0).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr map_NUw)

noncomputable def cuEquivMono :
    CU ≃* monoSub cbothFtwoHyp :=
  (CU.equivMapOfInjective (Kstab v0).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr map_CU)

theorem natCard_Cboth_quot : Nat.card (Cboth ⧸ ΩIn Cboth) = 2 ^ 9 := by
  rw [natCard_quot_ΩIn cbothFtwoHyp, finrank_Cboth]

theorem natCard_CU :
    Nat.card CU = 1966080 := by
  rw [Nat.card_congr cuEquivMono.toEquiv, natCard_monoSub, natCard_Cboth_quot, natCard_Ftwo]
  norm_num

instance finite_monoSub_cboth :
    Finite (monoSub cbothFtwoHyp) :=
  Finite.of_equiv _ cuEquivMono.toEquiv

theorem alpha_monoProj_surjective : Function.Surjective (alpha.comp (monoProj cbothFtwoHyp)) := by
  rw [MonoidHom.coe_comp]
  exact alpha_surjective.comp (monoProj_surjective cbothFtwoHyp)

noncomputable def betaCU :
    CU →* Equiv.Perm (Fin 5) :=
  (alpha.comp (monoProj cbothFtwoHyp)).comp cuEquivMono.toMonoidHom

theorem betaCU_surjective :
    Function.Surjective betaCU := by
  rw [betaCU, MonoidHom.coe_comp]
  exact alpha_monoProj_surjective.comp cuEquivMono.surjective

theorem natCard_ker_betaCU :
    Nat.card betaCU.ker = 2 ^ 14 := by
  have h1 : Nat.card (alpha.comp (monoProj cbothFtwoHyp)).ker = 2 ^ 9 * 32 := by
    rw [natCard_ker_comp_of_surjective (monoProj_surjective cbothFtwoHyp) alpha_surjective,
      natCard_ker_monoProj, natCard_Cboth_quot, natCard_ker_alpha]
  rw [betaCU, natCard_ker_comp_of_surjective cuEquivMono.surjective
    alpha_monoProj_surjective, h1]
  have hk : cuEquivMono.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).2 cuEquivMono.injective
  rw [hk, Subgroup.card_bot]
  norm_num

theorem ker_betaCU :
    betaCU.ker = CFSG.pCore 2 CU := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ker_eq_pCore_of_surjective betaCU_surjective
    (IsPGroup.of_card (n := 14) natCard_ker_betaCU) pCore_perm_five

theorem natCard_pCore_CU :
    Nat.card (CFSG.pCore 2 CU) = 2 ^ 14 := by
  rw [← ker_betaCU, natCard_ker_betaCU]

noncomputable def cuQuotEquiv :
    CU ⧸ CFSG.pCore 2 CU ≃* Equiv.Perm (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq ker_betaCU.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective betaCU betaCU_surjective)

end CFSG.Monster.B.TwoA
