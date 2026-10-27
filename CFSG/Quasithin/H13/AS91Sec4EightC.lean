module

public import CFSG.Quasithin.H13.AS91Sec4EightC3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

theorem mul_comm_iff_mul_inv_mul_inv_eq_one {X : Type*} [Group X] (x y : X) :
    x * y = y * x ↔ x * y * x⁻¹ * y⁻¹ = 1 := by
  constructor
  · intro hxy
    rw [hxy]
    group
  · intro hxy
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [hxy, one_mul]

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section I


@[expose] noncomputable def Iset : Set ↥D.E := {x | ∃ e : ↥D.E, x = e⁻¹ * (D.tb : MulAut ↥D.E) e}

@[expose] noncomputable def Cb : Subgroup ↥D.Mb := centralizer {D.tb}

theorem tb_apply (e : ↥D.E) : (((D.tb : MulAut ↥D.E) e : ↥D.E) : G) = D.q0e * e * D.q0e⁻¹ := rfl

theorem apply_mem_Iset {φ : ↥D.Mb} (hφ : φ ∈ D.Cb) {x : ↥D.E} (hx : x ∈ D.Iset) :
    (φ : MulAut ↥D.E) x ∈ D.Iset := by
  obtain ⟨e, rfl⟩ := hx
  refine ⟨(φ : MulAut ↥D.E) e, ?_⟩
  have hc : (φ : MulAut ↥D.E) * (D.tb : MulAut ↥D.E) = (D.tb : MulAut ↥D.E) * (φ : MulAut ↥D.E) :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp hφ)
  rw [map_mul, map_inv]
  congr 1
  exact (congrArg (fun ψ : MulAut ↥D.E => ψ e) hc)

@[expose] noncomputable def omE (c : ℕ) : ↥D.E := ⟨D.elt7 c, D.E1_le_E (D.elt7_mem_E1 c)⟩

theorem omE_one : D.omE 1 = D.zE := Subtype.ext D.elt7_one

theorem bE_one : D.bE 1 = D.rep 3 := by
  rw [bE, if_neg one_ne_zero]
  rfl

theorem rep3_mem_E1 : D.rep 3 ∈ D.E1 := D.bE_one ▸ D.bE_mem_E1 1

theorem crd_rep3 : D.crd (D.rep 3) = 2 := by
  rw [← D.bE_one]
  exact D.crd_bE (j := 1) (by norm_num)

end I

section ICodes

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

theorem wc_eq_of_crd6 {x : G} (hx : x ∈ D.E1) {w : ℕ} (hw : w ∈ Two.w1List)
    (h1 : Two.crd6 w = D.crd x / 2) : w = D.wc x := by
  rw [crd_div_two] at h1
  rw [← Two.vec6_crd6 w hw, h1, Two.vec6_crd6 _ (D.wc_mem hx)]

theorem polar_40_q0 : QuadraticMap.polar CFSG.GF2Type.Smith1979.GammaU.q0 (vecOf 40) (vecOf Two.q0c) = 1 := by
  rw [polar_vecOf]
  decide

theorem wc_q0 : D.wc D.q0e = Two.q0c := by
  rw [wc, q0e, D.ψV_cl_rep, codeOf_vecOf (by decide)]

theorem Ielt_facts (e : ↥D.E) :
    ((e⁻¹ * (D.tb : MulAut ↥D.E) e : ↥D.E) : G) ∈ D.E1 ∧
      D.wc ((e⁻¹ * (D.tb : MulAut ↥D.E) e : ↥D.E) : G) =
        codeOf (D.Φo (h.setting.ρ ⟨(e : G)⁻¹, inv_mem (D.E_le_M e.2)⟩) (vecOf Two.q0c) +
          vecOf Two.q0c) := by
  have hq := D.q0e_mem_QG
  have heM : (e : G) ∈ h.setting.M := D.E_le_M e.2
  have hval : ((e⁻¹ * (D.tb : MulAut ↥D.E) e : ↥D.E) : G) =
      ((e : G)⁻¹ * D.q0e * ((e : G)⁻¹)⁻¹) * D.q0e⁻¹ := by
    rw [Subgroup.coe_mul, tb_apply, Subgroup.coe_inv, inv_inv]
    group
  have hc1 : (e : G)⁻¹ * D.q0e * ((e : G)⁻¹)⁻¹ ∈ h.setting.QG := h.setting.conj_mem_QG (inv_mem heM) hq
  have hQ : ((e : G)⁻¹ * D.q0e * ((e : G)⁻¹)⁻¹) * D.q0e⁻¹ ∈ h.setting.QG := mul_mem hc1 (inv_mem hq)
  refine ⟨D.mem_E1_of_mem_E (hval ▸ hQ) (e⁻¹ * (D.tb : MulAut ↥D.E) e).2, ?_⟩
  rw [hval, D.wc_mul hc1 (inv_mem hq), D.wc_conj (inv_mem heM) hq]
  rw [show D.wc D.q0e⁻¹ = D.wc D.q0e by rw [wc, h.setting.cl_inv hq, ← wc], D.wc_q0]
  rw [← codeOf_vecOf (n := Two.q0c) (by decide), ← codeOf_add, codeOf_vecOf (by decide)]

include hOut hTw hHat

theorem mem_Iset_iff (x : ↥D.E) :
    x ∈ D.Iset ↔ (x : G) ∈ D.E1 ∧ D.crd x ∈ Two.i7List := by
  obtain ⟨-, -, hi3, hi4, -⟩ := Two.iOK48_spec
  obtain ⟨-, -, -, -, hid, hc, -⟩ := Two.ebOK46_spec
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨hE1, hw⟩ := D.Ielt_facts e
    refine ⟨hE1, ?_⟩
    have hU := D.Φo_mem_eb hOut hTw (inv_mem e.2) (inv_mem (D.E_le_M e.2))
    obtain ⟨r, hr, hUr⟩ := complete hid hc _ hU
    have hit : D.wc ((e⁻¹ * (D.tb : MulAut ↥D.E) e : ↥D.E) : G) ∈ Two.itList () := by
      rw [hw, hUr, ← vecOf_appN, ← vecOf_xor,
        codeOf_vecOf (Nat.xor_lt_two_pow (n := 12)
          (appN_lt (okRows_spec (enumGrp_sound Two.gensOK_eb r hr).1).2 _) (by decide))]
      simp only [Two.itList, List.mem_dedup, List.mem_map]
      exact ⟨r, hr, rfl⟩
    obtain ⟨h1, h2⟩ := hi3 _ hit
    unfold crd
    split_ifs
    · exact h1
    · exact h2
  · rintro ⟨hx, hcx⟩
    obtain ⟨w, hw, hwc⟩ := hi4 _ hcx
    have hw1 : w ∈ Two.w1List := (Two.iOK48_spec.2.1) w hw
    have hwx := D.wc_eq_of_crd6 hx hw1 hwc
    simp only [Two.itList, List.mem_dedup, List.mem_map] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    obtain ⟨-, U, hU, hUr⟩ := enumGrp_sound Two.gensOK_eb r hr
    obtain ⟨s, hsE, hsU⟩ := D.exists_mem_E hOut hTw hU
    set e : ↥D.E := ⟨(s : G)⁻¹, inv_mem hsE⟩ with he
    obtain ⟨hyE1, hyw⟩ := D.Ielt_facts e
    have hρ : h.setting.ρ ⟨(e : G)⁻¹, inv_mem (D.E_le_M e.2)⟩ = h.setting.ρ s := by
      congr 1
      apply Subtype.ext
      simp [he]
    rw [hρ, hsU, hUr, ← vecOf_appN, ← vecOf_xor,
      codeOf_vecOf (Nat.xor_lt_two_pow (n := 12)
        (appN_lt (okRows_spec (enumGrp_sound Two.gensOK_eb r hr).1).2 _) (by decide)), hwx] at hyw
    set y : ↥D.E := e⁻¹ * (D.tb : MulAut ↥D.E) e with hy
    have hcl : h.setting.cl (y : G) = h.setting.cl (x : G) := by
      apply D.ψV.injective
      rw [← vecOf_codeOf (D.ψV (h.setting.cl (y : G))), ← vecOf_codeOf (D.ψV (h.setting.cl (x : G)))]
      exact congrArg vecOf hyw
    rcases (h.setting.cl_eq_cl_iff (D.E1_le_QG hyE1) (D.E1_le_QG hx)).mp hcl with h1 | h1
    · exact ⟨e, Subtype.ext h1⟩
    ·
      have hf : D.rep 40 ∈ D.E1 := D.mem_E1.mpr ⟨D.rep_mem _, by
        rw [D.ψV_cl_rep]
        exact (Two.vecOf_mem_W1 (by decide)).mpr (by decide)⟩
      set f : ↥D.E := ⟨D.rep 40, D.E1_le_E hf⟩ with hfdef
      have hfz : ((f⁻¹ * (D.tb : MulAut ↥D.E) f : ↥D.E) : G) = z := by
        rw [Subgroup.coe_mul, tb_apply, Subgroup.coe_inv]
        have hpol : QuadraticMap.polar h.setting.q (h.setting.cl D.q0e) (h.setting.cl (D.rep 40)) = 1 := by
          rw [D.polar_ψV, QuadraticMap.polar_comm, D.ψV_cl_rep, q0e, D.ψV_cl_rep]
          exact polar_40_q0
        rw [conj_eq_mul_z_of_polar h.setting D.q0e_mem_QG (D.rep_mem _) hpol]
        change (D.rep 40)⁻¹ * (D.rep 40 * h.setting.z) = z
        rw [← mul_assoc, inv_mul_cancel, one_mul]
        rfl
      refine ⟨e * f, Subtype.ext ?_⟩
      have hEc : ∀ a b : ↥D.E, a * b = b * a := fun a b =>
        Subtype.ext (D.E_comm hOut hTw hHat a.2 b.2)
      have e2 : (e * f)⁻¹ * (D.tb : MulAut ↥D.E) (e * f) =
          (e⁻¹ * (D.tb : MulAut ↥D.E) e) * (f⁻¹ * (D.tb : MulAut ↥D.E) f) := by
        rw [map_mul, mul_inv_rev]
        calc f⁻¹ * e⁻¹ * ((D.tb : MulAut ↥D.E) e * (D.tb : MulAut ↥D.E) f) =
            e⁻¹ * (f⁻¹ * (D.tb : MulAut ↥D.E) e) * (D.tb : MulAut ↥D.E) f := by
              rw [hEc f⁻¹ e⁻¹]; group
          _ = e⁻¹ * ((D.tb : MulAut ↥D.E) e * f⁻¹) * (D.tb : MulAut ↥D.E) f := by
              rw [hEc f⁻¹]
          _ = _ := by group
      rw [e2, Subgroup.coe_mul, hfz]
      exact h1

theorem zE_mem_Iset : D.zE ∈ D.Iset := by
  refine (D.mem_Iset_iff hOut hTw hHat D.zE).mpr ⟨D.z_mem_E1, ?_⟩
  change D.crd z ∈ Two.i7List
  rw [D.crd_z]
  decide

theorem crd_of_conj {x : ↥D.E} (hx : x ∈ D.Iset) {g : G} (hg : g * z * g⁻¹ = (x : G))
    (hne : (x : G) ≠ z) : D.crd x ∈ Two.omList := by
  obtain ⟨hxE1, hci⟩ := (D.mem_Iset_iff hOut hTw hHat x).mp hx
  obtain ⟨-, hw1, -, hi4, hi5, -⟩ := Two.iOK48_spec
  obtain ⟨w, hw, hwc⟩ := hi4 _ hci
  have hwx := D.wc_eq_of_crd6 hxE1 (hw1 w hw) hwc
  have hxQ : g * z * g⁻¹ ∈ Q z := by
    rw [hg, ← h.setting_QG]
    exact D.E1_le_QG hxE1
  rcases D.conj_z hOut hTw g hxQ with h1 | ⟨k, hk, hkr⟩
  · exact absurd (hg ▸ h1) hne
  have hwk : D.wc (x : G) = codeOf (D.Φo (h.setting.ρ ⟨k, hk⟩) (vecOf 3)) := by
    rw [← hg, ← hkr, D.wc_conj hk (D.rep_mem 3), wc, D.ψV_cl_rep, codeOf_vecOf (by norm_num)]
  have hO : Two.inO1b w = true := by
    rw [hwx, hwk]
    exact Two.inO1_invariant (D.Φo_mem_nGrp hOut hTw (MonoidHom.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩))
      Two.inO1_three
  obtain ⟨h2, h3⟩ := hi5 w hw hO
  rw [hwx] at h2 h3
  unfold crd
  split_ifs
  · exact h2
  · exact h3

theorem mem_Cb_iff (n : ↥(normalizer (D.E : Set G))) :
    D.toMb n ∈ D.Cb ↔ (n : G) * D.q0e * (n : G)⁻¹ * D.q0e⁻¹ ∈ D.E := by
  have hqN : D.q0e ∈ normalizer (D.E : Set G) := D.QG_le_N D.q0e_mem_QG
  have hcN : (n : G) * D.q0e * (n : G)⁻¹ * D.q0e⁻¹ ∈ normalizer (D.E : Set G) :=
    mul_mem (mul_mem (mul_mem n.2 hqN) (inv_mem n.2)) (inv_mem hqN)
  have e1 : D.toMb ⟨_, hcN⟩ = D.toMb n * D.tb * (D.toMb n)⁻¹ * D.tb⁻¹ := by
    rw [tb, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [Cb, mem_centralizer_singleton_iff, mul_comm_iff_mul_inv_mul_inv_eq_one, ← e1]
  exact D.toMb_eq_one_iff hOut hTw hHat _

end ICodes

section Orbit

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)
  {g₁ : G} (hg₁ : g₁ * z * g₁⁻¹ = D.rep 3) {s₀ : h.setting.M}
  (hs₀ : D.Φo (h.setting.ρ s₀) = Two.tE)

include hOut hTw hHat hg₁ hs₀

theorem exists_Cb_crd_three : ∃ φ ∈ D.Cb, (((φ : MulAut ↥D.E) D.zE : ↥D.E) : G) ∈ D.E1 ∧
    D.crd (((φ : MulAut ↥D.E) D.zE : ↥D.E) : G) = 3 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hi12, hi13⟩ := Two.iOK48_spec
  obtain ⟨-, -, h3z⟩ := D.rep_props vecOf_three_ne q0_three
  have hg₁' : g₁ * h.setting.z * g₁⁻¹ = D.rep 3 := hg₁
  have hzQa : h.setting.z ∈ h.setting.Qa g₁ :=
    h.setting.z_mem_Qa_of_mem_QG hg₁' (D.rep_mem 3) h3z
  obtain ⟨y, hyQa, hyz⟩ : ∃ y ∈ h.setting.Qa g₁, h.setting.z * y ≠ y * h.setting.z := by
    by_contra! hcon
    rcases (h.setting.conjBy g₁).eq_one_or_z_of_commute hzQa hcon with h1 | h1
    · exact h.setting.z_ne_one h1
    · rw [Setting.conjBy_z, hg₁'] at h1
      exact h3z h1.symm
  have hc : y * h.setting.z * y⁻¹ = D.rep 3 * h.setting.z := by
    rcases (h.setting.conjBy g₁).commutator_eq_one_or_z hyQa hzQa with h1 | h1
    · exfalso
      apply hyz
      calc h.setting.z * y = (y * h.setting.z * y⁻¹ * h.setting.z⁻¹)⁻¹ * (y * h.setting.z) := by
            group
        _ = y * h.setting.z := by rw [h1, inv_one, one_mul]
    · rw [Setting.conjBy_z, hg₁'] at h1
      calc y * h.setting.z * y⁻¹ = (y * h.setting.z * y⁻¹ * h.setting.z⁻¹) * h.setting.z := by
            group
        _ = D.rep 3 * h.setting.z := by rw [h1]
  have hyN : y ∈ normalizer (D.E : Set G) := D.K_le_normalizer_E hOut hTw hg₁ hs₀ hHat
    (by rw [D.Kgrp_eq_K0 hOut hTw hg₁ hs₀]; exact Qa₁_le_K0 g₁ s₀ hyQa)
  have hr : D.rep Two.iWit48 ∈ h.setting.Qa g₁ := by
    refine (D.mem_Qa_iff_inI hOut hTw hg₁ (D.rep_mem _)).mpr ?_
    show Two.inIb (codeOf (D.ψV (h.setting.cl (D.rep Two.iWit48)))) = true
    rw [D.ψV_cl_rep, codeOf_vecOf (by decide)]
    exact hi12
  have hf : D.q0e * (D.rep Two.iWit48)⁻¹ ∈ D.E1 := by
    refine D.mem_E1.mpr ⟨mul_mem D.q0e_mem_QG (inv_mem (D.rep_mem _)), ?_⟩
    rw [h.setting.cl_mul D.q0e_mem_QG (inv_mem (D.rep_mem _)), h.setting.cl_inv (D.rep_mem _),
      map_add, q0e, D.ψV_cl_rep, D.ψV_cl_rep, ← vecOf_xor]
    exact (Two.vecOf_mem_W1 (by decide)).mpr hi13
  have hyr : y * D.rep Two.iWit48 * y⁻¹ * (D.rep Two.iWit48)⁻¹ ∈ D.E := by
    rcases (h.setting.conjBy g₁).commutator_eq_one_or_z hyQa hr with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1, Setting.conjBy_z, hg₁']
      exact D.E1_le_E D.rep3_mem_E1
  have hφ : D.toMb ⟨y, hyN⟩ ∈ D.Cb := by
    refine (D.mem_Cb_iff hOut hTw hHat ⟨y, hyN⟩).mpr ?_
    show y * D.q0e * y⁻¹ * D.q0e⁻¹ ∈ D.E
    have hfE : D.q0e * (D.rep Two.iWit48)⁻¹ ∈ D.E := D.E1_le_E hf
    have e2 : y * D.q0e * y⁻¹ * D.q0e⁻¹ = (y * (D.q0e * (D.rep Two.iWit48)⁻¹) * y⁻¹) *
        (y * D.rep Two.iWit48 * y⁻¹ * (D.rep Two.iWit48)⁻¹) * (D.q0e * (D.rep Two.iWit48)⁻¹)⁻¹ := by
      group
    rw [e2]
    exact mul_mem (mul_mem ((mem_normalizer_iff.mp hyN _).mp hfE) hyr) (inv_mem hfE)
  refine ⟨D.toMb ⟨y, hyN⟩, hφ, ?_⟩
  have hv : ((((D.toMb ⟨y, hyN⟩ : ↥D.Mb) : MulAut ↥D.E) D.zE : ↥D.E) : G) = D.rep 3 * z := hc
  rw [hv]
  refine ⟨mul_mem D.rep3_mem_E1 D.z_mem_E1, ?_⟩
  calc D.crd (D.rep 3 * z) = D.crd (D.rep 3) ^^^ D.crd z := D.crd_mul D.rep3_mem_E1 D.z_mem_E1
    _ = 2 ^^^ 1 := by rw [D.crd_rep3, D.crd_z]
    _ = 3 := by decide

theorem orbit_eq :
    MulAction.orbit ↥D.Cb D.zE = D.omE '' ↑(1 :: Two.omList).toFinset := by
  ext x
  constructor
  · rintro ⟨φ, rfl⟩
    change ((φ : ↥D.Mb) : MulAut ↥D.E) D.zE ∈ _
    have hx : ((φ : ↥D.Mb) : MulAut ↥D.E) D.zE ∈ D.Iset :=
      D.apply_mem_Iset φ.2 (D.zE_mem_Iset hOut hTw hHat)
    obtain ⟨n, hφn⟩ := D.toMb_surjective (φ : ↥D.Mb)
    have hg : (n : G) * z * (n : G)⁻¹ = ((((φ : ↥D.Mb) : MulAut ↥D.E) D.zE : ↥D.E) : G) := by
      rw [← hφn]
      rfl
    by_cases hz : ((((φ : ↥D.Mb) : MulAut ↥D.E) D.zE : ↥D.E) : G) = z
    · refine ⟨1, by simp, Subtype.ext ?_⟩
      exact D.elt7_one.trans hz.symm
    · have hc := D.crd_of_conj hOut hTw hHat hx hg hz
      have hxE1 := ((D.mem_Iset_iff hOut hTw hHat _).mp hx).1
      refine ⟨D.crd _, ?_, Subtype.ext (D.elt7_crd hxE1)⟩
      rw [Finset.mem_coe, List.mem_toFinset]
      exact List.mem_cons_of_mem _ hc
  · rintro ⟨c, hc, rfl⟩
    rw [Finset.mem_coe, List.mem_toFinset, List.mem_cons] at hc
    rcases hc with rfl | hc
    · rw [D.omE_one]
      exact MulAction.mem_orbit_self _
    obtain ⟨-, -, -, -, -, -, -, hi8, -⟩ := Two.iOK48_spec
    obtain ⟨φ, hφC, hφ1, hφ3⟩ := D.exists_Cb_crd_three hOut hTw hHat hg₁ hs₀
    obtain ⟨X, hX, hX2⟩ := hi8 (c ^^^ 1) (Two.omList_xor_one c hc)
    obtain ⟨ψ, hψ, hψX⟩ := D.exists_of_mem_c3List hOut hTw hHat hX
    have hpres := D.presE1_of_mem_Mz hOut hTw hψ.1
    have hA1 : Two.app7 X 1 = 1 := by
      have := D.crd_apply hpres (x := D.zE) D.z_mem_E1
      rw [D.mem_Mz.mp hψ.1, hψX] at this
      change D.crd z = Two.app7 X (D.crd z) at this
      rw [D.crd_z] at this
      exact this.symm
    have hcx : D.crd (((ψ : MulAut ↥D.E) ((φ : MulAut ↥D.E) D.zE) : ↥D.E) : G) = c := by
      rw [D.crd_apply hpres hφ1, hψX, hφ3, show (3 : ℕ) = 1 ^^^ 2 by decide, Two.app7_xor, hA1,
        hX2, Nat.xor_comm c 1, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    refine ⟨⟨ψ * φ, mul_mem hψ.2 hφC⟩, Subtype.ext ?_⟩
    change (((ψ : MulAut ↥D.E) ((φ : MulAut ↥D.E) D.zE) : ↥D.E) : G) = D.elt7 c
    rw [← hcx]
    exact (D.elt7_crd (hpres _ hφ1)).symm

theorem ncard_orbit : (MulAction.orbit ↥D.Cb D.zE).ncard = 7 := by
  have hinj : Set.InjOn D.omE ↑(1 :: Two.omList).toFinset := by
    intro a ha b hb hab
    have hlt : ∀ c ∈ (1 :: Two.omList).toFinset, c < 128 := by decide
    exact D.elt7_injective (hlt a ha) (hlt b hb) (congrArg Subtype.val hab)
  rw [D.orbit_eq hOut hTw hHat hg₁ hs₀, hinj.ncard_image, Set.ncard_coe_finset]
  decide

end Orbit

section Card

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem card_stabilizer_zE : Nat.card (MulAction.stabilizer ↥D.Cb D.zE) = 3072 := by
  rw [← D.card_C3 hOut hTw hHat]
  exact Nat.card_congr
    { toFun := fun φ => ⟨φ.1.1, Subgroup.mem_inf.mpr ⟨D.mem_Mz.mpr φ.2, φ.1.2⟩⟩
      invFun := fun φ => ⟨⟨φ.1, (Subgroup.mem_inf.mp φ.2).2⟩, D.mem_Mz.mp (Subgroup.mem_inf.mp φ.2).1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_Cb : Nat.card D.Cb = 21504 := by
  obtain ⟨g₁, hg₁⟩ := D.exists_g₁ hOut hTw
  obtain ⟨s₀, hs₀⟩ := D.exists_s₀ hOut hTw
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥D.Cb D.zE)
  rw [MulAction.index_stabilizer, D.ncard_orbit hOut hTw hHat hg₁ hs₀,
    D.card_stabilizer_zE hOut hTw hHat] at h1
  omega

end Card

end Data41

end CFSG.Quasithin.H13.AS91
