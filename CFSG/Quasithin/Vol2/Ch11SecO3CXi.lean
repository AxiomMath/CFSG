module

public import CFSG.Quasithin.Vol2.Ch11SecO3CXf
public import CFSG.Quasithin.Vol2.Ch11SecO3CXh
public import CFSG.Quasithin.Vol2.Ch11SecO1J
public import CFSG.Quasithin.Vol2.Ch11SecB21Cent
public import CFSG.Quasithin.Vol2.Ch11SecFOblCX
public import CFSG.Quasithin.Vol2.Ch11SecO3CXd

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 Matrix
open CFSG.Quasithin.Vol2.KGNat (psiSp vec4 spJ)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (eq_map_psiSp_of_sylow inf_normalizer_eq_sp
  exists_eq_map_torus_sp Usp_eq_unipotent)
open CFSG.QuasithinUnique.C5 (conjSubgroup_normalizer)
open scoped IsMulCommutative

theorem obl11_5_7Sp4CX_of (hF : Sp4Facts) (hN : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1110 : Stmt11_1_0) (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) : Obl11_5_7Sp4CX := by
  intro G _ _ T L I n V₁ V₃ X y h hV₁ hV₃ hk hW _ hX hy hyX hopp
  have hS := SecD.natSetting11_of h1102 h1141 h hV₁
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
  obtain ⟨hV₁₃, -⟩ := SecD.natV3Fact_holds G T L I n V₁ V₃ hS (Or.inr hk) hV₁ hV₃
  have hFr := O3CX.frame_of hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂ hV₃ hk hV₁₃
    hy hopp
  have := hFr.dQ_normal
  have hQ := fsuV_le_pCoreOf_normalizer hF h1102 h1103 h1141 h1143 h1154 h1156 h hV₁ hk
  have hWT : wH T I V₁ ≤ T :=
    (conjClosure_le_pCoreOf hQ).trans (pCoreOf_normalizer_V₁_le_T h hV₁)
  have hyV := SecA.L_le_normalizer_fsuV h hy
  have hXinf := cartan_le_inf hN h1102 h hV₁ hX hyX
  have hNW : Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer ((wH T I V₁ : Subgroup G) : Set G) := le_normalizer_conjClosure _ _
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, hg, hV₁g, -, hV₃g⟩ := O2.exists_coord hS hk
  have hV₁g' := hV₁g V₁ hV₁
  have hV₃g' := hV₃g V₃ hV₃
  have hD := SecO1.isHall_autOn_cartan hS hX
  rw [eq_map_psiSp_of_sylow hg, inf_normalizer_eq_sp hf g] at hD
  obtain ⟨x', hx'U, hDx⟩ := exists_eq_map_torus_sp hf g hD
  rw [← Usp_eq_unipotent] at hx'U
  have hg' : mat 2 K (g * x') *ᵥ vec4 1 0 0 0 = mat 2 K g *ᵥ vec4 1 0 0 0 := by
    rw [map_mul, ← Matrix.mulVec_mulVec, O3CX.Usp_mulVec_e0 hx'U]
  let ρ : StatedSp 2 K →* MulAut ↥(fsuV T I) := (autOn L (fsuV T I)).subtype.comp π
  have htor : ∀ a : Kˣ, ∃ x ∈ X, ∃ hx : x ∈ Subgroup.normalizer (fsuV T I : Set G),
      SecA.conjV (fsuV T I) x hx = ρ (g * x' * torusHom (Pi.mulSingle 0 a) * (g * x')⁻¹) := by
    intro a
    have hmem : psiSp π (g * x') (torusHom (Pi.mulSingle 0 a)) ∈ autOn X (fsuV T I) := by
      rw [hDx]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    obtain ⟨x, hxX, hxV, hxeq⟩ := SecA.mem_autOn_iff.mp hmem
    exact ⟨x, hxX, hxV, hxeq.symm⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSp 2 K),
      π γ = ⟨SecA.conjV (fsuV T I) y hyV, SecA.conjV_mem_autOn hy hyV⟩ := hf.onto _
  have hyγ : SecA.conjV (fsuV T I) y hyV =
      ((π γ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by rw [hγ]
  have hβ := O3CX.bil_ne_zero hf hV₁g' hV₃g' hyV hyγ hopp
  obtain ⟨a, ha⟩ := SecO1.exists_units_ne_one hn hK
  obtain ⟨x, hxX, hxV, hxa⟩ := htor a
  have hu := O3CX.eq_smul_of_mem_normalizer hf hg' hV₁g' hyV hyγ hβ ha (hXinf hxX).2 hxV hxa
  rw [← hg'] at hu hβ
  have hfull := O3CX.exists_trv_full ρ hg' (V := fsuV T I) (W := wH T I V₁)
    (fun w hw => by
      have hr := (conjClosure_le_pCoreOf hQ).trans (pCoreOf_normalizer_V₁_le_ROf h hV₁) hw
      have hC₃ := conjClosure_le_centralizer_V₃ hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h
        hV₁ hV₂ hV₃ hk hw
      obtain ⟨c, hc⟩ := O2.exists_trv_of_r1 hS hK hπ hf hV₁ hV₁g' hV₃g' hr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp hC₃ u hu).symm
      exact ⟨_, c, hc⟩)
    (fun hle => commutator_fsuV_conjClosure_ne_bot hW (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle))
    (fun a => by
      obtain ⟨t, htX, htV, ht⟩ := htor a
      exact ⟨t, hNW (hXinf htX).1.2, htV, ht⟩)
  obtain ⟨wf, wf', hR, hwf', hτ⟩ := O3CX.exists_roots (W := wH T I V₁)
    (C := Subgroup.centralizer (fsuV T I : Set G)) ρ (g * x')
    (fun c => by rw [hg']; exact hfull c)
    (fun _ hh h1 => O3CX.mem_centralizer_of_conjV_eq_one hh h1)
    (fun _ hh δ l hδ hl => hNW (O3CX.mem_normalizer_of_eigen hf (SecA.IsVi.le_fsuV hV₁) hV₁g' hh
      hδ (by rw [← hg']; exact hl)))
    hFr.wC hyV (mem_normalizer_centralizer' hyV) hyγ hβ hu
  obtain ⟨hτV, hτρ⟩ := hτ a
  set β := Matrix.toBilin' (spJ K) (mat 2 K (g * x') *ᵥ vec4 1 0 0 0)
    (mat 2 K γ⁻¹ *ᵥ (mat 2 K (g * x') *ᵥ vec4 1 0 0 0)) with hβdef
  set τ := (wf a * wf' ((a : K) * β ^ 2)⁻¹ * wf a) * (wf 1 * wf' (1 * β ^ 2)⁻¹ * wf 1) with hτdef
  have hzV : τ⁻¹ * x ∈ Subgroup.normalizer (fsuV T I : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hτV) hxV
  have hzC : τ⁻¹ * x ∈ Subgroup.centralizer (fsuV T I : Set G) :=
    O3CX.mem_centralizer_of_conjV_eq_one hzV (by
      rw [SecA.conjV_mul _ (Subgroup.inv_mem _ hτV) hxV, SecA.conjV_inv _ hτV, hτρ, hxa]
      exact inv_mul_cancel _)
  have hLT : ∀ c, wf c ∈ L ⊔ T := fun c => Subgroup.mem_sup_right (hWT (hR.mem c))
  have hyLT : y ∈ L ⊔ T := Subgroup.mem_sup_left hy
  have hLT' : ∀ d, wf' d ∈ L ⊔ T := fun d => by
    rw [hwf' d]
    exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).inv_mem hyLT) (hLT d)) hyLT
  have hτLT : τ ∈ L ⊔ T :=
    (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).mul_mem (hLT _) (hLT' _)) (hLT _))
      ((L ⊔ T).mul_mem ((L ⊔ T).mul_mem (hLT _) (hLT' _)) (hLT _))
  have hzLT : τ⁻¹ * x ∈ L ⊔ T :=
    (L ⊔ T).mul_mem ((L ⊔ T).inv_mem hτLT) (Subgroup.mem_sup_left (hX.1 hxX).1)
  obtain ⟨k, hk2⟩ := SecB.isPGroup_sup_inf_centralizer h1102 h ⟨τ⁻¹ * x, hzLT, hzC⟩
  have hzk : (τ⁻¹ * x) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk2
  have hxW' : x ∈ Subgroup.normalizer ((conjSubgroup (wH T I V₁) y : Subgroup G) : Set G) := by
    have h2 : x ∈ conjSubgroup (Subgroup.normalizer (V₁ : Set G)) y := by
      rw [conjSubgroup_normalizer]
      exact (hXinf hxX).2
    rw [mem_conjSubgroup_iff] at h2
    rw [← conjSubgroup_normalizer, mem_conjSubgroup_iff]
    exact hNW h2
  have hxn := O3CX.norm_of (hNW (hXinf hxX).1.2) hxW' (mem_normalizer_centralizer' hxV)
  have hzn := O3CX.norm_of (hFr.cW hzC) (hFr.cW' hzC) (Subgroup.le_normalizer hzC)
  intro q hq
  have hxq : x * q * x⁻¹ = q := by
    rw [Subgroup.mem_centralizer_iff.mp hq.2 x hxX, mul_inv_cancel_right]
  exact hR.mem_D_of_comm hFr hβ one_ne_zero a.ne_zero
    (fun h1 => ha (Units.val_eq_one.mp h1.symm)) hzC hzn hzk (mul_inv_cancel_left τ x).symm hxn
    hq.1 hxq

end CFSG.Quasithin.Vol2.Ch11.SecF
