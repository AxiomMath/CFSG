module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Siegel
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Vol2.Ch11SecANat

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open scoped IsMulCommutative commutatorElement

variable {K : Type} [Field K] [CharP K 2]

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem eq_rhoG_of_modZ (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (hcomm : commV H = ⊤) (hZ : ∀ z ∈ Z, z ∈ fixV H) {τ : MulAut W}
    (hτN : ∀ x ∈ H, τ * x * τ⁻¹ ∈ H) {γ : ↥(cayleyGroup K)}
    (hτ : ∀ w, f (τ w) = g2Act γ (f w)) : τ = ((rhoG hc0 hc1 π γ : ↥H) : MulAut W) := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : MulAut W, ρ = ((rhoG hc0 hc1 π γ : ↥H) : MulAut W) := ⟨_, rfl⟩
  have hρH : ρ ∈ H := hρ ▸ (rhoG hc0 hc1 π γ).2
  have hρi : ρ⁻¹ = ((rhoG hc0 hc1 π γ⁻¹ : ↥H) : MulAut W) := by
    rw [hρ, map_inv, Subgroup.coe_inv]
  have hδN : ∀ x ∈ H, (ρ⁻¹ * τ) * x * (ρ⁻¹ * τ)⁻¹ ∈ H := by
    intro x hx
    rw [show (ρ⁻¹ * τ) * x * (ρ⁻¹ * τ)⁻¹ = ρ⁻¹ * (τ * x * τ⁻¹) * ρ by group]
    exact H.mul_mem (H.mul_mem (H.inv_mem hρH) (hτN x hx)) hρH
  have hδ : ∀ w, f ((ρ⁻¹ * τ) w) = f w := by
    intro w
    rw [MulAut.mul_apply, hρi, IsCoord.actG hf hc0 hc1, hτ, g2Act_inv_apply]
  have h1 := eq_one_of_commV hcomm (commute_of_trivial_modG hf hc0 hc1 hδN hδ)
    (fun w => hZ _ ((hf.ker _).mp (by rw [hf.map_mul_inv, hδ, sub_self])))
  rw [← hρ]
  exact (inv_mul_eq_one.mp h1).symm

theorem commS_eq_vt (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (g : ↥(cayleyGroup K)) (hW : ∀ w : W, w ^ 2 = 1) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) :
    Ch11.SecA.commS ((perfectCore (stabQ (stdF K 2))).map (psiG hc0 hc1 π g))
        (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) =
      (commHom (psiG hc0 hc1 π g (tL 1))).range := by
  have ha : ((Units.mk0 c₀ hc0 : Kˣ) : K) ≠ 1 := hc1
  have hs1 : (1 : K) ≠ 0 := one_ne_zero
  have hle : Ch11.SecA.commS ((perfectCore (stabQ (stdF K 2))).map (psiG hc0 hc1 π g))
      (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) ≤
        (commHom (psiG hc0 hc1 π g (tL 1))).range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, hk, u, hu, rfl⟩
    obtain ⟨γ, hγ, rfl⟩ := hk
    obtain ⟨v, hv, hvz⟩ := exists_vt hf hc0 hc1 g hs1 hu
    obtain ⟨s', hs'⟩ := conj_tL_mem (perfectCore_le _ hγ) (1 : K)
    have hs'0 : s' ≠ 0 := by
      rintro rfl
      rw [tL_zero, mul_inv_eq_one, mul_eq_left] at hs'
      exact tL_one_ne_one hs'
    have hkv : psiG hc0 hc1 π g γ v ∈ (commHom (psiG hc0 hc1 π g (tL s'))).range := by
      obtain ⟨w, rfl⟩ := hv
      refine ⟨psiG hc0 hc1 π g γ w, ?_⟩
      rw [commHom_apply, commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, ← map_mul, ← hs',
        show γ * tL 1 * γ⁻¹ * γ = γ * tL 1 by group, map_mul, MulAut.mul_apply]
    have hkv' := vt_le hf hc0 hc1 g hW hZ hs1 hs'0 ha hkv
    have e : psiG hc0 hc1 π g γ u * u⁻¹ = psiG hc0 hc1 π g γ v * v⁻¹ := by
      conv_lhs => rw [← inv_mul_cancel_right u v]
      rw [map_mul, hZ _ (psiG_mem hc0 hc1 g _) _ hvz, mul_inv, mul_comm (u * v⁻¹), mul_assoc,
        mul_inv_cancel_left]
    rw [e]
    exact Subgroup.mul_mem _ hkv' (Subgroup.inv_mem _ hv)
  refine le_antisymm hle fun c hc => ?_
  have hd₀ : g2T (torHom2 K (Units.mk0 c₀ hc0)) ∈ perfectCore (stabQ (stdF K 2)) :=
    le_perfectCore_of_perfect sl2E1_le_stabQ (sl2E1_perfect hc0 hc1)
      (g2T_torHom2_mem_sl2E1 _)
  have hcU := vt_le_U2 hf hc0 hc1 g 1 hc
  obtain ⟨y, hyF, hy⟩ := exists_d0_sub_F2 ha (mem_gmapG.mp hcU)
  obtain ⟨u, hu⟩ := hf.surj (g2Act g y)
  have huU : u ∈ hf.pre (gmapG g (stdF K 2)).toAddSubgroup := by
    change f u ∈ gmapG g (stdF K 2)
    rw [mem_gmapG, hu, g2Act_inv_apply]
    exact hyF
  have hgen : psiG hc0 hc1 π g (g2T (torHom2 K (Units.mk0 c₀ hc0))) u * u⁻¹ ∈
      Ch11.SecA.commS ((perfectCore (stabQ (stdF K 2))).map (psiG hc0 hc1 π g))
        (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) :=
    Subgroup.subset_closure ⟨_, ⟨_, hd₀, rfl⟩, u, huU, rfl⟩
  have hfe : f (psiG hc0 hc1 π g (g2T (torHom2 K (Units.mk0 c₀ hc0))) u * u⁻¹) = f c := by
    rw [hf.map_mul_inv, f_psiG hf, hu, g2Act_inv_apply, ← map_sub, hy, g2Act_apply_inv]
  have hz : (psiG hc0 hc1 π g (g2T (torHom2 K (Units.mk0 c₀ hc0))) u * u⁻¹) * c⁻¹ ∈
      (commHom (psiG hc0 hc1 π g (tL 1))).range ⊓ Z :=
    ⟨Subgroup.mul_mem _ (hle hgen) (Subgroup.inv_mem _ hc), eq_of_f_eq hf hfe⟩
  rw [vt_inf_Z hf hc0 hc1 g hW hZ hs1 ha, Subgroup.mem_bot, mul_inv_eq_one] at hz
  rw [← hz]
  exact hgen

end Real

section Internal

variable {G : Type} [Group G]

theorem commutator_le_of_le_of_normalizer {V U M : Subgroup G} (hUV : U ≤ V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) : ⁅U, M⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro u hu m hm
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  refine V.mul_mem (hUV hu) ?_
  rw [← mul_assoc]
  exact (Subgroup.mem_normalizer_iff.mp (hMV hm) _).mp (V.inv_mem (hUV hu))

theorem commS_autOn_eq {V U M : Subgroup G} [IsMulCommutative ↥V] (hUV : U ≤ V)
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) :
    Ch11.SecA.commS (autOn M V) (U.subgroupOf V) = (⁅U, M⁆).subgroupOf V := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨φ, hφ, u, hu, rfl⟩
    obtain ⟨m, hmM, hmV, rfl⟩ := SecA.mem_autOn_iff.mp hφ
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      SecA.conjV_apply_coe]
    have h : m * (u : G) * m⁻¹ * (u : G)⁻¹ = ⁅(u : G), m⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hu hmM)
  · have hle : ⁅U, M⁆ ≤ (Ch11.SecA.commS (autOn M V) (U.subgroupOf V)).map V.subtype := by
      rw [Subgroup.commutator_le]
      intro u hu m hm
      have hmem : SecA.conjV V m (hMV hm) ⟨u, hUV hu⟩ * (⟨u, hUV hu⟩ : ↥V)⁻¹ ∈
          Ch11.SecA.commS (autOn M V) (U.subgroupOf V) :=
        Subgroup.subset_closure ⟨_, SecA.conjV_mem_autOn hm _, ⟨u, hUV hu⟩, hu, rfl⟩
      refine ⟨(SecA.conjV V m (hMV hm) ⟨u, hUV hu⟩ * (⟨u, hUV hu⟩ : ↥V)⁻¹)⁻¹,
        Subgroup.inv_mem _ hmem, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, SecA.conjV_apply_coe]
      rw [commutatorElement_def]
      group
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv
    obtain ⟨w, hw, hwv⟩ := hle hv
    rwa [← Subtype.ext hwv]

end Internal

end CFSG.Quasithin.Vol2.Ch11.G2Q8
