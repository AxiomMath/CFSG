module

public import CFSG.Quasithin.Vol2.Ch11SecO1D
public import CFSG.Quasithin.Vol2.Ch11SecO2B
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp qSp_inv Usp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom coe_torusHom)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (eq_map_psiSp_of_sylow inf_normalizer_eq_sp
  exists_eq_map_torus_sp Usp_eq_unipotent)
open scoped IsMulCommutative commutatorElement

namespace O3

variable {K : Type} [Field K]

theorem gmapSp_mul_of_stable {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hS : UStableSp S)
    (g : StatedSp 2 K) {x : StatedSp 2 K} (hx : x ∈ Usp K) : gmapSp (g * x) S = gmapSp g S := by
  ext v
  rw [mem_gmapSp, mem_gmapSp, _root_.mul_inv_rev, map_mul, ← Matrix.mulVec_mulVec,
    hS.mem_iff ((Usp K).inv_mem hx)]

theorem mat_torusHom (t : Fin 2 → Kˣ) :
    mat 2 K (torusHom t) = diagonal (Sum.elim (fun i => (t i : K)) fun i => ((t i)⁻¹ : Kˣ)) := by
  rw [mat_apply, coe_torusHom]

theorem torusHom_mulVec (t : Fin 2 → Kˣ) (v : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (torusHom t) *ᵥ v = vec4 ((t 0 : K) * v (.inl 0)) ((t 1 : K) * v (.inl 1))
      (((t 0)⁻¹ : Kˣ) * v (.inr 0)) (((t 1)⁻¹ : Kˣ) * v (.inr 1)) := by
  rw [mat_torusHom]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [mulVec_diagonal, vec4]

theorem comm_mulVec_f₁ (c : Kˣ) :
    mat 2 K (qSp 0 1 0 * torusHom (Pi.mulSingle 0 c) * (qSp 0 1 0)⁻¹ *
        (torusHom (Pi.mulSingle 0 c))⁻¹) *ᵥ vec4 0 0 0 1 = vec4 (1 - (c : K)) 0 0 1 := by
  rw [qSp_inv, ← map_inv, map_mul, map_mul, map_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [torusHom_mulVec, qSp_mulVec]
  refine vec4_eq ?_ (by simp [vec4]) (by simp [vec4]) (by simp [vec4])
  simp [vec4]
  ring

end O3

open O2 O3 in
theorem factSp4V3R1X_holds :
    ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ X : Subgroup G),
      SecD.NatSetting11 G T L I n → KindSp4 L (fsuV T I) n → IsVi T L I n 1 V₁ →
      IsVi T L I n 3 V₃ → IsCartanX T L X → ⁅V₃, ⁅pCoreOf 2 (LOf L V₁), X⁆⁆ ≠ ⊥ := by
  intro G _ _ T L I n V₁ V₃ X hS hk hV₁ hV₃ hX hbot
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, _, hK, π, f, hf, g, -, hg, hV₁g, -, hV₃g⟩ := exists_coord hS hk
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have : Finite (MulAut ↥(fsuV T I)) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨c, hc⟩ := SecO1.exists_units_ne_one hn hK
  have hD := SecO1.isHall_autOn_cartan hS hX
  rw [eq_map_psiSp_of_sylow hg, inf_normalizer_eq_sp hf g] at hD
  obtain ⟨x, hxU, hDx⟩ := exists_eq_map_torus_sp hf g hD
  rw [← Usp_eq_unipotent] at hxU
  have hV₁g' : V₁.subgroupOf (fsuV T I) = hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup := by
    rw [hV₁g V₁ hV₁, gmapSp_mul_of_stable spLine_stable g hxU]
  have hV₃g' : V₃.subgroupOf (fsuV T I) = hf.pre (gmapSp (g * x) (spHyp K)).toAddSubgroup := by
    rw [hV₃g V₃ hV₃, gmapSp_mul_of_stable spHyp_stable g hxU]
  have hmemX : psiSp π (g * x) (torusHom (Pi.mulSingle 0 c)) ∈ autOn X (fsuV T I) := by
    rw [hDx]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  obtain ⟨t, ht, htV, hteq⟩ := SecA.mem_autOn_iff.mp hmemX
  obtain ⟨y, hy, hyq⟩ := KA.exists_pCore_of_mem hf (g * x) (KA.qSp_mem_pCoreOf hK4 0 1)
  have hmemR : psiSp π (g * x) (qSp 0 1 0) ∈ autOn (pCoreOf 2 (LOf L V₁)) (fsuV T I) := by
    rw [← pCoreOf_p1_eq hS hV₁, hV₁g', ← hyq]
    exact (KA.mem_pCoreOf_iff' _ y).mpr hy
  obtain ⟨r, hr, hrV, hreq⟩ := SecA.mem_autOn_iff.mp hmemR
  obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K (g * x) *ᵥ vec4 0 0 0 1)
  have hu₀V₃ : (u₀ : G) ∈ V₃ := by
    rw [mem_iff_of_eq hV₃g', hu₀, mat_inv_mulVec]
    rfl
  have hrt : ⁅r, t⁆ ∈ ⁅pCoreOf 2 (LOf L V₁), X⁆ := Subgroup.commutator_mem_commutator hr ht
  have hrtV : ⁅r, t⁆ ∈ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrV htV)
      (Subgroup.inv_mem _ hrV)) (Subgroup.inv_mem _ htV)
  have h1 := mul_comm_of_commutator_eq_bot hbot hrt (u₀ : G) hu₀V₃
  have h2 : SecA.conjV (fsuV T I) ⁅r, t⁆ hrtV u₀ = u₀ :=
    Subtype.ext (by rw [SecA.conjV_apply_coe, h1, mul_inv_cancel_right])
  have hc' : SecA.conjV (fsuV T I) ⁅r, t⁆ hrtV = psiSp π (g * x) (qSp 0 1 0 *
      torusHom (Pi.mulSingle 0 c) * (qSp 0 1 0)⁻¹ * (torusHom (Pi.mulSingle 0 c))⁻¹) := by
    simp only [commutatorElement_def]
    rw [SecA.conjV_mul _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrV htV)
      (Subgroup.inv_mem _ hrV)) (Subgroup.inv_mem _ htV),
      SecA.conjV_mul _ (Subgroup.mul_mem _ hrV htV) (Subgroup.inv_mem _ hrV),
      SecA.conjV_mul _ hrV htV, SecA.conjV_inv _ hrV, SecA.conjV_inv _ htV, ← hreq, ← hteq, map_mul,
      map_mul, map_mul, map_inv, map_inv]
  rw [hc'] at h2
  have h3 := congrArg f h2
  rw [psiSp_apply, hf.act4, KA.gconj_mulVec_sp, hu₀, mat_inv_mulVec, comm_mulVec_f₁] at h3
  have h4 := congrArg (fun v => mat 2 K (g * x)⁻¹ *ᵥ v) h3
  simp only [mat_inv_mulVec] at h4
  have h5 := congrFun h4 (.inl 0)
  have h6 : (1 : K) - c = 0 := by simpa [vec4] using h5
  exact hc (Units.val_eq_one.mp (sub_eq_zero.mp h6).symm)

end CFSG.Quasithin.Vol2.Ch11.SecF
