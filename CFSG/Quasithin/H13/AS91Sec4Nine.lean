module

public import CFSG.Quasithin.H13.AS91Sec4NineComm
public import CFSG.Quasithin.H13.AS91Sec4Eight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

theorem C_le_M : H z ⊓ centralizer (zpowers (D.c : G) : Set G) ≤ h.setting.M := fun g hg =>
  h.setting.mem_M_iff.2 (by rw [h.setting_z]; exact mem_centralizer_singleton_iff.1 hg.1)

@[expose] noncomputable def psiC :
    ↥(H z ⊓ centralizer (zpowers (D.c : G) : Set G)) →* ↥(cMbar h.setting D.θ) :=
  ((h.setting.O.subtype.comp h.setting.ρ).comp (Subgroup.inclusion D.C_le_M)).codRestrict _
    fun g => rho_mem_cMbar D.ρ_c (h := Subgroup.inclusion D.C_le_M g) g.2.2

theorem psiC_surjective : Function.Surjective D.psiC := by
  intro y
  obtain ⟨m, hmX, hmy⟩ := exists_centralizer_of_mem_cMbar D.c_pow D.ρ_c y.2
  have hmH : (m : G) ∈ H z := by
    have hm := h.setting.mem_M_iff.1 m.2
    rw [h.setting_z] at hm
    exact mem_centralizer_singleton_iff.2 hm
  refine ⟨⟨m, hmH, hmX⟩, Subtype.ext ?_⟩
  exact hmy

theorem z_mem_C : z ∈ H z ⊓ centralizer (zpowers (D.c : G) : Set G) := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_iff.2 ?_⟩
  rintro _ ⟨k, rfl⟩
  have hcz : (D.c : G) * z = z * D.c := by
    have := h.setting.mem_M_iff.1 D.c.2
    rwa [h.setting_z] at this
  show (D.c : G) ^ k * z = z * (D.c : G) ^ k
  exact (Commute.zpow_left (show Commute (D.c : G) z from hcz) k).eq

theorem ker_psiC_le (hHat : HatM22SmallModules) :
    D.psiC.ker ≤ zpowers (⟨z, D.z_mem_C⟩ : ↥(H z ⊓ centralizer (zpowers (D.c : G) : Set G))) := by
  intro g hg
  have h1 : h.setting.ρ (Subgroup.inclusion D.C_le_M g) = 1 := by
    apply Subtype.ext
    have h0 := congrArg Subtype.val (MonoidHom.mem_ker.1 hg)
    exact h0
  have hQ := h.setting.mem_Q_of_ρ_eq_one h1
  have hQG : (g : G) ∈ h.setting.QG := ⟨_, hQ, rfl⟩
  have hgz : (g : G) ∈ zpowers h.setting.z := by
    rw [← inf_centralizer_eq hHat h.setting_width D.ρ_c D.θ_mem D.θ_ne D.hat]
    exact ⟨hQG, g.2.2⟩
  rw [h.setting_z] at hgz
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hgz
  exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩

theorem zC_mem_center :
    (⟨z, D.z_mem_C⟩ : ↥(H z ⊓ centralizer (zpowers (D.c : G) : Set G))) ∈
      center ↥(H z ⊓ centralizer (zpowers (D.c : G) : Set G)) := by
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2.1)

section Quasi

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)
  (hM : CFSG.CGT.T75P.M24SylowInput) (hJ : MathieuSmallIrr24)

include hOut hTw hHat hM hJ

theorem zC_mem_commutator :
    (⟨z, D.z_mem_C⟩ : ↥(H z ⊓ centralizer (zpowers (D.c : G) : Set G))) ∈
      commutator ↥(H z ⊓ centralizer (zpowers (D.c : G) : Set G)) := by
  have hz := D.z_mem_commutator hOut hTw hHat hM hJ
  rw [← Subgroup.map_subtype_commutator] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  have : w = ⟨z, D.z_mem_C⟩ := Subtype.ext hwz
  rwa [this] at hw

theorem commutator_C_eq_top :
    commutator ↥(H z ⊓ centralizer (zpowers (D.c : G) : Set G)) = ⊤ := by
  set C := H z ⊓ centralizer (zpowers (D.c : G) : Set G) with hC
  have hLp : commutator ↥(cMbar h.setting D.θ) = ⊤ := D.hat.1.1.commutator_eq_top
  have hmap : (commutator ↥C).map D.psiC = ⊤ := by
    rw [_root_.commutator_def, map_commutator,
      Subgroup.map_top_of_surjective _ (D.psiC_surjective), ← _root_.commutator_def, hLp]
  have hker : D.psiC.ker ≤ commutator ↥C :=
    (D.ker_psiC_le hHat).trans (zpowers_le.2 (D.zC_mem_commutator hOut hTw hHat hM hJ))
  rw [eq_top_iff]
  intro x _
  have hx : D.psiC x ∈ (commutator ↥C).map D.psiC := by rw [hmap]; exact mem_top _
  obtain ⟨k, hk, hkx⟩ := hx
  have hk' : k⁻¹ * x ∈ D.psiC.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
  have := mul_mem hk (hker hk')
  rwa [mul_inv_cancel_left] at this

theorem quasisimple_C :
    CFSG.IsQuasisimple ↥(H z ⊓ centralizer (zpowers (D.c : G) : Set G)) :=
  (CFSG.LocalCores.isQuasisimple_iff_of_surjective ⟨D.commutator_C_eq_top hOut hTw hHat hM hJ⟩
    D.psiC D.psiC_surjective ((D.ker_psiC_le hHat).trans (zpowers_le.2 D.zC_mem_center))).2 D.hat.1

end Quasi

section Inv

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem exists_inv_X :
    ∃ t ∈ H z, t * t = 1 ∧ ∀ x ∈ zpowers (D.c : G), t * x * t⁻¹ = x⁻¹ := by
  classical
  obtain ⟨-, -, s, -, -, hsN, -, -, -, -, -, hs, -, -, hs2, -, -, -⟩ :=
    D.exists_sGens_lift hOut hTw hHat
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinvs⟩ := Two.cjOK48_spec
  have hst := hinvs Two.cRows48 (by simp)
  have hinv := D.inv_θ_of_rows hs hst.1 hst.2
  have hsH : (s : G) ∈ H z := by
    have hs' := h.setting.mem_M_iff.1 s.2
    rw [h.setting_z] at hs'
    exact mem_centralizer_singleton_iff.2 hs'
  have hc3 : (D.c : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, D.c_pow, Subgroup.coe_one]
  have hsc : (s : G) * D.c * (s : G)⁻¹ = (D.c : G)⁻¹ := by
    have hmem : (s : G) * D.c * (s : G)⁻¹ ∈ zpowers (D.c : G) :=
      (mem_normalizer_iff.1 hsN _).1 (mem_zpowers _)
    have hmem' := mem_zpowers_iff_mem_range_orderOf.1 hmem
    rw [D.orderOf_c] at hmem'
    obtain ⟨k, hk, hkc⟩ := Finset.mem_image.1 hmem'
    have hk3 : k < 3 := Finset.mem_range.1 hk
    have hρ : h.setting.ρ (s * D.c * s⁻¹) = D.θ ^ k := by
      have e1 : s * D.c * s⁻¹ = D.c ^ k := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
        exact hkc.symm)
      rw [e1, map_pow, D.ρ_c]
    rw [map_mul, map_mul, map_inv, D.ρ_c, hinv] at hρ
    have hθ3 := D.θ_pow
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exfalso
      apply D.θ_ne
      rw [pow_zero] at hρ
      exact inv_eq_one.1 hρ
    · exfalso
      apply D.θ_ne
      rw [pow_one] at hρ
      have h2 : D.θ * D.θ = 1 := by
        calc D.θ * D.θ = D.θ⁻¹ * D.θ := by rw [hρ]
          _ = 1 := inv_mul_cancel _
      calc D.θ = D.θ ^ 3 * (D.θ * D.θ)⁻¹ := by group
        _ = 1 := by rw [hθ3, h2]; group
    · rw [← hkc]
      calc (D.c : G) ^ 2 = (D.c : G) ^ 3 * (D.c : G)⁻¹ := by group
        _ = (D.c : G)⁻¹ := by rw [hc3, one_mul]
  refine ⟨s, hsH, hs2, ?_⟩
  rintro _ ⟨k, rfl⟩
  change (s : G) * (D.c : G) ^ k * (s : G)⁻¹ = ((D.c : G) ^ k)⁻¹
  rw [← conj_zpow, hsc, inv_zpow]

end Inv

@[expose] noncomputable def toLoc49
    (hHat : HatM22SmallModules) (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) (hM : CFSG.CGT.T75P.M24SylowInput) (hJ : MathieuSmallIrr24) :
    Loc49 G z where
  toLoc48 := D.toLoc48 hHat hOut hTw hM hJ
  quasisimple := D.quasisimple_C hOut hTw hHat hM hJ
  inv_X := D.exists_inv_X hOut hTw hHat

end Data41

theorem stmt4_9_of
    (hHat : HatM22SmallModules) (hOut : KG82HatM22Out)
    (hTw : KG82HatM22Twelve) (hM : CFSG.CGT.T75P.M24SylowInput) (hJ : MathieuSmallIrr24) :
    Stmt4_9 := by
  intro G _ _ z h
  obtain ⟨D⟩ := h.nonempty_data41 hHat
  exact ⟨D.toLoc49 hHat hOut hTw hM hJ⟩

end CFSG.Quasithin.H13.AS91
