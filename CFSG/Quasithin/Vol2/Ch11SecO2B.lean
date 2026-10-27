module

public import CFSG.Quasithin.Vol2.Ch11SecO2A
public import CFSG.Quasithin.Vol2.Ch11SecFFacts
public import CFSG.Quasithin.Vol2.Ch11SecFFacts2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp)
open scoped IsMulCommutative commutatorElement

namespace O2

variable {G : Type} [Group G]

theorem commutatorElement_eq_inv {V : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ⁅(v : G), x⁆ = ((SecA.conjV V x hx v * v⁻¹ : ↥V) : G)⁻¹ := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, SecA.conjV_apply_coe, commutatorElement_def]
  group

theorem mul_comm_of_commutator_eq_bot {U P : Subgroup G} (h : ⁅U, P⁆ = ⊥) {p : G} (hp : p ∈ P) :
    ∀ u ∈ U, p * u = u * p := fun u hu => by
  have h1 : ⁅u, p⁆ ∈ ⁅U, P⁆ := Subgroup.commutator_mem_commutator hu hp
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

end O2

open O2 in
theorem factSp4Z_holds : FactSp4Z := by
  intro G _ _ T L I n V₁ V₃ hS hk hV₁ hV₃ P hP hPV₃
  have := SecO1.isMulCommutative hS
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, -, hV₁g, -, hV₃g⟩ := exists_coord hS hk
  rw [Subgroup.commutator_le]
  intro v hv p hp
  obtain ⟨c, hc⟩ := exists_trv_of_r1 hS hK hπ hf hV₁ (hV₁g V₁ hV₁) (hV₃g V₃ hV₃) (hP hp)
    (mul_comm_of_commutator_eq_bot hPV₃ hp)
  rw [commutatorElement_eq_inv (r1_le hS hV₁ (hP hp)).1.1.1 ⟨v, hv⟩]
  refine V₁.inv_mem ((mem_v1_iff (hV₁g V₁ hV₁) _).mpr
    ⟨c * Matrix.toBilin' (spJ K) (f ⟨v, hv⟩) (mat 2 K g *ᵥ vec4 1 0 0 0), ?_⟩)
  rw [hf.map_mul_inv, hc, hf.act4, SecB.K7.trv_mulVec, add_sub_cancel_left]

open O2 in
theorem factSp4ZCent_holds : FactSp4ZCent := by
  intro G _ _ T L I n V₁ V₃ hS hk hV₁ hV₃ P hP hPV₃
  have := SecO1.isMulCommutative hS
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, -, hV₁g, -, hV₃g⟩ := exists_coord hS hk
  rw [Subgroup.commutator_le]
  intro p hp l hl
  obtain ⟨c, hc⟩ := exists_trv_of_r1 hS hK hπ hf hV₁ (hV₁g V₁ hV₁) (hV₃g V₃ hV₃) (hP hp)
    (mul_comm_of_commutator_eq_bot hPV₃ hp)
  obtain ⟨δ, hδ, hδy⟩ := exists_act_l1 hS hK hπ hf hV₁ (hV₁g V₁ hV₁) hl
  have hpV := (r1_le hS hV₁ (hP hp)).1.1.1
  have hlV := l1_le_normalizer hS V₁ hl
  have hab : SecA.conjV (fsuV T I) p hpV * SecA.conjV (fsuV T I) l hlV =
      SecA.conjV (fsuV T I) l hlV * SecA.conjV (fsuV T I) p hpV := by
    rw [hc, hδ, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      SecB.K7.comm_trv hδy c]
  have hpl : ∀ w : ↥(fsuV T I),
      p * (l * (w : G) * l⁻¹) * p⁻¹ = l * (p * (w : G) * p⁻¹) * l⁻¹ := by
    intro w
    have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ w : ↥(fsuV T I)) : G)) hab
    simpa only [MulAut.mul_apply, SecA.conjV_apply_coe] using h1
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : l⁻¹ * v * l⁻¹⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hlV) v).mp hv
  have h2 : p⁻¹ * (l⁻¹ * v * l⁻¹⁻¹) * p⁻¹⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hpV) _).mp h1
  have hw : p⁻¹ * l⁻¹ * v * l * p ∈ fsuV T I := by simpa only [inv_inv, mul_assoc] using h2
  have h3 := hpl ⟨_, hw⟩
  have h4 : l * (p * (p⁻¹ * l⁻¹ * v * l * p) * p⁻¹) * l⁻¹ = v := by group
  rw [h4] at h3
  calc v * (p * l * p⁻¹ * l⁻¹)
      = p * (l * (p⁻¹ * l⁻¹ * v * l * p) * l⁻¹) * p⁻¹ * (p * l * p⁻¹ * l⁻¹) := by rw [h3]
    _ = p * l * p⁻¹ * l⁻¹ * v := by group

open O2 in
theorem factSp4VL1_holds : FactSp4VL1 := by
  intro G _ _ T L I n V₁ V₃ hS hk hV₁ hV₃
  have := SecO1.isMulCommutative hS
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, -, hV₁g, -, hV₃g⟩ := exists_coord hS hk
  rw [Subgroup.commutator_le]
  intro v hv l hl
  obtain ⟨δ, hδ, hδy⟩ := exists_act_l1 hS hK hπ hf hV₁ (hV₁g V₁ hV₁) hl
  rw [commutatorElement_eq_inv (l1_le_normalizer hS V₁ hl) ⟨v, hv⟩]
  refine V₃.inv_mem ((mem_v3_iff (hV₃g V₃ hV₃) _).mpr ?_)
  rw [hf.map_mul_inv, hδ, hf.act4, map_sub, LinearMap.sub_apply, sub_eq_zero]
  conv_lhs => rw [← hδy]
  exact spB_mat δ _ _

open O2 in
theorem factSp4V3R1_holds : FactSp4V3R1 := by
  intro G _ _ T L I n V₁ V₃ hS hk hV₁ hV₃ hbot
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, -, hV₁g, -, hV₃g⟩ := exists_coord hS hk
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have : Finite (MulAut ↥(fsuV T I)) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨y, hy, hyq⟩ := KA.exists_pCore_of_mem hf g (KA.qSp_mem_pCoreOf hK4 0 1)
  have hmem : psiSp π g (qSp 0 1 0) ∈ autOn (pCoreOf 2 (LOf L V₁)) (fsuV T I) := by
    rw [← pCoreOf_p1_eq hS hV₁, hV₁g V₁ hV₁, ← hyq]
    exact (KA.mem_pCoreOf_iff' _ y).mpr hy
  obtain ⟨r, hr, hrV, hreq⟩ := SecA.mem_autOn_iff.mp hmem
  obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 0 0 0 1)
  have hu₀V₃ : (u₀ : G) ∈ V₃ := by
    rw [mem_v3_iff (hV₃g V₃ hV₃), hu₀, spB_mat, toBilin'_spJ_apply]
    simp [vec4, Fin.sum_univ_two]
  have h1 := mul_comm_of_commutator_eq_bot hbot hr (u₀ : G) hu₀V₃
  have h2 : SecA.conjV (fsuV T I) r hrV u₀ = u₀ :=
    Subtype.ext (by rw [SecA.conjV_apply_coe, h1, mul_inv_cancel_right])
  rw [← hreq] at h2
  have h3 := congrArg f h2
  rw [psiSp_apply, hf.act4, KA.gconj_mulVec_sp, hu₀, mat_inv_mulVec, qSp_mulVec] at h3
  have h4 := congrArg (fun x => mat 2 K g⁻¹ *ᵥ x) h3
  simp only [mat_inv_mulVec] at h4
  have h5 := congrFun h4 (.inl 0)
  simp [vec4] at h5

end CFSG.Quasithin.Vol2.Ch11.SecF
