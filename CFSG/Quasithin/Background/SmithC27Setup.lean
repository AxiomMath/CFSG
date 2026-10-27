module

public import CFSG.Quasithin.Background.SmithC27Defs
public import CFSG.Quasithin.Background.C2PushThree

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

section V

variable {G : Type} [Group G]

theorem isElemAbelian_omegaOneCenterOf (Y : Subgroup G) : IsElemAbelian 2 (omegaOneCenterOf Y) :=
  ⟨⟨⟨fun x y => Subtype.ext (A4.mul_comm_of_mem_omegaOneCenterOf x.2 y.2)⟩⟩,
    fun _ hx => A4.sq_eq_one_of_mem_omegaOneCenterOf hx⟩

theorem omegaOneCenterOf_pCoreOf_le (X : Subgroup G) : omegaOneCenterOf (pCoreOf 2 X) ≤ X :=
  (A4.omegaOneCenterOf_le _).trans (pCoreOf_le 2 X)

theorem le_normalizer_omegaOneCenterOf_pCoreOf (X : Subgroup G) :
    X ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 X) : Set G) :=
  (le_normalizer_pCoreOf 2 X).trans (A4.normalizer_le_normalizer_omegaOneCenterOf _)

theorem pCoreOf_le_centralizer_omegaOneCenterOf (X : Subgroup G) :
    pCoreOf 2 X ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G) := by
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp
    (A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ hv)) q hq).symm

theorem le_normalizer_centralizer_omegaOneCenterOf_pCoreOf (X : Subgroup G) :
    X ≤ Subgroup.normalizer
      (Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G) : Set G) := by
  intro x hx
  have hxV := le_normalizer_omegaOneCenterOf_pCoreOf X hx
  have key : ∀ g ∈ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 X) : Set G),
      ∀ c ∈ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G),
        g * c * g⁻¹ ∈ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 X) : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : g⁻¹ * v * g ∈ omegaOneCenterOf (pCoreOf 2 X) :=
      (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
    have h1 := hc _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * v := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key x hxV c hc, fun hc => ?_⟩
  have := key x⁻¹ (Subgroup.inv_mem _ hxV) _ hc
  simpa [mul_assoc] using this

end V

namespace Hyp27

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G}

theorem K_le (h : Hyp27 H R M K) : K ≤ H := le_of_mem_cComp h.comp

theorem R_le (h : Hyp27 H R M K) : R ≤ H := h.hyp.radical.1

theorem isPGroup (h : Hyp27 H R M K) : IsPGroup 2 R := h.hyp.radical.isPGroup

theorem R_ne_bot (h : Hyp27 H R M K) : R ≠ ⊥ := h.hyp.radical.2.1

theorem sup_le (h : Hyp27 H R M K) : K ⊔ R ≤ H := _root_.sup_le h.K_le h.R_le

theorem perfect (h : Hyp27 H R M K) : ⁅K, K⁆ = K := perfect_of_mem_cComp h.comp

theorem inf_normalizer_le (h : Hyp27 H R M K) : H ⊓ Subgroup.normalizer (R : Set G) ≤ M :=
  (inf_normalizer_le_cgsIn h.R_ne_bot).trans h.hyp.cgs

theorem R_le_M (h : Hyp27 H R M K) : R ≤ M := fun _ hx =>
  h.inf_normalizer_le ⟨h.R_le hx, Subgroup.le_normalizer hx⟩

theorem sup_le_normalizer (h : Hyp27 H R M K) : K ⊔ R ≤ Subgroup.normalizer (K : Set G) :=
  _root_.sup_le Subgroup.le_normalizer h.norm

theorem coe_sup (h : Hyp27 H R M K) :
    ((K ⊔ R : Subgroup G) : Set G) = (K : Set G) * (R : Set G) :=
  Subgroup.coe_mul_of_right_le_normalizer_left K R h.norm

theorem exists_pow_mem (h : Hyp27 H R M K) {x : G} (hx : x ∈ K ⊔ R) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ K := by
  have hx' : x ∈ ((K ⊔ R : Subgroup G) : Set G) := hx
  rw [h.coe_sup] at hx'
  obtain ⟨y, hy, r, hr, rfl⟩ := hx'
  obtain ⟨j, hj⟩ := h.isPGroup ⟨r, hr⟩
  have hj' : r ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (h.norm hr) (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hy'⟩

theorem isTwoRadicalIn_sup (h : Hyp27 H R M K) : IsTwoRadicalIn (K ⊔ R) R :=
  C2Push.isTwoRadicalIn_sup_of_le_normalizer h.hyp.radical h.comp h.quasi h.norm

theorem pCoreOf_sup_le (h : Hyp27 H R M K) : pCoreOf 2 (K ⊔ R) ≤ R :=
  c2_1_pCore_le h.isTwoRadicalIn_sup

theorem charTwo_sup (h : Hyp27 H R M K) : CharTwo (K ⊔ R) :=
  A4.charTwo_sup h.charTwo h.norm h.isPGroup

theorem mem_cComp_sup (h : Hyp27 H R M K) : K ∈ cComp (K ⊔ R) :=
  cComp_mem_of_le h.comp le_sup_left h.sup_le

theorem isSylowTwoOf_conjClosure (h : Hyp27 H R M K) :
    IsSylowTwoOf R (conjClosure R (M ⊓ (K ⊔ R))) :=
  A4.isSylowTwoOf_mono h.hyp.sylow (le_conjClosure R _) (conjClosure_mono le_rfl inf_le_left)

theorem hypC23_sup (h : Hyp27 H R M K) : HypC23 (K ⊔ R) R (M ⊓ (K ⊔ R)) :=
  ⟨h.hyp.sqtk.mono h.sup_le, h.isTwoRadicalIn_sup, inf_le_right,
    le_inf ((C2Nine.cgsIn_mono_left h.sup_le R).trans h.hyp.cgs) (cgsIn_le _ R),
    h.isSylowTwoOf_conjClosure⟩

theorem omegaOneCenterOf_le (h : Hyp27 H R M K) :
    omegaOneCenterOf R ≤ omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) := by
  refine (Subgroup.closure_le _).mpr fun z hz => ?_
  obtain ⟨hzc, hz2⟩ := hz
  have hzR : z ∈ R := hzc.1
  have hzCP : z ∈ Subgroup.centralizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.pCoreOf_sup_le) hzc.2
  have hzP : z ∈ pCoreOf 2 (K ⊔ R) := h.charTwo_sup ⟨Subgroup.mem_sup_right hzR, hzCP⟩
  exact Subgroup.subset_closure ⟨⟨hzP, hzCP⟩, hz2⟩

theorem not_le_centralizer (h : Hyp27 H R M K) :
    ¬ K ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) := by
  intro hKV
  apply h.not_le
  have hZRne : omegaOneCenterOf R ≠ ⊥ :=
    CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot h.isPGroup h.R_ne_bot
  have hKZ : K ≤ Subgroup.centralizer (omegaOneCenterOf R : Set G) :=
    hKV.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.omegaOneCenterOf_le))
  intro x hx
  refine h.hyp.cgs ?_
  exact inf_normalizer_le_cgsIn_of_char (A4.omegaOneCenterOf_le R) hZRne
    (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R)
    ⟨h.K_le hx, Subgroup.centralizer_le_normalizer _ (hKZ hx)⟩

end Hyp27

end CFSG.Quasithin.SmithC27
