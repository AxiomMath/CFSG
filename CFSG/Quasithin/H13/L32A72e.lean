module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32ARuOne
public import CFSG.Quasithin.H13.L32AStRec
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem exists_sl3_e1 : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    ∃ A : H6.Γ, A • (![1, 0, 0] : Fin 3 → ZMod 2) = v := by
  decide +kernel

theorem borel_pow_four : ∀ g : H6.Γ, g ∈ H6.borel → g ^ 4 = 1 := by
  decide +kernel

@[expose] noncomputable def theta1 {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (e : ↥V ≃* Multiplicative (Fin 3 → ZMod 2))
    (A : H6.Γ) : ↥L →* H6.Γ :=
  H6.graph.toMonoidHom.comp ((MulAut.conj A⁻¹).toMonoidHom.comp (repV hLV e))

section Theta

variable {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
  (e : ↥V ≃* Multiplicative (Fin 3 → ZMod 2)) (A : H6.Γ)

theorem theta1_apply (l : ↥L) : theta1 hLV e A l = H6.graph (A⁻¹ * repV hLV e l * A) := by
  rw [theta1, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]

theorem theta1_surjective (hs : Function.Surjective (repV hLV e)) :
    Function.Surjective (theta1 hLV e A) := by
  intro g
  obtain ⟨l, hl⟩ := hs (A * H6.graph.symm g * A⁻¹)
  refine ⟨l, ?_⟩
  rw [theta1_apply, hl, show A⁻¹ * (A * H6.graph.symm g * A⁻¹) * A = H6.graph.symm g by group,
    MulEquiv.apply_symm_apply]

theorem theta1_eq_one_iff (l : ↥L) :
    theta1 hLV e A l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [theta1_apply, map_eq_one_iff _ H6.graph.injective]
  have hk : repV hLV e l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
    rw [← MonoidHom.mem_ker, repV_ker, Subgroup.mem_subgroupOf]
  rw [← hk]
  constructor
  · intro h
    calc repV hLV e l = A * (A⁻¹ * repV hLV e l * A) * A⁻¹ := by group
      _ = 1 := by rw [h]; group
  · intro h
    rw [h]
    group

theorem theta1_mem_Ll_iff {z : G} (hz : z ∈ V)
    (hA : A • (![1, 0, 0] : Fin 3 → ZMod 2) = Multiplicative.toAdd (e ⟨z, hz⟩)) (l : ↥L) :
    theta1 hLV e A l ∈ H6.Ll ↔ (l : G) * z * (l : G)⁻¹ = z := by
  have hlz : (l : G) * z * (l : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hLV l.2) z).mp hz
  have hrep := repV_mulVec hLV e l ⟨z, hz⟩ ⟨_, hlz⟩ rfl
  have key : repV hLV e l • Multiplicative.toAdd (e ⟨z, hz⟩) =
      Multiplicative.toAdd (e ⟨_, hlz⟩) := by
    rw [hrep]
    rfl
  rw [theta1_apply, H6.graph_mem_Ll_iff, H6.Lp, MulAction.mem_stabilizer_iff, mul_smul,
    mul_smul, hA, inv_smul_eq_iff, hA, key]
  constructor
  · intro h
    exact congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective h))
  · intro h
    have : (⟨(l : G) * z * (l : G)⁻¹, hlz⟩ : ↥V) = ⟨z, hz⟩ := Subtype.ext h
    rw [this]

end Theta

theorem card_inf_centralizer_eq_two [Finite G] {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (e : ↥V ≃* Multiplicative (Fin 3 → ZMod 2))
    {x : G} (hxL : x ∈ L) (hx3 : x ^ 3 = 1) (hxV : x ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = 2 := by
  set g := repV hLV e ⟨x, hxL⟩ with hg
  have hg3 : g ^ 3 = 1 := by
    rw [hg, ← map_pow, show (⟨x, hxL⟩ : ↥L) ^ 3 = 1 from Subtype.ext (by simpa using hx3),
      map_one]
  have hg1 : g ≠ 1 := fun h => hxV (by
    have h1 : (⟨x, hxL⟩ : ↥L) ∈ (repV hLV e).ker := h
    rw [repV_ker, Subgroup.mem_subgroupOf] at h1
    exact h1)
  rw [← H6.card_fix_v3 g hg3 hg1]
  have hcx : ∀ w : G, w ∈ Subgroup.centralizer ({x} : Set G) ↔ x * w * x⁻¹ = w := fun w => by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have key : ∀ v : ↥V, x * (v : G) * x⁻¹ = v ↔
      H6.ρV g (Multiplicative.toAdd (e v)) = Multiplicative.toAdd (e v) := fun v => by
    have hxv : x * (v : G) * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hxL) v).mp v.2
    have hrep := repV_mulVec hLV e ⟨x, hxL⟩ v ⟨_, hxv⟩ rfl
    have h1 : H6.ρV g (Multiplicative.toAdd (e v)) = Multiplicative.toAdd (e ⟨_, hxv⟩) := by
      rw [hrep]
      rfl
    rw [h1]
    constructor
    · intro h
      have : (⟨x * (v : G) * x⁻¹, hxv⟩ : ↥V) = v := Subtype.ext h
      rw [this]
    · intro h
      exact congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective h))
  refine Nat.card_congr
    { toFun := fun w => ⟨Multiplicative.toAdd (e ⟨w, (Subgroup.mem_inf.mp w.2).1⟩),
        (key _).mp ((hcx _).mp (Subgroup.mem_inf.mp w.2).2)⟩
      invFun := fun y => ⟨e.symm (Multiplicative.ofAdd y.1), Subgroup.mem_inf.mpr
        ⟨(e.symm (Multiplicative.ofAdd y.1)).2, (hcx _).mpr ((key _).mpr (by
          rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
          exact y.2))⟩⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }

theorem conj_fix_of_comm_mem {V : Subgroup G} {x s : G}
    (hx3 : x ^ 3 = 1) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ a ∈ V, a * a = 1)
    (hv : x * s * x⁻¹ * s⁻¹ ∈ V) :
    x * ((x * (x * s * x⁻¹ * s⁻¹) * x⁻¹) * s) * x⁻¹ = (x * (x * s * x⁻¹ * s⁻¹) * x⁻¹) * s := by
  have hv' := hv
  generalize hvd : x * s * x⁻¹ * s⁻¹ = v at hv' ⊢
  have hs : x * s * x⁻¹ = v * s := by rw [← hvd]; group
  have ha : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv'
  have h3 : x * (x * (x * s * x⁻¹) * x⁻¹) * x⁻¹ = s := by
    have : x * (x * (x * s * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * s * (x ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [this, hx3]
    group
  have e2 : x * (v * s) * x⁻¹ = (x * v * x⁻¹) * (v * s) := by
    calc x * (v * s) * x⁻¹ = (x * v * x⁻¹) * (x * s * x⁻¹) := by group
      _ = (x * v * x⁻¹) * (v * s) := by rw [hs]
  have e1 : x * (x * (x * s * x⁻¹) * x⁻¹) * x⁻¹ =
      (x * (x * v * x⁻¹) * x⁻¹) * (x * v * x⁻¹) * v * s := by
    calc x * (x * (x * s * x⁻¹) * x⁻¹) * x⁻¹ = x * (x * (v * s) * x⁻¹) * x⁻¹ := by rw [hs]
      _ = x * ((x * v * x⁻¹) * (v * s)) * x⁻¹ := by rw [e2]
      _ = (x * (x * v * x⁻¹) * x⁻¹) * (x * (v * s) * x⁻¹) := by group
      _ = (x * (x * v * x⁻¹) * x⁻¹) * ((x * v * x⁻¹) * (v * s)) := by rw [e2]
      _ = (x * (x * v * x⁻¹) * x⁻¹) * (x * v * x⁻¹) * v * s := by group
  rw [e1] at h3
  have hbav : (x * (x * v * x⁻¹) * x⁻¹) * (x * v * x⁻¹) * v = 1 := by
    calc (x * (x * v * x⁻¹) * x⁻¹) * (x * v * x⁻¹) * v =
        (x * (x * v * x⁻¹) * x⁻¹) * (x * v * x⁻¹) * v * s * s⁻¹ := by group
      _ = 1 := by rw [h3, mul_inv_cancel]
  generalize hav : x * v * x⁻¹ = a at ha hbav ⊢
  generalize hbv : x * a * x⁻¹ = b at hbav ⊢
  have hcomm : a * v = v * a := hVc a ha v hv'
  have ha2 : a * a = 1 := hV2 a ha
  have hbv' : b * v = a := by
    have h1 : b * v * a = 1 := by
      calc b * v * a = b * (v * a) := mul_assoc _ _ _
        _ = b * (a * v) := by rw [hcomm]
        _ = 1 := by rw [← mul_assoc]; exact hbav
    calc b * v = b * v * a * a := by rw [mul_assoc (b * v) a a, ha2, mul_one]
      _ = a := by rw [h1, one_mul]
  calc x * (a * s) * x⁻¹ = (x * a * x⁻¹) * (x * s * x⁻¹) := by group
    _ = b * (v * s) := by rw [hbv, hs]
    _ = (b * v) * s := (mul_assoc _ _ _).symm
    _ = a * s := by rw [hbv']

end CFSG.Quasithin.H13.L32A
