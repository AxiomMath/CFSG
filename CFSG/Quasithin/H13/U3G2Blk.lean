module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem mem_normalizer_centralizer_V {V : Subgroup G} {g : G}
    (hg : g ∈ normalizer (V : Set G)) : g ∈ normalizer (centralizer (V : Set G) : Set G) := by
  rw [mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (mem_normalizer_iff.1 (inv_mem hg) v).1 hv
      simpa using this
    have h1 := mem_centralizer_iff.1 hc _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * v := by group
  · intro hc
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : g * v * g⁻¹ ∈ V := (mem_normalizer_iff.1 hg v).1 hv
    have h1 := mem_centralizer_iff.1 hc _ hv'
    have h2 : g * (v * c) * g⁻¹ = g * (c * v) * g⁻¹ := by
      calc g * (v * c) * g⁻¹ = (g * v * g⁻¹) * (g * c * g⁻¹) := by group
        _ = (g * c * g⁻¹) * (g * v * g⁻¹) := h1
        _ = g * (c * v) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem commutator_le_right_of_le_normalizer {V L : Subgroup G}
    (hVL : V ≤ normalizer (L : Set G)) : ⁅V, L⁆ ≤ L := by
  rw [commutator_le]
  intro v hv l hl
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.1 (hVL hv) l).1 hl) (inv_mem hl)

theorem le_blockQ_of [Finite G] {V L : Subgroup G} (hV2 : IsPGroup 2 V)
    (hVL : V ≤ normalizer (L : Set G)) (hLV : L ≤ normalizer (V : Set G)) (hc : ⁅V, L⁆ = V) :
    V ≤ blockQ L := by
  have hle : V ≤ L := hc ▸ commutator_le_right_of_le_normalizer hVL
  exact C1.le_pCoreOf_of_normalized hle hLV hV2

theorem blockU_le_of_irr [Finite G] {L V : Subgroup G} (hL : IsShort2 L)
    (hLV : L ≤ normalizer (V : Set G)) (hVQ : V ≤ blockQ L) (hc : ⁅V, L⁆ = V)
    (hZ : V ⊓ centralizer (L : Set G) = ⊥) (hV1 : V ≠ ⊥) : blockU L ≤ V := by
  have hVU : V ≤ blockU L := by
    rw [← hc]
    exact commutator_mono hVQ le_rfl
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hW : V ⊔ blockZ L = blockU L := by
    rcases hL.2.2.2.2.2 (V ⊔ blockZ L) le_sup_right (sup_le hVU hZU)
        (fun l hl => C1.mem_normalizer_sup (hLV hl) (C1.mem_normalizer_blockZ (le_normalizer hl)))
      with h | h
    · exfalso
      apply hV1
      rw [eq_bot_iff, ← hZ]
      intro v hv
      have hvZ : v ∈ blockZ L := h ▸ mem_sup_left hv
      exact ⟨hv, (mem_inf.1 hvZ).2⟩
    · exact h
  let K : Subgroup G :=
    { carrier := {g | g ∈ normalizer (V : Set G) ∧ ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ V}
      one_mem' := ⟨one_mem _, fun l _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, hal⟩ ⟨hb, hbl⟩
        refine ⟨mul_mem ha hb, fun l hl => ?_⟩
        have e : a * b * l * (a * b)⁻¹ * l⁻¹ =
            a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ * (a * l * a⁻¹ * l⁻¹) := by group
        rw [e]
        exact mul_mem ((mem_normalizer_iff.1 ha _).1 (hbl l hl)) (hal l hl)
      inv_mem' := by
        rintro a ⟨ha, hal⟩
        refine ⟨inv_mem ha, fun l hl => ?_⟩
        have e : a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ = a⁻¹ * (a * l * a⁻¹ * l⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact (mem_normalizer_iff.1 (inv_mem ha) _).1 (inv_mem (hal l hl)) }
  have hVK : V ≤ K := fun v hv => by
    refine ⟨le_normalizer hv, fun l hl => ?_⟩
    have e : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
    rw [e]
    exact mul_mem hv ((mem_normalizer_iff.1 (hLV hl) _).1 (inv_mem hv))
  have hZK : blockZ L ≤ K := fun z hz => by
    have hzL : z ∈ L := C1.blockQ_le L (C1.blockU_le_blockQ hL (mem_inf.1 hz).1)
    refine ⟨hLV hzL, fun l hl => ?_⟩
    have hzl : z * l = l * z := (mem_centralizer_iff.1 (mem_inf.1 hz).2 l hl).symm
    have e : z * l * z⁻¹ * l⁻¹ = 1 := by
      rw [hzl]
      group
    rw [e]
    exact one_mem _
  have hUK : blockU L ≤ K := hW ▸ sup_le hVK hZK
  rw [← C1.commutator_blockU hL, commutator_le]
  intro u hu l hl
  exact (hUK hu).2 l hl

theorem commutator_mem_of_centralizer [Finite G] {L V : Subgroup G} (hL : IsShort2 L)
    (hLV : L ≤ normalizer (V : Set G)) (hUV : blockU L ≤ V)
    (hCL : L ⊓ centralizer (V : Set G) ≤ blockQ L) {y : G}
    (hyL : y ∈ normalizer (L : Set G)) (hyV : y ∈ centralizer (V : Set G)) :
    ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ V := by
  have hQ : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ blockQ L := by
    intro l hl
    refine hCL (mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hyL l).1 hl) (inv_mem hl), ?_⟩)
    have h1 : l * y⁻¹ * l⁻¹ ∈ centralizer (V : Set G) :=
      (mem_normalizer_iff.1 (mem_normalizer_centralizer_V (hLV hl)) _).1 (inv_mem hyV)
    have e : y * l * y⁻¹ * l⁻¹ = y * (l * y⁻¹ * l⁻¹) := by group
    rw [e]
    exact mul_mem hyV h1
  intro l hl
  exact hUV (C1.commutator_mem_blockU_of_mem_blockQ hL hQ l hl)

theorem normalizer_le_of_isUniqueM [Finite G] {X M C : Subgroup G} (hU : IsUniqueM X M)
    (hC2 : IsPGroup 2 C) (hC1 : C ≠ ⊥) (hXC : X ≤ normalizer (C : Set G)) :
    normalizer (C : Set G) ≤ M := by
  have hCO : C ≤ pCoreOf 2 (normalizer (C : Set G)) :=
    C1.le_pCoreOf_of_normalized le_normalizer le_rfl hC2
  have hO : pCoreOf 2 (normalizer (C : Set G)) ≠ ⊥ := fun h => hC1 (le_bot_iff.1 (h ▸ hCO))
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have h1 : M' = M := hU.2 M' ⟨hM'.1, hXC.trans hM'.2⟩
  exact h1 ▸ hM'.2

theorem card_inf_centralizer_cjSub [Finite G] (V : Subgroup G) (g : G) :
    Nat.card ↥(V ⊓ centralizer (cjSub g V : Set G)) =
      Nat.card ↥(cjSub g⁻¹ V ⊓ centralizer (V : Set G)) := by
  have key : ∀ (h : G) (y : G), y ∈ V ⊓ centralizer (cjSub h V : Set G) →
      h⁻¹ * y * h ∈ cjSub h⁻¹ V ⊓ centralizer (V : Set G) := by
    intro h y ⟨hyV, hyC⟩
    refine ⟨mem_cjSub.2 (by simpa [mul_assoc] using hyV), mem_centralizer_iff.2 fun v hv => ?_⟩
    have hv' : h * v * h⁻¹ ∈ cjSub h V := mem_cjSub.2 (by simpa [mul_assoc] using hv)
    have h1 := mem_centralizer_iff.1 hyC _ hv'
    calc v * (h⁻¹ * y * h) = h⁻¹ * ((h * v * h⁻¹) * y) * h := by group
      _ = h⁻¹ * (y * (h * v * h⁻¹)) * h := by rw [h1]
      _ = h⁻¹ * y * h * v := by group
  apply le_antisymm
  · have hle : (V ⊓ centralizer (cjSub g V : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ≤
        cjSub g⁻¹ V ⊓ centralizer (V : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      have := key g y hy
      simpa [mul_assoc] using this
    calc Nat.card ↥(V ⊓ centralizer (cjSub g V : Set G))
        = Nat.card ↥((V ⊓ centralizer (cjSub g V : Set G)).map
            (MulAut.conj g⁻¹).toMonoidHom) :=
          (card_map_of_injective (MulAut.conj g⁻¹).injective).symm
      _ ≤ _ := card_le_of_le hle
  · have hle : (cjSub g⁻¹ V ⊓ centralizer (V : Set G)).map (MulAut.conj g).toMonoidHom ≤
        V ⊓ centralizer (cjSub g V : Set G) := by
      rintro _ ⟨y, ⟨hyV, hyC⟩, rfl⟩
      have hyV' : g * y * g⁻¹ ∈ V := by simpa [mul_assoc] using mem_cjSub.1 hyV
      refine ⟨by simpa using hyV', mem_centralizer_iff.2 fun w hw => ?_⟩
      have hw' : g⁻¹ * w * g ∈ V := mem_cjSub.1 hw
      have h1 := mem_centralizer_iff.1 hyC _ hw'
      have : w * (g * y * g⁻¹) = g * y * g⁻¹ * w := by
        calc w * (g * y * g⁻¹) = g * ((g⁻¹ * w * g) * y) * g⁻¹ := by group
          _ = g * (y * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
          _ = g * y * g⁻¹ * w := by group
      simpa using this
    calc Nat.card ↥(cjSub g⁻¹ V ⊓ centralizer (V : Set G))
        = Nat.card ↥((cjSub g⁻¹ V ⊓ centralizer (V : Set G)).map
            (MulAut.conj g).toMonoidHom) :=
          (card_map_of_injective (MulAut.conj g).injective).symm
      _ ≤ _ := card_le_of_le hle

end CFSG.Quasithin.H13.U3
