module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem le_normalizer_of_commutator_le {Y X : Subgroup G} (h : ⁅Y, X⁆ ≤ Y) :
    X ≤ normalizer (Y : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := fun x hx y hy => by
    have h1 : y⁻¹ * x * y⁻¹⁻¹ * x⁻¹ ∈ Y := h (commutator_mem_commutator (inv_mem hy) hx)
    have e : x * y * x⁻¹ = y * (y⁻¹ * x * y⁻¹⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem hy h1
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun hy => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this

theorem exists_cjSub_le_of_sylow [Finite G] (P : Sylow 2 G) {H Q : Subgroup G}
    (hPH : (P : Subgroup G) ≤ H) (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) :
    ∃ c ∈ H, cjSub c Q ≤ (P : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Q.subgroupOf H) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H R (P.subtype hPH)
  refine ⟨c, c.2, fun x hx => ?_⟩
  have hq := mem_cjSub.1 hx
  have hqR : (⟨(c : G)⁻¹ * x * c, hQH hq⟩ : H) ∈ (R : Subgroup H) :=
    hR (Subgroup.mem_subgroupOf.mpr hq)
  have hmem : MulAut.conj c (⟨(c : G)⁻¹ * x * c, hQH hq⟩ : H) ∈
      ((c • R : Sylow 2 H) : Subgroup H) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hqR
  rw [hc, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  simpa [mul_assoc] using hmem

theorem cjSub_commutator_eq (g : G) (X Y : Subgroup G) :
    cjSub g ⁅X, Y⁆ = ⁅cjSub g X, cjSub g Y⁆ :=
  Subgroup.map_commutator _ _ _

@[expose] def PairEq (Y X W : Subgroup G) : Prop :=
  Y ⊓ X = W ∧ ⁅Y, X⁆ = W ∧ Y ⊓ centralizer (X : Set G) = W ∧ X ⊓ centralizer (Y : Set G) = W

theorem PairEq.symm {Y X W : Subgroup G} (h : PairEq Y X W) : PairEq X Y W := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by rw [inf_comm]; exact h1, by rw [commutator_comm]; exact h2, h4, h3⟩

theorem PairEq.cjSub {Y X W : Subgroup G} (h : PairEq Y X W) (g : G) :
    PairEq (cjSub g Y) (cjSub g X) (cjSub g W) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← B2F.cjSub_inf, h1]
  · rw [← cjSub_commutator_eq, h2]
  · rw [← B2F.cjSub_centralizer, ← B2F.cjSub_inf, h3]
  · rw [← B2F.cjSub_centralizer, ← B2F.cjSub_inf, h4]

@[expose] def gen5 (Y X : Subgroup G) : Set G :=
  {y | y ∈ Y ∧ ∃ x ∈ X, x ∉ centralizer (Y : Set G) ∧ x * y = y * x}

@[expose] def v1Of (Y X : Subgroup G) : Subgroup G :=
  closure {c | ∃ y ∈ gen5 Y X, ∃ x ∈ gen5 X Y, c = y * x * y⁻¹ * x⁻¹}

theorem v1Of_le_comm (Y X : Subgroup G) : v1Of X Y ≤ v1Of Y X := by
  refine (closure_le _).2 ?_
  rintro c ⟨x, hx, y, hy, rfl⟩
  have h : y * x * y⁻¹ * x⁻¹ ∈ v1Of Y X := subset_closure ⟨y, hy, x, hx, rfl⟩
  have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
  rw [SetLike.mem_coe, e]
  exact inv_mem h

theorem v1Of_comm (Y X : Subgroup G) : v1Of X Y = v1Of Y X :=
  le_antisymm (v1Of_le_comm Y X) (v1Of_le_comm X Y)

theorem conj_mem_gen5 {Y X : Subgroup G} {g y : G} (hy : y ∈ gen5 (cjSub g Y) (cjSub g X)) :
    g⁻¹ * y * g ∈ gen5 Y X := by
  obtain ⟨hyY, x, hxX, hxC, hxy⟩ := hy
  refine ⟨mem_cjSub.1 hyY, g⁻¹ * x * g, mem_cjSub.1 hxX, fun hC => hxC ?_, ?_⟩
  · rw [← B2F.cjSub_centralizer, mem_cjSub]
    exact hC
  · calc g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
      _ = g⁻¹ * (y * x) * g := by rw [hxy]
      _ = g⁻¹ * y * g * (g⁻¹ * x * g) := by group

theorem v1Of_cjSub_le (g : G) (Y X : Subgroup G) :
    v1Of (cjSub g Y) (cjSub g X) ≤ cjSub g (v1Of Y X) := by
  refine (closure_le _).2 ?_
  rintro c ⟨y, hy, x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_cjSub]
  have e : g⁻¹ * (y * x * y⁻¹ * x⁻¹) * g =
      (g⁻¹ * y * g) * (g⁻¹ * x * g) * (g⁻¹ * y * g)⁻¹ * (g⁻¹ * x * g)⁻¹ := by group
  rw [e]
  exact subset_closure ⟨_, conj_mem_gen5 hy, _, conj_mem_gen5 hx, rfl⟩

theorem v1Of_cjSub (g : G) (Y X : Subgroup G) :
    v1Of (cjSub g Y) (cjSub g X) = cjSub g (v1Of Y X) := by
  refine le_antisymm (v1Of_cjSub_le g Y X) ?_
  have h := v1Of_cjSub_le g⁻¹ (cjSub g Y) (cjSub g X)
  rw [cjSub_inv_cjSub, cjSub_inv_cjSub] at h
  have := cjSub_mono (g := g) h
  rwa [cjSub_cjSub_inv] at this

end CFSG.Quasithin.H13.U3
