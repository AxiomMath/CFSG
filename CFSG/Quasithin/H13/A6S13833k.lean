module

public import CFSG.Quasithin.H13.A6S13833j

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

@[expose] def cvrE (i j : Fin 6) : Fin 6 → ZMod 2 := Pi.single i 1 + Pi.single j 1

@[expose] def cvrW2 : List (Fin 6 → ZMod 2) :=
  [cvrE 0 1, cvrE 0 2, cvrE 0 3, cvrE 0 4, cvrE 0 5, cvrE 1 2, cvrE 1 3, cvrE 1 4, cvrE 1 5,
    cvrE 2 3, cvrE 2 4, cvrE 2 5, cvrE 3 4, cvrE 3 5, cvrE 4 5]

@[expose] def cvrTri : List (Perm (Fin 6)) := [swap 0 1 * swap 1 2, swap 3 4 * swap 4 5]

@[expose] def cvrPair : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 1 2, swap 0 1 * swap 1 3, swap 0 1 * swap 1 4, swap 0 1 * swap 1 5,
    swap 0 2 * swap 2 1, swap 0 2 * swap 2 3, swap 0 2 * swap 2 4, swap 0 2 * swap 2 5,
    swap 0 2 * swap 1 3, swap 0 2 * swap 1 4, swap 0 2 * swap 1 5, swap 0 3 * swap 1 4,
    swap 0 3 * swap 1 5, swap 0 4 * swap 1 5]

@[expose] def cvrSpread : List (Perm (Fin 6)) :=
  [1, swap 0 2 * swap 2 1, swap 0 3 * swap 3 1, swap 0 4 * swap 4 1, swap 0 5 * swap 5 1]

theorem cvr_even : ∀ σ ∈ cvrTri ++ cvrPair ++ cvrSpread, Perm.sign σ = 1 := by
  decide +kernel

theorem cvr_tri : ∀ f : Fin 6 → ZMod 2, ∑ i, f i = 0 → f ≠ 0 → f ≠ onesV →
    ∃ σ ∈ cvrTri, f + vp σ f ∈ cvrW2 := by
  decide +kernel

theorem cvr_pair : ∀ g ∈ cvrW2, ∃ τ ∈ cvrPair, vp τ g = cvrE 0 1 := by
  decide +kernel

theorem cvr_spread : ∀ j : Fin 6, j ≠ 0 → ∃ τ ∈ cvrSpread, vp τ (cvrE 0 1) = cvrE 0 j := by
  decide +kernel

theorem cvr_sum : ∀ y : Fin 6 → ZMod 2, ∑ i, y i = 0 →
    y = y 1 • cvrE 0 1 + y 2 • cvrE 0 2 + y 3 • cvrE 0 3 + y 4 • cvrE 0 4 + y 5 • cvrE 0 5 := by
  decide +kernel

theorem cvr_zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem cvr_closure {P : (Fin 6 → ZMod 2) → Prop} (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hperm : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → ∀ a, P a → P (vp σ a))
    {f : Fin 6 → ZMod 2} (hf : P f) (hfs : ∑ i, f i = 0) (hf0 : f ≠ 0) (hf1 : f ≠ onesV)
    {y : Fin 6 → ZMod 2} (hy : ∑ i, y i = 0) : P y := by
  obtain ⟨σ, hσ, hg⟩ := cvr_tri f hfs hf0 hf1
  have hσs : Perm.sign σ = 1 :=
    cvr_even σ (List.mem_append_left _ (List.mem_append_left _ hσ))
  have hPg : P (f + vp σ f) := hadd _ _ hf (hperm σ hσs f hf)
  obtain ⟨τ, hτ, hτg⟩ := cvr_pair _ hg
  have hτs : Perm.sign τ = 1 :=
    cvr_even τ (List.mem_append_left _ (List.mem_append_right _ hτ))
  have h01 : P (cvrE 0 1) := hτg ▸ hperm τ hτs _ hPg
  have hj : ∀ j : Fin 6, j ≠ 0 → P (cvrE 0 j) := by
    intro j hj
    obtain ⟨κ, hκ, hκe⟩ := cvr_spread j hj
    have hκs : Perm.sign κ = 1 := cvr_even κ (List.mem_append_right _ hκ)
    exact hκe ▸ hperm κ hκs _ h01
  have hsm : ∀ (c : ZMod 2) a, P a → P (c • a) := by
    intro c a ha
    rcases cvr_zmod2_cases c with rfl | rfl
    · rw [zero_smul]
      exact h0
    · rw [one_smul]
      exact ha
  rw [cvr_sum y hy]
  refine hadd _ _ (hadd _ _ (hadd _ _ (hadd _ _ ?_ ?_) ?_) ?_) ?_ <;>
    exact hsm _ _ (hj _ (by decide))

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem centralizer_QH_le_U1c (h13314 : Stmt13_3_14) {ρ : ↥S.G1 →* Perm (Fin 6)}
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, ρ k = σ)
    {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
    (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
    (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
      Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u))) :
    conjClosure S.V3 S.G1 ⊓ Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) ≤ S.U1c β := by
  have hV1C : ∀ x ∈ fsuV1 T V, x ∈ Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    rcases (S.mem_V1_iff).1 hx with rfl | rfl
    · simp
    · exact S.mul_z_comm (pCoreOf_le 2 _ hq)
  let P : (Fin 6 → ZMod 2) → Prop := fun f => ∃ w : ↥(conjClosure S.V3 S.G1),
    (w : G) ∈ Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) ∧
      ((Multiplicative.toAdd (β w) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) = f
  have h0 : P 0 := ⟨1, Subgroup.one_mem _, by simp⟩
  have hadd : ∀ a b, P a → P b → P (a + b) := by
    rintro a b ⟨w₁, hw₁, rfl⟩ ⟨w₂, hw₂, rfl⟩
    exact ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, by simp⟩
  have hperm : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → ∀ a, P a → P (vp σ a) := by
    rintro σ hσ a ⟨w, hw, rfl⟩
    obtain ⟨k, hk⟩ := honto σ (Equiv.Perm.mem_alternatingGroup.2 hσ)
    have hkw : (k : G) * w * (k : G)⁻¹ ∈ conjClosure S.V3 S.G1 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 k.2) w).mp w.2
    refine ⟨⟨_, hkw⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_centralizer (le_normalizer_pCoreOf 2 S.G1 k.2)) w).mp hw
    · rw [hβe k w ⟨_, hkw⟩ rfl, hk]
      rfl
  rintro u ⟨huU, huC⟩
  by_contra hnot
  have hfP : P ((Multiplicative.toAdd (β ⟨u, huU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) :=
    ⟨⟨u, huU⟩, huC, rfl⟩
  have hxc : Multiplicative.toAdd (β ⟨u, huU⟩) ∉ constWeight 6 := fun h =>
    hnot ((S.mem_U1c).2 ⟨huU, h⟩)
  have hf0 : ((Multiplicative.toAdd (β ⟨u, huU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) ≠ 0 :=
    fun h => hxc ((mem_constWeight_iff _).2 (Or.inl (Subtype.ext h)))
  have hf1 : ((Multiplicative.toAdd (β ⟨u, huU⟩) : ↥(evenWeight 6)) : Fin 6 → ZMod 2) ≠ onesV :=
    fun h => hxc ((mem_constWeight_iff _).2 (Or.inr (Subtype.ext h)))
  have hUC : ∀ v ∈ conjClosure S.V3 S.G1, v ∈ Subgroup.centralizer (pCoreOf 2 S.G1 : Set G) := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := cvr_closure h0 hadd hperm hfP
      (sum_zero_of_mem_ev (Multiplicative.toAdd (β ⟨u, huU⟩)).2) hf0 hf1
      (sum_zero_of_mem_ev (Multiplicative.toAdd (β ⟨v, hv⟩)).2)
    have hβw : β w = β ⟨v, hv⟩ := Multiplicative.toAdd.injective (Subtype.ext hwv)
    have hβ : β (⟨v, hv⟩ * w⁻¹) = 1 := by
      rw [map_mul, map_inv, hβw, mul_inv_cancel]
    have hm := Subgroup.mul_mem _ (hV1C _ ((hβk _).1 hβ)) hw
    simpa using hm
  apply h13314 G T L V S.V2 S.h13 S.irr S.zv S.isV2 S.not_iso_a5
  intro q hq
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  rw [hg1] at hq
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact ((Subgroup.mem_centralizer_iff.1 (hUC v (S.V3_le_UH (S.V2_le_V3 hv)))) q hq).symm

end Setting4

theorem input13833CoverZH_of (h13314 : Stmt13_3_14) : Input13833CoverZH :=
  fun _ _ _ _ _ _ S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ honto _ _ hβk hβe _ _ _ _ _ _ =>
    S.centralizer_QH_le_U1c h13314 (fun σ hσ => (honto σ hσ).imp fun _ hk => hk.2) hβk hβe

end CFSG.Quasithin.H13.A6
