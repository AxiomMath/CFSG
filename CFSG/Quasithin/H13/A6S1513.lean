module

public import CFSG.Quasithin.H13.A6S1357
public import CFSG.Quasithin.Background.F9Five

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def C012 : List (Perm (Fin 6)) :=
  [1, swap 0 1 * swap 1 2, swap 0 1 * swap 1 2 * (swap 0 1 * swap 1 2)]

@[expose] def ToW2 (y : P6) : Prop :=
  ∃ σ ∈ C012, InW2 (act4f σ y) ∧ act4f σ y ≠ 1 ∧ act4f σ y ≠ e0123

instance (y : P6) : Decidable (ToW2 y) := by unfold ToW2; infer_instance

theorem toW2 : ∀ y : P6, InW34 y → y ≠ 1 → y ≠ e0123 → ToW2 y := by
  decide +kernel

@[expose] def W2Span (y : P6) : Prop :=
  ∀ u : P6, InW2 u → u = 1 ∨ u = e0123 ∨ u = y ∨ u = y * e0123

instance (y : P6) : Decidable (W2Span y) := by unfold W2Span; infer_instance

theorem w2Span : ∀ y : P6, InW2 y → y ≠ 1 → y ≠ e0123 → W2Span y := by
  decide +kernel

theorem le_sup_of_relIndex_two {G : Type} [Group G] {A Q : Subgroup G} {x : G}
    (hidx : (A ⊓ Q).relIndex A = 2) (hxA : x ∈ A) (hxQ : x ∉ Q) (hx2 : x * x = 1) :
    A ≤ Subgroup.zpowers x ⊔ Q := by
  intro a ha
  by_cases haQ : a ∈ Q
  · exact Subgroup.mem_sup_right haQ
  have hidx' : ((A ⊓ Q).subgroupOf A).index = 2 := hidx
  have hmem := (Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨a, ha⟩) (b := ⟨x, hxA⟩)).2
    (by
      constructor
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.1 h).2 haQ
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.1 h).2 hxQ)
  have hax : a * x ∈ Q := (Subgroup.mem_subgroupOf.1 hmem).2
  have e : a = (a * x) * x := by
    rw [mul_assoc, hx2, mul_one]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hax)
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem relIndex_V3 : S.V3.relIndex V = 2 := by
  have h := Subgroup.relIndex_mul_card S.V3 V
  rw [inf_eq_left.2 S.V3_le_V, S.card_V3, S.card_V] at h
  omega

theorem isPGroup_sup_of_lt
    (hNS : ¬ LieModel G .PSp 3 2 1) (h1356two : Input1356Two)
    (h13315 : Stmt13_3_15) {H : Subgroup G} (hH : H ∈ S.Hz) {g : G} (hg : g ∈ H)
    (hlt : fsuV1 T V < V ⊓ conjSub g⁻¹ V) : IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V) := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  set Q := pCoreOf 2 H with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hgQ : conjSub g⁻¹ Q = Q := A5.conjSub_self_of_mem (hHQ (H.inv_mem hg))
  by_cases hVQ : V ≤ Q
  · have hVgQ : conjSub g⁻¹ V ≤ Q := by
      rw [← hgQ]
      exact conjSub_mono _ hVQ
    exact hQ2.to_le (sup_le hVQ hVgQ)
  have hV3 : S.V3 = V ⊓ Q := (hF.F95_1 S.relIndex_V3 hVQ).1
  have hV2 : IsElemAbelian 2 V := S.elemAbelian_V
  by_cases hx : V ⊓ conjSub g⁻¹ V ≤ Q
  ·
    obtain ⟨x, hxVV, hxV1⟩ := IsConcreteLE.exists_of_lt hlt
    have hxV : x ∈ V := hxVV.1
    have hx3 : x ∈ S.V3 := by
      rw [hV3]
      exact ⟨hxV, hx hxVV⟩
    obtain ⟨_, hxW3⟩ := S.mem_pre.1 hx3
    have hy1 : (S.frame.ψ ⟨x, hxV⟩ : P6) ≠ 1 := fun h => hxV1 (by
      have : (⟨x, hxV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h)
      exact S.mem_V1_iff.2 (Or.inl (congrArg Subtype.val this)))
    have hyz : (S.frame.ψ ⟨x, hxV⟩ : P6) ≠ e0123 := fun h => hxV1 (by
      have : (⟨x, hxV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
        S.frame.ψ.injective (by rw [S.psi_z]; exact Subtype.ext h)
      exact S.mem_V1_iff.2 (Or.inr (congrArg Subtype.val this)))
    obtain ⟨σ, hσC, hσW2, hσ1, hσz⟩ :=
      toW2 _ ⟨(S.frame.ψ ⟨x, hxV⟩).2, hxW3⟩ hy1 hyz
    obtain ⟨c, hcL1, hc⟩ := S.exists_L1_c012
    have hl : ∃ l : ↥(Subgroup.normalizer (V : Set G)), (l : G) ∈ S.L1 ∧ S.frame.ρ l = σ := by
      simp only [C012, List.mem_cons, List.not_mem_nil, or_false] at hσC
      rcases hσC with rfl | rfl | rfl
      · exact ⟨1, S.L1.one_mem, map_one _⟩
      · exact ⟨c, hcL1, hc⟩
      · exact ⟨c * c, S.L1.mul_mem hcL1 hcL1, by rw [map_mul, hc]⟩
    obtain ⟨l, hlL1, hlσ⟩ := hl
    have hlH : (l : G) ∈ H := (le_sup_left.trans hH.1.1) hlL1
    have hlV1 : (l : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G) :=
      S.L1T_le_NV1 (le_sup_left (a := S.L1) hlL1)
    set g' := g * (l : G)⁻¹ with hg'
    have hVg' : conjSub g'⁻¹ V = conjSub (l : G) (conjSub g⁻¹ V) := by
      rw [hg', mul_inv_rev, inv_inv, conjSub_mul]
    have hyV : (l : G) * x * (l : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp l.2 x).mp hxV
    have hψy : (S.frame.ψ ⟨(l : G) * x * (l : G)⁻¹, hyV⟩ : P6) =
        act4f σ (S.frame.ψ ⟨x, hxV⟩ : P6) := by
      rw [S.psi_conj l ⟨x, hxV⟩, act4_coe, hlσ]
      rfl
    have hyVg' : (l : G) * x * (l : G)⁻¹ ∈ conjSub g'⁻¹ V := by
      rw [hVg']
      exact mul_mem_conjSub hxVV.2
    have hV1g' : fsuV1 T V ≤ conjSub g'⁻¹ V := by
      rw [hVg', ← A5.conjSub_self_of_mem hlV1]
      exact conjSub_mono _ (hlt.le.trans inf_le_right)
    have hV2le : S.V2 ≤ V ⊓ conjSub g'⁻¹ V := by
      intro w hw
      obtain ⟨hwV, hwW2⟩ := S.mem_pre.1 hw
      refine ⟨hwV, ?_⟩
      have hspan := w2Span _ hσW2 hσ1 hσz _ hwW2
      rw [← hψy] at hspan
      have hinj : ∀ u : ↥V, (S.frame.ψ ⟨w, hwV⟩ : P6) = (S.frame.ψ u : P6) → w = u :=
        fun u h => congrArg Subtype.val (S.frame.ψ.injective (Subtype.ext h))
      rcases hspan with h | h | h | h
      · rw [hinj 1 (by rw [map_one]; exact h)]
        exact Subgroup.one_mem _
      · rw [hinj ⟨S.z, S.z_mem_V⟩ (by rw [S.psi_z]; exact h)]
        exact hV1g' (S.mem_V1_iff.2 (Or.inr rfl))
      · rw [hinj _ h]
        exact hyVg'
      · rw [hinj (⟨(l : G) * x * (l : G)⁻¹, hyV⟩ * ⟨S.z, S.z_mem_V⟩)
          (by rw [map_mul, S.psi_z]; exact h)]
        exact Subgroup.mul_mem _ hyVg' (hV1g' (S.mem_V1_iff.2 (Or.inr rfl)))
    have hN : conjSub g'⁻¹ V ≤ Subgroup.normalizer (V : Set G) := by
      rcases S.lemma13_5_6_three hNS h1356two h13315 g' hV2le with h0 | ⟨-, hN, -⟩
      · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
        exact h0.trans (Subgroup.centralizer_le_normalizer _)
      · exact hN
    have hP : IsPGroup 2 ↥(V ⊔ conjSub g'⁻¹ V) :=
      IsPGroup.to_sup_of_normal_left' S.isPGroup_V (F7.isPGroup_conjSub S.isPGroup_V) hN
    have e : V ⊔ conjSub g⁻¹ V = conjSub (l : G)⁻¹ (V ⊔ conjSub g'⁻¹ V) := by
      rw [conjSub_sup, hVg', conjSub_conjSub_inv, A5.conjSub_self_of_mem (Subgroup.inv_mem _ l.2)]
    rw [e]
    exact F7.isPGroup_conjSub hP
  ·
    obtain ⟨x, hxVV, hxQ⟩ := IsConcreteLE.not_le_iff_exists.1 hx
    have hx2 : x * x = 1 := by
      have := hV2.2 x hxVV.1
      rwa [pow_two] at this
    have hidxV : (V ⊓ Q).relIndex V = 2 := hV3 ▸ S.relIndex_V3
    have hidxVg : (conjSub g⁻¹ V ⊓ Q).relIndex (conjSub g⁻¹ V) = 2 := by
      rw [← hgQ, ← conjSub_inf]
      have := Subgroup.relIndex_map_map_of_injective (V ⊓ Q) V
        (f := (MulAut.conj g⁻¹).toMonoidHom) (MulEquiv.injective _)
      exact this.trans hidxV
    have h1 := le_sup_of_relIndex_two hidxV hxVV.1 hxQ hx2
    have h2 := le_sup_of_relIndex_two hidxVg hxVV.2 hxQ hx2
    have hP : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ Q) := by
      refine IsPGroup.to_sup_of_normal_right' ?_ hQ2 ?_
      · exact IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, pow_one]
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          refine orderOf_eq_prime (by rwa [pow_two]) fun h => hxQ ?_
          rw [h]
          exact Q.one_mem)
      · rw [Subgroup.zpowers_le]
        exact hHQ (hF.V_le_H hxVV.1)
    exact hP.to_le (sup_le h1 h2)

theorem comm_centralizer_V3 (h13315 : Stmt13_3_15) (H : Subgroup G) :
    ⁅V, H ⊓ Subgroup.centralizer (S.V3 : Set G)⁆ ≤ fsuV1 T V := by
  classical
  let X : Subgroup G := if IsHatA6 L then oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ else L₁Of L S.V2
  have hX₁ : IsHatA6 L → X = oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆ := fun h => by simp [X, h]
  have hX₂ : ¬ IsHatA6 L → X = L₁Of L S.V2 := fun h => by simp [X, h]
  obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := h13315 G T L V S.V2 X _ S.h13 S.irr S.zv S.isV2
    S.not_iso_a5 hX₁ hX₂ rfl
  exact (Subgroup.commutator_mono le_rfl inf_le_right).trans
    ((h9 S.V3 S.V2_le_V3 S.V3_le_V S.T_le_normalizer_V3 S.card_V3).2 S.not_lieModel_psu33)

end Setting4

end CFSG.Quasithin.H13.A6
