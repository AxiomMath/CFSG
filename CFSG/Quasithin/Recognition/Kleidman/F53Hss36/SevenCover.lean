module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenA
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Cover

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def FactH8 : Prop :=
  ∀ (P : Subgroup (Perm (Fin 5))), Nat.card P = 8 → ∀ p₀ : Fin 5, (∀ σ ∈ P, σ p₀ = p₀) →
    ∀ y : Perm (Fin 5),
      y ∈ P ⊓ alternatingGroup (Fin 5) ↔ (Perm.sign y = 1 ∧ y * y = 1 ∧ y p₀ = p₀)

@[expose] def Claim4Spec (H M S : Subgroup G) : Prop :=
  ∀ {κ ρ δ : Geo H M}, Ctx H M S κ ρ δ → Vn ρ ≤ oTwoRes (stab δ) ⊔ Qv δ

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem card_map_edge {δ μ : Geo H M} (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ)
    {θ : ↥(stab δ) →* Perm (Fin 5)} (hθk : θ.ker = (Qv δ).subgroupOf (stab δ)) :
    Nat.card (((stab δ ⊓ stab μ).subgroupOf (stab δ)).map θ) = 8 := by
  rw [← relIndex_inf_eq_card_map hθk inf_le_left, Subgroup.inf_relIndex_left]
  exact relIndex_Qv_inf_false C.hA hμ hδ

theorem map_Qv_eq_map_edge {δ μ : Geo H M} (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ)
    {θ : ↥(stab δ) →* Perm (Fin 5)} (hθk : θ.ker = (Qv δ).subgroupOf (stab δ)) :
    ((Qv μ).subgroupOf (stab δ)).map θ = ((stab δ ⊓ stab μ).subgroupOf (stab δ)).map θ := by
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ hδ
  have hδμ : δ ∈ nbrs μ := mem_nbrs_comm hμ
  have hQμs : Qv μ ≤ stab δ := Qv_le_stab_of_mem_nbrs C.hA hδμ
  have hQδn : stab δ ≤ Subgroup.normalizer (Qv δ : Set G) := le_normalizer_pCoreOf 2 (stab δ)
  have h28 : Qv μ ⊔ Qv δ = stab μ ⊓ stab δ := C.h28 C.hb1 μ δ hδμ (C.bAt_eq_of_true hvμ)
  apply le_antisymm
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ (le_inf hQμs (pCoreOf_le 2 _)))
  · rintro _ ⟨g, hg, rfl⟩
    have hg' : (g : G) ∈ ((Qv μ ⊔ Qv δ : Subgroup G) : Set G) := by
      rw [h28, inf_comm]; exact Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (Qv μ) (Qv δ) (hQμs.trans hQδn)] at hg'
    obtain ⟨x, hx, q, hq, hxq⟩ := hg'
    have hqs : q ∈ stab δ := pCoreOf_le 2 _ hq
    refine ⟨⟨x, hQμs hx⟩, Subgroup.mem_subgroupOf.mpr hx, ?_⟩
    have hq1 : θ ⟨q, hqs⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf]; exact hq
    have e : g = ⟨x, hQμs hx⟩ * ⟨q, hqs⟩ := Subtype.ext hxq.symm
    rw [e, map_mul, hq1, mul_one]

theorem mem_stab_of_map_mem {δ μ : Geo H M} (hμ : μ ∈ nbrs δ)
    {θ : ↥(stab δ) →* Perm (Fin 5)} (hθk : θ.ker = (Qv δ).subgroupOf (stab δ)) {g : G}
    (hg : g ∈ stab δ) (hmem : θ ⟨g, hg⟩ ∈ ((stab δ ⊓ stab μ).subgroupOf (stab δ)).map θ) :
    g ∈ stab μ := by
  obtain ⟨k, hk, hkg⟩ := hmem
  have hq : (k⁻¹ * ⟨g, hg⟩ : ↥(stab δ)) ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
  rw [hθk, Subgroup.mem_subgroupOf] at hq
  have hkμ : (k : G) ∈ stab μ := (Subgroup.mem_subgroupOf.mp hk).2
  have hqμ : ((k⁻¹ * ⟨g, hg⟩ : ↥(stab δ)) : G) ∈ stab μ := Qv_le_stab_of_mem_nbrs C.hA hμ hq
  have e : g = (k : G) * ((k⁻¹ * ⟨g, hg⟩ : ↥(stab δ)) : G) := by simp
  rw [e]
  exact (stab μ).mul_mem hkμ hqμ

theorem vtype_path (P : CritPath α β α') {j : ℕ} (hj : j ≤ bMin H M) :
    vtype (P.p j) = decide (Even j) := by
  have h := P.vtype_iff C.hA hj
  rw [C.hv] at h
  by_cases he : Even j
  · rw [decide_eq_true he]; exact h.mpr he
  · rw [decide_eq_false he]
    cases hv : vtype (P.p j)
    · rfl
    · exact absurd (h.mp hv) he

theorem vtype_P_δ (P : CritPath α β α') : vtype P.δ = false := by
  have hb := C.hb5
  obtain ⟨k, hk⟩ := C.hodd
  rw [C.vtype_path P (j := bMin H M - 2) (by omega), decide_eq_false]
  rw [Nat.not_even_iff_odd]; exact ⟨k - 1, by omega⟩

theorem vtype_P_γ (P : CritPath α β α') : vtype P.γ = true := by
  have hb := C.hb5
  obtain ⟨k, hk⟩ := C.hodd
  rw [C.vtype_path P (j := bMin H M - 1) (by omega), decide_eq_true]
  exact ⟨k, by omega⟩

theorem dist_beta_P_δ (P : CritPath α β α') : dist β P.δ + 3 = bMin H M := by
  show dist β (P.p (bMin H M - 2)) + 3 = bMin H M
  have hb := C.hb5
  have := P.dist_of_le (i := 1) (j := bMin H M - 2) (by omega) (by omega)
  rw [P.p_one] at this
  omega

theorem dist_beta_P_ε (P : CritPath α β α') : dist β P.ε + 4 = bMin H M := by
  show dist β (P.p (bMin H M - 3)) + 4 = bMin H M
  have hb := C.hb5
  have := P.dist_of_le (i := 1) (j := bMin H M - 3) (by omega) (by omega)
  rw [P.p_one] at this
  omega

theorem dist_beta_P_γ (P : CritPath α β α') : dist β P.γ + 2 = bMin H M := by
  show dist β (P.p (bMin H M - 1)) + 2 = bMin H M
  have hb := C.hb5
  have := P.dist_of_le (i := 1) (j := bMin H M - 1) (by omega) (by omega)
  rw [P.p_one] at this
  omega

theorem exists_moves_point (h4 : Claim4Spec H M S) (hH8 : FactH8) (P : CritPath α β α')
    (hW : ¬ Wnn β ≤ stab P.γ) {θ : ↥(stab P.δ) →* Perm (Fin 5)}
    (hθs : Function.Surjective θ) (hθk : θ.ker = (Qv P.δ).subgroupOf (stab P.δ)) {p₀ : Fin 5}
    (hp₀ : ∀ σ ∈ ((stab P.δ ⊓ stab P.γ).subgroupOf (stab P.δ)).map θ, σ p₀ = p₀) :
    ∃ w ∈ Wnn β, ∃ hw : w ∈ stab P.δ, θ ⟨w, hw⟩ p₀ ≠ p₀ := by
  have hb := C.hb5
  have hvδ := C.vtype_P_δ P
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hε : P.ε ∈ nbrs P.δ := mem_nbrs_comm (P.ε_adj (by omega))
  have h7a := C.Wnn_le_of_claim4 h4 C.vtype_beta hvδ (C.dist_beta_P_δ P).le
    (C.dist_beta_P_ε P).le
  have hWδ : Wnn β ≤ stab P.δ := C.Wnn_le_stab_of_dist C.vtype_beta (C.dist_beta_P_δ P).le
  obtain ⟨w, hwW, hwγ⟩ := Set.not_subset.mp hW
  have hwδ : w ∈ stab P.δ := hWδ hwW
  refine ⟨w, hwW, hwδ, fun hfix => hwγ ?_⟩
  obtain ⟨p₁, hp₁, -⟩ := exists_fix_trans_of_card_eight _ (C.card_map_edge hvδ hε hθk)
  have hwT : θ ⟨w, hwδ⟩ ∈ ((stab P.δ ⊓ stab P.ε).subgroupOf (stab P.δ)).map θ ⊓
      alternatingGroup (Fin 5) := by
    refine ⟨⟨⟨w, hwδ⟩, Subgroup.mem_subgroupOf.mpr ⟨hwδ, (h7a hwW).1⟩, rfl⟩, ?_⟩
    exact (S34.mem_sup_iff_alt hθs hθk hwδ).mp (h7a hwW).2
  obtain ⟨hs, hsq, -⟩ := (hH8 _ (C.card_map_edge hvδ hε hθk) p₁ hp₁ _).mp hwT
  have hwD := ((hH8 _ (C.card_map_edge hvδ hγ hθk) p₀ hp₀ _).mpr ⟨hs, hsq, hfix⟩).1
  exact C.mem_stab_of_map_mem hγ hθk hwδ hwD

theorem cover_eq (h4 : Claim4Spec H M S) (hH8 : FactH8) (P : CritPath α β α')
    (hW : ¬ Wnn β ≤ stab P.γ) : Wnn β ⊔ Qv P.γ = stab P.δ := by
  have hb := C.hb5
  have hvδ := C.vtype_P_δ P
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hWδ : Wnn β ≤ stab P.δ := C.Wnn_le_stab_of_dist C.vtype_beta (C.dist_beta_P_δ P).le
  have hQγ : Qv P.γ ≤ stab P.δ := Qv_le_stab_of_mem_nbrs C.hA (mem_nbrs_comm hγ)
  have hXs : Wnn β ⊔ Qv P.γ ≤ stab P.δ := sup_le hWδ hQγ
  obtain ⟨-, θ, -, hθs, hθk, -⟩ := C.exists_secData hvδ
  obtain ⟨p₀, hp₀, htr⟩ := exists_fix_trans_of_card_eight _ (C.card_map_edge hvδ hγ hθk)
  obtain ⟨w, hwW, hwδ, hwp⟩ := C.exists_moves_point h4 hH8 P hW hθs hθk hp₀
  set X := Wnn β ⊔ Qv P.γ with hX
  have htop : (X.subgroupOf (stab P.δ)).map θ = ⊤ := by
    refine F5b_core _ _ (C.card_map_edge hvδ hγ hθk) p₀ htr ?_ ?_
    · rw [← C.map_Qv_eq_map_edge hvδ hγ hθk]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_right)
    · intro hle
      have hmem : θ ⟨w, hwδ⟩ ∈ (X.subgroupOf (stab P.δ)).map θ :=
        ⟨⟨w, hwδ⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hwW), rfl⟩
      exact hwp (by simpa [MulAction.mem_stabilizer_iff] using hle hmem)
  have hcov : X ⊔ Qv P.δ = stab P.δ := by
    apply le_antisymm (sup_le hXs (pCoreOf_le 2 _))
    intro g hg
    have hθg : θ ⟨g, hg⟩ ∈ (X.subgroupOf (stab P.δ)).map θ := by rw [htop]; trivial
    obtain ⟨x, hx, hxg⟩ := hθg
    have hq : (x⁻¹ * ⟨g, hg⟩ : ↥(stab P.δ)) ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxg, inv_mul_cancel]
    rw [hθk, Subgroup.mem_subgroupOf] at hq
    have e : g = (x : G) * ((x⁻¹ * ⟨g, hg⟩ : ↥(stab P.δ)) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
      (Subgroup.mem_sup_right hq)
  exact C.eq_stab_of_cover hvδ hγ hXs le_sup_right hcov

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
