module

public import CFSG.Quasithin.Recognition.Kleidman.F204.T3Crit
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPath

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom
  CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem isPGroup_two_conjSub {K : Subgroup G} (hK : IsPGroup 2 K) (g : G) :
    IsPGroup 2 (conjSub g K) :=
  hK.map (MulAut.conj g).toMonoidHom

section Frame

variable (F : Frame L1 L2 S D X)
include F

theorem Q1_le_mul_of_index4 {K : Subgroup G} (hKB : K ≤ bigB L1 L2 S) (hK2 : IsPGroup 2 K)
    (h4 : (K ⊓ Q2 L1 L2 S).relIndex K = 4) :
    ∀ q ∈ Q1 L1 L2 S, ∃ k ∈ K, ∃ q' ∈ Q2 L1 L2 S, q = k * q' := by
  have hA := Amal.of_frame F
  obtain ⟨φ, -, hφk⟩ := exists_phi_P2 F
  have hBP1 : bigB L1 L2 S ≤ P1 L1 L2 S := le_sup_right
  have hBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hSB : IsSylowTwoOf S (bigB L1 L2 S) := by
    have := hA.amalgam.sylow_inf
    rwa [F.P1_inf_P2] at this
  obtain ⟨b, hb, hKb⟩ := isSylowTwoOf_exists_conj_le hSB hKB hK2
  set S'' := conjSub b S with hS''
  have hbP1 : b ∈ P1 L1 L2 S := hBP1 hb
  have hbP2 : b ∈ P2 L1 L2 S := hBP2 hb
  have hQ1b : conjSub b (Q1 L1 L2 S) = Q1 L1 L2 S := conjSub_Q1 F hbP1
  have hQ2b : conjSub b (Q2 L1 L2 S) = Q2 L1 L2 S :=
    conjSub_eq_of_mem_normalizer (P2_le_normalizer_Q2 L1 L2 S hbP2)
  have hQ1S'' : Q1 L1 L2 S ≤ S'' := by
    rw [← hQ1b]; exact conjSub_mono b F.Q1_le_S
  have hS''P : S'' ≤ P2 L1 L2 S := by
    intro x hx
    rw [hS'', mem_conjSub] at hx
    have : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
    rw [this]
    exact (P2 L1 L2 S).mul_mem ((P2 L1 L2 S).mul_mem hbP2 (S_le_P2 F hx)) ((P2 L1 L2 S).inv_mem hbP2)
  have hKP : K ≤ P2 L1 L2 S := hKB.trans hBP2
  have hidx4 : (S'' ⊓ Q2 L1 L2 S).relIndex S'' = 4 := by
    have e : S'' ⊓ Q2 L1 L2 S = conjSub b (S ⊓ Q2 L1 L2 S) := by
      rw [conjSub_inf, hQ2b]
    rw [e, hS'', relIndex_conjSub, inf_comm]
    exact (Subgroup.inf_relIndex_right (H := Q2 L1 L2 S) (K := S)).trans (relIndex_Q2_S F)
  have hc1 := card_inf_of_relIndex h4
  have hc2 := card_inf_of_relIndex hidx4
  have key := exists_mul_ker_of_card (P := P2 L1 L2 S) (K := K) (M := S'') (Q := Q2 L1 L2 S) φ hφk
    hKb hS''P (by rw [← hc1, ← hc2]; ring)
  intro q hq
  obtain ⟨k, hk, hkq⟩ := key q (hQ1S'' hq)
  exact ⟨k, hk, k⁻¹ * q, hkq, by group⟩


end Frame

section Vertex

variable (F : Frame L1 L2 S D X)
include F

theorem Qv_le_mul_of_index4 {x ε : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hε : ε ∈ nbrs x) {K : Subgroup G} (hKx : K ≤ stab x) (hKε : K ≤ stab ε)
    (hK2 : IsPGroup 2 K) (h4 : (K ⊓ Qv x).relIndex K = 4) :
    ∀ q ∈ Qv ε, ∃ k ∈ K, ∃ q' ∈ Qv x, q = k * q' := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨g, hg1, hg0⟩ := exists_edge_conj_true hx hε
  have hsx : stab x = conjSub (g : G) (P2 L1 L2 S) := by rw [← hg1, stab_smul, stab_γ₁ h₂]
  have hsε : stab ε = conjSub (g : G) (P1 L1 L2 S) := by rw [← hg0, stab_smul, stab_γ₀ h₁]
  have hQx : Qv x = conjSub (g : G) (Q2 L1 L2 S) := by
    rw [← hg1, Qv_smul]; unfold Qv; rw [stab_γ₁ h₂]
  have hQε : Qv ε = conjSub (g : G) (Q1 L1 L2 S) := by
    rw [← hg0, Qv_smul]; unfold Qv; rw [stab_γ₀ h₁]
  set K' := conjSub (g : G)⁻¹ K with hK'
  have hK'B : K' ≤ bigB L1 L2 S := by
    have h : K' ≤ P2 L1 L2 S ⊓ P1 L1 L2 S := by
      have := conjSub_mono (g : G)⁻¹ (le_inf hKx hKε : K ≤ stab x ⊓ stab ε)
      rwa [hsx, hsε, ← conjSub_inf, conjSub_conjSub_inv] at this
    rwa [inf_comm, F.P1_inf_P2] at h
  have hK'2 : IsPGroup 2 K' := isPGroup_two_conjSub hK2 _
  have h4' : (K' ⊓ Q2 L1 L2 S).relIndex K' = 4 := by
    have e : K' ⊓ Q2 L1 L2 S = conjSub (g : G)⁻¹ (K ⊓ Qv x) := by
      rw [conjSub_inf, hQx, conjSub_conjSub_inv]
    rw [e, hK', relIndex_conjSub]
    exact h4
  have key := Q1_le_mul_of_index4 F hK'B hK'2 h4'
  intro q hq
  rw [hQε, mem_conjSub] at hq
  obtain ⟨k₁, hk₁, q₂, hq₂, hq₁⟩ := key _ hq
  refine ⟨(g : G) * k₁ * (g : G)⁻¹, ?_, (g : G) * q₂ * (g : G)⁻¹, ?_, ?_⟩
  · have := mul_mem_conjSub (g := (g : G)) hk₁
    rwa [hK', conjSub_inv_conjSub] at this
  · rw [hQx]; exact mul_mem_conjSub hq₂
  · calc q = (g : G) * ((g : G)⁻¹ * q * (g : G)) * (g : G)⁻¹ := by group
      _ = _ := by rw [hq₁]; group


theorem no_D_end (hT3 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ¬ ZCentral δ)
    {x y : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = false)
    (hd : dist x y ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S)) : Zv x ≤ Qv y := by
  have hA := Amal.of_frame F
  by_contra hn
  have hb2 := two_le_bMin F
  have hge : bMin (P1 L1 L2 S) (P2 L1 L2 S) ≤ bAt x := bMin_le_bAt x
  have hle : bAt x ≤ dist x y := by
    by_contra hlt
    exact hn (Zv_le_Qv_of_dist_lt (not_le.mp hlt))
  have hdist : dist x y = bMin (P1 L1 L2 S) (P2 L1 L2 S) := by omega
  have hbAt : bAt x = bMin (P1 L1 L2 S) (P2 L1 L2 S) := by omega
  obtain ⟨β, hxβ, hβy⟩ := exists_adj_dist_eq hA.amalgam.gen (α := y) (δ := x)
    (d := bMin (P1 L1 L2 S) (P2 L1 L2 S) - 1) (by rw [CosetGeom.dist_comm, hdist]; omega)
  have hc : IsCritData x β y :=
    { adj := hxβ
      bAt_eq := hbAt
      dist_eq := hdist
      dist_eq' := by rw [CosetGeom.dist_comm, hβy]; omega
      not_le := hn }
  obtain ⟨-, hvx, -⟩ := T3_H4 F hT3 hc
  rw [hx] at hvx
  exact Bool.noConfusion hvx

end Vertex

end CFSG.Quasithin.Kleidman.F204
