module

public import CFSG.Quasithin.Recognition.SzVBA5Geo
public import CFSG.Quasithin.Recognition.SzVBA5Uc

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

omit [Finite G] in
theorem Uc_eq_at (hN : G₁ ≤ Subgroup.normalizer (V : Set G))
    (hUc : ∀ β β' : CosetGeom G₀ G₁ G₂, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β →
      (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β' → Uc V (γ₀ G₀ G₁ G₂) β = Uc V (γ₀ G₀ G₁ G₂) β')
    {y l l' : CosetGeom G₀ G₁ G₂} (hy : vtype y = false) (hl : (graph G₀ G₁ G₂).Adj y l)
    (hl' : (graph G₀ G₁ G₂).Adj y l') : Uc V y l = Uc V y l' := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₀ hy
  have h1 : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (g⁻¹ • l) := by
    have := (smul_adj g⁻¹).mpr hl
    rwa [inv_smul_smul] at this
  have h2 : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) (g⁻¹ • l') := by
    have := (smul_adj g⁻¹).mpr hl'
    rwa [inv_smul_smul] at this
  have e := hUc _ _ h1 h2
  have e1 := Uc_smul (V := V) (G₂ := G₂) hN g (γ₀ G₀ G₁ G₂) (g⁻¹ • l)
  have e2 := Uc_smul (V := V) (G₂ := G₂) hN g (γ₀ G₀ G₁ G₂) (g⁻¹ • l')
  rw [smul_inv_smul] at e1 e2
  rw [e1, e2, e]

theorem eq_of_ne_bot_of_le_card_two {C Z : Subgroup G} (hne : C ≠ ⊥) (hle : C ≤ Z)
    (hZ : Nat.card Z = 2) : C = Z := by
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 : Nat.card C ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  have h0 : 0 < Nat.card C := Nat.card_pos
  omega

section Crit

variable {u δ x ω p2 : CosetGeom G₀ G₁ G₂} (D : CritFacts G₀ G₁ G₂ T V z u δ x ω p2)

include D

theorem inf_Zv_Vv_u_eq_bot {β : CosetGeom G₀ G₁ G₂}
    (hβ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β) (hβ1 : β ≠ γ₁ G₀ G₁ G₂) :
    Zv z β ⊓ Vv V u = ⊥ := by
  have hN := D.hC.hyp.normalizes
  have hvβ : vtype β = true := vtype_eq_true_of_adj hβ vtype_γ₀
  have hZV : Zv z β ≤ V := by
    have := Zv_le_Vv_of_adj D.hC.klein.z_mem hN (G₂_le_normalizer_zpowers D.hC) hβ vtype_γ₀
    rwa [Vv_γ₀ hN] at this
  by_contra hne
  have h1 : Zv z β ⊓ Vv V u = Zv z β :=
    eq_of_ne_bot_of_le_card_two hne inf_le_left (card_Zv D.hC hvβ)
  have h2 : Zv z β ⊓ Vv V u = Zv z (γ₁ G₀ G₁ G₂) := by
    refine eq_of_ne_bot_of_le_card_two hne ?_ (card_Zv D.hC vtype_γ₁)
    rw [Zv_γ₁ (G₂_le_normalizer_zpowers D.hC), ← D.A_inf]
    exact le_inf (inf_le_left.trans hZV) inf_le_right
  exact Zv_ne_of_adj D.hC vtype_γ₀ hβ adj_γ₀_γ₁ hβ1 (h1.symm.trans h2)

theorem commute_of_mem_Uc_u
    (hUc : ∀ β β' : CosetGeom G₀ G₁ G₂, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β →
      (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β' → Uc V (γ₀ G₀ G₁ G₂) β = Uc V (γ₀ G₀ G₁ G₂) β')
    {β : CosetGeom G₀ G₁ G₂} (hβ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β)
    (hβ1 : β ≠ γ₁ G₀ G₁ G₂) {w : G} (hw : w ∈ Vv V β) {a : G} (ha : a ∈ Uc V δ u) :
    w * a = a * w := by
  have hN := D.hC.hyp.normalizes
  have hvβ : vtype β = true := vtype_eq_true_of_adj hβ vtype_γ₀
  have ha' : a ∈ Uc V δ x := by
    rw [← Uc_eq_at hN hUc D.t_δ D.adj_δu D.adj_δx]
    exact ha
  have haQ : a ∈ pCoreOf 2 (stab β) := D.Wx_le_Qβ β hβ (mem_Uc.mp ha').2
  have hwQδ : w ∈ pCoreOf 2 (stab δ) := D.Wβ_le_Qδ β hβ hw
  have hwδ : w ∈ stab δ := pCoreOf_le 2 _ hwQδ
  have hwu : w ∈ stab u := by
    rw [← ballStab_one_eq_pCoreOf D.hC δ] at hwQδ
    exact ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr D.adj_δu).le hwQδ
  have hc1 : w * a * w⁻¹ * a⁻¹ ∈ Zv z β := by
    have := Subgroup.commutator_mem_commutator hw haQ
    rw [commutatorElement_def] at this
    exact commutator_Vv_pCoreOf_le_Zv D.hC hvβ this
  have hc2 : w * a * w⁻¹ * a⁻¹ ∈ Uc V δ u := by
    have hnorm := stab_inf_le_normalizer_Uc (V := V) (G₂ := G₂) hN δ u ⟨hwδ, hwu⟩
    have := (Subgroup.mem_normalizer_iff.mp hnorm a).mp ha
    exact (Uc V δ u).mul_mem this ((Uc V δ u).inv_mem ha)
  have hc3 : w * a * w⁻¹ * a⁻¹ ∈ Zv z β ⊓ Vv V u := ⟨hc1, (mem_Uc.mp hc2).2⟩
  rw [inf_Zv_Vv_u_eq_bot D hβ hβ1, Subgroup.mem_bot] at hc3
  calc w * a = (w * a * w⁻¹ * a⁻¹) * (a * w) := by group
    _ = a * w := by rw [hc3, one_mul]

end Crit

omit [Finite G] in
theorem edge_data (hC : GeoCtx G₀ G₁ G₂ T V z) (g : ↥G₀) :
    stab (g • γ₀ G₀ G₁ G₂) = conjSub (g : G) G₁ ∧ stab (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) G₂ ∧
      pCoreOf 2 (stab (g • γ₀ G₀ G₁ G₂)) = conjSub (g : G) (pCoreOf 2 G₁) ∧
      pCoreOf 2 (stab (g • γ₁ G₀ G₁ G₂)) = conjSub (g : G) (pCoreOf 2 G₂) ∧
      Vv V (g • γ₀ G₀ G₁ G₂) = conjSub (g : G) V ∧
      Vv V (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) (conjClosure V G₂) := by
  have h0 : stab (g • γ₀ G₀ G₁ G₂) = conjSub (g : G) G₁ := by
    rw [stab_smul, stab_γ₀ hC.hyp.le₁]
  have h1 : stab (g • γ₁ G₀ G₁ G₂) = conjSub (g : G) G₂ := by
    rw [stab_smul, stab_γ₁ hC.hyp.le₂]
  refine ⟨h0, h1, by rw [h0, pCoreOf_conjSub], by rw [h1, pCoreOf_conjSub],
    Vv_smul_γ₀ hC.hyp.normalizes g, ?_⟩
  rw [Vv_smul hC.hyp.normalizes, Vv_γ₁ hC.hyp.le₂ hC.hyp.normalizes]

omit [Finite G] in
theorem hLF1_at_u {u : CosetGeom G₀ G₁ G₂} (hC : GeoCtx G₀ G₁ G₂ T V z) (hu : vtype u = true)
    (hZu : Zv z u = Subgroup.zpowers z)
    (hLF1 : ∀ {w : G}, w ∈ G₂ → w * w = 1 → w ∉ pCoreOf 2 G₂ →
      ∀ c : G, ∃ a ∈ conjClosure V G₂, w * a * w⁻¹ * a⁻¹ ∉ ({1, c, z, c * z} : Set G))
    {w : G} (hw : w ∈ stab u) (hw2 : w * w = 1) (hwQ : w ∉ pCoreOf 2 (stab u)) (c : G) :
    ∃ a ∈ Vv V u, w * a * w⁻¹ * a⁻¹ ∉ ({1, c, z, c * z} : Set G) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hu
  obtain ⟨-, hst, -, hQ, -, hW⟩ := edge_data hC g
  set g' : G := (g : G) with hg'
  have hzg : g' * z * g'⁻¹ = z := by
    have h1 : g' * z * g'⁻¹ ∈ Subgroup.zpowers z := by
      rw [Zv_smul_γ₁ (G₂_le_normalizer_zpowers hC)] at hZu
      rw [← hZu]
      exact mul_mem_conjSub (Subgroup.mem_zpowers z)
    have hzz : z * z = 1 := z_mul_self hC
    have hz1 : g' * z * g'⁻¹ ≠ 1 := by
      intro h
      apply hC.klein.z_ne_one
      have := congrArg (fun t => g'⁻¹ * t * g') h
      simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · exfalso
      apply hz1
      rw [← hk, ← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul]
      have : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hzz]
      rw [this, one_zpow]
    · rw [← hk, ← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul]
      have : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hzz]
      rw [this, one_zpow, mul_one, zpow_one]
  have hzg' : g'⁻¹ * z * g' = z := by
    calc g'⁻¹ * z * g' = g'⁻¹ * (g' * z * g'⁻¹) * g' := by rw [hzg]
      _ = z := by group
  rw [hst, mem_conjSub] at hw
  rw [hQ, mem_conjSub] at hwQ
  have hw2' : (g'⁻¹ * w * g') * (g'⁻¹ * w * g') = 1 := by
    calc (g'⁻¹ * w * g') * (g'⁻¹ * w * g') = g'⁻¹ * (w * w) * g' := by group
      _ = 1 := by rw [hw2]; group
  obtain ⟨a₀, ha₀, hnot⟩ := hLF1 hw hw2' hwQ (g'⁻¹ * c * g')
  refine ⟨g' * a₀ * g'⁻¹, ?_, ?_⟩
  · rw [hW]
    exact mul_mem_conjSub ha₀
  · intro hmem
    apply hnot
    have e : g'⁻¹ * (w * (g' * a₀ * g'⁻¹) * w⁻¹ * (g' * a₀ * g'⁻¹)⁻¹) * g' =
        (g'⁻¹ * w * g') * a₀ * (g'⁻¹ * w * g')⁻¹ * a₀⁻¹ := by group
    have hmem' := congrArg (fun t => g'⁻¹ * t * g') (show w * (g' * a₀ * g'⁻¹) * w⁻¹ *
      (g' * a₀ * g'⁻¹)⁻¹ = w * (g' * a₀ * g'⁻¹) * w⁻¹ * (g' * a₀ * g'⁻¹)⁻¹ from rfl)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem ⊢
    rcases hmem with h | h | h | h
    · left
      rw [← e, h]
      group
    · right; left
      rw [← e, h]
    · right; right; left
      rw [← e, h, hzg']
    · right; right; right
      rw [← e, h]
      calc g'⁻¹ * (c * z) * g' = (g'⁻¹ * c * g') * (g'⁻¹ * z * g') := by group
        _ = (g'⁻¹ * c * g') * z := by rw [hzg']

omit [Finite G] in
theorem caseA_at_edge {y u : CosetGeom G₀ G₁ G₂} (hC : GeoCtx G₀ G₁ G₂ T V z)
    (hy : vtype y = false) (hadj : (graph G₀ G₁ G₂).Adj y u)
    (hL1 : ∀ {w : G}, w ∈ pCoreOf 2 G₁ → w * w = 1 → w ∉ pCoreOf 2 G₂ →
      ∃ a ∈ conjClosure V G₂, a ∈ secCentr (pCoreOf 2 G₁) V ∧ w * a * w⁻¹ * a⁻¹ ≠ 1)
    {w : G} (hw : w ∈ pCoreOf 2 (stab y)) (hw2 : w * w = 1) (hwQ : w ∉ pCoreOf 2 (stab u)) :
    ∃ a ∈ Uc V y u, w * a * w⁻¹ * a⁻¹ ≠ 1 := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hadj hy
  obtain ⟨-, -, hQ0, hQ1, hV0, hW⟩ := edge_data hC g
  set g' : G := (g : G) with hg'
  rw [hQ0, mem_conjSub] at hw
  rw [hQ1, mem_conjSub] at hwQ
  have hw2' : (g'⁻¹ * w * g') * (g'⁻¹ * w * g') = 1 := by
    calc (g'⁻¹ * w * g') * (g'⁻¹ * w * g') = g'⁻¹ * (w * w) * g' := by group
      _ = 1 := by rw [hw2]; group
  obtain ⟨a₀, ha₀W, ha₀S, hne⟩ := hL1 hw hw2' hwQ
  refine ⟨g' * a₀ * g'⁻¹, ?_, ?_⟩
  · refine mem_Uc.mpr ⟨?_, ?_⟩
    · have h1 : g' * a₀ * g'⁻¹ ∈ conjSub g' (secCentr (pCoreOf 2 G₁) V) := mul_mem_conjSub ha₀S
      rw [conjSub_secCentr, ← hQ0, ← hV0] at h1
      exact mem_secCentr.mp h1
    · rw [hW]
      exact mul_mem_conjSub ha₀W
  · intro h
    apply hne
    have e : g'⁻¹ * (w * (g' * a₀ * g'⁻¹) * w⁻¹ * (g' * a₀ * g'⁻¹)⁻¹) * g' =
        (g'⁻¹ * w * g') * a₀ * (g'⁻¹ * w * g')⁻¹ * a₀⁻¹ := by group
    rw [← e, h]
    group

end CFSG.Quasithin.SzVB
