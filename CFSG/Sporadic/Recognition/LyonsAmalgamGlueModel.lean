module

public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueInputs
public import CFSG.Sporadic.Recognition.LyonsAmalgamTransversal
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelTau
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.Glue

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Recognition.LyonsSims

@[expose] def botEquivBot {A A' : Type*} [Group A] [Group A'] :
    ↥(⊥ : Subgroup A) ≃* ↥(⊥ : Subgroup A') where
  toFun _ := 1
  invFun _ := 1
  left_inv x := Subtype.ext (Subgroup.mem_bot.1 x.2).symm
  right_inv x := Subtype.ext (Subgroup.mem_bot.1 x.2).symm
  map_mul' _ _ := by simp

theorem coe_botEquivBot {A A' : Type*} [Group A] [Group A'] (x : ↥(⊥ : Subgroup A)) :
    ((botEquivBot x : ↥(⊥ : Subgroup A')) : A') = 1 := rfl

theorem exists_treeEquiv {n₁ n₂ : ℕ} (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32) {m : ℕ}
    {G₁ G₂ E₁ E₂ : Array Table} {par lab : Array ℕ} {succ : Array (Array ℕ)}
    {g₁ : ℕ → Perm (Fin n₁)} {g₂ : ℕ → Perm (Fin n₂)}
    (hG₁ : G₁.size = m) (hG₂ : G₂.size = m)
    (hg₁ : ∀ l < m, Rep n₁ G₁[l]! (g₁ l)) (hg₂ : ∀ l < m, Rep n₂ G₂[l]! (g₂ l))
    (hT₁ : mulTreeOK n₁ G₁ E₁ par lab = true) (hT₂ : mulTreeOK n₂ G₂ E₂ par lab = true)
    (hd₁ : hkeysDistinct n₁ E₁.toList = true) (hd₂ : hkeysDistinct n₂ E₂.toList = true)
    (hs : E₂.size = E₁.size)
    (hsucc : ∀ k < E₁.size, ∀ l < m, (succ[k]!)[l]! < E₁.size ∧
      tblEq n₁ E₁[(succ[k]!)[l]!]! (compT n₁ E₁[k]! G₁[l]!) = true ∧
      tblEq n₂ E₂[(succ[k]!)[l]!]! (compT n₂ E₂[k]! G₂[l]!) = true)
    {P₂ : Subgroup (Perm (Fin n₂))} (hP₂ : P₂ ≤ Subgroup.closure (g₂ '' {l | l < m}))
    (hg₂P : ∀ l < m, g₂ l ∈ P₂) :
    ExactEnum n₁ (Subgroup.closure (g₁ '' {l | l < m})) E₁ ∧
    ∃ Φ : ↥(Subgroup.closure (g₁ '' {l | l < m})) ≃* ↥P₂,
      (∀ (k : ℕ) (_ : k < E₁.size)
        (hmem : tablePerm n₁ E₁[k]! ∈ Subgroup.closure (g₁ '' {l | l < m})),
        ((Φ ⟨tablePerm n₁ E₁[k]!, hmem⟩ : ↥P₂) : Perm (Fin n₂)) = tablePerm n₂ E₂[k]!) ∧
      ∀ (l : ℕ) (_ : l < m) (hmem : g₁ l ∈ Subgroup.closure (g₁ '' {l | l < m})),
        ((Φ ⟨g₁ l, hmem⟩ : ↥P₂) : Perm (Fin n₂)) = g₂ l := by
  classical
  set P₁ : Subgroup (Perm (Fin n₁)) := Subgroup.closure (g₁ '' {l | l < m}) with hP₁
  have hgP₁ : ∀ l < m, g₁ l ∈ P₁ := fun l hl => Subgroup.subset_closure ⟨l, hl, rfl⟩
  have hGg₁ : ∀ l < G₁.size, Rep n₁ G₁[l]! (g₁ l) ∧ g₁ l ∈ P₁ := fun l hl =>
    ⟨hg₁ l (hG₁ ▸ hl), hgP₁ l (hG₁ ▸ hl)⟩
  have hGg₂ : ∀ l < G₂.size, Rep n₂ G₂[l]! (g₂ l) ∧ g₂ l ∈ P₂ := fun l hl =>
    ⟨hg₂ l (hG₂ ▸ hl), hg₂P l (hG₂ ▸ hl)⟩
  have hspec₁ := mulTreeOK_spec hn₁ P₁ hGg₁ hT₁
  have hspec₂ := mulTreeOK_spec hn₂ P₂ hGg₂ hT₂
  have hrep₁ : ∀ k < E₁.size, Rep n₁ E₁[k]! (tablePerm n₁ E₁[k]!) := by
    intro k hk
    obtain ⟨c, -, hc⟩ := hspec₁ k hk
    rw [tablePerm_eq hc]
    exact hc
  have hmem₁ : ∀ k < E₁.size, tablePerm n₁ E₁[k]! ∈ P₁ := by
    intro k hk
    obtain ⟨c, hc, hcrep⟩ := hspec₁ k hk
    rw [tablePerm_eq hcrep]
    exact hc
  have hrep₂ : ∀ k < E₂.size, Rep n₂ E₂[k]! (tablePerm n₂ E₂[k]!) := by
    intro k hk
    obtain ⟨c, -, hc⟩ := hspec₂ k hk
    rw [tablePerm_eq hc]
    exact hc
  have hmem₂ : ∀ k < E₂.size, tablePerm n₂ E₂[k]! ∈ P₂ := by
    intro k hk
    obtain ⟨c, hc, hcrep⟩ := hspec₂ k hk
    rw [tablePerm_eq hcrep]
    exact hc
  have hnodup₁ := nodup_of_hkeysDistinct (forall₂_tablePerm hrep₁) hd₁
  have hnodup₂ := nodup_of_hkeysDistinct (forall₂_tablePerm hrep₂) hd₂
  obtain ⟨hpos₁, h0₁, -⟩ := Tau.mulTree_facts hn₁ (fun l hl => (hGg₁ l hl).1) hT₁
  obtain ⟨hpos₂, h0₂, -⟩ := Tau.mulTree_facts hn₂ (fun l hl => (hGg₂ l hl).1) hT₂
  have hsch : ∀ i < E₁.size, ∀ k < m, tablePerm n₁ E₁[i]! * g₁ k =
      1 * tablePerm n₁ E₁[(succ[i]!)[k]!]! := by
    intro i hi k hk
    obtain ⟨hlt, e1, -⟩ := hsucc i hi k hk
    rw [one_mul]
    exact ((tblEq_iff_eq (hrep₁ _ hlt) (Rep.compT (hrep₁ i hi) (hg₁ k hk))).1 e1).symm
  have hsch' : ∀ i < E₁.size, ∀ k < m, tablePerm n₂ E₂[i]! * g₂ k =
      1 * tablePerm n₂ E₂[(succ[i]!)[k]!]! := by
    intro i hi k hk
    obtain ⟨hlt, -, e2⟩ := hsucc i hi k hk
    rw [one_mul]
    exact ((tblEq_iff_eq (hrep₂ _ (hs ▸ hlt))
      (Rep.compT (hrep₂ i (hs ▸ hi)) (hg₂ k hk))).1 e2).symm
  have hdist : ∀ i < E₁.size, ∀ j < E₁.size, tablePerm n₁ E₁[i]! * (tablePerm n₁ E₁[j]!)⁻¹ ∈
      (⊥ : Subgroup (Perm (Fin n₁))) → i = j := by
    intro i hi j hj h
    exact Tau.inj_of_nodup hnodup₁ hi hj (mul_inv_eq_one.1 (Subgroup.mem_bot.1 h))
  have hdist' : ∀ i < E₁.size, ∀ j < E₁.size, tablePerm n₂ E₂[i]! * (tablePerm n₂ E₂[j]!)⁻¹ ∈
      (⊥ : Subgroup (Perm (Fin n₂))) → i = j := by
    intro i hi j hj h
    exact Tau.inj_of_nodup hnodup₂ (hs ▸ hi) (hs ▸ hj) (mul_inv_eq_one.1 (Subgroup.mem_bot.1 h))
  have hcov := transversal_cover (P := P₁) (H := (⊥ : Subgroup (Perm (Fin n₁)))) (m := m)
    (n := E₁.size) (g := g₁) (v := fun i => tablePerm n₁ E₁[i]!)
    (σ := fun k i => (succ[i]!)[k]!) (hh := fun _ _ => 1) le_rfl hpos₁ h0₁
    (fun i hi k hk => (hsucc i hi k hk).1) (fun _ _ _ _ => Subgroup.one_mem _) hsch
  obtain ⟨Φ, hΦ1, hΦ2, -⟩ := exists_mulEquiv_of_transversal (P := P₁)
    (H := (⊥ : Subgroup (Perm (Fin n₁)))) (P' := P₂) (H' := (⊥ : Subgroup (Perm (Fin n₂))))
    bot_le bot_le botEquivBot (m := m) (n := E₁.size) (g := g₁) (g' := g₂)
    (v := fun i => tablePerm n₁ E₁[i]!) (v' := fun i => tablePerm n₂ E₂[i]!)
    (σ := fun k i => (succ[i]!)[k]!) (hh := fun _ _ => 1) (hh' := fun _ _ => 1)
    hgP₁ hg₂P le_rfl hP₂ hpos₁ h0₁ h0₂ hmem₁ (fun i hi => hmem₂ i (hs ▸ hi))
    (fun i hi k hk => (hsucc i hi k hk).1) (fun _ _ _ _ => Subgroup.one_mem _)
    (fun _ _ _ _ => Subgroup.one_mem _) (fun _ _ _ _ _ => rfl) hsch hsch' hdist hdist'
  refine ⟨⟨hrep₁, hmem₁, ?_, hnodup₁⟩, Φ, ?_, ?_⟩
  · intro x hx
    obtain ⟨h, hh1, i, hi, rfl⟩ := hcov x hx
    have : h = 1 := Subgroup.mem_bot.1 hh1
    subst this
    refine ⟨i, hi, ?_⟩
    rw [one_mul]
    exact hrep₁ i hi
  · intro k hk hmem
    have h1 := hΦ1 1 (Subgroup.one_mem _) k hk
    have e : (⟨1 * tablePerm n₁ E₁[k]!, P₁.mul_mem (Subgroup.one_mem _) (hmem₁ k hk)⟩ :
        ↥P₁) = ⟨tablePerm n₁ E₁[k]!, hmem⟩ := Subtype.ext (one_mul _)
    rw [e] at h1
    rw [h1]
    simp [coe_botEquivBot]
  · intro l hl hmem
    exact hΦ2 l hl

theorem sideOK_spec {n : ℕ} (hn : n < 2 ^ 32) {G V E : Array Table}
    {succ : Array (Array (ℕ × ℕ))} {g v : ℕ → Perm (Fin n)} {H : Subgroup (Perm (Fin n))}
    (hg : ∀ k < G.size, Rep n G[k]! (g k)) (hv : ∀ i < V.size, Rep n V[i]! (v i))
    (hE : ExactEnum n H E) (h : sideOK n G V E succ = true) :
    0 < V.size ∧ v 0 = 1 ∧
    (∀ i < V.size, ∀ k < G.size, ((succ[i]!)[k]!).1 < V.size ∧ ((succ[i]!)[k]!).2 < E.size ∧
      v i * g k = tablePerm n E[((succ[i]!)[k]!).2]! * v ((succ[i]!)[k]!).1) ∧
    (∀ i < V.size, ∀ j < V.size, v i * (v j)⁻¹ ∈ H → i = j) := by
  classical
  simp only [sideOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hpos, h0⟩, -⟩, hsch⟩, hdist⟩ := h
  refine ⟨hpos, (tblEq_iff_eq (hv 0 hpos) (Rep.idT hn)).1 h0, ?_, ?_⟩
  · intro i hi k hk
    obtain ⟨-, hk'⟩ := hsch i hi
    obtain ⟨⟨hσ, hix⟩, e⟩ := hk' k hk
    refine ⟨hσ, hix, ?_⟩
    have hrepE := hE.rep _ hix
    have := (tblEq_iff_eq (Rep.compT (hv i hi) (hg k hk))
      (Rep.compT hrepE (hv _ hσ))).1 e
    exact this
  · intro i hi j hj hmem
    by_contra hne
    have hij := hdist i hi j hj
    have hij' : ¬ (i = j) := hne
    have hfalse : memT n E (compT n V[i]! (invT n V[j]!)) = false := by
      rcases hij with e | e
      · exact absurd e hij'
      · simpa using e
    obtain ⟨k, hk, hrk⟩ := hE.cover _ hmem
    have hrep : Rep n (compT n V[i]! (invT n V[j]!)) (v i * (v j)⁻¹) :=
      Rep.compT (hv i hi) (rep_invT_of_rep hn (hv j hj))
    have htrue : memT n E (compT n V[i]! (invT n V[j]!)) = true := by
      rw [memT, Array.any_eq_true]
      refine ⟨k, hk, ?_⟩
      rw [← getElem!_pos E k hk]
      exact (tblEq_iff_eq hrep hrk).2 rfl
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue

theorem exists_cosetEquiv {n₁ n₂ : ℕ} (hn₁ : n₁ < 2 ^ 32) (hn₂ : n₂ < 2 ^ 32) {m : ℕ}
    {G₁ G₂ V₁ V₂ E₁ E₂ : Array Table} {succ : Array (Array (ℕ × ℕ))}
    {g₁ v₁ : ℕ → Perm (Fin n₁)} {g₂ v₂ : ℕ → Perm (Fin n₂)}
    {P₁ H₁ : Subgroup (Perm (Fin n₁))} {P₂ H₂ : Subgroup (Perm (Fin n₂))}
    (hHP₁ : H₁ ≤ P₁) (hHP₂ : H₂ ≤ P₂) (hG₁ : G₁.size = m) (hG₂ : G₂.size = m)
    (hg₁ : ∀ k < m, Rep n₁ G₁[k]! (g₁ k)) (hg₂ : ∀ k < m, Rep n₂ G₂[k]! (g₂ k))
    (hgP₁ : ∀ k < m, g₁ k ∈ P₁) (hgP₂ : ∀ k < m, g₂ k ∈ P₂)
    (hgen₁ : P₁ ≤ Subgroup.closure (g₁ '' {k | k < m}))
    (hgen₂ : P₂ ≤ Subgroup.closure (g₂ '' {k | k < m}))
    (hV₁ : ∀ i < V₁.size, Rep n₁ V₁[i]! (v₁ i)) (hV₂ : ∀ i < V₂.size, Rep n₂ V₂[i]! (v₂ i))
    (hvP₁ : ∀ i < V₁.size, v₁ i ∈ P₁) (hvP₂ : ∀ i < V₂.size, v₂ i ∈ P₂)
    (hVs : V₂.size = V₁.size)
    (hE₁ : ExactEnum n₁ H₁ E₁) (hE₂ : ExactEnum n₂ H₂ E₂) (hEs : E₂.size = E₁.size)
    (ι : ↥H₁ ≃* ↥H₂)
    (hι : ∀ (k : ℕ) (_ : k < E₁.size) (hmem : tablePerm n₁ E₁[k]! ∈ H₁),
      ((ι ⟨tablePerm n₁ E₁[k]!, hmem⟩ : ↥H₂) : Perm (Fin n₂)) = tablePerm n₂ E₂[k]!)
    (h₁ : sideOK n₁ G₁ V₁ E₁ succ = true) (h₂ : sideOK n₂ G₂ V₂ E₂ succ = true) :
    ∃ Φ : ↥P₁ ≃* ↥P₂,
      (∀ (h : Perm (Fin n₁)) (hH : h ∈ H₁),
        ((Φ ⟨h, hHP₁ hH⟩ : ↥P₂) : Perm (Fin n₂)) = ((ι ⟨h, hH⟩ : ↥H₂) : Perm (Fin n₂))) ∧
      (∀ (k : ℕ) (hk : k < m), ((Φ ⟨g₁ k, hgP₁ k hk⟩ : ↥P₂) : Perm (Fin n₂)) = g₂ k) ∧
      Nat.card ↥P₁ = Nat.card ↥H₁ * V₁.size := by
  classical
  obtain ⟨hpos₁, hv0₁, hs₁, hd₁⟩ :=
    sideOK_spec hn₁ (fun k hk => hg₁ k (hG₁ ▸ hk)) hV₁ hE₁ h₁
  obtain ⟨hpos₂, hv0₂, hs₂, hd₂⟩ :=
    sideOK_spec hn₂ (fun k hk => hg₂ k (hG₂ ▸ hk)) hV₂ hE₂ h₂
  obtain ⟨Φ, hΦ1, hΦ2, hcard⟩ := exists_mulEquiv_of_transversal (P := P₁) (H := H₁) (P' := P₂)
    (H' := H₂) hHP₁ hHP₂ ι (m := m) (n := V₁.size) (g := g₁) (g' := g₂) (v := v₁) (v' := v₂)
    (σ := fun k i => ((succ[i]!)[k]!).1)
    (hh := fun k i => tablePerm n₁ E₁[((succ[i]!)[k]!).2]!)
    (hh' := fun k i => tablePerm n₂ E₂[((succ[i]!)[k]!).2]!)
    hgP₁ hgP₂ hgen₁ hgen₂ hpos₁ hv0₁ hv0₂ hvP₁ (fun i hi => hvP₂ i (hVs ▸ hi))
    (fun i hi k hk => (hs₁ i hi k (hG₁ ▸ hk)).1)
    (fun i hi k hk => hE₁.mem _ (hs₁ i hi k (hG₁ ▸ hk)).2.1)
    (fun i hi k hk => hE₂.mem _ (hEs ▸ (hs₁ i hi k (hG₁ ▸ hk)).2.1))
    (fun i hi k hk hmem => hι _ (hs₁ i hi k (hG₁ ▸ hk)).2.1 hmem)
    (fun i hi k hk => (hs₁ i hi k (hG₁ ▸ hk)).2.2)
    (fun i hi k hk => (hs₂ i (hVs ▸ hi) k (hG₂ ▸ hk)).2.2) hd₁
    (fun i hi j hj => hd₂ i (hVs ▸ hi) j (hVs ▸ hj))
  refine ⟨Φ, fun h hH => ?_, hΦ2, hcard⟩
  have h1 := hΦ1 h hH 0 hpos₁
  have e : (⟨h * v₁ 0, P₁.mul_mem (hHP₁ hH) (hvP₁ 0 hpos₁)⟩ : ↥P₁) = ⟨h, hHP₁ hH⟩ :=
    Subtype.ext (show h * v₁ 0 = h by rw [hv0₁, mul_one])
  rw [e, hv0₂, mul_one] at h1
  exact h1

end CFSG.Sporadic.Recognition.LyonsSims.Glue
