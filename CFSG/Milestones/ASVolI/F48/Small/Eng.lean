module

public import CFSG.Milestones.ASVolI.F48.Small.Core

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.CosetTable

section Sem

variable {N n : ℕ} {X : Subgroup (Equiv.Perm (Fin N))}

@[expose] def burnsideF48s_eRec (G : Fin n → ↥X) (LS LSi : List (List ℕ)) : Prop :=
  ∀ i : Fin n, RepL (LS.getD i []) ((G i : ↥X) : Equiv.Perm (Fin N)) ∧
    RepL (LSi.getD i []) (((G i)⁻¹ : ↥X) : Equiv.Perm (Fin N))

variable {G : Fin n → ↥X} {LS LSi : List (List ℕ)}

theorem burnsideF48s_e_ev_invW {H : Type*} [Group H] (h : Fin n → H) (w : List (Fin n × Bool)) :
    burnsideF48s_ev h (burnsideF48s_eInvW w) = (burnsideF48s_ev h w)⁻¹ := by
  induction w with
  | nil => simp [burnsideF48s_eInvW]
  | cons l w ih =>
    have e : burnsideF48s_eInvW (l :: w) = burnsideF48s_eInvW w ++ [(l.1, !l.2)] := by
      simp [burnsideF48s_eInvW]
    rw [e, burnsideF48s_ev_append, ih, burnsideF48s_ev_cons, burnsideF48s_ev_cons,
      burnsideF48s_ev_nil, mul_one, mul_inv_rev]
    obtain ⟨i, b⟩ := l
    cases b <;> simp

theorem burnsideF48s_e_repL (hG : burnsideF48s_eRec G LS LSi) (w : List (Fin n × Bool)) :
    RepL (burnsideF48s_eEvL N LS LSi w) ((burnsideF48s_ev G w : ↥X) : Equiv.Perm (Fin N)) := by
  have hlet : ∀ l : Fin n × Bool, RepL (burnsideF48s_eLetL LS LSi l)
      ((cond l.2 (G l.1) (G l.1)⁻¹ : ↥X) : Equiv.Perm (Fin N)) := by
    rintro ⟨i, b⟩
    cases b
    · exact (hG i).2
    · exact (hG i).1
  have key : ∀ (w : List (Fin n × Bool)) (acc : List ℕ) (σ : ↥X),
      RepL acc (σ : Equiv.Perm (Fin N)) →
      RepL (w.foldl (fun acc l => compL acc (burnsideF48s_eLetL LS LSi l)) acc)
        ((σ * burnsideF48s_ev G w : ↥X) : Equiv.Perm (Fin N)) := by
    intro w
    induction w with
    | nil =>
      intro acc σ h
      simpa using h
    | cons l w ih =>
      intro acc σ h
      rw [List.foldl_cons, burnsideF48s_ev_cons, ← mul_assoc]
      refine ih _ _ ?_
      rw [Subgroup.coe_mul]
      exact repL_mul h (hlet l)
  have := key w (List.range N) 1 (repL_one N)
  rwa [one_mul] at this

theorem burnsideF48s_e_eq (hG : burnsideF48s_eRec G LS LSi) {w w' : List (Fin n × Bool)}
    (h : burnsideF48s_eEvL N LS LSi w = burnsideF48s_eEvL N LS LSi w') :
    burnsideF48s_ev G w = burnsideF48s_ev G w' := by
  apply Subtype.ext
  have h' := burnsideF48s_e_repL hG w'
  rw [← h] at h'
  exact eq_of_repL (burnsideF48s_e_repL hG w) h'

theorem burnsideF48s_e_one (hG : burnsideF48s_eRec G LS LSi) {w : List (Fin n × Bool)}
    (h : burnsideF48s_eEvL N LS LSi w = List.range N) : burnsideF48s_ev G w = 1 := by
  apply Subtype.ext
  have h' := burnsideF48s_e_repL hG w
  rw [h] at h'
  exact eq_of_repL h' (repL_one N)

theorem burnsideF48s_e_repL_mul (hG : burnsideF48s_eRec G LS LSi) (w w' : List (Fin n × Bool)) :
    RepL (compL (burnsideF48s_eEvL N LS LSi w) (burnsideF48s_eEvL N LS LSi w'))
      ((burnsideF48s_ev G w * burnsideF48s_ev G w' : ↥X) : Equiv.Perm (Fin N)) := by
  rw [Subgroup.coe_mul]
  exact repL_mul (burnsideF48s_e_repL hG w) (burnsideF48s_e_repL hG w')

theorem burnsideF48s_e_mul_eq (hG : burnsideF48s_eRec G LS LSi) {w₁ w₂ w₃ w₄ : List (Fin n × Bool)}
    (h : compL (burnsideF48s_eEvL N LS LSi w₁) (burnsideF48s_eEvL N LS LSi w₂) =
      compL (burnsideF48s_eEvL N LS LSi w₃) (burnsideF48s_eEvL N LS LSi w₄)) :
    burnsideF48s_ev G w₁ * burnsideF48s_ev G w₂ = burnsideF48s_ev G w₃ * burnsideF48s_ev G w₄ := by
  apply Subtype.ext
  have h' := burnsideF48s_e_repL_mul hG w₃ w₄
  rw [← h] at h'
  exact eq_of_repL (burnsideF48s_e_repL_mul hG w₁ w₂) h'

theorem burnsideF48s_e_getD_map {α β : Type*} (f : α → β) (l : List α) {i : ℕ}
    (hi : i < l.length) (d : β) (d' : α) : (l.map f).getD i d = f (l.getD i d') := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
  simp

theorem burnsideF48s_e_getD_mem {α : Type*} (l : List α) {i : ℕ} (hi : i < l.length) (d : α) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

theorem burnsideF48s_e_mem_map {α β : Type*} {f : α → β} {l : List α} {b : β} (d : α)
    (h : b ∈ l.map f) : ∃ i < l.length, b = f (l.getD i d) := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]⟩

theorem burnsideF48s_e_cover (hG : burnsideF48s_eRec G LS LSi) {Ws : List (List (Fin n × Bool))}
    (hn : 0 < Ws.length) (h0 : Ws.getD 0 [] = []) {gs : List (Fin n)}
    (hcl : burnsideF48s_eClosed (Ws.map (burnsideF48s_eEvL N LS LSi)) LS (gs.map Fin.val) = true)
    {S : Set ↥X} (hS : ∀ s ∈ S, ∃ g ∈ gs, s = G g) :
    ∀ z ∈ Subgroup.closure S, ∃ i < Ws.length, z = burnsideF48s_ev G (Ws.getD i []) := by
  intro z hz
  have hsub := closure_subset_of_right_closed (S := S)
    (P := {z | ∃ i < Ws.length, z = burnsideF48s_ev G (Ws.getD i [])})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, hn, by rw [h0]; rfl⟩
    (fun p ⟨i, hi, hp⟩ s hs => by
      obtain ⟨g, hg', rfl⟩ := hS s hs
      simp only [burnsideF48s_eClosed, List.all_eq_true] at hcl
      have hmemi : burnsideF48s_eEvL N LS LSi (Ws.getD i []) ∈
          Ws.map (burnsideF48s_eEvL N LS LSi) :=
        List.mem_map_of_mem (burnsideF48s_e_getD_mem Ws hi [])
      have h1 := hcl _ hmemi g.val (List.mem_map_of_mem hg')
      rw [List.contains_iff_mem] at h1
      obtain ⟨j, hj, hjeq⟩ := burnsideF48s_e_mem_map [] h1
      refine ⟨j, hj, ?_⟩
      rw [hp]
      apply Subtype.ext
      have h2 : RepL (compL (burnsideF48s_eEvL N LS LSi (Ws.getD i [])) (LS.getD g.val []))
          ((burnsideF48s_ev G (Ws.getD i []) * G g : ↥X) : Equiv.Perm (Fin N)) := by
        rw [Subgroup.coe_mul]
        exact repL_mul (burnsideF48s_e_repL hG _) (hG g).1
      rw [hjeq] at h2
      exact eq_of_repL h2 (burnsideF48s_e_repL hG _))
  exact hsub hz

theorem burnsideF48s_e_cover_words (hG : burnsideF48s_eRec G LS LSi)
    {Ws gw : List (List (Fin n × Bool))} (hn : 0 < Ws.length) (h0 : Ws.getD 0 [] = [])
    (hcl : burnsideF48s_eClosedW (Ws.map (burnsideF48s_eEvL N LS LSi))
      (gw.map (burnsideF48s_eEvL N LS LSi)) = true)
    {S : Set ↥X} (hS : ∀ s ∈ S, ∃ w ∈ gw, s = burnsideF48s_ev G w) :
    ∀ z ∈ Subgroup.closure S, ∃ i < Ws.length, z = burnsideF48s_ev G (Ws.getD i []) := by
  intro z hz
  have hsub := closure_subset_of_right_closed (S := S)
    (P := {z | ∃ i < Ws.length, z = burnsideF48s_ev G (Ws.getD i [])})
    (fun s _ => ⟨orderOf s, orderOf_pos s, pow_orderOf_eq_one s⟩)
    ⟨0, hn, by rw [h0]; rfl⟩
    (fun p ⟨i, hi, hp⟩ s hs => by
      obtain ⟨w, hw, rfl⟩ := hS s hs
      simp only [burnsideF48s_eClosedW, List.all_eq_true] at hcl
      have hmemi : burnsideF48s_eEvL N LS LSi (Ws.getD i []) ∈
          Ws.map (burnsideF48s_eEvL N LS LSi) :=
        List.mem_map_of_mem (burnsideF48s_e_getD_mem Ws hi [])
      have h1 := hcl _ hmemi _ (List.mem_map_of_mem hw)
      rw [List.contains_iff_mem] at h1
      obtain ⟨j, hj, hjeq⟩ := burnsideF48s_e_mem_map [] h1
      refine ⟨j, hj, ?_⟩
      rw [hp]
      have h2 := burnsideF48s_e_repL_mul hG (Ws.getD i []) w
      rw [hjeq] at h2
      exact Subtype.ext (eq_of_repL h2 (burnsideF48s_e_repL hG _)))
  exact hsub hz

theorem burnsideF48s_e_card_of_cover (hG : burnsideF48s_eRec G LS LSi) {H : Subgroup ↥X}
    {Ws : List (List (Fin n × Bool))}
    (hcov : ∀ z ∈ H, ∃ i < Ws.length, z = burnsideF48s_ev G (Ws.getD i []))
    (hmem : ∀ i < Ws.length, burnsideF48s_ev G (Ws.getD i []) ∈ H)
    (hdist : (Ws.map (burnsideF48s_eEvL N LS LSi)).Nodup) : Nat.card ↥H = Ws.length := by
  let F : Fin Ws.length → ↥H := fun i => ⟨_, hmem i i.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun i j hij => ?_, fun z => ?_⟩
    · have e : burnsideF48s_ev G (Ws.getD i []) = burnsideF48s_ev G (Ws.getD j []) :=
        congrArg Subtype.val hij
      have e2 : burnsideF48s_eEvL N LS LSi (Ws.getD i []) =
          burnsideF48s_eEvL N LS LSi (Ws.getD j []) :=
        repL_unique (burnsideF48s_e_repL hG _) (e ▸ burnsideF48s_e_repL hG _)
      rw [← burnsideF48s_e_getD_map (burnsideF48s_eEvL N LS LSi) _ i.2 [] [],
        ← burnsideF48s_e_getD_map (burnsideF48s_eEvL N LS LSi) _ j.2 [] []] at e2
      have hi : (i : ℕ) < (Ws.map (burnsideF48s_eEvL N LS LSi)).length := by simp
      have hj : (j : ℕ) < (Ws.map (burnsideF48s_eEvL N LS LSi)).length := by simp
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at e2
      exact Fin.ext ((List.Nodup.getElem_inj_iff hdist).1 e2)
    · obtain ⟨i, hi, hz⟩ := hcov z z.2
      exact ⟨⟨i, hi⟩, Subtype.ext hz.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem burnsideF48s_e_closure_top {T : Set (Equiv.Perm (Fin N))} (hX : X = Subgroup.closure T)
    {S : Set ↥X} (hST : X.subtype '' S = T) : Subgroup.closure S = ⊤ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [MonoidHom.map_closure, hST, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hX]

end Sem

section Model

variable {N n : ℕ} {X : Subgroup (Equiv.Perm (Fin N))}

structure burnsideF48s_EModel (G : Fin n → ↥X) (LS LSi : List (List ℕ)) (P1 P2 K : Subgroup ↥X)
    (P1W P2W KW R1 R2 : List (List (Fin n × Bool))) : Prop where
  rep : burnsideF48s_eRec G LS LSi
  sup : P1 ⊔ P2 = ⊤
  K_le : K ≤ P1 ⊓ P2
  cov1 : ∀ z ∈ P1, ∃ i < P1W.length, z = burnsideF48s_ev G (P1W.getD i [])
  cov2 : ∀ z ∈ P2, ∃ j < P2W.length, z = burnsideF48s_ev G (P2W.getD j [])
  covK : ∀ z ∈ K, ∃ l < KW.length, z = burnsideF48s_ev G (KW.getD l [])
  let1 : ∀ i < P1W.length, ∀ l ∈ P1W.getD i [], G l.1 ∈ P1
  let2 : ∀ j < P2W.length, ∀ l ∈ P2W.getD j [], G l.1 ∈ P2
  memK : ∀ l < KW.length, burnsideF48s_ev G (KW.getD l []) ∈ K
  rel1 : ∀ r ∈ R1, (∀ l ∈ r, G l.1 ∈ P1) ∧ burnsideF48s_ev G r = 1
  rel2 : ∀ r ∈ R2, (∀ l ∈ r, G l.1 ∈ P2) ∧ burnsideF48s_ev G r = 1

structure burnsideF48s_ECands (G : Fin n → ↥X) (LS LSi : List (List ℕ)) (P1 P2 : Subgroup ↥X)
    (P1W P2W KW R1 R2 TW U V W : List (List (Fin n × Bool))) (m : ℕ) : Prop where
  lenV : U.length ≤ V.length
  lenW : U.length ≤ W.length
  letT : ∀ t < TW.length, ∀ l ∈ TW.getD t [], G l.1 ∈ P1 ⊓ P2
  letU : ∀ k < U.length, ∀ l ∈ U.getD k [], G l.1 ∈ P1
  letV : ∀ k < U.length, ∀ l ∈ V.getD k [], G l.1 ∈ P2
  letW : ∀ k < U.length, ∀ l ∈ W.getD k [], G l.1 ∈ P1 ⊓ P2
  cand : burnsideF48s_eCandOK (P1W.map (burnsideF48s_eEvL N LS LSi))
    (P2W.map (burnsideF48s_eEvL N LS LSi)) (KW.map (burnsideF48s_eEvL N LS LSi))
    (TW.map (burnsideF48s_eEvL N LS LSi)) (U.map (burnsideF48s_eEvL N LS LSi))
    (V.map (burnsideF48s_eEvL N LS LSi)) (W.map (burnsideF48s_eEvL N LS LSi)) = true
  tc : ∀ k < U.length,
    Finite (PG n (burnsideF48s_eWs R1 R2 m (U.getD k []) (V.getD k []) (W.getD k []))) ∧
      (Nat.card (PG n (burnsideF48s_eWs R1 R2 m (U.getD k []) (V.getD k []) (W.getD k []))) <
          Nat.card ↥X ∨
        (Nat.card (PG n (burnsideF48s_eWs R1 R2 m (U.getD k []) (V.getD k []) (W.getD k []))) ≤
            Nat.card ↥X ∧
          burnsideF48s_ev G (burnsideF48s_eCandRel m (U.getD k []) (V.getD k []) (W.getD k [])) =
            1))

variable {G : Fin n → ↥X} {LS LSi : List (List ℕ)} {P1 P2 K : Subgroup ↥X}
  {P1W P2W KW R1 R2 TW U V W : List (List (Fin n × Bool))} {m : ℕ}

theorem burnsideF48s_EModel.mem1 (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    {i : ℕ} (hi : i < P1W.length) : burnsideF48s_ev G (P1W.getD i []) ∈ P1 :=
  burnsideF48s_ev_mem G _ (hM.let1 i hi)

theorem burnsideF48s_EModel.mem2 (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    {j : ℕ} (hj : j < P2W.length) : burnsideF48s_ev G (P2W.getD j []) ∈ P2 :=
  burnsideF48s_ev_mem G _ (hM.let2 j hj)

theorem burnsideF48s_EModel.memKL (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    {z : ↥X} (hz : z ∈ K) {w : List (Fin n × Bool)} (hw : burnsideF48s_ev G w = z) :
    (KW.map (burnsideF48s_eEvL N LS LSi)).contains (burnsideF48s_eEvL N LS LSi w) = true := by
  obtain ⟨l, hl, rfl⟩ := hM.covK z hz
  rw [List.contains_iff_mem]
  have e : burnsideF48s_eEvL N LS LSi w = burnsideF48s_eEvL N LS LSi (KW.getD l []) :=
    repL_unique (burnsideF48s_e_repL hM.rep w) (hw ▸ burnsideF48s_e_repL hM.rep _)
  rw [e]
  exact List.mem_map_of_mem (burnsideF48s_e_getD_mem KW hl [])

theorem burnsideF48s_EModel.mem_of_contains2
    (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2) {w : List (Fin n × Bool)}
    (h : (P2W.map (burnsideF48s_eEvL N LS LSi)).contains (burnsideF48s_eEvL N LS LSi w) = true) :
    burnsideF48s_ev G w ∈ P2 := by
  rw [List.contains_iff_mem] at h
  obtain ⟨j, hj, e⟩ := burnsideF48s_e_mem_map [] h
  rw [burnsideF48s_e_eq hM.rep e]
  exact hM.mem2 hj

theorem burnsideF48s_EModel.mem_of_contains1
    (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2) {w : List (Fin n × Bool)}
    (h : (P1W.map (burnsideF48s_eEvL N LS LSi)).contains (burnsideF48s_eEvL N LS LSi w) = true) :
    burnsideF48s_ev G w ∈ P1 := by
  rw [List.contains_iff_mem] at h
  obtain ⟨i, hi, e⟩ := burnsideF48s_e_mem_map [] h
  rw [burnsideF48s_e_eq hM.rep e]
  exact hM.mem1 hi

theorem burnsideF48s_EModel.norm_of
    (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2) {w : List (Fin n × Bool)}
    (hK : ∀ k ∈ K, burnsideF48s_ev G w * k * (burnsideF48s_ev G w)⁻¹ ∈ K) :
    burnsideF48s_eNorm (KW.map (burnsideF48s_eEvL N LS LSi)) (burnsideF48s_eEvL N LS LSi w) =
      true := by
  simp only [burnsideF48s_eNorm, List.all_eq_true, List.any_eq_true, beq_iff_eq]
  intro kl hkl
  obtain ⟨l, hl, rfl⟩ := burnsideF48s_e_mem_map [] hkl
  have hk := hM.memK l hl
  have hconj := hK _ hk
  obtain ⟨l', hl', e'⟩ := hM.covK _ hconj
  refine ⟨_, List.mem_map_of_mem (burnsideF48s_e_getD_mem KW hl' []), ?_⟩
  have e2 : burnsideF48s_ev G w * burnsideF48s_ev G (KW.getD l []) =
      burnsideF48s_ev G (KW.getD l' []) * burnsideF48s_ev G w := by
    rw [← e']
    group
  exact repL_unique (burnsideF48s_e_repL_mul hM.rep _ _)
    (by rw [e2]; exact burnsideF48s_e_repL_mul hM.rep _ _)

theorem burnsideF48s_e_cand (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    (hC : burnsideF48s_ECands G LS LSi P1 P2 P1W P2W KW R1 R2 TW U V W m) {x y c : ↥X}
    (hx : x ∈ P1) (hx2 : x ∉ P2) (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hxx : x * x ∈ K)
    (hy : y ∈ P2) (hy1 : y ∉ P1) (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hyy : y * y ∈ K)
    (hc : c ∈ K) :
    ∃ t < TW.length, ∃ k < U.length,
      burnsideF48s_ev G (TW.getD t []) * x = burnsideF48s_ev G (U.getD k []) *
          burnsideF48s_ev G (TW.getD t []) ∧
        burnsideF48s_ev G (TW.getD t []) * y = burnsideF48s_ev G (V.getD k []) *
          burnsideF48s_ev G (TW.getD t []) ∧
        burnsideF48s_ev G (TW.getD t []) * c = burnsideF48s_ev G (W.getD k []) *
          burnsideF48s_ev G (TW.getD t []) := by
  obtain ⟨i, hi, rfl⟩ := hM.cov1 x hx
  obtain ⟨j, hj, rfl⟩ := hM.cov2 y hy
  obtain ⟨l, hl, rfl⟩ := hM.covK c hc
  have hC0 := hC.cand
  simp only [burnsideF48s_eCandOK, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hC0
  have hxi := hC0 _ (List.mem_map_of_mem (burnsideF48s_e_getD_mem P1W hi []))
  rcases hxi with ((h1 | h1) | h1) | hxi
  · rw [hM.norm_of hxK] at h1
    exact absurd h1 (by simp)
  · have h2 := hM.memKL hxx (w := P1W.getD i [] ++ P1W.getD i [])
      (by rw [burnsideF48s_ev_append])
    rw [show burnsideF48s_eEvL N LS LSi (P1W.getD i [] ++ P1W.getD i []) =
        compL (burnsideF48s_eEvL N LS LSi (P1W.getD i []))
          (burnsideF48s_eEvL N LS LSi (P1W.getD i [])) from
      repL_unique (burnsideF48s_e_repL hM.rep _)
        (by rw [burnsideF48s_ev_append]; exact burnsideF48s_e_repL_mul hM.rep _ _)] at h2
    rw [h2] at h1
    exact absurd h1 (by simp)
  · exact absurd (hM.mem_of_contains2 h1) hx2
  have hyj := hxi _ (List.mem_map_of_mem (burnsideF48s_e_getD_mem P2W hj []))
  rcases hyj with ((h1 | h1) | h1) | hyj
  · rw [hM.norm_of hyK] at h1
    exact absurd h1 (by simp)
  · have h2 := hM.memKL hyy (w := P2W.getD j [] ++ P2W.getD j [])
      (by rw [burnsideF48s_ev_append])
    rw [show burnsideF48s_eEvL N LS LSi (P2W.getD j [] ++ P2W.getD j []) =
        compL (burnsideF48s_eEvL N LS LSi (P2W.getD j []))
          (burnsideF48s_eEvL N LS LSi (P2W.getD j [])) from
      repL_unique (burnsideF48s_e_repL hM.rep _)
        (by rw [burnsideF48s_ev_append]; exact burnsideF48s_e_repL_mul hM.rep _ _)] at h2
    rw [h2] at h1
    exact absurd h1 (by simp)
  · exact absurd (hM.mem_of_contains1 h1) hy1
  have hcl := hyj _ (List.mem_map_of_mem (burnsideF48s_e_getD_mem KW hl []))
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hcl
  obtain ⟨tl, htl, k, hk, ⟨e1, e2⟩, e3⟩ := hcl
  obtain ⟨t, ht, rfl⟩ := burnsideF48s_e_mem_map [] htl
  rw [List.length_map] at hk
  rw [burnsideF48s_e_getD_map _ _ hk [] []] at e1
  rw [burnsideF48s_e_getD_map _ _ (hk.trans_le hC.lenV) [] []] at e2
  rw [burnsideF48s_e_getD_map _ _ (hk.trans_le hC.lenW) [] []] at e3
  exact ⟨t, ht, k, hk, burnsideF48s_e_mul_eq hM.rep e1, burnsideF48s_e_mul_eq hM.rep e2,
    burnsideF48s_e_mul_eq hM.rep e3⟩

end Model

section Core

variable {N n : ℕ} {X : Subgroup (Equiv.Perm (Fin N))} {G : Fin n → ↥X} {LS LSi : List (List ℕ)}
  {P1 P2 K : Subgroup ↥X} {P1W P2W KW R1 R2 TW U V W : List (List (Fin n × Bool))} {m : ℕ}

theorem burnsideF48s_e_core (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    (hC : burnsideF48s_ECands G LS LSi P1 P2 P1W P2W KW R1 R2 TW U V W m)
    {Y : Type} [Group Y] (f₁ : ↥P1 →* Y) (f₂ : ↥P2 →* Y)
    (h12 : ∀ (t : ↥X) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤) (hcard : Nat.card ↥X ≤ Nat.card Y)
    {x y c : ↥X} (hx : x ∈ P1) (hx2 : x ∉ P2) (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hxx : x * x ∈ K)
    (hy : y ∈ P2) (hy1 : y ∉ P1) (hyK : ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hyy : y * y ∈ K)
    (hc : c ∈ K) (hrel : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ m = f₁ ⟨c, (hM.K_le hc).1⟩) :
    ∃ φ : Y ≃* ↥X, (∀ z : ↥P1, φ (f₁ z) = z) ∧ ∀ z : ↥P2, φ (f₂ z) = z := by
  obtain ⟨t, ht, k, hk, ex, ey, ec⟩ := burnsideF48s_e_cand hM hC hx hx2 hxK hxx hy hy1 hyK hyy hc
  have hTB : burnsideF48s_ev G (TW.getD t []) ∈ P1 ⊓ P2 := burnsideF48s_ev_mem G _ (hC.letT t ht)
  set T := burnsideF48s_ev G (TW.getD t []) with hT
  have hU : ∀ l ∈ U.getD k [], G l.1 ∈ P1 := hC.letU k hk
  have hV : ∀ l ∈ V.getD k [], G l.1 ∈ P2 := hC.letV k hk
  have hW1 : ∀ l ∈ W.getD k [], G l.1 ∈ P1 := fun l hl => (hC.letW k hk l hl).1
  obtain ⟨mU, eU⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) _ hU
  obtain ⟨mV, eV⟩ := burnsideF48s_ev_yL_B (f₁ := f₁) (f₂ := f₂) h12 _ hV
  obtain ⟨mW, eW⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) _ hW1
  have eu : burnsideF48s_ev G (U.getD k []) = T * x * T⁻¹ := by rw [ex]; group
  have ev' : burnsideF48s_ev G (V.getD k []) = T * y * T⁻¹ := by rw [ey]; group
  have ew : burnsideF48s_ev G (W.getD k []) = T * c * T⁻¹ := by rw [ec]; group
  have fU : f₁ ⟨_, mU⟩ = f₁ ⟨T, hTB.1⟩ * f₁ ⟨x, hx⟩ * (f₁ ⟨T, hTB.1⟩)⁻¹ := by
    have e : (⟨_, mU⟩ : ↥P1) = ⟨T, hTB.1⟩ * ⟨x, hx⟩ * (⟨T, hTB.1⟩ : ↥P1)⁻¹ := Subtype.ext eu
    rw [e, map_mul, map_mul, map_inv]
  have fV : f₂ ⟨_, mV⟩ = f₁ ⟨T, hTB.1⟩ * f₂ ⟨y, hy⟩ * (f₁ ⟨T, hTB.1⟩)⁻¹ := by
    have e : (⟨_, mV⟩ : ↥P2) = ⟨T, hTB.2⟩ * ⟨y, hy⟩ * (⟨T, hTB.2⟩ : ↥P2)⁻¹ := Subtype.ext ev'
    rw [e, map_mul, map_mul, map_inv, ← h12 T hTB]
  have fW : f₁ ⟨_, mW⟩ = f₁ ⟨T, hTB.1⟩ * f₁ ⟨c, (hM.K_le hc).1⟩ * (f₁ ⟨T, hTB.1⟩)⁻¹ := by
    have e : (⟨_, mW⟩ : ↥P1) = ⟨T, hTB.1⟩ * ⟨c, (hM.K_le hc).1⟩ * (⟨T, hTB.1⟩ : ↥P1)⁻¹ :=
      Subtype.ext ew
    rw [e, map_mul, map_mul, map_inv]
  set yL := burnsideF48s_yL G f₁ f₂ with hyL
  have hcandY : burnsideF48s_ev yL
      (burnsideF48s_eCandRel m (U.getD k []) (V.getD k []) (W.getD k [])) = 1 := by
    unfold burnsideF48s_eCandRel
    rw [burnsideF48s_ev_append, burnsideF48s_ev_replicate, burnsideF48s_ev_append,
      burnsideF48s_e_ev_invW, eU, eV, eW, fU, fV, fW]
    have e : f₁ ⟨T, hTB.1⟩ * f₁ ⟨x, hx⟩ * (f₁ ⟨T, hTB.1⟩)⁻¹ *
        (f₁ ⟨T, hTB.1⟩ * f₂ ⟨y, hy⟩ * (f₁ ⟨T, hTB.1⟩)⁻¹) =
        f₁ ⟨T, hTB.1⟩ * (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) * (f₁ ⟨T, hTB.1⟩)⁻¹ := by
      group
    rw [e, conj_pow, hrel]
    group
  have hrelY : ∀ r ∈ R1 ++ R2, burnsideF48s_ev yL r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with hr1 | hr2
    · obtain ⟨hl, h1⟩ := hM.rel1 r hr1
      obtain ⟨mr, e⟩ := burnsideF48s_ev_yL_A (f₁ := f₁) (f₂ := f₂) r hl
      rw [e]
      have : (⟨_, mr⟩ : ↥P1) = 1 := Subtype.ext h1
      rw [this, map_one]
    · obtain ⟨hl, h1⟩ := hM.rel2 r hr2
      obtain ⟨mr, e⟩ := burnsideF48s_ev_yL_B (f₁ := f₁) (f₂ := f₂) h12 r hl
      rw [e]
      have : (⟨_, mr⟩ : ↥P2) = 1 := Subtype.ext h1
      rw [this, map_one]
  have hY : ∀ r ∈ burnsideF48s_eWs R1 R2 m (U.getD k []) (V.getD k []) (W.getD k []),
      burnsideF48s_ev yL r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact hrelY r h
    · rw [List.mem_singleton] at h
      rw [h]
      exact hcandY
  have hcov1 : ∀ z ∈ P1, ∃ w : List (Fin n × Bool), (∀ l ∈ w, G l.1 ∈ P1) ∧
      burnsideF48s_ev G w = z := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := hM.cov1 z hz
    exact ⟨_, hM.let1 i hi, rfl⟩
  have hcov2 : ∀ z ∈ P2, ∃ w : List (Fin n × Bool), (∀ l ∈ w, G l.1 ∈ P2) ∧
      burnsideF48s_ev G w = z := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := hM.cov2 z hz
    exact ⟨_, hM.let2 j hj, rfl⟩
  obtain ⟨hfin, htc⟩ := hC.tc k hk
  haveI := hfin
  have hYle := burnsideF48s_core_card_le (L := G) (f₁ := f₁) (f₂ := f₂) h12 hgen hcov1 hcov2 hY
  rcases htc with hlt | ⟨hle, hX1⟩
  · exact absurd (hcard.trans hYle) (not_le.2 hlt)
  · have hD : ∀ r ∈ burnsideF48s_eWs R1 R2 m (U.getD k []) (V.getD k []) (W.getD k []),
        burnsideF48s_ev G r = 1 := by
      intro r hr
      rcases List.mem_append.1 hr with h | h
      · rcases List.mem_append.1 h with h1 | h2
        · exact (hM.rel1 r h1).2
        · exact (hM.rel2 r h2).2
      · rw [List.mem_singleton] at h
        rw [h]
        exact hX1
    exact burnsideF48s_core_gen h12 hgen hM.sup hcov1 hcov2 hD hY hle hcard

end Core

section QE

open CFSG.Open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

variable {N n : ℕ} {X : Subgroup (Equiv.Perm (Fin N))} {G : Fin n → ↥X} {LS LSi : List (List ℕ)}
  {P1 P2 K : Subgroup ↥X} {P1W P2W KW R1 R2 TW U V W : List (List (Fin n × Bool))} {m : ℕ}

theorem burnsideF48s_e_conj_inv_mem {H : Type*} [Group H] {L : Subgroup H} [Finite ↥L] {a : H}
    (h : ∀ k ∈ L, a * k * a⁻¹ ∈ L) : ∀ k ∈ L, a⁻¹ * k * a ∈ L := by
  have hle : L.map (MulAut.conj a).toMonoidHom ≤ L := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have heq : L.map (MulAut.conj a).toMonoidHom = L :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj a).injective])
  intro k hk
  rw [← heq] at hk
  obtain ⟨k₁, hk₁, e⟩ := hk
  have e' : a⁻¹ * k * a = k₁ := by
    rw [← e]
    show a⁻¹ * (a * k₁ * a⁻¹) * a = k₁
    group
  rw [e']
  exact hk₁

theorem burnsideF48s_e_core_conj (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    (hC : burnsideF48s_ECands G LS LSi P1 P2 P1W P2W KW R1 R2 TW U V W m)
    {Y : Type} [Group Y] (f₁ : ↥P1 →* Y) (f₂ : ↥P2 →* Y)
    (h12 : ∀ (t : ↥X) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤) (hcard : Nat.card ↥X ≤ Nat.card Y)
    {K'' : Subgroup ↥X} (hK''le : K'' ≤ P1 ⊓ P2) {t : ↥X} (ht : t ∈ P1 ⊓ P2)
    (hiff : ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ K)
    {x y c : ↥X} (hx : x ∈ P1) (hx2 : x ∉ P2) (hxK : ∀ k ∈ K'', x * k * x⁻¹ ∈ K'')
    (hxx : x * x ∈ K'') (hy : y ∈ P2) (hy1 : y ∉ P1) (hyK : ∀ k ∈ K'', y * k * y⁻¹ ∈ K'')
    (hyy : y * y ∈ K'') (hc : c ∈ K'')
    (hrel : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ m = f₁ ⟨c, (hK''le hc).1⟩) :
    ∃ φ : Y ≃* ↥X, (∀ z : ↥P1, φ (f₁ z) = z) ∧ ∀ z : ↥P2, φ (f₂ z) = z := by
  have hconjK : ∀ {z : ↥X}, (∀ k ∈ K'', z * k * z⁻¹ ∈ K'') →
      ∀ k ∈ K, (t * z * t⁻¹) * k * (t * z * t⁻¹)⁻¹ ∈ K := by
    intro z hz k hk
    have h1 : t⁻¹ * k * t ∈ K'' := (hiff _).2 (by simpa [mul_assoc] using hk)
    have h2 := (hiff _).1 (hz _ h1)
    have e : t * (z * (t⁻¹ * k * t) * z⁻¹) * t⁻¹ = (t * z * t⁻¹) * k * (t * z * t⁻¹)⁻¹ := by group
    rwa [e] at h2
  have hsq : ∀ {z : ↥X}, z * z ∈ K'' → (t * z * t⁻¹) * (t * z * t⁻¹) ∈ K := by
    intro z hz
    have e : t * (z * z) * t⁻¹ = (t * z * t⁻¹) * (t * z * t⁻¹) := by group
    rw [← e]
    exact (hiff _).1 hz
  have hx' : t * x * t⁻¹ ∈ P1 := P1.mul_mem (P1.mul_mem ht.1 hx) (P1.inv_mem ht.1)
  have hy' : t * y * t⁻¹ ∈ P2 := P2.mul_mem (P2.mul_mem ht.2 hy) (P2.inv_mem ht.2)
  have hx2' : t * x * t⁻¹ ∉ P2 := fun h => hx2 (by
    have := P2.mul_mem (P2.mul_mem (P2.inv_mem ht.2) h) ht.2
    simpa [mul_assoc] using this)
  have hy1' : t * y * t⁻¹ ∉ P1 := fun h => hy1 (by
    have := P1.mul_mem (P1.mul_mem (P1.inv_mem ht.1) h) ht.1
    simpa [mul_assoc] using this)
  have hc' : t * c * t⁻¹ ∈ K := (hiff _).1 hc
  have hrel' : (f₁ ⟨t * x * t⁻¹, hx'⟩ * f₂ ⟨t * y * t⁻¹, hy'⟩) ^ m =
      f₁ ⟨t * c * t⁻¹, (hM.K_le hc').1⟩ := by
    have e1 : (⟨t * x * t⁻¹, hx'⟩ : ↥P1) = ⟨t, ht.1⟩ * ⟨x, hx⟩ * (⟨t, ht.1⟩ : ↥P1)⁻¹ := rfl
    have e2 : (⟨t * y * t⁻¹, hy'⟩ : ↥P2) = ⟨t, ht.2⟩ * ⟨y, hy⟩ * (⟨t, ht.2⟩ : ↥P2)⁻¹ := rfl
    have e3 : (⟨t * c * t⁻¹, (hM.K_le hc').1⟩ : ↥P1) =
        ⟨t, ht.1⟩ * ⟨c, (hK''le hc).1⟩ * (⟨t, ht.1⟩ : ↥P1)⁻¹ := rfl
    rw [e1, e2, e3, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
      ← h12 t ht]
    have e : f₁ ⟨t, ht.1⟩ * f₁ ⟨x, hx⟩ * (f₁ ⟨t, ht.1⟩)⁻¹ *
        (f₁ ⟨t, ht.1⟩ * f₂ ⟨y, hy⟩ * (f₁ ⟨t, ht.1⟩)⁻¹) =
        f₁ ⟨t, ht.1⟩ * (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) * (f₁ ⟨t, ht.1⟩)⁻¹ := by
      group
    rw [e, conj_pow, hrel]
  exact burnsideF48s_e_core hM hC f₁ f₂ h12 hgen hcard hx' hx2' (hconjK hxK) (hsq hxx) hy' hy1'
    (hconjK hyK) (hsq hyy) hc' hrel'

theorem burnsideF48s_e_core' (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    (hC : burnsideF48s_ECands G LS LSi P1 P2 P1W P2W KW R1 R2 TW U V W m)
    (hconj : ∀ K'' : Subgroup ↥X, K'' ≤ P1 ⊓ P2 → Nat.card ↥K'' = Nat.card ↥K →
      ∃ t ∈ P1 ⊓ P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ K)
    {Y : Type} [Group Y] (f₁ : ↥P1 →* Y) (f₂ : ↥P2 →* Y)
    (h12 : ∀ (t : ↥X) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩)
    (hgen : f₁.range ⊔ f₂.range = ⊤) (hcard : Nat.card ↥X ≤ Nat.card Y)
    {K'' : Subgroup ↥X} (hK''le : K'' ≤ P1 ⊓ P2) (hK''card : Nat.card ↥K'' = Nat.card ↥K)
    {x y c : ↥X} (hx : x ∈ P1) (hx2 : x ∉ P2) (hxK : ∀ k ∈ K'', x * k * x⁻¹ ∈ K'')
    (hxx : x * x ∈ K'') (hy : y ∈ P2) (hy1 : y ∉ P1) (hyK : ∀ k ∈ K'', y * k * y⁻¹ ∈ K'')
    (hyy : y * y ∈ K'') (hc : c ∈ K'')
    (hrel : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ m = f₁ ⟨c, (hK''le hc).1⟩) :
    ∃ φ : Y ≃* ↥X, (∀ z : ↥P1, φ (f₁ z) = z) ∧ ∀ z : ↥P2, φ (f₂ z) = z := by
  obtain ⟨t, ht, hiff⟩ := hconj K'' hK''le hK''card
  exact burnsideF48s_e_core_conj hM hC f₁ f₂ h12 hgen hcard hK''le ht hiff hx hx2 hxK hxx hy hy1
    hyK hyy hc hrel

@[expose] def burnsideF48s_ECore {N : ℕ} {X : Subgroup (Equiv.Perm (Fin N))} (P1 P2 : Subgroup ↥X)
    (m : ℕ) (Q : Subgroup ↥X → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] (f₁ : ↥P1 →* Y) (f₂ : ↥P2 →* Y),
    (∀ (t : ↥X) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩) → f₁.range ⊔ f₂.range = ⊤ →
    Nat.card ↥X ≤ Nat.card Y → ∀ (K'' : Subgroup ↥X) (hK''le : K'' ≤ P1 ⊓ P2), Q K'' →
    ∀ (x y c : ↥X) (hx : x ∈ P1) (hy : y ∈ P2) (hc : c ∈ K''), x ∉ P2 →
      (∀ k ∈ K'', x * k * x⁻¹ ∈ K'') → x * x ∈ K'' → y ∉ P1 →
      (∀ k ∈ K'', y * k * y⁻¹ ∈ K'') → y * y ∈ K'' →
      (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ m = f₁ ⟨c, (hK''le hc).1⟩ →
      ∃ φ : Y ≃* ↥X, (∀ z : ↥P1, φ (f₁ z) = z) ∧ ∀ z : ↥P2, φ (f₂ z) = z

theorem burnsideF48s_e_ecore (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    (hC : burnsideF48s_ECands G LS LSi P1 P2 P1W P2W KW R1 R2 TW U V W m)
    (hconj : ∀ K'' : Subgroup ↥X, K'' ≤ P1 ⊓ P2 → Nat.card ↥K'' = Nat.card ↥K →
      ∃ t ∈ P1 ⊓ P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ K) :
    burnsideF48s_ECore P1 P2 m (fun K'' => Nat.card ↥K'' = Nat.card ↥K) :=
  fun _ _ f₁ f₂ h12 hgen hcard _ hK''le hQ _ _ _ hx hy hc hx2 hxK hxx hy1 hyK hyy hrel =>
    burnsideF48s_e_core' hM hC hconj f₁ f₂ h12 hgen hcard hK''le hQ hx hx2 hxK hxx hy hy1 hyK hyy
      hc hrel

theorem burnsideF48s_e_ecore_multi {r : ℕ} {Ks : Fin r → Subgroup ↥X}
    {KWs TWs Us Vs Ws : Fin r → List (List (Fin n × Bool))}
    (hMs : ∀ j, burnsideF48s_EModel G LS LSi P1 P2 (Ks j) P1W P2W (KWs j) R1 R2)
    (hCs : ∀ j, burnsideF48s_ECands G LS LSi P1 P2 P1W P2W (KWs j) R1 R2 (TWs j) (Us j) (Vs j)
      (Ws j) m)
    {Q : Subgroup ↥X → Prop}
    (hconj : ∀ K'' : Subgroup ↥X, K'' ≤ P1 ⊓ P2 → Q K'' →
      ∃ j, ∃ t ∈ P1 ⊓ P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ Ks j) :
    burnsideF48s_ECore P1 P2 m Q := by
  intro _ _ f₁ f₂ h12 hgen hcard K'' hK''le hQ x y c hx hy hc hx2 hxK hxx hy1 hyK hyy hrel
  obtain ⟨j, t, ht, hiff⟩ := hconj K'' hK''le hQ
  exact burnsideF48s_e_core_conj (hMs j) (hCs j) f₁ f₂ h12 hgen hcard hK''le ht hiff hx hx2 hxK hxx
    hy hy1 hyK hyy hc hrel

theorem burnsideF48s_e_range_comp {A B C : Type*} [Group A] [Group B] [Group C] (g : B →* C)
    (e : A ≃* B) : (g.comp e.toMonoidHom).range = g.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map]

theorem burnsideF48s_e_qe_of_core {Q : Subgroup ↥X → Prop} (hcore : burnsideF48s_ECore P1 P2 m Q)
    {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E} (θ : ↥X ≃* E)
    {A₁ A₂ : Subgroup ↥X} (hA : (A₁ = P1 ∧ A₂ = P2) ∨ (A₁ = P2 ∧ A₂ = P1))
    (hM1 : M₁ = A₁.map θ.toMonoidHom) (hM2 : M₂ = A₂.map θ.toMonoidHom) (hgen : M₁ ⊔ M₂ = ⊤)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hcard : Nat.card ↥X ≤ Nat.card Y)
    {a : ↥M₁} {b : ↥M₂} {K' : Subgroup E} (haM : (a : E) ∉ M₂) (hbM : (b : E) ∉ M₁)
    (hK'le : K' ≤ M₁ ⊓ M₂) (hQ : Q (K'.comap θ.toMonoidHom))
    (haK : ∀ k ∈ K', (a : E) * k * (a : E)⁻¹ ∈ K') (hbK : ∀ k ∈ K', (b : E) * k * (b : E)⁻¹ ∈ K')
    (ha2 : (a : E) * a ∈ K') (hb2 : (b : E) * b ∈ K')
    {c : ↥(M₁ ⊓ M₂)} (hcK : (c : E) ∈ K') (hrel : (β.φ1 a * β.φ2 b) ^ m = β.φ12 c) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion := by
  let eG : ↥(M₁ ⊔ M₂) ≃* E := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have h12β : ∀ (t : E) (h1 : t ∈ M₁) (h2 : t ∈ M₂), β.φ1 ⟨t, h1⟩ = β.φ2 ⟨t, h2⟩ :=
    fun t h1 h2 => (β.comm1 ⟨t, ⟨h1, h2⟩⟩).trans (β.comm2 ⟨t, ⟨h1, h2⟩⟩).symm
  have hmemθ : ∀ {A : Subgroup ↥X} {M : Subgroup E}, M = A.map θ.toMonoidHom →
      ∀ z, θ z ∈ M ↔ z ∈ A := by
    intro A M hM z
    rw [hM]
    exact Subgroup.mem_map_iff_mem θ.injective
  have hpre : ∀ {A : Subgroup ↥X} {M : Subgroup E}, M = A.map θ.toMonoidHom →
      ∀ u : ↥M, ∃ z, z ∈ A ∧ θ z = u := by
    intro A M hM u
    obtain ⟨z, hz, hzu⟩ : (u : E) ∈ A.map θ.toMonoidHom := by rw [← hM]; exact u.2
    exact ⟨z, hz, hzu⟩
  set K'' : Subgroup ↥X := K'.comap θ.toMonoidHom with hK''
  have hθK : ∀ z, z ∈ K'' ↔ θ z ∈ K' := fun z => Iff.rfl
  have hB : ∀ z, θ z ∈ M₁ ⊓ M₂ ↔ z ∈ P1 ⊓ P2 := by
    intro z
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hmemθ hM1, hmemθ hM2]
    rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Iff.rfl
    · exact and_comm
  have hK''le : K'' ≤ P1 ⊓ P2 := fun z hz => (hB z).1 (hK'le ((hθK z).1 hz))
  have hK'fin : Finite ↥K' := inferInstance
  have hconjE : ∀ {z : E}, (∀ k ∈ K', z * k * z⁻¹ ∈ K') → ∀ z₀ : ↥X, θ z₀ = z →
      ∀ k ∈ K'', z₀ * k * z₀⁻¹ ∈ K'' := by
    intro z hz z₀ hz₀ k hk
    rw [hθK, map_mul, map_mul, map_inv, hz₀]
    exact hz _ ((hθK k).1 hk)
  have hsqE : ∀ {z : E}, z * z ∈ K' → ∀ z₀ : ↥X, θ z₀ = z → z₀ * z₀ ∈ K'' := by
    intro z hz z₀ hz₀
    rw [hθK, map_mul, hz₀]
    exact hz
  rcases hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
  · rw [hA1] at hM1
    rw [hA2] at hM2
    let r₁ : ↥P1 ≃* ↥M₁ := (θ.subgroupMap P1).trans (MulEquiv.subgroupCongr hM1.symm)
    let r₂ : ↥P2 ≃* ↥M₂ := (θ.subgroupMap P2).trans (MulEquiv.subgroupCongr hM2.symm)
    let f₁ : ↥P1 →* Y := β.φ1.comp r₁.toMonoidHom
    let f₂ : ↥P2 →* Y := β.φ2.comp r₂.toMonoidHom
    have hf12 : ∀ (t : ↥X) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ := fun t h =>
      h12β (θ t) _ _
    have hfgen : f₁.range ⊔ f₂.range = ⊤ := by
      rw [show f₁.range = β.φ1.range from burnsideF48s_e_range_comp _ _,
        show f₂.range = β.φ2.range from burnsideF48s_e_range_comp _ _]
      exact β.gen
    obtain ⟨x, hx, hxa⟩ := hpre hM1 a
    obtain ⟨y, hy, hyb⟩ := hpre hM2 b
    obtain ⟨c₀, hc₀, hc₀c⟩ := hpre (A := P1) hM1 ⟨c, c.2.1⟩
    have hx2 : x ∉ P2 := fun h => haM (hxa ▸ (hmemθ hM2 x).2 h)
    have hy1 : y ∉ P1 := fun h => hbM (hyb ▸ (hmemθ hM1 y).2 h)
    have hcK'' : c₀ ∈ K'' := by rw [hθK, hc₀c]; exact hcK
    have hra : r₁ ⟨x, hx⟩ = a := Subtype.ext hxa
    have hrb : r₂ ⟨y, hy⟩ = b := Subtype.ext hyb
    have hrc : r₁ ⟨c₀, (hK''le hcK'').1⟩ = ⟨c, c.2.1⟩ := Subtype.ext hc₀c
    have hrel' : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ m = f₁ ⟨c₀, (hK''le hcK'').1⟩ := by
      show (β.φ1 (r₁ ⟨x, hx⟩) * β.φ2 (r₂ ⟨y, hy⟩)) ^ m = β.φ1 (r₁ ⟨c₀, (hK''le hcK'').1⟩)
      rw [hra, hrb, hrc, hrel]
      exact (β.comm1 c).symm
    obtain ⟨φ, hφ1, hφ2⟩ := hcore Y f₁ f₂ hf12 hfgen hcard K'' hK''le hQ x y c₀ hx hy hcK'' hx2
      (hconjE haK x hxa) (hsqE ha2 x hxa) hy1 (hconjE hbK y hyb) (hsqE hb2 y hyb) hrel'
    refine burnsideF48s_qe_of_equiv β hβ (φ.trans (θ.trans eG.symm)) (fun u => ?_) (fun u => ?_)
    · obtain ⟨z, hz, hzu⟩ := hpre hM1 u
      have hu : u = r₁ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₁ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ1]
      exact (hmemθ hM1 z).2 hz
    · obtain ⟨z, hz, hzu⟩ := hpre hM2 u
      have hu : u = r₂ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₂ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ2]
      exact (hmemθ hM2 z).2 hz
  · rw [hA1] at hM1
    rw [hA2] at hM2
    let r₁ : ↥P1 ≃* ↥M₂ := (θ.subgroupMap P1).trans (MulEquiv.subgroupCongr hM2.symm)
    let r₂ : ↥P2 ≃* ↥M₁ := (θ.subgroupMap P2).trans (MulEquiv.subgroupCongr hM1.symm)
    let f₁ : ↥P1 →* Y := β.φ2.comp r₁.toMonoidHom
    let f₂ : ↥P2 →* Y := β.φ1.comp r₂.toMonoidHom
    have hf12 : ∀ (t : ↥X) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ := fun t h =>
      (h12β (θ t) _ _).symm
    have hfgen : f₁.range ⊔ f₂.range = ⊤ := by
      rw [show f₁.range = β.φ2.range from burnsideF48s_e_range_comp _ _,
        show f₂.range = β.φ1.range from burnsideF48s_e_range_comp _ _, sup_comm]
      exact β.gen
    have haK' := burnsideF48s_e_conj_inv_mem haK
    have hd : (a : E)⁻¹ * c * a ∈ K' := haK' _ hcK
    have hdM := hK'le hd
    obtain ⟨x, hx, hxb⟩ := hpre hM2 b
    obtain ⟨y, hy, hya⟩ := hpre hM1 a
    obtain ⟨d₀, hd₀, hd₀d⟩ := hpre (A := P1) hM2 ⟨_, hdM.2⟩
    have hx2 : x ∉ P2 := fun h => hbM (hxb ▸ (hmemθ hM1 x).2 h)
    have hy1 : y ∉ P1 := fun h => haM (hya ▸ (hmemθ hM2 y).2 h)
    have hdK'' : d₀ ∈ K'' := by rw [hθK, hd₀d]; exact hd
    have hrb : r₁ ⟨x, hx⟩ = b := Subtype.ext hxb
    have hra : r₂ ⟨y, hy⟩ = a := Subtype.ext hya
    have hrd : r₁ ⟨d₀, (hK''le hdK'').1⟩ = ⟨_, hdM.2⟩ := Subtype.ext hd₀d
    have hrel' : (f₁ ⟨x, hx⟩ * f₂ ⟨y, hy⟩) ^ m = f₁ ⟨d₀, (hK''le hdK'').1⟩ := by
      show (β.φ2 (r₁ ⟨x, hx⟩) * β.φ1 (r₂ ⟨y, hy⟩)) ^ m = β.φ2 (r₁ ⟨d₀, (hK''le hdK'').1⟩)
      rw [hrb, hra, hrd, ← h12β _ hdM.1 hdM.2]
      have e1 : (⟨(a : E)⁻¹ * c * a, hdM.1⟩ : ↥M₁) = a⁻¹ * ⟨c, c.2.1⟩ * a := rfl
      have e2 : (β.φ2 b * β.φ1 a) ^ m = (β.φ1 a)⁻¹ * (β.φ1 a * β.φ2 b) ^ m * β.φ1 a := by
        rw [show (β.φ1 a)⁻¹ * (β.φ1 a * β.φ2 b) ^ m * β.φ1 a =
            ((β.φ1 a)⁻¹ * (β.φ1 a * β.φ2 b) * ((β.φ1 a)⁻¹)⁻¹) ^ m by rw [conj_pow, inv_inv]]
        congr 1
        group
      have e3 : ∀ u v w : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
          β.φ1 (u⁻¹ * v * w) = (β.φ1 u)⁻¹ * β.φ1 v * β.φ1 w := by
        intro u v w
        rw [map_mul, map_mul, map_inv]
      rw [e2, hrel]
      have e5 : β.φ1 ⟨(a : E)⁻¹ * c * a, hdM.1⟩ = (β.φ1 a)⁻¹ * β.φ1 ⟨c, c.2.1⟩ * β.φ1 a :=
        (congrArg β.φ1 e1).trans (e3 a ⟨c, c.2.1⟩ a)
      rw [e5]
      exact congrArg (fun z => (β.φ1 a)⁻¹ * z * β.φ1 a) (β.comm1 c).symm
    obtain ⟨φ, hφ1, hφ2⟩ := hcore Y f₁ f₂ hf12 hfgen hcard K'' hK''le hQ x y d₀ hx hy hdK'' hx2
      (hconjE hbK x hxb) (hsqE hb2 x hxb) hy1 (hconjE haK y hya) (hsqE ha2 y hya) hrel'
    refine burnsideF48s_qe_of_equiv β hβ (φ.trans (θ.trans eG.symm)) (fun u => ?_) (fun u => ?_)
    · obtain ⟨z, hz, hzu⟩ := hpre hM1 u
      have hu : u = r₂ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₂ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ2]
      exact (hmemθ hM1 z).2 hz
    · obtain ⟨z, hz, hzu⟩ := hpre hM2 u
      have hu : u = r₁ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₁ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ1]
      exact (hmemθ hM2 z).2 hz

theorem burnsideF48s_e_qe (hM : burnsideF48s_EModel G LS LSi P1 P2 K P1W P2W KW R1 R2)
    (hC : burnsideF48s_ECands G LS LSi P1 P2 P1W P2W KW R1 R2 TW U V W m)
    (hconj : ∀ K'' : Subgroup ↥X, K'' ≤ P1 ⊓ P2 → Nat.card ↥K'' = Nat.card ↥K →
      ∃ t ∈ P1 ⊓ P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ K)
    {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E} (θ : ↥X ≃* E)
    {A₁ A₂ : Subgroup ↥X} (hA : (A₁ = P1 ∧ A₂ = P2) ∨ (A₁ = P2 ∧ A₂ = P1))
    (hM1 : M₁ = A₁.map θ.toMonoidHom) (hM2 : M₂ = A₂.map θ.toMonoidHom) (hgen : M₁ ⊔ M₂ = ⊤)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hcard : Nat.card ↥X ≤ Nat.card Y)
    {a : ↥M₁} {b : ↥M₂} {K' : Subgroup E} (haM : (a : E) ∉ M₂) (hbM : (b : E) ∉ M₁)
    (hK'le : K' ≤ M₁ ⊓ M₂) (hK'card : Nat.card ↥K' = Nat.card ↥K)
    (haK : ∀ k ∈ K', (a : E) * k * (a : E)⁻¹ ∈ K') (hbK : ∀ k ∈ K', (b : E) * k * (b : E)⁻¹ ∈ K')
    (ha2 : (a : E) * a ∈ K') (hb2 : (b : E) * b ∈ K')
    {c : ↥(M₁ ⊓ M₂)} (hcK : (c : E) ∈ K') (hrel : (β.φ1 a * β.φ2 b) ^ m = β.φ12 c) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion :=
  burnsideF48s_e_qe_of_core (burnsideF48s_e_ecore hM hC hconj) θ hA hM1 hM2 hgen β hβ hcard haM hbM
    hK'le (by rw [← hK'card]; exact Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv fun z => Iff.rfl))
    haK hbK ha2 hb2 hcK hrel

end QE

section Sylow

open CFSG.Open CFSG.ASVolI.ChF

theorem burnsideF48s_e_sylow_conj {H : Type*} [Group H] [Finite H] {B K : Subgroup H} {q : ℕ}
    [Fact q.Prime] (hKB : K ≤ B) (hKq : IsPGroup q ↥K) (hidx : ¬ q ∣ K.relIndex B) :
    ∀ K'' : Subgroup H, K'' ≤ B → Nat.card ↥K'' = Nat.card ↥K →
      ∃ t ∈ B, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ K := by
  intro K'' hK''B hcard
  have hq1 : IsPGroup q ↥(K.subgroupOf B) := hKq.comap_of_injective B.subtype B.subtype_injective
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hKq
  have hK''q : IsPGroup q ↥K'' := IsPGroup.of_card (n := n) (hcard.trans hn)
  have hq2 : IsPGroup q ↥(K''.subgroupOf B) :=
    hK''q.comap_of_injective B.subtype B.subtype_injective
  have hrel : K''.relIndex B = K.relIndex B := by
    have h1 := Subgroup.relIndex_mul_card (H := K'') (K := B)
    have h2 := Subgroup.relIndex_mul_card (H := K) (K := B)
    rw [inf_eq_left.2 hK''B] at h1
    rw [inf_eq_left.2 hKB] at h2
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    rw [hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  let P : Sylow q ↥B := hq1.toSylow (by rw [← Subgroup.relIndex]; exact hidx)
  let Q : Sylow q ↥B := hq2.toSylow (by rw [← Subgroup.relIndex, hrel]; exact hidx)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥B Q P
  refine ⟨g, g.2, fun z => ?_⟩
  by_cases hz : z ∈ B
  · have hQ : (⟨z, hz⟩ : ↥B) ∈ (Q : Subgroup ↥B) ↔ z ∈ K'' := by
      rw [IsPGroup.toSylow_coe]
      exact Iff.rfl
    have hP : (g * ⟨z, hz⟩ * g⁻¹ : ↥B) ∈ (P : Subgroup ↥B) ↔ (g : H) * z * (g : H)⁻¹ ∈ K := by
      rw [IsPGroup.toSylow_coe]
      exact Iff.rfl
    rw [← hQ, ← hP, ← hg, Sylow.coe_subgroup_smul, ← Subgroup.smul_mem_pointwise_smul_iff
      (a := MulAut.conj g)]
    exact Iff.rfl
  · constructor
    · intro h
      exact absurd (hK''B h) hz
    · intro h
      exfalso
      apply hz
      have := B.mul_mem (B.mul_mem (B.inv_mem g.2) (hKB h)) g.2
      simpa [mul_assoc] using this

theorem burnsideF48s_e_card_sylow {E : Type} [Group E] [Finite E] {p : ℕ} [hp : Fact p.Prime]
    {S Gp : Subgroup E} (hS : IsSylowOf p S Gp) {k a : ℕ} (hG : Nat.card ↥Gp = p ^ k * a)
    (ha : ¬ p ∣ a) : Nat.card ↥S = p ^ k := by
  obtain ⟨hSG, hSp, hidx⟩ := hS
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hSp
  have h1 := Subgroup.relIndex_mul_card (H := S) (K := Gp)
  rw [inf_eq_left.2 hSG, hn, hG] at h1
  have ha0 : a ≠ 0 := fun h => ha (h ▸ dvd_zero p)
  have hi0 : S.relIndex Gp ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1
    exact (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) ha0) h1.symm
  have hf : (S.relIndex Gp * p ^ n).factorization p = (p ^ k * a).factorization p := by rw [h1]
  rw [Nat.factorization_mul hi0 (pow_ne_zero _ hp.out.ne_zero),
    Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) ha0, Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow_self hp.out, Nat.factorization_pow_self hp.out,
    Nat.factorization_eq_zero_of_not_dvd hidx, Nat.factorization_eq_zero_of_not_dvd ha] at hf
  rw [hn]
  congr 1
  omega

theorem burnsideF48s_e_card_compl {E : Type} [Group E] [Finite E] {p : ℕ} [hp : Fact p.Prime]
    {Gp M₁ M₂ : Subgroup E}
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) {K' : Subgroup E}
    (hK' : IsComplementIn K' (pCoreOf p (Gp ⊓ (M₁ ⊓ M₂))) (M₁ ⊓ M₂)) :
    ∃ S : Subgroup E, IsSylowOf p S Gp ∧ Nat.card ↥K' * Nat.card ↥S = Nat.card ↥(M₁ ⊓ M₂) := by
  obtain ⟨⟨S, hS, hB⟩, -⟩ := hP
  refine ⟨S, hS, ?_⟩
  set Bp := Gp ⊓ (M₁ ⊓ M₂) with hBp
  set Sb := pCoreOf p Bp with hSb
  have hSB : S ≤ Bp := by rw [hB]; exact le_inf hS.1 Subgroup.le_normalizer
  have hBN : Bp ≤ Subgroup.normalizer (S : Set E) := by rw [hB]; exact inf_le_right
  have hSn : (S.subgroupOf Bp).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).2 hBN
  have hSp : IsPGroup p ↥(S.subgroupOf Bp) :=
    hS.2.1.comap_of_injective Bp.subtype Bp.subtype_injective
  have hSSb : S ≤ Sb := by
    have h1 : S.subgroupOf Bp ≤ CFSG.pCore p ↥Bp := le_sSup ⟨hSn, hSp⟩
    intro s hs
    exact ⟨⟨s, hSB hs⟩, h1 hs, rfl⟩
  have hSbp : IsPGroup p ↥Sb := (CFSG.pCore_isPGroup).map Bp.subtype
  have hSbG : Sb ≤ Gp := (Subgroup.map_subtype_le _).trans inf_le_left
  have hcardS : Nat.card ↥Sb = Nat.card ↥S := by
    have h1 := Subgroup.relIndex_mul_relIndex S Sb Gp hSSb hSbG
    obtain ⟨j, hj⟩ := hSbp.index (S.subgroupOf Sb)
    have hj0 : j = 0 := by
      by_contra hne
      apply hS.2.2
      rw [← h1]
      exact Dvd.dvd.mul_right (by rw [Subgroup.relIndex, hj]; exact dvd_pow_self p hne) _
    have h2 : S.relIndex Sb = 1 := by rw [Subgroup.relIndex, hj, hj0, pow_zero]
    have h3 := Subgroup.relIndex_mul_card (H := S) (K := Sb)
    rw [inf_eq_left.2 hSSb, h2, one_mul] at h3
    exact h3.symm
  have hSbK : Sb ⊓ K' = ⊥ := hK'.2.2.1
  let f : ↥Sb × ↥K' → ↥(M₁ ⊓ M₂) := fun x =>
    ⟨x.1 * x.2, (M₁ ⊓ M₂).mul_mem (hK'.1 x.1.2) (hK'.2.1 x.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, fun g => ?_⟩
    · have e : (x.1 : E) * x.2 = y.1 * y.2 := congrArg Subtype.val hxy
      have h1 : (y.1 : E)⁻¹ * x.1 = y.2 * (x.2 : E)⁻¹ := by
        calc (y.1 : E)⁻¹ * x.1 = (y.1 : E)⁻¹ * (x.1 * x.2) * (x.2 : E)⁻¹ := by group
          _ = (y.1 : E)⁻¹ * (y.1 * y.2) * (x.2 : E)⁻¹ := by rw [e]
          _ = y.2 * (x.2 : E)⁻¹ := by group
      have h2 : (y.1 : E)⁻¹ * x.1 ∈ Sb ⊓ K' :=
        ⟨Sb.mul_mem (Sb.inv_mem y.1.2) x.1.2, h1 ▸ K'.mul_mem y.2.2 (K'.inv_mem x.2.2)⟩
      rw [hSbK, Subgroup.mem_bot, inv_mul_eq_one] at h2
      have e2 : (x.2 : E) = y.2 := by
        rw [← h2] at e
        exact mul_left_cancel e
      exact Prod.ext (Subtype.ext h2.symm) (Subtype.ext e2)
    · obtain ⟨q, hq, k, hk, hqk⟩ := hK'.2.2.2 g g.2
      exact ⟨(⟨q, hq⟩, ⟨k, hk⟩), Subtype.ext hqk⟩
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at this
  rw [← this, ← hcardS, mul_comm]

end Sylow

end CFSG.ASVolI
