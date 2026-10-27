module

public import CFSG.Certificates.CosetTableOrders

public section

namespace CFSG.Quasithin.C48Cover

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] def stabCheck (ws subs : List (List (Fin m × Bool))) (k cap : ℕ)
    (fix move : List (List (Fin m × Bool))) : Bool :=
  let P := colParamsShort ws subs k
  let st := enumerateHLT P cap
  let δ : ℕ → ℕ → ℕ := fun c x => st.tab.getD (c * P.L + x) 0
  (!st.overflow && st.complete P.L) &&
    invConsistentNative P.L (colInv ws) st && relsClosedNative P.L st (colCodes ws ws) &&
    fix.all (fun u => (u.map (colCode ws)).foldl δ 1 == 1) &&
    move.all fun u => (u.map (colCode ws)).foldl δ 1 != 1

theorem exists_subgroup_of_stabCheck {ws subs : List (List (Fin m × Bool))} {k cap : ℕ}
    {fix move : List (List (Fin m × Bool))} (h : stabCheck ws subs k cap fix move = true)
    {rels : Set (FreeGroup (Fin m))}
    (hrels : {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} = rels) :
    ∃ S : Subgroup (PresentedGroup rels),
      (∀ u ∈ fix, PresentedGroup.mk rels (FreeGroup.mk u) ∈ S) ∧
        ∀ u ∈ move, PresentedGroup.mk rels (FreeGroup.mk u) ∉ S := by
  subst hrels
  unfold stabCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hc⟩, hi⟩, hrel⟩, hfix⟩, hmove⟩ := h
  set P := colParamsShort ws subs k
  set st := enumerateHLT P cap
  have hL : P.L = (cols ws).length := rfl
  rw [hL] at hc hi hrel hfix hmove
  set Lc := (cols ws).length
  let δ : ℕ → ℕ → ℕ := fun c x => st.tab.getD (c * Lc + colOfCode ws x) 0
  have hlive : ∀ c, st.live c = true → ∀ x < 2 * m, st.live (δ c x) = true :=
    fun c hl x hx => St.complete_step hc hl (colOfCode_lt ws hx)
  have hinv : ∀ c, st.live c = true → ∀ x < 2 * m, δ (δ c x) (invCode x) = c := by
    intro c hl x hx
    have := invConsistent_spec hi hl (colOfCode_lt ws hx)
    simp only [δ, colOfCode_invCode ws hx]
    exact this
  have hrel' : ∀ c, st.live c = true → ∀ r ∈ codes ws, r.foldl δ c = c := by
    intro c hl r hr
    simp only [codes, List.mem_map] at hr
    obtain ⟨v, hv, rfl⟩ := hr
    show (v.map letterCode).foldl (fun c x => st.tab.getD (c * Lc + colOfCode ws x) 0) c = c
    rw [foldl_colOfCode]
    exact relsClosed_spec hrel hl (List.mem_map_of_mem hv)
  obtain ⟨ψ, hψ⟩ := exists_action_step ws (fun c => st.live c = true) δ hlive hinv hrel'
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  have hw : ∀ u : List (Fin m × Bool), ∀ y ∈ u.map letterCode, y < 2 * m := by
    intro u y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, -, rfl⟩ := hy
    unfold letterCode
    have := x.1.isLt
    split <;> omega
  have hact : ∀ (u : List (Fin m × Bool)) (c : {c : ℕ // st.live c = true}),
      ((ψ (PresentedGroup.mk rels (FreeGroup.mk u))).unop c).1 =
        (u.map (colCode ws)).foldl (fun c x => st.tab.getD (c * Lc + x) 0) c.1 := by
    intro u c
    rw [← evalWord_presLetter, act_evalWord_step ψ hψ _ (hw u) c]
    exact foldl_colOfCode ws st Lc u c.1
  have hone := St.live_one hc
  set c₀ : {c : ℕ // st.live c = true} := ⟨1, hone⟩ with hc₀
  let S : Subgroup (PresentedGroup rels) :=
    { carrier := {g | (ψ g).unop c₀ = c₀}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul, MulOpposite.unop_mul, Equiv.Perm.coe_mul,
          Function.comp_apply] at ha hb ⊢
        rw [ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_inv, MulOpposite.unop_inv] at ha ⊢
        rw [Equiv.Perm.inv_eq_iff_eq, ha] }
  refine ⟨S, fun u hu => ?_, fun u hu hmem => ?_⟩
  · show (ψ (PresentedGroup.mk rels (FreeGroup.mk u))).unop c₀ = c₀
    apply Subtype.ext
    rw [hact u c₀]
    exact hfix u hu
  · have h1 : (ψ (PresentedGroup.mk rels (FreeGroup.mk u))).unop c₀ = c₀ := hmem
    have h2 := congrArg Subtype.val h1
    rw [hact u c₀] at h2
    exact hmove u hu h2

end CFSG.Quasithin.C48Cover
