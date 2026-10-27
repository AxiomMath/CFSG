module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Mod3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

@[expose] def cls1w : List (List ℕ) :=
  [[], [1, 3, 0, 2], [1, 0, 2, 0, 1], [2, 0, 1, 0, 2], [2, 0, 1, 3, 2], [2, 2, 3, 1, 1],
    [3, 1, 3, 0, 2], [1, 0, 1, 0, 2, 0, 2], [2, 0, 2, 0, 1, 0, 1], [2, 3, 1, 0, 2, 3, 1],
    [2, 2, 3, 2, 2, 0, 2, 0, 1], [2, 3, 2, 3, 1, 1, 0, 1, 0, 1]]

@[expose] def cls2w : List (List ℕ) :=
  [[], [1, 1, 3, 2], [1, 3, 2, 2], [1, 3, 2, 3, 2, 2], [2, 0, 1, 1, 0, 1, 1], [2, 0, 2, 2, 3, 0, 1],
    [2, 2, 0, 2, 2, 0, 1], [2, 2, 3, 0, 1, 3, 1], [2, 3, 0, 1, 1, 0, 1], [0, 2, 2, 0, 2, 2, 0, 1],
    [1, 0, 2, 2, 0, 1, 0, 1], [1, 1, 0, 1, 0, 2, 3, 1], [1, 3, 0, 1, 0, 2, 3, 1],
    [1, 3, 0, 1, 1, 3, 1, 1], [1, 3, 1, 0, 2, 2, 0, 1], [2, 3, 1, 0, 2, 3, 0, 2],
    [2, 3, 2, 3, 2, 2, 0, 1], [3, 2, 2, 3, 0, 1, 3, 1], [3, 2, 3, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 0, 1, 3, 1]]

@[expose] def aW (w : List ℕ) : Ah := ⟨wordAP w, wordAP_mem w⟩

@[expose] def fconjL (w : List ℕ) : PL := comp (comp (evalAL w) fhatL) (evalAL (invAL w))

theorem repL_aW (w : List ℕ) : RepL (evalAL w) ((aW w : Ah) : P45) := repL_wordAP w

theorem repL_aW_inv (w : List ℕ) : RepL (evalAL (invAL w)) (((aW w)⁻¹ : Ah) : P45) := by
  have : (((aW w)⁻¹ : Ah) : P45) = wordAP (invAL w) := by
    rw [wordAP_invAL]
    rfl
  rw [this]
  exact repL_wordAP _

theorem repL_fconj (w : List ℕ) :
    RepL (fconjL w) ((aW w * fhatA * (aW w)⁻¹ : Ah) : P45) :=
  repL_mul (repL_mul (repL_aW w) repL_fhat) (repL_aW_inv w)

theorem fconjL_nil : fconjL [] = fhatL := by decide +kernel

theorem card_cent_fhat_of_class {H : Subgroup Ah} {Γ : Set Ah} (hΓ : Subgroup.closure Γ = H)
    (hf : fhatA ∈ H) (ws : List (List ℕ)) (gl : List PL)
    (hgl : ∀ s ∈ Γ, ∃ sL ∈ gl, RepL sL (s : P45)) (hws : ∀ w ∈ ws, aW w ∈ H)
    (hnd : (ws.map fconjL).Nodup) (hid : ([] : List ℕ) ∈ ws)
    (hcl : ∀ w ∈ ws, ∀ s ∈ gl, ∃ w' ∈ ws, comp s (fconjL w) = comp (fconjL w') s) :
    Nat.card ↥(Subgroup.centralizer ({(⟨fhatA, hf⟩ : ↥H)} : Set ↥H)) * ws.length =
      Nat.card ↥H := by
  have h := card_centralizer_mul_of_closed_class (Γ := Γ) hΓ hf
    (cl := ws.map fun w => aW w * fhatA * (aW w)⁻¹) ?_ ?_ ?_ ?_
  · rwa [List.length_map] at h
  · refine List.Nodup.of_map (fun a : Ah => permL (a : P45)) ?_
    rw [List.map_map]
    have : ((fun a : Ah => permL (a : P45)) ∘ fun w => aW w * fhatA * (aW w)⁻¹) = fconjL :=
      funext fun w => permL_eq_of_repL (repL_fconj w)
    rw [this]
    exact hnd
  · intro c hc
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    exact ⟨aW w, hws w hw, rfl⟩
  · refine List.mem_map.2 ⟨[], hid, ?_⟩
    apply Subtype.ext
    apply eq_of_repL (repL_fconj [])
    rw [fconjL_nil]
    exact repL_fhat
  · intro c hc s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
    obtain ⟨sL, hsL, hrep⟩ := hgl s hs
    obtain ⟨w', hw', hcomm⟩ := hcl w hw sL hsL
    refine List.mem_map.2 ⟨w', hw', ?_⟩
    have h1 : s * (aW w * fhatA * (aW w)⁻¹) = (aW w' * fhatA * (aW w')⁻¹) * s := by
      apply Subtype.ext
      apply eq_of_repL (l := comp sL (fconjL w))
      · exact repL_mul hrep (repL_fconj w)
      · rw [hcomm]
        exact repL_mul (repL_fconj w') hrep
    calc aW w' * fhatA * (aW w')⁻¹ = (aW w' * fhatA * (aW w')⁻¹ * s) * s⁻¹ := by group
      _ = s * (aW w * fhatA * (aW w)⁻¹) * s⁻¹ := by rw [← h1]

theorem card_inf_centralizer {H : Subgroup Ah} (hf : fhatA ∈ H) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({fhatA} : Set Ah)) =
      Nat.card ↥(Subgroup.centralizer ({(⟨fhatA, hf⟩ : ↥H)} : Set ↥H)) := by
  have e : (H ⊓ Subgroup.centralizer ({fhatA} : Set Ah)).subgroupOf H =
      Subgroup.centralizer ({(⟨fhatA, hf⟩ : ↥H)} : Set ↥H) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using h
    · intro h
      refine ⟨x.2, ?_⟩
      have h' := congrArg (fun y : ↥H => (y : Ah)) h
      simpa only [Subgroup.coe_mul] using h'
  rw [← e]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm

@[expose] def genP1L : List PL := (List.range 5).map gTL ++ [fhatL, c3L, DL 1]

@[expose] def genP2L : List PL := (List.range 5).map gTL ++ [fhatL, c3L, evalAL wb]

theorem cls1_check : (cls1w.map fconjL).Nodup ∧ ([] : List ℕ) ∈ cls1w ∧
    ∀ w ∈ cls1w, ∀ s ∈ genP1L, ∃ w' ∈ cls1w, comp s (fconjL w) = comp (fconjL w') s := by
  decide +kernel

theorem cls2_check : (cls2w.map fconjL).Nodup ∧ ([] : List ℕ) ∈ cls2w ∧
    ∀ w ∈ cls2w, ∀ s ∈ genP2L, ∃ w' ∈ cls2w, comp s (fconjL w) = comp (fconjL w') s := by
  decide +kernel

theorem cls1_mem : ∀ w ∈ cls1w, (evalAL w).getD 0 0 = 0 := by decide +kernel

theorem cls2_mem : ∀ w ∈ cls2w, sameSet (imgSet (evalAL w) L0) L0 = true := by decide +kernel

theorem bA_not_mem_P1h : bA ∉ P1h := by
  intro h
  have h1 := (mem_P1h_iff bA).1 h
  have h2 := repL_bA.2 0
  have h3 : (evalAL wb).getD 0 0 ≠ 0 := by decide +kernel
  apply h3
  have h2' : (evalAL wb).getD 0 0 = (((bA : P45) 0 : Fin 45) : ℕ) := h2
  rw [h2', h1]
  rfl

end CFSG.Quasithin.H13.F431.U42Aut
