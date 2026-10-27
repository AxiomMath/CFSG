module

public import CFSG.RankThree.GF2n.Smith81.S81XE7Grp
public import CFSG.RankThree.GF2n.Smith81.S81XE7Def

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model


variable {K : Type} [Field K]

private theorem pf_xE_zero (γ : Fin (Tag.rank .E7) → ℤ) : xE γ (0 : K) = 1 :=
  e7Data_valid.xm_zero K γ

private theorem pf_xE_add (γ : Fin (Tag.rank .E7) → ℤ) (c d : K) :
    xE γ (c + d) = xE γ c * xE γ d :=
  e7Data_valid.xm_add K γ c d

private theorem pf_prodX_cons (γ : Fin (Tag.rank .E7) → ℤ) (L : List (Fin (Tag.rank .E7) → ℤ))
    (c : (Fin (Tag.rank .E7) → ℤ) → K) :
    prodX (γ :: L) c = xE γ (c γ) * prodX L c := by
  simp only [prodX, List.map_cons, List.prod_cons]

theorem endoE_prodX (L : List (Fin (Tag.rank .E7) → ℤ)) (c : (Fin (Tag.rank .E7) → ℤ) → K) :
    endoE (prodX L c) =
      (L.map fun γ => (1 : Module.End K (V K)) + c γ • e7Data.rootOp K γ).prod := by
  induction L with
  | nil => exact e7Data_valid.endo_one K
  | cons γ L ih =>
    have h1 : endoE (prodX (γ :: L) c) = endoE (xE γ (c γ)) * endoE (prodX L c) := by
      rw [pf_prodX_cons]
      exact e7Data_valid.endo_mul K _ _
    have h2 : endoE (xE γ (c γ)) = 1 + c γ • e7Data.rootOp K γ :=
      e7Data_valid.endo_xm K γ (c γ)
    rw [h1, h2, ih]
    simp only [List.map_cons, List.prod_cons]

theorem xE_comm_of_mem_Phi {a : Fin e7Data.d} {γ δ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Phi a)
    (hδ : δ ∈ Phi a) (c d : K) : xE γ c * xE δ d = xE δ d * xE γ c := by
  obtain ⟨hγr, hγa⟩ := mem_Phi.1 hγ
  obtain ⟨hδr, hδa⟩ := mem_Phi.1 hδ
  have hsum : pr a (γ + δ) = pr a γ + pr a δ := dotProduct_add (e7Data.wt a) γ δ
  rw [hγa, hδa] at hsum
  have hne : γ + δ ≠ 0 := by
    intro h
    have h0 : pr a 0 = 0 := by simp [pr]
    rw [h, h0] at hsum
    omega
  have hnr : ¬ IsRoot .E7 (γ + δ) := by
    intro hr
    rcases pr_mem hr a with h | h | h <;> omega
  have hcomm := (e7Data_valid.commutator_xm K hγr hδr hne).2 hnr c d
  exact commutatorElement_eq_one_iff_mul_comm.1 hcomm

private theorem pf_xE_mul_prodX {a : Fin e7Data.d} {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ Phi a)
    (e : K) (c : (Fin (Tag.rank .E7) → ℤ) → K) (L : List (Fin (Tag.rank .E7) → ℤ)) :
    (∀ δ ∈ L, δ ∈ Phi a) → xE γ e * prodX L c = prodX L c * xE γ e := by
  induction L with
  | nil => intro _; simp [prodX]
  | cons δ L ih =>
    intro hL
    have hδ : δ ∈ Phi a := hL δ (by simp)
    have hL' : ∀ ε ∈ L, ε ∈ Phi a := fun ε hε => hL ε (by simp [hε])
    have h1 : xE γ e * xE δ (c δ) = xE δ (c δ) * xE γ e := xE_comm_of_mem_Phi hγ hδ e (c δ)
    have h2 : xE γ e * prodX L c = prodX L c * xE γ e := ih hL'
    rw [pf_prodX_cons]
    calc xE γ e * (xE δ (c δ) * prodX L c)
        = (xE γ e * xE δ (c δ)) * prodX L c := (mul_assoc _ _ _).symm
      _ = (xE δ (c δ) * xE γ e) * prodX L c := by rw [h1]
      _ = xE δ (c δ) * (xE γ e * prodX L c) := mul_assoc _ _ _
      _ = xE δ (c δ) * (prodX L c * xE γ e) := by rw [h2]
      _ = xE δ (c δ) * prodX L c * xE γ e := (mul_assoc _ _ _).symm

theorem prodX_mul {a : Fin e7Data.d} {L : List (Fin (Tag.rank .E7) → ℤ)} (hL : ∀ γ ∈ L, γ ∈ Phi a)
    (c d : (Fin (Tag.rank .E7) → ℤ) → K) : prodX L c * prodX L d = prodX L (c + d) := by
  induction L with
  | nil => simp [prodX]
  | cons γ L ih =>
    have hγ : γ ∈ Phi a := hL γ (by simp)
    have hL' : ∀ δ ∈ L, δ ∈ Phi a := fun δ hδ => hL δ (by simp [hδ])
    have hI := ih hL'
    have hPy := pf_xE_mul_prodX hγ (d γ) c L hL'
    have hadd := pf_xE_add γ (c γ) (d γ)
    simp only [pf_prodX_cons, Pi.add_apply]
    rw [← hI, hadd]
    calc xE γ (c γ) * prodX L c * (xE γ (d γ) * prodX L d)
        = xE γ (c γ) * (prodX L c * xE γ (d γ)) * prodX L d := by simp only [mul_assoc]
      _ = xE γ (c γ) * (xE γ (d γ) * prodX L c) * prodX L d := by rw [← hPy]
      _ = (xE γ (c γ) * xE γ (d γ)) * (prodX L c * prodX L d) := by simp only [mul_assoc]

theorem prodX_zero (L : List (Fin (Tag.rank .E7) → ℤ)) : prodX L (0 : (Fin (Tag.rank .E7) → ℤ) → K) = 1 := by
  induction L with
  | nil => simp [prodX]
  | cons γ L ih => rw [pf_prodX_cons, ih, Pi.zero_apply, pf_xE_zero, mul_one]

theorem prodX_eq_one {L : List (Fin (Tag.rank .E7) → ℤ)} {c : (Fin (Tag.rank .E7) → ℤ) → K}
    (hc : ∀ γ ∈ L, c γ = 0) : prodX L c = 1 := by
  induction L with
  | nil => simp [prodX]
  | cons γ L ih =>
    rw [pf_prodX_cons, hc γ (by simp), ih (fun δ hδ => hc δ (by simp [hδ])), pf_xE_zero, mul_one]

theorem prodX_eq_single {L : List (Fin (Tag.rank .E7) → ℤ)} (hnd : L.Nodup)
    {δ₀ : Fin (Tag.rank .E7) → ℤ} (h0 : δ₀ ∈ L) {c : (Fin (Tag.rank .E7) → ℤ) → K}
    (hc : ∀ γ ∈ L, γ ≠ δ₀ → c γ = 0) : prodX L c = xE δ₀ (c δ₀) := by
  induction L with
  | nil => simp at h0
  | cons x L ih =>
    rw [List.nodup_cons] at hnd
    rw [pf_prodX_cons]
    by_cases hx : x = δ₀
    · subst hx
      have h1 : prodX L c = 1 :=
        prodX_eq_one (fun γ hγ => hc γ (by simp [hγ]) (fun e => hnd.1 (e ▸ hγ)))
      rw [h1, mul_one]
    · have hδL : δ₀ ∈ L := (List.mem_cons.1 h0).resolve_left (fun e => hx e.symm)
      have hcx : c x = 0 := hc x (by simp) hx
      rw [hcx, pf_xE_zero, one_mul]
      exact ih hnd.2 hδL (fun γ hγ hne => hc γ (by simp [hγ]) hne)

theorem mem_UA_iff {a : Fin e7Data.d} {u : Gp K} :
    u ∈ UA K a ↔ ∃ c : (Fin (Tag.rank .E7) → ℤ) → K, u = prodX (Phi a).toList c := by
  constructor
  · intro hu
    let P : Subgroup (Gp K) :=
      { carrier := {v | ∃ c : (Fin (Tag.rank .E7) → ℤ) → K, v = prodX (Phi a).toList c}
        mul_mem' := by
          rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩
          exact ⟨c + d, prodX_mul (fun γ hγ => Finset.mem_toList.1 hγ) c d⟩
        one_mem' := ⟨0, (prodX_zero _).symm⟩
        inv_mem' := by
          rintro _ ⟨c, rfl⟩
          refine ⟨-c, inv_eq_of_mul_eq_one_right ?_⟩
          rw [prodX_mul (fun γ hγ => Finset.mem_toList.1 hγ) c (-c), add_neg_cancel, prodX_zero] }
    have hle : UA K a ≤ P := by
      unfold UA
      refine (Subgroup.closure_le P).2 ?_
      rintro g ⟨γ, hγ, c, rfl⟩
      show ∃ c' : (Fin (Tag.rank .E7) → ℤ) → K, xE γ c = prodX (Phi a).toList c'
      refine ⟨fun δ => if δ = γ then c else 0, ?_⟩
      have h := prodX_eq_single (Finset.nodup_toList _) (Finset.mem_toList.2 hγ)
        (c := fun δ => if δ = γ then c else 0) (fun δ _ hne => if_neg hne)
      rw [h]
      simp
    obtain ⟨c, hc⟩ := hle hu
    exact ⟨c, hc⟩
  · rintro ⟨c, rfl⟩
    unfold prodX
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
    unfold UA
    apply Subgroup.subset_closure
    exact ⟨γ, Finset.mem_toList.1 hγ, c γ, rfl⟩

theorem exists_pr_eq_neg_one {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) :
    ∃ b : Fin e7Data.d, pr b δ = -1 := by
  have hpos : 0 < (Finset.univ.filter fun a : Fin e7Data.d => pr a δ = -1).card := by
    rw [(card_pr hδ).2.1]
    norm_num
  obtain ⟨b, hb⟩ := Finset.card_pos.1 hpos
  exact ⟨b, (Finset.mem_filter.1 hb).2⟩

variable [CharP K 2]

theorem coef_prodX (a : Fin e7Data.d) (c : (Fin (Tag.rank .E7) → ℤ) → K) (b : Fin e7Data.d)
    {δ : Fin (Tag.rank .E7) → ℤ} (hδ : IsRoot .E7 δ) (hb : pr b δ = -1) :
    endoE (prodX (Phi a).toList c) (Finsupp.single b 1) (shift δ b) =
      if δ ∈ Phi a then c δ else 0 := by
  rw [endoE_prodX]
  have hL : ∀ γ ∈ (Phi a).toList, IsRoot .E7 γ ∧ pr a γ = 1 := fun γ hγ =>
    mem_Phi.1 (Finset.mem_toList.1 hγ)
  have h := coef_prod a (Phi a).toList hL (Finset.nodup_toList _) c b δ hδ hb
  simp only [Finset.mem_toList] at h
  exact h

theorem coef_eq_zero_of_prodX_eq {a a' : Fin e7Data.d} {c c' : (Fin (Tag.rank .E7) → ℤ) → K}
    (h : prodX (Phi a).toList c = prodX (Phi a').toList c') {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : δ ∈ Phi a) (hδ' : δ ∉ Phi a') : c δ = 0 := by
  have hroot : IsRoot .E7 δ := (mem_Phi.1 hδ).1
  obtain ⟨b, hb⟩ := exists_pr_eq_neg_one hroot
  have h1 := coef_prodX a c b hroot hb
  have h2 := coef_prodX a' c' b hroot hb
  rw [h, if_pos hδ] at h1
  rw [if_neg hδ'] at h2
  exact h1.symm.trans h2

theorem UA_inf_UA {a a' : Fin e7Data.d}
    (hU : ∀ γ γ' : Fin (Tag.rank .E7) → ℤ, γ ∈ Phi a → γ ∈ Phi a' → γ' ∈ Phi a → γ' ∈ Phi a' → γ = γ') :
    ∀ u ∈ UA K a ⊓ UA K a', u = 1 ∨ ∃ (δ : Fin (Tag.rank .E7) → ℤ) (c : K), IsRoot .E7 δ ∧ c ≠ 0 ∧
      u = xE δ c := by
  intro u hu
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨c, hc⟩ := mem_UA_iff.1 h1
  obtain ⟨c', hc'⟩ := mem_UA_iff.1 h2
  have h : prodX (Phi a).toList c = prodX (Phi a').toList c' := hc.symm.trans hc'
  by_cases hex : ∃ δ₀, δ₀ ∈ Phi a ∧ δ₀ ∈ Phi a'
  · obtain ⟨δ₀, hδa, hδa'⟩ := hex
    have hz : ∀ γ ∈ (Phi a).toList, γ ≠ δ₀ → c γ = 0 := by
      intro γ hγ hne
      refine coef_eq_zero_of_prodX_eq h (Finset.mem_toList.1 hγ) ?_
      intro hγ'
      exact hne (hU γ δ₀ (Finset.mem_toList.1 hγ) hγ' hδa hδa')
    have hu' : u = xE δ₀ (c δ₀) := by
      rw [hc]
      exact prodX_eq_single (Finset.nodup_toList _) (Finset.mem_toList.2 hδa) hz
    by_cases hc0 : c δ₀ = 0
    · left
      rw [hu', hc0, pf_xE_zero]
    · right
      exact ⟨δ₀, c δ₀, (mem_Phi.1 hδa).1, hc0, hu'⟩
  · have hex' : ∀ δ₀, δ₀ ∈ Phi a → δ₀ ∉ Phi a' := fun δ₀ h1 h2 => hex ⟨δ₀, h1, h2⟩
    left
    rw [hc]
    apply prodX_eq_one
    intro γ hγ
    exact coef_eq_zero_of_prodX_eq h (Finset.mem_toList.1 hγ) (hex' γ (Finset.mem_toList.1 hγ))

private theorem pf_coef_eq_self {a : Fin e7Data.d} {c c' : (Fin (Tag.rank .E7) → ℤ) → K}
    (h : prodX (Phi a).toList c = prodX (Phi a).toList c') {δ : Fin (Tag.rank .E7) → ℤ}
    (hδ : δ ∈ Phi a) : c δ = c' δ := by
  have hroot : IsRoot .E7 δ := (mem_Phi.1 hδ).1
  obtain ⟨b, hb⟩ := exists_pr_eq_neg_one hroot
  have h1 := coef_prodX a c b hroot hb
  have h2 := coef_prodX a c' b hroot hb
  rw [h, if_pos hδ] at h1
  rw [if_pos hδ] at h2
  exact h1.symm.trans h2

theorem card_UA_ge [Finite K] (a : Fin e7Data.d) :
    Nat.card K ^ (Phi a).card ≤ Nat.card (UA K a) := by
  haveI : Finite (Module.End K (V K)) := Module.finite_of_finite K
  haveI : Finite (Gp K) := Finite.of_injective (e7Data_valid.endo K) (e7Data_valid.endo_injective K)
  let F : (↥(Phi a) → K) → ↥(UA K a) := fun f =>
    ⟨prodX (Phi a).toList (fun γ => if h : γ ∈ Phi a then f ⟨γ, h⟩ else 0),
      mem_UA_iff.2 ⟨_, rfl⟩⟩
  have hF : Function.Injective F := by
    intro f g hfg
    have h1 : prodX (Phi a).toList (fun γ => if h : γ ∈ Phi a then f ⟨γ, h⟩ else 0) =
        prodX (Phi a).toList (fun γ => if h : γ ∈ Phi a then g ⟨γ, h⟩ else 0) :=
      congrArg Subtype.val hfg
    funext x
    have h2 := pf_coef_eq_self (a := a) h1 x.2
    simpa [x.2] using h2
  calc Nat.card K ^ (Phi a).card = Nat.card (↥(Phi a) → K) := by
        rw [Nat.card_fun, Nat.card_eq_finsetCard]
    _ ≤ Nat.card (UA K a) := Nat.card_le_card_of_injective F hF

end CFSG.RankThree.GF2n.Smith81.E7X
