module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bInv
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bV

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 xY)

@[expose] def El : List PL := ((List.range 43).filter fun k => invTgt.getD k 0 == 3).map invL

@[expose] def Xw (w : PL) : List PL :=
  Tl.filter fun s => comp s s == idL && comp s w == comp w s && El.contains (comp s w)

theorem Tl_nodup : Tl.Nodup := by decide +kernel

theorem e1_check : ∀ l ∈ Tl, comp l l = idL → l ∉ Vl →
    (Tl.filter fun m => comp m m == idL && comp m l == comp l m).length < 16 := by
  decide +kernel

theorem e2_check : ∀ w ∈ El, (Xw w).length ≤ 8 ∧ ∃ a ∈ Xw w, ∃ b ∈ Xw w, comp a b ∉ Xw w := by
  decide +kernel

theorem mem_El {k : ℕ} (hk : k < 43) (h3 : invTgt.getD k 0 = 3) : invL k ∈ El := by
  unfold El
  exact List.mem_map.2 ⟨k, List.mem_filter.2 ⟨List.mem_range.2 hk, by rw [h3]; rfl⟩, rfl⟩

theorem card_le_length_of_reps (L : Subgroup Ah) {F : List PL}
    (hF : ∀ s ∈ L, ∃ l ∈ F, RepL l (s : P45)) : Nat.card L ≤ F.length := by
  classical
  have hmem : ∀ g : ↥L, permL ((g : Ah) : P45) ∈ F.toFinset := by
    intro g
    obtain ⟨l, hl, hrep⟩ := hF g g.2
    rw [List.mem_toFinset, permL_eq_of_repL hrep]
    exact hl
  have hinj : Function.Injective fun g : ↥L =>
      (⟨permL ((g : Ah) : P45), hmem g⟩ : ↥F.toFinset) := by
    intro g₁ g₂ hg
    have h1 : permL ((g₁ : Ah) : P45) = permL ((g₂ : Ah) : P45) := congrArg Subtype.val hg
    have h2 : ((g₁ : Ah) : P45) = ((g₂ : Ah) : P45) :=
      eq_of_repL (repL_permL _) (h1 ▸ repL_permL _)
    exact Subtype.ext (Subtype.ext h2)
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h3 : Nat.card ↥F.toFinset = F.toFinset.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [h3] at h1
  exact h1.trans (List.toFinset_card_le F)

theorem closed_of_card_ge (L : Subgroup Ah) {F : List PL} (hnd : F.Nodup)
    (hF : ∀ s ∈ L, ∃ l ∈ F, RepL l (s : P45)) (hcard : F.length ≤ Nat.card L) :
    ∀ a ∈ F, ∀ b ∈ F, comp a b ∈ F := by
  classical
  have hmem : ∀ g : ↥L, permL ((g : Ah) : P45) ∈ F.toFinset := by
    intro g
    obtain ⟨l, hl, hrep⟩ := hF g g.2
    rw [List.mem_toFinset, permL_eq_of_repL hrep]
    exact hl
  have hinj : Function.Injective fun g : ↥L =>
      (⟨permL ((g : Ah) : P45), hmem g⟩ : ↥F.toFinset) := by
    intro g₁ g₂ hg
    have h1 : permL ((g₁ : Ah) : P45) = permL ((g₂ : Ah) : P45) := congrArg Subtype.val hg
    have h2 : ((g₁ : Ah) : P45) = ((g₂ : Ah) : P45) :=
      eq_of_repL (repL_permL _) (h1 ▸ repL_permL _)
    exact Subtype.ext (Subtype.ext h2)
  have h3 : Nat.card ↥F.toFinset = F.length := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]
  have hbij := hinj.bijective_of_nat_card_le (by rw [h3]; exact hcard)
  have hsurj : ∀ a ∈ F, ∃ s : ↥L, permL ((s : Ah) : P45) = a := by
    intro a ha
    obtain ⟨s, hs⟩ := hbij.2 ⟨a, List.mem_toFinset.2 ha⟩
    exact ⟨s, congrArg Subtype.val hs⟩
  intro a ha b hb
  obtain ⟨s, hs⟩ := hsurj a ha
  obtain ⟨t, ht⟩ := hsurj b hb
  have hra : RepL a ((s : Ah) : P45) := hs ▸ repL_permL _
  have hrb : RepL b ((t : Ah) : P45) := ht ▸ repL_permL _
  have hst := hmem (s * t)
  rw [List.mem_toFinset] at hst
  have : permL (((s * t : ↥L) : Ah) : P45) = comp a b :=
    permL_eq_of_repL (repL_mul hra hrb)
  rwa [this] at hst

theorem signA_xA : signA xA = 1 := signA_incl xY

theorem t0A_mem_TAh :
    t0A ∈ TAh := by
  have h : Tl.getD 20 [] ∈ Tl := by decide +kernel
  obtain ⟨y, hy, hyrep⟩ := exists_T_of_mem_Tl h
  have : t0A = incl y := Subtype.ext (eq_of_repL repL_t0A hyrep)
  rw [this]
  exact (mem_TAh_iff _).2 ⟨y, hy, rfl⟩

theorem signA_t0A :
    signA t0A = 1 := (signA_eq_one_iff _).2 t0A_mem_TAh.2

theorem signA_conj' (g u : Ah) : signA (g * u * g⁻¹) = signA u := by
  have := signA_conj g⁻¹ u
  simpa using this

theorem exists_Tl_of_mem_TAh
    {a : Ah} (ha : a ∈ TAh) : ∃ l ∈ Tl, RepL l (a : P45) := by
  obtain ⟨y, hy, rfl⟩ := (mem_TAh_iff a).1 ha
  obtain ⟨i, hi, hrep⟩ := (U42.mem_T_iff y).1 hy
  refine ⟨Tl.getD i [], ?_, hrep⟩
  rw [List.getD_eq_getElem _ _ (by have := U42.chkT_spec.1; omega)]
  exact List.getElem_mem _

theorem outer_inv_type {u : Ah}
    (hu : u ∈ That) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hout : u ∉ Yh) :
    IsGoodInv u ∨ ∃ k < 43, RepL (invL k) (u : P45) ∧ invTgt.getD k 0 = 3 := by
  obtain ⟨k, hk, hrep, g, -, hg⟩ := inv_type hu hu2 hu1
  have hneg : signA u = -1 := (signA_eq_neg_one_iff u).2 hout
  have hsg : signA (g * u * g⁻¹) = -1 := by rw [signA_conj', hneg]
  have htgt := inv_check.2.2 k hk
  generalize hj : invTgt.getD k 0 = j at htgt hg
  interval_cases j
  · exfalso
    have e : repA 0 = xA := by simp [repA]
    rw [e] at hg
    rw [hg, signA_xA] at hsg
    exact absurd hsg (by decide)
  · exfalso
    have : repA 1 = t0A := by simp [repA]
    rw [this] at hg
    rw [hg, signA_t0A] at hsg
    exact absurd hsg (by decide)
  · left
    have : repA 2 = fhatA := by simp [repA]
    rw [this] at hg
    refine ⟨That_le_Bh hu, hout, by rw [pow_two]; exact hu2, ?_⟩
    have e : u = g⁻¹ * fhatA * g⁻¹⁻¹ := by
      rw [← hg]
      group
    rw [e, card_centralizer_conj fhatA g⁻¹]
    exact card_centralizer_fhat
  · right
    exact ⟨k, hk, hrep, hj⟩

theorem signA_e0A : signA e0A = -1 := by
  rw [e0A, map_mul, signA_fhatA, signA_xA]
  rfl

theorem inner_inv_type {u : Ah}
    (hu : u ∈ TAh) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ j, (j = 0 ∨ j = 1) ∧ ∃ g : Ah, (g ∈ P1h ∨ g ∈ P2h) ∧ g * u * g⁻¹ = repA j := by
  obtain ⟨k, hk, -, g, hg, hgeq⟩ := inv_type hu.1 hu2 hu1
  have hs : signA (g * u * g⁻¹) = 1 := by
    rw [signA_conj']
    exact (signA_eq_one_iff u).2 hu.2
  have htgt := inv_check.2.2 k hk
  generalize hj : invTgt.getD k 0 = j at htgt hgeq
  refine ⟨j, ?_, g, hg, hgeq⟩
  interval_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    have e : repA 2 = fhatA := by simp [repA]
    rw [hgeq, e, signA_fhatA] at hs
    exact absurd hs (by decide)
  · exfalso
    have e : repA 3 = e0A := by simp [repA]
    rw [hgeq, e, signA_e0A] at hs
    exact absurd hs (by decide)

end CFSG.Quasithin.H13.F431.U42Aut
