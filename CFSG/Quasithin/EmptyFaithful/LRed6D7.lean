module

public import CFSG.Quasithin.EmptyFaithful.LRed6Real
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin

namespace LRed6

namespace D7

open Equiv Finset

abbrev P7 : Type := G6.PermMod 7

theorem sq_eq_one (m : P7) : m * m = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  change Multiplicative.toAdd m i + Multiplicative.toAdd m i = 0
  exact CharTwo.add_self_eq_zero _

theorem toAdd_act (σ : Perm (Fin 7)) (m : P7) (i : Fin 7) :
    Multiplicative.toAdd (G6.permAct 7 σ m) i = Multiplicative.toAdd m (σ⁻¹ i) := rfl

theorem exists_split {M : Subgroup P7} {σ : Perm (Fin 7)} (hσ3 : σ ^ 3 = 1)
    (hσM : ∀ m ∈ M, G6.permAct 7 σ m ∈ M) (hfree : ∀ m ∈ M, G6.permAct 7 σ m = m → m = 1)
    {m : P7} (hm : m ∈ M) : ∃ u ∈ M, m = u * G6.permAct 7 σ u := by
  set a : MulAut P7 := G6.permAct 7 σ with ha
  have ha3 : a ^ 3 = 1 := by rw [ha, ← map_pow, hσ3, map_one]
  have h3 : a (a (a m)) = m := by
    have : (a ^ 3) m = m := by rw [ha3]; rfl
    simpa [pow_succ, MulAut.mul_apply] using this
  have hu : a m ∈ M := hσM m hm
  have hu2 : a (a m) ∈ M := hσM _ hu
  have hN : m * a m * a (a m) = 1 := by
    apply hfree _ (M.mul_mem (M.mul_mem hm hu) hu2)
    rw [map_mul, map_mul, h3, mul_comm (a m * a (a m)) m, ← mul_assoc]
  refine ⟨a m, hu, ?_⟩
  have h1 : m * (a m * a (a m)) = 1 := by rw [← mul_assoc]; exact hN
  have h2 := sq_eq_one m
  calc m = m * (m * (a m * a (a m))) := by rw [h1, mul_one]
    _ = (m * m) * (a m * a (a m)) := by rw [mul_assoc]
    _ = a m * a (a m) := by rw [h2, one_mul]

theorem sum_stable (σ : Perm (Fin 7)) (u : P7) (O : Finset (Fin 7)) (hO : ∀ i, i ∈ O ↔ σ i ∈ O) :
    ∑ i ∈ O, Multiplicative.toAdd (u * G6.permAct 7 σ u) i = 0 := by
  have h1 : ∑ i ∈ O, Multiplicative.toAdd (G6.permAct 7 σ u) i =
      ∑ i ∈ O, Multiplicative.toAdd u i := by
    simp only [toAdd_act]
    refine Finset.sum_nbij' (fun i => σ⁻¹ i) (fun i => σ i) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      exact (hO _).mpr (by simpa using hi)
    · intro i hi
      exact (hO i).mp hi
    · intro i _
      simp
    · intro i _
      simp
    · intro i _
      rfl
  simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib, h1]
  exact CharTwo.add_self_eq_zero _

theorem orbit_facts {σ : Perm (Fin 7)} (hσ3 : σ ^ 3 = 1) {i₀ : Fin 7} (h : σ i₀ ≠ i₀) :
    ({i₀, σ i₀, σ (σ i₀)} : Finset (Fin 7)).card = 3 ∧
      (∀ i, i ∈ ({i₀, σ i₀, σ (σ i₀)} : Finset (Fin 7)) ↔
        σ i ∈ ({i₀, σ i₀, σ (σ i₀)} : Finset (Fin 7))) ∧
      (∀ i ∈ ({i₀, σ i₀, σ (σ i₀)} : Finset (Fin 7)), σ i ≠ i) := by
  have h3 : σ (σ (σ i₀)) = i₀ := by
    have := congrArg (fun f : Perm (Fin 7) => f i₀) hσ3
    simpa [pow_succ, Perm.mul_apply] using this
  have hne2 : σ (σ i₀) ≠ σ i₀ := fun e => h (σ.injective e)
  have hne3 : σ (σ i₀) ≠ i₀ := fun e => h (by
    have := congrArg σ e
    rw [h3] at this
    exact this.symm)
  refine ⟨Finset.card_eq_three.mpr ⟨i₀, σ i₀, σ (σ i₀), h.symm, hne3.symm, hne2.symm, rfl⟩, ?_, ?_⟩
  · intro i
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl h3
    · rintro (e | e | e)
      · right; right
        apply σ.injective
        rw [e, h3]
      · left
        exact σ.injective e
      · right; left
        exact σ.injective e
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact h
    · exact hne2
    · intro e
      apply hne3
      rw [h3] at e
      exact e.symm

set_option maxRecDepth 100000 in
theorem count_six : ∀ mv O₁ : Finset (Fin 7), O₁ ⊆ mv → mv.card = 6 → O₁.card = 3 →
    (Finset.univ.filter (fun f : Fin 7 → ZMod 2 =>
      (∀ i, i ∉ mv → f i = 0) ∧ ∑ i, f i = 0 ∧ ∑ i ∈ O₁, f i = 0)).card ≤ 16 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem count_three : ∀ mv : Finset (Fin 7), mv.card ≤ 3 →
    (Finset.univ.filter (fun f : Fin 7 → ZMod 2 =>
      (∀ i, i ∉ mv → f i = 0) ∧ ∑ i, f i = 0)).card ≤ 4 := by
  decide +kernel

theorem card_le_of_subset {M : Subgroup P7} (F : Finset (Fin 7 → ZMod 2))
    (hF : ∀ m ∈ M, Multiplicative.toAdd m ∈ F) : Nat.card ↥M ≤ F.card := by
  have hinj : Function.Injective
      (fun m : ↥M => (⟨Multiplicative.toAdd (m : P7), hF m m.2⟩ : ↥F)) := by
    intro a b h
    have h' : Multiplicative.toAdd (a : P7) = Multiplicative.toAdd (b : P7) := by
      simpa using congrArg Subtype.val h
    exact Subtype.ext (Multiplicative.toAdd.injective h')
  calc Nat.card ↥M ≤ Nat.card ↥F := Nat.card_le_card_of_injective _ hinj
    _ = F.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]

theorem mem_of_card_le {M : Subgroup P7} (F : Finset (Fin 7 → ZMod 2))
    (hF : ∀ m ∈ M, Multiplicative.toAdd m ∈ F) (hc : F.card ≤ Nat.card ↥M) {f : Fin 7 → ZMod 2}
    (hf : f ∈ F) : Multiplicative.ofAdd f ∈ M := by
  have hinj : Function.Injective
      (fun m : ↥M => (⟨Multiplicative.toAdd (m : P7), hF m m.2⟩ : ↥F)) := by
    intro a b h
    have h' : Multiplicative.toAdd (a : P7) = Multiplicative.toAdd (b : P7) := by
      simpa using congrArg Subtype.val h
    exact Subtype.ext (Multiplicative.toAdd.injective h')
  have hc' : Nat.card ↥F ≤ Nat.card ↥M := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hc
  obtain ⟨m, hm⟩ := (hinj.bijective_of_nat_card_le hc').2 ⟨f, hf⟩
  have : Multiplicative.toAdd (m : P7) = f := congrArg Subtype.val hm
  rw [← this]
  exact m.2

def ind (a b : Fin 7) : Fin 7 → ZMod 2 := fun i => if i = a ∨ i = b then 1 else 0

theorem ind_sum : ∀ a b : Fin 7, a ≠ b → ∑ i, ind a b i = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem ind_sum_sub : ∀ a b : Fin 7, a ≠ b → ∀ O : Finset (Fin 7), (a ∈ O ↔ b ∈ O) →
    ∑ i ∈ O, ind a b i = 0 := by
  decide +kernel

theorem pair_fix {x : Perm (Fin 7)} {a b : Fin 7}
    (h : G6.permAct 7 x (Multiplicative.ofAdd (ind a b)) = Multiplicative.ofAdd (ind a b)) :
    (x a = a ∨ x a = b) ∧ (x b = a ∨ x b = b) := by
  have key : ∀ c : Fin 7, (c = a ∨ c = b) → (x c = a ∨ x c = b) := by
    intro c hc
    have h1 := congrFun (congrArg Multiplicative.toAdd h) (x c)
    rw [toAdd_act] at h1
    have e1 : x⁻¹ (x c) = c := by simp
    simp only [toAdd_ofAdd, e1] at h1
    have h2 : ind a b c = 1 := by simp [ind, hc]
    rw [h2] at h1
    by_contra hcon
    have h3 : ind a b (x c) = 0 := by simp [ind]; tauto
    rw [h3] at h1
    exact absurd h1 (by decide)
  exact ⟨key a (Or.inl rfl), key b (Or.inr rfl)⟩

theorem triple_fix {x : Perm (Fin 7)} {a b c : Fin 7} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : G6.permAct 7 x (Multiplicative.ofAdd (ind a b)) = Multiplicative.ofAdd (ind a b))
    (h2 : G6.permAct 7 x (Multiplicative.ofAdd (ind a c)) = Multiplicative.ofAdd (ind a c))
    (h3 : G6.permAct 7 x (Multiplicative.ofAdd (ind b c)) = Multiplicative.ofAdd (ind b c)) :
    x a = a ∧ x b = b ∧ x c = c := by
  obtain ⟨ha1, hb1⟩ := pair_fix h1
  obtain ⟨ha2, hc2⟩ := pair_fix h2
  obtain ⟨hb3, hc3⟩ := pair_fix h3
  refine ⟨?_, ?_, ?_⟩
  · rcases ha1 with e | e
    · exact e
    · rcases ha2 with e' | e'
      · exact e'
      · exact absurd (e.symm.trans e') hbc
  · rcases hb1 with e | e
    · rcases hb3 with e' | e'
      · exact absurd (e.symm.trans e') hab
      · exact absurd (e.symm.trans e') hac
    · exact e
  · rcases hc2 with e | e
    · rcases hc3 with e' | e'
      · exact absurd (e.symm.trans e') hab
      · exact absurd (e.symm.trans e') hac
    · exact e

theorem d7_core (M : Subgroup P7) (hM : M ≤ G6.coreMod 7) (hcard : Nat.card ↥M = 16)
    (σ x : Perm (Fin 7)) (hσ3 : σ ^ 3 = 1) (hσM : ∀ m ∈ M, G6.permAct 7 σ m ∈ M)
    (hfree : ∀ m ∈ M, G6.permAct 7 σ m = m → m = 1)
    (hx : ∀ m ∈ M, G6.permAct 7 x m = m) : x = 1 := by
  classical
  have hsplit : ∀ m ∈ M, ∃ u ∈ M, m = u * G6.permAct 7 σ u :=
    fun m hm => exists_split hσ3 hσM hfree hm
  have hfixed : ∀ m ∈ M, ∀ p : Fin 7, σ p = p → Multiplicative.toAdd m p = 0 := by
    intro m hm p hp
    obtain ⟨u, -, rfl⟩ := hsplit m hm
    have := sum_stable σ u {p} (by
      intro i
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl
        exact hp
      · intro h
        exact σ.injective (h.trans hp.symm))
    simpa using this
  have hsum : ∀ m ∈ M, ∑ i, Multiplicative.toAdd m i = 0 := fun m hm => hM hm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod : (σ.support)ᶜ.card ≡ Fintype.card (Fin 7) [MOD 3] :=
    Perm.card_compl_support_modEq (p := 3) (n := 1) (by simpa using hσ3)
  have hcompl : σ.support.card + (σ.support)ᶜ.card = 7 := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  have hs : σ.support.card = 0 ∨ σ.support.card = 3 ∨ σ.support.card = 6 := by
    simp only [Nat.ModEq, Fintype.card_fin] at hmod
    omega
  have hsupp : ∀ F : Finset (Fin 7 → ZMod 2), ∀ i, i ∉ σ.support → σ i = i := fun F i hi =>
    Perm.notMem_support.mp hi
  rcases hs with h0 | h3 | h6
  ·
    have hσ1 : σ = 1 := Perm.card_support_eq_zero.mp h0
    have hbot : M = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have := hfree m hm (by rw [hσ1, map_one]; rfl)
      simpa using this
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  ·
    exfalso
    set F : Finset (Fin 7 → ZMod 2) := Finset.univ.filter (fun f : Fin 7 → ZMod 2 =>
      (∀ i, i ∉ σ.support → f i = 0) ∧ ∑ i, f i = 0) with hF
    have h1 : Nat.card ↥M ≤ F.card := by
      refine card_le_of_subset F fun m hm => ?_
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun i hi => hfixed m hm i (hsupp F i hi), hsum m hm⟩
    have h2 : F.card ≤ 4 := count_three σ.support (le_of_eq h3)
    omega
  ·
    have hne : σ.support.Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨i₀, hi₀⟩ := hne
    have hmov : σ i₀ ≠ i₀ := Perm.mem_support.mp hi₀
    obtain ⟨hc3, hst, hmv⟩ := orbit_facts hσ3 hmov
    set O₁ : Finset (Fin 7) := {i₀, σ i₀, σ (σ i₀)} with hO₁
    have hO₁sub : O₁ ⊆ σ.support := fun i hi => Perm.mem_support.mpr (hmv i hi)
    set O₂ : Finset (Fin 7) := σ.support \ O₁ with hO₂
    have hc2 : O₂.card = 3 := by
      rw [hO₂, Finset.card_sdiff_of_subset hO₁sub, h6, hc3]
    set F : Finset (Fin 7 → ZMod 2) := Finset.univ.filter (fun f : Fin 7 → ZMod 2 =>
      (∀ i, i ∉ σ.support → f i = 0) ∧ ∑ i, f i = 0 ∧ ∑ i ∈ O₁, f i = 0) with hF
    have hFM : ∀ m ∈ M, Multiplicative.toAdd m ∈ F := by
      intro m hm
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun i hi => hfixed m hm i (hsupp F i hi), hsum m hm, ?_⟩
      obtain ⟨u, -, rfl⟩ := hsplit m hm
      exact sum_stable σ u O₁ hst
    have hFcard : F.card ≤ 16 := count_six σ.support O₁ hO₁sub h6 hc3
    have hmem : ∀ a b : Fin 7, a ≠ b → a ∈ σ.support → b ∈ σ.support → (a ∈ O₁ ↔ b ∈ O₁) →
        Multiplicative.ofAdd (ind a b) ∈ M := by
      intro a b hab ha hb hO
      refine mem_of_card_le F hFM (by omega) ?_
      simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun i hi => ?_, ind_sum a b hab, ind_sum_sub a b hab O₁ hO⟩
      have hia : i ≠ a := fun e => hi (e ▸ ha)
      have hib : i ≠ b := fun e => hi (e ▸ hb)
      simp [ind, hia, hib]
    have hfix3 : ∀ a b c : Fin 7, a ≠ b → a ≠ c → b ≠ c → a ∈ σ.support → b ∈ σ.support →
        c ∈ σ.support → ((a ∈ O₁ ↔ b ∈ O₁) ∧ (a ∈ O₁ ↔ c ∈ O₁) ∧ (b ∈ O₁ ↔ c ∈ O₁)) →
        x a = a ∧ x b = b ∧ x c = c := by
      intro a b c hab hac hbc ha hb hc ⟨h1, h2, h3⟩
      exact triple_fix hab hac hbc (hx _ (hmem a b hab ha hb h1)) (hx _ (hmem a c hac ha hc h2))
        (hx _ (hmem b c hbc hb hc h3))
    have hne1 : σ i₀ ≠ i₀ := hmov
    have hne2 : σ (σ i₀) ≠ σ i₀ := fun e => hmov (σ.injective e)
    have hne3 : σ (σ i₀) ≠ i₀ := fun e => hmov (by
      have h3' : σ (σ (σ i₀)) = i₀ := by
        have := congrArg (fun f : Perm (Fin 7) => f i₀) hσ3
        simpa [pow_succ, Perm.mul_apply] using this
      have := congrArg σ e
      rw [h3'] at this
      exact this.symm)
    have hin1 : ∀ i ∈ O₁, x i = i := by
      have hi0 : i₀ ∈ O₁ := by simp [hO₁]
      have hi1 : σ i₀ ∈ O₁ := by simp [hO₁]
      have hi2 : σ (σ i₀) ∈ O₁ := by simp [hO₁]
      obtain ⟨e0, e1, e2⟩ := hfix3 i₀ (σ i₀) (σ (σ i₀)) hne1.symm hne3.symm hne2.symm
        (hO₁sub hi0) (hO₁sub hi1) (hO₁sub hi2) ⟨iff_of_true hi0 hi1, iff_of_true hi0 hi2,
          iff_of_true hi1 hi2⟩
      intro i hi
      simp only [hO₁, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> assumption
    have hin2 : ∀ i ∈ O₂, x i = i := by
      obtain ⟨a, b, c, hab, hac, hbc, hO2e⟩ := Finset.card_eq_three.mp hc2
      have ha : a ∈ O₂ := by rw [hO2e]; simp
      have hb : b ∈ O₂ := by rw [hO2e]; simp
      have hc : c ∈ O₂ := by rw [hO2e]; simp
      have hO₂sub : ∀ i ∈ O₂, i ∈ σ.support ∧ i ∉ O₁ := fun i hi => by
        rw [hO₂, Finset.mem_sdiff] at hi
        exact hi
      obtain ⟨e0, e1, e2⟩ := hfix3 a b c hab hac hbc (hO₂sub a ha).1 (hO₂sub b hb).1
        (hO₂sub c hc).1 ⟨iff_of_false (hO₂sub a ha).2 (hO₂sub b hb).2,
          iff_of_false (hO₂sub a ha).2 (hO₂sub c hc).2,
          iff_of_false (hO₂sub b hb).2 (hO₂sub c hc).2⟩
      intro i hi
      rw [hO2e] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> assumption
    have hxs : x.support ⊆ (σ.support)ᶜ := by
      intro i hi
      rw [Finset.mem_compl]
      intro hiσ
      have hxi : x i = i := by
        by_cases h1 : i ∈ O₁
        · exact hin1 i h1
        · exact hin2 i (by rw [hO₂, Finset.mem_sdiff]; exact ⟨hiσ, h1⟩)
      exact Perm.mem_support.mp hi hxi
    have hcx : x.support.card ≤ 1 := by
      have := Finset.card_le_card hxs
      omega
    have h0 : x.support.card = 0 := by
      have := Perm.card_support_ne_one x
      omega
    exact Perm.card_support_eq_zero.mp h0

end D7

section Alt7

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit

variable {V : Type*} [CommGroup V]

theorem alt7_fix {L : Subgroup (MulAut V)} {U Z : Subgroup V} (h : AlternatingNatural L U Z 7)
    {W : Subgroup V} [Finite ↥W] (hWU : W ≤ U) (hWZ : W ⊓ Z = ⊥) (hW : Nat.card ↥W = 16)
    {a : MulAut V} (ha : a ∈ L) (ha3 : a ^ 3 = 1) (haW : ∀ w ∈ W, a w ∈ W)
    (haC : ∀ w ∈ W, a w = w → w = 1) {x : MulAut V} (hx : x ∈ L) (hxW : ∀ w ∈ W, x w = w) :
    x = 1 := by
  obtain ⟨π₀, hπ₀⟩ := h
  let π : ↥(alternatingGroup (Fin 7)) →* ↥L := π₀
  have hπ : (FFModel.altDn 7).RealizesVia L U Z π := hπ₀
  have hinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
  obtain ⟨τ, hτ⟩ : ∃ τ : ↥(alternatingGroup (Fin 7)), π τ = ⟨a, ha⟩ := hπ.1 ⟨a, ha⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(alternatingGroup (Fin 7)), π γ = ⟨x, hx⟩ := hπ.1 ⟨x, hx⟩
  have hτ3 : τ ^ 3 = 1 := by
    apply hinj
    calc π (τ ^ 3) = (π τ) ^ 3 := map_pow π τ 3
      _ = (⟨a, ha⟩ : ↥L) ^ 3 := by rw [hτ]
      _ = 1 := Subtype.ext ha3
      _ = π 1 := (map_one π).symm
  have hker : (FFModel.altDn 7).ker = ⊥ := by
    have hc : Nat.card ↥(FFModel.altDn 7).ker = 1 := by
      show Nat.card ↥(Subgroup.zpowers (G6.allOnes 7) ⊓ G6.coreMod 7) = 1
      rw [card_dnZ (by norm_num)]
      decide
    exact Subgroup.eq_bot_of_card_eq _ hc
  obtain ⟨Wm, hWm, -, hcardWm, hfix, hstab, hfree⟩ := exists_preimage hπ hWU hWZ
  have hτW : ∀ w ∈ W, ((π τ : ↥L) : MulAut V) w = w → w = 1 := by
    intro w hw hwτ
    rw [hτ] at hwτ
    exact haC w hw hwτ
  have hτWm : ∀ w ∈ W, ((π τ : ↥L) : MulAut V) w ∈ W := by
    intro w hw
    rw [hτ]
    exact haW w hw
  have hγW : ∀ w ∈ W, ((π γ : ↥L) : MulAut V) w = w := by
    intro w hw
    rw [hγ]
    exact hxW w hw
  have hcard16 : Nat.card ↥Wm = 16 := by
    rw [hcardWm, hW, hker, Subgroup.card_bot]
  have hx1 : (γ : Equiv.Perm (Fin 7)) = 1 := by
    refine D7.d7_core Wm hWm hcard16 (τ : Equiv.Perm (Fin 7)) (γ : Equiv.Perm (Fin 7)) ?_ ?_ ?_ ?_
    · have := congrArg (fun g : ↥(alternatingGroup (Fin 7)) => (g : Equiv.Perm (Fin 7))) hτ3
      simpa using this
    · intro m hm
      exact hstab τ hτWm m hm
    · intro m hm hmτ
      have h1 := hfree τ hτWm hτW m hm (by
        rw [hker]
        have : (FFModel.altDn 7).act τ m = m := hmτ
        exact Subgroup.mem_bot.mpr (mul_inv_eq_one.mpr this))
      rw [hker] at h1
      exact Subgroup.mem_bot.mp h1
    · intro m hm
      have h1 := hfix γ hγW m hm
      rw [hker] at h1
      have := Subgroup.mem_bot.mp h1
      exact mul_inv_eq_one.mp this
  have hγ1 : γ = 1 := Subtype.ext hx1
  have h3 : (⟨x, hx⟩ : ↥L) = 1 := by rw [← hγ, hγ1, map_one]
  exact congrArg Subtype.val h3

end Alt7

end LRed6

end CFSG.Quasithin
