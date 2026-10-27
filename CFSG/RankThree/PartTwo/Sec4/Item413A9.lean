module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG

theorem three_mul_le_three_pow (a : ℕ) : 3 * a ≤ 3 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · norm_num
    · have h1 : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
      calc 3 * (a + 1) = 3 * a + 3 := by ring
        _ ≤ 3 ^ a + 3 := by omega
        _ ≤ 3 ^ a + 2 * 3 ^ a := by
            have : 3 ≤ 3 ^ a := by
              calc 3 = 3 ^ 1 := by norm_num
                _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha
            omega
        _ = 3 ^ (a + 1) := by ring

section Perm

variable {α : Type*} [Finite α]

theorem card_pow_three_le_of_faithful (n : ℕ) :
    ∀ (E : Subgroup (Equiv.Perm α)) (S : Set α), S.ncard ≤ n →
      (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) → (∀ e ∈ E, e ^ 3 = 1) →
      (∀ e ∈ E, ∀ x ∈ S, e x ∈ S) → (∀ e ∈ E, (∀ x ∈ S, e x = x) → e = 1) →
      Nat.card E ^ 3 ≤ 3 ^ S.ncard := by
  induction n with
  | zero =>
    intro E S hS _ _ _ hfaith
    have hS0 : S = ∅ := (Set.ncard_eq_zero (Set.toFinite S)).mp (by omega)
    have hE : E = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      rw [Subgroup.mem_bot]
      exact hfaith e he (by simp [hS0])
    rw [hE, Subgroup.card_bot, one_pow]
    exact Nat.one_le_pow _ _ (by norm_num)
  | succ n ih =>
    intro E S hS hcomm h3 hinv hfaith
    rcases S.eq_empty_or_nonempty with hS0 | ⟨x, hx⟩
    · have hE : E = ⊥ := by
        rw [eq_bot_iff]
        intro e he
        rw [Subgroup.mem_bot]
        exact hfaith e he (by simp [hS0])
      rw [hE, Subgroup.card_bot, one_pow]
      exact Nat.one_le_pow _ _ (by norm_num)
    set O : Set α := {y | ∃ e ∈ E, e x = y} with hOdef
    set E₁ : Subgroup (Equiv.Perm α) := E ⊓ MulAction.stabilizer (Equiv.Perm α) x with hE₁def
    have hOS : O ⊆ S := by
      rintro _ ⟨e, he, rfl⟩
      exact hinv e he x hx
    have hE₁O : ∀ e ∈ E₁, ∀ y ∈ O, e y = y := by
      rintro e ⟨heE, hex⟩ _ ⟨g, hg, rfl⟩
      have hex' : e x = x := hex
      calc e (g x) = (e * g) x := rfl
        _ = (g * e) x := by rw [hcomm e heE g hg]
        _ = g (e x) := rfl
        _ = g x := by rw [hex']
    have horbit : MulAction.orbit E x = O := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g, g.2, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨⟨e, he⟩, rfl⟩
    have hstab : (MulAction.stabilizer E x).map E.subtype = E₁ := by
      ext e
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨g.2, hg⟩
      · rintro ⟨he, hex⟩
        exact ⟨⟨e, he⟩, hex, rfl⟩
    have hcard : Nat.card E = O.ncard * Nat.card E₁ := by
      rw [← Subgroup.card_mul_index (MulAction.stabilizer E x), MulAction.index_stabilizer,
        horbit, ← hstab, Subgroup.card_map_of_injective E.subtype_injective, mul_comm]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using h3 g g.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (hk ▸ Dvd.intro _ hcard.symm : O.ncard ∣ 3 ^ k)
    have hE₁E : E₁ ≤ E := inf_le_left
    have hinv₁ : ∀ e ∈ E₁, ∀ y ∈ S \ O, e y ∈ S \ O := by
      rintro e he y ⟨hyS, hyO⟩
      refine ⟨hinv e (hE₁E he) y hyS, fun ⟨g, hg, hgy⟩ => hyO ⟨e⁻¹ * g,
        E.mul_mem (E.inv_mem (hE₁E he)) hg, ?_⟩⟩
      simp [Equiv.Perm.mul_apply, hgy]
    have hfaith₁ : ∀ e ∈ E₁, (∀ y ∈ S \ O, e y = y) → e = 1 := by
      intro e he h
      refine hfaith e (hE₁E he) fun z hz => ?_
      by_cases hzO : z ∈ O
      · exact hE₁O e he z hzO
      · exact h z ⟨hz, hzO⟩
    have hxO : x ∈ O := ⟨1, E.one_mem, rfl⟩
    have hOcard : 0 < O.ncard := (Set.ncard_pos (Set.toFinite O)).mpr ⟨x, hxO⟩
    have hdiff : (S \ O).ncard = S.ncard - O.ncard := Set.ncard_sdiff hOS
    have hOle : O.ncard ≤ S.ncard := Set.ncard_le_ncard hOS
    have hIH := ih E₁ (S \ O) (by omega)
      (fun e he f hf => hcomm e (hE₁E he) f (hE₁E hf)) (fun e he => h3 e (hE₁E he)) hinv₁
      hfaith₁
    have hO3 : O.ncard ^ 3 ≤ 3 ^ O.ncard := by
      rw [ha, ← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right (by norm_num) (three_mul_le_three_pow a)
    calc Nat.card E ^ 3 = O.ncard ^ 3 * Nat.card E₁ ^ 3 := by rw [hcard, mul_pow]
      _ ≤ 3 ^ O.ncard * 3 ^ (S \ O).ncard := Nat.mul_le_mul hO3 hIH
      _ = 3 ^ S.ncard := by
          rw [← pow_add, hdiff]
          congr 1
          omega

end Perm

theorem rankA9_holds :
    CFSG.pRank 3 (alternatingGroup (Fin 9) ⧸ Subgroup.center (alternatingGroup (Fin 9))) ≤ 3 := by
  have hZ : Subgroup.center (alternatingGroup (Fin 9)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  set e : alternatingGroup (Fin 9) ⧸ Subgroup.center (alternatingGroup (Fin 9)) ≃*
      alternatingGroup (Fin 9) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine csSup_le' ?_
  rintro r ⟨B, hB, hcard⟩
  set f : alternatingGroup (Fin 9) ⧸ Subgroup.center (alternatingGroup (Fin 9)) →*
      Equiv.Perm (Fin 9) := (alternatingGroup (Fin 9)).subtype.comp e.toMonoidHom
  have hf : Function.Injective f :=
    (alternatingGroup (Fin 9)).subtype_injective.comp e.injective
  have hcomm : ∀ x ∈ B.map f, ∀ y ∈ B.map f, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hB.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have h3 : ∀ x ∈ B.map f, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (A := B) x hx, map_one]
  have hle := card_pow_three_le_of_faithful (Set.univ : Set (Fin 9)).ncard (B.map f) Set.univ
    le_rfl hcomm h3 (fun _ _ _ _ => Set.mem_univ _)
    (fun e _ he => Equiv.ext fun x => he x (Set.mem_univ x))
  rw [Subgroup.card_map_of_injective hf, hcard, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin, ← pow_mul] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  omega

end CFSG.RankThree.PartTwo.Sec4
