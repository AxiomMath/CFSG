module

public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutRed
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32AC50b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm

namespace Alt7

@[expose] def e9List : List (Perm (Fin 7)) :=
  ([0, 1, 2].flatMap fun i => [0, 1, 2].map fun j => c012 ^ i * c456 ^ j)

theorem e9_closed : (1 : Perm (Fin 7)) ∈ e9List ∧
    (∀ a ∈ e9List, ∀ b ∈ e9List, a * b ∈ e9List) ∧ ∀ a ∈ e9List, a⁻¹ ∈ e9List := by
  have h : decide ((1 : Perm (Fin 7)) ∈ e9List) = true ∧
      e9List.all (fun a => e9List.all fun b => decide (a * b ∈ e9List)) = true ∧
      e9List.all (fun a => decide (a⁻¹ ∈ e9List)) = true := by
    decide +kernel
  exact ⟨of_decide_eq_true h.1, of_all₂ h.2.1, of_all h.2.2⟩

theorem e9_facts : e9List.Nodup ∧ e9List.length = 9 ∧
    (∀ a ∈ e9List, ∀ b ∈ e9List, a * b = b * a) ∧ ∀ a ∈ e9List, a ^ 3 = 1 := by
  have h : e9List.Nodup ∧ e9List.length = 9 ∧
      e9List.all (fun a => e9List.all fun b => decide (a * b = b * a)) = true ∧
      e9List.all (fun a => decide (a ^ 3 = 1)) = true := by
    decide +kernel
  exact ⟨h.1, h.2.1, of_all₂ h.2.2.1, of_all h.2.2.2⟩

@[expose] def e9Sub : Subgroup (Perm (Fin 7)) := listSub e9List e9_closed

theorem card_e9Sub : Nat.card e9Sub = 9 := by
  rw [e9Sub, card_listSub _ _ e9_facts.1, e9_facts.2.1]

theorem mem_e9Sub {x : Perm (Fin 7)} : x ∈ e9Sub ↔ ∃ i j : ℕ, x = c012 ^ i * c456 ^ j := by
  constructor
  · intro hx
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
    exact ⟨i, j, rfl⟩
  · rintro ⟨i, j, rfl⟩
    have h3 : ∀ k : ℕ, c012 ^ k = c012 ^ (k % 3) ∧ c456 ^ k = c456 ^ (k % 3) := fun k => by
      have ha := three_facts.2.2.2.2.2.1
      have hb := three_facts.2.2.2.2.2.2.1
      constructor
      · conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, ha, one_pow, one_mul]
      · conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hb, one_pow, one_mul]
    rw [(h3 i).1, (h3 j).2]
    have hi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    show c012 ^ (i % 3) * c456 ^ (j % 3) ∈ e9List
    interval_cases (i % 3) <;> interval_cases (j % 3) <;> decide +kernel

end Alt7

theorem exists_e9_of_hom {A B : Type*} [Group A] [Finite A] [Group B] (φ : A →* B)
    (hker : IsPGroup 2 φ.ker) {E : Subgroup B} (hE : E ≤ φ.range) (hE9 : Nat.card E = 9)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ P : Subgroup A, IsElementaryAbelian 3 P ∧ Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := E.comap φ with hQ
  obtain ⟨m, hm⟩ := hker.exists_card_eq
  have hφQ : (φ.comp Q.subtype).range = E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hQ, Subgroup.map_comap_eq,
      inf_eq_right.mpr hE]
  have hkerQ : Nat.card (φ.comp Q.subtype).ker = 2 ^ m := by
    rw [← hm]
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.2⟩, fun x => ⟨⟨x.1, ?_⟩, x.2⟩, fun _ => rfl,
      fun _ => rfl⟩
    show φ x.1 ∈ E
    rw [MonoidHom.mem_ker.mp x.2]
    exact E.one_mem
  have hcardQ : Nat.card Q = 2 ^ m * 9 := by
    rw [← hkerQ, ← hE9, ← hφQ, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      mul_comm]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _)
  obtain ⟨P⟩ : Nonempty (Sylow 3 Q) := inferInstance
  obtain ⟨r, hr⟩ := P.isPGroup'.exists_card_eq
  have hPi : ¬ 3 ∣ (P : Subgroup Q).index := P.not_dvd_index
  have hPmul := (P : Subgroup Q).card_mul_index
  rw [hr, hcardQ] at hPmul
  have hr2 : r = 2 := by
    have h1 : 3 ^ r ∣ 2 ^ m * 9 := ⟨_, hPmul.symm⟩
    have h2 : 3 ^ r ∣ 9 := (Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 3 2)) h1)
    have hr2 : r ≤ 2 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at h2
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
    by_contra hne
    have hr1 : r < 2 := lt_of_le_of_ne hr2 hne
    apply hPi
    have e : (P : Subgroup Q).index = 2 ^ m * 3 ^ (2 - r) := by
      have h9 : 2 ^ m * 9 = 3 ^ r * (2 ^ m * 3 ^ (2 - r)) := by
        have e9 : (9 : ℕ) = 3 ^ r * 3 ^ (2 - r) := by
          rw [← pow_add, show r + (2 - r) = 2 by omega]
          norm_num
        rw [e9]
        ring
      rw [h9] at hPmul
      exact Nat.eq_of_mul_eq_mul_left (by positivity) hPmul
    rw [e]
    exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  subst hr2
  set ψ : ↥(P : Subgroup Q) →* B := (φ.comp Q.subtype).comp (P : Subgroup Q).subtype with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := hker ⟨((x : Q) : A), hx⟩
    have hk' : x ^ 2 ^ k = 1 := Subtype.ext (Subtype.ext (by
      have := congrArg (fun y : φ.ker => (y : A)) hk
      simpa using this))
    obtain ⟨j, hj⟩ := P.isPGroup' x
    have h1 := orderOf_dvd_of_pow_eq_one hk'
    have h2 := orderOf_dvd_of_pow_eq_one hj
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 2 3)) h1 h2)
  have hψE : ∀ x, ψ x ∈ E := fun x => x.1.2
  have hcomm : ∀ x y : ↥(P : Subgroup Q), x * y = y * x := fun x y =>
    hψinj (by rw [map_mul, map_mul]; exact hEc _ (hψE x) _ (hψE y))
  have hexp : ∀ x : ↥(P : Subgroup Q), x ^ 3 = 1 := fun x =>
    hψinj (by rw [map_pow, map_one]; exact hE3 _ (hψE x))
  set P' : Subgroup A := ((P : Subgroup Q).map Q.subtype) with hP'
  have e : ↥(P : Subgroup Q) ≃* ↥P' :=
    (P : Subgroup Q).equivMapOfInjective Q.subtype Q.subtype_injective
  refine ⟨P', ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨x', rfl⟩ := e.surjective x
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hcomm]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨x', rfl⟩ := e.surjective x
      rw [← map_pow, hexp, map_one]
  · rw [← Nat.card_congr e.toEquiv, hr]
    norm_num

theorem two_le_pRank_of_e9 {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsElementaryAbelian 3 P) (h9 : Nat.card P = 9) : 2 ≤ CFSG.pRank 3 X :=
  CFSG.LieType.SteinbergBR.le_pRank_of_card (by norm_num) P hP (by rw [h9]; norm_num)

end CFSG.Quasithin.H13.L32A.C
