module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieU3OStd

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieOdd

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ} {p : ℕ}

@[expose] def NotCentralizing {X : Type*} [Group X] (P Q : Subgroup X) : Prop :=
  ∃ g : X, (∀ y ∈ Q, g * y = y * g) ∧ ¬ ∀ y ∈ P, g * y = y * g

theorem NotCentralizing.map {X : Type*} [Group X] {P : Subgroup X} (α : X ≃* X)
    (hα : P.map α.toMonoidHom = P) {Q : Subgroup X} (h : NotCentralizing P Q) :
    NotCentralizing P (Q.map α.toMonoidHom) := by
  obtain ⟨g, hgQ, hgP⟩ := h
  refine ⟨α g, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    show α g * α y = α y * α g
    rw [← map_mul, ← map_mul, hgQ y hy]
  · intro hall
    apply hgP
    intro y hy
    have hy' : α y ∈ P := by
      rw [← hα]
      exact ⟨y, hy, rfl⟩
    have := hall (α y) hy'
    rw [← map_mul, ← map_mul] at this
    exact α.injective this

theorem comm_of_mem_zpowers {X : Type*} [Group X] {g x y : X} (hx : g * x = x * g)
    (hy : y ∈ Subgroup.zpowers x) : g * y = y * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact ((show Commute g x from hx).zpow_right k).eq

theorem eq_zpowers_of_card_prime [hp : Fact p.Prime] {X : Type*} [Group X] {Q : Subgroup X}
    (hQ : Nat.card Q = p) {q : X} (hq : q ∈ Q) (hq1 : q ≠ 1) : Q = Subgroup.zpowers q := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact hp.out.ne_zero)
  have hord : orderOf q ∣ p := by
    have := orderOf_dvd_natCard (⟨q, hq⟩ : Q)
    rwa [Subgroup.orderOf_mk, hQ] at this
  have hordp : orderOf q = p := by
    rcases (Nat.dvd_prime hp.out).1 hord with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hq1
    · exact h
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hq) ?_
  rw [Nat.card_zpowers, hordp, hQ]

theorem card_zpowers_prime [hp : Fact p.Prime] {X : Type*} [Group X] {q : X} (hqp : q ^ p = 1)
    (hq1 : q ≠ 1) : Nat.card (Subgroup.zpowers q) = p := by
  have hord : orderOf q ∣ p := orderOf_dvd_of_pow_eq_one hqp
  rw [Nat.card_zpowers]
  rcases (Nat.dvd_prime hp.out).1 hord with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hq1
  · exact h

theorem three_ne_zero_zmod [hp : Fact p.Prime] (hp3 : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro h
  have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 this)

theorem two_ne_zero_zmod [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)

theorem s01_comm_diag_iff (d : Fin 3 → Kˣ) :
    (s01GL : GL (Fin 3) K) * diagHom 3 d = diagHom 3 d * s01GL ↔ d 1 = d 0 := by
  rw [← mul_inv_eq_iff_eq_mul, s01GL_conj_diagHom, (diagHom_injective 3).eq_iff]
  constructor
  · intro h
    simpa using congrFun h 0
  · intro h
    funext i
    fin_cases i <;> simp [h]

theorem s12_comm_diag_iff (d : Fin 3 → Kˣ) :
    (s12GL : GL (Fin 3) K) * diagHom 3 d = diagHom 3 d * s12GL ↔ d 2 = d 1 := by
  rw [← mul_inv_eq_iff_eq_mul, s12GL_conj_diagHom, (diagHom_injective 3).eq_iff]
  constructor
  · intro h
    simpa using congrFun h 1
  · intro h
    funext i
    fin_cases i <;> simp [h]

theorem s02_comm_diag_iff (d : Fin 3 → Kˣ) :
    (s02GL : GL (Fin 3) K) * diagHom 3 d = diagHom 3 d * s02GL ↔ d 2 = d 0 := by
  rw [← mul_inv_eq_iff_eq_mul, s02GL_conj_diagHom, (diagHom_injective 3).eq_iff]
  constructor
  · intro h
    simpa using congrFun h 0
  · intro h
    funext i
    fin_cases i <;> simp [h]

section Dd

variable {ζ : Kˣ}

theorem s01_comm_dd_iff (hζ : orderOf ζ = p) (a b : ℕ) :
    (s01GL : GL (Fin 3) K) * dd ζ a b = dd ζ a b * s01GL ↔ (b : ZMod p) = a := by
  unfold dd
  rw [s01_comm_diag_iff]
  exact pow_eq_pow_iff hζ

theorem s12_comm_dd_iff (hζ : orderOf ζ = p) (a b : ℕ) :
    (s12GL : GL (Fin 3) K) * dd ζ a b = dd ζ a b * s12GL ↔ (a : ZMod p) + 2 * b = 0 := by
  unfold dd
  rw [s12_comm_diag_iff]
  show (ζ ^ a * ζ ^ b)⁻¹ = ζ ^ b ↔ _
  rw [inv_eq_iff_mul_eq_one, ← pow_add, ← pow_add, pow_eq_one_iff' hζ]
  push_cast
  constructor <;> intro h <;> linear_combination h

theorem s02_comm_dd_iff (hζ : orderOf ζ = p) (a b : ℕ) :
    (s02GL : GL (Fin 3) K) * dd ζ a b = dd ζ a b * s02GL ↔ 2 * (a : ZMod p) + b = 0 := by
  unfold dd
  rw [s02_comm_diag_iff]
  show (ζ ^ a * ζ ^ b)⁻¹ = ζ ^ a ↔ _
  rw [inv_eq_iff_mul_eq_one, ← pow_add, ← pow_add, pow_eq_one_iff' hζ]
  push_cast
  constructor <;> intro h <;> linear_combination h

theorem injective_dd_entries (hζ : orderOf ζ = p) {a b : ℕ} (hab : (a : ZMod p) ≠ b)
    (hbc : (a : ZMod p) + 2 * b ≠ 0) (hac : 2 * (a : ZMod p) + b ≠ 0) :
    Function.Injective (fun i : Fin 3 => ((![ζ ^ a, ζ ^ b, (ζ ^ a * ζ ^ b)⁻¹] i : Kˣ) : K)) := by
  intro i j hij
  have hij' : ![ζ ^ a, ζ ^ b, (ζ ^ a * ζ ^ b)⁻¹] i = ![ζ ^ a, ζ ^ b, (ζ ^ a * ζ ^ b)⁻¹] j :=
    Units.ext hij
  have e1 : ζ ^ a = ζ ^ b → False := fun h => hab ((pow_eq_pow_iff hζ).1 h)
  have e2 : ζ ^ b = (ζ ^ a * ζ ^ b)⁻¹ → False := fun h => by
    apply hbc
    have := (s12_comm_dd_iff (K := K) hζ a b).1
    apply this
    unfold dd
    rw [s12_comm_diag_iff]
    exact h.symm
  have e3 : ζ ^ a = (ζ ^ a * ζ ^ b)⁻¹ → False := fun h => by
    apply hac
    have := (s02_comm_dd_iff (K := K) hζ a b).1
    apply this
    unfold dd
    rw [s02_comm_diag_iff]
    exact h.symm
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij' e1
  · exact absurd hij' e3
  · exact absurd hij'.symm e1
  · rfl
  · exact absurd hij' e2
  · exact absurd hij'.symm e3
  · exact absurd hij'.symm e2
  · rfl

end Dd

theorem exists_special [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ c₂ c₃ : ℕ, (1 : ZMod p) + 2 * c₂ = 0 ∧ (2 : ZMod p) + c₃ = 0 := by
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hp1 := hp.out.one_lt
  refine ⟨(p - 1) / 2, p - 2, ?_, ?_⟩
  · have h1 : 1 + 2 * ((p - 1) / 2) = p := by omega
    have := congrArg (fun n : ℕ => (n : ZMod p)) h1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, ZMod.natCast_self] at this
    exact this
  · have h1 : 2 + (p - 2) = p := by omega
    have := congrArg (fun n : ℕ => (n : ZMod p)) h1
    simp only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self] at this
    exact this

end CFSG.Quasithin.H13.NQCore.U3O
