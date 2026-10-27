module

public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace CoreP

section Combinatorics

theorem eq_or_eq_or_eq_of_card_eq_three {α : Type*} [Finite α] (h : Nat.card α = 3) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (d : α) : d = a ∨ d = b ∨ d = c := by
  obtain ⟨e⟩ : Nonempty (α ≃ Fin 3) := ⟨Finite.equivFinOfCardEq h⟩
  have key : ∀ a b c d : Fin 3, a ≠ b → a ≠ c → b ≠ c → d = a ∨ d = b ∨ d = c := by decide
  rcases key (e a) (e b) (e c) (e d) (e.injective.ne hab) (e.injective.ne hac)
    (e.injective.ne hbc) with h | h | h
  · exact Or.inl (e.injective h)
  · exact Or.inr (Or.inl (e.injective h))
  · exact Or.inr (Or.inr (e.injective h))

theorem exists_two_pow_mul_three_pow_of_dvd {n a : ℕ} (h : n ∣ 3 * 2 ^ a) :
    ∃ i j : ℕ, n = 2 ^ i * 3 ^ j := by
  obtain ⟨k₁, k₂, hk₁, hk₂, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk₂
  rcases (Nat.dvd_prime Nat.prime_three).mp hk₁ with rfl | rfl
  · exact ⟨i, 0, by simp⟩
  · exact ⟨i, 1, by ring⟩

theorem not_three_dvd_two_pow (a : ℕ) : ¬ 3 ∣ 2 ^ a := fun h => by
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

end Combinatorics

section Coset

theorem mem_normalCore_iff {X : Type*} [Group X] {H : Subgroup X} {r : X} :
    r ∈ H.normalCore ↔ ∀ g : X, g * r * g⁻¹ ∈ H := Iff.rfl

theorem exists_mul_of_index_three {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : H.index = 3) {c : X} (hc : c ∉ H) (hc2 : c ^ 2 ∉ H) (g : X) :
    (∃ h ∈ H, g = h) ∨ (∃ h ∈ H, g = c * h) ∨ (∃ h ∈ H, g = c ^ 2 * h) := by
  have hcard : Nat.card (X ⧸ H) = 3 := by rw [← Subgroup.index_eq_card]; exact hH
  have h01 : (QuotientGroup.mk 1 : X ⧸ H) ≠ QuotientGroup.mk c := by
    intro h; apply hc; simpa [QuotientGroup.eq] using h
  have h02 : (QuotientGroup.mk 1 : X ⧸ H) ≠ QuotientGroup.mk (c ^ 2) := by
    intro h; apply hc2; simpa [QuotientGroup.eq] using h
  have h12 : (QuotientGroup.mk c : X ⧸ H) ≠ QuotientGroup.mk (c ^ 2) := by
    intro h; apply hc
    have := QuotientGroup.eq.mp h
    have e : c⁻¹ * c ^ 2 = c := by group
    rwa [e] at this
  rcases eq_or_eq_or_eq_of_card_eq_three hcard h01 h02 h12 (QuotientGroup.mk g) with h | h | h
  · exact Or.inl ⟨g, by simpa [QuotientGroup.eq] using h, rfl⟩
  · exact Or.inr (Or.inl ⟨c⁻¹ * g, QuotientGroup.eq.mp h.symm, by group⟩)
  · exact Or.inr (Or.inr ⟨(c ^ 2)⁻¹ * g, QuotientGroup.eq.mp h.symm, by group⟩)

theorem mem_normalCore_of_index_three {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : H.index = 3) {c : X} (hc : c ∉ H) (hc2 : c ^ 2 ∉ H) {r : X} (h0 : r ∈ H)
    (h1 : c⁻¹ * r * c ∈ H) (h2 : (c ^ 2)⁻¹ * r * c ^ 2 ∈ H) : r ∈ H.normalCore := by
  rw [mem_normalCore_iff]
  intro g
  have hg : g * r * g⁻¹ = (g⁻¹)⁻¹ * r * g⁻¹ := by rw [inv_inv]
  rw [hg]
  rcases exists_mul_of_index_three hH hc hc2 g⁻¹ with ⟨h, hh, e⟩ | ⟨h, hh, e⟩ | ⟨h, hh, e⟩
  · rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) h0) hh
  · rw [e]
    have : (c * h)⁻¹ * r * (c * h) = h⁻¹ * (c⁻¹ * r * c) * h := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) h1) hh
  · rw [e]
    have : (c ^ 2 * h)⁻¹ * r * (c ^ 2 * h) = h⁻¹ * ((c ^ 2)⁻¹ * r * c ^ 2) * h := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) h2) hh

theorem pow_three_mem_normalCore {X : Type*} [Group X] [Finite X] {H : Subgroup X}
    (hH : H.index = 3) {y : X}
    (hy : y ∈ Subgroup.closure {x : X | ∃ k : ℕ, orderOf x = 3 ^ k}) :
    y ^ 3 ∈ H.normalCore := by
  classical
  have := Fintype.ofFinite (X ⧸ H)
  have hcard : Nat.card (X ⧸ H) = 3 := by rw [← Subgroup.index_eq_card]; exact hH
  have : Nontrivial (X ⧸ H) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]; norm_num
  let φ : X →* Equiv.Perm (X ⧸ H) := MulAction.toPermHom X (X ⧸ H)
  let ε : X →* ℤˣ := Equiv.Perm.sign.comp φ
  have hgen : Subgroup.closure {x : X | ∃ k : ℕ, orderOf x = 3 ^ k} ≤ ε.ker := by
    rw [Subgroup.closure_le]
    rintro x ⟨k, hk⟩
    show ε x = 1
    have h1 : ε x ^ (3 ^ k) = 1 := by rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    have h2 : ε x ^ 2 = 1 := Int.units_sq _
    exact (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_right k (by norm_num))).mp ⟨h2, h1⟩
  have hmem : φ y ∈ alternatingGroup (X ⧸ H) := Equiv.Perm.mem_alternatingGroup.mpr (hgen hy)
  have hA : Nat.card (alternatingGroup (X ⧸ H)) = 3 := by
    rw [nat_card_alternatingGroup, hcard]; decide
  have h3 : (φ y) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := alternatingGroup (X ⧸ H)) (x := ⟨φ y, hmem⟩)
    rw [hA] at this
    exact congrArg Subtype.val this
  rw [Subgroup.normalCore_eq_ker]
  exact MonoidHom.mem_ker.mpr (by rw [map_pow]; exact h3)

end Coset

section Residual

variable {G : Type*} [Group G]

theorem oPrimeResidualOf_le_self (p : ℕ) (P : Subgroup G) : oPrimeResidualOf p P ≤ P := by
  unfold oPrimeResidualOf
  exact (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem mem_oPrimeResidualOf_of_orderOf {p : ℕ} {P : Subgroup G} {x : G} (hx : x ∈ P) {k : ℕ}
    (hk : orderOf x = p ^ k) : x ∈ oPrimeResidualOf p P :=
  Subgroup.subset_closure ⟨hx, k, hk⟩

theorem conj_mem_oPrimeResidualOf {p : ℕ} {P : Subgroup G} {g : G} (hg : g ∈ P) {q : G}
    (hq : q ∈ oPrimeResidualOf p P) : g * q * g⁻¹ ∈ oPrimeResidualOf p P := by
  unfold oPrimeResidualOf at hq ⊢
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨P.mul_mem (P.mul_mem hg hx.1) (P.inv_mem hg), ?_⟩
    obtain ⟨k, hk⟩ := hx.2
    refine ⟨k, ?_⟩
    rw [← hk]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ha

theorem le_normalizer_oPrimeResidualOf [Finite G] (p : ℕ) (P : Subgroup G) :
    P ≤ Subgroup.normalizer (oPrimeResidualOf p P : Set G) :=
  fun _ hg => Subgroup.mem_normalizer_fintype fun _ hn => conj_mem_oPrimeResidualOf hg hn

theorem oPrimeResidualOf_eq_map (p : ℕ) (P : Subgroup G) :
    oPrimeResidualOf p P =
      (Subgroup.closure {x : ↥P | ∃ k : ℕ, orderOf x = p ^ k}).map P.subtype := by
  unfold oPrimeResidualOf
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hx⟩, ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, ⟨k, hk⟩, rfl⟩
    exact ⟨hy, k, by simpa using hk⟩

end Residual

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_le_of_isPGroup {P E U : Subgroup G} (hEP : E ≤ P) (hE3 : IsPGroup 3 ↥E)
    (hEsyl : ¬ 3 ∣ (E.subgroupOf P).index) (hUP : U ≤ P) (hU3 : IsPGroup 3 ↥U) :
    ∃ g ∈ P, ∀ u ∈ U, g⁻¹ * u * g ∈ E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3' : IsPGroup 3 ↥(E.subgroupOf P) :=
    hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEP).symm
  have hU3' : IsPGroup 3 ↥(U.subgroupOf P) :=
    hU3.of_equiv (Subgroup.subgroupOfEquivOfLe hUP).symm
  let S₀ : Sylow 3 ↥P := hE3'.toSylow hEsyl
  obtain ⟨S, hS⟩ := hU3'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P S₀ S
  refine ⟨g, g.2, fun u hu => ?_⟩
  have hu' : (⟨u, hUP hu⟩ : ↥P) ∈ (S : Subgroup ↥P) :=
    hS (Subgroup.mem_subgroupOf.mpr hu)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hu'
  obtain ⟨s, hs, hsu⟩ := hu'
  have hs' : (s : G) ∈ E := Subgroup.mem_subgroupOf.mp hs
  have hsu' : (g : G) * s * (g : G)⁻¹ = u := congrArg Subtype.val hsu
  have : (g : G)⁻¹ * u * g = s := by rw [← hsu']; group
  rw [this]
  exact hs'

end Sylow

section PCore

variable {G : Type*} [Group G]

theorem inf_le_pCoreOf_of_le_normalizer {K Q : Subgroup G} (hK2 : IsPGroup 2 ↥K)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) : K ⊓ Q ≤ pCoreOf 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun _q hq => Subgroup.inf_normalizer_le_normalizer_inf ⟨hQK hq, Subgroup.le_normalizer hq⟩)
    (hK2.to_le inf_le_left)

theorem map_conj_eq_of_mem_normalizer {N : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mpr (by simpa [mul_assoc] using hy)
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem commutator_mem_pCoreOf {K Q : Subgroup G} (hK2 : IsPGroup 2 ↥K)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    {r f : G} (hr : r ∈ K) (hf : f ∈ Q) : ⁅r, f⁆ ∈ pCoreOf 2 Q := by
  have h1 : ⁅r, f⁆ ∈ K := by
    have e : ⁅r, f⁆ = r * (f * r⁻¹ * f⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem hr ((Subgroup.mem_normalizer_iff.mp (hQK hf) r⁻¹).mp (K.inv_mem hr))
  have h2 : ⁅r, f⁆ ∈ Q := by
    have e : ⁅r, f⁆ = (r * f * r⁻¹) * f⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKQ hr) f).mp hf) (Q.inv_mem hf)
  exact inf_le_pCoreOf_of_le_normalizer hK2 hQK ⟨h1, h2⟩

theorem four_lt_card_commutator [Finite G] {K Q : Subgroup G} (hK2 : IsPGroup 2 ↥K)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    {f : G} (hf : f ∈ Q) {r : Fin 5 → G} (hr : ∀ i, r i ∈ K)
    (hinj : Function.Injective fun i => ⁅⁅r i, f⁆, f⁆) :
    4 < Nat.card ↥⁅pCoreOf 2 Q, Subgroup.zpowers f⁆ := by
  let F : Fin 5 → ↥⁅pCoreOf 2 Q, Subgroup.zpowers f⁆ := fun i =>
    ⟨⁅⁅r i, f⁆, f⁆, Subgroup.commutator_mem_commutator
      (commutator_mem_pCoreOf hK2 hQK hKQ (hr i) hf) (Subgroup.mem_zpowers f)⟩
  have hF : Function.Injective F := fun i j h => hinj (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

theorem card_commutator_conj {Q : Subgroup G} {g f x : G}
    (hg : g ∈ Subgroup.normalizer (pCoreOf 2 Q : Set G))
    (hx : Subgroup.zpowers x = (Subgroup.zpowers f).map (MulAut.conj g).toMonoidHom) :
    Nat.card ↥⁅pCoreOf 2 Q, Subgroup.zpowers x⁆ = Nat.card ↥⁅pCoreOf 2 Q, Subgroup.zpowers f⁆ := by
  have h1 : ⁅pCoreOf 2 Q, Subgroup.zpowers x⁆ =
      (⁅pCoreOf 2 Q, Subgroup.zpowers f⁆).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hg, hx]
  rw [h1]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

end PCore

section General

variable {G : Type} [Group G] [Finite G]

theorem charTwo_gen {P K E : Subgroup G}
    (hKP : K ≤ P) (hKn : P ≤ Subgroup.normalizer (K : Set G)) (hK2 : IsPGroup 2 ↥K)
    (hord : ∀ x ∈ P, ∃ i j : ℕ, orderOf x = 2 ^ i * 3 ^ j)
    (hEP : E ≤ P) (hE3 : IsPGroup 3 ↥E) (hEsyl : ¬ 3 ∣ (E.subgroupOf P).index)
    (hdat : ∀ e ∈ E, e ≠ 1 → ∃ f : G, Subgroup.zpowers f = Subgroup.zpowers e ∧
      ∃ r : Fin 5 → G, (∀ i, r i ∈ K) ∧ Function.Injective fun i => ⁅⁅r i, f⁆, f⁆) :
    CharTwo P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKpc : K ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKP hKn hK2
  set C : Subgroup G := P ⊓ Subgroup.centralizer (pCoreOf 2 P : Set G) with hC
  have hCn : ∀ g ∈ P, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    rintro g hg c ⟨hcP, hcC⟩
    refine ⟨P.mul_mem (P.mul_mem hg hcP) (P.inv_mem hg),
      Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
    have h1 : g⁻¹ * n * g ∈ pCoreOf 2 P := by
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P (P.inv_mem hg)) n).mp hn
      simpa using this
    have h2 : (g⁻¹ * n * g) * c = c * (g⁻¹ * n * g) := Subgroup.mem_centralizer_iff.mp hcC _ h1
    calc n * (g * c * g⁻¹) = g * ((g⁻¹ * n * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by rw [h2]
      _ = g * c * g⁻¹ * n := by group
  have hC2 : IsPGroup 2 ↥C := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨c, hc⟩
    obtain ⟨i, j, hij⟩ := hord c hc.1
    by_cases hj : j = 0
    · exact ⟨i, by rw [Subgroup.orderOf_mk, hij, hj]; simp⟩
    · exfalso
      have h3 : 3 ∣ orderOf c := by
        rw [hij]
        exact Dvd.dvd.mul_left (dvd_pow_self 3 hj) _
      have hne0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
      have hc'3 : orderOf (c ^ (orderOf c / 3)) = 3 := orderOf_pow_orderOf_div hne0 h3
      have hc'C : c ^ (orderOf c / 3) ∈ C := C.pow_mem hc _
      have hU3 : IsPGroup 3 ↥(Subgroup.zpowers (c ^ (orderOf c / 3))) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc'3]; norm_num)
      obtain ⟨g, hgP, hg⟩ := exists_conj_le_of_isPGroup hEP hE3 hEsyl
        (Subgroup.zpowers_le.mpr hc'C.1) hU3
      have heE : g⁻¹ * c ^ (orderOf c / 3) * g ∈ E := hg _ (Subgroup.mem_zpowers _)
      have heC : g⁻¹ * c ^ (orderOf c / 3) * g ∈ C := by
        have := hCn g⁻¹ (P.inv_mem hgP) _ hc'C
        simpa using this
      have hne : g⁻¹ * c ^ (orderOf c / 3) * g ≠ 1 := by
        intro h
        have h' : c ^ (orderOf c / 3) = 1 := by
          have e : c ^ (orderOf c / 3) = g * (g⁻¹ * c ^ (orderOf c / 3) * g) * g⁻¹ := by group
          rw [e, h]
          group
        rw [h', orderOf_one] at hc'3
        omega
      obtain ⟨f, hf, r, hrK, hinj⟩ := hdat _ heE hne
      have hfC : f ∈ C := Subgroup.zpowers_le.mpr heC (hf ▸ Subgroup.mem_zpowers f)
      have hcomm : ∀ i, ⁅r i, f⁆ = 1 := fun i => by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_centralizer_iff.mp hfC.2 (r i) (hKpc (hrK i))
      have h01 : (0 : Fin 5) = 1 := @hinj 0 1 (by simp [hcomm])
      exact absurd h01 (by decide)
  have hPC : P ≤ Subgroup.normalizer (C : Set G) :=
    fun g hg => Subgroup.mem_normalizer_fintype fun n hn => hCn g hg n hn
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hPC hC2

theorem four_lt_card_gen {P K E : Subgroup G}
    (hKP : K ≤ P) (hKn : P ≤ Subgroup.normalizer (K : Set G)) (hK2 : IsPGroup 2 ↥K)
    (hEP : E ≤ P) (hE3 : IsPGroup 3 ↥E) (hEsyl : ¬ 3 ∣ (E.subgroupOf P).index)
    (hdat : ∀ e ∈ E, e ≠ 1 → ∃ f : G, Subgroup.zpowers f = Subgroup.zpowers e ∧
      ∃ r : Fin 5 → G, (∀ i, r i ∈ K) ∧ Function.Injective fun i => ⁅⁅r i, f⁆, f⁆)
    {x : G} (hxQ : x ∈ oPrimeResidualOf 3 P) (hx3 : orderOf x = 3) :
    4 < Nat.card ↥⁅pCoreOf 2 (oPrimeResidualOf 3 P), Subgroup.zpowers x⁆ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQP : oPrimeResidualOf 3 P ≤ P := oPrimeResidualOf_le_self 3 P
  have hPQ : P ≤ Subgroup.normalizer (oPrimeResidualOf 3 P : Set G) :=
    le_normalizer_oPrimeResidualOf 3 P
  have hU3 : IsPGroup 3 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3]; norm_num)
  obtain ⟨g, hgP, hg⟩ := exists_conj_le_of_isPGroup hEP hE3 hEsyl
    (Subgroup.zpowers_le.mpr (hQP hxQ)) hU3
  have heE : g⁻¹ * x * g ∈ E := hg x (Subgroup.mem_zpowers x)
  have hne : g⁻¹ * x * g ≠ 1 := by
    intro h
    have hx1 : x = 1 := by
      have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [e, h]
      group
    rw [hx1, orderOf_one] at hx3
    omega
  obtain ⟨f, hf, r, hrK, hinj⟩ := hdat _ heE hne
  have hfE : f ∈ E := Subgroup.zpowers_le.mpr heE (hf ▸ Subgroup.mem_zpowers f)
  have hfQ : f ∈ oPrimeResidualOf 3 P := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hE3 ⟨f, hfE⟩
    exact mem_oPrimeResidualOf_of_orderOf (hEP hfE) (k := k) (by rwa [Subgroup.orderOf_mk] at hk)
  have h4 := four_lt_card_commutator hK2 (hQP.trans hKn) (hKP.trans hPQ) hfQ hrK hinj
  have hgN : g ∈ Subgroup.normalizer (pCoreOf 2 (oPrimeResidualOf 3 P) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hPQ hgP)
  have hxz : Subgroup.zpowers x = (Subgroup.zpowers f).map (MulAut.conj g).toMonoidHom := by
    rw [hf, MonoidHom.map_zpowers]
    congr 1
    show x = g * (g⁻¹ * x * g) * g⁻¹
    group
  rw [card_commutator_conj hgN hxz]
  exact h4

end General

section Index

variable {G : Type*} [Group G]

@[expose] def normalCoreIn (B P : Subgroup G) : Subgroup G :=
  (B.subgroupOf P).normalCore.map P.subtype

theorem mem_normalCoreIn_iff {B P : Subgroup G} {k : G} :
    k ∈ normalCoreIn B P ↔ k ∈ P ∧ ∀ g ∈ P, g * k * g⁻¹ ∈ B := by
  unfold normalCoreIn
  constructor
  · rintro ⟨k₀, hk₀, rfl⟩
    exact ⟨k₀.2, fun g hg => hk₀ ⟨g, hg⟩⟩
  · rintro ⟨hk, h⟩
    exact ⟨⟨k, hk⟩, fun b => h b b.2, rfl⟩

theorem normalCoreIn_le {B P : Subgroup G} : normalCoreIn B P ≤ B := fun _ hk => by
  simpa using (mem_normalCoreIn_iff.mp hk).2 1 P.one_mem

theorem normalCoreIn_le_right {B P : Subgroup G} : normalCoreIn B P ≤ P :=
  fun _ hk => (mem_normalCoreIn_iff.mp hk).1

theorem conj_mem_normalCoreIn {B P : Subgroup G} {g : G} (hg : g ∈ P) {k : G}
    (hk : k ∈ normalCoreIn B P) : g * k * g⁻¹ ∈ normalCoreIn B P := by
  obtain ⟨hkP, hk⟩ := mem_normalCoreIn_iff.mp hk
  refine mem_normalCoreIn_iff.mpr ⟨P.mul_mem (P.mul_mem hg hkP) (P.inv_mem hg), fun h hh => ?_⟩
  have := hk (h * g) (P.mul_mem hh hg)
  simpa [mul_assoc] using this

theorem not_mem_of_orderOf_eq_three {B : Subgroup G} (hB2 : IsPGroup 2 ↥B) {x : G}
    (hx : orderOf x = 3) : x ∉ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hxB
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hB2 ⟨x, hxB⟩
  rw [Subgroup.orderOf_mk, hx] at hk
  have h3 : (3 : ℕ) ∣ 2 ^ k := by rw [← hk]
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem index_subgroupOf_eq_three [Finite G] {B P : Subgroup G} (hBP : B ≤ P)
    (hcard : Nat.card ↥P = 3 * Nat.card ↥B) : (B.subgroupOf P).index = 3 := by
  have h1 := Subgroup.card_mul_index (B.subgroupOf P)
  have h2 : Nat.card ↥(B.subgroupOf P) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
  rw [h2, hcard, mul_comm 3] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem index_subgroupOf_zpowers [Finite G] {P : Subgroup G} {a : ℕ}
    (hcard : Nat.card ↥P = 3 * 2 ^ a) {x : G} (hx : x ∈ P) (hx3 : orderOf x = 3) :
    ((Subgroup.zpowers x).subgroupOf P).index = 2 ^ a := by
  have h1 := Subgroup.card_mul_index ((Subgroup.zpowers x).subgroupOf P)
  have h2 : Nat.card ↥((Subgroup.zpowers x).subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hx)).toEquiv,
      Nat.card_zpowers, hx3]
  rw [h2, hcard] at h1
  omega

theorem mem_normalCoreIn_of_index_three [Finite G] {B P : Subgroup G} (hBP : B ≤ P)
    (hcard : Nat.card ↥P = 3 * Nat.card ↥B) {x : G} (hxP : x ∈ P) (hx3 : orderOf x = 3)
    (hxB : x ∉ B) {r : G} (h0 : r ∈ B) (h1 : x⁻¹ * r * x ∈ B) (h2 : x * r * x⁻¹ ∈ B) :
    r ∈ normalCoreIn B P := by
  have hidx := index_subgroupOf_eq_three hBP hcard
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hxinv : x ^ 2 = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx3')
  have hc : (⟨x, hxP⟩ : ↥P) ∉ B.subgroupOf P := fun h => hxB (Subgroup.mem_subgroupOf.mp h)
  have hc2 : (⟨x, hxP⟩ : ↥P) ^ 2 ∉ B.subgroupOf P := by
    intro h
    apply hxB
    have h' : x ^ 2 ∈ B := Subgroup.mem_subgroupOf.mp h
    rw [hxinv] at h'
    simpa using B.inv_mem h'
  have hcore := mem_normalCore_of_index_three (X := ↥P) hidx hc hc2
    (r := ⟨r, hBP h0⟩) (Subgroup.mem_subgroupOf.mpr h0)
    (Subgroup.mem_subgroupOf.mpr (by simpa using h1))
    (Subgroup.mem_subgroupOf.mpr (by simpa [hxinv] using h2))
  exact Subgroup.mem_map.mpr ⟨_, hcore, rfl⟩

theorem pow_three_mem_normalCoreIn [Finite G] {B P : Subgroup G} (hBP : B ≤ P)
    (hcard : Nat.card ↥P = 3 * Nat.card ↥B) {y : G} (hy : y ∈ oPrimeResidualOf 3 P) :
    y ^ 3 ∈ normalCoreIn B P := by
  rw [oPrimeResidualOf_eq_map] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  exact Subgroup.mem_map.mpr
    ⟨y' ^ 3, pow_three_mem_normalCore (index_subgroupOf_eq_three hBP hcard) hy',
      map_pow P.subtype y' 3⟩

theorem zpowers_eq_of_mem_of_ne_one [Finite G] {x e : G} (hx3 : orderOf x = 3)
    (he : e ∈ Subgroup.zpowers x) (hne : e ≠ 1) : Subgroup.zpowers x = Subgroup.zpowers e := by
  have h1 : orderOf e ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers x) he
    rwa [Nat.card_zpowers, hx3] at this
  have h2 : orderOf e = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he) ?_).symm
  rw [Nat.card_zpowers, Nat.card_zpowers, h2, hx3]

theorem sup_eq_of_card_eq_three_mul [Finite G] {B P Q : Subgroup G} (hBP : B ≤ P) (hQP : Q ≤ P)
    (hcard : Nat.card ↥P = 3 * Nat.card ↥B) {x : G} (hxQ : x ∈ Q) (hxB : x ∉ B) : Q ⊔ B = P := by
  have hle : Q ⊔ B ≤ P := sup_le hQP hBP
  have hd1 : Nat.card ↥B ∣ Nat.card ↥(Q ⊔ B) := Subgroup.card_dvd_of_le le_sup_right
  have hd2 : Nat.card ↥(Q ⊔ B) ∣ 3 * Nat.card ↥B := hcard ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨m, hm⟩ := hd1
  have hm3 : m ∣ 3 := by
    rw [hm, mul_comm 3] at hd2
    exact (Nat.mul_dvd_mul_iff_left Nat.card_pos).mp hd2
  rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with rfl | rfl
  · exfalso
    have heq : B = Q ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hm, mul_one])
    exact hxB (heq ▸ Subgroup.mem_sup_left hxQ)
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hm, mul_comm])

end Index

end CoreP

open CoreP

theorem core_gen {G : Type} [Group G] [Finite G] {P K E : Subgroup G}
    (hKP : K ≤ P) (hKn : P ≤ Subgroup.normalizer (K : Set G)) (hK2 : IsPGroup 2 ↥K)
    (hord : ∀ x ∈ P, ∃ i j : ℕ, orderOf x = 2 ^ i * 3 ^ j)
    (hEP : E ≤ P) (hE3 : IsPGroup 3 ↥E) (hEsyl : ¬ 3 ∣ (E.subgroupOf P).index)
    (hN1 : ∀ y ∈ oPrimeResidualOf 3 P, ∃ m : ℕ, y ^ 3 ^ m ∈ K)
    (hdat : ∀ e ∈ E, e ≠ 1 → ∃ f : G, Subgroup.zpowers f = Subgroup.zpowers e ∧
      ∃ r : Fin 5 → G, (∀ i, r i ∈ K) ∧ Function.Injective fun i => ⁅⁅r i, f⁆, f⁆) :
    CharTwo P ∧
      (∀ y ∈ oPrimeResidualOf 3 P, ∃ k : ℕ, y ^ 3 ^ k ∈ pCoreOf 2 (oPrimeResidualOf 3 P)) ∧
      (∀ x ∈ oPrimeResidualOf 3 P, orderOf x = 3 →
        4 < Nat.card ↥⁅pCoreOf 2 (oPrimeResidualOf 3 P), Subgroup.zpowers x⁆) :=
  ⟨charTwo_gen hKP hKn hK2 hord hEP hE3 hEsyl hdat,
    fun y hy => by
      obtain ⟨m, hm⟩ := hN1 y hy
      exact ⟨m, inf_le_pCoreOf_of_le_normalizer hK2 ((oPrimeResidualOf_le_self 3 P).trans hKn)
        ⟨hm, (oPrimeResidualOf 3 P).pow_mem hy _⟩⟩,
    fun _ hx hx3 => four_lt_card_gen hKP hKn hK2 hEP hE3 hEsyl hdat hx hx3⟩

theorem idx3_P {G : Type} [Group G] [Finite G] {B P : Subgroup G}
    (hB2 : IsPGroup 2 ↥B) (hBP : B ≤ P) (hcard : Nat.card ↥P = 3 * Nat.card ↥B)
    (hnN : ¬ P ≤ Subgroup.normalizer (B : Set G))
    {x₀ : G} (hx₀ : x₀ ∈ P) (hx₀3 : orderOf x₀ = 3)
    {r : Fin 5 → G} (hr0 : ∀ i, r i ∈ B) (hr1 : ∀ i, x₀⁻¹ * r i * x₀ ∈ B)
    (hr2 : ∀ i, x₀ * r i * x₀⁻¹ ∈ B)
    (hinj : Function.Injective fun i => ⁅⁅r i, x₀⁆, x₀⁆) :
    CharTwo P ∧ (∀ y ∈ oPrimeResidualOf 3 P, y ^ 3 ∈ pCoreOf 2 (oPrimeResidualOf 3 P)) ∧
      (∀ x ∈ oPrimeResidualOf 3 P, orderOf x = 3 →
        4 < Nat.card ↥⁅pCoreOf 2 (oPrimeResidualOf 3 P), Subgroup.zpowers x⁆) ∧
      oPrimeResidualOf 3 P ⊔ B = P := by
  have _ := hnN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hB2.exists_card_eq
  have hPcard : Nat.card ↥P = 3 * 2 ^ a := by rw [hcard, ha]
  have hx₀B : x₀ ∉ B := not_mem_of_orderOf_eq_three hB2 hx₀3
  have hKn : P ≤ Subgroup.normalizer (normalCoreIn B P : Set G) :=
    fun g hg => Subgroup.mem_normalizer_fintype fun k hk => conj_mem_normalCoreIn hg hk
  have hK2 : IsPGroup 2 ↥(normalCoreIn B P) := hB2.to_le normalCoreIn_le
  have hrK : ∀ i, r i ∈ normalCoreIn B P := fun i =>
    mem_normalCoreIn_of_index_three hBP hcard hx₀ hx₀3 hx₀B (hr0 i) (hr1 i) (hr2 i)
  have hord : ∀ x ∈ P, ∃ i j : ℕ, orderOf x = 2 ^ i * 3 ^ j := fun x hx =>
    exists_two_pow_mul_three_pow_of_dvd (hPcard ▸ Subgroup.orderOf_dvd_natCard P hx)
  have hE3 : IsPGroup 3 ↥(Subgroup.zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀3]; norm_num)
  have hEsyl : ¬ 3 ∣ ((Subgroup.zpowers x₀).subgroupOf P).index := by
    rw [index_subgroupOf_zpowers hPcard hx₀ hx₀3]
    exact not_three_dvd_two_pow a
  have hN1 : ∀ y ∈ oPrimeResidualOf 3 P, ∃ m : ℕ, y ^ 3 ^ m ∈ normalCoreIn B P := fun y hy =>
    ⟨1, by simpa using pow_three_mem_normalCoreIn hBP hcard hy⟩
  have hdat : ∀ e ∈ Subgroup.zpowers x₀, e ≠ 1 → ∃ f : G,
      Subgroup.zpowers f = Subgroup.zpowers e ∧ ∃ r : Fin 5 → G,
        (∀ i, r i ∈ normalCoreIn B P) ∧ Function.Injective fun i => ⁅⁅r i, f⁆, f⁆ :=
    fun e he hne => ⟨x₀, zpowers_eq_of_mem_of_ne_one hx₀3 he hne, r, hrK, hinj⟩
  obtain ⟨hchar, -, h3⟩ := core_gen normalCoreIn_le_right hKn hK2 hord (Subgroup.zpowers_le.mpr hx₀)
    hE3 hEsyl hN1 hdat
  refine ⟨hchar, fun y hy => ?_, h3, ?_⟩
  · exact inf_le_pCoreOf_of_le_normalizer hK2 ((oPrimeResidualOf_le_self 3 P).trans hKn)
      ⟨pow_three_mem_normalCoreIn hBP hcard hy, (oPrimeResidualOf 3 P).pow_mem hy 3⟩
  · exact sup_eq_of_card_eq_three_mul hBP (oPrimeResidualOf_le_self 3 P) hcard
      (mem_oPrimeResidualOf_of_orderOf hx₀ (k := 1) (by simpa using hx₀3)) hx₀B

end CFSG.Quasithin.S151S9T
