module

public import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
public import CFSG.Quasithin.Background.B1MoreNineC
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecABasicL0

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def Step3_3_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D X : Subgroup G), Hyp331 G T M L D →
    oTwoUpper X = X → T ≤ Subgroup.normalizer (X : Set G) →
    Nonempty (↥(X ⊔ T) ⧸ CFSG.pCore 2 ↥(X ⊔ T) ≃* Equiv.Perm (Fin 3)) →
    ¬ D ≤ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G) →
    InH T (X ⊔ T ⊔ D) → X ⊔ T ⊔ D ≤ Subgroup.normalizer (conjClosure X D : Set G) →
    X ⊔ T ⊔ D = conjClosure X D ⊔ T ⊔ D →
      (∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
        IsPSL 2 p 1 (↥(conjClosure X D ⊔ T) ⧸ CFSG.pCore 2 ↥(conjClosure X D ⊔ T))) ∧
      (pCoreOf 2 X ≤ pCoreOf 2 (conjClosure X D) ∧
        (∃ _ : ((pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T)).Normal,
          Nonempty (↥(X ⊔ T) ⧸ (pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T) ≃*
            DihedralGroup 6)) ∧
        (D ⊓ Subgroup.normalizer (X : Set G)).relIndex D = 3) ∧
      HasNoncentralTwoChief X 3 ∧
      (¬ HasNoncentralTwoChief X 5 →
        (HasNoncentralTwoChief (conjClosure X D) 1 ∧ ¬ HasNoncentralTwoChief (conjClosure X D) 2 ∧
          (∀ A B : Subgroup G, IsTwoChiefFactor (conjClosure X D) A B →
            ¬ ⁅A, conjClosure X D⁆ ≤ B → 2 ^ 10 ≤ B.relIndex A) ∧
          2 ^ 12 ≤ Nat.card T) ∧
        (frattini ↥(pCoreOf 2 X)).map (pCoreOf 2 X).subtype ≤
          (Subgroup.center ↥(conjClosure X D)).map (conjClosure X D).subtype ∧
        (Subgroup.center ↥(conjClosure X D ⊔ T) ≠ ⊥ → 2 ^ 12 < Nat.card T))

variable {G : Type} [Group G] [Finite G]

namespace Lem3320

theorem relIndex_eq_three_of_iso {H T : Subgroup G} (hT : IsSylowTwoOf T H)
    (e : ↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) : T.relIndex H = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardQ : Nat.card (↥H ⧸ CFSG.pCore 2 ↥H) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H)
  rw [hcardQ] at h1
  obtain ⟨a, ha⟩ := hT.2.1.exists_card_eq
  obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
  have h2 := Subgroup.relIndex_mul_card (H := T) (K := H)
  rw [inf_of_le_left hT.1, ha] at h2
  rw [hb] at h1
  set r := T.relIndex H with hr
  have hodd : ¬ 2 ∣ r := hT.2.2
  have heq : r * 2 ^ a = 3 * 2 ^ (b + 1) := by rw [h2, h1, pow_succ]; ring
  have h3 : 3 ∣ r := by
    have : 3 ∣ r * 2 ^ a := ⟨2 ^ (b + 1), heq⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2)) this)
  have hr3 : r ∣ 3 := by
    have hcop : Nat.Coprime r (2 ^ (b + 1)) :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd).symm
    exact hcop.dvd_of_dvd_mul_right ⟨2 ^ a, heq.symm⟩
  exact Nat.dvd_antisymm hr3 h3

theorem maxOver_eq_of_relIndex_prime {H T : Subgroup G} (hTH : T ≤ H) {p : ℕ} (hp : p.Prime)
    (hidx : T.relIndex H = p) : maxOver H T = {T} := by
  have key : ∀ K : Subgroup G, T ≤ K → K ≤ H → K = T ∨ K = H := by
    intro K hTK hKH
    have h1 := Subgroup.relIndex_mul_relIndex T K H hTK hKH
    rw [hidx] at h1
    rcases (Nat.dvd_prime hp).mp (Dvd.intro _ h1) with h | h
    · left
      exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hTK
    · right
      rw [h] at h1
      have h2 : K.relIndex H = 1 := by
        have hp0 : 0 < p := hp.pos
        have : p * K.relIndex H = p * 1 := by rw [h1, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hp0 this
      exact le_antisymm hKH (Subgroup.relIndex_eq_one.mp h2)
  have hTH' : T < H := by
    refine lt_of_le_of_ne hTH fun heq => ?_
    rw [heq, Subgroup.relIndex_self] at hidx
    exact hp.one_lt.ne hidx
  ext N
  simp only [maxOver, IsMaxSubgroupIn, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hNH, -⟩, hTN⟩
    rcases key N hTN hNH.le with h | h
    · exact h
    · exact absurd h hNH.ne
  · rintro rfl
    refine ⟨⟨hTH', fun K hTK hKH => ?_⟩, le_rfl⟩
    rcases key K hTK.le hKH with h | h
    · exact absurd h hTK.ne'
    · exact h

omit [Finite G] in
theorem conjClosure_sup_eq {X T D : Subgroup G} (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) :
    conjClosure X (T ⊔ D) = conjClosure X D := by
  refine le_antisymm (conjClosure_le fun g hg x hx => ?_)
    (conjClosure_mono le_rfl le_sup_right)
  have hDT' : D ≤ Subgroup.normalizer ((T : Subgroup G) : Set G) := hDT
  obtain ⟨t, ht, d, hd, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hDT').mp hg
  have ht' : d⁻¹ * t * d ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (D.inv_mem hd |> hDT) t).mp ht
    simpa using this
  have hx' : (d⁻¹ * t * d) * x * (d⁻¹ * t * d)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (hTX ht') x).mp hx
  have e : t * d * x * (t * d)⁻¹ = d * ((d⁻¹ * t * d) * x * (d⁻¹ * t * d)⁻¹) * d⁻¹ := by group
  rw [e]
  exact mem_conjClosure hd hx'

end Lem3320

open Lem3320

variable {T M L D : Subgroup G}

theorem stmt3_3_20_of (h10 : Stmt3_3_10) (hS : Step3_3_20) : Stmt3_3_20 := by
  intro G _ _ T M L D X h hX hTX ⟨e⟩ hDR
  have hTsyl : IsSylowTwoOf T (X ⊔ T) :=
    ⟨le_sup_right, h.sylow.1, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow le_sup_right⟩
  have hR : pCoreOf 2 (X ⊔ T) ≠ ⊥ := by
    intro hb
    apply hDR
    rw [hb]
    intro d _
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [SetLike.mem_coe, Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro hz
      have := congrArg (fun w => d⁻¹ * w * d) hz
      simpa [mul_assoc] using this
  have hidx := relIndex_eq_three_of_iso hTsyl e
  have hmax := maxOver_eq_of_relIndex_prime le_sup_right Nat.prime_three hidx
  have hO : pCoreOf 2 (X ⊔ T ⊔ D) ≠ ⊥ :=
    (h10 G T M L D h).1 (X ⊔ T) ⟨le_sup_right, hR⟩ ⟨T, hmax⟩
  have hYeq : conjClosure X (T ⊔ D) = conjClosure X D := conjClosure_sup_eq hTX h.DN
  have hTN : T ⊔ D ≤ Subgroup.normalizer (conjClosure X D : Set G) := by
    rw [← hYeq]
    exact le_normalizer_conjClosure X (T ⊔ D)
  have hXN : X ≤ Subgroup.normalizer (conjClosure X D : Set G) :=
    (le_conjClosure X D).trans Subgroup.le_normalizer
  have hBN : X ⊔ T ⊔ D ≤ Subgroup.normalizer (conjClosure X D : Set G) := by
    rw [sup_assoc]
    exact sup_le hXN hTN
  have hBeq : X ⊔ T ⊔ D = conjClosure X D ⊔ T ⊔ D := by
    refine le_antisymm (sup_le (sup_le ((le_conjClosure X D).trans le_sup_left |>.trans
      le_sup_left) (le_sup_right.trans le_sup_left)) le_sup_right) ?_
    refine sup_le (sup_le ?_ (le_sup_right.trans le_sup_left)) le_sup_right
    refine conjClosure_le fun d hd x hx => ?_
    exact (X ⊔ T ⊔ D).mul_mem ((X ⊔ T ⊔ D).mul_mem (Subgroup.mem_sup_right hd)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx)))
      ((X ⊔ T ⊔ D).inv_mem (Subgroup.mem_sup_right hd))
  have hInH : InH T (X ⊔ T ⊔ D) := ⟨le_sup_right.trans le_sup_left, hO⟩
  exact ⟨⟨hInH, hBN, hBeq⟩, hS G T M L D X h hX hTX ⟨e⟩ hDR hInH hBN hBeq⟩

end CFSG.Quasithin.H13
