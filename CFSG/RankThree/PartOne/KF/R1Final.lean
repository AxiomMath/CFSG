module

public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartOne.KF.Reduction123
public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.SymCtxQuot
public import CFSG.RankThree.PartOne.KF.ToralQuot

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem Table123Generic.maximal [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Generic p L A₀ F) :
    ∀ F' : Subgroup G, F' ≤ L → (∀ x ∈ F', x ^ p = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → F ≤ F' → F' = F :=
  h.toCore.maximal

theorem Table123Generic.F_exp [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Generic p L A₀ F) : ∀ f ∈ F, f ^ p = 1 := h.toCore.F_exp

theorem Table123Generic.F_comm [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Generic p L A₀ F) : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := h.toCore.F_comm

theorem exists_r1frame [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 1) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      Nat.card K = 2 ^ f ∧ (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧ CharP K 2 ∧
      ∃ ε : ↥L →* StatedProj (StatedSL 3 K), IsCentralPQuot p ε ∧
        (∀ t ∈ (torusSU p 3 K).subgroupOf (StatedSL 3 K), ∃ x : F,
          ε (Subgroup.inclusion h.F_le x) = QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf
            (StatedSL 3 K)) t) ∧
        ∀ x : F, ∃ t ∈ (torusSU p 3 K).subgroupOf (StatedSL 3 K),
          ε (Subgroup.inclusion h.F_le x) = QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf
            (StatedSL 3 K)) t := by
  classical
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
  have hp := h.prime
  have h5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
    have hdvd : p ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hpq
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨z, ?_⟩
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  obtain ⟨ζ, hζ'⟩ := hζ
  let q := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))
  have hq := isCentralPQuot_statedSL (K := K) hp h5
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
  have hε₀ := isCentralPQuot_center e hcop
  have hTexp : ∀ t ∈ (torusSU p 3 K).subgroupOf (StatedSL 3 K), t ^ p = 1 := by
    intro t ht
    obtain ⟨d, hd1, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hd, diagU_pow, show d ^ p = 1 from funext hd1, diagU_one]
    rfl
  have hTcomm : ∀ s ∈ (torusSU p 3 K).subgroupOf (StatedSL 3 K),
      ∀ t ∈ (torusSU p 3 K).subgroupOf (StatedSL 3 K), s * t = t * s := by
    intro s hs t ht
    obtain ⟨d, -, -, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp hs)
    obtain ⟨d', -, -, hd'⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp ht)
    apply Subtype.ext
    show (s : GL (Fin 3) K) * t = t * s
    rw [← hd, ← hd', diagU_mul, diagU_mul, mul_comm]
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot q hq _ hε₀ hTexp hTcomm
    (fun X hexp hcomm => exists_conj_torus_statedSL hp ⟨ζ, hζ'⟩ X hexp hcomm) h.F_le h.F_exp
    h.F_comm h.maximal
  exact ⟨f, K, hKf, hKfin, hf1, hpq, hK, ⟨ζ, hζ'⟩, hchar, ε, hε, hFT₁, hFT₂⟩

theorem exists_r1ctx [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (SymCtx p 3 K L F) := by
  classical
  obtain ⟨f, K, hKf, hKfin, hf1, hpq, hK, ⟨ζ, hζ'⟩, -, ε, hε, hFT₁, hFT₂⟩ := exists_r1frame h hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hdist : ∀ i j : Fin 3, i ≠ j → ∃ x ∈ torusSU p 3 K, ent x i i ≠ ent x j j := fun i j hij =>
    torusSU_char_distinct hζ'.pow_eq_one
      (hζ'.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)) hij
  obtain ⟨SM⟩ := SymCtx.ofMatrixGroup (p := p) (StatedSL 3 K) torusSU_le_statedSL
    (fun σ => permGL_mem_statedSL σ) hdist
  let q := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))
  have hq := isCentralPQuot_statedSL (K := K) hp h5
  exact ⟨K, hKf, hKfin, ⟨ζ, hζ'⟩, SymCtx.ofCentralQuot SM q hq ε hε h.F_le h.F_exp hFT₁ hFT₂⟩

theorem perm_three_pow_prime_eq_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (π : Equiv.Perm (Fin 3)) (hπ : π ^ p = 1) : π = 1 := by
  have h1 : orderOf π ∣ p := orderOf_dvd_of_pow_eq_one hπ
  have h2 : orderOf π ∣ 6 := by
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    rw [← h6]
    exact orderOf_dvd_natCard π
  have hcop : Nat.Coprime p 6 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
    have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases p <;> first | omega | (norm_num at hp)
  have h3 : orderOf π ∣ Nat.gcd p 6 := Nat.dvd_gcd h1 h2
  rw [hcop] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem kf123Row1 : KF123Row 1 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r1ctx h.toCore hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hp3 : ¬ p ∣ 3 := fun hd => by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  exact ⟨hmodel, S.card_F (m := 2) rfl hp.pos hζ, ⟨S.weylEquiv hp hp2 hζ⟩,
    S.torusImage_eq_closure hp hp2 hζ,
    fun _ B hBF hB => S.torusIrreducible hp (by norm_num) hp3 B hBF hB,
    fun h11 => absurd h11 (by norm_num)⟩

theorem kf123NTRow1 : KF123NTRow 1 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r1ctx h.toCore hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hpowF : ∀ a : F, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection hp hp2 (by norm_num)
    (fun π hπ => perm_three_pow_prime_eq_one hp h5 π hπ) hζ
    (fun α hα _ => perm_three_aut_inner α hα) hpowF hyL hyF

end CFSG.RankThree.PartOne
