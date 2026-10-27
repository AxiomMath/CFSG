module

public import CFSG.Milestones.ASVolI.A3L3.Core
public import CFSG.Milestones.ASVolI.A3L3.Pull

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open scoped Pointwise

theorem burnsideA315y_mem_of_coprime {G : Type} [Group G] {S N : Subgroup G} [Finite ↥S]
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ S ⊔ N)
    (hcop : Nat.Coprime (orderOf x) (Nat.card ↥S)) : x ∈ N := by
  haveI : (N.subgroupOf (S ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hSN
  let f : ↥S →* ↥(S ⊔ N) ⧸ N.subgroupOf (S ⊔ N) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_left)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf (S ⊔ N)) q
    have hy' : y ∈ (S : Set G) * (N : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right S N hSN]
      exact hy
    obtain ⟨s, hs, n, hn, rfl⟩ := hy'
    refine ⟨⟨s, hs⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion le_sup_left ⟨s, hs⟩) :
      ↥(S ⊔ N) ⧸ N.subgroupOf (S ⊔ N)) = QuotientGroup.mk ⟨s * n, hy⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hn
  set q : ↥(S ⊔ N) ⧸ N.subgroupOf (S ⊔ N) := QuotientGroup.mk (⟨x, hx⟩ : ↥(S ⊔ N)) with hq
  have hdvd1 : orderOf q ∣ orderOf x := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf (S ⊔ N))) (⟨x, hx⟩ : ↥(S ⊔ N))
    rwa [Subgroup.orderOf_mk] at h1
  obtain ⟨s, hs⟩ := hf q
  have hdvd2 : orderOf q ∣ Nat.card ↥S := by
    rw [← hs]
    exact (orderOf_map_dvd f s).trans (orderOf_dvd_natCard s)
  have h1 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  rw [orderOf_eq_one_iff, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem burnsideA315y_perm_inf {G : Type} [Group G] [Finite G] {L T B : Subgroup G} [hLn : L.Normal]
    (hT : IsPGroup 2 ↥T) (hBodd : Odd (Nat.card ↥B))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    (B : Set G) * ((T ⊓ L : Subgroup G) : Set G) = ((T ⊓ L : Subgroup G) : Set G) * (B : Set G) := by
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have key : ∀ t' ∈ T, t' ∈ B ⊔ L → t' ∈ L := by
    intro t' ht' hmem
    refine burnsideA315y_mem_of_coprime hBN hmem ?_
    have h1 := hT.orderOf_coprime (Nat.coprime_two_left.2 hBodd) ⟨t', ht'⟩
    rwa [Subgroup.orderOf_mk] at h1
  ext x
  constructor
  · rintro ⟨b, hb, t, ⟨htT, htL⟩, rfl⟩
    have hbt : b * t ∈ (T : Set G) * (B : Set G) := by
      rw [← hperm]
      exact Set.mul_mem_mul hb htT
    obtain ⟨t', ht', b', hb', he⟩ := hbt
    have he' : t' * b' = b * t := he
    have ht'L : t' ∈ L := by
      refine key t' ht' ?_
      have h2 : t' = b * t * b⁻¹ * (b * b'⁻¹) := by
        calc t' = t' * b' * b'⁻¹ := by group
          _ = b * t * b'⁻¹ := by rw [he']
          _ = b * t * b⁻¹ * (b * b'⁻¹) := by group
      rw [h2]
      exact mul_mem (Subgroup.mem_sup_right (hLn.conj_mem t htL b))
        (Subgroup.mem_sup_left (B.mul_mem hb (B.inv_mem hb')))
    exact ⟨t', ⟨ht', ht'L⟩, b', hb', he⟩
  · rintro ⟨t, ⟨htT, htL⟩, b, hb, rfl⟩
    have htb : t * b ∈ (B : Set G) * (T : Set G) := by
      rw [hperm]
      exact Set.mul_mem_mul htT hb
    obtain ⟨b', hb', t', ht', he⟩ := htb
    have he' : b' * t' = t * b := he
    have ht'L : t' ∈ L := by
      refine key t' ht' ?_
      have h2 : t' = b'⁻¹ * b * (b⁻¹ * t * b) := by
        calc t' = b'⁻¹ * (b' * t') := by group
          _ = b'⁻¹ * (t * b) := by rw [he']
          _ = b'⁻¹ * b * (b⁻¹ * t * b) := by group
      rw [h2]
      have h3 : b⁻¹ * t * b⁻¹⁻¹ ∈ L := hLn.conj_mem t htL b⁻¹
      rw [inv_inv] at h3
      exact mul_mem (Subgroup.mem_sup_left (B.mul_mem (B.inv_mem hb') hb))
        (Subgroup.mem_sup_right h3)
    exact ⟨b', hb', t', ⟨ht', ht'L⟩, he⟩

namespace burnsideA315y_Model

variable {F : Type} [Field F] {X : Type} [Group X] (M : burnsideA315y_Model F X)

theorem case3 [Finite F] [Finite X] (hsteps : burnsideA315y_StepsStatement)
    (hcartan : burnsideA315y_CartanStatement) {δ : Bool} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nonempty (↥M.K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
    (hΓscal : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g → ∀ μ : Fˣ,
      (μ : F) = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 →
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ M.Γ)
    (hΓdiag : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g →
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 → ∀ (n : ℕ) (s : Fˣ),
        (s : F) = (ulBlock ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det ^ n →
          burnsideA315y_dgl s ∈ M.Γ)
    (hSK : Nat.card ↥(M.S ⊓ M.K) = 2 ^ (Nat.card ↥M.K).factorization 2)
    (hScard : Nat.card ↥M.S = 2 ^ (Nat.card (CFSG.GorensteinWalter.PGL2 (ZMod p))).factorization 2 *
      Nat.card ↥(M.S ⊓ Subgroup.centralizer (M.K : Set X)))
    {L' : Subgroup X} (hKL : M.K ≤ L') (hL'c : L' ≤ M.c.range)
    (hrel : ¬ p ∣ L'.relIndex M.c.range)
    (hD₀cyc : IsCyclic ↥(M.D₀.map M.c))
    (hD₀card : Nat.card ↥(M.D₀.map M.c) ∣ (if δ then p - 1 else p + 1))
    {U : Subgroup X} (hU : CFSG.Quasithin.A315.IsSylowOf p U L')
    (hUD : M.D₀.map M.c ≤ Subgroup.normalizer (U : Set X))
    {B : Subgroup X} (hBc : B ≤ M.c.range) (hBz : ∀ b ∈ B, b * M.z = M.z * b)
    (hab : IsMulCommutative ↥B) (hodd : Odd (Nat.card ↥B))
    (hperm : (B : Set X) * (M.S : Set X) = (M.S : Set X) * (B : Set X)) :
    ∃ K : Subgroup X, K ≤ L' ∧ CFSG.Quasithin.IsSL2 p ↥K ∧
      B = (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set X)) ∧
      IsCyclic ↥(B ⊓ K) ∧ IsCyclic ↥(B ⊓ Subgroup.centralizer (K : Set X)) ∧
      (∃ H U : Subgroup X, CFSG.Quasithin.A315.IsSylowOf p U L' ∧
        CFSG.Quasithin.A315.IsCartan p U (L' ⊔ B) H ∧ B ⊓ Subgroup.centralizer (K : Set X) ≤ H) ∧
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) ∣ (if δ then p - 1 else p + 1) ∧
      (((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
          ((Nat.card ↥(B ⊓ K) : ℕ) : ℤ) ∣ (p : ℤ) - ε) ∧
        CFSG.Quasithin.A315.InvertedIn (B ⊓ K) (M.S ⊓ K)) ∨
       ((p % 8 = 3 ∨ p % 8 = 5) ∧ Nat.card ↥(B ⊓ K) = 3 ∧
        CFSG.Quasithin.A315.InvertedIn (B ⊓ K) (M.S ⊓ Subgroup.normalizer (B : Set X) ⊓
          Subgroup.centralizer ((B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) : Set X)))) := by
  obtain ⟨hBeq, hcyc1, hlast⟩ :=
    M.steps hsteps hp2 hK hΓscal hΓdiag hBc hBz hab hodd hperm hSK hScard
  have hBM : B ≤ M.Mz := fun b hb =>
    ⟨hBc hb, Subgroup.mem_centralizer_singleton_iff.mpr (hBz b hb)⟩
  have hQD : B ⊓ Subgroup.centralizer (M.K : Set X) ≤ M.D₀.map M.c := by
    rw [← M.Mz_inf_centralizer]
    exact inf_le_inf_right _ hBM
  have hQcard : Nat.card ↥(B ⊓ Subgroup.centralizer (M.K : Set X)) ∣
      (if δ then p - 1 else p + 1) :=
    (Subgroup.card_dvd_of_le hQD).trans hD₀card
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpQ : ¬ p ∣ Nat.card ↥(B ⊓ Subgroup.centralizer (M.K : Set X)) := by
    intro hdvd
    have h1 := hdvd.trans hQcard
    cases δ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      have h2 : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp h1
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one h2)
    | true =>
      simp only [↓reduceIte] at h1
      have := Nat.le_of_dvd (by omega) h1
      omega
  refine ⟨M.K, hKL, hK, hBeq, hcyc1, burnsideA315x_cyclic_of_le hQD hD₀cyc, ?_, hQcard, ?_⟩
  · have hrel' : ¬ p ∣ L'.relIndex (L' ⊔ B) := by
      intro h
      apply hrel
      exact h.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex L' (L' ⊔ B) M.c.range
        le_sup_left (sup_le hL'c hBc)))
    obtain ⟨H, hH, hQH⟩ := hcartan X p hp L' (L' ⊔ B) U
      (B ⊓ Subgroup.centralizer (M.K : Set X)) le_sup_left hU hrel'
      (inf_le_left.trans le_sup_right) (hQD.trans hUD) hpQ
    exact ⟨H, U, hU, hH, hQH⟩
  · rcases hlast with ⟨hε, t, ht, hinv⟩ | ⟨h8, h3, t, ht, hinv⟩
    · exact Or.inl ⟨hε, t, ht, hinv⟩
    · have htC : t ∈ Subgroup.centralizer
          ((B ⊓ Subgroup.centralizer (M.K : Set X) : Subgroup X) : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact M.central c ⟨hBM hc.1, hc.2⟩ t (M.S_le_Mz ht.1)
      exact Or.inr ⟨h8, h3, t, ⟨ht, htC⟩, hinv⟩

end burnsideA315y_Model

theorem burnsideA315y_finish {G P : Type} [Group G] [Group P] [Finite P] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) [L.Normal] (e : ↥L ≃* P)
    {δ : Bool} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hL : CFSG.Quasithin.IsPSLEps3 δ p 1 ↥L)
    {F : Type} [Field F] [Finite F] (M : burnsideA315y_Model F (MulAut P))
    (hfit : burnsideA315y_FittingStatement) (hsteps : burnsideA315y_StepsStatement)
    (hcartan : burnsideA315y_CartanStatement)
    (hSsyl : ∃ R : Subgroup P, CFSG.QuasithinUnique.IsSylowTwoOf R ⊤ ∧
      M.S = R.map (MulAut.conj : P →* MulAut P))
    (hoddc : ∀ φ : MulAut P, Odd (orderOf φ) → φ ∈ M.c.range)
    (hK : Nonempty (↥M.K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
    (hΓscal : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g → ∀ μ : Fˣ,
      (μ : F) = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 →
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ M.Γ)
    (hΓdiag : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g →
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 → ∀ (n : ℕ) (s : Fˣ),
        (s : F) = (ulBlock ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det ^ n →
          burnsideA315y_dgl s ∈ M.Γ)
    (hSK : Nat.card ↥(M.S ⊓ M.K) = 2 ^ (Nat.card ↥M.K).factorization 2)
    (hScard : Nat.card ↥M.S = 2 ^ (Nat.card (CFSG.GorensteinWalter.PGL2 (ZMod p))).factorization 2 *
      Nat.card ↥(M.S ⊓ Subgroup.centralizer (M.K : Set (MulAut P))))
    (hKL : M.K ≤ (MulAut.conj : P →* MulAut P).range)
    (hLc : (MulAut.conj : P →* MulAut P).range ≤ M.c.range)
    (hrel : ¬ p ∣ (MulAut.conj : P →* MulAut P).range.relIndex M.c.range)
    (hD₀cyc : IsCyclic ↥(M.D₀.map M.c))
    (hD₀card : Nat.card ↥(M.D₀.map M.c) ∣ (if δ then p - 1 else p + 1))
    (hU : ∃ U : Subgroup (MulAut P),
      CFSG.Quasithin.A315.IsSylowOf p U (MulAut.conj : P →* MulAut P).range ∧
      M.D₀.map M.c ≤ Subgroup.normalizer (U : Set (MulAut P)))
    (hE : ∀ B' : Subgroup (MulAut P), B' ≤ M.c.range → IsMulCommutative ↥B' →
      Odd (Nat.card ↥B') → ¬ IsPGroup 3 ↥B' →
      (B' : Set (MulAut P)) * (M.S : Set (MulAut P)) =
        (M.S : Set (MulAut P)) * (B' : Set (MulAut P)) → M.DichE B' →
      δ = true ∧ B' ≤ (MulAut.conj : P →* MulAut P).range ∧
        CFSG.Quasithin.IsElemAbelianOfRank p 2 ↥B' ∧
        M.S ≤ Subgroup.normalizer (B' : Set (MulAut P)) ∧ B' ≠ ⊥ ∧
        ∀ C : Subgroup (MulAut P), C ≤ B' → M.S ≤ Subgroup.normalizer (C : Set (MulAut P)) →
          C = ⊥ ∨ C = B')
    (hab : IsMulCommutative ↥B) :
    CFSG.Quasithin.A315Case2 L T B ∨ CFSG.Quasithin.A315Case3 L T B := by
  haveI := h.sqtk.finite
  obtain ⟨R, hR, hRS⟩ := hSsyl
  obtain ⟨e', he'⟩ := burnsideA315y_exists_alpha_sylow e h.sylow hR
  have hαinj := burnsideA315y_alpha_injective L e' (burnsideA315x_centralizer_eq_bot h)
  have hTS : (T ⊓ L).map (burnsideA315y_alpha L e') = M.S := by rw [he', hRS]
  refine burnsideA315y_pullback_of_hyp h e' Fact.out hp2 hL ?_
  rw [burnsideA315y_map_alpha_L, hTS]
  set α := burnsideA315y_alpha L e' with hα
  have hB'c : B.map α ≤ M.c.range := by
    rintro _ ⟨b, hb, rfl⟩
    apply hoddc
    have h1 : orderOf (⟨b, hb⟩ : ↥B) ∣ Nat.card ↥B := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat (Odd.of_dvd_nat h.odd h1) (orderOf_map_dvd α b)
  have hB'ab : IsMulCommutative ↥(B.map α) := by
    refine ⟨⟨?_⟩⟩
    rintro ⟨_, ⟨a, ha, rfl⟩⟩ ⟨_, ⟨b, hb, rfl⟩⟩
    apply Subtype.ext
    show α a * α b = α b * α a
    rw [← map_mul, ← map_mul]
    have := hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg α (congrArg Subtype.val this)
  have hB'odd : Odd (Nat.card ↥(B.map α)) := by
    rw [Subgroup.card_map_of_injective hαinj]
    exact h.odd
  have hB'3 : ¬ IsPGroup 3 ↥(B.map α) := by
    intro h3
    apply h.residual
    apply CFSG.Quasithin.A315.pResidualOf_eq_bot_of_isPGroup
    exact h3.of_equiv (Subgroup.equivMapOfInjective B α hαinj).symm
  have hB'perm : ((B.map α : Subgroup (MulAut P)) : Set (MulAut P)) * (M.S : Set (MulAut P)) =
      (M.S : Set (MulAut P)) * ((B.map α : Subgroup (MulAut P)) : Set (MulAut P)) := by
    rw [← hTS]
    exact burnsideA315x_map_permute α (burnsideA315y_perm_inf h.sylow.2.1 h.odd h.perm)
  rcases M.dichotomy hfit hB'c hB'ab hB'odd hB'3 hB'perm with hz | hE'
  · right
    obtain ⟨U, hU, hUD⟩ := hU
    exact M.case3 hsteps hcartan hp2 hK hΓscal hΓdiag hSK hScard hKL hLc hrel hD₀cyc hD₀card hU
      hUD hB'c hz hB'ab hB'odd hB'perm
  · left
    exact hE _ hB'c hB'ab hB'odd hB'3 hB'perm hE'

end CFSG.ASVolI
