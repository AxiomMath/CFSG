module

public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace F6

open scoped MatrixGroups in
@[expose] def DicksonPSL2 : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime], 1 ≤ f → ∀ H : Subgroup PSL(2, GaloisField p f),
    (CFSG.Open.IsElemAbelian p H ∧ ∃ m : ℕ, m ≤ f ∧ Nat.card H = p ^ m) ∨
    (IsCyclic H ∧ (Nat.card H ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      Nat.card H ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1))) ∨
    (∃ z : ℕ, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    (16 ∣ p ^ (2 * f) - 1 ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ (m t : ℕ) (P : Subgroup H) (_ : P.Normal), CFSG.Open.IsElemAbelian p P ∧
      Nat.card P = p ^ m ∧ IsCyclic (H ⧸ P) ∧ Nat.card (H ⧸ P) = t ∧ t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∨
    (∃ m : ℕ, m ∣ f ∧ Nonempty (H ≃* PSL(2, GaloisField p m))) ∨
    (∃ m : ℕ, 2 * m ∣ f ∧ Nonempty (H ≃* PGL(2, GaloisField p m)))

@[expose] def L2DicksonFacts : Prop :=
  ∀ (p e : ℕ) (K : Type) [Field K] [Finite K], p.Prime → p ≠ 2 → 1 ≤ e →
    Nat.card K = p ^ e → ∀ H : Subgroup (StatedProj (StatedSL 2 K)),
      (Nonempty (↥H ≃* DihedralGroup 6) → (p ^ e % 12 = 1 ∨ p ^ e % 12 = 11)) ∧
      (Nonempty (↥H ≃* DihedralGroup 12) → (p ^ e % 24 = 1 ∨ p ^ e % 24 = 23)) ∧
      ¬ Nonempty (↥H ≃* Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) ×
        Multiplicative (ZMod 2)))

theorem alternating_four_center : ∀ σ : Equiv.Perm (Fin 4),
    (Equiv.Perm.sign σ = 1 ∧ (∀ ρ : Equiv.Perm (Fin 4), Equiv.Perm.sign ρ = 1 → σ * ρ = ρ * σ)) →
      σ = 1 := by
  decide +kernel

theorem perm_four_center : ∀ σ : Equiv.Perm (Fin 4),
    (∀ ρ : Equiv.Perm (Fin 4), σ * ρ = ρ * σ) → σ = 1 := by
  decide +kernel

theorem alternating_four_noncomm : ¬ ∀ σ ρ : Equiv.Perm (Fin 4),
    (Equiv.Perm.sign σ = 1 ∧ Equiv.Perm.sign ρ = 1) → σ * ρ = ρ * σ := by
  decide +kernel

theorem dihedral_six_facts :
    (∀ g : DihedralGroup 6, DihedralGroup.r 3 * g = g * DihedralGroup.r 3) ∧
    DihedralGroup.r (3 : ZMod 6) ≠ 1 ∧
    DihedralGroup.r (1 : ZMod 6) * DihedralGroup.sr 0 ≠ DihedralGroup.sr 0 * DihedralGroup.r 1 := by
  decide +kernel

theorem dihedral_twelve_facts :
    (∀ g : DihedralGroup 12, DihedralGroup.r 6 * g = g * DihedralGroup.r 6) ∧
    DihedralGroup.r (6 : ZMod 12) ≠ 1 ∧
    DihedralGroup.r (1 : ZMod 12) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1 := by
  decide +kernel

theorem z3_e4_pow_six : ∀ x : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) ×
    Multiplicative (ZMod 2)), x ^ 6 = 1 := by
  decide +kernel

theorem center_eq_bot_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hez : e z ∈ Subgroup.center H := Subgroup.mem_center_iff.mpr fun h => by
    obtain ⟨g, rfl⟩ := e.surjective h
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
  rw [hH, Subgroup.mem_bot] at hez
  rw [Subgroup.mem_bot]
  exact e.injective (hez.trans (map_one e).symm)

theorem center_alternating_four : Subgroup.center ↥(alternatingGroup (Fin 4)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  refine Subtype.ext (alternating_four_center z.1 ⟨Equiv.Perm.mem_alternatingGroup.mp z.2,
    fun ρ hρ => ?_⟩)
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz
    ⟨ρ, Equiv.Perm.mem_alternatingGroup.mpr hρ⟩).symm

theorem center_perm_four : Subgroup.center (Equiv.Perm (Fin 4)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  exact perm_four_center z fun ρ => (Subgroup.mem_center_iff.mp hz ρ).symm

theorem eq_zero_of_kind_seven {p m t N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hN : N = 12 ∨ N = 24)
    (hNt : N = t * p ^ m) (ht : t ∣ p ^ m - 1) : m = 0 := by
  by_contra hm
  have hpN : p ∣ N := hNt ▸ Dvd.dvd.mul_left (dvd_pow_self p hm) t
  have hN24 : N ∣ 2 ^ 3 * 3 := by rcases hN with rfl | rfl <;> norm_num
  have hp24 : p ∣ 2 ^ 3 * 3 := hpN.trans hN24
  have hp3 : p = 3 := by
    rcases (Nat.Prime.dvd_mul hp).mp hp24 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow h)) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
  subst hp3
  have hm1 : m = 1 := by
    by_contra hm1
    have h9 : 3 ^ 2 ∣ N := hNt ▸ Dvd.dvd.mul_left (pow_dvd_pow 3 (by omega)) t
    rcases hN with rfl | rfl <;> norm_num at h9
  subst hm1
  have := Nat.le_of_dvd (by norm_num) ht
  rcases hN with rfl | rfl <;> omega

open scoped MatrixGroups in
theorem dihedral_of_dickson (hD : DicksonPSL2) {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {H : Subgroup PSL(2, GaloisField p f)}
    (hcard : Nat.card H = 12 ∨ Nat.card H = 24) (hcyc : ¬ IsCyclic ↥H)
    (hZ : Subgroup.center ↥H ≠ ⊥) :
    ∃ z : ℕ, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨
      z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧ Nonempty (↥H ≃* DihedralGroup z) := by
  rcases hD p f hf H with ⟨-, m, -, hm⟩ | ⟨hc, -⟩ | h3 | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, P, hPn, -, hPc, hQc, hQt, ht, -⟩ | ⟨m, -, ⟨e⟩⟩ | ⟨m, -, ⟨e⟩⟩
  · exfalso
    have h2 : 2 ∣ p ^ m := hm ▸ (by rcases hcard with h | h <;> rw [h] <;> norm_num)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  · exact absurd hc hcyc
  · exact h3
  · exact absurd (center_eq_bot_of_mulEquiv' e center_alternating_four) hZ
  · exact absurd (center_eq_bot_of_mulEquiv' e center_perm_four) hZ
  · exfalso
    have h60 : Nat.card ↥H = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.card_eq_fintype_card, Nat.factorial]
    omega
  · exfalso
    have hHt : Nat.card ↥H = t * p ^ m := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup P, hQt, hPc]
    have hm0 := eq_zero_of_kind_seven hp.out hp2 (hHt ▸ hcard) rfl ht
    subst hm0
    have hPbot : P = ⊥ := Subgroup.card_eq_one.mp (by rw [hPc, pow_zero])
    subst hPbot
    exact hcyc (isCyclic_of_surjective (QuotientGroup.quotientBot.toMonoidHom)
      QuotientGroup.quotientBot.surjective)
  · exact absurd (center_eq_bot_of_mulEquiv' e
      (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField p m))) hZ
  · exact absurd (center_eq_bot_of_mulEquiv' e
      (CFSG.GorensteinWalter.pgl2_center_eq_bot (GaloisField p m))) hZ

theorem eq_of_mulEquiv_dihedral {z n : ℕ} (e : DihedralGroup z ≃* DihedralGroup n) :
    z = n := by
  have h := Nat.card_congr e.toEquiv
  rw [DihedralGroup.nat_card, DihedralGroup.nat_card] at h
  omega

theorem dvd_of_dihedral_le (hD : DicksonPSL2) {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {H : Subgroup PSL(2, GaloisField p f)} {n : ℕ} (hn : n = 6 ∨ n = 12)
    (φ : ↥H ≃* DihedralGroup n) :
    n ∣ (p ^ f + 1) / 2 ∨ n ∣ (p ^ f - 1) / 2 := by
  have hodd : Odd (p ^ f) := (hp.out.eq_two_or_odd'.resolve_left hp2).pow
  have hgcd : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (Dvd.intro k rfl)
  obtain ⟨⟨r6, hr6, hr6ne⟩, hnc⟩ : (∃ g : DihedralGroup n, (∀ x : DihedralGroup n, g * x = x * g) ∧
      g ≠ 1) ∧ DihedralGroup.r (1 : ZMod n) * DihedralGroup.sr 0 ≠
        DihedralGroup.sr 0 * DihedralGroup.r 1 := by
    rcases hn with rfl | rfl
    · exact ⟨⟨_, dihedral_six_facts.1, dihedral_six_facts.2.1⟩, dihedral_six_facts.2.2⟩
    · exact ⟨⟨_, dihedral_twelve_facts.1, dihedral_twelve_facts.2.1⟩,
        dihedral_twelve_facts.2.2⟩
  have hcard : Nat.card ↥H = 12 ∨ Nat.card ↥H = 24 := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
    rcases hn with rfl | rfl <;> norm_num
  have hcyc : ¬ IsCyclic ↥H := by
    intro hc
    have : IsCyclic (DihedralGroup n) := isCyclic_of_surjective φ.toMonoidHom φ.surjective
    exact hnc (IsCyclic.isMulCommutative.is_comm.comm _ _)
  have hZ : Subgroup.center ↥H ≠ ⊥ := by
    intro hbot
    have := center_eq_bot_of_mulEquiv' φ.symm hbot
    have hmem : r6 ∈ Subgroup.center (DihedralGroup n) :=
      Subgroup.mem_center_iff.mpr fun x => (hr6 x).symm
    rw [this, Subgroup.mem_bot] at hmem
    exact hr6ne hmem
  obtain ⟨z, hz, ⟨ψ⟩⟩ := dihedral_of_dickson hD hp2 hf hcard hcyc hZ
  have hzn := eq_of_mulEquiv_dihedral (ψ.symm.trans φ)
  rw [hgcd, hzn] at hz
  exact hz

theorem l2DicksonFacts_of_dickson (hD : DicksonPSL2) : L2DicksonFacts := by
  intro p e K _ _ hp hp2 he hK H
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField p e) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (GaloisField p e) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card p e (by omega)]
  let ε : StatedProj (StatedSL 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField p e) :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2)
        (FiniteField.ringEquivOfCardEq hcardK))
  let H' := H.map ε.toMonoidHom
  let ι : ↥H ≃* ↥H' := H.equivMapOfInjective ε.toMonoidHom ε.injective
  have hodd : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  refine ⟨fun ⟨φ⟩ => ?_, fun ⟨φ⟩ => ?_, fun ⟨φ⟩ => ?_⟩
  · rcases dvd_of_dihedral_le hD hp2 he (Or.inl rfl) (ι.symm.trans φ) with ⟨c, hc⟩ | ⟨c, hc⟩
    · obtain ⟨k, hk⟩ := hodd
      right
      omega
    · obtain ⟨k, hk⟩ := hodd
      left
      omega
  · rcases dvd_of_dihedral_le hD hp2 he (Or.inr rfl) (ι.symm.trans φ) with ⟨c, hc⟩ | ⟨c, hc⟩
    · obtain ⟨k, hk⟩ := hodd
      right
      omega
    · obtain ⟨k, hk⟩ := hodd
      left
      omega
  ·
    have φ' : ↥H' ≃* Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) ×
        Multiplicative (ZMod 2)) := ι.symm.trans φ
    have hcard : Nat.card ↥H' = 12 ∨ Nat.card ↥H' = 24 := by
      left
      rw [Nat.card_congr φ'.toEquiv]
      simp
    have hcyc : ¬ IsCyclic ↥H' := by
      intro hc
      have : IsCyclic (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) ×
          Multiplicative (ZMod 2))) := isCyclic_of_surjective φ'.toMonoidHom φ'.surjective
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
        (α := Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
      have h6 := orderOf_dvd_of_pow_eq_one (z3_e4_pow_six g)
      rw [hg] at h6
      simp at h6
    have hZ : Subgroup.center ↥H' ≠ ⊥ := by
      intro hbot
      have hc := center_eq_bot_of_mulEquiv' φ'.symm hbot
      have htop : Subgroup.center (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) ×
          Multiplicative (ZMod 2))) = ⊤ := Subgroup.center_eq_top
      rw [htop] at hc
      have : (Multiplicative.ofAdd (1 : ZMod 3), (1 : Multiplicative (ZMod 2)),
          (1 : Multiplicative (ZMod 2))) ∈ (⊥ : Subgroup _) := hc ▸ Subgroup.mem_top _
      rw [Subgroup.mem_bot] at this
      exact absurd this (by decide)
    obtain ⟨z, -, ⟨ψ⟩⟩ := dihedral_of_dickson hD hp2 he hcard hcyc hZ
    have hz : z = 6 := by
      have h := Nat.card_congr (ψ.symm.trans φ').toEquiv
      rw [DihedralGroup.nat_card] at h
      simp at h
      omega
    subst hz
    apply dihedral_six_facts.2.2
    apply (ψ.symm.trans φ').injective
    rw [map_mul, map_mul, mul_comm]

end F6

end CFSG.Quasithin
