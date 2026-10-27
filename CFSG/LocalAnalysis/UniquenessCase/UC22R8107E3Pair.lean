module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Loss
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107PairCore
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddNormalizerOrderThreeCentralizes
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem pRank_three_le_three_of_not_sp {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L : Subgroup G} (hL : L ∈ calC D.M) :
    CFSG.Open.pRank 3 D.M ≤ 3 := by
  by_contra h
  exact hnsp (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL)
    (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega)))

theorem five_le_of_mem_sig {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ}
    (hp : p ∈ D.sig) : 5 ≤ p := by
  have h3σ : 3 ∉ D.sig := fun h =>
    hnsp (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) h)
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have h2 := hpp.two_le
  have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hpp
  omega

theorem exists_pair_of_fixed {M K L : Subgroup G} (hK : K ∈ calC M) (hL : L ∈ calC M)
    (hKL : K ≠ L)
    (hKN : ∀ H : Subgroup G, H ≤ M → Odd (Nat.card H) → H ≤ normalizer (K : Set G))
    (hLN : ∀ H : Subgroup G, H ≤ M → Odd (Nat.card H) → H ≤ normalizer (L : Set G)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G} (hQM : Q ≤ M) (hQ : IsPGroup p Q) {b₁ : G}
    (hb₁K : b₁ ∈ K) (hb₁ : orderOf b₁ = 3)
    (hb₁Q : ∀ u ∈ Q, b₁⁻¹ * (u * b₁ * u⁻¹) ∈ pCoreOf 2 K) {b₂ : G} (hb₂L : b₂ ∈ L)
    (hb₂ : orderOf b₂ = 3) (hb₂Q : ∀ u ∈ Q, b₂⁻¹ * (u * b₂ * u⁻¹) ∈ pCoreOf 2 L) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ ∃ a₁ ∈ K ⊓ R, ∃ a₂ ∈ L ⊓ R,
      orderOf a₁ = 3 ∧ orderOf a₂ = 3 ∧ a₁ ∈ centralizer (Q : Set G) ∧
        a₂ ∈ centralizer (Q : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQodd : Odd (Nat.card Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hLC := P2251c.le_centralizerMod_of_ne hK hL hKL
  obtain ⟨a₂, ha₂L, ha₂, ha₂Q, -⟩ := P2251c.exists_orderOf_three (P₂ := ⊥) hp2 hQ
    IsPGroup.of_bot bot_le (hLN Q hQM hQodd) bot_le hb₂L hb₂ hb₂Q
    fun u hu => by rw [mem_bot.1 hu]; simp
  have hz₂ : IsPGroup 3 (zpowers a₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha₂, pow_one])
  have hz₂K : zpowers a₂ ≤ normalizer (K : Set G) :=
    hKN _ (zpowers_le.2 (hL.1.le ha₂L)) (by rw [Nat.card_zpowers, ha₂]; decide)
  obtain ⟨a₁, ha₁K, ha₁, ha₁Q, ha₁₂⟩ := P2251c.exists_orderOf_three (P₂ := zpowers a₂) hp2 hQ hz₂
    (zpowers_le.2 ha₂Q) (hKN Q hQM hQodd) hz₂K hb₁K hb₁ hb₁Q fun v hv =>
    P2251c.inv_mul_conj_mem_of_mem_centralizerMod (hLC (zpowers_le.2 ha₂L hv)) hb₁K
  have hz₁ : IsPGroup 3 (zpowers a₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha₁, pow_one])
  have hE : IsPGroup 3 (zpowers a₁ ⊔ zpowers a₂ : Subgroup G) :=
    hz₁.to_sup_of_normal_right' hz₂ (zpowers_le.2 (centralizer_le_normalizer _ ha₁₂))
  have hEM : zpowers a₁ ⊔ zpowers a₂ ≤ M :=
    sup_le (zpowers_le.2 (hK.1.le ha₁K)) (zpowers_le.2 (hL.1.le ha₂L))
  obtain ⟨R, hR, hER⟩ : ∃ R, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ zpowers a₁ ⊔ zpowers a₂ ≤ R := by
    obtain ⟨S, hS⟩ := (hE.comap_subtype (K := M)).exists_le_sylow
    exact ⟨_, ⟨S, rfl⟩, fun y hy => ⟨⟨y, hEM hy⟩, hS (by exact hy), rfl⟩⟩
  exact ⟨R, hR, a₁, mem_inf.2 ⟨ha₁K, hER (mem_sup_left (mem_zpowers a₁))⟩, a₂,
    mem_inf.2 ⟨ha₂L, hER (mem_sup_right (mem_zpowers a₂))⟩, ha₁, ha₂, ha₁Q, ha₂Q⟩

private theorem exists_orderOf_three_centralizer_of_not_dvd {L : Subgroup G}
    (r : CFSG.Open.pRank 3 L = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : IsPGroup p P) (hPN : P ≤ normalizer (L : Set G)) (hpL : ¬ p ∣ Nat.card (Bar2 L)) :
    ∃ b ∈ L, orderOf b = 3 ∧ b ∈ centralizer (P : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpL' : ¬ p ∣ Nat.card L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h2
    · exact hpL h1
    · exact P2251c.not_dvd_card_of_isPGroup_two
        (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L) 2) hp hp2 h2
  obtain ⟨S, hS⟩ :=
    CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp Nat.prime_three hP hPN hpL'
  have hTL : (S : Subgroup L).map L.subtype ≤ L := map_subtype_le _
  have hTc : IsCyclic ((S : Subgroup L).map L.subtype) :=
    R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one r hTL (S.isPGroup'.map L.subtype)
  have h3S : 3 ∣ Nat.card (S : Subgroup L) := by
    rw [Sylow.card_eq_multiplicity]
    exact dvd_pow_self 3 (Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne'
      (R8107Odd.three_dvd_card_of_pRank_eq_one r)).ne'
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S : Subgroup L)) 3 h3S
  have hso : orderOf ((s : L) : G) = 3 := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hs]
  have hFT : zpowers ((s : L) : G) ≤ (S : Subgroup L).map L.subtype :=
    zpowers_le.2 (mem_map_of_mem L.subtype s.2)
  have hPC := GorensteinWalter.odd_subgroup_le_centralizer_of_le_normalizer_card_three P _
    (by obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP; rw [hn]; exact (hp.odd_of_ne_two hp2).pow)
    (by rw [Nat.card_zpowers, hso])
    (hS.trans (GorensteinWalter.normalizer_le_normalizer_of_le_cyclic hTc hFT))
  exact ⟨(s : L), (s : L).2, hso, mem_centralizer_iff.2 fun u hu =>
    (mem_centralizer_iff.1 (hPC hu) _ (mem_zpowers _)).symm⟩

private theorem false_of_pair_rank_two {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) (hnsp : ¬ IsStronglyPEmbedded 3 D.M)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hp : p ∈ D.sig) {R E A : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R D.M) (hEZ : E ≤ R ⊓ centralizer (R : Set G))
    (hEel : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2)
    (hA : A ≤ D.M ⊓ centralizer (E : Set G)) (hAel : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) : False := by
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have h3σ : 3 ∉ D.sig := fun h => hnsp (UC6S846.sp_of_mem_sig hSg hns h)
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hΓ := h76 p hp hp2 (UC6S846.sp_of_mem_sig hSg hns hp) 3 Nat.prime_three E
    (hEZ.trans (inf_le_left.trans hR.le)) hEel hEc
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp hA hAel hAc))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp
      (hA.trans (inf_le_inf_left _ ((centralizer_le hXE).trans (centralizer_le_normalizer _))))
      hAel hAc))
  exact hnsp (h614 (UC6S846.sig_subset_sig1 hSg hns) 3 Nat.prime_three (by norm_num) h3σ R hR E
    hEZ hEel hEc hΓ)

theorem dvd_card_bar2_of_loss {D : Data G} (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) (hnsp : ¬ IsStronglyPEmbedded 3 D.M)
    {L₁ L₂ : Subgroup G} (hL₁ : L₁ ∈ calC D.M) (hL₂ : L₂ ∈ calC D.M) (h12 : L₁ ≠ L₂)
    (r₁ : CFSG.Open.pRank 3 L₁ = 1) (r₂ : CFSG.Open.pRank 3 L₂ = 1)
    (hZ₁ : center (Bar2 L₁) = ⊥)
    (hloss₁ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₁) p)
    (hloss₂ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₂) p) {p : ℕ}
    (hp : p ∈ D.sig) : p ∣ Nat.card (Bar2 L₁) ∧ p ∣ Nat.card (Bar2 L₂) := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp5 := five_le_of_mem_sig hSg hnsp hL₁ hp
  have hN₁ : ∀ H : Subgroup G, H ≤ D.M → Odd (Nat.card H) → H ≤ normalizer (L₁ : Set G) :=
    fun _ hHM hH => R8107Odd.le_normalizer_of_odd h82 hnsp hL₁ r₁ hHM hH
  have hN₂ : ∀ H : Subgroup G, H ≤ D.M → Odd (Nat.card H) → H ≤ normalizer (L₂ : Set G) :=
    fun _ hHM hH => R8107Odd.le_normalizer_of_odd h82 hnsp hL₂ r₂ hHM hH
  have hc₁ : ∀ B : Subgroup G, B ≤ L₁ → IsPGroup 3 B → IsCyclic B :=
    fun _ hB hBp => R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one r₁ hB hBp
  have hc₂ : ∀ B : Subgroup G, B ≤ L₂ → IsPGroup 3 B → IsCyclic B :=
    fun _ hB hBp => R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one r₂ hB hBp
  obtain ⟨P, hPM, hP, hPc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hSg.three_le p hp)
  have hPodd : Odd (Nat.card P) := hPc ▸ (hpp.odd_of_ne_two hp2).pow
  have hsq : ∀ Q : Subgroup G, Nat.card P ≤ p * Nat.card Q → p ^ 2 ≤ Nat.card Q := fun Q hQ => by
    refine Nat.le_of_mul_le_mul_left (c := p) ?_ hpp.pos
    calc p * p ^ 2 = Nat.card P := by rw [hPc]; ring
      _ ≤ p * Nat.card Q := hQ
  have hfix : ∀ {b : G}, b ∈ centralizer (P : Set G) → ∀ u ∈ P, b⁻¹ * (u * b * u⁻¹) = 1 :=
    fun hb u hu => by rw [mem_centralizer_iff.1 hb u hu, mul_inv_cancel_right, inv_mul_cancel]
  refine ⟨by_contra fun hpL => ?_, by_contra fun hpL => ?_⟩
  · obtain ⟨b₁, hb₁L, hb₁, hb₁P⟩ :=
      exists_orderOf_three_centralizer_of_not_dvd r₁ hpp hp2 hP.isPGroup (hN₁ P hPM hPodd) hpL
    obtain ⟨Q, hQP, hQc, b₂, hb₂L, hb₂, hb₂Q⟩ :=
      R8107Pair.exists_fixed_of_lossAt (hloss₂ p hpp hp5) (hN₂ P hPM hPodd) hP
    obtain ⟨R, E, A, hR, hEZ, hEel, hEc, hA, hAel, hAc⟩ :=
      R8107Pair.exists_elemAbelian_of_fixed_pair hL₁ hL₂ h12 hN₁ hN₂ hZ₁ hc₁ hc₂ hpp hp2
        (hQP.trans hPM) (hP.mono hQP) (hsq Q hQc) hb₁L hb₁
        (fun u hu => by rw [hfix hb₁P u (hQP hu)]; exact one_mem _) hb₂L hb₂ hb₂Q
    exact false_of_pair_rank_two hSg h76 h614 hnsp hL₁ hp hR hEZ hEel hEc hA hAel hAc
  · obtain ⟨b₂, hb₂L, hb₂, hb₂P⟩ :=
      exists_orderOf_three_centralizer_of_not_dvd r₂ hpp hp2 hP.isPGroup (hN₂ P hPM hPodd) hpL
    obtain ⟨Q, hQP, hQc, b₁, hb₁L, hb₁, hb₁Q⟩ :=
      R8107Pair.exists_fixed_of_lossAt (hloss₁ p hpp hp5) (hN₁ P hPM hPodd) hP
    obtain ⟨R, E, A, hR, hEZ, hEel, hEc, hA, hAel, hAc⟩ :=
      R8107Pair.exists_elemAbelian_of_fixed_pair hL₁ hL₂ h12 hN₁ hN₂ hZ₁ hc₁ hc₂ hpp hp2
        (hQP.trans hPM) (hP.mono hQP) (hsq Q hQc) hb₁L hb₁ hb₁Q hb₂L hb₂
        (fun u hu => by rw [hfix hb₂P u (hQP hu)]; exact one_mem _)
    exact false_of_pair_rank_two hSg h76 h614 hnsp hL₁ hp hR hEZ hEel hEc hA hAel hAc

theorem exists_pair_mem_sig {D : Data G} (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L₁ L₂ : Subgroup G} (hL₁ : L₁ ∈ calC D.M)
    (hL₂ : L₂ ∈ calC D.M) (h12 : L₁ ≠ L₂) (r₁ : CFSG.Open.pRank 3 L₁ = 1)
    (r₂ : CFSG.Open.pRank 3 L₂ = 1)
    (hloss₁ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₁) p)
    (hloss₂ : ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L₂) p) {p : ℕ}
    (hp : p ∈ D.sig) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R D.M ∧ ∃ a₁ ∈ L₁ ⊓ R, ∃ a₂ ∈ L₂ ⊓ R,
      orderOf a₁ = 3 ∧ orderOf a₂ = 3 ∧
        ∃ y ∈ D.M, orderOf y = p ∧ y * a₁ = a₁ * y ∧ y * a₂ = a₂ * y := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp5 := five_le_of_mem_sig hSg hnsp hL₁ hp
  have hN₁ : ∀ H : Subgroup G, H ≤ D.M → Odd (Nat.card H) → H ≤ normalizer (L₁ : Set G) :=
    fun _ hHM hH => R8107Odd.le_normalizer_of_odd h82 hnsp hL₁ r₁ hHM hH
  have hN₂ : ∀ H : Subgroup G, H ≤ D.M → Odd (Nat.card H) → H ≤ normalizer (L₂ : Set G) :=
    fun _ hHM hH => R8107Odd.le_normalizer_of_odd h82 hnsp hL₂ r₂ hHM hH
  obtain ⟨P, hPM, hP, hPc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hSg.three_le p hp)
  have hodd : ∀ Q ≤ P, Odd (Nat.card Q) := fun Q hQ =>
    Odd.of_dvd_nat (hPc ▸ (hpp.odd_of_ne_two hp2).pow) (Subgroup.card_dvd_of_le hQ)
  obtain ⟨Q₁, hQ₁P, hQ₁c, b₁, hb₁L, hb₁, hb₁Q⟩ :=
    R8107Pair.exists_fixed_of_lossAt (hloss₁ p hpp hp5) (hN₁ P hPM (hodd P le_rfl)) hP
  obtain ⟨Q₂, hQ₂Q₁, hQ₂c, b₂, hb₂L, hb₂, hb₂Q⟩ := R8107Pair.exists_fixed_of_lossAt
    (hloss₂ p hpp hp5) (hN₂ Q₁ (hQ₁P.trans hPM) (hodd Q₁ hQ₁P)) (hP.mono hQ₁P)
  have hQ₂P : Q₂ ≤ P := hQ₂Q₁.trans hQ₁P
  have hQ₂p : IsPGroup p Q₂ := (hP.mono hQ₂P).isPGroup
  obtain ⟨R, hR, a₁, ha₁, a₂, ha₂, ho₁, ho₂, ha₁Q, ha₂Q⟩ := exists_pair_of_fixed hL₁ hL₂ h12 hN₁
    hN₂ hpp hp2 (hQ₂P.trans hPM) hQ₂p hb₁L hb₁ (fun u hu => hb₁Q u (hQ₂Q₁ hu)) hb₂L hb₂ hb₂Q
  have hpQ : p ∣ Nat.card Q₂ := hQ₂p.card_eq_or_dvd.resolve_left fun h1 => by
    have h2 : p * (p * p) ≤ p * (p * 1) :=
      calc p * (p * p) = Nat.card P := by rw [hPc]; ring
        _ ≤ p * Nat.card Q₁ := hQ₁c
        _ ≤ p * (p * Nat.card Q₂) := Nat.mul_le_mul_left _ hQ₂c
        _ = p * (p * 1) := by rw [h1]
    have := Nat.le_of_mul_le_mul_left (Nat.le_of_mul_le_mul_left h2 hpp.pos) hpp.pos
    have := hpp.two_le
    omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q₂) p hpQ
  exact ⟨R, hR, a₁, ha₁, a₂, ha₂, ho₁, ho₂, y, hQ₂P.trans hPM y.2,
    by rw [Subgroup.orderOf_coe, hy], mem_centralizer_iff.1 ha₁Q y y.2,
    mem_centralizer_iff.1 ha₂Q y y.2⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3

end
