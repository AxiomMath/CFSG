module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDTransport
public import CFSG.LocalAnalysis.StandardType.GGInvolutionRankOneRepresentative
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
public import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem qtwoDL1_transfer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs L : Subgroup G}
    (hBs : IsElemAbelian p Bs) {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {r₀ : MulAut ↥Bs} (hr₀C : r₀ ∈ ggCoxRefl M e) (h6 : Nat.card ↥(ggRankOne Bs r₀) = 6)
    {X : Subgroup G} (hXN : Bs ≤ Subgroup.normalizer (X : Set G))
    {r : MulAut ↥Bs} (hrX : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) :
    ggRankOne Bs r = ggRankOneIn X Bs r ∧ Nat.card ↥(ggRankOne Bs r) = 6 := by
  have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  obtain ⟨a, haA, hra⟩ :=
    ggCoxRefl_conj_of_connected e (ggSimplyLacedConnected_of_weyl hpres.1 h3) hr₀C hrC
  obtain ⟨g, -, -, hg, -⟩ := ggRankOne_conj_of_mem_ggAutomizerJoin haA r₀
  have hcard : Nat.card ↥(ggRankOne Bs r) = 6 := by
    rw [hra, ← hg, Subgroup.card_map_of_injective (MulAut.conj g).injective, h6]
  have hle : ggRankOneIn X Bs r ≤ ggRankOne Bs r := LinFusion.ggOTwoPrime_mono inf_le_right
  obtain ⟨n, hnS, -, ⟨k, hk⟩, hnact⟩ := exists_two_representative_mem_ggRankOneIn hrX hrefl.1
  have hmove : ∃ b : ↥Bs, r b ≠ b := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hfix := hrefl.2
    have hcard1 : Nat.card {b : ↥Bs // r b = b} = Nat.card ↥Bs :=
      Nat.card_congr ⟨fun b => b.1, fun b => ⟨b, hall b⟩, fun _ => rfl, fun _ => rfl⟩
    rw [hcard1] at hfix
    have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
    have : p = 1 := by
      have h' : Nat.card ↥Bs * p = Nat.card ↥Bs * 1 := by rw [hfix, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hpos h'
    exact hp.one_lt.ne' this
  obtain ⟨b, hb⟩ := hmove
  have hBsC : Bs ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhBs : h ∈ Bs := (Subgroup.map_subtype_le _) hh
    exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨h, hhBs⟩ ⟨c, hc⟩)
  have hbN : (b : G) ∈ Subgroup.normalizer (ggRankOneIn X Bs r : Set G) := by
    apply ggMem_normalizer_oTwoPrime
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hXN b.2, Subgroup.le_normalizer (hBsC b.2)⟩
  have hz : (b : G) * n * (b : G)⁻¹ * n⁻¹ ∈ ggRankOneIn X Bs r := by
    have h1 : (b : G) * n * (b : G)⁻¹ ∈ ggRankOneIn X Bs r :=
      (Subgroup.mem_normalizer_iff.mp hbN n).mp hnS
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hnS)
  have hzeq : (b : G) * n * (b : G)⁻¹ * n⁻¹ = ((b * (r b)⁻¹ : ↥Bs) : G) := by
    have h1 : ((r b⁻¹ : ↥Bs) : G) = n * (b : G)⁻¹ * n⁻¹ := by
      rw [hnact (b⁻¹)]; simp
    rw [map_inv] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
    rw [h1]; group
  set z : ↥Bs := b * (r b)⁻¹ with hzdef
  have hz1 : z ≠ 1 := by
    intro h; apply hb; rw [hzdef, mul_inv_eq_one] at h; exact h.symm
  have hzp : orderOf (z : G) = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    exact orderOf_eq_prime (hBs.2 z z.2) hz1'
  have hpdvd : p ∣ Nat.card ↥(ggRankOneIn X Bs r) := by
    rw [← hzp]; exact Subgroup.orderOf_dvd_natCard _ (hzeq ▸ hz)
  have hn1 : n ≠ 1 := by
    intro h1; apply hb; apply Subtype.ext; rw [hnact b, h1]; group
  have h2dvd : 2 ∣ Nat.card ↥(ggRankOneIn X Bs r) := by
    have hord : orderOf n ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hj0 : j ≠ 0 := by
      intro h0; rw [h0, pow_zero] at hj'; exact hn1 (orderOf_eq_one_iff.mp hj')
    have h2n : 2 ∣ orderOf n := by rw [hj']; exact dvd_pow_self 2 hj0
    exact h2n.trans (Subgroup.orderOf_dvd_natCard _ hnS)
  have hdvd6 : Nat.card ↥(ggRankOneIn X Bs r) ∣ 6 := hcard ▸ Subgroup.card_dvd_of_le hle
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h2p : 2 * p ∣ Nat.card ↥(ggRankOneIn X Bs r) := hcop.mul_dvd_of_dvd_of_dvd h2dvd hpdvd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hcard' : Nat.card ↥(ggRankOneIn X Bs r) = 6 := by
    have hc6 : Nat.card ↥(ggRankOneIn X Bs r) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    have hcpos : 0 < Nat.card ↥(ggRankOneIn X Bs r) := Nat.card_pos
    have h2p' := Nat.le_of_dvd hcpos h2p
    omega
  exact ⟨(Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcard'])).symm, hcard⟩

end CFSG.StandardType.QTwo

end
