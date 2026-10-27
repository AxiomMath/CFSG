module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

private lemma qTwoPTB_mem_ggHyperplane_iff {G : Type} [Group G] {Bs : Subgroup G}
    {r : MulAut ↥Bs} {h : G} :
    h ∈ ggHyperplane Bs r ↔ ∃ b : ↥Bs, r b = b ∧ (b : G) = h := by
  rw [ggHyperplane, Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

private lemma qTwoPTB_ggHyperplane_le {G : Type} [Group G] {Bs : Subgroup G}
    (r : MulAut ↥Bs) : ggHyperplane Bs r ≤ Bs := by
  intro h hh
  rw [qTwoPTB_mem_ggHyperplane_iff] at hh
  obtain ⟨b, -, rfl⟩ := hh
  exact b.2

private lemma qTwoPTB_odd_pow_involution {G : Type} [Group G] {r : G} (hr : r ^ 2 = 1)
    {k : ℕ} (hk : Odd k) : r ^ k = r := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_succ, pow_mul, hr, one_pow, one_mul]

private lemma qTwoPTB_conj_pow_apply {G : Type} [Group G] {Bs : Subgroup G}
    {r : MulAut ↥Bs} {n : G}
    (hnr : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) (k : ℕ) (b : ↥Bs) :
    (((r ^ k) b : ↥Bs) : G) = n ^ k * (b : G) * (n ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', MulAut.mul_apply, hnr ((r ^ k) b), ih]
    group

theorem p_dvd_card_mulAut_rankOne {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer L Bs) (hrefl : GGIsReflection p r) :
    p ∣ Nat.card (MulAut ↥(ggRankOneIn L Bs r)) := by
  classical
  obtain ⟨hp, hBsE, -, -⟩ := ggConfig_bstar_facts hcfg.1.1
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
  have hHle : ggHyperplane Bs r ≤ Bs := qTwoPTB_ggHyperplane_le r
  have hBsC : Bs ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hBsE.1.is_comm.comm (⟨h, hHle hh⟩ : ↥Bs) ⟨b, hb⟩)
  obtain ⟨n, hnL, hnN, hnr⟩ := mem_ggAutomizer_iff.mp hr
  have hnC : n ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨b, hrb, rfl⟩ := qTwoPTB_mem_ggHyperplane_iff.mp hh
    have h1 := hnr b
    rw [hrb] at h1
    have hcomm : (b : G) * n = n * (b : G) := by
      nth_rw 1 [h1]
      group
    exact hcomm
  have hBsE' : Bs ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) : Subgroup G) : Set G) := by
    intro b hb
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hBsL hb, Subgroup.le_normalizer (hBsC hb)⟩
  have hBS : Bs ≤ Subgroup.normalizer ((ggRankOneIn L Bs r : Subgroup G) : Set G) := by
    intro b hb
    rw [ggRankOneIn]
    exact ggMem_normalizer_oTwoPrime (hBsE' hb)
  obtain ⟨a, k, hk_odd, hord⟩ :=
    Nat.exists_eq_two_pow_mul_odd (ne_of_gt (orderOf_pos n))
  let u : G := n ^ k
  have hu2 : u ^ (2 ^ a) = 1 := by
    dsimp only [u]
    rw [← pow_mul, mul_comm k (2 ^ a), ← hord, pow_orderOf_eq_one]
  have huL : u ∈ L := by
    dsimp only [u]
    exact Subgroup.pow_mem (K := L) hnL k
  have huC : u ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    dsimp only [u]
    exact Subgroup.pow_mem (K := Subgroup.centralizer (ggHyperplane Bs r : Set G)) hnC k
  have huE : u ∈ L ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) := ⟨huL, huC⟩
  have huS : u ∈ ggRankOneIn L Bs r := by
    rw [ggRankOneIn, ggOTwoPrime]
    exact Subgroup.subset_closure ⟨huE, ⟨a, hu2⟩⟩
  have hru (b : ↥Bs) : ((r b : ↥Bs) : G) = u * (b : G) * u⁻¹ := by
    have h1 : r ^ k = r := qTwoPTB_odd_pow_involution hrefl.1 hk_odd
    calc ((r b : ↥Bs) : G) = (((r ^ k) b : ↥Bs) : G) := by rw [h1]
      _ = n ^ k * (b : G) * (n ^ k)⁻¹ := qTwoPTB_conj_pow_apply hnr k b
      _ = u * (b : G) * u⁻¹ := by dsimp only [u]
  have hr_ne_one : r ≠ 1 := by
    intro hr1
    have hcard : Nat.card {b : ↥Bs // r b = b} = Nat.card ↥Bs :=
      Nat.card_congr
        { toFun := fun y => y.1
          invFun := fun b => ⟨b, by rw [hr1]; rfl⟩
          left_inv := fun y => Subtype.ext rfl
          right_inv := fun b => rfl }
    have h := hrefl.2
    rw [hcard] at h
    have h' : Nat.card ↥Bs * p = Nat.card ↥Bs * 1 := by rw [Nat.mul_one]; exact h
    have hpos : 0 < Nat.card ↥Bs :=
      Nat.card_pos_iff.mpr ⟨Nonempty.intro (1 : ↥Bs), inferInstance⟩
    have hp1 : p = 1 := Nat.mul_left_cancel hpos h'
    have hpge : 2 ≤ p := hp.two_le
    omega
  obtain ⟨b₀, hb₀⟩ : ∃ b : ↥Bs, r b ≠ b := by
    by_contra h
    push Not at h
    exact hr_ne_one (MulEquiv.ext h)
  have hub : u * (b₀ : G) * u⁻¹ ≠ (b₀ : G) := by
    intro hcon
    apply hb₀
    have h1 := hru b₀
    rw [hcon] at h1
    exact Subtype.ext h1
  have hbS : (b₀ : G) ∈
      Subgroup.normalizer ((ggRankOneIn L Bs r : Subgroup G) : Set G) := hBS b₀.2
  let σ : MulAut ↥(ggRankOneIn L Bs r) :=
    (Subgroup.normalizerMonoidHom (ggRankOneIn L Bs r)) ⟨(b₀ : G), hbS⟩
  have hσu : σ ⟨u, huS⟩ ≠ ⟨u, huS⟩ := by
    intro hcon
    apply hub
    have h1 := congrArg (fun y : ↥(ggRankOneIn L Bs r) => (y : G)) hcon
    dsimp only [σ] at h1
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
    change (b₀ : G) * u * (b₀ : G)⁻¹ = u at h1
    have hcomm : (b₀ : G) * u = u * (b₀ : G) := by
      calc (b₀ : G) * u = ((b₀ : G) * u * (b₀ : G)⁻¹) * (b₀ : G) := by group
        _ = u * (b₀ : G) := by rw [h1]
    calc u * (b₀ : G) * u⁻¹ = (b₀ : G) * u * u⁻¹ := by rw [hcomm]
      _ = (b₀ : G) := by group
  have hσ_ne : σ ≠ 1 := by
    intro h1
    exact hσu (by rw [h1]; rfl)
  have hσp : σ ^ p = 1 := by
    dsimp only [σ]
    have hbp : (b₀ : G) ^ p = 1 := hBsE.2 (b₀ : G) b₀.2
    have hpow1 : (⟨(b₀ : G), hbS⟩ : ↥(Subgroup.normalizer
        ((ggRankOneIn L Bs r : Subgroup G) : Set G))) ^ p = 1 := by
      apply Subtype.ext
      change (b₀ : G) ^ p = (1 : G)
      exact hbp
    rw [← map_pow, hpow1, map_one]
  have horder_dvd : orderOf σ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hσp
  have horder : orderOf σ = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf σ) horder_dvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hσ_ne
    · exact h1
  rw [← horder]
  exact orderOf_dvd_natCard σ

end CFSG.StandardType.QTwo

end
