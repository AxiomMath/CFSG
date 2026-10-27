module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpStdSubShape
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpStdSubCoord
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJShape
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpMemberL
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosLocalConj
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRootsWeyl
import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Universal.Spin

theorem stdsub_sum_pair {k p : ℕ} (v : Fin k → ZMod p) (a b : Fin k) (s t : ℤ) :
    ∑ c, v c * (((Pi.single a s - Pi.single b t : Fin k → ℤ) c : ℤ) : ZMod p) =
      v a * s - v b * t := by
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

theorem stdsub_dot_pair {k : ℕ} {ε : Fin k → ℤ} (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (a b : Fin k) : ggDDot ε (Pi.single a (ε a) - Pi.single b (ε b)) = 0 := by
  simp only [ggDDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases hε a with h | h <;> rcases hε b with h' | h' <;> simp [h, h']

theorem ggDk_stdSub_point
    (hKG : GGSecFiveKGPosInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hB : Bs = B) (hss : GGDNoSameSupp e φ) :
    ∃ (a₀ : Fin k) (d₀ : ↥Bs), D = Subgroup.closure {x, (d₀ : G)} ∧ GGDPumpPt e φ a₀ d₀ ∧
      p ∣ Nat.card J ∧ ∀ η : Fin k → ℤ,
        η ∈ ggDMemberRoots e φ J ↔ η ∈ ggDMemberRoots e φ L ∧ η a₀ = 0 := by
  classical
  obtain ⟨t, n, f, ψ, hloc⟩ :=
    ggKGPosRankStmt_holds G p B Bs x L D J 𝒦 hcfg L (Or.inl rfl) hsplit
  obtain ⟨g, hstd⟩ := ggKGPos_exists_stdPos hloc
  obtain ⟨hpJ, T, hT, hTc⟩ := ggDk_jShape hKG hcfg hsplit hpres hle3 hk hM φ hφ hB hss
    (ggKGPosLocalHyp_comp_conj hloc g) hstd
  obtain ⟨⟨hp, hp2, -, -⟩, -, ⟨hBs, -, -⟩, -, -⟩ := hloc
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hcfg.1.1.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨hDB, -, hDcard, hxD, -, hJ, hDJ⟩ := hcfg.1.1.2.2.1
  obtain ⟨hcard, ε, hε, hΦL, xb, rfl, hfx⟩ :=
    ggDk_memberRoots_L hKG hcfg hsplit hpres hle3 hk hM φ hφ hss
  obtain ⟨θ, hθ⟩ := ggDk_exists_coord_fix hp hp2 hBs hk hcard hpres.2 φ hφ
  rw [← hB] at hDB hDJ
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hxε : ∀ a b, (ε a : ZMod p) * θ (Additive.ofMul xb) a =
      (ε b : ZMod p) * θ (Additive.ofMul xb) b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    obtain ⟨u, hu, -⟩ : Pi.single a (ε a) - Pi.single b (ε b) ∈ ggDMemberRoots e φ L := by
      rw [hΦL]
      exact ⟨a, b, hab, rfl⟩
    have h0 := (hθ u _ hu xb).mp ((hfx u _ hu).mpr (stdsub_dot_pair hε a b))
    rw [stdsub_sum_pair] at h0
    linear_combination h0
  obtain ⟨d, hdD, hdx⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers (xb : G) := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers (xb : G) from fun d hd => h d hd)
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 _ xb.2) hx1, pow_two] at h1
    have h2 : p * 2 ≤ p * p := Nat.mul_le_mul_left p hp.two_le
    have h3 := hp.two_le
    omega
  have hdC : d ∈ Subgroup.centralizer (J : Set G) := (Subgroup.mem_inf.mp (hDJ ▸ hdD)).2
  let db : ↥Bs := ⟨d, hDB hdD⟩
  have hΦJ : ∀ η ∈ ggDMemberRoots e φ J, ∃ a b, a ≠ b ∧
      (ε a : ZMod p) * θ (Additive.ofMul db) a = (ε b : ZMod p) * θ (Additive.ofMul db) b ∧
      η = Pi.single a (ε a) - Pi.single b (ε b) := by
    rintro η ⟨u, hu, huJ⟩
    have hηL : η ∈ ggDMemberRoots e φ L := ⟨u, hu, ggAutomizer_mono Bs hJL huJ⟩
    rw [hΦL] at hηL
    obtain ⟨a, b, hab, rfl⟩ := hηL
    have hfix : ((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) db = db := by
      refine ggAutomizer_apply_eq_of_le_centralizer (fun j hj => ?_) huJ
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_centralizer_iff.mp hdC j hj).symm
    have h0 := (hθ u _ hu db).mp hfix
    rw [stdsub_sum_pair] at h0
    exact ⟨a, b, hab, by linear_combination h0, rfl⟩
  have hshift := ggDk_coord_shift hp θ hε (fun h => hx1 (by rw [h]; rfl)) hxε db
  have hnc : ∃ a b, (ε a : ZMod p) * θ (Additive.ofMul db) a ≠
      (ε b : ZMod p) * θ (Additive.ofMul db) b := by
    by_contra h
    push Not at h
    obtain ⟨n, hn⟩ := hshift ((ε ⟨0, by omega⟩ : ZMod p) * θ (Additive.ofMul db) ⟨0, by omega⟩)
    have h1 : db * (xb ^ n)⁻¹ = 1 := Additive.ofMul.injective (θ.injective (funext fun a => by
      rw [hn a, h a ⟨0, by omega⟩, sub_self, mul_zero, ofMul_one, map_zero, Pi.zero_apply]))
    exact hdx (by
      rw [show d = (xb : G) ^ n from congrArg Subtype.val (mul_inv_eq_one.mp h1)]
      exact Subgroup.npow_mem_zpowers _ n)
  obtain ⟨a₀, hsh, hiff⟩ := ggDk_signedA_off_of_card hε _ hnc hΦJ hT hTc
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨b₀, hb₀⟩ := exists_ne a₀
  obtain ⟨n, hn⟩ := hshift ((ε b₀ : ZMod p) * θ (Additive.ofMul db) b₀)
  have hμ : (ε a₀ : ZMod p) * ((ε a₀ : ZMod p) * θ (Additive.ofMul db) a₀ -
      (ε b₀ : ZMod p) * θ (Additive.ofMul db) b₀) ≠ 0 :=
    mul_ne_zero (by rcases hε a₀ with h | h <;> simp [h]) (sub_ne_zero.mpr (hsh b₀ hb₀).1.symm)
  have hθd₀ : ∀ a, θ (Additive.ofMul (db * (xb ^ n)⁻¹)) a = if a = a₀ then (ε a₀ : ZMod p) *
      ((ε a₀ : ZMod p) * θ (Additive.ofMul db) a₀ - (ε b₀ : ZMod p) * θ (Additive.ofMul db) b₀)
      else 0 := fun a => by
    rw [hn a]
    split_ifs with ha
    · rw [ha]
    · rw [(hsh a ha).2 b₀ hb₀, sub_self, mul_zero]
  have hd₀D : ((db * (xb ^ n)⁻¹ : ↥Bs) : G) ∈ D := D.mul_mem hdD (D.inv_mem (D.pow_mem hxD n))
  have hd₀x : ((db * (xb ^ n)⁻¹ : ↥Bs) : G) ∉ Subgroup.zpowers (xb : G) := fun h => hdx (by
    have h2 : d = ((db * (xb ^ n)⁻¹ : ↥Bs) : G) * (xb : G) ^ n := by
      push_cast
      exact (inv_mul_cancel_right _ _).symm
    rw [h2]
    exact (Subgroup.zpowers _).mul_mem h (Subgroup.npow_mem_zpowers _ n))
  refine ⟨a₀, db * (xb ^ n)⁻¹, (ggClosure_pair_eq hp hDcard hxD hd₀D hx1 (hBs.2 _ xb.2) hd₀x).symm,
    ⟨fun h => hμ ?_, fun u η hu => ?_⟩, hpJ, fun η => ?_⟩
  · have h3 := hθd₀ a₀
    rw [h, ofMul_one, map_zero, Pi.zero_apply, if_pos rfl] at h3
    exact h3.symm
  ·
    rw [hθ u η hu, Finset.sum_eq_single a₀ (fun c _ hc => by rw [hθd₀, if_neg hc, zero_mul])
      (fun h => absurd (Finset.mem_univ a₀) h), hθd₀, if_pos rfl, mul_eq_zero, or_iff_right hμ]
    rcases ggDRootSet_apply (hu.mem (by omega)) a₀ with h | h | h <;> rw [h] <;> simp
  · rw [hΦL]
    exact hiff η

end CFSG.StandardType

end
