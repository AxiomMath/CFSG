module

public import CFSG.Quasithin.Background.SmithD310USetup
public import CFSG.Quasithin.Background.SmithD39TwoBender
public import CFSG.Quasithin.Background.SmithD39TwoSz

public section

namespace CFSG.Quasithin.SmithD310U

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Quasithin.SmithD39Two
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

theorem beta_false_of_sz (hA23 : A23SQTKListFact) (hSzF : H13.SimpleThreePrimeSuzukiFact)
    {M T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W} {A : Subgroup (MulAut W)}
    {r : ℚ} {k : ℕ} (hS : D310USit M T L V t A r k)
    (hSZ : ∀ K : Subgroup (MulAut W), K ∈ cComp M → CFSG.IsQuasisimple ↥K →
      K ≤ Subgroup.centralizer (L : Set (MulAut W)) →
      (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n) →
      A ≤ Subgroup.centralizer (K : Set (MulAut W)))
    {u w : MulAut W} (hu : u ∈ L) (hw : w ∈ L) (hu3 : u ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (huw : u * w = w * u) (hu1 : u ≠ 1) (hwu : w ∉ Subgroup.zpowers u)
    {u' s : MulAut W} (hu' : u' ∈ L) (hs : s ∈ L) (hu'3 : u' ^ 3 = 1) (hu'1 : u' ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u' * s⁻¹ = u'⁻¹) : False := by
  set C := M ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hCdef
  set B := A ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hBdef
  have hLM := hS.L_le
  have hMq := hS.qsqtk
  have hBC : B ≤ C := hS.cent_le_cent
  have hS2 : ∀ x ∈ C, ∀ y ∈ C, y ^ 3 = 1 → y ≠ 1 → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      x * y * x⁻¹ = y⁻¹ → False := fun x hx y hy hy3 hy1 hx2 hxy =>
    no_inverting_two_elt hMq hLM hu hw hu3 hw3 huw hu1 hwu hx hy hy3 hy1 hx2 hxy
  rcases exists_moved_piece hS.pCoreOf_two_cent_eq_bot hBC hS.isPGroup_cent hS.hB
      hS.M_le_normalizer with ⟨p, hp, hp2, hpB⟩ | ⟨K, hK, hKq, hKC, hKB⟩
  · by_cases hp3 : p = 3
    ·
      subst hp3
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨g, hg, hgB⟩ := Set.not_subset.1 hpB
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hgB
      push Not at hgB
      obtain ⟨b, hbB, hbg⟩ := hgB
      have hbC : b ∈ C := hBC hbB
      have hb2 : b ^ 2 = 1 := hS.isA2.isElemAbelian2.2 b hbB.1
      have hbP : ∀ g ∈ CFSG.Open.pCoreOf 3 C, b * g * b⁻¹ ∈ CFSG.Open.pCoreOf 3 C :=
        fun g hg => (Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 C hbC) g).1 hg
      obtain ⟨y, hyP, hy3, hy1, hby⟩ := exists_inv_of_not_comm
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 C) hb2 hbP hg hbg
      exact hS2 b hbC y (CFSG.LieType.BorelTits.pCoreOf_le 3 C hyP) hy3 hy1
        ⟨1, by simpa using hb2⟩ hby
    ·
      have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
        · exact absurd h hp2
        · exact absurd h hp3
        · exact absurd (h ▸ hp) (by norm_num)
        · exact h
      apply hpB
      rw [← Subgroup.le_centralizer_iff]
      exact (inf_le_left : B ≤ A).trans (hS.le_centralizer_pCoreOf_cent hp hp5)
  · by_cases h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)
    ·
      have hcyc : ∀ P : Sylow 3 ↥K, IsCyclic ↥P :=
        isCyclic_sylow_three_of_le hMq hLM hu' hs hu'3 hu'1 hs2 hsu hKC
      obtain ⟨y, x, hy3, -, hx2, hxy⟩ := exists_two_elt_inverting hKq h3 hcyc
      have hy1 : (y : MulAut W) ≠ 1 := by
        intro h
        have : y = 1 := Subtype.ext h
        rw [this, orderOf_one] at hy3
        norm_num at hy3
      refine hS2 x (hKC x.2) y (hKC y.2) ?_ hy1 ?_ ?_
      · have := pow_orderOf_eq_one y
        rw [hy3] at this
        exact congrArg Subtype.val this
      · obtain ⟨k, hk⟩ := hx2
        exact ⟨k, congrArg Subtype.val hk⟩
      · exact congrArg Subtype.val hxy
    ·
      apply hKB
      exact (inf_le_left : B ≤ A).trans (hSZ K hK hKq (hKC.trans inf_le_right)
        (suzukiModel_of_le hA23 hSzF hMq (hKC.trans inf_le_left) hKq h3))

theorem sz_le_centralizer (h38 : D38Top) {M T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ} (hS : D310USit M T L V t A r k)
    {K : Subgroup (MulAut W)} (hK : K ∈ cComp M) (hKq : CFSG.IsQuasisimple ↥K)
    (hKL : K ≤ Subgroup.centralizer (L : Set (MulAut W)))
    (hSz : ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n) :
    A ≤ Subgroup.centralizer (K : Set (MulAut W)) :=
  sz_comp_le_centralizer h38 hS.exp hS.qsqtk hS.M_le_normalizer hS.L_le hS.perfect
    hS.commV_eq_top hS.hr hS.hr2 hS.hAQ hK hKq hKL hSz

theorem beta_false (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) {M T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ} (hS : D310USit M T L V t A r k)
    {u w : MulAut W} (hu : u ∈ L) (hw : w ∈ L) (hu3 : u ^ 3 = 1) (hw3 : w ^ 3 = 1)
    (huw : u * w = w * u) (hu1 : u ≠ 1) (hwu : w ∉ Subgroup.zpowers u)
    {u' s : MulAut W} (hu' : u' ∈ L) (hs : s ∈ L) (hu'3 : u' ^ 3 = 1) (hu'1 : u' ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u' * s⁻¹ = u'⁻¹) : False :=
  beta_false_of_sz hA23 hSzF hS (fun _ hK hKq hKL hSz => sz_le_centralizer h38 hS hK hKq hKL hSz)
    hu hw hu3 hw3 huw hu1 hwu hu' hs hu'3 hu'1 hs2 hsu

end CFSG.Quasithin.SmithD310U
