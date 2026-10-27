module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Cent

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

theorem mem_normalizer_of_mem_normalizer_zpowers {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD5 B b₀) (hodd : Odd (Nat.card ↥(Subgroup.centralizer (E : Set G))))
    (hD : Odd (Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G))))
    {g : G} (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hGsimple, hHyp, hCanon⟩ := hstd
  obtain ⟨hb₀ord, hKC, hKn, hKz, hKmark, hcyc, hrank, hconj, hEmax, hb₀E, hEcard, hXcard⟩ := hHyp
  obtain ⟨hdisj, hsup, hmax, hcard, hself⟩ := hCanon
  have _ := hB.1
  have _ := hrec.1
  have _ := hodd
  have _ := hD
  obtain ⟨hKs, _⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD (r := 5) (by norm_num) hKmark hKz
  have hA3 : IsPGroup 3 ↥(E ⊓ K) := CFSG.Open.IsElemAbelian.isPGroup hmax.2.1
  have hAc : ¬ IsCyclic ↥(E ⊓ K) := by
    intro hcycA
    obtain ⟨gA, hgA⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcycA
    have hgen : Subgroup.zpowers gA = ⊤ := hgA
    have hgA3 : gA ^ 3 = 1 := by
      apply Subtype.ext
      have hmem : (gA : G) ∈ E ⊓ K := gA.2
      have h := hmax.2.1.2 (gA : G) hmem
      simpa using h
    have hcard_g : orderOf gA = 3 ^ 5 := by
      rw [← Nat.card_zpowers, hgen, Subgroup.card_top, hcard]
    have hdvd : orderOf gA ∣ 3 := orderOf_dvd_of_pow_eq_one hgA3
    have hdiv : 3 ^ 5 ∣ 3 := by rw [← hcard_g]; exact hdvd
    norm_num at hdiv
  exact normalizer_zpowers_le_normalizer hKs hKC hKn hcyc (A := E ⊓ K) inf_le_right hA3 hAc hg

end CFSG.StandardType.FrameRoute.FS81

end
