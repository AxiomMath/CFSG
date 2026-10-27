module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WInp2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WKl
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126 S126P31
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Pointwise

theorem borelF_absurd_w31 (hB : BorelF_w31) (hNP : NoPermL_w31) (h1229 : Lemma12_6_29)
    {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]
    (F : Frame126 T L V) (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    {H K : Subgroup G} (hIs : IsHK T L F.V1 H K) (h918 : HypF918 T V L F.V1 F.V5 H K)
    (hK : conjClosure K T = K) {n : ℕ} (h2 : 2 ≤ n) (he : Even n)
    (hX : (IsPSL 2 2 n (starMod_w31 H K) ∨ IsPSL 3 2 n (starMod_w31 H K)) ∧ 4 ≤ n ∨
      IsPSU 3 2 n (starMod_w31 H K)) : False := by
  obtain ⟨P, hPL, p, hp, hp3, hP0, hPp, hperm⟩ :=
    hB h1229 G T L V F hH hZ H K hIs h918 hK n h2 he hX
  exact hP0 (hNP G T L V F hH hZ P hPL p hp hp3 hPp hperm)

theorem kListWeak12631_holdsF
    (hE : E114ListF_w31) (hM22 : NoM22_w31) (hSz : NoSzF_w31) (hPar : ParityF_w31)
    (hB : BorelF_w31) (hNP : NoPermL_w31) (hSp4 : NoSp4F_w31) (hG2 : NoG2F_w31)
    (hD : NoL2PairF_w31) : KListWeak12631 := by
  intro h1229 G _ _ T L V _ F hH hZ H K hIs h918
  rcases hE h1229 G T L V F hH hZ H K hIs h918 with
    ⟨n, h2, ⟨hK, hfam⟩ | ⟨hK, hfam⟩⟩ | ⟨hn2, hM⟩
  ·
    rcases hfam with h | h | h | h | h | h
    ·
      by_cases hn2' : n = 2
      · subst hn2'
        exact Or.inl (psl224Alt5_w31 _ h)
      · have he := hPar h1229 G T L V F hH hZ H K hIs h918 hK n h2 (Or.inl h)
        obtain ⟨r, hr⟩ := he
        exact (borelF_absurd_w31 hB hNP h1229 F hH hZ hIs h918 hK h2 ⟨r, hr⟩
          (Or.inl ⟨Or.inl h, by omega⟩)).elim
    ·
      exact (hSz h1229 G T L V F hH hZ H K hIs h918 n h2 h).elim
    ·
      have he := hPar h1229 G T L V F hH hZ H K hIs h918 hK n h2 (Or.inr (Or.inr h))
      exact (borelF_absurd_w31 hB hNP h1229 F hH hZ hIs h918 hK h2 he (Or.inr h)).elim
    ·
      by_cases hn2' : n = 2
      · subst hn2'
        exact Or.inr h
      · have he := hPar h1229 G T L V F hH hZ H K hIs h918 hK n h2 (Or.inr (Or.inl h))
        obtain ⟨r, hr⟩ := he
        exact (borelF_absurd_w31 hB hNP h1229 F hH hZ hIs h918 hK h2 ⟨r, hr⟩
          (Or.inl ⟨Or.inr h, by omega⟩)).elim
    ·
      exact (hSp4 h1229 G T L V F hH hZ H K hIs h918 hK n h2 h).elim
    ·
      exact (hG2 h1229 G T L V F hH hZ H K hIs h918 hK n h2 h).elim
  ·
    rcases hfam with h | h | ⟨hn2', hA⟩
    ·
      have hn2'' := hD h1229 G T L V F hH hZ H K hIs h918 hK n h2 h
      subst hn2''
      exact Or.inl (psl224Alt5_w31 _ h)
    ·
      exact (hSz h1229 G T L V F hH hZ H K hIs h918 n h2 h).elim
    ·
      exact Or.inl hA
  ·
    exact (hM22 h1229 G T L V F hH hZ H K hIs h918 hn2 hM).elim

end CFSG.Quasithin.H13
