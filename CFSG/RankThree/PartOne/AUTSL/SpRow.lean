module

public import CFSG.RankThree.PartOne.AUTSL.SpCore
public import CFSG.RankThree.PartOne.AUTSL.Transport

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank

namespace AUTSL

theorem coreStmt_sp (K : Type) [Field K] [Finite K] [CharP K 2] : CoreStmt (StatedSp 3 K) := by
  intro S hS hsyl _ E B hEc hE5 hBE hBN hB α hαB hα3 hα1 x hxB
  obtain ⟨S₀, hS₀⟩ := hsyl
  obtain ⟨𝒲, h𝒲⟩ := exists_stab_family_sp (by norm_num : 1 ≤ 3) _ S₀ hS₀
  exact sp_core hS 𝒲 h𝒲 hEc hE5 hBE hBN hB α hαB hα3 hα1 x hxB

theorem kf1511BTESp6_holds : KF1511BTESp6 := by
  refine kf1511BTEAt_of_core .PSp 3 ?_
  intro X _ _ f hmodel
  have hcl : StatedClassicalModel X .PSp 3 2 f := by
    rcases hmodel with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨-, K, hF, hFin, hcard, ⟨e₀⟩⟩ := hcl
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
    have h1 : ringChar K ∣ 2 ^ f := by
      rw [← hcard, Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self _ n.ne_zero
    have h3 : ringChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    exact CharP.congr (ringChar K) h3
  have hbot : spScalars 3 K = ⊥ := spScalars_eq_bot_of_charTwo
  have hinj : Function.Injective (proj 3 K) :=
    (MonoidHom.ker_eq_bot_iff _).1 (by rw [ker_proj, hbot])
  let ψ : StatedSp 3 K ≃* StatedProj (StatedSp 3 K) :=
    MulEquiv.ofBijective (proj 3 K) ⟨hinj, proj_surjective⟩
  exact transport_core (e₀.trans ψ.symm) (coreStmt_sp K)

end AUTSL

end CFSG.RankThree.PartOne
