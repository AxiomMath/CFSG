module

public import CFSG.RankThree.PartOne.K133.ResTransfer
public import CFSG.RankThree.PartOne.K133.KillL2
public import CFSG.RankThree.PartOne.K133.UnipPSL2
import CFSG.Adapters.LinearCatalog
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.RankThree.GroupTheory CFSG.GorensteinWalter CFSG.RankThree.PartOne.S13K
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem goodRes_psl2 {F : Type} [Field F] [Finite F] {r : ℕ} [Fact r.Prime] [CharP F r] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : GoodRes p (PSL2 F) := by
  classical
  by_cases hpr : p = r
  · subst hpr
    intro Ē hE hc ⟨C, hCĒ, hCc, Kb, hKs, hKn, hpK, hfix⟩
    exfalso
    have hC : IsElementaryAbelian p C := isElementaryAbelian_of_le hE hCĒ
    obtain ⟨C₀, hC₀C, hC₀in, hC₀card⟩ := exists_inner_core_psl2 hp hp2 C hC
    have hp0 : 0 < p := hp.pos
    have hC₀gt : 1 < Nat.card C₀ := by
      rw [hCc, pow_two] at hC₀card
      have h1 : p ≤ Nat.card C₀ := Nat.le_of_mul_le_mul_left hC₀card hp0
      have := hp.one_lt
      omega
    obtain ⟨β, hβ, hβ1⟩ : ∃ β ∈ C₀, β ≠ 1 := by
      by_contra hno
      push Not at hno
      have : C₀ = ⊥ := (Subgroup.eq_bot_iff_forall C₀).2 hno
      rw [this, Subgroup.card_bot] at hC₀gt
      omega
    obtain ⟨g, hg⟩ := hC₀in hβ
    have hβp : β ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := C) β (hC₀C hβ)
    have hgp : g ^ p = 1 := by
      have h1 : MulAut.conj (g ^ p) = 1 := by rw [map_pow, hg, hβp]
      have h2 : g ^ p ∈ Subgroup.center (PSL2 F) := by
        rw [Subgroup.mem_center_iff]
        intro z
        have h3 := DFunLike.congr_fun h1 z
        rw [MulAut.conj_apply, MulAut.one_apply] at h3
        calc z * g ^ p = (g ^ p * z * (g ^ p)⁻¹) * g ^ p := by rw [h3]
          _ = g ^ p * z := by group
      rw [psl2_center_eq_bot F, Subgroup.mem_bot] at h2
      exact h2
    have hg1 : g ≠ 1 := by
      intro h1
      apply hβ1
      rw [← hg, h1, map_one]
    have hexp : ∀ k : Kb, k ^ p = 1 := by
      intro k
      have hcomm : g * (k : PSL2 F) = (k : PSL2 F) * g := by
        have h1 := hfix β (hC₀C hβ) k k.2
        rw [← hg, MulAut.conj_apply] at h1
        calc g * (k : PSL2 F) = (g * (k : PSL2 F) * g⁻¹) * g := by group
          _ = (k : PSL2 F) * g := by rw [h1]
      have := psl2_centralizer_pow hp2 g k hg1 hgp hcomm
      exact Subtype.ext (by simpa using this)
    have hPg : IsPGroup p Kb := fun k => ⟨1, by simpa using hexp k⟩
    have : Group.IsNilpotent Kb := hPg.isNilpotent
    have hsol : Group.IsSolvable Kb := inferInstance
    obtain ⟨a, b, hab⟩ := hKn
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsol a b)
  · have hne : ((p : ℕ) : F) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff F r p] at h0
      exact hpr ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).1 h0).symm
    have : NeZero ((p : ℕ) : F) := ⟨hne⟩
    exact (noRankThree_psl2 hp hp2).dead.good.goodRes

theorem kf133ResMaxItem_zero (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) : KF133ResMaxItem 0 :=
  KF133ResMaxAt.of_goodRes hTypes fun X _ _ _ hne hX p hp h5 => by
    obtain ⟨q, hq2, -, hv, ⟨e0⟩⟩ := hX
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have e : X ≃* PSL2 (GaloisField q.p q.exponent) :=
      e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
    exact GoodRes.of_mulEquiv hp e (goodRes_psl2 (r := q.p) hp (by omega))

end CFSG.RankThree.PartOne.K133
