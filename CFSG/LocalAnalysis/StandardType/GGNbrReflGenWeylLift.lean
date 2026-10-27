module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflectionLift
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

variable {G : Type} [Group G] [Finite G]

theorem exists_isReflection_overGamma_of_weylElt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs K : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {n : K}
    (hnW : GGTorusWeylElt p (ggGamma K hN).range n)
    (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma K hN).range : Set (MulAut ↥K)))
    (hrefl : GGIsReflection p (ggConjAut (ggGamma K hN).range hn)) :
    ∃ (g : G) (hgK : g ∈ K) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
      GGIsReflection p (ggConjAut Bs hg) ∧
        GGOverGamma hN (ggConjAut Bs hg) (ggConjAut (ggGamma K hN).range hn) := by
  classical
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_ggTorusWeylElt hN hSC hnW
  have h₀ : GGOverGamma hN (ggConjAut Bs hnN)
      (ggConjAut (ggGamma K hN).range hn) := by
    have h := ggOverGamma_conjAut (hN := hN) n.2 hnN
    have heq : ggConjAut (ggGamma K hN).range
          (conj_mem_normalizer_range_ggGamma hN n.2 hnN)
        = ggConjAut (ggGamma K hN).range hn := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rfl
    rwa [heq] at h
  obtain ⟨k, m, hm_odd, horder⟩ :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_pos (n : G)).ne'
  let g : G := (n : G) ^ m
  have hgK : g ∈ K := Subgroup.pow_mem K n.2 m
  have hg : g ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.pow_mem (Subgroup.normalizer (Bs : Set G)) hnN m
  have hg_eq : ggConjAut Bs hg = ggConjAut Bs hnN ^ m := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply Bs hg b, ggConjAut_pow_apply Bs hnN m b]
  have ham : (ggConjAut (ggGamma K hN).range hn) ^ m
      = ggConjAut (ggGamma K hN).range hn := by
    obtain ⟨j, hj⟩ := hm_odd
    rw [hj, pow_succ, pow_mul, hrefl.1, one_pow, one_mul]
  have hGOGm : GGOverGamma hN (ggConjAut Bs hnN ^ m)
      (ggConjAut (ggGamma K hN).range hn) := by
    have h := h₀.pow m
    rwa [ham] at h
  have hfix : ∀ v ∈ (ggGamma K hN).rangeRestrict.ker,
      (ggConjAut Bs hnN ^ m) v = v := by
    intro v hv
    have hv1 : ggGamma K hN v = 1 := by
      have h := (MonoidHom.mem_ker (f := (ggGamma K hN).rangeRestrict)).mp hv
      simpa using Subtype.ext_iff.mp h
    have hvc : (v : G) ∈ Subgroup.centralizer (K : Set G) :=
      (ggGamma_eq_one_iff K hN v).mp hv1
    have hcomm : (n : G) ^ m * (v : G) = (v : G) * (n : G) ^ m :=
      (Subgroup.mem_centralizer_iff.mp hvc) ((n : G) ^ m) hgK
    apply Subtype.ext
    rw [ggConjAut_pow_apply Bs hnN m v, hcomm]
    group
  have hc : (ggConjAut Bs hnN ^ m) ^ 2 ^ k = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [← pow_mul, ggConjAut_pow_apply Bs hnN (m * 2 ^ k) b]
    have hpow : (n : G) ^ (m * 2 ^ k) = 1 := by
      rw [Nat.mul_comm m (2 ^ k), ← horder, pow_orderOf_eq_one]
    rw [hpow]
    simp
  have hVc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
  have hVp : ∀ v : ↥Bs, v ^ p = 1 := fun v => Subtype.ext (hBs.2 v v.2)
  have hlifts : GGIsReflection p (ggConjAut Bs hnN ^ m) :=
    isReflection_of_quotient hp hp2 hVc hVp (ggGamma K hN).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _) (ggConjAut Bs hnN ^ m)
      (ggConjAut (ggGamma K hN).range hn) hGOGm hfix hc hrefl.1 hrefl.2
  exact ⟨g, hgK, hg, by rw [hg_eq]; exact hlifts, by rw [hg_eq]; exact hGOGm⟩

end CFSG.StandardType

end
