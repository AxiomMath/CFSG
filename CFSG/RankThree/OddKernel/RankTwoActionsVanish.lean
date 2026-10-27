module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwoAction
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm

theorem sq_eq_one_of_eq_one_or_inv {W : Type*} [Group W] {g : MulAut W}
    (h : g = 1 ∨ ∀ w, g w = w⁻¹) : g ^ 2 = 1 := by
  rcases h with rfl | h
  · exact one_pow 2
  · ext w
    rw [sq, MulAut.mul_apply, h, h, inv_inv, MulAut.one_apply]

theorem exists_inv_ne_of_pow_eq_one {W : Type*} [Group W] [Nontrivial W] {p : ℕ}
    (hp2 : p ≠ 2) (hp : p.Prime) (hpow : ∀ w : W, w ^ p = 1) : ∃ w : W, w⁻¹ ≠ w := by
  obtain ⟨w, hw⟩ := exists_ne (1 : W)
  refine ⟨w, fun h => hw ?_⟩
  have h2 : w ^ 2 = 1 := by rw [sq, ← inv_mul_cancel w, h]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  have := hpow w
  rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at this
  exact this

theorem centerless_semisimple_prime_quotient_rank_two_actions_vanish {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y)
    [P.Normal] (hP : IsPGroup p P) (hE : layer (Y ⧸ P) = ⊤) (hZ : center (Y ⧸ P) = ⊥)
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup p Q) (hrank : pRank p Q ≤ 2)
    (β : Y →* MulAut Q) : β = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hβ
  have : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hβ (MonoidHom.ext fun y => MulEquiv.ext fun q => Subsingleton.elim _ _)
  obtain ⟨D, hDc, -, hDexp, -, -, hker⟩ := supercritical_witness hp2 hQ
  have hrank' : CFSG.Open.pRank p (⊤ : Subgroup Q) ≤ 2 := by
    rw [← pRank_eq_open_pRank_top]
    exact hrank
  set W := D ⧸ frattini D
  set φ : Y →* MulAut W := (frattiniAction D).comp β with hφ
  obtain ⟨hW2, hJne, hJperf, -, -, hJq, hcen, -, -⟩ :=
    critical_rank_two_action_recognition hp2 hQ hrank' D hDexp hker β hβ φ.range rfl
  set J := φ.range with hJ
  have hDp : IsPGroup p D := hQ.to_subgroup D
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hDp
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hW2
  set ψ := elemAutEquivGL e with hψ
  have hJ'ne : J.map ψ.toMonoidHom ≠ ⊥ := by
    rw [Ne, map_eq_bot_iff_of_injective _ ψ.injective]
    exact hJne
  have : Group.IsPerfect (J.map ψ.toMonoidHom) := Group.IsPerfect.map _
  obtain ⟨g, hgJ, hg⟩ := mem_map.1 (neg_one_mem_of_perfect hp2 _ hJ'ne)
  have hginv : ∀ w : W, g w = w⁻¹ := (elemAutEquivGL_eq_neg_one_iff e g).1 hg
  have hgcen : (⟨g, hgJ⟩ : J) ∈ center J := (hcen ⟨g, hgJ⟩).2 (Or.inr hginv)
  have : Nontrivial W := by
    rw [← Finite.one_lt_card_iff_nontrivial, hW2]
    exact Nat.one_lt_pow two_ne_zero hp.one_lt
  obtain ⟨w, hw⟩ := exists_inv_ne_of_pow_eq_one hp2 hp hWpow
  have hg1 : (⟨g, hgJ⟩ : J) ≠ 1 := by
    intro h
    have := congrArg (fun x : J => (x : MulAut W) w) h
    simp only [OneMemClass.coe_one, MulAut.one_apply, hginv] at this
    exact hw this
  set φ' : Y →* J := φ.rangeRestrict with hφ'
  have hφ's : Function.Surjective φ' := φ.rangeRestrict_surjective
  have hBn : (P.map φ').Normal := Subgroup.Normal.map inferInstance φ' hφ's
  have hBp : IsPGroup p (P.map φ') := hP.map φ'
  have hJqF : CFSG.IsQuasisimple J := by
    refine ⟨hJperf, hJq.2, ?_⟩
    have : IsSimpleGroup (J ⧸ center J) := hJq.2
    have : Nontrivial (J ⧸ center J) := IsSimpleGroup.toNontrivial
    by_contra hab
    push Not at hab
    have hcomm : commutator (J ⧸ center J) = ⊥ := by
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [mem_centralizer_iff]
      intro b _
      exact hab b a
    have : Group.IsPerfect (J ⧸ center J) := inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hcomm
    exact top_ne_bot hcomm
  have hBtop : P.map φ' ≠ ⊤ := by
    intro htop
    have : Nontrivial J := (nontrivial_iff_ne_bot J).2 hJne
    have hJp : IsPGroup p J := by
      have := hBp.of_equiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
      exact this
    exact Group.IsPerfect.not_isNilpotent J hJp.isNilpotent
  have hBcen : P.map φ' ≤ center J :=
    ((CFSG.LocalCores.quasisimple_normal_subgroups hJqF hBn).resolve_left hBtop)
  have hBbot : P.map φ' = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨k, hk⟩ := hBp ⟨b, hb⟩
    have hb2 : b ^ 2 = 1 := by
      have hb' := (hcen b).1 (hBcen hb)
      have := sq_eq_one_of_eq_one_or_inv
        (show (b : MulAut W) = 1 ∨ ∀ w, (b : MulAut W) w = w⁻¹ from hb')
      exact Subtype.ext (by rw [SubgroupClass.coe_pow, this, OneMemClass.coe_one])
    have hbk : b ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime (2 ^ 1) (p ^ k) :=
      Nat.Coprime.pow 1 k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have hord : orderOf b ∣ Nat.gcd 2 (p ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb2) (orderOf_dvd_of_pow_eq_one hbk)
    rw [show Nat.gcd 2 (p ^ k) = 1 by simpa using hcop, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact (mem_bot).2 hord
  have hPker : P ≤ φ'.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, ← mem_bot, ← hBbot]
    exact mem_map_of_mem φ' hx
  set χ : Y ⧸ P →* J := QuotientGroup.lift P φ' hPker with hχ
  have hχs : Function.Surjective χ := by
    intro j
    obtain ⟨y, rfl⟩ := hφ's j
    exact ⟨(y : Y ⧸ P), rfl⟩
  have hZJ := (centerless_semisimple_quotient hE hZ χ hχs).2
  rw [hZJ, mem_bot] at hgcen
  exact hg1 hgcen

theorem le_center_of_centerless_semisimple_prime_quotient {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y)
    [P.Normal] (hP : IsPGroup p P) (hE : layer (Y ⧸ P) = ⊤) (hZ : center (Y ⧸ P) = ⊥)
    (Q : Subgroup Y) [Q.Normal] (hQ : IsPGroup p Q) (hrank : pRank p Q ≤ 2) :
    Q ≤ center Y := by
  have h := centerless_semisimple_prime_quotient_rank_two_actions_vanish hp hp2 P hP hE hZ hQ
    hrank (MulAut.conjNormal (H := Q))
  intro q hq
  rw [mem_center_iff]
  intro y
  have := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : Y)) (DFunLike.congr_fun h y)
  simp only [MulAut.conjNormal_apply, MonoidHom.one_apply, MulAut.one_apply] at this
  calc y * q = y * q * y⁻¹ * y := by group
    _ = q * y := by rw [this]

end CFSG.RankThree.OddKernel
