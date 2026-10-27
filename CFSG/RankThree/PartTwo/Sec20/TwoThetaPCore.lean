module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.RankThree.PartTwo.Sec20.TwoThetaNorm
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofTheta
import CFSG.GH74.GLS.Stage2.Final.Thm4.L192Rep
import CFSG.HardMathSupport.Solomon.Coordinator.L3ASL2

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace TwoTheta

open CFSG.RankThree.PartTwo.Sec20.TwoTheta

section PCore

variable {Λ : Type} [Group Λ] [Finite Λ] [Group.IsPerfect Λ]

theorem hom_eq_one_of_gl_two
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* projSL 3 (GaloisField 2 2)) {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {n : ℕ} (hn : n ≤ 2) (ρ : Λ →* GL (Fin n) (ZMod p)) : ρ = 1 := by
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := (ZMod.natCast_eq_zero_iff 3 p).mp h'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp this)
  have hdet : ∀ l, Matrix.GeneralLinearGroup.det (ρ l) = 1 := fun l =>
    CFSG.SectionRank.Ccomm.perfect_hom_eq_one (Matrix.GeneralLinearGroup.det.comp ρ) l
  interval_cases n
  · exact MonoidHom.ext fun l => Subsingleton.elim _ _
  · refine MonoidHom.ext fun l => ?_
    have h1 := hdet l
    have h2 : Matrix.det ((ρ l : GL (Fin 1) (ZMod p)) : Matrix (Fin 1) (Fin 1) (ZMod p)) = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, h1]
      rfl
    rw [Matrix.det_fin_one] at h2
    apply Units.ext
    ext i j
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
    simpa using h2
  · have hH : CFSG.Open.pRank 3 (⊤ : Subgroup ρ.range) ≤ 1 := by
      apply CFSG.SectionRank.pRank_le Nat.prime_three.one_lt
      intro E _ hE
      have hE' := CFSG.SectionRank.isElemAbelian_map hE ρ.range.subtype
      have hdetE : ∀ x ∈ E.map ρ.range.subtype,
          ((x : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
        rintro _ ⟨y, -, rfl⟩
        obtain ⟨l, hl⟩ := y.2
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        show ((Matrix.GeneralLinearGroup.det (y : GL (Fin 2) (ZMod p)) : (ZMod p)ˣ) : ZMod p) = 1
        rw [← hl, hdet l]
        rfl
      have := CFSG.HardMathSupport.Solomon.Coordinator.card_le_three_of_elemAbelian_sl2 h3 hE' hdetE
      rw [Subgroup.card_map_of_injective ρ.range.subtype_injective] at this
      simpa using this
    have h1 := Res5.hom_eq_one_of_l34 e hH ρ.rangeRestrict
    refine MonoidHom.ext fun l => ?_
    have h2 := congrArg (fun f : Λ →* ρ.range => (f l : GL (Fin 2) (ZMod p))) h1
    simpa using h2

theorem fixes_pCore
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* projSL 3 (GaloisField 2 2)) {Y : Type} [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hrank : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2)
    (φ : Λ →* MulAut Y) (g : Λ) : ∀ y ∈ CFSG.pCore p Y, φ g y = y := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Q := CFSG.pCore p Y with hQ
  have hQchar : ∀ g : Λ, Q.map (φ g).toMonoidHom = Q := fun g =>
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) (φ g)
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup Q) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Q]
    exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hrank
  obtain ⟨n, ρ, hn, -, hker⟩ :=
    CFSG.GH74.GLS.Stage2.Final.Thm4.L192.exists_rep (by omega : p ≠ 2) hQp hrk
      (Res5.restrictAut φ Q hQchar)
  have hρ : ρ = 1 := hom_eq_one_of_gl_two e (by omega) hn ρ
  have hα : Res5.restrictAut φ Q hQchar = 1 := by
    apply hom_eq_one_of_threeElements e
    rintro x ⟨k, hk⟩
    apply hker x _ (by rw [hρ]; rfl)
    have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_left h1
      (Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_three hp).mpr (by omega)))
  intro y hy
  have h2 : Res5.restrictAut φ Q hQchar g ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hα]; rfl
  exact (Res5.restrictAut_apply φ Q hQchar g ⟨y, hy⟩).symm.trans (congrArg Subtype.val h2)

end PCore

end TwoTheta

end CFSG.RankThree.PartTwo.Sec20
