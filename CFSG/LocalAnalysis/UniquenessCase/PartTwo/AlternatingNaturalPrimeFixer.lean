module

public import CFSG.Quasithin.Background.B4Models
import CFSG.Quasithin.Background.FFC4Real
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKAltFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem exists_prime_order_fixer_of_alternatingNatural
    {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {n p : ℕ}
    (hpPrime : p.Prime) (hpodd : Odd p) (hn : 2 * (p - 1) < n)
    (hN : AlternatingNatural H (⊤ : Subgroup W) ⊥ n) :
    ∀ x : W, ∃ b ∈ H, orderOf b = p ∧ b x = x := by
  classical
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  have hp3 : 3 ≤ p := by
    have := hpPrime.two_le
    omega
  have hn5 : 5 ≤ n := by omega
  obtain ⟨π, hπ⟩ := hN
  have hπinj : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFC.altDn_faithful hn5) hπ
  obtain ⟨-, -, -, -, -, hsec, -, β, -, hβker, hβeq⟩ := hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one β]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβker u).mp hu))
  intro x
  let u : ↥(⊤ : Subgroup W) := ⟨x, trivial⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  let f : Fin n → ZMod 2 := Multiplicative.toAdd (m : (FFModel.altDn n).Amb)
  obtain ⟨b, hb⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (n := p - 1)
    (by simpa [ZMod.card] using hn)
  have hlarge : p ≤ (Finset.univ.filter (fun i => f i = b)).card := by omega
  obtain ⟨s, hssub, hscard⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ.filter (fun i => f i = b)) (n := p) hlarge
  have hconst : ∀ i ∈ s, Multiplicative.toAdd (m : (FFModel.altDn n).Amb) i = b := by
    intro i hi
    exact (Finset.mem_filter.mp (hssub hi)).2
  obtain ⟨σ, -, -, hσord, hσA, hσfix⟩ :=
    s16k_exists_pcycle_fix (m := (m : (FFModel.altDn n).Amb)) hpPrime hpodd s hscard hconst
  let γ : (FFModel.altDn n).Gam := ⟨σ, hσA⟩
  have hγord : orderOf γ = p := by
    calc orderOf γ = orderOf σ := (Subgroup.orderOf_coe γ).symm
         _ = p := hσord
  have hmAct : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) ∈
      (FFModel.altDn n).sec := hsec γ m m.2
  have hRep : (⟨(FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb), hmAct⟩ :
      ↥((FFModel.altDn n).sec)) = m := by
    apply Subtype.ext
    exact hσfix
  have hβfix : β ⟨((π γ : ↥H) : MulAut W) x, trivial⟩ = β u := by
    calc β ⟨((π γ : ↥H) : MulAut W) x, trivial⟩ =
          QuotientGroup.mk ⟨(FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb), hmAct⟩ :=
          hβeq γ u m trivial hmAct hm.symm
      _ = QuotientGroup.mk m := congrArg QuotientGroup.mk hRep
      _ = β u := hm
  have hfix : ((π γ : ↥H) : MulAut W) x = x :=
    congrArg Subtype.val (hβinj hβfix)
  refine ⟨((π γ : ↥H) : MulAut W), (π γ).2, ?_, hfix⟩
  rw [Subgroup.orderOf_coe, orderOf_injective π hπinj γ]
  exact hγord

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
