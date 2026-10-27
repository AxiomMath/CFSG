module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourOddDefs

import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourOddGroup
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourOddQuot
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourOddAct

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggTwE6SCFourNotTwoLocal_of_odd {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTwE6SCFourNotTwoLocalOdd R I) : GGTwE6SCFourNotTwoLocal R I := by
  intro L' _ _ ψ hs hk hc A hA hAI hcard hSC
  obtain ⟨K₂, hK₂le, hK₂p, hK₂all⟩ := SCFourOdd.exists_twoPart hk
  have hK₂c : K₂ ≤ Subgroup.center L' := hK₂le.trans hk
  haveI : K₂.Normal := Subgroup.normal_of_le_center hK₂c
  have hAK₂ : ∀ a ∈ A, ∀ z ∈ K₂, a z ∈ K₂ := by
    intro a ha z hz
    obtain ⟨φ, _, hφ⟩ := hAI a ha
    have hzker : z ∈ ψ.ker := hK₂le hz
    have hψz : ψ (a z) = 1 := by
      rw [← hφ z, MonoidHom.mem_ker.mp hzker, map_one]
    obtain ⟨k, hk⟩ := hK₂p ⟨z, hz⟩
    have hk' : z ^ 2 ^ k = 1 := by
      have := congrArg (Subtype.val) hk
      simpa using this
    exact hK₂all (a z) (MonoidHom.mem_ker.mpr hψz)
      ⟨k, by rw [← map_pow, hk', map_one]⟩
  obtain ⟨Φ, hΦ⟩ := SCFourOdd.exists_quotient_action A hAK₂
  have hinj : Function.Injective Φ :=
    SCFourOdd.injective_of_quotient_action hc hK₂c A Φ hΦ
  let ψ₀ : L' ⧸ K₂ →* R := QuotientGroup.lift K₂ ψ hK₂le
  let A₀ : Subgroup (MulAut (L' ⧸ K₂)) := Φ.range
  have hA₀ : IsElemAbelian 3 A₀ := by
    constructor
    · refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
      change (x : MulAut (L' ⧸ K₂)) * (y : MulAut (L' ⧸ K₂)) =
        (y : MulAut (L' ⧸ K₂)) * (x : MulAut (L' ⧸ K₂))
      rw [← ha, ← hb]
      show Φ a * Φ b = Φ b * Φ a
      rw [← map_mul, ← map_mul, hA.1.is_comm.comm a b]
    · intro x hx
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
      rw [← ha]
      have ha3 : a ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hA.2 a a.2)
      show Φ a ^ 3 = 1
      rw [← map_pow, ha3, map_one]
  have hAI₀ : ∀ a₀ ∈ A₀, ∃ φ ∈ I, ∀ l₀ : L' ⧸ K₂, φ (ψ₀ l₀) = ψ₀ (a₀ l₀) := by
    intro a₀ ha₀
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ha₀
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    refine ⟨φ, hφI, fun l₀ => ?_⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l₀
    rw [hΦ a l, QuotientGroup.lift_mk (φ := ψ) K₂ hK₂le ((a : MulAut L') l),
      QuotientGroup.lift_mk (φ := ψ) K₂ hK₂le l]
    exact hφ l
  have hcard₀ : Nat.card A₀ = 3 ^ 4 := by
    have h : Nat.card A₀ = Nat.card A := by
      change Nat.card Φ.range = Nat.card A
      rw [← Nat.card_range_of_injective hinj]
      rfl
    rw [h, hcard]
  have hSC₀ : GGTorusSelfCent 3 A₀ := by
    intro n₀ hn₀ hn₀3
    obtain ⟨n, ⟨hnn₀, hn3⟩, huniq⟩ := SCFourOdd.existsUnique_cube_lift hK₂c hK₂p hn₀3
    have hfix : ∀ a : A, (a : MulAut L') n = n := by
      intro a
      have h1 : (((a : MulAut L') n : L') : L' ⧸ K₂) = n₀ := by
        rw [← hΦ a n, hnn₀]
        exact hn₀ (Φ a) (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
      have h2 : ((a : MulAut L') n) ^ 3 = 1 := by rw [← map_pow, hn3, map_one]
      exact huniq ((a : MulAut L') n) ⟨h1, h2⟩
    have hmem : MulAut.conj n ∈ A := hSC n (fun a ha => hfix ⟨a, ha⟩) hn3
    refine MonoidHom.mem_range.mpr ⟨⟨MulAut.conj n, hmem⟩, ?_⟩
    ext l₀
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l₀
    rw [hΦ ⟨MulAut.conj n, hmem⟩ l, MulAut.conj_apply, MulAut.conj_apply,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hnn₀]
  have hmain := h (L' ⧸ K₂) ψ₀
    (SCFourOdd.lift_surjective ψ hs hK₂le)
    (SCFourOdd.lift_ker_le_center ψ hk hK₂le)
    (SCFourOdd.quotient_commutator_eq_top hc K₂)
    (SCFourOdd.odd_card_ker_lift ψ hK₂le hK₂p hK₂all)
    A₀ hA₀ hAI₀ hcard₀ hSC₀
  intro hVex
  obtain ⟨V, hVbot, hVp, hVinv⟩ := hVex
  have hV₀ : ∀ a₀ ∈ A₀, ∀ l₀ : L' ⧸ K₂, ψ₀ l₀ ∈ V → ψ₀ (a₀ l₀) ∈ V := by
    intro a₀ ha₀ l₀ hl₀
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp ha₀
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l₀
    have h1 : ψ₀ (l : L' ⧸ K₂) = ψ l := QuotientGroup.lift_mk (φ := ψ) K₂ hK₂le l
    have h2 : ψ₀ (Φ a (l : L' ⧸ K₂)) = ψ ((a : MulAut L') l) := by
      rw [hΦ a l, QuotientGroup.lift_mk (φ := ψ) K₂ hK₂le ((a : MulAut L') l)]
    rw [h2]
    exact hVinv a a.2 l (h1 ▸ hl₀)
  exact hmain ⟨V, hVbot, hVp, hV₀⟩

theorem ggTwE6ThreeSCFourNotTwoLocalInput_of_odd (h : GGTwE6ThreeSCFourNotTwoLocalOddInput) :
    GGTwE6ThreeSCFourNotTwoLocalInput :=
  fun K _ _ n hn hK hd => ggTwE6SCFourNotTwoLocal_of_odd (h K n hn hK hd)

end CFSG.StandardType
