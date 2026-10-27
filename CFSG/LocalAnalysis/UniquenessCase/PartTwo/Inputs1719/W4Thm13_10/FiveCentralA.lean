module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.A5MinDegreeSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenModOdd
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.Quasithin.Background.D2X1
public import CFSG.Quasithin.Background.OddCoprimeFixV

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem eq_one_of_commute_of_isAlt_five {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {N : Subgroup (MulAut W)} (hN : IsAlt ↥N 5)
    (hfixN : fixV N = ⊥) {t : MulAut W} (htN : t ∈ Subgroup.normalizer (N : Set (MulAut W)))
    (hnc : ∃ x ∈ N, t * x ≠ x * t) (htm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    {d : MulAut W} (hd5 : d ^ 5 = 1) (hdN : ∀ x ∈ N, d * x = x * d) : d = 1 := by
  obtain ⟨e⟩ := hN
  set α : MulAut ↥N := N.normalizerMonoidHom ⟨t, htN⟩ with hαdef
  have hαapp : ∀ n : ↥N, ((α n : ↥N) : MulAut W) = t * n * t⁻¹ := fun n =>
    N.normalizerMonoidHom_apply_apply_coe _ n
  have hα : α ≠ 1 := by
    intro h
    obtain ⟨x, hxN, hxne⟩ := hnc
    apply hxne
    have hx := hαapp ⟨x, hxN⟩
    rw [h, MulAut.one_apply] at hx
    calc t * x = (t * x * t⁻¹) * t := by group
      _ = x * t := by rw [← hx]
  obtain ⟨P', hP'2, hP'top⟩ := Inputs1719.exists_isPGroup_sup_map_eq_top_of_isAlt_five ⟨e⟩ hα
  set P : Subgroup (MulAut W) := P'.map N.subtype with hPdef
  have hP2 : IsPGroup 2 P := hP'2.map _
  have hPN : P ≤ N := Subgroup.map_subtype_le P'
  have hNeq : N = P ⊔ P.map (MulAut.conj t).toMonoidHom := by
    have hmap : (P'.map α.toMonoidHom).map N.subtype = P.map (MulAut.conj t).toMonoidHom := by
      rw [hPdef, Subgroup.map_map, Subgroup.map_map]
      congr 1
    calc N = (⊤ : Subgroup ↥N).map N.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = P ⊔ P.map (MulAut.conj t).toMonoidHom := by
          rw [← hP'top, Subgroup.map_sup, hmap]
  have hinf : fixV P ⊓ fixV (Subgroup.zpowers t) = ⊥ := by
    rw [eq_bot_iff, ← hfixN]
    intro w hw
    have hc : P ⊔ P.map (MulAut.conj t).toMonoidHom ≤
        centSub (fixV P ⊓ fixV (Subgroup.zpowers t)) := by
      refine sup_le ?_ ?_
      · intro p hp u hu
        exact (Subgroup.mem_inf.mp hu).1 p hp
      · rintro _ ⟨p, hp, rfl⟩ u hu
        obtain ⟨huP, hut⟩ := Subgroup.mem_inf.mp hu
        have hut' : t u = u := mem_fixV_zpowers_iff_apply.mp hut
        have hut'' : t⁻¹ u = u := by
          calc t⁻¹ u = t⁻¹ (t u) := by rw [hut']
            _ = u := MulAut.inv_apply_self _ t u
        show (t * p * t⁻¹) u = u
        simp only [MulAut.mul_apply]
        rw [hut'', huP p hp, hut']
    intro n hn
    exact (hc (hNeq ▸ hn)) w hw
  have hrkP : rk ↥(fixV P) ≤ 3 := by
    have h1 := rk_sup_add_rk_inf (fixV P) (fixV (Subgroup.zpowers t))
    rw [hinf, rk_bot] at h1
    have h2 := rk_mono (le_top : fixV P ⊔ fixV (Subgroup.zpowers t) ≤ ⊤)
    rw [rk_top] at h2
    have h3 := rk_add_rkIdx (fixV (Subgroup.zpowers t))
    omega
  by_contra hd1
  have hord : orderOf d = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime hd5 hd1
  have hdP : ∀ p ∈ P, d * p = p * d := fun p hp => hdN p (hPN hp)
  have hPz : ∀ p ∈ P, ∀ x ∈ Subgroup.zpowers d, p * x * p⁻¹ ∈ Subgroup.zpowers d := by
    intro p hp x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hk : p * d ^ k = d ^ k * p := ((Commute.zpow_left (hdP p hp) k)).symm.eq
    rw [hk, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers d k
  have hzP : ∀ x ∈ Subgroup.zpowers d, ∀ p ∈ P, x * p * x⁻¹ ∈ P := by
    intro x hx p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hk : d ^ k * p = p * d ^ k := (Commute.zpow_left (hdP p hp) k).eq
    rw [hk, mul_inv_cancel_right]
    exact hp
  have hzz : ∀ x ∈ Subgroup.zpowers d, ∀ y ∈ Subgroup.zpowers d,
      x * y * x⁻¹ ∈ Subgroup.zpowers d := fun x hx y hy =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx)
  set U₀ : Subgroup W := commSub ⊤ (Subgroup.zpowers d) ⊓ fixV P with hU₀
  have hstab : StableUnder (Subgroup.zpowers d) U₀ :=
    stableUnder_inf (stableUnder_commSub hzz (fun _ _ _ _ => Subgroup.mem_top _))
      (stableUnder_fixV hzP)
  have hmap : U₀.map d.toMonoidHom = U₀ := by
    have hle : U₀.map d.toMonoidHom ≤ U₀ := by
      rintro _ ⟨u, hu, rfl⟩
      exact hstab d (Subgroup.mem_zpowers d) u hu
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective d.injective])
  have hcop : U₀ ⊓ fixV (Subgroup.zpowers d) = ⊥ := by
    have h := commV_inf_fixV_eq_bot_of_odd_card hW (Subgroup.zpowers d)
      (by rw [Nat.card_zpowers, hord]; decide)
    rw [eq_bot_iff, ← h, commV_eq_commSub]
    exact inf_le_inf_right _ inf_le_left
  have hdvd := s16c167_prime_dvd_pow_rk hW Nat.prime_five hord hmap hcop
  have hne : commSub ⊤ (Subgroup.zpowers d) ≠ ⊥ := by
    intro h
    have h1 : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers d) := commSub_eq_bot_iff.mp h
    have hd1' : d = 1 := by
      ext w
      exact mem_fixV_zpowers_iff_apply.mp (h1 (Subgroup.mem_top w))
    rw [hd1', orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hpos : 0 < rk ↥U₀ :=
    rk_inf_fixV_pos_of_isPGroup_two hW hP2
      (stableUnder_commSub hPz (fun _ _ _ _ => Subgroup.mem_top _)) hne
  have hle3 : rk ↥U₀ ≤ 3 := (rk_mono inf_le_right).trans hrkP
  generalize rk ↥U₀ = r at hpos hle3 hdvd
  interval_cases r <;> norm_num at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10
