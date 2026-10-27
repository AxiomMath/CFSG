module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggFixLine_central_complement {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {ι : Type} {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x)
    (hF2 : Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) = 2)
    (hT : Module.finrank (ZMod p) ↥(ggFixLineT r s) = N - 1)
    {c : ↥(ggFixLineQ S)} (hc : c ∈ Subgroup.center ↥(ggFixLineQ S))
    (hc1 : c ≠ 1) (hcop : Nat.Coprime (orderOf c) p) : False := by
  classical
  let A : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range r ∪ Set.range s)
  let T : Submodule (ZMod p) V := ggFixLineT r s
  let ρ : A →* (↥T ≃ₗ[ZMod p] ↥T) :=
    (ggLinRestrictHom T).comp (Subgroup.inclusion (ggFixLine_A_le_stab S))
  have hinj : Function.Injective ρ := ggFixLine_restrict_injective S
  have hTprops := ggFixLine_T_props S
  have hTmem : ∀ g ∈ A, ∀ v : V, g v - v ∈ T := hTprops.1
  have hT' : Module.finrank (ZMod p) ↥T = N - 1 := hT
  haveI hι : Finite ι := S.finite_family
  haveI hfinV : Module.Finite (ZMod p) V := ggFixLine_finite s S.s_refl S.fix_H
  have hVdim : Module.finrank (ZMod p) V = N :=
    (ggFixLine_split S.odd S.five_le S.dvd S.dim_le S.indep S.pair S.r_form hF2).1
  have hTne : T ≠ ⊤ := by
    intro htop
    have hEq : Module.finrank (ZMod p) ↥T = Module.finrank (ZMod p) V := by
      rw [htop]; simp
    have h1 : Module.finrank (ZMod p) ↥T = N - 1 := hT'
    have h2 : Module.finrank (ZMod p) V = N := hVdim
    have h5 : 5 ≤ N := S.five_le
    omega
  obtain ⟨v, hvT⟩ : ∃ v : V, v ∉ T := by
    by_contra h
    push Not at h
    exact hTne (Submodule.eq_top_iff'.mpr h)
  have hcrange : c.val ∈ MonoidHom.range ρ := by
    change c.val ∈ ggFixLineQ S
    exact c.2
  obtain ⟨ĉ, hĉ⟩ : ∃ a : A, ρ a = c.val := hcrange
  have hcomm : ∀ a : A, ĉ * a = a * ĉ := by
    intro a
    apply hinj
    rw [map_mul, map_mul]
    have hmem : ρ a ∈ ggFixLineQ S := by
      change ρ a ∈ MonoidHom.range ρ
      exact ⟨a, rfl⟩
    have hcenter := (Subgroup.mem_center_iff.mp hc) (⟨ρ a, hmem⟩ : ↥(ggFixLineQ S))
    have hval := congrArg Subtype.val hcenter
    simpa [hĉ] using hval.symm
  let m : ℕ := orderOf c
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ m := (ZMod.natCast_eq_zero_iff m p).mp hzero
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop.symm hdvd
  have hcm : c ^ m = 1 := pow_orderOf_eq_one c
  have hcvalm : c.val ^ m = 1 := by
    have := congrArg Subtype.val hcm
    simpa using this
  have hĉm : ĉ ^ m = 1 := by
    apply hinj
    rw [map_pow, hĉ, hcvalm, map_one]
  have hcĉm : (ĉ : V ≃ₗ[ZMod p] V) ^ m = 1 := by
    rw [← Subgroup.coe_pow, hĉm]
    simp
  let W : Submodule (ZMod p) ↥T := LinearMap.ker ((c.val : ↥T →ₗ[ZMod p] ↥T) - 1)
  have hWmem : ∀ y : ↥T, y ∈ W ↔ c.val y = y := by
    intro y
    simp [W, sub_eq_zero]
  have hWinv : ∀ a ∈ ggFixLineQ S, ∀ w ∈ W, a w ∈ W := by
    intro a ha w hw
    rw [hWmem] at hw ⊢
    have hcenter := (Subgroup.mem_center_iff.mp hc) (⟨a, ha⟩ : ↥(ggFixLineQ S))
    have hval := congrArg Subtype.val hcenter
    have hval' : (a * c.val) w = (c.val * a) w := by
      simpa only [Subgroup.coe_mul] using congrArg (fun e : ↥T ≃ₗ[ZMod p] ↥T => e w) hval
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hval'
    calc c.val (a w) = a (c.val w) := hval'.symm
      _ = a w := by rw [hw]
  have hWbot : W = ⊥ := by
    rcases (ggFixLine_Q_absIrred S).1 W hWinv with h | h
    · exact h
    · exfalso
      apply hc1
      apply Subtype.ext
      apply LinearEquiv.ext
      intro y
      have hy : y ∈ W := by rw [h]; exact Submodule.mem_top
      simpa using (hWmem y).mp hy
  have hcapply : ∀ y : ↥T, (c.val y : V) = (ĉ : V ≃ₗ[ZMod p] V) y := by
    intro y
    rw [← hĉ]
    simp only [ρ, ggLinRestrictHom, MonoidHom.comp_apply]
    exact LinearEquiv.ofSubmodules_apply (ĉ : V ≃ₗ[ZMod p] V) _ y
  have hUdisj : ∀ x ∈ T, (ĉ : V ≃ₗ[ZMod p] V) x = x → x = 0 := by
    intro x hx hfix
    have hxW : (⟨x, hx⟩ : ↥T) ∈ W := by
      rw [hWmem]
      apply Subtype.ext
      rw [hcapply]
      exact hfix
    have hzero : (⟨x, hx⟩ : ↥T) = 0 := by
      rw [hWbot] at hxW
      simpa using hxW
    simpa using congrArg Subtype.val hzero
  let f : ℕ → V := fun i => ((ĉ : V ≃ₗ[ZMod p] V) ^ i) v
  let Ssum : V := ∑ i ∈ Finset.range m, f i
  let w : V := (m : ZMod p)⁻¹ • Ssum
  have hfS : (ĉ : V ≃ₗ[ZMod p] V) Ssum = Ssum := by
    have hstep : ∀ i ∈ Finset.range m,
        (ĉ : V ≃ₗ[ZMod p] V) (f i) = f (i + 1) := by
      intro i hi
      simp only [f, pow_succ', LinearEquiv.mul_apply]
    have hshift : ∑ i ∈ Finset.range m, f (i + 1) = ∑ i ∈ Finset.range m, f i := by
      have htel := Finset.sum_range_sub f m
      rw [Finset.sum_sub_distrib] at htel
      have hfm : f m = f 0 := by
        simp [f, hcĉm]
      rw [hfm, sub_self] at htel
      exact sub_eq_zero.mp htel
    calc (ĉ : V ≃ₗ[ZMod p] V) Ssum
        = ∑ i ∈ Finset.range m, (ĉ : V ≃ₗ[ZMod p] V) (f i) := by
            simp only [Ssum, map_sum]
      _ = ∑ i ∈ Finset.range m, f (i + 1) := Finset.sum_congr rfl hstep
      _ = ∑ i ∈ Finset.range m, f i := hshift
      _ = Ssum := rfl
  have hwfix : (ĉ : V ≃ₗ[ZMod p] V) w = w := by
    simp only [w, map_smul, hfS]
  have hwvT : w - v ∈ T := by
    have hwv : w - v = (m : ZMod p)⁻¹ • (Ssum - (m : ZMod p) • v) := by
      simp only [w, smul_sub, smul_smul, inv_mul_cancel₀ hm0, one_smul]
    have hterm : ∀ i ∈ Finset.range m, f i - v ∈ T := by
      intro i hi
      have hmemA : ((ĉ : V ≃ₗ[ZMod p] V) ^ i) ∈ A := by
        have h1 : ((ĉ ^ i : A) : V ≃ₗ[ZMod p] V) ∈ A := (ĉ ^ i).2
        rwa [Subgroup.coe_pow] at h1
      simpa only [f] using hTmem _ hmemA v
    have hsumT : Ssum - (m : ZMod p) • v ∈ T := by
      have hsplit : Ssum - (m : ZMod p) • v = ∑ i ∈ Finset.range m, (f i - v) := by
        rw [Finset.sum_sub_distrib]
        have hsumv : (∑ _i ∈ Finset.range m, v) = (m : ZMod p) • v := by
          rw [Finset.sum_const, Finset.card_range]
          exact (Nat.cast_smul_eq_nsmul (ZMod p) m v).symm
        rw [hsumv]
      rw [hsplit]
      exact T.sum_mem (fun i hi => hterm i hi)
    rw [hwv]
    exact T.smul_mem _ hsumT
  have hwne : w ≠ 0 := by
    intro hw0
    have hneg : -v ∈ T := by
      rw [hw0] at hwvT
      simpa using hwvT
    exact hvT (by simpa using T.neg_mem hneg)
  have hAfix : ∀ a : A, (a : V ≃ₗ[ZMod p] V) w = w := by
    intro a
    have h1 : (a : V ≃ₗ[ZMod p] V) w - w ∈ T := hTmem _ a.2 w
    have h2 : (ĉ : V ≃ₗ[ZMod p] V) ((a : V ≃ₗ[ZMod p] V) w - w)
        = (a : V ≃ₗ[ZMod p] V) w - w := by
      have hcoe : (ĉ : V ≃ₗ[ZMod p] V) * (a : V ≃ₗ[ZMod p] V)
          = (a : V ≃ₗ[ZMod p] V) * (ĉ : V ≃ₗ[ZMod p] V) := by
        have := congrArg (fun x : A => (x : V ≃ₗ[ZMod p] V)) (hcomm a)
        simpa using this
      have haw : (ĉ : V ≃ₗ[ZMod p] V) ((a : V ≃ₗ[ZMod p] V) w)
          = (a : V ≃ₗ[ZMod p] V) w := by
        have := congrArg (fun e : V ≃ₗ[ZMod p] V => e w) hcoe
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
        rw [this, hwfix]
      rw [map_sub, hwfix, haw]
    exact sub_eq_zero.mp (hUdisj _ h1 h2)
  have hwfixGen : w ∈ ggLinFix (Set.range r ∪ Set.range s) := by
    intro g hg
    exact hAfix ⟨g, Subgroup.subset_closure hg⟩
  rw [ggFixLine_fix_A S] at hwfixGen
  exact hwne (by simpa using hwfixGen)

end CFSG.StandardType

end
