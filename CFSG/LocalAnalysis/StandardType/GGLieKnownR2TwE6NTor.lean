module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NDefs
public import CFSG.LieType.Steinberg.TwistedE6.RankOne

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Minuscule.MinData
open scoped commutatorElement

private theorem twE6t_exists_wt :
    ∃ w : Fin e6Data.d, e6Data.wt w (nd 2) = -1 ∧ e6Data.wt w (nd 4) = 0 := by
  decide

private theorem twE6t_endo_eval
    {k : Type} [Field k] {w : Fin e6Data.d} (hw2 : e6Data.wt w (nd 2) = -1)
    (hw4 : e6Data.wt w (nd 4) = 0) (s d : k) :
    e6Data_valid.endo k (e6Data_valid.xm k (Pi.single (nd 2) 1) s *
      e6Data_valid.xm k (Pi.single (nd 4) 1) d) (Finsupp.single w 1)
        (e6Data_valid.sRefl (nd 2) w) = s := by
  rw [e6Data_valid.endo_mul, Module.End.mul_apply,
    endo_single_of_mem_rankOne hw4 (Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k _ _)),
    e6Data_valid.endo_xm, ← e6Data_valid.blockOp_upper,
    e6Data_valid.blockOp_single_of_eq_neg_one k hw2]
  have hne := e6Data_valid.sRefl_ne_self (i := nd 2) (a := w) (by omega)
  simp [Finsupp.single_apply, hne]

theorem torusRegularAlpha3
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {t : kˣ} (ht : (t : k) ^ 2 ≠ 1) : TorusRegularAlpha3 θ := by
  intro y hy hfix
  have hne1 : rho (Pi.single (nd 2) 1) ≠ Pi.single (nd 2) 1 := by
    rw [rho_single]; decide
  have hp : proj (Pi.single (nd 2) 1) = Pi.single (2 : Fin 4) 1 := by rw [proj_single]; rfl
  obtain ⟨c, hc⟩ :=
    (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ (nd 2)) hp hne1 y).1 hy
  rw [twistSign_single, Int.cast_one, one_mul, rho_single,
    show rhoPerm (nd 2) = nd 4 from rfl] at hc
  have hH : hHatE k θ (nf 2) = (hPairE θ (nd 2) (nd 4)).range := rfl
  have htm : hPairE θ (nd 2) (nd 4) t ∈ hHatE k θ (nf 2) := hH ▸ ⟨t, rfl⟩
  let h : fixedGroup k θ := ⟨hPairE θ (nd 2) (nd 4) t, hHatE_le_fixedGroup θ hθ (nf 2) htm⟩
  have hh : h ∈ (⨆ i, hHat k θ i : Subgroup (fixedGroup k θ)) :=
    Subgroup.mem_iSup_of_mem (nf 2) (by
      rw [hHat, Subgroup.mem_subgroupOf]
      exact htm)
  have e := congrArg Subtype.val (hfix h hh)
  have hconj : ∀ (j : Fin (Tag.rank .E6)) (s : kˣ) (γ : Fin (Tag.rank .E6) → ℤ),
      IsRoot .E6 γ →
      ∀ (a b : k) (δ : Fin (Tag.rank .E6) → ℤ), IsRoot .E6 δ →
      e6Data_valid.hm k j s * (e6Data_valid.xm k γ a * e6Data_valid.xm k δ b) *
        (e6Data_valid.hm k j s)⁻¹ =
      e6Data_valid.xm k γ (((s ^ toWeight γ j : kˣ) : k) * a) *
        e6Data_valid.xm k δ (((s ^ toWeight δ j : kˣ) : k) * b) := by
    intro j s γ hγ a b δ hδ
    rw [← e6Data_valid.hm_conj_xm k hγ, ← e6Data_valid.hm_conj_xm k hδ]
    group
  change (hPairE θ (nd 2) (nd 4) t * (y : e6Data_valid.minGroup k) *
    (hPairE θ (nd 2) (nd 4) t)⁻¹) = y at e
  rw [hc] at e
  change e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map θ t) * _ *
    (e6Data_valid.hm k (nd 2) t * e6Data_valid.hm k (nd 4) (Units.map θ t))⁻¹ = _ at e
  rw [mul_inv_rev, show ∀ A B X : e6Data_valid.minGroup k, A * B * X * (B⁻¹ * A⁻¹) =
      A * (B * X * B⁻¹) * A⁻¹ from fun _ _ _ => by group,
    hconj _ _ _ (isRoot_single _ _) _ _ _ (isRoot_single _ _),
    hconj _ _ _ (isRoot_single _ _) _ _ _ (isRoot_single _ _)] at e
  obtain ⟨w, hw2, hw4⟩ := twE6t_exists_wt
  have e' := congrArg (fun g => e6Data_valid.endo k g (Finsupp.single w 1)
    (e6Data_valid.sRefl (nd 2) w)) e
  simp only [twE6t_endo_eval hw2 hw4] at e'
  have hw : toWeight (Pi.single (nd 2) 1 : Fin (Tag.rank .E6) → ℤ) (nd 2) = 2 ∧
      toWeight (Pi.single (nd 2) 1 : Fin (Tag.rank .E6) → ℤ) (nd 4) = 0 := by decide
  rw [hw.1, hw.2] at e'
  have hc0 : c = 0 := by
    have : ((t : k) ^ 2 - 1) * c = 0 := by
      simp only [zpow_zero, Units.val_one, one_mul, Units.val_zpow_eq_zpow_val] at e'
      rw [sub_mul, one_mul, sub_eq_zero]
      simpa using e'
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0) ht
    · exact h0
  refine Subtype.ext ?_
  rw [hc, hc0, map_zero, e6Data_valid.xm_zero, e6Data_valid.xm_zero, mul_one]
  rfl

end CFSG.StandardType.LieKnownR2.Short
