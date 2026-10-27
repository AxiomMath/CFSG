module

public import CFSG.Milestones.ASVolI.F431.BF436U5B
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieStab
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LocalAnalysis.EvenBN.U5
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit

theorem burnsideF4m_F436U5_B_holds : burnsideF4m_F436U5_B := by
  intro E _ Gp M₁ M₂ hyp Tb hTb fb hfbT hgr
  haveI := hyp.finite
  haveI := hyp.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfb2 : fb * fb = 1 := hgr.2.1
  obtain ⟨K, fK, h, Ψ, a, h1, h2, hs⟩ := burnsideF4m_u5_exists_frob_conj hyp.toHypF_4_4g hgr
  have := h.finite
  set s : E := (a : E)⁻¹ * fb * a with hsdef
  set φ : hypPSU h 2 1 →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hrange : φ.range = Gp := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Ψ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hsφ : ∀ y, s * φ y * s⁻¹ = φ (fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) y) := hs
  have hFF : ∀ y, fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)
      (fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) y) = y := by
    intro y
    have e : fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) *
        fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) = 1 := by
      rw [← map_mul, CFSG.Quasithin.H13.F431.Un.OL5.fld5_bar_mul_self, map_one]
    have := congrArg (fun β : MulAut (hypPSU h 2 1) => β y) e
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ k ∈ M₁ ⊓ M₂, e = n * k := fun e => by
    obtain ⟨n, hn, k, hk, he⟩ := hyp.split e
    exact ⟨n, hn, k, hk, he⟩
  have hyam := (u5_yamStd (h := h)).isYAmalgamPair
  have hself1 : ∀ g : hypPSU h 2 1,
      g ∈ Subgroup.normalizer ((u5PtP h : Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) →
        g ∈ u5PtP h :=
    fun g hg => burnsideF4d_selfNorm hyam g (Subgroup.mem_normalizer_iff.mp hg)
  have hyam' : IsYAmalgamPair (hypProjUnitriangular h 2 1) (u5LnP h) (u5PtP h) := by
    refine ⟨hyam.1, hyam.2.1.symm, fun X => ?_⟩
    rw [hyam.2.2 X, or_comm]
  have hself2 : ∀ g : hypPSU h 2 1,
      g ∈ Subgroup.normalizer ((u5LnP h : Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) →
        g ∈ u5LnP h :=
    fun g hg => burnsideF4d_selfNorm hyam' g (Subgroup.mem_normalizer_iff.mp hg)
  have hsM1 : s ∈ M₁ := by
    have hN := burnsideF4m_mem_normalizer_of_act φ hφ hrange (P := u5PtP h)
      (fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)) hsφ
      (fun g hg => (CFSG.Quasithin.H13.F431.Un.OL5.fStab5_Pt h
        (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) g).2 hg) hFF
    rw [← h1] at hN
    have hsplit' : ∀ e : E, ∃ n ∈ Gp, ∃ k ∈ M₂ ⊓ M₁, e = n * k := fun e => by
      obtain ⟨n, hn, k, hk, he⟩ := hsplit e
      exact ⟨n, hn, k, ⟨hk.2, hk.1⟩, he⟩
    exact burnsideF4m_normalizer_inf_le (M₁ := M₂) hsplit' φ hφ hrange h1 hself1 hN
  have hsM2 : s ∈ M₂ := by
    have hN := burnsideF4m_mem_normalizer_of_act φ hφ hrange (P := u5LnP h)
      (fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)) hsφ
      (fun g hg => (CFSG.Quasithin.H13.F431.Un.OL5.fStab5_Ln h
        (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) g).2 hg) hFF
    rw [← h2] at hN
    exact burnsideF4m_normalizer_inf_le (M₁ := M₁) hsplit φ hφ hrange h2 hself2 hN
  have hs2 : s ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, hsdef]
    calc (a : E)⁻¹ * fb * a * ((a : E)⁻¹ * fb * a) = (a : E)⁻¹ * (fb * fb) * a := by group
      _ = 1 := by rw [hfb2]; group
  have hTb' : CFSG.QuasithinUnique.IsSylowTwoOf Tb (M₁ ⊓ M₂) := hTb
  obtain ⟨c, hc, hle⟩ := CFSG.Quasithin.F7.isSylowTwoOf_exists_conj_le hTb'
    ((Subgroup.zpowers_le (H := M₁ ⊓ M₂)).mpr ⟨hsM1, hsM2⟩)
    (CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow hs2)
  have hsc : s ∈ CFSG.Quasithin.conjSub c Tb := hle (Subgroup.mem_zpowers s)
  rw [CFSG.Quasithin.mem_conjSub] at hsc
  refine ⟨c⁻¹ * s * c, hsc, ⟨c⁻¹ * (a : E)⁻¹, by rw [hsdef]; group⟩, ?_⟩
  obtain ⟨v₀, t₀, x₀, ⟨hv1, hv2⟩, ht2, hx1, fv, ft, fx, hvv, ht3, r2, r3, r4, r5⟩ :=
    burnsideF4m_u5_sp_witness h
  set ψ : hypSU h 2 1 →* E :=
    (MulAut.conj c⁻¹).toMonoidHom.comp (φ.comp (hypProj h 2 1)) with hψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj c⁻¹).injective.comp (hφ.comp (burnsideF4m_u5_proj_injective h))
  have hψapp : ∀ g, ψ g = c⁻¹ * φ (hypProj h 2 1 g) * c := by
    intro g
    simp only [hψ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
  have hcG : ∀ {y : E}, y ∈ Gp → c⁻¹ * y * c ∈ Gp := by
    intro y hy
    have := hyp.normal.conj_mem y hy c⁻¹
    rwa [inv_inv] at this
  have hcM : ∀ {M : Subgroup E}, c ∈ M → ∀ {y : E}, y ∈ M → c⁻¹ * y * c ∈ M := by
    intro M hcM y hy
    exact M.mul_mem (M.mul_mem (M.inv_mem hcM) hy) hcM
  have hφP1 : ∀ g ∈ u5PtStab h, φ (hypProj h 2 1 g) ∈ Gp ⊓ M₁ := by
    intro g hg
    rw [h1]
    exact ⟨hypProj h 2 1 g, CFSG.Quasithin.H13.F431.Un.proj_mem_u5PtP_iff.2 hg, rfl⟩
  have hφP2 : ∀ g ∈ u5LnStab h, φ (hypProj h 2 1 g) ∈ Gp ⊓ M₂ := by
    intro g hg
    rw [h2]
    exact ⟨hypProj h 2 1 g, CFSG.Quasithin.H13.F431.Un.proj_mem_u5LnP_iff.2 hg, rfl⟩
  have hcent : ∀ g : hypSU h 2 1, fieldAut h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h) g = g →
      ψ g ∈ Subgroup.centralizer ({c⁻¹ * s * c} : Set E) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff, hψapp]
    have hcomm : s * φ (hypProj h 2 1 g) = φ (hypProj h 2 1 g) * s := by
      have := hsφ (hypProj h 2 1 g)
      rw [fieldP_apply, hg] at this
      calc s * φ (hypProj h 2 1 g) = s * φ (hypProj h 2 1 g) * s⁻¹ * s := by group
        _ = φ (hypProj h 2 1 g) * s := by rw [this]
    calc c⁻¹ * φ (hypProj h 2 1 g) * c * (c⁻¹ * s * c) =
        c⁻¹ * (φ (hypProj h 2 1 g) * s) * c := by group
      _ = c⁻¹ * (s * φ (hypProj h 2 1 g)) * c := by rw [hcomm]
      _ = c⁻¹ * s * c * (c⁻¹ * φ (hypProj h 2 1 g) * c) := by group
  refine ⟨ψ v₀, ψ t₀, ψ x₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩,
      hcent v₀ fv⟩
    · rw [hψapp]
      exact hcG (hφP1 v₀ hv1).1
    · rw [hψapp]
      exact hcM hc.1 (hφP1 v₀ hv1).2
    · rw [hψapp]
      exact hcM hc.2 (hφP2 v₀ hv2).2
  · refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, hcent t₀ ft⟩
    · rw [hψapp]
      exact hcG (hφP2 t₀ ht2).1
    · rw [hψapp]
      exact hcM hc.2 (hφP2 t₀ ht2).2
  · refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, hcent x₀ fx⟩
    · rw [hψapp]
      exact hcG (hφP1 x₀ hx1).1
    · rw [hψapp]
      exact hcM hc.1 (hφP1 x₀ hx1).2
  · rw [← map_mul, hvv, map_one]
  · rw [← map_pow, ht3, map_one]
  · have := congrArg ψ r2
    simpa only [map_mul, map_inv] using this
  · have := congrArg ψ r3
    simpa only [map_mul, map_inv] using this
  · have := congrArg ψ r4
    simpa only [map_mul, map_inv, map_pow, map_one] using this
  · intro h0
    apply r5
    apply hψinj
    simpa only [map_mul, map_inv, map_one] using h0

section F436

set_option linter.unusedSectionVars false


theorem burnsideF4m_F436U5_holds : burnsideF4m_F436U5 :=
  burnsideF4m_F436U5_of burnsideF4m_F436U5_A_holds burnsideF4m_F436U5_B_holds

theorem burnsideF4m_F_4_36 : F_4_36 :=
  burnsideF4m_F_4_36_of_U5 burnsideF4m_F436U5_holds

end F436

end CFSG.ASVolI
