module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormalizer
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormF4Desc
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideGe
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbientRefl
import CFSG.LocalAnalysis.StandardType.GGQ2ExcInsideMoved
import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawF4Norm
import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.GroupTheory.PermSixSylowThree
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.QTwoCav


namespace ExcCoordDatum

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .F4 L p}
  {T₀ : Subgroup (ModGL .F4 L)} (d : ExcCoordDatum S T₀ 0)
include d

theorem card_inf_eq_nine {R : Subgroup (ModGL .F4 L)} (hR : Nat.card R = 360)
    {k l : ExcRaw.Root 0} (hkl : k ≠ l)
    (hk : rootDiagUnit Tag.F4 (fun j => d.ζ ^ corootPair (d.γ k) (Pi.single j 1)) ∈ R)
    (hl : rootDiagUnit Tag.F4 (fun j => d.ζ ^ corootPair (d.γ l) (Pi.single j 1)) ∈ R) :
    Nat.card ↥(T₀ ⊓ R) = 9 := by
  classical
  have hT : Nat.card ↥T₀ = 81 := by
    have h : Nat.card ↥T₀ = Nat.card (ExcRaw.V 0) := Nat.card_congr d.coord.toEquiv
    rw [h, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rfl
  have : Finite ↥T₀ := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have : Finite ↥(T₀ ⊓ R) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : T₀ ⊓ R ≤ T₀))
  have hdvd : Nat.card ↥(T₀ ⊓ R) ∣ 9 := by
    have h1 : Nat.card ↥(T₀ ⊓ R) ∣ 81 := hT ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(T₀ ⊓ R) ∣ 360 := hR ▸ Subgroup.card_dvd_of_le inf_le_right
    simpa using Nat.dvd_gcd h1 h2
  obtain ⟨xk, hxkR, hxk⟩ : ∃ x : ↥T₀, (x : ModGL Tag.F4 L) ∈ R ∧
      d.coord (Additive.ofMul x) = ExcRaw.coroot 0 k := ⟨⟨_, d.coroot_mem k⟩, hk, d.coord_coroot k⟩
  obtain ⟨xl, hxlR, hxl⟩ : ∃ x : ↥T₀, (x : ModGL Tag.F4 L) ∈ R ∧
      d.coord (Additive.ofMul x) = ExcRaw.coroot 0 l := ⟨⟨_, d.coroot_mem l⟩, hl, d.coord_coroot l⟩
  have hmem : ∀ ab : ZMod 3 × ZMod 3,
      ((xk ^ ab.1.val * xl ^ ab.2.val : ↥T₀) : ModGL Tag.F4 L) ∈ T₀ ⊓ R := fun ab =>
    Subgroup.mem_inf.2 ⟨(xk ^ ab.1.val * xl ^ ab.2.val).2, by
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
      exact mul_mem (pow_mem hxkR _) (pow_mem hxlR _)⟩
  have hcoord : ∀ a b : ZMod 3, d.coord (Additive.ofMul (xk ^ a.val * xl ^ b.val)) =
      a • ExcRaw.coroot 0 k + b • ExcRaw.coroot 0 l := by
    intro a b
    rw [ofMul_mul, ofMul_pow, ofMul_pow, map_add, map_nsmul, map_nsmul, hxk, hxl,
      ← Nat.cast_smul_eq_nsmul (ZMod 3), ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
  have hinj : Function.Injective
      (fun ab : ZMod 3 × ZMod 3 => (⟨_, hmem ab⟩ : ↥(T₀ ⊓ R))) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : xk ^ a.val * xl ^ b.val = xk ^ a'.val * xl ^ b'.val :=
      Subtype.ext (congrArg Subtype.val h :)
    have h'' := congrArg (fun x => d.coord (Additive.ofMul x)) h'
    simp only [hcoord] at h''
    have h0 : (a - a') • ExcRaw.coroot 0 k + (b - b') • ExcRaw.coroot 0 l = 0 := by
      rw [sub_smul, sub_smul, sub_add_sub_comm, h'', sub_self]
    obtain ⟨ha, hb⟩ := ExcRaw.coroot_zero_linIndep hkl h0
    rw [sub_eq_zero] at ha hb
    rw [ha, hb]
  have hle : 9 ≤ Nat.card ↥(T₀ ⊓ R) := by
    have h := Nat.card_le_card_of_injective _ hinj
    simpa using h
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

end ExcCoordDatum


namespace ExcCoordDatum

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup .F4 L p}
  {T₀ : Subgroup (ModGL .F4 L)} (d : ExcCoordDatum S T₀ 0)
include d

theorem rootSL2_mem_rationalPoints (hS : NegLangTwo S) {c : Finset (ExcRaw.Root 0)}
    {k : ExcRaw.Root 0} (hk : k ∈ c) :
    rootSL2 .F4 L (d.γ k) WSL ∈ rootSpan Tag.F4 L (codeRoots d.γ c) ⊓ S.D.model := by
  refine ⟨rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (L := L) (d.isRoot k) WSL),
    Subgroup.commutator_le_self S.D.model
      (rootWeylSL2_mem_Γ_of_rho_neg S (Or.inl rfl) (by rw [hS.1, pow_one]) hS.2.1 (d.isRoot k)
        (hS.2.2 _ (d.isRoot k)))⟩
  rintro δ (rfl | rfl)
  · exact ⟨k, hk, Or.inl rfl⟩
  · exact ⟨k, hk, Or.inr rfl⟩

theorem rootSL2_not_mem_codeComponent (hS : NegLangTwo S) {c : Finset (ExcRaw.Root 0)}
    {H : Subgroup (ModGL .F4 L)} (e : ↥H ≃* Equiv.Perm (Fin 6))
    (hR : codeComponent S d.γ c = ⁅H, H⁆) (hQ : Nat.card ↥(T₀ ⊓ codeComponent S d.γ c) = 9)
    {k l : ExcRaw.Root 0} (hk : k ∈ c) (hl : l ∈ c) (hkl : k ≠ l) :
    rootSL2 .F4 L (d.γ k) WSL ∉ codeComponent S d.γ c := by
  intro hw
  have : CharP L 2 := hS.charP
  have hN := d.rootSL2_mem_normalizer hS k
  have hw2 : rootSL2 .F4 L (d.γ k) WSL * rootSL2 .F4 L (d.γ k) WSL = 1 :=
    rootWeylSL2_mul_self_of_charTwo (d.γ k)
  have hRH : codeComponent S d.γ c ≤ H := by
    rw [hR]
    exact Subgroup.commutator_le_self H
  have hor := CFSG.GroupTheory.PermSixSylowThree.commute_or_inv_of_sq_commute e
    (inf_le_right.trans hRH) hQ (hR ▸ hw)
    (fun y hy => Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hN y).1 (Subgroup.mem_inf.1 hy).1,
      mul_mem (mul_mem hw (Subgroup.mem_inf.1 hy).2) (inv_mem hw)⟩)
    (fun y _ => by rw [pow_two, hw2, one_mul, mul_one])
  have hconj : ∀ t : ↥T₀, d.coord (Additive.ofMul (ggConjAut T₀ hN t)) =
      ExcRaw.reflection 0 k (d.coord (Additive.ofMul t)) := by
    intro t
    rw [← d.ggLin_ggConjAut_rootSL2 hS k, ggLin_apply_ofMul]
  obtain ⟨xk, hxkR, hxk⟩ : ∃ x : ↥T₀, (x : ModGL Tag.F4 L) ∈ codeComponent S d.γ c ∧
      d.coord (Additive.ofMul x) = ExcRaw.coroot 0 k :=
    ⟨⟨_, d.coroot_mem k⟩, coroot_mem_codeComponent (Or.inl rfl) hS d hk, d.coord_coroot k⟩
  obtain ⟨xl, hxlR, hxl⟩ : ∃ x : ↥T₀, (x : ModGL Tag.F4 L) ∈ codeComponent S d.γ c ∧
      d.coord (Additive.ofMul x) = ExcRaw.coroot 0 l :=
    ⟨⟨_, d.coroot_mem l⟩, coroot_mem_codeComponent (Or.inl rfl) hS d hl, d.coord_coroot l⟩
  rcases hor with hcomm | hinv
  · have h1 : ggConjAut T₀ hN xk = xk := Subtype.ext (by
      rw [ggConjAut_apply, hcomm _ (Subgroup.mem_inf.2 ⟨xk.2, hxkR⟩), mul_inv_cancel_right])
    have h2 := hconj xk
    rw [h1, hxk, ExcRaw.reflection_apply, ExcRaw.root_coroot] at h2
    have h3 : (2 : ZMod 3) • ExcRaw.coroot 0 k + (0 : ZMod 3) • ExcRaw.coroot 0 l = 0 := by
      funext t
      have h4 := congrFun h2 t
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h4 ⊢
      linear_combination h4
    exact absurd (ExcRaw.coroot_zero_linIndep hkl h3).1 (by decide)
  · have h1 : ggConjAut T₀ hN xl = xl⁻¹ := Subtype.ext (by
      rw [ggConjAut_apply, hinv _ (Subgroup.mem_inf.2 ⟨xl.2, hxlR⟩), Subgroup.coe_inv])
    have h2 := hconj xl
    rw [h1, ofMul_inv, map_neg, hxl, ExcRaw.reflection_apply, ExcRaw.pairing_eq] at h2
    have h3 : (-(ExcRaw.pairing 0 k l : ZMod 3)) • ExcRaw.coroot 0 k +
        (2 : ZMod 3) • ExcRaw.coroot 0 l = 0 := by
      funext t
      have h4 := congrFun h2 t
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul,
        Pi.zero_apply] at h4 ⊢
      linear_combination (-1 : ZMod 3) * h4
    exact absurd (ExcRaw.coroot_zero_linIndep hkl h3).2 (by decide)

theorem exists_induce_of_mem_weyl (hS : NegLangTwo S) {c : Finset (ExcRaw.Root 0)}
    {H : Subgroup (ModGL .F4 L)} (e : ↥H ≃* Equiv.Perm (Fin 6))
    (hR : codeComponent S d.γ c = ⁅H, H⁆)
    (hwH : ∀ k ∈ c, rootSL2 .F4 L (d.γ k) WSL ∈ H)
    (hwR : ∀ k ∈ c, rootSL2 .F4 L (d.γ k) WSL ∉ codeComponent S d.γ c)
    {s : ExcRaw.V 0 ≃ₗ[ZMod 3] ExcRaw.V 0} (hs : s ∈ ExcRaw.weyl 0 c) :
    ∃ h ∈ H, ∃ hN : h ∈ Subgroup.normalizer (T₀ : Set (ModGL .F4 L)),
      ggLin (p := 3) d.coord (ggConjAut T₀ hN) = s ∧
        (h ∈ codeComponent S d.γ c ↔ LinearEquiv.det s = 1) := by
  have step : ∀ k ∈ c, ∀ y : ExcRaw.V 0 ≃ₗ[ZMod 3] ExcRaw.V 0,
      (∃ h ∈ H, ∃ hN : h ∈ Subgroup.normalizer (T₀ : Set (ModGL .F4 L)),
        ggLin (p := 3) d.coord (ggConjAut T₀ hN) = y ∧
          (h ∈ codeComponent S d.γ c ↔ LinearEquiv.det y = 1)) →
      ∃ h ∈ H, ∃ hN : h ∈ Subgroup.normalizer (T₀ : Set (ModGL .F4 L)),
        ggLin (p := 3) d.coord (ggConjAut T₀ hN) = ExcRaw.reflection 0 k * y ∧
          (h ∈ codeComponent S d.γ c ↔ LinearEquiv.det (ExcRaw.reflection 0 k * y) = 1) := by
    rintro k hk y ⟨h, hH, hN, hy, hiff⟩
    have hNk := d.rootSL2_mem_normalizer hS k
    refine ⟨rootSL2 .F4 L (d.γ k) WSL * h, mul_mem (hwH k hk) hH, mul_mem hNk hN, ?_, ?_⟩
    · have hmul : ggConjAut T₀ (mul_mem hNk hN) = ggConjAut T₀ hNk * ggConjAut T₀ hN :=
        MulEquiv.ext fun b => Subtype.ext (by
          rw [MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply, ggConjAut_apply]
          group)
      rw [hmul, map_mul, d.ggLin_ggConjAut_rootSL2 hS k, hy]
    · have hdet : LinearEquiv.det (ExcRaw.reflection 0 k * y) = -1 * LinearEquiv.det y :=
        (map_mul _ _ _).trans (congrArg (· * LinearEquiv.det y) (ExcRaw.det_reflection 0 k))
      have hu : ∀ u : (ZMod 3)ˣ, (-1 * u = 1 ↔ ¬ u = 1) := by decide
      have hmm := CFSG.GroupTheory.PermSixSylowThree.mul_mem_commutator_iff e (hwH k hk) hH
      rw [← hR] at hmm
      rw [hdet, hu, ← hiff, hmm]
      exact ⟨fun h' hh => hwR k hk (h'.2 hh),
        fun h' => ⟨fun hw' => absurd hw' (hwR k hk), fun hh => absurd hh h'⟩⟩
  unfold ExcRaw.weyl at hs
  induction hs using Subgroup.closure_induction_left with
  | one =>
    refine ⟨1, one_mem _, one_mem _, ?_, ⟨fun _ => map_one _, fun _ => one_mem _⟩⟩
    have h1 : ggConjAut T₀ (one_mem (Subgroup.normalizer (T₀ : Set (ModGL .F4 L)))) = 1 :=
      MulEquiv.ext fun b => Subtype.ext (by rw [ggConjAut_apply]; simp)
    rw [h1, map_one]
  | mul_left x hx y hy ih =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact step k (Finset.mem_coe.1 hk) y ih
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨k, hk, rfl⟩ := hx
    rw [show (ExcRaw.reflection 0 k)⁻¹ = ExcRaw.reflection 0 k from rfl]
    exact step k (Finset.mem_coe.1 hk) y ih

end ExcCoordDatum

theorem excF4NormB2 : ExcF4NormB2 := by
  intro L _ _ p S hS T₀ d c hc h4
  classical
  obtain ⟨e⟩ := d.nonempty_rationalPoints_equiv_perm hS hc.1 h4
  have hR := codeComponent_eq_commutator S d.γ
    (CFSG.GroupTheory.PermSixSylowThree.commutator_commutator_eq e)
  have hRH : codeComponent S d.γ c ≤ rootSpan Tag.F4 L (codeRoots d.γ c) ⊓ S.D.model := by
    rw [hR]
    exact Subgroup.commutator_le_self _
  have hother : ∀ k ∈ c, ∃ l ∈ c, l ≠ k := fun k _ => Finset.exists_mem_ne (by omega) k
  obtain ⟨k₀, hk₀⟩ : c.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨l₀, hl₀, hl₀k₀⟩ := hother k₀ hk₀
  have hQ : Nat.card ↥(T₀ ⊓ codeComponent S d.γ c) = 9 :=
    d.card_inf_eq_nine (by rw [hR]; exact CFSG.GroupTheory.PermSixSylowThree.card_commutator e)
      (Ne.symm hl₀k₀) (coroot_mem_codeComponent (Or.inl rfl) hS d hk₀)
      (coroot_mem_codeComponent (Or.inl rfl) hS d hl₀)
  have hwH : ∀ k ∈ c, rootSL2 .F4 L (d.γ k) WSL ∈
      rootSpan Tag.F4 L (codeRoots d.γ c) ⊓ S.D.model :=
    fun k hk => d.rootSL2_mem_rationalPoints hS hk
  have hwR : ∀ k ∈ c, rootSL2 .F4 L (d.γ k) WSL ∉ codeComponent S d.γ c := fun k hk => by
    obtain ⟨l, hl, hlk⟩ := hother k hk
    exact d.rootSL2_not_mem_codeComponent hS e hR hQ hk hl (Ne.symm hlk)
  apply le_antisymm
  · intro s hs
    have hsW : s ∈ ExcRaw.weyl 0 c :=
      d.map_ggAutomizer_codeComponent_le_weyl ExcRaw.rootSep_zero hc.1 hs
    refine ⟨hsW, ?_⟩
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨g, hgR, -, hgφ⟩ := mem_ggAutomizer_iff.1 hφ
    obtain ⟨h, hH, hN, hhs, hiff⟩ := d.exists_induce_of_mem_weyl hS e hR hwH hwR hsW
    have hφh : φ = ggConjAut T₀ hN := ggLin_injective d.coord hhs.symm
    have hx : h⁻¹ * g ∈ ⁅rootSpan Tag.F4 L (codeRoots d.γ c) ⊓ S.D.model,
        rootSpan Tag.F4 L (codeRoots d.γ c) ⊓ S.D.model⁆ := by
      refine CFSG.GroupTheory.PermSixSylowThree.mem_commutator_of_commute e
        (inf_le_right.trans hRH) hQ (mul_mem (inv_mem hH) (hRH hgR)) fun y hy => ?_
      have h1 := hgφ ⟨y, (Subgroup.mem_inf.1 hy).1⟩
      rw [hφh, ggConjAut_apply] at h1
      calc h⁻¹ * g * y = h⁻¹ * (g * y * g⁻¹) * g := by group
        _ = h⁻¹ * (h * y * h⁻¹) * g := by rw [← h1]
        _ = y * (h⁻¹ * g) := by group
    have hhR : h ∈ codeComponent S d.γ c := by
      rw [hR] at hgR ⊢
      have h2 := mul_mem hgR (inv_mem hx)
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h2
    exact MonoidHom.mem_ker.2 (hiff.1 hhR)
  · rintro s ⟨hsW, hdet⟩
    obtain ⟨h, -, hN, hhs, hiff⟩ := d.exists_induce_of_mem_weyl hS e hR hwH hwR hsW
    exact Subgroup.mem_map.2 ⟨ggConjAut T₀ hN,
      ggConjAut_mem_ggAutomizer (hiff.2 (MonoidHom.mem_ker.1 hdet)) hN, hhs⟩

theorem excF4NormRootWeyl : ExcF4NormRootWeyl := by
  intro L _ _ p S hS T₀ d c hc h4 i hi
  have nine : ∀ c' : Finset (ExcRaw.Root 0), (∃ U, ExcRaw.occurs 0 U c') → c'.card = 9 →
      ∀ i ∈ c', rootSL2 .F4 L (d.γ i) WSL ∈ codeComponent S d.γ c' := by
    intro c' hc' h9 i hi
    rw [codeComponent_eq_of_perfect S d.γ (d.commutator_rationalPoints_eq hS hc' h9)]
    exact d.rootSL2_mem_rationalPoints hS hi
  obtain ⟨U, hU⟩ := hc.1
  by_cases hU0 : U = ⊥
  · subst hU0
    have huniv := ExcRaw.eq_univ_of_occurs_bot hU
    obtain ⟨U', c', hic', h9, hocc⟩ := ExcRaw.exists_occurs_nine i
    refine codeComponent_mono S d.γ ?_ (nine c' ⟨U', hocc⟩ h9 i hic')
    rw [huniv]
    exact Finset.subset_univ c'
  · have hcard := d.card_of_occurs hS hU hU0
    have hne := ExcRaw.card_ne_of_admissible_zero hc
    exact nine c hc.1 (by omega) i hi

theorem excCoreNormalizer_F4 : ExcCoreNormalizer 0 .F4 :=
  excCoreNormalizer_F4_of_inputs excF4NormB2 excF4NormRootWeyl

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
