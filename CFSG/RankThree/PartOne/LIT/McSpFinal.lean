module

public import CFSG.RankThree.PartOne.LIT.McSpForm
public import CFSG.RankThree.PartOne.LIT.McMitchell

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical (IsTransvectionWith)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  (H : Subgroup (V ≃ₗ[ZMod p] V))

private theorem exists_dual_one_of_notMem' {W : Submodule (ZMod p) V} {x : V} (hx : x ∉ W) :
    ∃ f : Module.Dual (ZMod p) V, f x = 1 ∧ ∀ y ∈ W, f y = 0 := by
  obtain ⟨ψ, hψx, hψ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨(ψ x)⁻¹ • ψ, ?_, fun y hy => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψx]
  · have h : ψ y ∈ W.map ψ := Submodule.mem_map_of_mem hy
    rw [hψ, Submodule.mem_bot] at h
    rw [LinearMap.smul_apply, h, smul_zero]

theorem IsFrame.exists_mem_apply_eq_of_notMem_span {U L : Submodule (ZMod p) V}
    (hF : IsFrame H U L) {u u' : V} (hu : u ∈ U) (hu' : u' ∈ U) (hu0 : u ≠ 0)
    (hspan : u' ∉ Submodule.span (ZMod p) {u}) : ∃ t ∈ H, t u = u' := by
  have hc : u' - u ∈ U := U.sub_mem hu' hu
  have hnot : u ∉ L ⊔ Submodule.span (ZMod p) {u' - u} := by
    intro hmem
    obtain ⟨y, hyL, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hyU : y ∈ U := by
      have : y = u - s • (u' - u) := eq_sub_of_add_eq hyz
      rw [this]
      exact U.sub_mem hu (U.smul_mem s hc)
    have hy0 : y = 0 := Submodule.disjoint_def.mp hF.1.disjoint y hyU hyL
    rw [hy0, zero_add] at hyz
    by_cases hs : s = 0
    · rw [hs, zero_smul] at hyz
      exact hu0 hyz.symm
    · apply hspan
      refine Submodule.mem_span_singleton.mpr ⟨s⁻¹ * (1 + s), ?_⟩
      have h1 : s • u' = (1 + s) • u := by
        have h2 : s • (u' - u) = u := hyz
        rw [smul_sub] at h2
        rw [add_smul, one_smul]
        exact sub_eq_iff_eq_add.mp h2
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hs, one_smul]
  obtain ⟨f, hfu, hfW⟩ := exists_dual_one_of_notMem' hnot
  have hfL : ∀ l ∈ L, f l = 0 := fun l hl => hfW l (Submodule.mem_sup_left hl)
  have hfc : f (u' - u) = 0 :=
    hfW _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  obtain ⟨-, t, ht, htx⟩ := hF.2.2.2 (u' - u) hc f hfL hfc
  refine ⟨t, ht, ?_⟩
  rw [htx u, hfu, one_smul]
  abel

theorem IsFrame.exists_mem_apply_eq_smul {U L : Submodule (ZMod p) V} (hF : IsFrame H U L)
    {u : V} (hu : u ∈ U) (hu0 : u ≠ 0) {s : ZMod p} (hs : s ≠ 0) :
    ∃ g ∈ H, g u = s • u := by
  obtain ⟨w, hwU, hw⟩ : ∃ w ∈ U, w ∉ Submodule.span (ZMod p) {u} := by
    by_contra hno
    push Not at hno
    have h1 := Submodule.finrank_mono (show U ≤ Submodule.span (ZMod p) {u} from hno)
    rw [finrank_span_singleton hu0, hF.2.1] at h1
    omega
  have hw0 : w ≠ 0 := fun h0 => hw (h0 ▸ Submodule.zero_mem _)
  obtain ⟨t₁, ht₁, h₁⟩ := hF.exists_mem_apply_eq_of_notMem_span H hu hwU hu0 hw
  have hsw : s • u ∉ Submodule.span (ZMod p) {w} := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact smul_ne_zero hs hu0 hc.symm
    exact hw (Submodule.mem_span_singleton.mpr ⟨c⁻¹ * s, by
      rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩)
  obtain ⟨t₂, ht₂, h₂⟩ := hF.exists_mem_apply_eq_of_notMem_span H hwU (U.smul_mem s hu) hw0 hsw
  exact ⟨t₂ * t₁, H.mul_mem ht₂ ht₁, by rw [LinearEquiv.mul_apply, h₁, h₂]⟩

private theorem pow_apply_of_transvection {c : V ≃ₗ[ZMod p] V} {x : V}
    {f : Module.Dual (ZMod p) V} (hfx : f x = 0) (hc : ∀ z, c z = z + f z • x) (n : ℕ)
    (z : V) : (c ^ n) z = z + ((n : ZMod p) * f z) • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, hc (z + ((n : ZMod p) * f z) • x)]
    simp only [map_add, map_smul, hfx, smul_eq_mul]
    push_cast
    module

theorem transvection_mem_commutator {B : LinearMap.BilinForm (ZMod p) V} (hB : B.IsAlt)
    (hHB : ∀ g ∈ H, ∀ x y, B (g x) (g y) = B x y) {t g : V ≃ₗ[ZMod p] V} (ht : t ∈ H)
    (hg : g ∈ H) {x : V} {t₀ s : ZMod p} (htz : ∀ z, t z = z + (t₀ * B z x) • x)
    (hgx : g x = s • x) (hs : s ^ 2 - 1 ≠ 0) : t ∈ ⁅H, H⁆ := by
  have hxx : B x x = 0 := hB.self_eq_zero x
  have htinv : ∀ z, t⁻¹ z = z - (t₀ * B z x) • x := by
    intro z
    show t.symm z = _
    rw [LinearEquiv.symm_apply_eq, htz]
    simp only [LinearMap.map_sub₂, LinearMap.map_smul₂, hxx, smul_eq_mul, mul_zero, sub_zero]
    abel
  have hBg : ∀ w, B (g⁻¹ w) x = s * B w x := fun w => by
    have := hHB g hg (g⁻¹ w) x
    rw [show g (g⁻¹ w) = w from LinearEquiv.apply_symm_apply g w, hgx, map_smul,
      smul_eq_mul] at this
    exact this.symm
  have hc : ∀ z, (⁅g, t⁆ : V ≃ₗ[ZMod p] V) z = z + (((s ^ 2 - 1) * t₀) * B z x) • x := by
    intro z
    rw [commutatorElement_def]
    simp only [LinearEquiv.mul_apply]
    have hw : B (t⁻¹ z) x = B z x := by
      rw [htinv z]
      simp only [LinearMap.map_sub₂, LinearMap.map_smul₂, hxx, smul_eq_mul, mul_zero, sub_zero]
    rw [htz (g⁻¹ (t⁻¹ z)), map_add, map_smul, hgx, hBg, hw,
      show g (g⁻¹ (t⁻¹ z)) = t⁻¹ z from LinearEquiv.apply_symm_apply g _, htinv z]
    simp only [smul_smul]
    module
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod p) V, f = ((s ^ 2 - 1) * t₀) • B.flip x := ⟨_, rfl⟩
  have hfz : ∀ z, f z = ((s ^ 2 - 1) * t₀) * B z x := fun z => by
    rw [hf, LinearMap.smul_apply, LinearMap.BilinForm.flip_apply, smul_eq_mul]
  have hfx : f x = 0 := by rw [hfz, hxx, mul_zero]
  have hc' : ∀ z, (⁅g, t⁆ : V ≃ₗ[ZMod p] V) z = z + f z • x := fun z => by rw [hc z, hfz z]
  have hkc : (((s ^ 2 - 1)⁻¹ : ZMod p).val : ZMod p) * (s ^ 2 - 1) = 1 := by
    rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ hs]
  have hpow : (⁅g, t⁆ : V ≃ₗ[ZMod p] V) ^ ((s ^ 2 - 1)⁻¹ : ZMod p).val = t := by
    ext z
    rw [pow_apply_of_transvection hfx hc', htz z, hfz z]
    congr 2
    linear_combination (t₀ * B z x) * hkc
  rw [← hpow]
  exact Subgroup.pow_mem _ (Subgroup.commutator_mem_commutator hg ht) _

private theorem generators_nonempty [Module.Finite (ZMod p) V]
    (hdim : Module.finrank (ZMod p) V = 4)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    {S : Set (V ≃ₗ[ZMod p] V)} (hHS : H = Subgroup.closure S) : S.Nonempty := by
  by_contra hS0
  rw [Set.not_nonempty_iff_eq_empty] at hS0
  have hH : H = ⊥ := by rw [hHS, hS0, Subgroup.closure_empty]
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod p) (by rw [hdim]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  rcases hirr (Submodule.span (ZMod p) {x}) (fun h hh y hy => by
      rw [hH, Subgroup.mem_bot] at hh
      rw [hh]
      exact hy) with h | h
  · exact hx (Submodule.span_singleton_eq_bot.mp h)
  · have := finrank_span_singleton (K := ZMod p) hx
    rw [h, finrank_top, hdim] at this
    omega

theorem sp_branch [Module.Finite (ZMod p) V] (hp5 : 5 ≤ p)
    (hdim : Module.finrank (ZMod p) V = 4)
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hua : HasUniqueAxes H) :
    ∃ B : LinearMap.BilinForm (ZMod p) V, B.IsAlt ∧ B.Nondegenerate ∧
      ∀ g : V ≃ₗ[ZMod p] V, g ∈ H ↔ ∀ x y, B (g x) (g y) = B x y := by
  obtain ⟨U, L, hF⟩ := exists_frame H hdim hirr hgen
  obtain ⟨B, hB, hBnd, haxes⟩ := hua.exists_form H hdim hirr hgen hF
  refine ⟨B, hB, hBnd, ?_⟩
  obtain ⟨S, hS, hHS⟩ := hgen
  have hxx : ∀ x, B x x = 0 := fun x => hB.self_eq_zero x
  have hgenB : ∀ t ∈ S, t ∈ H ∧ ∃ (x : V) (h : Module.Dual (ZMod p) V) (t₀ : ZMod p),
      IsTransvectionWith t x h ∧ t₀ ≠ 0 ∧ ∀ z, t z = z + (t₀ * B z x) • x := by
    intro t ht
    have htH : t ∈ H := hHS ▸ Subgroup.subset_closure ht
    obtain ⟨x, h, hxh⟩ := hS t ht
    obtain ⟨t₀, ht₀⟩ := haxes x h (TrIn.of_isTransvectionWith htH hxh) hxh.1 hxh.2.1
    refine ⟨htH, x, h, t₀, hxh, ?_, fun z => by rw [hxh.2.2.2 z, ht₀ z]⟩
    rintro rfl
    exact hxh.2.1 (LinearMap.ext fun y => by rw [ht₀ y, zero_mul, LinearMap.zero_apply])
  have hHB : ∀ g ∈ H, ∀ x y, B (g x) (g y) = B x y := by
    intro g hg
    rw [hHS] at hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ x y, B (g x) (g y) = B x y)
      (fun t ht => ?_) (fun x y => rfl) (fun g₁ g₂ _ _ h₁ h₂ x y => ?_)
      (fun g _ hg x y => ?_) hg
    · obtain ⟨-, x₀, h, t₀, -, -, htz⟩ := hgenB t ht
      intro z w
      have hneg : -B x₀ w = B w x₀ := hB.neg_eq x₀ w
      rw [htz z, htz w]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hxx x₀]
      linear_combination (-(t₀ * B z x₀)) * hneg
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h₁, h₂]
    · have := hg (g⁻¹ x) (g⁻¹ y)
      rw [show g (g⁻¹ x) = x from LinearEquiv.apply_symm_apply g x,
        show g (g⁻¹ y) = y from LinearEquiv.apply_symm_apply g y] at this
      exact this.symm
  have hcomm : ⁅H, H⁆ = H := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_) ?_
    · rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)
    · calc H = Subgroup.closure S := hHS
        _ ≤ ⁅H, H⁆ := (Subgroup.closure_le _).mpr fun t ht => by
          obtain ⟨htH, x, h, t₀, hxh, -, htz⟩ := hgenB t ht
          obtain ⟨b, g, φ, hφ, hg, hφb, hga⟩ :=
            exists_partner H hirr ⟨S, hS, hHS⟩ hxh.1 hxh.2.1 (TrIn.of_isTransvectionWith htH hxh)
          have hF' := isFrame_of_reciprocal H hdim hφ hg hφb hga
          have hxU : x ∈ Submodule.span (ZMod p) {x, b} :=
            Submodule.subset_span (Set.mem_insert _ _)
          have h2 : (2 : ZMod p) ≠ 0 := by
            intro h0
            have h3 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
            rw [ZMod.natCast_eq_zero_iff] at h3
            have := Nat.le_of_dvd (by norm_num) h3
            omega
          have h3 : (2 : ZMod p) ^ 2 - 1 ≠ 0 := by
            have h4 : (2 : ZMod p) ^ 2 - 1 = ((3 : ℕ) : ZMod p) := by norm_num
            rw [h4, Ne, ZMod.natCast_eq_zero_iff]
            intro hd
            have := Nat.le_of_dvd (by norm_num) hd
            omega
          obtain ⟨g₀, hg₀, hg₀x⟩ := hF'.exists_mem_apply_eq_smul H hxU hxh.1 h2
          exact transvection_mem_commutator H hB hHB htH hg₀ htz hg₀x h3
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hcomm
  obtain ⟨t, htS⟩ := generators_nonempty H hdim hirr hHS
  obtain ⟨htH, x, h, t₀, hxh, ht₀, htz⟩ := hgenB t htS
  exact eq_isometries_of_perfect_irreducible (by omega) hdim B hB hBnd H hHB hirr hxh.1 ht₀
    ⟨t, htH, htz⟩

end CFSG.RankThree.PartOne.LIT
