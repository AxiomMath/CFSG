module

public import CFSG.Quasithin.Vol2.Ch10SecG31H
public import CFSG.Quasithin.Vol2.Ch10SecG31C

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.GroupTheory.GLnTwoSplitting CFSG.Open CFSG.Quasithin.ASInputs
open CFSG.Quasithin.Vol2.Ch10.SecD (mem_zpowers_iff_of_sq card_zpowers_of_sq map_zpowers_mulAut)

section Group

variable {G : Type*} [Group G]

theorem le_pCoreOf_two {N H : Subgroup G} (hNH : N ≤ H)
    (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hp : IsPGroup 2 N) : N ≤ pCoreOf 2 H := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNH (fun h hh => ?_) hp
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hnorm h hh n hn, fun hn => ?_⟩
  have := hnorm h⁻¹ (H.inv_mem hh) _ hn
  simpa [mul_assoc] using this

end Group

variable {V : Type} [CommGroup V]

omit [CommGroup V] in
theorem exists_ne_one_of_card_two {G : Type*} [Group G] {X : Subgroup G} (hX : Nat.card X = 2) :
    ∃ x ∈ X, x ≠ 1 := by
  by_contra! h
  have : X = ⊥ := (Subgroup.eq_bot_iff_forall X).2 h
  rw [this, Subgroup.card_bot] at hX
  omega

theorem eq_zpowers_of_card_two [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup V}
    (hX : Nat.card X = 2) {x : V} (hx : x ∈ X) (hx1 : x ≠ 1) : X = Subgroup.zpowers x := by
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx) ?_).symm
  rw [hX, card_zpowers_of_sq (hV x) hx1]

theorem eq_of_zpowers_eq (hV : ∀ v : V, v ^ 2 = 1) {a b : V} (ha : a ≠ 1)
    (h : Subgroup.zpowers a = Subgroup.zpowers b) : a = b := by
  have : a ∈ Subgroup.zpowers b := h ▸ Subgroup.mem_zpowers a
  rcases (mem_zpowers_iff_of_sq (hV b)).1 this with h1 | h1
  · exact absurd h1 ha
  · exact h1

variable [Module (ZMod 2) (Additive V)]

@[expose] def subE : Subgroup V ≃o Submodule (ZMod 2) (Additive V) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

theorem mem_subE {X : Subgroup V} {w : Additive V} : w ∈ subE X ↔ Additive.toMul w ∈ X := by
  rw [subE, OrderIso.trans_apply, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]

theorem subE_zpowers (hV : ∀ v : V, v ^ 2 = 1) (x : V) :
    subE (Subgroup.zpowers x) = Submodule.span (ZMod 2) {Additive.ofMul x} := by
  ext w
  rw [mem_subE, mem_zpowers_iff_of_sq (hV x), mem_span_singleton_iff_two]
  constructor
  · rintro (h | h)
    · left
      exact Additive.toMul.injective (by rw [h]; rfl)
    · right
      exact Additive.toMul.injective (by rw [h]; rfl)
  · rintro (rfl | rfl)
    · left
      rfl
    · right
      rfl

theorem subE_g31V [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Δ : Set (Subgroup V)}
    (hΔ : ∀ X ∈ Δ, Nat.card X = 2) : subE (g31V Δ) = Submodule.span (ZMod 2) (vecs Δ) := by
  rw [g31V, OrderIso.map_iSup₂]
  refine le_antisymm (iSup₂_le fun X hX => ?_) (Submodule.span_le.2 fun w hw => ?_)
  · obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_two (hΔ X hX)
    rw [eq_zpowers_of_card_two hV (hΔ X hX) hx hx1, subE_zpowers hV, Submodule.span_le,
      Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨hx1, ?_⟩
    show Subgroup.zpowers x ∈ Δ
    rw [← eq_zpowers_of_card_two hV (hΔ X hX) hx hx1]
    exact hX
  · refine (le_iSup₂ (f := fun X (_ : X ∈ Δ) => subE X) _ hw.2) ?_
    rw [subE_zpowers hV, ofMul_toMul]
    exact Submodule.mem_span_singleton_self w

theorem mem_g31V_iff [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Δ : Set (Subgroup V)}
    (hΔ : ∀ X ∈ Δ, Nat.card X = 2) {v : V} :
    v ∈ g31V Δ ↔ Additive.ofMul v ∈ Submodule.span (ZMod 2) (vecs Δ) := by
  rw [← subE_g31V hV hΔ, mem_subE]
  rfl

theorem natCard_eq_two_pow (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U] :
    Nat.card U = 2 ^ finrank (ZMod 2) U := by
  have := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := U), ZMod.card]

omit [CommGroup V] [Module (ZMod 2) (Additive V)] in
theorem transvection_comp_mem {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    {K : Subgroup (E ≃ₗ[ZMod 2] E)} {k : E ≃ₗ[ZMod 2] E} (hk : k ∈ K) {φ : Dual (ZMod 2) E}
    {d : E} (h : φ d = 0) (ht : LinearEquiv.transvection h ∈ K)
    (h' : (φ ∘ₗ (k : E →ₗ[ZMod 2] E)) (k.symm d) = 0) : LinearEquiv.transvection h' ∈ K := by
  have hm : k⁻¹ * LinearEquiv.transvection h * k⁻¹⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.inv_mem hk) ht) (K.inv_mem (K.inv_mem hk))
  rwa [mul_transvection_mul_inv k⁻¹ h (transvection_comp_apply_eq_zero k⁻¹ h)] at hm

theorem hyp_vecs (hV : ∀ v : V, v ^ 2 = 1) {Gm : Subgroup (MulAut V)} {Δ₀ : Set (Subgroup V)}
    (hinv : ∀ X ∈ Δ₀, ∀ g ∈ Gm, X.map (g : MulAut V).toMonoidHom ∈ Δ₀)
    (htrans : ∀ X ∈ Δ₀, ∀ Y ∈ Δ₀, ∃ g ∈ Gm, X.map (g : MulAut V).toMonoidHom = Y) :
    Hyp (Gm.map linAutHom) (vecs Δ₀) (forms Gm) := by
  refine ⟨fun w hw h0 => hw.1 (by rw [h0]; rfl), fun w _ φ hφ => hφ.1, fun w _ φ hφ h => hφ.2,
    ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ w hw
    refine ⟨?_, ?_⟩
    · rw [linAutHom_apply]
      simpa using hw.1
    · rw [linAutHom_apply, toMul_ofMul, ← map_zpowers_mulAut]
      exact hinv _ hw.2 g hg
  · rintro _ ⟨g, hg, rfl⟩ w hw φ
    have hk : linAutHom g ∈ Gm.map linAutHom := ⟨g, hg, rfl⟩
    constructor
    · rintro ⟨h, ht⟩
      have h' : (φ ∘ₗ (linAutHom g : Additive V →ₗ[ZMod 2] Additive V)) w = 0 := h
      refine ⟨h', ?_⟩
      have := transvection_comp_mem hk h ht (by simpa using h)
      rwa [transvection_congr rfl ((linAutHom g).symm_apply_apply w) _ h'] at this
    · rintro ⟨h, ht⟩
      have h' : φ (linAutHom g w) = 0 := h
      refine ⟨h', ?_⟩
      have hc : ((φ ∘ₗ (linAutHom g : Additive V →ₗ[ZMod 2] Additive V)) ∘ₗ
          (((linAutHom g)⁻¹ : Additive V ≃ₗ[ZMod 2] Additive V) :
            Additive V →ₗ[ZMod 2] Additive V)) ((linAutHom g)⁻¹.symm w) = 0 := by
        show φ (linAutHom g ((linAutHom g)⁻¹ (linAutHom g w))) = 0
        rw [show (linAutHom g)⁻¹ (linAutHom g w) = w from (linAutHom g).symm_apply_apply w]
        exact h'
      have := transvection_comp_mem (Subgroup.inv_mem _ hk) h ht hc
      have hf : (φ ∘ₗ (linAutHom g : Additive V →ₗ[ZMod 2] Additive V)) ∘ₗ
          (((linAutHom g)⁻¹ : Additive V ≃ₗ[ZMod 2] Additive V) :
            Additive V →ₗ[ZMod 2] Additive V) = φ := by
        ext v
        show φ (linAutHom g ((linAutHom g)⁻¹ v)) = φ v
        rw [show linAutHom g ((linAutHom g)⁻¹ v) = v from (linAutHom g).apply_symm_apply v]
      rwa [transvection_congr hf rfl hc h'] at this
  · intro w hw w' hw'
    obtain ⟨g, hg, hgX⟩ := htrans _ hw.2 _ hw'.2
    refine ⟨linAutHom g, ⟨g, hg, rfl⟩, ?_⟩
    rw [map_zpowers_mulAut] at hgX
    have := eq_of_zpowers_eq hV (fun h => hw.1 ((MulEquiv.map_eq_one_iff g).1 h)) hgX
    rw [linAutHom_apply, this, ofMul_toMul]

theorem O2_of_pCoreOf {Gm : Subgroup (MulAut V)} (hO2 : pCoreOf 2 Gm = ⊥)
    (N : Subgroup (Additive V ≃ₗ[ZMod 2] Additive V)) (hN : N ≤ Gm.map linAutHom)
    (hnorm : ∀ k ∈ Gm.map linAutHom, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (h4 : ∀ n ∈ N, n ^ 4 = 1) :
    N = ⊥ := by
  have hle : N.comap linAutHom ⊓ Gm ≤ pCoreOf 2 Gm := by
    refine le_pCoreOf_two inf_le_right (fun h hh n hn => ⟨?_,
      Gm.mul_mem (Gm.mul_mem hh hn.2) (Gm.inv_mem hh)⟩) ?_
    · show linAutHom (h * n * h⁻¹) ∈ N
      rw [map_mul, map_mul, map_inv]
      exact hnorm _ ⟨h, hh, rfl⟩ _ hn.1
    · rintro ⟨n, hn⟩
      refine ⟨2, Subtype.ext (linAutHom_injective ?_)⟩
      simp only [Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
      exact h4 _ hn.1
  rw [hO2] at hle
  refine (Subgroup.eq_bot_iff_forall N).2 fun n hn => ?_
  obtain ⟨g, hg, rfl⟩ := hN hn
  have hg1 : g ∈ (⊥ : Subgroup (MulAut V)) := hle ⟨hn, hg⟩
  rw [Subgroup.mem_bot] at hg1
  rw [hg1, map_one]

theorem map_g31G [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Gm : Subgroup (MulAut V)}
    {Δ : Set (Subgroup V)} (hΔ : ∀ X ∈ Δ, Nat.card X = 2) :
    (g31G Gm Δ).map linAutHom = Subgroup.closure (gens (vecs Δ) (forms Gm)) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun X hX g hg => ?_
    obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_two (hΔ X hX)
    have hXx := eq_zpowers_of_card_two hV (hΔ X hX) hx hx1
    rw [hXx] at hg
    obtain ⟨hgm, φ, h, he⟩ := (mem_transvGroup_zpowers_iff hV hx1).1 hg
    show linAutHom g ∈ Subgroup.closure (gens (vecs Δ) (forms Gm))
    rw [he]
    exact Subgroup.subset_closure ⟨Additive.ofMul x, ⟨hx1, hXx ▸ hX⟩, φ,
      ⟨h, he ▸ ⟨g, hgm, rfl⟩⟩, h, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro t ⟨w, hw, φ, ⟨h, g, hg, hgt⟩, h', rfl⟩
    refine ⟨g, ?_, hgt⟩
    have hgX : g ∈ transvGroup Gm (Subgroup.zpowers (Additive.toMul w)) :=
      (mem_transvGroup_zpowers_iff hV hw.1).2 ⟨hg, φ, h, hgt⟩
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hw.2 hgX)

theorem card_transvGroup [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Gm : Subgroup (MulAut V)}
    {x : V} (hx1 : x ≠ 1) : Nat.card (transvGroup Gm (Subgroup.zpowers x)) =
      2 ^ finrank (ZMod 2) (forms Gm (Additive.ofMul x)) := by
  have hx' : Additive.ofMul x ≠ 0 := by simpa using hx1
  have : Finite (Dual (ZMod 2) (Additive V)) := Module.finite_of_finite (ZMod 2)
  rw [← natCard_eq_two_pow (forms Gm (Additive.ofMul x)),
    ← Subgroup.card_map_of_injective (f := linAutHom)
    linAutHom_injective]
  symm
  refine Nat.card_eq_of_bijective (fun φ => ⟨LinearEquiv.transvection (mem_forms.1 φ.2).1, ?_⟩)
    ⟨fun φ ψ hφψ => ?_, fun t => ?_⟩
  · obtain ⟨h, g, hg, hgt⟩ := φ.2
    exact ⟨g, (mem_transvGroup_zpowers_iff hV hx1).2 ⟨hg, φ, h, hgt⟩, hgt⟩
  · refine Subtype.ext (LinearMap.ext fun w => smul_left_injective (ZMod 2) hx' ?_)
    have := LinearEquiv.congr_fun (congrArg Subtype.val hφψ) w
    rw [transvection_apply, transvection_apply] at this
    exact add_left_cancel this
  · obtain ⟨t, g, hg, rfl⟩ := t
    obtain ⟨hgm, φ, h, he⟩ := (mem_transvGroup_zpowers_iff hV hx1).1 hg
    exact ⟨⟨φ, h, he ▸ ⟨g, hgm, rfl⟩⟩, Subtype.ext he.symm⟩

end CFSG.Quasithin.G31
