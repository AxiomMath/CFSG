module

public import CFSG.Quasithin.EmptyFaithful.S153E54G

public section

namespace CFSG.Quasithin

namespace S153E54

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.Om4Model
  CFSG.Quasithin.S153E CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Easy

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}

theorem I_eq_54 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂)
    {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) :
    Igp153 T M V₁ Mc g = Y153 Mc M ⊔ UH153 T M V₁ Mc := by
  have hyp := hyp54 h113 cx c
  have := hyp.G26_one hg (hgV_of_notOrth cx c hgZ)
  rwa [conjClosure_Zp_eq cx] at this

theorem g26_all (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂)
    {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) :
    (VZ T M ⊔ (UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g) ≤ Pgp153 T M V₁ Mc g) ∧
    (VZ T M ≤ centerOf (Pgp153 T M V₁ Mc g)) ∧
    (⁅VZ T M ⊔ (UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g), Igp153 T M V₁ Mc g⁆ ≤
      VZ T M) ∧
    ((Pgp153 T M V₁ Mc g : Subgroup G) : Set G) = (Wgp153 T M V₁ Mc g : Set G) *
      (conjSubgroup (Wgp153 T M V₁ Mc g) g : Set G) ∧
    Igp153 T M V₁ Mc g ≤ Subgroup.normalizer (Pgp153 T M V₁ Mc g : Set G) := by
  have hyp := hyp54 h113 cx c
  have hU : UH153 T M V₁ Mc = conjClosure (Zp54 T M V₁ Mc) Mc := (conjClosure_Zp_eq cx).symm
  have hgV := hgV_of_notOrth cx c hgZ
  have hVL := conjClosure_Z_Y h113 cx c
  obtain ⟨-, h32, h33, -, -, h36⟩ := hyp.G26_three hU hg hgV rfl
  have h4 := hyp.G26_four hU hg hgV rfl
  obtain ⟨-, hSset⟩ := hyp.G26_two (U := UH153 T M V₁ Mc)
    (I := UH153 T M V₁ Mc ⊔ rconj (UH153 T M V₁ Mc) g)
    (S := pCoreOf 2 (UH153 T M V₁ Mc ⊔ rconj (UH153 T M V₁ Mc) g))
    (W := UH153 T M V₁ Mc ⊓ pCoreOf 2 (UH153 T M V₁ Mc ⊔ rconj (UH153 T M V₁ Mc) g))
    hU hg hgV rfl rfl rfl
  rw [hVL] at h32 h33 h4
  exact ⟨h32, h33, h4, hSset, h36⟩

theorem relIndex_Zp (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    (Zp54 T M V₁ Mc).relIndex (VZ T M) = 2 := by
  obtain ⟨P, -, hQ, hU, -⟩ := c.h53two.perp
  have := c.h53two.card_Vstar
  rw [hQ] at this
  have e : Zp54 T M V₁ Mc = P := hU
  rw [e]
  exact this

theorem card_Zp (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) :
    Nat.card ↥(Zp54 T M V₁ Mc) = 8 := by
  have h1 := Subgroup.relIndex_mul_card (Zp54 T M V₁ Mc) (VZ T M)
  have e : Zp54 T M V₁ Mc ⊓ VZ T M = Zp54 T M V₁ Mc := inf_of_le_left inf_le_left
  rw [relIndex_Zp cx c, e, cx.c.hyp.card_VZ] at h1
  omega

theorem three_eq_54 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) :
    UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g =
      Wgp153 T M V₁ Mc g ⊓ conjSubgroup (Wgp153 T M V₁ Mc g) g := by
  obtain ⟨h1, -, -, -, h5⟩ := g26_all h113 cx c hg hgZ
  ext x
  constructor
  · intro hx
    have hxP : x ∈ Pgp153 T M V₁ Mc g := h1 (Subgroup.mem_sup_right hx)
    have hgI : g ∈ Igp153 T M V₁ Mc g := by
      rw [I_eq_54 h113 cx c hg hgZ]
      exact Subgroup.mem_sup_left hg
    refine ⟨⟨hx.1, hxP⟩, mem_conjSubgroup_iff.2 ⟨mem_conjSubgroup_iff.1 hx.2, ?_⟩⟩
    exact (Subgroup.mem_normalizer_iff.1 (h5 hgI) x).1 hxP
  · intro hx
    exact ⟨hx.1.1, mem_conjSubgroup_iff.2 (mem_conjSubgroup_iff.1 hx.2).1⟩

theorem isPerp_conj_54 (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15353 cx N₁ N₂) {g : G}
    (hg : g ∈ Y153 Mc M) :
    IsPerp153 cx.c (conjSubgroup (quasithinOmegaOneCenter T) g)
      (VZ T M ⊓ conjSubgroup (Zp54 T M V₁ Mc) g) := by
  have hgM : g ∈ M := Y153_le Mc M hg
  have hVn := cx.c.hyp.le_normalizer
  have hconjV : ∀ {y x : G}, y ∈ M → x ∈ VZ T M → y * x * y⁻¹ ∈ VZ T M := fun {y x} hy hx =>
    (Subgroup.mem_normalizer_iff.1 (hVn hy) x).1 hx
  have hperp := isPerp_Zp cx c
  have haV : ∀ a : G, g * a * g⁻¹ ∈ quasithinOmegaOneCenter T → a ∈ VZ T M := fun a ha => by
    have := hconjV (M.inv_mem hgM) (cx.c.hyp.Z_le_VZ ha)
    simpa [mul_assoc] using this
  intro v
  constructor
  · rintro ⟨hv, hv'⟩
    refine ⟨hv, fun a ha => ?_⟩
    have ha' : g * a * g⁻¹ ∈ quasithinOmegaOneCenter T := mem_conjSubgroup_iff.1 ha
    have hgv : g * v * g⁻¹ ∈ Zp54 T M V₁ Mc := mem_conjSubgroup_iff.1 hv'
    have h1 : Orth153 cx.c (g * a * g⁻¹) (g * v * g⁻¹) := ((hperp _).1 hgv).2 _ ha'
    exact (orth_conj cx hgM (haV a ha') hv (cx.c.hyp.Z_le_VZ ha') ((hperp _).1 hgv).1).1 h1
  · rintro ⟨hv, h⟩
    refine ⟨hv, mem_conjSubgroup_iff.2 ((hperp _).2 ⟨hconjV hgM hv, fun z' hz' => ?_⟩)⟩
    have ha : g⁻¹ * z' * g ∈ conjSubgroup (quasithinOmegaOneCenter T) g :=
      mem_conjSubgroup_iff.2 (by simpa [mul_assoc] using hz')
    have h1 := h _ ha
    have ha' : g * (g⁻¹ * z' * g) * g⁻¹ ∈ VZ T M := by
      have : g * (g⁻¹ * z' * g) * g⁻¹ = z' := by group
      rw [this]
      exact cx.c.hyp.Z_le_VZ hz'
    have haV' : g⁻¹ * z' * g ∈ VZ T M := haV _ (by simpa [mul_assoc] using hz')
    have := (orth_conj cx hgM haV' hv ha' (hconjV hgM hv)).2 h1
    have e : g * (g⁻¹ * z' * g) * g⁻¹ = z' := by group
    rwa [e] at this

theorem three_perp_54 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) :
    ∃ B₁ B₂ : Subgroup G, IsPerp153 cx.c (quasithinOmegaOneCenter T) B₁ ∧
      IsPerp153 cx.c (conjSubgroup (quasithinOmegaOneCenter T) g) B₂ ∧
      UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g = B₁ ⊓ B₂ := by
  have hgM : g ∈ M := Y153_le Mc M hg
  have hVn := cx.c.hyp.le_normalizer
  have hconjV : ∀ {y x : G}, y ∈ M → x ∈ VZ T M → y * x * y⁻¹ ∈ VZ T M := fun {y x} hy hx =>
    (Subgroup.mem_normalizer_iff.1 (hVn hy) x).1 hx
  refine ⟨Zp54 T M V₁ Mc, VZ T M ⊓ conjSubgroup (Zp54 T M V₁ Mc) g, isPerp_Zp cx c,
    isPerp_conj_54 cx c hg, ?_⟩
  have hXV := inf_le_V h113 cx c hg hgZ
  ext x
  constructor
  · intro hx
    have hxV : x ∈ VZ T M := hXV hx
    refine ⟨⟨hxV, hx.1⟩, hxV, mem_conjSubgroup_iff.2 ⟨hconjV hgM hxV, mem_conjSubgroup_iff.1 hx.2⟩⟩
  · rintro ⟨⟨hxV, hxU⟩, -, hx⟩
    exact ⟨hxU, mem_conjSubgroup_iff.2 (mem_conjSubgroup_iff.1 hx).2⟩

theorem three_klein_54 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) :
    IsKleinFour153 (UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g) := by
  have hV := cx.c.hyp.elemAbelian
  have hgM : g ∈ M := Y153_le Mc M hg
  have hVn := cx.c.hyp.le_normalizer
  have hconjV : ∀ {y x : G}, y ∈ M → x ∈ VZ T M → y * x * y⁻¹ ∈ VZ T M := fun {y x} hy hx =>
    (Subgroup.mem_normalizer_iff.1 (hVn hy) x).1 hx
  have hXV := inf_le_V h113 cx c hg hgZ
  obtain ⟨z, hz, hz1, hzgen⟩ := exists_Z_gen cx
  obtain ⟨-, hnZ2⟩ := not_orth_conj cx hg hgZ hz hzgen
  refine ⟨?_, fun a ha b hb => ?_, fun a ha => ?_⟩
  ·
    set A := Zp54 T M V₁ Mc with hA
    set B := conjSubgroup A g with hB
    have hAV : A ≤ VZ T M := inf_le_left
    have hBV : B ≤ VZ T M := fun y hy => by
      have := hconjV (M.inv_mem hgM) (hAV (mem_conjSubgroup_iff.1 hy))
      simpa [mul_assoc] using this
    have hA8 : Nat.card ↥A = 8 := card_Zp cx c
    have hB8 : Nat.card ↥B = 8 := by rw [card_conjSubgroup153, hA8]
    have hX : UH153 T M V₁ Mc ⊓ conjSubgroup (UH153 T M V₁ Mc) g = A ⊓ B := by
      ext x
      constructor
      · intro hx
        have hxV : x ∈ VZ T M := hXV hx
        exact ⟨⟨hxV, hx.1⟩, mem_conjSubgroup_iff.2 ⟨hconjV hgM hxV,
          mem_conjSubgroup_iff.1 hx.2⟩⟩
      · rintro ⟨⟨hxV, hxU⟩, hx⟩
        exact ⟨hxU, mem_conjSubgroup_iff.2 (mem_conjSubgroup_iff.1 hx).2⟩
    rw [hX]
    have hAi : A.relIndex (VZ T M) = 2 := relIndex_Zp cx c
    have hBi : B.relIndex (VZ T M) = 2 := by
      have h1 := Subgroup.relIndex_mul_card B (VZ T M)
      rw [inf_of_le_left hBV, hB8, cx.c.hyp.card_VZ] at h1
      omega
    have hle := Subgroup.relIndex_inf_le (H := A) (K := B) (L := VZ T M)
    have h2 := Subgroup.relIndex_mul_card (A ⊓ B) (VZ T M)
    rw [inf_of_le_left (inf_le_left.trans hAV), cx.c.hyp.card_VZ] at h2
    rw [hAi, hBi] at hle
    have hge : 4 ≤ Nat.card ↥(A ⊓ B) := by
      by_contra hlt
      push Not at hlt
      have hpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
      have : (A ⊓ B).relIndex (VZ T M) ≤ 4 := hle
      interval_cases h : Nat.card ↥(A ⊓ B) <;> omega
    have hdvd : Nat.card ↥(A ⊓ B) ∣ 8 := by
      rw [← hA8]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card ↥(A ⊓ B) ≠ 8 := by
      intro h8
      have hAB : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hA8])
      have hzA : z ∈ A := ⟨cx.c.hyp.Z_le_VZ hz, (Z_le_ZS cx).trans (ZS_le_U cx) hz⟩
      have hzB : z ∈ B := by
        have : z ∈ A ⊓ B := by rw [hAB]; exact hzA
        exact this.2
      have hgz : g * z * g⁻¹ ∈ A := mem_conjSubgroup_iff.1 hzB
      exact hnZ2 (((isPerp_Zp cx c _).1 hgz).2 z hz)
    have h4 : Nat.card ↥(A ⊓ B) = 4 := by
      have hle8 := Nat.le_of_dvd (by norm_num) hdvd
      generalize Nat.card ↥(A ⊓ B) = k at hdvd hne hge hle8 ⊢
      interval_cases k <;> omega
    exact h4
  · have ha' : a ∈ VZ T M := hXV ha
    have hb' : b ∈ VZ T M := hXV hb
    exact B2F.isElemAbelian_comm hV ha' hb'
  · exact F7.isElemAbelian_pow_eq_one hV (hXV ha)

theorem five_54 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    (c : Chain15353 cx N₁ N₂) {g : G} (hg : g ∈ Y153 Mc M) (hgZ : NotOrth153 cx.c g) :
    ⁅conjSubgroup (Wgp153 T M V₁ Mc g) g, UH153 T M V₁ Mc⁆ ≤ Wgp153 T M V₁ Mc g ∧
      conjSubgroup (Wgp153 T M V₁ Mc g) g ≤
        Subgroup.normalizer (UH153 T M V₁ Mc : Set G) := by
  obtain ⟨-, -, -, -, h5⟩ := g26_all h113 cx c hg hgZ
  have hI := I_eq_54 h113 cx c hg hgZ
  have hgI : g ∈ Igp153 T M V₁ Mc g := by
    rw [hI]
    exact Subgroup.mem_sup_left hg
  have hUI : UH153 T M V₁ Mc ≤ Igp153 T M V₁ Mc g := le_sup_left
  obtain ⟨-, -, hST, hINorm, -⟩ := sx_facts_gen (L := Y153 Mc M) (U := UH153 T M V₁ Mc)
    (I := Igp153 T M V₁ Mc g) hI (U_le_T cx) (T_le_normalizer_U cx) cx.hF.normalizes_L
    cx.hF.sylow_LT
  have hWgS : ∀ y ∈ conjSubgroup (Wgp153 T M V₁ Mc g) g, y ∈ Pgp153 T M V₁ Mc g := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ Pgp153 T M V₁ Mc g := (mem_conjSubgroup_iff.1 hy).2
    have := hINorm g⁻¹ ((Igp153 T M V₁ Mc g).inv_mem hgI) _ h1
    simpa [mul_assoc] using this
  have hnorm : conjSubgroup (Wgp153 T M V₁ Mc g) g ≤
      Subgroup.normalizer (UH153 T M V₁ Mc : Set G) := fun y hy => T_le_normalizer_U cx (hST (hWgS y hy))
  refine ⟨?_, hnorm⟩
  rw [Subgroup.commutator_le]
  intro y hy u hu
  have hyN : y * u * y⁻¹ ∈ UH153 T M V₁ Mc := (Subgroup.mem_normalizer_iff.1 (hnorm hy) u).1 hu
  have h1 : y * u * y⁻¹ * u⁻¹ ∈ UH153 T M V₁ Mc :=
    (UH153 T M V₁ Mc).mul_mem hyN ((UH153 T M V₁ Mc).inv_mem hu)
  have h2 : y * u * y⁻¹ * u⁻¹ ∈ Pgp153 T M V₁ Mc g := by
    have e : y * u * y⁻¹ * u⁻¹ = y * (u * y⁻¹ * u⁻¹) := by group
    rw [e]
    refine (Pgp153 T M V₁ Mc g).mul_mem (hWgS y hy) ?_
    exact hINorm u (hUI hu) y⁻¹ ((Pgp153 T M V₁ Mc g).inv_mem (hWgS y hy))
  exact ⟨h1, h2⟩

end Easy

end S153E54

end CFSG.Quasithin
