module

public import CFSG.Quasithin.EmptyFaithful.S153E56P8

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Axis

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}
  (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem tildeE'_comm (a b : ↥(tildeOf (quasithinOmegaOneCenter T)
    (conjSubgroup (Egp153 T M V₁ Mc y) t₁))) : a * b = b * a :=
  Subtype.ext (B2F.isElemAbelian_comm S.cx.hF.isElemAbelian_tilde
    (secImg_mono (E'_le_U S) a.2) (secImg_mono (E'_le_U S) b.2))

theorem mem_centralizer_V0_iff {u : G} (hu : u ∈ conjSubgroup (Egp153 T M V₁ Mc y) t₁) :
    u ∈ Subgroup.centralizer ((quasithinOmegaOneCenter T ⊔
      conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G) ↔
      u * zp S = zp S * u := by
  have huMc : u ∈ Mc := U_le_Mc S (E'_le_U S hu)
  constructor
  · intro h
    exact (Subgroup.mem_centralizer_iff.1 h (zp S) (Subgroup.mem_sup_right (zp_mem S))).symm
  · intro h
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    obtain ⟨z, hz, z', hz', rfl⟩ := (mem_V0_iff S).1 hv
    have hzu : z * u = u * z := Z_comm_Mc S hz huMc
    have hz'u : z' * u = u * z' := by
      rcases (mem_Z'_iff S).1 hz' with rfl | rfl
      · simp
      · exact h.symm
    calc z * z' * u = z * (z' * u) := mul_assoc _ _ _
      _ = z * (u * z') := by rw [hz'u]
      _ = (z * u) * z' := (mul_assoc _ _ _).symm
      _ = (u * z) * z' := by rw [hzu]
      _ = u * (z * z') := mul_assoc _ _ _

theorem Z_le_E'C : quasithinOmegaOneCenter T ≤ conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
    Subgroup.centralizer ((quasithinOmegaOneCenter T ⊔
      conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G) := fun _ hz =>
  ⟨Z_le_E' S hz, Subgroup.mem_centralizer_iff.2 fun _ hv =>
    (Z_comm_Mc S hz (U_le_Mc S (V0_le_U S hv))).symm⟩

theorem mem_AxE'_iff (a : ↥(tildeOf (quasithinOmegaOneCenter T)
    (conjSubgroup (Egp153 T M V₁ Mc y) t₁))) :
    a ∈ (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
      Subgroup.centralizer ((quasithinOmegaOneCenter T ⊔
        conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G))).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)) ↔
      bet S.cx (inE' S a) (aa S) = 0 := by
  obtain ⟨n, hnE', hn⟩ := mem_tilde_iff.1 a.2
  have hnU : (n : G) ∈ UH153 T M V₁ Mc := E'_le_U S hnE'
  have hq : inE' S a = pi S.cx ⟨n, hnU⟩ := Subtype.ext hn.symm
  rw [Subgroup.mem_subgroupOf, ← hn, smk_mem_tilde_iff (Z_le_E'C S), hq, aa_eq, bet_pi S,
    comm153_eq_zero_iff, commutatorElement_eq_one_iff_mul_comm]
  constructor
  · rintro ⟨_, hc⟩
    exact (mem_centralizer_V0_iff S hnE').1 hc
  · intro h
    exact ⟨hnE', (mem_centralizer_V0_iff S hnE').2 h⟩

theorem X_axis_field_fix : IsFullAxisGroup153
    (autOn (tildeOf (quasithinOmegaOneCenter T) (Xgp153 T M V₁ Mc y))
      (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)))
    ((tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁ ⊓
      Subgroup.centralizer ((quasithinOmegaOneCenter T ⊔
        conjSubgroup (quasithinOmegaOneCenter T) y : Subgroup G) : Set G))).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁))) := by
  intro g
  rw [mem_autOn_X_iff S (E'_le_U S) (X_le_normalizer_E' S) g]
  have hsplit := split_model S
  obtain ⟨w₀, hw₀, hw₀a⟩ := exists_w₀ S
  obtain ⟨w₀', rfl⟩ := (mem_Et2_iff S).1 hw₀
  constructor
  · rintro ⟨x, hx, hg⟩
    have hOO := rhoX_isOO S hx
    have hfix := rhoX_fix_aa S hx
    have htr := rhoX_tr₁ S hx
    have key := fun w hw => hsplit.contra hOO hfix htr hw₀ hw₀a (w := w) hw
    have hcmem : rhoX S hx (inE' S w₀') * (inE' S w₀')⁻¹ ∈ Et2 T M V₁ Mc y t₁ :=
      (Et2 T M V₁ Mc y t₁).mul_mem (hOO.map₂ _ hw₀) ((Et2 T M V₁ Mc y t₁).inv_mem hw₀)
    have hca : bet S.cx (rhoX S hx (inE' S w₀') * (inE' S w₀')⁻¹) (aa S) = 0 :=
      hsplit.contra_perp hOO hfix
    have hgw : ∀ w, inE' S (g w) = rhoX S hx (inE' S w) := fun w => Subtype.ext (hg w)
    refine ⟨fun a ha => ?_, fun w => ?_⟩
    · have h1 := (mem_AxE'_iff S a).1 ha
      have h2 := key (inE' S a) (inE'_mem_Et2 S a)
      rw [h1, sm_zero, mul_one] at h2
      exact inE'_injective S ((hgw a).trans h2)
    · rw [mem_AxE'_iff S, map_mul, map_inv, hgw, hsplit.mul_inv_left]
      have h3 := hOO.iso (inE' S w) (aa S)
      rw [hfix] at h3
      rw [h3]
      exact zmod_two_add_self _
  · rintro ⟨ha, hw⟩
    have hc₀ : bet S.cx (inE' S (g w₀' * w₀'⁻¹)) (aa S) = 0 := (mem_AxE'_iff S _).1 (hw w₀')
    have hcE : inE' S (g w₀' * w₀'⁻¹) ∈ Et2 T M V₁ Mc y t₁ := inE'_mem_Et2 S _
    obtain ⟨x, hx, hρ⟩ := exists_rhoX S (fun q => bet S.cx (inE' S (g w₀' * w₀'⁻¹)) q)
      (fun e _ e' _ => hsplit.add_right _ e e') hc₀
    refine ⟨x, hx, fun w => ?_⟩
    have hOO := rhoX_isOO S hx
    have hfix := rhoX_fix_aa S hx
    have htr := rhoX_tr₁ S hx
    have hcx : rhoX S hx (inE' S w₀') * (inE' S w₀')⁻¹ = inE' S (g w₀' * w₀'⁻¹) := by
      refine hsplit.pair_ext ((Et2 T M V₁ Mc y t₁).mul_mem (hOO.map₂ _ hw₀)
        ((Et2 T M V₁ Mc y t₁).inv_mem hw₀)) hcE fun e he => ?_
      rw [hsplit.contra_pair hOO hfix htr e he, hw₀a, mul_one]
      have h := hρ e he
      by_cases h0 : bet S.cx (inE' S (g w₀' * w₀'⁻¹)) e = 0
      · rw [h0, sm_zero, mul_one] at h
        rw [h0]
        exact phi_eq_zero_iff.2 h
      · have h1 := zmod_two_eq_one h0
        rw [h1, sm_one] at h
        rw [h1]
        refine phi_eq_one_iff.2 fun hh => ?_
        have h2 : e * aa S = e := h.symm.trans hh
        exact aa_ne_one S (mul_eq_left.1 h2)
    have hform := hsplit.contra hOO hfix htr hw₀ hw₀a (w := inE' S w) (inE'_mem_Et2 S w)
    rw [hcx] at hform
    have hfinal : inE' S (g w) = inE' S w * sm (bet S.cx (inE' S w) (aa S)) (inE' S (g w₀' * w₀'⁻¹)) := by
      by_cases hb : bet S.cx (inE' S w) (aa S) = 0
      · have hmem := (mem_AxE'_iff S w).2 hb
        rw [ha w hmem, hb, sm_zero, mul_one]
      · have hb1 := zmod_two_eq_one hb
        rw [hb1, sm_one]
        have hmem := (mem_AxE'_iff S (w * w₀'⁻¹)).2 (by
          rw [map_mul, map_inv, hsplit.mul_inv_left, hb1, hw₀a]
          decide)
        have h1 := ha _ hmem
        rw [map_mul, map_inv] at h1
        have h2 : g w = w * (g w₀' * w₀'⁻¹) := by
          calc g w = (g w * (g w₀')⁻¹) * g w₀' := by rw [inv_mul_cancel_right]
            _ = (w * w₀'⁻¹) * g w₀' := by rw [h1]
            _ = w * (g w₀' * w₀'⁻¹) := by rw [mul_assoc, tildeE'_comm S w₀'⁻¹, ← mul_assoc]
        rw [h2, map_mul]
    show ((g w : ↥(tildeOf (quasithinOmegaOneCenter T)
      (conjSubgroup (Egp153 T M V₁ Mc y) t₁))) : Gz T) = ((rhoX S hx (inE' S w) : Ut T M V₁ Mc) : Gz T)
    rw [hform, ← hfinal]
    rfl

end Axis

end S153E56p

end CFSG.Quasithin
