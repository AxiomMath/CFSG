module

public import CFSG.Quasithin.EmptyFaithful.S153E56P7

public section

namespace CFSG.Quasithin

namespace S153E56p

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S153E CFSG.Quasithin.S153E57
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

section Bridge

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {s : ℕ} {y t₁ : G}
  (S : Ctx56 T Mc M V₁ V₂ t N₁ N₂ s y t₁)

include S

theorem mem_V0_iff {n : G} :
    n ∈ quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ↔
      ∃ z ∈ quasithinOmegaOneCenter T, ∃ z' ∈ conjSubgroup (quasithinOmegaOneCenter T) y,
        n = z * z' := by
  constructor
  · intro h
    have hcomm : ∀ z ∈ quasithinOmegaOneCenter T, ∀ z' ∈ conjSubgroup (quasithinOmegaOneCenter T) y,
        z * z' = z' * z := fun z hz z' hz' =>
      Z_comm_Mc S hz (U_le_Mc S (S.hG.Z'_le_U hz'))
    let K : Subgroup G :=
      { carrier := {n | ∃ z ∈ quasithinOmegaOneCenter T,
          ∃ z' ∈ conjSubgroup (quasithinOmegaOneCenter T) y, n = z * z'}
        one_mem' := ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨z₁, hz₁, z₁', hz₁', rfl⟩ ⟨z₂, hz₂, z₂', hz₂', rfl⟩
          refine ⟨z₁ * z₂, Subgroup.mul_mem _ hz₁ hz₂, z₁' * z₂', Subgroup.mul_mem _ hz₁' hz₂', ?_⟩
          have e := hcomm z₂ hz₂ z₁' hz₁'
          calc z₁ * z₁' * (z₂ * z₂') = z₁ * (z₁' * z₂) * z₂' := by group
            _ = z₁ * (z₂ * z₁') * z₂' := by rw [← e]
            _ = z₁ * z₂ * (z₁' * z₂') := by group
        inv_mem' := by
          rintro _ ⟨z, hz, z', hz', rfl⟩
          refine ⟨z⁻¹, Subgroup.inv_mem _ hz, z'⁻¹, Subgroup.inv_mem _ hz', ?_⟩
          have e := (Commute.inv_inv (show Commute z z' from hcomm z hz z' hz')).eq
          rw [mul_inv_rev, e] }
    have : quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤ K :=
      sup_le (fun z hz => ⟨z, hz, 1, Subgroup.one_mem _, by simp⟩)
        (fun z' hz' => ⟨1, Subgroup.one_mem _, z', hz', by simp⟩)
    exact this h
  · rintro ⟨z, hz, z', hz', rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hz')

theorem mem_tildeV0_iff {w : Gz T} :
    w ∈ tildeOf (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T ⊔
        conjSubgroup (quasithinOmegaOneCenter T) y) ↔
      w = 1 ∨ w = smk T ⟨zp S, Mc_le_NZ S.cx (U_le_Mc S (zp_mem_U S))⟩ := by
  constructor
  · intro h
    obtain ⟨n, hn, rfl⟩ := mem_tilde_iff.1 h
    obtain ⟨z, hz, z', hz', e⟩ := (mem_V0_iff S).1 hn
    have e1 : n = (⟨z, Subgroup.le_normalizer hz⟩ : ↥(NZ T)) *
        ⟨z', Mc_le_NZ S.cx (U_le_Mc S (S.hG.Z'_le_U hz'))⟩ := Subtype.ext e
    have e2 : smk T (⟨z, Subgroup.le_normalizer hz⟩ : ↥(NZ T)) = 1 := secMk_eq_one_iff.2 hz
    rw [e1, map_mul, e2, one_mul]
    rcases (mem_Z'_iff S).1 hz' with rfl | rfl
    · left
      rfl
    · right
      rfl
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact mem_tilde_iff.2 ⟨_, Subgroup.mem_sup_right (zp_mem S), rfl⟩

@[expose] def inE : ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)) →* Ut T M V₁ Mc :=
  Subgroup.inclusion (tilde_E_le_U S)

@[expose] def inE' : ↥(tildeOf (quasithinOmegaOneCenter T) (conjSubgroup (Egp153 T M V₁ Mc y) t₁)) →*
    Ut T M V₁ Mc := Subgroup.inclusion (tilde_E'_le_U S)

theorem inE_injective : Function.Injective (inE S) := Subgroup.inclusion_injective _

theorem inE'_injective : Function.Injective (inE' S) := Subgroup.inclusion_injective _

theorem mem_Et1_iff {q : Ut T M V₁ Mc} : q ∈ Et1 T M V₁ Mc y ↔ ∃ w, inE S w = q := by
  unfold Et1
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact ⟨⟨(q : Gz T), h⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    exact w.2

theorem mem_Et2_iff {q : Ut T M V₁ Mc} : q ∈ Et2 T M V₁ Mc y t₁ ↔ ∃ w, inE' S w = q := by
  unfold Et2
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact ⟨⟨(q : Gz T), h⟩, rfl⟩
  · rintro ⟨w, rfl⟩
    exact w.2

theorem inE_mem_Et1 (w : ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y))) :
    inE S w ∈ Et1 T M V₁ Mc y := (mem_Et1_iff S).2 ⟨w, rfl⟩

theorem inE'_mem_Et2 (w : ↥(tildeOf (quasithinOmegaOneCenter T)
    (conjSubgroup (Egp153 T M V₁ Mc y) t₁))) : inE' S w ∈ Et2 T M V₁ Mc y t₁ :=
  (mem_Et2_iff S).2 ⟨w, rfl⟩

theorem mem_autOn_X_iff {B : Subgroup G} (hBU : B ≤ UH153 T M V₁ Mc)
    (hXB : Xgp153 T M V₁ Mc y ≤ Subgroup.normalizer (B : Set G))
    (g : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) B)) :
    g ∈ autOn (tildeOf (quasithinOmegaOneCenter T) (Xgp153 T M V₁ Mc y))
        (tildeOf (quasithinOmegaOneCenter T) B) ↔
      ∃ (x : G) (hx : x ∈ Xgp153 T M V₁ Mc y), ∀ w : ↥(tildeOf (quasithinOmegaOneCenter T) B),
        ((g w : ↥(tildeOf (quasithinOmegaOneCenter T) B)) : Gz T) =
          ((rhoX S hx ⟨w, secImg_mono hBU w.2⟩ : Ut T M V₁ Mc) : Gz T) := by
  rw [mem_autOn_iff]
  constructor
  · rintro ⟨s', hs', rfl⟩
    obtain ⟨n, hnX, hn⟩ := mem_tilde_iff.1 hs'
    refine ⟨(n : G), hnX, fun w => ?_⟩
    rw [conjAct_apply_coe']
    have h1 := rho_apply_coe S.cx n ⟨w, secImg_mono hBU w.2⟩
    change _ = ((rho S.cx n ⟨w, secImg_mono hBU w.2⟩ : Ut T M V₁ Mc) : Gz T)
    rw [h1, ← hn]
  · rintro ⟨x, hx, hg⟩
    refine ⟨⟨smk T ⟨x, X_le_NZ S hx⟩, secMk_mem_normalizer_secImg (hXB hx)⟩,
      secMk_mem_secImg hx, ?_⟩
    ext w
    rw [conjAct_apply_coe']
    have h1 := rho_apply_coe S.cx ⟨x, X_le_NZ S hx⟩ ⟨w, secImg_mono hBU w.2⟩
    show _ = ((g w : ↥(tildeOf (quasithinOmegaOneCenter T) B)) : Gz T)
    rw [hg w]
    exact h1.symm

theorem tildeE_comm (a b : ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y))) :
    a * b = b * a :=
  Subtype.ext (B2F.isElemAbelian_comm S.cx.hF.isElemAbelian_tilde
    (secImg_mono (E_le_U S) a.2) (secImg_mono (E_le_U S) b.2))

theorem tildeE_sq (a : ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y))) : a * a = 1 := by
  apply Subtype.ext
  have := S.cx.hF.isElemAbelian_tilde.2 a (secImg_mono (E_le_U S) a.2)
  rw [pow_two] at this
  exact this

theorem X_transv_field : IsFullTransvGroup153
    (autOn (tildeOf (quasithinOmegaOneCenter T) (Xgp153 T M V₁ Mc y))
      (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)))
    ((tildeOf (quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T ⊔
        conjSubgroup (quasithinOmegaOneCenter T) y)).subgroupOf
      (tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y))) := by
  intro g
  rw [mem_autOn_X_iff S (E_le_U S) (X_le_normalizer_E S) g]
  constructor
  · rintro ⟨x, hx, hg⟩ w
    rw [Subgroup.mem_subgroupOf, mem_tildeV0_iff S]
    have h1 := rhoX_tr₁ S hx _ (inE_mem_Et1 S w)
    have h2 : ((g w * w⁻¹ : ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y))) : Gz T) =
        ((rhoX S hx (inE S w) : Ut T M V₁ Mc) : Gz T) * (w : Gz T)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hg w]
      rfl
    rw [h2]
    rcases h1 with h | h
    · left
      rw [h]
      exact mul_inv_cancel _
    · right
      rw [h]
      have hc := congrArg Subtype.val (Ut_comm S.cx (inE S w) (aa S))
      have h3 : ((inE S w * aa S : Ut T M V₁ Mc) : Gz T) = (w : Gz T) * (aa S : Gz T) := rfl
      rw [h3]
      have h4 : (w : Gz T) * (aa S : Gz T) = (aa S : Gz T) * (w : Gz T) := hc
      rw [h4, mul_assoc, mul_inv_cancel, mul_one]
      rfl
  · intro hg
    have hcomm := tildeE_comm S
    have hsq := tildeE_sq S
    let aE : ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)) :=
      ⟨smk T ⟨zp S, Mc_le_NZ S.cx (U_le_Mc S (zp_mem_U S))⟩, secMk_mem_secImg (zp_mem_E S)⟩
    have haE1 : aE ≠ 1 := fun h => zp_not_mem_Z S (secMk_eq_one_iff.1 (congrArg Subtype.val h))
    have H1 : ∀ w : ↥(tildeOf (quasithinOmegaOneCenter T) (Egp153 T M V₁ Mc y)),
        g w = w ∨ g w = w * aE := by
      intro w
      have h1 := hg w
      rw [Subgroup.mem_subgroupOf, mem_tildeV0_iff S] at h1
      have e1 : g w = (g w * w⁻¹) * w := by rw [inv_mul_cancel_right]
      rcases h1 with h | h
      · left
        have : g w * w⁻¹ = 1 := Subtype.ext h
        rw [e1, this, one_mul]
      · right
        have : g w * w⁻¹ = aE := Subtype.ext h
        rw [e1, this, hcomm]
    have H3 : g aE = aE := by
      rcases H1 aE with h | h
      · exact h
      · exfalso
        apply haE1
        have h1 : g aE = 1 := by rw [h, hsq]
        have h2 : g aE = g 1 := by rw [h1, map_one]
        exact g.injective h2
    let φ : Ut T M V₁ Mc → ZMod 2 := fun q => phi g (Function.invFun (inE S) q)
    have hφ : ∀ w, φ (inE S w) = phi g w := fun w => by
      simp only [φ]
      rw [Function.leftInverse_invFun (inE_injective S) w]
    have hadd : ∀ e ∈ Et1 T M V₁ Mc y, ∀ e' ∈ Et1 T M V₁ Mc y, φ (e * e') = φ e + φ e' := by
      intro e he e' he'
      obtain ⟨w, rfl⟩ := (mem_Et1_iff S).1 he
      obtain ⟨w', rfl⟩ := (mem_Et1_iff S).1 he'
      rw [← map_mul, hφ, hφ, hφ]
      exact phi_add hcomm hsq haE1 H1 w w'
    have hφa : φ (aa S) = 0 := by
      have : aa S = inE S aE := rfl
      rw [this, hφ, phi_eq_zero_iff]
      exact H3
    obtain ⟨x, hx, hρ⟩ := exists_rhoX S φ hadd hφa
    refine ⟨x, hx, fun w => ?_⟩
    have h1 := hρ (inE S w) (inE_mem_Et1 S w)
    rw [hφ] at h1
    show _ = ((rhoX S hx (inE S w) : Ut T M V₁ Mc) : Gz T)
    rw [h1]
    by_cases hgw : g w = w
    · rw [phi_eq_zero_iff.2 hgw, sm_zero, mul_one]
      exact congrArg Subtype.val hgw
    · rw [phi_eq_one_iff.2 hgw, sm_one]
      rcases H1 w with h | h
      · exact absurd h hgw
      · rw [h]
        rfl

end Bridge

end S153E56p

end CFSG.Quasithin
