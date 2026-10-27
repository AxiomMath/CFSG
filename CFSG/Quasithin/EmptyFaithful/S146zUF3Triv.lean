module

public import CFSG.Quasithin.EmptyFaithful.S146zUF3Seq
public import CFSG.Quasithin.EmptyFaithful.S145Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S146zU

namespace UF3

section Gen

variable {G : Type} [Group G]

theorem actH_eq_one_iff {V₁ IH H : Subgroup G} (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G))
    (x : ↥H) :
    actH hV₁ hIH x = 1 ↔ ∀ u ∈ IH, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ V₁ := by
  have hxu : ∀ u ∈ IH, (x : G) * u * (x : G)⁻¹ ∈ IH := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hIH x.2) u).mp hu
  constructor
  · intro h u hu
    have h1 := actH_tildeHom hV₁ hIH hIHN x ⟨u, hu⟩ ⟨_, hxu u hu⟩ rfl
    rw [h, MulAut.one_apply, tildeHom_eq_iff] at h1
    have h2 : u⁻¹ * ((x : G) * u * (x : G)⁻¹) ∈ V₁ := h1
    have h3 : u * (u⁻¹ * ((x : G) * u * (x : G)⁻¹)) * u⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hIHN hu) _).mp h2
    have e : u * (u⁻¹ * ((x : G) * u * (x : G)⁻¹)) * u⁻¹ = (x : G) * u * (x : G)⁻¹ * u⁻¹ := by
      group
    rwa [e] at h3
  · intro h
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.one_apply]
    obtain ⟨u, rfl⟩ := tildeHom_surjective hIHN w
    rw [actH_tildeHom hV₁ hIH hIHN x u ⟨_, hxu u u.2⟩ rfl, tildeHom_eq_iff]
    have hc := h (u : G) u.2
    have h3 : (u : G)⁻¹ * ((x : G) * (u : G) * (x : G)⁻¹ * (u : G)⁻¹)⁻¹ * (u : G)⁻¹⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hIHN (IH.inv_mem u.2)) _).mp (V₁.inv_mem hc)
    have e : ((x : G) * (u : G) * (x : G)⁻¹)⁻¹ * (u : G) =
        (u : G)⁻¹ * ((x : G) * (u : G) * (x : G)⁻¹ * (u : G)⁻¹)⁻¹ * (u : G)⁻¹⁻¹ := by group
    show ((x : G) * (u : G) * (x : G)⁻¹)⁻¹ * (u : G) ∈ V₁
    rw [e]
    exact h3

theorem le_normalizer_of_le_of_comm {U W : Subgroup G} (hWU : W ≤ U)
    (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) : U ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
    (hU a ha x (hWU hx)).symm)

end Gen

section Hyp

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem actH_eq_one_of_mem_pCoreOf (h : HypF91 T V L V₁ Vp H) {W J : Subgroup G}
    (hV₁W : V₁ ≤ W) (hJU : J ≤ conjClosure Vp H) (hWN : H ≤ Subgroup.normalizer (W : Set G))
    (hJN : H ≤ Subgroup.normalizer (J : Set G)) (hJW : J ≤ Subgroup.normalizer (W : Set G))
    {x : ↥H} (hx : (x : G) ∈ pCoreOf 2 H) : actH hWN hJN x = 1 := by
  rw [actH_eq_one_iff hWN hJN hJW]
  intro u hu
  have h1 := V₁.inv_mem (h.commutator_conjClosure_le u (hJU hu) x hx)
  have e : (u * (x : G) * u⁻¹ * (x : G)⁻¹)⁻¹ = (x : G) * u * (x : G)⁻¹ * u⁻¹ := by group
  rw [e] at h1
  exact hV₁W h1

theorem actH_eq_one_iff_mem_pCoreOf (h : HypF91 T V L V₁ Vp H)
    (hV₁N : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hUN : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G))
    (hUV : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G)) (x : ↥H) :
    actH hV₁N hUN x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  constructor
  · intro hx
    rw [actH_eq_one_iff hV₁N hUN hUV] at hx
    rw [h.pCoreOf_eq_centralizerMod]
    exact ⟨x.2, hV₁N x.2, hx⟩
  · exact actH_eq_one_of_mem_pCoreOf h le_rfl le_rfl hV₁N hUN hUV

end Hyp

section Setting

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem hypF91_mcOf (S : Setting146 G T M) :
    HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) :=
  (S.lemma_14_5_14 (S.isHz_iff.mpr S.isHTM_mcOf)).2.toHypF91

theorem isElemAbelian_uOfL22 (S : Setting146 G T M) : IsElemAbelian 2 (uOfL22 T M) :=
  S.lemma_14_5_15_two S.isHTM_mcOf

theorem uOfL22_le_normalizer_Z (S : Setting146 G T M) :
    uOfL22 T M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  ((hypF91_mcOf S).conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 (mcOf T))).trans
    (hypF91_mcOf S).H_normalizes_V₁

theorem uOfL22_le_normalizer_of_le (S : Setting146 G T M) {W : Subgroup G}
    (hWU : W ≤ uOfL22 T M) : uOfL22 T M ≤ Subgroup.normalizer (W : Set G) :=
  le_normalizer_of_le_of_comm hWU fun _ ha _ hb =>
    B2F.isElemAbelian_comm (isElemAbelian_uOfL22 S) ha hb

theorem isElemAbelian_tildeOf_of_le (S : Setting146 G T M) (W : Subgroup G) {J : Subgroup G}
    (hJU : J ≤ uOfL22 T M) : IsElemAbelian 2 (tildeOf W J) :=
  isElemAbelian_secImg (B2F.isElemAbelian_mono hJU (isElemAbelian_uOfL22 S))

theorem trivial_sections (S : Setting146 G T M) {W J : Subgroup G}
    (hZW : quasithinOmegaOneCenter T ≤ W) (hWJ : W ≤ J) (hJU : J ≤ uOfL22 T M)
    (hWN : mcOf T ≤ Subgroup.normalizer (W : Set G))
    (hJN : mcOf T ≤ Subgroup.normalizer (J : Set G)) {x : ↥(mcOf T)}
    (hx : (x : G) ∈ pCoreOf 2 (mcOf T)) : actH hWN hJN x = 1 :=
  actH_eq_one_of_mem_pCoreOf (hypF91_mcOf S) hZW hJU hWN hJN
    (hJU.trans (uOfL22_le_normalizer_of_le S (hWJ.trans hJU))) hx

theorem actH_Z_U_eq_one_iff (S : Setting146 G T M)
    (hZN : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (hUN : mcOf T ≤ Subgroup.normalizer (uOfL22 T M : Set G)) (x : ↥(mcOf T)) :
    actH hZN hUN x = 1 ↔ (x : G) ∈ pCoreOf 2 (mcOf T) :=
  actH_eq_one_iff_mem_pCoreOf (hypF91_mcOf S) hZN hUN (uOfL22_le_normalizer_Z S) x

end Setting

end UF3

end S146zU

end CFSG.Quasithin
