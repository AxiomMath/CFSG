module

public import CFSG.Quasithin.AppendixH.H16.ConjNat
public import CFSG.Quasithin.AppendixH.H16.Transport

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Open

@[expose] def H162Z {V : Type*} [CommGroup V] (ρ : ↥M24g →* MulAut V) (Q : V → ZMod 2)
    (V₅ : Subgroup V) (KO : Subgroup S24) (z : S24) : Prop :=
  (rk ↥(fixV (rImg ρ (Subgroup.zpowers z)) ⊔ V₅) = 8 ∧
      ∀ x ∈ fixV (rImg ρ (Subgroup.zpowers z)) ⊔ V₅, Q x = 0) ∧
    cenM ρ (fixV (rImg ρ (Subgroup.zpowers z))) = (Subgroup.zpowers z).subgroupOf M24g ∧
    (rk ↥(V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))) = 4 ∧
      IsE2k 4 ((cenM ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))).map M24g.subtype) ∧
      pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z} : Set S24)) =
        KO ⊔ (cenM ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))).map M24g.subtype ∧
      ∀ element ∈ pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z} : Set S24)),
        ∃ kernelElement ∈ KO,
          ∃ centralizerElement ∈
            (cenM ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))).map M24g.subtype,
            element = kernelElement * centralizerElement) ∧
    (∀ B : Subgroup S24, z ∈ B →
      B ≤ (cenM ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))).map M24g.subtype →
        rk ↥(fixV (rImg ρ B)) = 8 - rk ↥B) ∧
    (∀ g ∈ M24g ⊓ Subgroup.centralizer ({z} : Set S24),
      rk ↥(commOn (fixV (rImg ρ (Subgroup.zpowers z))) (rImg ρ (Subgroup.zpowers g))) = 1 →
        g ∈ pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z} : Set S24)))

section Twist

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem conjSubg_zpowers {X : Type*} [Group X] (g x : X) :
    conjSubg g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  rw [conjSubg, MonoidHom.map_zpowers]
  congr 1

theorem card_conjSubg {X : Type*} [Group X] (g : X) (A : Subgroup X) :
    Nat.card ↥(conjSubg g A) = Nat.card ↥A := by
  rw [conjSubg]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem rk_conjSubg (g : S24) (A : Subgroup S24) : rk ↥(conjSubg g A) = rk ↥A := by
  unfold rk
  rw [card_conjSubg]

theorem isE2k_conjSubg (k : ℕ) (g : S24) {A : Subgroup S24} (h : IsE2k k A) :
    IsE2k k (conjSubg g A) := by
  obtain ⟨hEA, hcard⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 := E3.isElemAbelian_conjSubgroup hEA g⁻¹
    rw [conjSubgroup] at h1
    simp only [inv_inv] at h1
    exact h1
  · rw [card_conjSubg, hcard]

theorem inf_centralizer_conj {τ : S24} (hτ : τ ∈ M24g) (z : S24) :
    M24g ⊓ Subgroup.centralizer ({τ⁻¹ * z * τ} : Set S24) =
      conjSubg τ⁻¹ (M24g ⊓ Subgroup.centralizer ({z} : Set S24)) := by
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mem_conjSubg_iff,
    Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  simp only [inv_inv]
  constructor
  · rintro ⟨hxM, hxc⟩
    refine ⟨?_, ?_⟩
    · exact M24g.mul_mem (M24g.mul_mem hτ hxM) (M24g.inv_mem hτ)
    · calc (τ * x * τ⁻¹) * z
          = τ * (x * (τ⁻¹ * z * τ)) * τ⁻¹ := by group
        _ = τ * ((τ⁻¹ * z * τ) * x) * τ⁻¹ := by rw [hxc]
        _ = z * (τ * x * τ⁻¹) := by group
  · rintro ⟨hxM, hxc⟩
    refine ⟨?_, ?_⟩
    · have hx : x = τ⁻¹ * (τ * x * τ⁻¹) * τ := by group
      rw [hx]
      exact M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hτ) hxM) hτ
    · calc x * (τ⁻¹ * z * τ)
          = τ⁻¹ * ((τ * x * τ⁻¹) * z) * τ := by group
        _ = τ⁻¹ * (z * (τ * x * τ⁻¹)) * τ := by rw [hxc]
        _ = (τ⁻¹ * z * τ) * x := by group

variable (ρ : ↥M24g →* MulAut V) (ρ' : ↥M24g →* MulAut W) (e : V ≃* W) (τ : ↥M24g)

private theorem mem_cenM_aux
    (hcongr : ∀ γ : ↥M24g, congrHom e (ρ γ) = ρ' (τ⁻¹ * γ * τ)) (U : Subgroup V) (γ : ↥M24g) :
    γ ∈ cenM ρ U ↔ τ⁻¹ * γ * τ ∈ cenM ρ' (U.map e.toMonoidHom) := by
  rw [cenM, Subgroup.mem_comap, mem_centSub, cenM, Subgroup.mem_comap, mem_centSub]
  constructor
  · intro h w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    change ρ' (τ⁻¹ * γ * τ) (e u) = e u
    rw [← hcongr γ, congrHom_apply, e.symm_apply_apply, h u hu]
  · intro h u hu
    have hh := h (e u) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
    change ρ' (τ⁻¹ * γ * τ) (e u) = e u at hh
    rw [← hcongr γ, congrHom_apply, e.symm_apply_apply] at hh
    exact e.injective hh

theorem fixV_rImg_twist
    (hcongr : ∀ γ : ↥M24g, congrHom e (ρ γ) = ρ' (τ⁻¹ * γ * τ)) {A : Subgroup S24}
    (hA : A ≤ M24g) :
    (fixV (rImg ρ A)).map e.toMonoidHom = fixV (rImg ρ' (conjSubg ((τ : S24)⁻¹) A)) := by
  rw [← fixV_map_congrHom e (rImg ρ A), map_congrHom_rImg ρ ρ' e τ hcongr hA]

theorem cenMS_twist
    (hcongr : ∀ γ : ↥M24g, congrHom e (ρ γ) = ρ' (τ⁻¹ * γ * τ)) (U : Subgroup V) :
    (cenM ρ U).map M24g.subtype =
      conjSubg (τ : S24) ((cenM ρ' (U.map e.toMonoidHom)).map M24g.subtype) := by
  ext x
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [mem_conjSubg_iff]
    refine ⟨τ⁻¹ * γ * τ, (mem_cenM_aux ρ ρ' e τ hcongr U γ).mp hγ, ?_⟩
    simp only [map_mul, map_inv]
    rw [show (↑τ : S24) = M24g.subtype τ from rfl]
  · intro hx
    rw [mem_conjSubg_iff, Subgroup.mem_map] at hx
    obtain ⟨γ', hγ', hγ'x⟩ := hx
    refine ⟨τ * γ' * τ⁻¹, ?_, ?_⟩
    · change τ * γ' * τ⁻¹ ∈ cenM ρ U
      rw [mem_cenM_aux ρ ρ' e τ hcongr U]
      convert hγ' using 1
      group
    · rw [show (τ : S24) = M24g.subtype τ from rfl] at hγ'x
      simp only [map_mul, map_inv, hγ'x]
      group

theorem mem_cenM_twist
    (hcongr : ∀ γ : ↥M24g, congrHom e (ρ γ) = ρ' (τ⁻¹ * γ * τ)) (U : Subgroup V) (γ : ↥M24g) :
    γ ∈ cenM ρ U ↔ τ⁻¹ * γ * τ ∈ cenM ρ' (U.map e.toMonoidHom) :=
  mem_cenM_aux ρ ρ' e τ hcongr U γ

theorem H162Z_of_twist
    (hcongr : ∀ γ : ↥M24g, congrHom e (ρ γ) = ρ' (τ⁻¹ * γ * τ))
    {Q : V → ZMod 2} {Q' : W → ZMod 2} (hQ : ∀ x, Q' (e x) = Q x)
    {V₅ : Subgroup V} {V₅' : Subgroup W} (hV₅ : V₅.map e.toMonoidHom = V₅')
    {KO KO' : Subgroup S24} (hKO : KO' = conjSubg ((τ : S24)⁻¹) KO)
    {z z' : S24} (hzM : z ∈ M24g) (hz : z' = (τ : S24)⁻¹ * z * (τ : S24)) :
    H162Z ρ' Q' V₅' KO' z' → H162Z ρ Q V₅ KO z := by
  intro h
  unfold H162Z at h ⊢
  set zz : Subgroup S24 := Subgroup.zpowers z with hzzdef
  set zz' : Subgroup S24 := Subgroup.zpowers z' with hzz'def
  set Wz : Subgroup V := fixV (rImg ρ zz) with hWzdef
  set Wz' : Subgroup W := fixV (rImg ρ' zz') with hWz'def
  set D : Subgroup S24 := (cenM ρ (V₅ ⊓ Wz)).map M24g.subtype with hDdef
  set D' : Subgroup S24 := (cenM ρ' (V₅' ⊓ Wz')).map M24g.subtype with hD'def
  obtain ⟨⟨h3a, h3b⟩, h5, ⟨h6a, h6b, h6c, h6d⟩, h7, h8⟩ := h
  have hzz : zz ≤ M24g := by
    rw [hzzdef]
    exact Subgroup.zpowers_le.mpr hzM
  have hzz' : conjSubg ((τ : S24)⁻¹) zz = zz' := by
    rw [hzzdef, hzz'def, conjSubg_zpowers]
    simp only [inv_inv]
    rw [hz]
  have hconj_zz : conjSubg (τ : S24) zz' = zz := by
    rw [← hzz']
    exact conjSubg_inv_conjSubg ((τ : S24)⁻¹) zz
  have hWz : Wz.map e.toMonoidHom = Wz' := by
    rw [hWzdef, hWz'def]
    rw [fixV_rImg_twist ρ ρ' e τ hcongr hzz, hzz']
  have hVW : (V₅ ⊓ Wz).map e.toMonoidHom = V₅' ⊓ Wz' := by
    rw [Subgroup.map_inf V₅ Wz e.toMonoidHom e.injective, hV₅, hWz]
  have hD : D = conjSubg (τ : S24) D' := by
    rw [hDdef, hD'def]
    have hh := cenMS_twist ρ ρ' e τ hcongr (V₅ ⊓ Wz)
    rw [hVW] at hh
    exact hh
  have hDle : D ≤ M24g := by
    rw [hDdef]
    exact Subgroup.map_subtype_le _
  have hC : M24g ⊓ Subgroup.centralizer ({z'} : Set S24) =
      conjSubg ((τ : S24)⁻¹) (M24g ⊓ Subgroup.centralizer ({z} : Set S24)) := by
    rw [hz]
    exact inf_centralizer_conj τ.2 z
  have hC' : conjSubg (τ : S24) (M24g ⊓ Subgroup.centralizer ({z'} : Set S24)) =
      M24g ⊓ Subgroup.centralizer ({z} : Set S24) := by
    rw [hC]
    exact conjSubg_inv_conjSubg ((τ : S24)⁻¹) (M24g ⊓ Subgroup.centralizer ({z} : Set S24))
  have hpC : pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z} : Set S24)) =
      conjSubg (τ : S24) (pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z'} : Set S24))) := by
    rw [← hC']
    exact pCoreOf_conjSubg 2 (τ : S24) (M24g ⊓ Subgroup.centralizer ({z'} : Set S24))
  have hKOconj : conjSubg (τ : S24) KO' = KO := by
    rw [hKO]
    exact conjSubg_inv_conjSubg ((τ : S24)⁻¹) KO
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← rk_map_mulEquiv e (Wz ⊔ V₅), Subgroup.map_sup, hWz, hV₅]
    exact h3a
  · intro x hx
    have hx' : e x ∈ Wz' ⊔ V₅' := by
      have hmem : e x ∈ (Wz ⊔ V₅).map e.toMonoidHom := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [Subgroup.map_sup, hWz, hV₅] at hmem
    rw [← hQ x]
    exact h3b (e x) hx'
  · ext γ
    rw [mem_cenM_twist ρ ρ' e τ hcongr Wz γ, hWz, h5, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf,
      show (↑(τ⁻¹ * γ * τ) : S24) = (τ : S24)⁻¹ * (γ : S24) * (τ : S24) by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv],
      ← hconj_zz, mem_conjSubg_iff]
  · rw [← rk_map_mulEquiv e (V₅ ⊓ Wz), hVW]
    exact h6a
  · rw [hD]
    exact isE2k_conjSubg 4 (τ : S24) h6b
  · calc pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z} : Set S24)) =
          conjSubg (τ : S24) (pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z'} : Set S24))) := hpC
      _ = conjSubg (τ : S24) (KO' ⊔ D') := by rw [h6c]
      _ = conjSubg (τ : S24) KO' ⊔ conjSubg (τ : S24) D' := by
            simp only [conjSubg, Subgroup.map_sup]
      _ = KO ⊔ D := by rw [hKOconj, hD]
  · intro element helement
    have helement' : τ⁻¹ * element * τ ∈
        pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z'} : Set S24)) := by
      rw [hpC] at helement
      rwa [mem_conjSubg_iff] at helement
    obtain ⟨k', hk', c', hc', hkc⟩ := h6d (τ⁻¹ * element * τ) helement'
    refine ⟨(τ : S24) * k' * (τ : S24)⁻¹, ?_, (τ : S24) * c' * (τ : S24)⁻¹, ?_, ?_⟩
    · rw [← hKOconj, mem_conjSubg_iff]
      convert hk' using 1
      group
    · rw [hD, mem_conjSubg_iff]
      convert hc' using 1
      group
    · calc element = (τ : S24) * (k' * c') * (τ : S24)⁻¹ := by
              rw [← hkc]
              simp only [Subgroup.coe_inv]
              group
        _ = (τ : S24) * k' * (τ : S24)⁻¹ * ((τ : S24) * c' * (τ : S24)⁻¹) := by
              group
  · intro B hzB hBD
    have hBM : B ≤ M24g := hBD.trans hDle
    set B' : Subgroup S24 := conjSubg ((τ : S24)⁻¹) B with hB'def
    have hz'B' : z' ∈ B' := by
      rw [hB'def, mem_conjSubg_iff, hz]
      convert hzB using 1
      group
    have hB'D' : B' ≤ D' := by
      rw [hB'def]
      calc conjSubg ((τ : S24)⁻¹) B ≤ conjSubg ((τ : S24)⁻¹) D := conjSubg_mono _ hBD
        _ = conjSubg ((τ : S24)⁻¹) (conjSubg (τ : S24) D') := by rw [← hD]
        _ = D' := conjSubg_inv_conjSubg (τ : S24) D'
    have hfix : (fixV (rImg ρ B)).map e.toMonoidHom = fixV (rImg ρ' B') := by
      rw [hB'def]
      exact fixV_rImg_twist ρ ρ' e τ hcongr hBM
    have hrkfix : rk ↥(fixV (rImg ρ B)) = rk ↥(fixV (rImg ρ' B')) := by
      rw [← rk_map_mulEquiv e (fixV (rImg ρ B)), hfix]
    rw [hrkfix, h7 B' hz'B' hB'D',
      show rk ↥B' = rk ↥B from rk_conjSubg ((τ : S24)⁻¹) B]
  · intro g hg h1
    have hgM : g ∈ M24g := hg.1
    have hA : Subgroup.zpowers g ≤ M24g := Subgroup.zpowers_le.mpr hgM
    set g' : S24 := (τ : S24)⁻¹ * g * (τ : S24) with hg'def
    have hg' : g' ∈ M24g ⊓ Subgroup.centralizer ({z'} : Set S24) := by
      have hmem : g ∈ conjSubg (τ : S24) (M24g ⊓ Subgroup.centralizer ({z'} : Set S24)) := by
        rw [hC']
        exact hg
      rw [hg'def]
      exact (mem_conjSubg_iff (τ : S24) (M24g ⊓ Subgroup.centralizer ({z'} : Set S24)) g).mp hmem
    have hconj_g : conjSubg ((τ : S24)⁻¹) (Subgroup.zpowers g) = Subgroup.zpowers g' := by
      rw [conjSubg_zpowers]
      simp only [inv_inv]
      rw [hg'def]
    have hmap : (rImg ρ (Subgroup.zpowers g)).map (congrHom e) = rImg ρ' (Subgroup.zpowers g') := by
      rw [← hconj_g]
      exact map_congrHom_rImg ρ ρ' e τ hcongr hA
    have hcomm : commOn Wz' (rImg ρ' (Subgroup.zpowers g')) =
        (commOn Wz (rImg ρ (Subgroup.zpowers g))).map e.toMonoidHom := by
      rw [← hWz, ← hmap]
      exact commOn_map_congrHom e Wz (rImg ρ (Subgroup.zpowers g))
    have hrkcomm : rk ↥(commOn Wz' (rImg ρ' (Subgroup.zpowers g'))) =
        rk ↥(commOn Wz (rImg ρ (Subgroup.zpowers g))) := by
      rw [hcomm, rk_map_mulEquiv]
    have hg'pC : g' ∈ pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z'} : Set S24)) :=
      h8 g' hg' (by rw [hrkcomm]; exact h1)
    rw [hpC, mem_conjSubg_iff]
    simpa [hg'def] using hg'pC

end Twist

end CFSG.ASVolI.H16
