module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Img
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2
import CFSG.LocalAnalysis.WeakClosure81.W183K3Img2A
import CFSG.LocalAnalysis.WeakClosure81.Twelve
import CFSG.LocalAnalysis.WeakClosure81.W183K3Dyn
import CFSG.CGT.PushingUpLit.BHS7.QuotInv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement
open W183K3

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem br3_twoComp (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {Kk F : Subgroup ↥(M.img H)} (hker : KStarData Kk F)
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H))
    {L : Subgroup G} (hLc : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a))
    {t : G} (htT : t ∈ D.T) (hne : conjSubgroup L t ≠ L)
    (hall : ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t) :
    ∃ L₁ L₂ : Subgroup (LGL 2 M.W), Br3TwoComp (M.img H) (M.img D.T) L₁ L₂ ∧
      quasiCentre L₁ ⊔ quasiCentre L₂ = Kk.map (M.img H).subtype ∧
      (∀ {P : ∀ (X : Type) [Group X], Prop},
        (∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → P X → P Y) →
          HasQuotShape L (kerMV V H : Set G) P → P (↥L₁ ⧸ Subgroup.center ↥L₁)) ∧
      (∀ {t' : G}, t' ∈ D.T → ActsOnDynkinMod (kerMV V H) L t' →
        ∃ τ ∈ M.img D.T, ActsOnDynkinMod (quasiCentre L₁) L₁ τ) := by
  classical
  have hQkeep := hQ
  obtain ⟨X, hXgrp, φ, hφs, hφk, hXsimple, hXnab⟩ := hQkeep
  letI : Group X := hXgrp
  have hKL : kerMV V H ≤ L := hLc.2.1
  have hLH : L ≤ H := hLc.2.2.1
  have hDT : D.T ≤ H := x.hyp.hyp171.2.1
  have hρker : ∀ j : ↥H, M.ρ j = 1 → (j : G) ∈ kerMV V H := by
    intro j hj
    rw [M.ρ_eq_one_iff j] at hj
    exact x.hyp.inf_centralizer_eOmegaZ_le_kerMV ⟨j.2, hj⟩
  set Z : Subgroup (LGL 2 M.W) := Kk.map (M.img H).subtype with hZ
  have hKk' : ∀ j : ↥H, (M.ρ j : LGL 2 M.W) ∈ Z ↔ (j : G) ∈ kerMV V H := by
    intro j
    have hYj : M.ρ j ∈ M.img H := M.mem_img.mpr ⟨j, j.2, rfl⟩
    rw [hZ]
    constructor
    · intro hmem
      rw [Subgroup.mem_map] at hmem
      obtain ⟨k, hkK, hkz⟩ := hmem
      exact (hKk j k hkz).1 hkK
    · intro hjK
      exact Subgroup.mem_map.mpr ⟨⟨M.ρ j, hYj⟩, (hKk j ⟨M.ρ j, hYj⟩ rfl).2 hjK, rfl⟩
  have himgK : ((kerMV V H).subgroupOf H).map M.ρ = Z := by
    ext r
    constructor
    · intro hr
      obtain ⟨j, hjK, hjρ⟩ := M.mem_img.mp hr
      rw [← hjρ]
      exact (hKk' j).2 hjK
    · intro hr
      rw [hZ, Subgroup.mem_map] at hr
      obtain ⟨k, hkK, hkr⟩ := hr
      obtain ⟨j, hjH, hjρ⟩ := M.mem_img.mp k.2
      exact M.mem_img.mpr ⟨j, (hKk j k hjρ.symm).1 hkK, hjρ.trans hkr⟩
  let L₂ : Subgroup G := conjSubgroup L t
  have htH : t ∈ H := hDT htT
  have htHinv : t⁻¹ ∈ H := hDT (D.T.inv_mem htT)
  have hHnorm : H ≤ Subgroup.normalizer (kerMV V H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hKL.trans hLH)).mp hLc.1
  have hKmap : (kerMV V H).map (MulAut.conj t⁻¹).toMonoidHom = kerMV V H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHnorm (hDT (D.T.inv_mem htT)))
  have hKt : (kerMV V H).map (MulAut.conj t).toMonoidHom = kerMV V H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHnorm htH)
  have hHmap : H.map (MulAut.conj t⁻¹).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htHinv)
  have hL₂c : IsComponentModN (kerMV V H) H L₂ :=
    w183K3Img2_isComponentModN_map (MulAut.conj t⁻¹) hKmap hHmap hLc
  have hL₂H : L₂ ≤ H := hL₂c.2.2.1
  have hcommG : ∀ a ∈ L, ∀ b ∈ L₂, a * b * a⁻¹ * b⁻¹ ∈ kerMV V H :=
    w183_components_commute hLc hL₂c hne.symm
  have hL₂img : M.img L₂ = cj (M.ρ ⟨t⁻¹, htHinv⟩) (M.img L) := by
    have h := M.img_conj (A := L) hLH (j := ⟨t⁻¹, htHinv⟩)
    rw [inv_inv] at h
    exact h.symm
  have hcommZL : ⁅M.img L, M.img L₂⁆ ≤ Z := by
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    obtain ⟨j, hjL, rfl⟩ := M.mem_img.1 ha
    obtain ⟨k, hkL₂, rfl⟩ := M.mem_img.1 hb
    have hmem := hcommG (j : G) hjL (k : G) hkL₂
    have hcoe : ((j * k * j⁻¹ * k⁻¹ : ↥H) : G) =
        (j : G) * (k : G) * (j : G)⁻¹ * (k : G)⁻¹ := by simp
    have hj₀K : (((j * k * j⁻¹ * k⁻¹ : ↥H) : G)) ∈ kerMV V H := by rw [hcoe]; exact hmem
    have hZmem : (M.ρ (j * k * j⁻¹ * k⁻¹) : LGL 2 M.W) ∈ Z := (hKk' _).2 hj₀K
    have hval : (M.ρ (j * k * j⁻¹ * k⁻¹) : LGL 2 M.W) = ⁅M.ρ j, M.ρ k⁆ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, commutatorElement_def]
    rwa [hval] at hZmem
  have hneImg : M.img L ≠ M.img L₂ := by
    intro heq
    apply hne
    have hcomapL : (M.img L).comap M.ρ = L.subgroupOf H :=
      Subgroup.comap_map_eq_self (f := M.ρ) (H := L.subgroupOf H) fun q hq =>
        Subgroup.mem_subgroupOf.mpr (hKL (hρker q (MonoidHom.mem_ker.mp hq)))
    have hcomapL₂ : (M.img L₂).comap M.ρ = L₂.subgroupOf H :=
      Subgroup.comap_map_eq_self (f := M.ρ) (H := L₂.subgroupOf H) fun q hq =>
        Subgroup.mem_subgroupOf.mpr (hL₂c.2.1 (hρker q (MonoidHom.mem_ker.mp hq)))
    have hsub : L.subgroupOf H = L₂.subgroupOf H := by
      rw [← hcomapL, heq, hcomapL₂]
    have h := congrArg (Subgroup.map H.subtype) hsub
    rw [Subgroup.map_subgroupOf_eq_of_le hLH,
      Subgroup.map_subgroupOf_eq_of_le hL₂H] at h
    exact h.symm
  have hYsup : M.img H = M.img L ⊔ M.img D.T := by
    rw [← M.img_sup hLH hDT, hLT]
  have hΛY : M.img L ⊔ M.img L₂ ≤ M.img H :=
    sup_le (M.img_mono hLH) (M.img_mono hL₂H)
  have hZleL₁ : Z ≤ M.img L := by
    rw [hZ]
    rintro z ⟨k, hkK, rfl⟩
    obtain ⟨j, hjH, hjρ⟩ := M.mem_img.mp k.2
    have hjK : (j : G) ∈ kerMV V H := (hKk j k hjρ.symm).1 hkK
    have hmem : M.ρ j ∈ M.img L := M.mem_img.mpr ⟨j, hKL hjK, rfl⟩
    rwa [hjρ] at hmem
  have hZleL₂ : Z ≤ M.img L₂ := by
    rw [hZ]
    rintro z ⟨k, hkK, rfl⟩
    obtain ⟨j, hjH, hjρ⟩ := M.mem_img.mp k.2
    have hjK : (j : G) ∈ kerMV V H := (hKk j k hjρ.symm).1 hkK
    have hmem : M.ρ j ∈ M.img L₂ := M.mem_img.mpr ⟨j, hL₂c.2.1 hjK, rfl⟩
    rwa [hjρ] at hmem
  have hstepL₂ : ∀ b ∈ M.img L₂, ∀ x ∈ M.img L, b * x * b⁻¹ ∈ M.img L := by
    intro b hb x hx
    have hbxZ : ⁅b, x⁆ ∈ Z := by
      have h1 : ⁅b, x⁆ ∈ ⁅M.img L₂, M.img L⁆ := Subgroup.commutator_mem_commutator hb hx
      rw [Subgroup.commutator_comm] at h1
      exact hcommZL h1
    have hthis : b * x * b⁻¹ = ⁅b, x⁆ * x := by rw [commutatorElement_def]; group
    rw [hthis]
    exact (M.img L).mul_mem (hZleL₁ hbxZ) hx
  have hL₂normL₁ : M.img L₂ ≤
      Subgroup.normalizer ((M.img L : Subgroup (LGL 2 M.W)) : Set _) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hstepL₂ b hb a ha
    · intro ha
      have h := hstepL₂ b⁻¹ ((M.img L₂).inv_mem hb) (b * a * b⁻¹) ha
      have h2 : b⁻¹ * (b * a * b⁻¹) * b = a := by group
      rw [inv_inv] at h
      rwa [h2] at h
  have hstepL₁ : ∀ a ∈ M.img L, ∀ y ∈ M.img L₂, a * y * a⁻¹ ∈ M.img L₂ := by
    intro a ha y hy
    have hayZ : ⁅a, y⁆ ∈ Z := hcommZL (Subgroup.commutator_mem_commutator ha hy)
    have hthis : a * y * a⁻¹ = ⁅a, y⁆ * y := by rw [commutatorElement_def]; group
    rw [hthis]
    exact (M.img L₂).mul_mem (hZleL₂ hayZ) hy
  have hL₁normL₂ : M.img L ≤
      Subgroup.normalizer ((M.img L₂ : Subgroup (LGL 2 M.W)) : Set _) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact hstepL₁ a ha b hb
    · intro hb
      have h := hstepL₁ a⁻¹ ((M.img L).inv_mem ha) (a * b * a⁻¹) hb
      have h2 : a⁻¹ * (a * b * a⁻¹) * a = b := by group
      rw [inv_inv] at h
      rwa [h2] at h
  have hΛnormL₁ : M.img L ⊔ M.img L₂ ≤
      Subgroup.normalizer ((M.img L : Subgroup (LGL 2 M.W)) : Set _) :=
    sup_le Subgroup.le_normalizer hL₂normL₁
  have hΛnormL₂ : M.img L ⊔ M.img L₂ ≤
      Subgroup.normalizer ((M.img L₂ : Subgroup (LGL 2 M.W)) : Set _) :=
    sup_le hL₁normL₂ Subgroup.le_normalizer
  set F' : Subgroup (LGL 2 M.W) := F.map (M.img H).subtype with hF'def
  have hZleF' : Z ≤ F' := by
    rw [hZ, hF'def]
    exact Subgroup.map_mono (hker.eq_F ▸ hker.le)
  have hF'normY : M.img H ≤ Subgroup.normalizer (F' : Set (LGL 2 M.W)) := by
    have hn : (F'.subgroupOf (M.img H)).Normal := by
      have h1 : F'.subgroupOf (M.img H) = F := by
        rw [hF'def]
        show (F.map (M.img H).subtype).comap (M.img H).subtype = F
        rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
      rw [h1]
      exact hker.soc.normal_right
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (by
      rw [hF'def]
      exact Subgroup.map_subtype_le F)).mp hn
  have hF'cj : ∀ (y : LGL 2 M.W), y ∈ M.img H → cj y F' = F' := fun y hy => by
    simpa [cj] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hF'normY hy)
  have hZnormY : M.img H ≤ Subgroup.normalizer (Z : Set (LGL 2 M.W)) := by
    have hZsub : Z.subgroupOf (M.img H) = Kk := by
      rw [hZ]
      show (Kk.map (M.img H).subtype).comap (M.img H).subtype = Kk
      rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (by
      rw [hZ]
      exact Subgroup.map_subtype_le Kk)).mp ?_
    rw [hZsub]
    exact hker.soc.normal_left
  have hZcj : ∀ (y : LGL 2 M.W), y ∈ M.img H → cj y Z = Z := fun y hy => by
    simpa [cj] using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZnormY hy)
  have hZcentF' : ∀ z ∈ Z, ∀ f ∈ F', z * f = f * z := by
    intro z hz f hf
    rw [hZ] at hz
    obtain ⟨k, hkK, rfl⟩ := hz
    rw [hF'def] at hf
    obtain ⟨g, hgF, rfl⟩ := hf
    have hcent : k ∈ Subgroup.centralizer (F : Set ↥(M.img H)) := by
      have h := hkK
      rw [hker.cent, hker.eq_F] at h
      exact h
    have h1 : g * k = k * g := Subgroup.mem_centralizer_iff.mp hcent g hgF
    exact (congrArg Subtype.val h1).symm
  obtain ⟨θ, hθs, hθk⟩ :=
    w183K3Img2_quot_of_shape M hLH hKL hρker hKk' φ hφs hφk
  have hΛT : (M.img L ⊔ M.img L₂) ⊔ M.img D.T = M.img H := by
    refine le_antisymm (sup_le (sup_le (M.img_mono hLH) (M.img_mono hL₂H)) (M.img_mono hDT)) ?_
    calc M.img H = M.img L ⊔ M.img D.T := hYsup
      _ ≤ (M.img L ⊔ M.img L₂) ⊔ M.img D.T :=
          sup_le (le_sup_of_le_left le_sup_left) le_sup_right
  have hperm : ∀ z ∈ M.img H, (cj z (M.img L) = M.img L ∧ cj z (M.img L₂) = M.img L₂) ∨
      (cj z (M.img L) = M.img L₂ ∧ cj z (M.img L₂) = M.img L) := by
    let P : LGL 2 M.W → Prop := fun u =>
      (cj u (M.img L) = M.img L ∧ cj u (M.img L₂) = M.img L₂) ∨
        (cj u (M.img L) = M.img L₂ ∧ cj u (M.img L₂) = M.img L)
    have hPmul : ∀ u v : LGL 2 M.W, P u → P v → P (u * v) := by
      intro u v hu hv
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hv with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · left
        exact ⟨by rw [← cj_cj u v (M.img L), k1, h1],
          by rw [← cj_cj u v (M.img L₂), k2, h2]⟩
      · right
        exact ⟨by rw [← cj_cj u v (M.img L), k1, h2],
          by rw [← cj_cj u v (M.img L₂), k2, h1]⟩
      · right
        exact ⟨by rw [← cj_cj u v (M.img L), k1, h1],
          by rw [← cj_cj u v (M.img L₂), k2, h2]⟩
      · left
        exact ⟨by rw [← cj_cj u v (M.img L), k1, h2],
          by rw [← cj_cj u v (M.img L₂), k2, h1]⟩
    have hPone : P 1 := by
      left
      exact ⟨cj_one _, cj_one _⟩
    have hPinv : ∀ u : LGL 2 M.W, P u → P u⁻¹ := by
      intro u hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        refine ⟨?_, ?_⟩
        · have hh := congrArg (fun A => cj u⁻¹ A) h1
          rw [cj_self_inv u (M.img L)] at hh
          exact hh.symm
        · have hh := congrArg (fun A => cj u⁻¹ A) h2
          rw [cj_self_inv u (M.img L₂)] at hh
          exact hh.symm
      · right
        refine ⟨?_, ?_⟩
        · have hh := congrArg (fun A => cj u⁻¹ A) h2
          rw [cj_self_inv u (M.img L₂)] at hh
          exact hh.symm
        · have hh := congrArg (fun A => cj u⁻¹ A) h1
          rw [cj_self_inv u (M.img L)] at hh
          exact hh.symm
    let S : Subgroup (LGL 2 M.W) :=
      { carrier := {u | P u}
        mul_mem' := fun {u v} hu hv => hPmul u v hu hv
        one_mem' := hPone
        inv_mem' := fun {u} hu => hPinv u hu }
    have hL₁S : M.img L ≤ S := by
      intro a ha
      change P a
      left
      refine ⟨?_, ?_⟩
      · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ha)
      · rw [cj]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL₁normL₂ ha)
    have hTS : M.img D.T ≤ S := by
      intro b hb
      obtain ⟨s, hs, rfl⟩ := M.mem_img.1 hb
      show (cj (M.ρ s) (M.img L) = M.img L ∧ cj (M.ρ s) (M.img L₂) = M.img L₂) ∨
        (cj (M.ρ s) (M.img L) = M.img L₂ ∧ cj (M.ρ s) (M.img L₂) = M.img L)
      have hcjb_inj : Function.Injective (fun C : Subgroup (LGL 2 M.W) => cj (M.ρ s) C) := by
        intro C D hCD
        have hthis := congrArg (fun C : Subgroup (LGL 2 M.W) => cj (M.ρ s)⁻¹ C) hCD
        rw [cj_self_inv (M.ρ s) C, cj_self_inv (M.ρ s) D] at hthis
        exact hthis
      have hbL : cj (M.ρ s) (M.img L) = M.img (conjSubgroup L (s : G)⁻¹) :=
        M.img_conj (A := L) hLH s
      have hbL₂ : cj (M.ρ s) (M.img L₂) = M.img (conjSubgroup L (t * (s : G)⁻¹)) := by
        have h := M.img_conj (A := conjSubgroup L t) hL₂H s
        rw [conjSubgroup_conjSubgroup] at h
        exact h
      have h1 : M.img (conjSubgroup L (s : G)⁻¹) = M.img L ∨
          M.img (conjSubgroup L (s : G)⁻¹) = M.img L₂ := by
        rcases hall (s : G)⁻¹ (D.T.inv_mem hs) with h | h
        · left; rw [h]
        · right; rw [h]
      have h2 : M.img (conjSubgroup L (t * (s : G)⁻¹)) = M.img L ∨
          M.img (conjSubgroup L (t * (s : G)⁻¹)) = M.img L₂ := by
        rcases hall (t * (s : G)⁻¹) (D.T.mul_mem htT (D.T.inv_mem hs)) with h | h
        · left; rw [h]
        · right; rw [h]
      rw [hbL, hbL₂]
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exfalso
        refine hneImg (hcjb_inj ?_)
        change cj (M.ρ s) (M.img L) = cj (M.ρ s) (M.img L₂)
        rw [hbL, hbL₂]
        exact h1.trans h2.symm
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exfalso
        refine hneImg (hcjb_inj ?_)
        change cj (M.ρ s) (M.img L) = cj (M.ρ s) (M.img L₂)
        rw [hbL, hbL₂]
        exact h1.trans h2.symm
    intro z hz
    have hz' : z ∈ M.img L ⊔ M.img D.T := hYsup ▸ hz
    change P z
    exact sup_le hL₁S hTS hz'
  have hsupfix : ∀ z ∈ M.img H, cj z (M.img L ⊔ M.img L₂) = M.img L ⊔ M.img L₂ := by
    intro z hz
    rcases hperm z hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [cj, Subgroup.map_sup]
      change cj z (M.img L) ⊔ cj z (M.img L₂) = M.img L ⊔ M.img L₂
      rw [h1, h2]
    · rw [cj, Subgroup.map_sup]
      change cj z (M.img L) ⊔ cj z (M.img L₂) = M.img L ⊔ M.img L₂
      rw [h1, h2, sup_comm]
  have hΛn : ((M.img L ⊔ M.img L₂).subgroupOf (M.img H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hΛY).mpr fun z hz =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [cj] using hsupfix z hz)
  have hT2 : IsPGroup 2 ↥((M.img D.T).subgroupOf (M.img H)) :=
    (M.isPGroup_img x.hyp.isSylowIn_T.isPGroup).of_equiv
      (Subgroup.subgroupOfEquivOfLe (M.img_mono hDT)).symm
  have hsubT : ((M.img L ⊔ M.img L₂).subgroupOf (M.img H)) ⊔
      ((M.img D.T).subgroupOf (M.img H)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hΛY (M.img_mono hDT), hΛT, Subgroup.subgroupOf_self]
  have hFleΛ : F' ≤ M.img L ⊔ M.img L₂ := by
    have hle := CFSG.CGT.PushingUpLit.BHS7.opResidual_le_of_le_sup (Γ := ↥(M.img H))
      (G := ⊤) (N := (M.img L ⊔ M.img L₂).subgroupOf (M.img H))
      (T := (M.img D.T).subgroupOf (M.img H)) hT2
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hΛn]; exact le_top)
      (by rw [sup_comm]; exact le_of_eq hsubT.symm)
    rw [hker.eq_F] at hle
    have hmap : F.map (M.img H).subtype ≤ M.img L ⊔ M.img L₂ := by
      have hmono := Subgroup.map_mono (f := (M.img H).subtype) hle
      rwa [Subgroup.map_subgroupOf_eq_of_le hΛY] at hmono
    rwa [hF'def]
  have hstepF' : ∀ y ∈ M.img L, ∀ a ∈ F' ⊓ M.img L, y * a * y⁻¹ ∈ F' ⊓ M.img L := by
    intro y hy a ha
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hF'normY (M.img_mono hLH hy)) a).1 ha.1,
       (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) a).1 ha.2⟩
  have hA₁n : ((F' ⊓ M.img L).subgroupOf (M.img L)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hstepF' y hy a ha
    · intro ha
      have h := hstepF' y⁻¹ ((M.img L).inv_mem hy) (y * a * y⁻¹) ha
      have h2 : y⁻¹ * (y * a * y⁻¹) * y = a := by group
      rw [inv_inv] at h
      rwa [h2] at h
  have hcase : F' ⊓ M.img L = Z ∨ M.img L ≤ F' := by
    rcases w183K3Img2_map_subgroupOf_eq_bot_or_le inf_le_right (le_inf hZleF' hZleL₁)
      θ hθs hθk hXsimple hA₁n with hbot | htop
    · left
      refine le_antisymm ?_ (le_inf hZleF' hZleL₁)
      intro a ha
      have hmem : θ (⟨a, ha.2⟩) ∈
          ((F' ⊓ M.img L).subgroupOf (M.img L)).map θ :=
        Subgroup.mem_map.mpr ⟨⟨a, ha.2⟩,
          Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [hbot] at hmem
      exact (hθk ⟨a, ha.2⟩).1 (Subgroup.mem_bot.mp hmem)
    · right
      exact htop.trans inf_le_left
  have hF'perf : ⁅F', F'⁆ = F' := by
    rw [hF'def, ← Subgroup.map_commutator, ← hker.eq_F, hker.perfect, hker.eq_F]
  have hx₀ : (M.ρ ⟨t⁻¹, htHinv⟩ : LGL 2 M.W) ∈ M.img H :=
    M.mem_img.mpr ⟨⟨t⁻¹, htHinv⟩, htHinv, rfl⟩
  have hF'eqΛ : F' = M.img L ⊔ M.img L₂ := by
    rcases hcase with hZcase | hLcase
    · exfalso
      have hZcjx : cj (M.ρ ⟨t⁻¹, htHinv⟩) Z = Z := hZcj _ hx₀
      have hF'Z₂ : F' ⊓ M.img L₂ = Z := by
        have h1 : cj (M.ρ ⟨t⁻¹, htHinv⟩) (F' ⊓ M.img L) =
            cj (M.ρ ⟨t⁻¹, htHinv⟩) F' ⊓ cj (M.ρ ⟨t⁻¹, htHinv⟩) (M.img L) := by
          rw [cj]
          exact Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective
        rw [hZcase] at h1
        rw [hZcjx, hF'cj _ hx₀, ← hL₂img] at h1
        exact h1.symm
      have hFL₁ : ⁅F', M.img L⁆ ≤ Z := by
        refine Subgroup.commutator_le.mpr fun f hf l hl => ?_
        have hlY : l ∈ M.img H := M.img_mono hLH hl
        have hflF' : l * f * l⁻¹ * f⁻¹ ∈ F' :=
          F'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hF'normY hlY) f).1 hf) (F'.inv_mem hf)
        have hflL : l * f * l⁻¹ * f⁻¹ ∈ M.img L := by
          have hfN : f ∈ Subgroup.normalizer ((M.img L : Subgroup (LGL 2 M.W)) : Set _) :=
            hΛnormL₁ (hFleΛ hf)
          have hfinv : f * l⁻¹ * f⁻¹ ∈ M.img L :=
            (M.img L).inv_mem ((Subgroup.mem_normalizer_iff.mp hfN l).1 hl)
          have hthis : l * f * l⁻¹ * f⁻¹ = l * (f * l⁻¹ * f⁻¹) := by group
          rw [hthis]
          exact (M.img L).mul_mem hl hfinv
        have hmem : l * f * l⁻¹ * f⁻¹ ∈ F' ⊓ M.img L := Subgroup.mem_inf.mpr ⟨hflF', hflL⟩
        rw [hZcase] at hmem
        have hinv : f * l * f⁻¹ * l⁻¹ = (l * f * l⁻¹ * f⁻¹)⁻¹ := by group
        rw [commutatorElement_def, hinv]
        exact Z.inv_mem hmem
      have hFL₂ : ⁅F', M.img L₂⁆ ≤ Z := by
        refine Subgroup.commutator_le.mpr fun f hf l hl => ?_
        have hlY : l ∈ M.img H := M.img_mono hL₂H hl
        have hflF' : l * f * l⁻¹ * f⁻¹ ∈ F' :=
          F'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hF'normY hlY) f).1 hf) (F'.inv_mem hf)
        have hflL : l * f * l⁻¹ * f⁻¹ ∈ M.img L₂ := by
          have hfN : f ∈ Subgroup.normalizer ((M.img L₂ : Subgroup (LGL 2 M.W)) : Set _) :=
            hΛnormL₂ (hFleΛ hf)
          have hfinv : f * l⁻¹ * f⁻¹ ∈ M.img L₂ :=
            (M.img L₂).inv_mem ((Subgroup.mem_normalizer_iff.mp hfN l).1 hl)
          have hthis : l * f * l⁻¹ * f⁻¹ = l * (f * l⁻¹ * f⁻¹) := by group
          rw [hthis]
          exact (M.img L₂).mul_mem hl hfinv
        have hmem : l * f * l⁻¹ * f⁻¹ ∈ F' ⊓ M.img L₂ := Subgroup.mem_inf.mpr ⟨hflF', hflL⟩
        rw [hF'Z₂] at hmem
        have hinv : f * l * f⁻¹ * l⁻¹ = (l * f * l⁻¹ * f⁻¹)⁻¹ := by group
        rw [commutatorElement_def, hinv]
        exact Z.inv_mem hmem
      have hFΛle : ⁅F', M.img L ⊔ M.img L₂⁆ ≤ Z := by
        refine Subgroup.commutator_le.mpr fun f hf x hx => ?_
        haveI : ((M.img L₂).subgroupOf (M.img L ⊔ M.img L₂)).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hΛnormL₂
        have hxsub : (⟨x, hx⟩ : ↥(M.img L ⊔ M.img L₂)) ∈
            (M.img L).subgroupOf (M.img L ⊔ M.img L₂) ⊔
              (M.img L₂).subgroupOf (M.img L ⊔ M.img L₂) := by
          rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
          exact Subgroup.mem_top _
        obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_right).1 hxsub
        have ha' : (a : LGL 2 M.W) ∈ M.img L := Subgroup.mem_subgroupOf.mp ha
        have hb' : (b : LGL 2 M.W) ∈ M.img L₂ := Subgroup.mem_subgroupOf.mp hb
        have hxeq : (a : LGL 2 M.W) * (b : LGL 2 M.W) = x := congrArg Subtype.val hab
        have hfa : ⁅f, (a : LGL 2 M.W)⁆ ∈ Z :=
          hFL₁ (Subgroup.commutator_mem_commutator hf ha')
        have hfb : ⁅f, (b : LGL 2 M.W)⁆ ∈ Z :=
          hFL₂ (Subgroup.commutator_mem_commutator hf hb')
        have haY : (a : LGL 2 M.W) ∈ M.img H := M.img_mono hLH ha'
        have hconj : (a : LGL 2 M.W) * ⁅f, (b : LGL 2 M.W)⁆ * (a : LGL 2 M.W)⁻¹ ∈ Z :=
          (Subgroup.mem_normalizer_iff.mp (hZnormY haY) _).1 hfb
        have hmain : ⁅f, (a : LGL 2 M.W) * (b : LGL 2 M.W)⁆ ∈ Z := by
          rw [commutatorElement_mul_right_eq_mul_conj]
          have h := Z.mul_mem hfa hconj
          simpa [mul_assoc] using h
        rwa [hxeq] at hmain
      have hFF'le : ⁅F', F'⁆ ≤ Z :=
        (Subgroup.commutator_mono le_rfl hFleΛ).trans hFΛle
      have hF'Z : F' ≤ Z := by
        rw [← hF'perf]
        exact hFF'le
      have hFK : F ≤ Kk := by
        intro f hf
        have hmem : (f : LGL 2 M.W) ∈ F' := by
          rw [hF'def]
          exact Subgroup.mem_map.mpr ⟨f, hf, rfl⟩
        have hZmem := hF'Z hmem
        rw [hZ, Subgroup.mem_map] at hZmem
        obtain ⟨k, hkK, hk⟩ := hZmem
        have hkf : k = f := Subtype.ext hk
        rwa [hkf] at hkK
      exact hker.soc.not_le hFK
    · have hL₂F' : M.img L₂ ≤ F' := by
        rw [hL₂img, ← hF'cj _ hx₀]
        exact Subgroup.map_mono hLcase
      exact le_antisymm hFleΛ (sup_le hLcase hL₂F')
  have hZcΛ : ∀ z ∈ Z, ∀ l ∈ M.img L ⊔ M.img L₂, z * l = l * z := by
    rw [← hF'eqΛ]
    exact hZcentF'
  have hZleΛ : Z ≤ M.img L ⊔ M.img L₂ := hF'eqΛ ▸ hZleF'
  set L₁ : Subgroup (LGL 2 M.W) := ⁅M.img L, M.img L⁆ with hL₁def
  set L₂' : Subgroup (LGL 2 M.W) := ⁅M.img L₂, M.img L₂⁆ with hL₂'def
  have hL₁le : L₁ ≤ M.img L := by rw [hL₁def]; exact Subgroup.commutator_le_self _
  have hL₂'le : L₂' ≤ M.img L₂ := by rw [hL₂'def]; exact Subgroup.commutator_le_self _
  have hZcL₁ : ∀ z ∈ Z, ∀ a ∈ M.img L, z * a = a * z :=
    fun z hz a ha => hZcΛ z hz a (Subgroup.mem_sup_left ha)
  have hZcL₂ : ∀ z ∈ Z, ∀ a ∈ M.img L₂, z * a = a * z :=
    fun z hz a ha => hZcΛ z hz a (Subgroup.mem_sup_right ha)
  have hquasi₁ := w183K3Img2_quasi_of_quot (A := M.img L) (Z' := Z) hZleL₁ hZcL₁
    θ hθs hθk hXsimple hXnab
  have hL₁eq : M.img L = L₁ ⊔ Z := hquasi₁.1
  have hquasiL₁ : CFSG.Open.IsQuasisimple ↥L₁ := hquasi₁.2.1
  have hcentreL₁ : quasiCentre L₁ = L₁ ⊓ Z := hquasi₁.2.2
  have hQ₂ : HasQuotShape L₂ (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    refine w183K3Img2_hasQuotShape_of_mulEquiv (K := kerMV V H)
      (Subgroup.equivMapOfInjective L (MulAut.conj t⁻¹).toMonoidHom
        (MulAut.conj t⁻¹).injective) ?_ hQ
    intro l
    constructor
    · intro hl
      rw [← hKmap]
      exact Subgroup.mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hl
    · intro hl
      have h1 : (MulAut.conj t) ((MulAut.conj t⁻¹) l) ∈
          (kerMV V H).map (MulAut.conj t).toMonoidHom := Subgroup.mem_map_of_mem _ hl
      rw [hKt] at h1
      simpa [MulAut.conj_apply, mul_assoc] using h1
  obtain ⟨X₂, hX₂grp, φ₂, hφ₂s, hφ₂k, hX₂simple, hX₂nab⟩ := hQ₂
  letI : Group X₂ := hX₂grp
  obtain ⟨θ₂, hθ₂s, hθ₂k⟩ :=
    w183K3Img2_quot_of_shape M hL₂H hL₂c.2.1 hρker hKk' φ₂ hφ₂s hφ₂k
  have hquasi₂ := w183K3Img2_quasi_of_quot (A := M.img L₂) (Z' := Z) hZleL₂ hZcL₂
    θ₂ hθ₂s hθ₂k hX₂simple hX₂nab
  have hL₂'eq : M.img L₂ = L₂' ⊔ Z := hquasi₂.1
  have hquasiL₂' : CFSG.Open.IsQuasisimple ↥L₂' := hquasi₂.2.1
  have hcentreL₂' : quasiCentre L₂' = L₂' ⊓ Z := hquasi₂.2.2
  have hstep₁ : ∀ y ∈ M.img L, ∀ a ∈ M.img L ⊓ M.img L₂,
      y * a * y⁻¹ ∈ M.img L ⊓ M.img L₂ := by
    intro y hy a ha
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) a).1 ha.1,
       (Subgroup.mem_normalizer_iff.mp (hL₁normL₂ hy) a).1 ha.2⟩
  have hstep₂ : ∀ y ∈ M.img L₂, ∀ a ∈ M.img L ⊓ M.img L₂,
      y * a * y⁻¹ ∈ M.img L ⊓ M.img L₂ := by
    intro y hy a ha
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hL₂normL₁ hy) a).1 ha.1,
       (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) a).1 ha.2⟩
  have hA₁n : ((M.img L ⊓ M.img L₂).subgroupOf (M.img L)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hstep₁ y hy a ha
    · intro ha
      have h := hstep₁ y⁻¹ ((M.img L).inv_mem hy) (y * a * y⁻¹) ha
      have h2 : y⁻¹ * (y * a * y⁻¹) * y = a := by group
      rw [inv_inv] at h
      rwa [h2] at h
  have hA₂n : ((M.img L ⊓ M.img L₂).subgroupOf (M.img L₂)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hstep₂ y hy a ha
    · intro ha
      have h := hstep₂ y⁻¹ ((M.img L₂).inv_mem hy) (y * a * y⁻¹) ha
      have h2 : y⁻¹ * (y * a * y⁻¹) * y = a := by group
      rw [inv_inv] at h
      rwa [h2] at h
  have hL₁L₂ : M.img L ⊓ M.img L₂ = Z := by
    refine le_antisymm ?_ (le_inf hZleL₁ hZleL₂)
    have hc₁ := w183K3Img2_map_subgroupOf_eq_bot_or_le inf_le_left
      (le_inf hZleL₁ hZleL₂) θ hθs hθk hXsimple hA₁n
    have hc₂ := w183K3Img2_map_subgroupOf_eq_bot_or_le inf_le_right
      (le_inf hZleL₁ hZleL₂) θ₂ hθ₂s hθ₂k hX₂simple hA₂n
    rcases hc₁ with h₁ | h₁
    · intro a ha
      have hmem : θ (⟨a, ha.1⟩) ∈
          ((M.img L ⊓ M.img L₂).subgroupOf (M.img L)).map θ :=
        Subgroup.mem_map.mpr ⟨⟨a, ha.1⟩,
          Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [h₁] at hmem
      exact (hθk ⟨a, ha.1⟩).1 (Subgroup.mem_bot.mp hmem)
    rcases hc₂ with h₂ | h₂
    · intro a ha
      have hmem : θ₂ (⟨a, ha.2⟩) ∈
          ((M.img L ⊓ M.img L₂).subgroupOf (M.img L₂)).map θ₂ :=
        Subgroup.mem_map.mpr ⟨⟨a, ha.2⟩,
          Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [h₂] at hmem
      exact (hθ₂k ⟨a, ha.2⟩).1 (Subgroup.mem_bot.mp hmem)
    · exact absurd (le_antisymm (h₁.trans inf_le_right) (h₂.trans inf_le_left)) hneImg
  have hcommL₁L₂' : ∀ a ∈ L₁, ∀ b ∈ L₂', a * b = b * a := by
    have hthree : ⁅L₁, M.img L₂⁆ = ⊥ := by
      refine commutator_commutator_eq_bot_of_rotate (H₁ := M.img L) (H₂ := M.img L)
        (H₃ := M.img L₂) ?_ ?_
      · rw [eq_bot_iff]
        calc ⁅⁅M.img L, M.img L₂⁆, M.img L⁆ ≤ ⁅Z, M.img L⁆ :=
              Subgroup.commutator_mono hcommZL le_rfl
          _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
              (fun z hz => Subgroup.mem_centralizer_iff.mpr fun a ha =>
                (hZcL₁ z hz a ha).symm)
      · rw [Subgroup.commutator_comm (M.img L₂) (M.img L)]
        rw [eq_bot_iff]
        calc ⁅⁅M.img L, M.img L₂⁆, M.img L⁆ ≤ ⁅Z, M.img L⁆ :=
              Subgroup.commutator_mono hcommZL le_rfl
          _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
              (fun z hz => Subgroup.mem_centralizer_iff.mpr fun a ha =>
                (hZcL₁ z hz a ha).symm)
    have hcen : L₁ ≤ Subgroup.centralizer (M.img L₂ : Set (LGL 2 M.W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hthree
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hcen ha) b (hL₂'le hb)).symm
  have hΛeq : M.img L ⊔ M.img L₂ = L₁ ⊔ L₂' ⊔ Z := by
    rw [hL₁eq, hL₂'eq]
    ac_rfl
  have hZL₁comm : ∀ a ∈ L₁, ∀ z ∈ Z, a * z = z * a :=
    fun a ha z hz => (hZcΛ z hz a (Subgroup.mem_sup_left (hL₁le ha))).symm
  have hZL₂comm : ∀ b ∈ L₂', ∀ z ∈ Z, b * z = z * b :=
    fun b hb z hz => (hZcΛ z hz b (Subgroup.mem_sup_right (hL₂'le hb))).symm
  have hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z :=
    fun z hz z' hz' => hZcΛ z hz z' (hZleΛ hz')
  have hΛle : M.img L ⊔ M.img L₂ ≤ L₁ ⊔ L₂' := by
    have h := w183K3Img2_commutator_sup_sup_le hcommL₁L₂' hZL₁comm hZL₂comm hZZ
    rw [← hΛeq] at h
    have hperf : M.img L ⊔ M.img L₂ = ⁅M.img L ⊔ M.img L₂, M.img L ⊔ M.img L₂⁆ := by
      rw [← hF'eqΛ, hF'perf]
    rw [hperf]
    exact h
  have hZjoin : quasiCentre L₁ ⊔ quasiCentre L₂' = Z := by
    refine le_antisymm ?_ ?_
    · refine sup_le ?_ ?_
      · rw [hcentreL₁]; exact inf_le_right
      · rw [hcentreL₂']; exact inf_le_right
    · intro z hz
      have hzΛ : z ∈ L₁ ⊔ L₂' := hΛle (hZleΛ hz)
      obtain ⟨a, ha, b, hb, hab⟩ := (w183K3Img2_mem_sup_of_comm hcommL₁L₂').mp hzΛ
      have haQ : a ∈ quasiCentre L₁ := by
        rw [mem_quasiCentre]
        refine ⟨ha, fun x hx => ?_⟩
        have hzx : z * x = x * z := hZcΛ z hz x (Subgroup.mem_sup_left (hL₁le hx))
        have hbx : b * x = x * b := (hcommL₁L₂' x hx b hb).symm
        calc a * x = z * b⁻¹ * x := by rw [← hab]; group
          _ = z * (b⁻¹ * x) := by group
          _ = z * (x * b⁻¹) := by
                have hinv : b⁻¹ * x = x * b⁻¹ := by
                  have h := congrArg (fun t => b⁻¹ * t * b⁻¹) hbx
                  simpa [mul_assoc] using h.symm
                rw [hinv]
          _ = (z * x) * b⁻¹ := by group
          _ = (x * z) * b⁻¹ := by rw [hzx]
          _ = x * (z * b⁻¹) := by group
          _ = x * a := by rw [← hab]; group
      have hbQ : b ∈ quasiCentre L₂' := by
        rw [mem_quasiCentre]
        refine ⟨hb, fun x hx => ?_⟩
        have hzx : z * x = x * z := hZcΛ z hz x (Subgroup.mem_sup_right (hL₂'le hx))
        have hax : a * x = x * a := hcommL₁L₂' a ha x hx
        calc b * x = z * a⁻¹ * x := by
              rw [← hab, hcommL₁L₂' a ha b hb]; group
          _ = z * (a⁻¹ * x) := by group
          _ = z * (x * a⁻¹) := by
                have hinv : a⁻¹ * x = x * a⁻¹ := by
                  have h := congrArg (fun t => a⁻¹ * t * a⁻¹) hax
                  simpa [mul_assoc] using h.symm
                rw [hinv]
          _ = (z * x) * a⁻¹ := by group
          _ = (x * z) * a⁻¹ := by rw [hzx]
          _ = x * (z * a⁻¹) := by group
          _ = x * b := by rw [← hab, hcommL₁L₂' a ha b hb]; group
      rw [← hab]
      exact Subgroup.mul_mem_sup haQ hbQ
  have hZodd : Odd (Nat.card ↥Z) := by
    rw [hZ]
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective Kk (M.img H).subtype
      (M.img H).subtype_injective).toEquiv]
    exact hker.odd
  refine ⟨L₁, L₂', ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, hquasiL₁, hquasiL₂', ?_, ?_, hcommL₁L₂', ?_, ?_, ?_, ?_, ?_⟩
    · exact hL₁le.trans (M.img_mono hLH)
    · exact hL₂'le.trans (M.img_mono hL₂H)
    · have hcard : Nat.card ↥(Subgroup.center ↥L₁) = Nat.card ↥(L₁ ⊓ Z) := by
        rw [← hcentreL₁]
        exact Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center ↥L₁)
          L₁.subtype L₁.subtype_injective).toEquiv
      rw [hcard]
      exact hZodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    · have hcard : Nat.card ↥(Subgroup.center ↥L₂') = Nat.card ↥(L₂' ⊓ Z) := by
        rw [← hcentreL₂']
        exact Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center ↥L₂')
          L₂'.subtype L₂'.subtype_injective).toEquiv
      rw [hcard]
      exact hZodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    · intro heq
      have hle' : L₁ ≤ M.img L ⊓ M.img L₂ := le_inf hL₁le (heq ▸ hL₂'le)
      have hleZ : L₁ ≤ Z := by rwa [hL₁L₂] at hle'
      obtain ⟨a, ha, b, hb, hab⟩ := W183K3.quasi_exists_noncomm hquasiL₁
      exact hab (hZZ a (hleZ ha) b (hleZ hb))
    · intro y hy
      rcases hperm y hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [hL₁def]
          change (⁅M.img L, M.img L⁆).map (MulAut.conj y).toMonoidHom = ⁅M.img L, M.img L⁆
          rw [Subgroup.map_commutator,
            show (M.img L).map (MulAut.conj y).toMonoidHom = M.img L from h1]
        · rw [hL₂'def]
          change (⁅M.img L₂, M.img L₂⁆).map (MulAut.conj y).toMonoidHom = ⁅M.img L₂, M.img L₂⁆
          rw [Subgroup.map_commutator,
            show (M.img L₂).map (MulAut.conj y).toMonoidHom = M.img L₂ from h2]
      · right
        refine ⟨?_, ?_⟩
        · rw [hL₁def, hL₂'def]
          change (⁅M.img L, M.img L⁆).map (MulAut.conj y).toMonoidHom = ⁅M.img L₂, M.img L₂⁆
          rw [Subgroup.map_commutator,
            show (M.img L).map (MulAut.conj y).toMonoidHom = M.img L₂ from h1]
        · rw [hL₂'def, hL₁def]
          change (⁅M.img L₂, M.img L₂⁆).map (MulAut.conj y).toMonoidHom = ⁅M.img L, M.img L⁆
          rw [Subgroup.map_commutator,
            show (M.img L₂).map (MulAut.conj y).toMonoidHom = M.img L from h2]
    · refine ⟨M.ρ ⟨t⁻¹, htHinv⟩, M.mem_img.mpr ⟨⟨t⁻¹, htHinv⟩, D.T.inv_mem htT, rfl⟩, ?_⟩
      rw [hL₁def, hL₂'def]
      change (⁅M.img L, M.img L⁆).map (MulAut.conj (M.ρ ⟨t⁻¹, htHinv⟩)).toMonoidHom =
        ⁅M.img L₂, M.img L₂⁆
      rw [Subgroup.map_commutator,
        show (M.img L).map (MulAut.conj (M.ρ ⟨t⁻¹, htHinv⟩)).toMonoidHom = M.img L₂
          from hL₂img.symm]
    · intro y hy hy₁ hy₂
      have hycentΛ : ∀ l ∈ L₁ ⊔ L₂', y * l = l * y := by
        intro l hl
        obtain ⟨a, ha, b, hb, rfl⟩ := (w183K3Img2_mem_sup_of_comm hcommL₁L₂').mp hl
        calc y * (a * b) = (y * a) * b := by group
          _ = (a * y) * b := by rw [hy₁ a ha]
          _ = a * (y * b) := by group
          _ = a * (b * y) := by rw [hy₂ b hb]
          _ = (a * b) * y := by group
      have hycentF : ∀ f ∈ F, y * f = f * y := by
        intro f hf
        have hfΛ : (f : LGL 2 M.W) ∈ L₁ ⊔ L₂' :=
          hΛle (hF'eqΛ ▸ Subgroup.mem_map.mpr ⟨f, hf, rfl⟩)
        exact hycentΛ (f : LGL 2 M.W) hfΛ
      have hy' : (⟨y, hy⟩ : ↥(M.img H)) ∈ Kk := by
        have hcent : (⟨y, hy⟩ : ↥(M.img H)) ∈
            Subgroup.centralizer (F : Set ↥(M.img H)) := by
          rw [Subgroup.mem_centralizer_iff]
          intro f hf
          apply Subtype.ext
          exact (hycentF f hf).symm
        rw [hker.cent, hker.eq_F]
        exact hcent
      have hmemZ : y ∈ Z := Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hy', rfl⟩
      exact hΛle (hZleΛ hmemZ)
    · intro y hy
      haveI := hΛn
      have hyX : (⟨y, hy⟩ : ↥(M.img H)) ∈
          ((M.img L ⊔ M.img L₂).subgroupOf (M.img H)) ⊔
            ((M.img D.T).subgroupOf (M.img H)) := by
        rw [hsubT]
        exact Subgroup.mem_top _
      obtain ⟨l, hl, u, hu, hlu⟩ := (Subgroup.mem_sup_of_normal_left).1 hyX
      exact ⟨(l : LGL 2 M.W), hΛle (Subgroup.mem_subgroupOf.mp hl),
        (u : LGL 2 M.W), Subgroup.mem_subgroupOf.mp hu, (congrArg Subtype.val hlu).symm⟩
  · exact hZjoin
  · intro P hP hQ'
    obtain ⟨X', hX'grp, φ', hφ's, hφ'k, hPX'⟩ := hQ'
    letI : Group X' := hX'grp
    obtain ⟨θ', hθ's, hθ'k⟩ :=
      w183K3Img2_quot_of_shape M hLH hKL hρker hKk' φ' hφ's hφ'k
    exact hP X' (↥L₁ ⧸ Subgroup.center ↥L₁)
      (w183K3Img2_center_quot_iso hZcL₁ hZleL₁ hL₁eq hcentreL₁ θ' hθ's hθ'k) hPX'
  · intro t' ht'T hdyn
    have ht'H : t' ∈ H := hDT ht'T
    have hsub := W183K3.actsOnDynkinMod_subgroupOf H hLH ht'H hdyn
    have hker' : M.ρ.ker ⊓ (L.subgroupOf H) ≤ (kerMV V H).subgroupOf H := by
      intro q hq
      rw [Subgroup.mem_subgroupOf]
      exact hρker q (MonoidHom.mem_ker.mp hq.1)
    have hmap := W183K3.actsOnDynkinMod_map M.ρ hker' hsub
    rw [himgK] at hmap
    have hτN : M.ρ ⟨t', ht'H⟩ ∈ Subgroup.normalizer
        ((M.img L : Subgroup (LGL 2 M.W)) : Set _) := hmap.1
    have hτN₁ : M.ρ ⟨t', ht'H⟩ ∈ Subgroup.normalizer (L₁ : Set (LGL 2 M.W)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      rw [hL₁def, Subgroup.map_commutator]
      have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hτN
      rw [h1]
    have hτNZ : M.ρ ⟨t', ht'H⟩ ∈ Subgroup.normalizer (Z : Set (LGL 2 M.W)) :=
      hZnormY (M.mem_img.mpr ⟨⟨t', ht'H⟩, ht'H, rfl⟩)
    have hLZeq : L₁ ⊔ Z = M.img L := hL₁eq.symm
    have hcent : ∀ z ∈ Z, ∀ l ∈ L₁ ⊔ Z, z * l = l * z := by
      rw [hLZeq]
      exact hZcL₁
    have hdyn' : ActsOnDynkinMod (Z ⊓ L₁) L₁ (M.ρ ⟨t', ht'H⟩) :=
      W183K3.actsOnDynkinMod_of_central hcent hτN₁ hτNZ (by rw [hLZeq]; exact hmap)
    have hZinf : Z ⊓ L₁ = quasiCentre L₁ := by
      rw [hcentreL₁, inf_comm]
    refine ⟨M.ρ ⟨t', ht'H⟩, M.mem_img.mpr ⟨⟨t', ht'H⟩, ht'T, rfl⟩, ?_⟩
    rwa [hZinf] at hdyn'

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
