module

public import CFSG.LocalAnalysis.StandardType.GGLangDictChar

public section

namespace CFSG.StandardType

section DictTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem dictTr_isComponentOf_comap {X' Y' : Type*} [Group X'] [Group Y']
    (φ : X' →* Y') (hφ : Function.Injective φ) {F : Subgroup X'} {L : Subgroup Y'}
    (hL : CFSG.Open.IsComponentOf L (F.map φ)) :
    CFSG.Open.IsComponentOf (L.comap φ) F := by
  obtain ⟨hLK, hsub, hq⟩ := hL
  have hLr : L ≤ φ.range := hLK.trans (Subgroup.map_le_range φ F)
  have hLmap : (L.comap φ).map φ = L := Subgroup.map_comap_eq_self hLr
  have hcomapF : (F.map φ).comap φ = F := Subgroup.comap_map_eq_self_of_injective hφ F
  have hLF : L.comap φ ≤ F := by
    have h1 : L.comap φ ≤ (F.map φ).comap φ := Subgroup.comap_mono hLK
    rwa [hcomapF] at h1
  have hsubF : CFSG.Open.IsSubnormal (L.comap φ) F := by
    have h1 := CFSG.Open.IsSubnormal.comap φ hsub
    rwa [hcomapF] at h1
  have e : ↥(L.comap φ) ≃* ↥L :=
    (Subgroup.equivMapOfInjective (L.comap φ) φ hφ).trans (MulEquiv.subgroupCongr hLmap)
  exact ⟨hLF, hsubF, CFSG.Open.IsQuasisimple.of_mulEquiv e hq⟩

private theorem dictTr_isComponentOf_map_iff {X' Y' : Type*} [Group X'] [Group Y']
    (φ : X' →* Y') (hφ : Function.Injective φ) (Lg : Subgroup Y') (F : Subgroup X') :
    CFSG.Open.IsComponentOf Lg (F.map φ) ↔
      ∃ R0 : Subgroup X', CFSG.Open.IsComponentOf R0 F ∧ Lg = R0.map φ := by
  constructor
  · intro hL
    have hLr : Lg ≤ φ.range := hL.1.trans (Subgroup.map_le_range φ F)
    have hLmap : (Lg.comap φ).map φ = Lg := Subgroup.map_comap_eq_self hLr
    refine ⟨Lg.comap φ, dictTr_isComponentOf_comap φ hφ hL, ?_⟩
    exact hLmap.symm
  · rintro ⟨R0, hR0, rfl⟩
    exact ⟨Subgroup.map_mono hR0.1, CFSG.Open.IsSubnormal.map φ hR0.2.1,
      CFSG.Open.IsQuasisimple.of_mulEquiv (R0.equivMapOfInjective φ hφ).symm hR0.2.2⟩

theorem isComponentOf_psi_range_centralizer_family_iff
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (Us : Set Bs) (Lg : Subgroup (GGAutU t n f)) :
    CFSG.Assembly.IsComponentOf Lg
        ((ggPsiU t n f).range ⊓ Subgroup.centralizer (Subtype.val '' Us : Set (GGAutU t n f))) ↔
      ∃ R : Subgroup (ModGL B.τ L),
        CFSG.Open.IsComponentOf R
          (B.setup.Γ ⊓ Subgroup.centralizer (Set.range fun u : Us => rootDiagUnit B.τ (B.a u.1))) ∧
          Lg = (R.comap B.ι).map (ggPsiBar t n f) := by
  let CΓ : Subgroup (ModGL B.τ L) :=
    B.setup.Γ ⊓ Subgroup.centralizer (Set.range fun u : Us => rootDiagUnit B.τ (B.a u.1))
  let X : Subgroup ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) := CΓ.comap B.ι
  have hle : CΓ ≤ B.ι.range := by
    intro x hx
    rw [B.ι_range]
    exact (Subgroup.mem_inf.1 hx).1
  have hXmap : X.map B.ι = CΓ := Subgroup.map_comap_eq_self hle
  have hU : (ggPsiU t n f).range = (ggPsiBar t n f).range := by
    rw [show ggPsiU t n f = (ggPsiBar t n f).comp (QuotientGroup.mk' _) from rfl,
      MonoidHom.range_comp]
    have htop : (QuotientGroup.mk' (Subgroup.center (ggU t n f).K)).range = ⊤ :=
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)
    rw [htop, ← MonoidHom.range_eq_map]
  have hcomm : ∀ (u : Bs) (k : (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K),
      (u : GGAutU t n f) * ggPsiBar t n f k = ggPsiBar t n f k * (u : GGAutU t n f) ↔
        rootDiagUnit B.τ (B.a u) * B.ι k = B.ι k * rootDiagUnit B.τ (B.a u) := by
    intro u k
    have hψ : Function.Injective (ggPsiBar t n f) := ggPsiBar_injective t n f B.center_bot
    have hconj : (u : GGAutU t n f) * ggPsiBar t n f k * (u : GGAutU t n f)⁻¹ =
        ggPsiBar t n f ((u : GGAutU t n f) k) := by
      ext x
      simp only [ggPsiBar, MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply]
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    have huk : (u : GGAutU t n f) * ggPsiBar t n f k = ggPsiBar t n f k * (u : GGAutU t n f)
        ↔ ((u : GGAutU t n f) k = k) := by
      constructor
      · intro h
        apply hψ
        rw [← hconj, h]
        group
      · intro h
        calc (u : GGAutU t n f) * ggPsiBar t n f k
            = ((u : GGAutU t n f) * ggPsiBar t n f k * (u : GGAutU t n f)⁻¹)
                * (u : GGAutU t n f) := by group
          _ = ggPsiBar t n f ((u : GGAutU t n f) k) * (u : GGAutU t n f) := by rw [hconj]
          _ = ggPsiBar t n f k * (u : GGAutU t n f) := by rw [h]
    have hd : rootDiagUnit B.τ (B.a u) * B.ι k = B.ι k * rootDiagUnit B.τ (B.a u)
        ↔ ((u : GGAutU t n f) k = k) := by
      constructor
      · intro h
        apply B.ι_inj
        rw [B.a_act u k, h]
        group
      · intro h
        have h' := B.a_act u k
        rw [h] at h'
        have h'' : rootDiagUnit B.τ (B.a u) * B.ι k * (rootDiagUnit B.τ (B.a u))⁻¹ =
            B.ι k := h'.symm
        calc rootDiagUnit B.τ (B.a u) * B.ι k
            = (rootDiagUnit B.τ (B.a u) * B.ι k * (rootDiagUnit B.τ (B.a u))⁻¹)
                * rootDiagUnit B.τ (B.a u) := by group
          _ = B.ι k * rootDiagUnit B.τ (B.a u) := by rw [h'']
    exact huk.trans hd.symm
  have hmap : X.map (ggPsiBar t n f) =
      (ggPsiU t n f).range ⊓ Subgroup.centralizer (Subtype.val '' Us : Set (GGAutU t n f)) := by
    rw [hU]
    apply le_antisymm
    · rintro x ⟨k, hk, rfl⟩
      have hk' := hk
      have hkC : B.ι k ∈ CΓ := hk'
      refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_range.2 ⟨k, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : ∃ u : Bs, u ∈ Us ∧ (u : GGAutU t n f) = y :=
        (Set.mem_image (Subtype.val : Bs → GGAutU t n f) Us y).1 hy
      obtain ⟨u, hu, rfl⟩ := hy'
      exact (hcomm u k).2
        ((Subgroup.mem_centralizer_iff.1 hkC.2) _ ⟨⟨u, hu⟩, rfl⟩)
    · rintro x ⟨hr, hc⟩
      obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hr
      refine Subgroup.mem_map.2 ⟨k, ?_, rfl⟩
      change B.ι k ∈ CΓ
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [← B.ι_range]
        exact MonoidHom.mem_range.2 ⟨k, rfl⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨u, rfl⟩ := hy
        exact (hcomm u.1 k).1 ((Subgroup.mem_centralizer_iff.1 hc) _ ⟨u.1, u.2, rfl⟩)
  have hstep : CFSG.Assembly.IsComponentOf Lg
      ((ggPsiU t n f).range ⊓ Subgroup.centralizer (Subtype.val '' Us : Set (GGAutU t n f))) ↔
      CFSG.Open.IsComponentOf Lg (X.map (ggPsiBar t n f)) := by
    rw [← hmap]
    exact CFSG.Assembly.isComponentOf_iff_open
  rw [hstep]
  constructor
  · intro hL
    obtain ⟨R0, hR0, hLg⟩ :=
      (dictTr_isComponentOf_map_iff (ggPsiBar t n f)
        (ggPsiBar_injective t n f B.center_bot) Lg X).1 hL
    refine ⟨R0.map B.ι, ?_, ?_⟩
    · have hcomp : CFSG.Open.IsComponentOf (R0.map B.ι) (X.map B.ι) :=
        (dictTr_isComponentOf_map_iff B.ι B.ι_inj (R0.map B.ι) X).2 ⟨R0, hR0, rfl⟩
      rwa [hXmap] at hcomp
    · rw [hLg, Subgroup.comap_map_eq_self_of_injective B.ι_inj R0]
  · rintro ⟨R, hR, hLg⟩
    have hR' : CFSG.Open.IsComponentOf R (X.map B.ι) := by rwa [hXmap]
    have hR0 : CFSG.Open.IsComponentOf (R.comap B.ι) X :=
      dictTr_isComponentOf_comap B.ι B.ι_inj hR'
    exact (dictTr_isComponentOf_map_iff (ggPsiBar t n f)
      (ggPsiBar_injective t n f B.center_bot) Lg X).2 ⟨R.comap B.ι, hR0, hLg⟩

theorem isComponentOf_psi_range_centralizer_iff
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (b : Bs) (Lg : Subgroup (GGAutU t n f)) :
    CFSG.Assembly.IsComponentOf Lg
        ((ggPsiU t n f).range ⊓ Subgroup.centralizer {(b : GGAutU t n f)}) ↔
      ∃ R : Subgroup (ModGL B.τ L),
        CFSG.Open.IsComponentOf R
          (B.setup.Γ ⊓ Subgroup.centralizer {rootDiagUnit B.τ (B.a b)}) ∧
          Lg = (R.comap B.ι).map (ggPsiBar t n f) := by
  have h := isComponentOf_psi_range_centralizer_family_iff B ({b} : Set Bs) Lg
  have hsingle : (Subtype.val '' ({b} : Set Bs) : Set (GGAutU t n f)) =
      {(b : GGAutU t n f)} := by
    rw [Set.image_singleton]
  have hrange : Set.range (fun u : ({b} : Set Bs) => rootDiagUnit B.τ (B.a u.1)) =
      {rootDiagUnit B.τ (B.a b)} := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      have hu : u = ⟨b, rfl⟩ := Subtype.ext (Set.mem_singleton_iff.1 u.2)
      rw [hu]
      rfl
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨⟨b, rfl⟩, rfl⟩
  rw [hsingle, hrange] at h
  exact h

end DictTransport

end CFSG.StandardType
