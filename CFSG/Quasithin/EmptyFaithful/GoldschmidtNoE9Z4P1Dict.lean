module

public import CFSG.Quasithin.EmptyFaithful.S14612ED
public import CFSG.Quasithin.EmptyFaithful.S146F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section Dict

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem map_rhoH_eq_autOn (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H) :
    (B.subgroupOf H).map (rhoH h) = autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) := by
  ext φ
  rw [Subgroup.mem_map]
  show _ ↔ φ ∈ autI h.isElemAbelian_tilde (tildeOf V₁ B)
  rw [mem_autI]
  have hn : ∀ x : ↥H, (C1Pack.toTilde h x : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈
      Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) :
        Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) := fun x =>
    HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) (H := H) le_rfl (C1Pack.toTilde h x).2
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨(C1Pack.toTilde h x : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁), hn x⟩, ?_,
      rfl⟩
    rw [C1Pack.coe_toTilde]
    exact secMk_mem_secImg (Subgroup.mem_subgroupOf.mp hx)
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨b, hbB, hbg⟩ := mem_secImg.mp hg
    refine ⟨⟨b, hBH hbB⟩, Subgroup.mem_subgroupOf.mpr hbB, ?_⟩
    have : g = ⟨(C1Pack.toTilde h ⟨b, hBH hbB⟩ : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁),
        hn ⟨b, hBH hbB⟩⟩ := Subtype.ext (by rw [C1Pack.coe_toTilde]; exact hbg.symm)
    rw [this]
    rfl

theorem map_rhoH_mem_Qset (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H)
    (hB : autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H)) ∈
      @Qset ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian h.isElemAbelian_tilde)
        (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)))) :
    (B.subgroupOf H).map (rhoH h) ∈ Qset (rhoH h).range := by
  rw [map_rhoH_eq_autOn h hBH, range_rhoH h]
  exact hB

theorem pCoreOf_le_HLb (h : HypF91 T V L V₁ Vp H)
    (hsplit : ∀ w : UMod h, ∃ a ∈ kOf (rhoH h), ∃ c ∈ fixV (rhoH h).range, w = a * c)
    (Q : Subgroup (MulAut ↥(kOf (rhoH h)))) : pCoreOf 2 H ≤ HLb (resBeta (rhoH h)) Q := by
  intro x hx
  have hxH : x ∈ H := pCoreOf_le 2 H hx
  refine (mem_HLb_iff hxH).mpr ?_
  have h1 : rhoH h ⟨x, hxH⟩ = 1 := (rhoH_eq_one_iff h ⟨x, hxH⟩).mpr hx
  have h2 : resBeta (rhoH h) ⟨x, hxH⟩ = 1 := by
    rw [← MonoidHom.mem_ker, ker_resBeta _ hsplit, MonoidHom.mem_ker]
    exact h1
  rw [h2]
  exact Q.one_mem

theorem conjSub_HLb_of_conjBy (h : HypF91 T V L V₁ Vp H)
    {Q : Subgroup (MulAut ↥(kOf (rhoH h)))} {y : ↥H}
    (hQ : conjBy (resBeta (rhoH h) y) Q = Q) :
    conjSub (y : G) (HLb (resBeta (rhoH h)) Q) = HLb (resBeta (rhoH h)) Q :=
  conjSub_HLb y.2 (fun q => by rw [← mem_conjBy_iff, hQ]) 

end Dict

section Setup

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.g_not_mem_of_setup (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (hs : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g) : (g : G) ∉ mcOf T := by
  intro hg
  obtain ⟨z, hz, hz1⟩ := S.exists_ne_one_Z
  apply S.conj_not_mem_Z hH hs hz hz1
  have hgN : (g : G) ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    rw [S.normalizer_Z]
    exact hg
  exact (Subgroup.mem_normalizer_iff.mp hgN z).mp hz

theorem Setting146.le_of_setup (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (hs : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g) :
    F8.Uγ (VZ T M) H (g : G) ≤ H ∧ conjClosure (VZ T M) H ≤ conjSub (g : G) H := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  refine ⟨h98.Uγ_le_H hs, ?_⟩
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← hs.edge₁, stab_smul, stab_γ₁ h98.amalgamHypV.le₂]
  have h1 := (h98.F913_2 hs).1
  rw [← hstab]
  exact h1.trans ((pCoreOf_le 2 _).trans inf_le_right)

end Setup

end CFSG.Quasithin
