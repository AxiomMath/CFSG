module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K45Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45SplitCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup CFSG.Quasithin
open scoped commutatorElement

variable {E : Type} [Group E] [Finite E] {H Z : Subgroup E} [H.Normal] [Z.Normal]
  {η : E →* Equiv.Perm (Fin 5)}

@[expose] noncomputable def quotientEta (hZH : Z ≤ H) (hker : η.ker = H) :
    E ⧸ Z →* Equiv.Perm (Fin 5) :=
  QuotientGroup.lift Z η (by rw [hker]; exact hZH)

theorem quotientEta_mk (hZH : Z ≤ H) (hker : η.ker = H) (e : E) :
    quotientEta hZH hker (QuotientGroup.mk' Z e) = η e := rfl

theorem quotientEta_ker (hZH : Z ≤ H) (hker : η.ker = H) :
    (quotientEta hZH hker).ker = H.map (QuotientGroup.mk' Z) := by
  dsimp only [quotientEta]
  rw [QuotientGroup.ker_lift, hker]

theorem quotientEta_range (hZH : Z ≤ H) (hker : η.ker = H)
    (hrange : η.range = alternatingGroup (Fin 5)) :
    (quotientEta hZH hker).range = alternatingGroup (Fin 5) := by
  rw [← hrange]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective Z y
    exact ⟨e, by rw [quotientEta_mk]⟩
  · rintro ⟨e, rfl⟩
    exact ⟨QuotientGroup.mk' Z e, by rw [quotientEta_mk]⟩

theorem ker_subgroupMap_mk' :
    ((QuotientGroup.mk' Z).subgroupMap H).ker = Z.subgroupOf H := by
  rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk' Z]

@[expose] noncomputable def quotientIso :
    (↥H ⧸ Z.subgroupOf H) ≃* ↥(H.map (QuotientGroup.mk' Z)) :=
  QuotientGroup.liftEquiv (N := Z.subgroupOf H) (φ := (QuotientGroup.mk' Z).subgroupMap H)
    ((QuotientGroup.mk' Z).subgroupMap_surjective H) ker_subgroupMap_mk'.symm

theorem quotientIso_mk (h : ↥H) :
    quotientIso (QuotientGroup.mk h) = (QuotientGroup.mk' Z).subgroupMap H h :=
  QuotientGroup.liftEquiv_mk (N := Z.subgroupOf H) (φ := (QuotientGroup.mk' Z).subgroupMap H)
    ((QuotientGroup.mk' Z).subgroupMap_surjective H) ker_subgroupMap_mk'.symm h

@[expose] noncomputable def quotientTheta (θ : (↥H ⧸ Z.subgroupOf H) ≃* ↥(G6.coreMod 5)) :
    ↥(H.map (QuotientGroup.mk' Z)) ≃* ↥(G6.coreMod 5) :=
  quotientIso.symm.trans θ

theorem quotientTheta_mk (θ : (↥H ⧸ Z.subgroupOf H) ≃* ↥(G6.coreMod 5)) (h : ↥H) :
    quotientTheta θ ((QuotientGroup.mk' Z).subgroupMap H h) = θ (QuotientGroup.mk h) := by
  show θ (quotientIso.symm ((QuotientGroup.mk' Z).subgroupMap H h)) = θ (QuotientGroup.mk h)
  rw [← quotientIso_mk h, MulEquiv.symm_apply_apply]

theorem quotientTheta_conj (θ : (↥H ⧸ Z.subgroupOf H) ≃* ↥(G6.coreMod 5)) (hZH : Z ≤ H)
    (hker : η.ker = H)
    (hθ : ∀ (g : E) (h : ↥H), θ (QuotientGroup.mk (MulAut.conjNormal g h)) =
      G6.coreAct 5 (η g) (θ (QuotientGroup.mk h)))
    (g : E ⧸ Z) (v : ↥(H.map (QuotientGroup.mk' Z))) :
    quotientTheta θ (MulAut.conjNormal g v) =
      G6.coreAct 5 (quotientEta hZH hker g) (quotientTheta θ v) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z g
  obtain ⟨h, hhH, hv⟩ := Subgroup.mem_map.mp
    (show (v : E ⧸ Z) ∈ H.map (QuotientGroup.mk' Z) from v.2)
  have hv' : v = (QuotientGroup.mk' Z).subgroupMap H ⟨h, hhH⟩ := by
    apply Subtype.ext
    exact hv.symm
  have hconj : MulAut.conjNormal (QuotientGroup.mk' Z a)
        ((QuotientGroup.mk' Z).subgroupMap H ⟨h, hhH⟩) =
      (QuotientGroup.mk' Z).subgroupMap H (MulAut.conjNormal a ⟨h, hhH⟩) := by
    apply Subtype.ext
    show QuotientGroup.mk' Z a * ((QuotientGroup.mk' Z).subgroupMap H ⟨h, hhH⟩ : E ⧸ Z) *
        (QuotientGroup.mk' Z a)⁻¹ = QuotientGroup.mk' Z (MulAut.conjNormal a ⟨h, hhH⟩ : ↥H)
    rw [MulAut.conjNormal_apply, map_mul, map_mul, map_inv]
    rfl
  rw [hv', hconj, quotientTheta_mk θ, quotientTheta_mk θ, quotientEta_mk]
  exact hθ a ⟨h, hhH⟩

theorem comap_inf_eq (hZH : Z ≤ H) {K : Subgroup (E ⧸ Z)}
    (hVK : H.map (QuotientGroup.mk' Z) ⊓ K = ⊥) :
    K.comap (QuotientGroup.mk' Z) ⊓ H = Z := by
  refine le_antisymm ?_ ?_
  · intro e he
    obtain ⟨heS, heH⟩ := Subgroup.mem_inf.mp he
    have hqeV : QuotientGroup.mk' Z e ∈ H.map (QuotientGroup.mk' Z) :=
      Subgroup.mem_map.mpr ⟨e, heH, rfl⟩
    have hqe_bot : QuotientGroup.mk' Z e ∈ H.map (QuotientGroup.mk' Z) ⊓ K :=
      Subgroup.mem_inf.mpr ⟨hqeV, heS⟩
    rw [hVK] at hqe_bot
    have hq1 : QuotientGroup.mk' Z e = 1 := by simpa using hqe_bot
    exact (QuotientGroup.ker_mk' Z) ▸ MonoidHom.mem_ker.mpr hq1
  · intro z hz
    exact Subgroup.mem_inf.mpr ⟨by
      show QuotientGroup.mk' Z z ∈ K
      rw [show QuotientGroup.mk' Z z = 1 from
        MonoidHom.mem_ker.mp ((QuotientGroup.ker_mk' Z).symm ▸ hz)]
      exact K.one_mem, hZH hz⟩

theorem comap_sup_eq_top {K : Subgroup (E ⧸ Z)}
    (hsup : H.map (QuotientGroup.mk' Z) ⊔ K = ⊤) :
    K.comap (QuotientGroup.mk' Z) ⊔ H = ⊤ := by
  haveI : (H.map (QuotientGroup.mk' Z)).Normal :=
    (inferInstance : H.Normal).map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  refine eq_top_iff.mpr ?_
  intro e _
  have hq : QuotientGroup.mk' Z e ∈ H.map (QuotientGroup.mk' Z) ⊔ K := by
    rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨v, hvV, k, hkK, hqeq⟩ := Subgroup.mem_sup_of_normal_left.1 hq
  obtain ⟨h, hhH, hvh⟩ := Subgroup.mem_map.mp hvV
  have hkS : h⁻¹ * e ∈ K.comap (QuotientGroup.mk' Z) := by
    show QuotientGroup.mk' Z (h⁻¹ * e) ∈ K
    rw [map_mul, map_inv, hvh, ← hqeq]
    rw [show v⁻¹ * (v * k) = k by group]
    exact hkK
  have heq : e = h * (h⁻¹ * e) := by group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hhH) (Subgroup.mem_sup_left hkS)

theorem splitDelta5_holds : SplitDelta5 := by
  intro E _ _ H Z _ _ hZH η hker hrange θ hθ
  classical
  haveI hV : (H.map (QuotientGroup.mk' Z)).Normal :=
    (inferInstance : H.Normal).map (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  obtain ⟨K, hVKbot, hVKsup⟩ := exists_complement_of_delta5 (H.map (QuotientGroup.mk' Z))
    (quotientEta hZH hker) (quotientEta_ker hZH hker) (quotientEta_range hZH hker hrange)
    (quotientTheta θ) (quotientTheta_conj θ hZH hker hθ)
  have hSH : K.comap (QuotientGroup.mk' Z) ⊓ H = Z := comap_inf_eq hZH hVKbot
  exact ⟨K.comap (QuotientGroup.mk' Z), le_of_eq_of_le hSH.symm inf_le_left, hSH,
    comap_sup_eq_top hVKsup⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
