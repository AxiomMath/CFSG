module

public import CFSG.Quasithin.Vol2.KGFactC31J4Gen
public import CFSG.Quasithin.Vol2.KGFactHeInspJ4
public import CFSG.Quasithin.Vol2.KGFactJ4Base

public section

namespace CFSG.Quasithin.KGC31.J4

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31

abbrev G₀ : Type := ↥CFSG.Sporadic.J4.J

variable {A : Type} [Group A]

structure Setup (S M₀ R M V : Subgroup A) : Prop where
  hS : S.Normal
  hSs : IsSporadic .J4 ↥S
  hCS : Subgroup.centralizer (S : Set A) = ⊥
  hM₀S : M₀ ≤ S
  hper : ⁅M₀, M₀⁆ = M₀
  hM₀ne : M₀ ≠ ⊥
  hcomp : ∃ L ∈ cComp M, M₀ = conjClosure L M
  hR2 : IsPGroup 2 ↥R
  hRM : R ≤ M
  hMN : M ≤ Subgroup.normalizer (M₀ : Set A)
  hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A)
  hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀))
  hVM₀ : V ≤ M₀
  hVne : V ≠ ⊥
  hV : IsElemAbelian 2 V
  hcomm : ⁅V, M₀⁆ = V
  hVc : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R))
  hNVM : Subgroup.normalizer (V : Set A) ⊓ Subgroup.normalizer (M₀ : Set A) ≤ M
  hNR : Subgroup.normalizer (R : Set A) ≤ M
  hSM : ¬ S ≤ M
  hJ : Subgroup.normalizer (CFSG.Quasithin.thompsonJ R : Set A) ≤ M
  hZ : Subgroup.normalizer (CFSG.Quasithin.centerOf R : Set A) ≤ M
  hΩ : Subgroup.normalizer (CFSG.Quasithin.omegaOneCenterOf (CFSG.Quasithin.thompsonJ R) : Set A) ≤
    M

namespace Setup

variable {S M₀ R M V : Subgroup A} (h : Setup S M₀ R M V)
include h

theorem hM₀V : M₀ ≤ Subgroup.normalizer (V : Set A) := le_normalizer_of_comm h.hcomm

theorem hVO [Finite A] : V ≤ pCoreOf 2 M₀ :=
  (orb_facts h.hR2 h.hRM h.hMN h.hM₀R h.hsyl h.hVM₀ h.hV h.hcomm h.hVc h.hNR).1

theorem hOR [Finite A] : pCoreOf 2 M₀ ≤ R :=
  (orb_facts h.hR2 h.hRM h.hMN h.hM₀R h.hsyl h.hVM₀ h.hV h.hcomm h.hVc h.hNR).2.1

theorem hVR [Finite A] : V ≤ R := h.hVO.trans h.hOR

theorem hRC [Finite A] : R ≤ Subgroup.centralizer (V : Set A) :=
  (orb_facts h.hR2 h.hRM h.hMN h.hM₀R h.hsyl h.hVM₀ h.hV h.hcomm h.hVc h.hNR).2.2.1

theorem hrad [Finite A] : pCoreOf 2 (Subgroup.normalizer (R : Set A)) = R :=
  pCoreOf_normalizer_eq h.hR2 h.hMN h.hM₀R h.hsyl h.hNR

theorem V_le_center [Finite A] : V ≤ CFSG.Quasithin.centerOf R := fun v hv =>
  ⟨h.hVR hv, Subgroup.mem_centralizer_iff.mpr fun _r hr =>
    (Subgroup.mem_centralizer_iff.mp (h.hRC hr) v hv).symm⟩

theorem R_ne_bot [Finite A] : R ≠ ⊥ := fun hR => h.hVne (eq_bot_iff.mpr (hR ▸ h.hVR))

theorem not_card_le_four [Finite A] {W : Subgroup A} (hVW : V ≤ W) (hW : Nat.card W ≤ 4) :
    False := by
  have hV4 : Nat.card V ≤ 4 :=
    (Nat.card_le_card_of_injective (Subgroup.inclusion hVW)
      (Subgroup.inclusion_injective hVW)).trans hW
  have h1 := comm_eq_bot_of_card_le_four h.hper h.hM₀V hV4
  rw [h.hcomm] at h1
  exact h.hVne h1

end Setup

structure Iso (f : G₀ →* A) : Prop where
  inj : Function.Injective f
  range : f.range = ⊤

namespace Iso

variable {f : G₀ →* A} (hf : Iso f)
include hf

theorem surj : Function.Surjective f := MonoidHom.range_eq_top.mp hf.range

theorem map_centralizer (H : Subgroup G₀) :
    (Subgroup.centralizer (H : Set G₀)).map f =
      Subgroup.centralizer ((H.map f : Subgroup A) : Set A) := by
  rw [map_centralizer_eq f hf.inj H, hf.range, top_inf_eq]

theorem map_normalizer [Finite A] (H : Subgroup G₀) :
    (Subgroup.normalizer (H : Set G₀)).map f =
      Subgroup.normalizer ((H.map f : Subgroup A) : Set A) := by
  rw [map_normalizer_eq f hf.inj H, hf.range, top_inf_eq]

theorem card_map (H : Subgroup G₀) : Nat.card (H.map f) = Nat.card H :=
  Subgroup.card_map_of_injective hf.inj

theorem map_le_iff {H K : Subgroup G₀} : H.map f ≤ K.map f ↔ H ≤ K :=
  Subgroup.map_le_map_iff_of_injective hf.inj

theorem map_comap (K : Subgroup A) : (K.comap f).map f = K := by
  rw [Subgroup.map_comap_eq, hf.range, top_inf_eq]

theorem conj (x : A) : Iso ((MulAut.conj x).toMonoidHom.comp f) :=
  ⟨(MulAut.conj x).injective.comp hf.inj, by
    rw [MonoidHom.range_comp, hf.range,
      Subgroup.map_top_of_surjective _ (MulAut.conj x).surjective]⟩

omit hf in
theorem map_conj (H : Subgroup G₀) (g : G₀) :
    (H.map (MulAut.conj g).toMonoidHom).map f = (H.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

end Iso

theorem exists_iso [Finite A]
    {S : Subgroup A} (hSn : S.Normal) (hSs : IsSporadic .J4 ↥S)
    (hCS : Subgroup.centralizer (S : Set A) = ⊥) : S = ⊤ ∧ ∃ f : G₀ →* A, Iso f := by
  obtain ⟨e⟩ := hSs
  obtain ⟨ψ⟩ : Nonempty (↥S ≃* G₀) :=
    ⟨e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)⟩
  have hsurj : Function.Surjective (MulAut.conj : ↥S →* MulAut ↥S) := fun α => by
    obtain ⟨g, hg⟩ := CFSG.Quasithin.H13.KGInsp.j4_all_inner ψ α
    exact ⟨g, hg.symm⟩
  have hA : Nat.card A ≤ Nat.card S :=
    (card_le_card_mulAut hSn hCS).trans (Nat.card_le_card_of_surjective _ hsurj)
  have hStop : S = ⊤ :=
    Subgroup.eq_top_of_card_eq S (le_antisymm (Subgroup.card_le_card_group S) hA)
  let f : G₀ →* A := S.subtype.comp (ψ.symm : G₀ →* ↥S)
  have hfi : Function.Injective f := Subtype.val_injective.comp ψ.symm.injective
  have hfr : f.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ S := by rw [hStop]; trivial
    refine ⟨ψ ⟨x, hx⟩, ?_⟩
    show ((ψ.symm (ψ ⟨x, hx⟩) : ↥S) : A) = x
    rw [MulEquiv.symm_apply_apply]
  exact ⟨hStop, f, hfi, hfr⟩

@[expose] noncomputable def maxLoc : Fin 4 → Subgroup G₀
  | 0 => CFSG.Sporadic.J4.Hj
  | 1 => Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set G₀)
  | 2 => Subgroup.normalizer (CFSG.Quasithin.J4Loc.V0 : Set G₀)
  | 3 => CFSG.Quasithin.KGJ4.M4

theorem kw1 [Finite A] (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) {f : G₀ →* A} (hf : Iso f)
    {P : Subgroup A} (hP2 : IsPGroup 2 ↥P) (hP1 : P ≠ ⊥) :
    ∃ i : Fin 4, ∃ g : A, Subgroup.normalizer (P : Set A) ≤
      ((maxLoc i).map f).map (MulAut.conj g).toMonoidHom := by
  set P' := P.comap f with hP'
  have hPP' : P'.map f = P := hf.map_comap P
  have hP'2 : IsPGroup 2 ↥P' := hP2.comap_of_injective f hf.inj
  have hP'1 : P' ≠ ⊥ := fun h => hP1 (by rw [← hPP', h, Subgroup.map_bot])
  have hN : Subgroup.normalizer (P : Set A) = (Subgroup.normalizer (P' : Set G₀)).map f := by
    rw [hf.map_normalizer, hPP']
  obtain ⟨g, hg⟩ := hKW P' hP'2 hP'1
  have key : ∀ i : Fin 4, Subgroup.normalizer (P' : Set G₀) ≤
      (maxLoc i).map (MulAut.conj g).toMonoidHom →
      Subgroup.normalizer (P : Set A) ≤ ((maxLoc i).map f).map (MulAut.conj (f g)).toMonoidHom := by
    intro i hi
    rw [hN, ← Iso.map_conj]
    exact Subgroup.map_mono hi
  rcases hg with h0 | h1 | h2 | h3
  · exact ⟨0, f g, key 0 h0⟩
  · exact ⟨1, f g, key 1 h1⟩
  · exact ⟨2, f g, key 2 h2⟩
  · exact ⟨3, f g, key 3 h3⟩

end CFSG.Quasithin.KGC31.J4

end
