module

public import CFSG.Quasithin.Vol2.KGFactC31M24Lat
public import CFSG.Quasithin.Vol2.KGFactC31M24Base

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31

variable {A : Type} [Group A]

structure Setup (S M₀ R M V : Subgroup A) : Prop where
  hS : S.Normal
  hSs : IsSporadic .M24 ↥S
  hper : ⁅M₀, M₀⁆ = M₀
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
  hNR : Subgroup.normalizer (R : Set A) ≤ M

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

theorem normal_in_normalizer : Subgroup.normalizer (R : Set A) ≤
    Subgroup.normalizer (M₀ : Set A) := h.hNR.trans h.hMN

theorem V_comm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
  have := h.hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

theorem V_le_cent : V ≤ Subgroup.centralizer (V : Set A) := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun y hy => h.V_comm y hy x hx

theorem R_ne_bot [Finite A] : R ≠ ⊥ := fun hR => h.hVne (eq_bot_iff.mpr (hR ▸ h.hVR))

end Setup

structure Iso (f : G₀ →* A) : Prop where
  inj : Function.Injective f
  range : f.range = ⊤

namespace Iso

variable {f : G₀ →* A} (hf : Iso f)
include hf

theorem surj : Function.Surjective f := MonoidHom.range_eq_top.mp hf.range

theorem conj (c : G₀) : Iso (f.comp (MulAut.conj c).toMonoidHom) :=
  ⟨hf.inj.comp (MulAut.conj c).injective, by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective,
      ← MonoidHom.range_eq_map, hf.range]⟩

@[expose] noncomputable def equiv : G₀ ≃* A := MulEquiv.ofBijective f ⟨hf.inj, hf.surj⟩

theorem nonempty_equiv : Nonempty (A ≃* G₀) := ⟨hf.equiv.symm⟩

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

theorem card_A [Finite A] : Nat.card A = 244823040 := by
  rw [← Nat.card_congr hf.equiv.toEquiv, CFSG.Sporadic.Schreier.m24_card]

theorem isSimpleGroup : IsSimpleGroup A := by
  have : IsSimpleGroup NativeSporadic.M24 := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  exact hf.equiv.symm.isSimpleGroup

end Iso

theorem card_normalizer_eq [Finite A]
    {f : G₀ →* A} (hf : Iso f)
    {R : Subgroup A} (hR1 : R ≠ ⊥) (hRcard : Nat.card R ≤ 1024)
    (hrad : pCoreOf 2 (Subgroup.normalizer (R : Set A)) = R) {X : Subgroup G₀}
    (hXN : X.map f ≤ Subgroup.normalizer (R : Set A)) (hX : 1024 ∣ Nat.card X) :
    (Nat.card (Subgroup.normalizer (R : Set A)) = 322560 ∧ Nat.card R = 16) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 64512 ∧ Nat.card R = 64) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 138240 ∧ Nat.card R = 64) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 21504 ∧ Nat.card R = 128) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 9216 ∧ Nat.card R = 256) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 3072 ∧ Nat.card R = 512) ∨
      (Nat.card (Subgroup.normalizer (R : Set A)) = 1024 ∧ Nat.card R = 1024) := by
  have : IsSimpleGroup A := hf.isSimpleGroup
  have hRt : R ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, hf.card_A] at hRcard
    norm_num at hRcard
  obtain ⟨e⟩ := hf.nonempty_equiv
  exact card_normalizer_of_radical ⟨e⟩ hXN (by rw [hf.card_map]; exact hX) hrad
    (normalizer_ne_top hR1 hRt)

theorem card_dvd_of_le [Finite A] {H K : Subgroup A} (h : H ≤ K) : Nat.card H ∣ Nat.card K :=
  Subgroup.card_dvd_of_le h

end CFSG.Quasithin.KGC31.M24

end
