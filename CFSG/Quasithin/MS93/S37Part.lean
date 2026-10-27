module

public import CFSG.Quasithin.MS93.S37Coc

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

abbrev Dt (M L : Subgroup G) {S : Subgroup G} (θ : MulAut ↥S) : Subgroup G :=
  tImage θ (Dq M L)

abbrev Rt (M T L : Subgroup G) {S : Subgroup G} (θ : MulAut ↥S) : Subgroup G :=
  ⁅Uq M T L, Ut M T L θ⁆

theorem tImage_commutator {S : Subgroup G} (θ : MulAut ↥S) {H K : Subgroup G} (hH : H ≤ S)
    (hK : K ≤ S) : tImage θ ⁅H, K⁆ = ⁅tImage θ H, tImage θ K⁆ := by
  refine le_antisymm ?_ ?_
  · have h1 : ⁅H, K⁆ ≤ tImage θ⁻¹ ⁅tImage θ H, tImage θ K⁆ := by
      rw [Subgroup.commutator_le]
      intro h hh k hk
      have hθh : ((θ ⟨h, hH hh⟩ : ↥S) : G) ∈ tImage θ H := mem_tImage.2 ⟨h, hH hh, hh, rfl⟩
      have hθk : ((θ ⟨k, hK hk⟩ : ↥S) : G) ∈ tImage θ K := mem_tImage.2 ⟨k, hK hk, hk, rfl⟩
      have hc := Subgroup.commutator_mem_commutator hθh hθk
      have hcS : ⁅((θ ⟨h, hH hh⟩ : ↥S) : G), ((θ ⟨k, hK hk⟩ : ↥S) : G)⁆ ∈ S :=
        (⁅θ ⟨h, hH hh⟩, θ ⟨k, hK hk⟩⁆ : ↥S).2
      refine mem_tImage.2 ⟨_, hcS, hc, ?_⟩
      have e : (⟨_, hcS⟩ : ↥S) = θ ⁅(⟨h, hH hh⟩ : ↥S), ⟨k, hK hk⟩⁆ := by
        rw [map_commutatorElement]
        rfl
      rw [e, MulAut.inv_apply_self]
      rfl
    have hle : ⁅tImage θ H, tImage θ K⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have haS := tImage_le θ H ha
      have hbS := tImage_le θ K hb
      rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem haS hbS) (S.inv_mem haS)) (S.inv_mem hbS)
    have h2 := tImage_mono' θ h1
    rwa [tImage_tImage_inv' θ hle] at h2
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨h, hhS, hh, rfl⟩ := mem_tImage.1 ha
    obtain ⟨k, hkS, hk, rfl⟩ := mem_tImage.1 hb
    have hc : ⁅h, k⁆ ∈ ⁅H, K⁆ := Subgroup.commutator_mem_commutator hh hk
    refine mem_tImage.2 ⟨⁅h, k⁆, (⁅(⟨h, hhS⟩ : ↥S), ⟨k, hkS⟩⁆ : ↥S).2, hc, ?_⟩
    have e : (⟨⁅h, k⁆, (⁅(⟨h, hhS⟩ : ↥S), ⟨k, hkS⟩⁆ : ↥S).2⟩ : ↥S) =
        ⁅(⟨h, hhS⟩ : ↥S), ⟨k, hkS⟩⁆ := rfl
    rw [e, map_commutatorElement]
    rfl

variable [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

noncomputable def Usub (W : Submodule F (V4 F)) : Subgroup G :=
  ((AddSubgroup.toSubgroup W.toAddSubgroup).comap C.N.β).map (Uq M T L).subtype

theorem mem_Usub {W : Submodule F (V4 F)} {x : G} :
    x ∈ C.Usub W ↔ ∃ hx : x ∈ Uq M T L, C.N.co ⟨x, hx⟩ ∈ W := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem Usub_le (W : Submodule F (V4 F)) : C.Usub W ≤ Uq M T L :=
  Subgroup.map_subtype_le _

theorem A_le_Usub (W : Submodule F (V4 F)) :
    Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ C.Usub W := fun a ha =>
  (C.mem_Usub).2 ⟨ha.1, by rw [(C.N.co_eq_zero_iff _).2 ha]; exact W.zero_mem⟩

section Partner

variable (θ : MulAut ↥(T1 M T L)) (hE : C.rhoIm (Ut M T L θ) = X₂ F)
include hE

theorem comm_Ut_mem {x y : G} (hx : x ∈ pCoreOf 2 M) (hy : y ∈ Ut M T L θ) :
    ∃ u ∈ C.Usub (pt₀ F), u⁻¹ * ⁅y, x⁆ ∈ Dq M L := by
  have hyK : y ∈ L ⊔ pCoreOf 2 M := T1_le_sup (tImage_le θ _ hy)
  have hX : C.rho ⟨y, hyK⟩ ∈ X₂ F := hE ▸ (C.mem_rhoIm).2 ⟨y, hyK, hy, rfl⟩
  obtain ⟨u, hu, hco, hD⟩ := C.comm_mem_of_X₂ hx hyK hX
  exact ⟨u, (C.mem_Usub).2 ⟨hu, hco⟩, hD⟩

theorem Rt_le_Usub : Rt M T L θ ≤ C.Usub (pt₀ F) := by
  rw [Subgroup.commutator_le]
  intro u hu y hy
  have hyM : y ∈ M := C.Ut_le_M T1_le_T θ hy
  have hyK : y ∈ L ⊔ pCoreOf 2 M := T1_le_sup (tImage_le θ _ hy)
  have hc := C.comm_mem_inf C.pCore_le_T1 T1_le_T θ hy hu
  have e : ⁅u, y⁆ = ⁅y, u⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  refine (C.Usub (pt₀ F)).inv_mem ((C.mem_Usub).2 ⟨hc.1, ?_⟩)
  rw [C.co_comm hyM hu hc.1, show C.act hyM = C.act (C.sup_le_M hyK) from rfl,
    C.rho_spec ⟨y, hyK⟩]
  have hX : C.rho ⟨y, hyK⟩ ∈ X₂ F := hE ▸ (C.mem_rhoIm).2 ⟨y, hyK, hy, rfl⟩
  rw [← commSp_X₂]
  exact sub_mem_commSp hX _

theorem exists_Rt {u : G} (hu : u ∈ C.Usub (pt₀ F)) :
    ∃ r ∈ Rt M T L θ, r⁻¹ * u ∈ Uq M T L ⊓ Subgroup.centralizer (L : Set G) := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  obtain ⟨huU, hco⟩ := (C.mem_Usub).1 hu
  obtain ⟨y, hyK, hy, hρ⟩ := (C.mem_rhoIm).1
    (hE.symm ▸ (mem_X₂_iff.2 ⟨1, rfl⟩ : transv (e₁ F) 1 ∈ X₂ F))
  set c := C.N.co ⟨u, huU⟩ (.inl 0) with hc
  obtain ⟨u₁, hu₁⟩ := C.N.co_surj (c • f₁ F)
  have hyM : y ∈ M := C.sup_le_M hyK
  have hc1 := C.comm_mem_inf C.pCore_le_T1 T1_le_T θ hy u₁.2
  have hco1 : C.N.co ⟨⁅y, (u₁ : G)⁆, hc1.1⟩ = C.N.co ⟨u, huU⟩ := by
    rw [C.co_comm hyM u₁.2 hc1.1, show C.act hyM = C.act (C.sup_le_M hyK) from rfl,
      C.rho_spec ⟨y, hyK⟩, hρ, transv_mulVec, form_e₁, hu₁]
    obtain ⟨h1, h2, h3⟩ := mem_pt₀.1 hco
    funext i
    rcases i with i | i <;> fin_cases i
    · simp [f₁, e₁, hc]
    · simp [f₁, e₁, h1]
    · simp [f₁, e₁, h2]
    · simp [f₁, e₁, h3]
  refine ⟨⁅y, (u₁ : G)⁆, ?_, ?_⟩
  · have e : ⁅y, (u₁ : G)⁆ = ⁅(u₁ : G), y⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Rt M T L θ).inv_mem (Subgroup.commutator_mem_commutator u₁.2 hy)
  · rw [← (C.N.co_eq_zero_iff ⟨_, (Uq M T L).mul_mem ((Uq M T L).inv_mem hc1.1) huU⟩)]
    have e : (⟨⁅y, (u₁ : G)⁆⁻¹ * u, (Uq M T L).mul_mem ((Uq M T L).inv_mem hc1.1) huU⟩ :
        ↥(Uq M T L)) = (⟨⁅y, (u₁ : G)⁆, hc1.1⟩ : ↥(Uq M T L))⁻¹ * ⟨u, huU⟩ := rfl
    rw [e, C.N.co_mul, C.N.co_inv, hco1, neg_add_cancel]

end Partner

theorem tImage_Rt (θ : MulAut ↥(T1 M T L)) : tImage θ (Rt M T L θ⁻¹) = Rt M T L θ := by
  rw [tImage_commutator θ C.Uq_le_T1 (tImage_le θ⁻¹ _),
    tImage_tImage_inv' θ C.Uq_le_T1, Subgroup.commutator_comm]

theorem comm_Qt_mem (θ : MulAut ↥(T1 M T L)) (hE' : C.rhoIm (Ut M T L θ⁻¹) = X₂ F) {u z : G}
    (hu : u ∈ Uq M T L) (hz : z ∈ Qt M θ) :
    ∃ r ∈ Rt M T L θ, r⁻¹ * ⁅u, z⁆ ∈ Dt M L θ := by
  obtain ⟨x, hxT, hxQ, rfl⟩ := mem_tImage.1 hz
  have huT : u ∈ tImage θ (Ut M T L θ⁻¹) := by
    rw [tImage_tImage_inv' θ C.Uq_le_T1]
    exact hu
  obtain ⟨u'', hu''T, hu'', rfl⟩ := mem_tImage.1 huT
  obtain ⟨u₁, hu₁, hD₁⟩ := C.comm_Ut_mem θ⁻¹ hE' hxQ hu''
  obtain ⟨r₁, hr₁, ha₁⟩ := C.exists_Rt θ⁻¹ hE' hu₁
  have hr₁T : r₁ ∈ T1 M T L := (Subgroup.commutator_le.2 fun a ha b hb => by
    have haT := C.Uq_le_T1 ha
    have hbT := tImage_le θ⁻¹ _ hb
    rw [commutatorElement_def]
    exact (T1 M T L).mul_mem ((T1 M T L).mul_mem ((T1 M T L).mul_mem haT hbT)
      ((T1 M T L).inv_mem haT)) ((T1 M T L).inv_mem hbT)) hr₁
  have hd : r₁⁻¹ * ⁅u'', x⁆ ∈ Dq M L := by
    have e : r₁⁻¹ * ⁅u'', x⁆ = (r₁⁻¹ * u₁) * (u₁⁻¹ * ⁅u'', x⁆) := by group
    rw [e]
    exact (Dq M L).mul_mem ⟨(C.h.Uq_le_Xq.trans (Xq_le_pCoreOf M)) ha₁.1, ha₁.2⟩ hD₁
  have hdT : r₁⁻¹ * ⁅u'', x⁆ ∈ T1 M T L := C.pCore_le_T1 hd.1
  refine ⟨((θ ⟨r₁, hr₁T⟩ : ↥(T1 M T L)) : G), ?_, ?_⟩
  · rw [← C.tImage_Rt θ]
    exact mem_tImage.2 ⟨r₁, hr₁T, hr₁, rfl⟩
  · refine mem_tImage.2 ⟨_, hdT, hd, ?_⟩
    have e : (⟨r₁⁻¹ * ⁅u'', x⁆, hdT⟩ : ↥(T1 M T L)) =
        (⟨r₁, hr₁T⟩ : ↥(T1 M T L))⁻¹ * ⁅(⟨u'', hu''T⟩ : ↥(T1 M T L)), ⟨x, hxT⟩⁆ := rfl
    rw [e, map_mul, map_inv, map_commutatorElement]
    rfl

end Cfg

end CFSG.Quasithin.MS93.S37
