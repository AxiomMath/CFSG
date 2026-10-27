module

public import CFSG.Quasithin.Background.HL3NineComm
public import CFSG.Quasithin.Background.HMathieuCodeCent

public section

namespace CFSG.Quasithin.H.ModelType

open CFSG.Assembly.LowTwoRank CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem centralizer_eq_bot_of_map (e : V ≃* W) {H : Subgroup (MulAut V)}
    (h : Subgroup.centralizer (H.map (congrHom e) : Set (MulAut W)) = ⊥) :
    Subgroup.centralizer (H : Set (MulAut V)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : congrHom e x ∈ Subgroup.centralizer (H.map (congrHom e) : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hx y hy]
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.2 ((map_eq_one_iff _ (congrHom_injective e)).1 hx')

@[expose] noncomputable def equivMap (e : V ≃* W) (H : Subgroup (MulAut V)) :
    ↥H ≃* ↥(H.map (congrHom e)) :=
  H.equivMapOfInjective (congrHom e) (congrHom_injective e)

section L3Four

open CFSG.Quasithin.H.L3Nine SU3 Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem rhoT_scalGL_eq_one (hK : Nat.card K = (2 ^ 1) ^ 2) (l : Kˣ) :
    rhoT hK (scalGL l) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hl3 : (l : K) ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (l : K) l.ne_zero
    rwa [← Nat.card_eq_fintype_card, hK] at h
  refine MulEquiv.ext fun X => mat_injective ?_
  rw [mat_rhoT_scalGL, bar_apply, MulAut.one_apply, pow_one, ← pow_succ', hl3, one_smul]

theorem centralizer_img_eq_bot (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Subgroup.centralizer (img hK : Set (MulAut (HMod 1 K))) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  obtain ⟨l, rfl⟩ := exists_scalGL_of_commute le_rfl hK (f := f) fun g hg =>
    (Subgroup.mem_centralizer_iff.1 hf _ (rhoT_mem_img hK hg)).symm
  rw [rhoT_scalGL_eq_one hK l]
  exact Subgroup.one_mem _

@[expose] noncomputable def rhoS (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ↥(StatedSL 3 K) →* MulAut (HMod 1 K) :=
  (rhoT hK).comp (StatedSL 3 K).subtype

theorem range_rhoS (hK : Nat.card K = (2 ^ 1) ^ 2) : (rhoS hK).range = img hK := by
  rw [rhoS, MonoidHom.range_comp, Subgroup.range_subtype, img_eq_map]

theorem ker_rhoS (hK : Nat.card K = (2 ^ 1) ^ 2) :
    (rhoS hK).ker = (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  change rhoT hK (g : GL (Fin 3) K) = 1 ↔ _
  constructor
  · intro h
    obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h
    have hd0 : d ≠ 0 := by
      rintro rfl
      have h1 := (g : GL (Fin 3) K).det_ne_zero
      rw [hd, zero_smul, Matrix.det_zero] at h1
      exact h1 rfl
    refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
    have h1 := coe_scalGL (K := K) (Units.mk0 d hd0)
    rw [scalGL, Units.val_mk0] at h1
    rw [h1, hd]
  · rintro ⟨l, hl⟩
    rw [← hl]
    exact rhoT_scalGL_eq_one hK l

@[expose] noncomputable def imgEquivProj (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ↥(img hK) ≃* StatedProj (StatedSL 3 K) :=
  (MulEquiv.subgroupCongr (range_rhoS hK)).symm.trans
    ((QuotientGroup.quotientKerEquivRange (rhoS hK)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (ker_rhoS hK)))

theorem isPSL_of_binaryNine {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : BinaryNineTensor H ⊤ ⊥ 1) : IsPSL 3 2 2 ↥H := by
  obtain ⟨K, _, _, _, hK, hr⟩ := h
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨e, he⟩ := exists_model hK' hr
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, inferInstance,
    inferInstance, by rw [hK], ⟨?_⟩⟩
  exact ((equivMap e H).trans (MulEquiv.subgroupCongr he)).trans (imgEquivProj hK')

theorem centralizer_eq_bot_of_binaryNine {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : BinaryNineTensor H ⊤ ⊥ 1) : Subgroup.centralizer (H : Set (MulAut V)) = ⊥ := by
  obtain ⟨K, _, _, _, hK, hr⟩ := h
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨e, he⟩ := exists_model hK' hr
  exact centralizer_eq_bot_of_map e (by rw [he]; exact centralizer_img_eq_bot hK')

end L3Four

section Mathieu

theorem rhoC10_mog22_injective :
    Function.Injective (rhoC10 mog22 mog22_le_mog22plus) := fun a b hab => by
  have h := rhoC10_mog22plus_injective (a₁ := ⟨a, mog22_le_mog22plus a.2⟩)
    (a₂ := ⟨b, mog22_le_mog22plus b.2⟩) hab
  have h2 : (a : Equiv.Perm (Fin 24)) = b :=
    congrArg (fun x : ↥mog22plus => (x : Equiv.Perm (Fin 24))) h
  exact Subtype.ext h2

@[expose] noncomputable def autPermEquivM24 :
    ↥AutPerm ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24 :=
  (MulEquiv.subgroupCongr (AutPerm_eq_closure.trans bridge_closure_eq_map)).trans
    (CFSG.Blueprint.NativeSporadic.M24.equivMapOfInjective _
      (MulAut.conj bridgeQ⁻¹).injective).symm

theorem isSporadic_m22_of_code22
    {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} (h : MathieuCode22 H ⊤ ⊥) : IsSporadic .M22 ↥H := by
  obtain ⟨e, he⟩ := code22_std h
  let e2 : ↥(H.map (congrHom e)) ≃* ↥(rhoC10 mog22 mog22_le_mog22plus).range :=
    MulEquiv.subgroupCongr he
  let e3 : ↥mog22 ≃* ↥(rhoC10 mog22 mog22_le_mog22plus).range :=
    MonoidHom.ofInjective rhoC10_mog22_injective
  exact ⟨(((equivMap e H).trans e2).trans e3.symm).trans mog22EquivM22⟩

theorem isSporadic_m24_of_code24
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} (h : MathieuCode24 H ⊤ ⊥) :
    IsSporadic .M24 ↥H := by
  obtain ⟨e, he⟩ := code24_std h
  let e2 : ↥(H.map (congrHom e)) ≃* ↥(rhoC11 AutPerm le_rfl).range := MulEquiv.subgroupCongr he
  let e3 : ↥AutPerm ≃* ↥(rhoC11 AutPerm le_rfl).range :=
    MonoidHom.ofInjective (rhoC11_injective AutPerm le_rfl)
  exact ⟨(((equivMap e H).trans e2).trans e3.symm).trans autPermEquivM24⟩

theorem isSporadic_m24_of_cocode24
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} (h : MathieuCocode24 H ⊤ ⊥) :
    IsSporadic .M24 ↥H := by
  obtain ⟨e, he⟩ := cocode24_std h
  let e2 : ↥(H.map (congrHom e)) ≃* ↥(rho11 AutPerm le_rfl).range := MulEquiv.subgroupCongr he
  let e3 : ↥AutPerm ≃* ↥(rho11 AutPerm le_rfl).range :=
    MonoidHom.ofInjective (rho11_injective AutPerm le_rfl)
  exact ⟨(((equivMap e H).trans e2).trans e3.symm).trans autPermEquivM24⟩

theorem centralizer_eq_bot_of_code22
    {H : Subgroup (MulAut V)} (h : MathieuCode22 H ⊤ ⊥) :
    Subgroup.centralizer (H : Set (MulAut V)) = ⊥ := by
  obtain ⟨e, he⟩ := code22_std h
  exact centralizer_eq_bot_of_map e (by rw [he]; exact centralizer_rhoC10_mog22)

theorem centralizer_eq_bot_of_code24 {H : Subgroup (MulAut V)}
    (h : MathieuCode24 H ⊤ ⊥) : Subgroup.centralizer (H : Set (MulAut V)) = ⊥ := by
  obtain ⟨e, he⟩ := code24_std h
  exact centralizer_eq_bot_of_map e (by rw [he]; exact centralizer_rhoC11_autPerm)

theorem centralizer_eq_bot_of_cocode24 {H : Subgroup (MulAut V)}
    (h : MathieuCocode24 H ⊤ ⊥) : Subgroup.centralizer (H : Set (MulAut V)) = ⊥ := by
  obtain ⟨e, he⟩ := cocode24_std h
  exact centralizer_eq_bot_of_map e (by rw [he]; exact centralizer_rho11_autPerm)

end Mathieu

end CFSG.Quasithin.H.ModelType
