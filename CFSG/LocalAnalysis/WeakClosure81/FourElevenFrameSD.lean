module

public import CFSG.LocalAnalysis.WeakClosure81.FourElevenFrame
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
public import CFSG.GH74.Generic.S1.CompIdent
public import CFSG.GroupTheory.SupZpowersIndexTwo
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.E2P.Asc80
open CFSG.Blueprint (LieModel)

variable {Q : Type} [Group Q] [Finite Q]

theorem mem_sylow_of_commutes {T : Subgroup Q} {z : Q} (hT : IsSylowIn 2 T ⊤)
    (hz2 : orderOf z = 2) (hzT : ∀ t ∈ T, t * z = z * t) : z ∈ T := by
  by_contra hznot
  have hzz : z * z = 1 := by
    rw [← pow_two, ← hz2]
    exact pow_orderOf_eq_one z
  have hconj : ∀ p ∈ T, z * p * z⁻¹ ∈ T := by
    intro p hp
    rw [show z * p * z⁻¹ = p by rw [← hzT p hp]; group]
    exact hp
  have hle2 : T.relIndex (T ⊔ Subgroup.zpowers z) ≤ 2 :=
    CFSG.GroupTheory.relIndex_sup_zpowers_le_two hzz hconj
  have hne1 : T.relIndex (T ⊔ Subgroup.zpowers z) ≠ 1 := by
    intro h1
    apply hznot
    have hle : T ⊔ Subgroup.zpowers z ≤ T := Subgroup.relIndex_eq_one.mp h1
    exact hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hne0 : T.relIndex (T ⊔ Subgroup.zpowers z) ≠ 0 := by
    intro h0
    have hcard := Subgroup.relIndex_mul_card (H := T) (K := T ⊔ Subgroup.zpowers z)
    have hTinf : T ⊓ (T ⊔ Subgroup.zpowers z) = T :=
      inf_eq_left.mpr (le_sup_left : T ≤ T ⊔ Subgroup.zpowers z)
    rw [hTinf, h0, zero_mul] at hcard
    exact (Nat.card_pos (α := ↥(T ⊔ Subgroup.zpowers z))).ne' hcard.symm
  have hpos : 0 < T.relIndex (T ⊔ Subgroup.zpowers z) := Nat.pos_of_ne_zero hne0
  have heq2 : T.relIndex (T ⊔ Subgroup.zpowers z) = 2 := by omega
  have hdvd : 2 ∣ T.relIndex ⊤ := by
    rw [Subgroup.relIndex_top_right]
    rw [← heq2]
    exact Subgroup.relIndex_dvd_index_of_le le_sup_left
  exact hT.not_dvd_relIndex hdvd

theorem semidihedral_quarter_conj {m : ℕ} (hm4 : 4 ≤ m) {x : CFSG.Open.SemidihedralGroup m}
    (hx2 : orderOf x = 2)
    (hxz : x ∉ Subgroup.zpowers (CFSG.Semidihedral.z m)) :
    x * (CFSG.Semidihedral.r m ^ 2 ^ (m - 3)) * x⁻¹ =
      (CFSG.Semidihedral.r m ^ 2 ^ (m - 3))⁻¹ := by
  have hm3 : 3 ≤ m := by omega
  have hxz' : x ∉ Subgroup.zpowers
      ((CFSG.Semidihedral.r m) ^ (2 ^ (m - 1) / 2)) := by
    rw [show 2 ^ (m - 1) / 2 = CFSG.Semidihedral.half m from
      CFSG.Semidihedral.modulus_div_two m (by omega)]
    exact hxz
  obtain ⟨i, -, hxi⟩ :=
    CFSG.Semidihedral.Local.exists_reflection_coordinates (n := m) hm4 (MulEquiv.refl _) x hx2 hxz'
  have hxi' : x = CFSG.Semidihedral.element m hm3 i 1 := by simpa using hxi
  have hq : CFSG.Semidihedral.r m ^ 2 ^ (m - 3) =
      CFSG.Semidihedral.element m hm3
        ((2 ^ (m - 3) : ℕ) : ZMod (CFSG.Semidihedral.modulus m)) 0 := by
    rw [CFSG.Semidihedral.rotation_generator_eq_element m hm3,
      CFSG.Semidihedral.element_rotation_pow]
    congr 1
    simp
  rw [hxi', hq, CFSG.Semidihedral.conjugate_rotation_by_reflection m hm3,
    CFSG.Semidihedral.Local.twist_mul_quarter hm4, CFSG.Semidihedral.element_rotation_inv]

theorem sylow_semidihedral_of_lieModel {L : Subgroup Q} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : (LieModel ↥L .PSL 3 p 1 ∧ p % 4 = 3) ∨
      (LieModel ↥L .PSU 3 p 1 ∧ p % 4 = 1)) (S : Sylow 2 ↥L) :
    ∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥S ≃* CFSG.Open.SemidihedralGroup m) := by
  rcases hL with ⟨hL, hq⟩ | ⟨hL, hq⟩
  · have hmodel : StatedClassicalModel ↥L .PSL 3 p 1 :=
      LieModel.statedClassicalModel hL (by decide)
    have hLn : CFSG.GH74.GLS.IVK.IsLnEps 3 ↥L 1 (p ^ 1) :=
      CFSG.GH74.Generic.S1.isLnEps_of_model (Or.inl ⟨rfl, hmodel⟩)
    have hq' : p ^ 1 % 4 = 3 := by simpa using hq
    simpa using CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_L3_sd hp hp2 hLn hq' S
  · have hmodel : StatedClassicalModel ↥L .PSU 3 p 1 :=
      LieModel.statedClassicalModel hL (by decide)
    have hLn : CFSG.GH74.GLS.IVK.IsLnEps 3 ↥L (-1) (p ^ 1) :=
      CFSG.GH74.Generic.S1.isLnEps_of_model (Or.inr ⟨rfl, hmodel⟩)
    have hq' : p ^ 1 % 4 = 1 := by simpa using hq
    have hp1 : 1 < p ^ 1 := by simpa using hp.one_lt
    simpa using CFSG.GH74.GLS.IVK.Proofs2.Lemma44b.sylow_U3_sd hp hp2 hLn hq' hp1 S

omit [Finite Q] in
theorem dihedral_four_order_four_of_mem {H : Subgroup Q} {ρ u y : Q}
    (hgen : Subgroup.closure {ρ, u} = H)
    (hρ4 : orderOf ρ = 4) (hu2 : u ^ 2 = 1) (hrel : u * ρ * u⁻¹ = ρ⁻¹)
    (huρ : u ∉ Subgroup.zpowers ρ) (hyH : y ∈ H) (hy4 : orderOf y = 4) :
    y = ρ ∨ y = ρ⁻¹ := by
  have hρH : ρ ∈ H := by rw [← hgen]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have huH : u ∈ H := by
    rw [← hgen]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let ρH : H := ⟨ρ, hρH⟩
  let uH : H := ⟨u, huH⟩
  have hgenH : Subgroup.closure ({ρH, uH} : Set H) = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, MonoidHom.map_closure]
    have himg : (H.subtype : H →* Q) '' ({ρH, uH} : Set H) = ({ρ, u} : Set Q) := by
      rw [Set.image_pair]
      rfl
    rw [himg]
    exact hgen
  have hρH4 : orderOf ρH = 4 := by rw [← Subgroup.orderOf_coe, hρ4]
  have huH2 : uH ^ 2 = 1 := Subtype.ext (by simpa using hu2)
  have hrelH : uH * ρH * uH⁻¹ = ρH⁻¹ := Subtype.ext (by simpa using hrel)
  have huρH : uH ∉ Subgroup.zpowers ρH := by
    intro h
    apply huρ
    have h' : H.subtype uH ∈ (Subgroup.zpowers ρH).map H.subtype :=
      Subgroup.mem_map_of_mem _ h
    simpa [MonoidHom.map_zpowers, ρH, uH] using h'
  obtain ⟨e, he1, -⟩ :=
    CFSG.Semidihedral.Local.dihedral_normal_form (u := ρH) (x := uH) (h := 4)
      hgenH hρH4 huρH huH2 hrelH
  have hyH4 : orderOf (⟨y, hyH⟩ : H) = 4 := by rw [← Subgroup.orderOf_coe, hy4]
  set d : DihedralGroup 4 := e.symm ⟨y, hyH⟩ with hd
  have hd4 : orderOf d = 4 := by rw [← MulEquiv.orderOf_eq e, MulEquiv.apply_symm_apply, hyH4]
  rcases d with i | i
  · have hval : i.val = 1 ∨ i.val = 3 := by
      have h := hd4
      rw [DihedralGroup.orderOf_r] at h
      have hdiv : 4 / Nat.gcd 4 i.val = 4 := h
      have hgpos : 0 < Nat.gcd 4 i.val := Nat.gcd_pos_of_pos_left _ (by norm_num)
      have hgle : Nat.gcd 4 i.val ≤ 4 :=
        Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 4 i.val)
      have hcases : Nat.gcd 4 i.val = 1 ∨ Nat.gcd 4 i.val = 2 ∨
          Nat.gcd 4 i.val = 3 ∨ Nat.gcd 4 i.val = 4 := by omega
      have hgcd : Nat.gcd 4 i.val = 1 := by
        rcases hcases with h1 | h2 | h3 | h4
        · exact h1
        · exfalso; rw [h2] at hdiv; norm_num at hdiv
        · exfalso; rw [h3] at hdiv; norm_num at hdiv
        · exfalso; rw [h4] at hdiv; norm_num at hdiv
      have hi : i.val < 4 := ZMod.val_lt i
      interval_cases i.val <;> simp_all
    have hi : i = 1 ∨ i = 3 := by
      rcases hval with h1 | h3
      · left
        apply ZMod.val_injective 4
        rw [ZMod.val_one'' (by norm_num : (4 : ℕ) ≠ 1)]
        exact h1
      · right
        apply ZMod.val_injective 4
        change i.val = 3
        exact h3
    rcases hi with rfl | rfl
    · left
      have h1 : (⟨y, hyH⟩ : H) = ρH := by
        calc (⟨y, hyH⟩ : H) = e (e.symm ⟨y, hyH⟩) := (e.apply_symm_apply _).symm
          _ = e (DihedralGroup.r 1) := by rw [← hd]
          _ = ρH := he1
      exact Subtype.ext_iff.mp h1
    · right
      have h3 : (⟨y, hyH⟩ : H) = ρH ^ 3 := by
        calc (⟨y, hyH⟩ : H) = e (e.symm ⟨y, hyH⟩) := (e.apply_symm_apply _).symm
          _ = e (DihedralGroup.r 3) := by rw [← hd]
          _ = e ((DihedralGroup.r 1) ^ 3) := by
                rw [show (DihedralGroup.r 3 : DihedralGroup 4) = (DihedralGroup.r 1) ^ 3 from
                  (DihedralGroup.r_one_pow 3).symm]
          _ = (e (DihedralGroup.r 1)) ^ 3 := by rw [map_pow]
          _ = ρH ^ 3 := by rw [he1]
      have hinv : ρH ^ 3 = ρH⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← pow_succ', show 3 + 1 = 4 by norm_num, ← hρH4, pow_orderOf_eq_one]
      exact Subtype.ext_iff.mp (h3.trans hinv)
  · have h2 : orderOf (DihedralGroup.sr i) = 2 := DihedralGroup.orderOf_sr i
    omega

theorem exists_frame_four_sd {L : Subgroup Q} [L.Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : (LieModel ↥L .PSL 3 p 1 ∧ p % 4 = 3) ∨ (LieModel ↥L .PSU 3 p 1 ∧ p % 4 = 1))
    {T : Subgroup Q} {z u : Q}
    (hT : IsSylowIn 2 T ⊤) (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) (huT : u ∈ T) (huL : u ∈ L) (hu2 : orderOf u = 2)
    (huz : u ≠ z) :
    ∃ W : Subgroup Q, W ≤ L ∧ IsElemAbelian 2 W ∧ Nat.card W = 4 ∧ z ∈ W ∧
      T ⊓ centralizer ({u} : Set Q) ≤ normalizer (W : Set Q) ∧
      u ∉ centralizer (W : Set Q) ∧
      IsSylowIn 2 (T ⊓ (L ⊓ normalizer (W : Set Q))) (L ⊓ normalizer (W : Set Q)) := by
  classical
  have hzT' : z ∈ T := mem_sylow_of_commutes hT hz2 hzT
  set S : Subgroup Q := T ⊓ L with hSdef
  have hS : IsSylowIn 2 S L := by
    have hLnorm : (L.subgroupOf (⊤ : Subgroup Q)).Normal := by infer_instance
    simpa [S] using IsSylowIn.inf_normal (p := 2) hT (le_top : L ≤ ⊤) hLnorm
  have huS : u ∈ S := ⟨huT, huL⟩
  have hzS : z ∈ S := ⟨hzT', hzL⟩
  obtain ⟨m, hm4, ⟨e⟩⟩ := sylow_semidihedral_of_lieModel hp hp2 hL hS.toSylow
  let eS : ↥S ≃* CFSG.Open.SemidihedralGroup m :=
    (Subgroup.subgroupOfEquivOfLe hS.le).symm.trans e
  let uS : ↥S := ⟨u, huS⟩
  let zS : ↥S := ⟨z, hzS⟩
  have hzS_ord : orderOf zS = 2 := by
    rw [Subgroup.orderOf_mk]; exact hz2
  have huS_ord : orderOf uS = 2 := by
    rw [Subgroup.orderOf_mk]; exact hu2
  have hzuS : zS ≠ uS := by
    intro h
    exact huz (Subtype.ext_iff.mp h).symm
  have hzS_center : zS ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact hzT s.1 s.2.1
  have hfinSD : Finite (CFSG.Open.SemidihedralGroup m) :=
    CFSG.Semidihedral.presentation_finite m (by omega)
  have hzS_eq : eS zS = CFSG.Semidihedral.z m := by
    have hzc : eS zS ∈ Subgroup.center (CFSG.Open.SemidihedralGroup m) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨s, rfl⟩ := eS.surjective g
      simpa only [map_mul] using congrArg eS (Subgroup.mem_center_iff.mp hzS_center s)
    rw [CFSG.Semidihedral.center_eq_zpowers m hm4] at hzc
    have hzord : orderOf (eS zS) = 2 := by
      rw [MulEquiv.orderOf_eq eS zS, hzS_ord]
    have hzm2 : orderOf (CFSG.Semidihedral.z m) = 2 :=
      CFSG.Semidihedral.orderOf_z m (by omega)
    rcases (@CFSG.Semidihedral.KleinFourOddKernel.mem_zpowers_involution
      (CFSG.Open.SemidihedralGroup m) _ hfinSD
      (CFSG.Semidihedral.z m) (eS zS) hzm2).mp hzc with h1 | h1
    · rw [h1, orderOf_one] at hzord; omega
    · exact h1
  let K : Subgroup ↥S := CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup zS uS
  have hK : IsKleinFour K :=
    CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup_isKleinFour zS uS
      hzS_center hzS_ord huS_ord hzuS
  have huzK : uS ∉ Subgroup.zpowers zS := by
    intro h
    have h1 := (CFSG.Semidihedral.KleinFourOddKernel.mem_zpowers_involution
      zS uS hzS_ord).mp h
    rcases h1 with h1 | h1
    · rw [h1] at huS_ord; simp at huS_ord
    · exact huz (Subtype.ext_iff.mp h1)
  obtain ⟨hKfacts, hNfacts, hconj⟩ :=
    CFSG.Semidihedral.Local.semidihedral_four_subgroup_centralizers m hm4 eS.symm
  let rS : ↥S := eS.symm (CFSG.Semidihedral.r m)
  let ρS : ↥S := rS ^ (2 ^ (m - 1) / 4)
  let wS : ↥S := ρS * uS
  let W_S : Subgroup ↥S := CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup zS wS
  have hzS_pre : zS = eS.symm (CFSG.Semidihedral.z m) := by
    rw [← hzS_eq, MulEquiv.symm_apply_apply]
  have hz_m_eq : (eS.symm (CFSG.Semidihedral.r m)) ^ (2 ^ (m - 1) / 2) = zS := by
    rw [show 2 ^ (m - 1) / 2 = CFSG.Semidihedral.half m from
      CFSG.Semidihedral.modulus_div_two m (by omega)]
    rw [← map_pow (eS.symm) (CFSG.Semidihedral.r m) (CFSG.Semidihedral.half m)]
    change eS.symm (CFSG.Semidihedral.z m) = zS
    exact hzS_pre.symm
  have hzK : zS ∈ K := by
    simpa [hz_m_eq] using (hNfacts K hK).1
  have hCK : Subgroup.centralizer (K : Set ↥S) = K := by
    simpa [hz_m_eq] using (hNfacts K hK).2.1
  have huzK' : uS ∉ Subgroup.zpowers
      ((eS.symm (CFSG.Semidihedral.r m)) ^ (2 ^ (m - 1) / 2)) := by
    rwa [hz_m_eq]
  have huSK : uS ∈ K := by
    change uS ∈ CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup zS uS
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers uS)
  have hNK := (hNfacts K hK).2.2 uS huSK huzK'
  have hρS_ord : orderOf ρS = 4 := by
    simp only [ρS, rS]
    rw [← MulEquiv.orderOf_eq eS, map_pow, MulEquiv.apply_symm_apply]
    rw [show 2 ^ (m - 1) / 4 = 2 ^ (m - 3) from
      CFSG.Semidihedral.modulus_div_four m hm4]
    exact CFSG.QuasiDihedralFusion.orderOf_sdV hm4
  have huS_sq : uS * uS = 1 := by
    rw [← pow_two, ← huS_ord]
    exact pow_orderOf_eq_one uS
  have hx2 : orderOf (eS uS) = 2 := by
    rw [MulEquiv.orderOf_eq eS uS, huS_ord]
  have hxz : eS uS ∉ Subgroup.zpowers (CFSG.Semidihedral.z m) := by
    intro h
    have h1 := (@CFSG.Semidihedral.KleinFourOddKernel.mem_zpowers_involution
      (CFSG.Open.SemidihedralGroup m) _ hfinSD
      (CFSG.Semidihedral.z m) (eS uS)
      (CFSG.Semidihedral.orderOf_z m (by omega))).mp h
    rcases h1 with h1 | h1
    · have : orderOf (eS uS) = 1 := by rw [h1, orderOf_one]
      omega
    · apply huz
      have : uS = zS := by
        apply eS.injective
        rw [hzS_eq]
        exact h1
      exact Subtype.ext_iff.mp this
  have hρS_eq : eS ρS = CFSG.Semidihedral.r m ^ 2 ^ (m - 3) := by
    simp only [ρS, rS]
    rw [map_pow, MulEquiv.apply_symm_apply]
    rw [show 2 ^ (m - 1) / 4 = 2 ^ (m - 3) from
      CFSG.Semidihedral.modulus_div_four m hm4]
  have hxz' : eS uS ∉ Subgroup.zpowers
      ((CFSG.Semidihedral.r m) ^ (2 ^ (m - 1) / 2)) := by
    rw [show 2 ^ (m - 1) / 2 = CFSG.Semidihedral.half m from
      CFSG.Semidihedral.modulus_div_two m (by omega)]
    exact hxz
  obtain ⟨i, -, hxi⟩ :=
    CFSG.Semidihedral.Local.exists_reflection_coordinates (n := m) hm4 (MulEquiv.refl _)
      (eS uS) hx2 hxz'
  have hxi' : eS uS = CFSG.Semidihedral.element m (by omega) i 1 := by
    simpa using hxi
  have hq : CFSG.Semidihedral.r m ^ 2 ^ (m - 3) =
      CFSG.Semidihedral.element m (by omega)
        ((2 ^ (m - 3) : ℕ) : ZMod (CFSG.Semidihedral.modulus m)) 0 := by
    rw [CFSG.Semidihedral.rotation_generator_eq_element m (by omega),
      CFSG.Semidihedral.element_rotation_pow]
    congr 1
    simp
  have hwS_coord : eS wS = CFSG.Semidihedral.element m (by omega)
      (((2 ^ (m - 3) : ℕ) : ZMod (CFSG.Semidihedral.modulus m)) + i) 1 := by
    simp only [wS]
    rw [map_mul, hρS_eq, hxi', hq, ← CFSG.Semidihedral.element_rotation_mul]
  have hwS_sq : wS * wS = 1 := by
    apply eS.injective
    rw [map_mul, map_one]
    have hrel := semidihedral_quarter_conj hm4 hx2 hxz
    rw [hwS_coord]
    have hcoord : CFSG.Semidihedral.element m (by omega)
        (((2 ^ (m - 3) : ℕ) : ZMod (CFSG.Semidihedral.modulus m)) + i) 1 =
        CFSG.Semidihedral.r m ^ 2 ^ (m - 3) * eS uS := by
      calc CFSG.Semidihedral.element m (by omega)
            (((2 ^ (m - 3) : ℕ) : ZMod (CFSG.Semidihedral.modulus m)) + i) 1 =
          CFSG.Semidihedral.element m (by omega)
            ((2 ^ (m - 3) : ℕ) : ZMod (CFSG.Semidihedral.modulus m)) 0 *
            CFSG.Semidihedral.element m (by omega) i 1 := by
            rw [CFSG.Semidihedral.element_rotation_mul]
        _ = CFSG.Semidihedral.r m ^ 2 ^ (m - 3) * eS uS := by
            rw [hq, hxi']
    rw [hcoord]
    calc CFSG.Semidihedral.r m ^ 2 ^ (m - 3) * eS uS *
          (CFSG.Semidihedral.r m ^ 2 ^ (m - 3) * eS uS)
        = CFSG.Semidihedral.r m ^ 2 ^ (m - 3) *
            (eS uS * CFSG.Semidihedral.r m ^ 2 ^ (m - 3) * (eS uS)⁻¹) *
            (eS uS * eS uS) := by group
      _ = CFSG.Semidihedral.r m ^ 2 ^ (m - 3) *
            (CFSG.Semidihedral.r m ^ 2 ^ (m - 3))⁻¹ * 1 := by
          rw [hrel, show eS uS * eS uS = 1 from by
            simpa [sq, hx2] using pow_orderOf_eq_one (eS uS)]
      _ = 1 := by group
  have hwS_ne_one : wS ≠ 1 := by
    intro h
    have h1 : eS wS = 1 := by rw [h, map_one]
    rw [hwS_coord] at h1
    have h2 := (CFSG.Semidihedral.element_eq_one_iff m (by omega) _ 1).mp h1
    exact absurd h2.2 (by decide)
  have hwS_ne_z : wS ≠ zS := by
    intro h
    have h1 : eS wS = CFSG.Semidihedral.z m := by rw [h, hzS_eq]
    rw [hwS_coord] at h1
    rw [CFSG.Semidihedral.z_eq_element m (by omega)] at h1
    rw [CFSG.Semidihedral.element_eq_iff] at h1
    exact absurd h1.2 (by decide)
  have hwS_ord : orderOf wS = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) hwS_ne_one
  let W_S : Subgroup ↥S := CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup zS wS
  have hW : IsKleinFour W_S :=
    CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup_isKleinFour zS wS
      hzS_center hzS_ord hwS_ord (Ne.symm hwS_ne_z)
  have hzW : zS ∈ W_S := by
    change zS ∈ CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup zS wS
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers zS)
  have hwW : wS ∈ W_S := by
    change wS ∈ CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup zS wS
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers wS)
  have hCW : Subgroup.centralizer (W_S : Set ↥S) = W_S := by
    simpa [hz_m_eq] using (hNfacts W_S hW).2.1
  have hρS_ne_one : ρS ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hρS_ord
    omega
  have hρS_ne_z : ρS ≠ zS := by
    intro h
    rw [h, hzS_ord] at hρS_ord
    omega
  have hρw : ρS = wS * uS := by
    simp only [wS]
    rw [mul_assoc, huS_sq, mul_one]
  have hcomm : wS * zS = zS * wS := Subgroup.mem_center_iff.mp hzS_center wS
  have huSW : uS ∉ W_S := by
    intro h
    have hmem := (CFSG.Semidihedral.KleinFourOddKernel.mem_fourSubgroup
      zS wS uS hzS_center hzS_ord hwS_ord).mp h
    rcases hmem with h1 | h1 | h1 | h1
    · rw [h1, orderOf_one] at huS_ord
      omega
    · exact hzuS h1.symm
    · exact hρS_ne_one (by rw [hρw, ← h1, huS_sq])
    · have hz : ρS = zS := by
        calc ρS = wS * uS := hρw
          _ = wS * (zS * wS) := by rw [h1]
          _ = (wS * zS) * wS := by group
          _ = (zS * wS) * wS := by rw [hcomm]
          _ = zS * (wS * wS) := by group
          _ = zS := by rw [hwS_sq, mul_one]
      exact hρS_ne_z hz
  have huS_not_cent : uS ∉ Subgroup.centralizer (W_S : Set ↥S) := by
    rw [hCW]
    exact huSW
  let W : Subgroup Q := W_S.map S.subtype
  have hWle : W ≤ L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact hS.le y.2
  have hW4 : Nat.card W = 4 := by
    change Nat.card (W_S.map S.subtype) = 4
    rw [Subgroup.card_map_of_injective S.subtype_injective, hW.card_four]
  have hWk : IsKleinFour W := by
    change IsKleinFour (W_S.map S.subtype)
    exact CFSG.Semidihedral.Local.isKleinFour_of_mulEquiv
      (Subgroup.equivMapOfInjective W_S S.subtype S.subtype_injective)
  have hWel : IsElemAbelian 2 W :=
    ⟨IsKleinFour.isMulCommutative, fun x hx => by
      have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : W)
      rw [IsKleinFour.exponent_two] at h
      simpa using congrArg Subtype.val h⟩
  have hzW : z ∈ W := by
    change z ∈ W_S.map S.subtype
    exact Subgroup.mem_map_of_mem _ hzW
  have huW : u ∉ Subgroup.centralizer (W : Set Q) := by
    intro hu
    apply huS_not_cent
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    apply Subtype.ext
    have hwW : S.subtype w ∈ W := Subgroup.mem_map_of_mem _ hw
    exact Subgroup.mem_centralizer_iff.mp hu (S.subtype w) hwW
  let ρQ : Q := S.subtype ρS
  have hρQ4 : orderOf ρQ = 4 := by
    show orderOf (ρS : Q) = 4
    rw [Subgroup.orderOf_coe, hρS_ord]
  have hρS_sq : ρS ^ 2 = zS := by
    apply eS.injective
    rw [map_pow, hρS_eq, hzS_eq, hq]
    rw [CFSG.Semidihedral.element_rotation_pow]
    rw [show (2 : ℕ) • ((2 ^ (m - 3) : ℕ) : ZMod (CFSG.Semidihedral.modulus m)) =
      ((2 ^ (m - 2) : ℕ) : ZMod (CFSG.Semidihedral.modulus m)) by
        rw [nsmul_eq_mul, ← Nat.cast_mul]
        congr 1
        rw [← pow_succ']
        congr 1
        omega]
    rw [CFSG.Semidihedral.z_eq_element m (by omega)]
    simp [CFSG.Semidihedral.half]
  have hrelS : uS * ρS * uS⁻¹ = ρS⁻¹ := by
    apply eS.injective
    simpa only [map_mul, map_inv, hρS_eq] using semidihedral_quarter_conj hm4 hx2 hxz
  have hrelQ : u * ρQ * u⁻¹ = ρQ⁻¹ := by
    have h := congrArg S.subtype hrelS
    simpa [ρQ, uS] using h
  have huρQ : u ∉ Subgroup.zpowers ρQ := by
    intro h
    have hcomm : Commute u ρQ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      rw [← hk]
      exact (Commute.refl ρQ).zpow_left k
    have h1 : ρQ = ρQ⁻¹ := by
      calc ρQ = u * ρQ * u⁻¹ := by rw [hcomm.eq]; group
        _ = ρQ⁻¹ := hrelQ
    have h2 : ρQ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [h1]
      exact mul_inv_cancel ρQ
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hρQ4] at h3
    norm_num at h3
  let KQ : Subgroup Q := Subgroup.closure {z, u}
  let HQ : Subgroup Q := Subgroup.closure {ρQ, u}
  have hKQ_eq : KQ = K.map S.subtype := by
    change Subgroup.closure {z, u} =
      (CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup zS uS).map S.subtype
    rw [CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact CFSG.Semidihedral.Local.closure_pair_eq_sup z u
  have hKQS : KQ ≤ S := by
    rw [hKQ_eq]
    exact Subgroup.map_subtype_le K
  have hKQ_sub : KQ.subgroupOf S = K := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hKQS]
    exact hKQ_eq
  have hHQ_eq : HQ = (Subgroup.normalizer (K : Set ↥S)).map S.subtype := by
    change Subgroup.closure {ρQ, u} = _
    rw [hNK.1, MonoidHom.map_closure]
    congr 1
    ext x
    simp [ρQ, uS, ρS, rS]
  have hHQ_eq2 : HQ = S ⊓ Subgroup.normalizer (KQ : Set Q) := by
    have h := CFSG.Semidihedral.Local.normalizer_subgroupOf_eq (H := KQ) (K := S) hKQS
    calc HQ = (Subgroup.normalizer (K : Set ↥S)).map S.subtype := hHQ_eq
      _ = (Subgroup.normalizer ((KQ.subgroupOf S : Subgroup ↥S) : Set ↥S)).map S.subtype := by
            rw [hKQ_sub]
      _ = ((Subgroup.normalizer (KQ : Set Q)).subgroupOf S).map S.subtype := by rw [h]
      _ = S ⊓ Subgroup.normalizer (KQ : Set Q) := by
            rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hW_eq : W = Subgroup.closure {z, S.subtype wS} := by
    change (CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup zS wS).map S.subtype = _
    rw [CFSG.Semidihedral.KleinFourOddKernel.fourSubgroup, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact (CFSG.Semidihedral.Local.closure_pair_eq_sup z (S.subtype wS)).symm
  have hw_eq : S.subtype wS = ρQ * u := by
    change S.subtype (ρS * uS) = S.subtype ρS * u
    rw [map_mul]
    rfl
  have hT_le_NW : T ⊓ Subgroup.centralizer ({u} : Set Q) ≤
      Subgroup.normalizer (W : Set Q) := by
    intro t ht
    have hLN : L.Normal := inferInstance
    have htT : t ∈ T := ht.1
    have htu : u * t = t * u :=
      Subgroup.mem_centralizer_iff.mp ht.2 u (by simp)
    have htz : t * z = z * t := hzT t htT
    have htu' : t * u * t⁻¹ = u := by
      rw [show t * u = u * t from htu.symm, mul_assoc, mul_inv_cancel, mul_one]
    have htz' : t * z * t⁻¹ = z := by
      rw [htz, mul_assoc, mul_inv_cancel, mul_one]
    have htS : t ∈ Subgroup.normalizer (S : Set Q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        exact ⟨T.mul_mem (T.mul_mem htT hs.1) (T.inv_mem htT),
          hLN.conj_mem s hs.2 t⟩
      · intro hs
        have h2 : t⁻¹ * (t * s * t⁻¹) * t = s := by group
        refine ⟨?_, ?_⟩
        · rw [← h2]
          exact T.mul_mem (T.mul_mem (T.inv_mem htT) hs.1) htT
        · rw [← h2]
          simpa using hLN.conj_mem _ hs.2 t⁻¹
    have htK : t ∈ Subgroup.normalizer (KQ : Set Q) := by
      change t ∈ Subgroup.normalizer (Subgroup.closure ({z, u} : Set Q))
      apply Subgroup.mem_normalizer_fintype
      intro x hx
      have hmap : ∀ y ∈ Subgroup.closure ({z, u} : Set Q), t * y * t⁻¹ ∈
          Subgroup.closure ({z, u} : Set Q) := by
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem y hy =>
            rcases hy with rfl | rfl
            · rw [htz']
              exact Subgroup.subset_closure (Set.mem_insert _ _)
            · rw [htu']
              exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        | one => simp
        | mul a b ha hb iha ihb =>
            rw [show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group]
            exact Subgroup.mul_mem _ iha ihb
        | inv a ha iha =>
            rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ by group]
            exact Subgroup.inv_mem _ iha
      exact hmap x hx
    have htN : t ∈ Subgroup.normalizer (Subgroup.normalizer (KQ : Set Q)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change (Subgroup.normalizer (KQ : Set Q)).map (MulAut.conj t).toMonoidHom =
        Subgroup.normalizer (KQ : Set Q)
      rw [Subgroup.map_equiv_normalizer_eq]
      change Subgroup.normalizer ((KQ.map (MulAut.conj t) : Subgroup Q) : Set Q) =
        Subgroup.normalizer (KQ : Set Q)
      rw [(Subgroup.mem_normalizer_iff_map_conj_eq).mp htK]
    have htHQ : t ∈ Subgroup.normalizer (HQ : Set Q) := by
      rw [hHQ_eq2]
      apply Subgroup.mem_normalizer_fintype
      intro x hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp htS x).mp hx.1,
        (Subgroup.mem_normalizer_iff.mp htN x).mp hx.2⟩
    have hρQ_mem : ρQ ∈ HQ := Subgroup.subset_closure (Set.mem_insert _ _)
    have htρ : t * ρQ * t⁻¹ ∈ HQ :=
      (Subgroup.mem_normalizer_iff.mp htHQ ρQ).mp hρQ_mem
    have hy4 : orderOf (t * ρQ * t⁻¹) = 4 := by
      rw [← MulAut.conj_apply t ρQ, MulEquiv.orderOf_eq, hρQ4]
    have hcases := dihedral_four_order_four_of_mem (H := HQ) (ρ := ρQ) (u := u)
      (y := t * ρQ * t⁻¹) rfl hρQ4 (by rw [← hu2]; exact pow_orderOf_eq_one u)
      hrelQ huρQ htρ hy4
    have htw : t * (S.subtype wS) * t⁻¹ ∈
        Subgroup.closure {z, S.subtype wS} := by
      rw [hw_eq]
      rcases hcases with hcase | hcase
      · rw [show t * (ρQ * u) * t⁻¹ = (t * ρQ * t⁻¹) * (t * u * t⁻¹) by group,
          hcase, htu']
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · have hzinv : ρQ⁻¹ = z * ρQ := by
          have h4 : ρQ * ρQ ^ 3 = 1 := by
            rw [← pow_succ', show 1 + 3 = 4 by norm_num, ← hρQ4, pow_orderOf_eq_one]
          calc ρQ⁻¹ = ρQ ^ 3 := (eq_inv_of_mul_eq_one_right h4).symm
            _ = ρQ ^ 2 * ρQ := by rw [pow_succ]
            _ = z * ρQ := by
                rw [show ρQ ^ 2 = z from by
                  have h := congrArg S.subtype hρS_sq
                  simpa [ρQ] using h]
        rw [show t * (ρQ * u) * t⁻¹ = (t * ρQ * t⁻¹) * (t * u * t⁻¹) by group,
          hcase, htu', hzinv, mul_assoc]
        exact Subgroup.mul_mem _
          (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    rw [hW_eq]
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hmap : ∀ y ∈ Subgroup.closure ({z, S.subtype wS} : Set Q), t * y * t⁻¹ ∈
        Subgroup.closure ({z, S.subtype wS} : Set Q) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy =>
          rcases hy with rfl | rfl
          · rw [htz']
            exact Subgroup.subset_closure (Set.mem_insert _ _)
          · exact htw
      | one => simp
      | mul a b ha hb iha ihb =>
          rw [show t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) by group]
          exact Subgroup.mul_mem _ iha ihb
      | inv a ha iha =>
          rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ by group]
          exact Subgroup.inv_mem _ iha
    exact hmap x hx

  let M : Subgroup Q := L ⊓ Subgroup.centralizer (W : Set Q)
  let N : Subgroup Q := L ⊓ Subgroup.normalizer (W : Set Q)
  have hframe := exists_monomial_frame hp hp2
    (hL.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)) hWle hWel hW4
  obtain ⟨hMab, hMN, -⟩ := hframe
  have hWS : W ≤ S := by
    change W_S.map S.subtype ≤ S
    exact Subgroup.map_subtype_le W_S
  have hW_sub : W.subgroupOf S = W_S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hWS]
  have hCSW : S ⊓ Subgroup.centralizer (W : Set Q) = W := by
    have h := CFSG.Semidihedral.Local.centralizer_subgroupOf_eq (H := W) (K := S) hWS
    rw [hW_sub, hCW] at h
    calc S ⊓ Subgroup.centralizer (W : Set Q)
        = ((Subgroup.centralizer (W : Set Q)).subgroupOf S).map S.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      _ = W_S.map S.subtype := by rw [← h]
  have hSM : S ⊓ M = W := by
    change S ⊓ (L ⊓ Subgroup.centralizer (W : Set Q)) = W
    rw [← inf_assoc, inf_eq_left.mpr hS.le, hCSW]
  have hwS_not_mem : wS ∉ Subgroup.zpowers zS := by
    intro h
    have h1 := (CFSG.Semidihedral.KleinFourOddKernel.mem_zpowers_involution
      zS wS hzS_ord).mp h
    rcases h1 with h1 | h1
    · exact hwS_ne_one h1
    · exact hwS_ne_z h1
  have hwS_not_mem' : wS ∉ Subgroup.zpowers
      ((eS.symm (CFSG.Semidihedral.r m)) ^ (2 ^ (m - 1) / 2)) := by
    rwa [hz_m_eq]
  have hNW := (hNfacts W_S hW).2.2 wS hwW hwS_not_mem'
  have hNW_card : Nat.card (Subgroup.normalizer (W_S : Set ↥S)) = 8 := hNW.2.2
  have hSNW : S ⊓ Subgroup.normalizer (W : Set Q) =
      (Subgroup.normalizer (W_S : Set ↥S)).map S.subtype := by
    have h := CFSG.Semidihedral.Local.normalizer_subgroupOf_eq (H := W) (K := S) hWS
    rw [hW_sub] at h
    calc S ⊓ Subgroup.normalizer (W : Set Q)
        = ((Subgroup.normalizer (W : Set Q)).subgroupOf S).map S.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      _ = (Subgroup.normalizer (W_S : Set ↥S)).map S.subtype := by rw [← h]
  have hSN : S ⊓ N = (Subgroup.normalizer (W_S : Set ↥S)).map S.subtype := by
    change S ⊓ (L ⊓ Subgroup.normalizer (W : Set Q)) = _
    rw [← inf_assoc, inf_eq_left.mpr hS.le, hSNW]
  have hSN_card : Nat.card ↥(S ⊓ N) = 8 := by
    change Nat.card ↥(S ⊓ (L ⊓ Subgroup.normalizer (W : Set Q))) = 8
    rw [hSN, Subgroup.card_map_of_injective S.subtype_injective, hNW_card]

  have hWcomm : IsMulCommutative ↥W := IsKleinFour.isMulCommutative
  have hWC : W ≤ Subgroup.centralizer (W : Set Q) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hWcomm
  have hWM : W ≤ M := by
    change W ≤ L ⊓ Subgroup.centralizer (W : Set Q)
    intro x hx
    exact ⟨hWle hx, hWC hx⟩
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW4]; norm_num)
  have hWMnorm : (W.subgroupOf M).Normal := by
    apply Subgroup.normal_of_le_center
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hle : M ≤ Subgroup.centralizer (M : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMab
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hle y.2) x.1 x.2).symm
  let P : Sylow 2 ↥M := default
  let PQ : Subgroup Q := (P : Subgroup ↥M).map M.subtype
  have hPtop : IsSylowIn 2 (P : Subgroup ↥M) ⊤ :=
    ⟨le_top, P.isPGroup', by simpa using P.not_dvd_index⟩
  have hPM : IsSylowIn 2 PQ M := by
    have h := (CFSG.Quasithin.E1.isSylowIn_map_of_injective (f := M.subtype)
      M.subtype_injective).mpr hPtop
    simpa [PQ, Subgroup.map_top, Subgroup.range_subtype] using h
  have hPQM : PQ ≤ M := hPM.le
  have hPQ2 : IsPGroup 2 PQ := hPM.isPGroup
  obtain ⟨S', hS', hPQS'⟩ :=
    @CFSG.Quasithin.exists_isSylowIn_ge Q _ _ 2 ⟨Nat.prime_two⟩ L PQ
      (hPQM.trans inf_le_left) hPQ2
  have hWPQ : W ≤ PQ :=
    @IsSylowIn.le_of_normal Q _ 2 PQ M ⟨Nat.prime_two⟩ hPM W hWM hWMnorm hW2
  have hWS' : W ≤ S' := hWPQ.trans hPQS'
  obtain ⟨m', hm4', ⟨e'⟩⟩ := sylow_semidihedral_of_lieModel hp hp2 hL hS'.toSylow
  let eS' : ↥S' ≃* CFSG.Open.SemidihedralGroup m' :=
    (Subgroup.subgroupOfEquivOfLe hS'.le).symm.trans e'
  let W' : Subgroup ↥S' := W.subgroupOf S'
  have hW' : IsKleinFour W' :=
    CFSG.Semidihedral.Local.isKleinFour_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hWS').symm
  have hmain' :=
    CFSG.Semidihedral.Local.semidihedral_four_subgroup_centralizers m' hm4' eS'.symm
  obtain ⟨-, hNfacts', -⟩ := hmain'
  have hC'W : Subgroup.centralizer (W' : Set ↥S') = W' := by
    simpa using (hNfacts' W' hW').2.1
  have hCS'W : S' ⊓ Subgroup.centralizer (W : Set Q) = W := by
    have h := CFSG.Semidihedral.Local.centralizer_subgroupOf_eq (H := W) (K := S') hWS'
    rw [hC'W] at h
    calc S' ⊓ Subgroup.centralizer (W : Set Q)
        = ((Subgroup.centralizer (W : Set Q)).subgroupOf S').map S'.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_comm]
      _ = W'.map S'.subtype := by rw [← h]
      _ = W := Subgroup.map_subgroupOf_eq_of_le hWS'
  have hPQW : PQ ≤ W := by
    have hPQC : PQ ≤ Subgroup.centralizer (W : Set Q) := hPQM.trans inf_le_right
    have := le_inf hPQS' hPQC
    rwa [hCS'W] at this
  have hPQeq : PQ = W := le_antisymm hPQW hWPQ
  have hPcard : Nat.card P = 4 := by
    have h1 : Nat.card PQ = Nat.card P :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [hPQeq] at h1
    rw [← h1, hW4]
  have hPmult := @Sylow.card_eq_multiplicity (↥M) _ _ 2 ⟨Nat.prime_two⟩ P
  rw [hPcard] at hPmult
  have hMfac : (Nat.card ↥M).factorization 2 = 2 := by
    have h2 : 2 ^ (Nat.card ↥M).factorization 2 = 2 ^ 2 := by
      rw [← hPmult]
      norm_num
    exact Nat.pow_right_injective (a := 2) (by norm_num) h2

  have hMleN : M ≤ N := by
    change L ⊓ Subgroup.centralizer (W : Set Q) ≤ L ⊓ Subgroup.normalizer (W : Set Q)
    exact inf_le_inf_left L (Subgroup.centralizer_le_normalizer _)
  have hMNcard : Nat.card ↥N = 6 * Nat.card ↥M := by
    have h := Subgroup.relIndex_mul_card (H := M) (K := N)
    rw [inf_eq_left.mpr hMleN, hMN] at h
    exact h.symm
  have hNfac : (Nat.card ↥N).factorization 2 = 3 := by
    rw [hMNcard]
    rw [Nat.factorization_mul (by norm_num) (Nat.card_pos.ne')]
    have h62 : Nat.factorization 6 2 = 1 := by
      have h : Nat.factorization 6 = Nat.factorization 2 + Nat.factorization 3 := by
        rw [show 6 = 2 * 3 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num)]
      rw [h, Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
    change Nat.factorization 6 2 + (Nat.card ↥M).factorization 2 = 3
    rw [h62, hMfac]
  have hTN : T ⊓ N = S ⊓ N := by
    rw [hSdef]
    change T ⊓ (L ⊓ Subgroup.normalizer (W : Set Q)) =
      (T ⊓ L) ⊓ (L ⊓ Subgroup.normalizer (W : Set Q))
    rw [inf_assoc]
    congr 1
    exact (inf_eq_right.mpr inf_le_left).symm
  have hTNcard : Nat.card ↥(T ⊓ N) = 8 := by
    rw [hTN]
    exact hSN_card
  have hfinal : IsSylowIn 2 (T ⊓ N) N := by
    apply @CFSG.Quasithin.isSylowIn_of_card_eq Q _ _ 2 ⟨Nat.prime_two⟩
      (T ⊓ N) N inf_le_right
    rw [hTNcard, hNfac]
    norm_num
  exact ⟨W, hWle, hWel, hW4, hzW, hT_le_NW, huW, by simpa [N] using hfinal⟩

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
