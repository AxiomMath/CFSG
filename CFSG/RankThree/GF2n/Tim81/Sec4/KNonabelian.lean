module

public import CFSG.RankThree.GF2n.Tim81.Sec4.KElem
public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjH
public import CFSG.RankThree.GF2n.Tim81.Sec4.SL2Borel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.GorensteinWalter
open CFSG.RankThree.GF2n.Tim81.Sec4
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

theorem frattini_conj_le {P W : Subgroup G} (hP : IsPGroup 2 P)
    (hPhi : inSubgroup frattini P ≤ W) (y : G) :
    inSubgroup frattini (conjSubgroup y P) ≤ conjSubgroup y W := by
  have hP' : IsPGroup 2 (conjSubgroup y P) := hP.map (MulAut.conj y).toMonoidHom
  refine inSubgroup_frattini_le_of_sq hP' ?_ ?_
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨p ^ 2, hPhi (sq_mem_inSubgroup_frattini hP hp), ?_⟩
    simp only [MulAut.conj_apply, map_pow]
  · intro x hx z hz
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr
      ⟨⁅p, q⁆, hPhi (commutatorElement_mem_inSubgroup_frattini hP hp hq), ?_⟩
    simp only [MulAut.conj_apply, map_commutatorElement]

private theorem commutator_AB_le_D_aux (h : RootHyp M V) {y : G} (hyH : y ∈ H)
    (hK : KFactorization M V H y) :
    ⁅Pc M V ⊓ kOf V H, conjSubgroup y (Pc M V) ⊓ kOf V H⁆ ≤
      Pc M V ⊓ conjSubgroup y (Pc M V) := by
  classical
  set A : Subgroup G := Pc M V ⊓ kOf V H with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ kOf V H with hB
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  have hK' : kOf V H = A ⊔ B := by rw [hA, hB]; exact hK
  have hA_le_K : A ≤ kOf V H := by rw [hA]; exact inf_le_right
  have hB_le_K : B ≤ kOf V H := by rw [hB]; exact inf_le_right
  have hA_le_P : A ≤ Pc M V := by rw [hA]; exact inf_le_left
  have hB_le_P' : B ≤ conjSubgroup y (Pc M V) := by rw [hB]; exact inf_le_left
  have hD_le_P : D ≤ Pc M V := by rw [hD]; exact inf_le_left
  have hD_le_P' : D ≤ conjSubgroup y (Pc M V) := by rw [hD]; exact inf_le_right
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2' : IsPGroup 2 (conjSubgroup y (Pc M V)) :=
    hP2.map (MulAut.conj y).toMonoidHom
  have hA2 : IsPGroup 2 A := hP2.to_le hA_le_P
  have hB2 : IsPGroup 2 B := hP2'.to_le hB_le_P'
  have hA_der_le_V : ⁅A, A⁆ ≤ V := by
    refine (Subgroup.commutator_le.mpr ?_).trans
      ((inSubgroup_frattini_mono hP2 hA_le_P).trans h.toHyp.frattini_Pc_le)
    intro a ha b hb
    exact commutatorElement_mem_inSubgroup_frattini hA2 ha hb
  have hB_der_le_V' : ⁅B, B⁆ ≤ conjSubgroup y V := by
    refine (Subgroup.commutator_le.mpr ?_).trans
      ((inSubgroup_frattini_mono hP2' hB_le_P').trans
        (frattini_conj_le hP2 h.toHyp.frattini_Pc_le y))
    intro a ha b hb
    exact commutatorElement_mem_inSubgroup_frattini hB2 ha hb
  have hK_le_NP : kOf V H ≤ Subgroup.normalizer (Pc M V : Set G) :=
    (kOf_le_M h).trans h.toHyp.le_normalizer_Pc
  have hKP_le_P : ⁅kOf V H, Pc M V⁆ ≤ Pc M V :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hK_le_NP
  have hKA_le_P : ⁅kOf V H, A⁆ ≤ Pc M V :=
    (Subgroup.commutator_mono (le_refl (kOf V H)) hA_le_P).trans hKP_le_P
  have hKy : conjSubgroup y (kOf V H) = kOf V H :=
    conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H hyH)
  have hB_eq : B = conjSubgroup y A := by
    rw [hB, hA]
    simp only [conjSubgroup_inf, hKy]
  have hAy_le_K : conjSubgroup y⁻¹ A ≤ kOf V H := by
    have hKy' : conjSubgroup y⁻¹ (kOf V H) = kOf V H :=
      conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H (H.inv_mem hyH))
    calc conjSubgroup y⁻¹ A ≤ conjSubgroup y⁻¹ (kOf V H) := Subgroup.map_mono hA_le_K
      _ = kOf V H := hKy'
  have hAyA_le_P : ⁅conjSubgroup y⁻¹ A, A⁆ ≤ Pc M V :=
    (Subgroup.commutator_mono hAy_le_K (le_refl A)).trans hKA_le_P
  have hAB_le_P' : ⁅A, B⁆ ≤ conjSubgroup y (Pc M V) := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hAyA_le_P
    rw [Subgroup.map_commutator] at hmap
    have hL : conjSubgroup y (conjSubgroup y⁻¹ A) = A := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    change ⁅conjSubgroup y (conjSubgroup y⁻¹ A), conjSubgroup y A⁆ ≤
      conjSubgroup y (Pc M V) at hmap
    rw [hL, ← hB_eq] at hmap
    exact hmap
  have hAB_le_P : ⁅A, B⁆ ≤ Pc M V := by
    have hBnorm : B ≤ Subgroup.normalizer (Pc M V : Set G) := hB_le_K.trans hK_le_NP
    have hBP : ⁅B, Pc M V⁆ ≤ Pc M V :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hBnorm
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (le_refl B) hA_le_P).trans hBP
  rw [hD]
  exact le_inf hAB_le_P hAB_le_P'

private theorem centralizer_D_AB_aux (h : RootHyp M V) {y : G} (hyH : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M) :
    Pc M V ⊓ conjSubgroup y (Pc M V) ≤
        Subgroup.centralizer (Pc M V ⊓ kOf V H : Set G) ∧
      Pc M V ⊓ conjSubgroup y (Pc M V) ≤
        Subgroup.centralizer (conjSubgroup y (Pc M V) ⊓ kOf V H : Set G) := by
  classical
  set A : Subgroup G := Pc M V ⊓ kOf V H with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ kOf V H with hB
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  have hA_le_K : A ≤ kOf V H := by rw [hA]; exact inf_le_right
  have hB_le_K : B ≤ kOf V H := by rw [hB]; exact inf_le_right
  have hA_le_P : A ≤ Pc M V := by rw [hA]; exact inf_le_left
  have hB_le_P' : B ≤ conjSubgroup y (Pc M V) := by rw [hB]; exact inf_le_left
  have hD_le_P : D ≤ Pc M V := by rw [hD]; exact inf_le_left
  have hD_le_P' : D ≤ conjSubgroup y (Pc M V) := by rw [hD]; exact inf_le_right
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2' : IsPGroup 2 (conjSubgroup y (Pc M V)) :=
    hP2.map (MulAut.conj y).toMonoidHom
  have hA2 : IsPGroup 2 A := hP2.to_le hA_le_P
  have hB2 : IsPGroup 2 B := hP2'.to_le hB_le_P'
  have hK_le_NP : kOf V H ≤ Subgroup.normalizer (Pc M V : Set G) :=
    (kOf_le_M h).trans h.toHyp.le_normalizer_Pc
  have hD_le_CA : D ≤ Subgroup.centralizer (A : Set G) := by
    have hAnormPy : A ≤ Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) :=
      hA_le_K.trans (kOf_le_normalizer_conjSubgroup_Pc_of_mem h hyH)
    have hAPy : ⁅A, conjSubgroup y (Pc M V)⁆ ≤ conjSubgroup y (Pc M V) :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hAnormPy
    have hAD_le_P' : ⁅A, D⁆ ≤ conjSubgroup y (Pc M V) :=
      (Subgroup.commutator_mono (le_refl A) hD_le_P').trans hAPy
    have hAD_le_V : ⁅A, D⁆ ≤ V := by
      refine (Subgroup.commutator_le.mpr ?_).trans h.toHyp.frattini_Pc_le
      intro a ha d hd
      exact commutatorElement_mem_inSubgroup_frattini hP2 (hA_le_P ha) (hD_le_P hd)
    have hAD_bot : ⁅A, D⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact (le_inf hAD_le_V hAD_le_P').trans (le_of_eq (inf_conj_Pc_eq_bot h hH hnM))
    have hDA_bot : ⁅D, A⁆ = ⊥ := (Subgroup.commutator_comm D A).trans hAD_bot
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDA_bot
  have hD_le_CB : D ≤ Subgroup.centralizer (B : Set G) := by
    have hBnormP : B ≤ Subgroup.normalizer (Pc M V : Set G) := hB_le_K.trans hK_le_NP
    have hBP : ⁅B, Pc M V⁆ ≤ Pc M V :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hBnormP
    have hBD_le_P : ⁅B, D⁆ ≤ Pc M V :=
      (Subgroup.commutator_mono (le_refl B) hD_le_P).trans hBP
    have hBD_le_V' : ⁅B, D⁆ ≤ conjSubgroup y V := by
      refine (Subgroup.commutator_le.mpr ?_).trans
        (frattini_conj_le hP2 h.toHyp.frattini_Pc_le y)
      intro b hb d hd
      exact commutatorElement_mem_inSubgroup_frattini hP2' (hB_le_P' hb) (hD_le_P' hd)
    have hPV'_bot : Pc M V ⊓ conjSubgroup y V = ⊥ := by
      rw [inf_comm]
      exact conjSubgroup_inf_Pc_eq_bot h hH hnM
    have hBD_bot : ⁅B, D⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact (le_inf hBD_le_P hBD_le_V').trans (le_of_eq hPV'_bot)
    have hDB_bot : ⁅D, B⁆ = ⊥ := (Subgroup.commutator_comm D B).trans hBD_bot
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDB_bot
  exact ⟨hD_le_CA, hD_le_CB⟩

private theorem centralizer_D_K_aux {y : G}
    (hK : KFactorization M V H y)
    (hD_le_CA : Pc M V ⊓ conjSubgroup y (Pc M V) ≤
      Subgroup.centralizer (Pc M V ⊓ kOf V H : Set G))
    (hD_le_CB : Pc M V ⊓ conjSubgroup y (Pc M V) ≤
      Subgroup.centralizer (conjSubgroup y (Pc M V) ⊓ kOf V H : Set G)) :
    Pc M V ⊓ conjSubgroup y (Pc M V) ≤
      Subgroup.centralizer (kOf V H : Set G) := by
  classical
  set A : Subgroup G := Pc M V ⊓ kOf V H with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ kOf V H with hB
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  have hK' : kOf V H = A ⊔ B := by rw [hA, hB]; exact hK
  have hD_le_CA' : D ≤ Subgroup.centralizer (A : Set G) := by
    simpa [hA, hD] using hD_le_CA
  have hD_le_CB' : D ≤ Subgroup.centralizer (B : Set G) := by
    simpa [hB, hD] using hD_le_CB
  have hKD_bot : ⁅kOf V H, D⁆ = ⊥ := by
    rw [hK']
    refine le_bot_iff.mp (commutator_sup_le_of_commutator_le_and_normalize A B D ⊥ ?_ ?_ ?_ ?_)
    · exact ((Subgroup.commutator_comm A D).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hD_le_CA')).le
    · exact ((Subgroup.commutator_comm B D).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hD_le_CB')).le
    · intro b _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
    · intro b _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((Subgroup.commutator_comm D (kOf V H)).trans hKD_bot)

private theorem V_and_conj_V_le_centralizer_kOf {y : G} (hyH : y ∈ H) :
    V ≤ Subgroup.centralizer (kOf V H : Set G) ∧
      conjSubgroup y V ≤ Subgroup.centralizer (kOf V H : Set G) := by
  constructor
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk).2 v
      (le_xOf_self V H hv)).symm
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk).2 v
      (conjSubgroup_le_xOf_of_mem (V := V) (H := H) hyH hv)).symm

private theorem commutator_kOf_le_sup_R_aux (h : RootHyp M V) {y : G} (hyH : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H y) :
    ⁅kOf V H, kOf V H⁆ ≤
      V ⊔ (Pc M V ⊓ conjSubgroup y (Pc M V)) ⊔ conjSubgroup y V := by
  classical
  set A : Subgroup G := Pc M V ⊓ kOf V H with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ kOf V H with hB
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  set R : Subgroup G := V ⊔ D ⊔ conjSubgroup y V with hR
  have hK' : kOf V H = A ⊔ B := by rw [hA, hB]; exact hK
  have hA_le_K : A ≤ kOf V H := by rw [hA]; exact inf_le_right
  have hB_le_K : B ≤ kOf V H := by rw [hB]; exact inf_le_right
  have hA_le_P : A ≤ Pc M V := by rw [hA]; exact inf_le_left
  have hB_le_P' : B ≤ conjSubgroup y (Pc M V) := by rw [hB]; exact inf_le_left
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2' : IsPGroup 2 (conjSubgroup y (Pc M V)) :=
    hP2.map (MulAut.conj y).toMonoidHom
  have hA2 : IsPGroup 2 A := hP2.to_le hA_le_P
  have hB2 : IsPGroup 2 B := hP2'.to_le hB_le_P'
  have hA_der_le_V : ⁅A, A⁆ ≤ V := by
    refine (Subgroup.commutator_le.mpr ?_).trans
      ((inSubgroup_frattini_mono hP2 hA_le_P).trans h.toHyp.frattini_Pc_le)
    intro a ha b hb
    exact commutatorElement_mem_inSubgroup_frattini hA2 ha hb
  have hB_der_le_V' : ⁅B, B⁆ ≤ conjSubgroup y V := by
    refine (Subgroup.commutator_le.mpr ?_).trans
      ((inSubgroup_frattini_mono hP2' hB_le_P').trans
        (frattini_conj_le hP2 h.toHyp.frattini_Pc_le y))
    intro a ha b hb
    exact commutatorElement_mem_inSubgroup_frattini hB2 ha hb
  have hAB_le_D : ⁅A, B⁆ ≤ D := by
    simpa [hA, hB, hD] using
      commutator_AB_le_D_aux h hyH hK
  obtain ⟨hD_le_CA, hD_le_CB⟩ :=
    centralizer_D_AB_aux h hyH hH hnM
  have hD_le_CK : D ≤ Subgroup.centralizer (kOf V H : Set G) :=
    centralizer_D_K_aux hK hD_le_CA hD_le_CB
  obtain ⟨hV_le_CK, hV'_le_CK⟩ :=
    V_and_conj_V_le_centralizer_kOf (V := V) (H := H) hyH
  have hR_le_CK : R ≤ Subgroup.centralizer (kOf V H : Set G) := by
    rw [hR]
    exact sup_le (sup_le hV_le_CK hD_le_CK) hV'_le_CK
  have hK_le_NR : kOf V H ≤ Subgroup.normalizer (R : Set G) := by
    have hK_le_CR : kOf V H ≤ Subgroup.centralizer (R : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (Subgroup.mem_centralizer_iff.mp (hR_le_CK hr) k hk).symm
    exact hK_le_CR.trans (Subgroup.centralizer_le_normalizer _)
  have hA_norm_R : A ≤ Subgroup.normalizer (R : Set G) := hA_le_K.trans hK_le_NR
  have hB_norm_R : B ≤ Subgroup.normalizer (R : Set G) := hB_le_K.trans hK_le_NR
  have hAA_le_R : ⁅A, A⁆ ≤ R := hA_der_le_V.trans (le_sup_of_le_left (le_sup_of_le_left le_rfl))
  have hBA_le_R : ⁅B, A⁆ ≤ R := by
    rw [Subgroup.commutator_comm]
    exact hAB_le_D.trans (le_sup_of_le_left (le_sup_of_le_right le_rfl))
  have hBB_le_R : ⁅B, B⁆ ≤ R := hB_der_le_V'.trans (le_sup_of_le_right le_rfl)
  have hKA_le_R : ⁅kOf V H, A⁆ ≤ R := by
    rw [hK']
    exact commutator_sup_le_of_commutator_le_and_normalize A B A R
      hAA_le_R hBA_le_R hA_norm_R hB_norm_R
  have hKB_le_R : ⁅kOf V H, B⁆ ≤ R := by
    rw [hK']
    exact commutator_sup_le_of_commutator_le_and_normalize A B B R
      (hAB_le_D.trans (le_sup_of_le_left (le_sup_of_le_right le_rfl)))
      hBB_le_R hA_norm_R hB_norm_R
  rw [hK']
  have hKA' : ⁅A ⊔ B, A⁆ ≤ R := by rw [← hK']; exact hKA_le_R
  have hKB' : ⁅A ⊔ B, B⁆ ≤ R := by rw [← hK']; exact hKB_le_R
  have hAK'' : ⁅A, A ⊔ B⁆ ≤ R :=
    (Subgroup.commutator_comm A (A ⊔ B)).le.trans hKA'
  have hBK'' : ⁅B, A ⊔ B⁆ ≤ R :=
    (Subgroup.commutator_comm B (A ⊔ B)).le.trans hKB'
  exact commutator_sup_le_of_commutator_le_and_normalize A B (A ⊔ B) R
    hAK'' hBK'' hA_norm_R hB_norm_R

private theorem commutator_kOf_le_center_aux (h : RootHyp M V) {y : G} (hyH : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H y) :
    ⁅kOf V H, kOf V H⁆ ≤ Subgroup.centralizer (kOf V H : Set G) := by
  classical
  set A : Subgroup G := Pc M V ⊓ kOf V H with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ kOf V H with hB
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  have hK' : kOf V H = A ⊔ B := by rw [hA, hB]; exact hK
  have hA_le_K : A ≤ kOf V H := by rw [hA]; exact inf_le_right
  have hB_le_K : B ≤ kOf V H := by rw [hB]; exact inf_le_right
  have hA_le_P : A ≤ Pc M V := by rw [hA]; exact inf_le_left
  have hB_le_P' : B ≤ conjSubgroup y (Pc M V) := by rw [hB]; exact inf_le_left
  have hD_le_P : D ≤ Pc M V := by rw [hD]; exact inf_le_left
  have hD_le_P' : D ≤ conjSubgroup y (Pc M V) := by rw [hD]; exact inf_le_right
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hP2' : IsPGroup 2 (conjSubgroup y (Pc M V)) :=
    hP2.map (MulAut.conj y).toMonoidHom
  have hA2 : IsPGroup 2 A := hP2.to_le hA_le_P
  have hB2 : IsPGroup 2 B := hP2'.to_le hB_le_P'
  have hA_der_le_V : ⁅A, A⁆ ≤ V := by
    refine (Subgroup.commutator_le.mpr ?_).trans
      ((inSubgroup_frattini_mono hP2 hA_le_P).trans h.toHyp.frattini_Pc_le)
    intro a ha b hb
    exact commutatorElement_mem_inSubgroup_frattini hA2 ha hb
  have hB_der_le_V' : ⁅B, B⁆ ≤ conjSubgroup y V := by
    refine (Subgroup.commutator_le.mpr ?_).trans
      ((inSubgroup_frattini_mono hP2' hB_le_P').trans
        (frattini_conj_le hP2 h.toHyp.frattini_Pc_le y))
    intro a ha b hb
    exact commutatorElement_mem_inSubgroup_frattini hB2 ha hb
  have hAB_le_D : ⁅A, B⁆ ≤ D := by
    simpa [hA, hB, hD] using
      commutator_AB_le_D_aux h hyH hK
  obtain ⟨hD_le_CA, hD_le_CB⟩ :=
    centralizer_D_AB_aux h hyH hH hnM
  have hD_le_CK : D ≤ Subgroup.centralizer (kOf V H : Set G) :=
    centralizer_D_K_aux hK hD_le_CA hD_le_CB
  obtain ⟨hV_le_CK, hV'_le_CK⟩ :=
    V_and_conj_V_le_centralizer_kOf (V := V) (H := H) hyH
  have hK_le_NC : kOf V H ≤
      Subgroup.normalizer (Subgroup.centralizer (kOf V H : Set G) : Set G) := by
    have hK_le_CC : kOf V H ≤
        Subgroup.centralizer ((Subgroup.centralizer (kOf V H : Set G)) : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact (Subgroup.mem_centralizer_iff.mp hc k hk).symm
    exact hK_le_CC.trans (Subgroup.centralizer_le_normalizer _)
  conv_lhs => rw [hK']
  have hAA_CK : ⁅A, A⁆ ≤ Subgroup.centralizer (kOf V H : Set G) :=
    hA_der_le_V.trans hV_le_CK
  have hBA_CK : ⁅B, A⁆ ≤ Subgroup.centralizer (kOf V H : Set G) :=
    (Subgroup.commutator_comm B A).le.trans (hAB_le_D.trans hD_le_CK)
  have hBB_CK : ⁅B, B⁆ ≤ Subgroup.centralizer (kOf V H : Set G) :=
    hB_der_le_V'.trans hV'_le_CK
  have hA_NC : A ≤ Subgroup.normalizer
      (Subgroup.centralizer (kOf V H : Set G) : Set G) := hA_le_K.trans hK_le_NC
  have hB_NC : B ≤ Subgroup.normalizer
      (Subgroup.centralizer (kOf V H : Set G) : Set G) := hB_le_K.trans hK_le_NC
  have hKA_CK : ⁅A ⊔ B, A⁆ ≤ Subgroup.centralizer (kOf V H : Set G) :=
    commutator_sup_le_of_commutator_le_and_normalize A B A
      (Subgroup.centralizer (kOf V H : Set G)) hAA_CK hBA_CK hA_NC hB_NC
  have hKB_CK : ⁅A ⊔ B, B⁆ ≤ Subgroup.centralizer (kOf V H : Set G) :=
    commutator_sup_le_of_commutator_le_and_normalize A B B
      (Subgroup.centralizer (kOf V H : Set G))
      (hAB_le_D.trans hD_le_CK) hBB_CK hA_NC hB_NC
  have hKA'' : ⁅A, A ⊔ B⁆ ≤ Subgroup.centralizer (kOf V H : Set G) :=
    (Subgroup.commutator_comm A (A ⊔ B)).le.trans hKA_CK
  have hKB'' : ⁅B, A ⊔ B⁆ ≤ Subgroup.centralizer (kOf V H : Set G) :=
    (Subgroup.commutator_comm B (A ⊔ B)).le.trans hKB_CK
  exact commutator_sup_le_of_commutator_le_and_normalize A B (A ⊔ B)
    (Subgroup.centralizer (kOf V H : Set G)) hKA'' hKB'' hA_NC hB_NC

private theorem commutator_kOf_le_center_and_sup_aux (h : RootHyp M V) {y : G} (hyH : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H y) :
    ⁅kOf V H, kOf V H⁆ ≤ Subgroup.centralizer (kOf V H : Set G) ∧
      ⁅kOf V H, kOf V H⁆ ≤
        V ⊔ (Pc M V ⊓ conjSubgroup y (Pc M V)) ⊔ conjSubgroup y V :=
  ⟨commutator_kOf_le_center_aux h hyH hH hnM hK,
    commutator_kOf_le_sup_R_aux h hyH hH hnM hK⟩

private theorem commutator_Pc_inf_ne_bot_setup_aux (h : RootHyp M V) {y : G} (hyH : y ∈ H) :
    (⁅Pc M V ⊓ kOf V H, conjSubgroup y (Pc M V) ⊓ kOf V H⁆ ≤
        Pc M V ⊓ conjSubgroup y (Pc M V)) ∧
      (Pc M V ⊓ kOf V H ≤ Subgroup.normalizer
        (Pc M V ⊓ conjSubgroup y (Pc M V) : Set G)) ∧
      (conjSubgroup y (Pc M V) ⊓ kOf V H ≤ Subgroup.normalizer
        (Pc M V ⊓ conjSubgroup y (Pc M V) : Set G)) ∧
      (Pc M V ⊓ conjSubgroup y (Pc M V) ≤ Pc M V) ∧
      (Pc M V ⊓ conjSubgroup y (Pc M V) ≤ conjSubgroup y (Pc M V)) ∧
      (conjSubgroup y (Pc M V) ⊓ kOf V H = conjSubgroup y (Pc M V ⊓ kOf V H)) := by
  classical
  set A : Subgroup G := Pc M V ⊓ kOf V H with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ kOf V H with hB
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  have hA_le_K : A ≤ kOf V H := by rw [hA]; exact inf_le_right
  have hB_le_K : B ≤ kOf V H := by rw [hB]; exact inf_le_right
  have hA_le_P : A ≤ Pc M V := by rw [hA]; exact inf_le_left
  have hB_le_P' : B ≤ conjSubgroup y (Pc M V) := by rw [hB]; exact inf_le_left
  have hD_le_P : D ≤ Pc M V := by rw [hD]; exact inf_le_left
  have hD_le_P' : D ≤ conjSubgroup y (Pc M V) := by rw [hD]; exact inf_le_right
  have hK_le_NP : kOf V H ≤ Subgroup.normalizer (Pc M V : Set G) :=
    (kOf_le_M h).trans h.toHyp.le_normalizer_Pc
  have hK_le_NP' : kOf V H ≤ Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) :=
    kOf_le_normalizer_conjSubgroup_Pc_of_mem h hyH
  have hK_norm_D : kOf V H ≤ Subgroup.normalizer (D : Set G) := by
    intro k hk
    rw [← conjSubgroup_eq_self_iff]
    rw [hD, conjSubgroup_inf,
      conjSubgroup_eq_self_iff.mpr (hK_le_NP hk),
      conjSubgroup_eq_self_iff.mpr (hK_le_NP' hk)]
  have hA_normD : A ≤ Subgroup.normalizer (D : Set G) := hA_le_K.trans hK_norm_D
  have hB_normD : B ≤ Subgroup.normalizer (D : Set G) := hB_le_K.trans hK_norm_D
  have hB_eq : B = conjSubgroup y A := by
    rw [hB, hA]
    simp only [conjSubgroup_inf,
      conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H hyH)]
  have hKP_le_P : ⁅kOf V H, Pc M V⁆ ≤ Pc M V :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hK_le_NP
  have hKA_le_P : ⁅kOf V H, A⁆ ≤ Pc M V :=
    (Subgroup.commutator_mono (le_refl (kOf V H)) hA_le_P).trans hKP_le_P
  have hAy_le_K : conjSubgroup y⁻¹ A ≤ kOf V H := by
    have hKy' : conjSubgroup y⁻¹ (kOf V H) = kOf V H :=
      conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H (H.inv_mem hyH))
    calc conjSubgroup y⁻¹ A ≤ conjSubgroup y⁻¹ (kOf V H) := Subgroup.map_mono hA_le_K
      _ = kOf V H := hKy'
  have hAyA_le_P : ⁅conjSubgroup y⁻¹ A, A⁆ ≤ Pc M V :=
    (Subgroup.commutator_mono hAy_le_K (le_refl A)).trans hKA_le_P
  have hAB_le_P' : ⁅A, B⁆ ≤ conjSubgroup y (Pc M V) := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hAyA_le_P
    rw [Subgroup.map_commutator] at hmap
    have hL : conjSubgroup y (conjSubgroup y⁻¹ A) = A := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    change ⁅conjSubgroup y (conjSubgroup y⁻¹ A), conjSubgroup y A⁆ ≤
      conjSubgroup y (Pc M V) at hmap
    rw [hL, ← hB_eq] at hmap
    exact hmap
  have hAB_le_P : ⁅A, B⁆ ≤ Pc M V := by
    have hBnorm : B ≤ Subgroup.normalizer (Pc M V : Set G) := hB_le_K.trans hK_le_NP
    have hBP : ⁅B, Pc M V⁆ ≤ Pc M V :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hBnorm
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (le_refl B) hA_le_P).trans hBP
  have hAB_le_D : ⁅A, B⁆ ≤ D := by
    rw [hD]
    exact le_inf hAB_le_P hAB_le_P'
  exact ⟨hAB_le_D, hA_normD, hB_normD, hD_le_P, hD_le_P', hB_eq⟩

private theorem commutator_kOf_le_inf_conj_of_commutator_eq_bot_aux
    {A B D : Subgroup G} {y : G} (hK : kOf V H = A ⊔ B)
    (hAB_le_D : ⁅A, B⁆ ≤ D)
    (hA_normD : A ≤ Subgroup.normalizer (D : Set G))
    (hB_normD : B ≤ Subgroup.normalizer (D : Set G))
    (hB_eq : B = conjSubgroup y A) (hA_bot : ⁅A, A⁆ = ⊥) :
    ⁅kOf V H, kOf V H⁆ ≤ D := by
  have hB_bot : ⁅B, B⁆ = ⊥ := by
    rw [hB_eq]
    change ⁅Subgroup.map (MulAut.conj y).toMonoidHom A,
      Subgroup.map (MulAut.conj y).toMonoidHom A⁆ = ⊥
    rw [← Subgroup.map_commutator, hA_bot]
    simp
  rw [hK]
  have hKA_le_D : ⁅A ⊔ B, A⁆ ≤ D :=
    commutator_sup_le_of_commutator_le_and_normalize A B A D
      (hA_bot ▸ bot_le) ((Subgroup.commutator_comm B A).le.trans hAB_le_D)
      hA_normD hB_normD
  have hKB_le_D : ⁅A ⊔ B, B⁆ ≤ D :=
    commutator_sup_le_of_commutator_le_and_normalize A B B D
      hAB_le_D (hB_bot ▸ bot_le) hA_normD hB_normD
  have hAK_le_D : ⁅A, A ⊔ B⁆ ≤ D :=
    (Subgroup.commutator_comm A (A ⊔ B)).le.trans hKA_le_D
  have hBK_le_D : ⁅B, A ⊔ B⁆ ≤ D :=
    (Subgroup.commutator_comm B (A ⊔ B)).le.trans hKB_le_D
  exact commutator_sup_le_of_commutator_le_and_normalize A B (A ⊔ B) D
    hAK_le_D hBK_le_D hA_normD hB_normD

private theorem conj_Pc_le_normalizer_commutator_aux {y : G}
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) :
    conjSubgroup y (Pc M V) ≤
      Subgroup.normalizer ((⁅kOf V H, kOf V H⁆ : Subgroup G) : Set G) := by
  intro p hp
  rw [← conjSubgroup_eq_self_iff]
  have hpH : p ∈ H := by rw [hH]; exact Subgroup.mem_sup_right hp
  have hpK : conjSubgroup p (kOf V H) = kOf V H :=
    conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H hpH)
  change Subgroup.map (MulAut.conj p).toMonoidHom ⁅kOf V H, kOf V H⁆ =
    ⁅kOf V H, kOf V H⁆
  rw [Subgroup.map_commutator]
  change ⁅conjSubgroup p (kOf V H), conjSubgroup p (kOf V H)⁆ =
    ⁅kOf V H, kOf V H⁆
  rw [hpK]

private theorem commutator_subgroupOf_ne_bot_aux {y : G}
    (hK'_ne : ⁅kOf V H, kOf V H⁆ ≠ ⊥)
    (hK'_le_P' : ⁅kOf V H, kOf V H⁆ ≤ conjSubgroup y (Pc M V)) :
    (⁅kOf V H, kOf V H⁆).subgroupOf (conjSubgroup y (Pc M V)) ≠ ⊥ := by
  intro hbot
  apply hK'_ne
  rw [eq_bot_iff]
  intro x hx
  have hxP' : x ∈ conjSubgroup y (Pc M V) := hK'_le_P' hx
  have hxsub : (⟨x, hxP'⟩ : ↥(conjSubgroup y (Pc M V))) ∈
      (⁅kOf V H, kOf V H⁆).subgroupOf (conjSubgroup y (Pc M V)) :=
    Subgroup.mem_subgroupOf.mpr hx
  rw [hbot] at hxsub
  have hx1 : x = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hxsub)
  simpa [hx1]

private theorem center_element_mem_bot_aux (h : RootHyp M V) {y : G}
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    {D : Subgroup G} (hK'_le_D : ⁅kOf V H, kOf V H⁆ ≤ D) (hD_le_P : D ≤ Pc M V)
    (hN_normal : ((⁅kOf V H, kOf V H⁆).subgroupOf
      (conjSubgroup y (Pc M V))).Normal)
    (hN_ne : (⁅kOf V H, kOf V H⁆).subgroupOf (conjSubgroup y (Pc M V)) ≠ ⊥)
    (hP2' : IsPGroup 2 (conjSubgroup y (Pc M V))) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥(conjSubgroup y (Pc M V)) := IsPGroup.isNilpotent hP2'
  haveI : ((⁅kOf V H, kOf V H⁆).subgroupOf
      (conjSubgroup y (Pc M V))).Normal := hN_normal
  have hcenter_ne := Group.IsNilpotent.inf_center_ne_bot_of_normal
    (G := ↥(conjSubgroup y (Pc M V))) hN_ne
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcenter_ne
  have hxN : x.1 ∈ (⁅kOf V H, kOf V H⁆).subgroupOf (conjSubgroup y (Pc M V)) :=
    (Subgroup.mem_inf.mp x.2).1
  have hxZ : x.1 ∈ Subgroup.center ↥(conjSubgroup y (Pc M V)) :=
    (Subgroup.mem_inf.mp x.2).2
  have hxK' : (x.1 : G) ∈ ⁅kOf V H, kOf V H⁆ := Subgroup.mem_subgroupOf.mp hxN
  have hxC : (x.1 : G) ∈ Subgroup.centralizer
      (conjSubgroup y (Pc M V) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hcomm : ⟨p, hp⟩ * x.1 = x.1 * ⟨p, hp⟩ :=
      (Subgroup.mem_center_iff.mp hxZ) ⟨p, hp⟩
    exact congrArg Subtype.val hcomm
  have hcenterP' : conjSubgroup y (Pc M V) ⊓
      Subgroup.centralizer (conjSubgroup y (Pc M V) : Set G) = conjSubgroup y V := by
    rw [h.toHyp.centralizer_conj_Pc y]
    exact inf_eq_right.mpr (Subgroup.map_mono h.toHyp.le_Pc)
  have hxV' : (x.1 : G) ∈ conjSubgroup y V := by
    rw [← hcenterP']
    exact Subgroup.mem_inf.mpr ⟨x.1.2, hxC⟩
  have hxP : (x.1 : G) ∈ Pc M V := hD_le_P (hK'_le_D hxK')
  have hxbot : (x.1 : G) ∈ (⊥ : Subgroup G) := by
    have hmem : (x.1 : G) ∈ conjSubgroup y V ⊓ Pc M V := Subgroup.mem_inf.mpr ⟨hxV', hxP⟩
    rwa [conjSubgroup_inf_Pc_eq_bot h hH hnM] at hmem
  have hx1 : (x.1 : G) = 1 := Subgroup.mem_bot.mp hxbot
  exact hxne (Subtype.ext (Subtype.ext hx1))

private theorem commutator_Pc_inf_ne_bot_aux (h : RootHyp M V) {y : G} (hyH : y ∈ H)
    (hH : H = Pc M V ⊔ conjSubgroup y (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H y)
    (hK'_ne : ⁅kOf V H, kOf V H⁆ ≠ ⊥) :
    ⁅Pc M V ⊓ kOf V H, Pc M V ⊓ kOf V H⁆ ≠ ⊥ := by
  classical
  set A : Subgroup G := Pc M V ⊓ kOf V H with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ kOf V H with hB
  set D : Subgroup G := Pc M V ⊓ conjSubgroup y (Pc M V) with hD
  have hK' : kOf V H = A ⊔ B := by rw [hA, hB]; exact hK
  obtain ⟨hAB_le_D_ex, hA_normD_ex, hB_normD_ex, hD_le_P_ex, hD_le_P'_ex, hB_eq_ex⟩ :=
    commutator_Pc_inf_ne_bot_setup_aux h hyH
  have hAB_le_D : ⁅A, B⁆ ≤ D := by simpa [hA, hB, hD] using hAB_le_D_ex
  have hA_normD : A ≤ Subgroup.normalizer (D : Set G) := by
    simpa [hA, hD] using hA_normD_ex
  have hB_normD : B ≤ Subgroup.normalizer (D : Set G) := by
    simpa [hB, hD] using hB_normD_ex
  have hD_le_P : D ≤ Pc M V := by simpa [hD] using hD_le_P_ex
  have hD_le_P' : D ≤ conjSubgroup y (Pc M V) := by simpa [hD] using hD_le_P'_ex
  have hB_eq : B = conjSubgroup y A := by simpa [hA, hB] using hB_eq_ex
  intro hA_bot
  have hK'_le_D : ⁅kOf V H, kOf V H⁆ ≤ D :=
    commutator_kOf_le_inf_conj_of_commutator_eq_bot_aux hK' hAB_le_D hA_normD hB_normD
      hB_eq hA_bot
  have hK'_le_P' : ⁅kOf V H, kOf V H⁆ ≤ conjSubgroup y (Pc M V) :=
    hK'_le_D.trans hD_le_P'
  have hP2' : IsPGroup 2 (conjSubgroup y (Pc M V)) :=
    ((inSubgroup_pCore_two M).1.to_le inf_le_left).map (MulAut.conj y).toMonoidHom
  have hP'_le_NK' := conj_Pc_le_normalizer_commutator_aux (M := M) (V := V) (H := H) hH
  have hN_normal : ((⁅kOf V H, kOf V H⁆).subgroupOf
      (conjSubgroup y (Pc M V))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK'_le_P').mpr hP'_le_NK'
  have hN_ne := commutator_subgroupOf_ne_bot_aux hK'_ne hK'_le_P'
  exact center_element_mem_bot_aux h hH hnM hK'_le_D hD_le_P hN_normal hN_ne hP2'

theorem commutator_kOf_le_center (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀) :
    ⁅kOf V H, kOf V H⁆ ≤ Subgroup.centralizer (kOf V H : Set G) := by
  obtain ⟨y, hyH, hPy, -, hHy⟩ := exists_mem_conj_eq_of_eq_sup h hPH hH
  have hK' : kOf V H =
      (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y (Pc M V) ⊓ kOf V H) := by
    conv_lhs => rw [hK]
    rw [hPy]
  exact (commutator_kOf_le_center_and_sup_aux h hyH hHy hnM hK').1

theorem commutator_kOf_le_sup (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀) :
    ⁅kOf V H, kOf V H⁆ ≤
      V ⊔ (Pc M V ⊓ conjSubgroup h₀ (Pc M V)) ⊔ conjSubgroup h₀ V := by
  obtain ⟨y, hyH, hPy, hVy, hHy⟩ := exists_mem_conj_eq_of_eq_sup h hPH hH
  have hK' : kOf V H =
      (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y (Pc M V) ⊓ kOf V H) := by
    conv_lhs => rw [hK]
    rw [hPy]
  have hmain := (commutator_kOf_le_center_and_sup_aux h hyH hHy hnM hK').2
  rwa [← hPy, ← hVy] at hmain

theorem inf_conj_Pc_le_centralizer_kOf (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀) :
    Pc M V ⊓ conjSubgroup h₀ (Pc M V) ≤ Subgroup.centralizer (kOf V H : Set G) := by
  obtain ⟨y, hyH, hPy, -, hHy⟩ := exists_mem_conj_eq_of_eq_sup h hPH hH
  have hK' : kOf V H =
      (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y (Pc M V) ⊓ kOf V H) := by
    conv_lhs => rw [hK]
    rw [hPy]
  obtain ⟨hD_le_CA, hD_le_CB⟩ := centralizer_D_AB_aux h hyH hHy hnM
  rw [hPy]
  exact centralizer_D_K_aux hK' hD_le_CA hD_le_CB


theorem commutator_Pc_inf_ne_bot (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) :
    ⁅Pc M V ⊓ kOf V H, Pc M V ⊓ kOf V H⁆ ≠ ⊥ := by
  obtain ⟨y, hyH, hPy, -, hHy⟩ := exists_mem_conj_eq_of_eq_sup h hPH hH
  have hK' : kOf V H =
      (Pc M V ⊓ kOf V H) ⊔ (conjSubgroup y (Pc M V) ⊓ kOf V H) := by
    conv_lhs => rw [hK]
    rw [hPy]
  have hK'_ne : ⁅kOf V H, kOf V H⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, z, hz, hxz⟩ := hnab
    have hmem : ⁅x, z⁆ ∈ ⁅kOf V H, kOf V H⁆ :=
      Subgroup.commutator_mem_commutator hx hz
    rw [hbot] at hmem
    have h1 : ⁅x, z⁆ = 1 := Subgroup.mem_bot.mp hmem
    exact hxz (commutatorElement_eq_one_iff_mul_comm.mp h1)
  exact commutator_Pc_inf_ne_bot_aux h hyH hHy hnM hK' hK'_ne

theorem exists_sq_ne_one_conj_inf (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hnab : ∃ x ∈ kOf V H, ∃ y ∈ kOf V H, x * y ≠ y * x) :
    ∃ z ∈ conjSubgroup h₀ (Pc M V) ⊓ kOf V H, z * z ≠ 1 := by
  classical
  obtain ⟨y, hyH, hPy, -, hHy⟩ := exists_mem_conj_eq_of_eq_sup h hPH hH
  have hA_ne : ⁅Pc M V ⊓ kOf V H, Pc M V ⊓ kOf V H⁆ ≠ ⊥ :=
    commutator_Pc_inf_ne_bot h hPH hH hnM hK hnab
  set A : Subgroup G := Pc M V ⊓ kOf V H with hA
  set B : Subgroup G := conjSubgroup y (Pc M V) ⊓ kOf V H with hB
  have hB_eq : B = conjSubgroup y A := by
    rw [hB, hA]
    simp only [conjSubgroup_inf,
      conjSubgroup_eq_self_iff.mpr (le_normalizer_kOf V H hyH)]
  have hB_ne : ⁅B, B⁆ ≠ ⊥ := by
    intro hbot
    apply hA_ne
    have hmap : ⁅B, B⁆ = conjSubgroup y ⁅A, A⁆ := by
      rw [hB_eq]
      change ⁅Subgroup.map (MulAut.conj y).toMonoidHom A,
        Subgroup.map (MulAut.conj y).toMonoidHom A⁆ = _
      rw [← Subgroup.map_commutator]
      rfl
    rw [hmap] at hbot
    have h := congrArg (conjSubgroup y⁻¹) hbot
    simpa [conjSubgroup_conjSubgroup, conjSubgroup_one, conjSubgroup_bot] using h
  rw [hPy]
  by_contra hnone
  push Not at hnone
  have hB_der_bot : ⁅B, B⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hb2 : b * b = 1 := hnone b hb
    have hc2 : c * c = 1 := hnone c hc
    have hbc2 : (b * c) * (b * c) = 1 := hnone (b * c) (B.mul_mem hb hc)
    have h1 : b * c * b * c = 1 := by simpa [mul_assoc] using hbc2
    have h2 : b * c * b = c := by
      calc b * c * b = b * c * b * (c * c) := by rw [hc2]; group
        _ = (b * c * b * c) * c := by group
        _ = 1 * c := by rw [h1]
        _ = c := by group
    calc c * b = (b * b) * c * b := by rw [hb2]; group
      _ = b * (b * c * b) := by group
      _ = b * c := by rw [h2]
  exact hB_ne hB_der_bot


private theorem weaklyClosed_map_of_bijective {X Y : Type} [Group X] [Group Y]
    (ψ : X ≃* Y) {L : Subgroup X}
    (hwc : ∀ g : X, conjSubgroup g L ≤ Subgroup.normalizer (L : Set X) →
      conjSubgroup g L = L) :
    ∀ s : Y, conjSubgroup s (Subgroup.map ψ.toMonoidHom L) ≤
      Subgroup.normalizer (Subgroup.map ψ.toMonoidHom L : Set Y) →
      conjSubgroup s (Subgroup.map ψ.toMonoidHom L) =
        Subgroup.map ψ.toMonoidHom L := by
  intro s hs
  let g : X := ψ.symm s
  have hgs : ψ.toMonoidHom g = s := by simp [g]
  have hN : Subgroup.map ψ.toMonoidHom (Subgroup.normalizer (L : Set X)) =
      Subgroup.normalizer (Subgroup.map ψ.toMonoidHom L : Set Y) :=
    Subgroup.map_normalizer_eq_of_bijective L ψ.bijective
  have hs' : Subgroup.map ψ.toMonoidHom (conjSubgroup g L) ≤
      Subgroup.map ψ.toMonoidHom (Subgroup.normalizer (L : Set X)) := by
    rw [map_conjSubgroup ψ.toMonoidHom, hgs, hN]
    exact hs
  have hle : conjSubgroup g L ≤ Subgroup.normalizer (L : Set X) := by
    rw [Subgroup.map_le_map_iff] at hs'
    have hker : ψ.toMonoidHom.ker = ⊥ := MonoidHom.ker_eq_bot ψ.toMonoidHom ψ.injective
    rw [hker, sup_bot_eq] at hs'
    exact hs'
  have heq : conjSubgroup g L = L := hwc g hle
  calc conjSubgroup s (Subgroup.map ψ.toMonoidHom L)
      = Subgroup.map ψ.toMonoidHom (conjSubgroup g L) := by
        rw [map_conjSubgroup ψ.toMonoidHom, hgs]
    _ = Subgroup.map ψ.toMonoidHom L := by rw [heq]

private theorem imgK_weaklyClosed (h : RootHyp M V) (hPH : Pc M V ≤ H) :
    ∀ g : HBar V H, conjSubgroup g (imgK V H (Pc M V)) ≤
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) →
      conjSubgroup g (imgK V H (Pc M V)) = imgK V H (Pc M V) := by
  intro g hg
  obtain ⟨gH, rfl⟩ := piK_surjective V H g
  have hEq := imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) gH.2 hPH
  have hnorm : imgK V H (conjSubgroup (gH : G) (Pc M V)) ≤
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
    rwa [hEq]
  have heq := weaklyClosed_imgK h hPH gH.2 hnorm
  rwa [hEq] at heq


private theorem isPGroup_le_subgroupOf_normalizer_sl2 {F : Type} [Field F] [Fintype F]
    [CharP F 2] {T' : Subgroup SL(2, F)} {u : SL(2, F)}
    (hT'_eq_utri : T' = conjSubgroup u (utri F)) :
    ∀ Q : Subgroup ↥(Subgroup.normalizer (T' : Set SL(2, F))),
      IsPGroup 2 Q → Q ≤ T'.subgroupOf (Subgroup.normalizer (T' : Set SL(2, F))) := by
  let P' : Sylow 2 (SL(2, F)) :=
    (utriSylow F).mapSurjective (f := (MulAut.conj u).toMonoidHom)
      (MulAut.conj u).surjective
  have hP'coe : (P' : Subgroup SL(2, F)) = T' := by
    rw [hT'_eq_utri]
    change Subgroup.map (MulAut.conj u).toMonoidHom (utri F) =
      conjSubgroup u (utri F)
    rfl
  have hP'_le_N : (P' : Subgroup SL(2, F)) ≤
      Subgroup.normalizer (T' : Set SL(2, F)) := by
    rw [hP'coe]
    exact Subgroup.le_normalizer
  let P'sub : Sylow 2 ↥(Subgroup.normalizer (T' : Set SL(2, F))) :=
    P'.subtype hP'_le_N
  have hP'sub_coe : (P'sub : Subgroup ↥(Subgroup.normalizer (T' : Set SL(2, F)))) =
      T'.subgroupOf (Subgroup.normalizer (T' : Set SL(2, F))) := by
    rw [Sylow.coe_subtype, hP'coe]
  have hP'sub_normal : ((P'sub : Subgroup ↥(Subgroup.normalizer (T' : Set SL(2, F))))).Normal := by
    rw [hP'sub_coe]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.le_normalizer)).mpr le_rfl
  haveI : Unique (Sylow 2 ↥(Subgroup.normalizer (T' : Set SL(2, F)))) :=
    Sylow.unique_of_normal P'sub hP'sub_normal
  intro Q hQ
  obtain ⟨Q', hQ'⟩ := hQ.exists_le_sylow
  have hQ'eq : Q' = P'sub := Subsingleton.elim Q' P'sub
  rw [hQ'eq, hP'sub_coe] at hQ'
  exact hQ'

private theorem inf_normalizer_eq_bot_of_inf_eq_bot {F : Type} [Field F] [Fintype F]
    [CharP F 2] {T T' : Subgroup SL(2, F)} (hT2 : IsPGroup 2 T)
    (hT_inter_T' : T ⊓ T' = ⊥)
    (hQ_le_T' : ∀ Q : Subgroup ↥(Subgroup.normalizer (T' : Set SL(2, F))),
      IsPGroup 2 Q → Q ≤ T'.subgroupOf (Subgroup.normalizer (T' : Set SL(2, F)))) :
    T ⊓ Subgroup.normalizer (T' : Set SL(2, F)) = ⊥ := by
  have hT_inter_N : T ⊓ Subgroup.normalizer (T' : Set SL(2, F)) ≤ T' := by
    have hQ2 : IsPGroup 2 ((T ⊓ Subgroup.normalizer (T' : Set SL(2, F))).subgroupOf
        (Subgroup.normalizer (T' : Set SL(2, F)))) := by
      have hEq : (T ⊓ Subgroup.normalizer (T' : Set SL(2, F))).subgroupOf
          (Subgroup.normalizer (T' : Set SL(2, F))) =
          T.subgroupOf (Subgroup.normalizer (T' : Set SL(2, F))) := by
        ext z
        simp [Subgroup.mem_subgroupOf]
      rw [hEq]
      exact hT2.comap_subtype
    have hQle := hQ_le_T' _ hQ2
    intro z hz
    have hzN : z ∈ Subgroup.normalizer (T' : Set SL(2, F)) := (Subgroup.mem_inf.mp hz).2
    have hzQ : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (T' : Set SL(2, F)))) ∈
        (T ⊓ Subgroup.normalizer (T' : Set SL(2, F))).subgroupOf
          (Subgroup.normalizer (T' : Set SL(2, F))) := Subgroup.mem_subgroupOf.mpr hz
    exact Subgroup.mem_subgroupOf.mp (hQle hzQ)
  rw [eq_bot_iff]
  exact (le_inf inf_le_left hT_inter_N).trans (le_of_eq hT_inter_T')

private theorem inf_normalizer_map_eq_bot_of_sl2 {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) {L L' : Subgroup (HBar V H)} {T T' : Subgroup SL(2, F)}
    (hT : T = Subgroup.map ψ.toMonoidHom L) (hT' : T' = Subgroup.map ψ.toMonoidHom L')
    (h : T ⊓ Subgroup.normalizer (T' : Set SL(2, F)) = ⊥) :
    L ⊓ Subgroup.normalizer (L' : Set (HBar V H)) = ⊥ := by
  rw [eq_bot_iff] at h ⊢
  intro z hz
  have hzL : z ∈ L := (Subgroup.mem_inf.mp hz).1
  have hzN : z ∈ Subgroup.normalizer (L' : Set (HBar V H)) := (Subgroup.mem_inf.mp hz).2
  have hzT : ψ z ∈ T := by
    rw [hT]
    exact Subgroup.mem_map.mpr ⟨z, hzL, rfl⟩
  have hNmap : Subgroup.map ψ.toMonoidHom (Subgroup.normalizer (L' : Set (HBar V H))) =
      Subgroup.normalizer (T' : Set SL(2, F)) := by
    rw [hT']
    exact Subgroup.map_normalizer_eq_of_bijective L' ψ.bijective
  have hzN' : ψ z ∈ Subgroup.normalizer (T' : Set SL(2, F)) := by
    rw [← hNmap]
    exact Subgroup.mem_map.mpr ⟨z, hzN, rfl⟩
  have hzbot : ψ z ∈ (⊥ : Subgroup SL(2, F)) := h (Subgroup.mem_inf.mpr ⟨hzT, hzN'⟩)
  have hz1 : ψ z = 1 := Subgroup.mem_bot.mp hzbot
  exact Subgroup.mem_bot.mpr (ψ.injective (by simpa using hz1))

private theorem conj_utri_eq_of_map_conj {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) {y : G} (hyH : y ∈ H) {L L' : Subgroup (HBar V H)}
    {T T' : Subgroup SL(2, F)}
    (hL'_eq : L' = conjSubgroup (piK V H ⟨y, hyH⟩) L)
    (hT : T = Subgroup.map ψ.toMonoidHom L)
    (hT' : T' = Subgroup.map ψ.toMonoidHom L')
    {x : SL(2, F)} (hT_eq : T = conjSubgroup x (utri F)) :
    T' = conjSubgroup (ψ (piK V H ⟨y, hyH⟩) * x) (utri F) := by
  rw [hT', hL'_eq, map_conjSubgroup ψ.toMonoidHom, ← hT, hT_eq,
    conjSubgroup_conjSubgroup]
  rfl

theorem inf_imgK_normalizer_conj_eq_bot_of_ne (h : RootHyp M V)
    (hPH : Pc M V ≤ H) {y : G} (hyH : y ∈ H)
    (hne : imgK V H (conjSubgroup y (Pc M V)) ≠ imgK V H (Pc M V))
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) :
    imgK V H (Pc M V) ⊓ Subgroup.normalizer
      (imgK V H (conjSubgroup y (Pc M V)) : Set (HBar V H)) = ⊥ := by
  classical
  haveI : Finite F := Finite.of_fintype F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup (HBar V H) := imgK V H (Pc M V)
  let L' : Subgroup (HBar V H) := imgK V H (conjSubgroup y (Pc M V))
  let T : Subgroup SL(2, F) := Subgroup.map ψ.toMonoidHom L
  let T' : Subgroup SL(2, F) := Subgroup.map ψ.toMonoidHom L'
  have hL2 : IsPGroup 2 L :=
    ((inSubgroup_pCore_two M).1.to_le inf_le_left).comap_subtype.map (piK V H)
  have hL'2 : IsPGroup 2 L' :=
    (((inSubgroup_pCore_two M).1.to_le inf_le_left).map (MulAut.conj y).toMonoidHom).comap_subtype.map
      (piK V H)
  have hL_ne_L' : L ≠ L' := fun heq => hne heq.symm
  have hL'_eq : L' = conjSubgroup (piK V H ⟨y, hyH⟩) L := by
    simpa [L, L'] using (imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) hyH hPH)
  have hL_ne : L ≠ ⊥ := by
    intro hbot
    apply hL_ne_L'
    rw [hL'_eq, hbot, conjSubgroup_bot]
  have hL'_ne : L' ≠ ⊥ := by
    rw [hL'_eq]
    intro hbot
    apply hL_ne
    have h := congrArg (conjSubgroup (piK V H ⟨y, hyH⟩)⁻¹) hbot
    simpa [conjSubgroup_conjSubgroup, conjSubgroup_one, conjSubgroup_bot] using h
  have hT2 : IsPGroup 2 T := hL2.map ψ.toMonoidHom
  have hT'2 : IsPGroup 2 T' := hL'2.map ψ.toMonoidHom
  have hT_ne : T ≠ ⊥ := by
    intro hbot
    apply hL_ne
    exact Subgroup.map_injective ψ.injective (by simpa [T] using hbot)
  have hT'_ne : T' ≠ ⊥ := by
    intro hbot
    apply hL'_ne
    exact Subgroup.map_injective ψ.injective (by simpa [T'] using hbot)
  have hT_ne_T' : T ≠ T' := by
    intro hEq
    apply hL_ne_L'
    exact Subgroup.map_injective ψ.injective (by simpa [T, T'] using hEq)
  have hwcL : ∀ g : HBar V H, conjSubgroup g L ≤
      Subgroup.normalizer (L : Set (HBar V H)) → conjSubgroup g L = L := by
    simpa [L] using imgK_weaklyClosed h hPH
  have hwcT : ∀ s : SL(2, F), conjSubgroup s T ≤
      Subgroup.normalizer (T : Set SL(2, F)) → conjSubgroup s T = T :=
    weaklyClosed_map_of_bijective ψ (by simpa [L, T] using hwcL)
  have hcardT : Nat.card T = Fintype.card F :=
    (card_eq_of_weaklyClosed hT2 hT_ne hwcT).1
  obtain ⟨x, hT_eq⟩ := exists_conj_eq_utri hT2 hT_ne hwcT
  have hT'_eq_utri : T' = conjSubgroup (ψ (piK V H ⟨y, hyH⟩) * x) (utri F) :=
    conj_utri_eq_of_map_conj ψ hyH hL'_eq rfl rfl hT_eq
  have hQ_le_T' := isPGroup_le_subgroupOf_normalizer_sl2 hT'_eq_utri
  have hwcT' : ∀ s' : SL(2, F), conjSubgroup s' T' ≤
      Subgroup.normalizer (T' : Set SL(2, F)) → conjSubgroup s' T' = T' := by
    intro s' hs'
    have hQ2 : IsPGroup 2 ((conjSubgroup s' T').subgroupOf
        (Subgroup.normalizer (T' : Set SL(2, F)))) :=
      (hT'2.map (MulAut.conj s').toMonoidHom).comap_subtype
    have hQle := hQ_le_T' _ hQ2
    have hle : conjSubgroup s' T' ≤ T' := by
      intro z hz
      have hzN : z ∈ Subgroup.normalizer (T' : Set SL(2, F)) := hs' (by simpa using hz)
      have hzQ : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (T' : Set SL(2, F)))) ∈
          (conjSubgroup s' T').subgroupOf
            (Subgroup.normalizer (T' : Set SL(2, F))) := Subgroup.mem_subgroupOf.mpr hz
      exact Subgroup.mem_subgroupOf.mp (hQle hzQ)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
  have hT_inter_T' : T ⊓ T' = ⊥ :=
    inf_eq_bot_of_weaklyClosed_ne hT2 hT_ne hwcT hT'2 hT'_ne hwcT' hT_ne_T'
  have hT_inter_N_bot : T ⊓ Subgroup.normalizer (T' : Set SL(2, F)) = ⊥ :=
    inf_normalizer_eq_bot_of_inf_eq_bot hT2 hT_inter_T' hQ_le_T'
  exact inf_normalizer_map_eq_bot_of_sl2 ψ rfl rfl hT_inter_N_bot

theorem inf_imgK_normalizer_eq_bot_of_sl2 (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (ψ : HBar V H ≃* SL(2, F)) :
    imgK V H (Pc M V) ⊓ Subgroup.normalizer
      (imgK V H (conjSubgroup h₀ (Pc M V)) : Set (HBar V H)) = ⊥ := by
  obtain ⟨y, hyH, hPy, -, hHy⟩ := exists_mem_conj_eq_of_eq_sup h hPH hH
  have hmain := inf_imgK_normalizer_conj_eq_bot_of_ne h hPH hyH
    (imgK_ne_bot_and_ne_of_sup h hPH hHy hnM).2.symm ψ
  rwa [← hPy] at hmain


end RootHyp

end CFSG.RankThree.GF2n.Tim81
