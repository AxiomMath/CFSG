module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentSylowT
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentTransferData
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentClasses
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3

public section

namespace CFSG.OddTranspositions.PartThree.Wong.SplitData

open Subgroup
open scoped Pointwise
open CFSG.BenderSuzuki.External
open CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G] (D : SplitData G)

theorem A_le_commutator_map {K0 : Subgroup D.X} (hidx : K0.index = 2) :
    D.A ≤ (commutator K0).map (D.X.subtype.comp K0.subtype) := by
  have hA_le_X : D.A ≤ D.X := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (D.d_commute_u x).eq
  have hX_le_K0 : commutator D.X ≤ K0 := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    have key : ∀ u v : D.X, u * v ∈ K0 ↔ (u ∈ K0 ↔ v ∈ K0) :=
      fun u v => Subgroup.mul_mem_iff_of_index_two hidx
    have h : a * b * a⁻¹ * b⁻¹ ∈ K0 := by
      rw [key, key, key, Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
      tauto
    exact h
  have hA_eq : D.A = ⁅D.A, D.A⁆ :=
    D.commutator_A_eq.symm.trans (Subgroup.map_subtype_commutator D.A)
  have hA_le_K0G : D.A ≤ K0.map D.X.subtype := by
    calc D.A = ⁅D.A, D.A⁆ := hA_eq
      _ ≤ ⁅D.X, D.X⁆ := Subgroup.commutator_mono hA_le_X hA_le_X
      _ = (commutator D.X).map D.X.subtype := (Subgroup.map_subtype_commutator D.X).symm
      _ ≤ K0.map D.X.subtype := Subgroup.map_mono hX_le_K0
  calc D.A = ⁅D.A, D.A⁆ := hA_eq
    _ ≤ ⁅K0.map D.X.subtype, K0.map D.X.subtype⁆ :=
        Subgroup.commutator_mono hA_le_K0G hA_le_K0G
    _ = (commutator K0).map (D.X.subtype.comp K0.subtype) := by
        rw [← Subgroup.map_commutator, ← Subgroup.map_subtype_commutator, Subgroup.map_map]

theorem exists_sylow_map_eq_M {K0 : Subgroup D.X} (hK0 : K0.Normal) (hidx : K0.index = 2)
    (hK0T : K0.map D.X.subtype ⊓ D.T = D.M) :
    ∃ M1 : Sylow 2 K0, (M1 : Subgroup K0).map (D.X.subtype.comp K0.subtype) = D.M := by
  let f : K0 →* G := D.X.subtype.comp K0.subtype
  have hf : Function.Injective f := D.X.subtype_injective.comp K0.subtype_injective
  have hfr : f.range = K0.map D.X.subtype := by
    show (D.X.subtype.comp K0.subtype).range = K0.map D.X.subtype
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hM_le_K0G : D.M ≤ K0.map D.X.subtype := by rw [← hK0T]; exact inf_le_left
  have hM_le_range : D.M ≤ f.range := by rwa [hfr]
  let M1s : Subgroup K0 := D.M.comap f
  have hM1map : M1s.map f = D.M := Subgroup.map_comap_eq_self hM_le_range
  have hcardM : Nat.card D.M = 16 := D.transfer_subgroup_data.1
  have hM_pgroup : IsPGroup 2 D.M := IsPGroup.of_card (n := 4) (by rw [hcardM]; norm_num)
  have hM1_pgroup : IsPGroup 2 M1s := hM_pgroup.comap_of_injective f hf
  obtain ⟨P_T, hP_T⟩ :=
    D.second_centralizer_sylow_presentation.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hcardT : Nat.card D.T = 32 := D.card_T
  have hPT_card : Nat.card (P_T : Subgroup D.X) = 32 := by
    rw [← hcardT, ← hP_T, Subgroup.card_map_of_injective D.X.subtype_injective]
  have hcardX : Nat.card D.X = 32 * P_T.index := by
    have h := Subgroup.card_mul_index (H := (P_T : Subgroup D.X))
    rw [hPT_card] at h
    exact h.symm
  have hcardK0 : Nat.card K0 = 16 * P_T.index := by
    have h := Subgroup.card_mul_index (H := K0)
    rw [hidx, hcardX] at h
    have h' : Nat.card K0 * 2 = (16 * P_T.index) * 2 := by rw [h]; ring
    exact Nat.mul_right_cancel (by norm_num : (0 : ℕ) < 2) h'
  have hcardM1s : Nat.card M1s = 16 := by
    rw [← Subgroup.card_map_of_injective (f := f) hf, hM1map, hcardM]
  have hM1_index : M1s.index = P_T.index := by
    rw [Subgroup.index_eq_card_div, hcardM1s, hcardK0]
    exact Nat.mul_div_right P_T.index (by norm_num : (0 : ℕ) < 16)
  have hodd : ¬ 2 ∣ M1s.index := by
    rw [hM1_index]
    exact P_T.not_dvd_index
  exact ⟨hM1_pgroup.toSylow hodd, by rw [IsPGroup.toSylow_coe]; exact hM1map⟩

theorem grun_focal_eq_four {K0 : Subgroup D.X} (hK0 : K0.Normal) (hidx : K0.index = 2)
    (hK0T : K0.map D.X.subtype ⊓ D.T = D.M) :
    normalizer (D.M : Set G) ⊓ K0.map D.X.subtype = D.M ∧
    D.M ⊓ (commutator K0).map (D.X.subtype.comp K0.subtype) = D.J := by
  let f : K0 →* G := D.X.subtype.comp K0.subtype
  have hf : Function.Injective f := D.X.subtype_injective.comp K0.subtype_injective
  have hfr : f.range = K0.map D.X.subtype := by
    show (D.X.subtype.comp K0.subtype).range = K0.map D.X.subtype
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hM_le_K0G : D.M ≤ K0.map D.X.subtype := by rw [← hK0T]; exact inf_le_left
  have hM_le_range : D.M ≤ f.range := by rwa [hfr]
  have hpart1 : normalizer (D.M : Set G) ⊓ K0.map D.X.subtype = D.M := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgnorm, hgK0G⟩ := mem_inf.mp hg
      have hmap : D.M.map (MulAut.conj g).toMonoidHom = D.M :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hgnorm
      have hMder : ⁅D.M, D.M⁆ = zpowers D.v := by
        rw [← Subgroup.map_subtype_commutator D.M, D.commutator_M_eq]
      have hconj_der : (zpowers D.v).map (MulAut.conj g).toMonoidHom = zpowers D.v := by
        rw [← hMder, Subgroup.map_commutator, hmap]
      have hv_conj : g * D.v * g⁻¹ ∈ zpowers D.v := by
        rw [← hconj_der]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers D.v)
      rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_v).mp hv_conj with hv1 | hv2
      · exfalso
        have hv_eq_one : D.v = 1 := by
          have := congrArg (fun t => g⁻¹ * t * g) hv1
          simpa [mul_assoc] using this
        have h2 := D.orderOf_v
        rw [hv_eq_one, orderOf_one] at h2
        norm_num at h2
      · have hgCv : g ∈ centralizer ({D.v} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc g * D.v = g * D.v * g⁻¹ * g := by group
            _ = D.v * g := by rw [hv2]
        have hgX : g ∈ D.X := by
          have := Subgroup.map_le_range (f := D.X.subtype) K0 hgK0G
          rwa [Subgroup.range_subtype] at this
        have hgT : g ∈ D.T := mem_inf.mpr ⟨hgX, hgCv⟩
        exact hK0T ▸ mem_inf.mpr ⟨hgK0G, hgT⟩
    · exact le_inf Subgroup.le_normalizer hM_le_K0G
  obtain ⟨M1, hM1map⟩ := D.exists_sylow_map_eq_M hK0 hidx hK0T
  have hM1map' : (M1 : Subgroup K0).map f = D.M := hM1map
  have hgrun : (M1 : Subgroup K0) ⊓ commutator K0 =
      huppertIV34GrunKernelSubgroup (Q := K0) (M1 : Subgroup K0) :=
    huppert_IV_3_4_first_grun (Q := K0) (q := 2) M1
  have hN : Subgroup.normalizer ((M1 : Subgroup K0) : Set K0) = (M1 : Subgroup K0) := by
    apply le_antisymm
    · intro n hn
      have hmap : (M1 : Subgroup K0).map (MulAut.conj n).toMonoidHom = (M1 : Subgroup K0) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
      have hfn_norm : f n ∈ normalizer (D.M : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        rw [← hM1map']
        calc ((M1 : Subgroup K0).map f).map (MulAut.conj (f n)).toMonoidHom
            = (M1 : Subgroup K0).map ((MulAut.conj (f n)).toMonoidHom.comp f) :=
              Subgroup.map_map (M1 : Subgroup K0) (MulAut.conj (f n)).toMonoidHom f
          _ = (M1 : Subgroup K0).map (f.comp (MulAut.conj n).toMonoidHom) := by
              congr 1
          _ = ((M1 : Subgroup K0).map (MulAut.conj n).toMonoidHom).map f :=
              (Subgroup.map_map (M1 : Subgroup K0) f
                (MulAut.conj n).toMonoidHom).symm
          _ = (M1 : Subgroup K0).map f := by rw [hmap]
      have hfn_K0G : f n ∈ K0.map D.X.subtype := by
        rw [← hfr]
        exact ⟨n, rfl⟩
      have hfn_M : f n ∈ D.M := hpart1 ▸ mem_inf.mpr ⟨hfn_norm, hfn_K0G⟩
      rw [← hM1map'] at hfn_M
      rcases Subgroup.mem_map.mp hfn_M with ⟨m, hm, hfm⟩
      exact (hf hfm) ▸ hm
    · intro n hn
      exact Subgroup.le_normalizer hn
  let Pder : Subgroup K0 := (commutator (M1 : Subgroup K0)).map (M1 : Subgroup K0).subtype
  have hPder_map : Pder.map f = zpowers D.v := by
    have hPder_eq : Pder = ⁅(M1 : Subgroup K0), (M1 : Subgroup K0)⁆ := by
      rw [show Pder = (commutator (M1 : Subgroup K0)).map (M1 : Subgroup K0).subtype from rfl,
        Subgroup.map_subtype_commutator]
    rw [hPder_eq, Subgroup.map_commutator, hM1map',
      ← Subgroup.map_subtype_commutator D.M, D.commutator_M_eq]
  have hA_le_K0' : D.A ≤ (commutator K0).map f := D.A_le_commutator_map hidx
  have hA_le_range : D.A ≤ f.range :=
    hA_le_K0'.trans (by
      rw [← Subgroup.map_top f]
      exact Subgroup.map_mono (le_top : commutator (↥K0) ≤ ⊤))
  have hJ_le_A : D.J ≤ D.A := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | rfl)
    · exact ⟨hM, rfl⟩
    · exact ⟨cM, rfl⟩
  have hJ_le_range : D.J ≤ f.range := hJ_le_A.trans hA_le_range
  let J1 : Subgroup K0 := D.J.comap f
  have hker_le_J1 : huppertIV34GrunKernelSubgroup (Q := K0) (M1 : Subgroup K0) ≤ J1 := by
    have mem_rc : ∀ {H : Subgroup K0} {g y : K0},
        y ∈ rightConjugate H g ↔ g * y * g⁻¹ ∈ H := by
      intro H g y
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [mul_assoc] using hz
      · intro h
        exact ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩
    rw [huppertIV34GrunKernelSubgroup_def, hN]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y (⟨hyP, hyN'⟩ | ⟨g, hyP, hyg⟩)
    · have hyPder : y ∈ Pder := hyN'
      have hmem : f y ∈ Pder.map f := Subgroup.mem_map_of_mem f hyPder
      rw [hPder_map] at hmem
      exact Subgroup.mem_comap.mpr
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hmem)
    · have hy_conj : g * y * g⁻¹ ∈ Pder := mem_rc.mp hyg
      have hmem : f (g * y * g⁻¹) ∈ Pder.map f := Subgroup.mem_map_of_mem f hy_conj
      rw [map_mul, map_mul, map_inv, hPder_map] at hmem
      rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_v).mp hmem with h1 | hveq
      · have hfy1 : f y = 1 := by
          have := congrArg (fun t => (f g)⁻¹ * t * (f g)) h1
          simpa [mul_assoc] using this
        exact Subgroup.mem_comap.mpr (by rw [hfy1]; exact Subgroup.one_mem _)
      · have hfy_M : f y ∈ D.M := by
          rw [← hM1map']
          exact Subgroup.mem_map_of_mem f hyP
        have hconj : IsConj D.v (f y) := by
          refine isConj_iff.mpr ⟨(f g)⁻¹, ?_⟩
          rw [inv_inv, ← hveq]
          group
        have hfy_eq : f y = (f g)⁻¹ * D.v * (f g) := by rw [← hveq]; group
        have hfy_sq : (f y) ^ 2 = 1 := by
          rw [pow_two, hfy_eq]
          calc (f g)⁻¹ * D.v * (f g) * ((f g)⁻¹ * D.v * (f g))
              = (f g)⁻¹ * (D.v * D.v) * (f g) := by group
            _ = 1 := by rw [D.v_mul_v, mul_one, inv_mul_cancel]
        have hfy_ne_one : f y ≠ 1 := by
          intro h
          have h1 : (f g)⁻¹ * D.v * (f g) = 1 := by rw [← hfy_eq]; exact h
          have hv1 : D.v = 1 := by
            have := congrArg (fun t => f g * t * (f g)⁻¹) h1
            simpa [mul_assoc] using this
          have h2 := D.orderOf_v
          rw [hv1, orderOf_one] at h2
          norm_num at h2
        have horder : orderOf (f y) = 2 := orderOf_eq_prime hfy_sq hfy_ne_one
        have hlist := D.transfer_subgroup_data.2.2.2.2.2.2.2.1 (f y) hfy_M
        rcases (hlist.mp horder) with hxu | hxv | hxw | hxvw | hxuv | hxuw | hxuvw
        · exfalso
          have hfgK0G : f g ∈ K0.map D.X.subtype := by rw [← hfr]; exact ⟨g, rfl⟩
          have hfgX : f g ∈ D.X := by
            have := Subgroup.map_le_range (f := D.X.subtype) K0 hfgK0G
            rwa [Subgroup.range_subtype] at this
          have hcomm : f g * D.u = D.u * f g :=
            Subgroup.mem_centralizer_singleton_iff.mp hfgX
          rw [hxu] at hveq
          have : D.v = D.u := by
            rw [← hveq]
            rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
          exact D.v_ne_u this
        · exact Subgroup.mem_comap.mpr (hxv ▸ Subgroup.subset_closure (by simp))
        · exact Subgroup.mem_comap.mpr (hxw ▸ Subgroup.subset_closure (by simp))
        · exact Subgroup.mem_comap.mpr
            (hxvw ▸ mul_mem (Subgroup.subset_closure (by simp))
              (Subgroup.subset_closure (by simp)))
        · exfalso
          have ht_fy : IsConj D.t (f y) := by rw [hxuv]; exact D.isConj_t_u_mul (Or.inl rfl)
          exact D.not_isConj_t_u ((ht_fy.trans hconj.symm).trans D.isConj_u_v.symm)
        · exfalso
          have ht_fy : IsConj D.t (f y) := by
            rw [hxuw]; exact D.isConj_t_u_mul (Or.inr (Or.inl rfl))
          exact D.not_isConj_t_u ((ht_fy.trans hconj.symm).trans D.isConj_u_v.symm)
        · exfalso
          have ht_fy : IsConj D.t (f y) := by
            rw [hxuvw, mul_assoc]; exact D.isConj_t_u_mul (Or.inr (Or.inr rfl))
          exact D.not_isConj_t_u ((ht_fy.trans hconj.symm).trans D.isConj_u_v.symm)
  have hker_image_le :
      (huppertIV34GrunKernelSubgroup (Q := K0) (M1 : Subgroup K0)).map f ≤ D.J := by
    calc _ ≤ J1.map f := Subgroup.map_mono hker_le_J1
      _ = D.J := by
        rw [show J1 = D.J.comap f from rfl, Subgroup.map_comap_eq_self hJ_le_range]
  have hpart2 : D.M ⊓ (commutator K0).map f = D.J := by
    apply le_antisymm
    · calc D.M ⊓ (commutator K0).map f
          = ((M1 : Subgroup K0) ⊓ commutator K0).map f := by
              rw [Subgroup.map_inf_eq _ _ f hf, hM1map']
        _ = (huppertIV34GrunKernelSubgroup (Q := K0) (M1 : Subgroup K0)).map f := by
              rw [hgrun]
        _ ≤ D.J := hker_image_le
    · exact le_inf (D.J_le_W.trans D.W_le_M) (hJ_le_A.trans hA_le_K0')
  exact ⟨hpart1, hpart2⟩

end CFSG.OddTranspositions.PartThree.Wong.SplitData
