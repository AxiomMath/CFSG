module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalDetWitness
public import Certificates.Data.J3Comm

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.Open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
open scoped Matrix commutatorElement

theorem commTriple_of_check {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
    [Inhabited M] [Inhabited V] (hWF : ∀ X : M, Sp.WF X) (D : CommTripleData)
    (hc : O.commTripleCheck D = true) :
    ∃ K : Subgroup (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ,
      Nat.card K = D.base.nP ∧ 9 < Nat.card {x : ↥(commutator ↥K) // x ^ 3 = 1} := by
  classical
  set S := NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB
  unfold Ops.commTripleCheck at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨-, hprog⟩, hregs⟩, hgen⟩, henum⟩, hfacts⟩ := hc
  unfold SylowCentralData.regsLt at hregs
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hregs
  obtain ⟨rk1, rk2, -, -⟩ := hregs
  set R := O.regsOf D.base.seedA D.base.seedB D.base.nregs D.base.prog
  set En := O.enumBFS #[R[D.base.rk1]!, R[D.base.rk2]!] D.base.nP
  unfold Ops.sylowGenFacts at hgen
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hgen
  obtain ⟨⟨⟨ho1, ho2⟩, hK1⟩, hK2⟩ := hgen
  have mem : ∀ {r}, r < D.base.nregs → Sp.toMat R[r]! ∈ S := fun hr => (Sp.regsOf_ok hprog hr).2
  have eK1 := Sp.pow_eq_one_of_check (hWF _) hK1
  have eK2 := Sp.pow_eq_one_of_check (hWF _) hK2
  let k1 := unitOf S (mem rk1) ho1.ne' eK1
  let k2 := unitOf S (mem rk2) ho2.ne' eK2
  have f1 : valHom S k1 = Sp.toMat R[D.base.rk1]! := valHom_unitOf S _ _ _
  have f2 : valHom S k2 = Sp.toMat R[D.base.rk2]! := valHom_unitOf S _ _ _
  obtain ⟨e, emat, emem, eall, einj⟩ := Sp.enum_spec hWF f1 f2 ho1.ne' ho2.ne'
    (unitOf_pow S _ _ eK1) (unitOf_pow S _ _ eK2) henum
  set K := Subgroup.closure ({k1, k2} : Set Sˣ)
  have hEsize : En.1.size = D.base.nP := by
    unfold Ops.enumOK at henum
    simp only [Bool.and_eq_true, beq_iff_eq] at henum
    exact henum.1.1.1.1.1.1.1.1
  have hFbij : ∃ F : Fin D.base.nP → K, Function.Bijective F := by
    let F : Fin D.base.nP → K := fun i => ⟨e i, emem i i.isLt⟩
    refine ⟨F, ⟨fun i j hij => Fin.ext (einj i i.isLt j j.isLt (congrArg Subtype.val hij)),
      fun u => ?_⟩⟩
    obtain ⟨i, hi, hu⟩ := eall u u.2
    exact ⟨⟨i, hi⟩, Subtype.ext hu.symm⟩
  obtain ⟨F, hF⟩ := hFbij
  haveI : Finite K := Finite.of_surjective F hF.2
  have hcardK : Nat.card K = D.base.nP := by
    rw [← Nat.card_eq_of_bijective F hF, Nat.card_fin]
  have listed : ∀ {X : M}, O.memOK En.1 X = true → ∃ u ∈ K, valHom S u = Sp.toMat X := by
    intro X hX
    obtain ⟨j, hj, hjX⟩ := Sp.memOK_spec hWF hX
    rw [hEsize] at hj
    exact ⟨e j, emem j hj, by rw [emat j hj, hjX]⟩
  unfold Ops.commTripleFacts at hfacts
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfacts
  obtain ⟨⟨hlen, hall⟩, hdist⟩ := hfacts
  rw [List.all_eq_true] at hall
  have key : ∀ t ∈ D.trip, ∃ cu : Sˣ, ∃ hcuK : cu ∈ K, cu ^ 3 = 1 ∧
      valHom S cu = Sp.toMat R[t.1]! ∧ (⟨cu, hcuK⟩ : ↥K) ∈ commutator ↥K := by
    intro t ht
    have h := hall t ht
    unfold Ops.commTripleOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hc1, hx1⟩, hg1⟩, hgsel⟩, hmem⟩, hcube⟩, hrel⟩ := h
    have hcube' := Sp.pow_eq_one_of_check (hWF _) hcube
    let cu := unitOf S (mem hc1) (by norm_num : (3 : ℕ) ≠ 0) hcube'
    have fc : valHom S cu = Sp.toMat R[t.1]! := valHom_unitOf S _ _ _
    obtain ⟨xu, hxu, fx⟩ := listed hmem
    obtain ⟨gu, hguK, fg⟩ : ∃ gu ∈ K, valHom S gu = Sp.toMat R[t.2.2]! := by
      rcases hgsel with h | h
      · exact ⟨k1, Subgroup.subset_closure (by simp), by rw [h]; exact f1⟩
      · exact ⟨k2, Subgroup.subset_closure (by simp), by rw [h]; exact f2⟩
    have hrel' : cu * (gu * xu) = xu * gu := valHom_injective S (by
      rw [map_mul, map_mul, map_mul, fc, fg, fx]
      have := Sp.toMat_eq (Sp.mul_wf (hWF _) (Sp.mul_wf (hWF _) (hWF _)))
        (Sp.mul_wf (hWF _) (hWF _)) hrel
      rwa [Sp.toMat_mul (hWF _) (Sp.mul_wf (hWF _) (hWF _)), Sp.toMat_mul (hWF _) (hWF _),
        Sp.toMat_mul (hWF _) (hWF _)] at this)
    have hcu_eq : cu = xu * gu * (xu⁻¹ * gu⁻¹) := by
      calc cu = cu * (gu * xu) * (gu * xu)⁻¹ := by rw [mul_inv_cancel_right]
        _ = xu * gu * (gu * xu)⁻¹ := by rw [hrel']
        _ = xu * gu * (xu⁻¹ * gu⁻¹) := by rw [mul_inv_rev]
    have hcuK : cu ∈ K := by
      rw [hcu_eq]
      exact K.mul_mem (K.mul_mem hxu hguK) (K.mul_mem (K.inv_mem hxu) (K.inv_mem hguK))
    refine ⟨cu, hcuK, unitOf_pow S _ _ hcube', fc, ?_⟩
    have hcomm : (⟨cu, hcuK⟩ : ↥K) = ⁅(⟨xu, hxu⟩ : ↥K), (⟨gu, hguK⟩ : ↥K)⁆ := by
      apply Subtype.ext
      rw [commutatorElement_def]
      show cu = xu * gu * xu⁻¹ * gu⁻¹
      rw [hcu_eq]
      simp only [mul_assoc]
    rw [hcomm, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  choose cu hcuK hcu3 hcuval hcuc using key
  let G : Fin D.trip.length → {x : ↥(commutator ↥K) // x ^ 3 = 1} := fun i =>
    ⟨⟨⟨cu D.trip[i] (List.getElem_mem i.isLt), hcuK _ (List.getElem_mem i.isLt)⟩,
      hcuc _ (List.getElem_mem i.isLt)⟩,
      Subtype.ext (Subtype.ext (hcu3 _ (List.getElem_mem i.isLt)))⟩
  have hvne : ∀ a b : Fin D.trip.length, (b : ℕ) < a →
      O.vne (O.vmul (O.unit D.base.t) R[(D.trip[a]).1]!)
        (O.vmul (O.unit D.base.t) R[(D.trip[b]).1]!) = true := by
    intro a b hba
    unfold Ops.distinctOK at hdist
    rw [List.all_eq_true] at hdist
    have h1 := hdist a (List.mem_range.2 (by simp))
    rw [List.all_eq_true] at h1
    have h2 := h1 b (List.mem_range.2 hba)
    simpa using h2
  have hvec : ∀ a b : Fin D.trip.length, (b : ℕ) < a →
      Sp.toMat R[(D.trip[a]).1]! = Sp.toMat R[(D.trip[b]).1]! → False := by
    intro a b hba hab
    apply Sp.toVec_ne (hvne a b hba)
    rw [Sp.toVec_vmul (Sp.unit_wf _) (hWF _), Sp.toVec_vmul (Sp.unit_wf _) (hWF _), hab]
  have hGinj : Function.Injective G := by
    intro i j hij
    by_contra hne
    have hcu : cu D.trip[i] (List.getElem_mem i.isLt) = cu D.trip[j] (List.getElem_mem j.isLt) :=
      congrArg Subtype.val (congrArg Subtype.val (congrArg Subtype.val hij))
    have hmat : Sp.toMat R[(D.trip[i]).1]! = Sp.toMat R[(D.trip[j]).1]! :=
      (hcuval _ (List.getElem_mem i.isLt)).symm.trans
        ((congrArg (valHom S) hcu).trans (hcuval _ (List.getElem_mem j.isLt)))
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact hvec j i h hmat.symm
    · exact hvec i j h hmat
  refine ⟨K, hcardK, ?_⟩
  have hcard := Nat.card_le_card_of_injective G hGinj
  rw [Nat.card_fin] at hcard
  omega

end CFSG.RankThree.PartTwo.Sec11
