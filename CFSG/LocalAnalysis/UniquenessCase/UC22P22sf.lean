module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22se
import CFSG.Quasithin.Background.A312SporAlt5
import CFSG.RankThree.PartOne.KFCL.L4Block
public import CFSG.Milestones.ASVolI.B1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped MatrixGroups commutatorElement Pointwise

namespace P22s

section DirProd

variable {X : Type} [Group X] {s : ℕ} {J : Subgroup X} {Hs : Fin s → Subgroup X}

theorem dirProd_pairwise (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) :
    Pairwise fun i j => ∀ x y : X, x ∈ Hs i → y ∈ Hs j → Commute x y :=
  fun i j hij x y hx hy => h.1 i j hij x hx y hy

noncomputable abbrev dirMap (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) : (∀ i, ↥(Hs i)) →* X :=
  Subgroup.noncommPiCoprod (dirProd_pairwise h)

theorem dirMap_injective (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) : Function.Injective (dirMap h) :=
  Subgroup.injective_noncommPiCoprod_of_iSupIndep h.2.1

theorem dirMap_range (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) : (dirMap h).range = J := by
  rw [Subgroup.noncommPiCoprod_range, h.2.2]

@[expose] noncomputable def dirEquiv (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) : (∀ i, ↥(Hs i)) ≃* ↥J :=
  (MonoidHom.ofInjective (dirMap_injective h)).trans (MulEquiv.subgroupCongr (dirMap_range h))

theorem dirEquiv_apply (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (u : ∀ i, ↥(Hs i)) :
    ((dirEquiv h u : ↥J) : X) = dirMap h u := rfl

@[expose] noncomputable def dirProj (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (i : Fin s) : ↥J →* ↥(Hs i) :=
  (Pi.evalMonoidHom (fun i => ↥(Hs i)) i).comp (dirEquiv h).symm.toMonoidHom

theorem le_of_dirProd (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (i : Fin s) : Hs i ≤ J :=
  h.2.2 ▸ le_iSup Hs i

theorem dirEquiv_symm_of_mem (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) {i : Fin s} {x : X}
    (hx : x ∈ Hs i) : (dirEquiv h).symm ⟨x, le_of_dirProd h i hx⟩ = Pi.mulSingle i ⟨x, hx⟩ := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [dirEquiv_apply, dirMap, Subgroup.noncommPiCoprod_mulSingle]

theorem dirProj_of_mem (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) {i : Fin s} {x : X} (hx : x ∈ Hs i) :
    ((dirProj h i ⟨x, le_of_dirProd h i hx⟩ : ↥(Hs i)) : X) = x := by
  simp only [dirProj, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    dirEquiv_symm_of_mem h hx, Pi.evalMonoidHom_apply, Pi.mulSingle_eq_same]

theorem dirMap_dirProj (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (q : ↥J) :
    dirMap h (fun i => dirProj h i q) = q := by
  have : (fun i => dirProj h i q) = (dirEquiv h).symm q := rfl
  rw [this, ← dirEquiv_apply, MulEquiv.apply_symm_apply]

theorem conj_eq_dirProj (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (q : ↥J) {i : Fin s} {x : X}
    (hx : x ∈ Hs i) :
    (q : X) * x * (q : X)⁻¹ = (dirProj h i q : X) * x * (dirProj h i q : X)⁻¹ := by
  classical
  set u : ∀ j, ↥(Hs j) := fun j => dirProj h j q with hu
  set u' : ∀ j, ↥(Hs j) := Function.update u i 1 with hu'
  have hsplit : u = Pi.mulSingle i (u i) * u' := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [hu']
    · simp [hu', hji]
  have hq : (q : X) = (u i : X) * dirMap h u' := by
    calc (q : X) = dirMap h u := (dirMap_dirProj h q).symm
      _ = dirMap h (Pi.mulSingle i (u i) * u') := by rw [← hsplit]
      _ = (u i : X) * dirMap h u' := by
        rw [map_mul, dirMap, Subgroup.noncommPiCoprod_mulSingle]
  have hc : Commute x (dirMap h u') := by
    rw [dirMap, Subgroup.noncommPiCoprod_apply]
    refine Finset.noncommProd_induction _ _ _ (fun y => Commute x y)
      (fun a b ha hb => ha.mul_right hb) (Commute.one_right x) fun j _ => ?_
    by_cases hji : j = i
    · subst hji
      have : u' j = 1 := by simp [hu']
      rw [this, OneMemClass.coe_one]
      exact Commute.one_right x
    · exact h.1 i j (Ne.symm hji) x hx _ (u' j).2
  have hw : dirMap h u' * x * (dirMap h u')⁻¹ = x := by
    rw [← hc.eq, mul_inv_cancel_right]
  calc (q : X) * x * (q : X)⁻¹ = (u i : X) * (dirMap h u' * x * (dirMap h u')⁻¹) * (u i : X)⁻¹ := by
        rw [hq]; group
    _ = (u i : X) * x * (u i : X)⁻¹ := by rw [hw]

theorem le_normalizer_of_conj {K A : Subgroup X} (h : ∀ y ∈ K, ∀ x ∈ A, y * x * y⁻¹ ∈ A) :
    K ≤ normalizer (A : Set X) := by
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h y hy x, fun hx => ?_⟩
  have := h y⁻¹ (K.inv_mem hy) _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_of_dirProd (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (i : Fin s) :
    J ≤ normalizer (Hs i : Set X) := by
  refine le_normalizer_of_conj fun q hq x hx => ?_
  rw [conj_eq_dirProj h ⟨q, hq⟩ hx]
  exact (Hs i).mul_mem ((Hs i).mul_mem (dirProj h i ⟨q, hq⟩).2 hx) ((Hs i).inv_mem (dirProj h i ⟨q, hq⟩).2)

theorem commutatorElement_eq_dirProj (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (q : ↥J) {i : Fin s}
    {x : X} (hx : x ∈ Hs i) : ⁅(q : X), x⁆ = ⁅(dirProj h i q : X), x⁆ := by
  rw [commutatorElement_def, commutatorElement_def, conj_eq_dirProj h q hx]

theorem mem_iSup_of_dirProj (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (q : ↥J) {K : Fin s → Subgroup X}
    (hK : ∀ i, (dirProj h i q : X) ∈ K i) : (q : X) ∈ ⨆ i, K i := by
  rw [← dirMap_dirProj h q, dirMap, Subgroup.noncommPiCoprod_apply]
  exact Subgroup.noncommProd_mem _ _ fun i _ => (le_iSup K i) (hK i)

end DirProd

section Small

variable {X : Type} [Group X] [Finite X]

theorem eq_bot_of_perfect_of_card_dvd_six {P : Subgroup X} (hP : ⁅P, P⁆ = P) (h6 : Nat.card P ∣ 6) :
    P = ⊥ := by
  refine CFSG.Quasithin.A312S.eq_bot_of_perfect_of_solvable hP
    (CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_)
  have hsub : (Nat.card P).primeFactors ⊆ (6 : ℕ).primeFactors :=
    Nat.primeFactors_mono h6 (by norm_num)
  have h62 : (6 : ℕ).primeFactors.card = 2 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
    decide
  exact (Finset.card_le_card hsub).trans h62.le

theorem card_sl2_galoisField_one : Nat.card SL(2, GaloisField 2 1) = 6 := by
  letI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using GaloisField.card 2 1 (by norm_num)
  rw [Matrix.card_SL_field 2, hq, Fin.prod_univ_two]
  norm_num

theorem isSimpleGroup_sl2_galoisField {e : ℕ} (he : 2 ≤ e) : IsSimpleGroup SL(2, GaloisField 2 e) := by
  refine CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup ?_
  rw [GaloisField.card 2 e (by omega)]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he

omit [Finite X] in
theorem map_conj_eq {A : Subgroup X} {n : X} (hn : n ∈ normalizer (A : Set X)) :
    A.map (MulAut.conj n).toMonoidHom = A := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_normalizer_iff.1 hn a).1 ha
  · intro hz
    refine ⟨n⁻¹ * z * n, ?_, by simp [mul_assoc]⟩
    exact (mem_normalizer_iff.1 hn (n⁻¹ * z * n)).2 (by simpa [mul_assoc] using hz)

theorem le_alternatingGroup_of_perfect {m : ℕ} {P : Subgroup (Equiv.Perm (Fin m))} (hP : ⁅P, P⁆ = P) :
    P ≤ alternatingGroup (Fin m) := by
  rw [← hP]
  refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
  rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem eq_bot_or_eq_of_isSimpleGroup {D N : Subgroup X} (hD : IsSimpleGroup ↥D) (hND : N ≤ D)
    (hDN : D ≤ normalizer (N : Set X)) : N = ⊥ ∨ N = D := by
  haveI : (N.subgroupOf D).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hND).2 hDN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf D) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hND
  · right
    exact le_antisymm hND (Subgroup.subgroupOf_eq_top.1 h)

end Small

section ProjImage

variable {X : Type} [Group X] [Finite X] {s : ℕ} {J Q : Subgroup X} {Hs : Fin s → Subgroup X}

@[expose] noncomputable def projHom (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (hQJ : Q ≤ J) (i : Fin s) :
    ↥Q →* ↥(Hs i) :=
  (dirProj h i).comp (Subgroup.inclusion hQJ)

@[expose] noncomputable def projImage (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (hQJ : Q ≤ J) (i : Fin s) :
    Subgroup X :=
  ((Hs i).subtype.comp (projHom h hQJ i)).range

theorem projImage_le (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (hQJ : Q ≤ J) (i : Fin s) :
    projImage h hQJ i ≤ Hs i := by
  rintro _ ⟨q, rfl⟩
  exact (projHom h hQJ i q).2

theorem projImage_perfect (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (hQJ : Q ≤ J) (i : Fin s)
    (hQp : ⁅Q, Q⁆ = Q) : ⁅projImage h hQJ i, projImage h hQJ i⁆ = projImage h hQJ i := by
  haveI : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQp
  exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.range _)

theorem inf_le_projImage (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (hQJ : Q ≤ J) (i : Fin s) :
    Q ⊓ Hs i ≤ projImage h hQJ i := by
  rintro x ⟨hxQ, hxi⟩
  refine ⟨⟨x, hxQ⟩, ?_⟩
  change ((dirProj h i ⟨x, hQJ hxQ⟩ : ↥(Hs i)) : X) = x
  exact dirProj_of_mem h hxi

theorem commutator_projImage (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (hQJ : Q ≤ J) (i : Fin s) :
    ⁅Q, Hs i⁆ = ⁅projImage h hQJ i, Hs i⁆ := by
  apply le_antisymm
  · refine Subgroup.commutator_le.mpr fun q hq x hx => ?_
    rw [commutatorElement_eq_dirProj h ⟨q, hQJ hq⟩ hx]
    exact Subgroup.commutator_mem_commutator ⟨⟨q, hq⟩, rfl⟩ hx
  · refine Subgroup.commutator_le.mpr fun p hp x hx => ?_
    obtain ⟨q, rfl⟩ := hp
    change ⁅((dirProj h i ⟨q, hQJ q.2⟩ : ↥(Hs i)) : X), x⁆ ∈ _
    rw [← commutatorElement_eq_dirProj h ⟨q, hQJ q.2⟩ hx]
    exact Subgroup.commutator_mem_commutator q.2 hx

theorem le_normalizer_projImage (h : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (hQJ : Q ≤ J) (i : Fin s)
    (hJQ : J ≤ normalizer (Q : Set X)) : Hs i ≤ normalizer (projImage h hQJ i : Set X) := by
  refine le_normalizer_of_conj fun x hx p hp => ?_
  obtain ⟨q, rfl⟩ := hp
  have hxJ : x ∈ J := le_of_dirProd h i hx
  have hc : x * (q : X) * x⁻¹ ∈ Q := (mem_normalizer_iff.1 (hJQ hxJ) q).1 q.2
  refine ⟨⟨_, hc⟩, ?_⟩
  change ((dirProj h i ⟨x * (q : X) * x⁻¹, hQJ hc⟩ : ↥(Hs i)) : X) =
    x * ((dirProj h i ⟨q, hQJ q.2⟩ : ↥(Hs i)) : X) * x⁻¹
  have e : (⟨x * (q : X) * x⁻¹, hQJ hc⟩ : ↥J) = ⟨x, hxJ⟩ * ⟨q, hQJ q.2⟩ * ⟨x, hxJ⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, dirProj_of_mem h hx]

end ProjImage

end P22s

open P22s

section Structure

variable {X : Type} [Group X] [Finite X] {s : ℕ} {Hst T J Q : Subgroup X} {Hs : Fin s → Subgroup X}

theorem uc22p22sf_le_J (hHJ : Hst ≤ normalizer (J : Set X)) (hprod : (J : Set X) * (T : Set X) = Hst)
    (hT2 : IsPGroup 2 T) (hQH : Q ≤ Hst) (hQp : ⁅Q, Q⁆ = Q) : Q ≤ J := by
  have hTH : T ≤ Hst := fun t ht => by
    show t ∈ (Hst : Set X)
    rw [← hprod]
    exact Set.mem_mul.mpr ⟨1, J.one_mem, t, ht, one_mul t⟩
  have hHJT : Hst ≤ J ⊔ T := fun x hx => by
    have hx' : x ∈ (Hst : Set X) := hx
    rw [← hprod] at hx'
    obtain ⟨j, hj, t, ht, hjt⟩ := Set.mem_mul.mp hx'
    rw [← hjt]
    exact (J ⊔ T).mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right ht)
  exact le_of_commutator_eq_self hT2 (hTH.trans hHJ) (hQH.trans hHJT) hQp

theorem uc22p22sf_commutator_ne_bot (hTH : T ≤ Hst) (hHQ : Hst ≤ normalizer (Q : Set X)) (hQJ : Q ≤ J)
    (hdir : CFSG.ASVolI.ChB.IsIntDirProd J Hs)
    (htrans : ∀ i j, ∃ t ∈ T, (Hs i).map (MulAut.conj t).toMonoidHom = Hs j) (hQp : ⁅Q, Q⁆ = Q)
    (hQ : Q ≠ ⊥) (i : Fin s) : ⁅Q, Hs i⁆ ≠ ⊥ := by
  intro h0
  apply hQ
  have hall : ∀ j, ⁅Hs j, Q⁆ = ⊥ := by
    intro j
    obtain ⟨t, ht, htj⟩ := htrans i j
    have hQt : Q.map (MulAut.conj t).toMonoidHom = Q :=
      map_conj_eq (hHQ (hTH ht))
    rw [Subgroup.commutator_comm, ← htj, ← hQt, ← Subgroup.map_commutator, h0, Subgroup.map_bot]
  have hJC : J ≤ centralizer (Q : Set X) := by
    rw [← hdir.2.2]
    exact iSup_le fun j => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hall j)
  rw [← hQp]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hQJ.trans hJC)

theorem uc22p22sf_factor (hdir : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (hQJ : Q ≤ J)
    (hJQ : J ≤ normalizer (Q : Set X)) (hQp : ⁅Q, Q⁆ = Q) (i : Fin s) (hne : ⁅Q, Hs i⁆ ≠ ⊥) :
    projImage hdir hQJ i = Q ⊓ Hs i ∧ ⁅Q ⊓ Hs i, Q ⊓ Hs i⁆ = Q ⊓ Hs i ∧ Q ⊓ Hs i ≠ ⊥ ∧
      (∀ e : ℕ, 1 ≤ e → Nonempty (↥(Hs i) ≃* SL(2, GaloisField 2 e)) →
        2 ≤ e ∧ Q ⊓ Hs i = Hs i ∧ IsSimpleGroup ↥(Q ⊓ Hs i)) ∧
      (∀ k : ℕ, Nonempty (↥(Hs i) ≃* Equiv.Perm (Fin (2 ^ k + 1))) →
        2 ≤ k ∧ Nonempty (↥(Q ⊓ Hs i) ≃* alternatingGroup (Fin (2 ^ k + 1))) ∧ IsSimpleGroup ↥(Q ⊓ Hs i)) := by
  set P : Subgroup X := projImage hdir hQJ i with hPdef
  set D : Subgroup X := Q ⊓ Hs i with hDdef
  have hPH : P ≤ Hs i := projImage_le hdir hQJ i
  have hPp : ⁅P, P⁆ = P := projImage_perfect hdir hQJ i hQp
  have hDP : D ≤ P := inf_le_projImage hdir hQJ i
  have hcomm : ⁅Q, Hs i⁆ = ⁅P, Hs i⁆ := commutator_projImage hdir hQJ i
  have hHP : Hs i ≤ normalizer (P : Set X) := le_normalizer_projImage hdir hQJ i hJQ
  have hHQ : Hs i ≤ normalizer (Q : Set X) := (le_of_dirProd hdir i).trans hJQ
  have hQHi : Q ≤ normalizer (Hs i : Set X) := hQJ.trans (le_normalizer_of_dirProd hdir i)
  have hcD : ⁅Q, Hs i⁆ ≤ D := by
    refine Subgroup.commutator_le.mpr fun q hq x hx => ⟨?_, ?_⟩
    · rw [commutatorElement_def, show q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) by group]
      exact Q.mul_mem hq ((mem_normalizer_iff.1 (hHQ hx) q⁻¹).1 (Q.inv_mem hq))
    · rw [commutatorElement_def]
      exact (Hs i).mul_mem ((mem_normalizer_iff.1 (hQHi hq) x).1 hx) ((Hs i).inv_mem hx)
  have hPne : P ≠ ⊥ := fun h => hne (by rw [hcomm, h, Subgroup.commutator_bot_left])
  have hDne : D ≠ ⊥ := fun h => hne (le_bot_iff.1 (h ▸ hcD))
  have hPD : P ≤ D := by
    calc P = ⁅P, P⁆ := hPp.symm
      _ ≤ ⁅P, Hs i⁆ := Subgroup.commutator_mono le_rfl hPH
      _ = ⁅Q, Hs i⁆ := hcomm.symm
      _ ≤ D := hcD
  have hPeq : P = D := le_antisymm hPD hDP
  refine ⟨hPeq, hPeq ▸ hPp, hDne, ?_⟩
  have hD2 : ∀ {Y : Type} [Group Y], (Nat.card Y ∣ 6) → Nonempty (↥(Hs i) ≃* Y) → False := by
    intro Y _ h6 ⟨ψ⟩
    apply hPne
    refine eq_bot_of_perfect_of_card_dvd_six hPp (dvd_trans ?_ h6)
    rw [← Nat.card_congr ψ.toEquiv]
    exact Subgroup.card_dvd_of_le hPH
  refine ⟨fun e he1 ⟨ψ⟩ => ?_, fun k ⟨ψ⟩ => ?_⟩
  · rcases Nat.lt_or_ge e 2 with he | he
    · obtain rfl : e = 1 := by omega
      exact (hD2 (card_sl2_galoisField_one ▸ dvd_rfl) ⟨ψ⟩).elim
    · haveI : IsSimpleGroup ↥(Hs i) := (ψ.isSimpleGroup_congr).2 (isSimpleGroup_sl2_galoisField he)
      have hDH : D = Hs i := by
        rcases eq_bot_or_eq_of_isSimpleGroup (D := Hs i) inferInstance inf_le_right
          (fun x hx => mem_normalizer_inf' (hHQ hx) (Subgroup.le_normalizer hx)) with h | h
        · exact absurd h hDne
        · exact h
      refine ⟨he, hDH, ?_⟩
      rw [hDH]
      infer_instance
  · rcases Nat.lt_or_ge k 2 with hk | hk
    · exfalso
      refine hD2 (Y := Equiv.Perm (Fin (2 ^ k + 1))) ?_ ⟨ψ⟩
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      interval_cases k <;> decide
    ·
      set m : ℕ := 2 ^ k + 1 with hm
      have hm5 : 5 ≤ m := by
        have : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        omega
      haveI hsA : IsSimpleGroup (alternatingGroup (Fin m)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm5)
      set f' : ↥Q →* ↥(Hs i) := projHom hdir hQJ i with hf'
      have hPrange : P = f'.range.map (Hs i).subtype := by
        rw [hPdef, projImage, MonoidHom.range_comp]
      set P' : Subgroup (Equiv.Perm (Fin m)) := ((ψ : ↥(Hs i) →* Equiv.Perm (Fin m)).comp f').range with hP'def
      have hP'p : ⁅P', P'⁆ = P' := by
        haveI : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQp
        exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.range _)
      have hP'A : P' ≤ alternatingGroup (Fin m) := le_alternatingGroup_of_perfect hP'p
      have hP'ne : P' ≠ ⊥ := by
        intro h
        apply hPne
        rw [hPrange, eq_bot_iff]
        rintro _ ⟨y, ⟨q, rfl⟩, rfl⟩
        have hq : ψ (f' q) ∈ P' := ⟨q, rfl⟩
        rw [h, Subgroup.mem_bot] at hq
        have : f' q = 1 := by simpa using congrArg ψ.symm hq
        rw [this]
        exact Subgroup.one_mem _
      have hP'n : (⊤ : Subgroup (Equiv.Perm (Fin m))) ≤ normalizer (P' : Set (Equiv.Perm (Fin m))) := by
        refine le_normalizer_of_conj fun σ _ τ hτ => ?_
        obtain ⟨q, rfl⟩ := hτ
        obtain ⟨x, rfl⟩ := ψ.surjective σ
        have hxP : (x : X) * (f' q : X) * (x : X)⁻¹ ∈ P := by
          have := (mem_normalizer_iff.1 (hHP x.2) (f' q : X)).1 ⟨q, rfl⟩
          exact this
        obtain ⟨q', hq'⟩ := hxP
        refine ⟨q', ?_⟩
        have e : f' q' = x * f' q * x⁻¹ := Subtype.ext hq'
        change ψ (f' q') = ψ x * ψ (f' q) * (ψ x)⁻¹
        rw [e, map_mul, map_mul, map_inv]
      have hP'eq : P' = alternatingGroup (Fin m) := by
        rcases eq_bot_or_eq_of_isSimpleGroup hsA hP'A
          (fun x _ => hP'n (Subgroup.mem_top x)) with h | h
        · exact absurd h hP'ne
        · exact h
      have eD : ↥D ≃* alternatingGroup (Fin m) :=
        (MulEquiv.subgroupCongr (hPeq.symm.trans hPrange)).trans
          (((Subgroup.equivMapOfInjective f'.range (Hs i).subtype (Hs i).subtype_injective).symm.trans
            (ψ.subgroupMap f'.range)).trans
            (MulEquiv.subgroupCongr (by rw [← MonoidHom.range_comp]; exact hP'eq)))
      exact ⟨hk, ⟨eD⟩, (eD.isSimpleGroup_congr).2 hsA⟩

theorem uc22p22sf_structure (hHJ : Hst ≤ normalizer (J : Set X)) (hprod : (J : Set X) * (T : Set X) = Hst)
    (hT2 : IsPGroup 2 T) (hdir : CFSG.ASVolI.ChB.IsIntDirProd J Hs)
    (htrans : ∀ i j, ∃ t ∈ T, (Hs i).map (MulAut.conj t).toMonoidHom = Hs j)
    (hfac : ∀ i, (∃ e : ℕ, 1 ≤ e ∧ Nonempty (↥(Hs i) ≃* SL(2, GaloisField 2 e))) ∨
      ∃ k : ℕ, Nonempty (↥(Hs i) ≃* Equiv.Perm (Fin (2 ^ k + 1))))
    (hQH : Q ≤ Hst) (hHQ : Hst ≤ normalizer (Q : Set X)) (hQp : ⁅Q, Q⁆ = Q) (hQ : Q ≠ ⊥) :
    Q ≤ J ∧ Q = ⨆ i, Q ⊓ Hs i ∧ ∀ i, ⁅Q ⊓ Hs i, Q ⊓ Hs i⁆ = Q ⊓ Hs i ∧ Q ⊓ Hs i ≠ ⊥ ∧
      IsSimpleGroup ↥(Q ⊓ Hs i) ∧
      (∀ e : ℕ, 1 ≤ e → Nonempty (↥(Hs i) ≃* SL(2, GaloisField 2 e)) → 2 ≤ e ∧ Q ⊓ Hs i = Hs i) ∧
      (∀ k : ℕ, Nonempty (↥(Hs i) ≃* Equiv.Perm (Fin (2 ^ k + 1))) →
        2 ≤ k ∧ Nonempty (↥(Q ⊓ Hs i) ≃* alternatingGroup (Fin (2 ^ k + 1)))) := by
  have hTH : T ≤ Hst := fun t ht => by
    show t ∈ (Hst : Set X)
    rw [← hprod]
    exact Set.mem_mul.mpr ⟨1, J.one_mem, t, ht, one_mul t⟩
  have hJH : J ≤ Hst := fun j hj => by
    show j ∈ (Hst : Set X)
    rw [← hprod]
    exact Set.mem_mul.mpr ⟨j, hj, 1, T.one_mem, mul_one j⟩
  have hQJ : Q ≤ J := uc22p22sf_le_J hHJ hprod hT2 hQH hQp
  have hJQ : J ≤ normalizer (Q : Set X) := hJH.trans hHQ
  have hF := fun i => uc22p22sf_factor hdir hQJ hJQ hQp i
    (uc22p22sf_commutator_ne_bot hTH hHQ hQJ hdir htrans hQp hQ i)
  refine ⟨hQJ, le_antisymm ?_ (iSup_le fun i => inf_le_left), fun i => ?_⟩
  · intro q hq
    refine mem_iSup_of_dirProj hdir ⟨q, hQJ hq⟩ fun i => ?_
    rw [← (hF i).1]
    exact ⟨⟨q, hq⟩, rfl⟩
  obtain ⟨-, hp, hne, hsl, hsym⟩ := hF i
  have hsimp : IsSimpleGroup ↥(Q ⊓ Hs i) := by
    rcases hfac i with ⟨e, he1, hψ⟩ | ⟨k, hψ⟩
    · exact (hsl e he1 hψ).2.2
    · exact (hsym k hψ).2.2
  exact ⟨hp, hne, hsimp, fun e he1 hψ => ⟨(hsl e he1 hψ).1, (hsl e he1 hψ).2.1⟩,
    fun k hψ => ⟨(hsym k hψ).1, (hsym k hψ).2.1⟩⟩

theorem uc22p22sf_eq_factor (hdir : CFSG.ASVolI.ChB.IsIntDirProd J Hs) (hQJ : Q ≤ J)
    (hQeq : Q = ⨆ i, Q ⊓ Hs i)
    (hD : ∀ i, ⁅Q ⊓ Hs i, Q ⊓ Hs i⁆ = Q ⊓ Hs i ∧ Q ⊓ Hs i ≠ ⊥ ∧ IsSimpleGroup ↥(Q ⊓ Hs i))
    {L : Subgroup X} (hLQ : L ≤ Q) (hQL : Q ≤ normalizer (L : Set X))
    (hLqs : ∀ N : Subgroup X, N ≤ L → L ≤ normalizer (N : Set X) → N = L ∨ L ≤ centralizer (N : Set X))
    (hLp : ⁅L, L⁆ = L) (hL : L ≠ ⊥) : ∃ i, L = Q ⊓ Hs i := by
  have hQD : ∀ i, Q ≤ normalizer ((Q ⊓ Hs i : Subgroup X) : Set X) := fun i x hx =>
    mem_normalizer_inf' (Subgroup.le_normalizer hx) (le_normalizer_of_dirProd hdir i (hQJ hx))
  by_cases hex : ∃ i, Q ⊓ Hs i ≤ L
  · obtain ⟨i, hi⟩ := hex
    rcases hLqs _ hi (hLQ.trans (hQD i)) with h | h
    · exact ⟨i, h.symm⟩
    · exfalso
      apply (hD i).2.1
      rw [← (hD i).1]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hi.trans h)
  · push Not at hex
    exfalso
    apply hL
    have hcomm : ∀ i, ⁅Q ⊓ Hs i, L⁆ = ⊥ := by
      intro i
      have hDQ : Q ⊓ Hs i ≤ Q := inf_le_left
      have hmeet : L ⊓ (Q ⊓ Hs i) = ⊥ := by
        rcases eq_bot_or_eq_of_isSimpleGroup (hD i).2.2 inf_le_right
          (fun x hx => mem_normalizer_inf' (hQL (hDQ hx)) (Subgroup.le_normalizer hx)) with h | h
        · exact h
        · exact absurd (h ▸ inf_le_left) (hex i)
      refine le_bot_iff.1 (hmeet ▸ le_inf ?_ ?_)
      · refine Subgroup.commutator_le.mpr fun d hd l hl => ?_
        rw [commutatorElement_def]
        exact L.mul_mem ((mem_normalizer_iff.1 (hQL (hDQ hd)) l).1 hl) (L.inv_mem hl)
      · refine Subgroup.commutator_le.mpr fun d hd l hl => ?_
        rw [commutatorElement_def, show d * l * d⁻¹ * l⁻¹ = d * (l * d⁻¹ * l⁻¹) by group]
        exact (Q ⊓ Hs i).mul_mem hd
          ((mem_normalizer_iff.1 (hQD i (hLQ hl)) d⁻¹).1 ((Q ⊓ Hs i).inv_mem hd))
    have hQC : Q ≤ centralizer (L : Set X) := by
      rw [hQeq]
      exact iSup_le fun i => Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i)
    rw [← hLp]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hLQ.trans hQC)

end Structure

end CFSG.LocalAnalysis.UniquenessCase.UC22
