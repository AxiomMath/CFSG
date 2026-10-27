module

public import CFSG.Sporadic.HNOddCore.SixC
public import Certificates.Certificate2084
public import Certificates.Certificate2087
public import Certificates.Certificate2091
public import Certificates.Certificate2092
public import Certificates.Certificate2094
public import Certificates.Certificate2096
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Certificates.Native Equiv

@[expose] def hPerm (i : ℕ) : Perm (Fin 1100) := Monster.B.Co2.permOfArr 1100 hArr[i]!

theorem h_facts
    {i : ℕ} (hi : i < hArr.size) :
    PRep 1100 hArr[i]! (hPerm i) ∧ hPerm i ∈ Dsub ∧ hPerm i 0 = 0 := by
  obtain ⟨h0, hinv, hsift⟩ := six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi
  have hp := (prep_permOfArr hinv).1
  rw [← permOfArr_eq_of_prep hp] at hp
  refine ⟨hp, (mem_Dsub_iff hp).1 hsift, Fin.ext ?_⟩
  rw [hPerm, ← hp 0, Fin.val_zero]
  exact h0

abbrev Hsub : Subgroup (Perm (Fin 1100)) :=
  Subgroup.closure (Set.range fun i : Fin hArr.size => hPerm i)

theorem Hsub_le :
    Hsub ≤ Dsub := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact (h_facts i.2).2.1

theorem Hsub_fix
    {h : Perm (Fin 1100)} (hh : h ∈ Hsub) : h 0 = 0 := by
  have hgen : ∀ i : Fin hArr.size,
      hPerm i ∈ MulAction.stabilizer (Perm (Fin 1100)) (0 : Fin 1100) := fun i => by
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact (h_facts i.2).2.2
  have hle : Hsub ≤ MulAction.stabilizer (Perm (Fin 1100)) (0 : Fin 1100) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact SetLike.mem_coe.2 (hgen i)
  have := hle hh
  rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at this

theorem ls_cert {i : ℕ} (hi : i < 5) :
    orbitCertOK 1100 hArr lsArr[i]! (posArr 1100 lsArr[i]!)
      (orbitRecs hArr lsArr[i]! (posArr 1100 lsArr[i]!)).1
      (orbitRecs hArr lsArr[i]! (posArr 1100 lsArr[i]!)).2 = true :=
  six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi

theorem ls_orbit
    {i : ℕ} (hi : i < 5) :
    MulAction.orbit Hsub ((ptList_of_pointsOK (orbitCertOK_spec (ls_cert hi)).2.1).pt
      ⟨0, (orbitCertOK_spec (ls_cert hi)).1⟩) =
      Set.range (ptList_of_pointsOK (orbitCertOK_spec (ls_cert hi)).2.1).pt :=
  orbit_eq_of_orbitCertOK (fun _ hs => (h_facts hs).1) (ls_cert hi)

@[expose] def labD (p : Fin 1100) : Fin 5 :=
  ⟨labArr[(p : ℕ)]!, (six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p p.2).1⟩

theorem labD_iff {i : ℕ} (hi : i < 5) (p : Fin 1100) :
    (labD p : ℕ) = i ↔
      p ∈ Set.range (ptList_of_pointsOK (orbitCertOK_spec (ls_cert hi)).2.1).pt := by
  constructor
  · intro h
    have hc := (six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p p.2).2
    have h' : labArr[(p : ℕ)]! = i := h
    rw [h', Array.contains_iff_mem, Array.mem_iff_getElem] at hc
    obtain ⟨k, hk, he⟩ := hc
    refine ⟨⟨k, hk⟩, Fin.ext ?_⟩
    rw [PtList.pt_val, getElem!_pos _ k hk]
    exact he
  · rintro ⟨k, rfl⟩
    show labArr[(lsArr[i]!)[(k : ℕ)]!]! = i
    exact six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi k k.2

theorem ls_sizes
    {i : ℕ} (hi : i < 5) : (lsArr[i]!).size = [1, 336, 105, 630, 28][i]! := by
  have h1 := six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 := six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hs : (lsArr.map Array.size)[i]! = (lsArr[i]!).size := by
    rw [getElem!_pos _ i (by simp [h1, hi]), Array.getElem_map,
      getElem!_pos lsArr i (by rw [h1]; exact hi)]
  rw [← hs, h2]
  interval_cases i <;> rfl

theorem card_labD (i : Fin 5) :
    Nat.card {p : Fin 1100 // labD p = i} = [1, 336, 105, 630, 28][(i : ℕ)]! := by
  rw [← ls_sizes i.2]
  have e : {p : Fin 1100 // labD p = i} ≃
      Set.range (ptList_of_pointsOK (orbitCertOK_spec (ls_cert i.2)).2.1).pt :=
    Equiv.subtypeEquivRight fun p => by
      rw [← labD_iff i.2 p, Fin.ext_iff]
  rw [Nat.card_congr e, Nat.card_coe_set_eq,
    Set.ncard_range_of_injective (PtList.pt_injective _), Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem labD_zero : labD 0 = 0 := by
  apply Fin.ext
  show (labD 0 : ℕ) = 0
  rw [labD_iff (i := 0) (by norm_num)]
  refine ⟨⟨0, (orbitCertOK_spec (ls_cert (i := 0) (by norm_num))).1⟩, Fin.ext ?_⟩
  rw [PtList.pt_val]
  exact six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

@[expose] def subSizesD : Fin 5 → ℕ := ![1, 336, 105, 630, 28]

theorem subSizesD_blocks : ∀ S : Finset (Fin 5), (0 : Fin 5) ∈ S →
    (∑ i ∈ S, subSizesD i) ∣ 1100 → S = {0} ∨ S = Finset.univ := by
  decide

instance Dsub_pretransitive :
    MulAction.IsPretransitive Dsub (Fin 1100) where
  exists_smul_eq p q := by
    obtain ⟨g, hg, he⟩ := Dsub_transitive p q
    exact ⟨⟨g, hg⟩, he⟩

abbrev HD : Subgroup Dsub := Hsub.subgroupOf Dsub

theorem orbit_rel
    {i : ℕ} (hi : i < 5) {p q : Fin 1100}
    (hp : p ∈ Set.range (ptList_of_pointsOK (orbitCertOK_spec (ls_cert hi)).2.1).pt)
    (hq : q ∈ Set.range (ptList_of_pointsOK (orbitCertOK_spec (ls_cert hi)).2.1).pt) :
    ∃ h ∈ HD, h • p = q := by
  rw [← ls_orbit hi] at hp hq
  obtain ⟨g1, hg1⟩ := hp
  obtain ⟨g2, hg2⟩ := hq
  simp only at hg1 hg2
  refine ⟨⟨(g2 * g1⁻¹ : Hsub), Hsub_le (g2 * g1⁻¹ : Hsub).2⟩, (g2 * g1⁻¹ : Hsub).2, ?_⟩
  have e : (g2 * g1⁻¹) • p = q := by
    rw [mul_smul, ← hg1, inv_smul_smul, hg2]
  exact e

theorem Dsub_preprimitive :
    MulAction.IsPreprimitive Dsub (Fin 1100) := by
  refine CFSG.Sporadic.Th.isPreprimitive_of_suborbit_labels_of_finite (0 : Fin 1100) HD
    (fun h hh => Hsub_fix hh) labD ?_ ?_ ?_
  · intro h hh p
    apply Fin.ext
    have hi := (labD p).2
    rw [labD_iff hi]
    have hp : p ∈ Set.range (ptList_of_pointsOK (orbitCertOK_spec (ls_cert hi)).2.1).pt :=
      (labD_iff hi p).1 rfl
    rw [← ls_orbit hi] at hp ⊢
    obtain ⟨g, hg⟩ := hp
    simp only at hg
    refine ⟨⟨(h : Perm (Fin 1100)), hh⟩ * g, ?_⟩
    show (⟨(h : Perm (Fin 1100)), hh⟩ * g : Hsub) • _ = h • p
    rw [mul_smul, hg]
    rfl
  · intro p q hpq
    have hp := (labD_iff (labD p).2 p).1 rfl
    have hq : q ∈ Set.range (ptList_of_pointsOK (orbitCertOK_spec (ls_cert (labD p).2)).2.1).pt :=
      (labD_iff (labD p).2 q).1 (by rw [hpq])
    exact orbit_rel (labD p).2 hp hq
  · intro S hS hdvd
    rw [labD_zero] at hS ⊢
    have hsum : (∑ i ∈ S, Nat.card {p : Fin 1100 // labD p = i}) = ∑ i ∈ S, subSizesD i :=
      Finset.sum_congr rfl fun i _ => by rw [card_labD]; fin_cases i <;> rfl
    rw [hsum, Nat.card_eq_fintype_card (α := Fin 1100), Fintype.card_fin] at hdvd
    exact subSizesD_blocks S hS hdvd

instance Dsub_faithful : FaithfulSMul Dsub (Fin 1100) := ⟨fun h => Subtype.ext (Equiv.ext h)⟩

theorem card_stab_D :
    Nat.card (MulAction.stabilizer Dsub (0 : Fin 1100)) = 40320 := by
  have h := (MulAction.stabilizer Dsub (0 : Fin 1100)).card_mul_index
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ] at h
  have h1 : (Set.univ : Set (Fin 1100)).ncard = 1100 := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [h1, card_Dsub] at h
  generalize Nat.card (MulAction.stabilizer Dsub (0 : Fin 1100)) = x at h ⊢
  omega

theorem closure_aD_bD :
    Subgroup.closure ({⟨aD, Subgroup.subset_closure (Set.mem_insert _ _)⟩,
      ⟨bD, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩} : Set Dsub) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage (k := ({aD, bD} : Set (Perm (Fin 1100))))
  convert h using 2
  ext ⟨g, hg⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]

theorem Dsub_simple :
    IsSimpleGroup Dsub := by
  have := Dsub_preprimitive
  refine CFSG.GroupActions.isSimpleGroup_of_preprimitive_of_coprime_generator_orders
    (Ω := Fin 1100) (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) _ _
    closure_aD_bD 0 ?_ ?_
  · rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, orderOf_aD, orderOf_bD]
    norm_num
  · rw [card_stab_D, ← Subgroup.orderOf_coe, Subgroup.coe_mul, orderOf_abD]
    norm_num

theorem conj_D
    {g : ℕ} (hg : g < 12) : ∀ y ∈ Dsub, om0Perm g * y * (om0Perm g)⁻¹ ∈ Dsub := by
  have hinv := prep_inv_of_pisInv (prep_om0 hg) (six_parts.2.1 g hg)
  obtain ⟨ha, hb⟩ := six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 g hg
  have hle : Dsub ≤ Dsub.comap (MulAut.conj (om0Perm g)).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        mul_assoc]
      exact (mem_Dsub_iff (prep_pcomp (prep_om0 hg) (prep_pcomp prep_aD hinv))).1 ha
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        mul_assoc]
      exact (mem_Dsub_iff (prep_pcomp (prep_om0 hg) (prep_pcomp prep_bD hinv))).1 hb
  intro y hy
  have := hle hy
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem range_le_normalizer_D :
    phi6.range ≤ Subgroup.normalizer (Dsub : Set (Perm (Fin 1100))) := by
  rw [range_eq_closure phi6 closure_g6C, Subgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  have e : phi6 (g6C s) = om0Perm s := by rw [om0Perm, dite_eq_left s.2]
  show phi6 (g6C s) ∈ _
  rw [SetLike.mem_coe, e]
  exact mem_normalizer_of_conj fun y hy => conj_D s.2 y hy

theorem om0Perm_five_not_mem :
    om0Perm 5 ∉ Dsub := fun h => by
  have := (mem_Dsub_iff (prep_om0 (s := 5) (by norm_num))).2 h
  rw [six_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2] at this
  exact Bool.false_ne_true this

abbrev Dr :
    Subgroup phi6.range := Dsub.subgroupOf phi6.range

theorem card_Dr :
    Nat.card Dr = 44352000 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Dsub_le_range).toEquiv, card_Dsub]

theorem Dr_ne_top :
    Dr ≠ ⊤ := fun h => by
  have : (⟨om0Perm 5, om0Perm_mem (by norm_num)⟩ : phi6.range) ∈ Dr := h ▸ Subgroup.mem_top _
  exact om0Perm_five_not_mem this

theorem index_Dr :
    Dr.index = 2 := by
  have h := Dr.card_mul_index
  rw [card_Dr] at h
  have hle := card_phi6_range_le
  have h1 : Dr.index ≠ 1 := fun e => Dr_ne_top (Subgroup.index_eq_one.1 e)
  have h0 : Dr.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : Dr.index ≤ 2 := by
    by_contra hc
    push Not at hc
    have : 44352000 * 3 ≤ 44352000 * Dr.index := Nat.mul_le_mul_left _ hc
    omega
  omega

theorem card_phi6_range :
    Nat.card phi6.range = 88704000 := by
  rw [← Dr.card_mul_index, card_Dr, index_Dr]

theorem card_ker_phi6 :
    Nat.card phi6.ker = 2 := by
  have h := phi6.ker.card_mul_index
  rw [Subgroup.index_ker, card_phi6_range, card_CJ_t6] at h
  generalize Nat.card phi6.ker = x at h ⊢
  omega

theorem Dr_simple :
    IsSimpleGroup Dr :=
  @MulEquiv.isSimpleGroup Dr _ Dsub _ Dsub_simple (Subgroup.subgroupOfEquivOfLe Dsub_le_range)

theorem Dr_noncomm :
    ∃ a b : Dr, a * b ≠ b * a := by
  have key : ∀ (K H : Subgroup (Perm (Fin 1100))) (a b : Perm (Fin 1100)), a ∈ K → b ∈ K →
      a ∈ H → b ∈ H → a * b ≠ b * a → ∃ x y : H.subgroupOf K, x * y ≠ y * x := by
    intro K H a b haK hbK haH hbH hab
    refine ⟨⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.2 haH⟩, ⟨⟨b, hbK⟩, Subgroup.mem_subgroupOf.2 hbH⟩,
      fun h => hab ?_⟩
    have := congrArg (fun x : H.subgroupOf K => ((x : K) : Perm (Fin 1100))) h
    simpa using this
  exact key _ _ aD bD aD_mem bD_mem (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) abD_ne_ba

end CFSG.Sporadic.HNOddCore
