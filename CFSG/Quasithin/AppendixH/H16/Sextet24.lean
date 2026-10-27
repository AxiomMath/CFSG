module

public import CFSG.Quasithin.AppendixH.Common.Sextet
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Quasithin.Background.HLUBlocks
public import CFSG.Quasithin.Background.HLUCode24Gen

public section

open scoped Pointwise

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.LU
  CFSG.Monster.Code CFSG.Open

@[expose] def stdSextet : Finset (Finset (Fin 24)) :=
  Finset.univ.image fun i : Fin 6 => Finset.univ.filter fun x : Fin 24 => lab6 x = i

private def cls (i : Fin 6) : Finset (Fin 24) :=
  Finset.univ.filter fun x : Fin 24 => lab6 x = i

private theorem stdSextet_eq_image : stdSextet = Finset.univ.image cls := rfl

private theorem cls_card (i : Fin 6) : (cls i).card = 4 := by
  revert i; decide

private theorem cls_disj : ∀ i j : Fin 6, i ≠ j → Disjoint (cls i) (cls j) := by
  decide

private theorem cls_zero : cls (0 : Fin 6) = ({0, 1, 12, 21} : Finset (Fin 24)) := by
  decide

private theorem cls_mem_stdSextet (i : Fin 6) : cls i ∈ stdSextet := by
  rw [stdSextet_eq_image, Finset.mem_image]
  exact ⟨i, Finset.mem_univ _, rfl⟩

private theorem synd_cls_union : ∀ i j : Fin 6, i ≠ j →
    CFSG.Quasithin.H.Mathieu.synd
      (fun k : Fin 24 => if k ∈ cls i ∪ cls j then (1 : ZMod 2) else 0) = 0 := by
  decide +kernel

private theorem isOctad_cls (i j : Fin 6) (hij : i ≠ j) : IsOctad (cls i ∪ cls j) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.card_union_of_disjoint (cls_disj i j hij), cls_card i, cls_card j]
  · rw [CFSG.Quasithin.H.Mathieu.mem_golayC_iff,
      ← CFSG.Quasithin.H.Mathieu.synd_eq_zero_iff]
    exact synd_cls_union i j hij

private theorem isSextet_image_cls (f : Fin 6 → Finset (Fin 24))
    (hcard : (Finset.univ.image f).card = 6)
    (htet : ∀ i, (f i).card = 4)
    (hdisj : ∀ i j, i ≠ j → Disjoint (f i) (f j))
    (hcov : (Finset.univ.image f).biUnion id = Finset.univ)
    (hoct : ∀ i j, i ≠ j → IsOctad (f i ∪ f j)) :
    IsSextet (Finset.univ.image f) := by
  refine ⟨hcard, ?_, ?_, hcov, ?_⟩
  · intro B hB
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
    exact htet i
  · intro B hB B' hB' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hB'
    exact hdisj i j fun h => hne (by rw [h])
  · intro B hB B' hB' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hB'
    exact hoct i j fun h => hne (by rw [h])

theorem isSextet_stdSextet : IsSextet stdSextet := by
  rw [stdSextet_eq_image]
  exact isSextet_image_cls cls (by decide) cls_card cls_disj (by decide) isOctad_cls

private theorem smul_four_eq (g : S24) (a b c d : Fin 24)
    (ha : g 0 = a) (hb : g 1 = b) (hc : g 2 = c) (hd : g 3 = d) :
    g • ({0, 1, 2, 3} : Finset (Fin 24)) = {a, b, c, d} := by
  ext x
  rw [smul_finset_eq_map, Finset.mem_map_equiv]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · left; rw [← ha, ← h]; simp
    · right; left; rw [← hb, ← h]; simp
    · right; right; left; rw [← hc, ← h]; simp
    · right; right; right; rw [← hd, ← h]; simp
  · rintro (rfl | rfl | rfl | rfl)
    · left; rw [← ha]; simp
    · right; left; rw [← hb]; simp
    · right; right; left; rw [← hc]; simp
    · right; right; right; rw [← hd]; simp

private theorem exists_smul_cls_zero_eq
    (Y : Finset (Fin 24)) (hY : Y.card = 4) :
    ∃ τ ∈ M24g, τ • cls 0 = Y := by
  obtain ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz, hYeq⟩ := Finset.card_eq_four.mp hY
  obtain ⟨s, hs, hs0, hs1, hs2, hs3⟩ :=
    CFSG.Monster.B.TwoA.autPerm_maps_four u v w z huv huw huz hvw hvz hwz
  obtain ⟨p, hp, hp0, hp1, hp2, hp3⟩ :=
    CFSG.Monster.B.TwoA.autPerm_maps_four 0 1 12 21 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  refine ⟨s * p⁻¹, M24g.mul_mem hs (M24g.inv_mem hp), ?_⟩
  have hpB : p • ({0, 1, 2, 3} : Finset (Fin 24)) = cls 0 := by
    rw [cls_zero]
    exact smul_four_eq p 0 1 12 21 hp0 hp1 hp2 hp3
  have hq : p⁻¹ • cls 0 = ({0, 1, 2, 3} : Finset (Fin 24)) := by
    rw [← hpB]; simp
  have hsY : s • ({0, 1, 2, 3} : Finset (Fin 24)) = Y := by
    rw [hYeq]
    exact smul_four_eq s u v w z hs0 hs1 hs2 hs3
  rw [mul_smul, hq, hsY]

theorem exists_smul_stdSextet {S : Finset (Finset (Fin 24))}
    (hS : IsSextet S) : ∃ τ ∈ M24g, τ • stdSextet = S := by
  have hSkeep : IsSextet S := hS
  obtain ⟨hcard, htet, hdisj, hcov, hoct⟩ := hS
  have hSne : S.Nonempty := Finset.card_pos.1 (by rw [hcard]; norm_num)
  obtain ⟨B, hB⟩ := hSne
  have hB4 : B.card = 4 := htet B hB
  obtain ⟨τ, hτ, hτB⟩ := exists_smul_cls_zero_eq B hB4
  refine ⟨τ, hτ, ?_⟩
  have hBmem : B ∈ τ • stdSextet := by
    rw [← hτB]
    exact Finset.mem_smul_finset.2 ⟨cls 0, cls_mem_stdSextet 0, rfl⟩
  exact CFSG.ASVolI.AppH.sextet_eq_of_mem
    (CFSG.ASVolI.AppH.isSextet_smul hτ isSextet_stdSextet) hSkeep hBmem hB

private theorem smul_cls {σ : S24} (hσ : σ ∈ blockP lab6) (i : Fin 6) :
    σ • cls i = cls (lab6 (σ (rep6 i))) := by
  ext z
  rw [smul_finset_eq_map, Finset.mem_map_equiv]
  simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa [lab6_rep6 i] using (hσ (σ.symm z) (rep6 i)).symm

private theorem common_mem_iff (x y : Fin 24) :
    (∃ T ∈ stdSextet, x ∈ T ∧ y ∈ T) ↔ lab6 x = lab6 y := by
  constructor
  · rintro ⟨T, hT, hxT, hyT⟩
    rw [stdSextet_eq_image, Finset.mem_image] at hT
    obtain ⟨i, -, rfl⟩ := hT
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hxT hyT
    rw [hxT, hyT]
  · intro h
    refine ⟨cls (lab6 x), cls_mem_stdSextet _, ?_, ?_⟩
    · simp [cls]
    · simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.symm

theorem smul_stdSextet_iff (σ : S24) : σ • stdSextet = stdSextet ↔ σ ∈ blockP lab6 := by
  constructor
  · intro h x y
    rw [← common_mem_iff (σ x) (σ y), ← common_mem_iff x y]
    constructor
    · rintro ⟨T, hT, hxT, hyT⟩
      rw [← h] at hT
      obtain ⟨T', hT', rfl⟩ := Finset.mem_smul_finset.1 hT
      refine ⟨T', hT', ?_, ?_⟩
      · simpa [smul_finset_eq_map, Finset.mem_map_equiv] using hxT
      · simpa [smul_finset_eq_map, Finset.mem_map_equiv] using hyT
    · rintro ⟨T', hT', hxT', hyT'⟩
      refine ⟨σ • T', ?_, ?_, ?_⟩
      · rw [← h]
        exact Finset.mem_smul_finset.2 ⟨T', hT', rfl⟩
      · exact Finset.mem_smul_finset.2 ⟨x, hxT', by simp [Equiv.Perm.smul_def]⟩
      · exact Finset.mem_smul_finset.2 ⟨y, hyT', by simp [Equiv.Perm.smul_def]⟩
  · intro hσ
    have hsub : σ • stdSextet ⊆ stdSextet := by
      intro X hX
      rw [Finset.mem_smul_finset] at hX
      obtain ⟨T, hT, rfl⟩ := hX
      rw [stdSextet_eq_image, Finset.mem_image] at hT ⊢
      obtain ⟨i, -, rfl⟩ := hT
      exact ⟨lab6 (σ (rep6 i)), Finset.mem_univ _, (smul_cls hσ i).symm⟩
    have hcard : (σ • stdSextet).card = stdSextet.card := Finset.card_smul_finset σ stdSextet
    exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

private def tetradsThrough0 : Finset (Finset (Fin 24)) :=
  ((Finset.univ.erase (0 : Fin 24)).powersetCard 3).image (insert 0)

private theorem card_of_mem_tetradsThrough0 {Y : Finset (Fin 24)}
    (hY : Y ∈ tetradsThrough0) : Y.card = 4 := by
  rw [tetradsThrough0, Finset.mem_image] at hY
  obtain ⟨Z, hZ, rfl⟩ := hY
  have h0Z : (0 : Fin 24) ∉ Z := by
    intro h
    exact (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hZ).1 h)).1 rfl
  rw [Finset.card_insert_of_notMem h0Z, (Finset.mem_powersetCard.1 hZ).2]

private theorem zero_mem_tetradsThrough0 {Y : Finset (Fin 24)}
    (hY : Y ∈ tetradsThrough0) : (0 : Fin 24) ∈ Y := by
  rw [tetradsThrough0, Finset.mem_image] at hY
  obtain ⟨Z, hZ, rfl⟩ := hY
  exact Finset.mem_insert_self _ _

private theorem card_tetradsThrough0 : tetradsThrough0.card = 1771 := by
  have hinj : Set.InjOn (insert (0 : Fin 24))
      ((Finset.univ.erase (0 : Fin 24)).powersetCard 3 : Set (Finset (Fin 24))) := by
    intro A hA B hB hAB
    have h0A : (0 : Fin 24) ∉ A := by
      intro h
      exact (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hA).1 h)).1 rfl
    have h0B : (0 : Fin 24) ∉ B := by
      intro h
      exact (Finset.mem_erase.1 ((Finset.mem_powersetCard.1 hB).1 h)).1 rfl
    calc A = (insert 0 A).erase 0 := (Finset.erase_insert h0A).symm
      _ = (insert 0 B).erase 0 := by rw [hAB]
      _ = B := Finset.erase_insert h0B
  rw [tetradsThrough0, Finset.card_image_of_injOn hinj, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin 24)), Finset.card_univ,
    Fintype.card_fin]
  decide

private noncomputable def sextetTau
    (Y : Finset (Fin 24)) : S24 :=
  if h : Y.card = 4 then Classical.choose (exists_smul_cls_zero_eq Y h) else 1

private theorem sextetTau_mem {Y : Finset (Fin 24)}
    (hY : Y.card = 4) : sextetTau Y ∈ M24g := by
  unfold sextetTau
  rw [dif_pos hY]
  exact (Classical.choose_spec (exists_smul_cls_zero_eq Y hY)).1

private theorem sextetTau_smul {Y : Finset (Fin 24)}
    (hY : Y.card = 4) : sextetTau Y • cls 0 = Y := by
  unfold sextetTau
  rw [dif_pos hY]
  exact (Classical.choose_spec (exists_smul_cls_zero_eq Y hY)).2

theorem card_MY_stdSextet_le :
    Nat.card ↥(MY M24g stdSextet) ≤ 138240 := by
  haveI : Fintype ↥M24g := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbit ↥M24g stdSextet) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer ↥M24g stdSextet) := Fintype.ofFinite _
  have hGcard : Fintype.card ↥M24g = 244823040 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_AutPerm
  have horbit : 1771 ≤ Fintype.card (MulAction.orbit ↥M24g stdSextet) := by
    let f : Finset (Fin 24) → Finset (Finset (Fin 24)) :=
      fun Y => sextetTau Y • stdSextet
    have hf_mem : ∀ Y ∈ (tetradsThrough0 : Set (Finset (Fin 24))),
        f Y ∈ MulAction.orbit ↥M24g stdSextet := by
      intro Y hY
      have hY4 : Y.card = 4 := card_of_mem_tetradsThrough0 hY
      exact ⟨⟨sextetTau Y, sextetTau_mem hY4⟩, rfl⟩
    have hf_inj : Set.InjOn f (tetradsThrough0 : Set (Finset (Fin 24))) := by
      intro Y hY Y' hY' heq
      have hY4 : Y.card = 4 := card_of_mem_tetradsThrough0 hY
      have hY'4 : Y'.card = 4 := card_of_mem_tetradsThrough0 hY'
      have hY0 : (0 : Fin 24) ∈ Y := zero_mem_tetradsThrough0 hY
      have hY'0 : (0 : Fin 24) ∈ Y' := zero_mem_tetradsThrough0 hY'
      have heq' : sextetTau Y • stdSextet = sextetTau Y' • stdSextet := heq
      have hYmem : Y ∈ sextetTau Y • stdSextet :=
        Finset.mem_smul_finset.2 ⟨cls 0, cls_mem_stdSextet 0, sextetTau_smul hY4⟩
      have hY'mem : Y' ∈ sextetTau Y • stdSextet := by
        rw [heq']
        exact Finset.mem_smul_finset.2 ⟨cls 0, cls_mem_stdSextet 0, sextetTau_smul hY'4⟩
      have hsext : IsSextet (sextetTau Y • stdSextet) :=
        CFSG.ASVolI.AppH.isSextet_smul (sextetTau_mem hY4) isSextet_stdSextet
      by_contra hne
      exact (Finset.disjoint_left.1 (hsext.2.2.1 Y hYmem Y' hY'mem hne)) hY0 hY'0
    have hle := Set.ncard_le_ncard_of_injOn (s := (tetradsThrough0 : Set (Finset (Fin 24))))
      (t := MulAction.orbit ↥M24g stdSextet) f hf_mem hf_inj
    rw [Set.ncard_coe_finset, card_tetradsThrough0] at hle
    rwa [Set.fintypeCard_eq_ncard]
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥M24g) stdSextet
  have hstab_le : Fintype.card (MulAction.stabilizer ↥M24g stdSextet) ≤ 138240 := by
    have h : 1771 * Fintype.card (MulAction.stabilizer ↥M24g stdSextet) ≤ 244823040 := by
      rw [← hGcard, ← hos]
      exact Nat.mul_le_mul_right _ horbit
    omega
  have hstab_eq : Fintype.card (MulAction.stabilizer ↥M24g stdSextet) =
      Nat.card ↥(MY M24g stdSextet) := by
    have heq : MulAction.stabilizer ↥M24g stdSextet =
        (MY M24g stdSextet).subgroupOf M24g := by
      ext g
      unfold MY
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        exact ⟨g.2, h⟩
      · intro h
        exact h.2
    rw [← Nat.card_eq_fintype_card, heq]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show MY M24g stdSextet ≤ M24g from inf_le_left)).toEquiv
  rw [← hstab_eq]
  exact hstab_le

end CFSG.ASVolI.H16
