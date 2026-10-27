module

public import CFSG.Quasithin.Background.E6EighteenHeRes
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He
public import Certificates.Certificate7200

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.HeldB
open CFSG.Sporadic.SmallOddCore CFSG.Quasithin.E6.HeInvPerfect
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

theorem perfect_of_isSimpleGroup_nonab {Y : Type*} [Group Y] {D : Subgroup Y}
    (hs : IsSimpleGroup ↥D) (hnab : ∃ a b : ↥D, a * b ≠ b * a) : ⁅D, D⁆ = D := by
  rcases hs.eq_bot_or_eq_top_of_normal (commutator ↥D) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hm : ⁅a, b⁆ ∈ commutator ↥D := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · rw [← Subgroup.map_subtype_commutator, h, Subgroup.map_top, Subgroup.range_subtype]

theorem exists_perfect_in_of_mulEquiv {S H : Type*} [Group S] [Group H] {F : Subgroup S}
    (ψ : H ≃* ↥F) {D : Subgroup H} (hD : ⁅D, D⁆ = D) {n : ℕ} (hn : n ∣ Nat.card D) :
    ∃ D' : Subgroup S, D' ≤ F ∧ ⁅D', D'⁆ = D' ∧ n ∣ Nat.card D' := by
  set f : H →* S := F.subtype.comp ψ.toMonoidHom with hf
  have hinj : Function.Injective f := F.subtype_injective.comp ψ.injective
  refine ⟨D.map f, ?_, ?_, ?_⟩
  · rintro _ ⟨d, -, rfl⟩
    exact (ψ d).2
  · rw [← Subgroup.map_commutator, hD]
  · rw [Subgroup.card_map_of_injective hinj]
    exact hn

theorem exists_perfect_heInnerGrp0 :
    ∃ D : Subgroup ↥heInnerGrp0, ⁅D, D⁆ = D ∧ 64 ∣ Nat.card D := by
  obtain ⟨⟨hs, hnab⟩, hcard, hle, -⟩ := heD_facts
  have hDp := perfect_of_isSimpleGroup_nonab hs hnab
  refine ⟨perfectCore ((genGroup 105 heDGens heDPerm).comap heRho0), perfectCore_perfect _, ?_⟩
  have hmap : (perfectCore ((genGroup 105 heDGens heDPerm).comap heRho0)).map heRho0 =
      genGroup 105 heDGens heDPerm := by
    rw [map_perfectCore, Subgroup.map_comap_eq, inf_eq_right.2 hle,
      perfectCore_eq_self_of_perfect hDp]
  have h1 := Subgroup.card_map_dvd (H := perfectCore ((genGroup 105 heDGens heDPerm).comap heRho0))
    heRho0
  rw [hmap, hcard] at h1
  exact (show (64 : ℕ) ∣ 20160 by norm_num).trans h1

theorem heX1Comm_check :
    enumOK 42 heX1CommGens heX1CommEnum = true ∧ heX1CommEnum.tabs.size = 10752 :=
  Certificates.certificate7200

@[expose] def heX1CommPerm (k : ℕ) : Equiv.Perm (Fin 42) :=
  ⁅heInnerSigmaP1 (if k = 0 then 2 else 3), heInnerSigmaP1 8⁆

theorem heXTabs_size : heXTabs.size = 9 := by simp [heXTabs]

theorem heX1CommGens_size : heX1CommGens.size = 2 := rfl

theorem tabRep_heX1CommGens :
    ∀ k < heX1CommGens.size, TabRep heX1CommGens[k]! (heX1CommPerm k) := by
  have hinv : invsOK 42 heXTabs heXInvs = true := by
    have h := he2_R.2.2
    simp only [normalOK, Bool.and_eq_true] at h
    exact h.1
  have hrep : ∀ j < 9, TabRep heXTabs[j]! (heInnerSigmaP1 j) := fun j hj =>
    tabRep_heXTabs j (by rw [heXTabs_size]; exact hj)
  have hrepi : ∀ j < 9, TabRep heXInvs[j]! (heInnerSigmaP1 j)⁻¹ := fun j hj =>
    invsOK_spec hinv (by rw [heXTabs_size]; exact hj) (hrep j hj)
  intro k hk
  rw [heX1CommGens_size] at hk
  interval_cases k
  · show TabRep (commTab 42 heXTabs[2]! heXTabs[8]! heXInvs[2]! heXInvs[8]!)
      ⁅heInnerSigmaP1 2, heInnerSigmaP1 8⁆
    exact TabRep.commTab (hrep 2 (by norm_num)) (hrep 8 (by norm_num)) (hrepi 2 (by norm_num))
      (hrepi 8 (by norm_num))
  · show TabRep (commTab 42 heXTabs[3]! heXTabs[8]! heXInvs[3]! heXInvs[8]!)
      ⁅heInnerSigmaP1 3, heInnerSigmaP1 8⁆
    exact TabRep.commTab (hrep 3 (by norm_num)) (hrep 8 (by norm_num)) (hrepi 3 (by norm_num))
      (hrepi 8 (by norm_num))

theorem card_genGroup_heXTabs :
    Nat.card (genGroup 42 heXTabs heInnerSigmaP1) = 10752 := by
  rw [heX_enumerates.card, Array.length_toList, he2_X.2.1]

theorem heX1_perfect :
    ⁅genGroup 42 heXTabs heInnerSigmaP1, genGroup 42 heXTabs heInnerSigmaP1⁆ =
      genGroup 42 heXTabs heInnerSigmaP1 := by
  set X := genGroup 42 heXTabs heInnerSigmaP1 with hX
  have henum : Enumerates (genGroup 42 heX1CommGens heX1CommPerm) heX1CommEnum.tabs.toList :=
    enumerates_closure (genGroup_hA tabRep_heX1CommGens) (genGroup_hgens tabRep_heX1CommGens)
      heX1Comm_check.1
  have hY : Nat.card (genGroup 42 heX1CommGens heX1CommPerm) = 10752 := by
    rw [henum.card, Array.length_toList, heX1Comm_check.2]
  have hmem : ∀ j < 9, heInnerSigmaP1 j ∈ X := fun j hj =>
    Subgroup.subset_closure ⟨j, by rw [heXTabs_size]; exact hj, rfl⟩
  have hYle : genGroup 42 heX1CommGens heX1CommPerm ≤ ⁅X, X⁆ := by
    rw [genGroup, Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    have ha : (if k = 0 then 2 else 3) < 9 := by split_ifs <;> norm_num
    exact Subgroup.commutator_mem_commutator (hmem _ ha) (hmem 8 (by norm_num))
  refine Subgroup.eq_of_le_of_card_ge (A3.commutator_self_le X) ?_
  rw [card_genGroup_heXTabs, ← hY]
  exact Subgroup.card_le_of_le hYle

theorem exists_perfect_heInnerGrp1 :
    ∃ D : Subgroup ↥heInnerGrp1, ⁅D, D⁆ = D ∧ 64 ∣ Nat.card D := by
  refine ⟨perfectCore (⊤ : Subgroup ↥heInnerGrp1), perfectCore_perfect _, ?_⟩
  have hmap : (perfectCore (⊤ : Subgroup ↥heInnerGrp1)).map heRho1 =
      genGroup 42 heXTabs heInnerSigmaP1 := by
    rw [map_perfectCore, Subgroup.map_top, heRho1_range,
      perfectCore_eq_self_of_perfect heX1_perfect]
  have h1 := Subgroup.card_map_dvd (H := perfectCore (⊤ : Subgroup ↥heInnerGrp1)) heRho1
  rw [hmap, card_genGroup_heXTabs] at h1
  exact (show (64 : ℕ) ∣ 10752 by norm_num).trans h1

theorem factHeInvPerfect_holds :
    FactHeInvPerfect := by
  intro S _ ⟨e⟩ x hx
  have hF : fixedSubgroup (MulAut.conj x) ≤ Subgroup.centralizer ({x} : Set S) := by
    intro y hy
    have hy' : x * y * x⁻¹ = y := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * x = x * y * x⁻¹ * x := by rw [hy']
      _ = x * y := by group
  rcases CFSG.SeitzReduction.SporadicRefine.he_inner_fixedSubgroup_cases e x hx with h0 | h1
  · obtain ⟨ψ⟩ := h0
    obtain ⟨D, hD, h64⟩ := exists_perfect_heInnerGrp0
    obtain ⟨D', hD'F, hD'p, hD'c⟩ := exists_perfect_in_of_mulEquiv ψ.symm hD h64
    exact ⟨D', hD'F.trans hF, hD'p, hD'c⟩
  · obtain ⟨ψ⟩ := h1
    obtain ⟨D, hD, h64⟩ := exists_perfect_heInnerGrp1
    obtain ⟨D', hD'F, hD'p, hD'c⟩ := exists_perfect_in_of_mulEquiv ψ.symm hD h64
    exact ⟨D', hD'F.trans hF, hD'p, hD'c⟩

end E6

end CFSG.Quasithin
