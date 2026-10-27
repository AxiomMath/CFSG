module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

theorem sl4_card_eq_card_mul_card_ker {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    Nat.card G = Nat.card H * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

@[expose] def sl4_iota {M : Type*} [Group M] (R K : Subgroup M) [R.Normal] (J : Subgroup (M ⧸ R))
    (hKJ : K.map (QuotientGroup.mk' R) = J) : ↥K →* ↥J :=
  MonoidHom.codRestrict ((QuotientGroup.mk' R).comp K.subtype) J (fun k => by
    rw [← hKJ]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' R) k.2)

theorem sl4_iota_val {M : Type*} [Group M] (R K : Subgroup M) [R.Normal] (J : Subgroup (M ⧸ R))
    (hKJ : K.map (QuotientGroup.mk' R) = J) (k : ↥K) :
    ((sl4_iota R K J hKJ k : ↥J) : M ⧸ R) = QuotientGroup.mk' R (k : M) := rfl

theorem sl4_iota_surj {M : Type*} [Group M] (R K : Subgroup M) [R.Normal] (J : Subgroup (M ⧸ R))
    (hKJ : K.map (QuotientGroup.mk' R) = J) :
    Function.Surjective (sl4_iota R K J hKJ) := by
  intro j
  have hj : ((j : ↥J) : M ⧸ R) ∈ K.map (QuotientGroup.mk' R) := by
    rw [hKJ]
    exact j.2
  obtain ⟨k, hk, hkj⟩ := Subgroup.mem_map.1 hj
  exact ⟨⟨k, hk⟩, Subtype.ext hkj⟩

theorem sl4_ker_map_le {M : Type*} [Group M] (R K : Subgroup M) [R.Normal] (J : Subgroup (M ⧸ R))
    (hKJ : K.map (QuotientGroup.mk' R) = J) :
    ((sl4_iota R K J hKJ).ker).map K.subtype ≤ R := by
  rintro x ⟨k, hk, rfl⟩
  have hk' : k ∈ (sl4_iota R K J hKJ).ker := hk
  rw [MonoidHom.mem_ker] at hk'
  have h1 : ((sl4_iota R K J hKJ k : ↥J) : M ⧸ R) = 1 :=
    congrArg (fun x : ↥J => (x : M ⧸ R)) hk'
  have h2 : ((k : M) : M ⧸ R) = 1 := (sl4_iota_val R K J hKJ k).symm.trans h1
  exact (QuotientGroup.eq_one_iff (k : M)).1 h2

theorem sl4_card_ker_dvd {M : Type*} [Group M] (R K : Subgroup M) [R.Normal]
    (J : Subgroup (M ⧸ R)) (hKJ : K.map (QuotientGroup.mk' R) = J) :
    Nat.card (sl4_iota R K J hKJ).ker ∣ Nat.card R := by
  rw [← Subgroup.card_subtype K (sl4_iota R K J hKJ).ker]
  exact Subgroup.card_dvd_of_le (sl4_ker_map_le R K J hKJ)

theorem sl4_card_ker_comp {G H : Type*} [Group G] [Group H] [Finite H]
    (ι : G →* H) (hι : Function.Surjective ι) :
    Nat.card ((QuotientGroup.mk' (Subgroup.center H)).comp ι).ker =
      Nat.card (Subgroup.center H) * Nat.card ι.ker := by
  have hπ : Function.Surjective ((QuotientGroup.mk' (Subgroup.center H)).comp ι) :=
    (QuotientGroup.mk'_surjective _).comp hι
  have e1 := sl4_card_eq_card_mul_card_ker ((QuotientGroup.mk' (Subgroup.center H)).comp ι) hπ
  have e2 := sl4_card_eq_card_mul_card_ker ι hι
  have e3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H)
  have hpos : 0 < Nat.card (H ⧸ Subgroup.center H) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← e1, e2, e3, mul_assoc]

theorem exists_surjection_coprime {M : Type*} [Group M] [Finite M] (R K : Subgroup M) [R.Normal]
    (J : Subgroup (M ⧸ R)) (hKJ : K.map (QuotientGroup.mk' R) = J) (m : ℕ)
    (hR : Nat.Coprime (Nat.card R) m) (hZ : Nat.Coprime (Nat.card (Subgroup.center J)) m) :
    ∃ π : ↥K →* ↥J ⧸ Subgroup.center ↥J, Function.Surjective π ∧ Nat.Coprime (Nat.card π.ker) m := by
  refine ⟨(QuotientGroup.mk' (Subgroup.center ↥J)).comp (sl4_iota R K J hKJ), ?_, ?_⟩
  · exact (QuotientGroup.mk'_surjective _).comp (sl4_iota_surj R K J hKJ)
  · rw [sl4_card_ker_comp (sl4_iota R K J hKJ) (sl4_iota_surj R K J hKJ)]
    exact Nat.coprime_mul_iff_left.2 ⟨hZ, Nat.Coprime.of_dvd_left (sl4_card_ker_dvd R K J hKJ) hR⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
