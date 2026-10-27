module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

theorem mk_ne_one_of_odd_card {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN : IsPGroup 2 N) {Y : Subgroup H} (hY : Odd (Nat.card Y)) {y : H} (hy : y ∈ Y)
    (hy1 : y ≠ 1) : QuotientGroup.mk' N y ≠ 1 := by
  intro h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff y] at h
  obtain ⟨k, hk⟩ := hN ⟨y, h⟩
  have hpow : y ^ (2 ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  have hdvd1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hdvd2 : orderOf y ∣ Nat.card Y := Subgroup.orderOf_dvd_natCard Y hy
  have hodd : Odd (orderOf y) := Odd.of_dvd_nat hY hdvd2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
  have hj0 : j = 0 := by
    by_contra hj0
    have hdiv : 2 ∣ orderOf y := by rw [hj]; exact dvd_pow_self 2 hj0
    exact hodd.not_two_dvd_nat hdiv
  exact hy1 (orderOf_eq_one_iff.1 (by rw [hj, hj0, pow_zero]))

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}

theorem card_map_subgroupOf_eq_two_pow_mQuot (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G)) :
    Nat.card ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) =
      2 ^ E3.mQuot V (UOf M V g) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ :=
    IsPGroup.iff_card.1 (isElemAbelian_map_subgroupOf (K := K) h).isPGroup
  have hcard : Nat.card ((V.subgroupOf (LOf V g)).map
      (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) = (UOf M V g).relIndex V :=
    card_map_subgroupOf_eq_relIndex h hKset
  have hrel : (UOf M V g).relIndex V = 2 ^ k := by rw [← hcard, hk]
  have hmq : E3.mQuot V (UOf M V g) = k := by
    change padicValNat 2 ((UOf M V g).relIndex V) = k
    rw [hrel, padicValNat.prime_pow]
  rw [hcard, hmq, hrel]

theorem card_eq_and_odd_of_torusData (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {g₀ : ↥(LOf V g) ⧸ K.subgroupOf (LOf V g)}
    {T : Subgroup (↥(LOf V g) ⧸ K.subgroupOf (LOf V g))}
    (hT : TorusData ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))))
      g₀ T) :
    Nat.card T = 2 ^ E3.mQuot V (UOf M V g) - 1 ∧ Odd (Nat.card T) := by
  have hcardA : Nat.card ((V.subgroupOf (LOf V g)).map
      (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) = 2 ^ E3.mQuot V (UOf M V g) :=
    card_map_subgroupOf_eq_two_pow_mQuot (K := K) h hKset
  have hAne : ((V.subgroupOf (LOf V g)).map
      (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) ≠ ⊥ :=
    map_subgroupOf_ne_bot (K := K) h hKset
  have h1lt : 1 < Nat.card ((V.subgroupOf (LOf V g)).map
      (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 hAne
  have h2 : 1 < 2 ^ E3.mQuot V (UOf M V g) := by
    rw [← hcardA]; exact h1lt
  have hmq0 : E3.mQuot V (UOf M V g) ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at h2
    exact lt_irrefl 1 h2
  refine ⟨?_, ?_⟩
  · rw [hT.2.1, hcardA]
  · rw [hT.2.1, hcardA]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.2 ⟨even_two, hmq0⟩) odd_one

theorem map_subtype_le_of_torusData (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {l : G} (hlL : l ∈ LOf V g) (hlV : conjSubgroup V g = conjSubgroup V l)
    {T : Subgroup (↥(LOf V g) ⧸ K.subgroupOf (LOf V g))}
    (hT : TorusData ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))))
      (QuotientGroup.mk' (K.subgroupOf (LOf V g)) ⟨l, hlL⟩) T)
    {Y' : Subgroup ↥(LOf V g)} (hY' : Y'.map (QuotientGroup.mk' (K.subgroupOf (LOf V g))) = T) :
    Y'.map (LOf V g).subtype ≤ LOf V g ⊓ M ⊓ conjSubgroup M g := by
  rintro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have hπT : QuotientGroup.mk' (K.subgroupOf (LOf V g)) y' ∈ T :=
    hY' ▸ Subgroup.mem_map_of_mem (QuotientGroup.mk' (K.subgroupOf (LOf V g))) hy'
  refine ⟨⟨y'.2, ?_⟩, ?_⟩
  · exact mem_M_of_mk_mem_normalizer h hgen hKset (hT.2.2.1 hπT)
  · have hnorm := hT.2.2.2.1 hπT
    rw [← map_subgroupOf_conjSubgroup_eq hlL hlV] at hnorm
    exact mem_conjM_of_mk_mem_normalizer h hgen hKset hnorm

theorem exists_conj_mul_inv_mem_UOf_of_torusData (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {g₀ : ↥(LOf V g) ⧸ K.subgroupOf (LOf V g)}
    {T : Subgroup (↥(LOf V g) ⧸ K.subgroupOf (LOf V g))}
    (hT : TorusData ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))))
      g₀ T)
    {Y' : Subgroup ↥(LOf V g)} (hY' : Y'.map (QuotientGroup.mk' (K.subgroupOf (LOf V g))) = T)
    (hYM : Y'.map (LOf V g).subtype ≤ M) {v w : G} (hv : v ∈ V) (hvU : v ∉ UOf M V g)
    (hw : w ∈ V) (hwU : w ∉ UOf M V g) :
    ∃ y ∈ Y'.map (LOf V g).subtype, y * v * y⁻¹ * w⁻¹ ∈ UOf M V g := by
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ K.subgroupOf L) := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup (↥L ⧸ K.subgroupOf L) := (V.subgroupOf L).map π
  let v' : ↥L := ⟨v, Subgroup.mem_sup_left hv⟩
  let w' : ↥L := ⟨w, Subgroup.mem_sup_left hw⟩
  have hv'A : π v' ∈ A := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hv)
  have hw'A : π w' ∈ A := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hw)
  have hv'1 : π v' ≠ 1 := fun hπ =>
    hvU ((mk_eq_one_iff_mem_UOf (K := K) h hKset (v := v') hv).1 hπ)
  have hw'1 : π w' ≠ 1 := fun hπ =>
    hwU ((mk_eq_one_iff_mem_UOf (K := K) h hKset (v := w') hw).1 hπ)
  obtain ⟨t, htT, htab⟩ := hT.2.2.2.2.1 (π v') hv'A hv'1 (π w') hw'A hw'1
  rw [← hY'] at htT
  obtain ⟨y', hy', hy't⟩ := Subgroup.mem_map.1 htT
  have hpi1 : π (y' * v' * y'⁻¹ * w'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy't, htab, mul_inv_cancel]
  have hKmem : (y' * v' * y'⁻¹ * w'⁻¹) ∈ K.subgroupOf L :=
    (QuotientGroup.eq_one_iff _).1 hpi1
  have hKG : (y' : G) * v * (y' : G)⁻¹ * w⁻¹ ∈ K := by
    have h := Subgroup.mem_subgroupOf.1 hKmem
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hyM : (y' : G) ∈ M := hYM (Subgroup.mem_map_of_mem _ hy')
  have hyNorm : (y' : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [h.normalizer_eq]; exact hyM
  have hyvV : (y' : G) * v * (y' : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 hyNorm v).1 hv
  have hVmem : (y' : G) * v * (y' : G)⁻¹ * w⁻¹ ∈ V :=
    V.mul_mem hyvV (V.inv_mem hw)
  refine ⟨(y' : G), Subgroup.mem_map_of_mem _ hy', ?_⟩
  rw [← V_inf_K_eq_U h hKset]
  exact ⟨hVmem, hKG⟩

theorem mem_NOf_of_torusData (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {l : G} (hlL : l ∈ LOf V g) (hlV : conjSubgroup V g = conjSubgroup V l)
    {T : Subgroup (↥(LOf V g) ⧸ K.subgroupOf (LOf V g))}
    (hT : TorusData ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))))
      (QuotientGroup.mk' (K.subgroupOf (LOf V g)) ⟨l, hlL⟩) T)
    {Y' : Subgroup ↥(LOf V g)} (hY' : Y'.map (QuotientGroup.mk' (K.subgroupOf (LOf V g))) = T)
    (hodd : Odd (Nat.card Y')) {y : G} (hy : y ∈ Y'.map (LOf V g).subtype) (hy1 : y ≠ 1)
    {v : G} (hv : v ∈ V) (hyv : y * v * y⁻¹ = v) : v ∈ NOf M V g := by
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ K.subgroupOf L) := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup (↥L ⧸ K.subgroupOf L) := (V.subgroupOf L).map π
  rw [Subgroup.mem_map] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have hy'1 : y' ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  have hπyT : π y' ∈ T := hY' ▸ Subgroup.mem_map_of_mem π hy'
  have hπy1 : π y' ≠ 1 :=
    mk_ne_one_of_odd_card (K.subgroupOf L) (isPGroup_subgroupOf_LOf h hKset) hodd hy' hy'1
  by_cases hvU : v ∈ UOf M V g
  · obtain ⟨c, s₁, hs₁, s₂, hs₂, hs₁1, hs₂1, hπ⟩ := hT.2.2.2.2.2.2 (π y') hπyT hπy1
    refine mem_NOf_of_mk_eq_mul h hgen hKset hlL hlV hs₁ hs₂ hs₁1 hs₂1 hπ
      (Subgroup.mem_sup_left hvU) ?_
    rw [show (y' : G) * v * (y' : G)⁻¹ = v from hyv, mul_inv_cancel]
    exact (NOf M V g).one_mem
  · let v' : ↥L := ⟨v, Subgroup.mem_sup_left hv⟩
    have hv'A : π v' ∈ A := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.2 hv)
    have hv'1 : π v' ≠ 1 := fun hπ =>
      hvU ((mk_eq_one_iff_mem_UOf (K := K) h hKset (v := v') hv).1 hπ)
    have hfixL : y' * v' * y'⁻¹ = v' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hyv
    have hfixπ : π y' * π v' * (π y')⁻¹ = π v' := by
      simpa only [map_mul, map_inv] using congrArg π hfixL
    exact absurd (hT.2.2.2.2.2.1 (π y') hπyT (π v') hv'A hv'1 hfixπ) hπy1

theorem exists_isFixedPointFreeTorus_of_torusData (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {l : G} (hlL : l ∈ LOf V g) (hlV : conjSubgroup V g = conjSubgroup V l)
    {T : Subgroup (↥(LOf V g) ⧸ K.subgroupOf (LOf V g))}
    (hT : TorusData ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))))
      (QuotientGroup.mk' (K.subgroupOf (LOf V g)) ⟨l, hlL⟩) T) :
    ∃ Y : Subgroup G, IsFixedPointFreeTorus M V g Y := by
  obtain ⟨hTcard, hTodd⟩ := card_eq_and_odd_of_torusData (K := K) h hKset hT
  obtain ⟨Y', hY'cyc, hY'card, hY'⟩ :=
    exists_isCyclic_map_eq_of_isPGroup (K.subgroupOf (LOf V g))
      (isPGroup_subgroupOf_LOf h hKset) hT.1 hTodd
  have hYle := map_subtype_le_of_torusData h hgen hKset hlL hlV hT hY'
  haveI : IsCyclic ↥Y' := hY'cyc
  have hcyc : IsCyclic ↥(Y'.map (LOf V g).subtype) :=
    isCyclic_of_surjective (((LOf V g).subtype).subgroupMap Y')
      (((LOf V g).subtype).subgroupMap_surjective Y')
  have hcardY : Nat.card (Y'.map (LOf V g).subtype) = 2 ^ E3.mQuot V (UOf M V g) - 1 := by
    rw [Subgroup.card_map_of_injective (K := Y') (LOf V g).subtype_injective, hY'card, hTcard]
  have hoddY' : Odd (Nat.card Y') := by rw [hY'card]; exact hTodd
  have hYM : Y'.map (LOf V g).subtype ≤ M := fun y hy => by
    have h1 : y ∈ LOf V g ⊓ M := (Subgroup.mem_inf.1 (hYle hy)).1
    exact (Subgroup.mem_inf.1 h1).2
  refine ⟨Y'.map (LOf V g).subtype, ⟨hYle, hcardY, hcyc, ?_⟩, ?_⟩
  · intro v hv hvU w hw hwU
    exact exists_conj_mul_inv_mem_UOf_of_torusData h hKset hT hY' hYM hv hvU hw hwU
  · intro y hy hy1 v hv hyv
    exact mem_NOf_of_torusData h hgen hKset hlL hlV hT hY' hoddY' hy hy1 hv hyv

end CFSG.LocalAnalysis.WeakClosure81
