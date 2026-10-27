module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNCoprime
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN

open Subgroup

variable {G : Type} [Group G] [Finite G] {N T A K : Subgroup G} {r : ℕ}

omit [Finite G] in
theorem barIn_mono {H Y Z : Subgroup G} (hYZ : Y ≤ Z) : barIn H Y ≤ barIn H Z := by
  unfold barIn
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hYZ)

omit [Finite G] in
theorem mem_barIn {H Y : Subgroup G} {q : UC22.BarInf H} :
    q ∈ barIn H Y ↔ ∃ y : ↥H, (y : G) ∈ Y ∧
      QuotientGroup.mk' (CFSG.solvableRadical ↥H) y = q := by
  rw [barIn, Subgroup.mem_map]
  exact ⟨fun ⟨y, hy, hyq⟩ => ⟨y, Subgroup.mem_subgroupOf.mp hy, hyq⟩,
    fun ⟨y, hy, hyq⟩ => ⟨y, Subgroup.mem_subgroupOf.mpr hy, hyq⟩⟩

omit [Finite G] in
theorem mem_liftIn {H : Subgroup G} {L : Subgroup (UC22.BarInf H)} {x : G} :
    x ∈ liftIn H L ↔ ∃ h : x ∈ H,
      QuotientGroup.mk' (CFSG.solvableRadical ↥H) ⟨x, h⟩ ∈ L := by
  rw [liftIn, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hπ⟩
    exact ⟨⟨x, hx⟩, hπ, rfl⟩

omit [Finite G] in
theorem barIn_liftIn (H : Subgroup G) (L : Subgroup (UC22.BarInf H)) :
    barIn H (liftIn H L) = L := by
  refine le_antisymm ?_ ?_
  · rintro q ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ liftIn H L := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨_, hyL⟩ := (mem_liftIn).1 hy'
    simpa using hyL
  · intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥H) q
    exact ⟨y, Subgroup.mem_subgroupOf.mpr ((mem_liftIn).2 ⟨y.2, hq⟩), rfl⟩

omit [Finite G] in
theorem le_normalizer_liftIn {B H : Subgroup G} {L : Subgroup (UC22.BarInf H)}
    (hBH : B ≤ H) (hBN : B ≤ normalizer (H : Set G))
    (hBL : barIn H B ≤ normalizer (L : Set (UC22.BarInf H))) :
    B ≤ normalizer (liftIn H L : Set G) := by
  have key : ∀ b ∈ B, ∀ x ∈ liftIn H L, b * x * b⁻¹ ∈ liftIn H L := by
    intro b hb x hx
    obtain ⟨hxH, hxL⟩ := (mem_liftIn).1 hx
    have hbH : b ∈ H := hBH hb
    have hconjH : b * x * b⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.1 (hBN hb) x).1 hxH
    refine (mem_liftIn).2 ⟨hconjH, ?_⟩
    have hbL : QuotientGroup.mk' (CFSG.solvableRadical ↥H) ⟨b, hbH⟩ ∈ barIn H B :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
    have hquot : QuotientGroup.mk' (CFSG.solvableRadical ↥H) ⟨b * x * b⁻¹, hconjH⟩ =
        QuotientGroup.mk' (CFSG.solvableRadical ↥H) ⟨b, hbH⟩ *
          QuotientGroup.mk' (CFSG.solvableRadical ↥H) ⟨x, hxH⟩ *
            (QuotientGroup.mk' (CFSG.solvableRadical ↥H) ⟨b, hbH⟩)⁻¹ := by
      rw [show (⟨b * x * b⁻¹, hconjH⟩ : ↥H) = ⟨b, hbH⟩ * ⟨x, hxH⟩ * ⟨b, hbH⟩⁻¹ from
        Subtype.ext rfl]
      simp only [map_mul, map_inv]
    rw [hquot]
    exact (Subgroup.mem_normalizer_iff.1 (hBL hbL) _).1 hxL
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key b hb x
  · intro hx
    have h := key b⁻¹ (B.inv_mem hb) (b * x * b⁻¹) hx
    rwa [show b⁻¹ * (b * x * b⁻¹) * (b⁻¹)⁻¹ = x by group] at h

theorem barIn_Hinf {H D : Subgroup G} (hDH : D ≤ H) :
    barIn H (UC22.Hinf D) = UC22.Hinf (barIn H D) := by
  have h1 : (UC22.Hinf D).subgroupOf H = UC22.Hinf (D.subgroupOf H) :=
    CFSG.RankThree.PartTwo.KFacts.subgroupOf_inSubgroup_perfectResidual hDH
  calc barIn H (UC22.Hinf D)
      = ((UC22.Hinf D).subgroupOf H).map
          (QuotientGroup.mk' (CFSG.solvableRadical ↥H)) := rfl
    _ = (UC22.Hinf (D.subgroupOf H)).map
          (QuotientGroup.mk' (CFSG.solvableRadical ↥H)) := by rw [h1]
    _ = UC22.Hinf ((D.subgroupOf H).map
          (QuotientGroup.mk' (CFSG.solvableRadical ↥H))) :=
        CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map _ _
    _ = UC22.Hinf (barIn H D) := rfl

theorem Hyp146N.barIn_inf_liftIn_eq (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) (hATK : A ⊔ T ≤ K)
    (hNK : N ⊓ normalizer (A : Set G) ≤ K)
    {L : Subgroup (UC22.BarInf (UC22.conjClosure N A))}
    (hgen : (barIn (UC22.conjClosure N A) T ⊓ L) ⊔
      (centralizer (barIn (UC22.conjClosure N A) A :
        Set (UC22.BarInf (UC22.conjClosure N A))) ⊓ L) = L) :
    barIn (UC22.conjClosure N A) (K ⊓ liftIn (UC22.conjClosure N A) L) = L := by
  let H := UC22.conjClosure N A
  have hle : barIn H (K ⊓ liftIn H L) ≤ L := by
    have hmono : barIn H (K ⊓ liftIn H L) ≤ barIn H (liftIn H L) := barIn_mono inf_le_right
    rwa [barIn_liftIn H L] at hmono
  refine le_antisymm hle ?_
  have hsup : (barIn H T ⊓ L) ⊔
      (centralizer (barIn H A : Set (UC22.BarInf H)) ⊓ L) ≤
        barIn H (K ⊓ liftIn H L) := by
    refine sup_le ?_ ?_
    · rintro q ⟨hqT, hqL⟩
      obtain ⟨t, htT, rfl⟩ := (mem_barIn).1 hqT
      have htL : (t : G) ∈ liftIn H L := by
        rw [mem_liftIn]
        exact ⟨t.2, hqL⟩
      exact (mem_barIn).2 ⟨t, ⟨hATK (Subgroup.mem_sup_right htT), htL⟩, rfl⟩
    · intro q hq
      have hq' := h.centralizer_barIn_le hns L hq
      obtain ⟨z, hz, rfl⟩ := (mem_barIn).1 hq'
      have hzN : (z : G) ∈ N :=
        h.conjClosure_le (Subgroup.map_subtype_le _ hz.2)
      have hzNA : (z : G) ∈ normalizer (A : Set G) :=
        Subgroup.centralizer_le_normalizer (A : Set G) hz.1
      exact (mem_barIn).2
        ⟨z, ⟨hNK (Subgroup.mem_inf.mpr ⟨hzN, hzNA⟩), hz.2⟩, rfl⟩
  rwa [hgen] at hsup

theorem not_dvd_card_of_barIn_eq {H E : Subgroup G} {L : Subgroup (UC22.BarInf H)} {r : ℕ}
    (hEH : E ≤ H) (hEL : barIn H E = L) (hr : r.Prime)
    (hrL : ¬ r ∣ Nat.card L) (hrR : ¬ r ∣ Nat.card (UC22.OInf H)) :
    ¬ r ∣ Nat.card E := by
  have : Fact r.Prime := ⟨hr⟩
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  let ψ : ↥E →* UC22.BarInf H :=
    (QuotientGroup.mk' (CFSG.solvableRadical ↥H)).comp (Subgroup.inclusion hEH)
  have hψmem : ∀ z : ↥E, ψ z ∈ L := by
    intro z
    have hz : ψ z ∈ barIn H E :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr z.2)
    rwa [hEL] at hz
  have hdvdR : orderOf (ψ x) ∣ r := hx ▸ orderOf_map_dvd ψ x
  have hdvdL : orderOf (ψ x) ∣ Nat.card L := by
    have hord : orderOf (⟨ψ x, hψmem x⟩ : ↥L) = orderOf (ψ x) :=
      (Subgroup.orderOf_coe (⟨ψ x, hψmem x⟩ : ↥L)).symm
    rw [← hord]
    exact orderOf_dvd_natCard (⟨ψ x, hψmem x⟩ : ↥L)
  rcases (Nat.dvd_prime hr).1 hdvdR with h1 | h1
  · have hx1 : ψ x = 1 := orderOf_eq_one_iff.1 h1
    have hxrad : Subgroup.inclusion hEH x ∈ CFSG.solvableRadical ↥H :=
      (QuotientGroup.eq_one_iff _).1 (by simpa [ψ] using hx1)
    have hxR : (x : G) ∈ UC22.OInf H :=
      ⟨Subgroup.inclusion hEH x, hxrad, rfl⟩
    have hdvdRcard : r ∣ Nat.card (UC22.OInf H) := by
      have hord := orderOf_dvd_natCard (⟨(x : G), hxR⟩ : ↥(UC22.OInf H))
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe x] at hord
      rwa [hx] at hord
    exact hrR hdvdRcard
  · exact hrL (h1 ▸ hdvdL)

theorem barIn_OInf_eq_bot {H E : Subgroup G} {L : Subgroup (UC22.BarInf H)}
    (hEH : E ≤ H) (hEL : barIn H E = L) (hLsimple : IsSimpleGroup L)
    (hLnotsolv : ¬ Group.IsSolvable ↥L) :
    barIn H (UC22.OInf E) = ⊥ := by
  have hOEH : UC22.OInf E ≤ H := (Subgroup.map_subtype_le _).trans hEH
  have hOleL : barIn H (UC22.OInf E) ≤ L := by
    rw [← hEL]
    exact barIn_mono (Subgroup.map_subtype_le _)
  have hnorm : ∀ l ∈ L, ∀ n ∈ barIn H (UC22.OInf E),
      l * n * l⁻¹ ∈ barIn H (UC22.OInf E) := by
    intro l hl n hn
    have hl' : l ∈ barIn H E := by rwa [hEL]
    obtain ⟨e, heE, rfl⟩ := (mem_barIn).1 hl'
    obtain ⟨y, hyO, rfl⟩ := (mem_barIn).1 hn
    have heN : (e : G) ∈ normalizer (UC22.OInf E : Set G) :=
      UC22.uc22p20a_le_normalizer_oinf E heE
    have hy' : (e : G) * (y : G) * (e : G)⁻¹ ∈ UC22.OInf E :=
      (Subgroup.mem_normalizer_iff.1 heN (y : G)).1 hyO
    refine (mem_barIn).2 ⟨e * y * e⁻¹, ?_, ?_⟩
    · simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hy'
    · simp only [map_mul, map_inv]
  let M := (barIn H (UC22.OInf E)).subgroupOf L
  have hMnormal : M.Normal :=
    ⟨fun n hn g => hnorm (g : UC22.BarInf H) g.2 (n : UC22.BarInf H) hn⟩
  have hOsol : Group.IsSolvable ↥(barIn H (UC22.OInf E)) := by
    have : Group.IsSolvable ↥(UC22.OInf E) := UC22.uc22p20a_isSolvable_oinf E
    have : Group.IsSolvable ↥((UC22.OInf E).subgroupOf H) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hOEH).symm
    exact Group.isSolvable_of_surjective
      (MonoidHom.subgroupMap_surjective
        (QuotientGroup.mk' (CFSG.solvableRadical ↥H)) ((UC22.OInf E).subgroupOf H))
  have : M.Normal := hMnormal
  rcases hLsimple.eq_bot_or_eq_top_of_normal M with hM | hM
  · have hmap : ((barIn H (UC22.OInf E)).subgroupOf L).map L.subtype = ⊥ := by
      change M.map L.subtype = ⊥
      rw [hM, Subgroup.map_bot]
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hOleL] at hmap
  · have htop : barIn H (UC22.OInf E) = L := by
      refine le_antisymm hOleL ?_
      intro x hx
      have hxM : (⟨x, hx⟩ : ↥L) ∈ M := by
        rw [hM]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hxM
    rw [htop] at hOsol
    exact absurd hOsol hLnotsolv

theorem Hyp146N.exists_perfect_of_barThree (h : Hyp146N N T A r)
    (hns : ¬ Group.IsSolvable ↥(UC22.conjClosure N A)) (hATK : A ⊔ T ≤ K)
    (hNK : N ⊓ normalizer (A : Set G) ≤ K)
    (h3 : BarThree (barIn (UC22.conjClosure N A) A) (barIn (UC22.conjClosure N A) T) r) :
    ∃ E : Subgroup G, E ≤ K ∧ ⁅E, E⁆ = E ∧ A ≤ normalizer (E : Set G) ∧
      ¬ r ∣ Nat.card E ∧ ¬ ⁅E, A⁆ ≤ UC22.OInf E := by
  obtain ⟨L, hLsimple, hLperf, hAL, hLcomm, hrL, hgen⟩ := h3
  let H := UC22.conjClosure N A
  let Lpre := liftIn H L
  let D := K ⊓ Lpre
  have hDH : D ≤ H := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hHinfDH : UC22.Hinf D ≤ H := (Subgroup.map_subtype_le _).trans hDH
  have hAH : A ≤ H := UC22.uc22p22v_le_conjClosure N A
  have hAK : A ≤ K := le_sup_left.trans hATK
  have hAN : A ≤ normalizer (H : Set G) :=
    h.le.trans (UC22.uc22p22v_le_normalizer_conjClosure N A)
  have hANL : A ≤ normalizer (Lpre : Set G) := le_normalizer_liftIn hAH hAN hAL
  have hANK : A ≤ normalizer (K : Set G) := hAK.trans Subgroup.le_normalizer
  have hAND : A ≤ normalizer (D : Set G) :=
    (le_inf hANK hANL).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hbarD : barIn H D = L := Hyp146N.barIn_inf_liftIn_eq h hns hATK hNK hgen
  have hLperfect : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLperf
  have : Group.IsPerfect ↥L := hLperfect
  have hHinfL : UC22.Hinf L = L :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.perfectResidual_map_eq_of_isPerfect hLperfect
  have hbarE : barIn H (UC22.Hinf D) = L := by
    rw [barIn_Hinf hDH, hbarD, hHinfL]
  have : IsSimpleGroup ↥L := hLsimple
  have hLnotsolv : ¬ Group.IsSolvable ↥L := Group.IsPerfect.not_isSolvable ↥L
  refine ⟨UC22.Hinf D, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le _).trans inf_le_left
  · exact Subgroup.isPerfect_iff.mp
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map D)
  · exact hAND.trans
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map D)
  · exact not_dvd_card_of_barIn_eq hHinfDH hbarE h.prime hrL (h.not_dvd_card_OInf hns)
  · intro hle
    have hbotOE : barIn H (UC22.OInf (UC22.Hinf D)) = ⊥ :=
      barIn_OInf_eq_bot hHinfDH hbarE hLsimple hLnotsolv
    have hcomm : barIn H ⁅UC22.Hinf D, A⁆ = ⁅L, barIn H A⁆ := by
      rw [barIn_commutator hHinfDH hAH, hbarE]
    have hle' : barIn H ⁅UC22.Hinf D, A⁆ ≤ ⊥ :=
      (barIn_mono hle).trans (le_of_eq hbotOE)
    have hLbot : ⁅L, barIn H A⁆ = ⊥ := by
      rw [hcomm] at hle'
      exact le_bot_iff.mp hle'
    exact hLcomm hLbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN
