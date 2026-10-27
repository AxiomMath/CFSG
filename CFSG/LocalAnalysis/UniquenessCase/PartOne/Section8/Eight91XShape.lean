module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Model
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91D4Core
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (card_map_of_disjoint_ker)

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (card_map_of_disjoint_ker)

private theorem k891xshape_extra_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {p n : ℕ} (h : IsExtraspecialExpP p n A) : IsExtraspecialExpP p n B := by
  unfold IsExtraspecialExpP at h ⊢
  obtain ⟨hcard, hexp, hcomm, hcenter⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact hcard
  · rw [← Monoid.exponent_eq_of_mulEquiv e]; exact hexp
  · have h1 : (commutator A).map e.toMonoidHom = commutator B := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    have h2 : (center A).map e.toMonoidHom = center B := Subgroup.map_center_eq e
    rw [← h1, hcomm, h2]
  · have hcard : Nat.card (center B) = Nat.card (center A) := by
      rw [← Subgroup.map_center_eq e]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective (center A) e.toMonoidHom e.injective).toEquiv).symm
    rw [hcard]; exact hcenter

private theorem k891xshape_su32_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : R891SU32 A) : R891SU32 B := by
  obtain ⟨φ, hsurj, hker, hcent⟩ := h
  refine ⟨φ.comp e.symm.toMonoidHom, hsurj.comp e.symm.surjective, ?_, ?_⟩
  · have hker_eq : (φ.comp e.symm.toMonoidHom).ker = φ.ker.map e.toMonoidHom := by
      ext y
      constructor
      · intro hy
        refine ⟨e.symm y, hy, ?_⟩
        simp
      · rintro ⟨a, ha, rfl⟩
        simpa using ha
    rw [hker_eq]
    exact k891xshape_extra_of_mulEquiv
      (Subgroup.equivMapOfInjective φ.ker e.toMonoidHom e.injective) hker
  · intro y hy
    rw [MonoidHom.mem_ker]
    have hx : e.symm y ∈ Subgroup.centralizer (φ.ker : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hea : e a ∈ (φ.comp e.symm.toMonoidHom).ker := by
        rw [MonoidHom.mem_ker]
        simpa using ha
      have hya := (Subgroup.mem_centralizer_iff.mp hy) (e a) hea
      refine e.injective ?_
      calc e (a * e.symm y) = e a * e (e.symm y) := map_mul _ _ _
        _ = e a * y := by rw [MulEquiv.apply_symm_apply]
        _ = y * e a := hya
        _ = e (e.symm y) * e a := by rw [MulEquiv.apply_symm_apply]
        _ = e (e.symm y * a) := (map_mul _ _ _).symm
    exact hcent hx

private theorem k891xshape_quasisimple_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  obtain ⟨hcomm, hsimple⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 : (commutator A).map e.toMonoidHom = commutator B := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr e.surjective]
      rfl
    rw [← h1, hcomm, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective]
  · exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e))).mp hsimple

private theorem k891xshape_threeCover_lieModel_of_mulEquiv {A B : Type} [Group A] [Group B]
    (e : A ≃* B) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m p f : ℕ}
    (h : ThreeCover (fun Y _ => LieModel Y t m p f) A) :
    ThreeCover (fun Y _ => LieModel Y t m p f) B := by
  obtain ⟨hq, hcenter, hquot⟩ := h
  refine ⟨k891xshape_quasisimple_of_mulEquiv e hq, ?_, ?_⟩
  · have hcard : Nat.card (center B) = Nat.card (center A) := by
      rw [← Subgroup.map_center_eq e]
      exact (Nat.card_congr
        (Subgroup.equivMapOfInjective (center A) e.toMonoidHom e.injective).toEquiv).symm
    rw [hcard, hcenter]
  · exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)) hquot

private theorem k891xshape_sl3Two_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {n : ℕ} (h : R891SL3Two A n) : R891SL3Two B n := by
  unfold R891SL3Two at h ⊢
  rcases h with ⟨hn, hsu⟩ | ⟨hn, hev, hcov⟩ | ⟨hn, hod, hcov⟩
  · exact Or.inl ⟨hn, k891xshape_su32_of_mulEquiv e hsu⟩
  · exact Or.inr (Or.inl ⟨hn, hev, k891xshape_threeCover_lieModel_of_mulEquiv e hcov⟩)
  · exact Or.inr (Or.inr ⟨hn, hod, k891xshape_threeCover_lieModel_of_mulEquiv e hcov⟩)

private theorem k891xshape_le_pCore {X : Type} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hp : IsPGroup 2 N) : N ≤ CFSG.pCore 2 X :=
  le_sSup ⟨hN, hp⟩

private theorem k891xshape_pCore_two_eq_bot_of_sl3two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : R891SL3Two Y n) : CFSG.pCore 2 Y = ⊥ := by
  unfold R891SL3Two at h
  rcases h with ⟨rfl, hsu⟩ | ⟨hn, -, hcov⟩ | ⟨hn, -, hcov⟩
  · obtain ⟨φ, hsurj, hker, hcent⟩ := hsu
    unfold IsExtraspecialExpP at hker
    have hKp : IsPGroup 3 ↥φ.ker := IsPGroup.of_card (n := 1 + 2 * 1) hker.1
    have hdisj : Disjoint (CFSG.pCore 2 Y) φ.ker :=
      IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ CFSG.pCore_isPGroup hKp
    have hle : CFSG.pCore 2 Y ≤ φ.ker :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (Subgroup.commutator_eq_bot_of_disjoint hdisj)).trans hcent
    rw [eq_bot_iff]
    exact (le_inf le_rfl hle).trans (le_of_eq (disjoint_iff.mp hdisj))
  · obtain ⟨hq, hcenter, hquot⟩ := hcov
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (CFSG.pCore 2 Y) with hle | htop
    · have hcenterP : IsPGroup 3 (center Y) := IsPGroup.of_card (n := 1) (by rw [hcenter]; norm_num)
      have hdisj : Disjoint (CFSG.pCore 2 Y) (center Y) :=
        IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ CFSG.pCore_isPGroup hcenterP
      rw [eq_bot_iff]
      exact (le_inf le_rfl hle).trans (le_of_eq (disjoint_iff.mp hdisj))
    · exfalso
      have htop2 : IsPGroup 2 (⊤ : Subgroup Y) := htop ▸ CFSG.pCore_isPGroup
      exact @Group.IsPerfect.not_isNilpotent Y _
        (CFSG.ComponentClassification.Quasisimple.nontrivial hq) ⟨hq.1⟩
        ((htop2.of_equiv Subgroup.topEquiv).isNilpotent)
  · obtain ⟨hq, hcenter, hquot⟩ := hcov
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (CFSG.pCore 2 Y) with hle | htop
    · have hcenterP : IsPGroup 3 (center Y) := IsPGroup.of_card (n := 1) (by rw [hcenter]; norm_num)
      have hdisj : Disjoint (CFSG.pCore 2 Y) (center Y) :=
        IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ CFSG.pCore_isPGroup hcenterP
      rw [eq_bot_iff]
      exact (le_inf le_rfl hle).trans (le_of_eq (disjoint_iff.mp hdisj))
    · exfalso
      have htop2 : IsPGroup 2 (⊤ : Subgroup Y) := htop ▸ CFSG.pCore_isPGroup
      exact @Group.IsPerfect.not_isNilpotent Y _
        (CFSG.ComponentClassification.Quasisimple.nontrivial hq) ⟨hq.1⟩
        ((htop2.of_equiv Subgroup.topEquiv).isNilpotent)

private theorem k891xshape_orderOf_two_pow_of_map {G G' : Type} [Group G] [Finite G] [Group G']
    (φ : G →* G') (hker : IsPGroup 2 φ.ker) {x : G} {k : ℕ}
    (hk : orderOf (φ x) = 2 ^ k) : ∃ j : ℕ, orderOf x = 2 ^ j := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hdvd : 2 ^ k ∣ orderOf x := hk ▸ orderOf_map_dvd φ x
  rw [hab] at hdvd
  have hcop : Nat.Coprime (2 ^ k) b :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hb))
  have hka : 2 ^ k ∣ 2 ^ a := hcop.dvd_of_dvd_mul_right hdvd
  have hxker : x ^ 2 ^ a ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    rw [map_pow]
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    exact hka
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hker ⟨x ^ 2 ^ a, hxker⟩
  rw [Subgroup.orderOf_mk] at hj
  have hord : orderOf (x ^ 2 ^ a) = b := by
    rw [orderOf_pow, hab]
    have h1 : Nat.gcd (2 ^ a * b) (2 ^ a) = 2 ^ a := by
      rw [Nat.gcd_comm]
      exact Nat.gcd_eq_left (dvd_mul_right (2 ^ a) b)
    rw [h1, Nat.mul_div_cancel_left]
    exact pow_pos (by norm_num) a
  rw [hord] at hj
  have hb1 : b = 1 := by
    rcases j with _ | m
    · simpa using hj
    · exfalso
      have heven : Even b := by
        rw [hj, pow_succ]
        exact ⟨2 ^ m, by ring⟩
      exact Nat.not_odd_iff_even.mpr heven hb
  exact ⟨a, by rw [hab, hb1, mul_one]⟩

private theorem k891xshape_map_pElementSubgroup_two {G G' : Type} [Group G] [Group G'] [Finite G]
    (φ : G →* G') (hker : IsPGroup 2 φ.ker) (X : Subgroup G) :
    (CFSG.RankThree.PartOne.pElementSubgroup 2 X).map φ =
      CFSG.RankThree.PartOne.pElementSubgroup 2 (X.map φ) := by
  unfold CFSG.RankThree.PartOne.pElementSubgroup
  rw [MonoidHom.map_closure]
  apply le_antisymm
  · refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨hx, k, hk⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hk ▸ orderOf_map_dvd φ x)
    exact ⟨j, hj⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨⟨x, hx, rfl⟩, k, hk⟩
    obtain ⟨j, hj⟩ := k891xshape_orderOf_two_pow_of_map φ hker hk
    exact Subgroup.subset_closure ⟨x, ⟨hx, j, hj⟩, rfl⟩

private theorem k891xshape_factorization_three_bar2 {G : Type} [Group G] [Finite G] {L : Subgroup G} :
    (Nat.card ↥L).factorization 3 = (Nat.card (Bar2 L)).factorization 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let O : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hcardmul : Nat.card O * Nat.card (Bar2 L) = Nat.card ↥L := by
    have hh := Subgroup.card_ker_mul_card_of_surjective (f := QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O)
    simpa [O, Bar2, QuotientGroup.ker_mk'] using hh
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  have h3O : ¬ 3 ∣ Nat.card O := by
    rw [hn]
    intro h3
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hfacO : (Nat.card O).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3O
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card (Bar2 L) ≠ 0 := Nat.card_pos.ne'
  rw [← hcardmul, Nat.factorization_mul hO0 hB0, Finsupp.add_apply, hfacO, zero_add]

private theorem k891xshape_isSylowOf_barImage {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (hQ : IsSylowOf 3 Q L) : IsSylowOf 3 (barImage L Q) (⊤ : Subgroup (Bar2 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQL : Q ≤ L := hQ.le
  have hQp : IsPGroup 3 Q := hQ.isPGroup
  have hdisj : Disjoint (Q.subgroupOf L) (CFSG.pCore 2 ↥L) :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hQp.comap_subtype CFSG.pCore_isPGroup
  have hcard : Nat.card (barImage L Q) = Nat.card Q := by
    have hdisj' : Disjoint (Q.subgroupOf L) (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
      rwa [QuotientGroup.ker_mk']
    have h1 : Nat.card (barImage L Q) = Nat.card (Q.subgroupOf L) :=
      card_map_of_disjoint_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (Q.subgroupOf L) hdisj'
    have h2 : Nat.card (Q.subgroupOf L) = Nat.card Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
    exact h1.trans h2
  have hfac := k891xshape_factorization_three_bar2 (L := L)
  have hQcard : Nat.card Q = 3 ^ (Nat.card (⊤ : Subgroup (Bar2 L))).factorization 3 := by
    rw [Subgroup.card_top, ← hfac]
    exact hQ.card_eq
  exact CFSG.ABGLocalTools.isSylowOf_of_card le_top (hcard.trans hQcard)

private theorem k891xshape_centralizer_subgroupOf_map {G : Type} [Group G] {M A : Subgroup G}
    (hAM : A ≤ M) :
    (Subgroup.centralizer (A.subgroupOf M : Set ↥M)).map M.subtype =
      M ⊓ Subgroup.centralizer (A : Set G) := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m.2, ?_⟩
    intro a ha
    have hy : (⟨a, hAM ha⟩ : ↥M) ∈ A.subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact ha
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hm) ⟨a, hAM ha⟩ hy)
  · rintro ⟨hgM, hgc⟩
    refine ⟨⟨g, hgM⟩, ?_, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hgc) (y : G) (Subgroup.mem_subgroupOf.mp hy)

private theorem k891xshape_barImage_centralizer {G : Type} [Group G] [Finite G] {L Z : Subgroup G}
    (hZL : Z ≤ L) (hZp : IsPGroup 3 (Z.subgroupOf L)) :
    barImage L (L ⊓ centralizer (Z : Set G)) = centralizer (barImage L Z : Set (Bar2 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    rw [hn]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hsub : (L ⊓ centralizer (Z : Set G)).subgroupOf L =
      centralizer (Z.subgroupOf L : Set ↥L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left, k891xshape_centralizer_subgroupOf_map hZL]
  rw [barImage, hsub]
  exact (CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hN3 hZp).symm

private theorem k891xshape_barImage_opp {G : Type} [Group G] [Finite G] {L Y : Subgroup G}
    (hYL : Y ≤ L) :
    barImage L (Opp 2 Y) = Opp 2 (barImage L Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNp : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hbot : IsPGroup 2 (L.subtype : ↥L →* G).ker := by
    rw [show (L.subtype : ↥L →* G).ker = ⊥ from Subgroup.ker_subtype L]
    exact IsPGroup.of_bot
  have hmap : (CFSG.RankThree.PartOne.pElementSubgroup 2 (Y.subgroupOf L)).map L.subtype =
      Opp 2 Y := by
    rw [k891xshape_map_pElementSubgroup_two L.subtype hbot (Y.subgroupOf L),
      Subgroup.map_subgroupOf_eq_of_le hYL]
    rfl
  have hsub : (Opp 2 Y).subgroupOf L =
      CFSG.RankThree.PartOne.pElementSubgroup 2 (Y.subgroupOf L) := by
    change Subgroup.comap L.subtype (Opp 2 Y) =
      CFSG.RankThree.PartOne.pElementSubgroup 2 (Y.subgroupOf L)
    rw [← hmap, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  rw [barImage, hsub]
  exact k891xshape_map_pElementSubgroup_two _ hNp (Y.subgroupOf L)

private theorem k891xshape_barImage_derInf8 {G : Type} [Group G] [Finite G] {L Y : Subgroup G}
    (hYL : Y ≤ L) :
    barImage L (DerInf8 Y) = DerInf8 (barImage L Y) := by
  have hDL : DerInf8 Y ≤ L :=
    (Subgroup.map_subtype_le (perfectResidual ↥Y)).trans hYL
  have hsub : (DerInf8 Y).subgroupOf L = inSubgroup perfectResidual (Y.subgroupOf L) := by
    apply Subgroup.map_injective L.subtype_injective
    show Subgroup.map L.subtype ((DerInf8 Y).subgroupOf L) =
      Subgroup.map L.subtype (inSubgroup perfectResidual (Y.subgroupOf L))
    have h1 : Subgroup.map L.subtype ((DerInf8 Y).subgroupOf L) = DerInf8 Y :=
      Subgroup.map_subgroupOf_eq_of_le hDL
    have h2 : Subgroup.map L.subtype (inSubgroup perfectResidual (Y.subgroupOf L)) = DerInf8 Y := by
      rw [CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
        L.subtype L.subtype_injective (Y.subgroupOf L)]
      rw [Subgroup.map_subgroupOf_eq_of_le hYL]
      rfl
    rw [h1, h2]
  rw [barImage, hsub]
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Yl : Subgroup ↥L := Y.subgroupOf L
  let f : ↥Yl →* ↥(Yl.map π) :=
    (π.comp Yl.subtype).codRestrict _ (fun y => Subgroup.mem_map_of_mem π y.2)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp z.2
    exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩
  have hres := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq f hf
  have hcomp : (Yl.map π).subtype.comp f = π.comp Yl.subtype := by
    ext x; rfl
  change ((CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥Yl).map Yl.subtype).map π =
    ((CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥(Yl.map π)).map (Yl.map π).subtype)
  rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map, hres]

private theorem k891xshape_zOf_map_of_injOn {H Y : Type} [Group H] [Group Y] (φ : H →* Y)
    {T : Subgroup H} (hinj : Set.InjOn φ (T : Set H)) :
    ZOf (T.map φ) = (ZOf T).map φ := by
  ext y
  constructor
  · rintro ⟨⟨t₀, ht₀, rfl⟩, hy⟩
    refine ⟨t₀, ⟨ht₀, Subgroup.mem_centralizer_iff.mpr ?_⟩, rfl⟩
    intro t ht
    have := Subgroup.mem_centralizer_iff.mp hy (φ t) (Subgroup.mem_map_of_mem φ ht)
    rw [← map_mul, ← map_mul] at this
    exact hinj (T.mul_mem ht ht₀) (T.mul_mem ht₀ ht) this
  · rintro ⟨z, ⟨hzT, hzc⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem φ hzT, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hzc t ht]

private theorem k891xshape_zOf_subgroupOf {G : Type} [Group G] {T : Subgroup G} (M : Subgroup G)
    (hTM : T ≤ M) :
    ZOf (T.subgroupOf M) = (ZOf T).subgroupOf M := by
  ext a
  simp only [ZOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨haT, hac⟩
    refine ⟨haT, fun t ht => ?_⟩
    exact congrArg Subtype.val (hac ⟨t, hTM ht⟩ ht)
  · rintro ⟨haT, hac⟩
    refine ⟨haT, fun t ht => ?_⟩
    exact Subtype.ext (hac t ht)

private theorem k891xshape_mk_injOn {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (hQp : IsPGroup 3 (Q.subgroupOf L)) :
    Set.InjOn (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (Q.subgroupOf L : Set ↥L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    rw [hn]
    intro h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hbot : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ⊓ Q.subgroupOf L = ⊥ := by
    rw [QuotientGroup.ker_mk', inf_comm]
    exact CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hN3 hQp
  intro a ha b hb hab
  have hmem : a * b⁻¹ ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker ⊓ Q.subgroupOf L := by
    refine ⟨?_, (Q.subgroupOf L).mul_mem ha ((Q.subgroupOf L).inv_mem hb)⟩
    show (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (a * b⁻¹) = 1
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  rw [hbot, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

private theorem k891xshape_zOf_barImage {G : Type} [Group G] [Finite G] {L Q : Subgroup G}
    (hQL : Q ≤ L) (hQp : IsPGroup 3 (Q.subgroupOf L)) :
    ZOf (barImage L Q) = barImage L (ZOf Q) := by
  have hinj := k891xshape_mk_injOn (L := L) (Q := Q) hQp
  have h1 := k891xshape_zOf_map_of_injOn (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) hinj
  rw [show barImage L Q = (Q.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) from rfl,
    h1, k891xshape_zOf_subgroupOf L hQL]
  rfl


private theorem k891xshape_barImage_R891X {G : Type} [Group G] [Finite G] {L Z : Subgroup G}
    (hZL : Z ≤ L) (hZp : IsPGroup 3 (Z.subgroupOf L)) (n : ℕ) :
    barImage L (R891X L Z n) = R891X (⊤ : Subgroup (Bar2 L)) (barImage L Z) n := by
  unfold R891X
  by_cases hn : n = 1
  · rw [if_pos hn, if_pos hn]
    rw [k891xshape_barImage_opp inf_le_left, k891xshape_barImage_centralizer hZL hZp]
    rw [top_inf_eq]
  · rw [if_neg hn, if_neg hn]
    rw [k891xshape_barImage_derInf8 inf_le_left, k891xshape_barImage_centralizer hZL hZp]
    rw [top_inf_eq]

private theorem k891xshape_pCore_eq_ker {G : Type} [Group G] [Finite G]
    {L X : Subgroup G} (hXL : X ≤ L)
    (hbot : CFSG.pCore 2 ↥(barImage L X) = ⊥) :
    CFSG.pCore 2 ↥X = ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
      (Subgroup.inclusion hXL)).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let g : ↥X →* Bar2 L := π.comp (Subgroup.inclusion hXL)
  have hgr : g.range = barImage L X := by
    rw [show g = π.comp (Subgroup.inclusion hXL) from rfl, MonoidHom.range_comp,
      Subgroup.inclusion_range, barImage]
  have hker : g.ker = (CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hXL) := by
    rw [show g = π.comp (Subgroup.inclusion hXL) from rfl,
      ← MonoidHom.comap_ker π (Subgroup.inclusion hXL), QuotientGroup.ker_mk']
  apply le_antisymm
  ·
    let g' : ↥X →* ↥(barImage L X) := g.codRestrict (barImage L X) (fun x => by
      rw [← hgr]; exact ⟨x, rfl⟩)
    have hg'ker : g'.ker = g.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact Subtype.ext_iff
    have hg'surj : Function.Surjective g' := by
      intro y
      have hy : (y : Bar2 L) ∈ g.range := by rw [hgr]; exact y.2
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
      exact ⟨x, Subtype.ext hx⟩
    have hnorm : ((CFSG.pCore 2 ↥X).map g').Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥X)).map g' hg'surj
    have hp : IsPGroup 2 ((CFSG.pCore 2 ↥X).map g') :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map g'
    have hle : (CFSG.pCore 2 ↥X).map g' ≤ CFSG.pCore 2 ↥(barImage L X) :=
      k891xshape_le_pCore hnorm hp
    rw [hbot] at hle
    intro x hx
    have hx' : g' x ∈ (CFSG.pCore 2 ↥X).map g' := Subgroup.mem_map_of_mem g' hx
    have hxbot : g' x = 1 := by
      have := hle hx'
      rwa [Subgroup.mem_bot] at this
    rw [← hg'ker, MonoidHom.mem_ker]
    exact hxbot
  ·
    rw [hker]
    have hnorm : ((CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hXL)).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥L)).comap (Subgroup.inclusion hXL)
    have hp : IsPGroup 2 ((CFSG.pCore 2 ↥L).comap (Subgroup.inclusion hXL)) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).comap_of_injective
        (Subgroup.inclusion hXL) (Subgroup.inclusion_injective hXL)
    exact k891xshape_le_pCore hnorm hp

private noncomputable def k891xshape_bar2_iso {G : Type} [Group G] [Finite G]
    {L X : Subgroup G} (hXL : X ≤ L)
    (hbot : CFSG.pCore 2 ↥(barImage L X) = ⊥) :
    Bar2 X ≃* ↥(barImage L X) := by
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let g : ↥X →* Bar2 L := π.comp (Subgroup.inclusion hXL)
  have hgr : g.range = barImage L X := by
    rw [show g = π.comp (Subgroup.inclusion hXL) from rfl, MonoidHom.range_comp,
      Subgroup.inclusion_range, barImage]
  have hker : CFSG.pCore 2 ↥X = g.ker := k891xshape_pCore_eq_ker hXL hbot
  have e : Bar2 X ≃* ↥g.range :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivRange g)
  rw [hgr] at e
  exact e

private theorem k891xshape_R891X_le {G : Type} [Group G] [Finite G] {L Z : Subgroup G} (n : ℕ) :
    R891X L Z n ≤ L := by
  unfold R891X
  by_cases hn : n = 1
  · rw [if_pos hn]
    change CFSG.RankThree.PartOne.pElementSubgroup 2 (L ⊓ centralizer (Z : Set G)) ≤ L
    unfold CFSG.RankThree.PartOne.pElementSubgroup
    rw [Subgroup.closure_le]
    intro x hx
    exact (Subgroup.mem_inf.mp hx.1).1
  · rw [if_neg hn]
    exact (Subgroup.map_subtype_le (perfectResidual ↥(L ⊓ centralizer (Z : Set G)))).trans inf_le_left

private theorem k891xshape_xShape
    {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (n : ℕ) (hset : R891Set D L S n)
    (hbasic : R891Basic D L S) :
    R891SL3Two (Bar2 (R891X L (ZOf (S ⊓ L)) n)) n := by
  let Z : Subgroup G := ZOf (S ⊓ L)
  have hZL : Z ≤ L := inf_le_left.trans inf_le_right
  have hZp : IsPGroup 3 (Z.subgroupOf L) := by
    have hZcard : Nat.card Z = 3 := hbasic.zOrder
    have hZpZ : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
    exact hZpZ.comap_of_injective L.subtype Subtype.coe_injective
  have hQp : IsPGroup 3 ((S ⊓ L).subgroupOf L) := hbasic.sylowL.isPGroup.comap_subtype
  have hsyl : IsSylowOf 3 (barImage L (S ⊓ L)) (⊤ : Subgroup (Bar2 L)) :=
    k891xshape_isSylowOf_barImage hbasic.sylowL
  have hSL3 : R891SL3Two ↥(R891X (⊤ : Subgroup (Bar2 L))
      (ZOf (barImage L (S ⊓ L))) n) n := by
    by_cases hn : n = 1
    · obtain ⟨S₀, B₀, hsetup⟩ := exists_r891D4Setup hset.d4
      obtain ⟨z, hzS, hz3, hz1, g, hZeq⟩ := hsetup.exists_zOf_eq hsyl
      obtain ⟨R₀, hR₀⟩ := hsetup.layer z hzS hz3 hz1
      have hR := hR₀.map (MulAut.conj g)
      have hcent : centralizer (ZOf (barImage L (S ⊓ L)) : Set (Bar2 L)) =
          centralizer ({(MulAut.conj g) z} : Set (Bar2 L)) := by
        rw [hZeq, MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure,
          Subgroup.centralizer_closure]
        rfl
      have hXeq : R891X (⊤ : Subgroup (Bar2 L))
          (ZOf (barImage L (S ⊓ L))) n = R₀.map (MulAut.conj g).toMonoidHom := by
        rw [R891X, if_pos hn, top_inf_eq, hcent]
        exact hR.opp_eq hn
      rw [hXeq]
      exact hR.sl3Two
    · have hn1 : 1 ≤ n := hset.d4.admissible.2.1
      have hn2 : 2 ≤ n := by omega
      have hZbar : Nat.card (ZOf (barImage L (S ⊓ L))) = 3 := by
        rw [k891xshape_zOf_barImage inf_le_right hQp]
        have hmap : Nat.card (barImage L Z) = Nat.card Z := by
          let π := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
          have hdisj : Disjoint (Z.subgroupOf L) π.ker := by
            rw [QuotientGroup.ker_mk']
            exact IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hZp
              (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
          change Nat.card ((Z.subgroupOf L).map π) = Nat.card Z
          rw [card_map_of_disjoint_ker π _ hdisj,
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv]
        change Nat.card (barImage L Z) = 3
        exact hmap.trans hbasic.zOrder
      exact r891SL3Two_R891X_of_central_sylow_of_two_le hn2 hset.d4 hsyl hZbar
  have hZbar : ZOf (barImage L (S ⊓ L)) = barImage L Z :=
    k891xshape_zOf_barImage inf_le_right hQp
  have hXbar : R891X (⊤ : Subgroup (Bar2 L)) (barImage L Z) n = barImage L (R891X L Z n) :=
    (k891xshape_barImage_R891X hZL hZp n).symm
  have hSL3' : R891SL3Two ↥(barImage L (R891X L Z n)) n := by
    rw [hZbar, hXbar] at hSL3
    exact hSL3
  have hbot : CFSG.pCore 2 ↥(barImage L (R891X L Z n)) = ⊥ :=
    k891xshape_pCore_two_eq_bot_of_sl3two hSL3'
  have hXle : R891X L Z n ≤ L := k891xshape_R891X_le n
  have e := k891xshape_bar2_iso hXle hbot
  exact k891xshape_sl3Two_of_mulEquiv e.symm hSL3'


private theorem k891xshzw_R891X_le_centralizer {G : Type} [Group G] [Finite G]
    (L Z : Subgroup G) (n : ℕ) :
    R891X L Z n ≤ Subgroup.centralizer (Z : Set G) := by
  unfold R891X
  by_cases hn : n = 1
  · rw [if_pos hn]
    change CFSG.RankThree.PartOne.pElementSubgroup 2 (L ⊓ centralizer (Z : Set G)) ≤
      centralizer (Z : Set G)
    unfold CFSG.RankThree.PartOne.pElementSubgroup
    rw [Subgroup.closure_le]
    intro x hx
    exact (Subgroup.mem_inf.mp hx.1).2
  · rw [if_neg hn]
    exact (Subgroup.map_subtype_le (perfectResidual ↥(L ⊓ centralizer (Z : Set G)))).trans
      inf_le_right

private theorem k891xshzw_eq_of_barImage_eq {G : Type} [Group G] [Finite G]
    {L A B : Subgroup G} (hAL : A ≤ L) (hBL : B ≤ L)
    (hAp : IsPGroup 3 A) (hBp : IsPGroup 3 B)
    (hAB : A ≤ Subgroup.centralizer (B : Set G))
    (hbar : barImage L A = barImage L B) : A = B := by
  have hABn : A ≤ Subgroup.normalizer (B : Set G) :=
    hAB.trans (Subgroup.centralizer_le_normalizer (B : Set G))
  have hQp : IsPGroup 3 ↥(A ⊔ B) := IsPGroup.to_sup_of_normal_right' hAp hBp hABn
  have hQpL : IsPGroup 3 ((A ⊔ B).subgroupOf L) := hQp.comap_subtype
  have hinj := k891xshape_mk_injOn (L := L) (Q := A ⊔ B) hQpL
  apply le_antisymm
  · intro a ha
    have haL : a ∈ L := hAL ha
    have hmemA : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨a, haL⟩ : ↥L) ∈ barImage L A :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
    have hmemB : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨a, haL⟩ : ↥L) ∈ barImage L B := by
      rw [← hbar]
      exact hmemA
    obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hmemB
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have heq : (⟨a, haL⟩ : ↥L) = b :=
      hinj (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left ha))
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hbB)) hbeq.symm
    have hval : a = (b : G) := by simpa using congrArg Subtype.val heq
    rw [hval]
    exact hbB
  · intro b hb
    have hbL : b ∈ L := hBL hb
    have hmemB : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨b, hbL⟩ : ↥L) ∈ barImage L B :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
    have hmemA : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨b, hbL⟩ : ↥L) ∈ barImage L A := by
      rw [hbar]
      exact hmemB
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hmemA
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have heq : (⟨b, hbL⟩ : ↥L) = a :=
      hinj (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hb))
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left haA)) haeq.symm
    have hval : b = (a : G) := by simpa using congrArg Subtype.val heq
    rw [hval]
    exact haA

private theorem k891xshape_zWeak {G : Type} [Group G] [Finite G] (D : Data G)
    (hD4 : R891D4Core) (L S : Subgroup G) (n : ℕ) (hset : R891Set D L S n)
    (hbasic : R891Basic D L S) :
    ∀ m ∈ D.M, (ZOf (S ⊓ L)).map (MulAut.conj m).toMonoidHom ≤ R891X L (ZOf (S ⊓ L)) n →
      (ZOf (S ⊓ L)).map (MulAut.conj m).toMonoidHom = ZOf (S ⊓ L) := by
  intro m hm hle
  let Z : Subgroup G := ZOf (S ⊓ L)
  let P : Subgroup G := S ⊓ L
  have hZL : Z ≤ L := inf_le_left.trans inf_le_right
  have hPL : P ≤ L := inf_le_right
  have hZcard : Nat.card Z = 3 := hbasic.zOrder
  have hZpZ : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
  have hZp : IsPGroup 3 (Z.subgroupOf L) :=
    hZpZ.comap_of_injective L.subtype Subtype.coe_injective
  have hPp : IsPGroup 3 (P.subgroupOf L) := hbasic.sylowL.isPGroup.comap_subtype
  have hsyl : IsSylowOf 3 (barImage L P) ⊤ := k891xshape_isSylowOf_barImage hbasic.sylowL
  have hmL : m ∈ Subgroup.normalizer (L : Set G) := hbasic.normal hm
  let e : MulAut ↥L := Subgroup.normalizerMonoidHom (H := L) ⟨m, hmL⟩
  have he_apply : ∀ x : ↥L, ((e x : ↥L) : G) = (MulAut.conj m) (x : G) := by
    intro x
    rfl
  have hchar : (CFSG.pCore 2 ↥L).map e.toMonoidHom = CFSG.pCore 2 ↥L :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance e
  let φ : MulAut (Bar2 L) :=
    QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) e hchar
  have hφ_apply : ∀ x : ↥L, φ (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) (e x) := fun x =>
    QuotientGroup.congr_mk' (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) e hchar x
  have hcomp : φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp e.toMonoidHom := by
    ext x
    exact hφ_apply x
  have hsub : ∀ A : Subgroup G, A ≤ L →
      (A.subgroupOf L).map e.toMonoidHom =
        (A.map (MulAut.conj m).toMonoidHom).subgroupOf L := by
    intro A hAL
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨(y : G), hyA, ?_⟩)
      exact (he_apply y).symm.trans (congrArg Subtype.val hyx)
    · intro hx
      have hx' : (x : G) ∈ A.map (MulAut.conj m).toMonoidHom :=
        Subgroup.mem_subgroupOf.mp hx
      obtain ⟨a, haA, hax⟩ := Subgroup.mem_map.mp hx'
      refine Subgroup.mem_map.mpr
        ⟨(⟨a, hAL haA⟩ : ↥L), Subgroup.mem_subgroupOf.mpr haA, ?_⟩
      apply Subtype.ext
      change ((e ⟨a, hAL haA⟩ : ↥L) : G) = (x : G)
      rw [he_apply]
      exact hax
  have hbarA : ∀ A : Subgroup G, A ≤ L →
      barImage L (A.map (MulAut.conj m).toMonoidHom) =
        (barImage L A).map φ.toMonoidHom := by
    intro A hAL
    calc barImage L (A.map (MulAut.conj m).toMonoidHom)
        = ((A.map (MulAut.conj m).toMonoidHom).subgroupOf L).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := rfl
      _ = (((A.subgroupOf L).map e.toMonoidHom).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by rw [hsub A hAL]
      _ = (A.subgroupOf L).map
            ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp e.toMonoidHom) := by
            rw [Subgroup.map_map]
      _ = (A.subgroupOf L).map
            (φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by
            rw [← hcomp]
      _ = ((A.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map
            φ.toMonoidHom := by
            rw [← Subgroup.map_map]
      _ = (barImage L A).map φ.toMonoidHom := rfl
  have hbarZ := hbarA Z hZL
  have hZmL : Z.map (MulAut.conj m).toMonoidHom ≤ L := by
    rintro x ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hmL z).mp (hZL hz)
  have hZcent : Z.map (MulAut.conj m).toMonoidHom ≤ Subgroup.centralizer (Z : Set G) :=
    hle.trans (k891xshzw_R891X_le_centralizer L Z n)
  obtain ⟨-, -, -, hbig, -⟩ := hD4 (Bar2 L) n hset.d4
  obtain ⟨-, -, -, hweak⟩ := hbig (barImage L P) hsyl
  have hle' : (ZOf (barImage L P)).map φ.toMonoidHom ≤
      R891X ⊤ (ZOf (barImage L P)) n := by
    rw [k891xshape_zOf_barImage hPL hPp, ← hbarZ]
    calc barImage L (Z.map (MulAut.conj m).toMonoidHom)
        ≤ barImage L (R891X L Z n) :=
          Subgroup.map_mono (Subgroup.subgroupOf_mono L hle)
      _ = R891X ⊤ (barImage L Z) n := k891xshape_barImage_R891X hZL hZp n
  have hweakZ := hweak φ hle'
  have hbar : barImage L (Z.map (MulAut.conj m).toMonoidHom) = barImage L Z := by
    rw [hbarZ, ← k891xshape_zOf_barImage hPL hPp]
    exact hweakZ
  exact k891xshzw_eq_of_barImage_eq hZmL hZL
    (hZpZ.map (MulAut.conj m).toMonoidHom) hZpZ hZcent hbar

private theorem k891xsher_le_of_le_sup_of_isPGroup {G : Type} [Group G]
    {M H N R : Subgroup G} (hHM : H ≤ M) (hNM : N ≤ M) (hRM : R ≤ M)
    [hHnorm : (H.subgroupOf M).Normal]
    (hRHN : R ≤ H ⊔ N) (hR3 : IsPGroup 3 R) (hN2 : IsPGroup 2 N) :
    R ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let q : ↥M →* (↥M ⧸ H.subgroupOf M) := QuotientGroup.mk' _
  have hRNsub : R.subgroupOf M ≤ (H ⊔ N).subgroupOf M :=
    Subgroup.subgroupOf_mono M hRHN
  rw [Subgroup.subgroupOf_sup hHM hNM] at hRNsub
  have hleMap : (R.subgroupOf M).map q ≤ (N.subgroupOf M).map q := by
    refine (Subgroup.map_mono hRNsub).trans (le_of_eq ?_)
    rw [Subgroup.map_sup]
    have hker : (H.subgroupOf M).map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hker, bot_sup_eq]
  have h3 : IsPGroup 3 ((R.subgroupOf M).map q) :=
    (hR3.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm).map q
  have h2 : IsPGroup 2 ((R.subgroupOf M).map q) :=
    ((hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNM).symm).map q).to_le hleMap
  have hd := IsPGroup.disjoint_of_ne 2 3 (by norm_num)
    ((R.subgroupOf M).map q) ((R.subgroupOf M).map q) h2 h3
  have hbot : (R.subgroupOf M).map q = ⊥ := disjoint_self.mp hd
  have hRK : R.subgroupOf M ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hbot
  rw [QuotientGroup.ker_mk'] at hRK
  intro r hr
  exact (Subgroup.mem_subgroupOf.mp (hRK ((Subgroup.mem_subgroupOf (H := R) (K := M)
    (h := (⟨r, hRM hr⟩ : ↥M))).mpr hr)))

private theorem k891xsher_R891X_le_M0 {G : Type} [Group G] [Finite G] (L Z : Subgroup G)
    (n : ℕ) : R891X L Z n ≤ L ⊓ centralizer (Z : Set G) := by
  unfold R891X
  split
  · change CFSG.RankThree.PartOne.pElementSubgroup 2 (L ⊓ centralizer (Z : Set G)) ≤
      L ⊓ centralizer (Z : Set G)
    unfold CFSG.RankThree.PartOne.pElementSubgroup
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  · exact Subgroup.map_subtype_le _

private theorem k891xsher_R891X_normalizer {G : Type} [Group G] [Finite G] (L Z : Subgroup G)
    (n : ℕ) : (L ⊓ centralizer (Z : Set G)) ≤
      Subgroup.normalizer (R891X L Z n : Set G) := by
  intro m hm
  by_cases hn : n = 1
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    unfold R891X
    rw [if_pos hn]
    unfold Opp
    change (CFSG.RankThree.PartOne.pElementSubgroup 2 (L ⊓ centralizer (Z : Set G))).map
        (MulAut.conj m).toMonoidHom =
      CFSG.RankThree.PartOne.pElementSubgroup 2 (L ⊓ centralizer (Z : Set G))
    rw [k891xshape_map_pElementSubgroup_two (MulAut.conj m).toMonoidHom ?_ _]
    · congr 1
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)
    · have hk : (MulAut.conj m).toMonoidHom.ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj m).injective
      rw [hk]
      exact IsPGroup.of_bot
  · unfold R891X
    rw [if_neg hn]
    exact CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains _
      (Subgroup.le_normalizer hm)

private theorem k891xshape_exists_R {G : Type} [Group G] [Finite G] (D : Data G)
    (hD4 : R891D4Core) (L S : Subgroup G) (n : ℕ) (hset : R891Set D L S n)
    (hbasic : R891Basic D L S) :
    ∃ R : Subgroup G, R ≤ R891X L (ZOf (S ⊓ L)) n ∧ R ≤ S ⊓ L ∧
      IsExtraspecialExpP 3 1 ↥R ∧ ZOf (S ⊓ L) ≤ R := by
  let Z : Subgroup G := ZOf (S ⊓ L)
  let M0 : Subgroup G := L ⊓ centralizer (Z : Set G)
  let X : Subgroup G := R891X L Z n
  let πL : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Rbar : Subgroup (Bar2 L) := barImage L (S ⊓ L)
  have hZL : Z ≤ L := inf_le_left.trans inf_le_right
  have hZp : IsPGroup 3 (Z.subgroupOf L) := by
    have hZcard : Nat.card Z = 3 := hbasic.zOrder
    have hZpZ : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZcard]; norm_num)
    exact hZpZ.comap_of_injective L.subtype Subtype.coe_injective
  have hQp : IsPGroup 3 ((S ⊓ L).subgroupOf L) := hbasic.sylowL.isPGroup.comap_subtype
  have hSyl : IsSylowOf 3 Rbar (⊤ : Subgroup (Bar2 L)) :=
    k891xshape_isSylowOf_barImage hbasic.sylowL
  have hZbar : ZOf Rbar = barImage L Z := k891xshape_zOf_barImage inf_le_right hQp
  have hXbar : R891X (⊤ : Subgroup (Bar2 L)) (barImage L Z) n = barImage L X :=
    (k891xshape_barImage_R891X hZL hZp n).symm
  obtain ⟨-, -, -, hbig, -⟩ := hD4 (Bar2 L) n hset.d4
  obtain ⟨-, ⟨Rb, hRbX, hRbP, hRbExtra, hZbarRb⟩, -, -⟩ := hbig Rbar hSyl
  have hRbX' : Rb ≤ barImage L X := by
    rw [← hXbar, ← hZbar]
    exact hRbX
  let Rpre : Subgroup G := (Rb.comap πL).map L.subtype
  let R : Subgroup G := Rpre ⊓ (S ⊓ L)
  have hRpre_L : Rpre ≤ L := Subgroup.map_subtype_le _
  have hR_L : R ≤ L := inf_le_left.trans hRpre_L
  have hRSL : R ≤ S ⊓ L := inf_le_right
  have hSL_cent : S ⊓ L ≤ centralizer (Z : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact inf_le_right
  have hR_M0 : R ≤ M0 := le_inf hR_L (hRSL.trans hSL_cent)
  have hXM0 : X ≤ M0 := k891xsher_R891X_le_M0 L Z n
  let O2L : Subgroup G := (CFSG.pCore 2 ↥L).map L.subtype
  let N1 : Subgroup G := O2L ⊓ M0
  have hN1_2 : IsPGroup 2 N1 :=
    ((CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype).to_le inf_le_left
  have hR_XN : R ≤ X ⊔ N1 := by
    intro r hr
    have hrL : r ∈ L := hR_L hr
    have hrM0 : r ∈ M0 := hR_M0 hr
    have hrpre : r ∈ Rpre := (Subgroup.mem_inf.mp hr).1
    obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp hrpre
    have hyl : y = (⟨r, hrL⟩ : ↥L) := Subtype.ext hyr
    have hπr : πL (⟨r, hrL⟩ : ↥L) ∈ Rb := by
      rw [← hyl]
      exact Subgroup.mem_comap.mp hy
    obtain ⟨x, hx, hxr⟩ :=
      Subgroup.mem_map.mp (hRbX' hπr : πL (⟨r, hrL⟩ : ↥L) ∈ (X.subgroupOf L).map πL)
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hu : x⁻¹ * (⟨r, hrL⟩ : ↥L) ∈ (CFSG.pCore 2 ↥L) := by
      have h1 : x⁻¹ * (⟨r, hrL⟩ : ↥L) ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxr, inv_mul_cancel]
      rwa [QuotientGroup.ker_mk'] at h1
    have huO2 : ((x⁻¹ * (⟨r, hrL⟩ : ↥L) : ↥L) : G) ∈ O2L :=
      Subgroup.mem_map_of_mem L.subtype hu
    have hval : ((x⁻¹ * (⟨r, hrL⟩ : ↥L) : ↥L) : G) = (x : G)⁻¹ * r := by simp
    have huM0 : ((x⁻¹ * (⟨r, hrL⟩ : ↥L) : ↥L) : G) ∈ M0 := by
      rw [hval]
      exact M0.mul_mem (M0.inv_mem (hXM0 hxX)) hrM0
    have huN1 : ((x⁻¹ * (⟨r, hrL⟩ : ↥L) : ↥L) : G) ∈ N1 :=
      Subgroup.mem_inf.mpr ⟨huO2, huM0⟩
    rw [show r = (x : G) * ((x⁻¹ * (⟨r, hrL⟩ : ↥L) : ↥L) : G) by rw [hval]; group]
    exact (X ⊔ N1).mul_mem ((le_sup_left : X ≤ X ⊔ N1) hxX)
      ((le_sup_right : N1 ≤ X ⊔ N1) huN1)
  have hXM0norm : (X.subgroupOf M0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM0).mpr
      (k891xsher_R891X_normalizer L Z n)
  have hR3 : IsPGroup 3 R := hbasic.sylowL.isPGroup.to_le hRSL
  have hRleX : R ≤ X :=
    k891xsher_le_of_le_sup_of_isPGroup (hHnorm := hXM0norm) hXM0 inf_le_right hR_M0
      hR_XN hR3 hN1_2
  have hZR : Z ≤ R := by
    refine le_inf ?_ inf_le_left
    intro z hz
    have hzL : z ∈ L := hZL hz
    have hzZbar : πL (⟨z, hzL⟩ : ↥L) ∈ ZOf Rbar := by
      rw [hZbar]
      exact Subgroup.mem_map.mpr ⟨(⟨z, hzL⟩ : ↥L),
        (Subgroup.mem_subgroupOf (H := Z) (K := L) (h := (⟨z, hzL⟩ : ↥L))).mpr hz, rfl⟩
    exact Subgroup.mem_map_of_mem L.subtype (Subgroup.mem_comap.mpr (hZbarRb hzZbar))
  have hRSLsub : R.subgroupOf L ≤ (S ⊓ L).subgroupOf L := Subgroup.subgroupOf_mono L hRSL
  have hinj : Set.InjOn πL (R.subgroupOf L : Set ↥L) :=
    Set.InjOn.mono hRSLsub (k891xshape_mk_injOn (L := L) (Q := S ⊓ L) hQp)
  have hRpre_sub : Rpre.subgroupOf L = Rb.comap πL := by
    show ((Rb.comap πL).map L.subtype).comap L.subtype = Rb.comap πL
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hRsub_map : (R.subgroupOf L).map πL = Rb := by
    apply le_antisymm
    · refine (Subgroup.map_mono ?_).trans (Subgroup.map_comap_le πL Rb)
      intro x hx
      have hxR : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hx
      have hxpre : x ∈ Rpre.subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hxR).1
      rwa [hRpre_sub] at hxpre
    · intro y hy
      obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp (hRbP hy)
      have hsRpre : s ∈ Rpre.subgroupOf L := by
        rw [hRpre_sub, Subgroup.mem_comap]
        change (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) s ∈ Rb
        rw [hsy]
        exact hy
      refine Subgroup.mem_map.mpr ⟨s, ?_, hsy⟩
      show s ∈ Rpre.subgroupOf L ⊓ (S ⊓ L).subgroupOf L
      exact ⟨hsRpre, hs⟩
  let f : ↥(R.subgroupOf L) →* ↥Rb :=
    (πL.comp (R.subgroupOf L).subtype).codRestrict Rb
      (fun x => hRsub_map ▸ Subgroup.mem_map_of_mem πL x.2)
  have hf_inj : Function.Injective f := by
    intro a b hab
    refine Subtype.ext (hinj a.2 b.2 ?_)
    simpa [f] using Subtype.ext_iff.mp hab
  have hf_surj : Function.Surjective f := by
    intro y
    have hy' : (y : Bar2 L) ∈ (R.subgroupOf L).map πL := by
      rw [hRsub_map]
      exact y.2
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy'
    exact ⟨⟨s, hs⟩, Subtype.ext (by simpa [f] using hsy)⟩
  have e0 : ↥(R.subgroupOf L) ≃* ↥Rb := MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have e : ↥R ≃* ↥Rb := (Subgroup.subgroupOfEquivOfLe hR_L).symm.trans e0
  exact ⟨R, hRleX, hRSL, k891xshape_extra_of_mulEquiv e.symm hRbExtra, hZR⟩

theorem s891_x_shape
    {G : Type} [Group G] [Finite G] (D : Data G)
    (L S : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S) :
    ∃ R : Subgroup G, R891XShape D L S n R := by
  have hD4 := r891D4Core_holds
  obtain ⟨R, hRle, hRsyl, hRext, hZR⟩ := k891xshape_exists_R D hD4 L S n hset hbasic
  exact ⟨R, hRle, hRsyl, hRext, hZR, k891xshape_xShape D L S n hset hbasic,
    k891xshape_zWeak D hD4 L S n hset hbasic⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
