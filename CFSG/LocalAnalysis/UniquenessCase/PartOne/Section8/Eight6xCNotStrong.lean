module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsAlt KStrongEmbedded72)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (QuotK7 R72 Sec7Hyp)

@[expose] def KF7Dichotomy {G : Type} [Group G] [Finite G] (D : Data G) (p : ℕ)
    (H : Subgroup G) : Prop :=
  Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) ∨
    (p = 5 ∧ ∀ Y : Subgroup (QuotK7 p H),
      Y ≤ ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) →
      ⁅Y, Y⁆ = Y → ∀ (S : Type) [Group S], IsSimpleGroup S →
        ∀ f : ↥Y →* S, Function.Surjective f → IsAlt S 5)

private theorem k1471s1_imageModK_opp_normal {G : Type} [Group G] [Finite G] {p : ℕ}
    {H : Subgroup G} : (UC22.F07.ImageModK p H (UC22.Opp p H)).Normal := by
  have hOppH : ((UC22.Opp p H).subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (UC22.Opp p H : Set G) :=
      UC6.mem_normalizer_Opp_uc6 (Subgroup.le_normalizer g.2) p
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have h := hOppH.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    (QuotientGroup.mk'_surjective _)
  simpa [UC22.F07.ImageModK] using h

theorem kf7Dichotomy_of_r72 {G : Type} [Group G] [Finite G] {D : Data G}
    (h72 : R72 D) (hKF7 : KStrongEmbedded72) {p : ℕ} {H : Subgroup G}
    (h : Sec7Hyp D p H) : KF7Dichotomy D p H := by
  classical
  have h72' := UC22.r72Shape_of_r72 h72 h
  obtain ⟨hp, hp2, hM, -, hHM, hrank⟩ := h
  have hrankH : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M) := by omega
  have hNstrong : IsStronglyPEmbedded p
      (((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) :=
    UC6.R869S.isStronglyPEmbedded_map_quotient_pPrimeCore hp hM hHM hrankH
  have hOp : CFSG.pPrimeCore p (QuotK7 p H) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hKF := hKF7 p hp hp2 (QuotK7 p H) hOp
    (UC22.F07.ImageModK p H (UC22.Opp p H)) k1471s1_imageModK_opp_normal h72'.1 h72'.2
    (((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) hNstrong
  rcases hKF with hsol | ⟨hp5, -, hquot⟩
  · exact Or.inl hsol
  · refine Or.inr ⟨hp5, ?_⟩
    intro Y hY hYperf S hGrp hS f hf
    exact @hquot Y hY hYperf S hGrp hS f hf

private theorem k1471s2_pCoreOf_le {G : Type} [Group G] (q : ℕ) (H : Subgroup G) :
    pCoreOf q H ≤ H :=
  Subgroup.map_subtype_le _

open scoped commutatorElement in
private theorem k1471s2_mem_coset {G : Type} [Group G] {L X : Subgroup G}
    (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L) {y x o : G} (hy : y ∈ L) (hx : x ∈ X)
    (ho : o ∈ pCoreOf 2 L) : y⁻¹ * (x * (y * o) * x⁻¹) ∈ pCoreOf 2 L := by
  have h1 : ⁅y⁻¹, x⁆ ∈ pCoreOf 2 L :=
    hLX (Subgroup.commutator_mem_commutator (L.inv_mem hy) hx)
  have h2 : ⁅o, x⁆ ∈ pCoreOf 2 L :=
    hLX (Subgroup.commutator_mem_commutator (k1471s2_pCoreOf_le 2 L ho) hx)
  have h3 : y⁻¹ * (x * (y * o) * x⁻¹) = ⁅y⁻¹, x⁆ * (⁅o, x⁆⁻¹ * o) := by
    simp only [commutatorElement_def]
    group
  rw [h3]
  exact (pCoreOf 2 L).mul_mem h1 ((pCoreOf 2 L).mul_mem ((pCoreOf 2 L).inv_mem h2) ho)

private theorem k1471s2_exists_fixed {G : Type} [Group G] [Finite G] {L X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : IsPGroup p X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L) {y : G}
    (hy : y ∈ L) : ∃ o ∈ pCoreOf 2 L, ∀ x ∈ X, x * (y * o) * x⁻¹ = y * o := by
  have : Fact p.Prime := ⟨hp⟩
  have hO2 : IsPGroup 2 (pCoreOf 2 L) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
  have hnd : ¬ p ∣ Nat.card (pCoreOf 2 L) := by
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  let _ : MulAction X (pCoreOf 2 L) :=
    { smul := fun x o =>
        ⟨y⁻¹ * ((x : G) * (y * (o : G)) * (x : G)⁻¹), k1471s2_mem_coset hLX hy x.2 o.2⟩
      one_smul := fun o => Subtype.ext (by
        change y⁻¹ * (((1 : X) : G) * (y * (o : G)) * ((1 : X) : G)⁻¹) = (o : G)
        simp)
      mul_smul := fun a b o => Subtype.ext (by
        change y⁻¹ * (((a * b : X) : G) * (y * (o : G)) * ((a * b : X) : G)⁻¹) =
          y⁻¹ * ((a : G) * (y * (y⁻¹ * ((b : G) * (y * (o : G)) * (b : G)⁻¹))) * (a : G)⁻¹)
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  obtain ⟨⟨o, ho⟩, hfix⟩ := hX.nonempty_fixed_point_of_prime_not_dvd_card (pCoreOf 2 L) hnd
  refine ⟨o, ho, fun x hx => ?_⟩
  have h := congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hfix) ⟨x, hx⟩)
  change y⁻¹ * (x * (y * o) * x⁻¹) = o at h
  calc x * (y * o) * x⁻¹ = y * (y⁻¹ * (x * (y * o) * x⁻¹)) := by group
    _ = y * o := by rw [h]

theorem eq_inf_centralizer_sup_pCore_of_commutator_le {G : Type} [Group G] [Finite G]
    {L X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hX : IsPGroup p X)
    (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L) : L = (centralizer (X : Set G) ⊓ L) ⊔ pCoreOf 2 L := by
  refine le_antisymm (fun y hy => ?_) (sup_le inf_le_right (k1471s2_pCoreOf_le 2 L))
  obtain ⟨o, ho, hfix⟩ := k1471s2_exists_fixed hp hp2 hX hLX hy
  have hyo : y * o ∈ centralizer (X : Set G) ⊓ L := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_,
      L.mul_mem hy (k1471s2_pCoreOf_le 2 L ho)⟩
    exact (mul_inv_eq_iff_eq_mul.mp (hfix x hx))
  have h := Subgroup.mul_mem_sup hyo ((pCoreOf 2 L).inv_mem ho)
  simpa using h

private theorem k1471s3_surjective {G : Type} [Group G] {L C : Subgroup G} (hCL : C ≤ L)
    (hL : L = C ⊔ pCoreOf 2 L) :
    Function.Surjective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hCL)) := by
  have hsup : C.subgroupOf L ⊔ CFSG.pCore 2 ↥L = ⊤ := by
    have h := congrArg (fun K : Subgroup G => K.subgroupOf L) hL.symm
    simp only [Subgroup.subgroupOf_self] at h
    rwa [Subgroup.subgroupOf_sup hCL (k1471s2_pCoreOf_le 2 L), CFSG.openPCoreOf_subgroupOf] at h
  have hbot : (CFSG.pCore 2 ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' _).symm)
  have hmap : (C.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) hsup
    rwa [Subgroup.map_sup, hbot, sup_bot_eq, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h
  intro b
  have hb : b ∈ (C.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [hmap]
    exact Subgroup.mem_top b
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hb
  exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩

private theorem k1471s3_ker_isPGroup {G : Type} [Group G] {L C : Subgroup G} (hCL : C ≤ L) :
    IsPGroup 2 ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hCL)).ker := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact CFSG.pCore_isPGroup.comap_of_injective _ (Subgroup.inclusion_injective hCL)

private theorem k1471s3_image_elemAbelian {G : Type} [Group G] {L E : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hEL : E ≤ L) (hEel : IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) :
    IsElemAbelian r ((E.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ∧
      Nat.card ((E.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = r ^ 2 := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint (E.subgroupOf L) (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker := by
    rw [QuotientGroup.ker_mk']
    exact IsPGroup.disjoint_of_ne r 2 hr2 _ _ (hEel.subgroupOf L).isPGroup CFSG.pCore_isPGroup
  refine ⟨(hEel.subgroupOf L).map _, ?_⟩
  rw [UC6S846.card_map_of_disjoint_ker _ _ hdisj, ← hEcard]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv

theorem two_le_pRank_inf_centralizer_of_eq_sup {G : Type} [Group G] [Finite G] {L X : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hL : L = (centralizer (X : Set G) ⊓ L) ⊔ pCoreOf 2 L) (h1 : 1 < CFSG.Open.pRank r L) :
    2 ≤ CFSG.Open.pRank r (centralizer (X : Set G) ⊓ L) := by
  have hCL : centralizer (X : Set G) ⊓ L ≤ L := inf_le_right
  obtain ⟨E, hEL, hEel, hEcard⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hr (k := 2) h1
  obtain ⟨hEb, hcard⟩ := k1471s3_image_elemAbelian hr hr2 hEL hEel hEcard
  obtain ⟨Q, -, hQmap, hQdisj⟩ := UC6S846.exists_lift_pGroup
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hCL))
    (k1471s3_surjective hCL hL) (k1471s3_ker_isPGroup hCL) hr hr2 _ hEb.isPGroup
  have hQel : IsElemAbelian r Q :=
    UC6S846.isElemAbelian_of_disjoint_ker _ Q hQdisj (by rw [hQmap]; exact hEb)
  have hQcard : Nat.card Q = r ^ 2 := by
    rw [← UC6S846.card_map_of_disjoint_ker _ Q hQdisj, hQmap, hcard]
  refine UC6S846.le_pRank' hr (E := Q.map (centralizer (X : Set G) ⊓ L).subtype)
    (Subgroup.map_subtype_le Q) (hQel.map _) ?_
  rw [Subgroup.card_map_of_injective (centralizer (X : Set G) ⊓ L).subtype_injective, hQcard]

private theorem k1471s4_centralizer_ne_top {G : Type} [Group G] [Finite G] {D : Data G}
    {X : Subgroup G} (hcard : Nat.card X = 3) : centralizer (X : Set G) ≠ ⊤ := by
  have : IsSimpleGroup G := D.standing.simple
  have hX1 : 1 < Nat.card X := by
    rw [hcard]
    norm_num
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot X).mp hX1)
  refine fun htop => CFSG.RankThree.PartOne.centralizer_singleton_ne_top_of_simple
    D.standing.nonab (fun h => hx1 (OneMemClass.coe_eq_one.mp h)) (eq_top_iff.mpr ?_)
  rw [← htop]
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x.2)

private theorem k1471s4_one_lt_pRank {G : Type} [Group G] [Finite G] {L M X : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hLM : L ≤ M)
    (hrk : 2 ≤ CFSG.Open.pRank r (centralizer (X : Set G) ⊓ L)) :
    1 < CFSG.Open.pRank r (centralizer (X : Set G) ⊓ M) := by
  obtain ⟨E, hEC, hEel, hEcard⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hr hrk
  have h := UC6S846.le_pRank' hr (H := centralizer (X : Set G) ⊓ M) (E := E)
    (hEC.trans (inf_le_inf_left _ hLM)) hEel hEcard
  omega

theorem sec7Hyp_centralizer_of_choiceX {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hM : IsStronglyPEmbedded r D.M)
    (hrk : 2 ≤ CFSG.Open.pRank r (centralizer (X : Set G) ⊓ L)) :
    Sec7Hyp D r (centralizer (X : Set G)) :=
  ⟨hr, by omega, hM, k1471s4_centralizer_ne_top (D := D) hX.card, hX.notLe,
    k1471s4_one_lt_pRank hr (CFSG.Open.IsSubnormal.le hX.cex.mem.1) hrk⟩

private theorem k1471s5_exists_perfect {A B : Type} [Group A] [Finite A] [Group B]
    [Group.IsPerfect B] {ρ : A →* B} (hρ : Function.Surjective ρ) :
    ∃ P : Subgroup A, ⁅P, P⁆ = P ∧ P.map ρ = ⊤ := by
  have hstab : ∃ n, derivedSeries A (n + 1) = derivedSeries A n := by
    obtain ⟨x, y, hxy, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => derivedSeries A n)
    rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
    · exact ⟨x, le_antisymm (derivedSeries_antitone A (Nat.le_succ x))
        (h.le.trans (derivedSeries_antitone A hlt))⟩
    · exact ⟨y, le_antisymm (derivedSeries_antitone A (Nat.le_succ y))
        (h.symm.le.trans (derivedSeries_antitone A hlt))⟩
  obtain ⟨n, hn⟩ := hstab
  refine ⟨derivedSeries A n, ?_, ?_⟩
  · rw [← derivedSeries_succ]
    exact hn
  · rw [map_derivedSeries_eq hρ, Group.IsPerfect.derivedSeries_eq_top]

private theorem k1471s5_card_dvd {A B : Type} [Group A] [Group B] (ρ : A →* B) (S : Subgroup A)
    (hS : S.map ρ = ⊤) : Nat.card B ∣ Nat.card S :=
  Subgroup.card_dvd_of_surjective (f := ρ.domRestrict S)
    (MonoidHom.range_eq_top.mp (by rw [MonoidHom.domRestrict_range, hS]))

private theorem k1471s5_solvable_false {A U B : Type} [Group A] [Group U] [Group B] {r : ℕ}
    {Q : Subgroup A} (hQ : ⁅Q, Q⁆ = Q) {φ : A →* U} {Nb : Subgroup U} (hQN : Q.map φ ≤ Nb)
    {ρ : A →* B} (hρ : Q.map ρ = ⊤) (hB : r ∣ Nat.card B) (hker : ¬ r ∣ Nat.card φ.ker)
    (hsolv : Group.IsSolvable ↥Nb) : False := by
  have hbot : Q.map φ = ⊥ := by
    by_contra hne
    have hY : ⁅Q.map φ, Q.map φ⁆ = Q.map φ := by rw [← Subgroup.map_commutator, hQ]
    have : Group.IsPerfect ↥(Q.map φ) := Subgroup.isPerfect_iff.mpr hY
    have : Group.IsSolvable ↥(Q.map φ) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hQN)
    have : Nontrivial ↥(Q.map φ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable ↥(Q.map φ) inferInstance
  have hQk : Q ≤ φ.ker := (Subgroup.map_eq_bot_iff Q).mp hbot
  have hmap : (φ.ker).map ρ = ⊤ := by
    rw [eq_top_iff, ← hρ]
    exact Subgroup.map_mono hQk
  exact hker (hB.trans (k1471s5_card_dvd ρ φ.ker hmap))

private theorem k1471s5_exists_surjective {A U B : Type} [Group A] [Group U] [Group B] {r : ℕ}
    {Q : Subgroup A} {φ : A →* U} {ρ : A →* B} (hρ : Q.map ρ = ⊤) (hB : r ∣ Nat.card B)
    (hker : ¬ r ∣ Nat.card φ.ker) (hS : IsSimpleGroup B) :
    ∃ f : ↥(Q.map φ) →* B, Function.Surjective f := by
  have hmemQ : ∀ b : B, ∃ q ∈ Q, ρ q = b := fun b => by
    have hb : b ∈ Q.map ρ := by
      rw [hρ]
      exact Subgroup.mem_top b
    exact Subgroup.mem_map.mp hb
  have hnorm : ((Q ⊓ φ.ker).map ρ).Normal := by
    refine ⟨fun b hb g => ?_⟩
    obtain ⟨t, ht, rfl⟩ := hb
    obtain ⟨s, hs, rfl⟩ := hmemQ g
    refine ⟨s * t * s⁻¹, ⟨Q.mul_mem (Q.mul_mem hs ht.1) (Q.inv_mem hs), ?_⟩, by simp⟩
    have h : φ t = 1 := ht.2
    simp [h]
  have hbot : (Q ⊓ φ.ker).map ρ = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal ((Q ⊓ φ.ker).map ρ) with h | h
    · exact h
    · exact (hker (hB.trans ((k1471s5_card_dvd ρ _ h).trans
        (Subgroup.card_dvd_of_le inf_le_right)))).elim
  have hT : ∀ q ∈ Q, φ q = 1 → ρ q = 1 := fun q hq hφ =>
    Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_map_of_mem ρ (Subgroup.mem_inf.mpr ⟨hq, hφ⟩))
  have hg : Function.Surjective (φ.subgroupMap Q) := φ.subgroupMap_surjective Q
  have hle : (φ.subgroupMap Q).ker ≤ (ρ.domRestrict Q).ker := fun q hq =>
    MonoidHom.mem_ker.mpr (hT q q.2 (congrArg Subtype.val (MonoidHom.mem_ker.mp hq)))
  refine ⟨(φ.subgroupMap Q).liftOfSurjective hg ⟨ρ.domRestrict Q, hle⟩, fun b => ?_⟩
  obtain ⟨q, hq, rfl⟩ := hmemQ b
  exact ⟨φ.subgroupMap Q ⟨q, hq⟩, MonoidHom.liftOfRightInverse_comp_apply _ _ _
    ⟨ρ.domRestrict Q, hle⟩ ⟨q, hq⟩⟩

private theorem k1471s5_not_dvd_ker {C H : Type} [Group C] [Group H] [Finite H] {r : ℕ}
    (hr : r.Prime) {ι : C →* H} (hι : Function.Injective ι) :
    ¬ r ∣ Nat.card ((QuotientGroup.mk' (CFSG.pPrimeCore r H)).comp ι).ker := by
  have : Fact r.Prime := ⟨hr⟩
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact fun h => (hr.coprime_iff_not_dvd.mp CFSG.pPrimeCore_coprime_card)
    (h.trans (Subgroup.card_comap_dvd_of_injective _ ι hι))

private theorem k1471s5_sq_dvd_card_bar2 {G : Type} [Group G] [Finite G] {L : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (h1 : 1 < CFSG.Open.pRank r L) :
    r ^ 2 ∣ Nat.card (Bar2 L) := by
  obtain ⟨E, hEL, hEel, hEcard⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hr (k := 2) h1
  obtain ⟨-, hcard⟩ := k1471s3_image_elemAbelian hr hr2 hEL hEel hEcard
  rw [← hcard]
  exact Subgroup.card_subgroup_dvd_card _

theorem false_of_kf7Dichotomy_of_choiceX {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hS : IsSimpleGroup (Bar2 L)) {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (h1 : 1 < CFSG.Open.pRank r L)
    (hL : L = (centralizer (X : Set G) ⊓ L) ⊔ pCoreOf 2 L)
    (hdich : KF7Dichotomy D r (centralizer (X : Set G))) : False := by
  have hr2 : r ≠ 2 := by omega
  have hLM : L ≤ D.M := CFSG.Open.IsSubnormal.le hX.cex.mem.1
  have hCL : centralizer (X : Set G) ⊓ L ≤ L := inf_le_right
  have hCH : centralizer (X : Set G) ⊓ L ≤ centralizer (X : Set G) := inf_le_left
  have : Group.IsPerfect (Bar2 L) := ⟨hX.cex.mem.2.2.1⟩
  obtain ⟨Y, hY, hYtop⟩ := k1471s5_exists_perfect (k1471s3_surjective hCL hL)
  have hB : r ^ 2 ∣ Nat.card (Bar2 L) := k1471s5_sq_dvd_card_bar2 hr hr2 h1
  have hker := k1471s5_not_dvd_ker hr (Subgroup.inclusion_injective hCH)
  have hYN : Y.map ((QuotientGroup.mk' (CFSG.pPrimeCore r ↥(centralizer (X : Set G)))).comp
        (Subgroup.inclusion hCH)) ≤
      ((centralizer (X : Set G) ⊓ D.M).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore r ↥(centralizer (X : Set G)))) := by
    rintro _ ⟨p, -, rfl⟩
    exact ⟨Subgroup.inclusion hCH p, Subgroup.mem_subgroupOf.mpr ⟨p.2.1, hLM p.2.2⟩, rfl⟩
  rcases hdich with hsolv | ⟨hr5, hquot⟩
  · exact k1471s5_solvable_false hY hYN hYtop ((dvd_pow_self r two_ne_zero).trans hB) hker hsolv
  · obtain ⟨f, hf⟩ := k1471s5_exists_surjective hYtop ((dvd_pow_self r two_ne_zero).trans hB)
      hker hS
    have hperf : ⁅Y.map ((QuotientGroup.mk' (CFSG.pPrimeCore r ↥(centralizer (X : Set G)))).comp
        (Subgroup.inclusion hCH)), Y.map ((QuotientGroup.mk' (CFSG.pPrimeCore r
          ↥(centralizer (X : Set G)))).comp (Subgroup.inclusion hCH))⁆ =
        Y.map ((QuotientGroup.mk' (CFSG.pPrimeCore r ↥(centralizer (X : Set G)))).comp
          (Subgroup.inclusion hCH)) := by
      rw [← Subgroup.map_commutator, hY]
    obtain ⟨e⟩ := hquot _ hYN hperf (Bar2 L) hS f hf
    subst hr5
    have hcard : Nat.card (Bar2 L) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hcard] at hB
    norm_num at hB

theorem not_stronglyEmbedded_of_choiceX_of_leaves {G : Type} [Group G] [Finite G]
    {D : Data G}
    (h72 : R72 D) (hKF7 : KStrongEmbedded72) {L Q P X : Subgroup G}
    (hX : ChoiceX D L Q P X) (hLX : ⁅L, X⁆ ≤ pCoreOf 2 L) (hS : IsSimpleGroup (Bar2 L)) {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (h1 : 1 < CFSG.Open.pRank r L) :
    ¬ IsStronglyPEmbedded r D.M := by
  intro hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hX.card)
  have hL := eq_inf_centralizer_sup_pCore_of_commutator_le Nat.prime_three (by norm_num) hX3 hLX
  have hrk := two_le_pRank_inf_centralizer_of_eq_sup hr (by omega) hL h1
  have hSec := sec7Hyp_centralizer_of_choiceX hX hr hr3 hM hrk
  exact false_of_kf7Dichotomy_of_choiceX hX hS hr hr3 h1 hL (kf7Dichotomy_of_r72 h72 hKF7 hSec)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
