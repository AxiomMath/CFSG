module

public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Catalog
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.Milestones.LC_GL_local_rank_bounds
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree

open CFSG CFSG.RankThree.LocalRank CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped Pointwise

@[expose] noncomputable def mulAutQuotientHom {L : Type*} [Group L] (M : Subgroup L)
    [M.Characteristic] : MulAut L →* MulAut (L ⧸ M) where
  toFun φ := QuotientGroup.congr M M φ (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem mulAutQuotientHom_mk {L : Type*} [Group L] (M : Subgroup L) [M.Characteristic]
    (φ : MulAut L) (l : L) : mulAutQuotientHom M φ (l : L ⧸ M) = ((φ l : L) : L ⧸ M) :=
  rfl

variable {G : Type*} [Group G] [Finite G]

theorem three_not_dvd_card_aschbacherSolvableCore :
    ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 G) :=
  (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1

theorem injOn_mk_of_isPGroup {p : ℕ} (hp : p.Prime) {A : Subgroup G} (hA : IsPGroup p A) :
    Set.InjOn (QuotientGroup.mk' (aschbacherSolvableCore p G)) (A : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  have hdisj : Disjoint A (aschbacherSolvableCore p G) := Subgroup.disjoint_of_coprime_natCard (by
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2
      (solvable_prime_complement_core_characterization hp).2.2.1))
  intro x hx y hy hxy
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
  have hmem : x⁻¹ * y ∈ A ⊓ aschbacherSolvableCore p G := ⟨A.mul_mem (A.inv_mem hx) hy, hxy⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
  exact eq_of_inv_mul_eq_one hmem

theorem localRank_eq_pRank_of_even_kernel {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (N : Subgroup G)
    [N.Normal] (hN : ¬ r ∣ Nat.card N) (heven : Even (Nat.card N)) :
    localRank r G = CFSG.pRank r G ∧ CFSG.pRank r G = CFSG.pRank r (G ⧸ N) := by
  obtain ⟨h1, h2⟩ := CFSG.RankThree.Classical2.localRank_eq_pRank_of_even hr hr2 N hN heven
  have e1 : CFSG.pRank r G = CFSG.Assembly.pRank r (⊤ : Subgroup G) :=
    CFSG.SectionRank.pRank_eq_open_pRank_top r G
  have e2 : CFSG.pRank r (G ⧸ N) = CFSG.Assembly.pRank r (⊤ : Subgroup (G ⧸ N)) :=
    CFSG.SectionRank.pRank_eq_open_pRank_top r (G ⧸ N)
  exact ⟨h1.trans e1.symm, e1.trans (h2.trans e2.symm)⟩

theorem theta_quotient_core_and_ranks :
    aschbacherSolvableCore 3 (G ⧸ aschbacherSolvableCore 3 G) = ⊥ ∧
    (∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (aschbacherSolvableCore 3 G) →
      CFSG.pRank r (G ⧸ aschbacherSolvableCore 3 G) = CFSG.pRank r G ∧
      localRank r (G ⧸ aschbacherSolvableCore 3 G) ≤ localRank r G ∧
      (Even (Nat.card (aschbacherSolvableCore 3 G)) →
        localRank r G = CFSG.pRank r G ∧
          CFSG.pRank r G = CFSG.pRank r (G ⧸ aschbacherSolvableCore 3 G))) ∧
    (CFSG.pRank 3 (G ⧸ aschbacherSolvableCore 3 G) = CFSG.pRank 3 G ∧
      localRank 3 (G ⧸ aschbacherSolvableCore 3 G) ≤ localRank 3 G ∧
      (Even (Nat.card (aschbacherSolvableCore 3 G)) →
        localRank 3 G = CFSG.pRank 3 G ∧
          CFSG.pRank 3 G = CFSG.pRank 3 (G ⧸ aschbacherSolvableCore 3 G))) ∧
    (IsPGroup 2 (aschbacherSolvableCore 3 G) →
      evenRank (G ⧸ aschbacherSolvableCore 3 G) ≤ evenRank G ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 →
        localRank r (G ⧸ aschbacherSolvableCore 3 G) ≤ localRank r G) := by
  set N := aschbacherSolvableCore 3 G
  have hranks : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card N →
      CFSG.pRank r (G ⧸ N) = CFSG.pRank r G ∧ localRank r (G ⧸ N) ≤ localRank r G ∧
      (Even (Nat.card N) →
        localRank r G = CFSG.pRank r G ∧ CFSG.pRank r G = CFSG.pRank r (G ⧸ N)) :=
    fun r hr hr2 hN =>
      ⟨CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr N hN,
        CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 N hN,
        localRank_eq_pRank_of_even_kernel hr hr2 N hN⟩
  have htwo : IsPGroup 2 N → ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card N := by
    intro h2 r hr hr2 hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [hk] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  refine ⟨(solvable_prime_complement_core_quotient_centralizers Nat.prime_three N
      (solvable_prime_complement_core_characterization Nat.prime_three).1
      three_not_dvd_card_aschbacherSolvableCore).2.2.1, hranks,
    hranks 3 Nat.prime_three (by norm_num) three_not_dvd_card_aschbacherSolvableCore,
    fun h2 => ⟨?_, fun r hr hr2 => (hranks r hr hr2 (htwo h2 r hr hr2)).2.1⟩⟩
  apply csSup_le'
  rintro k ⟨r, H, hr, hr2, hH, rfl⟩
  calc CFSG.Assembly.pRank r H ≤ localRank r (G ⧸ N) :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr H hH
    _ ≤ localRank r G := (hranks r hr hr2 (htwo h2 r hr hr2)).2.1
    _ ≤ evenRank G := ((CFSG.Milestones.lc_gl_local_rank_bounds G).1 r hr hr2).2

theorem theta_quotient_isKGroupCat {G : Type} [Group G] (hG : CFSG.SectionRank.IsKGroupCat G) :
    CFSG.SectionRank.IsKGroupCat (G ⧸ aschbacherSolvableCore 3 G) :=
  hG.quotient _

theorem theta_quotient_isKGroup {G : Type} [Group G] (hG : CFSG.IsKGroup G) :
    CFSG.IsKGroup (G ⧸ aschbacherSolvableCore 3 G) :=
  hG.quotient _

theorem theta_quotient_three_subgroups :
    (∀ A : Subgroup G, IsPGroup 3 A →
      Set.InjOn (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) (A : Set G)) ∧
    (pCore 3 G).map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤
      pCore 3 (G ⧸ aschbacherSolvableCore 3 G) ∧
    Set.InjOn (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) (pCore 3 G : Set G) ∧
    (pCore 3 G ≠ ⊥ → pCore 3 (G ⧸ aschbacherSolvableCore 3 G) ≠ ⊥) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := QuotientGroup.mk' (aschbacherSolvableCore 3 G)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three (pCore_isPGroup (p := 3) (G := G))
  have hle : (pCore 3 G).map ρ ≤ pCore 3 (G ⧸ aschbacherSolvableCore 3 G) := by
    have : (pCore 3 G).Normal := pCore_normal
    exact le_sSup ⟨this.map ρ (QuotientGroup.mk'_surjective _),
      (pCore_isPGroup (p := 3) (G := G)).map ρ⟩
  refine ⟨fun A hA => injOn_mk_of_isPGroup Nat.prime_three hA, hle, hinj, fun hne hbot => hne ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hx1 : ρ x ∈ pCore 3 (G ⧸ aschbacherSolvableCore 3 G) :=
    hle (Subgroup.mem_map_of_mem ρ hx)
  rw [hbot, Subgroup.mem_bot] at hx1
  exact Subgroup.mem_bot.mpr (hinj hx (pCore 3 G).one_mem (by rw [hx1, map_one]))

theorem mem_normalizer_iff_mk_mem_normalizer {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hL : L ∈ thetaComponents p G) (g : G) :
    g ∈ Subgroup.normalizer (L : Set G) ↔
      QuotientGroup.mk' (aschbacherSolvableCore p G) g ∈
        Subgroup.normalizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) :
          Subgroup (G ⧸ aschbacherSolvableCore p G)) : Set (G ⧸ aschbacherSolvableCore p G)) := by
  set ρ := QuotientGroup.mk' (aschbacherSolvableCore p G)
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := G) hp
  obtain ⟨-, hequiv⟩ := theta_component_quotient_correspondence_equivariant (H := G) hp
  have hτ : ∀ h : G, MulAut.conj (ρ g) (ρ h) = ρ (MulAut.conj g h) := fun h => by
    simp only [MulAut.conj_apply, map_mul, map_inv]
  obtain ⟨hσL, hσLK⟩ := (hequiv (MulAut.conj g) (MulAut.conj (ρ g)) hτ).1 L hL
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.mem_normalizer_iff_map_conj_eq]
  change L.map (MulAut.conj g).toMonoidHom = L ↔
    (L.map ρ).map (MulAut.conj (ρ g)).toMonoidHom = L.map ρ
  rw [← hσLK]
  exact ⟨fun h => by rw [h], fun h => hbij.injOn hσL hL h⟩

theorem theta_component_quotient_structure {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hL : L ∈ thetaComponents p G) :
    inSubgroup (aschbacherSolvableCore p) L = L ⊓ aschbacherSolvableCore p G ∧
    IsComponent (L.map (QuotientGroup.mk' (aschbacherSolvableCore p G))) ∧
    (∃ η : (L ⧸ aschbacherSolvableCore p L) ≃*
        L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)),
      ∀ l : L, (η (l : L ⧸ aschbacherSolvableCore p L) : G ⧸ aschbacherSolvableCore p G) =
        QuotientGroup.mk' (aschbacherSolvableCore p G) (l : G)) ∧
    (Subgroup.normalizer (L : Set G)).map (QuotientGroup.mk' (aschbacherSolvableCore p G)) =
      Subgroup.normalizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) :
        Subgroup (G ⧸ aschbacherSolvableCore p G)) : Set (G ⧸ aschbacherSolvableCore p G)) ∧
    ((QuotientGroup.mk' (aschbacherSolvableCore p G)).domRestrict
        (Subgroup.normalizer (L : Set G))).ker =
      (aschbacherSolvableCore p G).subgroupOf (Subgroup.normalizer (L : Set G)) ∧
    Subgroup.normalizer (L : Set G) =
      (Subgroup.normalizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) :
        Subgroup (G ⧸ aschbacherSolvableCore p G)) : Set (G ⧸ aschbacherSolvableCore p G))).comap
        (QuotientGroup.mk' (aschbacherSolvableCore p G)) ∧
    aschbacherSolvableCore p G ≤ Subgroup.normalizer (L : Set G) ∧
    (∀ g : G, (g ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L,
        (g * l * g⁻¹) • (inSubgroup (aschbacherSolvableCore p) L : Set G) =
          l • (inSubgroup (aschbacherSolvableCore p) L : Set G)) ↔
      QuotientGroup.mk' (aschbacherSolvableCore p G) g ∈
        Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) :
          Subgroup (G ⧸ aschbacherSolvableCore p G)) : Set (G ⧸ aschbacherSolvableCore p G))) ∧
    Function.Surjective ((QuotientGroup.mk' (Subgroup.center
        (L.map (QuotientGroup.mk' (aschbacherSolvableCore p G))))).comp
        ((QuotientGroup.mk' (aschbacherSolvableCore p G)).subgroupMap L)) ∧
    (∀ l : L, (QuotientGroup.mk' (Subgroup.center
        (L.map (QuotientGroup.mk' (aschbacherSolvableCore p G))))).comp
        ((QuotientGroup.mk' (aschbacherSolvableCore p G)).subgroupMap L) l = 1 ↔
      (l : G) ∈ {g : G | g ∈ L ∧ QuotientGroup.mk' (aschbacherSolvableCore p G) g ∈
        (Subgroup.center (L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)))).map
          (L.map (QuotientGroup.mk' (aschbacherSolvableCore p G))).subtype}) ∧
    ∀ A : Subgroup G, A ≤ Subgroup.normalizer (L : Set G) ↔
      A.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) ≤
        Subgroup.normalizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) :
          Subgroup (G ⧸ aschbacherSolvableCore p G)) : Set (G ⧸ aschbacherSolvableCore p G)) := by
  set N := aschbacherSolvableCore p G
  set ρ := QuotientGroup.mk' N
  set K := L.map ρ
  have hM := solvable_prime_complement_core_subnormal_intersection hp hL.2.1
  have hnorm : Subgroup.normalizer (L : Set G) = (Subgroup.normalizer (K : Set (G ⧸ N))).comap ρ :=
    Subgroup.ext fun g => mem_normalizer_iff_mk_mem_normalizer hp hL g
  have hNle : N ≤ Subgroup.normalizer (L : Set G) := by
    rw [hnorm]
    intro n hn
    rw [Subgroup.mem_comap, show ρ n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact Subgroup.one_mem _
  refine ⟨hM, isComponent_map_of_mem_thetaComponents hp hL,
    exists_thetaQuotient_mulEquiv_map hp hL.2.1, ?_, ?_, hnorm, hNle, ?_, ?_, ?_, ?_⟩
  · rw [hnorm, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]
  · rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  · intro g
    constructor
    · rintro ⟨-, hg⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨l, hl, rfl⟩
      have h := (leftCoset_eq_iff (s := inSubgroup (aschbacherSolvableCore p) L)).mp (hg l hl)
      rw [hM] at h
      have h' : ρ (g * l * g⁻¹) = ρ l := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        exact h.2
      rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul] at h'
      exact h'.symm
    · intro hg
      have hgn : g ∈ Subgroup.normalizer (L : Set G) := by
        rw [hnorm, Subgroup.mem_comap]
        exact Subgroup.centralizer_le_normalizer _ hg
      refine ⟨hgn, fun l hl => ?_⟩
      rw [leftCoset_eq_iff, hM]
      have hgl : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgn l).mp hl
      have hc := Subgroup.mem_centralizer_iff.mp hg (ρ l) (Subgroup.mem_map_of_mem ρ hl)
      have h1 : ρ g * ρ l * (ρ g)⁻¹ = ρ l := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hc.symm
      have hmem : (g * l * g⁻¹)⁻¹ * l ∈ N := (QuotientGroup.eq_one_iff _).mp (by
        change ρ ((g * l * g⁻¹)⁻¹ * l) = 1
        rw [map_mul, map_inv, map_mul, map_mul, map_inv, h1, inv_mul_cancel])
      exact Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem hgl) hl, hmem⟩
  · exact (QuotientGroup.mk'_surjective _).comp (ρ.subgroupMap_surjective L)
  · intro l
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨l.2, ⟨_, h, rfl⟩⟩
    · rintro ⟨-, ⟨z, hz, hzl⟩⟩
      have : ρ.subgroupMap L l = z := Subtype.ext hzl.symm
      rw [this]
      exact hz
  · intro A
    rw [hnorm, Subgroup.map_le_iff_le_comap]

theorem theta_component_quotient_action {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hL : L ∈ thetaComponents p G)
    (U : Subgroup G) (hU : U ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (η : (L ⧸ aschbacherSolvableCore p L) ≃*
        L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)))
      (a : U →* MulAut (L ⧸ aschbacherSolvableCore p L))
      (b : U.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) →*
        MulAut (L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)))),
      (∀ l : L, (η (l : L ⧸ aschbacherSolvableCore p L) : G ⧸ aschbacherSolvableCore p G) =
        QuotientGroup.mk' (aschbacherSolvableCore p G) (l : G)) ∧
      (∀ (u : U) (l l' : L), (l' : G) = u * l * (u : G)⁻¹ →
        a u (l : L ⧸ aschbacherSolvableCore p L) = (l' : L ⧸ aschbacherSolvableCore p L)) ∧
      (∀ (v : U.map (QuotientGroup.mk' (aschbacherSolvableCore p G)))
        (k : L.map (QuotientGroup.mk' (aschbacherSolvableCore p G))),
        (b v k : G ⧸ aschbacherSolvableCore p G) = v * k * (v : G ⧸ aschbacherSolvableCore p G)⁻¹) ∧
      (∀ u : U, a u = 1 ↔ ((u : G) ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L,
        ((u : G) * l * (u : G)⁻¹) • (inSubgroup (aschbacherSolvableCore p) L : Set G) =
          l • (inSubgroup (aschbacherSolvableCore p) L : Set G))) ∧
      (∀ u : U, a u = 1 ↔ QuotientGroup.mk' (aschbacherSolvableCore p G) u ∈
        Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore p G)) :
          Subgroup (G ⧸ aschbacherSolvableCore p G)) : Set (G ⧸ aschbacherSolvableCore p G))) ∧
      (∀ u : U, MulAut.congr η (a u) =
        b ⟨QuotientGroup.mk' (aschbacherSolvableCore p G) u, Subgroup.mem_map_of_mem _ u.2⟩) ∧
      a.range.map (MulAut.congr η).toMonoidHom = b.range := by
  set N := aschbacherSolvableCore p G
  set ρ := QuotientGroup.mk' N
  set K := L.map ρ
  obtain ⟨-, -, ⟨η, hη⟩, hmapN, -, -, -, hC, -, -, hA⟩ := theta_component_quotient_structure hp hL
  have hchar : (aschbacherSolvableCore p L).Characteristic :=
    (solvable_prime_complement_core_characterization hp).2.1
  set a : U →* MulAut (L ⧸ aschbacherSolvableCore p L) :=
    (mulAutQuotientHom (aschbacherSolvableCore p L)).comp
      (L.normalizerMonoidHom.comp (Subgroup.inclusion hU))
  have hUK : U.map ρ ≤ Subgroup.normalizer (K : Set (G ⧸ N)) := (hA U).mp hU
  set b : U.map ρ →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hUK)
  have ha : ∀ (u : U) (l l' : L), (l' : G) = u * l * (u : G)⁻¹ →
      a u (l : L ⧸ aschbacherSolvableCore p L) = (l' : L ⧸ aschbacherSolvableCore p L) := by
    intro u l l' hl'
    have : (L.normalizerMonoidHom (Subgroup.inclusion hU u)) l = l' := Subtype.ext hl'.symm
    rw [← this]
    rfl
  have hb : ∀ (v : U.map ρ) (k : K), (b v k : G ⧸ N) = v * k * (v : G ⧸ N)⁻¹ :=
    fun v k => rfl
  have hker : ∀ u : U, a u = 1 ↔ ∀ l : L, (((u : G) * l * (u : G)⁻¹)⁻¹ * l) ∈
      inSubgroup (aschbacherSolvableCore p) L := by
    intro u
    constructor
    · intro h l
      have hl : a u (l : L ⧸ aschbacherSolvableCore p L) =
          (l : L ⧸ aschbacherSolvableCore p L) := by
        rw [h]
        rfl
      set l' : L := L.normalizerMonoidHom (Subgroup.inclusion hU u) l
      have hl' : a u (l : L ⧸ aschbacherSolvableCore p L) =
          (l' : L ⧸ aschbacherSolvableCore p L) := rfl
      rw [hl', QuotientGroup.eq] at hl
      exact ⟨_, hl, rfl⟩
    · intro h
      ext x
      induction x using QuotientGroup.induction_on with
      | H l =>
      rw [MulAut.one_apply]
      set l' : L := L.normalizerMonoidHom (Subgroup.inclusion hU u) l
      have hl' : a u (l : L ⧸ aschbacherSolvableCore p L) =
          (l' : L ⧸ aschbacherSolvableCore p L) := rfl
      rw [hl', QuotientGroup.eq]
      obtain ⟨y, hy, hyl⟩ := h l
      have : y = l'⁻¹ * l := Subtype.ext hyl
      rw [← this]
      exact hy
  have hkerC : ∀ u : U, a u = 1 ↔ ((u : G) ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L,
      ((u : G) * l * (u : G)⁻¹) • (inSubgroup (aschbacherSolvableCore p) L : Set G) =
        l • (inSubgroup (aschbacherSolvableCore p) L : Set G)) := by
    intro u
    rw [hker]
    constructor
    · intro h
      exact ⟨hU u.2, fun l hl => (leftCoset_eq_iff _).mpr (h ⟨l, hl⟩)⟩
    · rintro ⟨-, h⟩ l
      exact (leftCoset_eq_iff _).mp (h l l.2)
  have hconj : ∀ u : U, MulAut.congr η (a u) = b ⟨ρ u, Subgroup.mem_map_of_mem _ u.2⟩ := by
    intro u
    ext k
    obtain ⟨x, rfl⟩ := η.surjective k
    induction x using QuotientGroup.induction_on with
    | H l =>
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      hb]
    set l' : L := L.normalizerMonoidHom (Subgroup.inclusion hU u) l
    have hl' : a u (l : L ⧸ aschbacherSolvableCore p L) =
        (l' : L ⧸ aschbacherSolvableCore p L) := rfl
    rw [hl', hη, hη]
    change ρ ((u : G) * l * (u : G)⁻¹) = ρ u * ρ l * (ρ u)⁻¹
    rw [map_mul, map_mul, map_inv]
  refine ⟨η, a, b, hη, ha, hb, hkerC, fun u => (hkerC u).trans (hC u), hconj, ?_⟩
  have hcomp : (MulAut.congr η).toMonoidHom.comp a = b.comp (ρ.subgroupMap U) :=
    MonoidHom.ext fun u => hconj u
  rw [← MonoidHom.range_comp, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (ρ.subgroupMap_surjective U), ← MonoidHom.range_eq_map]

theorem theta_quotient_component_structure {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) :
    inSubgroup (aschbacherSolvableCore 3) L = L ⊓ aschbacherSolvableCore 3 G ∧
    IsComponent (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) ∧
    (∃ η : (L ⧸ aschbacherSolvableCore 3 L) ≃*
        L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
      ∀ l : L, (η (l : L ⧸ aschbacherSolvableCore 3 L) : G ⧸ aschbacherSolvableCore 3 G) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 G) (l : G)) ∧
    (Subgroup.normalizer (L : Set G)).map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) =
      Subgroup.normalizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
        Subgroup (G ⧸ aschbacherSolvableCore 3 G)) : Set (G ⧸ aschbacherSolvableCore 3 G)) ∧
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 G)).domRestrict
        (Subgroup.normalizer (L : Set G))).ker =
      (aschbacherSolvableCore 3 G).subgroupOf (Subgroup.normalizer (L : Set G)) ∧
    Subgroup.normalizer (L : Set G) =
      (Subgroup.normalizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
        Subgroup (G ⧸ aschbacherSolvableCore 3 G)) : Set (G ⧸ aschbacherSolvableCore 3 G))).comap
        (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ∧
    aschbacherSolvableCore 3 G ≤ Subgroup.normalizer (L : Set G) ∧
    (∀ g : G, (g ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L,
        (g * l * g⁻¹) • (inSubgroup (aschbacherSolvableCore 3) L : Set G) =
          l • (inSubgroup (aschbacherSolvableCore 3) L : Set G)) ↔
      QuotientGroup.mk' (aschbacherSolvableCore 3 G) g ∈
        Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
          Subgroup (G ⧸ aschbacherSolvableCore 3 G)) : Set (G ⧸ aschbacherSolvableCore 3 G))) ∧
    Function.Surjective ((QuotientGroup.mk' (Subgroup.center
        (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))))).comp
        ((QuotientGroup.mk' (aschbacherSolvableCore 3 G)).subgroupMap L)) ∧
    (∀ l : L, (QuotientGroup.mk' (Subgroup.center
        (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))))).comp
        ((QuotientGroup.mk' (aschbacherSolvableCore 3 G)).subgroupMap L) l = 1 ↔
      (l : G) ∈ {g : G | g ∈ L ∧ QuotientGroup.mk' (aschbacherSolvableCore 3 G) g ∈
        (Subgroup.center (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)))).map
          (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))).subtype}) ∧
    ∀ A : Subgroup G, A ≤ Subgroup.normalizer (L : Set G) ↔
      A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤
        Subgroup.normalizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
          Subgroup (G ⧸ aschbacherSolvableCore 3 G)) : Set (G ⧸ aschbacherSolvableCore 3 G)) :=
  theta_component_quotient_structure Nat.prime_three hL

theorem theta_quotient_component_action {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (U : Subgroup G) (hU : U ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (η : (L ⧸ aschbacherSolvableCore 3 L) ≃*
        L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)))
      (a : U →* MulAut (L ⧸ aschbacherSolvableCore 3 L))
      (b : U.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) →*
        MulAut (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)))),
      (∀ l : L, (η (l : L ⧸ aschbacherSolvableCore 3 L) : G ⧸ aschbacherSolvableCore 3 G) =
        QuotientGroup.mk' (aschbacherSolvableCore 3 G) (l : G)) ∧
      (∀ (u : U) (l l' : L), (l' : G) = u * l * (u : G)⁻¹ →
        a u (l : L ⧸ aschbacherSolvableCore 3 L) = (l' : L ⧸ aschbacherSolvableCore 3 L)) ∧
      (∀ (v : U.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)))
        (k : L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))),
        (b v k : G ⧸ aschbacherSolvableCore 3 G) = v * k * (v : G ⧸ aschbacherSolvableCore 3 G)⁻¹) ∧
      (∀ u : U, a u = 1 ↔ ((u : G) ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L,
        ((u : G) * l * (u : G)⁻¹) • (inSubgroup (aschbacherSolvableCore 3) L : Set G) =
          l • (inSubgroup (aschbacherSolvableCore 3) L : Set G))) ∧
      (∀ u : U, a u = 1 ↔ QuotientGroup.mk' (aschbacherSolvableCore 3 G) u ∈
        Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
          Subgroup (G ⧸ aschbacherSolvableCore 3 G)) : Set (G ⧸ aschbacherSolvableCore 3 G))) ∧
      (∀ u : U, MulAut.congr η (a u) =
        b ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 G) u, Subgroup.mem_map_of_mem _ u.2⟩) ∧
      a.range.map (MulAut.congr η).toMonoidHom = b.range :=
  theta_component_quotient_action Nat.prime_three hL U hU

end CFSG.RankThree
