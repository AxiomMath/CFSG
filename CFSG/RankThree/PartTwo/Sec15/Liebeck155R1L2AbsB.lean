module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2AbsDefs
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Y
import CFSG.RankThree.PartTwo.Sec15.MathUC155ThmC
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Frat
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open CFSG.Assembly.RankThreeEven (localRank projSL)
open CFSG.RankThree.PartTwo.Sec15

section Helpers

theorem res1L2B_mem_normalizer {G : Type*} [Group G] [Finite G] (R : Subgroup G) {w : G}
    (hw : ∀ s ∈ R, w * s * w⁻¹ ∈ R) : w ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact hw s hs
  · exact (Subgroup.card_map_of_injective (f := (MulAut.conj w).toMonoidHom)
      (MulAut.conj w).injective).ge

theorem res1L2B_mem_normalizer_zpowers {H : Type*} [Group H] {a x : H} (h : a * x * a⁻¹ = x⁻¹) :
    a ∈ Subgroup.normalizer (Subgroup.zpowers x : Set H) := by
  have key : ∀ b : H, b * x * b⁻¹ = x⁻¹ →
      ∀ y ∈ Subgroup.zpowers x, b * y * b⁻¹ ∈ Subgroup.zpowers x := by
    intro b hb y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, hb]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) _
  have h2 : a * x⁻¹ * a⁻¹ = x := by
    have := congrArg (fun t => t⁻¹) h
    simpa [mul_assoc] using this
  have h' : a⁻¹ * x * a⁻¹⁻¹ = x⁻¹ := by
    calc a⁻¹ * x * a⁻¹⁻¹ = a⁻¹ * (a * x⁻¹ * a⁻¹) * a⁻¹⁻¹ := by rw [h2]
      _ = x⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key a h y, fun hy => ?_⟩
  have := key a⁻¹ h' _ hy
  simpa [mul_assoc] using this

theorem res1L2B_exists_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B R : Subgroup G) (hRB : R ≤ B) (hR : IsPGroup p R)
    (hmax : ∀ X : Subgroup G, X ≤ B → IsPGroup p X → R ≤ X → X = R) :
    ∃ S : Sylow p B, (S : Subgroup B) = R.subgroupOf B := by
  refine ⟨{ toSubgroup := R.subgroupOf B
            isPGroup' := hR.comap_subtype
            is_maximal' := fun {Q} hQ hle => ?_ }, rfl⟩
  have hle' : R ≤ Q.map B.subtype := fun x hx =>
    ⟨⟨x, hRB hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have h := hmax (Q.map B.subtype) (Subgroup.map_subtype_le Q) (hQ.map _) hle'
  have hQ' : Q = (Q.map B.subtype).comap B.subtype :=
    (Subgroup.comap_map_eq_self_of_injective B.subtype_injective Q).symm
  rw [hQ', h]
  rfl

theorem res1L2B_card_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B R : Subgroup G) (hRB : R ≤ B) (hR : IsPGroup p R)
    (hmax : ∀ X : Subgroup G, X ≤ B → IsPGroup p X → R ≤ X → X = R)
    (X : Subgroup G) (hXB : X ≤ B) (hX : IsPGroup p X) : Nat.card X ≤ Nat.card R := by
  obtain ⟨S, hS⟩ := res1L2B_exists_sylow B R hRB hR hmax
  obtain ⟨Q, hQ⟩ := (hX.comap_subtype (K := B)).exists_le_sylow
  have h1 : Nat.card (X.subgroupOf B) ≤ Nat.card Q := Subgroup.card_le_of_le hQ
  have h2 : Nat.card Q = Nat.card S := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h3 : Nat.card S = Nat.card R := by
    rw [hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRB).toEquiv
  have h4 : Nat.card (X.subgroupOf B) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXB).toEquiv
  omega

theorem res1L2B_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B R : Subgroup G) (hRB : R ≤ B) (hR : IsPGroup p R)
    (hmax : ∀ X : Subgroup G, X ≤ B → IsPGroup p X → R ≤ X → X = R) :
    ¬ p ∣ (R.subgroupOf B).index := by
  obtain ⟨S, hS⟩ := res1L2B_exists_sylow B R hRB hR hmax
  have h := Sylow.not_dvd_index S
  rwa [hS] at h

theorem res1L2B_card_eq {G H : Type*} [Group G] [Group H] (f : G →* H) (X : Subgroup G) :
    Nat.card X = Nat.card (f.ker ⊓ X : Subgroup G) * Nat.card (X.map f) := by
  have h1 : Nat.card (f.ker.subgroupOf X) * (f.ker.subgroupOf X).index = Nat.card X :=
    Subgroup.card_mul_index _
  have h2 : (f.ker.subgroupOf X).index = Nat.card (X.map f) := Subgroup.relIndex_ker X f
  have h3 : Nat.card (f.ker.subgroupOf X) = Nat.card (f.ker ⊓ X : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right f.ker X]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h1, h2, h3]

theorem res1L2B_finite_map {G H : Type*} [Group G] [Finite G] [Group H] (f : G →* H)
    (X : Subgroup G) : Finite (X.map f) :=
  Finite.of_surjective (fun x : X => (⟨f x, x, x.2, rfl⟩ : X.map f))
    (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)

theorem res1L2B_isPGroup_zpowers {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] {x : G}
    (hx : x ^ p = 1) : IsPGroup p (Subgroup.zpowers x) := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).1
    (orderOf_dvd_of_pow_eq_one (n := p ^ 1) (by simpa using hx))
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem res1L2B_card_le_sup {G H : Type*} [Group G] [Finite G] [Group H] (ρ : G →* H) {p : ℕ}
    [Fact p.Prime] (R : Subgroup G) (hRker : R ≤ ρ.ker) (hR : IsPGroup p R)
    (hmax : ∀ X : Subgroup G, X ≤ ρ.ker → IsPGroup p X → R ≤ X → X = R)
    (j : G) (hj : j ^ p = 1) (hρj : ρ j ≠ 1) :
    ∀ X : Subgroup G, X ≤ (Subgroup.zpowers (ρ j)).comap ρ → IsPGroup p X →
      Nat.card X ≤ Nat.card (R ⊔ Subgroup.zpowers j : Subgroup G) := by
  have hρjp : orderOf (ρ j) = p := by
    refine orderOf_eq_prime ?_ hρj
    rw [← map_pow, hj, map_one]
  have hzp : Nat.card (Subgroup.zpowers (ρ j)) = p := by rw [Nat.card_zpowers, hρjp]
  have : Finite (Subgroup.zpowers (ρ j)) :=
    Nat.finite_of_card_ne_zero (by rw [hzp]; exact (Fact.out : p.Prime).ne_zero)
  intro X hX hXp
  have hl : Nat.card R * p ≤ Nat.card (R ⊔ Subgroup.zpowers j : Subgroup G) := by
    have := res1L2B_finite_map ρ (R ⊔ Subgroup.zpowers j)
    rw [res1L2B_card_eq ρ (R ⊔ Subgroup.zpowers j)]
    refine Nat.mul_le_mul ?_ ?_
    · exact Subgroup.card_le_of_le (le_inf hRker le_sup_left)
    · rw [← hzp]
      refine Subgroup.card_le_of_le ?_
      rw [Subgroup.zpowers_le]
      exact ⟨j, Subgroup.mem_sup_right (Subgroup.mem_zpowers j), rfl⟩
  have hX1 : Nat.card (ρ.ker ⊓ X : Subgroup G) ≤ Nat.card R :=
    res1L2B_card_le ρ.ker R hRker hR hmax _ inf_le_left hXp.to_inf_right
  have hX2 : Nat.card (X.map ρ) ≤ p := by
    rw [← hzp]
    exact Subgroup.card_le_of_le (Subgroup.map_le_iff_le_comap.mpr hX)
  calc Nat.card X = Nat.card (ρ.ker ⊓ X : Subgroup G) * Nat.card (X.map ρ) := res1L2B_card_eq ρ X
    _ ≤ Nat.card R * p := Nat.mul_le_mul hX1 hX2
    _ ≤ _ := hl

end Helpers

section Cover

private theorem res1L2B_isTwoLocal_map_mulEquiv {G H : Type*} [Group G] [Group H] {K : Subgroup G}
    (hK : CFSG.Open.IsTwoLocal K) (e : G ≃* H) : CFSG.Open.IsTwoLocal (K.map e.toMonoidHom) := by
  obtain ⟨P, hP, hP2, rfl⟩ := hK
  refine ⟨P.map e.toMonoidHom, ?_, hP2.map _, Subgroup.map_equiv_normalizer_eq P e⟩
  rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P e.injective]

private theorem res1L2B_localRank_le_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] (e : G ≃* H) {p : ℕ} (hp : p.Prime) : localRank p G ≤ localRank p H := by
  apply csSup_le'
  rintro _ ⟨K, hK, rfl⟩
  calc CFSG.Open.pRank p K ≤ CFSG.Open.pRank p (K.map e.toMonoidHom) :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp e.toMonoidHom
          e.injective K
    _ ≤ localRank p H := by
        refine le_csSup ⟨Nat.card H, ?_⟩
          ⟨K.map e.toMonoidHom, res1L2B_isTwoLocal_map_mulEquiv hK e, rfl⟩
        rintro _ ⟨Z, -, rfl⟩
        exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp Z).trans
          (Subgroup.card_le_card_group Z)

theorem res1L2B_false_of_cover_act
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hloc : localRank p G < 3) {Pi S : Subgroup G} [hPi : Group.IsPerfect Pi]
    {N : Subgroup Pi} [N.Normal] (hN : Group.IsSolvable N) {f : ℕ} (hf : 4 ≤ f) (hf4 : 4 ∣ f)
    (e : Pi ⧸ N ≃* projSL 2 (GaloisField 2 f)) (hS : IsPGroup p S)
    (hPS : Pi ≤ Subgroup.normalizer (S : Set G)) (hact : ∃ x ∈ Pi, ∃ s ∈ S, x * s * x⁻¹ ≠ s) :
    False := by
  have : Small.{0} G := by
    obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin G
    exact small_map eq
  let φ : G ≃* Shrink.{0} G := (Shrink.mulEquiv (α := G)).symm
  have : Finite (Shrink.{0} G) := Finite.of_equiv G φ.toEquiv
  let Pi' : Subgroup (Shrink.{0} G) := Pi.map φ.toMonoidHom
  let S' : Subgroup (Shrink.{0} G) := S.map φ.toMonoidHom
  let e1 : Pi ≃* Pi' := Subgroup.equivMapOfInjective Pi φ.toMonoidHom φ.injective
  have : Group.IsPerfect Pi' := Group.IsPerfect.ofSurjective (f := e1.toMonoidHom) e1.surjective
  let N' : Subgroup Pi' := N.map e1.toMonoidHom
  have : N'.Normal := Subgroup.Normal.map inferInstance e1.toMonoidHom e1.surjective
  have hN' : Group.IsSolvable N' :=
    Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective N e1.toMonoidHom
      e1.injective).toMonoidHom) (MulEquiv.surjective _)
  let e2 : Pi' ⧸ N' ≃* projSL 2 (GaloisField 2 f) := (QuotientGroup.congr N N' e1 rfl).symm.trans e
  have hloc' : localRank p (Shrink.{0} G) < 3 :=
    lt_of_le_of_lt (res1L2B_localRank_le_of_mulEquiv φ.symm (Fact.out : p.Prime)) hloc
  have hS' : IsPGroup p S' := hS.map _
  have hPS' : Pi' ≤ Subgroup.normalizer (S' : Set (Shrink.{0} G)) := by
    have h := Subgroup.map_mono (f := φ.toMonoidHom) hPS
    rwa [Subgroup.map_equiv_normalizer_eq] at h
  have hact' : ∃ x ∈ Pi', ∃ s ∈ S', x * s * x⁻¹ ≠ s := by
    obtain ⟨x, hx, s, hs, hne⟩ := hact
    refine ⟨φ x, ⟨x, hx, rfl⟩, φ s, ⟨s, hs, rfl⟩, fun h => hne (φ.injective ?_)⟩
    simpa using h
  rcases (by omega : f = 4 ∨ 6 ≤ f) with rfl | h6
  · exact Sylow155R1.false_of_perfect_cover_act_four (by omega) hloc' hN' e2 hS' hPS' hact'
  · exact Sylow155R1.false_of_perfect_cover_act hp5 hloc' hN' h6 e2 hS' hPS' hact'

end Cover

section YFacts

theorem res1L2B_Y_facts {Y : Type*} [Group Y] {n : ℕ} (hn : 2 ≤ n)
    (e : Y ≃* projSL 2 (GaloisField 2 n)) :
    Group.IsPerfect Y ∧ Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  have : IsSimpleGroup (projSL 2 (GaloisField 2 n)) :=
    CFSG.RankThree.PartTwo.Sec11.LSSolvableProof.isSimpleGroup_projSL hn
  have : IsSimpleGroup Y := e.isSimpleGroup
  have : Group.IsPerfect (projSL 2 (GaloisField 2 n)) :=
    Sylow155R1.isPerfect_projSL_two_even hn
  have hP : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨hP, ?_⟩
  have hc : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exfalso
      have h1 : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊥ :=
        Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr (le_of_eq h.symm)
      have h2 : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
        rw [← commutator_def]
        exact Group.IsPerfect.commutator_eq_top
      exact bot_ne_top (h1.symm.trans h2)
  intro a b hab
  have h : ∀ x : Y, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
    have := congrArg (fun φ : MulAut Y => φ x) hab
    simpa [MulAut.conj_apply] using this
  have hmem : b⁻¹ * a ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := h g
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
      _ = b⁻¹ * a * g := by group
  rw [hc, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.mp hmem).symm

end YFacts

section Config

variable {P : Type*} [Group P] [Finite P] {Y : Type*} [Group Y] {p : ℕ}

theorem res1L2B_cyclic (D : Res1L2Abs P Y p) (R : Subgroup P) (hRΘ : R ≤ D.Θ) (hR : IsPGroup p R)
    {θ : P} (hjθ : ∀ r ∈ R, D.j * r * D.j⁻¹ = θ⁻¹ * r * θ) :
    IsCyclic (R ⊓ Subgroup.centralizer ({θ} : Set P) : Subgroup P) := by
  have : Fact p.Prime := ⟨D.hp⟩
  by_contra hnc
  have hCp : IsPGroup p ↥(R ⊓ Subgroup.centralizer ({θ} : Set P)) := hR.to_inf_left
  obtain ⟨B, hB, hBcard⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (D.hp.odd_of_ne_two (by have := D.hp5; omega)) hCp hnc
  let E : Subgroup P := B.map (R ⊓ Subgroup.centralizer ({θ} : Set P)).subtype
  have hE : CFSG.Open.IsElemAbelian p E :=
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hB).map _
  have hEcard : Nat.card E = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hBcard]
  have hEle : E ≤ R ⊓ Subgroup.centralizer ({θ} : Set P) := Subgroup.map_subtype_le B
  have hEj : ∀ e ∈ E, e * D.j = D.j * e := by
    intro e he
    obtain ⟨heR, heθ⟩ := hEle he
    have h1 : e * θ = θ * e := Subgroup.mem_centralizer_singleton_iff.mp heθ
    have h2 := hjθ e heR
    have h3 : θ⁻¹ * e * θ = e := by
      calc θ⁻¹ * e * θ = θ⁻¹ * (e * θ) := by group
        _ = θ⁻¹ * (θ * e) := by rw [h1]
        _ = e := by group
    rw [h3] at h2
    calc e * D.j = (D.j * e * D.j⁻¹) * D.j := by rw [h2]
      _ = D.j * e := by group
  have hjE : D.j ∉ E := fun h => D.hρj (D.hΘker (hRΘ (hEle h).1))
  have hel : CFSG.Open.IsElemAbelian p (E ⊔ Subgroup.zpowers D.j) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE (CFSG.Open.isElemAbelian_zpowers D.hj)
      (fun a ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (Commute.zpow_right (show Commute a D.j from hEj a ha) i).eq)
  have hle : E ⊔ Subgroup.zpowers D.j ≤ D.M := by
    refine sup_le (fun e he => D.hCM ?_) (Subgroup.zpowers_le.2 D.hjM)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hEj e he)
  have hcard := D.hrank _ hle hel
  have hlt : Nat.card E < Nat.card (E ⊔ Subgroup.zpowers D.j : Subgroup P) := by
    by_contra hge
    push Not at hge
    have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : E ≤ E ⊔ Subgroup.zpowers D.j) hge
    apply hjE
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers D.j)
  omega

theorem res1L2B_exists_centralizing_cover
    (D : Res1L2Abs P Y p)
    (R : Subgroup P) (hRΘ : R ≤ D.Θ) (hR : IsPGroup p R)
    (hRmax : ∀ X : Subgroup P, X ≤ D.Θ → IsPGroup p X → R ≤ X → X = R) :
    ∃ Pi : Subgroup P, Pi ≤ Subgroup.normalizer (R : Set P) ∧
      Pi.map D.ρ = (MulAut.conj : Y →* MulAut Y).range ∧ ∀ x ∈ Pi, ∀ r ∈ R, x * r * x⁻¹ = r := by
  have : Fact p.Prime := ⟨D.hp⟩
  obtain ⟨eY⟩ := D.e
  have hn2 : 2 ≤ D.n := by have := D.hn4; omega
  obtain ⟨hYperf, hinj⟩ := res1L2B_Y_facts hn2 eY
  have hRker : R ≤ D.ρ.ker := hRΘ.trans D.hΘker
  have hmaxK : ∀ X : Subgroup P, X ≤ D.ρ.ker → IsPGroup p X → R ≤ X → X = R :=
    fun X hX hXp hRX => hRmax X (D.hker X hX hXp) hXp hRX
  have hfr : ∀ g : P, ∃ w ∈ Subgroup.normalizer (R : Set P), D.ρ g = D.ρ w := by
    intro g
    obtain ⟨b, hb, w, -, hw, hgw⟩ :=
      MathUC155ThmC.exists_mul_normalizes_of_card_max (⊤ : Subgroup P) D.ρ.ker R le_top
        (fun a _ b hb => D.ρ.normal_ker.conj_mem b hb a) hRker hR
        (fun X hX hXp => res1L2B_card_le D.ρ.ker R hRker hR hmaxK X hX hXp) g
        (Subgroup.mem_top g)
    refine ⟨w, res1L2B_mem_normalizer R hw, ?_⟩
    rw [hgw, map_mul, MonoidHom.mem_ker.mp hb, one_mul]
  set Inn : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range with hInn
  have hInnperf : ⁅Inn, Inn⁆ = Inn := by
    have h : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
      rw [← commutator_def]
      exact hYperf.commutator_eq_top
    rw [hInn, MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]
  have hle : Inn ≤ (Subgroup.normalizer (R : Set P)).map D.ρ := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨u, hu⟩ := D.hinn y
    obtain ⟨w, hw, huw⟩ := hfr u
    exact ⟨w, hw, by rw [← huw, hu]⟩
  obtain ⟨Pi, hPiN, hPiImg, hPiPerf, hPiNil⟩ := Sylow155R1.exists_perfect_cover_nilpotent D.ρ
    (Subgroup.normalizer (R : Set P)) Inn hInnperf hle
  refine ⟨Pi, hPiN, hPiImg, ?_⟩
  by_contra hcon
  push Not at hcon
  have : Group.IsPerfect Pi := Subgroup.isPerfect_iff.mpr hPiPerf
  have := hPiNil
  have hN : Group.IsSolvable ↥(D.ρ.comp Pi.subtype).ker := inferInstance
  have hrange : (D.ρ.comp Pi.subtype).range = Inn := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hPiImg
  let e : Pi ⧸ (D.ρ.comp Pi.subtype).ker ≃* projSL 2 (GaloisField 2 D.n) :=
    (QuotientGroup.quotientKerEquivRange (D.ρ.comp Pi.subtype)).trans
      ((MulEquiv.subgroupCongr hrange).trans ((MonoidHom.ofInjective hinj).symm.trans eY))
  exact res1L2B_false_of_cover_act (by have := D.hp5; omega) D.hloc hN D.hn4 D.hn e hR hPiN hcon

theorem Res1L2Abs.false_of_sylow_noncentral
    (D : Res1L2Abs P Y p)
    (R : Subgroup P) (hRΘ : R ≤ D.Θ) (hR : IsPGroup p R)
    (hRmax : ∀ X : Subgroup P, X ≤ D.Θ → IsPGroup p X → R ≤ X → X = R)
    (hRj : ∀ x ∈ R, D.j * x * D.j⁻¹ ∈ R) (hact : ∃ x ∈ R, D.j * x * D.j⁻¹ ≠ x) : False := by
  have : Fact p.Prime := ⟨D.hp⟩
  have hp2 : p ≠ 2 := by have := D.hp5; omega
  obtain ⟨eY⟩ := D.e
  have hn2 : 2 ≤ D.n := by have := D.hn4; omega
  obtain ⟨-, hinj⟩ := res1L2B_Y_facts hn2 eY
  have hRker : R ≤ D.ρ.ker := hRΘ.trans D.hΘker
  have hmaxK : ∀ X : Subgroup P, X ≤ D.ρ.ker → IsPGroup p X → R ≤ X → X = R :=
    fun X hX hXp hRX => hRmax X (D.hker X hX hXp) hXp hRX
  obtain ⟨Pi, hPiN, hPiImg, hPiC⟩ := res1L2B_exists_centralizing_cover D R hRΘ hR hRmax
  have hjN : D.j ∈ Subgroup.normalizer (R : Set P) := res1L2B_mem_normalizer R hRj
  have hjzp : IsPGroup p (Subgroup.zpowers D.j) := res1L2B_isPGroup_zpowers D.hj
  obtain ⟨y0, hy0⟩ := D.hjinn
  obtain ⟨c, hcPi, hc⟩ : ∃ c ∈ Pi, D.ρ c = D.ρ D.j := by
    have h : D.ρ D.j ∈ Pi.map D.ρ := by
      rw [hPiImg]
      exact ⟨y0, hy0.symm⟩
    obtain ⟨c, hc, hc'⟩ := h
    exact ⟨c, hc, hc'⟩
  have hkker : D.j * c⁻¹ ∈ D.ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hc, mul_inv_cancel]
  have hkN : D.j * c⁻¹ ∈ Subgroup.normalizer (R : Set P) :=
    (Subgroup.normalizer (R : Set P)).mul_mem hjN
      ((Subgroup.normalizer (R : Set P)).inv_mem (hPiN hcPi))
  have hjk : ∀ r ∈ R, D.j * r * D.j⁻¹ = (D.j * c⁻¹) * r * (D.j * c⁻¹)⁻¹ := by
    intro r hr
    have h1 := hPiC c⁻¹ (Pi.inv_mem hcPi) r hr
    rw [inv_inv] at h1
    calc D.j * r * D.j⁻¹ = D.j * (c⁻¹ * r * c) * D.j⁻¹ := by rw [h1]
      _ = (D.j * c⁻¹) * r * (D.j * c⁻¹)⁻¹ := by group
  have hRN : R ≤ D.ρ.ker ⊓ Subgroup.normalizer (R : Set P) :=
    le_inf hRker Subgroup.le_normalizer
  obtain ⟨θ', hθ'R, hθ'⟩ := MathUC155ThmC.exists_inner_of_conj_eq (p := p)
    (D.ρ.ker ⊓ Subgroup.normalizer (R : Set P)) R hRN
    (fun n hn r hr => (Subgroup.mem_normalizer_iff.mp hn.2 r).mp hr) hR
    (res1L2B_not_dvd_index _ R hRN hR
      (fun X hX hXp hRX => hmaxK X (hX.trans inf_le_left) hXp hRX))
    D.j (D.j * c⁻¹) hjzp ⟨hkker, hkN⟩ hjk
  set θ : P := θ'⁻¹ with hθdef
  have hθR : θ ∈ R := R.inv_mem hθ'R
  have hjθ : ∀ r ∈ R, D.j * r * D.j⁻¹ = θ⁻¹ * r * θ := by
    intro r hr
    rw [hθ' r hr, hθdef, inv_inv]
  have hy : R ≤ Subgroup.centralizer ({θ * D.j} : Set P) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hjθ r hr
    calc r * (θ * D.j) = θ * (θ⁻¹ * r * θ) * D.j := by group
      _ = θ * (D.j * r * D.j⁻¹) * D.j := by rw [h]
      _ = θ * D.j * r := by group
  have hθZ : ¬ R ≤ Subgroup.centralizer ({θ} : Set P) := by
    intro hcen
    obtain ⟨x, hx, hne⟩ := hact
    apply hne
    have h1 : x * θ = θ * x := Subgroup.mem_centralizer_singleton_iff.mp (hcen hx)
    rw [hjθ x hx]
    calc θ⁻¹ * x * θ = θ⁻¹ * (x * θ) := by group
      _ = θ⁻¹ * (θ * x) := by rw [h1]
      _ = x := by group
  have hRne : R ≠ ⊥ := by
    rintro rfl
    obtain ⟨x, hx, hne⟩ := hact
    rw [Subgroup.mem_bot] at hx
    apply hne
    rw [hx]
    group
  have hcyc := res1L2B_cyclic D R hRΘ hR hjθ
  set K₁ : Subgroup P := (Subgroup.zpowers (D.ρ D.j)).comap D.ρ with hK₁
  set Yb : Subgroup P :=
    (Subgroup.normalizer ((Subgroup.zpowers (D.ρ D.j) : Subgroup (MulAut Y)) :
      Set (MulAut Y))).comap D.ρ with hYb
  set Pm : Subgroup P := R ⊔ Subgroup.zpowers D.j with hPm
  have hΘK : D.Θ ≤ K₁ := fun x hx => by
    rw [hK₁, Subgroup.mem_comap, MonoidHom.mem_ker.mp (D.hΘker hx)]
    exact Subgroup.one_mem _
  have hRK : R ≤ K₁ := fun x hx => hΘK (hRΘ hx)
  have hjK : D.j ∈ K₁ := Subgroup.mem_comap.mpr (Subgroup.mem_zpowers _)
  have hPK : Pm ≤ K₁ := sup_le hRK (Subgroup.zpowers_le.2 hjK)
  have hPp : IsPGroup p Pm := hR.to_sup_of_normal_left' hjzp (Subgroup.zpowers_le.2 hjN)
  have hP : ∀ x ∈ Pm, ∃ r ∈ R, ∃ i : ℤ, x = r * D.j ^ i := by
    intro x hx
    have hx' : x ∈ ((R ⊔ Subgroup.zpowers D.j : Subgroup P) : Set P) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R (Subgroup.zpowers D.j)
      (Subgroup.zpowers_le.2 hjN)] at hx'
    obtain ⟨r, hr, s, hs, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    exact ⟨r, hr, i, rfl⟩
  have hKY : K₁ ≤ Yb := fun x hx => Subgroup.mem_comap.mpr
    (Subgroup.le_normalizer (Subgroup.mem_comap.mp hx))
  have hKn : ∀ a ∈ Yb, ∀ k ∈ K₁, a * k * a⁻¹ ∈ K₁ := by
    intro a ha k hk
    have ha' : D.ρ a ∈ Subgroup.normalizer
        ((Subgroup.zpowers (D.ρ D.j) : Subgroup (MulAut Y)) : Set (MulAut Y)) := ha
    have hk' : D.ρ k ∈ Subgroup.zpowers (D.ρ D.j) := hk
    show D.ρ (a * k * a⁻¹) ∈ Subgroup.zpowers (D.ρ D.j)
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp ha' _).mp hk'
  have hab : ∀ x ∈ K₁ ⊓ Subgroup.centralizer (R : Set P), ∀ x' ∈ K₁ ⊓ Subgroup.centralizer
      (R : Set P), Commute (D.ρ x) (D.ρ x') := by
    intro x hx x' hx'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hx.1)
    obtain ⟨i', hi'⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hx'.1)
    rw [← hi, ← hi']
    exact Commute.zpow_zpow_self _ _ _
  have hy0ne : y0 ≠ 1 := by
    rintro rfl
    apply D.hρj
    rw [hy0, map_one]
  have hy0p : y0 ^ p = 1 := by
    apply hinj
    rw [map_pow, ← hy0, ← map_pow, D.hj, map_one, map_one]
  have hy0ord : orderOf y0 = p := orderOf_eq_prime hy0p hy0ne
  obtain ⟨w, hw⟩ := l2_exists_inverter hn2 eY y0 hy0ne
    (by rw [hy0ord]; exact D.hp.odd_of_ne_two hp2)
  have hwy : w * y0 * w⁻¹ = y0⁻¹ := hw y0 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hwInn : MulAut.conj w ∈ Pi.map D.ρ := by
    rw [hPiImg]
    exact ⟨w, rfl⟩
  obtain ⟨g, hgPi, hg⟩ := hwInn
  have hginv : D.ρ g * D.ρ D.j * (D.ρ g)⁻¹ = (D.ρ D.j)⁻¹ := by
    rw [hg, hy0]
    have h : MulAut.conj (w * y0 * w⁻¹) = MulAut.conj y0⁻¹ := by rw [hwy]
    simpa [map_mul, map_inv] using h
  have hgY : g ∈ Yb := res1L2B_mem_normalizer_zpowers hginv
  have hgc : g ∈ Subgroup.centralizer (R : Set P) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h := hPiC g hgPi r hr
    calc r * g = (g * r * g⁻¹) * g := by rw [h]
      _ = g * r := by group
  have hinvK : ∀ x ∈ K₁ ⊓ Subgroup.centralizer (R : Set P),
      D.ρ g * D.ρ x * (D.ρ g)⁻¹ = (D.ρ x)⁻¹ := by
    intro x hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hx.1)
    rw [← hi, ← conj_zpow, hginv, inv_zpow]
  exact MathUC155ThmC.lemma438 D.ρ hp2 K₁ D.Θ R Pm Yb hΘK
    (fun k _ x hx => D.hΘn.conj_mem x hx k) hRΘ hR hRmax hPK hPp
    (res1L2B_card_le_sup D.ρ R hRker hR hmaxK D.j D.hj D.hρj) le_sup_left hRne hRker θ D.j hθR
    hθZ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) D.hj D.hρj hy hcyc hP hKY hKn hab g
    hgY hgc hinvK

end Config

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
