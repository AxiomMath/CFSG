module

public import CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

theorem burnsideF4nB_card_sigma_const {ι : Type*} {β : ι → Type*} [Finite ι]
    [∀ i, Finite (β i)] {k : ℕ} (h : ∀ i, Nat.card (β i) = k) :
    Nat.card (Σ i, β i) = Nat.card ι * k := by
  haveI := Fintype.ofFinite ι
  rw [Nat.card_sigma, Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]

theorem burnsideF4nB_card_diff_one {X : Type*} {s : Set X} {n : ℕ} (hs : Nat.card s = n + 1)
    {p : X} (hp : p ∈ s) : Nat.card {q // q ∈ s ∧ q ≠ p} = n := by
  have hfin : s.Finite := Set.finite_of_ncard_pos (by rw [← Nat.card_coe_set_eq, hs]; omega)
  have h1 : Nat.card {q // q ∈ s ∧ q ≠ p} = (s \ {p}).ncard := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [h1, Set.ncard_sdiff_singleton_of_mem hp, ← Nat.card_coe_set_eq, hs]
  rfl

@[expose] def burnsideF4nB_ext2 {V : Type} {Γ : SimpleGraph V} (π : GPath Γ 4) (w v : V)
    (hw : Γ.Adj (π 4) w) (hv : Γ.Adj w v) : GPath Γ 6 :=
  (π.snoc w hw).snoc v ((GPath.snoc_last π w hw).symm ▸ hv)

section Ext2

variable {V : Type} {Γ : SimpleGraph V} (π : GPath Γ 4) (w v : V) (hw : Γ.Adj (π 4) w)
  (hv : Γ.Adj w v)

theorem burnsideF4nB_ext2_le {i : ℕ} (hi : i ≤ 4) : burnsideF4nB_ext2 π w v hw hv i = π i := by
  unfold burnsideF4nB_ext2
  rw [GPath.snoc_of_le _ _ _ (by omega : i ≤ 4 + 1), GPath.snoc_of_le _ _ _ hi]

theorem burnsideF4nB_ext2_five : burnsideF4nB_ext2 π w v hw hv 5 = w := by
  unfold burnsideF4nB_ext2
  rw [GPath.snoc_of_le _ _ _ (le_refl (4 + 1))]
  exact GPath.snoc_last π w hw

theorem burnsideF4nB_ext2_six : burnsideF4nB_ext2 π w v hw hv 6 = v :=
  GPath.snoc_last _ v _

end Ext2

section Geo

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite Y] {c : α.Completion Y}

theorem burnsideF4nB_ncard_apart (F : c.Facts46 6) (hs : c.IsSmall 6)
    (hval : ∀ u : c.Γ, Nat.card (CosetGeom.nbrs u) = 3) (π : GPath c.graph 4) (hπ : π.NoBack) :
    {S : Set c.Γ | c.IsApartment 6 S ∧ ∀ i ≤ 4, π i ∈ S}.ncard = 8 := by
  have hconn := connected_graph c
  have hbip : ∀ a b : c.Γ, c.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
    fun _ _ h => CosetGeom.vtype_ne_of_adj h
  set a := π 0 with ha
  have hπg : c.graph.dist a (π 4) = 4 := (F.uniq 4 (by norm_num) a π ⟨rfl, hπ⟩).1
  have hπd : ∀ i ≤ 4, c.graph.dist a (π i) = i := fun i hi =>
    GPath.dist_prefix hconn π hπg hi
  have hgd : ∀ {b : c.Γ} {t : GPath c.graph 6}, t ∈ c.geods 6 a b → ∀ i ≤ 6,
      c.graph.dist a (t i) = i := by
    intro b t ht i hi
    have h := GPath.dist_prefix hconn t ht.2.2 hi
    rwa [ht.1] at h
  have hinj1 : ∀ {b : c.Γ}, c.graph.dist a b = 6 → ∀ {t t' : GPath c.graph 6},
      t ∈ c.geods 6 a b → t' ∈ c.geods 6 a b → t 1 = t' 1 → t = t' := by
    intro b hab t t' ht ht' h
    exact (burnsideF4b_allBij F hs hab).injOn ht ht' h
  have hcardg : ∀ {b : c.Γ}, c.graph.dist a b = 6 → Nat.card (c.geods 6 a b) = 3 := by
    intro b hab
    rw [Nat.card_congr (burnsideF4b_allBij F hs hab).equiv, hval]
  have hvert : ∀ {b : c.Γ} {t t' : GPath c.graph 6}, t ∈ c.geods 6 a b → t' ∈ c.geods 6 a b →
      ∀ {v : c.Γ} {k : ℕ}, v ∈ t.verts ∪ t'.verts → c.graph.dist a v = k → v = t k ∨ v = t' k := by
    intro b t t' ht ht' v k hv hk
    rcases hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · left
      rw [hgd ht j hj] at hk
      rw [hk]
    · right
      rw [hgd ht' j hj] at hk
      rw [hk]
  set Ext : Set (GPath c.graph 6) := {p | p ∈ GPath.nbPaths c.graph a 6 ∧ ∀ i ≤ 4, p i = π i}
    with hExt
  have hExt_geod : ∀ p ∈ Ext, p ∈ c.geods 6 a (p 6) := fun p hp => F.mem_geods hp.1
  have hExt_dist : ∀ p ∈ Ext, c.graph.dist a (p 6) = 6 := fun p hp => F.dist_m a p hp.1
  let R : ↥Ext → Type := fun p => {q // q ∈ c.geods 6 a (p.1 6) ∧ q ≠ p.1}
  let Φ : (Σ p : ↥Ext, R p) → Set c.Γ := fun x => Set.range (GPath.cycSeq x.1.1 x.2.1)
  have hrange : ∀ x : (Σ p : ↥Ext, R p),
      Φ x = x.1.1.verts ∪ x.2.1.verts := by
    intro x
    exact GPath.range_cycSeq (by norm_num) ((hExt_geod _ x.1.2).1.trans x.2.2.1.1.symm)
      (x.2.2.1.2.1.symm)
  have hmaps : ∀ x : (Σ p : ↥Ext, R p),
      Φ x ∈ {S : Set c.Γ | c.IsApartment 6 S ∧ ∀ i ≤ 4, π i ∈ S} := by
    intro x
    obtain ⟨hS, -, -⟩ := (F.lemma_F414_1 (hExt_dist _ x.1.2) (Φ x)).2
      ⟨x.1.1, x.2.1, hExt_geod _ x.1.2, x.2.2.1, fun h => x.2.2.2 h.symm, rfl⟩
    refine ⟨hS, fun i hi => ?_⟩
    rw [hrange]
    exact Or.inl ⟨i, by omega, x.1.2.2 i hi⟩
  have hΦinj : Function.Injective Φ := by
    rintro ⟨⟨p, hp⟩, ⟨q, hq, hqp⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq', hqp'⟩⟩ hΦ
    have hΦ' : Set.range (GPath.cycSeq p q) = Set.range (GPath.cycSeq p' q') := hΦ
    have hpg := hExt_geod p hp
    have hp'g := hExt_geod p' hp'
    have hr : Set.range (GPath.cycSeq p q) = p.verts ∪ q.verts :=
      hrange ⟨⟨p, hp⟩, ⟨q, hq, hqp⟩⟩
    have hr' : Set.range (GPath.cycSeq p' q') = p'.verts ∪ q'.verts :=
      hrange ⟨⟨p', hp'⟩, ⟨q', hq', hqp'⟩⟩
    have hb : p' 6 = p 6 := by
      have hmem : p' 6 ∈ p.verts ∪ q.verts := by
        have : p' 6 ∈ p'.verts ∪ q'.verts := Or.inl ⟨6, le_rfl, rfl⟩
        rw [← hr', ← hΦ', hr] at this
        exact this
      rcases hvert hpg hq hmem (hExt_dist p' hp') with h | h
      · exact h
      · exact h.trans hq.2.1
    have hab := hExt_dist p hp
    have hp'g2 : p' ∈ c.geods 6 a (p 6) := hb ▸ hp'g
    have hq'g2 : q' ∈ c.geods 6 a (p 6) := hb ▸ hq'
    have hsub : ∀ t : GPath c.graph 6, t = p' ∨ t = q' → ∀ i, i ≤ 6 →
        t i ∈ Set.range (GPath.cycSeq p q) := by
      intro t ht i hi
      rw [hΦ']
      have : t i ∈ p'.verts ∪ q'.verts := by
        rcases ht with rfl | rfl
        · exact Or.inl ⟨i, hi, rfl⟩
        · exact Or.inr ⟨i, hi, rfl⟩
      rw [← hr'] at this
      exact this
    have hpp' : p' = p := by
      rcases F.eq_of_verts_subset hs hab hpg hq (Ne.symm hqp) hp'g2 (hsub p' (Or.inl rfl)) with
        h | h
      · exact h
      · exfalso
        apply hqp
        apply hinj1 hab hq hpg
        rw [← h, hp'.2 1 (by norm_num), hp.2 1 (by norm_num)]
    subst hpp'
    have hqq' : q' = q := by
      rcases F.eq_of_verts_subset hs hab hpg hq (Ne.symm hqp) hq'g2 (hsub q' (Or.inr rfl)) with
        h | h
      · exact absurd h hqp'
      · exact h
    subst hqq'
    rfl
  have hsurj : ∀ S ∈ {S : Set c.Γ | c.IsApartment 6 S ∧ ∀ i ≤ 4, π i ∈ S}, ∃ x, Φ x = S := by
    rintro S ⟨hS, hπS⟩
    obtain ⟨φ⟩ := hS
    have hM : 0 < 2 * 6 := by norm_num
    have hM3 : 3 ≤ 2 * 6 := by norm_num
    have haS : a ∈ S := hπS 0 (by norm_num)
    obtain ⟨i₀, hi₀⟩ := φ.surjective ⟨a, haS⟩
    set z := GPath.polyWalk hM φ i₀.val with hz
    have hz0 : z 0 = a := by
      rw [hz, GPath.polyWalk_zero hM φ i₀, hi₀]
    have hdist : c.graph.dist (z 0) (z (0 + 6)) = 6 :=
      GPath.window_dist hconn hbip F.uniqueGeod z (GPath.polyWalk_adj hM φ i₀.val hM3)
        (GPath.polyWalk_nb hM φ i₀.val hM3) 0 le_rfl
    rw [hz0, Nat.zero_add] at hdist
    have hbS : z 6 ∈ S := GPath.polyWalk_mem hM φ i₀.val 6
    obtain ⟨p, q, hp, hq, hpq, hSeq⟩ := (F.lemma_F414_1 hdist S).1 ⟨⟨φ⟩, haS, hbS⟩
    have hSvq : ∀ {t t' : GPath c.graph 6}, t ∈ c.geods 6 a (z 6) → t' ∈ c.geods 6 a (z 6) →
        S = Set.range (GPath.cycSeq t t') → S = t.verts ∪ t'.verts := by
      intro t t' ht ht' h
      rw [h]
      exact GPath.range_cycSeq (by norm_num) (ht.1.trans ht'.1.symm) (ht.2.1.trans ht'.2.1.symm)
    have hext : ∀ {t t' : GPath c.graph 6}, t ∈ c.geods 6 a (z 6) → t' ∈ c.geods 6 a (z 6) →
        t ≠ t' → S = t.verts ∪ t'.verts → π 1 = t 1 → ∀ i ≤ 4, π i = t i := by
      intro t t' ht ht' htt' hSt h1 i hi
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · exact ht.1.symm
      have hπi : π i ∈ t.verts ∪ t'.verts := hSt ▸ hπS i hi
      rcases hvert ht ht' hπi (hπd i hi) with h | h
      · exact h
      · exfalso
        · have hgt : (t'.take i (by omega)).IsGeodesic := by
            show c.graph.dist ((t'.take i (by omega)) 0) ((t'.take i (by omega)) i) = i
            rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le i),
              GPath.take_apply_of_le _ _ _ le_rfl, ht'.1, ← h]
            exact hπd i hi
          have hgπ : (π.take i hi).IsGeodesic := by
            show c.graph.dist ((π.take i hi) 0) ((π.take i hi) i) = i
            rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le i), GPath.take_apply_of_le _ _ _ le_rfl]
            exact hπd i hi
          have heq := F.uniqueGeod i _ _ hgπ hgt
            (by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le i),
              GPath.take_apply_of_le _ _ _ (Nat.zero_le i), ht'.1])
            (by rw [GPath.take_apply_of_le _ _ _ le_rfl, GPath.take_apply_of_le _ _ _ le_rfl, h])
            (by omega)
          have h1' : π 1 = t' 1 := by
            have := congrArg (fun r : GPath c.graph i => r 1) heq
            simpa [GPath.take_apply_of_le _ _ _ (show 1 ≤ i by omega)] using this
          exact htt' (hinj1 hdist ht ht' (h1.symm.trans h1'))
    have hS1 : S = p.verts ∪ q.verts := hSvq hp hq hSeq
    have hπ1 : π 1 = p 1 ∨ π 1 = q 1 := hvert hp hq (hS1 ▸ hπS 1 (by norm_num)) (hπd 1 (by norm_num))
    have hmkExt : ∀ {t : GPath c.graph 6}, t ∈ c.geods 6 a (z 6) → (∀ i ≤ 4, π i = t i) →
        t ∈ Ext := by
      intro t ht h
      exact ⟨⟨ht.1, GPath.noBack_of_dist_eq hconn t (by rw [ht.1, ht.2.1]; exact hdist)⟩,
        fun i hi => (h i hi).symm⟩
    rcases hπ1 with h1 | h1
    · have hπp := hext hp hq hpq hS1 h1
      have hpE := hmkExt hp hπp
      refine ⟨⟨⟨p, hpE⟩, ⟨q, by rw [hp.2.1]; exact hq, Ne.symm hpq⟩⟩, ?_⟩
      exact hSeq.symm
    · have hS2 : S = q.verts ∪ p.verts := by rw [hS1, Set.union_comm]
      have hπq := hext hq hp (Ne.symm hpq) hS2 h1
      have hqE := hmkExt hq hπq
      refine ⟨⟨⟨q, hqE⟩, ⟨p, by rw [hq.2.1]; exact hp, hpq⟩⟩, ?_⟩
      show Set.range (GPath.cycSeq q p) = S
      rw [hSeq, GPath.range_cycSeq_comm (by norm_num) (hp.1.trans hq.1.symm)
        (hp.2.1.trans hq.2.1.symm)]
  have hset : {S : Set c.Γ | c.IsApartment 6 S ∧ ∀ i ≤ 4, π i ∈ S} = Set.range Φ := by
    ext S
    exact ⟨fun hS => hsurj S hS, by rintro ⟨x, rfl⟩; exact hmaps x⟩
  let W : Type := {w // w ∈ CosetGeom.nbrs (π 4) ∧ w ≠ π 3}
  let Vw : W → Type := fun w => {v // v ∈ CosetGeom.nbrs w.1 ∧ v ≠ π 4}
  have hW : Nat.card W = 2 := burnsideF4nB_card_diff_one (by rw [hval])
    ((π.adj 3 (by norm_num)).symm : c.graph.Adj (π 4) (π 3))
  have hVw : ∀ w : W, Nat.card (Vw w) = 2 := fun w =>
    burnsideF4nB_card_diff_one (by rw [hval]) (w.2.1.symm : c.graph.Adj w.1 (π 4))
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  haveI : ∀ w : W, Finite (Vw w) := fun w => Nat.finite_of_card_ne_zero (by rw [hVw w]; norm_num)
  let Ψ : (Σ w : W, Vw w) → GPath c.graph 6 := fun x =>
    burnsideF4nB_ext2 π x.1.1 x.2.1 x.1.2.1 x.2.2.1
  have hΨle : ∀ x : (Σ w : W, Vw w), ∀ i ≤ 4, Ψ x i = π i := fun x i hi =>
    burnsideF4nB_ext2_le π x.1.1 x.2.1 x.1.2.1 x.2.2.1 hi
  have hΨ5 : ∀ x : (Σ w : W, Vw w), Ψ x 5 = x.1.1 := fun x =>
    burnsideF4nB_ext2_five π x.1.1 x.2.1 x.1.2.1 x.2.2.1
  have hΨ6 : ∀ x : (Σ w : W, Vw w), Ψ x 6 = x.2.1 := fun x =>
    burnsideF4nB_ext2_six π x.1.1 x.2.1 x.1.2.1 x.2.2.1
  have hΨinj : Function.Injective Ψ := by
    intro x x' h
    have h5 : x.1.1 = x'.1.1 := by rw [← hΨ5 x, ← hΨ5 x', h]
    have h6 : x.2.1 = x'.2.1 := by rw [← hΨ6 x, ← hΨ6 x', h]
    obtain ⟨⟨w, hw⟩, ⟨v, hv⟩⟩ := x
    obtain ⟨⟨w', hw'⟩, ⟨v', hv'⟩⟩ := x'
    simp only at h5 h6
    subst h5
    subst h6
    rfl
  have hΨrange : Set.range Ψ = Ext := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨hΨle x 0 (Nat.zero_le 4), fun i hi => ?_⟩, fun i hi => hΨle x i hi⟩
      rcases (by omega : i ≤ 2 ∨ i = 3 ∨ i = 4) with h | rfl | rfl
      · rw [hΨle x i (by omega), hΨle x (i + 2) (by omega)]
        exact hπ i (by omega)
      · show Ψ x 3 ≠ Ψ x 5
        rw [hΨle x 3 (by omega), hΨ5]
        exact x.1.2.2.symm
      · show Ψ x 4 ≠ Ψ x 6
        rw [hΨle x 4 le_rfl, hΨ6]
        exact x.2.2.2.symm
    · rintro ⟨hp, hpπ⟩
      have hw : p 5 ∈ CosetGeom.nbrs (π 4) ∧ p 5 ≠ π 3 := by
        refine ⟨?_, ?_⟩
        · show c.graph.Adj (π 4) (p 5)
          rw [← hpπ 4 le_rfl]
          exact p.adj 4 (by norm_num)
        · rw [← hpπ 3 (by norm_num)]
          exact (hp.2 3 (by norm_num)).symm
      have hv : p 6 ∈ CosetGeom.nbrs (p 5) ∧ p 6 ≠ π 4 := by
        refine ⟨p.adj 5 (by norm_num), ?_⟩
        rw [← hpπ 4 le_rfl]
        exact (hp.2 4 (by norm_num)).symm
      refine ⟨⟨⟨p 5, hw⟩, ⟨p 6, hv⟩⟩, ?_⟩
      apply GPath.ext'
      intro i hi
      rcases (by omega : i ≤ 4 ∨ i = 5 ∨ i = 6) with h | rfl | rfl
      · rw [hΨle _ i h, hpπ i h]
      · exact hΨ5 _
      · exact hΨ6 _
  have hExtcard : Nat.card ↥Ext = 4 := by
    rw [← hΨrange, ← Nat.card_congr (Equiv.ofInjective Ψ hΨinj),
      burnsideF4nB_card_sigma_const hVw, hW]
  haveI : Finite ↥Ext := Nat.finite_of_card_ne_zero (by rw [hExtcard]; norm_num)
  have hR : ∀ p : ↥Ext, Nat.card (R p) = 2 := fun p =>
    burnsideF4nB_card_diff_one (hcardg (hExt_dist _ p.2)) (hExt_geod _ p.2)
  haveI : ∀ p : ↥Ext, Finite (R p) := fun p =>
    Nat.finite_of_card_ne_zero (by rw [hR p]; norm_num)
  rw [hset, ← Nat.card_coe_set_eq, ← Nat.card_congr (Equiv.ofInjective Φ hΦinj),
    burnsideF4nB_card_sigma_const hR, hExtcard]

end Geo

end CFSG.ASVolI
