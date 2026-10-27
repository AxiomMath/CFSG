module

public import CFSG.Milestones.ASVolI.F4TISets
public import CFSG.Milestones.ASVolI.F431.JRed
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

@[expose] def burnsideF4ja_CentInput : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → κ ≠ .L3 → κ ≠ .G2d → Odd Gp.index → (Gp ≠ ⊤ ∨ κ = .Sp4) →
    ∀ x ∈ Gp, x ≠ 1 → x * x = 1 →
      (¬ ∃ g ∈ Gp, g * x * g⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) →
      ∃ w : E, IsConj x w ∧
        (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂)

section Generic

variable {G : Type} [Group G]

theorem burnsideF4ja_orderOf_eq_two_iff {x : G} : orderOf x = 2 ↔ x ≠ 1 ∧ x * x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff, pow_two]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem burnsideF4ja_orderOf_eq_of_isConj {x y : G} (h : IsConj x y) :
    orderOf x = orderOf y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact SemiconjBy.orderOf_eq c (show c * x = y * c by rw [← hc]; group)

theorem burnsideF4ja_inv_of_isConj {a b : G} (h : IsConj a b) (hb1 : b ≠ 1) (hb2 : b * b = 1) :
    a ≠ 1 ∧ a * a = 1 := by
  rw [← burnsideF4ja_orderOf_eq_two_iff, burnsideF4ja_orderOf_eq_of_isConj h,
    burnsideF4ja_orderOf_eq_two_iff]
  exact ⟨hb1, hb2⟩

theorem burnsideF4ja_card_centralizer_of_isConj {x y : G} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  rw [burnsideF4d_Z1_centralizer_conj, burnsideF4ja_card_conjSub]

theorem burnsideF4ja_isConj_subtype {H : Subgroup G} {x y : ↥H} :
    IsConj x y ↔ ∃ g ∈ H, g * (x : G) * g⁻¹ = (y : G) := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, c.2, congrArg Subtype.val hc⟩
  · rintro ⟨g, hg, hgxy⟩
    exact ⟨⟨g, hg⟩, Subtype.ext hgxy⟩

theorem burnsideF4ja_mem_normalizer_of_commute {S : Subgroup G} {x : G}
    (h : ∀ s ∈ S, s * x = x * s) : x ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : x * y * x⁻¹ = y := by rw [← h y hy]; group
    rw [h1]
    exact hy
  · intro hy
    have h1 := h _ hy
    have h2 : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * (x * y * x⁻¹ * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [h1]
        _ = x * y * x⁻¹ := by group
    rw [h2]
    exact hy

theorem burnsideF4ja_mem_normalizer_of_conjSub_eq {c : G} {X : Subgroup G}
    (h : conjSub c X = X) : c ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : c * x * c⁻¹ ∈ conjSub c X := mul_mem_conjSub hx
    rwa [h] at h1
  · intro hx
    rw [← h, mem_conjSub] at hx
    simpa [mul_assoc] using hx

variable [Finite G]

theorem burnsideF4ja_sylow_conj {P Q H : Subgroup G} (hP : ChF.IsSylowOf 2 P H)
    (hQ : ChF.IsSylowOf 2 Q H) : ∃ m ∈ H, P = conjSub m Q := by
  obtain ⟨m, hm, hle⟩ := F7.isSylowTwoOf_exists_conj_le (T := Q) (H := H) hQ hP.1 hP.2.1
  refine ⟨m, hm, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [burnsideF4ja_card_conjSub]
  exact burnsideF4ja_card_le_of_isSylowOf hP hQ.1 hQ.2.1

theorem burnsideF4ja_conj_into_sylow {T H : Subgroup G} (hT : ChF.IsSylowOf 2 T H) {x : G}
    (hx : x ∈ H) (hx2 : x * x = 1) : ∃ m ∈ H, m⁻¹ * x * m ∈ T := by
  obtain ⟨m, hm, hle⟩ := F7.isSylowTwoOf_exists_conj_le (T := T) (H := H) hT
    (Subgroup.zpowers_le.mpr hx) (burnsideF4ja_isPGroup_zpowers hx2)
  exact ⟨m, hm, mem_conjSub.mp (hle (Subgroup.mem_zpowers x))⟩

theorem burnsideF4ja_isSylowOf_conjSub {T H : Subgroup G} (hT : ChF.IsSylowOf 2 T H) {m : G}
    (hm : m ∈ H) : ChF.IsSylowOf 2 (conjSub m T) H := by
  have h := F7.isSylowTwoOf_conj (T := T) (H := H) hT m
  rwa [burnsideF4ja_conjSub_of_mem hm] at h

theorem burnsideF4ja_exists_transversal (Good : Set G)
    (hcov : ∀ x : G, orderOf x = 2 → ∃ w ∈ Good, IsConj w x) :
    ∃ T : Finset G, (∀ w ∈ T, w ∈ Good ∧ orderOf w = 2) ∧
      ∀ x : G, orderOf x = 2 → ∃! w, w ∈ T ∧ IsConj w x := by
  classical
  let rep : ConjClasses G → G := fun c =>
    if h : ∃ w ∈ Good, ConjClasses.mk w = c then Classical.choose h else 1
  have hrep : ∀ x : G, orderOf x = 2 →
      rep (ConjClasses.mk x) ∈ Good ∧
        ConjClasses.mk (rep (ConjClasses.mk x)) = ConjClasses.mk x := by
    intro x hx
    have h : ∃ w ∈ Good, ConjClasses.mk w = ConjClasses.mk x := by
      obtain ⟨w, hw, hwx⟩ := hcov x hx
      exact ⟨w, hw, ConjClasses.mk_eq_mk_iff_isConj.mpr hwx⟩
    have e : rep (ConjClasses.mk x) = Classical.choose h := dif_pos h
    rw [e]
    exact Classical.choose_spec h
  let inv : Finset G := (Set.toFinite {x : G | orderOf x = 2}).toFinset
  have hinv : ∀ x : G, x ∈ inv ↔ orderOf x = 2 := fun x => by simp [inv]
  refine ⟨inv.image (fun x => rep (ConjClasses.mk x)), ?_, ?_⟩
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    have hx' : orderOf x = 2 := (hinv x).mp hx
    obtain ⟨h1, h2⟩ := hrep x hx'
    refine ⟨h1, ?_⟩
    rw [burnsideF4ja_orderOf_eq_of_isConj (ConjClasses.mk_eq_mk_iff_isConj.mp h2)]
    exact hx'
  · intro x hx
    obtain ⟨-, h2⟩ := hrep x hx
    refine ⟨rep (ConjClasses.mk x), ⟨Finset.mem_image.mpr ⟨x, (hinv x).mpr hx, rfl⟩,
      ConjClasses.mk_eq_mk_iff_isConj.mp h2⟩, ?_⟩
    rintro w ⟨hw, hwx⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨-, h2'⟩ := hrep y ((hinv y).mp hy)
    have h3 : ConjClasses.mk y = ConjClasses.mk x := by
      rw [← h2']
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr hwx
    rw [h3]

end Generic

section CardTrick

variable {E M : Type} [Group E] [Group M]

theorem burnsideF4ja_card_range_inf_centralizer {N : Subgroup E} {b : ↥N →* M}
    (hb : Function.Injective b) {x : E} (hx : x ∈ N) :
    Nat.card ↥(b.range ⊓ Subgroup.centralizer ({b ⟨x, hx⟩} : Set M)) =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set E)) := by
  rw [← subImg_self, burnsideF4ja_subImg_inf_centralizer hb N hx,
    L3.card_subImg b hb inf_le_left]

variable [Finite E] [Finite M]

theorem burnsideF4ja_card_trick {N N' : Subgroup E} {b : ↥N →* M} {b' : ↥N' →* M}
    (hb : Function.Injective b) (hb' : Function.Injective b') (e : E → M)
    (he : ∀ x (hx : x ∈ N), e x = b ⟨x, hx⟩) (he' : ∀ x (hx : x ∈ N'), e x = b' ⟨x, hx⟩)
    {w y : E} (hw : w ∈ N) (hy : y ∈ N') (hwy : IsConj y w) (hewy : IsConj (e y) (e w))
    (h1 : Subgroup.centralizer ({w} : Set E) ≤ N)
    (h2 : Subgroup.centralizer ({e y} : Set M) ≤ b'.range) :
    Subgroup.centralizer ({e w} : Set M) ≤ b.range ∧
      Subgroup.centralizer ({y} : Set E) ≤ N' := by
  have hE := burnsideF4ja_card_centralizer_of_isConj hwy
  have hM := burnsideF4ja_card_centralizer_of_isConj hewy
  rw [he w hw] at hM ⊢
  rw [he' y hy] at hM h2
  have c1 := burnsideF4ja_card_range_inf_centralizer hb hw
  have c2 := burnsideF4ja_card_range_inf_centralizer hb' hy
  rw [inf_of_le_right h1] at c1
  rw [inf_of_le_right h2] at c2
  have l1 : Nat.card ↥(b.range ⊓ Subgroup.centralizer ({b ⟨w, hw⟩} : Set M)) ≤
      Nat.card ↥(Subgroup.centralizer ({b ⟨w, hw⟩} : Set M)) :=
    Subgroup.card_le_of_le inf_le_right
  have l2 : Nat.card ↥(N' ⊓ Subgroup.centralizer ({y} : Set E)) ≤
      Nat.card ↥(Subgroup.centralizer ({y} : Set E)) :=
    Subgroup.card_le_of_le inf_le_right
  refine ⟨?_, ?_⟩
  · have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right :
      b.range ⊓ Subgroup.centralizer ({b ⟨w, hw⟩} : Set M) ≤ _) (by omega)
    rw [← heq]
    exact inf_le_left
  · have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right :
      N' ⊓ Subgroup.centralizer ({y} : Set E) ≤ _) (by omega)
    rw [← heq]
    exact inf_le_left

end CardTrick

section LieSide


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4ja_lie_facts (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hL3 : κ ≠ .L3)
    (hG2d : κ ≠ .G2d) :
    (∀ w ∈ ctr (oPPrime 2 (Gp ⊓ M₁)), w ≠ 1 → ∀ n ∈ Gp, n * w = w * n → n ∈ M₁) ∧
    (κ ≠ .Sp4 → Set.ncard (InvClasses ↥Gp) = 2) ∧
    (κ = .Sp4 → Set.ncard (InvClasses ↥Gp) = 3 ∧ ∀ x ∈ Gp, x ≠ 1 → x * x = 1 →
      ∃ g ∈ Gp, g * x * g⁻¹ ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) := by
  have hyp' := burnsideF4j_restrict ChF.nativeChartCompatibility hyp
  have h27 := as_F_4_27 κ f ↥Gp ⊤ _ _ hyp' rfl
  dsimp only at h27
  obtain ⟨-, -, h2, h3, h4, -⟩ := h27
  have hZ : ctr (oPPrime 2 (Gp ⊓ M₁)) =
      (ctr (oPPrime 2 ((Gp ⊓ M₁).subgroupOf Gp))).map Gp.subtype := by
    rw [burnsideF4j_inf_eq_map Gp M₁, burnsideF4d_oPPrime_map _ Gp.subtype_injective,
      burnsideF4j_ctr_map _ Gp.subtype_injective, ← burnsideF4j_inf_eq_map]
  have hS : ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
      (ctr (pCoreOf 2 ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp))).map
        Gp.subtype := by
    rw [burnsideF4j_inf_inf_eq_map, burnsideF4j_pCoreOf_map _ Gp.subtype_injective,
      burnsideF4j_ctr_map _ Gp.subtype_injective]
  refine ⟨?_, fun hSp => (h3 ⟨hL3, hSp, hG2d⟩).1, fun hSp => ⟨(h2 hSp).1, ?_⟩⟩
  · intro w hw hw1 n hn hnw
    rw [hZ] at hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    have h1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; rfl)
    have hc := ((h4 hL3).1 w₀ hw₀ h1).2.2.1
    have hn' : (⟨n, hn⟩ : ↥Gp) ∈ Subgroup.centralizer ({w₀} : Set ↥Gp) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hnw
    have h5 := hc hn'
    rw [Subgroup.mem_subgroupOf] at h5
    exact h5.2
  · intro x hx hx1 hx2
    have hmem : ConjClasses.mk (⟨x, hx⟩ : ↥Gp) ∈ InvClasses ↥Gp :=
      ⟨⟨x, hx⟩, ConjClasses.mem_carrier_mk, fun h => hx1 (congrArg Subtype.val h),
        Subtype.ext hx2⟩
    obtain ⟨y, hy, hyc⟩ := (h2 hSp).2.1 _ hmem
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    refine ⟨((c⁻¹ : ↥Gp) : E), (c⁻¹).2, ?_⟩
    rw [hS]
    refine ⟨y, hyc, ?_⟩
    have hy' : y = c⁻¹ * ⟨x, hx⟩ * c := by rw [← hc]; group
    rw [hy']
    simp

theorem burnsideF4ja_centralizer_Z1bar_le (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hL3 : κ ≠ .L3)
    (hG2d : κ ≠ .G2d) {w : E} (hw : w ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) (hw1 : w ≠ 1) :
    Subgroup.centralizer ({w} : Set E) ≤ M₁ := by
  intro c hc
  obtain ⟨n, hn, h, hh, rfl⟩ := hyp.split c
  have hhN : h ∈ Subgroup.normalizer ((ctr (oPPrime 2 (Gp ⊓ M₁)) : Subgroup E) : Set E) :=
    burnsideF4j_mem_normalizer_ctr (burnsideF4d_Z1_normalizer_oPPrime
      (burnsideF4j_le_normalizer_inf hyp.normal M₁ hh.1))
  have hw' : h * w * h⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) :=
    (Subgroup.mem_normalizer_iff.mp hhN w).mp hw
  have hw'1 : h * w * h⁻¹ ≠ 1 := by
    intro h0
    apply hw1
    calc w = h⁻¹ * (h * w * h⁻¹) * h := by group
      _ = 1 := by rw [h0]; group
  obtain ⟨m, hm, hmw⟩ := burnsideF4j_Z1_conj hyp hL3 hG2d hw hw1 hw' hw'1
  have hc' : n * h * w = w * (n * h) := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hnm : n * m * w = w * (n * m) := by
    calc n * m * w = n * (m * w * m⁻¹) * m := by group
      _ = n * (h * w * h⁻¹) * m := by rw [hmw]
      _ = n * h * w * (h⁻¹ * m) := by group
      _ = w * (n * h) * (h⁻¹ * m) := by rw [hc']
      _ = w * (n * m) := by group
  have hnmM : n * m ∈ M₁ :=
    (burnsideF4ja_lie_facts hyp hL3 hG2d).1 w hw hw1 (n * m) (Gp.mul_mem hn hm.1) hnm
  have hnM : n ∈ M₁ := by
    have h1 := M₁.mul_mem hnmM (M₁.inv_mem hm.2.1)
    simpa using h1
  exact M₁.mul_mem hnM hh.1

theorem burnsideF4ja_centInput_top (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hGp : Gp = ⊤)
    (hL3 : κ ≠ .L3) (hSp : κ ≠ .Sp4) (hG2d : κ ≠ .G2d) {z₀ : E}
    (hz₀ : z₀ ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) (hz₀1 : z₀ ≠ 1) {x : E} (hx1 : x ≠ 1)
    (hx2 : x * x = 1) (hx : ¬ ∃ g ∈ Gp, g * x * g⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) :
    ∃ w : E, IsConj x w ∧ Subgroup.centralizer ({w} : Set E) ≤ M₂ := by
  subst hGp
  haveI := hyp.finite
  rw [top_inf_eq] at hz₀ hx
  have h27 := as_F_4_27 κ f E ⊤ M₁ M₂ hyp rfl
  dsimp only at h27
  obtain ⟨-, -, -, h3, h4, -⟩ := h27
  obtain ⟨hcard, ⟨C, ⟨hCI, hCm⟩, -⟩, hcov, hlong, hnb⟩ := h3 ⟨hL3, hSp, hG2d⟩
  obtain ⟨t, -, htR, htC⟩ := (h4 hL3).2 hG2d
  have ht1 : t ≠ 1 := htR.2.1
  have ht2 : t * t = 1 := htR.2.2.1
  have hnotZ : ∀ y : E, y ≠ 1 → y * y = 1 → hyp.toHypF_4_4g.chart.RootInvolution true y →
      ∀ c : E, c * y * c⁻¹ ∉ ctr (pCoreOf 2 (M₁ ⊓ M₂)) := fun y hy1 hy2 hyR c hc =>
    hnb y ⟨(hlong y hy1 hy2).mpr ⟨c, Subgroup.mem_top c, hc⟩, hyR⟩
  have hxl : ¬ hyp.toHypF_4_4g.chart.RootInvolution false x := by
    intro hR
    obtain ⟨c, -, hc⟩ := (hlong x hx1 hx2).mp hR
    obtain ⟨hc1, hc2⟩ := burnsideF4ja_inv_of_isConj
      (isConj_iff.mpr ⟨c, rfl⟩ : IsConj x (c * x * c⁻¹)).symm hx1 hx2
    exact hx ⟨c, Subgroup.mem_top c,
      burnsideF4j_top_ZS_inv_mem_Z1 hyp hL3 hSp hG2d hz₀ hz₀1 hc hc1 hc2⟩
  have hxs : hyp.toHypF_4_4g.chart.RootInvolution true x := (hcov x hx1 hx2).resolve_left hxl
  refine ⟨t, ?_, htC⟩
  by_contra hxt
  have hne : ConjClasses.mk x ≠ ConjClasses.mk t := fun h =>
    hxt (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  have hsub : ({ConjClasses.mk x, ConjClasses.mk t} : Set (ConjClasses E)) ⊆ InvClasses E := by
    intro D hD
    rcases hD with rfl | hD
    · exact ⟨x, ConjClasses.mem_carrier_mk, hx1, hx2⟩
    · rw [Set.mem_singleton_iff] at hD
      subst hD
      exact ⟨t, ConjClasses.mem_carrier_mk, ht1, ht2⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, Set.ncard_pair hne])
    (Set.toFinite _)
  rw [← heq] at hCI
  obtain ⟨y, hyC, hyS⟩ := hCm
  rcases hCI with rfl | hCt
  · rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hyC
    obtain ⟨c, hc⟩ := isConj_iff.mp hyC.symm
    exact hnotZ x hx1 hx2 hxs c (hc ▸ hyS)
  · rw [Set.mem_singleton_iff] at hCt
    subst hCt
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hyC
    obtain ⟨c, hc⟩ := isConj_iff.mp hyC.symm
    exact hnotZ t ht1 ht2 htR c (hc ▸ hyS)

theorem burnsideF4ja_not_long (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {w : E}
    (hw : w ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) {g : E} (hg : g ∈ Gp)
    (hct : Subgroup.centralizer ({g * w * g⁻¹} : Set E) ≤ M₂) : False := by
  haveI := hyp.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSyl, hB⟩ := burnsideF4j_sylow_data hyp
  have hP := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  have hgen := burnsideF4j_parabolics_gen hP
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSL : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ oPPrime 2 (Gp ⊓ M₁) :=
    burnsideF4d_Z1_le_oPPrime hSyl.2.1
      (le_inf (hSB.trans inf_le_left) (hSB.trans (inf_le_right.trans inf_le_left)))
  have hLG : oPPrime 2 (Gp ⊓ M₁) ≤ Gp ⊓ M₁ := burnsideF4d_oPPrime_le _
  have P1 : ∀ y ∈ Gp, conjSub y (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ≤ Gp ⊓ M₂ → y ∈ M₂ := by
    intro y hy hyS
    have hS2 : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (Gp ⊓ M₂) :=
      F7.isSylowTwoOf_mono_right hSyl
        (le_inf (hSB.trans inf_le_left) (hSB.trans (inf_le_right.trans inf_le_right)))
        inf_le_left
    have hyS2 : ChF.IsSylowOf 2 (conjSub y (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) (Gp ⊓ M₂) :=
      F7.isSylowTwoOf_mono_right (burnsideF4ja_isSylowOf_conjSub hSyl hy) hyS inf_le_left
    obtain ⟨m, hm, hmeq⟩ := burnsideF4ja_sylow_conj hyS2 hS2
    have hN : m⁻¹ * y ∈
        Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) := by
      apply burnsideF4ja_mem_normalizer_of_conjSub_eq
      rw [conjSub_mul, hmeq, conjSub_conjSub_inv]
    have hmy : m⁻¹ * y ∈ Gp ⊓ (M₁ ⊓ M₂) := by
      rw [hB]
      exact ⟨Gp.mul_mem (Gp.inv_mem hm.1) hy, hN⟩
    have h1 := M₂.mul_mem hm.2 hmy.2.2
    simpa using h1
  have hgL : ∀ y ∈ oPPrime 2 (Gp ⊓ M₁), g * y * g⁻¹ ∈ Gp ⊓ M₂ := by
    intro y hy
    refine ⟨Gp.mul_mem (Gp.mul_mem hg (hLG hy).1) (Gp.inv_mem hg), hct ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyw : y * w = w * y := Subgroup.mem_centralizer_iff.mp hw.2 y hy
    calc g * y * g⁻¹ * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hyw]
      _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
  have hgM : g ∈ M₂ := by
    refine P1 g hg fun x hx => ?_
    rw [mem_conjSub] at hx
    have h1 := hgL _ (hSL hx)
    simpa [mul_assoc] using h1
  have hLM : oPPrime 2 (Gp ⊓ M₁) ≤ Gp ⊓ M₂ := by
    intro y hy
    have hg2 : g ∈ Gp ⊓ M₂ := ⟨hg, hgM⟩
    have h1 := (Gp ⊓ M₂).mul_mem ((Gp ⊓ M₂).mul_mem ((Gp ⊓ M₂).inv_mem hg2) (hgL y hy)) hg2
    simpa [mul_assoc] using h1
  have h1M : Gp ⊓ M₁ ≤ M₂ := by
    intro x hx
    refine P1 x hx.1 fun y hy => ?_
    rw [mem_conjSub] at hy
    have hxN := burnsideF4d_le_normalizer_oPPrime (Gp ⊓ M₁) hx
    have h2 : x * (x⁻¹ * y * x) * x⁻¹ ∈ oPPrime 2 (Gp ⊓ M₁) :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp (hSL hy)
    have h3 : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [h3] at h2
    exact hLM h2
  obtain ⟨-, -, -, hmax⟩ := hP
  have hne := ((hmax (Gp ⊓ M₂)).mpr (Or.inr rfl)).2.2.1
  apply hne
  apply le_antisymm inf_le_left
  calc Gp = (Gp ⊓ M₁) ⊔ (Gp ⊓ M₂) := hgen.symm
    _ ≤ Gp ⊓ M₂ := sup_le (le_inf inf_le_left h1M) le_rfl

end LieSide

section Reduction


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4ja_fusion_fwd (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (i j : ↥(M₁ ⊓ M₂))
    (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hij : IsConj (i : E) (j : E)) : IsConj (bM β ε i) (bM β ε j) := by
  haveI := hyp.amalgam.finite
  obtain ⟨g, hgij⟩ := isConj_iff.mp hij
  obtain ⟨T, hT⟩ := burnsideF4j_exists_sylow (M₁ ⊓ M₂)
  have hST := burnsideF4j_S_le_sylow hyp.amalgam (show IsSylowTwoOf T (M₁ ⊓ M₂) from hT)
  obtain ⟨h, hh⟩ := as_F_4_30 κ f E Gp M₁ M₂ hyp.amalgam T hT Y β hyp.faithful {i} {j}
    (by rintro u rfl; exact hST hi) (by rintro u rfl; exact hST hj) ⟨g, by
      rw [Set.image_singleton, Set.image_singleton, Set.image_singleton, hgij]⟩
  rw [Set.image_singleton, Set.image_singleton, Set.image_singleton] at hh
  have hh' : h * bmap β i * h⁻¹ = bmap β j := Set.singleton_eq_singleton_iff.1 hh
  refine isConj_iff.2 ⟨epsG β ε h, ?_⟩
  show epsG β ε h * epsG β ε (bmap β i) * (epsG β ε h)⁻¹ = epsG β ε (bmap β j)
  rw [← hh', map_mul, map_mul, map_inv]

theorem burnsideF4ja_F_4_43_of (hin : burnsideF4ja_CentInput) (h35 : F_4_35) (h38 : F_4_38)
    (h39 : F_4_39) (h42 : F_4_42) : F_4_43 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL hL3
  classical
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG2d := hyp.not_G2d
  have hb₁ : Function.Injective (burnsideF4d_bOne β ε) := burnsideF4j_bOne_injective hyp
  have hb₂ : Function.Injective (burnsideF4d_bTwo β ε) := burnsideF4j_bTwo_injective hyp
  have hagree : ∀ g (h1 : g ∈ M₁) (h2 : g ∈ M₂),
      burnsideF4d_bOne β ε ⟨g, h1⟩ = burnsideF4d_bTwo β ε ⟨g, h2⟩ :=
    (burnsideF4d_amalgIsoM β hyp.faithful ε hyp.inj).agree
  set b₁ := burnsideF4d_bOne β ε with hb₁def
  set b₂ := burnsideF4d_bTwo β ε with hb₂def
  set e : E → M := amalgamMap b₁ b₂ with hedef
  have he₁ : ∀ x (hx : x ∈ M₁), e x = b₁ ⟨x, hx⟩ := fun x hx => amalgamMap_of_mem₁ b₁ b₂ hx
  have he₂ : ∀ x (hx : x ∈ M₂), e x = b₂ ⟨x, hx⟩ :=
    fun x hx => amalgamMap_of_mem₂ b₁ b₂ hagree hx
  have heb : ∀ v : ↥(M₁ ⊓ M₂), e v = bM β ε v := fun v => he₁ v v.2.1
  have hR₁ : MiOne β ε = b₁.range := by rw [burnsideF4d_MiOne_eq, subImg_self]
  have hR₂ : MiTwo β ε = b₂.range := by rw [burnsideF4d_MiTwo_eq, subImg_self]
  obtain ⟨T₀, hT₀⟩ := burnsideF4ja_exists_isSylowOf (MiOne β ε ⊓ MiTwo β ε)
  have h38' := h38 κ f E Gp M₁ M₂ Y β M ε z hyp hL T₀ hT₀
  have hodd : Odd Gp.index := h38'.2.2
  obtain ⟨hSGp, -⟩ := burnsideF4j_sylow_data hyp.amalgam
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ (M₁ ⊓ M₂) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hSG : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp := hSB.trans inf_le_left
  have hS1 : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ := hSB.trans (inf_le_right.trans inf_le_left)
  have hS2 : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₂ := hSB.trans (inf_le_right.trans inf_le_right)
  have hSE : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ⊤ := by
    refine ⟨le_top, hSGp.2.1, ?_⟩
    rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hSG]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h1 | h1
    · exact hSGp.2.2 h1
    · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)
  have hSM₁ : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) M₁ :=
    F7.isSylowTwoOf_mono_right hSE hS1 le_top
  have hSM₂ : ChF.IsSylowOf 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) M₂ :=
    F7.isSylowTwoOf_mono_right hSE hS2 le_top
  have hSM : ChF.IsSylowOf 2 (SinM Gp β ε) ⊤ := by
    have h1 := burnsideF4j_F_4_33_odd hyp hodd hT₀
    rwa [h38'.1] at h1
  set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hSdef
  have hKE : ∀ a c : E, a ∈ S → c ∈ S → a ≠ 1 → c ≠ 1 → a * a = 1 → c * c = 1 →
      (IsConj a c ↔ IsConj (e a) (e c)) ∧ (IsConj a c → ∃ g ∈ Gp, g * a * g⁻¹ = c) := by
    intro a c ha hc ha1 hc1 ha2 hc2
    have h35' := h35 κ f E Gp M₁ M₂ Y β M ε z hyp ⟨a, (hSB ha).2⟩ ⟨c, (hSB hc).2⟩ ha hc
      (fun h => ha1 (congrArg Subtype.val h)) (fun h => hc1 (congrArg Subtype.val h))
      (Subtype.ext ha2) (Subtype.ext hc2)
    have hfw := burnsideF4ja_fusion_fwd hyp ⟨a, (hSB ha).2⟩ ⟨c, (hSB hc).2⟩ ha hc
    have hea : e a = bM β ε ⟨a, (hSB ha).2⟩ := heb ⟨a, (hSB ha).2⟩
    have hec : e c = bM β ε ⟨c, (hSB hc).2⟩ := heb ⟨c, (hSB hc).2⟩
    rw [hea, hec]
    refine ⟨⟨hfw, fun h => ?_⟩, fun h => h35'.mpr (hfw h)⟩
    obtain ⟨g, -, hg⟩ := h35'.mpr h
    exact isConj_iff.mpr ⟨g, hg⟩
  have hCP : ∀ u x : E, u ∈ S → u ≠ 1 → u * u = 1 → (x ∈ M₁ ∨ x ∈ M₂) → x ≠ 1 →
      x * x = 1 → (IsConj u x ↔ IsConj (e u) (e x)) := by
    intro u x hu hu1 hu2 hxM hx1 hx2
    obtain ⟨x₀, hx₀S, hx₀x, hex₀⟩ : ∃ x₀ ∈ S, IsConj x₀ x ∧ IsConj (e x₀) (e x) := by
      rcases hxM with hx | hx
      · obtain ⟨m, hm, hmx⟩ := burnsideF4ja_conj_into_sylow hSM₁ hx hx2
        refine ⟨m⁻¹ * x * m, hmx, isConj_iff.mpr ⟨m, by group⟩,
          isConj_iff.mpr ⟨b₁ ⟨m, hm⟩, ?_⟩⟩
        rw [he₁ _ (hS1 hmx), he₁ x hx, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (show m * (m⁻¹ * x * m) * m⁻¹ = x by group)
      · obtain ⟨m, hm, hmx⟩ := burnsideF4ja_conj_into_sylow hSM₂ hx hx2
        refine ⟨m⁻¹ * x * m, hmx, isConj_iff.mpr ⟨m, by group⟩,
          isConj_iff.mpr ⟨b₂ ⟨m, hm⟩, ?_⟩⟩
        rw [he₂ _ (hS2 hmx), he₂ x hx, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (show m * (m⁻¹ * x * m) * m⁻¹ = x by group)
    obtain ⟨hx₀1, hx₀2⟩ := burnsideF4ja_inv_of_isConj hx₀x hx1 hx2
    have hk := (hKE u x₀ hu hx₀S hu1 hx₀1 hu2 hx₀2).1
    constructor
    · intro h
      exact (hk.mp (h.trans hx₀x.symm)).trans hex₀
    · intro h
      exact (hk.mpr (h.trans hex₀.symm)).trans hx₀x
  have hZ1 := burnsideF4j_Z1_eq hyp
  have hz := hyp.z_mem.1 hL3
  rw [hZ1] at hz
  obtain ⟨zb, hzbM, hzbZ, hzbe⟩ := mem_subImg.mp hz
  have hzb1 : zb ≠ 1 := by
    rintro rfl
    exact hyp.z_inv.1 (by rw [← hzbe]; exact map_one b₁)
  have hzb2 : zb * zb = 1 := by
    have h1 : b₁ (⟨zb, hzbM⟩ * ⟨zb, hzbM⟩) = b₁ 1 := by
      rw [map_mul, hzbe, map_one]; exact hyp.z_inv.2
    exact congrArg Subtype.val (hb₁ h1)
  have hSL : S ≤ oPPrime 2 (Gp ⊓ M₁) :=
    burnsideF4d_Z1_le_oPPrime hSGp.2.1 (le_inf hSG hS1)
  have hzbGp : zb ∈ Gp := (burnsideF4d_oPPrime_le _ hzbZ.1).1
  have hzbS : zb ∈ S := by
    have hcomm : ∀ s ∈ S, s * zb = zb * s := fun s hs =>
      Subgroup.mem_centralizer_iff.mp hzbZ.2 s (hSL hs)
    have hN : Subgroup.zpowers zb ≤ Subgroup.normalizer (S : Set E) :=
      Subgroup.zpowers_le.mpr (burnsideF4ja_mem_normalizer_of_commute hcomm)
    have hP : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers zb) :=
      IsPGroup.to_sup_of_normal_left' hSGp.2.1 (burnsideF4ja_isPGroup_zpowers hzb2) hN
    have hle : S ⊔ Subgroup.zpowers zb ≤ Gp := sup_le hSG (Subgroup.zpowers_le.mpr hzbGp)
    have heq := burnsideF4j_eq_of_sylow_le hSGp hP le_sup_left hle
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers zb)
  have hzbC : Subgroup.centralizer ({zb} : Set E) ≤ M₁ :=
    burnsideF4ja_centralizer_Z1bar_le hyp.amalgam hL3 hG2d hzbZ hzb1
  have hezb : e zb = z := by rw [he₁ zb hzbM]; exact hzbe
  let Good : Set E := {w | w ∈ S ∧ w ≠ 1 ∧ w * w = 1 ∧
    ((Subgroup.centralizer ({w} : Set E) ≤ M₁ ∧
        Subgroup.centralizer ({e w} : Set M) ≤ b₁.range) ∨
      (Subgroup.centralizer ({w} : Set E) ≤ M₂ ∧
        Subgroup.centralizer ({e w} : Set M) ≤ b₂.range))}
  have hzbG : zb ∈ Good :=
    ⟨hzbS, hzb1, hzb2, Or.inl ⟨hzbC, by rw [hezb, ← hR₁]; exact hyp.hb⟩⟩
  have hG : ∀ y ∈ S, y ≠ 1 → y * y = 1 →
      ((∃ g ∈ Gp, g * y * g⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∨
        Subgroup.centralizer ({e y} : Set M) ≤ b₁.range ∨
        Subgroup.centralizer ({e y} : Set M) ≤ b₂.range) →
      ∃ w ∈ Good, IsConj y w := by
    intro y hyS hy1 hy2 hyM
    by_cases hlong : ∃ g ∈ Gp, g * y * g⁻¹ ∈ ctr (oPPrime 2 (Gp ⊓ M₁))
    · obtain ⟨g, hg, hgy⟩ := hlong
      have hgy1 : g * y * g⁻¹ ≠ 1 := by
        intro h0
        apply hy1
        calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
          _ = 1 := by rw [h0]; group
      obtain ⟨m, -, hm⟩ := burnsideF4j_Z1_conj hyp.amalgam hL3 hG2d hzbZ hzb1 hgy hgy1
      refine ⟨zb, hzbG, ?_⟩
      exact (isConj_iff.mpr ⟨g, rfl⟩).trans (isConj_iff.mpr ⟨m, hm⟩).symm
    · have hyM' : Subgroup.centralizer ({e y} : Set M) ≤ b₁.range ∨
          Subgroup.centralizer ({e y} : Set M) ≤ b₂.range := hyM.resolve_left hlong
      obtain ⟨w, hyw, hwC⟩ : ∃ w : E, IsConj y w ∧
          (Subgroup.centralizer ({w} : Set E) ≤ M₁ ∨ Subgroup.centralizer ({w} : Set E) ≤ M₂) := by
        by_cases hcase : Gp = ⊤ ∧ κ ≠ .Sp4
        · obtain ⟨w, hyw, hwC⟩ := burnsideF4ja_centInput_top hyp.amalgam hcase.1 hL3 hcase.2
            hG2d hzbZ hzb1 hy1 hy2 hlong
          exact ⟨w, hyw, Or.inr hwC⟩
        · have hor : Gp ≠ ⊤ ∨ κ = .Sp4 := by
            by_cases hGp : Gp = ⊤
            · exact Or.inr (by by_contra hk; exact hcase ⟨hGp, hk⟩)
            · exact Or.inl hGp
          exact hin κ f E Gp M₁ M₂ hyp.amalgam hL3 hG2d hodd hor y (hSG hyS) hy1 hy2 hlong
      obtain ⟨hw1, hw2⟩ := burnsideF4ja_inv_of_isConj hyw.symm hy1 hy2
      refine ⟨y, ⟨hyS, hy1, hy2, ?_⟩, IsConj.refl y⟩
      have hw0 : w ∈ Subgroup.centralizer ({w} : Set E) :=
        Subgroup.mem_centralizer_singleton_iff.mpr rfl
      rcases hwC with hwC | hwC <;> rcases hyM' with hyC | hyC
      · have hwM := hwC hw0
        have hc := (hCP y w hyS hy1 hy2 (Or.inl hwM) hw1 hw2).mp hyw
        exact Or.inl ⟨(burnsideF4ja_card_trick hb₁ hb₁ e he₁ he₁ hwM (hS1 hyS) hyw hc hwC
          hyC).2, hyC⟩
      · have hwM := hwC hw0
        have hc := (hCP y w hyS hy1 hy2 (Or.inl hwM) hw1 hw2).mp hyw
        exact Or.inr ⟨(burnsideF4ja_card_trick hb₁ hb₂ e he₁ he₂ hwM (hS2 hyS) hyw hc hwC
          hyC).2, hyC⟩
      · have hwM := hwC hw0
        have hc := (hCP y w hyS hy1 hy2 (Or.inr hwM) hw1 hw2).mp hyw
        exact Or.inl ⟨(burnsideF4ja_card_trick hb₂ hb₁ e he₂ he₁ hwM (hS1 hyS) hyw hc hwC
          hyC).2, hyC⟩
      · have hwM := hwC hw0
        have hc := (hCP y w hyS hy1 hy2 (Or.inr hwM) hw1 hw2).mp hyw
        exact Or.inr ⟨(burnsideF4ja_card_trick hb₂ hb₂ e he₂ he₂ hwM (hS2 hyS) hyw hc hwC
          hyC).2, hyC⟩
  have hinto : ∀ x ∈ Gp, x * x = 1 → ∃ g ∈ Gp, g⁻¹ * x * g ∈ S := fun x hx hx2 =>
    burnsideF4ja_conj_into_sylow hSGp hx hx2
  obtain ⟨-, hcl2, hcl3⟩ := burnsideF4ja_lie_facts hyp.amalgam hL3 hG2d
  have hmain : (∀ x : E, orderOf x = 2 → ∃ w ∈ Good, IsConj w x) ∧
      ∃ w₀ ∈ Good, ¬ IsConj zb w₀ := by
    by_cases hSp : κ = .Sp4
    · obtain ⟨hcard, hmeet⟩ := hcl3 hSp
      have hZS : ∀ y ∈ ctr S, y ≠ 1 → y * y = 1 → ∃ w ∈ Good, IsConj y w := by
        intro y hy hy1 hy2
        have hyS : y ∈ S := hy.1
        refine hG y hyS hy1 hy2 ?_
        by_cases hy1' : y ∈ ctr (oPPrime 2 (Gp ⊓ M₁))
        · exact Or.inl ⟨1, Gp.one_mem, by simpa using hy1'⟩
        by_cases hy2' : y ∈ ctr (oPPrime 2 (Gp ⊓ M₂))
        · refine Or.inr (Or.inr ?_)
          have hyM₂ : y ∈ M₂ := hS2 hyS
          have hmem : b₂ ⟨y, hyM₂⟩ ∈ ctr (oPPrime 2 (GiTwo Gp β ε)) := by
            rw [burnsideF4j_Z2_eq hyp]
            exact mem_subImg_of_mem _ hyM₂ hy2'
          have hne : b₂ ⟨y, hyM₂⟩ ≠ 1 := by
            intro h0
            apply hy1
            have h1 : (⟨y, hyM₂⟩ : ↥M₂) = 1 := hb₂ (by rw [h0, map_one])
            exact congrArg Subtype.val h1
          rw [he₂ y hyM₂, ← hR₂]
          exact (hyp.hc hSp).1 _ hmem hne
        · refine Or.inr (Or.inl ?_)
          have h1 := h39 κ f E Gp M₁ M₂ Y β M ε z hyp hL hSp ⟨y, (hSB hyS).2⟩ hy
            (fun h => hy1 (congrArg Subtype.val h)) (Subtype.ext hy2) hy1' hy2'
          rw [heb ⟨y, (hSB hyS).2⟩, ← hR₁]
          exact h1.trans inf_le_left
      refine ⟨fun x hx => ?_, ?_⟩
      · obtain ⟨hx1, hx2⟩ := burnsideF4ja_orderOf_eq_two_iff.mp hx
        have hxG : x ∈ Gp := burnsideF4d_two_elt_mem hodd (k := 1)
          (by rw [pow_one, pow_two]; exact hx2)
        obtain ⟨g, hg, hgx⟩ := hmeet x hxG hx1 hx2
        obtain ⟨hgx1, hgx2⟩ := burnsideF4ja_inv_of_isConj
          (isConj_iff.mpr ⟨g, rfl⟩ : IsConj x (g * x * g⁻¹)).symm hx1 hx2
        obtain ⟨w, hw, hwx⟩ := hZS _ hgx hgx1 hgx2
        exact ⟨w, hw, (hwx.symm.trans (isConj_iff.mpr ⟨g, rfl⟩).symm)⟩
      ·
        have hzbI : ConjClasses.mk (⟨zb, hzbGp⟩ : ↥Gp) ∈ InvClasses ↥Gp :=
          ⟨⟨zb, hzbGp⟩, ConjClasses.mem_carrier_mk, fun h => hzb1 (congrArg Subtype.val h),
            Subtype.ext hzb2⟩
        obtain ⟨C, hC, hCne⟩ : ∃ C ∈ InvClasses ↥Gp,
            C ≠ ConjClasses.mk (⟨zb, hzbGp⟩ : ↥Gp) := by
          by_contra hcon
          push Not at hcon
          have hsub : InvClasses ↥Gp ⊆ {ConjClasses.mk (⟨zb, hzbGp⟩ : ↥Gp)} :=
            fun C hC => hcon C hC
          have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [Set.ncard_singleton, hcard] at h1
          omega
        obtain ⟨y, hyC, hy1, hy2⟩ := hC
        have hy1' : (y : E) ≠ 1 := fun h => hy1 (Subtype.ext h)
        have hy2' : (y : E) * (y : E) = 1 := congrArg Subtype.val hy2
        obtain ⟨g, hg, hgy⟩ := hmeet y y.2 hy1' hy2'
        obtain ⟨hgy1, hgy2⟩ := burnsideF4ja_inv_of_isConj
          (isConj_iff.mpr ⟨g, rfl⟩ : IsConj (y : E) (g * y * g⁻¹)).symm hy1' hy2'
        obtain ⟨w, hw, hyw⟩ := hZS _ hgy hgy1 hgy2
        refine ⟨w, hw, fun hzw => ?_⟩
        have hzy : IsConj zb (g * y * g⁻¹) := hzw.trans hyw.symm
        obtain ⟨g', hg', hg'zy⟩ :=
          (hKE zb _ hzbS hgy.1 hzb1 hgy1 hzb2 hgy2).2 hzy
        apply hCne
        rw [← ConjClasses.mem_carrier_iff_mk_eq.mp hyC]
        rw [ConjClasses.mk_eq_mk_iff_isConj]
        rw [burnsideF4ja_isConj_subtype]
        refine ⟨g'⁻¹ * g, Gp.mul_mem (Gp.inv_mem hg') hg, ?_⟩
        show g'⁻¹ * g * (y : E) * (g'⁻¹ * g)⁻¹ = zb
        calc g'⁻¹ * g * (y : E) * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * y * g⁻¹) * g' := by group
          _ = g'⁻¹ * (g' * zb * g'⁻¹) * g' := by rw [hg'zy]
          _ = zb := by group
    ·
      obtain ⟨t, htQ, ⟨deg, chart, -, hRI⟩, htC⟩ := h42 κ f E Gp M₁ M₂ Y β M ε z hyp hL hL3
      obtain ⟨-, ht1, ht2, -⟩ := hRI
      have hQS : pCoreOf 2 (Gp ⊓ M₂) ≤ S := by
        refine F7.isSylowTwoOf_pCoreOf_le ?_
        exact F7.isSylowTwoOf_mono_right hSGp (le_inf hSG hS2) inf_le_left
      have htS : (t : E) ∈ S := hQS htQ
      have het : e t = b₂ t := he₂ t t.2
      have htC' : Subgroup.centralizer ({e t} : Set M) ≤ b₂.range := by
        rw [het, ← hR₂]; exact htC
      have hnl : ¬ ∃ g ∈ Gp, g * zb * g⁻¹ = (t : E) := by
        rintro ⟨g, hg, hgt⟩
        have hzt : IsConj zb (t : E) := isConj_iff.mpr ⟨g, hgt⟩
        have hezt := (hKE zb t hzbS htS hzb1 ht1 hzb2 ht2).1.mp hzt
        have hCt := (burnsideF4ja_card_trick hb₁ hb₂ e he₁ he₂ hzbM t.2 hzt.symm hezt.symm
          hzbC htC').2
        exact burnsideF4ja_not_long hyp.amalgam hzbZ hg (by rw [hgt]; exact hCt)
      obtain ⟨w₀, hw₀G, htw₀⟩ := hG t htS ht1 ht2 (Or.inr (Or.inr htC'))
      have hcard := hcl2 hSp
      have hzt' : ConjClasses.mk (⟨zb, hzbGp⟩ : ↥Gp) ≠ ConjClasses.mk (⟨t, hSG htS⟩ : ↥Gp) := by
        intro h
        rw [ConjClasses.mk_eq_mk_iff_isConj, burnsideF4ja_isConj_subtype] at h
        exact hnl h
      refine ⟨fun x hx => ?_, w₀, hw₀G, fun hzw => ?_⟩
      · obtain ⟨hx1, hx2⟩ := burnsideF4ja_orderOf_eq_two_iff.mp hx
        have hxG : x ∈ Gp := burnsideF4d_two_elt_mem hodd (k := 1)
          (by rw [pow_one, pow_two]; exact hx2)
        have hsub : ({ConjClasses.mk (⟨zb, hzbGp⟩ : ↥Gp),
            ConjClasses.mk (⟨t, hSG htS⟩ : ↥Gp)} : Set (ConjClasses ↥Gp)) ⊆ InvClasses ↥Gp := by
          intro C hC
          rcases hC with rfl | rfl
          · exact ⟨⟨zb, hzbGp⟩, ConjClasses.mem_carrier_mk,
              fun h => hzb1 (congrArg Subtype.val h), Subtype.ext hzb2⟩
          · exact ⟨⟨t, hSG htS⟩, ConjClasses.mem_carrier_mk,
              fun h => ht1 (congrArg Subtype.val h), Subtype.ext ht2⟩
        have heqC := Set.eq_of_subset_of_ncard_le hsub
          (by rw [hcard, Set.ncard_pair hzt']) (Set.toFinite _)
        have hxI : ConjClasses.mk (⟨x, hxG⟩ : ↥Gp) ∈ InvClasses ↥Gp :=
          ⟨⟨x, hxG⟩, ConjClasses.mem_carrier_mk, fun h => hx1 (congrArg Subtype.val h),
            Subtype.ext hx2⟩
        rw [← heqC] at hxI
        rcases hxI with hxz | hxt
        · rw [ConjClasses.mk_eq_mk_iff_isConj, burnsideF4ja_isConj_subtype] at hxz
          obtain ⟨g, -, hg⟩ := hxz
          exact ⟨zb, hzbG, (isConj_iff.mpr ⟨g, hg⟩).symm⟩
        · rw [Set.mem_singleton_iff, ConjClasses.mk_eq_mk_iff_isConj,
            burnsideF4ja_isConj_subtype] at hxt
          obtain ⟨g, -, hg⟩ := hxt
          exact ⟨w₀, hw₀G, htw₀.symm.trans (isConj_iff.mpr ⟨g, hg⟩).symm⟩
      · have hzt : IsConj zb (t : E) := hzw.trans htw₀.symm
        exact hnl ((hKE zb t hzbS htS hzb1 ht1 hzb2 ht2).2 hzt)
  obtain ⟨hcov, w₀, hw₀G, hzw₀⟩ := hmain
  obtain ⟨T, hTG, hTrep⟩ := burnsideF4ja_exists_transversal Good hcov
  have horder : ∀ w ∈ Good, orderOf w = 2 := fun w hw =>
    burnsideF4ja_orderOf_eq_two_iff.mpr ⟨hw.2.1, hw.2.2.1⟩
  have heorder : ∀ w ∈ Good, orderOf (e w) = 2 := by
    intro w hw
    rw [he₁ w (hS1 hw.1), orderOf_injective b₁ hb₁, Subgroup.orderOf_mk]
    exact horder w hw
  obtain ⟨u, ⟨huT, huzb⟩, -⟩ := hTrep zb (horder zb hzbG)
  obtain ⟨v, ⟨hvT, hvw₀⟩, -⟩ := hTrep w₀ (horder w₀ hw₀G)
  have huG := (hTG u huT).1
  have hvG := (hTG v hvT).1
  have huv : ¬ IsConj u v := fun h => hzw₀ ((huzb.symm.trans h).trans hvw₀)
  have huv' : ¬ IsConj (e u) (e v) := fun h =>
    huv ((hKE u v huG.1 hvG.1 huG.2.1 hvG.2.1 huG.2.2.1 hvG.2.2.1).1.mpr h)
  have hcard := card_eq_of_transversal_data (horder u huG) (horder v hvG) huv
    (heorder u huG) (heorder v hvG) huv' T (fun w hw => (hTG w hw).2) hTrep (T.image e)
    (fun w' hw' => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
      exact heorder w (hTG w hw).1)
    (fun x' hx' => by
      obtain ⟨hx'1, hx'2⟩ := burnsideF4ja_orderOf_eq_two_iff.mp hx'
      obtain ⟨m, -, hm⟩ := burnsideF4ja_conj_into_sylow hSM (Subgroup.mem_top x') hx'2
      rw [burnsideF4d_SinM_eq] at hm
      obtain ⟨y, hyM, hyS, hye⟩ := mem_subImg.mp hm
      have hy1 : y ≠ 1 := by
        rintro rfl
        apply hx'1
        have h0 : m⁻¹ * x' * m = 1 := by rw [← hye]; exact map_one b₁
        calc x' = m * (m⁻¹ * x' * m) * m⁻¹ := by group
          _ = 1 := by rw [h0]; group
      have hy2 : y * y = 1 := by
        have h1 : b₁ (⟨y, hyM⟩ * ⟨y, hyM⟩) = b₁ 1 := by
          rw [map_mul, hye, map_one]
          calc m⁻¹ * x' * m * (m⁻¹ * x' * m) = m⁻¹ * (x' * x') * m := by group
            _ = 1 := by rw [hx'2]; group
        exact congrArg Subtype.val (hb₁ h1)
      have hey : IsConj (e y) x' := by
        rw [he₁ y hyM, hye]
        exact isConj_iff.mpr ⟨m, by group⟩
      obtain ⟨w, ⟨hwT, hwy⟩, hwuniq⟩ :=
        hTrep y (burnsideF4ja_orderOf_eq_two_iff.mpr ⟨hy1, hy2⟩)
      have hwG := (hTG w hwT).1
      refine ⟨e w, ⟨Finset.mem_image_of_mem e hwT,
        ((hKE w y hwG.1 hyS hwG.2.1 hy1 hwG.2.2.1 hy2).1.mp hwy).trans hey⟩, ?_⟩
      rintro w' ⟨hw'T, hw'x⟩
      obtain ⟨w₁, hw₁T, rfl⟩ := Finset.mem_image.mp hw'T
      have hw₁G := (hTG w₁ hw₁T).1
      have h1 : IsConj (e w₁) (e y) := hw'x.trans hey.symm
      have h2 : IsConj w₁ y :=
        (hKE w₁ y hw₁G.1 hyS hw₁G.2.1 hy1 hw₁G.2.2.1 hy2).1.mpr h1
      rw [hwuniq w₁ ⟨hw₁T, h2⟩])
    e
    (fun w₁ hw₁ w₂ hw₂ h => by
      have g₁ := (hTG w₁ hw₁).1
      have g₂ := (hTG w₂ hw₂).1
      rw [he₁ w₁ (hS1 g₁.1), he₁ w₂ (hS1 g₂.1)] at h
      exact congrArg Subtype.val (hb₁ h))
    (fun w' => Finset.mem_image) huT hvT rfl rfl
    (fun w hw => by
      have hwG := (hTG w hw).1
      have hw0 : w ∈ Subgroup.centralizer ({w} : Set E) :=
        Subgroup.mem_centralizer_singleton_iff.mpr rfl
      rcases hwG.2.2.2 with ⟨hC, hCM⟩ | ⟨hC, hCM⟩
      · obtain ⟨ψ, hψi, hψr, hψw, hψx⟩ := exists_centralizer_hom (b1 := b₁) (b2 := b₂) b₁ hb₁
          (fun a ha => he₁ a ha) hC hCM
        refine ⟨ψ, hψi, hψr, hψw, fun x hxo => ?_, fun x hxo => ?_⟩
        · obtain ⟨hx1, hx2⟩ := burnsideF4ja_orderOf_eq_two_iff.mp hxo
          rw [hψx x]
          exact hCP u x huG.1 huG.2.1 huG.2.2.1 (Or.inl (hC x.2)) hx1 hx2
        · obtain ⟨hx1, hx2⟩ := burnsideF4ja_orderOf_eq_two_iff.mp hxo
          rw [hψx x]
          exact hCP v x hvG.1 hvG.2.1 hvG.2.2.1 (Or.inl (hC x.2)) hx1 hx2
      · obtain ⟨ψ, hψi, hψr, hψw, hψx⟩ := exists_centralizer_hom (b1 := b₁) (b2 := b₂) b₂ hb₂
          (fun a ha => he₂ a ha) hC hCM
        refine ⟨ψ, hψi, hψr, hψw, fun x hxo => ?_, fun x hxo => ?_⟩
        · obtain ⟨hx1, hx2⟩ := burnsideF4ja_orderOf_eq_two_iff.mp hxo
          rw [hψx x]
          exact hCP u x huG.1 huG.2.1 huG.2.2.1 (Or.inr (hC x.2)) hx1 hx2
        · obtain ⟨hx1, hx2⟩ := burnsideF4ja_orderOf_eq_two_iff.mp hxo
          rw [hψx x]
          exact hCP v x hvG.1 hvG.2.1 hvG.2.2.1 (Or.inr (hC x.2)) hx1 hx2)
  exact hcard.symm

end Reduction

end CFSG.ASVolI
