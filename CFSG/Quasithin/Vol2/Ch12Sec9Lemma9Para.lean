module

public import CFSG.Quasithin.Vol2.Ch12Sec9Final

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem index_subgroupOf_eq_two {W' W'' : Subgroup G} (hle : W' ≤ W'')
    (hc : Nat.card W'' = 2 * Nat.card W') : (W'.subgroupOf W'').index = 2 := by
  have h1 := Subgroup.card_mul_index (W'.subgroupOf W'')
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hc] at h1
  have hpos : 0 < Nat.card W' := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])

theorem mul_inv_mem_of_card_eq_two_mul {W' W'' : Subgroup G} (hle : W' ≤ W'')
    (hc : Nat.card W'' = 2 * Nat.card W') {x y : G} (hx : x ∈ W'') (hy : y ∈ W'')
    (hx' : x ∉ W') (hy' : y ∉ W') : x * y⁻¹ ∈ W' := by
  have key := Subgroup.mul_mem_iff_of_index_two (index_subgroupOf_eq_two hle hc)
    (a := ⟨x, hx⟩) (b := ⟨y⁻¹, W''.inv_mem hy⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
  rw [key]
  exact ⟨fun h => absurd h hx', fun h => absurd (W'.inv_mem_iff.1 h) hy'⟩

theorem commutator_mem_of_card_eq_two_mul {W' W'' : Subgroup G} (hle : W' ≤ W'')
    (hc : Nat.card W'' = 2 * Nat.card W') {t : G} (ht' : t ∈ Subgroup.normalizer (W' : Set G))
    (ht'' : t ∈ Subgroup.normalizer (W'' : Set G)) {x : G} (hx : x ∈ W'') :
    t * x * t⁻¹ * x⁻¹ ∈ W' := by
  have hidx := index_subgroupOf_eq_two hle hc
  have htx : t * x * t⁻¹ ∈ W'' := (Subgroup.mem_normalizer_iff.1 ht'' x).1 hx
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t * x * t⁻¹, htx⟩)
    (b := ⟨x⁻¹, W''.inv_mem hx⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at key
  rw [key, ← (Subgroup.mem_normalizer_iff.1 ht' x), Subgroup.inv_mem_iff]

omit [Finite G] in
theorem exists_commutator_image {A W : Subgroup G} {v : G}
    (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hAW : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a)
    (hcomm : ∀ a ∈ A, a * v * a⁻¹ * v⁻¹ ∈ W) :
    ∃ R : Subgroup G, R ≤ W ∧ (∀ w ∈ R, ∃ a ∈ A, a * v * a⁻¹ * v⁻¹ = w) ∧
      Nat.card A = Nat.card R * Nat.card ↥(A ⊓ Subgroup.centralizer ({v} : Set G)) := by
  let f : ↥A →* ↥W :=
    { toFun := fun a => ⟨(a : G) * v * (a : G)⁻¹ * v⁻¹, hcomm a a.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have ha := hcomm a a.2
        have hb := hcomm b b.2
        have e1 : (a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) =
            ((b : G) * v * (b : G)⁻¹ * v⁻¹) * a := hAW a a.2 _ hb
        have e2 := hW _ ha _ hb
        show ((a * b : ↥A) : G) * v * ((a * b : ↥A) : G)⁻¹ * v⁻¹ =
          ((a : G) * v * (a : G)⁻¹ * v⁻¹) * ((b : G) * v * (b : G)⁻¹ * v⁻¹)
        rw [Subgroup.coe_mul]
        calc (a : G) * b * v * ((a : G) * b)⁻¹ * v⁻¹ =
            ((a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹)) * v * (a : G)⁻¹ * v⁻¹ := by group
          _ = (((b : G) * v * (b : G)⁻¹ * v⁻¹) * a) * v * (a : G)⁻¹ * v⁻¹ := by rw [e1]
          _ = ((b : G) * v * (b : G)⁻¹ * v⁻¹) * ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by group
          _ = ((a : G) * v * (a : G)⁻¹ * v⁻¹) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) := e2.symm }
  refine ⟨f.range.map W.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, a.2, rfl⟩
  · have hker : Nat.card f.ker = Nat.card ↥(A ⊓ Subgroup.centralizer ({v} : Set G)) := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      · have h1 := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
        change (x.1 : G) * v * (x.1 : G)⁻¹ * v⁻¹ = 1 at h1
        show (x.1 : G) ∈ Subgroup.centralizer ({v} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        calc v * (x.1 : G) = ((x.1 : G) * v * (x.1 : G)⁻¹ * v⁻¹)⁻¹ * (x.1 * v) := by group
          _ = x.1 * v := by rw [h1, inv_one, one_mul]
      · rw [MonoidHom.mem_ker]
        apply Subtype.ext
        have h1 := Subgroup.mem_centralizer_iff.1 y.2.2 v rfl
        change (y : G) * v * (y : G)⁻¹ * v⁻¹ = 1
        rw [← h1]
        group
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, hker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
      Subgroup.card_map_of_injective W.subtype_injective]

theorem centralizer_le_normalizer_of_not_isCyclic (h1222 : Stmt12_2_2) (h1297 : Lemma12_9_7)
    {T L V : Subgroup G} {n : ℕ} (hcx : Cx1291 G T L V n) {B : Subgroup G} (hBV : B ≤ V)
    (hBc : ¬ IsCyclic B) :
    Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hsq x x.2)⟩
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.1 (hVp.to_le hBV)
  have hi2 : 2 ≤ i := by
    by_contra hlt
    apply hBc
    interval_cases i
    · rw [pow_zero, Subgroup.card_eq_one] at hi
      rw [hi]
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hi
      exact isCyclic_of_prime_card hi
  have hin : i ≤ n := by
    have h1 := Subgroup.card_le_of_le hBV
    rw [hi, hcard] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  rcases eq_or_lt_of_le hin with rfl | hlt
  · have hBeq : B = V := Subgroup.eq_of_le_of_card_ge hBV (by rw [hi, hcard])
    rw [hBeq]
    exact Subgroup.centralizer_le_normalizer _
  · obtain ⟨Vi, hVi⟩ := exists_tsub hT2 hsq hab hTV hcard i hin
    obtain ⟨l, hl, hlB⟩ := lemma12_8_3_two hcx.hyp hVi.1 hBV hVi.2.1 hi
    have h97 := h1297 G _ L V n hcx i Vi (by omega) hlt hVi
    intro c hc
    have hcB : c ∈ Subgroup.normalizer (B : Set G) := Subgroup.centralizer_le_normalizer _ hc
    rw [← hlB, mem_normalizer_conjugate_iff] at hcB
    have h1 := (h97 hcB).2
    have h2 : l⁻¹ * (l * c * l⁻¹) * l⁻¹⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      mul_mem (mul_mem (inv_mem (hLV hl)) h1) (inv_mem (inv_mem (hLV hl)))
    rwa [show l⁻¹ * (l * c * l⁻¹) * l⁻¹⁻¹ = c by group] at h2

section Para

variable {T L V : Subgroup G} {n : ℕ}

theorem inf_conjugate_eq_bot_of_commutator_ne_bot (h1298 : Lemma12_9_8)
    (hcx : Cx1291 G T L V n) {g : G} (hAV : ⁅CFSG.conjugate V g, V⁆ ≠ ⊥) :
    V ⊓ CFSG.conjugate V g = ⊥ := by
  by_contra hne
  apply hAV
  rw [Subgroup.commutator_comm]
  exact (h1298 G T L V n hcx).2 g hne

theorem inf_normalizer_eq_inf_centralizer (h1222 : Stmt12_2_2) (h1298 : Lemma12_9_8)
    (hcx : Cx1291 G T L V n) {g : G} (hAT : CFSG.conjugate V g ≤ T)
    (hAV : ⁅CFSG.conjugate V g, V⁆ ≠ ⊥) :
    V ⊓ Subgroup.normalizer (CFSG.conjugate V g : Set G) =
      V ⊓ Subgroup.centralizer (CFSG.conjugate V g : Set G) := by
  obtain ⟨-, hTV⟩ := hcx.hyp.hyp.le_and_normalizes h1222
  have hbot := inf_conjugate_eq_bot_of_commutator_ne_bot h1298 hcx hAV
  refine le_antisymm (fun i hi => ⟨hi.1, ?_⟩)
    (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))
  show i ∈ Subgroup.centralizer (CFSG.conjugate V g : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : a * i * a⁻¹ * i⁻¹ ∈ V :=
    V.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTV (hAT ha)) i).1 hi.1) (V.inv_mem hi.1)
  have h2 : a * i * a⁻¹ * i⁻¹ ∈ CFSG.conjugate V g := by
    have h3 : i * a⁻¹ * i⁻¹ ∈ CFSG.conjugate V g :=
      (Subgroup.mem_normalizer_iff.1 hi.2 _).1 (inv_mem ha)
    rw [show a * i * a⁻¹ * i⁻¹ = a * (i * a⁻¹ * i⁻¹) by group]
    exact mul_mem ha h3
  have h4 : a * i * a⁻¹ * i⁻¹ = 1 := by
    have h5 : a * i * a⁻¹ * i⁻¹ ∈ V ⊓ CFSG.conjugate V g := ⟨h1, h2⟩
    rwa [hbot, Subgroup.mem_bot] at h5
  calc a * i = (a * i * a⁻¹ * i⁻¹) * (i * a) := by group
    _ = i * a := by rw [h4, one_mul]

theorem inf_centralizer_eq_of_not_isCyclic (h1222 : Stmt12_2_2) (h1297 : Lemma12_9_7)
    (h1298 : Lemma12_9_8) (hcx : Cx1291 G T L V n) {g : G} (hAT : CFSG.conjugate V g ≤ T)
    (hAV : ⁅CFSG.conjugate V g, V⁆ ≠ ⊥) {B : Subgroup G} (hBA : B ≤ CFSG.conjugate V g)
    (hBc : ¬ IsCyclic B) :
    V ⊓ Subgroup.centralizer (B : Set G) =
      V ⊓ Subgroup.centralizer (CFSG.conjugate V g : Set G) := by
  have hN := LinearS3.centralizer_le_normalizer_conjugate
    (fun B hB hc => centralizer_le_normalizer_of_not_isCyclic h1222 h1297 hcx hB hc) g hBA hBc
  refine le_antisymm ?_ (inf_le_inf_left _ (Subgroup.centralizer_le hBA))
  rw [← inf_normalizer_eq_inf_centralizer h1222 h1298 hcx hAT hAV]
  exact inf_le_inf_left _ hN

omit [Finite G] in
theorem not_le_centralizer_of_commutator_ne_bot {g : G} (hAV : ⁅CFSG.conjugate V g, V⁆ ≠ ⊥) :
    ¬ V ≤ Subgroup.centralizer (CFSG.conjugate V g : Set G) := fun h => by
  apply hAV
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 h

theorem le_centralizer_of_isTSub (h1222 : Stmt12_2_2) (h1297 : Lemma12_9_7) (h1298 : Lemma12_9_8)
    (hcx : Cx1291 G T L V n) {g : G} (hAT : CFSG.conjugate V g ≤ T)
    (hAV : ⁅CFSG.conjugate V g, V⁆ ≠ ⊥) {W : Subgroup G} (hW : IsTSub T V W (n - 1)) :
    W ≤ Subgroup.centralizer (CFSG.conjugate V g : Set G) := by
  classical
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes h1222
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have hn4 : 4 ≤ n := by rcases hcx.n45 with h | h <;> omega
  have : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsq x x.2) }
  have hex : ∀ j : ℕ, ∃ F : Subgroup G, j ≤ n → IsTSub T V F j := fun j => by
    by_cases hj : j ≤ n
    · obtain ⟨F, hF⟩ := exists_tsub hT2 hsq hab hTV hcard j hj
      exact ⟨F, fun _ => hF⟩
    · exact ⟨⊥, fun h => absurd h hj⟩
  choose F hF using hex
  have hchain : ∀ j, j < n → F j ≤ F (j + 1) := by
    intro j hj
    have h1 := hF j hj.le
    have h2 := hF (j + 1) hj
    rcases tinv_comparable_of_hyp1281One h1222 hcx.hyp h1.1 h2.1 h1.2.2 h2.2.2 with h | h
    · exact h
    · exfalso
      have h3 := Subgroup.card_le_of_le h
      rw [h1.2.1, h2.2.1] at h3
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
      omega
  have hWF : W = F (n - 1) := by
    have h1 := hF (n - 1) (by omega)
    rcases tinv_comparable_of_hyp1281One h1222 hcx.hyp hW.1 h1.1 hW.2.2 h1.2.2 with h | h
    · exact Subgroup.eq_of_le_of_card_ge h (by rw [hW.2.1, h1.2.1])
    · exact (Subgroup.eq_of_le_of_card_ge h (by rw [hW.2.1, h1.2.1])).symm
  rw [hWF]
  by_contra hne
  have hP : ∃ j, ¬ F j ≤ Subgroup.centralizer (CFSG.conjugate V g : Set G) := ⟨n - 1, hne⟩
  set j₁ := Nat.find hP with hj₁
  have hj₁spec : ¬ F j₁ ≤ Subgroup.centralizer (CFSG.conjugate V g : Set G) := Nat.find_spec hP
  have hj₁le : j₁ ≤ n - 1 := Nat.find_min' hP hne
  have hj₁pos : j₁ ≠ 0 := by
    intro h0
    apply hj₁spec
    have h1 := (hF 0 (by omega)).2.1
    rw [pow_zero, Subgroup.card_eq_one] at h1
    rw [h0, h1]
    exact bot_le
  set j₀ := j₁ - 1 with hj₀
  have hj₀C : F j₀ ≤ Subgroup.centralizer (CFSG.conjugate V g : Set G) := by
    by_contra h
    exact Nat.find_min hP (show j₀ < j₁ by omega) h
  have hF₀ := hF j₀ (by omega)
  have hF₁ := hF j₁ (by omega)
  have hF₀₁ : F j₀ ≤ F j₁ := by
    have := hchain j₀ (by omega)
    rwa [show j₀ + 1 = j₁ by omega] at this
  obtain ⟨v, hv₁, hvC⟩ : ∃ v ∈ F j₁, v ∉ Subgroup.centralizer (CFSG.conjugate V g : Set G) := by
    by_contra h
    push Not at h
    exact hj₁spec h
  have hc₁ : Nat.card (F j₁) = 2 * Nat.card (F j₀) := by
    rw [hF₀.2.1, hF₁.2.1, show j₁ = j₀ + 1 by omega, pow_succ, mul_comm]
  obtain ⟨R, hRW, -, hcardA⟩ := exists_commutator_image (A := CFSG.conjugate V g) (W := F j₀)
    (v := v) (fun x hx y hy => hab x (hF₀.1 hx) y (hF₀.1 hy))
    (fun a ha w hw => Subgroup.mem_centralizer_iff.1 (hj₀C hw) a ha)
    (fun a ha => commutator_mem_of_card_eq_two_mul hF₀₁ hc₁ (hF₀.2.2 (hAT ha))
      (hF₁.2.2 (hAT ha)) hv₁)
  set B := CFSG.conjugate V g ⊓ Subgroup.centralizer ({v} : Set G) with hB
  have hcardB : 4 ≤ Nat.card B := by
    have h1 := Subgroup.card_le_of_le hRW
    rw [LinearS3.card_conjugate, hcard] at hcardA
    rw [hF₀.2.1] at h1
    have h2 : 2 ^ n ≤ 2 ^ j₀ * Nat.card B := by
      rw [hcardA]
      exact Nat.mul_le_mul_right _ h1
    have h3 : 2 ^ n = 2 ^ j₀ * 2 ^ (n - j₀) := by rw [← pow_add]; congr 1; omega
    rw [h3] at h2
    have h4 := Nat.le_of_mul_le_mul_left h2 (by positivity)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - j₀) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ Nat.card B := h4
  have hBc : ¬ IsCyclic B := LinearS3.not_isCyclic_of_four_le
    (fun x hx => LinearS3.sq_eq_one_of_mem_conjugate hx.1) hcardB
  have h1 := inf_centralizer_eq_of_not_isCyclic h1222 h1297 h1298 hcx hAT hAV inf_le_left hBc
  have hvB : v ∈ V ⊓ Subgroup.centralizer (B : Set G) := by
    refine ⟨hF₁.1 hv₁, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 hb.2 v rfl).symm
  rw [h1] at hvB
  exact hvC hvB.2

theorem card_inf_centralizer_eq_two_and_le_commutator (h1222 : Stmt12_2_2) (h1297 : Lemma12_9_7)
    (h1298 : Lemma12_9_8) (hcx : Cx1291 G T L V n) {g : G} (hAT : CFSG.conjugate V g ≤ T)
    (hAV : ⁅CFSG.conjugate V g, V⁆ ≠ ⊥) {W : Subgroup G} (hW : IsTSub T V W (n - 1)) :
    Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) = 2 ∧
      W ≤ ⁅CFSG.conjugate V g, V⁆ := by
  classical
  obtain ⟨hcard, hsq, hab⟩ := hcx.hyp.card_sq
  have hyp := hcx.hyp.hyp
  obtain ⟨-, hTV⟩ := hyp.le_and_normalizes h1222
  have hn4 : 4 ≤ n := by rcases hcx.n45 with h | h <;> omega
  have : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hab _ a.2 _ b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsq x x.2) }
  have hWC := le_centralizer_of_isTSub h1222 h1297 h1298 hcx hAT hAV hW
  obtain ⟨v, hvV, hvW⟩ : ∃ v ∈ V, v ∉ W := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show V ≤ W from h)
    rw [hcard, hW.2.1] at h1
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    omega
  have hcVW : Nat.card V = 2 * Nat.card W := by
    rw [hcard, hW.2.1, ← pow_succ']
    congr 1
    omega
  obtain ⟨R, hRW, hRsurj, hcardA⟩ := exists_commutator_image (A := CFSG.conjugate V g) (W := W)
    (v := v) (fun x hx y hy => hab x (hW.1 hx) y (hW.1 hy))
    (fun a ha w hw => Subgroup.mem_centralizer_iff.1 (hWC hw) a ha)
    (fun a ha => commutator_mem_of_card_eq_two_mul hW.1 hcVW (hW.2.2 (hAT ha))
      (hTV (hAT ha)) hvV)
  have hCv : CFSG.conjugate V g ⊓ Subgroup.centralizer ({v} : Set G) =
      CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G) := by
    refine le_antisymm (fun a ha => ⟨ha.1, ?_⟩)
      (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hvV)))
    show a ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hav : v * a = a * v := Subgroup.mem_centralizer_iff.1 ha.2 v rfl
    by_cases hxW : x ∈ W
    · exact (Subgroup.mem_centralizer_iff.1 (hWC hxW) a ha.1).symm
    · have hw : x * v⁻¹ ∈ W := mul_inv_mem_of_card_eq_two_mul hW.1 hcVW hx hvV hxW hvW
      have hw' := Subgroup.mem_centralizer_iff.1 (hWC hw) a ha.1
      calc x * a = (x * v⁻¹) * (v * a) := by group
        _ = (x * v⁻¹) * (a * v) := by rw [hav]
        _ = a * (x * v⁻¹) * v := by rw [← mul_assoc, ← hw']
        _ = a * x := by group
  rw [hCv] at hcardA
  have hle2 : Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) ≤ 2 := by
    by_contra h
    push Not at h
    have h4 : 4 ≤ Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (((show IsPGroup 2 ↥(CFSG.conjugate V g) from
        IsPGroup.of_card (by rw [LinearS3.card_conjugate, hcard]))).to_le
        (inf_le_left : CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G) ≤ _))
      rw [hk] at h ⊢
      have : 2 ≤ k := by
        by_contra hk2
        interval_cases k <;> norm_num at h
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
    have hBc := LinearS3.not_isCyclic_of_four_le
      (B := CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G))
      (fun x hx => LinearS3.sq_eq_one_of_mem_conjugate (V := V) hx.1) h4
    have h1 := inf_centralizer_eq_of_not_isCyclic h1222 h1297 h1298 hcx hAT hAV inf_le_left hBc
    apply not_le_centralizer_of_commutator_ne_bot hAV
    intro x hx
    have hx' : x ∈ V ⊓ Subgroup.centralizer
        ((CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
      refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hb.2 x hx).symm
    rw [h1] at hx'
    exact hx'.2
  have hRcard := Subgroup.card_le_of_le hRW
  rw [LinearS3.card_conjugate, hcard] at hcardA
  rw [hW.2.1] at hRcard
  have hpos : 0 < Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) :=
    Nat.card_pos
  have hn' : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have hR : Nat.card R = 2 ^ (n - 1) := by
    refine le_antisymm hRcard ?_
    by_contra hlt
    push Not at hlt
    have : Nat.card R * Nat.card ↥(CFSG.conjugate V g ⊓ Subgroup.centralizer (V : Set G)) <
        2 ^ (n - 1) * 2 := by
      calc Nat.card R * _ ≤ Nat.card R * 2 := Nat.mul_le_mul_left _ hle2
        _ < 2 ^ (n - 1) * 2 := by omega
    omega
  refine ⟨?_, ?_⟩
  · rw [hR, hn'] at hcardA
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) hcardA).symm
  · have hRW' : R = W := Subgroup.eq_of_le_of_card_ge hRW (by rw [hR, hW.2.1])
    intro w hw
    rw [← hRW'] at hw
    obtain ⟨a, ha, rfl⟩ := hRsurj w hw
    have h1 := Subgroup.commutator_mem_commutator ha hvV
    rwa [commutatorElement_def] at h1

end Para

end CFSG.Quasithin.H13
