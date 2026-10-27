module

public import CFSG.RankThree.PartTwo.Sec11.Item116FusionCases
import CFSG.RankThree.PartTwo.Sec11.Item116TheoremO
import CFSG.RankThree.PartTwo.Sec6.Item65Two

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace TheoremO

section General

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_zpow_mul_zpow_of_mem_closure_pair {x y : G} (hxy : x * y = y * x) {z : G}
    (hz : z ∈ Subgroup.closure ({x, y} : Set G)) : ∃ i j : ℤ, z = x ^ i * y ^ j := by
  induction hz using Subgroup.closure_induction with
  | mem w hw =>
    rcases hw with rfl | hw
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul u v _ _ hu hv =>
    obtain ⟨i, j, rfl⟩ := hu
    obtain ⟨k, l, rfl⟩ := hv
    refine ⟨i + k, j + l, ?_⟩
    have hcom : y ^ j * x ^ k = x ^ k * y ^ j :=
      ((Commute.zpow_zpow (hxy : Commute x y) k j).eq).symm
    calc x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l := by group
      _ = x ^ i * (x ^ k * y ^ j) * y ^ l := by rw [hcom]
      _ = x ^ (i + k) * y ^ (j + l) := by rw [zpow_add, zpow_add]; group
  | inv u _ hu =>
    obtain ⟨i, j, rfl⟩ := hu
    refine ⟨-i, -j, ?_⟩
    have hcom : y ^ (-j) * x ^ (-i) = x ^ (-i) * y ^ (-j) :=
      ((Commute.zpow_zpow (hxy : Commute x y) (-i) (-j)).eq).symm
    calc (x ^ i * y ^ j)⁻¹ = y ^ (-j) * x ^ (-i) := by group
      _ = x ^ (-i) * y ^ (-j) := hcom

omit [Finite G] in
theorem exists_zpowers_eq_mul {c a : G} (hca : c * a = a * c) (ha3 : a ^ 3 = 1) {e : G}
    (he : e ∈ Subgroup.closure ({c, a} : Set G)) (hec : e ∉ Subgroup.zpowers c) :
    ∃ b ∈ Subgroup.zpowers c, Subgroup.zpowers e = Subgroup.zpowers (a * b) := by
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hca he
  have ha3' : a ^ (3 : ℤ) = 1 := by exact_mod_cast ha3
  have hj := zpow_eq_zpow_emod j ha3'
  have hj0 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
  have hj3 : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
  have hcomm : ∀ k l : ℤ, c ^ k * a ^ l = a ^ l * c ^ k := fun k l =>
    (Commute.zpow_zpow (hca : Commute c a) k l).eq
  have hcomm1 : ∀ k : ℤ, c ^ k * a = a * c ^ k := fun k =>
    (Commute.zpow_left (hca : Commute c a) k).eq
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h1 | h2
  · exfalso
    apply hec
    rw [hj, h0, zpow_zero, mul_one]
    exact Subgroup.zpow_mem_zpowers c i
  · refine ⟨c ^ i, Subgroup.zpow_mem_zpowers c i, ?_⟩
    rw [hj, h1, zpow_one, hcomm1 i]
  · refine ⟨c ^ (-i), Subgroup.zpow_mem_zpowers c (-i), ?_⟩
    rw [← Subgroup.zpowers_inv]
    congr 1
    have hj' : a ^ (-j) = a := by
      rw [zpow_eq_zpow_emod (-j) ha3', show -j % 3 = 1 by omega, zpow_one]
    calc (c ^ i * a ^ j)⁻¹ = c ^ (-i) * a ^ (-j) := by rw [hcomm i j]; group
      _ = a * c ^ (-i) := by rw [hj', hcomm1 (-i)]

omit [Finite G] in
theorem centralizer_eq_of_zpowers_eq {x y : G} (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
    GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, h]

omit [Finite G] in
theorem thetaComponentsAt_eq_of_zpowers_eq {x y : G}
    (h : Subgroup.zpowers x = Subgroup.zpowers y) :
    thetaComponentsAt 3 x = thetaComponentsAt 3 y := by
  rw [thetaComponentsAt_eq_thetaComponentsIn, thetaComponentsAt_eq_thetaComponentsIn,
    centralizer_eq_of_zpowers_eq h]

theorem zpowers_eq_of_mem_of_ne_one {x y : G} (hx3 : x ^ 3 = 1) (hy : y ∈ Subgroup.zpowers x)
    (hy1 : y ≠ 1) : Subgroup.zpowers y = Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hy
    exact hy1 hy
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx3 hx1,
      orderOf_eq_prime hy3 hy1])

theorem card_theta_centralizer_conj (x g : G) :
    Nat.card (inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({g * x * g⁻¹} : Set G))) =
      Nat.card (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set G))) := by
  rw [← MulAut.conj_apply, ← map_centralizer_singleton, ← map_inSubgroup_aschbacherSolvableCore,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

omit [Finite G] in
theorem map_conj_sec11K (L : Subgroup G) (x g : G) :
    (sec11K L x).map (MulAut.conj g).toMonoidHom =
      sec11K (L.map (MulAut.conj g).toMonoidHom) (g * x * g⁻¹) := by
  rw [sec11K, sec11K, map_inSubgroup_perfectResidual,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_centralizer_singleton, MulAut.conj_apply]

omit [Finite G] in
theorem sec11K_mul_eq {L : Subgroup G} {x b : G} (hb : ∀ l ∈ L, l * b = b * l) :
    sec11K L (x * b) = sec11K L x := by
  have h : L ⊓ Subgroup.centralizer ({x * b} : Set G) =
      L ⊓ Subgroup.centralizer ({x} : Set G) := by
    ext l
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hl, h⟩
      refine ⟨hl, mul_right_cancel (b := b) ?_⟩
      calc l * x * b = l * (x * b) := by group
        _ = x * b * l := h
        _ = x * (b * l) := by group
        _ = x * (l * b) := by rw [hb l hl]
        _ = x * l * b := by group
    · rintro ⟨hl, h⟩
      refine ⟨hl, ?_⟩
      calc l * (x * b) = l * x * b := by group
        _ = x * l * b := by rw [h]
        _ = x * (l * b) := by group
        _ = x * (b * l) := by rw [hb l hl]
        _ = x * b * l := by group
  rw [sec11K, sec11K, h]

end General

end TheoremO

section Props

@[expose] def Item116P2b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
        Sec21.IsIrreducibleOn
            (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})) →
          CFSG.ABGLocalTools.IsSylowOf 3 R ⊤ → d ∉ Subgroup.zpowers c →
          (∀ w ∈ Subgroup.normalizer (A : Set G),
            (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
            (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c)) →
          ∀ n ∈ Subgroup.normalizer (A : Set G), n * c * n⁻¹ ∈ Subgroup.zpowers d →
            n * d * n⁻¹ ∈ Subgroup.zpowers c → n * a * n⁻¹ = a⁻¹ →
              Y.map (MulAut.conj n).toMonoidHom ≠ Y

@[expose] def Item116P2c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
        Sec21.IsIrreducibleOn
            (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})) →
          CFSG.ABGLocalTools.IsSylowOf 3 R ⊤ → d ∉ Subgroup.zpowers c →
          (∀ w ∈ Subgroup.normalizer (A : Set G),
            (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
            (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c)) →
          ∀ n ∈ Subgroup.normalizer (A : Set G), n * c * n⁻¹ ∈ Subgroup.zpowers d →
            n * d * n⁻¹ ∈ Subgroup.zpowers c → n * a * n⁻¹ = a⁻¹ →
              Y = sec11K L a ⊔ inSubgroup (aschbacherSolvableCore 3) Y

end Props

namespace TheoremO

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem mem_sec11K_d (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) : d ∈ sec11K L a := by
  have hA : A = Subgroup.closure {c, a, d} := by
    rw [← Item116Fusion.closure_cda_eq h hdL hdc, Set.pair_comm d a]
  have haB : a ∉ Subgroup.closure ({c, d} : Set G) := fun ha =>
    Item116Fusion.not_mem_innerPreimage h (Item116Fusion.closure_le_innerPreimage h hdL ha)
  exact (basic_facts_of_conj h45 h hdL hA h.a_mem haB).2.2.2.2

theorem exists_orderOf_eq_two_mem_sec11K (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) :
    ∃ t ∈ sec11K L a, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdK := mem_sec11K_d h45 h hdL hdc
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hK1 : sec11K L a ≠ ⊥ := fun hK => hd1 (by rwa [hK, Subgroup.mem_bot] at hdK)
  have h2 := Sec6.two_dvd_card_of_isPerfect
    (PartOne.EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _) hK1
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := sec11K L a) 2 h2
  exact ⟨t, t.2, by rw [Subgroup.orderOf_coe, ht]⟩

theorem mem_map_conj_of_conj_mem_zpowers (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) {n : G}
    (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c) : c ∈ Y.map (MulAut.conj n).toMonoidHom := by
  have hdY : d ∈ Y := h.sec11K_le (mem_sec11K_d h45 h hdL hdc)
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hnd1 : n * d * n⁻¹ ≠ 1 := fun h1 => hd1 (by
    calc d = n⁻¹ * (n * d * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have heq := zpowers_eq_of_mem_of_ne_one hc3 hnd hnd1
  have hmem : n * d * n⁻¹ ∈ Y.map (MulAut.conj n).toMonoidHom :=
    ⟨d, hdY, by simp [MulAut.conj_apply]⟩
  exact Subgroup.zpowers_le.mpr hmem (heq ▸ Subgroup.mem_zpowers c)

theorem map_conj_sec11K_eq (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {w b : G}
    (hwc : w * c * w⁻¹ = c) (hwa : w * a * w⁻¹ = a * b) (hb : b ∈ Subgroup.zpowers c) :
    (sec11K L a).map (MulAut.conj w).toMonoidHom = sec11K L a := by
  have hwC : w ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc w * c = w * c * w⁻¹ * w := by group
      _ = c * w := by rw [hwc]
  have hwH : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at hwC
    exact Subgroup.centralizer_le_normalizer _ hwC
  have hwL : L.map (MulAut.conj w).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (h.normalizer_le_normalizer_L h45 hwH)
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hbL : ∀ l ∈ L, l * b = b * l := by
    intro l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hlc : l * c = c * l := Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
    exact ((Commute.zpow_right (hlc : Commute l c) k).eq)
  rw [map_conj_sec11K, hwL, hwa, sec11K_mul_eq hbL]

theorem false_of_bcD8_of_odd_core (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hdc : d ∉ Subgroup.zpowers c) {n : G} (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c)
    (hna : n * a * n⁻¹ ∈ Subgroup.zpowers a) (hYn : Y.map (MulAut.conj n).toMonoidHom ≠ Y)
    (hodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G))))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hcA := h.mem_A
  have haA := h.a_mem
  have hc1 := h.ne_one
  have hcB : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have haB : a ∉ Subgroup.closure ({c, d} : Set G) := fun ha =>
    Item116Fusion.not_mem_innerPreimage h (Item116Fusion.closure_le_innerPreimage h hdL ha)
  have hac : a ∉ Subgroup.zpowers c := fun ha => haB (Subgroup.zpowers_le.mpr hcB ha)
  set F := Subgroup.closure ({c, a} : Set G) with hF
  have hFA : F ≤ A := by
    rw [hF, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hcA
    · exact haA
  have hFe : CFSG.Assembly.IsElemAbelian 3 F :=
    ⟨⟨⟨fun x y => Subtype.ext (hcomm _ (hFA x.2) _ (hFA y.2))⟩⟩, fun x hx => hexp x (hFA hx)⟩
  have hF9 : Nat.card F = 9 :=
    Item116Fusion.card_closure_pair_eq_nine hexp hcomm hcA haA hc1 hac
  have hcF : c ∈ F := Subgroup.subset_closure (by simp)
  obtain ⟨t, htK, ht2⟩ := exists_orderOf_eq_two_mem_sec11K h45 h hdL hdc
  have hT₀ : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hT₀1 : Subgroup.zpowers t ≠ ⊥ := fun h0 => ht1 (Subgroup.zpowers_eq_bot.mp h0)
  have htLa : t ∈ L ⊓ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le _ htK
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hFT : F ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    rw [← GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers, hF,
      Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | rfl
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLc htLa.1)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp htLa.2).symm
  have hna1 : n * a * n⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hYnL : Y.map (MulAut.conj n).toMonoidHom ∈ thetaComponentsAt 3 a := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt_Y
    rwa [MulAut.conj_apply, thetaComponentsAt_eq_of_zpowers_eq
      (zpowers_eq_of_mem_of_ne_one (hexp a haA) hna hna1)] at h1
  have hcYn := mem_map_conj_of_conj_mem_zpowers h45 h hdL hdc hnd
  have htr := Item116Fusion.exists_transvection_eq h hdL hWB hirr hdc
  refine TheoremO.false_of_charTwo_split_thetaComponents h.charTwoType hFe hF9.ge hcF hc1 hT₀
    hT₀1 hFT fun e heF hec => ?_
  obtain ⟨b, hb, he⟩ := exists_zpowers_eq_mul (hcomm c hcA a haA) (hexp a haA) heF hec
  obtain ⟨w, -, hwB, hwa⟩ := htr b (Subgroup.zpowers_le.mpr hcB hb)
  have hwc : w * c * w⁻¹ = c := hwB c hcB
  have he' : Subgroup.zpowers e = Subgroup.zpowers (w * a * w⁻¹) := by
    rw [hwa]
    exact he
  have hea : thetaComponentsAt 3 e = thetaComponentsAt 3 (w * a * w⁻¹) :=
    thetaComponentsAt_eq_of_zpowers_eq he'
  have hKw := map_conj_sec11K_eq h45 h hwc hwa hb
  refine ⟨Y.map (MulAut.conj w).toMonoidHom, ?_,
    (Y.map (MulAut.conj n).toMonoidHom).map (MulAut.conj w).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hea, ← MulAut.conj_apply]
    exact map_mem_thetaComponentsAt (MulAut.conj w) h.mem_thetaComponentsAt_Y
  · rw [hea, ← MulAut.conj_apply]
    exact map_mem_thetaComponentsAt (MulAut.conj w) hYnL
  · calc Subgroup.zpowers t ≤ sec11K L a := Subgroup.zpowers_le.mpr htK
      _ = (sec11K L a).map (MulAut.conj w).toMonoidHom := hKw.symm
      _ ≤ Y.map (MulAut.conj w).toMonoidHom := Subgroup.map_mono h.sec11K_le
  · have := Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hcYn
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwc] at this
  · intro hY
    exact hYn (Subgroup.map_injective (MulAut.conj w).injective hY).symm
  · rw [centralizer_eq_of_zpowers_eq he', card_theta_centralizer_conj]
    exact hodd

theorem false_of_bcD8_of_odd (hP2b : Item116P2b) (h45 : Sec4.Item4_5)
    (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hRG : CFSG.ABGLocalTools.IsSylowOf 3 R ⊤) (hdc : d ∉ Subgroup.zpowers c)
    (hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c))
    {n : G} (hnW : n ∈ Subgroup.normalizer (A : Set G)) (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d)
    (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c) (hna : n * a * n⁻¹ = a⁻¹)
    (hodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G))))) : False :=
  false_of_bcD8_of_odd_core h45 h hdL hWB hirr hdc hnd
    (by rw [hna]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a))
    (hP2b G A c L a R Y h d hdL hWB hirr hRG hdc hD8 n hnW hnc hnd hna) hodd

theorem exists_bcD8_of_not_mem (h : Sec11Std G A c L a R Y) {d : G}
    (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hdc : d ∉ Subgroup.zpowers c)
    (hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c))
    {w : G} (hwW : w ∈ Subgroup.normalizer (A : Set G)) {x : G} (hxA : x ∈ A)
    (hwx : x⁻¹ * (w⁻¹ * x * w) ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ n ∈ Subgroup.normalizer (A : Set G), n * c * n⁻¹ ∈ Subgroup.zpowers d ∧
      n * d * n⁻¹ ∈ Subgroup.zpowers c ∧ n * a * n⁻¹ = a⁻¹ := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA := h.a_mem
  set B := Subgroup.closure ({c, d} : Set G) with hB
  set W := Subgroup.normalizer (A : Set G) with hW
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
  have hBA : B ≤ A := by
    rw [hB, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h.mem_A
    · exact hdA
  have haB : a ∉ B := fun ha =>
    Item116Fusion.not_mem_innerPreimage h (Item116Fusion.closure_le_innerPreimage h hdL ha)
  have hconjB : ∀ g ∈ W, ∀ y ∈ B, g * y * g⁻¹ ∈ B := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hWB hg) y).mp hy
  have hwW' : w⁻¹ ∈ W := W.inv_mem hwW
  have htr := Item116Fusion.exists_transvection_eq h hdL hWB hirr hdc
  have hHW : ∀ u ∈ W, u ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      ∀ y ∈ A, y⁻¹ * (u⁻¹ * y * u) ∈ B := fun u huW huH =>
    Item116Fusion.conj_mem_of_mem_normalizer_zpowers h hdL hdc huW huH
  have hswap : w⁻¹ * c * w⁻¹⁻¹ ∈ Subgroup.zpowers d ∧ w⁻¹ * d * w⁻¹⁻¹ ∈ Subgroup.zpowers c := by
    rcases hD8 w⁻¹ hwW' with h1 | h2
    · exfalso
      apply hwx
      have hvH : w⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
        apply mem_normalizer_of_forall_conj_mem
        intro u hu
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        have hc3 : c ^ 3 = 1 := hexp c h.mem_A
        have hvc := h1.1
        rw [inv_inv] at hvc
        have hne : w⁻¹ * c * w ≠ 1 := fun h0 => h.ne_one (by
          calc c = w * (w⁻¹ * c * w) * w⁻¹ := by group
            _ = 1 := by rw [h0]; group)
        have heq := TheoremO.zpowers_eq_of_mem_of_ne_one hc3 hvc hne
        have hcm : c ∈ Subgroup.zpowers (w⁻¹ * c * w) := heq ▸ Subgroup.mem_zpowers c
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hcm
        have hwcw : w * c * w⁻¹ = c ^ j := by
          calc w * c * w⁻¹ = w * (w⁻¹ * c * w) ^ j * w⁻¹ := by rw [hj]
            _ = c ^ j := by rw [← conj_zpow, show w * (w⁻¹ * c * w) * w⁻¹ = c by group]
        rw [inv_inv, ← conj_zpow, hwcw, ← zpow_mul]
        exact Subgroup.zpow_mem_zpowers c _
      have := hHW w hwW (by
        have := Subgroup.inv_mem _ hvH
        rwa [inv_inv] at this) x hxA
      exact this
    · exact h2
  have hvaA : w⁻¹ * a * w⁻¹⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwW' a).mp haA
  obtain ⟨b, hb, k, hk3, hbk⟩ := Item116Fusion.exists_mem_closure_mul_pow h hdL hdc hvaA
  have hbA := hBA hb
  have hk2 : k = 2 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · exfalso
      apply haB
      rw [pow_zero, mul_one] at hbk
      have := hconjB w hwW _ (hbk ▸ hb)
      rwa [show w * (w⁻¹ * a * w⁻¹⁻¹) * w⁻¹ = a by group] at this
    · exfalso
      apply hwx
      refine Item116Fusion.conj_mem_of_closure hcomm hwW (Item116Fusion.closure_cda_eq h hdL hdc)
        ?_ x hxA
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      have hwB : ∀ y ∈ B, w⁻¹ * y * w ∈ B := fun y hy => by
        have := hconjB _ hwW' y hy
        rwa [inv_inv] at this
      rcases hs with rfl | rfl | rfl
      · exact B.mul_mem (B.inv_mem (Subgroup.subset_closure (by simp)))
          (hwB _ (Subgroup.subset_closure (by simp)))
      · exact B.mul_mem (B.inv_mem (Subgroup.subset_closure (by simp)))
          (hwB _ (Subgroup.subset_closure (by simp)))
      · rw [inv_inv, pow_one] at hbk
        rw [hbk, hcomm b hbA s haA, ← mul_assoc, inv_mul_cancel, one_mul]
        exact hb
    · rfl
  subst hk2
  obtain ⟨t, htW, htB, hta⟩ := htr b hb
  refine ⟨t * w⁻¹, W.mul_mem htW hwW', ?_, ?_, ?_⟩
  · have hvc := hswap.1
    rw [inv_inv] at hvc
    have hvcB : w⁻¹ * c * w ∈ B := by
      have := hconjB _ hwW' c (Subgroup.subset_closure (by simp))
      rwa [inv_inv] at this
    rw [show t * w⁻¹ * c * (t * w⁻¹)⁻¹ = t * (w⁻¹ * c * w) * t⁻¹ by group, htB _ hvcB]
    exact hvc
  · have hvd := hswap.2
    rw [inv_inv] at hvd
    have hvdB : w⁻¹ * d * w ∈ B := by
      have := hconjB _ hwW' d (Subgroup.subset_closure (by simp))
      rwa [inv_inv] at this
    rw [show t * w⁻¹ * d * (t * w⁻¹)⁻¹ = t * (w⁻¹ * d * w) * t⁻¹ by group, htB _ hvdB]
    exact hvd
  · have ha3 := hexp a haA
    have hb3 := hexp b hbA
    rw [inv_inv] at hbk
    have hab := hcomm a haA b hbA
    calc t * w⁻¹ * a * (t * w⁻¹)⁻¹ = t * (w⁻¹ * a * w) * t⁻¹ := by group
      _ = (t * b * t⁻¹) * (t * a * t⁻¹) ^ 2 := by rw [hbk, conj_pow]; group
      _ = b * (a * b) ^ 2 := by rw [htB b hb, hta]
      _ = a⁻¹ := by
        have hab' : Commute a b := hab
        rw [hab'.mul_pow 2]
        calc b * (a ^ 2 * b ^ 2) = (b * a ^ 2) * b ^ 2 := by group
          _ = (a ^ 2 * b) * b ^ 2 := by rw [(hab'.pow_left 2).eq]
          _ = a ^ 2 * b ^ 3 := by group
          _ = a⁻¹ := by
              rw [hb3, mul_one]
              exact eq_inv_of_mul_eq_one_left ((pow_succ a 2).symm.trans ha3)

end Certified

end TheoremO

section Main

@[expose] def Item116FusionE9Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G), Sec11Std G A c L a R Y → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      Subgroup.normalizer (A : Set G) ≤
          Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
        Sec21.IsIrreducibleOn
            (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})) →
          CFSG.ABGLocalTools.IsSylowOf 3 R ⊤ →
          (∀ w ∈ Subgroup.normalizer (A : Set G), (∃ k : ℕ, w ^ 3 ^ k = 1) →
            ∀ b ∈ Subgroup.closure ({c, d} : Set G), w * b * w⁻¹ = b) →
          (∀ w ∈ Subgroup.normalizer (A : Set G),
            (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
            (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c) ∨
            (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧
              w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
            (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧
              w * d * w⁻¹ ∈ Subgroup.zpowers (c * d))) →
          (d ∉ Subgroup.zpowers c →
            Subgroup.closure ({c, d, a} : Set G) = A ∧
            (∀ b ∈ Subgroup.closure ({c, d} : Set G), ∃ w ∈ Subgroup.normalizer (A : Set G),
              (∀ y ∈ Subgroup.closure ({c, d} : Set G), w * y * w⁻¹ = y) ∧
                w * a * w⁻¹ = a * b) ∧
            ∀ w ∈ Subgroup.normalizer (A : Set G),
              w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
                ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure ({c, d} : Set G)) →
          (Even (Nat.card (inSubgroup (aschbacherSolvableCore 3)
              (Subgroup.centralizer ({a} : Set G)))) ∨
            ∃ w ∈ Subgroup.normalizer (A : Set G),
              (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧
                w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
              (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧
                w * d * w⁻¹ ∈ Subgroup.zpowers (c * d))) →
            ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ A,
              x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure {c, d}

theorem item116FusionE9_of_even (hEven : Item116FusionE9Even) (hP2b : Item116P2b)
    (h45 : Sec4.Item4_5) : Item116FusionE9 := by
  intro G _ _ A c L a R Y h d hdL hWB hirr hRG h3 hsd16 hnd
  by_cases hcase : Even (Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)))) ∨
    ∃ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d))
  · exact hEven G A c L a R Y h d hdL hWB hirr hRG h3 hsd16 hnd hcase
  rw [not_or] at hcase
  obtain ⟨hodd, hnSD⟩ := hcase
  have hodd' := Nat.not_even_iff_odd.mp hodd
  have hdc := Item116Fusion.not_mem_zpowers_of_item45 h45 h hdL
  have hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c) := by
    intro w hw
    rcases hsd16 w hw with h1 | h2 | h3 | h4
    · exact Or.inl h1
    · exact Or.inr h2
    · exact absurd ⟨w, hw, Or.inl h3⟩ hnSD
    · exact absurd ⟨w, hw, Or.inr h4⟩ hnSD
  intro w hwW x hxA
  by_contra hwx
  obtain ⟨n, hnW, hnc, hnd', hna⟩ :=
    TheoremO.exists_bcD8_of_not_mem h hdL hWB hirr hdc hD8 hwW hxA hwx
  exact TheoremO.false_of_bcD8_of_odd hP2b h45 h hdL hWB hirr hRG hdc hD8 hnW hnc hnd' hna hodd'

end Main

end CFSG.RankThree.PartTwo.Sec11
