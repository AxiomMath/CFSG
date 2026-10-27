module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LL34Aut
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LL34Cover
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1E9
public import CFSG.Quasithin.Background.RonanE42Star

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.RankThreeEven (projSL)

section Gen

variable {G : Type} [Group G] [Finite G]

theorem two_pow_odd_mod_three {t : ℕ} (ht : t % 2 = 1) : 2 ^ t % 3 = 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, t = 2 * r + 1 := ⟨t / 2, by omega⟩
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

omit [Finite G] in
theorem commute_of_conj_mem_zpowers {d n : G} (hd : d ^ 3 = 1) {m : ℕ}
    (hn : n ^ 3 ^ m = 1) (hmem : n * d * n⁻¹ ∈ Subgroup.zpowers d) : n * d = d * n := by
  by_cases hd1 : d = 1
  · rw [hd1, mul_one, one_mul]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hd' : d ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact hd
  have hj' : d ^ j = d ^ (j % 3) := zpow_eq_zpow_emod j hd'
  have h0 : 0 ≤ j % 3 := Int.emod_nonneg _ (by norm_num)
  have h3 : j % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
  · exfalso
    rw [h, zpow_zero] at hj'
    have : n * d * n⁻¹ = 1 := hj.symm.trans hj'
    apply hd1
    calc d = n⁻¹ * (n * d * n⁻¹) * n := by group
      _ = 1 := by rw [this]; group
  · rw [h, zpow_one] at hj'
    calc n * d = n * d * n⁻¹ * n := by group
      _ = d * n := by rw [← hj, hj']
  · exfalso
    rw [h] at hj'
    have hx : n * d * n⁻¹ = d ^ 2 := by rw [← hj, hj', zpow_ofNat]
    have hconj : ∀ t : ℕ, n ^ t * d * (n ^ t)⁻¹ = d ^ (2 ^ t) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        calc n ^ (t + 1) * d * (n ^ (t + 1))⁻¹ = n * (n ^ t * d * (n ^ t)⁻¹) * n⁻¹ := by group
          _ = n * d ^ (2 ^ t) * n⁻¹ := by rw [ih]
          _ = (n * d * n⁻¹) ^ (2 ^ t) := by
              rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
          _ = d ^ (2 ^ (t + 1)) := by rw [hx, ← pow_mul, pow_succ, mul_comm]
    have hfix := hconj (3 ^ m)
    rw [hn, one_mul, inv_one, mul_one, pow_eq_pow_mod _ hd,
      two_pow_odd_mod_three (by rw [Nat.pow_mod]; norm_num)] at hfix
    apply hd1
    calc d = d ^ 2 * d⁻¹ := by group
      _ = 1 := by rw [← hfix, mul_inv_cancel]

omit [Finite G] in
theorem commute_of_mem_normalizer_zpowers {d n : G} (hd : d ^ 3 = 1) {m : ℕ}
    (hn : n ^ 3 ^ m = 1) (hnd : n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    n * d = d * n :=
  commute_of_conj_mem_zpowers hd hn
    ((Subgroup.mem_normalizer_iff.mp hnd d).mp (Subgroup.mem_zpowers d))

omit [Finite G] in
theorem mem_of_commute_of_maximal {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) {x : G}
    (hx3 : x ^ 3 = 1) (hxA : ∀ a ∈ A, a * x = x * a) : x ∈ A := by
  have hB := isElemAbelian_sup_zpowers hA hx3 hxA
  rw [← hmax _ hB le_sup_left]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

omit [Finite G] in
theorem mem_center_of_mem_centralizer {L : Subgroup G} {c : G} (hcL : c ∈ L)
    (hc : c ∈ Subgroup.centralizer (L : Set G)) : (⟨c, hcL⟩ : ↥L) ∈ Subgroup.center ↥L := by
  rw [Subgroup.mem_center_iff]
  intro l
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) l l.2)

omit [Finite G] in
theorem descAut_of_mem {L : Subgroup G} {l : G} (hl : l ∈ L) :
    descAut L ⟨l, Subgroup.le_normalizer hl⟩ =
      MulAut.conj (((⟨l, hl⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [descAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  rfl

omit [Finite G] in
theorem descAut_apply_of_commute {L : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (L : Set G)) {l : G} (hl : l ∈ L) (hc : n * l = l * n) :
    descAut L ⟨n, hn⟩ ((⟨l, hl⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) =
      ((⟨l, hl⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) := by
  rw [descAut_mk]
  congr 1
  apply Subtype.ext
  show n * l * n⁻¹ = l
  rw [hc, mul_inv_cancel_right]

theorem isElemAbelian_aBar {L A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hA : CFSG.Assembly.IsElemAbelian 3 A) : CFSG.Assembly.IsElemAbelian 3 (aBar hAN) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hx⟩ := (mem_aBar_iff hAN).mp x.2
    obtain ⟨b, hb, hy⟩ := (mem_aBar_iff hAN).mp y.2
    apply Subtype.ext
    show (x : MulAut (↥L ⧸ Subgroup.center ↥L)) * (y : MulAut (↥L ⧸ Subgroup.center ↥L)) =
      (y : MulAut (↥L ⧸ Subgroup.center ↥L)) * (x : MulAut (↥L ⧸ Subgroup.center ↥L))
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hab : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact hab
  · obtain ⟨a, ha, rfl⟩ := (mem_aBar_iff hAN).mp hx
    rw [← map_pow]
    have : (⟨a, hAN ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (hA.2 a ha)
    rw [this, map_one]

theorem conj_component_or_commute {L : Subgroup G} {d a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (had : a * d = d * a)
    {K : Subgroup ↥(L ⊓ Subgroup.centralizer {d})} (hK : IsComponent K) {K' : Subgroup G}
    (hK' : K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype) :
    a ∈ Subgroup.normalizer (K' : Set G) ∨
      ∀ x ∈ K', ∀ y ∈ K', a * x * a⁻¹ * y = y * (a * x * a⁻¹) := by
  subst hK'
  have had' : a⁻¹ * d = d * a⁻¹ := by
    calc a⁻¹ * d = a⁻¹ * (d * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * d) * a⁻¹ := by rw [had]
      _ = d * a⁻¹ := by group
  have hconjM : ∀ m ∈ L ⊓ Subgroup.centralizer {d},
      a * m * a⁻¹ ∈ L ⊓ Subgroup.centralizer {d} := by
    intro m hm
    rw [Subgroup.mem_inf] at hm
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp haL m).mp hm.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmd : m * d = d * m := Subgroup.mem_centralizer_singleton_iff.mp hm.2
    calc a * m * a⁻¹ * d = a * m * (a⁻¹ * d) := by group
      _ = a * m * (d * a⁻¹) := by rw [had']
      _ = a * (m * d) * a⁻¹ := by group
      _ = a * (d * m) * a⁻¹ := by rw [hmd]
      _ = a * d * m * a⁻¹ := by group
      _ = d * a * m * a⁻¹ := by rw [had]
      _ = d * (a * m * a⁻¹) := by group
  have hle : (L ⊓ Subgroup.centralizer {d}).map (MulAut.conj a).toMonoidHom ≤
      L ⊓ Subgroup.centralizer {d} := by
    rintro _ ⟨m, hm, rfl⟩
    exact hconjM m hm
  have hMa : (L ⊓ Subgroup.centralizer {d}).map (MulAut.conj a).toMonoidHom =
      L ⊓ Subgroup.centralizer {d} :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj a).injective])
  let σ : ↥(L ⊓ Subgroup.centralizer {d}) ≃* ↥(L ⊓ Subgroup.centralizer {d}) :=
    ((MulAut.conj a).subgroupMap (L ⊓ Subgroup.centralizer {d})).trans
      (MulEquiv.subgroupCongr hMa)
  have hσ : ∀ m : ↥(L ⊓ Subgroup.centralizer {d}), ((σ m : ↥(L ⊓ Subgroup.centralizer {d})) : G) =
      a * m * a⁻¹ := fun m => rfl
  have hK2 : IsComponent (K.map σ.toMonoidHom) := CFSG.LocalCores.isComponent_map_mulEquiv σ hK
  by_cases heq : K.map σ.toMonoidHom = K
  · left
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨m, hm, rfl⟩ := hx
    refine ⟨σ m, ?_, (hσ m).symm⟩
    rw [← heq]
    exact ⟨m, hm, rfl⟩
  · right
    intro x hx y hy
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨m', hm', rfl⟩ := hy
    have h := CFSG.Quasithin.RonanE42.isComponent_commute_of_ne' hK2 hK heq
      (⟨m, hm, rfl⟩ : σ m ∈ K.map σ.toMonoidHom) hm'
    have h' : ((σ m * m' : ↥(L ⊓ Subgroup.centralizer {d})) : G) =
        ((m' * σ m : ↥(L ⊓ Subgroup.centralizer {d})) : G) := congrArg Subtype.val h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hσ] at h'
    exact h'

variable {k : Type} [Field k] (hk : Nat.card k = 4)
include hk

theorem card_le_of_commute_bar {L : Subgroup G}
    (χ : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL 3 k) (hZc : Nat.card (Subgroup.center ↥L) ≤ 3)
    {y : ↥L ⧸ Subgroup.center ↥L} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) {H : Subgroup G} (hHL : H ≤ L)
    (hc : ∀ h (hh : h ∈ H), ((⟨h, hHL hh⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) * y =
      y * ((⟨h, hHL hh⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L)) : Nat.card H ≤ 27 := by
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  have hH : Nat.card (H.subgroupOf L) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  have h1 := card_map_mul_card_inf_ker π (H.subgroupOf L)
  have h2 : (H.subgroupOf L).map π ≤ Subgroup.centralizer {y} := by
    rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc h hh
  have h3 : Nat.card ((H.subgroupOf L).map π) ≤ 9 :=
    (Subgroup.card_le_of_le h2).trans (l34_card_centralizer hk χ hy3 hy1).le
  have h4 : Nat.card ((H.subgroupOf L) ⊓ π.ker : Subgroup ↥L) ≤ 3 := by
    have hker : π.ker = Subgroup.center ↥L := QuotientGroup.ker_mk' _
    rw [hker]
    exact (Subgroup.card_le_of_le inf_le_right).trans hZc
  rw [← hH, h1]
  nlinarith

end Gen

section Row


theorem row427_L34
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (eS : S ≃* projSL 3 (GaloisField 2 2)) : Row427 S := by
  intro G _ _ hG A hA hEF hθ L hL ⟨e⟩ d hdA hd1 hN hLd K hK htype
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hk : Nat.card (GaloisField 2 2) = 4 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨φ₀⟩ := KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 2)
  set χ : (↥L ⧸ Subgroup.center ↥L) ≃* projectiveSL 3 (GaloisField 2 2) :=
    (e.trans eS).trans φ₀ with hχ
  have hScard : Nat.card S = 20160 := by
    rw [Nat.card_congr (eS.trans φ₀).toEquiv, KFacts.L34.card_projectiveSL hk]
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    rank3II_4_5 G hG A (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
      (Or.inr ⟨hA.1, 3, le_rfl, by rw [hA.2]; norm_num⟩) L
      (mem_thetaComponents_of_isComponent3 hL)
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hAN hdA
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {d}).subtype :=
    ⟨_, rfl⟩
  have hK'M : K' ≤ L ⊓ Subgroup.centralizer {d} := hK' ▸ Subgroup.map_subtype_le K
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  have hK'd : K' ≤ Subgroup.centralizer {d} := hK'M.trans inf_le_right
  have eK : K ≃* K' := (K.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr hK'.symm)
  have hK'q : IsQuasisimple K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hK.1
  have hZ3 := isPGroup_center_of_isComponent hθ hL
  haveI : Group.IsPerfect ↥L := hL.1.1
  obtain ⟨hZd3, hexp⟩ := l34_cover hk hZ3
    ((e.trans eS).trans (CFSG.PGLModel.projSLEquivStatedProj 3 (GaloisField 2 2)))
  rcases htype with ⟨⟨φ⟩⟩ | ⟨-, hext⟩
  ·
    have φ' : K' ⧸ CFSG.pCore 2 K' ≃* alternatingGroup (Fin 5) :=
      (quotPCoreTwoCongr eK).symm.trans φ
    have hT : Ronan148R.IsA5Type (K' ⧸ CFSG.pCore 2 K') := ⟨φ'⟩
    obtain ⟨b, -, hK'c⟩ := card_eq_sixty_mul_pCore φ'
    have hK'60 : 60 ≤ Nat.card K' := by
      rw [hK'c]
      exact Nat.le_mul_of_pos_right 60 (by positivity)
    have hZc : Nat.card (Subgroup.center ↥L) ≤ 3 := Nat.le_of_dvd (by norm_num) hZd3
    have hd3 : d ^ 3 = 1 := hA.1.2 d hdA
    have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hZb : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
      have hZS : Subgroup.center S = ⊥ := RonanK429.center_eq_bot_of_isSimpleGroup hs hna
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      have hz' : e z ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro g
        obtain ⟨g', rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, hz g']
      rw [hZS, Subgroup.mem_bot] at hz'
      exact (map_eq_one_iff e e.injective).mp hz'
    have hconj := conj_injective_of_center hZb
    obtain ⟨f₀, hf₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 3
      (by rw [hK'c]; exact Dvd.dvd.mul_right (by norm_num) _)
    have hfK : (f₀ : G) ∈ K' := f₀.2
    have hf3 : (f₀ : G) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hf₀, pow_orderOf_eq_one, Subgroup.coe_one]
    have hf1 : (f₀ : G) ≠ 1 := by
      intro h
      have h1 : f₀ = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hf₀
      norm_num at hf₀
    have hfZ : ((⟨f₀, hK'L hfK⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) ≠ 1 := by
      intro h
      rw [QuotientGroup.eq_one_iff] at h
      apply hf1
      refine Ronan148R.eq_one_of_central_of_isA5Type hK'q hT hfK (fun x hx => ?_) hf3
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp h) ⟨x, hK'L hx⟩)
    have hfb3 : ((⟨f₀, hK'L hfK⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have h1 : (⟨f₀, hK'L hfK⟩ : ↥L) ^ 3 = 1 := Subtype.ext hf3
      rw [h1, QuotientGroup.mk_one]
    set α := descAut L ⟨d, hdN⟩ with hα
    have hρker : ∀ n : Subgroup.normalizer (L : Set G),
        descAut L n = 1 ↔ (n : G) ∈ Subgroup.centralizer (L : Set G) := descAut_eq_one_iff hL.1.1
    set I := (MulAut.conj : (↥L ⧸ Subgroup.center ↥L) →* MulAut (↥L ⧸ Subgroup.center ↥L)).range
      with hI
    have hαI : α ∉ I := by
      rintro ⟨y, hy⟩
      have hy1 : y ≠ 1 := by
        rintro rfl
        rw [map_one] at hy
        have hdC := (hρker ⟨d, hdN⟩).mp hy.symm
        apply hLd
        intro l hl
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hdC l hl)
      have hy3 : y ^ 3 = 1 := by
        apply hconj
        rw [map_pow, hy, map_one, hα, ← map_pow]
        have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext hd3
        rw [h1, map_one]
      have h27 := card_le_of_commute_bar hk χ hZc hy3 hy1 hK'L (fun h hh => by
        have h1 := descAut_apply_of_commute hdN (hK'L hh)
          (Subgroup.mem_centralizer_singleton_iff.mp (hK'd hh)).symm
        rw [← hα, ← hy, MulAut.conj_apply] at h1
        calc ((⟨h, hK'L hh⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) * y
            = y * ((⟨h, hK'L hh⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) * y⁻¹ * y := by rw [h1]
          _ = y * ((⟨h, hK'L hh⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) := by group)
      omega
    have hAK' : A ≤ Subgroup.normalizer (K' : Set G) := by
      intro a ha
      rcases conj_component_or_commute (hAN ha) (hAcomm a ha d hdA) hK hK' with h | h
      · exact h
      · exfalso
        set Ka : Subgroup G := K'.map (MulAut.conj a).toMonoidHom with hKa
        have hKaL : Ka ≤ L := by
          rintro _ ⟨x, hx, rfl⟩
          exact (Subgroup.mem_normalizer_iff.mp (hAN ha) x).mp (hK'L hx)
        have hKac : Nat.card Ka = Nat.card K' :=
          Subgroup.card_map_of_injective (MulAut.conj a).injective
        have h27 := card_le_of_commute_bar hk χ hZc hfb3 hfZ hKaL (fun z hz => by
          obtain ⟨x, hx, rfl⟩ := hz
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          exact Subtype.ext (h x hx _ hfK))
        omega
    obtain ⟨U, -, hU1, hU2, hAU⟩ := exists_sylow_two_normalized φ' hAK'
      (IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num))
    have hAE : A ∈ partTwoE G := ⟨hA.1, hA.2, U, hU1, hU2, hAU⟩
    have hAF : A ∈ partTwoF G := hEF ▸ hAE
    have habs : ∀ x : G, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A :=
      fun x hx3 hxA => mem_of_commute_of_maximal hA.1 hAF.2.1 hx3 hxA
    set B := aBar hAN with hB
    have hBab : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_aBar hAN hA.1
    have hαB : α ∈ B := descAut_mem_aBar hAN hdA
    have hα1 : α ≠ 1 := fun h => hαI ⟨1, by rw [map_one, h]⟩
    have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hBab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hB9 : Nat.card B = 9 := by
      have hBp : IsPGroup 3 B := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hBab.2 x x.2)⟩
      obtain ⟨m, hm⟩ := hBp.exists_card_eq
      have hle := l34_card_le_nine hk χ hBab
      rw [hm] at hle
      have hm2 : m ≤ 2 := by
        by_contra hcon
        have : 3 ^ 3 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases m
      · exfalso
        have hB1 : B = ⊥ := Subgroup.card_eq_one.mp (by rw [hm, pow_zero])
        rw [hB1, Subgroup.mem_bot] at hαB
        exact hα1 hαB
      · exfalso
        have hoα : orderOf α = 3 := orderOf_eq_prime (hBab.2 α hαB) hα1
        have hBz : Subgroup.zpowers α = B := Subgroup.eq_of_le_of_card_ge
          (Subgroup.zpowers_le.mpr hαB) (by rw [hm, Nat.card_zpowers, hoα, pow_one])
        have hAc : ∀ a ∈ A, ∀ x ∈ K', a * x = x * a := by
          intro a ha x hx
          have hρa : descAut L ⟨a, hAN ha⟩ ∈ Subgroup.zpowers α := hBz ▸ descAut_mem_aBar hAN ha
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hρa
          have h1 : descAut L (((⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ i)⁻¹ *
              ⟨a, hAN ha⟩) = 1 := by
            rw [map_mul, map_inv, map_zpow, ← hα, hi, inv_mul_cancel]
          have hcC : (d ^ i)⁻¹ * a ∈ Subgroup.centralizer (L : Set G) := (hρker _).mp h1
          have hxd : Commute x d := Subgroup.mem_centralizer_singleton_iff.mp (hK'd hx)
          have hxc : Commute x ((d ^ i)⁻¹ * a) := (Subgroup.mem_centralizer_iff.mp hcC x (hK'L hx))
          have ha' : a = d ^ i * ((d ^ i)⁻¹ * a) := by group
          rw [ha']
          exact ((hxd.zpow_right i).mul_right hxc).eq.symm
        have hfA : (f₀ : G) ∈ A := habs _ hf3 (fun a ha => hAc a ha _ hfK)
        apply hf1
        exact Ronan148R.eq_one_of_central_of_isA5Type hK'q hT hfK
          (fun x hx => (hAc _ hfA x hx).symm) hf3
      · rw [hm]
        norm_num
    have hZA : ∀ z : ↥L, z ∈ Subgroup.center ↥L → (z : G) ∈ A := by
      intro z hz
      have hz3 : z ^ 3 = 1 := by
        have h1 : orderOf (⟨z, hz⟩ : Subgroup.center ↥L) ∣ 3 := (orderOf_dvd_natCard _).trans hZd3
        exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp h1)
      have hz3' : (z : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hz3, Subgroup.coe_one]
      refine habs _ hz3' (fun a ha => ?_)
      have hwL : a * z * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hAN ha) z).mp z.2
      have hwZ : (⟨a * z * a⁻¹, hwL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        show (l : G) * (a * z * a⁻¹) = a * z * a⁻¹ * l
        have hl' : a⁻¹ * l * a ∈ L := by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hAN ha)) l).mp l.2
          rwa [inv_inv] at this
        have hzl : (a⁻¹ * l * a) * (z : G) = z * (a⁻¹ * l * a) :=
          congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨a⁻¹ * l * a, hl'⟩)
        calc (l : G) * (a * z * a⁻¹) = a * ((a⁻¹ * l * a) * (z : G)) * a⁻¹ := by group
          _ = a * ((z : G) * (a⁻¹ * l * a)) * a⁻¹ := by rw [hzl]
          _ = a * z * a⁻¹ * l := by group
      have hmem : a * z * a⁻¹ ∈ Subgroup.zpowers (z : G) := by
        by_cases hz1 : (z : G) = 1
        · rw [hz1, mul_one, mul_inv_cancel]
          exact Subgroup.one_mem _
        · have hZg : Subgroup.zpowers (z : G) = (Subgroup.center ↥L).map L.subtype := by
            refine Subgroup.eq_of_le_of_card_ge ?_ ?_
            · rw [Subgroup.zpowers_le]
              exact ⟨z, hz, rfl⟩
            · rw [Subgroup.card_map_of_injective L.subtype_injective, Nat.card_zpowers,
                orderOf_eq_prime hz3' hz1]
              exact hZc
          rw [hZg]
          exact ⟨_, hwZ, rfl⟩
      exact commute_of_conj_mem_zpowers hz3' (m := 1) (by rw [pow_one]; exact hA.1.2 a ha) hmem
    obtain ⟨hBI3, hdec⟩ := inf_inn_card_eq_three hk χ hZb hBab hB9 hαB hαI
    obtain ⟨ebar, he, he1⟩ : ∃ x ∈ B ⊓ I, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : B ⊓ I = ⊥ := eq_bot_iff.mpr fun x hx => hcon x hx
      rw [h1, Subgroup.card_bot] at hBI3
      norm_num at hBI3
    have he3 : ebar ^ 3 = 1 := hBab.2 _ he.1
    have hoe : orderOf ebar = 3 := orderOf_eq_prime he3 he1
    have hBIz : B ⊓ I = Subgroup.zpowers ebar :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he)
        (by rw [hBI3, Nat.card_zpowers, hoe])).symm
    obtain ⟨xb, hxb⟩ := he.2
    obtain ⟨l₂, rfl⟩ := QuotientGroup.mk_surjective xb
    have hρl₂ : descAut L ⟨l₂, Subgroup.le_normalizer l₂.2⟩ = ebar := by
      rw [descAut_of_mem l₂.2]
      exact hxb
    have hl₂N : (l₂ : G) ∈ Subgroup.normalizer (A : Set G) := by
      apply Subgroup.mem_normalizer_fintype
      intro a ha
      have hcL : (l₂ : G) * a * (l₂ : G)⁻¹ * a⁻¹ ∈ L := by
        have h1 : a * (l₂ : G)⁻¹ * a⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp (inv_mem l₂.2)
        have h2 : (l₂ : G) * a * (l₂ : G)⁻¹ * a⁻¹ = l₂ * (a * (l₂ : G)⁻¹ * a⁻¹) := by group
        rw [h2]
        exact L.mul_mem l₂.2 h1
      have hcρ : descAut L ⟨(l₂ : G) * a * (l₂ : G)⁻¹ * a⁻¹, Subgroup.le_normalizer hcL⟩ = 1 := by
        have h1 : (⟨(l₂ : G) * a * (l₂ : G)⁻¹ * a⁻¹, Subgroup.le_normalizer hcL⟩ :
            Subgroup.normalizer (L : Set G)) = ⟨l₂, Subgroup.le_normalizer l₂.2⟩ * ⟨a, hAN ha⟩ *
            (⟨l₂, Subgroup.le_normalizer l₂.2⟩)⁻¹ * (⟨a, hAN ha⟩)⁻¹ := Subtype.ext rfl
        rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hρl₂,
          hBcomm _ he.1 _ (descAut_mem_aBar hAN ha)]
        group
      have hcA := hZA _ (mem_center_of_mem_centralizer hcL ((hρker _).mp hcρ))
      have h3 : (l₂ : G) * a * (l₂ : G)⁻¹ = ((l₂ : G) * a * (l₂ : G)⁻¹ * a⁻¹) * a := by group
      rw [h3]
      exact A.mul_mem hcA ha
    have hl₂3 : (l₂ : G) ^ 3 = 1 := by
      have h1 : (l₂ : ↥L ⧸ Subgroup.center ↥L) ^ 3 = 1 := by
        apply hconj
        rw [map_pow, hxb, he3, map_one]
      have h2 : l₂ ^ 3 ∈ Subgroup.center ↥L := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        exact h1
      rw [← Subgroup.coe_pow, hexp l₂ h2, Subgroup.coe_one]
    have hl₂d : Commute (l₂ : G) d :=
      commute_of_mem_normalizer_zpowers hd3 (m := 1) (by rw [pow_one]; exact hl₂3) (hN hl₂N)
    have hl₂A : (l₂ : G) ∈ A := by
      refine habs _ hl₂3 (fun a ha => ?_)
      obtain ⟨i, hi⟩ := hdec _ (descAut_mem_aBar hAN ha)
      have hiB : α ^ i * descAut L ⟨a, hAN ha⟩ ∈ B ⊓ I :=
        ⟨B.mul_mem (B.zpow_mem hαB i) (descAut_mem_aBar hAN ha), hi⟩
      rw [hBIz] at hiB
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hiB
      have h1 : descAut L (((⟨l₂, Subgroup.le_normalizer l₂.2⟩ :
          Subgroup.normalizer (L : Set G)) ^ j)⁻¹ *
          (⟨d, hdN⟩ ^ i * ⟨a, hAN ha⟩)) = 1 := by
        rw [map_mul, map_inv, map_zpow, map_mul, map_zpow, hρl₂, ← hα, ← hj, inv_mul_cancel]
      have hcC : ((l₂ : G) ^ j)⁻¹ * (d ^ i * a) ∈ Subgroup.centralizer (L : Set G) :=
        (hρker _).mp h1
      have hl₂c : Commute (l₂ : G) (((l₂ : G) ^ j)⁻¹ * (d ^ i * a)) :=
        ((Subgroup.mem_centralizer_iff.mp hcC) _ l₂.2)
      have hac : a = d ^ (-i) * ((l₂ : G) ^ j * (((l₂ : G) ^ j)⁻¹ * (d ^ i * a))) := by group
      rw [hac]
      exact ((hl₂d.zpow_right (-i)).mul_right ((Commute.self_zpow _ j).mul_right hl₂c)).eq.symm
    have hPe : ∀ l : G, ∀ hl : l ∈ L, descAut L ⟨l, Subgroup.le_normalizer hl⟩ ∈ B → l ∈ A := by
      intro l hl hlB
      have hlI : descAut L ⟨l, Subgroup.le_normalizer hl⟩ ∈ B ⊓ I :=
        ⟨hlB, by rw [descAut_of_mem hl]; exact ⟨_, rfl⟩⟩
      rw [hBIz] at hlI
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hlI
      have h1 : ((⟨l, hl⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) =
          (l₂ : ↥L ⧸ Subgroup.center ↥L) ^ j := by
        apply hconj
        rw [map_zpow, hxb, hj, descAut_of_mem hl]
      have h2 : (l₂ ^ j)⁻¹ * ⟨l, hl⟩ ∈ Subgroup.center ↥L := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_zpow, ← h1, inv_mul_cancel]
      have h3 := hZA _ h2
      have h4 : l = (l₂ : G) ^ j * (((l₂ ^ j)⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
      rw [h4]
      exact A.mul_mem (A.zpow_mem hl₂A j) h3
    refine false_of_inner_commute hk χ hZb hBab hB9 hαB hαI (fun x hx3 hxN => ?_)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    have hρy : descAut L ⟨y, Subgroup.le_normalizer y.2⟩ =
        MulAut.conj (y : ↥L ⧸ Subgroup.center ↥L) := by
      rw [descAut_of_mem y.2]
    have hy3 : (y : G) ^ 3 = 1 := by
      have h2 : y ^ 3 ∈ Subgroup.center ↥L := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        exact hx3
      rw [← Subgroup.coe_pow, hexp y h2, Subgroup.coe_one]
    have hyN : (y : G) ∈ Subgroup.normalizer (A : Set G) := by
      apply Subgroup.mem_normalizer_fintype
      intro a ha
      have hcL : (y : G) * a * (y : G)⁻¹ * a⁻¹ ∈ L := by
        have h1 : a * (y : G)⁻¹ * a⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp (inv_mem y.2)
        have h2 : (y : G) * a * (y : G)⁻¹ * a⁻¹ = y * (a * (y : G)⁻¹ * a⁻¹) := by group
        rw [h2]
        exact L.mul_mem y.2 h1
      have hcB : descAut L ⟨(y : G) * a * (y : G)⁻¹ * a⁻¹, Subgroup.le_normalizer hcL⟩ ∈ B := by
        have h1 : (⟨(y : G) * a * (y : G)⁻¹ * a⁻¹, Subgroup.le_normalizer hcL⟩ :
            Subgroup.normalizer (L : Set G)) = ⟨y, Subgroup.le_normalizer y.2⟩ * ⟨a, hAN ha⟩ *
            (⟨y, Subgroup.le_normalizer y.2⟩)⁻¹ * (⟨a, hAN ha⟩)⁻¹ := Subtype.ext rfl
        rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv, hρy]
        refine B.mul_mem ?_ (B.inv_mem (descAut_mem_aBar hAN ha))
        exact (Subgroup.mem_normalizer_iff.mp hxN _).mp (descAut_mem_aBar hAN ha)
      have hcA := hPe _ hcL hcB
      have h3 : (y : G) * a * (y : G)⁻¹ = ((y : G) * a * (y : G)⁻¹ * a⁻¹) * a := by group
      rw [h3]
      exact A.mul_mem hcA ha
    have hyd : (y : G) * d = d * y :=
      commute_of_mem_normalizer_zpowers hd3 (m := 1) (by rw [pow_one]; exact hy3) (hN hyN)
    have h1 : descAut L (⟨y, Subgroup.le_normalizer y.2⟩ * ⟨d, hdN⟩) =
        descAut L (⟨d, hdN⟩ * ⟨y, Subgroup.le_normalizer y.2⟩) := by
      congr 1
      exact Subtype.ext hyd
    rw [map_mul, map_mul, hρy] at h1
    exact h1
  ·
    obtain ⟨N, _, ⟨eN⟩, ⟨eQ⟩⟩ := hext
    have hON' : Nat.card ((K ⧸ CFSG.pCore 2 K) ⧸ N) = 460815505920 := by
      rw [Nat.card_congr eQ.toEquiv, CFSG.Sporadic.ON.card_ON]
    have h1 : 19 * 31 * 343 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hON']
      exact Dvd.dvd.mul_right (by norm_num) _
    have h2 : 19 * 31 * 343 ∣ Nat.card L := by
      refine (h1.trans (Subgroup.card_quotient_dvd_card _)).trans ?_
      rw [Nat.card_congr eK.toEquiv]
      exact Subgroup.card_dvd_of_le hK'L
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L),
      Nat.card_congr e.toEquiv, hScard] at h2
    have h3 : 19 * 31 * 343 ∣ 20160 * 3 := h2.trans (Nat.mul_dvd_mul_left _ hZd3)
    norm_num at h3

theorem rowOf427_L34
    : RowOf427 (projSL 3 (GaloisField 2 2)) := by
  intro S _ _ hs hna ⟨eSX⟩
  exact row427_L34 hs hna eSX

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
