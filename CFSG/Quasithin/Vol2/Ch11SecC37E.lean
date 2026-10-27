module

public import CFSG.Quasithin.Vol2.Ch11SecC37Fix
public import CFSG.Quasithin.Vol2.Ch11SecCFacts3
public import CFSG.Quasithin.Vol2.Ch11SecCB51Ord
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecBBasic
public import CFSG.Quasithin.Vol2.Ch11SecC37D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.normalizer (A : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx) (Subgroup.inv_mem _ hg)
  · intro hx
    have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hx) hg
    simpa [mul_assoc] using this

omit [Finite G] in
theorem le_normalizer_zpowers {X : Subgroup G} {z : G} (hX : ∀ x ∈ X, x * z = z * x) :
    X ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  have key : ∀ x ∈ X, ∀ k : ℤ, x * z ^ k * x⁻¹ = z ^ k := by
    intro x hx k
    have h1 : x * z * x⁻¹ = z := by rw [hX x hx, mul_inv_cancel_right]
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, (key x hx k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h2 : x * h * x⁻¹ = x * z ^ k * x⁻¹ := by rw [key x hx k, hk]
    exact (mul_left_cancel (mul_right_cancel h2)).symm

theorem exists_coprime_orderOf_pow {p : ℕ} (hp : p.Prime) (x : G) :
    ∃ e : ℕ, Nat.Coprime (orderOf (x ^ p ^ e)) p := by
  suffices h : ∀ m : ℕ, ∀ y : G, orderOf y = m → ∃ e : ℕ, Nat.Coprime (orderOf (y ^ p ^ e)) p from
    h _ x rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro y hy
    by_cases hd : p ∣ m
    · have hpos : 0 < orderOf y := orderOf_pos y
      have h2 : orderOf (y ^ p) = m / p := by
        rw [orderOf_pow_of_dvd hp.ne_zero (hy ▸ hd), hy]
      obtain ⟨e, he⟩ := ih (m / p) (Nat.div_lt_self (by omega) hp.one_lt) (y ^ p) h2
      refine ⟨e + 1, ?_⟩
      rwa [pow_succ', pow_mul]
    · exact ⟨0, by rw [pow_zero, pow_one, hy]; exact (Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd))⟩

omit [Finite G] in
theorem d0Of_le_self (D : Subgroup G) : d0Of D ≤ D :=
  sup_le (opResidual_le 3 D) ((Subgroup.closure_le _).mpr fun _ hx =>
    CFSG.LieType.BorelTits.pCoreOf_le 3 D hx.1)

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem le_inf_M_of_lt (h331 : Stmt3_3_1) {Y : Subgroup G} (hTY : T ≤ Y) (hYH : Y < H) :
    Y ≤ H ⊓ Subgroup.normalizer (L : Set G) := by
  have hU := SecA.isUniqueMaxOver_of_isHStar h331 s.hyp s.h31.hstar
  obtain ⟨N, hN, hYN⟩ := exists_isMaxSubgroupIn hYH
  rw [(isUniqueMaxOver_iff.mp hU).2.2 N hN (hTY.trans hYN)] at hYN
  exact hYN

theorem exists_phi (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      ∃ φ : ↥(oTwoUpper H) →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective φ ∧
        ∀ y, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 (oTwoUpper H) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := oTwoUpper_data h1135 h1136 s.hyp s.hV₁ s.h31 s.hnot
  refine ⟨F, inferInstance, inferInstance, hF, e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun y => ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [pCore_eq_subgroupOf, Subgroup.mem_subgroupOf]

theorem pCoreOf_K_le_T : pCoreOf 2 (oTwoUpper H) ≤ T :=
  (F7.pCoreOf_mono_of_le_normalizer (oTwoUpper_le H) (le_normalizer_oTwoUpper H)).trans
    (F7.isSylowTwoOf_pCoreOf_le s.sylow)

theorem card_image_T {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    {φ : ↥(oTwoUpper H) →* Matrix.SpecialLinearGroup (Fin 2) F} (hφs : Function.Surjective φ) :
    IsPGroup 2 ↥((T.subgroupOf (oTwoUpper H)).map φ) ∧
      Nat.card ↥((T.subgroupOf (oTwoUpper H)).map φ) = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hS'2 : IsPGroup 2 ↥((T.subgroupOf (oTwoUpper H)).map φ) := by
    refine IsPGroup.map ?_ φ
    exact (s.hyp.fsu.sylow.1.to_le (inf_le_left : T ⊓ oTwoUpper H ≤ T)).of_equiv
      ((Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ oTwoUpper H ≤ oTwoUpper H)).symm.trans
        (MulEquiv.subgroupCongr (by ext x; simp [Subgroup.mem_subgroupOf])))
  refine ⟨hS'2, ?_⟩
  have hodd : ¬ 2 ∣ (T.subgroupOf (oTwoUpper H)).index := by
    have h3 := F7.isSylowTwoOf_odd_relIndex (F7.isSylowTwoOf_inf_normal s.sylow hKH
      (s.h31.hstar.1.1.trans (le_normalizer_oTwoUpper H)))
    have h4 : (T ⊓ oTwoUpper H).relIndex (oTwoUpper H) = T.relIndex (oTwoUpper H) := by
      rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.inf_subgroupOf_right]
    rw [h4] at h3
    exact h3
  obtain ⟨a, ha⟩ := hS'2.exists_card_eq
  have h1 := two_pow_dvd_card_map hF hφs hodd
  rw [ha] at h1
  have h2 : 2 ^ a ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← ha, ← hF, ← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd2 : Odd ((2 ^ n) ^ 2 - 1) := by
    rw [← pow_mul]
    exact SecA.odd_two_pow_sub_one (by have := s.two_le; omega)
  have h3 := B51.le_of_two_pow_dvd hodd2 h2
  have h4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  rw [ha, show a = n by omega]

theorem mem_normalizer_of_image {F : Type} [Field F] [Finite F]
    {φ : ↥(oTwoUpper H) →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hφker : ∀ y, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 (oTwoUpper H)) {x : ↥(oTwoUpper H)}
    (hx : φ x ∈ Subgroup.normalizer (((T.subgroupOf (oTwoUpper H)).map φ : Subgroup _) :
      Set (Matrix.SpecialLinearGroup (Fin 2) F))) :
    (x : G) ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
  have hpre : ∀ y : ↥(oTwoUpper H), φ y ∈ (T.subgroupOf (oTwoUpper H)).map φ → (y : G) ∈ T := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := hy
    have h1 : φ (y * t⁻¹) = 1 := by rw [map_mul, map_inv, hty, mul_inv_cancel]
    have h2 := s.pCoreOf_K_le_T ((hφker _).mp h1)
    have : (y : G) = ((y * t⁻¹ : ↥(oTwoUpper H)) : G) * t := by simp
    rw [this]
    exact T.mul_mem h2 (Subgroup.mem_subgroupOf.mp ht)
  have key : ∀ y : ↥(oTwoUpper H), φ y ∈ Subgroup.normalizer
        (((T.subgroupOf (oTwoUpper H)).map φ : Subgroup _) : Set _) → ∀ t ∈ T ⊓ oTwoUpper H,
      (y : G) * t * (y : G)⁻¹ ∈ T ⊓ oTwoUpper H := by
    intro y hy t ht
    have hmem : φ (y * ⟨t, ht.2⟩ * y⁻¹) ∈ (T.subgroupOf (oTwoUpper H)).map φ := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy _).mp
        ⟨⟨t, ht.2⟩, Subgroup.mem_subgroupOf.mpr ht.1, rfl⟩
    exact ⟨hpre _ hmem, (oTwoUpper H).mul_mem ((oTwoUpper H).mul_mem y.2 ht.2)
      ((oTwoUpper H).inv_mem y.2)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨key x hx t, fun ht => ?_⟩
  have := key x⁻¹ (by rw [map_inv]; exact Subgroup.inv_mem _ hx) _ ht
  simpa [mul_assoc] using this

theorem hall_ne_bot (h331 : Stmt3_3_1) (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6)
    (hSN : FactSL2SylowNormalizer) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    D ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, φ, hφs, hφker⟩ := s.exists_phi h1135 h1136
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    s.T_le.trans (le_normalizer_oTwoUpper H)
  obtain ⟨hS'2, hcard⟩ := s.card_image_T hF hφs
  obtain ⟨hNt, c, hcN, hc⟩ := hSN F n s.two_le hF _ hS'2 hcard
  obtain ⟨y, rfl⟩ := hφs c
  have hyN := s.mem_normalizer_of_image hφker hcN
  set NK : Subgroup G := oTwoUpper H ⊓
    Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) with hNK
  have hmapN : ∀ x : ↥(oTwoUpper H), (x : G) ∈ NK →
      φ x ∈ Subgroup.normalizer
        (((T.subgroupOf (oTwoUpper H)).map φ : Subgroup _) : Set _) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨x * t * x⁻¹, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact ((Subgroup.mem_normalizer_iff.mp hx.2 t).mp ⟨Subgroup.mem_subgroupOf.mp ht, t.2⟩).1
    · intro hz
      obtain ⟨t, ht, htz⟩ := hz
      refine ⟨x⁻¹ * t * x, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx.2) t).mp
          ⟨Subgroup.mem_subgroupOf.mp ht, t.2⟩
        simpa [mul_assoc] using this.1
      · rw [map_mul, map_mul, map_inv, htz]
        group
  have hTNK : T ≤ Subgroup.normalizer (NK : Set G) := by
    intro t ht
    have htK := hTK ht
    have htTK : t ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
      F7.mem_normalizer_inf (Subgroup.le_normalizer ht) htK
    exact F7.mem_normalizer_inf htK (mem_normalizer_normalizer htTK)
  have hYH : NK ⊔ T < H := by
    refine lt_of_le_of_ne (sup_le (inf_le_left.trans hKH) s.T_le) fun hY => hNt ?_
    rw [eq_top_iff]
    intro z _
    obtain ⟨k, rfl⟩ := hφs z
    have hk : (k : G) ∈ NK ⊔ T := hY.symm ▸ hKH k.2
    obtain ⟨a, ha, t, ht, hat⟩ := mem_sup_of_le_normalizer hTNK hk
    have htK : t ∈ oTwoUpper H := by
      have : t = a⁻¹ * k := by rw [hat]; group
      rw [this]
      exact (oTwoUpper H).mul_mem ((oTwoUpper H).inv_mem ha.1) k.2
    have htNK : t ∈ NK := ⟨htK, Subgroup.le_normalizer ⟨ht, htK⟩⟩
    exact hmapN k (hat ▸ NK.mul_mem ha htNK)
  have hyM : (y : G) ∈ H ⊓ Subgroup.normalizer (L : Set G) :=
    s.le_inf_M_of_lt h331 le_sup_right hYH (Subgroup.mem_sup_left ⟨y.2, hyN⟩)
  intro hD1
  obtain ⟨k, hk⟩ := hD.2.2
  rw [hD1, Subgroup.relIndex_bot_left] at hk
  have hyo : orderOf (⟨y, hyM⟩ : ↥(H ⊓ Subgroup.normalizer (L : Set G))) ∣ 2 ^ k :=
    hk ▸ orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hyo
  have hco : 2 ^ n - 1 ∣ 2 ^ k := by
    rw [← hc]
    refine (orderOf_map_dvd φ y).trans ?_
    rw [← Subgroup.orderOf_coe]
    exact hyo
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hco
  have hodd2 : Odd (2 ^ n - 1) := SecA.odd_two_pow_sub_one (by have := s.two_le; omega)
  rw [hj] at hodd2
  rcases j with _ | j
  · have h1 : 2 ^ n - 1 = 1 := by rw [hj, pow_zero]
    have h2 : 4 ≤ 2 ^ n := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) s.two_le
    omega
  · exact absurd hodd2 (by rw [Nat.odd_iff, pow_succ]; simp)

theorem exists_mem_d0Of (h331 : Stmt3_3_1) (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6)
    (hSN : FactSL2SylowNormalizer) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    ∃ d ∈ d0Of D, d ∈ oTwoUpper H ∧ Odd (orderOf d) ∧
      d ∉ Subgroup.centralizer (VZ T H : Set G) := by
  have hD1 := s.hall_ne_bot h331 h1135 h1136 hSN hD
  obtain ⟨d, hdD₀, hd1⟩ : ∃ d ∈ d0Of D, d ≠ 1 := by
    by_cases h3 : ∀ y ∈ D, ∃ k : ℕ, orderOf y = 3 ^ k
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hD3 : IsPGroup 3 ↥D := fun y => by
        obtain ⟨k, hk⟩ := h3 y y.2
        exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, ← hk, pow_orderOf_eq_one]; rfl)⟩
      have hpc : D ≤ pCoreOf 3 D :=
        CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 3 D D le_rfl
          (by rw [Subgroup.subgroupOf_self]; infer_instance) hD3
      obtain ⟨a, ha⟩ := hD3.exists_card_eq
      have ha1 : a ≠ 0 := by
        rintro rfl
        rw [pow_zero] at ha
        exact hD1 (Subgroup.card_eq_one.mp ha)
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 3
        (by rw [ha]; exact dvd_pow_self 3 ha1)
      refine ⟨y, Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hpc y.2, ?_⟩), ?_⟩
      · rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
      · intro hy1
        have : y = 1 := Subtype.ext hy1
        rw [this, orderOf_one] at hy
        norm_num at hy
    · push Not at h3
      obtain ⟨y, hyD, hy⟩ := h3
      obtain ⟨e, he⟩ := exists_coprime_orderOf_pow Nat.prime_three y
      refine ⟨y ^ 3 ^ e, Subgroup.mem_sup_left (Subgroup.subset_closure
        ⟨D.pow_mem hyD _, he⟩), fun h1 => ?_⟩
      have h2 := orderOf_dvd_of_pow_eq_one h1
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
      exact hy k hk
  have hdD : d ∈ D := d0Of_le_self D hdD₀
  have hdodd : Odd (orderOf d) := hD.2.1.of_dvd_nat (by
    rw [← Subgroup.orderOf_mk d hdD]
    exact orderOf_dvd_natCard _)
  have hdK : d ∈ oTwoUpper H := mem_oTwoUpper_of_odd (hD.1 hdD).1 hdodd
  refine ⟨d, hdD₀, hdK, hdodd, fun hdV => hd1 ?_⟩
  have h1 : d ∈ oTwoUpper H ⊓ Subgroup.centralizer (VZ T H : Set G) := ⟨hdK, hdV⟩
  rw [inf_centralizer_VZ_eq h1135 h1136 s.hyp s.hV₁ s.h31 s.hnot] at h1
  have h2 := pow_eq_one_of_mem_pGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hdodd
    (m := 1) (by rwa [pow_one])
  rwa [pow_one] at h2

theorem Z_inf_centralizer_L (hJ : L = ⁅L, thompsonJ T⁆) (hG16 : ASInputs.AS_G_1_6)
    (hAS : FactAStarSylow) (hFPF : FactSL2NatFPF) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1104 : Stmt11_0_4)
    (h1134 : Stmt11_3_4) (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) (h331 : Stmt3_3_1)
    (hSN : FactSL2SylowNormalizer) (hB : FactSL2Borel) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨d, hdD₀, hdK, hdodd, hdV⟩ := s.exists_mem_d0Of h331 h1135 h1136 hSN hD
  have hdL : d ∈ L :=
    d0Of_le h1104 h1134 h1135 h1136 hB s.hyp hJ s.hV₁ s.h31 s.hnot s.hAT s.hAC hD hdD₀
  rw [eq_bot_iff]
  rintro z ⟨hzZ, hzL⟩
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hzV : z ∈ VZ T H := Z_le_VZ T H hzZ
  have hfix : d * z * d⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp hzL d hdL, mul_inv_cancel_right]
  have hzK := s.mem_centralizer_of_fix hG16 hAS hFPF hF h1102 hG2 h1122 h1134 h1135 h1136 hdK
    hdodd hdV hzV hfix
  have hz2 : z ^ 2 = 1 := s.isElemAbelian_VZ.2 z hzV
  have hP : IsPGroup 2 ↥(Subgroup.zpowers z) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one]
  have hP1 : Subgroup.zpowers z ≠ ⊥ := by
    intro h
    exact hz1 ((Subgroup.zpowers_eq_bot).mp h)
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine sup_le (le_normalizer_zpowers fun x hx => ?_) (le_normalizer_zpowers fun x hx => ?_)
    · exact (Subgroup.mem_centralizer_iff.mp hzL x hx)
    · exact (Subgroup.mem_centralizer_iff.mp (Z_le_center T hzZ).2 x hx)
  have hNM := SecA.normalizer_le_of_isPGroup h331 s.hyp hP hP1 hLT
  refine s.K_not_le_M ((le_normalizer_zpowers fun x hx => ?_).trans hNM)
  exact (Subgroup.mem_centralizer_iff.mp hzK x hx)

theorem fsuV_inf_centralizer_L (hJ : L = ⁅L, thompsonJ T⁆) (hG16 : ASInputs.AS_G_1_6)
    (hAS : FactAStarSylow) (hFPF : FactSL2NatFPF) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1104 : Stmt11_0_4)
    (h1134 : Stmt11_3_4) (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) (h331 : Stmt3_3_1)
    (hSN : FactSL2SylowNormalizer) (hB : FactSL2Borel) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hZ := s.Z_inf_centralizer_L hJ hG16 hAS hFPF hF h1102 hG2 h1122 h1104 h1134 h1135 h1136
    h331 hSN hB hD
  by_contra hne
  have hT2 : IsPGroup 2 ↥T := s.hyp.fsu.sylow.1
  have hVT : fsuV T I ≤ T := SecA.fsuV_le_T s.hyp
  have hCT : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤ T := inf_le_left.trans hVT
  have hTC : T ≤ Subgroup.normalizer
      ((fsuV T I ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := fun t ht =>
    F7.mem_normalizer_inf (SecA.T_le_normalizer_fsuV T I ht)
      (le_normalizer_centralizer s.hyp.normal ht)
  have h1 := SecB.inf_centralizer_ne_bot hT2 hCT hTC hne
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  have huZ : (u : G) ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hVT hu.1.1, hu.2⟩, (SecA.isElemAbelian_fsuV s.hyp).2 u hu.1.1⟩
  have : (u : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨huZ, hu.1.2⟩
  rw [hZ, Subgroup.mem_bot] at this
  exact hu1 (Subtype.ext this)

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
