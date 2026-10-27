module

public import CFSG.Quasithin.H13.L32A727a
public import CFSG.Quasithin.EmptyFaithful.S146G2

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem modO2Image_sup {A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H) :
    modO2Image H (A ⊔ B) = modO2Image H A ⊔ modO2Image H B := by
  rw [modO2Image, Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

omit [Finite G] in
theorem modO2Image_self : modO2Image H H = ⊤ := by
  rw [modO2Image, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem isPGroup_modO2Image {p : ℕ} {A : Subgroup G} (hA : IsPGroup p ↥A) :
    IsPGroup p ↥(modO2Image H A) := by
  have h : IsPGroup p ↥(A.subgroupOf H) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hA ⟨x, Subgroup.mem_subgroupOf.mp hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  exact h.map _

omit [Finite G] in
theorem modO2Image_mono' {A B : Subgroup G} (h : A ≤ B) : modO2Image H A ≤ modO2Image H B :=
  Subgroup.map_mono fun x hx => (h hx : (x : G) ∈ B)

theorem modO2Image_oTwoUpper_pre {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hK : IsPGroup 3 ↥K) :
    modO2Image H (oTwoUpper (pre H K)) = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ((modO2Image_mono' (oTwoUpper_le _)).trans (modO2Image_pre K).le) ?_
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) z
  have hxK : (x : G) ∈ pre H K := (mem_pre x).mpr hz
  obtain ⟨k, hk⟩ := pow_mem_of_isPGroup hK hxK
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hk⟩
  have hj' : ((x : G) ^ 3 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  set y : ↥H := x ^ 2 ^ j with hy
  have hy3 : (y : G) ^ 3 ^ k = 1 := by
    rw [hy, Subgroup.coe_pow, ← pow_mul, mul_comm, pow_mul, hj']
  have hyodd : Odd (orderOf (y : G)) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy3)
    rw [hi]
    exact Odd.pow (by decide)
  have hyY : (y : G) ∈ oTwoUpper (pre H K) :=
    mem_oTwoUpper_of_odd (Subgroup.pow_mem _ hxK _) hyodd
  have hzy : QuotientGroup.mk' (CFSG.pCore 2 ↥H) y ∈ modO2Image H (oTwoUpper (pre H K)) :=
    ⟨y, Subgroup.mem_subgroupOf.mpr hyY, rfl⟩
  obtain ⟨i, hi⟩ := hK ⟨_, hz⟩
  have hi' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) x ^ 3 ^ i = 1 := by
    simpa using congrArg Subtype.val hi
  have hcop : Nat.Coprime (2 ^ j) (orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) x)) := by
    obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hi')
    rw [hl]
    exact Nat.Coprime.pow j l (by decide)
  have hmem := A4.mem_zpowers_pow_of_coprime hcop
  rw [← map_pow, ← hy] at hmem
  exact (Subgroup.zpowers_le.mpr hzy) hmem

theorem pre_le_M_of_le_l1 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hK : K ≤ modO2Image H (l1 T L V)) :
    pre H K ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_le_of_le S.hyp (le_sup_right.trans S.hz.1.1)
  have hLM := l1T_le_M S.hyp h1332
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hae⟩ := mem_modO2Image'.mp (hK hx)
  have h1 : a⁻¹ * x ∈ CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.eq]
    exact hae
  rw [← mem_pCoreOf_iff] at h1
  have e : (x : G) = (a : G) * ((a⁻¹ * x : ↥H) : G) := by simp
  rw [Subgroup.coe_subtype, e]
  exact Subgroup.mul_mem _ (le_sup_left.trans hLM ha) (le_sup_right.trans hLM (hOT h1))

theorem eq_sup_of_not_le (S : Setting147 G T L V H) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (ih : ∀ H₀ : Subgroup G, H₀ < H → Setting147 G T L V H₀ → Concl T L V H₀)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKn : K.Normal) (hK : IsPGroup 3 ↥K)
    (hKM : ¬ pre H K ≤ Subgroup.normalizer (L : Set G)) : H = pre H K ⊔ (l1 T L V ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pre H K ⊔ (l1 T L V ⊔ T) with hX
  have hXH : X ≤ H := sup_le (pre_le K) S.hz.1.1
  refine (lt_or_eq_of_le hXH).elim (fun hlt => ?_) fun h => h.symm
  exfalso
  have hXM : ¬ X ≤ Subgroup.normalizer (L : Set G) := fun h => hKM (le_sup_left.trans h)
  have S' := setting_of_le S h1332 h1334 le_sup_right hXH hXM
  refine hKM (le_M_of_concl S' h1332 (ih X hlt S') le_sup_left
    ((hXH.trans (le_normalizer_pre hKn))) ((pCoreOf_le_pre K).trans le_sup_left)
    (hXH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
    fun n hn => pow_mem_of_isPGroup hK hn)

theorem oTwoUpper_top_le {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (S : Setting147 G T L V H)
    (hKn : K.Normal) (hHe : H = pre H K ⊔ (l1 T L V ⊔ T))
    (hLK : modO2Image H (l1 T L V) ≤ K) :
    oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥(modO2Image H T) :=
    isPGroup_modO2Image (S.hyp.fsu.sylow.1)
  have hTop : (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ K ⊔ modO2Image H T := by
    have hl1 : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
    have hT : T ≤ H := le_sup_right.trans S.hz.1.1
    have e := congrArg (modO2Image H) hHe
    rw [modO2Image_self, modO2Image_sup (pre_le K) (sup_le hl1 hT), modO2Image_sup hl1 hT,
      modO2Image_pre] at e
    rw [e]
    exact sup_le le_sup_left (sup_le (hLK.trans le_sup_left) le_sup_right)
  exact oTwoUpper_le_of_pow_mem fun x hx =>
    exists_pow_mem_of_mem_sup_two hT2 (fun t _ => Subgroup.mem_normalizer_iff.mpr fun k =>
      ⟨fun hk => hKn.conj_mem k hk t, fun hk => by
        have := hKn.conj_mem _ hk t⁻¹
        convert this using 1
        group⟩) (hTop hx)

theorem isPOnePlusTwo_modO2Image {Y : Subgroup G} (hYH : Y ≤ H)
    (hHY : H ≤ Subgroup.normalizer (Y : Set G))
    (h : IsPOnePlusTwo 3 (↥Y ⧸ (pCoreOf 2 Y).subgroupOf Y)) :
    IsPOnePlusTwo 3 ↥(modO2Image H Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO1 : Y ⊓ pCoreOf 2 H ≤ pCoreOf 2 Y :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 H (hYH hy)⟩)
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  have hO2 : pCoreOf 2 Y ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYH)
      (hHY.trans (normalizer_le_normalizer_pCoreOf 2 Y)) (pCoreOf_isPGroup 2 Y)
  let φ : ↥Y →* (↥H ⧸ CFSG.pCore 2 ↥H) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hYH)
  have hrange : φ.range = modO2Image H Y := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hYH y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, Subgroup.mem_subgroupOf.mp hh⟩, rfl⟩
  have hker : φ.ker = (pCoreOf 2 Y).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [← mem_pCoreOf_iff]
    exact ⟨fun h => hO1 ⟨y.2, h⟩, fun h => hO2 h⟩
  exact isPOnePlusTwo_of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))) h

theorem hyp79 {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKn : K.Normal)
    (hexp : ∀ x ∈ K, x ^ 3 = 1) :
    oTwoUpper (oTwoUpper (pre H K)) = oTwoUpper (pre H K) ∧ oTwoUpper (pre H K) ≤ H ∧
      H ≤ Subgroup.normalizer (oTwoUpper (pre H K) : Set G) ∧
      ∀ y ∈ oTwoUpper (pre H K), y ^ 3 ∈ pCoreOf 2 (oTwoUpper (pre H K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := oTwoUpper (pre H K) with hY
  have hYH : Y ≤ H := (oTwoUpper_le _).trans (pre_le K)
  have hHY : H ≤ Subgroup.normalizer (Y : Set G) :=
    (le_normalizer_pre hKn).trans (normalizer_le_normalizer_oTwoUpper _)
  refine ⟨A4.oTwoUpper_oTwoUpper _, hYH, hHY, fun y hy => ?_⟩
  have hO1 : Y ⊓ pCoreOf 2 H ≤ pCoreOf 2 Y :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 H (hYH hy)⟩)
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  refine hO1 ⟨Y.pow_mem hy 3, ?_⟩
  have hyK := (mem_pre ⟨y, hYH hy⟩).mp (oTwoUpper_le _ hy)
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨y, hYH hy⟩ ^ 3) = 1 := by
    rw [map_pow]
    exact hexp _ hyK
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [← mem_pCoreOf_iff] at h2
  simpa using h2

end CFSG.Quasithin.H13.L32A.R727
