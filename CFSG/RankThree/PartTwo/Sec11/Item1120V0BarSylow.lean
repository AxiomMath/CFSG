module

public import Mathlib.GroupTheory.IndexNormal
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar

open CFSG.ABGLocalTools

theorem exists_isSylowOf_ge {G : Type*} [Group G] {p : ℕ} {K P : Subgroup G}
    (hPK : P ≤ K) (hP : IsPGroup p P) : ∃ T : Subgroup G, IsSylowOf p T K ∧ P ≤ T := by
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (hP.comap_subtype (K := K))
  refine ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ?_⟩
  exact Subgroup.mem_map_of_mem K.subtype
    (hQ (show (⟨x, hPK hx⟩ : K) ∈ P.comap K.subtype from hx))

theorem exists_conj_mem_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H R T : Subgroup G} (hR : IsSylowOf p R H) (hTH : T ≤ H) (hT : IsPGroup p T) :
    ∃ h ∈ H, ∀ x ∈ T, h⁻¹ * x * h ∈ R := by
  haveI : Finite (Sylow p G) :=
    Finite.of_injective (fun P : Sylow p G => ((P : Subgroup G) : Set G))
      fun P Q hPQ => Sylow.ext (SetLike.coe_injective hPQ)
  obtain ⟨Q0, hQ0⟩ := hR
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (hT.comap_subtype (K := H))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q0 S
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have hxS : (⟨x, hTH hx⟩ : H) ∈ (S : Subgroup H) :=
    hS (show (⟨x, hTH hx⟩ : H) ∈ T.comap H.subtype from hx)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
  rw [← hQ0]
  exact Subgroup.mem_map.mpr
    ⟨(MulAut.conj g)⁻¹ • (⟨x, hTH hx⟩ : H), hxS, by simp [MulAut.conj_inv_apply]⟩

theorem mem_sup_of_forall_comm {G : Type*} [Group G] {A S T : Subgroup G}
    (hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) (hS : S ≤ A) (hT : T ≤ A) {x : G}
    (hx : x ∈ S ⊔ T) : ∃ y ∈ S, ∃ z ∈ T, y * z = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, T.one_mem, mul_one x⟩
    · exact ⟨1, S.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, S.one_mem, 1, T.one_mem, mul_one 1⟩
  | mul x y _ _ hx hy =>
    obtain ⟨y₁, hy₁, z₁, hz₁, rfl⟩ := hx
    obtain ⟨y₂, hy₂, z₂, hz₂, rfl⟩ := hy
    refine ⟨y₁ * y₂, S.mul_mem hy₁ hy₂, z₁ * z₂, T.mul_mem hz₁ hz₂, ?_⟩
    have hc : z₁ * y₂ = y₂ * z₁ := hcomm z₁ (hT hz₁) y₂ (hS hy₂)
    calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by simp only [mul_assoc]
      _ = y₁ * (z₁ * y₂) * z₂ := by rw [hc]
      _ = y₁ * z₁ * (y₂ * z₂) := by simp only [mul_assoc]
  | inv x _ hx =>
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    refine ⟨y⁻¹, S.inv_mem hy, z⁻¹, T.inv_mem hz, ?_⟩
    rw [mul_inv_rev]
    exact hcomm y⁻¹ (hS (S.inv_mem hy)) z⁻¹ (hT (T.inv_mem hz))

theorem comm_mul_iff_of_comm {G : Type*} [Group G] {r x d : G} (hdr : d * r = r * d) :
    r * (x * d) = x * d * r ↔ r * x = x * r := by
  constructor
  · intro h1
    apply mul_right_cancel (b := d)
    calc r * x * d = r * (x * d) := by rw [mul_assoc]
      _ = x * d * r := h1
      _ = x * (d * r) := by rw [mul_assoc]
      _ = x * (r * d) := by rw [hdr]
      _ = x * r * d := by rw [mul_assoc]
  · intro h1
    calc r * (x * d) = r * x * d := by rw [mul_assoc]
      _ = x * r * d := by rw [h1]
      _ = x * (r * d) := by rw [mul_assoc]
      _ = x * (d * r) := by rw [hdr]
      _ = x * d * r := by rw [mul_assoc]

theorem isSylowOf_inf_centralizer_of_weakClosure
    {G : Type*} [Group G] [Finite G] {H R A D : Subgroup G} {a : G}
    (hR : IsSylowOf 3 R H)
    (hAR : A ≤ R)
    (hA3 : ∀ y ∈ A, y ^ 3 = 1)
    (hAΩ : ∀ y ∈ R, y ^ 3 = 1 → y ∈ A)
    (hAab : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (haA : a ∈ A)
    (hDA : D ≤ A) (hDR : ∀ u ∈ D, ∀ r ∈ R, u * r = r * u)
    (hAD : A = Subgroup.zpowers a ⊔ D) (haD : a ∉ D)
    (hNH : ∀ w ∈ H, w ∈ Subgroup.normalizer (A : Set G) → w ∈ Subgroup.normalizer (D : Set G)) :
    IsSylowOf 3 (R ⊓ Subgroup.centralizer ({a} : Set G))
      (H ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab y hy a haA)
  have hPK : R ⊓ Subgroup.centralizer ({a} : Set G) ≤ H ⊓ Subgroup.centralizer ({a} : Set G) :=
    inf_le_inf_right _ hR.le
  obtain ⟨T, hT, hRCT⟩ := exists_isSylowOf_ge hPK hR.isPGroup.to_inf_left
  have hTK : T ≤ H ⊓ Subgroup.centralizer ({a} : Set G) := hT.le
  have hTC : T ≤ Subgroup.centralizer ({a} : Set G) := hTK.trans inf_le_right
  have hAT : A ≤ T := fun y hy => hRCT ⟨hAR hy, hAC hy⟩
  obtain ⟨h, hhH, hconjT⟩ := exists_conj_mem_of_isPGroup hR (hTK.trans inf_le_left) hT.isPGroup
  have hconjA : ∀ y ∈ A, h⁻¹ * y * h ∈ A := by
    intro y hy
    apply hAΩ _ (hconjT y (hAT hy))
    have e : (h⁻¹ * y * h) ^ 3 = h⁻¹ * y ^ 3 * h := by
      have h3 := conj_pow (a := h⁻¹) (b := y) (i := 3)
      rwa [inv_inv] at h3
    rw [e, hA3 y hy, mul_one, inv_mul_cancel]
  have hsurj : ∀ y ∈ A, ∃ z ∈ A, h⁻¹ * z * h = y := by
    intro y hy
    let f : A → A := fun z => ⟨h⁻¹ * (z : G) * h, hconjA z z.2⟩
    have hf : Function.Injective f := by
      intro z w hzw
      have h1 : h⁻¹ * (z : G) * h = h⁻¹ * (w : G) * h := congrArg Subtype.val hzw
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
    obtain ⟨z, hz⟩ := Finite.surjective_of_injective hf ⟨y, hy⟩
    exact ⟨z, z.2, congrArg Subtype.val hz⟩
  have hnA : h ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    constructor
    · intro hx
      exact hconjA x hx
    · intro hx
      obtain ⟨z, hz, hzx⟩ := hsurj (h⁻¹ * x * h) hx
      have hzx' : z = x := mul_left_cancel (mul_right_cancel hzx)
      rw [← hzx']
      exact hz
  have hnD : h ∈ Subgroup.normalizer (D : Set G) := hNH h hhH hnA
  have hDc : ∀ x : G, x ∈ D ↔ h⁻¹ * x * h ∈ D := Subgroup.mem_normalizer_iff''.mp hnD
  have ha'D : h⁻¹ * a * h ∉ D := fun hD => haD ((hDc a).mpr hD)
  have ha'sup : h⁻¹ * a * h ∈ Subgroup.zpowers a ⊔ D := by
    rw [← hAD]
    exact hconjA a haA
  obtain ⟨y, hy, d, hd, hyd⟩ :=
    mem_sup_of_forall_comm hAab (Subgroup.zpowers_le.mpr haA) hDA ha'sup
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have ha3 : a ^ (3 : ℤ) = 1 := by simpa using hA3 a haA
  have hpow : ∀ k : ℤ, a ^ (1 + 3 * k) = a := by
    intro k
    rw [zpow_add, zpow_mul, ha3, one_zpow, mul_one, zpow_one]
  have hi3 : i % 3 ≠ 0 := by
    intro hi0
    have hai : a ^ i = 1 := by
      rw [show i = 3 * (i / 3) by omega, zpow_mul, ha3, one_zpow]
    rw [hai, one_mul] at hyd
    exact ha'D (by rw [← hyd]; exact hd)
  obtain ⟨j, k, hjk⟩ : ∃ j k : ℤ, i * j = 1 + 3 * k := by
    have hcase : i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hcase with h1 | h2
    · exact ⟨1, i / 3, by omega⟩
    · exact ⟨2, 2 * (i / 3) + 1, by omega⟩
  have haij : (a ^ i) ^ j = a := by
    rw [← zpow_mul, hjk, hpow]
  have hcomm_iff : ∀ r ∈ R, (r * a = a * r ↔ r * (h⁻¹ * a * h) = h⁻¹ * a * h * r) := by
    intro r hr
    rw [← hyd, comm_mul_iff_of_comm (hDR d hd r hr)]
    constructor
    · intro hra
      exact (show Commute r a from hra).zpow_right i
    · intro hrai
      have hc := (show Commute r (a ^ i) from hrai).zpow_right j
      rw [haij] at hc
      exact hc
  have hsub : R ⊓ Subgroup.centralizer ({h⁻¹ * a * h} : Set G) =
      R ⊓ Subgroup.centralizer ({a} : Set G) := by
    ext r
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hrR, hr⟩
      exact ⟨hrR, (hcomm_iff r hrR).mpr hr⟩
    · rintro ⟨hrR, hr⟩
      exact ⟨hrR, (hcomm_iff r hrR).mp hr⟩
  have hmem : ∀ x ∈ T, h⁻¹ * x * h ∈ R ⊓ Subgroup.centralizer ({h⁻¹ * a * h} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hconjT x hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp (hTC hx)
    calc h⁻¹ * x * h * (h⁻¹ * a * h) = h⁻¹ * (x * a) * h := by
          simp only [mul_assoc, mul_inv_cancel_left]
      _ = h⁻¹ * (a * x) * h := by rw [hxa]
      _ = h⁻¹ * a * h * (h⁻¹ * x * h) := by
          simp only [mul_assoc, mul_inv_cancel_left]
  have hcard1 : Nat.card T ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({h⁻¹ * a * h} : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun x : T => (⟨h⁻¹ * (x : G) * h, hmem x x.2⟩ :
        ↥(R ⊓ Subgroup.centralizer ({h⁻¹ * a * h} : Set G)))) ?_
    intro x y hxy
    have h1 : h⁻¹ * (x : G) * h = h⁻¹ * (y : G) * h := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hcard2 : Nat.card ↥(R ⊓ Subgroup.centralizer ({h⁻¹ * a * h} : Set G)) =
      Nat.card ↥(R ⊓ Subgroup.centralizer ({a} : Set G)) := by
    rw [hsub]
  have hEq : R ⊓ Subgroup.centralizer ({a} : Set G) = T :=
    Subgroup.eq_of_le_of_card_ge hRCT (hcard1.trans_eq hcard2)
  rw [hEq]
  exact hT

theorem exists_conj_mem_of_isSylowOf
    {G : Type*} [Group G] [Finite G] {N M T : Subgroup G}
    (hT : IsSylowOf 3 T N) (hMN : M ≤ N) (hNM : N ≤ Subgroup.normalizer (M : Set G))
    {y : G} (hy : y ∈ M) (hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1) :
    ∃ m ∈ M, m * y * m⁻¹ ∈ T := by
  obtain ⟨S, hS⟩ : IsSylowOf 3 (T ⊓ M) M := hT.inf_of_le_normalizer hMN hNM
  have key : ∀ s : ↥M, s ∈ (S : Subgroup ↥M) → (s : G) ∈ T := by
    intro s hs
    have h1 : M.subtype s ∈ (S : Subgroup ↥M).map M.subtype :=
      Subgroup.mem_map_of_mem _ hs
    rw [hS] at h1
    exact h1.1
  obtain ⟨k, hk⟩ := hy3
  obtain ⟨z, hzy⟩ : ∃ z : ↥M, (z : G) = y := ⟨⟨y, hy⟩, rfl⟩
  have hz : z ^ 3 ^ k = 1 := Subtype.ext (by simp [hzy, hk])
  have hR : IsPGroup 3 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card_dvd_pow (n := k) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hz
  haveI : Finite (Sylow 3 ↥M) :=
    Finite.of_injective (fun P : Sylow 3 ↥M => (P : Set ↥M)) SetLike.coe_injective
  obtain ⟨Q, hRQ⟩ := IsPGroup.exists_le_sylow hR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥M) S Q
  have hzQ : z ∈ (Q : Subgroup ↥M) := hRQ (Subgroup.mem_zpowers z)
  rw [← hg, Sylow.coe_subgroup_smul] at hzQ
  obtain ⟨s, hs, hsz⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hzQ
  have hcoe : (g : G) * (s : G) * (g : G)⁻¹ = y := by
    have h4 : (g : G) * (s : G) * (g : G)⁻¹ = (z : G) := congrArg Subtype.val hsz
    rw [hzy] at h4
    exact h4
  refine ⟨(g : G)⁻¹, M.inv_mem g.2, ?_⟩
  have h3 : (g : G)⁻¹ * y * ((g : G)⁻¹)⁻¹ = (s : G) := by
    rw [← hcoe]
    group
  rw [h3]
  exact key s hs

theorem conj_mem_of_card_le_three_mul
    {G : Type*} [Group G] [Finite G] {Q U : Subgroup G}
    (hQ : IsPGroup 3 Q) (hUQ : U ≤ Q) (hcard : Nat.card Q ≤ 3 * Nat.card U) :
    ∀ q ∈ Q, ∀ u ∈ U, q * u * q⁻¹ ∈ U := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  have hcardH : Nat.card (U.subgroupOf Q) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv
  have hmul : Nat.card U * (U.subgroupOf Q).index = Nat.card Q := by
    rw [← hcardH]
    exact Subgroup.card_mul_index (H := U.subgroupOf Q)
  have hpos : 0 < Nat.card U := by
    haveI : Nonempty U := ⟨1⟩
    exact Nat.card_pos
  have hidx : (U.subgroupOf Q).index = 1 ∨ (U.subgroupOf Q).index = 3 := by
    have hdvd : (U.subgroupOf Q).index ∣ 3 ^ n := by
      rw [← hn]
      exact Dvd.intro_left _ hmul
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hle : (U.subgroupOf Q).index ≤ 3 := by
      have h1 : Nat.card U * (U.subgroupOf Q).index ≤ Nat.card U * 3 := by
        rw [hmul, Nat.mul_comm (Nat.card U) 3]
        exact hcard
      exact Nat.le_of_mul_le_mul_left h1 hpos
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · exact Or.inl (hk.trans (by norm_num))
      · exact Or.inr (hk.trans (by norm_num))
    · exfalso
      have h9 : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      rw [← hk] at h9
      norm_num at h9
      omega
  rcases hidx with hidx1 | hidx3
  ·
    have htop : U.subgroupOf Q = ⊤ :=
      (Subgroup.index_eq_one (H := U.subgroupOf Q)).1 hidx1
    have hQU : Q ≤ U := by
      intro x hx
      have hmem : (⟨x, hx⟩ : Q) ∈ U.subgroupOf Q := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hmem
    intro q hq u hu
    exact U.mul_mem (U.mul_mem (hQU hq) hu) (U.inv_mem (hQU hq))
  ·
    have hn1 : (3 : ℕ) ^ n ≠ 1 := by
      rw [← hn, ← hmul, hidx3]
      omega
    have hmin : ((3 : ℕ) ^ n).minFac = 3 := by
      have hp : ((3 : ℕ) ^ n).minFac.Prime := Nat.minFac_prime hn1
      have hdvd : ((3 : ℕ) ^ n).minFac ∣ 3 ^ n := Nat.minFac_dvd _
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)
    haveI hnorm : (U.subgroupOf Q).Normal :=
      Subgroup.normal_of_index_eq_minFac_card (by rw [hn, hmin, hidx3])
    intro q hq u hu
    have hmem : (⟨u, hUQ hu⟩ : Q) ∈ U.subgroupOf Q := Subgroup.mem_subgroupOf.2 hu
    have key := hnorm.conj_mem _ hmem ⟨q, hq⟩
    exact Subgroup.mem_subgroupOf.1 key

theorem exists_threeElement_lift {Y Z : Type*} [Group Y] [Group Z] [Finite Y] (π : Y →* Z) {y : Y}
    {ζ : Z} (hπ : π y = ζ) (hζ : ∃ k : ℕ, ζ ^ 3 ^ k = 1) :
    ∃ y' ∈ Subgroup.zpowers y, (∃ k : ℕ, y' ^ 3 ^ k = 1) ∧ π y' = ζ := by
  obtain ⟨k, hk⟩ := hζ
  obtain ⟨j, u, hu3, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
  have hcop : Nat.Coprime (3 ^ max j k) u :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hu3)
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℕ, t ≡ 1 [MOD 3 ^ max j k] ∧ t ≡ 0 [MOD u] :=
    ⟨(Nat.chineseRemainder hcop 1 0).1, (Nat.chineseRemainder hcop 1 0).2⟩
  have hut : u ∣ t := Nat.modEq_zero_iff_dvd.1 ht2
  have hdvd : orderOf y ∣ t * 3 ^ j := by
    rw [hn, mul_comm t]
    exact mul_dvd_mul_left _ hut
  have hpow : (y ^ t) ^ (3 ^ j) = 1 := by
    rw [← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.1 hdvd
  have hζK : orderOf ζ ∣ 3 ^ max j k :=
    (orderOf_dvd_of_pow_eq_one hk).trans (pow_dvd_pow 3 (le_max_right j k))
  have hζt : ζ ^ t = ζ := by
    have hmod : t ≡ 1 [MOD orderOf ζ] := Nat.ModEq.of_dvd hζK ht1
    rw [pow_eq_pow_iff_modEq.2 hmod, pow_one]
  refine ⟨y ^ t, pow_mem (Subgroup.mem_zpowers y) t, ⟨j, hpow⟩, ?_⟩
  rw [map_pow, hπ, hζt]

theorem exists_conj_mem_fixer {G E : Type*} [Group G] [Finite G] [Group E] (J : Subgroup E)
    (X Hs T : Subgroup G)
    (f : G → MulAut E) (hf : ∀ m ∈ X, ∀ n ∈ X, f (m * n) = f m * f n)
    (hT : IsSylowOf 3 T Hs) (hTX : T ≤ X) (hTJ : ∀ t ∈ T, ∀ j ∈ J, f t j ∈ J)
    {y : G} (hyX : y ∈ X) (hyH : y ∈ Hs) (hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1)
    (hyJ : ∀ j ∈ J, f y j = j) :
    ∃ m ∈ X ⊓ Hs, (∀ j ∈ J, f m j = j) ∧ m * y * m⁻¹ ∈ T := by
  have hf1 : f 1 = 1 := by
    have h : f 1 = f 1 * f 1 := by
      have h0 := hf 1 X.one_mem 1 X.one_mem
      rwa [one_mul] at h0
    have h' : f 1 * f 1 = f 1 * 1 := by
      rw [mul_one]
      exact h.symm
    exact mul_left_cancel h'
  have hinvL : ∀ m ∈ X, ∀ j : E, f m⁻¹ (f m j) = j := by
    intro m hm j
    have h : f m⁻¹ * f m = 1 := by
      rw [← hf m⁻¹ (X.inv_mem hm) m hm]
      simp [hf1]
    have h2 := congrArg (fun σ : MulAut E => σ j) h
    simpa [MulAut.mul_apply, MulAut.one_apply] using h2
  have hinvR : ∀ m ∈ X, ∀ j : E, f m (f m⁻¹ j) = j := by
    intro m hm j
    have h : f m * f m⁻¹ = 1 := by
      rw [← hf m hm m⁻¹ (X.inv_mem hm)]
      simp [hf1]
    have h2 := congrArg (fun σ : MulAut E => σ j) h
    simpa [MulAut.mul_apply, MulAut.one_apply] using h2
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G,
      ∀ n : G, n ∈ M ↔ (n ∈ X ∧ n ∈ Hs ∧ ∀ j ∈ J, f n j = j) := by
    refine ⟨{ carrier := {n | n ∈ X ∧ n ∈ Hs ∧ ∀ j ∈ J, f n j = j}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun n => Iff.rfl⟩
    · rintro a b ⟨haX, haH, haJ⟩ ⟨hbX, hbH, hbJ⟩
      refine ⟨X.mul_mem haX hbX, Hs.mul_mem haH hbH, fun j hj => ?_⟩
      rw [hf a haX b hbX, MulAut.mul_apply, hbJ j hj, haJ j hj]
    · exact ⟨X.one_mem, Hs.one_mem, fun j _ => by simp [hf1]⟩
    · rintro a ⟨haX, haH, haJ⟩
      refine ⟨X.inv_mem haX, Hs.inv_mem haH, fun j hj => ?_⟩
      calc f a⁻¹ j = f a⁻¹ (f a j) := by rw [haJ j hj]
        _ = j := hinvL a haX j
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G,
      ∀ n : G, n ∈ N ↔ (n ∈ X ∧ n ∈ Hs ∧ ∀ j : E, j ∈ J ↔ f n j ∈ J) := by
    refine ⟨{ carrier := {n | n ∈ X ∧ n ∈ Hs ∧ ∀ j : E, j ∈ J ↔ f n j ∈ J}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun n => Iff.rfl⟩
    · rintro a b ⟨haX, haH, haJ⟩ ⟨hbX, hbH, hbJ⟩
      refine ⟨X.mul_mem haX hbX, Hs.mul_mem haH hbH, fun j => ?_⟩
      rw [hf a haX b hbX, MulAut.mul_apply]
      exact (hbJ j).trans (haJ (f b j))
    · exact ⟨X.one_mem, Hs.one_mem, fun j => by simp [hf1]⟩
    · rintro a ⟨haX, haH, haJ⟩
      refine ⟨X.inv_mem haX, Hs.inv_mem haH, fun j => ?_⟩
      have h := haJ (f a⁻¹ j)
      rw [hinvR a haX j] at h
      exact h.symm
  have hNH : N ≤ Hs := fun n hn => ((hN n).1 hn).2.1
  have hMN : M ≤ N := by
    intro n hn
    obtain ⟨hnX, hnH, hnJ⟩ := (hM n).1 hn
    refine (hN n).2 ⟨hnX, hnH, fun j => ⟨fun hj => ?_, fun hj => ?_⟩⟩
    · rw [hnJ j hj]
      exact hj
    · have hfk : f n (f n j) = f n j := hnJ (f n j) hj
      have h3 := hinvL n hnX (f n j)
      rw [hfk] at h3
      have hjeq : j = f n j := (hinvL n hnX j).symm.trans h3
      rw [hjeq]
      exact hj
  have hfwd : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M := by
    intro n hn m hm
    obtain ⟨hnX, hnH, -⟩ := (hN n).1 hn
    obtain ⟨hmX, hmH, hmJ⟩ := (hM m).1 hm
    obtain ⟨hn'X, hn'H, hn'J⟩ := (hN n⁻¹).1 (N.inv_mem hn)
    refine (hM _).2 ⟨X.mul_mem (X.mul_mem hnX hmX) hn'X,
      Hs.mul_mem (Hs.mul_mem hnH hmH) hn'H, fun j hj => ?_⟩
    have hjn : f n⁻¹ j ∈ J := (hn'J j).1 hj
    have e : f (n * m * n⁻¹) j = f n (f m (f n⁻¹ j)) := by
      rw [hf (n * m) (X.mul_mem hnX hmX) n⁻¹ hn'X, hf n hnX m hmX]
      simp only [MulAut.mul_apply]
    rw [e, hmJ _ hjn]
    exact hinvR n hnX j
  have hNnorm : N ≤ Subgroup.normalizer (M : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hfwd n hn x hx
    · intro hx
      have hx' : n * x * n⁻¹ ∈ M := hx
      have h := hfwd n⁻¹ (N.inv_mem hn) _ hx'
      have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
      rw [e] at h
      exact h
  have hTN : T ≤ N := by
    intro t ht
    refine (hN t).2 ⟨hTX ht, hT.le ht, fun j => ⟨fun hj => hTJ t ht j hj, fun hj => ?_⟩⟩
    have h := hTJ t⁻¹ (T.inv_mem ht) (f t j) hj
    rw [hinvL t (hTX ht) j] at h
    exact h
  have hT' : IsSylowOf 3 T N := hT.of_le hTN hNH
  have hyM : y ∈ M := (hM y).2 ⟨hyX, hyH, hyJ⟩
  obtain ⟨m, hmM, hmT⟩ := exists_conj_mem_of_isSylowOf hT' hMN hNnorm hyM hy3
  obtain ⟨hmX, hmH, hmJ⟩ := (hM m).1 hmM
  exact ⟨m, Subgroup.mem_inf.mpr ⟨hmX, hmH⟩, hmJ, hmT⟩

end CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar

end
