module

public import CFSG.Quasithin.H13.L32A706b
public import CFSG.Quasithin.H13.L32AC47a
public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.Background.F6ComponentBound
public import CFSG.Quasithin.Background.F918P1
public import CFSG.Quasithin.H13.L32AC33a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Generic

variable {Y : Type} [Group Y]

theorem mem_normalizer_of_conj_mem_fin [Finite Y] {A : Subgroup Y} {g : Y}
    (h : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ Subgroup.normalizer (A : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact h a ha
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mem_normalizer_of_cube {H K : Subgroup Y} (hKH : K ≤ H)
    (hK : (K.subgroupOf H).Normal ∨ (conjSubgroupsBy H K).ncard = 2) {y : Y} (hyH : y ∈ H)
    (hy3 : y ^ 3 = 1) : y ∈ Subgroup.normalizer (K : Set Y) := by
  rcases hK with hn | h2
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hn hyH
  · rw [H13.A5.ncard_conjSubgroupsBy_eq_index] at h2
    have hm := Subgroup.mul_self_mem_of_index_two h2 ⟨y, hyH⟩
    have e : (⟨y, hyH⟩ : ↥H) = (⟨y, hyH⟩ * ⟨y, hyH⟩) * (⟨y, hyH⟩ * ⟨y, hyH⟩) := by
      apply Subtype.ext
      show y = y * y * (y * y)
      calc y = y ^ 3 * y := by rw [hy3, one_mul]
        _ = y * y * (y * y) := by rw [pow_three]; simp only [mul_assoc]
    have h4 := mul_mem hm hm
    rw [← e] at h4
    exact Subgroup.mem_subgroupOf.mp h4

theorem centralizes_sz_of_inv' {N : Subgroup Y} [Finite N]
    {e : ℕ} (hN : IsSz e ↥N) {y t : Y} (hyN : y ∈ Subgroup.normalizer (N : Set Y))
    (htN : t ∈ Subgroup.normalizer (N : Set Y)) (hy3 : y ^ 3 = 1) {k : ℕ}
    (hk : (t * y * t⁻¹ * y) ^ 2 ^ k = 1) {n : Y} (hn : n ∈ N) : y * n * y⁻¹ = n := by
  have hNM : N ≤ Subgroup.normalizer (N : Set Y) := Subgroup.le_normalizer
  have : Finite ↥(N.subgroupOf (Subgroup.normalizer (N : Set Y))) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe hNM).symm.toEquiv
  have hN' : IsSz e ↥(N.subgroupOf (Subgroup.normalizer (N : Set Y))) :=
    isSz_congr (Subgroup.subgroupOfEquivOfLe hNM).symm hN
  have h := centralizes_sz_of_inv (N := N.subgroupOf (Subgroup.normalizer (N : Set Y))) hN'
    (y := (⟨y, hyN⟩ : ↥(Subgroup.normalizer (N : Set Y)))) (t := ⟨t, htN⟩)
    (Subtype.ext (by simpa using hy3)) (k := k) (Subtype.ext (by simpa using hk))
    (n := ⟨n, hNM hn⟩) (Subgroup.mem_subgroupOf.mpr hn)
  simpa using congrArg Subtype.val h

theorem isSolvable_sup_of_le_normalizer' {A B : Subgroup Y}
    (hBA : B ≤ Subgroup.normalizer (A : Set Y)) (hA : Group.IsSolvable ↥A)
    (hB : Group.IsSolvable ↥B) : Group.IsSolvable ↥(A ⊔ B) := by
  have hAV : A ≤ A ⊔ B := le_sup_left
  have hBV : B ≤ A ⊔ B := le_sup_right
  have hVN : A ⊔ B ≤ Subgroup.normalizer (A : Set Y) := sup_le Subgroup.le_normalizer hBA
  have : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAV).mpr hVN
  have hsA : Group.IsSolvable ↥(A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hAV).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAV).injective
  let ρ : ↥B →* ↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' (A.subgroupOf (A ⊔ B))).comp (Subgroup.inclusion hBV)
  have hρ : Function.Surjective ρ := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨a, ha, b, hb, hz⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBA).mp z.2
    refine ⟨⟨b, hb⟩, ?_⟩
    show QuotientGroup.mk' (A.subgroupOf (A ⊔ B)) (Subgroup.inclusion hBV ⟨b, hb⟩) =
      QuotientGroup.mk' (A.subgroupOf (A ⊔ B)) z
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have e : ((Subgroup.inclusion hBV ⟨b, hb⟩)⁻¹ * z : ↥(A ⊔ B)) = (b⁻¹ * a * b : Y) := by
      simp [hz, mul_assoc]
    rw [e]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hBA (B.inv_mem hb)) a).mp ha
    simpa using h1
  have hsQ : Group.IsSolvable (↥(A ⊔ B) ⧸ A.subgroupOf (A ⊔ B)) := Group.isSolvable_of_surjective hρ
  refine Group.isSolvable_of_ker_le_range (A.subgroupOf (A ⊔ B)).subtype
    (QuotientGroup.mk' (A.subgroupOf (A ⊔ B))) fun x hx => ?_
  rw [QuotientGroup.ker_mk'] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem isSolvable_of_isPGroup_odd [Finite Y] {S B : Subgroup Y} (hSB : S ≤ B)
    (hBN : B ≤ Subgroup.normalizer (S : Set Y)) (hS : IsPGroup 2 ↥S)
    (hodd : Odd (S.relIndex B)) : Group.IsSolvable ↥B := by
  have : (S.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hBN
  have hsS : Group.IsSolvable ↥(S.subgroupOf B) := by
    have h2 : IsPGroup 2 ↥(S.subgroupOf B) :=
      hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSB).symm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := h2.isNilpotent
    infer_instance
  have hsQ : Group.IsSolvable (↥B ⧸ S.subgroupOf B) := by
    refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
    rwa [← Subgroup.index_eq_card]
  refine Group.isSolvable_of_ker_le_range (S.subgroupOf B).subtype
    (QuotientGroup.mk' (S.subgroupOf B)) fun x hx => ?_
  rw [QuotientGroup.ker_mk'] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

end Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_cComp_of_le_of_le {H X K : Subgroup G} (hK : K ∈ cComp H) (hKX : K ≤ X)
    (hXH : X ≤ H) : K ∈ cComp X :=
  ⟨hK.1, hK.2.1, A3.subnormal_of_le_of_le hK.2.2.1 hKX hXH, fun J hJK hJ1 hJp hJX =>
    hK.2.2.2 J hJK hJ1 hJp (A3.subnormal_trans (A3.subnormal_of_le_of_le hJX hJK.le hKX)
      hK.2.2.1)⟩

omit [Finite G] in
theorem modO2Image_map_conj {H K : Subgroup G} (hKH : K ≤ H) (h : ↥H) :
    modO2Image H (K.map (MulAut.conj (h : G) : G →* G)) =
      (modO2Image H K).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) h) : _ →* (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  ext x
  rw [mem_modO2Image', Subgroup.mem_map]
  constructor
  · rintro ⟨a, ⟨k, hk, hka⟩, rfl⟩
    refine ⟨QuotientGroup.mk' _ ⟨k, hKH hk⟩, mem_modO2Image'.mpr ⟨_, hk, rfl⟩, ?_⟩
    have e : a = h * ⟨k, hKH hk⟩ * h⁻¹ := Subtype.ext (by simpa using hka.symm)
    rw [e]
    simp
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, hk, rfl⟩ := mem_modO2Image'.mp hz
    exact ⟨h * k * h⁻¹, ⟨k, hk, by simp⟩, by simp⟩

theorem mem_normalizer_of_mk {H K : Subgroup G} (hK : K ∈ cComp H) {h : ↥H}
    (hh : QuotientGroup.mk' (CFSG.pCore 2 ↥H) h ∈
      Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    (h : G) ∈ Subgroup.normalizer (K : Set G) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have h1 : K.map (MulAut.conj (h : G) : G →* G) ∈ cComp H := by
    have := cComp_map_mulEquiv (MulAut.conj (h : G)) hK
    rwa [MulEquiv.toMonoidHom_eq_coe,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer h.2)] at this
  have h2 : modO2Image H (K.map (MulAut.conj (h : G) : G →* G)) = modO2Image H K := by
    rw [modO2Image_map_conj hKH, Subgroup.mem_normalizer_iff_map_conj_eq.mp hh]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (modO2Image_injOn H h1 hK h2)

omit [Finite G] in
theorem mk_mem_normalizer {H K : Subgroup G} (hKH : K ≤ H) {y : ↥H}
    (hy : (y : G) ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) y ∈
      Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← modO2Image_map_conj hKH,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hy]

variable {T L V : Subgroup G}

theorem l1_star_normal (h1332 : Stmt13_3_2) {X : Subgroup G}
    (S : Setting147 G T L V (X ⊔ (l1 T L V ⊔ T)))
    (hXn : l1 T L V ⊔ T ≤ Subgroup.normalizer (X : Set G))
    (hcomm : ∀ y ∈ l1 T L V, ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (X ⊔ (l1 T L V ⊔ T))) :
    (modO2Image (X ⊔ (l1 T L V ⊔ T)) (l1 T L V)).Normal := by
  have hl1H : l1 T L V ≤ X ⊔ (l1 T L V ⊔ T) := Setting147.l1H' S
  have hl1N : l1 T L V ⊔ T ≤ Subgroup.normalizer (l1 T L V : Set G) :=
    sup_le Subgroup.le_normalizer (Setting147.T_le_N_l1 S h1332)
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨l, hl, rfl⟩ := mem_modO2Image'.mp hn
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(X ⊔ (l1 T L V ⊔ T))) g
  obtain ⟨x, hx, m, hm, hxm⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hXn).mp h.2
  have hl' : (m * l * m⁻¹ : G) ∈ l1 T L V := (Subgroup.mem_normalizer_iff.mp (hl1N hm) l).mp hl
  have hl'H : (m * l * m⁻¹ : G) ∈ X ⊔ (l1 T L V ⊔ T) := hl1H hl'
  have hxH : x ∈ X ⊔ (l1 T L V ⊔ T) := Subgroup.mem_sup_left hx
  refine mem_modO2Image'.mpr ⟨⟨m * l * m⁻¹, hl'H⟩, hl', ?_⟩
  have hcm := Setting147.mk_commute_of_mem ⟨_, hl'H⟩ ⟨x, hxH⟩ (hcomm _ hl' x hx)
  have e : h * l * h⁻¹ = (⟨x, hxH⟩ : ↥(X ⊔ (l1 T L V ⊔ T))) * ⟨m * l * m⁻¹, hl'H⟩ *
      (⟨x, hxH⟩ : ↥(X ⊔ (l1 T L V ⊔ T)))⁻¹ :=
    Subtype.ext (by simp [hxm, mul_assoc])
  rw [← map_mul, ← map_inv, ← map_mul, e, map_mul, map_mul, map_inv, ← hcm,
    mul_inv_cancel_right]

theorem false_of_l1_comm (h7 : Lemma14_7_7) (h1332 : Stmt13_3_2)
    {X K : Subgroup G} (S : Setting147 G T L V (X ⊔ (l1 T L V ⊔ T)))
    (hXn : l1 T L V ⊔ T ≤ Subgroup.normalizer (X : Set G))
    (hcomm : ∀ y ∈ l1 T L V, ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (X ⊔ (l1 T L V ⊔ T)))
    (hK : K ∈ cComp (X ⊔ (l1 T L V ⊔ T))) {e : ℕ} (hSz : IsSz e (cStar K)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP := h7 G T L V _ S (l1_star_normal h1332 S hXn hcomm)
  obtain ⟨φ⟩ := modO2_mulEquiv hK
  have hKsz : IsSz e ↥(modO2Image (X ⊔ (l1 T L V ⊔ T)) K) :=
    isSz_congr ((cStarEquiv K).trans φ) hSz
  have hsub : (modO2Image (X ⊔ (l1 T L V ⊔ T)) K).IsSubnormal :=
    A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
  have hcop : Nat.Coprime 3 (Nat.card ↥(modO2Image (X ⊔ (l1 T L V ⊔ T)) K)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (H13.A5.ConfSz.three_not_dvd_card hKsz)
  have hbot := F6.eq_bot_of_isSubnormal_of_coprime 3 hP hsub hcop
  have hnt := (H13.A5.ConfSz.isSimpleGroup hKsz).toNontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hbot

end CFSG.Quasithin.H13.L32A.C
