module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Shape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16c4v1_prh_fixSp_zpowers {F : Type} [Field F] [Finite F] {σ : F ≃+* F}
    (b : SUid σ 4) (x : Fin 4 → F) : x ∈ fixSp (Subgroup.zpowers b) ↔ b • x = x := by
  rw [mem_fixSp]
  exact ⟨fun h => h b (Subgroup.mem_zpowers b),
    fun h a ha => smul_eq_self_of_mem_zpowers ha h⟩

theorem s16c4v1_transvection (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {g : G} (hg : s16c4v1_Cex D V g)
    (hg' : s16c4v1_Cex D V g⁻¹) (h2 : s16c4v1_r2 V g = 4) :
    ∃ a ∈ conjSubgroup V g,
      8 * Nat.card (conjSubgroup V g ⊓
          Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :
            Subgroup G) = Nat.card (conjSubgroup V g) := by
  let A : Subgroup G := conjSubgroup V g
  have hAM : A ≤ D.M := hg.1
  have hAea : IsElemAbelian 2 A := E3.isElemAbelian_conjSubgroup hV g
  have hA2 : IsPGroup 2 A := hAea.isPGroup
  have hA1 : ∀ a ∈ A, ∀ x ∈ v1Sub D.M ⊥ V hV L, a * x * a⁻¹ = x :=
    s16c4v1_cex_cent_V1 S hstd hg hg'
  obtain ⟨φ, hφ, hker⟩ := s16c4v1_two_hom S hstd.r1217 hz hAM hA2 hA1
  have hkey : ∀ a : ↥A, ∀ v ∈ V,
      (a : G) * v * (a : G)⁻¹ = v ↔ φ a • s16c4v1_vec S v = s16c4v1_vec S v := by
    intro a v hv
    constructor
    · intro h
      rw [← hφ a v hv, h]
    · intro h
      have hdmem : ((a : G) * v * (a : G)⁻¹ * v⁻¹) ∈ ⁅V, A⁆ := by
        have h1 : (a : G) * v * (a : G)⁻¹ * v⁻¹ = ⁅(a : G), v⁆ := by
          rw [commutatorElement_def]
        rw [h1, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator a.2 hv
      have hdvec : s16c4v1_vec S ((a : G) * v * (a : G)⁻¹ * v⁻¹) = 0 := by
        have hav : (a : G) * v * (a : G)⁻¹ ∈ V := s16c4v1_conj_mem S (hAM a.2) hv
        rw [s16c4v1_vec_mul S hav (V.inv_mem hv)]
        have h1 : s16c4v1_vec S ((a : G) * v * (a : G)⁻¹) = s16c4v1_vec S v := by
          rw [hφ a v hv, h]
        have h2 : s16c4v1_vec S v + s16c4v1_vec S v⁻¹ = 0 := by
          have hh := s16c4v1_vec_mul S hv (V.inv_mem hv)
          rw [mul_inv_cancel, s16c4v1_vec_one] at hh
          exact hh.symm
        rw [h1, h2]
      have hd1 : (a : G) * v * (a : G)⁻¹ * v⁻¹ = 1 := by
        by_contra hne
        exact (s16c4v1_cex_D_sing S hstd hg hg' _ hdmem hne).1 hdvec
      exact mul_inv_eq_one.1 hd1
  have hE2 : ∀ x ∈ φ.range, x * x = 1 := by
    rintro x ⟨y, rfl⟩
    have hy : y * y = 1 := by
      apply Subtype.ext
      show (y : G) * (y : G) = 1
      simpa [pow_two] using hAea.2 (y : G) y.2
    rw [← map_mul, hy, map_one]
  have hEc : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    haveI : IsMulCommutative ↥A := hAea.1
    letI : CommGroup ↥A := IsMulCommutative.instCommGroup
    rintro x ⟨u, rfl⟩ y ⟨v, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm u v]
  have hF : Nat.card S.F.K = (2 ^ 1) ^ 2 := by rw [S.F.card_K]; norm_num
  have hcard : Nat.card ↥(φ.range) = 2 ^ (4 * 1) := by
    rw [show (4 : ℕ) * 1 = 4 by norm_num]
    rw [← Subgroup.index_ker φ]
    have hker_eq : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, hker a, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      refine forall₂_congr fun v hv => ?_
      constructor
      · intro h
        calc v * (a : G) = ((a : G) * v * (a : G)⁻¹) * (a : G) := by rw [h]
          _ = (a : G) * v := by group
      · intro h
        calc (a : G) * v * (a : G)⁻¹ = (v * (a : G)) * (a : G)⁻¹ := by rw [← h]
          _ = v := by group
    rw [hker_eq, show ((Subgroup.centralizer (V : Set G)).subgroupOf A).index =
        (Subgroup.centralizer (V : Set G)).relIndex A from rfl,
      E3.relIndex_eq_two_pow hA2 (Subgroup.centralizer (V : Set G))]
    have hmq : E3.mQuot A (Subgroup.centralizer (V : Set G)) = 4 := h2
    rw [hmq]
  obtain ⟨B₁, B₂, hB₁le, hB₂le, hB₁card, hB₂card, hB₁mem, hB₂mem, hfix₁, hfix₂, hsup⟩ :=
    s16_C4ModelTv_two_root_groups (F := S.F.K) (σ := S.F.σ) (E := φ.range)
      S.F.isUnitary S.F.two_eq_zero hE2 hEc le_rfl hF hcard
  have hB₁card' : Nat.card ↥B₁ = 2 := by simpa using hB₁card
  have hB₁ne : B₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB₁card'
    norm_num at hB₁card'
  obtain ⟨b, hbne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB₁ne
  set b₀ : SUid S.F.σ 4 := (b : SUid S.F.σ 4) with hb₀
  have hbB₁ : b₀ ∈ B₁ := by rw [hb₀]; exact b.2
  have hbE : b₀ ∈ φ.range := hB₁le hbB₁
  obtain ⟨a, haφ⟩ := MonoidHom.mem_range.1 hbE
  have hb2 : b₀ * b₀ = 1 := hE2 b₀ hbE
  have horder : orderOf b₀ = 2 := by
    have hdvd : orderOf b₀ ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.2 (by simpa [pow_two] using hb2)
    have hne1 : orderOf b₀ ≠ 1 := by
      intro h1
      apply hbne
      apply Subtype.ext
      rw [← hb₀]
      exact orderOf_eq_one_iff.1 h1
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exact absurd h1 hne1
    · exact h2
  have hB₁eq : B₁ = Subgroup.zpowers b₀ :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbB₁)
      (by rw [Nat.card_zpowers, horder, hB₁card'])).symm
  have hfixB₁ : ∀ x : Fin 4 → S.F.K, x ∈ fixSp B₁ ↔ b₀ • x = x := by
    intro x
    rw [hB₁eq]
    exact s16c4v1_prh_fixSp_zpowers b₀ x
  have hkeyb : ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ = v ↔
      b₀ • s16c4v1_vec S v = s16c4v1_vec S v := by
    intro v hv
    rw [hkey a v hv, haφ]
  have hZmem : ∀ z ∈ V,
      z ∈ (V ⊓ Subgroup.centralizer ({(a : G)} : Set G) : Subgroup G) ↔
        s16c4v1_vec S z ∈ fixSp B₁ := by
    intro z hz
    have hcz : z ∈ Subgroup.centralizer ({(a : G)} : Set G) ↔
        (a : G) * z * (a : G)⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        calc (a : G) * z * (a : G)⁻¹ = (z * (a : G)) * (a : G)⁻¹ := by rw [← h]
          _ = z := by group
      · intro h
        calc z * (a : G) = ((a : G) * z * (a : G)⁻¹) * (a : G) := by rw [h]
          _ = (a : G) * z := by group
    rw [Subgroup.mem_inf, and_iff_right hz, hcz, hfixB₁ (s16c4v1_vec S z), hkeyb z hz]
  have hCA : ∀ a' : ↥A, (a' : G) ∈ (A ⊓ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer ({(a : G)} : Set G) : Subgroup G) : Set G)) ↔
        φ a' ∈ B₁ := by
    intro a'
    rw [Subgroup.mem_inf, and_iff_right a'.2, Subgroup.mem_centralizer_iff]
    constructor
    · intro hc
      rw [hB₁mem]
      refine ⟨MonoidHom.mem_range.2 ⟨a', rfl⟩, fun x hx => ?_⟩
      obtain ⟨zz, hz, hzv⟩ := s16c4v1_exists_vec S x
      rw [← hzv, ← hkey a' zz hz]
      have hzZ : zz ∈ (V ⊓ Subgroup.centralizer ({(a : G)} : Set G) : Subgroup G) :=
        (hZmem zz hz).2 (hzv ▸ hx)
      have hcomm := hc zz hzZ
      rw [← hcomm]; group
    · intro hb'
      intro z hz
      have hzV : z ∈ V := (Subgroup.mem_inf.1 hz).1
      have hzfix : s16c4v1_vec S z ∈ fixSp B₁ := (hZmem z hzV).1 hz
      have hx := (hB₁mem (φ a')).1 hb'
      have hfix := hx.2 (s16c4v1_vec S z) hzfix
      have h2 : (a' : G) * z * (a' : G)⁻¹ = z := (hkey a' z hzV).2 hfix
      calc z * (a' : G) = ((a' : G) * z * (a' : G)⁻¹) * (a' : G) := by rw [h2]
        _ = (a' : G) * z := by group
  let K : Subgroup ↥A := B₁.comap φ
  have hK_eq : K = (A ⊓ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer ({(a : G)} : Set G) : Subgroup G) : Set G)).subgroupOf A := by
    ext a'
    rw [Subgroup.mem_subgroupOf]
    exact (hCA a').symm
  have hcardK : Nat.card (A ⊓ Subgroup.centralizer
      ((V ⊓ Subgroup.centralizer ({(a : G)} : Set G) : Subgroup G) : Set G) : Subgroup G) =
      Nat.card K := by
    rw [hK_eq]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
  have hcomap : K = (B₁.subgroupOf φ.range).comap φ.rangeRestrict := rfl
  have hindex : K.index = 8 := by
    have h1 : ((B₁.subgroupOf φ.range).comap φ.rangeRestrict).index =
        (B₁.subgroupOf φ.range).index :=
      Subgroup.index_comap_of_surjective (H := B₁.subgroupOf φ.range)
        (f := φ.rangeRestrict) (MonoidHom.rangeRestrict_surjective φ)
    rw [← hcomap] at h1
    rw [h1]
    have h2 := Subgroup.card_mul_index (H := B₁.subgroupOf φ.range)
    have hc : Nat.card ↥(B₁.subgroupOf φ.range) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁le).toEquiv, hB₁card']
    rw [hc] at h2
    have h3 : Nat.card ↥(φ.range) = 16 := by
      rw [hcard]; norm_num
    rw [h3] at h2
    omega
  refine ⟨(a : G), a.2, ?_⟩
  show 8 * Nat.card (A ⊓ Subgroup.centralizer
    ((V ⊓ Subgroup.centralizer ({(a : G)} : Set G) : Subgroup G) : Set G) : Subgroup G) = Nat.card A
  have h4 := Subgroup.card_mul_index (H := K)
  rw [hindex, ← hcardK, mul_comm] at h4
  exact h4

theorem s16c4v1_parity_false (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {g : G} (hg : s16c4v1_Cex D V g)
    (hg' : s16c4v1_Cex D V g⁻¹) (h2 : s16c4v1_r2 V g = 4) : False := by
  obtain ⟨a, haA, hcard⟩ := s16c4v1_transvection S hstd hz hg hg' h2
  obtain ⟨k, hk1, hk⟩ := s16c4v1_card_v1 S hstd.r1217 hz
  let Z : Subgroup G := V ⊓ Subgroup.centralizer ({a} : Set G)
  have hcardV : Nat.card (conjSubgroup V g) = 2 ^ (8 + 2 * k) := by
    rw [E3.card_conjSubgroup, s16c4v1_card_V S, hk]
    rw [show (4 : ℕ) ^ k = 2 ^ (2 * k) by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]]
    rw [← pow_add]
  have hcardAZ : Nat.card (conjSubgroup V g ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) =
      2 ^ (5 + 2 * k) := by
    have h := hcard
    rw [hcardV] at h
    have h8 : (2 : ℕ) ^ (8 + 2 * k) = 8 * 2 ^ (5 + 2 * k) := by
      have e : 8 + 2 * k = 3 + (5 + 2 * k) := by omega
      rw [e, pow_add]
      norm_num
    rw [h8] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8) h
  have hconj : conjSubgroup (conjSubgroup V g ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) g⁻¹ =
      V ⊓ Subgroup.centralizer (conjSubgroup Z g⁻¹ : Set G) := by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, E3.conjSubgroup_conj_inv]
  have hcardY : Nat.card (V ⊓ Subgroup.centralizer (conjSubgroup Z g⁻¹ : Set G) : Subgroup G) =
      2 ^ (5 + 2 * k) := by
    rw [← hconj, E3.card_conjSubgroup, hcardAZ]
  have hg'' : s16c4v1_Cex D V g⁻¹⁻¹ := by rw [inv_inv]; exact hg
  have hYle : conjSubgroup Z g⁻¹ ≤ conjSubgroup V g⁻¹ :=
    E3.conjSubgroup_mono_left g⁻¹ inf_le_left
  have hYcomm : ∀ y ∈ conjSubgroup Z g⁻¹, ∀ v ∈ V,
      y * (z * v * z⁻¹) * y⁻¹ = z * (y * v * y⁻¹) * z⁻¹ := by
    intro y hy v hv
    have hyM : y ∈ D.M := hg'.1 (hYle hy)
    have hyV1 : ∀ x ∈ v1Sub D.M ⊥ V hV L, y * x * y⁻¹ = x :=
      s16c4v1_cex_cent_V1 S hstd hg' hg'' y (hYle hy)
    exact s16c4v1_commute_of_lin S hstd.r1217 hz hyM
      (s16c4v1_lin_of_cent_V1 S hstd.r1217 hz hyM hyV1) v hv
  obtain ⟨j, hj⟩ := s16c4v1_card_cent_four_pow S hstd.r1217 hz (Y := conjSubgroup Z g⁻¹) hYcomm
  have hpow : (4 : ℕ) ^ j = 2 ^ (2 * j) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [hpow] at hj
  rw [hj] at hcardY
  have heq : 2 * j = 5 + 2 * k := Nat.pow_right_injective (a := 2) (by norm_num) hcardY
  omega

theorem s16c4v1_lemma13 (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {g : G} (hg : s16c4v1_Cex D V g) : False := by
  have hr := s16c4v1_rMV_ge_six S hstd hz
  have hg' : s16c4v1_Cex D V g⁻¹ := s16c4v1_cex_inv S hstd hr hg
  have hg'' : s16c4v1_Cex D V g⁻¹⁻¹ := by
    rw [inv_inv]
    exact hg
  have hcard : Nat.card (⁅V, conjSubgroup V g⁻¹⁆ : Subgroup G) =
      Nat.card (⁅V, conjSubgroup V g⁆ : Subgroup G) := s16c4v1_card_comm_inv V g
  rcases s16c4v1_cex_D_card S hstd hz hg hg' with h4 | h16
  · have h2g := s16c4v1_shape_two S hstd hz hg hg' h4
    have h2g' := s16c4v1_shape_two S hstd hz hg' hg'' (by rw [hcard]; exact h4)
    have h1g : s16c4v1_r1 V g ≤ 1 := by
      have e : s16c4v1_r2 V g⁻¹ = s16c4v1_r1 V g := by
        rw [s16c4v1_r2_eq_r1_inv V g⁻¹, inv_inv]
      rw [← e]
      exact h2g'
    have hle := s16c4v1_pairing_le hV (E3.isElemAbelian_conjSubgroup hV g)
      (s16c4v1_cex_comm_le (S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer) hg.1 hg'.1)
      h1g h2g
    omega
  · have h1g' : s16c4v1_r1 V g⁻¹ = 4 :=
      s16c4v1_shape_four S hstd hz hg' hg'' (by rw [hcard]; exact h16)
    have h2g : s16c4v1_r2 V g = 4 := by
      rw [s16c4v1_r2_eq_r1_inv, h1g']
    exact s16c4v1_parity_false S hstd hz hg hg' h2g

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
