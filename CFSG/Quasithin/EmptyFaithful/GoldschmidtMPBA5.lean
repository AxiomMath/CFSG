module

public import CFSG.Walter.J1.A5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main

public section

namespace CFSG.Quasithin.C58NS.MPB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank
open CFSG.Walter.J1.A5 (A)

section A5

theorem card_a5 : Nat.card A = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem sq_eq_one_of_pow_four {x : A} (h : x ^ 4 = 1) : x ^ 2 = 1 := by
  rcases CFSG.Walter.J1.A5.pow_eq_one x with h2 | h3 | h5
  · exact h2
  · have : x = 1 := by
      have e : x = x ^ 4 * (x ^ 3)⁻¹ := by group
      rw [e, h, h3]
      simp
    rw [this]
    simp
  · have : x = 1 := by
      have e : x = x ^ 5 * (x ^ 4)⁻¹ := by group
      rw [e, h, h5]
      simp
    rw [this]
    simp

theorem exists_two_involutions {S : Subgroup A} (hS : Nat.card S = 4) :
    ∃ a b : A, a ∈ S ∧ b ∈ S ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      a * b = b * a := by
  have hsq : ∀ x ∈ S, x ^ 2 = 1 := fun x hx => by
    have h4 : (⟨x, hx⟩ : S) ^ 4 = 1 := by
      have := pow_card_eq_one' (G := S) (x := ⟨x, hx⟩)
      rwa [hS] at this
    exact sq_eq_one_of_pow_four (by simpa using congrArg Subtype.val h4)
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy => by
    have hxy : (x * y) ^ 2 = 1 := hsq (x * y) (S.mul_mem hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq y hy)
    have h3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hxy)
    rw [mul_inv_rev, hx', hy'] at h3
    exact h3.symm
  have h2 : 2 ∣ Nat.card S := by rw [hS]; norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 h2
  have ha1 : (a : A) ≠ 1 := fun h => by
    have : a = 1 := Subtype.ext h
    rw [this, orderOf_one] at ha
    omega
  have hlt : ¬ S ≤ Subgroup.zpowers (a : A) := by
    intro hle
    have := Subgroup.card_le_of_le hle
    have hz : Nat.card (Subgroup.zpowers (a : A)) = 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, ha]
    omega
  obtain ⟨b, hbS, hbz⟩ := Set.not_subset.1 hlt
  refine ⟨a, b, a.2, hbS, hsq a a.2, hsq b hbS, ha1, ?_, ?_, hcomm a a.2 b hbS⟩
  · rintro rfl
    exact hbz (Subgroup.one_mem _)
  · rintro h
    exact hbz (h ▸ Subgroup.mem_zpowers _)

theorem not_normalize {a b x : A} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hc : a * b = b * a) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hna : a * x * a⁻¹ ∈ Subgroup.zpowers x) (hnb : b * x * b⁻¹ ∈ Subgroup.zpowers x) :
    False := by
  have hz : ∀ g : A, g ∈ Subgroup.zpowers x → g = 1 ∨ g = x ∨ g = x ^ 2 := fun g hg => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have e : x ^ k = x ^ (k % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
      have : x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
      rw [this, one_zpow, mul_one]
    have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
    have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
    rw [e]
    obtain ⟨r, hr⟩ : ∃ r : ℕ, k % 3 = r := ⟨(k % 3).toNat, (Int.toNat_of_nonneg h0).symm⟩
    rw [hr]
    have hr3 : r < 3 := by omega
    interval_cases r <;> simp
  have hy : x ^ 15 = 1 := by
    calc x ^ 15 = (x ^ 3) ^ 5 := by rw [← pow_mul]
      _ = 1 := by rw [hx3, one_pow]
  have hv : ∀ v : A, v ^ 2 = 1 → v ≠ 1 → v * x * v⁻¹ ∈ Subgroup.zpowers x →
      v * x * v⁻¹ = x⁻¹ := fun v hv2 hv1 hvz => by
    refine CFSG.Walter.J1.A5.conj_inv x v ⟨hx1, hy, hv2, hv1, ?_⟩
    rcases hz _ hvz with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have h1 := hv a ha ha1 hna
  have h2 := hv b hb hb1 hnb
  have e1 : a * b * x * (a * b)⁻¹ = x := by
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * x⁻¹ * a⁻¹ := by rw [h2]
      _ = (a * x * a⁻¹)⁻¹ := by group
      _ = x := by rw [h1, inv_inv]
  have hcent : x * (a * b) = (a * b) * x := (mul_inv_eq_iff_eq_mul.1 e1).symm
  have hab2 : (a * b) ^ 2 = 1 := by
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a * (a * b) * b := by rw [← hc]
      _ = a ^ 2 * b ^ 2 := by rw [pow_two, pow_two]; simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, one_mul]
  have hab1 : a * b ≠ 1 := fun h => by
    have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha)
    exact hab (hb'.trans ha').symm
  rcases CFSG.Walter.J1.A5.centralizer_three x (a * b) ⟨hx3, hx1, hcent⟩ with h | h | h
  · exact hab1 h
  · have h2' : x ^ 2 = 1 := h ▸ hab2
    apply hx1
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx3, h2']; simp
  · have h4 : x ^ 4 = 1 := by
      calc x ^ 4 = (x ^ 2) ^ 2 := by group
        _ = 1 := by rw [← h]; exact hab2
    apply hx1
    calc x = x ^ 4 * (x ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hx3]; simp

theorem card_of_sylow {P : Subgroup A} (hP : IsSylowTwoOf P ⊤) : Nat.card P = 4 := by
  obtain ⟨-, hp, hodd⟩ := hP
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have h1 := Subgroup.relIndex_mul_card P ⊤
  rw [inf_top_eq, Subgroup.card_top, card_a5, hk] at h1
  have hodd' : ¬ 2 ∣ P.relIndex ⊤ := hodd
  have hk5 : k ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h0 : 0 < P.relIndex ⊤ := Nat.pos_of_ne_zero (by rintro h'; rw [h'] at h1; omega)
    have := Nat.le_mul_of_pos_left (2 ^ k) h0
    omega
  rw [hk]
  interval_cases k <;> omega

theorem a5_false {K S Y : Subgroup A} (hK : Nat.card K = 3) (hS : Nat.card S = 4)
    (hSY : S ≤ Y) (hsub : IsSubnormal K Y) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 K := IsPGroup.of_card (p := 3) (n := 1) (by rw [hK]; norm_num)
  have hKcore : K ≤ pCoreOf 3 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 le_rfl Subgroup.le_normalizer hp
  have hKO : K ≤ pCoreOf 3 Y := hKcore.trans (A4.pCoreOf_le_of_subnormal 3 hsub)
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 Y).exists_card_eq
  have hdvd : Nat.card (pCoreOf 3 Y) ∣ 60 := card_a5 ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 h
    rw [← hk] at h9
    have := h9.trans hdvd
    omega
  have hge : Nat.card K ≤ Nat.card (pCoreOf 3 Y) := Subgroup.card_le_of_le hKO
  rw [hK] at hge
  have hKeq : K = pCoreOf 3 Y := by
    refine Subgroup.eq_of_le_of_card_ge hKO ?_
    rw [hK, hk]
    interval_cases k
    · rw [hk] at hge
      simp at hge
    · simp
  have hnorm : Y ≤ Subgroup.normalizer (K : Set A) := by
    rw [hKeq]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 Y
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (by rw [hK])
  have hy3 : (y : A) ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    simpa using congrArg Subtype.val this
  have hy1 : (y : A) ≠ 1 := fun h => by
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy
    omega
  have hzK : Subgroup.zpowers (y : A) = K :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 y.2)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy, hK])
  obtain ⟨a, b, haS, hbS, ha, hb, ha1, hb1, hab, hc⟩ := exists_two_involutions hS
  refine not_normalize ha hb ha1 hb1 hab hc hy3 hy1 ?_ ?_
  · rw [hzK]
    exact (Subgroup.mem_normalizer_iff.1 (hnorm (hSY haS)) (y : A)).1 y.2
  · rw [hzK]
    exact (Subgroup.mem_normalizer_iff.1 (hnorm (hSY hbS)) (y : A)).1 y.2

end A5

section Apply

variable {G : Type} [Group G] [Finite G]

theorem false_of_three_five {X R P K L : Subgroup G} (S : L246C127.Setting X R P K)
    (hL : IsBlock2 X L) (α : ↥L →* alternatingGroup (Fin 5))
    (hα : Function.Surjective α) (hK : Nat.card ((K.subgroupOf L).map α) = 3) : False := by
  have hSyl : IsSylowTwoOf (R ⊓ L) L :=
    L246C127.isSylowTwoOf_inf_of_isSubnormal' (C1GN.isSubnormal_of_isBlock2 hL) S.sylow
  have hYP : K ⊔ (R ⊓ L) ≤ P := sup_le S.KP (inf_le_left.trans S.TP)
  have hsub : IsSubnormal K (K ⊔ (R ⊓ L)) :=
    A4.subnormal_of_le_of_le S.subnormal le_sup_left hYP
  have h2 := A4.subnormal_map α (A4.subnormal_comap L.subtype hsub)
  have hSbar := Setup.Family.isSylowTwoOf_map_range α hSyl
  rw [MonoidHom.range_eq_top.2 hα] at hSbar
  refine a5_false hK (card_of_sylow hSbar) ?_ h2
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  exact Subgroup.mem_map.2 ⟨y, (Subgroup.comap_mono (le_sup_right : R ⊓ L ≤ K ⊔ R ⊓ L)) hy, rfl⟩

end Apply

end CFSG.Quasithin.C58NS.MPB
