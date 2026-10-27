module

public import CFSG.Sporadic.Recognition.JankoWongClasses
public import CFSG.Sporadic.Recognition.JankoWongSylow

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

structure Setup (G : Type) [Group G] [Finite G] where
  z : G
  ρ : ↥(centralizer ({z} : Set G)) →* Perm (Fin 8)
  order_z : orderOf z = 2
  cover : IsCover8 ρ (zIn z)
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a

theorem card_centralizer_perm_type2222 {c : Perm (Fin 8)} (h : c.cycleType = {2, 2, 2, 2}) :
    Nat.card ↥(centralizer ({c} : Set (Perm (Fin 8)))) = 384 := by
  rw [nat_card_centralizer, h]
  simp [Nat.factorial]

theorem card_centralizer_eq_of_isConj {G : Type*} [Group G] [Finite G] {x y : G} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({y} : Set G)) := by
  have hx := card_centralizer_mul_ncard_orbit x
  have hy := card_centralizer_mul_ncard_orbit y
  have horb : MulAction.orbit (ConjAct G) x = MulAction.orbit (ConjAct G) y :=
    (MulAction.orbit_eq_iff).mpr (ConjAct.mem_orbit_conjAct.mpr h)
  rw [horb] at hx
  have hpos : 0 < (MulAction.orbit (ConjAct G) y).ncard := by
    rw [← index_centralizer_eq_ncard]
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  exact Nat.eq_of_mul_eq_mul_right hpos (hx.trans hy.symm)


namespace Setup

variable {G : Type} [Group G] [Finite G] (S : Setup G)

abbrev H : Subgroup G := centralizer ({S.z} : Set G)

theorem oneClass (S : Setup G) : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v :=
  isConj_of_involutions_of_cover8 S.simple S.nonabelian S.order_z S.cover

theorem card_H (S : Setup G) : Nat.card S.H = 40320 := S.cover.nat_card_eq

theorem isCentralInvolution (S : Setup G) : IsCentralInvolution S.z :=
  ⟨S.order_z, exists_sylow_central_of_cover8 S.order_z S.cover⟩

theorem exists_central_involution {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    ∃ u ∈ T, orderOf u = 2 ∧ ∀ t ∈ T, t * u = u * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hne
  have hc : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center T) :=
    hT.of_injective (Subgroup.center T).subtype (Subgroup.center T).subtype_injective
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hcp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
    obtain ⟨hsub, -⟩ := hn
    exact not_subsingleton _ hsub
  have h2 : 2 ∣ Nat.card (Subgroup.center T) := by
    rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T) 2 h2
  refine ⟨((u : T) : G), (u : T).2, ?_, fun t ht => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hu
  · have := Subgroup.mem_center_iff.mp u.2 ⟨t, ht⟩
    exact congrArg Subtype.val this


theorem exists_conj_into_H (S : Setup G) {x : G} {T : Subgroup G} (hT : IsPGroup 2 T)
    (hne : T ≠ ⊥) (hx : ∀ t ∈ T, t * x = x * t) :
    ∃ g : G, g⁻¹ * x * g ∈ S.H ∧ ∀ t ∈ T, g⁻¹ * t * g ∈ S.H := by
  obtain ⟨u, huT, hu2, hucent⟩ := exists_central_involution hT hne
  obtain ⟨c, hc⟩ := isConj_iff.mp (S.oneClass S.z u S.order_z hu2)
  have key : ∀ y : G, y * u = u * y → c⁻¹ * y * c ∈ S.H := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c * S.z * c⁻¹ = u := hc
    calc c⁻¹ * y * c * S.z = c⁻¹ * y * (c * S.z * c⁻¹) * c := by group
      _ = c⁻¹ * (y * u) * c := by rw [h1]; group
      _ = c⁻¹ * (u * y) * c := by rw [hy]
      _ = S.z * (c⁻¹ * y * c) := by
        rw [← h1]; group
  exact ⟨c, key x (hx u huT).symm, fun t ht => key t (hucent t ht)⟩


theorem card_dvd_centralizer_of_conj (S : Setup G) {x : G} {T : Subgroup G} {g : G}
    (hxg : g⁻¹ * x * g ∈ S.H) (hTg : ∀ t ∈ T, g⁻¹ * t * g ∈ S.H)
    (hx : ∀ t ∈ T, t * x = x * t) :
    Nat.card T ∣ Nat.card (centralizer ({(⟨g⁻¹ * x * g, hxg⟩ : S.H)} : Set S.H)) := by
  set x' : S.H := ⟨g⁻¹ * x * g, hxg⟩ with hx'
  have hcent : ∀ t : T, (⟨g⁻¹ * t.1 * g, hTg t.1 t.2⟩ : S.H) ∈ centralizer ({x'} : Set S.H) := by
    intro t
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show g⁻¹ * t.1 * g * (g⁻¹ * x * g) = g⁻¹ * x * g * (g⁻¹ * t.1 * g)
    calc g⁻¹ * t.1 * g * (g⁻¹ * x * g) = g⁻¹ * (t.1 * x) * g := by group
      _ = g⁻¹ * (x * t.1) * g := by rw [hx t.1 t.2]
      _ = g⁻¹ * x * g * (g⁻¹ * t.1 * g) := by group
  let ψ : ↥T →* ↥(centralizer ({x'} : Set S.H)) :=
    { toFun := fun t => ⟨⟨g⁻¹ * t.1 * g, hTg t.1 t.2⟩, hcent t⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        show g⁻¹ * 1 * g = 1
        group
      map_mul' := by
        intro a b
        apply Subtype.ext; apply Subtype.ext
        show g⁻¹ * (a.1 * b.1) * g = g⁻¹ * a.1 * g * (g⁻¹ * b.1 * g)
        group }
  have hinj : Function.Injective ψ := by
    intro a b hab
    have h1 : g⁻¹ * a.1 * g = g⁻¹ * b.1 * g := congrArg (fun y => ((y.1 : S.H) : G)) hab
    apply Subtype.ext
    have := mul_left_cancel (mul_right_cancel h1)
    exact this
  exact Subgroup.card_dvd_of_injective ψ hinj


theorem two_pow_dvd_of_dvd {k n : ℕ} (hk : 2 ^ k ∣ n) (hn : n ≠ 0) (hb : n < 2 ^ 9) :
    k ≤ 8 := by
  have h1 : 2 ^ k ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hk
  by_contra hlt
  push Not at hlt
  have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem two_subgroup_centralizer_cases (S : Setup G) {x : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) (hxT : ∀ t ∈ T, t * x = x * t) :
    Nat.card T ∣ 4 ∨ (Nat.card T ∣ 8 ∧ ∀ y₁ ∈ T, ∀ y₂ ∈ T, y₁ ^ 2 = 1 → y₂ ^ 2 = 1 →
      y₁ ≠ 1 → y₂ ≠ 1 → y₁ = y₂) := by
  obtain ⟨g, hxg, hTg⟩ := S.exists_conj_into_H hT hne hxT
  set x' : S.H := ⟨g⁻¹ * x * g, hxg⟩ with hx'
  have hdvd := S.card_dvd_centralizer_of_conj hxg hTg hxT
  have hx'3 : x' ^ 3 = 1 := by
    apply Subtype.ext
    show (g⁻¹ * x * g) ^ 3 = 1
    have : (g⁻¹ * x * g) ^ 3 = g⁻¹ * x ^ 3 * g := by simp [pow_succ, mul_assoc]
    rw [this, hx3]; simp
  have hx'1 : x' ≠ 1 := by
    intro e
    apply hx1
    have h1 : g⁻¹ * x * g = 1 := congrArg Subtype.val e
    have h2 : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [h2, h1]; group
  have hρ1 : S.ρ x' ≠ 1 := by
    intro e
    rcases S.cover.mem_ker_iff.mp e with h1 | h1
    · exact hx'1 h1
    · rw [h1] at hx'3
      have : (zIn S.z) ^ 3 = zIn S.z := by
        rw [pow_succ, S.cover.sq_eq_one, one_mul]
      rw [this] at hx'3
      exact S.cover.ne_one hx'3
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hT
  rcases cycleType_of_cube_eq_one_ne_one (by rw [← map_pow, hx'3, map_one]) hρ1 with ht | ht
  ·
    right
    have hc := S.cover.card_centralizer_type3 hx'3 ht
    rw [hc, hk] at hdvd
    have hk8 : k ≤ 8 := two_pow_dvd_of_dvd hdvd (by norm_num) (by norm_num)
    refine ⟨?_, ?_⟩
    · rw [hk]
      interval_cases k <;> simp_all
    · intro y₁ hy₁ y₂ hy₂ h₁ h₂ h₁' h₂'
      have key : ∀ y ∈ T, y ^ 2 = 1 → y ≠ 1 → g⁻¹ * y * g = S.z := by
        intro y hy hy2 hy1
        have := S.cover.eq_z_of_involution_centralizer_type3 (x := x')
          (y := ⟨g⁻¹ * y * g, hTg y hy⟩) ht ?_ ?_ ?_
        · exact congrArg Subtype.val this
        · apply Subtype.ext
          show (g⁻¹ * y * g) ^ 2 = 1
          have : (g⁻¹ * y * g) ^ 2 = g⁻¹ * y ^ 2 * g := by simp [pow_two, mul_assoc]
          rw [this, hy2]; simp
        · intro e
          apply hy1
          have h1 : g⁻¹ * y * g = 1 := congrArg Subtype.val e
          have h2 : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
          rw [h2, h1]; group
        · apply Subtype.ext
          show g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * x * g * (g⁻¹ * y * g)
          calc g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
            _ = g⁻¹ * (x * y) * g := by rw [hxT y hy]
            _ = g⁻¹ * x * g * (g⁻¹ * y * g) := by group
      have e1 := key y₁ hy₁ h₁ h₁'
      have e2 := key y₂ hy₂ h₂ h₂'
      have : g⁻¹ * y₁ * g = g⁻¹ * y₂ * g := by rw [e1, e2]
      exact mul_left_cancel (mul_right_cancel this)
  ·
    left
    have hc := S.cover.card_centralizer_type33 hx'3 ht
    rw [hc, hk] at hdvd
    have hk8 : k ≤ 8 := two_pow_dvd_of_dvd hdvd (by norm_num) (by norm_num)
    rw [hk]
    interval_cases k <;> simp_all


theorem factorization_two_360 : (360 : ℕ).factorization 2 = 3 := by
  have : (360 : ℕ) = 2 ^ 3 * 45 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  have h45 : (45 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h45]

theorem factorization_two_36 : (36 : ℕ).factorization 2 = 2 := by
  have : (36 : ℕ) = 2 ^ 2 * 9 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  have h9 : (9 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h9]

theorem isPGroup_two_zpowers {M : Type*} [Group M] {t : M} (ht : t ^ 2 = 1) :
    IsPGroup 2 ↥(zpowers t) := by
  rw [IsPGroup.iff_orderOf]
  intro g
  have hg : (g : M) ^ 2 = 1 := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  have hd : orderOf (g : M) ∣ 2 := orderOf_dvd_of_pow_eq_one hg
  rw [Subgroup.orderOf_coe] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · exact ⟨0, by simpa using h1⟩
  · exact ⟨1, by simpa using h1⟩

theorem exists_sylow_image (S : Setup G) (x t : S.H) (htx : t ∈ centralizer ({x} : Set S.H))
    (ht2 : t ^ 2 = 1) :
    ∃ Q : Subgroup G, IsPGroup 2 Q ∧ (∀ q ∈ Q, q * (x : G) = (x : G) * q) ∧
      Nat.card Q = 2 ^ (Nat.card (centralizer ({x} : Set S.H))).factorization 2 ∧
        S.z ∈ Q ∧ (t : G) ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup S.H := centralizer ({x} : Set S.H) with hC
  have hzC : zIn S.z ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp (zIn_mem_center S.z) x).symm
  set t' : C := ⟨t, htx⟩ with ht'
  set z' : C := ⟨zIn S.z, hzC⟩ with hz'
  have ht'2 : t' ^ 2 = 1 := Subtype.ext ht2
  have hz'2 : z' ^ 2 = 1 := Subtype.ext (Subtype.ext (by
    show S.z ^ 2 = 1
    rw [← S.order_z]; exact pow_orderOf_eq_one S.z))
  obtain ⟨Q_E, hQt⟩ := (isPGroup_two_zpowers ht'2).exists_le_sylow
  have hz'Q : z' ∈ (Q_E : Subgroup C) := by
    have hzc : z' ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (zIn_mem_center S.z) c.1)
    have hnorm : (zpowers z').Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
    exact (isPGroup_two_zpowers hz'2).le_sylow_of_normal Q_E (Subgroup.mem_zpowers z')
  have ht'Q : t' ∈ (Q_E : Subgroup C) := hQt (Subgroup.mem_zpowers t')
  refine ⟨((Q_E : Subgroup C).map C.subtype).map S.H.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Q_E.isPGroup'.map C.subtype).map S.H.subtype
  · rintro q ⟨e, ⟨c, hc, rfl⟩, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp c.2
    exact congrArg Subtype.val this
  · rw [Subgroup.card_map_of_injective S.H.subtype_injective,
      Subgroup.card_map_of_injective C.subtype_injective]
    exact Q_E.card_eq_multiplicity
  · exact ⟨zIn S.z, ⟨z', hz'Q, rfl⟩, rfl⟩
  · exact ⟨t, ⟨t', ht'Q, rfl⟩, rfl⟩


theorem sylow_card_eq_of_max {C A : Subgroup G} (hA : IsPGroup 2 A) (hAC : A ≤ C)
    (hmax : ∀ B : Subgroup G, IsPGroup 2 B → B ≤ C → A ≤ B → Nat.card B ≤ Nat.card A)
    (T : Sylow 2 ↥C) : Nat.card T = Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA' : IsPGroup 2 ↥(A.subgroupOf C) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAC).symm
  obtain ⟨T', hT'⟩ := hA'.exists_le_sylow
  set B : Subgroup G := (T' : Subgroup C).map C.subtype with hB
  have hBp : IsPGroup 2 B := T'.isPGroup'.map C.subtype
  have hBC : B ≤ C := by
    rintro _ ⟨c, -, rfl⟩; exact c.2
  have hAB : A ≤ B := by
    intro a ha
    exact ⟨⟨a, hAC ha⟩, hT' (by simpa [Subgroup.mem_subgroupOf] using ha), rfl⟩
  have hcardB : Nat.card B = Nat.card T' := Subgroup.card_map_of_injective C.subtype_injective
  have h1 : Nat.card B ≤ Nat.card A := hmax B hBp hBC hAB
  have h2 : Nat.card A ≤ Nat.card B := Subgroup.card_le_of_le hAB
  have h3 : Nat.card T' = Nat.card A := by omega
  rw [← h3, T.card_eq_multiplicity, T'.card_eq_multiplicity]


theorem zIn_sq (S : Setup G) : (zIn S.z) ^ 2 = 1 := S.cover.sq_eq_one

theorem zIn_mem_centralizer (S : Setup G) (x : S.H) : zIn S.z ∈ centralizer ({x} : Set S.H) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_center_iff.mp (zIn_mem_center S.z) x).symm

theorem card_sylow_centralizer_type3 (S : Setup G) {x : S.H} (hx3 : x ^ 3 = 1)
    (ht : (S.ρ x).cycleType = {3}) (T : Sylow 2 ↥(centralizer ({(x : G)} : Set G))) :
    Nat.card T = 8 := by
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hx1 : (x : G) ≠ 1 := by
    intro e
    have : x = 1 := Subtype.ext e
    rw [this, map_one, cycleType_one] at ht
    simp at ht
  obtain ⟨Q, hQ2, hQx, hQcard, hzQ, -⟩ := exists_sylow_image S x (zIn S.z)
    (zIn_mem_centralizer S x) (zIn_sq S)
  rw [S.cover.card_centralizer_type3 hx3 ht, factorization_two_360] at hQcard
  have hQC : Q ≤ centralizer ({(x : G)} : Set G) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hQx q hq)
  have hz1 : S.z ≠ 1 := fun e => S.cover.ne_one (Subtype.ext e)
  have hmax : ∀ B : Subgroup G, IsPGroup 2 B → B ≤ centralizer ({(x : G)} : Set G) → Q ≤ B →
      Nat.card B ≤ Nat.card Q := by
    intro B hB hBC hQB
    have hBne : B ≠ ⊥ := fun e => hz1 (by
      have := hQB hzQ
      rw [e] at this
      simpa using this)
    have hBx : ∀ t ∈ B, t * (x : G) = (x : G) * t := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hBC ht)
    rw [hQcard]
    rcases S.two_subgroup_centralizer_cases hxG3 hx1 hB hBne hBx with h | ⟨h, -⟩
    · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) h
  rw [sylow_card_eq_of_max hQ2 hQC hmax T, hQcard]
  norm_num

theorem card_sylow_centralizer_type33 (S : Setup G) {x : S.H} (hx3 : x ^ 3 = 1)
    (ht : (S.ρ x).cycleType = {3, 3}) (T : Sylow 2 ↥(centralizer ({(x : G)} : Set G))) :
    Nat.card T = 4 := by
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hx1 : (x : G) ≠ 1 := by
    intro e
    have : x = 1 := Subtype.ext e
    rw [this, map_one, cycleType_one] at ht
    simp at ht
  obtain ⟨t, ht2, ht1, htz, htc⟩ := S.cover.exists_involution_centralizer_type33 hx3 ht
  have htx : t ∈ centralizer ({x} : Set S.H) := Subgroup.mem_centralizer_singleton_iff.mpr htc
  obtain ⟨Q, hQ2, hQx, hQcard, hzQ, htQ⟩ := exists_sylow_image S x t htx (by
    exact ht2)
  rw [S.cover.card_centralizer_type33 hx3 ht, factorization_two_36] at hQcard
  have hQC : Q ≤ centralizer ({(x : G)} : Set G) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hQx q hq)
  have hz1 : S.z ≠ 1 := fun e => S.cover.ne_one (Subtype.ext e)
  have hmax : ∀ B : Subgroup G, IsPGroup 2 B → B ≤ centralizer ({(x : G)} : Set G) → Q ≤ B →
      Nat.card B ≤ Nat.card Q := by
    intro B hB hBC hQB
    have hBne : B ≠ ⊥ := fun e => hz1 (by
      have := hQB hzQ
      rw [e] at this
      simpa using this)
    have hBx : ∀ t ∈ B, t * (x : G) = (x : G) * t := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mp (hBC ht)
    rw [hQcard]
    rcases S.two_subgroup_centralizer_cases hxG3 hx1 hB hBne hBx with h | ⟨-, huniq⟩
    · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
    · exfalso
      have hzB : S.z ∈ B := hQB hzQ
      have htB : (t : G) ∈ B := hQB htQ
      have hz2 : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z
      have ht2' : (t : G) ^ 2 = 1 := by
        have := congrArg Subtype.val ht2
        simpa using this
      have ht1' : (t : G) ≠ 1 := fun e => ht1 (Subtype.ext e)
      have := huniq _ htB _ hzB ht2' hz2 ht1' hz1
      exact htz (Subtype.ext this)
  rw [sylow_card_eq_of_max hQ2 hQC hmax T, hQcard]
  norm_num


end Setup

namespace IsCover8

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 8)} {z : E}

theorem card_le_three_of_three_subgroup (h : IsCover8 ρ z) [Finite E] {t : E} (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (htz : t ≠ z) {X : Subgroup E} (hX : IsPGroup 3 X)
    (hXt : ∀ x ∈ X, x * t = t * x) : Nat.card X ≤ 3 := by
  have hty := h.type2222_of_involution ht2 ht1 htz
  have hmem : ∀ x : X, ρ x.1 ∈ centralizer ({ρ t} : Set (Perm (Fin 8))) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hXt x.1 x.2]
  let f : ↥X →* ↥(centralizer ({ρ t} : Set (Perm (Fin 8)))) :=
    { toFun := fun x => ⟨ρ x.1, hmem x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : ρ a.1 = ρ b.1 := congrArg Subtype.val hab
    have h2 : ρ (a.1⁻¹ * b.1) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    rcases h.mem_ker_iff.mp h2 with h3 | h3
    · exact Subtype.ext (inv_mul_eq_one.mp h3)
    · exfalso
      have hzX : z ∈ X := by
        have : a.1⁻¹ * b.1 ∈ X := X.mul_mem (X.inv_mem a.2) b.2
        rwa [h3] at this
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨z, hzX⟩
      have hz : orderOf (⟨z, hzX⟩ : X) = 2 := by
        rw [← Subgroup.orderOf_coe]; exact h.orderOf_z
      rw [hz] at hj
      have : (3 : ℕ) ∣ 2 ^ 0 ∨ True := Or.inr trivial
      rcases j with _ | j
      · simp at hj
      · have h3d : 3 ∣ 2 := by rw [hj]; exact dvd_pow_self 3 (Nat.succ_ne_zero j)
        omega
  have hdvd := Subgroup.card_dvd_of_injective f hinj
  rw [card_centralizer_perm_type2222 hty] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk] at hdvd ⊢
  have hk8 : k ≤ 8 := by
    have h1 : 3 ^ k ≤ 384 := Nat.le_of_dvd (by norm_num) hdvd
    by_contra hlt
    push Not at hlt
    have : 3 ^ 9 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  interval_cases k <;> simp_all

end IsCover8

namespace Setup

variable {G : Type} [Group G] [Finite G]

theorem not_isConj_type3_type33 (S : Setup G) {x y : S.H} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hx : (S.ρ x).cycleType = {3}) (hy : (S.ρ y).cycleType = {3, 3}) :
    ¬ IsConj (x : G) (y : G) := by
  intro hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T1⟩ : Nonempty (Sylow 2 ↥(centralizer ({(x : G)} : Set G))) := inferInstance
  obtain ⟨T2⟩ : Nonempty (Sylow 2 ↥(centralizer ({(y : G)} : Set G))) := inferInstance
  have h1 := S.card_sylow_centralizer_type3 hx3 hx T1
  have h2 := S.card_sylow_centralizer_type33 hy3 hy T2
  have hcard := card_centralizer_eq_of_isConj hc
  rw [T1.card_eq_multiplicity, hcard] at h1
  rw [T2.card_eq_multiplicity] at h2
  rw [h2] at h1
  norm_num at h1


theorem factorization_three_40320 : (40320 : ℕ).factorization 3 = 2 := by
  have : (40320 : ℕ) = 3 ^ 2 * 4480 := by norm_num
  rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three]
  have h4480 : (4480 : ℕ).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  simp [h4480]

theorem not_centralizer_le_H (S : Setup G) {x : S.H} (hx3 : x ^ 3 = 1)
    (ht : (S.ρ x).cycleType = {3, 3}) :
    ¬ centralizer ({(x : G)} : Set G) ≤ S.H := by
  intro hle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, ht2, ht1, htz, htc⟩ := S.cover.exists_involution_centralizer_type33 hx3 ht
  have hxG3 : (x : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx3
    simpa using this
  have hx1 : (x : G) ≠ 1 := by
    intro e
    have : x = 1 := Subtype.ext e
    rw [this, map_one, cycleType_one] at ht
    simp at ht
  have htG2 : (t : G) ^ 2 = 1 := by
    have := congrArg Subtype.val ht2
    simpa using this
  have htG1 : (t : G) ≠ 1 := fun e => ht1 (Subtype.ext e)
  have htGcomm : (t : G) * (x : G) = (x : G) * (t : G) := congrArg Subtype.val htc
  have hcard : Nat.card (centralizer ({(t : G)} : Set G)) = 40320 := by
    have hconj : IsConj (t : G) S.z := S.oneClass _ _ (orderOf_eq_prime htG2 htG1) S.order_z
    rw [card_centralizer_eq_of_isConj hconj]
    exact S.card_H
  have hxC : (x : G) ∈ centralizer ({(t : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htGcomm.symm
  have hxp : IsPGroup 3 ↥(zpowers (⟨(x : G), hxC⟩ : centralizer ({(t : G)} : Set G))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hxG3 hx1
  obtain ⟨X, hX⟩ := hxp.exists_le_sylow
  have hXcard : Nat.card X = 3 ^ 2 := by
    rw [X.card_eq_multiplicity, hcard, factorization_three_40320]
  have hXcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hXcard
  set XG : Subgroup G := (X : Subgroup (centralizer ({(t : G)} : Set G))).map
    (centralizer ({(t : G)} : Set G)).subtype with hXG
  have hXGp : IsPGroup 3 XG := X.isPGroup'.map _
  have hXGcard : Nat.card XG = 9 := by
    rw [hXG, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hXcard]; norm_num
  have hxX : (⟨(x : G), hxC⟩ : centralizer ({(t : G)} : Set G)) ∈ (X : Subgroup _) :=
    hX (Subgroup.mem_zpowers _)
  have hXGx : ∀ y ∈ XG, y * (x : G) = (x : G) * y := by
    rintro _ ⟨c, hc, rfl⟩
    have h2 := hXcomm.is_comm.comm ⟨c, hc⟩ ⟨_, hxX⟩
    exact congrArg (fun w : ↥(X : Subgroup (centralizer ({(t : G)} : Set G))) => (w.1 : G)) h2
  have hXGH : XG ≤ S.H := fun y hy =>
    hle (Subgroup.mem_centralizer_singleton_iff.mpr (hXGx y hy))
  have hXGt : ∀ y ∈ XG, y * (t : G) = (t : G) * y := by
    rintro _ ⟨c, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hbound := S.cover.card_le_three_of_three_subgroup ht2 ht1 htz (X := XG.subgroupOf S.H)
    (hXGp.of_equiv (Subgroup.subgroupOfEquivOfLe hXGH).symm) (fun y hy => by
      apply Subtype.ext
      exact hXGt y.1 hy)
  have h9 : Nat.card (XG.subgroupOf S.H) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXGH).toEquiv, hXGcard]
  rw [h9] at hbound
  omega

end Setup
end CFSG.Sporadic.Recognition.JankoWong
