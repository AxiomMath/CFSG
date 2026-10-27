module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res5ProofBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG
open CFSG.Assembly (IsElemAbelian)
open scoped MatrixGroups

namespace Item211Res5Proof

open Item211Res4Proof

section Small

variable {F : Type} [Field F]

theorem two_three_ne_zero [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p) :
    (2 : F) ≠ 0 ∧ (3 : F) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime (by rw [Fintype.card_eq_nat_card, hF])
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  · have h' := (CharP.cast_eq_zero_iff F p 3).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) h'
    omega

@[expose] def ordThree (F : Type) [Field F] : SL(2, F) :=
  ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two]⟩

theorem ordThree_pow_three : ordThree F ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ordThree, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem ordThree_ne_one : ordThree F ≠ 1 := by
  intro h
  have e := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [ordThree] at e

theorem le_center_of_normal_isPGroup {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) (h2 : IsPGroup 2 N) : N ≤ Subgroup.center Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center Q
  set π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  have hsimple : IsSimpleGroup (Q ⧸ Z) := hQ.2.1
  have hnorm : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective Z)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
  · intro x hx
    have hxmap : π x ∈ N.map π := Subgroup.mem_map_of_mem π hx
    rw [hbot, Subgroup.mem_bot] at hxmap
    exact (QuotientGroup.eq_one_iff x).mp hxmap
  · exfalso
    have hp : IsPGroup 2 (Q ⧸ Z) := by
      intro g
      obtain ⟨n, hn, rfl⟩ : g ∈ N.map π := htop ▸ Subgroup.mem_top g
      obtain ⟨k, hk⟩ := h2 ⟨n, hn⟩
      exact ⟨k, by rw [← map_pow]; rw [show n ^ 2 ^ k = 1 from congrArg Subtype.val hk,
        map_one]⟩
    have := hsimple.toNontrivial
    have hcen : Nontrivial (Subgroup.center (Q ⧸ Z)) := hp.center_nontrivial
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Z)) with h | h
    · exact (Subgroup.nontrivial_iff_ne_bot _).mp hcen h
    · obtain ⟨a, b, hab⟩ := hQ.2.2
      apply hab
      have hb : b ∈ Subgroup.center (Q ⧸ Z) := h ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp hb a)

end Small

section Minus

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {κ₁ κ₂ : SL(2, F) →* G} {z : G}

theorem BlockPair.moves_or_le_threeGen (hB : BlockPair κ₁ κ₂ z) (hF4 : 4 ≤ Nat.card F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (T : Subgroup G) :
    (∃ t ∈ T, ∃ c, t * κ₁ c * t⁻¹ ≠ κ₁ c) ∨ ∀ c, κ₁ c ∈
      threeGen (Subgroup.centralizer ({z} : Set G)) ⊓ Subgroup.centralizer (T : Set G) := by
  by_cases h : ∃ t ∈ T, ∃ c, t * κ₁ c * t⁻¹ ≠ κ₁ c
  · exact Or.inl h
  push Not at h
  right
  intro c
  have hz : ∀ c, κ₁ c ∈ Subgroup.centralizer ({z} : Set G) := fun c =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hB.mul_z₁ c)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · refine Item211Lie3Proof.mem_of_normalizer hF4 h2 κ₁
      (fun a => mem_normalizer_threeGen (hz a))
      (not_isScalar2_of_cube h3 ordThree_pow_three ordThree_ne_one) ordThree_pow_three
      (z := 1) (fun a => by rw [mul_one, one_mul]) ?_ c
    rw [mul_one]
    exact Subgroup.subset_closure ⟨hz _, 1, by rw [pow_one, ← map_pow, ordThree_pow_three,
      map_one]⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := h t ht c
    calc t * κ₁ c = t * κ₁ c * t⁻¹ * t := by group
      _ = κ₁ c * t := by rw [this]

theorem BlockPair.minus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    (hB : BlockPair κ₁ κ₂ z) {T : Subgroup G} (hzT : z ∈ T)
    (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) {x : G} (hx3 : x ^ 3 = 1)
    (hxT : x ∈ Subgroup.centralizer (T : Set G)) :
    x ∈ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (threeGen (Subgroup.centralizer ({z} : Set G)) ⊓ Subgroup.centralizer (T : Set G)) :
        Subgroup G) : Set G) := by
  obtain ⟨h2, h3⟩ := two_three_ne_zero hp hp5 hF
  have hF4 : 4 ≤ Nat.card F := by omega
  set H := threeGen (Subgroup.centralizer ({z} : Set G)) ⊓ Subgroup.centralizer (T : Set G)
    with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H
  have hthree : threeGen (Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.closure_le _).mpr fun y hy => hy.1
  have hHz : ∀ h ∈ H, h * z = z * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hthree (Subgroup.mem_inf.mp hh).1)
  have hTz' : ∀ t ∈ T, t * z = z * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (hTz ht)
  have hxz : x * z = z * x := (Subgroup.mem_centralizer_iff.mp hxT z hzT).symm
  have hxH : x ∈ H := Subgroup.mem_inf.mpr ⟨Subgroup.subset_closure
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxz, 1, by rw [pow_one, hx3]⟩, hxT⟩
  have hHT : H ≤ Subgroup.centralizer (T : Set G) := fun h hh => (Subgroup.mem_inf.mp hh).2
  obtain ⟨a, b, hx, ha3, hb3⟩ := hB.cube_decomp hxz hx3
  have hxt : ∀ t ∈ T, t * (κ₁ a * κ₂ b) * t⁻¹ = κ₁ a * κ₂ b := fun t ht => by
    rw [← hx, (Subgroup.mem_centralizer_iff.mp hxT t ht), mul_inv_cancel_right]
  have haT : ∀ t ∈ T, t * κ₁ a * t⁻¹ = κ₁ a := fun t ht =>
    (hB.commute_parts h2 (hB.norm₁ t (hTz' t ht)) (hB.norm₂ t (hTz' t ht)) ha3 (hxt t ht)).1
  have hbT : ∀ t ∈ T, t * κ₂ b * t⁻¹ = κ₂ b := fun t ht => by
    have e : t * (κ₂ b * κ₁ a) * t⁻¹ = κ₂ b * κ₁ a := by rw [← hB.comm a b]; exact hxt t ht
    exact (hB.symm.commute_parts h2 (hB.norm₂ t (hTz' t ht)) (hB.norm₁ t (hTz' t ht)) hb3 e).1
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hcase₁ : (∀ h ∈ H, h * κ₁ a = κ₁ a * h) ∨ (∃ t ∈ T, ∃ c, t * κ₁ c * t⁻¹ ≠ κ₁ c) ∨
      (∀ c, κ₁ c ∈ H) := Or.inr (hB.moves_or_le_threeGen hF4 h2 h3 T)
  have hcase₂ : (∀ h ∈ H, h * κ₂ b = κ₂ b * h) ∨ (∃ t ∈ T, ∃ c, t * κ₂ c * t⁻¹ ≠ κ₂ c) ∨
      (∀ c, κ₂ c ∈ H) := Or.inr (hB.symm.moves_or_le_threeGen hF4 h2 h3 T)
  obtain ⟨a₁, ha₁, haa⟩ := conj_commute_of_cases hp hp5 hF hB.inj₁ hQ2 hQH hHQ
    (fun h hh => hB.norm₁ h (hHz h hh)) (fun t ht => hB.norm₁ t (hTz' t ht)) hHT haT hcase₁ hq
  obtain ⟨b₁, hb₁, hbb⟩ := conj_commute_of_cases hp hp5 hF hB.inj₂ hQ2 hQH hHQ
    (fun h hh => hB.norm₂ h (hHz h hh)) (fun t ht => hB.norm₂ t (hTz' t ht)) hHT hbT hcase₂ hq
  exact commute_of_parts hB hQ2 hq (hHQ hxH) hx ha3 hb3 ha₁ hb₁ haa hbb

end Minus

section Plus

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {κ₁ κ₂ : SL(2, F) →* G} {z : G}

theorem BlockPair.plusPart {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    (hB : BlockPair κ₁ κ₂ z) {D T : Subgroup G} (hDe : IsElemAbelian 3 D) {d : G} (hdD : d ∈ D)
    (hTD : T ≤ Subgroup.centralizer (D : Set G)) (hzT : z ∈ T)
    (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) {a₀ b₀ : SL(2, F)} (hd : d = κ₁ a₀ * κ₂ b₀)
    (ha₀3 : a₀ ^ 3 = 1) (hb₀3 : b₀ ^ 3 = 1) (hd1 : d ≠ 1) {x : G} (hxD : x ∈ D)
    {a b : SL(2, F)} (hx : x = κ₁ a * κ₂ b) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) {q : G}
    (hq : q ∈ inSubgroup (CFSG.pCore 2)
      (conjClosure D (Subgroup.centralizer ({d} : Set G)) ⊓ Subgroup.centralizer (T : Set G))) :
    ∃ a₁ : SL(2, F), q * κ₁ a * q⁻¹ = κ₁ a₁ ∧ a₁ * a = a * a₁ := by
  obtain ⟨h2, h3⟩ := two_three_ne_zero hp hp5 hF
  have hF4 : 4 ≤ Nat.card F := by omega
  set Cd := Subgroup.centralizer ({d} : Set G) with hCd
  set Cl := conjClosure D Cd with hCl
  set H := Cl ⊓ Subgroup.centralizer (T : Set G) with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H
  have hDcomm : ∀ y ∈ D, ∀ w ∈ D, y * w = w * y := fun y hy w hw =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨y, hy⟩ ⟨w, hw⟩)
  have hDCd : D ≤ Cd := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hDcomm y hy d hdD)
  have hClCd : Cl ≤ Cd := conjClosure_le hDCd
  have hHT : H ≤ Subgroup.centralizer (T : Set G) := fun h hh => (Subgroup.mem_inf.mp hh).2
  have hHz : ∀ h ∈ H, h * z = z * h := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp (hHT hh) z hzT).symm
  have hHd : ∀ h ∈ H, h * d * h⁻¹ = d := fun h hh => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hClCd (Subgroup.mem_inf.mp hh).1),
      mul_inv_cancel_right]
  have hTz' : ∀ t ∈ T, t * z = z * t := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mp (hTz ht)
  have hDz : ∀ y ∈ D, y * z = z * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (hTD hzT) y hy
  have hHn₁ : ∀ h ∈ H, ∀ c, h * κ₁ c * h⁻¹ ∈ κ₁.range := fun h hh => hB.norm₁ h (hHz h hh)
  have hTn₁ : ∀ t ∈ T, ∀ c, t * κ₁ c * t⁻¹ ∈ κ₁.range := fun t ht => hB.norm₁ t (hTz' t ht)
  have hHa₀ : ∀ h ∈ H, h * κ₁ a₀ * h⁻¹ = κ₁ a₀ := fun h hh =>
    (hB.commute_parts h2 (hHn₁ h hh) (hB.norm₂ h (hHz h hh)) ha₀3
      (by rw [← hd]; exact hHd h hh)).1
  have hxd : x * (κ₁ a₀ * κ₂ b₀) * x⁻¹ = κ₁ a₀ * κ₂ b₀ := by
    rw [← hd, hDcomm x hxD d hdD, mul_inv_cancel_right]
  have hxa₀ := (hB.commute_parts h2 (hB.norm₁ x (hDz x hxD)) (hB.norm₂ x (hDz x hxD)) ha₀3 hxd).1
  have hxb₀ : x * κ₂ b₀ * x⁻¹ = κ₂ b₀ := by
    have e : x * (κ₂ b₀ * κ₁ a₀) * x⁻¹ = κ₂ b₀ * κ₁ a₀ := by rw [← hB.comm a₀ b₀]; exact hxd
    exact (hB.symm.commute_parts h2 (hB.norm₂ x (hDz x hxD)) (hB.norm₁ x (hDz x hxD)) hb₀3 e).1
  have haa₀ : a * a₀ = a₀ * a := by
    apply hB.inj₁
    have e : x * κ₁ a₀ * x⁻¹ = κ₁ a * κ₁ a₀ * (κ₁ a)⁻¹ := by
      rw [hx]
      have hc := hB.comm a₀ b
      calc κ₁ a * κ₂ b * κ₁ a₀ * (κ₁ a * κ₂ b)⁻¹ =
          κ₁ a * (κ₂ b * κ₁ a₀) * (κ₂ b)⁻¹ * (κ₁ a)⁻¹ := by group
        _ = κ₁ a * κ₁ a₀ * (κ₁ a)⁻¹ := by rw [← hc]; group
    rw [hxa₀] at e
    rw [map_mul, map_mul]
    calc κ₁ a * κ₁ a₀ = κ₁ a * κ₁ a₀ * (κ₁ a)⁻¹ * κ₁ a := by group
      _ = κ₁ a₀ * κ₁ a := by rw [← e]
  have hbb₀ : b * b₀ = b₀ * b := by
    apply hB.inj₂
    have e : x * κ₂ b₀ * x⁻¹ = κ₂ b * κ₂ b₀ * (κ₂ b)⁻¹ := by
      rw [hx]
      have hc := hB.comm a b₀
      calc κ₁ a * κ₂ b * κ₂ b₀ * (κ₁ a * κ₂ b)⁻¹ =
          κ₁ a * (κ₂ b * κ₂ b₀ * (κ₂ b)⁻¹) * (κ₁ a)⁻¹ := by group
        _ = κ₂ b * κ₂ b₀ * (κ₂ b)⁻¹ := by
          have hw := hB.comm a (b * b₀ * b⁻¹)
          rw [map_mul, map_mul, map_inv] at hw
          rw [hw]
          group
    rw [hxb₀] at e
    rw [map_mul, map_mul]
    calc κ₂ b * κ₂ b₀ = κ₂ b * κ₂ b₀ * (κ₂ b)⁻¹ * κ₂ b := by group
      _ = κ₂ b₀ * κ₂ b := by rw [← e]
  have haT : ∀ t ∈ T, t * κ₁ a * t⁻¹ = κ₁ a := fun t ht =>
    (hB.commute_parts h2 (hTn₁ t ht) (hB.norm₂ t (hTz' t ht)) ha3
      (by rw [← hx, (Subgroup.mem_centralizer_iff.mp (hTD ht) x hxD).symm,
        mul_inv_cancel_right])).1
  by_cases ha₀1 : a₀ = 1
  ·
    have hd' : d = κ₂ b₀ := by rw [hd, ha₀1, map_one, one_mul]
    by_cases hmv : ∃ t ∈ T, ∃ c, t * κ₁ c * t⁻¹ ≠ κ₁ c
    · exact conj_commute_of_cases hp hp5 hF hB.inj₁ hQ2 hQH hHQ hHn₁ hTn₁ hHT haT
        (Or.inr (Or.inl hmv)) hq
    push Not at hmv
    by_cases ha1 : a = 1
    · exact ⟨1, by rw [ha1, map_one, mul_one, mul_inv_cancel], by rw [ha1]⟩
    have hb₀1 : b₀ ≠ 1 := fun h => hd1 (by rw [hd', h, map_one])
    have hbD : κ₂ b ∈ D := by
      rcases eq_one_or_eq_of_commute_of_cube h3 hb₀3 hb₀1 hb3 hbb₀ with h | h | h
      · rw [h, map_one]; exact D.one_mem
      · rw [h, ← hd']; exact hdD
      · rw [h, map_mul, ← hd']; exact D.mul_mem hdD hdD
    have haD : κ₁ a ∈ D := by
      have e : κ₁ a = x * (κ₂ b)⁻¹ := by rw [hx, mul_inv_cancel_right]
      rw [e]
      exact D.mul_mem hxD (D.inv_mem hbD)
    have hκCd : ∀ c, κ₁ c ∈ Cd := fun c => by
      rw [Subgroup.mem_centralizer_singleton_iff, hd']
      exact hB.comm c b₀
    have hκH : ∀ c, κ₁ c ∈ H := by
      intro c
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · refine Item211Lie3Proof.mem_of_normalizer hF4 h2 κ₁
          (fun a' => mem_normalizer_conjClosure' (hκCd a'))
          (not_isScalar2_of_cube h3 ha3 ha1) ha3 (z := 1) (fun a' => by rw [mul_one, one_mul])
          ?_ c
        rw [mul_one]
        exact le_conjClosure haD
      · rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have := hmv t ht c
        calc t * κ₁ c = t * κ₁ c * t⁻¹ * t := by group
          _ = κ₁ c * t := by rw [this]
    exact conj_commute_of_cases hp hp5 hF hB.inj₁ hQ2 hQH hHQ hHn₁ hTn₁ hHT haT
      (Or.inr (Or.inr hκH)) hq
  ·
    have hHa : ∀ h ∈ H, h * κ₁ a = κ₁ a * h := by
      intro h hh
      have hfix : h * κ₁ a * h⁻¹ = κ₁ a := by
        rcases eq_one_or_eq_of_commute_of_cube h3 ha₀3 ha₀1 ha3 haa₀ with e | e | e
        · rw [e, map_one, mul_one, mul_inv_cancel]
        · rw [e, hHa₀ h hh]
        · rw [e, map_mul]
          calc h * (κ₁ a₀ * κ₁ a₀) * h⁻¹ = (h * κ₁ a₀ * h⁻¹) * (h * κ₁ a₀ * h⁻¹) := by group
            _ = κ₁ a₀ * κ₁ a₀ := by rw [hHa₀ h hh]
      calc h * κ₁ a = h * κ₁ a * h⁻¹ * h := by group
        _ = κ₁ a * h := by rw [hfix]
    exact conj_commute_of_cases hp hp5 hF hB.inj₁ hQ2 hQH hHQ hHn₁ hTn₁ hHT haT (Or.inl hHa) hq

theorem BlockPair.plus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p)
    (hB : BlockPair κ₁ κ₂ z) {D T : Subgroup G} (hDe : IsElemAbelian 3 D) {d : G} (hdD : d ∈ D)
    (hd1 : d ≠ 1) (hTD : T ≤ Subgroup.centralizer (D : Set G)) (hzT : z ∈ T)
    (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) :
    D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D (Subgroup.centralizer ({d} : Set G)) ⊓ Subgroup.centralizer (T : Set G)) :
        Subgroup G) : Set G) := by
  set H := conjClosure D (Subgroup.centralizer ({d} : Set G)) ⊓
    Subgroup.centralizer (T : Set G) with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H
  have hDz : ∀ y ∈ D, y * z = z * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (hTD hzT) y hy
  obtain ⟨a₀, b₀, hd, ha₀3, hb₀3⟩ := hB.cube_decomp (hDz d hdD) (hDe.2 d hdD)
  have hd' : d = κ₂ b₀ * κ₁ a₀ := by rw [hd, hB.comm]
  intro x hxD
  obtain ⟨a, b, hx, ha3, hb3⟩ := hB.cube_decomp (hDz x hxD) (hDe.2 x hxD)
  have hx' : x = κ₂ b * κ₁ a := by rw [hx, hB.comm]
  have hxH : x ∈ H := Subgroup.mem_inf.mpr ⟨le_conjClosure hxD,
    Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_iff.mp (hTD ht) x hxD).symm⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨a₁, ha₁, haa⟩ := hB.plusPart hp hp5 hF hDe hdD hTD hzT hTz hd ha₀3 hb₀3 hd1 hxD hx ha3
    hb3 hq
  obtain ⟨b₁, hb₁, hbb⟩ := hB.symm.plusPart hp hp5 hF hDe hdD hTD hzT hTz hd' hb₀3 ha₀3 hd1 hxD
    hx' hb3 ha3 hq
  exact (commute_of_parts hB hQ2 hq (hHQ hxH) hx ha3 hb3 ha₁ hb₁ haa hbb)

end Plus

section Bot

variable {G : Type} [Group G]

theorem centralizer_le_normalizer_pCore {D : Subgroup G} {d : G} :
    Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D (Subgroup.centralizer ({d} : Set G))) : Subgroup G) : Set G) := fun _ hg =>
  CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _
    (mem_normalizer_conjClosure' hg)

theorem plus_bot_of_commutator {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F)
    (h2 : (2 : F) ≠ 0) {κ : SL(2, F) →* G} (hinj : Function.Injective κ) {D : Subgroup G}
    (hDe : IsElemAbelian 3 D) {d : G} (hdD : d ∈ D) (hκd : ∀ c, κ c * d = d * κ c)
    (hcomm : ∀ x ∈ Subgroup.centralizer ({d} : Set G),
      ∀ y ∈ Subgroup.centralizer ({d} : Set G), x * y * x⁻¹ * y⁻¹ ∈ κ.range) :
    D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D (Subgroup.centralizer ({d} : Set G))) : Subgroup G) : Set G) := by
  set Cd := Subgroup.centralizer ({d} : Set G) with hCd
  set Cl := conjClosure D Cd with hCl
  set Q := inSubgroup (CFSG.pCore 2) Cl with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map Cl.subtype
  have hDcomm : ∀ y ∈ D, ∀ w ∈ D, y * w = w * y := fun y hy w hw =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨y, hy⟩ ⟨w, hw⟩)
  have hDCd : D ≤ Cd := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hDcomm y hy d hdD)
  have hQCd : Q ≤ Cd := (Subgroup.map_subtype_le _).trans (conjClosure_le hDCd)
  have hCdQ : Cd ≤ Subgroup.normalizer (Q : Set G) := centralizer_le_normalizer_pCore
  have hκCd : ∀ c, κ c ∈ Cd := fun c =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hκd c)
  have hn : ∀ g ∈ Cd, ∀ c, g * κ c * g⁻¹ ∈ κ.range := by
    intro g hg c
    obtain ⟨c', hc'⟩ := hcomm g hg (κ c) (hκCd c)
    refine ⟨c' * c, ?_⟩
    rw [map_mul, hc']
    group
  have hcen : ∀ w ∈ Q, ∀ c, w * κ c = κ c * w := fun w hw =>
    commute_of_mem_two hF4 hinj hκCd hQ2 hCdQ hw (hn w (hQCd hw))
      (fun c => by simpa using hn w⁻¹ (Cd.inv_mem (hQCd hw)) c)
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hyCd := hDCd hy
  have hwQ : q * y * q⁻¹ * y⁻¹ ∈ Q := by
    have h1 : y * q⁻¹ * y⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hCdQ hyCd) _).mp (Q.inv_mem hq)
    have e : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq h1
  obtain ⟨c, hc⟩ := hcomm q (hQCd hq) y hyCd
  have hcZ : c ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro c'
    apply hinj
    rw [map_mul, map_mul, hc]
    exact (hcen _ hwQ c').symm
  rcases Item211Lie2Proof.eq_one_or_eq_neg_one_of_mem_center hcZ with h1 | h1
  · rw [h1, map_one] at hc
    calc q * y = q * y * q⁻¹ * y⁻¹ * (y * q) := by group
      _ = y * q := by rw [← hc, one_mul]
  · exfalso
    obtain ⟨c'', hc''⟩ := hn y hyCd (-1)
    have hc''2 : c'' ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hc'', conj_pow, sq, ← map_mul, neg_one_mul_neg_one_sl2, map_one, mul_one,
        mul_inv_cancel]
    have hyc : y * κ (-1) * y⁻¹ = κ (-1) := by
      rcases sl2_eq_one_or_neg_one_of_sq h2 hc''2 with h | h
      · exfalso
        apply neg_one_ne_one_sl2 h2
        apply hinj
        have e : κ (-1) = y⁻¹ * (y * κ (-1) * y⁻¹) * y := by group
        rw [e, ← hc'', h, map_one]
        group
      · rw [← hc'', h]
    have hqy : q * y * q⁻¹ = κ (-1) * y := by
      rw [← h1, hc]
      group
    have hy3 : y ^ 3 = 1 := hDe.2 y hy
    have hcube : (κ (-1) * y) ^ 3 = κ (-1) := by
      have hcm : Commute (κ (-1)) y := by
        show κ (-1) * y = y * κ (-1)
        calc κ (-1) * y = y * κ (-1) * y⁻¹ * y := by rw [hyc]
          _ = y * κ (-1) := by group
      rw [hcm.mul_pow, hy3, mul_one, ← map_pow, neg_one_pow_three]
    have h3 : (q * y * q⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3, mul_one, mul_inv_cancel]
    rw [hqy, hcube] at h3
    exact neg_one_ne_one_sl2 h2 (hinj (h3.trans (map_one κ).symm))

theorem plus_bot_of_quasisimple [Finite G] {D : Subgroup G} (hDe : IsElemAbelian 3 D) {d : G}
    (hdD : d ∈ D) (hqs : CFSG.IsQuasisimple (Subgroup.centralizer ({d} : Set G))) :
    D ≤ Subgroup.centralizer ((inSubgroup (CFSG.pCore 2)
      (conjClosure D (Subgroup.centralizer ({d} : Set G))) : Subgroup G) : Set G) := by
  set Cd := Subgroup.centralizer ({d} : Set G) with hCd
  set Cl := conjClosure D Cd with hCl
  set Q := inSubgroup (CFSG.pCore 2) Cl with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map Cl.subtype
  have hDcomm : ∀ y ∈ D, ∀ w ∈ D, y * w = w * y := fun y hy w hw =>
    congrArg Subtype.val (hDe.1.is_comm.comm ⟨y, hy⟩ ⟨w, hw⟩)
  have hDCd : D ≤ Cd := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hDcomm y hy d hdD)
  have hQCd : Q ≤ Cd := (Subgroup.map_subtype_le _).trans (conjClosure_le hDCd)
  have hnorm : (Q.subgroupOf Cd).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQCd).mpr centralizer_le_normalizer_pCore
  have hQ2' : IsPGroup 2 (Q.subgroupOf Cd) := by
    intro g
    obtain ⟨k, hk⟩ := hQ2 ⟨g, g.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by
      simpa using congrArg Subtype.val hk))⟩
  have hle := le_center_of_normal_isPGroup hqs hnorm hQ2'
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hqZ := hle (show (⟨q, hQCd hq⟩ : Cd) ∈ Q.subgroupOf Cd from hq)
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hqZ ⟨y, hDCd hy⟩)).symm

end Bot

end Item211Res5Proof

end CFSG.RankThree.PartTwo.Sec21
