module

public import CFSG.Quasithin.H13.L32AL2Ie
public import CFSG.Quasithin.H13.L32AL2If

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.QuasithinUnique

section General

variable {X : Type*} [Group X] {K : Subgroup X}

theorem GoodK.inf_eq_bot (hK : GoodK K) {C : Subgroup X}
    (hC : C ≤ Subgroup.centralizer (K : Set X)) : K ⊓ C = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun a ha => hK.center a ha.1 fun b hb => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hC ha.2) b hb).symm

theorem isPGroup_zpowers_of_pow_three {a : X} (ha : a ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers a) := by
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  change (a ^ n) ^ 3 ^ 1 = 1
  rw [pow_one, zpow_pow_three_eq_one ha n]

theorem isPGroup_sup_zpowers {a b : X} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a * b = b * a) :
    IsPGroup 3 ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_three ha)
    (isPGroup_zpowers_of_pow_three hb) (Subgroup.zpowers_le.mpr ?_)
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ((Commute.zpow_left (show Commute b a from hab.symm) n)).eq

theorem three_of_not_dvd [Finite X] {Y : Subgroup X} (hY : ¬ 9 ∣ Nat.card Y) {a a' : X}
    (ha : a ∈ Y) (ha' : a' ∈ Y) (ha3 : a ^ 3 = 1) (ha'3 : a' ^ 3 = 1) (hc : a * a' = a' * a) :
    a = 1 ∨ a' ∈ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  right
  set H := Subgroup.zpowers a ⊔ Subgroup.zpowers a' with hH
  have hHY : H ≤ Y := sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr ha')
  obtain ⟨k, hk⟩ := (isPGroup_sup_zpowers ha3 ha'3 hc).exists_card_eq
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hk1 : k ≤ 1 := by
    by_contra h2
    apply hY
    have h9 : 3 ^ 2 ∣ Nat.card H := hk ▸ Nat.pow_dvd_pow 3 (by omega)
    exact h9.trans (Subgroup.card_dvd_of_le hHY)
  have h3 : Nat.card H ≤ 3 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  have heq : Subgroup.zpowers a = H :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, hao]; exact h3)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a')

theorem GoodK.three [Finite X] (hK : GoodK K) :
    ∀ a ∈ K, ∀ a' ∈ K, a ^ 3 = 1 → a' ^ 3 = 1 → a * a' = a' * a →
      a = 1 ∨ a' ∈ Subgroup.zpowers a := fun _ ha _ ha' ha3 ha'3 hc =>
  three_of_not_dvd hK.card ha ha' ha3 ha'3 hc

theorem GoodK.mem_sup (hK : GoodK K) {Y : Subgroup X} (hKY : K ≤ Y) {g : X} (hgY : g ∈ Y)
    (hgN : g ∈ Subgroup.normalizer (K : Set X)) (hg3 : g ^ 3 = 1) :
    g ∈ K ⊔ (Y ⊓ Subgroup.centralizer (K : Set X)) := by
  obtain ⟨k, hk, hkg⟩ := hK.inner g hgN hg3
  have hc : k⁻¹ * g ∈ Y ⊓ Subgroup.centralizer (K : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hKY hk)) hgY,
      Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
    have h1 := hkg n hn
    calc n * (k⁻¹ * g) = k⁻¹ * (k * n * k⁻¹) * g := by group
      _ = k⁻¹ * (g * n * g⁻¹) * g := by rw [h1]
      _ = k⁻¹ * g * n := by group
  have e : g = k * (k⁻¹ * g) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hc)

end General

section A131

theorem mem_zpowers_of_sq {G : Type*} [Group G] {t x : G} (ht2 : t ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h : t ^ n = t ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul]
    have h2 : t ^ (2 : ℤ) = 1 := by exact_mod_cast ht2
    rw [h2, one_zpow, mul_one]
  rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hr | hr
  · left
    rw [h, hr, zpow_zero]
  · right
    rw [h, hr, zpow_one]

theorem pow_three_of_mem_sup {G : Type*} [Group G] {a b : G} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : a * b = b * a) {e : G} (he : e ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    e ^ 3 = 1 := by
  have hN : Subgroup.zpowers b ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => ?_))
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (show Commute a b from hab) n)).eq
  obtain ⟨x, hx, y, hy, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hN).1 he
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [((Commute.zpow_zpow (show Commute a b from hab) i j)).mul_pow, zpow_pow_three_eq_one ha,
    zpow_pow_three_eq_one hb, one_mul]

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

theorem GoodK.three_centralizer (hK : GoodK K) (hKX : K ≤ X) (hX : IsQuotientOfSQTKTC ↥X)
    {b b' : MulAut V} (hbX : b ∈ X) (hb'X : b' ∈ X) (hbC : b ∈ Subgroup.centralizer (K : Set _))
    (hb'C : b' ∈ Subgroup.centralizer (K : Set _)) (hb3 : b ^ 3 = 1) (hb'3 : b' ^ 3 = 1)
    (hc : b * b' = b' * b) : b = 1 ∨ b' ∈ Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, htK, r, hrK, ht2, hr3, hr1, htr⟩ := hK.inv
  have hrb : r * b = b * r := (Subgroup.mem_centralizer_iff.mp hbC r hrK)
  have hrb' : r * b' = b' * r := (Subgroup.mem_centralizer_iff.mp hb'C r hrK)
  have htb : t * b = b * t := (Subgroup.mem_centralizer_iff.mp hbC t htK)
  have htb' : t * b' = b' * t := (Subgroup.mem_centralizer_iff.mp hb'C t htK)
  have hrr : r ≠ r⁻¹ := by
    intro h
    have h2 : r * r = 1 := by
      calc r * r = r * r⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel r
    apply hr1
    calc r = r ^ 3 * (r * r)⁻¹ := by rw [pow_three]; group
      _ = 1 := by rw [hr3, h2]; group
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hrr
    rw [← htr]
    group
  set E := Subgroup.zpowers b ⊔ Subgroup.zpowers b' with hE
  set P := Subgroup.zpowers r ⊔ E with hP
  have hEp : IsPGroup 3 E := isPGroup_sup_zpowers hb3 hb'3 hc
  have hcenr : E ≤ Subgroup.centralizer ({r} : Set (MulAut V)) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hrb.symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hrb'.symm))
  have hrE : Subgroup.zpowers r ≤ Subgroup.normalizer (E : Set (MulAut V)) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hcenr he))
  have hPp : IsPGroup 3 P :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_three hr3) hEp hrE
  have hPX : P ≤ X := sup_le (Subgroup.zpowers_le.mpr (hKX hrK))
    (sup_le (Subgroup.zpowers_le.mpr hbX) (Subgroup.zpowers_le.mpr hb'X))
  have hcz : ∀ {w : MulAut V}, t * w = w * t →
      t ∈ Subgroup.normalizer ((Subgroup.zpowers w : Subgroup _) : Set (MulAut V)) :=
    fun hw => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun g hg => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        exact ((Commute.zpow_left (show Commute _ t from hw.symm) n)).eq)
  have h1 : t ∈ Subgroup.normalizer ((Subgroup.zpowers r : Subgroup _) : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (t * r * t⁻¹) = _
    rw [htr, Subgroup.zpowers_inv]
  have htN : t ∈ Subgroup.normalizer (P : Set (MulAut V)) :=
    mem_normalizer_sup' h1 (mem_normalizer_sup' (hcz htb) (hcz htb'))
  have hAn : ∀ a ∈ Subgroup.zpowers t, ∀ y ∈ P, a * y * a⁻¹ ∈ P := by
    intro a ha y hy
    rcases mem_zpowers_of_sq ht2 ha with rfl | rfl
    · simpa using hy
    · exact (Subgroup.mem_normalizer_iff.mp htN y).mp hy
  have hfaith : ∀ a ∈ Subgroup.zpowers t, (∀ y ∈ P, a * y = y * a) → a = 1 := by
    intro a ha hall
    rcases mem_zpowers_of_sq ht2 ha with h | rfl
    · exact h
    · exfalso
      apply hrr
      have h1 := hall r (Subgroup.mem_sup_left (Subgroup.mem_zpowers r))
      rw [← htr, h1, mul_inv_cancel_right]
  have hA2 : IsElemAbelian2 (Subgroup.zpowers t) := by
    refine ⟨fun a ha c hc' => ?_, fun a ha => ?_⟩
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
      exact ((Commute.refl t).zpow_zpow m k).eq
    · rcases mem_zpowers_of_sq ht2 ha with rfl | rfl
      · exact one_pow 2
      · exact ht2
  have hcyc := isCyclic_inf_centralizer_of_faithful (X := X) (P := P) (A := Subgroup.zpowers t)
    (p := 3) (by norm_num) hPX hPp hA2 (Subgroup.zpowers_le.mpr (hKX htK)) hAn hX hfaith
    (Subgroup.mem_zpowers t) ht1
  have hEle : E ≤ P ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) :=
    le_inf le_sup_right (sup_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr htb.symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr htb'.symm)))
  have hEc : IsCyclic ↥E := Subgroup.isCyclic_of_le hEle
  by_cases hb1 : b = 1
  · exact Or.inl hb1
  right
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using pow_three_of_mem_sup hb3 hb'3 hc g.2)
  have hcardE : Nat.card E ≤ 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have heq : Subgroup.zpowers b = E :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, hbo]; exact hcardE)
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b')

end A131

end CFSG.Quasithin.H13.L32A.L2
