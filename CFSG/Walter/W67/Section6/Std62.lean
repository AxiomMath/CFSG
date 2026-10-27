module

public import CFSG.Walter.W67.Section6.Core62B
public import CFSG.Walter.W67.Section6.Basic
public import CFSG.Walter.W67.Section6.Core61

public section

namespace CFSG.Walter.W67

namespace Sec6

variable {G : Type} [Group G] [Finite G] (s : Std G)

theorem index_ne_two_of_perfect {X : Type*} [Group X] (hX : commutator X = ⊤)
    (H : Subgroup X) : H.index ≠ 2 := by
  intro hidx
  have : H.Normal := Subgroup.normal_of_index_eq_two hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (X ⧸ H) := isCyclic_of_prime_card (p := 2) (by
    rw [← Subgroup.index_eq_card, hidx])
  have hle : commutator X ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro u _ v _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact hcyc.commGroup.mul_comm _ _
  rw [hX, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hidx
  exact absurd hidx (by norm_num)

theorem isConj_J
    {u : G} (hu : orderOf u = 2) : IsConj u s.J :=
  (lemma_2_2 G s.toHyp s.fr fun N _ => index_ne_two_of_perfect s.perfect N).2.2 u s.J hu
    s.orderOf_J

include s in
theorem two_facts {T : Subgroup G} (hT : IsPGroup 2 T) {a b : G} (ha : a ∈ T) (hb : b ∈ T) :
    a * b = b * a ∧ a * a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hT.exists_le_sylow
  have hab : a * b = b * a := by
    have := (s.abelian_sylow P).is_comm.comm ⟨a, hP ha⟩ ⟨b, hP hb⟩
    exact congrArg Subtype.val this
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G s.fr.S P
  refine ⟨hab, ?_⟩
  have haP : a ∈ ((g • s.fr.S : Sylow 2 G) : Subgroup G) := by rw [hg]; exact hP ha
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haP
  have h1 := s.fr.mul_self_of_mem_S haP
  simp only [MulAut.smul_def, MulAut.conj_inv_apply] at h1
  have h2 : a * a = g * ((g⁻¹ * a * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
  rw [h2, h1]
  group

theorem E_inf_JK :
    s.fr.E ⊓ (Subgroup.zpowers s.J ⊔ s.K) = ⊥ := by
  rw [eq_bot_iff]
  intro e he
  obtain ⟨heE, heJK⟩ := Subgroup.mem_inf.mp he
  have hodd : Odd (orderOf e) := (s.fr.odd_card_E).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ heE)
  have heK : e ∈ s.K :=
    mem_of_odd_of_mem_zpowers_sup' s.orderOf_J s.le_centralizer s.J_not_mem_K heJK hodd
  have : e ∈ s.K ⊓ s.fr.E := Subgroup.mem_inf.mpr ⟨heK, heE⟩
  rwa [s.fr.K_inf_E, Subgroup.mem_bot] at this

theorem E_le_normalizer_K : s.fr.E ≤ Subgroup.normalizer (s.K : Set G) :=
  s.fr.E_le_H.trans s.H_le_normalizer

theorem mem_KE {y : G} (hy : y ∈ s.K ⊔ s.fr.E) : ∃ k ∈ s.K, ∃ e ∈ s.fr.E, k * e = y :=
  (mem_sup_iff_of_le_normalizer (E_le_normalizer_K s)).mp hy

theorem eq_one_of_sq_mem_K
    {e : G} (he : e ∈ s.fr.E) (he2 : e * e ∈ s.K) : e = 1 := by
  have h1 : e * e ∈ s.K ⊓ s.fr.E := Subgroup.mem_inf.mpr ⟨he2, s.fr.E.mul_mem he he⟩
  rw [s.fr.K_inf_E, Subgroup.mem_bot] at h1
  have hodd : Odd (orderOf e) := (s.fr.odd_card_E).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ he)
  have hd : orderOf e ∣ Nat.gcd 2 (orderOf e) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)) dvd_rfl
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd), Nat.dvd_one,
    orderOf_eq_one_iff] at hd
  exact hd

theorem no_real
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts) {r : ℕ}
    [Fact r.Prime] (hrσ : r ∈ s.fr.σ) (u x t : G) (hu : orderOf u = 2)
    (hx : x ∈ Subgroup.centralizer ({u} : Set G)) (ht : t ∈ Subgroup.centralizer ({u} : Set G))
    (ht2 : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹) (hxr : IsPGroup r (Subgroup.zpowers x)) :
    x = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_J s hu)
  have hconj : ∀ y ∈ Subgroup.centralizer ({u} : Set G),
      g * y * g⁻¹ ∈ Subgroup.centralizer ({s.J} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← hg]
    calc g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
      _ = g * (u * y) * g⁻¹ := by rw [hy]
      _ = g * u * g⁻¹ * (g * y * g⁻¹) := by group
  have hx' := hconj x hx
  have ht' := hconj t ht
  have hIDP := s.fr.isInternalDirectProduct_H
  have hKE : s.K ⊔ s.fr.E ≤ Subgroup.centralizer ({s.J} : Set G) := sup_le s.K_le_H s.fr.E_le_H
  have hJKE : s.J ∉ s.K ⊔ s.fr.E := by
    intro hJ'
    have h1 := Subgroup.disjoint_def.mp hIDP.2.1 (Subgroup.mem_zpowers s.J) hJ'
    have h2 := s.orderOf_J
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hJC : s.J ∈ Subgroup.centralizer ((s.K ⊔ s.fr.E : Subgroup G) : Set G) :=
    hIDP.2.2 (Subgroup.mem_zpowers s.J)
  have hJN : Subgroup.zpowers s.J ≤ Subgroup.normalizer ((s.K ⊔ s.fr.E : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hJC)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hxr) ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hk
  have hrodd : Odd r := s.fr.odd_card_E.of_dvd_nat ((mem_sigma_iff s).mp hrσ).2
  have hodd : Odd (orderOf (g * x * g⁻¹)) := by rw [orderOf_conj_mul, hk]; exact hrodd.pow
  have hx'H : g * x * g⁻¹ ∈ Subgroup.zpowers s.J ⊔ (s.K ⊔ s.fr.E) := by rw [hIDP.1]; exact hx'
  have hx'KE := mem_of_odd_of_mem_zpowers_sup' s.orderOf_J hKE hJKE hx'H hodd
  have ht'H : g * t * g⁻¹ ∈ (s.K ⊔ s.fr.E) ⊔ Subgroup.zpowers s.J := by
    rw [sup_comm, hIDP.1]; exact ht'
  obtain ⟨k₀, hk₀, j, hj, hk₀j⟩ := (mem_sup_iff_of_le_normalizer hJN).mp ht'H
  have hjc : ∀ y ∈ s.K ⊔ s.fr.E, j * y = y * j := fun y hy => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
    exact (Commute.zpow_left ((Subgroup.mem_centralizer_iff.mp hJC y hy).symm) i).eq
  have hj2 : j * j = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hj
    rw [s.card_zpowers_J] at h1
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one]
    exact h1
  have ht'2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hk₀2 : k₀ * k₀ = 1 := by
    rw [← hk₀j] at ht'2
    calc k₀ * k₀ = k₀ * (k₀ * j) * j⁻¹ := by group
      _ = k₀ * (j * k₀) * j⁻¹ := by rw [hjc k₀ hk₀]
      _ = (k₀ * j) * (k₀ * j) * (j * j)⁻¹ := by group
      _ = 1 := by rw [ht'2, hj2]; group
  obtain ⟨k₁, hk₁, e₁, he₁, rfl⟩ := mem_KE s hk₀
  have he₁1 : e₁ = 1 := by
    refine eq_one_of_sq_mem_K s he₁ ?_
    have e1 : e₁ * e₁ = (k₁ * (e₁ * k₁ * e₁⁻¹))⁻¹ * ((k₁ * e₁) * (k₁ * e₁)) := by group
    rw [e1, hk₀2, mul_one]
    exact s.K.inv_mem (s.K.mul_mem hk₁
      ((Subgroup.mem_normalizer_iff.mp (E_le_normalizer_K s he₁) k₁).mp hk₁))
  rw [he₁1, mul_one] at hk₀j
  obtain ⟨k₂, hk₂, e₂, he₂, hx'eq⟩ := mem_KE s hx'KE
  have hrel : (k₁ * j) * (k₂ * e₂) * (k₁ * j)⁻¹ = (k₂ * e₂)⁻¹ := by
    rw [hk₀j, hx'eq]
    calc g * t * g⁻¹ * (g * x * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * x * t⁻¹) * g⁻¹ := by group
      _ = (g * x * g⁻¹)⁻¹ := by rw [htx]; group
  have hrel' : k₁ * (k₂ * e₂) * k₁⁻¹ = (k₂ * e₂)⁻¹ := by
    have hjke := hjc (k₂ * e₂) (hx'eq ▸ hx'KE)
    calc k₁ * (k₂ * e₂) * k₁⁻¹ = k₁ * ((k₂ * e₂) * j * j⁻¹) * k₁⁻¹ := by group
      _ = k₁ * (j * (k₂ * e₂) * j⁻¹) * k₁⁻¹ := by rw [← hjke]
      _ = (k₁ * j) * (k₂ * e₂) * (k₁ * j)⁻¹ := by group
      _ = (k₂ * e₂)⁻¹ := hrel
  have he₂1 : e₂ = 1 := by
    refine eq_one_of_sq_mem_K s he₂ ?_
    have e2 : e₂ * e₂ = (e₂ * (k₁ * k₂) * e₂⁻¹)⁻¹ * (k₂⁻¹ * k₁) := by
      have : e₂ * (k₁ * k₂) * e₂ = k₂⁻¹ * k₁ := by
        have h3 : (k₂ * e₂) * (k₁ * (k₂ * e₂) * k₁⁻¹) = 1 := by rw [hrel', mul_inv_cancel]
        calc e₂ * (k₁ * k₂) * e₂ = k₂⁻¹ * ((k₂ * e₂) * (k₁ * (k₂ * e₂) * k₁⁻¹)) * k₁ := by group
          _ = k₂⁻¹ * k₁ := by rw [h3]; group
      calc e₂ * e₂ = (e₂ * (k₁ * k₂) * e₂⁻¹)⁻¹ * (e₂ * (k₁ * k₂) * e₂) := by group
        _ = _ := by rw [this]
    rw [e2]
    exact s.K.mul_mem (s.K.inv_mem ((Subgroup.mem_normalizer_iff.mp (E_le_normalizer_K s he₂)
      _).mp (s.K.mul_mem hk₁ hk₂))) (s.K.mul_mem (s.K.inv_mem hk₂) hk₁)
  rw [he₂1, mul_one] at hx'eq
  have hdvd : orderOf x ∣ Nat.card s.K := by
    rw [← orderOf_conj_mul g x, ← hx'eq]
    exact Subgroup.orderOf_dvd_natCard _ hk₂
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk] at hdvd
    exact not_dvd_card_K s h41 h56 hJ hR hrσ ((dvd_pow_self r hk0).trans hdvd)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact hk

theorem mem_L_of_mul_self
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts)
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) {t : G}
    (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1) : t ∈ s.L X := by
  rw [normalizer_eq s hXE hX] at ht
  obtain ⟨ℓ, hℓ, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer (E_le_normalizer_L s hXE hX)).mp ht
  have hLE := L_inf_E s h41 h56 hJ hR hXE hX
  have he2 : e * e ∈ s.L X := by
    have e1 : e * e = (ℓ * (e * ℓ * e⁻¹))⁻¹ * ((ℓ * e) * (ℓ * e)) := by group
    rw [e1, ht2, mul_one]
    exact (s.L X).inv_mem ((s.L X).mul_mem hℓ
      ((Subgroup.mem_normalizer_iff.mp (E_le_normalizer_L s hXE hX he) ℓ).mp hℓ))
  have h1 : e * e ∈ s.L X ⊓ s.fr.E := Subgroup.mem_inf.mpr ⟨he2, s.fr.E.mul_mem he he⟩
  rw [hLE, Subgroup.mem_bot] at h1
  have hodd : Odd (orderOf e) := (s.fr.odd_card_E).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ he)
  have hd : orderOf e ∣ Nat.gcd 2 (orderOf e) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h1)) dvd_rfl
  rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd), Nat.dvd_one,
    orderOf_eq_one_iff] at hd
  rw [hd, mul_one]
  exact hℓ

omit [Finite G] in
theorem pow_mem_sup_zpowers {K₀ : Subgroup G} {g : G}
    (hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (K₀ : Set G)) {m : G}
    (hm : m ∈ Subgroup.zpowers g ⊔ K₀) (n : ℕ) : m ^ n ∈ K₀ ⊔ Subgroup.zpowers (g ^ n) := by
  obtain ⟨e, he, k, hk, rfl⟩ := exists_mul_of_mem_sup hgN hm
  obtain ⟨k', hk', e1⟩ := exists_pow_mul_eq (hgN he) hk n
  rw [e1]
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left hk')
  have e : (g ^ i) ^ n = (g ^ n) ^ i := by
    rw [← zpow_natCast (g ^ i), ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  rw [e]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) i

theorem inf_zpowers_pow {r : ℕ} [Fact r.Prime] {P₀ : Subgroup G} {g : G}
    (hg : Subgroup.zpowers g = s.fr.E)
    (hP₀c : Nat.card P₀ = r ^ (Nat.card s.fr.E).factorization r) :
    P₀ ⊓ Subgroup.zpowers (g ^ Nat.card P₀) = ⊥ := by
  apply inf_eq_bot_of_coprime
  rw [Nat.card_zpowers, orderOf_pow' g (Nat.card_pos.ne'), hP₀c]
  have hog : orderOf g = Nat.card s.fr.E := by rw [← Nat.card_zpowers, hg]
  rw [hog, Nat.gcd_eq_right (Nat.ordProj_dvd _ _)]
  exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Fact.out Nat.card_pos.ne')

theorem inf_M₁
    (h41 : S_prop_4_1) (h56 : S_prop_5_6) (hJ : JFacts) (hR : RFacts) {r : ℕ}
    [Fact r.Prime] {P₀ : Subgroup G} (hP₀E : P₀ ≤ s.fr.E)
    (hP₀c : Nat.card P₀ = r ^ (Nat.card s.fr.E).factorization r) {X : Subgroup G}
    (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) {g : G} (hg : Subgroup.zpowers g = s.fr.E) :
    P₀ ⊓ (s.L X ⊔ Subgroup.zpowers (g ^ Nat.card P₀)) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨haP₀, haM⟩ := Subgroup.mem_inf.mp ha
  have hgE : Subgroup.zpowers (g ^ Nat.card P₀) ≤ s.fr.E :=
    Subgroup.zpowers_le.mpr (hg ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _)
  rw [sup_comm] at haM
  obtain ⟨e, he, ℓ, hℓ, rfl⟩ :=
    exists_mul_of_mem_sup (hgE.trans (E_le_normalizer_L s hXE hX)) haM
  have hℓE : ℓ ∈ s.L X ⊓ s.fr.E := by
    refine Subgroup.mem_inf.mpr ⟨hℓ, ?_⟩
    have e1 : ℓ = e⁻¹ * (e * ℓ) := by group
    rw [e1]
    exact s.fr.E.mul_mem (s.fr.E.inv_mem (hgE he)) (hP₀E haP₀)
  rw [L_inf_E s h41 h56 hJ hR hXE hX, Subgroup.mem_bot] at hℓE
  rw [hℓE, mul_one] at haP₀ ⊢
  have : e ∈ P₀ ⊓ Subgroup.zpowers (g ^ Nat.card P₀) := Subgroup.mem_inf.mpr ⟨haP₀, he⟩
  rwa [inf_zpowers_pow s hg hP₀c, Subgroup.mem_bot] at this

theorem inf_H₃
    {r : ℕ} [Fact r.Prime] {P₀ : Subgroup G} (hP₀E : P₀ ≤ s.fr.E)
    (hP₀c : Nat.card P₀ = r ^ (Nat.card s.fr.E).factorization r) {g : G}
    (hg : Subgroup.zpowers g = s.fr.E) :
    P₀ ⊓ (Subgroup.zpowers s.J ⊔ s.K ⊔ Subgroup.zpowers (g ^ Nat.card P₀)) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  obtain ⟨haP₀, haM⟩ := Subgroup.mem_inf.mp ha
  have hgE : Subgroup.zpowers (g ^ Nat.card P₀) ≤ s.fr.E :=
    Subgroup.zpowers_le.mpr (hg ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _)
  have hEN : s.fr.E ≤ Subgroup.normalizer ((Subgroup.zpowers s.J ⊔ s.K : Subgroup G) : Set G) :=
    fun e he => mem_normalizer_sup (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun j hj => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
        exact (Commute.zpow_left (s.commute_J (s.fr.E_le_H he)).symm i).eq))
      (E_le_normalizer_K s he)
  rw [sup_comm] at haM
  obtain ⟨e, he, k, hk, rfl⟩ := exists_mul_of_mem_sup (hgE.trans hEN) haM
  have hkE : k ∈ s.fr.E ⊓ (Subgroup.zpowers s.J ⊔ s.K) := by
    refine Subgroup.mem_inf.mpr ⟨?_, hk⟩
    have e1 : k = e⁻¹ * (e * k) := by group
    rw [e1]
    exact s.fr.E.mul_mem (s.fr.E.inv_mem (hgE he)) (hP₀E haP₀)
  rw [E_inf_JK s, Subgroup.mem_bot] at hkE
  rw [hkE, mul_one] at haP₀ ⊢
  have : e ∈ P₀ ⊓ Subgroup.zpowers (g ^ Nat.card P₀) := Subgroup.mem_inf.mpr ⟨haP₀, he⟩
  rwa [inf_zpowers_pow s hg hP₀c, Subgroup.mem_bot] at this

theorem pow_mem_H₃
    {g : G} (hg : Subgroup.zpowers g = s.fr.E) (n : ℕ) {x : G}
    (hx : x ∈ Subgroup.centralizer ({s.J} : Set G)) :
    x ^ n ∈ Subgroup.zpowers s.J ⊔ s.K ⊔ Subgroup.zpowers (g ^ n) := by
  have hIDP := s.fr.isInternalDirectProduct_H
  have hEN : s.fr.E ≤ Subgroup.normalizer ((Subgroup.zpowers s.J ⊔ s.K : Subgroup G) : Set G) :=
    fun e he => mem_normalizer_sup (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun j hj => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
        exact (Commute.zpow_left (s.commute_J (s.fr.E_le_H he)).symm i).eq))
      (E_le_normalizer_K s he)
  have hx' : x ∈ Subgroup.zpowers g ⊔ (Subgroup.zpowers s.J ⊔ s.K) := by
    rw [hg, sup_comm, sup_assoc, hIDP.1]
    exact hx
  exact pow_mem_sup_zpowers (hg ▸ hEN) hx' n

end Sec6

end CFSG.Walter.W67
