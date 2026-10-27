module

public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.Walter.W67.W1Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.F134

open CFSG.Quasithin.P134
open scoped Pointwise

theorem exists_pow_lt_three {G : Type*} [Group G] {x v : G} (hx : orderOf x = 3)
    (hv : v ∈ Subgroup.zpowers x) : ∃ a < 3, x ^ a = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  refine ⟨(k % 3).toNat, by omega, ?_⟩
  have h := zpow_mod_orderOf x k
  rw [hx] at h
  rw [← zpow_natCast, Int.toNat_of_nonneg h0, ← h]
  norm_num

theorem prime_not_dvd_nine_mul_two_pow {p k : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    ¬ p ∣ 9 * 2 ^ k := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h9 | h2'
  · have h9' : p ∣ 3 ^ 2 := by norm_num; exact h9
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h9'))
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2'))

theorem E9Config.exists_model_conj {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    (hcfg : E9Config L P T) {X : Type*} [Group X] {G T₀ : Subgroup X} {φ₀ : ↥L →* X}
    (hφ₀ : Function.Injective φ₀) (hφ₀G : ∀ x, φ₀ x ∈ G) (hφ₀s : ∀ y ∈ G, ∃ x, φ₀ x = y)
    (hT₀G : T₀ ≤ G) (hT₀ : IsPGroup 2 T₀) :
    ∃ φ : ↥L →* X, Function.Injective φ ∧ (∀ x, φ x ∈ G) ∧ (∀ y ∈ G, ∃ x, φ x = y) ∧
      T₀ ≤ ((T ⊓ L).subgroupOf L).map φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := E9Config.isSylowTwoOf_inf hcfg
  obtain ⟨TL, hTLdef⟩ : ∃ R : Subgroup ↥L, R = T₀.comap φ₀ := ⟨_, rfl⟩
  have hTLmap : TL.map φ₀ = T₀ := by
    rw [hTLdef]
    refine le_antisymm (Subgroup.map_comap_le _ _) fun y hy => ?_
    obtain ⟨x, rfl⟩ := hφ₀s y (hT₀G hy)
    exact ⟨x, hy, rfl⟩
  have hTLp : IsPGroup 2 TL :=
    hT₀.of_equiv ((TL.equivMapOfInjective _ hφ₀).trans (MulEquiv.subgroupCongr hTLmap)).symm
  have hUp : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  obtain ⟨Q, hQ⟩ := hTLp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥L) (hUp.toSylow hS.2.2) Q
  have hQU : ∀ x ∈ (Q : Subgroup ↥L), (MulAut.conj g)⁻¹ x ∈ (T ⊓ L).subgroupOf L := by
    intro x hx
    have hx' : x ∈ ((g • hUp.toSylow hS.2.2 : Sylow 2 ↥L) : Subgroup ↥L) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
    exact hx'
  have hback : ∀ x : ↥L, (φ₀.comp (MulAut.conj g).toMonoidHom) ((MulAut.conj g)⁻¹ x) = φ₀ x := by
    intro x
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MulAut.mul_apply, mul_inv_cancel,
      MulAut.one_apply]
  refine ⟨φ₀.comp (MulAut.conj g).toMonoidHom, hφ₀.comp (MulAut.conj g).injective,
    fun x => hφ₀G _, fun y hy => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hφ₀s y hy
    exact ⟨_, hback x⟩
  · intro y hy
    rw [← hTLmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨_, hQU x (hQ hx), hback x⟩

theorem E9Config.false_of_inv {A : Type} [Group A] {L P T : Subgroup A} (hcfg : E9Config L P T)
    (Inv : A → Prop)
    (hinv : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ y ∈ P, Inv y → Inv (t * y * t⁻¹))
    {x₀ : A} (hx₀P : x₀ ∈ P) (hx₀ : x₀ ≠ 1) (hx₀i : Inv x₀)
    (hmax : ∀ y ∈ P, Inv y → y ∈ Subgroup.zpowers x₀) : False := by
  have hconj : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      t * x₀ * t⁻¹ ∈ Subgroup.zpowers x₀ := fun t ht =>
    hmax _ ((Subgroup.mem_normalizer_iff.mp ht.2 _).1 hx₀P) (hinv t ht x₀ hx₀P hx₀i)
  have hinvT : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      t⁻¹ ∈ T ⊓ Subgroup.normalizer (P : Set A) :=
    fun t ht => (T ⊓ Subgroup.normalizer (P : Set A)).inv_mem ht
  have hpow : ∀ s ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ n ∈ Subgroup.zpowers x₀,
      s * n * s⁻¹ ∈ Subgroup.zpowers x₀ := by
    intro s hs n hn
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have e1 : s * x₀ ^ m * s⁻¹ = (s * x₀ * s⁻¹) ^ m := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [e1]
    exact Subgroup.zpow_mem _ (hconj s hs) m
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤
      Subgroup.normalizer (Subgroup.zpowers x₀ : Set A) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hpow t ht n, fun hn => ?_⟩
    have := hpow t⁻¹ (hinvT t ht) _ hn
    rwa [show t⁻¹ * (t * n * t⁻¹) * t⁻¹⁻¹ = n by group] at this
  rcases hcfg.irred _ (Subgroup.zpowers_le.mpr hx₀P) hnorm with h | h
  · have := Subgroup.mem_zpowers x₀
    rw [h, Subgroup.mem_bot] at this
    exact hx₀ this
  · have hc := Nat.card_zpowers x₀
    rw [h, hcfg.card] at hc
    have := orderOf_dvd_of_pow_eq_one (hcfg.exp x₀ hx₀P)
    rw [← hc] at this
    norm_num at this

theorem card_sup_zpowers_of_comm {X : Type*} [Group X] {x₁ x₂ : X} (ho1 : orderOf x₁ = 3)
    (ho2 : orderOf x₂ = 3) (hc : x₁ * x₂ = x₂ * x₁)
    (hd : ∀ a < 3, ∀ b < 3, 0 < b → x₂ ^ b ≠ x₁ ^ a) :
    Nat.card (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ : Subgroup X) = 9 ∧
      ∀ z ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, ∃ a < 3, ∃ b < 3, z = x₁ ^ a * x₂ ^ b := by
  have hnorm : Subgroup.zpowers x₂ ≤ Subgroup.normalizer (Subgroup.zpowers x₁ : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨a, -, rfl⟩ := exists_pow_lt_three ho1 hh
    exact (Commute.pow_left hc a).eq
  have hdisj : Disjoint (Subgroup.zpowers x₁) (Subgroup.zpowers x₂) := by
    rw [Subgroup.disjoint_def]
    intro v h1 h2
    obtain ⟨a, ha, rfl⟩ := exists_pow_lt_three ho1 h1
    obtain ⟨b, hb, hb'⟩ := exists_pow_lt_three ho2 h2
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rw [pow_zero] at hb'
      exact hb'.symm
    · exact absurd hb' (hd a ha b hb hb0)
  refine ⟨?_, fun z hz => ?_⟩
  · rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj,
      Nat.card_zpowers, Nat.card_zpowers, ho1, ho2]
  · obtain ⟨u, hu, v, hv, rfl⟩ := (CFSG.Walter.W67.mem_sup_iff_of_le_normalizer hnorm).mp hz
    obtain ⟨a, ha, rfl⟩ := exists_pow_lt_three ho1 hu
    obtain ⟨b, hb, rfl⟩ := exists_pow_lt_three ho2 hv
    exact ⟨a, ha, b, hb, rfl⟩

theorem isPGroup_index_of_card_nine {X : Type*} [Group X] {K R : Subgroup X} {m : ℕ}
    (hRK : R ≤ K) (hR : Nat.card R = 9) (hK : Nat.card K = 9 * m) (hm : ¬ 3 ∣ m) :
    IsPGroup 3 (R.subgroupOf K) ∧ ¬ 3 ∣ (R.subgroupOf K).index := by
  have hc : Nat.card (R.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, hR]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨IsPGroup.of_card (n := 2) (by rw [hc]; norm_num), ?_⟩
  have h := (R.subgroupOf K).card_mul_index
  rw [hc, hK] at h
  have him : (R.subgroupOf K).index = m := by omega
  rwa [him]

theorem exists_conj_of_card_nine {X : Type*} [Group X] {K P₀ Q : Subgroup X} [Finite K] {m : ℕ}
    (hP₀K : P₀ ≤ K) (hQK : Q ≤ K) (hP₀ : Nat.card P₀ = 9) (hQ : Nat.card Q = 9)
    (hK : Nat.card K = 9 * m) (hm : ¬ 3 ∣ m) :
    ∃ g ∈ K, (∀ y ∈ P₀, g * y * g⁻¹ ∈ Q) ∧ ∀ y ∈ Q, g⁻¹ * y * g ∈ P₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hQp, hQi⟩ := isPGroup_index_of_card_nine hQK hQ hK hm
  obtain ⟨hPp, hPi⟩ := isPGroup_index_of_card_nine hP₀K hP₀ hK hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥K) (hPp.toSylow hPi) (hQp.toSylow hQi)
  have hmemQ : ∀ x : K, x ∈ Q.subgroupOf K ↔ (MulAut.conj g)⁻¹ x ∈ P₀.subgroupOf K := by
    intro x
    have h : x ∈ ((g • hPp.toSylow hPi : Sylow 3 K) : Subgroup K) ↔ x ∈ Q.subgroupOf K := by
      rw [hg]
      rfl
    rw [← h, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine ⟨g, g.2, fun y hy => ?_, fun y hy => ?_⟩
  · exact (hmemQ (MulAut.conj g ⟨y, hP₀K hy⟩)).mpr (by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      exact hy)
  · have h := (hmemQ ⟨y, hQK hy⟩).mp hy
    rw [MulAut.conj_inv_apply] at h
    exact h

theorem exists_inv_of_conj {X : Type*} [Group X] {P₀ Q : Subgroup X} (f : X → Prop) {g : X}
    (hg : ∀ y ∈ P₀, g * y * g⁻¹ ∈ Q) (hg' : ∀ y ∈ Q, g⁻¹ * y * g ∈ P₀)
    (hfg : ∀ z, f z → f (g * z * g⁻¹)) (hfg' : ∀ z, f z → f (g⁻¹ * z * g))
    {x₁ : X} (hx₁ : x₁ ∈ P₀) (hx₁o : orderOf x₁ = 3) (hx₁f : f x₁)
    (hmax : ∀ z ∈ P₀, f z → z ∈ Subgroup.zpowers x₁) :
    ∃ y₀ ∈ Q, orderOf y₀ = 3 ∧ f y₀ ∧ ∀ y ∈ Q, f y → y ∈ Subgroup.zpowers y₀ := by
  refine ⟨g * x₁ * g⁻¹, hg x₁ hx₁, ?_, hfg x₁ hx₁f, fun y hy hfy => ?_⟩
  · rw [← hx₁o]
    exact MulEquiv.orderOf_eq (MulAut.conj g) x₁
  · have hz := hmax _ (hg' y hy) (hfg' y hfy)
    have hm : (MulAut.conj g).toMonoidHom (g⁻¹ * y * g) ∈
        (Subgroup.zpowers x₁).map (MulAut.conj g).toMonoidHom := Subgroup.mem_map_of_mem _ hz
    rw [MonoidHom.map_zpowers] at hm
    have e : (MulAut.conj g).toMonoidHom (g⁻¹ * y * g) = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e] at hm
    simpa using hm

theorem exists_inv_of_sylow {X : Type*} [Group X] {K P₀ Q : Subgroup X} [Finite K] {m : ℕ}
    (f : X → Prop) (hf : ∀ k ∈ K, ∀ z, f z → f (k * z * k⁻¹)) (hP₀K : P₀ ≤ K) (hQK : Q ≤ K)
    (hP₀ : Nat.card P₀ = 9) (hQ : Nat.card Q = 9) (hK : Nat.card K = 9 * m) (hm : ¬ 3 ∣ m)
    {x₁ : X} (hx₁ : x₁ ∈ P₀) (hx₁o : orderOf x₁ = 3) (hx₁f : f x₁)
    (hmax : ∀ z ∈ P₀, f z → z ∈ Subgroup.zpowers x₁) :
    ∃ y₀ ∈ Q, orderOf y₀ = 3 ∧ f y₀ ∧ ∀ y ∈ Q, f y → y ∈ Subgroup.zpowers y₀ := by
  obtain ⟨g, hgK, hg, hg'⟩ := exists_conj_of_card_nine hP₀K hQK hP₀ hQ hK hm
  refine exists_inv_of_conj f hg hg' (hf g hgK) (fun z hz => ?_) hx₁ hx₁o hx₁f hmax
  have := hf g⁻¹ (K.inv_mem hgK) z hz
  rwa [inv_inv] at this

theorem exists_inv_of_sylow_mul {X : Type*} [Group X] {K T₀ P₀ Q : Subgroup X} [Finite K]
    (f : X → Prop) (hf : ∀ t ∈ T₀, ∀ z, f z → f (t * z * t⁻¹)) (hT₀K : T₀ ≤ K) (hP₀K : P₀ ≤ K)
    (hQK : Q ≤ K) (hP₀ : Nat.card P₀ = 9) (hQ : Nat.card Q = 9)
    (hK : Nat.card K = 9 * Nat.card T₀) (hT₀3 : ¬ 3 ∣ Nat.card T₀)
    {x₁ : X} (hx₁ : x₁ ∈ P₀) (hx₁o : orderOf x₁ = 3) (hx₁f : f x₁)
    (hmax : ∀ z ∈ P₀, f z → z ∈ Subgroup.zpowers x₁) :
    ∃ y₀ ∈ Q, orderOf y₀ = 3 ∧ f y₀ ∧ ∀ y ∈ Q, f y → y ∈ Subgroup.zpowers y₀ := by
  obtain ⟨g, hgK, hg, hg'⟩ := exists_conj_of_card_nine hP₀K hQK hP₀ hQ hK hT₀3
  have : Finite T₀ := Finite.of_injective _ (Subgroup.inclusion_injective hT₀K)
  have : Finite P₀ := Finite.of_injective _ (Subgroup.inclusion_injective hP₀K)
  have hdisj : ∀ x ∈ T₀, x ∈ P₀ → x = 1 := by
    intro x hxT hxP
    have h1 : orderOf x ∣ Nat.card T₀ := Subgroup.orderOf_dvd_natCard T₀ hxT
    have h2 : orderOf x ∣ 9 := hP₀ ▸ Subgroup.orderOf_dvd_natCard P₀ hxP
    have h3 : orderOf x = 1 := by
      have hcop : Nat.Coprime (Nat.card T₀) 9 := by
        have : Nat.Coprime (Nat.card T₀) 3 :=
          (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT₀3))
        exact Nat.Coprime.pow_right 2 this
      exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact orderOf_eq_one_iff.mp h3
  let μ : T₀ × P₀ → K := fun q => ⟨q.1 * q.2, K.mul_mem (hT₀K q.1.2) (hP₀K q.2.2)⟩
  have hμ : Function.Injective μ := by
    rintro ⟨t, p⟩ ⟨t', p'⟩ h
    have h' : (t : X) * p = t' * p' := congrArg Subtype.val h
    have e : (t' : X)⁻¹ * t = p' * (p : X)⁻¹ := by
      calc (t' : X)⁻¹ * t = (t' : X)⁻¹ * (t * p) * (p : X)⁻¹ := by group
        _ = (t' : X)⁻¹ * (t' * p') * (p : X)⁻¹ := by rw [h']
        _ = p' * (p : X)⁻¹ := by group
    have h1 := hdisj _ (T₀.mul_mem (T₀.inv_mem t'.2) t.2) (e ▸ P₀.mul_mem p'.2 (P₀.inv_mem p.2))
    have htt : (t : X) = t' := by
      calc (t : X) = t' * ((t' : X)⁻¹ * t) := by group
        _ = t' := by rw [h1, mul_one]
    have hpp : (p : X) = p' := by
      rw [htt] at h'
      exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext htt) (Subtype.ext hpp)
  have hμb : Function.Bijective μ :=
    (Nat.bijective_iff_injective_and_card μ).mpr ⟨hμ, by rw [Nat.card_prod, hP₀, hK, mul_comm]⟩
  obtain ⟨⟨t, p⟩, htp⟩ := hμb.2 ⟨g, hgK⟩
  have hgtp : g = (t : X) * p := (congrArg Subtype.val htp).symm
  have ht : ∀ y ∈ P₀, (t : X) * y * (t : X)⁻¹ ∈ Q := by
    intro y hy
    have h := hg ((p : X)⁻¹ * y * p) (P₀.mul_mem (P₀.mul_mem (P₀.inv_mem p.2) hy) p.2)
    rwa [hgtp, show (t : X) * p * ((p : X)⁻¹ * y * p) * ((t : X) * p)⁻¹ =
      t * y * (t : X)⁻¹ by group] at h
  have ht' : ∀ y ∈ Q, (t : X)⁻¹ * y * t ∈ P₀ := by
    intro y hy
    have h := P₀.mul_mem (P₀.mul_mem p.2 (hg' y hy)) (P₀.inv_mem p.2)
    rwa [hgtp, show (p : X) * (((t : X) * p)⁻¹ * y * ((t : X) * p)) * (p : X)⁻¹ =
      (t : X)⁻¹ * y * t by group] at h
  refine exists_inv_of_conj f ht ht' (hf t t.2) (fun z hz => ?_) hx₁ hx₁o hx₁f hmax
  have := hf (t : X)⁻¹ (T₀.inv_mem t.2) z hz
  rwa [inv_inv] at this

theorem mul_conj_step {G : Type*} [Group G] {a u g c v : G} (hu : u * g = g * c)
    (ha : a * g = g * v) : a * u * g = g * (v * c) := by
  rw [mul_assoc, hu, ← mul_assoc, ha, mul_assoc]

theorem mul_rearrange {G : Type*} [Group G] {t d a b g v x₁ d' x₂ : G} (hb : b * g = g * v)
    (hd : d * a * g = x₁ * d' * x₂) : t * d * (a * b) * g = t * x₁ * d' * (x₂ * v) := by
  have e1 : t * d * (a * b) * g = t * (d * a * (b * g)) := by simp only [mul_assoc]
  have e2 : t * x₁ * d' * (x₂ * v) = t * (x₁ * d' * x₂ * v) := by simp only [mul_assoc]
  rw [e1, e2, hb, ← mul_assoc (d * a) g v, hd]

theorem card_le_of_cover {G : Type*} [Group G] {H T : Subgroup G} [Finite T] {n : ℕ}
    (c : Fin n → G) (hcov : ∀ h ∈ H, ∃ s : Fin n, ∃ t ∈ T, h = c s * t) :
    Nat.card H ≤ n * Nat.card T := by
  choose s t ht hst using fun h : H => hcov h h.2
  have hinj : Function.Injective fun h : H => ((s h, ⟨t h, ht h⟩) : Fin n × T) := by
    intro h h' e
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at e
    exact Subtype.ext ((hst h).trans (e.1 ▸ e.2 ▸ (hst h').symm))
  calc Nat.card H ≤ Nat.card (Fin n × T) := Nat.card_le_card_of_injective _ hinj
    _ = n * Nat.card T := by rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

end CFSG.Quasithin.F134
