module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Str
public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped Pointwise

variable {G : Type} [Group G]

private lemma mem_of_two_pow_mem {J' : Subgroup G} :
    ∀ (n : ℕ) (a : G) (m : ℕ), Odd m → a ^ m = 1 → a ^ (2 ^ n) ∈ J' → a ∈ J' := by
  intro n
  induction n with
  | zero => intro a m _ _ h; simpa using h
  | succ n ih =>
    intro a m hm ha h
    have h2 : a ^ 2 ∈ J' := by
      refine ih (a ^ 2) m hm ?_ ?_
      · rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
      · rwa [← pow_mul, ← pow_succ']
    obtain ⟨k, hk⟩ := exists_pow_eq_pow_two_mul ha hm 1
    rw [pow_one, pow_mul] at hk
    rw [hk]
    exact J'.pow_mem h2 k

private lemma mem_J_of_two_power {x : G} {X J' : Subgroup G} (hx : x ^ 3 = 1)
    (hXc : X ≤ Cen x) (hJc : J' ≤ Cen x) (hXodd : Odd (Nat.card X))
    (hXJ : ∀ u ∈ X, ∀ v ∈ J', u * v = v * u) {g : G}
    (hg : ∃ i : ℤ, ∃ u ∈ X, ∃ v ∈ J', g = x ^ i * u * v) {n : ℕ} (hn : g ^ (2 ^ n) = 1) :
    g ∈ J' := by
  obtain ⟨i, u, hu, v, hv, rfl⟩ := hg
  have hxu : Commute x u := (Subgroup.mem_centralizer_singleton_iff.mp (hXc hu)).symm
  have hxv : Commute x v := (Subgroup.mem_centralizer_singleton_iff.mp (hJc hv)).symm
  have huv : Commute u v := hXJ u hu v hv
  have hau : Commute (x ^ i) u := hxu.zpow_left i
  have hav : Commute (x ^ i * u) v := (hxv.zpow_left i).mul_left huv
  set m := 3 * Nat.card X with hm
  have hmodd : Odd m := (by decide : Odd 3).mul hXodd
  have hxm : (x ^ i) ^ m = 1 := by
    have : x ^ m = 1 := by rw [hm, pow_mul, hx, one_pow]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, this, one_zpow]
  have hum : u ^ m = 1 := by
    have : u ^ Nat.card X = 1 := by
      have := pow_card_eq_one' (x := (⟨u, hu⟩ : X))
      exact congrArg Subtype.val this
    rw [hm, mul_comm, pow_mul, this, one_pow]
  have ham : (x ^ i * u) ^ m = 1 := by rw [hau.mul_pow, hxm, hum, one_mul]
  have h1 : (x ^ i * u) ^ (2 ^ n) ∈ J' := by
    have h2 : (x ^ i * u) ^ (2 ^ n) * v ^ (2 ^ n) = 1 := by rw [← hav.mul_pow]; exact hn
    have : (x ^ i * u) ^ (2 ^ n) = (v ^ (2 ^ n))⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [this]
    exact J'.inv_mem (J'.pow_mem hv _)
  exact J'.mul_mem (mem_of_two_pow_mem n _ m hmodd ham h1) hv

private lemma op2_pow {H : Subgroup G} {y : G} (hy : y ∈ Op 2 H) : ∃ n : ℕ, y ^ (2 ^ n) = 1 := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := H) ⟨w, hw⟩
  have h1 : w ^ 2 ^ n = 1 := congrArg Subtype.val hn
  exact ⟨n, by rw [← map_pow, h1, map_one]⟩

private lemma op2_le {H : Subgroup G} {y : G} (hy : y ∈ Op 2 H) : y ∈ H := by
  obtain ⟨w, _, rfl⟩ := Subgroup.mem_map.mp hy
  exact w.2

private lemma op2_conj {H : Subgroup G} {g y : G} (hg : g ∈ H) (hy : y ∈ Op 2 H) :
    g * y * g⁻¹ ∈ Op 2 H := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
  exact Subgroup.mem_map.mpr
    ⟨⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹, (pCore_normal (p := 2) (G := H)).conj_mem w hw ⟨g, hg⟩, rfl⟩

private lemma card_closure_le [Finite G] {b x z : G} (hb : b ^ 3 = 1) (hx : x ^ 3 = 1)
    (hbx : b * x = x * b) (hz : z ∈ Subgroup.zpowers b) :
    Nat.card (Subgroup.closure ({b, x, z} : Set G)) ≤ 9 := by
  have hle : Subgroup.closure ({b, x, z} : Set G) ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers x := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left hz
  have hnorm : Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    have hc : ∀ h ∈ Subgroup.zpowers x, b * h * b⁻¹ = h := by
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right (show Commute b x from hbx) k).mul_inv_cancel
    have hc' : ∀ h ∈ Subgroup.zpowers x, b⁻¹ * h * b = h := by
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right (show Commute b x from hbx) k).inv_mul_cancel
    constructor
    · intro hh; rw [hc h hh]; exact hh
    · intro hh
      have h3 := hc' _ hh
      rw [show b⁻¹ * (b * h * b⁻¹) * b = h by group] at h3
      rw [h3]; exact hh
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hcb : Nat.card (Subgroup.zpowers b) ≤ 3 :=
    (Nat.card_zpowers b ▸ Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb))
  have hcx : Nat.card (Subgroup.zpowers x) ≤ 3 :=
    (Nat.card_zpowers x ▸ Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx))
  have hsurj : Function.Surjective
      (fun p : Subgroup.zpowers b × Subgroup.zpowers x =>
        (⟨p.1.1 * p.2.1, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
          ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers x))) := by
    rintro ⟨s, hs⟩
    have hs' : s ∈ ((Subgroup.zpowers b : Set G) * (Subgroup.zpowers x : Set G)) := by
      rw [← hset]; exact hs
    obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.mp hs'
    exact ⟨(⟨a, ha⟩, ⟨d, hd⟩), rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod] at h1
  calc Nat.card (Subgroup.closure ({b, x, z} : Set G))
      ≤ Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    _ ≤ Nat.card (Subgroup.zpowers b) * Nat.card (Subgroup.zpowers x) := h1
    _ ≤ 3 * 3 := Nat.mul_le_mul hcb hcx

private lemma sec4_facts [Finite G] {b : G} {J B : Subgroup G} {b₁ b₂ : G}
    (h4 : FF79Sec4 b J B b₁ b₂) :
    b ^ 3 = 1 ∧ b₁ ^ 3 = 1 ∧ b₂ ^ 3 = 1 ∧ b * b₁ = b₁ * b ∧ b * b₂ = b₂ * b ∧
      b₁ * b₂ = b₂ * b₁ ∧ b₁ ∉ Subgroup.zpowers b ∧ b₂ ∉ Subgroup.zpowers b := by
  obtain ⟨hEA, hBeq, -⟩ := h4.mono
  have hbB : b ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  have hb₁B : b₁ ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  have hb₂B : b₂ ∈ B := hBeq ▸ Subgroup.subset_closure (by simp)
  haveI : IsMulCommutative B := hEA.1.toIsMulCommutative
  have hcomm : ∀ u v : G, u ∈ B → v ∈ B → u * v = v * u := fun u v hu hv =>
    congrArg Subtype.val (hEA.1.is_comm.comm (⟨u, hu⟩ : B) ⟨v, hv⟩)
  have hcube : ∀ u : G, u ∈ B → u ^ 3 = 1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hEA.1.exponent_dvd_p
    have : (⟨u, hu⟩ : B) ^ 3 = 1 := by
      rw [hk, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
    exact congrArg Subtype.val this
  have h27 : Nat.card B = 27 := by rw [hEA.2]; norm_num
  have hb3 := hcube b hbB
  have hb₁3 := hcube b₁ hb₁B
  have hb₂3 := hcube b₂ hb₂B
  refine ⟨hb3, hb₁3, hb₂3, hcomm _ _ hbB hb₁B, hcomm _ _ hbB hb₂B, hcomm _ _ hb₁B hb₂B, ?_, ?_⟩
  · intro hz
    have := card_closure_le (x := b₂) hb3 hb₂3 (hcomm _ _ hbB hb₂B) hz
    have hs : ({b, b₂, b₁} : Set G) = {b, b₁, b₂} := by rw [Set.pair_comm b₂ b₁]
    rw [hs, ← hBeq, h27] at this
    omega
  · intro hz
    have := card_closure_le (x := b₁) hb3 hb₁3 (hcomm _ _ hbB hb₁B) hz
    rw [← hBeq, h27] at this
    omega

private lemma card_cent_transport {J' : Subgroup G} {K : Type} [Group K] (e : J' ≃* K) (b : G)
    (hb : b ∈ J') :
    Nat.card ↥(Subgroup.centralizer ({e ⟨b, hb⟩} : Set K)) = Nat.card ↥(J' ⊓ Cen b) := by
  set b' : J' := ⟨b, hb⟩
  have h1 : (Subgroup.centralizer ({e b'} : Set K)).map e.symm.toMonoidHom =
      Subgroup.centralizer ({b'} : Set J') := by
    ext g
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.symm_symm]
    constructor
    · intro h
      apply e.injective
      rw [map_mul, map_mul]; exact h
    · intro h
      have := congrArg e h
      rwa [map_mul, map_mul] at this
  have h2 : (Subgroup.centralizer ({b'} : Set J')).map J'.subtype = J' ⊓ Cen b := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.subtype_apply]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, congrArg Subtype.val hc⟩
    · rintro ⟨hg, hc⟩
      exact ⟨⟨g, hg⟩, Subtype.ext hc, rfl⟩
  rw [← h2, Subgroup.card_map_of_injective J'.subtype_injective, ← h1,
    Subgroup.card_map_of_injective e.symm.injective]

private theorem main_aux (hT : FF79KTransvL5) {b x z t : G} (hc : FF79CentL5 x b z)
    (hxo : x ^ 3 = 1) (hb : orderOf b = 3) (hz : orderOf z = 3)
    (hzb : z ∉ Subgroup.zpowers b) (hbz : b * z = z * b) (ht2 : orderOf t = 2)
    (htx : t * x = x * t) (htz : t * z = z * t) (htb : t * b * t⁻¹ = b⁻¹) :
    ∀ y ∈ Op 2 (Cen t) ⊓ Cen x, ∀ y' ∈ Op 2 (Cen t) ⊓ Cen x,
      y * y' * y⁻¹ * y'⁻¹ ∈ Subgroup.zpowers t := by
  obtain ⟨X, J', hXc, hJc, hXodd, ⟨e⟩, hXJ, hdec, hbJ, hzJ, h7⟩ := hc.exists_decomp
  have hxt : t ∈ Cen x := Subgroup.mem_centralizer_singleton_iff.mpr htx
  have htJ : t ∈ J' := by
    refine mem_J_of_two_power hxo hXc hJc hXodd hXJ (hdec t hxt) (n := 1) ?_
    simpa [ht2] using pow_orderOf_eq_one t
  have h2J : ∀ y ∈ Op 2 (Cen t) ⊓ Cen x, y ∈ J' := fun y hy => by
    obtain ⟨n, hn⟩ := op2_pow hy.1
    exact mem_J_of_two_power hxo hXc hJc hXodd hXJ (hdec y hy.2) hn
  set t' : J' := ⟨t, htJ⟩ with ht'
  set b' : J' := ⟨b, hbJ⟩ with hb'
  set z' : J' := ⟨z, hzJ⟩ with hz'
  let R : Subgroup G := Op 2 (Cen t) ⊓ Cen x
  let R' : Subgroup (GL (Fin 5) (ZMod 2)) := (R.subgroupOf J').map e.toMonoidHom
  have hR'mem : ∀ a : J', e a ∈ R' ↔ (a : G) ∈ R := by
    intro a
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  have hord : ∀ a : J', orderOf (e a) = orderOf (a : G) := fun a => by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
  have hcomm : ∀ a c : J', (a : G) * c = c * a → e a * e c = e c * e a := fun a c h => by
    rw [← map_mul, ← map_mul]; exact congrArg e (Subtype.ext h)
  have hcomm' : ∀ a c : J', e a * e c = e c * e a → (a : G) * c = c * a := fun a c h => by
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (e.injective h)
  have hsy : e t' * e b' * (e t')⁻¹ = (e b')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    exact congrArg e (Subtype.ext htb)
  have hzy : e z' ∉ Subgroup.zpowers (e b') := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← map_zpow] at hk
    have := congrArg Subtype.val (e.injective hk)
    exact hzb (Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using this⟩)
  have hR'p : IsPGroup 2 R' := by
    rintro ⟨r, hr⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨n, hn⟩ := op2_pow (Subgroup.mem_subgroupOf.mp ha).1
    refine ⟨n, Subtype.ext ?_⟩
    have : a ^ 2 ^ n = 1 := Subtype.ext hn
    simp only [Subgroup.coe_pow, Subgroup.coe_one, MonoidHom.coe_coe]
    rw [← map_pow, this, map_one]
  have hR'le : R' ≤ Subgroup.centralizer ({e t'} : Set (GL (Fin 5) (ZMod 2))) := by
    intro r hr
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
    have haR : (a : G) ∈ R := Subgroup.mem_subgroupOf.mp ha
    have : (a : G) ∈ Cen t := op2_le haR.1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm t' a (Subgroup.mem_centralizer_singleton_iff.mp this).symm).symm
  have hR'norm : ∀ g ∈ Subgroup.centralizer ({e t'} : Set (GL (Fin 5) (ZMod 2))), ∀ r ∈ R',
      g * r * g⁻¹ ∈ R' := by
    intro g hg r hr
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨g0, rfl⟩ := e.surjective g
    have haR : (a : G) ∈ R := Subgroup.mem_subgroupOf.mp ha
    have hg0 : (g0 : G) ∈ Cen t := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm' g0 t' (Subgroup.mem_centralizer_singleton_iff.mp hg))
    have h1 : (g0 : G) * a * (g0 : G)⁻¹ ∈ R :=
      ⟨op2_conj hg0 haR.1, by
        have hg0x : (g0 : G) ∈ Cen x := hJc g0.2
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg0x haR.2) (Subgroup.inv_mem _ hg0x)⟩
    have := (hR'mem (g0 * a * g0⁻¹)).mpr h1
    simpa using this
  have hcent : 7 ∣ Nat.card ↥(Subgroup.centralizer ({e b'} : Set (GL (Fin 5) (ZMod 2)))) := by
    rw [card_cent_transport e b hbJ]; exact h7
  intro y hy y' hy'
  have key := hT (e t') (e b') (e z') (by rw [hord]; exact ht2) (by rw [hord]; exact hb) hcent
    hsy (by rw [hord]; exact hz)
    (hcomm z' b' hbz.symm) hzy
    (hcomm t' z' htz) R' hR'p hR'le hR'norm
    (e ⟨y, h2J y hy⟩) ((hR'mem _).mpr hy) (e ⟨y', h2J y' hy'⟩) ((hR'mem _).mpr hy')
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp key
  rw [← map_zpow, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hk
  have := congrArg Subtype.val (e.injective hk)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using this⟩

theorem ff79_4_4Bi_of (hstr : FF79_4_3Str) (hT : FF79KTransvL5) : FF79_4_4Bi := by
  intro G _ _ b J B b₁ b₂ h4 t ht x hx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hb3, hb₁3, hb₂3, hbb₁, hbb₂, hb₁b₂, hn₁, hn₂⟩ := sec4_facts h4
  have hS := hstr G b J B b₁ b₂ h4
  have hbo : orderOf b = 3 := h4.hyp.ord
  have hone : ∀ w : G, w ∉ Subgroup.zpowers b → w ≠ 1 := fun w hw h1 =>
    hw (h1 ▸ Subgroup.one_mem _)
  have hcb : t * b * t⁻¹ = b⁻¹ := ht.inv
  rcases hx with rfl | rfl
  · exact main_aux hT hS.cent₁ hb₁3 hbo (orderOf_eq_prime hb₂3 (hone _ hn₂)) hn₂ hbb₂ ht.ord
      ht.comm₁ ht.comm₂ hcb
  · exact main_aux hT hS.cent₂ hb₂3 hbo (orderOf_eq_prime hb₁3 (hone _ hn₁)) hn₁ hbb₁ ht.ord
      ht.comm₂ ht.comm₁ hcb

end CFSG.RankThree.PartTwo.Sec21.FF79
