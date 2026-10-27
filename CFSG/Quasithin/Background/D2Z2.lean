module

public import CFSG.Quasithin.Background.D2Y3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem involution_on_cyclic {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {C : Subgroup G} (hC : IsPGroup p C) (hcyc : IsCyclic C) {t : G} (ht2 : t ^ 2 = 1)
    (hn : ∀ y ∈ C, t * y * t⁻¹ ∈ C) :
    (∀ y ∈ C, t * y * t⁻¹ = y) ∨ (∀ y ∈ C, t * y * t⁻¹ = y⁻¹) := by
  obtain ⟨γ, hγ⟩ := hcyc.exists_generator
  set g : G := (γ : G) with hg
  have hgC : g ∈ C := γ.2
  have hCg : ∀ y ∈ C, ∃ j : ℤ, g ^ j = y := by
    intro y hy
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨y, hy⟩)
    refine ⟨j, ?_⟩
    have := congrArg Subtype.val hj
    simpa [hg] using this
  obtain ⟨m, hm⟩ := hCg (t * g * t⁻¹) (hn g hgC)
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hconj : ∀ j : ℤ, t * g ^ j * t⁻¹ = g ^ (m * j) := by
    intro j
    rw [← conj_zpow, ← hm, ← zpow_mul]
  have hsq : g ^ (m * m) = g := by
    have h1 : t * (t * g * t⁻¹) * t⁻¹ = g := by
      rw [htinv]
      calc t * (t * g * t) * t = (t * t) * g * (t * t) := by group
        _ = g := by rw [← pow_two, ht2]; simp
    calc g ^ (m * m) = t * g ^ m * t⁻¹ := (hconj m).symm
      _ = t * (t * g * t⁻¹) * t⁻¹ := by rw [← hm]
      _ = g := h1
  have hdvd : (orderOf g : ℤ) ∣ m * m - 1 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, hsq, zpow_one, mul_inv_cancel]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hC) γ
  have hk' : orderOf g = p ^ k := by rw [hg, Subgroup.orderOf_coe]; exact hk
  rw [hk'] at hdvd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out)
  have hfac : ((p : ℤ) ^ k) ∣ (m - 1) * (m + 1) := by
    have : m * m - 1 = (m - 1) * (m + 1) := by ring
    rw [← this]
    exact_mod_cast hdvd
  have hp2' : ¬ ((p : ℤ) ∣ 2) := by
    intro h
    have h2 : p ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) h2
    have hp1 := (Fact.out : p.Prime).two_le
    exact hp (by omega)
  by_cases hdiv : (p : ℤ) ∣ m - 1
  · have hndiv : ¬ ((p : ℤ) ∣ m + 1) := by
      intro h
      apply hp2'
      have := dvd_sub h hdiv
      have e : m + 1 - (m - 1) = 2 := by ring
      rwa [e] at this
    have hpk : ((p : ℤ) ^ k) ∣ m - 1 := hpz.pow_dvd_of_dvd_mul_right k hndiv hfac
    have hgm : g ^ m = g := by
      have : g ^ (m - 1) = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one, hk']
        exact_mod_cast hpk
      rw [zpow_sub, zpow_one, mul_inv_eq_one] at this
      exact this
    left
    intro y hy
    obtain ⟨j, rfl⟩ := hCg y hy
    rw [hconj, zpow_mul, hgm]
  · have hpk : ((p : ℤ) ^ k) ∣ m + 1 := hpz.pow_dvd_of_dvd_mul_left k hdiv hfac
    have hgm : g ^ m = g⁻¹ := by
      have : g ^ (m + 1) = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one, hk']
        exact_mod_cast hpk
      rw [zpow_add, zpow_one, mul_eq_one_iff_eq_inv] at this
      exact this
    right
    intro y hy
    obtain ⟨j, rfl⟩ := hCg y hy
    rw [hconj, zpow_mul, hgm, inv_zpow]

theorem generation_by_hyperplanes {A P : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥) (hP : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set (MulAut V))) :
    P ≤ ⨆ (B : Subgroup (MulAut V)) (_ : B ≤ A ∧ Nat.card A = 2 * Nat.card B),
      P ⊓ Subgroup.centralizer (B : Set (MulAut V)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  have hAelem : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hA.1 a a.2 b b.2)⟩⟩
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => Subtype.ext (hA.2 a a.2) }
  let _ : MulDistribMulAction A P := MulDistribMulAction.compHom P (conjAut hAP)
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    exact hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1 this).symm
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := P) hodd
  have hsmul : ∀ (b : A) (x : P), (((b • x : P)) : MulAut V) =
      (b : MulAut V) * x * (b : MulAut V)⁻¹ := fun b x => rfl
  intro y hy
  have hytop : (⟨y, hy⟩ : P) ∈ (⊤ : Subgroup P) := Subgroup.mem_top _
  rw [← hgen] at hytop
  have hmem : y ∈
      (⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B P).map P.subtype :=
    ⟨⟨y, hy⟩, hytop, rfl⟩
  have hle : (⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B P).map P.subtype ≤
      ⨆ (B : Subgroup (MulAut V)) (_ : B ≤ A ∧ Nat.card A = 2 * Nat.card B),
        P ⊓ Subgroup.centralizer (B : Set (MulAut V)) := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun B => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hB => ?_
    rintro _ ⟨x, hx, rfl⟩
    have hB' : B.map A.subtype ≤ A := by
      rintro _ ⟨b, -, rfl⟩
      exact b.2
    have hcard : Nat.card A = 2 * Nat.card (B.map A.subtype) := by
      have := B.card_mul_index
      rw [hB] at this
      rw [Subgroup.card_map_of_injective A.subtype_injective]
      omega
    have hxc : (x : MulAut V) ∈ P ⊓ Subgroup.centralizer
        ((B.map A.subtype : Subgroup (MulAut V)) : Set (MulAut V)) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨b, hb, rfl⟩
      have h1 : b • x = x := hx ⟨b, hb⟩
      have h2 := congrArg (fun z : P => (z : MulAut V)) h1
      simp only [hsmul] at h2
      show (b : MulAut V) * x = x * b
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    exact Subgroup.mem_iSup_of_mem (B.map A.subtype) (Subgroup.mem_iSup_of_mem ⟨hB', hcard⟩ hxc)
  exact hle hmem

omit [Finite V] in
structure KleinData (A : Subgroup (MulAut V)) (a b : MulAut V) : Prop where
  ha : a ∈ A
  hb : b ∈ A
  ha1 : a ≠ 1
  hb1 : b ≠ 1
  hab : a ≠ b
  ha2 : a ^ 2 = 1
  hb2 : b ^ 2 = 1
  comm : a * b = b * a
  mem : ∀ g ∈ A, g = 1 ∨ g = a ∨ g = b ∨ g = a * b

namespace KleinData

variable {A : Subgroup (MulAut V)} {a b : MulAut V}

omit [Finite V] in
theorem mul_self_a (k : KleinData A a b) : a * a = 1 := by rw [← pow_two]; exact k.ha2

omit [Finite V] in
theorem mul_self_b (k : KleinData A a b) : b * b = 1 := by rw [← pow_two]; exact k.hb2

omit [Finite V] in
theorem symm (k : KleinData A a b) : KleinData A b a :=
  ⟨k.hb, k.ha, k.hb1, k.ha1, k.hab.symm, k.hb2, k.ha2, k.comm.symm, fun g hg => by
    rcases k.mem g hg with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (by rw [h, k.comm])))⟩

omit [Finite V] in
theorem third (k : KleinData A a b) : KleinData A a (a * b) := by
  have hab2 : (a * b) ^ 2 = 1 := by
    rw [pow_two]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← k.comm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [k.mul_self_a, k.mul_self_b, one_mul]
  refine ⟨k.ha, A.mul_mem k.ha k.hb, k.ha1, ?_, ?_, k.ha2, hab2, ?_, fun g hg => ?_⟩
  · intro h
    apply k.hab
    have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact (inv_eq_of_mul_eq_one_right k.mul_self_a).symm
  · intro h
    exact k.hb1 (mul_left_cancel (a := a) (b := b) (c := 1) (by rw [mul_one]; exact h.symm))
  · rw [mul_assoc, k.comm.symm]
  · rcases k.mem g hg with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (by rw [h, ← mul_assoc, k.mul_self_a, one_mul])))
    · exact Or.inr (Or.inr (Or.inl h))

omit [Finite V] in
theorem third' (k : KleinData A a b) : KleinData A b (a * b) := by
  have := k.symm.third
  rwa [← k.comm] at this

omit [Finite V] in
theorem commute_all (k : KleinData A a b) {y : MulAut V} (hya : a * y = y * a)
    (hyb : b * y = y * b) : ∀ g ∈ A, g * y = y * g := by
  intro g hg
  rcases k.mem g hg with rfl | rfl | rfl | rfl
  · simp
  · exact hya
  · exact hyb
  · rw [mul_assoc, hyb, ← mul_assoc, hya, mul_assoc]

end KleinData

section D214

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem D214Hyp.isA2 (h : D214Hyp X A r) : IsA2 X A := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec h.mem
  exact hA2

theorem D214Hyp.exists_klein (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) :
    ∃ a b : MulAut V, KleinData A a b := by
  have hA2 := h.isA2
  have hrk : rk A = 2 := D2_14_4 hV h
  have hcard : Nat.card A = 4 := by
    rw [card_eq_two_pow_of_isPGroup hA2.isElemAbelian2.isPGroup, hrk]; norm_num
  obtain ⟨u, v, hu, hv, hu1, hv1, huv, hmem⟩ := exists_card_four hA2.isElemAbelian2 hcard
  exact ⟨u, v, ⟨hu, hv, hu1, hv1, huv, hA2.isElemAbelian2.2 u hu, hA2.isElemAbelian2.2 v hv,
    hA2.isElemAbelian2.1 u hu v hv, hmem⟩⟩

theorem D214Hyp.card_A (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) : Nat.card A = 4 := by
  have hrk : rk A = 2 := D2_14_4 hV h
  rw [card_eq_two_pow_of_isPGroup h.isA2.isElemAbelian2.isPGroup, hrk]; norm_num

theorem D214Hyp.conj_mem (h : D214Hyp X A r) {g y : MulAut V} (hg : g ∈ A)
    (hy : y ∈ pCoreOf 3 X) : g * y * g⁻¹ ∈ pCoreOf 3 X :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X (h.isA2.le hg)) y).mp hy

theorem D214Hyp.centR_conj (h : D214Hyp X A r) {t g y : MulAut V} (ht : t ∈ A) (hg : g ∈ A)
    (hy : y ∈ centR X t) : g * y * g⁻¹ ∈ centR X t := by
  rw [mem_centR] at hy ⊢
  refine ⟨h.conj_mem hg hy.1, ?_⟩
  have hc : Commute g t := h.isA2.isElemAbelian2.1 g hg t ht
  have h1 : g * t * g⁻¹ = t := by rw [hc.eq, mul_inv_cancel_right]
  have hyt : y * t = t * y := hy.2
  calc g * y * g⁻¹ * t = g * y * g⁻¹ * (g * t * g⁻¹) := by rw [h1]
    _ = g * (y * t) * g⁻¹ := by group
    _ = g * (t * y) * g⁻¹ := by rw [hyt]
    _ = (g * t * g⁻¹) * (g * y * g⁻¹) := by group
    _ = t * (g * y * g⁻¹) := by rw [h1]

theorem D214Hyp.isCyclic_centR (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t : MulAut V}
    (ht : t ∈ A) (ht1 : t ≠ 1) : IsCyclic ↥(centR X t) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact isCyclic_inf_centralizer_of_faithful (X := X) (P := pCoreOf 3 X) (A := A) (p := 3)
    (by norm_num) (pCoreOf_le 3 X) (pCoreOf_isPGroup 3 X) h.isA2.isElemAbelian2 h.isA2.le
    (fun a ha y hy => h.conj_mem ha hy) h.sqtk (faithful_pCore_three hV h) ht ht1

theorem isPGroup_centR (X : Subgroup (MulAut V)) (t : MulAut V) : IsPGroup 3 (centR X t) :=
  (pCoreOf_isPGroup 3 X).to_le inf_le_left

theorem eq_one_of_sq_eq_one_of_mem_pCoreOf {X : Subgroup (MulAut V)} {z : MulAut V}
    (hz : z ∈ pCoreOf 3 X) (h : z ^ 2 = 1) : z = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hodd := odd_orderOf_of_mem_pCoreOf hz
  have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hpos := orderOf_pos z
  obtain ⟨m, hm⟩ := hodd
  exact orderOf_eq_one_iff.mp (by omega)

omit [Finite V] in
theorem le_centR_of_mem {X B : Subgroup (MulAut V)} {t : MulAut V} (ht : t ∈ B) :
    pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V)) ≤ centR X t :=
  inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht))

theorem pCoreOf_le_sup_centR (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {a b : MulAut V}
    (k : KleinData A a b) : pCoreOf 3 X ≤ centR X a ⊔ centR X b ⊔ centR X (a * b) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hAP : A ≤ Subgroup.normalizer ((pCoreOf 3 X : Subgroup (MulAut V)) : Set (MulAut V)) :=
    h.isA2.le.trans (le_normalizer_pCoreOf 3 X)
  refine (generation_by_hyperplanes (p := 3) (by norm_num) h.isA2.isElemAbelian2 h.isA2.ne_bot
    (pCoreOf_isPGroup 3 X) hAP).trans ?_
  refine iSup₂_le fun B hB => ?_
  obtain ⟨hBA, hcard⟩ := hB
  have hA4 := h.card_A hV
  have hB2 : Nat.card B = 2 := by omega
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hB2
    omega
  obtain ⟨t, ht⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hBne
  have htB : (t : MulAut V) ∈ B := t.2
  have htA : (t : MulAut V) ∈ A := hBA htB
  have ht1 : (t : MulAut V) ≠ 1 := fun e => ht (Subtype.ext e)
  have hle := le_centR_of_mem (X := X) htB
  rcases k.mem _ htA with e | e | e | e
  · exact absurd e ht1
  · rw [e] at hle
    exact hle.trans (le_sup_left.trans le_sup_left)
  · rw [e] at hle
    exact hle.trans (le_sup_right.trans le_sup_left)
  · rw [e] at hle
    exact hle.trans le_sup_right

theorem centP_trivial (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {a b : MulAut V}
    (k : KleinData A a b) {z : MulAut V} (hz : z ∈ pCoreOf 3 X) (hza : a * z = z * a)
    (hzb : b * z = z * b) : z = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_contra hz1
  have hzall := k.commute_all hza hzb
  have key : ∀ t t' : MulAut V, KleinData A t t' → ∀ y ∈ centR X t, ∀ g ∈ A, g * y = y * g := by
    intro t t' kk y hy g hg
    have hzt : z ∈ centR X t := by
      rw [mem_centR]
      exact ⟨hz, (hzall t kk.ha).symm⟩
    rcases involution_on_cyclic (p := 3) (by norm_num) (isPGroup_centR X t)
      (h.isCyclic_centR hV kk.ha kk.ha1) kk.hb2
      (fun y hy => h.centR_conj kk.ha kk.hb hy) with htriv | hinv
    · have hy' := htriv y hy
      have hyt' : t' * y = y * t' := mul_inv_eq_iff_eq_mul.mp hy'
      have hyt : t * y = y * t := ((mem_centR.mp hy).2).symm
      exact kk.commute_all hyt hyt' g hg
    · exfalso
      have h1 := hinv z hzt
      have h2 : t' * z * t'⁻¹ = z := by rw [hzall t' kk.hb, mul_inv_cancel_right]
      rw [h2] at h1
      apply hz1
      apply eq_one_of_sq_eq_one_of_mem_pCoreOf hz
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr h1
  have hgen := pCoreOf_le_sup_centR hV h k
  have hall : ∀ y ∈ pCoreOf 3 X, a * y = y * a := by
    intro y hy
    have hy' := hgen hy
    have hcent : centR X a ⊔ centR X b ⊔ centR X (a * b) ≤
        Subgroup.centralizer (A : Set (MulAut V)) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        exact Subgroup.mem_centralizer_iff.mpr fun g hg => key a b k y hy g hg
      · intro y hy
        exact Subgroup.mem_centralizer_iff.mpr fun g hg => key b a k.symm y hy g hg
      · intro y hy
        exact Subgroup.mem_centralizer_iff.mpr fun g hg => key (a * b) a k.third.symm y hy g hg
    exact Subgroup.mem_centralizer_iff.mp (hcent hy') a k.ha
  exact k.ha1 (faithful_pCore_three hV h a k.ha hall)

theorem inverts_centR (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {a b : MulAut V}
    (k : KleinData A a b) : ∀ y ∈ centR X a, b * y * b⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rcases involution_on_cyclic (p := 3) (by norm_num) (isPGroup_centR X a)
    (h.isCyclic_centR hV k.ha k.ha1) k.hb2
    (fun y hy => h.centR_conj k.ha k.hb hy) with htriv | hinv
  · intro y hy
    have h1 := htriv y hy
    have hyb : b * y = y * b := mul_inv_eq_iff_eq_mul.mp h1
    have hya : a * y = y * a := ((mem_centR.mp hy).2).symm
    have : y = 1 := centP_trivial hV h k (mem_centR.mp hy).1 hya hyb
    rw [this]; simp
  · exact hinv

theorem not_centR_bot_pair (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {a b : MulAut V}
    (k : KleinData A a b) : ¬ (centR X a = ⊥ ∧ centR X b = ⊥) := by
  rintro ⟨ha, hb⟩
  have hgen := pCoreOf_le_sup_centR hV h k
  rw [ha, hb, bot_sup_eq, bot_sup_eq] at hgen
  have hab : a * b ∈ A := A.mul_mem k.ha k.hb
  have hab1 : a * b ≠ 1 := k.third.hb1
  apply hab1
  apply faithful_pCore_three hV h (a * b) hab
  intro y hy
  exact ((mem_centR.mp (hgen hy)).2).symm

theorem centR_data (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {a b : MulAut V}
    (k : KleinData A a b) (hne : centR X a ≠ ⊥) :
    Nat.card (centR X a) = 3 ∧
      rk (commSub (fixV (Subgroup.zpowers a)) (centR X a)) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hrkA : rk A = 2 := D2_14_4 hV h
  have hrk : 1 < rk A := by omega
  set B := Subgroup.zpowers a with hB
  have hBA : B ≤ A := Subgroup.zpowers_le.mpr k.ha
  have hBcard : Nat.card A = 2 * Nat.card B := by
    rw [h.card_A hV, hB, Nat.card_zpowers, orderOf_eq_prime k.ha2 k.ha1]
  have hcentB : pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V)) = centR X a := by
    apply le_antisymm (le_centR_of_mem (X := X) (Subgroup.mem_zpowers a))
    intro y hy
    obtain ⟨hyP, hya⟩ := mem_centR.mp hy
    refine ⟨hyP, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute a y from hya.symm) j).eq
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hyC : (y : MulAut V) ∈ centR X a := y.2
  have hyP : (y : MulAut V) ∈ pCoreOf 3 X := (mem_centR.mp hyC).1
  have hy1' : (y : MulAut V) ≠ 1 := fun e => hy1 (Subtype.ext e)
  have hbinv := inverts_centR hV h k _ hyC
  have hnc : b * (y : MulAut V) ≠ (y : MulAut V) * b := by
    intro hc
    have h1 : b * (y : MulAut V) * b⁻¹ = (y : MulAut V) := by rw [hc, mul_inv_cancel_right]
    rw [h1] at hbinv
    apply hy1'
    apply eq_one_of_sq_eq_one_of_mem_pCoreOf hyP
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr hbinv
  have hD3 : ⁅pCoreOf 3 X, A⁆ ≠ ⊥ := commutator_ne_bot_iff.mpr ⟨y, hyP, b, k.hb, hnc⟩
  have h13 := (D2_13 hV h.qhat h.mem (p := 3) (by norm_num) (D := ⁅pCoreOf 3 X, A⁆) rfl
    hD3).2.2.2.2 hrk
  obtain ⟨-, hB'⟩ := h13
  set D' := ⁅pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V)), A⁆ with hD'
  have hD'ne : D' ≠ ⊥ := by
    rw [hD', hcentB]
    exact commutator_ne_bot_iff.mpr ⟨y, hyC, b, k.hb, hnc⟩
  obtain ⟨hc3, -, -, hr2⟩ := hB' B hBA hBcard D' rfl hD'ne
  have hDeq : D' = centR X a := by
    apply le_antisymm
    · rw [hD', hcentB]
      refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
      have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ centR X a := h.centR_conj k.ha hg₂ ((centR X a).inv_mem hg₁)
      have : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact (centR X a).mul_mem hg₁ h1
    · intro z hz
      have hzP := (mem_centR.mp hz).1
      have hzb := inverts_centR hV h k z hz
      have hsq : z ^ 2 ∈ D' := by
        have hcomm : ⁅z, b⁆ ∈ D' := by
          rw [hD', hcentB]
          exact Subgroup.commutator_mem_commutator hz k.hb
        have : ⁅z, b⁆ = z ^ 2 := by
          have e : ⁅z, b⁆ = z * (b * z * b⁻¹)⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e, hzb, inv_inv, pow_two]
        rwa [this] at hcomm
      have hodd := odd_orderOf_of_mem_pCoreOf hzP
      obtain ⟨m, hm⟩ := hodd
      have : z = (z ^ 2) ^ (m + 1) := by
        have e : (z ^ 2) ^ (m + 1) = z ^ (2 * (m + 1)) := by rw [← pow_mul]
        rw [e]
        have h2 : 2 * (m + 1) = orderOf z + 1 := by omega
        rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
      rw [this]
      exact D'.pow_mem hsq _
  rw [hDeq] at hc3 hr2
  exact ⟨hc3, hr2⟩

end D214

end CFSG.Quasithin
