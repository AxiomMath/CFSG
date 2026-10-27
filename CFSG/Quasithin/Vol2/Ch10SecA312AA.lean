module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LieType.BorelTits.Basic
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.QuasithinUnique

variable {X : Type} [Group X]

@[expose] def ptStab (S : Set X) : Subgroup (MulAut X) where
  carrier := {ρ | ∀ x ∈ S, ρ x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x hx => by
    show a (b x) = x
    rw [hb x hx, ha x hx]
  inv_mem' := fun {a} ha x hx => by
    show a.symm x = x
    conv_lhs => rw [← ha x hx]
    exact a.symm_apply_apply x

@[expose] def setStab (S : Set X) : Subgroup (MulAut X) where
  carrier := {ρ | ∀ x, x ∈ S ↔ ρ x ∈ S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (hb x).trans (ha (b x))
  inv_mem' := fun {a} ha x => by
    show x ∈ S ↔ a.symm x ∈ S
    rw [ha (a.symm x), MulEquiv.apply_symm_apply]

theorem mul_conj_mul_inv (α : MulAut X) (t : X) :
    α * MulAut.conj t * α⁻¹ = MulAut.conj (α t) := by
  ext x
  show α (t * α.symm x * t⁻¹) = α t * x * (α t)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem conj_mem_setStab {S : Subgroup X} {t : X}
    (ht : t ∈ Subgroup.normalizer (S : Set X)) : MulAut.conj t ∈ setStab (S : Set X) :=
  fun x => Subgroup.mem_normalizer_iff.mp ht x

theorem mem_setStab_of_mem_ptStab {S : Set X} {ρ : MulAut X} (h : ρ ∈ ptStab S) :
    ρ ∈ setStab S := by
  intro x
  constructor
  · intro hx
    show ρ x ∈ S
    rw [h x hx]
    exact hx
  · intro hx
    have h2 : ρ.symm (ρ x) = ρ x := ((ptStab S).inv_mem h) (ρ x) hx
    rw [MulEquiv.symm_apply_apply] at h2
    rw [h2]
    exact hx

theorem mem_setStab_of_maps {T : Subgroup X} {α : MulAut X} (hαT : ∀ t ∈ T, α t ∈ T) {k : ℕ}
    (hk : α ^ 2 ^ k = 1) : α ∈ setStab (T : Set X) := by
  have hpow : ∀ n : ℕ, ∀ t ∈ T, (α ^ n) t ∈ T := by
    intro n
    induction n with
    | zero => exact fun t ht => ht
    | succ n ih =>
      intro t ht
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hαT t ht)
  have hinv : α⁻¹ = α ^ (2 ^ k - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hk]
  intro x
  constructor
  · exact hαT x
  · intro hx
    have h := hpow (2 ^ k - 1) _ hx
    rw [← hinv] at h
    have h' : α⁻¹ (α x) = x := α.symm_apply_apply x
    rw [h'] at h
    exact h

theorem fix_of_commute [Finite X] (hO : CFSG.pCore 2 X = ⊥) {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) {β : MulAut X} (hβT : β ∈ setStab (T : Set X))
    (hc : ∀ t ∈ T, β * MulAut.conj t = MulAut.conj t * β) : ∀ t ∈ T, β t = t := by
  intro t ht
  have h1 : MulAut.conj (β t) = MulAut.conj t := by
    rw [← mul_conj_mul_inv, hc t ht, mul_inv_cancel_right]
  have hc' : t⁻¹ * β t ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h2 := congrArg (fun φ : MulAut X => φ x) h1
    simp only [MulAut.conj_apply] at h2
    have h3 : β t * x = t * x * (t⁻¹ * β t) := by
      calc β t * x = β t * x * (β t)⁻¹ * β t := by group
        _ = t * x * t⁻¹ * β t := by rw [h2]
        _ = t * x * (t⁻¹ * β t) := by group
    calc x * (t⁻¹ * β t) = t⁻¹ * (t * x * (t⁻¹ * β t)) := by group
      _ = t⁻¹ * (β t * x) := by rw [h3]
      _ = t⁻¹ * β t * x := by group
  have hT' : t⁻¹ * β t ∈ T := T.mul_mem (T.inv_mem ht) ((hβT t).mp ht)
  have hle : T ⊓ Subgroup.center X ≤ CFSG.pCore 2 X :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup
      (Subgroup.normal_of_le_center inf_le_right) (hT.isPGroup.to_inf_left)
  have h4 : t⁻¹ * β t = 1 := by
    have := hle ⟨hT', hc'⟩
    rw [hO] at this
    exact this
  calc β t = t * (t⁻¹ * β t) := by group
    _ = t := by rw [h4, mul_one]

theorem exists_pow_involution {R : Type*} [Group R] [Finite R] (hR : IsPGroup 2 R) {γ : R}
    (hγ : γ ≠ 1) : ∃ n : ℕ, γ ^ n ≠ 1 ∧ γ ^ n * γ ^ n = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hR) γ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hγ (orderOf_eq_one_iff.mp (by rw [ha, pow_zero]))
  have hdvd : 2 ^ (a - 1) ∣ orderOf γ := by
    rw [ha]
    exact Nat.pow_dvd_pow 2 (Nat.sub_le a 1)
  have hord : orderOf (γ ^ 2 ^ (a - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, ha]
    have : 2 ^ a = 2 ^ (a - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha0)]
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  refine ⟨2 ^ (a - 1), fun h => ?_, ?_⟩
  · rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · have h := pow_orderOf_eq_one (γ ^ 2 ^ (a - 1))
    rw [hord, pow_two] at h
    exact h

theorem exists_involution_fix [Finite X] (hO : CFSG.pCore 2 X = ⊥) {T B : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hTB : T ≤ Subgroup.normalizer (B : Set X)) {α : MulAut X}
    (hαB : ∀ b ∈ B, α b = b) (hαT : ∀ t ∈ T, α t ∈ T) (hα2 : ∃ k : ℕ, α ^ 2 ^ k = 1)
    (hα1 : α ≠ 1) :
    ∃ β : MulAut X, β ≠ 1 ∧ β * β = 1 ∧ (∀ b ∈ B, β b = b) ∧ ∀ t ∈ T, β t = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hα2
  have hαTs : α ∈ setStab (T : Set X) := mem_setStab_of_maps hαT hk
  have hαB' : α ∈ ptStab (B : Set X) := hαB
  set N : Subgroup (MulAut X) := T.map (MulAut.conj : X →* MulAut X) with hN
  set R : Subgroup (MulAut X) := N ⊔ Subgroup.zpowers α with hR
  have hNp : IsPGroup 2 N := hT.isPGroup.map _
  have hZp : IsPGroup 2 (Subgroup.zpowers α) := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hαN : α ∈ Subgroup.normalizer (N : Set (MulAut X)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨α t, hαT t ht, (mul_conj_mul_inv α t).symm⟩
    · rintro ⟨s, hs, hsh⟩
      refine ⟨α⁻¹ s, ((setStab (T : Set X)).inv_mem hαTs s).mp hs, ?_⟩
      have h1 : MulAut.conj (α⁻¹ s) = α⁻¹ * MulAut.conj s * α⁻¹⁻¹ := (mul_conj_mul_inv α⁻¹ s).symm
      rw [h1]
      change α⁻¹ * (MulAut.conj : X →* MulAut X) s * α⁻¹⁻¹ = h
      rw [hsh, inv_inv]
      group
  have hRp : IsPGroup 2 R :=
    hNp.to_sup_of_normal_left' hZp ((Subgroup.zpowers_le).mpr hαN)
  have hRB : R ≤ setStab (B : Set X) := by
    refine sup_le ?_ ((Subgroup.zpowers_le).mpr (mem_setStab_of_mem_ptStab hαB'))
    rintro _ ⟨t, ht, rfl⟩
    exact conj_mem_setStab (hTB ht)
  have hRT : R ≤ setStab (T : Set X) := by
    refine sup_le ?_ ((Subgroup.zpowers_le).mpr hαTs)
    rintro _ ⟨t, ht, rfl⟩
    exact conj_mem_setStab (Subgroup.le_normalizer ht)
  set C : Subgroup R := (ptStab (B : Set X)).subgroupOf R with hC
  have hCn : C.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hC, Subgroup.mem_subgroupOf] at hn ⊢
    intro b hb
    have hgB := hRB g.2
    have hb' : (g : MulAut X)⁻¹ b ∈ B := ((setStab (B : Set X)).inv_mem hgB b).mp hb
    show (g : MulAut X) ((n : MulAut X) ((g : MulAut X)⁻¹ b)) = b
    rw [hn _ hb']
    exact (g : MulAut X).apply_symm_apply b
  have hαR : α ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers α)
  have hC1 : C ≠ ⊥ := by
    intro h
    have hmem : (⟨α, hαR⟩ : R) ∈ C := by
      rw [hC, Subgroup.mem_subgroupOf]
      exact hαB'
    rw [h, Subgroup.mem_bot] at hmem
    exact hα1 (congrArg Subtype.val hmem)
  have hRp' : IsPGroup 2 ↥R := hRp
  have : Group.IsNilpotent ↥R := hRp'.isNilpotent
  have hCZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hC1
  obtain ⟨γ, hγ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hCZ
  have hγ1' : (γ : R) ≠ 1 := fun h => hγ1 (Subtype.ext h)
  obtain ⟨n, hn1, hn2⟩ := exists_pow_involution hRp' hγ1'
  have hδC : (γ : R) ^ n ∈ C := C.pow_mem γ.2.1 n
  have hδZ : (γ : R) ^ n ∈ Subgroup.center R := (Subgroup.center R).pow_mem γ.2.2 n
  refine ⟨(((γ : R) ^ n : R) : MulAut X), fun h => hn1 (Subtype.ext h), ?_, ?_, ?_⟩
  · have := congrArg Subtype.val hn2
    simpa using this
  · exact Subgroup.mem_subgroupOf.mp hδC
  · refine fix_of_commute hO hT (hRT ((γ : R) ^ n).2) fun t ht => ?_
    have hct : (⟨MulAut.conj t, Subgroup.mem_sup_left ⟨t, ht, rfl⟩⟩ : R) * (γ : R) ^ n =
        (γ : R) ^ n * ⟨MulAut.conj t, Subgroup.mem_sup_left ⟨t, ht, rfl⟩⟩ :=
      (Subgroup.mem_center_iff.mp hδZ) _
    exact (congrArg Subtype.val hct).symm

theorem exists_center_of_conj [Finite X] {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) {g : X}
    (hg : MulAut.conj g * MulAut.conj g = 1) (hgT : ∀ t ∈ T, MulAut.conj g t = t) :
    ∃ z ∈ T, (∀ t ∈ T, z * t = t * z) ∧ MulAut.conj z = MulAut.conj g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgc : g ∈ Subgroup.centralizer (T : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h := hgT t ht
    rw [MulAut.conj_apply] at h
    calc t * g = g * t * g⁻¹ * g := by rw [h]
      _ = g * t := by group
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hbez : ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m + (m : ℤ) * Nat.gcdB (2 ^ a) m = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop]
    rfl
  set A := Nat.gcdA (2 ^ a) m
  set Bz := Nat.gcdB (2 ^ a) m
  set w := g ^ (((2 ^ a : ℕ) : ℤ) * A) with hw
  set z := g ^ ((m : ℤ) * Bz) with hz
  have hgwz : g = w * z := by
    rw [hw, hz, ← zpow_add, hbez, zpow_one]
  have hn : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hz2 : z ^ 2 ^ a = 1 := by
    rw [hz, ← zpow_natCast, ← zpow_mul]
    have : (m : ℤ) * Bz * ((2 ^ a : ℕ) : ℤ) = (orderOf g : ℤ) * Bz := by
      rw [hnm]
      push_cast
      ring
    rw [this, zpow_mul, zpow_natCast, hn, one_zpow]
  have hw1 : MulAut.conj w = 1 := by
    set c := MulAut.conj w with hcdef
    have hc2 : c ^ 2 = 1 := by
      rw [hcdef, hw, map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        show ((2 : ℕ) : ℤ) = 2 by rfl, zpow_two, hg, one_zpow]
    have hcm : c ^ m = 1 := by
      rw [hcdef, ← map_pow, hw, ← zpow_natCast, ← zpow_mul]
      have : ((2 ^ a : ℕ) : ℤ) * A * (m : ℤ) = (orderOf g : ℤ) * A := by
        rw [hnm]
        push_cast
        ring
      rw [this, zpow_mul, zpow_natCast, hn, one_zpow, map_one]
    have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    have h2 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one hcm
    have h3 : orderOf c ∣ Nat.gcd 2 m := Nat.dvd_gcd h1 h2
    rw [Nat.coprime_two_left.mpr hm] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hzc : z ∈ Subgroup.centralizer (T : Set X) := by
    rw [hz]
    exact Subgroup.zpow_mem _ hgc _
  have hzN : z ∈ Subgroup.normalizer (T : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hcomm : ∀ s ∈ T, z * s * z⁻¹ = s := fun s hs => by
      rw [(Subgroup.mem_centralizer_iff.mp hzc s hs).symm]
      group
    constructor
    · intro hh
      rw [hcomm h hh]
      exact hh
    · intro hh
      have := hcomm _ hh
      have e : h = z * h * z⁻¹ := by
        calc h = z⁻¹ * (z * h * z⁻¹) * z := by group
          _ = z⁻¹ * (z * (z * h * z⁻¹) * z⁻¹) * z := by rw [this]
          _ = z * h * z⁻¹ := by group
      rw [e]
      exact hh
  have hzp : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨x, hx⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨a, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
  have hsup : IsPGroup 2 ↥(T ⊔ Subgroup.zpowers z) :=
    hT.isPGroup.to_sup_of_normal_left' hzp ((Subgroup.zpowers_le).mpr hzN)
  have heq := IsSylowTwoOf.eq_of_le hT le_sup_left le_top hsup
  have hzT : z ∈ T := by
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  refine ⟨z, hzT, fun t ht => (Subgroup.mem_centralizer_iff.mp hzc t ht).symm, ?_⟩
  rw [hgwz, map_mul, hw1, one_mul]

theorem false_of_V [Finite X] {B V : Subgroup X} (hVB : V ≤ B) (hV : IsElemAbelian 2 V)
    (hBV : B ≤ Subgroup.normalizer (V : Set X)) (hcomm : ⁅V, B⁆ = V) (hV1 : V ≠ ⊥)
    (hc : pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X))
    (hZ : ∀ v ∈ pCoreOf 2 B, (∀ u ∈ pCoreOf 2 B, u * v = v * u) → v * v = 1 →
      ∀ b ∈ B, b * v = v * b) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  have hVO : V ≤ pCoreOf 2 B := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVB hBV hVp
  have hle : V ≤ Subgroup.centralizer (B : Set X) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    refine hZ v (hVO hv) (fun u hu => ?_) ?_ b hb
    · exact (Subgroup.mem_centralizer_iff.mp (hc hu) v hv).symm
    · rw [← pow_two]
      exact hV.2 v hv
  have hbot : ⁅V, B⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hle
  exact hV1 (hcomm ▸ hbot)

end CFSG.Quasithin.Vol2.Ch10.A312A
