module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Quasithin.Background.G6PGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type*} [CommGroup V]

@[expose] def norm3 (k : MulAut V) : V →* V where
  toFun x := x * k x * k (k x)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    ac_rfl

theorem norm3_apply (k : MulAut V) (x : V) : norm3 k x = x * k x * k (k x) := rfl

theorem norm3_comp (k : MulAut V) (hk : k ^ 3 = 1) (x : V) : norm3 k (k x) = norm3 k x := by
  have h3 : k (k (k x)) = x := by
    have := congrArg (fun f : MulAut V => f x) hk
    simpa [pow_succ] using this
  rw [norm3_apply, norm3_apply, h3]
  ac_rfl

theorem fixV_zpowers_iff {k : MulAut V} {v : V} : v ∈ fixV (Subgroup.zpowers k) ↔ k v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem norm3_mem_fixV (k : MulAut V) (hk : k ^ 3 = 1) (x : V) :
    norm3 k x ∈ fixV (Subgroup.zpowers k) := by
  rw [fixV_zpowers_iff]
  have h3 : k (k (k x)) = x := by
    have := congrArg (fun f : MulAut V => f x) hk
    simpa [pow_succ] using this
  rw [norm3_apply, map_mul, map_mul, h3]
  ac_rfl

theorem commV_le_ker_norm3 (k : MulAut V) (hk : k ^ 3 = 1) :
    commV (Subgroup.zpowers k) ≤ (norm3 k).ker := by
  have hz : ∀ (z : ℤ) (v : V), norm3 k ((k ^ z) v) = norm3 k v := by
    intro z
    induction z using Int.induction_on with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      rw [zpow_add_one, MulAut.mul_apply, ih (k v), norm3_comp k hk]
    | pred i ih =>
      intro v
      rw [zpow_sub_one, MulAut.mul_apply, ih (k⁻¹ v), ← norm3_comp k hk (k⁻¹ v)]
      simp
  rw [G6.commV_le_iff]
  intro x hx v
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [MonoidHom.mem_ker, map_mul, map_inv, hz, mul_inv_cancel]

theorem commV_inf_fixV_of_pow_three (hV : ∀ v : V, v ^ 2 = 1) {k : MulAut V} (hk : k ^ 3 = 1) :
    commV (Subgroup.zpowers k) ⊓ fixV (Subgroup.zpowers k) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
  have hn : norm3 k y = 1 := commV_le_ker_norm3 k hk hy1
  have hy2' : k y = y := fixV_zpowers_iff.1 hy2
  rw [norm3_apply, hy2', hy2', ← sq, hV, one_mul] at hn
  rw [Subgroup.mem_bot]
  exact hn

theorem commV_sup_fixV_of_pow_three (hV : ∀ v : V, v ^ 2 = 1) {k : MulAut V} (hk : k ^ 3 = 1) :
    commV (Subgroup.zpowers k) ⊔ fixV (Subgroup.zpowers k) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : k x * x⁻¹ ∈ commV (Subgroup.zpowers k) :=
    G6.mem_commV_of_mem (Subgroup.mem_zpowers k) x
  have h2 : k (k x) * x⁻¹ ∈ commV (Subgroup.zpowers k) := by
    have := G6.mem_commV_of_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers k) 2) x
    simpa [pow_two] using this
  have hx : x = ((k x * x⁻¹) * (k (k x) * x⁻¹)) * norm3 k x := by
    have hx2 : x * x = 1 := by rw [← sq, hV]
    have hkx2 : k x * k x = 1 := by rw [← sq, hV]
    have hkkx2 : k (k x) * k (k x) = 1 := by rw [← sq, hV]
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [norm3_apply, hxinv]
    calc x = (k x * k x) * (k (k x) * k (k x)) * (x * x) * x := by
          rw [hkx2, hkkx2, hx2]; simp
      _ = k x * x * (k (k x) * x) * (x * k x * k (k x)) := by ac_rfl
  rw [hx]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem _ h1 h2) (norm3_mem_fixV k hk x)

theorem exists_fixed_ne_one {A Q : Type*} [Group A] [Finite A] [Group Q] [MulAction Q A]
    (hQ : IsPGroup 2 Q) (hA : ∀ a : A, a ^ 2 = 1) (h1 : ∀ q : Q, q • (1 : A) = 1)
    (hne : ∃ a : A, a ≠ 1) : ∃ a : A, a ≠ 1 ∧ ∀ q : Q, q • a = a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hQ.card_modEq_card_fixedPoints A
  obtain ⟨a₀, ha₀⟩ := hne
  have heven : 2 ∣ Nat.card A := by
    rw [← orderOf_eq_prime (hA a₀) ha₀]
    exact orderOf_dvd_natCard a₀
  by_contra hcon
  push Not at hcon
  have hfix : Nat.card (MulAction.fixedPoints Q A) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, h1⟩⟩⟩
    have hx : (x : A) = 1 := by
      by_contra hx
      obtain ⟨q, hq⟩ := hcon x hx
      exact hq (x.2 q)
    have hy : (y : A) = 1 := by
      by_contra hy
      obtain ⟨q, hq⟩ := hcon y hy
      exact hq (y.2 q)
    rw [hx, hy]
  rw [hfix] at hmod
  unfold Nat.ModEq at hmod
  omega

theorem IsSylowTwoOf.eq_of_le {G : Type*} [Group G] [Finite G] {P Q X : Subgroup G}
    (hP : IsSylowTwoOf P X) (hPQ : P ≤ Q) (hQX : Q ≤ X) (hQ : IsPGroup 2 Q) : Q = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul := Subgroup.relIndex_mul_relIndex P Q X hPQ hQX
  have hodd : ¬ 2 ∣ P.relIndex X := hP.2.2
  have hpow : ∃ m : ℕ, P.relIndex Q = 2 ^ m := by
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hQ
    have hdvd : P.relIndex Q ∣ 2 ^ b := hb ▸ Subgroup.relIndex_dvd_card P Q
    exact (Nat.dvd_prime_pow Nat.prime_two).1 hdvd |>.imp fun _ h => h.2
  obtain ⟨m, hm⟩ := hpow
  have hm0 : m = 0 := by
    by_contra hm0
    apply hodd
    rw [← hmul, hm]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 hm0) _
  rw [hm0, pow_zero, Subgroup.relIndex_eq_one] at hm
  exact le_antisymm hm hPQ

@[expose] def signHom (u : V) (hu : u * u = 1) : ℤˣ →* V where
  toFun e := if e = 1 then 1 else u
  map_one' := by simp
  map_mul' e f := by
    rcases Int.units_eq_one_or e with rfl | rfl <;> rcases Int.units_eq_one_or f with rfl | rfl
    · simp
    · simp
    · simp
    · simp [hu]

theorem signHom_apply_mem (u : V) (hu : u * u = 1) (e : ℤˣ) :
    signHom u hu e = 1 ∨ signHom u hu e = u := by
  unfold signHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs <;> simp

theorem signHom_mul_self (u : V) (hu : u * u = 1) (e : ℤˣ) :
    signHom u hu e * signHom u hu e = 1 := by
  rcases signHom_apply_mem u hu e with h | h <;> rw [h]
  · exact mul_one 1
  · exact hu

theorem map_signHom {χ : V →* ℤˣ} {u : V} (hu : u * u = 1) (hχu : χ u = 1) (e : ℤˣ) :
    χ (signHom u hu e) = 1 := by
  rcases signHom_apply_mem u hu e with h | h <;> rw [h]
  · exact map_one χ
  · exact hχu

@[expose] def transvectionOf (χ : V →* ℤˣ) (u : V) (hu : u * u = 1) (hχu : χ u = 1) :
    MulAut V where
  toFun v := v * signHom u hu (χ v)
  invFun v := v * signHom u hu (χ v)
  left_inv v := by
    show v * signHom u hu (χ v) * signHom u hu (χ (v * signHom u hu (χ v))) = v
    rw [map_mul, map_signHom hu hχu, mul_one, mul_assoc, signHom_mul_self, mul_one]
  right_inv v := by
    show v * signHom u hu (χ v) * signHom u hu (χ (v * signHom u hu (χ v))) = v
    rw [map_mul, map_signHom hu hχu, mul_one, mul_assoc, signHom_mul_self, mul_one]
  map_mul' v w := by
    simp only [map_mul]
    ac_rfl

theorem transvectionOf_apply (χ : V →* ℤˣ) (u : V) (hu : u * u = 1) (hχu : χ u = 1) (v : V) :
    transvectionOf χ u hu hχu v = v * signHom u hu (χ v) := rfl

theorem false_of_sylow_normalizes [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {P : Subgroup (MulAut V)}
    (hP : IsSylowTwoOf P ⊤) {k : MulAut V} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1)
    (hPk : P ≤ Subgroup.normalizer (Subgroup.zpowers k : Set (MulAut V)))
    (hC : fixV (Subgroup.zpowers k) ≠ ⊥) : False := by
  classical
  set W := commV (Subgroup.zpowers k) with hW
  set C := fixV (Subgroup.zpowers k) with hCdef
  have hWC : W ⊓ C = ⊥ := commV_inf_fixV_of_pow_three hV hk3
  have hWC' : W ⊔ C = ⊤ := commV_sup_fixV_of_pow_three hV hk3
  have hconj : ∀ p ∈ P, ∀ x ∈ Subgroup.zpowers k, p * x * p⁻¹ ∈ Subgroup.zpowers k :=
    fun p hp x hx => (Subgroup.mem_normalizer_iff.1 (hPk hp) x).1 hx
  have hPW : ∀ p ∈ P, ∀ w ∈ W, p w ∈ W := fun p hp w hw =>
    G6.apply_mem_commV (X := Subgroup.zpowers k) (hconj p hp) hw
  have hPC : ∀ p ∈ P, ∀ c ∈ C, p c ∈ C := by
    intro p hp c hc
    rw [mem_fixV] at hc ⊢
    intro x hx
    have h1 : p⁻¹ * x * p ∈ Subgroup.zpowers k := by
      have := hconj p⁻¹ (P.inv_mem hp) x hx
      simpa using this
    have h2 := hc _ h1
    have : x (p c) = p ((p⁻¹ * x * p) c) := by simp
    rw [this, h2]
  have hW1 : ∃ w : W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hk1
    ext v
    have h := hcon ⟨k v * v⁻¹, G6.mem_commV_of_mem (Subgroup.mem_zpowers k) v⟩
    have h' : k v * v⁻¹ = 1 := congrArg Subtype.val h
    simpa [mul_inv_eq_one] using h'
  have hP2 : IsPGroup 2 P := hP.2.1
  let actW : MulAction P W :=
    { smul := fun p w => ⟨(p : MulAut V) w, hPW p p.2 w w.2⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun p q w => Subtype.ext rfl }
  obtain ⟨u, hu1, hufix⟩ := exists_fixed_ne_one (A := W) (Q := P) hP2
    (fun w => Subtype.ext (hV w)) (fun p => Subtype.ext (map_one (p : MulAut V))) hW1
  have hufix' : ∀ p ∈ P, p (u : V) = u := fun p hp =>
    congrArg Subtype.val (hufix ⟨p, hp⟩)
  have hu1' : (u : V) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huu : (u : V) * u = 1 := by rw [← sq, hV]
  let chars : Subgroup (V →* ℤˣ) :=
    { carrier := {f | ∀ w ∈ W, f w = 1}
      one_mem' := fun w _ => rfl
      mul_mem' := fun {f g} hf hg w hw => by simp [hf w hw, hg w hw]
      inv_mem' := fun {f} hf w hw => by simp [hf w hw] }
  let actC : MulAction P chars :=
    { smul := fun p f => ⟨f.1.comp ((p : MulAut V)⁻¹).toMonoidHom, fun w hw => by
        simpa using f.2 _ (hPW _ (P.inv_mem p.2) w hw)⟩
      one_smul := fun f => Subtype.ext (MonoidHom.ext fun v => rfl)
      mul_smul := fun p q f => Subtype.ext (MonoidHom.ext fun v => by
        show f.1 (((p : MulAut V) * q)⁻¹ v) = f.1 ((q : MulAut V)⁻¹ ((p : MulAut V)⁻¹ v))
        rw [mul_inv_rev]
        rfl) }
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hC
    rw [← hWC, htop, top_inf_eq]
  obtain ⟨f₀, hf₀1, hf₀W⟩ := G6.exists_character_of_ne_top hV hWtop
  obtain ⟨χ, hχ1, hχfix⟩ := exists_fixed_ne_one (A := chars) (Q := P) hP2
    (fun f => Subtype.ext (MonoidHom.ext fun v => by
      show (f.1 v) ^ 2 = 1
      rcases Int.units_eq_one_or (f.1 v) with h | h <;> rw [h] <;> rfl))
    (fun p => Subtype.ext (MonoidHom.ext fun v => rfl))
    ⟨⟨f₀, hf₀W⟩, fun h => hf₀1 (congrArg Subtype.val h)⟩
  have hχW : ∀ w ∈ W, χ.1 w = 1 := χ.2
  have hχP : ∀ p ∈ P, ∀ v, χ.1 (p v) = χ.1 v := by
    intro p hp v
    have h := hχfix ⟨p, hp⟩
    have h' : ((⟨p, hp⟩ : P) • χ).1 (p v) = χ.1 (p v) := by rw [h]
    have h'' : ((⟨p, hp⟩ : P) • χ).1 (p v) = χ.1 v := by
      show χ.1 ((p : MulAut V)⁻¹ (p v)) = χ.1 v
      simp
    rw [← h', h'']
  have hχ1' : χ.1 ≠ 1 := fun h => hχ1 (Subtype.ext h)
  have hχu : χ.1 u = 1 := hχW u u.2
  set τ := transvectionOf χ.1 u huu hχu with hτ
  have hτP : ∀ p ∈ P, p * τ * p⁻¹ = τ := by
    intro p hp
    ext v
    rw [MulAut.mul_apply, MulAut.mul_apply, transvectionOf_apply, transvectionOf_apply, map_mul]
    have hχv : χ.1 ((p : MulAut V)⁻¹ v) = χ.1 v := by
      have := hχP p hp ((p : MulAut V)⁻¹ v)
      simpa using this.symm
    rw [hχv]
    have : p ((p : MulAut V)⁻¹ v) = v := by simp
    rw [this]
    rcases signHom_apply_mem (u : V) huu (χ.1 v) with h | h <;> rw [h]
    · rw [map_one]
    · rw [hufix' p hp]
  have hτ2 : τ * τ = 1 := by
    ext v
    rw [MulAut.mul_apply, MulAut.one_apply]
    exact (transvectionOf χ.1 u huu hχu).left_inv v
  have hτnot : τ ∉ P := by
    intro hτP'
    obtain ⟨c, hcC, hχc⟩ : ∃ c ∈ C, χ.1 c ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hχ1'
      ext v
      have hv : v ∈ W ⊔ C := by rw [hWC']; trivial
      obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
      simp [hχW w hw, hcon c hc]
    have hτc : τ c = c * u := by
      rw [hτ, transvectionOf_apply]
      congr 1
      unfold signHom
      simp [hχc]
    have hmem : τ c ∈ C := hPC τ hτP' c hcC
    rw [hτc] at hmem
    have huC : (u : V) ∈ C := by
      have := C.mul_mem (C.inv_mem hcC) hmem
      simpa using this
    have : (u : V) ∈ W ⊓ C := ⟨u.2, huC⟩
    rw [hWC, Subgroup.mem_bot] at this
    exact hu1' this
  have hτ2grp : IsPGroup 2 (Subgroup.zpowers τ) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    apply orderOf_eq_prime
    · rw [sq]; exact hτ2
    · intro h
      apply hτnot
      rw [h]
      exact P.one_mem
  have hsup : IsPGroup 2 (P ⊔ Subgroup.zpowers τ : Subgroup (MulAut V)) := by
    refine IsPGroup.to_sup_of_normal_right' hP2 hτ2grp ?_
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← conj_zpow, hτP p hp]
      exact Subgroup.zpow_mem_zpowers τ z
    · intro hx
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hx
      have : x = τ ^ z := by
        rw [← hτP p hp, conj_zpow] at hz
        have := congrArg (fun y => p⁻¹ * y * p) hz
        simpa [mul_assoc] using this.symm
      rw [this]
      exact Subgroup.zpow_mem_zpowers τ z
  have heq := IsSylowTwoOf.eq_of_le hP le_sup_left le_top hsup
  apply hτnot
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)

end CFSG.Quasithin.G64
