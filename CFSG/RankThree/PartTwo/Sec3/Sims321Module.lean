module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

section Module

variable {W : Type*} [CommGroup W] [Finite W]

@[expose] def fixSubgroup (τ : MulAut W) : Subgroup W where
  carrier := {w | τ w = w}
  one_mem' := map_one τ
  mul_mem' {a b} ha hb := by simp_all [map_mul]
  inv_mem' {a} ha := by simp_all [map_inv]

theorem mem_fixSubgroup {τ : MulAut W} {w : W} : w ∈ fixSubgroup τ ↔ τ w = w := Iff.rfl

theorem card_mod_eq_one_of_fpf {r : ℕ} (hr : r.Prime) (φ : MulAut W) (hφ : φ ^ r = 1)
    (hfix : ∀ w, φ w = w → w = 1) : Nat.card W % r = 1 % r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hH : IsPGroup r (Subgroup.zpowers φ) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hφ)
  have hmod := hH.card_modEq_card_fixedPoints W
  have hfp : Nat.card (MulAction.fixedPoints (Subgroup.zpowers φ) W) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have hone : ∀ a : MulAction.fixedPoints (Subgroup.zpowers φ) W, (a : W) = 1 := by
      intro a
      apply hfix
      exact MulAction.mem_fixedPoints.1 a.2 ⟨φ, Subgroup.mem_zpowers φ⟩
    exact ⟨⟨fun a b => Subtype.ext ((hone a).trans (hone b).symm)⟩,
      ⟨⟨1, MulAction.mem_fixedPoints.2 fun m => map_one (m : MulAut W)⟩⟩⟩
  rw [hfp] at hmod
  exact hmod

private theorem card_fixSubgroup_conj (ψ τ : MulAut W) :
    Nat.card (fixSubgroup (ψ * τ * ψ⁻¹)) = Nat.card (fixSubgroup τ) := by
  have h1 : ∀ w : W, w ∈ fixSubgroup (ψ * τ * ψ⁻¹) → ψ⁻¹ w ∈ fixSubgroup τ := by
    intro w hw
    rw [mem_fixSubgroup] at hw ⊢
    have : ψ (τ (ψ⁻¹ w)) = ψ (ψ⁻¹ w) := by simpa using hw
    exact ψ.injective this
  have h2 : ∀ w : W, w ∈ fixSubgroup τ → ψ w ∈ fixSubgroup (ψ * τ * ψ⁻¹) := by
    intro w hw
    rw [mem_fixSubgroup] at hw ⊢
    simp [hw]
  exact Nat.card_congr
    { toFun := fun w => ⟨ψ⁻¹ w.1, h1 w.1 w.2⟩
      invFun := fun w => ⟨ψ w.1, h2 w.1 w.2⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }

theorem card_fixSubgroup_sq (hexp : ∀ w : W, w ^ 2 = 1) {r : ℕ} (hr : Odd r) (φ τ : MulAut W)
    (hφ : φ ^ r = 1) (hfix : ∀ w, φ w = w → w = 1) (hτ : τ ^ 2 = 1)
    (hτφ : τ * φ * τ⁻¹ = φ⁻¹) : Nat.card (fixSubgroup τ) ^ 2 = Nat.card W := by
  have hinv : ∀ w : W, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hexp w)
  have hττ : ∀ w : W, τ (τ w) = w := fun w => by
    simpa [sq] using congrArg (fun e : MulAut W => e w) hτ
  apply le_antisymm
  ·
    obtain ⟨a, rfl⟩ := hr
    set ψ : MulAut W := φ ^ a with hψdef
    have hτψ : τ * ψ * τ⁻¹ = ψ⁻¹ := by
      rw [hψdef, ← inv_pow, ← hτφ, conj_pow]
    have hτψ' : τ * ψ⁻¹ = ψ * τ := by
      have : τ * ψ⁻¹ * τ⁻¹ = ψ := by
        have := congrArg (fun e => e⁻¹) hτψ
        simpa [mul_assoc] using this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have hψψ : ψ⁻¹ * ψ⁻¹ = φ := by
      have h1 : ψ * ψ * φ = 1 := by
        rw [hψdef, ← pow_add, ← pow_succ]
        have : a + a + 1 = 2 * a + 1 := by ring
        rw [this]
        exact hφ
      rw [← mul_inv_rev]
      exact (eq_inv_of_mul_eq_one_right h1).symm
    have hconj : ψ * τ * ψ⁻¹ = τ * φ := by
      rw [← hτψ', mul_assoc, hψψ]
    have hcard : Nat.card (fixSubgroup (τ * φ)) = Nat.card (fixSubgroup τ) := by
      rw [← hconj]
      exact card_fixSubgroup_conj ψ τ
    have hdisj : ∀ w : W, w ∈ fixSubgroup τ → w ∈ fixSubgroup (τ * φ) → w = 1 := by
      intro w h1 h2
      rw [mem_fixSubgroup] at h1 h2
      apply hfix
      have h2' : τ (φ w) = w := h2
      have : φ w = τ w := by
        have := congrArg τ h2'
        rw [hττ] at this
        exact this
      rw [this, h1]
    have hinj : Function.Injective
        (fun p : fixSubgroup τ × fixSubgroup (τ * φ) => ((p.1 : W) * (p.2 : W))) := by
      rintro ⟨⟨c, hc⟩, ⟨k, hk⟩⟩ ⟨⟨c', hc'⟩, ⟨k', hk'⟩⟩ h
      simp only at h
      have hdiv : c / c' = k' / k := by
        rw [div_eq_div_iff_mul_eq_mul, h, mul_comm]
      have hmem1 : c / c' ∈ fixSubgroup τ := (fixSubgroup τ).div_mem hc hc'
      have hmem2 : c / c' ∈ fixSubgroup (τ * φ) :=
        hdiv ▸ (fixSubgroup (τ * φ)).div_mem hk' hk
      have hcc : c = c' := div_eq_one.1 (hdisj _ hmem1 hmem2)
      subst hcc
      have : k = k' := mul_left_cancel h
      subst this
      rfl
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hcard] at this
    rw [sq]
    exact this
  ·
    let f : W →* W := MonoidHom.mk' (fun w => w⁻¹ * τ w) (fun a b => by
      rw [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm])
    have hker : f.ker = fixSubgroup τ := by
      ext w
      simp only [f, MonoidHom.mem_ker, MonoidHom.mk'_apply, mem_fixSubgroup, inv_mul_eq_one]
      exact eq_comm
    have hran : f.range ≤ fixSubgroup τ := by
      rintro _ ⟨w, rfl⟩
      show τ (w⁻¹ * τ w) = w⁻¹ * τ w
      rw [map_mul, map_inv, hττ, hinv (τ w), hinv w, mul_comm]
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hker] at h1
    have h2 : Nat.card f.range ≤ Nat.card (fixSubgroup τ) := Subgroup.card_le_of_le hran
    calc Nat.card W = Nat.card (fixSubgroup τ) * Nat.card f.range := h1.symm
      _ ≤ Nat.card (fixSubgroup τ) * Nat.card (fixSubgroup τ) := Nat.mul_le_mul_left _ h2
      _ = Nat.card (fixSubgroup τ) ^ 2 := (sq _).symm

private theorem two_pow_le_of_dihedral [Nontrivial W] (hexp : ∀ w : W, w ^ 2 = 1) {r k : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hk : orderOf (2 : ZMod r) = k) (hko : Odd k)
    (φ τ : MulAut W) (hφ : φ ^ r = 1) (hfix : ∀ w, φ w = w → w = 1) (hτ : τ ^ 2 = 1)
    (hτφ : τ * φ * τ⁻¹ = φ⁻¹) :
    2 ^ (2 * k) ≤ Nat.card W ∧ 2 ^ k ≤ (fixSubgroup τ).index := by
  have h1 := card_mod_eq_one_of_fpf hr φ hφ hfix
  have h2 := card_fixSubgroup_sq hexp (hr.odd_of_ne_two hr2) φ τ hφ hfix hτ hτφ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : IsPGroup 2 W := fun w => ⟨1, by simpa using hexp w⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp2
  have hC : Nat.card (fixSubgroup τ) ∣ 2 ^ m := hm ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hC
  have hmj : m = 2 * j := by
    have : 2 ^ m = 2 ^ (2 * j) := by rw [← hm, ← h2, hj]; ring
    exact Nat.pow_right_injective (le_refl 2) this
  have hmod : (2 : ZMod r) ^ m = 1 := by
    have := (ZMod.natCast_eq_natCast_iff (2 ^ m) 1 r).2 (by rw [← hm]; exact h1)
    simpa using this
  have hkm : k ∣ m := hk ▸ orderOf_dvd_of_pow_eq_one hmod
  have hkj : k ∣ j := (Odd.coprime_two_right hko).dvd_of_dvd_mul_left (hmj ▸ hkm)
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : Nat.card W = 1 := by simpa using hm
    exact (Finite.one_lt_card (α := W)).ne' this
  have hkj' : k ≤ j := Nat.le_of_dvd (by omega) hkj
  refine ⟨?_, ?_⟩
  · rw [hm, hmj]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · have h3 := Subgroup.card_mul_index (fixSubgroup τ)
    rw [hj, hm, hmj, two_mul, pow_add] at h3
    have hidx : (fixSubgroup τ).index = 2 ^ j := Nat.eq_of_mul_eq_mul_left (by positivity) h3
    rw [hidx]
    exact Nat.pow_le_pow_right (by norm_num) hkj'

end Module

section Restrict

variable {V : Type*} [Group V]

private def stabW (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {γ | ∀ w, w ∈ W ↔ γ w ∈ W}
  one_mem' _ := Iff.rfl
  mul_mem' {a b} ha hb w := (hb w).trans (ha (b w))
  inv_mem' {a} ha w := by
    have := ha (a⁻¹ w)
    rwa [MulAut.apply_inv_self, iff_comm] at this

private def restrictHom (W : Subgroup V) : stabW W →* MulAut W where
  toFun γ :=
    { toFun := fun w => ⟨γ.1 w, (γ.2 w.1).1 w.2⟩
      invFun := fun w => ⟨γ.1⁻¹ w, ((stabW W).inv_mem γ.2 w.1).1 w.2⟩
      left_inv := fun w => Subtype.ext (MulAut.inv_apply_self _ _ _)
      right_inv := fun w => Subtype.ext (MulAut.apply_inv_self _ _ _)
      map_mul' := fun a b => Subtype.ext (map_mul γ.1 (a : V) (b : V)) }
  map_one' := rfl
  map_mul' _ _ := rfl

end Restrict

private theorem core {V : Type*} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {r k : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hk : orderOf (2 : ZMod r) = k) (hko : Odd k)
    (α β : MulAut V) (hα : α ^ r = 1) (hβ : β ^ 2 = 1) (hβα : β * α * β⁻¹ = α⁻¹)
    (hα1 : α ≠ 1) :
    2 ^ (2 * k) ≤ (fixSubgroup α).index ∧ 2 ^ k ≤ (fixSubgroup β).index := by
  have hodd : Odd r := hr.odd_of_ne_two hr2
  let f : V →* V := MonoidHom.mk' (fun v => v⁻¹ * α v) (fun a b => by
    rw [map_mul, mul_inv_rev, mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm])
  have hf : ∀ v, f v = v⁻¹ * α v := fun v => rfl
  let W : Subgroup V := f.range
  have hker : f.ker = fixSubgroup α := by
    ext v
    simp only [f, MonoidHom.mem_ker, MonoidHom.mk'_apply, mem_fixSubgroup, inv_mul_eq_one]
    exact eq_comm
  have hindex : (fixSubgroup α).index = Nat.card W := by
    rw [← hker]
    exact Subgroup.index_ker f
  have hcomm : ∀ γ : MulAut V, γ * α = α * γ → ∀ w ∈ W, γ w ∈ W := by
    rintro γ hγ _ ⟨v, rfl⟩
    refine ⟨γ v, ?_⟩
    have : γ (α v) = α (γ v) := congrArg (fun e : MulAut V => e v) hγ
    simp [hf, map_mul, map_inv, this]
  have hβmul : ∀ v, β (α v) = α⁻¹ (β v) := fun v => by
    have := congrArg (fun e : MulAut V => e (β v)) hβα
    simpa using this
  have hββ : ∀ x, β (β x) = x := fun x => by
    simpa [sq] using congrArg (fun e : MulAut V => e x) hβ
  have hβW : ∀ w ∈ W, β w ∈ W := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(α⁻¹ (β v))⁻¹, ?_⟩
    simp only [hf, map_mul, map_inv, hβmul, inv_inv, MulAut.apply_inv_self]
    exact mul_comm _ _
  have hαS : α ∈ stabW W := fun w =>
    ⟨hcomm α rfl w, fun h => by simpa using hcomm α⁻¹ (by simp) _ h⟩
  have hβS : β ∈ stabW W := fun w => ⟨hβW w, fun h => by simpa [hββ] using hβW _ h⟩
  have hφ' : restrictHom W ⟨α, hαS⟩ ^ r = 1 := by
    rw [← map_pow]
    have : (⟨α, hαS⟩ : stabW W) ^ r = 1 := Subtype.ext (by simpa using hα)
    rw [this, map_one]
  have hτ' : restrictHom W ⟨β, hβS⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨β, hβS⟩ : stabW W) ^ 2 = 1 := Subtype.ext (by simpa using hβ)
    rw [this, map_one]
  have hτφ' : restrictHom W ⟨β, hβS⟩ * restrictHom W ⟨α, hαS⟩ * (restrictHom W ⟨β, hβS⟩)⁻¹ =
      (restrictHom W ⟨α, hαS⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using hβα)
  have hfixφ : ∀ w : W, restrictHom W ⟨α, hαS⟩ w = w → w = 1 := by
    intro w hw
    have hαw : α (w : V) = w := congrArg Subtype.val hw
    obtain ⟨v, hv⟩ := w.2
    have hv' : α v = v * w := by
      rw [← hv, hf]
      simp
    have h1 : ∀ i : ℕ, (α ^ i) v = v * (w : V) ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαw, hv', pow_succ]
        rw [mul_assoc, mul_comm (w : V) ((w : V) ^ i)]
    have h2 : (w : V) ^ r = 1 := by
      have := h1 r
      rw [hα, MulAut.one_apply] at this
      exact mul_left_cancel (a := v) (by rw [mul_one]; exact this.symm)
    obtain ⟨a, ha⟩ := hodd
    have h3 : (w : V) ^ r = w := by
      rw [ha, pow_succ, pow_mul, hV2, one_pow, one_mul]
    exact Subtype.ext (h3.symm.trans h2)
  have hW : Nontrivial W := by
    obtain ⟨v, hv⟩ : ∃ v, α v ≠ v := by
      by_contra h
      exact hα1 (MulEquiv.ext fun v => by_contra fun hv => h ⟨v, hv⟩)
    refine ⟨⟨⟨f v, v, rfl⟩, 1, ?_⟩⟩
    intro h
    apply hv
    have h' : f v = 1 := congrArg Subtype.val h
    exact (inv_mul_eq_one.1 h').symm
  obtain ⟨hA, hB⟩ := two_pow_le_of_dihedral (W := W) (fun w => Subtype.ext (by simpa using hV2 w))
    hr hr2 hk hko _ _ hφ' hfixφ hτ' hτφ'
  refine ⟨hindex ▸ hA, hB.trans ?_⟩
  have hsub : fixSubgroup (restrictHom W ⟨β, hβS⟩) = (fixSubgroup β).subgroupOf W := by
    ext w
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, mem_fixSubgroup]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [hsub]
  have hne : (fixSubgroup β).relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  have := Subgroup.relIndex_le_of_le_right (H := fixSubgroup β) (le_top : W ≤ ⊤) hne
  rw [Subgroup.relIndex_top_right] at this
  exact this

private theorem coe_normalizerMonoidHom_pow {G : Type*} [Group G] (V : Subgroup G)
    (g : Subgroup.normalizer (V : Set G)) (n : ℕ) (v : V) :
    (((V.normalizerMonoidHom g ^ n) v : V) : G) = (g : G) ^ n * v * ((g : G) ^ n)⁻¹ := by
  rw [← map_pow]
  rfl

theorem two_pow_le_relIndex_centralizer {G : Type*} [Group G] [Finite G] {V : Subgroup G}
    (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1) {y s : G}
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (hs : s ∈ Subgroup.normalizer (V : Set G))
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hk : orderOf (2 : ZMod r) = k) (hko : Odd k)
    (hyr : ∀ v ∈ V, y ^ r * v * (y ^ r)⁻¹ = v) (hs2 : ∀ v ∈ V, s ^ 2 * v * (s ^ 2)⁻¹ = v)
    (hsy : ∀ v ∈ V, (s * y * s⁻¹) * v * (s * y * s⁻¹)⁻¹ = y⁻¹ * v * y)
    (hy1 : ∃ v ∈ V, y * v * y⁻¹ ≠ v) :
    2 ^ (2 * k) ≤ (V ⊓ Subgroup.centralizer ({y} : Set G)).relIndex V ∧
      2 ^ k ≤ (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V := by
  letI : CommGroup V :=
    { (inferInstance : Group V) with mul_comm := fun a b => Subtype.ext (hVc a a.2 b b.2) }
  have hrel : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (V : Set G)),
      (V ⊓ Subgroup.centralizer ({g} : Set G)).relIndex V =
        (fixSubgroup (V.normalizerMonoidHom ⟨g, hg⟩)).index := by
    intro g hg
    show ((V ⊓ Subgroup.centralizer ({g} : Set G)).subgroupOf V).index = _
    congr 1
    ext v
    rw [Subgroup.mem_subgroupOf, mem_fixSubgroup, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show g * v * g⁻¹ = v
      rw [mul_inv_eq_iff_eq_mul]
      exact h.symm
    · intro h
      refine ⟨v.2, ?_⟩
      have : g * v * g⁻¹ = v := congrArg Subtype.val h
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
  have hαr : V.normalizerMonoidHom ⟨y, hy⟩ ^ r = 1 := by
    ext v
    rw [coe_normalizerMonoidHom_pow]
    exact hyr v v.2
  have hβ2 : V.normalizerMonoidHom ⟨s, hs⟩ ^ 2 = 1 := by
    ext v
    rw [coe_normalizerMonoidHom_pow]
    exact hs2 v v.2
  have hβα : V.normalizerMonoidHom ⟨s, hs⟩ * V.normalizerMonoidHom ⟨y, hy⟩ *
      (V.normalizerMonoidHom ⟨s, hs⟩)⁻¹ = (V.normalizerMonoidHom ⟨y, hy⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    ext v
    show (s * y * s⁻¹) * v * (s * y * s⁻¹)⁻¹ = y⁻¹ * v * (y⁻¹)⁻¹
    rw [hsy v v.2, inv_inv]
  have hα1 : V.normalizerMonoidHom ⟨y, hy⟩ ≠ 1 := by
    obtain ⟨v, hv, hne⟩ := hy1
    intro h
    exact hne (congrArg (fun e : MulAut V => ((e ⟨v, hv⟩ : V) : G)) h)
  have hV2' : ∀ v : V, v ^ 2 = 1 := fun v => Subtype.ext (by
    show (v : G) ^ 2 = 1
    rw [sq]
    exact hV2 v v.2)
  rw [hrel y hy, hrel s hs]
  exact core hV2' hr hr2 hk hko _ _ hαr hβ2 hβα hα1

end CFSG.RankThree.PartTwo.Sec3.Sims321
