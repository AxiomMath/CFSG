module

public import CFSG.Monster.GMS.Extraspecial
public import CFSG.Monster.GMS.Facts.Co1Module
public import CFSG.Monster.GMS.TwoCentral
public import CFSG.Sporadic.Co1

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section Abstract

variable {H : Type} [Group H] (P : Subgroup H) [P.Normal]

private noncomputable def conjAdd (g : H) :
    Additive (Abelianization P) →+ Additive (Abelianization P) :=
  MonoidHom.toAdditive (Abelianization.map (MulAut.conjNormal (H := P) g).toMonoidHom)

omit [P.Normal] in
private theorem exists_of (v : Additive (Abelianization P)) :
    ∃ x : P, Additive.ofMul (Abelianization.of x) = v := by
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective v.toMul
  refine ⟨q, ?_⟩
  change Additive.ofMul (QuotientGroup.mk q : Abelianization P) = v
  rw [hq]
  rfl

private theorem mulAut_apply_eq_of_mem_center {Q : Type*} [Group Q]
    (hcard : Nat.card (Subgroup.center Q) = 2) (ψ : MulAut Q) {a : Q}
    (ha : a ∈ Subgroup.center Q) : ψ a = a := by
  have hψa : ψ a ∈ Subgroup.center Q := Subgroup.mem_center_iff.mpr fun r => by
    obtain ⟨s, rfl⟩ := ψ.surjective r
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha s]
  by_cases h1 : a = 1
  · rw [h1, map_one]
  · have hne : (⟨ψ a, hψa⟩ : Subgroup.center Q) ≠ 1 := fun h => h1 (ψ.injective
      ((congrArg Subtype.val h).trans (map_one ψ).symm))
    have hne' : (⟨a, ha⟩ : Subgroup.center Q) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q)).1 hcard
    exact congrArg Subtype.val ((hy _ hne).trans (hy _ hne').symm)

theorem exists_vec_of_extraspecial
    (h13 : Co1ModuleUniqueness) [Finite H]
    (hP : IsExtraspecialPGroup 2 P) (hcard : Nat.card P = 2 ^ 25)
    (hcent : Subgroup.centralizer (P : Set H) ≤ P) (φ : H →* Co1) (hφs : Function.Surjective φ)
    (hφk : φ.ker = P) :
    ∃ v : P → Fin 24 → ZMod 2, (∀ x y, v (x * y) = v x + v y) ∧
      (∀ x, v x = 0 ↔ x ∈ Subgroup.center P) ∧
      (∀ (c : H) (x : P), v (MulAut.conjNormal c x) = co1Act (φ c) (v x)) ∧
      Function.Surjective v := by
  classical
  have hc : commutator P = Subgroup.center P := hP.2.1
  have hfr : frattini P = Subgroup.center P := hP.2.2.1
  have hZcard : Nat.card (Subgroup.center P) = 2 := hP.2.2.2
  have hfin : Fact (IsPGroup 2 P) := ⟨hP.1⟩
  have hsq : ∀ v : Additive (Abelianization P), (2 : ℕ) • v = 0 := by
    intro v
    obtain ⟨x, rfl⟩ := exists_of P v
    rw [← ofMul_pow, ← map_pow]
    have hx : x ^ 2 ∈ commutator P := by
      rw [hc, ← hfr]
      exact CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) x
    rw [← Abelianization.ker_of] at hx
    rw [MonoidHom.mem_ker.1 hx]
    rfl
  let _inst : Module (ZMod 2) (Additive (Abelianization P)) := AddCommGroup.zmodModule hsq
  let π : P → Additive (Abelianization P) := fun x => Additive.ofMul (Abelianization.of x)
  have hπmul : ∀ x y, π (x * y) = π x + π y := fun x y => by
    simp only [π, map_mul, ofMul_mul]
  have hπeq : ∀ x y, π x = π y ↔ x⁻¹ * y ∈ Subgroup.center P := by
    intro x y
    rw [← hc]
    constructor
    · intro h
      exact QuotientGroup.eq.1 (Additive.ofMul.injective h)
    · intro h
      exact congrArg Additive.ofMul (QuotientGroup.eq.2 h)
  have hπsurj : Function.Surjective π := fun v => exists_of P v
  have hπ1 : π 1 = 0 := by simp [π]
  have hπ0 : ∀ x, π x = 0 ↔ x ∈ Subgroup.center P := by
    intro x
    rw [← hπ1, hπeq, mul_one, inv_mem_iff]
  let conjEnd : H →* Module.End (ZMod 2) (Additive (Abelianization P)) :=
    { toFun := fun g => (conjAdd P g).toZModLinearMap 2
      map_one' := by
        refine LinearMap.ext fun v => ?_
        obtain ⟨q, rfl⟩ := exists_of P v
        change Additive.ofMul (Abelianization.of (MulAut.conjNormal (1 : H) q)) = _
        rw [map_one]
        rfl
      map_mul' := fun g g' => by
        refine LinearMap.ext fun v => ?_
        obtain ⟨q, rfl⟩ := exists_of P v
        change Additive.ofMul (Abelianization.of (MulAut.conjNormal (g * g') q)) =
          Additive.ofMul (Abelianization.of (MulAut.conjNormal g (MulAut.conjNormal g' q)))
        rw [map_mul]
        rfl }
  have hconjEnd : ∀ (g : H) (x : P), conjEnd g (π x) = π (MulAut.conjNormal g x) :=
    fun g x => rfl
  have hker : φ.ker ≤ conjEnd.toHomUnits.ker := by
    intro g hg
    rw [hφk] at hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := exists_of P v
    show conjEnd g (π x) = π x
    rw [hconjEnd]
    have hgx : MulAut.conjNormal g x = (⟨g, hg⟩ : P) * x * (⟨g, hg⟩ : P)⁻¹ :=
      Subtype.ext (by simp [MulAut.conjNormal_apply])
    rw [hgx, hπmul, hπmul]
    have h0 : π (⟨g, hg⟩ : P) + π (⟨g, hg⟩ : P)⁻¹ = 0 := by
      rw [← hπmul, mul_inv_cancel, hπ1]
    calc π (⟨g, hg⟩ : P) + π x + π (⟨g, hg⟩ : P)⁻¹
        = π x + (π (⟨g, hg⟩ : P) + π (⟨g, hg⟩ : P)⁻¹) := by abel
      _ = π x := by rw [h0, add_zero]
  let ρGL : Co1 →* (Module.End (ZMod 2) (Additive (Abelianization P)))ˣ :=
    (MonoidHom.liftOfSurjective φ hφs) ⟨conjEnd.toHomUnits, hker⟩
  let ρ : Representation (ZMod 2) Co1 (Additive (Abelianization P)) :=
    (Units.coeHom _).comp ρGL
  have hρ : ∀ (c : H) (v : Additive (Abelianization P)), ρ (φ c) v = conjEnd c v := by
    intro c v
    have h := MonoidHom.liftOfRightInverse_comp_apply φ (Function.surjInv hφs)
      (Function.rightInverse_surjInv hφs) ⟨conjEnd.toHomUnits, hker⟩ c
    show ((ρGL (φ c) : (Module.End (ZMod 2) (Additive (Abelianization P)))ˣ) :
      Module.End (ZMod 2) (Additive (Abelianization P))) v = _
    rw [show ρGL (φ c) = conjEnd.toHomUnits c from h]
    rfl
  have hρ1 : ρ ≠ 1 := by
    intro hρ1
    have hsqP : ∀ c : H, c * c ∈ P := by
      intro c
      apply hcent
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hc1 : ∀ y : P, π (MulAut.conjNormal c y) = π y := by
        intro y
        have h := congrArg (fun r : Representation (ZMod 2) Co1 (Additive (Abelianization P)) =>
          r (φ c) (π y)) hρ1
        simp only [hρ, hconjEnd] at h
        exact h
      have hcc : ∀ y : P, MulAut.conjNormal c (MulAut.conjNormal c y) = y := by
        intro y
        have hd : y⁻¹ * MulAut.conjNormal c y ∈ Subgroup.center P :=
          (hπeq _ _).1 (hc1 y).symm
        set d : P := y⁻¹ * MulAut.conjNormal c y with hd_def
        have hd2 : d * d = 1 := by
          have h2 : (⟨d, hd⟩ : Subgroup.center P) ^ 2 = 1 := by
            rw [← hZcard]
            exact pow_card_eq_one'
          have := congrArg (fun a : Subgroup.center P => ((a : P))) h2
          simpa [pow_two] using this
        have hfix : MulAut.conjNormal c d = d := mulAut_apply_eq_of_mem_center hZcard _ hd
        have hy' : MulAut.conjNormal c y = y * d := by rw [hd_def]; group
        calc MulAut.conjNormal c (MulAut.conjNormal c y)
            = MulAut.conjNormal c (y * d) := by rw [← hy']
          _ = MulAut.conjNormal c y * MulAut.conjNormal c d := map_mul _ _ _
          _ = (y * d) * d := by rw [hfix, hy']
          _ = y := by rw [mul_assoc, hd2, mul_one]
      have h1 := congrArg Subtype.val (hcc ⟨q, hq⟩)
      simp only [MulAut.conjNormal_apply] at h1
      calc q * (c * c) = (c * (c * q * c⁻¹) * c⁻¹) * (c * c) := by rw [h1]
        _ = (c * c) * q := by group
    have hsq1 : ∀ g : Co1, g * g = 1 := by
      intro g
      obtain ⟨c, rfl⟩ := hφs g
      rw [← map_mul, ← MonoidHom.mem_ker, hφk]
      exact hsqP c
    have hpg : IsPGroup 2 Co1 := fun g => ⟨1, by simpa [pow_two] using hsq1 g⟩
    have hfinCo1 : Finite Co1 := Nat.finite_of_card_ne_zero (by
      rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hpg
    rw [CFSG.Sporadic.Co1.card_Co1] at hn
    have h3 : (3 : ℕ) ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hfin24 : Module.finrank (ZMod 2) (Additive (Abelianization P)) = 24 := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 (Additive (Abelianization P))
    have hV : Nat.card (Additive (Abelianization P)) = 2 ^ 24 := by
      have e1 : Nat.card (Additive (Abelianization P)) = Nat.card (Abelianization P) :=
        Nat.card_congr Additive.toMul
      have e2 : Nat.card P = Nat.card (P ⧸ commutator P) * Nat.card (commutator P) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      have e3 : Nat.card (Abelianization P) = Nat.card (P ⧸ commutator P) := rfl
      have e4 : Nat.card (commutator P) = 2 := by rw [hc]; exact hZcard
      rw [e1, e3]
      rw [e4, hcard] at e2
      omega
    rw [hV] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  obtain ⟨ψ, hψ⟩ := h13 (Additive (Abelianization P)) hfin24 ρ hρ1
  refine ⟨fun x => ψ (π x), fun x y => ?_, fun x => ?_, fun c x => ?_, ?_⟩
  · simp only [hπmul, map_add]
  · rw [map_eq_zero_iff _ ψ.injective, hπ0]
  · have h := hψ (φ c) (π x)
    rw [hρ, hconjEnd] at h
    exact h
  · exact ψ.surjective.comp hπsurj

end Abstract

section System

variable {G : Type*} [Group G]

theorem mem_zpowers_iff_of_orderOf_two {z g : G} (hz : orderOf z = 2) :
    g ∈ Subgroup.zpowers z ↔ g = 1 ∨ g = z := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← zpow_mod_orderOf, hz]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; simp [h]
    · right; simp [h]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

structure LeechSystem (z : G) where
  φ : Subgroup.centralizer ({z} : Set G) →* Co1
  φ_surj : Function.Surjective φ
  φ_ker : ∀ c : Subgroup.centralizer ({z} : Set G), φ c = 1 ↔ (c : G) ∈ leechQ z
  extraspecial : ExtraspecialData (leechQ z) z
  center_eq : ∀ q ∈ leechQ z, (∀ p ∈ leechQ z, p * q = q * p) → q = 1 ∨ q = z
  vec : G → Fin 24 → ZMod 2
  vec_mul : ∀ p ∈ leechQ z, ∀ q ∈ leechQ z, vec (p * q) = vec p + vec q
  vec_eq_zero : ∀ q ∈ leechQ z, (vec q = 0 ↔ q = 1 ∨ q = z)
  vec_conj : ∀ (c : Subgroup.centralizer ({z} : Set G)), ∀ q ∈ leechQ z,
    vec ((c : G) * q * (c : G)⁻¹) = co1Act (φ c) (vec q)
  vec_surj : ∀ w : Fin 24 → ZMod 2, ∃ q ∈ leechQ z, vec q = w

theorem exists_leechSystem
    (h13 : Co1ModuleUniqueness) {G : Type} [Group G] [Finite G] {z : G}
    (h : GMSLeechCentralizer z) : Nonempty (LeechSystem z) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  set P : Subgroup C := CFSG.pCore 2 C with hP
  have hext := h.extraspecialData
  have hz2 : orderOf z = 2 := h.1
  have hQ : IsExtraspecialPGroup 2 P := h.2.1
  have hcard : Nat.card P = 2 ^ 25 := h.2.2.1
  have hcent : Subgroup.centralizer (P : Set C) ≤ P := h.2.2.2.2
  obtain ⟨φ, hφs, hφk⟩ := h.2.2.2.1
  obtain ⟨v, hv1, hv2, hv3, hv4⟩ := exists_vec_of_extraspecial P h13 hQ hcard hcent φ hφs hφk
  let ι : P → G := fun x => ((x : C) : G)
  have hι_inj : Function.Injective ι := fun x y hxy => Subtype.ext (Subtype.ext hxy)
  have hmemQ : ∀ g, g ∈ leechQ z ↔ ∃ x : P, ι x = g := by
    intro g
    constructor
    · intro hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
  have hcenter : ∀ x : P, x ∈ Subgroup.center P ↔ ι x = 1 ∨ ι x = z := by
    intro x
    rw [← mem_zpowers_iff_of_orderOf_two hz2, ← center_pCore_map_eq_zpowers hz2 hQ hcent]
    constructor
    · intro hx
      exact ⟨(x : C), ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨w, hw, rfl⟩, hy⟩
      have : w = x := hι_inj hy
      rw [← this]
      exact hw
  let vec : G → Fin 24 → ZMod 2 := fun g =>
    if hg : g ∈ leechQ z then v (Classical.choose ((hmemQ g).1 hg)) else 0
  have hvec : ∀ x : P, vec (ι x) = v x := by
    intro x
    have hg : ι x ∈ leechQ z := (hmemQ _).2 ⟨x, rfl⟩
    simp only [vec, hg, ↓reduceDIte]
    congr 1
    exact hι_inj (Classical.choose_spec ((hmemQ _).1 hg))
  refine ⟨⟨φ, hφs, ?_, hext, ?_, vec, ?_, ?_, ?_, ?_⟩⟩
  · intro c
    rw [← MonoidHom.mem_ker, hφk, hmemQ]
    constructor
    · intro hc
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨x, hx⟩
      have : (x : C) = c := Subtype.ext hx
      rw [← this]
      exact x.2
  · intro q hq hcomm
    obtain ⟨x, rfl⟩ := (hmemQ q).1 hq
    refine (hcenter x).1 (Subgroup.mem_center_iff.mpr fun y => ?_)
    exact Subtype.ext (Subtype.ext (hcomm (ι y) ((hmemQ _).2 ⟨y, rfl⟩)))
  · intro p hp q hq
    obtain ⟨x, rfl⟩ := (hmemQ p).1 hp
    obtain ⟨y, rfl⟩ := (hmemQ q).1 hq
    have : ι x * ι y = ι (x * y) := rfl
    rw [this, hvec, hvec, hvec, hv1]
  · intro q hq
    obtain ⟨x, rfl⟩ := (hmemQ q).1 hq
    rw [hvec, hv2, hcenter]
  · intro c q hq
    obtain ⟨x, rfl⟩ := (hmemQ q).1 hq
    have : (c : G) * ι x * (c : G)⁻¹ = ι (MulAut.conjNormal c x) := by
      simp [ι, MulAut.conjNormal_apply]
    rw [this, hvec, hv3, hvec]
  · intro w
    obtain ⟨x, hx⟩ := hv4 w
    exact ⟨ι x, (hmemQ _).2 ⟨x, rfl⟩, by rw [hvec, hx]⟩

end System

end CFSG.Monster.GMS
