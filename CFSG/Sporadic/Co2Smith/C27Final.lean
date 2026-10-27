module

public import CFSG.Sporadic.Co2Smith.CBound

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open Subgroup

universe u

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type u} [Group G] [Finite G] {z : G}

abbrev EG (z : G) : Subgroup G :=
  (CFSG.pCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype

omit [Finite G] in
theorem mem_EG {x : G} : x ∈ EG z ↔
    ∃ hx : x ∈ centralizer ({z} : Set G),
      (⟨x, hx⟩ : centralizer ({z} : Set G)) ∈ CFSG.pCore 2 (centralizer ({z} : Set G)) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨_, h, rfl⟩

abbrev D0G (z g : G) : Subgroup G :=
  (EG z).map (MulAut.conj g⁻¹).toMonoidHom ⊓ centralizer ({z} : Set G)

omit [Finite G] in
theorem mem_D0G {g y : G} : y ∈ D0G z g ↔ g * y * g⁻¹ ∈ EG z ∧ y ∈ centralizer ({z} : Set G) := by
  rw [Subgroup.mem_inf, mem_map_conj_inv]

theorem conj_not_mem_EG
    (hc : CCFacts) (hG : SmithHyp G z) (φ : centralizer ({z} : Set G) ≃* Cz) {g : G}
    (hs : g * z * g⁻¹ ≠ z) (h : g * z * g⁻¹ ∈ EG z) : False := by
  obtain ⟨hsH, hsE⟩ := mem_EG.mp h
  have hsH' : (g⁻¹)⁻¹ * z * g⁻¹ ∈ centralizer ({z} : Set G) := by rwa [inv_inv]
  have := smith_2_2 hc hG φ g⁻¹ hsH' (by convert hsE using 2; simp)
  exact hs (by rwa [inv_inv] at this)

omit [Finite G] in
theorem EG_conj {h e : G} (hh : h ∈ centralizer ({z} : Set G)) (he : e ∈ EG z) :
    h * e * h⁻¹ ∈ EG z := by
  obtain ⟨heH, heE⟩ := mem_EG.mp he
  refine mem_EG.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hh heH) (Subgroup.inv_mem _ hh), ?_⟩
  have := (CFSG.pCore_normal (p := 2) (G := centralizer ({z} : Set G))).conj_mem _ heE ⟨h, hh⟩
  convert this using 1

theorem D1_normal :
    ∀ x ∈ XC 1, ∀ d ∈ D1, x * d * x⁻¹ ∈ D1 := by
  intro x hx d hd
  have h1 : Commute x (cR 1) := mem_centralizer_singleton_iff.mp hx
  have h2 : Commute d (cR 1) := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).1
  exact Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
    ((h1.mul_left h2).mul_left h1.inv_left).eq,
    (CFSG.pCore_normal (p := 2) (G := Cz)).conj_mem _ (Subgroup.mem_inf.mp hd).2 x⟩

omit [Finite G] in
theorem card_D0G (φ : centralizer ({z} : Set G) ≃* Cz) {g : G}
    (hs : g * z * g⁻¹ ∈ centralizer ({z} : Set G)) :
    Nat.card (D0G z g) = ceInv (φ ⟨_, hs⟩) := by
  unfold ceInv
  set s : centralizer ({z} : Set G) := ⟨_, hs⟩
  have e1 : D0G z g ≃ {q : CFSG.pCore 2 (centralizer ({z} : Set G)) //
      (q : centralizer ({z} : Set G)) * s = s * q} :=
    { toFun := fun y => ⟨⟨⟨g * y * g⁻¹, (mem_EG.mp (mem_D0G.mp y.2).1).1⟩,
          (mem_EG.mp (mem_D0G.mp y.2).1).2⟩, Subtype.ext (by
          show g * (y : G) * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * y * g⁻¹)
          have hc' : (y : G) * z = z * y :=
            mem_centralizer_singleton_iff.mp (mem_D0G.mp y.2).2
          calc g * (y : G) * g⁻¹ * (g * z * g⁻¹) = g * ((y : G) * z) * g⁻¹ := by group
            _ = g * (z * y) * g⁻¹ := by rw [hc']
            _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group)⟩
      invFun := fun q => ⟨g⁻¹ * ((q : centralizer ({z} : Set G)) : G) * g, mem_D0G.mpr
        ⟨by
          rw [show g * (g⁻¹ * ((q : centralizer ({z} : Set G)) : G) * g) * g⁻¹ =
            ((q : centralizer ({z} : Set G)) : G) by group]
          exact mem_EG.mpr ⟨_, q.1.2⟩,
        by
          rw [mem_centralizer_singleton_iff]
          have hq := congrArg Subtype.val q.2
          simp only [Subgroup.coe_mul, s] at hq
          calc g⁻¹ * ((q : centralizer ({z} : Set G)) : G) * g * z =
              g⁻¹ * (((q : centralizer ({z} : Set G)) : G) * (g * z * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * z * g⁻¹) * ((q : centralizer ({z} : Set G)) : G)) * g := by
                rw [hq]
            _ = z * (g⁻¹ * ((q : centralizer ({z} : Set G)) : G) * g) := by group⟩⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun q => Subtype.ext (Subtype.ext (Subtype.ext (by simp [mul_assoc]))) }
  have e2 : {q : CFSG.pCore 2 (centralizer ({z} : Set G)) //
      (q : centralizer ({z} : Set G)) * s = s * q} ≃
      {q : CFSG.pCore 2 Cz // (q : Cz) * φ s = φ s * q} :=
    { toFun := fun q => ⟨⟨φ q, apply_mem_pCore_two φ q.1.2⟩, by
        show φ q * φ s = φ s * φ q
        rw [← map_mul, ← map_mul, q.2]⟩
      invFun := fun q => ⟨⟨φ.symm q, symm_apply_mem_pCore_two φ q.1.2⟩, by
        apply φ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact q.2⟩
      left_inv := fun q => Subtype.ext (Subtype.ext (by simp))
      right_inv := fun q => Subtype.ext (Subtype.ext (by simp)) }
  exact Nat.card_congr (e1.trans e2)

theorem exists_mul_of_card_le {D D₀ A : Subgroup G} (hDD₀ : D ⊓ D₀ = ⊥)
    (hmem : ∀ d ∈ D, ∀ y ∈ D₀, d * y ∈ A) (hA : Nat.card A ≤ Nat.card D * Nat.card D₀)
    {a : G} (ha : a ∈ A) : ∃ d ∈ D, ∃ y ∈ D₀, d * y = a := by
  let μ : D × D₀ → A := fun p => ⟨p.1 * p.2, hmem _ p.1.2 _ p.2.2⟩
  have hinj : Function.Injective μ := by
    rintro ⟨⟨d, hd⟩, ⟨y, hy⟩⟩ ⟨⟨d', hd'⟩, ⟨y', hy'⟩⟩ h
    have h' : d * y = d' * y' := congrArg Subtype.val h
    have h2 : d'⁻¹ * d = y' * y⁻¹ := by
      calc d'⁻¹ * d = d'⁻¹ * (d * y) * y⁻¹ := by group
        _ = d'⁻¹ * (d' * y') * y⁻¹ := by rw [h']
        _ = y' * y⁻¹ := by group
    have h3 : d'⁻¹ * d ∈ D ⊓ D₀ := Subgroup.mem_inf.mpr
      ⟨D.mul_mem (D.inv_mem hd') hd, h2 ▸ D₀.mul_mem hy' (D₀.inv_mem hy)⟩
    rw [hDD₀, Subgroup.mem_bot, inv_mul_eq_one] at h3
    subst h3
    obtain rfl : y = y' := mul_left_cancel h'
    rfl
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod]; exact hA)
  obtain ⟨⟨⟨d, hd⟩, ⟨y, hy⟩⟩, hp⟩ := hbij.2 ⟨a, ha⟩
  exact ⟨d, hd, y, hy, congrArg Subtype.val hp⟩

theorem false_of_first
    (hc : CCFacts) (hG : SmithHyp G z) (φ : centralizer ({z} : Set G) ≃* Cz)
    (hA : ∀ g : G, ∀ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G), ∀ h : Cz,
      h * φ ⟨_, ht⟩ * h⁻¹ ≠ cR 5)
    {g : G} (ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G)) (hte : g⁻¹ * z * g ≠ z)
    {t₁ : G} (ht₁H : t₁ ∈ centralizer ({z} : Set G)) (hφt : φ ⟨t₁, ht₁H⟩ = cR 1)
    (hX : cent2 z t₁ = cent2 z (g⁻¹ * z * g))
    (hinvt : invEInv (φ ⟨_, ht⟩) = 32) : False := by
  have hz2 := hG.orderOf_eq
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have hφz := φ_zC hc hG φ
  have hιt : ιM φ (cR 1) = t₁ := by rw [← hφt, ιM_φ]
  have hXm : cent2 z t₁ = (XC 1).map (ιM φ) := by rw [← hιt]; exact cent2_eq_map φ (cR 1)
  have hXmem : ∀ x ∈ cent2 z t₁, x ∈ centralizer ({z} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (mem_cent2.mp hx).1
  set D := D1.map (ιM φ) with hD
  set D₀ := D0G z g with hD₀
  have hDX : D ≤ cent2 z t₁ := by
    rw [hXm]
    exact Subgroup.map_mono inf_le_left
  have hDE : ∀ d ∈ D, d ∈ EG z := by
    rintro _ ⟨d, hd, rfl⟩
    exact mem_EG.mpr ⟨ιM_mem φ d, symm_apply_mem_pCore_two φ (Subgroup.mem_inf.mp hd).2⟩
  have hXD : ∀ x ∈ cent2 z t₁, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro x hx d hd
    rw [hXm] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨d', hd', rfl⟩ := hd
    exact ⟨x' * d' * x'⁻¹, D1_normal x' hx' d' hd', by rw [map_mul, map_mul, map_inv]⟩
  have hD₀X : D₀ ≤ cent2 z t₁ := by
    intro y hy
    obtain ⟨hyE, hyH⟩ := mem_D0G.mp hy
    rw [hX, mem_cent2]
    refine ⟨mem_centralizer_singleton_iff.mp hyH, ?_⟩
    have hc' : g * y * g⁻¹ * z = z * (g * y * g⁻¹) :=
      mem_centralizer_singleton_iff.mp (mem_EG.mp hyE).1
    calc y * (g⁻¹ * z * g) = g⁻¹ * ((g * y * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [hc']
      _ = g⁻¹ * z * g * y := by group
  have hXD₀ : ∀ x ∈ cent2 z t₁, ∀ y ∈ D₀, x * y * x⁻¹ ∈ D₀ := by
    intro x hx y hy
    obtain ⟨hyE, hyH⟩ := mem_D0G.mp hy
    have hxH := hXmem x hx
    rw [hX, mem_cent2] at hx
    have hgx : g * x * g⁻¹ ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [hx.2]
        _ = z * (g * x * g⁻¹) := by group
    refine mem_D0G.mpr ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hxH hyH)
      (Subgroup.inv_mem _ hxH)⟩
    have := EG_conj hgx hyE
    rwa [show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ by
      group] at this
  have hzD₀ : z ∉ D₀ := by
    intro h
    refine conj_not_mem_EG hc hG φ (g := g) (fun e => hte ?_) (mem_D0G.mp h).1
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [e]
      _ = z := by group
  have hDD₀ : D ⊓ D₀ = ⊥ := by
    by_contra hne
    set N := (D ⊓ D₀).comap (ιM φ)
    have hND : N ≤ D1 := by
      intro n hn
      obtain ⟨n', hn', e⟩ := (Subgroup.mem_inf.mp hn).1
      rwa [ιM_injective φ e] at hn'
    have hNX : ∀ x ∈ XC 1, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
      intro x hx n hn
      have hx' : ιM φ x ∈ cent2 z t₁ := by rw [hXm]; exact ⟨x, hx, rfl⟩
      show ιM φ (x * n * x⁻¹) ∈ D ⊓ D₀
      rw [map_mul, map_mul, map_inv]
      exact Subgroup.mem_inf.mpr ⟨hXD _ hx' _ (Subgroup.mem_inf.mp hn).1,
        hXD₀ _ hx' _ (Subgroup.mem_inf.mp hn).2⟩
    have hN1 : N ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨a', -, rfl⟩ := (Subgroup.mem_inf.mp ha).1
      have : a' ∈ N := ha
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot, this, map_one]
    have := c1_hmin hc N hND hNX hN1
    have hzN : ιM φ zCz ∈ D ⊓ D₀ := this
    rw [ιM_zM φ hφz] at hzN
    exact hzD₀ (Subgroup.mem_inf.mp hzN).2
  have hcomm : ∀ d ∈ D, ∀ y ∈ D₀, d * y = y * d := by
    intro d hd y hy
    have h1 : d * y * d⁻¹ * y⁻¹ ∈ D := by
      rw [show d * y * d⁻¹ * y⁻¹ = d * (y * d⁻¹ * y⁻¹) by group]
      exact D.mul_mem hd (hXD y (hD₀X hy) d⁻¹ (D.inv_mem hd))
    have h2 : d * y * d⁻¹ * y⁻¹ ∈ D₀ := D₀.mul_mem (hXD₀ d (hDX hd) y hy) (D₀.inv_mem hy)
    have h3 : d * y * d⁻¹ * y⁻¹ ∈ D ⊓ D₀ := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hDD₀, Subgroup.mem_bot] at h3
    calc d * y = (d * y * d⁻¹ * y⁻¹) * (y * d) := by group
      _ = y * d := by rw [h3, one_mul]
  have hcardD : Nat.card D = 32 := by
    rw [hD, Subgroup.card_map_of_injective (ιM_injective φ), natCard_D1 hc]
  have hsH : (g⁻¹)⁻¹ * z * g⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [inv_inv]
    exact conj_mem_centralizer ht
  have hsz : (g⁻¹)⁻¹ * z * g⁻¹ ≠ z := fun e => hte (by
    rw [inv_inv] at e
    calc g⁻¹ * z * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [e]
      _ = z := by group)
  have hs' : g * z * g⁻¹ ∈ centralizer ({z} : Set G) := conj_mem_centralizer ht
  have hφs : φ ⟨_, hsH⟩ = φ ⟨_, hs'⟩ := congrArg φ (Subtype.ext (by simp))
  have hce : ceInv (φ ⟨_, hsH⟩) = 32 := by
    rcases smith_conj_classes hc hG φ g⁻¹ hsH with h1 | ⟨i, hi, h, hh⟩
    · exact absurd h1 hsz
    have hi5 : i ≠ 5 := fun e => hA g⁻¹ hsH h (by rw [hh, e]; rfl)
    have hk' : ∀ i : Fin 9, i ∈ ({1, 2, 5} : Finset (Fin 9)) → i ≠ 5 →
        Native.ccCE[(i : ℕ)]! = 32 := by decide
    rw [← ceInv_conj h, hh, hc.ce i]
    exact hk' i hi hi5
  have hcardD₀ : Nat.card D₀ = 32 := by
    rw [hD₀, card_D0G φ hs', ← hφs, hce]
  have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, D1_comm hc a ha b hb]
  set CXD := centralizer (D : Set G) ⊓ cent2 z t₁ with hCXD
  have hCXDm : CXD = (centralizer (D1 : Set Cz) ⊓ XC 1).map (ιM φ) := by
    rw [hCXD, hXm, hD, centralizer_map_eq]
  have hcardCXD : Nat.card CXD ≤ Nat.card D * Nat.card D₀ := by
    rw [hcardD, hcardD₀, hCXDm, Subgroup.card_map_of_injective (ιM_injective φ)]
    exact (c1_cxd_card hc).trans (by norm_num)
  have hmemCXD : ∀ d ∈ D, ∀ y ∈ D₀, d * y ∈ CXD := by
    intro d hd y hy
    refine Subgroup.mem_inf.mpr ⟨mem_centralizer_iff.mpr fun b hb => ?_,
      (cent2 z t₁).mul_mem (hDX hd) (hD₀X hy)⟩
    rw [← mul_assoc, hDab b hb d hd, mul_assoc, hcomm b hb y hy, ← mul_assoc]
  obtain ⟨j, hjC, hj80⟩ := c1_j hc
  have hjG : ιM φ j ∈ CXD := by rw [hCXDm]; exact ⟨j, hjC, rfl⟩
  obtain ⟨_, ⟨d, hd, rfl⟩, y, hy, hdy⟩ := exists_mul_of_card_le hDD₀ hmemCXD hcardCXD hjG
  obtain ⟨hyE, hyH⟩ := mem_D0G.mp hy
  have hφy : φ ⟨y, hyH⟩ = d⁻¹ * j := by
    apply ιM_injective φ
    rw [ιM_φ, map_mul, map_inv, ← hdy]
    group
  have hdC : d ∈ centralizer (D1 : Set Cz) ⊓ XC 1 :=
    Subgroup.mem_inf.mpr ⟨mem_centralizer_iff.mpr fun b hb => D1_comm hc b hb d hd,
      (Subgroup.mem_inf.mp hd).1⟩
  have hyC : φ ⟨y, hyH⟩ ∈ centralizer (D1 : Set Cz) ⊓ XC 1 := by
    rw [hφy]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hdC) hjC
  have hy80 : invEInv (φ ⟨y, hyH⟩) = 80 := by
    rw [hφy, invEInv_mul_pCore (Subgroup.inv_mem _ (Subgroup.mem_inf.mp hd).2) j, hj80]
  have hyy : φ ⟨y, hyH⟩ * φ ⟨y, hyH⟩ = 1 := c1_cxd_sq hc _ hyC
  obtain ⟨k, hk, h, hh⟩ := second_of_invE hc hyy hy80
  obtain ⟨heH, heE⟩ := mem_EG.mp hyE
  have hyy' : y * y = 1 := by
    have := congrArg (ιM φ) hyy
    rwa [map_mul, ιM_φ, map_one] at this
  have he2 : (⟨_, heH⟩ : centralizer ({z} : Set G)) * ⟨_, heH⟩ = 1 := Subtype.ext (by
    show g * y * g⁻¹ * (g * y * g⁻¹) = 1
    calc g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hyy']; group)
  have hy1 : y ≠ 1 := by
    rintro rfl
    have e1 : φ ⟨1, hyH⟩ = 1 := by rw [show (⟨1, hyH⟩ : centralizer ({z} : Set G)) = 1 from rfl,
      map_one]
    rw [e1, invEInv_pCore hc (one_mem _)] at hy80
    exact absurd hy80 (by norm_num)
  have he1 : (⟨_, heH⟩ : centralizer ({z} : Set G)) ≠ 1 := fun e => hy1 (by
    have := congrArg Subtype.val e
    simp only [OneMemClass.coe_one] at this
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group)
  have hez : (⟨_, heH⟩ : centralizer ({z} : Set G)) ≠ zC z := fun e => by
    have h1 : g * y * g⁻¹ = z := congrArg Subtype.val e
    have h2 : y = g⁻¹ * z * g := by
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * z * g := by rw [h1]
    have h3 : (⟨y, hyH⟩ : centralizer ({z} : Set G)) = ⟨_, ht⟩ := Subtype.ext h2
    rw [h3, hinvt] at hy80
    exact absurd hy80 (by norm_num)
  obtain ⟨Q, hQe, hQ2, hQc⟩ := e_bound hc hG φ heE he2 he1 hez
  have hconj : (g * (ιM φ h)⁻¹) * iC φ (cR (k + 3)) * (g * (ιM φ h)⁻¹)⁻¹ = g * y * g⁻¹ := by
    have e1 : iC φ (cR (k + 3)) = ιM φ h * y * (ιM φ h)⁻¹ := by
      rw [← hh, show iC φ (h * φ ⟨y, hyH⟩ * h⁻¹) = ιM φ (h * φ ⟨y, hyH⟩ * h⁻¹) from rfl,
        map_mul, map_mul, map_inv, ιM_φ]
    rw [e1]
    group
  have hle := card_le_conj (fun Q' hQ'x hQ' => a2_bound hc hG φ hA hk hQ'x hQ')
    (g * (ιM φ h)⁻¹) (Q := Q) (by rw [hconj]; exact hQe) hQ2
  rw [hQc] at hle
  exact absurd hle (by norm_num)

omit [Finite G] in
theorem cent2_mul_z (t : G) : cent2 z (t * z) = cent2 z t := by
  ext x
  rw [mem_cent2, mem_cent2]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, mul_right_cancel (b := z) ?_⟩
    calc x * t * z = x * (t * z) := by rw [mul_assoc]
      _ = t * z * x := h2
      _ = t * x * z := by rw [mul_assoc, ← h1, ← mul_assoc]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc x * (t * z) = t * x * z := by rw [← mul_assoc, h2]
      _ = t * z * x := by rw [mul_assoc, h1, ← mul_assoc]

theorem smith_2_7
    (hc : CCFacts) (hG : SmithHyp G z) (φ : centralizer ({z} : Set G) ≃* Cz) :
    ∃ g : G, ∃ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G), ∃ h : Cz,
      h * φ ⟨_, ht⟩ * h⁻¹ = cR 5 := by
  by_contra hA'
  have hA : ∀ g : G, ∀ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G), ∀ h : Cz,
      h * φ ⟨_, ht⟩ * h⁻¹ ≠ cR 5 := fun g ht h e => hA' ⟨g, ht, h, e⟩
  obtain ⟨g, ht, hte⟩ := exists_conj_mem_ne hG
  have hAk : ∀ k : Cz, ∀ g : G, ∀ ht : g⁻¹ * z * g ∈ centralizer ({z} : Set G), ∀ h' : Cz,
      h' * (φ.trans (MulAut.conj k)) ⟨_, ht⟩ * h'⁻¹ ≠ cR 5 := by
    intro k g' ht' h' e
    refine hA g' ht' (h' * k) ?_
    rw [← e]
    simp only [MulEquiv.trans_apply, MulAut.conj_apply]
    group
  have hinv : ∀ k : Cz, ∀ i : Fin 9, ∀ h : Cz, h * φ ⟨_, ht⟩ * h⁻¹ = cR i →
      invEInv ((φ.trans (MulAut.conj k)) ⟨_, ht⟩) = Native.ccInvE[(i : ℕ)]! := by
    intro k i h hh
    simp only [MulEquiv.trans_apply, MulAut.conj_apply]
    rw [invEInv_conj, ← cz_invE hc i, ← hh, invEInv_conj]
  rcases smith_conj_classes hc hG φ g ht with h1 | ⟨i, hi, h, hh⟩
  · exact hte h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  ·
    refine false_of_first hc hG (φ.trans (MulAut.conj h)) (hAk h) ht hte ht ?_ rfl
      ((hinv h 1 h hh).trans (by decide))
    simp only [MulEquiv.trans_apply, MulAut.conj_apply]
    exact hh
  ·
    obtain ⟨h2, hh2⟩ := c1_two hc
    have ht₁ : g⁻¹ * z * g * z ∈ centralizer ({z} : Set G) :=
      (centralizer ({z} : Set G)).mul_mem ht (mem_centralizer_singleton_iff.mpr rfl)
    refine false_of_first hc hG (φ.trans (MulAut.conj (h2 * h))) (hAk (h2 * h)) ht hte ht₁ ?_
      (cent2_mul_z _) ((hinv (h2 * h) 2 h hh).trans (by decide))
    have e1 : (⟨g⁻¹ * z * g * z, ht₁⟩ : centralizer ({z} : Set G)) = ⟨_, ht⟩ * zC z := rfl
    simp only [MulEquiv.trans_apply, MulAut.conj_apply]
    rw [e1, map_mul, φ_zC hc hG φ, ← hh2]
    have hzc : h * zCz * h⁻¹ = zCz := by rw [zCz_comm h, mul_inv_cancel_right]
    calc h2 * h * (φ ⟨_, ht⟩ * zCz) * (h2 * h)⁻¹ =
        h2 * ((h * φ ⟨_, ht⟩ * h⁻¹) * (h * zCz * h⁻¹)) * h2⁻¹ := by group
      _ = h2 * (cR 2 * zCz) * h2⁻¹ := by rw [hh, hzc]; rfl
  · exact hA g ht h hh

end CFSG.Sporadic.Co2Smith
