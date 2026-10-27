module

public import CFSG.Quasithin.Vol2.Ch3Sec3CZA6
public import CFSG.Walter.Bender1970.S2.OddFitting
import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Par32 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace Lem3331S

theorem quad_check : ∀ σ ∈ elemsR1, σ ≠ 1 → σ ≠ c45 → ∃ v : A6Coc.Vec4,
    A6Coc.act ((CZA6.c012 * σ * CZA6.c012⁻¹) *
        (CZA6.c012 * CZA6.c012 * σ * (CZA6.c012 * CZA6.c012)⁻¹))
      (v + A6Coc.act (σ * (CZA6.c012 * σ * CZA6.c012⁻¹)) v) ≠
      v + A6Coc.act (σ * (CZA6.c012 * σ * CZA6.c012⁻¹)) v := by
  decide +kernel

theorem cent_check_S : ∀ σ ∈ S6Syl.elemsS, σ * CZA6.c012 = CZA6.c012 * σ →
    σ = 1 ∨ σ = c45 := by
  decide +kernel

theorem cent_check_R : ∀ σ ∈ elemsR1, σ * CZA6.c012 = CZA6.c012 * σ → σ = 1 ∨ σ = c45 := by
  decide +kernel

theorem c45_comm : c45 * CZA6.c012 = CZA6.c012 * c45 := by decide

theorem c012_cube : CZA6.c012 * (CZA6.c012 * CZA6.c012) = 1 := by decide

theorem c012_ne_one : CZA6.c012 ≠ 1 := by decide

theorem c45_ne_one : c45 ≠ 1 := by decide

theorem c45_sq : c45 * c45 = 1 := by decide

theorem c45_not_mem_alt : c45 ∉ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup, sign_c45]
  decide

@[expose] def x0 : A6Coc.Vec4 := A6Coc.crd (A6Coc.duad 3 4)

theorem x0_fix : A6Coc.act CZA6.c012 x0 = x0 := by decide +kernel

theorem x0_move : x0 + A6Coc.act c45 x0 ≠ 0 := by decide +kernel

theorem vec4_neg : ∀ x : A6Coc.Vec4, -x = x := by decide +kernel

theorem vec4_add_self : ∀ x : A6Coc.Vec4, x + x = 0 := by decide +kernel

theorem pow_four_pow {H : Type*} [Monoid H] {c : H} (hc : c * (c * c) = 1) (k : ℕ) :
    c ^ 4 ^ k = c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, ih]
    calc c ^ 4 = c * (c * (c * c)) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = c := by rw [hc, mul_one]

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {d x : G} :
    x ∈ CFSG.conjugate H d ↔ d * x * d⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : d * ((MulAut.conj d⁻¹).toMonoidHom y) * d⁻¹ = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e]
    exact hy
  · intro hx
    refine ⟨d * x * d⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

open CFSG in
theorem double_commutator_eq [Finite G] (P K : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card (↥K))) (hsolv : Group.IsSolvable K) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ :=
  GL83.commutator_double_eq_self P K hPK hcop hsolv

theorem card_mul_card_le [Finite G] {A B Z : Subgroup G} (hA : A ≤ Z) (hB : B ≤ Z)
    (hAB : A ⊓ B = ⊥) : Nat.card A * Nat.card B ≤ Nat.card Z := by
  let f : ↥A × ↥B → ↥Z := fun x => ⟨(x.1 : G) * x.2, Z.mul_mem (hA x.1.2) (hB x.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : (a : G) * b = a' * b' := congrArg Subtype.val h
    have h2 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have h3 : (a' : G)⁻¹ * a ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hAB, Subgroup.mem_bot] at h3
    have ha : (a : G) = a' := by
      calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
        _ = a' := by rw [h3, mul_one]
    have hb : (b : G) = b' := by
      have := h1
      rw [ha] at this
      exact mul_left_cancel this
    rw [Subtype.ext ha, Subtype.ext hb]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem card_le_two_mul [Finite G] {A Z : Subgroup G}
    (h : ∀ x ∈ Z, ∀ y ∈ Z, x ∉ A → y ∉ A → x⁻¹ * y ∈ A) : Nat.card Z ≤ 2 * Nat.card A := by
  classical
  by_cases hall : ∀ x ∈ Z, x ∈ A
  · have : Nat.card Z ≤ Nat.card A := Subgroup.card_le_of_le hall
    omega
  push Not at hall
  obtain ⟨z₀, hz₀, hz₀A⟩ := hall
  let f : ↥Z → ↥A × Bool := fun x =>
    if hx : (x : G) ∈ A then (⟨x, hx⟩, false) else (⟨z₀⁻¹ * x, h z₀ hz₀ x x.2 hz₀A hx⟩, true)
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : (x : G) ∈ A <;> by_cases hy : (y : G) ∈ A <;>
      simp only [f, hx, hy, dite_true, dite_false, Prod.mk.injEq, Subtype.mk.injEq,
        Bool.false_eq_true, Bool.true_eq_false, and_false, and_true] at hxy
    · exact Subtype.ext hxy
    · exact Subtype.ext (mul_left_cancel hxy)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem exists_conj_sylow_three [Finite G] {P T B B' : Subgroup G} (hTP : T ≤ P)
    (hT2 : IsPGroup 2 T) (hcard : Nat.card P = 3 * Nat.card T) (hBP : B ≤ P) (hB'P : B' ≤ P)
    (hB3 : Nat.card B = 3) (hB'3 : Nat.card B' = 3) :
    ∃ k ∈ T, B.map (MulAut.conj k).toMonoidHom = B' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
  have hc1 : Nat.card (B.subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv, hB3]
  have hc2 : Nat.card (B'.subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'P).toEquiv, hB'3]
  have hidx : ∀ H : Subgroup ↥P, Nat.card H = 3 → ¬ 3 ∣ H.index := by
    intro H hH h3
    have h1 := Subgroup.card_mul_index H
    rw [hH, hcard, hn] at h1
    have h2 : H.index = 2 ^ n := by omega
    rw [h2] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  let S₁ : Sylow 3 ↥P :=
    (IsPGroup.of_card (n := 1) (by rw [hc1, pow_one])).toSylow (hidx _ hc1)
  let S₂ : Sylow 3 ↥P :=
    (IsPGroup.of_card (n := 1) (by rw [hc2, pow_one])).toSylow (hidx _ hc2)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥P S₁ S₂
  have hcompl : (T.subgroupOf P).IsComplement' (B.subgroupOf P) := by
    apply Subgroup.isComplement'_of_coprime
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv, hc1, hcard, mul_comm]
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv, hc1, hn]
      exact Nat.Coprime.pow_left n (by norm_num)
  obtain ⟨⟨k', b'⟩, hkb, -⟩ := hcompl.existsUnique g
  have hk : ((k' : ↥P) : G) ∈ T := Subgroup.mem_subgroupOf.mp k'.2
  have hb : ((b' : ↥P) : G) ∈ B := Subgroup.mem_subgroupOf.mp b'.2
  refine ⟨_, hk, ?_⟩
  have hgB : ∀ x ∈ B, (g : G) * x * (g : G)⁻¹ ∈ B' := by
    intro x hx
    have hxP : x ∈ P := hBP hx
    have h1 : (⟨x, hxP⟩ : ↥P) ∈ (S₁ : Subgroup ↥P) := Subgroup.mem_subgroupOf.mpr hx
    have h2 : g * ⟨x, hxP⟩ * g⁻¹ ∈ ((g • S₁ : Sylow 3 _) : Subgroup ↥P) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨_, h1, rfl⟩
    rw [hg] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have hg' : (g : G) = ((k' : ↥P) : G) * ((b' : ↥P) : G) := by
    rw [← hkb]
    rfl
  have hle : B.map (MulAut.conj ((k' : ↥P) : G)).toMonoidHom ≤ B' := by
    rintro _ ⟨x, hx, rfl⟩
    have hxb : ((b' : ↥P) : G)⁻¹ * x * ((b' : ↥P) : G) ∈ B :=
      B.mul_mem (B.mul_mem (B.inv_mem hb) hx) hb
    have h1 := hgB _ hxb
    have e : (g : G) * (((b' : ↥P) : G)⁻¹ * x * ((b' : ↥P) : G)) * (g : G)⁻¹ =
        ((k' : ↥P) : G) * x * ((k' : ↥P) : G)⁻¹ := by
      rw [hg']
      group
    rw [e] at h1
    exact h1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hB'3, Subgroup.card_map_of_injective (MulAut.conj _).injective, hB3]


theorem card_eq_two_mul [Finite G] {A Z : Subgroup G} (hAZ : A ≤ Z) {w : G} (hw : w ∈ Z)
    (hwA : w ∉ A) (h : ∀ x ∈ Z, x ∈ A ∨ w⁻¹ * x ∈ A) : Nat.card Z = 2 * Nat.card A := by
  have hle := card_le_two_mul (A := A) (Z := Z) (fun x hx y hy hxA hyA => by
    rcases h x hx with h1 | h1
    · exact absurd h1 hxA
    rcases h y hy with h2 | h2
    · exact absurd h2 hyA
    have e : x⁻¹ * y = (w⁻¹ * x)⁻¹ * (w⁻¹ * y) := by group
    rw [e]
    exact A.mul_mem (A.inv_mem h1) h2)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hAZ
  have hne : Nat.card A ≠ Nat.card Z := fun he =>
    hwA ((Subgroup.eq_of_le_of_card_ge hAZ he.ge) ▸ hw)
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hne hm.symm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have hm2 : 2 ≤ m := by omega
  have h3 : Nat.card A * 2 ≤ Nat.card A * m := Nat.mul_le_mul_left _ hm2
  nlinarith

theorem map_conj_le_inf_centralizer {R X Y : Subgroup G} {g : G}
    (hgR : g ∈ Subgroup.normalizer (R : Set G)) (hXY : ∀ y ∈ Y, g * y * g⁻¹ ∈ X) :
    (R ⊓ Subgroup.centralizer (X : Set G)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      R ⊓ Subgroup.centralizer (Y : Set G) := by
  rintro _ ⟨x, ⟨hxR, hxX⟩, rfl⟩
  have hxR' : x ∈ R := hxR
  have hxX' : x ∈ Subgroup.centralizer (X : Set G) := hxX
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgR) x).mp hxR'
    simpa using this
  · show g⁻¹ * x * g ∈ Subgroup.centralizer (Y : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := Subgroup.mem_centralizer_iff.mp hxX' _ (hXY y hy)
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * x * g * y := by group

section Pieces

variable {L T : Subgroup G} (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6))
  (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G))

theorem rho_eq_of_quad {W : Subgroup G} (β : ↥(blockU L) →* Multiplicative A6Coc.Vec4)
    (hβs : Function.Surjective β)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (β u') = A6Coc.act (ρ g) (Multiplicative.toAdd (β u)))
    (hWLT : W ≤ L ⊔ T) (hWR : ∀ x (hx : x ∈ W), ρ ⟨x, hLTN (hWLT hx)⟩ ∈ r1)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hUW : ∀ u ∈ blockU L, ∀ x ∈ W, u * x * u⁻¹ ∈ W)
    {ℓ : G} (hℓ : ℓ ∈ L) (hρℓ : ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = CZA6.c012)
    (hℓW : ∀ x ∈ W, ℓ * x * ℓ⁻¹ ∈ W) :
    ∀ x (hx : x ∈ W), ρ ⟨x, hLTN (hWLT hx)⟩ = 1 ∨ ρ ⟨x, hLTN (hWLT hx)⟩ = c45 := by
  have hquad : ∀ x (hx : x ∈ W) y (hy : y ∈ W), ∀ v : A6Coc.Vec4,
      A6Coc.act (ρ ⟨y, hLTN (hWLT hy)⟩) (v + A6Coc.act (ρ ⟨x, hLTN (hWLT hx)⟩) v) =
        v + A6Coc.act (ρ ⟨x, hLTN (hWLT hx)⟩) v := by
    intro x hx y hy v
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd v)
    have hxN : x ∈ Subgroup.normalizer (L : Set G) := hLTN (hWLT hx)
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := hLTN (hWLT hy)
    let u₁ : ↥(blockU L) := ⟨x * u * x⁻¹, Mod32.conj_mem_blockU hxN u⟩
    have hβ1 := hβe ⟨x, hxN⟩ u u₁ rfl
    let c : ↥(blockU L) := u * u₁⁻¹
    have hcβ : Multiplicative.toAdd (β c) = v + A6Coc.act (ρ ⟨x, hxN⟩) v := by
      have e : Multiplicative.toAdd (β c) = Multiplicative.toAdd (β u) +
          (-Multiplicative.toAdd (β u₁)) := by
        show Multiplicative.toAdd (β (u * u₁⁻¹)) = _
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
      rw [e, hβ1, hu]
      show v + -(A6Coc.act (ρ ⟨x, hxN⟩) v) = v + A6Coc.act (ρ ⟨x, hxN⟩) v
      rw [vec4_neg]
    have hcW : (c : G) ∈ W := by
      have e : (c : G) = ((u : G) * x * (u : G)⁻¹) * x⁻¹ := by
        show (u : G) * (x * u * x⁻¹)⁻¹ = _
        group
      rw [e]
      exact W.mul_mem (hUW u u.2 x hx) (W.inv_mem hx)
    have hyc : y * c * y⁻¹ = c := by
      rw [hWab y hy c hcW]
      group
    let c' : ↥(blockU L) := ⟨y * c * y⁻¹, Mod32.conj_mem_blockU hyN c⟩
    have hβ2 := hβe ⟨y, hyN⟩ c c' rfl
    have hcc : c' = c := Subtype.ext hyc
    rw [hcc, hcβ] at hβ2
    exact hβ2.symm
  intro x hx
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hσ : ρ ⟨x, hLTN (hWLT hx)⟩ ∈ elemsR1 := by
    rw [← mem_r1_iff]
    exact hWR x hx
  obtain ⟨v, hv⟩ := quad_check _ hσ h1 h2
  have hℓN : ℓ ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hℓ
  have hx₁ : ℓ * x * ℓ⁻¹ ∈ W := hℓW x hx
  have hx₂ : ℓ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹ ∈ W := hℓW _ hx₁
  have ha : x * (ℓ * x * ℓ⁻¹) ∈ W := W.mul_mem hx hx₁
  have hb : (ℓ * x * ℓ⁻¹) * (ℓ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹) ∈ W := W.mul_mem hx₁ hx₂
  have hq := hquad _ ha _ hb v
  have eρ1 : ρ ⟨ℓ * x * ℓ⁻¹, hLTN (hWLT hx₁)⟩ =
      CZA6.c012 * ρ ⟨x, hLTN (hWLT hx)⟩ * CZA6.c012⁻¹ := by
    have e : (⟨ℓ * x * ℓ⁻¹, hLTN (hWLT hx₁)⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨ℓ, hℓN⟩ * ⟨x, hLTN (hWLT hx)⟩ * (⟨ℓ, hℓN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ :=
      rfl
    rw [e, map_mul, map_mul, map_inv, hρℓ]
  have eρ2 : ρ ⟨ℓ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹, hLTN (hWLT hx₂)⟩ =
      CZA6.c012 * CZA6.c012 * ρ ⟨x, hLTN (hWLT hx)⟩ * (CZA6.c012 * CZA6.c012)⁻¹ := by
    have e : (⟨ℓ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹, hLTN (hWLT hx₂)⟩ :
        ↥(Subgroup.normalizer (L : Set G))) =
        ⟨ℓ, hℓN⟩ * ⟨ℓ * x * ℓ⁻¹, hLTN (hWLT hx₁)⟩ *
          (⟨ℓ, hℓN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hρℓ, eρ1]
    group
  have eρa : ρ ⟨x * (ℓ * x * ℓ⁻¹), hLTN (hWLT ha)⟩ =
      ρ ⟨x, hLTN (hWLT hx)⟩ * (CZA6.c012 * ρ ⟨x, hLTN (hWLT hx)⟩ * CZA6.c012⁻¹) := by
    have e : (⟨x * (ℓ * x * ℓ⁻¹), hLTN (hWLT ha)⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨x, hLTN (hWLT hx)⟩ * ⟨ℓ * x * ℓ⁻¹, hLTN (hWLT hx₁)⟩ := rfl
    rw [e, map_mul, eρ1]
  have eρb : ρ ⟨(ℓ * x * ℓ⁻¹) * (ℓ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹), hLTN (hWLT hb)⟩ =
      (CZA6.c012 * ρ ⟨x, hLTN (hWLT hx)⟩ * CZA6.c012⁻¹) *
        (CZA6.c012 * CZA6.c012 * ρ ⟨x, hLTN (hWLT hx)⟩ * (CZA6.c012 * CZA6.c012)⁻¹) := by
    have e : (⟨(ℓ * x * ℓ⁻¹) * (ℓ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹), hLTN (hWLT hb)⟩ :
        ↥(Subgroup.normalizer (L : Set G))) =
        ⟨ℓ * x * ℓ⁻¹, hLTN (hWLT hx₁)⟩ * ⟨ℓ * (ℓ * x * ℓ⁻¹) * ℓ⁻¹, hLTN (hWLT hx₂)⟩ := rfl
    rw [e, map_mul, eρ1, eρ2]
  rw [eρa, eρb] at hq
  exact hv hq

theorem relIndex_sup_eq_two [Finite G] {Q W : Subgroup G} (hQLT : Q ≤ L ⊔ T)
    (hWLT : W ≤ L ⊔ T) (hWQ : W ≤ Subgroup.normalizer (Q : Set G))
    (hρ1 : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 ↔ g ∈ Q)
    (hρW : ∀ x (hx : x ∈ W), ρ ⟨x, hLTN (hWLT hx)⟩ = 1 ∨ ρ ⟨x, hLTN (hWLT hx)⟩ = c45)
    {w₀ : G} (hw₀ : w₀ ∈ W) (hw₀ρ : ρ ⟨w₀, hLTN (hWLT hw₀)⟩ = c45) :
    Q.relIndex (Q ⊔ W) = 2 := by
  have hSLT : Q ⊔ W ≤ L ⊔ T := sup_le hQLT hWLT
  have hSρ : ∀ s (hs : s ∈ Q ⊔ W), ρ ⟨s, hLTN (hSLT hs)⟩ = 1 ∨
      ρ ⟨s, hLTN (hSLT hs)⟩ = c45 := by
    intro s hs
    obtain ⟨q, hq, x, hx, hqx⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hWQ).mp hs
    have e : (⟨s, hLTN (hSLT hs)⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨q, hLTN (hQLT hq)⟩ * ⟨x, hLTN (hWLT hx)⟩ := Subtype.ext hqx
    rw [e, map_mul, (hρ1 q (hQLT hq)).mpr hq, one_mul]
    exact hρW x hx
  have hSN : Q ⊔ W ≤ Subgroup.normalizer (L : Set G) := hSLT.trans hLTN
  let φ : ↥(Q ⊔ W) →* Equiv.Perm (Fin 6) := ρ.comp (Subgroup.inclusion hSN)
  have hφker : φ.ker = Q.subgroupOf (Q ⊔ W) := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hρ1 s (hSLT s.2)
  have hφrange : Nat.card φ.range = 2 := by
    have hle : φ.range ≤ Subgroup.zpowers c45 := by
      rintro _ ⟨s, rfl⟩
      show ρ ⟨(s : G), hLTN (hSLT s.2)⟩ ∈ Subgroup.zpowers c45
      rcases hSρ s s.2 with h1 | h1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [h1]
        exact Subgroup.mem_zpowers c45
    have h2 : Nat.card φ.range ≤ 2 := by
      have := Subgroup.card_le_of_le hle
      rwa [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact c45_sq) c45_ne_one] at this
    have h3 : φ.range ≠ ⊥ := by
      intro hbot
      have h4 : φ ⟨w₀, Subgroup.mem_sup_right hw₀⟩ ∈ φ.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h4
      have h5 : ρ ⟨w₀, hLTN (hWLT hw₀)⟩ = 1 := h4
      rw [hw₀ρ] at h5
      exact c45_ne_one h5
    have h5 := (Subgroup.one_lt_card_iff_ne_bot _).mpr h3
    omega
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hφrange, hφker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : Q ≤ Q ⊔ W)).toEquiv] at h1
  have h2 := Subgroup.relIndex_mul_card (H := Q) (K := Q ⊔ W)
  rw [inf_of_le_left (le_sup_left : Q ≤ Q ⊔ W), h1] at h2
  have hpos : 0 < Nat.card ↥Q := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h2

theorem eq_inf_sup_sup {Q W : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hρL : ∀ s ∈ alternatingGroup (Fin 6), ∃ ℓ, ∃ hℓ : ℓ ∈ L,
      ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = s)
    (hρ1 : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 ↔ g ∈ Q) (hQT : Q ≤ T) (hWT : W ≤ T)
    {w₀ : G} (hw₀ : w₀ ∈ W) (hw₀ρ : ρ ⟨w₀, hTL (hWT hw₀)⟩ = c45) :
    T = T ⊓ L ⊔ Q ⊔ W := by
  have hT5a : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ alternatingGroup (Fin 6) → t ∈ T ⊓ L ⊔ Q := by
    intro t ht hA'
    obtain ⟨ℓ, hℓ, e⟩ := hρL _ hA'
    have hm : ℓ⁻¹ * t ∈ L ⊔ T :=
      (L ⊔ T).mul_mem ((L ⊔ T).inv_mem (Subgroup.mem_sup_left hℓ)) (Subgroup.mem_sup_right ht)
    have h1 : ℓ⁻¹ * t ∈ Q := by
      rw [← hρ1 _ hm]
      have e2 : (⟨ℓ⁻¹ * t, hLTN hm⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          (⟨ℓ, Subgroup.le_normalizer hℓ⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ *
            ⟨t, hTL ht⟩ := rfl
      rw [e2, map_mul, map_inv, e, inv_mul_cancel]
    have hℓT : ℓ ∈ T := by
      have h2 := T.mul_mem ht (T.inv_mem (hQT h1))
      have e4 : t * (ℓ⁻¹ * t)⁻¹ = ℓ := by group
      rwa [e4] at h2
    have e3 : t = ℓ * (ℓ⁻¹ * t) := by group
    rw [e3]
    exact Subgroup.mul_mem_sup ⟨hℓT, hℓ⟩ h1
  refine le_antisymm (fun t ht => ?_) (sup_le (sup_le inf_le_left hQT) hWT)
  by_cases hA' : ρ ⟨t, hTL ht⟩ ∈ alternatingGroup (Fin 6)
  · exact Subgroup.mem_sup_left (hT5a t ht hA')
  · have htw : t * w₀ ∈ T := T.mul_mem ht (hWT hw₀)
    have hA2 : ρ ⟨t * w₀, hTL htw⟩ ∈ alternatingGroup (Fin 6) := by
      have e : (⟨t * w₀, hTL htw⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨t, hTL ht⟩ * ⟨w₀, hTL (hWT hw₀)⟩ := rfl
      rw [Equiv.Perm.mem_alternatingGroup] at hA' ⊢
      rw [e, map_mul, hw₀ρ, Equiv.Perm.sign_mul, sign_c45]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (ρ ⟨t, hTL ht⟩)) with h1 | h1
      · exact absurd h1 hA'
      · rw [h1]
        decide
    have h1 := hT5a _ htw hA2
    have e : t = (t * w₀) * w₀⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right (W.inv_mem hw₀))

theorem card_inf_centralizer_eq_two [Finite G] {Z A' : Subgroup G}
    (β : ↥(blockU L) →* Multiplicative A6Coc.Vec4)
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hZdec : ∀ z ∈ Z, ∃ u ∈ Z ⊓ blockU L, ∃ c ∈ Z ⊓ Subgroup.centralizer (L : Set G),
      z = u * c)
    (hfixZ : ∀ u : ↥(blockU L), (u : G) ∈ Z → Multiplicative.toAdd (β u) = 0 ∨
      Multiplicative.toAdd (β u) = CZA6.w0)
    (hA'Z : A' ≤ Z) (hAA' : (Z ⊓ Subgroup.centralizer (L : Set G)) ⊓ A' = ⊥)
    (hcard : Nat.card A' = Nat.card ↥(Z ⊓ Subgroup.centralizer (L : Set G)))
    (h1 : 1 < Nat.card ↥(Z ⊓ Subgroup.centralizer (L : Set G))) :
    Nat.card ↥(Z ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
  have hZL_C : ∀ u : ↥(blockU L), Multiplicative.toAdd (β u) = 0 →
      (u : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro u hu
    have h2 : β u = 1 := Multiplicative.toAdd.injective (by rw [toAdd_one]; exact hu)
    have h3 : u ∈ β.ker := h2
    rw [hβk, Subgroup.mem_subgroupOf] at h3
    exact h3.2
  have hZA : Nat.card Z ≤ 2 * Nat.card ↥(Z ⊓ Subgroup.centralizer (L : Set G)) := by
    apply card_le_two_mul
    intro x hx y hy hxA hyA
    obtain ⟨u₁, hu₁, c₁, hc₁, rfl⟩ := hZdec x hx
    obtain ⟨u₂, hu₂, c₂, hc₂, rfl⟩ := hZdec y hy
    have hb : ∀ (u : G) (hu : u ∈ Z ⊓ blockU L) (c : G),
        c ∈ Z ⊓ Subgroup.centralizer (L : Set G) →
        u * c ∉ Z ⊓ Subgroup.centralizer (L : Set G) →
          Multiplicative.toAdd (β ⟨u, hu.2⟩) = CZA6.w0 := by
      intro u hu c hc huc
      rcases hfixZ ⟨u, hu.2⟩ hu.1 with h0 | h0
      · exfalso
        exact huc ⟨Z.mul_mem hu.1 hc.1, Subgroup.mul_mem _ (hZL_C ⟨u, hu.2⟩ h0) hc.2⟩
      · exact h0
    have h2 := hb u₁ hu₁ c₁ hc₁ hxA
    have h3 := hb u₂ hu₂ c₂ hc₂ hyA
    have h4 : Multiplicative.toAdd
        (β ((⟨u₁, hu₁.2⟩ : ↥(blockU L))⁻¹ * ⟨u₂, hu₂.2⟩)) = 0 := by
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, h2, h3, vec4_neg, vec4_add_self]
    have h5 := hZL_C _ h4
    refine ⟨Z.mul_mem (Z.inv_mem (Z.mul_mem hu₁.1 hc₁.1)) (Z.mul_mem hu₂.1 hc₂.1), ?_⟩
    have e : (u₁ * c₁)⁻¹ * (u₂ * c₂) = c₁⁻¹ * (u₁⁻¹ * u₂) * c₂ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc₁.2) h5) hc₂.2
  have h2 := card_mul_card_le (inf_le_left : Z ⊓ Subgroup.centralizer (L : Set G) ≤ Z) hA'Z hAA'
  rw [hcard] at h2
  have h3 : Nat.card ↥(Z ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 := by nlinarith
  omega

end Pieces

section Pieces2

variable {L T : Subgroup G} (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6))
  (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G))

theorem exists_pow_eq {Q : Subgroup G} (hQ2 : IsPGroup 2 ↥Q)
    (hρ1 : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 ↔ g ∈ Q)
    {ℓ : G} (hℓ : ℓ ∈ L) (hρℓ : ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = CZA6.c012) :
    ∃ k : ℕ, (ℓ ^ 4 ^ k) ^ 3 = 1 ∧
      ρ ⟨ℓ ^ 4 ^ k, Subgroup.le_normalizer (L.pow_mem hℓ _)⟩ = CZA6.c012 := by
  have hm : ℓ ^ 3 ∈ L ⊔ T := (L ⊔ T).pow_mem (Subgroup.mem_sup_left hℓ) 3
  have hℓ3 : ℓ ^ 3 ∈ Q := by
    rw [← hρ1 _ hm]
    have e : (⟨ℓ ^ 3, hLTN hm⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ^ 3 := rfl
    rw [e, map_pow, hρℓ]
    decide
  obtain ⟨k, hk⟩ := hQ2 ⟨ℓ ^ 3, hℓ3⟩
  have hk' : (ℓ ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_, ?_⟩
  · have h44 : (4 : ℕ) ^ k = 2 ^ k * 2 ^ k := by
      rw [← mul_pow]
      norm_num
    have e : (ℓ ^ 4 ^ k) ^ 3 = ((ℓ ^ 3) ^ 2 ^ k) ^ 2 ^ k := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, h44]
      congr 1
      ring
    rw [e, hk', one_pow]
  · have e : (⟨ℓ ^ 4 ^ k, Subgroup.le_normalizer (L.pow_mem hℓ _)⟩ :
        ↥(Subgroup.normalizer (L : Set G))) = ⟨ℓ, Subgroup.le_normalizer hℓ⟩ ^ 4 ^ k := rfl
    rw [e, map_pow, hρℓ, pow_four_pow c012_cube]

theorem card_pre_p1 [Finite G] {Q : Subgroup G} (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    (hQ2 : IsPGroup 2 ↥Q) (hQLT : Q ≤ L ⊔ T)
    (htop : (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤)
    (hρ1 : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 ↔ g ∈ Q) (hTP : T ≤ pre ρ hLTN p1) :
    Nat.card (pre ρ hLTN p1) = 3 * Nat.card T := by
  have hPcard : Nat.card (pre ρ hLTN p1) = 48 * Nat.card Q := by
    rw [card_pre ρ hLTN p1, htop, top_inf_eq, card_p1]
    congr 1
    have hk2 : (ρ.comp (Subgroup.inclusion hLTN)).ker = Q.subgroupOf (L ⊔ T) := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hρ1 g g.2
    rw [hk2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQLT).toEquiv
  obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp hT2
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ2
  have h1 := Subgroup.relIndex_mul_card (H := T) (K := pre ρ hLTN p1)
  rw [inf_of_le_left hTP] at h1
  have hodd : ¬ 2 ∣ T.relIndex (pre ρ hLTN p1) := fun h2 =>
    hTidx (h2.trans (Subgroup.relIndex_dvd_index_of_le hTP))
  rw [hPcard, hj, hi] at h1 ⊢
  have h48 : (48 : ℕ) * 2 ^ j = 3 * 2 ^ (j + 4) := by
    rw [pow_add]
    ring
  rw [h48] at h1 ⊢
  have hcop : Nat.Coprime (T.relIndex (pre ρ hLTN p1)) (2 ^ (j + 4)) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.symm
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd))
  have h3 : T.relIndex (pre ρ hLTN p1) ∣ 3 * 2 ^ (j + 4) := ⟨2 ^ i, by rw [← h1]⟩
  have h4 : T.relIndex (pre ρ hLTN p1) ∣ 3 := hcop.dvd_of_dvd_mul_right h3
  rcases (Nat.dvd_prime Nat.prime_three).mp h4 with h5 | h5
  · exfalso
    rw [h5, one_mul] at h1
    have h6 : 3 ∣ 2 ^ i := ⟨2 ^ (j + 4), h1⟩
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h6
    omega
  · rw [h5] at h1
    omega

theorem exists_v₁ (β : ↥(blockU L) →* Multiplicative A6Coc.Vec4)
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (β u') = A6Coc.act (ρ g) (Multiplicative.toAdd (β u)))
    (hUab : ∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x)
    {b : G} (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1)
    (hρb : ρ ⟨b, hbN⟩ = CZA6.c012) {w : G} (hwN : w ∈ Subgroup.normalizer (L : Set G))
    (hwρ : ρ ⟨w, hwN⟩ = c45) :
    ∃ v ∈ blockU L, v ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) ∧
      v * w * v⁻¹ * w⁻¹ ∉ Subgroup.centralizer (L : Set G) := by
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x0)
  let u₁ : ↥(blockU L) := ⟨b * u * b⁻¹, Mod32.conj_mem_blockU hbN u⟩
  let u₂ : ↥(blockU L) := ⟨b * u₁ * b⁻¹, Mod32.conj_mem_blockU hbN u₁⟩
  let v₁ : ↥(blockU L) := u * u₁ * u₂
  have hβu₁ : Multiplicative.toAdd (β u₁) = x0 := by
    rw [hβe ⟨b, hbN⟩ u u₁ rfl, hρb, hu, toAdd_ofAdd]
    exact x0_fix
  have hβu₂ : Multiplicative.toAdd (β u₂) = x0 := by
    rw [hβe ⟨b, hbN⟩ u₁ u₂ rfl, hρb, hβu₁]
    exact x0_fix
  have hβv₁ : Multiplicative.toAdd (β v₁) = x0 := by
    show Multiplicative.toAdd (β (u * u₁ * u₂)) = x0
    rw [map_mul β, map_mul β, toAdd_mul, toAdd_mul, hu, toAdd_ofAdd, hβu₁, hβu₂, vec4_add_self,
      zero_add]
  have h3 : b * (u₂ : G) * b⁻¹ = u := by
    show b * (b * (b * (u : G) * b⁻¹) * b⁻¹) * b⁻¹ = u
    have e : b * (b * (b * (u : G) * b⁻¹) * b⁻¹) * b⁻¹ = b ^ 3 * u * (b ^ 3)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [e, hb3, one_mul, inv_one, mul_one]
  have hbv : b * (v₁ : G) * b⁻¹ = v₁ := by
    have hc : (u : G) * ((u₁ : G) * u₂) = ((u₁ : G) * u₂) * u :=
      hUab _ u.2 _ ((blockU L).mul_mem u₁.2 u₂.2)
    have e1 : b * (v₁ : G) * b⁻¹ = (b * u * b⁻¹) * (b * u₁ * b⁻¹) * (b * u₂ * b⁻¹) := by
      show b * ((u : G) * u₁ * u₂) * b⁻¹ = _
      group
    rw [e1, h3]
    show (u₁ : G) * u₂ * u = (u : G) * u₁ * u₂
    rw [mul_assoc (u : G), hc]
  refine ⟨v₁, v₁.2, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc : Commute b (v₁ : G) := by
      show b * v₁ = v₁ * b
      calc b * (v₁ : G) = (b * v₁ * b⁻¹) * b := by group
        _ = v₁ * b := by rw [hbv]
    exact (hc.zpow_left i).eq
  · let c₁ : ↥(blockU L) := v₁ * ⟨w * (v₁ : G)⁻¹ * w⁻¹, Mod32.conj_mem_blockU hwN v₁⁻¹⟩
    have hc₁β : Multiplicative.toAdd (β c₁) = x0 + A6Coc.act c45 x0 := by
      have e := hβe ⟨w, hwN⟩ v₁⁻¹ ⟨w * (v₁ : G)⁻¹ * w⁻¹, Mod32.conj_mem_blockU hwN v₁⁻¹⟩ rfl
      show Multiplicative.toAdd (β (v₁ * _)) = _
      rw [map_mul, toAdd_mul, e, map_inv, toAdd_inv, hβv₁, vec4_neg, hwρ]
    have hc₁ : (c₁ : G) = (v₁ : G) * w * (v₁ : G)⁻¹ * w⁻¹ := by
      show (v₁ : G) * (w * (v₁ : G)⁻¹ * w⁻¹) = _
      group
    rw [← hc₁]
    intro hc
    have h1 : c₁ ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact ⟨c₁.2, hc⟩
    apply x0_move
    rw [← hc₁β]
    have h2 : β c₁ = 1 := h1
    rw [h2]
    rfl

theorem le_of_index_two {C K Kw W : Subgroup G}
    (hidx : (Kw.subgroupOf K).index = 2) (hCK : C ≤ K)
    (hKwW : Kw ≤ Subgroup.centralizer (W : Set G))
    {w : G} (hw : w ∈ W) (hwC : ∀ t ∈ C, t * (w * t⁻¹ * w⁻¹) ∈ Subgroup.centralizer (L : Set G))
    {v₁ : G} (hv₁ : v₁ ∈ K) (hv₁w : v₁ * w * v₁⁻¹ * w⁻¹ ∉ Subgroup.centralizer (L : Set G)) :
    C ≤ Kw := by
  have hv₁Kw : v₁ ∉ Kw := by
    intro h1
    apply hv₁w
    have h2 : w * v₁ = v₁ * w := Subgroup.mem_centralizer_iff.mp (hKwW h1) w hw
    have e : v₁ * w * v₁⁻¹ * w⁻¹ = 1 := by
      rw [← h2]
      group
    rw [e]
    exact Subgroup.one_mem _
  intro t ht
  by_contra htV
  have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨t, hCK ht⟩ : ↥K)⁻¹)
    (b := ⟨v₁, hv₁⟩)).mpr (iff_of_false (fun h' => htV (by
      have := Subgroup.mem_subgroupOf.mp h'
      simpa using this)) (fun h' => hv₁Kw (Subgroup.mem_subgroupOf.mp h')))
  have hc : t⁻¹ * v₁ ∈ Kw := Subgroup.mem_subgroupOf.mp key
  apply hv₁w
  have h2 : w * (t⁻¹ * v₁) = (t⁻¹ * v₁) * w := Subgroup.mem_centralizer_iff.mp (hKwW hc) w hw
  have e : v₁ * w * v₁⁻¹ * w⁻¹ = t * (w * t⁻¹ * w⁻¹) := by
    calc v₁ * w * v₁⁻¹ * w⁻¹ = t * ((t⁻¹ * v₁) * w) * (t⁻¹ * v₁)⁻¹ * t⁻¹ * w⁻¹ := by group
      _ = t * (w * (t⁻¹ * v₁)) * (t⁻¹ * v₁)⁻¹ * t⁻¹ * w⁻¹ := by rw [h2]
      _ = t * (w * t⁻¹ * w⁻¹) := by group
  rw [e]
  exact hwC t ht

theorem le_sup_of_index_two {K Kw V : Subgroup G} (hidx : (Kw.subgroupOf K).index = 2)
    {v₁ : G} (hv₁ : v₁ ∈ K) (hv₁V : v₁ ∈ V) (hv₁Kw : v₁ ∉ Kw) : K ≤ V ⊔ Kw := by
  intro x hx
  by_cases hxV : x ∈ Kw
  · exact Subgroup.mem_sup_right hxV
  · have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨v₁, hv₁⟩ : ↥K)⁻¹)
      (b := ⟨x, hx⟩)).mpr (iff_of_false (fun h' => hv₁Kw (by
        have := Subgroup.mem_subgroupOf.mp h'
        simpa using this)) (fun h' => hxV (Subgroup.mem_subgroupOf.mp h')))
    have hc : v₁⁻¹ * x ∈ Kw := Subgroup.mem_subgroupOf.mp key
    have e : x = v₁ * (v₁⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hv₁V hc

theorem mem_normalizer_of_le [Finite G] {S X V W B : Subgroup G} {g : G}
    (hSle : S ≤ X ⊔ ⁅V, B⁆) (hX : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ S)
    (hV : V.map (MulAut.conj g⁻¹).toMonoidHom ≤ W) (hB : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ B)
    (hWB : ⁅W, B⁆ ≤ S) : g ∈ Subgroup.normalizer (S : Set G) := by
  have hmap : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    refine (Subgroup.map_mono hSle).trans ?_
    rw [Subgroup.map_sup]
    refine sup_le hX ?_
    rw [Subgroup.map_commutator]
    exact (Subgroup.commutator_mono hV hB).trans hWB
  have hcard : Nat.card (S.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj _).injective
  have heq := Subgroup.eq_of_le_of_card_ge hmap hcard.ge
  have hinv : g⁻¹ ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hmap ⟨x, hx, rfl⟩
    · intro hx
      rw [← heq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := (MulAut.conj g⁻¹).injective hyx
      rw [← hyx']
      exact hy
  simpa using Subgroup.inv_mem _ hinv

end Pieces2

theorem exists_mul_mem_normalizer [Finite G] {P T B : Subgroup G} (hTP : T ≤ P)
    (hT2 : IsPGroup 2 T) (hPT : Nat.card P = 3 * Nat.card T) (hBP : B ≤ P) (hB3 : Nat.card B = 3)
    {d : G} (hdP : d ∈ Subgroup.normalizer (P : Set G)) :
    ∃ κ ∈ T, d * κ ∈ Subgroup.normalizer (B : Set G) := by
  have hBdP : CFSG.conjugate B d ≤ P := fun x hx => by
    have h1 := hBP (mem_conjugate_iff.mp hx)
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdP) _).mp h1
    simpa [mul_assoc] using this
  have hBd3 : Nat.card (CFSG.conjugate B d) = 3 := by
    rw [← hB3]
    exact Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective
  obtain ⟨κ, hκT, hκB⟩ := exists_conj_sylow_three hTP hT2 hPT hBP hBdP hB3 hBd3
  refine ⟨κ, hκT, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : κ * x * κ⁻¹ ∈ B.map (MulAut.conj κ).toMonoidHom := ⟨x, hx, rfl⟩
    rw [hκB] at h1
    have h2 := mem_conjugate_iff.mp h1
    have e : d * κ * x * (d * κ)⁻¹ = d * (κ * x * κ⁻¹) * d⁻¹ := by group
    rw [e]
    exact h2
  · intro hx
    have e : d * (κ * x * κ⁻¹) * d⁻¹ = d * κ * x * (d * κ)⁻¹ := by group
    have h1 : κ * x * κ⁻¹ ∈ CFSG.conjugate B d := mem_conjugate_iff.mpr (e ▸ hx)
    rw [← hκB] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    have hyx' : y = x := by
      have h2 : κ * y * κ⁻¹ = κ * x * κ⁻¹ := hyx
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← hyx']
    exact hy

theorem index_two_of_conj [Finite G] {Q Rr B V W : Subgroup G} {g w : G} (hQR : Q ≤ Rr)
    (hgR : g ∈ Subgroup.normalizer (Rr : Set G)) (hgB : g ∈ Subgroup.normalizer (B : Set G))
    (hgV1 : ∀ v ∈ V, g⁻¹ * v * g ∈ W) (hgV2 : ∀ x ∈ W, g * x * g⁻¹ ∈ V)
    (hW' : Rr ⊓ Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer (V : Set G) =
      Q ⊓ Subgroup.centralizer (B : Set G))
    (hwR : w ∈ Rr) (hwB : w ∈ Subgroup.centralizer (B : Set G)) (hwW : w ∈ W) (hwQ : w ∉ Q)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hdichR : ∀ x ∈ Rr ⊓ Subgroup.centralizer (B : Set G),
      x ∈ Q ⊓ Subgroup.centralizer (B : Set G) ∨ w⁻¹ * x ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    ((Q ⊓ Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer (W : Set G)).subgroupOf
      (Q ⊓ Subgroup.centralizer (B : Set G))).index = 2 := by
  set CQB := Q ⊓ Subgroup.centralizer (B : Set G) with hCQBdef
  set CRB := Rr ⊓ Subgroup.centralizer (B : Set G) with hCRBdef
  have hgCRB : g ∈ Subgroup.normalizer (CRB : Set G) :=
    mem_normalizer_inf hgR (B2F.normalizer_le_normalizer_centralizer B hgB)
  have hWcard : Nat.card ↥(CRB ⊓ Subgroup.centralizer (W : Set G)) = Nat.card CQB := by
    rw [← hW']
    apply le_antisymm
    · have h1 := map_conj_le_inf_centralizer (R := CRB) (X := W) (Y := V)
        (Subgroup.inv_mem _ hgCRB) (fun v hv => by rw [inv_inv]; exact hgV1 v hv)
      have h2 := Subgroup.card_le_of_le h1
      rwa [Subgroup.card_map_of_injective (MulAut.conj _).injective] at h2
    · have h1 := map_conj_le_inf_centralizer (R := CRB) (X := V) (Y := W) hgCRB hgV2
      have h2 := Subgroup.card_le_of_le h1
      rwa [Subgroup.card_map_of_injective (MulAut.conj _).injective] at h2
  have hwWC : w ∈ Subgroup.centralizer (W : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => hWab y hy w hwW
  have hcard2 : Nat.card ↥(CRB ⊓ Subgroup.centralizer (W : Set G)) =
      2 * Nat.card ↥(CQB ⊓ Subgroup.centralizer (W : Set G)) := by
    refine card_eq_two_mul (fun x hx => ⟨⟨hQR hx.1.1, hx.1.2⟩, hx.2⟩) ⟨⟨hwR, hwB⟩, hwWC⟩
      (fun h1 => hwQ h1.1.1) (fun x hx => ?_)
    rcases hdichR x hx.1 with h1 | h1
    · exact Or.inl ⟨h1, hx.2⟩
    · exact Or.inr ⟨h1, Subgroup.mul_mem _ (Subgroup.inv_mem _ hwWC) hx.2⟩
  have h1 := Subgroup.relIndex_mul_card (H := CQB ⊓ Subgroup.centralizer (W : Set G)) (K := CQB)
  rw [inf_of_le_left inf_le_left] at h1
  have hpos : 0 < Nat.card ↥(CQB ⊓ Subgroup.centralizer (W : Set G)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans (hWcard.symm.trans hcard2))

theorem card_C_Z [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T ≠ ⊥)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6))
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (β : ↥(blockU L) →* Multiplicative A6Coc.Vec4)
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (β u') = A6Coc.act (ρ g) (Multiplicative.toAdd (β u)))
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ sylowS6)
    (hH : (ρ.comp (Subgroup.inclusion hLTN)).range = alternatingGroup (Fin 6) ∨
      (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤)
    (h27 : Stmt3_3_27) {d : G} (hdD : d ∈ D) (hdM : d ∉ M)
    (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T) :
    Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
  obtain ⟨hshort, -⟩ := hA6
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hMp := Hyp331.mPlus_eq_of_le hTL
  obtain ⟨-, -, -, ⟨-, hV4⟩⟩ := stmt3_3_7_of h38 h39 G T M L D h
  rw [hMp] at hV4
  have hVL : ⁅vPlus L T, L⁆ ≤ blockU L :=
    (Subgroup.commutator_mono hVQ le_rfl).trans (Hyp331.commutator_qL_le_blockU hshort hTL)
  have hZV : quasithinOmegaOneCenter T ≤ vPlus L T := le_conjClosure _ _
  have hUL : blockU L ≤ L := commutator_le_right_of_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
  have hCZU : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.normalizer (blockU L : Set G) :=
    fun c hc => Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hUL hc.2)
  have hZdec : ∀ z ∈ quasithinOmegaOneCenter T, ∃ u ∈ quasithinOmegaOneCenter T ⊓ blockU L,
      ∃ c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G), z = u * c := by
    intro z hz
    have h1 : z ∈ blockU L ⊔ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := by
      have h2 := hZV hz
      rw [hV4] at h2
      exact (sup_le_sup_right hVL _) h2
    obtain ⟨u, hu, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCZU).mp h1
    refine ⟨u, ⟨?_, hu⟩, c, hc, rfl⟩
    have := (quasithinOmegaOneCenter T).mul_mem hz ((quasithinOmegaOneCenter T).inv_mem hc.1)
    rwa [mul_inv_cancel_right] at this
  obtain ⟨t₁, ht₁, e₁⟩ := CZA6.mem_image_sylow ρ hLTN hTidx (fun t ht => hρT t ht) hH
    CZA6.b1_mem_sylowS6 b1_mem_alt
  obtain ⟨t₂, ht₂, e₂⟩ := CZA6.mem_image_sylow ρ hLTN hTidx (fun t ht => hρT t ht) hH
    CZA6.s1_mem_sylowS6 s1_mem_alt
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hfixZ : ∀ u : ↥(blockU L), (u : G) ∈ quasithinOmegaOneCenter T →
      Multiplicative.toAdd (β u) = 0 ∨ Multiplicative.toAdd (β u) = CZA6.w0 := by
    intro u huZ
    have hfix : ∀ t (ht : t ∈ T), A6Coc.act (ρ ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩)
        (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β u) := by
      intro t ht
      have e := hβe ⟨t, hLTN (Subgroup.mem_sup_right ht)⟩ u u (by
        have h1 := Subgroup.mem_centralizer_iff.mp (hTZ ht) u huZ
        show (u : G) = t * u * t⁻¹
        rw [← h1]
        group)
      exact e.symm
    apply CZA6.fix_D8
    · rw [← e₁]
      exact hfix t₁ ht₁
    · rw [← e₂]
      exact hfix t₂ ht₂
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hZT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le _).mpr fun z hz => hz.1.1
  have hAC : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≤ tC L T :=
    fun z hz => ⟨hZT hz.1, hz.2⟩
  have hAd : CFSG.conjugate (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) d ≤
      quasithinOmegaOneCenter T := fun x hx => by
    have h1 := (mem_conjugate_iff.mp hx).1
    have := conj_mem_omegaOneCenter (Subgroup.inv_mem _ hdT) h1
    simpa [mul_assoc] using this
  have hAAd : (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) ⊓
      CFSG.conjugate (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) d = ⊥ := by
    have h1 := (h27 G T M L D h d hdD hdM hdV hTC).1
    rw [eq_bot_iff] at h1 ⊢
    intro x hx
    exact h1 ⟨hAC hx.1, mem_conjugate_iff.mpr (hAC (mem_conjugate_iff.mp hx.2))⟩
  have hcardAd : Nat.card (CFSG.conjugate
      (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) d) =
      Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) :=
    Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective
  obtain ⟨z, hzZ, hz1, -, hzL, -⟩ := h.exists_involution_tC hTL hTC
  have hA1 : 1 < Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    have hz : z ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := ⟨hzZ, hzL⟩
    rw [hbot, Subgroup.mem_bot] at hz
    exact hz1 hz
  exact card_inf_centralizer_eq_two β hβk hZdec hfixZ hAd hAAd hcardAd hA1

theorem rest_S [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6))
    (hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G))
    (β : ↥(blockU L) →* Multiplicative A6Coc.Vec4) (hβs : Function.Surjective β)
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (β u') = A6Coc.act (ρ g) (Multiplicative.toAdd (β u)))
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ sylowS6)
    (hρ1 : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 ↔ g ∈ qL L T)
    {d : G} (hdT : d ∈ Subgroup.normalizer (T : Set G))
    (hdP : d ∈ Subgroup.normalizer (pre ρ hLTN p1 : Set G))
    (hdR : d ∈ Subgroup.normalizer (pre ρ hLTN r1 : Set G))
    (hRP : pCoreOf 2 (pre ρ hLTN p1) = pre ρ hLTN r1)
    (hCVQ : ∀ g ∈ L ⊔ T, g ∈ Subgroup.centralizer (vPlus L T : Set G) → g ∈ qL L T)
    (hVdLT : CFSG.conjugate (vPlus L T) d ≤ L ⊔ T)
    (hρVd : ∀ x (hx : x ∈ CFSG.conjugate (vPlus L T) d),
      ρ ⟨x, hLTN (hVdLT hx)⟩ = 1 ∨ ρ ⟨x, hLTN (hVdLT hx)⟩ = c45)
    (htop : (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤)
    (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T)
    {ℓc : G} (hℓc : ℓc ∈ L) (hρℓc : ρ ⟨ℓc, Subgroup.le_normalizer hℓc⟩ = CZA6.c012)
    (hℓcP : ℓc ∈ pre ρ hLTN p1) :
    d ∈ Subgroup.normalizer ((qL L T ⊔ CFSG.conjugate (vPlus L T) d : Subgroup G) : Set G) ∧
      CFSG.conjugate (vPlus L T) d ≤ Subgroup.centralizer (tC L T : Set G) ∧
      qL L T = vPlus L T ⊔
        (qL L T ⊓ Subgroup.centralizer (CFSG.conjugate (vPlus L T) d : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, -⟩ := hA6
  set V := vPlus L T with hVdef
  set Q := qL L T with hQdef
  set C := tC L T with hCdef
  set Vd := CFSG.conjugate V d with hVddef
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : V ≤ Q := hred.1.trans inf_le_left
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hQLT : Q ≤ L ⊔ T := hQT.trans le_sup_right
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hred.2.1.1
    exact setLike_mul_comm ha hb
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hUV : blockU L ≤ V := h.blockU_le_vPlus h38 h39 hshort hTL
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.2.2.1
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hCQ : C ≤ Q := h.tC_le_qL h38 h39 hTL
  have hVT : V ≤ T := hVQ.trans hQT
  have hQU : ⁅Q, L⁆ ≤ blockU L := Hyp331.commutator_qL_le_blockU hshort hTL
  have hdinv : ∀ {H : Subgroup G}, d ∈ Subgroup.normalizer (H : Set G) → ∀ x,
      d * x * d⁻¹ ∈ H → x ∈ H := by
    intro H hd x hx
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd) _).mp hx
    simpa [mul_assoc] using this
  have hQR : Q ≤ pre ρ hLTN r1 := fun g hg => (mem_pre ρ hLTN).mpr ⟨hQLT hg, by
    rw [(hρ1 g (hQLT hg)).mpr hg]
    exact Subgroup.one_mem _⟩
  have hVdT : Vd ≤ T := fun x hx => hdinv hdT x (hVT (mem_conjugate_iff.mp hx))
  have hVdR : Vd ≤ pre ρ hLTN r1 := fun x hx => hdinv hdR x (hQR (hVQ (mem_conjugate_iff.mp hx)))
  have hconjVd : ∀ g, d * g * d⁻¹ ∈ Subgroup.normalizer (V : Set G) → ∀ x ∈ Vd,
      g * x * g⁻¹ ∈ Vd := by
    intro g hg x hx
    rw [mem_conjugate_iff] at hx ⊢
    have e : d * (g * x * g⁻¹) * d⁻¹ = (d * g * d⁻¹) * (d * x * d⁻¹) * (d * g * d⁻¹)⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hx
  have hTVd : ∀ g ∈ T, ∀ x ∈ Vd, g * x * g⁻¹ ∈ Vd := fun g hg =>
    hconjVd g (hLTV (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hdT g).mp hg)))
  have hPVd : ∀ g ∈ pre ρ hLTN p1, ∀ x ∈ Vd, g * x * g⁻¹ ∈ Vd := fun g hg =>
    hconjVd g (hLTV (pre_le_sup ρ hLTN p1 ((Subgroup.mem_normalizer_iff.mp hdP g).mp hg)))
  have hVdab : ∀ a ∈ Vd, ∀ b ∈ Vd, a * b = b * a := by
    intro a ha b hb
    have h1 := hVab _ (mem_conjugate_iff.mp ha) _ (mem_conjugate_iff.mp hb)
    have e : d * (a * b) * d⁻¹ = d * (b * a) * d⁻¹ := by
      calc d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
        _ = (d * b * d⁻¹) * (d * a * d⁻¹) := h1
        _ = d * (b * a) * d⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  obtain ⟨k, hb3, hρb⟩ := exists_pow_eq ρ hLTN hQ2 hρ1 hℓc hρℓc
  have hbL : ℓc ^ 4 ^ k ∈ L := L.pow_mem hℓc _
  have hbN : ℓc ^ 4 ^ k ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hbL
  have hb1 : ℓc ^ 4 ^ k ≠ 1 := by
    intro h1
    apply c012_ne_one
    rw [← hρb]
    have e : (⟨ℓc ^ 4 ^ k, Subgroup.le_normalizer hbL⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      1 := Subtype.ext h1
    rw [e, map_one]
  have hB3 : Nat.card (Subgroup.zpowers (ℓc ^ 4 ^ k)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hBL : Subgroup.zpowers (ℓc ^ 4 ^ k) ≤ L := Subgroup.zpowers_le.mpr hbL
  have hBP : Subgroup.zpowers (ℓc ^ 4 ^ k) ≤ pre ρ hLTN p1 :=
    Subgroup.zpowers_le.mpr ((pre ρ hLTN p1).pow_mem hℓcP _)
  have hρB : ∀ g (hg : g ∈ Subgroup.zpowers (ℓc ^ 4 ^ k)),
      ρ ⟨g, Subgroup.le_normalizer (hBL hg)⟩ ∈ Subgroup.zpowers CZA6.c012 := by
    intro g hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have e : (⟨(ℓc ^ 4 ^ k) ^ i, Subgroup.le_normalizer (hBL hg)⟩ :
        ↥(Subgroup.normalizer (L : Set G))) = ⟨ℓc ^ 4 ^ k, hbN⟩ ^ i := rfl
    rw [e, map_zpow, hρb]
    exact Subgroup.zpow_mem_zpowers _ _
  set B := Subgroup.zpowers (ℓc ^ 4 ^ k) with hBdef
  have hTP : T ≤ pre ρ hLTN p1 := fun t ht =>
    (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_right ht, sylowS6_le_p1 (hρT t ht)⟩
  have hPT := card_pre_p1 ρ hLTN hT2 hTidx hQ2 hQLT htop hρ1 hTP
  obtain ⟨κ, hκT, hd'B⟩ := exists_mul_mem_normalizer hTP hT2 hPT hBP hB3 hdP
  have hd'T : d * κ ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.mul_mem _ hdT (Subgroup.le_normalizer hκT)
  have hκR : κ ∈ Subgroup.normalizer (pre ρ hLTN r1 : Set G) := by
    rw [← hRP]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hTP hκT)
  have hd'R : d * κ ∈ Subgroup.normalizer (pre ρ hLTN r1 : Set G) := Subgroup.mul_mem _ hdR hκR
  have hd'V1 : ∀ v ∈ V, (d * κ)⁻¹ * v * (d * κ) ∈ Vd := by
    intro v hv
    have h1 : d⁻¹ * v * d ∈ Vd := mem_conjugate_iff.mpr (by simpa [mul_assoc] using hv)
    have h2 := hTVd κ⁻¹ (T.inv_mem hκT) _ h1
    have e : (d * κ)⁻¹ * v * (d * κ) = κ⁻¹ * (d⁻¹ * v * d) * κ⁻¹⁻¹ := by group
    rw [e]
    exact h2
  have hd'V2 : ∀ x ∈ Vd, (d * κ) * x * (d * κ)⁻¹ ∈ V := by
    intro x hx
    have h1 := hTVd κ hκT x hx
    have e : (d * κ) * x * (d * κ)⁻¹ = d * (κ * x * κ⁻¹) * d⁻¹ := by group
    rw [e]
    exact mem_conjugate_iff.mp h1
  have hBVd : B ≤ Subgroup.normalizer (Vd : Set G) := fun g hg =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hPVd g (hBP hg) x hx, fun hx => by
      have := hPVd g⁻¹ ((pre ρ hLTN p1).inv_mem (hBP hg)) _ hx
      simpa [mul_assoc] using this⟩
  have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := (hBL.trans le_sup_left).trans hLTQ
  have hcopB : ∀ {H : Subgroup G}, IsPGroup 2 ↥H → Nat.Coprime (Nat.card B) (Nat.card H) := by
    intro H hH
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
    rw [hB3, hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hsolv : ∀ {H : Subgroup G}, IsPGroup 2 ↥H → Group.IsSolvable ↥H := by
    intro H hH
    have := hH.isNilpotent
    infer_instance
  have hVd2 : IsPGroup 2 ↥Vd := hT2.to_le hVdT
  have hVdBQ : ⁅Vd, B⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro x hx g hg
    have hxLT : x ∈ L ⊔ T := hVdLT hx
    have hgLT : g ∈ L ⊔ T := Subgroup.mem_sup_left (hBL hg)
    have hm : ⁅x, g⁆ ∈ L ⊔ T := (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).mul_mem hxLT hgLT)
      ((L ⊔ T).inv_mem hxLT)) ((L ⊔ T).inv_mem hgLT)
    rw [← hρ1 _ hm]
    have e : (⟨⁅x, g⁆, hLTN hm⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⁅(⟨x, hLTN hxLT⟩ : ↥(Subgroup.normalizer (L : Set G))), ⟨g, hLTN hgLT⟩⁆ := rfl
    rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    have hρg : ρ ⟨g, hLTN hgLT⟩ ∈ Subgroup.zpowers CZA6.c012 := hρB g hg
    rcases hρVd x hx with h1 | h1
    · rw [h1, one_mul, mul_one]
    · rw [h1]
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hρg
      rw [← hi]
      exact ((Commute.zpow_right c45_comm i) : Commute c45 (CZA6.c012 ^ i)).eq
  have hVdcop := CFSG.Walter.le_sup_commutator_of_coprime hBVd (hsolv hVd2) (hcopB hVd2)
  obtain ⟨w, ⟨hwVd, hwB⟩, hwQ⟩ : ∃ w ∈ Vd ⊓ Subgroup.centralizer (B : Set G), w ∉ Q := by
    by_contra hcon
    push Not at hcon
    exact hdV (hVdcop.trans (sup_le (fun x hx => hcon x hx) hVdBQ))
  have hwLT : w ∈ L ⊔ T := hVdLT hwVd
  have hwρ : ρ ⟨w, hLTN hwLT⟩ = c45 := by
    rcases hρVd w hwVd with h1 | h1
    · exact absurd ((hρ1 w hwLT).mp h1) hwQ
    · exact h1
  have hcentρ : ∀ x (hx : x ∈ L ⊔ T), x ∈ Subgroup.centralizer (B : Set G) →
      ρ ⟨x, hLTN hx⟩ * CZA6.c012 = CZA6.c012 * ρ ⟨x, hLTN hx⟩ := by
    intro x hx hxB
    have h1 : ℓc ^ 4 ^ k * x = x * ℓc ^ 4 ^ k :=
      Subgroup.mem_centralizer_iff.mp hxB _ (Subgroup.mem_zpowers _)
    have e : (⟨x, hLTN hx⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨ℓc ^ 4 ^ k, hbN⟩ =
        ⟨ℓc ^ 4 ^ k, hbN⟩ * ⟨x, hLTN hx⟩ := Subtype.ext h1.symm
    rw [← hρb, ← map_mul, e, map_mul]
  have hw' : ∀ x (hx : x ∈ L ⊔ T), ρ ⟨x, hLTN hx⟩ = c45 → w⁻¹ * x ∈ Q := by
    intro x hx h1
    have hm : w⁻¹ * x ∈ L ⊔ T := (L ⊔ T).mul_mem ((L ⊔ T).inv_mem hwLT) hx
    rw [← hρ1 _ hm]
    have e : (⟨w⁻¹ * x, hLTN hm⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        (⟨w, hLTN hwLT⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨x, hLTN hx⟩ := rfl
    rw [e, map_mul, map_inv, hwρ, h1, inv_mul_cancel]
  have hdichR : ∀ x ∈ pre ρ hLTN r1 ⊓ Subgroup.centralizer (B : Set G),
      x ∈ Q ⊓ Subgroup.centralizer (B : Set G) ∨
        w⁻¹ * x ∈ Q ⊓ Subgroup.centralizer (B : Set G) := by
    intro x hx
    have hxLT : x ∈ L ⊔ T := pre_le_sup ρ hLTN r1 hx.1
    have hσ : ρ ⟨x, hLTN hxLT⟩ ∈ elemsR1 := by
      rw [← mem_r1_iff]
      exact ((mem_pre ρ hLTN).mp hx.1).2
    rcases cent_check_R _ hσ (hcentρ x hxLT hx.2) with h1 | h1
    · exact Or.inl ⟨(hρ1 x hxLT).mp h1, hx.2⟩
    · exact Or.inr ⟨hw' x hxLT h1, Subgroup.mul_mem _ (Subgroup.inv_mem _ hwB) hx.2⟩
  have hW' : pre ρ hLTN r1 ⊓ Subgroup.centralizer (B : Set G) ⊓
      Subgroup.centralizer (V : Set G) = Q ⊓ Subgroup.centralizer (B : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨hxR, hxB⟩, hxV⟩
      exact ⟨hCVQ x (pre_le_sup ρ hLTN r1 hxR) hxV, hxB⟩
    · rintro ⟨hxQ, hxB⟩
      exact ⟨⟨hQR hxQ, hxB⟩, hQV hxQ⟩
  have hidx2 := index_two_of_conj hQR hd'R hd'B hd'V1 hd'V2 hW' (hVdR hwVd) hwB hwVd hwQ
    hVdab hdichR
  have hUab : ∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x := fun x hx y hy =>
    hVab x (hUV hx) y (hUV hy)
  have hwN : w ∈ Subgroup.normalizer (L : Set G) := hLTN hwLT
  obtain ⟨v₁, hv₁U, hv₁B, hv₁w⟩ := exists_v₁ ρ β hβs hβk hβe hUab hbN hb3 hρb hwN hwρ
  have hv₁K : v₁ ∈ Q ⊓ Subgroup.centralizer (B : Set G) := ⟨hVQ (hUV hv₁U), hv₁B⟩
  have hCN : T ≤ Subgroup.normalizer (C : Set G) := Hyp331.le_normalizer_tC hTL
  have hCV := le_of_index_two (C := C) (K := Q ⊓ Subgroup.centralizer (B : Set G))
    (W := Vd) hidx2
    (fun t ht => ⟨hCQ ht, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBL) ht.2⟩)
    inf_le_right hwVd
    (fun t ht => (C.mul_mem ht ((Subgroup.mem_normalizer_iff.mp (hCN (hVdT hwVd)) _).mp
      (C.inv_mem ht))).2) hv₁K hv₁w
  have hVdC : Vd ≤ Subgroup.centralizer (C : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hCV ht).2 x hx).symm
  have hv₁Kw : v₁ ∉ Q ⊓ Subgroup.centralizer (B : Set G) ⊓ Subgroup.centralizer (Vd : Set G) := by
    intro h1
    apply hv₁w
    have h2 : w * v₁ = v₁ * w := Subgroup.mem_centralizer_iff.mp h1.2 w hwVd
    have e : v₁ * w * v₁⁻¹ * w⁻¹ = 1 := by
      rw [← h2]
      group
    rw [e]
    exact Subgroup.one_mem _
  have hCQBle := le_sup_of_index_two hidx2 hv₁K (hUV hv₁U) hv₁Kw
  have hQcop := CFSG.Walter.le_sup_commutator_of_coprime hBQ (hsolv hQ2) (hcopB hQ2)
  have hQBU : ⁅Q, B⁆ ≤ blockU L := (Subgroup.commutator_mono le_rfl hBL).trans hQU
  have hQ4 : Q = V ⊔ (Q ⊓ Subgroup.centralizer (Vd : Set G)) := by
    refine le_antisymm ?_ (sup_le hVQ inf_le_left)
    refine hQcop.trans (sup_le (hCQBle.trans (sup_le_sup_left (fun x hx => ⟨hx.1.1, hx.2⟩) V))
      ((hQBU.trans hUV).trans le_sup_left))
  have hdouble : ∀ {H : Subgroup G}, IsPGroup 2 ↥H → B ≤ Subgroup.normalizer (H : Set G) →
      ⁅⁅H, B⁆, B⁆ = ⁅H, B⁆ := fun hH hBH =>
    double_commutator_eq B _ hBH (hcopB hH) (hsolv hH)
  have hQVB : ⁅Q, B⁆ ≤ ⁅V, B⁆ := by
    rw [← hdouble hQ2 hBQ]
    exact Subgroup.commutator_mono (hQBU.trans hUV) le_rfl
  have hVdVB : ⁅Vd, B⁆ ≤ ⁅V, B⁆ := by
    rw [← hdouble hVd2 hBVd]
    exact (Subgroup.commutator_mono hVdBQ le_rfl).trans hQVB
  have hTB : T ⊓ Subgroup.centralizer (B : Set G) ≤ Q ⊔ Vd := by
    intro x hx
    have hxLT : x ∈ L ⊔ T := Subgroup.mem_sup_right hx.1
    have hσ : ρ ⟨x, hLTN hxLT⟩ ∈ S6Syl.elemsS := by
      have := hρT x hx.1
      rw [S6Syl.sylowS6_eq] at this
      exact this
    rcases cent_check_S _ hσ (hcentρ x hxLT hx.2) with h1 | h1
    · exact Subgroup.mem_sup_left ((hρ1 x hxLT).mp h1)
    · have e : x = w * (w⁻¹ * x) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hwVd)
        (Subgroup.mem_sup_left (hw' x hxLT h1))
  have hSle : Q ⊔ Vd ≤ (T ⊓ Subgroup.centralizer (B : Set G)) ⊔ ⁅V, B⁆ := by
    apply sup_le
    · exact hQcop.trans (sup_le_sup (fun x hx => ⟨hQT hx.1, hx.2⟩) hQVB)
    · exact hVdcop.trans (sup_le_sup (fun x hx => ⟨hVdT hx.1, hx.2⟩) hVdVB)
  have hmapV : V.map (MulAut.conj (d * κ)⁻¹).toMonoidHom ≤ Vd := by
    rintro _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hd'V1 v hv
  have hmapB : B.map (MulAut.conj (d * κ)⁻¹).toMonoidHom ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd'B) x).mp hx
  have hmapTB : (T ⊓ Subgroup.centralizer (B : Set G)).map
      (MulAut.conj (d * κ)⁻¹).toMonoidHom ≤ T ⊓ Subgroup.centralizer (B : Set G) :=
    map_conj_le_inf_centralizer hd'T fun y hy => (Subgroup.mem_normalizer_iff.mp hd'B y).mp hy
  have hd'S := mem_normalizer_of_le hSle (hmapTB.trans hTB) hmapV hmapB
    (hVdBQ.trans le_sup_left)
  have hκS : κ ∈ Subgroup.normalizer ((Q ⊔ Vd : Subgroup G) : Set G) :=
    C1.mem_normalizer_sup (hLTQ (Subgroup.mem_sup_right hκT))
      (Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hTVd κ hκT x hx, fun hx => by
        have := hTVd κ⁻¹ (T.inv_mem hκT) _ hx
        simpa [mul_assoc] using this⟩)
  have hdS : d ∈ Subgroup.normalizer ((Q ⊔ Vd : Subgroup G) : Set G) := by
    have e : d = (d * κ) * κ⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hd'S (Subgroup.inv_mem _ hκS)
  exact ⟨hdS, hVdC, hQ4⟩

theorem step3_3_31S_aux [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h25 : Stmt3_3_25) (h27 : Stmt3_3_27)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T ≠ ⊥) {d : G} (hdD : d ∈ D)
    (hdM : d ∉ M) (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T) :
    (qL L T).relIndex (qL L T ⊔ CFSG.conjugate (vPlus L T) d) = 2 ∧
      d ∈ Subgroup.normalizer ((qL L T ⊔ CFSG.conjugate (vPlus L T) d : Subgroup G) : Set G) ∧
      CFSG.conjugate (vPlus L T) d ≤ Subgroup.centralizer (tC L T : Set G) ∧
      qL L T = vPlus L T ⊔
        (qL L T ⊓ Subgroup.centralizer (CFSG.conjugate (vPlus L T) d : Set G)) ∧
      T = T ⊓ L ⊔ qL L T ⊔ CFSG.conjugate (vPlus L T) d ∧
      Nat.card ↥(quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hshort, α, hA⟩ := id hA6
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := vPlus L T with hVdef
  set Q := qL L T with hQdef
  set C := tC L T with hCdef
  set U := blockU L with hUdef
  set Vd := CFSG.conjugate V d with hVddef
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : V ≤ Q := hred.1.trans inf_le_left
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hQLT : Q ≤ L ⊔ T := hQT.trans le_sup_right
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hred.2.1.1
    exact setLike_mul_comm ha hb
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hUV : U ≤ V := h.blockU_le_vPlus h38 h39 hshort hTL
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := hred.2.2.2.1
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hCQ : C ≤ Q := h.tC_le_qL h38 h39 hTL
  have hVT : V ≤ T := hVQ.trans hQT
  have hQU : ⁅Q, L⁆ ≤ U := Hyp331.commutator_qL_le_blockU hshort hTL
  obtain ⟨ρ, β, hβs, hβk, hβe, hρT, hρL, -, hker, hK, hX⟩ :=
    CZA6.exists_rho_cZ h38 h39 h hA6 hTL
  have hρ1 : ∀ g (hg : g ∈ L ⊔ T), ρ ⟨g, hLTN hg⟩ = 1 ↔ g ∈ Q := fun g hg =>
    ⟨hK g hg _, fun hgQ => (hker g hg _).mpr (hQV hgQ)⟩
  have hH := eq_alternatingGroup_or_eq_top (H := (ρ.comp (Subgroup.inclusion hLTN)).range)
    (fun s hs => by
      obtain ⟨ℓ, hℓ, e⟩ := hρL s hs
      exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩)
  obtain ⟨-, -, hYT, -, hRP, -⟩ := parabolic ρ hLTN hT2 hTidx
    (fun g hg h1 => hK g hg (hLTN hg) h1) (fun t ht => hρT t ht) hρL hH
    sylowS6_le_p1 r1_le_p1 p1_le_normalizer (fun x hx => sq_eq_one_of_mem_r1 hx) card_p1 card_r1
    c45_mem_r1 s1_mem_alt t1_mem_alt s1_mem_p1 t1_mem_p1 comm_not_mem_r1
  have hPSL : ¬ IsPSL 3 2 1 ↥(autOn L V) := by
    intro hP
    have h1 := h.card_autOn_dvd hTL
    have h2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
      obtain ⟨hαs, hαk, -⟩ := hA
      rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
        nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [Vol2.Ch11.SecA.card_of_isPSL (by norm_num) hP, h2] at h1
    revert h1
    decide
  obtain ⟨-, h25b, -⟩ := h25 G T M L D h
  obtain ⟨hDY, hDR, -⟩ := h25b hTC hPSL
  have hYP : oTwoUpper (L ⊓ Subgroup.centralizer (Z : Set G)) ⊔ T = pre ρ hLTN p1 := by
    rw [hX, hYT]
  have hdR : d ∈ Subgroup.normalizer (pre ρ hLTN r1 : Set G) := by
    have := hDR hdD
    rwa [hYP, hRP] at this
  have hdP : d ∈ Subgroup.normalizer (pre ρ hLTN p1 : Set G) := by
    rw [← hYP]
    exact C1.mem_normalizer_sup (hDY hdD) hdT
  have hdinv : ∀ {H : Subgroup G}, d ∈ Subgroup.normalizer (H : Set G) → ∀ x,
      d * x * d⁻¹ ∈ H → x ∈ H := by
    intro H hd x hx
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd) _).mp hx
    simpa [mul_assoc] using this
  have hQR : Q ≤ pre ρ hLTN r1 := fun g hg => (mem_pre ρ hLTN).mpr ⟨hQLT hg, by
    rw [(hρ1 g (hQLT hg)).mpr hg]
    exact Subgroup.one_mem _⟩
  have hVdT : Vd ≤ T := fun x hx => hdinv hdT x (hVT (mem_conjugate_iff.mp hx))
  have hVdR : Vd ≤ pre ρ hLTN r1 := fun x hx => hdinv hdR x (hQR (hVQ (mem_conjugate_iff.mp hx)))
  have hVdLT : Vd ≤ L ⊔ T := hVdT.trans le_sup_right
  have hconjVd : ∀ g, d * g * d⁻¹ ∈ Subgroup.normalizer (V : Set G) → ∀ x ∈ Vd,
      g * x * g⁻¹ ∈ Vd := by
    intro g hg x hx
    rw [mem_conjugate_iff] at hx ⊢
    have e : d * (g * x * g⁻¹) * d⁻¹ = (d * g * d⁻¹) * (d * x * d⁻¹) * (d * g * d⁻¹)⁻¹ := by
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hx
  have hTVd : ∀ g ∈ T, ∀ x ∈ Vd, g * x * g⁻¹ ∈ Vd := fun g hg =>
    hconjVd g (hLTV (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hdT g).mp hg)))
  have hPVd : ∀ g ∈ pre ρ hLTN p1, ∀ x ∈ Vd, g * x * g⁻¹ ∈ Vd := fun g hg =>
    hconjVd g (hLTV (pre_le_sup ρ hLTN p1 ((Subgroup.mem_normalizer_iff.mp hdP g).mp hg)))
  have hVdab : ∀ a ∈ Vd, ∀ b ∈ Vd, a * b = b * a := by
    intro a ha b hb
    have h1 := hVab _ (mem_conjugate_iff.mp ha) _ (mem_conjugate_iff.mp hb)
    have e : d * (a * b) * d⁻¹ = d * (b * a) * d⁻¹ := by
      calc d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
        _ = (d * b * d⁻¹) * (d * a * d⁻¹) := h1
        _ = d * (b * a) * d⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  obtain ⟨ℓc, hℓc, hρℓc⟩ := hρL CZA6.c012 CZA6.c012_mem_alt
  have hℓcP : ℓc ∈ pre ρ hLTN p1 := (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hℓc, by
    rw [hρℓc]
    exact CZA6.c012_mem_p1⟩
  have hρVd := rho_eq_of_quad ρ hLTN β hβs hβe hVdLT
    (fun x hx => ((mem_pre ρ hLTN).mp (hVdR hx)).2) hVdab
    (fun u hu x hx => hTVd u (hVT (hUV hu)) x hx) hℓc hρℓc (fun x hx => hPVd ℓc hℓcP x hx)
  obtain ⟨w₀, hw₀Vd, hw₀Q⟩ := Set.not_subset.mp hdV
  have hw₀ρ : ρ ⟨w₀, hLTN (hVdLT hw₀Vd)⟩ = c45 := by
    rcases hρVd w₀ hw₀Vd with h1 | h1
    · exact absurd ((hρ1 w₀ (hVdLT hw₀Vd)).mp h1) hw₀Q
    · exact h1
  have htop : (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤ := by
    rcases hH with hA' | hT'
    · exfalso
      have h1 : c45 ∈ (ρ.comp (Subgroup.inclusion hLTN)).range :=
        ⟨⟨w₀, hVdLT hw₀Vd⟩, hw₀ρ⟩
      rw [hA'] at h1
      exact c45_not_mem_alt h1
    · exact hT'
  have hrel := relIndex_sup_eq_two ρ hLTN hQLT hVdLT (hVdLT.trans hLTQ) hρ1 hρVd hw₀Vd hw₀ρ
  have hT5 := eq_inf_sup_sup ρ hLTN hTL hρL hρ1 hQT hVdT hw₀Vd hw₀ρ
  have hZ2 := card_C_Z h38 h39 h hA6 hTL hTC ρ hLTN β hβk hβe hρT hH h27 hdD hdM hdV
  obtain ⟨hdS, hVdC, hQ4⟩ := rest_S h38 h39 h hA6 hTL ρ hLTN β hβs hβk hβe hρT hρ1 hdT hdP
    hdR hRP (fun g hg hgV => (hρ1 g hg).mp ((hker g hg _).mpr hgV)) hVdLT hρVd htop hdV hℓc hρℓc
    hℓcP
  exact ⟨hrel, hdS, hVdC, hQ4, hT5, hZ2⟩

theorem step3_3_31S_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h25 : Stmt3_3_25) (h27 : Stmt3_3_27) : Step3_3_31S := by
  intro G _ _ T M L D h hA6 hTL hTC d hdD hdM hdV
  exact step3_3_31S_aux h38 h39 h25 h27 h hA6 hTL hTC hdD hdM hdV



end Lem3331S

end CFSG.Quasithin.H13
