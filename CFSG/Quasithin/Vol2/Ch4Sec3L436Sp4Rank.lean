module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4End
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436
open scoped IsMulCommutative commutatorElement

namespace L436

theorem pow_val_add_of_pow_eq_one {M : Type*} [Monoid M] {p : ℕ} [NeZero p] {g : M}
    (hg : g ^ p = 1) (a b : ZMod p) : g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

theorem three_le_pRank_of_commute {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y c : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hc : c ^ p = 1) (hxy : x * y = y * x)
    (hxc : x * c = c * x) (hyc : y * c = c * y)
    (hind : ∀ a b d : ZMod p, x ^ a.val * y ^ b.val * c ^ d.val = 1 → a = 0 ∧ b = 0 ∧ d = 0) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  set T := Subgroup.closure ({x, y, c} : Set G) with hT
  have hTc : IsMulCommutative T := by
    refine Subgroup.isMulCommutative_closure ?_
    rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) - <;>
      first
        | exact Commute.refl _
        | exact hxy
        | exact hxy.symm
        | exact hxc
        | exact hxc.symm
        | exact hyc
        | exact hyc.symm
  set x' : T := ⟨x, Subgroup.subset_closure (by simp)⟩
  set y' : T := ⟨y, Subgroup.subset_closure (by simp)⟩
  set c' : T := ⟨c, Subgroup.subset_closure (by simp)⟩
  have hx' : x' ^ p = 1 := Subtype.ext (by simpa using hx)
  have hy' : y' ^ p = 1 := Subtype.ext (by simpa using hy)
  have hc' : c' ^ p = 1 := Subtype.ext (by simpa using hc)
  let f : Multiplicative (Fin 3 → ZMod p) →* T :=
    { toFun := fun v => x' ^ (Multiplicative.toAdd v 0).val * y' ^ (Multiplicative.toAdd v 1).val *
        c' ^ (Multiplicative.toAdd v 2).val
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Pi.add_apply, pow_val_add_of_pow_eq_one hx',
          pow_val_add_of_pow_eq_one hy', pow_val_add_of_pow_eq_one hc']
        rw [mul_mul_mul_comm (x' ^ _ * y' ^ _), mul_mul_mul_comm (x' ^ _) (y' ^ _)] }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h := hind (Multiplicative.toAdd v 0) (Multiplicative.toAdd v 1) (Multiplicative.toAdd v 2)
      (congrArg Subtype.val hv)
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  set E := (T.subtype.comp f).range with hE
  have hinj : Function.Injective (T.subtype.comp f) := Subtype.val_injective.comp hf
  have hcard : Nat.card E = p ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have hEl : CFSG.Open.IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, v, rfl⟩ := a
      obtain ⟨_, w, rfl⟩ := b
      apply Subtype.ext
      change (T.subtype.comp f) v * (T.subtype.comp f) w =
        (T.subtype.comp f) w * (T.subtype.comp f) v
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨v, rfl⟩
      rw [← map_pow]
      have : v ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul,
          CharP.cast_eq_zero, zero_mul]
      rw [this, map_one]
  exact CFSG.SectionRank.le_pRank hp.out.one_lt le_top hEl hcard

section Commuting

variable {Ω : Type*} [Group Ω]

theorem conj_mem_sSup {𝓢 : Set (Subgroup Ω)} {g : Ω}
    (h : ∀ D ∈ 𝓢, ∀ d ∈ D, g * d * g⁻¹ ∈ sSup 𝓢) : ∀ x ∈ sSup 𝓢, g * x * g⁻¹ ∈ sSup 𝓢 := by
  intro x hx
  have hle : sSup 𝓢 ≤ (sSup 𝓢).comap (MulAut.conj g).toMonoidHom :=
    sSup_le fun D hD d hd => by
      simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact h D hD d hd
  have := hle hx
  simpa [MulAut.conj_apply] using this

theorem sSup_eq_sup_sSup_diff {𝓛 : Set (Subgroup Ω)} {A : Subgroup Ω} (hA : A ∈ 𝓛) :
    sSup 𝓛 = A ⊔ sSup (𝓛 \ {A}) := by
  have e : 𝓛 = insert A (𝓛 \ {A}) := by
    ext B
    by_cases h : B = A
    · subst h
      simp [hA]
    · simp [h]
  calc sSup 𝓛 = sSup (insert A (𝓛 \ {A})) := by rw [← e]
    _ = A ⊔ sSup (𝓛 \ {A}) := sSup_insert

variable {𝓛 : Set (Subgroup Ω)}
  (hcomm : ∀ A ∈ 𝓛, ∀ B ∈ 𝓛, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
include hcomm

theorem sSup_diff_le_centralizer {A : Subgroup Ω} (hA : A ∈ 𝓛) :
    sSup (𝓛 \ {A}) ≤ Subgroup.centralizer (A : Set Ω) :=
  sSup_le fun B hB b hb => Subgroup.mem_centralizer_iff.mpr fun a ha =>
    hcomm A hA B hB.1 (fun h => hB.2 h.symm) a ha b hb

theorem conj_mem_of_mem {A B : Subgroup Ω} (hA : A ∈ 𝓛) (hB : B ∈ 𝓛) :
    ∀ g ∈ A, ∀ b ∈ B, g * b * g⁻¹ ∈ B := by
  intro g hg b hb
  by_cases h : A = B
  · subst h
    exact mul_mem (mul_mem hg hb) (inv_mem hg)
  · rw [hcomm A hA B hB h g hg b hb, mul_inv_cancel_right]
    exact hb

theorem sSup_le_normalizer {B : Subgroup Ω} (hB : B ∈ 𝓛) :
    sSup 𝓛 ≤ Subgroup.normalizer (B : Set Ω) := sSup_le fun A hA g hg => by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨fun hb => conj_mem_of_mem hcomm hA hB g hg b hb, fun hb => ?_⟩
  have := conj_mem_of_mem hcomm hA hB g⁻¹ (inv_mem hg) _ hb
  simpa [mul_assoc] using this

theorem sSup_le_normalizer_sSup_diff (A : Subgroup Ω) :
    sSup 𝓛 ≤ Subgroup.normalizer ((sSup (𝓛 \ {A}) : Subgroup Ω) : Set Ω) := by
  intro g hg
  have h1 : ∀ g ∈ sSup 𝓛, ∀ x ∈ sSup (𝓛 \ {A}), g * x * g⁻¹ ∈ sSup (𝓛 \ {A}) := fun g hg =>
    conj_mem_sSup fun D hD d hd =>
      le_sSup hD ((Subgroup.mem_normalizer_iff.mp (sSup_le_normalizer hcomm hD.1 hg) d).mp hd)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h1 g hg x hx, fun hx => ?_⟩
  have := h1 g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

end Commuting

section Proj

variable {Ω : Type*} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem exists_proj {A B K : Subgroup Ω} (hBA : B ≤ Subgroup.centralizer (A : Set Ω))
    (hKAB : K ≤ A ⊔ B) (hKB : K ≤ Subgroup.normalizer (B : Set Ω)) (hKB1 : K ⊓ B = ⊥) :
    ∃ φ : ↥(A ⊓ (K ⊔ B)) →* ↥K, Function.Surjective φ ∧
      (∀ m : ↥(A ⊓ (K ⊔ B)), ((φ m : ↥K) : Ω)⁻¹ * m ∈ B) ∧
      (∀ (m : ↥(A ⊓ (K ⊔ B))) (k : ↥K), (k : Ω)⁻¹ * m ∈ B → φ m = k) := by
  classical
  set Y := K ⊔ B with hY
  have hYB : Y ≤ Subgroup.normalizer (B : Set Ω) := _root_.sup_le hKB Subgroup.le_normalizer
  have hBY : B ≤ Y := le_sup_right
  have : (B.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBY).2 hYB
  set q := QuotientGroup.mk' (B.subgroupOf Y) with hq
  let ι : ↥K →* ↥Y ⧸ B.subgroupOf Y := q.comp (Subgroup.inclusion le_sup_left)
  have hι : Function.Bijective ι := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro k hk
      have h1 : Subgroup.inclusion (le_sup_left : K ≤ Y) k ∈ B.subgroupOf Y :=
        (QuotientGroup.eq_one_iff _).mp hk
      have h2 : (k : Ω) ∈ K ⊓ B := Subgroup.mem_inf.mpr ⟨k.2, h1⟩
      rw [hKB1, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    · intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf Y) z
      have hy : (y : Ω) ∈ ((K ⊔ B : Subgroup Ω) : Set Ω) := y.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right K B hKB] at hy
      obtain ⟨k, hk, b, hb, hkb⟩ := hy
      refine ⟨⟨k, hk⟩, ?_⟩
      show q (Subgroup.inclusion le_sup_left ⟨k, hk⟩) = q y
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have e : ((Subgroup.inclusion (le_sup_left : K ≤ Y) ⟨k, hk⟩)⁻¹ * y : ↥Y) = (b : Ω) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        rw [← hkb]
        group
      rw [e]
      exact hb
  let e := MulEquiv.ofBijective ι hι
  let φ : ↥(A ⊓ Y) →* ↥K := e.symm.toMonoidHom.comp (q.comp (Subgroup.inclusion inf_le_right))
  have hφ : ∀ m : ↥(A ⊓ Y), ((φ m : ↥K) : Ω)⁻¹ * m ∈ B := by
    intro m
    have h1 : ι (φ m) = q (Subgroup.inclusion inf_le_right m) := e.apply_symm_apply _
    have h2 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have huniq : ∀ (m : ↥(A ⊓ Y)) (k : ↥K), (k : Ω)⁻¹ * m ∈ B → φ m = k := by
    intro m k hk
    have h1 := hφ m
    have h3 : ((φ m : ↥K) : Ω)⁻¹ * k ∈ K ⊓ B := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (φ m).2) k.2, ?_⟩
      have := mul_mem h1 (inv_mem hk)
      simpa [mul_assoc] using this
    rw [hKB1, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  refine ⟨φ, ?_, hφ, huniq⟩
  intro k
  have hk : (k : Ω) ∈ ((A ⊔ B : Subgroup Ω) : Set Ω) := hKAB k.2
  have hAB : A ≤ Subgroup.normalizer (B : Set Ω) :=
    (Subgroup.le_centralizer_iff.mp hBA).trans (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hk
  obtain ⟨a, ha, b, hb, hab⟩ := hk
  have hka : a = (k : Ω) * b⁻¹ := by rw [← hab]; group
  have haY : a ∈ Y := by
    rw [hka]
    exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right (inv_mem hb))
  refine ⟨⟨a, ha, haY⟩, huniq _ k ?_⟩
  have e2 : (k : Ω)⁻¹ * a = b⁻¹ := by rw [hka]; group
  show (k : Ω)⁻¹ * a ∈ B
  rw [e2]
  exact inv_mem hb

theorem exists_t {A B K : Subgroup Ω} (hBA : B ≤ Subgroup.centralizer (A : Set Ω))
    (hKAB : K ≤ A ⊔ B) (hKB : K ≤ Subgroup.normalizer (B : Set Ω)) (hKB1 : K ⊓ B = ⊥)
    (hO2 : pCoreOf 2 A = ⊥) (hKp : ⁅K, K⁆ = K) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (eK : ↥K ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F)) {a : Ω}
    (haK : a ∈ K) :
    ∃ t ∈ A, orderOf t = orderOf a ∧ (∀ j : ℕ, t ^ j ∈ B → a ^ j = 1) ∧
      ∀ y : Ω, (∀ x ∈ A, y * x * y⁻¹ ∈ A) → (∀ b ∈ B, y * b * y⁻¹ ∈ B) →
        (∀ k ∈ K, y * k = k * y) → y * t = t * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := A ⊓ (K ⊔ B) with hM
  obtain ⟨φ, hφs, hφ, huniq⟩ := exists_proj hBA hKAB hKB hKB1
  set P' : Subgroup ↥M := perfectCore ⊤ with hP'
  let ψ : ↥P' →* ↥K := φ.comp P'.subtype
  have hKtop : perfectCore (⊤ : Subgroup ↥K) = ⊤ := by
    apply perfectCore_eq_self_of_perfect
    have := Subgroup.isPerfect_iff.mpr hKp
    exact Group.isPerfect_def.mp this
  have hψs : Function.Surjective ψ := by
    have h1 : P'.map φ = ⊤ := by
      rw [hP', map_perfectCore, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hφs,
        hKtop]
    intro k
    obtain ⟨m, hm, hmk⟩ : k ∈ P'.map φ := h1 ▸ Subgroup.mem_top k
    exact ⟨⟨m, hm⟩, hmk⟩
  have hP'p : Group.IsPerfect ↥P' := Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  have hkerB : ∀ m : ↥P', ψ m = 1 → (((m : ↥M) : Ω)) ∈ B := by
    intro m hm
    have h1 := hφ (m : ↥M)
    have h2 : φ (m : ↥M) = ψ m := rfl
    rw [h2, hm] at h1
    simpa using h1
  have hkerc : ψ.ker ≤ Subgroup.center ↥P' := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    have hb := hkerB m hm
    have hgA : ((g : ↥M) : Ω) ∈ A := (g : ↥M).2.1
    exact Subgroup.mem_centralizer_iff.mp (hBA hb) _ hgA
  have h2 : IsPGroup 2 ψ.ker := isPGroup_two_of_mulEquiv_stated_psl_two_even ψ.ker hkerc hn hF
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).trans eK)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hb := hkerB m hm
    have hmA : ((m : ↥M) : Ω) ∈ A := (m : ↥M).2.1
    obtain ⟨k, hk⟩ := h2 ⟨m, hm⟩
    have hk' : ((m : ↥M) : Ω) ^ 2 ^ k = 1 := by
      have := congrArg (fun x : ↥ψ.ker => (((x : ↥P') : ↥M) : Ω)) hk
      simpa using this
    have hzA : Subgroup.zpowers ((m : ↥M) : Ω) ≤ A := Subgroup.zpowers_le.mpr hmA
    have hzN : A ≤ Subgroup.normalizer (Subgroup.zpowers ((m : ↥M) : Ω) : Set Ω) := by
      intro g hg
      have hc : Commute g ((m : ↥M) : Ω) := Subgroup.mem_centralizer_iff.mp (hBA hb) g hg
      have hgc : g ∈ Subgroup.centralizer (Subgroup.zpowers ((m : ↥M) : Ω) : Set Ω) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨j, rfl⟩
        exact ((hc.zpow_right j).eq).symm
      exact Subgroup.centralizer_le_normalizer _ hgc
    have hz2 : IsPGroup 2 (Subgroup.zpowers ((m : ↥M) : Ω)) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
    have hz : Subgroup.zpowers ((m : ↥M) : Ω) ≤ pCoreOf 2 A :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hzA hzN hz2
    rw [hO2] at hz
    have h1 := hz (Subgroup.mem_zpowers _)
    rw [Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨m, hm⟩ := hψs ⟨a, haK⟩
  have hmo : orderOf m = orderOf a := by
    have h1 := orderOf_injective ψ hinj m
    rw [hm] at h1
    rw [← h1]
    exact (Subgroup.orderOf_coe (⟨a, haK⟩ : ↥K)).symm
  refine ⟨((m : ↥M) : Ω), (m : ↥M).2.1, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hmo]
  · intro j hj
    have h1 : ψ (m ^ j) = 1 := by
      have := huniq ((m ^ j : ↥P') : ↥M) 1 (by simpa using hj)
      exact this
    rw [map_pow, hm] at h1
    have := congrArg Subtype.val h1
    simpa using this
  · intro y hyA hyB hyK
    have hyM : ∀ x ∈ M, y * x * y⁻¹ ∈ M := by
      intro x hx
      refine ⟨hyA x hx.1, ?_⟩
      have hle : K ⊔ B ≤ (K ⊔ B).comap (MulAut.conj y).toMonoidHom := by
        refine _root_.sup_le (fun k hk => ?_) (fun b hb => ?_)
        · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [hyK k hk, mul_inv_cancel_right]
          exact Subgroup.mem_sup_left hk
        · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact Subgroup.mem_sup_right (hyB b hb)
      simpa [MulAut.conj_apply] using hle hx.2
    let c : ↥M →* ↥M :=
      { toFun := fun x => ⟨y * x * y⁻¹, hyM x x.2⟩
        map_one' := by ext; simp
        map_mul' := fun u v => by
          ext
          simp only [Subgroup.coe_mul]
          group }
    have hcinj : Function.Injective c := fun u v h => by
      have h1 := congrArg Subtype.val h
      simp only [c, MonoidHom.coe_mk, OneHom.coe_mk] at h1
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
    have hcsurj : Function.Surjective c := Finite.injective_iff_surjective.mp hcinj
    have hcP : ∀ x ∈ P', c x ∈ P' := by
      have h1 : P'.map c = P' := by
        rw [hP', map_perfectCore, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hcsurj]
      intro x hx
      rw [← h1]
      exact Subgroup.mem_map_of_mem c hx
    have hψc : ψ ⟨c m, hcP m m.2⟩ = ψ m := by
      show φ (c m) = φ m
      apply huniq
      have h1 := hyB _ (hφ (m : ↥M))
      have hyk : Commute y ((φ (m : ↥M) : ↥K) : Ω) := hyK _ (φ (m : ↥M)).2
      have e : ((φ (m : ↥M) : ↥K) : Ω)⁻¹ * ((c m : ↥M) : Ω) =
          y * (((φ (m : ↥M) : ↥K) : Ω)⁻¹ * ((m : ↥M) : Ω)) * y⁻¹ := by
        show ((φ (m : ↥M) : ↥K) : Ω)⁻¹ * (y * ((m : ↥M) : Ω) * y⁻¹) = _
        calc ((φ (m : ↥M) : ↥K) : Ω)⁻¹ * (y * ((m : ↥M) : Ω) * y⁻¹)
            = (((φ (m : ↥M) : ↥K) : Ω)⁻¹ * y) * ((m : ↥M) : Ω) * y⁻¹ := by group
          _ = (y * ((φ (m : ↥M) : ↥K) : Ω)⁻¹) * ((m : ↥M) : Ω) * y⁻¹ := by
              rw [← (hyk.inv_right).eq]
          _ = y * (((φ (m : ↥M) : ↥K) : Ω)⁻¹ * ((m : ↥M) : Ω)) * y⁻¹ := by group
      rw [e]
      exact h1
    have heq : (⟨c m, hcP m m.2⟩ : ↥P') = m := hinj hψc
    have h3 := congrArg (fun x : ↥P' => ((x : ↥M) : Ω)) heq
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk] at h3
    calc y * ((m : ↥M) : Ω) = (y * ((m : ↥M) : Ω) * y⁻¹) * y := by group
      _ = ((m : ↥M) : Ω) * y := by rw [h3]

theorem exists_le_of_commuting {𝓛 : Set (Subgroup Ω)}
    (hcomm : ∀ A ∈ 𝓛, ∀ B ∈ 𝓛, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hO2 : ∀ A ∈ 𝓛, pCoreOf 2 A = ⊥) {K : Subgroup Ω} (hKs : IsSimpleGroup ↥K)
    (hKp : ⁅K, K⁆ = K) {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    (eK : ↥K ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))
    (hKL : K ≤ sSup 𝓛) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {a : Ω} (haK : a ∈ K)
    (hao : orderOf a = p) {y : Ω} (hyo : orderOf y = p) (hyK : ∀ k ∈ K, y * k = k * y)
    (hyL : ∀ A ∈ 𝓛, A.map (MulAut.conj y).toMonoidHom ∈ 𝓛) (hyS : y ∉ sSup 𝓛)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup Ω) ≤ 2) :
    ∃ A ∈ 𝓛, K ≤ A := by
  classical
  set mv : Subgroup Ω → Prop := fun A => ∃ x ∈ A, ∃ k ∈ K, x * k ≠ k * x with hmv
  have hKB1 : ∀ A ∈ 𝓛, mv A → K ⊓ sSup (𝓛 \ {A}) = ⊥ := by
    intro A hA hmvA
    have hKN : K ≤ Subgroup.normalizer ((sSup (𝓛 \ {A}) : Subgroup Ω) : Set Ω) :=
      hKL.trans (sSup_le_normalizer_sSup_diff hcomm A)
    have hN : ((K ⊓ sSup (𝓛 \ {A})).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun k hk =>
        mem_normalizer_inf (Subgroup.le_normalizer hk) (hKN hk)
    have := hKs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ sSup (𝓛 \ {A})).subgroupOf K) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : ↥K) ∈ (K ⊓ sSup (𝓛 \ {A})).subgroupOf K := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      obtain ⟨x, hx, k, hk, hxk⟩ := hmvA
      have hkB : k ∈ sSup (𝓛 \ {A}) := by
        have : (⟨k, hk⟩ : ↥K) ∈ (K ⊓ sSup (𝓛 \ {A})).subgroupOf K := h ▸ Subgroup.mem_top _
        exact this.2
      exact hxk (Subgroup.mem_centralizer_iff.mp (sSup_diff_le_centralizer hcomm hA hkB) x hx)
  have ht : ∀ A ∈ 𝓛, mv A → ∃ t ∈ A, orderOf t = p ∧
      (∀ j : ℕ, t ^ j ∈ sSup (𝓛 \ {A}) → p ∣ j) ∧
      (A.map (MulAut.conj y).toMonoidHom = A → y * t = t * y) := by
    intro A hA hmvA
    obtain ⟨t, htA, hto, htj, hty⟩ := exists_t (sSup_diff_le_centralizer hcomm hA)
      (hKL.trans (sSup_eq_sup_sSup_diff hA).le) (hKL.trans (sSup_le_normalizer_sSup_diff hcomm A))
      (hKB1 A hA hmvA) (hO2 A hA) hKp hn hF eK haK
    refine ⟨t, htA, hto.trans hao, fun j hj => hao ▸ orderOf_dvd_of_pow_eq_one (htj j hj),
      fun hyA => hty y ?_ ?_ hyK⟩
    · intro x hx
      have : (MulAut.conj y).toMonoidHom x ∈ A.map (MulAut.conj y).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rw [hyA] at this
      simpa [MulAut.conj_apply] using this
    · refine conj_mem_sSup fun D hD d hd => ?_
      have hD' : D.map (MulAut.conj y).toMonoidHom ∈ 𝓛 \ {A} := by
        refine ⟨hyL D hD.1, fun h => hD.2 ?_⟩
        have h1 : D.map (MulAut.conj y).toMonoidHom = A.map (MulAut.conj y).toMonoidHom := by
          rw [hyA]
          exact h
        exact Subgroup.map_injective (MulAut.conj y).injective h1
      have : (MulAut.conj y).toMonoidHom d ∈ D.map (MulAut.conj y).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hd
      exact le_sSup hD' (by simpa [MulAut.conj_apply] using this)
  have hex : ∃ A ∈ 𝓛, mv A := by
    by_contra hno
    push Not at hno
    have hc : sSup 𝓛 ≤ Subgroup.centralizer (K : Set Ω) := sSup_le fun A hA x hx =>
      Subgroup.mem_centralizer_iff.mpr fun k hk => by
        have := hno A hA
        simp only [hmv, not_exists, not_and, not_not] at this
        exact (this x hx k hk).symm
    have hb : ⁅K, K⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (hKL.trans hc)
    rw [hKp] at hb
    have := hKs
    obtain ⟨u, v, huv⟩ := exists_pair_ne ↥K
    apply huv
    have hu : (u : Ω) ∈ (⊥ : Subgroup Ω) := by
      rw [← hb]
      exact u.2
    have hv : (v : Ω) ∈ (⊥ : Subgroup Ω) := by
      rw [← hb]
      exact v.2
    exact Subtype.ext ((Subgroup.mem_bot.mp hu).trans (Subgroup.mem_bot.mp hv).symm)
  obtain ⟨A₀, hA₀, hmv₀⟩ := hex
  have hpow : ∀ {t : Ω}, orderOf t = p → t ^ p = 1 := fun h => h ▸ pow_orderOf_eq_one _
  have hzero : ∀ (c : ZMod p), p ∣ c.val → c = 0 := fun c h =>
    (ZMod.val_eq_zero c).mp (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt c))
  by_cases h1 : ∃ A₁ ∈ 𝓛, A₁ ≠ A₀ ∧ mv A₁
  · exfalso
    obtain ⟨A₁, hA₁, hne, hmv₁⟩ := h1
    obtain ⟨t₀, ht₀A, ht₀o, ht₀j, ht₀y⟩ := ht A₀ hA₀ hmv₀
    obtain ⟨t₁, ht₁A, ht₁o, ht₁j, ht₁y⟩ := ht A₁ hA₁ hmv₁
    have hA₁B₀ : A₁ ≤ sSup (𝓛 \ {A₀}) := le_sSup ⟨hA₁, hne⟩
    have hA₀B₁ : A₀ ≤ sSup (𝓛 \ {A₁}) := le_sSup ⟨hA₀, hne.symm⟩
    have hc01 : t₀ * t₁ = t₁ * t₀ := hcomm A₀ hA₀ A₁ hA₁ hne.symm t₀ ht₀A t₁ ht₁A
    by_cases h2 : ∃ A₂ ∈ 𝓛, A₂ ≠ A₀ ∧ A₂ ≠ A₁ ∧ mv A₂
    · obtain ⟨A₂, hA₂, hne₀, hne₁, hmv₂⟩ := h2
      obtain ⟨t₂, ht₂A, ht₂o, -, -⟩ := ht A₂ hA₂ hmv₂
      have hc02 := hcomm A₀ hA₀ A₂ hA₂ hne₀.symm t₀ ht₀A t₂ ht₂A
      have hc12 := hcomm A₁ hA₁ A₂ hA₂ hne₁.symm t₁ ht₁A t₂ ht₂A
      have hA₂B₀ : A₂ ≤ sSup (𝓛 \ {A₀}) := le_sSup ⟨hA₂, hne₀⟩
      have hA₂B₁ : A₂ ≤ sSup (𝓛 \ {A₁}) := le_sSup ⟨hA₂, hne₁⟩
      have h3 := three_le_pRank_of_commute (hpow ht₀o) (hpow ht₁o) (hpow ht₂o) hc01 hc02 hc12
        (fun a b d hab => by
          have ha : a = 0 := by
            apply hzero
            apply ht₀j
            have e : t₀ ^ a.val = (t₁ ^ b.val * t₂ ^ d.val)⁻¹ := by
              rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
              exact hab
            rw [e]
            exact inv_mem (mul_mem (pow_mem (hA₁B₀ ht₁A) _) (pow_mem (hA₂B₀ ht₂A) _))
          rw [ha, ZMod.val_zero, pow_zero, one_mul] at hab
          have hb : b = 0 := by
            apply hzero
            apply ht₁j
            rw [eq_inv_of_mul_eq_one_left hab]
            exact inv_mem (pow_mem (hA₂B₁ ht₂A) _)
          rw [hb, ZMod.val_zero, pow_zero, one_mul] at hab
          have hd : d = 0 := by
            apply hzero
            have := orderOf_dvd_of_pow_eq_one hab
            rwa [ht₂o] at this
          exact ⟨ha, hb, hd⟩)
      omega
    · push Not at h2
      have hmvy : ∀ A, mv A → mv (A.map (MulAut.conj y).toMonoidHom) := by
        rintro A ⟨x, hx, k, hk, hxk⟩
        refine ⟨y * x * y⁻¹, ⟨x, hx, by simp [MulAut.conj_apply]⟩, k, hk, fun h => hxk ?_⟩
        have hyk := hyK k hk
        have e1 : y * x * y⁻¹ * k = y * (x * k) * y⁻¹ := by
          have : y⁻¹ * k = k * y⁻¹ := (Commute.inv_left hyk).eq
          rw [mul_assoc (y * x), this]
          group
        have e2 : k * (y * x * y⁻¹) = y * (k * x) * y⁻¹ := by
          rw [← mul_assoc, ← mul_assoc, ← hyk]
          group
        rw [e1, e2] at h
        exact mul_left_cancel (mul_right_cancel h)
      have hin : ∀ A ∈ 𝓛, mv A → A = A₀ ∨ A = A₁ := fun A hA hmvA => by
        by_contra h
        push Not at h
        exact h2 A hA h.1 h.2 hmvA
      have hσ₀ := hin _ (hyL A₀ hA₀) (hmvy A₀ hmv₀)
      have hσ₁ := hin _ (hyL A₁ hA₁) (hmvy A₁ hmv₁)
      have hinjσ : ∀ X Y : Subgroup Ω, X.map (MulAut.conj y).toMonoidHom =
          Y.map (MulAut.conj y).toMonoidHom → X = Y := fun X Y h =>
        Subgroup.map_injective (MulAut.conj y).injective h
      have hfix : A₀.map (MulAut.conj y).toMonoidHom = A₀ ∧
          A₁.map (MulAut.conj y).toMonoidHom = A₁ := by
        by_contra hnot
        have hswap : A₀.map (MulAut.conj y).toMonoidHom = A₁ ∧
            A₁.map (MulAut.conj y).toMonoidHom = A₀ := by
          rcases hσ₀ with h0 | h0 <;> rcases hσ₁ with h1' | h1'
          · exact absurd (hinjσ _ _ (h0.trans h1'.symm)) hne.symm
          · exact absurd ⟨h0, h1'⟩ hnot
          · exact ⟨h0, h1'⟩
          · exact absurd (hinjσ _ _ (h0.trans h1'.symm)) hne.symm
        have hsq : ∀ x ∈ A₀, y * (y * x * y⁻¹) * y⁻¹ ∈ A₀ := by
          intro x hx
          have h1 : y * x * y⁻¹ ∈ A₁ := by
            rw [← hswap.1]
            exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
          have h2 : y * (y * x * y⁻¹) * y⁻¹ ∈ A₁.map (MulAut.conj y).toMonoidHom :=
            ⟨_, h1, by simp [MulAut.conj_apply]⟩
          rwa [hswap.2] at h2
        have hev : ∀ j : ℕ, ∀ x ∈ A₀, y ^ (2 * j) * x * (y ^ (2 * j))⁻¹ ∈ A₀ := by
          intro j
          induction j with
          | zero => intro x hx; simpa using hx
          | succ j ih =>
            intro x hx
            have e : y ^ (2 * (j + 1)) * x * (y ^ (2 * (j + 1)))⁻¹ =
                y * (y * (y ^ (2 * j) * x * (y ^ (2 * j))⁻¹) * y⁻¹) * y⁻¹ := by
              rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, pow_succ]
              group
            rw [e]
            exact hsq _ (ih x hx)
        obtain ⟨j, hj⟩ : ∃ j : ℕ, p + 1 = 2 * j := by
          rcases hp.out.eq_two_or_odd' with h | h
          · exact absurd h hp2
          · obtain ⟨k, hk⟩ := h
            exact ⟨k + 1, by omega⟩
        have hyp1 : y ^ (2 * j) = y := by
          rw [← hj, pow_succ, hpow hyo, one_mul]
        have hle : A₀.map (MulAut.conj y).toMonoidHom ≤ A₀ := by
          rintro _ ⟨x, hx, rfl⟩
          have := hev j x hx
          rw [hyp1] at this
          simpa [MulAut.conj_apply] using this
        have hcard : Nat.card ↥(A₀.map (MulAut.conj y).toMonoidHom) = Nat.card ↥A₀ :=
          Subgroup.card_map_of_injective (MulAut.conj y).injective
        have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
        exact hne (hswap.1.symm.trans heq)
      have h3 := three_le_pRank_of_commute (hpow ht₀o) (hpow ht₁o) (hpow hyo) hc01
        (ht₀y hfix.1).symm (ht₁y hfix.2).symm
        (fun a b d hab => by
          have hd : d = 0 := by
            by_contra hd0
            apply hyS
            have hyd : y ^ d.val ∈ sSup 𝓛 := by
              have e : y ^ d.val = (t₀ ^ a.val * t₁ ^ b.val)⁻¹ := eq_inv_of_mul_eq_one_right hab
              rw [e]
              exact inv_mem (mul_mem (pow_mem (le_sSup hA₀ ht₀A) _)
                (pow_mem (le_sSup hA₁ ht₁A) _))
            have hcop : Nat.Coprime (orderOf y) d.val := by
              rw [hyo]
              exact Nat.coprime_of_lt_prime (fun h => hd0 ((ZMod.val_eq_zero d).mp h))
                (ZMod.val_lt d) hp.out
            have hord : orderOf (y ^ d.val) = orderOf y := Nat.Coprime.orderOf_pow hcop
            have hle : Subgroup.zpowers (y ^ d.val) ≤ Subgroup.zpowers y :=
              Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers y _)
            have heq : Subgroup.zpowers (y ^ d.val) = Subgroup.zpowers y :=
              Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
            have hy : y ∈ Subgroup.zpowers (y ^ d.val) := heq ▸ Subgroup.mem_zpowers y
            exact (Subgroup.zpowers_le.mpr hyd) hy
          rw [hd, ZMod.val_zero, pow_zero, mul_one] at hab
          have ha : a = 0 := by
            apply hzero
            apply ht₀j
            rw [eq_inv_of_mul_eq_one_left hab]
            exact inv_mem (pow_mem (hA₁B₀ ht₁A) _)
          rw [ha, ZMod.val_zero, pow_zero, one_mul] at hab
          have hb : b = 0 := by
            apply hzero
            have := orderOf_dvd_of_pow_eq_one hab
            rwa [ht₁o] at this
          exact ⟨ha, hb, hd⟩)
      omega
  ·
    push Not at h1
    refine ⟨A₀, hA₀, ?_⟩
    set B₀ := sSup (𝓛 \ {A₀}) with hB₀
    have hB₀K : B₀ ≤ Subgroup.centralizer (K : Set Ω) := sSup_le fun D hD x hx =>
      Subgroup.mem_centralizer_iff.mpr fun k hk => by
        have := h1 D hD.1 hD.2
        simp only [hmv, not_exists, not_and, not_not] at this
        exact (this x hx k hk).symm
    have hB₀A : B₀ ≤ Subgroup.centralizer (A₀ : Set Ω) := sSup_diff_le_centralizer hcomm hA₀
    have hAN : A₀ ≤ Subgroup.normalizer (B₀ : Set Ω) :=
      (Subgroup.le_centralizer_iff.mp hB₀A).trans (Subgroup.centralizer_le_normalizer _)
    have hdec : ∀ k ∈ K, ∃ x ∈ A₀, ∃ b ∈ B₀, x * b = k := by
      intro k hk
      have h1 : k ∈ ((A₀ ⊔ B₀ : Subgroup Ω) : Set Ω) := by
        rw [← sSup_eq_sup_sSup_diff hA₀]
        exact hKL hk
      rw [Subgroup.coe_mul_of_left_le_normalizer_right A₀ B₀ hAN] at h1
      obtain ⟨x, hx, b, hb, hxb⟩ := h1
      exact ⟨x, hx, b, hb, hxb⟩
    rw [← hKp, Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hdec k₁ hk₁
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hdec k₂ hk₂
    have c1 : Commute b₁ a₂ := (Subgroup.mem_centralizer_iff.mp (hB₀A hb₁) a₂ ha₂).symm
    have c3 : Commute b₂ a₁ := (Subgroup.mem_centralizer_iff.mp (hB₀A hb₂) a₁ ha₁).symm
    have c2 : Commute b₁ b₂ := by
      have h1 : Commute b₂ (a₁ * b₁) :=
        (Subgroup.mem_centralizer_iff.mp (hB₀K hb₂) _ hk₁).symm
      have h2 : Commute b₂ a₁⁻¹ := c3.inv_right
      have h3 : Commute b₂ (a₁⁻¹ * (a₁ * b₁)) := h2.mul_right h1
      rw [inv_mul_cancel_left] at h3
      exact h3.symm
    have e : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹
          = a₁ * (b₁ * a₂) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
        _ = a₁ * (a₂ * b₁) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [c1.eq]
        _ = a₁ * a₂ * (b₁ * b₂ * b₁⁻¹) * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
        _ = a₁ * a₂ * b₂ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [c2.eq, mul_inv_cancel_right]
        _ = a₁ * a₂ * (b₂ * a₁⁻¹ * b₂⁻¹) * a₂⁻¹ := by group
        _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by rw [(c3.inv_right).eq, mul_inv_cancel_right]
    rw [e, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha₁ ha₂) (inv_mem ha₁)) (inv_mem ha₂)

end Proj

end L436

variable {G : Type} [Group G] [Finite G]

namespace Setting436Sp4

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (s : Setting436Sp4 G T M L n I H K t)
include s

theorem pCoreOf_GZ_le_centralizer_Z :
    pCoreOf 2 (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) ≤
      Subgroup.centralizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzQ : z ∈ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) :=
    (s.concl.Q₁_cent.symm.le.trans inf_le_left) hz
  have hzC := A4.omegaOneCenterOf_le_centerOf _ (s.star.2 (s.star.1 hzQ))
  exact (Subgroup.mem_centralizer_iff.mp hzC.2 x hx).symm

theorem exists_KZ (h37 : A37ForSQTK) (h39 : A39ForSQTK) :
    ∃ KZ ∈ cComp (Subgroup.centralizer
        (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)),
      sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ KZ := by
  classical
  set V := v432 T M L with hV
  set Z := sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hZ
  set K₂ := sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hK₂
  set Q₁ := sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hQ₁
  set H₀ := Subgroup.centralizer (Z : Set G) with hH₀
  set GZ := Subgroup.normalizer (Z : Set G) with hGZ
  set QZ := pCoreOf 2 GZ with hQZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := s.sk.base.hyp
  have hH₀GZ : H₀ ≤ GZ := Subgroup.centralizer_le_normalizer _
  have hGZH₀ : GZ ≤ Subgroup.normalizer (H₀ : Set G) := fun g hg =>
    A4.mem_normalizer_centralizer hg
  have hZab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := mul_comm_of_exp_two s.concl.V_sq
  have hZH₀' : Z ≤ H₀ := fun z hz => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    hZab w (s.Z_le_V hw) z (s.Z_le_V hz)
  have hZ2 : IsPGroup 2 Z := (pCoreOf_isPGroup 2 GZ).to_le s.Z_le_pCoreOf
  have hZH₀ : Z ≤ pCoreOf 2 H₀ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZH₀'
    (Subgroup.centralizer_le_normalizer _) hZ2
  have hH₀ : pCoreOf 2 H₀ ≠ ⊥ := fun h => s.Z_ne_bot (le_bot_iff.mp (h ▸ hZH₀))
  have hQZH₀ : QZ ≤ H₀ := s.pCoreOf_GZ_le_centralizer_Z
  have hO₂ : pCoreOf 2 H₀ ≤ QZ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 H₀).trans hH₀GZ) (hGZH₀.trans (normalizer_le_normalizer_pCoreOf 2 H₀))
    (pCoreOf_isPGroup 2 H₀)
  have hK₂H₀ : K₂ ≤ H₀ := s.concl.K₂_le
  have hK₂GZ : K₂ ≤ GZ := hK₂H₀.trans hH₀GZ
  have hspan : cCompSpan H₀ = perfectCore H₀ :=
    lemma_1_2_1_one hyp.qtke hyp.simple hyp.nonabelian h39 hH₀
  have hK₂span : K₂ ≤ sSup (cComp H₀) := by
    have h1 := le_perfectCore_of_perfect hK₂H₀ (perfectCore_perfect _)
    rw [← hspan] at h1
    exact h1
  set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥GZ) with hρ
  have hρ1 : ∀ x : ↥GZ, ρ x = 1 ↔ (x : G) ∈ QZ := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
  let img : Subgroup G → Subgroup (↥GZ ⧸ CFSG.pCore 2 ↥GZ) := fun X => (X.subgroupOf GZ).map ρ
  set 𝓛 := img '' cComp H₀ with h𝓛
  have hmem_img : ∀ (X : Subgroup G) (w : ↥GZ ⧸ CFSG.pCore 2 ↥GZ), w ∈ img X ↔
      ∃ x : ↥GZ, (x : G) ∈ X ∧ ρ x = w := by
    intro X w
    exact ⟨fun ⟨x, hx, hxw⟩ => ⟨x, hx, hxw⟩, fun ⟨x, hx, hxw⟩ => ⟨x, hx, hxw⟩⟩
  have hρmul : ∀ a b : ↥GZ, ρ a * ρ b = ρ b * ρ a ↔ (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ QZ := by
    intro a b
    have e : ((a * b * a⁻¹ * b⁻¹ : ↥GZ) : G) = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ := by simp
    rw [← e, ← hρ1 (a * b * a⁻¹ * b⁻¹)]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc ρ a * ρ b = (ρ a * ρ b * (ρ a)⁻¹ * (ρ b)⁻¹) * (ρ b * ρ a) := by group
        _ = ρ b * ρ a := by rw [h, one_mul]
  have hcomm : ∀ A ∈ 𝓛, ∀ B ∈ 𝓛, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨L₁, hL₁, rfl⟩ _ ⟨L₂, hL₂, rfl⟩ hne _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    have hL : L₁ ≠ L₂ := fun h => hne (h ▸ rfl)
    have hc := (lemma_1_2_1_two hyp.qtke hyp.simple hyp.nonabelian h37 hH₀ hL₁ hL₂ hL)
    have h1 : (x : G) * z * (x : G)⁻¹ * (z : G)⁻¹ ∈ QZ := by
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
        (Subgroup.mem_subgroupOf.mp hz)
      rw [commutatorElement_def] at this
      exact hO₂ (hc.2 (hc.1 this))
    exact (hρmul x z).mpr h1
  have hSQ := SQTKHyp.of_sqtkGroup ↥GZ s.sqtkGroup_GZ
  have hO2 : ∀ A ∈ 𝓛, pCoreOf 2 A = ⊥ := by
    rintro _ ⟨L₁, hL₁, rfl⟩
    exact hSQ.pCoreOf_two_of_subnormal
      (subnormal_of_mem_cComp (modO2Image_mem_cComp (cComp_normalizer hL₁)))
  let ψ₀ : ↥K₂ →* ↥GZ ⧸ CFSG.pCore 2 ↥GZ := ρ.comp (Subgroup.inclusion hK₂GZ)
  have hrange : ψ₀.range = img K₂ := by
    show (ρ.comp (Subgroup.inclusion hK₂GZ)).range = (K₂.subgroupOf GZ).map ρ
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let ψ : ↥K₂ →* ↥(img K₂) := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ₀.rangeRestrict
  have hψs : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ₀.rangeRestrict_surjective
  have hK₂QZ : ∀ k : ↥K₂, (k : G) ∈ QZ ↔ k ∈ CFSG.pCore 2 ↥K₂ := by
    intro k
    constructor
    · intro hk
      have hle : K₂ ⊓ QZ ≤ Q₁ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg)
          (le_normalizer_pCoreOf 2 GZ (hK₂GZ hg))) ((pCoreOf_isPGroup 2 GZ).to_le inf_le_right)
      obtain ⟨y, hy, hyk⟩ := hle ⟨k.2, hk⟩
      have : y = k := Subtype.ext hyk
      rw [← this]
      exact hy
    · intro hk
      exact (s.star.1.trans (s.star.2.trans (A4.omegaOneCenterOf_le _))) ⟨k, hk, rfl⟩
  have hψker : ψ.ker = CFSG.pCore 2 ↥K₂ := by
    ext k
    rw [MonoidHom.mem_ker, ← hK₂QZ]
    show ψ k = 1 ↔ ((Subgroup.inclusion hK₂GZ k : ↥GZ) : G) ∈ QZ
    rw [← hρ1]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  let eKbar : ↥(img K₂) ≃* ModO2 K₂ :=
    ((QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).symm
  have hKs : IsSimpleGroup ↥(img K₂) := by
    have := s.isSimpleGroup_modO2_K₂
    exact eKbar.isSimpleGroup
  have hKp : ⁅img K₂, img K₂⁆ = img K₂ := by
    have : Group.IsPerfect ↥K₂ := Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective hψs)
  obtain ⟨-, F, hF', hFf, hcard, ⟨eF⟩⟩ := s.concl.psl
  have hKL : img K₂ ≤ sSup 𝓛 := by
    have hle : sSup (cComp H₀) ≤ ((sSup 𝓛).comap ρ).map GZ.subtype := by
      refine sSup_le fun L₁ hL₁ x hx => ?_
      have hxGZ : x ∈ GZ := (le_of_mem_cComp hL₁).trans hH₀GZ hx
      refine ⟨⟨x, hxGZ⟩, ?_, rfl⟩
      exact (le_sSup (show img L₁ ∈ 𝓛 from ⟨L₁, hL₁, rfl⟩) : img L₁ ≤ sSup 𝓛)
        ⟨⟨x, hxGZ⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle (hK₂span (Subgroup.mem_subgroupOf.mp hx))
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  obtain ⟨p, hp, hp2, hpn⟩ := s.exists_odd_prime_dvd
  have : Fact p.Prime := ⟨hp⟩
  have hρord : ∀ x : ↥GZ, orderOf (x : G) = p → orderOf (ρ x) = p := by
    intro x hx
    have hx' : orderOf x = p := by rw [← Subgroup.orderOf_coe]; exact hx
    have hd : orderOf (ρ x) ∣ p := orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow, ← hx', pow_orderOf_eq_one, map_one])
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exfalso
      have h1 : (x : G) ∈ QZ := (hρ1 x).mp (orderOf_eq_one_iff.mp h)
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 GZ) ⟨x, h1⟩
      have hk' : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hdvd : p ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
    · exact h
  obtain ⟨a, haK₂, hao⟩ := s.exists_elt_K₂ hp hpn
  obtain ⟨y, hyN, hyC, hyo, -, -, hyK, -⟩ := s.exists_elt_Y₁ hp hpn
  have hyK' : ∀ k ∈ img K₂, ρ ⟨y, hyN⟩ * k = k * ρ ⟨y, hyN⟩ := by
    rintro _ ⟨k, hk, rfl⟩
    refine (hρmul _ _).mpr ?_
    exact (s.star.1.trans (s.star.2.trans (A4.omegaOneCenterOf_le _)))
      (hyK _ (Subgroup.mem_subgroupOf.mp hk))
  have hyL : ∀ A ∈ 𝓛, A.map (MulAut.conj (ρ ⟨y, hyN⟩)).toMonoidHom ∈ 𝓛 := by
    rintro _ ⟨L₁, hL₁, rfl⟩
    refine ⟨L₁.map (MulAut.conj y).toMonoidHom, ?_, ?_⟩
    · have h1 := cComp_map_mulEquiv (MulAut.conj y) hL₁
      have h2 : H₀.map (MulAut.conj y).toMonoidHom = H₀ :=
        A38.map_conj_eq_iff.mpr (hGZH₀ hyN)
      rwa [h2] at h1
    · ext w
      constructor
      · intro hw
        obtain ⟨x, hx, hxw⟩ := hw
        obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
        have hlGZ : l ∈ GZ := (le_of_mem_cComp hL₁).trans hH₀GZ hl
        refine Subgroup.mem_map.mpr
          ⟨ρ ⟨l, hlGZ⟩, ⟨⟨l, hlGZ⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, ?_⟩
        rw [← hxw]
        show ρ ⟨y, hyN⟩ * ρ ⟨l, hlGZ⟩ * (ρ ⟨y, hyN⟩)⁻¹ = ρ x
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hlx]
        rfl
      · intro hw
        obtain ⟨v, hv, hvw⟩ := Subgroup.mem_map.mp hw
        obtain ⟨lG, hlG, rfl⟩ := hv
        refine Subgroup.mem_map.mpr ⟨⟨y, hyN⟩ * lG * ⟨y, hyN⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
        · exact ⟨lG, Subgroup.mem_subgroupOf.mp hlG, by simp [MulAut.conj_apply]⟩
        · rw [← hvw]
          simp [map_mul, map_inv, MulAut.conj_apply]
  have hyS : ρ ⟨y, hyN⟩ ∉ sSup 𝓛 := by
    intro h
    have hle : sSup 𝓛 ≤ img H₀ := sSup_le (by
      rintro _ ⟨L₁, hL₁, rfl⟩ _ ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mpr ((le_of_mem_cComp hL₁)
        (Subgroup.mem_subgroupOf.mp hx)), rfl⟩)
    obtain ⟨x, hx, hxy⟩ := hle h
    have h1 : ρ (x⁻¹ * ⟨y, hyN⟩) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := (hρ1 _).mp h1
    apply hyC
    have e : y = (x : G) * ((x : G)⁻¹ * y) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_subgroupOf.mp hx) (hQZH₀ (by simpa using h2))
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup (↥GZ ⧸ CFSG.pCore 2 ↥GZ)) ≤ 2 := by
    rw [pRank_modO2_eq GZ hp hp2, ← pRank_top_subtype (p := p) GZ]
    exact s.sqtkGroup_GZ.1 p hp hp2
  obtain ⟨A, ⟨KZ, hKZ, rfl⟩, hle⟩ := L436.exists_le_of_commuting hcomm hO2 hKs hKp
    hyp.two_le hcard (eKbar.trans eF) hKL hp2
    (⟨⟨a, hK₂GZ haK₂⟩, Subgroup.mem_subgroupOf.mpr haK₂, rfl⟩ : ρ ⟨a, hK₂GZ haK₂⟩ ∈ img K₂)
    (hρord _ hao) (hρord _ hyo) hyK' hyL hyS hrank
  refine ⟨KZ, hKZ, ?_⟩
  have hKZsup : K₂ ≤ KZ ⊔ QZ := by
    intro k hk
    obtain ⟨x, hx, hxk⟩ := hle ⟨⟨k, hK₂GZ hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have h1 : ρ (x⁻¹ * ⟨k, hK₂GZ hk⟩) = 1 := by rw [map_mul, map_inv, hxk, inv_mul_cancel]
    have h2 := (hρ1 _).mp h1
    have e : k = (x : G) * ((x : G)⁻¹ * k) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
      (Subgroup.mem_sup_right (by simpa using h2))
  have hQZO : QZ ≤ pCoreOf 2 H₀ := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQZH₀
    (hH₀GZ.trans (le_normalizer_pCoreOf 2 GZ)) (pCoreOf_isPGroup 2 GZ)
  have hQZN : QZ ≤ Subgroup.normalizer (KZ : Set G) :=
    hQZO.trans (P134.pCoreOf_le_normalizer_of_mem_cComp hKZ)
  exact L436.le_of_perfect_of_le_sup_of_isPGroup' (_root_.sup_le Subgroup.le_normalizer hQZN)
    (pCoreOf_isPGroup 2 GZ) (perfectCore_perfect _) hKZsup

end Setting436Sp4

theorem step436KZ_holds (h37 : A37ForSQTK) (h39 : A39ForSQTK) : Step436KZ := by
  intro G _ _ T M L n I H K t s
  exact s.exists_KZ h37 h39

end CFSG.Quasithin.H13.Ch4
