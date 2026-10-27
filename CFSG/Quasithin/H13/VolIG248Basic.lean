module

public import CFSG.Quasithin.H13.VolIG248Tilde
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F9Section
public import CFSG.Quasithin.Background.G2A5Six

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.Quasithin.A5Model Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

namespace G248

theorem comm_Q_mem_core {V V₁ L T H : Subgroup G} (hb : AlmostSpecialCoreBase V V₁ L T H)
    (hg : G22Conclusion V V₁ T H) {u q : G} (hu : u ∈ conjClosure V H) (hq : q ∈ pCoreOf 2 H)
    (hqN : q ∈ normalizer (V₁ : Set G)) : u * q * u⁻¹ * q⁻¹ ∈ V₁ := by
  have hcc := hb.conjClosure_le_N hg
  have hqQ : tmk V₁ ⟨q, hqN⟩ ∈ tildeOf V₁ (pCoreOf 2 H) := secMk_mem_secImg hq
  have hxy : tmk V₁ ⟨u, hcc hu⟩ * tmk V₁ ⟨q, hqN⟩ = tmk V₁ ⟨q, hqN⟩ * tmk V₁ ⟨u, hcc hu⟩ :=
    (mem_centralizer_of_mem_omegaOneCenterOf
      ((secImg_le_iff.1 hg.one.2) ⟨u, hcc hu⟩ hu) hqQ).symm
  exact commutator_mem_of_secMk_commute hxy

theorem sq_eq_one_of_mem_K4 : ∀ σ : A5, σ ∈ K4 → σ ^ 2 = 1 := by decide

theorem exists_mul_pow_mem_K4 : ∀ σ : A5, σ ∈ A4s → ∃ k : ℕ, k < 3 ∧ σ * (c3A ^ k)⁻¹ ∈ K4 := by
  decide

structure Setting (V V₁ L T H : Subgroup G) (g : G) where
  St : A5SettingCore V V₁ L T H
  comm : ⁅conjClosure V H, lOne L V₁⁆ ⊔ V₁ = conjClosure V H
  O2 : pCoreOf 2 (lOne L V₁) ≤ pCoreOf 2 H
  hg : g ∈ L
  hgN : g ∉ normalizer (V₁ : Set G)

namespace Setting

variable [Finite G] {V V₁ L T H : Subgroup G} {g : G} (X : Setting V V₁ L T H g)
include X

omit [Finite G] in
theorem LT_le_normL : L ⊔ T ≤ normalizer (L : Set G) :=
  sup_le le_normalizer X.St.hyp.base.T_le_normL

omit [Finite G] in
theorem exists_not_comm : ∃ l ∈ L, ∃ v ∈ conjClosure V₁ L, l * v * l⁻¹ ≠ v := by
  obtain ⟨l, hl⟩ := X.St.D.surj c3A
  by_contra hcon
  push Not at hcon
  have h1 : X.St.D.alpha ⟨l, X.St.D.hnorm l.2⟩ = 1 := by
    rw [RawData5.alpha_eq_one_iff]
    intro v
    exact hcon l l.2 v v.2
  rw [X.St.D.alpha_of_mem, hl] at h1
  have h2 : ((c3A : A5) : Equiv.Perm (Fin 5)) = 1 :=
    pact_injective (h1.trans (map_one pact).symm)
  exact absurd h2 (by decide)

omit [Finite G] in
theorem commutator_VL_eq : ⁅conjClosure V₁ L, L⁆ = conjClosure V₁ L := by
  set Y : Subgroup G := ⁅conjClosure V₁ L, L⁆ with hY
  have hYV : Y ≤ conjClosure V₁ L := by
    rw [hY, commutator_le]
    intro v hv l hl
    have h1 : l * v⁻¹ * l⁻¹ ∈ conjClosure V₁ L :=
      (mem_normalizer_iff.mp (X.St.D.hnorm hl) _).mp (inv_mem hv)
    rw [commutatorElement_def]
    have e : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
    rw [e]
    exact mul_mem hv h1
  have hYL : L ≤ normalizer (Y : Set G) :=
    F9.le_normalizer_commutator_of_le X.St.D.hnorm le_normalizer
  rcases X.St.irreducible_L hYV hYL with hbot | heq
  · exfalso
    obtain ⟨l, hl, v, hv, hne⟩ := X.exists_not_comm
    have hc : ⁅v, l⁆ ∈ Y := commutator_mem_commutator hv hl
    rw [hbot, mem_bot, commutatorElement_def] at hc
    apply hne
    calc l * v * l⁻¹ = (v * l * v⁻¹ * l⁻¹)⁻¹ * v := by group
      _ = v := by rw [hc, inv_one, one_mul]
  · exact heq

omit [Finite G] in
theorem VL_le_L : conjClosure V₁ L ≤ L := by
  rw [← X.commutator_VL_eq, commutator_le]
  intro v hv l hl
  rw [commutatorElement_def]
  have hvN : v ∈ normalizer (L : Set G) := X.LT_le_normL (X.St.VL_le_LT hv)
  have h1 : v * l * v⁻¹ ∈ L := (mem_normalizer_iff.mp hvN l).mp hl
  exact mul_mem h1 (inv_mem hl)

omit [Finite G] in
theorem U_le_L : conjClosure V H ≤ L := by
  rw [← X.comm]
  refine sup_le ?_ ((le_conjClosure V₁ L).trans X.VL_le_L)
  rw [commutator_le]
  intro u hu l hl
  have hlL : l ∈ L := ((oTwoUpper_le _) hl).1
  rw [commutatorElement_def]
  have h1 : u * l * u⁻¹ ∈ L := (mem_normalizer_iff.mp (X.St.U_le_normL hu) l).mp hlL
  exact mul_mem h1 (inv_mem hlL)

theorem sup_eq : L ⊔ conjClosure V H = L := sup_eq_left.2 X.U_le_L

theorem I_eq : conjClosure V H ⊔ rconj (conjClosure V H) g = L := by
  rw [X.St.hyp.G24_two X.hg X.hgN, X.sup_eq]

theorem mem_pCoreOf_L_iff {x : G} (hx : x ∈ L) :
    x ∈ pCoreOf 2 L ↔ x ∈ pCoreOf 2 (L ⊔ T) := by
  have h1 := X.St.inf_pCoreOf_eq_ker (I := L) X.sup_eq.symm
  rw [X.St.D.ker_eq] at h1
  have h2 : (⟨x, hx⟩ : ↥L) ∈ (L ⊓ pCoreOf 2 L).subgroupOf L ↔
      (⟨x, hx⟩ : ↥L) ∈ (pCoreOf 2 (L ⊔ T)).subgroupOf L := by rw [h1]
  simp only [mem_subgroupOf, mem_inf] at h2
  exact ⟨fun h => h2.1 ⟨hx, h⟩, fun h => (h2.2 h).2⟩

theorem theta_eq_one_iff (x : ↥L) : X.St.D.θ x = 1 ↔ (x : G) ∈ pCoreOf 2 L := by
  rw [X.mem_pCoreOf_L_iff x.2, ← MonoidHom.mem_ker, X.St.D.ker_eq, mem_subgroupOf]

omit [Finite G] X in
theorem lOne_le_L : lOne L V₁ ≤ L := fun _ hl => ((oTwoUpper_le _) hl).1

omit [Finite G] X in
theorem lOne_le_N : lOne L V₁ ≤ normalizer (V₁ : Set G) := fun _ hl => ((oTwoUpper_le _) hl).2

omit [Finite G] in
theorem lOne_le_H : lOne L V₁ ≤ H := le_sup_left.trans X.St.hyp.base.lOne_sup_le

omit [Finite G] in
theorem theta_lOne {l : G} (hl : l ∈ lOne L V₁) : X.St.D.θ ⟨l, lOne_le_L hl⟩ ∈ A4s :=
  X.St.theta_mem_A4s_of_normalizer _ (lOne_le_N hl)

omit [Finite G] in
theorem mem_normalizer_K4 {y : G} (hy : y ∈ L) (hyA : X.St.D.θ ⟨y, hy⟩ ∈ A4s) :
    y ∈ normalizer (((K4.comap X.St.D.θ).map L.subtype : Subgroup G) : Set G) := by
  have key : ∀ (y : G) (hy : y ∈ L), X.St.D.θ ⟨y, hy⟩ ∈ A4s →
      ∀ x ∈ (K4.comap X.St.D.θ).map L.subtype, y * x * y⁻¹ ∈ (K4.comap X.St.D.θ).map L.subtype := by
    rintro y hy hyA _ ⟨a, ha, rfl⟩
    refine ⟨⟨y, hy⟩ * a * ⟨y, hy⟩⁻¹, ?_, rfl⟩
    show X.St.D.θ (⟨y, hy⟩ * a * ⟨y, hy⟩⁻¹) ∈ K4
    rw [map_mul, map_mul, map_inv]
    exact K4_norm _ hyA _ ha
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key y hy hyA x, fun hx => ?_⟩
  have hyA' : X.St.D.θ ⟨y⁻¹, inv_mem hy⟩ ∈ A4s := by
    have : (⟨y⁻¹, inv_mem hy⟩ : ↥L) = (⟨y, hy⟩ : ↥L)⁻¹ := rfl
    rw [this, map_inv]
    exact inv_mem hyA
  have := key y⁻¹ (inv_mem hy) hyA' _ hx
  simpa [mul_assoc] using this

theorem mem_pCoreOf_lOne {l : G} (hl : l ∈ lOne L V₁) (hK : X.St.D.θ ⟨l, lOne_le_L hl⟩ ∈ K4) :
    l ∈ pCoreOf 2 (lOne L V₁) := by
  set D := X.St.D
  set M : Subgroup G := lOne L V₁ ⊓ (K4.comap D.θ).map L.subtype with hM
  have hlM : l ∈ M := ⟨hl, ⟨⟨l, lOne_le_L hl⟩, hK, rfl⟩⟩
  have hMle : M ≤ lOne L V₁ := inf_le_left
  have hMN : lOne L V₁ ≤ normalizer (M : Set G) := by
    intro y hy
    refine inf_normalizer_le_normalizer_inf ⟨?_, X.mem_normalizer_K4 (lOne_le_L hy)
      (X.theta_lOne hy)⟩
    exact le_normalizer_oTwoUpper _ ((oTwoUpper_le _) hy)
  have hMp : IsPGroup 2 M := by
    refine isPGroup_two_of_forall fun c hc => ?_
    obtain ⟨-, ⟨a, ha, rfl⟩⟩ := hc
    have h2 : D.θ (a ^ 2) = 1 := by
      rw [map_pow]
      exact sq_eq_one_of_mem_K4 _ ha
    have h3 : ((a ^ 2 : ↥L) : G) ∈ pCoreOf 2 (L ⊔ T) :=
      (X.mem_pCoreOf_L_iff (a ^ 2).2).1 ((X.theta_eq_one_iff _).1 h2)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one_of_mem (pCoreOf_isPGroup 2 (L ⊔ T)) h3
    refine ⟨j + 1, ?_⟩
    rw [pow_succ', pow_mul]
    simpa using hj
  exact le_pCoreOf_of_le_normalizer 2 hMle hMN hMp hlM

theorem exists_t : ∃ t : ↥L, (t : G) ∈ lOne L V₁ ∧ X.St.D.θ t = c3A :=
  X.St.D.exists_l1_of_odd (le_conjClosure V₁ L) X.St.D.line c3A c3A_mem c3A_pow

theorem pow_three_mem {t : ↥L} (ht : (t : G) ∈ lOne L V₁) (htθ : X.St.D.θ t = c3A) :
    (t : G) ^ 3 ∈ pCoreOf 2 H := by
  have h3 : ((t : G) ^ 3) ∈ lOne L V₁ := pow_mem ht 3
  refine X.O2 (X.mem_pCoreOf_lOne h3 ?_)
  have : (⟨(t : G) ^ 3, lOne_le_L h3⟩ : ↥L) = t ^ 3 := rfl
  rw [this, map_pow, htθ, c3A_pow]
  exact one_mem _

theorem exists_pow {t : ↥L} (ht : (t : G) ∈ lOne L V₁) (htθ : X.St.D.θ t = c3A) {l : G}
    (hl : l ∈ lOne L V₁) : ∃ k : ℕ, l * ((t : G) ^ k)⁻¹ ∈ pCoreOf 2 H := by
  obtain ⟨k, -, hk⟩ := exists_mul_pow_mem_K4 _ (X.theta_lOne hl)
  refine ⟨k, X.O2 (X.mem_pCoreOf_lOne (mul_mem hl (inv_mem (pow_mem ht k))) ?_)⟩
  have : (⟨l * ((t : G) ^ k)⁻¹, lOne_le_L (mul_mem hl (inv_mem (pow_mem ht k)))⟩ : ↥L) =
      ⟨l, lOne_le_L hl⟩ * (t ^ k)⁻¹ := rfl
  rw [this, map_mul, map_inv, map_pow, htθ]
  exact hk

omit [Finite G] in
theorem lOne_le_normU : lOne L V₁ ≤ normalizer (conjClosure V H : Set G) :=
  X.lOne_le_H.trans (le_normalizer_conjClosure V H)

theorem norm_mem {t : ↥L} (ht : (t : G) ∈ lOne L V₁) (htθ : X.St.D.θ t = c3A) :
    ∀ y ∈ conjClosure V H,
      y * ((t : G) * y * (t : G)⁻¹) * ((t : G) ^ 2 * y * ((t : G) ^ 2)⁻¹) ∈ V₁ := by
  have hb := X.St.hyp.base
  have hg := X.St.hyp.g22
  refine norm_mem_of_commutator_sup (hb.conjClosure_le_N hg)
    (fun x hx y hy => X.St.hyp.G22_commutator_mem hx hy)
    (X.lOne_le_normU ht) (lOne_le_N ht) X.lOne_le_normU ?_ ?_ X.comm
  · intro u hu
    have h1 := comm_Q_mem_core hb hg (inv_mem hu) (X.pow_three_mem ht htθ)
      (pow_mem (lOne_le_N ht) 3)
    have e : ((t : G) ^ 3 * u * ((t : G) ^ 3)⁻¹)⁻¹ * u =
        (u⁻¹ * (t : G) ^ 3 * u⁻¹⁻¹ * ((t : G) ^ 3)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  · intro l hl
    obtain ⟨k, hk⟩ := X.exists_pow ht htθ hl
    refine ⟨k, fun u hu => ?_⟩
    have hy : (t : G) ^ k * u * ((t : G) ^ k)⁻¹ ∈ conjClosure V H :=
      (mem_normalizer_iff.mp (pow_mem (X.lOne_le_normU ht) k) u).mp hu
    have h1 := comm_Q_mem_core hb hg (inv_mem hy) hk
      (mul_mem (lOne_le_N hl) (inv_mem (pow_mem (lOne_le_N ht) k)))
    have e : (l * u * l⁻¹)⁻¹ * ((t : G) ^ k * u * ((t : G) ^ k)⁻¹) =
        ((((t : G) ^ k * u * ((t : G) ^ k)⁻¹))⁻¹ * (l * ((t : G) ^ k)⁻¹) *
          (((t : G) ^ k * u * ((t : G) ^ k)⁻¹))⁻¹⁻¹ * (l * ((t : G) ^ k)⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1

theorem mem_V_of_comm_mem {t : ↥L} (ht : (t : G) ∈ lOne L V₁) (htθ : X.St.D.θ t = c3A)
    {x : G} (hx : x ∈ conjClosure V H) (hxV : (t : G) * x * (t : G)⁻¹ * x⁻¹ ∈ V) : x ∈ V := by
  have hb := X.St.hyp.base
  have htV : (t : G) ∈ normalizer (V : Set G) := by
    have h := F9.le_normalizer_commutator_of_le (X := lOne L V₁) (A := conjClosure V₁ L)
      (B := lOne L V₁) (lOne_le_L.trans X.St.D.hnorm) le_normalizer ht
    rwa [← X.St.hyp.V_eq] at h
  exact mem_of_conj_comm_mem hb.le_V (le_conjClosure V H) (hb.conjClosure_le_N X.St.hyp.g22)
    (fun x hx y hy => X.St.hyp.G22_commutator_mem hx hy) (fun x hx => X.St.hyp.G22_sq_mem hx)
    htV (X.norm_mem ht htθ) hx hxV

theorem inf_le_V : conjClosure V H ⊓ rconj (conjClosure V H) g ≤ V := by
  obtain ⟨t, ht, htθ⟩ := X.exists_t
  intro x hx
  have h5 := X.St.hyp.G24_five rfl X.hg X.hgN rfl
  have htI : (t : G) ∈ conjClosure V H ⊔ rconj (conjClosure V H) g := by
    rw [X.I_eq]
    exact t.2
  have hc : ⁅x, (t : G)⁆ ∈ conjClosure V₁ L :=
    h5 (commutator_mem_commutator (mem_sup_right hx) htI)
  have hcU : (t : G) * x * (t : G)⁻¹ * x⁻¹ ∈ conjClosure V H := by
    have h1 : (t : G) * x * (t : G)⁻¹ ∈ conjClosure V H :=
      (mem_normalizer_iff.mp (X.lOne_le_normU ht) x).mp hx.1
    exact mul_mem h1 (inv_mem hx.1)
  have hcVL : (t : G) * x * (t : G)⁻¹ * x⁻¹ ∈ conjClosure V₁ L := by
    have := inv_mem hc
    rw [commutatorElement_def] at this
    simpa [mul_assoc] using this
  exact X.mem_V_of_comm_mem ht htθ hx.1 (X.St.inf_le_V hcVL hcU)

theorem S₂_eq : conjClosure V₁ L ⊔ (conjClosure V H ⊓ rconj (conjClosure V H) g) =
    conjClosure V₁ L :=
  sup_eq_left.2 (X.inf_le_V.trans X.St.V_le_VL)

end Setting

end G248

end CFSG.Quasithin.H13.VolI
