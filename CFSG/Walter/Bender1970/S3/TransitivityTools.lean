module

public import CFSG.Walter.Bender1970.S3.Tools
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped commutatorElement

section Involution

variable {G : Type*} [Group G]

theorem commutator_zpowers_le_of_forall {A C : Subgroup G} {t : G} (ht : orderOf t = 2)
    (h : ∀ a ∈ A, ⁅a, t⁆ ∈ C) : ⁅A, Subgroup.zpowers t⁆ ≤ C := by
  rw [Subgroup.commutator_le]
  intro a ha g hg
  rcases eq_one_or_eq_of_mem_zpowers ht hg with rfl | rfl
  · rw [commutatorElement_one_right]
    exact C.one_mem
  · exact h a ha

theorem commutatorElement_mem_centralizer_of_conj {N : Subgroup G} {x s : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G))
    (hs : (∀ n ∈ N, s * n * s⁻¹ = n) ∨ (∀ n ∈ N, s * n * s⁻¹ = n⁻¹)) :
    ⁅x, s⁆ ∈ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hm : x⁻¹ * n * x ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) n).mp hn
    simpa using this
  have key : ⁅x, s⁆ * n * ⁅x, s⁆⁻¹ = n := by
    rcases hs with hs | hs
    · have h1 : s⁻¹ * n * s = n := by
        have := hs n hn
        calc s⁻¹ * n * s = s⁻¹ * (s * n * s⁻¹) * s := by rw [this]
          _ = n := by group
      have h2 := hs _ hm
      calc ⁅x, s⁆ * n * ⁅x, s⁆⁻¹ = x * (s * (x⁻¹ * (s⁻¹ * n * s) * x) * s⁻¹) * x⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = n := by rw [h1, h2]; group
    · have h1 : s⁻¹ * n * s = n⁻¹ := by
        have := hs n⁻¹ (N.inv_mem hn)
        rw [inv_inv] at this
        calc s⁻¹ * n * s = s⁻¹ * (s * n⁻¹ * s⁻¹) * s := by rw [this]
          _ = n⁻¹ := by group
      have h2 := hs _ (N.inv_mem hm)
      calc ⁅x, s⁆ * n * ⁅x, s⁆⁻¹ = x * (s * (x⁻¹ * (s⁻¹ * n * s) * x) * s⁻¹) * x⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = x * (s * (x⁻¹ * n * x)⁻¹ * s⁻¹) * x⁻¹ := by rw [h1]; group
        _ = n := by rw [h2]; group
  calc n * ⁅x, s⁆ = ⁅x, s⁆ * n * ⁅x, s⁆⁻¹ * ⁅x, s⁆ := by rw [key]
    _ = ⁅x, s⁆ * n := by group

theorem mem_sup_of_le_normalizer {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G))
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, (a₂⁻¹ * b₁ * a₂) * b₂, B.mul_mem ?_ hb₂, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hAB ha₂)) b₁).mp hb₁
    simpa using this
  · rintro _ _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, by group⟩
    exact (Subgroup.mem_normalizer_iff.mp (hAB ha) b⁻¹).mp (B.inv_mem hb)

end Involution

section Components

variable {G : Type*} [Group G]

theorem IsComponentOf.of_le_normalizer {L Y X : Subgroup G} (hL : IsComponentOf L Y)
    (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set G)) : IsComponentOf L X :=
  ⟨hL.1.trans hYX, isSubnormal_subgroupOf_trans hL.1 hL.2.1
    (isSubnormal_subgroupOf_of_le_normalizer hYX hXY), hL.2.2⟩

theorem IsComponentOf.of_le {L X Y : Subgroup G} (hL : IsComponentOf L X) (hLY : L ≤ Y)
    (hYX : Y ≤ X) : IsComponentOf L Y :=
  ⟨hLY, isSubnormal_subgroupOf_of_le hLY hYX hL.2.1, hL.2.2⟩

theorem IsComponentOf.map_conj {G : Type} [Group G] [Finite G] {L X : Subgroup G}
    (hL : IsComponentOf L X) (g : G) :
    IsComponentOf (L.map (MulAut.conj g).toMonoidHom) (X.map (MulAut.conj g).toMonoidHom) :=
  ⟨Subgroup.map_mono hL.1, isSubnormal_map_conj g hL.2.1,
    fstar_isQuasisimple_conjugateSubgroup L g hL.2.2⟩

variable [Finite G]

theorem commutator_eq_bot_or_le_of_isComponentOf {L X A : Subgroup G} (hL : IsComponentOf L X)
    (hA : A ≤ Subgroup.normalizer (L : Set G)) : ⁅L, A⁆ = ⊥ ∨ L ≤ ⁅L, A⁆ := by
  have hLL : IsComponentOf L L :=
    ⟨le_rfl, by rw [Subgroup.subgroupOf_self]; exact Subgroup.IsSubnormal.top, hL.2.2⟩
  have hc := isComponent_subgroupOf_of_isComponentOf hLL
  have hle : ⁅L, A⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hA
  have hN : (⁅L, A⁆.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
      (Subgroup.normalizer_commutator_ge_left L A)
  rcases CFSG.LocalCores.component_normal_subgroup hc hN with h | h
  · exact Or.inr (CFSG.LocalCores.le_of_subgroupOf_le le_rfl h)
  · left
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf (le_refl L) h
    rw [inf_of_le_left hle, Subgroup.commutator_comm] at h1
    have hP : Group.IsPerfect L := (Group.isPerfect_def).2 hL.2.2.2.1
    exact CFSG.LocalCores.perfect_double_commutator hP h1

end Components

section Cyclic

variable {G : Type*} [Group G] [Finite G]

theorem card_range_dvd_of_isCyclic {V Q : Type*} [Group V] [Group Q] [Finite V] [IsCyclic Q]
    {p : ℕ} (hV : ∀ x : V, x ^ p = 1) (φ : V →* Q) : Nat.card φ.range ∣ p := by
  have : IsCyclic φ.range := Subgroup.isCyclic _
  rw [← IsCyclic.exponent_eq_card]
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
  obtain ⟨_, x, rfl⟩ := y
  exact Subtype.ext (by simp [← map_pow, hV x])

theorem card_le_mul_card_inf_of_isCyclic {U C V : Subgroup G} [(C.subgroupOf U).Normal]
    (hcyc : IsCyclic (U ⧸ C.subgroupOf U)) (hVU : V ≤ U) {p : ℕ} (hp : p.Prime)
    (hV : ∀ x ∈ V, x ^ p = 1) : Nat.card V ≤ p * Nat.card (V ⊓ C : Subgroup G) := by
  set φ : V →* U ⧸ C.subgroupOf U :=
    (QuotientGroup.mk' (C.subgroupOf U)).comp (Subgroup.inclusion hVU) with hφ
  have hker : φ.ker = C.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hcardker : Nat.card φ.ker = Nat.card (V ⊓ C : Subgroup G) := by
    rw [hker, ← Subgroup.card_map_of_injective V.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h1 := card_range_dvd_of_isCyclic (fun x : V => Subtype.ext (hV x x.2)) φ
  have h2 : Nat.card V = Nat.card φ.ker * Nat.card φ.range := by
    rw [← φ.ker.card_mul_index, Subgroup.index_ker]
  rw [h2, hcardker, mul_comm]
  exact Nat.mul_le_mul_right _ (Nat.le_of_dvd hp.pos h1)

theorem exists_mem_inv_mul_mem_of_isCyclic {U C V : Subgroup G} [(C.subgroupOf U).Normal]
    (hcyc : IsCyclic (U ⧸ C.subgroupOf U)) (hVU : V ≤ U) {p : ℕ} (hp : p.Prime)
    (hV : ∀ x ∈ V, x ^ p = 1) {R : Subgroup G} (hRV : R ≤ V) (hRC : ¬ R ≤ C) {v : G}
    (hv : v ∈ V) : ∃ r ∈ R, r⁻¹ * v ∈ C := by
  classical
  set φ : V →* U ⧸ C.subgroupOf U :=
    (QuotientGroup.mk' (C.subgroupOf U)).comp (Subgroup.inclusion hVU) with hφ
  have hφker : ∀ w : V, φ w = 1 ↔ (w : G) ∈ C := by
    intro w
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    rfl
  set R' := R.subgroupOf V with hR'
  have h1 := card_range_dvd_of_isCyclic (fun x : V => Subtype.ext (hV x x.2)) φ
  obtain ⟨r₀, hr₀R, hr₀C⟩ := Set.not_subset.mp hRC
  have hne : R'.map φ ≠ ⊥ := by
    intro h
    have hmem : φ ⟨r₀, hRV hr₀R⟩ ∈ R'.map φ := ⟨⟨r₀, hRV hr₀R⟩, hr₀R, rfl⟩
    rw [h, Subgroup.mem_bot, hφker] at hmem
    exact hr₀C hmem
  have hle : R'.map φ ≤ φ.range := Subgroup.map_le_range φ R'
  have hcard : Nat.card φ.range ≤ Nat.card (R'.map φ) := by
    have h2 : Nat.card (R'.map φ) ∣ Nat.card φ.range := Subgroup.card_dvd_of_le hle
    have h3 : Nat.card (R'.map φ) ≠ 1 := by
      rw [Ne, Subgroup.card_eq_one]
      exact hne
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · rw [h]
      exact Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    · rcases (Nat.dvd_prime hp).mp (h ▸ h2) with h' | h'
      · exact absurd h' h3
      · rw [h, h']
  have heq : R'.map φ = φ.range := Subgroup.eq_of_le_of_card_ge hle hcard
  have hv' : φ ⟨v, hv⟩ ∈ R'.map φ := heq ▸ ⟨⟨v, hv⟩, rfl⟩
  obtain ⟨r, hrR, hrv⟩ := hv'
  refine ⟨r, hrR, ?_⟩
  have h4 : φ (r⁻¹ * ⟨v, hv⟩) = 1 := by rw [map_mul, map_inv, hrv, inv_mul_cancel]
  rw [hφker] at h4
  exact h4

end Cyclic

section Coprime

variable {G : Type*} [Group G] [Finite G]

theorem le_iSup_inf_centralizer {E N : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hEcomm : IsMulCommutative E) (hEexp : ∀ x ∈ E, x ^ p = 1) (hEcard : p ^ 2 ≤ Nat.card E)
    (hEN : E ≤ Subgroup.normalizer (N : Set G)) (hcop : ¬ p ∣ Nat.card N) :
    N ≤ ⨆ (e : G) (_ : e ∈ E) (_ : e ≠ 1), N ⊓ Subgroup.centralizer ({e} : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hEexp x x.2) }
  let _ : MulDistribMulAction E N := Subgroup.conjMulDistribMulActionOfLeNormalizer E N hEN
  have : E.Normalizes N := ⟨hEN⟩
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := E) (H := N)
    hEcard hcop
  intro x hx
  have h1 : (⟨x, hx⟩ : N) ∈ ⨆ (a : E) (_ : a ≠ 1),
      CFSG.fixedPointSubgroup (Subgroup.zpowers a) N := hgen ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem N.subtype h1
  simp only [Subgroup.map_iSup] at h2
  have h3 : (⨆ (a : E) (_ : a ≠ 1),
      (CFSG.fixedPointSubgroup (Subgroup.zpowers a) N).map N.subtype) ≤
      ⨆ (e : G) (_ : e ∈ E) (_ : e ≠ 1), N ⊓ Subgroup.centralizer ({e} : Set G) := by
    refine iSup₂_le fun a ha => ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) N := hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy'
    have hya : (a : G) * y * (a : G)⁻¹ = y := by
      have h4 := congrArg Subtype.val hy'
      rwa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h4
    have hmem : (y : G) ∈ N ⊓ Subgroup.centralizer ({(a : G)} : Set G) := by
      refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (y : G) * a = (a : G) * y * (a : G)⁻¹ * a := by rw [hya]
        _ = a * y := by group
    have ha' : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    exact le_iSup₂_of_le (f := fun (e : G) (_ : e ∈ E) =>
      ⨆ (_ : e ≠ 1), N ⊓ Subgroup.centralizer ({e} : Set G)) (a : G) a.2
      (le_iSup_of_le ha' le_rfl) hmem
  exact h3 h2

theorem exists_inf_centralizer_ne_bot {E N : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hEcomm : IsMulCommutative E) (hEexp : ∀ x ∈ E, x ^ p = 1) (hE1 : E ≠ ⊥)
    (hEN : E ≤ Subgroup.normalizer (N : Set G)) (hcop : ¬ p ∣ Nat.card N) (hN : N ≠ ⊥) :
    ∃ B ≤ E, Nat.card E = p * Nat.card B ∧
      N ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p E :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hEexp x x.2) }
  have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hE1
  let _ : MulDistribMulAction E N := Subgroup.conjMulDistribMulActionOfLeNormalizer E N hEN
  have : E.Normalizes N := ⟨hEN⟩
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := E) (H := N) hcop
  by_contra hcon
  push Not at hcon
  apply hN
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : N) ∈ ⨆ (B : Subgroup E) (_ : B.index = p),
      CFSG.fixedPointSubgroup B N := hgen ▸ Subgroup.mem_top _
  have h2 : (⨆ (B : Subgroup E) (_ : B.index = p), CFSG.fixedPointSubgroup B N) = ⊥ := by
    refine le_bot_iff.mp (iSup₂_le fun B hB => ?_)
    have hcardB : Nat.card E = p * Nat.card (B.map E.subtype) := by
      rw [Subgroup.card_map_of_injective E.subtype_injective, ← B.card_mul_index, hB, mul_comm]
    have h3 := hcon (B.map E.subtype) (Subgroup.map_subtype_le B) hcardB
    intro y hy
    have hmem : (y : G) ∈ N ⊓ Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G) := by
      refine ⟨y.2, ?_⟩
      show (y : G) ∈ Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hyb : (b : E) • y = y := hy ⟨b, hb⟩
      have h4 := congrArg Subtype.val hyb
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h4
      calc ((b : E) : G) * y = (b : G) * y * (b : G)⁻¹ * b := by group
        _ = y * b := by rw [h4]
    rw [h3, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  rw [h2, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

end Coprime

end CFSG.Walter
