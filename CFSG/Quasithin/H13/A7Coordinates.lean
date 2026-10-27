module

public import CFSG.Quasithin.H13.A7HyperplaneBasic
public import CFSG.Quasithin.SteinbergCBSevenSylowAFive
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.H13.Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB
open scoped Pointwise

section Config

variable {G : Type*} [Group G]

structure A7NatConfig (T L V : Subgroup G) (ψ : V ≃* Multiplicative (evenWeight 7)) : Prop where
  le_T : V ≤ T
  L_le : L ≤ normalizer (V : Set G)
  T_le : T ≤ normalizer (V : Set G)
  Lact : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ l σ
  Lonto : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ l σ
  Nact : ∀ n ∈ normalizer (V : Set G), ∃ σ, IsCoordAct ψ n σ
  NM : normalizer (V : Set G) ≤ normalizer (L : Set G)
  TI : ∀ m ∈ normalizer (L : Set G), CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥
  wt26 : ∀ v : V, (hammingNorm (vec ψ v) = 2 ∨ hammingNorm (vec ψ v) = 6) →
    centralizer ({(v : G)} : Set G) ≤ normalizer (L : Set G)
  wt4 : ∀ g : G, CFSG.conjugate V g ≠ V → ∀ v : V, (v : G) ∈ CFSG.conjugate V g → v ≠ 1 →
    hammingNorm (vec ψ v) = 4

end Config

@[expose] def StmtA7NaturalModuleConfig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∃ (V : Subgroup G) (ψ : V ≃* Multiplicative (evenWeight 7)), A7NatConfig T L V ψ

theorem pCoreOf_eq_map_cfsgPCore {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) :
    pCoreOf p H = (CFSG.pCore p H).map H.subtype := CFSG.openPCoreOf_eq_map_pCore p H

theorem threeCycle_mem : swap (0 : Fin 7) 1 * swap 1 2 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide +kernel

theorem threeCycle_ne_one : swap (0 : Fin 7) 1 * swap 1 2 ≠ 1 := by
  decide +kernel

theorem isCoordAct_one_of_mem_centralizer {G : Type*} [Group G] {V : Subgroup G}
    (ψ : V ≃* Multiplicative (evenWeight 7)) {l : G} (hl : l ∈ centralizer (V : Set G)) :
    IsCoordAct ψ l 1 := by
  intro x y hxy
  have : y = x := Subtype.ext (by rw [hxy, ← mem_centralizer_iff.1 hl x x.2]; group)
  rw [this, permAct7_one]

theorem A7NatConfig.not_le_centralizer {G : Type*} [Group G] {T L V : Subgroup G}
    {ψ : V ≃* Multiplicative (evenWeight 7)} (h : A7NatConfig T L V ψ) :
    ¬ L ≤ centralizer (V : Set G) := by
  intro hLC
  obtain ⟨l, hl, hact⟩ := h.Lonto _ threeCycle_mem
  exact threeCycle_ne_one
    (IsCoordAct.unique ψ (h.L_le hl) hact (isCoordAct_one_of_mem_centralizer ψ (hLC hl)))

@[expose] def relabelE (τ : Perm (Fin 7)) :
    Multiplicative (evenWeight 7) ≃* Multiplicative (evenWeight 7) where
  toFun x := Multiplicative.ofAdd ⟨permAct7 τ (Multiplicative.toAdd x : evenWeight 7),
    permAct7_mem_evenWeight τ (Multiplicative.toAdd x).2⟩
  invFun x := Multiplicative.ofAdd ⟨permAct7 τ⁻¹ (Multiplicative.toAdd x : evenWeight 7),
    permAct7_mem_evenWeight τ⁻¹ (Multiplicative.toAdd x).2⟩
  left_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp only [toAdd_ofAdd]
    exact permAct7_inv_apply τ _
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp only [toAdd_ofAdd]
    exact permAct7_apply_inv τ _
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp only [toAdd_ofAdd, toAdd_mul, Submodule.coe_add, map_add]

section Relabel

variable {G : Type*} [Group G] {V : Subgroup G}

theorem vec_trans_relabelE (ψ : V ≃* Multiplicative (evenWeight 7)) (τ : Perm (Fin 7)) (x : V) :
    vec (ψ.trans (relabelE τ)) x = permAct7 τ (vec ψ x) :=
  rfl

theorem permAct7_injective (τ : Perm (Fin 7)) : Function.Injective (permAct7 τ) := by
  intro a b h
  rw [← permAct7_inv_apply τ a, h, permAct7_inv_apply]

theorem isCoordAct_trans_relabelE_iff (ψ : V ≃* Multiplicative (evenWeight 7))
    (τ : Perm (Fin 7)) {n : G} {σ : Perm (Fin 7)} :
    IsCoordAct (ψ.trans (relabelE τ)) n (τ * σ * τ⁻¹) ↔ IsCoordAct ψ n σ := by
  have key : ∀ v, permAct7 (τ * σ * τ⁻¹) (permAct7 τ v) = permAct7 τ (permAct7 σ v) := by
    intro v
    rw [permAct7_conj, permAct7_inv_apply]
  unfold IsCoordAct
  simp only [vec_trans_relabelE, key]
  constructor
  · intro h x y hxy
    exact permAct7_injective τ (h x y hxy)
  · intro h x y hxy
    rw [h x y hxy]

theorem isCoordAct_trans_relabelE_iff' (ψ : V ≃* Multiplicative (evenWeight 7))
    (τ : Perm (Fin 7)) {n : G} {σ : Perm (Fin 7)} :
    IsCoordAct (ψ.trans (relabelE τ)) n σ ↔ IsCoordAct ψ n (τ⁻¹ * σ * τ) := by
  rw [← isCoordAct_trans_relabelE_iff ψ τ]
  congr! 1
  group

theorem hammingNorm_vec_trans_relabelE (ψ : V ≃* Multiplicative (evenWeight 7))
    (τ : Perm (Fin 7)) (x : V) :
    hammingNorm (vec (ψ.trans (relabelE τ)) x) = hammingNorm (vec ψ x) := by
  rw [vec_trans_relabelE, hammingNorm_permAct7]

theorem A7NatConfig.relabel {T L : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}
    (h : A7NatConfig T L V ψ) (τ : Perm (Fin 7)) :
    A7NatConfig T L V (ψ.trans (relabelE τ)) where
  le_T := h.le_T
  L_le := h.L_le
  T_le := h.T_le
  Lact l hl := by
    obtain ⟨σ, hσ, hact⟩ := h.Lact l hl
    refine ⟨τ * σ * τ⁻¹, ?_, (isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
    exact (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ
  Lonto σ hσ := by
    have hσ' : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ⁻¹
    rw [inv_inv] at hσ'
    obtain ⟨l, hl, hact⟩ := h.Lonto _ hσ'
    exact ⟨l, hl, (isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩
  Nact n hn := by
    obtain ⟨σ, hact⟩ := h.Nact n hn
    exact ⟨τ * σ * τ⁻¹, (isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
  NM := h.NM
  TI := h.TI
  wt26 v hv := by
    rw [hammingNorm_vec_trans_relabelE] at hv
    exact h.wt26 v hv
  wt4 g hg v hv hv1 := by
    rw [hammingNorm_vec_trans_relabelE]
    exact h.wt4 g hg v hv hv1

end Relabel

theorem card_filter_sevenCond_even : (Finset.univ.filter fun g : Perm (Fin 7) =>
    sevenCond g ∧ sign g = 1).card = 8 := by
  decide +kernel

theorem nat_card_sevenP_inf_alternating :
    Nat.card (sevenP ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) = 8 := by
  rw [← sevenA_inf_sevenB, ← card_filter_sevenCond_even, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_sevenA, mem_sevenB, mem_alternatingGroup, sevenCond,
    and_assoc]

theorem coord_card_perm_seven : Nat.card (Perm (Fin 7)) = 5040 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem coord_card_alternating_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem sevenP_inf_isSylow {B : Subgroup (Perm (Fin 7))}
    (hB : B = alternatingGroup (Fin 7) ∨ B = ⊤) :
    IsPGroup 2 ((sevenP ⊓ B).subgroupOf B) ∧ ¬ 2 ∣ ((sevenP ⊓ B).subgroupOf B).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ((sevenP ⊓ B).subgroupOf B) = Nat.card (sevenP ⊓ B : Subgroup _) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have hmul := ((sevenP ⊓ B).subgroupOf B).index_mul_card
  rw [hcard] at hmul
  rcases hB with rfl | rfl
  · rw [nat_card_sevenP_inf_alternating, coord_card_alternating_seven] at hmul
    refine ⟨IsPGroup.of_card (n := 3) ?_, ?_⟩
    · rw [hcard, nat_card_sevenP_inf_alternating]
      norm_num
    · omega
  · have h16 : Nat.card (sevenP ⊓ (⊤ : Subgroup (Perm (Fin 7))) : Subgroup _) = 16 := by
      rw [inf_top_eq, nat_card_sevenP]
    rw [h16, Nat.card_congr (Equiv.subtypeUnivEquiv mem_top), coord_card_perm_seven] at hmul
    refine ⟨IsPGroup.of_card (n := 4) ?_, ?_⟩
    · rw [hcard, h16]
      norm_num
    · omega

section Align

variable {G : Type*} [Group G]

theorem eq_alternating_or_eq_top {B : Subgroup (Perm (Fin 7))}
    (hAB : alternatingGroup (Fin 7) ≤ B) : B = alternatingGroup (Fin 7) ∨ B = ⊤ := by
  by_cases h : ∃ b ∈ B, sign b ≠ 1
  · right
    obtain ⟨b, hb, hsb⟩ := h
    rw [eq_top_iff]
    intro g _
    by_cases hg : sign g = 1
    · exact hAB (mem_alternatingGroup.2 hg)
    · have hsb' : sign b = -1 := (Int.units_eq_one_or (sign b)).resolve_left hsb
      have hsg' : sign g = -1 := (Int.units_eq_one_or (sign g)).resolve_left hg
      have : b⁻¹ * g ∈ alternatingGroup (Fin 7) := by
        rw [mem_alternatingGroup, map_mul, map_inv, hsb', hsg']
        rfl
      have h2 := mul_mem hb (hAB this)
      rwa [mul_inv_cancel_left] at h2
  · left
    push Not at h
    exact le_antisymm (fun b hb => mem_alternatingGroup.2 (h b hb)) hAB

theorem A7NatConfig.exists_aligned [Finite G] {T L V : Subgroup G} (hT : quasithinIsSylowTwo T)
    {ψ : V ≃* Multiplicative (evenWeight 7)} (h : A7NatConfig T L V ψ) :
    ∃ ψ' : V ≃* Multiplicative (evenWeight 7), A7NatConfig T L V ψ' ∧
      ∀ σ : Perm (Fin 7), (∃ t ∈ T, IsCoordAct ψ' t σ) ↔
        σ ∈ sevenP ∧ ∃ n ∈ normalizer (V : Set G), IsCoordAct ψ' n σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (V : Set G) with hNdef
  set ρ := coordRep ψ (le_refl N) h.Nact with hρ
  set B := ρ.range with hBdef
  have hρspec : ∀ n : N, IsCoordAct ψ n (ρ n) := coordRep_spec ψ (le_refl N) h.Nact
  have hρeq : ∀ (n : N) {σ : Perm (Fin 7)}, IsCoordAct ψ n σ → ρ n = σ := fun n σ hσ =>
    IsCoordAct.unique ψ n.2 (hρspec n) hσ
  have hAB : alternatingGroup (Fin 7) ≤ B := by
    intro σ hσ
    obtain ⟨l, hl, hact⟩ := h.Lonto σ hσ
    exact ⟨⟨l, h.L_le hl⟩, hρeq _ hact⟩
  have hB := eq_alternating_or_eq_top hAB
  set TG : Sylow 2 G := hT.1.toSylow hT.2 with hTG
  have hTGcoe : (TG : Subgroup G) = T := IsPGroup.toSylow_coe hT.1 hT.2
  have hTN : (TG : Subgroup G) ≤ N := hTGcoe ▸ h.T_le
  set TN : Sylow 2 N := TG.subtype hTN with hTNdef
  set TB : Sylow 2 B := TN.mapSurjective ρ.rangeRestrict_surjective with hTBdef
  obtain ⟨hS2, hSidx⟩ := sevenP_inf_isSylow hB
  set S0 : Sylow 2 B := hS2.toSylow hSidx with hS0def
  have hS0coe : (S0 : Subgroup B) = (sevenP ⊓ B).subgroupOf B := IsPGroup.toSylow_coe hS2 hSidx
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq B S0 TB
  have hTBmem : ∀ σ : B, σ ∈ (TB : Subgroup B) ↔ ∃ t ∈ T, ∃ ht : t ∈ N, ρ ⟨t, ht⟩ = σ := by
    intro σ
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : ((t : G)) ∈ T := by
        have : t ∈ (TG : Subgroup G).subgroupOf N := ht
        rw [mem_subgroupOf, hTGcoe] at this
        exact this
      exact ⟨t, ht', t.2, rfl⟩
    · rintro ⟨t, ht, htN, hσ⟩
      refine ⟨⟨t, htN⟩, ?_, Subtype.ext hσ⟩
      show (⟨t, htN⟩ : N) ∈ (TG : Subgroup G).subgroupOf N
      rw [mem_subgroupOf, hTGcoe]
      exact ht
  have hbmem : ∀ σ : B, σ ∈ (TB : Subgroup B) ↔ b⁻¹ * σ * b ∈ (S0 : Subgroup B) := by
    intro σ
    rw [← hb, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  set τ : Perm (Fin 7) := (b : Perm (Fin 7))⁻¹ with hτ
  refine ⟨ψ.trans (relabelE τ), h.relabel τ, fun σ => ?_⟩
  have hbB : (b : Perm (Fin 7)) ∈ B := b.2
  constructor
  · rintro ⟨t, ht, hact⟩
    rw [isCoordAct_trans_relabelE_iff'] at hact
    have htN : t ∈ N := h.T_le ht
    set σ₀ := τ⁻¹ * σ * τ with hσ₀
    have hσ₀B : σ₀ ∈ B := ⟨⟨t, htN⟩, hρeq ⟨t, htN⟩ hact⟩
    have h1 : (⟨σ₀, hσ₀B⟩ : B) ∈ (TB : Subgroup B) :=
      (hTBmem _).2 ⟨t, ht, htN, hρeq ⟨t, htN⟩ hact⟩
    rw [hbmem, hS0coe, mem_subgroupOf] at h1
    have h2 : ((b⁻¹ * ⟨σ₀, hσ₀B⟩ * b : B) : Perm (Fin 7)) = σ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      show (b : Perm (Fin 7))⁻¹ * σ₀ * b = σ
      rw [hσ₀, hτ, inv_inv]
      group
    rw [h2] at h1
    exact ⟨h1.1, t, htN, (isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩
  · rintro ⟨hσP, n, hn, hact⟩
    rw [isCoordAct_trans_relabelE_iff'] at hact
    set σ₀ := τ⁻¹ * σ * τ with hσ₀
    have hσ₀B : σ₀ ∈ B := ⟨⟨n, hn⟩, hρeq ⟨n, hn⟩ hact⟩
    have hσB : σ ∈ B := by
      have : σ = (b : Perm (Fin 7))⁻¹ * σ₀ * b := by
        rw [hσ₀, hτ, inv_inv]
        group
      rw [this]
      exact mul_mem (mul_mem (inv_mem hbB) hσ₀B) hbB
    have h1 : (⟨σ₀, hσ₀B⟩ : B) ∈ (TB : Subgroup B) := by
      rw [hbmem, hS0coe, mem_subgroupOf]
      have h2 : ((b⁻¹ * ⟨σ₀, hσ₀B⟩ * b : B) : Perm (Fin 7)) = σ := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        show (b : Perm (Fin 7))⁻¹ * σ₀ * b = σ
        rw [hσ₀, hτ, inv_inv]
        group
      rw [h2]
      exact ⟨hσP, hσB⟩
    obtain ⟨t, ht, htN, htσ⟩ := (hTBmem _).1 h1
    refine ⟨t, ht, (isCoordAct_trans_relabelE_iff' ψ τ).2 ?_⟩
    have := hρspec ⟨t, htN⟩
    rw [htσ] at this
    exact this

end Align

section Fixed

variable {G : Type*} [Group G]

theorem sevenP_gens_fix : ∀ v ∈ ({Pi.single 0 1 + Pi.single 1 1,
    Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1} : Set (Fin 7 → ZMod 2)),
    ∀ g ∈ ({swap 0 1, swap 2 3, swap 4 5, swap 2 4 * swap 3 5} : Set (Perm (Fin 7))),
      permAct7 g v = v := by
  intro v hv g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv hg
  rcases hv with rfl | rfl <;> rcases hg with rfl | rfl | rfl | rfl <;>
    (funext i; fin_cases i <;> decide)

theorem sevenP_fix {g : Perm (Fin 7)} (hg : g ∈ sevenP) {v : Fin 7 → ZMod 2}
    (hv : v = Pi.single 0 1 + Pi.single 1 1 ∨
      v = Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1) :
    permAct7 g v = v := by
  have hstab : sevenP ≤ vecStab v := by
    rw [sevenP, closure_le]
    intro g hg
    exact sevenP_gens_fix v (by rcases hv with rfl | rfl <;> simp) g hg
  exact hstab hg

theorem mem_omegaOneCenter_of_fixed {T V : Subgroup G} (hVT : V ≤ T)
    (ψ : V ≃* Multiplicative (evenWeight 7))
    (hTP : ∀ t ∈ T, ∃ σ ∈ sevenP, IsCoordAct ψ t σ) (hTV : T ≤ normalizer (V : Set G))
    {x : V} (hx : ∀ g ∈ sevenP, permAct7 g (vec ψ x) = vec ψ x) :
    (x : G) ∈ quasithinOmegaOneCenter T := by
  apply Subgroup.subset_closure
  refine ⟨⟨hVT x.2, ?_⟩, ?_⟩
  · show (x : G) ∈ centralizer (T : Set G)
    rw [mem_centralizer_iff]
    intro t ht
    obtain ⟨σ, hσ, hact⟩ := hTP t ht
    let y : V := ⟨t * x * t⁻¹, (mem_normalizer_iff.1 (hTV ht) x).1 x.2⟩
    have h1 := hact x y rfl
    rw [hx σ hσ] at h1
    have h2 : (t * x * t⁻¹ : G) = x := congrArg Subtype.val (vec_injective ψ h1)
    calc t * (x : G) = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [h2]
  · rw [pow_two]
    exact congrArg Subtype.val (sq_eq_one_of_vec ψ x)

end Fixed

end CFSG.Quasithin.H13.A7
