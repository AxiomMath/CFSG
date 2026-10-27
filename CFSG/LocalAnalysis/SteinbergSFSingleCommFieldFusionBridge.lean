module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFixedDefs
public import CFSG.LocalAnalysis.EvenBN.Common.FreeSeries
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBJQuadraticFieldFiltration

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.LocalAnalysis.ComponentInitial (sectionRightConj card_inf_centralizer_eq_mul_card_fixed
  coset_conj_of_section)
open CFSG.LocalAnalysis.EvenBN.Common (fixed_eq_range_of_card_eq_sq sectionRightConj_sectionRightConj)

section Bridge

theorem ffBridge_card_sq {G : Type*} [Group G] [Finite G] {a : G} (ha : a * a = 1) {r : ℕ}
    (V : Fin (r + 1) → Subgroup G) (hV0 : V 0 = ⊥)
    (hVle : ∀ i : Fin r, V i.castSucc ≤ V i.succ) (haV : ∀ i, a ∈ normalizer (V i : Set G))
    [∀ i : Fin r, ((V i.castSucc).subgroupOf (V i.succ)).Normal]
    [∀ i : Fin r, IsElementaryAbelian 2 (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ))]
    (hfac : ∀ i : Fin r,
      Nat.card {q : V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ) |
        sectionRightConj (haV i.succ) (haV i.castSucc) q = q} ^ 2 =
        Nat.card (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ))) :
    ∀ i : Fin r, Nat.card (V i.succ ⊓ centralizer {a} : Subgroup G) ^ 2 =
      Nat.card (V i.succ) := by
  have key : ∀ j : Fin (r + 1), Nat.card (V j ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card (V j) ∧
      ∀ k ∈ V j, a * k * (a * k) = 1 → ∃ m ∈ V j, a * k = m⁻¹ * a * m := by
    intro j
    induction j using Fin.induction with
    | zero =>
      rw [hV0]
      refine ⟨by rw [bot_inf_eq, card_bot, one_pow], fun k hk _ => ?_⟩
      rw [mem_bot.mp hk]
      exact ⟨1, one_mem _, by group⟩
    | succ i ih =>
      obtain ⟨ihc, ihj⟩ := ih
      have h1 := card_inf_centralizer_eq_mul_card_fixed (hVle i) (haV i.succ) (haV i.castSucc) ha
        ihj
      have h2 := card_eq_card_quotient_mul_card_subgroup ((V i.castSucc).subgroupOf (V i.succ))
      rw [Nat.card_congr (subgroupOfEquivOfLe (hVle i)).toEquiv] at h2
      have h3 := hfac i
      set c := Nat.card (V i.castSucc ⊓ centralizer {a} : Subgroup G)
      set f := Nat.card {x | sectionRightConj (haV i.succ) (haV i.castSucc) x = x}
      set q := Nat.card (V i.succ ⧸ (V i.castSucc).subgroupOf (V i.succ))
      have hpos : 0 < c ^ 2 := pow_pos Nat.card_pos 2
      have hcard : Nat.card (V i.succ ⊓ centralizer {a} : Subgroup G) ^ 2 = Nat.card (V i.succ) := by
        rw [h1, mul_pow, h3, h2, ← ihc, mul_comm]
      have e : c ^ 2 * f ^ 2 = c ^ 2 * q := by
        rw [← mul_pow, ← h1, hcard, h2, ← ihc, mul_comm]
      have hfix := fixed_eq_range_of_card_eq_sq
        (sectionRightConj (haV i.succ) (haV i.castSucc))
        (sectionRightConj_sectionRightConj (haV i.succ) (haV i.castSucc) ha)
        (Nat.eq_of_mul_eq_mul_left hpos e).symm
      exact ⟨hcard, fun k hk hsq =>
        coset_conj_of_section (hVle i) (haV i.succ) (haV i.castSucc) ha hfix ihj hk hsq⟩
  exact fun i => (key i.succ).1

section Generic

open scoped IsMulCommutative
open CFSG.LocalAnalysis.ComponentInitial

theorem ffAbstract_card_sq {E : Type} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    {K : Type} [Field K] {m r : ℕ} (hK : Nat.card K = 2 ^ (2 * m))
    (μ : Kˣ →* MulAut E) (ν : MulAut E) (hν : ∀ x, ν (ν x) = x)
    (hνμ : ∀ (l : Kˣ) (x : E), ν (μ l (ν x)) = μ (l ^ 2 ^ m) x)
    (C : Fin (r + 1) → Subgroup E) (hC0 : C 0 = ⊥) (hCr : C (Fin.last r) = ⊤)
    (hCle : ∀ i : Fin r, C i.castSucc ≤ C i.succ)
    (hμC : ∀ (l : Kˣ) (i : Fin (r + 1)) (x : E), x ∈ C i → μ l x ∈ C i)
    (c : Fin r → E → K)
    (hc_mul : ∀ (i : Fin r) (x y : E), x ∈ C i.succ → y ∈ C i.succ → c i (x * y) = c i x + c i y)
    (hc_ker : ∀ (i : Fin r) (x : E), x ∈ C i.succ → (c i x = 0 ↔ x ∈ C i.castSucc))
    (hc_surj : ∀ (i : Fin r) (k : K), ∃ y ∈ C i.succ, c i y = k)
    (hc_equiv : ∀ (i : Fin r) (l : Kˣ) (x : E), x ∈ C i.succ → c i (μ l x) = (l : K) * c i x) :
    Nat.card E = Nat.card {x : E | ν x = x} ^ 2 := by
  classical
  have hA : ∀ x : Additive E, x + x = 0 := fun x => by
    show Additive.ofMul (Additive.toMul x * Additive.toMul x) = 0
    rw [mul_self_eq_one_of_isElementaryAbelian_two]
    rfl
  let σ : Kˣ →* AddMonoid.End (Additive E) :=
    { toFun := fun l => AddMonoidHom.mk' (fun x : Additive E => Additive.ofMul (μ l (Additive.toMul x)))
        (fun x y => by simp [map_mul])
      map_one' := by
        ext x
        show Additive.ofMul ((μ 1) (Additive.toMul x)) = x
        simp
      map_mul' := fun l l' => by
        ext x
        show Additive.ofMul ((μ (l * l')) (Additive.toMul x)) =
          Additive.ofMul ((μ l) ((μ l') (Additive.toMul x)))
        simp [map_mul] }
  let μA : Kˣ →* (AddMonoid.End (Additive E))ˣ := σ.toHomUnits
  have hμA : ∀ (l : Kˣ) (x : Additive E),
      ((μA l : (AddMonoid.End (Additive E))ˣ) : AddMonoid.End (Additive E)) x =
        Additive.ofMul (μ l (Additive.toMul x)) := fun l x => rfl
  let Ct : ℕ → AddSubgroup (Additive E) := fun i =>
    if h : i < r + 1 then Subgroup.toAddSubgroup (C ⟨i, h⟩) else ⊤
  have hCt : ∀ i (h : i < r + 1), Ct i = Subgroup.toAddSubgroup (C ⟨i, h⟩) := fun i h => by
    simp only [Ct, dif_pos h]
  have hCt_cast : ∀ i : Fin r, Ct (i : ℕ) = Subgroup.toAddSubgroup (C i.castSucc) := fun i => by
    rw [hCt i (by omega)]
    rfl
  have hCt_succ : ∀ i : Fin r, Ct ((i : ℕ) + 1) = Subgroup.toAddSubgroup (C i.succ) := fun i => by
    rw [hCt (i + 1) (by omega)]
    rfl
  have hCinv : ∀ i ≤ r, ∀ (l : Kˣ) (x : Additive E), x ∈ Ct i →
      ((μA l : (AddMonoid.End (Additive E))ˣ) : AddMonoid.End (Additive E)) x ∈ Ct i := by
    intro i hi l x hx
    have hi' : i < r + 1 := by omega
    rw [hCt i hi'] at hx ⊢
    exact hμC l ⟨i, hi'⟩ _ hx
  have hCmono : ∀ i < r, Ct i ≤ Ct (i + 1) := by
    intro i hi
    rw [hCt i (by omega), hCt (i + 1) (by omega)]
    exact (Subgroup.toAddSubgroup : Subgroup E ≃o AddSubgroup (Additive E)).monotone
      (hCle ⟨i, hi⟩)
  have hC0' : Ct 0 = ⊥ := by
    rw [hCt 0 (by omega)]
    have : C ⟨0, by omega⟩ = ⊥ := hC0
    rw [this]
    exact (Subgroup.toAddSubgroup : Subgroup E ≃o AddSubgroup (Additive E)).map_bot
  have hCr' : Ct r = ⊤ := by
    rw [hCt r (by omega)]
    have : C ⟨r, by omega⟩ = ⊤ := hCr
    rw [this]
    exact (Subgroup.toAddSubgroup : Subgroup E ≃o AddSubgroup (Additive E)).map_top
  have hlayer : ∀ i : Fin r,
      ∃ φ' : (Ct ((i : ℕ) + 1) ⧸ (Ct (i : ℕ)).addSubgroupOf (Ct ((i : ℕ) + 1))) ≃+ K,
        ∀ (l : Kˣ) (x : Ct ((i : ℕ) + 1)),
          φ' (⟨((μA l : (AddMonoid.End (Additive E))ˣ) : AddMonoid.End (Additive E)) x,
            hCinv _ i.2 l x x.2⟩ : Ct ((i : ℕ) + 1)) = (l : K) * φ' (x : Ct ((i : ℕ) + 1)) := by
    intro i
    have hmem : ∀ x : Ct ((i : ℕ) + 1), Additive.toMul (x : Additive E) ∈ C i.succ := fun x => by
      have key : (x : Additive E) ∈ Subgroup.toAddSubgroup (C i.succ) := by
        rw [← hCt_succ i]
        exact x.2
      exact key
    let ψ : Ct ((i : ℕ) + 1) →+ K :=
      AddMonoidHom.mk' (fun x => c i (Additive.toMul (x : Additive E)))
        (fun x y => hc_mul i _ _ (hmem x) (hmem y))
    have hker : ψ.ker = (Ct (i : ℕ)).addSubgroupOf (Ct ((i : ℕ) + 1)) := by
      ext x
      rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hCt_cast i]
      exact hc_ker i _ (hmem x)
    have hsurj : Function.Surjective ψ := fun k => by
      obtain ⟨y, hy, hyk⟩ := hc_surj i k
      exact ⟨⟨Additive.ofMul y, by rw [hCt_succ i]; exact hy⟩, hyk⟩
    refine ⟨(QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective ψ hsurj), fun l x => ?_⟩
    show c i (μ l (Additive.toMul (x : Additive E))) = (l : K) * c i (Additive.toMul (x : Additive E))
    exact hc_equiv i l _ (hmem x)
  choose φ' hφ' using hlayer
  let νA : Additive E ≃+ Additive E := MulEquiv.toAdditive ν
  have hνA : ∀ x : Additive E, νA (νA x) = x := fun x => by
    show Additive.ofMul (ν (ν (Additive.toMul x))) = x
    rw [hν]
    rfl
  have hνsymm : ∀ y : E, ν.symm y = ν y := fun y =>
    ν.injective (by rw [MulEquiv.apply_symm_apply, hν])
  have hνμA : ∀ (l : Kˣ) (x : Additive E),
      νA (((μA l : (AddMonoid.End (Additive E))ˣ) : AddMonoid.End (Additive E)) (νA.symm x)) =
        ((μA (l ^ 2 ^ m) : (AddMonoid.End (Additive E))ˣ) : AddMonoid.End (Additive E)) x := by
    intro l x
    show Additive.ofMul (ν (μ l (ν.symm (Additive.toMul x)))) =
      Additive.ofMul (μ (l ^ 2 ^ m) (Additive.toMul x))
    rw [hνsymm, hνμ]
  have key := ComponentInitial.QuadraticFieldFiltration.quadratic_field_scalar_filtration_fixed_commutators
    hK hA μA Ct hC0' hCr' hCmono hCinv φ' hφ' νA hνA hνμA
  have hinv : ∀ z : E, z⁻¹ = z := fun z =>
    inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_isElementaryAbelian_two z)
  have hfix : {x : E | ν x = x} = Set.range fun x => x⁻¹ * ν x := by
    ext x
    constructor
    · intro hx
      have hx' : Additive.ofMul x ∈ {y : Additive E | νA y = y} :=
        congrArg Additive.ofMul hx
      rw [key.1] at hx'
      obtain ⟨y, hy⟩ := hx'
      refine ⟨Additive.toMul y, ?_⟩
      have h2 : ν (Additive.toMul y) / Additive.toMul y = x := by
        have := congrArg Additive.toMul hy
        simpa [νA, toMul_sub] using this
      show (Additive.toMul y)⁻¹ * ν (Additive.toMul y) = x
      rw [← h2, div_eq_mul_inv, mul_comm]
    · rintro ⟨y, rfl⟩
      show ν (y⁻¹ * ν y) = y⁻¹ * ν y
      simp [map_mul, map_inv, hν, hinv, mul_comm]
  exact card_eq_card_fixed_sq ν hfix

theorem ffBridge_scalar_section {G : Type} [Group G] [Finite G] {K : Type} [Field K] {m r : ℕ}
    (hK : Nat.card K = 2 ^ (2 * m)) (μ : Kˣ →* G) {a : G} (ha : a * a = 1)
    (hμa : ∀ l : Kˣ, a⁻¹ * μ l * a = μ (l ^ 2 ^ m))
    {W' W : Subgroup G} [(W'.subgroupOf W).Normal] [IsElementaryAbelian 2 (↥W ⧸ W'.subgroupOf W)]
    (haW : a ∈ normalizer (W : Set G)) (haW' : a ∈ normalizer (W' : Set G))
    (C : Fin (r + 1) → Subgroup G) (hC0 : C 0 = W') (hCr : C (Fin.last r) = W)
    (hCle : ∀ i : Fin r, C i.castSucc ≤ C i.succ)
    (hμC : ∀ (l : Kˣ) (i : Fin (r + 1)), μ l ∈ normalizer (C i : Set G))
    (hC : ∀ i : Fin r, ∃ c : G → K, ScalarLayer μ (C i.succ) (C i.castSucc) c) :
    Nat.card {q : ↥W ⧸ W'.subgroupOf W | sectionRightConj haW haW' q = q} ^ 2 =
      Nat.card (↥W ⧸ W'.subgroupOf W) := by
  classical
  subst hC0 hCr
  choose c hc using hC
  have hmono : ∀ j : Fin (r + 1), C 0 ≤ C j := fun j =>
    (Fin.monotone_iff_le_succ.mpr hCle) (Fin.zero_le j)
  have hμW : ∀ l : Kˣ, μ l ∈ normalizer (C (Fin.last r) : Set G) := fun l => hμC l _
  have hμW' : ∀ l : Kˣ, μ l ∈ normalizer (C 0 : Set G) := fun l => hμC l _
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  let μE : Kˣ →* MulAut (↥(C (Fin.last r)) ⧸ (C 0).subgroupOf (C (Fin.last r))) :=
    { toFun := fun l => sectionRightConj (hμW l) (hμW' l)
      map_one' := by
        ext q
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
        rw [sectionRightConj_mk (hμW 1) (hμW' 1) k k (by simp)]
        rfl
      map_mul' := fun l l' => by
        ext q
        obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
        have hcomm : μ l' * μ l = μ (l * l') := by
          rw [← map_mul, mul_comm]
        let k₁ : ↥(C (Fin.last r)) :=
          ⟨(μ l')⁻¹ * k * μ l', inv_mul_mul_mem_of_mem_normalizer (hμW l') k.2⟩
        let k₂ : ↥(C (Fin.last r)) :=
          ⟨(μ l)⁻¹ * k₁ * μ l, inv_mul_mul_mem_of_mem_normalizer (hμW l) k₁.2⟩
        show sectionRightConj (hμW (l * l')) (hμW' (l * l')) (QuotientGroup.mk k) =
          sectionRightConj (hμW l) (hμW' l) (sectionRightConj (hμW l') (hμW' l') (QuotientGroup.mk k))
        rw [sectionRightConj_mk (hμW l') (hμW' l') k k₁ rfl,
          sectionRightConj_mk (hμW l) (hμW' l) k₁ k₂ rfl,
          sectionRightConj_mk (hμW (l * l')) (hμW' (l * l')) k k₂ ?_]
        show ((k₂ : ↥(C (Fin.last r))) : G) = (μ (l * l'))⁻¹ * k * μ (l * l')
        rw [← hcomm]
        change (μ l)⁻¹ * ((μ l')⁻¹ * k * μ l') * μ l = _
        group }
  have hνμ : ∀ (l : Kˣ) (q : ↥(C (Fin.last r)) ⧸ (C 0).subgroupOf (C (Fin.last r))),
      sectionRightConj haW haW' (μE l (sectionRightConj haW haW' q)) = μE (l ^ 2 ^ m) q := by
    intro l q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    let k₁ : ↥(C (Fin.last r)) := ⟨a⁻¹ * k * a, inv_mul_mul_mem_of_mem_normalizer haW k.2⟩
    let k₂ : ↥(C (Fin.last r)) :=
      ⟨(μ l)⁻¹ * k₁ * μ l, inv_mul_mul_mem_of_mem_normalizer (hμW l) k₁.2⟩
    let k₃ : ↥(C (Fin.last r)) := ⟨a⁻¹ * k₂ * a, inv_mul_mul_mem_of_mem_normalizer haW k₂.2⟩
    show sectionRightConj haW haW' (sectionRightConj (hμW l) (hμW' l)
        (sectionRightConj haW haW' (QuotientGroup.mk k))) =
      sectionRightConj (hμW (l ^ 2 ^ m)) (hμW' (l ^ 2 ^ m)) (QuotientGroup.mk k)
    rw [sectionRightConj_mk haW haW' k k₁ rfl, sectionRightConj_mk (hμW l) (hμW' l) k₁ k₂ rfl,
      sectionRightConj_mk haW haW' k₂ k₃ rfl,
      sectionRightConj_mk (hμW (l ^ 2 ^ m)) (hμW' (l ^ 2 ^ m)) k k₃ ?_]
    show ((k₃ : ↥(C (Fin.last r))) : G) = (μ (l ^ 2 ^ m))⁻¹ * k * μ (l ^ 2 ^ m)
    rw [← hμa l]
    change a⁻¹ * ((μ l)⁻¹ * (a⁻¹ * k * a) * μ l) * a = (a⁻¹ * μ l * a)⁻¹ * k * (a⁻¹ * μ l * a)
    simp only [mul_inv_rev, inv_inv, hainv, mul_assoc]
  have hmono' : ∀ j : Fin (r + 1), C j ≤ C (Fin.last r) := fun j =>
    (Fin.monotone_iff_le_succ.mpr hCle) (Fin.le_last j)
  let π : ↥(C (Fin.last r)) →* ↥(C (Fin.last r)) ⧸ (C 0).subgroupOf (C (Fin.last r)) :=
    QuotientGroup.mk' _
  have hπker : ∀ x : ↥(C (Fin.last r)), π x = 1 ↔ (x : G) ∈ C 0 := fun x => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  let C' : Fin (r + 1) → Subgroup (↥(C (Fin.last r)) ⧸ (C 0).subgroupOf (C (Fin.last r))) :=
    fun i => ((C i).subgroupOf (C (Fin.last r))).map π
  have hmemC' : ∀ (i : Fin (r + 1)) (q : ↥(C (Fin.last r)) ⧸ (C 0).subgroupOf (C (Fin.last r))),
      q ∈ C' i ↔ ∃ x : ↥(C (Fin.last r)), (x : G) ∈ C i ∧ π x = q := by
    intro i q
    simp only [C', Subgroup.mem_map, mem_subgroupOf]
  let rep : (↥(C (Fin.last r)) ⧸ (C 0).subgroupOf (C (Fin.last r))) → ↥(C (Fin.last r)) :=
    fun q => Classical.choose (QuotientGroup.mk_surjective q)
  have hrep : ∀ q, π (rep q) = q := fun q => Classical.choose_spec (QuotientGroup.mk_surjective q)
  let c' : Fin r → (↥(C (Fin.last r)) ⧸ (C 0).subgroupOf (C (Fin.last r))) → K :=
    fun i q => c i ((rep q : ↥(C (Fin.last r))) : G)
  have hc' : ∀ (i : Fin r) (x : ↥(C (Fin.last r))), (x : G) ∈ C i.succ → c' i (π x) = c i x := by
    intro i x hx
    have h2 : ((rep (π x))⁻¹ * x : ↥(C (Fin.last r))) ∈ (C 0).subgroupOf (C (Fin.last r)) :=
      QuotientGroup.eq.mp (hrep (π x))
    have h2' : ((rep (π x) : ↥(C (Fin.last r))) : G)⁻¹ * x ∈ C 0 := h2
    have hw : ((rep (π x) : ↥(C (Fin.last r))) : G)⁻¹ * x ∈ C i.castSucc := hmono _ h2'
    have hw' : ((rep (π x) : ↥(C (Fin.last r))) : G)⁻¹ * x ∈ C i.succ := hCle i hw
    have hx' : ((rep (π x) : ↥(C (Fin.last r))) : G) ∈ C i.succ := by
      have := (C i.succ).mul_mem hx ((C i.succ).inv_mem hw')
      simpa using this
    have h3 := (hc i).map_mul _ hx' _ hw'
    rw [show ((rep (π x) : ↥(C (Fin.last r))) : G) * (((rep (π x) : ↥(C (Fin.last r))) : G)⁻¹ * x) =
      x by group] at h3
    have h4 : c i (((rep (π x) : ↥(C (Fin.last r))) : G)⁻¹ * x) = 0 := ((hc i).ker _ hw').mpr hw
    show c i ((rep (π x) : ↥(C (Fin.last r))) : G) = c i x
    rw [h3, h4, add_zero]
  refine (ffAbstract_card_sq (E := ↥(C (Fin.last r)) ⧸ (C 0).subgroupOf (C (Fin.last r))) hK μE
    (sectionRightConj haW haW') (fun x => sectionRightConj_sectionRightConj haW haW' ha x) hνμ C'
    ?_ ?_ ?_ ?_ c' ?_ ?_ ?_ ?_).symm
  · show ((C 0).subgroupOf (C (Fin.last r))).map π = ⊥
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    exact (hπker x).mpr hx
  · show ((C (Fin.last r)).subgroupOf (C (Fin.last r))).map π = ⊤
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  · intro i
    exact Subgroup.map_mono (fun x hx => mem_subgroupOf.mpr (hCle i (mem_subgroupOf.mp hx)))
  · intro l i q hq
    obtain ⟨x, hxi, rfl⟩ := (hmemC' i q).mp hq
    let x' : ↥(C (Fin.last r)) :=
      ⟨(μ l)⁻¹ * x * μ l, inv_mul_mul_mem_of_mem_normalizer (hμW l) x.2⟩
    refine (hmemC' i _).mpr ⟨x', inv_mul_mul_mem_of_mem_normalizer (hμC l i) hxi, ?_⟩
    exact (sectionRightConj_mk (hμW l) (hμW' l) x x' rfl).symm
  · intro i q q' hq hq'
    obtain ⟨x, hx, rfl⟩ := (hmemC' _ q).mp hq
    obtain ⟨y, hy, rfl⟩ := (hmemC' _ q').mp hq'
    have hxy : ((x * y : ↥(C (Fin.last r))) : G) ∈ C i.succ := (C i.succ).mul_mem hx hy
    rw [← map_mul, hc' i x hx, hc' i y hy, hc' i (x * y) hxy]
    exact (hc i).map_mul _ hx _ hy
  · intro i q hq
    obtain ⟨x, hx, rfl⟩ := (hmemC' _ q).mp hq
    rw [hc' i x hx, (hc i).ker _ hx]
    constructor
    · intro hxc
      exact (hmemC' _ _).mpr ⟨x, hxc, rfl⟩
    · intro hq'
      obtain ⟨y, hy, hyx⟩ := (hmemC' _ _).mp hq'
      have h1 : (y⁻¹ * x : ↥(C (Fin.last r))) ∈ (C 0).subgroupOf (C (Fin.last r)) :=
        QuotientGroup.eq.mp hyx
      have h2 : ((y⁻¹ * x : ↥(C (Fin.last r))) : G) ∈ C 0 := h1
      have e : (x : G) = (y : G) * ((y : G)⁻¹ * x) := by group
      rw [e]
      exact (C i.castSucc).mul_mem hy (hmono _ h2)
  · intro i k
    obtain ⟨y, hy, hyk⟩ := (hc i).surj k
    have hyW : y ∈ C (Fin.last r) := hmono' i.succ hy
    refine ⟨π ⟨y, hyW⟩, (hmemC' _ _).mpr ⟨⟨y, hyW⟩, hy, rfl⟩, ?_⟩
    rw [hc' i ⟨y, hyW⟩ hy]
    exact hyk
  · intro i l q hq
    obtain ⟨x, hx, rfl⟩ := (hmemC' _ q).mp hq
    let x' : ↥(C (Fin.last r)) :=
      ⟨(μ l)⁻¹ * x * μ l, inv_mul_mul_mem_of_mem_normalizer (hμW l) x.2⟩
    have hx' : (x' : G) ∈ C i.succ := inv_mul_mul_mem_of_mem_normalizer (hμC l i.succ) hx
    have e : μE l (π x) = π x' := sectionRightConj_mk (hμW l) (hμW' l) x x' rfl
    rw [e, hc' i x' hx', hc' i x hx]
    exact (hc i).equiv l x hx

end Generic

theorem ffBridge_scalar_section_one {G : Type} [Group G] [Finite G] {K : Type} [Field K] {m : ℕ}
    (hK : Nat.card K = 2 ^ (2 * m)) (μ : Kˣ →* G) {a : G} (ha : a * a = 1)
    (hμa : ∀ l : Kˣ, a⁻¹ * μ l * a = μ (l ^ 2 ^ m))
    {W' W : Subgroup G} [(W'.subgroupOf W).Normal] [IsElementaryAbelian 2 (↥W ⧸ W'.subgroupOf W)]
    (haW : a ∈ normalizer (W : Set G)) (haW' : a ∈ normalizer (W' : Set G))
    (hle : W' ≤ W) (hμW : ∀ l : Kˣ, μ l ∈ normalizer (W : Set G))
    (hμW' : ∀ l : Kˣ, μ l ∈ normalizer (W' : Set G))
    {c : G → K} (hc : ScalarLayer μ W W' c) :
    Nat.card {q : ↥W ⧸ W'.subgroupOf W | sectionRightConj haW haW' q = q} ^ 2 =
      Nat.card (↥W ⧸ W'.subgroupOf W) := by
  refine ffBridge_scalar_section (r := 1) hK μ ha hμa haW haW' ![W', W] rfl rfl ?_ ?_ ?_
  · intro i
    fin_cases i
    exact hle
  · intro l i
    fin_cases i
    exacts [hμW' l, hμW l]
  · intro i
    fin_cases i
    exact ⟨c, hc⟩

theorem ffBridge_scalar_section_two {G : Type} [Group G] [Finite G] {K : Type} [Field K] {m : ℕ}
    (hK : Nat.card K = 2 ^ (2 * m)) (μ : Kˣ →* G) {a : G} (ha : a * a = 1)
    (hμa : ∀ l : Kˣ, a⁻¹ * μ l * a = μ (l ^ 2 ^ m))
    {W' W : Subgroup G} [(W'.subgroupOf W).Normal] [IsElementaryAbelian 2 (↥W ⧸ W'.subgroupOf W)]
    (haW : a ∈ normalizer (W : Set G)) (haW' : a ∈ normalizer (W' : Set G))
    (C₁ : Subgroup G) (h01 : W' ≤ C₁) (h12 : C₁ ≤ W)
    (hμW : ∀ l : Kˣ, μ l ∈ normalizer (W : Set G)) (hμC₁ : ∀ l : Kˣ, μ l ∈ normalizer (C₁ : Set G))
    (hμW' : ∀ l : Kˣ, μ l ∈ normalizer (W' : Set G))
    {c₀ c₁ : G → K} (hc₀ : ScalarLayer μ C₁ W' c₀) (hc₁ : ScalarLayer μ W C₁ c₁) :
    Nat.card {q : ↥W ⧸ W'.subgroupOf W | sectionRightConj haW haW' q = q} ^ 2 =
      Nat.card (↥W ⧸ W'.subgroupOf W) := by
  refine ffBridge_scalar_section (r := 2) hK μ ha hμa haW haW' ![W', C₁, W] rfl rfl ?_ ?_ ?_
  · intro i
    fin_cases i
    exacts [h01, h12]
  · intro l i
    fin_cases i
    exacts [hμW' l, hμC₁ l, hμW l]
  · intro i
    fin_cases i
    exacts [⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩]

section Calculus

variable {G : Type*} [Group G] {K : Type*} [Field K] {μ : Kˣ →* G}

theorem ffTorus_mem_normalizer_bot (g : G) : g ∈ normalizer ((⊥ : Subgroup G) : Set G) := by
  rw [Subgroup.normalizer_eq_top]
  exact Subgroup.mem_top g

theorem ffTorus_mem_map_conj_iff (W : Subgroup G) (g x : G) :
    x ∈ W.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ W := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem ScalarLayer.conj {W W' : Subgroup G} {c : G → K} (h : ScalarLayer μ W W' c) (g : G) :
    ScalarLayer ((MulAut.conj g).toMonoidHom.comp μ) (W.map (MulAut.conj g).toMonoidHom)
      (W'.map (MulAut.conj g).toMonoidHom) (fun x => c (g⁻¹ * x * g)) where
  map_mul x hx y hy := by
    rw [ffTorus_mem_map_conj_iff] at hx hy
    have := h.map_mul _ hx _ hy
    rwa [show g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g by group] at this
  ker x hx := by
    rw [ffTorus_mem_map_conj_iff] at hx
    rw [ffTorus_mem_map_conj_iff]
    exact h.ker _ hx
  surj k := by
    obtain ⟨y, hy, hyk⟩ := h.surj k
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    refine ⟨g * y * g⁻¹, (ffTorus_mem_map_conj_iff _ _ _).mpr (by rw [e]; exact hy), ?_⟩
    show c (g⁻¹ * (g * y * g⁻¹) * g) = k
    rw [e]
    exact hyk
  equiv l x hx := by
    rw [ffTorus_mem_map_conj_iff] at hx
    have := h.equiv l _ hx
    have e : g⁻¹ * ((g * μ l * g⁻¹)⁻¹ * x * (g * μ l * g⁻¹)) * g =
        (μ l)⁻¹ * (g⁻¹ * x * g) * μ l := by group
    show c (g⁻¹ * ((g * μ l * g⁻¹)⁻¹ * x * (g * μ l * g⁻¹)) * g) = (l : K) * c (g⁻¹ * x * g)
    rw [e]
    exact this

theorem ScalarLayer.of_sup {W W' Y : Subgroup G} {cY : G → K} (hW'W : W' ≤ W) (hYW : Y ≤ W)
    (hsup : ∀ x ∈ W, ∃ m ∈ W', ∃ y ∈ Y, x = m * y)
    (hnorm : ∀ y ∈ Y, ∀ m ∈ W', y * m * y⁻¹ ∈ W')
    (hμW' : ∀ l : Kˣ, μ l ∈ normalizer (W' : Set G))
    (hμY : ∀ l : Kˣ, μ l ∈ normalizer (Y : Set G))
    (hY : ScalarLayer μ Y (W' ⊓ Y) cY) : ∃ c : G → K, ScalarLayer μ W W' c := by
  classical
  choose! mm hmm yy hyy hxy using hsup
  have K1 : ∀ x ∈ W, ∀ m' ∈ W', ∀ y' ∈ Y, x = m' * y' → cY (yy x) = cY y' := by
    intro x hx m' hm' y' hy' hx'
    have h1 : yy x * y'⁻¹ = (mm x)⁻¹ * m' := by
      have e := (hxy x hx).symm.trans hx'
      calc yy x * y'⁻¹ = (mm x)⁻¹ * (mm x * yy x) * y'⁻¹ := by group
        _ = (mm x)⁻¹ * (m' * y') * y'⁻¹ := by rw [e]
        _ = (mm x)⁻¹ * m' := by group
    have h2a : (mm x)⁻¹ * m' ∈ W' := mul_mem (inv_mem (hmm x hx)) hm'
    have h2b : yy x * y'⁻¹ ∈ Y := Y.mul_mem (hyy x hx) (Y.inv_mem hy')
    have h2 : yy x * y'⁻¹ ∈ W' ⊓ Y := mem_inf.mpr ⟨by rw [h1]; exact h2a, h2b⟩
    have h3 : cY (yy x * y'⁻¹) = 0 := (hY.ker _ h2b).mpr h2
    have h4 := hY.map_mul _ h2b _ hy'
    rw [inv_mul_cancel_right, h3, zero_add] at h4
    exact h4
  refine ⟨fun x => cY (yy x), ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx'
    have hmul : x * x' = (mm x * (yy x * mm x' * (yy x)⁻¹)) * (yy x * yy x') := by
      calc x * x' = (mm x * yy x) * (mm x' * yy x') := by rw [← hxy x hx, ← hxy x' hx']
        _ = _ := by group
    have := K1 (x * x') (mul_mem hx hx') (mm x * (yy x * mm x' * (yy x)⁻¹))
      (mul_mem (hmm x hx) (hnorm _ (hyy x hx) _ (hmm x' hx'))) (yy x * yy x')
      (mul_mem (hyy x hx) (hyy x' hx')) hmul
    rw [this]
    exact hY.map_mul _ (hyy x hx) _ (hyy x' hx')
  · intro x hx
    show cY (yy x) = 0 ↔ x ∈ W'
    constructor
    · intro h
      have : yy x ∈ W' := ((hY.ker _ (hyy x hx)).mp h).1
      rw [hxy x hx]
      exact mul_mem (hmm x hx) this
    · intro h
      have h1 : yy x ∈ W' := by
        have e : yy x = (mm x)⁻¹ * x := by
          conv_lhs => rw [show yy x = (mm x)⁻¹ * (mm x * yy x) by group, ← hxy x hx]
        rw [e]
        exact mul_mem (inv_mem (hmm x hx)) h
      exact (hY.ker _ (hyy x hx)).mpr ⟨h1, hyy x hx⟩
  · intro k
    obtain ⟨y, hy, hyk⟩ := hY.surj k
    refine ⟨y, hYW hy, ?_⟩
    show cY (yy y) = k
    rw [K1 y (hYW hy) 1 W'.one_mem y hy (one_mul y).symm]
    exact hyk
  · intro l x hx
    show cY (yy ((μ l)⁻¹ * x * μ l)) = (l : K) * cY (yy x)
    have hm1 : (μ l)⁻¹ * mm x * μ l ∈ W' :=
      CFSG.LocalAnalysis.ComponentInitial.inv_mul_mul_mem_of_mem_normalizer (hμW' l) (hmm x hx)
    have hy1 : (μ l)⁻¹ * yy x * μ l ∈ Y :=
      CFSG.LocalAnalysis.ComponentInitial.inv_mul_mul_mem_of_mem_normalizer (hμY l) (hyy x hx)
    have hx1 : (μ l)⁻¹ * x * μ l = ((μ l)⁻¹ * mm x * μ l) * ((μ l)⁻¹ * yy x * μ l) := by
      conv_lhs => rw [hxy x hx]
      group
    have hx2 : (μ l)⁻¹ * x * μ l ∈ W := by
      rw [hx1]
      exact mul_mem (hW'W hm1) (hYW hy1)
    rw [K1 _ hx2 _ hm1 _ hy1 hx1]
    exact hY.equiv l _ (hyy x hx)

theorem ScalarLayer.comp {Y Y' W W' : Subgroup G} {c₀ : G → K} (h : ScalarLayer μ Y Y' c₀)
    (κ : G → G) (hκY : ∀ x ∈ W, κ x ∈ Y) (hκmul : ∀ x ∈ W, ∀ y ∈ W, κ (x * y) = κ x * κ y)
    (hκker : ∀ x ∈ W, κ x ∈ Y' ↔ x ∈ W') (hκsurj : ∀ y ∈ Y, ∃ x ∈ W, κ x = y)
    (hκμ : ∀ (l : Kˣ), ∀ x ∈ W, κ ((μ l)⁻¹ * x * μ l) = (μ l)⁻¹ * κ x * μ l) :
    ScalarLayer μ W W' (fun x => c₀ (κ x)) where
  map_mul x hx y hy := by
    show c₀ (κ (x * y)) = c₀ (κ x) + c₀ (κ y)
    rw [hκmul x hx y hy]
    exact h.map_mul _ (hκY x hx) _ (hκY y hy)
  ker x hx := by
    show c₀ (κ x) = 0 ↔ x ∈ W'
    rw [h.ker _ (hκY x hx)]
    exact hκker x hx
  surj k := by
    obtain ⟨y, hy, hyk⟩ := h.surj k
    obtain ⟨x, hx, hxy⟩ := hκsurj y hy
    exact ⟨x, hx, by show c₀ (κ x) = k; rw [hxy]; exact hyk⟩
  equiv l x hx := by
    show c₀ (κ ((μ l)⁻¹ * x * μ l)) = (l : K) * c₀ (κ x)
    rw [hκμ l x hx]
    exact h.equiv l _ (hκY x hx)

end Calculus

section Torus

open CFSG.LocalAnalysis.SymplecticFourStandard.FullCenterTorus
  (exists_diagHom)
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]

theorem ffTorus_exists_oneParam (φ : L ≃* antiSp K) (f g : Kˣ →* Kˣ) :
    ∃ μ : Kˣ →* G, (∀ l, μ l ∈ J₀ φ) ∧ ffIsOneParam φ μ f g ∧
      (∀ {v₀ : G} {m : ℕ}, v₀ * v₀ = 1 →
        (∀ x : L, ((φ.symm ((frobAut K ^ m) (φ x)) : L) : G) = v₀ * x * v₀⁻¹) →
          ∀ l : Kˣ, v₀⁻¹ * μ l * v₀ = μ (l ^ 2 ^ m)) := by
  obtain ⟨τ, hτ⟩ := exists_diagHom (K := K) f g
  refine ⟨(L.subtype.comp φ.symm.toMonoidHom).comp τ, fun l => ?_, fun l a b c d => ?_,
    fun {v₀ m} hv2 hvF l => ?_⟩
  · exact symm_mem_pull.mpr ⟨f l, g l, (f l).ne_zero, (g l).ne_zero, hτ l⟩
  · exact Setup.symm_conj (diagTorus_conj (f l).ne_zero (g l).ne_zero (hτ l) a b c d)
  · have hinv : v₀⁻¹ = v₀ := inv_eq_of_mul_eq_one_right hv2
    have e := hvF (φ.symm (τ l))
    rw [MulEquiv.apply_symm_apply] at e
    have hfr : (frobAut K ^ m) (τ l) = τ (l ^ 2 ^ m) := by
      apply mat_ext
      rw [FieldInvolution.mat_frobAut_pow]
      have h1 : mat (τ l) = diagMat (f l : K) (g l : K) := hτ l
      have h2 : mat (τ (l ^ 2 ^ m)) =
          diagMat ((f (l ^ 2 ^ m) : Kˣ) : K) ((g (l ^ 2 ^ m) : Kˣ) : K) := hτ _
      have hm0 : 2 ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
      rw [h1, h2, map_pow, map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagMat, Matrix.diagonal_apply, inv_pow, hm0]
    rw [hfr] at e
    show v₀⁻¹ * ((φ.symm (τ l) : L) : G) * v₀ = ((φ.symm (τ (l ^ 2 ^ m)) : L) : G)
    rw [e, hinv]

theorem ffTorus_comm_w (φ : L ≃* antiSp K) {v₀ : G} {m : ℕ}
    (hvF : ∀ x : L, ((φ.symm ((frobAut K ^ m) (φ x)) : L) : G) = v₀ * x * v₀⁻¹) (k : Axis) :
    v₀ * w φ k = w φ k * v₀ := by
  have h01 : ∀ i j, mat (FullCenterWeyl.weylElt K k) i j = 0 ∨
      mat (FullCenterWeyl.weylElt K k) i j = 1 := by
    intro i j
    cases k <;> fin_cases i <;> fin_cases j <;>
      simp [mat, FullCenterWeyl.glMat_weylElt, FullCenterWeyl.weylMat]
  have h := hvF (φ.symm (FullCenterWeyl.weylElt K k))
  rw [MulEquiv.apply_symm_apply, FieldInvolution.frobAut_pow_eq_self m h01] at h
  change v₀ * ((φ.symm (FullCenterWeyl.weylElt K k) : L) : G) =
    ((φ.symm (FullCenterWeyl.weylElt K k) : L) : G) * v₀
  calc v₀ * ((φ.symm (FullCenterWeyl.weylElt K k) : L) : G)
      = (v₀ * ((φ.symm (FullCenterWeyl.weylElt K k) : L) : G) * v₀⁻¹) * v₀ := by group
    _ = _ := by rw [← h]

theorem ffTorus_card_K {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}
    (hS : SCSetting L K n φ t i) (hn : Even n) : Nat.card K = 2 ^ (2 * (n / 2)) := by
  rw [hS.fc.setup.card_K]
  obtain ⟨r, hr⟩ := hn
  congr 1
  omega

theorem ffTorus_conj_w (φ : L ≃* antiSp K) (k : Axis) {μ : Kˣ →* G} (hμJ : ∀ l, μ l ∈ J₀ φ)
    {v₀ : G} {m : ℕ} (hv2 : v₀ * v₀ = 1)
    (hvF : ∀ x : L, ((φ.symm ((frobAut K ^ m) (φ x)) : L) : G) = v₀ * x * v₀⁻¹)
    (hfrob : ∀ l : Kˣ, v₀⁻¹ * μ l * v₀ = μ (l ^ 2 ^ m)) :
    (∀ l, ((MulAut.conj (w φ k)⁻¹).toMonoidHom.comp μ) l ∈ J₀ φ) ∧
      ∀ l : Kˣ, v₀⁻¹ * ((MulAut.conj (w φ k)⁻¹).toMonoidHom.comp μ) l * v₀ =
        ((MulAut.conj (w φ k)⁻¹).toMonoidHom.comp μ) (l ^ 2 ^ m) := by
  have hwinv : (w φ k)⁻¹ = w φ k := FullCenterWeyl.w_inv k
  have hcomm := ffTorus_comm_w φ hvF k
  have hinv : v₀⁻¹ = v₀ := inv_eq_of_mul_eq_one_right hv2
  refine ⟨fun l => ?_, fun l => ?_⟩
  · have := FullCenterWeyl.conj_w_mem_J (φ := φ) k (hμJ l)
    change (w φ k)⁻¹ * μ l * ((w φ k)⁻¹)⁻¹ ∈ J₀ φ
    simp only [hwinv]
    simpa [hwinv] using this
  · change v₀⁻¹ * ((w φ k)⁻¹ * μ l * ((w φ k)⁻¹)⁻¹) * v₀ =
      (w φ k)⁻¹ * μ (l ^ 2 ^ m) * ((w φ k)⁻¹)⁻¹
    simp only [hwinv]
    rw [← hfrob l, hinv]
    have hc : v₀ * w φ k = w φ k * v₀ := hcomm
    calc v₀ * (w φ k * μ l * w φ k) * v₀ = (v₀ * w φ k) * μ l * (w φ k * v₀) := by group
      _ = (w φ k * v₀) * μ l * (v₀ * w φ k) := by rw [hc]
      _ = w φ k * (v₀ * μ l * v₀) * w φ k := by group

theorem ffTorus_normalizer_of_conj {φ : L ≃* antiSp K} {X : Subgroup G} {j : G} (hj : j ∈ J₀ φ)
    (h : ∀ g ∈ J₀ φ, ∀ x ∈ X, g⁻¹ * x * g ∈ X) : j ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff'']
  intro x
  refine ⟨fun hx => h j hj x hx, fun hx => ?_⟩
  have h2 := h j⁻¹ (inv_mem hj) _ hx
  have e : (j⁻¹)⁻¹ * (j⁻¹ * x * j) * j⁻¹ = x := by group
  rwa [e] at h2

theorem ffTorus_le_normalizer_sup {A B C : Subgroup G} (hB : A ≤ normalizer (B : Set G))
    (hC : A ≤ normalizer (C : Set G)) : A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) :=
  fun a ha => Subgroup.inf_normalizer_le_normalizer_sup B C (mem_inf.mpr ⟨hB ha, hC ha⟩)

theorem ffTorus_mem_normalizer_of_commute {X : Subgroup G} {y : G}
    (h : ∀ x ∈ X, y * x = x * y) : y ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff'']
  intro x
  constructor
  · intro hx
    have e : y⁻¹ * x * y = x := by
      rw [mul_assoc, ← h x hx, inv_mul_cancel_left]
    rw [e]
    exact hx
  · intro hx
    have e := h _ hx
    have e2 : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
    rw [e2, e]
    simpa using hx

theorem ffTorus_normalizer_map_conj {X : Subgroup G} {h : G} (hN : h ∈ normalizer (X : Set G))
    (g : G) :
    g * h * g⁻¹ ∈ normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff'']
  intro x
  rw [ffTorus_mem_map_conj_iff, ffTorus_mem_map_conj_iff]
  have e : g⁻¹ * ((g * h * g⁻¹)⁻¹ * x * (g * h * g⁻¹)) * g = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [e]
  exact mem_normalizer_iff''.mp hN _

theorem ffTorus_exists_sqrt {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∃ σ₀ : Kˣ →* Kˣ, ∀ l : Kˣ, σ₀ l ^ 2 = l := by
  have := Fintype.ofFinite K
  have hunit : ∀ l : Kˣ, l ^ Nat.card K = l := fun l => Units.ext (by
    rw [Units.val_pow_eq_pow_val, Nat.card_eq_fintype_card, FiniteField.pow_card])
  refine ⟨powMonoidHom (2 ^ (n - 1)), fun l => ?_⟩
  change (l ^ 2 ^ (n - 1)) ^ 2 = l
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, ← hK, hunit]

theorem ffTorus_exists_adapted_u (φ : L ≃* antiSp K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (k : Axis) :
    ∃ (μ : Kˣ →* G) (f g : Kˣ →* Kˣ), (∀ l, μ l ∈ J₀ φ) ∧ ffIsOneParam φ μ f g ∧
      (∀ l : Kˣ, ffUChar k (f l : K) (g l : K) = l) ∧
      (∀ {v₀ : G} {m : ℕ}, v₀ * v₀ = 1 →
        (∀ x : L, ((φ.symm ((frobAut K ^ m) (φ x)) : L) : G) = v₀ * x * v₀⁻¹) →
          ∀ l : Kˣ, v₀⁻¹ * μ l * v₀ = μ (l ^ 2 ^ m)) := by
  obtain ⟨σ₀, hσ₀⟩ := ffTorus_exists_sqrt (K := K) hn hK
  cases k
  · obtain ⟨μ, h1, h2, h3⟩ := ffTorus_exists_oneParam (G := G) φ (MonoidHom.id Kˣ) 1
    exact ⟨μ, _, _, h1, h2, fun l => by simp [ffUChar], h3⟩
  · obtain ⟨μ, h1, h2, h3⟩ := ffTorus_exists_oneParam (G := G) φ σ₀ 1
    refine ⟨μ, _, _, h1, h2, fun l => ?_, h3⟩
    have := congrArg Units.val (hσ₀ l)
    simpa [ffUChar, Units.val_pow_eq_pow_val] using this

theorem ffTorus_exists_adapted_a (φ : L ≃* antiSp K) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (k : Axis) :
    ∃ (μ : Kˣ →* G) (f g : Kˣ →* Kˣ), (∀ l, μ l ∈ J₀ φ) ∧ ffIsOneParam φ μ f g ∧
      (∀ l : Kˣ, ffAChar k (f l : K) (g l : K) = l) ∧
      (∀ {v₀ : G} {m : ℕ}, v₀ * v₀ = 1 →
        (∀ x : L, ((φ.symm ((frobAut K ^ m) (φ x)) : L) : G) = v₀ * x * v₀⁻¹) →
          ∀ l : Kˣ, v₀⁻¹ * μ l * v₀ = μ (l ^ 2 ^ m)) := by
  obtain ⟨σ₀, hσ₀⟩ := ffTorus_exists_sqrt (K := K) hn hK
  cases k
  · obtain ⟨μ, h1, h2, h3⟩ := ffTorus_exists_oneParam (G := G) φ 1 σ₀
    refine ⟨μ, _, _, h1, h2, fun l => ?_, h3⟩
    have := congrArg Units.val (hσ₀ l)
    simpa [ffAChar, Units.val_pow_eq_pow_val] using this
  · obtain ⟨μ, h1, h2, h3⟩ := ffTorus_exists_oneParam (G := G) φ (MonoidHom.id Kˣ) 1
    exact ⟨μ, _, _, h1, h2, fun l => by simp [ffAChar], h3⟩

end Torus

section BaseLayer

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis RootAxisTwoCore

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]

theorem ffLayer_U (φ : L ≃* antiSp K) (k : Axis) {μ : Kˣ →* G} {f g : Kˣ →* Kˣ}
    (hμ : ffIsOneParam φ μ f g) (hχ : ∀ l : Kˣ, ffUChar k (f l : K) (g l : K) = l) :
    ∃ c : G → K, ScalarLayer μ (U φ k) ⊥ c := by
  classical
  let c : G → K := Function.invFun (coordG φ k)
  have hc : ∀ b : K, c (coordG φ k b) = b := Function.leftInverse_invFun (coordG_injective φ k)
  have hconj : ∀ (l : Kˣ) (b : K), (μ l)⁻¹ * coordG φ k b * μ l =
      coordG φ k (ffUChar k (f l : K) (g l : K) * b) := by
    intro l b
    cases k
    · have := hμ l 0 b 0 0
      simpa [coordG, rootCoord, ffUChar] using this
    · have := hμ l 0 0 b 0
      simpa [coordG, rootCoord, ffUChar] using this
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := exists_coordG_eq φ k hx
    obtain ⟨b, rfl⟩ := exists_coordG_eq φ k hy
    rw [← coordG_add, hc, hc, hc]
  · intro x hx
    obtain ⟨a, rfl⟩ := exists_coordG_eq φ k hx
    rw [hc, mem_bot]
    constructor
    · rintro rfl
      exact coordG_zero φ k
    · intro h
      exact coordG_injective φ k (h.trans (coordG_zero φ k).symm)
  · intro b
    exact ⟨coordG φ k b, coordG_mem φ k b, hc b⟩
  · intro l x hx
    obtain ⟨a, rfl⟩ := exists_coordG_eq φ k hx
    rw [hconj, hc, hc, hχ l]

theorem ffLayer_U_normalizer (φ : L ≃* antiSp K) (k : Axis) {μ : Kˣ →* G} {f g : Kˣ →* Kˣ}
    (hμ : ffIsOneParam φ μ f g) (l : Kˣ) : μ l ∈ normalizer (U φ k : Set G) := by
  have hconj : ∀ (l : Kˣ) (b : K), ∃ b' : K, (μ l)⁻¹ * coordG φ k b * μ l = coordG φ k b' := by
    intro l b
    cases k
    · have := hμ l 0 b 0 0
      exact ⟨_, by simpa [coordG, rootCoord] using this⟩
    · have := hμ l 0 0 b 0
      exact ⟨_, by simpa [coordG, rootCoord] using this⟩
  rw [mem_normalizer_iff'']
  intro x
  constructor
  · intro hx
    obtain ⟨b, rfl⟩ := exists_coordG_eq φ k hx
    obtain ⟨b', hb'⟩ := hconj l b
    rw [hb']
    exact coordG_mem φ k b'
  · intro hx
    obtain ⟨b, hb⟩ := exists_coordG_eq φ k hx
    obtain ⟨b', hb'⟩ := hconj l⁻¹ b
    have e : x = μ l * coordG φ k b * (μ l)⁻¹ := by
      rw [hb]; group
    have h2 : μ l * coordG φ k b * (μ l)⁻¹ = (μ l⁻¹)⁻¹ * coordG φ k b * μ l⁻¹ := by
      rw [map_inv]; group
    rw [e, h2, hb']
    exact coordG_mem φ k b'

theorem ffLayer_W (φ : L ≃* antiSp K) {n : ℕ} {t : G} (h : FullCenter.FCHyp L K n φ t) (k : Axis)
    {μ : Kˣ →* G} [Finite G] (hμJ : ∀ l, μ l ∈ J₀ φ) {c₁ : G → K} (h₁ : ScalarLayer μ (U φ k) ⊥ c₁) :
    ScalarLayer μ (Wk φ t k) (U φ k) (fun x => c₁ (t⁻¹ * (x⁻¹ * t * x))) := by
  refine ScalarLayer.comp h₁ (fun x => t⁻¹ * (x⁻¹ * t * x)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact FullCenterTorus.kappa_mem_U h k (mem_inf.mp (FullCenterTorus.W_le_Fi h k hx)).2
  · intro x hx y hy
    exact FullCenterTorus.kappa_mul h
      ((FullCenterTorus.W_le_F k).trans (FullCenterTorus.F_le_H h) hx)
      ((FullCenterTorus.W_le_F k).trans (FullCenterTorus.F_le_H h) hy)
  · intro x hx
    have hWC : Wk φ t k ⊓ centralizer ({t} : Set G) = U φ k := FullCenterTorus.W_inf_C h k
    rw [mem_bot, FullCenterTorus.kappa_eq_one_iff, ← hWC]
    exact ⟨fun hxC => mem_inf.mpr ⟨hx, hxC⟩, fun hxU => (mem_inf.mp hxU).2⟩
  · intro y hy
    exact FullCenterTorus.exists_kappa_eq_W h k hy
  · intro l x hx
    exact FullCenterTorus.kappa_conj_torus h (hμJ l) x

theorem ffLayer_V (φ : L ≃* antiSp K) {n : ℕ} {t : G} (h : FullCenter.FCHyp L K n φ t) (i : Axis)
    (hne : ⁅A φ i, F φ t ⊓ D φ t i.swap⁆ ≠ ⊥) (hbot : ⁅A φ i.swap, F φ t ⊓ D φ t i⁆ = ⊥)
    {μ : Kˣ →* G} [Finite G] (hμJ : ∀ l, μ l ∈ J₀ φ) {c₁ : G → K} (h₁ : ScalarLayer μ (U φ i) ⊥ c₁) :
    ScalarLayer μ (Vtor φ t i i) (Wk φ t i)
      (fun x => c₁ ((t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)))) := by
  have hP : ∀ x ∈ Vtor φ t i i, x ∈ P₁ φ t i := fun x hx =>
    (mem_inf.mp (NextCores.M_le_P₀ h i hx.1)).1
  refine ScalarLayer.comp h₁ (fun x => (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x))) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact NextCores.sq_kappa_mem_U h i hne hbot (hP x hx)
  · intro x hx y hy
    exact NextCores.sq_kappa_mul h i hne hbot (hP x hx) (hP y hy)
  · intro x hx
    have hVF : Vtor φ t i i ⊓ F φ t = Wk φ t i := RootStandard.V_inf_F h i hne hbot i
    rw [mem_bot, NextCores.sq_kappa_eq_one_iff h i hne hbot (hP x hx), ← hVF]
    have hME : Mc φ t i ⊓ E φ t i = F φ t := NextCores.M_inf_E h i hne hbot
    constructor
    · intro hxE
      refine mem_inf.mpr ⟨hx, ?_⟩
      rw [← hME]
      exact mem_inf.mpr ⟨(mem_inf.mp hx).1, hxE⟩
    · intro hxF
      exact (FullCenterTorus.F_le_E0 h).trans (FullCenterWeyl.E0_le_E i) (mem_inf.mp hxF).2
  · intro y hy
    exact RootStandard.exists_V_sq_kappa_eq h i hne hbot hy
  · intro l x hx
    have := NextCores.sq_kappa_conj_torus h (inv_mem (hμJ l)) x
    rwa [inv_inv] at this

noncomputable def ffRho (φ : L ≃* antiSp K) (q : K × K × K × K) : G :=
  ((φ.symm (uElt q.1 q.2.1 q.2.2.1 q.2.2.2) : L) : G)

theorem ffRho_injective (φ : L ≃* antiSp K) : Function.Injective (ffRho (G := G) φ) :=
  fun q q' h => by
    have := uElt_inj (φ.symm.injective (Subtype.ext h))
    exact Prod.ext this.1 (Prod.ext this.2.1 (Prod.ext this.2.2.1 this.2.2.2))

theorem ffRho_mul (φ : L ≃* antiSp K) (q q' : K × K × K × K) :
    ffRho (G := G) φ q * ffRho φ q' =
      ffRho φ (q.1 + q'.1, q.2.1 + q'.2.1 + q.1 * q'.2.2.2,
        q.2.2.1 + q'.2.2.1 + q.1 * q'.2.1 + q.1 * q'.1 * q'.2.2.2 + q.2.1 * q'.1,
        q.2.2.2 + q'.2.2.2) := by
  change ((φ.symm (uElt q.1 q.2.1 q.2.2.1 q.2.2.2) : L) : G) *
      ((φ.symm (uElt q'.1 q'.2.1 q'.2.2.1 q'.2.2.2) : L) : G) = _
  rw [← Subgroup.coe_mul, ← map_mul, uElt_mul]
  rfl

theorem ffRho_mem_Z₀_iff (φ : L ≃* antiSp K) (x : G) :
    x ∈ Z₀ φ ↔ ∃ b c : K, x = ffRho φ (0, b, c, 0) := by
  constructor
  · intro hx
    obtain ⟨y, ⟨b, c, rfl⟩, rfl⟩ := exists_eq_symm_of_mem_pull hx
    exact ⟨b, c, rfl⟩
  · rintro ⟨b, c, rfl⟩
    exact symm_mem_pull.mpr ⟨b, c, rfl⟩

theorem ffLayer_A_two (φ : L ≃* antiSp K) {μ : Kˣ →* G} {f g : Kˣ →* Kˣ}
    (hμ : ffIsOneParam φ μ f g) (hχ : ∀ l : Kˣ, (f l : K) * (g l : K)⁻¹ = l) :
    ∃ c : G → K, ScalarLayer μ (A φ Axis.two) (Z₀ φ) c := by
  classical
  let c : G → K := fun x => if h : ∃ q, ffRho φ q = x then h.choose.1 else 0
  have hc : ∀ q, c (ffRho φ q) = q.1 := by
    intro q
    have h : ∃ q', ffRho φ q' = ffRho φ q := ⟨q, rfl⟩
    simp only [c, dif_pos h]
    rw [ffRho_injective φ h.choose_spec]
  have hA : ∀ x ∈ A φ Axis.two, ∃ a b c' : K, x = ffRho φ (a, b, c', 0) := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := exists_eq_symm_of_mem_pull hx
    obtain ⟨a, b, c', rfl⟩ := hy
    exact ⟨a, b, c', rfl⟩
  have hAmem : ∀ a b c' : K, ffRho φ (a, b, c', 0) ∈ A φ Axis.two := fun a b c' =>
    symm_mem_pull.mpr ⟨a, b, c', rfl⟩
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, b, c', rfl⟩ := hA x hx
    obtain ⟨a', b', c'', rfl⟩ := hA y hy
    rw [ffRho_mul, hc, hc, hc]
  · intro x hx
    obtain ⟨a, b, c', rfl⟩ := hA x hx
    rw [hc, ffRho_mem_Z₀_iff]
    constructor
    · intro h0
      exact ⟨b, c', by rw [show a = 0 from h0]⟩
    · rintro ⟨b', c'', h⟩
      exact congrArg Prod.fst (ffRho_injective φ h)
  · intro κ
    exact ⟨ffRho φ (κ, 0, 0, 0), hAmem κ 0 0, hc _⟩
  · intro l x hx
    obtain ⟨a, b, c', rfl⟩ := hA x hx
    have hconj : (μ l)⁻¹ * ffRho φ (a, b, c', 0) * μ l = ffRho φ ((f l : K) * (g l : K)⁻¹ * a,
        (f l : K) * (g l : K) * b, (f l : K) ^ 2 * c', (g l : K) ^ 2 * 0) := hμ l a b c' 0
    rw [hconj, hc, hc]
    simp only [hχ l]

theorem ffLayer_A_one (φ : L ≃* antiSp K) {μ : Kˣ →* G} {f g : Kˣ →* Kˣ}
    (hμ : ffIsOneParam φ μ f g) (hχ : ∀ l : Kˣ, (g l : K) ^ 2 = l) :
    ∃ c : G → K, ScalarLayer μ (A φ Axis.one) (Z₀ φ) c := by
  classical
  let c : G → K := fun x => if h : ∃ q, ffRho φ q = x then h.choose.2.2.2 else 0
  have hc : ∀ q, c (ffRho φ q) = q.2.2.2 := by
    intro q
    have h : ∃ q', ffRho φ q' = ffRho φ q := ⟨q, rfl⟩
    simp only [c, dif_pos h]
    rw [ffRho_injective φ h.choose_spec]
  have hA : ∀ x ∈ A φ Axis.one, ∃ b c' d : K, x = ffRho φ (0, b, c', d) := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := exists_eq_symm_of_mem_pull hx
    obtain ⟨b, c', d, rfl⟩ := hy
    exact ⟨b, c', d, rfl⟩
  have hAmem : ∀ b c' d : K, ffRho φ (0, b, c', d) ∈ A φ Axis.one := fun b c' d =>
    symm_mem_pull.mpr ⟨b, c', d, rfl⟩
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨b, c', d, rfl⟩ := hA x hx
    obtain ⟨b', c'', d', rfl⟩ := hA y hy
    rw [ffRho_mul, hc, hc, hc]
  · intro x hx
    obtain ⟨b, c', d, rfl⟩ := hA x hx
    rw [hc, ffRho_mem_Z₀_iff]
    constructor
    · intro h0
      exact ⟨b, c', by rw [show d = 0 from h0]⟩
    · rintro ⟨b', c'', h⟩
      exact congrArg (fun p : K × K × K × K => p.2.2.2) (ffRho_injective φ h)
  · intro κ
    exact ⟨ffRho φ (0, 0, 0, κ), hAmem 0 0 κ, hc _⟩
  · intro l x hx
    obtain ⟨b, c', d, rfl⟩ := hA x hx
    have hconj : (μ l)⁻¹ * ffRho φ (0, b, c', d) * μ l = ffRho φ ((f l : K) * (g l : K)⁻¹ * 0,
        (f l : K) * (g l : K) * b, (f l : K) ^ 2 * c', (g l : K) ^ 2 * d) := hμ l 0 b c' d
    rw [hconj, hc, hc]
    simp only [hχ l]

theorem ffLayer_A (φ : L ≃* antiSp K) (k : Axis) {μ : Kˣ →* G} {f g : Kˣ →* Kˣ}
    (hμ : ffIsOneParam φ μ f g) (hχ : ∀ l : Kˣ, ffAChar k (f l : K) (g l : K) = l) :
    ∃ c : G → K, ScalarLayer μ (A φ k) (Z₀ φ) c := by
  cases k
  · exact ffLayer_A_one φ hμ hχ
  · exact ffLayer_A_two φ hμ hχ

end BaseLayer

end Bridge

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
