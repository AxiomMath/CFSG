module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135Cnt
public import CFSG.Milestones.ASVolI.C135.Coords

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (QC cnj coe_cnj slNat slNat_surjective dualHom dualHom_dualHom
  coe_dualHom moduleAct_true_eq le_normalizer_centerOf le_normalizer_bot semi_eq_one lin_dual
  lin_of_dual tri_offender fixAll)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section CoordCommute

variable {Q L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F)}

theorem burnsideC135_commute_iff_coords
    (hD : burnsideC135_DSG Q L (burnsideC135_Wc β 1) (burnsideC135_Wc β 0)
      (slNat α) βU (burnsideC135_βc β 1) (burnsideC135_βc β 0))
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf (Q))
    {w : G} (hw : w ∈ burnsideC135_Wc β 1) (hwU : w ∉ centerOf (Q)) (k : ↥(Q)) :
    w * k = k * w ↔ ∃ c : F, Multiplicative.toAdd (β k) 1 =
      c • Multiplicative.toAdd (β ⟨w, burnsideC135_Wc_le 1 hw⟩) 0 := by
  classical
  obtain ⟨hsq₁, hsq₂⟩ := burnsideC135_W_sq hD
  have hQN : Q ≤ Subgroup.normalizer (burnsideC135_Wc β 0 : Set G) :=
    burnsideC135_le_normalizer_W₁ (burnsideC135_dualSplit_symm hD) hcomm
  have hk : (k : G) ∈ ((burnsideC135_Wc β 1 ⊔ burnsideC135_Wc β 0 : Subgroup G) : Set G) := by
    rw [hD.join]
    exact k.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (fun a ha => hQN (burnsideC135_Wc_le 1 ha))] at hk
  obtain ⟨w₁, hw₁, w₂, hw₂, hkw⟩ := hk
  have hcr := burnsideC135_commute_iff hD hcomm ⟨w, hw⟩ hwU ⟨w₂, hw₂⟩
  have hww₁ : w * w₁ = w₁ * w := burnsideC135_comm_of_sq hsq₁ hw hw₁
  have hβk : Multiplicative.toAdd (β k) 1 =
      Multiplicative.toAdd (β ⟨w₂, burnsideC135_Wc_le 0 hw₂⟩) 1 := by
    have e : k = ⟨w₁, burnsideC135_Wc_le 1 hw₁⟩ * ⟨w₂, burnsideC135_Wc_le 0 hw₂⟩ :=
      Subtype.ext hkw.symm
    rw [e, map_mul, toAdd_mul, Pi.add_apply]
    obtain ⟨hh, h1⟩ := burnsideC135_mem_Wc.mp hw₁
    have h1' : Multiplicative.toAdd (β ⟨w₁, burnsideC135_Wc_le 1 hw₁⟩) 1 = 0 := h1
    rw [h1', zero_add]
  rw [hβk]
  have e1 : (Multiplicative.toAdd (burnsideC135_βc β 0 ⟨w₂, hw₂⟩) =
      Multiplicative.toAdd (β ⟨w₂, burnsideC135_Wc_le 0 hw₂⟩) 1) := by
    rw [burnsideC135_βc_apply]; rfl
  have e2 : (Multiplicative.toAdd (burnsideC135_βc β 1 ⟨w, hw⟩) =
      Multiplicative.toAdd (β ⟨w, burnsideC135_Wc_le 1 hw⟩) 0) := by
    rw [burnsideC135_βc_apply]; rfl
  rw [← e1, ← e2, ← hcr]
  rw [← hkw]
  constructor
  · intro h
    calc w * w₂ = w₁⁻¹ * ((w * w₁) * w₂) := by rw [hww₁]; group
      _ = w₁⁻¹ * (w * (w₁ * w₂)) := by group
      _ = w₁⁻¹ * ((w₁ * w₂) * w) := by rw [h]
      _ = w₂ * w := by group
  · intro h
    calc w * (w₁ * w₂) = w₁ * (w * w₂) := by rw [← mul_assoc, hww₁, mul_assoc]
      _ = w₁ * (w₂ * w) := by rw [h]
      _ = w₁ * w₂ * w := by group

end CoordCommute

theorem burnsideC135_card_le_of_hom {F : Type} [Field F] [Fintype F] {K K' : Subgroup G}
    (hK'K : K' ≤ K) (f : ↥K → Fin 3 → F) (hf : ∀ x y, f (x * y) = f x + f y)
    (hker : ∀ x, f x = 0 ↔ (x : G) ∈ K') (S : Set (Fin 3 → F)) (hS : ∀ x, f x ∈ S) :
    Nat.card K ≤ Nat.card K' * Nat.card S := by
  classical
  let φ : ↥K →* Multiplicative (Fin 3 → F) :=
    { toFun := fun x => Multiplicative.ofAdd (f x)
      map_one' := by
        have h := hf 1 1
        rw [mul_one] at h
        have h0 : f 1 = 0 := by
          have := congrArg (fun v => v - f 1) h
          simpa using this.symm
        rw [h0]; rfl
      map_mul' := fun x y => by rw [hf]; rfl }
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hk : Nat.card φ.ker = Nat.card K' := by
    have e : φ.ker = K'.subgroupOf K := by
      refine Subgroup.ext fun x => ?_
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker]
      show Multiplicative.ofAdd (f x) = 1 ↔ _
      constructor
      · intro h; exact Multiplicative.ofAdd.injective h
      · intro h; rw [h]; rfl
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'K).toEquiv]
  have hr : Nat.card φ.range ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective (fun z : ↥φ.range =>
      (⟨Multiplicative.toAdd (z : Multiplicative (Fin 3 → F)), ?_⟩ : ↥S)) fun a b hab => ?_
    · obtain ⟨x, hx⟩ := z.2
      rw [← hx]
      exact hS x
    · have := congrArg Subtype.val hab
      exact Subtype.ext (Multiplicative.toAdd.injective this)
  rw [← h1, hk]
  exact Nat.mul_le_mul_left _ hr

theorem burnsideC135_card_line {F : Type} [Field F] [Fintype F] (x : Fin 3 → F) :
    Nat.card {v : Fin 3 → F | ∃ c : F, v = c • x} ≤ Fintype.card F := by
  classical
  have h : {v : Fin 3 → F | ∃ c : F, v = c • x} = Set.range (fun c : F => c • x) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_range, eq_comm]
  rw [h, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective

section Abelian

variable {Q L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F)}

theorem burnsideC135_card_abelian_le
    (hD : burnsideC135_DSG Q L (burnsideC135_Wc β 1) (burnsideC135_Wc β 0)
      (slNat α) βU (burnsideC135_βc β 1) (burnsideC135_βc β 0))
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf (Q))
    (hβk : β.ker = (centerOf (Q)).subgroupOf (Q))
    {K : Subgroup G} (hKQ : K ≤ Q) (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) :
    Nat.card K ≤ Fintype.card F ^ 6 := by
  classical
  set U := centerOf (Q) with hU
  have hUcard := burnsideC135_card_U hD
  set KU := K ⊔ U with hKU
  have hUc : ∀ u ∈ U, ∀ x ∈ Q, u * x = x * u := fun u hu x hx =>
    burnsideC135_U_comm hu hx
  have hKUc : (KU : Set G) = (K : Set G) * (U : Set G) := by
    rw [hKU, Subgroup.coe_mul_of_left_le_normalizer_right K U
      (fun k hk => burnsideC135_le_normalizer_centerOf (fun x hx => Subgroup.le_normalizer hx)
        (hKQ hk))]
  have hKUQ : KU ≤ Q := sup_le hKQ (inf_le_left)
  have hKUab : ∀ x ∈ KU, ∀ y ∈ KU, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ (K : Set G) * (U : Set G) := hKUc ▸ hx
    have hy' : y ∈ (K : Set G) * (U : Set G) := hKUc ▸ hy
    obtain ⟨a, ha, u, hu, rfl⟩ := hx'
    obtain ⟨b, hb, v, hv, rfl⟩ := hy'
    have h1 := hK a ha b hb
    have h2 := hUc u hu b (hKQ hb)
    have h3 := hUc v hv a (hKQ ha)
    have h4 := hUc u hu v hv.1
    calc a * u * (b * v) = a * (u * b) * v := by group
      _ = a * (b * u) * v := by rw [h2]
      _ = (a * b) * (u * v) := by group
      _ = (b * a) * (v * u) := by rw [h1, h4]
      _ = b * (a * v) * u := by group
      _ = b * (v * a) * u := by rw [h3]
      _ = b * v * (a * u) := by group
  have hKKU : K ≤ KU := le_sup_left
  refine (Subgroup.card_le_of_le hKKU).trans ?_
  let f : Fin 2 → ↥KU → Fin 3 → F := fun i x => Multiplicative.toAdd (β ⟨x, hKUQ x.2⟩) i
  have hf : ∀ i x y, f i (x * y) = f i x + f i y := by
    intro i x y
    show Multiplicative.toAdd (β (⟨x, hKUQ x.2⟩ * ⟨y, hKUQ y.2⟩)) i = _
    rw [map_mul, toAdd_mul, Pi.add_apply]
  have hUKU : U ≤ KU := le_sup_right
  by_cases h₁ : ∃ k₁ ∈ KU ⊓ burnsideC135_Wc β 1, k₁ ∉ U
  · by_cases h₂ : ∃ k₂ ∈ KU ⊓ burnsideC135_Wc β 0, k₂ ∉ U
    ·
      obtain ⟨k₁, ⟨hk₁K, hk₁W⟩, hk₁U⟩ := h₁
      obtain ⟨k₂, ⟨hk₂K, hk₂W⟩, hk₂U⟩ := h₂
      set x₁ := Multiplicative.toAdd (β ⟨k₁, burnsideC135_Wc_le 1 hk₁W⟩) 0
      set x₂ := Multiplicative.toAdd (β ⟨k₂, burnsideC135_Wc_le 0 hk₂W⟩) 1
      have hmem : ∀ x : ↥KU, (∃ c : F, f 1 x = c • x₁) ∧ (∃ c : F, f 0 x = c • x₂) := by
        intro x
        refine ⟨(burnsideC135_commute_iff_coords hD hcomm hk₁W hk₁U ⟨x, hKUQ x.2⟩).mp
          (hKUab _ hk₁K _ x.2), ?_⟩
        have hD' := burnsideC135_dualSplit_symm hD
        obtain ⟨hsq₁, hsq₂⟩ := burnsideC135_W_sq hD
        have hQN : Q ≤ Subgroup.normalizer (burnsideC135_Wc β 0 : Set G) :=
          burnsideC135_le_normalizer_W₁ hD' hcomm
        have hx : (x : G) ∈ ((burnsideC135_Wc β 1 ⊔ burnsideC135_Wc β 0 : Subgroup G) :
            Set G) := by rw [hD.join]; exact hKUQ x.2
        rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
          (fun a ha => hQN (burnsideC135_Wc_le 1 ha))] at hx
        obtain ⟨w₁, hw₁, w₂, hw₂, hxw⟩ := hx
        have hcr := burnsideC135_commute_iff hD' hcomm ⟨k₂, hk₂W⟩ hk₂U ⟨w₁, hw₁⟩
        have hk₂w₂ : k₂ * w₂ = w₂ * k₂ := burnsideC135_comm_of_sq hsq₂ hk₂W hw₂
        have hc : k₂ * w₁ = w₁ * k₂ := by
          have h5 := hKUab _ hk₂K _ x.2
          rw [← hxw] at h5
          calc k₂ * w₁ = (k₂ * (w₁ * w₂)) * w₂⁻¹ := by group
            _ = (w₁ * w₂ * k₂) * w₂⁻¹ := by rw [h5]
            _ = w₁ * (w₂ * k₂) * w₂⁻¹ := by group
            _ = w₁ * (k₂ * w₂) * w₂⁻¹ := by rw [hk₂w₂]
            _ = w₁ * k₂ := by group
        obtain ⟨c, hc'⟩ := hcr.mp hc
        refine ⟨c, ?_⟩
        have e : (⟨(x : G), hKUQ x.2⟩ : ↥(Q)) =
            ⟨w₁, burnsideC135_Wc_le 1 hw₁⟩ * ⟨w₂, burnsideC135_Wc_le 0 hw₂⟩ :=
          Subtype.ext hxw.symm
        show Multiplicative.toAdd (β ⟨(x : G), hKUQ x.2⟩) 0 = _
        rw [e, map_mul, toAdd_mul, Pi.add_apply]
        obtain ⟨hh, h0⟩ := burnsideC135_mem_Wc.mp hw₂
        have h0' : Multiplicative.toAdd (β ⟨w₂, burnsideC135_Wc_le 0 hw₂⟩) 0 = 0 := h0
        rw [h0', add_zero]
        rw [burnsideC135_βc_apply, burnsideC135_βc_apply] at hc'
        exact hc'
      have hstep₁ : Nat.card ↥KU ≤ Nat.card ↥(KU ⊓ burnsideC135_Wc β 1) * Fintype.card F := by
        refine (burnsideC135_card_le_of_hom inf_le_left (f 1) (hf 1) (fun x => ?_)
          {v | ∃ c : F, v = c • x₁} fun x => (hmem x).1).trans
          (Nat.mul_le_mul_left _ (burnsideC135_card_line x₁))
        constructor
        · intro h
          exact ⟨x.2, burnsideC135_mem_Wc.mpr ⟨hKUQ x.2, h⟩⟩
        · rintro ⟨-, h⟩
          obtain ⟨hh, h'⟩ := burnsideC135_mem_Wc.mp h
          exact h'
      have hstep₂ : Nat.card ↥(KU ⊓ burnsideC135_Wc β 1) ≤ Nat.card U * Fintype.card F := by
        have hle : U ≤ KU ⊓ burnsideC135_Wc β 1 := le_inf hUKU hD.le₁
        refine (burnsideC135_card_le_of_hom hle (fun x => f 0 ⟨x, x.2.1⟩)
          (fun x y => hf 0 ⟨x, x.2.1⟩ ⟨y, y.2.1⟩) (fun x => ?_) {v | ∃ c : F, v = c • x₂}
          fun x => (hmem ⟨x, x.2.1⟩).2).trans
          (Nat.mul_le_mul_left _ (burnsideC135_card_line x₂))
        constructor
        · intro h
          obtain ⟨hh, h1⟩ := burnsideC135_mem_Wc.mp x.2.2
          have h1' : Multiplicative.toAdd (β ⟨(x : G), hKUQ x.2.1⟩) 1 = 0 := h1
          have h2 : (⟨(x : G), hKUQ x.2.1⟩ : ↥(Q)) ∈ β.ker := by
            rw [MonoidHom.mem_ker]
            apply Multiplicative.toAdd.injective
            funext i
            rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
            · exact h
            · exact h1'
          rw [hβk, Subgroup.mem_subgroupOf] at h2
          exact h2
        · intro h
          have h2 : (⟨(x : G), hKUQ x.2.1⟩ : ↥(Q)) ∈ β.ker := by
            rw [hβk, Subgroup.mem_subgroupOf]
            exact h
          rw [MonoidHom.mem_ker] at h2
          show Multiplicative.toAdd (β ⟨(x : G), hKUQ x.2.1⟩) 0 = 0
          rw [h2]
          rfl
      calc Nat.card ↥KU ≤ Nat.card U * Fintype.card F * Fintype.card F :=
            hstep₁.trans (Nat.mul_le_mul_right _ hstep₂)
        _ ≤ Fintype.card F ^ 6 := by
            rw [hUcard]
            have hq : 1 ≤ Fintype.card F := Fintype.card_pos
            calc Fintype.card F ^ 3 * Fintype.card F * Fintype.card F =
                  Fintype.card F ^ 5 := by ring
              _ ≤ Fintype.card F ^ 6 := Nat.pow_le_pow_right hq (by norm_num)
    ·
      push Not at h₂
      refine (burnsideC135_card_le_of_hom hUKU (f 0) (hf 0) (fun x => ?_) Set.univ
        fun _ => Set.mem_univ _).trans ?_
      · constructor
        · intro h
          exact h₂ x ⟨x.2, burnsideC135_mem_Wc.mpr ⟨hKUQ x.2, h⟩⟩
        · intro h
          have h2 : (⟨(x : G), hKUQ x.2⟩ : ↥(Q)) ∈ β.ker := by
            rw [hβk, Subgroup.mem_subgroupOf]
            exact h
          rw [MonoidHom.mem_ker] at h2
          show Multiplicative.toAdd (β ⟨(x : G), hKUQ x.2⟩) 0 = 0
          rw [h2]
          rfl
      · rw [hUcard, Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
        ring_nf
        exact le_rfl
  ·
    push Not at h₁
    refine (burnsideC135_card_le_of_hom hUKU (f 1) (hf 1) (fun x => ?_) Set.univ
      fun _ => Set.mem_univ _).trans ?_
    · constructor
      · intro h
        exact h₁ x ⟨x.2, burnsideC135_mem_Wc.mpr ⟨hKUQ x.2, h⟩⟩
      · intro h
        have h2 : (⟨(x : G), hKUQ x.2⟩ : ↥(Q)) ∈ β.ker := by
          rw [hβk, Subgroup.mem_subgroupOf]
          exact h
        rw [MonoidHom.mem_ker] at h2
        show Multiplicative.toAdd (β ⟨(x : G), hKUQ x.2⟩) 1 = 0
        rw [h2]
        rfl
    · rw [hUcard, Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
      ring_nf
      exact le_rfl

end Abelian

end CFSG.ASVolI

end
