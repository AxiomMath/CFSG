module

public import CFSG.Quasithin.Recognition.M12AscTrans
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G]

theorem maximal2_of_normalizer [Finite G] (X S : Subgroup G)
    (hN : ∀ n ∈ X, (∀ s ∈ S, n * s * n⁻¹ ∈ S) → n ∈ S) :
    ∀ R : Subgroup G, R ≤ X → IsPGroup 2 R → S ≤ R → R = S := by
  intro R hRX hRp hSR
  by_contra hne
  have : Group.IsNilpotent ↥R := hRp.isNilpotent
  set T' : Subgroup R := S.subgroupOf R with hT'
  have hlt : T' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun g hg => ?_) hSR
    have : (⟨g, hg⟩ : R) ∈ T' := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨⟨n, hnR⟩, hnN, hnT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent T' hlt)
  apply hnT
  refine Subgroup.mem_subgroupOf.2 (hN n (hRX hnR) (fun s hs => ?_))
  have h1 : (⟨s, hSR hs⟩ : R) ∈ T' := Subgroup.mem_subgroupOf.2 hs
  have h2 := (Subgroup.mem_normalizer_iff.1 hnN _).1 h1
  exact Subgroup.mem_subgroupOf.1 h2

theorem exists_conj_mem_of_maximal [Finite G] (X S : Subgroup G) (hSX : S ≤ X) (hSp : IsPGroup 2 S)
    (hSmax : ∀ R : Subgroup G, R ≤ X → IsPGroup 2 R → S ≤ R → R = S) {y : G} (hyX : y ∈ X)
    (hy2 : y * y = 1) (hy1 : y ≠ 1) : ∃ c ∈ X, c * y * c⁻¹ ∈ S := by
  classical
  let P : Sylow 2 X := sylowOfMaximal X S hSX hSp hSmax
  set yN : X := ⟨y, hyX⟩ with hyN'
  have hyN2 : yN ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hy2)
  have hyNne : yN ≠ 1 := fun e => hy1 (congrArg Subtype.val e)
  have hyp2 : IsPGroup 2 (Subgroup.zpowers yN) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hyN2 hyNne]; simp
  obtain ⟨S1, hS1⟩ := hyp2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq X P S1
  have hmem : yN ∈ ((c • P : Sylow 2 X) : Subgroup X) := by
    rw [hc]; exact hS1 (Subgroup.mem_zpowers yN)
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hmem
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.1 hmem
  have hwy' : (c : G) * (w : G) * (c : G)⁻¹ = y := by
    simpa [MulAut.conj_apply, hyN'] using congrArg Subtype.val hwy
  have hwS : (w : G) ∈ S := Subgroup.mem_subgroupOf.1 hw
  refine ⟨((c⁻¹ : X) : G), (c⁻¹).2, ?_⟩
  have : ((c⁻¹ : X) : G) * y * ((c⁻¹ : X) : G)⁻¹ = (w : G) := by
    rw [← hwy']
    simp only [Subgroup.coe_inv]
    group
  rw [this]
  exact hwS

@[expose] def extInv (V : Subgroup G) (r : G) (hr2 : r * r = 1) (hrV : ∀ v ∈ V, r * v * r⁻¹ ∈ V) :
    Subgroup G where
  carrier := {x | x ∈ V ∨ ∃ v ∈ V, x = v * r}
  one_mem' := Or.inl V.one_mem
  mul_mem' := by
    have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
    rintro a b (ha | ⟨v1, hv1, rfl⟩) (hb | ⟨v2, hv2, rfl⟩)
    · exact Or.inl (V.mul_mem ha hb)
    · exact Or.inr ⟨a * v2, V.mul_mem ha hv2, by group⟩
    · refine Or.inr ⟨v1 * (r * b * r⁻¹), V.mul_mem hv1 (hrV b hb), ?_⟩
      group
    · refine Or.inl ?_
      have : v1 * r * (v2 * r) = v1 * (r * v2 * r⁻¹) := by
        calc v1 * r * (v2 * r) = v1 * (r * v2 * r⁻¹) * (r * r) := by group
          _ = v1 * (r * v2 * r⁻¹) := by rw [hr2, mul_one]
      rw [this]
      exact V.mul_mem hv1 (hrV v2 hv2)
  inv_mem' := by
    have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
    rintro a (ha | ⟨v, hv, rfl⟩)
    · exact Or.inl (V.inv_mem ha)
    · refine Or.inr ⟨r * v⁻¹ * r⁻¹, hrV _ (V.inv_mem hv), ?_⟩
      calc (v * r)⁻¹ = r⁻¹ * v⁻¹ := mul_inv_rev v r
        _ = r * v⁻¹ := by rw [hri]
        _ = (r * v⁻¹ * r⁻¹) * r := by group

theorem le_extInv {V : Subgroup G} {r : G} {hr2 : r * r = 1} {hrV : ∀ v ∈ V, r * v * r⁻¹ ∈ V} :
    V ≤ extInv V r hr2 hrV := fun _ hx => Or.inl hx

theorem card_extInv [Finite G] {V : Subgroup G} {r : G} {hr2 : r * r = 1}
    {hrV : ∀ v ∈ V, r * v * r⁻¹ ∈ V} (hr : r ∉ V) :
    Nat.card (extInv V r hr2 hrV) = 2 * Nat.card V := by
  have hset : ((extInv V r hr2 hrV : Subgroup G) : Set G) =
      (V : Set G) ∪ (fun v => v * r) '' (V : Set G) := by
    ext x
    simp only [Set.mem_union, Set.mem_image]
    constructor
    · rintro (h | ⟨v, hv, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, rfl⟩
    · rintro (h | ⟨v, hv, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, rfl⟩
  have hdisj : Disjoint (V : Set G) ((fun v => v * r) '' (V : Set G)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨v, hv, rfl⟩
    apply hr
    have : r = v⁻¹ * (v * r) := by group
    rw [this]
    exact V.mul_mem (V.inv_mem hv) hx
  have e1 : Nat.card (extInv V r hr2 hrV) = ((extInv V r hr2 hrV : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  have e2 : Nat.card V = (V : Set G).ncard := Nat.card_coe_set_eq _
  rw [e1, hset, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (mul_left_injective r)]
  omega

theorem relIndex_eq_two_of_card [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (h : Nat.card B = 2 * Nat.card A) : A.relIndex B = 2 := by
  have h1 := Subgroup.card_mul_index (A.subgroupOf B)
  have h2 : Nat.card (A.subgroupOf B) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  rw [h2] at h1
  have hpos : 0 < Nat.card A := Nat.card_pos
  show (A.subgroupOf B).index = 2
  have : Nat.card A * (A.subgroupOf B).index = Nat.card A * 2 := by omega
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem card_inf_of_transversal [Finite G] {S X₀ : Subgroup G} {u : G} (huS : u ∈ S)
    (hu : u ∉ X₀) (h : ∀ a ∈ S, a ∈ X₀ ∨ a * u ∈ X₀) :
    Nat.card S = 2 * Nat.card (S ⊓ X₀ : Subgroup G) := by
  have hidx : (X₀.subgroupOf S).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨u, huS⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf]
    show Xor ((b : G) * u ∈ X₀) ((b : G) ∈ X₀)
    rcases h b b.2 with hb | hb
    · refine Or.inr ⟨hb, fun h2 => hu ?_⟩
      have := X₀.mul_mem (X₀.inv_mem hb) h2
      simpa using this
    · refine Or.inl ⟨hb, fun h2 => hu ?_⟩
      have := X₀.mul_mem (X₀.inv_mem h2) hb
      simpa using this
  have h1 := Subgroup.card_mul_index (X₀.subgroupOf S)
  rw [hidx] at h1
  have h2 : Nat.card (X₀.subgroupOf S) = Nat.card (S ⊓ X₀ : Subgroup G) := by
    have : X₀.subgroupOf S = (S ⊓ X₀).subgroupOf S := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : S ⊓ X₀ ≤ S)).toEquiv
  omega

theorem exists_odd_card_of_maximal [Finite G] (X S : Subgroup G) (hSX : S ≤ X) (hSp : IsPGroup 2 S)
    (hSmax : ∀ R : Subgroup G, R ≤ X → IsPGroup 2 R → S ≤ R → R = S) :
    ∃ m : ℕ, Odd m ∧ Nat.card X = Nat.card S * m := by
  let P : Sylow 2 X := sylowOfMaximal X S hSX hSp hSmax
  have hodd : Odd (P : Subgroup X).index := by
    have := P.not_dvd_index
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 this)
  refine ⟨(P : Subgroup X).index, hodd, ?_⟩
  have h1 := Subgroup.card_mul_index (P : Subgroup X)
  have h2 : Nat.card (P : Subgroup X) = Nat.card S := by
    rw [coe_sylowOfMaximal]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem card_le_of_isPGroup_of_odd [Finite G] {Y R : Subgroup G} {j m : ℕ}
    (hY : Nat.card Y = 2 ^ j * m) (hm : Odd m) (hR : IsPGroup 2 R) (hRY : R ≤ Y) :
    Nat.card R ≤ 2 ^ j := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
  have hdvd : Nat.card R ∣ Nat.card Y := Subgroup.card_dvd_of_le hRY
  rw [hk, hY] at hdvd
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  have h2 : 2 ^ k ∣ 2 ^ j := hcop.dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd (by positivity) h2

theorem sq_mem_of_transversal {X X₀ : Subgroup G} (hn : ∀ x ∈ X, ∀ w ∈ X₀, x * w * x⁻¹ ∈ X₀)
    {u : G} (hu : u * u = 1) (huX : u ∈ X) (htr : ∀ a ∈ X, a ∈ X₀ ∨ a * u ∈ X₀) {a : G}
    (ha : a ∈ X) : a * a ∈ X₀ := by
  rcases htr a ha with h | h
  · exact X₀.mul_mem h h
  · have e : a * a = (a * u) * (u * (a * u) * u⁻¹) := by
      calc a * a = a * (u * u) * a := by rw [hu, mul_one]
        _ = (a * u) * (u * (a * u) * u⁻¹) := by group
    rw [e]
    exact X₀.mul_mem h (hn u huX _ h)

end CFSG.Quasithin
