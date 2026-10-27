module

public import CFSG.Quasithin.Vol2.Ch12Sec6L19d
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 S126L19d Equiv
open scoped IsMulCommutative

namespace S126L20

theorem toAdd_iota_mul (y y' : D8) :
    Multiplicative.toAdd (iota (y * y')) =
      Multiplicative.toAdd (iota y) + Multiplicative.toAdd (iota y') := by
  rw [map_mul, toAdd_mul]

theorem mul_self_eq_one (y : D8) : y * y = 1 := by
  apply iota_inj
  rw [map_one]
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_iota_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem card_D8_eq : Nat.card D8 = 64 := by
  refine le_antisymm ?_ card_D8
  have hinj : Function.Injective fun y : D8 => cmp (Multiplicative.toAdd (iota y)) := by
    intro y y' h
    apply iota_inj
    apply Multiplicative.toAdd.injective
    rw [← emb_iota y, ← emb_iota y']
    exact congrArg emb h
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := Fin 6 → ZMod 2), Fintype.card_fun, ZMod.card,
    Fintype.card_fin] at h

theorem wt_iota_of_wt4 {y : D8} (hy : HasWt 4 y) :
    (Finset.univ.filter fun i => Multiplicative.toAdd (iota y) i ≠ 0).card = 4 := by
  obtain ⟨m, rfl, hm⟩ := hy
  rw [iota_mk]
  rcases nrm_eq m with h | h
  · rw [h]
    exact hm
  · rw [h]
    change (Finset.univ.filter fun i => (Multiplicative.toAdd (m : PermMod 8) + ones8) i ≠ 0).card
      = 4
    rw [wt_add_ones]
    change 8 - wt (m : PermMod 8) = 4
    rw [hm]

theorem not_hasWt4_one : ¬ HasWt 4 (1 : D8) := by
  rintro ⟨m, hm, h4⟩
  rcases (mk_eq_one_iff m).1 hm with rfl | rfl
  · rw [Subgroup.coe_one, wt_one] at h4
    exact absurd h4 (by norm_num)
  · change wt (allOnes 8) = 4 at h4
    rw [wt_allOnes] at h4
    exact absurd h4 (by norm_num)

@[expose] noncomputable def kap : D8 →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun y := Multiplicative.ofAdd
    (Multiplicative.toAdd (iota y) 3 + Multiplicative.toAdd (iota y) 4,
      Multiplicative.toAdd (iota y) 3 + Multiplicative.toAdd (iota y) 5)
  map_one' := by
    simp only [map_one, toAdd_one, Pi.zero_apply, add_zero]
    rfl
  map_mul' y y' := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_iota_mul, Pi.add_apply, toAdd_mul, toAdd_ofAdd, Prod.mk_add_mk]
    congr 1 <;> ring

theorem kap_apply (y : D8) : Multiplicative.toAdd (kap y) =
    (Multiplicative.toAdd (iota y) 3 + Multiplicative.toAdd (iota y) 4,
      Multiplicative.toAdd (iota y) 3 + Multiplicative.toAdd (iota y) 5) := rfl

theorem ker_chk : ∀ z₁ z₂ : Fin 6 → ZMod 2,
    emb z₁ 3 + emb z₁ 4 = 0 → emb z₁ 3 + emb z₁ 5 = 0 →
    emb z₂ 3 + emb z₂ 4 = 0 → emb z₂ 3 + emb z₂ 5 = 0 →
    (Finset.univ.filter fun i => emb z₁ i ≠ 0).card = 4 →
    (Finset.univ.filter fun i => emb z₂ i ≠ 0).card = 4 →
    (Finset.univ.filter fun i => (emb z₁ + emb z₂) i ≠ 0).card ≠ 4 := by
  decide +kernel

theorem kap_eq_one {y : D8} (h : kap y = 1) :
    Multiplicative.toAdd (iota y) 3 + Multiplicative.toAdd (iota y) 4 = 0 ∧
      Multiplicative.toAdd (iota y) 3 + Multiplicative.toAdd (iota y) 5 = 0 := by
  have h1 := congrArg Multiplicative.toAdd h
  rw [kap_apply, toAdd_one] at h1
  exact Prod.mk.inj h1

theorem card_le_two_of_forall {K : Type*} [Group K] [Finite K]
    (h : ∀ a b : K, a ≠ 1 → b ≠ 1 → a = b) : Nat.card K ≤ 2 := by
  classical
  have hinj : Function.Injective fun k : K => if k = 1 then (0 : Fin 2) else 1 := by
    intro a b hab
    by_cases ha : a = 1 <;> by_cases hb : b = 1
    · rw [ha, hb]
    · simp [ha, hb] at hab
    · simp [ha, hb] at hab
    · exact h a b ha hb
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_fin] at this

theorem card_le_eight {W : Subgroup D8} (hW : ∀ y ∈ W, y ≠ 1 → HasWt 4 y) : Nat.card W ≤ 8 := by
  let f : ↥W →* Multiplicative (ZMod 2 × ZMod 2) := kap.comp W.subtype
  have h1 : Nat.card W = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h2 : Nat.card f.range ≤ 4 := by
    calc Nat.card f.range ≤ Nat.card (Multiplicative (ZMod 2 × ZMod 2)) :=
          Subgroup.card_le_card_group _
      _ = 4 := by
          rw [Nat.card_eq_fintype_card]
          rfl
  have h3 : Nat.card f.ker ≤ 2 := by
    refine card_le_two_of_forall fun a b ha hb => ?_
    by_contra hab
    set y₁ : D8 := ((a : ↥W) : D8) with hy₁
    set y₂ : D8 := ((b : ↥W) : D8) with hy₂
    have hy₁1 : y₁ ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
    have hy₂1 : y₂ ≠ 1 := fun h => hb (Subtype.ext (Subtype.ext h))
    have hy12 : y₁ ≠ y₂ := fun h => hab (Subtype.ext (Subtype.ext h))
    have hk₁ : kap y₁ = 1 := a.2
    have hk₂ : kap y₂ = 1 := b.2
    have hm : y₁ * y₂ ∈ W := W.mul_mem (a : ↥W).2 (b : ↥W).2
    have hm1 : y₁ * y₂ ≠ 1 := by
      intro h
      apply hy12
      calc y₁ = y₁ * (y₂ * y₂) := by rw [mul_self_eq_one, mul_one]
        _ = (y₁ * y₂) * y₂ := by rw [mul_assoc]
        _ = y₂ := by rw [h, one_mul]
    have w₁ := wt_iota_of_wt4 (hW y₁ (a : ↥W).2 hy₁1)
    have w₂ := wt_iota_of_wt4 (hW y₂ (b : ↥W).2 hy₂1)
    have w₃ := wt_iota_of_wt4 (hW _ hm hm1)
    rw [toAdd_iota_mul] at w₃
    obtain ⟨c₁, c₂⟩ := kap_eq_one hk₁
    obtain ⟨d₁, d₂⟩ := kap_eq_one hk₂
    rw [← emb_iota y₁] at w₁ c₁ c₂ w₃
    rw [← emb_iota y₂] at w₂ d₁ d₂ w₃
    exact ker_chk _ _ c₁ c₂ d₁ d₂ w₁ w₂ w₃
  rw [h1]
  calc Nat.card f.range * Nat.card f.ker ≤ 4 * 2 := Nat.mul_le_mul h2 h3
    _ = 8 := by norm_num

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem card_V (F : Frame126 T L V) :
    Nat.card V = 64 * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup F.β.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective F.β F.β_surj).toEquiv,
    card_D8_eq] at h1
  rw [h1]
  congr 1
  exact Nat.card_congr
    { toFun := fun x => ⟨((x : ↥V) : G), (x : ↥V).2, (F.β_ker _).1 x.2⟩
      invFun := fun y => ⟨⟨y, y.2.1⟩, (F.β_ker _).2 y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

omit [IsMulCommutative ↥V] in
theorem facts (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    V ≤ T ∧ T ≤ Subgroup.normalizer (V : Set G) ∧
      (∀ m ∈ Subgroup.normalizer (L : Set G),
        CFSG.conjugate V m = V ∨ V ⊓ CFSG.conjugate V m = ⊥) ∧
      (Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) ∨
        V ⊓ Subgroup.centralizer (L : Set G) = ⊥) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, hTI, hMV, -⟩ := hall V hyp.irrPlus
  exact ⟨hVT, hTV, hTI, hMV⟩

omit [IsMulCommutative ↥V] in
theorem isPGroup_V (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) : IsPGroup 2 V :=
  hH.hyp.sylow.1.to_le (facts h1222 hH).1

omit [Finite G] [IsMulCommutative ↥V] in
theorem exists_centralizer_conj (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {g v : G} (hv : v ∈ V ⊓ conjSubgroup V g) :
    ∃ c ∈ Subgroup.centralizer ({v} : Set G), conjSubgroup V g = conjSubgroup V c := by
  obtain ⟨hvV, hvg⟩ := hv
  obtain ⟨l, hlL, hl⟩ := hfus v hvV g (mem_conjSubgroup_iff.1 hvg)
  refine ⟨l⁻¹ * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc l⁻¹ * g * v = l⁻¹ * (g * v * g⁻¹) * g := by group
      _ = l⁻¹ * (l * v * l⁻¹) * g := by rw [hl]
      _ = v * (l⁻¹ * g) := by group
  · rw [← conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ (hLV hlL))]

omit [IsMulCommutative ↥V] in
theorem centralizer_le_normalizer_V (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) {x : G}
    (hxV : x ∈ V) (hx1 : x ≠ 1)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨-, -, hTI, -⟩ := facts h1222 hH
  intro c hc
  exact mem_normalizer_of_TI hTI hxV hx1 (hC hc) (Subgroup.mem_centralizer_singleton_iff.1 hc)

theorem centralizer_le_of_not_wt4 (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1262 : Theorem12_6_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {x : G} (hxV : x ∈ V)
    (hx1 : x ≠ 1) (hx4 : ¬ F.Wt4 x) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  apply centralizer_le_normalizer_V h1222 hH hxV hx1
  by_cases hβ : F.β ⟨x, hxV⟩ = 1
  · have hxL : x ∈ Subgroup.centralizer (L : Set G) := (F.β_ker _).1 hβ
    have hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := fun h => hx1 (by
      have hm : x ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hxV, hxL⟩
      rw [h] at hm
      exact hm)
    have hxT : x ∈ V ⊓ Subgroup.centralizer (T : Set G) := by
      rw [← (part2 h1222 hH hZ).2]
      exact ⟨hxV, hxL⟩
    exact centralizer_le_M h331 hH hx1 ((facts h1222 hH).1 hxV) hxL hxT.2
  · rcases cases_of_ne_one hβ with hn | h4
    · exact h1262 G T L V F hH x ⟨hxV, hn⟩
    · exact absurd ⟨hxV, h4⟩ hx4

theorem wt4_of_mem_inter (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {g : G} (hg : g ∉ Subgroup.normalizer (V : Set G)) {x : G}
    (hx : x ∈ V ⊓ conjSubgroup V g) (hx1 : x ≠ 1) : F.Wt4 x := by
  by_contra h4
  obtain ⟨c, hc, hcg⟩ := exists_centralizer_conj hH.hyp.irrPlus.2.2.1 hfus hx
  have hcN := centralizer_le_of_not_wt4 h331 h1222 h1262 F hH hx.1 hx1 h4 hc
  apply hg
  rw [← conjSubgroup_eq_iff_mem_normalizer, hcg, conjSubgroup_eq_iff_mem_normalizer.2 hcN]

theorem card_inter_le (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    {g : G} (hg : g ∉ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(V ⊓ conjSubgroup V g) ≤ 8 := by
  set U := V ⊓ conjSubgroup V g with hU
  have hw : ∀ u : ↥U, (u : G) ≠ 1 → HasWt 4 (F.β ⟨u, u.2.1⟩) := fun u hu => by
    obtain ⟨hv, h⟩ := wt4_of_mem_inter h331 h1222 h1262 F hH hfus hg u.2 hu
    exact h
  let W : Subgroup D8 := (U.subgroupOf V).map F.β
  have hW : ∀ y ∈ W, y ≠ 1 → HasWt 4 y := by
    rintro _ ⟨u, hu, rfl⟩ hu1
    have hu1' : (u : G) ≠ 1 := fun h => hu1 (by rw [show u = 1 from Subtype.ext h, map_one])
    exact hw ⟨u, hu⟩ hu1'
  let φ : ↥U → ↥W := fun u => ⟨F.β ⟨u, u.2.1⟩, ⟨⟨u, u.2.1⟩, u.2, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro u u' h
    have h1 : F.β ⟨u, u.2.1⟩ = F.β ⟨u', u'.2.1⟩ := congrArg Subtype.val h
    by_contra hne
    have hm : ((u⁻¹ * u' : ↥U) : G) ≠ 1 := by
      intro h2
      apply hne
      have h3 : u⁻¹ * u' = 1 := Subtype.ext h2
      exact (inv_mul_eq_one.1 h3)
    have h4 := hw (u⁻¹ * u') hm
    have h5 : F.β ⟨((u⁻¹ * u' : ↥U) : G), (u⁻¹ * u').2.1⟩ = 1 := by
      have e : (⟨((u⁻¹ * u' : ↥U) : G), (u⁻¹ * u').2.1⟩ : ↥V) =
          (⟨u, u.2.1⟩ : ↥V)⁻¹ * ⟨u', u'.2.1⟩ := rfl
      rw [e, map_mul, map_inv, h1, inv_mul_cancel]
    rw [h5] at h4
    exact not_hasWt4_one h4
  calc Nat.card ↥U ≤ Nat.card ↥W := Nat.card_le_card_of_injective φ hφ
    _ ≤ 8 := card_le_eight hW

theorem rParam_bounds (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹) :
    3 ≤ E3.rParam V ∧ (V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ → 4 ≤ E3.rParam V) := by
  have hV2 := isPGroup_V h1222 hH
  have key : ∀ U : Subgroup G, U ≤ V →
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) →
        Nat.card V ≤ 2 ^ E3.mQuot V U * 8 := by
    intro U hUV hC
    obtain ⟨c, hcU, hcN⟩ := Set.not_subset.1 hC
    have hUle : U ≤ V ⊓ conjSubgroup V c := by
      intro u hu
      refine ⟨hUV hu, mem_conjSubgroup_iff.2 ?_⟩
      have h1 : u * c = c * u := Subgroup.mem_centralizer_iff.1 hcU u hu
      rw [← h1, mul_inv_cancel_right]
      exact hUV hu
    rw [E3.card_eq_two_pow_mul hV2 hUV]
    exact Nat.mul_le_mul_left _ ((Subgroup.card_le_of_le hUle).trans
      (card_inter_le h331 h1222 h1262 F hH hfus hcN))
  have hV : Nat.card V = 64 * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) := card_V F
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have bound : ∀ (n : ℕ), 2 ^ n * 8 ≤ Nat.card V → ∀ U ∈ {U : Subgroup G | U ≤ V ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)},
        (n : ℕ∞) ≤ (E3.mQuot V U : ℕ∞) := by
    intro n hn U hU
    have h1 := key U hU.1 hU.2
    have h2 : 2 ^ n ≤ 2 ^ E3.mQuot V U := by
      have := hn.trans h1
      exact Nat.le_of_mul_le_mul_right this (by norm_num)
    exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  refine ⟨le_iInf₂ fun U hU => ?_, fun hZ => le_iInf₂ fun U hU => ?_⟩
  · have := bound 3 (by rw [hV]; omega) U hU
    exact_mod_cast this
  · have h2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := (part2 h1222 hH hZ).1
    have := bound 4 (by rw [hV, h2]; norm_num) U hU
    exact_mod_cast this

end S126L20

end CFSG.Quasithin.H13
