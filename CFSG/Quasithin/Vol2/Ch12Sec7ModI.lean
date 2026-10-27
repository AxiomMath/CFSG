module

import all CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Quasithin.Vol2.Ch12Sec2Ident
public import CFSG.Quasithin.Vol2.Ch12Sec7ModF

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem le_of_isPGroup_of_le_normalizer [Finite G] {T U : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hU : IsPGroup 2 U) (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : IsPGroup 2 (U ⊔ T : Subgroup G) := hU.to_sup_of_normal_left' hT.1 hTU
  have hle : T ≤ U ⊔ T := le_sup_right
  have hrel : T.relIndex (U ⊔ T) = 1 := by
    have hp : IsPGroup 2 (T.subgroupOf (U ⊔ T)) :=
      hT.1.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hK
    have hdvd : T.relIndex (U ⊔ T) ∣ 2 ^ n := by
      rw [← hn, Subgroup.relIndex]
      exact Subgroup.index_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hodd : ¬ 2 ∣ T.relIndex (U ⊔ T) := fun h2 =>
      hT.2 (dvd_trans h2 ⟨_, (Subgroup.relIndex_mul_index hle).symm⟩)
    rcases k with _ | k
    · simpa using hk
    · exact absurd (hk ▸ dvd_pow_self 2 (Nat.succ_ne_zero k)) hodd
  have := Subgroup.relIndex_eq_one.1 hrel
  exact le_sup_left.trans this

theorem normalizer_of_maps [Finite G] {W : Subgroup G} {x : G}
    (hmap : ∀ w ∈ W, x * w * x⁻¹ ∈ W) : x ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hmap g, fun hg => ?_⟩
  let f : ↥W → ↥W := fun w => ⟨x * w * x⁻¹, hmap w w.2⟩
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hf ⟨_, hg⟩
  have := congrArg Subtype.val hw
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact w.2

theorem le_normalizer_of_maps [Finite G] {W K : Subgroup G}
    (hmap : ∀ x ∈ K, ∀ w ∈ W, x * w * x⁻¹ ∈ W) : K ≤ Subgroup.normalizer (W : Set G) :=
  fun x hx => normalizer_of_maps (hmap x hx)

variable {V : Subgroup G} [IsMulCommutative ↥V]

@[expose] def Coding.subG (C : Coding ↥V) (l : List ℕ) (h0 : 0 ∈ l)
    (hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ V, C.cd ⟨g, hg⟩ ∈ l}
  one_mem' := ⟨V.one_mem, by
    have h := C.cd_one
    exact (show C.cd 1 ∈ l by rw [h]; exact h0)⟩
  mul_mem' {a b} := by
    rintro ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨V.mul_mem ha hb, ?_⟩
    have e := C.cd_mul ⟨a, ha⟩ ⟨b, hb⟩
    rw [show (⟨a * b, V.mul_mem ha hb⟩ : ↥V) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, e]
    exact hx _ ha' _ hb'
  inv_mem' {a} := by
    rintro ⟨ha, ha'⟩
    refine ⟨V.inv_mem ha, ?_⟩
    rw [show (⟨a⁻¹, V.inv_mem ha⟩ : ↥V) = (⟨a, ha⟩)⁻¹ from rfl, C.cd_inv]
    exact ha'

theorem Coding.mem_subG (C : Coding ↥V) {l : List ℕ} {h0 : 0 ∈ l}
    {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l} (v : ↥V) :
    (v : G) ∈ C.subG l h0 hx ↔ C.cd v ∈ l :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.2, h⟩⟩

theorem Coding.subG_le (C : Coding ↥V) (l : List ℕ) (h0 : 0 ∈ l)
    (hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l) : C.subG l h0 hx ≤ V := fun _ ⟨hg, _⟩ => hg

theorem Coding.card_subG (C : Coding ↥V) {l : List ℕ} {h0 : 0 ∈ l}
    {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l} (hnd : l.Nodup) (hlt : ∀ c ∈ l, c < 64) :
    Nat.card (C.subG l h0 hx) = l.length := by
  have e : ↥(C.subG l h0 hx) ≃ {v : ↥V | (v : G) ∈ C.subG l h0 hx} :=
    { toFun := fun g => ⟨⟨g, C.subG_le l h0 hx g.2⟩, g.2⟩
      invFun := fun v => ⟨v.1, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact C.card_of_codes _ l hnd hlt fun v => C.mem_subG (h0 := h0) (hx := hx) v

theorem Coding.eq_subG (C : Coding ↥V) {l : List ℕ} {h0 : 0 ∈ l}
    {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l} {W : Subgroup G} (hW : W ≤ V)
    (h : ∀ v : ↥V, (v : G) ∈ W ↔ C.cd v ∈ l) : W = C.subG l h0 hx := by
  ext g
  constructor
  · intro hg
    exact (C.mem_subG ⟨g, hW hg⟩).2 ((h ⟨g, hW hg⟩).1 hg)
  · intro hg
    exact (h ⟨g, C.subG_le l h0 hx hg⟩).2 ((C.mem_subG ⟨g, C.subG_le l h0 hx hg⟩).1 hg)

omit [IsMulCommutative ↥V] in
theorem conjAct_val {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ((conjAct V ⟨x, hx⟩ v : ↥V) : G) = x * v * x⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe V _ v

omit [IsMulCommutative ↥V] in
theorem mem_autOn' {K : Subgroup G} {a : MulAut ↥V} :
    a ∈ autOn K V ↔ ∃ x, ∃ hx : x ∈ Subgroup.normalizer (V : Set G), x ∈ K ∧
      conjAct V ⟨x, hx⟩ = a := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, y.2, hy, rfl⟩
  · rintro ⟨x, hx, hxK, rfl⟩
    exact ⟨⟨x, hx⟩, hxK, rfl⟩

omit [IsMulCommutative ↥V] in
theorem conjAct_mem_autOn {K : Subgroup G} {x : G} (hxK : x ∈ K)
    (hx : x ∈ Subgroup.normalizer (V : Set G)) : conjAct V ⟨x, hx⟩ ∈ autOn K V :=
  mem_autOn'.2 ⟨x, hx, hxK, rfl⟩

omit [IsMulCommutative ↥V] in
theorem conjAct_eq_one' {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨x, hx⟩ = 1 ↔ x ∈ Subgroup.centralizer (V : Set G) :=
  A4.conjAct_eq_one_iff

omit [IsMulCommutative ↥V] in
theorem conjAct_mul' {x y : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    conjAct V ⟨x * y, Subgroup.mul_mem _ hx hy⟩ = conjAct V ⟨x, hx⟩ * conjAct V ⟨y, hy⟩ :=
  map_mul (conjAct V) ⟨x, hx⟩ ⟨y, hy⟩

theorem cd_conj (C : Coding ↥V) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    C.cd ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx v).1 v.2⟩ =
      (C.cB (conjAct V ⟨x, hx⟩)).app (C.cd v) := by
  rw [← C.cd_apply]
  congr 1

theorem commute_iff_code (C : Coding ↥V) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (v : ↥V) : x * v = v * x ↔ (C.cB (conjAct V ⟨x, hx⟩)).app (C.cd v) = C.cd v := by
  rw [← C.apply_eq_self_iff]
  constructor
  · intro h
    apply Subtype.ext
    rw [conjAct_val, h, mul_inv_cancel_right]
  · intro h
    have := congrArg Subtype.val h
    rw [conjAct_val] at this
    calc x * v = x * v * x⁻¹ * x := by group
      _ = v * x := by rw [this]

variable [Finite G]

omit [IsMulCommutative ↥V] in
theorem map_pCore_autOnSurj {P : Subgroup G} (hP : P ≤ Subgroup.normalizer (V : Set G))
    (hK : IsPGroup 2 (P ⊓ Subgroup.centralizer (V : Set G) : Subgroup G)) :
    (CFSG.Open.pCore 2 ↥P).map (autOnSurj hP) = CFSG.Open.pCore 2 ↥(autOn P V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := autOnSurj hP with hf
  have hsurj := autOnSurj_surjective hP
  apply le_antisymm (CFSG.LieType.BorelTits.map_pCore_le 2 f hsurj)
  set N := (CFSG.Open.pCore 2 ↥(autOn P V)).comap f with hN
  have hNn : N.Normal := (CFSG.LieType.BorelTits.pCore_normal 2).comap f
  have hNp : IsPGroup 2 N := by
    have hker : IsPGroup 2 f.ker := by
      rw [ker_autOnSurj hP]
      have e : (Subgroup.centralizer (V : Set G)).subgroupOf P ≃*
          (P ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :=
        { toFun := fun x => ⟨x.1.1, x.1.2, Subgroup.mem_subgroupOf.1 x.2⟩
          invFun := fun x => ⟨⟨x.1, x.2.1⟩, Subgroup.mem_subgroupOf.2 x.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl }
      exact hK.of_equiv e.symm
    exact (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥(autOn P V))).comap_of_ker_isPGroup f
      hker
  have hle := CFSG.LieType.BorelTits.le_pCore 2 hNn hNp
  intro a ha
  obtain ⟨y, rfl⟩ := hsurj a
  exact ⟨y, hle ha, rfl⟩

omit [IsMulCommutative ↥V] in
theorem autOn_pCoreOf {P : Subgroup G} (hP : P ≤ Subgroup.normalizer (V : Set G))
    (hK : IsPGroup 2 (P ⊓ Subgroup.centralizer (V : Set G) : Subgroup G)) :
    autOn (pCoreOf 2 P) V =
      (CFSG.Open.pCore 2 ↥(autOn P V)).map (autOn P V).subtype := by
  set f := autOnSurj hP with hf
  have himg : autOn (pCoreOf 2 P) V =
      ((CFSG.Open.pCore 2 ↥P).map f).map (autOn P V).subtype := by
    ext a
    constructor
    · intro ha
      obtain ⟨x, hx, hxP, rfl⟩ := mem_autOn'.1 ha
      obtain ⟨y, hy, rfl⟩ := hxP
      exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact conjAct_mem_autOn (Subgroup.mem_map_of_mem P.subtype hy) (hP y.2)
  rw [himg, map_pCore_autOnSurj hP hK]

end CFSG.Quasithin.H13.S127.Mod

end
