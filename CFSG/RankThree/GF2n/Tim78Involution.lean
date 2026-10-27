module

public import CFSG.RankThree.GF2n.Basic
import CFSG.RankThree.GF2n.Tim78Abelian
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose] def classIn (V A : Subgroup G) : Set (Subgroup G) :=
  {W | (∃ g : G, W = conjSubgroup g V) ∧ W ≤ A}

theorem comm_of_isElemAbelian {E : Subgroup G} (hE : Assembly.IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

variable [Finite G]

theorem exists_two_of_three_le_ncard {V A : Subgroup G} (h : 3 ≤ (classIn V A).ncard) :
    ∃ U W : Subgroup G, U ∈ classIn V A ∧ W ∈ classIn V A ∧ U ≠ V ∧ W ≠ V ∧ U ≠ W := by
  have hfin : (classIn V A).Finite := Set.toFinite _
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff hfin).mp (by omega)
  by_cases haV : a = V
  · exact ⟨b, c, hb, hc, fun h => hab (haV.trans h.symm), fun h => hac (haV.trans h.symm), hbc⟩
  by_cases hbV : b = V
  · exact ⟨a, c, ha, hc, haV, fun h => hbc (hbV.trans h.symm), hac⟩
  · exact ⟨a, b, ha, hb, haV, hbV, hab⟩

theorem sup_eq_of_inf_eq_bot {A V U : Subgroup G} {n : ℕ} (hA : Assembly.IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ (2 * n)) (hVA : V ≤ A) (hUA : U ≤ A)
    (hVcard : Nat.card V = 2 ^ n) (hUcard : Nat.card U = 2 ^ n) (hVU : V ⊓ U = ⊥) :
    V ⊔ U = A := by
  have hUV : V ≤ Subgroup.normalizer (U : Set G) := le_normalizer_of_comm fun v hv u hu =>
    comm_of_isElemAbelian hA (hVA hv) (hUA hu)
  have h := PartTwo.Sec6.card_sup_mul_card_inf hUV
  rw [hVU, Subgroup.card_bot, mul_one, hVcard, hUcard, ← pow_add, ← two_mul] at h
  exact Subgroup.eq_of_le_of_card_ge (sup_le hVA hUA) (by rw [hAcard, h])

theorem tim78_2_17 {A V : Subgroup G} {n : ℕ} (hA : Assembly.IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ (2 * n)) (hVcard : Nat.card V = 2 ^ n) (hVTI : IsTI V)
    (hVA : V ≤ A)
    (hcls : 3 ≤ (classIn V A).ncard) {t : G} (htA : t ∈ Subgroup.normalizer (A : Set G))
    (htV : V ≤ Subgroup.centralizer ({t} : Set G)) (ht : orderOf t = 2) :
    ⁅A, Subgroup.zpowers t⁆ = ⊥ ∨ ⁅A, Subgroup.zpowers t⁆ = V := by
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => comm_of_isElemAbelian hA ha hb
  have htA' : ∀ s ∈ A, t * s * t⁻¹ ∈ A := fun s hs => (Subgroup.mem_normalizer_iff.mp htA s).mp hs
  obtain ⟨U, W, ⟨⟨g₁, hU⟩, hUA⟩, ⟨⟨g₂, hW⟩, hWA⟩, hUV, hWV, hUW⟩ :=
    exists_two_of_three_le_ncard hcls
  have hUcard : Nat.card U = 2 ^ n := by rw [hU, card_conjSubgroup, hVcard]
  have hWcard : Nat.card W = 2 ^ n := by rw [hW, card_conjSubgroup, hVcard]
  have hUTI : IsTI U := hU ▸ isTI_conjSubgroup hVTI g₁
  have hWTI : IsTI W := hW ▸ isTI_conjSubgroup hVTI g₂
  have hVU : V ⊓ U = ⊥ := hU ▸ inf_conjSubgroup_eq_bot_of_isTI hVTI (hU ▸ hUV)
  have hVW : V ⊓ W = ⊥ := hW ▸ inf_conjSubgroup_eq_bot_of_isTI hVTI (hW ▸ hWV)
  have hUWbot : U ⊓ W = ⊥ := by
    have e : W = conjSubgroup (g₂ * g₁⁻¹) U := by
      rw [hU, hW, ← conjSubgroup_mul, inv_mul_cancel_right]
    rw [e]
    exact inf_conjSubgroup_eq_bot_of_isTI hUTI (e ▸ hUW.symm)
  have hAVU : V ⊔ U = A := sup_eq_of_inf_eq_bot hA hAcard hVA hUA hVcard hUcard hVU
  have hAVW : V ⊔ W = A := sup_eq_of_inf_eq_bot hA hAcard hVA hWA hVcard hWcard hVW
  set C := A ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  have hVC : V ≤ C := le_inf hVA htV
  by_cases hCV : C = V
  ·
    right
    have hcommV : ∀ a ∈ A, ⁅a, t⁆ ∈ V := by
      intro a ha
      have ha2 : a⁻¹ ^ 2 = 1 := by rw [inv_pow, hA.2 a ha, inv_one]
      have hd : dlt t (dlt t a⁻¹) = 1 := by
        rw [dlt_dlt hAc htA' (A.inv_mem ha) ha2, ht2, dlt]
        group
      have hmem : dlt t a⁻¹ ∈ C := ⟨dlt_mem htA' (A.inv_mem ha),
        Subgroup.mem_centralizer_singleton_iff.mpr (dlt_eq_one_iff.mp hd).symm⟩
      rw [hCV] at hmem
      have : ⁅a, t⁆ = dlt t a⁻¹ := by
        rw [commutatorElement_def, dlt, inv_inv]
        group
      rw [this]
      exact hmem
    have hle : ⁅A, Subgroup.zpowers t⁆ ≤ V := by
      rw [Subgroup.commutator_le]
      intro a ha y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hk : t ^ k = 1 ∨ t ^ k = t := by
        rw [← zpow_mod_orderOf, ht]
        rcases Int.emod_two_eq_zero_or_one k with h | h
        · left
          rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
        · right
          rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
      rcases hk with hk | hk
      · rw [hk, commutatorElement_one_right]
        exact V.one_mem
      · rw [hk]
        exact hcommV a ha
    refine le_antisymm hle ?_
    have hcommA : ∀ a ∈ A, ⁅a, t⁆ ∈ A := fun a ha => hVA (hcommV a ha)
    let f : A →* A :=
      { toFun := fun a => ⟨⁅(a : G), t⁆, hcommA a a.2⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp only [Subgroup.coe_mul, commutatorElement_def]
          have h1 : t * (a : G)⁻¹ * t⁻¹ ∈ A := htA' _ (A.inv_mem a.2)
          have h2 : t * (b : G)⁻¹ * t⁻¹ ∈ A := htA' _ (A.inv_mem b.2)
          have hab : (a : G) * b = b * a := hAc _ a.2 _ b.2
          calc (a : G) * b * t * ((a : G) * b)⁻¹ * t⁻¹
              = (a : G) * ((b : G) * ((t * (b : G)⁻¹ * t⁻¹) * (t * (a : G)⁻¹ * t⁻¹))) := by
                group
            _ = (a : G) * ((b : G) * ((t * (a : G)⁻¹ * t⁻¹) * (t * (b : G)⁻¹ * t⁻¹))) := by
                rw [hAc _ h2 _ h1]
            _ = (a : G) * (((b : G) * (t * (a : G)⁻¹ * t⁻¹)) * (t * (b : G)⁻¹ * t⁻¹)) := by
                group
            _ = (a : G) * (((t * (a : G)⁻¹ * t⁻¹) * b) * (t * (b : G)⁻¹ * t⁻¹)) := by
                rw [hAc _ b.2 _ h1]
            _ = (a : G) * t * (a : G)⁻¹ * t⁻¹ * ((b : G) * t * (b : G)⁻¹ * t⁻¹) := by group }
    have hker : f.ker = V.subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h' : ⁅(a : G), t⁆ = 1 := congrArg Subtype.val h
        rw [commutatorElement_eq_one_iff_mul_comm] at h'
        have : (a : G) ∈ C := ⟨a.2, Subgroup.mem_centralizer_singleton_iff.mpr h'⟩
        rwa [hCV] at this
      · intro h
        apply Subtype.ext
        have := Subgroup.mem_centralizer_singleton_iff.mp (htV h)
        change ⁅(a : G), t⁆ = 1
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact this
    have hrange : f.range = V.subgroupOf A := by
      have hle' : f.range ≤ V.subgroupOf A := by
        rintro _ ⟨a, rfl⟩
        exact hcommV a a.2
      refine Subgroup.eq_of_le_of_card_ge hle' ?_
      have hVsub : Nat.card (V.subgroupOf A) = 2 ^ n := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv, hVcard]
      have h1 := Subgroup.card_mul_index f.ker
      rw [Subgroup.index_ker, hker, hVsub, hAcard, two_mul, pow_add] at h1
      rw [hVsub, Nat.eq_of_mul_eq_mul_left (by positivity) h1]
    intro v hv
    have hv' : (⟨v, hVA hv⟩ : A) ∈ f.range := by
      rw [hrange]
      exact hv
    obtain ⟨a, ha⟩ := hv'
    have : ⁅(a : G), t⁆ = v := congrArg Subtype.val ha
    rw [← this]
    exact Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_zpowers t)
  ·
    left
    have hVltC : V < C := lt_of_le_of_ne hVC (Ne.symm hCV)
    have hCA : C ≤ A := inf_le_left
    have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
    obtain ⟨k, hk⟩ := (hA2.to_le hCA).exists_card_eq
    have hkn : n < k := by
      have := Subgroup.card_lt_of_lt hVltC
      rw [hVcard, hk] at this
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    have hXC : ∀ X : Subgroup G, X ≤ A → Nat.card X = 2 ^ n → C ⊓ X ≠ ⊥ := by
      intro X hXA hXcard hbot
      have hCX : C ≤ Subgroup.normalizer (X : Set G) := le_normalizer_of_comm fun c hc x hx =>
        hAc c (hCA hc) x (hXA hx)
      have h := PartTwo.Sec6.card_sup_mul_card_inf hCX
      rw [hbot, Subgroup.card_bot, mul_one, hk, hXcard] at h
      have hle : Nat.card (C ⊔ X : Subgroup G) ≤ Nat.card A :=
        Subgroup.card_le_of_le (sup_le hCA hXA)
      rw [h, hAcard, ← pow_add] at hle
      have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
      omega
    have hnorm : ∀ X : Subgroup G, IsTI X → X ≤ A → Nat.card X = 2 ^ n →
        ∀ x ∈ X, t * x * t⁻¹ ∈ X := by
      intro X hXTI hXA hXcard
      obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (hXC X hXA hXcard)
      have hut : t * u = u * t := (Subgroup.mem_centralizer_singleton_iff.mp hu.1.2).symm
      have hmem : u ∈ X ⊓ conjSubgroup t X := by
        refine Subgroup.mem_inf.mpr ⟨hu.2, ?_⟩
        rw [mem_conjSubgroup]
        have : t⁻¹ * u * t = u := by
          calc t⁻¹ * u * t = t⁻¹ * (u * t) := by group
            _ = t⁻¹ * (t * u) := by rw [hut]
            _ = u := by group
        rw [this]
        exact hu.2
      have heq : conjSubgroup t X = X := conjSubgroup_eq_of_isTI hXTI fun h => by
        rw [h] at hmem
        exact hu1 (Subtype.ext (Subgroup.mem_bot.mp hmem))
      intro x hx
      have : t * x * t⁻¹ ∈ conjSubgroup t X := by
        rw [mem_conjSubgroup]
        group
        exact hx
      rwa [heq] at this
    have htU := hnorm U hUTI hUA hUcard
    have htW := hnorm W hWTI hWA hWcard
    have hcen : ∀ a ∈ A, t * a = a * t := by
      intro a ha
      have hd : ∀ X : Subgroup G, V ⊔ X = A → (∀ x ∈ X, t * x * t⁻¹ ∈ X) → X ≤ A →
          dlt t a ∈ X := by
        intro X hVX htX hXA
        have hXV : X ≤ Subgroup.normalizer (V : Set G) := le_normalizer_of_comm fun x hx v hv =>
          hAc x (hXA hx) v (hVA hv)
        obtain ⟨v, hv, x, hx, rfl⟩ := exists_mul_of_mem_sup hXV (hVX ▸ ha)
        have hvt : t * v * t⁻¹ = v := by
          have := Subgroup.mem_centralizer_singleton_iff.mp (htV hv)
          rw [← this]
          group
        have : dlt t (v * x) = dlt t x := by
          unfold dlt
          calc (v * x)⁻¹ * (t * (v * x) * t⁻¹)
              = x⁻¹ * v⁻¹ * ((t * v * t⁻¹) * (t * x * t⁻¹)) := by group
            _ = x⁻¹ * v⁻¹ * (v * (t * x * t⁻¹)) := by rw [hvt]
            _ = x⁻¹ * (t * x * t⁻¹) := by group
        rw [this]
        exact dlt_mem htX hx
      have h1 : dlt t a ∈ U ⊓ W := ⟨hd U hAVU htU hUA, hd W hAVW htW hWA⟩
      rw [hUWbot, Subgroup.mem_bot] at h1
      exact dlt_eq_one_iff.mp h1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (hcen a ha) k).eq

end CFSG.RankThree.GF2n.Tim78
