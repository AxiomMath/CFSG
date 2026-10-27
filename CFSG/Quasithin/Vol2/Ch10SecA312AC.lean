module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Vol2.Ch10SecA312AA

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem pCoreOf_eq_map (B : Subgroup X) : pCoreOf 2 B = (CFSG.pCore 2 ↥B).map B.subtype :=
  CFSG.openPCoreOf_eq_map_pCore 2 B

omit [Finite X] in
theorem not_isPGroup_two_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : ¬ IsPGroup 2 Q := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Q := h2.isNilpotent
  obtain ⟨a, b, hab⟩ := hQ.2.2
  have : Nontrivial (Q ⧸ Subgroup.center Q) := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have : Nontrivial Q := (QuotientGroup.mk_surjective (s := Subgroup.center Q)).nontrivial
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := Q)).ne
    (Group.isPerfect_def.mp hQ.1)

theorem false_of_pCore_eq_bot {B V : Subgroup X} (h : CFSG.pCore 2 ↥B = ⊥) (hVB : V ≤ B)
    (hV : IsElemAbelian 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set X)) (hcomm : ⁅V, B⁆ = V)
    (hV1 : V ≠ ⊥) (hc : pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X)) : False := by
  refine false_of_V hVB hV hBV hcomm hV1 hc fun v hv _ _ b _ => ?_
  rw [pCoreOf_eq_map, h, Subgroup.map_bot, Subgroup.mem_bot] at hv
  rw [hv, mul_one, one_mul]

theorem false_of_quasisimple_quotient {B V : Subgroup X} (W : Subgroup ↥B) [W.Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hW : ∀ w ∈ W, w ^ p = 1) (hq : CFSG.IsQuasisimple (↥B ⧸ W))
    (hVB : V ≤ B) (hV : IsElemAbelian 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set X))
    (hcomm : ⁅V, B⁆ = V) (hV1 : V ≠ ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V' : Subgroup ↥B := V.subgroupOf B with hV'
  have hV'n : V'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVB).mpr hBV
  have hV'p : IsPGroup 2 V' := fun x => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using hV.2 _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  set N : Subgroup (↥B ⧸ W) := V'.map (QuotientGroup.mk' W) with hN
  have hNn : N.Normal := hV'n.map _ (QuotientGroup.mk'_surjective W)
  have hNp : IsPGroup 2 N := hV'p.map _
  have hNZ : N ≤ Subgroup.center (↥B ⧸ W) := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hNn with h | h
    · exfalso
      apply not_isPGroup_two_of_quasisimple hq
      rw [h] at hNp
      exact hNp.of_equiv Subgroup.topEquiv
    · exact h
  have hcent : ∀ v ∈ V, ∀ b ∈ B, b * v = v * b := by
    intro v hv b hb
    set v' : ↥B := ⟨v, hVB hv⟩
    set b' : ↥B := ⟨b, hb⟩
    have hv'V : v' ∈ V' := Subgroup.mem_subgroupOf.mpr hv
    have hmk : (QuotientGroup.mk' W v') ∈ Subgroup.center (↥B ⧸ W) := hNZ ⟨v', hv'V, rfl⟩
    set c : ↥B := v'⁻¹ * b'⁻¹ * v' * b' with hcdef
    have hcW : c ∈ W := by
      rw [← QuotientGroup.eq_one_iff, hcdef]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h1 := (Subgroup.mem_center_iff.mp hmk) (QuotientGroup.mk' W b')
      simp only [QuotientGroup.mk'_apply] at h1
      rw [mul_assoc _ (v' : ↥B ⧸ W) (b' : ↥B ⧸ W), ← h1]
      group
    have hcV : c ∈ V' := by
      have hconj : b'⁻¹ * v' * b' ∈ V' := by
        have := hV'n.conj_mem v' hv'V b'⁻¹
        simpa using this
      have := V'.mul_mem (V'.inv_mem hv'V) hconj
      rw [hcdef]
      simpa [mul_assoc] using this
    have hc2 : c ^ 2 = 1 := by
      have := hV.2 _ (Subgroup.mem_subgroupOf.mp hcV)
      exact Subtype.ext (by simpa using this)
    have hcp : c ^ p = 1 := hW c hcW
    have hc1 : c = 1 := by
      have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
      have h2 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
      have h3 : orderOf c ∣ Nat.gcd 2 p := Nat.dvd_gcd h1 h2
      rw [(Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)] at h3
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    have : b' * v' = v' * b' := by
      have h := hc1
      rw [hcdef] at h
      calc b' * v' = b' * v' * (v'⁻¹ * b'⁻¹ * v' * b') := by rw [h, mul_one]
        _ = v' * b' := by group
    exact congrArg Subtype.val this
  have hle : V ≤ Subgroup.centralizer (B : Set X) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hcent v hv b hb
  have hbot : ⁅V, B⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hle
  exact hV1 (hcomm ▸ hbot)

theorem false_of_quasisimple {B V : Subgroup X} (hq : CFSG.IsQuasisimple ↥B) (hVB : V ≤ B)
    (hV : IsElemAbelian 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set X)) (hcomm : ⁅V, B⁆ = V)
    (hV1 : V ≠ ⊥) : False :=
  false_of_quasisimple_quotient (⊥ : Subgroup ↥B) Nat.prime_three (by norm_num)
    (fun w hw => by rw [Subgroup.mem_bot] at hw; rw [hw, one_pow])
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientBot).symm hq)
    hVB hV hBV hcomm hV1

theorem not_isPGroup_of_perfect {B : Subgroup X} (hB : ⁅B, B⁆ = B) (hB1 : B ≠ ⊥) :
    ¬ IsPGroup 2 B := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent B := h2.isNilpotent
  have hs : Group.IsSolvable B := inferInstance
  have h1 := (isSolvable_iff_perfectCore_eq_bot B).1 hs
  rw [perfectCore_eq_self_of_perfect hB] at h1
  exact hB1 h1

theorem false_of_simple {T B V : Subgroup X} (hB : B ∈ lFamily T) (hs : IsSimpleGroup ↥B)
    (hVB : V ≤ B) (hV : IsElemAbelian 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set X))
    (hcomm : ⁅V, B⁆ = V) (hV1 : V ≠ ⊥) (hc : pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X)) :
    False := by
  have hBc : quasithinIsCComponent B (B ⊔ T) := hB
  have hnp : ¬ IsPGroup 2 ↥B := not_isPGroup_of_perfect hBc.2.1 hBc.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : CFSG.pCore 2 ↥B = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥B) with h | h
    · exact h
    · exfalso
      apply hnp
      have := CFSG.pCore_isPGroup (p := 2) (G := ↥B)
      rw [h] at this
      exact IsPGroup.of_equiv this Subgroup.topEquiv
  exact false_of_pCore_eq_bot h hVB hV hBV hcomm hV1 hc

theorem center_map_normal {Y : Type*} [Group Y] {W : Subgroup Y} [W.Normal] :
    ((Subgroup.center ↥W).map W.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hx
  have hmap := Subgroup.characteristic_iff_map_eq.mp (inferInstance :
    (Subgroup.center ↥W).Characteristic) (MulAut.conjNormal g : MulAut ↥W)
  have hc' : (MulAut.conjNormal g : MulAut ↥W) c ∈ Subgroup.center ↥W := by
    rw [← hmap]
    exact ⟨c, hc, rfl⟩
  refine ⟨_, hc', ?_⟩
  rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]

theorem le_center_of_card_two {Y : Type*} [Group Y] {M : Subgroup Y} (hM : M.Normal)
    (h2 : Nat.card M = 2) : M ≤ Subgroup.center Y := by
  intro m hm
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hm1 : m = 1
  · rw [hm1, one_mul, mul_one]
  · have hc : g * m * g⁻¹ ∈ M := hM.conj_mem m hm g
    have hc1 : g * m * g⁻¹ ≠ 1 := by
      intro h
      apply hm1
      calc m = g⁻¹ * (g * m * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hcard : ∀ a b : M, a ≠ 1 → b ≠ 1 → a = b := by
      intro a b ha hb
      obtain ⟨x, y, hxy, hu⟩ := Nat.card_eq_two_iff.mp h2
      have mem : ∀ c : M, c = x ∨ c = y := fun c => by
        have : c ∈ ({x, y} : Set M) := hu ▸ Set.mem_univ c
        simpa using this
      rcases mem 1 with h1 | h1 <;> rcases mem a with h3 | h3 <;> rcases mem b with h4 | h4 <;>
        first
        | exact h3.trans h4.symm
        | exact absurd (h3.trans h1.symm) ha
        | exact absurd (h4.trans h1.symm) hb
    have := hcard ⟨g * m * g⁻¹, hc⟩ ⟨m, hm⟩ (fun h => hc1 (congrArg Subtype.val h))
      (fun h => hm1 (congrArg Subtype.val h))
    have h5 : g * m * g⁻¹ = m := congrArg Subtype.val this
    calc g * m = g * m * g⁻¹ * g := by group
      _ = m * g := by rw [h5]

theorem false_of_center_card_two {B V : Subgroup X} (W : Subgroup ↥B) [W.Normal]
    (hW2 : IsPGroup 2 W) (hZ : Nat.card (Subgroup.center ↥W) = 2)
    (hs : IsSimpleGroup (↥B ⧸ W)) (hnp : ¬ IsPGroup 2 (↥B ⧸ W)) (hVB : V ≤ B)
    (hV : IsElemAbelian 2 V) (hBV : B ≤ Subgroup.normalizer (V : Set X)) (hcomm : ⁅V, B⁆ = V)
    (hV1 : V ≠ ⊥) (hc : pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWle : W ≤ CFSG.pCore 2 ↥B :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup inferInstance hW2
  have hle : CFSG.pCore 2 ↥B ≤ W := by
    have hn : ((CFSG.pCore 2 ↥B).map (QuotientGroup.mk' W)).Normal :=
      (inferInstance : (CFSG.pCore 2 ↥B).Normal).map _ (QuotientGroup.mk'_surjective W)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥B).map
      (QuotientGroup.mk' W)) with h | h
    · intro x hx
      have : (QuotientGroup.mk' W x) ∈ (CFSG.pCore 2 ↥B).map (QuotientGroup.mk' W) := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · exfalso
      apply hnp
      have hp : IsPGroup 2 ((CFSG.pCore 2 ↥B).map (QuotientGroup.mk' W)) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).map _
      rw [h] at hp
      exact hp.of_equiv Subgroup.topEquiv
  have heq : CFSG.pCore 2 ↥B = W := le_antisymm hle hWle
  have hZn := center_map_normal (W := W)
  have hZc : (Subgroup.center ↥W).map W.subtype ≤ Subgroup.center ↥B :=
    le_center_of_card_two hZn (by
      rw [Subgroup.card_map_of_injective W.subtype_injective, hZ])
  refine false_of_V hVB hV hBV hcomm hV1 hc fun v hv hvc _ b hb => ?_
  rw [pCoreOf_eq_map, heq] at hv hvc
  obtain ⟨v', hv'W, rfl⟩ := hv
  have hv'Z : v' ∈ (Subgroup.center ↥W).map W.subtype := by
    refine ⟨⟨v', hv'W⟩, Subgroup.mem_center_iff.mpr fun u => ?_, rfl⟩
    have := hvc _ ⟨u, u.2, rfl⟩
    exact Subtype.ext (Subtype.ext (by simpa using this))
  have := (Subgroup.mem_center_iff.mp (hZc hv'Z)) ⟨b, hb⟩
  exact congrArg Subtype.val this

end CFSG.Quasithin.Vol2.Ch10.A312A
