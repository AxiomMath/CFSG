
module

public import CFSG.Sporadic.Fi24.OctadAction
public import CFSG.Sporadic.FischerOddCore.CentralExt
public import CFSG.Sporadic.FischerOddCore.Fi24WitCheckInputs

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24 (R J M MR tR D24 jR cls)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem fi24_table_fix_iff
    {T : Table} {r : R} (hT : Rep 306936 T r) (k : Fin 306936) :
    ap T k.val = k.val ↔ r * cls k * r⁻¹ = cls k := by
  rw [hT k.val k.isLt, idx_of_lt r k.isLt, ← Fi24.cls_smul_R]
  constructor
  · intro h
    congr 1
    exact Fin.ext h
  · intro h
    exact congrArg Fin.val (Fi24.cls_injective h)

theorem card_fixed_D24
    (l : List (Table × R)) (hl : ∀ p ∈ l, Rep 306936 p.1 p.2) :
    Nat.card {x : D24 // ∀ p ∈ l, p.2 * x * p.2⁻¹ = x} =
      (List.range 306936).countP fun i => l.all fun p => ap p.1 i == i := by
  classical
  have e1 : {k : Fin 306936 // ∀ p ∈ l, ap p.1 k.val = k.val} ≃
      {x : D24 // ∀ p ∈ l, p.2 * x * p.2⁻¹ = x} :=
    Equiv.subtypeEquiv Fi24.clsEquiv fun k => by
      simp only [Fi24.clsEquiv_apply]
      exact forall₂_congr fun p hp => fi24_table_fix_iff (hl p hp) k
  have e2 : {k : Fin 306936 // ∀ p ∈ l, ap p.1 k.val = k.val} ≃
      ((Finset.range 306936).filter fun i => ∀ p ∈ l, ap p.1 i = i) :=
    { toFun := fun k => ⟨k.1.1, Finset.mem_filter.2 ⟨Finset.mem_range.2 k.1.2, k.2⟩⟩
      invFun := fun i => ⟨⟨i.1, Finset.mem_range.1 (Finset.mem_filter.1 i.2).1⟩,
        (Finset.mem_filter.1 i.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e1, Nat.card_congr e2, Nat.card_eq_finsetCard,
    ← Nat.count_eq_card_filter_range]
  unfold Nat.count
  exact List.countP_congr fun i _ => by simp [List.all_eq_true]

@[expose] def fi23ToR :
    CFSG.Sporadic.Fi23.J →* R :=
  jR.comp (M.subtype.comp
    (@MulEquiv.toMonoidHom CFSG.Sporadic.Fi23.J M inferInstance inferInstance
      Fi24.fi23EquivM.symm))

theorem fi23ToR_apply
    (u : CFSG.Sporadic.Fi23.J) :
    fi23ToR u = jR (Fi24.fi23EquivM.symm u : J) := rfl

theorem fi23ToR_mem
    (u : CFSG.Sporadic.Fi23.J) : fi23ToR u ∈ MR :=
  ⟨_, (Fi24.fi23EquivM.symm u).2, rfl⟩

theorem fi23ToR_injective :
    Function.Injective fi23ToR := by
  intro u v h
  rw [fi23ToR_apply, fi23ToR_apply] at h
  exact Fi24.fi23EquivM.symm.injective (Subtype.ext (Fi24.jR_injective h))

theorem exists_fi23ToR
    {m : R} (hm : m ∈ MR) : ∃ u, fi23ToR u = m := by
  obtain ⟨g, hg, rfl⟩ := hm
  exact ⟨Fi24.fi23EquivM ⟨g, hg⟩, by rw [fi23ToR_apply, MulEquiv.symm_apply_apply]⟩

theorem fi23ToR_a :
    fi23ToR CFSG.Sporadic.Fi23.a = jR (Fi24.mGen0 : J) := by
  rw [fi23ToR_apply, ← Fi24.fi23EquivM_mGen0, MulEquiv.symm_apply_apply]

theorem fi23ToR_b :
    fi23ToR CFSG.Sporadic.Fi23.b = jR (Fi24.mGen1 : J) := by
  rw [fi23ToR_apply, ← Fi24.fi23EquivM_mGen1, MulEquiv.symm_apply_apply]

abbrev fi24M0T : Table :=
  wordT Fi24.Native.nPts (Fi24.Native.letterJ Fi24.letters) Fi24.Native.localWords[0]!

abbrev fi24M1T : Table :=
  wordT Fi24.Native.nPts (Fi24.Native.letterJ Fi24.letters) Fi24.Native.localWords[1]!

theorem rep_fi24M0T :
    Rep 306936 fi24M0T (fi23ToR CFSG.Sporadic.Fi23.a) := by
  rw [fi23ToR_a]
  exact Fi24.rep_jR (Rep.wordT (n := 306936) (by norm_num) _ fun z hz =>
    Fi24.rep_letterJ (Fi24.localWords_letters (by norm_num) z hz).2)

theorem rep_fi24M1T :
    Rep 306936 fi24M1T (fi23ToR CFSG.Sporadic.Fi23.b) := by
  rw [fi23ToR_b]
  exact Fi24.rep_jR (Rep.wordT (n := 306936) (by norm_num) _ fun z hz =>
    Fi24.rep_letterJ (Fi24.localWords_letters (by norm_num) z hz).2)

theorem rep_fi24GenT
    {A Ai B Bi : Table}
    (hA : Rep 306936 A (fi23ToR CFSG.Sporadic.Fi23.a))
    (hAi : Rep 306936 Ai (fi23ToR CFSG.Sporadic.Fi23.a)⁻¹)
    (hB : Rep 306936 B (fi23ToR CFSG.Sporadic.Fi23.b))
    (hBi : Rep 306936 Bi (fi23ToR CFSG.Sporadic.Fi23.b)⁻¹) (z : ℤ) :
    Rep 306936 (fi24GenT A Ai B Bi z) (fi23ToR (CFSG.Sporadic.Fi23.genG z)) := by
  unfold fi24GenT CFSG.Sporadic.Fi23.genG
  by_cases h1 : z = 1
  · rw [ite_eq_left h1, ite_eq_left h1]
    exact hA
  by_cases h2 : z = -1
  · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2, map_inv]
    exact hAi
  by_cases h3 : z = 2
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, ite_eq_right h1, ite_eq_right h2,
      ite_eq_left h3]
    exact hB
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h1, ite_eq_right h2,
      ite_eq_right h3, map_inv]
    exact hBi

theorem rep_fi24WordT
    {A Ai B Bi : Table}
    (hA : Rep 306936 A (fi23ToR CFSG.Sporadic.Fi23.a))
    (hAi : Rep 306936 Ai (fi23ToR CFSG.Sporadic.Fi23.a)⁻¹)
    (hB : Rep 306936 B (fi23ToR CFSG.Sporadic.Fi23.b))
    (hBi : Rep 306936 Bi (fi23ToR CFSG.Sporadic.Fi23.b)⁻¹) (w : List ℤ) :
    Rep 306936 (wordT Fi24.Native.nPts (fi24GenT A Ai B Bi) w)
      (fi23ToR (wordG CFSG.Sporadic.Fi23.genG w)) := by
  have h := Rep.wordT (n := 306936) (G := R) (by norm_num)
    (gensG := fi23ToR ∘ CFSG.Sporadic.Fi23.genG)
    w fun z _ => rep_fi24GenT hA hAi hB hBi z
  have e : wordG (fi23ToR ∘ CFSG.Sporadic.Fi23.genG) w =
      fi23ToR (wordG CFSG.Sporadic.Fi23.genG w) := by
    unfold wordG
    rw [map_list_prod, List.map_map]
  rwa [e] at h

theorem oddCore_eq_bot_of_normal_le {G : Type*} [Group G] [Finite G] {K L : Subgroup G}
    (hKL : K ≤ L) (hK : (K.subgroupOf L).Normal) (hL : CFSG.oddCore ↥L = ⊥) :
    CFSG.oddCore ↥K = ⊥ := by
  set N := (CFSG.oddCore ↥K).map K.subtype
  have hNK : N ≤ K := Subgroup.map_subtype_le _
  have hnormal : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk, hkn⟩ := hn
    have hconj : ∀ x ∈ K, (l : G) * x * (l : G)⁻¹ ∈ K := fun x hx => by
      have := hK.conj_mem ⟨x, hKL hx⟩ (Subgroup.mem_subgroupOf.2 hx) l
      rwa [Subgroup.mem_subgroupOf] at this
    have hconj' : ∀ x ∈ K, (l : G)⁻¹ * x * (l : G) ∈ K := fun x hx => by
      have := hK.conj_mem ⟨x, hKL hx⟩ (Subgroup.mem_subgroupOf.2 hx) l⁻¹
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    let φ : K ≃* K :=
      { toFun := fun x => ⟨l * x * (l : G)⁻¹, hconj x x.2⟩
        invFun := fun x => ⟨(l : G)⁻¹ * x * l, hconj' x x.2⟩
        left_inv := fun x => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    refine ⟨φ k, map_oddCore_le φ ⟨k, hk, rfl⟩, ?_⟩
    change (l : G) * (k : G) * (l : G)⁻¹ = ((l * n * l⁻¹ : L) : G)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hkn]
    rfl
  have hodd : Odd (Nat.card (N.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNK.trans hKL)).toEquiv,
      Nat.card_congr ((CFSG.oddCore ↥K).equivMapOfInjective _ K.subtype_injective).toEquiv.symm]
    exact odd_card_oddCore
  have hle := le_oddCore_of_normal hnormal hodd
  rw [hL, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
  have hbot : N = ⊥ := disjoint_self.1 (hle.mono_right (hNK.trans hKL))
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 hbot

end CFSG.Sporadic.FischerOddCore
