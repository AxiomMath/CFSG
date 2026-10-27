module

public import CFSG.Quasithin.Recognition.SzVBOddL24Facts

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type*} [Group G]

structure A5Facts (P T V : Subgroup G) (z : G) : Prop where
  klein : KleinData P V z
  l24 : L24Facts P T V
  abel : IsElemAbelian 2 (conjClosure V P)
  ker_le : ∀ x : ↥P, x ∈ kerAct P V → (x : G) ∈ pCoreOf 2 P
  inv_one_fixed : ∀ x : ↥P, x * x = 1 → x ∉ kerAct P V →
    ∃ ω : ConjSet P V, x • ω = ω ∧ ∀ U : ConjSet P V, x • U = U → U = ω
  T_sq : ∀ x : ↥P, (x : G) ∈ T → x * x ∈ kerAct P V
  perfect : P ≤ ⁅P, P⁆ ⊔ pCoreOf 2 P

@[expose] def secCentr (Q V : Subgroup G) : Subgroup G where
  carrier := {w | w ∈ Subgroup.normalizer (V : Set G) ∧ ∀ q ∈ Q, q * w * q⁻¹ * w⁻¹ ∈ V}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun q hq => ?_⟩
    have e : q * (a * b) * q⁻¹ * (a * b)⁻¹ =
        (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact V.mul_mem (ha' q hq) ((Subgroup.mem_normalizer_iff.mp ha _).mp (hb' q hq))
  one_mem' := ⟨Subgroup.one_mem _, fun q _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, fun q hq => ?_⟩
    have e : q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ = a⁻¹ * (q * a * q⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) _).mp (V.inv_mem (ha' q hq))

theorem mem_secCentr {Q V : Subgroup G} {w : G} :
    w ∈ secCentr Q V ↔ w ∈ Subgroup.normalizer (V : Set G) ∧
      ∀ q ∈ Q, q * w * q⁻¹ * w⁻¹ ∈ V := Iff.rfl

theorem conjSub_secCentr (g : G) (Q V : Subgroup G) :
    conjSub g (secCentr Q V) = secCentr (conjSub g Q) (conjSub g V) := by
  ext x
  rw [mem_conjSub, mem_secCentr, mem_secCentr]
  constructor
  · rintro ⟨hN, h⟩
    refine ⟨?_, fun q hq => ?_⟩
    · rw [conjSub_normalizer, mem_conjSub]
      exact hN
    · rw [mem_conjSub] at hq ⊢
      have := h _ hq
      have e : g⁻¹ * (q * x * q⁻¹ * x⁻¹) * g =
          (g⁻¹ * q * g) * (g⁻¹ * x * g) * (g⁻¹ * q * g)⁻¹ * (g⁻¹ * x * g)⁻¹ := by group
      rw [e]
      exact this
  · rintro ⟨hN, h⟩
    refine ⟨?_, fun q hq => ?_⟩
    · rw [conjSub_normalizer, mem_conjSub] at hN
      exact hN
    · have := h (g * q * g⁻¹) (mul_mem_conjSub hq)
      rw [mem_conjSub] at this
      have e : g⁻¹ * (g * q * g⁻¹ * x * (g * q * g⁻¹)⁻¹ * x⁻¹) * g =
          q * (g⁻¹ * x * g) * q⁻¹ * (g⁻¹ * x * g)⁻¹ := by group
      rwa [e] at this

@[expose] def A5FixedW (P V : Subgroup G) (z : G) : Prop :=
  ∃ w ∈ conjClosure V P, w ∉ Subgroup.zpowers z ∧
    ∀ g ∈ P, g * w * g⁻¹ * w⁻¹ ∈ Subgroup.zpowers z

theorem exists_tDataG_mem {P V : Subgroup G} {z : G} (hK : KleinData P V z) :
    ∃ t : ConjSet P V → G, TDataG P (conjClosure V P) t z ∧
      ∀ U : ConjSet P V, t U ∈ U.1 ∧ t U ≠ 1 ∧ t U ≠ z := by
  have hex : ∀ U : ConjSet P V, ∃ t, t ∈ U.1 ∧ t ≠ 1 ∧ t ≠ z := fun U => by
    obtain ⟨t, ht, ht1, htz⟩ := exists_klein_ne z (hK.card_point U)
    exact ⟨t, ht, ht1, htz⟩
  choose t htU ht1 htz using hex
  have htt : ∀ U : ConjSet P V, t U * t U = 1 := fun U => by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one (hK.isElemAbelian_point U) (htU U)
  have hcases : ∀ (U : ConjSet P V) {a : G}, a ∈ U.1 → a = 1 ∨ a = z ∨ a = t U ∨ a = t U * z :=
    fun U a ha => klein_cases (hK.isElemAbelian_point U) (hK.card_point U) (hK.z_mem_point U)
      hK.z_ne_one (htU U) (ht1 U) (htz U) ha
  have hUU' : ∀ (U U' : ConjSet P V) (w : G), w ∈ U.1 → w ∈ U'.1 → w ≠ 1 → w ≠ z → U = U' :=
    fun U U' w hw hw' hw1 hwz => Subtype.ext
      (klein_eq_of_mem (hK.isElemAbelian_point U) (hK.card_point U) (hK.card_point U')
        (hK.z_mem_point U) (hK.z_mem_point U') hK.z_ne_one hw hw' hw1 hwz)
  have hgen : conjClosure V P = Subgroup.closure (insert z (Set.range t)) := by
    apply le_antisymm
    · refine conjClosure_le fun h hh v hv => ?_
      let U : ConjSet P V := ⟨conjSub h V, h, hh, rfl⟩
      have hmem : h * v * h⁻¹ ∈ U.1 := mul_mem_conjSub hv
      have hz : z ∈ Subgroup.closure (insert z (Set.range t)) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have htU' : t U ∈ Subgroup.closure (insert z (Set.range t)) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨U, rfl⟩)
      rcases hcases U hmem with e | e | e | e
      · rw [e]
        exact Subgroup.one_mem _
      · rw [e]
        exact hz
      · rw [e]
        exact htU'
      · rw [e]
        exact Subgroup.mul_mem _ htU' hz
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with h | ⟨U, hU⟩
      · rw [h]
        exact le_conjClosure V P hK.z_mem
      · rw [← hU]
        exact ConjSet.val_le_conjClosure U (htU U)
  have hact : ∀ (x : ↥P) (U : ConjSet P V), (x : G) * t U * (x : G)⁻¹ = t (x • U) ∨
      (x : G) * t U * (x : G)⁻¹ = t (x • U) * z := by
    intro x U
    have hxP : (x : G) ∈ P := x.2
    have hback : ∀ b : G, (x : G) * t U * (x : G)⁻¹ = b → t U = (x : G)⁻¹ * b * (x : G) :=
      fun b hb => by
        rw [← hb]
        group
    have hmem : (x : G) * t U * (x : G)⁻¹ ∈ (x • U : ConjSet P V).1 := by
      rw [ConjSet.smul_val]
      exact mul_mem_conjSub (htU U)
    have hne1 : (x : G) * t U * (x : G)⁻¹ ≠ 1 := fun h =>
      ht1 U ((hback 1 h).trans (by group))
    have hnez : (x : G) * t U * (x : G)⁻¹ ≠ z := fun h => by
      refine htz U ((hback z h).trans ?_)
      have h2 := hK.conj_z (P.inv_mem hxP)
      rwa [inv_inv] at h2
    rcases hcases (x • U) hmem with e | e | e | e
    · exact absurd e hne1
    · exact absurd e hnez
    · exact Or.inl e
    · exact Or.inr e
  have hdist : ∀ U U' : ConjSet P V, U ≠ U' → t U * t U' ≠ 1 ∧ t U * t U' ≠ z := by
    intro U U' hne
    constructor
    · intro h
      have h' : t U = t U' := mul_right_cancel (h.trans (htt U').symm)
      refine hne (hUU' U U' (t U) (htU U) ?_ (ht1 U) (htz U))
      rw [h']
      exact htU U'
    · intro h
      have h' : t U' = t U * z := by
        calc t U' = t U * (t U * t U') := by rw [← mul_assoc, htt U, one_mul]
          _ = t U * z := by rw [h]
      refine hne (hUU' U U' (t U') ?_ (htU U') (ht1 U') (htz U'))
      rw [h']
      exact U.1.mul_mem (htU U) (hK.z_mem_point U)
  exact ⟨t, { z_mem := le_conjClosure V P hK.z_mem
              t_mem := fun U => ConjSet.val_le_conjClosure U (htU U)
              gen := hgen
              t_sq := htt
              z_sq := hK.z_mul_self
              z_ne_one := hK.z_ne_one
              z_cent := hK.z_cent
              act := hact
              distinct := hdist }, fun U => ⟨htU U, ht1 U, htz U⟩⟩

end CFSG.Quasithin.SzVB
