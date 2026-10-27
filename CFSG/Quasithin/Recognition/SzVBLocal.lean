module

public import CFSG.Quasithin.Background.Ordering
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

@[expose] def ConjSet (P V : Subgroup G) : Type _ :=
  {U : Subgroup G // ∃ x ∈ P, U = conjSub x V}

namespace ConjSet

instance instMulAction (P V : Subgroup G) : MulAction ↥P (ConjSet P V) where
  smul x U := ⟨conjSub (x : G) U.1, by
    obtain ⟨y, hy, hU⟩ := U.2
    exact ⟨(x : G) * y, P.mul_mem x.2 hy, by rw [hU, conjSub_mul]⟩⟩
  one_smul U := by
    apply Subtype.ext
    exact conjSub_one U.1
  mul_smul x y U := by
    apply Subtype.ext
    exact conjSub_mul (x : G) (y : G) U.1

theorem smul_val (P V : Subgroup G) (x : ↥P) (U : ConjSet P V) :
    (x • U : ConjSet P V).1 = conjSub (x : G) U.1 := rfl

@[expose] def base (P V : Subgroup G) : ConjSet P V :=
  ⟨V, 1, P.one_mem, (conjSub_one V).symm⟩

@[expose] def mk (P V : Subgroup G) (x : ↥P) : ConjSet P V :=
  (x • base P V : ConjSet P V)

instance instFinite [Finite G] (P V : Subgroup G) : Finite (ConjSet P V) :=
  Finite.of_surjective (fun x : ↥P => mk P V x) fun U => by
    obtain ⟨x, hx, hU⟩ := U.2
    exact ⟨⟨x, hx⟩, Subtype.ext hU.symm⟩

theorem val_le_conjClosure {P V : Subgroup G} (U : ConjSet P V) : U.1 ≤ conjClosure V P := by
  obtain ⟨x, hx, hU⟩ := U.2
  intro a ha
  rw [hU, mem_conjSub] at ha
  have h := mem_conjClosure hx ha
  have e : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
  rwa [e] at h

end ConjSet

structure KleinData (P V : Subgroup G) (z : G) : Prop where
  V_le : V ≤ P
  elemAbelian : IsElemAbelian 2 V
  card_eq : Nat.card ↥V = 4
  z_mem : z ∈ V
  z_ne_one : z ≠ 1
  z_cent : ∀ x ∈ P, x * z = z * x

structure TDataG (P W : Subgroup G) {Ω : Type*} [MulAction ↥P Ω] (t : Ω → G) (z : G) :
    Prop where
  z_mem : z ∈ W
  t_mem : ∀ a, t a ∈ W
  gen : W = Subgroup.closure (insert z (Set.range t))
  t_sq : ∀ a, t a * t a = 1
  z_sq : z * z = 1
  z_ne_one : z ≠ 1
  z_cent : ∀ x ∈ P, x * z = z * x
  act : ∀ (x : ↥P) (a : Ω), (x : G) * t a * (x : G)⁻¹ = t (x • a) ∨
    (x : G) * t a * (x : G)⁻¹ = t (x • a) * z
  distinct : ∀ a b : Ω, a ≠ b → t a * t b ≠ 1 ∧ t a * t b ≠ z

theorem klein_cases {U : Subgroup G} {z t a : G} (hU : IsElemAbelian 2 U)
    (hcard : Nat.card ↥U = 4) (hz : z ∈ U) (hz1 : z ≠ 1) (ht : t ∈ U) (ht1 : t ≠ 1)
    (htz : t ≠ z) (ha : a ∈ U) : a = 1 ∨ a = z ∨ a = t ∨ a = t * z := by
  classical
  have hzz : z * z = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hU hz
  have htz1 : t * z ≠ 1 := by
    intro h
    apply htz
    rw [eq_inv_of_mul_eq_one_left h]
    exact inv_eq_of_mul_eq_one_right hzz
  have hnot1 : (1 : G) ∉ ({z, t, t * z} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hz1 h.symm, fun h => ht1 h.symm, fun h => htz1 h.symm⟩
  have hnotz : z ∉ ({t, t * z} : Finset G) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => htz h.symm, fun h => ht1 (mul_eq_right.mp h.symm)⟩
  have hnott : t ∉ ({t * z} : Finset G) := by
    simp only [Finset.mem_singleton]
    exact fun h => hz1 (mul_eq_left.mp h.symm)
  have hS : ({1, z, t, t * z} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnotz,
      Finset.card_insert_of_notMem hnott, Finset.card_singleton]
  have hsub : (({1, z, t, t * z} : Finset G) : Set G) ⊆ (U : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact U.one_mem
    · rw [h]; exact hz
    · rw [h]; exact ht
    · rw [h]; exact U.mul_mem ht hz
  have hUcard : (U : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hfin : (U : Set G).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have heq : (({1, z, t, t * z} : Finset G) : Set G) = (U : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [Set.ncard_coe_finset, hS, hUcard])) hfin
  have hmem : a ∈ (({1, z, t, t * z} : Finset G) : Set G) := by
    rw [heq]
    exact ha
  simpa using hmem

theorem exists_klein_ne {U : Subgroup G} (z : G) (hcard : Nat.card ↥U = 4) :
    ∃ t ∈ U, t ≠ 1 ∧ t ≠ z := by
  by_contra hcon
  have hsub : (U : Set G) ⊆ {1, z} := by
    intro x hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    · refine Or.inr ?_
      by_contra hxz
      exact hcon ⟨x, hx, h1, hxz⟩
  have hle : (U : Set G).ncard ≤ ({1, z} : Set G).ncard := Set.ncard_le_ncard hsub
  have h2 : ({1, z} : Set G).ncard ≤ 2 := by
    calc ({1, z} : Set G).ncard ≤ ({z} : Set G).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hUcard : (U : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  omega

theorem klein_eq_of_mem {U U' : Subgroup G} {z t : G} (hU : IsElemAbelian 2 U)
    (hcard : Nat.card ↥U = 4) (hcard' : Nat.card ↥U' = 4) (hz : z ∈ U) (hz' : z ∈ U')
    (hz1 : z ≠ 1) (ht : t ∈ U) (ht' : t ∈ U') (ht1 : t ≠ 1) (htz : t ≠ z) : U = U' := by
  have hle : U ≤ U' := by
    intro a ha
    rcases klein_cases hU hcard hz hz1 ht ht1 htz ha with h | h | h | h
    · rw [h]; exact U'.one_mem
    · rw [h]; exact hz'
    · rw [h]; exact ht'
    · rw [h]; exact U'.mul_mem ht' hz'
  have : Finite ↥U' := Nat.finite_of_card_ne_zero (by rw [hcard']; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hle (hcard'.trans hcard.symm).le

theorem commutator_mem_klein {U : Subgroup G} {z c : G} (hU : IsElemAbelian 2 U)
    (hcard : Nat.card ↥U = 4) (hz : z ∈ U) (hz1 : z ≠ 1) (hcz : c * z = z * c)
    (hcU : conjSub c U = U) {a : G} (ha : a ∈ U) :
    c * a * c⁻¹ * a⁻¹ = 1 ∨ c * a * c⁻¹ * a⁻¹ = z := by
  have hca : c * a * c⁻¹ ∈ U := by
    have h := mul_mem_conjSub (g := c) ha
    rwa [hcU] at h
  have hcz' : c * z * c⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcz
  have hback : ∀ b : G, c * a * c⁻¹ = b → a = c⁻¹ * b * c := fun b hb => by
    rw [← hb]
    group
  by_cases h1 : a = 1
  · left
    rw [h1]
    group
  by_cases hz' : a = z
  · left
    rw [hz', hcz']
    exact mul_inv_cancel z
  rcases klein_cases hU hcard hz hz1 ha h1 hz' hca with h | h | h | h
  · exact absurd ((hback 1 h).trans (by group)) h1
  · refine absurd ((hback z h).trans ?_) hz'
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := mul_assoc _ _ _
      _ = c⁻¹ * (c * z) := by rw [hcz]
      _ = z := inv_mul_cancel_left c z
  · left
    rw [h]
    exact mul_inv_cancel a
  · right
    rw [h]
    exact mul_inv_eq_iff_eq_mul.mpr (F7.isElemAbelian_comm hU ha hz)

theorem commutator_mem_closure {P : Subgroup G} {z c : G} (hzz : z * z = 1)
    (hcent : ∀ x ∈ P, x * z = z * x) {s : Set G} (hsP : s ⊆ P)
    (hs : ∀ a ∈ s, c * a * c⁻¹ * a⁻¹ = 1 ∨ c * a * c⁻¹ * a⁻¹ = z) {a : G}
    (ha : a ∈ Subgroup.closure s) : c * a * c⁻¹ * a⁻¹ = 1 ∨ c * a * c⁻¹ * a⁻¹ = z := by
  have hconj : ∀ x ∈ P, x * z * x⁻¹ = z := fun x hx => mul_inv_eq_iff_eq_mul.mpr (hcent x hx)
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  suffices h : a ∈ P ∧ (c * a * c⁻¹ * a⁻¹ = 1 ∨ c * a * c⁻¹ * a⁻¹ = z) by exact h.2
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact ⟨hsP hx, hs x hx⟩
  | one => exact ⟨P.one_mem, Or.inl (by group)⟩
  | mul x y _ _ ihx ihy =>
    refine ⟨P.mul_mem ihx.1 ihy.1, ?_⟩
    have e : c * (x * y) * c⁻¹ * (x * y)⁻¹ =
        (c * x * c⁻¹ * x⁻¹) * (x * (c * y * c⁻¹ * y⁻¹) * x⁻¹) := by group
    have e2 : x * (c * y * c⁻¹ * y⁻¹) * x⁻¹ = c * y * c⁻¹ * y⁻¹ := by
      rcases ihy.2 with h | h
      · rw [h]
        group
      · rw [h]
        exact hconj x ihx.1
    rw [e, e2]
    rcases ihx.2 with h | h <;> rcases ihy.2 with h' | h' <;> rw [h, h']
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul z)
    · exact Or.inr (mul_one z)
    · exact Or.inl hzz
  | inv x _ ih =>
    refine ⟨P.inv_mem ih.1, ?_⟩
    have e : c * x⁻¹ * c⁻¹ * x⁻¹⁻¹ = x⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * x := by group
    rcases ih.2 with h | h
    · left
      rw [e, h]
      group
    · right
      rw [e, h, hzi]
      have h2 := hconj x⁻¹ (P.inv_mem ih.1)
      rwa [inv_inv] at h2

namespace KleinData

variable {P V : Subgroup G} {z : G}

theorem conj_z (hK : KleinData P V z) {x : G} (hx : x ∈ P) : x * z * x⁻¹ = z :=
  mul_inv_eq_iff_eq_mul.mpr (hK.z_cent x hx)

theorem z_mul_self (hK : KleinData P V z) : z * z = 1 := by
  rw [← pow_two]
  exact F7.isElemAbelian_pow_eq_one hK.elemAbelian hK.z_mem

theorem isElemAbelian_point (hK : KleinData P V z) (U : ConjSet P V) : IsElemAbelian 2 U.1 := by
  obtain ⟨x, -, hU⟩ := U.2
  rw [hU]
  exact F7.isElemAbelian_conjSub hK.elemAbelian

theorem card_point (hK : KleinData P V z) (U : ConjSet P V) : Nat.card ↥U.1 = 4 := by
  obtain ⟨x, -, hU⟩ := U.2
  have h : Nat.card ↥(conjSub x V) = Nat.card ↥V :=
    Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
  rw [hU, h]
  exact hK.card_eq

theorem z_mem_point (hK : KleinData P V z) (U : ConjSet P V) : z ∈ U.1 := by
  obtain ⟨x, hx, hU⟩ := U.2
  rw [hU]
  have h := mul_mem_conjSub (g := x) hK.z_mem
  rwa [hK.conj_z hx] at h

end KleinData

theorem exists_tDataG {P V : Subgroup G} {z : G} (hK : KleinData P V z) :
    ∃ t : ConjSet P V → G, TDataG P (conjClosure V P) t z := by
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
              distinct := hdist }⟩

theorem commutator_mem_of_fixes {P V : Subgroup G} {z : G} (hK : KleinData P V z) {c : G}
    (hc : c ∈ P) (hfix : ∀ U : ConjSet P V, (⟨c, hc⟩ : ↥P) • U = U) {a : G}
    (ha : a ∈ conjClosure V P) : c * a * c⁻¹ * a⁻¹ = 1 ∨ c * a * c⁻¹ * a⁻¹ = z := by
  refine commutator_mem_closure (P := P) hK.z_mul_self hK.z_cent
    (s := {x | ∃ h ∈ P, ∃ v ∈ V, h * v * h⁻¹ = x}) ?_ ?_ ha
  · rintro x ⟨h, hh, v, hv, rfl⟩
    exact P.mul_mem (P.mul_mem hh (hK.V_le hv)) (P.inv_mem hh)
  · rintro x ⟨h, hh, v, hv, rfl⟩
    let U : ConjSet P V := ⟨conjSub h V, h, hh, rfl⟩
    have hU : conjSub c U.1 = U.1 := congrArg Subtype.val (hfix U)
    exact commutator_mem_klein (hK.isElemAbelian_point U) (hK.card_point U)
      (hK.z_mem_point U) hK.z_ne_one (hK.z_cent c hc) hU (mul_mem_conjSub hv)

end CFSG.Quasithin.SzVB
