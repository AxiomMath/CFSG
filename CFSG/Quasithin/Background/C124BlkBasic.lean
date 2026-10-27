module

public import CFSG.Quasithin.Background.C124Star
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Background.C124B2102

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Extend

variable {G : Type*} [Group G] {Q : Type*} [Group Q]

theorem exists_extend_hom {U A B : Subgroup G}
    (hsup : ∀ u ∈ U, ∃ a ∈ A, ∃ b ∈ B, u = a * b) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (f : ↥A →* Q) (hf0 : ∀ (a : G) (ha : a ∈ A), a ∈ B → f ⟨a, ha⟩ = 1)
    (hf1 : ∀ (a : G) (ha : a ∈ A), f ⟨a, ha⟩ = 1 → a ∈ B) :
    ∃ g : ↥U →* Q, (∀ (u : ↥U) (a b : G) (ha : a ∈ A), b ∈ B → (u : G) = a * b →
        g u = f ⟨a, ha⟩) ∧ ∀ u : ↥U, g u = 1 ↔ (u : G) ∈ B := by
  classical
  have key : ∀ (a a' b b' : G) (ha : a ∈ A) (ha' : a' ∈ A), b ∈ B → b' ∈ B →
      a * b = a' * b' → f ⟨a, ha⟩ = f ⟨a', ha'⟩ := by
    intro a a' b b' ha ha' hb hb' h
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ B := h1 ▸ B.mul_mem hb' (B.inv_mem hb)
    have h3 := hf0 _ (A.mul_mem (A.inv_mem ha') ha) h2
    have h4 : f ⟨a'⁻¹ * a, A.mul_mem (A.inv_mem ha') ha⟩ = (f ⟨a', ha'⟩)⁻¹ * f ⟨a, ha⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [h4] at h3
    exact (inv_mul_eq_one.1 h3).symm
  let a₀ : ↥U → G := fun u => Classical.choose (hsup u u.2)
  have hspec : ∀ u : ↥U, a₀ u ∈ A ∧ ∃ b ∈ B, (u : G) = a₀ u * b :=
    fun u => Classical.choose_spec (hsup u u.2)
  have hdef : ∀ (u : ↥U) (a b : G) (ha : a ∈ A), b ∈ B → (u : G) = a * b →
      f ⟨a₀ u, (hspec u).1⟩ = f ⟨a, ha⟩ := by
    intro u a b ha hb h
    obtain ⟨b', hb', h'⟩ := (hspec u).2
    exact key _ _ b' b (hspec u).1 ha hb' hb (h'.symm.trans h)
  have hone : f ⟨a₀ 1, (hspec 1).1⟩ = 1 := by
    have := hdef 1 1 1 A.one_mem B.one_mem (by simp)
    rw [this]
    exact map_one f
  have hmul : ∀ u u' : ↥U, f ⟨a₀ (u * u'), (hspec (u * u')).1⟩ =
      f ⟨a₀ u, (hspec u).1⟩ * f ⟨a₀ u', (hspec u').1⟩ := by
    intro u u'
    obtain ⟨b, hb, hu⟩ := (hspec u).2
    obtain ⟨b', hb', hu'⟩ := (hspec u').2
    have hbc : b * a₀ u' = a₀ u' * b := (hc _ (hspec u').1 b hb).symm
    have hprod : ((u * u' : ↥U) : G) = (a₀ u * a₀ u') * (b * b') := by
      calc ((u * u' : ↥U) : G) = (a₀ u * b) * (a₀ u' * b') := by
            rw [Subgroup.coe_mul, ← hu, ← hu']
        _ = a₀ u * (b * a₀ u') * b' := by group
        _ = (a₀ u * a₀ u') * (b * b') := by rw [hbc]; group
    rw [hdef (u * u') (a₀ u * a₀ u') (b * b') (A.mul_mem (hspec u).1 (hspec u').1)
      (B.mul_mem hb hb') hprod]
    exact map_mul f ⟨a₀ u, (hspec u).1⟩ ⟨a₀ u', (hspec u').1⟩
  refine ⟨⟨⟨fun u => f ⟨a₀ u, (hspec u).1⟩, hone⟩, hmul⟩, ?_, ?_⟩
  · intro u a b ha hb h
    exact hdef u a b ha hb h
  · intro u
    constructor
    · intro h
      obtain ⟨b, hb, hu⟩ := (hspec u).2
      have h' : f ⟨a₀ u, (hspec u).1⟩ = 1 := h
      rw [hu]
      exact B.mul_mem (hf1 _ (hspec u).1 h') hb
    · intro hu
      have h1 := hdef u 1 u A.one_mem hu (by simp)
      show f ⟨a₀ u, (hspec u).1⟩ = 1
      rw [h1]
      exact map_one f

end Extend

section Module

variable {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] def blkVal : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem blkVal_apply (v : IntMod V hV) : blkVal hV v = v.val := rfl

theorem blkVal_injective : Function.Injective (blkVal hV) := IntMod.val_injective

theorem map_blkVal_commV {L : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    (commV (autI hV L)).map (blkVal hV) = ⁅V, L⁆ := by
  rw [Subgroup.commutator_comm]
  unfold commV
  rw [MonoidHom.map_closure, Subgroup.commutator_def]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, w, rfl⟩, rfl⟩
    obtain ⟨⟨b, hbN⟩, hbX, rfl⟩ := (mem_autI hV).1 ha
    refine ⟨b, hbX, w.val, w.val_mem, ?_⟩
    rw [blkVal_apply, IntMod.val_mul, IntMod.val_inv, convI_apply_val, commutatorElement_def]
  · rintro ⟨b, hbX, y, hy, rfl⟩
    refine ⟨_, ⟨convI hV ⟨b, hL hbX⟩, convI_mem_autI hV hbX (hL hbX), IntMod.mk hV ⟨y, hy⟩,
      rfl⟩, ?_⟩
    rw [blkVal_apply, IntMod.val_mul, IntMod.val_inv, convI_apply_val, commutatorElement_def]
    rfl

variable {L : Subgroup G}

theorem blockU_le (L : Subgroup G) : blockU L ≤ L := by
  rw [blockU, Subgroup.commutator_le]
  intro g hg h hh
  have hgL : g ∈ L := C1.blockQ_le L hg
  rw [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem hgL hh) (L.inv_mem hgL)) (L.inv_mem hh)

theorem conj_mem_commutator (hL : L ≤ Subgroup.normalizer (V : Set G)) {ℓ a : G} (hℓ : ℓ ∈ L)
    (ha : a ∈ ⁅V, L⁆) : ℓ * a * ℓ⁻¹ ∈ ⁅V, L⁆ := by
  have h : V.map (MulAut.conj ℓ).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hL hℓ)
  have h2 : L.map (MulAut.conj ℓ).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hℓ)
  have h3 : ⁅V, L⁆.map (MulAut.conj ℓ).toMonoidHom = ⁅V, L⁆ := by
    rw [Subgroup.map_commutator, h, h2]
  rw [← h3]
  exact ⟨a, ha, rfl⟩

end Module

section Ker

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)
  {L : Subgroup G}

theorem ker_starHom_eq_pCore (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hker : pCoreOf 2 L = L ⊓ Subgroup.centralizer (V : Set G)) :
    (starHom hV L hL).ker = CFSG.pCore 2 ↥L := by
  rw [ker_starHom, ← hker, pCoreOf_eq_map_pCore, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

end Ker

end CFSG.Quasithin.C124
