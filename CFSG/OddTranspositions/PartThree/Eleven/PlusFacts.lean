module

public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.OddTranspositions.PartThree.Eleven.IsomorphismTransport
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.OddTranspositions.PartThree

open IsoTransport

structure O4PlusFactors {X : Type} [Group X] (Θ : Set X) (A B : Subgroup X) : Prop where
  sup_eq : A ⊔ B = commutator X
  inf_eq : A ⊓ B = ⊥
  commute : ∀ a ∈ A, ∀ b ∈ B, Commute a b
  simpleA : IsSimpleGroup A
  cardA : Nat.card A = 60
  simpleB : IsSimpleGroup B
  cardB : Nat.card B = 60
  swap : ∀ r ∈ Θ, A.map (MulAut.conj r).toMonoidHom = B
  involutions : ∀ x : X, orderOf x = 2 →
    x ∈ Θ ∨ (∃ a ∈ Θ, ∃ b ∈ Θ, a ≠ b ∧ Commute a b ∧ x = a * b) ∨ x ∈ A ∨ x ∈ B

structure O4PlusFrame {X : Type} [Group X] (Θ : Set X) (T : Subgroup X) (r : Fin 4 → X) :
    Prop where
  injective : Function.Injective r
  inter_eq : (T : Set X) ∩ Θ = Set.range r
  prod_eq : r 0 * r 1 * r 2 * r 3 = 1
  card_closure : ∀ i, Nat.card (Subgroup.closure (Set.range r \ {r i})) = 8
  even : ∀ (g : X) (σ : Equiv.Perm (Fin 4)), (∀ i, g * r i * g⁻¹ = r (σ i)) →
    σ ∈ alternatingGroup (Fin 4)
  alternating : ∀ σ ∈ alternatingGroup (Fin 4), ∃ g : X, ∀ i, g * r i * g⁻¹ = r (σ i)
  aut : ∀ φ : X ≃* X, φ '' Θ = Θ → (∀ i, φ (r i) = r i) →
    ∃ d ∈ Subgroup.closure (Set.range r), ∀ x, φ x = d * x * d⁻¹

structure O4PlusFacts (X : Type) [Group X] (Θ : Set X) : Prop where
  card : Nat.card X = 7200
  noncomm : ∀ a ∈ Θ, ∃ b ∈ Θ, ¬ Commute a b
  primitive : ∀ B : Set X, B ⊆ Θ → B.Nonempty →
    (∀ g : X, (fun y => g * y * g⁻¹) '' B = B ∨ Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
    B.Subsingleton ∨ B = Θ
  index_two : (commutator X).index = 2
  factors : ∃ A B : Subgroup X, O4PlusFactors Θ A B
  frame : ∀ T : Sylow 2 X, ∃ r : Fin 4 → X, O4PlusFrame Θ T r
  perp : ∀ φ : X ≃* X, φ '' Θ = Θ → ∀ a ∈ Θ, (∀ b ∈ Θ, Commute a b → φ b = b) →
    (∀ x, φ x = x) ∨ ∀ x, φ x = a * x * a⁻¹

theorem O4PlusFrame.map {X Y : Type} [Group X] [Group Y] {Θ : Set X} {Θ' : Set Y}
    (e : X ≃* Y) (he : e '' Θ = Θ') {T : Subgroup X} {r : Fin 4 → X}
    (h : O4PlusFrame Θ T r) : O4PlusFrame Θ' (T.map e.toMonoidHom) (fun i => e (r i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j hij => h.injective (e.injective hij)
  · have hT : (T.map e.toMonoidHom : Set Y) = e '' (T : Set X) := by
      rw [Subgroup.coe_map]
      apply Set.image_congr
      intro x _
      rfl
    have hTΘ : (T.map e.toMonoidHom : Set Y) ∩ Θ' = e '' ((T : Set X) ∩ Θ) := by
      rw [hT, ← he, Set.image_inter e.injective]
    rw [hTΘ, h.inter_eq, Set.range_comp' e r]
  · have := congr_arg e h.prod_eq
    simpa [map_mul] using this
  · intro i
    have hes : e '' (Set.range r \ {r i}) = Set.range (fun j => e (r j)) \ {e (r i)} := by
      rw [Set.image_sdiff e.injective, Set.range_comp' e r, Set.image_singleton]
    have hgen : Set.range (fun j => e (r j)) \ {e (r i)} =
        e.toMonoidHom '' (Set.range r \ {r i}) := by
      rw [← hes]
      apply Set.image_congr
      intro x _
      rfl
    have hcl : Subgroup.closure (Set.range (fun j => e (r j)) \ {e (r i)}) =
        (Subgroup.closure (Set.range r \ {r i})).map e.toMonoidHom := by
      rw [hgen, ← MonoidHom.map_closure e.toMonoidHom]
    have hcard := Nat.card_congr
      (Subgroup.equivMapOfInjective (Subgroup.closure (Set.range r \ {r i}))
        e.toMonoidHom e.injective).toEquiv
    rw [hcl]
    exact hcard.symm.trans (h.card_closure i)
  · intro g σ hg
    apply h.even (e.symm g) σ
    intro i
    have := congr_arg (fun z => e.symm z) (hg i)
    simpa [map_mul] using this
  · intro σ hσ
    obtain ⟨g, hg⟩ := h.alternating σ hσ
    exact ⟨e g, fun i => by
      have := congr_arg e (hg i)
      simpa [map_mul] using this⟩
  · intro φ' hφ' hfix
    let φ : X ≃* X := (e.trans φ').trans e.symm
    have hφim : φ '' Θ = Θ := by
      have : φ = (e.trans φ').trans e.symm := rfl
      rw [this, aut_image e φ' Θ, he, hφ', ← he]
      rw [Set.image_image]
      simp
    have hfixφ : ∀ i, φ (r i) = r i := by
      intro i
      change e.symm (φ' (e (r i))) = r i
      rw [hfix i]
      simp
    obtain ⟨d₀, hd₀, hd₀fix⟩ := h.aut φ hφim hfixφ
    refine ⟨e d₀, ?_, ?_⟩
    · have hcl : (Subgroup.closure (Set.range r)).map e.toMonoidHom =
          Subgroup.closure (Set.range (fun i => e (r i))) := by
        rw [MonoidHom.map_closure e.toMonoidHom]
        congr 1
        ext y; constructor
        · rintro ⟨x, hx, rfl⟩
          obtain ⟨i, rfl⟩ := hx
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨r i, ⟨i, rfl⟩, rfl⟩
      rw [← hcl]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hd₀
    · intro y
      have h1 := congr_arg e (hd₀fix (e.symm y))
      simpa [φ, map_mul] using h1

theorem O4PlusFacts.of_mulEquiv {X Y : Type} [Group X] [Group Y] {Θ : Set X} {Θ' : Set Y}
    (e : X ≃* Y) (he : e '' Θ = Θ') (h : O4PlusFacts X Θ) : O4PlusFacts Y Θ' := by
  have hmap := map_commutator e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv, h.card]
  · intro a ha
    rw [← he] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨b, hb, hnb⟩ := h.noncomm x hx
    refine ⟨e b, ?_, ?_⟩
    · rw [← he]; exact Set.mem_image_of_mem e hb
    · exact fun hc => hnb ((commute_map_iff e.injective).mp hc)
  · intro B' hB'sub hB'ne hB'inv
    let B : Set X := e.symm '' B'
    have hBsub : B ⊆ Θ := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' : y ∈ e '' Θ := by rw [he]; exact hB'sub hy
      obtain ⟨z, hz, rfl⟩ := hy'
      simpa using hz
    have hBne : B.Nonempty := hB'ne.image e.symm
    have hBinv : ∀ g : X, (fun y => g * y * g⁻¹) '' B = B ∨
        Disjoint ((fun y => g * y * g⁻¹) '' B) B := by
      intro g
      rcases hB'inv (e g) with hq | hd
      · left
        rw [← conj_symm_image e B' g, hq]
      · right
        rw [← conj_symm_image e B' g]
        exact Set.disjoint_image_of_injective (EquivLike.injective e.symm) hd
    have hB'eq : B' = e '' B := by
      rw [show B = e.symm '' B' from rfl, Set.image_image]
      simp
    rcases h.primitive B hBsub hBne hBinv with hs | heq
    · left
      rw [hB'eq]
      exact hs.image e
    · right
      rw [hB'eq, heq, he]
  · have hidx := Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective
      (commutator X)
    rw [← hmap, hidx, h.index_two]
  · obtain ⟨A, B, hAB⟩ := h.factors
    refine ⟨A.map e.toMonoidHom, B.map e.toMonoidHom, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← Subgroup.map_sup, hAB.sup_eq, hmap]
    · rw [← Subgroup.map_inf A B e.toMonoidHom e.injective, hAB.inf_eq, Subgroup.map_bot]
    · intro a ha b hb
      obtain ⟨a₀, ha₀, rfl⟩ := ha
      obtain ⟨b₀, hb₀, rfl⟩ := hb
      exact (hAB.commute a₀ ha₀ b₀ hb₀).map e
    · exact (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).isSimpleGroup_congr.mp
        hAB.simpleA
    · rw [← Nat.card_congr
        (Subgroup.equivMapOfInjective A e.toMonoidHom e.injective).toEquiv, hAB.cardA]
    · exact (Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).isSimpleGroup_congr.mp
        hAB.simpleB
    · rw [← Nat.card_congr
        (Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).toEquiv, hAB.cardB]
    · intro r hr
      rw [← he] at hr
      obtain ⟨r₀, hr₀, rfl⟩ := hr
      rw [conj_map e A r₀, hAB.swap r₀ hr₀]
    · intro x hx
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [MulEquiv.orderOf_eq e y] at hx
      rcases hAB.involutions y hx with hy | hy | hy | hy
      · left
        rw [← he]; exact Set.mem_image_of_mem e hy
      · right; left
        obtain ⟨a, ha, b, hb, hne, hcomm, hxy⟩ := hy
        refine ⟨e a, ?_, e b, ?_, ?_, ?_, ?_⟩
        · rw [← he]; exact Set.mem_image_of_mem e ha
        · rw [← he]; exact Set.mem_image_of_mem e hb
        · exact fun h => hne (e.injective h)
        · exact hcomm.map e
        · rw [hxy, map_mul]
      · right; right; left
        exact Set.mem_image_of_mem e hy
      · right; right; right
        exact Set.mem_image_of_mem e hy
  · intro T'
    let T : Sylow 2 X := T'.comapOfInjective (e : X →* Y) e.injective
      (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
    obtain ⟨r, hr⟩ := h.frame T
    refine ⟨fun i => e (r i), ?_⟩
    have hmapT : ((T : Subgroup X).map e.toMonoidHom) = (T' : Subgroup Y) := by
      change (T'.comap e.toMonoidHom).map e.toMonoidHom = (T' : Subgroup Y)
      rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective T']
    rw [← hmapT]
    exact O4PlusFrame.map e he hr
  · intro φ' hφ' a ha hfix
    let φ : X ≃* X := (e.trans φ').trans e.symm
    have hφim : φ '' Θ = Θ := by
      have : φ = (e.trans φ').trans e.symm := rfl
      rw [this, aut_image e φ' Θ, he, hφ', ← he]
      rw [Set.image_image]
      simp
    have ha' : e.symm a ∈ Θ := by
      rw [← he] at ha
      obtain ⟨a₀, ha₀, rfl⟩ := ha
      simpa using ha₀
    have hfix' : ∀ b ∈ Θ, Commute (e.symm a) b → φ b = b := by
      intro b hb hcomm
      have hb' : e b ∈ Θ' := by rw [← he]; exact Set.mem_image_of_mem e hb
      have hcomm' : Commute a (e b) := by
        have := hcomm.map e
        simpa using this
      have hfixb : φ' (e b) = e b := hfix (e b) hb' hcomm'
      change e.symm (φ' (e b)) = b
      rw [hfixb]
      simp
    rcases h.perp φ hφim (e.symm a) ha' hfix' with hfixall | hconj
    · left
      intro y
      have h1 := congr_arg e (hfixall (e.symm y))
      simpa [φ] using h1
    · right
      intro y
      have h1 := congr_arg e (hconj (e.symm y))
      simpa [φ, map_mul] using h1

end CFSG.OddTranspositions.PartThree
