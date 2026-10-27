module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.Eleven.IsomorphismTransport
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
import CFSG.Timmesfeld.Bridge.Asc72LocalImage
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.OddTranspositions.PartThree

open IsoTransport
open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

structure O4MinusFrame {X : Type} [Group X] (Θ : Set X) (T : Subgroup X) (r : Fin 3 → X) :
    Prop where
  injective : Function.Injective r
  inter_eq : (T : Set X) ∩ Θ = Set.range r
  commute : ∀ i j, Commute (r i) (r j)
  transitive : ∀ x ∈ centSet Θ (r 0 * r 1 * r 2), ∀ y ∈ centSet Θ (r 0 * r 1 * r 2),
    ∃ g ∈ localGroup Θ (r 0 * r 1 * r 2), g * x * g⁻¹ = y
  bender : Nonempty (localGroup Θ (r 0 * r 1 * r 2) ⧸
    Subgroup.center (localGroup Θ (r 0 * r 1 * r 2)) ≃* CFSG.Theory.Comparator.PSL2Model 2)
  centralizer : ∀ x : X, (∀ y ∈ centSet Θ (r 0 * r 1 * r 2), Commute x y) →
    x = 1 ∨ x = r 0 * r 1 * r 2
  card_centralizer : Nat.card (Subgroup.centralizer {r 0 * r 1 * r 2}) = 240
  not_mem : r 0 * r 1 * r 2 ∉ Θ
  not_mul : ∀ a ∈ centSet Θ (r 0 * r 1 * r 2), ∀ b ∈ centSet Θ (r 0 * r 1 * r 2),
    a * b ≠ r 0 * r 1 * r 2
  conj_commute : ∃ x : X, x * (r 0 * r 1 * r 2) * x⁻¹ ≠ r 0 * r 1 * r 2 ∧
    Commute (r 0 * r 1 * r 2) (x * (r 0 * r 1 * r 2) * x⁻¹)

structure O4MinusFacts (X : Type) [Group X] (Θ : Set X) : Prop where
  card : Nat.card X = 15600
  ncard : Θ.ncard = 65
  noncomm : ∀ a ∈ Θ, ∃ b ∈ Θ, ¬ Commute a b
  primitive : ∀ B : Set X, B ⊆ Θ → B.Nonempty →
    (∀ g : X, (fun y => g * y * g⁻¹) '' B = B ∨ Disjoint ((fun y => g * y * g⁻¹) '' B) B) →
    B.Subsingleton ∨ B = Θ
  index_two : (commutator X).index = 2
  derived : Nonempty (commutator X ≃* PSL225)
  aut : ∀ φ : X ≃* X, φ '' Θ = Θ → ∃ g : X, ∀ x, φ x = g * x * g⁻¹
  frame : ∀ T : Sylow 2 X, ∃ r : Fin 3 → X, O4MinusFrame Θ T r
  perp : ∀ φ : X ≃* X, φ '' Θ = Θ → ∀ a ∈ Θ, (∀ b ∈ Θ, Commute a b → φ b = b) →
    (∀ x, φ x = x) ∨ ∀ x, φ x = a * x * a⁻¹

private lemma s11m_localGroup_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (Θ : Set X)
    (t : X) : localGroup (e '' Θ) (e t) = (localGroup Θ t).map e.toMonoidHom := by
  rw [localGroup, localGroup, centSet_image, MonoidHom.map_closure]
  rfl

private lemma s11m_centralizer_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (t : X) :
    (Subgroup.centralizer ({t} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e t} : Set Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa [map_mul] using congrArg e (Subgroup.mem_centralizer_singleton_iff.mp hx))
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hy
        simpa [map_mul] using congrArg e.symm h)

theorem O4MinusFrame.map {X Y : Type} [Group X] [Group Y] {Θ : Set X} {Θ' : Set Y}
    (e : X ≃* Y) (he : e '' Θ = Θ') {T : Subgroup X} {r : Fin 3 → X}
    (h : O4MinusFrame Θ T r) : O4MinusFrame Θ' (T.map e.toMonoidHom) (fun i => e (r i)) := by
  have hte : e (r 0 * r 1 * r 2) = e (r 0) * e (r 1) * e (r 2) := by
    simp only [map_mul]
  have hcent : centSet Θ' (e (r 0 * r 1 * r 2)) = e '' centSet Θ (r 0 * r 1 * r 2) := by
    rw [← he, centSet_image]
  have hloc : localGroup Θ' (e (r 0 * r 1 * r 2)) =
      (localGroup Θ (r 0 * r 1 * r 2)).map e.toMonoidHom := by
    rw [← he, s11m_localGroup_map]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact h.injective (e.injective hij)
  · have hT : (T.map e.toMonoidHom : Set Y) = e '' (T : Set X) := by
      rw [Subgroup.coe_map]
      apply Set.image_congr
      intro x _
      rfl
    have hTΘ : (T.map e.toMonoidHom : Set Y) ∩ Θ' = e '' ((T : Set X) ∩ Θ) := by
      rw [hT, ← he, Set.image_inter e.injective]
    rw [hTΘ, h.inter_eq, Set.range_comp' e r]
  · intro i j
    exact (h.commute i j).map e
  · intro x hx y hy
    rw [← hte] at hx hy ⊢
    rw [hcent] at hx hy
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    obtain ⟨g₀, hg₀, hg₀eq⟩ := h.transitive x₀ hx₀ y₀ hy₀
    refine ⟨e g₀, ?_, ?_⟩
    · rw [hloc]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hg₀
    · simpa [map_mul] using congrArg e hg₀eq
  · rw [← hte]
    obtain ⟨φ⟩ := h.bender
    let ψ : localGroup Θ (r 0 * r 1 * r 2) ≃* localGroup Θ' (e (r 0 * r 1 * r 2)) :=
      (e.subgroupMap (localGroup Θ (r 0 * r 1 * r 2))).trans
        (MulEquiv.subgroupCongr hloc.symm)
    exact ⟨(QuotientGroup.congr (Subgroup.center (localGroup Θ (r 0 * r 1 * r 2)))
      (Subgroup.center (localGroup Θ' (e (r 0 * r 1 * r 2)))) ψ
      (Subgroup.map_center_eq ψ)).symm.trans φ⟩
  · rw [← hte]
    intro x hx
    have hx' : ∀ y ∈ centSet Θ (r 0 * r 1 * r 2), Commute (e.symm x) y := by
      intro y hy
      have hy' : e y ∈ centSet Θ' (e (r 0 * r 1 * r 2)) := by
        rw [hcent]
        exact ⟨y, hy, rfl⟩
      have h := hx (e y) hy'
      simpa using h.map e.symm
    rcases h.centralizer (e.symm x) hx' with h1 | h1
    · left
      rw [← e.apply_symm_apply x, h1, map_one]
    · right
      rw [← e.apply_symm_apply x, h1]
  · rw [← hte]
    rw [← s11m_centralizer_map e (r 0 * r 1 * r 2)]
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({r 0 * r 1 * r 2} : Set X)) e.toMonoidHom e.injective).toEquiv]
    exact h.card_centralizer
  · rw [← hte]
    intro hmem
    rw [← he] at hmem
    obtain ⟨y, hy, hye⟩ := hmem
    exact h.not_mem (e.injective hye ▸ hy)
  · rw [← hte]
    intro a ha b hb hab
    rw [hcent] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact h.not_mul a₀ ha₀ b₀ hb₀ (e.injective (by simpa [map_mul] using hab))
  · rw [← hte]
    obtain ⟨x₀, hx₀ne, hx₀c⟩ := h.conj_commute
    refine ⟨e x₀, ?_, ?_⟩
    · intro hcontra
      exact hx₀ne (e.injective (by simpa [map_mul] using hcontra))
    · simpa [map_mul] using hx₀c.map e

theorem O4MinusFacts.of_mulEquiv {X Y : Type} [Group X] [Group Y] {Θ : Set X} {Θ' : Set Y}
    (e : X ≃* Y) (he : e '' Θ = Θ') (h : O4MinusFacts X Θ) : O4MinusFacts Y Θ' := by
  rw [← he]
  have hmap := map_commutator e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv, h.card]
  · rw [Set.ncard_image_of_injective _ e.injective, h.ncard]
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨b, hb, hnb⟩ := h.noncomm x hx
    exact ⟨e b, Set.mem_image_of_mem e hb,
      fun hc => hnb ((commute_map_iff e.injective).mp hc)⟩
  · intro B' hB'sub hB'ne hB'inv
    let B : Set X := e.symm '' B'
    have hBsub : B ⊆ Θ := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz, rfl⟩ := hB'sub hy
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
      rw [hB'eq, heq]
  · have hidx := Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective (commutator X)
    rw [← hmap, hidx, h.index_two]
  · obtain ⟨φ⟩ := h.derived
    exact ⟨(MulEquiv.subgroupCongr hmap).symm.trans
      ((e.subgroupMap (commutator X)).symm.trans φ)⟩
  · intro φ' hφ'
    let φ : X ≃* X := (e.trans φ').trans e.symm
    have hφim : φ '' Θ = Θ := by
      have : φ = (e.trans φ').trans e.symm := rfl
      rw [this, aut_image e φ' Θ, hφ']
      rw [Set.image_image]
      simp
    obtain ⟨g₀, hg₀⟩ := h.aut φ hφim
    refine ⟨e g₀, fun y => ?_⟩
    have h1 := congr_arg e (hg₀ (e.symm y))
    simpa [φ, map_mul] using h1
  · intro T'
    let T : Sylow 2 X := T'.comapOfInjective (e : X →* Y) e.injective
      (by rw [MonoidHom.range_eq_top.mpr e.surjective]; exact le_top)
    obtain ⟨r, hr⟩ := h.frame T
    refine ⟨fun i => e (r i), ?_⟩
    have hmapT : ((T : Subgroup X).map e.toMonoidHom) = (T' : Subgroup Y) := by
      change (T'.comap e.toMonoidHom).map e.toMonoidHom = (T' : Subgroup Y)
      rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective T']
    rw [← hmapT]
    exact O4MinusFrame.map e rfl hr
  · intro φ' hφ' a ha hfix
    let φ : X ≃* X := (e.trans φ').trans e.symm
    have hφim : φ '' Θ = Θ := by
      have : φ = (e.trans φ').trans e.symm := rfl
      rw [this, aut_image e φ' Θ, hφ']
      rw [Set.image_image]
      simp
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    have ha' : e.symm (e a₀) ∈ Θ := by simpa using ha₀
    have hfix' : ∀ b ∈ Θ, Commute (e.symm (e a₀)) b → φ b = b := by
      intro b hb hcomm
      have hb' : e b ∈ e '' Θ := Set.mem_image_of_mem e hb
      have hcomm' : Commute (e a₀) (e b) := by
        have := hcomm.map e
        simpa using this
      have hfixb : φ' (e b) = e b := hfix (e b) hb' hcomm'
      change e.symm (φ' (e b)) = b
      rw [hfixb]
      simp
    rcases h.perp φ hφim (e.symm (e a₀)) ha' hfix' with hfixall | hconj
    · left
      intro y
      have h1 := congr_arg e (hfixall (e.symm y))
      simpa [φ] using h1
    · right
      intro y
      have h1 := congr_arg e (hconj (e.symm y))
      simpa [φ, map_mul] using h1

end CFSG.OddTranspositions.PartThree
