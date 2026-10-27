module

public import CFSG.RankThree.GF2n.Tim81RootCase2
public import CFSG.RankThree.GF2n.Tim78S4LemA
import CFSG.RankThree.GF2n.Tim77Prop24Inv
public import CFSG.RankThree.GF2n.Tim77Prop24Conj

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem commutator_conj_eq_sq {a y : G} (haa : a * a = 1) :
    ⁅a, a * (y⁻¹ * a * y)⁆ = (y⁻¹ * (a * y * a)) ^ 2 := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  rw [commutatorElement_def, sq]
  calc a * (a * (y⁻¹ * a * y)) * a⁻¹ * (a * (y⁻¹ * a * y))⁻¹
      = a * a * y⁻¹ * a * y * a⁻¹ * y⁻¹ * a⁻¹ * y * a⁻¹ := by group
    _ = y⁻¹ * a * y * a * y⁻¹ * a * y * a := by rw [haa, hainv]; group
    _ = y⁻¹ * (a * y * a) * (y⁻¹ * (a * y * a)) := by group

private theorem mem_normalizer_of_conj_le {L : Subgroup G} {q : G}
    (h1 : conjSubgroup q L ≤ L) (h2 : conjSubgroup q⁻¹ L ≤ L) :
    q ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    refine h1 (mem_conjSubgroup.mpr ?_)
    rwa [show q⁻¹ * (q * h * q⁻¹) * q = h by group]
  · intro hh
    exact h2 (mem_conjSubgroup.mpr (by rwa [inv_inv]))

private theorem conj_mono {y : G} {X Y : Subgroup G} (h : X ≤ Y) :
    conjSubgroup y X ≤ conjSubgroup y Y :=
  Subgroup.map_mono h

private theorem mem_normalizer_of_comm {A : Subgroup G} {t : G} (h : ∀ u ∈ A, t * u = u * t) :
    t ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [h u hu, mul_inv_cancel_right]
    exact hu
  · intro hu
    have e : t * u * t⁻¹ = u :=
      mul_left_cancel ((h _ hu).trans (show t * u * t⁻¹ * t = t * u by group))
    rwa [e] at hu

theorem exists_isMaxRootWitness_of_not_rootTypeStep [Finite G] {M B : Subgroup G}
    (hRT : ¬ RootTypeStep M B) : ∃ g : G, IsMaxRootWitness M B g := by
  classical
  obtain ⟨g, b, hb, hb1, hbM, hgM⟩ :
      ∃ g b : G, b ∈ B ∧ b ≠ 1 ∧ g * b * g⁻¹ ∈ M ∧ ¬ conjSubgroup g B ≤ M := by
    by_contra hcon
    exact hRT fun g b hb hb1 hbM => by
      by_contra hgM
      exact hcon ⟨g, b, hb, hb1, hbM, hgM⟩
  set S : Set G := {h | ¬ conjSubgroup h B ≤ M ∧ conjSubgroup h B ⊓ M ≠ ⊥} with hS
  have hgS : g ∈ S := by
    refine ⟨hgM, ?_⟩
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨g * b * g⁻¹, Subgroup.mem_inf.mpr ⟨?_, hbM⟩⟩, ?_⟩
    · rw [mem_conjSubgroup, show g⁻¹ * (g * b * g⁻¹) * g = b by group]
      exact hb
    · intro h1
      apply hb1
      have h2 : g * b * g⁻¹ = 1 := congrArg Subtype.val h1
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
  obtain ⟨g', hg'S, hmax⟩ := Set.exists_max_image S
    (fun h => Nat.card ↥(conjSubgroup h B ⊓ M)) (Set.toFinite S) ⟨g, hgS⟩
  exact ⟨g', hg'S.1, hg'S.2, fun h h1 h2 => hmax h ⟨h1, h2⟩⟩

namespace RootCore

variable [Finite G] {M B Q : Subgroup G} (H : RootCore M B Q)
include H

theorem exists_isMaxRootWitness (hRT : ¬ RootTypeStep M B) :
    ∃ g : G, IsMaxRootWitness M B g :=
  exists_isMaxRootWitness_of_not_rootTypeStep hRT

theorem comm_conj_self_of_rootStep1 {g : G} (h1 : RootStep1 M B Q g) {a y : G}
    (ha : a ∈ conjSubgroup g B ⊓ M) (hy : y ∈ Q) :
    a * (y⁻¹ * a * y) = y⁻¹ * a * y * a := by
  by_cases ha1 : a = 1
  · subst ha1; group
  obtain ⟨haA, haM⟩ := Subgroup.mem_inf.mp ha
  have haa : a * a = 1 := by
    rw [← sq]; exact (isElemAbelian_conjSubgroup H.elemAb g).2 a haA
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hNQ := H.M_le_normalizer_Q haM
  have hya : a * y * a ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp hNQ y).mp hy
    rwa [hainv] at this
  have hyia : a * y⁻¹ * a ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp hNQ y⁻¹).mp (inv_mem hy)
    rwa [hainv] at this
  have hc : a * (y⁻¹ * a * y) ∈ Q := by
    rw [show a * (y⁻¹ * a * y) = a * y⁻¹ * a * y by group]
    exact mul_mem hyia hy
  have hcB : ⁅a, a * (y⁻¹ * a * y)⁆ ∈ B := by
    rw [commutator_conj_eq_sq haa]
    exact H.sq_mem (mul_mem (inv_mem hy) hya)
  have hc2 : a * (y⁻¹ * a * y) * (a * (y⁻¹ * a * y)) = 1 := by
    rw [← sq]; exact h1 a ha ha1 _ hc hcB
  calc a * (y⁻¹ * a * y) = (a * (y⁻¹ * a * y))⁻¹ := (inv_eq_of_mul_eq_one_right hc2).symm
    _ = y⁻¹ * a⁻¹ * y * a⁻¹ := by group
    _ = y⁻¹ * a * y * a := by rw [hainv]

theorem comm_conj_of_rootStep1 {g : G} (hgM : ¬ conjSubgroup g B ≤ M) (h1 : RootStep1 M B Q g)
    {a x y : G}
    (ha : a ∈ conjSubgroup g B ⊓ M) (hx : x ∈ conjSubgroup g B ⊓ M) (hy : y ∈ Q) :
    x * (y⁻¹ * a * y) = y⁻¹ * a * y * x := by
  by_cases ha1 : a = 1
  · subst ha1; group
  obtain ⟨haA, haM⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨hxA, hxM⟩ := Subgroup.mem_inf.mp hx
  have hE := isElemAbelian_conjSubgroup H.elemAb g
  have hax : a * x = x * a := comm_of_isElemAbelian hE haA hxA
  set s := y⁻¹ * a * y with hs
  have hsa := H.comm_conj_self_of_rootStep1 h1 ha hy
  have hsN : s ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := by
    rw [H.normalizer_conj_eq]
    exact H.centralizer_le_conj haA ha1 (Subgroup.mem_centralizer_singleton_iff.mpr hsa.symm)
  have hcomA : s * x * s⁻¹ * x⁻¹ ∈ conjSubgroup g B :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hsN x).mp hxA) (inv_mem hxA)
  have hNQa := H.M_le_normalizer_Q (inv_mem haM)
  have hc : a⁻¹ * s ∈ Q := by
    rw [hs, show a⁻¹ * (y⁻¹ * a * y) = a⁻¹ * y⁻¹ * a⁻¹⁻¹ * y by group]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp hNQa y⁻¹).mp (inv_mem hy)) hy
  have hcomQ : s * x * s⁻¹ * x⁻¹ ∈ Q := by
    have hxc : x * (a⁻¹ * s)⁻¹ * x⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_Q hxM) _).mp (inv_mem hc)
    have hcx : (a⁻¹ * s) * (x * (a⁻¹ * s)⁻¹ * x⁻¹) ∈ Q := mul_mem hc hxc
    have haQ := (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_Q haM) _).mp hcx
    have hxa : a⁻¹ * x⁻¹ = x⁻¹ * a⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hax]
    have e : s * x * s⁻¹ * x⁻¹ =
        a * ((a⁻¹ * s) * (x * (a⁻¹ * s)⁻¹ * x⁻¹)) * a⁻¹ := by
      calc s * x * s⁻¹ * x⁻¹ = a * (a⁻¹ * s) * x * (a⁻¹ * s)⁻¹ * (a⁻¹ * x⁻¹) := by group
        _ = a * (a⁻¹ * s) * x * (a⁻¹ * s)⁻¹ * (x⁻¹ * a⁻¹) := by rw [hxa]
        _ = a * ((a⁻¹ * s) * (x * (a⁻¹ * s)⁻¹ * x⁻¹)) * a⁻¹ := by group
    rw [e]
    exact haQ
  have hbot : s * x * s⁻¹ * x⁻¹ ∈ conjSubgroup g B ⊓ Q := Subgroup.mem_inf.mpr ⟨hcomA, hcomQ⟩
  rw [H.conj_inf_R_eq_bot_of_not_le_M hgM, Subgroup.mem_bot] at hbot
  calc x * s = s * x * s⁻¹ * x⁻¹ * x * s * x⁻¹ * x := by rw [hbot]; group
    _ = s * x := by group

theorem comm_of_mem_conj_of_rootStep1 {g : G} (hgM : ¬ conjSubgroup g B ≤ M)
    (h1 : RootStep1 M B Q g) {x y s : G} (hx : x ∈ conjSubgroup g B ⊓ M) (hy : y ∈ Q)
    (hs : s ∈ conjSubgroup y (conjSubgroup g B ⊓ M)) : x * s = s * x := by
  have hs' := mem_conjSubgroup.mp hs
  have e : s = (y⁻¹)⁻¹ * (y⁻¹ * s * y) * y⁻¹ := by group
  rw [e]
  exact H.comm_conj_of_rootStep1 hgM h1 hs' hx (inv_mem hy)

theorem commutator_mem_of_isMaxRootWitness {g : G} (hW : IsMaxRootWitness M B g)
    (h1 : RootStep1 M B Q g) {x y s : G} (hx : x ∈ conjSubgroup g B) (hy : y ∈ Q)
    (hs : s ∈ conjSubgroup y (conjSubgroup g B ⊓ M)) :
    x * s * x⁻¹ * s⁻¹ ∈ conjSubgroup g B ⊓ M := by
  classical
  obtain ⟨hgM, hA0, hmax⟩ := hW
  set A := conjSubgroup g B with hA
  set A₀ := A ⊓ M with hA₀
  set A' := conjSubgroup y A with hA'
  have hE := isElemAbelian_conjSubgroup H.elemAb g
  have hti : IsTI A := isTI_conjSubgroup H.ti g
  have hA'g : A' = conjSubgroup (y * g) B := by rw [hA', hA, conjSubgroup_mul]
  obtain ⟨⟨a₀, ha₀⟩, ha₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA0
  have ha₀1 : a₀ ≠ 1 := fun h => ha₀1' (Subtype.ext h)
  have hs₀ : y * a₀ * y⁻¹ ∈ conjSubgroup y A₀ := by
    rw [mem_conjSubgroup, show y⁻¹ * (y * a₀ * y⁻¹) * y = a₀ by group]
    exact ha₀
  have hs₀1 : y * a₀ * y⁻¹ ≠ 1 := by
    intro h; apply ha₀1
    calc a₀ = y⁻¹ * (y * a₀ * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  have hconjA₀ : conjSubgroup y A₀ ≤ A' := conj_mono inf_le_left
  have hA₀yN : ∀ t ∈ conjSubgroup y A₀, t ∈ Subgroup.normalizer (A : Set G) := by
    intro t ht
    have hct := H.comm_of_mem_conj_of_rootStep1 hgM h1 ha₀ hy ht
    rw [hA, H.normalizer_conj_eq]
    exact H.centralizer_le_conj (Subgroup.mem_inf.mp ha₀).1 ha₀1
      (Subgroup.mem_centralizer_singleton_iff.mpr hct.symm)
  have hA₀N : ∀ a ∈ A₀, a ∈ Subgroup.normalizer (A' : Set G) := by
    intro a ha
    have hca := H.comm_of_mem_conj_of_rootStep1 hgM h1 ha hy hs₀
    rw [hA'g, H.normalizer_conj_eq]
    exact H.centralizer_le_conj (hA'g ▸ hconjA₀ hs₀) hs₀1
      (Subgroup.mem_centralizer_singleton_iff.mpr hca)
  have hsA' : s ∈ A' := hconjA₀ hs
  have hsN : s ∈ Subgroup.normalizer (A : Set G) := hA₀yN s hs
  by_cases hA'N : A' ≤ Subgroup.normalizer (A : Set G)
  ·
    have hel := Tim77.tim77_2_3 hE hti hA'N
    have hxs : x * s = s * x :=
      comm_of_isElemAbelian hel (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hsA')
    rw [show x * s * x⁻¹ * s⁻¹ = 1 by rw [hxs]; group]
    exact one_mem _
  have hLne : A ⊓ Subgroup.normalizer (A' : Set G) ≠ A := by
    intro hL
    have hconj : conjSubgroup y⁻¹ A' = A := by
      rw [hA', ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have hAN : conjSubgroup y⁻¹ A' ≤ Subgroup.normalizer (A' : Set G) :=
      hconj ▸ (hL ▸ inf_le_right)
    have hel' := Tim77.tim77_2_3 (isElemAbelian_conjSubgroup hE y) (isTI_conjSubgroup hti y) hAN
    rw [hconj] at hel'
    exact hA'N fun t ht => mem_normalizer_of_comm fun u hu =>
      comm_of_isElemAbelian hel' (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hu)
  have hLbot : A ⊓ Subgroup.normalizer (A' : Set G) ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨a₀, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp ha₀).1, hA₀N a₀ ha₀⟩⟩,
      fun h => ha₀1 (congrArg Subtype.val h)⟩
  have S : Tim77.Prop24Setup A A' (A ⊓ Subgroup.normalizer (A' : Set G))
      (A' ⊓ Subgroup.normalizer (A : Set G))
      ((A ⊓ Subgroup.normalizer (A' : Set G)) ⊔ (A' ⊓ Subgroup.normalizer (A : Set G))) :=
    ⟨hE, hti, ⟨y, rfl⟩, rfl, rfl, rfl, hLbot, hLne⟩
  have hcomm := S.commutator_mem_L hx (Subgroup.mem_inf.mpr ⟨hsA', hsN⟩)
  have hA₀le : A₀ ≤ A ⊓ Subgroup.normalizer (A' : Set G) := fun a ha =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp ha).1, hA₀N a ha⟩
  set h' := g⁻¹ * y * g with hh'
  have hLb : A' ⊓ Subgroup.normalizer (A : Set G) = conjSubgroup g (conjSubgroup h' B ⊓ M) := by
    rw [conjSubgroup_inf, ← conjSubgroup_mul, hA'g, hA, H.normalizer_conj_eq,
      show g * h' = y * g by rw [hh']; group]
  have hh'M : ¬ conjSubgroup h' B ≤ M := by
    intro hle
    apply hA'N
    rw [hA'g, show y * g = g * h' by rw [hh']; group, conjSubgroup_mul, hA, H.normalizer_conj_eq]
    exact conj_mono hle
  have hh'bot : conjSubgroup h' B ⊓ M ≠ ⊥ := by
    intro hbot
    have hmem : y * a₀ * y⁻¹ ∈ A' ⊓ Subgroup.normalizer (A : Set G) :=
      Subgroup.mem_inf.mpr ⟨hconjA₀ hs₀, hA₀yN _ hs₀⟩
    rw [hLb, hbot] at hmem
    have : g⁻¹ * (y * a₀ * y⁻¹) * g = 1 := by
      have := mem_conjSubgroup.mp hmem
      rwa [Subgroup.mem_bot] at this
    apply hs₀1
    calc y * a₀ * y⁻¹ = g * (g⁻¹ * (y * a₀ * y⁻¹) * g) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hcard : Nat.card ↥(A ⊓ Subgroup.normalizer (A' : Set G)) ≤ Nat.card ↥A₀ := by
    rw [← S.card_Lb_eq, hLb, card_conjSubgroup]
    exact hmax h' hh'M hh'bot
  have heq : A₀ = A ⊓ Subgroup.normalizer (A' : Set G) :=
    Subgroup.eq_of_le_of_card_ge hA₀le hcard
  rw [← heq] at hcomm
  exact hcomm

theorem rootTypeStep_of_rootStep1 (h1 : ∀ g : G, IsMaxRootWitness M B g → RootStep1 M B Q g)
    (hT79 : CitedT79 B Q) :
    RootTypeStep M B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hRT
  obtain ⟨g, hW⟩ := H.exists_isMaxRootWitness hRT
  have h1g := h1 g hW
  have hgM := hW.1
  have hA0 := hW.2.1
  set A := conjSubgroup g B with hA
  set A₀ := A ⊓ M with hA₀
  have hE := isElemAbelian_conjSubgroup H.elemAb g
  set L : Subgroup G := ⨆ (y : G) (_ : y ∈ Q), conjSubgroup y A₀ with hL
  set K : Subgroup G := A ⊔ Q with hK
  have hA₀2 : IsPGroup 2 A₀ := (H.isPGroup_B.map (MulAut.conj g).toMonoidHom).to_le inf_le_left
  have hA₀Q2 : IsPGroup 2 (A₀ ⊔ Q : Subgroup G) :=
    hA₀2.to_sup_of_normal_right' H.isPGroup_Q (inf_le_right.trans H.M_le_normalizer_Q)
  have hconj_le : ∀ {X : Subgroup G} {y : G}, A₀ ≤ X → Q ≤ X → y ∈ Q →
      conjSubgroup y A₀ ≤ X := by
    intro X y hA₀X hQX hy t ht
    have ht' := mem_conjSubgroup.mp ht
    rw [show t = y * (y⁻¹ * t * y) * y⁻¹ by group]
    exact mul_mem (mul_mem (hQX hy) (hA₀X ht')) (inv_mem (hQX hy))
  have hLA₀Q : L ≤ A₀ ⊔ Q := iSup₂_le fun y hy => hconj_le le_sup_left le_sup_right hy
  have hL2 : IsPGroup 2 L := hA₀Q2.to_le hLA₀Q
  have hLK : L ≤ K :=
    iSup₂_le fun y hy => hconj_le ((inf_le_left).trans le_sup_left) le_sup_right hy
  have hA₀L : A₀ ≤ L := by
    have := le_iSup₂_of_le (f := fun (y : G) (_ : y ∈ Q) => conjSubgroup y A₀) 1 (one_mem Q)
      le_rfl
    rwa [conjSubgroup_one] at this
  have hconjL : ∀ q : G, (∀ y ∈ Q, conjSubgroup q (conjSubgroup y A₀) ≤ L) →
      conjSubgroup q L ≤ L := by
    intro q hq
    rw [hL]
    unfold conjSubgroup
    rw [Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hy => hq y hy
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := by
    intro q hq
    have key : ∀ q' ∈ Q, conjSubgroup q' L ≤ L := fun q' hq' => hconjL q' fun y hy => by
      rw [← conjSubgroup_mul]
      exact le_iSup₂_of_le (f := fun (y : G) (_ : y ∈ Q) => conjSubgroup y A₀) (q' * y)
        (mul_mem hq' hy) le_rfl
    exact mem_normalizer_of_conj_le (key q hq) (key q⁻¹ (inv_mem hq))
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    intro x hx
    have key : ∀ x' ∈ A, conjSubgroup x' L ≤ L := fun x' hx' => hconjL x' fun y hy => by
      intro t ht
      have ht' := mem_conjSubgroup.mp ht
      set s := x'⁻¹ * t * x' with hs
      have hsL : s ∈ L := le_iSup₂_of_le (f := fun (y : G) (_ : y ∈ Q) => conjSubgroup y A₀) y
        hy le_rfl ht'
      have hcomm := H.commutator_mem_of_isMaxRootWitness hW h1g hx' hy
        ht'
      rw [show t = x' * s * x'⁻¹ * s⁻¹ * s by rw [hs]; group]
      exact mul_mem (hA₀L hcomm) hsL
    exact mem_normalizer_of_conj_le (key x hx) (key x⁻¹ (inv_mem hx))
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := sup_le hAN hQN
  have hLO : L ≤ inSubgroup (pCore 2) K := le_inSubgroup_pCore hLK hKN hL2
  have hO2 : inSubgroup (pCore 2) K ≠ ⊥ := by
    intro hbot
    apply hA0
    rw [eq_bot_iff]
    exact hA₀L.trans (hLO.trans hbot.le)
  have hBO := hT79 K le_sup_right hO2
  have hLAB : A ⊓ Subgroup.normalizer (B : Set G) = A₀ := by rw [H.normalizer_B]
  have hgB : B = conjSubgroup g⁻¹ A := by
    rw [hA, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  have S : Tim77.Prop24Setup A B (A ⊓ Subgroup.normalizer (B : Set G))
      (B ⊓ Subgroup.normalizer (A : Set G))
      ((A ⊓ Subgroup.normalizer (B : Set G)) ⊔ (B ⊓ Subgroup.normalizer (A : Set G))) :=
    ⟨hE, isTI_conjSubgroup H.ti g, ⟨g⁻¹, hgB⟩, rfl, rfl, rfl, hLAB ▸ hA0, fun h => hgM (by
      rw [← h, hLAB]; exact inf_le_right)⟩
  obtain ⟨a, haA, haM⟩ := Set.not_subset.mp hgM
  have haL : a ∉ A ⊓ Subgroup.normalizer (B : Set G) := by
    rw [hLAB]; exact fun h => haM (Subgroup.mem_inf.mp h).2
  obtain ⟨b, hbB, hbL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hodd := S.odd_orderOf_mul haA haL hbB hbL
  obtain ⟨hO2p, -, hKO⟩ := inSubgroup_pCore_two K
  have hAO2 : IsPGroup 2 (A ⊔ inSubgroup (pCore 2) K : Subgroup G) :=
    (H.isPGroup_B.map (MulAut.conj g).toMonoidHom).to_sup_of_normal_right' hO2p
      ((le_sup_left : A ≤ K).trans hKO)
  have hab : a * b = 1 := eq_one_of_odd_of_isPGroup hAO2
    (mul_mem (Subgroup.mem_sup_left haA) (Subgroup.mem_sup_right (hBO hbB))) hodd
  have hb1 : b ≠ 1 := fun h => hbL (h ▸ one_mem _)
  have hbA : b ∈ A := by
    rw [eq_inv_of_mul_eq_one_right hab]
    exact inv_mem haA
  apply hgM
  intro u hu
  refine H.normalizer_eq_and_centralizer_le.2 b hbB hb1
    (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  exact comm_of_isElemAbelian hE hu hbA

theorem rootStep1_of_not_le_M {g : G} (hgM : ¬ conjSubgroup g B ≤ M) : RootStep1 M B Q g :=
  H.rootStep1_of_case2 hgM (H.rootStep1Case2_of_not_le_M hgM)

theorem rootTypeStep_of_citedT79 (hT79 : CitedT79 B Q) : RootTypeStep M B :=
  H.rootTypeStep_of_rootStep1 (fun _ hW => H.rootStep1_of_not_le_M hW.1) hT79
end RootCore

end CFSG.RankThree.GF2n.Tim78
