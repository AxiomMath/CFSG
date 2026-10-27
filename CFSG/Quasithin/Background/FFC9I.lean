module

public import CFSG.Quasithin.Background.FFC9H
public import CFSG.Quasithin.Background.FFC9G
public import CFSG.Quasithin.Background.FFC6A
public import CFSG.Quasithin.Background.B1More13A

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Component

variable {V : Type} [CommGroup V] [Finite V]

theorem hasNoncentralThree_of_component (hP4 : AsB15Part4) (hB51 : AsB51)
    (hA21 : AsA21SQTKSection) {G K : Subgroup (MulAut V)} (hc : B56Counterex G)
    (hK : CFSG.Open.IsComponentOf K G) : HasNoncentralThree ↥K := by
  have hV := hc.hV
  have hb : B53Hyp G := hc.hyp
  have hO2 : pCoreOf 2 G = ⊥ := hb.1
  obtain ⟨A, hA, hKA⟩ := B55.exists_offender hP4 hV hb.2.1 hK
  obtain ⟨-, -, -, hst, -, -⟩ := B59.red_basic hV hK hA hKA
  have hKU : K ≤ stabSub (B59.W0 K A) := le_sup_left.trans hst
  have hfaith : ∀ g ∈ K, (∀ v ∈ B59.W0 K A, g v = v) → g = 1 := by
    have h0 : K ⊓ centSub (B59.W0 K A) = ⊥ := (B55.faithful_on_fixV hV hO2 hK hA hKA).1
    intro g hg hgW
    have hmem : g ∈ K ⊓ centSub (B59.W0 K A) := ⟨hg, hgW⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hmem
  have hb51 : B51Hyp (B59.Xr K A) (B59.Kr K A) := B59.b51Hyp_red hA21 hV hO2 hb hK hA hKA
  have hVM : ∀ v : ↥(B59.W0 K A), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  obtain ⟨P1, -⟩ := hB51 ↥(B59.W0 K A) hVM (B59.Xr K A) (B59.Kr K A) hb51
  exact (hasNoncentralThree_of_case1 P1.2).of_mulEquiv (resEquiv hKU hfaith).symm

theorem components_mul_comm {X L L' : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L X)
    (hL' : CFSG.Open.IsComponentOf L' X) (hne : L ≠ L') : ∀ l ∈ L, ∀ k ∈ L', l * k = k * l := by
  have h : ⁅L, L'⁆ = ⊥ := by
    rcases B113.component_le_or_commutator_eq_bot hL hL'.2.1 with h1 | h1
    · rcases B113.component_le_or_commutator_eq_bot hL' hL.2.1 with h2 | h2
      · exact absurd (le_antisymm h1 h2) hne
      · rw [Subgroup.commutator_comm]
        exact h2
    · exact h1
  intro l hl k hk
  have h1 : ⁅l, k⁆ ∈ (⊥ : Subgroup (MulAut V)) := h ▸ Subgroup.commutator_mem_commutator hl hk
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

end Component

@[expose] def B57Layer : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L G → ThreeRank2 ↥L →
      ∀ K : Subgroup (MulAut V), CFSG.Open.IsComponentOf K G → K = L

@[expose] def B57Exc : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L G → ThreeRank2 ↥L →
      (∀ K : Subgroup (MulAut V), CFSG.Open.IsComponentOf K G → K = L) →
        ¬ pCoreOf 3 G ≤ centerOf G → B56Case4 G

theorem b57Layer_of (hP4 : AsB15Part4) (hB51 : AsB51)
    (hA21 : AsA21SQTKSection) : B57Layer := by
  intro V _ _ G hc L hL h3 K hK
  by_contra hne
  have hcomm : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l := components_mul_comm hL hK (Ne.symm hne)
  obtain ⟨c, hc3, hcn⟩ := hasNoncentralThree_of_component hP4 hB51 hA21 hc hK
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := h3
  refine false_of_commuting_components hA21 (isQuotientOfSQTKTauCeti_of_b53 hc.hyp) hL.1 hK.1
    (B1Red.isQuasisimple_of_open hL.2.2) (B1Red.isQuasisimple_of_open hK.2.2) hcomm
    (x := (x : MulAut V)) (y := (y : MulAut V)) (c := (c : MulAut V)) x.2 y.2 c.2
    (fun h => hx1 (Subtype.ext h)) (by simpa using congrArg Subtype.val hx3)
    (by simpa using congrArg Subtype.val hy3) (by simpa using congrArg Subtype.val hc3)
    (congrArg Subtype.val hxy) (fun hmem => hyx ?_) (fun hcL => hcn ?_)
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm c hcL g g.2).symm

end FFC

end CFSG.Quasithin
