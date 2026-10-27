module

public import CFSG.Quasithin.Vol2.Ch11SecD557O
public import CFSG.Quasithin.Vol2.Ch11SecD557E
public import CFSG.Quasithin.Vol2.Ch11SecD557K
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Quasithin.SL3Model
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {n : ℕ} {V V₁ L T : Subgroup G}
  (St : L3Setting n V V₁ L T (Subgroup.normalizer (V₁ : Set G)))

omit [Finite G] in
theorem inf_centralizer_L_le
    (hSc : ∀ a ∈ pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))),
      ∀ b ∈ pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))), a * b = b * a)
    (hUL : conjClosure V (Subgroup.normalizer (V₁ : Set G)) ≤
      (conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ L) ⊔
        (conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G)))
    (hCS : conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G) ≤
      pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G)))) :
    conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G) ≤
      Subgroup.centralizer (conjClosure V (Subgroup.normalizer (V₁ : Set G)) : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup
    (A := conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ L)
    (B := conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G))
    (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb.2 a ha.2) (hUL hu)
  have h1 : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc.2 a ha.2
  have h2 : b * c = c * b := hSc b (hCS hb) c (hCS hc)
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

omit [Finite G] in
include St in
theorem le_center
    (hSc : ∀ a ∈ pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))),
      ∀ b ∈ pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))), a * b = b * a)
    (hUL : conjClosure V (Subgroup.normalizer (V₁ : Set G)) ≤
      (conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ L) ⊔
        (conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G)))
    (hCS : conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G) ≤
      pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G)))) :
    V₁ ⊔ (conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G)) ≤
      conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓
        Subgroup.centralizer (conjClosure V (Subgroup.normalizer (V₁ : Set G)) : Set G) := by
  refine sup_le (le_inf (St.hyp.base.le_V.trans (le_conjClosure _ _)) ?_)
    (le_inf inf_le_left (inf_centralizer_L_le hSc hUL hCS))
  exact Subgroup.le_centralizer_iff.mp (le_centralizer_V₁ St)

include St in
theorem card_U {x y : G} (hx : x ∈ L) (hy : y ∈ L) (hV : V = V₁ ⊔ rconj V₁ x ⊔ rconj V₁ y)
    (hS : pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))) ≤
      conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓
        rconj (conjClosure V (Subgroup.normalizer (V₁ : Set G))) x ⊓
        rconj (conjClosure V (Subgroup.normalizer (V₁ : Set G))) y)
    (hSc : ∀ a ∈ pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))),
      ∀ b ∈ pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))), a * b = b * a)
    (hSV : pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))) ≤
      V ⊔ (pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G))) ⊓
        Subgroup.centralizer (L : Set G)))
    (hCS : conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓ Subgroup.centralizer (L : Set G) ≤
      pCoreOf 2 (L ⊔ conjClosure V (Subgroup.normalizer (V₁ : Set G)))) :
    Nat.card ↥(conjClosure V (Subgroup.normalizer (V₁ : Set G))) =
      2 ^ (5 * n) * Nat.card ↥(conjClosure V (Subgroup.normalizer (V₁ : Set G)) ⊓
        Subgroup.centralizer (L : Set G)) := by
  set U := conjClosure V (Subgroup.normalizer (V₁ : Set G)) with hUdef
  set S := pCoreOf 2 (L ⊔ U) with hSdef
  obtain ⟨r, s, φ₇, φ₆, h7, -, h6, -, hcard⟩ := St.G25_fam hx hy hV
  have htg := St.tripleGrp hx hy hV
  have hSS₂ : S ≤ TripleGrp.S₂ (tripleU U x y) := by rw [S₂_tripleU]; exact hS
  have hS₂S : TripleGrp.S₂ (tripleU U x y) ≤ S := htg.S₂_le_S
  have hS₂S₃ : TripleGrp.S₂ (tripleU U x y) ≤ TripleGrp.S₃ S (tripleU U x y) :=
    (le_inf (htg.S₂_le_W 0) (htg.S₂_le_W 1)).trans (le_sup_left.trans le_sup_left)
  have hr : r = 0 := by
    by_contra hr
    obtain ⟨z, hz⟩ := h7.1 (Multiplicative.ofAdd
      (Pi.single ⟨0, Nat.pos_of_ne_zero hr⟩ (vE (GaloisField 2 n) 0)))
    have h1 := (h7.2.1 z).mpr (hS₂S₃ (hSS₂ z.2))
    rw [h1] at hz
    have h2 := congrFun (congrFun (congrArg Multiplicative.toAdd hz) ⟨0, Nat.pos_of_ne_zero hr⟩) 0
    simp [vE] at h2
  have hs : s = 0 := by
    by_contra hs
    obtain ⟨z, hz⟩ := h6.1 (Multiplicative.ofAdd
      (Pi.single ⟨0, Nat.pos_of_ne_zero hs⟩ (vE (GaloisField 2 n) 0)))
    have h1 := (h6.2.1 z).mpr (hSS₂ ((S₃_le _ _) z.2))
    rw [h1] at hz
    have h2 := congrFun (congrFun (congrArg Multiplicative.toAdd hz) ⟨0, Nat.pos_of_ne_zero hs⟩) 0
    simp [vE] at h2
  subst hr
  subst hs
  rw [le_antisymm hS₂S hSS₂] at hcard
  have hVS : V ≤ S :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((le_conjClosure _ _).trans le_sup_right) St.LU_le_normV St.isPGroup_V
  have hCeq : S ⊓ Subgroup.centralizer (L : Set G) = U ⊓ Subgroup.centralizer (L : Set G) :=
    le_antisymm (fun c hc => ⟨(hS hc.1).1.1, hc.2⟩) (fun c hc => ⟨hCS hc, hc.2⟩)
  have hinf : V ⊓ (S ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨hz.1, hz.2.2⟩
    rwa [inf_centralizer_eq_bot_of_natData St.D] at h1
  have hsup : V ⊔ (S ⊓ Subgroup.centralizer (L : Set G)) = S :=
    le_antisymm (sup_le hVS inf_le_left) hSV
  have hcS := card_sup_of_commute (A := V) (B := S ⊓ Subgroup.centralizer (L : Set G))
    (fun a ha b hb => hSc a (hVS ha) b hb.1) hinf
  rw [hsup, hCeq] at hcS
  have hrel := card_eq_mul_relIndex_le hVS
  rw [hcS] at hrel
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hrel' : V.relIndex S = Nat.card ↥(U ⊓ Subgroup.centralizer (L : Set G)) :=
    (Nat.eq_of_mul_eq_mul_left hVpos hrel).symm
  rw [hcard, hrel']
  ring_nf

end CFSG.Quasithin.Vol2.Ch11.SecD
