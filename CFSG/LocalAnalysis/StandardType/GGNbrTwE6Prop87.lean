module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6ThreeLine
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTriD4Three
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBTv
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

section Config

variable {G : Type} [Group G] [Finite G]

theorem card_mul_pow_le_of_normalizes {p : ℕ} (hp : p.Prime) {J₀ : Type} [Group J₀]
    (f : J₀ →* G) (hf : Function.Injective f) {C : Subgroup G} (hC : IsElemAbelian p C)
    (hCf : ∀ g ∈ C, ∀ j : J₀, f j * g = g * f j) {U E : Subgroup J₀} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hEU : E ≤ Subgroup.normalizer (U : Set J₀)) (hE : IsElemAbelian p E)
    (hEZ : E ⊓ Subgroup.center J₀ = ⊥) {k : ℕ} (hk : Nat.card E = p ^ k) :
    Nat.card C * p ^ k ≤ p ^ LargeEvenTwoLocalRank p G := by
  have := Fact.mk hp
  have hU' : U.map f ≠ ⊥ := fun h => hU ((Subgroup.map_eq_bot_iff_of_injective _ hf).1 h)
  have hU'2 : IsPGroup 2 (U.map f) := hU2.map f
  have hE' : IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE f
  have hE'N : E.map f ≤ Subgroup.normalizer (U.map f : Set G) :=
    (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map f)
  have hE'card : Nat.card (E.map f) = p ^ k := by
    rw [Subgroup.card_map_of_injective hf, hk]
  have hcomm : ∀ a ∈ C, ∀ b ∈ E.map f, a * b = b * a := by
    rintro a ha _ ⟨e, -, rfl⟩
    exact (hCf a ha e).symm
  have hdisj : Disjoint C (E.map f) := by
    rw [Subgroup.disjoint_def]
    rintro g hgC ⟨e, he, rfl⟩
    have hez : e ∈ Subgroup.center J₀ := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply hf
      rw [map_mul, map_mul]
      exact hCf _ hgC j
    have he1 : e = 1 := by
      have h1 : e ∈ E ⊓ Subgroup.center J₀ := ⟨he, hez⟩
      rw [hEZ] at h1
      exact Subgroup.mem_bot.1 h1
    rw [he1, map_one]
  have hnorm : E.map f ≤ Subgroup.normalizer (C : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer (C : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha b hb)
  have hCE : IsElemAbelian p (C ⊔ E.map f) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hC hE' hcomm
  obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hC)
  have hcard : Nat.card (C ⊔ E.map f : Subgroup G) = p ^ (c + k) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer C _ hnorm hdisj, hc,
      hE'card, pow_add]
  have hCN : C ≤ Subgroup.normalizer (U.map f : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨u, -, rfl⟩
    exact hCf g hg u
  have hle := le_twoLocalRank_of_normalizes hp hU' hU'2 hCE (sup_le hCN hE'N) hcard
  rw [hc, ← pow_add]
  exact Nat.pow_le_pow_right hp.pos hle

theorem isComponentOf_subgroupOf_ggFix_ggGamma_y {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (hyBs : y ∈ Bs) :
    IsComponentOf (J.subgroupOf L) (ggFix (ggGamma L hNL ⟨y, hyBs⟩)) := by
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hJLD : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    have hCD : Subgroup.centralizer (D : Set G) =
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
      rw [hnb.2.1, Subgroup.centralizer_closure]
      ext g
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hLx]
  have hfix : (ggFix (ggGamma L hNL ⟨y, hyBs⟩)).map L.subtype =
      L ⊓ Subgroup.centralizer ({y} : Set G) := map_ggFix_ggGamma L hNL ⟨y, hyBs⟩
  exact (isComponentOf_comap_of_injective L.subtype L.subtype_injective
    (by rw [hfix, ← hLD]; exact hJLD)).1

end Config

end CFSG.StandardType

end
