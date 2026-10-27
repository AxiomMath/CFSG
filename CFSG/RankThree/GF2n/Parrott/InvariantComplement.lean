module

public import CFSG.RankThree.GF2n.Parrott.ComplementExtraspecial
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Parrott.Setup

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section Projections

variable {T F : Subgroup G}

theorem T_le_J_of_sup (hsup : T ⊔ F = J z) : T ≤ J z := by
  rw [← hsup]
  exact le_sup_left

theorem F_le_J_of_sup (hsup : T ⊔ F = J z) : F ≤ J z := by
  rw [← hsup]
  exact le_sup_right

theorem exists_prod_of_mem_J (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (j : J z) :
    ∃ p : T × F, (p.1 : G) * (p.2 : G) = (j : G) := by
  have hj : (j : G) ∈ T ⊔ F := by
    rw [hsup]
    exact j.2
  obtain ⟨t, ht, f, hf, htf⟩ := (CFSG.mem_sup_of_commute hcomm).mp hj
  exact ⟨(⟨t, ht⟩, ⟨f, hf⟩), htf⟩

theorem eq_of_mul_eq_mul (hdisj : T ⊓ F = ⊥) {p q : T × F}
    (h : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G)) : p = q := by
  have hmemT : (q.1 : G)⁻¹ * (p.1 : G) ∈ T :=
    T.mul_mem (T.inv_mem q.1.2) p.1.2
  have h1 : (q.1 : G)⁻¹ * (p.1 : G) * (p.2 : G) = (q.2 : G) := by
    rw [mul_assoc, h]
    group
  have heq : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ :=
    eq_mul_inv_of_mul_eq h1
  have hmemF : (q.2 : G) * (p.2 : G)⁻¹ ∈ F :=
    F.mul_mem q.2.2 (F.inv_mem p.2.2)
  have hmem : (q.1 : G)⁻¹ * (p.1 : G) ∈ T ⊓ F := ⟨hmemT, heq ▸ hmemF⟩
  have hone : (q.1 : G)⁻¹ * (p.1 : G) = 1 := by
    have := hmem
    rw [hdisj] at this
    exact Subgroup.mem_bot.mp this
  have hp1 : p.1 = q.1 := by
    apply Subtype.ext
    have h' := congrArg (fun x : G => (q.1 : G) * x) hone
    simpa [mul_assoc] using h'
  have hp2 : p.2 = q.2 := by
    apply Subtype.ext
    have h' : (p.1 : G) = (q.1 : G) := congrArg (fun x : T => (x : G)) hp1
    have hq : (p.1 : G) * (p.2 : G) = (p.1 : G) * (q.2 : G) := by
      rw [h, h']
    exact mul_left_cancel hq
  exact Prod.ext hp1 hp2

noncomputable def prodChoose (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (j : J z) : T × F :=
  Classical.choose (exists_prod_of_mem_J hcomm hsup j)

theorem prodChoose_spec (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f)
    (hsup : T ⊔ F = J z) (j : J z) :
    ((prodChoose hcomm hsup j).1 : G) * ((prodChoose hcomm hsup j).2 : G) = (j : G) :=
  Classical.choose_spec (exists_prod_of_mem_J hcomm hsup j)

theorem prodChoose_eq (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z)
    (j : J z) {p : T × F} (hp : (p.1 : G) * (p.2 : G) = (j : G)) :
    prodChoose hcomm hsup j = p :=
  eq_of_mul_eq_mul hdisj (by rw [prodChoose_spec, hp])

noncomputable def prodProjHom (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) :
    J z →* T × F where
  toFun := prodChoose hcomm hsup
  map_one' := by
    apply eq_of_mul_eq_mul hdisj
    rw [prodChoose_spec]
    simp
  map_mul' a b := by
    apply eq_of_mul_eq_mul hdisj
    rw [prodChoose_spec]
    have ha := prodChoose_spec hcomm hsup a
    have hb := prodChoose_spec hcomm hsup b
    have hc : Commute ((prodChoose hcomm hsup b).1 : G)
        ((prodChoose hcomm hsup a).2 : G) :=
      hcomm _ (prodChoose hcomm hsup b).1.2 _ (prodChoose hcomm hsup a).2.2
    calc (a : G) * (b : G)
        = (((prodChoose hcomm hsup a).1 : G) * ((prodChoose hcomm hsup a).2 : G)) *
            (((prodChoose hcomm hsup b).1 : G) * ((prodChoose hcomm hsup b).2 : G)) := by
          rw [ha, hb]
      _ = (((prodChoose hcomm hsup a).1 : G) * ((prodChoose hcomm hsup b).1 : G)) *
            (((prodChoose hcomm hsup a).2 : G) * ((prodChoose hcomm hsup b).2 : G)) := by
          calc
            ((prodChoose hcomm hsup a).1 : G) * ((prodChoose hcomm hsup a).2 : G) *
                (((prodChoose hcomm hsup b).1 : G) * ((prodChoose hcomm hsup b).2 : G))
                = ((prodChoose hcomm hsup a).1 : G) *
                    (((prodChoose hcomm hsup a).2 : G) * ((prodChoose hcomm hsup b).1 : G)) *
                      ((prodChoose hcomm hsup b).2 : G) := by group
            _ = ((prodChoose hcomm hsup a).1 : G) *
                    (((prodChoose hcomm hsup b).1 : G) * ((prodChoose hcomm hsup a).2 : G)) *
                      ((prodChoose hcomm hsup b).2 : G) := by rw [hc.eq.symm]
            _ = ((prodChoose hcomm hsup a).1 : G) * ((prodChoose hcomm hsup b).1 : G) *
                    (((prodChoose hcomm hsup a).2 : G) * ((prodChoose hcomm hsup b).2 : G)) := by
                  group
      _ = (((prodChoose hcomm hsup a * prodChoose hcomm hsup b).1 : G)) *
            (((prodChoose hcomm hsup a * prodChoose hcomm hsup b).2 : G)) := rfl

noncomputable def prT (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) :
    J z →* T :=
  (MonoidHom.fst T F).comp (prodProjHom hdisj hcomm hsup)

noncomputable def prF (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) :
    J z →* F :=
  (MonoidHom.snd T F).comp (prodProjHom hdisj hcomm hsup)

theorem prT_mul_prF (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) (j : J z) :
    ((prT hdisj hcomm hsup j : T) : G) * ((prF hdisj hcomm hsup j : F) : G) = (j : G) :=
  prodChoose_spec hcomm hsup j

theorem prT_inclusion_T (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) (t : T) :
    prT hdisj hcomm hsup (Subgroup.inclusion (T_le_J_of_sup hsup) t) = t := by
  have h : prodProjHom hdisj hcomm hsup (Subgroup.inclusion (T_le_J_of_sup hsup) t) = (t, 1) := by
    apply prodChoose_eq hdisj hcomm hsup
    simp
  change (prodProjHom hdisj hcomm hsup
    (Subgroup.inclusion (T_le_J_of_sup hsup) t)).1 = t
  rw [h]

theorem prF_inclusion_T (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) (t : T) :
    prF hdisj hcomm hsup (Subgroup.inclusion (T_le_J_of_sup hsup) t) = 1 := by
  have h : prodProjHom hdisj hcomm hsup (Subgroup.inclusion (T_le_J_of_sup hsup) t) = (t, 1) := by
    apply prodChoose_eq hdisj hcomm hsup
    simp
  change (prodProjHom hdisj hcomm hsup
    (Subgroup.inclusion (T_le_J_of_sup hsup) t)).2 = 1
  rw [h]

theorem prF_inclusion_F (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) (f : F) :
    prF hdisj hcomm hsup (Subgroup.inclusion (F_le_J_of_sup hsup) f) = f := by
  have h : prodProjHom hdisj hcomm hsup (Subgroup.inclusion (F_le_J_of_sup hsup) f) = (1, f) := by
    apply prodChoose_eq hdisj hcomm hsup
    simp
  change (prodProjHom hdisj hcomm hsup
    (Subgroup.inclusion (F_le_J_of_sup hsup) f)).2 = f
  rw [h]

theorem prT_inclusion_F (hdisj : T ⊓ F = ⊥)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) (f : F) :
    prT hdisj hcomm hsup (Subgroup.inclusion (F_le_J_of_sup hsup) f) = 1 := by
  have h : prodProjHom hdisj hcomm hsup (Subgroup.inclusion (F_le_J_of_sup hsup) f) = (1, f) := by
    apply prodChoose_eq hdisj hcomm hsup
    simp
  change (prodProjHom hdisj hcomm hsup
    (Subgroup.inclusion (F_le_J_of_sup hsup) f)).1 = 1
  rw [h]

end Projections

section Main

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)
variable {T F : Subgroup G}

theorem T_le_centerIn_of_decomposition (hT : Nat.card T = 2)
    (hcomm : ∀ t ∈ T, ∀ f ∈ F, Commute t f) (hsup : T ⊔ F = J z) :
    T ≤ centerIn (J z) := by
  intro t ht
  refine ⟨T_le_J_of_sup hsup ht, ?_⟩
  change t ∈ Subgroup.centralizer (J z : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (central_in_J_of_decomposition hT hcomm hsup t ht x hx).eq.symm

end Main

end CFSG.RankThree.GF2n.Parrott
