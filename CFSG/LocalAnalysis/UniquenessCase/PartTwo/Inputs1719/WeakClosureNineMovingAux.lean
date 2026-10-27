module

public import CFSG.LocalAnalysis.WeakClosure81.SevenOne
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Goldschmidt.Steps.G37Basic
public import CFSG.Quasithin.Background.E3Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNRedKer
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.MV914

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81

section Conj

variable {G : Type} [Group G] [Finite G]

theorem commute_of_conjSubgroup_le_normalizer {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV1 : V ≠ ⊥) (hTI : CFSG.CGT.Timmesfeld75.IsTI V) {g : G}
    (hg : conjSubgroup V g ≤ normalizer (V : Set G)) :
    ∀ a ∈ conjSubgroup V g, ∀ v ∈ V, a * v = v * a := by
  have hA : conjSubgroup V g ⊓ normalizer (V : Set G) ≠ ⊥ := by
    rw [inf_eq_left.mpr hg]
    intro h
    apply hV1
    have hc := E3.card_conjSubgroup V g
    rw [h, Subgroup.card_bot] at hc
    exact Subgroup.eq_bot_of_card_eq V hc.symm
  rcases two_conj_eq_or_comm hV hTI ⟨g, rfl⟩ ⟨1, (conjSubgroup_one V).symm⟩ hA with
    h | ⟨y, hy, hVy⟩
  · exact h
  · have hyN : y⁻¹ ∈ normalizer (V : Set G) := inv_mem (sup_le hg Subgroup.le_normalizer hy)
    have hAV : conjSubgroup V g = V := by
      rw [← E3.conjSubgroup_conj_inv (conjSubgroup V g) y, ← hVy]
      exact conjSubgroup_eq_iff_mem_normalizer.mpr hyN
    intro a ha v hv
    rw [hAV] at ha
    exact hV.comm ha hv

end Conj

section Bar

variable {Z : Type*} [Group Z]

theorem eq_one_of_mem_of_sq_eq_one {C : Subgroup Z} (hCn : C.Normal)
    (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hO2 : ∀ K : Subgroup Z, K.Normal → IsPGroup 2 K → K = ⊥) {c : Z} (hc : c ∈ C)
    (hc2 : c ^ 2 = 1) : c = 1 := by
  let Ω : Subgroup Z :=
    { carrier := {x | x ∈ C ∧ x ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => ⟨C.mul_mem ha.1 hb.1, by
        rw [Commute.mul_pow (hC a ha.1 b hb.1) 2, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨C.one_mem, one_pow 2⟩
      inv_mem' := fun {a} ha => ⟨C.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hΩn : Ω.Normal := ⟨fun x hx z => ⟨hCn.conj_mem x hx.1 z, by
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩⟩
  have hΩ2 : IsPGroup 2 Ω := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact x.2.2)⟩
  have hcΩ : c ∈ Ω := ⟨hc, hc2⟩
  rw [hO2 Ω hΩn hΩ2] at hcΩ
  exact Subgroup.mem_bot.mp hcΩ

theorem le_centralizer_normalClosure {L C : Subgroup Z} [C.Normal] (h : ⁅L, C⁆ = ⊥) :
    C ≤ centralizer (normalClosure (L : Set Z) : Set Z) :=
  le_centralizer_iff.mpr (normalClosure_le_normal (commutator_eq_bot_iff_le_centralizer.mp h))

theorem eq_one_of_isComponent [Finite Z] {Lb Cb Tb : Subgroup Z} (hL : CFSG.IsComponent Lb)
    (hCn : Cb.Normal) (hLC : ¬ Lb ≤ Cb) (hT : IsPGroup 2 Tb) (hsup : Lb ⊔ Tb = ⊤)
    (hO2 : ∀ K : Subgroup Z, K.Normal → IsPGroup 2 K → K = ⊥) {c : Z} (hc : c ∈ Cb)
    (hc2 : c ^ 2 = 1) : c = 1 := by
  have hcomm : ⁅Lb, Cb⁆ = ⊥ := (CFSG.LocalCores.component_normal_subgroup hL hCn).resolve_left hLC
  have hCE := le_centralizer_normalClosure hcomm
  have hEsup : normalClosure (Lb : Set Z) ⊔ Tb = ⊤ :=
    eq_top_iff.mpr (hsup.symm.le.trans (sup_le_sup_right le_normalClosure Tb))
  have hEC := NF914.centralizer_le_of_isPGroup_quotient hT hEsup hO2
  exact eq_one_of_mem_of_sq_eq_one hCn
    (fun a ha b hb => mem_centralizer_iff.mp (hCE hb) a (hEC (hCE ha))) hO2 hc hc2

end Bar

section Perfect

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_map_le {V N L : Subgroup G} {Z : Type*} [Group Z] (ψ : ↥N →* Z)
    (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) (hLN : L ≤ N)
    (hNV : N ≤ normalizer (V : Set G)) (hLp : ⁅L, L⁆ = L)
    (h : (L.subgroupOf N).map ψ ≤ ((centralizer (V : Set G)).subgroupOf N).map ψ) :
    L ≤ centralizer (V : Set G) := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 N) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have : Group.IsNilpotent (pCoreOf 2 N) := hQ2.isNilpotent
  refine CFSG.Goldschmidt.G37.le_of_perfect_of_le_sup (Subgroup.isPerfect_iff.mpr hLp)
    (fun l hl => ?_) (((CFSG.LieType.BorelTits.pCoreOf_le 2 N).trans hNV).trans
      (B2F.normalizer_le_normalizer_centralizer V)) inferInstance
  obtain ⟨c, hc, hcl⟩ := h (mem_map_of_mem ψ (show (⟨l, hLN hl⟩ : ↥N) ∈ L.subgroupOf N from hl))
  have hq : ((⟨l, hLN hl⟩ * c⁻¹ : ↥N) : G) ∈ pCoreOf 2 N :=
    (hψk _).mp (by rw [map_mul, map_inv, hcl, mul_inv_cancel])
  have hl' : l = ((⟨l, hLN hl⟩ * c⁻¹ : ↥N) : G) * (c : G) := by simp
  rw [hl']
  exact mul_mem_sup hq (mem_subgroupOf.mp hc)

end Perfect

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.MV914
