module

public import CFSG.RankThree.Native.ONTripleLocalCheck
public import CFSG.RankThree.Native.ONTripleTheory
public import CFSG.RankThree.Native.ONTripleElts

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup
open scoped commutatorElement

theorem zF_comm_of (k : Fin 8) : zF * PresentedGroup.of k = PresentedGroup.of k * zF := by
  have hrel : ∀ k : Fin 8, k.val < 7 →
      [(7, true), (k, true), (7, false), (k, false)] ∈ coverRels 1 1 1 := by decide
  by_cases hk : k.val < 7
  · have h := PresentedGroup.one_of_mem (rels := {r : FreeGroup (Fin 8) |
      r ∈ (coverRels 1 1 1).map FreeGroup.mk}) (List.mem_map_of_mem (hrel k hk))
    have e : PresentedGroup.mk {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
        (FreeGroup.mk [(7, true), (k, true), (7, false), (k, false)]) =
        zF * PresentedGroup.of k * zF⁻¹ * (PresentedGroup.of k)⁻¹ := rfl
    rw [e] at h
    calc zF * PresentedGroup.of k = zF * PresentedGroup.of k * zF⁻¹ * (PresentedGroup.of k)⁻¹ *
        (PresentedGroup.of k * zF) := by group
      _ = PresentedGroup.of k * zF := by rw [h, one_mul]
  · have h7 : ((7 : Fin 8) : ℕ) = 7 := rfl
    have : k = 7 := Fin.ext (by rw [h7]; have := k.isLt; omega)
    subst this
    rfl

theorem zF_central (g : FHat 1 1 1) : zF * g = g * zF := by
  have hle : (⊤ : Subgroup (FHat 1 1 1)) ≤ centralizer {zF} := by
    rw [← PresentedGroup.closure_range_of, closure_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact (zF_comm_of k).symm
  exact (mem_centralizer_singleton_iff.1 (hle (mem_top g))).symm

theorem zM_comm {g : Mat45ˣ} (hg : g ∈ M) : zM * g = g * zM := by
  obtain ⟨f, rfl⟩ := hg
  rw [show zM = psiM zF from psiM_zF.symm, ← map_mul, ← map_mul, zF_central]

theorem zM_cube : zM ^ 3 = 1 := by
  rw [show zM = psiM zF from psiM_zF.symm, ← map_pow, zF_cube, map_one]

theorem rX_mem (i : Fin 4) : rX.getD i.val 0 ∈ rX := by
  fin_cases i <;> decide

theorem xM_cube (i : Fin 4) : xM i ^ 3 = 1 :=
  p0_facts.1 _ (rX_mem i)

theorem omegaN_lt (i j : Fin 4) : omegaN i j < 3 := by
  fin_cases i <;> fin_cases j <;> decide

theorem xM_comm (i j : Fin 4) : ⁅xM i, xM j⁆ = zM ^ omegaN i j := by
  by_cases hij : i = j
  · subst hij
    rw [commutatorElement_self]
    have : omegaN i i = 0 := by fin_cases i <;> rfl
    rw [this, pow_zero]
  · have hne : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have hc := p0_facts.2 i i.isLt j j.isLt hne
    rw [commutatorElement_def, ← zM_eq, ← hc]
    group

abbrev GM : Type := M

@[expose] def zG : GM := ⟨zM, gM_mem 7⟩

@[expose] def xG (i : Fin 4) : GM := ⟨xM i, eM_mem _⟩

@[expose] def omegaZ (i j : Fin 4) : ZMod 3 := (omegaN i j : ZMod 3)

theorem omegaZ_val (i j : Fin 4) : (omegaZ i j).val = omegaN i j := by
  rw [omegaZ, ZMod.val_natCast, Nat.mod_eq_of_lt (omegaN_lt i j)]

theorem zG_central (g : GM) : zG * g = g * zG := Subtype.ext (zM_comm g.2)

theorem relG : ThreeQRel zG xG omegaZ where
  xcube := Subtype.ext (by simpa [zG] using zM_cube)
  x1 := fun h => gM_seven_ne (congrArg Subtype.val h)
  vcube := fun i => Subtype.ext (by simpa [xG] using xM_cube i)
  xv := fun i => zG_central _
  comm := fun i j => Subtype.ext (by
    rw [omegaZ_val]
    simpa [xG, zG, commutatorElement_def] using xM_comm i j)
  nondeg := by decide

abbrev P0G : Subgroup GM := threeQ zG xG

theorem card_GM : Nat.card GM = 1382446517760 := card_M

theorem factorization_card_GM : (Nat.card GM).factorization 3 = 5 := by
  rw [card_GM, show (1382446517760 : ℕ) = 3 ^ 5 * 5689080320 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def P0Syl : Sylow 3 GM :=
  Sylow.ofCard P0G (by rw [relG.card_threeQ, factorization_card_GM]; norm_num)

theorem P0Syl_coe : (P0Syl : Subgroup GM) = P0G := rfl

theorem ThreeQRel.map {G G' : Type*} [Group G] [Group G'] {x : G} {v : Fin 4 → G}
    {ω : Fin 4 → Fin 4 → ZMod 3} (h : ThreeQRel x v ω) (φ : G →* G')
    (hφ : Function.Injective φ) : ThreeQRel (φ x) (fun i => φ (v i)) ω where
  xcube := by rw [← map_pow, h.xcube, map_one]
  x1 := fun e => h.x1 (hφ (by rw [e, map_one]))
  vcube := fun i => by rw [← map_pow, h.vcube, map_one]
  xv := fun i => by rw [← map_mul, h.xv, map_mul]
  comm := fun i j => by rw [← map_commutatorElement, h.comm, map_pow]
  nondeg := h.nondeg

theorem threeQ_map {G G' : Type*} [Group G] [Group G'] (x : G) (v : Fin 4 → G) (φ : G →* G') :
    threeQ (φ x) (fun i => φ (v i)) = (threeQ x v).map φ := by
  rw [threeQ, threeQ, MonoidHom.map_closure, Set.image_insert_eq, Set.range_comp']

theorem sylow_eq_threeQ (P : Sylow 3 GM) : ∃ g : GM,
    (P : Subgroup GM) = threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P0Syl P
  refine ⟨g, ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, P0Syl_coe, Subgroup.pointwise_smul_def]
  exact (threeQ_map zG xG (MulAut.conj g).toMonoidHom).symm

theorem relG_conj (g : GM) :
    ThreeQRel (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) omegaZ :=
  relG.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem isExtraspecial_of_eq {G : Type*} [Group G] {P Q : Subgroup G} (h : P = Q)
    (hQ : CFSG.IsExtraspecialPGroup 3 Q) : CFSG.IsExtraspecialPGroup 3 P := by
  subst h; exact hQ

theorem part_one_M (A : Subgroup GM) (hA : IsPGroup 3 A) (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h27 : Nat.card A = 27) :
    ∃ P : Sylow 3 GM, A ≤ P ∧ (A.subgroupOf P).Normal ∧
      CFSG.IsExtraspecialPGroup 3 (P : Subgroup GM) ∧ Nat.card (P : Subgroup GM) = 3 ^ 5 ∧
      Monoid.exponent (P : Subgroup GM) = 3 := by
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := sylow_eq_threeQ P
  have hr := relG_conj g
  set Q := threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) with hQ
  refine ⟨P, hAP, ?_, ?_, ?_, ?_⟩
  ·
    have hAQ : A ≤ Q := hg ▸ hAP
    set B : Subgroup Q := A.subgroupOf Q with hB
    have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
      Subtype.ext (hab _ ha _ hb)
    have hB27 : Nat.card B = 27 := by
      rw [hB, Nat.card_congr (subgroupOfEquivOfLe hAQ).toEquiv, h27]
    have hZ := hr.center_le_of_abelian B hBab hB27
    have hcomm : commutator Q ≤ B := by rw [hr.commutator_eq_center]; exact hZ
    have hnQ : B.Normal := Subgroup.Normal.of_commutator_le (G := Q) hcomm
    rw [hg]
    exact hnQ
  · rw [hg]; exact hr.isExtraspecial
  · rw [hg, hr.card_threeQ]; norm_num
  · rw [hg]; exact hr.exponent_threeQ

end CFSG.RankThree.Native.ONTriple
