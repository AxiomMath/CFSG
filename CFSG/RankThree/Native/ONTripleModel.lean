module

public import CFSG.RankThree.Native.ONTriplePres
public import CFSG.Sporadic.Bridge.ONSurj
public import Certificates.Certificate8143
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.CosetTable CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.Bridge TauCeti

theorem model_check :
    (∀ r ∈ coverRels 1 1 1, FreeGroup.lift gM (FreeGroup.mk r) = 1) ∧
      gM 0 * gM 1 ≠ gM 1 * gM 0 ∧ gM 7 ≠ 1 :=
  Certificates.certificate8143

theorem coverRels_length : (coverRels 1 1 1).length = 37 := by decide

theorem lift_gM_relator :
    ∀ r ∈ {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk},
    FreeGroup.lift gM r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  exact model_check.1 w hw

@[expose] def psiM :
    FHat 1 1 1 →* Mat45ˣ := PresentedGroup.toGroup lift_gM_relator

theorem psiM_of
    (k : Fin 8) : psiM (PresentedGroup.of k) = gM k := PresentedGroup.toGroup.of _

abbrev M : Subgroup Mat45ˣ := psiM.range

theorem gM_mem (k : Fin 8) : gM k ∈ M := ⟨_, psiM_of k⟩

theorem gM_zero_one_ne : gM 0 * gM 1 ≠ gM 1 * gM 0 :=
  model_check.2.1

theorem gM_seven_ne : gM 7 ≠ 1 :=
  model_check.2.2

abbrev PON : GroupPresentation := Sporadic.onanPresentation

private theorem presentation_ONan : SporadicName.ONan.presentation = Sporadic.onanPresentation :=
  rfl

theorem nonempty_equiv_PON :
    Nonempty (Blueprint.NativeSporadic.ON ≃* PON.Group) := by
  have h := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  unfold SporadicName.Group at h
  rw [presentation_ONan] at h
  exact h

theorem card_PON :
    Nat.card PON.Group = 460815505920 := by
  obtain ⟨e⟩ := nonempty_equiv_PON
  rw [← CFSG.Sporadic.ON.card_ON_eq]
  exact (Nat.card_congr e.toEquiv).symm

instance :
    IsSimpleGroup PON.Group := by
  obtain ⟨e⟩ := nonempty_equiv_PON
  have h := CFSG.Sporadic.ON.isSimpleGroup_ON
  exact @MulEquiv.isSimpleGroup PON.Group _ Blueprint.NativeSporadic.ON _ h e.symm

theorem generatorCount_PON : PON.generatorCount = 7 := CFSG.Sporadic.Bridge.ON.generatorCount_eq

@[expose] def pGen (P : GroupPresentation) (i : ℕ) : P.Group :=
  if h : i < P.generatorCount then PresentedGroup.of ⟨i, h⟩ else 1

theorem pGen_of (P : GroupPresentation) (i : Fin P.generatorCount) :
    pGen P i.val = PresentedGroup.of i := by
  unfold pGen
  simp [i.isLt]

theorem pGen_seven : pGen PON 7 = 1 := by
  unfold pGen
  simp [generatorCount_PON]

theorem wordProd_pGen_relator (P : GroupPresentation) {v : List (ℕ × Bool)}
    (hv : v ∈ P.relatorLetters) : wordProd (pGen P) v = 1 := by
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  rw [← lift_mk]
  have hlift : FreeGroup.lift (fun i : Fin P.generatorCount => pGen P i.val) =
      (PresentedGroup.mk P.relatorSet : FreeGroup _ →* P.Group) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of, pGen_of]
    rfl
  rw [hlift]
  exact PresentedGroup.one_of_mem (relators_mem P w hw)

@[expose] def dropZ (w : List (Fin 8 × Bool)) : List (ℕ × Bool) :=
  (w.filter fun l => l.1.val != 7).map fun l => (l.1.val, l.2)

theorem wordProd_map_val (w : List (Fin 8 × Bool)) :
    wordProd (pGen PON) (w.map fun l => (l.1.val, l.2)) = wordProd (pGen PON) (dropZ w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨k, b⟩ := l
    by_cases hk : k.val = 7
    · have hd : dropZ ((k, b) :: w) = dropZ w := by
        simp [dropZ, hk]
      rw [hd, ← ih]
      simp only [wordProd, List.map_cons, List.prod_cons, hk, pGen_seven, inv_one, ite_self,
        one_mul]
    · have hd : dropZ ((k, b) :: w) = (k.val, b) :: dropZ w := by
        simp [dropZ, hk]
      rw [hd]
      simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]

theorem dropZ_cases : ∀ r ∈ coverRels 1 1 1, dropZ r ∈ CFSG.Sporadic.Bridge.ONGPL.Native.rels ∨
    dropZ r = [] ∨ ∃ i < 7, dropZ r = [(i, true), (i, false)] := by
  decide

@[expose] def piImg (k : Fin 8) : PON.Group := pGen PON k.val

theorem lift_piImg_mk (w : List (Fin 8 × Bool)) : FreeGroup.lift piImg (FreeGroup.mk w) =
    wordProd (pGen PON) (w.map fun l => (l.1.val, l.2)) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [show FreeGroup.mk (x :: w) = FreeGroup.mk [x] * FreeGroup.mk w from rfl, map_mul, ih]
    obtain ⟨i, b⟩ := x
    cases b with
    | true =>
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, ↓reduceIte, piImg]
    | false =>
      rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp only [wordProd, List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte, piImg]

theorem lift_piImg_relator :
    ∀ r ∈ {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk},
      FreeGroup.lift piImg r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [lift_piImg_mk, wordProd_map_val]
  rcases dropZ_cases w hw with h | h | ⟨i, -, h⟩
  · rw [← CFSG.Sporadic.Bridge.ON.relatorLetters_eq] at h
    exact wordProd_pGen_relator PON h
  · rw [h]; rfl
  · rw [h]; simp [wordProd]

@[expose] def piON : FHat 1 1 1 →* PON.Group := PresentedGroup.toGroup lift_piImg_relator

theorem piON_of (k : Fin 8) : piON (PresentedGroup.of k) = pGen PON k.val :=
  PresentedGroup.toGroup.of _

theorem piON_surjective : Function.Surjective piON := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hi : i.val < 8 := by
    have h1 := i.isLt
    have h2 := generatorCount_PON
    omega
  refine ⟨PresentedGroup.of ⟨i.val, hi⟩, ?_⟩
  rw [piON_of]
  exact pGen_of PON i

@[expose] def zF : FHat 1 1 1 := PresentedGroup.of 7

theorem psiM_zF : psiM zF = gM 7 := psiM_of 7

theorem zF_ne_one :
    zF ≠ 1 := fun h => gM_seven_ne (by rw [← psiM_zF, h, map_one])

theorem zF_cube : zF ^ 3 = 1 := by
  have hmem : [(7, true), (7, true), (7, true)] ∈ coverRels 1 1 1 := by decide
  have := PresentedGroup.one_of_mem (rels := {r : FreeGroup (Fin 8) |
    r ∈ (coverRels 1 1 1).map FreeGroup.mk}) (List.mem_map_of_mem hmem)
  rw [zF, pow_succ, pow_succ, pow_one]
  exact this

theorem orderOf_zF : orderOf zF = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime zF_cube zF_ne_one

theorem zF_mem_ker : zF ∈ piON.ker := by
  rw [MonoidHom.mem_ker, zF, piON_of]
  exact pGen_seven

instance : Finite (FHat 1 1 1) := card_FHat_one_le.1

theorem ker_piON :
    piON.ker = Subgroup.zpowers zF := by
  have hle : Subgroup.zpowers zF ≤ piON.ker := (Subgroup.zpowers_le).2 zF_mem_ker
  have hz : Nat.card (Subgroup.zpowers zF) = 3 := by rw [Nat.card_zpowers, orderOf_zF]
  have hk := Subgroup.card_ker_mul_card_of_surjective (f := piON) piON_surjective
  rw [card_PON] at hk
  have hF := card_FHat_one_le.2
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hz]
  omega

theorem card_FHat_one :
    Nat.card (FHat 1 1 1) = 1382446517760 := by
  have hk := Subgroup.card_ker_mul_card_of_surjective (f := piON) piON_surjective
  rw [card_PON, ker_piON, Nat.card_zpowers, orderOf_zF] at hk
  omega

theorem psiM_injective :
    Function.Injective psiM := by
  rw [← MonoidHom.ker_eq_bot_iff]
  set N := psiM.ker
  have hNz : N ⊓ Subgroup.zpowers zF = ⊥ := by
    have : Fact (Nat.card (Subgroup.zpowers zF)).Prime := ⟨by
      rw [Nat.card_zpowers, orderOf_zF]; exact Nat.prime_three⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((N ⊓ Subgroup.zpowers zF).subgroupOf
        (Subgroup.zpowers zF)) with h | h
    · rw [eq_bot_iff]
      intro g hg
      have : (⟨g, hg.2⟩ : Subgroup.zpowers zF) ∈ (N ⊓ Subgroup.zpowers zF).subgroupOf
          (Subgroup.zpowers zF) := by rw [Subgroup.mem_subgroupOf]; exact hg
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    · exfalso
      have : (⟨zF, Subgroup.mem_zpowers zF⟩ : Subgroup.zpowers zF) ∈
          (N ⊓ Subgroup.zpowers zF).subgroupOf (Subgroup.zpowers zF) := by rw [h]; trivial
      rw [Subgroup.mem_subgroupOf] at this
      have h1 : psiM zF = 1 := this.1
      rw [psiM_zF] at h1
      exact gM_seven_ne h1
  have hnorm : (N.map piON).Normal := Subgroup.Normal.map psiM.normal_ker piON piON_surjective
  rcases hnorm.eq_bot_or_eq_top with h | h
  · rw [eq_bot_iff]
    intro g hg
    have hk : g ∈ piON.ker := by
      rw [MonoidHom.mem_ker]
      have : piON g ∈ N.map piON := ⟨g, hg, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    rw [ker_piON] at hk
    rw [← hNz]
    exact ⟨hg, hk⟩
  · exfalso
    apply gM_zero_one_ne
    have hcyc : ∀ g : FHat 1 1 1, ∃ k : ℤ, psiM g = gM 7 ^ k := by
      intro g
      have : piON g ∈ N.map piON := by rw [h]; trivial
      obtain ⟨n, hn, hng⟩ := this
      have hk : g * n⁻¹ ∈ piON.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hng, mul_inv_cancel]
      rw [ker_piON] at hk
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hk
      refine ⟨k, ?_⟩
      have hn1 : psiM n = 1 := hn
      have := congrArg psiM hk
      rw [map_zpow, psiM_zF, map_mul, map_inv, hn1, inv_one, mul_one] at this
      exact this.symm
    obtain ⟨k0, h0⟩ := hcyc (PresentedGroup.of 0)
    obtain ⟨k1, h1⟩ := hcyc (PresentedGroup.of 1)
    rw [psiM_of] at h0 h1
    rw [h0, h1, ← zpow_add, ← zpow_add, add_comm]

@[expose] def modelEquiv :
    FHat 1 1 1 ≃* M :=
  MulEquiv.ofBijective psiM.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.2 psiM_injective, psiM.rangeRestrict_surjective⟩

theorem modelEquiv_apply
    (g : FHat 1 1 1) : (modelEquiv g : Mat45ˣ) = psiM g := rfl

theorem card_M :
    Nat.card M = 1382446517760 := by
  rw [← Nat.card_congr modelEquiv.toEquiv, card_FHat_one]

end CFSG.RankThree.Native.ONTriple
