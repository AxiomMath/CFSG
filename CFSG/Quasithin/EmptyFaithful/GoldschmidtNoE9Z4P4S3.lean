module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4Rec
import CFSG.RankThree.PartOne.Q1327T.Perm3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.S1417
open scoped commutatorElement

section Abstract

variable {G : Type} [Group G] [Finite G]

theorem nonempty_oTwoQuot_equiv_perm_of_quotient {X Q : Subgroup G} (hQX : Q ≤ X)
    (hQ : IsPGroup 2 Q) (hQn : (Q.subgroupOf X).Normal)
    (e : (↥X ⧸ Q.subgroupOf X) ≃* Equiv.Perm (Fin 3)) :
    Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨eD⟩ := nonempty_dihedral_three_equiv_perm
  have hXN : X ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mp hQn
  have hbot : IsPGroup 2 (⊥ : Subgroup G) := fun x => ⟨0, Subsingleton.elim _ _⟩
  have h := oTwoQuot_sup_equiv_perm (H₁ := Q) (H₂ := X) (T₀ := ⊥) (Q := Q) hXN bot_le bot_le hbot
    bot_le (inf_eq_left.mpr hQX) hQ ⟨hQn, ⟨e.trans eD.symm⟩⟩
  rwa [sup_bot_eq] at h

end Abstract

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem e9z4_oTwoQuot_equiv_perm (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    (hdat : IsE9Dat T M H PQ R₁ R₂ s) :
    Nonempty (OTwoQuot (R₂ ⊔ (T ⊓ Subgroup.normalizer (R₁ : Set G))) ≃* Equiv.Perm (Fin 3)) := by
  classical
  obtain ⟨h98, hsplit, Q₁, Q₂, hstr, hpp, hR₁, hR₂⟩ := hdat.setup h35 S hred hshape
  subst hR₁ hR₂
  have hTH : T ≤ H := hred.isHTM.1.1
  obtain ⟨t, htT, ht2, htinv⟩ := hstr.inv
  have hQ₁P : Q₁ ≤ (PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91)) := hpp.1
  have hQ₂P : Q₂ ≤ (PQ.subgroupOf H).map (resBeta (rhoH h98.toHypF91)) := hpp.2.1
  have hQ₁3 : Nat.card Q₁ = 3 := hpp.2.2.1
  have hQ₂3 : Nat.card Q₂ = 3 := hpp.2.2.2.1
  have hr₂ : Q₂ ≤ (resBeta (rhoH h98.toHypF91)).range := hQ₂P.trans hstr.P_le_X
  have hT₀H : T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Q₁ : Set G) ≤ H :=
    inf_le_left.trans hTH
  have hXH : HLb (resBeta (rhoH h98.toHypF91)) Q₂ ⊔
      (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Q₁ : Set G)) ≤ H :=
    sup_le (HLb_le _) hT₀H
  have hQX : pCoreOf 2 H ≤ HLb (resBeta (rhoH h98.toHypF91)) Q₂ ⊔
      (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Q₁ : Set G)) :=
    hdat.plane₂.1.trans le_sup_left
  let φ : ↥(HLb (resBeta (rhoH h98.toHypF91)) Q₂ ⊔
      (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Q₁ : Set G)))
      →* MulAut ↥(kOf (rhoH h98.toHypF91)) :=
    (resBeta (rhoH h98.toHypF91)).comp (Subgroup.inclusion hXH)
  have hφker : φ.ker = (pCoreOf 2 H).subgroupOf (HLb (resBeta (rhoH h98.toHypF91)) Q₂ ⊔
      (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Q₁ : Set G))) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : resBeta (rhoH h98.toHypF91) (Subgroup.inclusion hXH x) = 1 ↔
        (x : G) ∈ pCoreOf 2 H := by
      rw [← MonoidHom.mem_ker, ker_resBeta_eq h98.toHypF91 hsplit, Subgroup.mem_subgroupOf]
      exact Iff.rfl
    exact h1
  have hφrange : φ.range = Q₂ ⊔ Subgroup.zpowers t := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro _ ⟨x, rfl⟩
      have hx : (x : G) ∈ HLb (resBeta (rhoH h98.toHypF91)) (Q₂ ⊔ Subgroup.zpowers t) := by
        have hle : HLb (resBeta (rhoH h98.toHypF91)) Q₂ ⊔
            (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Q₁ : Set G)) ≤
            HLb (resBeta (rhoH h98.toHypF91)) (Q₂ ⊔ Subgroup.zpowers t) := by
          refine sup_le (HLb_mono le_sup_left) (fun y hy => ?_)
          exact (mem_HLb_iff (hT₀H hy)).mpr (Subgroup.mem_sup_right
            (resBeta_mem_zpowers_of_mem_normalizer h98.toHypF91 rfl hstr hQ₁P hQ₁3 htT ht2
              (hT₀H hy) hy.1 hy.2))
        exact hle x.2
      exact (mem_HLb_iff (hXH x.2)).mp hx
    · intro q hq
      obtain ⟨r, hr⟩ := hr₂ hq
      have hrR : (r : G) ∈ HLb (resBeta (rhoH h98.toHypF91)) Q₂ :=
        mem_HLb_of_mem (by rw [hr]; exact hq)
      exact ⟨⟨r, Subgroup.mem_sup_left hrR⟩, hr⟩
    · rw [Subgroup.zpowers_le]
      obtain ⟨x, hxH, hxT, hxN, hxt⟩ := exists_mem_normalizer_resBeta_eq h98.toHypF91 rfl hstr
        hQ₁P htT ht2
      exact ⟨⟨x, Subgroup.mem_sup_right ⟨hxT, hxN⟩⟩, hxt⟩
  have hcard6 : Nat.card ↥φ.range = 6 := by
    rw [hφrange]
    exact hstr.card_plane_S3 htT ht2 hQ₂P hQ₂3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hqQ, hq1, hqz, hq3⟩ := exists_generator_of_prime_card hQ₂3
  have hq : q ∈ φ.range := hφrange ▸ Subgroup.mem_sup_left hqQ
  have ht : t ∈ φ.range := hφrange ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have ht1 : t ≠ 1 := fun e => by rw [e, orderOf_one] at ht2; omega
  have htt : t * t = 1 := by
    rw [← pow_two, ← ht2]
    exact pow_orderOf_eq_one t
  obtain ⟨eS⟩ := CFSG.RankThree.PartOne.Q1327T.nonempty_mulEquiv_perm_three
    (⟨q, hq⟩ : ↥φ.range) ⟨t, ht⟩
    (Subtype.ext (by simpa using (by rw [← hq3]; exact pow_orderOf_eq_one q : q ^ 3 = 1)))
    (fun e => hq1 (congrArg Subtype.val e)) (Subtype.ext htt)
    (fun e => ht1 (congrArg Subtype.val e))
    (Subtype.ext (htinv q (hQ₂P hqQ))) hcard6
  have hQn : ((pCoreOf 2 H).subgroupOf (HLb (resBeta (rhoH h98.toHypF91)) Q₂ ⊔
      (T ⊓ Subgroup.normalizer (HLb (resBeta (rhoH h98.toHypF91)) Q₁ : Set G)))).Normal :=
    hφker ▸ φ.normal_ker
  exact nonempty_oTwoQuot_equiv_perm_of_quotient hQX (pCoreOf_isPGroup 2 H) hQn
    ((QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans eS))

end Main

end CFSG.Quasithin
