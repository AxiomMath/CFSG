module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20b

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
  (BarInf uc22p20bSimpSec uc22p20bCj uc22p20bOrb uc22p20b_simpSec_restrict
    uc22p20b_simpSec_of_surjective uc22p20b_simpSec_comm uc22p20b_simpSec_sSup_cComp
    uc22p20b_le_normalizer_orb uc22p20b_orb_le uc22p20b_le_orb uc22p20b_sSup_cComp_orb
    uc22p20b_cComp_orb)

theorem simpSec_barInf_of_cComp_sup {G : Type} [Group G] [Finite G] {L B : Subgroup G}
    (hB : B ≤ normalizer (L : Set G)) (hBs : Group.IsSolvable ↥B)
    (hsSup : sSup (cComp L) = L) {Λ : Type} [Group Λ] (hnc : ∃ a b : Λ, a * b ≠ b * a)
    (h : uc22p20bSimpSec ↥(L ⊔ B) Λ) : ∃ C ∈ cComp L, Nonempty (BarInf C ≃* Λ) := by
  have hLX : L ≤ L ⊔ B := le_sup_left
  have hNn : (L.subgroupOf (L ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 (sup_le Subgroup.le_normalizer hB)
  haveI := hNn
  rcases uc22p20b_simpSec_restrict (L.subgroupOf (L ⊔ B)) h with h1 | h2
  · have h1' : uc22p20bSimpSec ↥L Λ :=
      uc22p20b_simpSec_of_surjective (Subgroup.subgroupOfEquivOfLe hLX).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hLX).symm.surjective h1
    haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
    have h1'' : uc22p20bSimpSec ↥(sSup (cComp L)) Λ := by
      rw [hsSup]
      exact h1'
    exact uc22p20b_simpSec_sSup_cComp hnc (cComp L) (Set.toFinite _) subset_rfl h1''
  · exfalso
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' (L.subgroupOf (L ⊔ B))).comp
          (Subgroup.inclusion (le_sup_right : B ≤ L ⊔ B))) := by
      intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf (L ⊔ B)) q
      have hx' : x ∈ ((L ⊔ B : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L B hB] at hx'
      obtain ⟨l, hl, b, hb, rfl⟩ := hx'
      refine ⟨⟨b, hb⟩, ?_⟩
      simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using (Subgroup.mem_normalizer_iff''.1 (hB hb) l).1 hl
    haveI : Group.IsSolvable ↥B := hBs
    haveI : Group.IsSolvable (↥(L ⊔ B) ⧸ L.subgroupOf (L ⊔ B)) :=
      Group.isSolvable_of_surjective hsurj
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (uc22p20b_simpSec_comm h2 a b)

theorem exists_conj_barInf_of_simpSec {Q : Type} [Group Q] [Finite Q] {H T C : Subgroup Q}
    (hC : C ∈ cComp H) (hTH : T ≤ H) (hT : Group.IsSolvable ↥T) {Λ : Type} [Group Λ]
    (hnc : ∃ a b : Λ, a * b ≠ b * a) (h : uc22p20bSimpSec ↥(C ⊔ T) Λ) :
    ∃ t ∈ T, Nonempty (BarInf (uc22p20bCj t C) ≃* Λ) := by
  have hOT : uc22p20bOrb T C ⊔ T = C ⊔ T :=
    le_antisymm (sup_le (uc22p20b_orb_le le_sup_right le_sup_left) le_sup_right)
      (sup_le ((uc22p20b_le_orb T C).trans le_sup_left) le_sup_right)
  have hsSup : sSup (cComp (uc22p20bOrb T C)) = uc22p20bOrb T C :=
    uc22p20b_sSup_cComp_orb hC hTH
  have h' : uc22p20bSimpSec ↥(uc22p20bOrb T C ⊔ T) Λ := by
    rw [hOT]
    exact h
  obtain ⟨C', hC', e⟩ := simpSec_barInf_of_cComp_sup (uc22p20b_le_normalizer_orb T C) hT hsSup
    hnc h'
  rw [uc22p20b_cComp_orb hC hTH] at hC'
  obtain ⟨t, rfl⟩ := hC'
  exact ⟨t, t.2, e⟩

theorem map_solvableRadical_mulEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : (CFSG.solvableRadical A).map e.toMonoidHom = CFSG.solvableRadical B := by
  have key : ∀ {A B : Type} [Group A] [Group B] [Finite A] (e : A ≃* B),
      (CFSG.solvableRadical A).map e.toMonoidHom ≤ CFSG.solvableRadical B := by
    intro A B _ _ _ e
    have hn : ((CFSG.solvableRadical A).map e.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ e.surjective
    haveI := A3.solvableRadical_isSolvable (G := A)
    have hs : Group.IsSolvable ↥((CFSG.solvableRadical A).map e.toMonoidHom) :=
      Group.isSolvable_of_surjective (f := ((CFSG.solvableRadical A).equivMapOfInjective
        e.toMonoidHom e.injective).toMonoidHom) (MulEquiv.surjective _)
    exact A3.le_solvableRadical hn hs
  refine le_antisymm (key e) ?_
  intro y hy
  have h1 : e.symm y ∈ (CFSG.solvableRadical B).map e.symm.toMonoidHom := ⟨y, hy, rfl⟩
  exact ⟨e.symm y, key e.symm h1, by simp⟩

theorem nonempty_mulEquiv_barInf_conj {Q : Type} [Group Q] [Finite Q] (g : Q) (C : Subgroup Q) :
    Nonempty (BarInf (uc22p20bCj g C) ≃* BarInf C) := by
  let e : ↥C ≃* ↥(uc22p20bCj g C) :=
    Subgroup.equivMapOfInjective C (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact ⟨(QuotientGroup.congr (CFSG.solvableRadical ↥C)
    (CFSG.solvableRadical ↥(uc22p20bCj g C)) e (map_solvableRadical_mulEquiv e)).symm⟩

end CFSG.LocalAnalysis.WeakClosure81
