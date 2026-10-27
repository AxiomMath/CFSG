module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.GroupTheory.SylowTwoOfMulEquiv
import CFSG.GroupTheory.SolvableHallNodes

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.QuasithinUnique

open scoped Pointwise

variable {G G' : Type*} [Group G] [Group G']

private theorem complement_relations
    {P S H : Subgroup G} {P' S' J : Subgroup G'} (e : ↥P ≃* ↥P')
    (hmap : (S.subgroupOf P).map e.toMonoidHom = S'.subgroupOf P')
    (hS : IsSylowTwoOf S P) (hS' : IsSylowTwoOf S' P')
    (hSH : S ⊔ H = P ⊓ Subgroup.normalizer (S : Set G)) (hSH' : S ⊓ H = ⊥)
    (hS'J : S' ⊔ J = P' ⊓ Subgroup.normalizer (S' : Set G')) (hS'J' : S' ⊓ J = ⊥) :
    ((S'.subgroupOf P' ⊔ (H.subgroupOf P).map e.toMonoidHom) =
        Subgroup.normalizer (S'.subgroupOf P' : Set ↥P')) ∧
      ((S'.subgroupOf P' ⊓ (H.subgroupOf P).map e.toMonoidHom) = ⊥) ∧
      ((S'.subgroupOf P' ⊔ J.subgroupOf P') =
        Subgroup.normalizer (S'.subgroupOf P' : Set ↥P')) ∧
      ((S'.subgroupOf P' ⊓ J.subgroupOf P') = ⊥) := by
  classical
  let S₁ : Subgroup ↥P := S.subgroupOf P
  let S₁' : Subgroup ↥P' := S'.subgroupOf P'
  let H₁ : Subgroup ↥P' := (H.subgroupOf P).map e.toMonoidHom
  let F₁ : Subgroup ↥P' := Subgroup.normalizer (S₁' : Set ↥P')
  let J₁ : Subgroup ↥P' := J.subgroupOf P'
  have hHleP : H ≤ P :=
    (le_sup_right : H ≤ S ⊔ H).trans (le_of_eq hSH |>.trans inf_le_left)
  have hJleP' : J ≤ P' :=
    (le_sup_right : J ≤ S' ⊔ J).trans (le_of_eq hS'J |>.trans inf_le_left)
  have hS₁'sup : S₁' ⊔ H₁ = F₁ := by
    have hS₁'sup : S₁ ⊔ H.subgroupOf P = (P ⊓ Subgroup.normalizer (S : Set G)).subgroupOf P := by
      rw [← Subgroup.subgroupOf_sup hS.1 hHleP, hSH]
    have hmap_sup : (S₁ ⊔ H.subgroupOf P).map e.toMonoidHom = S₁' ⊔ H₁ := by
      rw [Subgroup.map_sup, hmap]
    have hF : ((P ⊓ Subgroup.normalizer (S : Set G)).subgroupOf P).map e.toMonoidHom = F₁ := by
      have h1 : (P ⊓ Subgroup.normalizer (S : Set G)).subgroupOf P =
          (Subgroup.normalizer (S : Set G)).subgroupOf P := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
      rw [h1, Subgroup.subgroupOf_normalizer_eq hS.1, Subgroup.map_equiv_normalizer_eq, hmap]
    rw [← hmap_sup, hS₁'sup, hF]
  have hS₁'inf : S₁' ⊓ H₁ = ⊥ := by
    have hS₁'inf : S₁ ⊓ H.subgroupOf P = (S ⊓ H).subgroupOf P := by
      ext x
      simp only [S₁, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    have hmap_inf : (S₁ ⊓ H.subgroupOf P).map e.toMonoidHom = S₁' ⊓ H₁ := by
      rw [Subgroup.map_inf _ _ e.toMonoidHom e.injective, hmap]
    rw [← hmap_inf, hS₁'inf, hSH', Subgroup.bot_subgroupOf, Subgroup.map_bot]
  have hS₁'Jsup : S₁' ⊔ J₁ = F₁ := by
    have hS₁'sup : (S' ⊔ J).subgroupOf P' = S₁' ⊔ J₁ :=
      Subgroup.subgroupOf_sup hS'.1 hJleP'
    have hF : (P' ⊓ Subgroup.normalizer (S' : Set G')).subgroupOf P' = F₁ := by
      have h1 : (P' ⊓ Subgroup.normalizer (S' : Set G')).subgroupOf P' =
          (Subgroup.normalizer (S' : Set G')).subgroupOf P' := by
        ext x
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
      rw [h1, Subgroup.subgroupOf_normalizer_eq hS'.1]
    rw [← hS₁'sup, hS'J, hF]
  have hS₁'Jinf : S₁' ⊓ J₁ = ⊥ := by
    have hS₁'inf : S₁' ⊓ J₁ = (S' ⊓ J).subgroupOf P' := by
      ext x
      simp only [S₁', J₁, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [hS₁'inf, hS'J', Subgroup.bot_subgroupOf]
  exact ⟨hS₁'sup, hS₁'inf, hS₁'Jsup, hS₁'Jinf⟩

private theorem exists_conj_complement_of_relations
    {P H : Subgroup G} {P' S' J : Subgroup G'} [Finite ↥P']
    (e : ↥P ≃* ↥P') (hS' : IsSylowTwoOf S' P')
    (hS₁'sup : S'.subgroupOf P' ⊔ (H.subgroupOf P).map e.toMonoidHom =
      Subgroup.normalizer (S'.subgroupOf P' : Set ↥P'))
    (hS₁'inf : S'.subgroupOf P' ⊓ (H.subgroupOf P).map e.toMonoidHom = ⊥)
    (hS₁'Jsup : S'.subgroupOf P' ⊔ J.subgroupOf P' =
      Subgroup.normalizer (S'.subgroupOf P' : Set ↥P'))
    (hS₁'Jinf : S'.subgroupOf P' ⊓ J.subgroupOf P' = ⊥) :
    ∃ n : ↥P', n ∈ S'.subgroupOf P' ∧
      J.subgroupOf P' =
        ((H.subgroupOf P).map e.toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S₁' : Subgroup ↥P' := S'.subgroupOf P'
  let H₁ : Subgroup ↥P' := (H.subgroupOf P).map e.toMonoidHom
  let F₁ : Subgroup ↥P' := Subgroup.normalizer (S₁' : Set ↥P')
  let J₁ : Subgroup ↥P' := J.subgroupOf P'
  have hH₁leF : H₁ ≤ F₁ :=
    (le_sup_right : H₁ ≤ S₁' ⊔ H₁).trans (le_of_eq hS₁'sup)
  have hJ₁leF : J₁ ≤ F₁ :=
    (le_sup_right : J₁ ≤ S₁' ⊔ J₁).trans (le_of_eq hS₁'Jsup)
  let N : Subgroup ↥F₁ := S₁'.subgroupOf F₁
  let HF : Subgroup ↥F₁ := H₁.subgroupOf F₁
  let JF : Subgroup ↥F₁ := J₁.subgroupOf F₁
  haveI : N.Normal := Subgroup.normal_in_normalizer
  have hS₁'p : IsPGroup 2 ↥S₁' :=
    hS'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS'.1).symm
  have hNp : IsPGroup 2 ↥N :=
    hS₁'p.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer : S₁' ≤ F₁)).symm
  haveI : Group.IsNilpotent ↥N := hNp.isNilpotent
  have hNsolv : Group.IsSolvable ↥N := inferInstance
  have hNcard : Nat.card ↥N = Nat.card ↥S₁' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer : S₁' ≤ F₁)).toEquiv
  have hNindex : N.index = S₁'.relIndex F₁ := rfl
  have hoddS : ¬ 2 ∣ S₁'.index := by simpa [S₁'] using hS'.2.2
  have hodd : ¬ 2 ∣ S₁'.relIndex F₁ := fun hd =>
    hoddS (hd.trans (Subgroup.relIndex_dvd_index_of_le
      (Subgroup.le_normalizer : S₁' ≤ F₁)))
  have hcop : Nat.Coprime (Nat.card ↥N) N.index := by
    rw [hNcard, hNindex]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS₁'p
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have hNHmul : (N : Set ↥F₁) * (HF : Set ↥F₁) = Set.univ := by
    have hsupNF : N ⊔ HF = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (Subgroup.le_normalizer : S₁' ≤ F₁) hH₁leF,
        hS₁'sup, Subgroup.subgroupOf_self]
    rw [← Subgroup.normal_mul N HF, hsupNF]
    rfl
  have hNJmul : (N : Set ↥F₁) * (JF : Set ↥F₁) = Set.univ := by
    have hsupNJ : N ⊔ JF = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (Subgroup.le_normalizer : S₁' ≤ F₁) hJ₁leF,
        hS₁'Jsup, Subgroup.subgroupOf_self]
    rw [← Subgroup.normal_mul N JF, hsupNJ]
    rfl
  have hNHinf : N ⊓ HF = ⊥ := by
    have h : N ⊓ HF = (S₁' ⊓ H₁).subgroupOf F₁ := by
      ext x
      simp only [N, HF, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [h, hS₁'inf, Subgroup.bot_subgroupOf]
  have hNJinf : N ⊓ JF = ⊥ := by
    have h : N ⊓ JF = (S₁' ⊓ J₁).subgroupOf F₁ := by
      ext x
      simp only [N, JF, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [h, hS₁'Jinf, Subgroup.bot_subgroupOf]
  obtain ⟨nF, hnF, hEqF⟩ :=
    CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy N hNsolv hcop
      hNHmul hNJmul hNHinf hNJinf
  let nP : ↥P' := (nF : ↥F₁)
  have hnP : nP ∈ S₁' := Subgroup.mem_subgroupOf.mp hnF
  refine ⟨nP, hnP, ?_⟩
  have hcomp : F₁.subtype.comp (MulAut.conj nF⁻¹).toMonoidHom =
      (MulAut.conj nP⁻¹).toMonoidHom.comp F₁.subtype := by
    ext x
    simp [nP, MulAut.conj_apply, mul_assoc]
  have h := congrArg (Subgroup.map F₁.subtype) hEqF
  rw [Subgroup.map_subgroupOf_eq_of_le hJ₁leF, Subgroup.map_map, hcomp,
    ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hH₁leF] at h
  exact h

private theorem exists_mulEquiv_map_of_conj {P S H : Subgroup G} {P' S' J : Subgroup G'}
    (e : ↥P ≃* ↥P') {n : ↥P'} (hn : n ∈ S'.subgroupOf P')
    (hSmap : ∀ x : ↥P, (x : G) ∈ S ↔ e x ∈ S'.subgroupOf P')
    (hNmem : ∀ y : ↥P', (y : G') ∈ Subgroup.normalizer (S' : Set G') ↔
      y ∈ Subgroup.normalizer (S'.subgroupOf P' : Set ↥P'))
    (hnorm : ∀ x : ↥P, (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      e x ∈ Subgroup.normalizer (S'.subgroupOf P' : Set ↥P'))
    (hJeq : J.subgroupOf P' =
      ((H.subgroupOf P).map e.toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom) :
    ∃ ψ : ↥P ≃* ↥P',
      (∀ x : ↥P, (x : G) ∈ S ↔ (ψ x : G') ∈ S') ∧
      (∀ x : ↥P, (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
        (ψ x : G') ∈ Subgroup.normalizer (S' : Set G')) ∧
      ∀ x : ↥P, (x : G) ∈ H ↔ (ψ x : G') ∈ J := by
  let S₁' : Subgroup ↥P' := S'.subgroupOf P'
  let F₁ : Subgroup ↥P' := Subgroup.normalizer (S₁' : Set ↥P')
  let φ : ↥P' ≃* ↥P' := MulAut.conj n⁻¹
  have hfixS : ∀ y : ↥P', y ∈ S₁' ↔ φ y ∈ S₁' := by
    intro y
    constructor
    · intro hy
      have h : n⁻¹ * y * n ∈ S₁' :=
        S₁'.mul_mem (S₁'.mul_mem (S₁'.inv_mem hn) hy) hn
      simpa [φ, MulAut.conj_apply] using h
    · intro hy
      have hy' : n⁻¹ * y * n ∈ S₁' := by simpa [φ, MulAut.conj_apply] using hy
      have h : n * (n⁻¹ * y * n) * n⁻¹ ∈ S₁' :=
        S₁'.mul_mem (S₁'.mul_mem hn hy') (S₁'.inv_mem hn)
      simpa [MulAut.conj_apply, mul_assoc] using h
  have hmapS : S₁'.map φ.toMonoidHom = S₁' := by
    ext y
    rw [Subgroup.mem_map_equiv]
    exact (hfixS (φ.symm y)).trans (by simp)
  have hmapS_symm : S₁'.map φ.symm.toMonoidHom = S₁' := by
    ext y
    rw [Subgroup.mem_map_equiv]
    exact (hfixS y).symm
  have hfixF : ∀ y : ↥P', y ∈ F₁ ↔ φ y ∈ F₁ := by
    have hmapF : F₁.map φ.toMonoidHom = F₁ := by
      rw [Subgroup.map_equiv_normalizer_eq, hmapS]
    have hmapF_symm : F₁.map φ.symm.toMonoidHom = F₁ := by
      rw [Subgroup.map_equiv_normalizer_eq, hmapS_symm]
    intro y
    constructor
    · intro hy
      rw [← hmapF]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hy
    · intro hy
      have h : φ.symm (φ y) ∈ F₁ := by
        rw [← hmapF_symm]
        exact Subgroup.mem_map_of_mem φ.symm.toMonoidHom hy
      simpa using h
  refine ⟨e.trans φ, ?_, ?_, ?_⟩
  · intro x
    have h2 : (e.trans φ x : G') ∈ S' ↔ φ (e x) ∈ S₁' :=
      (Subgroup.mem_subgroupOf).symm
    exact (hSmap x).trans ((hfixS (e x)).trans h2.symm)
  · intro x
    have h2 : (e.trans φ x : G') ∈ Subgroup.normalizer (S' : Set G') ↔
        φ (e x) ∈ F₁ :=
      (hNmem (e.trans φ x)).trans (by rfl)
    exact (hnorm x).trans ((hfixF (e x)).trans h2.symm)
  · intro x
    have h1 : (x : G) ∈ H ↔ e x ∈ (H.subgroupOf P).map e.toMonoidHom := by
      rw [← Subgroup.mem_subgroupOf (H := H) (K := P)]
      exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm
    have h2 : (e.trans φ x : G') ∈ J ↔ φ (e x) ∈ J.subgroupOf P' :=
      (Subgroup.mem_subgroupOf).symm
    have h3 : e x ∈ (H.subgroupOf P).map e.toMonoidHom ↔ φ (e x) ∈ J.subgroupOf P' := by
      rw [hJeq]
      conv_rhs => rw [Subgroup.mem_map_equiv]
      rw [MulEquiv.symm_apply_apply]
    exact h1.trans (h3.trans h2.symm)

theorem exists_mulEquiv_map_sylow_complement [Finite G] {P S H : Subgroup G}
    {P' S' J : Subgroup G'} (ψ₀ : ↥P ≃* ↥P') (hS : IsSylowTwoOf S P) (hS' : IsSylowTwoOf S' P')
    (hSH : S ⊔ H = P ⊓ Subgroup.normalizer (S : Set G)) (hSH' : S ⊓ H = ⊥)
    (hS'J : S' ⊔ J = P' ⊓ Subgroup.normalizer (S' : Set G')) (hS'J' : S' ⊓ J = ⊥) :
    ∃ ψ : ↥P ≃* ↥P',
      (∀ x : ↥P, (x : G) ∈ S ↔ (ψ x : G') ∈ S') ∧
      (∀ x : ↥P, (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
        (ψ x : G') ∈ Subgroup.normalizer (S' : Set G')) ∧
      ∀ x : ↥P, (x : G) ∈ H ↔ (ψ x : G') ∈ J := by
  classical
  haveI : Finite ↥P' := Finite.of_equiv _ ψ₀.toEquiv
  obtain ⟨e, hmap⟩ :=
    CFSG.exists_mulEquiv_map_subgroupOf_eq_of_isSylowTwoOf ψ₀ hS hS'
  let S₁ : Subgroup ↥P := S.subgroupOf P
  have hSmap : ∀ x : ↥P, (x : G) ∈ S ↔ e x ∈ S'.subgroupOf P' := by
    intro x
    rw [← Subgroup.mem_subgroupOf (H := S) (K := P), ← hmap]
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm
  have hNmem : ∀ y : ↥P',
      (y : G') ∈ Subgroup.normalizer (S' : Set G') ↔
        y ∈ Subgroup.normalizer (S'.subgroupOf P' : Set ↥P') := by
    intro y
    rw [← Subgroup.mem_subgroupOf (H := Subgroup.normalizer (S' : Set G')) (K := P'),
      Subgroup.subgroupOf_normalizer_eq hS'.1]
  have hnorm : ∀ x : ↥P, (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
      e x ∈ Subgroup.normalizer (S'.subgroupOf P' : Set ↥P') := by
    intro x
    have hleft : (x : G) ∈ Subgroup.normalizer (S : Set G) ↔
        x ∈ Subgroup.normalizer (S₁ : Set ↥P) := by
      rw [← Subgroup.mem_subgroupOf (H := Subgroup.normalizer (S : Set G)) (K := P),
        Subgroup.subgroupOf_normalizer_eq hS.1]
    have hNmap : (Subgroup.normalizer (S₁ : Set ↥P)).map e.toMonoidHom =
        Subgroup.normalizer (S'.subgroupOf P' : Set ↥P') := by
      have hmap' : Subgroup.map e.toMonoidHom (S.subgroupOf P) = S'.subgroupOf P' := hmap
      rw [Subgroup.map_equiv_normalizer_eq]
      change Subgroup.normalizer ((S.subgroupOf P).map e.toMonoidHom) =
        Subgroup.normalizer (S'.subgroupOf P' : Set ↥P')
      rw [hmap']
    rw [hleft, ← hNmap, Subgroup.mem_map_equiv]
    simp
  obtain ⟨hS₁'sup, hS₁'inf, hS₁'Jsup, hS₁'Jinf⟩ :=
    complement_relations e hmap hS hS' hSH hSH' hS'J hS'J'
  obtain ⟨n, hn, hJeq⟩ :=
    exists_conj_complement_of_relations e hS' hS₁'sup hS₁'inf hS₁'Jsup hS₁'Jinf
  exact exists_mulEquiv_map_of_conj e hn hSmap hNmem hnorm hJeq

end CFSG.Quasithin.F112R.St84
