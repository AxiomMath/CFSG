module

public import CFSG.RankThree.GF2n.Stroth78.Sec4SixWStruct
public import CFSG.Fischer.Classification.Orthogonal2.SpRadical

import CFSG.RankThree.GF2n.Stroth78.Sec3Seven
import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec4Bound
import CFSG.RankThree.GF2n.Stroth78.Sec2EighteenR
import CFSG.RankThree.GF2n.Stroth78.Sec4Two

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification Matrix

namespace Sec4SixW

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

theorem le_normalizer_Lbar_of_perfect (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {Ω : Subgroup ↥(Xsub S a)}
    (hΩ : ⁅Ω, Ω⁆ = Ω) (hΩc : ∀ g ∈ Ω, (g : Hbar z) * α₀ = α₀ * g)
    (hZ : ∀ x ∈ Xsub S a, rhoZ S x = 1) :
    Ω.map (Xsub S a).subtype ≤ Subgroup.normalizer (Lbar S a : Set (Hbar z)) := by
  obtain ⟨hA2, haα⟩ := mem_A2set_and_aVec_mem_of_mem_Rbar h hα₀ hα₀1
  have hP : ⁅Ω.map (Xsub S a).subtype, Ω.map (Xsub S a).subtype⁆ =
      Ω.map (Xsub S a).subtype := by
    rw [← Subgroup.map_commutator, hΩ]
  refine le_trans (le_CH_of_perfect (S := S) h hP hA2 haα ?_ ?_) (CH_le_normalizer_Lbar S a)
  · rintro _ ⟨g, hg, rfl⟩
    exact hΩc g hg
  · intro x hx v hv
    have hxX : (QuotientGroup.mk x : Hbar z) ∈ Xsub S a := by
      obtain ⟨g, -, hgx⟩ := hx
      rw [← hgx]
      exact g.2
    have h2 := rhoZ_mk S x ⟨v, hv⟩
    rw [hZ _ hxX, MulAut.one_apply] at h2
    exact h2.symm

theorem eq_one_or_eq_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2)
    {x : G} (hx : x ≠ 1) (y : G) : y = 1 ∨ y = x := by
  classical
  have := Fintype.ofFinite G
  by_contra hne
  push Not at hne
  have h3 : ({1, x, y} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne.2.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hx.symm, hne.1.symm⟩
  have := Finset.card_le_univ ({1, x, y} : Finset G)
  rw [Fintype.card_eq_nat_card] at this
  omega

theorem card_Lbar_le_and_exists_of_sp (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1)
    (hZ : ∀ x ∈ Xsub S a, rhoZ S x = 1)
    (ψ : Hbar z ≃* ↥(Xsub S a) × Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hψ : ∀ p, ψ.symm p = (p.1 : Hbar z) * p.2)
    {Ω K : Subgroup ↥(Xsub S a)} (hΩ : ⁅Ω, Ω⁆ = Ω)
    (hΩc : ∀ g ∈ Ω, (g : Hbar z) * α₀ = α₀ * g) (hKΩ : K ≤ Ω)
    (h4 : ∀ E' : Subgroup ↥(Xsub S a), (∀ x ∈ E', (x : Hbar z) * α₀ = α₀ * x) →
      IsPGroup 2 E' → Ω ≤ Subgroup.normalizer (E' : Set ↥(Xsub S a)) → E' ≤ K)
    (h5 : ∀ E' : Subgroup ↥(Xsub S a), alphaInX S h hα₀ ∈ E' → E' ≤ K →
      Ω ≤ Subgroup.normalizer (E' : Set ↥(Xsub S a)) →
      E' = Subgroup.zpowers (alphaInX S h hα₀) ∨ E' = K) :
    Nat.card ↥(Lbar S a) ≤ 2 * Nat.card K ∧
      ∃ β ∈ Lbar S a, β ≠ 1 ∧ β ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) ∧
        Lbar S a ≤ Xsub S a ⊔ Subgroup.zpowers β := by
  classical
  have hψX : ∀ x : ↥(Xsub S a), ψ (x : Hbar z) = (x, 1) := by
    intro x
    apply ψ.symm.injective
    rw [MulEquiv.symm_apply_apply, hψ]
    simp
  have hψdec : ∀ g : Hbar z, g = ((ψ g).1 : Hbar z) * (ψ g).2 := by
    intro g
    have := hψ (ψ g)
    rw [MulEquiv.symm_apply_apply] at this
    exact this
  let f : Hbar z →* ↥(Xsub S a) := (MonoidHom.fst _ _).comp ψ.toMonoidHom
  have hf : ∀ g, f g = (ψ g).1 := fun _ => rfl
  let Ehat : Subgroup ↥(Xsub S a) := (Lbar S a).map f
  have hΩN := le_normalizer_Lbar_of_perfect S h hα₀ hα₀1 hΩ hΩc hZ
  have hconj : ∀ g ∈ Ω, ∀ y ∈ Ehat, g * y * g⁻¹ ∈ Ehat := by
    intro g hg y hy
    obtain ⟨l, hl, rfl⟩ := hy
    have hgN : (g : Hbar z) ∈ Subgroup.normalizer (Lbar S a : Set (Hbar z)) :=
      hΩN ⟨g, hg, rfl⟩
    refine ⟨(g : Hbar z) * l * (g : Hbar z)⁻¹, (Subgroup.mem_normalizer_iff.mp hgN l).mp hl, ?_⟩
    rw [map_mul, map_mul, map_inv, hf, hψX]
  have hEN : Ω ≤ Subgroup.normalizer (Ehat : Set ↥(Xsub S a)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj g hg y hy, fun hy => ?_⟩
    have := hconj g⁻¹ (inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hEc : ∀ x ∈ Ehat, (x : Hbar z) * α₀ = α₀ * x := by
    rintro _ ⟨l, hl, rfl⟩
    have hla : l * α₀ = α₀ * l :=
      (Subgroup.mem_centralizer_iff.mp (Lbar_le_centralizer S h hα₀ hl) α₀
        (Set.mem_singleton _)).symm
    have hα₀X : α₀ ∈ Xsub S a := h.Rbar_le_Xsub hα₀
    have := congrArg (fun g => ((ψ g).1 : Hbar z)) hla
    simp only [map_mul, Prod.fst_mul, Subgroup.coe_mul] at this
    rw [hψX ⟨α₀, hα₀X⟩] at this
    exact this
  have hE2 : IsPGroup 2 Ehat :=
    (isElemAbelian_Lbar S h.mem_Q h.isConj).isPGroup.map f
  have hEK : Ehat ≤ K := h4 Ehat hEc hE2 hEN
  let fL : ↥(Lbar S a) →* ↥(Xsub S a) := f.comp (Lbar S a).subtype
  have hrange : fL.range = Ehat := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ∀ l ∈ fL.ker, ((l : ↥(Lbar S a)) : Hbar z) ∈
      Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z)) := by
    intro l hl
    refine ⟨l.2, ?_⟩
    have h1 : (ψ (l : Hbar z)).1 = 1 := hl
    rw [hψdec (l : Hbar z), h1]
    simp only [OneMemClass.coe_one, one_mul]
    exact (ψ (l : Hbar z)).2.2
  have hkercard : Nat.card fL.ker ≤ 2 := by
    have hinj : Function.Injective (fun l : fL.ker =>
        (⟨((l : ↥(Lbar S a)) : Hbar z), hker l l.2⟩ :
          ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))))) := by
      intro l₁ l₂ h12
      simp only [Subtype.mk.injEq] at h12
      exact Subtype.ext (Subtype.ext h12)
    exact (Nat.card_le_card_of_injective _ hinj).trans
      (card_inf_centralizer_Xsub_le_two S h h217)
  have hLcard : Nat.card ↥(Lbar S a) = Nat.card fL.ker * Nat.card fL.range :=
    (Subgroup.card_ker_mul_card_range fL).symm
  have hcard1 : Nat.card ↥(Lbar S a) ≤ 2 * Nat.card K := by
    rw [hLcard, hrange]
    exact Nat.mul_le_mul hkercard (Subgroup.card_le_of_le hEK)
  refine ⟨hcard1, ?_⟩
  let LX : Subgroup ↥(Xsub S a) := (Lbar S a).comap (Xsub S a).subtype
  have hdLX : alphaInX S h hα₀ ∈ LX := Rbar_le_Lbar S a hα₀
  have hLXE : LX ≤ Ehat := by
    intro x hx
    refine ⟨(x : Hbar z), hx, ?_⟩
    rw [hf, hψX]
  have hLXN : Ω ≤ Subgroup.normalizer (LX : Set ↥(Xsub S a)) := by
    intro g hg
    have hgN : (g : Hbar z) ∈ Subgroup.normalizer (Lbar S a : Set (Hbar z)) :=
      hΩN ⟨g, hg, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    change (y : Hbar z) ∈ Lbar S a ↔ ((g * y * g⁻¹ : ↥(Xsub S a)) : Hbar z) ∈ Lbar S a
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp hgN y
  rcases h5 LX hdLX (hLXE.trans hEK) hLXN with hLX | hLX
  ·
    exfalso
    apply false_of_card_Lbar_le_four S h
    have hLX2 : Nat.card LX ≤ 2 := by
      rw [hLX, Nat.card_zpowers]
      have h2 : (alphaInX S h hα₀) ^ 2 = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, coe_alphaInX, OneMemClass.coe_one]
        exact (isElemAbelian_Lbar S h.mem_Q h.isConj).2 α₀ (Rbar_le_Lbar S a hα₀)
      exact orderOf_le_of_pow_eq_one (by norm_num) h2
    let gL : ↥(Lbar S a) →* Subgroup.centralizer (Xsub S a : Set (Hbar z)) :=
      ((MonoidHom.snd _ _).comp ψ.toMonoidHom).comp (Lbar S a).subtype
    have hgker : Nat.card gL.ker ≤ Nat.card LX := by
      have hmem : ∀ l ∈ gL.ker, ((l : ↥(Lbar S a)) : Hbar z) ∈ Xsub S a := by
        intro l hl
        have h1 : (ψ (l : Hbar z)).2 = 1 := hl
        rw [hψdec (l : Hbar z), h1, OneMemClass.coe_one, mul_one]
        exact (ψ (l : Hbar z)).1.2
      have hinj : Function.Injective (fun l : gL.ker =>
          (⟨⟨((l : ↥(Lbar S a)) : Hbar z), hmem l l.2⟩, (l : ↥(Lbar S a)).2⟩ : ↥LX)) := by
        intro l₁ l₂ h12
        have h' : ((l₁ : ↥(Lbar S a)) : Hbar z) = ((l₂ : ↥(Lbar S a)) : Hbar z) :=
          congrArg (fun x : ↥LX => ((x : ↥(Xsub S a)) : Hbar z)) h12
        exact Subtype.ext (Subtype.ext h')
      exact Nat.card_le_card_of_injective _ hinj
    have hgrange : Nat.card gL.range ≤ 2 := by
      have h2 : IsPGroup 2 gL.range :=
        ((isElemAbelian_Lbar S h.mem_Q h.isConj).isPGroup.of_surjective
          gL.rangeRestrict gL.rangeRestrict_surjective)
      obtain ⟨n, hn⟩ := h2.exists_card_eq
      have hdvd : Nat.card gL.range ∣ 6 :=
        (Subgroup.card_subgroup_dvd_card gL.range).trans
          (card_centralizer_Xsub_dvd_six S h h217)
      rw [hn] at hdvd ⊢
      rcases n with _ | _ | n
      · norm_num
      · norm_num
      · exfalso
        have : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ n + 2)).trans hdvd
        norm_num at this
    rw [← Subgroup.card_ker_mul_card_range gL]
    calc Nat.card gL.ker * Nat.card gL.range ≤ 2 * 2 :=
          Nat.mul_le_mul (hgker.trans hLX2) hgrange
      _ = 4 := rfl
  ·
    have hx1 : ∀ l ∈ Lbar S a, (ψ l).1 ∈ LX := fun l hl => by
      rw [hLX]; exact hEK ⟨l, hl, rfl⟩
    have hc : ∀ l ∈ Lbar S a, ((ψ l).2 : Hbar z) ∈ Lbar S a := by
      intro l hl
      have : ((ψ l).2 : Hbar z) = ((ψ l).1 : Hbar z)⁻¹ * l := by
        have hd := hψdec l
        calc ((ψ l).2 : Hbar z)
            = ((ψ l).1 : Hbar z)⁻¹ * (((ψ l).1 : Hbar z) * (ψ l).2) := by group
          _ = ((ψ l).1 : Hbar z)⁻¹ * l := by rw [← hd]
      rw [this]
      exact mul_mem (inv_mem (hx1 l hl)) hl
    have hex : ∃ l ∈ Lbar S a, ((ψ l).2 : Hbar z) ≠ 1 := by
      by_contra hno
      push Not at hno
      have hLX' : ∀ l ∈ Lbar S a, l ∈ Xsub S a := by
        intro l hl
        rw [hψdec l, hno l hl, mul_one]
        exact ((ψ l).1).2
      obtain ⟨hA2, -⟩ := mem_A2set_and_aVec_mem_of_mem_Rbar h hα₀ hα₀1
      have hP : ⁅Ω.map (Xsub S a).subtype, Ω.map (Xsub S a).subtype⁆ =
          Ω.map (Xsub S a).subtype := by
        rw [← Subgroup.map_commutator, hΩ]
      have hfix := rhoLin_apply_eq_self_of_perfect S hP hA2
        (by rintro _ ⟨g, hg, rfl⟩; exact hΩc g hg)
      apply h.not_forall_Lbar_fix_commSpace (fun α hα β hβ => stroth78_35 S h h217 h3 hα hβ) hA2
      intro l hl v hv
      have hlX := hLX' l hl
      have hψl : ψ l = (⟨l, hlX⟩, 1) := hψX ⟨l, hlX⟩
      have hlΩ : l ∈ Ω.map (Xsub S a).subtype := by
        refine ⟨⟨l, hlX⟩, hKΩ (hEK ⟨l, hl, ?_⟩), rfl⟩
        rw [hf, hψl]
      exact hfix l hlΩ v hv
    obtain ⟨l₀, hl₀, hβ1⟩ := hex
    refine ⟨((ψ l₀).2 : Hbar z), hc l₀ hl₀, hβ1, (ψ l₀).2.2, ?_⟩
    intro l hl
    have hcl : ((ψ l).2 : Hbar z) = 1 ∨ ((ψ l).2 : Hbar z) = ((ψ l₀).2 : Hbar z) := by
      have hT := card_inf_centralizer_Xsub_le_two S h h217
      have hne : (⟨((ψ l₀).2 : Hbar z), hc l₀ hl₀, (ψ l₀).2.2⟩ :
          ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z)))) ≠ 1 := fun h' =>
        hβ1 (congrArg Subtype.val h')
      rcases eq_one_or_eq_of_card_le_two hT hne
          (y := ⟨((ψ l).2 : Hbar z), hc l hl, (ψ l).2.2⟩) with h' | h'
      · left
        exact congrArg (fun t : ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) =>
          (t : Hbar z)) h'
      · right
        exact congrArg (fun t : ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) =>
          (t : Hbar z)) h'
    rw [hψdec l]
    refine mul_mem (Subgroup.mem_sup_left ((ψ l).1).2) ?_
    rcases hcl with h' | h'
    · rw [h']; exact one_mem _
    · rw [h']; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem sp_data_of_mulEquiv {X : Type} [Group X] {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (Ψ : X ≃* TauCeti.BilinForm.isometryGroup b) {d : X} {u : Fin (2 * m) → ZMod 2}
    (hu : u ≠ 0) (hd : Ψ d = Orth2.spT (f := b) halt u) :
    ∃ Ω K : Subgroup X, ⁅Ω, Ω⁆ = Ω ∧ (∀ g ∈ Ω, g * d = d * g) ∧ K ≤ Ω ∧
      Nat.card K = 2 ^ (2 * m - 1) ∧
      (∀ E' : Subgroup X, (∀ x ∈ E', x * d = d * x) → IsPGroup 2 E' →
        Ω ≤ Subgroup.normalizer (E' : Set X) → E' ≤ K) ∧
      (∀ E' : Subgroup X, d ∈ E' → E' ≤ K → Ω ≤ Subgroup.normalizer (E' : Set X) →
        E' = Subgroup.zpowers d ∨ E' = K) := by
  have hb : b.IsAlt := halt
  have hbn := Orth2.nondegenerate_of_isAlt halt hnd
  have hk : Module.finrank (ZMod 2) (Fin (2 * m) → ZMod 2) = 2 * m := Module.finrank_fin_fun _
  have hn : 5 ≤ Module.finrank (ZMod 2) (Fin (2 * m) → ZMod 2) := by omega
  let Ω := (Orth2.spOmega hb u).comap Ψ.toMonoidHom
  let K := (Orth2.spRadical b u).comap Ψ.toMonoidHom
  have hmap : ∀ A : Subgroup (TauCeti.BilinForm.isometryGroup b),
      A.comap Ψ.toMonoidHom = A.map Ψ.symm.toMonoidHom := fun A =>
    (Subgroup.map_equiv_eq_comap_symm Ψ.symm A).symm
  have hcomap : ∀ A : Subgroup X, (A.map Ψ.toMonoidHom).comap Ψ.toMonoidHom = A := fun A =>
    Subgroup.comap_map_eq_self_of_injective Ψ.injective A
  have hnorm : ∀ A : Subgroup X, Ω ≤ Subgroup.normalizer (A : Set X) →
      Orth2.spOmega hb u ≤ Subgroup.normalizer
        ((A.map Ψ.toMonoidHom : Subgroup _) : Set (TauCeti.BilinForm.isometryGroup b)) := by
    intro A hA ρ hρ
    have hρ' : Ψ.symm ρ ∈ Ω := by
      change Ψ (Ψ.symm ρ) ∈ Orth2.spOmega hb u
      rw [MulEquiv.apply_symm_apply]; exact hρ
    have hN := hA hρ'
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Ψ.symm ρ * x * (Ψ.symm ρ)⁻¹, (hN x).mp hx, ?_⟩
      change Ψ (Ψ.symm ρ * x * (Ψ.symm ρ)⁻¹) = _
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rfl
    · rintro ⟨x, hx, hxe⟩
      refine ⟨Ψ.symm y, ?_, MulEquiv.apply_symm_apply _ _⟩
      have : Ψ.symm y = (Ψ.symm ρ)⁻¹ * x * Ψ.symm ρ := by
        apply Ψ.injective
        rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        change Ψ x = _ at hxe
        rw [hxe]
        group
      rw [this]
      have := (hN ((Ψ.symm ρ)⁻¹ * x * Ψ.symm ρ)).mpr (by
        rw [show Ψ.symm ρ * ((Ψ.symm ρ)⁻¹ * x * Ψ.symm ρ) * (Ψ.symm ρ)⁻¹ = x by group]
        exact hx)
      exact this
  refine ⟨Ω, K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ⁅(Orth2.spOmega hb u).comap Ψ.toMonoidHom, (Orth2.spOmega hb u).comap Ψ.toMonoidHom⁆ =
      (Orth2.spOmega hb u).comap Ψ.toMonoidHom
    rw [hmap, ← Subgroup.map_commutator, Orth2.commutator_spOmega hb hbn hn u]
  · intro g hg
    have h1 := Orth2.spOmega_le_centralizer hb hbn hg
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    apply Ψ.injective
    rw [map_mul, map_mul, hd]
    exact h1
  · exact Subgroup.comap_mono (Orth2.spRadical_le_spOmega hb hbn hn hu)
  · rw [Nat.card_congr ((Subgroup.equivMapOfInjective _ _ Ψ.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective Ψ.surjective _))).toEquiv,
      Orth2.card_spRadical hb hbn hu, hk]
  · intro E' hE'c hE'2 hE'N
    have hfix : ∀ g ∈ E'.map Ψ.toMonoidHom,
        (g : (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] _) u = u := by
      rintro _ ⟨x, hx, rfl⟩
      refine Orth2.apply_eq_of_commute_spT hb hbn hu ?_
      change Ψ x * _ = _ * Ψ x
      rw [← hd, ← map_mul, ← map_mul, hE'c x hx]
    have := Orth2.le_spRadical_of_isPGroup hb hbn hn hu hfix (hE'2.map _) (hnorm E' hE'N)
    rw [← hcomap E']
    exact Subgroup.comap_mono this
  · intro E' hdE hE'K hE'N
    have h1 : Orth2.spT hb u ∈ E'.map Ψ.toMonoidHom := ⟨d, hdE, hd⟩
    have h2 : E'.map Ψ.toMonoidHom ≤ Orth2.spRadical b u := by
      rw [Subgroup.map_le_iff_le_comap]; exact hE'K
    rcases Orth2.eq_zpowers_or_eq_spRadical hb hbn hn hu h1 h2 (hnorm E' hE'N) with h | h
    · left
      have hz : Subgroup.zpowers (Ψ d) = (Subgroup.zpowers d).map Ψ.toMonoidHom :=
        (MonoidHom.map_zpowers Ψ.toMonoidHom d).symm
      rw [← hcomap E', h, ← hd, hz, hcomap]
    · right
      rw [← hcomap E', h]

theorem card_Lbar_le_and_exists (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hO₀ : fischerLinearModel (threeResidualClass (alphaInX S h hα₀))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZX : Subgroup.center ↥(Xsub S a) = ⊥) :
    Nat.card ↥(Lbar S a) ≤ 2 ^ (2 * m) ∧
      ∃ β ∈ Lbar S a, β ≠ 1 ∧ β ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) ∧
        Lbar S a ≤ (threeResidualJoin (alphaInX S h hα₀)).map (Xsub S a).subtype ⊔
          Subgroup.zpowers β := by
  have hαT : α₀ ∈ Tset S a := h.mem_Tset_of_mem_Rbar hα₀ hα₀1
  have hαE : ((alphaInX S h hα₀ : ↥(Xsub S a)) : Hbar z) ∈ Eset S a := Tset_subset_Eset S a hαT
  have hW := threeResidualQuot_eq_top_of_sp S h h217 h3 hαE hm halt hnd hO₀
  let eX : ↥(Xsub S a) ≃* ↥(threeResidualQuot (alphaInX S h hα₀)) :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZX.symm)).trans (quotCenterEquiv hW)
  obtain ⟨Φ, hΦ⟩ := Orth2.exists_mulEquiv_isometryGroup_of_fischerLinearModel halt hO₀
  have heX : eX (alphaInX S h hα₀) = alphaBar S h hα₀ := by
    apply Subtype.ext
    change ((quotCenterEquiv hW _ : ↥(threeResidualQuot (alphaInX S h hα₀))) :
      ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) = _
    rw [coe_quotCenterEquiv]
    rfl
  obtain ⟨u, hu0, hu⟩ := (hΦ (alphaBar S h hα₀)).mp (alphaBar_mem S h hα₀)
  let Ψ := eX.trans Φ
  have hΨ : Ψ (alphaInX S h hα₀) = Orth2.spT (f := b) halt u := by
    change Φ (eX (alphaInX S h hα₀)) = _
    rw [heX, hu]
  obtain ⟨Ω, K, hΩ, hΩc, hKΩ, hKcard, h4, h5⟩ := sp_data_of_mulEquiv hm halt hnd Ψ hu0 hΨ
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_Hbar_prod S h h217 h3 hαE hm halt hnd hO₀ hZX
  have hZ := rhoZ_Xsub_eq_one S h h217 h3 hαT hm halt hnd hO₀
  have hcoe : ∀ x y : ↥(Xsub S a), x * y = y * x ↔ (x : Hbar z) * y = y * x := fun x y =>
    ⟨fun h' => by rw [← Subgroup.coe_mul, h', Subgroup.coe_mul],
      fun h' => Subtype.ext (by rw [Subgroup.coe_mul, h', Subgroup.coe_mul])⟩
  obtain ⟨hcard, hβ⟩ := card_Lbar_le_and_exists_of_sp S h h217 h3 hα₀ hα₀1 hZ ψ hψ hΩ
    (fun g hg => (hcoe g _).mp (hΩc g hg)) hKΩ
    (fun E' hE'c hE'2 hE'N => h4 E' (fun x hx => (hcoe x _).mpr (hE'c x hx)) hE'2 hE'N) h5
  have hWX : (threeResidualJoin (alphaInX S h hα₀)).map (Xsub S a).subtype = Xsub S a := by
    rw [threeResidualJoin_eq_top_of_center_eq_bot hZX hW, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine ⟨?_, by rw [hWX]; exact hβ⟩
  calc Nat.card ↥(Lbar S a) ≤ 2 * Nat.card K := hcard
    _ = 2 ^ (2 * m) := by
      rw [hKcard, ← pow_succ']
      congr 1
      omega

theorem card_Lbar_le (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hO₀ : fischerLinearModel (threeResidualClass (alphaInX S h hα₀))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZX : Subgroup.center ↥(Xsub S a) = ⊥) :
    Nat.card ↥(Lbar S a) ≤ 2 ^ (2 * m) :=
  (card_Lbar_le_and_exists S h h217 h3 hα₀ hα₀1 hm halt hnd hO₀ hZX).1

theorem exists_mem_Lbar_centralizer (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hO₀ : fischerLinearModel (threeResidualClass (alphaInX S h hα₀))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZX : Subgroup.center ↥(Xsub S a) = ⊥) :
    ∃ β ∈ Lbar S a, β ≠ 1 ∧ β ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) ∧
      Lbar S a ≤ (threeResidualJoin (alphaInX S h hα₀)).map (Xsub S a).subtype ⊔
        Subgroup.zpowers β :=
  (card_Lbar_le_and_exists S h h217 h3 hα₀ hα₀1 hm halt hnd hO₀ hZX).2

theorem le_two_mul (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hO₀ : fischerLinearModel (threeResidualClass (alphaInX S h hα₀))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZX : Subgroup.center ↥(Xsub S a) = ⊥) :
    w ≤ 2 * m := by
  have hcard := card_Lbar_le S h h217 h3 hα₀ hα₀1 hm halt hnd hO₀ hZX
  have h18 := card_Lbar_ge_of_width_r S h.isConj h.mem_Q h.not_mem_ZQ h.mem_Qa h.card_F
    (r := 1) (by rw [card_Rbar_eq_two S h h217 h3, pow_one])
  have e : 1 + w - 1 = w := by omega
  rw [e] at h18
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (h18.trans hcard)

theorem even_card_centralizer_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hO₀ : fischerLinearModel (threeResidualClass (alphaInX S h hα₀))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZX : Subgroup.center ↥(Xsub S a) = ⊥) :
    Even (Nat.card (Subgroup.centralizer (Xsub S a : Set (Hbar z)))) := by
  obtain ⟨β, hβL, hβ1, hβC, -⟩ := exists_mem_Lbar_centralizer S h h217 h3 hα₀ hα₀1 hm halt hnd
    hO₀ hZX
  have h2 : β ^ 2 = 1 := (isElemAbelian_Lbar S h.mem_Q h.isConj).2 β hβL
  have hord : orderOf (⟨β, hβC⟩ : Subgroup.centralizer (Xsub S a : Set (Hbar z))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime h2 hβ1
  rw [even_iff_two_dvd, ← hord]
  exact orderOf_dvd_natCard _

end Sec4SixW

end CFSG.RankThree.GF2n.Stroth78
