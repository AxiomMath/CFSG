module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs2
public import CFSG.Quasithin.Background.HSp4A6Pair
public import Certificates.Certificate7067
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUA6Inn
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUA6Def
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_normal_of_alt_six {M : Type*} [Group M]
    (e : M ≃* MulAut ↥(alternatingGroup (Fin 6))) {N : Subgroup M}
    (hN : Nonempty (↥N ≃* ↥(alternatingGroup (Fin 6)))) : N.Normal := by
  obtain ⟨f⟩ := hN
  have h := CFSG.EvenSporadicStandard.Fin76b.A6X.inn_unique
    ((N.equivMapOfInjective e.toMonoidHom e.injective).symm.trans f)
  have hN : N = (N.map e.toMonoidHom).comap e.toMonoidHom :=
    (Subgroup.comap_map_eq_self_of_injective e.injective N).symm
  rw [hN, h]
  exact Subgroup.Normal.comap
    (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _) e.toMonoidHom

open CFSG.Quasithin.H CFSG.Quasithin.H.PairG in
theorem s16t_pair_model_aux {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (GL ι K)} (θ : ↥Γ →* ↥Γ) {W : Type*} [CommGroup W]
    {L : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W}
    (hinf : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = ⊤)
    (hU₁ : ∀ h : ↥L, ∀ u ∈ I₁, (h : MulAut W) u ∈ I₁)
    (hU₂ : ∀ h : ↥L, ∀ u ∈ I₂, (h : MulAut W) u ∈ I₂)
    (π : ↥Γ →* ↥L) (hπs : Function.Surjective π)
    (e₁ : ↥I₁ ≃* StdMod ι K) (e₂ : ↥I₂ ≃* StdMod ι K)
    (he₁ : ∀ (γ : ↥Γ) (u : ↥I₁) (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ I₁),
      e₁ ⟨_, hu⟩ = matAut (γ : GL ι K) (e₁ u))
    (he₂ : ∀ (γ : ↥Γ) (w : ↥I₂) (hw : ((π γ : ↥L) : MulAut W) (w : W) ∈ I₂),
      e₂ ⟨_, hw⟩ = matAut ((θ γ : ↥Γ) : GL ι K) (e₂ w)) :
    ∃ e : W ≃* PairMod ι K, L.map (congrHom e) = pairImg Γ θ ∧
      I₁.map e.toMonoidHom = V₁ ι K ∧ I₂.map e.toMonoidHom = V₂ ι K := by
  classical
  let μ : ↥I₁ × ↥I₂ →* W := I₁.subtype.coprod I₂.subtype
  have hμ : Function.Bijective μ := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      have h' : (a : W) * b = c * d := h
      obtain ⟨h1, h2⟩ := Pair.decomp_unique hinf a.2 b.2 c.2 d.2 h'
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · intro v
      obtain ⟨a, ha, b, hb, hab⟩ := Pair.exists_decomp hsup v
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  let dec : (↥I₁ × ↥I₂) ≃* W := MulEquiv.ofBijective μ hμ
  let e : W ≃* PairMod ι K := dec.symm.trans (MulEquiv.prodCongr e₁ e₂)
  have hpair : ∀ γ : ↥Γ, congrHom e ((π γ : ↥L) : MulAut W) = pairHom Γ θ γ := by
    intro γ
    refine MulEquiv.ext fun x => ?_
    rw [congrHom_apply, pairHom_apply, pairAut_apply]
    set a := e₁.symm x.1 with ha
    set b := e₂.symm x.2 with hb
    have hx : e.symm x = (a : W) * b := rfl
    rw [hx, map_mul]
    have ha' : ((π γ : ↥L) : MulAut W) (a : W) ∈ I₁ := hU₁ _ a a.2
    have hb' : ((π γ : ↥L) : MulAut W) (b : W) ∈ I₂ := hU₂ _ b b.2
    have hdec : dec.symm (((π γ : ↥L) : MulAut W) (a : W) * ((π γ : ↥L) : MulAut W) (b : W)) =
        (⟨_, ha'⟩, ⟨_, hb'⟩) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change MulEquiv.prodCongr e₁ e₂ (dec.symm _) = _
    rw [hdec]
    change (e₁ ⟨_, ha'⟩, e₂ ⟨_, hb'⟩) = _
    rw [he₁ γ a ha', he₂ γ b hb', ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  have hleft : ∀ a : ↥I₁, e (a : W) = (e₁ a, 1) := by
    intro a
    have : dec.symm (a : W) = (a, 1) := by
      rw [MulEquiv.symm_apply_eq]
      exact (mul_one _).symm
    change MulEquiv.prodCongr e₁ e₂ (dec.symm (a : W)) = _
    rw [this]
    exact Prod.ext rfl (map_one e₂)
  have hright : ∀ b : ↥I₂, e (b : W) = (1, e₂ b) := by
    intro b
    have : dec.symm (b : W) = (1, b) := by
      rw [MulEquiv.symm_apply_eq]
      exact (one_mul _).symm
    change MulEquiv.prodCongr e₁ e₂ (dec.symm (b : W)) = _
    rw [this]
    exact Prod.ext (map_one e₁) rfl
  refine ⟨e, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨γ, hγ⟩ := hπs ⟨h, hh⟩
      have : h = ((π γ : ↥L) : MulAut W) := by rw [hγ]
      rw [this, hpair]
      exact pairHom_mem_pairImg _ _ γ
    · rintro ⟨γ, rfl⟩
      exact ⟨_, (π γ).2, hpair γ⟩
  · ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [mem_V₁]
      exact congrArg Prod.snd (hleft ⟨a, ha⟩)
    · intro hx
      rw [mem_V₁] at hx
      refine ⟨((e₁.symm x.1 : ↥I₁) : W), (e₁.symm x.1).2, ?_⟩
      change e ((e₁.symm x.1 : ↥I₁) : W) = x
      rw [hleft, MulEquiv.apply_symm_apply]
      exact Prod.ext rfl hx.symm
  · ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [mem_V₂]
      exact congrArg Prod.fst (hright ⟨b, hb⟩)
    · intro hx
      rw [mem_V₂] at hx
      refine ⟨((e₂.symm x.2 : ↥I₂) : W), (e₂.symm x.2).2, ?_⟩
      change e ((e₂.symm x.2 : ↥I₂) : W) = x
      rw [hright, MulEquiv.apply_symm_apply]
      exact Prod.ext hx.symm rfl

open CFSG.Quasithin.H CFSG.Quasithin.H.PairG in
theorem s16t_injective_of_natural {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {Γ : Subgroup (GL ι K)} (p : ↥Γ →* ↥L) (e : ↥I ≃* StdMod ι K)
    (he : ∀ (γ : ↥Γ) (u : ↥I) (hu : ((p γ : ↥L) : MulAut W) (u : W) ∈ I),
      e ⟨_, hu⟩ = matAut (γ : GL ι K) (e u)) : Function.Injective p := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply Subtype.ext
  apply Units.ext
  show ((γ : GL ι K) : Matrix ι ι K) = 1
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [Matrix.one_mulVec]
  obtain ⟨u, hu⟩ := e.surjective (Multiplicative.ofAdd v)
  have h1 := he γ u (by rw [hγ]; exact u.2)
  have h2 : (⟨((p γ : ↥L) : MulAut W) (u : W), by rw [hγ]; exact u.2⟩ : ↥I) = u := by
    apply Subtype.ext
    show ((p γ : ↥L) : MulAut W) (u : W) = u
    rw [hγ]
    rfl
  rw [h2, hu] at h1
  exact (congrArg Multiplicative.toAdd h1).symm

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.PairG CFSG.Quasithin.H.Sp4A6 in
theorem s16t_natural_gamma
    {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {I : Subgroup W}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥L} (hπ : (FFModel.altDn 6).RealizesVia L I ⊥ π) :
    ∃ e : ↥I ≃* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2),
      ∀ (γ : ↥Γ₆) (u : ↥I)
        (hu : (((π.comp psiEquiv.symm.toMonoidHom) γ : ↥L) : MulAut W) (u : W) ∈ I),
        e ⟨_, hu⟩ = matAut (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (e u) := by
  obtain ⟨e₁, he₁⟩ := exists_natural hπ
  refine ⟨e₁, fun γ u hu => ?_⟩
  have h := he₁ (psiEquiv.symm γ) u hu
  have e : psiHom ((psiEquiv.symm γ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
      (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
    have := congrArg Subtype.val (psiEquiv.apply_symm_apply γ)
    exact this
  rw [← e]
  exact h

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.PairG CFSG.Quasithin.H.Sp4A6 in
theorem s16t_exists_pair_model
    {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {I₁ I₂ : Subgroup W}
    (hinf : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = ⊤)
    (h₁ : AlternatingNatural L I₁ ⊥ 6) (h₂ : AlternatingNatural L I₂ ⊥ 6)
    (hne : ∀ ψ ∈ Subgroup.centralizer (L : Set (MulAut W)), I₁.map ψ.toMonoidHom ≠ I₂) :
    ∃ e : W ≃* PairMod (Fin 2 ⊕ Fin 2) (ZMod 2), L.map (congrHom e) = pairImg Γ₆ tau₆ := by
  classical
  obtain ⟨π₁, hπ₁⟩ := h₁
  obtain ⟨π₂, hπ₂⟩ := h₂
  have hU₁ : ∀ h : ↥L, ∀ u ∈ I₁, (h : MulAut W) u ∈ I₁ := hπ₁.2.2.2.1
  have hU₂ : ∀ h : ↥L, ∀ u ∈ I₂, (h : MulAut W) u ∈ I₂ := hπ₂.2.2.2.1
  obtain ⟨e₁, he₁⟩ := s16t_natural_gamma hπ₁
  obtain ⟨e₂, he₂⟩ := s16t_natural_gamma hπ₂
  set p₁ : ↥Γ₆ →* ↥L := π₁.comp psiEquiv.symm.toMonoidHom
  set p₂ : ↥Γ₆ →* ↥L := π₂.comp psiEquiv.symm.toMonoidHom
  have hp₁s : Function.Surjective p₁ := hπ₁.1.comp psiEquiv.symm.surjective
  have hp₂s : Function.Surjective p₂ := hπ₂.1.comp psiEquiv.symm.surjective
  have hp₁i : Function.Injective p₁ := s16t_injective_of_natural p₁ e₁ he₁
  have hp₂i : Function.Injective p₂ := s16t_injective_of_natural p₂ e₂ he₂
  let q₁ : ↥Γ₆ ≃* ↥L := MulEquiv.ofBijective p₁ ⟨hp₁i, hp₁s⟩
  let q₂ : ↥Γ₆ ≃* ↥L := MulEquiv.ofBijective p₂ ⟨hp₂i, hp₂s⟩
  let α : MulAut ↥Γ₆ := q₁.trans q₂.symm
  have hα : ∀ γ, p₂ (α γ) = p₁ γ := fun γ => q₂.apply_symm_apply (q₁ γ)
  have key : ∀ (θ : ↥Γ₆ →* ↥Γ₆) (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)),
      (∀ γ, ((α γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) =
        B * ((θ γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * B⁻¹) →
      ∃ e : W ≃* PairMod (Fin 2 ⊕ Fin 2) (ZMod 2), L.map (congrHom e) = pairImg Γ₆ θ ∧
        I₁.map e.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) (ZMod 2) ∧
        I₂.map e.toMonoidHom = V₂ (Fin 2 ⊕ Fin 2) (ZMod 2) := by
    intro θ B hB
    let e₂' : ↥I₂ ≃* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) := e₂.trans (matAut B⁻¹)
    refine s16t_pair_model_aux θ hinf hsup hU₁ hU₂ p₁ hp₁s e₁ e₂' he₁ (fun γ w hw => ?_)
    have hw' : ((p₂ (α γ) : ↥L) : MulAut W) (w : W) ∈ I₂ := by rw [hα]; exact hw
    have h1 : e₂ ⟨((p₂ (α γ) : ↥L) : MulAut W) (w : W), hw'⟩ =
        matAut ((α γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (e₂ w) := he₂ (α γ) w hw'
    have h2 : (⟨((p₁ γ : ↥L) : MulAut W) (w : W), hw⟩ : ↥I₂) =
        ⟨((p₂ (α γ) : ↥L) : MulAut W) (w : W), hw'⟩ := by
      apply Subtype.ext
      show ((p₁ γ : ↥L) : MulAut W) (w : W) = ((p₂ (α γ) : ↥L) : MulAut W) (w : W)
      rw [hα]
    have hmat : B⁻¹ * ((α γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) =
        ((θ γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * B⁻¹ := by
      rw [hB γ]
      group
    change matAut B⁻¹ (e₂ ⟨_, hw⟩) = matAut ((θ γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2))
      (matAut B⁻¹ (e₂ w))
    rw [h2, h1]
    calc matAut B⁻¹ (matAut ((α γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (e₂ w))
        = matHom (B⁻¹ * ((α γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2))) (e₂ w) := by
          rw [map_mul]
          rfl
      _ = matHom (((θ γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * B⁻¹) (e₂ w) := by rw [hmat]
      _ = matAut ((θ γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (matAut B⁻¹ (e₂ w)) := by
          rw [map_mul]
          rfl
  obtain ⟨⟨B, ε⟩, hBε⟩ := autΦ_surjective α
  cases ε
  ·
    exfalso
    have hB : ∀ γ, ((α γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) =
        (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) *
          (((MonoidHom.id ↥Γ₆) γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) *
          (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ := by
      intro γ
      rw [← hBε]
      exact coe_conjB B γ
    obtain ⟨e, he, hI₁, hI₂⟩ := key (MonoidHom.id ↥Γ₆) B hB
    set s := swapAut (Fin 2 ⊕ Fin 2) (ZMod 2)
    let ψ : MulAut W := (MulAut.congr e).symm s
    have hψc : congrHom e ψ = s := (MulAut.congr e).apply_symm_apply s
    have hψ : ∀ w, e (ψ w) = s (e w) := fun w =>
      (congrArg (fun x => e (ψ x)) (e.symm_apply_apply w)).symm.trans
        ((congrHom_apply e ψ (e w)).symm.trans (congrArg (fun f => f (e w)) hψc))
    have hmem₁ : ∀ w, e w ∈ V₁ (Fin 2 ⊕ Fin 2) (ZMod 2) ↔ w ∈ I₁ := fun w => by
      rw [← hI₁, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    have hmem₂ : ∀ w, e w ∈ V₂ (Fin 2 ⊕ Fin 2) (ZMod 2) ↔ w ∈ I₂ := fun w => by
      rw [← hI₂, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    have hψψ : ∀ w, ψ (ψ w) = w := fun w => by
      apply e.injective
      rw [hψ, hψ]
      rfl
    refine hne ψ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hc : congrHom e h ∈ pairImg Γ₆ (MonoidHom.id ↥Γ₆) := he ▸ ⟨h, hh, rfl⟩
      obtain ⟨γ, hγ⟩ := hc
      apply congrHom_injective e
      rw [map_mul, map_mul, ← hγ, hψc, pairHom_apply]
      exact (mul_inv_eq_iff_eq_mul.1 (swapAut_conj_pairAut (natAut Γ₆ γ) (natAut Γ₆ γ))).symm
    · ext w
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine (hmem₂ _).1 ?_
        change e (ψ a) ∈ V₂ (Fin 2 ⊕ Fin 2) (ZMod 2)
        rw [hψ, mem_V₂]
        exact mem_V₁.1 ((hmem₁ a).2 ha)
      · intro hw
        refine ⟨ψ w, ?_, hψψ w⟩
        refine (hmem₁ _).1 ?_
        rw [hψ, mem_V₁]
        exact mem_V₂.1 ((hmem₂ w).2 hw)
  · have hB : ∀ γ, ((α γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) =
        (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) *
          ((tau₆ γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) *
          (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ := by
      intro γ
      rw [← hBε]
      exact coe_conjB B (tau₆ γ)
    obtain ⟨e, he, -, -⟩ := key tau₆ (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) hB
    exact ⟨e, he⟩

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.PairG CFSG.Quasithin.H.Sp4A6 in
theorem s16t_aParam_lt_two_of_alt_pair
    {W : Type} [CommGroup W] [Finite W] {L M : Subgroup (MulAut W)} (hLM : L ≤ M)
    (hMA : Nonempty (↥M ≃* MulAut ↥(alternatingGroup (Fin 6))))
    (hL : UC22.IsAlt ↥L 6)
    (hsum : SumOfTwoInequiv (fun H U Z => AlternatingNatural H U Z 6) L ⊤ ⊥) :
    E3.aParam M < 2 ∧ 3 ≤ E3.mParam M := by
  obtain ⟨I₁, I₂, -, -, hI12, -, hU, hN₁, hN₂, hne⟩ := hsum
  have hinf : I₁ ⊓ I₂ = ⊥ := by
    rw [bot_sup_eq] at hI12
    exact le_bot_iff.1 hI12
  have hsup : I₁ ⊔ I₂ = ⊤ := by
    rw [bot_sup_eq] at hU
    exact hU
  obtain ⟨e, he⟩ := s16t_exists_pair_model hinf hsup hN₁ hN₂ hne
  obtain ⟨eM⟩ := hMA
  obtain ⟨eL⟩ := hL
  have hnorm : (L.subgroupOf M).Normal :=
    s16t_normal_of_alt_six eM ⟨(Subgroup.subgroupOfEquivOfLe hLM).trans eL⟩
  have hconj := (Subgroup.normal_subgroupOf_iff hLM).1 hnorm
  have hMN : M ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun x hx =>
    Subgroup.mem_normalizer_iff.2 fun h =>
      ⟨fun hh => hconj h x hh hx, fun hh => by
        have h1 := hconj _ x⁻¹ hh (M.inv_mem hx)
        rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at h1⟩
  haveI : Finite (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2)) := Finite.of_equiv W e.toEquiv
  have h2 : M.map (congrHom e) ≤ Sp4.pairNormSp (ZMod 2) :=
    (PairG.map_le_pairNorm tau₆ e he hMN).trans pairNorm_le
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
  refine ⟨?_, ?_⟩
  · rw [← aParam_map_congrHom e]
    exact Sp4.aParam_lt le_rfl hK h2
  · rw [← mParam_map_congrHom e]
    exact Sp4.le_mParam le_rfl hK h2

theorem s16t_aBar_lt_two_and_three_le_mBar_of_case168_1
    (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (h1 : Case168_1 D ⊥ V hV L) (hv : v1Sub D.M ⊥ V hV L = ⊥) :
    aBar D.M ⊥ V hV < 2 ∧ 3 ≤ mBar D.M ⊥ V hV := by
  obtain ⟨hMA, hL, hsum, -⟩ := h1
  have hLM : L ≤ D.M := hc.setting.hyp151.le
  have key : ∀ V₁ : Subgroup G, V₁ = ⊥ →
      SumOfTwoInequiv (fun H U Z => AlternatingNatural H U Z 6) (barSub V₁ V hV L)
        (⊤ : Subgroup (Vtil V₁ V hV)) ⊥ →
      SumOfTwoInequiv (fun H U Z => AlternatingNatural H U Z 6) (barSub ⊥ V hV L)
        (⊤ : Subgroup (Vtil ⊥ V hV)) ⊥ := by
    intro V₁ h0 hs
    subst h0
    exact hs
  exact s16t_aParam_lt_two_of_alt_pair (barSub_mono ⊥ V hV hLM) hMA hL (key _ hv hsum)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
