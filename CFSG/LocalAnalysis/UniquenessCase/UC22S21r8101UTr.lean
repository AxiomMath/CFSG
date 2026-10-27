module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XD
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UBar
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XF
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Cong
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Glauberman.Wielandt
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

section Generic

variable {Q : Type} [Group Q] [Finite Q]

theorem u81_not_swap {F₀ F₁ : Subgroup Q} (hinf : F₀ ⊓ F₁ = ⊥) (hbot : F₀ ≠ ⊥) {x : Q}
    (hN : x ∈ normalizer (F₀ : Set Q)) (hs : ∀ f ∈ F₀, x * f * x⁻¹ ∈ F₁) : False := by
  obtain ⟨f, hf, hf1⟩ := (Subgroup.bot_or_exists_ne_one F₀).resolve_left hbot
  have h : x * f * x⁻¹ ∈ F₀ ⊓ F₁ := ⟨(Subgroup.mem_normalizer_iff.1 hN f).1 hf, hs f hf⟩
  rw [hinf, Subgroup.mem_bot] at h
  exact hf1 (by simpa using h)

theorem u81_inner_of_transfer {F₀ F₁ : Subgroup Q} [IsMulCommutative (Outer ↥F₀)]
    (hinf : F₀ ⊓ F₁ = ⊥) (hbot : F₀ ≠ ⊥)
    (hcases : ∀ x : Q, (x ∈ normalizer (F₀ : Set Q) ∧ x ∈ normalizer (F₁ : Set Q)) ∨
      ((∀ f ∈ F₀, x * f * x⁻¹ ∈ F₁) ∧ ∀ f ∈ F₁, x * f * x⁻¹ ∈ F₀))
    {t : Q} (ht : ∀ f ∈ F₀, t * f * t⁻¹ ∈ F₁) {e : Q} (he : e ∈ commutator Q)
    (h₀ : ∃ x₀ ∈ F₀, ∀ f ∈ F₀, e * f * e⁻¹ = x₀ * f * x₀⁻¹) :
    ∃ x₁ ∈ F₁, ∀ f ∈ F₁, e * f * e⁻¹ = x₁ * f * x₁⁻¹ := by
  classical
  set N := normalizer (F₀ : Set Q) with hNdef
  have hsw : ∀ x, x ∉ N → (∀ f ∈ F₀, x * f * x⁻¹ ∈ F₁) ∧ ∀ f ∈ F₁, x * f * x⁻¹ ∈ F₀ :=
    fun x hx => (hcases x).resolve_left fun h => hx h.1
  have hsw' : ∀ x, x ∉ N → ∀ f ∈ F₁, x⁻¹ * f * x ∈ F₀ := fun x hx f hf => by
    have h := (hsw x⁻¹ fun h => hx (by simpa using N.inv_mem h)).2 f hf
    rwa [inv_inv] at h
  have hmulN : ∀ x y, x ∉ N → y ∉ N → x⁻¹ * y ∈ N := fun x y hx hy =>
    Subgroup.mem_normalizer_fintype fun f hf => by
      rw [show x⁻¹ * y * f * (x⁻¹ * y)⁻¹ = x⁻¹ * (y * f * y⁻¹) * x by group]
      exact hsw' x hx _ ((hsw y hy).1 f hf)
  have htN : t ∉ N := fun h => u81_not_swap hinf hbot h ht
  obtain ⟨x₀, hx₀, hc₀⟩ := h₀
  have heN : e ∈ N := Subgroup.mem_normalizer_fintype fun f hf => by
    rw [hc₀ f hf]
    exact F₀.mul_mem (F₀.mul_mem hx₀ hf) (F₀.inv_mem hx₀)
  have heN₁ : e ∈ normalizer (F₁ : Set Q) :=
    ((hcases e).resolve_right fun h => u81_not_swap hinf hbot heN h.1).2
  have hg : ∀ x : Q, x⁻¹ * e * x ∈ N := by
    intro x
    by_cases hx : x ∈ N
    · exact N.mul_mem (N.mul_mem (N.inv_mem hx) heN) hx
    · refine Subgroup.mem_normalizer_fintype fun f hf => ?_
      rw [show x⁻¹ * e * x * f * (x⁻¹ * e * x)⁻¹ = x⁻¹ * (e * (x * f * x⁻¹) * e⁻¹) * x by group]
      exact hsw' x hx _ ((Subgroup.mem_normalizer_iff.1 heN₁ _).1 ((hsw x hx).1 f hf))
  let φ : ↥N →* Abelianization (Outer ↥F₀) := Abelianization.of.comp
    ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥F₀)).comp
      F₀.normalizerMonoidHom)
  have hφ : ∀ (g : Q) (hgN : g ∈ N), φ ⟨g, hgN⟩ = 1 →
      ∃ y ∈ F₀, ∀ f ∈ F₀, g * f * g⁻¹ = y * f * y⁻¹ := by
    intro g hgN h1
    have h3 : _ ∈ (Abelianization.of : Outer ↥F₀ →* _).ker := h1
    rw [Abelianization.ker_of] at h3
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).1
      (Abelianization.commutator_subset_ker (MonoidHom.id _) h3)
    refine ⟨y, y.2, fun f hf => ?_⟩
    have h4 := congrArg (fun α : MulAut ↥F₀ => ((α ⟨f, hf⟩ : ↥F₀) : Q)) hy
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h4
    rw [h4, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have he1 : φ ⟨e, heN⟩ = 1 := by
    have h5 : F₀.normalizerMonoidHom ⟨e, heN⟩ = MulAut.conj ⟨x₀, hx₀⟩ := by
      ext f
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hc₀ f f.2, MulAut.conj_apply]
      rfl
    have h6 : MulAut.conj (⟨x₀, hx₀⟩ : ↥F₀) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥F₀ := MonoidHom.mem_range.2 ⟨_, rfl⟩
    change Abelianization.of (QuotientGroup.mk' _ (F₀.normalizerMonoidHom ⟨e, heN⟩)) = 1
    rw [h5, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 h6, map_one]
  haveI : Fintype (Q ⧸ N) := Fintype.ofFinite _
  have hV : φ.transfer e = 1 := Abelianization.commutator_subset_ker φ.transfer he
  rw [CFSG.LocalAnalysis.GLTheoremB.MovingAround.GlaubermanB.transfer_eq_prod_of_conj_mem φ e hg,
    Fintype.prod_eq_single (t : Q ⧸ N) ?_] at hV
  · have hst : (Quotient.out (t : Q ⧸ N))⁻¹ * t ∈ N :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' (t : Q ⧸ N))
    set s := Quotient.out (t : Q ⧸ N)
    have hsN : s ∉ N := fun h => htN (by simpa using N.mul_mem h hst)
    obtain ⟨y, hy, hcy⟩ := hφ _ (hg s) hV
    refine ⟨s * y * s⁻¹, (hsw s hsN).1 y hy, fun f hf => ?_⟩
    have h6 := hcy _ (hsw' s hsN f hf)
    calc e * f * e⁻¹ = s * ((s⁻¹ * e * s) * (s⁻¹ * f * s) * (s⁻¹ * e * s)⁻¹) * s⁻¹ := by group
      _ = s * (y * (s⁻¹ * f * s) * y⁻¹) * s⁻¹ := by rw [h6]
      _ = s * y * s⁻¹ * f * (s * y * s⁻¹)⁻¹ := by group
  · intro q hq
    by_cases hx : Quotient.out q ∈ N
    · have h7 : (⟨(Quotient.out q)⁻¹ * e * Quotient.out q, hg _⟩ : ↥N) =
          (⟨_, hx⟩ : ↥N)⁻¹ * ⟨e, heN⟩ * ⟨_, hx⟩ := rfl
      rw [h7, map_mul, map_mul, he1, mul_one, map_inv, inv_mul_cancel]
    · exact absurd ((QuotientGroup.out_eq' q).symm.trans
        (QuotientGroup.eq.2 (hmulN _ _ hx htN))) hq

end Generic

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem u81_inner_right (u : U4X D L K n) {e : Bar2 D.M}
    (he : e ∈ commutator (Bar2 D.M))
    (h₀ : ∃ x₀ ∈ barImage D.M L, ∀ f ∈ barImage D.M L, e * f * e⁻¹ = x₀ * f * x₀⁻¹) :
    ∃ x₁ ∈ barImage D.M K, ∀ f ∈ barImage D.M K, e * f * e⁻¹ = x₁ * f * x₁⁻¹ := by
  obtain ⟨-, hinf, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  haveI : IsMulCommutative (Outer ↥(barImage D.M L)) := by
    rcases (Nat.dvd_prime u.prime_n).1 (u81_card_outer_dvd (u4x_shape_barImage u.hL u.shape))
      with h1 | hn
    · haveI : Subsingleton (Outer ↥(barImage D.M L)) := (Nat.card_eq_one_iff_unique.1 h1).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · haveI : Fact n.Prime := ⟨u.prime_n⟩
      haveI := isCyclic_of_prime_card hn
      infer_instance
  have hbot : barImage D.M L ≠ ⊥ := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv u.hL
    haveI : IsSimpleGroup (Bar2 L) := by
      rcases u.shape with h | h
      · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
      · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h
    haveI : Nontrivial ↥(barImage D.M L) := e.symm.toEquiv.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hcases : ∀ x : Bar2 D.M,
      (x ∈ normalizer (barImage D.M L : Set (Bar2 D.M)) ∧
        x ∈ normalizer (barImage D.M K : Set (Bar2 D.M))) ∨
      ((∀ f ∈ barImage D.M L, x * f * x⁻¹ ∈ barImage D.M K) ∧
        ∀ f ∈ barImage D.M K, x * f * x⁻¹ ∈ barImage D.M L) := by
    intro x
    obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective D.M x
    rcases u.conj_cases m.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨uc22ine229_mk_mem_normalizer h1, uc22ine229_mk_mem_normalizer h2⟩
    · exact Or.inr ⟨fun f hf => u4x_conj_mem_barImage h1 hf,
        fun f hf => u4x_conj_mem_barImage h2 hf⟩
  obtain ⟨m, hm, hmK⟩ := u.mem_K
  exact u81_inner_of_transfer hinf hbot hcases (t := uc22p21cPi D.M ⟨m, hm⟩)
    (fun f hf => u4x_conj_mem_barImage hmK.symm hf) he h₀

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
