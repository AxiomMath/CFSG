module

public import CFSG.Quasithin.EmptyFaithful.S146P1
public import CFSG.Quasithin.EmptyFaithful.S146zIGen
public import CFSG.Quasithin.EmptyFaithful.S146zHOfour

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

@[expose] def Input14613B1Act : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t →
        mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 4 →
          ∀ (δ δ' : F8.Geom T (yOfL22 T M) H) (k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)),
            F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k →
            0 < mIdx (F8.Uγ (VZ T M) H (k : G))
              (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) →
            mIdx (conjClosure (VZ T M) H)
                (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤
              mIdx (F8.Uγ (VZ T M) H (k : G))
                (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) →
              F8.Uγ (VZ T M) H (k : G) ≤ Subgroup.normalizer (uHi T M H H₁ : Set G)

section Core

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.case13One_of_act (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) {k x u : G} (hk : k ∉ mcOf T)
    (hUkH : conjSub k (conjClosure (VZ T M) H) ≤ H)
    (hUle : conjClosure (VZ T M) H ≤ conjSub k H)
    (hN : conjSub k (conjClosure (VZ T M) H) ≤ Subgroup.normalizer (uHi T M H H₁ : Set G))
    (hx : x ∈ conjSub k (conjClosure (VZ T M) H)) (hu : u ∈ uHi T M H H₁)
    (hn : x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hr : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2) : Case13One T M H p H₁ := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  have hp : p.Prime := hred.prime
  have hp2 : p ≠ 2 := hred.odd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hi₁ : uHi T M H H₁ ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  have hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 4 := by
    rw [card_Wsub h91 hi₁, card_tildeOf_eq_relIndex (Z_le_uHi T M H H₁) (hi₁.trans hUZ),
      HypF98.relIndex_eq_two_pow_mIdx (hUp.to_le hi₁), hr]
    norm_num
  have hxH : x ∈ H := hUkH hx
  have hu₀U : u ∈ conjClosure (VZ T M) H := hi₁ hu
  have hw₁ : clsU h91 hu₀U ∈ Wsub h91 (uHi T M H H₁) := clsU_mem_Wsub h91 hu₀U hu
  have hw₁ne : clsU h91 hu₀U ≠ 1 := by
    intro e
    have hu₀Z : u ∈ quasithinOmegaOneCenter T := (clsU_eq_one_iff h91 hu₀U).mp e
    apply hn
    have h1 : x * u * x⁻¹ ∈ quasithinOmegaOneCenter T :=
      (Subgroup.mem_normalizer_iff.mp (hHN hxH) u).mp hu₀Z
    exact (quasithinOmegaOneCenter T).mul_mem h1 ((quasithinOmegaOneCenter T).inv_mem hu₀Z)
  have hpW : p < Nat.card (Wsub h91 (uHi T M H H₁)) :=
    h.prime_lt_card_Wsub S hred h91 ⟨_, hw₁, hw₁ne⟩
  have hp3' : p = 3 := by omega
  subst hp3'
  have hOF : IsOFourPlusOn T M H := h.isOFourPlusOn S hred hr
  refine ⟨rfl, hOF, k⁻¹, ?_, ?_, ?_, ?_⟩
  · intro hmem
    exact hk (by simpa using (mcOf T).inv_mem hmem)
  · rw [inv_inv]
    intro hle
    apply hn
    have h1 := hle (Subgroup.commutator_mem_commutator hu hx)
    have e : x * u * x⁻¹ * u⁻¹ = (⁅u, x⁆)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact (quasithinOmegaOneCenter T).inv_mem h1
  · rw [inv_inv]
    exact le_inf hUkH hN
  · rw [inv_inv]
    exact hUle

end Core

theorem input14613B1P_of_act (hact : Input14613B1Act) : Input14613B1P := by
  intro G _ _ T M S H PQ p hred H₀ H₁ H₂ t h hex h4
  obtain ⟨γ, γ', g, hs, hlt⟩ := hex
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  obtain ⟨δ, δ', k, sk, hpos, hle, -⟩ := h98.lemma_14_5_18_four hs hlt
  have hnorm := hact G T M S H PQ p hred H₀ H₁ H₂ t h h4 δ δ' k sk hpos hle
  obtain ⟨hUkH, hUle⟩ := S.setup_le hH sk
  have hkg := S.setup_g_not hH sk
  have hr₁ : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2 := by
    have := h.mIdx_uK_sup_eq S hred
    omega
  have hr₂ : mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = 2 := by
    have e : mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) =
        mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) := by
      unfold mIdx
      rw [h.relIndex_uHi_eq S hred]
    rw [e, hr₁]
  obtain ⟨x, hx, hxQ⟩ : ∃ x ∈ F8.Uγ (VZ T M) H (k : G), x ∉ pCoreOf 2 H := by
    by_contra hall
    push Not at hall
    have hUD : F8.Uγ (VZ T M) H (k : G) ≤ F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G) := by
      rw [h98.Dγ_eq_inf_pCoreOf sk]
      exact le_inf le_rfl hall
    have h1 : (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)).relIndex
        (F8.Uγ (VZ T M) H (k : G)) = 1 := Subgroup.relIndex_eq_one.mpr hUD
    unfold mIdx at hpos
    rw [h1] at hpos
    simp at hpos
  have hxH : x ∈ H := hUkH hx
  rcases h.exists_nontrivial_of_not_mem S hred hxH hxQ with ⟨u, hu, hn⟩ | ⟨u, hu, hn⟩
  · exact Or.inl (h.case13One_of_act S hred hkg hUkH hUle hnorm hx hu hn hr₁)
  · refine Or.inr (h.swap.case13One_of_act S hred hkg hUkH hUle ?_ hx hu hn hr₂)
    intro y hy
    rcases h.normalizer_or_swap S hred (hUkH hy) with ⟨-, -, h2⟩ | ⟨h1, -⟩
    · exact mem_normalizer_of_conjSub_eq h2
    · exfalso
      have h1' := conjSub_eq_of_mem_normalizer (hnorm hy)
      rw [h1'] at h1
      have hZeq : uHi T M H H₁ = quasithinOmegaOneCenter T := by
        have h3 : uHi T M H H₁ ⊓ uHi T M H H₂ = quasithinOmegaOneCenter T := h.dir_inf
        rw [← h1, inf_idem] at h3
        exact h3
      rw [hZeq] at hr₁
      unfold mIdx at hr₁
      simp at hr₁

end CFSG.Quasithin
