module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.Quasithin.Background.A3FactsRank
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.Open CFSG.SectionRank CFSG.LocalCores

section Pi

variable {ι : Type} [DecidableEq ι] {S : ι → Type} [∀ i, Group (S i)]

@[expose] noncomputable def inclPair {i₁ i₂ : ι} (h : i₁ ≠ i₂) : S i₁ × S i₂ →* ∀ i, S i :=
  (MonoidHom.mulSingle S i₁).noncommCoprod (MonoidHom.mulSingle S i₂)
    (fun a b => Pi.mulSingle_commute h a b)

theorem inclPair_apply {i₁ i₂ : ι} (h : i₁ ≠ i₂) (a : S i₁) (b : S i₂) :
    inclPair h (a, b) = Pi.mulSingle i₁ a * Pi.mulSingle i₂ b :=
  rfl

theorem inclPair_injective {i₁ i₂ : ι} (h : i₁ ≠ i₂) :
    Function.Injective (inclPair (S := S) h) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  rw [inclPair_apply, inclPair_apply] at hab
  have h1 := congrFun hab i₁
  have h2 := congrFun hab i₂
  simp [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h.symm] at h1 h2
  exact Prod.ext h1 h2

@[expose] noncomputable def inclTriple {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃)
    (h23 : i₂ ≠ i₃) : (S i₁ × S i₂) × S i₃ →* ∀ i, S i :=
  (inclPair h12).noncommCoprod (MonoidHom.mulSingle S i₃) (fun ab c => by
    rcases ab with ⟨a, b⟩
    rw [inclPair_apply]
    exact (Pi.mulSingle_commute h13 a c).mul_left (Pi.mulSingle_commute h23 b c))

theorem inclTriple_apply {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (a : S i₁) (b : S i₂) (c : S i₃) :
    inclTriple h12 h13 h23 ((a, b), c) =
      Pi.mulSingle i₁ a * Pi.mulSingle i₂ b * Pi.mulSingle i₃ c :=
  rfl

theorem inclTriple_injective {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) :
    Function.Injective (inclTriple (S := S) h12 h13 h23) := by
  rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ habc
  rw [inclTriple_apply, inclTriple_apply] at habc
  have h1 := congrFun habc i₁
  have h2 := congrFun habc i₂
  have h3 := congrFun habc i₃
  simp [Pi.mulSingle_eq_of_ne h12, Pi.mulSingle_eq_of_ne h12.symm, Pi.mulSingle_eq_of_ne h13,
    Pi.mulSingle_eq_of_ne h13.symm, Pi.mulSingle_eq_of_ne h23, Pi.mulSingle_eq_of_ne h23.symm]
    at h1 h2 h3
  exact Prod.ext (Prod.ext h1 h2) h3

variable [Finite ι] [∀ i, Finite (S i)] {p : ℕ}

theorem pRank_pi_pair_ge (hp : 1 < p) {i₁ i₂ : ι} (h : i₁ ≠ i₂) :
    CFSG.Open.pRank p (⊤ : Subgroup (S i₁)) + CFSG.Open.pRank p (⊤ : Subgroup (S i₂)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (∀ i, S i)) :=
  (pRank_prod_ge hp).trans (pRank_top_le_of_injective hp (inclPair h) (inclPair_injective h))

theorem pRank_pi_triple_ge (hp : 1 < p) {i₁ i₂ i₃ : ι} (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃)
    (h23 : i₂ ≠ i₃) :
    CFSG.Open.pRank p (⊤ : Subgroup (S i₁)) + CFSG.Open.pRank p (⊤ : Subgroup (S i₂)) +
        CFSG.Open.pRank p (⊤ : Subgroup (S i₃)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (∀ i, S i)) := by
  have h1 := pRank_prod_ge (S := S i₁) (T := S i₂) hp
  have h2 := pRank_prod_ge (S := S i₁ × S i₂) (T := S i₃) hp
  have h3 := pRank_top_le_of_injective hp (inclTriple (S := S) h12 h13 h23)
    (inclTriple_injective h12 h13 h23)
  omega

end Pi

section Components

variable {H : Type} [Group H] [Finite H]

theorem pRank_piQ_le_two
    (hsqt : CFSG.IsStronglyQuasithin (↥(CFSG.layer H) ⧸ Subgroup.center ↥(CFSG.layer H)))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r
      (⊤ : Subgroup (∀ K : ComponentIndex H, ↥K.1 ⧸ Subgroup.center ↥K.1)) ≤ 2 := by
  rw [pRank_top_eq_of_mulEquiv hr.one_lt (layerCentralQuotientEquiv H)]
  exact isStronglyQuasithin_iff.1 hsqt r hr hr2

theorem pRank_le_one_of_two_iso
    (hsqt : CFSG.IsStronglyQuasithin (↥(CFSG.layer H) ⧸ Subgroup.center ↥(CFSG.layer H)))
    {K₁ K₂ : ComponentIndex H} (hne : K₁ ≠ K₂)
    (e : (↥K₁.1 ⧸ Subgroup.center ↥K₁.1) ≃* (↥K₂.1 ⧸ Subgroup.center ↥K₂.1))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup (↥K₁.1 ⧸ Subgroup.center ↥K₁.1)) ≤ 1 := by
  have h1 := pRank_pi_pair_ge (S := fun K : ComponentIndex H => ↥K.1 ⧸ Subgroup.center ↥K.1)
    hr.one_lt hne
  have h2 := pRank_piQ_le_two hsqt hr hr2
  have h3 := pRank_top_eq_of_mulEquiv hr.one_lt e
  omega

theorem not_three_iso
    (hsqt : CFSG.IsStronglyQuasithin (↥(CFSG.layer H) ⧸ Subgroup.center ↥(CFSG.layer H)))
    {K₁ K₂ K₃ : ComponentIndex H} (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃)
    (e₂ : (↥K₁.1 ⧸ Subgroup.center ↥K₁.1) ≃* (↥K₂.1 ⧸ Subgroup.center ↥K₂.1))
    (e₃ : (↥K₁.1 ⧸ Subgroup.center ↥K₁.1) ≃* (↥K₃.1 ⧸ Subgroup.center ↥K₃.1)) : False := by
  obtain ⟨hsimple, hnonab⟩ := (layer_central_quotient (G := H)).2.1 K₁
  obtain ⟨r, hr, hr2, hpos⟩ := exists_odd_prime_pRank_pos hnonab
  have h1 := pRank_pi_triple_ge (S := fun K : ComponentIndex H => ↥K.1 ⧸ Subgroup.center ↥K.1)
    hr.one_lt h12 h13 h23
  have h2 := pRank_piQ_le_two hsqt hr hr2
  have h3 := pRank_top_eq_of_mulEquiv hr.one_lt e₂
  have h4 := pRank_top_eq_of_mulEquiv hr.one_lt e₃
  omega

@[expose] noncomputable def centerQuotientEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)

end Components

end A3Facts

end CFSG.Quasithin
