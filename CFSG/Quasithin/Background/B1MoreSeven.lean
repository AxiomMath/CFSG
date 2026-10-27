module

public import CFSG.Quasithin.Background.B1MoreSevenE

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {V : Type*} [CommGroup V]

theorem B7_2_1 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G A H : Subgroup (MulAut V)}
    (hA : IsFFStarOffender G A) (hH : oTwoUpper H = H) (hHA : ⁅H, A⁆ = H)
    (hCF : AllTwoChiefFactorsCentral H) {a : MulAut V} (ha : a ∈ A)
    (ha0 : commSub (commV (Subgroup.zpowers a)) A = ⊥) {I : Subgroup V}
    (hI : I ∈ IrrPlus H (⊤ : Subgroup V)) : I.map a.toMonoidHom = I := by
  by_contra hne
  have hcomm : ∀ b ∈ A, ∀ v : V, b (a v * v⁻¹) = a v * v⁻¹ := by
    intro b hb v
    have h1 : commV (Subgroup.zpowers a) ≤ fixV A := commSub_eq_bot_iff.1 ha0
    have h2 : a v * v⁻¹ ∈ commV (Subgroup.zpowers a) :=
      Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, v, rfl⟩
    exact h1 h2 b hb
  exact B72Hyp.false_of_B72 hV hA ⟨hHA, ha, hA.2.2.1.1, hcomm, hI, hne⟩ hH hCF

theorem B7_2_2 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G A H : Subgroup (MulAut V)}
    (hA : IsFFStarMin G A) (hH : oTwoUpper H = H) (hHA : ⁅H, A⁆ = H)
    (hCF : AllTwoChiefFactorsCentral H) :
    ∀ a ∈ A, ∀ I ∈ IrrPlus H (⊤ : Subgroup V), I.map a.toMonoidHom = I := by
  intro a ha I hI
  have hquad : IsQuadratic A := B1_4_3 hV hA
  refine B7_2_1 hV hA.1 hH hHA hCF ha ?_ hI
  rw [commSub_eq_bot_iff]
  have hle : commV (Subgroup.zpowers a) ≤ commV A := by
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, hx, v, rfl⟩
    exact ⟨x, (Subgroup.zpowers_le.2 ha) hx, v, rfl⟩
  exact hle.trans hquad

theorem B1_5_3 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G A X : Subgroup (MulAut V)}
    (hA : IsFFStarMin G A) (hX : oTwoUpper X = X) (hXA : ⁅X, A⁆ = X)
    (hCF : AllTwoChiefFactorsCentral X) :
    ∀ a ∈ A, ∀ I ∈ IrrPlus X (⊤ : Subgroup V), I.map a.toMonoidHom = I :=
  B7_2_2 hV hA hX hXA hCF

@[expose] def AsB15Part4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G A : Subgroup (MulAut V), IsFFStarOffender G A →
      ∀ K : Subgroup (MulAut V), CFSG.Open.IsComponentOf K G →
        A ≤ Subgroup.normalizer (K : Set (MulAut V))

end CFSG.Quasithin
