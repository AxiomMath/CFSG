module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped MatrixGroups Matrix

private theorem exists_omegaModel_aux {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {a : ℕ}
    (ha : 2 ≤ a) {K : Type} [Field K] [Finite K] (hcard : Nat.card K = 2 ^ a)
    (π : ↥(StatedOmega (StatedQuadPlus 2 K)) →* ↥H) (hsurj : Function.Surjective π)
    (β : ↥(⊤ : Subgroup W) →*
      (↥(⊤ : Subgroup (Multiplicative (OmI → K))) ⧸
        (⊥ : Subgroup (Multiplicative (OmI → K))).subgroupOf ⊤))
    (hβs : Function.Surjective β) (hβk : ∀ u : ↥(⊤ : Subgroup W), β u = 1 → u = 1)
    (hβact : ∀ (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) (u : ↥(⊤ : Subgroup W))
      (m : ↥(⊤ : Subgroup (Multiplicative (OmI → K)))),
      β u = QuotientGroup.mk m →
        β ⟨(π γ : MulAut W) u, Subgroup.mem_top _⟩ = QuotientGroup.mk
          ⟨Multiplicative.ofAdd (((γ : GL OmI K) : Matrix OmI OmI K) *ᵥ
            Multiplicative.toAdd (m : Multiplicative (OmI → K))), Subgroup.mem_top _⟩) :
    ∃ S : OmegaModel W, S.omega = H ∧ Nat.card S.K = 2 ^ a := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := a)
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    exact hβk
  let A : Type := Multiplicative (OmI → K)
  let q : (↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf (⊤ : Subgroup A)) ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (⊤ : Subgroup A))).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have hq : ∀ m : ↥(⊤ : Subgroup A), q (QuotientGroup.mk m) = (m : A) := fun m => rfl
  let e : W ≃* A := Subgroup.topEquiv.symm.trans ((MulEquiv.ofBijective β ⟨hβinj, hβs⟩).trans q)
  have he : ∀ w : W, e w = q (β ⟨w, Subgroup.mem_top w⟩) := fun w => rfl
  have hint : ∀ (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) (w : W),
      e ((π γ : MulAut W) w) = Multiplicative.ofAdd
        (((γ : GL OmI K) : Matrix OmI OmI K) *ᵥ Multiplicative.toAdd (e w)) := by
    intro γ w
    have hm : β ⟨w, Subgroup.mem_top w⟩ = QuotientGroup.mk ⟨e w, Subgroup.mem_top _⟩ :=
      q.injective (by rw [hq]; exact (he w).symm)
    have h1 := hβact γ ⟨w, Subgroup.mem_top w⟩ ⟨e w, Subgroup.mem_top _⟩ hm
    have h2 := congrArg q h1
    rw [hq] at h2
    exact (he _).trans h2
  have hact : ∀ (γ : ↥(StatedOmega (StatedQuadPlus 2 K))), (π γ : MulAut W) =
      (MulAut.congr e.symm).toMonoidHom (OmegaModel.natActHom K (γ : GL OmI K)) := by
    intro γ
    ext w
    apply e.injective
    rw [hint γ w]
    simp [OmegaModel.natActHom, OmegaModel.natAut, MulAut.congr]
  have h4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  let S : OmegaModel W := { K := K, four_le := h4, e := e }
  refine ⟨S, ?_, hcard⟩
  ext φ
  rw [OmegaModel.omega, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have := hact ⟨γ, hγ⟩
    have h5 : S.actHom γ = (π ⟨γ, hγ⟩ : MulAut W) := this.symm
    rw [h5]
    exact (π ⟨γ, hγ⟩).2
  · intro hφ
    obtain ⟨γ, hγ⟩ := hsurj ⟨φ, hφ⟩
    refine ⟨γ, γ.2, ?_⟩
    have h5 : S.actHom γ = (π γ : MulAut W) := (hact γ).symm
    rw [h5, hγ]

theorem exists_omegaModel_of_natOmegaPlus {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {a : ℕ} (ha : 2 ≤ a) (h : NatOmegaPlus H ⊤ ⊥ 4 a) :
    ∃ S : OmegaModel W, S.omega = H ∧ Nat.card S.K = 2 ^ a := by
  obtain ⟨-, K, hF, hfin, hcard, π, hsurj, -, -, -, -, -, -, β, hβs, hβk, hβact⟩ := h
  exact exists_omegaModel_aux ha hcard π hsurj β hβs
    (fun u hu => Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu)))
    (fun γ u m hm => hβact γ u m _ _ hm)

theorem exists_omegaModel_of_case1633 {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {m : ℕ} (h : Case1633 D V₀ V hV L m) :
    ∃ S : OmegaModel (Vtil V₀ V hV), S.omega = lBar V₀ V hV L ∧ Nat.card S.K = 2 ^ m := by
  rcases h with ⟨⟨-, hnat, -⟩, rfl⟩ | ⟨⟨-, hnat, -⟩, rfl⟩
  · exact exists_omegaModel_of_natOmegaPlus (by norm_num) hnat
  · exact exists_omegaModel_of_natOmegaPlus (by norm_num) hnat

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
