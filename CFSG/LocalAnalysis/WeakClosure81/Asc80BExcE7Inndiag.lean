module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcE7Inv
import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UOuter
import CFSG.GH74.GLS.Stage1.Main.BrTwoClassE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

private theorem fixed_of_two_generators_e7 {G : Type} [Group G] [Finite (MulAut G)]
    (E : Subgroup (MulAut G)) {e₁ e₂ : MulAut G} (h₁ : e₁ ∈ E) (h₂ : e₂ ∈ E)
    (hsq₁ : e₁ * e₁ = 1) (hsq₂ : e₂ * e₂ = 1) (hcomm : e₁ * e₂ = e₂ * e₁)
    (hne₁ : e₁ ≠ 1) (hne₂ : e₂ ≠ 1) (hne : e₁ ≠ e₂) (h4 : Nat.card E = 4)
    {a : G} (hfix₁ : e₁ a = a) (hfix₂ : e₂ a = a) : ∀ e ∈ E, e a = a := by
  obtain ⟨hmem, -, -, hcard⟩ :=
    CFSG.GH74.GLS.Stage1.Main.four_of_invols hsq₁ hsq₂ hcomm hne₁ hne₂ hne
  have hEeq : Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ = E :=
    Subgroup.eq_of_le_of_card_ge
      (sup_le (Subgroup.zpowers_le.2 h₁) (Subgroup.zpowers_le.2 h₂))
      (by rw [hcard, h4])
  intro e he
  rw [← hEeq] at he
  rcases hmem e he with rfl | rfl | rfl | rfl
  · rfl
  · exact hfix₁
  · exact hfix₂
  · rw [MulAut.mul_apply, hfix₂, hfix₁]


theorem exists_fixed_rElement_four_e7_or_nontoral {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (E : Subgroup (MulAut ↥(adjointGroup .E7 K)))
    (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4) :
    (∃ y : ↥(adjointGroup .E7 K), y ≠ 1 ∧ (∃ n : ℕ, y ^ (ringChar K ^ n) = 1) ∧
      ∀ e ∈ E, e y = y) ∨
    ∃ x₁ x₂ : ModGL .E7 K, x₁ ^ 2 = 1 ∧ x₂ ^ 2 = 1 ∧ x₁ * x₂ = x₂ * x₁ ∧
      x₁ ≠ 1 ∧ x₂ ≠ 1 ∧ x₁ ≠ x₂ ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) x₁ ∈
        adjointGroup .E7 (AlgebraicClosure K) ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) x₂ ∈
        adjointGroup .E7 (AlgebraicClosure K) ∧
      (∀ y : ↥(adjointGroup .E7 K), Commute (y : ModGL .E7 K) x₁ →
        Commute (y : ModGL .E7 K) x₂ → ∀ e ∈ E, e y = y) ∧
      ¬ ∃ g ∈ adjointGroup .E7 (AlgebraicClosure K),
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x₁ * g ∈
          torusGroup .E7 (AlgebraicClosure K) ∧
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) x₂ * g ∈
          torusGroup .E7 (AlgebraicClosure K) := by
  classical
  by_cases hin : E ≤ CFSG.StandardType.LayerSixE.inndiagAut .E7 K
  ·
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
    have hq : Nat.card K = ringChar K ^ (f : ℕ) := by
      rw [Nat.card_eq_fintype_card]
      exact hf
    have hodd : Odd (Nat.card K) := by
      rw [hq]
      exact (hℓ.eq_two_or_odd'.resolve_left hK).pow
    have : Finite (ModGL .E7 K) := finite_modGL
    have : Finite ↥(adjointGroup .E7 K) := Subtype.finite
    have : Finite (MulAut ↥(adjointGroup .E7 K)) :=
      Finite.of_injective (fun e : MulAut ↥(adjointGroup .E7 K) => (e : _ → _))
        DFunLike.coe_injective
    have : Finite ↥E := Subtype.finite
    have : Fintype ↥E := Fintype.ofFinite _
    set L := AlgebraicClosure K with hLdef
    set ι : K →+* L := algebraMap K L with hι
    obtain ⟨-, -, hfaith, -⟩ :=
      exceptional_Lang_finite_root_centralizer_faithfulness .E7 K hodd L ι
    have hlt1 : ({1} : Finset ↥E).card < (Finset.univ : Finset ↥E).card := by
      rw [Finset.card_singleton, Finset.card_univ, ← Nat.card_eq_fintype_card, h4]
      norm_num
    obtain ⟨e₁E, -, he₁nmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt1
    have he₁ne' : (e₁E : MulAut ↥(adjointGroup .E7 K)) ≠ 1 := by
      intro h
      exact he₁nmem (by rw [Finset.mem_singleton]; exact Subtype.ext h)
    have hcard2 : ({1, e₁E} : Finset ↥E).card = 2 := by
      rw [Finset.card_pair_eq_two_iff]
      intro h
      exact he₁ne' (congrArg Subtype.val h).symm
    have hlt2 : ({1, e₁E} : Finset ↥E).card < (Finset.univ : Finset ↥E).card := by
      rw [hcard2, Finset.card_univ, ← Nat.card_eq_fintype_card, h4]
      norm_num
    obtain ⟨e₂E, -, he₂nmem⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt2
    have he₂ne' : (e₂E : MulAut ↥(adjointGroup .E7 K)) ≠ 1 := by
      intro h
      exact he₂nmem (by
        rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (Subtype.ext h))
    have he₂ne₁' : (e₂E : MulAut ↥(adjointGroup .E7 K)) ≠
        (e₁E : MulAut ↥(adjointGroup .E7 K)) := by
      intro h
      exact he₂nmem (by
        rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Subtype.ext h))
    set e₁ : MulAut ↥(adjointGroup .E7 K) :=
      (e₁E : MulAut ↥(adjointGroup .E7 K)) with he₁def
    set e₂ : MulAut ↥(adjointGroup .E7 K) :=
      (e₂E : MulAut ↥(adjointGroup .E7 K)) with he₂def
    have he₁E : e₁ ∈ E := he₁def ▸ e₁E.2
    have he₂E : e₂ ∈ E := he₂def ▸ e₂E.2
    have he₁ne : e₁ ≠ 1 := he₁def ▸ he₁ne'
    have he₂ne : e₂ ≠ 1 := he₂def ▸ he₂ne'
    have he₂ne₁ : e₂ ≠ e₁ := fun h =>
      he₂ne₁' (he₂def.symm.trans (h.trans he₁def))
    obtain ⟨h₁, hh₁adj, hact₁⟩ :=
      CFSG.StandardType.TableCRes.exists_hmat_of_mem_inndiagAut (hin he₁E)
    obtain ⟨h₂, hh₂adj, hact₂⟩ :=
      CFSG.StandardType.TableCRes.exists_hmat_of_mem_inndiagAut (hin he₂E)
    have hsq₁ : e₁ * e₁ = 1 := by rw [← sq]; exact hE.2 e₁ he₁E
    have hsq₂ : e₂ * e₂ = 1 := by rw [← sq]; exact hE.2 e₂ he₂E
    have hcommE : e₁ * e₂ = e₂ * e₁ :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e₁, he₁E⟩ ⟨e₂, he₂E⟩)
    have hcen : ∀ (e : MulAut ↥(adjointGroup .E7 K)) (h : ModGL .E7 K), e * e = 1 →
        (∀ c : ↥(adjointGroup .E7 K),
          ((e c : ↥(adjointGroup .E7 K)) : ModGL .E7 K) = h * c * h⁻¹) →
        ∀ c : ↥(adjointGroup .E7 K),
          baseChangeGL ι (h ^ 2) * baseChangeGL ι c =
            baseChangeGL ι c * baseChangeGL ι (h ^ 2) := by
      intro e h hsq hact c
      have hfix : e (e c) = c := by
        have h0 := congrArg (fun g : MulAut ↥(adjointGroup .E7 K) => g c) hsq
        simpa only [MulAut.mul_apply, MulAut.one_apply] using h0
      have h1 := hact (e c)
      rw [hfix, hact c] at h1
      have h3 : h ^ 2 * (c : ModGL .E7 K) * (h ^ 2)⁻¹ = (c : ModGL .E7 K) := by
        calc h ^ 2 * (c : ModGL .E7 K) * (h ^ 2)⁻¹ =
            h * (h * (c : ModGL .E7 K) * h⁻¹) * h⁻¹ := by
              rw [pow_two, mul_inv_rev]; group
          _ = (c : ModGL .E7 K) := h1.symm
      have h4 : h ^ 2 * (c : ModGL .E7 K) = (c : ModGL .E7 K) * h ^ 2 := by
        calc h ^ 2 * (c : ModGL .E7 K) =
            (h ^ 2 * (c : ModGL .E7 K) * (h ^ 2)⁻¹) * h ^ 2 := by
              rw [pow_two, mul_inv_rev]; group
          _ = (c : ModGL .E7 K) * h ^ 2 := by rw [h3]
      simpa only [map_mul] using congrArg (baseChangeGL ι) h4
    have hcommC₁ := hcen e₁ h₁ hsq₁ hact₁
    have hcommC₂ := hcen e₂ h₂ hsq₂ hact₂
    have hz₁adj : baseChangeGL ι (h₁ ^ 2) ∈ adjointGroup .E7 L := by
      rw [map_pow]
      exact pow_mem hh₁adj 2
    have hz₁ : baseChangeGL ι (h₁ ^ 2) = 1 := by
      refine hfaith _ hz₁adj ?_
      intro h hh
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hh
      exact hcommC₁ ⟨c, hc⟩
    have hsq₁' : h₁ ^ 2 = 1 := baseChangeGL_injective ι (by rw [hz₁, map_one])
    have hz₂adj : baseChangeGL ι (h₂ ^ 2) ∈ adjointGroup .E7 L := by
      rw [map_pow]
      exact pow_mem hh₂adj 2
    have hz₂ : baseChangeGL ι (h₂ ^ 2) = 1 := by
      refine hfaith _ hz₂adj ?_
      intro h hh
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hh
      exact hcommC₂ ⟨c, hc⟩
    have hsq₂' : h₂ ^ 2 = 1 := baseChangeGL_injective ι (by rw [hz₂, map_one])
    have hgen : ∀ c : ↥(adjointGroup .E7 K), e₁ (e₂ c) = e₂ (e₁ c) := by
      intro c
      have h := congrArg (fun g : MulAut ↥(adjointGroup .E7 K) => g c) hcommE
      simpa only [MulAut.mul_apply] using h
    have hcommC₁₂ : ∀ c : ↥(adjointGroup .E7 K),
        baseChangeGL ι ((h₂ * h₁)⁻¹ * (h₁ * h₂)) * baseChangeGL ι c =
          baseChangeGL ι c * baseChangeGL ι ((h₂ * h₁)⁻¹ * (h₁ * h₂)) := by
      intro c
      have hL : ((e₁ (e₂ c) : ↥(adjointGroup .E7 K)) : ModGL .E7 K) =
          h₁ * (h₂ * (c : ModGL .E7 K) * h₂⁻¹) * h₁⁻¹ := by
        rw [hact₁ (e₂ c), hact₂ c]
      have hR : ((e₂ (e₁ c) : ↥(adjointGroup .E7 K)) : ModGL .E7 K) =
          h₂ * (h₁ * (c : ModGL .E7 K) * h₁⁻¹) * h₂⁻¹ := by
        rw [hact₂ (e₁ c), hact₁ c]
      have hmain : h₁ * (h₂ * (c : ModGL .E7 K) * h₂⁻¹) * h₁⁻¹ =
          h₂ * (h₁ * (c : ModGL .E7 K) * h₁⁻¹) * h₂⁻¹ := by
        rw [← hL, ← hR, hgen c]
      have h3 : ((h₂ * h₁)⁻¹ * (h₁ * h₂)) * (c : ModGL .E7 K) *
          ((h₂ * h₁)⁻¹ * (h₁ * h₂))⁻¹ = (c : ModGL .E7 K) := by
        calc ((h₂ * h₁)⁻¹ * (h₁ * h₂)) * (c : ModGL .E7 K) *
              ((h₂ * h₁)⁻¹ * (h₁ * h₂))⁻¹ =
            (h₂ * h₁)⁻¹ * (h₁ * (h₂ * (c : ModGL .E7 K) * h₂⁻¹) * h₁⁻¹) *
              (h₂ * h₁) := by group
          _ = (h₂ * h₁)⁻¹ * (h₂ * (h₁ * (c : ModGL .E7 K) * h₁⁻¹) * h₂⁻¹) *
              (h₂ * h₁) := by rw [hmain]
          _ = (c : ModGL .E7 K) := by group
      have h4 : ((h₂ * h₁)⁻¹ * (h₁ * h₂)) * (c : ModGL .E7 K) =
          (c : ModGL .E7 K) * ((h₂ * h₁)⁻¹ * (h₁ * h₂)) := by
        calc ((h₂ * h₁)⁻¹ * (h₁ * h₂)) * (c : ModGL .E7 K) =
            (((h₂ * h₁)⁻¹ * (h₁ * h₂)) * (c : ModGL .E7 K) *
              ((h₂ * h₁)⁻¹ * (h₁ * h₂))⁻¹) * ((h₂ * h₁)⁻¹ * (h₁ * h₂)) := by group
          _ = (c : ModGL .E7 K) * ((h₂ * h₁)⁻¹ * (h₁ * h₂)) := by rw [h3]
      simpa only [map_mul] using congrArg (baseChangeGL ι) h4
    have hz₁₂adj : baseChangeGL ι ((h₂ * h₁)⁻¹ * (h₁ * h₂)) ∈
        adjointGroup .E7 L := by
      rw [map_mul, map_inv, map_mul, map_mul]
      exact mul_mem (inv_mem (mul_mem hh₂adj hh₁adj)) (mul_mem hh₁adj hh₂adj)
    have hcommz : (h₂ * h₁)⁻¹ * (h₁ * h₂) = 1 := by
      have hz : baseChangeGL ι ((h₂ * h₁)⁻¹ * (h₁ * h₂)) = 1 := by
        refine hfaith _ hz₁₂adj ?_
        intro h hh
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hh
        exact hcommC₁₂ ⟨c, hc⟩
      exact baseChangeGL_injective ι (by rw [hz, map_one])
    have hcommh : h₁ * h₂ = h₂ * h₁ := by
      calc h₁ * h₂ = (h₂ * h₁) * ((h₂ * h₁)⁻¹ * (h₁ * h₂)) := by group
        _ = (h₂ * h₁) * 1 := by rw [hcommz]
        _ = h₂ * h₁ := by group
    have hh₁ne : h₁ ≠ 1 := by
      intro h
      apply he₁ne
      refine MulEquiv.ext fun c => Subtype.ext ?_
      rw [hact₁ c, h]
      simp
    have hh₂ne : h₂ ≠ 1 := by
      intro h
      apply he₂ne
      refine MulEquiv.ext fun c => Subtype.ext ?_
      rw [hact₂ c, h]
      simp
    have hhne : h₁ ≠ h₂ := by
      intro h
      apply he₂ne₁
      refine MulEquiv.ext fun c => Subtype.ext ?_
      rw [hact₂ c, hact₁ c, h]
    have hfixed : ∀ y : ↥(adjointGroup .E7 K), Commute (y : ModGL .E7 K) h₁ →
        Commute (y : ModGL .E7 K) h₂ → ∀ e ∈ E, e y = y := by
      intro y hy₁ hy₂
      have hfix₁ : e₁ y = y := by
        refine Subtype.ext ?_
        rw [hact₁ y]
        calc h₁ * (y : ModGL .E7 K) * h₁⁻¹ =
            (y : ModGL .E7 K) * h₁ * h₁⁻¹ := by rw [← hy₁.eq]
          _ = (y : ModGL .E7 K) := by group
      have hfix₂ : e₂ y = y := by
        refine Subtype.ext ?_
        rw [hact₂ y]
        calc h₂ * (y : ModGL .E7 K) * h₂⁻¹ =
            (y : ModGL .E7 K) * h₂ * h₂⁻¹ := by rw [← hy₂.eq]
          _ = (y : ModGL .E7 K) := by group
      exact fixed_of_two_generators_e7 E he₁E he₂E hsq₁ hsq₂ hcommE he₁ne he₂ne
        he₂ne₁.symm h4 hfix₁ hfix₂
    by_cases htor : ∃ g ∈ adjointGroup .E7 L,
        g⁻¹ * baseChangeGL ι h₁ * g ∈ torusGroup .E7 L ∧
          g⁻¹ * baseChangeGL ι h₂ * g ∈ torusGroup .E7 L
    · obtain ⟨g, hg, hg₁, hg₂⟩ := htor
      obtain ⟨u, hu1, hun, hucomm₁, hucomm₂⟩ :=
        exists_rElement_commute_toral_pair_e7 hK hsq₁' hsq₂' hg hg₁ hg₂
      exact Or.inl ⟨u, hu1, hun, hfixed u hucomm₁ hucomm₂⟩
    · exact Or.inr ⟨h₁, h₂, hsq₁', hsq₂', hcommh, hh₁ne, hh₂ne, hhne,
        hh₁adj, hh₂adj, hfixed, htor⟩
  · exact Or.inl (exists_fixed_rElement_four_e7_of_not_inndiag hK E hE h4 hin)

end CFSG.LocalAnalysis.WeakClosure81
