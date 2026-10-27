module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPrimeBridge
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPrimeGeneration

public section

namespace CFSG.RankThree.PartOne

open Module CFSG CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
open scoped commutatorElement

theorem split_prime_orthogonal_plane_components_generate
    {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1)
    (A : Subgroup (ProjOrthDerived Q)) (hA : Assembly.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) :
    (⨆ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
        (CFSG.layer ↥(Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).map
          (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))).subtype) = ⊤ ∧
    ∀ B : Subgroup (MulAut (ProjOrthDerived Q)),
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B →
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤
        (⨆ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
          (CFSG.layer ↥(B ⊓ Subgroup.centralizer
              ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
            (B ⊓ Subgroup.centralizer
              ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype) ∧
      (⨅ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
        Subgroup.centralizer (((CFSG.layer ↥(B ⊓ Subgroup.centralizer
              ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
            (B ⊓ Subgroup.centralizer
              ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype :
            Subgroup (MulAut (ProjOrthDerived Q))) : Set (MulAut (ProjOrthDerived Q)))) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_dvd_card_sub_one hp hpq
  have hpl : p ≠ ringChar K := fun h => hpK (by rw [h]; exact ringChar.Nat.cast_ringChar)
  have hq : 3 < Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h2 : p ≤ Nat.card K - 1 := Nat.le_of_dvd (by omega) hpq
    omega
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : CharP K (ringChar K) := ringChar.charP K
  have hℓ : (ringChar K).Prime :=
    (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
      (CharP.char_ne_zero_of_finite K (ringChar K))
  have : Nontrivial V := by
    obtain ⟨U, hU3, -⟩ := hT
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have := Module.finrank_zero_of_subsingleton (R := K) (M := ↥U)
    omega
  set Ω := orthDerived Q with hΩ
  set ρ : ↥Ω →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf Ω) with hρ
  have hρsurj : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  obtain ⟨Ã, hÃM, -, e, he, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_inner_plane_kernel_line_quadratic_decomposition
      (ℓ := ringChar K) hℓ hp hp2 hpl Q hQ A hA hAcard
  have : IsMulCommutative Ã := ⟨⟨fun a b => e.injective (by
    have := hA.1
    rw [map_mul, map_mul, mul_comm' (e a) (e b)])⟩⟩
  have hexpÃ : ∀ x : Ã, x ^ p = 1 := fun x => e.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (hA.2 _ (e x).2))
  have hGel : Assembly.IsElemAbelian p (Ã.map Ω.subtype) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      apply Subtype.ext
      show (a : V ≃ₗ[K] V) * b = b * a
      have h : (⟨a, ha⟩ : Ã) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := mul_comm' _ _
      exact congrArg (fun y : Ã => ((y : Ω) : V ≃ₗ[K] V)) h
    · rintro _ ⟨a, ha, rfl⟩
      show ((a : Ω) : V ≃ₗ[K] V) ^ p = 1
      have h := congrArg (fun y : Ã => ((y : Ω) : V ≃ₗ[K] V)) (hexpÃ ⟨a, ha⟩)
      simpa using h
  have hGcard : Nat.card (Ã.map Ω.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective Ω.subtype_injective, ← hAcard]
    exact Nat.card_congr e.toEquiv
  have hgenV := orthogonal_plane_derived_centralizers_generate hQ hT hp hp3 hpq (Ã.map Ω.subtype)
    (Subgroup.map_subtype_le Ã) hGel hGcard
  have hgenΩ := iSup_commutator_isometryCentralizer_eq_top Ã hgenV
  have hlift : ∀ a ∈ A, a ≠ 1 → ∃ x : ↥Ω, x ∈ Ã ∧ x ≠ 1 ∧ ρ x = a ∧ orderOf x = p := by
    intro a ha ha1
    have hx1 : ((e.symm ⟨a, ha⟩ : Ã) : Ω) ≠ 1 := by
      intro h1
      have h2 : e.symm ⟨a, ha⟩ = 1 := Subtype.ext h1
      apply ha1
      have h3 : (⟨a, ha⟩ : A) = 1 := by
        rw [← e.apply_symm_apply ⟨a, ha⟩, h2, map_one]
      exact congrArg Subtype.val h3
    refine ⟨((e.symm ⟨a, ha⟩ : Ã) : Ω), (e.symm ⟨a, ha⟩).2, hx1, ?_, ?_⟩
    · have := he (e.symm ⟨a, ha⟩)
      rw [e.apply_symm_apply] at this
      exact this.symm
    · refine orderOf_eq_prime ?_ hx1
      have := congrArg (fun y : Ã => (y : Ω)) (hexpÃ (e.symm ⟨a, ha⟩))
      simpa using this
  have hx : ∀ x : ↥Ω, x ∈ Ã → x ≠ 1 → ρ x ∈ A ∧ ρ x ≠ 1 ∧ orderOf x = p := by
    intro x hxÃ hx1
    refine ⟨hÃM hxÃ, ?_, orderOf_eq_prime (by
      have := congrArg (fun y : Ã => (y : Ω)) (hexpÃ ⟨x, hxÃ⟩)
      simpa using this) hx1⟩
    intro h1
    apply hx1
    have h2 : e ⟨x, hxÃ⟩ = 1 := Subtype.ext (by rw [he]; exact h1)
    have := e.injective (h2.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hkey : (⨆ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
      ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆) = ⊤ := by
    refine le_antisymm le_top ?_
    have h1 : (⊤ : Subgroup (ProjOrthDerived Q)) = (⊤ : Subgroup ↥Ω).map ρ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hρsurj]
    rw [h1, ← hgenΩ, Subgroup.map_iSup]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun x => iSup_le fun hxx => ?_
    obtain ⟨haA, ha1, hxp⟩ := hx x hxx.1 hxx.2
    obtain ⟨-, h2, -⟩ := orthogonal_local_derived_centralizer_contained_in_layer hQ hT hp hp3 hpl hq
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range le_rfl A hA hAcard
      (ρ x) haA ha1 x rfl hxp
    rw [← h2]
    exact le_iSup₂_of_le (ρ x) ⟨haA, ha1⟩ le_rfl
  have hlayer : ∀ a ∈ A, a ≠ 1 → ∀ B : Subgroup (MulAut (ProjOrthDerived Q)),
      (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ B →
      ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
          Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆ ≤
        (CFSG.layer ↥(Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).map
          (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))).subtype ∧
      ((CFSG.layer ↥(Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).map
          (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))).subtype).map
          (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) ≤
        (CFSG.layer ↥(B ⊓ Subgroup.centralizer
          ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
          (B ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype ∧
      ∀ φ : MulAut (ProjOrthDerived Q),
        (∀ e ∈ (CFSG.layer ↥(B ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
          (B ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype,
          φ * e = e * φ) →
        ∀ n ∈ ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
          Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆, φ n = n := by
    intro a ha ha1 B hB
    obtain ⟨x, hxÃ, hx1, hxa, hxp⟩ := hlift a ha ha1
    obtain ⟨-, -, h3, h4, h5⟩ := orthogonal_local_derived_centralizer_contained_in_layer hQ hT hp
      hp3 hpl hq B hB A hA hAcard a ha ha1 x hxa hxp
    exact ⟨h3, h4, h5⟩
  have hpart1 : (⨆ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
        (CFSG.layer ↥(Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)))).map
          (Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))).subtype) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hkey]
    exact iSup_mono fun a => iSup_mono fun ha =>
      (hlayer a ha.1 ha.2 (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range
        le_rfl).1
  refine ⟨hpart1, fun B hB => ⟨?_, ?_⟩⟩
  · rw [MonoidHom.range_eq_map]
    refine le_trans (Subgroup.map_mono (hpart1.ge)) ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    exact le_iSup₂_of_le a ha (hlayer a ha.1 ha.2 B hB).2.1
  · rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_iInf] at hφ
    have hfix : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
        Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆, φ n = n := by
      intro a ha ha1 n hn
      have h1 := hφ a
      rw [Subgroup.mem_iInf] at h1
      have h2 := h1 ⟨ha, ha1⟩
      exact (hlayer a ha ha1 B hB).2.2 φ
        (fun d hd => (Subgroup.mem_centralizer_iff.mp h2 d hd).symm) n hn
    have hall : ∀ n : ProjOrthDerived Q, φ n = n := by
      intro n
      have hn : n ∈ (⨆ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
          ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
            Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆) := by
        rw [hkey]
        exact Subgroup.mem_top n
      have hle : (⨆ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1),
          ⁅Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)),
            Subgroup.centralizer ({a} : Set (ProjOrthDerived Q))⁆) ≤
          MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id _) :=
        iSup_le fun a => iSup_le fun ha m hm => hfix a ha.1 ha.2 m hm
      exact hle hn
    exact MulEquiv.ext fun n => hall n

end CFSG.RankThree.PartOne
