module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcE6Graph
public import CFSG.LieType.Chevalley.CLSOddE6AllInvolutionFourGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootDiag)


theorem exists_inv_E6_graph_of {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e) (he : 1 ≤ e)
    {Q : adjointGroup TwistTag.E6.tag K → Prop}
    (hQ : ∀ θ : adjointGroup TwistTag.E6.tag K →* adjointGroup TwistTag.E6.tag K,
      Function.Injective θ → ∀ w, Q w → Q (θ w))
    (hQP : ∃ w : adjointGroup TwistTag.E6.tag K, Q w ∧
      diagramMap TwistTag.E6 K * (w : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹ =
        (w : ModGL TwistTag.E6.tag K)⁻¹)
    (hQD : ∃ w : adjointGroup TwistTag.E6.tag K, Q w ∧
      rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 K *
          (w : ModGL TwistTag.E6.tag K) *
          (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 K)⁻¹ =
        (w : ModGL TwistTag.E6.tag K)⁻¹)
    (g : adjointGroup TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (β : MulAut (adjointGroup TwistTag.E6.tag K))
    (hβg : ∀ h : adjointGroup TwistTag.E6.tag K, (β h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        h * (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hβ : β ^ 2 = 1) :
    ∃ x : adjointGroup TwistTag.E6.tag K, β x = x⁻¹ ∧ Q x := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact Odd.pow (hp.odd_of_ne_two hp2)
  have : Fact p.Prime := ⟨hp⟩
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p e with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, hK]
  have hFrι : ∀ c : K, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k :=
    CFSG.LieType.Chevalley.OddE6AllInvolution.isAlgebraic_zmod_algebraicClosure K p
  set P := diagramMap TwistTag.E6 k with hPdef
  set b : Fin TwistTag.E6.tag.rank → kˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b
    with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness TwistTag.E6.tag K hKodd k ι
  have hgG : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag k :=
    hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup TwistTag.E6.tag k :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k b).1
  have hdb : baseChangeGL ι (rootDiagUnit TwistTag.E6.tag a) = rootDiagUnit TwistTag.E6.tag b :=
    baseChangeGL_rootDiagUnit ι a
  have hPι : baseChangeGL ι (diagramMap TwistTag.E6 K) = P := baseChangeGL_diagramMap ι TwistTag.E6
  have hxconj : ∀ h : adjointGroup TwistTag.E6.tag K,
      x * P * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * (x * P)⁻¹ =
        baseChangeGL ι (β h : ModGL TwistTag.E6.tag K) := by
    intro h
    rw [hβg h, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
      hdb, hPι, hx_def]
    group
  obtain ⟨-, hHR, hRnorm, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group TwistTag.E6.tag K hKodd k Fr hFr
  have hgR := hHR ⟨g, g.2, rfl⟩
  have hFd : Units.map (entrywiseHom Fr) (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b := by
    refine Units.ext ?_
    change entrywise Fr (rootDiag b) = rootDiag b
    rw [entrywise_rootDiag]
    congr 1
    funext i
    ext
    exact hFrι _
  have hRF : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (P ^ 0)) =
        adjointGroup TwistTag.E6.tag k ⊓
          (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL TwistTag.E6.tag k p e (P ^ 0) y = y ↔ Units.map (entrywiseHom Fr) y = y
    rw [frobTwistGL_apply, pow_zero, one_mul, inv_one, mul_one]
  have hxR : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (P ^ 0)) := by
    rw [hRF]
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hβ2 : ∀ h, β (β h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup TwistTag.E6.tag K) => φ h) hβ
    simpa [sq] using this
  have hP2 : P * P = 1 := by
    have h := diagramMap_pow_order TwistTag.E6 k
    rwa [show TwistTag.E6.order = 2 from rfl, sq] at h
  have hPG : ∀ y ∈ adjointGroup TwistTag.E6.tag k,
      P * y * P⁻¹ ∈ adjointGroup TwistTag.E6.tag k := by
    have hQ := conj_mem_adjointGroup_of_map_eq (map_conj_diagramMap_zpow TwistTag.E6 k 1)
    rw [zpow_one] at hQ
    exact hQ
  have hx2 : (x * P) ^ 2 = 1 := by
    have hsqG : (x * P) ^ 2 ∈ adjointGroup TwistTag.E6.tag k := by
      have e : (x * P) ^ 2 = x * (P * x * P⁻¹) * (P * P) := by
        rw [sq]
        group
      rw [e, hP2, mul_one]
      exact mul_mem hxG (hPG x hxG)
    refine hfaith _ hsqG fun y hy => ?_
    obtain ⟨h, hh, rfl⟩ := hy
    have h1 := hxconj ⟨h, hh⟩
    have h2 := hxconj (β ⟨h, hh⟩)
    rw [hβ2] at h2
    change x * P * baseChangeGL ι h * (x * P)⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * P * (x * P) * baseChangeGL ι h =
        (x * P * (x * P * baseChangeGL ι h * (x * P)⁻¹) * (x * P)⁻¹) * (x * P * (x * P)) := by
          group
      _ = baseChangeGL ι h * (x * P * (x * P)) := by rw [h1, h2]
  obtain ⟨-, -, -, hnode⟩ :=
    E6_rational_graph_coset_fixed_components p hp2 he k halg 0 (Or.inl rfl)
  obtain ⟨⟨y, hyR, hyA⟩, -⟩ := hnode x hxR hx2
  rw [hRF] at hyR
  rcases hyA with hyP | hyD
  · obtain ⟨w₀, hgood, hinvK⟩ := hQP
    refine exists_inv_of_injective_conj (baseChangeGL ι) hinj β (x * P)
      (fun u => (hxconj u).symm) (hRnorm hyR) hQ hgood ?_
    have h1 : baseChangeGL ι (diagramMap TwistTag.E6 K * (w₀ : ModGL TwistTag.E6.tag K) *
        (diagramMap TwistTag.E6 K)⁻¹) =
          P * baseChangeGL ι (w₀ : ModGL TwistTag.E6.tag K) * P⁻¹ := by
      rw [map_mul, map_mul, map_inv, hPι]
    rw [hyP, ← h1, hinvK, map_inv]
  · obtain ⟨w₀, hgood, hinvK⟩ := hQD
    have hdι : baseChangeGL ι (rootDiagUnit TwistTag.E6.tag
        (![1, -1, 1, 1, 1, 1] : Fin TwistTag.E6.tag.rank → Kˣ)) =
        rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] := by
      refine (baseChangeGL_rootDiagUnit ι _).trans ?_
      congr 1
      funext i
      change Fin 6 at i
      fin_cases i <;> simp
    refine exists_inv_of_injective_conj (baseChangeGL ι) hinj β (x * P)
      (fun u => (hxconj u).symm) (hRnorm hyR) hQ hgood ?_
    have h2 : baseChangeGL ι (rootDiagUnit TwistTag.E6.tag
        (![1, -1, 1, 1, 1, 1] : Fin TwistTag.E6.tag.rank → Kˣ) * diagramMap TwistTag.E6 K *
        (w₀ : ModGL TwistTag.E6.tag K) *
        (rootDiagUnit TwistTag.E6.tag
          (![1, -1, 1, 1, 1, 1] : Fin TwistTag.E6.tag.rank → Kˣ) * diagramMap TwistTag.E6 K)⁻¹) =
          (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * P) *
            baseChangeGL ι (w₀ : ModGL TwistTag.E6.tag K) *
            (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * P)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_mul, hdι, hPι]
    rw [hyD]
    exact h2.symm.trans ((congrArg (baseChangeGL ι) hinvK).trans (map_inv _ _))

theorem exists_inv_good_E6_graph {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e)
    (g : adjointGroup TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (β : MulAut (adjointGroup TwistTag.E6.tag K))
    (hβg : ∀ h : adjointGroup TwistTag.E6.tag K, (β h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K *
        h * (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹)
    (hβ : β ^ 2 = 1) :
    ∃ x : adjointGroup TwistTag.E6.tag K, orderOf x = p ∧ β x = x⁻¹ ∧ IsSpecialGood p x := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, pow_zero] at h3
      omega
    · omega
  obtain ⟨x, hx, hxo, hxg⟩ := exists_inv_E6_graph_of hp hp2 hK he
    (Q := fun w => orderOf w = p ∧ IsSpecialGood p w)
    (fun θ hθ w hw => ⟨(orderOf_injective θ hθ w).trans hw.1, hw.2.map hθ⟩)
    (by
      obtain ⟨w, hwo, hwi, hwg⟩ := exists_diagramMap_inv_good_E6 hp hp2 hK h3
      exact ⟨w, ⟨hwo, hwg⟩, hwi⟩)
    (by
      obtain ⟨w, hwo, hwi, hwg⟩ :=
        exists_rootDiag_diagramMap_inv_good_E6 hp hp2 hK h3 (s := ![1, -1, 1, 1, 1, 1]) rfl
      exact ⟨w, ⟨hwo, hwg⟩, hwi⟩)
    g a β hβg hβ
  exact ⟨x, hxo, hx, hxg⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
