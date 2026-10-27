module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcE6TwGraph
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwInner
public import CFSG.LieType.Chevalley.CLSOddTwistedE6AllInvolutionFourGroup
public import CFSG.LieType.AlgebraicGroups.E6RationalGraphCoset
public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem exists_inv_outer_E6tw
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {R : ℕ → ℕ → Prop}
    (hPgr : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p],
      ∃ u : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)),
        orderOf u = p ∧ (∃ (H : Subgroup _) (e n : ℕ), u ∈ H ∧ IsSpecialType p e n ↥H ∧ R e n) ∧
        diagramMap TwistTag.E6 k * (u : ModGL TwistTag.E6.tag k) * (diagramMap TwistTag.E6 k)⁻¹ =
          (u : ModGL TwistTag.E6.tag k)⁻¹)
    (hPdg : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p],
      ∃ u : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)),
        orderOf u = p ∧ (∃ (H : Subgroup _) (e n : ℕ), u ∈ H ∧ IsSpecialType p e n ↥H ∧ R e n) ∧
        (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) *
            (u : ModGL TwistTag.E6.tag k) *
            (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k)⁻¹ =
          (u : ModGL TwistTag.E6.tag k)⁻¹)
    (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (hα : α ^ 2 = 1)
    (hαo : α ∉ twistedE6Inn K σ) :
    ∃ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, orderOf x = p ∧ α x = x⁻¹ ∧
      ∃ (H : Subgroup (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (e n : ℕ), x ∈ H ∧
        IsSpecialType p e n ↥H ∧ R e n := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hKo : Nat.card K = (p ^ f) ^ TwistTag.E6.order := hK
  obtain ⟨-, -, -, -, -, hΔ, -, -, ⟨_, -, -, -, -, -, hsq⟩, hσP, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨g, u, hform⟩ : ∃ g u, α = MulAut.conj g *
      compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ σ := by
    rcases hsq α hα with hinn | ⟨-, g, u, h⟩
    · exact absurd hinn hαo
    · exact ⟨g, u, h⟩
  set D := rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) with hD
  have hαg : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (α h : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * D * diagramMap TwistTag.E6 K * h *
        (diagramMap TwistTag.E6 K)⁻¹ * D⁻¹ * (g : ModGL TwistTag.E6.tag K)⁻¹ := fun h => by
    rw [hform, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hΔ, hσP, ← hD]
    group
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK'
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFr_def, iterateFrobenius_def]
  have hFrι : ∀ c : K, Fr (ι c) = ι (σ c) := fun c => by rw [hFr, hσ, map_pow]
  have halg := CFSG.LieType.Chevalley.OddE6AllInvolution.isAlgebraic_zmod_algebraicClosure K p
  set P := diagramMap TwistTag.E6 k with hPdef
  set b : Fin TwistTag.E6.tag.rank → kˣ :=
    fun i => Units.map ι.toMonoidHom (compatDiag TwistTag.E6 σ.toRingHom u i) with hb_def
  set x := baseChangeGL ι (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b
    with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ := odd_diagram_fixed_ambient_centralizer_trivial TwistTag.E6 hp hf
    hodd K hKo σ.toRingHom hσ k ι
  obtain ⟨-, -, hHR, hHN, -, -, -⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.E6
    hp hf hodd K hKo σ.toRingHom hσ k Fr hFr
  have hgH : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι) := ⟨g, g.2, rfl⟩
  have hgG : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag k :=
    hHG hgH
  have hbG := (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k b).1
  have hxG : x ∈ adjointGroup TwistTag.E6.tag k := mul_mem hgG hbG
  have hdb : baseChangeGL ι D = rootDiagUnit TwistTag.E6.tag b := baseChangeGL_rootDiagUnit ι _
  have hPι : baseChangeGL ι (diagramMap TwistTag.E6 K) = P := baseChangeGL_diagramMap ι TwistTag.E6
  have hxconj : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      x * P * baseChangeGL ι (h : ModGL TwistTag.E6.tag K) * (x * P)⁻¹ =
        baseChangeGL ι (α h : ModGL TwistTag.E6.tag K) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
      hdb, hPι, hx_def]
    group
  have hFb : twistHom TwistTag.E6 k Fr (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b := by
    refine twistHom_rootDiagUnit fun i => Units.ext ?_
    change ι ((compatDiag TwistTag.E6 σ.toRingHom u (TwistTag.E6.perm i) : Kˣ) : K) =
      Fr (ι ((compatDiag TwistTag.E6 σ.toRingHom u i : Kˣ) : K))
    rw [compatDiag_perm, hFrι]
    rfl
  have hbR : rootDiagUnit TwistTag.E6.tag b ∈ twistedFixedGroup TwistTag.E6 k Fr :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 k Fr).2 ⟨hbG, hFb⟩
  have hxR : x ∈ twistedFixedGroup TwistTag.E6 k Fr := mul_mem (hHR hgH) hbR
  have hRF : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (P ^ 1)) = twistedFixedGroup TwistTag.E6 k Fr := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL TwistTag.E6.tag k p f (P ^ 1) y = y ↔ twistHom TwistTag.E6 k Fr y = y
    rw [frobTwistGL_apply, pow_one, twistHom_apply]
  have hα2 : ∀ h, α (α h) = h := fun h => by
    rw [← MulAut.mul_apply, ← sq, hα, MulAut.one_apply]
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
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * P * baseChangeGL ι h * (x * P)⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * P * (x * P) * baseChangeGL ι h =
        (x * P * (x * P * baseChangeGL ι h * (x * P)⁻¹) * (x * P)⁻¹) * (x * P * (x * P)) := by
          group
      _ = baseChangeGL ι h * (x * P * (x * P)) := by rw [h1, h2]
  obtain ⟨-, -, -, hnode⟩ :=
    E6_rational_graph_coset_fixed_components p hp2 hf k halg 1 (Or.inr rfl)
  obtain ⟨⟨y, hyR, hyA⟩, -⟩ := hnode x (hRF ▸ hxR) hx2
  rw [hRF] at hyR
  have hyN :=
    CFSG.LieType.Chevalley.OddTwistedE6AllInvolution.mem_normalizer_of_subgroupOf_normal
      hHR hHN hyR
  have hRF' : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)) =
      twistedFixedGroup TwistTag.E6 k Fr := by
    simpa only [pow_one, hPdef] using hRF
  have hTR : ∀ v ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k)),
      y⁻¹ * v * y ∈ twistedFixedGroup TwistTag.E6 k Fr := by
    intro v hv
    rw [hRF'] at hv
    exact mul_mem (mul_mem (inv_mem hyR) hv) hyR
  have hRn : twistedFixedGroup TwistTag.E6 k Fr ≤ Subgroup.normalizer
      (((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι) :
        Subgroup (ModGL TwistTag.E6.tag k)) : Set (ModGL TwistTag.E6.tag k)) :=
    fun r hr =>
      CFSG.LieType.Chevalley.OddTwistedE6AllInvolution.mem_normalizer_of_subgroupOf_normal
        hHR hHN hr
  have hcop : Nat.Coprime
      (((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι)).subgroupOf
        (twistedFixedGroup TwistTag.E6 k Fr)).index p :=
    coprime_index_twistedFixedGroup TwistTag.E6 hp hf hodd K hKo σ.toRingHom hσ k Fr hFr
  have hβz : ∀ u : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      baseChangeGL ι (α u : ModGL TwistTag.E6.tag K) =
        (x * P) * baseChangeGL ι (u : ModGL TwistTag.E6.tag K) * (x * P)⁻¹ :=
    fun u => (hxconj u).symm
  rcases hyA with hyP | hyD
  ·
    obtain ⟨u, hu, hgood, hinvP⟩ := hPgr k
    have hinv : y * (x * P) * y⁻¹ * (u : ModGL TwistTag.E6.tag k) *
        (y * (x * P) * y⁻¹)⁻¹ = (u : ModGL TwistTag.E6.tag k)⁻¹ := by
      rw [hyP]
      exact hinvP
    obtain ⟨H, e, n, huH, hH, hR⟩ := hgood
    obtain ⟨w, H₀, hw, hwα, hwH₀, ⟨φ⟩⟩ :=
      exists_inv_of_conj_index (baseChangeGL ι) hinj α (x * P) hβz hHR hRn hcop
        (T := fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k))) (y := y) hTR hu huH
        (fun v hv => by simpa using hH.1 ⟨v, hv⟩) hinv
    exact ⟨w, hw, hwα, H₀, e, n, hwH₀, hH.of_mulEquiv φ, hR⟩
  ·
    obtain ⟨u, hu, hgood, hinvD⟩ := hPdg k
    have hinv : y * (x * P) * y⁻¹ * (u : ModGL TwistTag.E6.tag k) *
        (y * (x * P) * y⁻¹)⁻¹ = (u : ModGL TwistTag.E6.tag k)⁻¹ := by
      rw [hyD]
      exact hinvD
    obtain ⟨H, e, n, huH, hH, hR⟩ := hgood
    obtain ⟨w, H₀, hw, hwα, hwH₀, ⟨φ⟩⟩ :=
      exists_inv_of_conj_index (baseChangeGL ι) hinj α (x * P) hβz hHR hRn hcop
        (T := fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k))) (y := y) hTR hu huH
        (fun v hv => by simpa using hH.1 ⟨v, hv⟩) hinv
    exact ⟨w, hw, hwα, H₀, e, n, hwH₀, hH.of_mulEquiv φ, hR⟩

theorem exists_inv_good_outer_E6tw
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (h3 : 3 < p ^ f)
    (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (hα : α ^ 2 = 1)
    (hαo : α ∉ twistedE6Inn K σ) :
    ∃ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, orderOf x = p ∧ α x = x⁻¹ ∧
      IsSpecialGood p x := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  exact exists_inv_outer_E6tw hp2 hf hK σ hσ (R := fun e n => e ≤ n ∧ 3 < p ^ e)
    (fun k _ _ _ => by
      obtain ⟨ι₀⟩ := nonempty_galoisField_ringHom k p f
      exact exists_inv_good_E6tw_graph (K := GaloisField p f) (k := k) ι₀ hp2 hcard h3)
    (fun k _ _ _ => by
      obtain ⟨ι₀⟩ := nonempty_galoisField_ringHom k p f
      exact exists_inv_good_E6tw_graph_diag (K := GaloisField p f) (k := k) ι₀ hp2 hcard h3)
    α hα hαo

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
