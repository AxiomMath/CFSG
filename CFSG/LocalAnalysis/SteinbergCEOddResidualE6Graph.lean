module

public import CFSG.LocalAnalysis.SteinbergCEOddResidualE6GraphCore
public import CFSG.LieType.Chevalley.OddDiagramFixedAmbientCentralizer
public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergCE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open E6GraphCoset

namespace E6GraphCoset

theorem exists_normal_simple_of_mulEquiv {A B : Type*} [Group A] [Group B] (ψ : A ≃* B)
    (S : Subgroup A) (hSn : S.Normal) (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) {T : Type*} [Group T] (eS : S ≃* T) :
    ∃ S' : Subgroup B, S'.Normal ∧ IsSimpleGroup S' ∧ (∃ a b : S', a * b ≠ b * a) ∧
      Nonempty (S' ≃* T) := by
  let e : S ≃* S.map ψ.toMonoidHom := S.equivMapOfInjective ψ.toMonoidHom ψ.injective
  refine ⟨S.map ψ.toMonoidHom, hSn.map _ ψ.surjective, (MulEquiv.isSimpleGroup_congr e).1 hSs,
    ?_, ⟨e.symm.trans eS⟩⟩
  obtain ⟨a, b, hab⟩ := hSnab
  refine ⟨e a, e b, fun h => hab ?_⟩
  apply e.injective
  rw [map_mul, map_mul, h]

end E6GraphCoset

theorem odd_E6_graph_coset_fixed_no_normal_even_SL2
    {F : Type} [Field F] [Finite F]
    (hF : Odd (Nat.card F)) {α : MulAut (adjointGroup TwistTag.E6.tag F)}
    {g : adjointGroup TwistTag.E6.tag F} {a : Fin TwistTag.E6.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag F, (α h : ModGL TwistTag.E6.tag F) =
      (g : ModGL TwistTag.E6.tag F) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 F *
        h * (diagramMap TwistTag.E6 F)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag F)⁻¹)
    (hα : α ^ 2 = 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (K : Type) [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set k := AlgebraicClosure F
  set ι := algebraMap F k with hι
  set p := ringChar F with hp_def
  have hpF : CharP F p := ringChar.charP F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP k p := charP_of_injective_algebraMap (algebraMap F k).injective p
  have hp2 : p ≠ 2 := by
    intro h2
    rw [Nat.card_eq_fintype_card, hcard, h2] at hF
    exact Nat.not_even_iff_odd.2 hF ((Nat.even_pow' n.ne_zero).2 even_two)
  set Fr := iterateFrobenius k p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card F := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have hFrι : ∀ c : F, Fr (ι c) = ι c := fun c => by
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k := by
    let _ : Algebra (ZMod p) k := ZMod.algebra k p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := F) ({y} : Finset k)
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y := congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  set P := diagramMap TwistTag.E6 k with hPdef
  set b : Fin TwistTag.E6.tag.rank → kˣ := fun i => Units.map ι.toMonoidHom (a i) with hb_def
  set x := baseChangeGL ι (g : ModGL TwistTag.E6.tag F) * rootDiagUnit TwistTag.E6.tag b
    with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness TwistTag.E6.tag F hF k ι
  have hgG : baseChangeGL ι (g : ModGL TwistTag.E6.tag F) ∈ adjointGroup TwistTag.E6.tag k :=
    hHG ⟨g, g.2, rfl⟩
  have hxG : x ∈ adjointGroup TwistTag.E6.tag k :=
    mul_mem hgG (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k b).1
  have hdb : baseChangeGL ι (rootDiagUnit TwistTag.E6.tag a) = rootDiagUnit TwistTag.E6.tag b :=
    baseChangeGL_rootDiagUnit ι a
  have hPι : baseChangeGL ι (diagramMap TwistTag.E6 F) = P := baseChangeGL_diagramMap ι TwistTag.E6
  have hxconj : ∀ h : adjointGroup TwistTag.E6.tag F,
      x * P * baseChangeGL ι (h : ModGL TwistTag.E6.tag F) * (x * P)⁻¹ =
        baseChangeGL ι (α h : ModGL TwistTag.E6.tag F) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
      hdb, hPι, hx_def]
    group
  obtain ⟨-, hHR, -, hder⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group TwistTag.E6.tag F hF k Fr hFr
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
  have hRF : graphRational k p n 0 =
        adjointGroup TwistTag.E6.tag k ⊓
          (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
    ext y
    refine Subgroup.mem_inf.trans ((and_congr Iff.rfl ?_).trans Subgroup.mem_inf.symm)
    change frobTwistGL TwistTag.E6.tag k p n (P ^ 0) y = y ↔ Units.map (entrywiseHom Fr) y = y
    rw [frobTwistGL_apply, pow_zero, one_mul, inv_one, mul_one]
  have hxR : x ∈ graphRational k p n 0 := by
    rw [hRF]
    refine Subgroup.mem_inf.2 ⟨hxG, ?_⟩
    change Units.map (entrywiseHom Fr) x = x
    rw [hx_def, map_mul, hFd]
    congr 1
    exact (Subgroup.mem_inf.1 hgR).2
  have hα2 : ∀ h, α (α h) = h := fun h => by
    have := congrArg (fun φ : MulAut (adjointGroup TwistTag.E6.tag F) => φ h) hα
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
    have h2 := hxconj (α ⟨h, hh⟩)
    rw [hα2] at h2
    change x * P * baseChangeGL ι h * (x * P)⁻¹ = _ at h1
    change _ = baseChangeGL ι h at h2
    rw [sq]
    calc x * P * (x * P) * baseChangeGL ι h =
        (x * P * (x * P * baseChangeGL ι h * (x * P)⁻¹) * (x * P)⁻¹) * (x * P * (x * P)) := by
          group
      _ = baseChangeGL ι h * (x * P * (x * P)) := by rw [h1, h2]
  have hHder : ⁅graphRational k p n 0, graphRational k p n 0⁆ =
      (adjointGroup TwistTag.E6.tag F).map (baseChangeGL ι) := by
    rw [hRF]
    exact hder
  let φ : adjointGroup TwistTag.E6.tag F →* ModGL TwistTag.E6.tag k :=
    (baseChangeGL ι).comp (adjointGroup TwistTag.E6.tag F).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))).map φ =
      graphCosetFixed k p n 0 x := by
    rw [graphCosetFixed, hHder]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL TwistTag.E6.tag F) * (x * P) =
        x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag F)
      calc baseChangeGL ι (c : ModGL TwistTag.E6.tag F) * (x * P) =
          (x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag F) * (x * P)⁻¹) * (x * P) := by
            rw [h1]
        _ = x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag F) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have hcx' : baseChangeGL ι c * (x * P) = x * P * baseChangeGL ι c := hcx
      have h2 : x * P * baseChangeGL ι c * (x * P)⁻¹ = baseChangeGL ι c := by
        rw [← hcx']
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ := exists_normal_simple_of_mulEquiv
    ((Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)) S hSn hSs hSnab
    eS
  exact E6_graph_coset_fixed_no_normal_even_SL2 p hp2 n.pos k halg 0 (Or.inl rfl) hxR hx2 S'
    hS'n hS's hS'nab K eS'

theorem odd_twisted_E6_outer_fixed_no_normal_even_SL2
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (F : Type) [Field F] [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))
    (hα : α ^ 2 = 1) (hαo : α ∉ twistedE6Inn F σ)
    (S : Subgroup (α.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (K : Type) [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hKo : Nat.card F = (p ^ f) ^ TwistTag.E6.order := hF
  obtain ⟨-, -, -, -, -, hΔ, -, -, ⟨Θ, -, -, -, -, -, hsq⟩, hσP, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf F hF σ hσ
  obtain ⟨g, u, hform⟩ : ∃ g u, α = MulAut.conj g *
      compatDiagAutHom TwistTag.E6 F σ.toRingHom u * fieldActor σ σ := by
    rcases hsq α hα with hinn | ⟨-, g, u, h⟩
    · exact absurd hinn hαo
    · exact ⟨g, u, h⟩
  set D := rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) with hD
  have hαg : ∀ h : graphFixedRootGroup TwistTag.E6 F σ.toRingHom,
      (α h : ModGL TwistTag.E6.tag F) =
      (g : ModGL TwistTag.E6.tag F) * D * diagramMap TwistTag.E6 F * h *
        (diagramMap TwistTag.E6 F)⁻¹ * D⁻¹ * (g : ModGL TwistTag.E6.tag F)⁻¹ := fun h => by
    rw [hform, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hΔ, hσP, ← hD]
    group
  set k := AlgebraicClosure F
  set ι := algebraMap F k with hι
  have hcharF : ringChar F = p := by
    obtain ⟨n, hpn, hcard⟩ := FiniteField.card F (ringChar F)
    have h1 : ringChar F ∣ p ^ (f * 2) := by
      rw [pow_mul, ← hF, Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self _ n.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hpn hp).1 (hpn.dvd_of_dvd_pow h1)
  have : CharP F p := hcharF ▸ ringChar.charP F
  have : CharP k p := charP_of_injective_algebraMap (algebraMap F k).injective p
  set Fr := iterateFrobenius k p f with hFr_def
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFr_def, iterateFrobenius_def]
  have hFrι : ∀ c : F, Fr (ι c) = ι (σ c) := fun c => by rw [hFr, hσ, map_pow]
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k := by
    let _ : Algebra (ZMod p) k := ZMod.algebra k p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := F) ({y} : Finset k)
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y :=
      congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  set P := diagramMap TwistTag.E6 k with hPdef
  set b : Fin TwistTag.E6.tag.rank → kˣ :=
    fun i => Units.map ι.toMonoidHom (compatDiag TwistTag.E6 σ.toRingHom u i) with hb_def
  set x := baseChangeGL ι (g : ModGL TwistTag.E6.tag F) * rootDiagUnit TwistTag.E6.tag b
    with hx_def
  obtain ⟨hinj, hHG, hfaith, -⟩ := odd_diagram_fixed_ambient_centralizer_trivial TwistTag.E6 hp hf
    hodd F hKo σ.toRingHom hσ k ι
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.E6
    hp hf hodd F hKo σ.toRingHom hσ k Fr hFr
  have hgH : baseChangeGL ι (g : ModGL TwistTag.E6.tag F) ∈
      (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map (baseChangeGL ι) := ⟨g, g.2, rfl⟩
  have hgG : baseChangeGL ι (g : ModGL TwistTag.E6.tag F) ∈ adjointGroup TwistTag.E6.tag k :=
    hHG hgH
  have hbG := (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k b).1
  have hxG : x ∈ adjointGroup TwistTag.E6.tag k := mul_mem hgG hbG
  have hdb : baseChangeGL ι D = rootDiagUnit TwistTag.E6.tag b := baseChangeGL_rootDiagUnit ι _
  have hPι : baseChangeGL ι (diagramMap TwistTag.E6 F) = P := baseChangeGL_diagramMap ι TwistTag.E6
  have hxconj : ∀ h : graphFixedRootGroup TwistTag.E6 F σ.toRingHom,
      x * P * baseChangeGL ι (h : ModGL TwistTag.E6.tag F) * (x * P)⁻¹ =
        baseChangeGL ι (α h : ModGL TwistTag.E6.tag F) := by
    intro h
    rw [hαg h, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
      hdb, hPι, hx_def]
    group
  have hFb : twistHom TwistTag.E6 k Fr (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b := by
    refine twistHom_rootDiagUnit fun i => Units.ext ?_
    change ι ((compatDiag TwistTag.E6 σ.toRingHom u (TwistTag.E6.perm i) : Fˣ) : F) =
      Fr (ι ((compatDiag TwistTag.E6 σ.toRingHom u i : Fˣ) : F))
    rw [compatDiag_perm, hFrι]
    rfl
  have hbR : rootDiagUnit TwistTag.E6.tag b ∈ twistedFixedGroup TwistTag.E6 k Fr :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 k Fr).2 ⟨hbG, hFb⟩
  have hxR : x ∈ twistedFixedGroup TwistTag.E6 k Fr := mul_mem (hHR hgH) hbR
  have hRF : graphRational k p f 1 = twistedFixedGroup TwistTag.E6 k Fr := by
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
  have hHder : ⁅graphRational k p f 1, graphRational k p f 1⁆ =
      (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).map (baseChangeGL ι) := by
    rw [hRF]
    exact hder
  let φ : graphFixedRootGroup TwistTag.E6 F σ.toRingHom →* ModGL TwistTag.E6.tag k :=
    (baseChangeGL ι).comp (graphFixedRootGroup TwistTag.E6 F σ.toRingHom).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  have hmap : (α.toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 F σ.toRingHom))).map φ =
      graphCosetFixed k p f 1 x := by
    rw [graphCosetFixed, hHder]
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨⟨c, c.2, rfl⟩, ?_⟩
      have h1 := hxconj c
      have hc' : α c = c := hc
      rw [hc'] at h1
      change baseChangeGL ι (c : ModGL TwistTag.E6.tag F) * (x * P) =
        x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag F)
      calc baseChangeGL ι (c : ModGL TwistTag.E6.tag F) * (x * P) =
          (x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag F) * (x * P)⁻¹) * (x * P) := by
            rw [h1]
        _ = x * P * baseChangeGL ι (c : ModGL TwistTag.E6.tag F) := by group
    · rintro ⟨⟨c, hc, rfl⟩, hcx⟩
      refine ⟨⟨c, hc⟩, ?_, rfl⟩
      have h1 := hxconj ⟨c, hc⟩
      have hcx' : baseChangeGL ι c * (x * P) = x * P * baseChangeGL ι c := hcx
      have h2 : x * P * baseChangeGL ι c * (x * P)⁻¹ = baseChangeGL ι c := by
        rw [← hcx']
        group
      rw [h2] at h1
      exact Subtype.ext (hinj h1.symm)
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ := exists_normal_simple_of_mulEquiv
    ((Subgroup.equivMapOfInjective _ φ hφ).trans (MulEquiv.subgroupCongr hmap)) S hSn hSs hSnab
    eS
  exact E6_graph_coset_fixed_no_normal_even_SL2 p hp2 hf k halg 1 (Or.inr rfl) (hRF ▸ hxR) hx2 S'
    hS'n hS's hS'nab K eS'

end CFSG.LocalAnalysis.SteinbergCE
