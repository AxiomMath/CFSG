module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpFork
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDichotomy
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpConj
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section RealizationStep

private theorem ggInduced_mono' {G : Type} [Group G] {H H' : Subgroup G} {Bs : Subgroup G}
    (h : H ≤ H') {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced H Bs) : φ ∈ ggInduced H' Bs := by
  obtain ⟨g, hg, hgN, hgφ⟩ := hφ
  exact ⟨g, h hg, hgN, hgφ⟩

private theorem ggBraid_conj_eq {α : Type*} [Group α] {a u v : α} (hu : u * u = 1)
    (h : v = (u * v) * u * (u * v)⁻¹) :
    (a * u) * v * (a * u)⁻¹ = (a * v) * u * (a * v)⁻¹ := by
  have hu' : u⁻¹ = u := inv_eq_iff_mul_eq_one.mpr hu
  have key : (u * v) * u * (u * v)⁻¹ = u * v * u * v⁻¹ * u := by
    rw [mul_inv_rev, hu']
    group
  calc
    (a * u) * v * (a * u)⁻¹
        = (a * u) * (u * v * u * v⁻¹ * u) * (a * u)⁻¹ := by
          conv_lhs => rw [h]
          rw [key]
    _ = a * (u * u) * v * u * v⁻¹ * (u * u⁻¹) * a⁻¹ := by group
    _ = a * v * u * v⁻¹ * a⁻¹ := by rw [hu, mul_one, mul_inv_cancel, mul_one]
    _ = (a * v) * u * (a * v)⁻¹ := by rw [mul_inv_rev]; group

theorem ggForkCross_realize (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hJr : GGForkJr)
    (hPump : GGForkPumpOr) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hop : GGOpAutTrivial p Bs) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hNT : GGNoTransvection p Bs) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hsc : GGScalarsOrWeyl' p B Bs x D J) (hp5 : 5 ≤ p) {Λ : Type} [DecidableEq Λ]
    {C : Matrix Λ Λ ℤ}
    {b c v₂ : Λ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    {φ : Λ → MulAut ↥Bs} {φa : MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    {ha : V} {αa : Module.Dual (ZMod p) V} (hF : GGForkPairing C b c h α ha αa)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hlina : ∀ w, ggLin (p := p) ι φa w = w - αa w • ha)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hAK : ggAutomizer K Bs = Subgroup.closure (φ '' {i | i ≠ b} ∪ {φa}))
    (hvb : v₂ ≠ b) (hvc : v₂ ≠ c) :
    αa (h b) = 0 ∨ ∃ X : Subgroup G, GGAutLattice p Bs X ∧
      (φ b * φ c) * φa * (φ b * φ c)⁻¹ ∈ ggInduced X Bs ∧ φ c ∈ ggInduced X Bs ∧
        φ v₂ ∈ ggInduced X Bs := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hxB : x ∈ B := hcfg.1.2.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hxB
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  have hDxy : D = Subgroup.closure {x, y} := hnb.2.1
  have hrefl : ∀ i, GGIsReflection p (φ i) := fun i =>
    ggIsReflection_of_eq_reflection hp2 ι (hF.self i)
      (ggLin_eq_reflection ι (hF.self i) (hlin i))
  have hφL : ∀ i, φ i ∈ ggInduced L Bs := by
    intro i
    have h : φ i ∈ ggAutomizer L Bs := by
      rw [hAL]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    exact mem_ggAutomizer_iff.mp h
  have hφK : ∀ i, i ≠ b → φ i ∈ ggInduced K Bs := by
    intro i hi
    have h : φ i ∈ ggAutomizer K Bs := by
      rw [hAK]
      exact Subgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩)
    exact mem_ggAutomizer_iff.mp h
  have hφaK : φa ∈ ggInduced K Bs := by
    have h : φa ∈ ggAutomizer K Bs := by
      rw [hAK]
      exact Subgroup.subset_closure (Or.inr rfl)
    exact mem_ggAutomizer_iff.mp h
  have hfixD : ∀ i, i ≠ b → D ≤ ggFixG Bs (φ i) := by
    intro i hi
    obtain ⟨ℓ, hℓL, _hℓN, hℓ⟩ := hφL i
    obtain ⟨k, hkK, _hkN, hk⟩ := hφK i hi
    have hℓx : ℓ * x * ℓ⁻¹ = x := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hLx hℓL)
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    have hky : k * y * k⁻¹ = y := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (hKy hkK)
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [hDxy, Subgroup.closure_le]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact GGDichotomy.mem_ggFixG_of_induced hxBs hℓ hℓx
    · exact GGDichotomy.mem_ggFixG_of_induced hyBs hk hky
  have hJrc := hJr G p B Bs x L D J hcfg hInn hNT hp5 (φ c) (hφL c) (hrefl c)
  have hJrv := hJr G p B Bs x L D J hcfg hInn hNT hp5 (φ v₂) (hφL v₂) (hrefl v₂)
  have hcJ : φ c ∈ ggInduced J Bs := hJrc.2 (hfixD c hF.ne.symm)
  have hvJ : φ v₂ ∈ ggInduced J Bs := hJrv.2 (hfixD v₂ hvb)
  obtain ⟨Jr, hindc, hJC, hpc⟩ := hJrc.1
  obtain ⟨ℓ, hℓL, hℓN, hℓ⟩ := hφL b
  obtain ⟨k, hkK, hkN, hk⟩ := hφaK
  have hg : ℓ * k ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.mul_mem _ hℓN hkN
  have hc2 : φ c * φ c = 1 := by
    simpa [pow_two] using (hrefl c).1
  have hbmul : ggConjAut Bs hg = φ b * φa := by
    ext b'
    rw [ggConjAut_apply, MulAut.mul_apply, hℓ (φa b'), hk b']
    group
  have htconj : (φ b * φ c) * φa * (φ b * φ c)⁻¹ =
      ggConjAut Bs hg * φ c * (ggConjAut Bs hg)⁻¹ := by
    rw [hbmul]
    exact ggBraid_conj_eq hc2 (ggFork_braid ι hF hlin hlina)
  obtain ⟨hrt, hindt, hJCt, hpct⟩ := ggRealization_conj hp hg (hrefl c) hindc hJC hpc
  rw [← htconj] at hrt hindt hJCt hpct
  rcases ggDichotomy_refined hL hP hcfg hInn hrt hindt hJCt hpct with
    hLt | ⟨d, K', hnb', hJK', hJtK'⟩ | hcomm
  ·
    right
    exact ⟨L, (hPump G p B Bs x L D J hcfg hop hInn hNT hsc hp5).1,
      ggInduced_mono' hLt hindt, hφL c, hφL v₂⟩
  ·
    right
    rcases (hPump G p B Bs x L D J hcfg hop hInn hNT hsc hp5).2 d K' hnb' with hlat | hnoref
    · exact ⟨K', hlat, ggInduced_mono' hJtK' hindt, ggInduced_mono' hJK' hcJ,
        ggInduced_mono' hJK' hvJ⟩
    · exact absurd hrt (hnoref _ (ggInduced_mono' hJtK' hindt))
  ·
    left
    exact ggFork_cross_zero_of_commute hp2 ι hF hlin hlina hind (hcomm (φ c) hcJ)

end RealizationStep

end CFSG.StandardType
