module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Group
public import CFSG.RankThree.GF2n.Stroth80.Satz5Stroth
import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Form
import CFSG.ClassicalGroups.Orthogonal.PlanePairQuadruple
import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Additive
public import CFSG.HardMathSupport.Kantor79.LongRoot
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.HardMathSupport.Kantor79 CFSG.HardMathSupport.GuralnickMalle QuadraticMap
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

omit [CharP K 2] in
theorem Ctx.induces_rootA_of_cmCommAct (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (s : ↥(XbarH M Q Z B)) {a₁ a₂ : ↥(cmComm M Q Z B K γ M₀ φ)} {l : K}
    (hs : ∀ v, cmCommAct hc φ s v =
      v + l • (QuadraticMap.polar (cmCommQf B φ) v a₁ • a₂ +
        QuadraticMap.polar (cmCommQf B φ) v a₂ • a₁)) :
    Satz5.Induces M₀ ((s : ↥(H0 M Z)) : G) (Satz5.rootA M₀ (a₂ : M₀.E) (a₁ : M₀.E) l) := by
  intro x hx
  have hxsup : M₀.π x ∈ cmComm M Q Z B K γ M₀ φ ⊔
      M₀.B.orthogonal (cmComm M Q Z B K γ M₀ φ) := by
    rw [(hc.isCompl_cmComm_orthogonal hD φ hφπ).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨e₁, he₁, e₂, he₂, hxeq⟩ := Submodule.mem_sup.mp hxsup
  have hφe₂ : φ (s : ↥(H0 M Z)) e₂ = e₂ :=
    hc.action_fixes_orthogonal_of_mem_XbarH hD φ hφπ s he₂
  have hBe₂ : ∀ a : ↥(cmComm M Q Z B K γ M₀ φ), M₀.B e₂ (a : M₀.E) = 0 := by
    intro a
    have h := he₂ (a : M₀.E) a.2
    rw [Tim79.QuadModel.B_comm, h, neg_zero]
  have hφe₁ : φ (s : ↥(H0 M Z)) e₁ =
      e₁ + l • (M₀.B e₁ (a₁ : M₀.E) • (a₂ : M₀.E) +
        M₀.B e₁ (a₂ : M₀.E) • (a₁ : M₀.E)) := by
    have h := congrArg Subtype.val (hs ⟨e₁, he₁⟩)
    simpa only [Submodule.coe_add, Submodule.coe_smul, polar_cmCommQf, coe_cmCommAct] using h
  rw [hφπ (s : ↥(H0 M Z)) x hx, ← hxeq, map_add, hφe₁, hφe₂]
  unfold Satz5.rootA
  have hB₁ : M₀.B (e₁ + e₂) (a₁ : M₀.E) = M₀.B e₁ (a₁ : M₀.E) := by
    rw [map_add, LinearMap.add_apply, hBe₂ a₁, add_zero]
  have hB₂ : M₀.B (e₁ + e₂) (a₂ : M₀.E) = M₀.B e₁ (a₂ : M₀.E) := by
    rw [map_add, LinearMap.add_apply, hBe₂ a₂, add_zero]
  rw [hB₁, hB₂, smul_add, smul_smul, smul_smul]
  abel

omit [CharP K 2] in
private theorem linearIndependent_pair_of_span_finrank_eq_two {E : Type} [AddCommGroup E]
    [Module K E] {A : Submodule K E} (hA : Module.finrank K A = 2) {a b : E}
    (hspan : Submodule.span K ({a, b} : Set E) = A) : LinearIndependent K ![a, b] := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  have hrange : Set.range ![a, b] = ({a, b} : Set E) := by
    ext x
    simp [eq_comm, or_comm]
  rw [hrange]
  show Fintype.card (Fin 2) = Module.finrank K ↥(Submodule.span K ({a, b} : Set E))
  rw [hspan, hA]
  simp

private theorem exists_induces_rootA_of_siegelAxis (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {m : ℕ} {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)}
    {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ))}
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    {a₁ a₂ : ↥(cmComm M Q Z B K γ M₀ φ)} {A : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
    {l : K} (hA : A = Submodule.span K ({a₁, a₂} : Set ↥(cmComm M Q Z B K γ M₀ φ)))
    (hQa₁ : cmCommQf B φ a₁ = 0) (hQa₂ : cmCommQf B φ a₂ = 0)
    (hpol : QuadraticMap.polarBilin (cmCommQf B φ) a₂ a₁ = 0)
    (hli : LinearIndependent K ![a₂, a₁]) (hl : l ≠ 0)
    (hlift : ∀ s, IsLongRootElement (cmCommQf B φ) s → movedSpace s = A →
      ∃ g : SL(m, K), ρ g = s) :
    ∃ a ∈ (XbarH M Q Z B).map (H0 M Z).subtype,
      Satz5.Induces M₀ a (Satz5.rootA M₀ (a₂ : M₀.E) (a₁ : M₀.E) l) := by
  have hnd : ∀ x : ↥(cmComm M Q Z B K γ M₀ φ),
      (∀ y, QuadraticMap.polar (cmCommQf B φ) x y = 0) → x = 0 :=
    hc.cmCommQf_nondegenerate hD φ hφπ
  obtain ⟨hS, hmv⟩ :=
    isLongRootElement_siegelEquiv (cmCommQf B φ) a₂ a₁ hQa₂ hQa₁ hpol hnd hli hl
  have hmvA : movedSpace (siegelEquiv (cmCommQf B φ) a₂ a₁ hQa₂ hQa₁ hpol l) = A := by
    rw [hmv, hA, Set.pair_comm]
  obtain ⟨g, hg⟩ := hlift _ hS hmvA
  obtain ⟨s, hs⟩ := xbarHToXbar_surjective hc (σ₀ g)
  have hact : cmCommAct hc φ s = siegelEquiv (cmCommQf B φ) a₂ a₁ hQa₂ hQa₁ hpol l := by
    rw [← hρ g s hs, hg]
  refine ⟨((s : ↥(H0 M Z)) : G), Subgroup.mem_map.mpr ⟨s, s.2, rfl⟩, ?_⟩
  refine hc.induces_rootA_of_cmCommAct hD φ hφπ s (a₁ := a₁) (a₂ := a₂) (l := l) ?_
  intro v
  rw [hact]
  simp only [siegelEquiv_apply, siegelLin_apply, polarBilin_apply_apply, smul_add]
  abel

theorem Ctx.false_of_siegel_axes (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y)) {m : ℕ}
    {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)}
    {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ))}
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    {t₁ t₂ : SL(m, K)} (hS₁ : IsLongRootElement (cmCommQf B φ) (ρ t₁))
    (hS₂ : IsLongRootElement (cmCommQf B φ) (ρ t₂))
    (h1 : Module.finrank K ↥(movedSpace (ρ t₁) ⊓ movedSpace (ρ t₂)) = 1)
    (hno : ¬ movedSpace (ρ t₁) ≤ LinearMap.BilinForm.orthogonal
      (QuadraticMap.polarBilin (cmCommQf B φ)) (movedSpace (ρ t₂)))
    (hlift₁ : ∀ s, IsLongRootElement (cmCommQf B φ) s → movedSpace s = movedSpace (ρ t₁) →
      ∃ g, ρ g = s)
    (hlift₂ : ∀ s, IsLongRootElement (cmCommQf B φ) s → movedSpace s = movedSpace (ρ t₂) →
      ∃ g, ρ g = s) :
    False := by
  classical
  have hnd := hc.cmCommQf_nondegenerate hD φ hφπ
  have hA₁ : Module.finrank K ↥(movedSpace (ρ t₁)) = 2 := hS₁.finrank_movedSpace hnd
  have hA₂ : Module.finrank K ↥(movedSpace (ρ t₂)) = 2 := hS₂.finrank_movedSpace hnd
  obtain ⟨v₁, v₂, w₁, w₂, h11, h22, h12, h21, hv, hw, hsp₁, hsp₂⟩ :=
    exists_hyperbolic_quadruple_of_planes hnd hA₁ hA₂
      (fun w hw => hS₁.qf_eq_zero_of_mem_movedSpace hw)
      (fun w hw => hS₂.qf_eq_zero_of_mem_movedSpace hw) h1 hno
  have hmem₁ : ∀ x ∈ Submodule.span K ({w₁, v₂} : Set ↥(cmComm M Q Z B K γ M₀ φ)),
      x ∈ movedSpace (ρ t₁) := by
    rw [hsp₁]
    exact fun x hx => hx
  have hmem₂ : ∀ x ∈ Submodule.span K ({v₂, v₁} : Set ↥(cmComm M Q Z B K γ M₀ φ)),
      x ∈ movedSpace (ρ t₂) := by
    rw [hsp₂]
    exact fun x hx => hx
  have hw₁A : w₁ ∈ movedSpace (ρ t₁) :=
    hmem₁ w₁ (Submodule.subset_span (by simp))
  have hv₂A₁ : v₂ ∈ movedSpace (ρ t₁) :=
    hmem₁ v₂ (Submodule.subset_span (by simp))
  have hv₂A₂ : v₂ ∈ movedSpace (ρ t₂) :=
    hmem₂ v₂ (Submodule.subset_span (by simp))
  have hv₁A : v₁ ∈ movedSpace (ρ t₂) :=
    hmem₂ v₁ (Submodule.subset_span (by simp))
  have hind₁ : LinearIndependent K ![v₂, w₁] :=
    linearIndependent_pair_of_span_finrank_eq_two hA₁ (by rw [Set.pair_comm]; exact hsp₁)
  have hind₂ : LinearIndependent K ![v₁, v₂] :=
    linearIndependent_pair_of_span_finrank_eq_two hA₂ (by rw [Set.pair_comm]; exact hsp₂)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hD.card]
    exact hc.hyp.q4
  obtain ⟨ν, hν0, hν1⟩ := exists_ne_zero_ne_one_of_four_le_card hK4
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  have hset : Satz5.Setting M₀ ((XbarH M Q Z B).map (H0 M Z).subtype)
      (v₁ : M₀.E) (v₂ : M₀.E) (w₁ : M₀.E) (w₂ : M₀.E) := by
    obtain ⟨hnorm, hcent, hfaith⟩ :=
      hc.hyp.satz5_conditions hD.reg (Subgroup.map_subtype_le (XbarH M Q Z B))
    refine Satz5.Setting.mk hD.reg htwo ?_ ?_ ?_ ?_ ?_ ?_ hnorm hcent hfaith
    · rw [← polar_cmCommQf]; exact h11
    · rw [← polar_cmCommQf]; exact h22
    · rw [← polar_cmCommQf]; exact h12
    · rw [← polar_cmCommQf]; exact h21
    · rw [← polar_cmCommQf]; exact hv
    · rw [← polar_cmCommQf]; exact hw
  refine hset.false_of_rootLifts hν0 hν1 ?_ ?_
  · rintro l (rfl | rfl)
    · exact exists_induces_rootA_of_siegelAxis hc hD φ hφπ hρ (A := movedSpace (ρ t₁))
        (a₁ := w₁) (a₂ := v₂) hsp₁.symm (hS₁.qf_eq_zero_of_mem_movedSpace hw₁A)
        (hS₁.qf_eq_zero_of_mem_movedSpace hv₂A₁) h21 hind₁ one_ne_zero hlift₁
    · exact exists_induces_rootA_of_siegelAxis hc hD φ hφπ hρ (A := movedSpace (ρ t₁))
        (a₁ := w₁) (a₂ := v₂) hsp₁.symm (hS₁.qf_eq_zero_of_mem_movedSpace hw₁A)
        (hS₁.qf_eq_zero_of_mem_movedSpace hv₂A₁) h21 hind₁ hν0 hlift₁
  · rintro l (rfl | rfl)
    · exact exists_induces_rootA_of_siegelAxis hc hD φ hφπ hρ (A := movedSpace (ρ t₂))
        (a₁ := v₂) (a₂ := v₁) hsp₂.symm (hS₂.qf_eq_zero_of_mem_movedSpace hv₂A₂)
        (hS₂.qf_eq_zero_of_mem_movedSpace hv₁A) hv hind₂ one_ne_zero hlift₂
    · exact exists_induces_rootA_of_siegelAxis hc hD φ hφπ hρ (A := movedSpace (ρ t₂))
        (a₁ := v₂) (a₂ := v₁) hsp₂.symm (hS₂.qf_eq_zero_of_mem_movedSpace hv₂A₂)
        (hS₂.qf_eq_zero_of_mem_movedSpace hv₁A) hv hind₂ hν0 hlift₂

end CFSG.RankThree.GF2n.Stroth80
