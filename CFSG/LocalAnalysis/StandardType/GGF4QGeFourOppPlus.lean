module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppSp
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOppPumpup
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusForcing
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusOm
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourR3CommPlus
import CFSG.LocalAnalysis.StandardType.GGF4OriginalRankOnePlus
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsCover
import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusAutomizer
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal

namespace F4Model

theorem le_card_of_conj_mem {W H : Type} [Group W] [Group H] [Finite H] (R : F4Rep W)
    (φ : W →* H) (hφ : Function.Injective φ) (w : W) {X : Subgroup H}
    (hX : ∀ i : Fin 4, i ≠ 0 → φ (w * R.s i * w⁻¹) ∈ X) : 48 ≤ Nat.card X := by
  classical
  obtain ⟨hlen, hnd, hne⟩ := f4PCWords_spec
  set ψ : W →* H := φ.comp (MulAut.conj w).toMonoidHom with hψ
  have hψinj : Function.Injective ψ := hφ.comp (MulAut.conj w).injective
  have hmem : ∀ l ∈ f4PCWords, ψ (R.wd l) ∈ X := by
    intro l hl
    have h := R.wd_mem_closure_of_ne (k := 0) (hne l hl) (S := (X.comap ψ : Set W))
      (fun i hi => hX i hi)
    rw [Subgroup.closure_eq] at h
    exact h
  have hinj : ∀ l₁ ∈ f4PCWords, ∀ l₂ ∈ f4PCWords, ψ (R.wd l₁) = ψ (R.wd l₂) → l₁ = l₂ := by
    intro l₁ h₁ l₂ h₂ h
    have hw : R.wd l₁ = R.wd l₂ := hψinj h
    have hm : evalW l₁ = evalW l₂ := M4.toMat_injective (by rw [← R.rho_wd, ← R.rho_wd, hw])
    exact List.inj_on_of_nodup_map hnd h₁ h₂ hm
  have hnd' : (f4PCWords.map fun l => ψ (R.wd l)).Nodup :=
    List.Nodup.map_on hinj (List.Nodup.of_map evalW hnd)
  set S : Finset H := (f4PCWords.map fun l => ψ (R.wd l)).toFinset with hS
  have hScard : S.card = 48 := by
    rw [hS, List.toFinset_card_of_nodup hnd', List.length_map, hlen]
  have hSX : (S : Set H) ⊆ X := by
    intro z hz
    rw [hS, Finset.mem_coe, List.mem_toFinset, List.mem_map] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    exact hmem l hl
  calc 48 = (S : Set H).ncard := by rw [Set.ncard_coe_finset, hScard]
    _ ≤ (X : Set H).ncard := Set.ncard_le_ncard hSX (Set.toFinite _)
    _ = Nat.card X := (Nat.card_coe_set_eq (X : Set H)).symm

end F4Model

open F4Model

section Weyl

variable {G : Type} [Group G]

theorem orderOf_conj_simple_mul {H : Type} [Group H] (φ : CoxeterMatrix.F₄.Group →* H)
    (hφ : Function.Injective φ) (w : CoxeterMatrix.F₄.Group) (i j : Fin 4) :
    orderOf (φ (w * CoxeterMatrix.F₄.simple i * w⁻¹) * φ (w * CoxeterMatrix.F₄.simple j * w⁻¹)) =
      CoxeterMatrix.F₄ i j := by
  have h1 : φ (w * CoxeterMatrix.F₄.simple i * w⁻¹) * φ (w * CoxeterMatrix.F₄.simple j * w⁻¹) =
      φ (w * (CoxeterMatrix.F₄.simple i * CoxeterMatrix.F₄.simple j) * w⁻¹) := by
    rw [← map_mul]
    congr 1
    group
  have hsc : orderOf (w * (CoxeterMatrix.F₄.simple i * CoxeterMatrix.F₄.simple j) * w⁻¹) =
      orderOf (CoxeterMatrix.F₄.simple i * CoxeterMatrix.F₄.simple j) :=
    (SemiconjBy.orderOf_eq w (by simp [SemiconjBy, mul_assoc])).symm
  rw [h1, orderOf_injective φ hφ, hsc]
  simpa [CoxeterMatrix.toCoxeterSystem_simple] using
    CoxeterSystem.orderOf_simple_mul_simple CoxeterMatrix.F₄.toCoxeterSystem i j

theorem ggWeylReflectionGroup_of_card_le_48 [Finite G] {p : ℕ} {Bs : Subgroup G}
    (R : F4Rep CoxeterMatrix.F₄.Group) (hRs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i)
    (φ : CoxeterMatrix.F₄.Group →* MulAut ↥Bs) (hφ : Function.Injective φ)
    (w : CoxeterMatrix.F₄.Group) {X : Subgroup (MulAut ↥Bs)}
    (hX : ∀ i : Fin 4, i ≠ 0 → φ (w * CoxeterMatrix.F₄.simple i * w⁻¹) ∈ X)
    (hcard : Nat.card X ≤ 48)
    (hrefl : ∀ i : Fin 4, GGIsReflection p (φ (w * CoxeterMatrix.F₄.simple i * w⁻¹))) :
    GGWeylReflectionGroup p X := by
  classical
  let σ : Fin 3 → Fin 4 := ![3, 2, 1]
  have hσ0 : ∀ k : Fin 3, σ k ≠ 0 := by decide
  have hσM : ∀ k l : Fin 3, CoxeterMatrix.F₄ (σ k) (σ l) = CoxeterMatrix.B 3 k l := by
    intro k l
    fin_cases k <;> fin_cases l <;> rfl
  let t : Fin 3 → MulAut ↥Bs := fun k => φ (w * CoxeterMatrix.F₄.simple (σ k) * w⁻¹)
  have hlift : (CoxeterMatrix.B 3).IsLiftable t := by
    intro k l
    have h := pow_orderOf_eq_one (t k * t l)
    rwa [show orderOf (t k * t l) = CoxeterMatrix.B 3 k l from
      (orderOf_conj_simple_mul φ hφ w (σ k) (σ l)).trans (hσM k l)] at h
  let cs := (CoxeterMatrix.B 3).toCoxeterSystem
  let lam : (CoxeterMatrix.B 3).Group →* MulAut ↥Bs := cs.lift ⟨t, hlift⟩
  have hlam : ∀ k, lam ((CoxeterMatrix.B 3).simple k) = t k := by
    intro k
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    exact cs.lift_apply_simple hlift k
  have hle : lam.range ≤ X := by
    rw [MonoidHom.range_eq_map, ← cs.subgroup_closure_range_simple, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    rw [CoxeterMatrix.toCoxeterSystem_simple, hlam]
    exact hX (σ k) (hσ0 k)
  have hmem : ∀ i : Fin 4, i ≠ 0 → φ (w * R.s i * w⁻¹) ∈ lam.range := by
    intro i hi
    obtain ⟨k, rfl⟩ : ∃ k : Fin 3, σ k = i := by
      fin_cases i
      · exact absurd rfl hi
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
    exact ⟨(CoxeterMatrix.B 3).simple k, by rw [hlam, hRs]⟩
  have hge : 48 ≤ Nat.card lam.range := le_card_of_conj_mem R φ hφ w hmem
  have hrange : lam.range = X := Subgroup.eq_of_le_of_card_ge hle (hcard.trans hge)
  have hcardB : Nat.card (CoxeterMatrix.B 3).Group = 48 :=
    (ggCoxeterB_card 3 (by norm_num)).trans (by norm_num [Nat.factorial])
  have hinj : Function.Injective lam := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have h := Subgroup.card_ker_mul_card_range lam
    have hr : Nat.card lam.range = 48 := le_antisymm (hrange ▸ hcard) hge
    rw [hr, hcardB] at h
    exact Subgroup.card_eq_one.mp (by omega)
  have hWB : GGIsWeylMatrix (CoxeterMatrix.B 3) :=
    Or.inl ⟨3, Equiv.refl _, by omega,
      Or.inr (Or.inl ⟨by norm_num, (ggCoxeterMatrix_reindex_refl _).symm⟩)⟩
  refine ⟨Fin 3, CoxeterMatrix.B 3, hWB,
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun k => ?_⟩
  show GGIsReflection p (lam ((CoxeterMatrix.B 3).simple k))
  rw [hlam]
  exact hrefl (σ k)

theorem sup_ggAutomizer_eq_of_frame {Bs L K A : Subgroup G}
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (w : CoxeterMatrix.F₄.Group)
    (hL : ∀ i : Fin 4, i ≠ 3 →
      ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) ∈ ggAutomizer L Bs)
    (hA : ∀ i : Fin 4, i ≠ 0 →
      ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) ∈ ggAutomizer A Bs)
    (hAW : ggAutomizer A Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs) :
    ggAutomizer L Bs ⊔ ggAutomizer A Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
  refine le_antisymm (sup_le le_sup_left hAW) fun φ hφ => ?_
  set P : Subgroup CoxeterMatrix.F₄.Group :=
    (ggAutomizer L Bs ⊔ ggAutomizer A Bs).comap
      ((ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom) with hP
  have hsimple : ∀ i, CoxeterMatrix.F₄.simple i ∈ P.comap (MulAut.conj w).toMonoidHom := by
    intro i
    change ((e (w * CoxeterMatrix.F₄.simple i * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
      MulAut ↥Bs) ∈ ggAutomizer L Bs ⊔ ggAutomizer A Bs
    by_cases h3 : i = 3
    · subst h3
      exact (le_sup_right : ggAutomizer A Bs ≤ _) (hA 3 (by decide))
    · exact (le_sup_left : ggAutomizer L Bs ≤ _) (hL i h3)
  have htop : P.comap (MulAut.conj w).toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← CoxeterMatrix.F₄.toCoxeterSystem.subgroup_closure_range_simple,
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [CoxeterMatrix.toCoxeterSystem_simple]
    exact hsimple i
  set z := e.symm ⟨φ, hφ⟩ with hz
  have hzP : w⁻¹ * z * w ∈ P.comap (MulAut.conj w).toMonoidHom := by
    rw [htop]
    exact Subgroup.mem_top _
  have hw : w * (w⁻¹ * z * w) * w⁻¹ = z := by group
  have hzP' : z ∈ P := by
    have h := Subgroup.mem_comap.mp hzP
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hw] at h
    exact h
  have hez : ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) = φ := by
    rw [hz, MulEquiv.apply_symm_apply]
  rw [← hez]
  exact hzP'

end Weyl

section Endpoint

theorem ggF4QGeFourPlusPlane_of_frame (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1) (hmark : GGCentralImage .POmegaMinus 4 f L)
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (he : ∀ i, GGIsReflection p
      ((e (CoxeterMatrix.F₄.simple i) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs))
    (R : F4Rep CoxeterMatrix.F₄.Group) (hRs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i)
    {a : Fin 3 → CoxeterMatrix.F₄.Group}
    (haL : ∀ z, z ∈ Subgroup.closure (Set.range a) →
      ((e z : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs)
    {ga : CoxeterMatrix.F₄.Group}
    (hga : ga * a 0 * ga⁻¹ = R.s 0 ∧ ga * a 1 * ga⁻¹ = R.s 1 ∧ ga * a 2 * ga⁻¹ = R.s 2)
    (w₂ : CoxeterMatrix.F₄.Group)
    (hv : (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E1.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E1.neg.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E2.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E2.neg.toFun)
    (hrL : ((e (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
      MulAut ↥Bs) ∈ ggAutomizer L Bs)
    (huL : ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
      MulAut ↥Bs) ∈ ggAutomizer L Bs)
    (hvL : ((e (w₂ * CoxeterMatrix.F₄.simple 0 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
      MulAut ↥Bs) ∈ ggAutomizer L Bs)
    {n : G} (hnN : n ∈ Subgroup.normalizer (Bs : Set G))
    (hn : ∀ b : ↥Bs, ((((e (w₂ * CoxeterMatrix.F₄.simple 3 * w₂⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) b : ↥Bs) : G) = n * b * n⁻¹)
    (hnc : n ∈ Subgroup.centralizer (ggRankOneIn L Bs
      ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
        MulAut ↥Bs) : Set G)) :
    p = 5 ∧ f = 2 ∧ ∃ (D' J' : Subgroup G) (d : G) (A : Subgroup G),
      D' = ggHyperplane Bs ((e (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ⊓
        ggHyperplane Bs ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∧
      J' = LargeEvenLayer (L ⊓ Subgroup.centralizer (D' : Set G)) ∧
      D' = Subgroup.closure {x, d} ∧ LargeEvenStdSub p B x L D' J' ∧
      GGConfig p B Bs x L D' J' ∧ GGNbr p B x D' J' d A ∧
      A = ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J' ∧
      A.map (MulAut.conj n).toMonoidHom = A ∧ J' ≤ A ∧
      GGHasLabel ⟨.A, 3, f⟩ (↥J' ⧸ Subgroup.center ↥J') ∧ Subgroup.center ↥J' = ⊥ ∧
      GGInnerDiagOn Bs A ∧ GGHasLabel ⟨.A, 5, 2⟩ (↥A ⧸ Subgroup.center ↥A) ∧
      GGCentralImage .PSL 6 2 A ∧
      GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) d A ∧
      ggAutomizer L Bs ⊔ ggAutomizer A Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
  classical
  have hR : GGSecFiveRestHyp p B Bs x L D J := hcfg.1
  have hc : GGConfig p B Bs x L D J := hR.1
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have : Fact p.Prime := ⟨hpp⟩
  have hAind : (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  have hF4W : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e :=
    ⟨hF4W, he⟩
  set φW : CoxeterMatrix.F₄.Group →* MulAut ↥Bs :=
    (ggAutomizer L Bs ⊔ ggAutomizer K Bs).subtype.comp e.toMonoidHom with hφWdef
  have hφW : Function.Injective φW := Subtype.val_injective.comp e.injective
  have hInnL : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  obtain ⟨-, -, hxBs, hLx, hBs4⟩ := hc.tableB_facts
  have hZL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p := by
    rw [hc.bstar_inf_centralizer_L, Nat.card_zpowers,
      orderOf_eq_prime (hEl.2 x hxBs) hc.1.2.2.2.2.2.2.1.2.2.1]
  obtain ⟨-, -, -, hL4⟩ := plusMember_facts_of_image ggInnerDiagMpInput_holds hpp hEl hNT hBs4 hf
    hpq hmark hInnL hZL
  obtain ⟨hB, hcard4⟩ := hc.eq_bstar_of_card_le hL4.le
  have hxne : x ≠ 1 := hc.1.2.2.2.2.2.2.1.2.2.1
  obtain ⟨xB, hxB⟩ : ∃ xB : ↥Bs, (xB : G) = x := ⟨⟨x, hxBs⟩, rfl⟩
  have hx1 : xB ≠ 1 := fun h => hxne (by rw [← hxB, h, Subgroup.coe_one])
  have hxL : ∀ φ ∈ ggAutomizer L Bs, φ xB = xB := by
    intro φ hφ
    obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
    apply Subtype.ext
    rw [hg xB, hxB]
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)
    rw [hgx]
    group
  have hfr := exists_bstarFrame_at hp2 hEl hNT hcard4 hAind e he R hRs haL hga hx1 hxL w₂ hv
  simp only [hRs] at hfr
  obtain ⟨r, hrdef⟩ : ∃ r : MulAut ↥Bs, r = φW (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) :=
    ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : MulAut ↥Bs, u = φW (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) :=
    ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : MulAut ↥Bs, v = φW (w₂ * CoxeterMatrix.F₄.simple 0 * w₂⁻¹) :=
    ⟨_, rfl⟩
  obtain ⟨r', hr'def⟩ : ∃ r' : MulAut ↥Bs, r' = φW (w₂ * CoxeterMatrix.F₄.simple 3 * w₂⁻¹) :=
    ⟨_, rfl⟩
  have hrdef' : r = ((e (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) := hrdef
  have hudef' : u = ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) := hudef
  have hvdef' : v = ((e (w₂ * CoxeterMatrix.F₄.simple 0 * w₂⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) := hvdef
  have hr'def' : r' = ((e (w₂ * CoxeterMatrix.F₄.simple 3 * w₂⁻¹) :
      ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) := hr'def
  rw [← hrdef', ← hudef', ← hr'def'] at hfr
  rw [← hrdef'] at hrL
  rw [← hudef'] at huL hnc
  rw [← hvdef'] at hvL
  rw [← hr'def'] at hn
  obtain ⟨d, hrx, hux, hrd, hud, hr'd, hpl, hr'x, hmv, hopp⟩ := hfr
  have hru : orderOf (r * u) = 4 := by
    rw [hrdef, hudef, orderOf_conj_simple_mul φW hφW]
    rfl
  have huv : orderOf (u * v) = 3 := by
    rw [hudef, hvdef, orderOf_conj_simple_mul φW hφW]
    rfl
  have hrr' : orderOf (r * r') = 3 := by
    rw [hrdef, hr'def, orderOf_conj_simple_mul φW hφW]
    rfl
  have hrR : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 ⟨w₂, 2, hrdef'⟩
  have huR : GGIsReflection p u := ggCoxRefl_isReflection hpres.2 ⟨w₂, 1, hudef'⟩
  have hvR : GGIsReflection p v := ggCoxRefl_isReflection hpres.2 ⟨w₂, 0, hvdef'⟩
  have hr'R : GGIsReflection p r' := ggCoxRefl_isReflection hpres.2 ⟨w₂, 3, hr'def'⟩
  have hr2 : r * r = 1 := by rw [← pow_two]; exact hrR.1
  have hu2 : u * u = 1 := by rw [← pow_two]; exact huR.1
  have hru4 : (r * u) ^ 4 = 1 := by rw [← hru]; exact pow_orderOf_eq_one _
  have hru2 : (r * u) ^ 2 ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hru] at h'
    norm_num at h'
  have huv3 : (u * v) ^ 3 = 1 := by rw [← huv]; exact pow_orderOf_eq_one _
  have huvne : u ≠ v := by
    intro h
    rw [h, ← pow_two, hvR.1, orderOf_one] at huv
    omega
  have hrr'3 : (r * r') ^ 3 = 1 := by rw [← hrr']; exact pow_orderOf_eq_one _
  have hrr'ne : r ≠ r' := by
    intro h
    rw [h, ← pow_two, hr'R.1, orderOf_one] at hrr'
    omega
  set D' : Subgroup G := ggHyperplane Bs r ⊓ ggHyperplane Bs u with hD'def
  set J' : Subgroup G := LargeEvenLayer (L ⊓ Subgroup.centralizer (D' : Set G)) with hJ'def
  obtain ⟨hJcomp, hJcent, hSrJ, hSuJ, hpJ, hsmall, hhJ, hZJ⟩ :=
    ggOppPlus_plane_of_cfg hcfg hf hpq hmark hrL huL hr2 hu2 hru4 hru2 hxB hrx hux hrd hud hpl
      hmv hJ'def.symm
  obtain ⟨hPq, hPcard⟩ := ggOppPlus_rankOne_of_cfg hcfg hf hpq hmark huL huR
  obtain ⟨hD'eq, hStd, hnbr, hAn, hJA, -, hrA, huA, hr'A⟩ :=
    exists_oppPumpup_of_plane (ggPumpupInput_of_lBalance hLB) hc hB hpres w₂ hrdef' hudef' hr'def'
      hrL huL hxB hrx hux hrd hud hr'd hpl hr'x hmv hnN hn hnc hJ'def.symm hJcomp hJcent hSrJ hSuJ
      hpJ hsmall hPq hPcard
  set A : Subgroup G := ggLayerClosure p (Subgroup.centralizer ({(d : G)} : Set G)) J' with hAdef
  have hc' : GGConfig p B Bs x L D' J' := hR.config_of_stdSub hStd
  have hInnA : GGInnerDiagOn Bs A := hNPLA G p B Bs x L D J hR D' J' hStd d A hnbr
  have hAN := isComponentOf_of_isNeighborOf hc'.1.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hc'.2.2 hnbr)
  have hd1 : d ≠ 1 := by
    have h := hopp 1 0
    rwa [map_one, OneMemClass.coe_one, MulAut.one_apply, pow_zero] at h
  have hdG1 : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hBCA : Bs ⊓ Subgroup.centralizer (A : Set G) = Subgroup.zpowers (d : G) := by
    have h := inf_centralizer_eq_zpowers_of_sHat hnbr.1
    rw [hB] at h
    exact h
  have hZA : Nat.card ↥(Bs ⊓ Subgroup.centralizer (A : Set G)) = p := by
    rw [hBCA, Nat.card_zpowers, orderOf_eq_prime (hEl.2 _ d.2) hdG1]
  have hBsN : Bs ≤ Subgroup.normalizer (A : Set G) := by
    rw [← hB]
    exact hAN.2
  have hOm : ¬ GGHasLabel ⟨.twD, 4, f⟩ (↥A ⧸ Subgroup.center ↥A) :=
    not_twD4_of_plusMembers ggInnerDiagMpInput_holds hpp hEl hNT hBs4 hf hpq hxBs d.2
      hc.1.2.2.2.2.2.2.1.2.2.2.1.2.1 hAN.1.2.1 hBsN hmark hInnL hZL hAN.1.2.2.1 hInnA hZA
      hrL huL hvL hrA hr'A hrR huR hvR hr'R huvne huv3 hru4 hru2 hrr'ne hrr'3
  have hΛJ : LargeEvenInLambda2 (⟨.A, 3, f⟩ : LargeEvenLabel) :=
    ⟨le_trans (by norm_num : 1 ≤ 2) hf, by norm_num, fun _ => hf⟩
  obtain ⟨hp5, hf2, -, hhA⟩ := ggOppPlus_psl6Four_of_config hB3 hLB hc' hInnL hInnA hnbr hJA hpJ
    hJcent.le hf hpq hΛJ hhJ hOm
  have hAimg : GGCentralImage .PSL 6 2 A :=
    ggF4Ends_centralImage_PSL (m := 5) hAN.1.2.2.1 (by norm_num) le_rfl (by omega) hhA
  have hdC : (d : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hAN.1.1 hh))
  have hfixA : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer A Bs, φ b = b) →
      (b : G) ∈ Subgroup.centralizer (A : Set G) := by
    intro b hb
    have hxp' : xB ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hxB, Subgroup.coe_one]
      exact hEl.2 x hxBs)
    obtain ⟨j, hj⟩ := exists_eq_pow_of_frame_fix hpp hxp' hrx hr'd hpl hr'x (hb r hrA) (hb u huA)
      (hb r' hr'A)
    rw [hj, Subgroup.coe_pow]
    exact pow_mem hdC j
  have hFL : GGFixLineComp Bs (d : G) A := hc'.fixLineComp_nbr_of_fix hB hnbr hfixA
  have hoppW : ∀ w ∈ (ggAutomizer L Bs ⊔ ggAutomizer K Bs), ∀ b : ↥Bs, (b : G) = (d : G) →
      ((w b : ↥Bs) : G) ∉ Subgroup.zpowers x := by
    rw [← hxB]
    exact forall_not_mem_zpowers_of_frame e hopp
  have hgen : ∀ k : Fin 4, k ≠ 0 → φW (w₂ * CoxeterMatrix.F₄.simple k * w₂⁻¹) ∈
      ggAutomizer A Bs := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · rw [hudef] at huA
      exact huA
    · rw [hrdef] at hrA
      exact hrA
    · rw [hr'def] at hr'A
      exact hr'A
  have hA48 : Nat.card ↥(ggAutomizer A Bs) ≤ 48 :=
    card_ggAutomizer_le_48_of_psl6Four hc' hInnA hnbr hp5 hhA
  have hAAW : ggAutomizer A Bs ≤ (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
    have h := le_range_of_card_le_48 R φW hφW w₂ (X := ggAutomizer A Bs)
      (fun k hk => by rw [hRs]; exact hgen k hk) hA48
    intro φ hφ
    obtain ⟨v', rfl⟩ := h hφ
    exact (e v').2
  have hWRA : GGWeylReflectionGroup p (ggAutomizer A Bs) :=
    ggWeylReflectionGroup_of_card_le_48 R hRs φW hφW w₂ hgen hA48
      (fun i => ggCoxRefl_isReflection hpres.2 ⟨w₂, i, rfl⟩)
  have hLA : ggAutomizer L Bs ⊔ ggAutomizer A Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    refine sup_ggAutomizer_eq_of_frame (e := e) w₂ (fun i hi => ?_) (fun i hi => ?_) hAAW
    · fin_cases i
      · show ((e (w₂ * CoxeterMatrix.F₄.simple 0 * w₂⁻¹) :
            ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs
        rw [← hvdef']
        exact hvL
      · show ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) :
            ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs
        rw [← hudef']
        exact huL
      · show ((e (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) :
            ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer L Bs
        rw [← hrdef']
        exact hrL
      · exact absurd rfl hi
    · fin_cases i
      · exact absurd rfl hi
      · show ((e (w₂ * CoxeterMatrix.F₄.simple 1 * w₂⁻¹) :
            ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer A Bs
        rw [← hudef']
        exact huA
      · show ((e (w₂ * CoxeterMatrix.F₄.simple 2 * w₂⁻¹) :
            ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer A Bs
        rw [← hrdef']
        exact hrA
      · show ((e (w₂ * CoxeterMatrix.F₄.simple 3 * w₂⁻¹) :
            ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∈ ggAutomizer A Bs
        rw [← hr'def']
        exact hr'A
  refine ⟨hp5, hf2, D', J', (d : G), A, by rw [hD'def, hrdef', hudef'], hJ'def, hD'eq, hStd, hc',
    hnbr, hAdef, hAn, hJA, hhJ, hZJ, hInnA, hhA, hAimg, ⟨hFL, hdG1, hBsN, hAAW, hWRA, hoppW⟩, hLA⟩

theorem ggF4QGeFourOppPlus_plane_at (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr p B x D J y K)
    (hWF4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1) (hLim : GGCentralImage .POmegaMinus 4 f L)
    (hεL : ∃ ε : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer L Bs), ∀ i, GGIsReflection p
      ((ε ((CoxeterMatrix.B 3).simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (hfam : ∀ (e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e' →
        GGOriginalRankOneFamily p L (L ⊔ K) Bs (ggCoxRefl CoxeterMatrix.F₄ e')) :
    p = 5 ∧ f = 2 ∧ ∃ (e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs))
      (w : CoxeterMatrix.F₄.Group) (n : G),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e' ∧ n ∈ L ⊔ K ∧
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((((e' (w * CoxeterMatrix.F₄.simple 3 * w⁻¹) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) b : ↥Bs) : G) = n * b * n⁻¹) ∧
      n ∈ Subgroup.centralizer (ggRankOneIn L Bs
        ((e' (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) : ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
          MulAut ↥Bs) : Set G) ∧
      ∃ (D' J' : Subgroup G) (d : G) (A : Subgroup G),
      D' = ggHyperplane Bs ((e' (w * CoxeterMatrix.F₄.simple 2 * w⁻¹) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ⊓
        ggHyperplane Bs ((e' (w * CoxeterMatrix.F₄.simple 1 * w⁻¹) :
          ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs) ∧
      J' = LargeEvenLayer (L ⊓ Subgroup.centralizer (D' : Set G)) ∧
      D' = Subgroup.closure {x, d} ∧ LargeEvenStdSub p B x L D' J' ∧
      GGConfig p B Bs x L D' J' ∧ GGNbr p B x D' J' d A ∧
      A = ggLayerClosure p (Subgroup.centralizer ({d} : Set G)) J' ∧
      A.map (MulAut.conj n).toMonoidHom = A ∧ J' ≤ A ∧
      GGHasLabel ⟨.A, 3, f⟩ (↥J' ⧸ Subgroup.center ↥J') ∧ Subgroup.center ↥J' = ⊥ ∧
      GGInnerDiagOn Bs A ∧ GGHasLabel ⟨.A, 5, 2⟩ (↥A ⧸ Subgroup.center ↥A) ∧
      GGCentralImage .PSL 6 2 A ∧
      GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) d A ∧
      ggAutomizer L Bs ⊔ ggAutomizer A Bs = ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
  classical
  set W := ggAutomizer L Bs ⊔ ggAutomizer K Bs with hWdef
  have hcfg : GGF4QGeFourCfg p B Bs x L D J y K := ⟨hR, hW, hq, hNb⟩
  have hEl : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  obtain ⟨hpp, hp2⟩ : p.Prime ∧ p ≠ 2 := by
    obtain ⟨⟨⟨⟨-, -, -, -, -, hβ, -⟩, -⟩, -⟩, -⟩ := hcfg
    exact ⟨hβ.1, hβ.2.1⟩
  have hAind : W ≤ ggInduced ⊤ Bs := by
    intro φ hφ
    have h1 : φ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
    rw [ggAutomizer_eq] at h1
    exact h1
  obtain ⟨εL, hεL⟩ := hεL
  obtain ⟨e, he⟩ := hWF4
  have hF4W : GGIsWeylMatrix CoxeterMatrix.F₄ :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩))))
  have hpres : GGCoxeterPres p W CoxeterMatrix.F₄ e := ⟨hF4W, he⟩
  obtain ⟨a, ha, ha01, ha12, ha02, haL⟩ :=
    exists_f4Triple_of_weyl hpp hp2 hEl hNT hAind hpres le_sup_left εL hεL (Equiv.refl _)
      (fun _ _ => rfl)
  obtain ⟨R, hRs0⟩ := exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hRs : ∀ k, R.s k = CoxeterMatrix.F₄.simple k := by
    intro k
    rw [hRs0 k, CoxeterMatrix.toCoxeterSystem_simple]
  have haR : ∀ k, R.IsRefl (a k) := fun k => (F4Rep.isRefl_iff hRs0).2 (ha k)
  obtain ⟨e', a', g, he', haL', hga⟩ :=
    exists_f4Pres_tripleB e he R hRs haR ha01 ha12 ha02 fun z hz => (haL z).1 hz
  have hmemL : ∀ k : Fin 3, ((e' (g⁻¹ * CoxeterMatrix.F₄.simple k.castSucc * g⁻¹⁻¹) : ↥W) :
      MulAut ↥Bs) ∈ ggAutomizer L Bs := by
    intro k
    apply haL'
    have hk : g * a' k * g⁻¹ = R.s k.castSucc := by
      fin_cases k
      · exact hga.1
      · exact hga.2.1
      · exact hga.2.2
    rw [show g⁻¹ * CoxeterMatrix.F₄.simple k.castSucc * g⁻¹⁻¹ = a' k by
      rw [← hRs, ← hk]; group]
    exact Subgroup.subset_closure ⟨k, rfl⟩
  obtain ⟨n, hnLK, hnN, hn, hnc⟩ := ggF4QGeFourR3S1S3_plus hcfg hf hpq hLim ⟨hF4W, he'⟩
    (hfam e' ⟨hF4W, he'⟩) εL hεL (Equiv.refl _) (fun _ _ => rfl) g⁻¹ rfl rfl (hmemL 1)
  obtain ⟨hp5, hf2, hrest⟩ := ggF4QGeFourPlusPlane_of_frame hLB hB3 hNPLA hcfg hf hpq hLim he' R
    hRs haL' hga g⁻¹ (Or.inl (by rw [mul_inv_cancel, inv_one, map_one, Matrix.one_mulVec]))
    (hmemL 2) (hmemL 1) (hmemL 0) hnN hn hnc
  exact ⟨hp5, hf2, e', g⁻¹, n, ⟨hF4W, he'⟩, hnLK, hnN, hn, hnc, hrest⟩

theorem ggF4QGeFourOppPlus_at (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp p B Bs x L D J) (hW : GGSecFiveWeylCase' p B Bs x D J)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L) {y : G} {K : Subgroup G}
    (hNb : GGNbr p B x D J y K)
    (hWF4 : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {f : ℕ} (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1) (hLim : GGCentralImage .POmegaMinus 4 f L)
    (hεL : ∃ ε : (CoxeterMatrix.B 3).Group ≃* ↥(ggAutomizer L Bs), ∀ i, GGIsReflection p
      ((ε ((CoxeterMatrix.B 3).simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (hfam : ∀ (e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)),
      GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e' →
        GGOriginalRankOneFamily p L (L ⊔ K) Bs (ggCoxRefl CoxeterMatrix.F₄ e')) :
    p = 5 ∧ f = 2 ∧ ∃ (z : G) (A : Subgroup G),
      GGF4QGeFourOppEnd p Bs x (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z A ∧
        GGCentralImage .PSL 6 2 A := by
  obtain ⟨hp5, hf2, -, -, -, -, -, -, -, -, -, -, d, A, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hAimg, hEnd, -⟩ :=
    ggF4QGeFourOppPlus_plane_at hLB hB3 hNPLA hR hW hq hNb hWF4 hf hpq hLim hεL hfam
  exact ⟨hp5, hf2, d, A, hEnd, hAimg⟩

theorem ggF4QGeFourOppPlusInput_of_inputs (hLB : GGLBalanceInput) (hB3 : GGK0ExcB3)
    (hNPLA : GGNewPlaneLocalActionInput) : GGF4QGeFourOppPlusInput := by
  intro G _ _ p B Bs x L D J hR hW hq y K hNb _ _ hWF4 f hf hpq hLim
  have hcfg : GGF4QGeFourCfg p B Bs x L D J y K := ⟨hR, hW, hq, hNb⟩
  exact ggF4QGeFourOppPlus_at hLB hB3 hNPLA hR hW hq hNb hWF4 hf hpq hLim
    (ggF4Plus_original_b3_of_cfg hcfg hf hpq hLim)
    (fun _ hpres' => ggF4OriginalRankOneFamily_plus hcfg hpres' hf hpq hLim)

end Endpoint

end CFSG.StandardType

end
