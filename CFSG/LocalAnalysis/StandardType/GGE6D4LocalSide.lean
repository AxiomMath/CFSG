module

public import CFSG.LocalAnalysis.StandardType.GGE6D4LocalJ
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import CFSG.LocalAnalysis.StandardType.GGE6D4ReflConj
import CFSG.LocalAnalysis.StandardType.GGE6D4LocalDatum
import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv
import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor

public section

namespace CFSG.StandardType.E6D4Side

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem xDatumFin_of_torData {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hMC : GGIntCartan M C) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (φ : Fin N → MulAut ↥Bs) (h : Fin N → V) (α : Fin N → Module.Dual (ZMod p) V),
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧ (∀ i, GGIsReflection p (φ i)) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      (∃ f : M.Group ≃* ↥(ggAutomizer X Bs), ∀ i, (f (M.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, hVadd, hVmod, hι⟩ := exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, α, hlin, hpair, -, -⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  refine ⟨V, hVadd, hVmod, ι, (fun k => ggTDρB X Bs (ggTDnH w hnk k)),
    (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))), α, hlin, ?_, hpair, ⟨e, he⟩, hcl⟩
  intro i
  exact ggIsReflection_of_eq_reflection hp2 ι (hfx i) (ggLin_eq_reflection ι (hfx i) (hlin i))

theorem d4Map_facts :
    (∀ k, E6D4Refl.d4Map k ≠ 0 ∧ E6D4Refl.d4Map k ≠ 5) ∧ Function.Injective E6D4Refl.d4Map ∧
      ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → ∃ k, E6D4Refl.d4Map k = j := by
  decide

theorem coxeterE6_d4Map (k l : Fin 4) :
    CoxeterMatrix.E₆ (E6D4Refl.d4Map k) (E6D4Refl.d4Map l) = ggCoxeterMatrixD 4 k l := by
  fin_cases k <;> fin_cases l <;> rfl

theorem sideDatum_of_d4
    {G : Type} [Group G] [Finite G] {Bs X J : Subgroup G} {z : G}
    (hXD : GGResXDatumE6x 3 Bs X z) (hJX : ggAutomizer J Bs ≤ ggAutomizer X Bs)
    {VJ : Type} [AddCommGroup VJ] [Module (ZMod 3) VJ] (ιJ : Additive ↥Bs ≃+ VJ)
    (φJ : Fin 4 → MulAut ↥Bs) (hJ : Fin 4 → VJ) (αJ : Fin 4 → Module.Dual (ZMod 3) VJ)
    (hlinJ : ∀ k w, ggLin (p := 3) ιJ (φJ k) w = w - αJ k w • hJ k)
    (hreflJ : ∀ k, GGIsReflection 3 (φJ k))
    (hpairJ : ∀ k l, αJ k (hJ l) = (CartanMatrix.D 4 k l : ZMod 3))
    (fJ : (ggCoxeterMatrixD 4).Group ≃* ↥(ggAutomizer J Bs))
    (hfJ : ∀ k, (fJ ((ggCoxeterMatrixD 4).simple k) : MulAut ↥Bs) = φJ k)
    (hclJ : ggAutomizer J Bs = Subgroup.closure (Set.range φJ)) :
    GGResTwoNodeSideDatum 3 Bs X J := by
  classical
  obtain ⟨Λ, iΛf, iΛd, M, C, V, iVa, iVm, ι, φ, h, α, e, hM, hWM, hMC, hlin, hrefl, hpair,
    ⟨f, hf⟩, hcl, -⟩ := hXD
  letI := iΛf; letI := iΛd; letI := iVa; letI := iVm
  subst hM
  have hRCS : GGReflConjSimple 3 (ggAutomizer X Bs) φ :=
    ggReflConjSimple_of_weylMatrix (by norm_num) (Or.inr (Or.inl ⟨e, rfl⟩))
      (by rw [← Fintype.card_congr e, Fintype.card_fin]; norm_num) hMC ι φ h α hpair hlin hcl
  have hφJX : ∀ k, φJ k ∈ ggAutomizer X Bs := fun k => hJX (by rw [← hfJ k]; exact (fJ _).2)
  let t : Fin 4 → (CoxeterMatrix.E₆.reindex e).Group := fun k => f.symm ⟨φJ k, hφJX k⟩
  have hft : ∀ k, (f (t k) : MulAut ↥Bs) = φJ k := fun k => by simp [t]
  have htc : ∀ k, ∃ (w : (CoxeterMatrix.E₆.reindex e).Group) (i : Λ),
      t k = w * (CoxeterMatrix.E₆.reindex e).simple i * w⁻¹ := by
    intro k
    obtain ⟨g, hg, i, hgi⟩ := hRCS (φJ k) (hφJX k) (hreflJ k)
    refine ⟨f.symm ⟨g, hg⟩, i, f.injective (Subtype.ext ?_)⟩
    rw [hft, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hf]
    exact hgi
  have hto : ∀ k l, orderOf (t k * t l) = ggCoxeterMatrixD 4 k l := by
    intro k l
    have h1 : orderOf (t k * t l) = orderOf (φJ k * φJ l) := by
      rw [← MulEquiv.orderOf_eq f, map_mul, ← Subgroup.orderOf_coe, Subgroup.coe_mul, hft, hft]
    have h2 : φJ k * φJ l = ((fJ ((ggCoxeterMatrixD 4).simple k *
        (ggCoxeterMatrixD 4).simple l) : ↥(ggAutomizer J Bs)) : MulAut ↥Bs) := by
      rw [map_mul, Subgroup.coe_mul, hfJ, hfJ]
    rw [h1, h2, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← CoxeterMatrix.toCoxeterSystem_simple]
    exact CoxeterSystem.orderOf_simple_mul_simple _ k l
  let ψ : (CoxeterMatrix.E₆.reindex e).Group ≃* WeylGroup Tag.E6 :=
    (CoxeterMatrix.E₆.reindexGroupEquiv e).trans ggE6Row_coxeterGroupEquiv
  have hψs : ∀ i, ψ ((CoxeterMatrix.E₆.reindex e).simple i) = simple Tag.E6 (e.symm i) := by
    intro i
    simp only [ψ, MulEquiv.trans_apply, CoxeterMatrix.reindexGroupEquiv_apply_simple,
      ggE6Row_coxeterGroupEquiv_simple]
  obtain ⟨u₀, hu₀⟩ := E6D4Refl.exists_conj_eq_simple_d4Map (fun k => ψ (t k))
    (fun k => by
      obtain ⟨w, i, hwi⟩ := htc k
      exact ⟨ψ w, e.symm i, by rw [hwi, map_mul, map_mul, map_inv, hψs]⟩)
    (fun k l => by rw [← map_mul, MulEquiv.orderOf_eq, hto])
  set u : (CoxeterMatrix.E₆.reindex e).Group := ψ.symm u₀ with hu
  have htu : ∀ k, t k = u⁻¹ * (CoxeterMatrix.E₆.reindex e).simple (e (E6D4Refl.d4Map k)) * u := by
    intro k
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, hψs, e.symm_apply_apply, ← hu₀ k, hu,
      MulEquiv.apply_symm_apply]
    group
  set g : MulAut ↥Bs := (f u : MulAut ↥Bs) with hg
  let φ' : Λ → MulAut ↥Bs := fun i => g⁻¹ * φ i * g
  let f' : (CoxeterMatrix.E₆.reindex e).Group ≃* ↥(ggAutomizer X Bs) := (MulAut.conj u⁻¹).trans f
  have hf' : ∀ i, (f' ((CoxeterMatrix.E₆.reindex e).simple i) : MulAut ↥Bs) = φ' i := by
    intro i
    show (f (u⁻¹ * (CoxeterMatrix.E₆.reindex e).simple i * u⁻¹⁻¹) : MulAut ↥Bs) = g⁻¹ * φ i * g
    rw [inv_inv, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hf]
  have hφ'J : ∀ k, φ' (e (E6D4Refl.d4Map k)) = φJ k := by
    intro k
    rw [← hft k, htu k, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hf]
  let ι' : Additive ↥Bs ≃+ V := (MulEquiv.toAdditive g).trans ι
  have hlin'0 : ∀ i, ggLin (p := 3) ι' (φ' i) = ggLin (p := 3) ι (φ i) := by
    intro i
    refine LinearEquiv.ext fun v => ?_
    rw [ggLin_apply, ggLin_apply]
    simp [ι', φ', MulEquiv.toAdditive_apply_apply, MulEquiv.toAdditive_symm_apply_apply]
  have hlin' : ∀ i w, ggLin (p := 3) ι' (φ' i) w = w - α i w • h i := fun i w => by
    rw [hlin'0]
    exact hlin i w
  have hrefl' : ∀ i, GGIsReflection 3 (φ' i) := fun i => by
    simpa [φ'] using (hrefl i).conj g⁻¹
  have hcl' : ggAutomizer X Bs = Subgroup.closure (Set.range φ') := by
    let F : (CoxeterMatrix.E₆.reindex e).Group →* MulAut ↥Bs :=
      (ggAutomizer X Bs).subtype.comp f'.toMonoidHom
    have hFr : F.range = ggAutomizer X Bs := by
      ext a
      constructor
      · rintro ⟨w, rfl⟩
        exact (f' w).2
      · intro ha
        exact ⟨f'.symm ⟨a, ha⟩, by simp [F]⟩
    rw [← hFr, MonoidHom.range_eq_map,
      ← (CoxeterMatrix.E₆.reindex e).toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure]
    congr 1
    ext a
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [F, CoxeterMatrix.toCoxeterSystem_simple, hf']⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(CoxeterMatrix.E₆.reindex e).toCoxeterSystem.simple i, ⟨i, rfl⟩,
        by simp [F, CoxeterMatrix.toCoxeterSystem_simple, hf']⟩
  obtain ⟨hd4ne, hd4inj, hd4surj⟩ := d4Map_facts
  let σf : Fin 4 → {j : Λ // j ≠ e 0 ∧ j ≠ e 5} := fun k =>
    ⟨e (E6D4Refl.d4Map k), fun h0 => (hd4ne k).1 (e.injective h0),
      fun h5 => (hd4ne k).2 (e.injective h5)⟩
  have hσb : Function.Bijective σf := by
    refine ⟨fun k l hkl => hd4inj (e.injective (congrArg Subtype.val hkl)), fun j => ?_⟩
    obtain ⟨k, hk⟩ := hd4surj (e.symm j)
      (fun h0 => j.2.1 (e.symm_apply_eq.mp h0)) (fun h5 => j.2.2 (e.symm_apply_eq.mp h5))
    exact ⟨k, Subtype.ext (by simp [σf, hk])⟩
  let σ : Fin 4 ≃ {j : Λ // j ≠ e 0 ∧ j ≠ e 5} := Equiv.ofBijective σf hσb
  have hσ : ∀ k, ((σ k : {j : Λ // j ≠ e 0 ∧ j ≠ e 5}) : Λ) = e (E6D4Refl.d4Map k) := fun k => rfl
  let MJ : CoxeterMatrix {j : Λ // j ≠ e 0 ∧ j ≠ e 5} := (ggCoxeterMatrixD 4).reindex σ
  have hWMJ : GGIsWeylMatrix MJ := Or.inl ⟨4, σ, by norm_num, Or.inr (Or.inr ⟨le_rfl, rfl⟩)⟩
  have hMJ : ∀ j j' : {j : Λ // j ≠ e 0 ∧ j ≠ e 5},
      MJ.M j j' = (CoxeterMatrix.E₆.reindex e).M j j' := by
    intro j j'
    obtain ⟨k, rfl⟩ := σ.surjective j
    obtain ⟨l, rfl⟩ := σ.surjective j'
    rw [CoxeterMatrix.reindex_apply, σ.symm_apply_apply, σ.symm_apply_apply, hσ, hσ,
      CoxeterMatrix.reindex_apply, e.symm_apply_apply, e.symm_apply_apply]
    exact (coxeterE6_d4Map k l).symm
  let fJ' : MJ.Group ≃* ↥(ggAutomizer J Bs) :=
    ((ggCoxeterMatrixD 4).reindexGroupEquiv σ).trans fJ
  have hfJ' : ∀ j, (fJ' (MJ.simple j) : MulAut ↥Bs) = φ' j := by
    intro j
    obtain ⟨k, rfl⟩ := σ.surjective j
    change (fJ (((ggCoxeterMatrixD 4).reindexGroupEquiv σ)
      (((ggCoxeterMatrixD 4).reindex σ).simple (σ k))) : MulAut ↥Bs) = φ' (σ k)
    rw [CoxeterMatrix.reindexGroupEquiv_apply_simple, σ.symm_apply_apply, hfJ, hσ, hφ'J]
  have hrange : Set.range φJ =
      Set.range fun j : {j : Λ // j ≠ e 0 ∧ j ≠ e 5} => φ' j := by
    ext a
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨σ k, hφ'J k⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, rfl⟩ := σ.surjective j
      exact ⟨k, (hφ'J k).symm⟩
  have hclJ' : ggAutomizer J Bs =
      Subgroup.closure (Set.range fun j : {j : Λ // j ≠ e 0 ∧ j ≠ e 5} => φ' j) := by
    rw [hclJ, hrange]
  have hRCJ : GGReflConjSimple 3 (ggAutomizer J Bs) φJ :=
    ggReflConjSimple_of_weylMatrix (by norm_num)
      (Or.inl ⟨4, Equiv.refl _, by norm_num, Or.inr (Or.inr ⟨le_rfl,
        CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)⟩)⟩)
      (by simp) (ggIntCartan_D 4) ιJ φJ hJ αJ hpairJ hlinJ hclJ
  have hRCJ' : GGReflConjSimple 3 (ggAutomizer J Bs)
      (fun j : {j : Λ // j ≠ e 0 ∧ j ≠ e 5} => φ' j) := by
    intro s hs hr
    obtain ⟨w, hw, k, hk⟩ := hRCJ s hs hr
    exact ⟨w, hw, σ k, hk.trans (congrArg (fun a => w * a * w⁻¹) (hφ'J k).symm)⟩
  have hb : e 0 ≠ e 5 := fun h05 => absurd (e.injective h05) (by decide)
  exact ⟨Λ, iΛf, iΛd, e 0, e 5, CoxeterMatrix.E₆.reindex e, C, MJ, V, iVa, iVm, ι', φ', h, α, hb, hWM, hMC, hWMJ, hMJ,
    hlin', hrefl', hpair, ⟨f', hf'⟩, hcl', ⟨fJ', hfJ'⟩, hclJ', hRCJ'⟩

theorem ggE6D4TwoNodeLocalRest_of_twX
    (hLB : GGLBalanceInput) (hRig : GGLabelRigidInput) (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hQ1 : GGBstarInnerDiagJInput) (hTw : GGE6D4TwoNodeTwXDatum) :
    GGE6D4TwoNodeLocalRest := by
  intro G _ _ B Bs x L D J y K hH X z hXz labJ labX hJΛ hXΛ hJl hXl hrow htag
  obtain ⟨-, hE6, -, -, -, hDt, -⟩ := hT
  obtain ⟨n, rfl, hcase⟩ := E6D4J.row_cases hrow htag
  have hXD : GGResXDatumE6x 3 Bs X z := by
    rcases hcase with ⟨h, rfl⟩ | ⟨-, rfl⟩
    · refine E6D4Loc.ggResXDatumE6x_split hRig hE6 hLift hH hXz hXΛ hXl rfl ?_
      unfold ggTorM
      simpa using h
    · exact hTw G B Bs x L D J y K hH X z hXz _ _ hJΛ hXΛ hJl hXl hrow rfl
  refine ⟨fun _ => hXD, ?_⟩
  have h3 : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
    rcases hcase with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hInnJ : GGInnerDiagOn Bs J := hQ1 G 3 B Bs x L D J hH.1 hH.2.2.1.1
  obtain ⟨hN, hTor⟩ := E6D4J.torData_J hRig hDt hLift hH hInnJ hJΛ hJl h3
  obtain ⟨hm, h3m⟩ := E6D4J.odd_and_dvd_ggTorMpm (n := n) hJΛ.1 h3
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
  have hDc : Nat.card (B ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) = 3 ^ 2 := by
    rw [← hDeq]
    exact hH.1.2.2.1.2.2.1
  obtain ⟨-, hS4, -, -⟩ := E6D4J.clauses_of_torData hm h3m hH.1.2.1.2.1 hH.1.2.1.2.2.2
    hH.1.2.1.1 hH.1.2.1.2.2.1 hDc hN hTor
  have h3J : 3 ∣ Nat.card J := by
    have hd := Subgroup.card_dvd_of_le (inf_le_right : Bs ⊓ J ≤ J)
    rw [hS4] at hd
    exact (dvd_pow_self 3 (by norm_num)).trans hd
  have hJX : J ≤ X := by
    rcases hXz with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (hH.1.2.2.1.2.2.2.2.2.1).1.trans inf_le_left
    · exact le_of_ggNbr hLB hH.1.1 hH.1.2.2 h3J hH.2.2.2.2.1
  obtain ⟨VJ, iVJa, iVJm, ιJ, φJ, hJv, αJ, hlinJ, hreflJ, hpairJ, ⟨fJ, hfJ⟩, hclJ⟩ :=
    xDatumFin_of_torData (by norm_num) hm h3m (ggIntCartan_D 4) hH.1.2.1.2.1 hH.1.2.1.2.2.2 hN hTor
  letI := iVJa; letI := iVJm
  exact sideDatum_of_d4 hXD (ggAutomizer_mono Bs hJX) ιJ φJ hJv αJ hlinJ hreflJ hpairJ fJ hfJ hclJ

end E6D4Side

end CFSG.StandardType

end
