module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6DepAllDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6Consumer
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6Frame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeA5DepExclusion
public import CFSG.LocalAnalysis.StandardType.GGTWSmallLE3E6Datum
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeNineConsumer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwoNodeE6DepL_core (hDep : LR6E6DepAll) (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    (hFixK : GGTBFixNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) (hcard : Nat.card ↥Bs = 3 ^ 6)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (e : Fin 6 ≃ Λ) (hML : ML = CoxeterMatrix.E₆.reindex e) (hCL : GGIntCartan ML CL)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hdep : ¬ LinearIndependent (ZMod p) h) (hKd : GGResXDatumA p Bs K 5) : False := by
  classical
  subst hp3
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  let xv : V := ι (Additive.ofMul ⟨x, hx⟩)
  have hcardV : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) V := (FiniteField.pow_finrank_eq_natCard 3 V).symm
  have hV6 : Module.finrank (ZMod 3) V = 6 := by
    have hpow : 3 ^ Module.finrank (ZMod 3) V = 3 ^ 6 := by rw [← hcardV, hcard]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  have F : GGDepE6Frame (fun i : Fin 6 => h (e i)) (fun i => α (e i)) xv :=
    ggXDatumE6_dep_frame hFix (by norm_num) hH hx e hML hCL hφ hpair hAL hdep
  let r : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
  have hr : ∀ (i : Fin 6) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  obtain ⟨AA, hAA⟩ : ∃ AA : Subgroup (MulAut ↥Bs), AA = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ⟨_, rfl⟩
  rw [← hAA] at hA
  have hφAA : ∀ i, φ i ∈ AA := fun i =>
    hAA ▸ Subgroup.mem_sup_left (by rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hrR : ∀ i : Fin 6, r i ∈ AA.map (ggLin (p := 3) ι) := fun i =>
    Subgroup.mem_map.mpr ⟨φ (e i), hφAA (e i), rfl⟩
  have hnt : ∀ g ∈ AA.map (ggLin (p := 3) ι),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg hcond
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hmem := hA hψA
      rw [ggAutomizer_eq] at hmem
      exact hmem
    exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond)
  have hyD : y ∈ D := by
    rw [hH.2.2.2.2.1.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy : y ∈ Bs := hH.1.2.1.1 (hH.1.2.2.1.1 hyD)
  have hstabK := hOrbK G 3 B Bs x L D J y K hH hy
  rw [← hAA] at hstabK
  have hcardAK : Nat.card ↥(ggAutomizer K Bs) = Nat.factorial 6 := by
    simpa using hKd.card_automizer
  have hcardR : Nat.card ↥(AA.map (ggLin (p := 3) ι)) ≤
      3 ^ 6 * (6 * (3 - 1) * Nat.factorial 6) := by
    calc Nat.card ↥(AA.map (ggLin (p := 3) ι)) = Nat.card ↥AA :=
          (Nat.card_congr (Subgroup.equivMapOfInjective AA (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)) :=
          ggIndep_card_join_le AA ⟨y, hy⟩ hstabK
      _ ≤ 3 ^ 6 * ((3 - 1) * 6 * Nat.factorial 6) :=
          Nat.mul_le_mul hcard.le (Nat.mul_le_mul_left _ hcardAK.le)
      _ = 3 ^ 6 * (6 * (3 - 1) * Nat.factorial 6) := by rw [Nat.mul_comm (3 - 1) 6]
  have hline := hDep 3 rfl V hV6 (fun i => h (e i)) (fun i => α (e i)) xv r F hr
    (AA.map (ggLin (p := 3) ι)) hrR hnt hcardR
  obtain ⟨Λ', i1', i2', M', C', V', i3', i4', ι', φ', h', α', e', hM', hW', hC', hlin', hrefl',
    hpair', ⟨f', hf'⟩, hcl'⟩ := hKd
  letI := i1'; letI := i2'
  haveI : Nontrivial Λ' := ⟨e' 0, e' 1, fun hh => by
    have h01 : (0 : Fin 5) = 1 := e'.injective hh
    exact (by decide : (0 : Fin 5) ≠ 1) h01⟩
  have hKA : ggAutomizer K Bs ≤ AA := hAA ▸ le_sup_right
  obtain ⟨t', ht'K, _, ht'move⟩ := ggIndep_moving_K hFixK hH hx
  exact ggWeyl_rootLine_false hp2 ι hKA hW' hrefl' f' hf' hcl' ⟨t', ht'K, ht'move⟩ hnt hline

theorem ggTwoNodeE6L_LE3
    (hAll : LR6E6All) (hDep : LR6E6DepAll) (hOrb : GGResCentBoundInput)
    (hOrbK : GGResCentBoundNbrInput) (hRig : GGLabelRigidInput) (hT : GGTBTorAFrom 4)
    (hLift : GGTBTorLiftAFrom 4) (hR : GGTBXDatumResInput) (hTw : GGTWTwA5Open)
    (hJ2S : GGTBJTwoNodeSmallInput) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt (fun q labJ labK => ggRowTwoNodeSmallJA q labJ labK ∧ labK.rank = 5) p J K)
    (hL3 : GGResLeviSideDatumLE3 p Bs L J) (hL2 : ¬ GGResTwoNodeSideDatum p Bs L J)
    (hp3 : p = 3) (hcard : Nat.card ↥Bs = 3 ^ 6) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨hE6, hKd⟩ := ggLE3Small_E6_L hRig hT hLift hR hTw hJ2S hH hrow hL3 hL2 hp3 hcard
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hM, hW, hC, hlin, hrefl, hpair,
    ⟨f, hf⟩, hclos⟩ := hE6
  letI := i1; letI := i2; letI := i3; letI := i4
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  by_cases hind : LinearIndependent (ZMod p) h
  · exact ggTwoNodeIndepAtL_e6 hAll hOrb hFix hFixK hp3 hH hx (by rw [hcard]; norm_num) e hM hC
      hlin hrefl hpair f hclos hind
  · exact (ggTwoNodeE6DepL_core hDep hOrbK hFix hFixK hp3 hH hx hcard e hM hC hlin hpair hclos
      hind hKd).elim

end CFSG.StandardType

end
