module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeE6FrameK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e6K_card_coxeterE6 :
    Nat.card (CoxeterMatrix.E₆).Group = 51840 := by
  have hc : CFSG.Blueprint.Chevalley.Tag.cartan .E6 = CartanMatrix.E 6 :=
    CFSG.LieType.Chevalley.cartanE_eq 6
  have hmat : CoxeterMatrix.E₆ = CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6) := by
    have h := coxeterMatrix_eq_of_ggIntCartan
      (C := CFSG.Blueprint.Chevalley.Tag.cartan .E6)
      (M := CoxeterMatrix.E₆)
      (CFSG.LieType.Chevalley.isFiniteType_cartan .E6)
      (hc.symm ▸ ggIntCartan_E₆)
    exact h.symm
  have hgroup : CFSG.LieType.Chevalley.WeylGroup .E6 = (CoxeterMatrix.E₆).Group :=
    congrArg CoxeterMatrix.Group hmat.symm
  have hcardW : Nat.card (CFSG.LieType.Chevalley.WeylGroup .E6) =
      Nat.card (CoxeterMatrix.E₆).Group :=
    Nat.card_congr (Equiv.cast hgroup)
  rw [← hcardW]
  exact NoOffExc.card_weyl_E6

theorem ggE6K_card_AK {G : Type}
    [Group G] {Bs K : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ}
    (e : Fin 6 ≃ Λ) (hMK : MK = CoxeterMatrix.E₆.reindex e)
    (hfK : MK.Group ≃* ↥(ggAutomizer K Bs)) : Nat.card ↥(ggAutomizer K Bs) = 51840 := by
  subst hMK
  calc Nat.card ↥(ggAutomizer K Bs) = Nat.card (CoxeterMatrix.E₆.reindex e).Group :=
        (Nat.card_congr hfK.toEquiv).symm
    _ = Nat.card (CoxeterMatrix.E₆).Group :=
        Nat.card_congr ((CoxeterMatrix.E₆).reindexGroupEquiv e).toEquiv
    _ = 51840 := e6K_card_coxeterE6

theorem ggE6K_card_join_le (hOrbK : GGResCentBoundNbrInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp3 : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hBs : Nat.card ↥Bs ≤ 3 ^ 7) (hAK : Nat.card ↥(ggAutomizer K Bs) = 51840) :
    Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ 3 ^ 7 * (6 * (3 - 1) * 51840) := by
  have hstab := hOrbK G p B Bs x L D J y K hH hy
  have hjoin := ggIndep_card_join_le (ggAutomizer L Bs ⊔ ggAutomizer K Bs) ⟨y, hy⟩ hstab
  subst hp3
  calc Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)
      ≤ Nat.card ↥Bs * ((3 - 1) * 6 * Nat.card ↥(ggAutomizer K Bs)) := hjoin
    _ ≤ 3 ^ 7 * ((3 - 1) * 6 * 51840) := by
        rw [hAK]
        exact Nat.mul_le_mul_right _ hBs
    _ = 3 ^ 7 * (6 * (3 - 1) * 51840) := by ring

private theorem e6K_mem_zpowers {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {x b : G}
    (hxp : x ^ p = 1) (hb : b ∈ Subgroup.zpowers x) (hb1 : b ≠ 1) : x ∈ Subgroup.zpowers b := by
  have hp : p.Prime := Fact.out
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hb1
    simpa using hb
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hbdvd : orderOf b ∣ p := by
    rw [← hxord]
    exact orderOf_dvd_of_mem_zpowers hb
  have hbord : orderOf b = p := by
    rcases (Nat.dvd_prime hp).mp hbdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hb
  have heq : Subgroup.zpowers b = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hbord, hxord])
  rw [heq]
  exact Subgroup.mem_zpowers x

theorem ggE6K_moving_L_of_moving_K (hFix : GGTBFixInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    (hmoveK : ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧ t ⟨x, hx⟩ ≠ ⟨x, hx⟩)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs)) {b : ↥Bs} (hb1 : b ≠ 1)
    (hbK : ∀ ψ ∈ ggAutomizer K Bs, ψ b = b) :
    ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧ t b ≠ b := by
  by_contra hcon
  push Not at hcon
  have hLfix : ∀ ψ ∈ ggAutomizer L Bs, ψ b = b := by
    intro ψ hψ
    have hA' : ggAutomizer L Bs =
        Subgroup.closure {φ | φ ∈ ggAutomizer L Bs ∧ GGIsReflection p φ} := hLrefl
    have hle : Subgroup.closure {φ | φ ∈ ggAutomizer L Bs ∧ GGIsReflection p φ} ≤
        MulAction.stabilizer (MulAut ↥Bs) b := by
      rw [Subgroup.closure_le]
      intro φ hφ
      exact hcon φ hφ.1 hφ.2
    have hψ' : ψ ∈ Subgroup.closure {φ | φ ∈ ggAutomizer L Bs ∧ GGIsReflection p φ} := by
      rw [← hA']
      exact hψ
    exact hle hψ'
  have hbx : (b : G) ∈ Subgroup.zpowers x :=
    hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1 hH.2.2.2.2.2.1
      hH.2.2.2.2.2.2 b hLfix
  have hpre := hH.1.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hxp : x ^ p = 1 := hpre.2.1.2 x hxD
  have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hxb : x ∈ Subgroup.zpowers (b : G) := e6K_mem_zpowers hxp hbx hb1'
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxb
  have hxbm : (⟨x, hx⟩ : ↥Bs) = b ^ m := Subtype.ext (by simpa using hm.symm)
  have hKx : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    intro ψ hψ
    rw [hxbm, map_zpow, hbK ψ hψ]
  obtain ⟨t, htK, -, htm⟩ := hmoveK
  exact htm (hKx t htK)

theorem ggTwoNodeIndepAtK_e6_of_moving_K (hAll : LR6E6All) (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hmoveK : ∃ t ∈ ggAutomizer K Bs, GGIsReflection p t ∧
      t ⟨x, hH.1.tableB_facts.2.2.1⟩ ≠ ⟨x, hH.1.tableB_facts.2.2.1⟩)
    (hBs : Nat.card ↥Bs ≤ 3 ^ 7)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs))
    (hbound : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ 3 ^ 7 * (6 * (3 - 1) * 51840))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin 6 ≃ Λ) (hMK : MK = CoxeterMatrix.E₆.reindex e) (hCK : GGIntCartan MK CK)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have F := ggXDatumE6_indep_frame_K hp3 e hMK hCK hpair hind
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  generalize h (e 0) - h (e 2) + h (e 4) - h (e 5) = zv at F
  obtain ⟨b, hbbw⟩ : ∃ b : ↥Bs, ι (Additive.ofMul b) = zv :=
    ⟨Additive.toMul (ι.symm zv), by rw [ofMul_toMul, AddEquiv.apply_symm_apply]⟩
  have hb1 : b ≠ 1 := by
    intro h1
    apply F.x_ne
    rw [← hbbw, h1]
    simp
  have hbφ : ∀ j : Λ, φ j b = b := by
    intro j
    refine (ggLin_fix_iff (p := p) ι (φ j) b).mpr ?_
    rw [hbbw]
    have h1 := hφ j zv
    have hj : α j zv = 0 := by
      have := F.x_ker (e.symm j)
      simpa using this
    rw [hj, zero_smul, sub_zero] at h1
    exact h1
  have hbK : ∀ ψ ∈ ggAutomizer K Bs, ψ b = b := by
    rw [hAK]
    exact ggFixed_of_mem_closure φ b hbφ
  have hmove := ggE6K_moving_L_of_moving_K hFix hH hx hmoveK hLrefl hb1 hbK
  subst hp3
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hA : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top)
  have hcardV : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) V :=
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := Nat.card_congr Additive.ofMul
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) V := (FiniteField.pow_finrank_eq_natCard 3 V).symm
  have hdim : Module.finrank (ZMod 3) V ≤ 7 := by
    rw [hcardV] at hBs
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hBs
  let r : Fin 6 → (V ≃ₗ[ZMod 3] V) := fun i => ggLin (p := 3) ι (φ (e i))
  have hr : ∀ (i : Fin 6) (v : V), r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
  have hφsup : ∀ i, φ i ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := fun i =>
    Subgroup.mem_sup_right (by rw [hAK]; exact Subgroup.subset_closure ⟨i, rfl⟩)
  have hgen' : GGReflGenerated 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    ggIndep_reflGenerated_sup hLrefl hH.2.2.2.2.2.1
  obtain ⟨A', hA'⟩ : ∃ A' : Subgroup (MulAut ↥Bs), A' = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ⟨_, rfl⟩
  rw [← hA'] at hgen' hA hφsup hbound
  have hrA : ∀ i : Fin 6, r i ∈ A'.map (ggLin (p := 3) ι) := fun i =>
    Subgroup.mem_map.mpr ⟨φ (e i), hφsup (e i), rfl⟩
  have hgenA : A'.map (ggLin (p := 3) ι) =
      Subgroup.closure {s | s ∈ A'.map (ggLin (p := 3) ι) ∧ GGLinRefl s} := by
    apply le_antisymm
    · calc A'.map (ggLin (p := 3) ι)
          = (Subgroup.closure {ψ | ψ ∈ A' ∧ GGIsReflection 3 ψ}).map (ggLin (p := 3) ι) := by
            rw [← hgen']
        _ = Subgroup.closure ((ggLin (p := 3) ι) '' {ψ | ψ ∈ A' ∧ GGIsReflection 3 ψ}) :=
            MonoidHom.map_closure _ _
        _ ≤ Subgroup.closure {s | s ∈ A'.map (ggLin (p := 3) ι) ∧ GGLinRefl s} := by
            apply Subgroup.closure_mono
            rintro _ ⟨ψ, ⟨hψA, hψr⟩, rfl⟩
            exact ⟨Subgroup.mem_map.mpr ⟨ψ, hψA, rfl⟩,
              (ggRC_isReflection_iff_linRefl (p := 3) ι ψ).mp hψr⟩
    · rw [Subgroup.closure_le]
      intro s hs
      exact hs.1
  have hnt : ∀ g ∈ A'.map (ggLin (p := 3) ι),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg hcond
    obtain ⟨ψ, hψA, rfl⟩ := Subgroup.mem_map.mp hg
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      have hmem := hA hψA
      rw [ggAutomizer_eq] at hmem
      exact hmem
    exact hH.2.2.2.1 ψ hψind (ggRC_isTransvection_of_lin ι ψ hcond)
  have hcardA : Nat.card ↥(A'.map (ggLin (p := 3) ι)) ≤ 3 ^ 7 * (6 * (3 - 1) * 51840) := by
    calc Nat.card ↥(A'.map (ggLin (p := 3) ι)) = Nat.card ↥A' :=
          (Nat.card_congr (Subgroup.equivMapOfInjective A' (ggLin (p := 3) ι)
            (ggLin_injective ι)).toEquiv).symm
      _ ≤ 3 ^ 7 * (6 * (3 - 1) * 51840) := hbound
  obtain ⟨t, htL, htrefl, htmove⟩ := hmove
  have hmoveA : ∃ s ∈ A'.map (ggLin (p := 3) ι), GGLinRefl s ∧ s zv ≠ zv := by
    refine ⟨ggLin (p := 3) ι t, Subgroup.mem_map.mpr ⟨t, ?_, rfl⟩,
      (ggRC_isReflection_iff_linRefl (p := 3) ι t).mp htrefl, ?_⟩
    · rw [hA']
      exact Subgroup.mem_sup_left htL
    · intro hfix
      apply htmove
      refine (ggLin_fix_iff (p := 3) ι t b).mpr ?_
      rw [hbbw]
      exact hfix
  have hlin := hAll 3 rfl V hdim (fun i => h (e i)) (fun i => α (e i)) zv r F hr
    (A'.map (ggLin (p := 3) ι)) hrA hgenA hnt hcardA hmoveA
  rw [← hA']
  exact ggRC_weylReflGroup_of_linWeyl ι A' hlin

theorem ggTwoNodeIndepAtK_e6 (hAll : LR6E6All) (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hBs : Nat.card ↥Bs ≤ 3 ^ 7)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs))
    (hbound : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤ 3 ^ 7 * (6 * (3 - 1) * 51840))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin 6 ≃ Λ) (hMK : MK = CoxeterMatrix.E₆.reindex e) (hCK : GGIntCartan MK CK)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  exact ggTwoNodeIndepAtK_e6_of_moving_K hAll hFix hp3 hH
    (ggIndep_moving_K hFixK hH hH.1.tableB_facts.2.2.1) hBs hLrefl hbound
    e hMK hCK hφ hpair hAK hind

end CFSG.StandardType

end
