module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEndFacts
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5
public import CFSG.LocalAnalysis.StandardType.GGSpJoinReflPairing
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGP3LineNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import CFSG.Monster.B.TwoA.Base.SymFiveAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

private theorem e6QTwoU5_weyl_A4
    (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows)
    (hcfg : GGConfig 3 B Bs x L D J) (hBs : IsElemAbelian 3 Bs)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 4 ∧ lab.n = 1) 3 Bs L) :
    GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : ∀ (_r _m N : ℕ), Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop :=
    fun _ _ N _ M => ∃ e : Fin 4 ≃ Fin N, M = (CoxeterMatrix.A 4).reindex e
  have hL' : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ)
      (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
        GGTBTorRowAt p lab r m N C M ∧ P r m N C M) 3 Bs L := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hL
    obtain ⟨⟨htwA, hrank, hn⟩, hnorm, hinds⟩ := hP
    obtain ⟨t, r, n⟩ := lab
    simp only at htwA hrank hn
    subst htwA
    subst hrank
    subst hn
    exact ⟨⟨4 - ggTorEnn 3 ⟨.twA, 4, 1⟩, ggTorM ⟨.twA, 4, 1⟩, 4,
      CartanMatrix.A 4, CoxeterMatrix.A 4,
      GGTBTorRowAt.aInd (p := 3) (lab := ⟨.twA, 4, 1⟩) (Or.inr rfl) (by decide) (by decide),
      ⟨Equiv.refl (Fin 4), rfl⟩⟩, hnorm, hinds⟩
  obtain ⟨lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hP, hBsI, hlift, hT, -⟩ :=
    l05nPlQ_marking_with hW hLift (by norm_num : 3 ≠ 2) P hL'
  obtain ⟨e, he⟩ := hP
  obtain ⟨hom, hpm, -, hMC⟩ := l05nPlP1_row_facts Nat.prime_three (by norm_num) hlab hrow
  have hTor := hT ↥L (ggQuotHom θ) (ggGamma L hN).range
    (ggTorusTBGroup_of_L hcfg hperf θ hN hBsI hlift)
  have hWeyl : GGWeylOfType 3 M (ggAutomizer L Bs) :=
    NSJoin.weylOfType_of_torData (p := 3) (m := m) (N := N) (C := C) (M := M)
      (by norm_num) hom hpm hMC hBs hstar hN hTor
  have hWeyl' : GGWeylOfType 3 ((CoxeterMatrix.A 4).reindex e) (ggAutomizer L Bs) := by
    rwa [he] at hWeyl
  exact GGWeylOfType.of_reindex (M := CoxeterMatrix.A 4) (e := e) hWeyl'

private theorem e6QTwoU5_card_Bs
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J) (hTBF : GGTBFixInput)
    (hA4 : GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs))
    (horderx : orderOf x = 3) :
    Nat.card Bs = 3 ^ 5 := by
  have hle := card_le_pow_mul_card_of_weylOfType hA4 ((Subgroup.zpowers x).subgroupOf Bs)
    (fun b hb => Subgroup.mem_subgroupOf.mpr (GGSecFiveE6QTwoCfg.fix hTBF hC b hb))
  have hF : Nat.card ((Subgroup.zpowers x).subgroupOf Bs) ≤ 3 := by
    rw [← horderx, ← Nat.card_zpowers]
    exact Nat.card_le_card_of_injective
      (fun b => (⟨((b : ↥Bs) : G), Subgroup.mem_subgroupOf.mp b.2⟩ : Subgroup.zpowers x))
      (fun a b h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext h'))
  have hge : 3 ^ 5 ≤ Nat.card Bs := GGSecFiveE6QTwoCfg.three_pow_five_le_card hC
  rw [Fintype.card_fin] at hle
  have hmul : (3 : ℕ) ^ 4 * Nat.card ((Subgroup.zpowers x).subgroupOf Bs) ≤ 3 ^ 5 := by
    rw [show (3 : ℕ) ^ 5 = 3 ^ 4 * 3 by norm_num]
    exact Nat.mul_le_mul_left _ hF
  exact le_antisymm (hle.trans hmul) hge

private theorem e6QTwoU5_cartan_A4 [Fact (Nat.Prime 3)]
    (hNT : GGNoTransvection 3 Bs)
    (hA4 : GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs))
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) :
    ∃ (e : (CoxeterMatrix.A 4).Group ≃* ↥(ggAutomizer L Bs)) (h : Fin 4 → V)
      (α : Fin 4 → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2),
      (∀ i, ggLin (p := 3) ι ((e ((CoxeterMatrix.A 4).simple i) : ↥(ggAutomizer L Bs)) :
          MulAut ↥Bs) = Module.reflection (hα i)) ∧
      ∀ i j, α i (h j) = (CartanMatrix.A 4 i j : ZMod 3) := by
  classical
  have hsl : ∀ i j : Fin 4, i ≠ j →
      CartanMatrix.A 4 i j = 0 ∨ CartanMatrix.A 4 i j = -1 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  let par : Fin 4 → Fin 4 := ![0, 0, 1, 2]
  let depth : Fin 4 → ℕ := ![0, 1, 2, 3]
  have hpar : ∀ i j : Fin 4, i ≠ j →
      (CartanMatrix.A 4 i j = -1 ↔
        ((i ≠ 0 ∧ par i = j) ∨ (j ≠ 0 ∧ par j = i))) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hdepth : ∀ i : Fin 4, i ≠ 0 → depth (par i) < depth i := by decide
  exact SpJoinRefl.exists_cartan_pairing_of_weylOfType
    (p := 3) (M := CoxeterMatrix.A 4) (C := CartanMatrix.A 4)
    (by norm_num) hNT (ggIntCartan_A 4) hsl par 0 depth hpar hdepth hA4
    (fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer hφ) ι

private theorem e6QTwoU5_exists_e6W
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hNT : GGNoTransvection 3 Bs) (hxB : x ∈ Bs) (hx1 : x ≠ 1)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (hVcard : Nat.card V = 3 ^ 5) (ι : Additive ↥Bs ≃+ V) :
    ∃ (A₀ : Subgroup (MulAut ↥Bs)) (W : Subgroup (V ≃ₗ[ZMod 3] V)),
      A₀ ≤ ggAutomizer ⊤ Bs ∧ A₀.map (ggLin (p := 3) ι) = W ∧
      576 ≤ Nat.card (MulAction.stabilizer W (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  obtain ⟨A₀, -, hA₀le, hWeylA₀, hcardA₀, -⟩ := GGSecFiveE6QTwoCfg.exists_join hC
  have hA₀ind : ∀ ψ ∈ A₀, ψ ∈ ggInduced ⊤ Bs :=
    fun ψ hψ => mem_ggInduced_top_of_mem_ggAutomizer (hA₀le hψ)
  obtain ⟨e6, h6, α6, hα6, hrefl6, hP6⟩ :=
    E6QTwo.exists_cartan_pairing_E6 hNT hWeylA₀ hA₀ind ι
  obtain ⟨B6, hB6⟩ := E6QTwo.exists_bilinForm hP6 hVcard
  have hmapA : A₀.map (ggLin (p := 3) ι) = E6QTwo.e6Weyl hα6 :=
    E6QTwo.map_ggLin_eq_e6Weyl ι e6 hα6 hrefl6
  have hE6card : Nat.card (E6QTwo.e6Weyl hα6) = 51840 := by
    rw [E6QTwo.card_e6Weyl_eq ι e6 hα6 hrefl6]
    exact hcardA₀
  let vx : V := ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))
  have hvx : vx ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, hxB⟩ : ↥Bs) = 0 := ι.injective (by simpa [vx] using h0)
    have h2 : (⟨x, hxB⟩ : ↥Bs) = 1 := by
      simpa using congrArg Additive.toMul h1
    exact hx1 (by simpa using congrArg Subtype.val h2)
  have hcases := E6QTwo.stabilizer_cases hP6 hVcard hB6 hα6 hE6card hvx
  have hstabc : 576 ≤ Nat.card (MulAction.stabilizer (E6QTwo.e6Weyl hα6) vx) := by
    rcases hcases with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨-, h1⟩
    · omega
    · omega
    · omega
  exact ⟨A₀, E6QTwo.e6Weyl hα6, hA₀le, hmapA, by simpa [vx] using hstabc⟩

omit [Finite G] in
private theorem e6QTwoU5_map_A1 [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (A₀ : Subgroup (MulAut ↥Bs)) (W : Subgroup (V ≃ₗ[ZMod 3] V))
    (hmapA : A₀.map (ggLin (p := 3) ι) = W) (hxB : x ∈ Bs) :
    (A₀ ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxB⟩ : ↥Bs)).map (ggLin (p := 3) ι) =
      (MulAction.stabilizer W (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)))).map W.subtype := by
  classical
  set A₁ : Subgroup (MulAut ↥Bs) :=
    A₀ ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxB⟩ : ↥Bs) with hA₁
  set W₁ : Subgroup ↥W :=
    MulAction.stabilizer W (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) with hW₁
  change A₁.map (ggLin (p := 3) ι) = W₁.map W.subtype
  have hle : A₁.map (ggLin (p := 3) ι) ≤ W₁.map W.subtype := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have hψA : ψ ∈ A₀ := (Subgroup.mem_inf.mp hψ).1
    have hψfix : ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ := (Subgroup.mem_inf.mp hψ).2
    have hmem : ggLin (p := 3) ι ψ ∈ W := by
      rw [← hmapA]
      exact Subgroup.mem_map_of_mem _ hψA
    have hstab : (⟨ggLin (p := 3) ι ψ, hmem⟩ : ↥W) ∈
        MulAction.stabilizer W (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) :=
      MulAction.mem_stabilizer_iff.mpr ((ggLin_fix_iff ι ψ ⟨x, hxB⟩).mp hψfix)
    exact Subgroup.mem_map_of_mem W.subtype hstab
  have hge : W₁.map W.subtype ≤ A₁.map (ggLin (p := 3) ι) := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hφmem : (φ.1 : V ≃ₗ[ZMod 3] V) ∈ A₀.map (ggLin (p := 3) ι) := by
      rw [hmapA]
      exact φ.2
    obtain ⟨ψ, hψ, hψeq⟩ := Subgroup.mem_map.mp hφmem
    have hφfix : (φ.1 : V ≃ₗ[ZMod 3] V) (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) =
        ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) := by
      change (φ : V ≃ₗ[ZMod 3] V) • ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) =
        ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))
      exact hφ
    have hψfix : ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ := by
      apply (ggLin_fix_iff (p := 3) ι ψ ⟨x, hxB⟩).mpr
      rw [hψeq]
      simpa using hφfix
    have hmemA₁ : ggLin (p := 3) ι ψ ∈ A₁.map (ggLin (p := 3) ι) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mpr
        ⟨hψ, MulAction.mem_stabilizer_iff.mpr hψfix⟩)
    rwa [hψeq] at hmemA₁
  exact le_antisymm hle hge

private theorem e6QTwoU5_stab_lower [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (A₀ : Subgroup (MulAut ↥Bs)) (W : Subgroup (V ≃ₗ[ZMod 3] V))
    (hxB : x ∈ Bs)
    (hA₀le : A₀ ≤ ggAutomizer ⊤ Bs)
    (hmapA₁ : (A₀ ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxB⟩ : ↥Bs)).map
        (ggLin (p := 3) ι) =
      (MulAction.stabilizer W (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)))).map W.subtype)
    (hstab : 576 ≤ Nat.card (MulAction.stabilizer W (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))))) :
    576 ≤ Nat.card ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxB⟩ : ↥Bs)) := by
  classical
  set A₁ : Subgroup (MulAut ↥Bs) :=
    A₀ ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxB⟩ : ↥Bs) with hA₁
  set W₁ : Subgroup ↥W :=
    MulAction.stabilizer W (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) with hW₁
  have hmapA₁' : A₁.map (ggLin (p := 3) ι) = W₁.map W.subtype := by
    rw [hA₁, hW₁]
    exact hmapA₁
  have hcard : Nat.card A₁ = Nat.card W₁ := by
    calc Nat.card A₁ = Nat.card (A₁.map (ggLin (p := 3) ι)) :=
          (Subgroup.card_map_of_injective (ggLin_injective ι)).symm
      _ = Nat.card (W₁.map W.subtype) := by rw [hmapA₁']
      _ = Nat.card W₁ := Subgroup.card_map_of_injective W.subtype_injective
  have hle : A₁ ≤ ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxB⟩ : ↥Bs) :=
    le_inf (inf_le_left.trans hA₀le) inf_le_right
  have hstab' : 576 ≤ Nat.card W₁ := by simpa [hW₁] using hstab
  rw [← hcard] at hstab'
  exact hstab'.trans (Subgroup.card_le_of_le hle)

private theorem e6QTwoU5_aut_card
    (hA4 : GGWeylOfType 3 (CoxeterMatrix.A 4) (ggAutomizer L Bs)) :
    Nat.card (MulAut ↥(ggAutomizer L Bs)) ≤ 120 := by
  obtain ⟨E, -⟩ := exists_permEquiv_of_ggWeylOfType_A (m := 4) hA4
  have : Finite (MulAut ↥(ggAutomizer L Bs)) :=
    Finite.of_injective (fun φ : MulAut ↥(ggAutomizer L Bs) =>
      (φ : ↥(ggAutomizer L Bs) → ↥(ggAutomizer L Bs))) DFunLike.coe_injective
  rw [← Nat.card_congr (MulAut.congr E).toEquiv]
  calc Nat.card (MulAut (Equiv.Perm (Fin 5))) ≤ Nat.card (Equiv.Perm (Fin 5)) :=
        Nat.card_le_card_of_surjective _ CFSG.Monster.B.TwoA.sym5_conj_surjective
    _ = 120 := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl

private theorem e6QTwoU5_stab_normalizer
    (ha₀ : GGLNoncyclicInput) (hcfg : GGConfig 3 B Bs x L D J) (hxB : x ∈ Bs)
    (St : Subgroup (MulAut ↥Bs))
    (hStmem : ∀ φ : MulAut ↥Bs, φ ∈ St ↔
      φ ∈ ggAutomizer ⊤ Bs ∧ φ ⟨x, hxB⟩ = ⟨x, hxB⟩) :
    St ≤ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) := by
  intro φ hφ
  exact ggAutomizer_fixes_mem_normalizer ha₀ hcfg hxB ((hStmem φ).mp hφ).1 ((hStmem φ).mp hφ).2

omit [Finite G] in
private theorem e6QTwoU5_ker_centralizes
    (St : Subgroup (MulAut ↥Bs))
    (hStN : St ≤ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs))) :
    ∀ φ : ↥St, φ ∈ ((ggAutomizer L Bs).normalizerMonoidHom.comp
        (Subgroup.inclusion hStN)).ker →
      ∀ a ∈ ggAutomizer L Bs, a * (φ : MulAut ↥Bs) = (φ : MulAut ↥Bs) * a := by
  intro φ hφ a ha
  have h1 : Subgroup.inclusion hStN φ ∈ (ggAutomizer L Bs).normalizerMonoidHom.ker :=
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hφ)
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h1
  exact Subgroup.mem_centralizer_iff.mp h1 a ha

omit [Finite G] in
private theorem e6QTwoU5_vx_ne_zero {V : Type} [AddCommGroup V]
    (ι : Additive ↥Bs ≃+ V) (hxB : x ∈ Bs) (hx1 : x ≠ 1) :
    ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) ≠ 0 := by
  intro h0
  have h1 : Additive.ofMul (⟨x, hxB⟩ : ↥Bs) = 0 := ι.injective (by simpa using h0)
  have h2 : (⟨x, hxB⟩ : ↥Bs) = 1 := by simpa using congrArg Additive.toMul h1
  exact hx1 (by simpa using congrArg Subtype.val h2)

omit [Finite G] in
private theorem e6QTwoU5_alpha_vx [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (e4 : (CoxeterMatrix.A 4).Group ≃* ↥(ggAutomizer L Bs))
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V)
    (hα4 : ∀ i, α4 i (h4 i) = 2)
    (hrefl4 : ∀ i, ggLin (p := 3) ι ((e4 ((CoxeterMatrix.A 4).simple i) :
      ↥(ggAutomizer L Bs)) : MulAut ↥Bs) = Module.reflection (hα4 i))
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) (hxB : x ∈ Bs) :
    ∀ i : Fin 4, α4 i (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) = 0 := by
  intro i
  let φ : MulAut ↥Bs := ((e4 ((CoxeterMatrix.A 4).simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hφA : φ ∈ ggAutomizer L Bs := (e4 ((CoxeterMatrix.A 4).simple i)).2
  have hfix : φ ⟨x, hxB⟩ = ⟨x, hxB⟩ := ggAutomizer_apply_eq_of_le_centralizer hLx hφA
  have hfixv : ggLin (p := 3) ι φ (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))) =
      ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)) :=
    (ggLin_fix_iff ι φ ⟨x, hxB⟩).mp hfix
  have hr : ggLin (p := 3) ι φ = (Module.reflection (hα4 i) : V ≃ₗ[ZMod 3] V) := hrefl4 i
  rw [hr, Module.reflection_apply] at hfixv
  have hzero : (α4 i (ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs)))) • h4 i = 0 := sub_eq_self.mp hfixv
  have hhi : h4 i ≠ 0 := (ne_zero_of_apply_eq_two (p := 3) (by norm_num) (hα4 i)).1
  exact (smul_eq_zero.mp hzero).resolve_right hhi

private theorem e6QTwoU5_eigen
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V) (hα4 : ∀ i, α4 i (h4 i) = 2)
    (r : Fin 4 → V ≃ₗ[ZMod 3] V) (hr : ∀ i, r i = Module.reflection (hα4 i))
    {C : V →ₗ[ZMod 3] V} (i : Fin 4) (hC : ∀ w, C (r i w) = r i (C w)) :
    C (h4 i) = (2 * α4 i (C (h4 i))) • h4 i := by
  have hrh : r i (h4 i) = -h4 i := by
    rw [hr i, Module.reflection_apply_self]
  have h1 : C (-h4 i) = r i (C (h4 i)) := by rw [← hrh, hC]
  rw [map_neg, hr i, Module.reflection_apply] at h1
  have h2 : (2 : ZMod 3) • C (h4 i) = (α4 i (C (h4 i))) • h4 i := by
    rw [eq_sub_iff_add_eq, neg_add_eq_iff_eq_add] at h1
    rw [two_smul, h1]
  have h22 : (2 * 2 : ZMod 3) = 1 := rfl
  have h := congrArg (fun x => (2 : ZMod 3) • x) h2
  simp only [smul_smul] at h
  rw [h22] at h
  rw [one_smul] at h
  exact h

private theorem e6QTwoU5_edge
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V) (hα4 : ∀ i, α4 i (h4 i) = 2)
    (r : Fin 4 → V ≃ₗ[ZMod 3] V) (hr : ∀ i, r i = Module.reflection (hα4 i))
    {C : V →ₗ[ZMod 3] V} (i j : Fin 4) (hij : α4 i (h4 j) ≠ 0)
    (hC : ∀ w, C (r i w) = r i (C w)) {a b : ZMod 3}
    (ha : C (h4 i) = a • h4 i) (hb : C (h4 j) = b • h4 j) : a = b := by
  have hi : h4 i ≠ 0 := (ne_zero_of_apply_eq_two (p := 3) (by norm_num) (hα4 i)).1
  have h1 : C (r i (h4 j)) = r i (C (h4 j)) := hC _
  rw [hr i] at h1
  simp only [Module.reflection_apply, map_sub, map_smul, hb, ha] at h1
  have h2 : (a * α4 i (h4 j)) • h4 i = (b * α4 i (h4 j)) • h4 i := by
    have h := h1
    simp only [smul_sub, smul_smul] at h
    rw [sub_eq_sub_iff_add_eq_add] at h
    simpa [mul_comm] using (add_left_cancel h).symm
  have h3 : (a - b) * α4 i (h4 j) = 0 := by
    have h4 : ((a - b) * α4 i (h4 j)) • h4 i = 0 := by
      rw [sub_mul, sub_smul, h2, sub_self]
    exact (smul_eq_zero.mp h4).resolve_right hi
  exact sub_eq_zero.mp (mul_eq_zero.mp h3 |>.resolve_right hij)

private theorem e6QTwoU5_scalar
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V) (hα4 : ∀ i, α4 i (h4 i) = 2)
    (r : Fin 4 → V ≃ₗ[ZMod 3] V) (hr : ∀ i, r i = Module.reflection (hα4 i))
    (hP4 : ∀ i j, α4 i (h4 j) = (CartanMatrix.A 4 i j : ZMod 3))
    {C : V →ₗ[ZMod 3] V} (hC : ∀ i w, C (r i w) = r i (C w)) :
    ∀ i, C (h4 i) = (2 * α4 0 (C (h4 0))) • h4 i := by
  have h01 : α4 0 (h4 1) ≠ 0 := by
    rw [hP4 0 1]
    have h : CartanMatrix.A 4 0 1 = -1 := by decide
    rw [h]
    norm_num
  have h12 : α4 1 (h4 2) ≠ 0 := by
    rw [hP4 1 2]
    have h : CartanMatrix.A 4 1 2 = -1 := by decide
    rw [h]
    norm_num
  have h23 : α4 2 (h4 3) ≠ 0 := by
    rw [hP4 2 3]
    have h : CartanMatrix.A 4 2 3 = -1 := by decide
    rw [h]
    norm_num
  have he : ∀ i, C (h4 i) = (2 * α4 i (C (h4 i))) • h4 i :=
    fun i => e6QTwoU5_eigen h4 α4 hα4 r hr i (hC i)
  have e01 : 2 * α4 0 (C (h4 0)) = 2 * α4 1 (C (h4 1)) :=
    e6QTwoU5_edge h4 α4 hα4 r hr 0 1 h01 (hC 0) (he 0) (he 1)
  have e12 : 2 * α4 1 (C (h4 1)) = 2 * α4 2 (C (h4 2)) :=
    e6QTwoU5_edge h4 α4 hα4 r hr 1 2 h12 (hC 1) (he 1) (he 2)
  have e23 : 2 * α4 2 (C (h4 2)) = 2 * α4 3 (C (h4 3)) :=
    e6QTwoU5_edge h4 α4 hα4 r hr 2 3 h23 (hC 2) (he 2) (he 3)
  intro i
  rw [he i]
  congr 1
  fin_cases i
  · rfl
  · exact e01.symm
  · exact e12.symm.trans e01.symm
  · exact e23.symm.trans (e12.symm.trans e01.symm)

private theorem e6QTwoU5_linearIndependent
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V)
    (hP4 : ∀ i j, α4 i (h4 j) = (CartanMatrix.A 4 i j : ZMod 3))
    (h5 : (5 : ZMod 3) ≠ 0) :
    (Matrix.of fun i j : Fin 4 => α4 i (h4 j)).det ≠ 0 ∧
      LinearIndependent (ZMod 3) h4 := by
  have hdet : (Matrix.of fun i j : Fin 4 => α4 i (h4 j)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j : Fin 4 => α4 i (h4 j))
        = (CartanMatrix.A 4).map (Int.castRingHom (ZMod 3)) := by
      ext i j
      exact hP4 i j
    rw [hmat]
    have hdet_eq : ((CartanMatrix.A 4).map (Int.castRingHom (ZMod 3))).det =
        ((CartanMatrix.A 4).det : ZMod 3) :=
      RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.A 4)
    rw [hdet_eq, CartanMatrix.A_det]
    show (5 : ZMod 3) ≠ 0
    exact h5
  exact ⟨hdet, linearIndependent_of_det_ne_zero h4 α4 hdet⟩

private theorem e6QTwoU5_vx_not_mem
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V) (vx : V)
    (hdet : (Matrix.of fun i j : Fin 4 => α4 i (h4 j)).det ≠ 0)
    (hαvx : ∀ j : Fin 4, α4 j vx = 0) (hvx : vx ≠ 0) :
    vx ∉ Submodule.span (ZMod 3) (Set.range h4) := by
  intro hw
  rw [Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, hc⟩ := hw
  have hcC : (Matrix.of fun j i : Fin 4 => α4 j (h4 i)).mulVec c = 0 := by
    ext j
    have h := congrArg (α4 j) hc
    rw [map_sum] at h
    simp only [map_smul, hαvx j, smul_eq_mul] at h
    change (Matrix.of fun j i : Fin 4 => α4 j (h4 i)).mulVec c j = 0
    rw [Matrix.mulVec, dotProduct]
    rw [← h]
    apply Finset.sum_congr rfl
    intro i _
    simp [Matrix.of_apply, mul_comm]
  have hdet' : (Matrix.of fun j i : Fin 4 => α4 j (h4 i)).det ≠ 0 := hdet
  have hc0 : c = 0 := Matrix.mulVec_injective_of_det_ne_zero hdet'
    (by rw [hcC, Matrix.mulVec_zero])
  have hzero : vx = 0 := by
    rw [← hc]
    simp [hc0]
  exact hvx hzero

private theorem e6QTwoU5_span
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V)
    (hP4 : ∀ i j, α4 i (h4 j) = (CartanMatrix.A 4 i j : ZMod 3))
    (h5 : (5 : ZMod 3) ≠ 0) (vx : V)
    (hαvx : ∀ j : Fin 4, α4 j vx = 0) (hvx : vx ≠ 0)
    (hVcard : Nat.card V = 3 ^ 5) :
    Submodule.span (ZMod 3) (Set.range h4 ∪ {vx}) = ⊤ := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  obtain ⟨hdet, hli⟩ := e6QTwoU5_linearIndependent h4 α4 hP4 h5
  set U := Submodule.span (ZMod 3) (Set.range h4) with hU
  have hU4 : Module.finrank (ZMod 3) U = 4 := by
    rw [show U = Submodule.span (ZMod 3) (Set.range h4) by rfl,
      finrank_span_eq_card hli, Fintype.card_fin]
  have hw0U : vx ∉ U := e6QTwoU5_vx_not_mem h4 α4 vx hdet hαvx hvx
  have hdisj : U ⊓ Submodule.span (ZMod 3) {vx} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨hyU, hyw⟩ := Submodule.mem_inf.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyw
    by_contra hne
    have hc : c ≠ 0 := by
      rintro rfl
      exact hne (zero_smul _ _)
    apply hw0U
    have h := U.smul_mem c⁻¹ hyU
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  have : Fintype V := Fintype.ofFinite V
  have hfin5 : Module.finrank (ZMod 3) V = 5 := by
    have hcard : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3), ZMod.card]
    rw [hVcard] at hcard
    exact (Nat.pow_right_injective (by norm_num) hcard).symm
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span (ZMod 3) {vx})
  rw [hdisj, finrank_bot, add_zero, hU4, finrank_span_singleton hvx] at hsum
  rw [Submodule.span_union, ← hU]
  exact Submodule.eq_top_of_finrank_eq (by omega)

omit [Finite G] in
private theorem e6QTwoU5_scalar_on_stab [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (St : Subgroup (MulAut ↥Bs)) (f : ↥St →* MulAut ↥(ggAutomizer L Bs))
    (e4 : (CoxeterMatrix.A 4).Group ≃* ↥(ggAutomizer L Bs))
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V) (hα4 : ∀ i, α4 i (h4 i) = 2)
    (hrefl4 : ∀ i, ggLin (p := 3) ι ((e4 ((CoxeterMatrix.A 4).simple i) :
      ↥(ggAutomizer L Bs)) : MulAut ↥Bs) = Module.reflection (hα4 i))
    (hP4 : ∀ i j, α4 i (h4 j) = (CartanMatrix.A 4 i j : ZMod 3))
    (hkerC : ∀ φ : ↥St, φ ∈ f.ker → ∀ a ∈ ggAutomizer L Bs,
      a * (φ : MulAut ↥Bs) = (φ : MulAut ↥Bs) * a) :
    ∀ φ : ↥St, φ ∈ f.ker → ∀ i : Fin 4,
      ggLin (p := 3) ι (φ : MulAut ↥Bs) (h4 i) =
        (2 * α4 0 (ggLin (p := 3) ι (φ : MulAut ↥Bs) (h4 0))) • h4 i := by
  classical
  let r : Fin 4 → V ≃ₗ[ZMod 3] V := fun i =>
    ggLin (p := 3) ι ((e4 ((CoxeterMatrix.A 4).simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hr : ∀ i, r i = Module.reflection (hα4 i) := fun i => hrefl4 i
  intro φ hφ i
  have hC : ∀ i w, (ggLin (p := 3) ι (φ : MulAut ↥Bs)).toLinearMap
      (r i w) = r i ((ggLin (p := 3) ι (φ : MulAut ↥Bs)).toLinearMap w) := by
    intro i w
    have hc := hkerC φ hφ _ (e4 ((CoxeterMatrix.A 4).simple i)).property
    have h := congrArg (fun φ' => ggLin (p := 3) ι φ' w) hc
    simp only [map_mul, LinearEquiv.mul_apply] at h
    exact h.symm
  exact e6QTwoU5_scalar h4 α4 hα4 r hr hP4 hC i

omit [Finite G] in
private theorem e6QTwoU5_ker_card [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (St : Subgroup (MulAut ↥Bs)) (f : ↥St →* MulAut ↥(ggAutomizer L Bs))
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V) (vx : V)
    (hspan : Submodule.span (ZMod 3) (Set.range h4 ∪ {vx}) = ⊤)
    (hscalar : ∀ φ : ↥St, φ ∈ f.ker → ∀ i : Fin 4,
      ggLin (p := 3) ι (φ : MulAut ↥Bs) (h4 i) =
        (2 * α4 0 (ggLin (p := 3) ι (φ : MulAut ↥Bs) (h4 0))) • h4 i)
    (hfix0 : ∀ φ : ↥St, ggLin (p := 3) ι (φ : MulAut ↥Bs) vx = vx) :
    Nat.card f.ker ≤ 3 := by
  classical
  let lam : MulAut ↥Bs → ZMod 3 := fun φ => 2 * α4 0 (ggLin (p := 3) ι φ (h4 0))
  have hinj : Function.Injective (fun φ : ↥f.ker => lam ((φ : ↥St) : MulAut ↥Bs)) := by
    intro φ ψ h
    have hlin : (ggLin (p := 3) ι ((φ : ↥St) : MulAut ↥Bs)).toLinearMap =
        (ggLin (p := 3) ι ((ψ : ↥St) : MulAut ↥Bs)).toLinearMap := by
      refine LinearMap.ext_on hspan ?_
      rintro y (⟨i, rfl⟩ | hy)
      · simp only [LinearEquiv.coe_coe]
        rw [hscalar _ φ.2 i, hscalar _ ψ.2 i]
        exact congrArg (· • h4 i) h
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        simp only [LinearEquiv.coe_coe]
        rw [hfix0, hfix0]
    exact Subtype.ext (Subtype.ext
      (ggLin_injective ι (LinearEquiv.toLinearMap_injective hlin)))
  calc Nat.card ↥f.ker ≤ Nat.card (ZMod 3) := Nat.card_le_card_of_injective _ hinj
    _ = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]

private theorem e6QTwoU5_stab_upper [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (hAut : Nat.card (MulAut ↥(ggAutomizer L Bs)) ≤ 120)
    (hxB : x ∈ Bs) (St : Subgroup (MulAut ↥Bs))
    (hStmem : ∀ φ : MulAut ↥Bs, φ ∈ St ↔
      φ ∈ ggAutomizer ⊤ Bs ∧ φ ⟨x, hxB⟩ = ⟨x, hxB⟩)
    (hStN : St ≤ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)))
    (e4 : (CoxeterMatrix.A 4).Group ≃* ↥(ggAutomizer L Bs))
    (h4 : Fin 4 → V) (α4 : Fin 4 → Module.Dual (ZMod 3) V) (hα4 : ∀ i, α4 i (h4 i) = 2)
    (hrefl4 : ∀ i, ggLin (p := 3) ι ((e4 ((CoxeterMatrix.A 4).simple i) :
      ↥(ggAutomizer L Bs)) : MulAut ↥Bs) = Module.reflection (hα4 i))
    (hP4 : ∀ i j, α4 i (h4 j) = (CartanMatrix.A 4 i j : ZMod 3))
    (h5 : (5 : ZMod 3) ≠ 0)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hx1 : x ≠ 1) (hVcard : Nat.card V = 3 ^ 5) :
    Nat.card ↥St ≤ 360 := by
  classical
  let vx : V := ι (Additive.ofMul (⟨x, hxB⟩ : ↥Bs))
  let f : ↥St →* MulAut ↥(ggAutomizer L Bs) :=
    (ggAutomizer L Bs).normalizerMonoidHom.comp (Subgroup.inclusion hStN)
  have hkerC : ∀ φ : ↥St, φ ∈ f.ker → ∀ a ∈ ggAutomizer L Bs,
      a * (φ : MulAut ↥Bs) = (φ : MulAut ↥Bs) * a :=
    e6QTwoU5_ker_centralizes St hStN
  have hvx : vx ≠ 0 := by
    simpa [vx] using e6QTwoU5_vx_ne_zero (V := V) (ι := ι) hxB hx1
  have hαvx : ∀ i : Fin 4, α4 i vx = 0 := by
    simpa [vx] using e6QTwoU5_alpha_vx (V := V) (ι := ι) e4 h4 α4 hα4 hrefl4 hLx hxB
  have hspan : Submodule.span (ZMod 3) (Set.range h4 ∪ {vx}) = ⊤ :=
    e6QTwoU5_span h4 α4 hP4 h5 vx hαvx hvx hVcard
  have hfix0 : ∀ φ : ↥St, ggLin (p := 3) ι (φ : MulAut ↥Bs) vx = vx := by
    intro φ
    simpa [vx] using (ggLin_fix_iff ι (φ : MulAut ↥Bs) ⟨x, hxB⟩).mp
      ((hStmem φ).mp φ.2).2
  have hscalar :=
    e6QTwoU5_scalar_on_stab (V := V) (ι := ι) St f e4 h4 α4 hα4 hrefl4 hP4 hkerC
  have hker_le : Nat.card f.ker ≤ 3 := e6QTwoU5_ker_card (ι := ι) St f h4 α4 vx hspan hscalar hfix0
  have hrange : Nat.card f.range ≤ 120 := (Subgroup.card_le_card_group f.range).trans hAut
  rw [← Subgroup.card_ker_mul_card_range f]
  exact (Nat.mul_le_mul hker_le hrange).trans (by norm_num)

theorem GGSecFiveE6QTwoCfg.false_of_twA4
    (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) (hTBF : GGTBFixInput)
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 4 ∧ lab.n = 1) 3 Bs L) :
    False := by
  classical
  obtain ⟨hRest, -, -, hBs, hxB, hx1, horderx, hLx, hstar, -, hNT⟩ :=
    e6QTwo_config_facts hC
  have hcfg : GGConfig 3 B Bs x L D J := hRest.1
  have h5 : (5 : ZMod 3) ≠ 0 := by decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA4 := e6QTwoU5_weyl_A4 hW hLift hcfg hBs hstar hL
  have hcard5 := e6QTwoU5_card_Bs hC hTBF hA4 horderx
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod 3) V := hVmod
  have hVcard : Nat.card V = 3 ^ 5 := by
    rw [← card_eq_of_ggLin ι]
    exact hcard5
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; norm_num)
  obtain ⟨e4, h4, α4, hα4, hrefl4, hP4⟩ := e6QTwoU5_cartan_A4 hNT hA4 ι
  obtain ⟨A₀, W, hA₀le, hmapA, hstab⟩ := e6QTwoU5_exists_e6W hC hNT hxB hx1 hVcard ι
  let St : Subgroup (MulAut ↥Bs) :=
    ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxB⟩ : ↥Bs)
  have hStmem : ∀ φ : MulAut ↥Bs, φ ∈ St ↔
      φ ∈ ggAutomizer ⊤ Bs ∧ φ ⟨x, hxB⟩ = ⟨x, hxB⟩ := fun φ => Iff.rfl
  have hmapA₁ := e6QTwoU5_map_A1 (ι := ι) A₀ W hmapA hxB
  have hge : 576 ≤ Nat.card St := e6QTwoU5_stab_lower (ι := ι) A₀ W hxB hA₀le hmapA₁ hstab
  have hAut := e6QTwoU5_aut_card hA4
  have hStN := e6QTwoU5_stab_normalizer ggLNoncyclicInput_holds hcfg hxB St hStmem
  have h360 : Nat.card ↥St ≤ 360 :=
    e6QTwoU5_stab_upper (ι := ι) hAut hxB St hStmem hStN e4 h4 α4 hα4 hrefl4 hP4 h5 hLx hx1
      hVcard
  omega

end CFSG.StandardType

end
