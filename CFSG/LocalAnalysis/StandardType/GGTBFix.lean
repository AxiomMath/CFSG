module

public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkSplit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestGen
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProof

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTorusNoFix (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∀ a ∈ A, (∀ n : L', GGTorusWeylElt p A n →
        MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem ggFix_automizer_le_zpowers_of_noFix {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type}
    [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hT : GGTorusNoFix p r R I) (b : Bs)
    (hb : ∀ φ ∈ ggAutomizer L Bs, φ b = b) : (b : G) ∈ Subgroup.zpowers x := by
  classical
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma L hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, ggBeta_mem L θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  have hcA := card_range_ggGamma_mul L hBN hp hS
  have hcβ := card_range_ggBeta_mul L θ hp hS hL hBN
  have hAβ : Nat.card (ggGamma L hBN).range = Nat.card (ggBeta L θ hBN).range :=
    Nat.eq_of_mul_eq_mul_right hp.pos (hcA.trans hcβ.symm)
  have hle : Nat.card (ggGamma L hBN).range ≤ Nat.card γ.range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have hr : p ^ r ≤ Nat.card γ.range := by
    refine le_trans ?_ hle
    rw [hAβ]
    exact pow_le_card_range_ggBeta hp hS hL θ hBN hlift
  have h3' : p ^ 3 ≤ Nat.card γ.range := by
    refine le_trans ?_ hle
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  have hker : ∀ b : Bs, γ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := fun b => by
    rw [hγ, ggGamma_eq_one_iff, ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1
      hS.2.2.2.1.1 hS.2.2.2.2]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  rw [← hker]
  refine hT L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI
    hr h3' (γ b) ⟨b, rfl⟩ ?_
  intro n hn
  have hWB : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨htp, htA⟩ := hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
      simpa using hWB w hw)
    simpa using Subgroup.inv_mem _ h
  have hφ : Bs.normalizerMonoidHom ⟨n, hnN⟩ ∈ ggAutomizer L Bs :=
    Subgroup.subset_closure ⟨(n : G), n.2, hnN, fun _ => rfl⟩
  have hnb : (n : G) * b * (n : G)⁻¹ = b := congrArg Subtype.val (hb _ hφ)
  have hc := ggGamma_conj L hBsN n b (hWB b b.2)
  rw [← hγ] at hc
  rw [← hc]
  congr 1
  exact Subtype.ext hnb

theorem ggTBSpan_of_fix_le {p : ℕ} [Fact p.Prime] {Bs : Subgroup G} {x : G} (hx : x ^ p = 1)
    {Λ : Type} [Fintype Λ] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (ha : V) (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hind : LinearIndependent (ZMod p) (ggOptFam ha h))
    (hfix : ∀ b : Bs, (∀ i, φ i b = b) → (b : G) ∈ Subgroup.zpowers x) :
    Submodule.span (ZMod p) (Set.range (ggOptFam ha h)) = ⊤ := by
  classical
  have hp : p.Prime := Fact.out
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  let W : Submodule (ZMod p) (Module.Dual (ZMod p) V) := Submodule.span (ZMod p) (Set.range α)
  have hker : ∀ w ∈ W.dualCoannihilator, ((Additive.toMul (ι.symm w) : Bs) : G) ∈
      Subgroup.zpowers x := by
    intro w hw
    refine hfix _ fun i => ?_
    have hαi : α i w = 0 :=
      (Submodule.mem_dualCoannihilator w).mp hw _ (Submodule.subset_span ⟨i, rfl⟩)
    have h1 := hlin i w
    rw [hαi, zero_smul, sub_zero, ggLin_apply] at h1
    have h2 := congrArg ι.symm h1
    rw [AddEquiv.symm_apply_apply] at h2
    exact Additive.ofMul.injective (by rw [h2]; rfl)
  let e : W.dualCoannihilator → Subgroup.zpowers x := fun w => ⟨_, hker w.1 w.2⟩
  have he : Function.Injective e := by
    intro w w' hww
    have h0 : ((Additive.toMul (ι.symm w.1) : Bs) : G) =
        ((Additive.toMul (ι.symm w'.1) : Bs) : G) :=
      congrArg (fun z : Subgroup.zpowers x => (z : G)) hww
    have h1 : (Additive.toMul (ι.symm w.1) : Bs) = Additive.toMul (ι.symm w'.1) := Subtype.ext h0
    exact Subtype.ext (ι.symm.injective (Additive.toMul.injective h1))
  have hcard : Nat.card W.dualCoannihilator ≤ p := by
    refine (Nat.card_le_card_of_injective e he).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hx
  have hkerrank : Module.finrank (ZMod p) W.dualCoannihilator ≤ 1 := by
    have h1 := FiniteField.pow_finrank_eq_natCard p W.dualCoannihilator
    have h2 : p ^ Module.finrank (ZMod p) W.dualCoannihilator ≤ p ^ 1 := by
      rw [h1, pow_one]; exact hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  have hW : Module.finrank (ZMod p) W ≤ Fintype.card Λ := finrank_range_le_card (R := ZMod p) α
  have hV : Module.finrank (ZMod p) V ≤ Fintype.card Λ + 1 := by
    rw [← Subspace.finrank_add_finrank_dualCoannihilator_eq W]
    omega
  have hle := hind.fintype_card_le_finrank
  rw [Fintype.card_option] at hle
  exact hind.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_option]; omega)

theorem ggFixed_of_mem_closure {E : Type*} [Group E] {Λ : Type*} (φ : Λ → MulAut E) (b : E)
    (hb : ∀ i, φ i b = b) : ∀ ψ ∈ Subgroup.closure (Set.range φ), ψ b = b := by
  intro ψ hψ
  have hle : Subgroup.closure (Set.range φ) ≤ MulAction.stabilizer (MulAut E) b := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hb i
  exact hle hψ

end Transfer

theorem ggTBSpanInput_of_fix (hFix : GGTBFixInput) : GGTBSpanInput := by
  intro G _ _ p B Bs x L D J hC hO hI hNT y K hN hR hPm _ Λ _ _ M C V _ _ ι φ φa h α ha αa b c hM
    hCM hF hlin hlina hind hL hK
  obtain ⟨-, hBs, hxB, -, -⟩ := hC.tableB_facts
  have hx : x ^ p = 1 := hBs.2 x hxB
  refine ggTBSpan_of_fix_le hx ι φ h α ha hlin hind fun b hb => ?_
  refine hFix G p B Bs x L D J hC hO hI hNT y K hN hR hPm b ?_
  rw [hL]
  exact ggFixed_of_mem_closure φ b hb

theorem ggCoxeterForkLabelInput_of_fix (hFix : GGTBFixInput) (h5 : GGForkCrossGe5Input)
    (hR : GGForkWeylExtRestInput) : GGCoxeterForkLabelInput :=
  ggCoxeterForkLabelInput_of_split (ggTBSpanInput_of_fix hFix) h5 hR

end CFSG.StandardType
