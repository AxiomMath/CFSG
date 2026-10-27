module

public import CFSG.LocalAnalysis.StandardType.GGTBJLinearMinusFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJLinearMinusWeyl
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourPlusForcing
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGRCSignedCoxeterB
import CFSG.LocalAnalysis.StandardType.GGPZWeylB
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Polynomial

theorem card_ggAutomizer_le_card_spSignedGroup
    {G : Type} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2] {n p : ℕ} [Fact p.Prime]
    (hpF : p ∣ Nat.card F + 1) {g : F[X]} [Fact (Irreducible g)] (hgd : g ∣ cyclotomic p F)
    (hζ : AdjoinRoot.root g ^ p = 1) {hC : (CoordSL.rootMat g).det = 1}
    {hCp : CoordSL.rootMat g ^ p = 1} {s t : ℕ}
    (ε : Fin n ≃ (Fin (CoordSL.rootPB g).dim × Fin s) ⊕ Fin t)
    (φ : Matrix.SpecialLinearGroup (Fin n) F →* G)
    (hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F))
    {Bs X : Subgroup G} (hX : φ.range = X)
    (hframe : (CoordSL.frameHom φ 1 ε hC hCp).range = Bs ⊓ X)
    (hsup : (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) = Bs) :
    Nat.card (ggAutomizer X Bs) ≤ Nat.card (SpJoin.spSignedGroup s p) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set fr : (Fin s → Multiplicative (ZMod p)) →* G := CoordSL.frameSigned φ 1 ε hC hCp with hfr
  have hfr_range : fr.range = Bs ⊓ X := by
    rw [hfr, CoordSL.frameSigned, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (MulEquiv.surjective _), Subgroup.map_top]
    exact hframe
  have hmemBX : ∀ f, fr f ∈ Bs ⊓ X := fun f => by
    rw [← hfr_range]
    exact ⟨f, rfl⟩
  have hmemB : ∀ f, fr f ∈ Bs := fun f => (hmemBX f).1
  let P : MulAut ↥Bs → Prop := fun α =>
    (∀ c : ↥Bs, (c : G) ∈ Subgroup.centralizer (X : Set G) → α c = c) ∧
      ∃ σ ∈ SpJoin.spSignedGroup s p, ∀ f, ((α ⟨fr f, hmemB f⟩ : ↥Bs) : G) = fr (σ f)
  let S : Subgroup (MulAut ↥Bs) :=
    { carrier := {α | P α}
      mul_mem' := by
        rintro α β ⟨hαc, σ, hσ, hα⟩ ⟨hβc, τ, hτ, hβ⟩
        refine ⟨fun c hc => ?_, σ * τ, Subgroup.mul_mem _ hσ hτ, fun f => ?_⟩
        · change α (β c) = c
          rw [hβc c hc, hαc c hc]
        · have h1 : β ⟨fr f, hmemB f⟩ = ⟨fr (τ f), hmemB (τ f)⟩ := Subtype.ext (hβ f)
          change ((α (β ⟨fr f, hmemB f⟩) : ↥Bs) : G) = fr ((σ * τ) f)
          rw [h1, hα (τ f), Equiv.Perm.mul_apply]
      one_mem' := ⟨fun c _ => rfl, 1, Subgroup.one_mem _, fun f => rfl⟩
      inv_mem' := by
        rintro α ⟨hαc, σ, hσ, hα⟩
        refine ⟨fun c hc => ?_, σ⁻¹, Subgroup.inv_mem _ hσ, fun f => ?_⟩
        · conv_lhs => rw [← hαc c hc]
          rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
        · have h1 : α ⟨fr (σ⁻¹ f), hmemB (σ⁻¹ f)⟩ = ⟨fr f, hmemB f⟩ := by
            refine Subtype.ext ?_
            rw [hα (σ⁻¹ f), ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
          have h2 : α⁻¹ ⟨fr f, hmemB f⟩ = ⟨fr (σ⁻¹ f), hmemB (σ⁻¹ f)⟩ := by
            rw [← h1, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
          rw [h2] }
  have hle : ggAutomizer X Bs ≤ S := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro α ⟨x, hxX, hxN, hα⟩
    refine ⟨fun c hc => Subtype.ext ?_, ?_⟩
    · rw [hα c]
      have hcx : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x hxX
      rw [hcx, mul_assoc, mul_inv_cancel, mul_one]
    · have hxφ : x ∈ φ.range := by rw [hX]; exact hxX
      have hnorm : ∀ f, ∃ f', x * fr f * x⁻¹ = fr f' := by
        intro f
        have hB : x * fr f * x⁻¹ ∈ Bs := by
          rw [← hα ⟨fr f, hmemB f⟩]
          exact (α ⟨fr f, hmemB f⟩).2
        have hXm : x * fr f * x⁻¹ ∈ X :=
          X.mul_mem (X.mul_mem hxX (hmemBX f).2) (X.inv_mem hxX)
        have hmem : x * fr f * x⁻¹ ∈ fr.range := by
          rw [hfr_range]
          exact ⟨hB, hXm⟩
        obtain ⟨f', hf'⟩ := hmem
        exact ⟨f', hf'.symm⟩
      obtain ⟨σ, hσ, hσf⟩ :=
        (CoordSL.signed_of_frame hpF hgd hζ ε φ hker 1).1 x hxφ hnorm
      exact ⟨σ, hσ, fun f => by rw [hα, hσf]⟩
  have hinj : ∃ F' : ↥S → ↥(SpJoin.spSignedGroup s p), Function.Injective F' := by
    choose σ hσ hσf using fun α : ↥S => α.2.2
    refine ⟨fun α => ⟨σ α, hσ α⟩, fun α β hαβ => ?_⟩
    have hσeq : σ α = σ β := congrArg Subtype.val hαβ
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    let E : Subgroup ↥Bs := MonoidHom.eqLocus (α : MulAut ↥Bs).toMonoidHom
      (β : MulAut ↥Bs).toMonoidHom
    have h1 : Bs ⊓ X ≤ E.map Bs.subtype := by
      intro y hy
      have hy' : y ∈ fr.range := by rw [hfr_range]; exact hy
      obtain ⟨f, hf⟩ := hy'
      refine ⟨⟨fr f, hmemB f⟩, ?_, hf⟩
      change (α : MulAut ↥Bs) _ = (β : MulAut ↥Bs) _
      refine Subtype.ext ?_
      rw [hσf α f, hσf β f, hσeq]
    have h2 : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ E.map Bs.subtype := by
      intro y hy
      refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
      change (α : MulAut ↥Bs) _ = (β : MulAut ↥Bs) _
      rw [α.2.1 _ hy.2, β.2.1 _ hy.2]
    have hBE : Bs ≤ E.map Bs.subtype := hsup.symm.le.trans (sup_le h1 h2)
    obtain ⟨e, he, hbe⟩ := hBE b.2
    have heb : e = b := Subtype.ext hbe
    rw [← heb]
    exact he
  obtain ⟨F', hF'⟩ := hinj
  exact Nat.card_le_card_of_injective (fun a : ↥(ggAutomizer X Bs) => F' ⟨a, hle a.2⟩)
    fun a b hab => Subtype.ext (congrArg (fun c : ↥S => (c : MulAut ↥Bs)) (hF' hab))

theorem card_ggAutomizer_le_48_of_psl6Four
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {d : G} {A : Subgroup G} (hc : GGConfig p B Bs x L D J) (hA : GGInnerDiagOn Bs A)
    (hn : GGNbr p B x D J d A) (hp5 : p = 5)
    (hlab : GGHasLabel ⟨.A, 5, 2⟩ (↥A ⧸ Subgroup.center ↥A)) :
    Nat.card (ggAutomizer A Bs) ≤ 48 := by
  subst hp5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hΛA : LargeEvenInLambda2 ⟨.A, 5, 2⟩ := ⟨by norm_num, by norm_num, fun _ => le_rfl⟩
  have hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, 5, 2⟩) 5 Bs A :=
    (hA.label (fun _ _ => True) 5).mono_label_of_hasLabel fun lab hΛ hhas _ =>
      ggLabelIso_a5_right (ggLabelRigidInput_holds lab ⟨.A, 5, 2⟩ _ hΛ hΛA hhas hlab)
  obtain ⟨F, hField, hFinite, hChar, g, hg, hC, hCp, s, t, ε, φ, hF, hgd, hroot, hφX, hφker, hs3,
      hframe, -, hsup⟩ :=
    exists_frame_of_linMinus hc (by norm_num : 5 ∣ 2 ^ 2 + 1) hmark
      fun hN => pow_three_le_card_range_ggGamma_bstar hc hn hN
  have hpF : 5 ∣ Nat.card F + 1 := by rw [hF]; norm_num
  have hpF0 : ((5 : ℕ) : F) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo (by norm_num) (by norm_num)
  have hdim : (CoordSL.rootPB g).dim = 2 :=
    SpNS.rootPB_dim_eq_two (by norm_num) (by norm_num) hpF0 hgd hpF
  have hs : s = 3 := by
    have h1 := Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod, hdim] at h1
    omega
  subst hs
  have hbound := card_ggAutomizer_le_card_spSignedGroup hpF hgd hroot ε φ hφker hφX hframe hsup
  obtain ⟨e, -⟩ := ggRC_coxeterB_equiv_spSigned (p := 5) (by norm_num) (k := 3) (by norm_num)
  have h48 : Nat.card (SpJoin.spSignedGroup 3 5) = 48 := by
    rw [← Nat.card_congr e.toEquiv, ggCoxeterB_card 3 (by norm_num)]
    norm_num [Nat.factorial]
  omega

end CFSG.StandardType

end
