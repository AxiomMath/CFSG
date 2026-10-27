module

public import CFSG.RankThree.GF2n.Smith81.S81E7Cent
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe7

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem unit_apply_inv_apply (u : (Module.End K (V K))ˣ) (w : V K) :
    (u : Module.End K (V K)) (((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) w) = w := by
  rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

theorem exists_idx0_perp_pr_neg_one : ∃ a ∈ idx0, ∃ β ∈ Perp, pr a β = -1 := by
  have hne : idx0.Nonempty := Finset.card_pos.1 (by have := card_idx0; omega)
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hb⟩ := exists_adjD a (mem_idx0.1 ha)
  obtain ⟨β, hβ, hpa, -⟩ := adjD_iff.1 hb
  exact ⟨a, ha, β, hβ, hpa⟩

theorem xu_one_single_perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) {a : Fin e7Data.d}
    (h : pr a β = -1) :
    ((e7Data_valid.xu K β 1 : (Module.End K (V K))ˣ) : Module.End K (V K)) (Finsupp.single a 1) =
      Finsupp.single a 1 + Finsupp.single (shift β a) 1 := by
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  rw [e7Data_valid.xu_apply, rootOp_single (K := K) hβ'.1 a, if_pos h, one_smul]

theorem Lam_faithful_V0 {l : (Module.End K (V K))ˣ} (hl : l ∈ Lam K)
    (h : ∀ v ∈ V0 K, (l : Module.End K (V K)) v = v) : l = 1 := by
  haveI : IsSimpleGroup (Lam K) := isSimpleGroup_Lam
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (Lam K), ∀ x : Lam K, x ∈ N ↔
      ∀ v ∈ V0 K, ((x : (Module.End K (V K))ˣ) : Module.End K (V K)) v = v :=
    ⟨{ carrier := {x | ∀ v ∈ V0 K, ((x : (Module.End K (V K))ˣ) : Module.End K (V K)) v = v}
       mul_mem' := by
         intro x y hx hy v hv
         have hx' : ∀ v ∈ V0 K, ((x : (Module.End K (V K))ˣ) : Module.End K (V K)) v = v := hx
         have hy' : ∀ v ∈ V0 K, ((y : (Module.End K (V K))ˣ) : Module.End K (V K)) v = v := hy
         rw [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, hy' v hv, hx' v hv]
       one_mem' := by
         intro v _
         simp
       inv_mem' := by
         intro x hx v hv
         have hx' : ∀ v ∈ V0 K, ((x : (Module.End K (V K))ˣ) : Module.End K (V K)) v = v := hx
         have hxi : ((x : (Module.End K (V K))ˣ))⁻¹ ∈ Lam K := (Lam K).inv_mem x.2
         have hw := hx' _ (Lam_stabilizes_V0 hxi hv)
         have hid := unit_apply_inv_apply (x : (Module.End K (V K))ˣ) v
         rw [Subgroup.coe_inv]
         exact hw.symm.trans hid }, fun x => Iff.rfl⟩
  haveI hNn : N.Normal := ⟨fun n hn g => by
    rw [hNdef] at hn ⊢
    intro v hv
    have hgv := Lam_stabilizes_V0 ((Lam K).inv_mem g.2) hv
    have h1 := hn _ hgv
    have h2 := unit_apply_inv_apply (g : (Module.End K (V K))ˣ) v
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul,
      Module.End.mul_apply, Module.End.mul_apply, h1, h2]⟩
  rcases Subgroup.Normal.eq_bot_or_eq_top N with hbot | htop
  · have hx : (⟨l, hl⟩ : ↥(Lam K)) ∈ N := (hNdef _).2 h
    rw [hbot, Subgroup.mem_bot] at hx
    exact congrArg Subtype.val hx
  · exfalso
    obtain ⟨a, ha, β, hβ, hpa⟩ := exists_idx0_perp_pr_neg_one
    have hxN : (⟨e7Data_valid.xu K β 1, xu_mem_Lam hβ 1⟩ : ↥(Lam K)) ∈ N := by
      rw [htop]
      exact Subgroup.mem_top _
    have hfix : ((e7Data_valid.xu K β 1 : (Module.End K (V K))ˣ) : Module.End K (V K))
        (Finsupp.single a 1) = Finsupp.single a 1 :=
      (hNdef _).1 hxN _ (single_mem_V0 ha)
    rw [xu_one_single_perp hβ hpa] at hfix
    have h3 : Finsupp.single (shift β a) (1 : K) = 0 :=
      add_left_cancel (hfix.trans (add_zero _).symm)
    exact one_ne_zero (Finsupp.single_eq_zero.1 h3)

end CFSG.RankThree.GF2n.Smith81.E7Model
