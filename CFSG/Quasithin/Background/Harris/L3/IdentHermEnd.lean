module

public import CFSG.Quasithin.Background.Harris.L3.IdentHerm
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.ConjTransport
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.SchurEnd

public section

namespace CFSG.Quasithin.G11.Harris.L3

set_option linter.unusedSectionVars false

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 CFSG.Quasithin.H.Tri Matrix
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_act_of_mem {L : Subgroup (GLV V)} {π : SL(3, F) →* ↥L}
    (hπ : Function.Surjective π) (hK : Nat.card F = (2 ^ n) ^ 2)
    {ψ : SL(3, F) →* SL(3, F)} (hψ : ∀ g, ψ (ψ g) = g) {E : Multiplicative V ≃* HMod n F}
    (hE : ∀ g u, E (Multiplicative.ofAdd (repOfHom L π g u)) =
      rho hK (ψ g) (E (Multiplicative.ofAdd u))) {l : GLV V} (hl : l ∈ L) :
    ∃ g : SL(3, F), ∀ u, hmu E (l u) = tw n (g : Matrix (Fin 3) (Fin 3) F) (hmu E u) := by
  obtain ⟨g', hg'⟩ := hπ ⟨l, hl⟩
  refine ⟨ψ g', fun u => ?_⟩
  have := hmu_act hK hψ hE (ψ g') u
  rw [hψ, hg'] at this
  exact this

theorem herm_smul_herm {c : F} (hc : bar n c = c) {X : Matrix (Fin 3) (Fin 3) F}
    (hX : (conjM n X)ᵀ = X) : (conjM n (c • X))ᵀ = c • X := by
  ext i j
  have h := congrFun (congrFun hX i) j
  simp only [conjM, Matrix.transpose_apply, Matrix.map_apply] at h ⊢
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hc, h]

@[expose] noncomputable def scalFun (E : Multiplicative V ≃* HMod n F) (c : F) (hc : bar n c = c)
    (u : V) : V :=
  Multiplicative.toAdd (E.symm (mkH (c • hmu E u) (herm_smul_herm hc (hmu_herm E u))))

theorem hmu_scalFun (E : Multiplicative V ≃* HMod n F) (c : F) (hc : bar n c = c) (u : V) :
    hmu E (scalFun E c hc u) = c • hmu E u := by
  simp [scalFun, hmu_apply, mat_mkH]

@[expose] noncomputable def scalEnd (E : Multiplicative V ≃* HMod n F) (c : F) (hc : bar n c = c) :
    Module.End (ZMod 2) V :=
  AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' (scalFun E c hc) fun u v =>
    hmu_injective E (by rw [hmu_scalFun, map_add, map_add, hmu_scalFun, hmu_scalFun, smul_add]))

theorem hmu_scalEnd (E : Multiplicative V ≃* HMod n F) (c : F) (hc : bar n c = c) (u : V) :
    hmu E (scalEnd E c hc u) = c • hmu E u := hmu_scalFun E c hc u

theorem scalEnd_mem {L : Subgroup (GLV V)} {π : SL(3, F) →* ↥L} (hπ : Function.Surjective π)
    (hK : Nat.card F = (2 ^ n) ^ 2) {ψ : SL(3, F) →* SL(3, F)} (hψ : ∀ g, ψ (ψ g) = g)
    {E : Multiplicative V ≃* HMod n F}
    (hE : ∀ g u, E (Multiplicative.ofAdd (repOfHom L π g u)) =
      rho hK (ψ g) (E (Multiplicative.ofAdd u))) (c : F) (hc : bar n c = c) :
    scalEnd E c hc ∈ endCommutant L := by
  rw [CFSG.Quasithin.Background.Harris.OrdinaryProofs.mem_endCommutant_iff]
  intro l hl
  obtain ⟨g, hg⟩ := exists_act_of_mem hπ hK hψ hE hl
  refine LinearMap.ext fun v => hmu_injective E ?_
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe]
  rw [hg, hmu_scalEnd, hmu_scalEnd, hg, tw_smul]

@[expose] noncomputable def vE00 (hK : Nat.card F = (2 ^ n) ^ 2)
    (E : Multiplicative V ≃* HMod n F) : V :=
  Multiplicative.toAdd (E.symm (e00 hK))

theorem hmu_vE00 (hK : Nat.card F = (2 ^ n) ^ 2) (E : Multiplicative V ≃* HMod n F) :
    hmu E (vE00 hK E) = mat (e00 hK) := by
  simp [vE00, hmu_apply]

theorem vE00_ne_zero (hK : Nat.card F = (2 ^ n) ^ 2) (E : Multiplicative V ≃* HMod n F) :
    vE00 hK E ≠ 0 := by
  intro h
  have := hmu_vE00 hK E
  rw [h, map_zero] at this
  have h00 := congrFun (congrFun this 0) 0
  simp [mat_pt, rk1_apply] at h00

theorem vE00_fixed (hK : Nat.card F = (2 ^ n) ^ 2) {E : Multiplicative V ≃* HMod n F}
    {Q : Set (GLV V)} (hQ : HermQ E Q) {q : GLV V} (hq : q ∈ Q) :
    q (vE00 hK E) = vE00 hK E := by
  obtain ⟨j, hj, a, h⟩ := hQ.act q hq
  apply hmu_injective E
  rw [h, hmu_vE00]
  have h2 := congrArg mat (rhoT_trGL_e00 hK hj a)
  rw [mat_rhoT, coe_trGL] at h2
  exact h2

theorem natCard_endCommutant_herm [Finite V] {L : Subgroup (GLV V)} {π : SL(3, F) →* ↥L}
    (hπ : Function.Surjective π) (hn : 1 ≤ n) (hK : Nat.card F = (2 ^ n) ^ 2)
    {ψ : SL(3, F) →* SL(3, F)} (hψ : ∀ g, ψ (ψ g) = g) {E : Multiplicative V ≃* HMod n F}
    (hE : ∀ g u, E (Multiplicative.ofAdd (repOfHom L π g u)) =
      rho hK (ψ g) (E (Multiplicative.ofAdd u))) (hirr : IsIrr L ⊤) :
    Nat.card (endCommutant L) = 2 ^ n := by
  classical
  have hQ := hermQ_radSet hK hψ hE
  have hQL := radSet_subset π ψ
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have : Finite (endCommutant L) := Subtype.finite
  have hFq : Nat.card {b : F // bar n b = b} = 2 ^ n := card_fixed hn hK
  refine le_antisymm ?_ ?_
  · rw [← hFq]
    refine Nat.card_le_card_of_injective
      (fun f => (⟨hmu E ((f : Module.End (ZMod 2) V) (vE00 hK E)) 0 0, hmu_bar E _ 0 0⟩ :
        {b : F // bar n b = b})) fun f f' hff => ?_
    have hfix : ∀ g : endCommutant L, ∀ q ∈ radSet π ψ,
        (q : GLV V) ((g : Module.End (ZMod 2) V) (vE00 hK E)) =
          (g : Module.End (ZMod 2) V) (vE00 hK E) := by
      intro g q hq
      rw [← CFSG.Quasithin.Background.Harris.OrdinaryProofs.endCommutant_apply_comm g.2
        (hQL hq), vE00_fixed hK hQ hq]
    have h00 : hmu E ((f : Module.End (ZMod 2) V) (vE00 hK E)) 0 0 =
        hmu E ((f' : Module.End (ZMod 2) V) (vE00 hK E)) 0 0 := congrArg Subtype.val hff
    have heq : (f : Module.End (ZMod 2) V) (vE00 hK E) =
        (f' : Module.End (ZMod 2) V) (vE00 hK E) := by
      apply hmu_injective E
      ext i j
      by_cases hij : i = 0 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := hij
        exact h00
      · rw [hmu_eq_zero_of_fixed hn hK hQ (hfix f) i j hij,
          hmu_eq_zero_of_fixed hn hK hQ (hfix f') i j hij]
    apply Subtype.ext
    by_contra hne
    have hsub : ((f - f' : endCommutant L) : Module.End (ZMod 2) V) ≠ 0 := fun h0 =>
      hne (sub_eq_zero.mp h0)
    have hinj := CFSG.Quasithin.Background.Harris.OrdinaryProofs.injective_of_mem_endCommutant
      hirr (f - f' : endCommutant L).2 hsub
    apply vE00_ne_zero hK E
    apply hinj
    rw [map_zero]
    show (f : Module.End (ZMod 2) V) (vE00 hK E) - (f' : Module.End (ZMod 2) V) (vE00 hK E) = 0
    rw [heq, sub_self]
  · rw [← hFq]
    refine Nat.card_le_card_of_injective
      (fun b => (⟨scalEnd E b.1 b.2, scalEnd_mem hπ hK hψ hE b.1 b.2⟩ : endCommutant L))
      fun b b' hbb => ?_
    have h1 := congrArg (fun f : endCommutant L =>
      hmu E ((f : Module.End (ZMod 2) V) (vE00 hK E)) 0 0) hbb
    simp only [hmu_scalEnd, hmu_vE00, Matrix.smul_apply] at h1
    have h2 : mat (e00 hK) 0 0 = 1 := by simp [mat_pt, rk1_apply]
    rw [h2, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h1
    exact Subtype.ext h1

end CFSG.Quasithin.G11.Harris.L3
