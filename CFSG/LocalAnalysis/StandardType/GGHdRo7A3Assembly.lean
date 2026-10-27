module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7D

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem a3_fixes_of_gen {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {H : Subgroup (V ≃ₗ[ZMod p] V)} {S : Set (V ≃ₗ[ZMod p] V)} (hHS : H = Subgroup.closure S)
    {z : V} (hS : ∀ s ∈ S, s z = z) : ∀ a ∈ H, a z = z := by
  intro a ha
  rw [hHS] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => rfl
  | mul x y _ _ hx hy => rw [LinearEquiv.mul_apply, hy, hx]
  | inv x _ hx =>
    conv_lhs => rw [← hx]
    simp

theorem a3_fix_of_leaves (hN : A3NormalizerLeaf) (hRF : A3ReflFixLeaf) {p : ℕ} [Fact p.Prime]
    {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V}
    {z : V} {H A : Subgroup (V ≃ₗ[ZMod p] V)} (hD : A3LinData p m V θ z H A)
    (hfix : ∀ a ∈ H, a z = z) : ∀ a, a ∈ H ↔ A3P p m θ z a := by
  intro a
  refine ⟨fun ha => ?_, hD.hPH a⟩
  obtain ⟨S, hS, hHS, -⟩ := hD.hgen
  have hSP : ∀ s ∈ S, A3P p m θ z s := fun s hs =>
    hRF hN p m V θ z H A hD s (hD.hHA (hS s hs).1) (hS s hs).2 (hfix s (hS s hs).1)
  rw [hHS] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hSP x hx
  | one => exact a3P_one
  | mul x y _ _ hx hy => exact a3P_mul hx hy
  | inv x _ hx => exact a3P_inv hx

theorem a3_lin_of_leaves (hN : A3NormalizerLeaf) (hRF : A3ReflFixLeaf) (hPW : A3PWeylLeaf)
    (hRU : A3ReflULeaf) (hR9 : A3ReflM9Leaf) (hSC : A3StabCardLeaf) (hRM : A3ReduceMLeaf)
    (hRV : A3ReduceVLeaf) (hC : DClassLargeLeaf) (hSm : A3LinSmallLeaf)
    (hKG : GGReflClassLargeInput') {p : ℕ} [Fact p.Prime] {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod p] V)} (hD : A3LinData p m V θ z H A) : ZS.LinWeyl p H := by
  obtain ⟨S, hS, hHS, -⟩ := hD.hgen
  have hgenR : (∀ r ∈ H, GGLinRefl r → r z = z) → ∀ a ∈ H, a z = z := fun h =>
    a3_fixes_of_gen hHS fun s hs => h s (hS s hs).1 (hS s hs).2
  by_cases hmove : ∃ a ∈ H, a z ≠ z
  · obtain ⟨a, ha, haz⟩ := hmove
    rcases hD.hfr.2.2 with ⟨hU, -⟩ | ⟨hM, -⟩
    · exact absurd (hgenR (fun r hr hrr => hRU p m V θ z H A hD hU r hr hrr) a ha) haz
    · have hm9 : m = 9 ∨ 12 ≤ m := by
        have h9 := hD.hm
        obtain ⟨k, hk⟩ := hD.h3
        omega
      by_cases hspan : ∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ (a3Aug p m).map θ
      · rcases hm9 with h9 | h12
        · exact hSm p m V θ z H A hD hM h9 hspan ⟨a, ha, haz⟩
        · obtain ⟨W, _, _, R, hfin, hirr, hgR, hcard, hlift⟩ :=
            hRV hSC hRF hN p m V θ z H A hD hM h12 hspan ⟨a, ha, haz⟩
          exact hlift (hC hKG p hD.hp (m - 1) (by omega) W hfin R hirr hgR hcard)
      · have hspan' : ∀ r ∈ H, GGLinRefl r → ggLinMove r ≤ (a3Aug p m).map θ := by
          intro r hr hrr
          by_contra hn
          exact hspan ⟨r, hr, hrr, hn⟩
        rcases hm9 with h9 | h12
        · exact absurd (hgenR (fun r hr hrr =>
            hR9 p m V θ z H A hD hM h9 r hr hrr (hspan' r hr hrr)) a ha) haz
        · obtain ⟨W, _, _, R, hfin, hirr, hgR, hcard, hlift⟩ :=
            hRM hSC hN p m V θ z H A hD hM h12 hspan'
          exact hlift (hC hKG p hD.hp (m - 2) (by omega) W hfin R hirr hgR hcard)
  · exact hPW p hD.hp m hD.hm hD.h3 V θ z hD.hfr H (a3_fix_of_leaves hN hRF hD fun a ha => by
      by_contra hne
      exact hmove ⟨a, ha, hne⟩)

theorem a3_core {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X O J : Subgroup G}
    {z : G} (hNoTVBs : GGNoTransvection p Bs) (hNoTV : NoTVLeaf) (hXD : XDatumGraphLeaf)
    (hGr : SUGraphLeaf)
    (hLin : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
      A3LinData p m V θ z H A → ZS.LinWeyl p H)
    (hDX : GGResXDatum p Bs X) (hDO : GGResXDatum p Bs O)
    (hAJ : (∃ a ∈ ggAutomizer J Bs, ∃ c ∈ ggAutomizer J Bs, a * c ≠ c * a) ∧
      ggAutomizer J Bs ≤ ggAutomizer X Bs ⊓ ggAutomizer O Bs)
    (hM : A3ModelAt p Bs X z)
    (hstab : ∀ (hz : z ∈ Bs), ∀ ψ ∈ ggAutomizer ⊤ Bs, ψ ⟨z, hz⟩ = ⟨z, hz⟩ →
      ∀ φ ∈ ggAutomizer X Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer X Bs) :
    GGWeylReflectionGroup p (ggAutomizer X Bs ⊔ ggAutomizer O Bs) := by
  obtain ⟨m, V, _, _, ι, θ, hz, hp3, hm, h3, hfr, hmod⟩ := hM
  have hlin : ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι),
      a (ι (Additive.ofMul (⟨z, hz⟩ : ↥Bs))) = ι (Additive.ofMul (⟨z, hz⟩ : ↥Bs)) →
      ∀ s ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι),
        a * s * a⁻¹ ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) := by
    intro a ha hfix s hs
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hs
    have hψz : ψ ⟨z, hz⟩ = ⟨z, hz⟩ := (ggLin_fix_iff (p := p) ι ψ (⟨z, hz⟩ : ↥Bs)).mpr hfix
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (hstab hz ψ hψ hψz φ hφ)
  obtain ⟨SX, hSX, hQX, hcX⟩ := hXD G p Bs X hDX V ι
  obtain ⟨SO, hSO, hQO, hcO⟩ := hXD G p Bs O hDO V ι
  have hNoT := hNoTV G p Bs hNoTVBs V ι
  obtain ⟨⟨a, haJ, c, hcJ, hac⟩, hJle⟩ := hAJ
  obtain ⟨S, hS, hQ, hconn⟩ := hGr p V _ _ ((ggAutomizer J Bs).map (ggLin (p := p) ι)) SX SO
    hSX hQX hcX hSO hQO hcO (Subgroup.map_mono (hJle.trans inf_le_left))
    (Subgroup.map_mono (hJle.trans inf_le_right))
    ⟨ggLin (p := p) ι a, Subgroup.mem_map_of_mem _ haJ, ggLin (p := p) ι c,
      Subgroup.mem_map_of_mem _ hcJ, fun h => hac (ggLin_injective (p := p) ι (by
        simpa [← map_mul] using h))⟩
  rw [← Subgroup.map_sup] at hS hQ
  have hDat : A3LinData p m V θ (ι (Additive.ofMul (⟨z, hz⟩ : ↥Bs)))
      ((ggAutomizer X Bs ⊔ ggAutomizer O Bs).map (ggLin (p := p) ι))
      ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) :=
    { hp := hp3
      hm := hm
      h3 := h3
      hfr := hfr
      hPH := fun g hg => Subgroup.map_mono le_sup_left ((hmod g).mpr hg)
      hHA := Subgroup.map_mono (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top))
      hStab := fun g hg hfix s hs => (hmod _).mp (hlin g hg hfix s ((hmod s).mpr hs))
      hNoT := hNoT
      hgen := ⟨S, hS, hQ, hconn⟩ }
  exact ggRC_weylReflGroup_of_linWeyl ι _ (hLin m V θ _ _ _ hDat)

theorem ggResSUCorank3Input_of_leaves (hX : GGResXDichotomyInput) (hJ : GGTBJInputR)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput')
    (hN : A3NormalizerLeaf) (hRF : A3ReflFixLeaf) (hPW : A3PWeylLeaf) (hRU : A3ReflULeaf)
    (hR9 : A3ReflM9Leaf) (hSC : A3StabCardLeaf) (hRM : A3ReduceMLeaf) (hRV : A3ReduceVLeaf)
    (hC : DClassLargeLeaf) (hSm : A3LinSmallLeaf) (hGr : SUGraphLeaf) (hNoTV : NoTVLeaf)
    (hXD : XDatumGraphLeaf) (hLM : A3LModelLeaf) (hLS : A3LStabLeaf) (hKM : A3KModelLeaf)
    (hKS : A3KStabLeaf) (hAJ : A3AJLeaf) : GGResSUCorank3Input := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hrow
  have hp3 : p = 3 := by
    rcases hrow with ⟨-, -, -, -, -, -, h3, -⟩ | ⟨-, -, -, -, -, -, h3, -⟩ <;> exact h3
  have hDL : GGResXDatum p Bs L := by
    rcases (hX G p B Bs x L D J y K hH).1 with hD | h7
    · exact hD
    · exfalso
      obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
      omega
  have hDK : GGResXDatum p Bs K := by
    rcases (hX G p B Bs x L D J y K hH).2 with hD | h7
    · exact hD
    · exfalso
      obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
      omega
  have hLin : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (θ : (Fin m → ZMod p) →ₗ[ZMod p] V) (z : V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
      A3LinData p m V θ z H A → ZS.LinWeyl p H :=
    fun _ _ _ _ _ _ _ _ hD => a3_lin_of_leaves hN hRF hPW hRU hR9 hSC hRM hRV hC hSm hKG hD
  have hAJ' := hAJ hX hJ hRig hLB G p B Bs x L D J y K hH
    (fun hr => hLM hRig G p B Bs x L D J y K hH hr)
    (fun hr => (hKM hRig hLB G p B Bs x L D J y K hH hr).1) hrow
  rcases hrow with hrow | hrow
  · exact a3_core hH.2.2.2.1 hNoTV hXD hGr hLin hDL hDK hAJ'
      (hLM hRig G p B Bs x L D J y K hH hrow) fun hx => hLS G p B Bs x L D J y K hH hrow hx
  · obtain ⟨hMK, hcen⟩ := hKM hRig hLB G p B Bs x L D J y K hH hrow
    rw [sup_comm]
    exact a3_core hH.2.2.2.1 hNoTV hXD hGr hLin hDK hDL
      ⟨hAJ'.1, hAJ'.2.trans (le_of_eq (inf_comm _ _))⟩ hMK
      fun hy => hKS G p B Bs x L D J y K hH hrow hy hcen

end CFSG.StandardType.HdRo7A3
