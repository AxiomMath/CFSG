module

public import CFSG.LocalAnalysis.StandardType.GGD5Forced
public import CFSG.LocalAnalysis.StandardType.GGQ2NbrD5Absorb

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module CFSG.StandardType.GGQ2NbrD5

private theorem ggQ2NbF_line_real {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hLB : GGLBalanceInput)
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (M : GGQTwoAmbModel 3 Bs y x K (L ⊔ K)) (e : Fin 5 ≃ M.ι)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (he0 : M.a = e 0)
    (hκx : ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x)
    (hJ3 : 3 ∣ Nat.card J)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore 3 ↥J))))
    (hSC : lup10d_SCData Bs J)
    {b0 : Fin 4} {γ : Equiv.Perm (Fin 4)} {lam c' : ZMod 3}
    (hadm : lup10fa_Adm b0 γ lam c') (hb0 : e (lup10ab_tau b0.castSucc) = M.b)
    (hWJreal : ∀ r ∈ lup10fa_WJ b0, ∃ ψ ∈ ggAutomizer J Bs, lup10d_fr_Real M κ ψ r)
    (hSpreal : ∀ r ∈ lup10fa_Sp γ lam c',
      ∃ ψ ∈ ggAutomizer ⊤ Bs, lup10d_fr_Real M κ ψ r)
    {z : lup10fa_Vec}
    (hzfix : ∀ j : Fin 4, j ≠ b0 → (lup10fa_s j.castSucc).mulVec z = z)
    (hzspan : z ∉ Submodule.span (ZMod 3) {lup10fa_x})
    (hzO : ∀ v : lup10fa_Vec, (∀ r ∈ lup10fa_O b0 γ lam c' z, r.mulVec v = v) →
      v ∈ Submodule.span (ZMod 3) {z}) :
    ∀ r ∈ lup10fa_O b0 γ lam c' z,
      ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, lup10d_fr_Real M κ ψ r := by
  have hB : GGBstar 3 B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hDy : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hDx : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hD9 : Nat.card ↥D = 9 := by
    rw [hDJ.1.2.2.1]
    norm_num
  have hDswap : D = Subgroup.closure {y, x} := by
    rw [hnb.2.1, Set.pair_comm]
  have hyfix : ∀ j : Fin 4, j ≠ b0 →
      (lup10fa_s j.castSucc).mulVec (κ M.yV) = κ M.yV :=
    lup10d_fr_yV_fixed M e κ hκs he0 hb0
  have hxp : y ^ 3 = 1 := hB.2.1.2 y M.hx
  have hyVspan : κ M.yV ∉ Submodule.span (ZMod 3) {lup10fa_x} :=
    lup10d_fr_yV_not_mem_span M κ hκx hxp hDswap hD9
  have hcardBs : Nat.card ↥Bs = 3 ^ 5 := by
    have h1 : Nat.card ↥Bs = Nat.card M.V :=
      Nat.card_congr (Additive.ofMul.trans M.model.toEquiv)
    have h2 : Nat.card M.V = Nat.card (Fin 5 → ZMod 3) := Nat.card_congr κ.toEquiv
    rw [h1, h2, Nat.card_fun, Nat.card_eq_fintype_card, ZMod.card, Nat.card_fin]
  have hcardBJ : Nat.card ↥(Bs ⊓ J) = 3 ^ 3 := by
    rw [hSC.2.2]
    norm_num
  have hb0ne : b0 ≠ 1 := by
    intro h
    apply hadm.2.2.1
    rw [h, hadm.1]
  have hzbD : (lup10d_fr_zb M κ z : G) ∈ D :=
    lup10d_fr_zB_mem_D M κ hκx hb0ne hyfix hyVspan hzfix hDy hDx
  have hzb1 : (lup10d_fr_zb M κ z : G) ≠ 1 :=
    lup10d_fr_zB_ne_one M κ hzspan
  let R : Set (MulAut ↥Bs) :=
    {ψ | ψ ∈ ggAutomizer ⊤ Bs ∧
      ∃ r ∈ lup10fa_R γ lam c' z, lup10d_fr_Real M κ ψ r}
  let S : Set (MulAut ↥Bs) :=
    {ψ | ψ ∈ ggAutomizer J Bs ∧
      ∃ r ∈ lup10fa_WJ b0, lup10d_fr_Real M κ ψ r}
  have hR : ∀ r ∈ R, r ∈ ggAutomizer ⊤ Bs ∧
      r (lup10d_fr_zb M κ z) = lup10d_fr_zb M κ z := by
    intro ψ hψ
    obtain ⟨hψtop, rr, hrr, hψreal⟩ := hψ
    refine ⟨hψtop, ?_⟩
    apply (ggLin_fix_iff (p := 3) M.model ψ (lup10d_fr_zb M κ z)).mpr
    rw [lup10d_fr_zb_model M κ z]
    apply κ.injective
    rw [hψreal (κ.symm z), LinearEquiv.apply_symm_apply, hrr.2]
  have hSsub : S ⊆ (ggAutomizer J Bs : Set (MulAut ↥Bs)) := fun ψ hψ => hψ.1
  have hOrbConj : ∀ ρ ∈ Subgroup.closure R, ∀ ψ ∈ ggQ2OrbitConj Bs R S,
      ρ * ψ * ρ⁻¹ ∈ ggQ2OrbitConj Bs R S := by
    intro ρ hρ ψ hψ
    refine Subgroup.closure_induction (p := fun ψ _ =>
      ρ * ψ * ρ⁻¹ ∈ ggQ2OrbitConj Bs R S) ?_ ?_ ?_ ?_ hψ
    · intro x hx
      obtain ⟨r, hr, s, hs, rfl⟩ := hx
      exact Subgroup.subset_closure
        ⟨ρ * r, Subgroup.mul_mem _ hρ hr, s, hs, by group⟩
    · simp
    · intro x y _ _ hx hy
      have h : ρ * (x * y) * ρ⁻¹ = (ρ * x * ρ⁻¹) * (ρ * y * ρ⁻¹) := by
        group
      rw [h]
      exact Subgroup.mul_mem _ hx hy
    · intro x _ hx
      have h : ρ * x⁻¹ * ρ⁻¹ = (ρ * x * ρ⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ hx
  have hOconj : ∀ r ∈ lup10fa_O b0 γ lam c' z,
      ∃ ψ ∈ ggQ2OrbitConj Bs R S, lup10d_fr_Real M κ ψ r := by
    intro r hr
    induction hr with
    | base hrs =>
        obtain ⟨ψ, hψJ, hψr⟩ := hWJreal _ hrs
        refine ⟨1 * ψ * 1⁻¹, Subgroup.subset_closure
          ⟨1, Subgroup.one_mem _, ψ, ⟨hψJ, _, hrs, hψr⟩, rfl⟩, ?_⟩
        simpa using hψr
    | conj hmem hsq _ ihP =>
        obtain ⟨ψt, hψt_top, hψt_real⟩ := hSpreal _ hmem.1
        have hψtfix : ψt (lup10d_fr_zb M κ z) = lup10d_fr_zb M κ z := by
          apply (ggLin_fix_iff (p := 3) M.model ψt (lup10d_fr_zb M κ z)).mpr
          rw [lup10d_fr_zb_model M κ z]
          apply κ.injective
          rw [hψt_real (κ.symm z), LinearEquiv.apply_symm_apply, hmem.2]
        have hψt2 : ψt * ψt = 1 := by
          have h2 : lup10d_fr_Real M κ (ψt * ψt) 1 := by
            have h := lup10d_fr_Real_mul M κ hψt_real hψt_real
            rwa [hsq] at h
          exact lup10d_fr_Real_unique M κ h2 (lup10d_fr_Real_one M κ)
        have hψtinv : ψt⁻¹ = ψt := inv_eq_of_mul_eq_one_left hψt2
        have hψtR : ψt ∈ R := ⟨hψt_top, ⟨_, hmem, hψt_real⟩⟩
        obtain ⟨ρ, hρ, hρreal⟩ := ihP
        refine ⟨ψt * ρ * ψt⁻¹,
          hOrbConj ψt (Subgroup.subset_closure hψtR) ρ hρ, ?_⟩
        rw [hψtinv]
        exact lup10d_fr_Real_mul M κ (lup10d_fr_Real_mul M κ hψt_real hρreal) hψt_real
  have hfix : ∀ b : ↥Bs, (∀ φ ∈ ggQ2OrbitConj Bs R S, φ b = b) →
      (b : G) ∈ Subgroup.zpowers (lup10d_fr_zb M κ z : G) := by
    intro b hb
    have hvO : ∀ r ∈ lup10fa_O b0 γ lam c' z,
        r.mulVec (κ (M.model (Additive.ofMul b))) =
          κ (M.model (Additive.ofMul b)) := by
      intro r hr
      obtain ⟨ψ, hψU, hψr⟩ := hOconj r hr
      have hfixb : ggLin (p := 3) M.model ψ (M.model (Additive.ofMul b)) =
          M.model (Additive.ofMul b) :=
        (ggLin_fix_iff (p := 3) M.model ψ b).mp (hb ψ hψU)
      rw [← hψr (M.model (Additive.ofMul b)), hfixb]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hzO _ hvO)
    have hmodel : M.model (Additive.ofMul b) =
        t • M.model (Additive.ofMul (lup10d_fr_zb M κ z)) := by
      apply κ.injective
      rw [map_smul, lup10d_fr_zb_model M κ z, LinearEquiv.apply_symm_apply, ← ht]
    rw [lup10d_fr_smul_model M (lup10d_fr_zb M κ z) t] at hmodel
    have hb_eq : b = lup10d_fr_zb M κ z ^ t.val :=
      Additive.ofMul.injective (M.model.injective hmodel)
    have hbG : (b : G) = ((lup10d_fr_zb M κ z : ↥Bs) : G) ^ t.val := by
      rw [hb_eq, Subgroup.coe_pow]
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨(t.val : ℤ), by rw [zpow_natCast]; exact hbG.symm⟩
  have hUle : ggQ2OrbitConj Bs R S ≤ ggAutomizer (ggG0 3 B x L D J) Bs :=
    ggQ2_lineOrbit_le_ggG0 hS hLB hcardBs hcardBJ hJ3 hZ
      (lup10d_fr_zb M κ z).2 hzbD hzb1 hR hSsub hfix
  intro r hr
  obtain ⟨ψ, hψU, hψr⟩ := hOconj r hr
  exact ⟨ψ, hUle hψU, hψr⟩

theorem ggQ2Nbr_forced_reflection {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (M : GGQTwoAmbModel 3 Bs y x K (L ⊔ K)) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hV : Submodule.span (ZMod 3)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤)
    (hbas : M.toLin.Basis) (hJ3 : 3 ∣ Nat.card J)
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center (↥J ⧸ LargeEvenPPrimeCore 3 ↥J))))
    (hAJ : ggAutomizer J Bs = Subgroup.closure (M.simple '' {k : M.ι | k ≠ M.a ∧ k ≠ M.b}))
    (hSC : lup10d_SCData Bs J) (hTF : lup10fa_TwistFacts)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3))
    (hκ1 : ∀ i : Fin 5, κ (M.coroot (e (lup10ab_tau i))) = Pi.single i 1)
    (hκs : ∀ (i : Fin 5) (v : M.V),
      κ (ggLin (p := 3) M.model (M.simple (e (lup10ab_tau i))) v) = (lup10fa_s i).mulVec (κ v))
    (hκx : ∃ ν : ZMod 3, ν ≠ 0 ∧ κ M.xV = ν • lup10fa_x)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs) (w' : MulAut ↥Bs)
    (hw'K : w' ∈ ggAutomizer K Bs) (b0 : Fin 4) (γ : Equiv.Perm (Fin 4)) (lam c' : ZMod 3)
    (hadm : lup10fa_Adm b0 γ lam c') (hb0 : e (lup10ab_tau b0.castSucc) = M.b)
    (hform : ∀ v : M.V, κ (ggLin (p := 3) M.model (w'⁻¹ * φ) v) =
      (lup10fa_twist γ lam c').mulVec (κ v)) :
    ∃ r' : MulAut ↥Bs, r' ∈ ggAutomizer (ggG0 3 B x L D J) Bs ∧
      ggLin (p := 3) M.model r' = ggLin (p := 3) M.model (φ * M.simple M.a * φ⁻¹) := by
  classical
  have _ : GGStdSubPrimeInput := hP
  have _ : GGQTwoCentralizerInput := h5
  have _ : GGQTwoI1 Bs D J := hI1
  have _ := hecart
  have _ := hV
  have _ := hbas
  have _ := hκ1
  have hKG0 : K ≤ ggG0 3 B x L D J := le_ggG0_of_ggNbr hnb
  have hLKleG0 : L ⊔ K ≤ ggG0 3 B x L D J :=
    sup_le (le_ggG0_left 3 B x L D J) hKG0
  have hsimple : ∀ k : M.ι, M.simple k ∈ ggAutomizer (L ⊔ K) Bs :=
    lup10d_fr_simple_mem M le_sup_right
  have hgenmem : ∀ k : M.ι, M.simple k ∈ ggAutomizer ⊤ Bs :=
    fun k => ggAutomizer_mono Bs le_top (hsimple k)
  have hS0realLK : ∀ r ∈ lup10fa_S0,
      ∃ ψ ∈ ggAutomizer (L ⊔ K) Bs, lup10d_fr_Real M κ ψ r :=
    lup10d_fr_S0_real M e κ hκs hsimple
  have hS0real : ∀ r ∈ lup10fa_S0,
      ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, lup10d_fr_Real M κ ψ r := by
    intro r hr
    obtain ⟨ψ, hψ, hreal⟩ := hS0realLK r hr
    exact ⟨ψ, ggAutomizer_mono Bs hLKleG0 hψ, hreal⟩
  have hWJreal : ∀ r ∈ lup10fa_WJ b0,
      ∃ ψ ∈ ggAutomizer J Bs, lup10d_fr_Real M κ ψ r :=
    lup10d_fr_WJ_real M e κ hκs he0 hAJ hb0
  have hw'G0 : w' ∈ ggAutomizer (ggG0 3 B x L D J) Bs :=
    ggAutomizer_mono Bs hKG0 hw'K
  have hw'top : w' ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hw'G0
  have hSpreal : ∀ r ∈ lup10fa_Sp γ lam c',
      ∃ ψ ∈ ggAutomizer ⊤ Bs, lup10d_fr_Real M κ ψ r :=
    lup10d_fr_Sp_real M e κ hκs he0 hgenmem hw'top hφ hform
  obtain ⟨-, z₁, z₂, hz, hSp⟩ := hTF b0 γ lam c' hadm
  have hOreal : ∀ z ∈ ({z₁, z₂} : Set lup10fa_Vec),
      ∀ r ∈ lup10fa_O b0 γ lam c' z,
        ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, lup10d_fr_Real M κ ψ r := by
    intro z hzmem
    obtain ⟨hzfix, hzspan, hzO⟩ := hz z hzmem
    exact ggQ2NbF_line_real hLB hS hnb M e κ hκs he0 hκx hJ3 hZ hSC hadm hb0
      hWJreal hSpreal hzfix hzspan hzO
  have hrSp : (lup10fa_twist γ lam c' * lup10fa_s 4 *
      (lup10fa_twist γ lam c')⁻¹) ∈ lup10fa_Sp γ lam c' :=
    lup10fa_ConjDer.base (Set.mem_union_right _ rfl)
  have hSpConjDer := hSp hrSp
  have hmemO : ∀ s ∈ (lup10fa_S0 ∪ lup10fa_O b0 γ lam c' z₁ ∪
      lup10fa_O b0 γ lam c' z₂),
      ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, lup10d_fr_Real M κ ψ s := by
    intro s hs
    rcases hs with (hs | hs) | hs
    · exact hS0real s hs
    · exact hOreal z₁ (by simp) s hs
    · exact hOreal z₂ (by simp) s hs
  obtain ⟨ψ₂, hψ₂G0, hψ₂real⟩ :=
    lup10d_fr_real_conjDer M κ hmemO hmemO hSpConjDer
  set χ : MulAut ↥Bs := (w'⁻¹ * φ) * M.simple M.a * (w'⁻¹ * φ)⁻¹ with hχdef
  have h4 : lup10d_fr_Real M κ (M.simple M.a) (lup10fa_s 4) := by
    have h := hκs (4 : Fin 5)
    have he4 : e (lup10ab_tau (4 : Fin 5)) = M.a := by
      rw [lup10d_fr_tau_four]
      exact he0.symm
    rwa [he4] at h
  have hχreal : lup10d_fr_Real M κ χ
      (lup10fa_twist γ lam c' * lup10fa_s 4 * (lup10fa_twist γ lam c')⁻¹) := by
    rw [hχdef]
    exact lup10d_fr_Real_mul M κ (lup10d_fr_Real_mul M κ hform h4)
      (lup10d_fr_Real_inv M κ hform)
  have huniq : χ = ψ₂ := lup10d_fr_Real_unique M κ hχreal hψ₂real
  have hχG0 : χ ∈ ggAutomizer (ggG0 3 B x L D J) Bs := by
    rw [huniq]
    exact hψ₂G0
  have hmem : w' * χ * w'⁻¹ ∈ ggAutomizer (ggG0 3 B x L D J) Bs :=
    mul_mem (mul_mem hw'G0 hχG0) (Subgroup.inv_mem _ hw'G0)
  have heq : w' * χ * w'⁻¹ = φ * M.simple M.a * φ⁻¹ := by
    rw [hχdef]
    group
  exact ⟨φ * M.simple M.a * φ⁻¹, heq ▸ hmem, rfl⟩


end CFSG.StandardType

end
