module

public import CFSG.LocalAnalysis.StandardType.GGQ2SubStab
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPerm
import CFSG.LocalAnalysis.StandardType.GGLargeDepOrder
import CFSG.LocalAnalysis.StandardType.GGLargeDepRestrictAux
import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
import CFSG.LocalAnalysis.StandardType.GGRCMonomial
import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem ggQ2TNR_order_contra {m n : ℕ} (hm : 11 ≤ m)
    (hcard : n ≤ 3 ^ m * (3 * (m + 1).factorial))
    (hbound : 3 ^ ((m - 1) * (m - 1 - 1) / 2) ≤ 8 * n) : False := by
  have hkey := l04fD3_key12 (p := 3) (by norm_num) (N := m + 1) (by omega)
  have hexp : ((m + 1) - 2) * ((m + 1) - 3) / 2 = (m - 1) * (m - 1 - 1) / 2 := by
    rw [show (m + 1) - 2 = m - 1 by omega, show (m + 1) - 3 = m - 1 - 1 by omega]
  rw [hexp] at hkey
  have h8 : 8 * n ≤
      8 * (3 ^ (m + 1) * (6 * (3 - 1) * (2 ^ (m + 1) * (m + 1).factorial))) := by
    refine Nat.mul_le_mul_left 8 (hcard.trans ?_)
    have hstep : 3 ^ m * (3 * (m + 1).factorial) ≤
        3 ^ (m + 1) * (3 * (m + 1).factorial) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    refine hstep.trans (Nat.mul_le_mul_left _ ?_)
    have h2 : (3 : ℕ) ≤ 6 * (3 - 1) * 2 ^ (m + 1) := by
      have h61 : 6 * (3 - 1) = 12 := by norm_num
      have hpos : 0 < 2 ^ (m + 1) := pow_pos (by norm_num) _
      rw [h61]
      omega
    calc 3 * (m + 1).factorial ≤ (6 * (3 - 1) * 2 ^ (m + 1)) * (m + 1).factorial :=
          Nat.mul_le_mul_right _ h2
      _ = 6 * (3 - 1) * (2 ^ (m + 1) * (m + 1).factorial) := by rw [mul_assoc]
  exact absurd (lt_of_le_of_lt h8 hkey) (not_lt.mpr hbound)

theorem ggQ2TN_caseII (hK : GGReflClassOmegaLarge) [Module.Finite (ZMod 3) V]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A) {m : ℕ} (hm : 11 ≤ m)
    (h3 : 3 ∣ m + 1) (c : Fin m → V) (α : Fin m → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A m i j : ZMod 3))
    (s : Fin m → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsA : ∀ i, s i ∈ A)
    (x : V) (hxfix : ∀ i, α i x = 0)
    (hfix : ∀ z, (∀ i, α i z = 0) → z ∈ Submodule.span (ZMod 3) {x})
    (hker : ∀ z ∈ Submodule.span (ZMod 3) (Set.range c), (∀ i, α i z = 0) → z = 0)
    (hconn : ∀ i j, Relation.ReflTransGen (fun a b => α a (c b) ≠ 0 ∧ α b (c a) ≠ 0) i j)
    (hH : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range c)) = m - 1)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x})
    (hcard : Nat.card A ≤ 3 ^ m * (3 * (m + 1).factorial))
    (hHR : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c)) :
    False := by
  classical
  have hfinV : Finite V := Module.finite_of_finite (ZMod 3)
  have hfinGL : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (fun v => congrFun h v))
  have hfinA : Finite A := Subtype.finite
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range c)
  let R : Subgroup (V ≃ₗ[ZMod 3] V) := reflGp A
  have hαc : ∀ i, α i (c i) = 2 := by
    intro i
    rw [hpair i i]
    have hdiag : CartanMatrix.A m i i = 2 := by simp [CartanMatrix.A]
    rw [hdiag]
    norm_num
  have hRA : R ≤ A := ggWAut_reflGp_le A
  have hsR : ∀ i, s i ∈ R := by
    intro i
    change s i ∈ Subgroup.closure {t | t ∈ A ∧ IsReflLin t}
    refine Subgroup.subset_closure ⟨hsA i, ⟨c i, α i, hαc i, ?_⟩⟩
    ext v
    rw [hs i v, Module.reflection_apply]
  have hstab : R ≤ ggLinStab H := by
    intro r hr
    exact ⟨fun v hv => hHR r hr v hv,
      fun v hv => hHR r⁻¹ (Subgroup.inv_mem R hr) v hv⟩
  let φ : R →* (H ≃ₗ[ZMod 3] H) := (ggLinRestrictHom H).comp (Subgroup.inclusion hstab)
  have hφapply : ∀ (r : R) (v : H),
      (((φ r) v : H) : V) = (r : V ≃ₗ[ZMod 3] V) (v : V) :=
    fun r v => l04fD2_restrict_apply H (Subgroup.inclusion hstab r) v
  have hφker : φ.ker = ⊥ := by
    refine le_antisymm (fun r hr => ?_) bot_le
    rw [Subgroup.mem_bot]
    have hr1 : φ r = 1 := MonoidHom.mem_ker.mp hr
    have hU : ∀ u ∈ H, (r : V ≃ₗ[ZMod 3] V) u = u := by
      intro u hu
      have h1 : ((φ r) ⟨u, hu⟩ : H) = ⟨u, hu⟩ := by
        rw [hr1]
        simp
      have h2 := congrArg (fun w : H => (w : V)) h1
      rw [← hφapply r ⟨u, hu⟩]
      exact h2
    have hV : ∀ v, (r : V ≃ₗ[ZMod 3] V) v - v ∈ H :=
      ggQ2Sub_R_move A hTF c α hαc s hs hsR x hfix H le_rfl hHR hRx r r.2
    have hone := ggQ2Sub_eq_one A hTF c α hαc s hs (fun i => hRA (hsR i)) x hfix H le_rfl
      (hRA r.2) hU hV
    exact Subtype.ext (LinearEquiv.ext (fun v => by simpa using hone v))
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hφker
  let Rbar : Subgroup (H ≃ₗ[ZMod 3] H) := φ.range
  let φR : R →* Rbar :=
    { toFun := fun r => ⟨φ r, ⟨r, rfl⟩⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b) }
  have hφRinj : Function.Injective φR := by
    intro a b hab
    exact hφinj (congrArg (fun q : Rbar => q.val) hab)
  have hφRbij : Function.Bijective φR := by
    refine ⟨hφRinj, fun q => ?_⟩
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp (q : Rbar).2
    exact ⟨r, Subtype.ext hr⟩
  have hcardRbar : Nat.card Rbar = Nat.card R :=
    (Nat.card_congr (Equiv.ofBijective φR hφRbij)).symm
  have hgenRbar : Rbar = Subgroup.closure {q | q ∈ Rbar ∧ GGLinRefl q} := by
    refine le_antisymm ?_ ((Subgroup.closure_le Rbar).mpr (fun q hq => hq.1))
    set K : Set (V ≃ₗ[ZMod 3] V) := {t | t ∈ A ∧ IsReflLin t} with hKdef
    have hS : Subgroup.closure ((Subtype.val : R → V ≃ₗ[ZMod 3] V) ⁻¹' K) = (⊤ : Subgroup R) :=
      Subgroup.closure_closure_coe_preimage (k := K)
    have htop : Subgroup.map φ (⊤ : Subgroup R) = Rbar := by
      rw [Subgroup.map_top]
    have hmap : Subgroup.map φ (⊤ : Subgroup R) =
        Subgroup.closure (φ '' ((Subtype.val : R → V ≃ₗ[ZMod 3] V) ⁻¹' K)) := by
      rw [← hS, MonoidHom.map_closure]
    have hsub : Subgroup.closure (φ '' ((Subtype.val : R → V ≃ₗ[ZMod 3] V) ⁻¹' K)) ≤
        Subgroup.closure {q | q ∈ Rbar ∧ GGLinRefl q} := by
      refine Subgroup.closure_mono ?_
      rintro q ⟨r, hr, rfl⟩
      obtain ⟨htA, htRefl⟩ := hr
      obtain ⟨c₀, ψ, hψ, hEq⟩ := htRefl
      have htA' : Module.reflection hψ ∈ A := hEq ▸ htA
      have hc₀H : c₀ ∈ H :=
        ggQ2Sub_refl_centre A hTF c α hαc s hs hsR x hfix H le_rfl hHR hRx hψ htA'
      refine ⟨MonoidHom.mem_range.mpr ⟨r, rfl⟩, ?_⟩
      have hr' : (⟨Module.reflection hψ, hEq ▸ r.2⟩ : R) = r := Subtype.ext hEq.symm
      rw [← hr']
      exact l04fD2_restrict_refl (p := 3) (by decide) H
        ⟨Module.reflection hψ, hstab (hEq ▸ r.2)⟩ hc₀H hψ
        (fun v => Module.reflection_apply v hψ)
    intro x hx
    rw [← htop, hmap] at hx
    exact hsub hx
  let hbar : Fin m → H := fun i => ⟨c i, Submodule.subset_span ⟨i, rfl⟩⟩
  let αbar : Fin m → Module.Dual (ZMod 3) H := fun i => (α i).comp H.subtype
  let sbar : Fin m → (H ≃ₗ[ZMod 3] H) := fun i => φ ⟨s i, hsR i⟩
  have hsbar_apply : ∀ (i : Fin m) (v : H), sbar i v = v - αbar i v • hbar i := by
    intro i v
    apply Subtype.ext
    rw [hφapply, hs i (v : V)]
    simp [αbar, hbar]
  have hαbar : ∀ i, αbar i (hbar i) = 2 := by
    intro i
    show α i (c i) = 2
    exact hαc i
  have hspanH : Submodule.span (ZMod 3) (Set.range hbar) = ⊤ := by
    refine Submodule.map_injective_of_injective H.subtype_injective ?_
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
    have hrange : H.subtype '' Set.range hbar = Set.range c := by
      ext v
      constructor
      · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨hbar i, ⟨i, rfl⟩, rfl⟩
    rw [hrange]
  have hkerH : ∀ w : H, (∀ i, αbar i w = 0) → w = 0 := by
    intro w hw
    apply Subtype.ext
    exact hker (w : V) w.2 (fun i => hw i)
  have hconnH : ∀ i j, Relation.ReflTransGen
      (fun a b => αbar a (hbar b) ≠ 0 ∧ αbar b (hbar a) ≠ 0) i j :=
    hconn
  have habs_bar : ZS.AbsIrred 3 (Subgroup.closure (Set.range sbar)) :=
    ggRC_absIrred_of_connected (p := 3) (by decide) sbar hbar αbar hsbar_apply hαbar
      hspanH hkerH hconnH _ rfl
  have hle_bar : Subgroup.closure (Set.range sbar) ≤ Rbar :=
    (Subgroup.closure_le Rbar).mpr (fun q hq => by
      obtain ⟨i, rfl⟩ := hq
      exact ⟨⟨s i, hsR i⟩, rfl⟩)
  have habs : ZS.AbsIrred 3 Rbar := ggWAut_absIrred_of_le hle_bar habs_bar
  have hPle : Subgroup.closure (Set.range s) ≤ R :=
    (Subgroup.closure_le R).mpr (fun q hq => by
      obtain ⟨i, rfl⟩ := hq
      exact hsR i)
  have hPcard : Nat.card (Subgroup.closure (Set.range s)) = (m + 1).factorial :=
    l04fD5_P_card (p := 3) (by decide) (by omega) hpair s hs
  obtain ⟨ρ, -, hρmem, hρinj⟩ :=
    l04fD5_perm_embed (p := 3) (by decide) (m := m) (by omega) hpair s hs
  let ρR : Equiv.Perm (Fin (m + 1)) →* R :=
    { toFun := fun σ => ⟨ρ σ, hPle (hρmem σ)⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun a b => Subtype.ext (map_mul ρ a b) }
  have hρRinj : Function.Injective ρR := by
    intro a b hab
    exact hρinj (congrArg (fun q : R => q.val) hab)
  let ψ : Equiv.Perm (Fin (m + 1)) →* Rbar := φR.comp ρR
  have hψinj : Function.Injective ψ := hφRinj.comp hρRinj
  have hK' := hK 3 (by decide) H (m - 1) hH (by omega) Rbar habs hgenRbar
  rcases hK' with himp | ⟨-, hbound⟩ | ⟨-, hbound⟩ | ⟨-, e, -⟩ | ⟨-, e, -⟩
  ·
    exfalso
    obtain ⟨b, hmon⟩ := ggRC_monomial_of_imprimitive (p := 3) (n := m - 1) hH Rbar habs
      hgenRbar himp
    obtain ⟨π, -, -, hπcomm, -⟩ := ggRC_monomial_hom (p := 3) b Rbar hmon
    let π' : Equiv.Perm (Fin (m + 1)) →* Equiv.Perm (Fin (m - 1)) := π.comp ψ
    have hπ'comm : IsMulCommutative π'.ker := by
      rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      apply hψinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (isMulCommutative_iff.mp hπcomm
        ⟨ψ (a : Equiv.Perm (Fin (m + 1))), a.2⟩
        ⟨ψ (b : Equiv.Perm (Fin (m + 1))), b.2⟩)
    exact ggRC_perm_not_monomial (N := m + 1) (m := m - 1) (by omega) (by omega) π' hπ'comm
  ·
    exfalso
    exact ggQ2TNR_order_contra hm (by rw [hcardRbar]; exact (Subgroup.card_le_of_le hRA).trans hcard)
      hbound
  ·
    exfalso
    exact ggQ2TNR_order_contra hm (by rw [hcardRbar]; exact (Subgroup.card_le_of_le hRA).trans hcard)
      hbound
  ·
    exfalso
    have hcardRbar_m : Nat.card Rbar = m.factorial := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rw [show m - 1 + 1 = m by omega]
    have hle : (m + 1).factorial ≤ m.factorial := by
      rw [← hPcard, ← hcardRbar_m, hcardRbar]
      exact Subgroup.card_le_of_le hPle
    have hlt : m.factorial < (m + 1).factorial :=
      Nat.factorial_lt_of_lt (by omega) (by omega)
    omega
  ·
    exfalso
    have hcardRbar_perm : Nat.card Rbar = (m + 1).factorial := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rw [show m - 1 + 2 = m + 1 by omega]
    have hcardge : Nat.card R ≤ Nat.card (Subgroup.closure (Set.range s)) := by
      rw [← hcardRbar, hcardRbar_perm, ← hPcard]
    have hReq : Subgroup.closure (Set.range s) = R :=
      Subgroup.eq_of_le_of_card_ge hPle hcardge
    have hxfixall : ∀ r ∈ R, r x = x := by
      intro r hr
      rw [← hReq] at hr
      refine Subgroup.closure_induction (p := fun a _ => a x = x) ?_ ?_ ?_ ?_ hr
      · rintro t ⟨i, rfl⟩
        rw [hs i x, hxfix i, zero_smul, sub_zero]
      · rfl
      · intro a b _ _ iha ihb
        rw [LinearEquiv.mul_apply, ihb, iha]
      · intro a _ iha
        have h2 : a⁻¹ (a x) = x := by
          rw [← LinearEquiv.mul_apply, inv_mul_cancel]
          rfl
        rwa [iha] at h2
    exact hRx (fun r hr => by rw [hxfixall r hr]; exact Submodule.mem_span_singleton_self x)

end CFSG.StandardType

end
