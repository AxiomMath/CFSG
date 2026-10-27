module

public import CFSG.Quasithin.H13.A6S13824a
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Rep
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3E
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C1PackC129Case
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Background.SmithB42Alt6Conj
public import CFSG.Quasithin.Background.SmithB45Alt6
public import CFSG.Quasithin.EmptyFaithful.S14113bMain
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.H13.A5Quad
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S1523
public import CFSG.Quasithin.H13.A5Sit15d
public import CFSG.Quasithin.H13.A6S13816b
public import CFSG.Quasithin.H13.A6S13826f
public import CFSG.Quasithin.H13.A6S13826g
public import CFSG.Quasithin.H13.A6S13827a
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Red
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Red
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
public import CFSG.Walter.J1
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem exists_alpha7 (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hKH : K ≤ H) (h7 : IsAlt 7 ↥(S.KSt H K)) :
    ∃ α : ↥K →* alternatingGroup (Fin 7), Function.Surjective α ∧
      ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  obtain ⟨ι⟩ := h7
  have hF1 := (hS.hF H hH).toHypF91
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF1.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF1.isElemAbelian_tilde⟩
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, actH hV₁ hIH x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF1.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hKst : S.KSt H K = (K.subgroupOf H).map (actH hV₁ hIH) :=
    autOn_tilde_eq_map_actH hV₁ hIH hKH
  let f : ↥K →* ↥(S.KSt H K) := ((actH hV₁ hIH).comp (Subgroup.inclusion hKH)).codRestrict _
    fun k => by
      rw [hKst]
      exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
  have hfs : Function.Surjective f := by
    rintro ⟨ψ, hψ⟩
    rw [hKst] at hψ
    obtain ⟨x, hx, rfl⟩ := hψ
    exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  refine ⟨ι.toMonoidHom.comp f, ι.surjective.comp hfs, fun k => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    ← Subtype.coe_inj]
  exact hker _

namespace DK

variable {S} {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem conj_mem (h : ↥H) (k : ↥K) : (h : G) * k * (h : G)⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp (hd.hKn h.2) k).mp k.2

theorem exists_conjHom {A : Type*} [Group A] {α : ↥K →* A} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    ∃ φ : ↥H →* MulAut A, ∀ (h : ↥H) (k : ↥K),
      φ h (α k) = α ⟨(h : G) * k * (h : G)⁻¹, hd.conj_mem h k⟩ := by
  let c : ↥H → ↥K →* ↥K := fun h =>
    { toFun := fun k => ⟨(h : G) * k * (h : G)⁻¹, hd.conj_mem h k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hc : ∀ (h : ↥H) (k : ↥K), ((c h k : ↥K) : G) = (h : G) * k * (h : G)⁻¹ := fun _ _ => rfl
  have hker : ∀ h : ↥H, α.ker ≤ (α.comp (c h)).ker := by
    intro h k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [MonoidHom.comp_apply, hαk, hc]
    have hq := (hαk k).1 hk
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H h.2) _).mp hq
  let f : ↥H → A →* A := fun h => α.liftOfSurjective hαs ⟨α.comp (c h), hker h⟩
  have hf : ∀ (h : ↥H) (k : ↥K), f h (α k) = α (c h k) := fun h k =>
    MonoidHom.liftOfRightInverse_comp_apply α _ _ ⟨α.comp (c h), hker h⟩ k
  have hfmul : ∀ h₁ h₂ : ↥H, ∀ a : A, f (h₁ * h₂) a = f h₁ (f h₂ a) := by
    intro h₁ h₂ a
    obtain ⟨k, rfl⟩ := hαs a
    rw [hf, hf, hf]
    congr 1
    apply Subtype.ext
    simp only [hc, Subgroup.coe_mul, mul_inv_rev]
    group
  have hfone : ∀ a : A, f 1 a = a := by
    intro a
    obtain ⟨k, rfl⟩ := hαs a
    rw [hf]
    congr 1
    apply Subtype.ext
    simp [hc]
  let φ : ↥H →* MulAut A :=
    { toFun := fun h =>
        { toFun := f h
          invFun := f h⁻¹
          left_inv := fun a => by rw [← hfmul, inv_mul_cancel, hfone]
          right_inv := fun a => by rw [← hfmul, mul_inv_cancel, hfone]
          map_mul' := map_mul (f h) }
      map_one' := MulEquiv.ext hfone
      map_mul' := fun h₁ h₂ => MulEquiv.ext (hfmul h₁ h₂) }
  exact ⟨φ, fun h k => hf h k⟩

theorem exists_rho7 {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) :
    ∃ ρ : ↥H →* Perm (Fin 7),
      (∀ (h : ↥H) (k : ↥K), ((α ⟨(h : G) * k * (h : G)⁻¹, hd.conj_mem h k⟩ :
          alternatingGroup (Fin 7)) : Perm (Fin 7)) = ρ h * α k * (ρ h)⁻¹) ∧
      (∀ k : ↥K, ρ ⟨(k : G), hd.hKH k.2⟩ = (α k : Perm (Fin 7))) ∧
      ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H := by
  obtain ⟨φ, hφ⟩ := hd.exists_conjHom hαs hαk
  let ρ : ↥H →* Perm (Fin 7) := L246A7.autA7.symm.toMonoidHom.comp φ
  have hρ : ∀ (h : ↥H) (a : alternatingGroup (Fin 7)),
      ((φ h a : alternatingGroup (Fin 7)) : Perm (Fin 7)) = ρ h * a * (ρ h)⁻¹ := by
    intro h a
    have h1 : L246A7.autA7 (ρ h) = φ h := L246A7.autA7.apply_symm_apply (φ h)
    rw [← h1, L246A7.autA7_apply]
  have hconj : ∀ (h : ↥H) (k : ↥K), ((α ⟨(h : G) * k * (h : G)⁻¹, hd.conj_mem h k⟩ :
      alternatingGroup (Fin 7)) : Perm (Fin 7)) = ρ h * α k * (ρ h)⁻¹ := fun h k => by
    rw [← hφ h k, hρ]
  refine ⟨ρ, hconj, fun k => ?_, fun h => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  ·
    apply L246A7.centerless
    intro a
    obtain ⟨k', rfl⟩ := hαs a
    rw [← hconj]
    have e : (⟨(⟨(k : G), hd.hKH k.2⟩ : ↥H) * (k' : G) * ((⟨(k : G), hd.hKH k.2⟩ : ↥H) : G)⁻¹,
        hd.conj_mem _ k'⟩ : ↥K) = k * k' * k⁻¹ := Subtype.ext (by simp)
    rw [e, map_mul, map_mul, map_inv]
    simp
  ·
    refine S.mem_pCoreOf_of_comm hd.hS hd.hH hd.hKH hd.hKn hd.hHK hd.hsimp hd.hnab h.2
      fun k hk => ?_
    have h2 := hconj h ⟨k, hk⟩
    rw [h1, one_mul, inv_one, mul_one] at h2
    have h3 : α (⟨(h : G) * k * (h : G)⁻¹, hd.conj_mem h ⟨k, hk⟩⟩ * (⟨k, hk⟩ : ↥K)⁻¹) = 1 := by
      rw [map_mul, map_inv, mul_inv_eq_one]
      exact Subtype.ext h2
    rw [hαk] at h3
    simpa using h3
  ·
    apply L246A7.centerless
    intro a
    obtain ⟨k, rfl⟩ := hαs a
    rw [← hconj]
    simp only [one_mul, inv_one, mul_one]
    have h2 : α (⟨(h : G) * k * (h : G)⁻¹, hd.conj_mem h k⟩ * k⁻¹) = 1 := by
      rw [hαk]
      have hq : (h : G) * k * (h : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 H := by
        have hk' : (k : G) * (h : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 H :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hd.hKH k.2)) _).mp
            ((pCoreOf 2 H).inv_mem h1)
        have e : (h : G) * k * (h : G)⁻¹ * (k : G)⁻¹ = (h : G) * ((k : G) * (h : G)⁻¹ * (k : G)⁻¹) :=
          by group
        rw [e]
        exact (pCoreOf 2 H).mul_mem h1 hk'
      simpa using hq
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    rw [h2]

end DK

end Setting4

end CFSG.Quasithin.H13.A6
