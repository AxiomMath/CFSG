module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155Act
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Ker
import CFSG.RankThree.PartTwo.Sec15.Sylow155Gen
import CFSG.RankThree.PartTwo.Sec15.Gagen155W315PBasic
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Sylow155B1

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sylow155B2

open Sylow155R

section Trivial

variable {W K : Subgroup G} [(K.subgroupOf W).Normal]

omit [Finite G] in
theorem qAct_eq_one (g : ↥(nWK W K)) (hg : ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ * w⁻¹ ∈ K) :
    qAct W K g = 1 := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H z =>
    rw [qAct_mk, MulAut.one_apply]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have h := hg (z : G)⁻¹ (W.inv_mem z.2)
    have e : (((conjW W K g z)⁻¹ * z : ↥W) : G) =
        (g : G) * (z : G)⁻¹ * (g : G)⁻¹ * ((z : G)⁻¹)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjW_apply]
      group
    rw [e]
    exact h

variable {n : ℕ} (φ : ↥W ⧸ K.subgroupOf W ≃* alternatingGroup (Fin n))
  (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))

omit [Finite G] in
theorem rho_eq_one (g : ↥(nWK W K)) (hg : ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ * w⁻¹ ∈ K) :
    rho φ autE g = 1 := by
  rw [rho, MonoidHom.comp_apply, MonoidHom.comp_apply, qAct_eq_one g hg, map_one, map_one]

omit [Finite G] in
theorem rho_eq_rho_of_forall (hWK : W ≤ Subgroup.normalizer (K : Set G)) (g : ↥(nWK W K))
    {y : G} (hy : y ∈ W) (hg : ∀ w ∈ W, (y⁻¹ * g) * w * (y⁻¹ * g)⁻¹ * w⁻¹ ∈ K) :
    rho φ autE g = rho φ autE ⟨y, mem_nWK hWK hy⟩ := by
  have h1 := rho_eq_one φ autE ((⟨y, mem_nWK hWK hy⟩ : ↥(nWK W K))⁻¹ * g) hg
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

end Trivial

theorem w155_le_m (A M X : Subgroup G) : w155 A M X ≤ M :=
  (Proof155Wx.w155_le_u155 A M X).trans (Sylow155B1.u155_le.trans inf_le_left)

theorem w155_le_normalizer (A M X : Subgroup G) :
    w155 A M X ≤ Subgroup.normalizer (pPrimeCoreOf 3 M : Set G) :=
  (w155_le_m A M X).trans (le_normalizer_pPrimeCoreOf 3 M)

theorem le_nWK {A M X H : Subgroup G} (hHM : H ≤ M)
    (hHΔ : H ≤ Subgroup.normalizer (delta A (lB A) M : Set G))
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ nWK (w155 A M X) (pPrimeCoreOf 3 M) :=
  le_inf (Proof155Wx.le_normalizer_w155 hHΔ hHX) (hHM.trans (le_normalizer_pPrimeCoreOf 3 M))

theorem u155_le_nWK (A M X : Subgroup G) : u155 A M X ≤ nWK (w155 A M X) (pPrimeCoreOf 3 M) :=
  le_nWK (Sylow155B1.u155_le.trans inf_le_left) (inf_le_left.trans Subgroup.le_normalizer)
    (Sylow155B1.u155_le.trans inf_le_right)

theorem delta_le_nWK {A M X : Subgroup G}
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G)) :
    delta A (lB A) M ≤ nWK (w155 A M X) (pPrimeCoreOf 3 M) :=
  le_nWK (delta_le M) Subgroup.le_normalizer hIX

theorem a_le_nWK {A X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    A ≤ nWK (w155 A M X) (pPrimeCoreOf 3 M) :=
  le_nWK (fun a ha => hC.mem_m.2 (le_sup_left (b := Y) ha)) (le_normalizer_delta M)
    (Sylow155B1.le_normalizer_x hC)

section Kernel

variable {A M X : Subgroup G} [((pPrimeCoreOf 3 M).subgroupOf (w155 A M X)).Normal] {n : ℕ}
  (φ : ↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X) ≃* alternatingGroup (Fin n))
  (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))

theorem rho_eq_one_of_mem_x {Y P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P)
    (hX : X ∈ thetaComponentsIn M) {x : G} (hx : x ∈ X)
    (hxn : x ∈ nWK (w155 A M X) (pPrimeCoreOf 3 M)) : rho φ autE ⟨x, hxn⟩ = 1 := by
  refine rho_eq_one φ autE _ fun w hw => ?_
  have h1 : ⁅w, x⁆ ∈ CFSG.Open.pCoreOf 2 M :=
    Proof155P.commutator_w155_le hf hX (Subgroup.commutator_mem_commutator hw hx)
  have h2 := Sec17.Proof17Q0.pCoreOf_le_pPrimeCoreOf M ((CFSG.Open.pCoreOf 2 M).inv_mem h1)
  rw [commutatorElement_inv, commutatorElement_def] at h2
  exact h2

theorem mem_pPrimeCoreOf_u155_of_rho_eq_one (hautE : ∀ σ, autE σ = MulAut.conjNormal σ) {w : G}
    (hw : w ∈ w155 A M X)
    (hρ : rho φ autE ⟨w, mem_nWK (w155_le_normalizer A M X) hw⟩ = 1) :
    w ∈ pPrimeCoreOf 3 (u155 A M X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hwK := (rho_eq_one_iff φ autE hautE (w155_le_normalizer A M X) w hw).mp hρ
  have hle : w155 A M X ⊓ pPrimeCoreOf 3 M ≤ pPrimeCoreOf 3 (u155 A M X) :=
    le_pPrimeCoreOf (inf_le_left.trans (Proof155Wx.w155_le_u155 A M X))
      ((u155_le_nWK A M X).trans Subgroup.inf_normalizer_le_normalizer_inf)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (coprime_card_pPrimeCoreOf 3 M))
  exact hle ⟨hw, hwK⟩

theorem ker_central (hautE : ∀ σ, autE σ = MulAut.conjNormal σ) {Y P : Subgroup G}
    (hf : Proof155Wx.Facts155W A X Y M P) (hX : X ∈ thetaComponentsIn M)
    (hBXW : b155 A M X ≤ X ⊔ w155 A M X) {k : G} (hk : k ∈ u155 A M X)
    (hρ : rho φ autE ⟨k, u155_le_nWK A M X hk⟩ = 1) :
    (∀ u ∈ u155 A M X, k * u * k⁻¹ * u⁻¹ ∈ pPrimeCoreOf 3 (u155 A M X)) ∧
      ∃ m : ℕ, k ^ 3 ^ m ∈ pPrimeCoreOf 3 (u155 A M X) :=
  Sylow155K.ker_central_u155 hBXW ((rho φ autE).comp (Subgroup.inclusion (u155_le_nWK A M X)))
    (fun _ hx _ => rho_eq_one_of_mem_x φ autE hf hX hx _)
    (fun _ hw hρw => mem_pPrimeCoreOf_u155_of_rho_eq_one φ autE hautE hw hρw) hk hρ

end Kernel

section Criterion

variable {A X K Y M T P : Subgroup G} [((pPrimeCoreOf 3 M).subgroupOf (w155 A M X)).Normal]
  {n : ℕ}
  (φ : ↥(w155 A M X) ⧸ (pPrimeCoreOf 3 M).subgroupOf (w155 A M X) ≃* alternatingGroup (Fin n))
  (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))

noncomputable abbrev rhoR (Y : Subgroup G) : Subgroup (Perm (Fin n)) :=
  ((CFSG.Open.pCoreOf 2 Y).subgroupOf (nWK (w155 A M X) (pPrimeCoreOf 3 M))).map (rho φ autE)

theorem conj_mem_sup (hautE : ∀ σ, autE σ = MulAut.conjNormal σ) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hf : Proof155Wx.Facts155W A X Y M P) (hBXW : b155 A M X ≤ X ⊔ w155 A M X) {g : G}
    (hgI : g ∈ delta A (lB A) M)
    (hgR : rho φ autE ⟨g, delta_le_nWK hIX hgI⟩ ∈
      Subgroup.normalizer (rhoR φ autE Y : Set (Perm (Fin n))))
    {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) :
    g * x * g⁻¹ ∈ CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := u155 A M X with hUdef
  set R := CFSG.Open.pCoreOf 2 Y with hRdef
  have hX : X ∈ thetaComponentsIn M := hE.mem_x
  have hRU : R ≤ U := Sylow155F.r_le_u155 hE hRP
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hgU : g ∈ Subgroup.normalizer (U : Set G) :=
    Sylow155B1.le_normalizer_u155 Subgroup.le_normalizer hIX hgI
  have hgU0 : g ∈ Subgroup.normalizer (pPrimeCoreOf 3 U : Set G) :=
    normalizer_le_normalizer_pPrimeCoreOf 3 U hgU
  have h2pow : ∀ r ∈ R, ∃ m : ℕ, r ^ 2 ^ m = 1 := by
    intro r hr
    obtain ⟨m, hm⟩ := hR2 ⟨r, hr⟩
    have h := congrArg Subtype.val hm
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    exact ⟨m, h⟩
  suffices hle : R ⊔ pPrimeCoreOf 3 U ≤
      (R ⊔ pPrimeCoreOf 3 U).comap (MulAut.conj g).toMonoidHom from hle hx
  refine sup_le (fun r hr => ?_) (fun y hy => ?_)
  ·
    change g * r * g⁻¹ ∈ R ⊔ pPrimeCoreOf 3 U
    have hrU := hRU hr
    have hgr : g * r * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hgU r).mp hrU
    have hρr : rho φ autE ⟨r, u155_le_nWK A M X hrU⟩ ∈ rhoR φ autE Y :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hr)
    have hρ := (Subgroup.mem_normalizer_iff.mp hgR _).mp hρr
    obtain ⟨r'', hr'', hρr''⟩ := Subgroup.mem_map.mp hρ
    rw [Subgroup.mem_subgroupOf] at hr''
    set r' : G := (r'' : G) with hr'def
    have hr'U : r' ∈ U := hRU hr''
    have hkU : r'⁻¹ * (g * r * g⁻¹) ∈ U := U.mul_mem (U.inv_mem hr'U) hgr
    have hρk : rho φ autE ⟨r'⁻¹ * (g * r * g⁻¹), u155_le_nWK A M X hkU⟩ = 1 := by
      have e : (⟨r'⁻¹ * (g * r * g⁻¹), u155_le_nWK A M X hkU⟩ :
          ↥(nWK (w155 A M X) (pPrimeCoreOf 3 M))) =
          r''⁻¹ * ((⟨g, delta_le_nWK hIX hgI⟩ : ↥(nWK (w155 A M X) (pPrimeCoreOf 3 M))) *
            ⟨r, u155_le_nWK A M X hrU⟩ * (⟨g, delta_le_nWK hIX hgI⟩)⁻¹) :=
        Subtype.ext rfl
      rw [e, map_mul, map_inv, map_mul, map_mul, map_inv, hρr'', inv_mul_cancel]
    obtain ⟨hcen, m, hm⟩ := ker_central φ autE hautE hf hX hBXW hkU hρk
    have hrc : r' * (r'⁻¹ * (g * r * g⁻¹)) * r'⁻¹ * (r'⁻¹ * (g * r * g⁻¹))⁻¹ ∈
        pPrimeCoreOf 3 U := by
      have h := (pPrimeCoreOf 3 U).inv_mem (hcen r' hr'U)
      have e : r' * (r'⁻¹ * (g * r * g⁻¹)) * r'⁻¹ * (r'⁻¹ * (g * r * g⁻¹))⁻¹ =
          ((r'⁻¹ * (g * r * g⁻¹)) * r' * (r'⁻¹ * (g * r * g⁻¹))⁻¹ * r'⁻¹)⁻¹ := by group
      rw [e]
      exact h
    have hrc2 : ∃ m : ℕ, (r' * (r'⁻¹ * (g * r * g⁻¹))) ^ 2 ^ m = 1 := by
      obtain ⟨m', hm'⟩ := h2pow r hr
      refine ⟨m', ?_⟩
      rw [mul_inv_cancel_left, conj_pow, hm', mul_one, mul_inv_cancel]
    have hk0 := Sylow155G.mem_of_mul_pow_two (le_normalizer_pPrimeCoreOf 3 U) hr'U hkU hrc
      (h2pow r' hr'') ⟨m, hm⟩ hrc2
    have e : g * r * g⁻¹ = r' * (r'⁻¹ * (g * r * g⁻¹)) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hr'' hk0
  · change g * y * g⁻¹ ∈ R ⊔ pPrimeCoreOf 3 U
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hgU0 y).mp hy)

theorem mem_normalizer_sup (hautE : ∀ σ, autE σ = MulAut.conjNormal σ)
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hf : Proof155Wx.Facts155W A X Y M P) (hBXW : b155 A M X ≤ X ⊔ w155 A M X) {g : G}
    (hgI : g ∈ delta A (lB A) M)
    (hgR : rho φ autE ⟨g, delta_le_nWK hIX hgI⟩ ∈
      Subgroup.normalizer (rhoR φ autE Y : Set (Perm (Fin n)))) :
    g ∈ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X) : Subgroup G) : Set G) := by
  have hgI' : g⁻¹ ∈ delta A (lB A) M := (delta A (lB A) M).inv_mem hgI
  have hgR' : rho φ autE ⟨g⁻¹, delta_le_nWK hIX hgI'⟩ ∈
      Subgroup.normalizer (rhoR φ autE Y : Set (Perm (Fin n))) := by
    have e : (⟨g⁻¹, delta_le_nWK hIX hgI'⟩ : ↥(nWK (w155 A M X) (pPrimeCoreOf 3 M))) =
        (⟨g, delta_le_nWK hIX hgI⟩)⁻¹ := Subtype.ext rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ hgR
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · exact conj_mem_sup φ autE hautE hE hRP hIX hf hBXW hgI hgR hx
  · have h := conj_mem_sup φ autE hautE hE hRP hIX hf hBXW hgI' hgR' hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at h

end Criterion

end Sylow155B2

end CFSG.RankThree.PartTwo.Sec15
