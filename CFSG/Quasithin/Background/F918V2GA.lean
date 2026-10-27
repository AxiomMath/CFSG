module

public import CFSG.Quasithin.Background.F918N3
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.EmptyFaithful.S153ZP

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

namespace Z391

theorem v2ga_iso_pullback {A Q : Type*} [Group A] [CommGroup Q] [MulDistribMulAction A Q]
    {A₂ Q₂ : Type*} [Group A₂] [CommGroup Q₂] [MulDistribMulAction A₂ Q₂] {θ : Q →* Q₂}
    (hθ : Function.Injective θ) (hact : ∀ a : A, ∃ a₂ : A₂, ∀ x, θ (a • x) = a₂ • θ x)
    {L₁ L₂ : Subgroup Q} (h : XMod.Iso A₂ (L₁.map θ) (L₂.map θ)) : XMod.Iso A L₁ L₂ := by
  obtain ⟨φ, hφ⟩ := h
  let e₁ := Subgroup.equivMapOfInjective L₁ θ hθ
  let e₂ := Subgroup.equivMapOfInjective L₂ θ hθ
  refine ⟨e₁.trans (φ.trans e₂.symm), fun a l l' hll' => ?_⟩
  obtain ⟨a₂, ha₂⟩ := hact a
  have hx : ((e₁ l : ↥(L₁.map θ)) : Q₂) = θ (l : Q) :=
    Subgroup.coe_equivMapOfInjective_apply L₁ θ hθ l
  have hx' : ((e₁ l' : ↥(L₁.map θ)) : Q₂) = θ (l' : Q) :=
    Subgroup.coe_equivMapOfInjective_apply L₁ θ hθ l'
  have h1 : a₂ • ((e₁ l : ↥(L₁.map θ)) : Q₂) = ((e₁ l' : ↥(L₁.map θ)) : Q₂) := by
    rw [hx, hx', ← ha₂, hll']
  have h2 := hφ a₂ (e₁ l) (e₁ l') h1
  have k1 : θ ((e₂.symm (φ (e₁ l)) : ↥L₂) : Q) = ((φ (e₁ l) : ↥(L₂.map θ)) : Q₂) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply L₂ θ hθ, MulEquiv.apply_symm_apply]
  have k2 : θ ((e₂.symm (φ (e₁ l')) : ↥L₂) : Q) = ((φ (e₁ l') : ↥(L₂.map θ)) : Q₂) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply L₂ θ hθ, MulEquiv.apply_symm_apply]
  show a • ((e₂.symm (φ (e₁ l)) : ↥L₂) : Q) = ((e₂.symm (φ (e₁ l')) : ↥L₂) : Q)
  apply hθ
  rw [ha₂, k1, k2, h2]

variable {W : Type} [CommGroup W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}
  {Q : Type} [CommGroup Q] [MulDistribMulAction ↥M Q]

theorem v2g_smul_map (π : W →* Q)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (S : Subgroup W) (t : ↥M) :
    t • S.map π = (S.map (t : MulAut W).toMonoidHom).map π := by
  ext q
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨x, hx, hxq⟩
    refine ⟨(t : MulAut W) x, ⟨x, hx, rfl⟩, ?_⟩
    show π ((t : MulAut W) x) = q
    rw [← hπM, hxq, smul_inv_smul]
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    show π x = t⁻¹ • π ((t : MulAut W) x)
    rw [← hπM, inv_smul_smul]

theorem v2g_comm_map [Finite W] (hD : D3Std M L T L V) (m : MulAut W) (hm : m ∈ M) :
    commSub (V.map m.toMonoidHom) L = V.map m.toMonoidHom := by
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hLconj : L.map (MulAut.conj m).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hD.hyp.Mp_normal hm)
  have := commSub_map_conj m V L
  rw [hLconj, hVcomm] at this
  exact this

theorem v2g_stab_of_smul_eq [Finite W] (hD : D3Std M L T L V) (π : W →* Q)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (hker : π.ker = fixV L)
    (t : ↥M) (h : t • V.map π = V.map π) : (t : MulAut W) ∈ stabSub V := by
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  rw [v2g_smul_map π hπM] at h
  rw [mem_stabSub_iff_map_eq]
  have h1 : V.map (t : MulAut W).toMonoidHom ≤ V ⊔ fixV L := by
    intro x hx
    have : π x ∈ V.map π := by rw [← h]; exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := this
    refine Subgroup.mem_sup.2 ⟨y, hy, y⁻¹ * x, ?_, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have h3 : V.map (t : MulAut W).toMonoidHom ≤ V :=
    calc V.map (t : MulAut W).toMonoidHom
        = commSub (V.map (t : MulAut W).toMonoidHom) L := (v2g_comm_map hD _ t.2).symm
      _ ≤ commSub (V ⊔ fixV L) L := commSub_mono h1 le_rfl
      _ = commSub V L := commSub_sup_fixV le_rfl
      _ = V := hVcomm
  refine Subgroup.eq_of_le_of_card_ge h3 ?_
  rw [Subgroup.card_map_of_injective (t : MulAut W).injective]

variable [Finite W]

theorem v2g_noniso (hD : D3Std M L T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g) (π : W →* Q)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (hker : π.ker = fixV L)
    (t : ↥M) (htT : (t : MulAut W) ∈ T) (htV : (t : MulAut W) ∉ stabSub V) :
    ¬ XMod.Iso ↥(L.subgroupOf M) (V.map π) (t • V.map π) := by
  intro hiso
  have hZ := z35_of_d3Std hD hlt hC
  set VT : Subgroup W := orbSup T V with hVT
  set C : Subgroup W := VT ⊓ fixV L with hCdef
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hLst : L ≤ stabSub VT ⊓ stabSub C := n2_Mp_le hD
  have hTst : T ≤ stabSub VT ⊓ stabSub C := n2_T_le hD
  let θ : Sec VT C →* Q :=
    QuotientGroup.lift (C.subgroupOf VT) (π.comp VT.subtype) (fun x hx => by
      have h1 : (x : W) ∈ fixV L := (Subgroup.mem_subgroupOf.1 hx).2
      rw [← hker] at h1
      exact h1)
  have hθ : ∀ v : ↥VT, θ (QuotientGroup.mk v) = π (v : W) := fun v => rfl
  have hθinj : Function.Injective θ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [hθ, hθ] at hab
        rw [QuotientGroup.eq]
        refine ⟨(a⁻¹ * b).2, ?_⟩
        show ((a⁻¹ * b : ↥VT) : W) ∈ fixV L
        rw [← hker, MonoidHom.mem_ker, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hab,
          inv_mul_cancel]
  have hact : ∀ a : ↥(autSec L VT C), ∃ a₂ : ↥(L.subgroupOf M), ∀ x, θ (a • x) = a₂ • θ x := by
    intro a
    obtain ⟨g, hgL, hga⟩ := (n2_mem_autSec hLst).1 a.2
    refine ⟨⟨⟨(g : MulAut W), hLM hgL⟩, Subgroup.mem_subgroupOf.2 hgL⟩, fun x => ?_⟩
    induction x using QuotientGroup.induction_on with
    | H w =>
      have e : (a : MulAut (Sec VT C)) = n2Rho VT C g := hga.symm
      change θ ((a : MulAut (Sec VT C)) (QuotientGroup.mk w)) = _
      rw [e, n2Rho_mk, hθ, hθ]
      exact (hπM ⟨(g : MulAut W), hLM hgL⟩ (w : W)).symm
  have hmapθ : ∀ S : Subgroup W, S ≤ VT → (sec35Img VT C S).map θ = S.map π := by
    intro S hS
    unfold sec35Img
    rw [Subgroup.map_map]
    have e : θ.comp (QuotientGroup.mk' (C.subgroupOf VT)) = π.comp VT.subtype := by
      ext u
      rfl
    rw [e, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hS]
  set g₀ : ↥(stabSub VT ⊓ stabSub C) := ⟨(t : MulAut W), hTst htT⟩ with hg₀
  have htstar : n2Rho VT C g₀ ∈ autSec T VT C := (n2_mem_autSec hTst).2 ⟨g₀, htT, rfl⟩
  have hVb : (sec35Img VT C V).map θ = V.map π := hmapθ V (le_orbSup T V)
  have hVbt : ((sec35Img VT C V).map (n2Rho VT C g₀).toMonoidHom).map θ = t • V.map π := by
    rw [n2_map_rho_sec35Img, hmapθ _ (map_le_orbSup htT), v2g_smul_map π hπM]
  have e1 : (sec35Img VT C V).map (1 : MulAut (Sec VT C)).toMonoidHom = sec35Img VT C V := by
    ext x
    simp
  have hiso' : XMod.Iso ↥(autSec L VT C) ((sec35Img VT C V).map (1 : MulAut (Sec VT C)).toMonoidHom)
      ((sec35Img VT C V).map (n2Rho VT C g₀).toMonoidHom) := by
    rw [e1]
    refine v2ga_iso_pullback hθinj hact ?_
    rw [hVb, hVbt]
    exact hiso
  have hh := hZ.homog 1 (Subgroup.one_mem _) _ htstar hiso'
  have hh' : t • V.map π = V.map π := by
    have := congrArg (fun S : Subgroup (Sec VT C) => S.map θ) hh
    rw [e1, hVb, hVbt] at this
    exact this.symm
  exact htV (v2g_stab_of_smul_eq hD π hπM hker t hh')

end Z391

end CFSG.Quasithin
