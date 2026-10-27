module

public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.InternalSecAutOn

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

namespace B51

section Comm

variable {G : Type} [Group G] {L W : Subgroup G} [IsMulCommutative ↥W]

theorem map_commV_autOn (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    (commV (autOn L W)).map W.subtype = ⁅W, L⁆ :=
  CFSG.Quasithin.AutOn.map_commV_autOn_eq hLW

theorem commV_autOn (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    commV (autOn L W) = (⁅W, L⁆ : Subgroup G).subgroupOf W := by
  rw [← map_commV_autOn hLW, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective W.subtype_injective]

theorem fixV_autOn (hLW : L ≤ Subgroup.normalizer (W : Set G)) :
    fixV (autOn L W) = (Subgroup.centralizer (L : Set G)).subgroupOf W :=
  CFSG.Quasithin.AutOn.fixV_autOn_eq hLW

end Comm

section Res

variable {G : Type} [Group G] {L W U : Subgroup G}

theorem coe_autOnHom_apply (hLU : L ≤ Subgroup.normalizer (U : Set G)) (l : ↥L) (u : ↥U) :
    ((((autOnHom hLU l : ↥(autOn L U)) : MulAut ↥U) u : ↥U) : G) = l * u * (l : G)⁻¹ :=
  Setup.rho_apply_coe hLU l u

@[expose] noncomputable def resAutOn (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hUW : U ≤ W) :
    ↥(autOn L W) →* ↥(autOn L U) :=
  (QuotientGroup.lift (autOnHom hLW).ker (autOnHom hLU) (fun l hl =>
      (mem_ker_autOnHom hLU l).2
        (Subgroup.centralizer_le hUW ((mem_ker_autOnHom hLW l).1 hl)))).comp
    (QuotientGroup.quotientKerEquivOfSurjective (autOnHom hLW)
      (autOnHom_surjective hLW)).symm.toMonoidHom

variable (hLW : L ≤ Subgroup.normalizer (W : Set G)) (hLU : L ≤ Subgroup.normalizer (U : Set G))
  (hUW : U ≤ W)

theorem resAutOn_autOnHom (l : ↥L) :
    resAutOn hLW hLU hUW (autOnHom hLW l) = autOnHom hLU l := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (autOnHom hLW)
      (autOnHom_surjective hLW)).symm (autOnHom hLW l) = QuotientGroup.mk l := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [resAutOn, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h]
  rfl

theorem resAutOn_surjective : Function.Surjective (resAutOn hLW hLU hUW) := by
  intro y
  obtain ⟨l, rfl⟩ := autOnHom_surjective hLU y
  exact ⟨autOnHom hLW l, resAutOn_autOnHom hLW hLU hUW l⟩

theorem resAutOn_apply (σ : ↥(autOn L W)) (u : ↥U) :
    ((((resAutOn hLW hLU hUW σ : ↥(autOn L U)) : MulAut ↥U) u : ↥U) : G) =
      (((σ : MulAut ↥W) ⟨u, hUW u.2⟩ : ↥W) : G) := by
  obtain ⟨l, rfl⟩ := autOnHom_surjective hLW σ
  rw [resAutOn_autOnHom, coe_autOnHom_apply, coe_autOnHom_apply]

variable [IsMulCommutative ↥W] [IsMulCommutative ↥U]

theorem realizesVia_resAutOn {Z : Subgroup G} {D : FFModel} {π : D.Gam →* ↥(autOn L W)}
    (h : D.RealizesVia (autOn L W) (U.subgroupOf W) (Z.subgroupOf W) π) :
    D.RealizesVia (V := ↥U) (autOn L U) ⊤ (Z.subgroupOf U) ((resAutOn hLW hLU hUW).comp π) := by
  obtain ⟨hπ, -, hkS, hinvU, hinvZ, hsec, hker, β, hβs, hβk, hβe⟩ := h
  have hres := resAutOn_apply hLW hLU hUW
  have hρs := resAutOn_surjective hLW hLU hUW
  let e : ↥(⊤ : Subgroup ↥U) →* ↥(U.subgroupOf W) :=
    { toFun := fun x => ⟨⟨((x : ↥U) : G), hUW (x : ↥U).2⟩, (x : ↥U).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨hρs.comp hπ, le_top, hkS, fun _ _ _ => trivial, ?_, hsec, hker, β.comp e, ?_, ?_, ?_⟩
  · intro σ' z hz
    obtain ⟨σ, rfl⟩ := hρs σ'
    rw [Subgroup.mem_subgroupOf, hres]
    exact hinvZ σ ⟨z, hUW z.2⟩ hz
  · intro y
    obtain ⟨u, rfl⟩ := hβs y
    exact ⟨⟨⟨((u : ↥W) : G), u.2⟩, trivial⟩, rfl⟩
  · intro u
    exact hβk (e u)
  · intro γ u m hu hm hum
    have hu' := hinvU (π γ) (e u) (e u).2
    have key : e ⟨(((resAutOn hLW hLU hUW).comp π γ : ↥(autOn L U)) : MulAut ↥U) (u : ↥U), hu⟩ =
        ⟨((π γ : ↥(autOn L W)) : MulAut ↥W) (e u : ↥W), hu'⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      exact hres (π γ) u
    show β (e _) = _
    rw [key]
    exact hβe γ (e u) m hu' hm hum

include hLW hLU hUW in
theorem binaryNaturalSL_res {Z : Subgroup G} {d a : ℕ}
    (h : BinaryNaturalSL (autOn L W) (U.subgroupOf W) (Z.subgroupOf W) d a) :
    BinaryNaturalSL (V := ↥U) (autOn L U) ⊤ (Z.subgroupOf U) d a := by
  obtain ⟨K, hK1, hK2, hK, π, hπ⟩ := h
  exact ⟨K, hK1, hK2, hK, _, realizesVia_resAutOn hLW hLU hUW hπ⟩

include hLW hLU hUW in
theorem binaryNaturalSp4_res {Z : Subgroup G} {a : ℕ}
    (h : BinaryNaturalSp4 (autOn L W) (U.subgroupOf W) (Z.subgroupOf W) a) :
    BinaryNaturalSp4 (V := ↥U) (autOn L U) ⊤ (Z.subgroupOf U) a := by
  obtain ⟨K, hK1, hK2, hK, π, hπ⟩ := h
  exact ⟨K, hK1, hK2, hK, _, realizesVia_resAutOn hLW hLU hUW hπ⟩

include hLW hLU hUW in
theorem g2Natural_res {Z : Subgroup G} {a : ℕ}
    (h : G2Natural (autOn L W) (U.subgroupOf W) (Z.subgroupOf W) a) :
    G2Natural (V := ↥U) (autOn L U) ⊤ (Z.subgroupOf U) a := by
  obtain ⟨K, hK1, hK2, hK, π, hπ⟩ := h
  exact ⟨K, hK1, hK2, hK, _, realizesVia_resAutOn hLW hLU hUW hπ⟩

end Res

section Inv

variable {G : Type} [Group G] {L W : Subgroup G}

theorem le_normalizer_map_of_inv (hLW : L ≤ Subgroup.normalizer (W : Set G)) {J : Subgroup ↥W}
    (hJ : ∀ σ ∈ autOn L W, ∀ u ∈ J, σ u ∈ J) :
    L ≤ Subgroup.normalizer ((J.map W.subtype : Subgroup G) : Set G) := by
  have key : ∀ l ∈ L, ∀ x ∈ J.map W.subtype, l * x * l⁻¹ ∈ J.map W.subtype := by
    rintro l hl _ ⟨w, hw, rfl⟩
    refine ⟨_, hJ _ (conjAct_mem_autOn hLW hl) w hw, ?_⟩
    show ((conjAct W ⟨l, hLW hl⟩ w : ↥W) : G) = l * (w : G) * l⁻¹
    rw [coe_conjAct_apply]
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key l hl x hx, fun hx => ?_⟩
  have := key l⁻¹ (L.inv_mem hl) _ hx
  simpa [mul_assoc] using this

end Inv

end B51

end CFSG.Quasithin.Vol2.Ch11.SecC
