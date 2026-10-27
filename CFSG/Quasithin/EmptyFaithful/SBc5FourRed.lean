module

public import CFSG.Quasithin.EmptyFaithful.SBd2Two
public import CFSG.Quasithin.EmptyFaithful.A38c5Ker
public import CFSG.Quasithin.EmptyFaithful.A38c5Aut
public import CFSG.Quasithin.EmptyFaithful.SBc5OrthDefs
public import CFSG.Quasithin.EmptyFaithful.SBc5Common

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc5

section Generic

variable {G : Type} [Group G]

theorem X153_eq_oPrimeResidualOf_inf {T M V₁ L : Subgroup G} (h3 : Clause32Three T M V₁ L) :
    X153 T M V₁ = oPrimeResidualOf 3 (L ⊓ Subgroup.centralizer (ZS153 T M V₁ : Set G)) := by
  have hZ1 : ZS153 T M V₁ ⊓ V₁ ≤ ZS153 T M V₁ := inf_le_left
  show oPrimeResidualOf 3 (Subgroup.centralizer (ZS153 T M V₁ : Set G)) = _
  unfold oPrimeResidualOf
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    have hx1 : x ∈ Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le (fun a ha => hZ1 ha) hx
    have hxL : x ∈ L := by
      rw [h3]
      exact Subgroup.subset_closure ⟨hx1, k, hk⟩
    exact ⟨⟨hxL, hx⟩, k, hk⟩
  · rintro ⟨⟨_, hx⟩, k, hk⟩
    exact ⟨hx, k, hk⟩

end Generic

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input32Four_of_residue (h113 : StageLemma14113) (hPre : Input32Preamble)
    (hres : OrthoFixedParabolic) : Input32Four := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c h1 h3
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hh : Hyp153 G T Mc M := hyp.hyp
  have Dc : Decomp153 T M V₁ V₂ t := hyp.decomp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  obtain ⟨hLc, -, -, -, hStarQ, -⟩ := c25.conc
  have hLI : L ≤ I := (le_of_mem_cComp hLc).trans (thompsonJ_le_self I)
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  obtain ⟨-, hb, hc⟩ := hPre G T Mc M V₁ V₂ Yp I L t c
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo (omegaOneCenter_le_Sgp hyp)
  have hUIpc : UI153 T I ≤ pCoreOf 2 I := hle.trans inf_le_left
  have hUIc : pCoreOf 2 I ≤ Subgroup.centralizer (UI153 T I : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hle hu).2 x hx).symm
  have hUUI : UL153 T I L ≤ UI153 T I :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := L) (K := UI153 T I)).mp (hLI.trans hIU)
  have hUe : IsElemAbelian 2 (UL153 T I L) := SBc.isElemAbelian_UL c
  have hIN : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := S153H.I_le_normalizer_UL c
  have hCS : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ Sgp153 T V₁ := hc.le.trans inf_le_left
  have hker : I ⊓ Subgroup.centralizer (UI153 T I : Set G) =
      I ⊓ Subgroup.centralizer (UL153 T I L : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le hUUI)
    · refine le_inf inf_le_left ?_
      intro x hx
      rw [← hb] at hx
      exact hUIc hx
  obtain ⟨a₁, a₂, ha₁V, ha₂V, -, ha₂1, hZS, -⟩ := SBd2.exists_ZS_basis hh Dc
  have ha₂U : a₂ ∈ UL153 T I L := SBc.V₂_le_UL h113 c ha₂V
  have ha₁ZS : a₁ ∈ ZS153 T M V₁ := (hZS a₁).2 (Or.inr (Or.inl rfl))
  have ha₂ZS : a₂ ∈ ZS153 T M V₁ := (hZS a₂).2 (Or.inr (Or.inr (Or.inl rfl)))
  have ha₂S : a₂ ∈ Subgroup.centralizer (Sgp153 T V₁ : Set G) := ha₂ZS.2
  have hLC : L ≤ Subgroup.centralizer ((ZS153 T M V₁ ⊓ V₁ : Subgroup G) : Set G) :=
    h3.le.trans (oPrimeResidualOf_le 3 _)
  have hLa₁ : ∀ l ∈ L, a₁ * l = l * a₁ := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hLC hl) a₁ ⟨ha₁ZS, ha₁V⟩
  set K : Subgroup G := L ⊓ Subgroup.centralizer (ZS153 T M V₁ : Set G) with hKdef
  have hKL : K ≤ L := inf_le_left
  have hKI : K ≤ I := hKL.trans hLI
  have hX : X153 T M V₁ = oPrimeResidualOf 3 K := X153_eq_oPrimeResidualOf_inf h3
  have hSK : Sgp153 T V₁ ≤ Subgroup.normalizer (K : Set G) := by
    intro s hs
    have hsC : s ∈ Subgroup.centralizer (ZS153 T M V₁ : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (Subgroup.mem_centralizer_iff.mp hz.2 s hs).symm
    have hsN : s ∈ Subgroup.normalizer
        (Subgroup.centralizer (ZS153 T M V₁ : Set G) : Set G) :=
      B2F.le_normalizer_centralizer (S := Subgroup.centralizer (ZS153 T M V₁ : Set G))
        (V := ZS153 T M V₁) (Subgroup.centralizer_le_normalizer _) hsC
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hIL (hSI hs), hsN⟩
  let f₁ := convHom (V := UI153 T I) hel I hIU
  let f₂ := convHom (V := UL153 T I L) hUe I hIN
  have hk : f₁.ker = f₂.ker := by rw [ker_convHom, ker_convHom, hker]
  have e₁L : autI hel L = (L.subgroupOf I).map f₁ := autI_eq_map_convHom hel hIU hLI
  have e₁K : autI hel K = (K.subgroupOf I).map f₁ := autI_eq_map_convHom hel hIU hKI
  have e₂L : autI hUe L = (L.subgroupOf I).map f₂ := autI_eq_map_convHom hUe hIN hLI
  have e₂K : autI hUe K = (K.subgroupOf I).map f₂ := autI_eq_map_convHom hUe hIN hKI
  obtain ⟨eiso⟩ := A38c5.nonempty_mulEquiv_map_of_ker_eq f₁ f₂ hk (L.subgroupOf I)
  let e' : ↥(autI hel L) ≃* ↥(autI hUe L) :=
    (MulEquiv.subgroupCongr e₁L).trans (eiso.trans (MulEquiv.subgroupCongr e₂L.symm))
  have hcomm₂ : commutator ↥(autI hUe L) = ⊤ :=
    commutator_eq_top_of_mulEquiv e' hStarQ.1.commutator_eq_top
  have hnt : Nontrivial ↥(autI hUe L) := by
    obtain ⟨-, -, a, b, hab⟩ := hStarQ
    have h1 : Nontrivial ↥(autI hel L) := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have hss : Subsingleton ↥(autOn L (UI153 T I)) := h
      exact hab (by rw [Subsingleton.elim a b])
    exact e'.injective.nontrivial
  have hLp : ⁅autI hUe L, autI hUe L⁆ = autI hUe L := by
    rw [commutator_subgroup_eq_map, hcomm₂, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hL1 : autI hUe L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 hnt
  obtain ⟨q, hq, hnd, ⟨E, hE, hEq⟩, hcard, hort⟩ := h1
  have hort' : autI hUe I = orthogonalGroupOf q := hort
  have hS₀ : IsSylowTwoOf (autI hUe (Sgp153 T V₁)) (orthogonalGroupOf q) :=
    hort' ▸ A38c5.isSylowTwoOf_autI hUe hsyl hIN hCS
  have hLΩ : autI hUe L ≤ orthogonalGroupOf q := hort' ▸ autI_mono hUe hLI
  have hLn : ((autI hUe L).subgroupOf (orthogonalGroupOf q)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨l, hl, hlx⟩ := (mem_autI hUe).1 hx
    have hg : (g : MulAut (IntMod (UL153 T I L) hUe)) ∈ autI hUe I := by
      rw [hort']
      exact g.2
    obtain ⟨i, hi, hig⟩ := (mem_autI hUe).1 hg
    have hil : (i : G) * l * (i : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hIL hi) l).1 hl
    have key : convI hUe (i * l * i⁻¹) =
        (g : MulAut (IntMod (UL153 T I L) hUe)) * x *
          (g : MulAut (IntMod (UL153 T I L) hUe))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hig, hlx]
    show (g : MulAut (IntMod (UL153 T I L) hUe)) * x *
      (g : MulAut (IntMod (UL153 T I L) hUe))⁻¹ ∈ autI hUe L
    rw [← key]
    exact convI_mem_autI hUe hil (i * l * i⁻¹).2
  set a : IntMod (UL153 T I L) hUe := IntMod.mk hUe ⟨a₂, ha₂U⟩ with ha
  have hav : a.val = a₂ := rfl
  have ha1 : a ≠ 1 := fun h => ha₂1 (by rw [← hav, h]; rfl)
  have hfixS : ∀ g ∈ autI hUe (Sgp153 T V₁), g a = a := by
    intro g hg
    obtain ⟨s, hs, rfl⟩ := (mem_autI hUe).1 hg
    refine IntMod.val_injective ?_
    rw [convI_apply_val, hav]
    have := Subgroup.mem_centralizer_iff.mp ha₂S (s : G) hs
    rw [this]
    group
  have hres' := hres (IntMod (UL153 T I L) hUe) IntMod.sq_eq_one q hq hnd E hE hEq hcard
    (autI hUe (Sgp153 T V₁)) (autI hUe L) hS₀ hLΩ hLn hLp hL1 a ha1 hfixS
  have hKstab : autI hUe K = autI hUe L ⊓ MulAction.stabilizer (MulAut (IntMod (UL153 T I L) hUe)) a := by
    ext φ
    rw [Subgroup.mem_inf]
    constructor
    · intro hφ
      refine ⟨autI_mono hUe hKL hφ, ?_⟩
      obtain ⟨g, hgK, rfl⟩ := (mem_autI hUe).1 hφ
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      refine IntMod.val_injective ?_
      rw [convI_apply_val, hav]
      have := Subgroup.mem_centralizer_iff.mp hgK.2 a₂ ha₂ZS
      rw [← this]
      group
    · rintro ⟨hφL, hφa⟩
      obtain ⟨g, hgL, rfl⟩ := (mem_autI hUe).1 hφL
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hφa
      have h2 := congrArg IntMod.val hφa
      rw [convI_apply_val, hav] at h2
      have hga₂ : a₂ * (g : G) = (g : G) * a₂ := by
        have : (g : G) * a₂ * (g : G)⁻¹ = a₂ := h2
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this.symm
      refine (mem_autI hUe).2 ⟨g, ⟨hgL, ?_⟩, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rcases (hZS z).mp hz with rfl | rfl | rfl | rfl
      · simp
      · exact hLa₁ _ hgL
      · exact hga₂
      · calc a₁ * a₂ * (g : G) = a₁ * (a₂ * (g : G)) := by group
          _ = a₁ * ((g : G) * a₂) := by rw [hga₂]
          _ = (a₁ * (g : G)) * a₂ := by group
          _ = ((g : G) * a₁) * a₂ := by rw [hLa₁ _ hgL]
          _ = (g : G) * (a₁ * a₂) := by group
  have hmax₂ : IsMaxParabolic2 (autI hUe L) (autI hUe K) := by
    rw [hKstab]
    exact hres'
  have hmax₁ : IsMaxParabolic2 (autI hel L) (autI hel K) := by
    rw [e₁L, e₁K]
    refine (A38c5.isMaxParabolic2_map_iff_of_ker_eq f₁ f₂ hk _ _).2 ?_
    rw [← e₂L, ← e₂K]
    exact hmax₂
  exact ⟨K, hKL, hmax₁, hSK, hX⟩

end Context

end SBc5

end CFSG.Quasithin
