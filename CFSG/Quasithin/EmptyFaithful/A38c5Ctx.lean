module

public import CFSG.Quasithin.EmptyFaithful.A38c5Core
public import CFSG.Quasithin.EmptyFaithful.A38c5Ker
public import CFSG.Quasithin.EmptyFaithful.S153H32
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

namespace CFSG.Quasithin.A38c5

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem isElemAbelian_of_le' {E X : Subgroup G} (hE : IsElemAbelian 2 E) (hXE : X ≤ E) :
    IsElemAbelian 2 X := CFSG.Open.IsElemAbelian.mono hE hXE

omit [Finite G] in
theorem mem_normalizer_commutator' {A B : Subgroup G} {s : G}
    (hA : s ∈ Subgroup.normalizer (A : Set G)) (hB : s ∈ Subgroup.normalizer (B : Set G)) :
    s ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem omegaOneCenter_le_S (h : Hyp15310 G T Mc M V₁ V₂ Yp t) :
    quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
  unfold quasithinOmegaOneCenter
  refine Subgroup.closure_mono fun z hz => ?_
  have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
  exact ⟨⟨S153D.VZ_le_Sgp153 h hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩

theorem commutator_eq_top_of_mulEquiv {G₁ G₂ : Type*} [Group G₁] [Group G₂] (e : G₁ ≃* G₂)
    (h : commutator G₁ = ⊤) : commutator G₂ = ⊤ := by
  have hs : (⊤ : Subgroup G₁).map e.toMonoidHom = ⊤ := Subgroup.map_top_of_surjective _ e.surjective
  have h1 : (commutator G₁).map e.toMonoidHom = commutator G₂ := by
    show (⁅(⊤ : Subgroup G₁), (⊤ : Subgroup G₁)⁆ : Subgroup G₁).map e.toMonoidHom =
      ⁅(⊤ : Subgroup G₂), (⊤ : Subgroup G₂)⁆
    rw [Subgroup.map_commutator, hs]
  rw [← h1, h, hs]

omit [Finite G] in
theorem commutator_subgroup_eq_map {H : Subgroup G} :
    ⁅H, H⁆ = (commutator ↥H).map H.subtype := by
  have h1 : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  show ⁅H, H⁆ = (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ : Subgroup ↥H).map H.subtype
  rw [Subgroup.map_commutator, h1]

theorem core_of_ctx (hFM : FiniteFactS8)
    (hPre : Preamble32 T V₁ I L) (c : Ctx15332 T Mc M V₁ V₂ Yp I L t)
    (cc : Concl15332 T M V₁ I L) {t' : G} (ht'T : t' ∈ T) (ht'S : t' ∉ Sgp153 T V₁)
    {A : Subgroup G} (hA : IsMaxElemAbelian (Sgp153 T V₁) A)
    (hstrong : cm3 (UL153 T I L) A <
      rk ↥A - rk ↥(A ⊓ Subgroup.centralizer ((UL153 T I L : Subgroup G) : Set G))) :
    cm1 (P153 T M V₁) (UL153 T I L) A + 1 = cm3 (UL153 T I L) A := by
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  obtain ⟨hLc, -, -, -, hStarQ, -⟩ := c25.conc
  have hLI : L ≤ I := (le_of_mem_cComp hLc).trans (thompsonJ_le_self I)
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  obtain ⟨hle, hel⟩ := conjClosure_le_centerOf_pCoreOf_of_sylowIn hsyl.1 hsyl.2.1 hsyl.2.2
    c25.ctx.charTwo (omegaOneCenter_le_S hyp)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUIpc : UI153 T I ≤ pCoreOf 2 I := hle.trans inf_le_left
  have hUIc : pCoreOf 2 I ≤ Subgroup.centralizer (UI153 T I : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hle hu).2 x hx).symm
  have hUUI : UL153 T I L ≤ UI153 T I :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := L) (K := UI153 T I)).mp (hLI.trans hIU)
  have hUe : IsElemAbelian 2 (UL153 T I L) := isElemAbelian_of_le' hel hUUI
  have hUS : UL153 T I L ≤ Sgp153 T V₁ := hUUI.trans (hUIpc.trans (S153D.pCoreOf_le_Sgp153' hF))
  have hIN : I ≤ Subgroup.normalizer (UL153 T I L : Set G) := fun i hi =>
    mem_normalizer_commutator' (hIU hi) (hIL hi)
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (UL153 T I L : Set G) := fun s hs => hIN (hSI hs)
  obtain ⟨-, hb, hc⟩ := hPre
  have hCS : I ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ Sgp153 T V₁ :=
    hc.le.trans inf_le_left
  have hC2 : IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (UL153 T I L : Set G)) := by
    rw [← hb]
    exact pCoreOf_isPGroup 2 I
  have hker : I ⊓ Subgroup.centralizer (UI153 T I : Set G) =
      I ⊓ Subgroup.centralizer (UL153 T I L : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le hUUI)
    · refine le_inf inf_le_left ?_
      intro x hx
      rw [← hb] at hx
      exact hUIc hx
  obtain ⟨q, hq, hnd, ⟨E, hE, hEq⟩, hcard, hort⟩ := cc.orthogonal
  obtain ⟨K, hKL, hKmax, hSK, hX⟩ := cc.X_eq
  have hKI : K ≤ I := hKL.trans hLI
  let f₁ := convHom (V := UI153 T I) hel I hIU
  let f₂ := convHom (V := UL153 T I L) hUe I hIN
  have hk : f₁.ker = f₂.ker := by
    rw [ker_convHom, ker_convHom, hker]
  have e₁L : autI hel L = (L.subgroupOf I).map f₁ := autI_eq_map_convHom hel hIU hLI
  have e₁K : autI hel K = (K.subgroupOf I).map f₁ := autI_eq_map_convHom hel hIU hKI
  have e₂L : autI hUe L = (L.subgroupOf I).map f₂ := autI_eq_map_convHom hUe hIN hLI
  have e₂K : autI hUe K = (K.subgroupOf I).map f₂ := autI_eq_map_convHom hUe hIN hKI
  have hmax₂ : IsMaxParabolic2 (autI hUe L) (autI hUe K) := by
    rw [e₂L, e₂K]
    refine (isMaxParabolic2_map_iff_of_ker_eq f₁ f₂ hk _ _).1 ?_
    rw [← e₁L, ← e₁K]
    exact hKmax
  obtain ⟨eiso⟩ := nonempty_mulEquiv_map_of_ker_eq f₁ f₂ hk (L.subgroupOf I)
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
  have hPsplit := (cc.P_split t' ht'T ht'S).1
  have hPS : P153 T M V₁ ≤ Sgp153 T V₁ := by
    show pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁) ≤ _
    rw [hPsplit]
    exact sup_le inf_le_left inf_le_left
  have hSCP : Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G) ≤ P153 T M V₁ := by
    show _ ≤ pCoreOf 2 (X153 T M V₁ ⊔ Sgp153 T V₁)
    rw [hPsplit]
    exact le_sup_left
  exact core_abstract hFM hUe hSN hIN hsyl hCS hC2 hUS q hq hnd E hE hEq hcard hort hLI hIL hLp hL1
    hKL hmax₂ hSK hX rfl hPS hSCP hA hstrong

end Context

end CFSG.Quasithin.A38c5
