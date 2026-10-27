module

public import CFSG.Quasithin.EmptyFaithful.A38c6Model
public import CFSG.Quasithin.EmptyFaithful.A38c6Klein
public import CFSG.Quasithin.EmptyFaithful.S153GCountIneq

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A38c5 CFSG.Quasithin.A38c5.Fm
open scoped commutatorElement

namespace CFSG.Quasithin.A38c6

section Side

variable {G : Type} [Group G] [Finite G]

structure CoreHyp153 (U S I L K X P : Subgroup G) : Prop where
  hV : IsElemAbelian 2 U
  hSN : S ≤ Subgroup.normalizer (U : Set G)
  hIN : I ≤ Subgroup.normalizer (U : Set G)
  hsyl : IsSylowTwoOf S I
  hCS : I ⊓ Subgroup.centralizer (U : Set G) ≤ S
  hC2 : IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (U : Set G))
  hUS : U ≤ S
  hLI : L ≤ I
  hIL : I ≤ Subgroup.normalizer (L : Set G)
  hKL : K ≤ L
  hSK : S ≤ Subgroup.normalizer (K : Set G)
  hX : X = oPrimeResidualOf 3 K
  hP : P = pCoreOf 2 (X ⊔ S)
  hPS : P ≤ S
  hSCP : S ⊓ Subgroup.centralizer (U : Set G) ≤ P
  quad : ∃ (q : IntMod U hV → ZMod 2), IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧
    (∃ E : Subgroup (IntMod U hV), Nat.card E = 2 ^ 3 ∧ ∀ e ∈ E, q e = 0) ∧
    Nat.card (IntMod U hV) = 2 ^ 6 ∧ autI hV I = orthogonalGroupOf q
  hLp : ⁅autI hV L, autI hV L⁆ = autI hV L
  hL1 : autI hV L ≠ ⊥
  hKmax : IsMaxParabolic2 (autI hV L) (autI hV K)


theorem coreHyp_of_ctx {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (hPre : Preamble32 T V₁ I L) (c : Ctx15332 T Mc M V₁ V₂ Yp I L t)
    (cc : Concl15332 T M V₁ I L) :
    ∃ K : Subgroup G, CoreHyp153 (UL153 T I L) (Sgp153 T V₁) I L K (X153 T M V₁) (P153 T M V₁) := by
  obtain ⟨t', ht'T, ht'S⟩ := exists_mem_T_not_mem_S c
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
  exact ⟨K, hUe, hSN, hIN, hsyl, hCS, hC2, hUS, hLI, hIL, hKL, hSK, hX, rfl, hPS, hSCP,
    ⟨q, hq, hnd, ⟨E, hE, hEq⟩, hcard, hort⟩, hLp, hL1, hmax₂⟩


omit [Finite G] in
theorem le_of_autI_le {U S K K' : Subgroup G} (hV : IsElemAbelian 2 U)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hKS : K ≤ S) (hK'S : K' ≤ S)
    (hC : S ⊓ Subgroup.centralizer (U : Set G) ≤ K') (h : autI hV K ≤ autI hV K') : K ≤ K' := by
  intro k hk
  have hkN : k ∈ Subgroup.normalizer (U : Set G) := hSN (hKS hk)
  have h1 : convI hV ⟨k, hkN⟩ ∈ autI hV K' := h (convI_mem_autI hV hk hkN)
  obtain ⟨g, hg, hgk⟩ := (mem_autI hV).1 h1
  have h2 : convI hV (⟨k, hkN⟩ * g⁻¹) = 1 := by rw [map_mul, map_inv, ← hgk, mul_inv_cancel]
  have h3 : k * (g : G)⁻¹ ∈ Subgroup.centralizer (U : Set G) := (convI_eq_one_iff hV _).1 h2
  have h4 : k * (g : G)⁻¹ ∈ K' := hC ⟨S.mul_mem (hKS hk) (S.inv_mem (hK'S hg)), h3⟩
  have := K'.mul_mem h4 hg
  simpa using this

omit [Finite G] in
theorem eq_of_autI_eq {U S K K' : Subgroup G} (hV : IsElemAbelian 2 U)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hKS : K ≤ S) (hK'S : K' ≤ S)
    (hC : S ⊓ Subgroup.centralizer (U : Set G) ≤ K) (hC' : S ⊓ Subgroup.centralizer (U : Set G) ≤ K')
    (h : autI hV K = autI hV K') : K = K' :=
  le_antisymm (le_of_autI_le hV hSN hKS hK'S hC' h.le) (le_of_autI_le hV hSN hK'S hKS hC h.ge)

omit [Finite G] in
theorem mem_S0_of_convI_mem {U S I L : Subgroup G} (hV : IsElemAbelian 2 U)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hLI : L ≤ I) (hSI : S ≤ I) (hIeq : I = L ⊔ S)
    (hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer (U : Set G)) {a : G} (haS : a ∈ S)
    (h : convI hV ⟨a, hSN haS⟩ ∈ autI hV L) : a ∈ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)) := by
  refine ⟨haS, ?_⟩
  obtain ⟨l, hl, hla⟩ := (mem_autI hV).1 h
  have h2 : convI hV (⟨a, hSN haS⟩ * l⁻¹) = 1 := by rw [map_mul, map_inv, ← hla, mul_inv_cancel]
  have h3 : a * (l : G)⁻¹ ∈ Subgroup.centralizer (U : Set G) := (convI_eq_one_iff hV _).1 h2
  have h4 : a * (l : G)⁻¹ ∈ I ⊓ Subgroup.centralizer (U : Set G) :=
    ⟨I.mul_mem (hSI haS) (I.inv_mem (hLI hl)), h3⟩
  have h5 : a * (l : G)⁻¹ ∈ pCoreOf 2 (L ⊔ S) := by
    rw [← hIeq, hb]
    exact h4
  have h6 : a = (a * (l : G)⁻¹) * l := by group
  rw [h6]
  exact (L ⊔ pCoreOf 2 (L ⊔ S)).mul_mem (Subgroup.mem_sup_right h5) (Subgroup.mem_sup_left hl)


omit [Finite G] in
theorem le_S0_of_autI_le {U S I L : Subgroup G} (hV : IsElemAbelian 2 U)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hLI : L ≤ I) (hSI : S ≤ I) (hIeq : I = L ⊔ S)
    (hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer (U : Set G)) {A : Subgroup G} (hAS : A ≤ S)
    (h : autI hV A ≤ autI hV L) : A ≤ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)) :=
  fun _ ha => mem_S0_of_convI_mem hV hSN hLI hSI hIeq hb (hAS ha)
    (h (convI_mem_autI hV ha (hSN (hAS ha))))

omit [Finite G] in
theorem autI_le_of_le_S0 {U S I L : Subgroup G} (hV : IsElemAbelian 2 U)
    (hIN : I ≤ Subgroup.normalizer (U : Set G)) (hLI : L ≤ I) (hIeq : I = L ⊔ S)
    (hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer (U : Set G)) {A : Subgroup G}
    (h : A ≤ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S))) : autI hV A ≤ autI hV L := by
  have hPc : pCoreOf 2 (L ⊔ S) = I ⊓ Subgroup.centralizer (U : Set G) := by rw [← hIeq, hb]
  have h1 : A ≤ L ⊔ (I ⊓ Subgroup.centralizer (U : Set G)) := fun a ha => by
    have := (h ha).2
    rwa [hPc] at this
  calc autI hV A ≤ autI hV (L ⊔ (I ⊓ Subgroup.centralizer (U : Set G))) := autI_mono hV h1
    _ = autI hV L ⊔ autI hV (I ⊓ Subgroup.centralizer (U : Set G)) :=
        autI_sup hV (hLI.trans hIN) (inf_le_left.trans hIN)
    _ = autI hV L := by
        rw [autI_eq_bot_of_le_centralizer hV inf_le_right, sup_bot_eq]

omit [Finite G] in
theorem autI_S0_eq {U S I L : Subgroup G} (hV : IsElemAbelian 2 U)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hIN : I ≤ Subgroup.normalizer (U : Set G))
    (hLI : L ≤ I) (hSI : S ≤ I) (hIeq : I = L ⊔ S)
    (hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer (U : Set G)) :
    autI hV (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S))) = autI hV S ⊓ autI hV L := by
  apply le_antisymm
  · exact le_inf (autI_mono hV inf_le_left) (autI_le_of_le_S0 hV hIN hLI hIeq hb le_rfl)
  · intro φ hφ
    obtain ⟨hφS, hφL⟩ := hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφS
    exact convI_mem_autI hV (mem_S0_of_convI_mem hV hSN hLI hSI hIeq hb hg hφL) g.2

theorem autI_P_eq {U S I L K X P : Subgroup G} (hV : IsElemAbelian 2 U)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hIN : I ≤ Subgroup.normalizer (U : Set G))
    (hsyl : IsSylowTwoOf S I) (hC2 : IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (U : Set G)))
    (hLI : L ≤ I) (hKL : K ≤ L) (hX : X = oPrimeResidualOf 3 K) (hP : P = pCoreOf 2 (X ⊔ S)) :
    autI hV P = pCoreOf 2 (oPrimeResidualOf 3 (autI hV K) ⊔ autI hV S) := by
  have hSI : S ≤ I := hsyl.1
  have hKI : K ≤ I := hKL.trans hLI
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := hKI.trans hIN
  have hXK : X ≤ K := by
    rw [hX]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hXN : X ≤ Subgroup.normalizer (U : Set G) := hXK.trans hKN
  have hXSI : X ⊔ S ≤ I := sup_le (hXK.trans hKI) hSI
  have hXSN : X ⊔ S ≤ Subgroup.normalizer (U : Set G) := hXSI.trans hIN
  have hC2' : IsPGroup 2 ↥((X ⊔ S) ⊓ Subgroup.centralizer (U : Set G)) :=
    hC2.to_le (inf_le_inf_right _ hXSI)
  rw [hP, autI_pCoreOf hV hXSN hC2', autI_sup hV hXN hSN, hX, autI_oPrimeResidualOf hV hKN]


omit [Finite G] in
theorem exists_mul_of_mem_sup_of_normalizes' {E A : Subgroup G}
    (hEA : ∀ e ∈ E, ∀ x ∈ A, e * x * e⁻¹ ∈ A) {y : G} (hy : y ∈ E ⊔ A) :
    ∃ e ∈ E, ∃ x ∈ A, y = e * x := by
  let M : Subgroup G :=
    { carrier := {y | ∃ e ∈ E, ∃ x ∈ A, y = e * x}
      one_mem' := ⟨1, E.one_mem, 1, A.one_mem, by rw [one_mul]⟩
      mul_mem' := by
        rintro _ _ ⟨e₁, he₁, x₁, hx₁, rfl⟩ ⟨e₂, he₂, x₂, hx₂, rfl⟩
        refine ⟨e₁ * e₂, E.mul_mem he₁ he₂, e₂⁻¹ * x₁ * e₂⁻¹⁻¹ * x₂,
          A.mul_mem (hEA e₂⁻¹ (E.inv_mem he₂) x₁ hx₁) hx₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨e, he, x, hx, rfl⟩
        refine ⟨e⁻¹, E.inv_mem he, e * x⁻¹ * e⁻¹, hEA e he x⁻¹ (A.inv_mem hx), ?_⟩
        group }
  have hle : E ⊔ A ≤ M := sup_le (fun e he => ⟨e, he, 1, A.one_mem, by rw [mul_one]⟩)
    (fun x hx => ⟨1, E.one_mem, x, hx, by rw [one_mul]⟩)
  exact hle hy

theorem card_autI_cjSub {U S P M : Subgroup G} {t' : G} (hV : IsElemAbelian 2 U)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hSCP : S ⊓ Subgroup.centralizer (U : Set G) ≤ P)
    (ht'S : cjSub t' S = S) (ht'P : cjSub t' P = P) (hPM : P ≤ M) (hMS : M ≤ S) :
    Nat.card ↥(autI hV (cjSub t' M)) = Nat.card ↥(autI hV M) := by
  have hM2S : cjSub t' M ≤ S := by
    have := cjSub_mono (g := t') hMS
    rwa [ht'S] at this
  have hPM2 : P ≤ cjSub t' M := by
    have := cjSub_mono (g := t') hPM
    rwa [ht'P] at this
  have hinf2 : cjSub t' M ⊓ Subgroup.centralizer (U : Set G) =
      S ⊓ Subgroup.centralizer (U : Set G) :=
    le_antisymm (inf_le_inf_right _ hM2S) (le_inf (hSCP.trans hPM2) inf_le_right)
  have hinf1 : M ⊓ Subgroup.centralizer (U : Set G) = S ⊓ Subgroup.centralizer (U : Set G) :=
    le_antisymm (inf_le_inf_right _ hMS) (le_inf (hSCP.trans hPM) inf_le_right)
  have h1 := card_autI_mul_card_inf hV (hM2S.trans hSN)
  have h2 := card_autI_mul_card_inf hV (hMS.trans hSN)
  rw [hinf2, card_cjSub] at h1
  rw [hinf1] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(S ⊓ Subgroup.centralizer (U : Set G)))) (h1.trans h2.symm)


theorem side_numbers_aux {U S I L K X P A : Subgroup G} (hV : IsElemAbelian 2 U)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hIN : I ≤ Subgroup.normalizer (U : Set G))
    (hsyl : IsSylowTwoOf S I) (hC2 : IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (U : Set G)))
    (hLI : L ≤ I) (hKL : K ≤ L) (hX : X = oPrimeResidualOf 3 K) (hP : P = pCoreOf 2 (X ⊔ S))
    (hPS : P ≤ S) (hSCP : S ⊓ Subgroup.centralizer (U : Set G) ≤ P)
    (hA : IsMaxElemAbelian S A) :
    cm3 U A = rkIdx (fixV (autI hV A)) ∧
      cm1 P U A = rk ↥(autI hV A ⊓ pCoreOf 2 (oPrimeResidualOf 3 (autI hV K) ⊔ autI hV S)) ∧
      cm0 P A = rk ↥(autI hV A) -
        rk ↥(autI hV A ⊓ pCoreOf 2 (oPrimeResidualOf 3 (autI hV K) ⊔ autI hV S)) := by
  have hAS : A ≤ S := hA.1
  have hAN : A ≤ Subgroup.normalizer (U : Set G) := hAS.trans hSN
  have hSI : S ≤ I := hsyl.1
  have hKI : K ≤ I := hKL.trans hLI
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := hKI.trans hIN
  have hXK : X ≤ K := by
    rw [hX]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hXN : X ≤ Subgroup.normalizer (U : Set G) := hXK.trans hKN
  have hXSI : X ⊔ S ≤ I := sup_le (hXK.trans hKI) hSI
  have hXSN : X ⊔ S ≤ Subgroup.normalizer (U : Set G) := hXSI.trans hIN
  have hC2' : IsPGroup 2 ↥((X ⊔ S) ⊓ Subgroup.centralizer (U : Set G)) :=
    hC2.to_le (inf_le_inf_right _ hXSI)
  have hautP : autI hV P = pCoreOf 2 (oPrimeResidualOf 3 (autI hV K) ⊔ autI hV S) := by
    rw [hP, autI_pCoreOf hV hXSN hC2', autI_sup hV hXN hSN, hX, autI_oPrimeResidualOf hV hKN]
  have e3 : cm3 U A = rkIdx (fixV (autI hV A)) := (rkIdx_fixV_autI hV hAN).symm
  have hinf := autI_inf_eq hV hAS hPS hSCP
  have h1 := rk_autI_add hV (le_trans inf_le_left hAN : A ⊓ P ≤ Subgroup.normalizer (U : Set G))
  have hA1 := rk_autI_add hV hAN
  have hCeq : A ⊓ P ⊓ Subgroup.centralizer (U : Set G) = A ⊓ Subgroup.centralizer (U : Set G) := by
    refine le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) fun x hx => ⟨⟨hx.1, hSCP ⟨hAS hx.1, hx.2⟩⟩, hx.2⟩
  rw [hinf, hautP, hCeq] at h1
  refine ⟨e3, ?_, ?_⟩
  · unfold cm1
    rw [hCeq]
    omega
  · unfold cm0
    omega


theorem strong_abstract {U S I L K X P A : Subgroup G}
    (hc : CoreHyp153 U S I L K X P) (hIeq : I = L ⊔ S)
    (hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer (U : Set G))
    (hA : IsMaxElemAbelian S A) (hAnot : ¬ A ≤ Subgroup.centralizer (U : Set G))
    (hstrong : rAV (autI hc.hV A) < 1) :
    cm3 U A = 3 ∧ cm1 P U A = 2 ∧ cm0 P A = 2 ∧ ¬ A ≤ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)) := by
  obtain ⟨hV, hSN, hIN, hsyl, hCS, hC2, hUS, hLI, hIL, hKL, hSK, hX, hP, hPS, hSCP,
    ⟨q, hq, hnd, ⟨E, hE, hEq⟩, hcard, hort⟩, hLp, hL1, hKmax⟩ := hc
  obtain ⟨e3, e1, e0⟩ := side_numbers_aux hV hSN hIN hsyl hC2 hLI hKL hX hP hPS hSCP hA
  have hW : ∀ w : IntMod U hV, w ^ 2 = 1 := IntMod.sq_eq_one
  have hFF : IsFFStarOffender (autI hV S) (autI hV A) :=
    offenderImages_isFFStarOffender hV hUS hSN
      (show autI hV A ∈ offenderImages hV S from ⟨A, ⟨hA, hAnot⟩, rfl⟩)
  have hS₀ : IsSylowTwoOf (autI hV S) (orthogonalGroupOf q) :=
    hort ▸ isSylowTwoOf_autI hV hsyl hIN hCS
  have hLΩ : autI hV L ≤ orthogonalGroupOf q := hort ▸ autI_mono hV hLI
  have hLn : ((autI hV L).subgroupOf (orthogonalGroupOf q)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨l, hl, hlx⟩ := (mem_autI hV).1 hx
    have hg : (g : MulAut (IntMod U hV)) ∈ autI hV I := by
      rw [hort]
      exact g.2
    obtain ⟨i, hi, hig⟩ := (mem_autI hV).1 hg
    have hil : (i : G) * l * (i : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hIL hi) l).1 hl
    have key : convI hV (i * l * i⁻¹) =
        (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hig, hlx]
    show (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ ∈ autI hV L
    rw [← key]
    exact convI_mem_autI hV hil (i * l * i⁻¹).2
  have hSKa := autI_le_normalizer hV hSK
  obtain ⟨h3, h2, h4, h5⟩ := strong_data' hW q hq hnd E hE hEq hcard hS₀ hLΩ hLn hLp hL1 hKmax
    hSKa ⟨hFF, hstrong⟩
  refine ⟨by rw [e3]; exact h3, by rw [e1]; exact h2, by rw [e0, h4, h2], ?_⟩
  intro h
  apply h5
  exact autI_le_of_le_S0 hV hIN hLI hIeq hb h

theorem side_abstract {U S I L K X P A : Subgroup G}
    (hc : CoreHyp153 U S I L K X P) (hIeq : I = L ⊔ S)
    (hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer (U : Set G))
    (hA : IsMaxElemAbelian S A) (hAnot : ¬ A ≤ Subgroup.centralizer (U : Set G))
    (hmin : ∀ B : Subgroup G, IsMaxElemAbelian S B → ¬ B ≤ Subgroup.centralizer (U : Set G) →
      autOn B U ≤ autOn A U → autOn B U = autOn A U) :
    ¬ A ≤ P ∧ cm1 P U A + 1 = cm3 U A ∧
      (cm0 P A = 1 ∨ (cm0 P A = 2 ∧ cm3 U A = 3 ∧ cm1 P U A = 2 ∧
        ¬ A ≤ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)))) := by
  obtain ⟨hV, hSN, hIN, hsyl, hCS, hC2, hUS, hLI, hIL, hKL, hSK, hX, hP, hPS, hSCP,
    ⟨q, hq, hnd, ⟨E, hE, hEq⟩, hcard, hort⟩, hLp, hL1, hKmax⟩ := hc
  obtain ⟨e3, e1, e0⟩ := side_numbers_aux hV hSN hIN hsyl hC2 hLI hKL hX hP hPS hSCP hA
  have hW : ∀ w : IntMod U hV, w ^ 2 = 1 := IntMod.sq_eq_one
  have hAS : A ≤ S := hA.1
  have hAN : A ≤ Subgroup.normalizer (U : Set G) := hAS.trans hSN
  have hFF : IsFFStarOffender (autI hV S) (autI hV A) :=
    offenderImages_isFFStarOffender hV hUS hSN
      (show autI hV A ∈ offenderImages hV S from ⟨A, ⟨hA, hAnot⟩, rfl⟩)
  have hS₀ : IsSylowTwoOf (autI hV S) (orthogonalGroupOf q) :=
    hort ▸ isSylowTwoOf_autI hV hsyl hIN hCS
  have hLΩ : autI hV L ≤ orthogonalGroupOf q := hort ▸ autI_mono hV hLI
  have hLn : ((autI hV L).subgroupOf (orthogonalGroupOf q)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨l, hl, hlx⟩ := (mem_autI hV).1 hx
    have hg : (g : MulAut (IntMod U hV)) ∈ autI hV I := by
      rw [hort]
      exact g.2
    obtain ⟨i, hi, hig⟩ := (mem_autI hV).1 hg
    have hil : (i : G) * l * (i : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hIL hi) l).1 hl
    have key : convI hV (i * l * i⁻¹) =
        (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hig, hlx]
    show (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ ∈ autI hV L
    rw [← key]
    exact convI_mem_autI hV hil (i * l * i⁻¹).2
  have hSKa := autI_le_normalizer hV hSK
  have hnotP : ∀ k : ℕ, cm0 P A = k → 0 < k → ¬ A ≤ P := by
    intro k hk hk0 hle
    have : cm0 P A = 0 := by
      unfold cm0
      rw [inf_eq_left.2 hle, Nat.sub_self]
    omega
  by_cases hstrong : rAV (autI hV A) < 1
  · obtain ⟨h3, h2, h4, h5⟩ := strong_data' hW q hq hnd E hE hEq hcard hS₀ hLΩ hLn hLp hL1 hKmax
      hSKa ⟨hFF, hstrong⟩
    have hc3 : cm3 U A = 3 := by rw [e3]; exact h3
    have hc1 : cm1 P U A = 2 := by rw [e1]; exact h2
    have hc0 : cm0 P A = 2 := by rw [e0, h4, h2]
    refine ⟨hnotP 2 hc0 (by norm_num), by omega, Or.inr ⟨hc0, hc3, hc1, ?_⟩⟩
    intro h
    apply h5
    have h1 : A ≤ L ⊔ (I ⊓ Subgroup.centralizer (U : Set G)) := fun a ha => by
      have := (h ha).2
      rwa [← hIeq, hb] at this
    calc autI hV A ≤ autI hV (L ⊔ (I ⊓ Subgroup.centralizer (U : Set G))) := autI_mono hV h1
      _ = autI hV L ⊔ autI hV (I ⊓ Subgroup.centralizer (U : Set G)) :=
          autI_sup hV (hLI.trans hIN) (inf_le_left.trans hIN)
      _ = autI hV L := by
          rw [autI_eq_bot_of_le_centralizer hV inf_le_right, sup_bot_eq]
  · have hmin' : ∀ B₀ : Subgroup (MulAut (IntMod U hV)), B₀ ≤ autI hV A →
        IsFFStarOffender (autI hV S) B₀ → B₀ = autI hV A := by
      intro B₀ hBA hB₀
      obtain ⟨D, hD, hDB⟩ := B2_9_1 hV hUS hSN (A := A) ⟨hA, hAnot⟩ (fun h => hstrong h.2.2) hB₀ hBA
      have h1 : autI hV D ≤ autI hV A := by rw [hDB]; exact hBA
      exact hDB.symm.trans (hmin D hD.1 hD.2 h1)
    have hrk := nonstrong_data hW q hq hnd E hE hEq hcard hS₀ hLΩ hLn hLp hL1 hKmax hSKa hFF hmin'
    have hcard' := B2_8_card_eq hV hUS hSN (A := A) ⟨hA, hAnot⟩ (fun h => hstrong h.2.2)
    have hidx : rkIdx (fixV (autI hV A)) = rk ↥(autI hV A) := by
      have h1 := Subgroup.card_mul_index (fixV (autI hV A))
      have h2 : (fixV (autI hV A)).index = Nat.card (autI hV A) := by
        refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := fixV (autI hV A))) ?_
        rw [h1, hcard']
        ring
      unfold rkIdx rk
      rw [h2]
    have hc3 : cm3 U A = rk ↥(autI hV A) := by rw [e3]; exact hidx
    have hc0 : cm0 P A = 1 := by rw [e0]; omega
    refine ⟨hnotP 1 hc0 (by norm_num), ?_, Or.inl hc0⟩
    rw [hc3, e1]
    omega



theorem hat_abstract {U S I L K X P A : Subgroup G} {t' : G}
    (hc : CoreHyp153 U S I L K X P) (hIeq : I = L ⊔ S)
    (hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer (U : Set G))
    (ht'S : cjSub t' S = S) (ht'P : cjSub t' P = P)
    (hA : IsMaxElemAbelian S A) (hAnot : ¬ A ≤ Subgroup.centralizer (U : Set G))
    (hm0 : cm0 P A = 2) (hnotS0 : ¬ A ≤ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)))
    (hnotS0t : ¬ A ≤ cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S))))
    (hne : cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S))) ≠ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S))) : False := by
  obtain ⟨hV, hSN, hIN, hsyl, hCS, hC2, hUS, hLI, hIL, hKL, hSK, hX, hP, hPS, hSCP,
    ⟨q, hq, hnd, ⟨E, hE, hEq⟩, hcard, hort⟩, hLp, hL1, hKmax⟩ := hc
  have hSI : S ≤ I := hsyl.1
  have hW : ∀ w : IntMod U hV, w ^ 2 = 1 := IntMod.sq_eq_one
  have hAS : A ≤ S := hA.1
  have hFF : IsFFStarOffender (autI hV S) (autI hV A) :=
    offenderImages_isFFStarOffender hV hUS hSN
      (show autI hV A ∈ offenderImages hV S from ⟨A, ⟨hA, hAnot⟩, rfl⟩)
  have hS₀ : IsSylowTwoOf (autI hV S) (orthogonalGroupOf q) :=
    hort ▸ isSylowTwoOf_autI hV hsyl hIN hCS
  have hLΩ : autI hV L ≤ orthogonalGroupOf q := hort ▸ autI_mono hV hLI
  have hLn : ((autI hV L).subgroupOf (orthogonalGroupOf q)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨l, hl, hlx⟩ := (mem_autI hV).1 hx
    have hg : (g : MulAut (IntMod U hV)) ∈ autI hV I := by
      rw [hort]
      exact g.2
    obtain ⟨i, hi, hig⟩ := (mem_autI hV).1 hg
    have hil : (i : G) * l * (i : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hIL hi) l).1 hl
    have key : convI hV (i * l * i⁻¹) =
        (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hig, hlx]
    show (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ ∈ autI hV L
    rw [← key]
    exact convI_mem_autI hV hil (i * l * i⁻¹).2
  have hSKa := autI_le_normalizer hV hSK
  have hautP := autI_P_eq hV hSN hIN hsyl hC2 hLI hKL hX hP
  obtain ⟨-, -, e0⟩ := side_numbers_aux hV hSN hIN hsyl hC2 hLI hKL hX hP hPS hSCP hA
  have hPS' : autI hV P ≤ autI hV S := autI_mono hV hPS
  obtain ⟨hP1, hP2, hP3, hP4, hP5⟩ := hat_facts hW q hq hnd E hE hEq hcard hS₀ hLΩ hLn hLp hL1
    hKmax hSKa (by rw [← hautP]; exact hPS')
  rw [← hautP] at hP1 hP2 hP4 hP5 e0
  have hS0eq := autI_S0_eq hV hSN hIN hLI hSI hIeq hb
  have hPS0 : P ≤ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)) :=
    le_S0_of_autI_le hV hSN hLI hSI hIeq hb hPS (hP1.trans inf_le_right)
  have hM₂S : cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S))) ≤ S := by
    have := cjSub_mono (g := t') (inf_le_left : S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)) ≤ S)
    rwa [ht'S] at this
  have hPM₂ : P ≤ cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S))) := by
    have := cjSub_mono (g := t') hPS0
    rwa [ht'P] at this
  have hsqP : ∀ z ∈ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)), z * z ∈ P := by
    intro z hz
    have hzN : z ∈ Subgroup.normalizer (U : Set G) := hSN hz.1
    have h1 : convI hV ⟨z, hzN⟩ ∈ autI hV S ⊓ autI hV L := by
      rw [← hS0eq]
      exact convI_mem_autI hV hz hzN
    have h2 := hP4 _ h1
    have h3 : convI hV ⟨z * z, hSN (S.mul_mem hz.1 hz.1)⟩ ∈ autI hV P := by
      have : convI hV ⟨z * z, hSN (S.mul_mem hz.1 hz.1)⟩ =
          convI hV ⟨z, hzN⟩ * convI hV ⟨z, hzN⟩ := by
        rw [← map_mul]
        rfl
      rw [this]
      exact h2
    obtain ⟨p, hp, hpz⟩ := (mem_autI hV).1 h3
    have h4 : convI hV (⟨z * z, hSN (S.mul_mem hz.1 hz.1)⟩ * p⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hpz, mul_inv_cancel]
    have h5 : z * z * (p : G)⁻¹ ∈ Subgroup.centralizer (U : Set G) := (convI_eq_one_iff hV _).1 h4
    have h6 : z * z * (p : G)⁻¹ ∈ P :=
      hSCP ⟨S.mul_mem (S.mul_mem hz.1 hz.1) (S.inv_mem (hPS hp)), h5⟩
    have := P.mul_mem h6 hp
    simpa using this
  have hPn : ((autI hV P).subgroupOf (autI hV S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPS', hautP]
    exact le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hidx : (autI hV P).relIndex (autI hV S) = 8 := by
    have h := Subgroup.relIndex_mul_card (autI hV P) (autI hV S)
    rw [inf_eq_left.2 hPS', hP2] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hS₀S : ∀ A' : Subgroup G, A' ≤ S → autI hV A' ≤ autI hV S := fun A' h => autI_mono hV h
  have hi₁ : (autI hV S ⊓ autI hV L).relIndex (autI hV S) = 2 := by
    have h := Subgroup.relIndex_mul_card (autI hV S ⊓ autI hV L) (autI hV S)
    rw [inf_eq_left.2 (inf_le_left : autI hV S ⊓ autI hV L ≤ autI hV S)] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h, hP3])
  have hM₂c : Nat.card ↥(autI hV (cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S))))) =
      Nat.card ↥(autI hV S ⊓ autI hV L) := by
    rw [card_autI_cjSub hV hSN hSCP ht'S ht'P hPS0 inf_le_left, hS0eq]
  have hi₂ : (autI hV (cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S))))).relIndex (autI hV S) = 2 := by
    have h := Subgroup.relIndex_mul_card (autI hV (cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)))))
      (autI hV S)
    rw [inf_eq_left.2 (autI_mono hV hM₂S), hM₂c] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h, hP3])
  have hAN' : autI hV A ≤ Subgroup.normalizer ((autI hV P : Subgroup (MulAut (IntMod U hV))) :
      Set (MulAut (IntMod U hV))) := by
    have : autI hV S ≤ Subgroup.normalizer ((autI hV P : Subgroup (MulAut (IntMod U hV))) :
        Set (MulAut (IntMod U hV))) := (Subgroup.normal_subgroupOf_iff_le_normalizer hPS').1 hPn
    exact (autI_mono hV hAS).trans this
  have hrel : (autI hV P).relIndex (autI hV A ⊔ autI hV P) = (autI hV P).relIndex (autI hV A) :=
    B2F.relIndex_sup_eq_of_le_normalizer' hAN'
  have hAe : IsElemAbelian2 (autI hV A) := hFF.2.2.1
  have hcA : Nat.card ↥(autI hV A) = 2 ^ rk ↥(autI hV A) := B1.card_elemAbelian hAe
  have hcAP : Nat.card ↥(autI hV P ⊓ autI hV A) = 2 ^ rk ↥(autI hV A ⊓ autI hV P) := by
    rw [inf_comm]
    exact B1.card_elemAbelian (A := autI hV A ⊓ autI hV P)
      ⟨fun a ha b hb => hAe.1 a ha.1 b hb.1, fun a ha => hAe.2 a ha.1⟩
  have hrk4 : rk ↥(autI hV A) = rk ↥(autI hV A ⊓ autI hV P) + 2 := by
    have hle : rk ↥(autI hV A ⊓ autI hV P) ≤ rk ↥(autI hV A) := rk_mono inf_le_left
    omega
  have hi₃' : (autI hV P).relIndex (autI hV A ⊔ autI hV P) = 4 := by
    rw [hrel]
    have h := Subgroup.relIndex_mul_card (autI hV P) (autI hV A)
    rw [hcA, hcAP, hrk4, pow_add] at h
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0 < 2) _) (by rw [h]; ring)
  have hM₃S : autI hV A ⊔ autI hV P ≤ autI hV S := sup_le (hS₀S A hAS) hPS'
  have hi₃ : (autI hV A ⊔ autI hV P).relIndex (autI hV S) = 2 := by
    have h := Subgroup.relIndex_mul_relIndex (autI hV P) (autI hV A ⊔ autI hV P) (autI hV S)
      le_sup_right hM₃S
    rw [hi₃', hidx] at h
    omega
  have hs₃ : ∀ x ∈ autI hV A ⊔ autI hV P, x * x ∈ autI hV P := by
    intro x hx
    obtain ⟨e, he, p, hp, rfl⟩ := exists_mul_of_mem_sup_of_normalizes' (E := autI hV A)
      (A := autI hV P) (fun e he y hy => (Subgroup.mem_normalizer_iff.mp (hAN' he) y).1 hy) hx
    have he2 : e * e = 1 := by
      have := hAe.2 e he
      rwa [pow_two] at this
    have h1 : e * p * (e * p) = (e * p * e⁻¹) * (e * e) * p := by group
    rw [h1, he2, mul_one]
    exact (autI hV P).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hAN' he) p).1 hp) hp
  have hs₂ : ∀ x ∈ autI hV (cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)))), x * x ∈ autI hV P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hx
    have hy' : t'⁻¹ * (y : G) * t' ∈ S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)) := mem_cjSub.1 hy
    have h1 := hsqP _ hy'
    have h2 : (y : G) * y ∈ P := by
      have : (y : G) * y = t' * (t'⁻¹ * y * t' * (t'⁻¹ * y * t')) * t'⁻¹ := by group
      rw [this]
      have h3 : t' * (t'⁻¹ * (y : G) * t' * (t'⁻¹ * y * t')) * t'⁻¹ ∈ cjSub t' P := by
        rw [mem_cjSub]
        simpa [mul_assoc] using h1
      rwa [ht'P] at h3
    have h4 : convI hV (y * y) ∈ autI hV P := convI_mem_autI hV h2 (y * y).2
    rw [← map_mul]
    exact h4
  have hd₁₂ : autI hV S ⊓ autI hV L ≠ autI hV (cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)))) := by
    intro h
    apply hne
    refine (eq_of_autI_eq hV hSN hM₂S inf_le_left (hSCP.trans hPM₂) (hSCP.trans hPS0) ?_)
    rw [← h, hS0eq]
  have hd₁₃ : autI hV S ⊓ autI hV L ≠ autI hV A ⊔ autI hV P := by
    intro h
    apply hnotS0
    refine le_S0_of_autI_le hV hSN hLI hSI hIeq hb hAS ?_
    have : autI hV A ≤ autI hV S ⊓ autI hV L := h ▸ le_sup_left
    exact this.trans inf_le_right
  have hd₂₃ : autI hV (cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)))) ≠ autI hV A ⊔ autI hV P := by
    intro h
    apply hnotS0t
    refine le_of_autI_le hV hSN hAS hM₂S (hSCP.trans hPM₂) ?_
    exact (h ▸ le_sup_left : autI hV A ≤ autI hV (cjSub t' (S ⊓ (L ⊔ pCoreOf 2 (L ⊔ S)))))
  exact three_klein (S := autI hV S) (P := autI hV P) hPS' hPn hidx hP5
    hP1
    (autI_mono hV hPM₂) le_sup_right inf_le_left (autI_mono hV hM₂S) hM₃S hi₁ hi₂ hi₃
    (fun x hx => hP4 x hx) hs₂ hs₃ hd₁₂ hd₁₃ hd₂₃

end Side

end CFSG.Quasithin.A38c6

namespace CFSG.Quasithin

open CFSG.Quasithin.A38c6

theorem countSideU_holds (hPre : Input32Preamble) : CountSideU := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc A hA
  have hP32 : Preamble32 T V₁ I L := hPre G T Mc M V₁ V₂ Yp I L t c
  obtain ⟨K, hc⟩ := coreHyp_of_ctx hP32 c cc
  have hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer ((UL153 T I L : Subgroup G) : Set G) := hP32.2.1
  obtain ⟨h1, h2, h3⟩ := side_abstract hc c.I_eq hb hA.1 hA.2.1 hA.2.2
  refine ⟨h1, h2, ?_⟩
  rcases h3 with h | ⟨h, -, -, h'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, h'⟩


theorem strongD_refined (hPre : Input32Preamble) :
    ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
      Ctx15332 T Mc M V₁ V₂ Yp I L t → Concl15332 T M V₁ I L →
        ∀ t' ∈ T, t' ∉ Sgp153 T V₁ → ∀ A : Subgroup G, IsMaxElemAbelian (Sgp153 T V₁) A →
          cm3 (conjBy153 t' (UL153 T I L)) A <
            rk ↥A - rk ↥(A ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) →
          ¬ A ≤ conjBy153 t' (S0153 T V₁ L) := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA hstrong
  have hP32 : Preamble32 T V₁ I L := hPre G T Mc M V₁ V₂ Yp I L t c
  obtain ⟨K, hc⟩ := coreHyp_of_ctx hP32 c cc
  have hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer ((UL153 T I L : Subgroup G) : Set G) := hP32.2.1
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t :=
    (c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L).ctx.hyp
  have ht'N : t' ∈ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp.hyp hyp.decomp ht'T
  have ht'XS : t' ∈ Subgroup.normalizer ((X153 T M V₁ ⊔ Sgp153 T V₁ : Subgroup G) : Set G) :=
    S153H.mem_normalizer_sup (S153H.T_le_normalizer_X c ht'T) ht'N
  have ht'P : t' ∈ Subgroup.normalizer (P153 T M V₁ : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 _ ht'XS
  obtain ⟨A', hA', rfl⟩ : ∃ A' : Subgroup G, IsMaxElemAbelian (Sgp153 T V₁) A' ∧ A = cjSub t' A' :=
    ⟨cjSub t'⁻¹ A, isMaxElemAbelian_cjSub (inv_mem ht'N) hA, (cjSub_cjSub_inv t' A).symm⟩
  have e3 : cm3 (conjBy153 t' (UL153 T I L)) (cjSub t' A') = cm3 (UL153 T I L) A' := by
    show rk ↥(cjSub t' (UL153 T I L)) - rk ↥(cjSub t' (UL153 T I L) ⊓
      Subgroup.centralizer ((cjSub t' A' : Subgroup G) : Set G)) = _
    rw [← cjSub_centralizer, ← cjSub_inf, rk_cjSub, rk_cjSub]
  have e2 : rk ↥(cjSub t' A') - rk ↥(cjSub t' A' ⊓
      Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) =
      rk ↥A' - rk ↥(A' ⊓ Subgroup.centralizer ((UL153 T I L : Subgroup G) : Set G)) := by
    show rk ↥(cjSub t' A') - rk ↥(cjSub t' A' ⊓
      Subgroup.centralizer ((cjSub t' (UL153 T I L) : Subgroup G) : Set G)) = _
    rw [← cjSub_centralizer, ← cjSub_inf, rk_cjSub, rk_cjSub]
  rw [e3, e2] at hstrong
  have hAnot' : ¬ A' ≤ Subgroup.centralizer ((UL153 T I L : Subgroup G) : Set G) := fun h => by
    rw [inf_eq_left.2 h, Nat.sub_self] at hstrong
    exact Nat.not_lt_zero _ hstrong
  have hFF' : IsFFStarOffender (autI hc.hV (Sgp153 T V₁)) (autI hc.hV A') :=
    offenderImages_isFFStarOffender hc.hV hc.hUS hc.hSN
      (show autI hc.hV A' ∈ offenderImages hc.hV (Sgp153 T V₁) from ⟨A', ⟨hA', hAnot'⟩, rfl⟩)
  have hlt : rAV (autI hc.hV A') < 1 :=
    rAV_autI_lt_one hc.hV hFF'.isA2 (hA'.1.trans hc.hSN) hstrong
  obtain ⟨-, -, -, h5⟩ := strong_abstract hc c.I_eq hb hA' hAnot' hlt
  intro hle
  apply h5
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj t').injective).1 hle

theorem countTHat_holds (hPre : Input32Preamble) : CountTHat := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S hne A hA hm0
  have hP32 : Preamble32 T V₁ I L := hPre G T Mc M V₁ V₂ Yp I L t c
  obtain ⟨K, hc⟩ := coreHyp_of_ctx hP32 c cc
  have hb : pCoreOf 2 I = I ⊓ Subgroup.centralizer ((UL153 T I L : Subgroup G) : Set G) := hP32.2.1
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t :=
    (c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L).ctx.hyp
  have ht'N : t' ∈ Subgroup.normalizer (Sgp153 T V₁ : Set G) :=
    Hyp153.T_le_normalizer_Sgp153 hyp.hyp hyp.decomp ht'T
  have ht'XS : t' ∈ Subgroup.normalizer ((X153 T M V₁ ⊔ Sgp153 T V₁ : Subgroup G) : Set G) :=
    S153H.mem_normalizer_sup (S153H.T_le_normalizer_X c ht'T) ht'N
  have ht'P : t' ∈ Subgroup.normalizer (P153 T M V₁ : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 _ ht'XS
  have hSeq : cjSub t' (Sgp153 T V₁) = Sgp153 T V₁ := map_conj_eq_of_mem_normalizer ht'N
  have hPeq : cjSub t' (P153 T M V₁) = P153 T M V₁ := map_conj_eq_of_mem_normalizer ht'P
  obtain ⟨h1, h2, h3⟩ := side_abstract hc c.I_eq hb hA.1 hA.2.1 hA.2.2
  have hcase : cm3 (UL153 T I L) A = 3 ∧ cm1 (P153 T M V₁) (UL153 T I L) A = 2 ∧
      ¬ A ≤ S0153 T V₁ L := by
    rcases h3 with h | ⟨-, h3, h1', h5⟩
    · omega
    · exact ⟨h3, h1', h5⟩
  have hI := countIneq_of_abstract G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA.1
  have hPeq' : P153 T M V₁ = (Sgp153 T V₁ ⊓ Subgroup.centralizer (UL153 T I L : Set G)) ⊔
      (Sgp153 T V₁ ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) :=
    (cc.P_split t' ht'T ht'S).1
  have hCP : Sgp153 T V₁ ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) ≤
      P153 T M V₁ := by
    rw [hPeq']
    exact le_sup_right
  have hAS : A ≤ Sgp153 T V₁ := hA.1.1
  have heq : A ⊓ P153 T M V₁ ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) =
      A ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G) := by
    refine le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) fun x hx => ⟨⟨hx.1, hCP ⟨hAS hx.1, hx.2⟩⟩, hx.2⟩
  have m1 : rk ↥(A ⊓ P153 T M V₁) ≤ rk ↥A := rk_mono inf_le_left
  have m2 : rk ↥(A ⊓ P153 T M V₁ ⊓ Subgroup.centralizer
      ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) ≤ rk ↥(A ⊓ P153 T M V₁) :=
    rk_mono inf_le_left
  have hrank : rk ↥A - rk ↥(A ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) =
      cm0 (P153 T M V₁) A + cm1 (P153 T M V₁) (conjBy153 t' (UL153 T I L)) A := by
    simp only [cm0, cm1]
    rw [← heq]
    omega
  have hstrongT : cm3 (conjBy153 t' (UL153 T I L)) A <
      rk ↥A - rk ↥(A ⊓ Subgroup.centralizer ((conjBy153 t' (UL153 T I L) : Subgroup G) : Set G)) := by
    rw [hrank]
    omega
  have hnotS0t := strongD_refined hPre G T Mc M V₁ V₂ Yp I L t c cc t' ht'T ht'S A hA.1 hstrongT
  exact hat_abstract hc c.I_eq hb hSeq hPeq hA.1 hA.2.1 hm0 hcase.2.2 hnotS0t hne

end CFSG.Quasithin
