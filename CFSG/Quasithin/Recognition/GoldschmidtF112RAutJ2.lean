module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2Lat
public import CFSG.Quasithin.Recognition.GoldschmidtF112RJ2
public import CFSG.Quasithin.Recognition.GoldschmidtF112TitsBorel
public import CFSG.Quasithin.Recognition.CertTitsAmalgamLocal
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsTransport
public import CFSG.Quasithin.Vol2.Ch5Sec1L34J2Aut
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicInversionAlternatingFive
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Recognition.CertTwoLocalPair

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
  CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312J2 CFSG.ComponentClassification.J2Cover

section Abstract

@[expose] def subgroupOfSwap {G : Type*} [Group G] (A B : Subgroup G) :
    ↥(A.subgroupOf B) ≃* ↥(B.subgroupOf A) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

noncomputable def oTwoQuotCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    oTwoQuot X ≃* oTwoQuot Y :=
  QuotientGroup.congr (pCore 2 X) (pCore 2 Y) e (map_pCore_mulEquiv 2 e)

theorem nonempty_perm_five_of_normal_alt5 {X : Type*} [Group X] [Finite X]
    (hX : Nat.card X = 120) (N : Subgroup X) [N.Normal] (e : ↥N ≃* alternatingGroup (Fin 5))
    (h2 : ∀ C : Subgroup X, C.Normal → IsPGroup 2 C → C = ⊥) :
    Nonempty (X ≃* Equiv.Perm (Fin 5)) := by
  let ψ : MulAut ↥N ≃* MulAut (alternatingGroup (Fin 5)) := H13.mulAutCongrOfMulEquiv e
  let θ := (CFSG.Semidihedral.Principal.CyclicAlternatingFive.autEquiv).symm
  let f : X →* Equiv.Perm (Fin 5) :=
    (θ.toMonoidHom.comp ψ.toMonoidHom).comp (MulAut.conjNormal (H := N))
  have hN60 : Nat.card N = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hcent : ∀ x ∈ f.ker, ∀ n : N, x * (n : X) * x⁻¹ = n := by
    intro x hx n
    have h1 : θ (ψ (MulAut.conjNormal (H := N) x)) = 1 := hx
    have h2' : MulAut.conjNormal (H := N) x = 1 := by
      have : ψ (MulAut.conjNormal (H := N) x) = 1 := θ.injective (h1.trans (map_one θ).symm)
      exact ψ.injective (this.trans (map_one ψ).symm)
    have := congrArg (fun φ : MulAut ↥N => ((φ n : ↥N) : X)) h2'
    simpa [MulAut.conjNormal_apply] using this
  have hinf : ∀ x ∈ f.ker, x ∈ N → x = 1 := by
    intro x hx hxN
    have hc : e ⟨x, hxN⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨n, rfl⟩ := e.surjective a
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have := hcent x hx n
      change (n : X) * x = x * n
      calc (n : X) * x = x * n * x⁻¹ * x := by rw [this]
        _ = x * n := by group
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
    have : (⟨x, hxN⟩ : ↥N) = 1 := e.injective (hc.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hle : Nat.card f.ker ≤ 2 := by
    have hq : Nat.card (X ⧸ N) = 2 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [hX, hN60] at h
      omega
    rw [← hq]
    refine Nat.card_le_card_of_injective (fun c => (QuotientGroup.mk (c : X) : X ⧸ N)) ?_
    intro c d hcd
    have h' : (c : X)⁻¹ * d ∈ N := QuotientGroup.eq.mp hcd
    have hk : (c : X)⁻¹ * d ∈ f.ker := f.ker.mul_mem (f.ker.inv_mem c.2) d.2
    have := hinf _ hk h'
    exact Subtype.ext (inv_mul_eq_one.mp this)
  have hp : IsPGroup 2 f.ker := by
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    rcases (show Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 by omega) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [h]; rfl)
  have hker : f.ker = ⊥ := h2 _ inferInstance hp
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hbij : Function.Bijective f := by
    refine (Function.Injective.bijective_of_nat_card_le hinj ?_)
    rw [hX, Nat.card_perm]
    simp [Nat.factorial]
  exact ⟨MulEquiv.ofBijective f hbij⟩

theorem exists_map_overgroup {A H : Type} [Group A] [Finite A] [Group H] [Finite H]
    (ψ : A ≃* H) {T₀ : Subgroup A} (hT₀ : IsSylowTwoOf T₀ ⊤) {S₀ : Subgroup H}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {Z : Subgroup A} (hTZ : T₀ ≤ Z) :
    ∃ f : A ≃* H, S₀ ≤ Z.map f.toMonoidHom ∧ Nat.card (Z.map f.toMonoidHom) = Nat.card Z := by
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow hS₀
    (QuasithinUnique.Unc25K1.isSylowTwoOf_top_map ψ hT₀)
  refine ⟨ψ.trans ρ, ?_, Subgroup.card_map_of_injective (ψ.trans ρ).injective⟩
  have hS : T₀.map (ψ.trans ρ).toMonoidHom = S₀ := by
    rw [← hρ, Subgroup.map_map]
    rfl
  rw [← hS]
  exact Subgroup.map_mono hTZ

theorem nonempty_equiv_of_overgroup {A H : Type} [Group A] [Finite A] [Group H] [Finite H]
    (ψ : A ≃* H) {T₀ : Subgroup A} (hT₀ : IsSylowTwoOf T₀ ⊤) {S₀ : Subgroup H}
    (hS₀ : IsSylowTwoOf S₀ ⊤) {Z : Subgroup A} (hTZ : T₀ ≤ Z) {M : Subgroup H}
    (hM : ∀ W : Subgroup H, S₀ ≤ W → Nat.card W = Nat.card Z → W = M) : Nonempty (↥Z ≃* ↥M) := by
  obtain ⟨f, hSZ, hc⟩ := exists_map_overgroup ψ hT₀ hS₀ hTZ
  exact ⟨(Z.equivMapOfInjective _ f.injective).trans (MulEquiv.subgroupCongr (hM _ hSZ hc))⟩

end Abstract

section Model


@[expose] noncomputable def J0 : Subgroup R := P.subgroupOf R

theorem J0_eq : J0 = P.subgroupOf R := rfl

theorem card_J0 : Nat.card J0 = 604800 := by
  rw [J0_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_R).toEquiv, card_P]

theorem index_J0 : J0.index = 2 := by
  have h := J0.card_mul_index
  rw [card_J0, card_R] at h
  omega

instance J0_normal : J0.Normal := Subgroup.normal_of_index_eq_two index_J0

noncomputable def ψJ : ↥J0 ≃* ↥CFSG.Sporadic.J2.J :=
  (MulEquiv.subgroupCongr J0_eq).trans ((Subgroup.subgroupOfEquivOfLe P_le_R).trans jEquivP.symm)

theorem relIndex_J0 {M : Subgroup R} (hSM : AJ2L.rCtx.S ≤ M) : J0.relIndex M = 2 := by
  have hrd : J0.relIndex M ∣ 2 := index_J0 ▸ Subgroup.relIndex_dvd_index_of_normal J0 M
  rcases (Nat.dvd_prime Nat.prime_two).mp hrd with h1 | h1
  · exfalso
    have hMJ : M ≤ J0 := Subgroup.relIndex_eq_one.mp h1
    have hd := Subgroup.card_dvd_of_le (hSM.trans hMJ)
    rw [AJ2L.rCtx_S_card, card_J0] at hd
    norm_num at hd
  · exact h1

theorem card_inf_J0 {M : Subgroup R} (hSM : AJ2L.rCtx.S ≤ M) :
    2 * Nat.card (M.subgroupOf J0) = Nat.card M := by
  have hr := Subgroup.relIndex_mul_card (H := J0) (K := M)
  rw [relIndex_J0 hSM] at hr
  rw [← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : M ⊓ J0 ≤ J0)).toEquiv,
    inf_comm]
  exact hr

theorem T0_sylow : IsSylowTwoOf (AJ2L.rCtx.S.subgroupOf J0) ⊤ := by
  have hc : Nat.card (AJ2L.rCtx.S.subgroupOf J0) = 2 ^ 7 := by
    have := card_inf_J0 (le_refl AJ2L.rCtx.S)
    rw [AJ2L.rCtx_S_card] at this
    omega
  refine ⟨le_top, IsPGroup.of_card hc, ?_⟩
  have e1 : ((AJ2L.rCtx.S.subgroupOf J0).subgroupOf ⊤).index =
      (AJ2L.rCtx.S.subgroupOf J0).index := Subgroup.relIndex_top_right _
  rw [e1]
  have h := (AJ2L.rCtx.S.subgroupOf J0).card_mul_index
  rw [hc, card_J0] at h
  have h2 : (AJ2L.rCtx.S.subgroupOf J0).index = 4725 := by omega
  rw [h2]
  norm_num

theorem eq_j2Y3_of_card {W : Subgroup ↥CFSG.Sporadic.J2.J} (hSW : j2CtxA.S ≤ W)
    (hc : Nat.card W = 1920) : W = j2CtxA.Y 3 := by
  rcases J2L.overgroup hSW with h | ⟨j, hj, hZ, hcj⟩
  · rw [h, Subgroup.card_top, CFSG.Sporadic.J2.card_J] at hc
    norm_num at hc
  · rw [hc] at hcj
    have hj3 : j = 3 := by
      interval_cases j <;> simp_all
    subst hj3
    exact hZ

theorem nonempty_y2InfEquiv :
    Nonempty (↥(J0.subgroupOf (AJ2L.rCtx.Y 2)) ≃* ↥(j2CtxA.Y 3)) := by
  have hTZ : AJ2L.rCtx.S.subgroupOf J0 ≤ (AJ2L.rCtx.Y 2).subgroupOf J0 := by
    intro x hx
    exact AJ2L.rCtx.S_le_Y 2 hx
  have hcZ : Nat.card ((AJ2L.rCtx.Y 2).subgroupOf J0) = 1920 := by
    have := card_inf_J0 (AJ2L.rCtx.S_le_Y 2)
    rw [AJ2L.card_Y2] at this
    omega
  obtain ⟨e⟩ := @nonempty_equiv_of_overgroup ↥J0 ↥CFSG.Sporadic.J2.J inferInstance
    inferInstance inferInstance inferInstance ψJ _ T0_sylow j2CtxA.S j2A_sylow _ hTZ
    (j2CtxA.Y 3) (fun W hW hc => eq_j2Y3_of_card hW (hc.trans hcZ))
  exact ⟨(subgroupOfSwap J0 (AJ2L.rCtx.Y 2)).trans e⟩

theorem y2Inf_normal : (J0.subgroupOf (AJ2L.rCtx.Y 2)).Normal :=
  J0_normal.comap (AJ2L.rCtx.Y 2).subtype

theorem card_pCore_Y2 : Nat.card (pCore 2 ↥(AJ2L.rCtx.Y 2)) = 2 ^ 5 := by
  have := AJ2L.card_pCoreOf_Y2
  rwa [pCoreOf, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at this

theorem pCoreOf_y2Inf_eq :
    pCoreOf 2 (J0.subgroupOf (AJ2L.rCtx.Y 2)) = pCore 2 ↥(AJ2L.rCtx.Y 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eN⟩ := nonempty_y2InfEquiv
  set N := J0.subgroupOf (AJ2L.rCtx.Y 2) with hN
  haveI hNn : N.Normal := y2Inf_normal
  have hnorm : (pCoreOf 2 N).Normal := by
    haveI : (pCore 2 ↥N).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := N) (pCore 2 ↥N)
    rw [Subgroup.normalizer_eq_top_iff.mpr hNn] at h
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)
  have hle : pCoreOf 2 N ≤ pCore 2 ↥(AJ2L.rCtx.Y 2) :=
    CFSG.LieType.BorelTits.le_pCore 2 hnorm (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_pCoreOf_of_mulEquiv eN 2, J2L.card_pCoreOf_Y3, card_pCore_Y2]

theorem isQ8D8_pCoreOf_Y2 : IsQ8D8 ↥(pCoreOf 2 (AJ2L.rCtx.Y 2)) := by
  obtain ⟨eN⟩ := nonempty_y2InfEquiv
  have h := isQ8D8_pCoreOf_of_mulEquiv eN isQ8D8_pCoreOf_Y3
  rw [pCoreOf_y2Inf_eq] at h
  exact isQ8D8_of_mulEquiv
    ((pCore 2 ↥(AJ2L.rCtx.Y 2)).equivMapOfInjective _ (Subgroup.subtype_injective _)) h

theorem quot_Y3_alt5 : Nonempty (oTwoQuot ↥(j2CtxA.Y 3) ≃* alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨V, hVn, hV, ⟨eA⟩⟩, -⟩ := j2_Y3_ext
  have hle : V ≤ pCore 2 ↥(j2CtxA.Y 3) := CFSG.LieType.BorelTits.le_pCore 2 hVn (IsPGroup.of_card hV.2)
  have hc : Nat.card (pCore 2 ↥(j2CtxA.Y 3)) = 2 ^ 5 := by
    have := J2L.card_pCoreOf_Y3
    rwa [pCoreOf, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at this
  have heq : V = pCore 2 ↥(j2CtxA.Y 3) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hV.2])
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans eA⟩

theorem perm5_Y2 : Nonempty (oTwoQuot ↥(AJ2L.rCtx.Y 2) ≃* Equiv.Perm (Fin 5)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eN⟩ := nonempty_y2InfEquiv
  obtain ⟨eA⟩ := quot_Y3_alt5
  set N := J0.subgroupOf (AJ2L.rCtx.Y 2) with hN
  haveI hNn : N.Normal := y2Inf_normal
  set Q := pCore 2 ↥(AJ2L.rCtx.Y 2) with hQ
  let g : ↥N →* ↥(AJ2L.rCtx.Y 2) ⧸ Q := (QuotientGroup.mk' Q).comp N.subtype
  have hker : g.ker = pCore 2 ↥N := by
    ext n
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (n : ↥(AJ2L.rCtx.Y 2)) : ↥(AJ2L.rCtx.Y 2) ⧸ Q) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, hQ, ← pCoreOf_y2Inf_eq, pCoreOf]
    exact Subgroup.mem_map_iff_mem (f := N.subtype) (Subgroup.subtype_injective _)
  have hrange : g.range = N.map (QuotientGroup.mk' Q) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eNq : ↥(N.map (QuotientGroup.mk' Q)) ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr hrange.symm).trans ((QuotientGroup.quotientKerEquivRange g).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans ((@oTwoQuotCongr ↥N ↥(j2CtxA.Y 3) inferInstance inferInstance eN).trans eA)))
  haveI : (N.map (QuotientGroup.mk' Q)).Normal := hNn.map _ (QuotientGroup.mk'_surjective Q)
  refine nonempty_perm_five_of_normal_alt5 ?_ _ eNq ?_
  · have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    have hQc : Nat.card Q = 2 ^ 5 := card_pCore_Y2
    rw [AJ2L.card_Y2, hQc] at h
    change Nat.card (↥(AJ2L.rCtx.Y 2) ⧸ Q) = 120
    omega
  · intro C hC hp
    exact le_bot_iff.mp ((CFSG.LieType.BorelTits.le_pCore 2 hC hp).trans
      (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot).le)

end Model

section Main


theorem y9AutJ2 : Y9AutJ2 := by
  intro G _ _ L1 L2 S hF h1 h2 hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, _, ⟨e⟩, T, M₁, M₂, hp, ⟨ψ1⟩, -, ⟨ψ2⟩⟩ := hA
  obtain ⟨E0⟩ : Nonempty (Y ≃* ↥R) :=
    ⟨e.trans ((H13.mulAutCongrOfMulEquiv (quasithinJ2MulEquivNative.trans nativeEquivP)).trans
      rAutEquiv.symm)⟩
  obtain ⟨E, hy2⟩ := @exists_yPair_conj Y ↥R inferInstance inferInstance
    inferInstance E0 AJ2L.rCtx.S AJ2L.rCtx_sylow T M₁ M₂ hp
  have hL1 : 5 ∣ Nat.card ↥(L1 ⊔ bigB L1 L2 S) := by
    have h60 : Nat.card (oTwoQuot ↥L1) = 60 := by
      rw [IsL2Quot.card (by norm_num) h1]
      norm_num
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L1)
    have h5 : 5 ∣ Nat.card L1 := by
      rw [hq]
      exact Dvd.dvd.mul_right (h60 ▸ (by norm_num : 5 ∣ 60)) _
    exact h5.trans (Subgroup.card_dvd_of_le le_sup_left)
  have φ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(M₁.map E.toMonoidHom) :=
    ψ1.trans (M₁.equivMapOfInjective E.toMonoidHom E.injective)
  have φ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(M₂.map E.toMonoidHom) :=
    ψ2.trans (M₂.equivMapOfInjective E.toMonoidHom E.injective)
  obtain ⟨hM1, hM2⟩ : M₁.map E.toMonoidHom = AJ2L.rCtx.Y 2 ∧
      M₂.map E.toMonoidHom = AJ2L.rCtx.Y 1 := by
    rcases AJ2L.yPair_eq hy2 with h' | ⟨hM1, -⟩
    · exact h'
    · exfalso
      rw [Nat.card_congr φ1.toEquiv, hM1, AJ2L.card_Y1] at hL1
      norm_num at hL1
  let P1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(AJ2L.rCtx.Y 2) := φ1.trans (MulEquiv.subgroupCongr hM1)
  let P2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(AJ2L.rCtx.Y 1) := φ2.trans (MulEquiv.subgroupCongr hM2)
  have hq8 : IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) :=
    isQ8D8_pCoreOf_of_mulEquiv P1 isQ8D8_pCoreOf_Y2
  have hLB : L1 ⊔ bigB L1 L2 S = L1 ⊔ S := by
    rw [bigB, F112TitsSlice.borelOf_eq_vs3 hF.1.h2 h2]
    apply le_antisymm
    · refine sup_le le_sup_left (sup_le (sup_le ?_ ?_) le_sup_right)
      · exact (inf_le_left : borelOf L1 S ≤ L1).trans le_sup_left
      · exact (inf_le_left : S ⊓ L2 ≤ S).trans le_sup_right
    · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hs5 : Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 5)) := by
    obtain ⟨σ⟩ := perm5_Y2
    exact ⟨(oTwoQuotCongr ((MulEquiv.subgroupCongr hLB.symm).trans P1)).trans σ⟩
  have hR : Hyp111R L1 L2 S := by
    obtain ⟨e1⟩ := h1
    obtain ⟨e2⟩ := F112J2.nonempty_psl_four_equiv_alt5
    exact (CFSG.Quasithin.hyp111R_of_perm_three_alt_five hF.1.symm h2 ⟨e1.trans e2⟩).symm
  obtain ⟨-, -, hQS⟩ := CFSG.GH74.QTGen4.DSGen4.leafSylowS hR
  have hct : CharTwo (L1 ⊔ bigB L1 L2 S) := by
    rw [F1.parabolic_eq]
    exact hF.1.h1.charTwo
  have hSP : S ≤ L1 ⊔ bigB L1 L2 S :=
    (le_sup_right : S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S).trans le_sup_right
  have hZ : Nat.card (Subgroup.center ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S))) ≤ 2 := by
    obtain ⟨z, -, -, hzz, hc, -⟩ := CFSG.Quasithin.H13.isQ8D8_central_facts hq8
    have hle : Subgroup.center ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≤ Subgroup.zpowers z :=
      fun c hc' => by
        rcases hc c hc' with rfl | rfl
        · exact one_mem _
        · exact Subgroup.mem_zpowers _
    calc Nat.card (Subgroup.center ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)))
        ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hle
      _ = orderOf z := Nat.card_zpowers z
      _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hzz)
  refine ⟨fun _ => centerOf_le_centralizer_two le_sup_left hct hSP hQS hZ, hs5, hq8, ?_⟩
  rw [card_pCoreOf_of_mulEquiv P2 2, AJ2L.card_pCoreOf_Y1]

end Main

end CFSG.Quasithin.F112R
