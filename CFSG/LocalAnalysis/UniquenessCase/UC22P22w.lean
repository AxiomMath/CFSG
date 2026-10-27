module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

section Dictionary

variable {M V : Subgroup G} {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]

theorem uc22p22w_fix_iff (hV : M ≤ normalizer (V : Set G)) (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ) (m : ↥M) (x : Vmod) :
    ρ (QuotientGroup.mk m) x = x ↔
      (m : G) * ((e.symm (Multiplicative.ofAdd x) : ↥V) : G) =
        ((e.symm (Multiplicative.ofAdd x) : ↥V) : G) * (m : G) := by
  have h := uc22br4_symm_rho hV e ρ hc m x
  set v : G := ((e.symm (Multiplicative.ofAdd x) : ↥V) : G) with hv
  constructor
  · intro hx
    rw [hx] at h
    calc (m : G) * v = ((m : G) * v * (m : G)⁻¹) * (m : G) := by group
      _ = v * (m : G) := by rw [← h]
  · intro hcomm
    have h2 : (m : G) * v * (m : G)⁻¹ = v := by
      calc (m : G) * v * (m : G)⁻¹ = (v * (m : G)) * (m : G)⁻¹ := by rw [hcomm]
        _ = v := by group
    rw [h2] at h
    have h3 : e.symm (Multiplicative.ofAdd (ρ (QuotientGroup.mk m) x)) =
        e.symm (Multiplicative.ofAdd x) := Subtype.ext h
    exact Multiplicative.ofAdd.injective (e.symm.injective h3)

theorem uc22p22w_card_fixSub (hV : M ≤ normalizer (V : Set G)) (e : ↥V ≃* Multiplicative Vmod)
    (ρ : Representation (ZMod 2) (MBar M V) Vmod) (hc : ConjModule M V e ρ) {B : Subgroup G}
    (hBM : B ≤ M) :
    Nat.card ↥(fixSub ρ (mbarImage M V B)) = Nat.card ↥(V ⊓ centralizer (B : Set G)) := by
  have hmem : ∀ (b : G) (hb : b ∈ B), (QuotientGroup.mk ⟨b, hBM hb⟩ : MBar M V) ∈ mbarImage M V B :=
    fun b hb => Subgroup.mem_map.2 ⟨⟨b, hBM hb⟩, hb, rfl⟩
  refine Nat.card_congr
    { toFun := fun w => ⟨((e.symm (Multiplicative.ofAdd (w : Vmod)) : ↥V) : G),
        Subgroup.mem_inf.2 ⟨(e.symm (Multiplicative.ofAdd (w : Vmod))).2,
          Subgroup.mem_centralizer_iff.2 fun b hb =>
            (uc22p22w_fix_iff hV e ρ hc ⟨b, hBM hb⟩ w).1 (w.2 _ (hmem b hb))⟩⟩
      invFun := fun v => ⟨Multiplicative.toAdd (e ⟨(v : G), (Subgroup.mem_inf.1 v.2).1⟩), ?_⟩
      left_inv := fun w => ?_
      right_inv := fun v => ?_ }
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    have hv := (Subgroup.mem_inf.1 v.2).2
    refine (uc22p22w_fix_iff hV e ρ hc x _).2 ?_
    simpa using (Subgroup.mem_centralizer_iff.1 hv (x : G) hx)
  · apply Subtype.ext
    simp
  · apply Subtype.ext
    simp

theorem uc22p22w_card_subgroupOf (H K : Subgroup G) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥(K ⊓ H) := by
  rw [inf_comm, ← Subgroup.subgroupOf_map_subtype H K]
  exact (Subgroup.card_subtype K _).symm

theorem uc22p22w_card_mul (hV : M ≤ normalizer (V : Set G)) {B : Subgroup G} (hBM : B ≤ M) :
    Nat.card ↥(mbarImage M V B) * Nat.card ↥(B ⊓ centralizer (V : Set G)) = Nat.card ↥B := by
  have h1 := uc22br4_card_mbarImage M V B hV hBM
  have h2 := Subgroup.card_mul_index ((centralizer (V : Set G)).subgroupOf B)
  rw [uc22p22w_card_subgroupOf] at h2
  rw [h1, mul_comm]
  exact h2

end Dictionary

theorem uc22p22w_inequality (D : Data G) {A B : Subgroup G} (hAT : A ≤ D.T)
    (hAel : IsElemAbelian 2 A)
    (hAmax : ∀ B : Subgroup G, B ≤ D.T → IsElemAbelian 2 B → Nat.card B ≤ Nat.card A)
    (hBA : B ≤ A) :
    Nat.card ↥B * Nat.card ↥(D.U ⊓ centralizer (B : Set G)) ≤
      Nat.card ↥A * Nat.card ↥(D.U ⊓ centralizer (A : Set G)) := by
  obtain ⟨hU1, hUel⟩ := uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM
  have hUT : D.U ≤ D.T := (hU1.trans inf_le_left).trans (uc22p22e_pCoreOf_le_T D)
  set C : Subgroup G := D.U ⊓ centralizer (B : Set G) with hC
  have hBel : IsElemAbelian 2 B := hAel.mono hBA
  have hCel : IsElemAbelian 2 C := hUel.mono inf_le_left
  have hcomm : ∀ a ∈ B, ∀ c ∈ C, a * c = c * a := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 a ha
  have hQel : IsElemAbelian 2 (B ⊔ C) := IsElemAbelian.sup_of_commute hBel hCel hcomm
  have hQT : B ⊔ C ≤ D.T := sup_le (hBA.trans hAT) (inf_le_left.trans hUT)
  have hQA : Nat.card ↥(B ⊔ C) ≤ Nat.card A := hAmax _ hQT hQel
  have hBN : B ≤ normalizer (C : Set G) := by
    intro b hb
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hcomm b hb c hc).symm
  have hprod := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hBN
  have hinf : Nat.card ↥(B ⊓ C) ≤ Nat.card ↥(D.U ⊓ centralizer (A : Set G)) := by
    refine Subgroup.card_le_of_le ?_
    intro x hx
    obtain ⟨hxB, hxC⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxC).1,
      Subgroup.mem_centralizer_iff.2 fun a ha => hAel.comm ha (hBA hxB)⟩
  calc Nat.card ↥B * Nat.card ↥C = Nat.card ↥(B ⊔ C) * Nat.card ↥(B ⊓ C) := hprod.symm
    _ ≤ Nat.card ↥A * Nat.card ↥(D.U ⊓ centralizer (A : Set G)) := Nat.mul_le_mul hQA hinf

theorem uc22p22w_offender (D : Data G) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]
    [Finite Umod] (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hρ : ConjModule D.M D.U e ρ) {A : Subgroup G}
    (hAT : A ≤ D.T) (hAel : IsElemAbelian 2 A)
    (hAmax : ∀ B : Subgroup G, B ≤ D.T → IsElemAbelian 2 B → Nat.card B ≤ Nat.card A)
    (hA1 : mbarImage D.M D.U A ≠ ⊥) : mbarImage D.M D.U A ∈ calP ρ := by
  have hV : D.M ≤ normalizer (D.U : Set G) := le_normalizer_uCore D.M D.T
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  refine ⟨hA1, (hAel.subgroupOf D.M).map _, ?_⟩
  intro Bbar hBbar
  let φA := uc22br4_phi D.M D.U A hAM
  set B' : Subgroup G := (Bbar.comap φA).map A.subtype with hB'
  have hB'A : B' ≤ A := Subgroup.map_subtype_le _
  have hB'M : B' ≤ D.M := hB'A.trans hAM
  have hA1B' : A ⊓ centralizer (D.U : Set G) ≤ B' := by
    intro a ha
    have h1 : φA ⟨a, ha.1⟩ = 1 := by
      rw [uc22br4_phi_apply, uc22br_gt_mk_eq_one_iff hV]
      exact ha.2
    refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
    show φA ⟨a, ha.1⟩ ∈ Bbar
    rw [h1]
    exact Subgroup.one_mem _
  have hB'img : mbarImage D.M D.U B' = Bbar := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, hax⟩ := hx
      have hxa : x = ⟨(a : G), hAM a.2⟩ := Subtype.ext hax.symm
      show (QuotientGroup.mk' (kerAct D.M D.U).normalCore) x ∈ Bbar
      rw [hxa]
      exact ha
    · intro y hy
      have hyA : y ∈ (uc22br4_phi D.M D.U A hAM).range := by
        rw [uc22br4_range_phi]
        exact hBbar hy
      obtain ⟨a, rfl⟩ := hyA
      refine ⟨⟨(a : G), hAM a.2⟩, ⟨a, hy, rfl⟩, rfl⟩
  have hB'inf : B' ⊓ centralizer (D.U : Set G) = A ⊓ centralizer (D.U : Set G) :=
    le_antisymm (inf_le_inf_right _ hB'A) (le_inf hA1B' inf_le_right)
  have h1 := uc22p22w_card_mul hV hB'M
  have h2 := uc22p22w_card_mul hV hAM
  have h3 := uc22p22w_card_fixSub hV e ρ hρ hB'M
  have h4 := uc22p22w_card_fixSub hV e ρ hρ hAM
  have h5 := uc22p22w_inequality D hAT hAel hAmax hB'A
  rw [hB'img, hB'inf] at h1
  rw [hB'img] at h3
  have hpos : 0 < Nat.card ↥(A ⊓ centralizer (D.U : Set G)) := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card ↥Bbar * Nat.card ↥(fixSub ρ Bbar) * Nat.card ↥(A ⊓ centralizer (D.U : Set G))
      = (Nat.card ↥Bbar * Nat.card ↥(A ⊓ centralizer (D.U : Set G))) * Nat.card ↥(fixSub ρ Bbar) := by
        ring
    _ = Nat.card ↥B' * Nat.card ↥(D.U ⊓ centralizer (B' : Set G)) := by rw [h1, h3]
    _ ≤ Nat.card ↥A * Nat.card ↥(D.U ⊓ centralizer (A : Set G)) := h5
    _ = (Nat.card ↥(mbarImage D.M D.U A) * Nat.card ↥(A ⊓ centralizer (D.U : Set G))) *
          Nat.card ↥(fixSub ρ (mbarImage D.M D.U A)) := by rw [h2, h4]
    _ = Nat.card ↥(mbarImage D.M D.U A) * Nat.card ↥(fixSub ρ (mbarImage D.M D.U A)) *
          Nat.card ↥(A ⊓ centralizer (D.U : Set G)) := by ring

theorem uc22p22w_image_calP (D : Data G) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]
    [Finite Umod] (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hρ : ConjModule D.M D.U e ρ) {A' : Subgroup G}
    (hA' : CFSG.Quasithin.IsMaxElemAbelian D.M A') :
    mbarImage D.M D.U A' = ⊥ ∨ mbarImage D.M D.U A' ∈ calP ρ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hA'M, hA'el, hA'max⟩ := hA'
  obtain ⟨k, hk, hkA⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6.exists_conj_le_of_isSylowOf D.sylowM
    hA'M (uc22p22e_isPGroup_of_elem hA'el)
  set A : Subgroup G := A'.map (MulAut.conj (k⁻¹ : G)).toMonoidHom with hA
  have hAT : A ≤ D.T := by
    rintro _ ⟨x, hx, rfl⟩
    have := hkA x hx
    simpa using this
  have hAel : IsElemAbelian 2 A := uc22p22e_isElemAbelian_map hA'el _
  have hcard : Nat.card ↥A = Nat.card ↥A' :=
    Subgroup.card_map_of_injective (MulAut.conj (k⁻¹ : G)).injective
  have hAmax : ∀ B : Subgroup G, B ≤ D.T → IsElemAbelian 2 B → Nat.card B ≤ Nat.card A := by
    intro B hBT hBel
    rw [hcard]
    exact hA'max B (hBT.trans D.sylowM.le) hBel
  have hA'eq : A.map (MulAut.conj (k : G)).toMonoidHom = A' := by
    rw [hA, Subgroup.map_map]
    have hcomp : (MulAut.conj (k : G)).toMonoidHom.comp (MulAut.conj (k⁻¹ : G)).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]
  have himg : mbarImage D.M D.U A' = (mbarImage D.M D.U A).map
      (MulAut.conj (QuotientGroup.mk ⟨k, hk⟩ : MBar D.M D.U)).toMonoidHom := by
    have h1 := uc22br4_mbarImage_map_conj D.M D.U A ⟨k, hk⟩
    have h2 : A.map (MulAut.conj ((⟨k, hk⟩ : ↥D.M) : G)).toMonoidHom = A' := hA'eq
    rw [h2] at h1
    exact h1
  by_cases hA1 : mbarImage D.M D.U A = ⊥
  · left
    rw [himg, hA1]
    exact Subgroup.map_bot _
  · right
    have hcalP := uc22p22w_offender D e ρ hρ hAT hAel hAmax hA1
    rw [himg]
    refine ⟨?_, hcalP.2.1.map _, isBestOffender_conj hcalP.2.2 _⟩
    intro hbot
    exact hA1 ((Subgroup.map_eq_bot_iff_of_injective (mbarImage D.M D.U A)
      (MulAut.conj _).injective).1 hbot)

theorem uc22p22w_nbar_eq_iSup (D : Data G) :
    mbarImage D.M D.U (proofN D) =
      ⨆ A : {A : Subgroup G // CFSG.Quasithin.IsMaxElemAbelian D.M A},
        mbarImage D.M D.U (A : Subgroup G) := by
  have h1 : proofN D =
      ⨆ A : {A : Subgroup G // CFSG.Quasithin.IsMaxElemAbelian D.M A}, (A : Subgroup G) := by
    have h0 : jOf D.M = CFSG.Quasithin.thompsonJ D.M :=
      CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ D.M
    show jOf D.M = _
    rw [h0]
    unfold CFSG.Quasithin.thompsonJ
    exact iSup_subtype'
  rw [h1]
  unfold mbarImage
  rw [uc22br4_subgroupOf_iSup D.M _ (fun A => A.2.1), Subgroup.map_iSup]

theorem uc22p22w_nbar_le_hP (D : Data G) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]
    [Finite Umod] (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hρ : ConjModule D.M D.U e ρ) :
    mbarImage D.M D.U (proofN D) ≤ hP ρ := by
  rw [uc22p22w_nbar_eq_iSup]
  refine iSup_le fun A => ?_
  rcases uc22p22w_image_calP D e ρ hρ A.2 with hbot | hmem
  · rw [hbot]
    exact bot_le
  · exact le_iSup₂_of_le (mbarImage D.M D.U (A : Subgroup G)) hmem le_rfl

theorem uc22p22w_hP_ne_bot (D : Data G) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]
    [Finite Umod] (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hρ : ConjModule D.M D.U e ρ)
    (hN : mbarImage D.M D.U (proofN D) ≠ ⊥) : hP ρ ≠ ⊥ := fun h =>
  hN (le_bot_iff.1 (h ▸ uc22p22w_nbar_le_hP D e ρ hρ))

section Restrict

variable {H : Type} [Group H] [Finite H] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

theorem uc22p22w_fixSub_restrict (ρ : Representation (ZMod 2) H W) (N : Subgroup H)
    (B : Subgroup ↥N) : fixSub (ρ.comp N.subtype) B = fixSub ρ (B.map N.subtype) := by
  ext w
  constructor
  · rintro hw _ ⟨b, hb, rfl⟩
    exact hw b hb
  · intro hw b hb
    exact hw _ ⟨b, hb, rfl⟩

theorem uc22p22w_calP_subgroupOf (ρ : Representation (ZMod 2) H W) (N : Subgroup H)
    {X : Subgroup H} (hX : X ∈ calP ρ) (hXN : X ≤ N) :
    X.subgroupOf N ∈ calP (ρ.comp N.subtype) := by
  obtain ⟨hne, hel, hbest⟩ := hX
  have hmap : (X.subgroupOf N).map N.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXN
  refine ⟨?_, hel.subgroupOf N, ?_⟩
  · intro hbot
    apply hne
    rw [← hmap, hbot, Subgroup.map_bot]
  · intro B hB
    have hle : B.map N.subtype ≤ X := by
      rw [← hmap]
      exact Subgroup.map_mono hB
    have h1 := hbest _ hle
    have e1 : Nat.card ↥B = Nat.card ↥(B.map N.subtype) :=
      (Subgroup.card_map_of_injective N.subtype_injective).symm
    have e2 : Nat.card ↥(X.subgroupOf N) = Nat.card ↥X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv
    rw [uc22p22w_fixSub_restrict, uc22p22w_fixSub_restrict, hmap, e1, e2]
    exact h1

end Restrict

theorem uc22p22w_hP_restrict (D : Data G) {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]
    [Finite Umod] (e : ↥D.U ≃* Multiplicative Umod)
    (ρ : Representation (ZMod 2) (MBar D.M D.U) Umod) (hρ : ConjModule D.M D.U e ρ) :
    hP (ρ.comp (mbarImage D.M D.U (proofN D)).subtype) = ⊤ := by
  set Nb := mbarImage D.M D.U (proofN D) with hNb
  rw [eq_top_iff]
  have hXle : ∀ A : {A : Subgroup G // CFSG.Quasithin.IsMaxElemAbelian D.M A},
      mbarImage D.M D.U (A : Subgroup G) ≤ Nb := fun A => by
    rw [hNb, uc22p22w_nbar_eq_iSup]
    exact le_iSup (fun A : {A : Subgroup G // CFSG.Quasithin.IsMaxElemAbelian D.M A} =>
      mbarImage D.M D.U (A : Subgroup G)) A
  have htop : (⊤ : Subgroup ↥Nb) = ⨆ A : {A : Subgroup G // CFSG.Quasithin.IsMaxElemAbelian D.M A},
      (mbarImage D.M D.U (A : Subgroup G)).subgroupOf Nb := by
    rw [← uc22br4_subgroupOf_iSup Nb _ hXle, ← uc22p22w_nbar_eq_iSup D]
    exact (Subgroup.subgroupOf_self Nb).symm
  rw [htop]
  refine iSup_le fun A => ?_
  rcases uc22p22w_image_calP D e ρ hρ A.2 with hbot | hmem
  · rw [hbot]
    simp
  · exact le_iSup₂_of_le _ (uc22p22w_calP_subgroupOf ρ Nb hmem (hXle A)) le_rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22
