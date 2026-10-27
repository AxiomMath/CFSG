module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Z1Card
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoProp
public import CFSG.GroupTheory.Commutator.JoinNormalizer
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecFB
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerMap

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.CGT.Timmesfeld75
open CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem str83G4_commutator_z2_facts
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    ⁅Z2 L1 L2 S, S⁆ ≤ Z1 L1 L2 S ∧
      (∀ x ∈ S, x ∉ Q2 L1 L2 S →
        Z1 L1 L2 S ≤ ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆) := by
  classical
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨V, hVZ, hVc, hnat⟩ :=
    str83G3Output_of_z2Central str83G4Z2Central_holds G L1 L2 S a
      ⟨hF, hB, ha, hSz, hL2, hZI⟩
  have hV : Str83G4V L1 L2 S V a := ⟨hVZ, hVc, hnat⟩
  have hZ1eq : Z1 L1 L2 S = V ⊓ Subgroup.centralizer (S : Set G) :=
    str83G4_z1_eq_inf_centralizer ⟨hF, hB, ha, hSz, hL2, hZI⟩ hV
  have hZ1V : Z1 L1 L2 S ≤ V := by rw [hZ1eq]; exact inf_le_left
  obtain ⟨hstep, hVH, hVea, hdata⟩ := hnat
  obtain ⟨e, ρ0, φ, hcompat, hφnat⟩ := hdata
  obtain ⟨-, hZ1Z2, -, hSQ2, hZ2CSeq⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hcore : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hHleP2 : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hHW : L2 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    hHleP2.trans (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hsylow : IsSylowTwoOf S (L2 ⊔ S) := by
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    have hQ : Q1 L2 L1 S = Q2 L1 L2 S := by simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hQ, show L2 ⊔ Q2 L1 L2 S = L2 ⊔ S from hsup2.symm] at h
    exact h
  let F := GaloisField 2 (2 * a + 1)
  haveI : Fintype F := Fintype.ofFinite _
  let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hVH hVea.isPGroup
  letI : CommGroup (Ch3z.chiefMod ⊥ V) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ V)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstep hVH hE e
  have hρeq : ρ0 = ρ := by
    refine MonoidHom.ext fun g' => LinearMap.ext fun w => ?_
    obtain ⟨h, rfl⟩ := e.surjective g'
    obtain ⟨h', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥(L2 ⊔ S)) h
    have hw : Additive.ofMul w.toMul = w := rfl
    rw [← hw, QuotientGroup.mk'_apply, hcompat h' w.toMul, l2ChiefSectionRep_apply_mk]
  have hnatρ : IsNaturalModule ρ := by
    refine ⟨φ, ?_⟩
    intro g w
    rw [← hρeq]
    exact hφnat g w
  let q : ↥(L2 ⊔ S) →* oTwoQuot ↥(L2 ⊔ S) :=
    QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L2 ⊔ S))
  let A : Subgroup (SL(2, F)) := ((S.subgroupOf (L2 ⊔ S)).map q).map e.toMonoidHom
  have hsylow' : IsSylowTwoOf S (L2 ⊔ S) := hsylow
  obtain ⟨hSH, hSp, hSidx⟩ := hsylow
  let PH : Sylow 2 ↥(L2 ⊔ S) := (hSp.comap_subtype (K := L2 ⊔ S)).toSylow hSidx
  have hPHcoe : (PH : Subgroup ↥(L2 ⊔ S)) = S.subgroupOf (L2 ⊔ S) := IsPGroup.toSylow_coe _ _
  let Pq : Sylow 2 (oTwoQuot ↥(L2 ⊔ S)) :=
    PH.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hPqcoe : (Pq : Subgroup (oTwoQuot ↥(L2 ⊔ S))) =
      (S.subgroupOf (L2 ⊔ S)).map q := by
    change ((PH.mapSurjective (f := q) (QuotientGroup.mk'_surjective _) :
      Sylow 2 (oTwoQuot ↥(L2 ⊔ S))) : Subgroup (oTwoQuot ↥(L2 ⊔ S))) =
      (S.subgroupOf (L2 ⊔ S)).map q
    rw [Sylow.coe_mapSurjective, hPHcoe]
  let PA : Sylow 2 (SL(2, F)) :=
    Pq.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective)
  have hPAcoe : (PA : Subgroup (SL(2, F))) = A := by
    change ((Pq.mapSurjective (f := e.toMonoidHom) (by simpa using e.surjective) :
      Sylow 2 (SL(2, F))) : Subgroup _) = A
    rw [Sylow.coe_mapSurjective, hPqcoe]
  obtain ⟨x, hx⟩ := exists_conjSubgroup_utri_eq_of_sylow PA
  have hxA : ∀ g : SL(2, F), g ∈ A ↔ x⁻¹ * g * x ∈ utri F := by
    intro g
    rw [← hPAcoe, ← hx, mem_conjSubgroup]
  have hAeq : A = (utri F).map (MulAut.conj x).toMonoidHom := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · intro hg
      refine ⟨x⁻¹ * g * x, (hxA g).mp hg, ?_⟩
      change (MulAut.conj x) (x⁻¹ * g * x) = g
      rw [MulAut.conj_apply]
      group
    · rintro ⟨u, hu, rfl⟩
      exact (hxA (x * u * x⁻¹)).mpr (by
        rw [show x⁻¹ * (x * u * x⁻¹) * x = u by group]
        exact hu)
  have hA2 : ∀ g ∈ A, g * g = 1 := by
    intro g hg
    have hg' : x⁻¹ * g * x ∈ utri F := (hxA g).mp hg
    obtain ⟨t, ht⟩ := mem_utri_iff.mp hg'
    have hgeq : g = x * utriElt t * x⁻¹ := by
      calc g = x * (x⁻¹ * g * x) * x⁻¹ := by group
        _ = x * utriElt t * x⁻¹ := by rw [ht]
    rw [hgeq]
    calc (x * utriElt t * x⁻¹) * (x * utriElt t * x⁻¹)
        = x * (utriElt t * utriElt t) * x⁻¹ := by group
      _ = 1 := by rw [utriElt_mul_self]; group
  have hAcard : Nat.card A = Nat.card F := by
    rw [hAeq, Subgroup.card_map_of_injective (MulAut.conj x).injective, card_utri]
  have hfixeq : ∀ {b : SL(2, F)} (hb : b ∈ A) (hb1 : b ≠ 1),
      fixedSub ρ (Subgroup.zpowers b) = fixedSub ρ A :=
    fun hb hb1 =>
      CFSG.RankThree.GF2n.Tim81.Sec2.IsNaturalModule.fixedSub_zpowers_eq hnatρ hA2 hAcard hb hb1
  have hfixAcard : Nat.card ↥(fixedSub ρ A) = Nat.card F :=
    CFSG.RankThree.GF2n.Tim81.Sec2.IsNaturalModule.natCard_fixedSub hnatρ hA2 hAcard
  have hker : q.ker = (Q2 L1 L2 S).subgroupOf (L2 ⊔ S) := by
    rw [QuotientGroup.ker_mk', ← CFSG.openPCoreOf_subgroupOf 2 (L2 ⊔ S), hcore]
  have hmain : ∀ s ∈ S, s ∉ Q2 L1 L2 S → ∀ z ∈ Z2 L1 L2 S,
      z * s * z⁻¹ * s⁻¹ ∈ Z1 L1 L2 S := by
    intro s hsS hsQ z hzZ
    have hsH : s ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) hsS
    let a : SL(2, F) := e (q ⟨s, hsH⟩)
    have haA : a ∈ A := by
      change e (q ⟨s, hsH⟩) ∈ ((S.subgroupOf (L2 ⊔ S)).map q).map e.toMonoidHom
      exact Subgroup.mem_map_of_mem e.toMonoidHom
        (Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hsS))
    have ha1 : a ≠ 1 := by
      intro h1
      apply hsQ
      have hq1 : q ⟨s, hsH⟩ = 1 := by
        apply e.injective
        rw [map_one]
        exact h1
      have hm : (⟨s, hsH⟩ : ↥(L2 ⊔ S)) ∈ q.ker := hq1
      rw [hker] at hm
      exact Subgroup.mem_subgroupOf.mp hm
    let y : G := s * z * s⁻¹ * z⁻¹
    have hyZ : y ∈ Z2 L1 L2 S := by
      have h1 : s * z * s⁻¹ ∈ Z2 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp (hHW hsH) z).mp hzZ
      exact (Z2 L1 L2 S).mul_mem h1 ((Z2 L1 L2 S).inv_mem hzZ)
    have hyV : y ∈ V := hVc s hsH z hzZ
    have hyfix : s * y * s⁻¹ = y := str86_commutator_fixed_of_sq hF hB (by omega) hL2 hsS hzZ
    let P : Subgroup ↥(L2 ⊔ S) := Subgroup.zpowers ⟨s, hsH⟩
    have hPsub : (P.map (L2 ⊔ S).subtype : Subgroup G) = Subgroup.zpowers s := by
      rw [show P = Subgroup.zpowers ⟨s, hsH⟩ from rfl, MonoidHom.map_zpowers]
      rfl
    have hPy : y ∈ Subgroup.centralizer ((P.map (L2 ⊔ S).subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [hPsub] at hh
      have hcomm_s : Commute s y := by
        rw [Commute]
        calc s * y = (s * y * s⁻¹) * s := by group
          _ = y * s := by rw [hyfix]
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (hcomm_s.zpow_left j).eq
    have hPimg : (P.map q).map e.toMonoidHom = Subgroup.zpowers a := by
      rw [show P = Subgroup.zpowers ⟨s, hsH⟩ from rfl, MonoidHom.map_zpowers,
        MonoidHom.map_zpowers]
      rfl
    have hfixmem0 : Additive.ofMul (chiefModBotMulEquiv V ⟨y, hyV⟩) ∈
        fixedSub ρ ((P.map q).map e.toMonoidHom) :=
      (mem_fixSub_chiefMod_bot_iff hstep hVH hE e P ⟨y, hyV⟩).mpr (by
        change (⟨y, hyV⟩ : ↥V).1 ∈ Subgroup.centralizer
          ((P.map (L2 ⊔ S).subtype : Subgroup G) : Set G)
        simpa [hPsub] using hPy)
    rw [hPimg] at hfixmem0
    have hfixmem : Additive.ofMul (chiefModBotMulEquiv V ⟨y, hyV⟩) ∈
        fixedSub ρ (Subgroup.zpowers a) := hfixmem0
    rw [hfixeq haA ha1] at hfixmem
    let P2 : Subgroup ↥(L2 ⊔ S) := S.subgroupOf (L2 ⊔ S)
    have hP2img : (P2.map q).map e.toMonoidHom = A := by
      rw [show P2 = S.subgroupOf (L2 ⊔ S) from rfl]
    have hP2sub : (P2.map (L2 ⊔ S).subtype : Subgroup G) = S :=
      Subgroup.map_subgroupOf_eq_of_le le_sup_right
    have hmem2 : Additive.ofMul (chiefModBotMulEquiv V ⟨y, hyV⟩) ∈
        fixedSub ρ ((P2.map q).map e.toMonoidHom) := by
      rw [hP2img]
      exact hfixmem
    have hycent : y ∈ Subgroup.centralizer (S : Set G) := by
      have h := (mem_fixSub_chiefMod_bot_iff hstep hVH hE e P2 ⟨y, hyV⟩).mp hmem2
      simpa [hP2sub] using h
    have hyZ1 : y ∈ Z1 L1 L2 S := by
      rw [hZ1eq]
      refine Subgroup.mem_inf.mpr ⟨hyV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hycent u hu
    have hinv : z * s * z⁻¹ * s⁻¹ = y⁻¹ := by
      show z * s * z⁻¹ * s⁻¹ = (s * z * s⁻¹ * z⁻¹)⁻¹
      group
    rw [hinv]
    exact (Z1 L1 L2 S).inv_mem hyZ1
  have hcomm_le : ⁅Z2 L1 L2 S, S⁆ ≤ Z1 L1 L2 S := by
    rw [Subgroup.commutator_le]
    intro z hz s hs
    by_cases hsQ : s ∈ Q2 L1 L2 S
    · have hcs : s ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) := hQ2C hsQ
      have h1 : z * s = s * z := (Subgroup.mem_centralizer_iff.mp hcs) z hz
      have hz1 : ⁅z, s⁆ = 1 := by
        rw [commutatorElement_def]
        calc z * s * z⁻¹ * s⁻¹ = (s * z) * z⁻¹ * s⁻¹ := by rw [h1]
          _ = 1 := by group
      rw [hz1]
      exact (Z1 L1 L2 S).one_mem
    · simpa [commutatorElement_def] using hmain s hs hsQ z hz
  refine ⟨hcomm_le, ?_⟩
  intro x hxS hxQ
  have hxH : x ∈ L2 ⊔ S := (le_sup_right : S ≤ L2 ⊔ S) hxS
  let abar : SL(2, F) := e (q ⟨x, hxH⟩)
  have haA : abar ∈ A := by
    change e (q ⟨x, hxH⟩) ∈ ((S.subgroupOf (L2 ⊔ S)).map q).map e.toMonoidHom
    exact Subgroup.mem_map_of_mem e.toMonoidHom
      (Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hxS))
  have ha1 : abar ≠ 1 := by
    intro h1
    apply hxQ
    have hq1 : q ⟨x, hxH⟩ = 1 := by
      apply e.injective
      rw [map_one]
      exact h1
    have hm : (⟨x, hxH⟩ : ↥(L2 ⊔ S)) ∈ q.ker := hq1
    rw [hker] at hm
    exact Subgroup.mem_subgroupOf.mp hm
  have hx2mem : x * x ∈ Q2 L1 L2 S := str86_sq_mem_q2 hF hB (by omega) hL2 hxS
  have hx2cent : x * x ∈ Subgroup.centralizer (V : Set G) := by
    have h := hQ2C hx2mem
    rw [Subgroup.mem_centralizer_iff] at h ⊢
    intro v hv
    exact h v (hVZ hv)
  have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1 hxH
  have hVcomm : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u :=
    fun u hu v hv => (B6.isElemAbelian_iff.mp hVea).1 u hu v hv
  have hPsub : ((Subgroup.zpowers ⟨x, hxH⟩).map (L2 ⊔ S).subtype : Subgroup G) =
      Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hPimg : ((Subgroup.zpowers ⟨x, hxH⟩).map q).map e.toMonoidHom =
      Subgroup.zpowers abar := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hCfix : Nat.card ↥(fixedSub ρ (Subgroup.zpowers abar)) = Nat.card F := by
    rw [hfixeq haA ha1]
    exact hfixAcard
  have hCcard_sub : Nat.card ↥(fixedSub ρ
        (((Subgroup.zpowers ⟨x, hxH⟩).map q).map e.toMonoidHom)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer
        (((Subgroup.zpowers ⟨x, hxH⟩).map (L2 ⊔ S).subtype : Subgroup G) : Set G)) :=
    fixSub_chiefMod_bot_card hstep hVH hE e (Subgroup.zpowers ⟨x, hxH⟩)
  rw [hPimg, hPsub] at hCcard_sub
  have hcentzp : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCcard : Nat.card ↥(V ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card F := by
    rw [← hcentzp]
    exact hCcard_sub.symm.trans hCfix
  have hVcard : Nat.card ↥V = Nat.card F * Nat.card F := by
    calc Nat.card ↥V = Nat.card (Ch3z.chiefMod ⊥ V) :=
          Nat.card_congr (chiefModBotMulEquiv V).toEquiv
      _ = Nat.card (Additive (Ch3z.chiefMod ⊥ V)) :=
          (Nat.card_congr Additive.toMul).symm
      _ = Nat.card (Fin 2 → F) := Nat.card_congr φ.toEquiv
      _ = Nat.card F * Nat.card F := by
          rw [Nat.card_fun, Nat.card_fin, pow_two]
  have hVxcard : Nat.card ↥⁅V, Subgroup.zpowers x⁆ = Nat.card F := by
    have hcard := CFSG.Quasithin.F53.Stellmacher.S43.card_commutator_zpowers
      (W := V) (x := x) hVcomm hxN
    have hmul : Nat.card ↥⁅V, Subgroup.zpowers x⁆ * Nat.card F =
        Nat.card F * Nat.card F := by
      calc Nat.card ↥⁅V, Subgroup.zpowers x⁆ * Nat.card F
          = (V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex V * Nat.card F := by
            rw [hcard]
        _ = (V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex V *
              Nat.card ↥(V ⊓ Subgroup.centralizer ({(x : G)} : Set G)) := by rw [hCcard]
        _ = Nat.card ↥V := by
          simpa [inf_eq_left.mpr inf_le_left] using
            Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer ({x} : Set G)) V
        _ = Nat.card F * Nat.card F := hVcard
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hfixedcard : Nat.card ↥(V ⊓ Subgroup.centralizer (S : Set G)) = 2 ^ (2 * a + 1) :=
    l2_chiefStep_fixedLine_card (n := 2 * a + 1) (by omega) hsylow' hVH hVea hstep e ρ0 φ
      hcompat hφnat
  have hFcard : Nat.card F = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  have hZ1card : Nat.card (Z1 L1 L2 S) = Nat.card F := by
    rw [hZ1eq, hfixedcard, hFcard]
  have hVx_le : ⁅V, Subgroup.zpowers x⁆ ≤ Z1 L1 L2 S := by
    calc ⁅V, Subgroup.zpowers x⁆ ≤ ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ :=
          Subgroup.commutator_mono hVZ le_rfl
      _ ≤ ⁅Z2 L1 L2 S, S⁆ :=
          Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hxS)
      _ ≤ Z1 L1 L2 S := hcomm_le
  have hVx_eq : ⁅V, Subgroup.zpowers x⁆ = Z1 L1 L2 S :=
    Subgroup.eq_of_le_of_card_ge hVx_le (by rw [hVxcard, hZ1card])
  rw [← hVx_eq]
  exact Subgroup.commutator_mono hVZ le_rfl

theorem str83G4_commutator_z2_zpowers
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) {x : G} (hx : x ∈ S)
    (hxQ : x ∉ Q2 L1 L2 S) :
    ⁅Z2 L1 L2 S, Subgroup.zpowers x⁆ = Z1 L1 L2 S := by
  obtain ⟨hle, hge⟩ := str83G4_commutator_z2_facts hfr
  refine le_antisymm ?_ (hge x hx hxQ)
  exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hx)).trans hle

theorem str83G4_commutator_z2_s
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    ⁅Z2 L1 L2 S, S⁆ = Z1 L1 L2 S := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨hle, hge⟩ := str83G4_commutator_z2_facts ⟨hF, hB, ha, hSz, hL2, hZI⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQ1nQ2 : ¬ Q1 L1 L2 S ≤ Q2 L1 L2 S :=
    not_pCoreOf_le_pCoreOf hF hB hS1 (Or.inl ⟨a, ha, hSz⟩)
  obtain ⟨x, hxQ1, hxQ2⟩ := SetLike.not_le_iff_exists.mp hQ1nQ2
  have hxS : x ∈ S := hQ1S hxQ1
  refine le_antisymm hle ?_
  exact (hge x hxS hxQ2).trans
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hxS))

theorem str83G4_commutator_x_q1_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hSP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hZ2P1 : Z2 L1 L2 S ≤ P1 L1 L2 S :=
    (z2_le_q1_of_rq hF hB ha hSz hL2).trans (hQ1S.trans hSP1)
  have hZ1N : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)
  have hQ1N : P1 L1 L2 S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P1 L1 L2 S)
  have hZ1conj : ∀ t : ↥(P1 L1 L2 S),
      (Z1 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom = Z1 L1 L2 S :=
    fun t => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZ1N t.2)
  have hQ1conj : ∀ t : ↥(P1 L1 L2 S),
      (Q1 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom = Q1 L1 L2 S :=
    fun t => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ1N t.2)
  have hZ1mapTop : ∀ t : ↥(P1 L1 L2 S),
      (Z2 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom ≤
        Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    intro t
    have hP1map : (P1 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom = P1 L1 L2 S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer t.2)
    exact ((Subgroup.map_mono hZ2P1).trans (le_of_eq hP1map)).trans hZ1N
  have hcomm : ∀ t : ↥(P1 L1 L2 S),
      ⁅(Z2 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S := by
    intro t
    have hZ2Q1 : ⁅Z2 L1 L2 S, Q1 L1 L2 S⁆ ≤ Z1 L1 L2 S := by
      calc ⁅Z2 L1 L2 S, Q1 L1 L2 S⁆ ≤ ⁅Z2 L1 L2 S, S⁆ :=
            Subgroup.commutator_mono le_rfl hQ1S
        _ = Z1 L1 L2 S := str83G4_commutator_z2_s ⟨hF, hB, ha, hSz, hL2, hZI⟩
    calc ⁅(Z2 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom, Q1 L1 L2 S⁆
        = ⁅(Z2 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom,
            (Q1 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom⁆ := by rw [hQ1conj t]
      _ = (⁅Z2 L1 L2 S, Q1 L1 L2 S⁆).map (MulAut.conj (t : G)).toMonoidHom :=
          (Subgroup.map_commutator _ _ _).symm
      _ ≤ (Z1 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom := Subgroup.map_mono hZ2Q1
      _ = Z1 L1 L2 S := hZ1conj t
  have hXeq : str83X L1 L2 S = ⨆ t : ↥(P1 L1 L2 S),
      (Z2 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom := by
    rw [str83X, CFSG.Quasithin.H13.P31Sec.conjClosure_eq_iSup]
  rw [hXeq]
  exact CFSG.GroupTheory.commutator_iSup_left_le_of_le_normalizer hZ1mapTop hcomm

theorem str83G4_centralizer_x_le
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hZ2 : ¬ L1 ⊔ S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G)) :
    (L1 ⊔ S) ⊓ Subgroup.centralizer (str83X L1 L2 S : Set G) ≤
      Q1 L1 L2 S ⊓ Q2 L1 L2 S := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨-, hZ1Z2, -, hSQ2, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hLhat : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := by
    have h1 : L1 ⊔ S = L1 ⊔ ((S ⊓ L1) ⊔ Q1 L1 L2 S) := congrArg (fun X => L1 ⊔ X) hS1
    rw [h1, ← sup_assoc, show L1 ⊔ (S ⊓ L1) = L1 from sup_eq_left.mpr inf_le_right]
  have hcore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hLhat]
    exact pCoreOf_sup_pCoreOf hF.1
  have hSP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hHleP1 : L1 ⊔ S ≤ P1 L1 L2 S := sup_le le_sup_left hSP1
  have hHX : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    hHleP1.trans (le_normalizer_str83X L1 L2 S)
  let C : Subgroup G := (L1 ⊔ S) ⊓ Subgroup.centralizer (str83X L1 L2 S : Set G)
  have hCH : C ≤ L1 ⊔ S := inf_le_left
  have hCQ1 : C ≤ Q1 L1 L2 S := by
    by_contra hCQ
    have hQ1N : L1 ⊔ S ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
      hHleP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
    have hCN : L1 ⊔ S ≤ Subgroup.normalizer (C : Set G) := by
      intro h hh
      exact A4.mem_normalizer_inf (Subgroup.le_normalizer hh)
        (F7.normalizer_le_normalizer_centralizer (str83X L1 L2 S) (hHX hh))
    have hN_le_H : C ⊔ Q1 L1 L2 S ≤ L1 ⊔ S :=
      sup_le hCH (hQ1S.trans le_sup_right)
    let N : Subgroup G := C ⊔ Q1 L1 L2 S
    have hNnorm : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G) :=
      F1.le_normalizer_sup hCN hQ1N
    let q : ↥(L1 ⊔ S) →* oTwoQuot ↥(L1 ⊔ S) :=
      QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))
    have hker : q.ker = (Q1 L1 L2 S).subgroupOf (L1 ⊔ S) := by
      rw [QuotientGroup.ker_mk', ← CFSG.openPCoreOf_subgroupOf 2 (L1 ⊔ S), hcore]
    have hNsub : (N.subgroupOf (L1 ⊔ S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN_le_H).mpr hNnorm
    let Nbar : Subgroup (oTwoQuot ↥(L1 ⊔ S)) := (N.subgroupOf (L1 ⊔ S)).map q
    have hNbarNorm : Nbar.Normal := hNsub.map q (QuotientGroup.mk'_surjective _)
    have hNbarNe : Nbar ≠ ⊥ := by
      intro hbot
      apply hCQ
      intro c hc
      have hcN : c ∈ N := (le_sup_left : C ≤ C ⊔ Q1 L1 L2 S) hc
      have hcNsub : (⟨c, hN_le_H hcN⟩ : ↥(L1 ⊔ S)) ∈ N.subgroupOf (L1 ⊔ S) := hcN
      have hq1 : q ⟨c, hN_le_H hcN⟩ = 1 := by
        have hmem : q ⟨c, hN_le_H hcN⟩ ∈ Nbar := Subgroup.mem_map_of_mem q hcNsub
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hmemker : (⟨c, hN_le_H hcN⟩ : ↥(L1 ⊔ S)) ∈ q.ker := hq1
      rw [hker] at hmemker
      exact Subgroup.mem_subgroupOf.mp hmemker
    have hsimpleSz : IsSimpleGroup ↥(Sz a) :=
      @MulEquiv.isSimpleGroup _ _ _ _ ((isQuasisimple_sz a ha).2.1)
        (((QuotientGroup.quotientMulEquivOfEq (center_sz a ha)).trans
          QuotientGroup.quotientBot).symm)
    have hsimple : IsSimpleGroup (oTwoQuot ↥(L1 ⊔ S)) := by
      rw [hLhat]
      exact @MulEquiv.isSimpleGroup _ _ _ _ hsimpleSz
        ((oTwoQuotSupEquiv hF.1).trans (Classical.choice hSz))
    have hNbarTop : Nbar = ⊤ :=
      (hsimple.eq_bot_or_eq_top_of_normal Nbar).resolve_left hNbarNe
    have hN_eq : N = L1 ⊔ S := by
      refine le_antisymm hN_le_H ?_
      intro h hh
      let hH : ↥(L1 ⊔ S) := ⟨h, hh⟩
      have hqmem : q hH ∈ Nbar := by rw [hNbarTop]; exact Subgroup.mem_top _
      obtain ⟨n, hnN, hnq⟩ := Subgroup.mem_map.mp hqmem
      have hq1 : q (hH * n⁻¹) = 1 := by
        rw [map_mul, map_inv, hnq, mul_inv_cancel]
      have hmemker : (hH * n⁻¹ : ↥(L1 ⊔ S)) ∈ q.ker := hq1
      rw [hker] at hmemker
      have hmemQ : h * (n : G)⁻¹ ∈ Q1 L1 L2 S := Subgroup.mem_subgroupOf.mp hmemker
      have heq : h = (h * (n : G)⁻¹) * (n : G) := by group
      rw [heq]
      exact N.mul_mem ((le_sup_right : Q1 L1 L2 S ≤ C ⊔ Q1 L1 L2 S) hmemQ) hnN
    have hXZ1 : ⁅str83X L1 L2 S, N⁆ ≤ Z1 L1 L2 S := by
      refine CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer ?_ ?_ ?_ ?_
      · exact hCH.trans (hHleP1.trans
          (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)))
      · exact (hQ1S.trans hSP1).trans
          (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S))
      · have hXC : ⁅str83X L1 L2 S, C⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
        rw [hXC]
        exact bot_le
      · exact str83G4_commutator_x_q1_le ⟨hF, hB, ha, hSz, hL2, hZI⟩
    have hZN : ⁅Z2 L1 L2 S, N⁆ ≤ Z2 L1 L2 S :=
      (Subgroup.commutator_mono (z2_le_str83X L1 L2 S) le_rfl).trans (hXZ1.trans hZ1Z2)
    rw [hN_eq] at hZN
    exact hZ2 (Subgroup.le_normalizer_iff_commutator_le_left.mpr hZN)
  have hCQ2 : C ≤ Q2 L1 L2 S := by
    have hCS : C ≤ S := hCQ1.trans hQ1S
    have hCcentZ2 : C ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
      (inf_le_right : C ≤ Subgroup.centralizer (str83X L1 L2 S : Set G)).trans
        (Subgroup.centralizer_le (z2_le_str83X L1 L2 S))
    calc C ≤ S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) := le_inf hCS hCcentZ2
      _ = Q2 L1 L2 S := hSQ2
  exact le_inf hCQ1 hCQ2

theorem str83G4_z1_le_center_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    Z1 L1 L2 S ≤ str83X L1 L2 S ⊓
      Subgroup.centralizer (str83X L1 L2 S : Set G) := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨-, hZ1Z2, -, -, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hZ2Q1 : Z2 L1 L2 S ≤ Q1 L1 L2 S := z2_le_q1_of_rq hF hB ha hSz hL2
  have hQ1Z1 : Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P1 L1 L2 S)
  have hZ1Q1 : Z1 L1 L2 S ≤ Subgroup.centralizer (Q1 L1 L2 S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp (hQ1Z1 hq) z hz).symm
  have hZ1Z2C : Z1 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    hZ1Q1.trans (Subgroup.centralizer_le hZ2Q1)
  have hZ1N : P1 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P1 L1 L2 S)
  have hconj : ∀ t : ↥(P1 L1 L2 S), Z1 L1 L2 S ≤
      Subgroup.centralizer ((Z2 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom : Set G) := by
    intro t
    have hmapZ1 : (Z1 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom = Z1 L1 L2 S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZ1N t.2)
    have h := CFSG.GorensteinWalter.centralizer_map_le_of_hom
      (MulAut.conj (t : G)).toMonoidHom (Z2 L1 L2 S) (Z1 L1 L2 S) hZ1Z2C
    rwa [hmapZ1] at h
  have hXeq : str83X L1 L2 S = ⨆ t : ↥(P1 L1 L2 S),
      (Z2 L1 L2 S).map (MulAut.conj (t : G)).toMonoidHom := by
    rw [str83X, CFSG.Quasithin.H13.P31Sec.conjClosure_eq_iSup]
  have hZ1X : Z1 L1 L2 S ≤ Subgroup.centralizer (str83X L1 L2 S : Set G) := by
    rw [hXeq]
    exact CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ hconj
  exact le_inf (hZ1Z2.trans (z2_le_str83X L1 L2 S)) hZ1X

end CFSG.Quasithin.Stroth

end
