module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordAAux2

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord
open CFSG.StandardType.OrdPNsSp CFSG.StandardType.OrdPNsGen Matrix NoOffOm

variable {G : Type} [Group G] [Finite G]

theorem hdRo7CKCoordAux_centralizer_B_eq {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    B ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  have hSHat : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hyB : y ∈ B := hSHat.2.1
  have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hSHat.2.2.2.1 hk) y (Set.mem_singleton y)).symm
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨hyB, hyC⟩)
  intro b hb
  obtain ⟨hbB, hbC⟩ := hb
  have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G) hbC
  have hcomm : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K := by
    rw [Subgroup.commutator_le]
    intro k hk n hn
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hcommute : Commute k b := Subgroup.mem_centralizer_iff.mp hbC k hk
    change @Bracket.bracket G G commutatorElement k (b ^ j) ∈ LargeEvenPPrimeCoreOf p K
    have h1 : @Bracket.bracket G G commutatorElement k (b ^ j) = 1 :=
      (hcommute.zpow_right j).commutator_eq
    rw [h1]
    exact Subgroup.one_mem _
  exact (hSHat.2.2.2.2.2 b).mp ⟨hbB, hbN, hcomm⟩

theorem hdRo7CKCoordAux_card_centralizer_bs_le_sq {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p ^ 2 := by
  haveI : Fact p.Prime := ⟨hH.1.tableB_facts.1⟩
  let A : Subgroup G := Bs ⊓ Subgroup.centralizer (K : Set G)
  have hDinf : Subgroup.zpowers y = B ⊓ Subgroup.centralizer (K : Set G) :=
    (hdRo7CKCoordAux_centralizer_B_eq hH).symm
  have hDcard : Nat.card ↥(Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hdRo7CKCoordAux_y_pow_eq_one hH) (hdRo7CKCoordAux_y_ne_one hH)
  have hBleBs : B ≤ Bs := hH.1.2.1.1
  have hBscard : Nat.card ↥Bs ≤ p * Nat.card ↥B := hH.1.2.1.2.2.1
  have hDleA : Subgroup.zpowers y ≤ A := by
    change Subgroup.zpowers y ≤ Bs ⊓ Subgroup.centralizer (K : Set G)
    rw [hDinf]
    exact inf_le_inf hBleBs le_rfl
  have hAinfB : A ⊓ B = Subgroup.zpowers y := by
    rw [hDinf]
    apply le_antisymm
    · intro z hz
      exact ⟨hz.2, hz.1.2⟩
    · intro z hz
      exact ⟨⟨hBleBs hz.1, hz.2⟩, hz.1⟩
  have hrel : (Subgroup.zpowers y).relIndex A ≤ B.relIndex Bs := by
    haveI : IsMulCommutative ↥Bs := hH.1.2.1.2.1.1
    haveI : (B.subgroupOf Bs).Normal := Subgroup.normal_of_isMulCommutative (B.subgroupOf Bs)
    have hAB : A ≤ Bs := inf_le_left
    let f0 : ↥A →* ↥Bs ⧸ (B.subgroupOf Bs) :=
      (QuotientGroup.mk' (B.subgroupOf Bs)).comp (Subgroup.inclusion hAB)
    have hker : f0.ker = (Subgroup.zpowers y).subgroupOf A := by
      ext z
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' (B.subgroupOf Bs) (Subgroup.inclusion hAB z) = 1 ↔
        z ∈ (Subgroup.zpowers y).subgroupOf A
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf]
      show ((Subgroup.inclusion hAB z : ↥Bs) : G) ∈ B ↔ (z : G) ∈ Subgroup.zpowers y
      rw [Subgroup.coe_inclusion]
      constructor
      · intro hzB
        have hzAB : (z : G) ∈ A ⊓ B := ⟨z.2, hzB⟩
        rwa [hAinfB] at hzAB
      · intro hzD
        have hzAB : (z : G) ∈ A ⊓ B := by rwa [← hAinfB] at hzD
        exact hzAB.2
    have hcard1 : Nat.card (↥A ⧸ f0.ker) = (Subgroup.zpowers y).relIndex A := by
      rw [hker]
      rfl
    have hcard2 : Nat.card (↥Bs ⧸ (B.subgroupOf Bs)) = B.relIndex Bs := rfl
    calc (Subgroup.zpowers y).relIndex A = Nat.card (↥A ⧸ f0.ker) := hcard1.symm
      _ = Nat.card f0.range :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange f0).toEquiv
      _ ≤ Nat.card (↥Bs ⧸ (B.subgroupOf Bs)) :=
          Nat.card_le_card_of_injective
            (fun w : f0.range => (w : ↥Bs ⧸ (B.subgroupOf Bs)))
            (fun _ _ h => Subtype.ext h)
      _ = B.relIndex Bs := hcard2
  have hAeq : Nat.card ↥A =
      (Subgroup.zpowers y).relIndex A * Nat.card ↥(Subgroup.zpowers y) := by
    rw [← Subgroup.relIndex_mul_card (Subgroup.zpowers y) A, inf_eq_left.mpr hDleA]
  have hBseq : Nat.card ↥Bs = B.relIndex Bs * Nat.card ↥B := by
    rw [← Subgroup.relIndex_mul_card B Bs, inf_eq_left.mpr hBleBs]
  have hpos : 0 < Nat.card ↥B := Nat.card_pos
  have hmain : Nat.card ↥A * Nat.card ↥B ≤ p ^ 2 * Nat.card ↥B := by
    calc Nat.card ↥A * Nat.card ↥B
        = ((Subgroup.zpowers y).relIndex A * Nat.card ↥(Subgroup.zpowers y)) *
            Nat.card ↥B := by rw [hAeq]
      _ ≤ (B.relIndex Bs * Nat.card ↥(Subgroup.zpowers y)) * Nat.card ↥B := by
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hrel)
      _ = Nat.card ↥(Subgroup.zpowers y) * (B.relIndex Bs * Nat.card ↥B) := by ring
      _ = Nat.card ↥(Subgroup.zpowers y) * Nat.card ↥Bs := by rw [hBseq]
      _ ≤ p * (p * Nat.card ↥B) := Nat.mul_le_mul (le_of_eq hDcard) hBscard
      _ = p ^ 2 * Nat.card ↥B := by ring
  exact Nat.le_of_mul_le_mul_right hmain hpos

theorem hdRo7CKCoordAux_card_inf_ge_two {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hZK : Subgroup.center ↥K = ⊥)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹) :
    p ^ 2 ≤ Nat.card ↥(Bs ⊓ K) := by
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  have hsplit := CFSG.StandardType.card_ggBstar_split hH.1.2.1 hZK hBsN hinner
  have hCcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p ^ 2 :=
    hdRo7CKCoordAux_card_centralizer_bs_le_sq hH
  have h4 : p ^ 4 ≤ Nat.card ↥Bs := hdRo7CKCoordAux_card_bstar_ge hH
  have hle : p ^ 2 * p ^ 2 ≤ Nat.card ↥(Bs ⊓ K) * p ^ 2 := by
    calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
      _ ≤ Nat.card ↥Bs := h4
      _ = Nat.card ↥(Bs ⊓ K) *
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := hsplit
      _ ≤ Nat.card ↥(Bs ⊓ K) * p ^ 2 := Nat.mul_le_mul_left _ hCcard
  exact Nat.le_of_mul_le_mul_right hle (pow_pos hp.pos 2)

theorem hdRo7CKCoordAux_card_inf_pow
    (hRig : GGLabelRigidInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowCorank2C p J K)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹) :
    ∃ labK : LargeEvenLabel, LargeEvenInLambda2 labK ∧
      GGHasLabel labK (↥K ⧸ Subgroup.center ↥K) ∧
      (labK.tag = .B ∨ labK.tag = .C) ∧ labK.n = 1 ∧
      5 ≤ labK.rank ∧ Nat.card ↥(Bs ⊓ K) = p ^ labK.rank := by
  have hrow' : GGResRowAt ggRowCorank2C p J K := hrow
  obtain ⟨labJ, labK, hJ2, hK2, hHasJ, hHasK, hp3, htagJ, hnJ, htagK, hnK, hrank⟩ := hrow
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := by omega
  have hnbr : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hperf : commutator ↥K = ⊤ := by
    have hID : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hnbr
    unfold GGInnerDiagOn LargeEvenMarking LargeEvenMarkingLegacy at hID
    exact hID.1
  have h5 : 5 ≤ labK.rank := hdRo7CLCoordAux_rank_ge_five hJ2 hnJ htagJ (by omega)
  have h4 : 4 ≤ labK.rank := by omega
  have h1n : 1 ≤ labK.n := by omega
  have hmodel : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSp labK.rank 2 labK.n :=
    hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC htagK (by omega) h1n hHasK
  obtain ⟨φ, hinj, hrange⟩ :=
    ggSpLiftInput_holds G K labK.rank labK.n h4 hperf hmodel
  haveI : CharP (GaloisField 2 labK.n) 2 :=
    charP_two_of_card (GaloisField.card 2 labK.n (by omega))
  have hZK : Subgroup.center ↥K = ⊥ := hdRo7CKCoordAux_center_K_eq_bot hH hrow'
  obtain ⟨hpow, hcomm, hmax, hcardE⟩ :=
    comap_inf_maximal hH.1.2.1 φ hinj hrange hZK hBsN hinner
  set E : Subgroup (StatedSp labK.rank (GaloisField 2 labK.n)) :=
    (Bs ⊓ K).comap φ with hEdef
  have hcardBs : Nat.card ↥(Bs ⊓ K) = Nat.card ↥E := hcardE.symm
  have hA := genMax_map_statedSpGL (n := labK.rank) (K := GaloisField 2 labK.n) hp hp2 hpow hcomm hmax
  have hΓ : ∀ g : GL (Fin (labK.rank + labK.rank)) (GaloisField 2 labK.n),
      (∀ v w, spFormD labK.rank (GaloisField 2 labK.n) (glin g v) (glin g w) =
        spFormD labK.rank (GaloisField 2 labK.n) v w) →
        g ∈ isoGL (spFormD labK.rank (GaloisField 2 labK.n)) :=
    fun g hg => hg
  have hneE : E ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥E = 1 := by rw [h]; exact Subgroup.card_bot
    have h3 : p ^ 2 ≤ Nat.card ↥(Bs ⊓ K) :=
      hdRo7CKCoordAux_card_inf_ge_two hH hZK hBsN hinner
    rw [hcardBs, h1] at h3
    have h2 : (4 : ℕ) ≤ p ^ 2 := by simpa using Nat.pow_le_pow_left hp.two_le 2
    omega
  have hne : ∃ c ∈ E.map (statedSpGL labK.rank (GaloisField 2 labK.n)), c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hneE
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    have h1 : statedSpGL labK.rank (GaloisField 2 labK.n) s = 1 := hcon _ ⟨s, hs, rfl⟩
    exact statedSpGL_injective (h1.trans (map_one _).symm)
  have hle := card_le_pow_lcm (K := GaloisField 2 labK.n) (d := labK.rank + labK.rank)
    (spFormD_isAlt) hA
  have hge := pow_lcm_le_card (K := GaloisField 2 labK.n) (d := labK.rank + labK.rank)
    (spFormD_isAlt) hA hΓ hne
  have hKcard : Nat.card (GaloisField 2 labK.n) = 2 := by
    rw [GaloisField.card 2 labK.n (by omega), hnK]; norm_num
  have hord : OrdPNS.ordQ (GaloisField 2 labK.n) p = 2 := by
    unfold OrdPNS.ordQ
    rw [hKcard, hp3]
    exact orderOf_eq_prime (p := 2) (by decide) (by decide)
  have hexp : (labK.rank + labK.rank) /
      Nat.lcm 2 (OrdPNS.ordQ (GaloisField 2 labK.n) p) = labK.rank := by
    rw [hord, Nat.lcm_self,
      show labK.rank + labK.rank = 2 * labK.rank by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have hcardmap : Nat.card ↥(E.map (statedSpGL labK.rank (GaloisField 2 labK.n))) =
      Nat.card ↥E := Subgroup.card_map_of_injective statedSpGL_injective
  have hEcard : Nat.card ↥E = p ^ labK.rank := by
    apply le_antisymm
    · rw [hcardmap, hexp] at hle
      exact hle
    · rw [hcardmap, hexp] at hge
      exact hge
  exact ⟨labK, hK2, hHasK, htagK, hnK, h5, by rw [hcardBs, hEcard]⟩

theorem hdRo7CKCoordAux_bstar_centralizer_eq
    (hRig : GGLabelRigidInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowCorank2C p J K)
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  obtain ⟨labK, hlabK, hKlab, htagK, hnK1, h5, hcard_inf⟩ :=
    hdRo7CKCoordAux_card_inf_pow hRig hH hrow hBsN hinner
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hZK : Subgroup.center ↥K = ⊥ := hdRo7CKCoordAux_center_K_eq_bot hH hrow
  have hsplit := CFSG.StandardType.card_ggBstar_split hH.1.2.1 hZK hBsN hinner
  have hupper : Nat.card ↥Bs ≤ p ^ (labK.rank + 1) :=
    hdRo7CKCoordAux_rankUpper hRig hH hrow labK hlabK hKlab htagK hnK1
  have hCcard_le : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p := by
    have hle : p ^ labK.rank * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤
        p ^ labK.rank * p := by
      calc p ^ labK.rank * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G))
          = Nat.card ↥(Bs ⊓ K) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
              rw [hcard_inf]
        _ = Nat.card ↥Bs := hsplit.symm
        _ ≤ p ^ (labK.rank + 1) := hupper
        _ = p ^ labK.rank * p := by rw [pow_succ]
    exact Nat.le_of_mul_le_mul_left hle (pow_pos hp.pos labK.rank)
  have hyC : y ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
    refine ⟨hH.1.2.1.1 hH.2.2.2.2.1.1.2.1, ?_⟩
    change y ∈ Subgroup.centralizer (K : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hH.2.2.2.2.1.1.2.2.2.1 hk) y
      (Set.mem_singleton y)).symm
  have hzy : Subgroup.zpowers y ≤ Bs ⊓ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hyC
  have hzycard : Nat.card ↥(Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hdRo7CKCoordAux_y_pow_eq_one hH) (hdRo7CKCoordAux_y_ne_one hH)
  exact (Subgroup.eq_of_le_of_card_ge hzy (by rw [hzycard]; exact hCcard_le)).symm

theorem hdRo7CKCoordAux_card_inf_ge
    (hRig : GGLabelRigidInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowCorank2C p J K)
    (hZK : Subgroup.center ↥K = ⊥) (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹) :
    p ^ 3 ≤ Nat.card ↥(Bs ⊓ K) := by
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsplit := CFSG.StandardType.card_ggBstar_split hH.1.2.1 hZK hBsN hinner
  have hCeq : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    hdRo7CKCoordAux_bstar_centralizer_eq hRig hH hrow hBsN hinner
  have hCcard : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) = p := by
    rw [hCeq, Nat.card_zpowers,
      orderOf_eq_prime (hdRo7CKCoordAux_y_pow_eq_one hH) (hdRo7CKCoordAux_y_ne_one hH)]
  have h4 : p ^ 4 ≤ Nat.card ↥Bs := hdRo7CKCoordAux_card_bstar_ge hH
  have hle : p ^ 3 * p ≤ Nat.card ↥(Bs ⊓ K) * p := by
    calc p ^ 3 * p = p ^ 4 := by ring
      _ ≤ Nat.card ↥Bs := h4
      _ = Nat.card ↥(Bs ⊓ K) *
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := hsplit
      _ = Nat.card ↥(Bs ⊓ K) * p := by rw [hCcard]
  exact Nat.le_of_mul_le_mul_right hle hp.pos

theorem hdRo7CKCoordAux_signedData_K
    (hRig : GGLabelRigidInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hrow : GGResRowAt ggRowCorank2C p J K)
    (R : Type) [Group R] (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hZK : Subgroup.center ↥K = ⊥) (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ K, ∀ y ∈ K, b * y * b⁻¹ = x * y * x⁻¹)
    (hTSC : GGTorusSignedEltSC p R) :
    hdRo7CLCoordAux_SignedData p Bs K := by
  have hBs : GGBstar p B Bs := hH.1.2.1
  have hEab : IsElemAbelian p (Bs ⊓ K) := hdRo7CKCoordAux_inf_ab hH
  have h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ K) :=
    hdRo7CKCoordAux_card_inf_ge hRig hH hrow hZK hBsN hinner
  let e₁ : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  have hTSC_K : GGTorusSignedEltSC p ↥K :=
    ggTorusSignedEltSC_of_mulEquiv (e₁.symm.trans θ) hTSC
  exact hdRo7CLCoordAux_signedData_of_signedEltSC hBs hZK hBsN hinner hEab h3 hTSC_K

end CFSG.StandardType.HdRo7C

end
