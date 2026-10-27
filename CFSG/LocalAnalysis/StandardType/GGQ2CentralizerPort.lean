module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSCDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

@[expose] def actionThree {R : Type*} [Group R] (A : Subgroup (MulAut R)) : Prop :=
  ∀ r : R, (∀ a ∈ A, a r = r) → IsPGroup 3 (Subgroup.zpowers r) → MulAut.conj r ∈ A

@[expose] def toralAt {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (hS : GGQTwoSetting p B Bs x L D J)
    (R : Type) [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : Prop :=
  actionThree (ggBeta L θ hN).range

@[expose] def internalAt {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (hS : GGQTwoSetting p B Bs x L D J)
    (R : Type) [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : Prop :=
  ∃ U : Subgroup L,
    IsElemAbelian 3 U ∧ U ≤ Bs.subgroupOf L ∧
      U.map ((MulAut.conj : R →* MulAut R).comp
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))) =
        (ggBeta L θ hN).range ⊓ (MulAut.conj : R →* MulAut R).range ∧
      ∀ z ∈ Subgroup.center L, IsPGroup 3 (Subgroup.zpowers z) → z ∈ U

@[expose] def toralInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (hS : GGQTwoSetting p B Bs x L D J) (R : Type) [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
    toralAt p B Bs x L D J hS R θ hN

@[expose] def internalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (hS : GGQTwoSetting p B Bs x L D J) (R : Type) [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
    x ∈ L → internalAt p B Bs x L D J hS R θ hN

@[expose] def externalTransfer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (hS : GGQTwoSetting p B Bs x L D J) (R : Type) [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
    x ∉ L → toralAt p B Bs x L D J hS R θ hN →
      ∀ j ∈ L, j ∈ Subgroup.centralizer (Bs : Set G) →
        IsPGroup p (Subgroup.zpowers j) → j ∈ Bs

@[expose] def internalTransfer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (hS : GGQTwoSetting p B Bs x L D J) (R : Type) [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
    x ∈ L → toralAt p B Bs x L D J hS R θ hN →
      internalAt p B Bs x L D J hS R θ hN →
      ∀ j ∈ L, j ∈ Subgroup.centralizer (Bs : Set G) →
        IsPGroup p (Subgroup.zpowers j) → j ∈ Bs

theorem largeEvenStdSub_le_left {G : Type*} [Group G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} (h : LargeEvenStdSub p B x L D J) : J ≤ L := by
  unfold LargeEvenStdSub LargeEvenStdSubPre at h
  exact h.1.2.2.2.2.2.1.1.trans inf_le_left

theorem ggqTwoSetting_le_left {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) : J ≤ L :=
  largeEvenStdSub_le_left hS.1.1.2.2

theorem assemble (hExt : externalTransfer) (hInt : internalTransfer) :
    toralInput ∧ internalInput → GGQTwoCentralizerInput := by
  rintro ⟨hTor, hIntIn⟩ G instG instFin p B Bs x L D J hS j hjJ hjCent hjP
  have hJL : J ≤ L := ggqTwoSetting_le_left hS
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGInnerDiagOn.le_normalizer hS.1.2.2.1.1
  have hT : toralAt p B Bs x L D J hS (L ⧸ Subgroup.center L) (MulEquiv.refl _) hN :=
    hTor (G := G) (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
      (hS := hS) (R := L ⧸ Subgroup.center L) (θ := MulEquiv.refl _) (hN := hN)
  by_cases hxL : x ∈ L
  · have hI : internalAt p B Bs x L D J hS (L ⧸ Subgroup.center L) (MulEquiv.refl _) hN :=
      hIntIn (G := G) (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
        (hS := hS) (R := L ⧸ Subgroup.center L) (θ := MulEquiv.refl _) (hN := hN) hxL
    exact hInt (G := G) (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
      (hS := hS) (R := L ⧸ Subgroup.center L) (θ := MulEquiv.refl _) (hN := hN)
      hxL hT hI j (hJL hjJ) hjCent hjP
  · exact hExt (G := G) (p := p) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J)
      (hS := hS) (R := L ⧸ Subgroup.center L) (θ := MulEquiv.refl _) (hN := hN)
      hxL hT j (hJL hjJ) hjCent hjP

theorem actionThree_of_torusCentSC {R : Type} [Group R] (hC : GGTorusCentSC 3 R)
    (A : Subgroup (MulAut R)) (E : Subgroup R) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E)
    (hEA : E.map (MulAut.conj : R →* MulAut R) ≤ A) : actionThree A := by
  intro r hfix hrP
  have hcomm : ∀ e ∈ E, r * e = e * r := by
    intro e he
    have hconjA : MulAut.conj e ∈ A := hEA ⟨e, he, rfl⟩
    have hre : (MulAut.conj e) r = r := hfix _ hconjA
    have h1 : e * r * e⁻¹ = r := by simpa [MulAut.conj_apply] using hre
    have h2 : e * r = r * e := by
      calc e * r = (e * r * e⁻¹) * e := by group
        _ = r * e := by rw [h1]
    exact h2.symm
  have hrE : r ∈ E := by
    refine hC E hE hcard hSC r hcomm ?_
    obtain ⟨k, hk⟩ :=
      IsPGroup.exists_pow_pow_eq_one hrP (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r)
    exact ⟨k, by simpa using congrArg (Subtype.val) hk⟩
  exact hEA ⟨r, hrE, rfl⟩

theorem actionThree_map_congr {R R' : Type*} [Group R] [Group R'] (σ : R ≃* R')
    {A : Subgroup (MulAut R)} (h : actionThree A) :
    actionThree (A.map (MulAut.congr σ).toMonoidHom) := by
  intro r hfix hr
  have hfix' : ∀ a ∈ A, a (σ.symm r) = σ.symm r := by
    intro a ha
    have h1 : (MulAut.congr σ a) r = r := hfix _ ⟨a, ha, rfl⟩
    rw [MulAut.congr_apply] at h1
    have h2 : σ (a (σ.symm r)) = r := h1
    calc a (σ.symm r) = σ.symm (σ (a (σ.symm r))) := (σ.symm_apply_apply _).symm
      _ = σ.symm r := by rw [h2]
  have hr' : IsPGroup 3 (Subgroup.zpowers (σ.symm r)) := by
    have hz : Subgroup.zpowers (σ.symm r) = (Subgroup.zpowers r).map σ.symm.toMonoidHom :=
      (MonoidHom.map_zpowers σ.symm.toMonoidHom r).symm
    rw [hz]
    exact hr.map _
  refine ⟨MulAut.conj (σ.symm r), h _ hfix' hr', ?_⟩
  ext y
  change σ (σ.symm r * σ.symm y * (σ.symm r)⁻¹) = r * y * r⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem actionThree_ggBeta_congr {G : Type} [Group G] {L Bs : Subgroup G} {R R' : Type}
    [Group R] [Group R'] (θ : L ⧸ Subgroup.center L ≃* R) (θ' : L ⧸ Subgroup.center L ≃* R')
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h : actionThree (ggBeta L θ' hN).range) :
    actionThree (ggBeta L θ hN).range := by
  have hrange : (ggBeta L θ hN).range =
      (ggBeta L θ' hN).range.map (MulAut.congr (θ'.symm.trans θ)).toMonoidHom := by
    rw [← MonoidHom.range_comp]
    congr 1
    ext b r
    simp [ggBeta, ggLAut, MulAut.congr_apply]
  rw [hrange]
  exact actionThree_map_congr _ h

theorem ggQ2Cent_exists_lift_three {L : Type} [Group L] [Finite L]
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center L)) (l₀ : L) (hl₀ : l₀ ^ 3 ∈ Subgroup.center L) :
    ∃ l : L, l ^ 3 = 1 ∧ l * l₀⁻¹ ∈ Subgroup.center L := by
  have hcop : Nat.Coprime (Nat.card (Subgroup.center L)) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  obtain ⟨j, _, hjmod⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (k := 3)
      (n := Nat.card (Subgroup.center L)) hcop (by decide)
  obtain ⟨t, ht⟩ : ∃ t, Nat.card (Subgroup.center L) * j = 3 * t + 1 := by
    refine ⟨Nat.card (Subgroup.center L) * j / 3, ?_⟩
    have h := Nat.div_add_mod (Nat.card (Subgroup.center L) * j) 3
    omega
  refine ⟨l₀ ^ (Nat.card (Subgroup.center L) * j), ?_, ?_⟩
  · have hz' : (l₀ ^ 3) ^ Nat.card (Subgroup.center L) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp
        (Subgroup.orderOf_dvd_natCard (Subgroup.center L) hl₀)
    calc
      (l₀ ^ (Nat.card (Subgroup.center L) * j)) ^ 3
          = (l₀ ^ 3) ^ (Nat.card (Subgroup.center L) * j) := by
            rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ = ((l₀ ^ 3) ^ Nat.card (Subgroup.center L)) ^ j := by rw [pow_mul]
      _ = 1 := by rw [hz']; simp
  · have hpow : l₀ ^ (Nat.card (Subgroup.center L) * j) * l₀⁻¹ =
        (l₀ ^ 3) ^ t := by
      rw [ht, pow_succ, pow_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [hpow]
    exact Subgroup.pow_mem (Subgroup.center L) hl₀ t

theorem ggQ2Cent_eq_of_lift_three {L : Type} [Group L] [Finite L]
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center L)) {l w : L} (hl : l ^ 3 = 1) (hw : w ^ 3 = 1)
    (hwl : w * l⁻¹ ∈ Subgroup.center L) : w = l := by
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  let z := w * l⁻¹
  have hzmem : z ∈ Subgroup.center L := hwl
  have hzcomm : Commute z l := (Subgroup.mem_center_iff.mp hzmem l).symm
  have hwz : w = z * l := by
    simp [z]
  have hz3 : z ^ 3 = 1 := by
    have h : w ^ 3 = z ^ 3 := by
      rw [hwz, hzcomm.mul_pow, hl, mul_one]
    simpa [h] using hw
  have hzm : z ^ Nat.card (Subgroup.center L) = 1 := by
    have hdvd : orderOf z ∣ Nat.card (Subgroup.center L) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center L) hzmem
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have hz1 : z = 1 :=
    (pow_eq_one_iff_of_coprime (a := z) hcop).mp ⟨hz3, hzm⟩
  rw [hwz, hz1, one_mul]

theorem conj_mem_range_ggBeta_of_centerPrime {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (h3Z : ¬ 3 ∣ Nat.card (Subgroup.center L))
    {g : R} (hfix : ∀ a ∈ (ggBeta L θ hN).range, a g = g) (hg3 : g ^ 3 = 1) :
    MulAut.conj g ∈ (ggBeta L θ hN).range := by
  let ψ : L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = Subgroup.center L := by
    ext l
    rw [MonoidHom.mem_ker]
    change θ (QuotientGroup.mk l) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  obtain ⟨l₀, hl₀⟩ := hψsurj g
  have hl₀3 : l₀ ^ 3 ∈ Subgroup.center L := by
    rw [← hψker, MonoidHom.mem_ker, map_pow, hl₀, hg3]
  obtain ⟨l, hl3, hll₀⟩ := ggQ2Cent_exists_lift_three h3Z l₀ hl₀3
  have hψl : ψ l = g := by
    have h1 : ψ (l * l₀⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hψker]
      exact hll₀
    rw [map_mul, map_inv, hl₀, mul_inv_eq_one] at h1
    exact h1
  have hlC : (l : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    let w : L := L.normalizerMonoidHom ⟨b, hN hb⟩ l
    have hw : (w : G) = b * l * b⁻¹ := normalizerMonoidHom_coe L ⟨b, hN hb⟩ l
    have hψw : ψ w = g := by
      have h1 := ggLAut_apply L θ ⟨b, hN hb⟩ l
      have h2 : ggLAut L θ ⟨b, hN hb⟩ g = g := hfix _ ⟨⟨b, hb⟩, rfl⟩
      calc ψ w = θ ((w : L) : L ⧸ Subgroup.center L) := rfl
        _ = ggLAut L θ ⟨b, hN hb⟩ (θ (l : L ⧸ Subgroup.center L)) := h1.symm
        _ = ggLAut L θ ⟨b, hN hb⟩ (ψ l) := rfl
        _ = g := by rw [hψl, h2]
    have hw3 : w ^ 3 = 1 := by
      change (L.normalizerMonoidHom ⟨b, hN hb⟩ l) ^ 3 = 1
      rw [show (L.normalizerMonoidHom ⟨b, hN hb⟩ l) ^ 3 =
          L.normalizerMonoidHom ⟨b, hN hb⟩ (l ^ 3) from (map_pow _ l 3).symm, hl3, map_one]
    have hwl : w * l⁻¹ ∈ Subgroup.center L := by
      rw [← hψker, MonoidHom.mem_ker, map_mul, map_inv, hψw, hψl, mul_inv_cancel]
    have hwl' : w = l := ggQ2Cent_eq_of_lift_three h3Z hl3 hw3 hwl
    have hbl : b * (l : G) * b⁻¹ = l := by rw [← hw, hwl']
    calc b * (l : G) = b * l * b⁻¹ * b := by group
      _ = l * b := by rw [hbl]
  have hl3G : (l : G) ^ 3 = 1 := by
    have h1 := congrArg Subtype.val hl3
    simpa using h1
  have hlBs : (l : G) ∈ Bs := hS.1.1.2.1.2.2.2 _ hlC hl3G
  have hβ : ggBeta L θ hN ⟨l, hlBs⟩ = MulAut.conj g := by
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    induction q using QuotientGroup.induction_on with
    | H m =>
      have hm : (L.normalizerMonoidHom ⟨(l : G), hN hlBs⟩ m : L) = l * m * l⁻¹ :=
        Subtype.ext (normalizerMonoidHom_coe L ⟨(l : G), hN hlBs⟩ m)
      have h1 := ggLAut_apply L θ ⟨(l : G), hN hlBs⟩ m
      rw [hm] at h1
      have hψl' : θ (l : L ⧸ Subgroup.center L) = g := hψl
      calc ggBeta L θ hN ⟨l, hlBs⟩ (θ (m : L ⧸ Subgroup.center L))
          = ggLAut L θ ⟨(l : G), hN hlBs⟩ (θ (m : L ⧸ Subgroup.center L)) := rfl
        _ = θ ((l * m * l⁻¹ : L) : L ⧸ Subgroup.center L) := h1
        _ = θ (l : L ⧸ Subgroup.center L) * θ (m : L ⧸ Subgroup.center L) *
            (θ (l : L ⧸ Subgroup.center L))⁻¹ := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul,
            map_mul, map_inv]
        _ = MulAut.conj g (θ (m : L ⧸ Subgroup.center L)) := by
          rw [hψl', MulAut.conj_apply]
  exact ⟨⟨l, hlBs⟩, hβ⟩

end CFSG.StandardType.GGQ2CentPort

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

@[expose] def labelOn (S : LargeEvenLabel → Prop) {G : Type} [Group G]
    (p : ℕ) (Bs L : Subgroup G) : Prop :=
  GGInnerDiagOnLabel (fun p lab => GGLabQTwo p lab ∧ S lab) p Bs L

@[expose] def labelTInput (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (hS : GGQTwoSetting p B Bs x L D J),
    labelOn S p Bs L →
    ∀ (R : Type) [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
      toralAt p B Bs x L D J hS R θ hN

@[expose] def labelTUInput (S : LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (hS : GGQTwoSetting p B Bs x L D J),
    labelOn S p Bs L →
    ∀ (R : Type) [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
      toralAt p B Bs x L D J hS R θ hN ∧ (x ∈ L → internalAt p B Bs x L D J hS R θ hN)

@[expose] def slTwoInput : Prop :=
  labelTInput (fun lab =>
    lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3))

@[expose] def psuAtLeastFiveTwoInput : Prop :=
  labelTUInput (fun lab => lab.tag = .twA ∧ 4 ≤ lab.rank)

@[expose] def spTwoTransportInput : Prop :=
  labelTInput (fun lab => lab.tag = .B ∨ lab.tag = .C)

@[expose] def omegaTwoTransportInput : Prop :=
  labelTInput (fun lab =>
    (lab.tag = .D ∧ 4 ≤ lab.rank) ∨
    (lab.tag = .twD ∧ 4 ≤ lab.rank))

@[expose] def eSevenTwoInput : Prop :=
  labelTInput (fun lab => lab.tag = .E7)

@[expose] def eEightTwoInput : Prop :=
  labelTInput (fun lab => lab.tag = .E8)

@[expose] def twistedESixTwoInput : Prop :=
  labelTUInput (fun lab => lab.tag = .twE6)

@[expose] def f4TwoInput : Prop :=
  labelTInput (fun lab => lab.tag = .F4)

@[expose] def e6TwoInput : Prop :=
  labelTInput (fun lab => lab.tag = .E6)

@[expose] def psuFourTwoInput : Prop :=
  labelTInput (fun lab =>
    (lab.tag = .twA ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 3))

@[expose] def smallLabelsTwoInput : Prop :=
  labelTInput (fun lab =>
    lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
      lab.tag = .G2der ∨ lab.tag = .twF4der ∨ (lab.tag = .twD ∧ lab.rank = 2))

end CFSG.StandardType.GGQ2CentPort

end
