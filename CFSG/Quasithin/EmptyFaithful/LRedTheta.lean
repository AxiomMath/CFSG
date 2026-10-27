module

public import CFSG.Quasithin.EmptyFaithful.S153F17
public import CFSG.Quasithin.EmptyFaithful.T1515eC
public import CFSG.Quasithin.Vol2.Ch10SecAShapeCard
public import CFSG.LieType.SteinbergBREvenSymplecticThreeRank
import CFSG.Open.StatedZModTwo
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch11.SecA (le_center_of_normal_ne_top card_range_dvd quotPCore_subgroupOf_equiv
  pRank_subgroupOf_eq map_oPrimeResidualOf_top)

section Theta

variable {G : Type} [Group G]

private theorem lred_conj_mem_theta {A : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    (hx : x ∈ thetaOf A) : g * x * g⁻¹ ∈ thetaOf A := by
  have : thetaOf A ≤ (thetaOf A).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    show g * y * g⁻¹ ∈ thetaOf A
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.1 hg y).1 hy.1, ?_⟩
    rw [← hy.2]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
  exact this hx

private theorem lred_theta_mono {A B : Subgroup G} (h : A ≤ B) : thetaOf A ≤ thetaOf B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

private theorem lred_theta_le_oPrime (H : Subgroup G) : thetaOf H ≤ oPrimeResidualOf 3 H :=
  Subgroup.closure_mono fun _ hx => ⟨hx.1, 1, by simpa using hx.2⟩

private theorem lred_rank_quot [Finite G] {L : Subgroup G} (hr : 2 ≤ CFSG.Open.pRank 3 L) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := ↥L) (p := 2))
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have h3' := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.pCore 2 ↥L) hN
  have h4 := pRank_top_subtype (p := 3) L
  omega

private theorem lred_three_dvd_quot [Finite G] {L : Subgroup G} (hr : 2 ≤ CFSG.Open.pRank 3 L) :
    3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
  refine dvd_trans ?_ (Subgroup.card_subgroup_dvd_card E)
  rw [hE]
  exact dvd_pow_self 3 (by have := lred_rank_quot hr; omega)

private theorem lred_le_thetaOf [Finite G] {L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hr : 2 ≤ CFSG.Open.pRank 3 L)
    (hZ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) < 9) : L ≤ thetaOf L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 ↥L with hQdef
  have hQn : Q.Normal := CFSG.pCore_normal
  set π : ↥L →* ↥L ⧸ Q := QuotientGroup.mk' Q with hπ
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Q)) := by
    have hN : ¬ 3 ∣ Nat.card Q := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := ↥L) (p := 2))
      rw [hQdef, hk]
      intro h
      have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    have h3' := CFSG.SectionRank.pRank_quotient_eq (p := 3) Q hN
    have h4 := pRank_top_subtype (p := 3) L
    omega
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup (↥L ⧸ Q))
  have hE9 : 9 ≤ Nat.card E := by
    rw [hEcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Q)) := Nat.pow_le_pow_right (by norm_num) hrank
  have hZ' : Nat.card (Subgroup.center (↥L ⧸ Q)) < 9 := hZ
  obtain ⟨e, heE, heZ⟩ : ∃ e ∈ E, e ∉ Subgroup.center (↥L ⧸ Q) := by
    by_contra hno
    push Not at hno
    have hle : E ≤ Subgroup.center (↥L ⧸ Q) := fun x hx => hno x hx
    have := Subgroup.card_le_of_le hle
    omega
  have he3 : e ^ 3 = 1 := hE.2 e heE
  have he1 : e ≠ 1 := fun h => heZ (h ▸ Subgroup.one_mem _)
  have heo : orderOf e = 3 := orderOf_eq_prime he3 he1
  obtain ⟨ℓ, hℓ⟩ := QuotientGroup.mk_surjective e
  have hℓ3 : ℓ ^ 3 ∈ Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hℓ]
    exact he3
  obtain ⟨c, hc⟩ := CFSG.pCore_isPGroup (G := ↥L) (p := 2) ⟨ℓ ^ 3, hℓ3⟩
  have hc' : (ℓ ^ 3) ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
  set ℓ' : ↥L := ℓ ^ 2 ^ c with hℓ'
  have hℓ'3 : ℓ' ^ 3 = 1 := by rw [hℓ', ← pow_mul, mul_comm, pow_mul]; exact hc'
  have hπℓ' : (QuotientGroup.mk ℓ' : ↥L ⧸ Q) = e ^ 2 ^ c := by rw [hℓ', QuotientGroup.mk_pow, hℓ]
  have hℓ'1 : ℓ' ≠ 1 := by
    intro h
    rw [h, QuotientGroup.mk_one] at hπℓ'
    have : orderOf e ∣ 2 ^ c := orderOf_dvd_of_pow_eq_one hπℓ'.symm
    rw [heo] at this
    have := Nat.prime_three.dvd_of_dvd_pow this
    omega
  have hord' : orderOf ℓ' = 3 := orderOf_eq_prime hℓ'3 hℓ'1
  have hnc : (QuotientGroup.mk ℓ' : ↥L ⧸ Q) ∉ Subgroup.center (↥L ⧸ Q) := by
    intro hmem
    apply heZ
    rw [hπℓ'] at hmem
    have h4 : (e ^ 2 ^ c) ^ 2 ^ c = e := by
      have h4c : 2 ^ c * 2 ^ c = 3 * (4 ^ c / 3) + 1 := by
        have h1 : 4 ^ c % 3 = 1 := by rw [Nat.pow_mod]; norm_num
        have h2 : 2 ^ c * 2 ^ c = 4 ^ c := by rw [← mul_pow]; norm_num
        rw [h2]
        omega
      rw [← pow_mul, h4c, pow_succ, pow_mul, he3, one_pow, one_mul]
    exact h4 ▸ Subgroup.pow_mem _ hmem _
  set W' : Subgroup ↥L := (thetaOf L).subgroupOf L with hW'
  have hWn : W'.Normal := ⟨fun w hw g => by
    rw [hW', Subgroup.mem_subgroupOf] at hw ⊢
    show (g : G) * (w : G) * (g : G)⁻¹ ∈ thetaOf L
    exact lred_conj_mem_theta (Subgroup.le_normalizer g.2) hw⟩
  have hℓ'W : ℓ' ∈ W' := by
    rw [hW', Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨ℓ'.2, by rw [Subgroup.orderOf_coe]; exact hord'⟩
  have hWmapn : (W'.map π).Normal := hWn.map π (QuotientGroup.mk'_surjective Q)
  have hWtop : W'.map π = ⊤ := by
    by_contra hne
    exact hnc ((le_center_of_normal_ne_top hQ hne) (Subgroup.mem_map_of_mem π hℓ'W))
  have hq2 : IsPGroup 2 (↥L ⧸ W') := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have hg : π g ∈ W'.map π := by rw [hWtop]; trivial
    obtain ⟨w, hw, hwg⟩ := hg
    have hp : (w⁻¹ * g) ∈ Q := by
      rw [← QuotientGroup.eq_one_iff]
      have : π (w⁻¹ * g) = 1 := by rw [map_mul, map_inv, hwg, inv_mul_cancel]
      exact this
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (G := ↥L) (p := 2) ⟨w⁻¹ * g, hp⟩
    refine ⟨k, ?_⟩
    have hk' : (w⁻¹ * g) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hq1 : (QuotientGroup.mk (w⁻¹ * g) : ↥L ⧸ W') = QuotientGroup.mk g := by
      rw [QuotientGroup.eq]
      have := hWn.conj_mem w hw g⁻¹
      simpa [mul_assoc] using this
    rw [← hq1, ← QuotientGroup.mk_pow, hk']
    rfl
  have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  have hWtop' : W' = ⊤ := by
    by_contra hne
    have hnt : Nontrivial (↥L ⧸ W') := by
      obtain ⟨g, hg⟩ : ∃ g : ↥L, g ∉ W' := by
        by_contra h
        push Not at h
        exact hne (eq_top_iff.2 fun x _ => h x)
      exact ⟨⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).1 h)⟩⟩
    have hnil : Group.IsNilpotent (↥L ⧸ W') := hq2.isNilpotent
    have hsolv : Group.IsSolvable (↥L ⧸ W') := inferInstance
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥L ⧸ W')
    have hperfQ : commutator (↥L ⧸ W') = ⊤ := by
      have : Group.IsPerfect (↥L ⧸ W') :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' W') (QuotientGroup.mk'_surjective W')
      exact this.commutator_eq_top
    rw [hperfQ] at hlt
    exact lt_irrefl _ hlt
  intro l hl
  have : (⟨l, hl⟩ : ↥L) ∈ W' := by rw [hWtop']; trivial
  exact Subgroup.mem_subgroupOf.1 this

private theorem lred_thetaOf_eq_of_oPrime [Finite G] {I L : Subgroup G} (hLI : L ≤ I)
    (hperf : ⁅L, L⁆ = L) (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hr : 2 ≤ CFSG.Open.pRank 3 L) (hZ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) < 9)
    (h : L = oPrimeResidualOf 3 I) : thetaOf I = L :=
  le_antisymm ((lred_theta_le_oPrime I).trans (le_of_eq h.symm))
    ((lred_le_thetaOf hperf hQ hr hZ).trans (lred_theta_mono hLI))

end Theta

section Types

variable {G : Type} [Group G] [Finite G]

private theorem lred_theta_of_model (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {I L : Subgroup G} (hH : SQTKGroup ↥I) (hL : L ∈ cComp I)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hr : CFSG.Open.pRank 3 L = 2)
    {S : Type} [Group S] [Finite S] (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* S) (hS : A318Exclusion S) :
    thetaOf I = L := by
  have hoP := eq_oPrimeResidualOf_three_of_exclusion hF h36 h38 hH hL hQ e hS
  have hZ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) < 9 := by
    have h1 := Subgroup.map_center_eq e
    rw [hS.center_eq_bot] at h1
    have h2 : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
    rw [h2, Subgroup.card_bot]
    norm_num
  exact lred_thetaOf_eq_of_oPrime (le_of_mem_cComp hL) (perfect_of_mem_cComp hL) hQ (by omega) hZ hoP

private theorem lred_isPSL_two_of_statedSL {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) : IsPSL n 2 1 X :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two hn e

private theorem lred_l3Free_979200 : L3Free1515e 979200 0 :=
  L3Free1515e.of_check (B := 100) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

private theorem lred_a318Exclusion_sp4 {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F))
    (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : A318Exclusion X := by
  have hcard4 : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF]
  have hchar : CharP F 2 := by
    obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
    have hd : ringChar F ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hF, hn]
      exact dvd_pow_self _ n.pos.ne'
    exact ringChar.eq_iff.mp ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hsP : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
      (Or.inl (Or.inr (by rw [hcard4])))
  have hsSp : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    (CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := F) (n := 2) (by norm_num)).symm.isSimpleGroup
  have hsX : IsSimpleGroup X := e.isSimpleGroup
  have hN : Nat.card X = 979200 := by
    rw [Nat.card_congr e.toEquiv, Vol2.Ch10.SecA.card_Sp4_pow (K := F) (n := 2) (by rw [hcard4]; norm_num)]
    norm_num
  exact A318Exclusion.of_card hsX hr hN lred_l3Free_979200

private theorem lred_theta_notHat (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) {I L : Subgroup G} (hH : SQTKGroup ↥I) (hL : L ∈ cComp I)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hr : CFSG.Open.pRank 3 L = 2)
    (hty : IsAltBlockType L 6 ∨ IsAltBlockType L 7 ∨ IsExcA7Block L ∨ IsG2Block L ∨ IsSp4Quot L ∨
      IsLnTwoQuot L 4 ∨ IsLnTwoQuot L 5) : thetaOf I = L := by
  have hrk := lred_rank_quot (L := L) (by omega)
  rcases hty with hA6 | hA7 | hExc | hG2 | hSp4 | hL4 | hL5
  · obtain ⟨e⟩ := quotPCore_equiv_alt_of_isAltBlockType hA6
    exact lred_theta_of_model hF h36 h38 hH hL hQ hr e hK.alt6
  · obtain ⟨e⟩ := quotPCore_equiv_alt_of_isAltBlockType hA7
    exact lred_theta_of_model hF h36 h38 hH hL hQ hr e hK.alt7
  · obtain ⟨-, ⟨α, hs, hk⟩, -⟩ := hExc
    exact lred_theta_of_model hF h36 h38 hH hL hQ hr
      ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective α hs))
      hK.alt7
  · exact lred_theta_of_model hF h36 h38 hH hL hQ hr (MulEquiv.refl _) (hK.u33 _ hG2.2.1)
  · obtain ⟨F, _, _, hF4, ⟨e⟩⟩ := hSp4
    exact lred_theta_of_model hF h36 h38 hH hL hQ hr (MulEquiv.refl _)
      (lred_a318Exclusion_sp4 hF4 e hrk)
  · obtain ⟨e⟩ := hL4
    exact lred_theta_of_model hF h36 h38 hH hL hQ hr (MulEquiv.refl _)
      (hK.l42 _ (lred_isPSL_two_of_statedSL (by norm_num) e))
  · obtain ⟨e⟩ := hL5
    exact lred_theta_of_model hF h36 h38 hH hL hQ hr (MulEquiv.refl _)
      (hK.l52 _ (lred_isPSL_two_of_statedSL (by norm_num) e))

end Types

section Hat

private theorem lred_map_thetaOf_top {G : Type} [Group G] (I : Subgroup G) :
    (thetaOf (⊤ : Subgroup ↥I)).map I.subtype = thetaOf I := by
  rw [thetaOf, thetaOf, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨-, hy⟩, rfl⟩
    exact ⟨y.2, by rw [Subgroup.coe_subtype, Subgroup.orderOf_coe, hy]⟩
  · rintro ⟨hx, hx3⟩
    exact ⟨⟨x, hx⟩, ⟨trivial, by rw [← Subgroup.orderOf_coe]; exact hx3⟩, rfl⟩

private theorem lred_card_statedSU_three {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 q K) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
  CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK

private theorem lred_sl3_ne_1080 {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ≠ 1080 := by
  intro h
  have h8 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h4 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hq10 : q ≤ 10 := by
    by_contra hc
    push Not at hc
    have h1331 : 11 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hc 3
    have hpos : 0 < (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.mul_pos (by omega) (by omega)
    have : q ^ 3 ≤ 1080 := by
      calc q ^ 3 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.le_mul_of_pos_right _ hpos
        _ = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by ring
        _ = 1080 := h
    omega
  interval_cases q <;> omega

private theorem lred_su3_ne_1080 {q : ℕ} (hq : 2 ≤ q) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ≠ 1080 := by
  intro h
  have h8 : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h4 : 4 ≤ q ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hq10 : q ≤ 10 := by
    by_contra hc
    push Not at hc
    have h1331 : 11 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hc 3
    have hpos : 0 < (q ^ 2 - 1) * (q ^ 3 + 1) := Nat.mul_pos (by omega) (by omega)
    have : q ^ 3 ≤ 1080 := by
      calc q ^ 3 ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := Nat.le_mul_of_pos_right _ hpos
        _ = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by ring
        _ = 1080 := h
    omega
  interval_cases q <;> omega

private theorem lred_starImage_equiv {H : Type} [Group H] [Finite H] {L : Subgroup H} [L.Normal]
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : IsPGroup 3 ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
    (h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Nonempty (↥(starImage 3 L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  set φ₀ : ↥L →* (↥L ⧸ CFSG.pCore 2 ↥L) := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ₀
  set π₃ := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hπ₃
  let ρ : ↥L →* ↥(starImage 3 L) :=
    (π₃.comp L.subtype).codRestrict (starImage 3 L) (fun x => ⟨x, x.2, rfl⟩)
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : ↥L, x ∈ ρ.ker → (x : H) ∈ CFSG.pPrimeCore 3 H := by
    intro x hx
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    change π₃ (x : H) = 1 at h1
    rwa [hπ₃, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hN3 : Nat.Coprime 3 (Nat.card ρ.ker) := by
    have hle : ρ.ker.map L.subtype ≤ CFSG.pPrimeCore 3 H := by
      rintro _ ⟨x, hx, rfl⟩
      exact hker x hx
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective L.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have hNX : ρ.ker.map φ₀ = ⊥ := by
    have hn : (ρ.ker.map φ₀).Normal :=
      Subgroup.Normal.map inferInstance φ₀ (QuotientGroup.mk'_surjective _)
    have hdvd : Nat.card (ρ.ker.map φ₀) ∣ Nat.card ρ.ker := by
      rw [← MonoidHom.domRestrict_range]
      exact card_range_dvd _
    have hne : ρ.ker.map φ₀ ≠ ⊤ := by
      intro htop
      rw [htop, Subgroup.card_top] at hdvd
      exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right hdvd hN3) h3)
        (by norm_num)
    have hle := le_center_of_normal_ne_top hQ hne
    have hP : IsPGroup 3 ↥(ρ.ker.map φ₀) := hZ.to_le hle
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hP
    have hm0 : m = 0 := by
      by_contra hm0
      have h3m : 3 ∣ Nat.card (ρ.ker.map φ₀) := by
        rw [hm]
        exact dvd_pow_self 3 hm0
      have := (Nat.Coprime.coprime_dvd_right hdvd hN3)
      exact absurd (Nat.Coprime.eq_one_of_dvd this h3m) (by norm_num)
    rw [hm0, pow_zero] at hm
    exact Subgroup.card_eq_one.mp hm
  have hle : ρ.ker ≤ φ₀.ker := by
    intro x hx
    have : φ₀ x ∈ ρ.ker.map φ₀ := Subgroup.mem_map_of_mem φ₀ hx
    rw [hNX, Subgroup.mem_bot] at this
    exact this
  have hle' : φ₀.ker ≤ ρ.ker := by
    intro x hx
    rw [hφ₀, QuotientGroup.ker_mk'] at hx
    rw [MonoidHom.mem_ker]
    refine Subtype.ext ?_
    change π₃ (x : H) = 1
    rw [hπ₃, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h1 : (x : H) ∈ (CFSG.pCore 2 ↥L).map L.subtype := ⟨x, hx, rfl⟩
    exact A318.pCore_two_le_pPrimeCore (p := 3) (by norm_num) (A318.map_pCore_le_pCore L h1)
  have hkereq : ρ.ker = CFSG.pCore 2 ↥L := by
    refine le_antisymm (hle.trans ?_) (by rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]; exact hle')
    rw [hφ₀, QuotientGroup.ker_mk']
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ρ hρ).symm).trans
    (QuotientGroup.quotientMulEquivOfEq hkereq)⟩

private theorem lred_theta_hat (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    {G : Type} [Group G] [Finite G] {I L : Subgroup G} (hH : SQTKGroup ↥I) (hL : L ∈ cComp I)
    (hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hr : CFSG.Open.pRank 3 L = 2)
    (hHat : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) (alternatingGroup (Fin 6))) : thetaOf I = L := by
  classical
  have hLH : L ≤ I := le_of_mem_cComp hL
  obtain ⟨-, hZ3, ⟨eA⟩⟩ := hHat
  have hrk := lred_rank_quot (L := L) (by omega)
  have h3X := lred_three_dvd_quot (L := L) (by omega)
  have hSQ := SQTKHyp.of_sqtkGroup ↥I hH
  have hLc := subgroupOf_mem_cComp hL
  obtain ⟨e₀⟩ := quotPCore_subgroupOf_equiv (L := L) hLH
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hQ
  have hr1 : 1 < CFSG.Open.pRank 3 (L.subgroupOf I) := by
    rw [pRank_subgroupOf_eq hLH Nat.prime_three (by norm_num)]
    omega
  have hconc := a318 hF hH (h36 _ hSQ) (h38 _ hSQ) hLc hQ' Nat.prime_three (by norm_num) hr1
  have hLn : (L.subgroupOf I).Normal :=
    A318.normal_of_pRank_gt_one hH (h38 _ hSQ) hLc Nat.prime_three (by norm_num) hr1
  have hcen' : Nat.card (Subgroup.center (↥(L.subgroupOf I) ⧸ CFSG.pCore 2 ↥(L.subgroupOf I))) = 3 := by
    have h1 := Subgroup.map_center_eq e₀
    rw [← hZ3, ← h1, Subgroup.card_map_of_injective e₀.injective]
  have hZ3' : IsPGroup 3 ↥(Subgroup.center
      (↥(L.subgroupOf I) ⧸ CFSG.pCore 2 ↥(L.subgroupOf I))) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [hcen']; norm_num)
  have h3X' : 3 ∣ Nat.card (↥(L.subgroupOf I) ⧸ CFSG.pCore 2 ↥(L.subgroupOf I)) := by
    rw [Nat.card_congr e₀.toEquiv]
    exact h3X
  obtain ⟨eS⟩ := lred_starImage_equiv (L := L.subgroupOf I) hQ' hZ3' h3X'
  let eLX : ↥(starImage 3 (L.subgroupOf I)) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) := eS.trans e₀
  rcases hconc with h1 | ⟨-, h2⟩ | ⟨-, -, h3a | h3b⟩
  ·
    have hL_eq : L = oPrimeResidualOf 3 I := by
      rw [← map_oPrimeResidualOf_top, ← h1, Subgroup.map_subgroupOf_eq_of_le hLH]
    exact lred_thetaOf_eq_of_oPrime hLH (perfect_of_mem_cComp hL) hQ (by omega)
      (by rw [hZ3]; norm_num) hL_eq
  ·
    exfalso
    obtain ⟨s, q, -, ⟨r, k, hrp, hk1, hq, hPSL⟩, -⟩ := h2
    have hsimpleS : IsSimpleGroup ↥(starImage 3 (L.subgroupOf I)) := by
      cases s
      · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 r k hPSL).2
      · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 r k hPSL).2
    have hsimpleX : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := eLX.symm.isSimpleGroup
    rcases hsimpleX.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with hb | ht
    · rw [hb, Subgroup.card_bot] at hZ3
      omega
    · obtain ⟨-, -, a, b, hab⟩ := hQ
      have : Subsingleton ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
        rw [ht]
        exact QuotientGroup.subsingleton_quotient_top
      exact hab (Subsingleton.elim _ _)
  ·
    have : L = thetaOf I := by
      rw [← lred_map_thetaOf_top, ← h3a, Subgroup.map_subgroupOf_eq_of_le hLH]
    exact this.symm
  ·
    exfalso
    obtain ⟨s, q, x, hSL, -⟩ := h3b
    have hX1080 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
      have h2 : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 360 := by
        rw [Nat.card_congr eA.toEquiv, card_alt_fin1515e 6 (by norm_num)]
        norm_num [Nat.factorial]
      rw [h1, h2, hZ3]
    have hSc : Nat.card ↥(starImage 3 (L.subgroupOf I)) = 1080 := by
      rw [Nat.card_congr eLX.toEquiv, hX1080]
    cases s
    ·
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hSL
      have h1 : 1 < q ^ 2 := hK ▸ Finite.one_lt_card
      have hq2 : 2 ≤ q := by
        rcases Nat.lt_or_ge q 2 with hlt | hge
        · interval_cases q <;> simp at h1
        · exact hge
      have h2 := lred_card_statedSU_three hK
      rw [← Nat.card_congr e.toEquiv, hSc] at h2
      exact lred_su3_ne_1080 hq2 h2.symm
    ·
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hSL
      have h2 := CFSG.SectionRank.OddCover.card_statedSL_three (K := K)
      rw [← Nat.card_congr e.toEquiv, hSc, hK] at h2
      exact lred_sl3_ne_1080 (hK ▸ Finite.one_lt_card) h2.symm

end Hat

theorem thetaEqComponent_of_a318 (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) : ThetaEqComponent := by
  intro G _ _ I L hH hL hQ hr hty
  rcases hty with hA6 | hA7 | hHat | hExc | hG2 | hSp4 | hL4 | hL5
  · exact lred_theta_notHat hF h36 h38 hK hH hL hQ hr (Or.inl hA6)
  · exact lred_theta_notHat hF h36 h38 hK hH hL hQ hr (Or.inr (Or.inl hA7))
  · exact lred_theta_hat hF h36 h38 hH hL hQ hr hHat.2.1
  · exact lred_theta_notHat hF h36 h38 hK hH hL hQ hr (Or.inr (Or.inr (Or.inl hExc)))
  · exact lred_theta_notHat hF h36 h38 hK hH hL hQ hr (Or.inr (Or.inr (Or.inr (Or.inl hG2))))
  · exact lred_theta_notHat hF h36 h38 hK hH hL hQ hr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSp4)))))
  · exact lred_theta_notHat hF h36 h38 hK hH hL hQ hr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL4))))))
  · exact lred_theta_notHat hF h36 h38 hK hH hL hQ hr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL5))))))

end CFSG.Quasithin
