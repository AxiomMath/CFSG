module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W11
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7QA
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4Six
public import CFSG.Quasithin.Vol2.Ch11SecD556A
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7QF
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7W8

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.E3
open scoped commutatorElement

theorem res627QL24_of
    (hK : KnownFacts15122Types)
    (hE : Vol2.Ch11.SecA.FactA318Excl) (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hB56 : AsB56) (hSix : Res624Six) : Res627QL24 := by
  intro G _ _ T M L V h t A D g ht hf U H UH R LU B a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34
    a35 a36 a37 _ _
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUUH : U ≤ UH := a13.1
  have hUHH : UH ≤ H := a13.2.1
  have hHUH : H ≤ Subgroup.normalizer (UH : Set G) := a13.2.2.1
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := a13.2.2.2.1
  have hO2t := a13.2.2.2.2.2
  set Q := ↥UH ⧸ U.subgroupOf UH with hQdef
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun g : MulAut Q => (g : Q → Q)) DFunLike.coe_injective
  have hU4 : Nat.card U = 4 := h.toHyp611Nat.card_fix_of_fieldAut ht hf
  have hU1 : U ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hU4
    omega
  have hVab := h.toHyp611.isElemAbelian
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hVab
  have hU2 : IsPGroup 2 U := hV2.to_le inf_le_left
  have hV16 : Nat.card V = 16 := by
    rw [h.natural.card_eq]
    norm_num
  have hmU : mQuot V U = 2 := by
    have h1 := card_eq_two_pow_mul hV2 (inf_le_left : U ≤ V)
    rw [hV16, hU4] at h1
    have h2 : 2 ^ mQuot V U * 4 = 4 * 4 := by rw [← h1]
    have h3 : 2 ^ mQuot V U = 2 ^ 2 := Nat.eq_of_mul_eq_mul_right (by norm_num) h2
    exact Nat.pow_right_injective (le_refl 2) h3
  have hUH' : U ≤ H := hUUH.trans hUHH
  have hO2H : pCoreOf 2 H ≠ ⊥ := by
    intro h0
    apply hU1
    rw [eq_bot_iff, ← h0]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUH' hHU hU2
  have hSQH : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2H
  have hDL : D ≤ L := a31.trans ((oTwoUpper_le _).trans inf_le_left)
  have hDNU : D ≤ Subgroup.normalizer (U : Set G) :=
    a31.trans ((oTwoUpper_le _).trans inf_le_right)
  have hDNV : D ≤ Subgroup.normalizer (V : Set G) := hDL.trans h.toHyp611.L_le_normalizer
  have hDNH : D ≤ Subgroup.normalizer (H : Set G) := fun d hd =>
    mem_normalizer_centralizer_ch62 (hDNU hd)
  have hDNUH : D ≤ Subgroup.normalizer (UH : Set G) := fun d hd =>
    mem_normalizer_conjClosure_ch62 (hDNV hd) (hDNH hd)
  have hD3 : ∀ d ∈ D, d ^ 3 = 1 := by
    intro d hd
    have := Subgroup.orderOf_dvd_natCard D hd
    rw [a32] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  set HD := H ⊔ D with hHDdef
  have hHDUH : HD ≤ Subgroup.normalizer (UH : Set G) := sup_le hHUH hDNUH
  have hHDU : HD ≤ Subgroup.normalizer (U : Set G) := sup_le hHU hDNU
  set ρ := actQuot UH U H hHUH hHU with hρ
  set ρ' := actQuot UH U HD hHDUH hHDU with hρ'
  set X := ρ.range with hX
  have hρρ' : ∀ (x : G) (hx : x ∈ H), ρ ⟨x, hx⟩ = ρ' ⟨x, (le_sup_left : H ≤ HD) hx⟩ :=
    fun x hx => rfl
  have hconjρ : ∀ (y : G) (hy : y ∈ HD) (x : G) (hx : x ∈ H) (hyx : y * x * y⁻¹ ∈ H),
      ρ' ⟨y, hy⟩ * ρ ⟨x, hx⟩ * (ρ' ⟨y, hy⟩)⁻¹ = ρ ⟨y * x * y⁻¹, hyx⟩ := by
    intro y hy x hx hyx
    rw [hρρ' x hx, hρρ' _ hyx, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hHDNH : HD ≤ Subgroup.normalizer (H : Set G) := sup_le Subgroup.le_normalizer hDNH
  have hρk : ∀ x : ↥H, ρ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := fun x => by
    rw [← a12]
    exact (mem_centralizerMod_iff_actQuot' (hKU := hHUH) (hKZ := hHU) x).symm
  have hkerS : Group.IsSolvable ρ.ker := by
    have h2 : IsPGroup 2 ρ.ker := fun x => by
      obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
        ⟨(x : ↥H), (hρk x).mp x.2⟩
      exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
    have := h2.isNilpotent
    infer_instance
  have hO2X : pCoreOf 2 X = ⊥ := pCoreOf_range_actQuot_eq_bot hO2t
  set As := (A.subgroupOf H).map ρ with hAs
  have hAab : IsElemAbelian 2 A := a16 ▸ isElemAbelian_conjSubgroup627 hVab g
  have hA16 : Nat.card A = 16 := by rw [a16, card_conjSubgroup, hV16]
  have hUH2 : IsPGroup 2 UH := B2F.isPGroup_of_isElemAbelian a9
  have hsq : ∀ q : Q, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H u =>
      rw [← QuotientGroup.mk_pow]
      have : u ^ 2 = 1 := Subtype.ext (by simpa using a9.2 u u.2)
      rw [this]
      rfl
  have hoff := isFFStarOffender627 hHUH hHU hUHH a20 hAab hA16 a23 a30 a36 hUH2 a37
  have hcen := le_centralizer_oddCore627 hHUH hHU hUHH a20 hAab hA16 a23 a30 a36 hsq
  have hAs4 : Nat.card As = 4 := card_offender627 hHUH hHU a20 hA16 a23 a30
  have hidx := index_fixV_offender627 hHUH hHU hUHH a20 hUH2 a37
  have hcomm4 := card_commV_offender627 hHUH hHU a20 a27 a35 a23
  have hmem := mem_aSet_two627 hHUH hHU hUHH a20 hAab hA16 a23 a30 a36
  have hoffY : IsFFStarOffender (cenOdd627 X) As := ⟨le_inf hoff.1 hcen, hoff.2⟩
  have hfix : ∀ a ∈ As, a ≠ 1 → fixV (Subgroup.zpowers a) = fixV As := by
    intro a ha ha1
    have ha2 : a ^ 2 = 1 := hoff.2.2.1.2 a ha
    have hza : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime ha2 ha1
    have hle : Subgroup.zpowers a ≤ As := Subgroup.zpowers_le.mpr ha
    refine hmem.2.2.2 _ hle ?_
    have hrel := Subgroup.relIndex_mul_card (Subgroup.zpowers a) As
    rw [inf_eq_left.mpr hle, hAs4, hza] at hrel
    have hri : (Subgroup.zpowers a).relIndex As = 2 := by omega
    rw [mQuot, hri]
    simp
  have hHV : ¬ H ≤ Subgroup.normalizer (V : Set G) := fun hle => a18 (a20.trans hle)
  have hres : ∀ K K' : Subgroup G, K ∈ cComp H → K' ∈ cComp H → 3 ∣ Nat.card K →
      3 ∣ Nat.card K' → K = K' := fun K K' hK₁ hK₂ h₁ h₂ =>
    hSix G T M L V h U inf_le_left hmU hHV a1 a2 a14 a15 K K' hK₁ hK₂ h₁ h₂
  have huniq := uniq_of_cComp627 ρ hkerS hres
  have hYX : cenOdd627 X ≤ X := inf_le_left
  have hO2Y : pCoreOf 2 (cenOdd627 X) = ⊥ := by
    have hn : ((cenOdd627 X).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr (le_normalizer_cenOdd627 X)
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ X hYX hn
    rw [hO2X] at this
    exact le_bot_iff.mp this
  have hb53 := b53Hyp_ffJ627 ρ hSQH hYX hO2Y
  have hJne : ffJ (cenOdd627 X) ≠ ⊥ := by
    intro h0
    have h1 := B6.le_ffJ hoffY
    rw [h0] at h1
    exact hoffY.2.1 (le_bot_iff.mp h1)
  have h1 := b56Case1_cenOdd627 hoffY hAs4 huniq (hB56 Q hsq _ hJne hb53)
  obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : D = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    rw [this, Subgroup.card_bot] at a32
    omega
  have hd3 : orderOf d = 3 := by
    have h2 := Subgroup.orderOf_dvd_natCard D hdD
    rw [a32] at h2
    rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h3 | h3
    · exact absurd (orderOf_eq_one_iff.mp h3) hd1
    · exact h3
  have hDz : Subgroup.zpowers d = D :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdD) (by rw [a32, Nat.card_zpowers, hd3])
  have hdH : d ∉ H := by
    intro hdH
    have hdC := h.mem_centralizer_V_of_odd627 ht hf (hDNV hdD)
      (Subgroup.le_normalizer (hDL hdD)) hdH (by decide : Odd 3) (hD3 d hdD)
    have h2 : ⁅V, D⁆ = ⊥ := by
      rw [← hDz, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
        Subgroup.zpowers_le]
      exact hdC
    rw [a33] at h2
    rw [h2, Subgroup.card_bot] at hV16
    omega
  have hUHD : U ≤ HD := hUH'.trans le_sup_left
  have hO2HD : pCoreOf 2 HD ≠ ⊥ := by
    intro h0
    apply hU1
    rw [eq_bot_iff, ← h0]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUHD hHDU hU2
  have hSQHD : SQTKGroup ↥HD := sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hO2HD
  have hdHD : d ∈ HD := (le_sup_right : D ≤ HD) hdD
  have hexcl : ∀ L' : Subgroup (MulAut Q), IsSubnormal L' X → CFSG.IsQuasisimple ↥L' →
      A318Exclusion ↥L' → False := fun L' hsn hq hS =>
    false_of_exclusion627 hF h36 h38 le_sup_left hHDNH hSQHD hdHD hdH hd3 ρ hρk hsn hq hS
  have hhat : ∀ L' : Subgroup (MulAut Q), IsSubnormal L' X → CFSG.IsQuasisimple ↥L' →
      IsHat ↥L' ↥(alternatingGroup (Fin 6)) → False := fun L' hsn _ hHat =>
    false_of_hat627 hF h36 h38 le_sup_left hHDNH hSQHD hdHD hdH hd3 ρ hρk hsn hHat
  obtain ⟨hAL, hsnL, hqL, hcases⟩ :=
    ffJ_analysis627 hK hE hoffY hAs4 hfix hcomm4.le hidx.le hexcl hhat h1
  set Ls := fstarJ627 X with hLs
  have hLsX : Ls ≤ X := A3.subnormal_le hsnL
  have h3L : 3 ∣ Nat.card Ls := by
    rcases hcases with hn | hn | hn
    · exact three_dvd_card_of_nat627 (Or.inl ⟨2, hn⟩)
    · exact three_dvd_card_of_nat627 (Or.inr (Or.inl ⟨1, hn⟩))
    · exact three_dvd_card_of_nat627 (Or.inr (Or.inl ⟨2, hn⟩))
  have hNLsH : ∀ (x : G) (hx : x ∈ H),
      ρ ⟨x, hx⟩ ∈ Subgroup.normalizer (Ls : Set (MulAut Q)) := by
    intro x hx
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    exact map_conj_eq_of_uniq627 huniq hsnL hqL h3L
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ⟨⟨x, hx⟩, rfl⟩))
  have hNLsD : ∀ (d' : G) (hd' : d' ∈ D),
      ρ' ⟨d', (le_sup_right : D ≤ HD) hd'⟩ ∈ Subgroup.normalizer (Ls : Set (MulAut Q)) := by
    intro d' hd'
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    refine map_conj_eq_of_uniq627 huniq hsnL hqL h3L ?_
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      have hdx : d' * x * d'⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hDNH hd') x).mp hx
      refine ⟨⟨_, hdx⟩, ?_⟩
      exact (hconjρ d' _ x hx hdx).symm
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  set K : Subgroup G := (Ls.comap ρ).map H.subtype with hKdef
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hmemK : ∀ (x : G) (hx : x ∈ H), x ∈ K ↔ ρ ⟨x, hx⟩ ∈ Ls := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro h2
      exact ⟨⟨x, hx⟩, h2, rfl⟩
  have hOK : pCoreOf 2 H ≤ K := by
    intro x hx
    have hxH := CFSG.LieType.BorelTits.pCoreOf_le 2 H hx
    rw [hmemK x hxH, (hρk ⟨x, hxH⟩).mpr hx]
    exact Ls.one_mem
  have hAK : A ≤ K := fun a ha => (hmemK a (a20 ha)).mpr (hAL ⟨⟨a, a20 ha⟩, ha, rfl⟩)
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    refine mem_normalizer_of_conj_mem627 fun k hk => ?_
    have hkH := hKH hk
    have hxk : x * k * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hx hkH) (H.inv_mem hx)
    rw [hmemK _ hxk]
    have e : ρ ⟨x * k * x⁻¹, hxk⟩ = ρ ⟨x, hx⟩ * ρ ⟨k, hkH⟩ * (ρ ⟨x, hx⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hNLsH x hx) _).mp ((hmemK k hkH).mp hk)
  have hDK : D ≤ Subgroup.normalizer (K : Set G) := by
    intro d' hd'
    refine mem_normalizer_of_conj_mem627 fun k hk => ?_
    have hkH := hKH hk
    have hdk : d' * k * d'⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hDNH hd') k).mp hkH
    rw [hmemK _ hdk, ← hconjρ d' _ k hkH hdk]
    exact (Subgroup.mem_normalizer_iff.mp (hNLsD d' hd') _).mp ((hmemK k hkH).mp hk)
  have hKs : (K.subgroupOf H).map ρ = Ls := by
    have e1 : K.subgroupOf H = Ls.comap ρ :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [e1, Subgroup.map_comap_eq, ← hX]
    exact inf_eq_right.mpr hLsX
  rcases hcases with hnat | hnat | hnat
  ·
    obtain ⟨hZ, hsum⟩ := natural_sl24627 hnat hAL hAs4 hoff.2.2.1 hcomm4.le hidx.le
    refine ⟨K, hOK, hKH, hAK, hHK, hDK, ?_⟩
    show BinaryNaturalSL ((K.subgroupOf H).map ρ) (commV ((K.subgroupOf H).map ρ)) ⊥ 2 2 ∧
      IsIntDirect (commV ((K.subgroupOf H).map ρ)) (fixV ((K.subgroupOf H).map ρ)) ⊤
    rw [hKs]
    exact ⟨hZ ▸ hnat, hsum⟩
  ·
    exfalso
    have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.toHyp611.toHyp5_0_1.T_le_normalizer
    have hQeq : ch6Q T V = pCoreOf 2 (L ⊔ T) := h.toHyp611.centralizer_eq
    have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) (sup_le ?_ ?_)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
      · exact hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
    have htU : ∀ u ∈ U, u * t = t * u := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mp hu.2
    have hdtQ : ∀ d ∈ D, d * t * d⁻¹ * t⁻¹ ∈ ch6Q T V := by
      intro d hd
      have hdL : d ∈ L := hDL hd
      have hcL : d * t * d⁻¹ * t⁻¹ ∈ L := by
        have h1 : t * d⁻¹ * t⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hTL ht) _).mp (L.inv_mem hdL)
        have e : d * t * d⁻¹ * t⁻¹ = d * (t * d⁻¹ * t⁻¹) := by group
        rw [e]
        exact L.mul_mem hdL h1
      have hcU : d * t * d⁻¹ * t⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have hu' : d⁻¹ * u * d ∈ U := by
          simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem
            (hDNU hd)) u).mp hu
        have h1 := htU u hu
        have h2 := htU _ hu'
        calc u * (d * t * d⁻¹ * t⁻¹) = d * ((d⁻¹ * u * d) * t) * d⁻¹ * t⁻¹ := by group
          _ = d * (t * (d⁻¹ * u * d)) * d⁻¹ * t⁻¹ := by rw [h2]
          _ = d * t * d⁻¹ * (u * t⁻¹) := by group
          _ = d * t * d⁻¹ * (t⁻¹ * u) := by
              congr 1
              calc u * t⁻¹ = t⁻¹ * (t * u) * t⁻¹ := by group
                _ = t⁻¹ * (u * t) * t⁻¹ := by rw [h1]
                _ = t⁻¹ * u := by group
          _ = d * t * d⁻¹ * t⁻¹ * u := by group
      have hcV := h.toHyp611Nat.mem_centralizer_V_of_U ht hf hcL hcU
      rw [hQeq]
      exact hO2L (h.toHyp611.toHyp5_0_1.inf_centralizer_le h.toHyp611.L_le_normalizer
        h.toHyp611.module.2.2 ⟨hcL, hcV⟩)
    have hDR : ∀ d ∈ D, d ∈ Subgroup.normalizer (R : Set G) := by
      intro d hd
      have hdQ : d ∈ Subgroup.normalizer (ch6Q T V : Set G) := by
        rw [hQeq]
        exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
          ((le_sup_left : L ≤ L ⊔ T) (hDL hd))
      have hQmap : (ch6Q T V).map (MulAut.conj d).toMonoidHom = ch6Q T V :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hdQ
      have hle : R.map (MulAut.conj d).toMonoidHom ≤ R := by
        rw [Subgroup.map_sup, hQmap]
        refine sup_le le_sup_left ?_
        rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
        have e : (MulAut.conj d).toMonoidHom t = (d * t * d⁻¹ * t⁻¹) * t := by
          simp [MulAut.conj_apply]
        rw [e]
        exact R.mul_mem ((le_sup_left : ch6Q T V ≤ R) (hdtQ d hd))
          ((le_sup_right : Subgroup.zpowers t ≤ R) (Subgroup.mem_zpowers t))
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj d).injective]))
    set Rs := (R.subgroupOf H).map ρ with hRs
    have hRsyl : IsSylowTwoOf Rs X := by
      refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
      · have hR2 : IsPGroup 2 (R.subgroupOf H) := by
          intro x
          obtain ⟨k, hk⟩ := a3.2.1 ⟨(x : ↥H), x.2⟩
          exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
        exact hR2.map ρ
      · intro h2
        apply a3.2.2
        have e : Rs.relIndex X = ((R.subgroupOf H) ⊔ ρ.ker).index := by
          rw [hRs, hX, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
            Subgroup.relIndex_top_right]
        have h3 : 2 ∣ ((R.subgroupOf H) ⊔ ρ.ker).index := e ▸ h2
        exact h3.trans (Subgroup.index_dvd_of_le le_sup_left)
    have hSsyl : IsSylowTwoOf (Rs ⊓ Ls) Ls :=
      RankOneRecog.isSylowTwoOf_inf_of_subnormal hRsyl hLsX (SBc3.isSubnormal_subgroupOf hsnL)
    refine false_of_centralize627 hHUH hHU hHDUH hHDU hKH hAK a34 fun d' hd' => ?_
    show (∀ q ∈ commV ((K.subgroupOf H).map ρ), ρ' ⟨d', (le_sup_right : D ≤ HD) hd'⟩ q = q) ∧
      ∀ x ∈ (K.subgroupOf H).map ρ, ρ' ⟨d', (le_sup_right : D ≤ HD) hd'⟩ * x =
        x * ρ' ⟨d', (le_sup_right : D ≤ HD) hd'⟩
    rw [hKs]
    set δ := ρ' ⟨d', (le_sup_right : D ≤ HD) hd'⟩ with hδ
    have hδR : δ ∈ Subgroup.normalizer (Rs : Set (MulAut Q)) := by
      refine mem_normalizer_of_conj_mem627 (S := Rs) ?_
      rintro _ ⟨⟨r₀, hr₀H⟩, hr₀R, rfl⟩
      have hr₀R' : r₀ ∈ R := hr₀R
      have hdr : d' * r₀ * d'⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hDR d' hd') r₀).mp hr₀R'
      rw [hδ, hconjρ d' _ r₀ hr₀H (a3.1 hdr)]
      exact ⟨⟨_, a3.1 hdr⟩, hdr, rfl⟩
    have hδS : δ ∈ Subgroup.normalizer
        ((Rs ⊓ Ls : Subgroup (MulAut Q)) : Set (MulAut Q)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h2 := Subgroup.mem_normalizer_iff.mp hδR x
      have h3 := Subgroup.mem_normalizer_iff.mp (hNLsD d' hd') x
      simp only [Subgroup.mem_inf]
      exact ⟨fun hx => ⟨h2.mp hx.1, h3.mp hx.2⟩, fun hx => ⟨h2.mpr hx.1, h3.mpr hx.2⟩⟩
    have hδ3 : δ ^ 3 = 1 := by
      rw [hδ, ← map_pow]
      have : (⟨d', (le_sup_right : D ≤ HD) hd'⟩ : ↥HD) ^ 3 = 1 :=
        Subtype.ext (by simpa using hD3 d' hd')
      rw [this, map_one]
    obtain ⟨hc, hfx⟩ := centralizes_of_sl32_627 hnat hqL.1 hSsyl.2.1 hSsyl.2.2 (hNLsD d' hd')
      hδS hδ3
    exact ⟨hfx, hc⟩
  ·
    exfalso
    have hrank : ∀ E : Subgroup G, E ≤ HD → CFSG.Open.IsElemAbelian 3 E → ∀ r,
        Nat.card E = 3 ^ r → r ≤ 2 := fun E hEY hEab r hr =>
      Vol2.Ch11.SecD.le_two_of_elemAbelian h.qtke.2.2 hU1 hU2 Nat.prime_three (by norm_num)
        (hEY.trans hHDU) hEab hr
    exact false_of_sl34G627 hHUH hHU hHDUH hHDU rfl a12 hrank hLsX hnat hdD hdH (hD3 d hdD)
      (hNLsD d hdD)

end CFSG.Quasithin.H13
