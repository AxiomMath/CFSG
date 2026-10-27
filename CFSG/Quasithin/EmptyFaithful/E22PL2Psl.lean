module

public import CFSG.Quasithin.EmptyFaithful.E22PD1
public import CFSG.Quasithin.EmptyFaithful.E22PGen
public import CFSG.Quasithin.EmptyFaithful.E22PTypeII
public import CFSG.Quasithin.EmptyFaithful.E22PS4
public import CFSG.Quasithin.EmptyFaithful.E22PDick
public import CFSG.Dihedral.PerfectDihedralFourgroupAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourCentralizerEqSelf
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups

public section

namespace CFSG.Quasithin.E22L2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.GorensteinWalter

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem e22pl2psl_eight_dvd {q : ℕ} (hq : q % 8 = 1 ∨ q % 8 = 7) :
    8 ∣ q * ((q ^ 2 - 1) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  have e : ((2 * m + 1) ^ 2 - 1) / 2 = 2 * (m * (m + 1)) := by
    have : (2 * m + 1) ^ 2 - 1 = 2 * (2 * (m * (m + 1))) := by
      have h : (2 * m + 1) ^ 2 = 2 * (2 * (m * (m + 1))) + 1 := by ring
      omega
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [e]
  have h4 : 4 ∣ m * (m + 1) := by
    rcases hq with h | h
    · exact Dvd.dvd.mul_right (by omega : 4 ∣ m) _
    · exact Dvd.dvd.mul_left (by omega : 4 ∣ m + 1) _
  exact Dvd.dvd.mul_left (by obtain ⟨c, hc⟩ := h4; exact ⟨c, by rw [hc]; ring⟩) _

omit [Field K] [Finite K] in
theorem e22pl2psl_isOddPrimePower (hp17 : 17 ≤ p) (hK : Nat.card K = p) :
    IsOddPrimePower (Nat.card K) :=
  ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩

theorem e22pl2psl_eight_dvd_card_q (hodd : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7) : 8 ∣ Nat.card (PSL2 K) := by
  rw [psl2_card_formula K hodd]
  obtain ⟨p, f, hp, hpodd, hf, hpf⟩ := hodd
  have h2 : 2 ∣ Nat.card K ^ 2 - 1 := by
    have hpo : Odd (Nat.card K) := by rw [hpf]; exact hpodd.pow
    obtain ⟨k, hk⟩ := hpo
    rw [hk]
    exact ⟨2 * k * (k + 1), by
      have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
      omega⟩
  rw [Nat.mul_div_assoc _ h2]
  exact e22pl2psl_eight_dvd hq8

theorem e22pl2psl_sylow_dihedral_q (hodd : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7) {T : Subgroup (PSL2 K)}
    (hT : IsSylowIn 2 T ⊤) :
    ∃ (S : Sylow 2 (PSL2 K)) (m : ℕ), (S : Subgroup (PSL2 K)) = T ∧ 2 ≤ m ∧
      Nonempty (↥(S : Subgroup (PSL2 K)) ≃* DihedralGroup (2 ^ m)) := by
  have hindex : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]; exact hT.not_dvd_relIndex
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 (PSL2 K) := hT.isPGroup.toSylow hindex
  obtain ⟨m, hm1, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hodd S
  have hST : (S : Subgroup (PSL2 K)) = T := rfl
  have e' : T ≃* DihedralGroup (2 ^ m) := (MulEquiv.subgroupCongr hST).symm.trans e
  refine ⟨S, m, hST, ?_, ⟨e⟩⟩
  by_contra hm
  have hm1' : m = 1 := by omega
  have hcardT : Nat.card T = 4 := by
    rw [Nat.card_congr e'.toEquiv, DihedralGroup.nat_card, hm1']
    norm_num
  have h8 := e22pl2psl_eight_dvd_card_q hodd hq8
  have hcardS : Nat.card S = 2 ^ (Nat.card (PSL2 K)).factorization 2 :=
    Sylow.card_eq_multiplicity S
  have hS : Nat.card S = 4 := hcardT
  have hfac : 3 ≤ (Nat.card (PSL2 K)).factorization 2 := by
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
      (Nat.card_pos (α := PSL2 K)).ne').mp (by simpa using h8 : 2 ^ 3 ∣ _)
  have : 2 ^ 3 ≤ 2 ^ (Nat.card (PSL2 K)).factorization 2 :=
    Nat.pow_le_pow_right (by norm_num) hfac
  omega

theorem e22pl2psl_centralizer_isSolvable (hodd : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {z : PSL2 K} (hz : orderOf z = 2) :
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set (PSL2 K))) := by
  obtain ⟨p, f, hp, hpodd, hf, hKpf⟩ := hodd
  have : Fact p.Prime := ⟨hp⟩
  have h3 : 3 < p ^ f := hKpf ▸ hcard
  have hodd2 : (p ^ f) % 2 = 1 := Nat.odd_iff.mp hpodd.pow
  obtain ⟨h1, h3'⟩ := CFSG.Walter.psl2_centralizer_involution K hKpf hpodd hf hz
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h | h
  · obtain ⟨-, ⟨e⟩⟩ := h1 h
    have : NeZero ((p ^ f - 1) / 2) := ⟨by omega⟩
    have := CFSG.Walter.isSolvable_dihedralGroup' ((p ^ f - 1) / 2)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨-, ⟨e⟩⟩ := h3' h
    have : NeZero ((p ^ f + 1) / 2) := ⟨by omega⟩
    have := CFSG.Walter.isSolvable_dihedralGroup' ((p ^ f + 1) / 2)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem inEFor_psl2_of_coatom
    (hodd : IsOddPrimePower (Nat.card K))
    (hq8 : Nat.card K % 8 = 1 ∨ Nat.card K % 8 = 7) (hq7 : 7 ≤ Nat.card K)
    (hcoat : ∀ {z : PSL2 K}, orderOf z = 2 → IsCoatom (Subgroup.centralizer ({z} : Set (PSL2 K))))
    {T : Subgroup (PSL2 K)} (hT : IsSylowIn 2 T ⊤) : InEFor 1 ⊤ T := by
  have hcard3 : 3 < Nat.card K := by omega
  have hsimple : IsSimpleGroup (PSL2 K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hperf : Group.IsPerfect (PSL2 K) := psl2_isPerfect_of_card_gt_three K hcard3
  obtain ⟨S, m, hST, hm2, ⟨e⟩⟩ := e22pl2psl_sylow_dihedral_q hodd hq8 hT
  subst hST
  obtain ⟨z, hzT, hz2, hzc, hzV, hAV⟩ := dihedral_sylow_data hm2 e
  have hTD : (S : Subgroup (PSL2 K)) ≤ Subgroup.centralizer ({z} : Set (PSL2 K)) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hzc t ht
  have hDs := e22pl2psl_centralizer_isSolvable hodd hcard3 hz2
  have hDmax := hcoat hz2
  have hsimple' : IsSimpleGroup ↥(⊤ : Subgroup (PSL2 K)) := Subgroup.topEquiv.isSimpleGroup
  have hcen : Subgroup.center (PSL2 K) = ⊥ := psl2_center_eq_bot K
  have hnc : ∃ a b : ↥(⊤ : Subgroup (PSL2 K)), a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    obtain ⟨x, hx⟩ := exists_ne (1 : PSL2 K)
    have hxc : x ∈ Subgroup.center (PSL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := hcomm ⟨y, Subgroup.mem_top y⟩ ⟨x, Subgroup.mem_top x⟩
      exact congrArg Subtype.val this
    rw [hcen, Subgroup.mem_bot] at hxc
    exact hx hxc
  have hCtop : Subgroup.centralizer ((⊤ : Subgroup (PSL2 K)) : Set (PSL2 K)) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
  have hII : ∀ A : Subgroup (PSL2 K), A ≤ (S : Subgroup (PSL2 K)) → Nat.card A = 2 →
      IsE 1 ⊤ (S : Subgroup (PSL2 K)) A ⊤ := fun A hAT hA =>
    isE_one_top_of_almostSimple ⊤ _ A hnc hCtop hT (top_sup_eq _) hAT hA
  refine inEFor_top_of_coatom hT hTD hDs hDmax hII ?_
  intro A hAT hAab hA4
  obtain ⟨hAcard, hAV⟩ := hAV A hAT hAab hA4
  obtain ⟨V', hV'T, hV', hne, hV'N, hVN, hN8, hC, hcomm⟩ :=
    dihedral_kleinFour_partner hm2 e hAT hAV
  have hO2 : pCoreOf 2 (⊤ : Subgroup (PSL2 K)) = ⊥ :=
    pCoreOf_top_eq_bot_of_normal_simple ⊤ hnc hCtop
  have hcent : Subgroup.centralizer (V' : Set (PSL2 K)) = V' :=
    psl2_kleinFour_centralizer_eq_self K hodd V' hV'
  have hsurj := perfect_dihedral_fourgroup_normalizer_surjective S hm2 e V' hV'T hV'
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  exact ⟨Subgroup.normalizer (V' : Set (PSL2 K)),
    isE_one_normalizer_kleinFour hT hO2 hAV hV' hAT hV'T hne hcent hsurj hN8 hVN hC hcomm,
    not_normalizer_le_centralizer hV' hsurj (hzV V' hV'T hV') hz1⟩

theorem inEFor_psl2_prime
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp17 : 17 ≤ p)
    (hK : Nat.card K = p) {T : Subgroup (PSL2 K)} (hT : IsSylowIn 2 T ⊤) :
    InEFor 1 ⊤ T :=
  inEFor_psl2_of_coatom (e22pl2psl_isOddPrimePower hp17 hK) (by rw [hK]; exact hp8)
    (by rw [hK]; exact hp17.trans' (by norm_num))
    (fun hz => psl2_centralizer_involution_isCoatom_pm_one hK hp8 hp17 hz) hT

theorem nParam_psl2_prime_le_one
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp17 : 17 ≤ p)
    (hK : Nat.card K = p) : nParam (⊤ : Subgroup (PSL2 K)) ≤ 1 := by
  obtain ⟨T, hT⟩ := exists_isSylowIn_two (⊤ : Subgroup (PSL2 K))
  have h := (nParam_le_iff (H := (⊤ : Subgroup (PSL2 K))) (n := 1) one_pos).mpr
    ((inE_iff_inEFor hT).mpr (inEFor_psl2_prime hp8 hp17 hK hT))
  simpa using h

end CFSG.Quasithin.E22L2
