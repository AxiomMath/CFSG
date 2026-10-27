module

public import CFSG.Quasithin.H13.L32A721Mc

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (E : Ctx7153 G T L V (hz T V))
include E

omit [Finite G] E in
theorem mk_eq_one_iff_mK (g : ↥(mK T V)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) g = 1 ↔ (g : G) ∈ pCoreOf 2 (mK T V) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact C2Six.mem_pCore_two_iff

theorem pPrimeCore_gamma_eq_bot (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (hC137 : U3.C137Statement) (h56 : AsB56) (h1338 : A6.Stmt13_3_8) :
    CFSG.pPrimeCore 3 (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro Nb hNb hcop
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) with hπ
  set N := (Nb.comap π).map (mK T V).subtype with hN
  have hNK : N ≤ mK T V := Subgroup.map_subtype_le _
  have hmemN : ∀ g : ↥(mK T V), (g : G) ∈ N ↔ π g ∈ Nb := by
    intro g
    constructor
    · rintro ⟨y, hy, hyg⟩
      have : y = g := Subtype.ext hyg
      rw [← this]
      exact hy
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hKN : mK T V ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    refine mem_normalizer_of_conj_mem_721 fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    change g * (y : G) * g⁻¹ ∈ N
    have e : g * (y : G) * g⁻¹ = ((⟨g, hg⟩ * y * (⟨g, hg⟩ : ↥(mK T V))⁻¹ : ↥(mK T V)) : G) := rfl
    rw [e, hmemN, map_mul, map_mul, map_inv]
    exact hNb.conj_mem _ hy _
  have h3 : ¬ 3 ∣ Nat.card ↥N := by
    intro h3
    rw [hN, Subgroup.card_map_of_injective (mK T V).subtype_injective] at h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Nb.comap π)) 3 h3
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hπx : π (x : ↥(mK T V)) ≠ 1 := by
      intro h1
      rw [mk_eq_one_iff_mK] at h1
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (mK T V)) ⟨_, h1⟩
      have hk' : ((x : ↥(mK T V)) : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hx3' : ((x : ↥(mK T V)) : G) ^ 3 = 1 := by
        have := congrArg (fun y : ↥(Nb.comap π) => ((y : ↥(mK T V)) : G)) hx3
        simpa using this
      have hcop2 : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
      have h1' := pow_gcd_eq_one.mpr ⟨hx3', hk'⟩
      rw [hcop2.gcd_eq_one, pow_one] at h1'
      have hx1 : x = 1 := Subtype.ext (Subtype.ext h1')
      rw [hx1, orderOf_one] at hx
      norm_num at hx
    have hx3'' : (x : ↥(mK T V)) ^ 3 = 1 := by
      have := congrArg Subtype.val hx3
      simpa using this
    have hπ3 : π (x : ↥(mK T V)) ^ 3 = 1 := by rw [← map_pow, hx3'', map_one]
    have hord : orderOf (⟨π x, Subgroup.mem_comap.mp x.2⟩ : ↥Nb) = 3 := by
      refine orderOf_eq_prime (Subtype.ext ?_) (fun h1 => hπx (congrArg Subtype.val h1))
      simpa using hπ3
    have h3N : 3 ∣ Nat.card ↥Nb := by rw [← hord]; exact orderOf_dvd_natCard _
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop h3N
  have hN2 := E.isPGroup_of_normal hF hC137 h56 h1338 hNK hKN h3
  have hNO : N ≤ pCoreOf 2 (mK T V) := le_pCoreOf_of_le_normalizer 2 hNK hKN hN2
  refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(mK T V)) y
  exact (mk_eq_one_iff_mK g).mpr (hNO ((hmemN g).mpr hy))

theorem isPGroup_centralizer_kbar (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (hC137 : U3.C137Statement) (h56 : AsB56) (h1338 : A6.Stmt13_3_8) :
    IsPGroup 3 ↥(Subgroup.centralizer ((modO2Image (mK T V) (kz T V) :
      Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
        Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V)))) := by
  have : (modO2Image (mK T V) (kz T V)).Normal := kbar_normal
  exact isPGroup_three_centralizer E.pRank_gamma_le
    (E.pPrimeCore_gamma_eq_bot hF hC137 h56 h1338) E.isPOnePlusTwo_kbar

theorem pCoreOf_mK_le_hz : pCoreOf 2 (mK T V) ≤ pCoreOf 2 (hz T V) :=
  le_pCoreOf_of_le_normalizer 2
    ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf E.isSylowTwoOf_mK).trans E.t_le_hz)
    (E.hz_le_mK.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem pCoreOf_mK_eq (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (hC137 : U3.C137Statement) (h56 : AsB56) (h1338 : A6.Stmt13_3_8) :
    pCoreOf 2 (mK T V) = pCoreOf 2 (hz T V) := by
  refine le_antisymm E.pCoreOf_mK_le_hz fun q hq => ?_
  have hqK : q ∈ mK T V := E.hz_le_mK (pCoreOf_le 2 _ hq)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥(mK T V)) with hπ
  have hOK : pCoreOf 2 (kz T V) ≤ pCoreOf 2 (mK T V) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans kz_le_mK)
      (normalizer_le_normalizer_pCoreOf 2 _) (pCoreOf_isPGroup 2 _)
  have hqC : π ⟨q, hqK⟩ ∈ Subgroup.centralizer ((modO2Image (mK T V) (kz T V) :
      Subgroup (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) :
        Set (↥(mK T V) ⧸ CFSG.pCore 2 ↥(mK T V))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_modO2Image_iff.mp hx
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, mk_eq_one_iff_mK]
    have hQ : (k : G) * q * (k : G)⁻¹ * q⁻¹ ∈ pCoreOf 2 (hz T V) :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _
        (oTwoUpper_le _ hk)) q).mp hq) (inv_mem hq)
    have hK : (k : G) * q * (k : G)⁻¹ * q⁻¹ ∈ kz T V := by
      rw [show (k : G) * q * (k : G)⁻¹ * q⁻¹ = (k : G) * (q * (k : G)⁻¹ * q⁻¹) by group]
      exact mul_mem hk ((Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _
        (pCoreOf_le 2 _ hq)) _).mp (inv_mem hk))
    have hO : (k : G) * q * (k : G)⁻¹ * q⁻¹ ∈ pCoreOf 2 (kz T V) := by
      rw [pCoreOf_eq_inf_pCoreOf (oTwoUpper_le _) (le_normalizer_oTwoUpper _)]
      exact ⟨hK, hQ⟩
    have e2 : ((k * ⟨q, hqK⟩ * (⟨q, hqK⟩ * k)⁻¹ : ↥(mK T V)) : G) =
        (k : G) * q * (k : G)⁻¹ * q⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e2]
    exact hOK hO
  obtain ⟨n, hn⟩ := E.isPGroup_centralizer_kbar hF hC137 h56 h1338 ⟨_, hqC⟩
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (hz T V)) ⟨q, hq⟩
  have hn' : (π ⟨q, hqK⟩) ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hm' : (π ⟨q, hqK⟩) ^ 2 ^ m = 1 := by
    rw [← map_pow]
    have : (⟨q, hqK⟩ : ↥(mK T V)) ^ 2 ^ m = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hm)
    rw [this, map_one]
  have hcop : Nat.Coprime (3 ^ n) (2 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
  have h1 := pow_gcd_eq_one.mpr ⟨hn', hm'⟩
  rw [hcop.gcd_eq_one, pow_one, mk_eq_one_iff_mK] at h1
  exact h1

end Ctx7153

end CFSG.Quasithin.H13.L32A
