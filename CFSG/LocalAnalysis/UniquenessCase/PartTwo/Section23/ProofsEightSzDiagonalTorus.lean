module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightSz
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag1
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Diag2
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightTheta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtySevenBFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_sylowBar2_with_mem {K T₀ : Subgroup G}
    (hS : IsSylowOf 2 (T₀ ⊓ K) K) :
    ∃ U : Sylow 2 (Bar2 K), ∀ l : ↥K,
      (QuotientGroup.mk l : Bar2 K) ∈ (U : Subgroup (Bar2 K)) ↔ (l : G) ∈ T₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  refine ⟨Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)), fun l => ?_⟩
  rw [show ((Q.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))) :
      Subgroup (Bar2 K)) =
      (Q : Subgroup ↥K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) from
    Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) Q, uc22ine229_mk_mem_map_iff Q,
    ← Subgroup.mem_map_iff_mem K.subtype_injective, hQ,
    Subgroup.map_subgroupOf_eq_of_le inf_le_right, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, l.2⟩⟩

private theorem exists_conj_uc22pwIndHom {K T₀ : Subgroup G} (hAut : KSzTwoAut) {a : ℕ}
    (hSz : IsSz (Bar2 K) a) (hT₀ : IsPGroup 2 T₀)
    (hT₀K : T₀ ≤ Subgroup.normalizer (K : Set G)) (U : Sylow 2 (Bar2 K))
    (hU : ∀ l : ↥K, (QuotientGroup.mk l : Bar2 K) ∈ (U : Subgroup (Bar2 K)) ↔ (l : G) ∈ T₀) :
    ∀ g : ↥T₀, ∃ u ∈ (U : Subgroup (Bar2 K)),
      uc22pwIndHom K T₀ hT₀K g = MulAut.conj u := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ : ∀ (g : ↥T₀) (x : Bar2 K),
      x ∈ (U : Subgroup (Bar2 K)) ↔ uc22pwIndHom K T₀ hT₀K g x ∈ (U : Subgroup (Bar2 K)) := by
    intro g x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [uc22pwIndHom_apply, uc22p20uInd_mk, hU, hU]
    exact Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer g.2) l
  have hψ2 : ∀ g : ↥T₀, ∃ n, orderOf (uc22pwIndHom K T₀ hT₀K g) = 2 ^ n := by
    intro g
    have hgdvd : orderOf (uc22pwIndHom K T₀ hT₀K g) ∣ orderOf (g : G) := by
      have h := orderOf_map_dvd (uc22pwIndHom K T₀ hT₀K) g
      simpa [Subgroup.orderOf_coe] using h
    obtain ⟨n, hn⟩ := hT₀ g
    have h2 : orderOf (g : G) ∣ 2 ^ n := by
      have h := orderOf_dvd_of_pow_eq_one hn
      simpa [Subgroup.orderOf_coe] using h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hgdvd.trans h2)
    exact ⟨k, hk⟩
  intro g
  exact hAut (Bar2 K) a hSz U (uc22pwIndHom K T₀ hT₀K g) (hψ2 g) fun x hx => (hψ g x).mp hx

private theorem exists_lift_pow_orderOf_eq {K : Subgroup G} {a r : ℕ} (hSz : IsSz (Bar2 K) a)
    {xbar : Bar2 K} (hr : r.Prime) (hrdvd : r ∣ 2 ^ a - 1) (hxbo : orderOf xbar = r) :
    ∃ (x : ↥K) (c : ℕ), (QuotientGroup.mk x : Bar2 K) = xbar ^ 2 ^ c ∧ orderOf x = r := by
  classical
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective xbar
  have hx₀o : orderOf (QuotientGroup.mk x₀ : Bar2 K) = r := by rw [hx₀]; exact hxbo
  obtain ⟨c, hc⟩ := uc22ine229_exists_pow_orderOf_eq x₀ hr
    (uc22ine229_ne_two (CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz) hrdvd) hx₀o
  refine ⟨x₀ ^ 2 ^ c, c, ?_, hc⟩
  show (QuotientGroup.mk (x₀ ^ 2 ^ c) : Bar2 K) = xbar ^ 2 ^ c
  rw [QuotientGroup.mk_pow, hx₀]

private theorem commutator_mem_sylowBar2 {K T₀ : Subgroup G}
    (hT₀K : T₀ ≤ Subgroup.normalizer (K : Set G)) (U : Sylow 2 (Bar2 K))
    (hconj : ∀ g : ↥T₀, ∃ u ∈ (U : Subgroup (Bar2 K)),
      uc22pwIndHom K T₀ hT₀K g = MulAut.conj u) {x : ↥K}
    (hxN : (QuotientGroup.mk x : Bar2 K) ∈
      Subgroup.normalizer ((U : Subgroup (Bar2 K)) : Set (Bar2 K))) :
    ∀ g : ↥T₀, uc22pwIndHom K T₀ hT₀K g (QuotientGroup.mk x) *
      (QuotientGroup.mk x)⁻¹ ∈ (U : Subgroup (Bar2 K)) := by
  intro g
  obtain ⟨u, hu, huψ⟩ := hconj g
  have h1 : uc22pwIndHom K T₀ hT₀K g (QuotientGroup.mk x) =
      u * QuotientGroup.mk x * u⁻¹ := by rw [huψ, MulAut.conj_apply]
  have h2 : QuotientGroup.mk x * u⁻¹ * (QuotientGroup.mk x)⁻¹ ∈ (U : Subgroup (Bar2 K)) :=
    (Subgroup.mem_normalizer_iff.mp hxN) u⁻¹ |>.mp ((U : Subgroup (Bar2 K)).inv_mem hu)
  have he : u * QuotientGroup.mk x * u⁻¹ * (QuotientGroup.mk x)⁻¹ =
      u * (QuotientGroup.mk x * u⁻¹ * (QuotientGroup.mk x)⁻¹) := by group
  rw [h1, he]
  exact (U : Subgroup (Bar2 K)).mul_mem hu h2

private theorem mem_normalizer_of_commutator_sylowBar2 {K T₀ : Subgroup G}
    (hT₀K : T₀ ≤ Subgroup.normalizer (K : Set G)) (U : Sylow 2 (Bar2 K))
    (hU : ∀ l : ↥K, (QuotientGroup.mk l : Bar2 K) ∈ (U : Subgroup (Bar2 K)) ↔ (l : G) ∈ T₀)
    {x : ↥K} (hcomm : ∀ g : ↥T₀, uc22pwIndHom K T₀ hT₀K g (QuotientGroup.mk x) *
      (QuotientGroup.mk x)⁻¹ ∈ (U : Subgroup (Bar2 K))) :
    (x : G) ∈ Subgroup.normalizer (T₀ : Set G) := by
  have key : ∀ h ∈ T₀, (x : G) * h * (x : G)⁻¹ ∈ T₀ := by
    intro h hh
    have hwK : (h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹ ∈ K := by
      have h1 : (h : G) * (x : G) * (h : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hT₀K hh)) x |>.mp x.2
      exact K.mul_mem h1 (K.inv_mem x.2)
    have hwU : (QuotientGroup.mk (⟨(h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹, hwK⟩ : ↥K) :
        Bar2 K) ∈ (U : Subgroup (Bar2 K)) := by
      have he : (QuotientGroup.mk (⟨(h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹, hwK⟩ : ↥K) :
          Bar2 K) = uc22pwIndHom K T₀ hT₀K ⟨h, hh⟩ (QuotientGroup.mk x) *
            (QuotientGroup.mk x)⁻¹ := by
        rw [uc22pwIndHom_apply, uc22p20uInd_mk]
        congr 1
      rw [he]
      exact hcomm ⟨h, hh⟩
    have hwT : (h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹ ∈ T₀ := (hU _).mp hwU
    have heq : (x : G) * (h : G) * (x : G)⁻¹ =
        ((h : G) * (x : G) * (h : G)⁻¹ * (x : G)⁻¹)⁻¹ * (h : G) := by group
    rw [heq]
    exact T₀.mul_mem (T₀.inv_mem hwT) hh
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    exact key t ht
  · exact le_of_eq (Subgroup.card_map_of_injective (K := T₀)
      (f := (MulAut.conj (x : G)).toMonoidHom) (MulAut.conj (x : G)).injective).symm

theorem exists_orderOf_mem_normalizer_of_isSz {K T₀ : Subgroup G} (hBor : KSzBorel)
    (hAut : KSzTwoAut) {a r : ℕ}
    (hSz : IsSz (Bar2 K) a) (hT₀ : IsPGroup 2 T₀)
    (hT₀K : T₀ ≤ Subgroup.normalizer (K : Set G))
    (hS : IsSylowOf 2 (T₀ ⊓ K) K) (hr : r.Prime) (hrdvd : r ∣ 2 ^ a - 1) :
    ∃ x ∈ K, orderOf x = r ∧ x ∈ Subgroup.normalizer (T₀ : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨U, hU⟩ := exists_sylowBar2_with_mem (K := K) (T₀ := T₀) hS
  obtain ⟨D, hDcard, hDN⟩ := hBor (Bar2 K) a hSz U
  obtain ⟨xd, hxd⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) r (by rw [hDcard]; exact hrdvd)
  have hxbo : orderOf (xd : Bar2 K) = r := by rw [Subgroup.orderOf_coe xd]; exact hxd
  have hxbarN : (xd : Bar2 K) ∈ Subgroup.normalizer ((U : Subgroup (Bar2 K)) : Set (Bar2 K)) :=
    hDN xd.2
  obtain ⟨x, c, hxbar, hxo⟩ := exists_lift_pow_orderOf_eq hSz hr hrdvd hxbo
  have hxN : (QuotientGroup.mk x : Bar2 K) ∈
      Subgroup.normalizer ((U : Subgroup (Bar2 K)) : Set (Bar2 K)) := by
    rw [hxbar]
    exact Subgroup.pow_mem _ hxbarN _
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hxo,
    mem_normalizer_of_commutator_sylowBar2 hT₀K U hU
      (commutator_mem_sylowBar2 hT₀K U (exists_conj_uc22pwIndHom hAut hSz hT₀ hT₀K U hU) hxN)⟩

private theorem inducedQuotInfAut_mem_sylowImage {D : Data G} {K : Subgroup G} {h : G}
    (hhT : h ∈ Subgroup.normalizer (D.T : Set G))
    (hhK : h ∈ Subgroup.normalizer (K : Set G)) {z : xbar K}
    (hz : z ∈ sylowImage D K) :
    inducedQuotInfAut K h hhK z ∈ sylowImage D K := by
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hz
  rw [inducedQuotInfAut_piBarInf]
  have hmemK : h * (l : G) * h⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hhK l).mp l.2
  have hmemT : h * (l : G) * h⁻¹ ∈ D.T :=
    (Subgroup.mem_normalizer_iff.mp hhT l).mp hl.1
  refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ?_)
  exact Subgroup.mem_inf.mpr ⟨hmemT, hmemK⟩

private theorem commutator_mem_solvableRadical_of_mem_calC {D : Data G} {K K' : Subgroup G}
    (hK : K ∈ calC D.M) (hK' : K' ∈ calC D.M) (hne : K ≠ K') {x l : G}
    (hx : x ∈ K') (hl : l ∈ K) (hxN : x ∈ Subgroup.normalizer (K : Set G)) :
    ⁅x, l⁆ ∈ (CFSG.solvableRadical ↥K).map K.subtype := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxM : x ∈ D.M := hK'.1.le hx
  have hlM : l ∈ D.M := hK.1.le hl
  have hconjK : x * l * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxN l).mp hl
  have hcommK : ⁅x, l⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem hconjK (K.inv_mem hl)
  have hcommP : ⁅x, l⁆ ∈ pCoreOf 2 D.M := by
    have hgl : uc22p21cPi D.M ⟨l, hlM⟩ * uc22p21cPi D.M ⟨x, hxM⟩ =
        uc22p21cPi D.M ⟨x, hxM⟩ * uc22p21cPi D.M ⟨l, hlM⟩ :=
      uc22p22l_barImage_commute hK hK' hne _
        (uc22p21c_mem_barImage.2 ⟨⟨l, hlM⟩, hl, rfl⟩) _
        (uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hx, rfl⟩)
    have h1 := uc22p22u_commutator_mem_pCoreOf hlM hxM hgl
    rw [← commutatorElement_inv x l] at h1
    simpa using (pCoreOf 2 D.M).inv_mem h1
  have hP2 : IsPGroup 2 ↥(K ⊓ pCoreOf 2 D.M) :=
    (uc22p21c_isPGroup_pCoreOf D.M).to_le
      (inf_le_right : K ⊓ pCoreOf 2 D.M ≤ pCoreOf 2 D.M)
  have hPnorm : ∀ k ∈ K, ∀ z ∈ K ⊓ pCoreOf 2 D.M,
      k * z * k⁻¹ ∈ K ⊓ pCoreOf 2 D.M := by
    intro k hk z hz
    exact ⟨K.mul_mem (K.mul_mem hk hz.1) (K.inv_mem hk),
      uc22p21c_conj_mem_pCoreOf_self (K := D.M) (hK.1.le hk) hz.2⟩
  exact (Subgroup.map_mono (CFSG.pCore_le_solvableRadical 2 ↥K))
    (uc22p21c_le_pCoreOf inf_le_left hP2 hPnorm ⟨hcommK, hcommP⟩)

private theorem inducedQuotInfAut_eq_one_of_mem_calC {D : Data G} {K K' : Subgroup G}
    (hK : K ∈ calC D.M) (hK' : K' ∈ calC D.M) (hne : K ≠ K') {x : G} (hx : x ∈ K')
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) :
    inducedQuotInfAut K x hxN = 1 := by
  classical
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  ext y
  obtain ⟨l, rfl⟩ := piBarInf_surjective K y
  rw [inducedQuotInfAut_piBarInf, MulAut.one_apply]
  have hconjK : x * (l : G) * x⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hxN l).mp l.2
  have hcommK : ⁅x, (l : G)⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem hconjK (K.inv_mem l.2)
  have hcommSol : ⁅x, (l : G)⁆ ∈ (CFSG.solvableRadical ↥K).map K.subtype :=
    commutator_mem_solvableRadical_of_mem_calC hK hK' hne hx l.2 hxN
  have hmem : (⟨x * (l : G) * x⁻¹, hconjK⟩ : ↥K) * l⁻¹ ∈ (piBarInf K).ker := by
    rw [piBarInf_ker hq]
    have hprod : (⟨x * (l : G) * x⁻¹, hconjK⟩ : ↥K) * l⁻¹ =
        ⟨⁅x, (l : G)⁆, hcommK⟩ := by
      ext
      simp [commutatorElement_def]
    rw [hprod]
    obtain ⟨z, hz, hzval⟩ := hcommSol
    rw [show (⟨⁅x, (l : G)⁆, hcommK⟩ : ↥K) = z from Subtype.ext hzval.symm]
    exact hz
  rw [MonoidHom.mem_ker, map_mul, map_inv] at hmem
  exact mul_inv_eq_one.mp hmem

private theorem inducedQuotInfAut_eq_conj_piBarInf {K : Subgroup G} {t : G}
    (htK : t ∈ K) (htN : t ∈ Subgroup.normalizer (K : Set G)) :
    inducedQuotInfAut K t htN = MulAut.conj (piBarInf K ⟨t, htK⟩) := by
  ext y
  obtain ⟨l, rfl⟩ := piBarInf_surjective K y
  rw [inducedQuotInfAut_piBarInf, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 2

private theorem exists_sylowImage_normalizer_of_conj {D : Data G} {K : Subgroup G} {h : G}
    (hK : K ∈ calC D.M) (hhT : h ∈ Subgroup.normalizer (D.T : Set G))
    (hhK : h ∈ Subgroup.normalizer (K : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hord : orderOf h = r)
    (hconj_inj : Function.Injective (MulAut.conj : xbar K →* MulAut (xbar K)))
    {d : xbar K} (hdne : d ≠ 1)
    (hθ : inducedQuotInfAut K h hhK = MulAut.conj d) :
    d ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))) ∧ d ∉ sylowImage D K := by
  have hθr : (inducedQuotInfAut K h hhK) ^ r = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact (orderOf_inducedQuotInfAut_dvd K hhK).trans (by rw [hord])
  have hdr : (MulAut.conj d) ^ r = 1 := by rw [← hθ]; exact hθr
  have hdvdord : orderOf d ∣ r := by
    apply orderOf_dvd_of_pow_eq_one
    apply hconj_inj
    rw [map_pow, hdr, map_one]
  have hdord : orderOf d = r := by
    rcases (Nat.dvd_prime hr).mp hdvdord with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hdne
    · exact h1
  refine ⟨?_, ?_⟩
  · refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨z, hz, rfl⟩
      rw [← hθ]
      exact inducedQuotInfAut_mem_sylowImage hhT hhK hz
    · exact le_of_eq (Subgroup.card_map_of_injective (K := sylowImage D K)
        (f := (MulAut.conj d).toMonoidHom) (MulAut.conj d).injective).symm
  · intro hdS
    have hS2 : IsPGroup 2 (sylowImage D K) :=
      (isSylowOf_map_piBarInf (D := D) (K := K) hK).isPGroup
    obtain ⟨c, hc⟩ := hS2 ⟨d, hdS⟩
    have hdvd : r ∣ 2 ^ c := by
      have h := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hc)
      simpa [Subgroup.orderOf_coe, hdord] using h
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))

private theorem pCoreOf_conj_mem {M : Subgroup G} {n g : G} (hg : g ∈ M)
    (hn : n ∈ pCoreOf 2 M) : g * n * g⁻¹ ∈ pCoreOf 2 M := by
  obtain ⟨m, hm, rfl⟩ := hn
  refine ⟨(⟨g, hg⟩ : ↥M) * m * (⟨g, hg⟩ : ↥M)⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥M)).conj_mem m hm _, ?_⟩
  simp

private theorem exists_prime_dvd_two_pow_sub_one_of_isSz {K : Subgroup G} {a : ℕ}
    (hSz : IsSz (Bar2 K) a) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ a - 1 := by
  have hodd : Odd a := CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 hSz
  have ha3 : 3 ≤ a := CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 hSz
  have hne1 : 2 ^ a - 1 ≠ 1 := by
    have h8 : 8 ≤ 2 ^ a := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
    omega
  obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne1
  exact ⟨r, hr, uc22ine229_ne_two hodd hrdvd, hrdvd⟩

private theorem not_dvd_card_center_of_isSz {K : Subgroup G} {a r : ℕ}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hSz : IsSz (Bar2 K) a)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ a - 1) :
    ¬ r ∣ Nat.card (Subgroup.center (Bar2 K)) := by
  rw [center_eq_bot_of_isSz hq hSz, Subgroup.card_bot]
  exact hr.not_dvd_one

private theorem conj_injective_of_isSz {K : Subgroup G} {a : ℕ}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hSz : IsSz (Bar2 K) a) :
    Function.Injective (MulAut.conj : xbar K →* MulAut (xbar K)) := by
  have hZbar : Subgroup.center (xbar K) = ⊥ := by
    obtain ⟨e⟩ := uc22p21k_quotCenter_equiv (center_barInf_eq_bot hq)
    exact CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e (center_barInf_eq_bot hq)
  exact P22y.conj_injective_of_center_eq_bot hZbar

private theorem exists_mem_conjClosure_normalizer_of_isSz {D : Data G}
    (hBor : KSzBorel) (hAut : KSzTwoAut) {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ}
    (hSz : IsSz (Bar2 K) a) (hc2 : (conjSetOf D.M K).ncard = 2) :
    ∃ (r : ℕ) (h : G), r.Prime ∧ r ∣ 2 ^ a - 1 ∧ r ≠ 2 ∧ h ∈ conjClosure D.M K ∧
      h ∈ Subgroup.normalizer (D.T : Set G) ∧ orderOf h = r := by
  obtain ⟨r, hr, hr2, hrdvd⟩ := exists_prime_dvd_two_pow_sub_one_of_isSz hSz
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hZ := not_dvd_card_center_of_isSz hq hSz hr hrdvd
  have hone : ∀ T₀ : Subgroup G, IsPGroup 2 T₀ →
      T₀ ≤ Subgroup.normalizer (K : Set G) → IsSylowOf 2 (T₀ ⊓ K) K →
      ∃ x ∈ K, orderOf x = r ∧ x ∈ Subgroup.normalizer (T₀ : Set G) :=
    fun T₀ hT₀ hT₀K hS =>
      exists_orderOf_mem_normalizer_of_isSz hBor hAut hSz hT₀ hT₀K hS hr hrdvd
  obtain ⟨h, hhR, hhord, hhT⟩ :=
    uc22ine229_exists_mem_conjClosure_normalizer D.sylowM hK (by rw [hc2]) hr hr2 hZ hone
  exact ⟨r, h, hr, hrdvd, hr2, hhR, hhT, hhord⟩

private theorem conjSet_data_of_ncard_eq_two {D : Data G} {K K' : Subgroup G} {t : G}
    (hK : K ∈ calC D.M) (htM : t ∈ D.M)
    (htK : K.map (MulAut.conj t).toMonoidHom ≠ K)
    (hc2 : (conjSetOf D.M K).ncard = 2)
    (hK'eq : K' = K.map (MulAut.conj t).toMonoidHom) :
    K' ∈ calC D.M ∧ conjSetOf D.M K = {K, K'} ∧ conjClosure D.M K = K ⊔ K' ∧
      K' ≤ Subgroup.normalizer (K : Set G) ∧
      K ≤ Subgroup.normalizer (K' : Set G) ∧
      K'.map (MulAut.conj t).toMonoidHom = K := by
  classical
  subst K'
  have hK'calC : K.map (MulAut.conj t).toMonoidHom ∈ calC D.M := by
    have h := uc22p22u_calC_conj (X := D.M) (M := D.M) (K := K) le_normalizer hK
      (m := t⁻¹) (D.M.inv_mem htM)
    simpa only [uniqueFourConj, inv_inv] using h
  have hset : conjSetOf D.M K = {K, K.map (MulAut.conj t).toMonoidHom} :=
    uc22p22d_conjSet_pair htM htK hc2
  have hclosure : conjClosure D.M K = K ⊔ K.map (MulAut.conj t).toMonoidHom :=
    uc22p22d_conjClosure_pair htM htK hc2
  have hne : K ≠ K.map (MulAut.conj t).toMonoidHom := fun h => htK h.symm
  have hK'norm : K.map (MulAut.conj t).toMonoidHom ≤
      Subgroup.normalizer (K : Set G) := uc22p22u_calC_normalizes hK hK'calC hne
  have hKnK' : K ≤ Subgroup.normalizer
      (K.map (MulAut.conj t).toMonoidHom : Set G) :=
    uc22p22u_calC_normalizes hK'calC hK (Ne.symm hne)
  refine ⟨hK'calC, hset, hclosure, hK'norm, hKnK', ?_⟩
  have hK''mem : (K.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj t).toMonoidHom ∈ conjSetOf D.M K := by
    refine ⟨t * t, D.M.mul_mem htM htM, ?_⟩
    change (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      K.map (MulAut.conj (t * t)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  rw [hset] at hK''mem
  rcases hK''mem with h | h
  · exact h
  · exact absurd (Subgroup.map_injective (MulAut.conj t).injective h) (Ne.symm hne)

private theorem exists_mem_sup_decomp_of_mem_conjClosure {D : Data G} {K K' : Subgroup G}
    {h : G} (hK : K ∈ calC D.M) (hK' : K' ∈ calC D.M) (hne : K ≠ K')
    (hK'norm : K' ≤ Subgroup.normalizer (K : Set G))
    (hKnK' : K ≤ Subgroup.normalizer (K' : Set G)) (hh : h ∈ K ⊔ K') :
    ∃ (k : ↥K) (k' : ↥K'), h = (k : G) * (k' : G) ∧
      h ∈ Subgroup.normalizer (K : Set G) ∧
      ∀ hhN : h ∈ Subgroup.normalizer (K : Set G),
        inducedQuotInfAut K h hhN = MulAut.conj (piBarInf K k) := by
  have hprod : h ∈ ((K : Set G) * (K' : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K K' hKnK']
    exact hh
  obtain ⟨k, hk, k', hk', hk_eq⟩ := hprod
  have hk_eq' : k * k' = h := hk_eq
  have hhN : h ∈ Subgroup.normalizer (K : Set G) := by
    rw [← hk_eq']
    exact (Subgroup.normalizer (K : Set G)).mul_mem (Subgroup.le_normalizer hk) (hK'norm hk')
  refine ⟨⟨k, hk⟩, ⟨k', hk'⟩, hk_eq'.symm, hhN, ?_⟩
  intro hhN'
  have hhNprod : k * k' ∈ Subgroup.normalizer (K : Set G) := by
    rw [hk_eq']
    exact hhN'
  have hθk' : inducedQuotInfAut K k' (hK'norm hk') = 1 :=
    inducedQuotInfAut_eq_one_of_mem_calC hK hK' hne hk' (hK'norm hk')
  have hθprod : inducedQuotInfAut K (k * k') hhNprod =
      MulAut.conj (piBarInf K ⟨k, hk⟩) := by
    rw [inducedQuotInfAut_mul K (Subgroup.le_normalizer hk) (hK'norm hk') hhNprod,
      inducedQuotInfAut_eq_conj_piBarInf hk (Subgroup.le_normalizer hk), hθk', mul_one]
  change inducedQuotInfAutHom K ⟨h, hhN'⟩ =
    MulAut.conj (piBarInf K ⟨k, hk⟩)
  rw [show (⟨h, hhN'⟩ : Subgroup.normalizer (K : Set G)) =
    ⟨k * k', hhNprod⟩ from Subtype.ext hk_eq'.symm]
  exact hθprod

private theorem exists_diagonal_torus_elem_of_theta {D : Data G} {K : Subgroup G} {a r : ℕ}
    {h : G} (hK : K ∈ calC D.M) (hSz : IsSz (Bar2 K) a)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ a - 1) (hr2 : r ≠ 2) (hhR : h ∈ conjClosure D.M K)
    (hhT : h ∈ Subgroup.normalizer (D.T : Set G))
    (hhK : h ∈ Subgroup.normalizer (K : Set G)) (hord : orderOf h = r)
    {d : xbar K} (hdne : d ≠ 1)
    (hθ : ∀ hh : h ∈ Subgroup.normalizer (K : Set G),
      inducedQuotInfAut K h hh = MulAut.conj d) :
    ∃ (r : ℕ) (h : G) (d : xbar K), r.Prime ∧ r ∣ 2 ^ a - 1 ∧ r ≠ 2 ∧
      h ∈ conjClosure D.M K ∧
      h ∈ Subgroup.normalizer (D.T : Set G) ∧
      h ∈ Subgroup.normalizer (K : Set G) ∧ orderOf h = r ∧
      d ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))) ∧
      d ∉ sylowImage D K ∧
      ∀ hh : h ∈ Subgroup.normalizer (K : Set G),
        inducedQuotInfAut K h hh = MulAut.conj d := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  have hconj_inj : Function.Injective (MulAut.conj : xbar K →* MulAut (xbar K)) :=
    conj_injective_of_isSz hq hSz
  obtain ⟨hdN, hdS⟩ := exists_sylowImage_normalizer_of_conj hK hhT hhK hr hr2 hord
    hconj_inj hdne (hθ hhK)
  exact ⟨r, h, d, hr, hrdvd, hr2, hhR, hhT, hhK, hord, hdN, hdS, hθ⟩

private theorem piBarInf_conj_ne_one_of_eq_one {D : Data G} {K K' : Subgroup G} {t h : G}
    {a r : ℕ} {k : ↥K} {k' : ↥K'} (hK : K ∈ calC D.M)
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (hSz : IsSz (Bar2 K) a)
    (hr : r.Prime) (hr2 : r ≠ 2) (hord : orderOf h = r) (hhM : h ∈ D.M)
    (htM : t ∈ D.M) (hk₂ : t * (k' : G) * t⁻¹ ∈ K)
    (hdecomp : h = (k : G) * (k' : G)) (hd0 : piBarInf K k = 1) :
    piBarInf K ⟨t * (k' : G) * t⁻¹, hk₂⟩ ≠ 1 := by
  intro hd
  have hcbar : Subgroup.center (Bar2 K) = ⊥ := center_eq_bot_of_isSz hq hSz
  have hkO : (k : G) ∈ pCoreOf 2 K := by
    have hker : (k : ↥K) ∈ (piBarInf K).ker := by
      rw [MonoidHom.mem_ker]
      exact hd0
    rw [piBarInf_ker hq, solvableRadical_eq_pCore_of_center_bar2_eq_bot hq hcbar] at hker
    exact ⟨k, hker, rfl⟩
  have hk₂O : t * (k' : G) * t⁻¹ ∈ pCoreOf 2 K := by
    have hker : (⟨t * (k' : G) * t⁻¹, hk₂⟩ : ↥K) ∈ (piBarInf K).ker := by
      rw [MonoidHom.mem_ker]
      exact hd
    rw [piBarInf_ker hq, solvableRadical_eq_pCore_of_center_bar2_eq_bot hq hcbar] at hker
    exact ⟨_, hker, rfl⟩
  have hkM : (k : G) ∈ pCoreOf 2 D.M := (uc22p21c_pCoreOf_le_of_subnormal hK.1) hkO
  have hk₂M : t * (k' : G) * t⁻¹ ∈ pCoreOf 2 D.M :=
    (uc22p21c_pCoreOf_le_of_subnormal hK.1) hk₂O
  have hk'M : (k' : G) ∈ pCoreOf 2 D.M := by
    have hconj := pCoreOf_conj_mem (M := D.M) (n := t * (k' : G) * t⁻¹) (g := t⁻¹)
      (D.M.inv_mem htM) hk₂M
    simp only [inv_inv] at hconj
    rwa [show t⁻¹ * (t * (k' : G) * t⁻¹) * t = (k' : G) by group] at hconj
  have hhP : h ∈ pCoreOf 2 D.M := by
    rw [hdecomp]
    exact (pCoreOf 2 D.M).mul_mem hkM hk'M
  exact not_mem_pCoreOf_of_prime_order hr hr2 hhM hord hhP

private theorem exists_conj_mem_normalizer_of_mem_sup {D : Data G} {K K' : Subgroup G}
    {t h : G} {r : ℕ} {k : ↥K} {k' : ↥K'}
    (hK : K ∈ calC D.M) (hK' : K' ∈ calC D.M) (hne : K ≠ K')
    (hK'eq : K' = K.map (MulAut.conj t).toMonoidHom)
    (htT : t ∈ D.T) (hK'norm : K' ≤ Subgroup.normalizer (K : Set G))
    (hclosure : conjClosure D.M K = K ⊔ K')
    (hhT : h ∈ Subgroup.normalizer (D.T : Set G)) (hord : orderOf h = r)
    (hdecomp : h = (k : G) * (k' : G)) (hk₂ : t * (k' : G) * t⁻¹ ∈ K) :
    ∃ h' : G, h' ∈ conjClosure D.M K ∧
      h' ∈ Subgroup.normalizer (D.T : Set G) ∧
      h' ∈ Subgroup.normalizer (K : Set G) ∧ orderOf h' = r ∧
      ∀ hh : h' ∈ Subgroup.normalizer (K : Set G),
        inducedQuotInfAut K h' hh =
          MulAut.conj (piBarInf K ⟨t * (k' : G) * t⁻¹, hk₂⟩) := by
  let h' : G := t * h * t⁻¹
  have h'eq : h' = (t * (k : G) * t⁻¹) * (t * (k' : G) * t⁻¹) := by
    simp only [h', hdecomp]
    group
  have hk₁ : t * (k : G) * t⁻¹ ∈ K' := by
    rw [hK'eq]
    exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom k.2
  have h'N : h' ∈ Subgroup.normalizer (K : Set G) := by
    rw [h'eq]
    exact (Subgroup.normalizer (K : Set G)).mul_mem (hK'norm hk₁)
      (Subgroup.le_normalizer hk₂)
  have h'T : h' ∈ Subgroup.normalizer (D.T : Set G) := by
    change t * h * t⁻¹ ∈ Subgroup.normalizer (D.T : Set G)
    exact (Subgroup.normalizer (D.T : Set G)).mul_mem
      ((Subgroup.normalizer (D.T : Set G)).mul_mem
        (Subgroup.le_normalizer htT) hhT)
      (Subgroup.le_normalizer (D.T.inv_mem htT))
  have h'ord : orderOf h' = r := by
    rw [show h' = MulAut.conj t h by simp only [h', MulAut.conj_apply],
      MulEquiv.orderOf_eq, hord]
  have h'R : h' ∈ conjClosure D.M K := by
    rw [hclosure, h'eq]
    exact (K ⊔ K').mul_mem (Subgroup.mem_sup_right hk₁) (Subgroup.mem_sup_left hk₂)
  have hxy : (t * (k : G) * t⁻¹) * (t * (k' : G) * t⁻¹) ∈
      Subgroup.normalizer (K : Set G) := h'eq ▸ h'N
  have hθprod : inducedQuotInfAut K
      ((t * (k : G) * t⁻¹) * (t * (k' : G) * t⁻¹)) hxy =
      MulAut.conj (piBarInf K ⟨t * (k' : G) * t⁻¹, hk₂⟩) := by
    rw [inducedQuotInfAut_mul K (hK'norm hk₁) (Subgroup.le_normalizer hk₂) hxy,
      inducedQuotInfAut_eq_one_of_mem_calC hK hK' hne hk₁ (hK'norm hk₁),
      inducedQuotInfAut_eq_conj_piBarInf hk₂ (Subgroup.le_normalizer hk₂), one_mul]
  refine ⟨h', h'R, h'T, h'N, h'ord, ?_⟩
  intro hh
  change inducedQuotInfAutHom K ⟨h', hh⟩ =
    MulAut.conj (piBarInf K ⟨t * (k' : G) * t⁻¹, hk₂⟩)
  rw [show (⟨h', hh⟩ : Subgroup.normalizer (K : Set G)) =
    ⟨(t * (k : G) * t⁻¹) * (t * (k' : G) * t⁻¹), hxy⟩ from Subtype.ext h'eq]
  exact hθprod

theorem Ctx23L.exists_diagonal_torus_elem {D : Data G}
    (hBor : KSzBorel) (hAut : KSzTwoAut) {K : Subgroup G} (hK : K ∈ calC D.M) {a : ℕ}
    (hSz : IsSz (Bar2 K) a) (hc2 : (conjSetOf D.M K).ncard = 2) {t : G} (htT : t ∈ D.T)
    (htK : K.map (MulAut.conj t).toMonoidHom ≠ K) :
    ∃ (r : ℕ) (h : G) (d : xbar K), r.Prime ∧ r ∣ 2 ^ a - 1 ∧ r ≠ 2 ∧
      h ∈ conjClosure D.M K ∧
      h ∈ Subgroup.normalizer (D.T : Set G) ∧
      h ∈ Subgroup.normalizer (K : Set G) ∧ orderOf h = r ∧
      d ∈ Subgroup.normalizer ((sylowImage D K : Set (xbar K))) ∧
      d ∉ sylowImage D K ∧
      ∀ hh : h ∈ Subgroup.normalizer (K : Set G),
        inducedQuotInfAut K h hh = MulAut.conj d := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htM : t ∈ D.M := D.sylowM.le htT
  have hq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  obtain ⟨r, h₀, hr, hrdvd, hr2, hh₀R, hh₀T, hh₀ord⟩ :=
    exists_mem_conjClosure_normalizer_of_isSz hBor hAut hK hSz hc2
  let K' : Subgroup G := K.map (MulAut.conj t).toMonoidHom
  obtain ⟨hK'calC, _, hclosure, hK'norm, hKnK', hK''eq⟩ :=
    conjSet_data_of_ncard_eq_two hK htM htK hc2 rfl
  have hne : K ≠ K' := fun h => htK h.symm
  obtain ⟨k₀, k₀', hdecomp, hxy, hθ⟩ :=
    exists_mem_sup_decomp_of_mem_conjClosure hK hK'calC hne hK'norm hKnK'
      (by rw [← hclosure]; exact hh₀R)
  by_cases hd0 : piBarInf K k₀ = 1
  · have hk₂ : t * (k₀' : G) * t⁻¹ ∈ K := by
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom (k₀' : ↥K').2
      rwa [hK''eq] at hmem
    obtain ⟨h', h'R, h'T, h'N, h'ord, h'θ⟩ :=
      exists_conj_mem_normalizer_of_mem_sup hK hK'calC hne rfl htT hK'norm hclosure
        hh₀T hh₀ord hdecomp hk₂
    have hhM : h₀ ∈ D.M := by
      rw [hdecomp]
      exact D.M.mul_mem (hK.1.le k₀.2) (hK'calC.1.le k₀'.2)
    have hdne : piBarInf K ⟨t * (k₀' : G) * t⁻¹, hk₂⟩ ≠ 1 :=
      piBarInf_conj_ne_one_of_eq_one hK hq hSz hr hr2 hh₀ord hhM htM hk₂ hdecomp hd0
    exact exists_diagonal_torus_elem_of_theta hK hSz hr hrdvd hr2 h'R h'T h'N h'ord hdne h'θ
  · exact exists_diagonal_torus_elem_of_theta hK hSz hr hrdvd hr2 hh₀R hh₀T hxy hh₀ord hd0 hθ

end CFSG.LocalAnalysis.UniquenessCase.UC22
