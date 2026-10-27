module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyTwoFit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SemiregularInverted

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_map_conj {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) (g : G) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map (MulAut.conj g).toMonoidHom)
      (K.map (MulAut.conj g).toMonoidHom) := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact h.2.2

theorem map_conj_map_conj_inv (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [Subgroup.map_conj_map_conj, inv_mul_cancel]
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
  rw [h, Subgroup.map_id]

theorem map_conj_normalizer (H : Subgroup G) (g : G) :
    (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
  Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)

private theorem pCoreOf_le_centralizer_Z (D : Data G) :
    CFSG.Open.pCoreOf 2 D.M ≤ Subgroup.centralizer (D.Z : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZT : D.Z ≤ Subgroup.centralizer (D.T : Set G) := fun z hz =>
    (CFSG.LocalAnalysis.RankThreeUC.omegaOneCenterIn_le_inf_centralizer D.T hz).2
  have hO2T : CFSG.Open.pCoreOf 2 D.M ≤ D.T := by
    obtain ⟨Q, hQ⟩ := D.sylowM.exists_sylow_eq_subgroupOf
    haveI : (CFSG.pCore 2 ↥D.M).Normal := CFSG.pCore_normal
    have h1 : CFSG.pCore 2 ↥D.M ≤ (Q : Subgroup ↥D.M) :=
      IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)) Q
    have h2 := Subgroup.map_mono (f := D.M.subtype) h1
    rwa [hQ, Subgroup.map_subgroupOf_eq_of_le D.sylowM.le] at h2
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact ((Subgroup.mem_centralizer_iff.mp (hZT hz)) x (hO2T hx)).symm

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem orderOf_mk_eq_of_torus (c : Ctx23L D Ch) {r : ℕ} {a b t u : G}
    (hT : OmegaPlusTorus c r a b t) (huM : u ∈ D.M) (hur : orderOf u = r) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨u, huM⟩ : ↥D.M)) = r := by
  haveI : Fact r.Prime := ⟨hT.r_prime⟩
  have hdiv : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨u, huM⟩ : ↥D.M)) ∣ r := by
    have h := orderOf_map_dvd (uc22p21cPi D.M) (⟨u, huM⟩ : ↥D.M)
    rwa [Subgroup.orderOf_mk, hur] at h
  have hne : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨u, huM⟩ : ↥D.M) ≠ 1 := by
    intro h1
    have hmem : (⟨u, huM⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).exists_card_eq
    have hdvd : r ∣ 2 ^ k := by
      have h2 : orderOf (⟨u, huM⟩ : ↥D.M) ∣ Nat.card ↥(CFSG.pCore 2 ↥D.M) :=
        Subgroup.orderOf_dvd_natCard _ hmem
      rwa [Subgroup.orderOf_mk, hur, hk] at h2
    exact hT.r_ne_two ((Nat.prime_dvd_prime_iff_eq hT.r_prime Nat.prime_two).mp
      (hT.r_prime.dvd_of_dvd_pow hdvd))
  rcases (Nat.dvd_prime hT.r_prime).mp hdiv with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h1

private theorem odd_orderOf_zpow_mul_of_torus (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : OmegaPlusTorus c r a b t) (i j : ℤ) : Odd (orderOf (a ^ i * b ^ j)) := by
  have haz : a ^ (r : ℤ) = 1 := by
    rw [zpow_natCast, ← hT.a_order]
    exact pow_orderOf_eq_one a
  have hbz : b ^ (r : ℤ) = 1 := by
    rw [zpow_natCast, ← hT.b_order]
    exact pow_orderOf_eq_one b
  have har : (a ^ i) ^ r = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm i (r : ℤ), zpow_mul, haz, one_zpow]
  have hbr : (b ^ j) ^ r = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm j (r : ℤ), zpow_mul, hbz, one_zpow]
  refine Odd.of_dvd_nat (hT.r_prime.odd_of_ne_two hT.r_ne_two) ?_
  rw [orderOf_dvd_iff_pow_eq_one]
  calc (a ^ i * b ^ j) ^ r = (a ^ i) ^ r * (b ^ j) ^ r :=
        ((show Commute a b from hT.commute).zpow_left i |>.zpow_right j).mul_pow r
    _ = 1 := by rw [har, hbr, mul_one]

private theorem not_mem_centralizer_zpow_mul_of_torus (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : OmegaPlusTorus c r a b t) (i j : ℤ) (hj : ¬ (r : ℤ) ∣ j) :
    a ^ i * b ^ j ∉ Subgroup.centralizer (D.Z : Set G) := by
  intro hdC
  have hbjC : b ^ j ∈ Subgroup.centralizer (D.Z : Set G) := by
    have h1 : b ^ j = (a ^ i)⁻¹ * (a ^ i * b ^ j) := by group
    rw [h1]
    exact (Subgroup.centralizer (D.Z : Set G)).mul_mem
      (inv_mem ((Subgroup.centralizer (D.Z : Set G)).zpow_mem hT.a_centralizes i)) hdC
  have hbj_ne : b ^ j ≠ 1 := by
    intro h1
    refine hj ?_
    rw [← hT.b_order]
    exact (orderOf_dvd_iff_zpow_eq_one (x := b) (i := j)).mpr h1
  have hzp : Subgroup.zpowers (b ^ j) = Subgroup.zpowers b :=
    TauCeti.zpowers_eq_zpowers_of_mem_zpowers hT.r_prime
      (by rw [← hT.b_order]; exact pow_orderOf_eq_one b) hbj_ne
      (Subgroup.zpow_mem_zpowers b j)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hzp.symm ▸ Subgroup.mem_zpowers b)
  refine hT.b_not_centralizes ?_
  rw [Subgroup.mem_centralizer_iff] at hbjC ⊢
  intro z hz
  calc z * b = z * (b ^ j) ^ m := by rw [hm]
    _ = (b ^ j) ^ m * z := ((show Commute z (b ^ j) from hbjC z hz).zpow_right m).eq
    _ = b * z := by rw [hm]

private theorem conj_zpow_mul_eq_inv_of_torus (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : OmegaPlusTorus c r a b t) (i j : ℤ) :
    t * (a ^ i * b ^ j) * t⁻¹ = (a ^ i * b ^ j)⁻¹ := by
  have hconj : ∀ n : ℤ, t * a ^ n * t⁻¹ = (a ^ n)⁻¹ := by
    intro n
    rw [show t * a ^ n * t⁻¹ = MulAut.conj t (a ^ n) from (MulAut.conj_apply t (a ^ n)).symm,
      map_zpow, show MulAut.conj t a = a⁻¹ from by rw [MulAut.conj_apply]; exact hT.t_inv_a,
      inv_zpow]
  have hconjb : ∀ n : ℤ, t * b ^ n * t⁻¹ = (b ^ n)⁻¹ := by
    intro n
    rw [show t * b ^ n * t⁻¹ = MulAut.conj t (b ^ n) from (MulAut.conj_apply t (b ^ n)).symm,
      map_zpow, show MulAut.conj t b = b⁻¹ from by rw [MulAut.conj_apply]; exact hT.t_inv_b,
      inv_zpow]
  rw [show t * (a ^ i * b ^ j) * t⁻¹ = (t * a ^ i * t⁻¹) * (t * b ^ j * t⁻¹) from by group,
    hconj i, hconjb j, mul_inv_rev]
  exact ((show Commute a b from hT.commute).zpow_left i |>.zpow_right j).inv_inv.eq

private theorem pCore_inf_centralizer_zpow_mul_eq_bot (c : Ctx23L D Ch) (h1930 : H1930 D)
    (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {r : ℕ} {a b t : G} (hT : OmegaPlusTorus c r a b t) (haM : a ∈ D.M)
    {p : ℕ} (hp : p ∈ D.sig) (i j : ℤ) (hj : ¬ (r : ℤ) ∣ j) :
    CFSG.pCore p (Bar2 D.M) ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M) ^ i *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hT.b_mem_M⟩ : ↥D.M) ^ j} :
        Set (Bar2 D.M)) = ⊥ := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hZM : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    have h := (h4 h1930 c).2.2
    rwa [(h4 h1930 c).1] at h
  have hdM : a ^ i * b ^ j ∈ D.M :=
    D.M.mul_mem (D.M.zpow_mem haM i) (D.M.zpow_mem hT.b_mem_M j)
  have hmain := pCore_inf_centralizer_bar_eq_bot_of_inverted (c := c) (hZM := hZM)
    (h1930 := h1930) (h6 := h6) (hsp := hsp) (d := a ^ i * b ^ j) (t := t)
    (hdM := hdM) (hd := odd_orderOf_zpow_mul_of_torus c hT i j)
    (hdZ := not_mem_centralizer_zpow_mul_of_torus c hT i j hj)
    (ht := conj_zpow_mul_eq_inv_of_torus c hT i j) (p := p) (hp := (D.sig_prime p hp).1)
    (hp2 := (D.sig_prime p hp).2) (hpsig := hp)
  have hbar_eq : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a ^ i * b ^ j, hdM⟩ : ↥D.M) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M) ^ i *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hT.b_mem_M⟩ : ↥D.M) ^ j := by
    have hd_eq : (⟨a ^ i * b ^ j, hdM⟩ : ↥D.M) =
        (⟨a, haM⟩ : ↥D.M) ^ i * (⟨b, hT.b_mem_M⟩ : ↥D.M) ^ j := by
      apply Subtype.ext
      simp
    rw [hd_eq, map_mul, map_zpow, map_zpow]
  rw [hbar_eq] at hmain
  exact hmain

private theorem bar_ne_zpowers_of_torus (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : OmegaPlusTorus c r a b t) (haM : a ∈ D.M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hT.b_mem_M⟩ : ↥D.M) ∉
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)) := by
  rintro hy
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
      ((⟨b, hT.b_mem_M⟩ : ↥D.M) * ((⟨a, haM⟩ : ↥D.M) ^ i)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hi, mul_inv_cancel]
  have hmem : (⟨b, hT.b_mem_M⟩ : ↥D.M) * ((⟨a, haM⟩ : ↥D.M) ^ i)⁻¹ ∈
      CFSG.pCore 2 ↥D.M :=
    (QuotientGroup.eq_one_iff _).1 hq
  set z : G := b * (a ^ i)⁻¹ with hz
  have hzO2 : z ∈ CFSG.Open.pCoreOf 2 D.M :=
    Subgroup.mem_map.mpr ⟨_, hmem, by simp [hz]⟩
  have hzC : z ∈ Subgroup.centralizer (D.Z : Set G) := pCoreOf_le_centralizer_Z D hzO2
  have haC : a ∈ Subgroup.centralizer (D.Z : Set G) := hT.a_centralizes
  refine hT.b_not_centralizes ?_
  have hb_eq : b = z * a ^ i := by
    rw [hz]
    group
  rw [hb_eq]
  exact (Subgroup.centralizer (D.Z : Set G)).mul_mem hzC
    ((Subgroup.centralizer (D.Z : Set G)).zpow_mem haC i)

private theorem not_mem_sig_r_of_torus (c : Ctx23L D Ch) (h1930 : H1930 D) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {r : ℕ} {a b t : G} (hT : OmegaPlusTorus c r a b t) (haM : a ∈ D.M) : r ∉ D.sig := by
  refine not_mem_sig_of_normalizer_not_le D Ch h1930 c h6 hsp hT.r_prime haM hT.a_order ?_
  intro hle
  refine hT.t_not_mem_M (hle ?_)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (t * a * t⁻¹) = Subgroup.zpowers a
  rw [hT.t_inv_a, Subgroup.zpowers_inv]

private theorem pCore_le_centralizer_bar_of_torus (c : Ctx23L D Ch) (h1930 : H1930 D)
    (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {r : ℕ} {a b t : G} (hT : OmegaPlusTorus c r a b t) (haM : a ∈ D.M)
    {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.pCore p (Bar2 D.M) ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)} : Set (Bar2 D.M)) := by
  classical
  haveI : Fact r.Prime := ⟨hT.r_prime⟩
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  set x : Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M) with hx
  set y : Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨b, hT.b_mem_M⟩ : ↥D.M) with hy
  have hxord : orderOf x = r := by
    rw [hx]
    exact orderOf_mk_eq_of_torus c hT haM hT.a_order
  have hyord : orderOf y = r := by
    rw [hy]
    exact orderOf_mk_eq_of_torus c hT hT.b_mem_M hT.b_order
  have hxy : x * y = y * x := by
    rw [hx, hy, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hT.commute
  have hyx : y ∉ Subgroup.zpowers x := by
    rw [hy, hx]
    exact bar_ne_zpowers_of_torus c hT haM
  have hr_not_sig : r ∉ D.sig := not_mem_sig_r_of_torus c h1930 h6 hsp hT haM
  have hcop : Nat.Coprime r (Nat.card (CFSG.pCore p (Bar2 D.M))) := by
    refine (Nat.Prime.coprime_iff_not_dvd hT.r_prime).mpr ?_
    intro hdvd
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M)).exists_card_eq
    rw [hk] at hdvd
    have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hT.r_prime (D.sig_prime p hp).1).mp
      (hT.r_prime.dvd_of_dvd_pow hdvd)
    exact (fun hpr : p = r => hr_not_sig (hpr ▸ hp)) hrp.symm
  have hxQ : x ∈ Subgroup.normalizer (CFSG.pCore p (Bar2 D.M) : Set (Bar2 D.M)) := by
    haveI : (CFSG.pCore p (Bar2 D.M)).Normal := CFSG.pCore_normal
    exact Subgroup.le_normalizer_of_normal (K := Subgroup.zpowers x) (Subgroup.mem_zpowers x)
  have hyQ : y ∈ Subgroup.normalizer (CFSG.pCore p (Bar2 D.M) : Set (Bar2 D.M)) := by
    haveI : (CFSG.pCore p (Bar2 D.M)).Normal := CFSG.pCore_normal
    exact Subgroup.le_normalizer_of_normal (K := Subgroup.zpowers y) (Subgroup.mem_zpowers y)
  refine CFSG.GroupTheory.le_centralizer_of_rank_two hxord hyord hxy hyx hxQ hyQ hcop ?_
  intro i j hj
  exact pCore_inf_centralizer_zpow_mul_eq_bot c h1930 h4 h6 hsp hT haM hp i j hj

private theorem le_normalizer_barPreimage_zpowers {a : G} (haM : a ∈ D.M)
    {P : Subgroup G} (hPM : P ≤ D.M)
    (hPcent : barImage D.M P ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)} : Set (Bar2 D.M))) :
    P ≤ Subgroup.normalizer (barPreimage D.M
      (Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M))) :
        Set G) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcent : uc22p21cPi D.M ⟨u, hPM hu⟩ ∈ Subgroup.centralizer
      ({uc22p21cPi D.M ⟨a, haM⟩} : Set (Bar2 D.M)) :=
    hPcent (uc22p21c_mem_barImage.2 ⟨⟨u, hPM hu⟩, hu, rfl⟩)
  have hcomm : Commute (uc22p21cPi D.M ⟨u, hPM hu⟩) (uc22p21cPi D.M ⟨a, haM⟩) :=
    ((Subgroup.mem_centralizer_iff.mp hcent) _ (Set.mem_singleton _)).symm
  have hconj : ∀ w : Bar2 D.M,
      w ∈ Subgroup.zpowers (uc22p21cPi D.M ⟨a, haM⟩) →
        uc22p21cPi D.M ⟨u, hPM hu⟩ * w * (uc22p21cPi D.M ⟨u, hPM hu⟩)⁻¹ = w := by
    intro w hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hn]
    rw [(hcomm.zpow_right n).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hle : (barPreimage D.M
      (Subgroup.zpowers (uc22p21cPi D.M ⟨a, haM⟩))).map
        (MulAut.conj u).toMonoidHom ≤
      barPreimage D.M (Subgroup.zpowers (uc22p21cPi D.M ⟨a, haM⟩)) := by
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨hyM, hyD⟩ := uc22p21c_mem_barPreimage.1 hy
    have huyM : u * y * u⁻¹ ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (hPM hu) hyM) (D.M.inv_mem (hPM hu))
    change u * y * u⁻¹ ∈ barPreimage D.M
      (Subgroup.zpowers (uc22p21cPi D.M ⟨a, haM⟩))
    refine uc22p21c_mem_barPreimage.2 ⟨huyM, ?_⟩
    have e : (⟨u * y * u⁻¹, huyM⟩ : ↥D.M) =
        ⟨u, hPM hu⟩ * ⟨y, hyM⟩ * ⟨u, hPM hu⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hconj _ hyD]
    exact hyD
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj u).injective]

private abbrev barA (D : Data G) (a : G) (haM : a ∈ D.M) : Bar2 D.M :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) (⟨a, haM⟩ : ↥D.M)

private abbrev preimageZpowers (D : Data G) (a : G) (haM : a ∈ D.M) : Subgroup G :=
  barPreimage D.M (Subgroup.zpowers (barA D a haM))

private theorem barImage_sylow_le_centralizer_of_torus (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h2123 : S21_23 D Ch) (hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)))
    {r : ℕ} {a b t : G} (hT : OmegaPlusTorus c r a b t) (haM : a ∈ D.M)
    {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M))) :
    barImage D.M P ≤ Subgroup.centralizer ({barA D a haM} : Set (Bar2 D.M)) := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hPnorm : (barImage D.M P).Normal :=
    (h2123 h1930 c.toCtx21 p hp P hP
      (isCyclic_fitting_commutator_of_cyclic D hcyc)).2.2.2.1
  have hPp : IsPGroup p (barImage D.M P) := by
    rw [barImage]
    exact (hP.isPGroup.comap_subtype).map _
  have hbar_le_pCore : barImage D.M P ≤ CFSG.pCore p (Bar2 D.M) :=
    le_sSup ⟨hPnorm, hPp⟩
  exact hbar_le_pCore.trans (pCore_le_centralizer_bar_of_torus c h1930 h4 h6 hsp hT haM hp)

private theorem isSylowOf_zpowers_preimage (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : OmegaPlusTorus c r a b t) (haM : a ∈ D.M) :
    CFSG.ABGLocalTools.IsSylowOf r (Subgroup.zpowers a) (preimageZpowers D a haM) := by
  haveI : Fact r.Prime := ⟨hT.r_prime⟩
  have hzple : Subgroup.zpowers a ≤ preimageZpowers D a haM :=
    Subgroup.zpowers_le.mpr
      (uc22p21c_mem_barPreimage.2 ⟨haM, Subgroup.mem_zpowers (barA D a haM)⟩)
  have hxord : orderOf (barA D a haM) = r := orderOf_mk_eq_of_torus c hT haM hT.a_order
  have hKcard : Nat.card ↥(preimageZpowers D a haM) =
      Nat.card (CFSG.Open.pCoreOf 2 D.M) * r := by
    change Nat.card ↥(barPreimage D.M (Subgroup.zpowers (barA D a haM))) = _
    rw [uc22p22u_card_barPreimage, Nat.card_zpowers, hxord]
  have hrelIndex : (Subgroup.zpowers a).relIndex (preimageZpowers D a haM) =
      Nat.card (CFSG.Open.pCoreOf 2 D.M) := by
    have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers a) (preimageZpowers D a haM)
    rw [inf_eq_left.mpr hzple, Nat.card_zpowers, hT.a_order, hKcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hT.r_prime.pos h1
  have hdvdIndex : ¬ r ∣ (Subgroup.zpowers a).relIndex (preimageZpowers D a haM) := by
    rw [hrelIndex]
    intro hd
    obtain ⟨n, hn⟩ := (uc22p21c_isPGroup_pCoreOf D.M).exists_card_eq
    rw [hn] at hd
    exact hT.r_ne_two ((Nat.prime_dvd_prime_iff_eq hT.r_prime Nat.prime_two).mp
      (hT.r_prime.dvd_of_dvd_pow hd))
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  exact ⟨hzple,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hT.a_order, pow_one]), hdvdIndex⟩

private theorem exists_sylow_r_le_normalizer_preimage (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h2123 : S21_23 D Ch) (hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)))
    {r : ℕ} {a b t : G} (hT : OmegaPlusTorus c r a b t) (haM : a ∈ D.M)
    {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M))) :
    ∃ S : Sylow r ↥(preimageZpowers D a haM),
      P ≤ Subgroup.normalizer
        (((S : Subgroup ↥(preimageZpowers D a haM)).map
          (preimageZpowers D a haM).subtype : Subgroup G) : Set G) := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hPM : P ≤ D.M := hP.le.trans (uc22p21c_barPreimage_le D.M (centE D.M))
  have hPcent :=
    barImage_sylow_le_centralizer_of_torus c h1930 h4 h6 hsp h2123 hcyc hT haM hp hP
  have hPK : P ≤ Subgroup.normalizer (preimageZpowers D a haM : Set G) :=
    le_normalizer_barPreimage_zpowers haM hPM hPcent
  have hxord : orderOf (barA D a haM) = r := orderOf_mk_eq_of_torus c hT haM hT.a_order
  have hcopK : Nat.Coprime p (Nat.card ↥(preimageZpowers D a haM)) := by
    have hYr : IsPGroup r ↥(Subgroup.zpowers (barA D a haM)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord, pow_one])
    exact natCard_barPreimage_coprime (Y := Subgroup.zpowers (barA D a haM)) hYr
      (D.sig_prime p hp).1 hT.r_prime
      (fun h => not_mem_sig_r_of_torus c h1930 h6 hsp hT haM (h ▸ hp))
      (D.sig_prime p hp).2
  exact CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup (p := p) (q := r)
    (D.sig_prime p hp).1 hT.r_prime hP.isPGroup hPK
    (fun hd => (D.sig_prime p hp).1.ne_one (hcopK.eq_one_of_dvd hd))

private theorem exists_conj_zpowers_of_sylow (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : OmegaPlusTorus c r a b t) (haM : a ∈ D.M)
    {S : Sylow r ↥(preimageZpowers D a haM)} :
    ∃ k : ↥(preimageZpowers D a haM),
      ((S : Subgroup ↥(preimageZpowers D a haM)).map
          (preimageZpowers D a haM).subtype : Subgroup G) =
        (Subgroup.zpowers a).map (MulAut.conj (k : G)).toMonoidHom := by
  haveI : Fact r.Prime := ⟨hT.r_prime⟩
  have hZsyl := isSylowOf_zpowers_preimage c hT haM
  haveI : MulAction.IsPretransitive ↥(preimageZpowers D a haM)
      (Sylow r ↥(preimageZpowers D a haM)) := Sylow.isPretransitive_of_finite
  obtain ⟨S₀, hS₀⟩ := hZsyl.exists_sylow_eq_subgroupOf
  obtain ⟨k, hk⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := ↥(preimageZpowers D a haM)) S₀ S
  have hzple : Subgroup.zpowers a ≤ preimageZpowers D a haM :=
    Subgroup.zpowers_le.mpr
      (uc22p21c_mem_barPreimage.2 ⟨haM, Subgroup.mem_zpowers (barA D a haM)⟩)
  have hS₀map : ((S₀ : Subgroup ↥(preimageZpowers D a haM)).map
      (preimageZpowers D a haM).subtype : Subgroup G) = Subgroup.zpowers a := by
    rw [hS₀, Subgroup.map_subgroupOf_eq_of_le hzple]
  have hcoe : (S : Subgroup ↥(preimageZpowers D a haM)) =
      (S₀ : Subgroup ↥(preimageZpowers D a haM)).map
        (MulAut.conj (k : ↥(preimageZpowers D a haM))).toMonoidHom := by
    have hsmul : ∀ H : Subgroup ↥(preimageZpowers D a haM),
        MulAut.conj (k : ↥(preimageZpowers D a haM)) • H =
          H.map (MulAut.conj (k : ↥(preimageZpowers D a haM))).toMonoidHom := by
      intro H
      ext x
      rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
      exact ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩⟩
    rw [← hk, Sylow.coe_subgroup_smul, hsmul]
  refine ⟨k, ?_⟩
  rw [hcoe, Subgroup.map_map_conj, hS₀map]
  rfl

private theorem exists_isSylowOf_map_conj_le_normalizer (c : Ctx23L D Ch)
    {r : ℕ} {a b t : G} (hT : OmegaPlusTorus c r a b t) (haM : a ∈ D.M)
    {p : ℕ} (hp : p ∈ D.sig) {k : ↥(preimageZpowers D a haM)} {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M)))
    (hPS : P ≤ Subgroup.normalizer
      (((Subgroup.zpowers a).map (MulAut.conj (k : G)).toMonoidHom : Subgroup G) : Set G)) :
    ∃ P' : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P' (barPreimage D.M (centE D.M)) ∧
        P' ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have hkM : (k : G) ∈ D.M := uc22p21c_barPreimage_le D.M _ k.2
  haveI hchar : (CFSG.layer (Bar2 D.M)).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hlayer : (CFSG.layer (Bar2 D.M)).Normal :=
    Subgroup.normal_of_characteristic (H := CFSG.layer (Bar2 D.M))
  haveI hcentEn : (centE D.M).Normal := Subgroup.normal_centralizer
  have hHN : D.M ≤ Subgroup.normalizer
      ((barPreimage D.M (centE D.M) : Subgroup G) : Set G) :=
    uc22p22u_barPreimage_normalizes (M := D.M) (D := centE D.M)
  have hHmap : (barPreimage D.M (centE D.M)).map
      (MulAut.conj ((k : G)⁻¹)).toMonoidHom = barPreimage D.M (centE D.M) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHN (D.M.inv_mem hkM))
  have hP'Syl : CFSG.ABGLocalTools.IsSylowOf p
      (P.map (MulAut.conj ((k : G)⁻¹)).toMonoidHom) (barPreimage D.M (centE D.M)) := by
    have h1 := isSylowOf_map_conj hP ((k : G)⁻¹)
    rwa [hHmap] at h1
  have hP'norm : P.map (MulAut.conj ((k : G)⁻¹)).toMonoidHom ≤
      Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    have h1 : P.map (MulAut.conj ((k : G)⁻¹)).toMonoidHom ≤
        (Subgroup.normalizer (((Subgroup.zpowers a).map
          (MulAut.conj (k : G)).toMonoidHom : Subgroup G) : Set G)).map
            (MulAut.conj ((k : G)⁻¹)).toMonoidHom := Subgroup.map_mono hPS
    rw [map_conj_normalizer] at h1
    have h2 : ((Subgroup.zpowers a).map (MulAut.conj (k : G)).toMonoidHom : Subgroup G).map
        (MulAut.conj ((k : G)⁻¹)).toMonoidHom = Subgroup.zpowers a :=
      map_conj_map_conj_inv (Subgroup.zpowers a) (k : G)
    rwa [h2] at h1
  exact ⟨P.map (MulAut.conj ((k : G)⁻¹)).toMonoidHom, hP'Syl, hP'norm⟩

private theorem exists_sylow_le_normalizer_zpowers_of_torus (c : Ctx23L D Ch)
    (h1930 : H1930 D) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h2123 : S21_23 D Ch) (hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)))
    {r : ℕ} {a b t : G} (hT : OmegaPlusTorus c r a b t)
    {p : ℕ} (hp : p ∈ D.sig) :
    ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M)) ∧
        P ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  have haM : a ∈ D.M := c.mem_M_of_torus h1930 h4 hT
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (barPreimage D.M (centE D.M))
  obtain ⟨S, hS⟩ :=
    exists_sylow_r_le_normalizer_preimage c h1930 h4 h6 hsp h2123 hcyc hT haM hp hP
  obtain ⟨k, hk⟩ := exists_conj_zpowers_of_sylow c hT haM (S := S)
  rw [hk] at hS
  exact exists_isSylowOf_map_conj_le_normalizer c hT haM hp hP hS

end Ctx23L

theorem s23_22Hyp2120_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) :
    S23_22Hyp2120 D Ch := by
  intro h1930 c h2 r a b t hT h6 hsp h8 h2123 hcyc
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Ctx23L.commutator_hinf_oTwoF_le_pCoreOf c h1930 hcyc
  · exact Ctx23L.calC_normal_and_shape_excluded c h1930 h8
  · intro p hp
    exact Ctx23L.exists_sylow_le_normalizer_zpowers_of_torus c h1930 h4 h6 hsp h2123 hcyc hT hp
  · intro p hp hrank
    exact Ctx23L.not_invertedIn_zpowers_of_torus c h1930 h2123 hcyc hT hp hrank

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
