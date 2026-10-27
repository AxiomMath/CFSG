module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Alt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Spec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16t3_inf_le_cTilde (hset : Setting16 D V₀ V L) {m : ℕ} (hm : m = 6 ∨ m = 7)
    (e : ↥(lBar V₀ V hV L) ≃* alternatingGroup (Fin m)) {YL YK : Subgroup G}
    (hYL : S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL)
    (hYK : S16t3CoverK D V₀ V hV (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) YK)
    (hR : IsPGroup 2 ↥(YL ⊓ YK)) : YL ⊓ YK ≤ F11.CTilde D.M V₀ V := by
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hYLs : YL ≤ stabTil V₀ V := hYL.1.trans hMs
  let φ : ↥YL →* ↥(barSub V₀ V hV YL) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hYLs))
      (barSub V₀ V hV YL) (fun g => actTil_mem_barSub V₀ V hV g.2 (hYLs g.2))
  have hφ : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV YL ψ).1 hψ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  have hYKsub : (YK.subgroupOf YL).Normal := by
    have hh := hYK.2.1.comap (Subgroup.inclusion hYL.1)
    rwa [Subgroup.comap_inclusion_subgroupOf hYL.1 YK] at hh
  have hRnorm : ((YL ⊓ YK).subgroupOf YL).Normal := by
    rw [Subgroup.inf_subgroupOf_left YK YL]
    exact hYKsub
  have hRsub : IsPGroup 2 ↥((YL ⊓ YK).subgroupOf YL) := by
    have h1 : IsPGroup 2 ↥((YL ⊓ YK) ⊓ YL) := hR.to_inf_left
    have heq : ((YL ⊓ YK) ⊓ YL).subgroupOf YL = (YL ⊓ YK).subgroupOf YL := by
      rw [inf_comm (YL ⊓ YK) YL]
      exact Subgroup.inf_subgroupOf_left (YL ⊓ YK) YL
    have h2 : IsPGroup 2 ↥(((YL ⊓ YK) ⊓ YL).subgroupOf YL) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : (YL ⊓ YK) ⊓ YL ≤ YL)).symm
    rw [heq] at h2
    exact h2
  have hNpg : IsPGroup 2 ↥(((YL ⊓ YK).subgroupOf YL).map φ) := hRsub.map φ
  let N : Subgroup ↥(barSub V₀ V hV YL) := ((YL ⊓ YK).subgroupOf YL).map φ
  have hNnorm : N.Normal := hRnorm.map φ hφ
  have h5m : 5 ≤ Nat.card (Fin m) := by rcases hm with rfl | rfl <;> simp [Nat.card_fin]
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup h5m
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := e.isSimpleGroup
  haveI : IsSimpleGroup ↥(barSub V₀ V hV YL) :=
    (MulEquiv.subgroupCongr hYL.2.2.1).isSimpleGroup
  haveI : N.Normal := hNnorm
  have hNpg' : IsPGroup 2 ↥N := hNpg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · intro r hr
    have hrYL : r ∈ YL := hr.1
    have hrR : (⟨r, hrYL⟩ : ↥YL) ∈ (YL ⊓ YK).subgroupOf YL := by
      rw [Subgroup.mem_subgroupOf]
      exact hr
    have hmemN : φ ⟨r, hrYL⟩ ∈ N := by
      change φ ⟨r, hrYL⟩ ∈ ((YL ⊓ YK).subgroupOf YL).map φ
      exact Subgroup.mem_map_of_mem φ hrR
    have hphi1 : φ ⟨r, hrYL⟩ = 1 := by
      rw [hbot] at hmemN
      exact Subgroup.mem_bot.1 hmemN
    have hact : (φ ⟨r, hrYL⟩ : MulAut (Vtil V₀ V hV)) = 1 := by
      rw [hphi1]
      rfl
    exact (mem_cTilde_iff (M := D.M) hV hMn).2
      ⟨hYL.1 hrYL, hMs (hYL.1 hrYL), hact⟩
  · exfalso
    have hpg_top : IsPGroup 2 ↥(⊤ : Subgroup ↥(barSub V₀ V hV YL)) := by
      rw [htop] at hNpg'
      exact hNpg'
    have hpg_bar : IsPGroup 2 ↥(barSub V₀ V hV YL) :=
      hpg_top.of_equiv Subgroup.topEquiv
    have hpg_lbar : IsPGroup 2 ↥(lBar V₀ V hV L) :=
      hpg_bar.of_equiv (MulEquiv.subgroupCongr hYL.2.2.1)
    have hpg_alt : IsPGroup 2 ↥(alternatingGroup (Fin m)) := hpg_lbar.of_equiv e
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨c, hc⟩ := hpg_alt.exists_card_eq
    have h3dvd : 3 ∣ Nat.card ↥(alternatingGroup (Fin m)) := by
      rcases hm with rfl | rfl <;>
        rw [nat_card_alternatingGroup, Nat.card_fin] <;> norm_num [Nat.factorial]
    rw [hc] at h3dvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)

theorem s16t3_cube_of_cover_alt (hset : Setting16 D V₀ V L) {m : ℕ} (hm : m = 6 ∨ m = 7)
    (e : ↥(lBar V₀ V hV L) ≃* alternatingGroup (Fin m)) {YL : Subgroup G}
    (hYL : S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL) {u : G} (hu : u ∈ YL) {k : ℕ}
    (hk : u ^ 3 ^ k = 1) {n : ↥(lBar V₀ V hV L)}
    (hn : barHom V₀ V hV (s16g_le_stabTil hset) ⟨u, hYL.1 hu⟩ =
      (n : MulAut (Vtil V₀ V hV)))
    (hcyc : ((e n : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).cycleType = 0 ∨
      ((e n : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).cycleType = {3} ∨
      ((e n : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).cycleType = {3, 3}) :
    u ^ 3 = 1 := by
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hYLs : YL ≤ stabTil V₀ V := hYL.1.trans hMs
  let φ : ↥YL →* ↥(barSub V₀ V hV YL) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hYLs))
      (barSub V₀ V hV YL) (fun g => actTil_mem_barSub V₀ V hV g.2 (hYLs g.2))
  have hφ : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV YL ψ).1 hψ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  let eL : ↥(barSub V₀ V hV YL) ≃* alternatingGroup (Fin m) :=
    (MulEquiv.subgroupCongr hYL.2.2.1).trans e
  let π : ↥YL →* alternatingGroup (Fin m) := eL.toMonoidHom.comp φ
  have hπ : Function.Surjective π := by
    intro a
    obtain ⟨b, hb⟩ := eL.surjective a
    obtain ⟨c, hc⟩ := hφ b
    exact ⟨c, by rw [show π c = eL (φ c) from rfl, hc, hb]⟩
  have hNker : φ.ker = (YL ⊓ F11.CTilde D.M V₀ V).subgroupOf YL := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      mem_cTilde_iff (M := D.M) hV hMn]
    have hgY : (g : G) ∈ YL := g.2
    constructor
    · intro h1
      exact ⟨hgY, hYL.1 hgY, hYLs hgY, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1
  have hπker : π.ker = (YL ⊓ F11.CTilde D.M V₀ V).subgroupOf YL := by
    have h1 : π.ker = φ.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      change eL (φ x) = 1 ↔ φ x = 1
      exact ⟨fun hx => eL.injective (by rw [hx, map_one]),
        fun hx => by rw [hx, map_one]⟩
    rw [h1, hNker]
  let O : Subgroup ↥YL := CFSG.pCore 2 ↥YL
  haveI : O.Normal := CFSG.pCore_normal (p := 2) (G := ↥YL)
  have hO : IsPGroup 2 ↥O := CFSG.pCore_isPGroup (p := 2) (G := ↥YL)
  have hOker : O ≤ π.ker := by
    rw [hπker]
    simpa only [O] using hYL.2.2.2.2.1
  have hcent : π.ker.map (QuotientGroup.mk' O) ≤ Subgroup.center (↥YL ⧸ O) := by
    rw [hπker]
    simpa only [O] using hYL.2.2.2.2.2.1
  have hZ3 : ∀ x ∈ π.ker, ∀ r : ℕ, x ^ 3 ^ r = 1 → x ^ 3 = 1 := by
    intro x hx r hxr
    rw [hπker] at hx
    have hxG : (x : G) ∈ YL ⊓ F11.CTilde D.M V₀ V := Subgroup.mem_subgroupOf.mp hx
    have hxGr : (x : G) ^ 3 ^ r = 1 := congrArg Subtype.val hxr
    exact Subtype.ext (hYL.2.2.2.2.2.2.2 (x : G) hxG r hxGr)
  have huY : (⟨u, hu⟩ : ↥YL) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
  have hφu : φ ⟨u, hu⟩ = (MulEquiv.subgroupCongr hYL.2.2.1).symm n := by
    apply Subtype.ext
    exact hn
  have hπu : π ⟨u, hu⟩ = e n := by
    change eL (φ ⟨u, hu⟩) = e n
    rw [hφu]
    simp [eL]
  have hcyc' : ((π ⟨u, hu⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).cycleType = 0 ∨
      ((π ⟨u, hu⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).cycleType = {3} ∨
      ((π ⟨u, hu⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)).cycleType = {3, 3} := by
    rw [hπu]
    exact hcyc
  have hmain : (⟨u, hu⟩ : ↥YL) ^ 3 = 1 :=
    s16t3_pow_three_of_alt_cover hm π hπ O hO hOker hcent hZ3 huY hcyc'
  exact congrArg Subtype.val hmain

theorem s16t3_cube_of_cover_K (hset : Setting16 D V₀ V L)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) {YK : Subgroup G}
    (hYK : S16t3CoverK D V₀ V hV (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) YK)
    {v : G} (hv : v ∈ YK) {k : ℕ} (hk : v ^ 3 ^ k = 1) : v ^ 3 = 1 := by
  have hMs : D.M ≤ stabTil V₀ V := s16g_le_stabTil hset
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hvM : v ∈ D.M := hYK.1 hv
  let vbar : MulAut (Vtil V₀ V hV) := barHom V₀ V hV hMs ⟨v, hvM⟩
  have hvbar_mem : vbar ∈ barSub V₀ V hV YK :=
    actTil_mem_barSub V₀ V hV hv (hMs hvM)
  have hvbar_K : vbar ∈ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := by
    rw [← hYK.2.2.1]
    exact hvbar_mem
  have hvbar_pow : vbar ^ 3 ^ k = 1 := by
    have hsub : (⟨v, hvM⟩ : ↥D.M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    have h1 : barHom V₀ V hV hMs ((⟨v, hvM⟩ : ↥D.M) ^ (3 ^ k)) = 1 := by
      rw [hsub, map_one]
    rw [map_pow] at h1
    simpa [vbar] using h1
  have hdvd3k : orderOf vbar ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hvbar_pow
  have hdvd168 : orderOf vbar ∣ 168 := by
    have hh := Subgroup.orderOf_dvd_natCard
      (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) hvbar_K
    rw [hK] at hh
    exact hh
  have hdvd3 : orderOf vbar ∣ 3 := by
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd3k
    rw [hj]
    have hle1 : j ≤ 1 := by
      by_contra hlt
      have h2 : 2 ≤ j := by omega
      have h27 : 3 ^ 2 ∣ 168 := dvd_trans (pow_dvd_pow 3 h2) (by rwa [hj] at hdvd168)
      norm_num at h27
    simpa using pow_dvd_pow 3 hle1
  have hvbar3 : vbar ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd3
  have hv3C : v ^ 3 ∈ F11.CTilde D.M V₀ V := by
    have hker : (⟨v, hvM⟩ : ↥D.M) ^ 3 ∈ (barHom V₀ V hV hMs).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hvbar3
    rw [ker_barHom V₀ V hV hMn hMs] at hker
    simpa using Subgroup.mem_subgroupOf.mp hker
  have hv3YK : v ^ 3 ∈ YK := pow_mem hv 3
  obtain ⟨j, hj⟩ := hYK.2.2.2 ⟨v ^ 3, hv3YK, hv3C⟩
  have hj' : (v ^ 3) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hv3pow3 : (v ^ 3) ^ 3 ^ k = 1 := by
    rw [← pow_mul, mul_comm (3 : ℕ) (3 ^ k), pow_mul, hk, one_pow]
  have hdvd2 : orderOf (v ^ 3) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have hdvd3' : orderOf (v ^ 3) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hv3pow3
  have hcop : Nat.Coprime (2 ^ j) (3 ^ k) :=
    Nat.Coprime.pow j k ((Nat.coprime_primes Nat.prime_two Nat.prime_three).2 (by norm_num))
  have hone : orderOf (v ^ 3) = 1 := by
    have hd : orderOf (v ^ 3) ∣ Nat.gcd (2 ^ j) (3 ^ k) := Nat.dvd_gcd hdvd2 hdvd3'
    rw [hcop] at hd
    exact Nat.dvd_one.1 hd
  exact orderOf_eq_one_iff.mp hone

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
