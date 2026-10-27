module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneYLemma
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddKF7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneSp6Plane
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.KInputsL62

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811Sylow.SignedLift

variable {c : Ctx82E3 D} {h : Case811Sylow c} (s : SignedLift h)

private lemma exists_perfect_le_inf_centralizer_of_lbar {p : ℕ} {v : Fin 3 → ZMod 3}
    {K : Subgroup c.Lbar}
    (hKle : K ≤ Subgroup.centralizer ({s.c₀ (Multiplicative.ofAdd v)} : Set c.Lbar))
    (hKperf : ⁅K, K⁆ = K) (hKdvd : p ∣ Nat.card K) :
    ∃ J : Subgroup G, J ≤ c.L ⊓ Subgroup.centralizer
        (Subgroup.zpowers (s.pt v) : Set G) ∧ ⁅J, J⁆ = J ∧ p ∣ Nat.card J := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hXleL : Subgroup.zpowers (s.pt v) ≤ c.L := Subgroup.zpowers_le.mpr (s.pt_mem_L v)
  have hXpg : IsPGroup 3 (Subgroup.zpowers (s.pt v)) :=
    h.elemAbelian.isPGroup.to_le (Subgroup.zpowers_le.mpr (s.pt_mem_A v))
  let Y : Subgroup G := c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (s.pt v) : Set G)
  let g : ↥Y →* c.Lbar := (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp
    (Subgroup.inclusion inf_le_left)
  have hcent := Ctx82E3.centralizer_map_lbar c (q := 3) (by norm_num) hXleL hXpg
  rw [s.lbar_image_zpowers_pt, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hcent
  have hgrange : g.range = Subgroup.centralizer ({s.c₀ (Multiplicative.ofAdd v)} : Set c.Lbar) := by
    rw [show g.range = (Y.subgroupOf c.L).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)) from by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]]
    exact hcent.symm
  have hKleRange : K ≤ g.range := by rw [hgrange]; exact hKle
  let Y0 : Subgroup ↥Y := Subgroup.comap g K
  have hY0map : Y0.map g = K := by simpa [Y0] using Subgroup.map_comap_eq_self hKleRange
  let gK : ↥Y0 →* ↥K :=
    { toFun := fun y => ⟨g (y : ↥Y), y.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hgKsurj : Function.Surjective gK := by
    intro k
    have hk : (k : c.Lbar) ∈ Y0.map g := by rw [hY0map]; exact k.2
    obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp hk
    exact ⟨⟨y, hy⟩, Subtype.ext hyval⟩
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
  obtain ⟨P, hPperf, hPmap⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.exists_perfect_map_eq_top gK hgKsurj
  let f : ↥Y0 →* G := Y.subtype.comp Y0.subtype
  let J : Subgroup G := P.map f
  have hfinj : Function.Injective f := Y.subtype_injective.comp Y0.subtype_injective
  have hJle : J ≤ Y := by rintro x ⟨y, -, rfl⟩; exact (y : Y).2
  have hJperf : ⁅J, J⁆ = J :=
    (Subgroup.map_commutator P P f).symm.trans (by rw [hPperf])
  have hKdvdP : Nat.card ↥K ∣ Nat.card P := by
    simpa [hPmap] using Subgroup.card_map_dvd P gK
  have hcardPJ : Nat.card P = Nat.card J := (Subgroup.card_map_of_injective hfinj).symm
  refine ⟨J, hJle, hJperf, ?_⟩
  have hpdvdP : p ∣ Nat.card P := hKdvd.trans hKdvdP
  rwa [hcardPJ] at hpdvdP

private lemma two_le_pRank_inf_normalizer_pt_of_perfect {p : ℕ} (hp : p.Prime) {y : G}
    (hyM : y ∈ D.M) (hyA : y ∈ Subgroup.centralizer (h.A : Set G))
    (hyp : orderOf y = p) (hyL : y ∉ c.L) {v : Fin 3 → ZMod 3}
    (hK : ∃ K : Subgroup c.Lbar, K ≤ Subgroup.centralizer ({s.c₀ (.ofAdd v)} : Set c.Lbar) ∧
      ⁅K, K⁆ = K ∧ p ∣ Nat.card K) :
    2 ≤ CFSG.Open.pRank p
      (D.M ⊓ Subgroup.normalizer (Subgroup.zpowers (s.pt v) : Set G)) := by
  obtain ⟨K, hKle, hKperf, hKdvd⟩ := hK
  obtain ⟨J, hJle, -, hJdvd⟩ := exists_perfect_le_inf_centralizer_of_lbar s (p := p) (v := v)
    hKle hKperf hKdvd
  have hdvd : p ∣ Nat.card
      (c.L ⊓ Subgroup.centralizer (Subgroup.zpowers (s.pt v) : Set G) : Subgroup G) :=
    hJdvd.trans (Subgroup.card_dvd_of_le hJle)
  have hXleA : Subgroup.zpowers (s.pt v) ≤ h.A :=
    Subgroup.zpowers_le.mpr (s.pt_mem_A v)
  obtain ⟨R, hR, hRcard, hRle⟩ :=
    h.exists_elemAbelian_sq_le_inf_normalizer hp hyM hyA hyp hyL hXleA hdvd
  exact CFSG.SectionRank.le_pRank hp.one_lt hRle hR hRcard

private lemma false_of_perfect_image {p : ℕ} (hp : p.Prime) {J H X : Subgroup G}
    (hJle : J ≤ c.L ⊓ Subgroup.centralizer (X : Set G))
    (hJperf : ⁅J, J⁆ = J) (hJdvd : p ∣ Nat.card J)
    (hHdef : H = Subgroup.normalizer (X : Set G))
    (hsol : Group.IsSolvable ↥(((H ⊓ D.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)))) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hJL : J ≤ c.L := hJle.trans inf_le_left
  have hJC : J ≤ Subgroup.centralizer (X : Set G) := hJle.trans inf_le_right
  have hJH : J ≤ H := by
    rw [hHdef]
    exact hJC.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hJM : J ≤ D.M := hJL.trans c.hyp81.1
  let f : ↥H →* UC22.F07.QuotK7 p H := QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)
  let Nbar : Subgroup (UC22.F07.QuotK7 p H) := ((H ⊓ D.M).subgroupOf H).map f
  let Jbar : Subgroup (UC22.F07.QuotK7 p H) := (J.subgroupOf H).map f
  have hJbar_le : Jbar ≤ Nbar :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_inf hJH hJM))
  have hJsub_perf : ⁅J.subgroupOf H, J.subgroupOf H⁆ = J.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJH, hJperf]
  have hJbar_perf : ⁅Jbar, Jbar⁆ = Jbar := by
    have hmap := Subgroup.map_commutator (J.subgroupOf H) (J.subgroupOf H) f
    change ⁅Subgroup.map f (J.subgroupOf H), Subgroup.map f (J.subgroupOf H)⁆ =
      Subgroup.map f (J.subgroupOf H)
    rw [← hmap, hJsub_perf]
  haveI : Group.IsSolvable ↥Nbar := hsol
  haveI : Group.IsSolvable ↥Jbar :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJbar_le)
      (Subgroup.inclusion_injective hJbar_le)
  have hJbar_bot : Jbar = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥Jbar := (Subgroup.bot_or_nontrivial Jbar).resolve_left hne
    haveI : Group.IsPerfect ↥Jbar := Subgroup.isPerfect_iff.mpr hJbar_perf
    exact Group.IsPerfect.not_isSolvable ↥Jbar inferInstance
  have hJcore : J.subgroupOf H ≤ CFSG.pPrimeCore p ↥H := by
    have hbot : Subgroup.map f (J.subgroupOf H) = ⊥ := hJbar_bot
    have hle := (Subgroup.map_eq_bot_iff (J.subgroupOf H) (f := f)).mp hbot
    simpa [f] using hle
  have hcardJ : Nat.card (J.subgroupOf H) = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv
  have hp_dvd_core : p ∣ Nat.card (CFSG.pPrimeCore p ↥H) := by
    have h1 : p ∣ Nat.card (J.subgroupOf H) := by rw [hcardJ]; exact hJdvd
    exact h1.trans (Subgroup.card_dvd_of_le hJcore)
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mp
    (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥H))) hp_dvd_core

private lemma exists_perm_signs_one (v : Fin 3 → ZMod 3) (hv : v ≠ 0)
    (hw : ∃ i, ∀ j, j ≠ i → v j = 0) :
    ∃ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) ∧
      v = fun i => ε i * (![1, 0, 0] : Fin 3 → ZMod 3) (σ i) := by
  revert v
  decide +kernel

theorem good_of_perfect (hKF7 : UC22.KF7Use D) {p : ℕ} (hp : p ∈ D.sig) (hp5 : p ≠ 5) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hyp : orderOf y = p) (hyL : y ∉ c.L)
    {v : Fin 3 → ZMod 3} (hv : v ≠ 0)
    (hK : ∃ K : Subgroup c.Lbar, K ≤ Subgroup.centralizer ({s.c₀ (.ofAdd v)} : Set c.Lbar) ∧
      ⁅K, K⁆ = K ∧ p ∣ Nat.card K) : GoodPoint D.M (s.pt v) := by
  change Subgroup.normalizer (Subgroup.zpowers (s.pt v) : Set G) ≤ D.M
  by_contra hHM
  let H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers (s.pt v) : Set G)
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp2 : p ≠ 2 := by
    have := c.five_le_of_mem_sigma hp
    omega
  have hrank : 1 < CFSG.Open.pRank p (H ⊓ D.M) := by
    have h2 := two_le_pRank_inf_normalizer_pt_of_perfect s hp_prime hy.1 hy.2 hyp hyL hK
    have hEq : H ⊓ D.M = D.M ⊓ Subgroup.normalizer (Subgroup.zpowers (s.pt v) : Set G) := by
      rw [show H = Subgroup.normalizer (Subgroup.zpowers (s.pt v) : Set G) from rfl, inf_comm]
    rw [hEq]
    omega
  have hHne : H ≠ ⊤ := by
    haveI : IsSimpleGroup G := D.standing.simple
    have hXcard : Nat.card (Subgroup.zpowers (s.pt v)) = 3 := by
      rw [Nat.card_zpowers, s.orderOf_pt hv]
    exact CFSG.RankThree.PartOne.Sec9Excl.normalizer_ne_top_of_simple
      D.standing.nonab Nat.prime_three hXcard
  have hsec : UC22.F07.Sec7Hyp D p H :=
    ⟨hp_prime, hp2, c.isStronglyPEmbedded_of_mem_sigma hp, hHne, hHM, hrank⟩
  rcases hKF7 p hp H hsec with hsol | ⟨hp5eq, -⟩
  · obtain ⟨K, hKle, hKperf, hKdvd⟩ := hK
    obtain ⟨J, hJle, hJperf, hJdvd⟩ :=
      exists_perfect_le_inf_centralizer_of_lbar s (p := p) (v := v) hKle hKperf hKdvd
    exact false_of_perfect_image (c := c) hp_prime hJle hJperf hJdvd rfl hsol
  · exact hp5 hp5eq

theorem good_of_weight_one_or_three_of_l62 (hPf : K7L6TwoPerfect)
    (hlie : IsLie811 c.Lbar .l6 2 1) (hKF7 : UC22.KF7Use D) (h7 : 7 ∈ D.sig) {y : G}
    (hy : y ∈ D.M ⊓ Subgroup.centralizer (h.A : Set G)) (hy7 : orderOf y = 7) (hyL : y ∉ c.L)
    {v : Fin 3 → ZMod 3} (hv : v ≠ 0) (hw : (∀ i, v i ≠ 0) ∨ ∃ i, ∀ j, j ≠ i → v j = 0) :
    GoodPoint D.M (s.pt v) := by
  have hbase1 : GoodPoint D.M (s.pt ![1, 0, 0]) := by
    have hK : ∃ K : Subgroup c.Lbar, K ≤ Subgroup.centralizer
        ({s.c₀ (.ofAdd ![1, 0, 0])} : Set c.Lbar) ∧ ⁅K, K⁆ = K ∧ 7 ∣ Nat.card K :=
      hPf c.Lbar hlie h.Abar h.isElemAbelian_Abar h.card_Abar s.c₀ s.signed
        ![1, 0, 0] (Or.inl rfl)
    exact good_of_perfect s hKF7 h7 (by norm_num) hy hy7 hyL (by decide) hK
  have hbase3 : GoodPoint D.M (s.pt ![1, 1, 1]) := by
    have hK : ∃ K : Subgroup c.Lbar, K ≤ Subgroup.centralizer
        ({s.c₀ (.ofAdd ![1, 1, 1])} : Set c.Lbar) ∧ ⁅K, K⁆ = K ∧ 7 ∣ Nat.card K :=
      hPf c.Lbar hlie h.Abar h.isElemAbelian_Abar h.card_Abar s.c₀ s.signed
        ![1, 1, 1] (Or.inr rfl)
    exact good_of_perfect s hKF7 h7 (by norm_num) hy hy7 hyL (by decide) hK
  rcases hw with hw3 | hw1
  · obtain ⟨g, -, hg⟩ := s.exists_conj (1 : Equiv.Perm (Fin 3)) v hw3
    have hgM : (g : G) ∈ D.M := c.hyp81.1 g.2
    have hc := hbase3.conj hgM
    rw [hg ![1, 1, 1]] at hc
    have hfun : (fun i => v i * (![1, 1, 1] : Fin 3 → ZMod 3)
        ((1 : Equiv.Perm (Fin 3)) i)) = v := by
      funext i
      fin_cases i <;> simp
    rwa [hfun] at hc
  · obtain ⟨σ, ε, hε, hv'⟩ := exists_perm_signs_one v hv hw1
    obtain ⟨g, -, hg⟩ := s.exists_conj σ ε hε
    have hgM : (g : G) ∈ D.M := c.hyp81.1 g.2
    have hc := hbase1.conj hgM
    rw [hg ![1, 0, 0]] at hc
    rwa [← hv'] at hc

end Case811Sylow.SignedLift

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
