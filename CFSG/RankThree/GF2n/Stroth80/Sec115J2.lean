module

public import CFSG.RankThree.GF2n.Stroth80.Sec115Excl
public import CFSG.RankThree.GF2n.Stroth80.Sec115Root
public import CFSG.RankThree.GF2n.Stroth80.Sec115Kt
public import CFSG.Sporadic.J2.CentEA
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55MJ2
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec112
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOddCore
import CFSG.Timmesfeld.LocalTwoSubgroups.CoprimeActionBounds

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

private noncomputable abbrev xbarToMod {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] :
    ↥(Xbar M Q Z B) →* XbarMod M Q Z B :=
  QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))

omit [Finite G] in
private theorem xbarToMod_ker :
    (xbarToMod (M := M) (Q := Q) (Z := Z) (B := B)).ker =
      Subgroup.center ↥(Xbar M Q Z B) :=
  QuotientGroup.ker_mk' _

private noncomputable abbrev xbarClassOfA (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) : ↥(Xbar M Q Z B) :=
  ⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨a, hc.LB_le_M ha⟩,
    Subgroup.subset_closure (hc.mk_mem_Ebar ha hA)⟩

private noncomputable abbrev tOfA (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) : XbarMod M Q Z B :=
  xbarToMod (xbarClassOfA hc ha hA)

private theorem mem_ebarIn_xbarClassOfA (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) : xbarClassOfA hc ha hA ∈ EbarIn M Q Z B :=
  hc.mk_mem_Ebar ha hA

omit [Finite G] in
private theorem isConj_map_of_mem_EbarIn {d₀ : ↥(Xbar M Q Z B)}
    (hcls : EbarIn M Q Z B = {g | IsConj d₀ g}) {u v : ↥(Xbar M Q Z B)}
    (hu : u ∈ EbarIn M Q Z B) (hv : v ∈ EbarIn M Q Z B) :
    IsConj (xbarToMod u) (xbarToMod v) := by
  rw [hcls] at hu hv
  obtain ⟨c, hc'⟩ := isConj_iff.1 hu
  obtain ⟨c', hc''⟩ := isConj_iff.1 hv
  refine MonoidHom.map_isConj (xbarToMod (M := M) (Q := Q) (Z := Z) (B := B)) ?_
  rw [isConj_iff]
  refine ⟨c' * c⁻¹, ?_⟩
  rw [← hc', ← hc'']
  group

private theorem orderOf_xbarToMod_mul_eq_four (hc : Ctx M Q Z B) {d e : Mbar M Q}
    (hd : d ∈ Ebar M Q Z B) (he : e ∈ Ebar M Q Z B) (hde : orderOf (d * e) = 4)
    (hde2 : (d * e) ^ 2 ∈ Ebar M Q Z B) :
    orderOf (xbarToMod (⟨d * e, Subgroup.mul_mem _ (Subgroup.subset_closure hd)
      (Subgroup.subset_closure he)⟩ : ↥(Xbar M Q Z B))) = 4 := by
  set x0 : ↥(Xbar M Q Z B) :=
    ⟨d * e, Subgroup.mul_mem _ (Subgroup.subset_closure hd) (Subgroup.subset_closure he)⟩
  have hde4 : (d * e) ^ 4 = 1 := by
    rw [← hde]
    exact pow_orderOf_eq_one (d * e)
  have hx4 : x0 ^ 4 = 1 := by
    apply Subtype.ext
    simpa [x0] using hde4
  have hx2 : xbarToMod x0 ^ 2 ≠ 1 := by
    intro h
    have h2 : xbarToMod (x0 ^ 2) = (1 : XbarMod M Q Z B) := by
      rw [map_pow]; exact h
    have hmem : (x0 ^ 2 : ↥(Xbar M Q Z B)) ∈
        (xbarToMod (M := M) (Q := Q) (Z := Z) (B := B)).ker :=
      MonoidHom.mem_ker.mpr h2
    rw [xbarToMod_ker] at hmem
    have hmemE : ((x0 ^ 2 : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B := by
      simpa [x0] using hde2
    exact hc.not_mem_center_Xbar_of_mem_Ebar hmemE hmem
  have hdvd : orderOf (xbarToMod x0) ∣ 4 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hx4, map_one]
  have h1 : orderOf (xbarToMod x0) ≠ 1 := by
    intro h
    have hx1 : xbarToMod x0 = 1 := orderOf_eq_one_iff.mp h
    exact hx2 (by rw [hx1]; exact one_pow 2)
  have h2 : orderOf (xbarToMod x0) ≠ 2 := fun h =>
    hx2 (by rw [← h]; exact pow_orderOf_eq_one _)
  have hdvd' : orderOf (xbarToMod x0) ∣ 2 ^ 2 := by simpa using hdvd
  obtain ⟨m, hm, hk⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).1 hdvd'
  rw [hk] at h1 h2 ⊢
  interval_cases m <;> simp_all

private theorem centralizer_map_xbarToMod (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) :
    (Subgroup.centralizer ({tOfA hc ha hA} : Set (XbarMod M Q Z B))) =
      (Subgroup.centralizer ({xbarClassOfA hc ha hA} : Set ↥(Xbar M Q Z B))).map
        (xbarToMod (M := M) (Q := Q) (Z := Z) (B := B)) := by
  have hcent : ∀ {K : Type} [Group K] (y : K),
      Subgroup.centralizer ((Subgroup.zpowers y : Subgroup K) : Set K) =
        Subgroup.centralizer ({y} : Set K) := by
    intro K _ y
    ext z
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact (h y (Subgroup.mem_zpowers y)).symm
    · intro h w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (((commute_iff_eq z y).mpr h).zpow_right n).eq.symm
  have hQ : IsPGroup 2 ↥(Subgroup.zpowers (xbarClassOfA hc ha hA)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_two_of_mem_ebarIn (mem_ebarIn_xbarClassOfA hc ha hA)]
    norm_num
  have hN : ¬ 2 ∣ Nat.card ↥(Subgroup.center ↥(Xbar M Q Z B)) :=
    hc.odd_card_center_Xbar.not_two_dvd_nat
  have h := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 2)
    (N := Subgroup.center ↥(Xbar M Q Z B)) hN hQ
  rw [MonoidHom.map_zpowers] at h
  rw [hcent, hcent] at h
  exact h

private theorem orderOf_tOfA (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) : orderOf (tOfA hc ha hA) = 2 := by
  have hsq : xbarClassOfA hc ha hA * xbarClassOfA hc ha hA = 1 := by
    rw [← pow_two, ← orderOf_eq_two_of_mem_ebarIn (mem_ebarIn_xbarClassOfA hc ha hA)]
    exact pow_orderOf_eq_one _
  have ht2 : tOfA hc ha hA * tOfA hc ha hA = 1 := by
    rw [← map_mul, hsq, map_one]
  have htne : tOfA hc ha hA ≠ 1 := by
    intro h
    have hmem : xbarClassOfA hc ha hA ∈
        (xbarToMod (M := M) (Q := Q) (Z := Z) (B := B)).ker :=
      MonoidHom.mem_ker.mpr h
    rw [xbarToMod_ker] at hmem
    exact hc.not_mem_center_Xbar_of_mem_Ebar (mem_ebarIn_xbarClassOfA hc ha hA) hmem
  have hdvd : orderOf (tOfA hc ha hA) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two]
    exact ht2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) htne
  · exact h

omit [Finite G] in
private theorem conj_apply_xbarToMod (y z : ↥(Xbar M Q Z B)) :
    MulAut.conj (xbarToMod y) (xbarToMod z) = xbarToMod (y * z * y⁻¹) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem xbarToMod_barLBConjAct (hc : Ctx M Q Z B)
    (l : ↥(bar M Q (LB M Q B))) (x : ↥(Xbar M Q Z B)) :
    xbarToMod (barLBConjAct hc l x) =
      xbarToMod ⟨(l : Mbar M Q) * (x : Mbar M Q) * (l : Mbar M Q)⁻¹,
        hc.Xbar_normal.conj_mem (x : Mbar M Q) x.2 (l : Mbar M Q)⟩ := by
  rw [barLBConjAct_apply]

private theorem conj_mul_xbarModConjAct (hc : Ctx M Q Z B) (k : ↥(Xbar M Q Z B))
    (hkN : (k : Mbar M Q) ∈ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q)))
    (l : ↥(bar M Q (LB M Q B))) :
    MulAut.conj (xbarToMod k) * xbarModConjAct hc l *
        (MulAut.conj (xbarToMod k))⁻¹ =
      xbarModConjAct hc ⟨(k : Mbar M Q) * (l : Mbar M Q) * (k : Mbar M Q)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hkN (l : Mbar M Q)).1 l.2⟩ := by
  have hinv : (MulAut.conj (xbarToMod k))⁻¹ = MulAut.conj ((xbarToMod k)⁻¹) :=
    (map_inv MulAut.conj _).symm
  have hninv : (xbarToMod k)⁻¹ = xbarToMod k⁻¹ :=
    (map_inv (xbarToMod (M := M) (Q := Q) (Z := Z) (B := B)) _).symm
  ext x
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(Xbar M Q Z B)) x
  simp only [MulAut.mul_apply, hinv, hninv, conj_apply_xbarToMod,
    xbarModConjAct_apply_mk, xbarToMod_barLBConjAct]
  apply congrArg xbarToMod
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

private noncomputable def innerPart (hc : Ctx M Q Z B) :
    Subgroup (MulAut (XbarMod M Q Z B)) :=
  (xbarModConjAct hc).range ⊓ (MulAut.conj (G := XbarMod M Q Z B)).range

private noncomputable def innerSubgroup (hc : Ctx M Q Z B) :
    Subgroup (XbarMod M Q Z B) :=
  (innerPart hc).comap (MulAut.conj (G := XbarMod M Q Z B))

private noncomputable def normalizerImage (K : Subgroup (Mbar M Q)) :
    Subgroup (XbarMod M Q Z B) :=
  (K.subgroupOf (Xbar M Q Z B)).map (xbarToMod (M := M) (Q := Q) (Z := Z) (B := B))

private theorem mem_centralizer_xbarToMod_iff (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {y : ↥(Xbar M Q Z B)} :
    xbarToMod y ∈ Subgroup.centralizer ({tOfA hc ha hA} : Set (XbarMod M Q Z B)) ↔
      y ∈ Subgroup.centralizer ({xbarClassOfA hc ha hA} : Set ↥(Xbar M Q Z B)) := by
  rw [centralizer_map_xbarToMod hc ha hA]
  constructor
  · intro hy
    obtain ⟨y', hy', hyeq⟩ := Subgroup.mem_map.mp hy
    have hz : y⁻¹ * y' ∈ (xbarToMod (M := M) (Q := Q) (Z := Z) (B := B)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyeq, inv_mul_cancel]
    rw [xbarToMod_ker] at hz
    have hye : y = y' * (y⁻¹ * y')⁻¹ := by group
    rw [hye]
    exact Subgroup.mul_mem _ hy' (Subgroup.center_le_centralizer _ (Subgroup.inv_mem _ hz))
  · intro hy
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩

private theorem mem_inf_centralizer_of_mem_centralizer (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {y : ↥(Xbar M Q Z B)}
    (hy : y ∈ Subgroup.centralizer ({xbarClassOfA hc ha hA} : Set ↥(Xbar M Q Z B))) :
    (y : Mbar M Q) ∈ Xbar M Q Z B ⊓ Subgroup.centralizer
      ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)) := by
  refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))

private theorem normalizerImage_normal (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) {K : Subgroup (Mbar M Q)}
    (hKnorm : ∀ c ∈ Xbar M Q Z B ⊓ Subgroup.centralizer
      ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)),
        ∀ k ∈ K, c * k * c⁻¹ ∈ K) :
    ∀ c ∈ Subgroup.centralizer ({tOfA hc ha hA} : Set (XbarMod M Q Z B)),
      ∀ k ∈ normalizerImage (M := M) (Q := Q) (Z := Z) (B := B) K,
        c * k * c⁻¹ ∈ normalizerImage (M := M) (Q := Q) (Z := Z) (B := B) K := by
  intro c hcC k hkN
  rw [centralizer_map_xbarToMod hc ha hA] at hcC
  obtain ⟨c0, hc0, heqc⟩ := Subgroup.mem_map.mp hcC
  obtain ⟨k0, hk0, heqk⟩ := Subgroup.mem_map.mp hkN
  refine Subgroup.mem_map.mpr ⟨c0 * k0 * c0⁻¹, ?_, ?_⟩
  · exact hKnorm (c0 : Mbar M Q) (mem_inf_centralizer_of_mem_centralizer hc ha hA hc0)
      (k0 : Mbar M Q) (Subgroup.mem_subgroupOf.mp hk0)
  · rw [map_mul, map_mul, map_inv, heqc, heqk]

private theorem normalizerImage_sq (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) {K : Subgroup (Mbar M Q)}
    (hKsq : ∀ x ∈ Xbar M Q Z B ⊓ Subgroup.centralizer
      ({(QuotientGroup.mk (⟨a, hc.LB_le_M ha⟩ : ↥M) : Mbar M Q)} : Set (Mbar M Q)),
        (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 ∈ K) :
    ∀ x ∈ Subgroup.centralizer ({tOfA hc ha hA} : Set (XbarMod M Q Z B)),
      (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 ∈
        normalizerImage (M := M) (Q := Q) (Z := Z) (B := B) K := by
  intro x hx hex
  have hodd : Odd (Nat.card ↥(xbarToMod (M := M) (Q := Q) (Z := Z) (B := B)).ker) := by
    rw [xbarToMod_ker]
    exact hc.odd_card_center_Xbar
  obtain ⟨e, he⟩ := hex
  obtain ⟨y, hyx, hy2⟩ := CFSG.SeitzReduction.LinearPilot.exists_lift_pow_two_pow_eq_one
    (xbarToMod (M := M) (Q := Q) (Z := Z) (B := B))
    (QuotientGroup.mk'_surjective _) hodd he
  have hyC : y ∈ Subgroup.centralizer ({xbarClassOfA hc ha hA} : Set ↥(Xbar M Q Z B)) :=
    (mem_centralizer_xbarToMod_iff hc ha hA).mp (by rw [hyx]; exact hx)
  refine Subgroup.mem_map.mpr ⟨y ^ 2, ?_, by rw [map_pow, hyx]⟩
  have hy2' : (y : Mbar M Q) ^ 2 ^ e = 1 := by
    simpa using congrArg Subtype.val hy2
  exact hKsq (y : Mbar M Q) (mem_inf_centralizer_of_mem_centralizer hc ha hA hyC) ⟨e, hy2'⟩

private theorem normalizerImage_normalizes (hc : Ctx M Q Z B)
    {K : Subgroup (Mbar M Q)}
    (hKN : K ≤ Subgroup.normalizer (bar M Q (LB M Q B) : Set (Mbar M Q))) :
    normalizerImage (M := M) (Q := Q) (Z := Z) (B := B) K ≤
      Subgroup.normalizer ((innerSubgroup hc : Subgroup (XbarMod M Q Z B)) :
        Set (XbarMod M Q Z B)) := by
  rw [Subgroup.le_normalizer_iff]
  intro n hn e he
  obtain ⟨k0, hk0, heqn⟩ := Subgroup.mem_map.mp hn
  change MulAut.conj (n * e * n⁻¹) ∈ innerPart hc
  change MulAut.conj e ∈ innerPart hc at he
  have hconj : ∀ y : XbarMod M Q Z B,
      MulAut.conj (xbarToMod k0 * y * (xbarToMod k0)⁻¹) =
        MulAut.conj (xbarToMod k0) * MulAut.conj y *
          (MulAut.conj (xbarToMod k0))⁻¹ := by
    intro y
    rw [map_mul, map_mul, map_inv]
  rw [← heqn, hconj]
  obtain ⟨heeA, heeI⟩ := Subgroup.mem_inf.mp he
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp heeA
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp heeI
  have hkK : (k0 : Mbar M Q) ∈ K := Subgroup.mem_subgroupOf.mp hk0
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [← hl, conj_mul_xbarModConjAct hc k0 (hKN hkK) l]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  · rw [← hg, ← hconj g]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

private theorem exists_centralizer_normalizing_subgroup (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) :
    ∃ N : Subgroup (XbarMod M Q Z B),
      (∀ c ∈ Subgroup.centralizer ({tOfA hc ha hA} : Set (XbarMod M Q Z B)),
        ∀ k ∈ N, c * k * c⁻¹ ∈ N) ∧
      (∀ x ∈ Subgroup.centralizer ({tOfA hc ha hA} : Set (XbarMod M Q Z B)),
        (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 ∈ N) ∧
      N ≤ Subgroup.normalizer ((innerSubgroup hc : Subgroup (XbarMod M Q Z B)) :
        Set (XbarMod M Q Z B)) := by
  obtain ⟨K, hKle, hKnorm, hKsq, hKN⟩ := hc.exists_normal_normalizer_LB_of_isA2 ha hA
  exact ⟨normalizerImage (M := M) (Q := Q) (Z := Z) (B := B) K,
    normalizerImage_normal hc ha hA hKnorm, normalizerImage_sq hc ha hA hKsq,
    normalizerImage_normalizes hc hKN⟩

private noncomputable abbrev aBarOf (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B) :
    ↥(bar M Q (LB M Q B)) :=
  ⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨a, hc.LB_le_M ha⟩,
    Subgroup.mem_map.mpr ⟨⟨a, hc.LB_le_M ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩⟩

private theorem xbarModConjAct_aBarOf (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a) :
    xbarModConjAct hc (aBarOf hc ha) = MulAut.conj (tOfA hc ha hA) := by
  ext x
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(Xbar M Q Z B)) x
  rw [xbarModConjAct_apply_mk, xbarToMod_barLBConjAct, conj_apply_xbarToMod]
  apply congrArg xbarToMod
  apply Subtype.ext
  rfl


private theorem card_range_le_two_mul_card_innerPart (hc : Ctx M Q Z B)
    (hInn : Nat.card ↥(MulAut.conj (G := XbarMod M Q Z B)).range =
      Nat.card (XbarMod M Q Z B))
    (hAut : Nat.card (MulAut (XbarMod M Q Z B)) ≤ 2 * Nat.card (XbarMod M Q Z B)) :
    Nat.card (xbarModConjAct hc).range ≤ 2 * Nat.card (innerPart hc) := by
  have hnorm : ∀ b ∈ (xbarModConjAct hc).range,
      ∀ a ∈ (MulAut.conj (G := XbarMod M Q Z B)).range, b * a * b⁻¹ ∈
        (MulAut.conj (G := XbarMod M Q Z B)).range := by
    intro b _ a ha
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp ha
    refine MonoidHom.mem_range.mpr ⟨b g, ?_⟩
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]
    rw [map_mul, map_mul, map_inv]
    simp
  have hsup := CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
    (xbarModConjAct hc).range (MulAut.conj (G := XbarMod M Q Z B)).range hnorm
  have hsup_le : Nat.card ↥((xbarModConjAct hc).range ⊔
      (MulAut.conj (G := XbarMod M Q Z B)).range) ≤ Nat.card (MulAut (XbarMod M Q Z B)) := by
    have h := Subgroup.card_le_of_le
      (le_top : (xbarModConjAct hc).range ⊔ (MulAut.conj (G := XbarMod M Q Z B)).range ≤ ⊤)
    rwa [Subgroup.card_top] at h
  have hmain : Nat.card (xbarModConjAct hc).range * Nat.card (XbarMod M Q Z B) ≤
      (2 * Nat.card (innerPart hc)) * Nat.card (XbarMod M Q Z B) := by
    calc Nat.card (xbarModConjAct hc).range * Nat.card (XbarMod M Q Z B)
        = Nat.card (xbarModConjAct hc).range *
            Nat.card ↥(MulAut.conj (G := XbarMod M Q Z B)).range := by rw [hInn]
      _ = Nat.card ↥((xbarModConjAct hc).range ⊔
            (MulAut.conj (G := XbarMod M Q Z B)).range) * Nat.card (innerPart hc) := by
          rw [innerPart, ← hsup]
      _ ≤ Nat.card (MulAut (XbarMod M Q Z B)) * Nat.card (innerPart hc) :=
          Nat.mul_le_mul_right _ hsup_le
      _ ≤ (2 * Nat.card (XbarMod M Q Z B)) * Nat.card (innerPart hc) :=
          Nat.mul_le_mul_right _ hAut
      _ = (2 * Nat.card (innerPart hc)) * Nat.card (XbarMod M Q Z B) := by ring
  exact Nat.le_of_mul_le_mul_right hmain Nat.card_pos

omit [Finite G] in
private theorem center_eq_bot_of_isSporadic_J2
    (hJ : CFSG.Blueprint.NativeSporadic.IsSporadic (XbarMod M Q Z B) .J2) :
    Subgroup.center (XbarMod M Q Z B) = ⊥ := by
  obtain ⟨e⟩ := hJ
  let φ : XbarMod M Q Z B ≃* ↥CFSG.Sporadic.Schreier.j2P :=
    e.trans CFSG.Sporadic.Schreier.j2PermEquiv
  rw [eq_bot_iff]
  intro x hx
  have h1 : φ x ∈ Subgroup.map φ (Subgroup.center (XbarMod M Q Z B)) :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [Subgroup.map_center_eq, CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.j2P_center_eq_bot] at h1
  rw [Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (φ.injective (h1.trans (map_one φ).symm))

omit [Finite G] in
private theorem injective_conj_of_isSporadic_J2
    (hJ : CFSG.Blueprint.NativeSporadic.IsSporadic (XbarMod M Q Z B) .J2) :
    Function.Injective (MulAut.conj (G := XbarMod M Q Z B)) := by
  have hcenter := center_eq_bot_of_isSporadic_J2 hJ
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [← hcenter, Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun f : MulAut (XbarMod M Q Z B) => f g) hx
  simp only [MulAut.conj_apply] at h
  have h' : x * g * x⁻¹ = g := by simpa using h
  calc g * x = (x * g * x⁻¹) * x := by rw [h']
    _ = x * g := by group

private theorem eight_le_card_innerPart (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {y : G} (hy : IsLBTorus M Q Z B y)
    (hJ : CFSG.Blueprint.NativeSporadic.IsSporadic (XbarMod M Q Z B) .J2) :
    8 ≤ Nat.card (innerPart hc) := by
  obtain ⟨e⟩ := hJ
  let φ : XbarMod M Q Z B ≃* ↥CFSG.Sporadic.Schreier.j2P :=
    e.trans CFSG.Sporadic.Schreier.j2PermEquiv
  have hconjinj := injective_conj_of_isSporadic_J2 ⟨e⟩
  have hInn : Nat.card ↥(MulAut.conj (G := XbarMod M Q Z B)).range =
      Nat.card (XbarMod M Q Z B) := by
    rw [← Subgroup.map_top (MulAut.conj (G := XbarMod M Q Z B)),
      Subgroup.card_map_of_injective hconjinj, Subgroup.card_top]
  have hAut : Nat.card (MulAut (XbarMod M Q Z B)) ≤ 2 * Nat.card (XbarMod M Q Z B) := by
    have h := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.j2_mulAut_card_le
    have e1 : Nat.card (MulAut (XbarMod M Q Z B)) =
        Nat.card (MulAut ↥CFSG.Sporadic.Schreier.j2P) :=
      Nat.card_congr (MulAut.congr φ).toEquiv
    have e2 : Nat.card (XbarMod M Q Z B) =
        Nat.card ↥CFSG.Sporadic.Schreier.j2P := Nat.card_congr φ.toEquiv
    rwa [e1, e2]
  have hle := card_range_le_two_mul_card_innerPart hc hInn hAut
  have hA16 := hc.sixteen_le_card_xbarModConjAct_range hw hn ha2 hy
  omega

private theorem card_innerSubgroup_eq_innerPart (hc : Ctx M Q Z B)
    (hconjinj : Function.Injective (MulAut.conj (G := XbarMod M Q Z B))) :
    Nat.card (innerSubgroup hc) = Nat.card (innerPart hc) := by
  have hmap : (innerSubgroup hc).map (MulAut.conj (G := XbarMod M Q Z B)) = innerPart hc :=
    Subgroup.map_comap_eq_self (fun x hx => hx.2)
  rw [← Subgroup.card_map_of_injective (f := MulAut.conj (G := XbarMod M Q Z B))
    (K := innerSubgroup hc) hconjinj, hmap]

private theorem isElemAbelian_innerSubgroup (hc : Ctx M Q Z B)
    (hconjinj : Function.Injective (MulAut.conj (G := XbarMod M Q Z B))) :
    CFSG.Open.IsElemAbelian 2 (innerSubgroup hc) := by
  have hA := hc.isElemAbelian_xbarModConjAct_range
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    apply hconjinj
    rw [map_mul, map_mul]
    have hxA : MulAut.conj (x : XbarMod M Q Z B) ∈ (xbarModConjAct hc).range :=
      (Subgroup.mem_comap.mp x.2).1
    have hyA : MulAut.conj (y : XbarMod M Q Z B) ∈ (xbarModConjAct hc).range :=
      (Subgroup.mem_comap.mp y.2).1
    exact congrArg Subtype.val
      (hA.1.is_comm.comm (⟨_, hxA⟩ : (xbarModConjAct hc).range) ⟨_, hyA⟩)
  · apply hconjinj
    rw [map_pow, map_one]
    exact hA.2 (MulAut.conj x) (Subgroup.mem_comap.mp hx).1

private theorem innerSubgroup_le_centralizer (hc : Ctx M Q Z B) {a : G} (ha : a ∈ LB M Q B)
    (hA : IsA2 Q Z a)
    (hconjinj : Function.Injective (MulAut.conj (G := XbarMod M Q Z B))) :
    innerSubgroup hc ≤
      Subgroup.centralizer ({tOfA hc ha hA} : Set (XbarMod M Q Z B)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxA : MulAut.conj (x : XbarMod M Q Z B) ∈ (xbarModConjAct hc).range :=
    (Subgroup.mem_comap.mp hx).1
  have htA : MulAut.conj (tOfA hc ha hA) ∈ (xbarModConjAct hc).range := by
    rw [← xbarModConjAct_aBarOf hc ha hA]
    exact MonoidHom.mem_range.mpr ⟨aBarOf hc ha, rfl⟩
  have hcomm := hc.isElemAbelian_xbarModConjAct_range.1.is_comm.comm
    (⟨_, hxA⟩ : (xbarModConjAct hc).range) ⟨_, htA⟩
  have hcomm' : MulAut.conj (x : XbarMod M Q Z B) * MulAut.conj (tOfA hc ha hA) =
      MulAut.conj (tOfA hc ha hA) * MulAut.conj (x : XbarMod M Q Z B) :=
    congrArg Subtype.val hcomm
  rw [← map_mul, ← map_mul] at hcomm'
  exact hconjinj hcomm'

private theorem exists_j2Cent_of_nondegenerate (hc : Ctx M Q Z B) {a : G}
    (ha : a ∈ LB M Q B) (hA : IsA2 Q Z a) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hnd : ∃ d ∈ Ebar M Q Z B, ∃ e ∈ Ebar M Q Z B, orderOf (d * e) = 4)
    (hJ : CFSG.Blueprint.NativeSporadic.IsSporadic (XbarMod M Q Z B) .J2) :
    ∃ E : Subgroup (XbarMod M Q Z B),
      CFSG.GH74.GLS.C3.Layer1.Bk.J2C.J2CentFacts (XbarMod M Q Z B) (tOfA hc ha hA) E ∧
      CFSG.Sporadic.J2.J2CentEAFacts (XbarMod M Q Z B) (tOfA hc ha hA) E := by
  obtain ⟨d, hd, e, he, hde⟩ := hnd
  obtain ⟨⟨d₀, hcls⟩, -, -, -, -⟩ := hc.ebarIn_rootData hw hn ⟨a, ha, hA⟩ stroth112_holds
  have hde2 : (d * e) ^ 2 ∈ Ebar M Q Z B :=
    (stroth112_holds G M Q Z B hc n hw hn ⟨a, ha, hA⟩).2 d hd e he |>.2 hde
  set x0 : ↥(Xbar M Q Z B) :=
    ⟨d * e, Subgroup.mul_mem _ (Subgroup.subset_closure hd) (Subgroup.subset_closure he)⟩
    with hx0
  have hxord : orderOf (xbarToMod x0) = 4 := by
    rw [hx0]
    exact orderOf_xbarToMod_mul_eq_four hc hd he hde hde2
  have hx2E : x0 ^ 2 ∈ EbarIn M Q Z B := by
    change ((x0 ^ 2 : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B
    rw [hx0]
    simpa using hde2
  have ht2 : orderOf (tOfA hc ha hA) = 2 := orderOf_tOfA hc ha hA
  have hconj : IsConj (tOfA hc ha hA) (xbarToMod x0 ^ 2) := by
    rw [← map_pow]
    exact isConj_map_of_mem_EbarIn hcls (mem_ebarIn_xbarClassOfA hc ha hA) hx2E
  have h128 : 2 ^ 7 ∣ Nat.card (Subgroup.centralizer
      ({tOfA hc ha hA} : Set (XbarMod M Q Z B))) :=
    CFSG.Sporadic.J2.two_pow_seven_dvd_card_centralizer_of_sq_isConj hJ hxord hconj
  obtain ⟨E, hE⟩ := CFSG.GH74.GLS.C3.Layer1.Bk.J2C.j2_cent_facts hJ ht2 h128
  exact ⟨E, hE, CFSG.Sporadic.J2.j2_cent_ea_facts hJ ht2 h128 hE⟩

theorem Ctx.not_isSporadic_J2_xbarMod (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hnd : ∃ d ∈ Ebar M Q Z B, ∃ e ∈ Ebar M Q Z B, orderOf (d * e) = 4) :
    ¬ CFSG.Blueprint.NativeSporadic.IsSporadic (XbarMod M Q Z B) .J2 := by
  intro hJ
  obtain ⟨a, haL, haA⟩ := ha2
  obtain ⟨y, hy⟩ := hc.exists_isLBTorus
  obtain ⟨E, hE, hEA⟩ := exists_j2Cent_of_nondegenerate hc haL haA hw hn hnd hJ
  obtain ⟨N, hNn, hNsq, hNA⟩ := exists_centralizer_normalizing_subgroup hc haL haA
  have hconjinj := injective_conj_of_isSporadic_J2 hJ
  have hcardE := card_innerSubgroup_eq_innerPart hc hconjinj
  have hEe := isElemAbelian_innerSubgroup hc hconjinj
  have hEcent := innerSubgroup_le_centralizer hc haL haA hconjinj
  have height : 8 ≤ Nat.card (innerSubgroup hc) := by
    rw [hcardE]
    exact eight_le_card_innerPart hc hw hn ⟨a, haL, haA⟩ hy hJ
  have hfour : Nat.card (innerSubgroup hc) ≤ 4 :=
    CFSG.Sporadic.J2.card_elemAbelian_le_four_of_normalized hE hEA hNn hNsq hEcent hEe hNA
  omega

end CFSG.RankThree.GF2n.Stroth80
