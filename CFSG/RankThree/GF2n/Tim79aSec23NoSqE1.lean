module

public import CFSG.RankThree.GF2n.Tim79aSec23MinGrp
public import CFSG.RankThree.GF2n.Tim79aSec23NoSq
public import CFSG.Timmesfeld.Transvection.Defs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.RankThree.GF2n.Tim78

section Abstract

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def NoCommonNbr (D : Set Y) (d : Y) : Prop :=
  ∀ e ∈ D, ¬ Commute d e → ∀ w ∈ D, Commute w d → Commute w e → False

theorem noCommonNbr_of_mem {D : Set Y} (hD : ∃ d₀ : Y, D = {g | IsConj d₀ g}) {v : Y}
    (hv : v ∈ D) (h : NoCommonNbr D v) : ∀ d ∈ D, NoCommonNbr D d := by
  obtain ⟨d₀, rfl⟩ := hD
  intro d hd e he hde w hw hwd hwe
  have hvd : IsConj v d := (hv : IsConj d₀ v).symm.trans hd
  obtain ⟨c, hc⟩ := isConj_iff.mp hvd
  have hmem : ∀ x, x ∈ {g | IsConj d₀ g} → c⁻¹ * x * c ∈ {g | IsConj d₀ g} := fun x hx =>
    (hx : IsConj d₀ x).trans (isConj_iff.mpr ⟨c⁻¹, by group⟩)
  have hconj : ∀ x y : Y, Commute x y ↔ Commute (c⁻¹ * x * c) (c⁻¹ * y * c) := fun x y => by
    constructor
    · intro hxy
      show c⁻¹ * x * c * (c⁻¹ * y * c) = c⁻¹ * y * c * (c⁻¹ * x * c)
      simp only [mul_assoc, mul_inv_cancel_left]; rw [← mul_assoc x, hxy.eq, mul_assoc]
    · intro hxy
      have := hxy.eq
      have h2 : x * y = y * x := by
        have e1 : c * (c⁻¹ * x * c * (c⁻¹ * y * c)) * c⁻¹ = x * y := by group
        have e2 : c * (c⁻¹ * y * c * (c⁻¹ * x * c)) * c⁻¹ = y * x := by group
        rw [← e1, ← e2, this]
      exact h2
  have hcd : c⁻¹ * d * c = v := by rw [← hc]; group
  refine h _ (hmem e he) ?_ _ (hmem w hw) ?_ ?_
  · rw [← hcd]; exact fun hh => hde ((hconj d e).mpr hh)
  · rw [← hcd]; exact (hconj w d).mp hwd
  · exact (hconj w e).mp hwe

theorem commute_of_noCommonNbr {D : Set Y} (h : ∀ d ∈ D, NoCommonNbr D d) {d a b : Y}
    (ha : a ∈ D) (hb : b ∈ D) (hd : d ∈ D) (had : Commute a d) (hbd : Commute b d) :
    Commute a b := by
  by_contra hab
  exact h a ha b hb hab d hd had.symm hbd.symm

theorem mem_mul_center_of_noCommonNbr {D : Set Y} (h : ∀ d ∈ D, NoCommonNbr D d)
    (hinv : ∀ d ∈ D, orderOf d = 2) (hnc : ∀ d ∈ D, d ∉ Subgroup.center Y) (hE1 : NoSqE1 D)
    {d a : Y} (hd : d ∈ D) (ha : a ∈ D) (had : Commute a d) :
    QuotientGroup.mk' (Subgroup.center Y) a = QuotientGroup.mk' (Subgroup.center Y) d := by
  classical
  set C₀ : Subgroup Y := cenGen D d with hC₀
  have hgen : ∀ x ∈ D ∩ (Subgroup.centralizer ({d} : Set Y) : Set Y),
      ∀ y ∈ D ∩ (Subgroup.centralizer ({d} : Set Y) : Set Y), x * y = y * x := by
    rintro x ⟨hxD, hxC⟩ y ⟨hyD, hyC⟩
    exact (commute_of_noCommonNbr h hxD hyD hd
      (Subgroup.mem_centralizer_singleton_iff.mp hxC)
      (Subgroup.mem_centralizer_singleton_iff.mp hyC)).eq
  letI : CommGroup C₀ := Subgroup.closureCommGroupOfComm fun x hx y hy _ => hgen x hx y hy
  have hsq : ∀ x ∈ C₀, x * x = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x * x = 1) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨hxD, -⟩
      rw [← sq, ← hinv x hxD]; exact pow_orderOf_eq_one x
    · simp
    · intro x y hx' hy' hx hy
      have hxy : x * y = y * x := by
        have := mul_comm (⟨x, hx'⟩ : C₀) ⟨y, hy'⟩
        exact congrArg Subtype.val this
      calc x * y * (x * y) = (x * x) * (y * y) := by
            rw [mul_assoc, ← mul_assoc y, ← hxy]; group
        _ = 1 := by rw [hx, hy, one_mul]
    · intro x _ hx
      rw [← mul_inv_rev, hx, inv_one]
  have h2 : IsPGroup 2 C₀ := fun g => ⟨1, by
    rw [pow_one, sq]; exact Subtype.ext (hsq g g.2)⟩
  have hle : C₀ ≤ Subgroup.zpowers d ⊔ Subgroup.center Y :=
    (le_inSubgroup_pCore le_rfl Subgroup.le_normalizer h2).trans (hE1 d hd)
  have haC : a ∈ C₀ := Subgroup.subset_closure
    ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr had⟩
  obtain ⟨x, hx, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hle haC)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hdd : d ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← sq, ← hinv d hd]; exact pow_orderOf_eq_one d
  have hz1 : QuotientGroup.mk' (Subgroup.center Y) z = 1 := (QuotientGroup.eq_one_iff z).2 hz
  rw [map_mul, hz1, mul_one, map_zpow, zpow_eq_zpow_emod n (by rw [← map_zpow, hdd, map_one])]
  have hmod := Int.emod_two_eq_zero_or_one n
  rcases hmod with h0 | h1
  · exfalso
    apply hnc _ ha
    have : QuotientGroup.mk' (Subgroup.center Y) (d ^ n * z) = 1 := by
      rw [map_mul, hz1, mul_one, map_zpow, zpow_eq_zpow_emod n (by rw [← map_zpow, hdd, map_one]),
        h0, zpow_zero]
    exact (QuotientGroup.eq_one_iff _).1 this
  · rw [h1, zpow_one]

theorem isolated_mk_of_noCommonNbr {D : Set Y} (hD : ∃ d₀ : Y, D = {g | IsConj d₀ g})
    (hroot : CFSG.Timmesfeld.IsRootInvolutionSet D) (hdeg : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4)
    (hnc : ∀ d ∈ D, d ∉ Subgroup.center Y) (hE1 : NoSqE1 D) (h : ∀ d ∈ D, NoCommonNbr D d)
    {d : Y} (hd : d ∈ D) (g : Y ⧸ Subgroup.center Y) :
    (g * QuotientGroup.mk' _ d * g⁻¹) * QuotientGroup.mk' _ d =
        QuotientGroup.mk' _ d * (g * QuotientGroup.mk' _ d * g⁻¹) →
      g * QuotientGroup.mk' (Subgroup.center Y) d * g⁻¹ = QuotientGroup.mk' _ d := by
  intro hcomm
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) g
  set a := y * d * y⁻¹ with ha_def
  have haD : a ∈ D := by
    obtain ⟨d₀, rfl⟩ := hD
    exact (hd : IsConj d₀ d).trans (isConj_iff.mpr ⟨y, rfl⟩)
  have hπa : π y * π d * (π y)⁻¹ = π a := by simp [ha_def, hπ]
  rw [hπa] at hcomm ⊢
  have hinv : ∀ x ∈ D, x * x = 1 := fun x hx => by
    rw [← sq, ← hroot.1 x hx]; exact pow_orderOf_eq_one x
  rcases hroot.2.1 a haD d hd with h2 | h4 | hodd
  ·
    have hc : Commute a d := by
      have h1 : (a * d) * (a * d) = 1 := by rw [← sq, ← h2]; exact pow_orderOf_eq_one _
      show a * d = d * a
      calc a * d = (a * d)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
        _ = d⁻¹ * a⁻¹ := mul_inv_rev a d
        _ = d * a := by rw [inv_eq_of_mul_eq_one_right (hinv d hd),
            inv_eq_of_mul_eq_one_right (hinv a haD)]
    exact mem_mul_center_of_noCommonNbr h (fun x hx => hroot.1 x hx) hnc hE1 hd haD hc
  · exact absurd h4 (hdeg a haD d hd)
  ·
    obtain ⟨k, hk⟩ := hodd
    have hsq : π ((a * d) ^ 2) = 1 := by
      have : π a * π d = π d * π a := hcomm
      have hπd : π d * π d = 1 := by rw [← map_mul, hinv d hd, map_one]
      have hπa' : π a * π a = 1 := by rw [← map_mul, hinv a haD, map_one]
      rw [sq, map_mul, map_mul]
      calc π a * π d * (π a * π d) = π a * (π d * π a) * π d := by group
        _ = π a * (π a * π d) * π d := by rw [this]
        _ = (π a * π a) * (π d * π d) := by group
        _ = 1 := by rw [hπd, hπa', one_mul]
    have hone : π (a * d) = 1 := by
      have hpow : (a * d) ^ (2 * (k + 1)) = a * d := by
        calc (a * d) ^ (2 * (k + 1)) = (a * d) ^ (orderOf (a * d) + 1) := by rw [hk]; ring_nf
          _ = a * d := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
      rw [← hpow, pow_mul, map_pow, hsq, one_pow]
    have hπd : π d * π d = 1 := by rw [← map_mul, hinv d hd, map_one]
    calc π a = π a * (π d * π d) := by rw [hπd, mul_one]
      _ = π (a * d) * π d := by rw [show π (a * d) = π a * π d from map_mul π a d, mul_assoc]
      _ = π d := by rw [hone, one_mul]

theorem false_of_isolated_mk
    (hsolv : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y)
    {d : Y} (hd2 : d * d = 1) (hdZ : d ∉ Subgroup.center Y)
    (hiso : ∀ g : Y ⧸ Subgroup.center Y,
      (g * QuotientGroup.mk' _ d * g⁻¹) * QuotientGroup.mk' _ d =
          QuotientGroup.mk' _ d * (g * QuotientGroup.mk' _ d * g⁻¹) →
        g * QuotientGroup.mk' (Subgroup.center Y) d * g⁻¹ = QuotientGroup.mk' _ d) :
    False := by
  classical
  haveI : Fintype (Y ⧸ Subgroup.center Y) := Fintype.ofFinite _
  set t := QuotientGroup.mk' (Subgroup.center Y) d with ht
  have ht1 : t ≠ 1 := fun h => hdZ ((QuotientGroup.eq_one_iff d).1 h)
  have ht2 : t * t = 1 := by rw [ht, ← map_mul, hd2, map_one]
  obtain ⟨N, hN, hodd, hNt⟩ := CFSG.ZStar.glauberman_zStar _ t ht1 ht2 hiso
  haveI := hN
  have hsolvN : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hbot : N = ⊥ := CFSG.Timmesfeld.solvable_normal_eq_bot_quotient_center hsolv N hsolvN
  have htc : t ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := hNt g
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : g * t * g⁻¹ = t := by
      calc g * t * g⁻¹ = g * t * g⁻¹ * t⁻¹ * t := by group
        _ = t := by rw [h1, one_mul]
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h2]
  have hZs : Group.IsSolvable (Subgroup.center (Y ⧸ Subgroup.center Y)) :=
    isSolvable_of_comm fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp a.2 b).symm)
  have hZ := CFSG.Timmesfeld.solvable_normal_eq_bot_quotient_center hsolv _ hZs
  rw [hZ, Subgroup.mem_bot] at htc
  exact ht1 htc

theorem false_of_noSqE1_of_noCommonNbr {D : Set Y} (hD : ∃ d₀ : Y, D = {g | IsConj d₀ g})
    (hroot : CFSG.Timmesfeld.IsRootInvolutionSet D) (hdeg : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4)
    (hnc : ∀ d ∈ D, d ∉ Subgroup.center Y)
    (hsolv : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y)
    (hE1 : NoSqE1 D) {v : Y} (hv : v ∈ D) (h : NoCommonNbr D v) : False := by
  have hall := noCommonNbr_of_mem hD hv h
  have hv2 : v * v = 1 := by rw [← sq, ← hroot.1 v hv]; exact pow_orderOf_eq_one v
  exact false_of_isolated_mk hsolv hv2 (hnc v hv)
    (isolated_mk_of_noCommonNbr hD hroot hdeg hnc hE1 hall hv)

end Abstract

@[expose] def OddTranspNoSqE1Dich : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (D : Set Y),
    (∃ d₀ : Y, D = {g | IsConj d₀ g}) → CFSG.Timmesfeld.IsRootInvolutionSet D →
    (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4) → Subgroup.closure D = ⊤ →
    (∀ d ∈ D, d ∉ Subgroup.center Y) →
    (∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N ≤ Subgroup.center Y) →
    (∀ (N : Subgroup Y) [N.Characteristic], ¬ N ≤ Subgroup.center Y → IsPGroup 2 (Y ⧸ N)) →
    (¬ ∃ u ∈ QuotientGroup.mk' (Subgroup.center Y) '' D,
        ∃ v ∈ QuotientGroup.mk' (Subgroup.center Y) '' D,
          u ≠ v ∧ Commute u v ∧ u * v ∈ QuotientGroup.mk' (Subgroup.center Y) '' D) →
    NoSqE1 D ∨
      CFSG.Timmesfeld.Transvection.TransvectionHyp (Y ⧸ Subgroup.center Y)
        {A | ∃ d ∈ D, A = Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center Y) d)}

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem noCommonNbr_of_noSqE1 (hd : Sec23Data V H) (h2 : Nat.card (barOf V H V) = 2)
    (hdeg : ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4)
    (hns : ¬ ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H)
    (hE1 : NoSqE1 (Dy V H)) : ∃ v ∈ Dy V H, NoCommonNbr (Dy V H) v := by
  classical
  obtain ⟨⟨v, hvV⟩, hv1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.barOf_V_ne_bot
  have hv1 : v ≠ 1 := fun h => hv1' (Subtype.ext h)
  have hvX : v ∈ barOf V H (xOf V H) := barOf_V_le V H hvV
  set v' : Xbar V H := ⟨v, hvX⟩ with hv'_def
  have hv'D : v' ∈ Dy V H := hc.barOf_V_subset_dbarOf hvV hv1
  have hv'2 : v' * v' = 1 := by
    rw [← sq]
    have := hd.root.1 v' hv'D
    rw [← this]; exact pow_orderOf_eq_one v'
  have hv2 : v * v = 1 := by
    have := congrArg Subtype.val hv'2
    simpa using this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hov : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  have hVv : barOf V H V = Subgroup.zpowers v := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hvV) ?_).symm
    rw [Nat.card_zpowers, h2, hov]
  have hPv : ∀ p ∈ barOf V H P, p * v = v * p := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_barOf_iff.mp hp
    obtain ⟨u, hu, rfl⟩ := mem_barOf_iff.mp hvV
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc.commute_of_mem_P hq hu).symm
  have hnormP : ∀ c : Xbar V H, c * v' = v' * c → ∀ p ∈ barOf V H P,
      (c : Hbar V H) * p * (c : Hbar V H)⁻¹ ∈ barOf V H P := by
    intro c hcv p hp
    have hcom : Commute (c : Hbar V H) v := by
      show (c : Hbar V H) * v = v * (c : Hbar V H)
      have := congrArg Subtype.val hcv
      simpa [hv'_def] using this
    have hcN : (c : Hbar V H) ∈
        Subgroup.normalizer ((barOf V H V : Subgroup (Hbar V H)) : Set (Hbar V H)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [hVv]
      have key : ∀ n : ℤ, (c : Hbar V H) * v ^ n * (c : Hbar V H)⁻¹ = v ^ n := fun n => by
        rw [(hcom.zpow_right n).eq]; group
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n, (key n).symm⟩
      · rintro ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have : x = (c : Hbar V H)⁻¹ * (c * x * (c : Hbar V H)⁻¹) * c := by group
        rw [this, ← hn]
        rw [mul_assoc, ← mul_assoc _ (v ^ n) _]
        have h1 : (c : Hbar V H)⁻¹ * v ^ n = v ^ n * (c : Hbar V H)⁻¹ := by
          have := (hcom.inv_left.zpow_right n).eq
          exact this
        rw [h1]; group
    rw [hc.normalizer_barOf_V] at hcN
    obtain ⟨m, hm, hmc⟩ := mem_barOf_iff.mp hcN
    obtain ⟨q, hq, rfl⟩ := mem_barOf_iff.mp hp
    have hmM : (m : G) ∈ M := hc.normalizer_eq ▸ hm
    have hmP := (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hmM) (q : G)).mp hq
    refine mem_barOf_iff.mpr ⟨m * q * m⁻¹, by simpa using hmP, by simp [hmc]⟩
  set D : Set (Xbar V H) := Dy V H with hD
  set C₀ : Subgroup (Xbar V H) := cenGen D v' with hC₀
  set R : Subgroup (Xbar V H) :=
    C₀ ⊓ (barOf V H P).comap (barOf V H (xOf V H)).subtype with hR
  have hP2 : IsPGroup 2 (barOf V H P) := by
    have : IsPGroup 2 (P.subgroupOf H) :=
      hc.isPGroup_P.of_equiv (Subgroup.subgroupOfEquivOfLe hc.PleH).symm
    exact this.map (piBar V H)
  have hR2 : IsPGroup 2 R := hP2.comap_subtype.to_le inf_le_right
  have hDinv : ∀ c ∈ D, c * c = 1 := fun c hc' => by
    rw [← sq]
    have := hd.root.1 c hc'
    rw [← this]; exact pow_orderOf_eq_one c
  have hgenC : ∀ c ∈ D, c * v' = v' * c → c ∈ C₀ := fun c hcD hcv =>
    Subgroup.subset_closure ⟨hcD, Subgroup.mem_centralizer_singleton_iff.mpr hcv⟩
  have hRnorm : ∀ c ∈ C₀, ∀ r ∈ R, c * r * c⁻¹ ∈ R ∧ c⁻¹ * r * c ∈ R := by
    intro c hc0
    refine Subgroup.closure_induction (p := fun c _ => ∀ r ∈ R, c * r * c⁻¹ ∈ R ∧ c⁻¹ * r * c ∈ R)
      ?_ ?_ ?_ ?_ hc0
    · rintro c ⟨hcD, hcC⟩ r hr
      have hcv : c * v' = v' * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
      have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hDinv c hcD)
      have hcC₀ : c ∈ C₀ := Subgroup.subset_closure ⟨hcD, hcC⟩
      have h1 : c * r * c⁻¹ ∈ R := by
        refine ⟨C₀.mul_mem (C₀.mul_mem hcC₀ hr.1) (C₀.inv_mem hcC₀), ?_⟩
        show ((c * r * c⁻¹ : Xbar V H) : Hbar V H) ∈ barOf V H P
        simpa using hnormP c hcv r hr.2
      refine ⟨h1, ?_⟩
      rw [hcinv] at h1 ⊢
      exact h1
    · intro r hr; simpa using hr
    · intro x y hx hy hx' hy' r hr
      refine ⟨?_, ?_⟩
      · have := (hx' _ (hy' r hr).1).1
        simpa [mul_assoc] using this
      · have := (hy' _ (hx' r hr).2).2
        simpa [mul_assoc] using this
    · intro x hx hx' r hr
      exact ⟨by simpa using (hx' r hr).2, by simpa using (hx' r hr).1⟩
  have hCN : C₀ ≤ Subgroup.normalizer (R : Set (Xbar V H)) := fun c hc0 =>
    Subgroup.mem_normalizer_iff.mpr fun x =>
      ⟨fun hx => (hRnorm c hc0 x hx).1, fun hx => by
        have := (hRnorm c hc0 _ hx).2
        simpa [mul_assoc] using this⟩
  have hRz : R ≤ Subgroup.zpowers v' ⊔ Subgroup.center (Xbar V H) :=
    (le_inSubgroup_pCore inf_le_left hCN hR2).trans (hE1 v' hv'D)
  set Zc : Subgroup (Hbar V H) :=
    (Subgroup.center (Xbar V H)).map (barOf V H (xOf V H)).subtype with hZc
  have hZn : ∀ (h : Hbar V H), ∀ z ∈ Zc, h * z * h⁻¹ ∈ Zc := by
    rintro h z ⟨z₀, hz₀, rfl⟩
    have hyX : h * (z₀ : Hbar V H) * h⁻¹ ∈ barOf V H (xOf V H) :=
      (normal_barOf_xOf V H).conj_mem _ z₀.2 h
    refine ⟨⟨_, hyX⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro g
    have hg : h⁻¹ * (g : Hbar V H) * h ∈ barOf V H (xOf V H) := by
      simpa using (normal_barOf_xOf V H).conj_mem _ g.2 h⁻¹
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₀ ⟨_, hg⟩)
    apply Subtype.ext
    simp only [Subgroup.coe_mul] at h2 ⊢
    calc (g : Hbar V H) * (h * z₀ * h⁻¹) = h * ((h⁻¹ * g * h) * z₀) * h⁻¹ := by group
      _ = h * (z₀ * (h⁻¹ * g * h)) * h⁻¹ := by rw [h2]
      _ = h * z₀ * h⁻¹ * g := by group
  have stepC : ∀ w ∈ D, w * v' = v' * w → ∀ p ∈ barOf V H P,
      (w : Hbar V H) * p * (w : Hbar V H)⁻¹ * p⁻¹ ∈ Zc := by
    intro w hwD hwv p hp
    have hw2 := hDinv w hwD
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hwH : (w : Hbar V H)⁻¹ = w := by
      have := congrArg Subtype.val hwinv
      simpa using this
    have hfX : p * (w : Hbar V H) * p⁻¹ ∈ barOf V H (xOf V H) :=
      (normal_barOf_xOf V H).conj_mem _ w.2 p
    set f : Xbar V H := ⟨_, hfX⟩ with hf_def
    have hfD : f ∈ D := hc.conj_mem_dbarOf (y := p) hwD
    have hpv : Commute p v := hPv p hp
    have hwv' : Commute (w : Hbar V H) v := by
      show (w : Hbar V H) * v = v * (w : Hbar V H)
      have := congrArg Subtype.val hwv
      simpa [hv'_def] using this
    have hfv : f * v' = v' * f := by
      apply Subtype.ext
      show (p * (w : Hbar V H) * p⁻¹) * v = v * (p * (w : Hbar V H) * p⁻¹)
      have h1 : p⁻¹ * v = v * p⁻¹ := hpv.inv_left.eq
      calc p * (w : Hbar V H) * p⁻¹ * v = p * ((w : Hbar V H) * (p⁻¹ * v)) := by group
        _ = p * ((w : Hbar V H) * (v * p⁻¹)) := by rw [h1]
        _ = p * (((w : Hbar V H) * v) * p⁻¹) := by group
        _ = p * ((v * (w : Hbar V H)) * p⁻¹) := by rw [hwv'.eq]
        _ = (p * v) * ((w : Hbar V H) * p⁻¹) := by group
        _ = (v * p) * ((w : Hbar V H) * p⁻¹) := by rw [hpv.eq]
        _ = v * (p * (w : Hbar V H) * p⁻¹) := by group
    have hεC : w * f ∈ C₀ := C₀.mul_mem (hgenC w hwD hwv) (hgenC f hfD hfv)
    have hεeq : ((w * f : Xbar V H) : Hbar V H) =
        (w : Hbar V H) * p * (w : Hbar V H)⁻¹ * p⁻¹ := by
      rw [hwH]; simp [hf_def]; group
    have hεP : ((w * f : Xbar V H) : Hbar V H) ∈ barOf V H P := by
      rw [hεeq]
      exact (barOf V H P).mul_mem (hnormP w hwv p hp) ((barOf V H P).inv_mem hp)
    obtain ⟨a, ha, z, hz, haz⟩ := Subgroup.mem_sup_of_normal_right.mp (hRz ⟨hεC, hεP⟩)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hv'z : v' ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hv'2
    have hmod : v' ^ n = v' ^ (n % 2) := zpow_eq_zpow_emod n hv'z
    rcases Int.emod_two_eq_zero_or_one n with hn | hn
    ·
      rw [hmod, hn, zpow_zero, one_mul] at haz
      rw [← hεeq, ← haz]
      exact ⟨z, hz, rfl⟩
    · rw [hmod, hn, zpow_one] at haz
      by_cases hπ : QuotientGroup.mk' (Subgroup.center (Xbar V H)) w =
          QuotientGroup.mk' (Subgroup.center (Xbar V H)) v'
      ·
        have hz' : w⁻¹ * v' ∈ Subgroup.center (Xbar V H) := QuotientGroup.eq.mp hπ
        have hz₂ : v'⁻¹ * w ∈ Subgroup.center (Xbar V H) := by
          simpa using (Subgroup.center (Xbar V H)).inv_mem hz'
        set ζ : Hbar V H := ((v'⁻¹ * w : Xbar V H) : Hbar V H) with hζ
        have hζZ : ζ ∈ Zc := ⟨_, hz₂, rfl⟩
        have hwζ : (w : Hbar V H) = v * ζ := by
          have : w = v' * (v'⁻¹ * w) := by group
          have := congrArg Subtype.val this
          simpa [hv'_def, hζ] using this
        have hζv : ζ * v = v * ζ := by
          have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₂ v')
          simpa [hv'_def, hζ] using this.symm
        have hE : (w : Hbar V H) * p * (w : Hbar V H)⁻¹ * p⁻¹ = ζ * (p * ζ * p⁻¹) := by
          rw [hwH, hwζ]
          calc v * ζ * p * (v * ζ) * p⁻¹ = (v * ζ) * (p * v) * ζ * p⁻¹ := by group
            _ = (v * ζ) * (v * p) * ζ * p⁻¹ := by rw [hpv.eq]
            _ = v * (ζ * v) * p * ζ * p⁻¹ := by group
            _ = v * (v * ζ) * p * ζ * p⁻¹ := by rw [hζv]
            _ = (v * v) * ζ * (p * ζ * p⁻¹) := by group
            _ = ζ * (p * ζ * p⁻¹) := by rw [hv2, one_mul]
        rw [hE]
        exact Zc.mul_mem hζZ (hZn p ζ hζZ)
      ·
        exfalso
        apply hns
        have hfeq : f = w * v' * z := by
          calc f = w⁻¹ * (w * f) := by group
            _ = w⁻¹ * (v' * z) := by rw [← haz]
            _ = w * v' * z := by rw [hwinv, mul_assoc]
        refine ⟨QuotientGroup.mk' _ w, ⟨w, hwD, rfl⟩, QuotientGroup.mk' _ v',
          ⟨v', hv'D, rfl⟩, hπ, ?_, f, hfD, ?_⟩
        · exact (show Commute w v' from hwv).map (QuotientGroup.mk' _)
        · have hz1 : (QuotientGroup.mk' (Subgroup.center (Xbar V H))) z = 1 :=
            (QuotientGroup.eq_one_iff z).mpr hz
          rw [hfeq, map_mul, map_mul, hz1, mul_one]
  refine ⟨v', hv'D, fun e heD hne w hwD hwv hwe => ?_⟩
  obtain ⟨e', -, he'⟩ := mem_barOf_iff.mp e.2
  have he'D : piBar V H e' ∈ dbarOf V H := he' ▸ heD
  have hHsup : P ⊔ Subgroup.closure {(e' : G)} = H :=
    hc.sup_eq_H_of_noncommute hdeg he'D hvV
      (fun h => hne (Subtype.ext (by simpa [he', hv'_def] using h)))
  have hwv' : w * v' = v' * w := hwv
  have hwe' : (w : Hbar V H) * piBar V H e' = piBar V H e' * w := by
    have := congrArg Subtype.val (show w * e = e * w from hwe)
    simpa [he'] using this
  let S : Subgroup ↥H :=
    { carrier := {h | ⁅(w : Hbar V H), piBar V H h⁆ ∈ Zc}
      mul_mem' := fun {a b} ha hb => by
        show ⁅(w : Hbar V H), piBar V H (a * b)⁆ ∈ Zc
        have hid : ⁅(w : Hbar V H), piBar V H (a * b)⁆ =
            ⁅(w : Hbar V H), piBar V H a⁆ *
              (piBar V H a * ⁅(w : Hbar V H), piBar V H b⁆ * (piBar V H a)⁻¹) := by
          rw [map_mul]; simp only [commutatorElement_def]; group
        rw [hid]
        exact Zc.mul_mem ha (hZn _ _ hb)
      one_mem' := by
        show ⁅(w : Hbar V H), piBar V H 1⁆ ∈ Zc
        simp
      inv_mem' := fun {a} ha => by
        show ⁅(w : Hbar V H), piBar V H a⁻¹⁆ ∈ Zc
        have hid : ⁅(w : Hbar V H), piBar V H a⁻¹⁆ =
            (piBar V H a)⁻¹ * ⁅(w : Hbar V H), piBar V H a⁆⁻¹ * piBar V H a := by
          rw [map_inv]; simp only [commutatorElement_def]; group
        rw [hid]
        simpa using hZn (piBar V H a)⁻¹ _ (Zc.inv_mem ha) }
  have hSH' : P ⊔ Subgroup.closure {(e' : G)} ≤ S.map H.subtype := by
    refine sup_le (fun q hq => ?_) ((Subgroup.closure_le _).2 fun x hx => ?_)
    · refine ⟨⟨q, hc.PleH hq⟩, ?_, rfl⟩
      show ⁅(w : Hbar V H), piBar V H ⟨q, hc.PleH hq⟩⁆ ∈ Zc
      have := stepC w hwD hwv' (piBar V H ⟨q, hc.PleH hq⟩)
        (mem_barOf_iff.mpr ⟨⟨q, hc.PleH hq⟩, hq, rfl⟩)
      simpa only [commutatorElement_def] using this
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨e', ?_, rfl⟩
      show ⁅(w : Hbar V H), piBar V H e'⁆ ∈ Zc
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hwe']
      exact Zc.one_mem
  have hSH : H ≤ S.map H.subtype := by rwa [hHsup] at hSH'
  have hSall : ∀ h : ↥H, ⁅(w : Hbar V H), piBar V H h⁆ ∈ Zc := fun h => by
    obtain ⟨h₀, hh₀, hh₀h⟩ := hSH h.2
    have : h₀ = h := Subtype.ext hh₀h
    rw [← this]; exact hh₀
  have hwY : ∀ y : Xbar V H, ⁅w, y⁆ ∈ Subgroup.center (Xbar V H) := by
    intro y
    obtain ⟨h, -, hhy⟩ := mem_barOf_iff.mp y.2
    obtain ⟨z₀, hz₀, hz₀e⟩ := hSall h
    rw [hhy] at hz₀e
    have : ⁅w, y⁆ = z₀ := Subtype.ext (by simpa [commutatorElement_def] using hz₀e.symm)
    rw [this]; exact hz₀
  have hwc : QuotientGroup.mk' (Subgroup.center (Xbar V H)) w ∈
      Subgroup.center (Xbar V H ⧸ Subgroup.center (Xbar V H)) := by
    rw [Subgroup.mem_center_iff]
    intro yt
    refine QuotientGroup.induction_on yt (fun y => ?_)
    show (y : Xbar V H ⧸ Subgroup.center (Xbar V H)) * (w : _) = (w : _) * (y : _)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hDinv w hwD)
    have := hwY y⁻¹
    simpa [commutatorElement_def, hwinv, mul_assoc] using this
  have hbot := hc.tilde_noSolvable hd (Subgroup.center (Xbar V H ⧸ Subgroup.center (Xbar V H)))
    inferInstance inferInstance
  rw [hbot, Subgroup.mem_bot] at hwc
  exact hd.noncentral w hwD ((QuotientGroup.eq_one_iff w).mp hwc)

theorem false_of_noSqE1 (hd : Sec23Data V H) (h2 : Nat.card (barOf V H V) = 2)
    (hdeg : ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4)
    (hns : ¬ ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H)
    (hE1 : NoSqE1 (Dy V H)) : False := by
  obtain ⟨v, hv, hN⟩ := hc.noCommonNbr_of_noSqE1 hd h2 hdeg hns hE1
  exact false_of_noSqE1_of_noCommonNbr hd.isClass hd.root hdeg hd.noncentral hd.solv hE1 hv hN

theorem isPGroup_quotient_of_characteristic (hd : Sec23Data V H)
    (N : Subgroup (Xbar V H)) [N.Characteristic] (hN : ¬ N ≤ Subgroup.center (Xbar V H)) :
    IsPGroup 2 (Xbar V H ⧸ N) := by
  classical
  haveI hXn : (barOf V H (xOf V H)).Normal := normal_barOf_xOf V H
  set Xs := barOf V H (xOf V H) with hXs
  set Nb : Subgroup (Hbar V H) := N.map Xs.subtype with hNb
  haveI hNbn : Nb.Normal := normal_map_subtype_of_characteristic N
  set N₀ : Subgroup G := preimOf V H Nb with hN₀
  have hN₀H : N₀ ≤ H := preimOf_le_H V H Nb
  have hKH : N₀ ⊔ P ≤ H := sup_le hN₀H hc.PleH
  have hP2 : IsPGroup 2 (barOf V H P) := by
    have : IsPGroup 2 (P.subgroupOf H) :=
      hc.isPGroup_P.of_equiv (Subgroup.subgroupOfEquivOfLe hc.PleH).symm
    exact this.map (piBar V H)
  have hlift : ∀ n ∈ N, ∃ n₀ : ↥H, (n₀ : G) ∈ N₀ ∧ piBar V H n₀ = (n : Hbar V H) := by
    intro n hn
    obtain ⟨n₀, hn₀⟩ := piBar_surjective V H (n : Hbar V H)
    exact ⟨n₀, mem_preimOf.mpr ⟨n₀, rfl, hn₀ ▸ ⟨n, hn, rfl⟩⟩, hn₀⟩
  by_cases hK : N₀ ⊔ P = H
  ·
    have hall : ∀ y : Hbar V H, y ∈ barOf V H P ⊔ Nb := by
      have hle : H ≤ preimOf V H (barOf V H P ⊔ Nb) := by
        refine (le_of_eq hK.symm).trans (sup_le ?_ ?_)
        · intro g hg
          obtain ⟨h, rfl, hS⟩ := mem_preimOf.mp hg
          exact mem_preimOf.mpr ⟨h, rfl, Subgroup.mem_sup_right hS⟩
        · intro p hp
          exact mem_preimOf.mpr ⟨⟨p, hc.PleH hp⟩, rfl,
            Subgroup.mem_sup_left (mem_barOf_iff.mpr ⟨⟨p, hc.PleH hp⟩, hp, rfl⟩)⟩
      intro y
      obtain ⟨x, rfl⟩ := piBar_surjective V H y
      obtain ⟨x', hx', hxS⟩ := mem_preimOf.mp (hle x.2)
      have : x' = x := Subtype.ext hx'
      rw [← this]; exact hxS
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨p, hp, n, hn, hpn⟩ := Subgroup.mem_sup_of_normal_right.mp (hall (x : Hbar V H))
    obtain ⟨n', hn', rfl⟩ := Subgroup.mem_map.mp hn
    have hpX : p ∈ Xs := by
      have : p = (x : Hbar V H) * (n' : Hbar V H)⁻¹ := by
        rw [← hpn]; simp
      rw [this]; exact Xs.mul_mem x.2 (Xs.inv_mem n'.2)
    obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
    refine ⟨k, ?_⟩
    have hxe : x = ⟨p, hpX⟩ * n' := Subtype.ext (by simpa using hpn.symm)
    have hpk : (⟨p, hpX⟩ : Xbar V H) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [hxe, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n').2 hn', mul_one,
      ← QuotientGroup.mk_pow, hpk, QuotientGroup.mk_one]
  · exfalso
    apply hN
    have hlt : N₀ ⊔ P < H := lt_of_le_of_ne hKH hK
    have hVO : V ≤ inSubgroup (pCore 2) (N₀ ⊔ P) :=
      hc.min _ le_sup_right (hc.pCore_ne_bot_of_le le_sup_right hKH) hlt
    obtain ⟨hO2, hOK, hOn⟩ := inSubgroup_pCore_two (N₀ ⊔ P)
    set O := inSubgroup (pCore 2) (N₀ ⊔ P) with hO
    set T : Subgroup G := O ⊓ N₀ with hT
    have hTH : T ≤ H := inf_le_right.trans hN₀H
    have hT2 : IsPGroup 2 T := hO2.to_le inf_le_left
    have hN₀n : ∀ h ∈ H, ∀ n₀ ∈ N₀, h * n₀ * h⁻¹ ∈ N₀ := fun h hh n₀ hn₀ =>
      (Subgroup.mem_normalizer_iff.mp (normalizer_preimOf hh) n₀).mp hn₀
    have hcomT : ∀ u ∈ V, ∀ n₀ ∈ N₀, u * n₀ * u⁻¹ * n₀⁻¹ ∈ T := by
      intro u hu n₀ hn₀
      refine ⟨?_, N₀.mul_mem (hN₀n u (hc.V_le_H hu) n₀ hn₀) (N₀.inv_mem hn₀)⟩
      have h1 : n₀ * u⁻¹ * n₀⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hOn (Subgroup.mem_sup_left hn₀)) _).mp (O.inv_mem (hVO hu))
      have := O.mul_mem (hVO hu) h1
      simpa [mul_assoc] using this
    have hTn : ∀ n₀ ∈ N₀, ∀ t ∈ T, n₀ * t * n₀⁻¹ ∈ T := fun n₀ hn₀ t ht =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hOn (Subgroup.mem_sup_left hn₀)) t).mp ht.1,
        N₀.mul_mem (N₀.mul_mem hn₀ ht.2) (N₀.inv_mem hn₀)⟩
    set Tb : Subgroup (Xbar V H) := (barOf V H T).comap Xs.subtype with hTb
    have hTb2 : IsPGroup 2 Tb := by
      have : IsPGroup 2 (barOf V H T) := by
        have : IsPGroup 2 (T.subgroupOf H) :=
          hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
        exact this.map (piBar V H)
      exact this.comap_subtype
    have hTbN : Tb ≤ N := by
      intro t ht
      have h1 : (t : Hbar V H) ∈ Nb := by
        rw [← barOf_preimOf V H Nb]; exact barOf_mono inf_le_right ht
      obtain ⟨n', hn', hn'e⟩ := Subgroup.mem_map.mp h1
      have : n' = t := Subtype.ext hn'e
      rw [← this]; exact hn'
    have hkey : ∀ n ∈ N, ∀ t ∈ Tb, n * t * n⁻¹ ∈ Tb := by
      intro n hn t ht
      obtain ⟨n₀, hn₀N, hn₀⟩ := hlift n hn
      obtain ⟨t₀, ht₀T, ht₀⟩ := mem_barOf_iff.mp (Subgroup.mem_comap.mp ht)
      show ((n * t * n⁻¹ : Xbar V H) : Hbar V H) ∈ barOf V H T
      refine mem_barOf_iff.mpr ⟨n₀ * t₀ * n₀⁻¹, hTn _ hn₀N _ ht₀T, ?_⟩
      simp [hn₀, ht₀]
    have hNTb : N ≤ Subgroup.normalizer (Tb : Set (Xbar V H)) := fun n hn =>
      Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hkey n hn x hx, fun hx => by
        have := hkey n⁻¹ (N.inv_mem hn) _ hx
        simpa [mul_assoc] using this⟩
    have hTbO : Tb ≤ inSubgroup (pCore 2) N := le_inSubgroup_pCore hTbN hNTb hTb2
    haveI : N.Normal := inferInstance
    haveI hOn' : (inSubgroup (pCore 2) N).Normal :=
      normal_map_subtype_of_characteristic (pCore 2 ↥N)
    have hOsol : Group.IsSolvable (inSubgroup (pCore 2) N) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Group.IsNilpotent (inSubgroup (pCore 2) N) :=
        IsPGroup.isNilpotent (inSubgroup_pCore_two N).1
      infer_instance
    have hTbZ : Tb ≤ Subgroup.center (Xbar V H) := hTbO.trans (hd.solv _ hOn' hOsol)
    have hVN : ∀ u : ↥H, (u : G) ∈ V → ∀ n ∈ N,
        ∀ hu : piBar V H u ∈ Xs, (⟨piBar V H u, hu⟩ : Xbar V H) * n *
          (⟨piBar V H u, hu⟩ : Xbar V H)⁻¹ * n⁻¹ ∈ Subgroup.center (Xbar V H) := by
      intro u huV n hn hu
      apply hTbZ
      obtain ⟨n₀, hn₀N, hn₀⟩ := hlift n hn
      show _ ∈ barOf V H T
      refine mem_barOf_iff.mpr ⟨u * n₀ * u⁻¹ * n₀⁻¹, hcomT _ huV _ hn₀N, ?_⟩
      simp [hn₀]
    set Zc : Subgroup (Hbar V H) := (Subgroup.center (Xbar V H)).map Xs.subtype with hZc
    have hZn : ∀ (h : Hbar V H), ∀ z ∈ Zc, h * z * h⁻¹ ∈ Zc := by
      rintro h z ⟨z₀, hz₀, rfl⟩
      have hyX : h * (z₀ : Hbar V H) * h⁻¹ ∈ barOf V H (xOf V H) :=
        (normal_barOf_xOf V H).conj_mem _ z₀.2 h
      refine ⟨⟨_, hyX⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
      intro g
      have hg : h⁻¹ * (g : Hbar V H) * h ∈ barOf V H (xOf V H) := by
        simpa using (normal_barOf_xOf V H).conj_mem _ g.2 h⁻¹
      have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz₀ ⟨_, hg⟩)
      apply Subtype.ext
      simp only [Subgroup.coe_mul] at h2 ⊢
      calc (g : Hbar V H) * (h * z₀ * h⁻¹) = h * ((h⁻¹ * g * h) * z₀) * h⁻¹ := by group
        _ = h * (z₀ * (h⁻¹ * g * h)) * h⁻¹ := by rw [h2]
        _ = h * z₀ * h⁻¹ * g := by group
    have hDN : ∀ d ∈ Dy V H, ∀ n ∈ N, d * n * d⁻¹ * n⁻¹ ∈ Subgroup.center (Xbar V H) := by
      intro d hdD n hn
      obtain ⟨x, hxD, -, hxd⟩ := mem_dbarOf_iff.mp hdD
      obtain ⟨-, U, ⟨h, hh, rfl⟩, hxU⟩ := hxD
      have hu : h⁻¹ * (x : G) * h ∈ V := mem_conjSubgroup.mp hxU
      set hb : ↥H := ⟨h, hh⟩ with hhb
      set u : ↥H := hb⁻¹ * x * hb with hu_def
      have huV : (u : G) ∈ V := by simpa [hu_def, hhb] using hu
      have huX : piBar V H u ∈ Xs := barOf_V_le V H (mem_barOf_iff.mpr ⟨u, huV, rfl⟩)
      have hn'b : (piBar V H hb)⁻¹ * (n : Hbar V H) * (piBar V H hb)⁻¹⁻¹ ∈ Nb :=
        hNbn.conj_mem _ ⟨n, hn, rfl⟩ (piBar V H hb)⁻¹
      obtain ⟨n', hn', hn'e⟩ := Subgroup.mem_map.mp hn'b
      have hc' := hVN u huV n' hn' huX
      have hmem : ((d * n * d⁻¹ * n⁻¹ : Xbar V H) : Hbar V H) ∈ Zc := by
        have hz := hZn (piBar V H hb) _ ⟨_, hc', rfl⟩
        have hdx : (d : Hbar V H) = piBar V H hb * piBar V H u * (piBar V H hb)⁻¹ := by
          rw [← hxd, hu_def]; simp only [map_mul, map_inv]; group
        have hn'' : (n' : Hbar V H) = (piBar V H hb)⁻¹ * (n : Hbar V H) * piBar V H hb := by
          rw [← inv_inv (piBar V H hb)]; simpa using hn'e
        convert hz using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
        rw [hdx, hn'']
        group
      obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp hmem
      have : z = d * n * d⁻¹ * n⁻¹ := Subtype.ext hze
      rw [← this]; exact hz
    have hall : ∀ y : Xbar V H, ∀ n ∈ N, y * n * y⁻¹ * n⁻¹ ∈ Subgroup.center (Xbar V H) := by
      intro y
      have hy : y ∈ Subgroup.closure (Dy V H) := hd.gen ▸ Subgroup.mem_top y
      refine Subgroup.closure_induction
        (p := fun y _ => ∀ n ∈ N, y * n * y⁻¹ * n⁻¹ ∈ Subgroup.center (Xbar V H))
        ?_ ?_ ?_ ?_ hy
      · exact fun d hdD => hDN d hdD
      · intro n _; simp
      · intro a b _ _ ha hb n hn
        have e : a * b * n * (a * b)⁻¹ * n⁻¹ =
            a * (b * n * b⁻¹ * n⁻¹) * a⁻¹ * (a * n * a⁻¹ * n⁻¹) := by group
        rw [e]
        exact (Subgroup.center _).mul_mem
          ((inferInstance : (Subgroup.center (Xbar V H)).Normal).conj_mem _ (hb n hn) a) (ha n hn)
      · intro a _ ha n hn
        have hm : a⁻¹ * n * a⁻¹⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem _ hn a⁻¹
        have := (Subgroup.center _).inv_mem (ha _ (by simpa using hm))
        have e : (a * (a⁻¹ * n * a) * a⁻¹ * (a⁻¹ * n * a)⁻¹)⁻¹ = a⁻¹ * n * a⁻¹⁻¹ * n⁻¹ := by group
        rw [← e]; simpa using this
    intro n hn
    have hnc : QuotientGroup.mk' (Subgroup.center (Xbar V H)) n ∈
        Subgroup.center (Xbar V H ⧸ Subgroup.center (Xbar V H)) := by
      rw [Subgroup.mem_center_iff]
      intro yt
      refine QuotientGroup.induction_on yt (fun y => ?_)
      show (y : Xbar V H ⧸ Subgroup.center (Xbar V H)) * (n : _) = (n : _) * (y : _)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h1 := hall y⁻¹ n hn
      have h2 := (inferInstance : (Subgroup.center (Xbar V H)).Normal).conj_mem _ h1 n⁻¹
      have e : n⁻¹ * (y⁻¹ * n * y⁻¹⁻¹ * n⁻¹) * n⁻¹⁻¹ = (y * n)⁻¹ * (n * y) := by group
      rw [← e]; exact h2
    have hbot := hc.tilde_noSolvable hd (Subgroup.center (Xbar V H ⧸ Subgroup.center (Xbar V H)))
      inferInstance inferInstance
    rw [hbot, Subgroup.mem_bot] at hnc
    exact (QuotientGroup.eq_one_iff n).mp hnc

theorem transvectionHyp_of_noSquare' (h : OddTranspNoSqE1Dich) (hd : Sec23Data V H)
    (hdeg : ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4)
    (hns : ¬ ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H) :
    CFSG.Timmesfeld.Transvection.TransvectionHyp (Xbar V H ⧸ Subgroup.center (Xbar V H))
      {A | ∃ d ∈ Dy V H,
        A = Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center (Xbar V H)) d)} := by
  rcases h (Xbar V H) (Dy V H) hd.isClass hd.root hdeg hd.gen hd.noncentral hd.solv
    (fun N _ hN => hc.isPGroup_quotient_of_characteristic hd N hN) hns with hE1 | hT
  · exact (hc.false_of_noSqE1 hd (hc.card_barOf_V_eq_two_of_not_meetsSq hd hns) hdeg hns
      hE1).elim
  · exact hT

end MinCex

end CFSG.RankThree.GF2n.Tim79a
