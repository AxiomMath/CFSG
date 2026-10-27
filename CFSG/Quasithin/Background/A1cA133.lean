module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace A1c

section Prelim

variable {L : Type*} [Group L]

theorem mem_centerOf_iff {P : Subgroup L} {z : L} :
    z ∈ centerOf P ↔ z ∈ P ∧ ∀ y ∈ P, y * z = z * y := by
  constructor
  · rintro ⟨hz, hc⟩
    exact ⟨hz, fun y hy => Subgroup.mem_centralizer_iff.1 hc y hy⟩
  · rintro ⟨hz, hc⟩
    exact ⟨hz, Subgroup.mem_centralizer_iff.2 hc⟩

theorem centerOf_eq_map_center (P : Subgroup L) :
    centerOf P = (Subgroup.center ↥P).map P.subtype := by
  ext z
  rw [Subgroup.mem_map]
  constructor
  · intro hz
    rw [mem_centerOf_iff] at hz
    refine ⟨⟨z, hz.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hz.2 g g.2)
  · rintro ⟨z', hz', rfl⟩
    rw [mem_centerOf_iff]
    exact ⟨z'.2, fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' ⟨y, hy⟩)⟩

theorem card_centerOf {p : ℕ} [Fact p.Prime] {P : Subgroup L} (hP : CFSG.IsExtraspecial p ↥P) :
    Nat.card (centerOf P) = p := by
  have := hP
  rw [centerOf_eq_map_center, Subgroup.card_map_of_injective P.subtype_injective]
  exact CFSG.IsExtraspecial.center_order_p p ↥P

theorem commutator_mem_centerOf {p : ℕ} [Fact p.Prime] {P : Subgroup L}
    (hP : CFSG.IsExtraspecial p ↥P) {a b : L} (ha : a ∈ P) (hb : b ∈ P) :
    a * b * a⁻¹ * b⁻¹ ∈ centerOf P := by
  have := hP
  have := CFSG.IsExtraspecial.quotient_elementary_abelian p ↥P
  rw [centerOf_eq_map_center]
  refine ⟨⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹, ?_, rfl⟩
  show _ ∈ Subgroup.center ↥P
  rw [← QuotientGroup.eq_one_iff]
  have hcomm : ((⟨a, ha⟩ : ↥P) : ↥P ⧸ Subgroup.center ↥P) * ((⟨b, hb⟩ : ↥P) : ↥P ⧸ Subgroup.center ↥P) =
      ((⟨b, hb⟩ : ↥P) : ↥P ⧸ Subgroup.center ↥P) * ((⟨a, ha⟩ : ↥P) : ↥P ⧸ Subgroup.center ↥P) :=
    mul_comm' _ _
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hcomm]
  group

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} {a : G} (h : a ^ p = 1) :
    IsPGroup p (Subgroup.zpowers a) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem zpowers_eq_of_card_eq_prime [Finite L] {p : ℕ} {Z : Subgroup L} (hZ : Nat.card Z = p)
    {ζ : L} (hζ : ζ ∈ Z) (hζo : orderOf ζ = p) : Subgroup.zpowers ζ = Z := by
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hζ) ?_
  rw [Nat.card_zpowers, hζo, hZ]

theorem commutatorElement_mul_of_commute_right {x y z : L} (h : Commute z y) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h' : z * y * z⁻¹ = y := by rw [h.eq]; group
  rw [commutatorElement_def, commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h']

theorem commutatorElement_mul_of_commute_left {x y z : L} (h : Commute z x) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have h' : z * x⁻¹ * z⁻¹ = x⁻¹ := by
    have := h.inv_right
    rw [this.eq]; group
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹ * z⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h']

theorem commutatorElement_inv_inv_eq {a b : L} (ha : Commute ⁅a, b⁆ a) (hb : Commute ⁅a, b⁆ b) :
    ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  have e : a * b = ⁅a, b⁆ * (b * a) := by rw [commutatorElement_def]; group
  have h1 : ⁅a, b⁆ * a⁻¹ = a⁻¹ * ⁅a, b⁆ := ha.inv_right.eq
  have h2 : ⁅a, b⁆ * b⁻¹ = b⁻¹ * ⁅a, b⁆ := hb.inv_right.eq
  calc ⁅a⁻¹, b⁻¹⁆ = a⁻¹ * b⁻¹ * (a * b) := by rw [commutatorElement_def]; group
    _ = a⁻¹ * b⁻¹ * (⁅a, b⁆ * (b * a)) := by rw [← e]
    _ = a⁻¹ * (b⁻¹ * ⁅a, b⁆) * (b * a) := by group
    _ = a⁻¹ * (⁅a, b⁆ * b⁻¹) * (b * a) := by rw [h2]
    _ = (a⁻¹ * ⁅a, b⁆) * b⁻¹ * (b * a) := by group
    _ = (⁅a, b⁆ * a⁻¹) * b⁻¹ * (b * a) := by rw [h1]
    _ = ⁅a, b⁆ := by group

end Prelim

section A133

variable {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]

theorem two_lt_pRank_of_inverting_element (hp2 : p ≠ 2) {P : Subgroup L} [P.Normal]
    (hP : IsPOnePlusTwo p ↥P) {t : L} (ht : ∀ y ∈ P, t * y * t⁻¹ * y ∈ centerOf P) {x : L}
    (hx : x ∈ Subgroup.centralizer ({t} : Set L)) (hxp : orderOf x = p)
    (hxV : ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ centerOf P) :
    2 < pRank p (⊤ : Subgroup L) := by
  classical
  obtain ⟨hext, hPcard, hPexp⟩ := hP
  have := hext
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hxt : t * x = x * t := Subgroup.mem_centralizer_iff.1 hx t (Set.mem_singleton t)
  set Z : Subgroup L := centerOf P with hZdef
  have hZP : Z ≤ P := inf_le_left
  have hZc : ∀ z ∈ Z, ∀ y ∈ P, y * z = z * y := fun z hz y hy => (mem_centerOf_iff.1 hz).2 y hy
  have hZcard : Nat.card Z = p := card_centerOf hext
  have hPp : ∀ y ∈ P, y ^ p = 1 := fun y hy => by
    simpa using congrArg Subtype.val (hPexp ⟨y, hy⟩)
  have hcomm_mem : ∀ a ∈ P, ∀ b ∈ P, a * b * a⁻¹ * b⁻¹ ∈ Z := fun a ha b hb =>
    commutator_mem_centerOf hext ha hb
  have hZconj : ∀ (g z : L), z ∈ Z → g * z * g⁻¹ ∈ Z := by
    intro g z hz
    rw [mem_centerOf_iff] at hz ⊢
    refine ⟨Subgroup.Normal.conj_mem ‹P.Normal› z hz.1 g, fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ P := by
      have := Subgroup.Normal.conj_mem ‹P.Normal› y hy g⁻¹
      simpa using this
    calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hz.2 _ hy']
      _ = g * z * g⁻¹ * y := by group
  have hZnormalizer : ∀ g : L, g ∈ Subgroup.normalizer (Z : Set L) := by
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hZconj g z hz, fun hz => ?_⟩
    have := hZconj g⁻¹ _ hz
    have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rwa [e] at this
  have hxpow : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hxZ : ∀ z ∈ Z, x * z = z * x := by
    obtain ⟨ζ, hζZ, hζo, hζc⟩ := exists_orderOf_eq_of_isPGroup_normalizer
      (isPGroup_zpowers_of_pow_eq_one hxpow) (fun g _ => hZnormalizer g) (by rw [hZcard])
    have hZeq : Subgroup.zpowers ζ = Z := zpowers_eq_of_card_eq_prime hZcard hζZ hζo
    intro z hz
    rw [← hZeq] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hc : x * ζ = ζ * x := Subgroup.mem_centralizer_iff.1 hζc x (Subgroup.mem_zpowers x)
    exact (Commute.zpow_right hc k).eq
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hle : P ≤ Z := fun a ha => mem_centerOf_iff.2 ⟨ha, fun y hy => hcon y hy a ha⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hZcard, hPcard] at h1
    have h2 : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
    omega
  have haZ : a ∉ Z := fun h => hab (hZc a h b hb).symm
  have hcZ : a * b * a⁻¹ * b⁻¹ ∈ Z := hcomm_mem a ha b hb
  have hc1 : a * b * a⁻¹ * b⁻¹ ≠ 1 := fun h =>
    hab (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h))
  have hco : orderOf (a * b * a⁻¹ * b⁻¹) = p := orderOf_eq_prime (hPp _ (hZP hcZ)) hc1
  have hZeq : Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) = Z :=
    zpowers_eq_of_card_eq_prime hZcard hcZ hco
  have htc : t * (a * b * a⁻¹ * b⁻¹) * t⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    have hz1 := ht a ha
    have hz2 := ht b hb
    set z₁ := t * a * t⁻¹ * a with hz₁
    set z₂ := t * b * t⁻¹ * b with hz₂
    have ea : t * a * t⁻¹ = z₁ * a⁻¹ := by rw [hz₁]; group
    have eb : t * b * t⁻¹ = z₂ * b⁻¹ := by rw [hz₂]; group
    have haP : a⁻¹ ∈ P := P.inv_mem ha
    have hbP : b⁻¹ ∈ P := P.inv_mem hb
    have c1a : Commute z₁ a⁻¹ := (hZc z₁ hz1 a⁻¹ haP).symm
    have c1b : Commute z₁ b⁻¹ := (hZc z₁ hz1 b⁻¹ hbP).symm
    have c2a : Commute z₂ a⁻¹ := (hZc z₂ hz2 a⁻¹ haP).symm
    have c2b : Commute z₂ b⁻¹ := (hZc z₂ hz2 b⁻¹ hbP).symm
    have c12 : Commute z₁ z₂ := (hZc z₁ hz1 z₂ (hZP hz2)).symm
    have cca : Commute ⁅a, b⁆ a := (hZc _ hcZ a ha).symm
    have ccb : Commute ⁅a, b⁆ b := (hZc _ hcZ b hb).symm
    calc t * (a * b * a⁻¹ * b⁻¹) * t⁻¹
        = (t * a * t⁻¹) * (t * b * t⁻¹) * (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹)⁻¹ := by group
      _ = ⁅z₁ * a⁻¹, z₂ * b⁻¹⁆ := by rw [ea, eb, commutatorElement_def]
      _ = ⁅a⁻¹ * z₁, z₂ * b⁻¹⁆ := by rw [c1a.eq]
      _ = ⁅a⁻¹, z₂ * b⁻¹⁆ := commutatorElement_mul_of_commute_right (c12.mul_right c1b)
      _ = ⁅a⁻¹, b⁻¹ * z₂⁆ := by rw [c2b.eq]
      _ = ⁅a⁻¹, b⁻¹⁆ := commutatorElement_mul_of_commute_left c2a
      _ = ⁅a, b⁆ := commutatorElement_inv_inv_eq cca ccb
      _ = a * b * a⁻¹ * b⁻¹ := commutatorElement_def a b
  have htZ : ∀ z ∈ Z, t * z = z * t := by
    intro z hz
    rw [← hZeq] at hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have h1 : t * (a * b * a⁻¹ * b⁻¹) ^ k * t⁻¹ = (a * b * a⁻¹ * b⁻¹) ^ k := by
      rw [← conj_zpow, htc]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hZn : Z.Normal := ⟨fun z hz g => hZconj g z hz⟩
  set π : L →* L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hPg : IsPGroup p ↥P := CFSG.IsExtraspecial.isPGroup p ↥P
  have hPmapp : IsPGroup p (P.map π) := hPg.map π
  have hxbarP : IsPGroup p (Subgroup.zpowers (π x)) :=
    isPGroup_zpowers_of_pow_eq_one (by rw [← map_pow, hxpow, map_one])
  have hPmapn : (P.map π).Normal := Subgroup.Normal.map ‹P.Normal› π (QuotientGroup.mk'_surjective Z)
  have hnorm' : Subgroup.zpowers (π x) ≤ Subgroup.normalizer ((P.map π : Subgroup (L ⧸ Z)) : Set (L ⧸ Z)) := by
    intro g _
    rw [Subgroup.normalizer_eq_top_iff.2 hPmapn]
    exact Subgroup.mem_top g
  have hPmap_ne : P.map π ≠ ⊥ := by
    intro h
    have hmem : π a ∈ P.map π := Subgroup.mem_map_of_mem π ha
    rw [h, Subgroup.mem_bot] at hmem
    exact haZ ((QuotientGroup.eq_one_iff a).1 hmem)
  have hdvd : p ∣ Nat.card (P.map π) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hPmapp
    rw [hn]
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.1 (by simpa using hn)) hPmap_ne
    · exact dvd_pow_self p (Nat.succ_ne_zero n)
  obtain ⟨v, hvmem, hvo, hvc⟩ := exists_orderOf_eq_of_isPGroup_normalizer hxbarP hnorm' hdvd
  obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.1 hvmem
  have hyZ : y ∉ Z := by
    intro hyZ'
    have h1 : π y = 1 := (QuotientGroup.eq_one_iff y).2 hyZ'
    rw [h1, orderOf_one] at hvo
    exact hp1.ne hvo
  have hxy : π x * π y = π y * π x :=
    Subgroup.mem_centralizer_iff.1 hvc (π x) (Subgroup.mem_zpowers (π x))
  have hz'Z : x * y * x⁻¹ * y⁻¹ ∈ Z := by
    rw [← QuotientGroup.eq_one_iff]
    show π (x * y * x⁻¹ * y⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxy]
    group
  have hxy1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    set z' := x * y * x⁻¹ * y⁻¹ with hz'
    set z₁ := t * y * t⁻¹ * y with hz₁
    have hz₁Z : z₁ ∈ Z := ht y hyP
    have hyz' : x * y * x⁻¹ = z' * y := by rw [hz']; group
    have hty : t * y * t⁻¹ = z₁ * y⁻¹ := by rw [hz₁]; group
    have hyP' : y⁻¹ ∈ P := P.inv_mem hyP
    have hxt' : x * t = t * x := hxt.symm
    have hA : x * (t * y * t⁻¹) * x⁻¹ = z' * (z₁ * y⁻¹) := by
      calc x * (t * y * t⁻¹) * x⁻¹ = (x * t) * y * (x * t)⁻¹ := by group
        _ = (t * x) * y * (t * x)⁻¹ := by rw [hxt']
        _ = t * (x * y * x⁻¹) * t⁻¹ := by group
        _ = t * (z' * y) * t⁻¹ := by rw [hyz']
        _ = (t * z' * t⁻¹) * (t * y * t⁻¹) := by group
        _ = z' * (z₁ * y⁻¹) := by
          rw [hty, mul_inv_eq_iff_eq_mul.2 (htZ z' hz'Z)]
    have hB : x * (t * y * t⁻¹) * x⁻¹ = z₁ * (y⁻¹ * z'⁻¹) := by
      calc x * (t * y * t⁻¹) * x⁻¹ = x * (z₁ * y⁻¹) * x⁻¹ := by rw [hty]
        _ = (x * z₁ * x⁻¹) * (x * y * x⁻¹)⁻¹ := by group
        _ = z₁ * (y⁻¹ * z'⁻¹) := by
          rw [mul_inv_eq_iff_eq_mul.2 (hxZ z₁ hz₁Z), hyz', mul_inv_rev]
    have hz'c : Commute z' y⁻¹ := (hZc z' hz'Z y⁻¹ hyP').symm
    have hz₁c : Commute z₁ z' := (hZc z₁ hz₁Z z' (hZP hz'Z)).symm
    have h1 : z' * z₁ * y⁻¹ = z₁ * z'⁻¹ * y⁻¹ := by
      calc z' * z₁ * y⁻¹ = z' * (z₁ * y⁻¹) := by group
        _ = z₁ * (y⁻¹ * z'⁻¹) := by rw [← hA, ← hB]
        _ = z₁ * (z'⁻¹ * y⁻¹) := by rw [(hz'c.inv_left).eq]
        _ = z₁ * z'⁻¹ * y⁻¹ := by group
    have h2 : z' * z₁ = z₁ * z'⁻¹ := mul_right_cancel h1
    have h3 : z' = z'⁻¹ := by
      rw [← hz₁c.eq] at h2
      exact mul_left_cancel h2
    have hsq : z' * z' = 1 := mul_eq_one_iff_eq_inv.2 h3
    have h2d : orderOf z' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have hpd : orderOf z' ∣ p := orderOf_dvd_of_pow_eq_one (hPp z' (hZP hz'Z))
    have hg : orderOf z' ∣ Nat.gcd 2 p := Nat.dvd_gcd h2d hpd
    have hcop : Nat.gcd 2 p = 1 :=
      (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).2 (Ne.symm hp2)
    rw [hcop] at hg
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hg)
  have hxyc : x * y = y * x := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hxy1)
  have hyo : orderOf y = p := orderOf_eq_prime (hPp y hyP) (fun h => hyZ (h ▸ Z.one_mem))
  have hZel : IsElemAbelian p Z :=
    ⟨⟨⟨fun a b => Subtype.ext (hZc a a.2 b (hZP b.2)).symm⟩⟩, fun z hz => hPp z (hZP hz)⟩
  obtain ⟨hE1, hE1card⟩ := exists_elemAbelian_sup_zpowers hZel hyo
    (fun e he => (hZc e he y hyP).symm) hyZ
  have hE1P : Z ⊔ Subgroup.zpowers y ≤ P := sup_le hZP (Subgroup.zpowers_le.2 hyP)
  have hE1C : Z ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({x} : Set L) := by
    refine sup_le (fun z hz => ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact hxZ z hz
    · exact Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]; exact hxyc
  have hxP : x ∉ Z ⊔ Subgroup.zpowers y := by
    intro hxE
    obtain ⟨y', hy', hy'Z⟩ := hxV
    exact hy'Z (hcomm_mem x (hE1P hxE) y' hy')
  obtain ⟨hE2, hE2card⟩ := exists_elemAbelian_sup_zpowers hE1 hxp
    (fun e he => (Subgroup.mem_centralizer_iff.1 (hE1C he) x (Set.mem_singleton x)).symm) hxP
  have h3 := le_pRank (Fact.out : p.Prime) (le_top : (Z ⊔ Subgroup.zpowers y) ⊔ Subgroup.zpowers x ≤ ⊤)
    hE2 (k := 3) (by rw [hE2card, hE1card, hZcard]; ring)
  omega

end A133

end A1c

end CFSG.Quasithin
