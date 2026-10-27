module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGOTwoPrimeMap
import CFSG.LocalAnalysis.StandardType.GGHyperplaneMem
import CFSG.LocalAnalysis.StandardType.GGKGPosSUTableB
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.StandardType

theorem ggOTwoPrime_subgroupOf {G : Type} [Group G] {X Y : Subgroup G} (hY : Y ≤ X) :
    (ggOTwoPrime Y).subgroupOf X = ggOTwoPrime (Y.subgroupOf X) := by
  apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr ((ggOTwoPrime_le Y).trans hY),
    ggOTwoPrime_map_of_injective X.subtype X.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hY]


private lemma excPayL_center_eq_one_of_pow_eq_one {G : Type} [Group G] {X : Subgroup G} {p : ℕ}
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p) {z : ↥X}
    (hz : z ∈ Subgroup.center ↥X) (hzp : z ^ p = 1) : z = 1 := by
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hZ ?_
    (orderOf_dvd_of_pow_eq_one hzp))
  exact Subgroup.orderOf_dvd_natCard (Subgroup.center ↥X) hz

private lemma excPayL_center_inf_eq_bot {G : Type} [Group G] {X Bs : Subgroup G} {p : ℕ}
    (hBs : IsElemAbelian p Bs)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p) :
    (Subgroup.center ↥X).map X.subtype ⊓ Bs = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzZ, hzB⟩
  rw [Subgroup.mem_bot]
  obtain ⟨z0, hz0, rfl⟩ := Subgroup.mem_map.mp hzZ
  have hzp : z0 ^ p = 1 := Subtype.ext (hBs.2 (z0 : G) hzB)
  simpa using congrArg X.subtype (excPayL_center_eq_one_of_pow_eq_one hZ hz0 hzp)


private lemma excPayL_comm_of_mem_elemAbelian {G : Type} [Group G] {Bs : Subgroup G}
    {p : ℕ} (hBs : IsElemAbelian p Bs) {a b : G} (ha : a ∈ Bs) (hb : b ∈ Bs) :
    a * b = b * a :=
  congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private lemma excPayL_eq_of_map_eq_of_mem_inf {G H : Type} [Group G] [Group H]
    {X Bs : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs) {η : ↥X →* H}
    (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {a a' : ↥X} (ha : (a : G) ∈ Bs) (ha' : (a' : G) ∈ Bs) (h : η a = η a') : a = a' := by
  have hmem : a⁻¹ * a' ∈ η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rw [hker] at hmem
  have hpow : (a⁻¹ * a') ^ p = 1 := by
    apply Subtype.ext
    change ((a : G)⁻¹ * (a' : G)) ^ p = 1
    have hap : (a : G) ^ p = 1 := hBs.2 _ ha
    have ha'p : (a' : G) ^ p = 1 := hBs.2 _ ha'
    have hcomm : Commute (a : G) (a' : G) := excPayL_comm_of_mem_elemAbelian hBs ha ha'
    calc ((a : G)⁻¹ * (a' : G)) ^ p = ((a : G)⁻¹) ^ p * (a' : G) ^ p :=
          (hcomm.inv_left).mul_pow p
      _ = ((a : G) ^ p)⁻¹ * 1 := by rw [inv_pow, hap, ha'p]
      _ = 1 := by rw [hap]; simp
  exact inv_mul_eq_one.mp (excPayL_center_eq_one_of_pow_eq_one hZ hmem hpow)

private lemma excPayL_conj_mem_of_mem_inf {G H : Type} [Group G] [Group H]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs) {η : ↥X →* H}
    (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) {x : ↥X} (hx : η x = y)
    {u : ↥X} (hu : (u : G) ∈ Bs) : ((x : G) * u * (x : G)⁻¹) ∈ Bs := by
  let w : ↥X := x * u * x⁻¹
  have hwEq : η w = y * η u * y⁻¹ := by
    change η (x * u * x⁻¹) = y * η u * y⁻¹
    rw [map_mul, map_mul, map_inv, hx]
  have huBY : η u ∈ BY := (hB (η u)).2 ⟨u, hu, rfl⟩
  have hwBY : η w ∈ BY := hwEq ▸ (Subgroup.mem_normalizer_iff.mp hy (η u)).mp huBY
  obtain ⟨u', hu'B, hu'η⟩ := (hB (η w)).1 hwBY
  let z : ↥X := u'⁻¹ * w
  have hzker : z ∈ η.ker := by
    rw [MonoidHom.mem_ker]
    change η (u'⁻¹ * w) = 1
    rw [map_mul, map_inv, hu'η]
    simp
  rw [hker] at hzker
  have hu_pow : u ^ p = 1 := Subtype.ext (hBs.2 (u : G) hu)
  have hwpow : w ^ p = 1 := by
    change (x * u * x⁻¹) ^ p = 1
    rw [conj_pow, hu_pow]
    simp
  have hu'pow : u' ^ p = 1 := Subtype.ext (hBs.2 (u' : G) hu'B)
  have hcomm : Commute u' z := Subgroup.mem_center_iff.mp hzker u'
  have hzpow : z ^ p = 1 := by
    have hw : w = u' * z := by
      rw [show z = u'⁻¹ * w from rfl]
      group
    have h := congrArg (fun t : ↥X => t ^ p) hw
    rw [hcomm.mul_pow, hwpow, hu'pow] at h
    simpa using h.symm
  have hz1 : z = 1 := excPayL_center_eq_one_of_pow_eq_one hZ hzker hzpow
  have hw : w = u' := by
    have h : u'⁻¹ * w = 1 := hz1
    exact (inv_mul_eq_one.mp h).symm
  change (w : G) ∈ Bs
  exact hw ▸ hu'B


private lemma excPayL_mem_normalizer {G H : Type} [Group G] [Group H] [Finite G]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) {x : ↥X} (hx : η x = y) :
    (x : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  have hstep1 : ∀ u : ↥X, (u : G) ∈ Bs → ((x : G) * u * (x : G)⁻¹) ∈ Bs :=
    fun u hu => excPayL_conj_mem_of_mem_inf hBs hker hZ hB hy hx hu
  have hforward : ∀ b ∈ Bs, (x : G) * b * (x : G)⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨u, hu, hc⟩ := hsplit b hb
    let uX : ↥X := ⟨u, hu.1⟩
    have hstep : (x : G) * u * (x : G)⁻¹ ∈ Bs := hstep1 uX hu.2
    have hcB : b * u⁻¹ ∈ Bs := Bs.mul_mem hb (Bs.inv_mem hu.2)
    have hxcomm : (x : G) * (b * u⁻¹) = (b * u⁻¹) * (x : G) :=
      Subgroup.mem_centralizer_iff.mp hc (x : G) x.2
    have hb_eq : b = (b * u⁻¹) * u := by group
    have hxconj : (x : G) * (b * u⁻¹) * (x : G)⁻¹ = b * u⁻¹ := by
      rw [hxcomm]
      group
    have hconj1 : (x : G) * b * (x : G)⁻¹ =
        (x : G) * ((b * u⁻¹) * u) * (x : G)⁻¹ := by
      conv_lhs => rw [hb_eq]
    have hconj2 : (x : G) * ((b * u⁻¹) * u) * (x : G)⁻¹ =
        (b * u⁻¹) * ((x : G) * u * (x : G)⁻¹) := by
      rw [show (x : G) * ((b * u⁻¹) * u) * (x : G)⁻¹ =
          ((x : G) * (b * u⁻¹) * (x : G)⁻¹) * ((x : G) * u * (x : G)⁻¹) by
            group]
      rw [hxconj]
    rw [hconj1.trans hconj2]
    exact Bs.mul_mem hcB hstep
  have hmap_le : Bs.map (MulAut.conj (x : G)).toMonoidHom ≤ Bs := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using hforward b hb
  have hmap_eq : Bs.map (MulAut.conj (x : G)).toMonoidHom = Bs := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj (x : G)).toMonoidHom)
      (MulAut.conj (x : G)).injective]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hmap_eq


private lemma excPayL_conjAut_sq_inf {G H : Type} [Group G] [Group H]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H))
    (hrefl : GGIsReflection p (ggConjAut BY hy))
    {x : ↥X} (hx : η x = y) (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G))
    {u : ↥X} (hu : (u : G) ∈ Bs) :
    (ggConjAut Bs hxN ^ 2) ⟨u, hu⟩ = ⟨u, hu⟩ := by
  let σ := ggConjAut Bs hxN
  let rY := ggConjAut BY hy
  let uB : ↥Bs := ⟨u, hu⟩
  have huBY : η u ∈ BY := (hB (η u)).2 ⟨u, hu, rfl⟩
  have hfixY : y * (y * η u * y⁻¹) * y⁻¹ = η u := by
    have hfix : rY (rY ⟨η u, huBY⟩) = ⟨η u, huBY⟩ := by
      have h := congrArg (fun φ : MulAut ↥BY => φ ⟨η u, huBY⟩) hrefl.1
      simpa [pow_two, MulAut.mul_apply] using h
    have hval : ((rY (rY ⟨η u, huBY⟩) : ↥BY) : H) =
        y * (y * η u * y⁻¹) * y⁻¹ := by
      rw [ggConjAut_apply BY hy, ggConjAut_apply BY hy]
    have hfix' := congrArg Subtype.val hfix
    rw [hval] at hfix'
    exact hfix'
  let uX' : ↥X := ⟨((σ ^ 2) uB : G), by
    have hx2 : ((σ ^ 2) uB : G) = (x : G) ^ 2 * (u : G) * ((x : G) ^ 2)⁻¹ := by
      simpa [σ, pow_two] using ggConjAut_pow_apply Bs hxN 2 uB
    rw [hx2]
    exact X.mul_mem (X.mul_mem (X.pow_mem x.2 2) u.2) (X.inv_mem (X.pow_mem x.2 2))⟩
  have hη : η uX' = η u := by
    have huX' : uX' = x ^ 2 * u * (x ^ 2)⁻¹ := by
      apply Subtype.ext
      change ((σ ^ 2) uB : G) = (x : G) ^ 2 * (u : G) * ((x : G) ^ 2)⁻¹
      simpa [σ, pow_two] using ggConjAut_pow_apply Bs hxN 2 uB
    rw [huX', map_mul, map_mul, map_inv, map_pow, hx]
    have hpow : y ^ 2 * η u * (y ^ 2)⁻¹ = y * (y * η u * y⁻¹) * y⁻¹ := by
      rw [pow_two]; group
    rw [hpow]
    exact hfixY
  have hEqX : uX' = u :=
    excPayL_eq_of_map_eq_of_mem_inf hBs hker hZ (show ((σ ^ 2) uB : G) ∈ Bs from
      ((σ ^ 2) uB).2) hu hη
  change (σ ^ 2) uB = uB
  exact Subtype.ext (congrArg (fun t : ↥X => (t : G)) hEqX)

private lemma excPayL_conjAut_sq_center {G : Type} [Group G] {Bs X : Subgroup G}
    {x : ↥X} (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G))
    {c : G} (hcB : c ∈ Bs) (hcX : c ∈ Subgroup.centralizer (X : Set G)) :
    (ggConjAut Bs hxN ^ 2) ⟨c, hcB⟩ = ⟨c, hcB⟩ := by
  let σ := ggConjAut Bs hxN
  have hσc : σ ⟨c, hcB⟩ = ⟨c, hcB⟩ := by
    apply Subtype.ext
    change (x : G) * c * (x : G)⁻¹ = c
    rw [Subgroup.mem_centralizer_iff.mp hcX (x : G) x.2]
    group
  rw [pow_two, MulAut.mul_apply, hσc, hσc]

private lemma excPayL_conjAut_sq {G H : Type} [Group G] [Group H] [Finite G]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H))
    (hrefl : GGIsReflection p (ggConjAut BY hy))
    {x : ↥X} (hx : η x = y) (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ggConjAut Bs hxN ^ 2 = 1 := by
  let σ := ggConjAut Bs hxN
  have hσ2_inf : ∀ (u : ↥X) (hu : (u : G) ∈ Bs),
      (σ ^ 2) ⟨u, hu⟩ = ⟨u, hu⟩ :=
    fun u hu => excPayL_conjAut_sq_inf hBs hker hZ hB hy hrefl hx hxN hu
  have hσ2 : ∀ b : ↥Bs, (σ ^ 2) b = b := by
    intro b
    obtain ⟨u, hu, hc⟩ := hsplit (b : G) b.2
    let uX : ↥X := ⟨u, hu.1⟩
    let uB : ↥Bs := ⟨u, hu.2⟩
    let c : G := (b : G) * u⁻¹
    have hcB : c ∈ Bs := Bs.mul_mem b.2 (Bs.inv_mem hu.2)
    have hb_eq : b = ⟨c, hcB⟩ * uB := by
      apply Subtype.ext
      change (b : G) = c * u
      rw [show c = (b : G) * u⁻¹ from rfl]
      group
    have hσ2c := excPayL_conjAut_sq_center hxN hcB hc
    have hσ2u : (σ ^ 2) uB = uB := hσ2_inf uX hu.2
    rw [hb_eq, map_mul, hσ2c, hσ2u]
  ext b
  simpa using hσ2 b

private lemma excPayL_hyperplane_map_le {G H : Type} [Group G] [Group H] [Finite G]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) {x : ↥X} (hx : η x = y)
    (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ((X ⊓ ggHyperplane Bs (ggConjAut Bs hxN)).subgroupOf X).map η ≤
      ggHyperplane BY (ggConjAut BY hy) := by
  classical
  let σ := ggConjAut Bs hxN
  let rY := ggConjAut BY hy
  let L : Subgroup G := X ⊓ ggHyperplane Bs σ
  intro q hq
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hq
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hlH : (l : G) ∈ ggHyperplane Bs σ := hlL.2
  let lB : ↥Bs := ⟨(l : G), Subgroup.map_subtype_le
    (MonoidHom.eqLocus (σ : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs))
    (by simpa [ggHyperplane] using hlH)⟩
  have hlfixB : σ lB = lB := (mem_ggHyperplane_iff' lB).mp (by simpa using hlH)
  have hlfix : x * l * x⁻¹ = l := by
    apply Subtype.ext
    have h := congrArg (fun t : ↥Bs => (t : G)) hlfixB
    simpa [σ, ggConjAut_apply Bs hxN lB] using h
  let qBY : ↥BY := ⟨η l, (hB (η l)).2 ⟨l, lB.2, rfl⟩⟩
  have hqfix : rY qBY = qBY := by
    apply Subtype.ext
    rw [ggConjAut_apply BY hy qBY]
    change y * η l * y⁻¹ = η l
    calc y * η l * y⁻¹ = η x * η l * (η x)⁻¹ := by rw [hx]
      _ = η (x * l * x⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = η l := by rw [hlfix]
  have hqH : ((qBY : ↥BY) : H) ∈ ggHyperplane BY rY :=
    (mem_ggHyperplane_iff' qBY).mpr hqfix
  simpa using hqH

private lemma excPayL_hyperplane_map_ge {G H : Type} [Group G] [Group H] [Finite G]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) {x : ↥X} (hx : η x = y)
    (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ggHyperplane BY (ggConjAut BY hy) ≤
      ((X ⊓ ggHyperplane Bs (ggConjAut Bs hxN)).subgroupOf X).map η := by
  classical
  let σ := ggConjAut Bs hxN
  let rY := ggConjAut BY hy
  let L : Subgroup G := X ⊓ ggHyperplane Bs σ
  intro q hq
  obtain ⟨b, hbK, hbH⟩ := Subgroup.mem_map.mp hq
  have hqB : BY.subtype b ∈ ggHyperplane BY rY := by
    rwa [hbH]
  have hfixb : rY b = b := (mem_ggHyperplane_iff' b).mp hqB
  obtain ⟨u, huB, huη⟩ := (hB (b : H)).1 b.2
  let uB : ↥Bs := ⟨u, huB⟩
  have hfixu : σ uB = uB := by
    apply Subtype.ext
    have hHfix : y * (b : H) * y⁻¹ = (b : H) := by
      have h := congrArg Subtype.val hfixb
      simpa [rY, ggConjAut_apply BY hy b] using h
    have hηconj : η (x * u * x⁻¹) = η u := by
      rw [map_mul, map_mul, map_inv, hx, huη, hHfix]
    have hxuxB : ((x * u * x⁻¹ : ↥X) : G) ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hxN (u : G)).mp huB
    have hxux := excPayL_eq_of_map_eq_of_mem_inf hBs hker hZ hxuxB huB hηconj
    exact congrArg (fun t : ↥X => (t : G)) hxux
  have huL : (u : G) ∈ L := by
    refine ⟨u.2, ?_⟩
    exact (mem_ggHyperplane_iff' uB).mpr hfixu
  refine Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr huL, ?_⟩
  exact huη.trans hbH

private lemma excPayL_hyperplane_map {G H : Type} [Group G] [Group H] [Finite G]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) {x : ↥X} (hx : η x = y)
    (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ((X ⊓ ggHyperplane Bs (ggConjAut Bs hxN)).subgroupOf X).map η =
      ggHyperplane BY (ggConjAut BY hy) :=
  le_antisymm (excPayL_hyperplane_map_le hBs hker hZ hB hy hx hxN)
    (excPayL_hyperplane_map_ge hBs hker hZ hB hy hx hxN)

private lemma excPayL_centralizes_L {G H : Type} [Group G] [Group H]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {L : Subgroup G} (hLBs : L ≤ Bs) {HY : Subgroup H}
    (hLmap : (L.subgroupOf X).map η = HY) {q : H}
    (hq : q ∈ Subgroup.centralizer (HY : Set H)) {x' : ↥X} (hx' : η x' = q) :
    ∀ l : ↥X, (l : G) ∈ L → x' * l * x'⁻¹ = l := by
  intro l hlL
  have hlH : η l ∈ HY := by
    have hmem : η l ∈ (L.subgroupOf X).map η :=
      Subgroup.mem_map_of_mem η (Subgroup.mem_subgroupOf.mpr hlL)
    rwa [hLmap] at hmem
  have hcommH : η l * η x' = η x' * η l := by
    rw [hx']
    exact Subgroup.mem_centralizer_iff.mp hq (η l) hlH
  let z : ↥X := x' * l * x'⁻¹ * l⁻¹
  have hzker : z ∈ η.ker := by
    rw [MonoidHom.mem_ker]
    change η (x' * l * x'⁻¹ * l⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [← hcommH]
    group
  rw [hker] at hzker
  have hlB : (l : G) ∈ Bs := hLBs hlL
  have hlpow : l ^ p = 1 := Subtype.ext (hBs.2 (l : G) hlB)
  have hwpow : (x' * l * x'⁻¹) ^ p = 1 := by
    rw [conj_pow, hlpow]
    simp
  have hzpow : z ^ p = 1 := by
    have hw_eq : x' * l * x'⁻¹ = z * l := by
      rw [show z = x' * l * x'⁻¹ * l⁻¹ from rfl]
      group
    have hzl : Commute z l := (Subgroup.mem_center_iff.mp hzker l).symm
    have h := congrArg (fun t : ↥X => t ^ p) hw_eq
    rw [hzl.mul_pow, hwpow, hlpow] at h
    simpa using h.symm
  have hz1 : z = 1 := excPayL_center_eq_one_of_pow_eq_one hZ hzker hzpow
  have hz_eq : x' * l * x'⁻¹ * l⁻¹ = 1 := hz1
  calc x' * l * x'⁻¹ = (x' * l * x'⁻¹ * l⁻¹) * l := by group
    _ = 1 * l := by rw [hz_eq]
    _ = l := one_mul _

private lemma excPayL_hyperplane_decomp {G : Type} [Group G] {Bs X : Subgroup G}
    {x : ↥X} (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    {h : G} (hh : h ∈ ggHyperplane Bs (ggConjAut Bs hxN)) :
    ∃ c u : G, c ∈ Subgroup.centralizer (X : Set G) ∧ c ∈ Bs ∧ u ∈ X ∧
      u ∈ ggHyperplane Bs (ggConjAut Bs hxN) ∧ h = c * u := by
  have hhB : h ∈ Bs :=
    Subgroup.map_subtype_le (MonoidHom.eqLocus (ggConjAut Bs hxN : ↥Bs →* ↥Bs)
      (MonoidHom.id ↥Bs)) (by simpa [ggHyperplane] using hh)
  obtain ⟨u, hu, hc⟩ := hsplit h hhB
  have hcB : h * u⁻¹ ∈ Bs := Bs.mul_mem hhB (Bs.inv_mem hu.2)
  have hcFix : ggConjAut Bs hxN ⟨h * u⁻¹, hcB⟩ = ⟨h * u⁻¹, hcB⟩ := by
    apply Subtype.ext
    change (x : G) * (h * u⁻¹) * (x : G)⁻¹ = h * u⁻¹
    rw [Subgroup.mem_centralizer_iff.mp hc (x : G) x.2]
    group
  have hhFix : ggConjAut Bs hxN ⟨h, hhB⟩ = ⟨h, hhB⟩ :=
    (mem_ggHyperplane_iff' (⟨h, hhB⟩ : ↥Bs)).mp (by simpa using hh)
  have huFix : ggConjAut Bs hxN ⟨u, hu.2⟩ = ⟨u, hu.2⟩ := by
    have hu_eq : (⟨u, hu.2⟩ : ↥Bs) =
        ⟨h * u⁻¹, hcB⟩⁻¹ * ⟨h, hhB⟩ := by
      apply Subtype.ext
      change u = (h * u⁻¹)⁻¹ * h
      group
    rw [hu_eq, map_mul, map_inv, hcFix, hhFix]
  exact ⟨h * u⁻¹, u, hc, hcB, hu.1,
    (mem_ggHyperplane_iff' (⟨u, hu.2⟩ : ↥Bs)).mpr huFix, by group⟩

private lemma excPayL_centralizes_hyperplane {G : Type} [Group G] {Bs X : Subgroup G}
    {x : ↥X} (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G))
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    {x' : ↥X}
    (hx'L : ∀ l : ↥X, (l : G) ∈ X ⊓ ggHyperplane Bs (ggConjAut Bs hxN) →
      x' * l * x'⁻¹ = l) :
    (x' : G) ∈ Subgroup.centralizer (ggHyperplane Bs (ggConjAut Bs hxN) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨c, u, hcX, hcB, huX, huH, h_eq⟩ :=
    excPayL_hyperplane_decomp hxN hsplit hh
  have huL : ((⟨u, huX⟩ : ↥X) : G) ∈ X ⊓ ggHyperplane Bs (ggConjAut Bs hxN) :=
    ⟨huX, huH⟩
  have hx'u : (x' : G) * u = u * (x' : G) := by
    have hG : (x' : G) * u * (x' : G)⁻¹ = u := by
      have h := congrArg (fun t : ↥X => (t : G)) (hx'L ⟨u, huX⟩ huL)
      simpa using h
    calc (x' : G) * u = (x' : G) * u * (x' : G)⁻¹ * (x' : G) := by group
      _ = u * (x' : G) := by rw [hG]
  have hx'c : (x' : G) * c = c * (x' : G) :=
    Subgroup.mem_centralizer_iff.mp hcX (x' : G) x'.2
  have hcalc : (x' : G) * h = h * (x' : G) := by
    rw [h_eq]
    calc (x' : G) * (c * u) = ((x' : G) * c) * u := by group
      _ = (c * (x' : G)) * u := by rw [hx'c]
      _ = c * ((x' : G) * u) := by group
      _ = c * (u * (x' : G)) := by rw [hx'u]
      _ = (c * u) * (x' : G) := by group
  exact hcalc.symm

private lemma excPayL_centralizer_map_le {G H : Type} [Group G] [Group H] [Finite G]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    {η : ↥X →* H} (hη : Function.Surjective η)
    (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) {x : ↥X} (hx : η x = y)
    (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ((X ⊓ Subgroup.centralizer (ggHyperplane Bs (ggConjAut Bs hxN) : Set G)).subgroupOf X).map η ≤
      Subgroup.centralizer (ggHyperplane BY (ggConjAut BY hy) : Set H) := by
  let σ := ggConjAut Bs hxN
  let rY := ggConjAut BY hy
  let L : Subgroup G := X ⊓ ggHyperplane Bs σ
  have hLmap : (L.subgroupOf X).map η = ggHyperplane BY rY := by
    simpa [L, σ, rY] using excPayL_hyperplane_map hBs hker hZ hB hy hx hxN
  intro q hq
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hq
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : h ∈ (L.subgroupOf X).map η := by rwa [hLmap]
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hh'
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hcommG : (l : G) * (x' : G) = (x' : G) * (l : G) :=
    Subgroup.mem_centralizer_iff.mp hx'.2 (l : G) hlL.2
  have hcommX : l * x' = x' * l := Subtype.ext hcommG
  simpa only [map_mul] using congrArg η hcommX

private lemma excPayL_centralizer_map_ge {G H : Type} [Group G] [Group H] [Finite G]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    {η : ↥X →* H} (hη : Function.Surjective η)
    (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) {x : ↥X} (hx : η x = y)
    (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    Subgroup.centralizer (ggHyperplane BY (ggConjAut BY hy) : Set H) ≤
      ((X ⊓ Subgroup.centralizer
        (ggHyperplane Bs (ggConjAut Bs hxN) : Set G)).subgroupOf X).map η := by
  let σ := ggConjAut Bs hxN
  let rY := ggConjAut BY hy
  let L : Subgroup G := X ⊓ ggHyperplane Bs σ
  have hLmap : (L.subgroupOf X).map η = ggHyperplane BY rY := by
    simpa [L, σ, rY] using excPayL_hyperplane_map hBs hker hZ hB hy hx hxN
  have hLBs : L ≤ Bs := fun z hz =>
    Subgroup.map_subtype_le (MonoidHom.eqLocus (σ : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs))
      (by simpa [L, ggHyperplane] using hz.2)
  intro q hq
  obtain ⟨x', hx'⟩ := hη q
  have hx'L : ∀ l : ↥X, (l : G) ∈ L → x' * l * x'⁻¹ = l :=
    excPayL_centralizes_L hBs hker hZ hLBs hLmap hq hx'
  have hx'C : (x' : G) ∈ Subgroup.centralizer (ggHyperplane Bs σ : Set G) :=
    excPayL_centralizes_hyperplane hxN hsplit (by
      intro l hl
      exact hx'L l (by simpa [L, σ] using hl))
  refine Subgroup.mem_map.mpr ⟨x', ?_, hx'⟩
  exact Subgroup.mem_subgroupOf.mpr ⟨x'.2, by simpa [σ] using hx'C⟩

private lemma excPayL_centralizer_map {G H : Type} [Group G] [Group H] [Finite G]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    {η : ↥X →* H} (hη : Function.Surjective η)
    (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) {x : ↥X} (hx : η x = y)
    (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ((X ⊓ Subgroup.centralizer (ggHyperplane Bs (ggConjAut Bs hxN) : Set G)).subgroupOf X).map η =
      Subgroup.centralizer (ggHyperplane BY (ggConjAut BY hy) : Set H) :=
  le_antisymm (excPayL_centralizer_map_le hBs hsplit hη hker hZ hB hy hx hxN)
    (excPayL_centralizer_map_ge hBs hsplit hη hker hZ hB hy hx hxN)

private lemma excPayL_decomp_unique {G : Type} [Group G] {A C : Subgroup G}
    (hAC : A ⊓ C = ⊥) {a a' c c' : G} (ha : a ∈ A) (ha' : a' ∈ A)
    (hc : c ∈ C) (hc' : c' ∈ C) (h : a * c = a' * c') : a = a' ∧ c = c' := by
  have hquot : a⁻¹ * a' = c * c'⁻¹ := by
    calc a⁻¹ * a' = a⁻¹ * (a' * c') * c'⁻¹ := by group
      _ = a⁻¹ * (a * c) * c'⁻¹ := by rw [← h]
      _ = c * c'⁻¹ := by group
  have hmem : a⁻¹ * a' ∈ A ⊓ C :=
    ⟨A.mul_mem (A.inv_mem ha) ha', hquot ▸ C.mul_mem hc (C.inv_mem hc')⟩
  rw [hAC, Subgroup.mem_bot] at hmem
  have haeq : a = a' := inv_mul_eq_one.mp hmem
  refine ⟨haeq, ?_⟩
  rw [haeq] at h
  exact mul_left_cancel h

private lemma excPayL_inf_centralizer_eq_bot {G : Type} [Group G] {X Bs : Subgroup G}
    {p : ℕ} (hBs : IsElemAbelian p Bs)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p) :
    (X ⊓ Bs) ⊓ (Subgroup.centralizer (X : Set G) ⊓ Bs) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨⟨hzX, hzB⟩, hzC, -⟩
  rw [Subgroup.mem_bot]
  have hzcenter : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hzC) (w : G) w.2)
  have hzmap : z ∈ (Subgroup.center ↥X).map X.subtype := ⟨⟨z, hzX⟩, hzcenter, rfl⟩
  have hzbot : z ∈ (⊥ : Subgroup G) := by
    rw [← excPayL_center_inf_eq_bot hBs hZ]
    exact ⟨hzmap, hzB⟩
  simpa using hzbot

private lemma excPayL_isComplement {G : Type} [Group G] {X Bs : Subgroup G} {p : ℕ}
    (hBs : IsElemAbelian p Bs)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (hAC : (X ⊓ Bs) ⊓ (Subgroup.centralizer (X : Set G) ⊓ Bs) = ⊥) :
    Subgroup.IsComplement' ((X ⊓ Bs).subgroupOf Bs)
      ((Subgroup.centralizer (X : Set G) ⊓ Bs).subgroupOf Bs) := by
  classical
  let A : Subgroup G := X ⊓ Bs
  let C : Subgroup G := Subgroup.centralizer (X : Set G) ⊓ Bs
  let A' : Subgroup ↥Bs := A.subgroupOf Bs
  let C' : Subgroup ↥Bs := C.subgroupOf Bs
  rw [Subgroup.isComplement'_def, Subgroup.isComplement_iff_existsUnique]
  intro v
  obtain ⟨u, hu, hc⟩ := hsplit (v : G) v.2
  have hcB : (v : G) * u⁻¹ ∈ Bs := Bs.mul_mem v.2 (Bs.inv_mem hu.2)
  let a : A' := ⟨⟨u, hu.2⟩, Subgroup.mem_subgroupOf.mpr ⟨hu.1, hu.2⟩⟩
  let c : C' := ⟨⟨(v : G) * u⁻¹, hcB⟩, Subgroup.mem_subgroupOf.mpr ⟨hc, hcB⟩⟩
  have hprod : ((a : ↥Bs) : G) * ((c : ↥Bs) : G) = (v : G) := by
    change u * ((v : G) * u⁻¹) = (v : G)
    rw [← mul_assoc, excPayL_comm_of_mem_elemAbelian hBs hu.2 v.2]
    group
  refine ⟨(a, c), Subtype.ext hprod, ?_⟩
  rintro ⟨a₁, c₁⟩ hprod₁
  have hprodG : ((a₁ : ↥Bs) : G) * ((c₁ : ↥Bs) : G) =
      ((a : ↥Bs) : G) * ((c : ↥Bs) : G) := by
    have h1 : ((a₁ : ↥Bs) : G) * ((c₁ : ↥Bs) : G) = (v : G) :=
      congrArg Subtype.val hprod₁
    rw [h1, hprod]
  have huniq := excPayL_decomp_unique (by simpa [A, C] using hAC)
    (Subgroup.mem_subgroupOf.mp a₁.2) (Subgroup.mem_subgroupOf.mp a.2)
    (Subgroup.mem_subgroupOf.mp c₁.2) (Subgroup.mem_subgroupOf.mp c.2) hprodG
  exact Prod.ext (Subtype.ext (Subtype.ext huniq.1))
    (Subtype.ext (Subtype.ext huniq.2))

private def excPayL_aX {G : Type} [Group G] {Bs X : Subgroup G}
    (a : (X ⊓ Bs).subgroupOf Bs) : ↥X :=
  ⟨((a : ↥Bs) : G), (Subgroup.mem_subgroupOf.mp a.2).1⟩

private lemma excPayL_isComplement_equiv_mul {V : Type} [Group V] {A' C' : Subgroup V}
    (hcompl : Subgroup.IsComplement' A' C') (a : A') (c : C') :
    hcompl.equiv ((a : V) * (c : V)) = (a, c) := by
  have h1 : hcompl.equiv (a : V) = (a, ⟨1, C'.one_mem⟩) := by
    apply Prod.ext
    · exact Subgroup.IsComplement.equiv_fst_eq_self_of_mem_of_one_mem hcompl C'.one_mem a.2
    · exact Subgroup.IsComplement.equiv_snd_eq_one_of_mem_of_one_mem hcompl C'.one_mem a.2
  rw [Subgroup.IsComplement.equiv_mul_right hcompl (a : V) c, h1]
  simp

private lemma excPayL_fixed_card_product {V : Type} [Group V] {A' C' : Subgroup V}
    (hcompl : Subgroup.IsComplement' A' C') {σ : MulAut V}
    (hfixC : ∀ c : C', σ (c : V) = (c : V)) :
    Nat.card {v : V // σ v = v} =
      Nat.card {a : A' // σ (a : V) = (a : V)} * Nat.card C' := by
  let e := hcompl.equiv
  let F : {v : V // σ v = v} → {a : A' // σ (a : V) = (a : V)} × C' := fun v =>
    let a := (e v.1).1
    let c := (e v.1).2
    have hva : ((a : V) * (c : V)) = v.1 :=
      Subgroup.IsComplement.equiv_fst_mul_equiv_snd hcompl v.1
    have hfixa : σ (a : V) = (a : V) := by
      have h1 : σ ((a : V) * (c : V)) = (σ (a : V)) * (c : V) := by
        rw [map_mul, hfixC c]
      rw [hva] at h1
      have h2 : (σ (a : V)) * (c : V) = (a : V) * (c : V) := by
        rw [← h1, v.2, hva]
      exact mul_right_cancel h2
    (⟨a, hfixa⟩, c)
  let Finv : {a : A' // σ (a : V) = (a : V)} × C' → {v : V // σ v = v} := fun q =>
    ⟨((q.1.1 : A') : V) * ((q.2 : C') : V), by
      rw [map_mul, q.1.2, hfixC q.2]⟩
  have hF_left : Function.LeftInverse Finv F := by
    intro v
    apply Subtype.ext
    exact Subgroup.IsComplement.equiv_fst_mul_equiv_snd hcompl v.1
  have hF_right : Function.RightInverse Finv F := by
    rintro ⟨⟨a, ha⟩, c⟩
    apply Prod.ext
    · apply Subtype.ext
      change (e (((a : A') : V) * ((c : C') : V))).1 = a
      rw [excPayL_isComplement_equiv_mul hcompl]
    · change (e (((a : A') : V) * ((c : C') : V))).2 = c
      rw [excPayL_isComplement_equiv_mul hcompl]
  have hF_bij : Function.Bijective F := ⟨hF_left.injective, hF_right.surjective⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective F hF_bij)

private lemma excPayL_eta_equiv {G H : Type} [Group G] [Group H]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y) :
    ∃ e : (X ⊓ Bs).subgroupOf Bs ≃ ↥BY,
      ∀ a, ((e a : ↥BY) : H) = η (excPayL_aX a) := by
  let eAfun : (X ⊓ Bs).subgroupOf Bs → ↥BY := fun a =>
    ⟨η (excPayL_aX a), (hB (η (excPayL_aX a))).2
      ⟨excPayL_aX a, (Subgroup.mem_subgroupOf.mp a.2).2, rfl⟩⟩
  have heA_inj : Function.Injective eAfun := by
    intro a a' h
    have hη : η (excPayL_aX a) = η (excPayL_aX a') := congrArg Subtype.val h
    have hX := excPayL_eq_of_map_eq_of_mem_inf hBs hker hZ
      (Subgroup.mem_subgroupOf.mp a.2).2 (Subgroup.mem_subgroupOf.mp a'.2).2 hη
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : ↥X => (t : G)) hX
  have heA_surj : Function.Surjective eAfun := by
    intro q
    obtain ⟨u, huB, huη⟩ := (hB (q : H)).1 q.2
    let a : (X ⊓ Bs).subgroupOf Bs :=
      ⟨⟨(u : G), huB⟩, Subgroup.mem_subgroupOf.mpr ⟨u.2, huB⟩⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact huη
  exact ⟨Equiv.ofBijective eAfun ⟨heA_inj, heA_surj⟩, fun a => rfl⟩

private lemma excPayL_fixed_iff {G H : Type} [Group G] [Group H]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) {x : ↥X} (hx : η x = y)
    (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G))
    {eA : (X ⊓ Bs).subgroupOf Bs ≃ ↥BY}
    (heA : ∀ a, ((eA a : ↥BY) : H) = η (excPayL_aX a)) :
    ∀ a : (X ⊓ Bs).subgroupOf Bs,
      ggConjAut Bs hxN (a : ↥Bs) = (a : ↥Bs) ↔
        ggConjAut BY hy (eA a) = eA a := by
  intro a
  constructor
  · intro hfix
    apply Subtype.ext
    rw [ggConjAut_apply BY hy (eA a), heA a]
    have hconj : (x : G) * ((a : ↥Bs) : G) * (x : G)⁻¹ = ((a : ↥Bs) : G) := by
      have h := congrArg (fun t : ↥Bs => (t : G)) hfix
      simpa [ggConjAut_apply Bs hxN (a : ↥Bs)] using h
    have hxax : x * excPayL_aX a * x⁻¹ = excPayL_aX a := Subtype.ext hconj
    calc y * η (excPayL_aX a) * y⁻¹ = η (x * excPayL_aX a * x⁻¹) := by
          rw [← hx, map_mul, map_mul, map_inv]
      _ = η (excPayL_aX a) := by rw [hxax]
  · intro hfix
    have hη : η (excPayL_aX a) = η (x * excPayL_aX a * x⁻¹) := by
      rw [map_mul, map_mul, map_inv, hx, ← heA a]
      rw [← ggConjAut_apply BY hy (eA a), congrArg Subtype.val hfix]
    have haBs : ((excPayL_aX a : ↥X) : G) ∈ Bs := (Subgroup.mem_subgroupOf.mp a.2).2
    have hxB : ((x * excPayL_aX a * x⁻¹ : ↥X) : G) ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hxN (excPayL_aX a : G)).mp haBs
    have hxax : excPayL_aX a = x * excPayL_aX a * x⁻¹ :=
      excPayL_eq_of_map_eq_of_mem_inf hBs hker hZ haBs hxB hη
    apply Subtype.ext
    have hG := congrArg (fun t : ↥X => (t : G)) hxax
    simpa [excPayL_aX, ggConjAut_apply Bs hxN (a : ↥Bs)] using hG.symm

private lemma excPayL_fixed_card {G H : Type} [Group G] [Group H] [Finite G]
    {Bs X : Subgroup G} {p : ℕ} (hBs : IsElemAbelian p Bs)
    {η : ↥X →* H} (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H)) (hrefl : GGIsReflection p (ggConjAut BY hy))
    {x : ↥X} (hx : η x = y) (hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    Nat.card {b : ↥Bs // ggConjAut Bs hxN b = b} * p = Nat.card ↥Bs := by
  classical
  let V := ↥Bs
  let σ := ggConjAut Bs hxN
  let rY := ggConjAut BY hy
  let A' : Subgroup V := (X ⊓ Bs).subgroupOf Bs
  let C' : Subgroup V := (Subgroup.centralizer (X : Set G) ⊓ Bs).subgroupOf Bs
  have hcompl : Subgroup.IsComplement' A' C' := by
    simpa [A', C'] using excPayL_isComplement hBs hsplit
      (excPayL_inf_centralizer_eq_bot hBs hZ)
  have hfixC : ∀ c : C', σ (c : V) = (c : V) := by
    intro c
    have hcC : ((c : V) : G) ∈ Subgroup.centralizer (X : Set G) :=
      (Subgroup.mem_subgroupOf.mp c.2).1
    have hcomm : (x : G) * ((c : V) : G) = ((c : V) : G) * (x : G) :=
      Subgroup.mem_centralizer_iff.mp hcC (x : G) x.2
    apply Subtype.ext
    change (x : G) * ((c : V) : G) * (x : G)⁻¹ = ((c : V) : G)
    rw [hcomm]
    group
  have hcardFix : Nat.card {v : V // σ v = v} =
      Nat.card {a : A' // σ (a : V) = (a : V)} * Nat.card C' :=
    excPayL_fixed_card_product hcompl hfixC
  obtain ⟨eA, heA⟩ := excPayL_eta_equiv hBs hker hZ hB
  have hfix_iff : ∀ a : A', σ (a : V) = (a : V) ↔ rY (eA a) = eA a :=
    excPayL_fixed_iff hBs hker hZ hB hy hx hxN heA
  let eFixA : {a : A' // σ (a : V) = (a : V)} ≃ {q : ↥BY // rY q = q} :=
    Equiv.subtypeEquiv eA hfix_iff
  have hcardA : Nat.card {a : A' // σ (a : V) = (a : V)} =
      Nat.card {q : ↥BY // rY q = q} := Nat.card_congr eFixA
  have hcardBY : Nat.card {q : ↥BY // rY q = q} * p = Nat.card ↥BY := hrefl.2
  have hcardA' : Nat.card A' = Nat.card ↥BY := Nat.card_congr eA
  have hcardV : Nat.card A' * Nat.card C' = Nat.card V := hcompl.card_mul_card
  calc Nat.card {v : V // σ v = v} * p
      = (Nat.card {a : A' // σ (a : V) = (a : V)} * Nat.card C') * p := by rw [hcardFix]
    _ = (Nat.card {a : A' // σ (a : V) = (a : V)} * p) * Nat.card C' := by ring
    _ = (Nat.card {q : ↥BY // rY q = q} * p) * Nat.card C' := by rw [hcardA]
    _ = Nat.card ↥BY * Nat.card C' := by rw [hcardBY]
    _ = Nat.card A' * Nat.card C' := by rw [hcardA']
    _ = Nat.card V := hcardV

private lemma excPayL_comm_generators {G H : Type} [Group G] [Group H]
    {X : Subgroup G} (η : ↥X →* H) (hker : η.ker ≤ Subgroup.center ↥X)
    (hodd : Odd (Nat.card η.ker)) {Y Y' : Subgroup G} (hY : Y ≤ X) (hY' : Y' ≤ X)
    (hcomm : ∀ x ∈ ((ggOTwoPrime Y).subgroupOf X).map η,
      ∀ y ∈ ((ggOTwoPrime Y').subgroupOf X).map η, x * y = y * x)
    {a b : G} (haY : a ∈ Y) (ha2 : ∃ k, a ^ 2 ^ k = 1)
    (hbY : b ∈ Y') (hb2 : ∃ k, b ^ 2 ^ k = 1) : a * b = b * a := by
  classical
  let aX : ↥X := ⟨a, hY haY⟩
  let bX : ↥X := ⟨b, hY' hbY⟩
  have haGen : aX ∈ (ggOTwoPrime Y).subgroupOf X := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨haY, ha2⟩
  have hbGen : bX ∈ (ggOTwoPrime Y').subgroupOf X := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨hbY, hb2⟩
  have hcomm' : η aX * η bX = η bX * η aX :=
    hcomm (η aX) (Subgroup.mem_map_of_mem η haGen)
      (η bX) (Subgroup.mem_map_of_mem η hbGen)
  let z : ↥X := aX * bX * aX⁻¹ * bX⁻¹
  have hzker : z ∈ η.ker := by
    rw [MonoidHom.mem_ker]
    change η (aX * bX * aX⁻¹ * bX⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm']
    group
  have hzcenter : z ∈ Subgroup.center ↥X := hker hzker
  have hzN : z ^ Nat.card η.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := η.ker) (x := ⟨z, hzker⟩))
  obtain ⟨k, hk⟩ := hb2
  have hbXk : bX ^ 2 ^ k = 1 := Subtype.ext hk
  have hzb : aX * bX * aX⁻¹ = z * bX := by
    rw [show z = aX * bX * aX⁻¹ * bX⁻¹ from rfl]
    group
  have hzcomm : Commute z bX := (Subgroup.mem_center_iff.mp hzcenter bX).symm
  have hz2 : z ^ 2 ^ k = 1 := by
    have h := congrArg (fun t : ↥X => t ^ 2 ^ k) hzb
    rw [conj_pow, hbXk, mul_one, hzcomm.mul_pow, hbXk, mul_one] at h
    simpa using h.symm
  have hcop : Nat.Coprime (2 ^ k) (Nat.card η.ker) := by
    have h2N : Nat.Coprime 2 (Nat.card η.ker) := Nat.coprime_two_left.mpr hodd
    exact h2N.pow_left k
  have hz1 : z = 1 :=
    orderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hz2) (orderOf_dvd_of_pow_eq_one hzN)
  have hzX : aX * bX = bX * aX := by
    have h : aX * bX * aX⁻¹ * bX⁻¹ = 1 := hz1
    calc aX * bX = (aX * bX * aX⁻¹ * bX⁻¹) * (bX * aX) := by group
      _ = 1 * (bX * aX) := by rw [h]
      _ = bX * aX := one_mul _
  exact congrArg Subtype.val hzX

theorem excPayL_refl_lift {G H : Type} [Group G] [Group H] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hsplit : ∀ b ∈ Bs, ∃ x ∈ X ⊓ Bs, b * x⁻¹ ∈ Subgroup.centralizer (X : Set G))
    (η : ↥X →* H) (hη : Function.Surjective η) (hker : η.ker = Subgroup.center ↥X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥X)))
    {BY : Subgroup H} (hB : ∀ y : H, y ∈ BY ↔ ∃ x : ↥X, (x : G) ∈ Bs ∧ η x = y)
    {y : H} (hy : y ∈ Subgroup.normalizer (BY : Set H))
    (hrefl : GGIsReflection p (ggConjAut BY hy)) :
    ∃ (x : G) (hxN : x ∈ Subgroup.normalizer (Bs : Set G)), x ∈ X ∧
      GGIsReflection p (ggConjAut Bs hxN) ∧
      ((ggRankOneIn X Bs (ggConjAut Bs hxN)).subgroupOf X).map η =
        ggRankOneIn ⊤ BY (ggConjAut BY hy) := by
  classical
  obtain ⟨x, hx⟩ := hη y
  have hxN : (x : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    excPayL_mem_normalizer hBs hker hZ hsplit hB hy hx
  have hσ2 : ggConjAut Bs hxN ^ 2 = 1 :=
    excPayL_conjAut_sq hBs hker hZ hsplit hB hy hrefl hx hxN
  have hfix : Nat.card {b : ↥Bs // ggConjAut Bs hxN b = b} * p = Nat.card ↥Bs :=
    excPayL_fixed_card hBs hker hZ hsplit hB hy hrefl hx hxN
  refine ⟨(x : G), hxN, x.2, ⟨hσ2, hfix⟩, ?_⟩
  let CX : Subgroup G :=
    X ⊓ Subgroup.centralizer (ggHyperplane Bs (ggConjAut Bs hxN) : Set G)
  have hCXle : CX ≤ X := inf_le_left
  have hCX : (CX.subgroupOf X).map η =
      Subgroup.centralizer (ggHyperplane BY (ggConjAut BY hy) : Set H) :=
    excPayL_centralizer_map hBs hsplit hη hker hZ hB hy hx hxN
  have hkerN : ∀ z ∈ η.ker, z ^ Nat.card ↥(Subgroup.center ↥X) = 1 := by
    intro z hz
    rw [hker] at hz
    have h := pow_card_eq_one' (G := Subgroup.center ↥X) (x := ⟨z, hz⟩)
    exact congrArg Subtype.val h
  have hmap := CFSG.StandardType.KGPosSU.ggOTwoPrime_map_of_odd_ker η hodd hkerN
    (CX.subgroupOf X)
  change ((ggOTwoPrime CX).subgroupOf X).map η =
    ggRankOneIn ⊤ BY (ggConjAut BY hy)
  calc ((ggOTwoPrime CX).subgroupOf X).map η
      = (ggOTwoPrime (CX.subgroupOf X)).map η := by rw [ggOTwoPrime_subgroupOf hCXle]
    _ = ggOTwoPrime ((CX.subgroupOf X).map η) := hmap.symm
    _ = ggOTwoPrime (Subgroup.centralizer (ggHyperplane BY (ggConjAut BY hy) : Set H)) := by
          rw [hCX]
    _ = ggRankOneIn ⊤ BY (ggConjAut BY hy) := by simp [ggRankOneIn]



theorem excPayL_comm_lift {G H : Type} [Group G] [Group H] [Finite G] {X : Subgroup G}
    (η : ↥X →* H) (hker : η.ker ≤ Subgroup.center ↥X) (hodd : Odd (Nat.card η.ker))
    {Y Y' : Subgroup G} (hY : Y ≤ X) (hY' : Y' ≤ X)
    (hcomm : ∀ x ∈ ((ggOTwoPrime Y).subgroupOf X).map η,
      ∀ y ∈ ((ggOTwoPrime Y').subgroupOf X).map η, x * y = y * x) :
    ∀ x ∈ ggOTwoPrime Y, ∀ y ∈ ggOTwoPrime Y', x * y = y * x := by
  rw [ggOTwoPrime, ggOTwoPrime]
  intro x hx y hy
  have hcent_le : Subgroup.closure ({y : G | y ∈ Y ∧ ∃ k, y ^ 2 ^ k = 1} : Set G) ≤
      Subgroup.centralizer
        (Subgroup.closure ({y : G | y ∈ Y' ∧ ∃ k, y ^ 2 ^ k = 1} : Set G) : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro a ha
    rw [Subgroup.centralizer_closure]
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro b hb
    exact (excPayL_comm_generators η hker hodd hY hY' hcomm ha.1 ha.2 hb.1 hb.2).symm
  exact (Subgroup.mem_centralizer_iff.mp (hcent_le hx) y hy).symm

end CFSG.StandardType.ExcPay
