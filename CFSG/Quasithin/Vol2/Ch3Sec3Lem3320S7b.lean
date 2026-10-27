module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S7a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

@[expose] def FactL2pSylowNorm : Prop :=
  ∀ p : ℕ, p.Prime → 3 < p → (p % 8 = 3 ∨ p % 8 = 5) → ∀ (Q : Type) [Group Q] [Finite Q],
    F6.IsL2 p 1 Q → ∀ S : Subgroup Q, IsSylowTwoOf S ⊤ →
      Nat.card ↥(Subgroup.normalizer (S : Set Q)) = 12

namespace S3320

variable {G : Type} [Group G] [Finite G]

theorem dih_pow_three_mul : ∀ a b : DihedralGroup 6, a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by
  decide

def dihThree : Subgroup (DihedralGroup 6) where
  carrier := {g | g ^ 3 = 1}
  mul_mem' := fun {a b} ha hb => dih_pow_three_mul a b ha hb
  one_mem' := one_pow 3
  inv_mem' := fun {a} ha => by
    show a⁻¹ ^ 3 = 1
    rw [inv_pow, show a ^ 3 = 1 from ha, inv_one]

theorem dih_pow_three_of_odd {g : DihedralGroup 6} (h : Odd (orderOf g)) : g ^ 3 = 1 := by
  have h12 : orderOf g ∣ 3 * 4 := by
    have := orderOf_dvd_natCard g
    rwa [DihedralGroup.nat_card] at this
  have hc : Nat.Coprime (orderOf g) 4 :=
    Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr h)
  exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right h12)

theorem dih_eq_one {g : DihedralGroup 6} {k : ℕ} (h3 : g ^ 3 = 1) (hk : g ^ 2 ^ k = 1) :
    g = 1 := by
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hk)
  have h2 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem dvd_three_of_dvd_twelve {n : ℕ} (h : n ∣ 12) (ho : Odd n) : n ∣ 3 := by
  have hc : Nat.Coprime n 4 := Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr ho)
  exact hc.dvd_of_dvd_mul_right (show n ∣ 3 * 4 from h)

omit [Finite G] in
theorem mem_of_odd_of_mem_sup {N S : Subgroup G} (hSN : S ≤ Subgroup.normalizer (N : Set G))
    (hS2 : IsPGroup 2 S) {y : G} (hy : y ∈ N ⊔ S) (hyo : Odd (orderOf y)) : y ∈ N := by
  obtain ⟨c, hc, r, hr, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hSN).mp hy
  obtain ⟨k, hk⟩ := hS2 ⟨r, hr⟩
  have hk' : r ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨c', hc', ec⟩ := pow_mul_mem hc (hSN hr) (2 ^ k)
  refine Lem3328.mem_of_pow_odd hyo (by rw [pow_orderOf_eq_one]; exact N.one_mem) (e := k) ?_
  rw [ec, hk', mul_one]
  exact hc'

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem simple_quot (hA : AS_A_1_31) (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D)) (hYB₀ : ¬ conjClosure X D ≤ B₀)
    (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤) :
    IsSimpleGroup (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D)) ∧
      ∃ a b : ↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D), a * b ≠ b * a := by
  obtain ⟨hsimp, hnab⟩ := H.isSimpleGroup_star hB (H.le_commutator_sup hA hB) hY H.hBY hYB₀
  rw [htop] at hsimp hnab
  refine ⟨(Subgroup.topEquiv : ↥(⊤ : Subgroup (↥(X ⊔ T ⊔ D) ⧸ B₀.subgroupOf (X ⊔ T ⊔ D))) ≃*
    _).symm.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨a, b, fun h => hab (Subtype.ext h)⟩

theorem mem_B₀_of_mem_pPrimeCore (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    {I : Subgroup G} (hIB : I ≤ X ⊔ T ⊔ D)
    (hItop : star (X ⊔ T ⊔ D) B₀ (perfectCore I) = ⊤) {x : G} (hx : x ∈ I)
    (hxP : (⟨x, hx⟩ : ↥I) ∈ CFSG.pPrimeCore 3 ↥I) : x ∈ B₀ := by
  obtain ⟨hsB, hnabB⟩ := H.simple_quot hA hB hY hYB₀ htop
  set P := (CFSG.pPrimeCore 3 ↥I).map I.subtype with hPdef
  have hPI : P ≤ I := Subgroup.map_subtype_le _
  have hPB : P ≤ X ⊔ T ⊔ D := hPI.trans hIB
  have hIP : I ≤ Subgroup.normalizer (P : Set G) := by
    have hn := CFSG.pPrimeCore_normal (p := 3) (G := ↥I)
    intro i hi
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨i, hi⟩ * w * ⟨i, hi⟩⁻¹, hn.conj_mem w hw _, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      refine ⟨⟨i, hi⟩⁻¹ * w * ⟨i, hi⟩, ?_, ?_⟩
      · have := hn.conj_mem w hw (⟨i, hi⟩⁻¹)
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hwz ⊢
        rw [hwz]
        group
  have hn : (star (X ⊔ T ⊔ D) B₀ P).Normal := by
    refine ⟨fun n hn q => ?_⟩
    have hq : q ∈ star (X ⊔ T ⊔ D) B₀ (perfectCore I) := by
      rw [hItop]
      exact Subgroup.mem_top q
    obtain ⟨k, hkB, hk, rfl⟩ := mem_star_iff.mp hq
    have hkN := mk_mem_normalizer_star (B := X ⊔ T ⊔ D) (N := B₀) (K := P) hkB
      (hIP (perfectCore_le I hk))
    exact (Subgroup.mem_normalizer_iff.mp hkN n).mp hn
  have hne : star (X ⊔ T ⊔ D) B₀ P ≠ ⊤ := by
    intro htopP
    obtain ⟨x₀, hx₀X, hx₀3, hx₀R, -⟩ := H.exists_x
    have hx₀B : x₀ ∈ X ⊔ T ⊔ D := Subgroup.mem_sup_left (Subgroup.mem_sup_left hx₀X)
    have hx₀B₀ : x₀ ∉ B₀ := fun h => hx₀R (hB.inf ⟨Subgroup.mem_sup_left hx₀X, h⟩)
    have hmem : QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨x₀, hx₀B⟩ ∈
        star (X ⊔ T ⊔ D) B₀ P := by
      rw [htopP]
      exact Subgroup.mem_top _
    obtain ⟨n, hnB, hnP, hnx⟩ := mem_star_iff.mp hmem
    obtain ⟨w, hw, rfl⟩ := hnP
    have hord : orderOf (QuotientGroup.mk' (B₀.subgroupOf (X ⊔ T ⊔ D)) ⟨x₀, hx₀B⟩) = 3 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [← map_pow]
        have : (⟨x₀, hx₀B⟩ : ↥(X ⊔ T ⊔ D)) ^ 3 = 1 := Subtype.ext (by simpa using hx₀3)
        rw [this, map_one]
      · rw [Ne, mk_eq_one_iff]
        exact hx₀B₀
    have h1 : 3 ∣ orderOf w := by
      rw [← hord, ← hnx]
      refine (orderOf_map_dvd _ _).trans ?_
      rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe w]
      rfl
    have h2 : Nat.Coprime 3 (orderOf w) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hw)
        CFSG.pPrimeCore_coprime_card
    exact absurd (Nat.Coprime.eq_one_of_dvd h2 h1) (by norm_num)
  have hbot : star (X ⊔ T ⊔ D) B₀ P = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right hne
  rw [star_eq_bot_iff hPB] at hbot
  exact hbot ⟨⟨x, hx⟩, hxP, rfl⟩

theorem dih_XT (hA : AS_A_1_31) (hB : IsB₀ X T D B₀) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D)) (hYB₀ : ¬ conjClosure X D ≤ B₀)
    (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤) {g : G} (hg : g ∈ D)
    (hcase : F6.IsF618CaseFour (plus (gZero X T g) (X ⊔ T))
        (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∨
      F6.IsF618CaseFour (plus (gZero X T g) (conjByElt g (X ⊔ T)))
        (plus (gZero X T g) (X ⊔ T)))
    (hsimp : IsSimpleGroup (↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g)))
    (hnab : ∃ a b : ↥(gZero X T g) ⧸ CFSG.pPrimeCore 3 ↥(gZero X T g), a * b ≠ b * a)
    (hK₀top : star (X ⊔ T ⊔ D) B₀ (perfectCore (gZero X T g)) = ⊤)
    (hP : pCoreOf 2 (conjClosure X D ⊔ T) = (conjClosure X D ⊔ T) ⊓ B₀) :
    ∃ _ : ((pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T)).Normal,
      Nonempty (↥(X ⊔ T) ⧸ (pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T) ≃*
        DihedralGroup 6) := by
  have hXTG : X ⊔ T ≤ gZero X T g := le_sup_left
  have hGB : gZero X T g ≤ X ⊔ T ⊔ D := gZero_le hg
  have hXTY : X ⊔ T ≤ conjClosure X D ⊔ T := sup_le_sup_right (le_conjClosure X D) T
  have hD12 : Nonempty (↥(plus (gZero X T g) (X ⊔ T)) ≃* DihedralGroup 6) := by
    rcases hcase with h | h
    · exact h.2.2.1
    · exact h.2.2.2
  obtain ⟨e⟩ := hD12
  let eG : ↥(X ⊔ T) ≃* ↥((X ⊔ T).subgroupOf (gZero X T g)) :=
    (Subgroup.subgroupOfEquivOfLe hXTG).symm
  let ψ : ↥(X ⊔ T) →* ↥(plus (gZero X T g) (X ⊔ T)) :=
    ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(gZero X T g))).subgroupMap
      ((X ⊔ T).subgroupOf (gZero X T g))).comp eG.toMonoidHom
  have hψs : Function.Surjective ψ := (MonoidHom.subgroupMap_surjective _ _).comp eG.surjective
  have hker : ψ.ker = (pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hP]
    have h1 : ψ u = 1 ↔ QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(gZero X T g))
        ⟨(u : G), hXTG u.2⟩ = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [h1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨hXTY u.2, H.mem_B₀_of_mem_pPrimeCore hA hB hY hYB₀ htop hGB hK₀top _ h⟩
    · intro h
      exact H.mem_pPrimeCore_of_mem hB hGB hsimp hnab _ h.2
  have hn : ((pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T)).Normal :=
    hker ▸ ψ.normal_ker
  exact ⟨hn, ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)).trans e⟩⟩

theorem pCoreOf_X_le (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D))
    (hP : pCoreOf 2 (conjClosure X D ⊔ T) = (conjClosure X D ⊔ T) ⊓ B₀)
    [((pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T)).Normal]
    (e : ↥(X ⊔ T) ⧸ (pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T) ≃* DihedralGroup 6) :
    pCoreOf 2 X ≤ pCoreOf 2 (conjClosure X D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ϕ : ↥(X ⊔ T) →* DihedralGroup 6 := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hX3 : ∀ x (hx : x ∈ X), ϕ ⟨x, Subgroup.mem_sup_left hx⟩ ∈ dihThree := by
    have key : ∀ y ∈ oTwoUpper X, ∀ hy : y ∈ X, ϕ ⟨y, Subgroup.mem_sup_left hy⟩ ∈ dihThree := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        intro _
        apply dih_pow_three_of_odd
        refine Odd.of_dvd_nat ?_ (orderOf_map_dvd ϕ _)
        rw [Subgroup.orderOf_mk]
        exact hz.2
      | one =>
        intro _
        show ϕ 1 ∈ dihThree
        rw [map_one]
        exact dihThree.one_mem
      | mul y z hy hz ihy ihz =>
        intro hyz
        have hy' : y ∈ X := oTwoUpper_le X hy
        have hz' : z ∈ X := oTwoUpper_le X hz
        have e1 : (⟨y * z, Subgroup.mem_sup_left hyz⟩ : ↥(X ⊔ T)) =
            ⟨y, Subgroup.mem_sup_left hy'⟩ * ⟨z, Subgroup.mem_sup_left hz'⟩ := rfl
        rw [e1, map_mul]
        exact dihThree.mul_mem (ihy hy') (ihz hz')
      | inv y hy ihy =>
        intro hy''
        have hy' : y ∈ X := oTwoUpper_le X hy
        have e1 : (⟨y⁻¹, Subgroup.mem_sup_left hy''⟩ : ↥(X ⊔ T)) =
            (⟨y, Subgroup.mem_sup_left hy'⟩ : ↥(X ⊔ T))⁻¹ := rfl
        rw [e1, map_inv]
        exact dihThree.inv_mem (ihy hy')
    intro x hx
    exact key x (by rw [H.hXX]; exact hx) hx
  intro q hq
  have hqX : q ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hq
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) ⟨q, hq⟩
  have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : ϕ ⟨q, Subgroup.mem_sup_left hqX⟩ = 1 := by
    refine dih_eq_one (hX3 q hqX) (k := k) ?_
    rw [← map_pow]
    have : (⟨q, Subgroup.mem_sup_left hqX⟩ : ↥(X ⊔ T)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk')
    rw [this, map_one]
  have h2 : (⟨q, Subgroup.mem_sup_left hqX⟩ : ↥(X ⊔ T)) ∈
      (pCoreOf 2 (conjClosure X D ⊔ T)).subgroupOf (X ⊔ T) := by
    have h3 : QuotientGroup.mk' _ (⟨q, Subgroup.mem_sup_left hqX⟩ : ↥(X ⊔ T)) = 1 :=
      (MulEquiv.map_eq_one_iff e).mp h1
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  rw [Subgroup.mem_subgroupOf, hP] at h2
  have hqY : q ∈ conjClosure X D := le_conjClosure X D hqX
  have hqO : q ∈ pCoreOf 2 (X ⊔ T ⊔ D) := hle ⟨hqY, h2.2⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (N := conjClosure X D ⊓ pCoreOf 2 (X ⊔ T ⊔ D)) inf_le_left ?_ ?_ ⟨hqY, hqO⟩
  · intro y hy
    exact ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hy)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Y_le_B hy))
  · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right

theorem relIndex_normalizer_X (hL2n : FactL2pSylowNorm) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D))
    (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤) {p : ℕ} (hp : p.Prime)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13)
    (hL : F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) :
    (D ⊓ Subgroup.normalizer (X : Set G)).relIndex D = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  have hOT : pCoreOf 2 (X ⊔ T ⊔ D) ≤ T := by
    rw [← hT₀]
    exact inf_le_left
  have hDB : D ≤ X ⊔ T ⊔ D := le_sup_right
  have hDB₀ : D ⊓ B₀ ≤ D ⊓ Subgroup.normalizer (X : Set G) := by
    refine le_inf inf_le_left (Main3324.le_normalizer_of_conj fun d hd x hx => ?_)
    have key : ∀ y ∈ oTwoUpper X, d * y * d⁻¹ ∈ X := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨hzX, hzo⟩ := hz
        have hzY : z ∈ conjClosure X D := le_conjClosure X D hzX
        have hc : d * z * d⁻¹ * z⁻¹ ∈ pCoreOf 2 (X ⊔ T ⊔ D) := by
          refine hle ⟨?_, ?_⟩
          · have h1 : d * z * d⁻¹ ∈ conjClosure X D :=
              (Subgroup.mem_normalizer_iff.mp (H.hBY (hDB hd.1)) z).mp hzY
            exact (conjClosure X D).mul_mem h1 ((conjClosure X D).inv_mem hzY)
          · have h1 : z * d⁻¹ * z⁻¹ ∈ B₀ :=
              (Subgroup.mem_normalizer_iff.mp
                (hB.nor (Subgroup.mem_sup_left (Subgroup.mem_sup_left hzX))) d⁻¹).mp
                (B₀.inv_mem hd.2)
            have e : d * z * d⁻¹ * z⁻¹ = d * (z * d⁻¹ * z⁻¹) := by group
            rw [e]
            exact B₀.mul_mem hd.2 h1
        have hy : d * z * d⁻¹ ∈ X ⊔ pCoreOf 2 (X ⊔ T ⊔ D) := by
          have e : d * z * d⁻¹ = (d * z * d⁻¹ * z⁻¹) * z := by group
          rw [e, sup_comm]
          exact Subgroup.mul_mem_sup hc hzX
        refine mem_of_odd_of_mem_sup (hOT.trans H.hTX)
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hy ?_
        have := orderOf_injective (MulAut.conj d).toMonoidHom (MulAut.conj d).injective z
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        rw [this]
        exact hzo
      | one => simp
      | mul y z _ _ ihy ihz =>
        have e : d * (y * z) * d⁻¹ = (d * y * d⁻¹) * (d * z * d⁻¹) := by group
        rw [e]
        exact X.mul_mem ihy ihz
      | inv y _ ihy =>
        have e : d * y⁻¹ * d⁻¹ = (d * y * d⁻¹)⁻¹ := by group
        rw [e]
        exact X.inv_mem ihy
    exact key x (by rw [H.hXX]; exact hx)
  have hne : ¬ D ≤ Subgroup.normalizer (X : Set G) := by
    intro hDX
    apply H.hD
    intro d hd
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) (X ⊔ T)
      (ChiefCount.mem_normalizer_sup (hDX hd) (H.h.DN hd))
  have hD3 : B₀.relIndex D ∣ 3 := by
    rw [← card_star hDB]
    have hodd : Odd (Nat.card ↥(star (X ⊔ T ⊔ D) B₀ D)) := by
      have h1 : Nat.card ↥(star (X ⊔ T ⊔ D) B₀ D) ∣ Nat.card ↥(D.subgroupOf (X ⊔ T ⊔ D)) :=
        Subgroup.card_dvd_of_surjective ((QuotientGroup.mk' _).subgroupMap_surjective _)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv] at h1
      exact Odd.of_dvd_nat H.h.Dodd h1
    have hTQ : star (X ⊔ T ⊔ D) B₀ T ≤ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := htop ▸ le_top
    have hDQ : star (X ⊔ T ⊔ D) B₀ D ≤ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := htop ▸ le_top
    have hsyl := H.isSylowTwoOf_star_T (B₀ := B₀)
    have hsyl' : IsSylowTwoOf ((star (X ⊔ T ⊔ D) B₀ T).subgroupOf
        (star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) ⊤ := by
      refine ⟨le_top, hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTQ).symm, fun h2 => ?_⟩
      apply hsyl.2.2
      have h3 : (((star (X ⊔ T ⊔ D) B₀ T).subgroupOf
          (star (X ⊔ T ⊔ D) B₀ (conjClosure X D))).subgroupOf ⊤).index =
          (star (X ⊔ T ⊔ D) B₀ T).relIndex (star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) :=
        Subgroup.relIndex_top_right _
      rw [h3, htop] at h2
      exact h2
    have hp3 : 3 < p := by
      have := hp.two_le
      omega
    have hp8 : p % 8 = 3 ∨ p % 8 = 5 := by omega
    have h12 := hL2n p hp hp3 hp8 _ hL _ hsyl'
    have hDN : (star (X ⊔ T ⊔ D) B₀ D).subgroupOf (star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) ≤
        Subgroup.normalizer (((star (X ⊔ T ⊔ D) B₀ T).subgroupOf
          (star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) : Subgroup ↥(star (X ⊔ T ⊔ D) B₀
            (conjClosure X D))) : Set ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) := by
      intro d hd
      rw [Subgroup.mem_normalizer_iff]
      intro s
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      obtain ⟨d', hd'B, hd', hdd⟩ := mem_star_iff.mp (Subgroup.mem_subgroupOf.mp hd)
      have hN := mk_mem_normalizer_star (B := X ⊔ T ⊔ D) (N := B₀) (K := T) hd'B (H.h.DN hd')
      rw [hdd] at hN
      exact Subgroup.mem_normalizer_iff.mp hN _
    have h1 := Subgroup.card_dvd_of_le hDN
    rw [h12, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv] at h1
    exact dvd_three_of_dvd_twelve h1 hodd
  have h1 : (D ⊓ Subgroup.normalizer (X : Set G)).relIndex D ∣ B₀.relIndex D := by
    have h2 : B₀.relIndex D = (D ⊓ B₀).relIndex D := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [h2]
    exact Subgroup.relIndex_dvd_of_le_left D hDB₀
  rcases (Nat.dvd_prime Nat.prime_three).mp (h1.trans hD3) with h | h
  · exact absurd (fun d hd => (Subgroup.relIndex_eq_one.mp h hd).2) hne
  · exact h

end Hyp3320

end S3320

end CFSG.Quasithin.H13
