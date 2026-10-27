module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRR

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

theorem dvd_card_modO2 {X : Type} [Group X] [Finite X] {B : Subgroup X} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (h : r ∣ Nat.card B) : r ∣ Nat.card (ModO2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
  have hc := (CFSG.pCore 2 ↥B).card_eq_card_quotient_mul_card_subgroup
  rw [hc, hk] at h
  have hc2 : Nat.Coprime r (2 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  exact hc2.dvd_of_dvd_mul_right h

theorem dvd_card_of_isExt {Y : Type} [Group Y] [Finite Y] {PV PY : ∀ (V : Type) [Group V], Prop}
    {r : ℕ} (h : IsExt Y PV PY) (hY : ∀ (Z : Type) [Group Z], PY Z → r ∣ Nat.card Z) :
    r ∣ Nat.card Y := by
  obtain ⟨V, hV, -, hPY⟩ := h
  exact (hY _ hPY).trans (Subgroup.card_quotient_dvd_card V)

theorem dvd_card_of_two_le_pRank {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (h : 2 ≤ CFSG.pRank r G) : r ∣ Nat.card G := by
  have : Fact r.Prime := ⟨hr⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  have h1 := Subgroup.card_subgroup_dvd_card E
  rw [hE] at h1
  exact (dvd_pow_self r two_ne_zero).trans h1

theorem two_le_open_pRank_of_mulEquiv {X : Type} [Group X] [Finite X] {L : Subgroup X}
    {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime) (e : ↥L ≃* G)
    (h : 2 ≤ CFSG.pRank r G) : 2 ≤ CFSG.Open.pRank r L := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e,
    ← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact h

theorem two_le_pRank_of_central {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (Z : Subgroup G) [Z.Normal] (hZc : Z ≤ Subgroup.center G)
    (hZ : Nat.card Z = p) (h : 2 ≤ CFSG.pRank p (G ⧸ Z)) : 2 ≤ CFSG.pRank p G := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h ⊢
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  set π := QuotientGroup.mk' Z with hπ
  set P : Subgroup G := E.comap π with hP
  have hZP : Z ≤ P := fun z hz => by
    show π z ∈ E
    rw [show π z = 1 from (QuotientGroup.eq_one_iff z).mpr hz]
    exact E.one_mem
  have hpowZ : ∀ x ∈ P, x ^ p ∈ Z := fun x hx => by
    have h1 : π (x ^ p) = 1 := by rw [map_pow]; exact hE.2 _ hx
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcommZ : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ Z := fun x hx y hy => by
    have hxy : π x * π y = π y * π x :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨π x, hx⟩ : ↥E) ⟨π y, hy⟩)
    have h1 : π ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hxy
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcen : ∀ z ∈ Z, ∀ g : G, Commute z g := fun z hz g =>
    (Subgroup.mem_center_iff.1 (hZc hz) g).symm
  have hcoe : ∀ x y : ↥P, ((⁅x, y⁆ : ↥P) : G) = ⁅(x : G), (y : G)⁆ := fun x y => by
    simp [commutatorElement_def]
  have hc : ∀ x y z : ↥P, Commute ⁅x, y⁆ z := fun x y z => by
    have := hcen _ (hcommZ x x.2 y y.2) z
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hcoe]; exact this.eq)
  have hZpow : ∀ z ∈ Z, z ^ p = 1 := fun z hz => by
    have h1 := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hcp : ∀ x y : ↥P, ⁅x, y⁆ ^ p = 1 := fun x y =>
    Subtype.ext (by rw [SubgroupClass.coe_pow, hcoe]; exact hZpow _ (hcommZ x x.2 y y.2))
  set φ := CFSG.SectionRank.powHom hc hp.out hp2 hcp with hφ
  have hcardP : Nat.card P = p ^ 3 := by
    let ρ : ↥P →* ↥E := (π.comp P.subtype).codRestrict E fun x => x.2
    have hρs : Function.Surjective ρ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
      exact ⟨⟨x, hy⟩, rfl⟩
    have hρk : ρ.ker = Z.subgroupOf P := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
      · intro hx
        exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
    have h1 := (ρ.ker).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv, hρk,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hEc, hZ] at h1
    rw [h1]
    ring
  set K : Subgroup ↥P := φ.ker with hK
  have hK2 : p ^ 2 ≤ Nat.card K := by
    have h1 : Nat.card ↥P = Nat.card φ.range * Nat.card K := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
    have h2 : φ.range ≤ Z.subgroupOf P := by
      rintro _ ⟨x, rfl⟩
      exact hpowZ x x.2
    have h3 := Subgroup.card_le_of_le h2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ] at h3
    rw [hcardP] at h1
    have hp0 : 0 < p := hp.out.pos
    by_contra hlt
    push Not at hlt
    have : p ^ 3 < p * p ^ 2 := by
      calc p ^ 3 = Nat.card φ.range * Nat.card K := h1
        _ < p * p ^ 2 := Nat.mul_lt_mul_of_le_of_lt h3 hlt hp0
    rw [← pow_succ'] at this
    exact lt_irrefl _ this
  obtain ⟨x, hxK, hxZ⟩ : ∃ x : ↥P, x ∈ K ∧ (x : G) ∉ Z := by
    by_contra hall
    push Not at hall
    have hle : K ≤ Z.subgroupOf P := fun x hx => hall x hx
    have h3 := Subgroup.card_le_of_le hle
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ] at h3
    have : p ^ 2 ≤ p ^ 1 := by rw [pow_one]; exact hK2.trans h3
    exact absurd (Nat.pow_le_pow_iff_right hp.out.one_lt |>.mp this) (by norm_num)
  have hxp : (x : G) ^ p = 1 := by
    have h1 : φ x = 1 := hxK
    exact congrArg Subtype.val h1
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr hall
    rw [this, Subgroup.card_bot] at hZ
    exact hp.out.one_lt.ne hZ
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens (hZpow z hzZ) hxp
    (hcen z hzZ x) hz1 fun n hn => hxZ ?_
  rw [← hn]
  exact Z.pow_mem hzZ n

theorem two_le_pRank_of_surjective_coprime {G Q : Type*} [Group G] [Finite G] [Group Q]
    {p : ℕ} [hp : Fact p.Prime] (f : G →* Q) (hf : Function.Surjective f)
    (hker : ¬ p ∣ Nat.card f.ker) (h : 2 ≤ CFSG.pRank p Q) : 2 ≤ CFSG.pRank p G := by
  have : Finite Q := Finite.of_surjective f hf
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h ⊢
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  set P : Subgroup G := E.comap f with hP
  have hkP : f.ker ≤ P := fun x hx => by
    show f x ∈ E
    rw [show f x = 1 from hx]
    exact E.one_mem
  have hcardP : Nat.card P = p ^ 2 * Nat.card f.ker := by
    let ρ : ↥P →* ↥E := (f.comp P.subtype).codRestrict E fun x => x.2
    have hρs : Function.Surjective ρ := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨⟨x, hy⟩, rfl⟩
    have hρk : ρ.ker = f.ker.subgroupOf P := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩
    have h1 := (ρ.ker).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρs).toEquiv, hρk,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkP).toEquiv, hEc] at h1
    exact h1
  obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥P) p
    (hcardP ▸ Dvd.intro _ rfl : p ^ 2 ∣ Nat.card ↥P)
  set S' : Subgroup G := S.map P.subtype with hS'
  have hS'c : Nat.card S' = p ^ 2 := by
    rw [hS', Subgroup.card_map_of_injective P.subtype_injective, hS]
  have hcop : Nat.Coprime (p ^ 2) (Nat.card f.ker) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hker)
  have hinj : ∀ x ∈ S', f x = 1 → x = 1 := fun x hx hfx => by
    have h1 : orderOf x ∣ p ^ 2 := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥S')
      rwa [Subgroup.orderOf_mk, hS'c] at this
    have h2 : orderOf x ∣ Nat.card f.ker := by
      have := orderOf_dvd_natCard (⟨x, hfx⟩ : ↥f.ker)
      rwa [show orderOf (⟨x, hfx⟩ : ↥f.ker) = orderOf x from Subgroup.orderOf_mk x hfx] at this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hmem : ∀ x ∈ S', f x ∈ E := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hab : IsElemAbelian p S' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have hfab : f (a * b) = f (b * a) := by
        rw [map_mul, map_mul]
        exact congrArg Subtype.val
          (hE.1.is_comm.comm (⟨f a, hmem a a.2⟩ : ↥E) ⟨f b, hmem b b.2⟩)
      have h1 := hinj ((a : G) * b * ((b : G) * a)⁻¹)
        (S'.mul_mem (S'.mul_mem a.2 b.2) (S'.inv_mem (S'.mul_mem b.2 a.2)))
        (by rw [map_mul, map_inv, hfab, mul_inv_cancel])
      exact Subtype.ext (mul_inv_eq_one.mp h1)
    · exact hinj _ (S'.pow_mem hx p) (by rw [map_pow]; exact hE.2 _ (hmem x hx))
  exact CFSG.SectionRank.le_pRank hp.out.one_lt le_top hab hS'c

end CFSG.Quasithin.Vol2.Ch10.SecB.KRR
