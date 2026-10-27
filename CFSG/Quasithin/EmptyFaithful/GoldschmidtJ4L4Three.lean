module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Alt8
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Lift
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.Quasithin.J4L4

local notation "A₈" => alternatingGroup (Fin 8)

variable {M Q : Type*} [Group M] [Group Q]

theorem centralizes_of_card_three {Z : Subgroup Q} (hZ : Z.Normal) (hZ3 : Nat.card Z = 3) {x : Q}
    (hx : x ^ 5 = 1) (z : Q) (hz : z ∈ Z) : x * z = z * x := by
  have := hZ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  have : IsCyclic Z := isCyclic_of_prime_card hZ3
  have hcard : Nat.card (MulAut Z) = 2 := by
    rw [IsCyclic.card_mulAut, hZ3]
    decide
  set κ : MulAut Z := MulAut.conjNormal x with hκ
  have h5 : κ ^ 5 = 1 := by
    rw [hκ, ← map_pow, hx, map_one]
  have h2 : κ ^ 2 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hone : κ = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one h2)
    have : Nat.gcd 5 2 = 1 := by norm_num
    rw [this] at h
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h)
  have := congrArg (fun φ : MulAut Z => ((φ ⟨z, hz⟩ : Z) : Q)) hone
  simp only [hκ, MulAut.conjNormal_apply, MulAut.one_apply] at this
  exact mul_inv_eq_iff_eq_mul.1 this

theorem isSolvable_comap [Finite M] (π : M →* Q) (hP : IsPGroup 2 π.ker) {Z : Subgroup Q}
    (hZ3 : Nat.card Z = 3) : Group.IsSolvable ↥(Z.comap π) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Z := Nat.finite_of_card_ne_zero (by omega)
  have : IsCyclic Z := isCyclic_of_prime_card hZ3
  have : Group.IsSolvable ↥π.ker := by
    have := hP.isNilpotent
    infer_instance
  have hle : π.ker ≤ Z.comap π := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact Z.one_mem
  let ρ : ↥(Z.comap π) →* ↥Z := (π.comp (Z.comap π).subtype).codRestrict Z fun w => w.2
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hle) ρ ?_
  intro w hw
  refine ⟨⟨w, ?_⟩, Subtype.ext rfl⟩
  have h1 : ρ w = 1 := hw
  have h2 : π (w : M) = 1 := congrArg Subtype.val h1
  exact h2

theorem nine_dvd_card {D Z : Subgroup Q} (hZD : Z ≤ D) (hZ : Z.Normal) (hZ3 : Nat.card Z = 3)
    {x : Q} (hxD : x ∈ D) (hxZ : x ∉ Z) (hx3 : x ^ 3 = 1) : 9 ∣ Nat.card D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (Z.subgroupOf D).Normal := hZ.subgroupOf D
  have h3N : Nat.card (Z.subgroupOf D) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv, hZ3]
  have hx1 : ((⟨x, hxD⟩ : D) : D ⧸ Z.subgroupOf D) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    exact hxZ (Subgroup.mem_subgroupOf.1 h1)
  have hx3' : ((⟨x, hxD⟩ : D) : D ⧸ Z.subgroupOf D) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have : (((⟨x, hxD⟩ : D) ^ 3 : D) : Q) = 1 := by
      rw [Subgroup.coe_pow]
      exact hx3
    rw [this]
    exact Z.one_mem
  have hord : orderOf ((⟨x, hxD⟩ : D) : D ⧸ Z.subgroupOf D) = 3 := by
    have hd : orderOf ((⟨x, hxD⟩ : D) : D ⧸ Z.subgroupOf D) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3'
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have h3q : 3 ∣ Nat.card (D ⧸ Z.subgroupOf D) := by
    rw [← hord]
    exact orderOf_dvd_natCard _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf D), h3N]
  obtain ⟨t, ht⟩ := h3q
  exact ⟨t, by rw [ht]; ring⟩

theorem false_of_normal_three [Finite M] [Finite Q] (π : M →* Q) (hπ : Function.Surjective π)
    (hP : IsPGroup 2 π.ker) {Z : Subgroup Q} (hZ : Z.Normal) (hZ3 : Nat.card Z = 3)
    (h9 : ∀ g : M, orderOf g = 5 → ¬ 9 ∣ Nat.card (Subgroup.centralizer ({g} : Set M)))
    {B : Type*} [Group B] (ι : B →* M) (hι : Function.Injective ι) (f : B →* A₈)
    (hf : Function.Surjective f) (hker : ∀ x : B, f x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite B := Finite.of_injective ι hι
  have hsimple : IsSimpleGroup A₈ := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨a, ha⟩ := exists_order_fifteen
  obtain ⟨b, hbodd, hb⟩ := exists_odd_lift f hf (x := a) (by rw [ha]; decide)
  have hb15 : orderOf b = 15 := by
    have h1 : 15 ∣ orderOf b := by
      have := orderOf_map_dvd f b
      rwa [hb, ha] at this
    have h2 : b ^ 15 = 1 := by
      obtain ⟨k, e2⟩ := hker (b ^ 15) (by rw [map_pow, hb]; exact ha ▸ pow_orderOf_eq_one a)
      have eo : (b ^ 15) ^ orderOf b = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
      have hc : Nat.Coprime (2 ^ k) (orderOf b) :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hbodd)
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one e2)
        (orderOf_dvd_of_pow_eq_one eo))
    exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one h2) h1
  set b' : M := ι b with hb'
  have hb'15 : orderOf b' = 15 := by
    rw [hb', orderOf_injective ι hι b, hb15]
  set g : M := b' ^ 3 with hg
  set c : M := b' ^ 5 with hc
  have hg5 : orderOf g = 5 := by
    rw [hg, orderOf_pow_of_dvd (by norm_num) (by rw [hb'15]; norm_num), hb'15]
  have hc3 : orderOf c = 3 := by
    rw [hc, orderOf_pow_of_dvd (by norm_num) (by rw [hb'15]; norm_num), hb'15]
  have hcg : c * g = g * c := (Commute.pow_pow_self b' 5 3).eq
  have hg5pow : g ^ 5 = 1 := hg5 ▸ pow_orderOf_eq_one g
  have hc3pow : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  have hg5' : (π g) ^ 5 = 1 := by
    rw [← map_pow, hg5pow, map_one]
  have hCg : Z ≤ (Subgroup.centralizer ({g} : Set M)).map π := by
    intro z hz
    obtain ⟨m, hm, hmz⟩ := exists_centralizer_lift π hπ hP hg5
      (d := z) (centralizes_of_card_three hZ hZ3 hg5' z hz).symm
    exact ⟨m, Subgroup.mem_centralizer_singleton_iff.2 hm, hmz⟩
  have hcZ : π c ∈ Z := by
    by_contra hnot
    have hcD : π c ∈ (Subgroup.centralizer ({g} : Set M)).map π :=
      ⟨c, Subgroup.mem_centralizer_singleton_iff.2 hcg, rfl⟩
    have h9D := nine_dvd_card hCg hZ hZ3 hcD hnot (by rw [← map_pow, hc3pow, map_one])
    exact h9 g hg5 (h9D.trans (Subgroup.card_map_dvd (Subgroup.centralizer ({g} : Set M)) π))
  have hWs := isSolvable_comap π hP hZ3
  have : (Z.comap π).Normal := hZ.comap π
  set N0 : Subgroup B := Z.comap (π.comp ι) with hN0
  have : N0.Normal := hZ.comap (π.comp ι)
  have : Group.IsSolvable ↥N0 := by
    let ι' : ↥N0 →* ↥(Z.comap π) := (ι.comp N0.subtype).codRestrict (Z.comap π) fun w => w.2
    refine Group.isSolvable_of_isSolvable_injective (f := ι') ?_
    intro u v huv
    have h1 := congrArg Subtype.val huv
    exact Subtype.ext (hι h1)
  have hbN : b ^ 5 ∈ N0 := by
    show π (ι (b ^ 5)) ∈ Z
    rw [map_pow]
    exact hcZ
  have : (N0.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hne : N0.map f ≠ ⊥ := by
    intro h
    have : f (b ^ 5) ∈ N0.map f := Subgroup.mem_map_of_mem f hbN
    rw [h, Subgroup.mem_bot, map_pow, hb] at this
    have h1 : orderOf (a ^ 5) = 3 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [ha]; norm_num), ha]
    rw [this, orderOf_one] at h1
    omega
  have htop : N0.map f = ⊤ := (hsimple.eq_bot_or_eq_top_of_normal _).resolve_left hne
  have hsurj : Function.Surjective (f.comp N0.subtype) := by
    intro y
    have : y ∈ N0.map f := htop ▸ Subgroup.mem_top y
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have : Group.IsSolvable A₈ := Group.isSolvable_of_surjective (f := f.comp N0.subtype) hsurj
  obtain ⟨u, v, huv⟩ := exists_noncomm
  exact huv ((IsSimpleGroup.comm_iff_isSolvable (G := A₈)).2 inferInstance u v)

end CFSG.Quasithin.J4L4
