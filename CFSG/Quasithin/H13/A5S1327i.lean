module

public import CFSG.Quasithin.H13.A5S1327h

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

theorem perm3_conj_mul : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ ^ 3 ≠ 1 →
    ((Equiv.swap 0 1 * Equiv.swap 1 2) * σ * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ * σ) ^ 3 = 1 ∧
      (Equiv.swap 0 1 * Equiv.swap 1 2) * σ * (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ * σ ≠ 1 := by
  decide +kernel

theorem perm3_words_gen : ∀ α β σ : Equiv.Perm (Fin 3), α ≠ 1 → α ^ 3 = 1 → β ≠ 1 → β ^ 2 = 1 →
    σ = 1 ∨ σ = α ∨ σ = α ^ 2 ∨ σ = β ∨ σ = α * β ∨ σ = α ^ 2 * β := by
  decide

theorem perm3_cube_mul : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by
  decide

section HallW

theorem mem_of_odd_of_mem_sup_normal {Q : Type} [Group Q] [Finite Q] {Zc Tb : Subgroup Q}
    (hZn : Zc.Normal) (hTb : IsPGroup 2 ↥Tb) {y : Q} (hy : y ∈ Zc ⊔ Tb)
    (hyo : Odd (orderOf y)) : y ∈ Zc := by
  have hTN : Tb ≤ Subgroup.normalizer (Zc : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hZn]
    exact le_top
  have hy' : y ∈ ((Zc ⊔ Tb : Subgroup Q) : Set Q) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Zc Tb hTN] at hy'
  obtain ⟨z, hz, t, ht, rfl⟩ := hy'
  have hyN : z * t ∈ Subgroup.normalizer (Zc : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hZn]
    exact Subgroup.mem_top _
  obtain ⟨z', hz', he⟩ := pow_mem_mul_of_normalizes (Zc.inv_mem hz) hyN (orderOf (z * t))
  rw [pow_orderOf_eq_one, mul_one] at he
  have htm : t ^ orderOf (z * t) ∈ Zc := by
    have e : t ^ orderOf (z * t) = (z⁻¹ * (z * t)) ^ orderOf (z * t) := by
      rw [inv_mul_cancel_left]
    rw [e, he]
    exact hz'
  obtain ⟨b, hb⟩ := hTb ⟨t, ht⟩
  have hb' : t ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hco : Nat.Coprime (orderOf (z * t)) (orderOf t) := by
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hb')
    rw [hc]
    exact Nat.Coprime.pow_right c (Nat.coprime_two_right.mpr hyo)
  have htZ : t ∈ Zc := (Subgroup.zpowers_le.mpr htm) (A4.mem_zpowers_pow_of_coprime hco)
  exact Zc.mul_mem hz htZ

theorem card_le_three_of_isPGroup {I : Type} [Group I] [Finite I] {N : Subgroup I} [N.Normal]
    (hN3 : Nat.Coprime 3 (Nat.card ↥N)) {Zc Tb : Subgroup (I ⧸ N)} (hZn : Zc.Normal)
    (hZc3 : Nat.card ↥Zc = 3) (hTb : IsPGroup 2 ↥Tb) {P : Subgroup I} (hP : IsPGroup 3 ↥P)
    (hPY : P ≤ (Zc ⊔ Tb).comap (QuotientGroup.mk' N)) : Nat.card ↥P ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' N with hπ
  have hinj : Function.Injective (π.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxN : (x : I) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨a, ha⟩ := hP x
    have h1 : orderOf (⟨x, hxN⟩ : ↥N) ∣ Nat.card ↥N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf (x : I) ∣ 3 ^ a := by
      refine orderOf_dvd_of_pow_eq_one ?_
      simpa using congrArg Subtype.val ha
    have h3 : orderOf (x : I) = 1 := by
      have hco := Nat.Coprime.coprime_dvd_right h1 hN3
      have hco' : Nat.Coprime (3 ^ a) (orderOf (x : I)) := Nat.Coprime.pow_left a hco
      exact Nat.Coprime.eq_one_of_dvd hco'.symm h2
    rw [orderOf_eq_one_iff] at h3
    exact Subgroup.mem_bot.mpr (Subtype.ext h3)
  have himg : (π.comp P.subtype).range ≤ Zc := by
    rintro _ ⟨x, rfl⟩
    refine mem_of_odd_of_mem_sup_normal hZn hTb (hPY x.2) ?_
    obtain ⟨a, ha⟩ := hP x
    have h2 : orderOf (π x) ∣ 3 ^ a := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow]
      have : (x : I) ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
      rw [this, map_one]
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    show Odd (orderOf (π x))
    rw [hc]
    exact Odd.pow (by decide)
  have h1 : Nat.card ↥P = Nat.card ↥(π.comp P.subtype).range :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv)
  rw [h1, ← hZc3]
  exact Subgroup.card_le_of_le himg

theorem exists_W {I : Type} [Group I] [Finite I] {N Tt : Subgroup I} [N.Normal]
    (hNs : Group.IsSolvable ↥N) (hN3 : Nat.Coprime 3 (Nat.card ↥N)) (hTt : IsSylowTwoOf Tt ⊤)
    {Zc : Subgroup (I ⧸ N)} (hZn : Zc.Normal) (hZc3 : Nat.card ↥Zc = 3) :
    ∃ W : Subgroup I, Tt ≤ W ∧ Nat.card ↥W = 3 * Nat.card ↥Tt ∧
      W ≤ (Zc ⊔ Tt.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) ∧
      Group.IsSolvable ↥W := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  set Tb := Tt.map π with hTb
  set A := Zc ⊔ Tb with hA
  set Y := A.comap π with hY
  have hTt2 : IsPGroup 2 ↥Tt := hTt.2.1
  have hTb2 : IsPGroup 2 ↥Tb := hTt2.map π
  have hTN : Tb ≤ Subgroup.normalizer (Zc : Set (I ⧸ N)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hZn]
    exact le_top
  have hAs : Group.IsSolvable ↥A := by
    have hZnA : (Zc.subgroupOf A).Normal := hZn.subgroupOf A
    have hZs : Group.IsSolvable ↥(Zc.subgroupOf A) := by
      refine Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext ?_)
      exact comm_of_card_three hZc3 a.2 b.2
    have hQ2 : IsPGroup 2 (↥A ⧸ Zc.subgroupOf A) := by
      intro q
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Zc.subgroupOf A) q
      have ha : (a : I ⧸ N) ∈ ((Zc ⊔ Tb : Subgroup (I ⧸ N)) : Set (I ⧸ N)) := a.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left Zc Tb hTN] at ha
      obtain ⟨z, hz, t, ht, hzt⟩ := ha
      obtain ⟨b, hb⟩ := hTb2 ⟨t, ht⟩
      refine ⟨b, ?_⟩
      have htA : t ∈ A := Subgroup.mem_sup_right ht
      have hzA : z ∈ A := Subgroup.mem_sup_left hz
      have e : a = ⟨z, hzA⟩ * ⟨t, htA⟩ := Subtype.ext hzt.symm
      have h1 : QuotientGroup.mk' (Zc.subgroupOf A) (⟨z, hzA⟩ : ↥A) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hz
      have h2 : (⟨t, htA⟩ : ↥A) ^ 2 ^ b = 1 := Subtype.ext (by simpa using congrArg Subtype.val hb)
      rw [e, map_mul, h1, one_mul, ← map_pow, h2, map_one]
    have := hQ2.isNilpotent
    exact Group.isSolvable_of_subgroup_quotient (Zc.subgroupOf A)
  have hNY : N ≤ Y := fun n hn => by
    show π n ∈ A
    have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [h1]
    exact A.one_mem
  have hYs : Group.IsSolvable ↥Y := by
    let g : ↥Y →* ↥A := (π.comp Y.subtype).codRestrict A fun y => y.2
    let f : ↥N →* ↥Y := Subgroup.inclusion hNY
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro y hy
    have h1 : π (y : I) = 1 := congrArg Subtype.val hy
    exact ⟨⟨y, (QuotientGroup.eq_one_iff _).mp h1⟩, rfl⟩
  have hTY : Tt ≤ Y := fun t ht => Subgroup.mem_sup_right ⟨t, ht, rfl⟩
  set pi23 : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} with hpi23
  have hTpi : CFSG.IsPiSubgroup pi23 (Tt.subgroupOf Y) := by
    intro p hp
    have hcard : Nat.card ↥(Tt.subgroupOf Y) = Nat.card ↥Tt :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv
    obtain ⟨a, ha⟩ := hTt2.exists_card_eq
    rw [hcard, ha] at hp
    have : p.val = 2 := (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).mp (p.2.dvd_of_dvd_pow hp)
    left
    exact Subtype.ext this
  obtain ⟨W', hW', hTW'⟩ := CFSG.SolvableHall.solvable_hall_containment hYs pi23 _ hTpi
  set W := W'.map Y.subtype with hW
  have hWcard : Nat.card ↥W = Nat.card ↥W' :=
    Subgroup.card_map_of_injective Y.subtype_injective
  have hTW : Tt ≤ W := fun t ht => ⟨⟨t, hTY ht⟩, hTW' ht, rfl⟩
  have hWY : W ≤ Y := Subgroup.map_subtype_le W'
  have h3W : 3 ∣ Nat.card ↥W := by
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Zc, z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Zc = ⊥ := eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hcon z hz)
      rw [this, Subgroup.card_bot] at hZc3
      omega
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N z
    have hyY : y ∈ Y := by
      show π y ∈ A
      rw [hy]
      exact Subgroup.mem_sup_left hz
    have h3y : 3 ∣ orderOf y := by
      have h1 : orderOf z ∣ orderOf y := by rw [← hy]; exact orderOf_map_dvd π y
      have h2 : orderOf z = 3 := by
        have h4 : orderOf (⟨z, hz⟩ : ↥Zc) ∣ 3 := hZc3 ▸ orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h4
        rcases (Nat.dvd_prime Nat.prime_three).1 h4 with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hz1
        · exact h
      rw [h2] at h1
      exact h1
    have h3Y : 3 ∣ Nat.card ↥Y := by
      have h1 : orderOf (⟨y, hyY⟩ : ↥Y) ∣ Nat.card ↥Y := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact h3y.trans h1
    have hidx : ¬ 3 ∣ W'.index := fun h =>
      hW'.p_in_pi_of_p_dvd_index ⟨3, Nat.prime_three⟩ h (Or.inr rfl)
    rw [← W'.card_mul_index] at h3Y
    rw [hWcard]
    exact (Nat.Prime.dvd_mul Nat.prime_three).1 h3Y |>.resolve_right hidx
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hTW
  have hkodd : ¬ 2 ∣ k := by
    intro h2
    apply hTt.2.2
    have h1 : Nat.card ↥W ∣ Nat.card I := Subgroup.card_subgroup_dvd_card W
    rw [hk, ← Tt.card_mul_index] at h1
    have h0 : 0 < Nat.card ↥Tt := Nat.card_pos
    have h3 := Nat.dvd_of_mul_dvd_mul_left h0 h1
    show 2 ∣ Tt.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h2.trans h3
  have hk3 : ∀ {d : ℕ}, d.Prime → d ∣ k → d = 3 := by
    intro d hd hdk
    have hdW : d ∣ Nat.card ↥W' := by
      rw [← hWcard, hk]
      exact Dvd.dvd.mul_left hdk _
    have hmem := hW'.p_in_pi_of_p_dvd_card ⟨d, hd⟩ hdW
    rcases hmem with h | h
    · have : d = 2 := congrArg Subtype.val h
      subst this
      exact absurd hdk hkodd
    · exact congrArg Subtype.val h
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact (Nat.card_pos (α := ↥W)).ne' hk
  set c := k.primeFactorsList.length with hc
  have hkc : k = 3 ^ c := Nat.eq_prime_pow_of_unique_prime_dvd hk0 hk3
  have hc1 : c = 1 := by
    rcases Nat.lt_or_ge c 2 with hlt | hge
    · interval_cases c
      · exfalso
        rw [hkc, pow_zero, mul_one] at hk
        obtain ⟨a, ha⟩ := hTt2.exists_card_eq
        rw [hk, ha] at h3W
        exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
          (Nat.prime_three.dvd_of_dvd_pow h3W)) (by norm_num)
      · rfl
    · exfalso
      have h9 : 3 ^ 2 ∣ Nat.card ↥W := by
        rw [hk, hkc]
        exact Dvd.dvd.mul_left (pow_dvd_pow 3 hge) _
      obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
      have hP3 : IsPGroup 3 ↥(P.map W.subtype) := by
        refine IsPGroup.of_card (n := 2) ?_
        rw [Subgroup.card_map_of_injective W.subtype_injective, hP]
      have hPY : P.map W.subtype ≤ Y := (Subgroup.map_subtype_le P).trans hWY
      have hle := card_le_three_of_isPGroup hN3 hZn hZc3 hTb2 hP3 hPY
      rw [Subgroup.card_map_of_injective W.subtype_injective, hP] at hle
      norm_num at hle
  refine ⟨W, hTW, ?_, hWY, ?_⟩
  · rw [hk, hkc, hc1, pow_one, mul_comm]
  · exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hWY)

end HallW

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_F0 {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hL1 : S.L1 ≤ Subgroup.centralizer (S.UH H : Set G)) :
    ∃ F : ↥(S.H0 H) →* Equiv.Perm (Fin 3),
      (∀ g : ↥(S.H0 H), F g = 1 ↔ (g : G) ∈ Subgroup.centralizer (S.UH H : Set G)) ∧
      Function.Surjective F := by
  classical
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨-, hUel, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hHN : H ≤ Subgroup.normalizer (S.UH H : Set G) := hUred.2.1
  have hIN : S.H0 H ≤ Subgroup.normalizer (S.UH H : Set G) := by
    refine (le_of_eq (S.H0_eq_sup hTH)).trans ?_
    exact sup_le (sup_le (hL1.trans (Subgroup.centralizer_le_normalizer _)) (hTH.trans hHN)) hHN
  obtain ⟨eS3⟩ := hS3
  have e3 : ↥(autI hUel H) ≃* Equiv.Perm (Fin 3) := eS3
  set f : ↥(S.H0 H) →* MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) H) hUel) :=
    convHom hUel (S.H0 H) hIN with hf
  have hfmem : ∀ g : ↥(S.H0 H), f g ∈ autI hUel H := by
    have hle : S.H0 H ≤ ((autI hUel H).comap f).map (S.H0 H).subtype := by
      refine (le_of_eq (S.H0_eq_sup hTH)).trans (sup_le (sup_le ?_ ?_) ?_)
      · intro l hl
        refine ⟨⟨l, Subgroup.mem_sup_left (S.L1_le_borel_L hl)⟩, ?_, rfl⟩
        show f ⟨l, Subgroup.mem_sup_left (S.L1_le_borel_L hl)⟩ ∈ autI hUel H
        have h1 : f ⟨l, Subgroup.mem_sup_left (S.L1_le_borel_L hl)⟩ =
            convI hUel ⟨l, hIN (Subgroup.mem_sup_left (S.L1_le_borel_L hl))⟩ := rfl
        rw [h1, (convI_eq_one_iff hUel _).2 (hL1 hl)]
        exact Subgroup.one_mem _
      · intro t ht
        exact ⟨⟨t, Subgroup.mem_sup_right (hTH ht)⟩,
          convI_mem_autI hUel (hTH ht) (hIN (Subgroup.mem_sup_right (hTH ht))), rfl⟩
      · intro h hh
        exact ⟨⟨h, Subgroup.mem_sup_right hh⟩,
          convI_mem_autI hUel hh (hIN (Subgroup.mem_sup_right hh)), rfl⟩
    intro g
    obtain ⟨w, hw, hwg⟩ := hle g.2
    have : w = g := Subtype.ext hwg
    rw [← this]
    exact hw
  set F : ↥(S.H0 H) →* Equiv.Perm (Fin 3) :=
    e3.toMonoidHom.comp (f.codRestrict (autI hUel H) hfmem) with hFdef
  refine ⟨F, fun g => ?_, fun σ => ?_⟩
  · have e1 : F g = 1 ↔ f g = 1 := by
      have : F g = e3 (f.codRestrict (autI hUel H) hfmem g) := rfl
      rw [this, MulEquiv.map_eq_one_iff]
      constructor
      · intro h1
        exact congrArg Subtype.val h1
      · intro h1
        exact Subtype.ext h1
    rw [e1]
    have : f g = convI hUel ⟨g, hIN g.2⟩ := rfl
    rw [this]
    exact convI_eq_one_iff hUel _
  · obtain ⟨g, hgH, hg⟩ := (mem_autI hUel).1 (e3.symm σ).2
    refine ⟨⟨g, Subgroup.mem_sup_right hgH⟩, ?_⟩
    have e : f.codRestrict (autI hUel H) hfmem ⟨g, Subgroup.mem_sup_right hgH⟩ = e3.symm σ := by
      apply Subtype.ext
      exact hg
    have : F ⟨g, Subgroup.mem_sup_right hgH⟩ =
        e3 (f.codRestrict (autI hUel H) hfmem ⟨g, Subgroup.mem_sup_right hgH⟩) := rfl
    rw [this, e, MulEquiv.apply_symm_apply]

theorem F0_eq_one_of_mem_pPrimeCore {H : Subgroup G} {F : ↥(S.H0 H) →* Equiv.Perm (Fin 3)}
    (hFs : Function.Surjective F) {x : ↥(S.H0 H)} (hx : x ∈ CFSG.pPrimeCore 3 ↥(S.H0 H)) :
    F x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hno : ∀ y ∈ CFSG.pPrimeCore 3 ↥(S.H0 H), F y ≠ 1 → F y ^ 3 ≠ 1 := by
    intro y hy hy1 hy3
    have h3 : orderOf (F y) = 3 := orderOf_eq_prime hy3 hy1
    have h1 : orderOf (F y) ∣ orderOf y := orderOf_map_dvd F y
    have h2 : orderOf (⟨y, hy⟩ : ↥(CFSG.pPrimeCore 3 ↥(S.H0 H))) ∣
        Nat.card ↥(CFSG.pPrimeCore 3 ↥(S.H0 H)) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h2
    rw [h3] at h1
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
      (h1.trans h2)
  by_contra hx1
  have hx3 := hno x hx hx1
  obtain ⟨hτ3, hτ1⟩ := perm3_conj_mul (F x) hx1 hx3
  obtain ⟨g, hg⟩ := hFs (Equiv.swap 0 1 * Equiv.swap 1 2)
  have hn : (CFSG.pPrimeCore 3 ↥(S.H0 H)).Normal := inferInstance
  have hy : g * x * g⁻¹ * x ∈ CFSG.pPrimeCore 3 ↥(S.H0 H) :=
    Subgroup.mul_mem _ (hn.conj_mem x hx g) hx
  have hFy : F (g * x * g⁻¹ * x) = (Equiv.swap 0 1 * Equiv.swap 1 2) * F x *
      (Equiv.swap 0 1 * Equiv.swap 1 2)⁻¹ * F x := by
    rw [map_mul, map_mul, map_mul, map_inv, hg]
  exact hno _ hy (by rw [hFy]; exact hτ1) (by rw [hFy]; exact hτ3)

theorem F0_eq_one_of_map_mem_K {H : Subgroup G} {F : ↥(S.H0 H) →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ g : ↥(S.H0 H), F g = 1 ↔ (g : G) ∈ Subgroup.centralizer (S.UH H : Set G))
    (hFs : Function.Surjective F) {L' : Subgroup ↥(S.H0 H)}
    (hL'U : L'.map (S.H0 H).subtype ≤ Subgroup.centralizer (S.UH H : Set G)) {g : ↥(S.H0 H)}
    (hg : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) g ∈
      L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))) : F g = 1 := by
  obtain ⟨l, hl, hlg⟩ := hg
  have hn : l⁻¹ * g ∈ CFSG.pPrimeCore 3 ↥(S.H0 H) := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hlg
    exact hlg
  have hFl : F l = 1 := (hF1 l).2 (hL'U ⟨l, hl, rfl⟩)
  have h1 := S.F0_eq_one_of_mem_pPrimeCore hFs hn
  rw [map_mul, map_inv, hFl, inv_one, one_mul] at h1
  exact h1

theorem F0_ne_one_of_map_mem_Zc {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    {K Zc : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))} (hc : S.Case3 H K Zc)
    {F : ↥(S.H0 H) →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ g : ↥(S.H0 H), F g = 1 ↔ (g : G) ∈ Subgroup.centralizer (S.UH H : Set G))
    (hFs : Function.Surjective F) {L' : Subgroup ↥(S.H0 H)}
    (hL'K : L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))) = K)
    (hL'U : L'.map (S.H0 H).subtype ≤ Subgroup.centralizer (S.UH H : Set G)) {d : ↥(S.H0 H)}
    (hd : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) d ∈ Zc)
    (hd1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) d ≠ 1) : F d ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N3 := CFSG.pPrimeCore 3 ↥(S.H0 H) with hN3
  set π := QuotientGroup.mk' N3 with hπ
  intro hFd
  have hall : ∀ g : ↥(S.H0 H), π g ∈ K ⊔ Zc → F g = 1 := by
    intro g hg
    obtain ⟨k, hk, z, hz, hkz⟩ := exists_mul_of_mem_sup_comm hc.comm hg
    have htop : Subgroup.zpowers (⟨π d, hd⟩ : ↥Zc) = ⊤ :=
      zpowers_eq_top_of_prime_card hc.card_Zc
        (fun h => hd1 (by simpa using congrArg Subtype.val h))
    have hmem : (⟨z, hz⟩ : ↥Zc) ∈ Subgroup.zpowers (⟨π d, hd⟩ : ↥Zc) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hzm : z = π (d ^ m) := by
      have := congrArg Subtype.val hm
      simp only [SubgroupClass.coe_zpow] at this
      rw [map_zpow]
      exact this.symm
    obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk'_surjective N3 k
    have hFg₁ : F g₁ = 1 := by
      refine S.F0_eq_one_of_map_mem_K hF1 hFs hL'U ?_
      rw [hL'K]
      show π g₁ ∈ K
      rw [hπ, hg₁]
      exact hk
    have hn : (g₁ * d ^ m)⁻¹ * g ∈ N3 := by
      have h1 : π (g₁ * d ^ m) = π g := by
        rw [map_mul, hkz, ← hzm]
        show π g₁ * z = k * z
        rw [hπ, hg₁]
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h1
      exact QuotientGroup.eq.mp h1
    have h2 := S.F0_eq_one_of_mem_pPrimeCore hFs hn
    rw [map_mul, map_inv, map_mul, map_zpow, hFg₁, hFd, one_zpow, mul_one, inv_one, one_mul] at h2
    exact h2
  apply hHZ
  have hTH : T ≤ H := hH.1.1
  rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_le S.h13.sylow hTH)]
  refine sup_le ?_ (T_le_centralizer_omegaOneCenter T)
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyH, hyo⟩
  have hyI : y ∈ S.H0 H := Subgroup.mem_sup_right hyH
  have hFy : F ⟨y, hyI⟩ = 1 := by
    refine hall _ ?_
    rw [hc.sup_eq]
    exact S.map_mem_twoResidual hyI hyo
  exact Subgroup.centralizer_le (le_conjClosure _ _) ((hF1 _).1 hFy)

theorem not_mem_centralizer_Z_of_F0 {H : Subgroup G}
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    {F : ↥(S.H0 H) →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ g : ↥(S.H0 H), F g = 1 ↔ (g : G) ∈ Subgroup.centralizer (S.UH H : Set G))
    {t₀ : ↥(S.H0 H)} (ht₀ : (t₀ : G) ∈ T) (hFt : F t₀ ≠ 1) {d : ↥(S.H0 H)} (hd1 : F d ≠ 1)
    (hd3 : F d ^ 3 = 1) : (d : G) ∉ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hC
  intro hdZ
  have ht₀Z : (t₀ : G) ∈ C := T_le_centralizer_omegaOneCenter T ht₀
  have hFt2 : F t₀ ^ 2 = 1 := by
    obtain ⟨b, hb⟩ := S.isPGroup_T ⟨t₀, ht₀⟩
    refine perm3_sq_of_two_pow (k := b) ?_
    rw [← map_pow]
    have : t₀ ^ 2 ^ b = 1 := Subtype.ext (by simpa using congrArg Subtype.val hb)
    rw [this, map_one]
  apply hHZ
  intro h hh
  have hhI : h ∈ S.H0 H := Subgroup.mem_sup_right hh
  have key : ∃ w : ↥(S.H0 H), (w : G) ∈ C ∧ F w = F ⟨h, hhI⟩ := by
    rcases perm3_words_gen (F d) (F t₀) (F ⟨h, hhI⟩) hd1 hd3 hFt hFt2 with
      h1 | h1 | h1 | h1 | h1 | h1
    · exact ⟨1, C.one_mem, by rw [map_one, h1]⟩
    · exact ⟨d, hdZ, h1.symm⟩
    · exact ⟨d ^ 2, by simpa using C.pow_mem hdZ 2, by rw [map_pow, h1]⟩
    · exact ⟨t₀, ht₀Z, h1.symm⟩
    · exact ⟨d * t₀, by simpa using C.mul_mem hdZ ht₀Z, by rw [map_mul, h1]⟩
    · exact ⟨d ^ 2 * t₀, by simpa using C.mul_mem (C.pow_mem hdZ 2) ht₀Z,
        by rw [map_mul, map_pow, h1]⟩
  obtain ⟨w, hwC, hFw⟩ := key
  have hc : F (w⁻¹ * ⟨h, hhI⟩) = 1 := by rw [map_mul, map_inv, hFw, inv_mul_cancel]
  have hcC : ((w⁻¹ * ⟨h, hhI⟩ : ↥(S.H0 H)) : G) ∈ C :=
    Subgroup.centralizer_le (le_conjClosure _ _) ((hF1 _).1 hc)
  have e : h = (w : G) * ((w⁻¹ * ⟨h, hhI⟩ : ↥(S.H0 H)) : G) := by simp
  rw [e]
  exact C.mul_mem hwC hcC

theorem exists_T_F0_ne_one (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    {F : ↥(S.H0 H) →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ g : ↥(S.H0 H), F g = 1 ↔ (g : G) ∈ Subgroup.centralizer (S.UH H : Set G)) :
    ∃ t₀ : ↥(S.H0 H), (t₀ : G) ∈ T ∧ F t₀ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  by_contra hall
  push Not at hall
  obtain ⟨hMP, -⟩ := S.hyp501.minParabolic_of_isHStar h331 hH
  apply hMP.not_normal
  have hTO : T ≤ pCoreOf 2 H := by
    intro t ht
    refine S.centralizer_UH_le_pCoreOf h331 h1222 hH hHZ hsolv hS3 ⟨hTH ht, ?_⟩
    exact (hF1 ⟨t, Subgroup.mem_sup_right (hTH ht)⟩).1 (hall _ ht)
  have heq : pCoreOf 2 H = T :=
    le_antisymm (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTH)) hTO
  rw [← heq]
  exact le_normalizer_pCoreOf 2 H

end Setting

end CFSG.Quasithin.H13.A5
