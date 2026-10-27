module

public import CFSG.Quasithin.Background.A4Coprime

public section

namespace CFSG.Quasithin.D14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_commutator {H A B : Subgroup G} (hA : H ≤ Subgroup.normalizer (A : Set G))
    (hB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hg)]

theorem le_normalizer_sup {H A B : Subgroup G} (hA : H ≤ Subgroup.normalizer (A : Set G))
    (hB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hg),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hg)]

theorem commutator_closure_le {S : Set G} {K N : Subgroup G}
    (hSN : Subgroup.closure S ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ s ∈ S, ∀ k ∈ K, ⁅s, k⁆ ∈ N) : ⁅Subgroup.closure S, K⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro x hx k hk
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact h s hs k hk
  | one => simp
  | mul x y hx hy ihx ihy =>
    have e : ⁅x * y, k⁆ = (x * ⁅y, k⁆ * x⁻¹) * ⁅x, k⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSN hx) _).mp ihy) ihx
  | inv x hx ih =>
    have e : ⁅x⁻¹, k⁆ = x⁻¹ * ⁅x, k⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff''.mp (hSN hx) _).mp (N.inv_mem ih)

theorem commutator_le_closure {S : Set G} {K N : Subgroup G}
    (hSN : Subgroup.closure S ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ k ∈ K, ∀ s ∈ S, ⁅k, s⁆ ∈ N) : ⁅K, Subgroup.closure S⁆ ≤ N := by
  rw [Subgroup.commutator_comm]
  refine commutator_closure_le hSN fun s hs k hk => ?_
  have := N.inv_mem (h k hk s hs)
  rwa [commutatorElement_inv] at this

theorem commutator_sup_le_of {W V Q M : Subgroup G} (hWV : W ≤ Subgroup.normalizer (V : Set G))
    (hWM : W ≤ Subgroup.normalizer (M : Set G)) (hV : ⁅V, Q⁆ ≤ M) (hW : ⁅W, Q⁆ ≤ M) :
    ⁅W ⊔ V, Q⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro x hx q hq
  have hx' : x ∈ ((W ⊔ V : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right W V hWV] at hx'
  obtain ⟨w, hw, v, hv, rfl⟩ := hx'
  have e : ⁅w * v, q⁆ = (w * ⁅v, q⁆ * w⁻¹) * ⁅w, q⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact M.mul_mem ((Subgroup.mem_normalizer_iff.mp (hWM hw) _).mp
    (hV (Subgroup.commutator_mem_commutator hv hq))) (hW (Subgroup.commutator_mem_commutator hw hq))

theorem commutator_sup_le {W V Q : Subgroup G} (hWV : W ≤ Subgroup.normalizer (V : Set G))
    (hQV : Q ≤ Subgroup.normalizer (V : Set G)) : ⁅W ⊔ V, Q⁆ ≤ ⁅W, Q⁆ ⊔ V := by
  rw [Subgroup.commutator_le]
  intro x hx q hq
  have hx' : x ∈ ((W ⊔ V : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right W V hWV] at hx'
  obtain ⟨w, hw, v, hv, rfl⟩ := hx'
  have e : ⁅w * v, q⁆ = (w * ⁅v, q⁆ * w⁻¹) * ⁅w, q⁆ := by
    simp only [commutatorElement_def]
    group
  have hvq : ⁅v, q⁆ ∈ V := by
    have e' : ⁅v, q⁆ = v * (q * v⁻¹ * q⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e']
    exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hQV hq) _).mp (V.inv_mem hv))
  rw [e]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hWV hw) _).mp hvq))
    (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hw hq))

theorem oTwoUpper_oTwoUpper (H : Subgroup G) : oTwoUpper (oTwoUpper H) = oTwoUpper H := by
  refine le_antisymm (oTwoUpper_le _) ?_
  show Subgroup.closure {x | x ∈ H ∧ Odd (orderOf x)} ≤ _
  rw [Subgroup.closure_le]
  rintro x ⟨hx, ho⟩
  exact mem_oTwoUpper_of_odd (mem_oTwoUpper_of_odd hx ho) ho

theorem commutator_le_commutator_commutator {H W : Subgroup G} (hW : IsPGroup 2 W) (hWH : W ≤ H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) :
    ⁅W, oTwoUpper H⁆ ≤ ⁅⁅W, oTwoUpper H⁆, oTwoUpper H⁆ := by
  set P := oTwoUpper H with hP
  have hPH : P ≤ H := oTwoUpper_le H
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := le_normalizer_oTwoUpper H
  have hHN : H ≤ Subgroup.normalizer ((⁅⁅W, P⁆, P⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator (le_normalizer_commutator hHW hHP) hHP
  have key := A4.commutator_le_of_oTwoUpper (A := P) (N := ⁅⁅W, P⁆, P⁆) (B := ⁅W, P⁆) (D := W)
    (hPH.trans hHN) (hWH.trans hHN)
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hPH.trans hHW))
    (fun d hd => by
      obtain ⟨j, hj⟩ := hW ⟨d, hd⟩
      refine ⟨j, ?_⟩
      have hj' : d ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      rw [hj']
      exact Subgroup.one_mem _)
    (Subgroup.commutator_comm P W).le (Subgroup.commutator_comm P ⁅W, P⁆).le
  rw [hP, oTwoUpper_oTwoUpper, ← hP, Subgroup.commutator_comm] at key
  exact key

theorem exists_fixed_of_lt [Finite G] {T K L : Subgroup G} (hT : IsPGroup 2 T) (hKT : K ≤ T)
    (hLK : L < K) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ x ∈ K, x ∉ L ∧ ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn : (L.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTL
  have hKn : (K.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTK
  set π := QuotientGroup.mk' (L.subgroupOf T) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ y : T, π y = 1 ↔ (y : G) ∈ L := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hnil : Group.IsNilpotent (↥T ⧸ L.subgroupOf T) := (hT.to_quotient _).isNilpotent
  have hKbn : ((K.subgroupOf T).map π).Normal := hKn.map π hπs
  have hne : (K.subgroupOf T).map π ≠ ⊥ := by
    obtain ⟨k, hkK, hkL⟩ := IsConcreteLE.exists_of_lt hLK
    intro hbot
    have hk : π ⟨k, hKT hkK⟩ ∈ (K.subgroupOf T).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hkK)
    rw [hbot, Subgroup.mem_bot, hker] at hk
    exact hkL hk
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp z.2).1
  have hzc := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp z.2).2
  refine ⟨y, Subgroup.mem_subgroupOf.mp hy, fun hyL => hz1 ?_, fun t ht => ?_⟩
  · apply Subtype.ext
    rw [← hyz]
    exact (hker y).mpr hyL
  · have h1 := hzc (π ⟨t, ht⟩)
    rw [← hyz] at h1
    have h2 : π (⟨t, ht⟩ * y * ⟨t, ht⟩⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    exact (hker _).mp h2

theorem le_of_le_commutator_sup [Finite G] {Q U V : Subgroup G} (hQ : IsPGroup 2 Q)
    (hUQ : U ≤ Q) (hQV : Q ≤ Subgroup.normalizer (V : Set G)) (h : U ≤ ⁅U, Q⁆ ⊔ V) : U ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hQ.isNilpotent
  set γ : ℕ → Subgroup G := fun k => ((⊤ : Subgroup ↥Q).lowerCentralSeries k).map Q.subtype
    with hγ
  have hQtop : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hγQ : ∀ k, γ k ≤ Q := fun k => Subgroup.map_subtype_le _
  have hγsucc : ∀ k, γ (k + 1) = ⁅γ k, Q⁆ := by
    intro k
    simp only [hγ, Subgroup.lowerCentralSeries_succ, Subgroup.map_commutator, hQtop]
  have key : ∀ k, U ≤ γ k ⊔ V := by
    intro k
    induction k with
    | zero =>
      simp only [hγ, Subgroup.lowerCentralSeries_zero, hQtop]
      exact hUQ.trans le_sup_left
    | succ k ih =>
      calc U ≤ ⁅U, Q⁆ ⊔ V := h
        _ ≤ ⁅γ k ⊔ V, Q⁆ ⊔ V := sup_le_sup_right (Subgroup.commutator_mono ih le_rfl) V
        _ ≤ (⁅γ k, Q⁆ ⊔ V) ⊔ V :=
          sup_le_sup_right (commutator_sup_le ((hγQ k).trans hQV) hQV) V
        _ = γ (k + 1) ⊔ V := by rw [hγsucc, sup_assoc, sup_idem]
  have hU := key c
  simp only [hγ, hc, Subgroup.map_bot, bot_sup_eq] at hU
  exact hU

theorem pow_oddPart_eq_one [Finite G] {x : G} (hx : Odd (orderOf x)) :
    x ^ (Nat.card G / 2 ^ (Nat.card G).factorization 2) = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  have h1 : orderOf x ∣ 2 ^ (Nat.card G).factorization 2 *
      (Nat.card G / 2 ^ (Nat.card G).factorization 2) := by
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    exact orderOf_dvd_natCard x
  have hcop : Nat.Coprime (orderOf x) (2 ^ (Nat.card G).factorization 2) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hx)
  exact hcop.dvd_of_dvd_mul_left h1

theorem not_two_dvd_oddPart [Finite G] :
    ¬ 2 ∣ Nat.card G / 2 ^ (Nat.card G).factorization 2 :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
    (Nat.coprime_ordCompl Nat.prime_two Nat.card_pos.ne')

open scoped IsMulCommutative in
theorem le_of_commutator_le [Finite G] {H S N : Subgroup G} (hS : IsSylowTwoOf S (oTwoUpper H))
    (hN : oTwoUpper H ≤ Subgroup.normalizer (N : Set G)) (hSN : ⁅S, oTwoUpper H⁆ ≤ N) :
    S ≤ N := by
  set P := oTwoUpper H with hP
  have hNn : (N.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  set π := QuotientGroup.mk' (N.subgroupOf P) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ y : P, π y = 1 ↔ (y : G) ∈ N := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcent : (S.subgroupOf P).map π ≤ Subgroup.center (↥P ⧸ N.subgroupOf P) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨x, rfl⟩ := hπs z
    have hc : ((x * s * x⁻¹ * s⁻¹ : P) : G) ∈ N := by
      have h1 : ⁅(s : G), (x : G)⁆ ∈ N :=
        hSN (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hs) x.2)
      have h2 := N.inv_mem h1
      rw [commutatorElement_inv, commutatorElement_def] at h2
      simpa using h2
    have h1 : π (x * s * x⁻¹ * s⁻¹) = 1 := (hker _).mpr hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π x * π s = (π x * π s * (π x)⁻¹ * (π s)⁻¹) * (π s * π x) := by group
      _ = π s * π x := by rw [h1, one_mul]
  have hodd : ¬ 2 ∣ (Subgroup.center (↥P ⧸ N.subgroupOf P)).index := by
    intro h2
    apply hS.2.2
    have h3 : (Subgroup.center (↥P ⧸ N.subgroupOf P)).index ∣ ((S.subgroupOf P).map π).index :=
      Subgroup.index_dvd_of_le hcent
    have h4 : (((S.subgroupOf P).map π).comap π).index = ((S.subgroupOf P).map π).index :=
      Subgroup.index_comap_of_surjective _ hπs
    have h5 : (((S.subgroupOf P).map π).comap π).index ∣ (S.subgroupOf P).index :=
      Subgroup.index_dvd_of_le (Subgroup.le_comap_map π _)
    rw [h4] at h5
    exact h2.trans (h3.trans h5)
  set n := (Subgroup.center (↥P ⧸ N.subgroupOf P)).index with hn
  set m := Nat.card G / 2 ^ (Nat.card G).factorization 2 with hm
  set φ := (powMonoidHom m).comp (MonoidHom.transferCenterPow (↥P ⧸ N.subgroupOf P)) with hφ
  have hφapp : ∀ z, ((φ z : Subgroup.center (↥P ⧸ N.subgroupOf P)) : ↥P ⧸ N.subgroupOf P) =
      (z ^ n) ^ m := fun z => by
    rw [hφ, MonoidHom.comp_apply, powMonoidHom_apply, Subgroup.coe_pow,
      MonoidHom.transferCenterPow_apply]
  have htriv : ∀ y : P, φ (π y) = 1 := by
    have hcl : Subgroup.closure (((↑) : P → G) ⁻¹' {x | x ∈ H ∧ Odd (orderOf x)}) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    have hle : Subgroup.closure (((↑) : P → G) ⁻¹' {x | x ∈ H ∧ Odd (orderOf x)}) ≤
        (φ.comp π).ker := by
      rw [Subgroup.closure_le]
      intro y hy
      have hy1 : y ^ m = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact pow_oddPart_eq_one hy.2)
      rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
      apply Subtype.ext
      rw [hφapp, Subgroup.coe_one, ← pow_mul, mul_comm, pow_mul, ← map_pow, hy1, map_one,
        one_pow]
    intro y
    have := hle (hcl ▸ Subgroup.mem_top y)
    exact this
  intro s hs
  have hsP : s ∈ P := hS.1 hs
  obtain ⟨b, hb⟩ := hS.2.1 ⟨s, hs⟩
  have hb' : s ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  set y : P := ⟨s, hsP⟩ with hy
  have hy2 : (π y) ^ 2 ^ b = 1 := by
    rw [← map_pow]
    have : y ^ 2 ^ b = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hy]; exact hb')
    rw [this, map_one]
  have hynm : (π y) ^ (n * m) = 1 := by
    rw [pow_mul, ← hφapp, htriv y]
    rfl
  have hnm : ¬ 2 ∣ n * m := fun h2 =>
    (Nat.Prime.dvd_mul Nat.prime_two).mp h2 |>.elim hodd not_two_dvd_oddPart
  have hcop : Nat.Coprime (2 ^ b) (n * m) :=
    Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnm)
  have hord : orderOf (π y) = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hy2) (orderOf_dvd_of_pow_eq_one hynm)
  exact (hker y).mp (orderOf_eq_one_iff.mp hord)

end CFSG.Quasithin.D14
