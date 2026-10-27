module

public import CFSG.Quasithin.Background.E2Seventeen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

namespace DihedralPair

variable {G : Type*} [Group G] [Finite G] {H T V U : Subgroup G} {x z : G}

omit [Finite G] in
theorem zpow_U (d : DihedralPair H T V U x z) (k : ℕ) :
    ∀ u ∈ U, z ^ k * u * (z ^ k)⁻¹ * u⁻¹ ∈ pCoreOf 2 H := by
  induction k with
  | zero => intro u _; simp
  | succ k ih =>
    intro u hu
    have h1 := ih u hu
    have h2 := d.zU u hu
    have h3 : z * (z ^ k * u * (z ^ k)⁻¹ * u⁻¹) * z⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp d.zN _).mp h1
    have e : z ^ (k + 1) * u * (z ^ (k + 1))⁻¹ * u⁻¹ =
        (z * (z ^ k * u * (z ^ k)⁻¹ * u⁻¹) * z⁻¹) * (z * u * z⁻¹ * u⁻¹) := by
      rw [pow_succ']
      group
    rw [e]
    exact (pCoreOf 2 H).mul_mem h3 h2

omit [Finite G] in
theorem pow (d : DihedralPair H T V U x z) (k : ℕ) (hk : z ^ k ≠ 1) :
    DihedralPair H T V U x (z ^ k) := by
  refine ⟨d.T2, d.TH, d.QT, d.char, d.VT, d.TV, d.elem, d.UV, d.VQU, d.xV, d.xU, d.U2,
    H.pow_mem d.zH k, ?_, hk, ?_, d.zpow_U k⟩
  · exact Odd.of_dvd_nat d.zodd (orderOf_pow_dvd k)
  · exact conj_eq_inv_of_mem_zpowers d.xz (Subgroup.npow_mem_zpowers z k)

theorem exists_prime_orderOf (d : DihedralPair H T V U x z) :
    ∃ z' ∈ Subgroup.zpowers z, (orderOf z').Prime ∧ DihedralPair H T V U x z' := by
  have hn1 : orderOf z ≠ 1 := fun h => d.z1 (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
  obtain ⟨m, hm⟩ := hpn
  have hpos : 0 < orderOf z := orderOf_pos z
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have hord : orderOf (z ^ m) = p := by
    rw [orderOf_pow' z hm0.ne', hm, Nat.gcd_mul_left_left]
    exact Nat.mul_div_cancel _ hm0
  have hz1 : z ^ m ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne' hord.symm
  exact ⟨z ^ m, Subgroup.npow_mem_zpowers z m, hord ▸ hp, d.pow m hz1⟩

theorem swap_U (d : DihedralPair H T V U x z) : cjSub (z * x) U = dpA H V U z := by
  have hxU : x ∈ Subgroup.normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun u hu => isElemAbelian_comm d.elem (d.UV hu) d.xV)
  rw [cjSub_mul, cjSub_eq_of_mem_normalizer hxU, d.Aeq]

theorem swap_A (d : DihedralPair H T V U x z) : cjSub (z * x) (dpA H V U z) = U := by
  have hxU : x ∈ Subgroup.normalizer (U : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.2 fun u hu => isElemAbelian_comm d.elem (d.UV hu) d.xV)
  have h1 : x * z = z⁻¹ * x := by
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z⁻¹ * x := by rw [d.xz]
  rw [d.Aeq, ← cjSub_mul, show z * x * z = z * (x * z) by group, h1,
    show z * (z⁻¹ * x) = x by group, cjSub_eq_of_mem_normalizer hxU]

theorem zxI (d : DihedralPair H T V U x z) : z * x ∈ dpI V z :=
  (dpI V z).mul_mem d.zI (Subgroup.mem_sup_left d.xV)

theorem U_inf_A (d : DihedralPair H T V U x z) : U ⊓ dpA H V U z = dpZ V z :=
  le_antisymm (fun _ hg => ⟨d.UV hg.1, d.AVz hg.2⟩) (le_inf d.ZU d.ZA)

theorem A_inf_centralizer_U (d : DihedralPair H T V U x z)
    (h : U ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z) :
    dpA H V U z ⊓ Subgroup.centralizer (U : Set G) = dpZ V z := by
  have hZ : cjSub (z * x) (dpZ V z) = dpZ V z :=
    cjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun ζ hζ => (d.ZC ζ hζ _ d.zxI).symm))
  have := congrArg (cjSub (z * x)) h
  rw [cjSub_inf, cjSub_centralizer, d.swap_U, d.swap_A, hZ] at this
  exact this

theorem UN_A (d : DihedralPair H T V U x z) :
    U ≤ Subgroup.normalizer (dpA H V U z : Set G) := by
  have key : ∀ u ∈ U, ∀ b ∈ dpA H V U z, u * b * u⁻¹ ∈ dpA H V U z := by
    intro u hu b hb
    have h1 : u * b * u⁻¹ * b⁻¹ ∈ dpZ V z := by
      have := Subgroup.commutator_mem_commutator hu hb
      rw [commutatorElement_def] at this
      exact d.comm2 this
    have e : u * b * u⁻¹ = (u * b * u⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact (dpA H V U z).mul_mem (d.ZA h1) hb
  exact fun u hu => B6.mem_normalizer_of_forall_mem (key u hu)
    (fun b hb => by simpa using key u⁻¹ (U.inv_mem hu) b hb)

theorem mem_P (d : DihedralPair H T V U x z) {g : G} (hg : g ∈ dpP H V U z) :
    ∃ u ∈ U, ∃ a ∈ dpA H V U z, u * a = g := by
  have hg' : g ∈ ((U ⊔ dpA H V U z : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ d.UN_A] at hg'
  obtain ⟨u, hu, a, ha, rfl⟩ := hg'
  exact ⟨u, hu, a, ha, rfl⟩

theorem card_P (d : DihedralPair H T V U x z) :
    Nat.card (dpP H V U z) = (dpZ V z).relIndex U * Nat.card (dpA H V U z) := by
  have h1 := Subgroup.relIndex_mul_card (dpA H V U z) (dpP H V U z)
  rw [inf_eq_left.2 (le_sup_right : dpA H V U z ≤ dpP H V U z)] at h1
  rw [← h1, dpP, relIndex_sup_eq_of_le_normalizer' d.UN_A, ← d.U_inf_A,
    Subgroup.inf_relIndex_left]

theorem counts (d : DihedralPair H T V U x z) (hV16 : Nat.card V = 2 ^ 4)
    (hr : ((dpA H V U z ⊓ Subgroup.centralizer (V : Set G)).relIndex (dpA H V U z)) ^ 3 ≤
      ((V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V) ^ 2) :
    (dpZ V z).relIndex (dpA H V U z) = 4 ∧ Nat.card (dpZ V z) = 2 ∧
      V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z := by
  rw [d.ACV] at hr
  set n := (dpZ V z).relIndex (dpA H V U z) with hn
  set m := (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V with hm
  have hn0 := d.relIndex_ne_zero
  have hn1 := d.relIndex_ne_one
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian d.Ael)
  have hnd : n ∣ 2 ^ k := hk ▸ Dvd.intro _ d.nZ
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hnd
  have hn2 : n ≠ 2 := by
    intro h2
    have hm2 : m ≤ 2 := d.relIndex_le_two_of_le (d.le_centralizer_of_relIndex_eq_two h2)
    rw [h2] at hr
    have h3 : m ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hm2 2
    have : 2 ^ 3 ≤ 2 ^ 2 := hr.trans h3
    norm_num at this
  have hn4 : 4 ≤ n := by
    rcases i with _ | _ | i
    · simp at hi
      exact absurd hi hn1
    · simp at hi
      exact absurd hi hn2
    · rw [hi, pow_succ, pow_succ]
      have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      omega
  have hZ2 : 2 ≤ Nat.card (dpZ V z) := by
    by_contra hlt
    push Not at hlt
    have hZ1 : dpZ V z = ⊥ := by
      rw [← Subgroup.card_eq_one]
      have := Nat.card_pos (α := dpZ V z)
      omega
    obtain ⟨-, hq⟩ := d.quad hZ1
    rw [d.ACV] at hq
    have : n ^ 3 ≤ n ^ 2 := hr.trans (Nat.pow_le_pow_left hq 2)
    have h4 : 4 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn4 3
    nlinarith
  have h8 : n * Nat.card (dpZ V z) = 8 := by
    have h1 := d.nZ
    rw [d.cardA] at h1
    have h2 := d.cardV
    rw [hV16] at h2
    norm_num at h2
    rw [h1]
    omega
  have hn4' : n = 4 := by
    have : n ≤ 4 := by nlinarith
    omega
  have hZ : Nat.card (dpZ V z) = 2 := by
    rw [hn4'] at h8
    omega
  refine ⟨hn4', hZ, ?_⟩
  have hm8 : 8 ≤ m := by
    rw [hn4'] at hr
    nlinarith
  have hmV := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (dpA H V U z : Set G)) V
  rw [inf_eq_left.2 inf_le_left, hV16] at hmV
  have hZVA : dpZ V z ≤ V ⊓ Subgroup.centralizer (dpA H V U z : Set G) := fun w hw =>
    ⟨hw.1, Subgroup.mem_centralizer_iff.2 fun a ha => isElemAbelian_comm d.Vzel (d.AVz ha) hw.2⟩
  refine (Subgroup.eq_of_le_of_card_ge hZVA ?_).symm
  have hpos : 0 < Nat.card ↥(V ⊓ Subgroup.centralizer (dpA H V U z : Set G)) := Nat.card_pos
  rw [hZ]
  nlinarith

theorem comm_AU (d : DihedralPair H T V U x z) {a u : G} (ha : a ∈ dpA H V U z) (hu : u ∈ U) :
    a * u * a⁻¹ * u⁻¹ ∈ dpZ V z := by
  have := Subgroup.commutator_mem_commutator hu ha
  rw [commutatorElement_def] at this
  have h1 := (dpZ V z).inv_mem (d.comm2 this)
  have e : a * u * a⁻¹ * u⁻¹ = (u * a * u⁻¹ * a⁻¹)⁻¹ := by group
  rw [e]
  exact h1

theorem comm_mem_Z (d : DihedralPair H T V U x z) {g h : G} (hg : g ∈ dpP H V U z)
    (hh : h ∈ dpP H V U z) : g * h * g⁻¹ * h⁻¹ ∈ dpZ V z := by
  obtain ⟨u, hu, a, ha, rfl⟩ := d.mem_P hg
  obtain ⟨u', hu', a', ha', rfl⟩ := d.mem_P hh
  set c₁ := a * u' * a⁻¹ * u'⁻¹ with hc₁
  set c₂ := a' * u * a'⁻¹ * u⁻¹ with hc₂
  have h1 : c₁ ∈ dpZ V z := d.comm_AU ha hu'
  have h2 : c₂ ∈ dpZ V z := d.comm_AU ha' hu
  have hI : ∀ {y : G}, y ∈ dpP H V U z → y ∈ dpI V z := fun hy =>
    (d.PR.trans inf_le_left) hy
  have huu : u * u' = u' * u := isElemAbelian_comm d.elem (d.UV hu) (d.UV hu')
  have haa : a * a' = a' * a := isElemAbelian_comm d.Ael ha ha'
  have e1 : u * a * (u' * a') = c₁ * (u * u' * (a * a')) := by
    have hc : u * c₁ = c₁ * u := (d.ZC c₁ h1 u (hI (Subgroup.mem_sup_left hu)))
    calc u * a * (u' * a') = u * (a * u' * a⁻¹ * u'⁻¹) * (u' * a) * a' := by group
      _ = c₁ * u * (u' * a) * a' := by rw [← hc₁, hc]
      _ = c₁ * (u * u' * (a * a')) := by group
  have e2 : u' * a' * (u * a) = c₂ * (u * u' * (a * a')) := by
    have hc : u' * c₂ = c₂ * u' := (d.ZC c₂ h2 u' (hI (Subgroup.mem_sup_left hu')))
    calc u' * a' * (u * a) = u' * (a' * u * a'⁻¹ * u⁻¹) * (u * a') * a := by group
      _ = c₂ * u' * (u * a') * a := by rw [← hc₂, hc]
      _ = c₂ * (u' * u * (a' * a)) := by group
      _ = c₂ * (u * u' * (a * a')) := by rw [huu, haa]
  have e : u * a * (u' * a') * (u * a)⁻¹ * (u' * a')⁻¹ =
      (u * a * (u' * a')) * (u' * a' * (u * a))⁻¹ := by group
  rw [e, e1, e2]
  have : c₁ * (u * u' * (a * a')) * (c₂ * (u * u' * (a * a')))⁻¹ = c₁ * c₂⁻¹ := by group
  rw [this]
  exact (dpZ V z).mul_mem h1 ((dpZ V z).inv_mem h2)

theorem sq_mem_Z (d : DihedralPair H T V U x z) {g : G} (hg : g ∈ dpP H V U z) :
    g * g ∈ dpZ V z := by
  obtain ⟨u, hu, a, ha, rfl⟩ := d.mem_P hg
  have hu2 : u * u = 1 := by simpa [pow_two] using d.elem.2 u (d.UV hu)
  have ha2 : a * a = 1 := by simpa [pow_two] using d.Ael.2 a ha
  have h1 := d.comm2 (by
    have := Subgroup.commutator_mem_commutator hu ha
    rwa [commutatorElement_def] at this)
  have e : u * a * (u * a) = (u * a * u⁻¹ * a⁻¹) * (a * (u * u) * a) := by group
  rw [e, hu2, mul_one, ha2, mul_one]
  exact h1

theorem U_inf_centralizer (d : DihedralPair H T V U x z)
    (h : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z) :
    U ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z :=
  le_antisymm (h ▸ inf_le_inf_right _ d.UV) (le_inf d.ZU (h ▸ inf_le_right))

theorem mem_Z_of_comm (d : DihedralPair H T V U x z)
    (h : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z) {c : G}
    (hc : c ∈ dpP H V U z) (hcomm : ∀ g ∈ dpP H V U z, g * c = c * g) : c ∈ dpZ V z := by
  have hU := d.U_inf_centralizer h
  have hA := d.A_inf_centralizer_U hU
  obtain ⟨u, hu, a, ha, rfl⟩ := d.mem_P hc
  have haC : a ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u' hu'
    have h1 := hcomm u' (Subgroup.mem_sup_left hu')
    have huu : u' * u = u * u' := isElemAbelian_comm d.elem (d.UV hu') (d.UV hu)
    calc u' * a = u⁻¹ * ((u' * u) * a) := by rw [huu]; group
      _ = u⁻¹ * (u' * (u * a)) := by group
      _ = u⁻¹ * (u * a * u') := by rw [h1]
      _ = a * u' := by group
  have huC : u ∈ Subgroup.centralizer (dpA H V U z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a' ha'
    have h1 := hcomm a' (Subgroup.mem_sup_right ha')
    have haa : a * a' = a' * a := isElemAbelian_comm d.Ael ha ha'
    calc a' * u = (a' * (u * a)) * a⁻¹ := by group
      _ = (u * a * a') * a⁻¹ := by rw [h1]
      _ = (u * (a * a')) * a⁻¹ := by group
      _ = (u * (a' * a)) * a⁻¹ := by rw [haa]
      _ = u * a' := by group
  have hu' : u ∈ dpZ V z := hU ▸ ⟨hu, huC⟩
  have ha' : a ∈ dpZ V z := hA ▸ ⟨ha, haC⟩
  exact (dpZ V z).mul_mem hu' ha'

theorem isExtraspecialPlus (d : DihedralPair H T V U x z) (hV16 : Nat.card V = 2 ^ 4)
    (hZ2 : Nat.card (dpZ V z) = 2)
    (hCA : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z) :
    IsExtraspecialPlus 2 (dpP H V U z) := by
  set P := dpP H V U z with hP
  set Z := dpZ V z with hZ
  have hZP : Z ≤ P := d.ZU.trans le_sup_left
  have hUcard : Nat.card U = 8 := by
    have := d.cardV
    rw [hV16] at this
    omega
  have hPI : P ≤ dpI V z := d.PR.trans inf_le_left
  have hcen : Subgroup.center ↥P = Z.subgroupOf P := by
    ext c
    rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact d.mem_Z_of_comm hCA c.2 (fun g hg => congrArg Subtype.val (h ⟨g, hg⟩))
    · intro hcZ g
      exact Subtype.ext (d.ZC c hcZ g (hPI g.2))
  have hZcard : Nat.card ↥(Subgroup.center ↥P) = 2 := by
    rw [hcen, ← hZ2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv
  have hrel : Z.relIndex U = 4 := by
    have h1 := Subgroup.relIndex_mul_card Z U
    rw [inf_eq_left.2 d.ZU, hZ2, hUcard] at h1
    omega
  have hPcard : Nat.card P = 2 ^ (1 + 2 * 2) := by
    rw [hP, d.card_P, hrel, d.cardA, hUcard]
    norm_num
  have hEA : IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => ?_ }
    · induction a using QuotientGroup.induction_on with
      | H g =>
      induction b using QuotientGroup.induction_on with
      | H h =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hcen,
        Subgroup.mem_subgroupOf]
      have := d.comm_mem_Z (P.inv_mem h.2) (P.inv_mem g.2)
      have e : (((g * h)⁻¹ * (h * g) : ↥P) : G) = (h : G)⁻¹ * (g : G)⁻¹ * (h : G)⁻¹⁻¹ *
          (g : G)⁻¹⁻¹ := by simp [mul_assoc]
      rw [e]
      exact this
    · induction a using QuotientGroup.induction_on with
      | H g =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hcen, Subgroup.mem_subgroupOf]
      have h1 : ((g ^ 2 : ↥P) : G) = (g : G) * (g : G) := by simp [pow_two]
      rw [h1]
      exact d.sq_mem_Z g.2
  have hnt : Nontrivial (↥P ⧸ Subgroup.center ↥P) := by
    have hZlt : Z < U := lt_of_le_of_ne d.ZU fun h => by
      have h1 : Nat.card Z = Nat.card U := by rw [h]
      rw [hZ2, hUcard] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨u, hu, huZ⟩ := IsConcreteLE.exists_of_lt hZlt
    refine nontrivial_of_ne ((⟨u, Subgroup.mem_sup_left hu⟩ : ↥P) : ↥P ⧸ Subgroup.center ↥P) 1
      fun h => huZ ?_
    rw [QuotientGroup.eq_one_iff, hcen, Subgroup.mem_subgroupOf] at h
    exact h
  refine ⟨⟨hZcard, hEA, hnt⟩, hPcard, U, le_sup_left, isElemAbelian_mono d.UV d.elem, ?_⟩
  rw [hUcard]
  norm_num

theorem inf_cjSub_pow_le (d : DihedralPair H T V U x z) (hp : (orderOf z).Prime)
    (hCA : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z) {k : ℕ} (hk0 : 0 < k)
    (hkp : k < orderOf z) : U ⊓ cjSub (z ^ k) U ≤ dpZ V z := by
  have hzk : z ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0.ne' hkp
  have dk := d.pow k hzk
  have hordk : orderOf (z ^ k) = orderOf z := by
    have h1 : orderOf (z ^ k) ∣ orderOf z := orderOf_pow_dvd k
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hzk
    · exact h
  have hzmem : z ∈ Subgroup.zpowers (z ^ k) := by
    have hle : Subgroup.zpowers (z ^ k) ≤ Subgroup.zpowers z :=
      Subgroup.zpowers_le.2 (Subgroup.npow_mem_zpowers z k)
    have heq : Subgroup.zpowers (z ^ k) = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hordk])
    rw [heq]
    exact Subgroup.mem_zpowers z
  have hzI : z ∈ dpI V (z ^ k) := Subgroup.zpowers_le.2 dk.zI hzmem
  rintro w ⟨hwU, hwk⟩
  have hwV : w ∈ V := d.UV hwU
  have hwVk : w ∈ cjSub (z ^ k) V := cjSub_mono d.UV hwk
  have hwC : w ∈ Subgroup.centralizer (dpI V (z ^ k) : Set G) := mem_centralizer_sup
    (Subgroup.mem_centralizer_iff.2 fun v hv => isElemAbelian_comm d.elem hv hwV)
    (Subgroup.mem_centralizer_iff.2 fun v hv => isElemAbelian_comm dk.Vzel hv hwVk)
  rw [← hCA]
  refine ⟨hwV, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
  have haV : z⁻¹ * a * z ∈ V := mem_cjSub.1 (d.AVz ha)
  have haI : a ∈ dpI V (z ^ k) := by
    have e : a = z * (z⁻¹ * a * z) * z⁻¹ := by group
    rw [e]
    exact (dpI V (z ^ k)).mul_mem ((dpI V (z ^ k)).mul_mem hzI (Subgroup.mem_sup_left haV))
      ((dpI V (z ^ k)).inv_mem hzI)
  exact Subgroup.mem_centralizer_iff.1 hwC a haI

theorem orderOf_eq_three_of_inf (d : DihedralPair H T V U x z)
    (hV16 : Nat.card V = 2 ^ 4) (hZ2 : Nat.card (dpZ V z) = 2)
    (hCA : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z)
    (hint : ∀ k : ℕ, 0 < k → k < orderOf z → U ⊓ cjSub (z ^ k) U ≤ dpZ V z) :
    orderOf z = 3 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set p := orderOf z with hpdef
  set P := dpP H V U z with hP
  set Z := dpZ V z with hZ
  have hUcard : Nat.card U = 8 := by
    have := d.cardV
    rw [hV16] at this
    omega
  have hPcard : Nat.card P = 32 := by
    have h := (d.isExtraspecialPlus hV16 hZ2 hCA).2.1
    rw [h]
    norm_num
  have hzP : z ∈ Subgroup.normalizer (P : Set G) := d.IP d.zI
  have hZnorm : ∀ g ∈ dpI V z, cjSub g Z = Z := fun g hg =>
    cjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun ζ hζ => (d.ZC ζ hζ g hg).symm))
  have hzpowI : ∀ i : ℕ, z ^ i ∈ dpI V z := fun i => (dpI V z).pow_mem d.zI i
  have hUiP : ∀ i : ℕ, cjSub (z ^ i) U ≤ P := fun i => by
    have h1 : cjSub (z ^ i) P = P :=
      cjSub_eq_of_mem_normalizer (Subgroup.pow_mem _ hzP i)
    rw [← h1]
    exact cjSub_mono le_sup_left
  have hZi : ∀ i : ℕ, Z ≤ cjSub (z ^ i) U := fun i => by
    rw [← hZnorm _ (hzpowI i)]
    exact cjSub_mono d.ZU
  have hUij : ∀ i j : ℕ, i < j → j < p → cjSub (z ^ i) U ⊓ cjSub (z ^ j) U ≤ Z := by
    intro i j hij hjp
    have e : cjSub (z ^ j) U = cjSub (z ^ i) (cjSub (z ^ (j - i)) U) := by
      rw [← cjSub_mul, ← pow_add, Nat.add_sub_cancel' hij.le]
    rw [e, ← cjSub_inf, ← hZnorm _ (hzpowI i)]
    exact cjSub_mono (hint _ (Nat.sub_pos_of_lt hij) (by omega))
  let fs : Subgroup G → Finset G := fun K => Finset.univ.filter (· ∈ K)
  have hfs : ∀ K : Subgroup G, (fs K).card = Nat.card K := fun K => by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have hfsle : ∀ {K L : Subgroup G}, K ≤ L → fs K ⊆ fs L := fun hKL g hg => by
    simp only [fs, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    exact hKL hg
  let S : ℕ → Finset G := fun i => fs (cjSub (z ^ i) U) \ fs Z
  have hS : ∀ i, (S i).card = 6 := fun i => by
    have h1 := Finset.card_sdiff_add_card_eq_card (hfsle (hZi i))
    rw [hfs, hfs, card_cjSub, hUcard, hZ2] at h1
    show (fs (cjSub (z ^ i) U) \ fs Z).card = 6
    omega
  have hdisj : ((Finset.range p : Finset ℕ) : Set ℕ).PairwiseDisjoint S := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rw [Function.onFun, Finset.disjoint_left]
    intro g hgi hgj
    simp only [S, fs, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hgi hgj
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hgi.2 (hUij i j h hj ⟨hgi.1, hgj.1⟩)
    · exact hgi.2 (hUij j i h hi ⟨hgj.1, hgi.1⟩)
  have hsub : (Finset.range p).biUnion S ⊆ fs P \ fs Z := by
    intro g hg
    rw [Finset.mem_biUnion] at hg
    obtain ⟨i, -, hgi⟩ := hg
    simp only [S, fs, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hgi ⊢
    exact ⟨hUiP i hgi.1, hgi.2⟩
  have hcardU : ((Finset.range p).biUnion S).card = 6 * p := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun i _ => hS i)]
    simp [mul_comm]
  have hcardP : (fs P \ fs Z).card = 30 := by
    have hZP : Z ≤ P := d.ZU.trans le_sup_left
    have h1 : (fs P \ fs Z).card + (fs Z).card = (fs P).card :=
      Finset.card_sdiff_add_card_eq_card (hfsle hZP)
    have h2 : (fs P).card = 32 := by rw [hfs, hPcard]
    have h3 : (fs Z).card = 2 := by rw [hfs, hZ2]
    omega
  have hp5 : 6 * p ≤ 30 := by
    rw [← hcardU, ← hcardP]
    exact Finset.card_le_card hsub
  have hp2 : p ≠ 2 := by
    intro h2
    have := d.zodd
    rw [← hpdef, h2] at this
    exact absurd this (by decide)
  have hpne5 : p ≠ 5 := by
    intro h5
    have heq : (Finset.range p).biUnion S = fs P \ fs Z :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcardU, hcardP, h5])
    have hsq : ∀ g ∈ P, g * g = 1 := by
      intro g hg
      by_cases hgZ : g ∈ Z
      · simpa [pow_two] using d.elem.2 g hgZ.1
      · have hmem : g ∈ fs P \ fs Z := by
          simp only [fs, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hg, hgZ⟩
        rw [← heq, Finset.mem_biUnion] at hmem
        obtain ⟨i, -, hgi⟩ := hmem
        simp only [S, fs, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
          true_and] at hgi
        simpa [pow_two] using (isElemAbelian_cjSub (isElemAbelian_mono d.UV d.elem)).2 g hgi.1
    have hcomm : ∀ g ∈ P, ∀ h ∈ P, g * h = h * g := by
      intro g hg h hh
      have h1 := hsq _ (P.mul_mem hg hh)
      have h2 := hsq g hg
      have h3 := hsq h hh
      calc g * h = g * (g * h * (g * h)) * h := by rw [h1]; group
        _ = (g * g) * h * g * (h * h) := by group
        _ = h * g := by rw [h2, h3]; group
    have hUA : U ⊓ Subgroup.centralizer (dpA H V U z : Set G) = U := inf_eq_left.2
      fun u hu => Subgroup.mem_centralizer_iff.2 fun a ha =>
        hcomm a (Subgroup.mem_sup_right ha) u (Subgroup.mem_sup_left hu)
    rw [d.U_inf_centralizer hCA] at hUA
    have h1 : Z = U := hUA
    have : Nat.card Z = Nat.card U := by rw [h1]
    rw [hZ2, hUcard] at this
    exact absurd this (by norm_num)
  have h0 : p ≠ 0 := (orderOf_pos z).ne'
  have h1 : p ≠ 1 := fun h => d.z1 (orderOf_eq_one_iff.1 h)
  have hodd : Odd p := d.zodd
  rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5) with h | h | h | h
  · exact absurd h hp2
  · exact h
  · rw [h] at hodd
    exact absurd hodd (by decide)
  · exact absurd h hpne5

theorem orderOf_eq_three (d : DihedralPair H T V U x z) (hp : (orderOf z).Prime)
    (hV16 : Nat.card V = 2 ^ 4) (hZ2 : Nat.card (dpZ V z) = 2)
    (hCA : V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z) : orderOf z = 3 :=
  d.orderOf_eq_three_of_inf hV16 hZ2 hCA fun _ hk0 hkp => d.inf_cjSub_pow_le hp hCA hk0 hkp

theorem S_le (d : DihedralPair H T V U x z) :
    Subgroup.zpowers z ⊔ Subgroup.zpowers x ≤ dpI V z :=
  sup_le (Subgroup.zpowers_le.2 d.zI) (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left d.xV))

omit [Finite G] in
theorem le_S_sup_P (d : DihedralPair H T V U x z) :
    dpI V z ≤ (Subgroup.zpowers z ⊔ Subgroup.zpowers x) ⊔ dpP H V U z := by
  set K := (Subgroup.zpowers z ⊔ Subgroup.zpowers x) ⊔ dpP H V U z with hK
  have hzK : z ∈ K := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hxK : x ∈ K := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hVK : V ≤ K := by
    intro v hv
    rcases d.U2 v hv with h | h
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left h)
    · have e : v = x * (x * v) := by rw [← mul_assoc, d.x2, one_mul]
      rw [e]
      exact K.mul_mem hxK (Subgroup.mem_sup_right (Subgroup.mem_sup_left h))
  refine sup_le hVK fun w hw => ?_
  rw [mem_cjSub] at hw
  have e : w = z * (z⁻¹ * w * z) * z⁻¹ := by group
  rw [e]
  exact K.mul_mem (K.mul_mem hzK (hVK hw)) (K.inv_mem hzK)

theorem P_inf_S (d : DihedralPair H T V U x z) :
    dpP H V U z ⊓ (Subgroup.zpowers z ⊔ Subgroup.zpowers x) = ⊥ := by
  set P := dpP H V U z with hP
  have hPT : P ≤ T := d.PR.trans d.RT
  have hodd : ∀ c ∈ Subgroup.zpowers z, c ∈ P → c = 1 := fun c hc hcP => by
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one d.T2 (hPT hcP)
    exact eq_one_of_odd_orderOf_of_pow_two_pow
      (Odd.of_dvd_nat d.zodd (orderOf_dvd_of_mem_zpowers hc)) hk
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine Subgroup.zpowers_le.2 (B6.mem_normalizer_of_forall_mem (fun c hc => ?_)
      (fun c hc => ?_))
    · rw [conj_eq_inv_of_mem_zpowers d.xz hc]
      exact (Subgroup.zpowers z).inv_mem hc
    · have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right d.x2
      have h1 := conj_eq_inv_of_mem_zpowers d.xz hc
      rw [hxi] at h1 ⊢
      rw [h1]
      exact (Subgroup.zpowers z).inv_mem hc
  have hxP : x ∉ P := fun hx => by
    have : x ∈ V ⊓ dpR H V U z := ⟨d.xV, d.PR hx⟩
    rw [d.VR] at this
    exact d.xU this
  rw [eq_bot_iff]
  rintro g ⟨hgP, hgS⟩
  rw [Subgroup.mem_bot]
  have hgS' : g ∈ ((Subgroup.zpowers z ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := hgS
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hxN] at hgS'
  obtain ⟨c, hc, y, hy, rfl⟩ := hgS'
  replace hgP : c * y ∈ P := hgP
  show c * y = 1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, d.x2]
  rw [zpow_eq_zpow_emod k hx2] at hgP ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero, mul_one] at hgP ⊢
    exact hodd c hc hgP
  · rw [h, zpow_one] at hgP ⊢
    exfalso
    have hxIP : x ∈ Subgroup.normalizer (P : Set G) := d.IP (Subgroup.mem_sup_left d.xV)
    have h1 : x * (c * x) * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hxIP _).mp hgP
    have e1 : x * (c * x) * x⁻¹ = c⁻¹ * x := by
      rw [← conj_eq_inv_of_mem_zpowers d.xz hc]
      group
    rw [e1] at h1
    have h2 : c * x * (c⁻¹ * x)⁻¹ = c ^ 2 ^ 1 := by
      rw [pow_one, pow_two]
      group
    have hc2 : c ^ 2 ^ 1 = 1 := by
      have := P.mul_mem hgP (P.inv_mem h1)
      rw [h2] at this
      exact hodd _ (Subgroup.pow_mem _ hc _) this
    have hc1 : c = 1 := eq_one_of_odd_orderOf_of_pow_two_pow
      (Odd.of_dvd_nat d.zodd (orderOf_dvd_of_mem_zpowers hc)) hc2
    rw [hc1, one_mul] at hgP
    exact hxP hgP

end DihedralPair

theorem exists_surjective_ker_of_complement {G : Type*} [Group G] {I P S : Subgroup G}
    (hPI : P ≤ I) (hSI : S ≤ I) (hN : I ≤ Subgroup.normalizer (P : Set G)) (hsup : I ≤ S ⊔ P)
    (hinf : P ⊓ S = ⊥) {Q : Type*} [Group Q] (e : ↥S ≃* Q) :
    ∃ φ : ↥I →* Q, Function.Surjective φ ∧ φ.ker = P.subgroupOf I := by
  have : (P.subgroupOf I).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPI).2 hN
  let f : ↥S →* ↥I ⧸ P.subgroupOf I := (QuotientGroup.mk' _).comp (Subgroup.inclusion hSI)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : Subgroup.inclusion hSI s ∈ P.subgroupOf I := (QuotientGroup.eq_one_iff _).1 hs
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at h1
    have h2 : (s : G) ∈ P ⊓ S := ⟨h1, s.2⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
    have hg : (g : G) ∈ ((S ⊔ P : Subgroup G) : Set G) := hsup g.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hSI.trans hN)] at hg
    obtain ⟨s, hs, p, hp, hsp⟩ := hg
    refine ⟨⟨s, hs⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hSI ⟨s, hs⟩) : ↥I ⧸ P.subgroupOf I) =
      QuotientGroup.mk g
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((Subgroup.inclusion hSI ⟨s, hs⟩)⁻¹ * g : ↥I) : G) = p := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, ← hsp]
      group
    rw [e]
    exact hp
  let e' : ↥S ≃* ↥I ⧸ P.subgroupOf I := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨(e.toMonoidHom.comp e'.symm.toMonoidHom).comp (QuotientGroup.mk' _), ?_, ?_⟩
  · exact (e.surjective.comp e'.symm.surjective).comp (QuotientGroup.mk'_surjective _)
  · ext g
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem nonempty_perm_three_mulEquiv_dihedral :
    Nonempty (Equiv.Perm (Fin 3) ≃* DihedralGroup 3) := by
  have hρ : orderOf (finRotate 3) = 3 := orderOf_eq_prime (by decide) (by decide)
  have hσ : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 := orderOf_eq_prime (by decide) (by decide)
  have hgen : (⊤ : Subgroup (Equiv.Perm (Fin 3))) =
      Subgroup.zpowers (finRotate 3) ⊔ Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
    exact (Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 1))
      (support_finRotate (n := 1)) 0).symm
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem (finRotate 3)
    (Equiv.swap (0 : Fin 3) 1) hgen (by decide) (by decide) (fun hmem => by
      have hdvd := orderOf_dvd_of_mem_zpowers hmem
      rw [hρ, hσ] at hdvd
      norm_num at hdvd)
  rwa [hρ] at h

theorem nonempty_zpowers_sup_mulEquiv_perm_three {G : Type*} [Group G] [Finite G] {ρ σ : G}
    (hρ : orderOf ρ = 3) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) :
    Nonempty (↥(Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) ≃* Equiv.Perm (Fin 3)) := by
  set S := Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ with hS
  have hρS : ρ ∈ S := Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ)
  have hσS : σ ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
  have hgen : (⊤ : Subgroup ↥S) = Subgroup.zpowers ⟨ρ, hρS⟩ ⊔ Subgroup.zpowers ⟨σ, hσS⟩ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  have hσ' : (⟨σ, hσS⟩ : ↥S) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hσ)
  have hrel' : (⟨σ, hσS⟩ : ↥S) * ⟨ρ, hρS⟩ * (⟨σ, hσS⟩ : ↥S)⁻¹ = (⟨ρ, hρS⟩ : ↥S)⁻¹ :=
    Subtype.ext (by simpa using hrel)
  have hnot : (⟨σ, hσS⟩ : ↥S) ∉ Subgroup.zpowers (⟨ρ, hρS⟩ : ↥S) := by
    intro hmem
    have h1 := orderOf_dvd_of_mem_zpowers hmem
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hρ,
      orderOf_eq_prime (p := 2) (by rw [pow_two, hσ]) hσ1] at h1
    norm_num at h1
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem _ _ hgen hσ' hrel' hnot
  rw [Subgroup.orderOf_mk, hρ] at e
  obtain ⟨e₃⟩ := nonempty_perm_three_mulEquiv_dihedral
  exact ⟨e.trans e₃.symm⟩

namespace DihedralPair

variable {G : Type*} [Group G] [Finite G] {H T V U : Subgroup G} {x z : G}

theorem exists_surjective_perm_three (d : DihedralPair H T V U x z) (hz3 : orderOf z = 3) :
    ∃ φ : ↥(dpI V z) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
      φ.ker = (dpP H V U z).subgroupOf (dpI V z) := by
  have hx1 : x ≠ 1 := fun h => d.xU (h ▸ U.one_mem)
  obtain ⟨e⟩ := nonempty_zpowers_sup_mulEquiv_perm_three hz3 d.x2 hx1 d.xz
  exact exists_surjective_ker_of_complement (d.PR.trans inf_le_left) d.S_le d.IP d.le_S_sup_P
    d.P_inf_S e

theorem cube_le_sq (d : DihedralPair H T V U x z)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI d.elem H)) :
    ((dpA H V U z ⊓ Subgroup.centralizer (V : Set G)).relIndex (dpA H V U z)) ^ 3 ≤
      ((V ⊓ Subgroup.centralizer (dpA H V U z : Set G)).relIndex V) ^ 2 := by
  set A := dpA H V U z with hA
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := d.AT.trans d.TV
  have hAH : A ≤ H := (d.AR.trans inf_le_left).trans d.IH
  have hAV : ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply d.relIndex_ne_one
    rw [← d.ACV, inf_eq_left.2 hle, Subgroup.relIndex_self]
  have h := le_kq_iff.1 hq (autI d.elem A) ⟨autI_mono d.elem hAH,
    (autI_eq_bot_iff d.elem hAN).not.2 hAV, isElemAbelian2_autI d.elem d.Ael hAN⟩
    (commSeries_autI_eq_bot_of_cubic d.cubic)
  rw [rAV_autI hAN] at h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian d.elem)
  obtain ⟨l, hl⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian d.Ael)
  have hdx := hk ▸ relIndex_dvd_card (V ⊓ Subgroup.centralizer (A : Set G)) V inf_le_left
  have hdy := hl ▸ relIndex_dvd_card (A ⊓ Subgroup.centralizer (V : Set G)) A inf_le_left
  obtain ⟨β, -, hβ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdx
  obtain ⟨α, -, hα⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdy
  have hα0 : 0 < α := by
    rcases Nat.eq_zero_or_pos α with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hα
      exact hAV ((Subgroup.relIndex_eq_one.1 hα).trans inf_le_right)
    · exact h0
  rw [hβ, hα, padicValNat.prime_pow, padicValNat.prime_pow,
    le_div_iff₀ (by exact_mod_cast hα0)] at h
  rw [hβ, hα, ← pow_mul, ← pow_mul]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have h3 : ((α * 3 : ℕ) : ℚ) ≤ ((β * 2 : ℕ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast h3

theorem stage_one (d : DihedralPair H T V U x z) (hp : (orderOf z).Prime)
    (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI d.elem H)) :
    orderOf z = 3 ∧ Nat.card (dpZ V z) = 2 ∧
      V ⊓ Subgroup.centralizer (dpA H V U z : Set G) = dpZ V z ∧
      IsExtraspecialPlus 2 (dpP H V U z) ∧
      dpI V z ≤ Subgroup.normalizer (dpP H V U z : Set G) ∧
      ∃ φ : ↥(dpI V z) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
        φ.ker = (dpP H V U z).subgroupOf (dpI V z) := by
  obtain ⟨-, hZ2, hCA⟩ := d.counts hV16 (d.cube_le_sq hq)
  have hz3 := d.orderOf_eq_three hp hV16 hZ2 hCA
  exact ⟨hz3, hZ2, hCA, d.isExtraspecialPlus hV16 hZ2 hCA, d.IP,
    d.exists_surjective_perm_three hz3⟩

end DihedralPair

end E2

end CFSG.Quasithin
