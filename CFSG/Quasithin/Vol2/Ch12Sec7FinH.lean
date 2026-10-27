module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinG
public import CFSG.Quasithin.Vol2.Ch12Sec7FinF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits

namespace S127

variable {X : Type} [Group X] [Finite X]

theorem mem_centralizer_of_odd {D J : Subgroup X} (hDn : D.Normal)
    (hJ : J ≤ Subgroup.centralizer (D : Set X))
    (hKJ : oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) ≤
      J.map (QuotientGroup.mk' (CFSG.pCore 2 X)))
    {z : X} (hz : Odd (orderOf z)) : z ∈ Subgroup.centralizer (D : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzK : QuotientGroup.mk' (CFSG.pCore 2 X) z ∈
      oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) :=
    mem_oTwoUpper_of_odd (Subgroup.mem_top _) (hz.of_dvd_nat (orderOf_map_dvd _ z))
  obtain ⟨j, hj, hjz⟩ := hKJ hzK
  have hq : j⁻¹ * z ∈ CFSG.pCore 2 X := by
    have : (j : X ⧸ CFSG.pCore 2 X) = (z : X ⧸ CFSG.pCore 2 X) := hjz
    exact QuotientGroup.eq.1 this
  obtain ⟨q, hqdef⟩ : ∃ q, q = j⁻¹ * z := ⟨_, rfl⟩
  rw [← hqdef] at hq
  have hzjq : z = j * q := by rw [hqdef]; group
  have hconj : ∀ e ∈ D, z * e * z⁻¹ = q * e * q⁻¹ := by
    intro e he
    have hqe : q * e * q⁻¹ ∈ D := hDn.conj_mem e he q
    have hjc := Subgroup.mem_centralizer_iff.1 (hJ hj) _ hqe
    rw [hzjq]
    calc j * q * e * (j * q)⁻¹ = j * (q * e * q⁻¹) * j⁻¹ := by group
      _ = q * e * q⁻¹ * j * j⁻¹ := by rw [← hjc]
      _ = q * e * q⁻¹ := by group
  have hpow : ∀ n : ℕ, ∀ e ∈ D, z ^ n * e * (z ^ n)⁻¹ = q ^ n * e * (q ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro e _; simp
    | succ n ih =>
      intro e he
      have h1 := ih e he
      have hzn : z ^ n * e * (z ^ n)⁻¹ ∈ D := hDn.conj_mem e he _
      calc z ^ (n + 1) * e * (z ^ (n + 1))⁻¹ = z * (z ^ n * e * (z ^ n)⁻¹) * z⁻¹ := by
            rw [pow_succ']; group
        _ = q * (z ^ n * e * (z ^ n)⁻¹) * q⁻¹ := hconj _ hzn
        _ = q * (q ^ n * e * (q ^ n)⁻¹) * q⁻¹ := by rw [h1]
        _ = q ^ (n + 1) * e * (q ^ (n + 1))⁻¹ := by rw [pow_succ']; group
  have hqm : q ^ orderOf z ∈ Subgroup.centralizer (D : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h := hpow (orderOf z) e he
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    calc e * q ^ orderOf z = q ^ orderOf z * e * (q ^ orderOf z)⁻¹ * q ^ orderOf z := by
          rw [← h]
      _ = q ^ orderOf z * e := by group
  have hP : IsPGroup 2 ↥(CFSG.pCore 2 X) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup (r := 2)
  obtain ⟨k, hk⟩ := hP ⟨q, hq⟩
  have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf z) (orderOf q) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk')
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hz))
  have hqC : q ∈ Subgroup.centralizer (D : Set X) :=
    (Subgroup.zpowers_le.2 hqm) (A4.mem_zpowers_pow_of_coprime hcop)
  rw [hzjq]
  exact Subgroup.mul_mem _ (hJ hj) hqC

omit [Finite X] in
theorem inf_centralizer_conj {D A : Subgroup X} (hDn : D.Normal) (k : X) :
    D ⊓ Subgroup.centralizer (A.map (MulAut.conj k).toMonoidHom : Set X) =
      (D ⊓ Subgroup.centralizer (A : Set X)).map (MulAut.conj k).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.1 hx
    refine ⟨k⁻¹ * x * k, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · have := hDn.conj_mem x hxD k⁻¹
      simpa using this
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := Subgroup.mem_centralizer_iff.1 hxC (k * a * k⁻¹) ⟨a, ha, rfl⟩
      calc a * (k⁻¹ * x * k) = k⁻¹ * (k * a * k⁻¹ * x) * k := by group
        _ = k⁻¹ * (x * (k * a * k⁻¹)) * k := by rw [h]
        _ = k⁻¹ * x * k * a := by group
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨hDn.conj_mem y hyD k, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 hyC a ha
    show k * a * k⁻¹ * (k * y * k⁻¹) = k * y * k⁻¹ * (k * a * k⁻¹)
    calc k * a * k⁻¹ * (k * y * k⁻¹) = k * (a * y) * k⁻¹ := by group
      _ = k * (y * a) * k⁻¹ := by rw [h]
      _ = k * y * k⁻¹ * (k * a * k⁻¹) := by group

omit [Finite X] in
theorem map_conj_normal {D : Subgroup X} (hDn : D.Normal) (k : X) :
    D.map (MulAut.conj k).toMonoidHom = D := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hDn.conj_mem y hy k
  · intro hx
    refine ⟨k⁻¹ * x * k, ?_, ?_⟩
    · have := hDn.conj_mem x hx k⁻¹
      simpa using this
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group

theorem not_relIndex_le_two
    (hpsl : IsPSL 2 2 2 ↥(oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X))))
    {D A : Subgroup X} (hDn : D.Normal) (hA : IsElemAbelian 2 A)
    (hA4 : Nat.card ↥(A.map (QuotientGroup.mk' (CFSG.pCore 2 X))) = 4)
    (hK : ¬ oTwoUpper (⊤ : Subgroup X) ≤ Subgroup.centralizer (D : Set X)) :
    ¬ (D ⊓ Subgroup.centralizer (A : Set X)).relIndex D ≤ 2 := by
  classical
  intro hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hKn : (oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X))).Normal := oTwoUpper_top_normal
  have hs : IsSimpleGroup ↥(oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X))) :=
    isSimpleGroup_of_isPSL hpsl
  have hnc := nonabelian_of_isPSL hpsl
  obtain ⟨k, hkK⟩ := exists_le_map_sup_conj hpsl hA hA4
  have hle' : (D ⊓ Subgroup.centralizer (A.map (MulAut.conj k).toMonoidHom : Set X)).relIndex D
      ≤ 2 := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj k).toMonoidHom)
      (D ⊓ Subgroup.centralizer (A : Set X)) D (MulAut.conj k).injective
    rw [map_conj_normal hDn k] at h
    rw [inf_centralizer_conj hDn k, h]
    exact hle
  set D₀ := (D ⊓ Subgroup.centralizer (A : Set X)) ⊓
    (D ⊓ Subgroup.centralizer (A.map (MulAut.conj k).toMonoidHom : Set X)) with hD₀
  have hidx : D₀.relIndex D ≤ 4 :=
    Subgroup.relIndex_inf_le.trans (Nat.mul_le_mul hle hle')
  have hDD₀ : D ≤ Subgroup.normalizer (D₀ : Set X) := by
    intro d hd
    have h1 := le_normalizer_of_relIndex_le_two inf_le_left hle hd
    have h2 := le_normalizer_of_relIndex_le_two inf_le_left hle' hd
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro u
    constructor
    · intro hu
      obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
      exact Subgroup.mem_inf.2 ⟨(h1 u).1 hu1, (h2 u).1 hu2⟩
    · intro hu
      obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
      exact Subgroup.mem_inf.2 ⟨(h1 u).2 hu1, (h2 u).2 hu2⟩
  set I := A ⊔ A.map (MulAut.conj k).toMonoidHom with hI
  have hIC : I ≤ Subgroup.centralizer (D₀ : Set X) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact inf_le_left.trans inf_le_right
    · rw [Subgroup.le_centralizer_iff]
      exact inf_le_right.trans inf_le_right
  have hNtop : Subgroup.normalizer (D : Set X) = ⊤ := Subgroup.normalizer_eq_top_iff.2 hDn
  set I₅ := Subgroup.closure {i : X | i ∈ I ∧ i ^ 5 = 1} with hI₅
  have hI₅s : I₅ ≤ stabSub D D₀ := by
    rw [hI₅, Subgroup.closure_le]
    rintro i ⟨hi, hi5⟩
    have hiN : i ∈ Subgroup.normalizer (D : Set X) := by rw [hNtop]; exact Subgroup.mem_top i
    exact ⟨hiN, hIC hi, fun d hd => conj_mem_of_pow_five hidx hi5 hiN
      (Subgroup.centralizer_le_normalizer _ (hIC hi)) hd⟩
  have hJC : ⁅I₅, I₅⁆ ≤ Subgroup.centralizer (D : Set X) :=
    (Subgroup.commutator_mono hI₅s hI₅s).trans (commutator_stabSub_le hDD₀)
  have hI₅n : ∀ g ∈ I, ∀ v ∈ I₅, g * v * g⁻¹ ∈ I₅ := by
    intro g hg v hv
    have hmap : I₅.map (MulAut.conj g).toMonoidHom ≤ I₅ := by
      rw [hI₅, MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨i, ⟨hi, hi5⟩, rfl⟩
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hi) (Subgroup.inv_mem _ hg), ?_⟩
      show (g * i * g⁻¹) ^ 5 = 1
      rw [conj_pow, hi5]
      group
    exact hmap ⟨v, hv, rfl⟩
  set φ := QuotientGroup.mk' (CFSG.pCore 2 X) with hφ
  have hKI₅ : oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) ≤ I₅.map φ := by
    set K := oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) with hKdef
    set N := (I₅.map φ ⊓ K).subgroupOf K with hN
    have hNn : N.Normal := by
      refine ⟨fun n hn κ => ?_⟩
      rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
      refine Subgroup.mem_inf.2 ⟨?_, hKn.conj_mem _ hn2 _⟩
      obtain ⟨g, hg, hgκ⟩ := hkK κ.2
      obtain ⟨v, hv, hvn⟩ := hn1
      refine ⟨g * v * g⁻¹, hI₅n g hg v hv, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [hgκ, hvn]
    have h60 := Vol2.Ch10.SecB.C11AmS.card_of_isPSL_two_two_two hpsl
    obtain ⟨⟨z, hzK⟩, hz5⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [h60]; norm_num)
    rw [Subgroup.orderOf_mk] at hz5
    obtain ⟨i, hi, hiz⟩ := hkK hzK
    have hi5 : i ^ 5 ∈ CFSG.pCore 2 X := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 X), MonoidHom.mem_ker, map_pow]
      show φ i ^ 5 = 1
      rw [hiz, ← hz5, pow_orderOf_eq_one]
    have hP : IsPGroup 2 ↥(CFSG.pCore 2 X) := by
      exact CFSG.LieType.BorelTits.pCore_isPGroup (r := 2)
    obtain ⟨m, hm⟩ := hP ⟨_, hi5⟩
    have hm' : (i ^ 5) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hi' : i ^ 2 ^ m ∈ I₅ := Subgroup.subset_closure
      ⟨Subgroup.pow_mem _ hi _, by rw [← pow_mul, mul_comm, pow_mul, hm']⟩
    have hz' : z ^ 2 ^ m ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hz5] at h1
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h1
      norm_num at this
    have hNne : N ≠ ⊥ := by
      intro hN0
      have hmem : (⟨z ^ 2 ^ m, K.pow_mem hzK _⟩ : ↥K) ∈ N := by
        rw [hN, Subgroup.mem_subgroupOf]
        refine Subgroup.mem_inf.2 ⟨⟨i ^ 2 ^ m, hi', ?_⟩, K.pow_mem hzK _⟩
        rw [map_pow, hiz]
      rw [hN0, Subgroup.mem_bot] at hmem
      exact hz' (congrArg Subtype.val hmem)
    have := hs
    have := hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact absurd h hNne
    · intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ N := h ▸ Subgroup.mem_top _
      rw [hN, Subgroup.mem_subgroupOf] at this
      exact (Subgroup.mem_inf.1 this).1
  have hKJ : oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) ≤ ⁅I₅, I₅⁆.map φ := by
    rw [Subgroup.map_commutator, ← oTwoUpper_top_perfect hs hnc]
    exact Subgroup.commutator_mono hKI₅ hKI₅
  apply hK
  rw [oTwoUpper, Subgroup.closure_le]
  rintro z ⟨-, hz⟩
  exact mem_centralizer_of_odd hDn hJC hKJ hz

end S127

end CFSG.Quasithin.H13
