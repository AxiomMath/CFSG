module

public import CFSG.Quasithin.H13.L32A768c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem oTwoUpper_map_of_injective {Y G : Type} [Group Y] [Group G] (f : Y →* G)
    (hf : Function.Injective f) (A : Subgroup Y) :
    (oTwoUpper A).map f = oTwoUpper (A.map f) := by
  rw [oTwoUpper, oTwoUpper, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨a, ⟨haA, hodd⟩, rfl⟩
    exact ⟨⟨a, haA, rfl⟩, by rwa [orderOf_injective f hf]⟩
  · rintro ⟨⟨a, haA, rfl⟩, hodd⟩
    exact ⟨a, ⟨haA, by rwa [orderOf_injective f hf] at hodd⟩, rfl⟩

section Central

variable {Y Q : Type} [Group Y] [Group Q] (φ : Y →* Q)

theorem mem_centralizer_of_odd (hker : φ.ker ≤ Subgroup.center Y) (hker2 : IsPGroup 2 φ.ker)
    {y g : Y} (hg : φ g * φ y = φ y * φ g) (hodd : Odd (orderOf g)) :
    g * y = y * g := by
  obtain ⟨c, hc⟩ : ∃ c, c = g * y * g⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hcK : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, hg]
    group
  have hcZ := hker hcK
  have hgy : g * y * g⁻¹ = c * y := by rw [hc]; group
  have hpow : ∀ n : ℕ, g ^ n * y * (g ^ n)⁻¹ = c ^ n * y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc g ^ (n + 1) * y * (g ^ (n + 1))⁻¹ = g * (g ^ n * y * (g ^ n)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (c ^ n * y) * g⁻¹ := by rw [ih]
        _ = c ^ n * (g * y * g⁻¹) := by
            rw [show g * (c ^ n * y) * g⁻¹ = (g * c ^ n * g⁻¹) * (g * y * g⁻¹) by group,
              show g * c ^ n * g⁻¹ = c ^ n by
                rw [Subgroup.mem_center_iff.mp (pow_mem hcZ n) g]; group]
        _ = c ^ (n + 1) * y := by rw [hgy, pow_succ, mul_assoc]
  have hcn : c ^ orderOf g = 1 := by
    have := hpow (orderOf g)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.mp this.symm)
  obtain ⟨k, hk⟩ := hker2 ⟨c, hcK⟩
  have hc2 : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hcn)
      (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)))
    (orderOf_dvd_of_pow_eq_one hc2)
  have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
  calc g * y = c * (y * g) := by rw [hc]; group
    _ = y * g := by rw [hc1, one_mul]

theorem exists_odd_preimage (hφs : Function.Surjective φ) (hker2 : IsPGroup 2 φ.ker) {x : Q}
    (hodd : Odd (orderOf x)) : ∃ g : Y, φ g = x ∧ Odd (orderOf g) := by
  obtain ⟨g₀, rfl⟩ := hφs x
  have hm : g₀ ^ orderOf (φ g₀) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := hker2 ⟨_, hm⟩
  have hk' : (g₀ ^ orderOf (φ g₀)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set g₁ := g₀ ^ 2 ^ k with hg₁
  have hg₁o : orderOf g₁ ∣ orderOf (φ g₀) := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hg₁, ← pow_mul, mul_comm, pow_mul, hk']
  have hcop : Nat.Coprime (2 ^ k) (orderOf (φ g₀)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨g₁ ^ b, by rw [map_pow, hg₁, map_pow, hb], ?_⟩
  exact (hodd.of_dvd_nat hg₁o).of_dvd_nat (orderOf_pow_dvd b)

theorem oTwoUpper_centralizer_map (hφs : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hker2 : IsPGroup 2 φ.ker) (y : Y) :
    oTwoUpper (Subgroup.centralizer ({φ y} : Set Q)) =
      (oTwoUpper (Subgroup.centralizer ({y} : Set Y))).map φ := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxC, hodd⟩
    obtain ⟨g, rfl, hgo⟩ := exists_odd_preimage φ hφs hker2 hodd
    have hgC : g ∈ Subgroup.centralizer ({y} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mem_centralizer_of_odd φ hker hker2
        (Subgroup.mem_centralizer_singleton_iff.mp hxC) hgo
    exact ⟨g, mem_oTwoUpper_of_odd hgC hgo, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgC, hodd⟩
    refine mem_oTwoUpper_of_odd ?_ (hodd.of_dvd_nat (orderOf_map_dvd φ g))
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC ⊢
    rw [← map_mul, hgC, map_mul]

theorem pCoreOf_map_eq [Finite Y] [Finite Q] (hker2 : IsPGroup 2 φ.ker) (B : Subgroup Y) :
    pCoreOf 2 (B.map φ) = (pCoreOf 2 B).map φ := by
  apply le_antisymm
  · set P := B ⊓ (pCoreOf 2 (B.map φ)).comap φ with hP
    have hPB : P ≤ pCoreOf 2 B := by
      refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun b hb => ?_) fun p => ?_
      · exact mem_normalizer_inf_of_mem (Subgroup.le_normalizer hb)
          (Subgroup.le_normalizer_comap φ (le_normalizer_pCoreOf 2 (B.map φ) ⟨b, hb, rfl⟩))
      · obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (B.map φ)) ⟨φ p, (Subgroup.mem_inf.mp p.2).2⟩
        have h1 : (p : Y) ^ 2 ^ k ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_pow]
          simpa using congrArg Subtype.val hk
        obtain ⟨j, hj⟩ := hker2 ⟨_, h1⟩
        have hj' : ((p : Y) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
        refine ⟨k + j, Subtype.ext ?_⟩
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, hj']
    intro x hx
    obtain ⟨b, hb, rfl⟩ := (pCoreOf_le 2 (B.map φ)) hx
    exact ⟨b, hPB (Subgroup.mem_inf.mpr ⟨hb, hx⟩), rfl⟩
  · refine le_pCoreOf_of_le_normalizer 2 (Subgroup.map_mono (pCoreOf_le 2 B)) ?_
      ((pCoreOf_isPGroup 2 B).map φ)
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.le_normalizer_map φ ⟨b, le_normalizer_pCoreOf 2 B hb, rfl⟩

theorem nonempty_quot_map_equiv [Finite Y] [Finite Q] (hker2 : IsPGroup 2 φ.ker) (B : Subgroup Y) :
    Nonempty (↥(B.map φ) ⧸ CFSG.pCore 2 ↥(B.map φ) ≃* ↥B ⧸ CFSG.pCore 2 ↥B) := by
  set ψ : ↥B →* ↥(B.map φ) ⧸ CFSG.pCore 2 ↥(B.map φ) :=
    (QuotientGroup.mk' _).comp (φ.subgroupMap B) with hψ
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (φ.subgroupMap_surjective B)
  have hKB : B ⊓ φ.ker ≤ pCoreOf 2 B :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun b hb => mem_normalizer_inf_of_mem (Subgroup.le_normalizer hb)
        (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact Subgroup.mem_top b))
      (hker2.to_le inf_le_right)
  have hψk : ψ.ker = CFSG.pCore 2 ↥B := by
    ext b
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf_self, ← pCoreOf_subgroupOf_self, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, pCoreOf_map_eq φ hker2 B]
    constructor
    · rintro ⟨p, hp, hpb⟩
      have hm : p⁻¹ * b ∈ B ⊓ φ.ker := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (pCoreOf_le 2 B hp)) b.2, ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, hpb]
        exact inv_mul_cancel _
      have := mul_mem hp (hKB hm)
      rwa [mul_inv_cancel_left] at this
    · intro hb
      exact ⟨b, hb, rfl⟩
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hψk)⟩

theorem relIndex_centralizer_map [Finite Y] [Finite Q] (hker : φ.ker ≤ Subgroup.center Y)
    (hker2 : IsPGroup 2 φ.ker) {A B : Subgroup Y}
    (hcomm : ∀ a ∈ A, ∀ w ∈ pCoreOf 2 B, a * w * a⁻¹ * w⁻¹ ∈ φ.ker → a * w * a⁻¹ * w⁻¹ = 1) :
    (A.map φ ⊓ Subgroup.centralizer (pCoreOf 2 (B.map φ) : Set Q)).relIndex (A.map φ) =
      (A ⊓ Subgroup.centralizer (pCoreOf 2 B : Set Y)).relIndex A := by
  set C := Subgroup.centralizer (pCoreOf 2 B : Set Y) with hC
  have hset : A.map φ ⊓ Subgroup.centralizer (pCoreOf 2 (B.map φ) : Set Q) = (A ⊓ C).map φ := by
    rw [pCoreOf_map_eq φ hker2 B]
    apply le_antisymm
    · rintro x ⟨⟨a, ha, rfl⟩, hxC⟩
      refine ⟨a, Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩, rfl⟩
      have hw' := Subgroup.mem_centralizer_iff.mp hxC (φ w) ⟨w, hw, rfl⟩
      have hk : a * w * a⁻¹ * w⁻¹ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hw']
        group
      have h1 := hcomm a ha w hw hk
      calc w * a = (a * w * a⁻¹ * w⁻¹)⁻¹ * (a * w) := by group
        _ = a * w := by rw [h1, inv_one, one_mul]
    · rintro x ⟨a, ha, rfl⟩
      obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
      refine Subgroup.mem_inf.mpr ⟨⟨a, haA, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, Subgroup.mem_centralizer_iff.mp haC w hw, map_mul]
  rw [hset]
  have hcard : ∀ X : Subgroup Y, Nat.card ↥(X.map φ) * Nat.card ↥(φ.ker ⊓ X) = Nat.card ↥X := by
    intro X
    have e1 := Subgroup.relIndex_map_map φ ⊥ X
    rw [Subgroup.map_bot, Subgroup.relIndex_bot_left, bot_sup_eq,
      Subgroup.relIndex_sup_right] at e1
    rw [e1]
    exact Subgroup.relIndex_mul_card φ.ker X
  have hkC : φ.ker ⊓ (A ⊓ C) = φ.ker ⊓ A := by
    refine le_antisymm (inf_le_inf_left _ inf_le_left) (le_inf inf_le_left (le_inf inf_le_right ?_))
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr fun w _ =>
      (Subgroup.mem_center_iff.mp (hker (Subgroup.mem_inf.mp hk).1) w)
  have h1 := hcard A
  have h2 := hcard (A ⊓ C)
  rw [hkC] at h2
  have e3 := Subgroup.relIndex_mul_card ((A ⊓ C).map φ) (A.map φ)
  rw [inf_eq_left.mpr (Subgroup.map_mono inf_le_left)] at e3
  have e4 := Subgroup.relIndex_mul_card (A ⊓ C) A
  rw [inf_eq_left.mpr inf_le_left] at e4
  have hpos : 0 < Nat.card ↥((A ⊓ C).map φ) * Nat.card ↥(φ.ker ⊓ A) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc ((A ⊓ C).map φ).relIndex (A.map φ) * (Nat.card ↥((A ⊓ C).map φ) * Nat.card ↥(φ.ker ⊓ A))
      = Nat.card ↥(A.map φ) * Nat.card ↥(φ.ker ⊓ A) := by rw [← mul_assoc, e3]
    _ = Nat.card ↥A := h1
    _ = (A ⊓ C).relIndex A * Nat.card ↥(A ⊓ C) := e4.symm
    _ = (A ⊓ C).relIndex A * (Nat.card ↥((A ⊓ C).map φ) * Nat.card ↥(φ.ker ⊓ A)) := by rw [h2]

end Central

end CFSG.Quasithin.H13.L32A
