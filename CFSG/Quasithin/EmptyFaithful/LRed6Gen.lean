module

public import CFSG.Quasithin.EmptyFaithful.Insp10Geom
public import CFSG.Quasithin.Background.S1567BYE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace LRed6

section FPF

variable {G : Type} [Group G] [Finite G]

theorem exists_fpf_element {Y V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVN : Y ≤ Subgroup.normalizer (V : Set G))
    (hQ : Nonempty (OTwoQuot Y ≃* Multiplicative (ZMod 3)))
    (hP : pCoreOf 2 Y ≤ Subgroup.centralizer (V : Set G)) (hcomm : ⁅V, Y⁆ = V) :
    ∃ y₀ ∈ Y, y₀ ^ 3 = 1 ∧ ∀ v ∈ V, y₀ * v * y₀⁻¹ = v → v = 1 := by
  classical
  obtain ⟨e⟩ := hQ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQcard : Nat.card (OTwoQuot Y) = 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd]
    simp
  have h3 : 3 ∣ Nat.card ↥Y := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Y)
    rw [hQcard] at this
    exact ⟨_, this⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hq0 : (QuotientGroup.mk x : OTwoQuot Y) ≠ 1 := by
    intro h
    have hx2 : x ∈ CFSG.Open.pCore 2 ↥Y := (QuotientGroup.eq_one_iff x).mp h
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2) ⟨x, hx2⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd : 3 ∣ 2 ^ k := hx ▸ orderOf_dvd_of_pow_eq_one hk'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  have hgen : Subgroup.zpowers (QuotientGroup.mk x : OTwoQuot Y) = ⊤ :=
    zpowers_eq_top_of_prime_card hQcard hq0
  set y₀ : G := (x : G) with hy₀
  have hy₀Y : y₀ ∈ Y := x.2
  have hy₀3 : y₀ ^ 3 = 1 := by
    have h1 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val h1
  have hact : ∀ y ∈ Y, ∃ i : ℤ, y * y₀ ^ (-i) ∈ Subgroup.centralizer (V : Set G) := by
    intro y hy
    have hmem : (QuotientGroup.mk (⟨y, hy⟩ : ↥Y) : OTwoQuot Y) ∈ Subgroup.zpowers (QuotientGroup.mk x : OTwoQuot Y) := by
      rw [hgen]
      exact Subgroup.mem_top _
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨i, hP ?_⟩
    have h1 : (QuotientGroup.mk ((⟨y, hy⟩ : ↥Y) * x ^ (-i)) : OTwoQuot Y) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, zpow_neg, ← hi, mul_inv_cancel]
    have h2 : (⟨y, hy⟩ : ↥Y) * x ^ (-i) ∈ CFSG.Open.pCore 2 ↥Y :=
      (QuotientGroup.eq_one_iff _).mp h1
    refine ⟨(⟨y, hy⟩ : ↥Y) * x ^ (-i), h2, ?_⟩
    simp [hy₀]
  have hN : y₀ ∈ Subgroup.normalizer (V : Set G) := hVN hy₀Y
  have hyN : ∀ y ∈ Y, ∀ v ∈ V, y * v * y⁻¹ ∈ V := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hVN hy) v).mp hv
  set σ : MulAut (IntMod V hV) := convI hV ⟨y₀, hN⟩ with hσ
  have hσval : ∀ u : IntMod V hV, (σ u).val = y₀ * u.val * y₀⁻¹ :=
    fun u => convI_apply_val hV ⟨y₀, hN⟩ u
  have hy₀3' : y₀ * y₀ * y₀ = 1 := by simpa [pow_succ] using hy₀3
  have hy₀3z : y₀ ^ (3 : ℤ) = 1 := by simpa using hy₀3
  have hσ3 : ∀ u : IntMod V hV, σ (σ (σ u)) = u := by
    intro u
    apply IntMod.val_injective
    rw [hσval, hσval, hσval]
    have : y₀ * (y₀ * (y₀ * u.val * y₀⁻¹) * y₀⁻¹) * y₀⁻¹ =
        (y₀ * y₀ * y₀) * u.val * (y₀ * y₀ * y₀)⁻¹ := by
      group
    rw [this, hy₀3']
    simp
  let δ : IntMod V hV →* IntMod V hV :=
    { toFun := fun u => u * (σ u)⁻¹
      map_one' := by simp
      map_mul' := fun u u' => by
        simp only [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hδ : ∀ u, δ u = u * (σ u)⁻¹ := fun u => rfl
  have hgen' : ∀ v ∈ V, ∀ y ∈ Y, ∃ hv : ⁅v, y⁆ ∈ V, IntMod.mk hV ⟨⁅v, y⁆, hv⟩ ∈ δ.range := by
    intro v hv y hy
    have hvy : ⁅v, y⁆ ∈ V := by
      have h1 := hyN y hy v⁻¹ (V.inv_mem hv)
      have : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact V.mul_mem hv h1
    refine ⟨hvy, ?_⟩
    obtain ⟨i, hi⟩ := hact y hy
    set n : G := y * y₀ ^ (-i) with hn
    have hy' : y = n * y₀ ^ i := by
      rw [hn]
      group
    have hi3 : y₀ ^ i = y₀ ^ (i % 3) := zpow_eq_zpow_emod i hy₀3z
    have hj : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    have hcomm' : ∀ j : ℤ, y₀ ^ i = y₀ ^ j → ⁅v, y⁆ = v * (y₀ ^ j * v⁻¹ * (y₀ ^ j)⁻¹) := by
      intro j hj'
      have hw : y₀ ^ j * v⁻¹ * (y₀ ^ j)⁻¹ ∈ V := by
        have : ∀ k : ℕ, y₀ ^ (k : ℤ) * v⁻¹ * (y₀ ^ (k : ℤ))⁻¹ ∈ V := by
          intro k
          induction k with
          | zero => simpa using V.inv_mem hv
          | succ k ih =>
            have := hyN y₀ hy₀Y _ ih
            have e : y₀ * (y₀ ^ (k : ℤ) * v⁻¹ * (y₀ ^ (k : ℤ))⁻¹) * y₀⁻¹ =
                y₀ ^ ((k + 1 : ℕ) : ℤ) * v⁻¹ * (y₀ ^ ((k + 1 : ℕ) : ℤ))⁻¹ := by
              push_cast
              group
            rw [e] at this
            exact this
        obtain ⟨k, hk⟩ : ∃ k : ℕ, y₀ ^ j = y₀ ^ (k : ℤ) := by
          refine ⟨(j % 3).toNat, ?_⟩
          rw [zpow_eq_zpow_emod j hy₀3z]
          congr 1
          have := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
          omega
        rw [hk]
        exact this k
      have hnc : n * (y₀ ^ j * v⁻¹ * (y₀ ^ j)⁻¹) = (y₀ ^ j * v⁻¹ * (y₀ ^ j)⁻¹) * n := by
        have := Subgroup.mem_centralizer_iff.mp hi _ hw
        exact this.symm
      calc ⁅v, y⁆ = v * (n * (y₀ ^ i * v⁻¹ * (y₀ ^ i)⁻¹) * n⁻¹) := by
            rw [hy']
            simp only [commutatorElement_def]
            group
        _ = v * (n * (y₀ ^ j * v⁻¹ * (y₀ ^ j)⁻¹) * n⁻¹) := by rw [hj']
        _ = v * ((y₀ ^ j * v⁻¹ * (y₀ ^ j)⁻¹) * n * n⁻¹) := by rw [hnc]
        _ = v * (y₀ ^ j * v⁻¹ * (y₀ ^ j)⁻¹) := by group
    set u : IntMod V hV := IntMod.mk hV ⟨v, hv⟩ with hu
    have huval : u.val = v := rfl
    rcases hj with h0 | h1 | h2
    · have e : ⁅v, y⁆ = 1 := by
        rw [hcomm' 0 (by rw [hi3, h0]), zpow_zero]
        group
      have : (IntMod.mk hV ⟨⁅v, y⁆, hvy⟩ : IntMod V hV) = 1 := by
        apply IntMod.val_injective
        show ⁅v, y⁆ = 1
        exact e
      rw [this]
      exact δ.range.one_mem
    · have e : ⁅v, y⁆ = v * (y₀ * v⁻¹ * y₀⁻¹) := by
        rw [hcomm' 1 (by rw [hi3, h1]), zpow_one]
      refine ⟨u, ?_⟩
      apply IntMod.val_injective
      show (u * (σ u)⁻¹).val = ⁅v, y⁆
      rw [IntMod.val_mul, IntMod.val_inv, hσval, e, huval]
      group
    · have e : ⁅v, y⁆ = v * (y₀ ^ (2 : ℤ) * v⁻¹ * (y₀ ^ (2 : ℤ))⁻¹) := hcomm' 2 (by rw [hi3, h2])
      refine ⟨u * σ u, ?_⟩
      have e2 : δ (u * σ u) = u * (σ (σ u))⁻¹ := by
        rw [map_mul, hδ, hδ]
        group
      rw [e2]
      apply IntMod.val_injective
      show (u * (σ (σ u))⁻¹).val = ⁅v, y⁆
      rw [IntMod.val_mul, IntMod.val_inv, hσval, hσval, e, huval]
      group
  have hallV : ∀ g ∈ V, ∃ hg : g ∈ V, IntMod.mk hV ⟨g, hg⟩ ∈ δ.range := by
    intro g hg
    have hg' : g ∈ ⁅V, Y⁆ := by
      rw [hcomm]
      exact hg
    rw [Subgroup.commutator_def] at hg'
    refine Subgroup.closure_induction
      (p := fun k _ => ∃ hk : k ∈ V, IntMod.mk hV ⟨k, hk⟩ ∈ δ.range) ?_ ?_ ?_ ?_ hg'
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hgen' a ha b hb
    · exact ⟨V.one_mem, δ.range.one_mem⟩
    · rintro a b _ _ ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨V.mul_mem ha hb, δ.range.mul_mem ha' hb'⟩
    · rintro a _ ⟨ha, ha'⟩
      exact ⟨V.inv_mem ha, δ.range.inv_mem ha'⟩
  refine ⟨y₀, hy₀Y, hy₀3, fun v hv hfix => ?_⟩
  obtain ⟨hv', u, hu⟩ := hallV v hv
  set u₀ : IntMod V hV := IntMod.mk hV ⟨v, hv⟩ with hu₀def
  have hσu₀ : σ u₀ = u₀ := by
    apply IntMod.val_injective
    rw [hσval]
    exact hfix
  have hu₀ : u₀ = u * (σ u)⁻¹ := hu.symm
  have hprod : (u * (σ u)⁻¹) * σ (u * (σ u)⁻¹) * σ (σ (u * (σ u)⁻¹)) = 1 := by
    simp only [map_mul, map_inv, hσ3]
    group
  rw [← hu₀, hσu₀, hσu₀] at hprod
  have h2 : u₀ * u₀ = 1 := by
    have := IntMod.sq_eq_one u₀
    rwa [pow_two] at this
  have h1 : u₀ = 1 := by
    calc u₀ = u₀ * u₀ * u₀ := by rw [h2, one_mul]
      _ = 1 := hprod
  have h3 := congrArg IntMod.val h1
  exact h3

end FPF

section YF

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem TE_le_normalizer_YF (c : Ctx153 G T Mc M V₁ V₂ t) (r66 : Res15366B T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) :
    TE153 T E ≤ Subgroup.normalizer (YF153 Mc M E s : Set G) := by
  have hTET : TE153 T E ≤ T := inf_le_left
  have hN : ((TE153 T E).subgroupOf T).Normal :=
    Subgroup.normal_of_index_eq_two r66.relIndex_two
  have hsT : s ∈ T := gl.s_mem.1
  intro t' ht'
  have h1 : s * t' * s⁻¹ ∈ TE153 T E := by
    have := hN.conj_mem ⟨t', hTET ht'⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨s, hsT⟩
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  have h2 : s * t' * s⁻¹ ∈ Subgroup.normalizer (YE153 Mc M E : Set G) :=
    S1567.YE_TE_le_normalizer_YE c (Subgroup.mem_sup_right h1)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  show x ∈ conjSubgroup (YE153 Mc M E) s ↔ t' * x * t'⁻¹ ∈ conjSubgroup (YE153 Mc M E) s
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  have e : s * (t' * x * t'⁻¹) * s⁻¹ = (s * t' * s⁻¹) * (s * x * s⁻¹) * (s * t' * s⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp h2 (s * x * s⁻¹)

theorem YF_quot (c : Ctx153 G T Mc M V₁ V₂ t) (r66 : Res15366B T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) (r68 : Res15368 T Mc M E s) (hne : YF153 Mc M E s ≠ ⊥) :
    Nonempty (OTwoQuot (YF153 Mc M E s) ≃* Multiplicative (ZMod 3)) := by
  have hYH : YF153 Mc M E s ≤ G1_153 T Mc M E s := le_sup_left
  have hH : G1_153 T Mc M E s ≤ Subgroup.normalizer (YF153 Mc M E s : Set G) :=
    sup_le Subgroup.le_normalizer (TE_le_normalizer_YF c r66 gl)
  have hgen : YF153 Mc M E s ≤ Subgroup.closure {x | x ∈ YF153 Mc M E s ∧ Odd (orderOf x)} :=
    (oTwoUpper_YF Mc M E s).ge
  refine S1567.nonempty_oTwoQuot_mulEquiv_zmod_three hYH hH hgen r68.triple.2.1 ?_
  intro hle
  apply hne
  have hp : IsPGroup 2 ↥(YF153 Mc M E s) := (pCoreOf_isPGroup 2 _).to_le hle
  have : YF153 Mc M E s ≤ ⊥ := by
    refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hx, hodd⟩
    obtain ⟨k, hk⟩ := hp ⟨x, hx⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h1 : orderOf x = 1 := by
      have hc : Nat.Coprime (orderOf x) (2 ^ k) :=
        (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)).symm
      exact Nat.eq_one_of_dvd_coprimes hc dvd_rfl hd
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  exact le_bot_iff.mp this

end YF

end LRed6

end CFSG.Quasithin
