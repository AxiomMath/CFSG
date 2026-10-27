module

public import CFSG.Quasithin.H13.A5W1622m
public import CFSG.Quasithin.H13.A5W1622l

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped Matrix

section Fixed

variable {G : Type} [Group G]

theorem eq_one_of_fixed_sumNatural {K₀ M : Subgroup G} {F : Type} [Field F]
    {α : ↥K₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α) {k : ℕ}
    (hM : IsSumOfNaturalModulesVia K₀ M ⊥ α false k) {x : G} (hx : x ∈ M)
    (hfix : ∀ g ∈ K₀, g * x * g⁻¹ = x) : x = 1 := by
  obtain ⟨-, -, β, -, hβk, hβe⟩ := hM
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  have hw : ∀ i, Multiplicative.toAdd (β ⟨x, hx⟩) i = 0 := by
    intro i
    refine fixed_eq_zero_of_sl3 fun A => ?_
    obtain ⟨g, hg⟩ := hα (e A)
    have hA : A = e.symm (α g) := by rw [hg, e.symm_apply_apply]
    have h := hβe g ⟨x, hx⟩ ⟨x, hx⟩ (hfix g g.2).symm i
    change ((A : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ _ = _
    rw [hA, coe_symm_statedSL]
    exact h.symm
  have h1 : β ⟨x, hx⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [hw i]
    rfl
  have h2 : (⟨x, hx⟩ : ↥M) = 1 := hβinj (h1.trans (map_one β).symm)
  exact congrArg Subtype.val h2

end Fixed

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem e2_eq_comm_mul {y : G} (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (hτ : S.frame.ρ ⟨y, hyN⟩ = c234 ∨ S.frame.ρ ⟨y, hyN⟩ = c234⁻¹) :
    S.e2 = (y * S.e2 * y⁻¹ * S.e2⁻¹) * (y⁻¹ * S.e2 * y * S.e2⁻¹) := by
  have hτ' : S.frame.ρ ⟨y, hyN⟩ ∈ ({c234, c234⁻¹} : Finset (Equiv.Perm (Fin 5))) := by
    rcases hτ with h | h <;> simp [h]
  have hprod := e23_eq_prod _ hτ'
  have hqV : y * S.e2 * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN _).mp S.e2_mem_V
  have hyN' : y⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hyN
  have hq'V : y⁻¹ * S.e2 * y ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp hyN' _).mp S.e2_mem_V
    simpa using this
  have hm1 : y * S.e2 * y⁻¹ * S.e2⁻¹ ∈ V := V.mul_mem hqV (V.inv_mem S.e2_mem_V)
  have hm2 : y⁻¹ * S.e2 * y * S.e2⁻¹ ∈ V := V.mul_mem hq'V (V.inv_mem S.e2_mem_V)
  have hψ1 : S.frame.ψ ⟨y * S.e2 * y⁻¹ * S.e2⁻¹, hm1⟩ =
      pact (S.frame.ρ ⟨y, hyN⟩) e23 * e23⁻¹ := by
    have e : (⟨y * S.e2 * y⁻¹ * S.e2⁻¹, hm1⟩ : ↥V) = ⟨_, hqV⟩ * (⟨S.e2, S.e2_mem_V⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, S.psi_conj ⟨y, hyN⟩ ⟨S.e2, S.e2_mem_V⟩, S.psi_e2]
  have hρinv : S.frame.ρ ⟨y⁻¹, hyN'⟩ = (S.frame.ρ ⟨y, hyN⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  have hψ2 : S.frame.ψ ⟨y⁻¹ * S.e2 * y * S.e2⁻¹, hm2⟩ =
      pact (S.frame.ρ ⟨y, hyN⟩)⁻¹ e23 * e23⁻¹ := by
    have hq'V' : y⁻¹ * S.e2 * y⁻¹⁻¹ ∈ V := by simpa using hq'V
    have e : (⟨y⁻¹ * S.e2 * y * S.e2⁻¹, hm2⟩ : ↥V) =
        ⟨y⁻¹ * S.e2 * y⁻¹⁻¹, hq'V'⟩ * (⟨S.e2, S.e2_mem_V⟩)⁻¹ := Subtype.ext (by simp)
    rw [e, map_mul, map_inv, S.psi_conj ⟨y⁻¹, hyN'⟩ ⟨S.e2, S.e2_mem_V⟩, S.psi_e2, hρinv]
  have hm12 : (y * S.e2 * y⁻¹ * S.e2⁻¹) * (y⁻¹ * S.e2 * y * S.e2⁻¹) ∈ V := V.mul_mem hm1 hm2
  have h3 : S.frame.ψ ⟨S.e2, S.e2_mem_V⟩ = S.frame.ψ ⟨_, hm12⟩ := by
    have e : (⟨_, hm12⟩ : ↥V) = ⟨_, hm1⟩ * ⟨_, hm2⟩ := rfl
    rw [e, map_mul, hψ1, hψ2, S.psi_e2]
    exact hprod
  exact congrArg Subtype.val (S.frame.ψ.injective h3)

theorem comm_conj_a_mem_zpowers {k r : G} (hkG : k ∈ Subgroup.centralizer ({S.v12} : Set G))
    (hrT : r ∈ S.Tv) (hkr : k * r * k⁻¹ ∈ S.Tv) :
    (k⁻¹ * S.a * k * S.a⁻¹) * r * (k⁻¹ * S.a * k * S.a⁻¹)⁻¹ * r⁻¹ ∈
      Subgroup.zpowers S.v12 := by
  obtain ⟨m₁, hm₁⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv hrT)
  obtain ⟨m₂, hm₂⟩ := Subgroup.mem_zpowers_iff.mp (S.comm_a_Tv hkr)
  have hvc : ∀ g ∈ Subgroup.centralizer ({S.v12} : Set G), ∀ m : ℤ,
      g * S.v12 ^ m = S.v12 ^ m * g := fun g hg m =>
    ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hg) m)).eq
  have h1 : S.a * r * S.a⁻¹ = S.v12 ^ m₁ * r := by
    rw [hm₁]; group
  have h2 : S.a * (k * r * k⁻¹) * S.a⁻¹ = S.v12 ^ m₂ * (k * r * k⁻¹) := by
    rw [hm₂]; group
  have hva : S.a⁻¹ * S.v12 ^ m₁ = S.v12 ^ m₁ * S.a⁻¹ :=
    hvc _ (Subgroup.inv_mem _ S.a_mem_Gv) m₁
  have h1' : S.a⁻¹ * r * S.a = S.v12 ^ (-m₁) * r := by
    have hr' : r = S.v12 ^ m₁ * (S.a⁻¹ * r * S.a) := by
      calc r = S.a⁻¹ * (S.a * r * S.a⁻¹) * S.a := by group
        _ = S.a⁻¹ * (S.v12 ^ m₁ * r) * S.a := by rw [h1]
        _ = (S.a⁻¹ * S.v12 ^ m₁) * r * S.a := by group
        _ = (S.v12 ^ m₁ * S.a⁻¹) * r * S.a := by rw [hva]
        _ = S.v12 ^ m₁ * (S.a⁻¹ * r * S.a) := by group
    calc S.a⁻¹ * r * S.a = S.v12 ^ (-m₁) * (S.v12 ^ m₁ * (S.a⁻¹ * r * S.a)) := by
          rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
      _ = S.v12 ^ (-m₁) * r := by rw [← hr']
  have e1 : (k⁻¹ * S.a * k * S.a⁻¹) * r * (k⁻¹ * S.a * k * S.a⁻¹)⁻¹ =
      k⁻¹ * (S.a * (k * (S.a⁻¹ * r * S.a) * k⁻¹) * S.a⁻¹) * k := by group
  have e2 : k * (S.v12 ^ (-m₁) * r) * k⁻¹ = S.v12 ^ (-m₁) * (k * r * k⁻¹) := by
    rw [← mul_assoc k, hvc k hkG (-m₁)]; group
  have e3 : S.a * (S.v12 ^ (-m₁) * (k * r * k⁻¹)) * S.a⁻¹ =
      S.v12 ^ (-m₁) * (S.a * (k * r * k⁻¹) * S.a⁻¹) := by
    rw [← mul_assoc S.a, hvc _ S.a_mem_Gv (-m₁)]; group
  have e5 : k⁻¹ * (S.v12 ^ (-m₁) * S.v12 ^ m₂) * k = S.v12 ^ (m₂ - m₁) := by
    rw [← zpow_add, show -m₁ + m₂ = m₂ - m₁ by ring, mul_assoc, ← hvc k hkG (m₂ - m₁)]
    group
  rw [e1, h1', e2, e3, h2]
  have e4 : k⁻¹ * (S.v12 ^ (-m₁) * (S.v12 ^ m₂ * (k * r * k⁻¹))) * k * r⁻¹ =
      (k⁻¹ * (S.v12 ^ (-m₁) * S.v12 ^ m₂) * k) * (k⁻¹ * (k * r * k⁻¹) * k) * r⁻¹ := by
    group
  rw [e4, e5]
  have e6 : S.v12 ^ (m₂ - m₁) * (k⁻¹ * (k * r * k⁻¹) * k) * r⁻¹ = S.v12 ^ (m₂ - m₁) := by
    group
  rw [e6]
  exact Subgroup.zpow_mem_zpowers _ _

theorem comm_mem_z0Of (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀p : ⁅K₀, K₀⁆ = K₀) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hchar : CharTwo (K₀ ⊔ S.Tv)) :
    ∀ k ∈ K₀, k⁻¹ * S.a * k * S.a⁻¹ ∈ ⁅z0Of S.v12 K₀, K₀⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcommA, -⟩ := S.comm_mem_blockU h1222 h517 hK₀G hK₀p hTK₀ hchar
  obtain ⟨hQO, -, -, hUQ⟩ := S.c134Q_facts h1222 h517 hK₀G hTK₀
  set O := pCoreOf 2 K₀ with hOdef
  have hOK : O ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hKO : K₀ ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  have hsyl : IsSylowTwoOf S.Tv (K₀ ⊔ S.Tv) :=
    C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv h1222 h517) le_sup_right (sup_le hK₀G S.Tv_le_Gv)
  have hnorm : (K₀.subgroupOf (K₀ ⊔ S.Tv)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hTK₀)
  have hOT : O ≤ S.Tv :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K₀ (K₀ ⊔ S.Tv)
      le_sup_left hnorm).trans (pCoreOf_le_of_isSylowTwoOf hsyl)
  have hUO : blockU K₀ ≤ O := by
    rw [blockU, Subgroup.commutator_le]
    intro r hr k hk
    have h1 : k * r⁻¹ * k⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hKO hk) _).mp (O.inv_mem hr)
    rw [commutatorElement_def]
    have e : r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) := by group
    rw [e]
    exact O.mul_mem hr h1
  set s : Set G := {x | x ∈ O ∧ ∀ r ∈ O, x * r * x⁻¹ * r⁻¹ ∈ Subgroup.zpowers S.v12} with hs
  have hZ0K : z0Of S.v12 K₀ ≤ K₀ := (Subgroup.closure_le _).mpr fun x hx => hOK hx.1
  have hKZ0 : K₀ ≤ Subgroup.normalizer ((z0Of S.v12 K₀ : Subgroup G) : Set G) := by
    refine le_normalizer_closure fun g hg x hx => ⟨?_, fun r hr => ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hKO hg) x).mp hx.1
    · have hr' : g⁻¹ * r * g ∈ O := by
        have := (Subgroup.mem_normalizer_iff.mp (hKO (K₀.inv_mem hg)) r).mp hr
        simpa using this
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hx.2 _ hr')
      have hgv : g * S.v12 ^ m = S.v12 ^ m * g :=
        (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hK₀G hg)) m).eq
      have e : g * x * g⁻¹ * r * (g * x * g⁻¹)⁻¹ * r⁻¹ =
          g * (x * (g⁻¹ * r * g) * x⁻¹ * (g⁻¹ * r * g)⁻¹) * g⁻¹ := by group
      rw [e, ← hm, hgv, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers _ _
  have haN : S.a ∈ Subgroup.normalizer (K₀ : Set G) := hTK₀ S.a_mem_Tv
  refine comm_mem_commutator_of_perfect hZ0K hKZ0 hK₀p haN fun k hk => ?_
  refine Subgroup.subset_closure ⟨hUO (hcommA k hk), fun r hr => ?_⟩
  have hkr : k * r * k⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO hk) r).mp hr
  exact S.comm_conj_a_mem_zpowers (hK₀G hk) (hOT hr) (hOT hkr)

theorem e2_mem_center_c134Q (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) {K₀ : Subgroup G} (hK₀G : K₀ ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hK₀p : ⁅K₀, K₀⁆ = K₀) (hTK₀ : S.Tv ≤ Subgroup.normalizer (K₀ : Set G))
    (hchar : CharTwo (K₀ ⊔ S.Tv)) (hLvK₀ : S.Lv ≤ K₀) :
    S.e2 ∈ centerOf (c134Q (K₀ ⊔ S.Tv) K₀) := by
  obtain ⟨-, hQT, -, hUQ⟩ := S.c134Q_facts h1222 h517 hK₀G hTK₀
  obtain ⟨y₀, hy₀, hy₀N, hτ₀⟩ := S.exists_Lv_line
  obtain ⟨he2U, -⟩ := S.e2_q_mem_blockU h1222 h517 hK₀G hK₀p hTK₀ hchar hLvK₀ hy₀ hy₀N hτ₀
  refine ⟨hUQ he2U, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
  have h := S.conj_e2_of_mem_Tv (hQT hr)
  calc r * S.e2 = (r * S.e2 * r⁻¹) * r := by group
    _ = S.e2 * r := by rw [h]

end Setting

end CFSG.Quasithin.H13.A5
