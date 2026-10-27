module

public import CFSG.Quasithin.Background.G64Statement
public import CFSG.Quasithin.EmptyFaithful.S153EB6B

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecG.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

theorem realizesVia_beta_inj {D : FFModel} {U : Subgroup V}
    {β : ↥U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : V) ∈ (⊥ : Subgroup V))
    (u u' : ↥U) (huu : β u = β u') : u = u' := by
  have h1 : β (u * u'⁻¹) = 1 := by rw [map_mul, map_inv, huu, mul_inv_cancel]
  have h2 := Subgroup.mem_bot.1 ((hβk _).1 h1)
  exact mul_inv_eq_one.1 (Subtype.ext h2)

theorem orderOf_image_eq_three {D : FFModel} {K : Subgroup (MulAut V)} {U : Subgroup V}
    {π : D.Gam →* ↥K} (h : D.RealizesVia K U ⊥ π) {γ : D.Gam} (hγ3 : γ ^ 3 = 1)
    {m' : D.Amb} (hm'sec : m' ∈ D.sec) (hm' : D.act γ m' * m'⁻¹ ∉ D.ker) :
    orderOf ((π γ : ↥K) : MulAut V) = 3 := by
  obtain ⟨-, -, -, hU, -, hsec, -, β, hβs, -, hβe⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg3 : ((π γ : ↥K) : MulAut V) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hγ3, map_one]
    rfl
  refine orderOf_eq_prime hg3 fun hg1 => ?_
  obtain ⟨u', hu'⟩ := hβs (QuotientGroup.mk ⟨m', hm'sec⟩)
  have hu1 : ((π γ : ↥K) : MulAut V) (u' : V) ∈ U := hU _ _ u'.2
  have hm1 : D.act γ m' ∈ D.sec := hsec γ m' hm'sec
  have := hβe γ u' ⟨m', hm'sec⟩ hu1 hm1 hu'
  have hfix : (⟨((π γ : ↥K) : MulAut V) (u' : V), hu1⟩ : ↥U) = u' := by
    apply Subtype.ext
    simp [hg1]
  rw [hfix, hu'] at this
  apply hm'
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
  simpa [mul_comm] using this

theorem exists_order_three_fix_sec (D : FFModel) (K : Subgroup (MulAut V)) (U : Subgroup V)
    (π : D.Gam →* ↥K) (h : D.RealizesVia K U ⊥ π)
    (hmodel : ∀ m ∈ D.sec, ∃ γ : D.Gam, γ ^ 3 = 1 ∧ D.act γ m * m⁻¹ ∈ D.ker ∧
      ∃ m' ∈ D.sec, D.act γ m' * m'⁻¹ ∉ D.ker) {p : V} (hp : p ∈ U) :
    ∃ g ∈ K, orderOf g = 3 ∧ g p = p := by
  have h' := h
  obtain ⟨-, -, -, hU, -, hsec, -, β, -, hβk, hβe⟩ := h'
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨p, hp⟩)
  obtain ⟨γ, hγ3, hγm, m', hm'sec, hm'⟩ := hmodel (m : D.Amb) m.2
  refine ⟨((π γ : ↥K) : MulAut V), (π γ).2, orderOf_image_eq_three h hγ3 hm'sec hm', ?_⟩
  have hu1 : ((π γ : ↥K) : MulAut V) p ∈ U := hU _ _ hp
  have hm1 : D.act γ (m : D.Amb) ∈ D.sec := hsec γ m m.2
  have h1 := hβe γ ⟨p, hp⟩ m hu1 hm1 hm.symm
  have h2 : (QuotientGroup.mk m : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
      QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm1⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_comm] using hγm
  rw [← h2, hm] at h1
  exact congrArg Subtype.val (realizesVia_beta_inj (D := D) hβk _ _ h1)

theorem exists_orderOf_eq_three_sec {D : FFModel} {K : Subgroup (MulAut V)} {U : Subgroup V}
    {π : D.Gam →* ↥K} (h : D.RealizesVia K U ⊥ π) {γ : D.Gam} (hγ3 : γ ^ 3 = 1)
    {m' : D.Amb} (hm'sec : m' ∈ D.sec) (hm' : D.act γ m' * m'⁻¹ ∉ D.ker) :
    ∃ g ∈ K, orderOf g = 3 :=
  ⟨_, (π γ).2, orderOf_image_eq_three h hγ3 hm'sec hm'⟩

theorem card_sec_of_realizesVia_nat {K : Type} [Field K] [Finite K] (n : ℕ)
    {H : Subgroup (MulAut V)} {U : Subgroup V} {π : ↥(StatedSL n K) →* ↥H}
    (h : (FFModel.nat (StatedSL n K)).RealizesVia H U ⊥ π) : Nat.card U = Nat.card K ^ n := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  have e1 := Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)
  have e2 : Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin n → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin n → K))).subgroupOf ⊤) = Nat.card (Fin n → K) := by
    rw [← Subgroup.index_eq_card, Subgroup.bot_subgroupOf, Subgroup.index_bot, Subgroup.card_top]
    exact Nat.card_congr Multiplicative.toAdd
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at e2
  exact e1.trans e2

theorem fix_three_or_lin_two {Ki : Subgroup (MulAut V)} {U : Subgroup V}
    (hmt : G64.ModuleType Ki U) :
    BinaryNaturalSL Ki U ⊥ 2 1 ∨ ∀ p ∈ U, ∃ g ∈ Ki, orderOf g = 3 ∧ g p = p := by
  rcases hmt with ⟨n, hn2, -, K, instK, instKF, hK, π, hπ⟩ | ⟨n, hn5, -, π, hπ⟩ |
    ⟨n, hn, π, hπ⟩
  · by_cases hn3 : 3 ≤ n
    · right
      intro p hp
      refine exists_order_three_fix_sec (FFModel.nat (StatedSL n K)) Ki U π hπ
        (fun (m : Multiplicative (Fin n → K)) _ => ?_) hp
      obtain ⟨γ, hγ3, hγm, m', hm'⟩ := S153EB6.natSL_fix (K := K) (by simpa using hK) n hn3 m
      refine ⟨γ, hγ3, ?_, m', Subgroup.mem_top _, fun hmem => hm' ?_⟩
      · show natAct (StatedSL n K) γ m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (Fin n → K)))
        rw [hγm, mul_inv_cancel]
        exact one_mem _
      · exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem)
    · left
      have hn : n = 2 := by omega
      subst hn
      exact ⟨K, instK, instKF, hK, π, hπ⟩
  · right
    intro p hp
    refine exists_order_three_fix_sec (FFModel.symDn n) Ki U π hπ
      (fun (m : G6.PermMod n) _ => ?_) hp
    obtain ⟨γ, hγ3, hγm, m', hm'c, hm'⟩ := S153EB6.perm_cyc n hn5 m
    refine ⟨γ, hγ3, ?_, m', hm'c, fun hmem => hm' (Subgroup.mem_inf.1 hmem).1⟩
    show G6.permAct n γ m * m⁻¹ ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n
    rw [hγm, show m * m⁻¹ = 1 from mul_inv_cancel m]
    exact one_mem _
  · right
    have hn5 : 5 ≤ n := by omega
    intro p hp
    refine exists_order_three_fix_sec (G64.symCoreModel n) Ki U π hπ
      (fun (m : G6.PermMod n) _ => ?_) hp
    obtain ⟨γ, hγ3, hγm, m', hm'c, hm'⟩ := S153EB6.perm_cyc n hn5 m
    refine ⟨γ, hγ3, ?_, m', hm'c, fun hmem => hm' ?_⟩
    · show G6.permAct n γ m * m⁻¹ ∈ (⊥ : Subgroup (G6.PermMod n))
      rw [hγm, show m * m⁻¹ = 1 from mul_inv_cancel m]
      exact one_mem _
    · have h1 : G6.permAct n γ m' * m'⁻¹ = 1 := Subgroup.mem_bot.1 hmem
      rw [h1]
      exact one_mem _

end CFSG.Quasithin.Vol2.Ch10.SecG.C10E4
