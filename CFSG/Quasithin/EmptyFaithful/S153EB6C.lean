module

public import CFSG.Quasithin.EmptyFaithful.S153E52In
public import CFSG.Quasithin.EmptyFaithful.S153EB6B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace S153EB6

theorem exists_order_three_fix {V : Type} [CommGroup V] (D : FFModel) (G : Subgroup (MulAut V))
    (π : D.Gam →* ↥G) (h : D.RealizesVia G ⊤ ⊥ π)
    (hmodel : ∀ m ∈ D.sec, ∃ γ : D.Gam, γ ^ 3 = 1 ∧ D.act γ m * m⁻¹ ∈ D.ker ∧
      ∃ m' ∈ D.sec, D.act γ m' * m'⁻¹ ∉ D.ker) (p : V) :
    ∃ g ∈ G, orderOf g = 3 ∧ g p = p := by
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  have hinj : ∀ u u' : ↥(⊤ : Subgroup V), β u = β u' → u = u' := by
    intro u u' huu
    have h1 : β (u * u'⁻¹) = 1 := by rw [map_mul, map_inv, huu, mul_inv_cancel]
    have h2 := Subgroup.mem_bot.1 ((hβk _).1 h1)
    exact mul_inv_eq_one.1 (Subtype.ext h2)
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨p, Subgroup.mem_top p⟩)
  obtain ⟨γ, hγ3, hγm, m', hm'sec, hm'⟩ := hmodel (m : D.Amb) m.2
  have hmk : ∀ (x : ↥D.sec) (y : D.Amb) (hy : y ∈ D.sec), y * (x : D.Amb)⁻¹ ∈ D.ker →
      (QuotientGroup.mk x : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk ⟨y, hy⟩ := by
    intro x y hy hker
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_comm] using hker
  have hmk' : ∀ (x : ↥D.sec) (y : D.Amb) (hy : y ∈ D.sec),
      (QuotientGroup.mk x : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk ⟨y, hy⟩ →
      y * (x : D.Amb)⁻¹ ∈ D.ker := by
    intro x y hy hq
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
    simpa [mul_comm] using hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg3 : ((π γ : ↥G) : MulAut V) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hγ3, map_one]
    rfl
  refine ⟨((π γ : ↥G) : MulAut V), (π γ).2, orderOf_eq_prime hg3 ?_, ?_⟩
  · intro hg1
    obtain ⟨u', hu'⟩ := hβs (QuotientGroup.mk ⟨m', hm'sec⟩)
    have hu1 : ((π γ : ↥G) : MulAut V) (u' : V) ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
    have hm1 : D.act γ m' ∈ D.sec := hsec γ m' hm'sec
    have := hβe γ u' ⟨m', hm'sec⟩ hu1 hm1 hu'
    have hfix : (⟨((π γ : ↥G) : MulAut V) (u' : V), hu1⟩ : ↥(⊤ : Subgroup V)) = u' := by
      apply Subtype.ext
      simp [hg1]
    rw [hfix, hu'] at this
    exact hm' (hmk' _ _ _ this)
  · have hu1 : ((π γ : ↥G) : MulAut V) p ∈ (⊤ : Subgroup V) := Subgroup.mem_top _
    have hm1 : D.act γ (m : D.Amb) ∈ D.sec := hsec γ m m.2
    have h1 := hβe γ ⟨p, Subgroup.mem_top p⟩ m hu1 hm1 hm.symm
    have h2 := hmk m (D.act γ (m : D.Amb)) hm1 hγm
    rw [← h2, hm] at h1
    exact congrArg Subtype.val (hinj _ _ h1)

theorem moduleType_top {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {a : MulAut V}
    (hc : G64.Conclusion G a)
    (hT : ∃ T, IsSylowTwoOf T G ∧ a ∈ T ∧ ∀ x ∈ T, x * a = a * x) : G64.ModuleType G ⊤ := by
  obtain ⟨s, Ks, -, hsup, -, -, hV, -, -, -, -, hmod, -, h4⟩ := hc
  obtain ⟨hs1, hG, -⟩ := h4 hT
  subst hs1
  have hK0 : Ks 0 = G := by
    have := (iSup_unique (f := Ks)).symm.trans hsup
    rw [← hG] at this
    exact this
  have hV0 : commV (Ks 0) = ⊤ := by
    have := (iSup_unique (f := fun i => commV (Ks i))).symm.trans hV
    exact this
  have h0 := hmod 0
  rw [hV0, hK0] at h0
  exact h0

theorem card_of_realizes_nat {V : Type} [CommGroup V] {K : Type} [Field K] [Finite K] (n : ℕ)
    (G : Subgroup (MulAut V)) (h : (FFModel.nat (StatedSL n K)).Realizes G ⊤ ⊥) :
    Nat.card V = Nat.card K ^ n := by
  obtain ⟨π, -, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  have e1 := Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)
  rw [Subgroup.card_top] at e1
  have e2 : Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin n → K))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin n → K))).subgroupOf ⊤) = Nat.card (Fin n → K) := by
    rw [← Subgroup.index_eq_card, Subgroup.bot_subgroupOf, Subgroup.index_bot, Subgroup.card_top]
    exact Nat.card_congr Multiplicative.toAdd
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at e2
  exact e1.trans e2

theorem input15352_main (h : G64.LemmaG64) : Input15352 := by
  intro V instC instF hexp G a hyp hcard hT hno
  have hmt := moduleType_top (h V hexp G a hyp hcard) hT
  obtain ⟨p, hp⟩ : ∃ p : V, ∀ w ∈ commV (Subgroup.zpowers a), w = 1 ∨ w = p := by
    obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : ↥(commV (Subgroup.zpowers a)))).1 hcard
    refine ⟨(y : V), fun w hw => ?_⟩
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · refine Or.inr ?_
      have := hyu ⟨w, hw⟩ (fun h' => hw1 (congrArg Subtype.val h'))
      exact congrArg Subtype.val this
  have key : ∀ g ∈ G, orderOf g = 3 → g p = p → False := by
    intro g hg hg3 hgp
    obtain ⟨w, hw, hgw⟩ := hno g hg hg3
    rcases hp w hw with rfl | rfl
    · exact hgw (map_one g)
    · exact hgw hgp
  rcases hmt with ⟨n, hn2, hn5, K, instK, instKF, hK, hreal⟩ | ⟨n, hn5, hn8, hreal⟩ |
    ⟨n, hn, hreal⟩
  · by_cases hn3 : 3 ≤ n
    · exfalso
      obtain ⟨π, hπ⟩ := hreal
      obtain ⟨g, hg, hg3, hgp⟩ := exists_order_three_fix (FFModel.nat (StatedSL n K)) G π hπ
        (fun (m : Multiplicative (Fin n → K)) _ => by
          obtain ⟨γ, hγ3, hγm, m', hm'⟩ := natSL_fix (K := K) (by simpa using hK) n hn3 m
          refine ⟨γ, hγ3, ?_, m', Subgroup.mem_top _, fun hmem => hm' ?_⟩
          · show natAct (StatedSL n K) γ m * m⁻¹ ∈ (⊥ : Subgroup (Multiplicative (Fin n → K)))
            rw [hγm, mul_inv_cancel]
            exact one_mem _
          · exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 hmem)) p
      exact key g hg hg3 hgp
    · have hn : n = 2 := by omega
      subst hn
      rw [card_of_realizes_nat 2 G hreal, hK]
      norm_num
  · exfalso
    obtain ⟨π, hπ⟩ := hreal
    obtain ⟨g, hg, hg3, hgp⟩ := exists_order_three_fix (FFModel.symDn n) G π hπ
      (fun (m : G6.PermMod n) _ => by
        obtain ⟨γ, hγ3, hγm, m', hm'c, hm'⟩ := perm_cyc n hn5 m
        refine ⟨γ, hγ3, ?_, m', hm'c, fun hmem => hm' (Subgroup.mem_inf.1 hmem).1⟩
        show G6.permAct n γ m * m⁻¹ ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n
        rw [hγm, show m * m⁻¹ = 1 from mul_inv_cancel m]
        exact one_mem _) p
    exact key g hg hg3 hgp
  · exfalso
    have hn5 : 5 ≤ n := by omega
    obtain ⟨π, hπ⟩ := hreal
    obtain ⟨g, hg, hg3, hgp⟩ := exists_order_three_fix (G64.symCoreModel n) G π hπ
      (fun (m : G6.PermMod n) _ => by
        obtain ⟨γ, hγ3, hγm, m', hm'c, hm'⟩ := perm_cyc n hn5 m
        refine ⟨γ, hγ3, ?_, m', hm'c, fun hmem => hm' ?_⟩
        · show G6.permAct n γ m * m⁻¹ ∈ (⊥ : Subgroup (G6.PermMod n))
          rw [hγm, show m * m⁻¹ = 1 from mul_inv_cancel m]
          exact one_mem _
        · have h1 : G6.permAct n γ m' * m'⁻¹ = 1 := Subgroup.mem_bot.1 hmem
          rw [h1]
          exact one_mem _) p
    exact key g hg hg3 hgp

end S153EB6

namespace S153E

theorem input15352_of_lemmaG64 (h : G64.LemmaG64) : Input15352 :=
  S153EB6.input15352_main h

end S153E

end CFSG.Quasithin
