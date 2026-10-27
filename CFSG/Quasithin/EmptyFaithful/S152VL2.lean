module

public import CFSG.Quasithin.EmptyFaithful.S152VL2a
public import CFSG.Quasithin.EmptyFaithful.S152VL2b
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32LeKOut
public import CFSG.Quasithin.EmptyFaithful.S152UTail

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open scoped commutatorElement

namespace S152V

theorem two_mul_ne_psl2_order {p N : ℕ} (hp : p.Prime) (hN : N = 360 ∨ N = 2520) :
    2 * N ≠ p * (p ^ 2 - 1) := by
  intro h
  have hp20 : p ≤ 20 := by
    by_contra hc
    push Not at hc
    have h1 : 21 * 440 ≤ p * (p ^ 2 - 1) := by
      apply Nat.mul_le_mul hc
      have : 441 ≤ p ^ 2 := by nlinarith
      omega
    rcases hN with rfl | rfl <;> omega
  interval_cases p
  all_goals first
    | (rcases hN with rfl | rfl <;> omega)
    | exact absurd hp (by norm_num)

theorem card_alternatingGroup_six' : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_alternatingGroup_seven' : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem exists_psl2_equiv {X : Type} [Group X] {p : ℕ} (h : StatedClassicalModel X .PSL 2 p 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
      Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := h
  exact ⟨F, hF, hFin, by simpa using hcard,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩

section Action

variable {G : Type} [Group G]

theorem inducesInner_of_cases_l2p {L : Subgroup G} {z : G} (hcases : Lemma115Cases L z) {p : ℕ}
    (hp : p.Prime) (hmodel : StatedClassicalModel L .PSL 2 p 1) (hp2 : p ≠ 2) : InducesInner z L := by
  have hZ : Subgroup.center ↥L = ⊥ := CFSG.Quasithin.F420.center_eq_bot_of_statedPSL hmodel
  have hcard : 2 * Nat.card ↥L = p * (p ^ 2 - 1) :=
    CFSG.Quasithin.F420.two_mul_card_of_statedPSL_two_odd hp hp2 hmodel
  have hcardL : ∀ n : ℕ, Nat.card (↥L ⧸ Subgroup.center ↥L) = n → Nat.card ↥L = n := by
    intro n hn
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L), hn, hZ, Subgroup.card_bot,
      mul_one]
  rcases hcases with ⟨-, -, h⟩ | ⟨-, -, -, h⟩ | ⟨φ, -, -, -, -⟩ | ⟨φ, -, -, -, -⟩ | ⟨-, h⟩ | ⟨-, l, hl, h, -⟩
  · exact h
  · exact h
  · exfalso
    have h6 := hcardL 360 (by rw [Nat.card_congr φ.toEquiv]; exact card_alternatingGroup_six')
    exact two_mul_ne_psl2_order hp (Or.inl rfl) (by rw [← h6]; exact hcard)
  · exfalso
    have h7 := hcardL 2520 (by rw [Nat.card_congr φ.toEquiv]; exact card_alternatingGroup_seven')
    exact two_mul_ne_psl2_order hp (Or.inr rfl) (by rw [← h7]; exact hcard)
  · exact h
  · exact ⟨l, hl, h⟩

theorem inner_involution_data {L : Subgroup G} {z : G} (hZ : Subgroup.center ↥L = ⊥) (hz2 : z ^ 2 = 1)
    (hcomm : ⁅L, Subgroup.zpowers z⁆ = L) (hL1 : L ≠ ⊥) (hin : InducesInner z L) :
    ∃ l ∈ L, l ≠ 1 ∧ l * l = 1 ∧ ∀ x ∈ L, z⁻¹ * x * z = l * x * l := by
  obtain ⟨l, hl, h⟩ := hin
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hll : l * l = 1 := by
    have hc : ∀ x ∈ L, (l * l) * x = x * (l * l) := by
      intro x hx
      have hy : z⁻¹ * x * z = l⁻¹ * x * l := h x hx
      have hyL : l⁻¹ * x * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
      have h1 : z⁻¹ * (z⁻¹ * x * z) * z = x := by
        rw [hzinv]
        calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
          _ = x := by rw [hzz]; group
      have h2 : z⁻¹ * (z⁻¹ * x * z) * z = l⁻¹ * (l⁻¹ * x * l) * l := by
        rw [hy]
        exact h _ hyL
      have h3 : x = (l * l)⁻¹ * x * (l * l) := by
        calc x = l⁻¹ * (l⁻¹ * x * l) * l := h1.symm.trans h2
          _ = (l * l)⁻¹ * x * (l * l) := by group
      calc (l * l) * x = (l * l) * ((l * l)⁻¹ * x * (l * l)) := by rw [← h3]
        _ = x * (l * l) := by group
    have hmem : (⟨l * l, L.mul_mem hl hl⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [hZ] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  have hlinv : l⁻¹ = l := inv_eq_of_mul_eq_one_right hll
  refine ⟨l, hl, ?_, hll, fun x hx => by rw [h x hx, hlinv]⟩
  intro hl1
  apply hL1
  rw [← le_bot_iff, ← hcomm]
  refine (Subgroup.commutator_le).2 fun g₁ hg₁ g₂ hg₂ => ?_
  have hc1 : g₁ * z = z * g₁ := by
    have := h g₁ hg₁
    rw [hl1] at this
    simp only [inv_one, one_mul, mul_one] at this
    calc g₁ * z = z * (z⁻¹ * g₁ * z) := by group
      _ = z * g₁ := by rw [this]
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2 ((Commute.zpow_right (show Commute g₁ z from hc1) n).eq)

end Action

section Centralize

variable {G : Type} [Group G] [Finite G]

theorem odd_centralizes_of_inner_involution {L : Subgroup G} {z l k : G} {p : ℕ}
    (hFM : IsFermatOrMersennePrime p) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p)
    (e : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) (hZ : Subgroup.center ↥L = ⊥)
    (hAut : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L) (hl : l ∈ L) (hl1 : l ≠ 1) (hll : l * l = 1)
    (hlz : ∀ x ∈ L, z⁻¹ * x * z = l * x * l) (hkN : k ∈ Subgroup.normalizer (L : Set G))
    (hkz : k * z = z * k) (hodd : Odd (orderOf k)) : ∀ x ∈ L, k * x = x * k := by
  have hlinv : l⁻¹ = l := inv_eq_of_mul_eq_one_right hll
  let lL : ↥L := ⟨l, hl⟩
  have hlL2 : lL ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hll)
  have hlL1 : lL ≠ 1 := fun h => hl1 (congrArg Subtype.val h)
  have hZ' : ∀ c : ↥L, (∀ y, c * y = y * c) → c = 1 := by
    intro c hc
    have hmem : c ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hc g).symm
    rw [hZ] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hP : ∀ g : ↥L, g * lL = lL * g → Odd (orderOf g) → g = 1 := fun g hg hgodd =>
    eq_one_of_commute_odd hFM hF e hlL2 hlL1 hg hgodd
  let kN : ↥(Subgroup.normalizer (L : Set G)) := ⟨k, hkN⟩
  let α : MulAut ↥L := L.normalizerMonoidHom kN
  have hα_apply : ∀ x : ↥L, ((α x : ↥L) : G) = k * (x : G) * k⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L kN x
  have hαodd : Odd (orderOf α) := by
    have h1 : orderOf α ∣ orderOf kN := orderOf_map_dvd L.normalizerMonoidHom kN
    have h2 : orderOf kN = orderOf k := Subgroup.orderOf_mk k hkN
    exact Odd.of_dvd_nat (h2 ▸ hodd) h1
  have hkzC : Commute k z := hkz
  have hzkC : Commute z k := hkz.symm
  have hc : α * MulAut.conj lL = MulAut.conj lL * α := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    have hxL : (x : G) ∈ L := x.2
    have hkxL : k * (x : G) * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hkN _).1 hxL
    have lhs : (((α * MulAut.conj lL) x : ↥L) : G) = k * (l * (x : G) * l⁻¹) * k⁻¹ := by
      rw [MulAut.mul_apply, hα_apply]
      simp [MulAut.conj_apply, lL]
    have rhs : (((MulAut.conj lL * α) x : ↥L) : G) = l * (k * (x : G) * k⁻¹) * l⁻¹ := by
      rw [MulAut.mul_apply]
      simp [MulAut.conj_apply, hα_apply, lL]
    rw [lhs, rhs]
    have h1 : l * (x : G) * l⁻¹ = z⁻¹ * (x : G) * z := by rw [hlz _ hxL, hlinv]
    have h2 : l * (k * (x : G) * k⁻¹) * l⁻¹ = z⁻¹ * (k * (x : G) * k⁻¹) * z := by
      rw [hlz _ hkxL, hlinv]
    rw [h1, h2]
    have hc1 : k * z⁻¹ = z⁻¹ * k := (Commute.inv_right hkzC).eq
    have hc2 : z * k⁻¹ = k⁻¹ * z := (Commute.inv_right hzkC).eq
    calc k * (z⁻¹ * (x : G) * z) * k⁻¹ = (k * z⁻¹) * (x : G) * (z * k⁻¹) := by group
      _ = (z⁻¹ * k) * (x : G) * (k⁻¹ * z) := by rw [hc1, hc2]
      _ = z⁻¹ * (k * (x : G) * k⁻¹) * z := by group
  have hα1 : α = 1 := odd_order_aut_eq_one hZ' hAut lL hP α hαodd hc
  intro x hx
  have h1 : ((α ⟨x, hx⟩ : ↥L) : G) = ((⟨x, hx⟩ : ↥L) : G) := by rw [hα1]; rfl
  rw [hα_apply] at h1
  have h2 : k * x * k⁻¹ = x := h1
  calc k * x = (k * x * k⁻¹) * k := by group
    _ = x * k := by rw [h2]

end Centralize

end S152V

open S152V in
theorem tail15215L2p_of (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) : Tail15215L2p := by
  intro G _ _ I S Mi L L₀ K P z cfg hex
  obtain ⟨p, hFM, hmodel⟩ := hex
  have hp : p.Prime := hFM.1
  have hp2 : p ≠ 2 := fm_ne_two hFM
  have hp3 : p ≠ 3 := by
    obtain ⟨-, -, -, -, hne3⟩ := hmodel.1
    exact fun h => hne3 (by simp [h])
  have h3 : 3 < p := by have := hp.two_le; omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_psl2_equiv hmodel
  have hZ : Subgroup.center ↥L = ⊥ := CFSG.Quasithin.F420.center_eq_bot_of_statedPSL hmodel
  have hcard : 2 * Nat.card ↥L = p * (p ^ 2 - 1) :=
    CFSG.Quasithin.F420.two_mul_card_of_statedPSL_two_odd hp hp2 hmodel
  have hheven : 2 ∣ p * (p ^ 2 - 1) := Dvd.intro _ hcard
  have hAut : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L := by
    have h1 := CFSG.QuasithinUnique.DoubleA3.card_mulAut_psl2_le_two_mul F hp hodd hF h3 hheven
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
    exact h1
  have hL1 : L ≠ ⊥ := by
    intro hL
    rw [hL, Subgroup.card_bot] at hcard
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    have h24 : 3 * 8 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul h3.le (by omega)
    omega
  have hin : InducesInner z L := inducesInner_of_cases_l2p cfg.cases hp hmodel hp2
  obtain ⟨l, hl, hl1, hll, hlz⟩ := inner_involution_data hZ cfg.z2 cfg.comm hL1 hin
  have hKI : K ≤ I := fun x hx => by
    have := cfg.K_le hx
    rw [cfg.hMi] at this
    exact this.1
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨horb, h2⟩ := hA3 G I S L cfg.sqtk cfg.sylow (Id2519.mem_cComp_of_isComponentIn cfg.comp)
    have h2' : (∀ t ∈ S, t ∈ Subgroup.normalizer (L : Set G)) ∨
        ∃ t ∈ S, conjSubgroupsBy S L = {L, conjByElt t L} := by
      rcases h2 with h | ⟨t, ht, -, h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, ht, h⟩
    obtain ⟨t, ht, hcos⟩ := exists_two_cosets cfg.sylow.1 horb h2'
    exact oTwoUpper_le_of_two_cosets hKI cfg.K_o2 ht hcos
  have hKC : K ≤ Subgroup.centralizer (L : Set G) := by
    refine cfg.K_o2.le.trans ((Subgroup.closure_le _).mpr fun k hk => ?_)
    have hkN : k ∈ Subgroup.normalizer (L : Set G) := hKN hk.1
    have hkz : k * z = z * k := by
      have hkMi := cfg.K_le hk.1
      rw [cfg.hMi] at hkMi
      exact (Subgroup.mem_centralizer_iff.1 hkMi.2 z (Set.mem_singleton z)).symm
    have hcomm := odd_centralizes_of_inner_involution hFM hF e hZ hAut hl hl1 hll hlz hkN hkz hk.2
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcomm x hx).symm
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.1 (hKC hk) x hx).symm

end CFSG.Quasithin
