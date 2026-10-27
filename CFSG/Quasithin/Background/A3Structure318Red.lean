
module

public import CFSG.Quasithin.Background.A3Structure320Core
public import CFSG.Quasithin.Background.A3Structure318Defs

public section

namespace CFSG.Quasithin

namespace A318

open CFSG.Open CFSG.SectionRank CFSG.Quasithin.A320
open scoped commutatorElement

theorem le_of_centralizes_of_pow_eq_one {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {L : Subgroup G} (hL : 2 ≤ CFSG.Open.pRank p L)
    (hG : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 2) {c : G} (hc : ∀ l ∈ L, c * l = l * c)
    (hcp : c ^ p = 1) : c ∈ L := by
  by_cases hc1 : c = 1
  · rw [hc1]
    exact L.one_mem
  obtain ⟨E, hEL, hEel, hEcard⟩ := exists_pRank hp.out.one_lt L
  by_contra hcL
  have hcE : c ∉ E := fun h => hcL (hEL h)
  have hord : orderOf c = p := orderOf_eq_prime hcp hc1
  have hmain := pRank_add_le (⊥ : Subgroup G) (by simpa [Nat.dvd_one] using hp.out.ne_one)
    (X := Subgroup.zpowers c) (E := E)
    (isElemAbelian_zpowers hcp) hEel
    (fun x hx e he => by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h1 : Commute c e := hc e (hEL he)
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (h1.zpow_left n).eq)
    (fun x hx e he hxe => by
      have hxe1 : x * e = 1 := Subgroup.mem_bot.1 hxe
      have hxE : x ∈ E := by
        have : x = e⁻¹ := eq_inv_of_mul_eq_one_left hxe1
        rw [this]
        exact E.inv_mem he
      have hx1 : x = 1 := by
        by_contra hx1
        exact hcE (Subgroup.zpowers_le.2 hxE (mem_zpowers_of_mem_zpowers_prime hord hx hx1))
      rw [hx1, one_mul] at hxe1
      exact ⟨hx1, hxe1⟩)
    (a := 1) (b := CFSG.Open.pRank p L)
    (by simp [Nat.card_zpowers, hord]) hEcard
  omega

theorem eq_one_of_centralizes {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {S : Subgroup G} [S.Normal] (hS2 : 2 ≤ CFSG.Open.pRank p S)
    (hG : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 2)
    (hZ : ∀ z ∈ S, (∀ s ∈ S, z * s = s * z) → z = 1) (hO : CFSG.pPrimeCore p G = ⊥)
    {c : G} (hc : ∀ s ∈ S, c * s = s * c) : c = 1 := by
  have hCn : (Subgroup.centralizer (S : Set G)).Normal := ⟨fun c hc g => by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by simpa using Subgroup.Normal.conj_mem ‹S.Normal› s hs g⁻¹
    have h1 := Subgroup.mem_centralizer_iff.1 hc (g⁻¹ * s * g) hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * s := by group⟩
  have hcop : Nat.Coprime p (Nat.card (Subgroup.centralizer (S : Set G))) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hdvd
    obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hc'p : (c' : G) ^ p = 1 := by
      have := pow_orderOf_eq_one c'
      rw [hc'] at this
      exact congrArg Subtype.val this
    have hcomm : ∀ l ∈ S, (c' : G) * l = l * (c' : G) := fun l hl =>
      (Subgroup.mem_centralizer_iff.1 c'.2 l hl).symm
    have hmem : (c' : G) ∈ S := le_of_centralizes_of_pow_eq_one hS2 hG hcomm hc'p
    have h1 : (c' : G) = 1 := hZ _ hmem hcomm
    have h2 : c' = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hc'
    exact hp.out.one_lt.ne hc'
  have hle : Subgroup.centralizer (S : Set G) ≤ CFSG.pPrimeCore p G := le_sSup ⟨hCn, hcop⟩
  rw [hO] at hle
  exact Subgroup.mem_bot.1 (hle (Subgroup.mem_centralizer_iff.2 fun s hs => (hc s hs).symm))

theorem closure_orderThree_eq {X : Type*} [Group X] [Finite X] (hS : CFSG.IsQuasisimple X)
    (hZ : Nat.card (Subgroup.center X) ≤ 3) (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) :
    Subgroup.closure {y : X | orderOf y = 3} = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hperf, hsimple, -⟩ := hS
  set T₀ : Subgroup X := Subgroup.closure {y : X | orderOf y = 3} with hT₀
  have hT₀n : T₀.Normal := ⟨fun n hn g => by
    refine Subgroup.closure_induction (p := fun n _ => g * n * g⁻¹ ∈ T₀) ?_ ?_ ?_ ?_ hn
    · intro y hy
      apply Subgroup.subset_closure
      show orderOf (g * y * g⁻¹) = 3
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
      simpa using this.trans hy
    · simp
    · intro x y _ _ hx hy
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact T₀.mul_mem hx hy
    · intro x _ hx
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact T₀.inv_mem hx⟩
  obtain ⟨E, -, hEel, hEcard⟩ := exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  have hcardE : 9 ≤ Nat.card E := by
    rw [hEcard]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup X) := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨e, heE, heZ⟩ : ∃ e ∈ E, e ∉ Subgroup.center X := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.center X := hcon
    have h1 := Subgroup.card_le_of_le hle
    omega
  have hy3 : orderOf e = 3 := by
    have he1 : e ≠ 1 := fun h => heZ (h ▸ Subgroup.one_mem _)
    exact orderOf_eq_prime (hEel.2 e heE) he1
  have hyT : e ∈ T₀ := Subgroup.subset_closure hy3
  have hQ : T₀ ⊔ Subgroup.center X = ⊤ := by
    have h1 : (T₀.map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
      Subgroup.Normal.map hT₀n _ (QuotientGroup.mk'_surjective _)
    have := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (T₀.map (QuotientGroup.mk' (Subgroup.center X))) with h | h
    · exfalso
      have hy1 : QuotientGroup.mk' (Subgroup.center X) e ∈
          T₀.map (QuotientGroup.mk' (Subgroup.center X)) := ⟨_, hyT, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy1
      exact heZ hy1
    · have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center X)) T₀
      rw [h, QuotientGroup.ker_mk', Subgroup.comap_top] at h2
      exact h2.symm
  have hcomm : ∀ a b : X ⧸ T₀, a * b = b * a := by
    intro a b
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨s', rfl⟩ := QuotientGroup.mk_surjective b
    have hs : s ∈ T₀ ⊔ Subgroup.center X := hQ ▸ Subgroup.mem_top s
    obtain ⟨t, ht, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hs
    have h1 : (QuotientGroup.mk (t * z) : X ⧸ T₀) = QuotientGroup.mk z := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t).2 ht, one_mul]
    rw [h1, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz s']
  have hcom : commutator X = ⊤ := Group.isPerfect_def.1 hperf
  have hle : commutator X ≤ T₀ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have h1 : QuotientGroup.mk' T₀ ⁅g₁, g₂⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
    exact (QuotientGroup.eq_one_iff _).1 h1
  exact top_unique (hcom ▸ hle)

theorem le_thetaOf {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hS : CFSG.IsQuasisimple ↥S) (hZ : Nat.card (Subgroup.center ↥S) ≤ 3)
    (h2 : 2 ≤ CFSG.Open.pRank 3 S) : S ≤ thetaOf (⊤ : Subgroup G) := by
  have h2' : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥S) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [pRank_top_subtype (p := 3) S]
    exact h2
  have hT₀top := closure_orderThree_eq hS hZ h2'
  intro s hs
  have hsT : (⟨s, hs⟩ : ↥S) ∈ Subgroup.closure {y : ↥S | orderOf y = 3} :=
    hT₀top ▸ Subgroup.mem_top _
  refine Subgroup.closure_induction
    (p := fun (y : ↥S) _ => (y : G) ∈ thetaOf (⊤ : Subgroup G)) ?_ ?_ ?_ ?_ hsT
  · intro y hy
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, (Subgroup.orderOf_coe y).trans hy⟩
  · exact Subgroup.one_mem _
  · intro x y _ _ hx hy
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    exact Subgroup.inv_mem _ hx

theorem a318_reduced (hF : A318Facts) {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hO : CFSG.pPrimeCore p G = ⊥) (hG : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 2)
    {S : Subgroup G} [S.Normal] (hS : CFSG.IsQuasisimple ↥S) (h2 : 2 ≤ CFSG.Open.pRank p S)
    (hZ1 : Subgroup.center ↥S = ⊥ → A23List ↥S)
    (hZ2 : Subgroup.center ↥S ≠ ⊥ →
      p = 3 ∧ Nat.card (Subgroup.center ↥S) = 3 ∧ A36Case2List ↥S) :
    S = oPrimeResidualOf p ⊤ ∨ (p = 3 ∧ A318Case2 S) ∨
      (p = 3 ∧ A318Case3Group ↥S ∧ (S = thetaOf (⊤ : Subgroup G) ∨ A318Case3b S)) := by
  by_cases hZ : Subgroup.center ↥S = ⊥
  ·
    have hsimple : IsSimpleGroup ↥S := by
      have : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hS.2.1
      exact (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
        ).isSimpleGroup
    have hZ' : ∀ z ∈ S, (∀ s ∈ S, z * s = s * z) → z = 1 := by
      intro z hz hc
      have : (⟨z, hz⟩ : ↥S) ∈ Subgroup.center ↥S :=
        Subgroup.mem_center_iff.2 fun g => (Subtype.ext (hc g g.2)).symm
      rw [hZ, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hC : ∀ c : G, (∀ s ∈ S, c * s = s * c) → c = 1 := fun c hc =>
      eq_one_of_centralizes h2 hG hZ' hO hc
    rcases hF.aut p hp.out hp2 G S hC hsimple (hZ1 hZ) h2 hG with h | ⟨hp3, h⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl ⟨hp3, h⟩)
  ·
    obtain ⟨hp3, hcard, hlist⟩ := hZ2 hZ
    subst hp3
    refine Or.inr (Or.inr ⟨rfl, hF.center ↥S hlist hcard, ?_⟩)
    by_cases hx : ∃ x : G, orderOf x = 3 ∧ x ∉ S
    · obtain ⟨x, hx3, hxS⟩ := hx
      exact Or.inr (hF.central G S hS hcard hlist hO h2 hG x hx3 hxS)
    · left
      push Not at hx
      refine le_antisymm (le_thetaOf hS hcard.le h2) ((Subgroup.closure_le S).2 ?_)
      rintro x ⟨-, hx3⟩
      exact hx x hx3

end A318

end CFSG.Quasithin
