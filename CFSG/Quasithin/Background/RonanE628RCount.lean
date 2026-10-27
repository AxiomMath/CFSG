module

public import CFSG.Open.LocalVocabulary
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin.RonanE628

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem rc_conj_eq_iff_comm {H : Type} [Group H] (a b v : H) :
    a * v * a⁻¹ = b * v * b⁻¹ ↔ (a⁻¹ * b) * v = v * (a⁻¹ * b) := by
  constructor
  · intro h
    have e : (a⁻¹ * b) * v * (a⁻¹ * b)⁻¹ = v := by
      calc (a⁻¹ * b) * v * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * v * b⁻¹) * a := by group
        _ = a⁻¹ * (a * v * a⁻¹) * a := by rw [h]
        _ = v := by group
    calc (a⁻¹ * b) * v = ((a⁻¹ * b) * v * (a⁻¹ * b)⁻¹) * (a⁻¹ * b) := by group
      _ = v * (a⁻¹ * b) := by rw [e]
  · intro h
    have e : b * v * b⁻¹ = a * ((a⁻¹ * b) * v * (a⁻¹ * b)⁻¹) * a⁻¹ := by group
    rw [e, h, mul_inv_cancel_right]

theorem rc_transitive {K V P : Subgroup G} (hVP : V ≤ P)
    (htr : ∀ p ∈ P, ∀ q ∈ P, p ≠ 1 → q ≠ 1 → ∃ k ∈ K, k⁻¹ * p * k = q)
    (hTI : ∀ g ∈ K, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSubgroup V g = ⊥)
    {v w : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hw : w ∈ V) (hw1 : w ≠ 1) :
    ∃ n ∈ K ⊓ Subgroup.normalizer (V : Set G), n⁻¹ * v * n = w := by
  obtain ⟨k, hkK, hk⟩ := htr v (hVP hv) w (hVP hw) hv1 hw1
  have hkV : k * w * k⁻¹ = v := by
    rw [← hk]
    group
  have hkN : k ∈ Subgroup.normalizer (V : Set G) := by
    by_contra hn
    have hbot := hTI k hkK hn
    have hkVmem : k * w * k⁻¹ ∈ V := by
      rw [hkV]
      exact hv
    have hmem : w ∈ V ⊓ conjSubgroup V k :=
      Subgroup.mem_inf.2 ⟨hw, mem_conjSubgroup_iff.2 hkVmem⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hw1 hmem
  exact ⟨k, Subgroup.mem_inf.2 ⟨hkK, hkN⟩, hk⟩

theorem rc_card_sub_one_dvd {N V : Subgroup G} {v₀ : G} (hv₀V : v₀ ∈ V) (hv₀1 : v₀ ≠ 1)
    (htrN : ∀ w ∈ V, w ≠ 1 → ∃ n ∈ N, n⁻¹ * v₀ * n = w)
    (hNV : N ≤ Subgroup.normalizer (V : Set G)) :
    (Nat.card V - 1) ∣ Nat.card N := by
  have h1V : (1 : G) ∈ (V : Set G) := one_mem V
  have hcardS : Nat.card ↥((V : Set G) \ {1}) = Nat.card V - 1 := by
    show Nat.card ↥((V : Set G) \ {1}) = Nat.card ↥(V : Set G) - 1
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem h1V]
  obtain ⟨Cn, hCn⟩ : ∃ C : Subgroup N,
      ∀ x : N, x ∈ C ↔ (x : G) ∈ Subgroup.centralizer ({v₀} : Set G) :=
    ⟨(Subgroup.centralizer ({v₀} : Set G)).subgroupOf N, fun x => Subgroup.mem_subgroupOf⟩
  have hψ : ∀ n : N, (n : G) * v₀ * (n : G)⁻¹ ∈ (V : Set G) \ {1} := by
    intro n
    have hn : (n : G) ∈ Subgroup.normalizer (V : Set G) := hNV n.2
    refine ⟨(Subgroup.mem_set_normalizer_iff.1 hn v₀).1 hv₀V, fun h => hv₀1 ?_⟩
    have h' : (n : G) * v₀ * (n : G)⁻¹ = 1 := Set.mem_singleton_iff.1 h
    calc v₀ = (n : G)⁻¹ * ((n : G) * v₀ * (n : G)⁻¹) * (n : G) := by group
      _ = 1 := by rw [h']; group
  let ψ : N → ↥((V : Set G) \ {1}) := fun n => ⟨(n : G) * v₀ * (n : G)⁻¹, hψ n⟩
  have hcompat : ∀ a b : N, (QuotientGroup.leftRel Cn) a b → ψ a = ψ b := by
    intro a b hab
    have hab' : a⁻¹ * b ∈ Cn := QuotientGroup.leftRel_apply.1 hab
    rw [hCn, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.mem_centralizer_iff] at hab'
    have hc : v₀ * ((a : G)⁻¹ * (b : G)) = ((a : G)⁻¹ * (b : G)) * v₀ :=
      hab' v₀ (Set.mem_singleton v₀)
    apply Subtype.ext
    exact (rc_conj_eq_iff_comm (a : G) (b : G) v₀).2 hc.symm
  let f : (N ⧸ Cn) → ↥((V : Set G) \ {1}) :=
    Quotient.lift (s := QuotientGroup.leftRel Cn) ψ hcompat
  have hbij : Function.Bijective f := by
    constructor
    · intro q₁ q₂ hq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₁
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q₂
      have hψab : ψ a = ψ b := hq
      have hv : (a : G) * v₀ * (a : G)⁻¹ = (b : G) * v₀ * (b : G)⁻¹ :=
        congrArg Subtype.val hψab
      apply QuotientGroup.eq.2
      rw [hCn, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact ((rc_conj_eq_iff_comm (a : G) (b : G) v₀).1 hv).symm
    · intro w
      obtain ⟨n, hnN, hn⟩ := htrN w.1 w.2.1 (fun h => w.2.2 (Set.mem_singleton_iff.2 h))
      refine ⟨QuotientGroup.mk (⟨n⁻¹, N.inv_mem hnN⟩ : N), Subtype.ext ?_⟩
      show (n⁻¹ : G) * v₀ * (n⁻¹ : G)⁻¹ = (w : G)
      rw [inv_inv]
      exact hn
  have hcardq : Nat.card (N ⧸ Cn) = Nat.card ↥((V : Set G) \ {1}) :=
    Nat.card_congr (Equiv.ofBijective f hbij)
  rw [← hcardS, ← hcardq, Subgroup.card_eq_card_quotient_mul_card_subgroup Cn]
  exact dvd_mul_right _ _

theorem rc_exists_cyclic {N : Subgroup G} [IsCyclic N] {d : ℕ} (hd : d ∣ Nat.card N) :
    ∃ Y : Subgroup G, Y ≤ N ∧ IsCyclic Y ∧ Nat.card Y = d := by
  haveI : Nonempty N := ⟨1⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥N)
  have hn0 : Nat.card N ≠ 0 := (Nat.card_pos (α := ↥N)).ne'
  have hm0 : Nat.card N / d ≠ 0 := by
    intro h0
    have h1 : d * (Nat.card N / d) = Nat.card N := Nat.mul_div_cancel' hd
    rw [h0, mul_zero] at h1
    exact hn0 h1.symm
  have hmdvd : Nat.card N / d ∣ orderOf g := by
    rw [hg]
    exact Nat.div_dvd_of_dvd hd
  have horder : orderOf (g ^ (Nat.card N / d)) = d := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hg, Nat.div_div_self hd hn0]
  refine ⟨Subgroup.zpowers ((g ^ (Nat.card N / d) : N) : G),
    Subgroup.zpowers_le.2 (g ^ (Nat.card N / d)).2, inferInstance, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, horder]

set_option linter.unusedVariables false in
theorem ti_counting {P K V : Subgroup G} (hP : IsElemAbelian 2 P) (hVP : V ≤ P) (hV : V ≠ ⊥)
    (hKP : K ≤ Subgroup.normalizer (P : Set G)) (hKc : IsCyclic K)
    (htr : ∀ p ∈ P, ∀ q ∈ P, p ≠ 1 → q ≠ 1 → ∃ k ∈ K, k⁻¹ * p * k = q)
    (hTI : ∀ g ∈ K, g ∉ Subgroup.normalizer (V : Set G) → V ⊓ conjSubgroup V g = ⊥) :
    ∃ Y : Subgroup G, Y ≤ K ⊓ Subgroup.normalizer (V : Set G) ∧ IsCyclic Y ∧
      Nat.card Y = Nat.card V - 1 := by
  obtain ⟨v₀, hv₀V, hv₀1⟩ : ∃ v₀ ∈ V, v₀ ≠ 1 := by
    by_contra hcon
    apply hV
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    exact hcon ⟨x, hx, fun h => hx1 (Subgroup.mem_bot.2 h)⟩
  have htrN : ∀ w ∈ V, w ≠ 1 → ∃ n ∈ K ⊓ Subgroup.normalizer (V : Set G), n⁻¹ * v₀ * n = w :=
    fun w hw hw1 => rc_transitive hVP htr hTI hv₀V hv₀1 hw hw1
  have hdvd : Nat.card V - 1 ∣ Nat.card ↥(K ⊓ Subgroup.normalizer (V : Set G)) :=
    rc_card_sub_one_dvd hv₀V hv₀1 htrN inf_le_right
  haveI : IsCyclic ↥(K ⊓ Subgroup.normalizer (V : Set G)) :=
    Subgroup.isCyclic_of_le inf_le_left
  obtain ⟨Y, hYN, hYc, hYcard⟩ := rc_exists_cyclic hdvd
  exact ⟨Y, hYN, hYc, hYcard⟩

end CFSG.Quasithin.RonanE628

end
