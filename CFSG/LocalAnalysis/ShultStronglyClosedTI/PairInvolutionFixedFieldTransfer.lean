module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthTransfer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.PairInvolutionFixedFieldOrbit

public section

namespace CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem no_conjugate_centralizes {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {Q : Subgroup G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) {u : G}
    (hQY : ¬ Q ≤ Subgroup.centralizer ({u} : Set G))
    (horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
        rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega}) :
    ∀ g : G, ¬ ∀ v ∈ Q, Commute (g⁻¹ * u * g) v := by
  intro g hg
  let Y := Subgroup.centralizer ({u} : Set G)
  let E : Subgroup G := Q ⊓ Y
  have hQH : Q ≤ H := point_subgroup_le h.distinguished_mem hQclass
  have hEQ : E < Q := lt_of_le_of_ne inf_le_left fun hEQ => hQY (inf_eq_left.mp hEQ)
  have hEcard : Nat.card E < Nat.card Q := Subgroup.card_lt_of_lt hEQ
  have hQ1 : 1 < Nat.card Q := lt_of_le_of_lt Nat.card_pos hEcard
  obtain ⟨v₀', hv₀'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    ((Subgroup.one_lt_card_iff_ne_bot Q).mp hQ1)
  have hv₀1 : (v₀' : G) ≠ 1 := fun h1 => hv₀' (Subtype.ext h1)
  have hv₀Q : (v₀' : G) ∈ Q := v₀'.2
  let gamma : rightCosetSpace H := rightCosetMk H g⁻¹
  have hsD : ∀ v ∈ (Q : Set G) \ {1}, g * v * g⁻¹ ∈ involutionPointClass z := by
    intro v hv
    simpa only [inv_inv] using conj_mem_pointClass (point_subgroup_class h hQclass hv) g⁻¹
  have hsY : ∀ v ∈ Q, g * v * g⁻¹ ∈ Y := by
    intro v hv
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hc : g⁻¹ * u * g * v = v * (g⁻¹ * u * g) := hg v hv
    calc
      g * v * g⁻¹ * u = g * (v * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * u * g * v) * g⁻¹ := by rw [hc]
      _ = u * (g * v * g⁻¹) := by group
  have hsfix : ∀ v ∈ Q, rightCosetTranslate H gamma (g * v * g⁻¹) = gamma := by
    intro v hv
    apply (translate_mk_fixed_iff H g⁻¹ _).mpr
    have hgv : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
    rw [hgv]
    exact hQH hv
  have hgammau : rightCosetTranslate H gamma u = gamma :=
    class_fixed_of_commute h (hsD _ ⟨hv₀Q, hv₀1⟩)
      (Subgroup.mem_centralizer_singleton_iff.mp (hsY _ hv₀Q)) (hsfix _ hv₀Q)
  have hgamma : gamma ∈ {omega : rightCosetSpace H | ∃ y ∈ Y,
      rightCosetTranslate H (rightCosetMk H 1) y = omega} := by
    rw [horbit]
    exact hgammau
  obtain ⟨y, hy, hygamma⟩ := hgamma
  have hw : ∀ v ∈ (Q : Set G) \ {1}, y * (g * v * g⁻¹) * y⁻¹ ∈ (E : Set G) \ {1} := by
    intro v hv
    have hwD : y * (g * v * g⁻¹) * y⁻¹ ∈ involutionPointClass z := by
      simpa only [inv_inv] using conj_mem_pointClass (hsD v hv) y⁻¹
    have hwH : y * (g * v * g⁻¹) * y⁻¹ ∈ H := by
      apply (translate_base_iff H _).mp
      rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hygamma, hsfix v hv.1,
        ← hygamma, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
    have hwQ : y * (g * v * g⁻¹) * y⁻¹ ∈ (Q : Set G) \ {1} := by
      rw [← class_inter_point h hQclass]
      exact ⟨hwD, hwH⟩
    refine ⟨⟨hwQ.1, ?_⟩, hwQ.2⟩
    exact Y.mul_mem (Y.mul_mem hy (hsY v hv.1)) (Y.inv_mem hy)
  have hinj : Nat.card ↥((Q : Set G) \ {1}) ≤ Nat.card ↥((E : Set G) \ {1}) := by
    refine Nat.card_le_card_of_injective
      (fun v : ↥((Q : Set G) \ {1}) => (⟨y * (g * v * g⁻¹) * y⁻¹, hw v v.2⟩ :
        ↥((E : Set G) \ {1}))) ?_
    intro v₁ v₂ hv
    have h' : y * (g * (v₁ : G) * g⁻¹) * y⁻¹ = y * (g * v₂ * g⁻¹) * y⁻¹ :=
      congrArg (fun x : ↥((E : Set G) \ {1}) => (x : G)) hv
    apply Subtype.ext
    simpa only [mul_left_inj, mul_right_inj] using h'
  rw [card_diff_one, card_diff_one] at hinj
  have hEpos : 0 < Nat.card E := Nat.card_pos
  omega

omit [Finite G] in
theorem simple_no_normal_index_two (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (D : Subgroup G) (hD : D.Normal) : D.index ≠ 2 := by
  intro hindex
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hsimple D hD with hbot | htop
  · rw [hbot, Subgroup.index_bot] at hindex
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyclic : IsCyclic G := isCyclic_of_prime_card hindex
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (mul_comm' a b)
  · rw [htop, Subgroup.index_top] at hindex
    exact absurd hindex (by norm_num)

theorem transfer_index_two {H Q : Subgroup G} (hQ4 : Nat.card Q = 4)
    (hQnorm : ∀ k ∈ H, ∀ v ∈ Q, k⁻¹ * v * k ∈ Q) (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ H)
    {u : G} (hu : orderOf u = 2) (hnocentral : ∀ g : G, ¬ ∀ v ∈ Q, Commute (g⁻¹ * u * g) v) :
    ∃ D : Subgroup G, D.Normal ∧ D.index = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := ↥((Q : Set G) \ {1})
  have hleft : ∀ k ∈ (S : Subgroup G), ∀ v ∈ (Q : Set G) \ {1},
      k * v * k⁻¹ ∈ (Q : Set G) \ {1} := by
    intro k hk v hv
    have h1 := hQnorm k⁻¹ (H.inv_mem (hSH hk)) v hv.1
    have h2 := conj_ne_one (w := k⁻¹) hv.2
    rw [inv_inv] at h1 h2
    exact ⟨h1, h2⟩
  have hright : ∀ k ∈ (S : Subgroup G), ∀ v ∈ (Q : Set G) \ {1},
      k⁻¹ * v * k ∈ (Q : Set G) \ {1} :=
    fun k hk v hv => ⟨hQnorm k (hSH hk) v hv.1, conj_ne_one hv.2⟩
  let φ : (S : Subgroup G) →* Equiv.Perm T :=
    { toFun := fun k =>
        { toFun := fun v => ⟨(k : G) * v * (k : G)⁻¹, hleft k k.2 v v.2⟩
          invFun := fun v => ⟨(k : G)⁻¹ * v * k, hright k k.2 v v.2⟩
          left_inv := fun v => Subtype.ext (by group)
          right_inv := fun v => Subtype.ext (by group) }
      map_one' := by
        ext v
        simp
      map_mul' := by
        intro a b
        ext v
        simp only [Subgroup.coe_mul, mul_inv_rev, Equiv.coe_fn_mk, Equiv.Perm.coe_mul,
          Function.comp_apply]
        group }
  let N := φ.ker
  have hkerQ : ∀ k ∈ N, ∀ v ∈ Q, Commute (k : G) v := by
    intro k hk v hv
    by_cases hv1 : v = 1
    · rw [hv1]
      exact Commute.one_right _
    · have hfix : φ k ⟨v, hv, hv1⟩ = ⟨v, hv, hv1⟩ := by
        rw [(MonoidHom.mem_ker).mp hk]
        rfl
      have hval : (k : G) * v * (k : G)⁻¹ = v := congrArg Subtype.val hfix
      have h' := congrArg (fun x : G => x * k) hval
      simp only [inv_mul_cancel_right] at h'
      exact h'
  have hcyclic : IsCyclic ((S : Subgroup G) ⧸ N) := by
    have hrange : Nat.card φ.range ∣ 6 := by
      have hT : Nat.card T = 3 := by rw [card_diff_one, hQ4]
      have h6 : Nat.card (Equiv.Perm T) = 6 := by
        rw [Nat.card_perm, hT]
        rfl
      exact h6 ▸ Subgroup.card_subgroup_dvd_card φ.range
    obtain ⟨n, hn⟩ := (S.isPGroup').exists_card_eq
    have hrange2 : Nat.card φ.range ∣ 2 ^ n := hn ▸ Subgroup.card_range_dvd φ
    obtain ⟨k, -, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrange2
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have h4 : 2 ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      have : 4 ∣ 6 := (hkcard ▸ h4).trans hrange
      omega
    let e := QuotientGroup.quotientKerEquivRange φ
    have hcard : Nat.card ((S : Subgroup G) ⧸ N) = 2 ^ k := by
      rw [Nat.card_congr e.toEquiv, hkcard]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk1 with hk0 | hk1'
    · rw [hk0, pow_zero] at hcard
      have : Subsingleton ((S : Subgroup G) ⧸ N) := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact isCyclic_of_subsingleton
    · rw [hk1', pow_one] at hcard
      exact isCyclic_of_prime_card hcard
  obtain ⟨g, hg⟩ := involution_conjugate_into_sylow S hu
  let x : (S : Subgroup G) := ⟨g⁻¹ * u * g, hg⟩
  have hxN : x ∉ N := fun hx => hnocentral g (hkerQ x hx)
  have hxorder : orderOf x = 2 := by
    rw [Subgroup.orderOf_mk, orderOf_conj_eq]
    exact hu
  have havoid : ∀ (a : G) (hmem : a⁻¹ * (x : G) * a ∈ (S : Subgroup G)),
      (⟨a⁻¹ * (x : G) * a, hmem⟩ : (S : Subgroup G)) ∉ N := by
    intro a hmem hmemN
    apply hnocentral (g * a)
    have heq : (g * a)⁻¹ * u * (g * a) = a⁻¹ * (x : G) * a := by
      change (g * a)⁻¹ * u * (g * a) = a⁻¹ * (g⁻¹ * u * g) * a
      group
    rw [heq]
    exact hkerQ _ hmemN
  exact (CFSG.ShultStronglyClosedTI.TwoCoreGrowth.thompson_cyclic_two_quotient_transfer
    S N x hxN hxorder havoid).2.2.2.2.2.2

end CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
