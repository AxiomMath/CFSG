module

import CFSG.RankThree.GF2n.Tim78Counting
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG

variable {G : Type} [Group G]

theorem commute_of_sq_mul {a b : G} (h : (a * b) ^ 2 = a ^ 2 * b ^ 2) : a * b = b * a := by
  rw [sq, sq, sq] at h
  have h' : a * (b * a) * b = a * (a * b) * b := by simpa [mul_assoc] using h
  exact (mul_left_cancel (mul_right_cancel h')).symm

theorem forall_mul_comm_of_sq {A : Subgroup G} (s : A → G) (hs : ∀ a : A, (a : G) ^ 2 = s a)
    (hsm : ∀ a b : A, s (a * b) = s a * s b) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  refine commute_of_sq_mul ?_
  have e1 := hs ⟨a, ha⟩
  have e2 := hs ⟨b, hb⟩
  have e3 := hs (⟨a, ha⟩ * ⟨b, hb⟩)
  rw [hsm] at e3
  change (a * b) ^ 2 = _ at e3
  change a ^ 2 = _ at e1
  change b ^ 2 = _ at e2
  rw [e3, e1, e2]

variable [Finite G]

theorem exists_conj_eq_of_card {Ω H : Subgroup G} (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hHcard : Nat.card H = Nat.card Ω - 1) (hHodd : Odd (Nat.card H))
    (hΩe : Assembly.IsElemAbelian 2 Ω) (hHΩ : H ≤ Subgroup.normalizer (Ω : Set G))
    (hfaith : ∀ h ∈ H, (∀ x ∈ Ω, h * x * h⁻¹ = x) → h = 1) {x y : G} (hx : x ∈ Ω)
    (hy : y ∈ Ω) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ h ∈ H, h * x * h⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial Ω := ⟨⟨⟨x, hx⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  let φ : H →* MulAut Ω := Ω.normalizerMonoidHom.comp (Subgroup.inclusion hHΩ)
  have hφ : ∀ (h : H) (z : Ω), ((φ h z : Ω) : G) = h * z * (h : G)⁻¹ := fun _ _ => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    apply Subtype.ext
    refine hfaith h h.2 fun z hz => ?_
    have := congrArg (fun f : MulAut Ω => ((f ⟨z, hz⟩ : Ω) : G)) hh
    rw [hφ] at this
    exact this
  have hKcard : Nat.card φ.range = Nat.card H :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hKc : ∀ a ∈ φ.range, ∀ b ∈ φ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hHc a a.2 b b.2))
  have hPc : ∀ a b : Ω, a * b = b * a := fun a b => hΩe.1.is_comm.comm a b
  have hPp : ∀ a : Ω, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hΩe.2 a a.2)
  have hKp : ¬ 2 ∣ Nat.card φ.range := by
    rw [hKcard, ← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hHodd
  rcases tim78_2_5 hPc hPp φ.range hKc hKp with hlt | ⟨-, htr⟩
  · rw [hKcard, hHcard] at hlt
    exact absurd hlt (lt_irrefl _)
  · obtain ⟨⟨k, ⟨h, rfl⟩⟩, hk, -⟩ := htr ⟨x, hx⟩ ⟨y, hy⟩
      (fun h => hx1 (congrArg Subtype.val h)) (fun h => hy1 (congrArg Subtype.val h))
    exact ⟨h, h.2, congrArg Subtype.val hk⟩

theorem abelian_of_equivalent_layers {A Ω H : Subgroup G} {n : ℕ}
    (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hHcard : Nat.card H = 2 ^ n - 1)
    (hA2 : IsPGroup 2 A) (hΩA : Ω ≤ A) (hΩe : Assembly.IsElemAbelian 2 Ω)
    (hΩcard : Nat.card Ω = 2 ^ n) (hHA : H ≤ Subgroup.normalizer (A : Set G))
    (hHΩ : H ≤ Subgroup.normalizer (Ω : Set G))
    (hfaith : ∀ h ∈ H, (∀ x ∈ Ω, h * x * h⁻¹ = x) → h = 1)
    (ψ : A →* Ω) (hψker : ∀ a : A, ψ a = 1 ↔ (a : G) ∈ Ω) (hψsurj : Function.Surjective ψ)
    (hψH : ∀ h ∈ H, ∀ a b : A, (b : G) = h * a * h⁻¹ → (ψ b : G) = h * ψ a * h⁻¹) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : n ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := H)
    rw [hHcard] at this
    norm_num at this
  have hHodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' hn).mpr even_two) odd_one
  have htr : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ 1 → y ≠ 1 → ∃ h ∈ H, h * x * h⁻¹ = y :=
    fun x hx y hy hx1 hy1 => exists_conj_eq_of_card hHc (by rw [hHcard, hΩcard]) hHodd hΩe hHΩ
      hfaith hx hy hx1 hy1
  have hΩnt : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial, hΩcard]
    exact Nat.one_lt_two_pow hn
  have hcent : ∀ x ∈ Ω, ∀ a ∈ A, x * a = a * x := by
    have : Group.IsNilpotent A := hA2.isNilpotent
    have hnorm : (Ω.subgroupOf A).Normal := by
      have e : Ω.subgroupOf A = ψ.ker := by
        ext a
        rw [MonoidHom.mem_ker, hψker, Subgroup.mem_subgroupOf]
      rw [e]
      infer_instance
    have hne : Ω.subgroupOf A ≠ ⊥ := by
      intro h
      obtain ⟨w, hw1⟩ := exists_ne (1 : Ω)
      apply hw1
      have : (⟨w, hΩA w.2⟩ : A) ∈ Ω.subgroupOf A := Subgroup.mem_subgroupOf.mpr w.2
      rw [h, Subgroup.mem_bot] at this
      have h2 : (w : G) = 1 := congrArg Subtype.val this
      exact Subtype.ext h2
    obtain ⟨⟨w, hw⟩, hw1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    obtain ⟨hwΩ, hwZ⟩ := Subgroup.mem_inf.mp hw
    have hwΩ' : (w : G) ∈ Ω := Subgroup.mem_subgroupOf.mp hwΩ
    have hw1' : (w : G) ≠ 1 := by
      intro h
      apply hw1
      exact Subtype.ext (Subtype.ext h)
    have hwc : ∀ a ∈ A, (w : G) * a = a * w := fun a ha =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hwZ ⟨a, ha⟩)).symm
    intro x hx a ha
    by_cases hx1 : x = 1
    · rw [hx1, one_mul, mul_one]
    obtain ⟨h, hh, rfl⟩ := htr _ hwΩ' x hx hw1' hx1
    have ha' : h⁻¹ * a * h ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hHA hh)) a).mp ha
      rwa [inv_inv] at this
    have hc := hwc _ ha'
    calc h * w * h⁻¹ * a = h * ((w : G) * (h⁻¹ * a * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * a * h) * w) * h⁻¹ := by rw [hc]
      _ = a * (h * w * h⁻¹) := by group
  obtain ⟨v, hv1⟩ := exists_ne (1 : Ω)
  obtain ⟨a₀, ha₀⟩ := hψsurj v
  have hv₀ : (ψ a₀ : G) ≠ 1 := by
    rw [ha₀]
    exact fun h => hv1 (Subtype.ext h)
  have hconjA : ∀ h ∈ H, h * (a₀ : G) * h⁻¹ ∈ A := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp (hHA hh) a₀).mp a₀.2
  have key : ∀ a : A, (ψ a : G) ≠ 1 → ∃ h ∈ H, ∃ ω ∈ Ω,
      (a : G) = h * a₀ * h⁻¹ * ω ∧ (ψ a : G) = h * ψ a₀ * h⁻¹ := by
    intro a ha
    obtain ⟨h, hh, hha⟩ := htr _ (ψ a₀).2 _ (ψ a).2 hv₀ ha
    have hψb := hψH h hh a₀ ⟨_, hconjA h hh⟩ rfl
    have hψ1 : ψ ((⟨_, hconjA h hh⟩ : A)⁻¹ * a) = 1 := by
      rw [map_mul, map_inv, Subtype.ext (hψb.trans hha), inv_mul_cancel]
    refine ⟨h, hh, (h * a₀ * h⁻¹)⁻¹ * a, (hψker _).mp hψ1, by group, hha.symm⟩
  have hsq : ∀ h ∈ H, ∀ ω ∈ Ω, (h * (a₀ : G) * h⁻¹ * ω) ^ 2 = h * (a₀ : G) ^ 2 * h⁻¹ := by
    intro h hh ω hω
    have hc : Commute (h * (a₀ : G) * h⁻¹) ω := (hcent ω hω _ (hconjA h hh)).symm
    rw [hc.mul_pow, hΩe.2 ω hω, mul_one, conj_pow]
  have hsqΩ : ∀ a : A, (ψ a : G) = 1 → (a : G) ^ 2 = 1 := fun a ha =>
    hΩe.2 _ ((hψker a).mp (Subtype.ext ha))
  by_cases h0 : (a₀ : G) ^ 2 = 1
  ·
    refine forall_mul_comm_of_sq (fun _ => 1) (fun a => ?_) (fun _ _ => (mul_one 1).symm)
    by_cases ha : (ψ a : G) = 1
    · exact hsqΩ a ha
    · obtain ⟨h, hh, ω, hω, hae, -⟩ := key a ha
      rw [hae, hsq h hh ω hω, h0, mul_one, mul_inv_cancel]
  ·
    have ha₀Ω : (a₀ : G) ^ 2 ∈ Ω := by
      have : ψ (a₀ ^ 2) = 1 := by
        rw [map_pow]
        exact Subtype.ext (hΩe.2 _ (ψ a₀).2)
      have h' := (hψker _).mp this
      rwa [Subgroup.coe_pow] at h'
    obtain ⟨h₀, hh₀, hh₀e⟩ := htr _ (ψ a₀).2 _ ha₀Ω hv₀ h0
    refine forall_mul_comm_of_sq (fun a => h₀ * ψ a * h₀⁻¹) (fun a => ?_) (fun a b => ?_)
    · by_cases ha : (ψ a : G) = 1
      · rw [hsqΩ a ha, ha, mul_one, mul_inv_cancel]
      · obtain ⟨h, hh, ω, hω, hae, hψa⟩ := key a ha
        rw [hae, hsq h hh ω hω, hψa, ← hh₀e]
        have hc : h * h₀ = h₀ * h := hHc h hh h₀ hh₀
        calc h * (h₀ * ψ a₀ * h₀⁻¹) * h⁻¹ = (h * h₀) * ψ a₀ * (h * h₀)⁻¹ := by group
          _ = (h₀ * h) * ψ a₀ * (h₀ * h)⁻¹ := by rw [hc]
          _ = h₀ * (h * ψ a₀ * h⁻¹) * h₀⁻¹ := by group
    · simp only [map_mul, Subgroup.coe_mul]
      group

end CFSG.RankThree.GF2n.Tim78
