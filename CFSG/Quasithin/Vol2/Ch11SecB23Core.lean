module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

theorem inf_centralizer_le_of_regular {X Y : Subgroup (MulAut W)}
    (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hreg : ∀ v w : W, v ≠ 1 → w ≠ 1 → ∃! x : ↥X, (x : MulAut W) v = w) :
    Y ⊓ Subgroup.centralizer (X : Set (MulAut W)) ≤ X := by
  intro y hy
  have hyc := (Subgroup.mem_inf.1 hy).2
  by_cases hW : ∃ v₀ : W, v₀ ≠ 1
  · obtain ⟨v₀, hv₀⟩ := hW
    have hyv : y v₀ ≠ 1 := fun h => hv₀ (by simpa using congrArg y.symm h)
    obtain ⟨⟨x₀, hx₀⟩, hx₀v, -⟩ := hreg v₀ (y v₀) hv₀ hyv
    suffices y = x₀ by rw [this]; exact hx₀
    ext w
    by_cases hw : w = 1
    · rw [hw, map_one, map_one]
    obtain ⟨⟨x, hx⟩, hxv, -⟩ := hreg v₀ w hv₀ hw
    simp only at hxv hx₀v
    have h1 : y * x = x * y := ((Subgroup.mem_centralizer_iff.1 hyc) x hx).symm
    have h2 : x₀ * x = x * x₀ := hXc x₀ hx₀ x hx
    rw [← hxv]
    calc y (x v₀) = (y * x) v₀ := rfl
      _ = (x * y) v₀ := by rw [h1]
      _ = x (x₀ v₀) := by simp [MulAut.mul_apply, hx₀v]
      _ = (x * x₀) v₀ := rfl
      _ = (x₀ * x) v₀ := by rw [h2]
      _ = x₀ (x v₀) := rfl
  · push Not at hW
    have : y = 1 := by
      ext w
      rw [hW w, map_one]
      rfl
    rw [this]
    exact X.one_mem

theorem commutator_mem_of_isCyclic {X Y : Subgroup (MulAut W)} (hX : IsCyclic ↥X)
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hC : Y ⊓ Subgroup.centralizer (X : Set (MulAut W)) ≤ X) {a b : MulAut W} (ha : a ∈ Y)
    (hb : b ∈ Y) : a * b * a⁻¹ * b⁻¹ ∈ X := by
  have hconj : ∀ y ∈ Y, ∃ m : ℤ, ∀ x ∈ X, y * x * y⁻¹ = x ^ m := by
    intro y hy
    let σ : ↥X →* ↥X :=
      { toFun := fun x => ⟨y * x * y⁻¹, ((Subgroup.mem_normalizer_iff.1 (hYX hy)) x).1 x.2⟩
        map_one' := by ext; simp
        map_mul' := fun x x' => by ext; simp [mul_assoc] }
    obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ
    refine ⟨m, fun x hx => ?_⟩
    have := congrArg Subtype.val (hm ⟨x, hx⟩)
    simpa [σ] using this
  have ha' := Y.inv_mem ha
  have hb' := Y.inv_mem hb
  obtain ⟨ma, hma⟩ := hconj a⁻¹ ha'
  obtain ⟨mb, hmb⟩ := hconj b⁻¹ hb'
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) ha') hb'
  refine hC ⟨hmem, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
  have hbx : b⁻¹ * x * b⁻¹⁻¹ ∈ X := ((Subgroup.mem_normalizer_iff.1 (hYX hb')) x).1 hx
  have hax : a⁻¹ * x * a⁻¹⁻¹ ∈ X := ((Subgroup.mem_normalizer_iff.1 (hYX ha')) x).1 hx
  have e1 : a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹ = x ^ (ma * mb) := by
    calc a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹ = a⁻¹ * (b⁻¹ * x * b⁻¹⁻¹) * a⁻¹⁻¹ := by group
      _ = (b⁻¹ * x * b⁻¹⁻¹) ^ ma := hma _ hbx
      _ = (x ^ mb) ^ ma := by rw [hmb x hx]
      _ = x ^ (ma * mb) := by rw [← zpow_mul, mul_comm]
  have e2 : b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹ = x ^ (ma * mb) := by
    calc b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹ = b⁻¹ * (a⁻¹ * x * a⁻¹⁻¹) * b⁻¹⁻¹ := by group
      _ = (a⁻¹ * x * a⁻¹⁻¹) ^ mb := hmb _ hax
      _ = (x ^ ma) ^ mb := by rw [hma x hx]
      _ = x ^ (ma * mb) := by rw [← zpow_mul]
  have e3 : a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹ = b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹ := e1.trans e2.symm
  calc x * (a * b * a⁻¹ * b⁻¹) =
        (a * b) * (b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹) * (a * b)⁻¹ * (a * b * a⁻¹ * b⁻¹) := by group
    _ = (a * b) * (a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹) * (a * b)⁻¹ * (a * b * a⁻¹ * b⁻¹) := by
        rw [e3]
    _ = a * b * a⁻¹ * b⁻¹ * x := by group

theorem le_sup_normalizer_of_regular [Finite W] (h112 : ASInputs.AS_A_1_12)
    (hW : ∀ w : W, w ^ 2 = 1) {X Y P : Subgroup (MulAut W)} (hXY : X ≤ Y)
    (hX : IsCyclic ↥X) (hXodd : Odd (Nat.card X))
    (hreg : ∀ v w : W, v ≠ 1 → w ≠ 1 → ∃! x : ↥X, (x : MulAut W) v = w)
    (hP : IsSylowTwoOf P Y) (hPc : IsCyclic ↥P)
    (hPX : P ≤ Subgroup.normalizer (X : Set (MulAut W))) :
    Y ≤ X ⊔ (Y ⊓ Subgroup.normalizer (P : Set (MulAut W))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSc : IsCyclic ((B6.toSylow2 hP : Sylow 2 ↥Y) : Subgroup ↥Y) := by
    rw [B6.toSylow2_coe]
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hP.1).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hP.1).symm.surjective
  obtain ⟨N, hNn, hNc⟩ := exists_normal_isComplement'_of_isCyclic_sylow (p := 2)
    (fun q hq _ => hq.two_le) (B6.toSylow2 hP) hSc
  have hSmap : ((B6.toSylow2 hP : Sylow 2 ↥Y) : Subgroup ↥Y).map Y.subtype = P := by
    rw [B6.toSylow2_coe, Subgroup.map_subgroupOf_eq_of_le hP.1]
  have hYeq : Y = N.map Y.subtype ⊔ P := by
    rw [← hSmap, ← Subgroup.map_sup, hNc.sup_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (B6.toSylow2 hP).isPGroup'
  have hNidx : N.index = 2 ^ k := by rw [hNc.symm.index_eq_card, hk]
  have hXN : X ≤ N.map Y.subtype := by
    intro x hx
    refine ⟨⟨x, hXY hx⟩, ?_, rfl⟩
    have h1 : orderOf (QuotientGroup.mk (⟨x, hXY hx⟩ : ↥Y) : ↥Y ⧸ N) ∣ 2 ^ k := by
      rw [← hNidx, Subgroup.index]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (QuotientGroup.mk (⟨x, hXY hx⟩ : ↥Y) : ↥Y ⧸ N) ∣ Nat.card X := by
      refine (orderOf_map_dvd (QuotientGroup.mk' N) _).trans ?_
      have : orderOf (⟨x, hXY hx⟩ : ↥Y) = orderOf (⟨x, hx⟩ : ↥X) := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      rw [this]
      exact orderOf_dvd_natCard _
    have h3 : orderOf (QuotientGroup.mk (⟨x, hXY hx⟩ : ↥Y) : ↥Y ⧸ N) = 1 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
      rw [hj] at h2 ⊢
      rcases j with _ | j
      · rfl
      · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h2)
          (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hXodd))
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hNodd : Odd (Nat.card (N.map Y.subtype)) := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, ← hNc.index_eq_card]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (B6.toSylow2 hP).not_dvd_index)
  have hNX := h112 W hW X (N.map Y.subtype) hX hreg hXN hNodd
  have hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut W)) := by
    rw [hYeq]; exact sup_le hNX hPX
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    intro a ha b hb
    have := mul_comm' (⟨a, ha⟩ : ↥X) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hC := inf_centralizer_le_of_regular (Y := Y) hXc hreg
  have hKY : Y ≤ Subgroup.normalizer ((X ⊔ P : Subgroup (MulAut W)) : Set (MulAut W)) := by
    have key : ∀ y ∈ Y, ∀ k ∈ X ⊔ P, y * k * y⁻¹ ∈ X ⊔ P := by
      intro y hy k hk
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X P hPX] at hk
      obtain ⟨x, hx, p, hp, rfl⟩ := hk
      have hyx : y * x * y⁻¹ ∈ X := ((Subgroup.mem_normalizer_iff.1 (hYX hy)) x).1 hx
      have hyp : y * p * y⁻¹ * p⁻¹ ∈ X := commutator_mem_of_isCyclic hX hYX hC hy (hP.1 hp)
      have e : y * (x * p) * y⁻¹ = (y * x * y⁻¹) * (y * p * y⁻¹ * p⁻¹) * p := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (X.mul_mem hyx hyp))
        (Subgroup.mem_sup_right hp)
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨key y hy k, fun hk => ?_⟩
    have := key y⁻¹ (Y.inv_mem hy) _ hk
    simpa [mul_assoc] using this
  have hfr := B6.frattini_two (sup_le hXY hP.1) hKY
    (F7.isSylowTwoOf_mono_right hP le_sup_right (sup_le hXY hP.1))
  refine hfr.trans (sup_le (sup_le le_sup_left ?_) le_sup_right)
  exact (le_inf hP.1 Subgroup.le_normalizer).trans le_sup_right

end CFSG.Quasithin.Vol2.Ch11.SecB
