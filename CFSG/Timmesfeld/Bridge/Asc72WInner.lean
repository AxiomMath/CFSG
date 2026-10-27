module

public import CFSG.Timmesfeld.Bridge.Asc72WBasic
public import CFSG.Timmesfeld.Bridge.Asc72OutCoset

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open Equiv CFSG.BenderSuzuki

namespace WreathData

variable {G : Type} [Group G] {D : Set G} {M : Subgroup G} (W : WreathData G D M)

theorem coe_pow_apply_of_forall {i : Fin W.r} {γ : MulAut (W.S i)} {g : G}
    (hγ : ∀ x : W.S i, ((γ x : W.S i) : G) = g * x * g⁻¹) (n : ℕ) (x : W.S i) :
    (((γ ^ n) x : W.S i) : G) = g ^ n * x * (g ^ n)⁻¹ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, hγ, ih, pow_succ']
    group

theorem orderOf_dvd_of_forall {i : Fin W.r} {γ : MulAut (W.S i)} {g : G}
    (hγ : ∀ x : W.S i, ((γ x : W.S i) : G) = g * x * g⁻¹) : orderOf γ ∣ orderOf g := by
  refine orderOf_dvd_of_pow_eq_one (MulEquiv.ext fun x => Subtype.ext ?_)
  rw [W.coe_pow_apply_of_forall hγ, pow_orderOf_eq_one]
  simp

variable [Finite G]

theorem innerOn_mul_of_swap (hS : Setup G D) {i k : Fin W.r} (hik : i ≠ k) {d d' : G}
    (hd : d ∈ D) (hd' : d' ∈ D) (hdπ : W.π d = Equiv.swap i k)
    (hd'π : W.π d' = Equiv.swap i k) : W.InnerOn i (d * d') := by
  obtain ⟨f, hf, ⟨ψ⟩⟩ := wreathData_factor_psl2 hS W i
  have hB : IsBenderGroup (W.S i) := .isPSL2 f hf ψ
  have := W.simple i
  have hZ : Subgroup.center (W.S i) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (W.S i)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := W.not_comm i
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
  obtain ⟨P⟩ : Nonempty (Sylow 2 (W.S i)) := inferInstance
  have hP : (P : Subgroup (W.S i)) ≠ ⊥ := by
    intro h
    have h4 := IsBenderGroup.four_le_card_center hB P
    have h1 := Subgroup.card_le_card_group (Subgroup.center (P : Subgroup (W.S i)))
    rw [Subgroup.card_eq_one.mpr h] at h1
    omega
  have hPab := IsBenderGroup.commute_of_psl2 hf ψ P
  have htrans : ∀ x ∈ (P : Subgroup (W.S i)), x ≠ 1 → ∀ y ∈ (P : Subgroup (W.S i)), y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer ((P : Subgroup (W.S i)) : Set (W.S i)), g * x * g⁻¹ = y :=
    fun x hx hx1 y hy hy1 => IsBenderGroup.exists_normalizer_conj hB P
      ⟨hx, fun q hq => hPab q hq x hx⟩ hx1 ⟨hy, fun q hq => hPab q hq y hy⟩ hy1
  set C : Set (MulAut (W.S i)) := {γ | ∃ e ∈ D, W.π e = Equiv.swap i k ∧
    ∀ x : W.S i, ((γ x : W.S i) : G) = d * e * x * (d * e)⁻¹} with hC
  have hinn : ∀ γ ∈ C, ∀ m : W.S i, γ * MulAut.conj m ∈ C := by
    rintro γ ⟨e, he, heπ, hγ⟩ m
    have hmM : (m : G) ∈ M := W.le i m.2
    refine ⟨(m : G)⁻¹ * e * m, ?_, ?_, fun x => ?_⟩
    · simpa using hS.conj_mem (m : G)⁻¹ he
    · rw [map_mul, map_mul, map_inv, W.π_eq_one_of_mem hmM, inv_one, one_mul, mul_one, heπ]
    · rw [MulAut.mul_apply, hγ, MulAut.conj_apply]
      have hy : e * ((m : G) * x * (m : G)⁻¹) * e⁻¹ ∈ W.S k := by
        have := W.conj_mem e ((W.S i).mul_mem ((W.S i).mul_mem m.2 x.2) ((W.S i).inv_mem m.2))
        rwa [heπ, Equiv.swap_apply_left] at this
      have hc : Commute (m : G) (e * ((m : G) * x * (m : G)⁻¹) * e⁻¹) := W.commute_of_ne hik m.2 hy
      have hc' : (m : G)⁻¹ * (e * ((m : G) * x * (m : G)⁻¹) * e⁻¹) * m =
          e * ((m : G) * x * (m : G)⁻¹) * e⁻¹ := by
        rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]
      push_cast
      calc d * e * ((m : G) * x * (m : G)⁻¹) * (d * e)⁻¹
          = d * (e * ((m : G) * x * (m : G)⁻¹) * e⁻¹) * d⁻¹ := by group
        _ = d * ((m : G)⁻¹ * (e * ((m : G) * x * (m : G)⁻¹) * e⁻¹) * m) * d⁻¹ := by rw [hc']
        _ = d * ((m : G)⁻¹ * e * m) * x * (d * ((m : G)⁻¹ * e * m))⁻¹ := by group
  have hord : ∀ γ ∈ C, orderOf γ ∣ 2 ∨ Odd (orderOf γ) := by
    rintro γ ⟨e, he, -, hγ⟩
    have hdvd := W.orderOf_dvd_of_forall hγ
    rcases hS.oddT.2 d hd e he with h | h
    · exact Or.inl (hdvd.trans h)
    · exact Or.inr (Odd.of_dvd_nat h hdvd)
  have hπ1 : W.π (d * d') i = i := by
    rw [map_mul, hdπ, hd'π, Equiv.Perm.mul_apply, Equiv.swap_apply_self]
  have hγ₀ : W.restr i (d * d') hπ1 ∈ C := ⟨d', hd', hd'π, fun x => W.restr_apply i _ hπ1 x⟩
  obtain ⟨m, hm⟩ := subset_inner_of_coset_orders hZ (W.not_comm i) P hP htrans C hinn hord _ hγ₀
  refine ⟨m, m.2, fun x hx => ?_⟩
  have h := congrArg (fun γ : MulAut (W.S i) => ((γ ⟨x, hx⟩ : W.S i) : G)) hm
  simp only [MulAut.conj_apply, W.restr_apply] at h
  exact h.symm

theorem innerOn_conj_swap (hS : Setup G D) {i₀ : Fin W.r} {t : Fin W.r → G} (ht0 : t i₀ = 1)
    (htD : ∀ l, l ≠ i₀ → t l ∈ D) (htπ : ∀ l, W.π (t l) = Equiv.swap i₀ l) {u : G}
    (hu : u ∈ D) {i j : Fin W.r} (hij : i ≠ j) (huπ : W.π u = Equiv.swap i j)
    (hcomm : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ W.S k, Commute u x) :
    W.InnerOn i₀ (t j * u * (t i)⁻¹) := by
  by_cases hi : i = i₀
  · subst hi
    rw [ht0, inv_one, mul_one]
    exact W.innerOn_mul_of_swap hS hij (htD j (Ne.symm hij)) hu (htπ j) huπ
  by_cases hj : j = i₀
  · subst hj
    rw [ht0, one_mul, hS.oddT.inv_eq (htD i hi)]
    exact W.innerOn_mul_of_swap hS (Ne.symm hij) hu (htD i hi)
      (by rw [huπ, Equiv.swap_comm]) (htπ i)
  have hu2 := hS.oddT.mul_self_eq_one hu
  have hvD : u * t i * u ∈ D := by
    simpa only [hS.oddT.inv_eq hu] using hS.conj_mem u (htD i hi)
  have hvπ : W.π (u * t i * u) = Equiv.swap i₀ j := by
    rw [map_mul, map_mul, htπ i, huπ]
    calc Equiv.swap i j * Equiv.swap i₀ i * Equiv.swap i j
        = Equiv.swap i j * Equiv.swap i₀ i * (Equiv.swap i j)⁻¹ := by rw [Equiv.swap_inv]
      _ = Equiv.swap (Equiv.swap i j i₀) (Equiv.swap i j i) := (Equiv.swap_apply_apply _ _ _).symm
      _ = Equiv.swap i₀ j := by
        rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj), Equiv.swap_apply_left]
  have e1 : t j * u * (t i)⁻¹ = t j * (u * t i * u) * u := by
    rw [hS.oddT.inv_eq (htD i hi)]
    calc t j * u * t i = t j * u * t i * (u * u) := by rw [hu2, mul_one]
      _ = t j * (u * t i * u) * u := by group
  rw [e1]
  exact (W.innerOn_mul_of_swap hS (Ne.symm hj) (htD j hj) hvD (htπ j) hvπ).mul
    (W.innerOn_of_commute (hcomm i₀ (Ne.symm hi) (Ne.symm hj)))

end WreathData

end CFSG.Timmesfeld.Bridge.Asc72
