
module

public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

@[expose] def FFModel.Faithful (D : FFModel) : Prop :=
  ∀ γ : D.Gam, (∀ m ∈ D.sec, D.act γ m * m⁻¹ ∈ D.ker) → γ = 1

theorem FFModel.RealizesVia.injective_of_faithful {V : Type*} [CommGroup V] {D : FFModel}
    (hD : D.Faithful) {H : Subgroup (MulAut V)} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H ⊤ ⊥ π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨_, _, _, _, _, hsec, _, β, hβs, _, hβe⟩ := h
  apply hD
  intro m hm
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have hact : D.act γ m ∈ D.sec := hsec γ m hm
  have h1 := hβe γ u ⟨m, hm⟩ (by trivial) hact hu
  have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), (by trivial)⟩ : ↥(⊤ : Subgroup V)) = u :=
    Subtype.ext (by rw [hγ]; rfl)
  rw [h2, hu] at h1
  have h3 := QuotientGroup.eq.mp h1
  have h4 : m⁻¹ * D.act γ m ∈ D.ker := h3
  rw [mul_comm]
  exact h4

section NatFaithful

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem natAct_faithful (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) (γ : ↥Γ)
    (h : ∀ m : Multiplicative (ι → K), natAct Γ γ m * m⁻¹ = 1) : γ = 1 := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h3 := h (Multiplicative.ofAdd (Pi.single j 1))
  have h4 := congrArg Multiplicative.toAdd h3
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_one] at h4
  have h2 : Multiplicative.toAdd (natAct Γ γ (Multiplicative.ofAdd (Pi.single j 1))) =
      Pi.single j 1 := sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h4)
  have h5 := congrFun h2 i
  simp [natAct] at h5
  simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply]
  rw [h5]
  simp [Pi.single_apply]

theorem FFModel.nat_faithful (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    (FFModel.nat Γ).Faithful := fun γ h =>
  natAct_faithful Γ γ fun m => Subgroup.mem_bot.mp (h m trivial)

end NatFaithful

section IsoTypes

variable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}

theorem BinaryNaturalSL.exists_equiv {d a : ℕ} (h : BinaryNaturalSL H ⊤ ⊥ d a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
      Nonempty (↥(StatedSL d K) ≃* ↥H) := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  exact ⟨K, hK, hf, hc, ⟨MulEquiv.ofBijective π
    ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩⟩⟩

theorem BinaryNaturalSp4.exists_equiv {a : ℕ} (h : BinaryNaturalSp4 H ⊤ ⊥ a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ a ∧
      Nonempty (↥(StatedSp 2 K) ≃* ↥H) := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  exact ⟨K, hK, hf, hc, ⟨MulEquiv.ofBijective π
    ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩⟩⟩

theorem BinaryNaturalSU3.exists_equiv {a : ℕ} (h : BinaryNaturalSU3 H ⊤ ⊥ a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ a) ^ 2 ∧
      Nonempty (↥(StatedSU 3 (2 ^ a) K) ≃* ↥H) := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  exact ⟨K, hK, hf, hc, ⟨MulEquiv.ofBijective π
    ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩⟩⟩

theorem BinaryNaturalSz.exists_equiv {f : ℕ} (h : BinaryNaturalSz H ⊤ ⊥ f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧
      Nonempty (↥(CFSG.Blueprint.suzukiGroup a K) ≃* ↥H) := by
  obtain ⟨a, ha, hf, K, hK, hfin, hc, π, hπ⟩ := h
  exact ⟨a, K, hK, hfin, ha, hf, hc, ⟨MulEquiv.ofBijective π
    ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩⟩⟩

end IsoTypes

end CFSG.Quasithin
