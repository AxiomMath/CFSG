module

public import CFSG.Quasithin.EmptyFaithful.S153NBase
public import CFSG.Quasithin.EmptyFaithful.S153NMl3A
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
import CFSG.Quasithin.EmptyFaithful.S1565M7

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace Ml3

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {X : Subgroup (MulAut W)} {U Z : Subgroup W} {Γ : Subgroup (GL ι K)} {π : ↥Γ →* ↥X}

theorem corr_mem_iff (R : SzN15.NatReal X U Z Γ π) {β : ↥U →* Multiplicative (ι → K)}
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z)
    (hβe : ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥X) : MulAut W) u ∈ U),
      β ⟨((π γ : ↥X) : MulAut W) u, hu⟩ = natAct Γ γ (β u))
    (γ : ↥Γ) (u : ↥U) :
    ((π γ : ↥X) : MulAut W) (u : W) * (u : W)⁻¹ ∈ Z ↔ natAct Γ γ (β u) = β u := by
  have hu : ((π γ : ↥X) : MulAut W) (u : W) ∈ U := R.U_inv _ u u.2
  have hm : ((π γ : ↥X) : MulAut W) (u : W) * (u : W)⁻¹ ∈ U := U.mul_mem hu (U.inv_mem u.2)
  have h1 : β ⟨((π γ : ↥X) : MulAut W) (u : W) * (u : W)⁻¹, hm⟩ = natAct Γ γ (β u) * (β u)⁻¹ := by
    have : (⟨((π γ : ↥X) : MulAut W) (u : W) * (u : W)⁻¹, hm⟩ : ↥U) =
        ⟨((π γ : ↥X) : MulAut W) (u : W), hu⟩ * u⁻¹ := rfl
    rw [this, map_mul, map_inv, hβe γ u hu]
  rw [← hβk ⟨_, hm⟩, h1, mul_inv_eq_one]

end Ml3

namespace Ml3

theorem false_of_order_three {W : Type} [CommGroup W] (hW : ∀ v : W, v ^ 2 = 1)
    {Γ J : Subgroup (MulAut W)} {w : W} (hJΓ : J ≤ Γ) (h3 : ¬ 3 ∣ Nat.card ↥(stabAt Γ w))
    {A : Type*} [Group A] {π : A →* ↥J} (hinj : Function.Injective π) {ρ : A} (hρ1 : ρ ≠ 1)
    (hρ3 : ρ ^ 3 = 1) (hmem : ((π ρ : ↥J) : MulAut W) w * w⁻¹ ∈ fixV J) : False := by
  refine false_of_lift hW hJΓ h3 (g := ((π ρ : ↥J) : MulAut W)) (π ρ).2 ?_ ?_ hmem
  · intro h
    apply hρ1
    apply hinj
    rw [map_one]
    exact Subtype.ext h
  · have h1 : (π ρ) ^ 3 = 1 := by rw [← map_pow, hρ3, map_one]
    have h2 := congrArg (fun y : ↥J => (y : MulAut W)) h1
    simpa using h2

end Ml3

theorem false_of_natural_sl3 {W : Type} [CommGroup W] [Finite W] (hW : ∀ v : W, v ^ 2 = 1)
    {Γ J : Subgroup (MulAut W)} {w : W} {m : ℕ} (hJΓ : J ≤ Γ)
    (hnat : BinaryNaturalSL J ⊤ (fixV J) 3 m) (hw : w ∉ fixV J)
    (h3 : ¬ 3 ∣ Nat.card ↥(stabAt Γ w)) : False := by
  have _ := hw
  have _ := ‹Finite W›
  obtain ⟨K, _, _, -, π₀, hπ₀⟩ := hnat
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 3 K) →* ↥J,
      (FFModel.nat (StatedSL 3 K)).RealizesVia J ⊤ (fixV J) π := ⟨π₀, hπ₀⟩
  have hinj : Function.Injective π := natural_realizes_injective _ hπ
  have R := SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, -, hβk, hβe⟩ := R.exists_β
  obtain ⟨ρ, hρ1, hρ3, hρx⟩ :=
    Ml3.exists_statedSL_order_three (Multiplicative.toAdd (β ⟨w, trivial⟩))
  refine Ml3.false_of_order_three hW hJΓ h3 hinj hρ1 hρ3 ?_
  refine (Ml3.corr_mem_iff R hβk hβe ρ ⟨w, trivial⟩).2 ?_
  show Multiplicative.ofAdd _ = _
  rw [hρx]
  rfl

end CFSG.Quasithin.S153N
