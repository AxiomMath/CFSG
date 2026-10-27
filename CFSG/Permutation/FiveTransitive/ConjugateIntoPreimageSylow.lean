module

public import CFSG.Permutation.FiveTransitive.SylowPreimageNormalizer

public section

namespace CFSG

namespace FiveTransitive.ConjugateIntoPreimageSylow

open MulAction

variable {G H : Type*} [Group G] [Group H]

private theorem into_sylow [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (u : G) (hu : IsPGroup p (Subgroup.zpowers u)) :
    ∃ k : G, k * u * k⁻¹ ∈ (P : Subgroup G) := by
  obtain ⟨T, hT⟩ := hu.exists_le_sylow
  obtain ⟨k, hk⟩ := exists_smul_eq G T P
  have he : (T : Subgroup G).map (MulAut.conj k).toMonoidHom = P :=
    congrArg Sylow.toSubgroup hk
  refine ⟨k, ?_⟩
  rw [← he]
  exact ⟨u, hT (Subgroup.mem_zpowers u), rfl⟩

theorem exists_conjugate [Finite G]
    (f : G →* H) (hf : Function.Surjective f) (V : Subgroup H)
    (P : Sylow 2 (V.comap f)) (u : G) (hu : u ^ 2 = 1)
    (hlocal : ∃ c : H, c * f u * c⁻¹ ∈ V) :
    ∃ c : G, c * u * c⁻¹ ∈ SylowPreimageNormalizer.ambient f V P := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ := hlocal
  obtain ⟨g, hg⟩ := hf d
  have hgv : g * u * g⁻¹ ∈ V.comap f := by
    change f (g * u * g⁻¹) ∈ V
    simpa only [map_mul, map_inv, hg] using hd
  let v : V.comap f := ⟨g * u * g⁻¹, hgv⟩
  have hv2 : v ^ 2 = 1 := by
    apply Subtype.ext
    change (g * u * g⁻¹) ^ 2 = 1
    change (MulAut.conj g u) ^ 2 = 1
    rw [← map_pow, hu, map_one]
  have hvp : IsPGroup 2 (Subgroup.zpowers v) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hv2
  obtain ⟨k, hk⟩ := into_sylow P v hvp
  refine ⟨k.val * g, ?_⟩
  have hm : k.val * (g * u * g⁻¹) * k.val⁻¹ ∈ SylowPreimageNormalizer.ambient f V P :=
    ⟨k * v * k⁻¹, hk, rfl⟩
  convert hm using 1
  group

end FiveTransitive.ConjugateIntoPreimageSylow

end CFSG
