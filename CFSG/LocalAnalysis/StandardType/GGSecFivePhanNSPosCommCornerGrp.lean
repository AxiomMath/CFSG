module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem ggNSPosPF3C_mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (hg : ∀ b ∈ H, g * b * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  classical
  let c : ↥H → ↥H := fun b => ⟨g * b * g⁻¹, hg b b.2⟩
  have hinj : Function.Injective c := by
    intro a b hab
    have h1 : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hsurj : Function.Surjective c := Finite.surjective_of_injective hinj
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hg h hh, fun hh => ?_⟩
  obtain ⟨b, hb⟩ := hsurj ⟨g * h * g⁻¹, hh⟩
  have h1 : g * (b : G) * g⁻¹ = g * h * g⁻¹ := congrArg Subtype.val hb
  have h2 : (b : G) = h := mul_left_cancel (mul_right_cancel h1)
  rw [← h2]
  exact b.2

theorem ggNSPosPF3C_conj_trivial_of_noTransvection {Bs : Subgroup G} (hel : IsElemAbelian 3 Bs)
    (hNT : GGNoTransvection 3 Bs) {E : Subgroup G} (hE : Nat.card ↥E = 3) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hEg : ∀ e ∈ E, g * e * g⁻¹ = e)
    (hmv : ∀ b ∈ Bs, b⁻¹ * (g * b * g⁻¹) ∈ E) : ∀ b ∈ Bs, g * b * g⁻¹ = b := by
  classical
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨b0, hb0, hne⟩ := hcon
  have hcomm : ∀ a b : ↥Bs, a * b = b * a := fun a b => hel.1.is_comm.comm a b
  let φ : MulAut ↥Bs := ggConjAut Bs hg
  have hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := fun b => ggConjAut_apply Bs hg b
  let θ : ↥Bs →* ↥Bs :=
    MonoidHom.mk' (fun b => b⁻¹ * φ b) (fun a b => by
      show (a * b)⁻¹ * φ (a * b) = (a⁻¹ * φ a) * (b⁻¹ * φ b)
      rw [mul_inv_rev, map_mul, hcomm b⁻¹ a⁻¹]
      calc a⁻¹ * b⁻¹ * (φ a * φ b) = a⁻¹ * (b⁻¹ * φ a) * φ b := by group
        _ = a⁻¹ * (φ a * b⁻¹) * φ b := by rw [hcomm b⁻¹ (φ a)]
        _ = a⁻¹ * φ a * (b⁻¹ * φ b) := by group)
  have hθ : ∀ b : ↥Bs, θ b = b⁻¹ * φ b := fun b => rfl
  have hker : ∀ b : ↥Bs, θ b = 1 ↔ φ b = b := by
    intro b
    rw [hθ, inv_mul_eq_one, eq_comm]
  have hrange : θ.range.map Bs.subtype ≤ E := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    show ((b⁻¹ * φ b : ↥Bs) : G) ∈ E
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
    exact hmv b b.2
  have hdvd : Nat.card ↥θ.range ∣ 3 := by
    have h1 := Subgroup.card_dvd_of_le hrange
    rwa [Subgroup.card_map_of_injective Bs.subtype_injective, hE] at h1
  have hθ1 : θ ⟨b0, hb0⟩ ≠ 1 := by
    rw [Ne, hker]
    intro h1
    apply hne
    have h2 := congrArg Subtype.val h1
    rw [hφ] at h2
    exact h2
  have hcard1 : Nat.card ↥θ.range ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one] at h1
    apply hθ1
    have h2 : θ ⟨b0, hb0⟩ ∈ θ.range := ⟨_, rfl⟩
    rw [h1] at h2
    exact (Subgroup.mem_bot.mp h2)
  have hcard3 : Nat.card ↥θ.range = 3 :=
    (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd).resolve_left hcard1
  have hidx : θ.ker.index = 3 := by rw [Subgroup.index_ker, hcard3]
  have hcardBs : Nat.card ↥θ.ker * 3 = Nat.card ↥Bs := by
    rw [← hidx]
    exact Subgroup.card_mul_index θ.ker
  have hfix : Nat.card {b : ↥Bs // φ b = b} = Nat.card ↥θ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun b => (MonoidHom.mem_ker.trans (hker b)).symm))
  have htr : GGIsTransvection 3 φ := by
    refine ⟨by rw [hfix]; exact hcardBs, fun b => ?_⟩
    apply Subtype.ext
    rw [hφ, Subgroup.coe_mul, Subgroup.coe_inv, hφ]
    exact hEg _ (hmv b b.2)
  exact hNT φ (ggConjAut_mem_ggInduced (Subgroup.mem_top g) hg) htr

end CFSG.StandardType

end
