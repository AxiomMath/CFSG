module

public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111CVertA

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open

variable {Z : Type} [Group Z]

theorem comm_mem_of_isExtensionOf [Finite Z] {N : Subgroup Z} [N.Normal]
    (ψ : Z ⧸ N →* Multiplicative (ZMod 2))
    (eK : ↥ψ.ker ≃* (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) ×
      Multiplicative (ZMod 2)))) {c u : Z} (hc : ψ c = 1) (hu : ψ u = 1) :
    c * u * c⁻¹ * u⁻¹ ∈ N := by
  have hK : ∀ x y : Z ⧸ N, ψ x = 1 → ψ y = 1 → x * y = y * x := by
    intro x y hx hy
    have := mul_comm (eK ⟨x, hx⟩) (eK ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at this
    exact Subtype.mk.inj (eK.injective this)
  have h1 := hK (QuotientGroup.mk c) (QuotientGroup.mk u) hc hu
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  calc (c : Z ⧸ N) * u * (c : Z ⧸ N)⁻¹ * (u : Z ⧸ N)⁻¹
      = ((u : Z ⧸ N) * c) * (c : Z ⧸ N)⁻¹ * (u : Z ⧸ N)⁻¹ := by rw [h1]
    _ = 1 := by group

theorem noVc_of_autM12_right [Finite Z]
    (hext : F6.IsExtensionOf₃ Z (Multiplicative (ZMod 2))
      (Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) : NoVc Z := by
  intro V c hVn hV16 hVe hc3 hfree
  obtain ⟨N, hNn, ⟨eN⟩, ψ, -, ⟨eK⟩⟩ := hext
  let θ : Z →* Multiplicative (ZMod 2) := ψ.comp (QuotientGroup.mk' N)
  have hθc : θ c = 1 := by
    have h3 : θ c ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
    exact (by decide : ∀ x : Multiplicative (ZMod 2), x ^ 3 = 1 → x = 1) _ h3
  have hcomm : ∀ u : Z, θ u = 1 → c * u * c⁻¹ * u⁻¹ ∈ N := fun u hu =>
    comm_mem_of_isExtensionOf ψ eK hθc hu
  let θV : ↥V →* Multiplicative (ZMod 2) := θ.comp V.subtype
  have hker8 : 8 ≤ Nat.card θV.ker := by
    have h1 := Subgroup.index_mul_card θV.ker
    rw [Subgroup.index_ker, hV16] at h1
    have h2 : Nat.card θV.range ≤ 2 := by
      have := Subgroup.card_le_card_group θV.range
      rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2))] at this
    by_contra hlt
    have := Nat.mul_le_mul h2 (Nat.le_of_lt_succ (not_le.mp hlt))
    omega
  have hN4 : Nat.card ↥(V ⊓ N) ≤ 4 := card_inf_le_of_mulEquiv eN
    (mul_self_eq_one_of_isElemAbelian hVe) (by rw [Nat.card_eq_fintype_card]; decide)
  obtain ⟨u, huV, huθ, huN⟩ : ∃ u ∈ V, θ u = 1 ∧ u ∉ N := by
    by_contra hno
    push Not at hno
    have hle : Nat.card θV.ker ≤ Nat.card ↥(V ⊓ N) :=
      Nat.card_le_card_of_injective
        (fun u => (⟨u.1, u.1.2, hno u.1 u.1.2 (MonoidHom.mem_ker.mp u.2)⟩ : ↥(V ⊓ N)))
        (fun a b h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)))
    omega
  have hn : u⁻¹ * (c * u * c⁻¹) ∈ V ⊓ N := by
    refine ⟨V.mul_mem (V.inv_mem huV) (hVn.conj_mem u huV c), ?_⟩
    have h1 := hNn.conj_mem _ (hcomm u huθ) u⁻¹
    have e : u⁻¹ * (c * u * c⁻¹ * u⁻¹) * u⁻¹⁻¹ = u⁻¹ * (c * u * c⁻¹) := by group
    rwa [e] at h1
  let S : Set Z := (fun w => u * w) '' ((V ⊓ N : Subgroup Z) : Set Z)
  have hS : ∀ s ∈ S, c * s * c⁻¹ ∈ S := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨(u⁻¹ * (c * u * c⁻¹)) * (c * w * c⁻¹), (V ⊓ N).mul_mem hn
      ⟨hVn.conj_mem w hw.1 c, hNn.conj_mem w hw.2 c⟩, ?_⟩
    show u * (u⁻¹ * (c * u * c⁻¹) * (c * w * c⁻¹)) = c * (u * w) * c⁻¹
    group
  have hSW : Nat.card S = Nat.card ↥(V ⊓ N) :=
    Nat.card_image_of_injective (mul_right_injective u) _
  have hW3 : Nat.card ↥(V ⊓ N) % 3 ≠ 0 := by
    have hd : Nat.card ↥(V ⊓ N) ∣ 16 := hV16 ▸ Subgroup.card_dvd_of_le inf_le_left
    intro h0
    have : 3 ∣ 16 := (Nat.dvd_of_mod_eq_zero h0).trans hd
    omega
  obtain ⟨s, ⟨w, hw, rfl⟩, hsc⟩ := exists_fixed_of_card_mod_three hS hc3 (by rw [hSW]; exact hW3)
  have h1 : u * w = 1 := hfree (u * w) (V.mul_mem huV hw.1) hsc
  apply huN
  have : u = w⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [this]
  exact N.inv_mem hw.2

end Y15111

end CFSG.Quasithin
