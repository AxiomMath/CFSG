module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEReduce

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal

namespace StdPosExc

theorem exists_stdPos_of_inducedToral {U C : Type} [Group U] [Group C]
    {Δ : UniversalRootDatum U} {ι : U →* C} (hι : Function.Surjective ι)
    (hkerι : ι.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card ι.ker))
    (hinv : ∀ γ ∈ Δ.roots, ∀ z ∈ Δ.rootGroup γ, z * z = 1) {𝒟 V : Subgroup (MulAut C)}
    (hV : ∀ δ ∈ V, ∀ γ ∈ Δ.roots, ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ,
      ι (h * z * h⁻¹) = δ (ι z))
    {G : Type} [Group G] [Finite G] {ψ : U →* G} {p r : ℕ} {Bs : Subgroup G}
    (hT : ∀ E : Subgroup (MulAut C), E ≤ 𝒟 → IsElemAbelian p E → p ^ r ≤ Nat.card E →
      ∃ g : C, E.map (MulAut.conj (MulAut.conj g)).toMonoidHom ≤ V)
    (hBs : IsElemAbelian p Bs) (hBN : Bs ≤ Subgroup.normalizer (ψ.range : Set G))
    (hind : ∀ b ∈ Bs, ∃ α ∈ 𝒟, LayerSixE.GGInduces ι ψ b α)
    (hcen : ∀ b ∈ Bs, LayerSixE.GGInduces ι ψ b 1 →
      b ∈ Subgroup.centralizer (ψ.range : Set G))
    (hc : p ^ r * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs) :
    ∃ s : U, GGKGPosStdPos Δ (ψ.comp (MulAut.conj s).toMonoidHom) Bs := by
  choose! α hα𝒟 hα using hind
  have hmul : ∀ x ∈ Bs, ∀ y ∈ Bs, α (x * y) = α x * α y := fun x hx y hy =>
    LayerSixE.GGInduces.unique hι (hBN (Bs.mul_mem hx hy)) (hα _ (Bs.mul_mem hx hy))
      ((hα x hx).mul (hBN hy) (hα y hy))
  let θ : ↥Bs →* MulAut C := MonoidHom.mk' (fun b => α b) fun x y => hmul x x.2 y y.2
  have hkerC : ∀ b : ↥Bs, θ b = 1 → (b : G) ∈ Subgroup.centralizer (ψ.range : Set G) := by
    intro b hb1
    change α b = 1 at hb1
    have h1 := hα b b.2
    rw [hb1] at h1
    exact hcen b b.2 h1
  have hkerle : Nat.card θ.ker ≤
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : ↥Bs) : G), (x : ↥Bs).2, hkerC x.1 (MonoidHom.mem_ker.mp x.2)⟩)
      fun x y hxy => ?_
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hcard : Nat.card ↥Bs ≤
      Nat.card θ.range * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
    rw [← Subgroup.card_ker_mul_card_range θ, mul_comm]
    exact Nat.mul_le_mul_left _ hkerle
  have hpos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) := Nat.card_pos
  have hr : p ^ r ≤ Nat.card θ.range := Nat.le_of_mul_le_mul_right (hc.trans hcard) hpos
  have hXel : IsElemAbelian p θ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, rfl⟩ := a
      obtain ⟨_, y, rfl⟩ := b
      apply Subtype.ext
      change θ x * θ y = θ y * θ x
      rw [← map_mul, ← map_mul, hBs.1.is_comm.comm x y]
    · rintro _ ⟨x, rfl⟩
      have hx : x ^ p = 1 := Subtype.ext (by simpa using hBs.2 x x.2)
      rw [← map_pow, hx, map_one]
  have hX𝒟 : θ.range ≤ 𝒟 := by
    rintro _ ⟨b, rfl⟩
    exact hα𝒟 b b.2
  obtain ⟨g, hg⟩ := hT θ.range hX𝒟 hXel hr
  obtain ⟨s, hs⟩ := hι g⁻¹
  refine ⟨s, fun b hb γ hγ => ?_⟩
  have hδ : MulAut.conj g * α b * (MulAut.conj g)⁻¹ ∈ V :=
    hg ⟨θ ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
  obtain ⟨h, hh, hhz⟩ := hV _ hδ γ hγ
  refine ⟨h, hh, fun z hz => ?_⟩
  show b * ψ (s * z * s⁻¹) * b⁻¹ = ψ (s * (h * z * h⁻¹) * s⁻¹)
  obtain ⟨y', hy'⟩ := LayerSixE.exists_conj_eq (hBN hb) (s * z * s⁻¹)
  have hιy' : ι y' = ι (s * (h * z * h⁻¹) * s⁻¹) := by
    have e1 : ι (s * (h * z * h⁻¹) * s⁻¹) = ι s * ι (h * z * h⁻¹) * (ι s)⁻¹ := by
      simp only [map_mul, map_inv]
    have e2 : ι (s * z * s⁻¹) = ι s * ι z * (ι s)⁻¹ := by simp only [map_mul, map_inv]
    rw [hα b hb _ _ hy', e1, e2, hhz z hz, hs]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, inv_inv]
    group
  obtain ⟨ζ, hζ⟩ : ∃ ζ : U, ζ = (s * (h * z * h⁻¹) * s⁻¹)⁻¹ * y' := ⟨_, rfl⟩
  have hζker : ζ ∈ ι.ker := by
    rw [MonoidHom.mem_ker, hζ, map_mul, map_inv, hιy', inv_mul_cancel]
  have hy'w : y' = s * (h * z * h⁻¹) * s⁻¹ * ζ := by rw [hζ, mul_inv_cancel_left]
  have hz2 : z * z = 1 := hinv γ hγ z hz
  have hww : s * (h * z * h⁻¹) * s⁻¹ * (s * (h * z * h⁻¹) * s⁻¹) = 1 := by
    calc _ = s * (h * (z * z) * h⁻¹) * s⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hψy' : ψ y' * ψ y' = 1 := by
    have e : ψ y' * ψ y' = b * ψ (s * z * s⁻¹ * (s * z * s⁻¹)) * b⁻¹ := by
      rw [hy', map_mul ψ (s * z * s⁻¹)]
      group
    rw [e, show s * z * s⁻¹ * (s * z * s⁻¹) = s * (z * z) * s⁻¹ by group, hz2]
    simp
  have hζ2 : ψ ζ * ψ ζ = 1 := by
    have hcomm := Subgroup.mem_center_iff.mp (hkerι hζker) (s * (h * z * h⁻¹) * s⁻¹)
    have hyy : y' * y' = ζ * ζ := by
      calc y' * y' = s * (h * z * h⁻¹) * s⁻¹ * (ζ * (s * (h * z * h⁻¹) * s⁻¹)) * ζ := by
            rw [hy'w]; group
        _ = s * (h * z * h⁻¹) * s⁻¹ * (s * (h * z * h⁻¹) * s⁻¹) * (ζ * ζ) := by
            rw [← hcomm]; group
        _ = ζ * ζ := by rw [hww, one_mul]
    rw [← map_mul, ← hyy, map_mul, hψy']
  have hψζ : ψ ζ = 1 := by
    have h1 : orderOf (⟨ζ, hζker⟩ : ι.ker) ∣ Nat.card ι.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    obtain ⟨m, hm⟩ := hodd.of_dvd_nat h1
    have h2 : ψ ζ ^ orderOf ζ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [hm, pow_succ, pow_mul, sq, hζ2, one_pow, one_mul] at h2
    exact h2
  calc b * ψ (s * z * s⁻¹) * b⁻¹ = ψ y' := hy'.symm
    _ = ψ (s * (h * z * h⁻¹) * s⁻¹) * ψ ζ := by rw [hy'w, map_mul ψ _ ζ]
    _ = ψ (s * (h * z * h⁻¹) * s⁻¹) := by rw [hψζ, mul_one]

end StdPosExc

end CFSG.StandardType

end
