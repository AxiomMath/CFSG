module

public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG.RankThree.PartOne

variable {G : Type} [Group G]

theorem mem_torusImage_iff {E Y : Subgroup G} {φ : MulAut E} :
    φ ∈ torusImage E Y ↔ ∃ (x : G) (hx : x ∈ Subgroup.normalizer (E : Set G)), x ∈ Y ∧
      E.normalizerMonoidHom ⟨x, hx⟩ = φ := by
  simp only [torusImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, x.2, hx, rfl⟩
  · rintro ⟨x, hx, hxY, rfl⟩
    exact ⟨⟨x, hx⟩, hxY, rfl⟩

theorem card_torusImage_dvd_of_injective {Q : Type} [Group Q] (ι : Q →* G)
    (hι : Function.Injective ι) {E : Subgroup Q} {V Y : Subgroup G} (hV : E.map ι = V)
    (hY : ∀ x, ι x ∈ Y) :
    Nat.card ↥(torusImage E ⊤) ∣ Nat.card ↥(torusImage V Y) := by
  subst hV
  let e : E ≃* E.map ι := Subgroup.equivMapOfInjective E ι hι
  have hle : (torusImage E ⊤).map (MulAut.congr e).toMonoidHom ≤ torusImage (E.map ι) Y := by
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨x, hx, -, rfl⟩ := mem_torusImage_iff.1 hα
    refine mem_torusImage_iff.2 ⟨ι x, Subgroup.le_normalizer_map ι (Subgroup.mem_map_of_mem ι hx),
      hY x, ?_⟩
    ext e'
    obtain ⟨e₀, rfl⟩ := e.surjective e'
    show ι x * ((e e₀ : E.map ι) : G) * (ι x)⁻¹ =
      ((e (E.normalizerMonoidHom ⟨x, hx⟩ (e.symm (e e₀))) : E.map ι) : G)
    rw [e.symm_apply_apply]
    simp [e, Subgroup.coe_equivMapOfInjective_apply]
  calc Nat.card ↥(torusImage E ⊤)
      = Nat.card ↥((torusImage E ⊤).map (MulAut.congr e).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.congr e).injective).symm
    _ ∣ Nat.card ↥(torusImage (E.map ι) Y) := Subgroup.card_dvd_of_le hle

theorem card_torusImage_dvd_of_card [Finite G] {V Y H : Subgroup G} {m : ℕ} (hHY : H ≤ Y)
    (hHc : H ≤ Subgroup.centralizer (V : Set G))
    (hN : Nat.card ↥(Y ⊓ Subgroup.normalizer (V : Set G)) = m * Nat.card ↥H) :
    Nat.card ↥(torusImage V Y) ∣ m := by
  classical
  have hHN : H ≤ Y ⊓ Subgroup.normalizer (V : Set G) :=
    le_inf hHY (hHc.trans (Subgroup.centralizer_le_normalizer (V : Set G)))
  let ψ : ↥(Y ⊓ Subgroup.normalizer (V : Set G)) →* MulAut V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)
  have hrange : ψ.range = torusImage V Y := by
    ext φ
    rw [mem_torusImage_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n.1, n.2.2, n.2.1, rfl⟩
    · rintro ⟨x, hx, hxY, rfl⟩
      exact ⟨⟨x, Subgroup.mem_inf.2 ⟨hxY, hx⟩⟩, rfl⟩
  have hker : H.subgroupOf (Y ⊓ Subgroup.normalizer (V : Set G)) ≤ ψ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext v
    have hc := Subgroup.mem_centralizer_iff.1 (hHc (Subgroup.mem_subgroupOf.1 hn)) v v.2
    show (n : G) * (v : G) * (n : G)⁻¹ = v
    rw [← hc]
    group
  have h1 := Subgroup.card_ker_mul_card_range ψ
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hker
  have h3 : Nat.card ↥(H.subgroupOf (Y ⊓ Subgroup.normalizer (V : Set G))) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [hc, h3, hN, hrange] at h1
  have h4 : Nat.card H * (c * Nat.card ↥(torusImage V Y)) = Nat.card H * m := by
    rw [← mul_assoc, h1, mul_comm]
  exact Dvd.intro_left c (Nat.eq_of_mul_eq_mul_left hpos h4)

end CFSG.RankThree.PartOne.K133H
