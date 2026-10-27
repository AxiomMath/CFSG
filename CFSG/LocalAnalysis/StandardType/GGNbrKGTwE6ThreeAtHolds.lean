module

public import CFSG.LocalAnalysis.StandardType.GGNbrKGTwE6ThreeAtDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoLocalInducedAut
public import CFSG.LocalAnalysis.StandardType.GGTwoLocalStableSylow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

theorem ggTwoLocalLift_of_at {p r s : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (h : GGTwoLocalAt p r s R I F) : GGTwoLocalLift p r s R I F := by
  intro L' _ _ ψ hψ hker hperf a ha hφmem hainn
  haveI : Finite R := Finite.of_surjective ψ hψ
  have hZ : Subgroup.center R = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center R) with hc | hc
    · exact hc
    · exfalso
      obtain ⟨x, y, hxy⟩ := hna
      have hx : x ∈ Subgroup.center R := by rw [hc]; exact Subgroup.mem_top x
      have hy : y ∈ Subgroup.center R := by rw [hc]; exact Subgroup.mem_top y
      exact hxy (((Subgroup.mem_center_iff.mp hx) y).symm)
  obtain ⟨Θ, hΘinj, hΘ⟩ := TwoLocalAt.exists_inducedAut ψ hψ hker hZ hperf
  have hΘp : (Θ a) ^ p = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨φ, hφ, hφψ⟩ := hφmem
  have hΘmem : Θ a ∈ Subgroup.closure (I ∪ F) := by
    have hΘeq : Θ a = φ := by
      refine MulEquiv.ext fun x => ?_
      obtain ⟨l, rfl⟩ := hψ x
      rw [hΘ a l, hφψ l]
    rw [hΘeq]
    exact hφ
  have hΘconj : ∀ l : L', Θ (MulAut.conj l) = MulAut.conj (ψ l) := by
    intro l
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hψ x
    simp only [hΘ, MulAut.conj_apply, map_mul, map_inv]
  have hΘinn : Θ a ∉ (MulAut.conj : R →* MulAut R).range := by
    intro hrange
    rw [MonoidHom.mem_range] at hrange
    obtain ⟨r, hr⟩ := hrange
    obtain ⟨l, rfl⟩ := hψ r
    rw [← hΘconj l] at hr
    exact hainn ⟨l, hΘinj hr⟩
  obtain ⟨Ē, hle, hab, hGG, hr, hs'⟩ := h (inferInstance : Finite R) (Θ a) hΘp hΘmem hΘinn
  have hzmap : (Subgroup.zpowers a).map Θ = Subgroup.zpowers (Θ a) := by
    rw [Subgroup.zpowers_eq_closure, MonoidHom.map_closure, Set.image_singleton,
      Subgroup.zpowers_eq_closure]
  have hconjmap : (MulAut.conj : L' →* MulAut L').range.map Θ =
      (MulAut.conj : R →* MulAut R).range := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [MonoidHom.mem_range] at hx ⊢
      obtain ⟨l, rfl⟩ := hx
      exact ⟨ψ l, (hΘconj l).symm⟩
    · intro y hy
      rw [MonoidHom.mem_range] at hy
      obtain ⟨r, rfl⟩ := hy
      obtain ⟨l, rfl⟩ := hψ r
      rw [Subgroup.mem_map]
      exact ⟨MulAut.conj l, ⟨l, rfl⟩, hΘconj l⟩
  have hmap : (Subgroup.zpowers a ⊔ (MulAut.conj : L' →* MulAut L').range).map Θ =
      Subgroup.zpowers (Θ a) ⊔ (MulAut.conj : R →* MulAut R).range := by
    rw [Subgroup.map_sup, hzmap, hconjmap]
  have hHbar_le : Subgroup.zpowers (Θ a) ⊔ (MulAut.conj : R →* MulAut R).range ≤ Θ.range := by
    rw [← hmap]
    exact Subgroup.map_le_range Θ _
  have hErange : Ē ≤ Θ.range := hle.trans hHbar_le
  have hEmap : (Ē.comap Θ).map Θ = Ē :=
    Subgroup.map_comap_eq_self (f := Θ) (H := Ē) hErange
  have hcard : Nat.card (Ē.comap Θ) = Nat.card Ē := by
    rw [← Subgroup.card_map_of_injective (K := Ē.comap Θ) hΘinj, hEmap]
  have hE_le : Ē.comap Θ ≤ Subgroup.zpowers a ⊔ (MulAut.conj : L' →* MulAut L').range := by
    apply (Subgroup.map_le_map_iff_of_injective hΘinj).mp
    rw [hEmap, hmap]
    exact hle
  have hEab : IsElemAbelian p (Ē.comap Θ) := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro e1 e2
      apply Subtype.ext
      apply hΘinj
      change Θ ((e1 : MulAut L') * (e2 : MulAut L')) = Θ ((e2 : MulAut L') * (e1 : MulAut L'))
      rw [map_mul, map_mul]
      have h1 : Θ (e1 : MulAut L') ∈ Ē := Subgroup.mem_comap.mp e1.2
      have h2 : Θ (e2 : MulAut L') ∈ Ē := Subgroup.mem_comap.mp e2.2
      have hcomm := (isMulCommutative_iff.mp hab.1) (⟨Θ e1, h1⟩ : Ē) ⟨Θ e2, h2⟩
      simpa using congrArg Subtype.val hcomm
    · intro e he
      apply hΘinj
      rw [map_pow, map_one]
      exact hab.2 (Θ e) (Subgroup.mem_comap.mp he)
  obtain ⟨V, hV1, hV2, hVst⟩ := hGG
  have hEstab : ∀ e ∈ Ē.comap Θ, ∀ w : L', ψ w ∈ V → ψ (e w) ∈ V := by
    intro e he w hw
    rw [← hΘ e w]
    exact hVst (Θ e) (Subgroup.mem_comap.mp he) (ψ w) hw
  have hGG' : GGTwoLocalAut (Ē.comap Θ) :=
    TwoLocalAt.exists_stable_two_subgroup ψ hψ hker V hV1 hV2 (Ē.comap Θ) hEstab
  refine ⟨Ē.comap Θ, hE_le, hEab, hGG', ?_, ?_⟩
  · rw [hcard]; exact hr
  · intro hnotI
    rw [hcard]
    exact hs' (fun hmem => hnotI ⟨Θ a, hmem, fun l => hΘ a l⟩)

theorem ggNbrKGTwE6ThreeAddTwoLocal_of_at (h : GGNbrKGTwE6ThreeAddTwoLocalAt) :
    GGNbrKGTwE6ThreeAddTwoLocal := by
  intro lab hlab ht h3 Q hQ
  refine largeEvenRawDatum_mono ?_ (h lab hlab ht h3 Q hQ)
  rintro R _ I F ⟨hQ', hK⟩
  exact ⟨hQ', fun hs hna => ggTwoLocalLift_of_at hs hna (hK hs hna)⟩

end CFSG.StandardType
