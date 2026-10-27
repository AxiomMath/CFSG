module

import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]

omit [Finite X] in
theorem inf_eq_bot_of_isPGroup_of_not_dvd {p : ℕ} (hp : p.Prime) {T K : Subgroup X}
    (hT : IsPGroup p T) (hK : ¬ p ∣ Nat.card K) : T ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hT ⟨x, hx.1⟩
  have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ Nat.card K := by
    rw [← Subgroup.orderOf_mk x hx.2]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) (Nat.card K) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hK)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem pRank_map_le_of_not_dvd {p : ℕ} (hp : p.Prime) (φ : X →* Y)
    (hker : ¬ p ∣ Nat.card φ.ker) (U : Subgroup X) :
    CFSG.Open.pRank p (U.map φ) ≤ CFSG.Open.pRank p U := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEU, hE, hEcard⟩ := Sec5.exists_elemAbelian_le_of_le_pRank hp
    (le_refl (CFSG.Open.pRank p (U.map φ)))
  set W : Subgroup X := U ⊓ E.comap φ with hW
  let ψ : W →* E := (φ.comp W.subtype).codRestrict E fun w => w.2.2
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨u, hu, hue⟩ := hEU e.2
    exact ⟨⟨u, hu, show φ u ∈ E by rw [hue]; exact e.2⟩, Subtype.ext hue⟩
  obtain ⟨T⟩ : Nonempty (Sylow p W) := inferInstance
  have hEp : IsPGroup p E := Sec5.isPGroup_of_isElemAbelian hE
  have htop : ((T.mapSurjective hψ : Sylow p E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hEp.to_subgroup ⊤) le_top).symm
  set T' : Subgroup X := (T : Subgroup W).map W.subtype with hT'
  have hT'p : IsPGroup p T' := T.isPGroup'.map _
  have hT'K : T' ⊓ φ.ker = ⊥ := inf_eq_bot_of_isPGroup_of_not_dvd hp hT'p hker
  have hinj : ∀ x ∈ T', ∀ y ∈ T', φ x = φ y → x = y := by
    intro x hx y hy hxy
    have hm : x * y⁻¹ ∈ T' ⊓ φ.ker :=
      ⟨T'.mul_mem hx (T'.inv_mem hy), show φ (x * y⁻¹) = 1 by
        rw [map_mul, map_inv, hxy, mul_inv_cancel]⟩
    rw [hT'K, Subgroup.mem_bot, mul_inv_eq_one] at hm
    exact hm
  have hT'E : T'.map φ = E := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
      exact w.2.2
    · intro e he
      have : (⟨e, he⟩ : E) ∈ ((T.mapSurjective hψ : Sylow p E) : Subgroup E) := htop ▸ trivial
      rw [Sylow.coe_mapSurjective] at this
      obtain ⟨w, hw, hwe⟩ := this
      exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwe⟩
  have hcard : Nat.card T' = Nat.card E := by
    rw [← hT'E]
    exact Nat.card_congr (Equiv.ofBijective (fun x : T' => (⟨φ x, ⟨x, x.2, rfl⟩⟩ : T'.map φ))
      ⟨fun x y hxy => Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy)),
        fun ⟨_, ⟨x, hx, rfl⟩⟩ => ⟨⟨x, hx⟩, rfl⟩⟩)
  have hT'e : CFSG.Assembly.IsElemAbelian p T' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj _ (T'.mul_mem a.2 b.2) _ (T'.mul_mem b.2 a.2) ?_)⟩⟩,
      fun x hx => hinj _ (T'.pow_mem hx p) _ T'.one_mem ?_⟩
    · have ha : φ a ∈ E := hT'E ▸ Subgroup.mem_map_of_mem φ a.2
      have hb : φ b ∈ E := hT'E ▸ Subgroup.mem_map_of_mem φ b.2
      simp only [Subgroup.coe_mul, map_mul]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨φ a, ha⟩ ⟨φ b, hb⟩)
    · have hx' : φ x ∈ E := hT'E ▸ Subgroup.mem_map_of_mem φ hx
      rw [map_pow, hE.2 _ hx', map_one]
  have hT'U : T' ≤ U := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2.1
  exact Sec5.le_pRank_of_elemAbelian hp hT'U hT'e (by rw [hcard, hEcard])

theorem map_normalizer_eq_of_not_dvd {p : ℕ} (hp : p.Prime) (K : Subgroup X) [K.Normal]
    (hK : ¬ p ∣ Nat.card K) {B : Subgroup X} (hB : IsPGroup p B) :
    (Subgroup.normalizer (B : Set X)).map (QuotientGroup.mk' K) =
      Subgroup.normalizer ((B.map (QuotientGroup.mk' K) : Subgroup (X ⧸ K)) : Set (X ⧸ K)) := by
  have : Fact p.Prime := ⟨hp⟩
  set ρ := QuotientGroup.mk' K with hρ
  refine le_antisymm (Subgroup.le_normalizer_map ρ) ?_
  intro z hz
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K z
  set W := (B.map ρ).comap ρ with hW
  have hBW : B ≤ W := Subgroup.le_comap_map ρ B
  obtain ⟨T, hTB⟩ := (hB.comap_of_injective W.subtype W.subtype_injective |>.to_le
    (le_refl (B.subgroupOf W))).exists_le_sylow
  set T' : Subgroup X := (T : Subgroup W).map W.subtype with hT'
  have hBT' : B ≤ T' := by
    intro b hb
    exact ⟨⟨b, hBW hb⟩, hTB (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  have hT'p : IsPGroup p T' := T.isPGroup'.map _
  have hkerK : ¬ p ∣ Nat.card ρ.ker := by rwa [QuotientGroup.ker_mk']
  have hT'eq : T' = B := by
    refine (Subgroup.eq_of_le_of_card_ge hBT' ?_).symm
    have h1 : Nat.card T' = Nat.card (T'.map ρ) := by
      have hT'K : T' ⊓ ρ.ker = ⊥ := inf_eq_bot_of_isPGroup_of_not_dvd hp hT'p hkerK
      refine Nat.card_congr (Equiv.ofBijective (fun x : T' => (⟨ρ x, ⟨x, x.2, rfl⟩⟩ : T'.map ρ))
        ⟨fun x y hxy => Subtype.ext ?_, fun ⟨_, ⟨x, hx, rfl⟩⟩ => ⟨⟨x, hx⟩, rfl⟩⟩)
      have hxy' : ρ (x : X) = ρ (y : X) := congrArg Subtype.val hxy
      have hm : (x : X) * (y : X)⁻¹ ∈ T' ⊓ ρ.ker :=
        ⟨T'.mul_mem x.2 (T'.inv_mem y.2), show ρ ((x : X) * (y : X)⁻¹) = 1 by
          rw [map_mul, map_inv, hxy', mul_inv_cancel]⟩
      rw [hT'K, Subgroup.mem_bot, mul_inv_eq_one] at hm
      exact hm
    have h2 : T'.map ρ ≤ B.map ρ := by
      rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
      exact w.2
    have h3 : Nat.card (B.map ρ) ≤ Nat.card B :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd B ρ)
    rw [h1]
    exact (Subgroup.card_le_of_le h2).trans h3
  have hy : ∀ h ∈ W, y * h * y⁻¹ ∈ W := by
    intro h hh
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hz _).mp hh
  obtain ⟨h, hhW, hhy⟩ := OddKernel.exists_mul_mem_normalizer_of_sylow T hy
  rw [← hT', hT'eq] at hhy
  obtain ⟨b, hb, hbh⟩ := hhW
  refine ⟨b⁻¹ * (h * y), Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hb)) hhy,
    ?_⟩
  rw [map_mul, map_mul, map_inv, hbh, inv_mul_cancel_left]

end CFSG.RankThree.PartTwo.Sec4
