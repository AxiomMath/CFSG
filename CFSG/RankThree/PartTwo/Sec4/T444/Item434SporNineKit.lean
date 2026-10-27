module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporNine

open CFSG CFSG.RankThree.PartTwo CFSG.LocalCores
open Item434Kit Item434Alt

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem false_of_le_M (h : Ctx434Core G A M Q) {D : Subgroup G}
    (hD : CFSG.Assembly.IsElemAbelian 3 D) (hD81 : 81 ≤ Nat.card D) (hDM : D ≤ M) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (Sec5.isPGroup_of_isElemAbelian hD).exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := D) (n := 4)
    (by rw [hk]; exact pow_dvd_pow 3 hk4)
  have hKe : CFSG.Assembly.IsElemAbelian 3 (K.map D.subtype) :=
    Sec5.isElemAbelian_of_le hD (Subgroup.map_subtype_le K)
  have h4 : 4 ≤ CFSG.Open.pRank 3 M :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three M)
      ⟨_, (Subgroup.map_subtype_le K).trans hDM, hKe,
        by rw [Subgroup.card_map_of_injective D.subtype_injective, hK]⟩
  rw [h.pRank_eq] at h4
  omega

theorem coe_mem_M_of_centralizer (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    (hZA : (Subgroup.center (layer G)).map (layer G).subtype ≤ A)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3)
    {U : Subgroup X}
    (hUA : A.map (quotConj e) = U.map (MulAut.conj : X →* MulAut X)) {u : X} (hu : u ∈ U)
    (hu1 : u ≠ 1) {x : layer G} (hx : layerQuot e x ∈ Subgroup.centralizer ({u} : Set X)) :
    (x : G) ∈ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  set Z' : Subgroup G := A ⊓ Subgroup.centralizer (layer G : Set G) with hZ'
  have hZ'e : CFSG.Assembly.IsElemAbelian 3 Z' := Sec5.isElemAbelian_of_le h.isE27.1 inf_le_left
  have hcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  have hZL : ∀ z : layer G, z ∈ Subgroup.center (layer G) → (z : G) ∈ Z' := by
    intro z hz
    refine ⟨hZA ⟨z, hz, rfl⟩, ?_⟩
    show (z : G) ∈ Subgroup.centralizer (layer G : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩)
  have hmem : (MulAut.conj u : MulAut X) ∈ A.map (quotConj e) := by
    rw [hUA]
    exact ⟨u, hu, rfl⟩
  obtain ⟨a, haA, hau⟩ := hmem
  have haZ' : a ∉ Z' := by
    intro haZ
    have h1 : quotConj e a = 1 := by
      rw [← MonoidHom.mem_ker, ker_quotConj h.isQuasisimple e]
      exact haZ.2
    rw [hau] at h1
    exact hu1 (hinj (h1.trans (map_one (MulAut.conj : X →* MulAut X)).symm))
  set B : Subgroup G := Z' ⊔ Subgroup.zpowers a with hB
  have hBA : B ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr haA)
  obtain ⟨-, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hZ'e haZ' (h.isE27.1.2 a haA)
    (fun z hz => hcommA z hz.1 a haA)
  have hB9 : 9 ≤ Nat.card B := by
    rw [hB, hBcard, hC3]
  have hxa : (x : G) * a * (x : G)⁻¹ ∈ B := by
    set c' : layer G := x * (layerConj G a x)⁻¹ with hc'
    have hc'ker : c' ∈ Subgroup.center (layer G) := by
      rw [← ker_layerQuot e, MonoidHom.mem_ker, hc', map_mul, map_inv, ← quotConj_layerQuot,
        hau, MulAut.conj_apply]
      have h1 : u * layerQuot e x * u⁻¹ = layerQuot e x := by
        have h2 := Subgroup.mem_centralizer_singleton_iff.mp hx
        rw [← h2, mul_inv_cancel_right]
      rw [h1, mul_inv_cancel]
    have hxa_eq : (x : G) * a * (x : G)⁻¹ = (c' : G) * a := by
      rw [hc']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, layerConj_apply_coe]
      group
    rw [hxa_eq]
    exact B.mul_mem (Subgroup.mem_sup_left (hZL c' hc'ker))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  have hmapB : B.map (MulAut.conj (x : G)).toMonoidHom ≤ B := by
    rw [hB, Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr hxa)
    rintro _ ⟨z, hz, rfl⟩
    have hxz : (x : G) * z * (x : G)⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp hz.2 x x.2
      rw [this, mul_inv_cancel_right]
    change (x : G) * z * (x : G)⁻¹ ∈ Z' ⊔ Subgroup.zpowers a
    rw [hxz]
    exact Subgroup.mem_sup_left hz
  have hxN : (x : G) ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.mem_normalizer_fintype fun n hn => hmapB ⟨n, hn, rfl⟩
  exact normalizer_le h hBA hB9 hxN

theorem false_of_lift_e81 (h : Ctx434Core G A M Q) (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hcen : Subgroup.center X = ⊥) (hZA : (Subgroup.center (layer G)).map (layer G).subtype ≤ A)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3)
    {U : Subgroup X} (hUA : A.map (quotConj e) = U.map (MulAut.conj : X →* MulAut X))
    (hU9 : Nat.card U = 9)
    (hlift : ∀ u ∈ U, u ≠ 1 → ∃ E : Subgroup (layer G), CFSG.Assembly.IsElemAbelian 3 E ∧
      81 ≤ Nat.card E ∧ ∀ x ∈ E, layerQuot e x ∈ Subgroup.centralizer ({u} : Set X)) :
    False := by
  have hU1 : U ≠ ⊥ := fun hbot => by
    rw [hbot, Subgroup.card_bot] at hU9
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU1
  have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  obtain ⟨E, hE, hE81, hEu⟩ := hlift u hu hu1'
  refine false_of_le_M h (D := E.map (layer G).subtype)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hE) ?_ ?_
  · rw [Subgroup.card_map_of_injective (layer G).subtype_injective]
    exact hE81
  · rintro _ ⟨y, hy, rfl⟩
    exact coe_mem_M_of_centralizer h e hcen hZA hC3 hUA hu hu1' (hEu y hy)

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item434SporNine
