module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Cover

open CFSG CFSG.RankThree.PartTwo CFSG.LocalCores
open Item434Kit Item434Alt

theorem mulAut_eq_conj_of_ker_le_center {L X : Type*} [Group L] [Group X] [Group.IsPerfect L]
    (π : L →* X) (hπ : π.ker ≤ Subgroup.center L) (α : MulAut L) (ũ : L)
    (h : ∀ l, π (α l) = π ũ * π l * (π ũ)⁻¹) : α = MulAut.conj ũ := by
  have hmem : ∀ l, (MulAut.conj ũ l)⁻¹ * α l ∈ Subgroup.center L := by
    intro l
    apply hπ
    rw [MonoidHom.mem_ker, map_mul, map_inv, MulAut.conj_apply, map_mul, map_mul, map_inv, h l]
    group
  have hmul : ∀ l m, (MulAut.conj ũ (l * m))⁻¹ * α (l * m) =
      ((MulAut.conj ũ l)⁻¹ * α l) * ((MulAut.conj ũ m)⁻¹ * α m) := by
    intro l m
    have hc := Subgroup.mem_center_iff.mp (hmem l) ((MulAut.conj ũ m)⁻¹)
    calc (MulAut.conj ũ (l * m))⁻¹ * α (l * m)
        = (MulAut.conj ũ m)⁻¹ * ((MulAut.conj ũ l)⁻¹ * α l) * α m := by
          simp only [map_mul, mul_inv_rev, mul_assoc]
      _ = ((MulAut.conj ũ l)⁻¹ * α l) * (MulAut.conj ũ m)⁻¹ * α m := by rw [hc]
      _ = ((MulAut.conj ũ l)⁻¹ * α l) * ((MulAut.conj ũ m)⁻¹ * α m) := by rw [mul_assoc]
  let f : L →* Subgroup.center L :=
    { toFun := fun l => ⟨(MulAut.conj ũ l)⁻¹ * α l, hmem l⟩
      map_one' := by
        refine Subtype.ext ?_
        simp
      map_mul' := fun l m => Subtype.ext (hmul l m) }
  have hker : _root_.commutator L ≤ f.ker := Abelianization.commutator_subset_ker f
  ext l
  have hl : l ∈ f.ker := hker Group.IsPerfect.mem_commutator
  have h1 : (MulAut.conj ũ l)⁻¹ * α l = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
  exact (inv_mul_eq_one.mp h1).symm

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem layerConj_eq_conj (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {a : G} {u : X}
    (hau : quotConj e a = MulAut.conj u) {ũ : layer G} (hũ : layerQuot e ũ = u) :
    layerConj G a = MulAut.conj ũ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  refine mulAut_eq_conj_of_ker_le_center (layerQuot e) (le_of_eq (ker_layerQuot e)) _ ũ ?_
  intro l
  rw [← quotConj_layerQuot, hau, hũ, MulAut.conj_apply]

theorem conj_mem_center_layer (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) {a : G} {u : X}
    (hau : quotConj e a = MulAut.conj u) {z : layer G} (hz : z ∈ Subgroup.center (layer G)) :
    a * (z : G) = (z : G) * a := by
  obtain ⟨ũ, hũ⟩ := layerQuot_surjective e u
  have h1 := layerConj_eq_conj h e hau hũ
  have h2 : layerConj G a z = z := by
    rw [h1, MulAut.conj_apply]
    have hc := Subgroup.mem_center_iff.mp hz ũ
    calc ũ * z * ũ⁻¹ = z * ũ * ũ⁻¹ := by rw [hc]
      _ = z := by group
  have h3 := congrArg Subtype.val h2
  rw [layerConj_apply_coe] at h3
  calc a * (z : G) = a * z * a⁻¹ * a := by group
    _ = (z : G) * a := by rw [h3]

theorem mem_inf_centralizer_of_mem_center_layer (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hinn : A.map (quotConj e) ≤ (MulAut.conj : X →* MulAut X).range) {z : layer G}
    (hz : z ∈ Subgroup.center (layer G)) (hz3 : z ^ 3 = 1) :
    (z : G) ∈ A ⊓ Subgroup.centralizer (layer G : Set G) := by
  refine ⟨h.rank3II_4_35 ?_ (by exact congrArg Subtype.val hz3), ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨u, hu⟩ := hinn ⟨a, ha, rfl⟩
    exact conj_mem_center_layer h e hu.symm hz
  · show (z : G) ∈ Subgroup.centralizer (layer G : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨l, hl⟩)

theorem card_map_quotConj_eq (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) :
    Nat.card (A.map (quotConj e)) = Nat.card h.layerStar := by
  have h1 := card_eq_card_inf_ker_mul_card_map (quotConj e) A
  rw [ker_quotConj h.isQuasisimple e, h.isE27.2] at h1
  have h2 := h.card_inf_mul_card_layerStar
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.symm.trans h2.symm)

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
    (hinn : A.map (quotConj e) ≤ (MulAut.conj : X →* MulAut X).range)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3)
    {u : X} (hu1 : u ≠ 1) (hu : (MulAut.conj : X →* MulAut X) u ∈ A.map (quotConj e))
    {x : layer G} (hx : layerQuot e x ∈ Subgroup.centralizer ({u} : Set X)) :
    (x : G) ∈ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  set Z' : Subgroup G := A ⊓ Subgroup.centralizer (layer G : Set G) with hZ'
  have hZ'e : CFSG.Assembly.IsElemAbelian 3 Z' := Sec5.isElemAbelian_of_le h.isE27.1 inf_le_left
  obtain ⟨a, haA, hau⟩ := hu
  have haZ' : a ∉ Z' := by
    intro haZ
    have h1 : quotConj e a = 1 := by
      rw [← MonoidHom.mem_ker, ker_quotConj h.isQuasisimple e]
      exact haZ.2
    rw [hau] at h1
    exact hu1 (hinj (h1.trans (map_one (MulAut.conj : X →* MulAut X)).symm))
  set B : Subgroup G := Z' ⊔ Subgroup.zpowers a with hB
  have hBA : B ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr haA)
  have hcommA : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b := fun b hb c hc =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  obtain ⟨-, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hZ'e haZ' (h.isE27.1.2 a haA)
    (fun z hz => hcommA z hz.1 a haA)
  have hB9 : 9 ≤ Nat.card B := by
    rw [hB, hBcard, hC3]
  set ζ : layer G := x * (layerConj G a x)⁻¹ with hζ
  have hζker : ζ ∈ Subgroup.center (layer G) := by
    rw [← ker_layerQuot e, MonoidHom.mem_ker, hζ, map_mul, map_inv, ← quotConj_layerQuot, hau,
      MulAut.conj_apply]
    have h1 : u * layerQuot e x * u⁻¹ = layerQuot e x := by
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp hx
      rw [← h2, mul_inv_cancel_right]
    rw [h1, mul_inv_cancel]
  have hxa_eq : (x : G) * a * (x : G)⁻¹ = (ζ : G) * a := by
    rw [hζ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, layerConj_apply_coe]
    group
  have hacomm : a * (ζ : G) = (ζ : G) * a := conj_mem_center_layer h e hau hζker
  have hζ3 : ζ ^ 3 = 1 := by
    have h1 : (x : G) * a ^ 3 * (x : G)⁻¹ = 1 := by
      rw [h.isE27.1.2 a haA]
      group
    have h2 : (x : G) * a ^ 3 * (x : G)⁻¹ = ((ζ : G) * a) ^ 3 := by
      rw [← hxa_eq, conj_pow]
    have h3 : ((ζ : G) * a) ^ 3 = (ζ : G) ^ 3 * a ^ 3 := (Commute.mul_pow hacomm.symm 3)
    rw [h2, h3, h.isE27.1.2 a haA, mul_one] at h1
    exact Subtype.ext (by simpa using h1)
  have hζZ' : (ζ : G) ∈ Z' := mem_inf_centralizer_of_mem_center_layer h e hinn hζker hζ3
  have hxa : (x : G) * a * (x : G)⁻¹ ∈ B := by
    rw [hxa_eq]
    exact B.mul_mem (Subgroup.mem_sup_left hζZ') (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
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

theorem false_of_lift (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    (hinn : A.map (quotConj e) ≤ (MulAut.conj : X →* MulAut X).range)
    (hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3)
    {u : X} (hu1 : u ≠ 1) (hu : (MulAut.conj : X →* MulAut X) u ∈ A.map (quotConj e))
    {E : Subgroup (layer G)} (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE81 : 81 ≤ Nat.card E)
    (hEu : ∀ x ∈ E, layerQuot e x ∈ Subgroup.centralizer ({u} : Set X)) : False := by
  refine false_of_le_M h (D := E.map (layer G).subtype)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hE) ?_ ?_
  · rw [Subgroup.card_map_of_injective (layer G).subtype_injective]
    exact hE81
  · rintro _ ⟨y, hy, rfl⟩
    exact coe_mem_M_of_centralizer h e hcen hinn hC3 hu1 hu (hEu y hy)

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item434Cover
