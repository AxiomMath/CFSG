module

public import CFSG.RankThree.PartTwo.Sec17.Item17ParaSTransfer
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaW
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

section Y1

variable {A : Subgroup G}

theorem map_conj_delta_le {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) (Y : Subgroup G) :
    (delta A (lB A) Y).map (MulAut.conj g).toMonoidHom ≤
      delta A (lB A) (Y.map (MulAut.conj g).toMonoidHom) := by
  rw [delta, Subgroup.map_le_iff_le_comap]
  refine sSup_le fun Q hQ => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_delta (rank3II_14_4_5 (isNaturalFamily_lB A) hg hQ.1) (Subgroup.map_mono hQ.2)

theorem map_conj_delta {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) (Y : Subgroup G) :
    (delta A (lB A) Y).map (MulAut.conj g).toMonoidHom =
      delta A (lB A) (Y.map (MulAut.conj g).toMonoidHom) := by
  refine le_antisymm (map_conj_delta_le hg Y) ?_
  have h := map_conj_delta_le (inv_mem hg) (Y.map (MulAut.conj g).toMonoidHom)
  rw [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h
  have h' := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h
  rwa [map_conj_map_conj, mul_inv_cancel, map_conj_one] at h'

theorem map_conj_mem_scriptY1 {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY1 A (lB A)) :
    Y.map (MulAut.conj g).toMonoidHom ∈ scriptY1 A (lB A) := by
  obtain ⟨⟨⟨⟨hYtop, hAY⟩, hO2⟩, hYΔ⟩, hO3⟩ := hY
  refine ⟨⟨⟨⟨fun htop => hYtop ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have h := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) htop
    rwa [map_conj_map_conj, inv_mul_cancel, map_conj_one,
      Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective] at h
  · calc A = A.map (MulAut.conj g).toMonoidHom := (Late.map_conj_eq_of_mem_normalizer hg).symm
      _ ≤ (Subgroup.normalizer (Y : Set G)).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hAY
      _ = _ := Subgroup.map_equiv_normalizer_eq Y (MulAut.conj g)
  · rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv]
    exact fun h => hO2 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp h)
  · rw [← map_conj_delta hg, ← hYΔ]
  · rw [← Sec21.map_oPrimeResidualOf, hO3, Subgroup.map_bot]

theorem map_conj_mem_scriptY1Star {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    {Y : Subgroup G} (hY : Y ∈ scriptY1Star A (lB A)) :
    Y.map (MulAut.conj g).toMonoidHom ∈ scriptY1Star A (lB A) :=
  maximal_map_conj (W := Subgroup.normalizer (A : Set G))
    (fun _ hS _ hw => map_conj_mem_scriptY1 hw hS) hY hg

end Y1

section Normalizes

omit [Finite G] in
theorem conj_inv_eq_of_commute {k c : G} (h : k * c = c * k) : k⁻¹ * c⁻¹ * k⁻¹⁻¹ = c⁻¹ := by
  rw [inv_inv, (Commute.inv_inv (show Commute k c from h)).eq, inv_mul_cancel_right]

theorem Sec15R.normalizer_zpowers_le_normalizer_L {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h3 : 3 ∣ Nat.card L) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  have hz : Subgroup.zpowers ((MulAut.conj g) c) = Subgroup.zpowers c := by
    have hmap : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom =
        Subgroup.zpowers ((MulAut.conj g) c) := MonoidHom.map_zpowers _ _
    rw [← hmap]
    exact Late.map_conj_eq_of_mem_normalizer hg
  have hLg : L.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 c := by
    have := map_mem_thetaComponentsAt (MulAut.conj g) h.mem_lA.1
    rwa [thetaComponentsAt_eq_thetaComponentsIn, centralizer_singleton_eq_of_zpowers_eq hz,
      ← thetaComponentsAt_eq_thetaComponentsIn] at this
  have h3' : 3 ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 _ hLg h3'
  exact mem_normalizer_of_map_conj_eq' heq

end Normalizes

section Inverts

variable {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G} {w : G}
  {Q : Subgroup G}

theorem Sec17W.exists_inverts_c
    (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1721 : Item1721)
    (h175 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item175 A c)
    (h : Sec17W G A c L Y₀ Y₁ S p P w Q) :
    ∃ s₁ ∈ Subgroup.normalizer (A : Set G), s₁ * c * s₁⁻¹ = c⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  obtain ⟨hΩ, hcL, -, hAeq⟩ := h.hj_facts h1715 h415 hJ
  have hwL : w ∈ L := (Subgroup.mem_inf.mp h.w_mem).2
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_mem hwL h.orderOf_w
  have hc3 : c ^ 3 = 1 := h.c_pow_three
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ one_mem L)
  have hc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcA : c ∈ A := h.c_mem
  have hAc : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_of_mem ha hcA)
  obtain ⟨T, hT, hAT⟩ := Item134SylowBarProof.exists_isSylowOf_le hAc h.isE27.isPGroup
  have hCL := Sec15R.centralizer_le_normalizer_L h.toSec15R h3L
  have hS : IsSylowOf 3 (T ⊓ L) L := hT.inf_of_le_normalizer h.le_centralizer_c hCL
  have hcomm := commutator_mem_of_hj h415 hJ h.mem_partTwoF hAeq h.le_centralizer_c hc
    hT.isPGroup hAT hT.le (hT.le.trans hCL) hS
  obtain ⟨h₀, hh₀⟩ := exists_conj_eq_inv_of_weaklyClosed h.isSimpleGroup h.nonabelian hc hT
    (hAT hcA) (h175 G A c L h.toSec15R hΩ) hcomm hcL
  have hh₀z : (Subgroup.zpowers c).map (MulAut.conj h₀).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (h₀ * c * h₀⁻¹) = _
    rw [hh₀, Subgroup.zpowers_inv]
  have hh₀H : h₀ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_of_map_conj_eq' hh₀z
  have hh₀L : L.map (MulAut.conj h₀).toMonoidHom = L :=
    Late.map_conj_eq_of_mem_normalizer
      (Sec15R.normalizer_zpowers_le_normalizer_L h.toSec15R h3L hh₀H)
  have hAle : A ≤ Subgroup.zpowers c ⊔ L := by
    rw [hAeq]
    exact sup_le_sup_left inf_le_right _
  have hA'le : A.map (MulAut.conj h₀).toMonoidHom ≤ Subgroup.zpowers c ⊔ L := by
    calc A.map (MulAut.conj h₀).toMonoidHom ≤
          (Subgroup.zpowers c ⊔ L).map (MulAut.conj h₀).toMonoidHom := Subgroup.map_mono hAle
      _ = Subgroup.zpowers c ⊔ L := by rw [Subgroup.map_sup, hh₀z, hh₀L]
  have hcA' : c ∈ A.map (MulAut.conj h₀).toMonoidHom := by
    refine ⟨c⁻¹, inv_mem hcA, ?_⟩
    change h₀ * c⁻¹ * h₀⁻¹ = c
    have := congrArg (fun x => x⁻¹) hh₀
    simpa [mul_assoc] using this
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := Subgroup.mem_centralizer_iff.mpr fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hx)
  have hN3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  obtain ⟨g, hgL, hg⟩ := KFacts.KS14.j2_exists_conjugate_of_card_twentySeven_of_quot h415 hN3 hJ
    hcC hcL hc3 hAle hA'le hcA hcA' h.isE27.2
    (by rw [Subgroup.card_map_of_injective (MulAut.conj h₀).injective, h.isE27.2])
  refine ⟨g * h₀, mem_normalizer_of_map_conj_eq' ?_, ?_⟩
  · rw [map_conj_mul, hg, conjugate, map_conj_map_conj, mul_inv_cancel, map_conj_one]
  · have hgc : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp
      (h.le_centralizer_c hgL)
    have hgc' : g * c⁻¹ * g⁻¹ = c⁻¹ := by
      rw [(Commute.inv_right (show Commute g c from hgc)).eq, mul_inv_cancel_right]
    calc g * h₀ * c * (g * h₀)⁻¹ = g * (h₀ * c * h₀⁻¹) * g⁻¹ := by group
      _ = c⁻¹ := by rw [hh₀, hgc']

theorem Sec17W.exists_inverts_c_normalizes
    (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1721 : Item1721)
    (h175 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item175 A c)
    (h : Sec17W G A c L Y₀ Y₁ S p P w Q) :
    ∃ s₂ ∈ Subgroup.normalizer (A : Set G), s₂ * c * s₂⁻¹ = c⁻¹ ∧
      s₂ ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  obtain ⟨-, -, h9, hAeq⟩ := h.hj_facts h1715 h415 hJ
  obtain ⟨s₁, hs₁A, hs₁c⟩ := h.exists_inverts_c h415 h1715 h1721 h175
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
  have hwL : w ∈ L := (Subgroup.mem_inf.mp h.w_mem).2
  have h3L : 3 ∣ Nat.card L := three_dvd_card_of_mem hwL h.orderOf_w
  have hs₁z : (Subgroup.zpowers c).map (MulAut.conj s₁).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (s₁ * c * s₁⁻¹) = _
    rw [hs₁c, Subgroup.zpowers_inv]
  have hs₁L : s₁ ∈ Subgroup.normalizer (L : Set G) :=
    Sec15R.normalizer_zpowers_le_normalizer_L h.toSec15R h3L (mem_normalizer_of_map_conj_eq' hs₁z)
  set w₁ := s₁ * w * s₁⁻¹ with hw₁
  have hw₁A : w₁ ∈ Subgroup.normalizer (A : Set G) := mul_mem (mul_mem hs₁A hwA) (inv_mem hs₁A)
  have hw₁L : w₁ ∈ L := (Subgroup.mem_normalizer_iff.mp hs₁L w).mp hwL
  have hw₁nA : w₁ ∉ A := fun hmem => h.w_not_mem (by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hs₁A) _).mp hmem
    rwa [show s₁⁻¹ * w₁ * s₁⁻¹⁻¹ = w by rw [hw₁]; group] at this)
  have hw₁3 : orderOf w₁ = 3 := by
    rw [show w₁ = MulAut.conj s₁ w from rfl, MulEquiv.orderOf_eq, h.orderOf_w]
  obtain ⟨hT₁, hwN⟩ := isSylowOf_inf_sup_zpowers h415 hJ h.isE27 h9 hwA hwL h.w_not_mem
    h.orderOf_w
  obtain ⟨hT₂, hw₁N⟩ := isSylowOf_inf_sup_zpowers h415 hJ h.isE27 h9 hw₁A hw₁L hw₁nA hw₁3
  set K := L ⊓ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) with hK
  have hT₁K : IsSylowOf 3 ((A ⊓ L) ⊔ Subgroup.zpowers w) K :=
    isSylowOf_of_le_of_le hT₁ (le_inf hT₁.le (sup_le Subgroup.le_normalizer hwN)) inf_le_left
  have hT₂K : IsSylowOf 3 ((A ⊓ L) ⊔ Subgroup.zpowers w₁) K :=
    isSylowOf_of_le_of_le hT₂ (le_inf hT₂.le (sup_le Subgroup.le_normalizer hw₁N)) inf_le_left
  obtain ⟨k, hkK, hk⟩ := Item134SylowBarProof.exists_conj_of_isSylowOf hT₁K hT₂K
  have hkL : k ∈ L := (Subgroup.mem_inf.mp hkK).1
  have hkE : k ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hkK).2
  have hkc : k * c = c * k :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hkL)
  have hkz : (Subgroup.zpowers c).map (MulAut.conj k).toMonoidHom = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (k * c * k⁻¹) = _
    rw [hkc, mul_inv_cancel_right]
  have hkA : k ∈ Subgroup.normalizer (A : Set G) := by
    rw [hAeq]
    exact mem_normalizer_sup (mem_normalizer_of_map_conj_eq' hkz) hkE
  refine ⟨k⁻¹ * s₁, mul_mem (inv_mem hkA) hs₁A, ?_, ?_⟩
  · have hkc' : k⁻¹ * c⁻¹ * k⁻¹⁻¹ = c⁻¹ := conj_inv_eq_of_commute hkc
    calc k⁻¹ * s₁ * c * (k⁻¹ * s₁)⁻¹ = k⁻¹ * (s₁ * c * s₁⁻¹) * k⁻¹⁻¹ := by group
      _ = c⁻¹ := by rw [hs₁c, hkc']
  · refine mem_normalizer_of_map_conj_eq' ?_
    have hsup : A ⊔ Subgroup.zpowers w = Subgroup.zpowers c ⊔ ((A ⊓ L) ⊔ Subgroup.zpowers w) := by
      conv_lhs => rw [hAeq]
      rw [sup_assoc]
    have hs₁Aw : (A ⊔ Subgroup.zpowers w).map (MulAut.conj s₁).toMonoidHom =
        Subgroup.zpowers c ⊔ ((A ⊓ L) ⊔ Subgroup.zpowers w₁) := by
      rw [Subgroup.map_sup, Late.map_conj_eq_of_mem_normalizer hs₁A, MonoidHom.map_zpowers]
      conv_lhs => rw [hAeq]
      rw [sup_assoc]
      rfl
    have hT₁k : ((A ⊓ L) ⊔ Subgroup.zpowers w₁).map (MulAut.conj k⁻¹).toMonoidHom =
        (A ⊓ L) ⊔ Subgroup.zpowers w := by
      rw [hk, map_conj_map_conj, inv_mul_cancel, map_conj_one]
    have hck : (Subgroup.zpowers c).map (MulAut.conj k⁻¹).toMonoidHom = Subgroup.zpowers c :=
      Late.map_conj_eq_of_mem_normalizer (inv_mem (mem_normalizer_of_map_conj_eq' hkz))
    calc (A ⊔ Subgroup.zpowers w).map (MulAut.conj (k⁻¹ * s₁)).toMonoidHom =
          ((A ⊔ Subgroup.zpowers w).map (MulAut.conj s₁).toMonoidHom).map
            (MulAut.conj k⁻¹).toMonoidHom := map_conj_mul _ _ _
      _ = (Subgroup.zpowers c ⊔ ((A ⊓ L) ⊔ Subgroup.zpowers w₁)).map
            (MulAut.conj k⁻¹).toMonoidHom := by rw [hs₁Aw]
      _ = Subgroup.zpowers c ⊔ ((A ⊓ L) ⊔ Subgroup.zpowers w) := by
          rw [Subgroup.map_sup, hck, hT₁k]
      _ = A ⊔ Subgroup.zpowers w := hsup.symm

end Inverts

end CFSG.RankThree.PartTwo.Sec17
