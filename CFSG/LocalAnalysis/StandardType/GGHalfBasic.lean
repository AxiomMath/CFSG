module

public import CFSG.LocalAnalysis.StandardType.GGHalfCoords
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockEmbed
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

theorem basic :
    (∀ b ∈ Bs, ∀ c ∈ Bs, b * c = c * b) ∧ (∀ b ∈ Bs, b ^ 3 = 1) ∧ x ∈ Bs ∧ y ∈ Bs ∧
    x ≠ 1 ∧ y ≠ 1 ∧ (∀ l ∈ L, x * l = l * x) ∧ (∀ k ∈ K, y * k = k * y) ∧
    (¬ ∀ k ∈ K, x * k = k * x) ∧
    (∀ g ∈ Bs, (∀ l ∈ L, g * l = l * g) → g ∈ Subgroup.zpowers x) := by
  obtain ⟨hI, hBs, hDJ⟩ := h.cfg
  obtain ⟨-, hp3, -, -, hnbr, -, -⟩ := h.nbr
  subst hp3
  have hSstar := hI.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb c hc
    exact congrArg Subtype.val (hBs.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc⟩)
  · exact hBs.2.1.2
  · exact hBs.1 hSstar.2.1
  · exact hBs.1 hnbr.1.2.1
  · exact hSstar.2.2.1
  · exact hnbr.1.2.2.1
  · intro l hl
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hSstar.2.2.2.1.1 hl)).symm
  · intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)).symm
  · intro hcomm
    apply hnbr.2.2.2
    have hbot : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcomm k hk).symm
    rw [hbot]
    exact bot_le
  · have hp : Nat.Prime 3 := hI.2.2.2.2.2.1.1
    have hxne : x ≠ 1 := hSstar.2.2.1
    have hxBs : x ∈ Bs := hBs.1 hSstar.2.1
    have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
    have hxpow : x ^ 3 = 1 := hBs.2.1.2 x hxBs
    have hxord : orderOf x = 3 := by
      have : Fact (Nat.Prime 3) := ⟨hp⟩
      exact orderOf_eq_prime hxpow hxne
    intro g hg hgc
    let S : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G)
    have hxS : x ∈ S := ⟨hxBs, Subgroup.mem_centralizer_iff.mpr (fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLx hl))⟩
    have hgS : g ∈ S := ⟨hg, Subgroup.mem_centralizer_iff.mpr (fun l hl =>
      (hgc l hl).symm)⟩
    have hSp : IsPGroup 3 ↥S := fun s => ⟨1, by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
      exact hBs.2.1.2 (s : G) s.2.1⟩
    have hScyc : IsCyclic ↥S := hSstar.2.2.2.2 S inf_le_right hSp
    obtain ⟨s, hs⟩ := hScyc.exists_generator
    have hmap : (Subgroup.zpowers s).map S.subtype = Subgroup.zpowers (s : G) :=
      MonoidHom.map_zpowers S.subtype s
    have hSeq : S = Subgroup.zpowers (s : G) := by
      apply le_antisymm
      · intro z hz
        have hz' : z ∈ (Subgroup.zpowers s).map S.subtype :=
          ⟨⟨z, hz⟩, hs ⟨z, hz⟩, rfl⟩
        rwa [hmap] at hz'
      · rw [Subgroup.zpowers_le]
        exact s.2
    have hs_pow : s ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      exact hBs.2.1.2 (s : G) s.2.1
    have hsord_dvd : orderOf s ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hs_pow
    have hsord : orderOf s = 3 := by
      rcases (Nat.dvd_prime hp).mp hsord_dvd with h1 | hp'
      · exfalso
        have hs1 : s = 1 := orderOf_eq_one_iff.mp h1
        have hxmem : (⟨x, hxS⟩ : S) ∈ Subgroup.zpowers s := hs ⟨x, hxS⟩
        rw [hs1] at hxmem
        have hxe : (⟨x, hxS⟩ : S) = 1 := by simpa using hxmem
        exact hxne (Subtype.ext_iff.mp hxe)
      · exact hp'
    have hcardS : Nat.card S = 3 := by
      have hord : orderOf (s : G) = orderOf s :=
        orderOf_injective S.subtype Subtype.coe_injective s
      rw [hSeq, Nat.card_zpowers, hord, hsord]
    have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, hxord]
    have hzxle : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxS
    have heq : Subgroup.zpowers x = S :=
      Subgroup.eq_of_le_of_card_ge hzxle (by rw [hcardS, hcardx])
    rw [heq]
    exact hgS

theorem pComponent_K : LargeEvenPComponent 3 (Subgroup.centralizer ({y} : Set G)) K := by
  obtain ⟨-, hp3, -, -, hnbr, -, -⟩ := h.nbr
  subst hp3
  exact hnbr.1.2.2.2.2.1

theorem pComponent_L : LargeEvenPComponent 3 (Subgroup.centralizer ({x} : Set G)) L := by
  obtain ⟨hI, hBs, hDJ⟩ := h.cfg
  obtain ⟨-, hp3, hn, -, -, -, -⟩ := h.nbr
  subst hp3
  have hinj : Function.Injective (φ₁.comp (slLower2Hom m)) :=
    h.coords.inj₁.comp (slLower2Hom_injective m)
  have hcardJ : Nat.card J = Nat.card (SpecialLinearGroup (Fin (m + 1)) F2) := by
    rw [← h.coords.rangeJ]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hm : 1 ≤ m := by omega
  have hpJ : 3 ∣ Nat.card J := by
    rw [hcardJ]
    exact three_dvd_card_sl m hm
  exact (eq_of_le_of_stdSub hI hDJ hpJ).2.1

end GGHalfCtx

end CFSG.StandardType

end
