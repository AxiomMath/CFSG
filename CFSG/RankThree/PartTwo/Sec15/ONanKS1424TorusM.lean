module

public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Torus
import CFSG.RankThree.PartOne.LIT.RankPSL3
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {T : Type} [Group T]

theorem isElemAbelian_map_hom {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian p E) :
    CFSG.Assembly.IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem pRank_three_le [Finite T] {n : ℕ} (hn : 1 ≤ n) (h : Sec4.IsoLThreePi T 2 n) :
    CFSG.Open.pRank 3 (⊤ : Subgroup T) ≤ 2 := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have : Finite (projSL 3 (GaloisField 2 n)) := Finite.of_equiv T φ.toEquiv
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ]
    exact CFSG.RankThree.PartOne.LIT.pRank_projSL_three_le hn (GaloisField.card 2 n (by omega))
      Nat.prime_three (by norm_num)
  · have : Finite (projSU 3 2 n) := Finite.of_equiv T φ.toEquiv
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ]
    exact CFSG.RankThree.PartOne.LIT.pRank_projSU_three_le hn Nat.prime_three (by norm_num)

theorem card_le_nine [Finite T] {n : ℕ} (hn : 1 ≤ n) (h : Sec4.IsoLThreePi T 2 n)
    {E : Subgroup T} (hE : CFSG.Assembly.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
  have hk2 : k ≤ 2 :=
    (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk).trans (pRank_three_le hn h)
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem card_top_prod (S : Subgroup T) :
    Nat.card ((⊤ : Subgroup (Multiplicative (ZMod 3))).prod S) = 3 * Nat.card S := by
  rw [Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup (Multiplicative (ZMod 3))) S).toEquiv,
    Nat.card_prod, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem proj_data [Finite T] {n : ℕ} (hn : 1 ≤ n) (h : Sec4.IsoLThreePi T 2 n)
    (Ā : Subgroup (Multiplicative (ZMod 3) × T)) (hĀe : CFSG.Assembly.IsElemAbelian 3 Ā)
    (hĀ27 : Nat.card Ā = 27) :
    CFSG.Assembly.IsElemAbelian 3 (Ā.map (MonoidHom.snd (Multiplicative (ZMod 3)) T)) ∧
      Nat.card (Ā.map (MonoidHom.snd (Multiplicative (ZMod 3)) T)) = 9 ∧
      Ā = (⊤ : Subgroup (Multiplicative (ZMod 3))).prod
        (Ā.map (MonoidHom.snd (Multiplicative (ZMod 3)) T)) := by
  set E : Subgroup T := Ā.map (MonoidHom.snd (Multiplicative (ZMod 3)) T) with hE
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := isElemAbelian_map_hom _ hĀe
  have hAle : Ā ≤ (⊤ : Subgroup (Multiplicative (ZMod 3))).prod E := fun a ha =>
    Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ⟨a, ha, rfl⟩⟩
  have hE9 : Nat.card E = 9 := by
    have h1 : 27 ≤ 3 * Nat.card E := by
      rw [← card_top_prod, ← hĀ27]
      exact Subgroup.card_le_of_le hAle
    have h2 := card_le_nine hn h hEe
    omega
  exact ⟨hEe, hE9, Subgroup.eq_of_le_of_card_ge hAle (by rw [card_top_prod, hE9, hĀ27])⟩

theorem torus_M {n : ℕ} (hn : 4 ≤ n) (h : Sec4.IsoLThreePi T 2 n)
    (Ā : Subgroup (Multiplicative (ZMod 3) × T)) (hĀe : CFSG.Assembly.IsElemAbelian 3 Ā)
    (hĀ27 : Nat.card Ā = 27)
    (hcen : Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) ≤ Ā) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ Ē : Subgroup (Multiplicative (ZMod 3) × T),
      CFSG.Assembly.IsElemAbelian p Ē ∧ Nat.card Ē = p ^ 2 ∧
      Ā ≤ Subgroup.normalizer (Ē : Set (Multiplicative (ZMod 3) × T)) ∧ ⁅Ē, Ā⁆ = Ē ∧
      Nat.card (Ā ⊓ Subgroup.centralizer (Ē : Set (Multiplicative (ZMod 3) × T)) :
        Subgroup (Multiplicative (ZMod 3) × T)) = 9 := by
  obtain ⟨π, K, _, hK, hq, ⟨M⟩⟩ := exists_lmodel (by omega : 1 ≤ n) h
  have := hK.finite
  have : Finite T := Finite.of_surjective M.μ M.surjective
  obtain ⟨hEe, hE9, hAeq⟩ := proj_data (by omega) h Ā hĀe hĀ27
  set E : Subgroup T := Ā.map (MonoidHom.snd (Multiplicative (ZMod 3)) T) with hE
  have hmemA : ∀ e ∈ E, ((1 : Multiplicative (ZMod 3)), e) ∈ Ā := fun e he => by
    rw [hAeq]
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, he⟩
  have hC : ∀ t : T, (∀ e ∈ E, t * e = e * t) → t ∈ E := by
    intro t ht
    have h1 : ((1 : Multiplicative (ZMod 3)), t) ∈
        Subgroup.centralizer (Ā : Set (Multiplicative (ZMod 3) × T)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      refine Prod.ext (by simp) ?_
      show a.2 * t = t * a.2
      exact (ht a.2 ⟨a, ha, rfl⟩).symm
    have h2 := hcen h1
    rw [hAeq] at h2
    exact (Subgroup.mem_prod.mp h2).2
  obtain ⟨r, hr, hr3, Ē, hĒe, hĒc, hEn, hĒE, hC3⟩ :=
    torus_model (by omega) hK hq M hEe hE9 hC
  have hinj : Function.Injective (MonoidHom.inr (Multiplicative (ZMod 3)) T) :=
    fun x y hxy => congrArg Prod.snd hxy
  have hnorm : Ā ≤ Subgroup.normalizer
      ((Ē.map (MonoidHom.inr (Multiplicative (ZMod 3)) T) : Subgroup _) : Set _) := by
    have hconj : ∀ b ∈ Ā, ∀ x ∈ Ē.map (MonoidHom.inr (Multiplicative (ZMod 3)) T),
        b * x * b⁻¹ ∈ Ē.map (MonoidHom.inr (Multiplicative (ZMod 3)) T) := by
      rintro b hb _ ⟨t, ht, rfl⟩
      have hb2 : b.2 ∈ E := ⟨b, hb, rfl⟩
      refine ⟨b.2 * t * b.2⁻¹, (Subgroup.mem_normalizer_iff.mp (hEn hb2) t).mp ht, ?_⟩
      refine Prod.ext ?_ rfl
      show (1 : Multiplicative (ZMod 3)) = b.1 * 1 * b.1⁻¹
      rw [mul_one]
      exact (mul_inv_cancel b.1).symm
    intro a ha
    exact Subgroup.mem_normalizer_fintype fun x hx => hconj a ha x hx
  refine ⟨r, hr, hr3, Ē.map (MonoidHom.inr (Multiplicative (ZMod 3)) T),
    isElemAbelian_map_hom _ hĒe, ?_, hnorm, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hĒc]
  · apply le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hnorm)
    have hle : E.map (MonoidHom.inr (Multiplicative (ZMod 3)) T) ≤ Ā := by
      rintro _ ⟨e, he, rfl⟩
      exact hmemA e he
    calc Ē.map (MonoidHom.inr (Multiplicative (ZMod 3)) T)
        = (⁅Ē, E⁆).map (MonoidHom.inr (Multiplicative (ZMod 3)) T) := by rw [hĒE]
      _ = ⁅Ē.map (MonoidHom.inr (Multiplicative (ZMod 3)) T),
            E.map (MonoidHom.inr (Multiplicative (ZMod 3)) T)⁆ := Subgroup.map_commutator _ _ _
      _ ≤ ⁅Ē.map (MonoidHom.inr (Multiplicative (ZMod 3)) T), Ā⁆ :=
          Subgroup.commutator_mono le_rfl hle
  · have hD : Ā ⊓ Subgroup.centralizer
        ((Ē.map (MonoidHom.inr (Multiplicative (ZMod 3)) T) : Subgroup _) : Set _) =
        (⊤ : Subgroup (Multiplicative (ZMod 3))).prod
          (E ⊓ Subgroup.centralizer (Ē : Set T)) := by
      ext a
      constructor
      · rintro ⟨haA, haC⟩
        have ha2 : a.2 ∈ E := ⟨a, haA, rfl⟩
        refine Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ha2, ?_⟩
        show a.2 ∈ Subgroup.centralizer (Ē : Set T)
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have := Subgroup.mem_centralizer_iff.mp haC (1, t) ⟨t, ht, rfl⟩
        exact congrArg Prod.snd this
      · intro ha
        obtain ⟨-, ha2E, ha2C⟩ := Subgroup.mem_prod.mp ha
        refine ⟨hAeq ▸ Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, ha2E⟩, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr ?_
        rintro _ ⟨t, ht, rfl⟩
        refine Prod.ext (by simp) ?_
        exact Subgroup.mem_centralizer_iff.mp ha2C t ht
    rw [hD, card_top_prod, hC3]

end CFSG.RankThree.PartTwo.Sec15.KS1424
