module

public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

@[expose] def jAtLeast (m q : ℕ) (X : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ X ∧ IsElemAbelian 2 E ∧ m ≤ q * Nat.card E), E

theorem jAtLeast_le (m q : ℕ) (X : Subgroup G) : jAtLeast m q X ≤ X := by
  rw [jAtLeast]
  exact iSup_le fun _ => iSup_le fun hE => hE.1

theorem le_jAtLeast {m q : ℕ} {X E : Subgroup G} (hEX : E ≤ X)
    (hE : IsElemAbelian 2 E) (hm : m ≤ q * Nat.card E) : E ≤ jAtLeast m q X := by
  rw [jAtLeast]
  exact le_iSup₂_of_le E ⟨hEX, hE, hm⟩ le_rfl

theorem jAtLeast_mono {m q : ℕ} {X Y : Subgroup G} (h : X ≤ Y) :
    jAtLeast m q X ≤ jAtLeast m q Y := by
  rw [jAtLeast]
  exact iSup_le fun E => iSup_le fun hE =>
    le_jAtLeast (hE.1.trans h) hE.2.1 hE.2.2

theorem jAtLeast_eq_of_le {m q : ℕ} {X Y : Subgroup G}
    (h1 : jAtLeast m q Y ≤ X) (h2 : X ≤ Y) :
    jAtLeast m q X = jAtLeast m q Y := by
  refine le_antisymm ?_ ?_
  · rw [jAtLeast]
    exact iSup_le fun E => iSup_le fun hE =>
      le_jAtLeast (hE.1.trans h2) hE.2.1 hE.2.2
  · rw [jAtLeast]
    exact iSup_le fun E => iSup_le fun hE =>
      le_jAtLeast ((le_jAtLeast hE.1 hE.2.1 hE.2.2).trans h1) hE.2.1 hE.2.2

private theorem map_conj_le_jAtLeast {m q : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    (jAtLeast m q X).map (MulAut.conj g) ≤ jAtLeast m q X := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg
  rw [jAtLeast, Subgroup.map_iSup]
  refine iSup_le fun E => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hE => ?_
  refine le_jAtLeast ?_ ?_ ?_
  · exact (Subgroup.map_mono hE.1).trans (le_of_eq hg)
  · exact CFSG.SectionRank.isElemAbelian_map hE.2.1 (MulAut.conj g).toMonoidHom
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE.2.2

theorem normalizer_le_normalizer_jAtLeast (m q : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (jAtLeast m q X : Set G) := by
  intro g hg
  have hle := map_conj_le_jAtLeast (m := m) (q := q) (X := X) hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem exists_not_le_of_not_jAtLeast_le {m q : ℕ} {X Y : Subgroup G}
    (h : ¬ jAtLeast m q X ≤ Y) :
    ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian 2 E ∧ m ≤ q * Nat.card E ∧ ¬ E ≤ Y := by
  by_contra hcon
  apply h
  rw [jAtLeast]
  refine iSup_le fun E => iSup_le fun hE => ?_
  by_contra hEY
  exact hcon ⟨E, hE.1, hE.2.1, hE.2.2, hEY⟩

theorem thompsonJ_le_jAtLeast {q : ℕ} (hq : 1 ≤ q) (S : Subgroup G) :
    thompsonJ S ≤ jAtLeast (2 ^ pRank 2 S) q S := by
  rw [thompsonJ]
  refine iSup_le fun A => iSup_le fun hA => ?_
  have hcard : Nat.card A = 2 ^ pRank 2 S := by
    have := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
    simpa using this
  refine le_jAtLeast hA.1 hA.2.1 ?_
  rw [← hcard]
  exact Nat.le_mul_of_pos_left _ (by omega)

theorem relIndex_centralizer_le_mul {S V F : Subgroup G} {k : ℕ}
    (hV : IsElemAbelian 2 V) (hVS : V ≤ S) (hF : IsElemAbelian 2 F) (hFS : F ≤ S)
    (hk : 2 ^ pRank 2 S ≤ k * Nat.card F) :
    (Subgroup.centralizer (F : Set G)).relIndex V ≤
      k * (Subgroup.centralizer (V : Set G)).relIndex F := by
  have hFp : IsPGroup 2 F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hFp
  have haS : a ≤ pRank 2 S :=
    CFSG.SectionRank.le_pRank (by norm_num) hFS hF ha
  have hcardF : Nat.card F * 2 ^ (pRank 2 S - a) = 2 ^ pRank 2 S := by
    rw [ha, ← pow_add, Nat.add_sub_of_le haS]
  have hFc : IsElemAbelianCorank S (pRank 2 S - a) F := ⟨hFS, hF, hcardF⟩
  let CF : Subgroup G := Subgroup.centralizer (F : Set G)
  let CV : Subgroup G := Subgroup.centralizer (V : Set G)
  change CF.relIndex V ≤ k * CV.relIndex F
  have hle : Nat.card V ≤ (F ⊓ CV).relIndex F *
      Nat.card ↥(V ⊓ CF) * 2 ^ (pRank 2 S - a) :=
    card_le_relIndex_mul_card_mul_two_pow hV hVS hFc
  rw [Subgroup.inf_relIndex_left] at hle
  have hVcard : CF.relIndex V * Nat.card ↥(V ⊓ CF) = Nat.card V := by
    rw [inf_comm V CF]
    exact Subgroup.relIndex_mul_card CF V
  have h1 : CF.relIndex V * Nat.card ↥(V ⊓ CF) ≤
      (CV.relIndex F * 2 ^ (pRank 2 S - a)) * Nat.card ↥(V ⊓ CF) := by
    rw [hVcard]
    calc Nat.card V ≤ CV.relIndex F * Nat.card ↥(V ⊓ CF) *
          2 ^ (pRank 2 S - a) := hle
      _ = (CV.relIndex F * 2 ^ (pRank 2 S - a)) * Nat.card ↥(V ⊓ CF) := by ring
  have h2 : CF.relIndex V ≤ CV.relIndex F * 2 ^ (pRank 2 S - a) :=
    Nat.le_of_mul_le_mul_right h1 Nat.card_pos
  have hk' : 2 ^ (pRank 2 S - a) * Nat.card F ≤ k * Nat.card F := by
    calc 2 ^ (pRank 2 S - a) * Nat.card F = Nat.card F * 2 ^ (pRank 2 S - a) := by
          rw [mul_comm]
      _ = 2 ^ pRank 2 S := hcardF
      _ ≤ k * Nat.card F := hk
  have h3 : 2 ^ (pRank 2 S - a) ≤ k :=
    Nat.le_of_mul_le_mul_right hk' Nat.card_pos
  calc CF.relIndex V
      ≤ CV.relIndex F * 2 ^ (pRank 2 S - a) := h2
    _ ≤ CV.relIndex F * k := Nat.mul_le_mul_left _ h3
    _ = k * CV.relIndex F := by ring

end CFSG.Quasithin.Stroth
