module

public import CFSG.RankThree.PartOne.N1322.Bridge2
public import CFSG.RankThree.PartOne.NF7H.DatumStmt
public import CFSG.RankThree.PartOne.NF7J.Final
public import CFSG.RankThree.PartOne.NF7J.Trans
public import CFSG.RankThree.PartOne.N1322.CoreHyp

public section

namespace CFSG.RankThree.PartOne.N1322

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G} {c : G}
  {L E : Subgroup G}

theorem bridge (hGA : CFSG.Open.GriessAllModelsStatement)
    (h12 : Sec12Hyp G p A c L E) (hF12 : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    (hEA : E = A) (hL : ¬ IsLThreeTypeAt p L)
    (hOdd : KF1322Odd) (hKty : KF1322Kty) (hG2 : KF1322G2) (hPairJ : NF7J.PairMember)
    (hNF7U : NF7H.KF1322NF7U) :
    ∃ d : CoreData (ZMod p), CoreHyp d ∧
      (d.n = 4 → Nonempty (d.X ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) →
        Nonempty (reflectionGroup p E ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
          Nonempty (torusImage E L ≃* DihedralGroup 4)) := by
  obtain ⟨-, r, hr1, hr12, hmodel, hweyl, hr8, hr9⟩ := hF12.three
  have hp5 : 5 ≤ p := Sec12Three.five_le h12
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h12.A_card
  have hr_le8 : r ≤ 8 := by
    by_contra hlt
    have h4 := hr9 (by omega)
    have h34 : p ^ 3 = p ^ 4 := hcard.symm.trans h4
    have := Nat.pow_right_injective (Fact.out : p.Prime).two_le h34
    omega
  have hr_ne1 : r ≠ 1 := by
    rintro rfl
    exact hL hmodel
  have hr2 : 2 ≤ r := by omega
  obtain ⟨n, hn, he, hnr, hr7n⟩ : ∃ n : ℕ, (n = 4 ∨ n = 6 ∨ n = 8) ∧
      Nonempty (torusImage E L ≃* DihedralGroup n) ∧
        (n = 4 → (r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8)) ∧ (r = 7 → n = 4) := by
    rcases row_cases hr2 hr_le8 hweyl with ⟨e, hr⟩ | ⟨e, hr⟩ | ⟨e, hr⟩
    · exact ⟨6, Or.inr (Or.inl rfl), e, fun h => by omega, fun h => by omega⟩
    · exact ⟨8, Or.inr (Or.inr rfl), e, fun h => by omega, fun h => by omega⟩
    · exact ⟨4, Or.inl rfl, e, fun _ => hr, fun _ => rfl⟩
  obtain ⟨e'⟩ := he
  have hel := h12.E_elem
  obtain ⟨f⟩ := LinAlg.exists_coords E hcard
  have hcE : c ∈ E := by rw [hEA]; exact h12.c_mem
  obtain ⟨v, hv⟩ := Sec127.exists_vec f hcE
  have hv0 : v ≠ 0 := Sec127.vec_ne_zero f h12.c_ne_one hv
  have hinj := LinAlg.coordGL_injective f
  have hno : r ≠ 7 → ∀ t₀ ∈ reflectionSet p E, ∀ s₀ ∈ reflectionSet p E, DiffClass E L t₀ s₀ →
      ∀ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)), (r = 2 → w ∈ cNormalizer c) →
        conjAut E w hw * t₀ * (conjAut E w hw)⁻¹ ≠ s₀ := by
    intro hr7 t₀ ht₀ s₀ hs₀ hdc w hw hw2
    by_cases hr2' : r = 2
    · subst hr2'
      exact hG2 G p A c L E h12 hF12 hF13 hT hEA hL hmodel t₀ ht₀ s₀ hs₀ hdc w (hw2 rfl) hw
    · have hr3478 : r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 8 := by omega
      have hmod : RowModel p L 3 ∨ RowModel p L 4 ∨ RowModel p L 5 ∨ RowModel p L 6 ∨
          RowModel p L 8 := by
        rcases hr3478 with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl hmodel
        · exact Or.inr (Or.inl hmodel)
        · exact Or.inr (Or.inr (Or.inl hmodel))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hmodel)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hmodel)))
      exact hKty G p A c L E h12 hF12 hF13 hT hEA hL hmod t₀ ht₀ s₀ hs₀ hdc w hw
  have hlift : ∀ φ ∈ reflectionGroup p E, ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
      conjAut E w hw = φ := fun φ hφ =>
    Sec1322.exists_lift (Sec1322.reflectionGroup_le E hφ)
  have hdc : ∀ t₀ s₀ : MulAut E,
      LinAlg.coordGL f t₀ ∈ (torusImage E L).map (LinAlg.coordGL f) →
      LinAlg.coordGL f s₀ ∈ (torusImage E L).map (LinAlg.coordGL f) →
      (∀ l ∈ (torusImage E L).map (LinAlg.coordGL f),
        l * LinAlg.coordGL f t₀ * l⁻¹ ≠ LinAlg.coordGL f s₀) → DiffClass E L t₀ s₀ := by
    intro t₀ s₀ htL hsL hdiff
    refine ⟨(Subgroup.mem_map_iff_mem hinj).mp htL, (Subgroup.mem_map_iff_mem hinj).mp hsL,
      fun l hl heq => hdiff (LinAlg.coordGL f l) (Subgroup.mem_map_of_mem _ hl) ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul, heq]
  have hkAH : r ≠ 7 → ∀ g ∈ (reflectionGroup p E).map (LinAlg.coordGL f),
      (r = 2 → ∃ μ : ZMod p, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v = μ • v) →
      ∀ t ∈ LinAlg.coordGL f '' reflectionSet p E, ∀ s ∈ LinAlg.coordGL f '' reflectionSet p E,
        t ∈ (torusImage E L).map (LinAlg.coordGL f) → s ∈ (torusImage E L).map (LinAlg.coordGL f) →
        (∀ l ∈ (torusImage E L).map (LinAlg.coordGL f), l * t * l⁻¹ ≠ s) → g * t * g⁻¹ ≠ s := by
    intro hr7 g hg hcond2 t ht s hs htL hsL hdiff heq
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    obtain ⟨w, hw, hwφ⟩ := hlift φ hφ
    have hw2 : r = 2 → w ∈ cNormalizer c := by
      intro hr2
      refine Sec127.mem_cNormalizer_of_stabilizes f hv ⟨w, hw⟩ ?_
      obtain ⟨μ, hμ'⟩ := hcond2 hr2
      have h1 : LinAlg.wAction f ⟨w, hw⟩ v = LinAlg.coordHom f φ v := by
        rw [← hwφ]; rfl
      rw [h1, ← coordGL_mulVec_eq, hμ']
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    apply hno hr7 t₀ ht₀ s₀ hs₀ (hdc t₀ s₀ htL hsL hdiff) w hw hw2
    rw [hwφ]
    apply hinj
    rw [map_mul, map_mul, map_inv]
    exact heq
  refine ⟨⟨(reflectionGroup p E).map (LinAlg.coordGL f), LinAlg.coordGL f '' reflectionSet p E,
    (torusImage E L).map (LinAlg.coordGL f), v, n⟩, ?_, ?_⟩
  · exact
    { refl := fun g hg => by
        obtain ⟨t, ht, rfl⟩ := hg
        exact isRefl_coordGL f ht.1
      gen := map_reflectionGroup f
      Dconj := fun x hx g hg => by
        obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hx
        obtain ⟨t, ht, rfl⟩ := hg
        refine ⟨φ * t * φ⁻¹, coordGL_conj_mem hφ ht, ?_⟩
        rw [map_mul, map_mul, map_inv]
      Lle := Subgroup.map_mono (torusImage_le_reflectionGroup hF12)
      Lgen := map_closure_inter f hF12
      Ldih := ⟨(Subgroup.equivMapOfInjective (torusImage E L) (LinAlg.coordGL f) hinj).symm.trans
        e'⟩
      n_mem := hn
      c_ne := hv0
      c_fix := fixes_field f h12 hv
      lines := lines_field f h12 hF12 hv hv0
      N := N_field f hF12 hv
      kHU := by
        by_cases hr7 : r = 7
        · have hm7 : RowModel p L 7 := hr7 ▸ hmodel
          exact Or.inr ⟨hr7n hr7, hNF7U G p A c L E h12 hF12 hF13 hT hEA hL hm7 f v hv hv0⟩
        · exact Or.inl fun g hg hμ => hkAH hr7 g hg (fun _ => hμ)
      p5 := hp5
      irr := fun U hU => X_irreducible f h12 hF12 hF13 hv hv0 U (fun g hg w hw => hU ⟨g, hg⟩ w hw)
      noTransv := by
        intro g hg hg'
        obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg
        exact hF13.noTransvection ⟨φ, Sec1322.reflectionGroup_le E hφ,
          (LinAlg.isAutTransvection_iff_matrix_of_rank f φ).mpr hg'⟩
      kO := fun s hs t ht hodd => by
        obtain ⟨s₀, hs₀, rfl⟩ := hs
        obtain ⟨t₀, ht₀, rfl⟩ := ht
        have key := hOdd G p A c L E h12 hF12 hF13 hT hEA hL s₀ hs₀ t₀ ht₀
        rw [← map_mul, orderOf_injective (LinAlg.coordGL f) hinj] at hodd ⊢
        exact key hodd
      kAL := by
        by_cases hr7 : r = 7
        · right
          intro H hHX e7 hD hD'
          obtain ⟨D⟩ := NF7J.exists_datum f
            (fun x y => Subtype.ext (Torsion37.mul_comm_of_isElementaryAbelian hel x.2 y.2)) H hHX e7
            hD hD'
          exact NF7J.nf7j_false_of_pair hGA hPairJ h12 hF12 hF13 hT hEA hL (hr7 ▸ hmodel) D
        · left
          exact fun hn4 g hg _ => hkAH hr7 g hg (fun h2 => absurd h2 (by have := hnr hn4; omega)) }
  · intro hn4 he4
    obtain ⟨e4⟩ := he4
    refine ⟨⟨(Subgroup.equivMapOfInjective (reflectionGroup p E) (LinAlg.coordGL f) hinj).trans
      e4⟩, ?_⟩
    rcases hnr hn4 with rfl | rfl | rfl | rfl <;> exact hweyl

end CFSG.RankThree.PartOne.N1322
