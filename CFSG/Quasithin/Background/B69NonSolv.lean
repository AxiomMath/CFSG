module

public import CFSG.Quasithin.Background.B69Comp
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.B6Offenders

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

namespace B69

theorem isSolvable_pi {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)]
    (h : ∀ i, Group.IsSolvable (G i)) : Group.IsSolvable (∀ i, G i) := by
  choose n hn using fun i => (h i).solvable
  refine ⟨⟨∑ i, n i, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  funext i
  have h1 : (derivedSeries (∀ i, G i) (∑ i, n i)).map (Pi.evalMonoidHom G i) ≤
      derivedSeries (G i) (∑ i, n i) := map_derivedSeries_le_derivedSeries _ _
  have h2 : derivedSeries (G i) (∑ i, n i) ≤ derivedSeries (G i) (n i) :=
    derivedSeries_antitone (G i)
      (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i))
  have h3 : x i ∈ derivedSeries (G i) (n i) := h2 (h1 (Subgroup.mem_map_of_mem _ hx))
  rw [hn i, Subgroup.mem_bot] at h3
  exact h3

theorem isSolvable_iSup_of_commute {Ω : Type*} [Group Ω] {ι : Type*} [Fintype ι] (H : ι → Subgroup Ω)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a)
    (hs : ∀ i, Group.IsSolvable ↥(H i)) : Group.IsSolvable ↥(⨆ i, H i) := by
  have hcomm : Pairwise fun i j : ι => ∀ x y : Ω, x ∈ H i → y ∈ H j → Commute x y :=
    fun i j hij x y hx hy => hc i j hij x hx y hy
  have hpi : Group.IsSolvable (∀ i, ↥(H i)) := isSolvable_pi hs
  have hrange := Subgroup.noncommPiCoprod_range (H := H) (hcomm := hcomm)
  have hsurj : Function.Surjective (Subgroup.noncommPiCoprod hcomm).rangeRestrict :=
    (Subgroup.noncommPiCoprod hcomm).rangeRestrict_surjective
  have : Group.IsSolvable ↥(Subgroup.noncommPiCoprod hcomm).range :=
    Group.isSolvable_of_surjective hsurj
  rw [hrange] at this
  exact this

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem conjAut_eq_map (g : MulAut V) (A : Subgroup (MulAut V)) :
    B1.conjAut g A = A.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [B1.mem_conjAut, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

omit [Finite V] in
theorem conjAut_commutator {F A : Subgroup (MulAut V)} {g : MulAut V}
    (hF : F.map (MulAut.conj g).toMonoidHom = F) :
    B1.conjAut g ⁅F, A⁆ = ⁅F, B1.conjAut g A⁆ := by
  rw [conjAut_eq_map, conjAut_eq_map, Subgroup.map_commutator, hF]

theorem fitting_comm_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {X T M A : Subgroup (MulAut V)}
    (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥) (hns : ¬ Group.IsSolvable ↥X)
    (hA : IsFFStarMin X A) : ⁅fittingOfSub X, A⁆ = ⊥ := by
  by_contra hne
  by_cases hJ : ⁅fittingOfSub X, ffJP {A | IsFFStarMin X A} X⁆ = ⊥
  · have hAJ : A ≤ ffJP {A | IsFFStarMin X A} X :=
      le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ {A | IsFFStarMin X A}) =>
        ⨆ (_ : B ≤ X), B) A hA (le_iSup (fun _ : A ≤ X => A) hA.1.1)
    exact hne (le_bot_iff.1 (hJ ▸ Subgroup.commutator_mono le_rfl hAJ))
  · obtain ⟨s, H, h1, hdp, -, -, -, -, -, -, h4, -⟩ := CFSG.Quasithin.EmptyFaithfulMultiple.inputB19_holds V hV X hO2 hJ
    have hS := setting_fittingOfSub (X := X) hO2
    have hAX : A ≤ X := hA.1.1
    have hconj : ∀ g ∈ X, B1.conjAut g A ≤ ⨆ i, H i := by
      intro g hg
      have hmin : IsFFStarMin X (B1.conjAut g A) := by
        refine ⟨B1.isFFStarOffender_conjAut hA.1 hg, fun B hB hBA => ?_⟩
        have hB' : IsFFStarOffender X (B1.conjAut g⁻¹ B) :=
          B1.isFFStarOffender_conjAut hB (X.inv_mem hg)
        have hBA' : FFLe X (B1.conjAut g⁻¹ B) A := by
          have := B1.ffLe_conjAut hBA (X.inv_mem hg)
          rwa [B1.conjAut_inv_conjAut] at this
        have := hA.2 _ hB' hBA'
        rw [← B1.conjAut_conjAut_inv g B, this]
      have hnb : ⁅fittingOfSub X, B1.conjAut g A⁆ ≠ ⊥ := by
        intro hb
        apply hne
        have e := conjAut_commutator (A := A) (hS.map_conj_eq hg)
        rw [hb] at e
        have e2 := congrArg (B1.conjAut g⁻¹) e
        rw [B1.conjAut_inv_conjAut] at e2
        have e3 : B1.conjAut g⁻¹ (⊥ : Subgroup (MulAut V)) = ⊥ := by
          rw [conjAut_eq_map]
          exact Subgroup.map_bot _
        rw [e3] at e2
        exact e2
      obtain ⟨i, hi⟩ := (h4 _).1 ⟨hmin, hnb⟩
      exact hi.1.trans (le_iSup H i)
    set N : Subgroup (MulAut V) := Subgroup.closure {x | ∃ g ∈ X, ∃ a ∈ A, x = g * a * g⁻¹} with hN
    have hNgen : ∀ g ∈ X, ∀ a ∈ A, g * a * g⁻¹ ∈ N := fun g hg a ha =>
      Subgroup.subset_closure ⟨g, hg, a, ha, rfl⟩
    have hNX : N ≤ X := by
      rw [hN, Subgroup.closure_le]
      rintro _ ⟨g, hg, a, ha, rfl⟩
      exact X.mul_mem (X.mul_mem hg (hAX ha)) (X.inv_mem hg)
    have hAN : A ≤ N := fun a ha => by simpa using hNgen 1 X.one_mem a ha
    have hNn : X ≤ Subgroup.normalizer (N : Set (MulAut V)) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ k ∈ X, ∀ x ∈ N, k * x * k⁻¹ ∈ N := by
        intro k hk x hx
        induction hx using Subgroup.closure_induction with
        | mem x hx =>
          obtain ⟨g, hg, a, ha, rfl⟩ := hx
          have := hNgen (k * g) (X.mul_mem hk hg) a ha
          simpa [mul_assoc] using this
        | one => simp
        | mul x y _ _ ihx ihy => simpa [mul_assoc] using N.mul_mem ihx ihy
        | inv x _ ih => simpa [mul_assoc] using N.inv_mem ih
      intro x
      refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
      have := key k⁻¹ (X.inv_mem hk) _ hx
      simpa [mul_assoc] using this
    have hNY : N ≤ ⨆ i, H i := by
      rw [hN, Subgroup.closure_le]
      rintro _ ⟨g, hg, a, ha, rfl⟩
      exact hconj g hg (B1.mem_conjAut.2 (by simpa [mul_assoc] using ha))
    rcases h.le_kerIn_or_twoResidual_le hNX hNn with hJN | hK
    ·
      have := h.le_pCoreOf_of_isPGroup_of_le_kerIn
        (B6.isPGroup_two_of_isElemAbelian2 hA.1.2.2.1) (hAN.trans hJN)
      rw [hO2] at this
      exact hA.1.2.1 (le_bot_iff.1 this)
    ·
      apply hns
      have hsolvG : ∀ i, Group.IsSolvable ↥(H i) := fun i => by
        obtain ⟨e⟩ := (h1 i).2
        have hfin : Finite ↥(H i) := Finite.of_equiv _ e.symm.toEquiv
        have h6 : Nat.card ↥(H i) = 6 := by rw [Nat.card_congr e.toEquiv, card_sl2]
        have hsf : Squarefree (6 : ℕ) := by
          rw [show (6 : ℕ) = 2 * 3 by norm_num]
          exact (Nat.squarefree_mul (by norm_num)).2
            ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
        have : IsZGroup ↥(H i) := IsZGroup.of_squarefree (by rw [h6]; exact hsf)
        infer_instance
      have hcomm : ∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a := fun i j hij a ha b hb =>
        hdp.1 (some i) (some j) (by simpa using hij) a ha b hb
      have hsolvY := isSolvable_iSup_of_commute H hcomm hsolvG
      refine B6.isSolvable_of_twoResidual ?_
      rw [B6.twoResidual_top_eq_subgroupOf]
      let f : ↥((twoResidual X).subgroupOf X) →* ↥(⨆ i, H i) :=
        (((X.subtype.comp ((twoResidual X).subgroupOf X).subtype)).codRestrict (⨆ i, H i)
          (fun x => hNY (hK x.2)))
      refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(⨆ i, H i) => (z : MulAut V)) hxy

theorem exists_component_of_nonsolvable (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4)
    {X T M A : Subgroup (MulAut V)} (h : MinParabolic X T M) (hO2 : pCoreOf 2 X = ⊥)
    (hns : ¬ Group.IsSolvable ↥X) (hA : IsFFStarMin X A) :
    ∃ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X ∧ ⁅L, A⁆ = L :=
  exists_component hV hP4 hO2 hA (fitting_comm_eq_bot hV h hO2 hns hA)

end B69

end CFSG.Quasithin
