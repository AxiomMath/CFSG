module

public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFix
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpComp
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpPull
import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
public import CFSG.Assembly.LargeEvenDefs

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

namespace CFSG.StandardType

namespace A6InsideSp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType.ChoiceTwo

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type}
  [Field L] [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)}
  (F : ChoiceTwo.SpFrame K n ζ E)

theorem exists_single_and_eq_spFixedFactor (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (hL : Module.finrank K L = 2) (hs : 4 ≤ F.s) {c : Fin F.s → ZMod 3} (hc : c ≠ 0)
    {B Lx D J : Subgroup (StatedSp n K)} (hBE : B ≤ E)
    (hLx : IsComponentOf Lx (Subgroup.centralizer {F.tor c}))
    (hcyc : ∀ S : Subgroup (StatedSp n K), S ≤ Subgroup.centralizer (Lx : Set (StatedSp n K)) →
      IsPGroup 3 S → IsCyclic S)
    (hpre : LargeEvenStdSubPre 3 B (F.tor c) Lx D J) (h27 : ¬ 27 ∣ Nat.card J) :
    ∃ i₀, (∀ i, c i ≠ 0 ↔ i = i₀) ∧ Lx = spFixedFactor (F.tor c) := by
  classical
  haveI hfin : Module.Finite K L := by
    haveI : Module.Finite K (Fin F.s → L) :=
      Module.Finite.of_injective F.Φ.toLinearMap F.Φ.injective
    have hi : Fin F.s := ⟨0, by omega⟩
    exact Module.Finite.of_surjective (LinearMap.proj (R := K) hi)
      (fun l => ⟨fun _ => l, rfl⟩)
  have hsn : F.s = n := s_eq F hL
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨i₀, hc₀⟩ : ∃ i : Fin F.s, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨hDB, -, hDcard, hxD, -, hJcomp, -⟩ := hpre
  have hx3 : F.tor c ^ 3 = 1 := F.tor_pow_three hζo.pow_eq_one c
  have hT3 : spEnd (F.tor c) ^ 3 = 1 := by
    rw [← ChoiceTwo.spEnd_pow, hx3, ChoiceTwo.spEnd_one]
  have blocks : SpPrimaryBlocks 2 1 3 (F.tor c) (proj n K (F.tor c)) :=
    F.blocks_tor hK hζo hc
  obtain ⟨h, hh, hLO⟩ := SevSpNs.exists_le_spSupported blocks hLx
  have hLx_le : Lx ≤ spFixedFactor (F.tor c) := by
    rcases primaryFactor_cases hK hT3 hh with rfl | rfl
    · rwa [KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton] at hLO
    · exfalso
      rw [ChoiceTwo.reciprocal_phi3, Set.pair_eq_singleton] at hLO
      have hLn : ∀ m ∈ Subgroup.centralizer ({F.tor c} : Set (StatedSp n K)),
          ∀ g ∈ Lx, m * g * m⁻¹ ∈ Lx :=
        (SevSpNs.exists_spSupported_of_isComponentOf (f := 1) (p := 3)
          (by simpa using hK) (by norm_num) Nat.prime_three (by norm_num)
          hx3 blocks hLx).1
      have hJCD : IsComponentOf J (Subgroup.centralizer (D : Set (StatedSp n K))) :=
        isComponentOf_centralizer_of_inf (x := F.tor c) (D := D) (L₀ := Lx) (J := J)
          hxD hLx.1 hLn hJcomp
      have hD9 : Nat.card D = 9 := by
        rw [hDcard]
        norm_num
      obtain ⟨d, hdD, hdi₀, hind, hDeq⟩ :=
        exists_eq_closure_pair F (c := c) (i₀ := i₀) hζo (hDB.trans hBE) hD9 hxD hc₀
      let cκ : ZMod 3 → Fin F.s → ZMod 3 :=
        fun κ i => if d i + κ * c i = 0 then c i else 0
      have hJle : ∀ κ : ZMod 3, J ≤ spFixedFactor (F.tor (cκ κ)) := by
        intro κ
        refine le_spFixedFactor_of_isComponentOf F hK hζo hL (f := cκ κ) (D := D) (Q := J)
          ?_ ?_ ?_ hJCD h27
        · rw [hDeq, Subgroup.closure_le]
          rintro g (rfl | rfl)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (F.tor_comm hζo.pow_eq_one c (cκ κ))
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (F.tor_comm hζo.pow_eq_one d (cκ κ))
        · intro g hgD
          have hmemD : F.tor (d + κ • c) ∈ D := by
            rw [hDeq]
            have heq : d + κ • c = κ • c + (1 : ZMod 3) • d := by
              rw [one_smul]
              abel
            rw [heq]
            exact (mem_closure_pair_iff F hζo.pow_eq_one).mpr ⟨κ, 1, rfl⟩
          have hg' : g ∈ Subgroup.centralizer ({F.tor (d + κ • c)} : Set (StatedSp n K)) := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact (Subgroup.mem_centralizer_iff.mp hgD _ hmemD).symm
          have hm1 : F.tor (cκ κ) ∈ spFixedFactor (F.tor (d + κ • c)) := by
            refine F.tor_mem_spFixedFactor hK hζo (d + κ • c) (cκ κ) ?_
            intro i hi
            show (if d i + κ * c i = 0 then c i else 0) = 0
            rw [if_neg (by simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hi)]
          have hm2 : F.tor (c - cκ κ) ∈ spSupported (F.tor (d + κ • c)) {phi3 K} := by
            refine F.tor_mem_spSupported hK hζo (d + κ • c) (c - cκ κ) ?_
              (Set.mem_singleton _)
            intro i hi
            show (c - cκ κ) i = 0
            have hci : cκ κ i = c i := by
              show (if d i + κ * c i = 0 then c i else 0) = c i
              rw [if_pos (by simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hi)]
            simp only [Pi.sub_apply, hci, sub_self]
          have hmul : F.tor (cκ κ) * F.tor (c - cκ κ) = F.tor c := by
            rw [← F.tor_add hζo.pow_eq_one]
            congr 1
            abel
          have hgm : g * (F.tor (cκ κ) * F.tor (c - cκ κ)) =
              F.tor (cκ κ) * F.tor (c - cκ κ) * g := by
            rw [hmul]
            exact (Subgroup.mem_centralizer_iff.mp hgD _ hxD).symm
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact commute_of_commute_mul hK (F.tor_pow_three hζo.pow_eq_one _) hm1 hm2 hg' hgm
        · intro g hg
          rw [hDeq, mem_centralizer_closure_pair]
          constructor
          · have h₁ : spSupported (F.tor (cκ κ)) {phi3 K} ≤
                Subgroup.centralizer ({F.tor c} : Set (StatedSp n K)) :=
              spSupported_le_centralizer_tor F hK hζo (κ := (1 : ZMod 3))
                (f := cκ κ) (h := c) (by
                  intro i hi
                  have hci : cκ κ i = c i := by
                    by_cases hcnd : d i + κ * c i = 0
                    · show (if d i + κ * c i = 0 then c i else 0) = c i
                      rw [if_pos hcnd]
                    · exact absurd (by
                        show (if d i + κ * c i = 0 then c i else 0) = 0
                        rw [if_neg hcnd]) hi
                  rw [one_mul, hci])
            exact Subgroup.mem_centralizer_singleton_iff.mp (h₁ hg)
          · have h₂ : spSupported (F.tor (cκ κ)) {phi3 K} ≤
                Subgroup.centralizer ({F.tor d} : Set (StatedSp n K)) :=
              spSupported_le_centralizer_tor F hK hζo (κ := -κ)
                (f := cκ κ) (h := d) (by
                  intro i hi
                  have hcnd : d i + κ * c i = 0 := by
                    by_contra hne
                    exact hi (by
                      show (if d i + κ * c i = 0 then c i else 0) = 0
                      rw [if_neg hne])
                  have hci : cκ κ i = c i := by
                    show (if d i + κ * c i = 0 then c i else 0) = c i
                    rw [if_pos hcnd]
                  rw [hci]
                  linear_combination hcnd)
            exact Subgroup.mem_centralizer_singleton_iff.mp (h₂ hg)
      have hJzero : ∀ i : Fin F.s, c i = 0 →
          J ≤ spFixedFactor (F.tor (Pi.single i (1 : ZMod 3))) := by
        intro i hi g hgJ
        have hgS : g ∈ spSupported (F.tor c) {phi3 K} := hLO (hJcomp.1 hgJ).1
        refine mem_spFixedFactor_of_disjoint F hK hζo (f₁ := Pi.single i (1 : ZMod 3))
          (f₂ := c) ?_ hgS ?_
        · intro k hk
          by_cases hki : k = i
          · subst hki
            exact hi
          · have h0 : (Pi.single (M := fun _ => ZMod 3) i (1 : ZMod 3)) k = 0 :=
              Pi.single_eq_of_ne hki 1
            exact absurd h0 hk
        · have hm : F.tor (Pi.single i (1 : ZMod 3)) ∈ spFixedFactor (F.tor c) := by
            refine F.tor_mem_spFixedFactor hK hζo c (Pi.single i (1 : ZMod 3)) ?_
            intro k hk
            by_cases hki : k = i
            · subst hki
              exact absurd hi hk
            · rw [Pi.single_eq_of_ne hki]
          exact (commute_of_mem_spFixedFactor hK hx3 (O := {phi3 K})
            (fun hmem => phi3_ne_X_sub_one hmem.symm) hm hgS).symm
      have hbot : J = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall J).mpr fun g hgJ => ?_
        refine eq_one_of_forall_mem_spFixedFactor F hK hζo
          (fs := Sum.elim (fun κ : ZMod 3 => cκ κ)
            (fun i : {k : Fin F.s // c k = 0} => Pi.single i.val (1 : ZMod 3))) ?_ ?_
        · intro i
          by_cases hi : c i = 0
          · refine ⟨Sum.inr ⟨i, hi⟩, ?_⟩
            simpa using (one_ne_zero : (1 : ZMod 3) ≠ 0)
          · refine ⟨Sum.inl (-(d i) * (c i)⁻¹), ?_⟩
            show (if d i + (-(d i) * (c i)⁻¹) * c i = 0 then c i else 0) ≠ 0
            have hsum : d i + (-(d i) * (c i)⁻¹) * c i = 0 := by
              rw [mul_assoc, inv_mul_cancel₀ hi, mul_one]
              exact add_neg_cancel _
            rw [if_pos hsum]
            exact hi
        · rintro (κ | ⟨i, hi⟩)
          · exact hJle κ hgJ
          · exact hJzero i hi hgJ
      have hle : J ≤ Subgroup.centralizer (J : Set (StatedSp n K)) := by
        rw [hbot]
        exact bot_le
      exact not_le_centralizer_self_of_isQuasisimple hJcomp.2.2 hle
  have hsingle : ∀ i : Fin F.s, c i ≠ 0 → i = i₀ := by
    intro i hi
    by_contra hne
    set u : StatedSp n K := F.tor (Pi.single i (1 : ZMod 3)) with hu
    set v : StatedSp n K := F.tor (Pi.single i₀ (1 : ZMod 3)) with hv
    have huS : u ∈ spSupported (F.tor c) {phi3 K} := by
      rw [hu]
      refine F.tor_mem_spSupported hK hζo c (Pi.single i (1 : ZMod 3)) ?_
        (Set.mem_singleton _)
      intro k hk
      by_cases hki : k = i
      · subst hki
        exact absurd hk hi
      · rw [Pi.single_eq_of_ne hki]
    have hvS : v ∈ spSupported (F.tor c) {phi3 K} := by
      rw [hv]
      refine F.tor_mem_spSupported hK hζo c (Pi.single i₀ (1 : ZMod 3)) ?_
        (Set.mem_singleton _)
      intro k hk
      by_cases hki : k = i₀
      · subst hki
        exact absurd hk hc₀
      · rw [Pi.single_eq_of_ne hki]
    have huC : u ∈ Subgroup.centralizer (Lx : Set (StatedSp n K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact commute_of_mem_spFixedFactor hK hx3 (O := {phi3 K})
        (fun hmem => phi3_ne_X_sub_one hmem.symm) (hLx_le hl) huS
    have hvC : v ∈ Subgroup.centralizer (Lx : Set (StatedSp n K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact commute_of_mem_spFixedFactor hK hx3 (O := {phi3 K})
        (fun hmem => phi3_ne_X_sub_one hmem.symm) (hLx_le hl) hvS
    have hS : Subgroup.closure {u, v} ≤
        Subgroup.centralizer (Lx : Set (StatedSp n K)) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact huC
      · exact hvC
    have hS3 : IsPGroup 3 (Subgroup.closure {u, v}) := by
      rw [hu, hv]
      exact isPGroup_closure_pair F hζo.pow_eq_one _ _
    have hind : ∀ α β : ZMod 3,
        α • Pi.single i (1 : ZMod 3) + β • Pi.single i₀ (1 : ZMod 3) = 0 →
          α = 0 ∧ β = 0 := by
      intro α β h
      constructor
      · have h1i : (Pi.single (M := fun _ => ZMod 3) i₀ (1 : ZMod 3)) i = 0 :=
          Pi.single_eq_of_ne hne 1
        have h1 := congrFun h i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
          Pi.single_eq_same, h1i, mul_zero, mul_one, add_zero] at h1
        exact h1
      · have hi0 : (Pi.single (M := fun _ => ZMod 3) i (1 : ZMod 3)) i₀ = 0 :=
          Pi.single_eq_of_ne (Ne.symm hne) 1
        have h1 := congrFun h i₀
        simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
          Pi.single_eq_same, hi0, mul_zero, mul_one, zero_add] at h1
        exact h1
    have hncyc : ¬ IsCyclic (Subgroup.closure {u, v}) := by
      rw [hu, hv]
      exact not_isCyclic_closure_pair F hζo hind
    exact hncyc (hcyc _ hS hS3)
  have heq : Lx = spFixedFactor (F.tor c) := by
    have hiff : ∀ i, c i ≠ 0 ↔ i = i₀ :=
      fun i => ⟨hsingle i, fun hi => by rw [hi]; exact hc₀⟩
    have hzero : F.zeroSet c = Finset.univ.erase i₀ := by
      ext i
      rw [F.mem_zeroSet, Finset.mem_erase]
      constructor
      · intro hci
        refine ⟨?_, Finset.mem_univ i⟩
        rintro rfl
        exact (hiff i).mpr rfl hci
      · rintro ⟨hii, -⟩
        by_contra hci
        exact hii ((hiff i).mp hci)
    have hdim : spFixedDim (F.tor c) = 2 * (F.s - 1) := by
      rw [F.spFixedDim_tor hζo hL c, hzero,
        Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
    have hlist : SpFixedListed (F.tor c) := by
      refine ⟨?_, ?_⟩
      · rw [hdim]
        omega
      · rintro ⟨h2, -⟩
        rw [hdim] at h2
        omega
    have h42 : ¬ (spFixedDim (F.tor c) = 4 ∧ Nat.card K = 2) := by
      rintro ⟨h4, -⟩
      rw [hdim] at h4
      omega
    have hq : CFSG.IsQuasisimple ↥(spFixedFactor (F.tor c)) :=
      CFSG.RankThree.PartOne.spFixedFactor_isQuasisimple (ℓ := 2) (f := 1) (p := 3)
        (by simpa using hK) Nat.prime_two (by norm_num) blocks hlist h42
    have hcomp : IsComponentOf (spFixedFactor (F.tor c))
        (Subgroup.centralizer ({F.tor c} : Set (StatedSp n K))) :=
      SpNonsplitComp.isComponentOf_of_normalizes
        (spFixedFactor_le_centralizer (F.tor c))
        (spFixedFactor_normalized (F.tor c)) hq
    rcases isComponentOf_eq_or_commute hLx hcomp with heq | hcomm
    · exact heq
    · exfalso
      have hcomm' : ⁅spFixedFactor (F.tor c), Lx⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hcomm
      have hle : spFixedFactor (F.tor c) ≤
          Subgroup.centralizer (Lx : Set (StatedSp n K)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
      exact not_le_centralizer_self_of_isQuasisimple hLx.2.2 (hLx_le.trans hle)
  exact ⟨i₀, fun i => ⟨hsingle i, fun hi => by rw [hi]; exact hc₀⟩, heq⟩

end Frame

end A6InsideSp

end CFSG.StandardType
