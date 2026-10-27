module

public import CFSG.LocalAnalysis.StandardType.GGK1CCoDefs
public import CFSG.LocalAnalysis.StandardType.GGK1CCoBlocks
public import CFSG.LocalAnalysis.StandardType.GGK1CCoLabel
public import CFSG.LocalAnalysis.StandardType.GGK1CCoComp
public import CFSG.LocalAnalysis.StandardType.GGK1CSigmaIn
public import CFSG.LocalAnalysis.StandardType.GGK1SigmaAbs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

private theorem ggK1C_map_centralizer {r : ℕ} {K : Type} [Field K]
    (hb : Function.Bijective (proj r K)) (x : ↥(StatedSp r K)) :
    (Subgroup.centralizer ({x} : Set ↥(StatedSp r K))).map (proj r K) =
      Subgroup.centralizer ({proj r K x} : Set (StatedProj (StatedSp r K))) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := Subgroup.mem_centralizer_singleton_iff.mp hz
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, hz']
  · intro hy
    obtain ⟨z, rfl⟩ := hb.2 y
    refine ⟨z, ?_, rfl⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    apply hb.1
    rw [map_mul, map_mul]
    exact hy'

private theorem ggK1C_comm_iSup {G : Type} [Group G] {ι : Type} (A : ι → Subgroup G) (i : ι)
    (hcomm : ∀ j k : ι, j ≠ k → ∀ a ∈ A j, ∀ b ∈ A k, Commute a b) :
    (⨆ (j : ι) (_ : j ≠ i), A j) ≤ Subgroup.centralizer (A i : Set G) := by
  refine iSup₂_le fun j hj b hb => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact hcomm i j (Ne.symm hj) h hh b hb

theorem ggK1C_core_sigma {p nf d r : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (hK : Nat.card K = 2 ^ nf) (hr : 1 ≤ r)
    {x : ↥(StatedSp r K)} {m : List ℕ} (hm : GGK1CMultOf p nf d r K x m)
    (hx : x ^ p = 1) :
    GGKacSigmaClause p
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r)) (LargeEvenGSpSet K r))
      (ggMultDatumC p nf d m) (StatedProj (StatedSp r K))
      (MonoidHom.id (StatedProj (StatedSp r K))) (MulAut.conj (proj r K x)) := by
  intro o ho hqs A hxA hA hAI
  have hnf : 1 ≤ nf := by
    rcases Nat.eq_zero_or_pos nf with h0 | hpos
    · subst h0
      rw [pow_zero] at hK
      have h2 := Finite.one_lt_card (α := K)
      omega
    · exact hpos
  obtain ⟨B⟩ := ggK1CCo_blocks_exists hnf hp hp2 hdvd hK hm hx
  obtain ⟨F⟩ := ggK1CCo_family_of_blocks B hK
  obtain ⟨i, hi, t₀, ht₀, ht₀p, a₀, ha₀, hnc⟩ := F.hsolv o ho hqs
  obtain ⟨hZ, hIinn⟩ := ggK1C_centreless_inner hnf hr hK
  haveI : NeZero r := ⟨by omega⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardK : Fintype.card K = 2 ^ nf := by rw [Fintype.card_eq_nat_card, hK]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := nf) hcardK
  have hb : Function.Bijective (proj r K) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
  have hcent := ggK1C_comm_iSup F.A i F.hcomm
  have hSC : ∀ a ∈ (F.A i).map (proj r K), ∀ b ∈ (⨆ (j : F.ι) (_ : j ≠ i), F.A j).map (proj r K),
      a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hbm, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hcent hbm) a ha
    rw [← map_mul, ← map_mul, this]
  have hdisj : Disjoint ((F.A i).map (proj r K))
      ((⨆ (j : F.ι) (_ : j ≠ i), F.A j).map (proj r K)) := by
    rw [disjoint_iff, ← Subgroup.map_inf _ _ (proj r K) hb.1, (disjoint_iff.mp (F.hindep i)),
      Subgroup.map_bot]
  have hsup : (F.A i).map (proj r K) ⊔ (⨆ (j : F.ι) (_ : j ≠ i), F.A j).map (proj r K) =
      Subgroup.centralizer ({proj r K x} : Set (StatedProj (StatedSp r K))) := by
    rw [← Subgroup.map_sup, ← iSup_split_single F.A i, F.hjoin, ggK1C_map_centralizer hb]
  have hcomp : ∀ J : Subgroup (StatedProj (StatedSp r K)),
      CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj (proj r K x))) →
        ∀ j ∈ J, ∀ a ∈ (F.A i).map (proj r K), a * j = j * a := by
    intro J hJ j hj a ha
    obtain ⟨k, hq, rfl⟩ := ggK1CCo_component_eq F hJ
    have hki : k ≠ i := by
      rintro rfl
      have := F.hqs k hq
      rw [hi] at this
      rw [hqs] at this
      exact absurd this (by decide)
    obtain ⟨j', hj', rfl⟩ := hj
    obtain ⟨a', ha', rfl⟩ := ha
    have hj'k : j' ∈ F.A k := by
      refine Subgroup.commutator_le.mpr (fun g₁ h₁ g₂ h₂ => ?_) hj'
      exact (F.A k).mul_mem ((F.A k).mul_mem ((F.A k).mul_mem h₁ h₂) ((F.A k).inv_mem h₁))
        ((F.A k).inv_mem h₂)
    have := F.hcomm i k (Ne.symm hki) a' ha' j' hj'k
    rw [← map_mul, ← map_mul, this]
  have hAI' : ∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r))
      (LargeEvenGSpSet K r), ∀ l, φ l = a l := by
    intro a ha
    obtain ⟨φ, hφ, h⟩ := hAI a ha
    exact ⟨φ, hφ, fun l => by simpa using h l⟩
  refine ggK1_sigma_abstract hZ _ hIinn (proj r K x) _ _ hSC hdisj hsup hcomp
    (t₀ := proj r K t₀) (a₀ := proj r K a₀) (Subgroup.mem_map_of_mem _ ht₀)
    (Subgroup.mem_map_of_mem _ ha₀) (by rw [← map_pow, ht₀p, map_one]) ?_ A hxA hA hAI'
  intro h
  apply hnc
  apply hb.1
  rw [map_mul, map_mul]
  exact h

end CFSG.StandardType

end
