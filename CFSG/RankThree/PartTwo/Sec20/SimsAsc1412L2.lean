module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Statements
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Skel
public import Certificates.Certificate43
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Max
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L2Tools
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2Gen
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Hyp
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
import CFSG.RankThree.PartTwo.Sec3.TwoOfThreeNormal
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup CFSG.GorensteinWalter
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem normalizer_le_normalizer_fourChar_1412 (S : Subgroup X) (k : Fin 4) :
    Subgroup.normalizer (S : Set X) ≤ Subgroup.normalizer (Sec18.fourChar S k : Set X) := by
  have h0 : Subgroup.normalizer (S : Set X) ≤ Subgroup.normalizer (Sec18.fourChar S 0 : Set X) := by
    rw [Sec18.Item181ThreeProof.fourChar_zero]
    exact Sec18.Item181ThreeProof.normalizer_le_normalizer_omegaG S
  have h1 : Subgroup.normalizer (S : Set X) ≤ Subgroup.normalizer (Sec18.fourChar S 1 : Set X) := by
    rw [Sec18.Item181ThreeProof.fourChar_one]
    exact Sec18.Item181ThreeProof.normalizer_le_normalizer_jG S 0
  have h2 : Subgroup.normalizer (S : Set X) ≤ Subgroup.normalizer (Sec18.fourChar S 2 : Set X) := by
    rw [Sec18.Item181ThreeProof.fourChar_two]
    exact (Sec18.Item181ThreeProof.normalizer_le_normalizer_jG S 1).trans
      (Sec18.Item181ThreeProof.normalizer_le_normalizer_omegaG (Sec3.jG S 1))
  have h3 : Subgroup.normalizer (S : Set X) ≤ Subgroup.normalizer (Sec18.fourChar S 3 : Set X) := by
    rw [Sec18.Item181ThreeProof.fourChar_three]
    exact (Sec18.Item181ThreeProof.normalizer_le_normalizer_jG S 2).trans
      (Sec18.Item181ThreeProof.normalizer_le_normalizer_omegaG (Sec3.jG S 2))
  fin_cases k
  exacts [h0, h1, h2, h3]

theorem forall_conj_mem_zpowers_of_sup_ne_top (h : Hyp1411 X L S)
    (hKQ : CFSG.pPrimeCore 3 X = CFSG.pCore 2 X) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hq : 9 < p ^ f)
    (e : ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p f))
    {x : X} (hxL : x ∈ L) (hx : orderOf x = 3) {i : Fin 4}
    (hi : Subgroup.normalizer (Subgroup.zpowers x : Set X) ⊔
      Subgroup.normalizer (Sec18.fourChar S i : Set X) ≠ ⊤) :
    ∀ s ∈ S, QuotientGroup.mk' (CFSG.pPrimeCore 3 X) s * QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x *
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) s)⁻¹ ∈
      Subgroup.zpowers (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) x) := by
  classical
  set K := CFSG.pPrimeCore 3 X with hKdef
  set π := QuotientGroup.mk' K with hπ
  set H := Subgroup.normalizer (Subgroup.zpowers x : Set X) ⊔
    Subgroup.normalizer (Sec18.fourChar S i : Set X) with hHdef
  set F := GaloisField p f with hFdef
  have : Fintype F := Fintype.ofFinite F
  have hf0 : f ≠ 0 := by
    rintro rfl
    norm_num at hq
  have hF : Nat.card F = p ^ f := GaloisField.card p f hf0
  have hLn : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective K)
  have hSH : S ≤ H :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_fourChar_1412 S i)).trans le_sup_right
  have hKH : K ≤ H := by rw [hKQ]; exact h.2.2.2.2.2.1.trans hSH
  set ε := e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL F) with hεdef
  set xs : ↥(L.map π) := ⟨π x, Subgroup.mem_map_of_mem π hxL⟩ with hxsdef
  have hx3 : orderOf (π x) = 3 := orderOf_mk_eq_three_of_pPrimeCore_eq hKQ hx
  have hxs3 : orderOf xs = 3 := by rw [Subgroup.orderOf_mk]; exact hx3
  have hxh3 : orderOf (ε xs) = 3 := by rw [MulEquiv.orderOf_eq]; exact hxs3
  set H' : Subgroup (PSL(2, F)) := ((H.map π).subgroupOf (L.map π)).map ε.toMonoidHom with hH'def
  have hmemH' : ∀ n : ↥(L.map π), ε n ∈ H' ↔ (n : X ⧸ K) ∈ H.map π := by
    intro n
    constructor
    · rintro ⟨m, hm, hmn⟩
      have : m = n := ε.injective hmn
      rw [← this]
      exact hm
    · intro hn
      exact ⟨n, hn, rfl⟩
  have hzp : ∀ n : ↥(L.map π), ε n ∈ Subgroup.zpowers (ε xs) ↔ n ∈ Subgroup.zpowers xs := by
    intro n
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ε.injective ?_⟩
      rw [map_zpow]
      exact hk
    · rintro ⟨k, rfl⟩
      exact ⟨k, by rw [map_zpow]⟩
  have hNH' : Subgroup.normalizer (Subgroup.zpowers (ε xs) : Set (PSL(2, F))) ≤ H' := by
    intro d hd
    obtain ⟨n, rfl⟩ := ε.surjective d
    rw [hmemH']
    obtain ⟨y, hyL, hy⟩ := n.2
    rw [← hy]
    refine Subgroup.map_mono le_sup_left (mem_map_normalizer_of_mem_normalizer hKQ hx ?_)
    rw [hy]
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have h1 : ε n * ε xs * (ε n)⁻¹ ∈ Subgroup.zpowers (ε xs) :=
      (Subgroup.mem_normalizer_iff.mp hd (ε xs)).mp (Subgroup.mem_zpowers _)
    rw [← map_inv, ← map_mul, ← map_mul, hzp] at h1
    obtain ⟨j, hj⟩ := h1
    have h2 : (n : X ⧸ K) * π x * (n : X ⧸ K)⁻¹ = π x ^ j := by
      have := congrArg (fun m : ↥(L.map π) => (m : X ⧸ K)) hj
      simpa [hxsdef] using this.symm
    refine ⟨j * k, ?_⟩
    show (π x) ^ (j * k) = (n : X ⧸ K) * (π x) ^ k * (n : X ⧸ K)⁻¹
    rw [zpow_mul, ← h2, conj_zpow]
  rcases (isCoatom_normalizer_zpowers_of_orderOf_eq_three hF hp2 hp3 hq hxh3).le_iff.mp hNH' with
    hTop | hEq
  ·
    exfalso
    apply hi
    have hLH : L.map π ≤ H.map π := fun n hn => (hmemH' ⟨n, hn⟩).mp (hTop ▸ Subgroup.mem_top _)
    have hSHm : S.map π ≤ H.map π := Subgroup.map_mono hSH
    have htop : H.map π = ⊤ := by
      rw [eq_top_iff, ← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective K),
        ← h.2.2.2.2.2.2.1, Subgroup.map_sup]
      exact sup_le hSHm hLH
    have := Subgroup.comap_map_eq π H
    rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.mpr hKH] at this
    exact this.symm
  ·
    intro s hs
    have hsH : π s ∈ H.map π := Subgroup.mem_map_of_mem π (hSH hs)
    have hxH : π x ∈ H.map π := by
      have : ε xs ∈ H' := by rw [hEq]; exact Subgroup.le_normalizer (Subgroup.mem_zpowers _)
      exact (hmemH' xs).mp this
    set ys : ↥(L.map π) := ⟨π s * π x * (π s)⁻¹, hLn.conj_mem _ (Subgroup.mem_map_of_mem π hxL) _⟩
      with hysdef
    have hysH : ε ys ∈ H' :=
      (hmemH' ys).mpr ((H.map π).mul_mem ((H.map π).mul_mem hsH hxH) ((H.map π).inv_mem hsH))
    rw [hEq] at hysH
    have hys3 : orderOf (ε ys) = 3 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      rw [show π s * π x * (π s)⁻¹ = MulAut.conj (π s) (π x) from rfl, MulEquiv.orderOf_eq]
      exact hx3
    have hmem := mem_zpowers_of_mem_normalizer_of_orderOf_eq_three hF hp2 hp3 (by omega) hxh3
      hysH hys3
    rw [hzp] at hmem
    obtain ⟨j, hj⟩ := hmem
    refine ⟨j, ?_⟩
    have := congrArg (fun m : ↥(L.map π) => (m : X ⧸ K)) hj
    simpa [hysdef, hxsdef] using this

theorem asc82Item1412L2_of_noSmall
    (hNS : ∀ (X : Type) [Group X] [Finite X] (L S : Subgroup X), Hyp1411 X L S →
      ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ 3 → 9 < p ^ f →
        Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
          CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p f)) → NoSmall1411 X L S) :
    Asc82Item1412L2 := by
  intro X _ _ L S x h hKQ hL hxL hx hxS _
  obtain ⟨p, f, hpF, hp2, hp3, hq, ⟨e⟩⟩ := hL
  set K := CFSG.pPrimeCore 3 X with hKdef
  set π := QuotientGroup.mk' K with hπ
  by_cases hall : ∀ s ∈ S, π s * π x * (π s)⁻¹ ∈ Subgroup.zpowers (π x)
  ·
    have hS2 : IsPGroup 2 S := h.2.2.2.2.1
    have hx3 : orderOf (π x) = 3 := orderOf_mk_eq_three_of_pPrimeCore_eq hKQ hx
    have hcomm : ∀ s ∈ S, π s * π x = π x * π s := fun s hs =>
      commute_mk_of_conj_mem_zpowers hS2 hx3 hxS hs (hall s hs)
    have hf0 : f ≠ 0 := by
      rintro rfl
      norm_num at hq
    have hp : p.Prime := hpF.out
    have hchar : ringChar (GaloisField p f) = p := ringChar.eq (GaloisField p f) p
    obtain ⟨-, hZ⟩ := isSimpleGroup_and_center_eq_bot_of_L2 hp2 hq e
    set ε := e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField p f)) with hεdef
    have hF2 : ringChar (GaloisField p f) ≠ 2 := by rw [hchar]; exact hp2
    have hF3 : ringChar (GaloisField p f) ≠ 3 := by rw [hchar]; exact hp3
    have hrel := fun (A : Subgroup X) (hAS : A ≤ S) (hA : Sec3.IsElemTwo A) =>
      relIndex_le_four_of_commute h hKQ hF2 hF3 ε hZ hxL hx3 hcomm hAS hA
    have hCQ := centralizer_pCore_le_of_hyp1411 h
    have hLn : L.Normal := h.2.1
    have hQS : CFSG.pCore 2 X ≤ S := h.2.2.2.2.2.1
    have hSL : S ⊔ L = ⊤ := h.2.2.2.2.2.2.1
    obtain ⟨i₁, i₂, h12, hn1, hn2⟩ := two_fourChar_normal_of_relIndex_le_four hCQ hS2 hQS hLn hSL
      (fun A hAS hA => (hrel A hAS hA).1)
      (fun A hAS hA h4 => by
        obtain ⟨⟨t, htA, htQ, htL⟩, σ, hσ1, hσ2⟩ := (hrel A hAS hA).2 h4
        exact ⟨t, htA, htQ, noSmallEight1412_of_inner h hKQ hp2 hp3 hq e hσ1 hσ2 (hA.2 t htA)
          htQ htL⟩)
      (hNS X L S h p f hp2 hp3 hq ⟨e⟩)
    refine ⟨i₁, i₂, h12, ?_, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr hn1]
      exact sup_top_eq _
    · rw [Subgroup.normalizer_eq_top_iff.mpr hn2]
      exact sup_top_eq _
  ·
    have key : ∀ i : Fin 4, Subgroup.normalizer (Subgroup.zpowers x : Set X) ⊔
        Subgroup.normalizer (Sec18.fourChar S i : Set X) = ⊤ := by
      intro i
      by_contra hi
      exact hall (forall_conj_mem_zpowers_of_sup_ne_top h hKQ hp2 hp3 hq e hxL hx hi)
    exact ⟨0, 1, by decide, key 0, key 1⟩

theorem asc82Item1412L2_holds : Asc82Item1412L2 :=
  asc82Item1412L2_of_noSmall fun _ _ _ _ _ h _ _ _ hp2 hp3 hq hL =>
    noSmall1411_L2_odd h hp2 hp3 hq hL

end CFSG.RankThree.PartTwo.Sec20
