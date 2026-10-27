module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGNSJoinRankOneOfRk1
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
open scoped MatrixGroups

section RankTwo

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def ggRankTwo (Bs : Subgroup G) (r r' : MulAut ↥Bs) : Subgroup G :=
  ggOTwoPrime (Subgroup.centralizer
    ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G))

@[expose] noncomputable def ggRankTwoIn (X Bs : Subgroup G) (r r' : MulAut ↥Bs) : Subgroup G :=
  ggOTwoPrime (X ⊓ Subgroup.centralizer
    ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G))

theorem ggRankTwo_comm (Bs : Subgroup G) (r r' : MulAut ↥Bs) :
    ggRankTwo Bs r r' = ggRankTwo Bs r' r := by
  rw [ggRankTwo, ggRankTwo, inf_comm]

theorem ggRankTwo_map_conj {Bs : Subgroup G} {g : G} {a : MulAut ↥Bs}
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) (r r' : MulAut ↥Bs) :
    (ggRankTwo Bs r r').map (MulAut.conj g).toMonoidHom =
      ggRankTwo Bs (a * r * a⁻¹) (a * r' * a⁻¹) := by
  rw [ggRankTwo, ggRankTwo, ggOTwoPrime_map_conj, ggMap_conj_centralizer,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ggHyperplane_map_conj ha r,
    ggHyperplane_map_conj ha r']

theorem ggRankTwoIn_map_conj {X Bs : Subgroup G} {g : G} {a : MulAut ↥Bs}
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) (r r' : MulAut ↥Bs) :
    (ggRankTwoIn X Bs r r').map (MulAut.conj g).toMonoidHom =
      ggRankTwoIn (X.map (MulAut.conj g).toMonoidHom) Bs (a * r * a⁻¹) (a * r' * a⁻¹) := by
  rw [ggRankTwoIn, ggRankTwoIn, ggOTwoPrime_map_conj,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ggMap_conj_centralizer,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ggHyperplane_map_conj ha r,
    ggHyperplane_map_conj ha r']

@[expose] noncomputable def qtwoNode (Bs : Subgroup G) {m : ℕ} (r : Fin m → MulAut ↥Bs)
    (i : Fin m) : Subgroup G :=
  ggRankOne Bs (r i)

@[expose] noncomputable def qtwoW (Bs : Subgroup G) {m : ℕ} (r : Fin m → MulAut ↥Bs)
    (i j : Fin m) : Subgroup G :=
  if ggCoxeterMatrixD m i j = 3 then ggRankTwo Bs (r i) (r j)
  else qtwoNode Bs r i ⊔ qtwoNode Bs r j

theorem qtwoW_of_edge {Bs : Subgroup G} {m : ℕ} (r : Fin m → MulAut ↥Bs) {i j : Fin m}
    (h : ggCoxeterMatrixD m i j = 3) : qtwoW Bs r i j = ggRankTwo Bs (r i) (r j) := by
  rw [qtwoW, if_pos h]

theorem qtwoW_of_nonedge {Bs : Subgroup G} {m : ℕ} (r : Fin m → MulAut ↥Bs) {i j : Fin m}
    (h : ggCoxeterMatrixD m i j = 2) : qtwoW Bs r i j = qtwoNode Bs r i ⊔ qtwoNode Bs r j := by
  rw [qtwoW, if_neg (by omega)]

theorem qtwoW_symm (Bs : Subgroup G) {m : ℕ} (r : Fin m → MulAut ↥Bs) (i j : Fin m) :
    qtwoW Bs r i j = qtwoW Bs r j i := by
  rw [qtwoW, qtwoW, (ggCoxeterMatrixD m).symmetric i j]
  split_ifs
  · exact ggRankTwo_comm _ _ _
  · exact sup_comm _ _

end RankTwo

section System

variable {G : Type} [Group G]

theorem natCard_galoisField_two_two : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem qtwoSystem_of_local {m : ℕ} {H : Subgroup G} {U : Fin m → Subgroup G}
    {W : Fin m → Fin m → Subgroup G}
    (hiso : ∀ i, Nonempty (Su (GaloisField 2 2) 2 1 2 ≃* U i))
    (hsymm : ∀ i j, W i j = W j i)
    (hjoin : ∀ i j, ggCoxeterMatrixD m i j = 2 → W i j = U i ⊔ U j)
    (hcomm : ∀ i j, ggCoxeterMatrixD m i j = 2 → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j, ggCoxeterMatrixD m i j = 3 →
      UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (W i j) (U i) (U j))
    (hgen : (⨆ (i : Fin m) (j : Fin m) (_ : i < j), W i j) = H)
    (hA3 : ∀ i j k, ggCoxeterMatrixD m i j = 3 → ggCoxeterMatrixD m j k = 3 →
      ggCoxeterMatrixD m i k = 2 →
      ∃ θ : Su (GaloisField 2 2) 2 1 4 →* G, θ.range = W i j ⊔ W j k)
    (hfar1 : ∀ i j k, ggCoxeterMatrixD m j k = 3 → ggCoxeterMatrixD m i j = 2 →
      ggCoxeterMatrixD m i k = 2 → ∀ x ∈ U i, ∀ y ∈ W j k, x * y = y * x)
    (hfar2 : ∀ i k j l, ggCoxeterMatrixD m i k = 3 → ggCoxeterMatrixD m j l = 3 →
      ggCoxeterMatrixD m i j = 2 → ggCoxeterMatrixD m i l = 2 → ggCoxeterMatrixD m k j = 2 →
      ggCoxeterMatrixD m k l = 2 → ∀ x ∈ W i k, ∀ y ∈ W j l, x * y = y * x) :
    QTwoWeakPhanSystemD (GaloisField 2 2) m H U W := by
  refine
    { card_four := natCard_galoisField_two_two
      hlab := fun i j h => ggCoxeterMatrixD_two_or_three i j h
      iso := hiso
      symm := hsymm
      join := hjoin
      comm := hcomm
      pair := hpair
      gen := ?_
      adjA3 := hA3
      farNodeEdge := hfar1
      farEdgeEdge := hfar2 }
  rw [← hgen]
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    rcases lt_or_gt_of_ne hij with h | h
    · exact le_iSup_of_le i (le_iSup_of_le j (le_iSup (fun _ : i < j => W i j) h))
    · rw [hsymm i j]
      exact le_iSup_of_le j (le_iSup_of_le i (le_iSup (fun _ : j < i => W j i) h))
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    exact le_iSup_of_le i (le_iSup_of_le j (le_iSup (fun _ : i ≠ j => W i j) hij.ne))

theorem qtwoSystem_of_nodes [Finite G] {m : ℕ} (Bs : Subgroup G) (r : Fin m → MulAut ↥Bs)
    {H : Subgroup G}
    (hiso : ∀ i, Nonempty (Su (GaloisField 2 2) 2 1 2 ≃* qtwoNode Bs r i))
    (hcomm : ∀ i j, ggCoxeterMatrixD m i j = 2 →
      ∀ x ∈ qtwoNode Bs r i, ∀ y ∈ qtwoNode Bs r j, x * y = y * x)
    (hpair : ∀ i j, ggCoxeterMatrixD m i j = 3 →
      UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (qtwoW Bs r i j) (qtwoNode Bs r i)
        (qtwoNode Bs r j))
    (hgen : (⨆ (i : Fin m) (j : Fin m) (_ : i < j), qtwoW Bs r i j) = H)
    (hA3 : ∀ i j k, ggCoxeterMatrixD m i j = 3 → ggCoxeterMatrixD m j k = 3 →
      ggCoxeterMatrixD m i k = 2 → ∃ θ : Su (GaloisField 2 2) 2 1 4 →* G,
        θ.range = qtwoW Bs r i j ⊔ qtwoW Bs r j k)
    (hfar1 : ∀ i j k, ggCoxeterMatrixD m j k = 3 → ggCoxeterMatrixD m i j = 2 →
      ggCoxeterMatrixD m i k = 2 →
      ∀ x ∈ qtwoNode Bs r i, ∀ y ∈ qtwoW Bs r j k, x * y = y * x)
    (hfar2 : ∀ i k j l, ggCoxeterMatrixD m i k = 3 → ggCoxeterMatrixD m j l = 3 →
      ggCoxeterMatrixD m i j = 2 → ggCoxeterMatrixD m i l = 2 → ggCoxeterMatrixD m k j = 2 →
      ggCoxeterMatrixD m k l = 2 →
      ∀ x ∈ qtwoW Bs r i k, ∀ y ∈ qtwoW Bs r j l, x * y = y * x) :
    QTwoWeakPhanSystemD (GaloisField 2 2) m H (qtwoNode Bs r) (qtwoW Bs r) :=
  qtwoSystem_of_local hiso (qtwoW_symm Bs r) (fun _ _ h => qtwoW_of_nonedge r h) hcomm hpair
    hgen hA3 hfar1 hfar2

end System

section RankOne

theorem qtwo_rankOne_six_of_rk1 (hRk1 : GGSecFiveRk1PhanInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs)
    (hrC : r ∈ ggCoxRefl M e) (h6 : Nat.card ↥(ggRankOneIn L Bs r) = 6) :
    p = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : SL(2, F) →* G),
      Nat.card F = 2 ∧ Function.Injective θ ∧ θ.range = ggRankOneIn L Bs r := by
  have hr : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  obtain ⟨F, hF, hfin, θ, hchar, hθinj, hθrange, -, hnsplit, -⟩ :=
    ggRankOneIn_sl2_of_rk1 hRk1 hcfg hns hpres h3 (Or.inl rfl) hrA hr
  haveI := hchar
  have hcard : Nat.card F * (Nat.card F ^ 2 - 1) = 6 := by
    rw [← h6, ← hθrange, ← ggSL2_card F]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv
  have hq : Nat.card F = 2 := by
    haveI := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hn] at hcard ⊢
    rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
    · have hn1 : (n : ℕ) = 1 := by have := n.pos; omega
      rw [hn1]
      norm_num
    · exfalso
      have h4 : 4 ≤ 2 ^ (n : ℕ) :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h
      have h15 : 15 ≤ (2 ^ (n : ℕ)) ^ 2 - 1 := by
        have : 16 ≤ (2 ^ (n : ℕ)) ^ 2 := by simpa using Nat.pow_le_pow_left h4 2
        omega
      have h60 : 60 ≤ 2 ^ (n : ℕ) * ((2 ^ (n : ℕ)) ^ 2 - 1) :=
        calc (60 : ℕ) = 4 * 15 := by norm_num
          _ ≤ 2 ^ (n : ℕ) * ((2 ^ (n : ℕ)) ^ 2 - 1) := Nat.mul_le_mul h4 h15
      omega
  have hp3 : p ∣ 3 := by
    have h := hnsplit hns
    rw [hq] at h
    simpa using h
  exact ⟨(Nat.prime_dvd_prime_iff_eq (ggRouteCfg_prime hcfg).1 Nat.prime_three).mp hp3,
    F, hF, hfin, θ, hq, hθinj, hθrange⟩

end RankOne

end CFSG.StandardType.QTwo

end
