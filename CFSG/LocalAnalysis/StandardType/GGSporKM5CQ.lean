module

public import CFSG.LocalAnalysis.StandardType.GGSporKM5Comm
public import CFSG.LocalAnalysis.StandardType.GGSporKM5Sylow
import CFSG.LocalAnalysis.StandardType.GGSporKCommDataF
import CFSG.LocalAnalysis.StandardType.GGSporKCommDataSylow

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.Monster.B.Pinned CFSG.Monster.Generated CFSG.HardMathSupport.Dickson.I271
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus
open _root_.Timmesfeld.PcFive

private theorem fiveB_cw_head : ∀ (i : Fin 2) (j : Fin 6),
    (cw[i.val * 9 + (j.val + 2)]!)[0]! = 0 ∧
      (cw[i.val * 9 + (j.val + 2)]!)[1]! = 0 := by
  decide +kernel

private theorem fiveB_prodAsc_mem {H : Subgroup Gmat} {v : Array ℕ}
    (h : ∀ k : Fin 9, fiveGenG k ∈ H ∨ v[k.val]! = 0) :
    prodAsc fiveGenG v ∈ H := by
  unfold prodAsc
  apply list_prod_mem
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [List.mem_range] at hk
  rw [dif_pos hk]
  rcases h ⟨k, hk⟩ with hg | hv
  · exact pow_mem hg _
  · rw [hv, pow_zero]
    exact H.one_mem

private theorem fiveB_high_mem (hD : CommData 5 qFiveB xFiveB mFiveB) {i : Fin 9}
    (hi : 2 ≤ i.val) :
    fiveGenG i ∈ Subgroup.closure (Set.range qFiveB) := by
  rcases lt_or_eq_of_le (show i.val ≤ 8 by omega) with h8 | h8
  · have hq : qFiveB ⟨i.val - 2, by omega⟩ = fiveGenG i := by
      rw [qFiveB]
      congr 1
      apply Fin.ext
      show i.val - 2 + 2 = i.val
      omega
    rw [← hq]
    exact Subgroup.subset_closure ⟨⟨i.val - 2, by omega⟩, rfl⟩
  · have hx : fiveGenG i = xFiveB := by
      rw [xFiveB]
      congr 1
      apply Fin.ext
      exact h8
    rw [hx]
    exact hD.mem_z

private theorem fiveB_low_normalizes (hD : CommData 5 qFiveB xFiveB mFiveB)
    (hcomm : ∀ i j : Fin 9, i < j → fiveGenG i * fiveGenG j * (fiveGenG i)⁻¹ =
      prodAsc fiveGenG cw[i.val * 9 + j.val]!)
    {i : Fin 9} (hi : i.val < 2) :
    fiveGenG i ∈ Subgroup.normalizer (Subgroup.closure (Set.range qFiveB) : Set Gmat) := by
  have hb : ∀ j : Fin 6, ((fiveGenG i)⁻¹)⁻¹ * qFiveB j * (fiveGenG i)⁻¹ ∈
      Subgroup.closure (Set.range qFiveB) := by
    intro j
    have hp : j.val + 2 < 9 := by omega
    have hq : qFiveB j = fiveGenG ⟨j.val + 2, hp⟩ := by
      rw [qFiveB]
    have h := hcomm i ⟨j.val + 2, hp⟩ (by show i.val < j.val + 2; omega)
    rw [← hq] at h
    have hmem : prodAsc fiveGenG cw[i.val * 9 + (j.val + 2)]! ∈
        Subgroup.closure (Set.range qFiveB) := by
      apply fiveB_prodAsc_mem
      intro k
      by_cases hk : k.val < 2
      · right
        have hdata := fiveB_cw_head ⟨i.val, hi⟩ j
        have hk' : k.val = 0 ∨ k.val = 1 := by omega
        rcases hk' with h0 | h1
        · rw [h0]; exact hdata.1
        · rw [h1]; exact hdata.2
      · left
        exact fiveB_high_mem hD (by omega)
    rw [inv_inv, h]
    exact hmem
  have hx : (fiveGenG i)⁻¹ ∈
      Subgroup.normalizer (Subgroup.closure (Set.range qFiveB) : Set Gmat) :=
    mem_normalizer_of_conj fun g hg => CommData.conj_mem (b := (fiveGenG i)⁻¹) hb hg
  simpa using Subgroup.inv_mem _ hx

private theorem fiveB_closure_le_normalizer [Finite Gmat]
    (hD : CommData 5 qFiveB xFiveB mFiveB)
    (hcomm : ∀ i j : Fin 9, i < j →
      fiveGenG i * fiveGenG j * (fiveGenG i)⁻¹ = prodAsc fiveGenG cw[i.val * 9 + j.val]!) :
    Subgroup.closure (Set.range fiveGenG) ≤
      Subgroup.normalizer (Subgroup.closure (Set.range qFiveB) : Set Gmat) := by
  rw [Subgroup.closure_le]
  rintro x ⟨i, rfl⟩
  by_cases hi : i.val < 2
  · exact fiveB_low_normalizes hD hcomm hi
  · exact Subgroup.le_normalizer (fiveB_high_mem hD (by omega))

private def fiveB_R (i : Fin 2) : Matrix (Fin 6) (Fin 6) (ZMod 5) :=
  Matrix.of fun j k => ((cw[i.val * 9 + (j.val + 2)]!)[k.val + 2]! : ZMod 5)

private theorem fiveB_cw_lt : ∀ (i : Fin 2) (j : Fin 6) (k : Fin 9),
    (cw[i.val * 9 + (j.val + 2)]!)[k.val]! < 5 := by
  decide +kernel

private theorem fiveB_R_val (i : Fin 2) (j : Fin 6) (k : Fin 6) :
    ((fiveB_R i) j k).val = (cw[i.val * 9 + (j.val + 2)]!)[k.val + 2]! := by
  simp only [fiveB_R, Matrix.of_apply]
  exact ZMod.val_natCast_of_lt (fiveB_cw_lt i j ⟨k.val + 2, by omega⟩)

private theorem fiveB_prodAsc_split {G : Type*} [Group G] (g : Fin 9 → G) (v : Array ℕ)
    (h0 : v[0]! = 0) (h1 : v[1]! = 0) :
    prodAsc g v =
      (List.ofFn fun k : Fin 6 => g ⟨k.val + 2, by omega⟩ ^ v[k.val + 2]!).prod *
        g 8 ^ v[8]! := by
  simp only [prodAsc, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil,
    List.ofFn_succ, List.ofFn_zero, h0, h1, pow_zero, one_mul, mul_one, mul_assoc]
  simp

private theorem fiveB_actMat_inv
    (hD : CommData 5 qFiveB xFiveB mFiveB)
    (hcomm : ∀ i j : Fin 9, i < j →
      fiveGenG i * fiveGenG j * (fiveGenG i)⁻¹ = prodAsc fiveGenG cw[i.val * 9 + j.val]!)
    (i : Fin 2) :
    CommData.actMat 5 qFiveB xFiveB mFiveB (fiveGenG ⟨i.val, by omega⟩)⁻¹ = fiveB_R i := by
  refine hD.actMat_eq (R := fiveB_R i)
    (c := fun j => (cw[i.val * 9 + (j.val + 2)]!)[8]!) ?_
  intro j
  rw [inv_inv]
  simp only [qFiveB]
  have hij : (⟨i.val, by omega⟩ : Fin 9) < ⟨j.val + 2, by omega⟩ := by
    show i.val < j.val + 2
    omega
  rw [hcomm ⟨i.val, by omega⟩ ⟨j.val + 2, by omega⟩ hij]
  rw [fiveB_prodAsc_split fiveGenG (cw[i.val * 9 + (j.val + 2)]!)
    (fiveB_cw_head i j).1 (fiveB_cw_head i j).2]
  congr 1
  apply congrArg List.prod
  rw [List.ofFn_inj]
  funext k
  rw [fiveB_R_val i j k]

private theorem fiveB_ker_eq_of_card {S R : Type*} [Group S] [Finite S] [Monoid R] (ρ : S →* R)
    (K : Subgroup S) (hK : K ≤ ρ.ker) (hS : Nat.card S = 5 ^ 9) (hKc : Nat.card K = 5 ^ 7)
    (a b : S)
    (hinj : ∀ i j i' j' : Fin 5,
      ρ (a ^ (i : ℕ) * b ^ (j : ℕ)) = ρ (a ^ (i' : ℕ) * b ^ (j' : ℕ)) → i = i' ∧ j = j') :
    ρ.ker = K := by
  let F : Fin 5 × Fin 5 → S ⧸ ρ.ker :=
    fun p => (a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ) : S ⧸ ρ.ker)
  have hF : Function.Injective F := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hmem : (a ^ (i : ℕ) * b ^ (j : ℕ))⁻¹ *
        (a ^ (i' : ℕ) * b ^ (j' : ℕ)) ∈ ρ.ker := by
      rw [← QuotientGroup.eq]
      simpa [F] using h
    have hρ : ρ (a ^ (i' : ℕ) * b ^ (j' : ℕ)) =
        ρ (a ^ (i : ℕ) * b ^ (j : ℕ)) :=
      (MonoidHom.eq_iff ρ).mpr hmem
    obtain ⟨hi, hj⟩ := hinj i j i' j' hρ.symm
    exact Prod.ext hi hj
  have hcard_le : 25 ≤ Nat.card (S ⧸ ρ.ker) := by
    have h := Nat.card_le_card_of_injective F hF
    simpa [Nat.card_prod, Nat.card_fin] using h
  have hindex : (ρ.ker).index = Nat.card (S ⧸ ρ.ker) := rfl
  have hcard_le' : Nat.card ρ.ker * 25 ≤ 5 ^ 9 := by
    calc Nat.card ρ.ker * 25 ≤ Nat.card ρ.ker * (ρ.ker).index :=
          Nat.mul_le_mul_left _ (by rw [hindex]; exact hcard_le)
      _ = 5 ^ 9 := by rw [Subgroup.card_mul_index, hS]
  have hker_le : Nat.card ρ.ker ≤ 5 ^ 7 := by
    have h := hcard_le'
    rw [show (5 : ℕ) ^ 9 = 5 ^ 7 * 25 by norm_num] at h
    exact Nat.le_of_mul_le_mul_right h (by norm_num)
  exact (Subgroup.eq_of_le_of_card_ge hK (by rw [hKc]; exact hker_le)).symm

private theorem fiveB_R_inj : ∀ i j i' j' : Fin 5,
    fiveB_R 0 ^ (i : ℕ) * fiveB_R 1 ^ (j : ℕ) =
      fiveB_R 0 ^ (i' : ℕ) * fiveB_R 1 ^ (j' : ℕ) → i = i' ∧ j = j' := by
  decide +kernel

private theorem fiveB_q_le_closure :
    Subgroup.closure (Set.range qFiveB) ≤ Subgroup.closure (Set.range fiveGenG) := by
  apply Subgroup.closure_mono
  rintro x ⟨i, rfl⟩
  exact ⟨_, rfl⟩

private theorem fiveB_actMat_eq_one (hD : CommData 5 qFiveB xFiveB mFiveB) {g : Gmat}
    (hg : ∀ i : Fin 6, g⁻¹ * qFiveB i * g = qFiveB i) :
    CommData.actMat 5 qFiveB xFiveB mFiveB g = 1 := by
  ext i j
  simp only [CommData.actMat, Matrix.of_apply, hg i, hD.coord_q, Matrix.one_apply,
    Pi.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem fiveB_inf_centralizer_le [Finite Gmat] [Fact (Nat.Prime 5)]
    (hD : CommData 5 qFiveB xFiveB mFiveB)
    (hcomm : ∀ i j : Fin 9, i < j →
      fiveGenG i * fiveGenG j * (fiveGenG i)⁻¹ = prodAsc fiveGenG cw[i.val * 9 + j.val]!)
    (hS : Nat.card ↥(Subgroup.closure (Set.range fiveGenG)) = 5 ^ 9) :
    Nat.card ↥(Subgroup.closure (Set.range fiveGenG) ⊓
      Subgroup.centralizer (Subgroup.closure (Set.range qFiveB) : Set Gmat)) ≤ 5 := by
  let S : Subgroup Gmat := Subgroup.closure (Set.range fiveGenG)
  let Q : Subgroup Gmat := Subgroup.closure (Set.range qFiveB)
  change Nat.card ↥(S ⊓ Subgroup.centralizer (Q : Set Gmat)) ≤ 5
  have hQS : Q ≤ S := fiveB_q_le_closure
  have hSN : S ≤ Subgroup.normalizer (Q : Set Gmat) := fiveB_closure_le_normalizer hD hcomm
  have hL : ∀ b ∈ S, ∀ i, b⁻¹ * qFiveB i * b ∈ Q := by
    intro b hb i
    have hb' := hSN hb
    rw [Subgroup.mem_normalizer_iff''] at hb'
    exact (hb' (qFiveB i)).1 (Subgroup.subset_closure ⟨i, rfl⟩)
  let ρ : S →* Matrix (Fin 6) (Fin 6) (ZMod 5) := hD.actHom S hL
  let a : S := ⟨(fiveGenG 0)⁻¹, S.inv_mem (Subgroup.subset_closure ⟨0, rfl⟩)⟩
  let b : S := ⟨(fiveGenG 1)⁻¹, S.inv_mem (Subgroup.subset_closure ⟨1, rfl⟩)⟩
  have hρa : ρ a = fiveB_R 0 := by
    rw [CommData.actHom_apply]
    show CommData.actMat 5 qFiveB xFiveB mFiveB ((fiveGenG 0)⁻¹) = fiveB_R 0
    simpa using fiveB_actMat_inv hD hcomm 0
  have hρb : ρ b = fiveB_R 1 := by
    rw [CommData.actHom_apply]
    show CommData.actMat 5 qFiveB xFiveB mFiveB ((fiveGenG 1)⁻¹) = fiveB_R 1
    simpa using fiveB_actMat_inv hD hcomm 1
  have hρab : ∀ m n : ℕ, ρ (a ^ m * b ^ n) = fiveB_R 0 ^ m * fiveB_R 1 ^ n := by
    intro m n
    rw [map_mul, map_pow, map_pow, hρa, hρb]
  have hinj : ∀ i j i' j' : Fin 5,
      ρ (a ^ (i : ℕ) * b ^ (j : ℕ)) = ρ (a ^ (i' : ℕ) * b ^ (j' : ℕ)) →
        i = i' ∧ j = j' := by
    intro i j i' j' h
    rw [hρab (i : ℕ) (j : ℕ), hρab (i' : ℕ) (j' : ℕ)] at h
    exact fiveB_R_inj i j i' j' h
  have hK : Q.subgroupOf S ≤ ρ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, CommData.actHom_apply]
    exact hD.actMat_of_mem (Subgroup.mem_subgroupOf.1 hk)
  have hcardQ : Nat.card Q = 5 ^ 7 := by simpa using hD.card_eq
  have hKc : Nat.card ↥(Q.subgroupOf S) = 5 ^ 7 := by
    rw [← hcardQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
  have hS' : Nat.card ↥S = 5 ^ 9 := hS
  have hker : ρ.ker = Q.subgroupOf S :=
    fiveB_ker_eq_of_card ρ (Q.subgroupOf S) hK hS' hKc a b hinj
  have hTle : (S ⊓ Subgroup.centralizer (Q : Set Gmat)) ≤ Subgroup.zpowers xFiveB := by
    intro g hg
    have hgS : g ∈ S := hg.1
    have hgC : g ∈ Subgroup.centralizer (Q : Set Gmat) := hg.2
    have hconj : ∀ i : Fin 6, g⁻¹ * qFiveB i * g = qFiveB i := by
      intro i
      have hc : qFiveB i * g = g * qFiveB i :=
        Subgroup.mem_centralizer_iff.1 hgC (qFiveB i) (Subgroup.subset_closure ⟨i, rfl⟩)
      calc g⁻¹ * qFiveB i * g = g⁻¹ * (qFiveB i * g) := by group
        _ = g⁻¹ * (g * qFiveB i) := by rw [hc]
        _ = qFiveB i := by group
    have hact : CommData.actMat 5 qFiveB xFiveB mFiveB g = 1 :=
      fiveB_actMat_eq_one hD hconj
    have hmem : (⟨g, hgS⟩ : S) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, CommData.actHom_apply]
      exact hact
    rw [hker] at hmem
    have hgQ : g ∈ Q := Subgroup.mem_subgroupOf.1 hmem
    have hmem2 : g ∈ Q ⊓ Subgroup.centralizer (Q : Set Gmat) := ⟨hgQ, hgC⟩
    rwa [commData_inf_centralizer hD] at hmem2
  calc Nat.card ↥(S ⊓ Subgroup.centralizer (Q : Set Gmat))
      ≤ Nat.card ↥(Subgroup.zpowers xFiveB) := Subgroup.card_le_of_le hTle
    _ = 5 := by rw [Nat.card_zpowers, hD.orderOf_z]

theorem five_card_closure_eq :
    Nat.card ↥(Subgroup.closure (Set.range fiveGenG)) = 5 ^ (Nat.card Gmat).factorization 5 := by
  rw [five_sylow_closure.1, factorization_Gmat_five]

theorem five_closure_le_normalizer :
    Subgroup.closure (Set.range fiveGenG) ≤
      Subgroup.normalizer (Subgroup.closure (Set.range qFiveB) : Set Gmat) := by
  obtain ⟨hfin, -, -, -, hcomm, -⟩ := gmat_five_setup
  have : Finite Gmat := hfin
  exact fiveB_closure_le_normalizer fiveCommData hcomm

theorem five_card_inf_centralizer_le :
    Nat.card ↥(Subgroup.closure (Set.range fiveGenG) ⊓
      Subgroup.centralizer (Subgroup.closure (Set.range qFiveB) : Set Gmat)) ≤ 5 := by
  obtain ⟨hfin, -, -, -, hcomm, -⟩ := gmat_five_setup
  have : Finite Gmat := hfin
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact fiveB_inf_centralizer_le fiveCommData hcomm five_sylow_closure.1

theorem five_hCQ :
    ∀ P : Subgroup Gmat,
      P ≤ Subgroup.centralizer (Subgroup.closure (Set.range qFiveB) : Set Gmat) →
        IsPGroup 5 P → Nat.card ↥P ≤ 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite Gmat := gmat_five_setup.1
  intro P hPC hP
  exact commData_card_le_of_sylow five_card_closure_eq five_closure_le_normalizer
    five_card_inf_centralizer_le P hPC hP

end CFSG.StandardType.SporadicShape
