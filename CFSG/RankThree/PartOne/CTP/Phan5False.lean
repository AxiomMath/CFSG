module

public import CFSG.RankThree.PartOne.CTP.Phan5Cent
public import CFSG.RankThree.PartOne.CTP.Phan5Group
public import CFSG.RankThree.PartOne.S12.AmbientTransport

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem phan5_centralizer_ambient
    {N B : Subgroup G} {f : ℕ} {M : Fin 4 → Subgroup G}
    (hf : 2 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) (h25 : 25 ∣ 2 ^ f + 1) (hB : IsElementaryAbelian 5 B)
    (hBN : B ≤ N) (hMN : ∀ i, M i ≤ N) (hgen : (⨆ i, M i) = N)
    (hmod : ∀ i, StatedClassicalModel ↥(M i) .PSL 2 2 f)
    (hcomm : ∀ i j, i ≠ j → ¬ chainAdj i j →
      M i ≤ Subgroup.centralizer (M j : Set G) ∧ M i ⊓ M j = ⊥)
    (hadj : ∀ i j, chainAdj i j → CentrallyUThree f ↥(M i ⊔ M j))
    (htor : CTTorusCondition 5 B M) :
    IsCyclic ↥(Subgroup.centralizer ((M 0 ⊔ M 1 ⊔ M 3 : Subgroup G) : Set G) ⊓ N) ∧
      ∃ y ∈ Subgroup.centralizer ((M 0 ⊔ M 1 ⊔ M 3 : Subgroup G) : Set G) ⊓ N, orderOf y = 5 := by
  have hgen' := iSup_subgroupOf_eq_top hMN hgen
  obtain ⟨hcyc, y, hy, hy5⟩ := phan5_centralizer (N := ↥N) (f := f)
    (M := fun i => (M i).subgroupOf N) (B := B.subgroupOf N) hf h5 h25
    (isElementaryAbelian_of_equiv (Subgroup.subgroupOfEquivOfLe hBN).symm hB) hgen'
    (fun i => statedClassicalModel_subgroupOf (hMN i) (hmod i))
    (fun i j hij hnadj => commuting_subgroupOf (hcomm i j hij hnadj))
    (fun i j hadjij => by
      obtain ⟨e⟩ := nonempty_sup_subgroupOf_equiv (hMN i) (hMN j)
      exact centrallyUThree_of_equiv e.symm (hadj i j hadjij))
    (ctTorusCondition_subgroupOf hBN hMN htor)
  have hT : (M 0).subgroupOf N ⊔ (M 1).subgroupOf N ⊔ (M 3).subgroupOf N =
      (M 0 ⊔ M 1 ⊔ M 3).subgroupOf N := by
    rw [Subgroup.subgroupOf_sup (sup_le (hMN 0) (hMN 1)) (hMN 3),
      Subgroup.subgroupOf_sup (hMN 0) (hMN 1)]
  have hTN : M 0 ⊔ M 1 ⊔ M 3 ≤ N := sup_le (sup_le (hMN 0) (hMN 1)) (hMN 3)
  have hY : Subgroup.centralizer (((M 0).subgroupOf N ⊔ (M 1).subgroupOf N ⊔
      (M 3).subgroupOf N : Subgroup N) : Set N) =
      (Subgroup.centralizer ((M 0 ⊔ M 1 ⊔ M 3 : Subgroup G) : Set G) ⊓ N).subgroupOf N := by
    rw [hT, centralizer_subgroupOf_eq hTN, Subgroup.inf_subgroupOf_right]
  rw [hY] at hcyc hy
  refine ⟨?_, (y : G), Subgroup.mem_subgroupOf.mp hy, ?_⟩
  · exact (Subgroup.subgroupOfEquivOfLe inf_le_right).isCyclic.mp hcyc
  · rw [Subgroup.orderOf_coe]
    exact hy5

theorem phan5_false
    {N E B : Subgroup G} {c : G} {f : ℕ} {M : Fin 4 → Subgroup G}
    (hf : 2 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) (h25 : 25 ∣ 2 ^ f + 1)
    (hMN : ∀ i, M i ≤ N) (hgen : (⨆ i, M i) = N) (hBN : B ≤ N)
    (hmod : ∀ i, StatedClassicalModel ↥(M i) .PSL 2 2 f)
    (hcomm : ∀ i j, i ≠ j → ¬ chainAdj i j →
      M i ≤ Subgroup.centralizer (M j : Set G) ∧ M i ⊓ M j = ⊥)
    (hadj : ∀ i j, chainAdj i j → CentrallyUThree f ↥(M i ⊔ M j))
    (hB : IsElementaryAbelian 5 B) (hBcard : Nat.card B = 5 ^ 3) (htor : CTTorusCondition 5 B M)
    (hE : IsElementaryAbelian 5 E) (hBE : B ≤ E) (hEcard : Nat.card E = 5 * Nat.card B)
    (hEgen : E = Subgroup.zpowers c ⊔ B)
    (hcN : ∀ i, c ∈ Subgroup.normalizer (M i : Set G))
    (hcout : c ∉ M 0 ⊔ Subgroup.centralizer (M 0 : Set G))
    (hmax : ∀ z : G, orderOf z = 5 → (∀ e ∈ E, e * z = z * e) → z ∈ E) : False := by
  obtain ⟨hcyc, y, hyY, hy5⟩ := phan5_centralizer_ambient hf h5 h25 hB hBN hMN hgen hmod hcomm
    hadj htor
  have hcE : c ∈ E := by
    rw [hEgen]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hnormM : ∀ i, E ≤ Subgroup.normalizer (M i : Set G) := by
    intro i
    rw [hEgen]
    exact sup_le ((Subgroup.zpowers_le).mpr (hcN i)) (le_normalizer_of_dec (htor.1 i).1)
  have hMi : ∀ e ∈ E, ∀ i, ∀ x ∈ M i, e * x * e⁻¹ ∈ M i := fun e he i x hx =>
    (Subgroup.mem_normalizer_iff.mp (hnormM i he) x).mp hx
  have hnormN : ∀ e ∈ E, ∀ x ∈ N, e * x * e⁻¹ ∈ N := by
    intro e he x hx
    rw [← hgen] at hx ⊢
    refine Subgroup.iSup_induction (fun i => M i) hx
      (C := fun x => e * x * e⁻¹ ∈ ⨆ i, M i) (fun i x hx => ?_) (by simp) (fun x y hx hy => ?_)
    · exact Subgroup.mem_iSup_of_mem i (hMi e he i x hx)
    · have : e * (x * y) * e⁻¹ = (e * x * e⁻¹) * (e * y * e⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
  have hnormT : ∀ e ∈ E, ∀ x ∈ M 0 ⊔ M 1 ⊔ M 3, e * x * e⁻¹ ∈ M 0 ⊔ M 1 ⊔ M 3 := by
    intro e he x hx
    have hle : M 0 ⊔ M 1 ⊔ M 3 ≤ (M 0 ⊔ M 1 ⊔ M 3).comap (MulAut.conj e).toMonoidHom := by
      refine sup_le (sup_le (fun x hx => ?_) (fun x hx => ?_)) (fun x hx => ?_)
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hMi e he 0 x hx))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hMi e he 1 x hx))
      · exact Subgroup.mem_sup_right (hMi e he 3 x hx)
    exact hle hx
  have hnormY : ∀ e ∈ E, ∀ x ∈ Subgroup.centralizer ((M 0 ⊔ M 1 ⊔ M 3 : Subgroup G) : Set G) ⊓ N,
      e * x * e⁻¹ ∈ Subgroup.centralizer ((M 0 ⊔ M 1 ⊔ M 3 : Subgroup G) : Set G) ⊓ N := by
    intro e he x hx
    refine ⟨Subgroup.mem_centralizer_iff.mpr (fun t ht => ?_), hnormN e he x hx.2⟩
    have ht' : e⁻¹ * t * e ∈ M 0 ⊔ M 1 ⊔ M 3 := by
      have := hnormT e⁻¹ (Subgroup.inv_mem _ he) t ht
      simpa using this
    have h := Subgroup.mem_centralizer_iff.mp hx.1 _ ht'
    calc t * (e * x * e⁻¹) = e * ((e⁻¹ * t * e) * x) * e⁻¹ := by group
      _ = e * (x * (e⁻¹ * t * e)) * e⁻¹ := by rw [h]
      _ = (e * x * e⁻¹) * t := by group
  have hyE : y ∈ E := by
    refine hmax y hy5 (fun e he => ?_)
    have := commute_of_cyclic_normalized
      (Subgroup.centralizer ((M 0 ⊔ M 1 ⊔ M 3 : Subgroup G) : Set G) ⊓ N) hyY hy5
      (CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := E) e he) (hnormY e he)
    exact this
  have hyC := hyY.1
  have hyC' : ∀ i, M i ≤ M 0 ⊔ M 1 ⊔ M 3 → y ∈ Subgroup.centralizer (M i : Set G) := by
    intro i hi
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_iff.mp hyC h (hi hh)
  have h0 := hyC' 0 (le_sup_left.trans le_sup_left)
  have h1 := hyC' 1 (le_sup_right.trans le_sup_left)
  have h3 := hyC' 3 le_sup_right
  have hBX : B ≤ M 0 ⊔ Subgroup.centralizer (M 0 : Set G) := by
    calc B = (B ⊓ Subgroup.centralizer (M 0 : Set G)) ⊔ (B ⊓ M 0) := (htor.1 0).1
      _ ≤ M 0 ⊔ Subgroup.centralizer (M 0 : Set G) :=
        sup_le (inf_le_right.trans le_sup_right) (inf_le_right.trans le_sup_left)
  have hyB : y ∈ B :=
    inf_le_of_outer hBE hEcard hBX hcE hcout ⟨hyE, Subgroup.mem_sup_right h0⟩
  have h30 : M 3 ≤ Subgroup.centralizer (M 0 : Set G) :=
    (hcomm 3 0 (by decide) (by simp [chainAdj])).1
  have h31 : M 3 ≤ Subgroup.centralizer (M 1 : Set G) :=
    (hcomm 3 1 (by decide) (by simp [chainAdj])).1
  have hy1 : y = 1 := eq_one_of_torus_centralizes hBcard htor h30 h31 hyB h0 h1 h3
  rw [hy1, orderOf_one] at hy5
  omega

end Ambient

end CFSG.RankThree.PartOne.CTP
