module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09u
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5N
import CFSG.GroupTheory.PCoreSurjective
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen4Aux
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R917A5L
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92a
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.GroupTheory.ThreeTranspositions (HasE9)

variable {G : Type} [Group G] [Finite G]

private theorem ne_top_of_hyp97' {D : Data G} {Y H D₃ S : Subgroup G} (hY : Hyp97 D Y H D₃ S) :
    H ≠ ⊤ := by
  haveI := D.standing.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : H ≠ ⊥ := by
    intro h
    have hD : D₃ ≤ ⊥ := h ▸ hY.1.2.2.1.trans ((opp_le_self 3 Y).trans hY.1.2.1.1)
    have h3 := hY.1.2.2.2
    rw [le_bot_iff.1 hD, card_bot] at h3
    exact absurd h3 (by norm_num)
  have hne := CFSG.LocalAnalysis.UniquenessCase.PartTwo.pCoreOf_ne_bot_of_fstar hY.2.2.1.2 hH
  intro htop
  refine CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab
    (show IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) from
      ⟨pCoreOf 2 H, hne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩) ?_
  exact top_le_iff.1 (htop.ge.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))

theorem r913A5S_holds (hKF : KFactShape92A5Normalizer) (D : Data G) (h92 : R92 D) :
    R913A5S D := by
  intro Y H D₃ S hY hA5 hSH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYH : Y ≤ H := hY.1.2.1.1
  have hXY : Opp 3 Y ≤ Y := opp_le_self 3 Y
  have hXL : Opp 3 Y ≤ L9 Y H := opp_le_L9 Y H
  have hDX : D₃ ≤ Opp 3 Y := hY.1.2.2.1
  have hDL : D₃ ≤ L9 Y H := hDX.trans hXL
  have hD3 : Nat.card D₃ = 3 := hY.1.2.2.2
  have hLH : L9 Y H ≤ H := L9_le_of_le hYH
  obtain ⟨h1, h2⟩ := h92 Y H D₃ hY.1 (ne_top_of_hyp97' hY)
  have hYHM : Y ≤ H ⊓ D.M := le_inf hYH hY.1.1.1
  have hHMX : H ⊓ D.M ≤ normalizer (Opp 3 Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hXY.trans hYHM)).1 (r9R5_holds D Y H D₃ S hY).1
  obtain ⟨φ, hφ, hker⟩ := exists_surjective_Lbar9 hYH
  set ψ : ↥(Opp 3 Y) →* Lbar9 Y H := φ.comp (inclusion hXL) with hψ
  have hψk : ψ.ker ≤ CFSG.pCore 2 ↥(Opp 3 Y) := fun x hx => by
    have hcov : Opp 3 Y = Opp 3 Y ⊔ pCoreOf 2 (Opp 3 Y) :=
      (sup_eq_left.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).symm
    exact (CFSG.mem_openPCoreOf_iff x).1 (inf_I9_le_pCoreOf le_rfl hcov hA5 (hXY.trans hYH)
      (mem_inf.2 ⟨x.2, (hker _).1 (MonoidHom.mem_ker.1 hx)⟩))
  have hKA5 : IsAlt (Bar2 ψ.range) 5 := by
    obtain ⟨e⟩ := hA5
    obtain ⟨f⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker
      ψ.rangeRestrict ψ.rangeRestrict_surjective
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥(Opp 3 Y))).to_le
        ((MonoidHom.ker_rangeRestrict ψ).le.trans hψk))
    exact ⟨f.symm.trans e⟩
  have hnorm : ∀ g : ↥(L9 Y H), (g : G) ∈ normalizer (Opp 3 Y : Set G) →
      φ g ∈ normalizer (ψ.range : Set (Lbar9 Y H)) := by
    have key : ∀ g : ↥(L9 Y H), (g : G) ∈ normalizer (Opp 3 Y : Set G) →
        ∀ k ∈ ψ.range, φ g * k * (φ g)⁻¹ ∈ ψ.range := by
      rintro g hg _ ⟨x, rfl⟩
      refine ⟨⟨g * x * g⁻¹, (mem_normalizer_iff.1 hg x).1 x.2⟩, ?_⟩
      simp only [hψ, MonoidHom.comp_apply]
      rw [← map_inv, ← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext rfl)
    intro g hg
    refine mem_normalizer_iff.2 fun k => ⟨key g hg k, fun h => ?_⟩
    simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ h
  set Db : Subgroup (Lbar9 Y H) := (D₃.subgroupOf (Opp 3 Y)).map ψ with hDb
  have hDb3 : Nat.card Db = 3 := by
    have hc : Nat.card (D₃.subgroupOf (Opp 3 Y)) = 3 :=
      (Nat.card_congr (subgroupOfEquivOfLe hDX).toEquiv).trans hD3
    rcases (Nat.dvd_prime Nat.prime_three).1 (hc ▸ card_map_dvd _ ψ) with h | h
    · refine absurd (hD3 ▸ card_dvd_of_le fun d hd => ?_) (not_dvd_card_I9 H)
      have hk := (Subgroup.map_eq_bot_iff _).1 (Subgroup.card_eq_one.1 h)
        (show (⟨d, hDX hd⟩ : ↥(Opp 3 Y)) ∈ D₃.subgroupOf (Opp 3 Y) from hd)
      exact (hker _).1 (MonoidHom.mem_ker.1 hk)
    · exact h
  set J : Subgroup G := D₃ ⊔ (L9 Y H ⊓ I9 H) with hJ
  have hJL : J ≤ L9 Y H := sup_le hDL inf_le_left
  have hJ1 : ∀ l : ↥(L9 Y H), φ l ∈ Db → (l : G) ∈ J := by
    rintro l ⟨x, hx, hxl⟩
    have hx' : φ (inclusion hXL x) = φ l := hxl
    have hi : (x : G)⁻¹ * l ∈ I9 H := by
      have h := (hker ((inclusion hXL x)⁻¹ * l)).1 (by rw [map_mul, map_inv, hx', inv_mul_cancel])
      simpa using h
    rw [show (l : G) = x * ((x : G)⁻¹ * l) by group]
    exact mul_mem ((le_sup_left : D₃ ≤ J) (mem_subgroupOf.1 hx))
      ((le_sup_right : L9 Y H ⊓ I9 H ≤ J)
        (mem_inf.2 ⟨(L9 Y H).mul_mem ((L9 Y H).inv_mem (hXL x.2)) l.2, hi⟩))
  have hJ2 : ∀ j ∈ J, ∀ hj : j ∈ L9 Y H, φ ⟨j, hj⟩ ∈ ψ.range := by
    have hP : J ≤ ((ψ.range).comap φ).map (L9 Y H).subtype := by
      refine sup_le (fun d hd => ⟨⟨d, hDL hd⟩, ⟨⟨d, hDX hd⟩, rfl⟩, rfl⟩) fun x hx => ?_
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      show φ ⟨x, hx.1⟩ ∈ ψ.range
      rw [(hker _).2 hx.2]
      exact one_mem _
    intro j hjJ hj
    obtain ⟨j', hj', hjj⟩ := hP hjJ
    rw [show (⟨j, hj⟩ : ↥(L9 Y H)) = j' from Subtype.ext hjj.symm]
    exact hj'
  have hN : normalizer (Db : Set (Lbar9 Y H)) ≤ normalizer (ψ.range : Set (Lbar9 Y H)) := by
    intro y hy
    obtain ⟨l, rfl⟩ := hφ y
    have hDl : D₃.map (MulAut.conj (l : G)).toMonoidHom ≤ J := by
      rintro _ ⟨d, hd, rfl⟩
      have hdl := hJ1 (l * ⟨d, hDL hd⟩ * l⁻¹) (by
        rw [map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.1 hy _).1 ⟨⟨d, hDX hd⟩, hd, rfl⟩)
      simpa [MulAut.conj_apply] using hdl
    have hJ9 : ¬ HasE9 ↥J := fun h => not_hasE9_L9 hY.1
      (CFSG.GroupTheory.ThreeTranspositions.HasE9.map_injective (inclusion hJL)
        (inclusion_injective hJL) h)
    have hDl3 : Nat.card (D₃.map (MulAut.conj (l : G)).toMonoidHom) = 3 := by
      rw [card_map_of_injective (MulAut.conj (l : G)).injective, hD3]
    obtain ⟨j, hjJ, hj⟩ := exists_map_conj_eq_of_card_eq_three hJ9 le_sup_left hDl hD3 hDl3
    have hn : j⁻¹ * (l : G) ∈ normalizer (D₃ : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have e : ∀ a b : G, (MulAut.conj (a * b)).toMonoidHom =
          (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := fun a b => by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      have e1 : (MulAut.conj j⁻¹).toMonoidHom.comp (MulAut.conj j).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      change D₃.map (MulAut.conj (j⁻¹ * l)).toMonoidHom = D₃
      rw [e, ← Subgroup.map_map, ← hj, Subgroup.map_map, e1, Subgroup.map_id]
    have hnM : j⁻¹ * (l : G) ∈ D.M := normalizer_le_of_mem_uniqueSet D.maxLocal
      (hY.1.1.2.2 D₃ (hDX.trans hXY) hD3) hn
    have hjL : j ∈ L9 Y H := hJL hjJ
    have hnL : j⁻¹ * (l : G) ∈ L9 Y H := mul_mem (inv_mem hjL) l.2
    rw [show l = ⟨j, hjL⟩ * ⟨j⁻¹ * l, hnL⟩ from Subtype.ext (by simp), map_mul]
    exact mul_mem (le_normalizer (hJ2 j hjJ hjL)) (hnorm _ (hHMX ⟨hLH hnL, hnM⟩))
  obtain ⟨Q, hQ⟩ := hSH.inf_of_le_normalizer hLH (le_normalizer_L9 Y H)
  have hT : ((Q.mapSurjective hφ : Sylow 2 (Lbar9 Y H)) : Subgroup (Lbar9 Y H)) ≤
      normalizer (ψ.range : Set (Lbar9 Y H)) := by
    rw [Sylow.coe_mapSurjective]
    rintro _ ⟨q, hq, rfl⟩
    have hqS : (q : G) ∈ S ⊓ L9 Y H := by
      rw [← hQ]
      exact mem_map_of_mem _ hq
    exact hnorm q (hHMX (hYHM (hY.2.2.2.le hqS.1)))
  rcases hKF (Lbar9 Y H) h2 ψ.range Db (Q.mapSurjective hφ) hKA5 (map_le_range ψ _) hDb3 hN hT
    with hK | hLie
  ·
    left
    refine le_antisymm (h1.le.trans (sup_le (fun l hl => ?_) le_sup_right))
      (sup_le (map_subtype_le _) inf_le_left)
    obtain ⟨x, hx⟩ : φ ⟨l, hl⟩ ∈ ψ.range := hK ▸ mem_top _
    have hx' : φ (inclusion hXL x) = φ ⟨l, hl⟩ := hx
    have hi : (x : G)⁻¹ * l ∈ I9 H := by
      have h := (hker ((inclusion hXL x)⁻¹ * ⟨l, hl⟩)).1
        (by rw [map_mul, map_inv, hx', inv_mul_cancel])
      simpa using h
    rw [show l = (x : G) * ((x : G)⁻¹ * l) by group]
    exact mul_mem ((le_sup_right : H ⊓ D.M ≤ I9 H ⊔ (H ⊓ D.M)) (hYHM (hXY x.2)))
      ((le_sup_left : I9 H ≤ I9 H ⊔ (H ⊓ D.M)) hi)
  · exact Or.inr hLie

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
