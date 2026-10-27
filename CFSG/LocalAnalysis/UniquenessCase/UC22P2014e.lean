module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p2014e_le_of_card_dvd {p : ℕ} [Fact p.Prime] {S H L : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf p S H) (hLH : L ≤ H) (hHL : H ≤ normalizer (L : Set G))
    (hdvd : Nat.card S ∣ Nat.card L) : S ≤ L := by
  have h1 := (hS.inf_of_le_normalizer hLH hHL).card_eq
  have h2 : Nat.card S ∣ Nat.card (S ⊓ L : Subgroup G) := by
    rw [h1, hS.card_eq]
    rw [hS.card_eq] at hdvd
    exact pow_dvd_pow p
      ((Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').1 hdvd)
  exact inf_eq_left.1 (Subgroup.eq_of_le_of_card_ge inf_le_left (Nat.le_of_dvd Nat.card_pos h2))

theorem uc22p2014e_opp_le {p : ℕ} [Fact p.Prime] {P H L : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P H) (hLH : L ≤ H) (hHL : H ≤ normalizer (L : Set G))
    (hdvd : Nat.card P ∣ Nat.card L) : Opp p H ≤ L := by
  refine (Subgroup.closure_le _).2 ?_
  rintro y ⟨hyH, k, hk⟩
  have hY : IsPGroup p ((zpowers y).subgroupOf H) :=
    (IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])).comap_subtype
  obtain ⟨Q, hQ⟩ := hY.exists_le_sylow
  have hS : CFSG.ABGLocalTools.IsSylowOf p ((Q : Subgroup ↥H).map H.subtype) H := ⟨Q, rfl⟩
  have hSL := uc22p2014e_le_of_card_dvd hS hLH hHL (by rw [hS.card_eq, ← hP.card_eq]; exact hdvd)
  exact hSL ⟨⟨y, hyH⟩, hQ (Subgroup.mem_subgroupOf.2 (mem_zpowers y)), rfl⟩

theorem uc22p2014e_opp_eq_of_le {p : ℕ} {A B : Subgroup G} (hAB : A ≤ B) (hBA : Opp p B ≤ A) :
    Opp p B = Opp p A := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_)
    (Subgroup.closure_mono fun y hy => ⟨hAB hy.1, hy.2⟩)
  rintro y ⟨hyB, k, hk⟩
  exact Subgroup.subset_closure ⟨hBA (Subgroup.subset_closure ⟨hyB, k, hk⟩), k, hk⟩

theorem uc22p2014e_opp_top_eq_subgroupOf {p : ℕ} (hp : p.Prime) (B : Subgroup G) :
    Opp p (⊤ : Subgroup ↥B) = (Opp p B).subgroupOf B := by
  apply Subgroup.map_injective B.subtype_injective
  have hle : Opp p B ≤ B := (Subgroup.closure_le _).2 fun y hy => hy.1
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hle]
  unfold Opp
  rw [PartTwo.s13_pElementSubgroup_map hp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem uc22p2014e_range_eq_opp_top {p : ℕ} (hp : p.Prime) {X Y : Type} [Group X] [Group Y]
    [Finite Y] (g : X →* Y) (hg : g.range = Opp p (⊤ : Subgroup Y)) (N : Subgroup Y) [N.Normal] :
    ((QuotientGroup.mk' N).comp g).range = Opp p (⊤ : Subgroup (Y ⧸ N)) := by
  rw [MonoidHom.range_comp, hg]
  unfold Opp
  rw [PartTwo.s13_pElementSubgroup_map hp,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

theorem uc22p2014e_nonempty_mulEquiv {p : ℕ} (hp : p.Prime) {A B L : Subgroup G} (hAB : A ≤ B)
    (hBA : B ≤ normalizer (A : Set G)) (hAL : A ≤ L) (hopp : Opp p B ≤ A) :
    Nonempty (↥(Opp p (⊤ : Subgroup (Bar2 B))) ≃*
      ↥(Opp p (⊤ : Subgroup (Bar2 (barImage L A))))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKB : Opp p B ≤ B := hopp.trans hAB
  set ψ : ↥A →* ↥(barImage L A) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hAL)).codRestrict
      (barImage L A) (fun a => ⟨Subgroup.inclusion hAL a, Subgroup.mem_subgroupOf.2 a.2, rfl⟩)
      with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  have hψk : IsPGroup 2 ψ.ker := by
    refine (CFSG.pCore_isPGroup.comap_of_injective (Subgroup.inclusion hAL)
      (Subgroup.inclusion_injective hAL)).to_le fun a ha => ?_
    rw [MonoidHom.mem_ker] at ha
    rw [Subgroup.mem_comap, ← QuotientGroup.eq_one_iff]
    exact congrArg Subtype.val ha
  have hk : ψ.ker ≤ CFSG.pCore 2 ↥A := le_sSup ⟨ψ.normal_ker, hψk⟩
  have hA : ∀ a : ↥A, ψ a ∈ CFSG.pCore 2 ↥(barImage L A) ↔ a ∈ CFSG.pCore 2 ↥A := by
    intro a
    rw [← CFSG.map_pCore_eq_of_surjective_of_isPGroup_ker ψ hψs hψk, ← Subgroup.mem_comap,
      Subgroup.comap_map_eq, sup_eq_left.2 hk]
  set f₁ : ↥(Opp p B) →* Bar2 B :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥B)).comp (Subgroup.inclusion hKB) with hf₁
  set f₂ : ↥(Opp p B) →* Bar2 (barImage L A) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(barImage L A))).comp (ψ.comp (Subgroup.inclusion hopp))
    with hf₂
  have h1 : f₁.range = Opp p (⊤ : Subgroup (Bar2 B)) := by
    refine uc22p2014e_range_eq_opp_top hp _ ?_ _
    rw [Subgroup.inclusion_range, uc22p2014e_opp_top_eq_subgroupOf hp]
  have h2 : f₂.range = Opp p (⊤ : Subgroup (Bar2 (barImage L A))) := by
    refine uc22p2014e_range_eq_opp_top hp _ ?_ _
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, uc22p2014e_opp_eq_of_le hAB hopp,
      ← uc22p2014e_opp_top_eq_subgroupOf hp]
    unfold Opp
    rw [PartTwo.s13_pElementSubgroup_map hp, Subgroup.map_top_of_surjective _ hψs]
  have hker : f₁.ker = f₂.ker := by
    ext k
    simp only [hf₁, hf₂, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rw [hA, ← CFSG.mem_openPCoreOf_iff, ← CFSG.mem_openPCoreOf_iff]
    simp only [Subgroup.coe_inclusion]
    exact ⟨fun h => CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hAB ⟨hopp k.2, h⟩,
      fun h => CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hAB hBA h⟩
  exact ⟨(MulEquiv.subgroupCongr h1.symm).trans
    ((QuotientGroup.quotientKerEquivRange f₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        ((QuotientGroup.quotientKerEquivRange f₂).trans (MulEquiv.subgroupCongr h2))))⟩

theorem uc22p2014e_inf_le_normalizer {H M L : Subgroup G} (hHL : H ≤ normalizer (L : Set G)) :
    H ⊓ M ≤ normalizer ((M ⊓ L : Subgroup G) : Set G) := fun h hh => by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hh.2) y
  have h2 := Subgroup.mem_normalizer_iff.1 (hHL hh.1) y
  exact ⟨fun hy => ⟨h1.1 hy.1, h2.1 hy.2⟩, fun hy => ⟨h1.2 hy.1, h2.2 hy.2⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
