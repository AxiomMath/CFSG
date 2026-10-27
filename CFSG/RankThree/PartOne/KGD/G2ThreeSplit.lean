module

public import CFSG.RankThree.PartOne.KGD.G2Abstract
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor

public section

namespace CFSG.RankThree.PartOne.KGD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.LocalRank CFSG.RankThree.Chevalley
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ComponentClassification.UnbalancedCatalog
open scoped Pointwise

theorem solvable_normal_split (K : Type) [Field K] [Finite K]
    (hKodd : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1)
    (x : adjointGroup .G2 K) (hxp : orderOf x = p) :
    ∀ V : Subgroup (centralizer ({x} : Set (adjointGroup .G2 K))), V.Normal →
      Group.IsSolvable V →
      (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 4 := by
  classical
  obtain ⟨hconjH, -, -, -, -⟩ := odd_G2_split_prime_toral_Sylow_and_centralizers K hKodd hp hp3 hpq
  have hPx : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxp, pow_one])
  obtain ⟨g, hg⟩ := hconjH _ hPx
  have hgx : g * x * g⁻¹ ∈ (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) :=
    hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgx
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hao : orderOf (rootDiagUnit .G2 a) = p := by
    rw [← ha, orderOf_injective _ (adjointGroup .G2 K).subtype_injective,
      show g * x * g⁻¹ = (MulAut.conj g).toMonoidHom x from rfl,
      orderOf_injective _ (MulAut.conj g).injective x, hxp]
  rcases toral_centralizer_cases_G2 K hKodd hp hp3 hpq a hao with ⟨⟨-, hMH, -⟩, -⟩ |
    ⟨⟨α, -, -, -, -, -, hQq, hcomm, hZ, hZH, -⟩, -⟩
  · obtain ⟨φ, hφ⟩ := exists_injective_of_toralCentralizer_eq_torusGroup ha hMH
    exact solvable_normal_abelian_card_le _ (Or.inl ⟨φ, hφ⟩)
  · obtain ⟨-, hRq, φ, hφ⟩ := derived_centralizer_data ha hcomm hQq hZ hZH
    exact solvable_normal_abelian_card_le _ (Or.inr ⟨hRq, φ, hφ⟩)

theorem autThetaT_eq_bot_of_split (K : Type) [Field K] [Finite K]
    (hKodd : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1)
    (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (A : Subgroup (MulAut (adjointGroup .G2 K))) (hA : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2)
    (hAinn : A ≤ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range) :
    autThetaT p B A = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨hconjH, -, -, -, -⟩ := odd_G2_split_prime_toral_Sylow_and_centralizers K hKodd hp hp3 hpq
  obtain ⟨P, hPmap, hPcard, hPp, hPpow⟩ := plane_comap_conj hinj hp hA hAcard hAinn
  obtain ⟨g, hg⟩ := hconjH P hPp
  set F := (adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom with hFdef
  have hF : Function.Injective F := Subtype.val_injective.comp (MulAut.conj g).injective
  have hPH : P.map F = torusTorsion K p := by
    have : NeZero p := ⟨hp.ne_zero⟩
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      rw [mem_torusTorsion_iff]
      refine ⟨hg ⟨u, hu, rfl⟩, ?_⟩
      rw [← map_pow, hPpow u hu, map_one]
    · rw [natCard_torusTorsion hpq, Subgroup.card_map_of_injective hF, hPcard]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hpq)
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have key : ∀ i : Fin Tag.G2.rank, ∃ u ∈ P, u ≠ 1 ∧
      (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
          centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)).map F =
        rootSubgroup .G2 K (Pi.single i 1) ⊔ rootSubgroup .G2 K (-Pi.single i 1) ∧
      CFSG.IsQuasisimple (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
        centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) := by
    intro i
    obtain ⟨j, hji⟩ : ∃ j : Fin Tag.G2.rank, j ≠ i := by
      rcases fin_G2_cases i with rfl | rfl
      · exact ⟨g2ir, by decide⟩
      · exact ⟨g2ia, by decide⟩
    set c : Fin Tag.G2.rank → Kˣ := fun k => if k = i then 1 else ζ with hc
    have hcp : c ^ p = 1 := funext fun k => by
      by_cases hk : k = i <;> simp [hc, hk, hζp]
    have hc1 : c ≠ 1 := fun h => hζ1 (by simpa [hc, hji] using congrFun h j)
    have hci : c i = 1 := by simp [hc]
    have hdc : rootDiagUnit .G2 c ∈ P.map F := by
      rw [hPH]
      exact (rootDiagUnit_mem_torusTorsion_iff p c).2 hcp
    obtain ⟨u, hu, hdu⟩ := hdc
    have hu1 : u ≠ 1 := fun h => hc1 (rootDiagUnit_injective (by
      rw [← hdu, h, map_one, rootDiagUnit_one]))
    obtain ⟨hRmap, hRq⟩ := derived_centralizer_root_data hKodd hp hp3 hpq hdu hcp hc1 i hci
    exact ⟨u, hu, hu1, hRmap, hRq⟩
  obtain ⟨u₁, hu₁, hu₁1, hR₁, hq₁⟩ := key g2ia
  obtain ⟨u₂, hu₂, hu₂1, hR₂, hq₂⟩ := key g2ir
  have htop : (⁅centralizer ({u₁} : Set (adjointGroup .G2 K)),
        centralizer ({u₁} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ⊔
      ⁅centralizer ({u₂} : Set (adjointGroup .G2 K)),
        centralizer ({u₂} : Set (adjointGroup .G2 K))⁆ = ⊤ := by
    apply Subgroup.map_injective hF
    rw [Subgroup.map_sup, hR₁, hR₂, rootSubgroup_simple_sup_eq_adjointGroup]
    ext z
    refine ⟨fun hz => ⟨g⁻¹ * (⟨z, hz⟩ : adjointGroup .G2 K) * g, Subgroup.mem_top _, ?_⟩, ?_⟩
    · change ((g * (g⁻¹ * (⟨z, hz⟩ : adjointGroup .G2 K) * g) * g⁻¹ : adjointGroup .G2 K) :
        ModGL .G2 K) = z
      rw [show g * (g⁻¹ * (⟨z, hz⟩ : adjointGroup .G2 K) * g) * g⁻¹ =
        (⟨z, hz⟩ : adjointGroup .G2 K) by group]
    · rintro ⟨y, -, rfl⟩
      exact ((MulAut.conj g) y).2
  have hbA : ∀ u ∈ P, (MulAut.conj u : MulAut (adjointGroup .G2 K)) ∈ A := fun u hu =>
    hPmap ▸ Subgroup.mem_map_of_mem _ hu
  have hb1 : ∀ u : adjointGroup .G2 K, u ≠ 1 →
      (MulAut.conj u : MulAut (adjointGroup .G2 K)) ≠ 1 := fun u hu h =>
    hu (hinj (by rw [h, map_one]))
  have hRY : ∀ u : adjointGroup .G2 K, (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
      centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ≤
      centralizer ({u} : Set (adjointGroup .G2 K)) := fun u =>
    Subgroup.commutator_le.2 fun v hv w hw => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hv hw) (inv_mem hv)) (inv_mem hw)
  have hfix₁ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₁ (hRY u₁)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₁
  have hfix₂ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₂ (hRY u₂)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₂
  rw [eq_bot_iff]
  intro s hs
  obtain ⟨s₁, hs₁, hs₁eq⟩ := exists_mem_theta_of_mem_autThetaT hp B hs (hbA u₁ hu₁)
    (hb1 u₁ hu₁1) (hB ⟨u₁, rfl⟩)
  obtain ⟨s₂, hs₂, hs₂eq⟩ := exists_mem_theta_of_mem_autThetaT hp B hs (hbA u₂ hu₂)
    (hb1 u₂ hu₂1) (hB ⟨u₂, rfl⟩)
  have hle : (⁅centralizer ({u₁} : Set (adjointGroup .G2 K)),
        centralizer ({u₁} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ⊔
      ⁅centralizer ({u₂} : Set (adjointGroup .G2 K)),
        centralizer ({u₂} : Set (adjointGroup .G2 K))⁆ ≤
      MonoidHom.eqLocus (s : MulAut (adjointGroup .G2 K)).toMonoidHom (MonoidHom.id _) :=
    sup_le (fun r hr => by rw [← hs₁eq]; exact hfix₁ s₁ hs₁ r hr)
      (fun r hr => by rw [← hs₂eq]; exact hfix₂ s₂ hs₂ r hr)
  rw [htop] at hle
  rw [Subgroup.mem_bot]
  exact MulEquiv.ext fun y => hle (Subgroup.mem_top y)

end CFSG.RankThree.PartOne.KGD
