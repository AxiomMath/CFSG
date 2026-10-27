module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPBar
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymDefs
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymOmega

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}
  {X : Type} [Group X] {φ : ↥(kGenIn V H) →* X}

private theorem wc85bg_conjSubgroup_zpowers {X : Type} [Group X] (t g : X) :
    conjSubgroup (Subgroup.zpowers t) g = Subgroup.zpowers (g⁻¹ * t * g) := by
  change (Subgroup.zpowers t).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [MonoidHom.map_zpowers]
  congr 1
  simp [MulAut.conj_apply]

private theorem wc85bg_conjSubgroup_wClos (x : G) :
    conjSubgroup (E3.wClos V 0 T) x =
      ⨆ A ∈ E3.gammaSet V 0 T, conjSubgroup A x := by
  rw [show conjSubgroup (E3.wClos V 0 T) x =
      (E3.wClos V 0 T).map (MulAut.conj x⁻¹).toMonoidHom from rfl]
  unfold E3.wClos
  rw [Subgroup.map_iSup]
  refine iSup_congr fun A => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ => rfl

private theorem wc85bg_exists_conjSubgroup_of_mem_gammaSet (hV : IsPGroup 2 V)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V 0 T) :
    ∃ g : G, A = conjSubgroup V g ∧ conjSubgroup V g ≤ T := by
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  have hp : IsPGroup 2 (conjSubgroup V g) := E3.isPGroup_conjSubgroup hV g
  have hAe : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hp hAg).1 hm
  exact ⟨g, hAe, hAe ▸ hAT⟩

private theorem wc85bg_mem_normalizer_wClos (x : G)
    (h : ∀ A ∈ E3.gammaSet V 0 T, conjSubgroup A x ≤ E3.wClos V 0 T) :
    x ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
  have hle : conjSubgroup (E3.wClos V 0 T) x ≤ E3.wClos V 0 T := by
    rw [wc85bg_conjSubgroup_wClos]
    exact iSup₂_le h
  exact conjSubgroup_eq_iff_mem_normalizer.mp
    (Subgroup.eq_of_le_of_card_ge hle (E3.card_conjSubgroup _ x).ge)

theorem mem_normalizer_wClos_of_mem_setNormalizer (s : TailSetup V H T φ)
    (hfirst : ∀ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) → U ≤ H →
      U ∈ omegaHIn V H ∨ ∀ W ∈ omegaHIn V H, ∀ u ∈ U, ∀ w ∈ W, u * w = w * u)
    {t : X} (ht : barSub (kGenIn V H) φ V = Subgroup.zpowers t) {P : Sylow 2 X}
    (hP : (P : Subgroup X) = barSub (kGenIn V H) φ T) (k : ↥(kGenIn V H))
    (hk : φ k ∈ Subgroup.setNormalizer (symT t (P : Subgroup X))) :
    (k : G) ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
  have hV : IsPGroup 2 V :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian s.hyp83.elemAbelian
  have hxN : (k : G)⁻¹ ∈ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
    refine wc85bg_mem_normalizer_wClos ((k : G)⁻¹) fun A hA => ?_
    obtain ⟨g, rfl, hgT⟩ := wc85bg_exists_conjSubgroup_of_mem_gammaSet hV hA
    have hU : conjSubgroup V g ≤ H := hgT.trans s.hyp83.T_le_H
    rcases hfirst (conjSubgroup V g) ⟨g, rfl⟩ hU with hUom | hcomm
    · obtain ⟨k₁, hUeq⟩ := exists_conjSubgroup_eq_of_mem_omegaHIn s hUom
      have hk₁T : conjSubgroup V (k₁ : G) ≤ T := hUeq ▸ hgT
      have hmem1 : (φ k₁)⁻¹ * t * φ k₁ ∈ symT t (P : Subgroup X) :=
        (conjSubgroup_le_T_iff_mem_symT s ht hP k₁).mp hk₁T
      have hmem2 : (φ (k₁ * k⁻¹))⁻¹ * t * φ (k₁ * k⁻¹) ∈ symT t (P : Subgroup X) := by
        have h := (Subgroup.mem_set_normalizer_iff.mp hk _).1 hmem1
        simpa [map_mul, map_inv, mul_assoc] using h
      have hleT : conjSubgroup V (g * (k : G)⁻¹) ≤ T := by
        rw [← conjSubgroup_conjSubgroup V g ((k : G)⁻¹), hUeq,
          conjSubgroup_conjSubgroup]
        exact (conjSubgroup_le_T_iff_mem_symT s ht hP (k₁ * k⁻¹)).mpr hmem2
      have hmemGam : conjSubgroup V (g * (k : G)⁻¹) ∈ E3.gammaSet V 0 T :=
        ⟨hleT, g * (k : G)⁻¹, le_rfl, E3.mQuot_self _⟩
      rw [conjSubgroup_conjSubgroup V g ((k : G)⁻¹)]
      exact le_iSup₂_of_le _ hmemGam le_rfl
    · have hKc : kGenIn V H ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
        kGenIn_le_centralizer_of_comm_omegaHIn s.hyp83.le_H hcomm
      have hkN : (k : G) ∈ Subgroup.normalizer (conjSubgroup V g : Set G) :=
        Subgroup.centralizer_le_normalizer (conjSubgroup V g : Set G) (hKc k.2)
      have hEqU : conjSubgroup (conjSubgroup V g) ((k : G)⁻¹) = conjSubgroup V g :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (by simpa using Subgroup.inv_mem _ hkN)
      rw [hEqU]
      exact le_iSup₂_of_le _ ⟨hgT, g, le_rfl, E3.mQuot_self _⟩ le_rfl
  exact (by simpa using Subgroup.inv_mem _ hxN : (k : G) ∈
    Subgroup.normalizer (E3.wClos V 0 T : Set G))


theorem threeFirst_of_bar_generation (s : TailSetup V H T φ)
    (hfirst : ∀ U : Subgroup G, (∃ g : G, U = conjSubgroup V g) → U ≤ H →
      U ∈ omegaHIn V H ∨ ∀ W ∈ omegaHIn V H, ∀ u ∈ U, ∀ w ∈ W, u * w = w * u)
    {t : X} (ht : barSub (kGenIn V H) φ V = Subgroup.zpowers t) {P : Sylow 2 X}
    (hP : (P : Subgroup X) = barSub (kGenIn V H) φ T)
    (hgen : Subgroup.closure ((Subgroup.centralizer ({t} : Set X) : Set X) ∪
      (Subgroup.setNormalizer (symT t (P : Subgroup X)) : Set X)) = ⊤) :
    H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
      (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) := by
  have hV : IsPGroup 2 V :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian s.hyp83.elemAbelian
  let R : Subgroup G := (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
    (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G))
  have hTW : T ≤ Subgroup.normalizer (E3.wClos V 0 T : Set G) := by
    intro x hx
    refine wc85bg_mem_normalizer_wClos x ?_
    intro A hA
    obtain ⟨g, rfl, hgT⟩ := wc85bg_exists_conjSubgroup_of_mem_gammaSet hV hA
    have hleT : conjSubgroup V (g * x) ≤ T := by
      rw [← conjSubgroup_conjSubgroup V g x]
      exact conjSubgroup_le_of_le hgT hx
    have hm0 : E3.mQuot (conjSubgroup V (g * x)) (conjSubgroup V (g * x)) = 0 :=
      E3.mQuot_self _
    have hmemGam : conjSubgroup V (g * x) ∈ E3.gammaSet V 0 T :=
      ⟨hleT, g * x, le_rfl, hm0⟩
    rw [conjSubgroup_conjSubgroup]
    exact le_iSup₂_of_le (conjSubgroup V (g * x)) hmemGam le_rfl
  have hT_le_R : T ≤ R := by
    refine le_trans (le_inf s.hyp83.T_le_H ?_) le_sup_right
    exact hTW
  let S : Subgroup X := (R.subgroupOf (kGenIn V H)).map φ
  have hCS : Subgroup.centralizer ({t} : Set X) ≤ S := by
    intro x hx
    obtain ⟨k₀, rfl⟩ := s.bar.surjective x
    refine Subgroup.mem_map.mpr ⟨k₀, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine (le_sup_left : H ⊓ Subgroup.normalizer (V : Set G) ≤ R) ⟨?_, ?_⟩
    · exact kGenIn_le_H s.hyp83.le_H k₀.2
    · refine (mem_normalizer_iff_bar s k₀).mpr ?_
      rw [ht]
      have hxt : t * φ k₀ = φ k₀ * t :=
        Subgroup.mem_centralizer_iff.mp hx t (by simp)
      have hconj : (φ k₀)⁻¹ * t * (φ k₀) = t := by
        calc (φ k₀)⁻¹ * t * (φ k₀) = (φ k₀)⁻¹ * (t * φ k₀) := by group
          _ = (φ k₀)⁻¹ * (φ k₀ * t) := by rw [hxt]
          _ = t := by group
      exact conjSubgroup_eq_iff_mem_normalizer.mp (by
        rw [wc85bg_conjSubgroup_zpowers, hconj])
  have hNS : Subgroup.setNormalizer (symT t (P : Subgroup X)) ≤ S := by
    intro x hx
    obtain ⟨k₀, rfl⟩ := s.bar.surjective x
    refine Subgroup.mem_map.mpr ⟨k₀, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine (le_sup_right : H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G) ≤ R) ⟨?_, ?_⟩
    · exact kGenIn_le_H s.hyp83.le_H k₀.2
    · exact mem_normalizer_wClos_of_mem_setNormalizer s hfirst ht hP k₀ hx
  have hS : S = ⊤ := by
    have hle : Subgroup.closure ((Subgroup.centralizer ({t} : Set X) : Set X) ∪
        (Subgroup.setNormalizer (symT t (P : Subgroup X)) : Set X)) ≤ S :=
      (Subgroup.closure_le S).mpr (Set.union_subset hCS hNS)
    exact le_antisymm le_top (hgen ▸ hle)
  have hmemR : ∀ k : ↥(kGenIn V H), (k : G) ∈ R := by
    intro k
    have hkS : φ k ∈ S := by
      rw [hS]
      exact Subgroup.mem_top _
    obtain ⟨r, hr, hφr⟩ := Subgroup.mem_map.mp hkS
    have hrR : (r : G) ∈ R := hr
    have hkr : ((k * r⁻¹ : ↥(kGenIn V H)) : G) ∈ R := by
      have hφ1 : φ (k * r⁻¹) = 1 := by
        rw [map_mul, map_inv, hφr, mul_inv_cancel]
      refine (le_sup_left : H ⊓ Subgroup.normalizer (V : Set G) ≤ R) ⟨?_, ?_⟩
      · exact kGenIn_le_H s.hyp83.le_H (k * r⁻¹).2
      · refine (mem_normalizer_iff_bar s (k * r⁻¹)).mpr ?_
        rw [hφ1]
        exact Subgroup.one_mem _
    have hmul : ((k * r⁻¹ : ↥(kGenIn V H)) : G) * (r : G) ∈ R := R.mul_mem hkr hrR
    have heq : ((k * r⁻¹ : ↥(kGenIn V H)) : G) * (r : G) = (k : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact heq ▸ hmul
  have hK_le_R : kGenIn V H ≤ R := by
    refine iSup₂_le fun g hg => ?_
    intro x hx
    have hxK : x ∈ kGenIn V H := by
      have hle : conjSubgroup V g ≤ kGenIn V H := le_iSup₂_of_le g hg le_rfl
      exact hle hx
    exact hmemR ⟨x, hxK⟩
  have hH_le_R : H ≤ R := by
    rw [s.eq_sup]
    exact sup_le hK_le_R hT_le_R
  exact le_antisymm hH_le_R (sup_le inf_le_left inf_le_left)


end CFSG.LocalAnalysis.WeakClosure81

end
