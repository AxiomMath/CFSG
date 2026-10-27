module

public import CFSG.Quasithin.Vol2.Ch11SecB24Claim
public import CFSG.Quasithin.Vol2.Ch11SecB22Six

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

theorem conjSubgroup_eq_bot_iff {G : Type} [Group G] {X : Subgroup G} {g : G} :
    conjSubgroup X g = ⊥ ↔ X = ⊥ :=
  ⟨fun h => by rw [← E3.conjSubgroup_conj_inv X g, h, E3.conjSubgroup_bot],
    fun h => by rw [h, E3.conjSubgroup_bot]⟩

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem autI_mem_aSet_n (hI : In24) (h : Hyp24 T L I n V₁ V₂) {g : G}
    (hAT : conjSubgroup (fsuV T I) g ≤ T) (hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥) :
    autI (h.flag hI).elem (conjSubgroup (fsuV T I) g) ∈
      E3.aSet n (autI (h.flag hI).elem ⊤) := by
  have hV := (h.flag hI).elem
  have hAN : conjSubgroup (fsuV T I) g ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    hAT.trans (T_le_normalizer_fsuV T I)
  have hAC : ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    intro hC
    apply hnc
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hC
  have hs := h.sParam hI hV
  have hn := h.hyp.one_lt
  have := autI_mem_aSet_of_le hV le_rfl hAN hAC (by rw [E3.mQuot_self, hs]; omega)
  rwa [E3.mQuot_self, hs, Nat.sub_zero] at this

theorem inf_centralizer_le_ROf (hI : In24) (h : Hyp24 T L I n V₁ V₂) :
    T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ ROf T L V₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hO2⟩ := hI.s3228 G T L I h.hyp.fsu
  rw [fsuL0_eq h.hyp] at hO2
  rw [← hO2]
  have hsub : LOf L V₂ ⊔ T ≤ L ⊔ T :=
    sup_le_sup_right ((perfectCore_le _).trans inf_le_left) T
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_
    (hsub.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  rw [hO2]
  exact inf_le_left.trans le_sup_right

theorem le_ROf (hI : In24) (h : Hyp24 T L I n V₁ V₂) {g : G}
    (hAT : conjSubgroup (fsuV T I) g ≤ T) : conjSubgroup (fsuV T I) g ≤ ROf T L V₂ := by
  by_cases hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ = ⊥
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hnc
    exact (le_inf hAT hnc).trans (inf_centralizer_le_ROf hI h)
  by_contra hAR
  have hfl := h.flag hI
  obtain ⟨h1, h2, h3⟩ := hI.facts.r2 G L (fsuV T I) ⊤ T V₁ V₂ n hfl _ hAT
    (E3.isElemAbelian_conjSubgroup hfl.elem g) (autI_mem_aSet_n hI h hAT hnc) hAR
  exact claim24 hI h hnc hfl.le₂ h1 h2 h3

theorem wClos_le_ROf (hI : In24) (h : Hyp24 T L I n V₁ V₂) :
    E3.wClos (fsuV T I) 0 T ≤ ROf T L V₂ := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, g, hAg, hA0⟩ := hA
  have hAeq : A = conjSubgroup (fsuV T I) g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup (isPGroup_fsuV h.hyp) g) hAg).mp hA0
  subst hAeq
  exact le_ROf hI h hAT

theorem line24 (hI : In24) (h : Hyp24 T L I n V₁ V₂) {g : G}
    (hAT : conjSubgroup (fsuV T I) g ≤ T) (hnc : ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥) :
    ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂ ∧
      fsuV T I ⊓ Subgroup.centralizer (conjSubgroup (fsuV T I) g : Set G) = V₂ := by
  have hfl := h.flag hI
  rcases hI.facts.r2Line G L (fsuV T I) ⊤ T V₁ V₂ n hfl _ (le_ROf hI h hAT)
    (E3.isElemAbelian_conjSubgroup hfl.elem g) (autI_mem_aSet_n hI h hAT hnc) with
    hc | ⟨hm1, hm2, l, hl, hl1⟩
  · exact hc
  exfalso
  set V := fsuV T I with hVdef
  set A := conjSubgroup V g with hAdef
  have hlV : l ∈ Subgroup.normalizer (V : Set G) :=
    hfl.le_normalizer (((perfectCore_le _).trans inf_le_left) hl)
  have hVl : conjSubgroup V l = V := conjSubgroup_eq_iff_mem_normalizer.mpr hlV
  have hCl : conjSubgroup (Subgroup.centralizer (V : Set G)) l =
      Subgroup.centralizer (V : Set G) := by
    rw [E3.conjSubgroup_centralizer, hVl]
  have hA : conjSubgroup A l = conjSubgroup V (g * l) := conjSubgroup_conjSubgroup _ _ _
  have e : ⁅V, conjSubgroup A l⁆ = conjSubgroup ⁅V, A⁆ l := by
    rw [E3.conjSubgroup_commutator, hVl]
  have h2 : E3.mQuot (conjSubgroup V (g * l))
      (conjSubgroup V (g * l) ⊓ Subgroup.centralizer (V : Set G)) = n := by
    have := E3.mQuot_conjSubgroup A (A ⊓ Subgroup.centralizer (V : Set G)) l
    rw [E3.conjSubgroup_inf, hCl, hA, hm1] at this
    exact this
  have h3 : E3.mQuot V (V ⊓ Subgroup.centralizer (conjSubgroup V (g * l) : Set G)) = n := by
    have := E3.mQuot_conjSubgroup V (V ⊓ Subgroup.centralizer (A : Set G)) l
    rw [conjSubgroup_inf_centralizer, hVl, hA, hm2] at this
    exact this
  have hnc' : ⁅V, conjSubgroup V (g * l)⁆ ≠ ⊥ := by
    rw [← hA, e]
    exact fun h0 => hnc (conjSubgroup_eq_bot_iff.mp h0)
  rw [hA] at hl1
  exact claim24 hI h hnc' le_rfl hl1 h2 h3

end CFSG.Quasithin.Vol2.Ch11.SecB
