module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L612
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L64
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.L84
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T85.Hat
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T85.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6Base

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T85

section Generic

variable {G : Type*} [Group G]

theorem sup_le_centralizer_sup {A B C D : Subgroup G} (h₁ : A ≤ Subgroup.centralizer (C : Set G))
    (h₂ : A ≤ Subgroup.centralizer (D : Set G)) (h₃ : B ≤ Subgroup.centralizer (C : Set G))
    (h₄ : B ≤ Subgroup.centralizer (D : Set G)) :
    A ⊔ B ≤ Subgroup.centralizer ((C ⊔ D : Subgroup G) : Set G) := by
  refine sup_le (Subgroup.le_centralizer_iff.mpr (sup_le ?_ ?_))
    (Subgroup.le_centralizer_iff.mpr (sup_le ?_ ?_))
  · exact Subgroup.le_centralizer_iff.mp h₁
  · exact Subgroup.le_centralizer_iff.mp h₂
  · exact Subgroup.le_centralizer_iff.mp h₃
  · exact Subgroup.le_centralizer_iff.mp h₄

theorem isDirectProduct_of_commute {S : Set (Subgroup G)} {W : Subgroup G}
    (hcomm : ∀ J ∈ S, ∀ L ∈ S, J ≠ L → ∀ x ∈ J, ∀ y ∈ L, Commute x y)
    (hsup : sSup S = W) (hZ : zOf W = ⊥) : IsDirectProduct S W where
  commute := hcomm
  sSup_eq := hsup
  indep := by
    intro J hJ
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxJ, hxS⟩ := Subgroup.mem_inf.mp hx
    have hcent : ∀ Y ∈ S, ∀ y ∈ Y, x * y = y * x := by
      intro Y hY y hy
      by_cases hYJ : Y = J
      · subst hYJ
        have hle : sSup (S \ {Y}) ≤ Subgroup.centralizer (Y : Set G) := by
          refine sSup_le fun Z hZ' z hz => Subgroup.mem_centralizer_iff.mpr fun y' hy' => ?_
          exact (hcomm Y hY Z hZ'.1 (fun h => hZ'.2 h.symm) y' hy' z hz).eq
        exact (Subgroup.mem_centralizer_iff.mp (hle hxS) y hy).symm
      · exact (hcomm J hJ Y hY (fun h => hYJ h.symm) x hxJ y hy).eq
    have hsub : sSup (S \ {J}) ≤ sSup S := sSup_le_sSup Set.sdiff_subset
    have hxW : x ∈ W := hsup ▸ hsub hxS
    have hxz : x ∈ zOf W := by
      refine mem_zOf_iff.mpr ⟨hxW, fun w hw => ?_⟩
      have hle : sSup S ≤ Subgroup.centralizer ({x} : Set G) := by
        refine sSup_le fun Y hY y hy => ?_
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcent Y hY y hy).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hsup ▸ hw))
    rw [hZ] at hxz
    exact hxz

end Generic

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E K : Subgroup G}

theorem commute_wK
    (h : Counterexample p A θ) (hB : TypeB p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ lcal (thetaOf θ F)) (h₂ : K₂ ∈ lcal (thetaOf θ F)) (hne : K₁ ≠ K₂) :
    ∀ x ∈ wK θ E K₁, ∀ y ∈ wK θ E K₂, Commute x y := by
  have hBc := hB.toTypeBCore
  have hind : lcal (thetaOf θ F) = Ind (thetaOf θ F) :=
    (Counterexample.ind_eq_lcal_line_of_typeB h hBc hF hFE).symm
  have c1 : K₁ ≤ Subgroup.centralizer (K₂ : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      ((Counterexample.isRegFam_line_of_typeB h hBc hF hFE).isDirectProduct.commute K₁ h₁ K₂ h₂
        hne x hx y hy).eq.symm
  have c2 : lHat (thetaOf θ E) (K₁ ⊓ Subgroup.centralizer (E : Set G)) ≤
      Subgroup.centralizer (K₂ : Set G) :=
    h.lemma_8_4 hB hF hFE (inf_centralizer_mem_ind_plane h hBc hF hFE h₁) (hind ▸ h₂)
      (inf_centralizer_ne h hBc hF hFE h₂ h₁ hne.symm)
  have c4 : lHat (thetaOf θ E) (K₂ ⊓ Subgroup.centralizer (E : Set G)) ≤
      Subgroup.centralizer (K₁ : Set G) :=
    h.lemma_8_4 hB hF hFE (inf_centralizer_mem_ind_plane h hBc hF hFE h₂) (hind ▸ h₁)
      (inf_centralizer_ne h hBc hF hFE h₁ h₂ hne)
  have c6 : lHat (thetaOf θ E) (K₁ ⊓ Subgroup.centralizer (E : Set G)) ≤
      Subgroup.centralizer
        (lHat (thetaOf θ E) (K₂ ⊓ Subgroup.centralizer (E : Set G)) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (commute_lHat h hBc hF hFE h₁ h₂ hne x hx y hy).eq.symm
  have c3 : K₁ ≤ Subgroup.centralizer
      (lHat (thetaOf θ E) (K₂ ⊓ Subgroup.centralizer (E : Set G)) : Set G) :=
    Subgroup.le_centralizer_iff.mp c4
  have hle : wK θ E K₁ ≤ Subgroup.centralizer (wK θ E K₂ : Set G) :=
    sup_le_centralizer_sup c1 c3 c2 c6
  exact fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

theorem wK_injOn
    (h : Counterexample p A θ) (hB : TypeB p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ lcal (thetaOf θ F)) (h₂ : K₂ ∈ lcal (thetaOf θ F))
    (heq : wK θ E K₁ = wK θ E K₂) : K₁ = K₂ := by
  by_contra hne
  have hc := commute_wK h hB hF hFE h₁ h₂ hne
  rw [← heq] at hc
  refine (mem_lcal_iff.mp h₁).2.2.2 (isMulCommutative_iff.mpr fun a b => ?_)
  exact Subtype.ext (hc a (le_sup_left (a := K₁) a.2) b (le_sup_left (a := K₁) b.2)).eq

theorem map_conj_wK (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) {a : G} (ha : a ∈ A)
    (K' : Subgroup G) :
    (wK θ E K').map (MulAut.conj a).toMonoidHom =
      wK θ E (K'.map (MulAut.conj a).toMonoidHom) := by
  unfold wK
  rw [Subgroup.map_sup, map_conj_lHat (h.isFunctor.normalizes_thetaOf hB.mem.1 ha),
    Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective,
    Near.Lemma212.map_conj_centralizer_of_commute E
      (fun b hb => h.comm_of_mem_A (hB.mem.1 hb) ha)]

theorem lHat_le_kOf
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) (L : Subgroup G) :
    lHat (thetaOf θ E) L ≤ kOf (thetaOf θ E) := by
  rw [← (isDirectProduct_lcal_kOf
    (h.sol_thetaOf hB.mem.1 (h.ne_bot_of_mem_E1 hB.mem))).sSup_eq]
  exact sSup_le_sSup fun R hR => hR.1

theorem maximal_thetaOf_line (h : Counterexample p A θ) (hB : TypeB p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    Maximal (· ∈ Msig p A θ) (thetaOf θ F) := by
  obtain ⟨a, ha, ha1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  exact hB.maximal a ha fun haE => hFE (h.line_eq_zpowers hB.mem haE ha1).symm

theorem not_kOf_le
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    ¬ kOf (thetaOf θ E) ≤ thetaOf θ F := by
  intro hle
  have hΩ := Counterexample.isRegFam_ind_E_of_typeB h hB
  obtain ⟨Q, hQ⟩ := hΩ.nonempty
  obtain ⟨R, hR, hRQ⟩ := exists_le_of_mem_ind_E h hB hQ
  obtain ⟨f, hf, hf1⟩ := h.exists_ne_one_of_mem_E1 hF
  have hRk : R ≤ kOf (thetaOf θ E) := by
    rw [← (isDirectProduct_lcal_kOf
      (h.sol_thetaOf hB.mem.1 (h.ne_bot_of_mem_E1 hB.mem))).sSup_eq]
    exact le_sSup hR
  have hfQ : Q.map (MulAut.conj f).toMonoidHom ∈ Ind (thetaOf θ E) :=
    map_conj_mem_ind_E h hB hF.1 f hf Q hQ
  have hdisj : Disjoint Q (Q.map (MulAut.conj f).toMonoidHom) :=
    hΩ.isDirectProduct.indep.pairwiseDisjoint hQ hfQ
      (map_conj_ne_ind_E h hB hF hFE f hf hf1 Q hQ).symm
  have hR1 : ∀ x ∈ R, x = 1 := by
    intro x hx
    have hxF : x ∈ thetaOf θ F := hle (hRk hx)
    have hcomm : f * x = x * f :=
      Subgroup.mem_centralizer_iff.mp (h.isFunctor.thetaOf_le_centralizer hF.1 hxF) f hf
    have hxQ : x ∈ Q.map (MulAut.conj f).toMonoidHom :=
      ⟨x, hRQ hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcomm]; group⟩
    exact Subgroup.mem_bot.mp (disjoint_iff.mp hdisj ▸ Subgroup.mem_inf.mpr ⟨hRQ hx, hxQ⟩)
  refine (mem_lcal_iff.mp hR).2.2.2 (isMulCommutative_iff.mpr fun a b => ?_)
  exact Subtype.ext (by simp only [Subgroup.coe_mul]; rw [hR1 _ a.2, hR1 _ b.2])

theorem sSup_msig_eq
    (h : Counterexample p A θ) (hB : TypeB p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    sSup (Msig p A θ) = thetaOf θ F ⊔ kOf (thetaOf θ E) := by
  have hHF : thetaOf θ F ∈ Msig p A θ := h.thetaOf_mem_msig hF.1 (h.ne_bot_of_mem_E1 hF)
  have hKE : kOf (thetaOf θ E) ∈ Msig p A θ :=
    kOf_mem_msig (h.thetaOf_mem_msig hB.mem.1 (h.ne_bot_of_mem_E1 hB.mem))
  have hT : ({thetaOf θ F, kOf (thetaOf θ E)} : Set (Subgroup G)) ⊆ Msig p A θ := by
    rintro _ (rfl | rfl)
    exacts [hHF, hKE]
  have hX : sSup ({thetaOf θ F, kOf (thetaOf θ E)} : Set (Subgroup G)) =
      thetaOf θ F ⊔ kOf (thetaOf θ E) := sSup_pair
  refine le_antisymm ?_ (sup_le (le_sSup hHF) (le_sSup hKE))
  rcases h.lemma_6_12 ⟨_, hT, rfl⟩ with ⟨hall, -⟩ | ⟨hXM, -⟩
  · exact hX ▸ sSup_le hall
  · exfalso
    have hle : kOf (thetaOf θ E) ≤ thetaOf θ F :=
      (le_sSup (show kOf (thetaOf θ E) ∈ ({thetaOf θ F, kOf (thetaOf θ E)} : Set (Subgroup G)) from
        Or.inr rfl)).trans ((maximal_thetaOf_line h hB hF hFE).2 hXM
          (le_sSup (show thetaOf θ F ∈ ({thetaOf θ F, kOf (thetaOf θ E)} : Set (Subgroup G)) from
            Or.inl rfl)))
    exact not_kOf_le h hB.toTypeBCore hF hFE hle

theorem sSup_wK_eq
    (h : Counterexample p A θ) (hB : TypeBCore p A θ E K) {F : Subgroup G}
    (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    sSup {Y | ∃ K' ∈ lcal (thetaOf θ F), Y = wK θ E K'} =
      thetaOf θ F ⊔ kOf (thetaOf θ E) := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨K', hK', rfl⟩
    exact sup_le_sup (lcal_le hK') (lHat_le_kOf h hB _)
  · refine sup_le ?_ ?_
    · refine le_trans (Counterexample.isRegFam_line_of_typeB h hB hF hFE).isDirectProduct.sSup_eq.ge
        (sSup_le fun K' hK' => le_sSup_of_le ⟨K', hK', rfl⟩ le_sup_left)
    · refine le_trans (isDirectProduct_lcal_kOf
        (h.sol_thetaOf hB.mem.1 (h.ne_bot_of_mem_E1 hB.mem))).sSup_eq.ge
        (sSup_le fun R hR => ?_)
      obtain ⟨Q, hQ, hRQ⟩ := exists_mem_ind_E_ge h hB hR
      obtain ⟨K', hK', heq⟩ := exists_inf_centralizer_eq_smear h hB hF hFE hQ
      exact le_sSup_of_le ⟨K', hK', rfl⟩ (le_trans
        (le_lHat_of_mem_conjOrbit h hB hF hFE hQ heq (RegFam.self_mem_conjOrbit Q F) hR hRQ)
        le_sup_right)

end T85

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
