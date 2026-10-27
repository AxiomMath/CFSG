module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvFact
public import CFSG.Quasithin.Vol2.Ch10SecB5Ev

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem inGzero_data (h : MaxCtx T L I t Ψ c) :
    XOf T L Ψ A ≤ conjClosure (XOf T L Ψ A)
        (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) ∧
      Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) ≤
        Subgroup.normalizer (conjClosure (XOf T L Ψ A)
          (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) : Set G) ∧
      IsSylowTwoOf (T ⊓ conjClosure (XOf T L Ψ A)
          (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
        (conjClosure (XOf T L Ψ A)
          (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T))) := by
  set G₀ := Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) with hG₀
  set X := XOf T L Ψ A with hXdef
  have hTG₀ : T ≤ G₀ := le_sup_right.trans le_sup_right
  have hXG₀ : X ≤ G₀ := (oTwoUpper_le _).trans le_sup_right
  have hT : IsSylowTwoOf T G₀ :=
    ⟨hTG₀, h.hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le h.hyp.fsu.sylow hTG₀⟩
  have hKG₀ : conjClosure X G₀ ≤ G₀ := conjClosure_le fun g hg x hx =>
    G₀.mul_mem (G₀.mul_mem hg (hXG₀ hx)) (G₀.inv_mem hg)
  exact ⟨le_conjClosure X G₀, le_normalizer_conjClosure X G₀,
    B6.isSylowTwoOf_inf_normal hT hKG₀ (le_normalizer_conjClosure X G₀)⟩

theorem normalizer_T1_le_XOf_Lk2 (hF : Fact10_2_5Lk2) (h : MaxCtx T L I t Ψ c)
    (hD : ParData A K E) {k : ℕ} (hk : k = 4 ∨ k = 5)
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (↥(conjClosure (XOf T L Ψ A)
          (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T))) ⧸
        CFSG.pCore 2 ↥(conjClosure (XOf T L Ψ A)
          (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))) .PSL k 2 1)
    (haut : Nonempty (↥(conjClosure (XOf T L Ψ A)
          (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) ⊔ T) ⧸
        CFSG.pCore 2 ↥(conjClosure (XOf T L Ψ A)
          (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) ⊔ T) ≃*
      MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2)))) :
    Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
  obtain ⟨hXK, hG₀K, hS⟩ := inGzero_data h (A := A)
  have hTN := (le_sup_right.trans le_sup_right).trans hG₀K
  obtain ⟨hwc, h3⟩ := hF G _ T _ k hk hmod h.hyp.fsu.sylow.1 hTN hS haut hXK
    (isXi_XOf h hD).2.1 (oTwoUpper_oTwoUpper' _) (relIndex_XOf h hD)
    (fun x hx => pow_three_mem h hD hx)
  exact normalizer_T1_le_of_weakClosed h hD hXK hS (le_sup_left.trans hG₀K) hwc h3

end CFSG.Quasithin.Vol2.Ch10.SecB
