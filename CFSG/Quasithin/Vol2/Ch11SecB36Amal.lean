module

public import CFSG.Quasithin.Vol2.Ch11SecB36F7
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Quasithin.Vol2.Ch11SecB36Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem isSylowTwoOf_QM (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n) :
    QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer (VM T L I : Set G))
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (VM T L I : Set G)) := by
  have hR := isTwoReducedIn_VM h1103 hyp
  have hTS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (L : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hyp.normal
  have hsub : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (VM T L I : Set G) ≤
      Subgroup.normalizer (L : Set G) := inf_le_left
  have hN : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer
      ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (VM T L I : Set G) :
        Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hR.2.1)
  have h := QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hTS hsub
    (Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer hsub).mpr hN))
  rwa [← inf_assoc, inf_eq_left.mpr hyp.normal] at h

theorem isTwoReducedIn_NQ (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n) :
    IsTwoReducedIn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VM T L I : Set G) : Subgroup G) : Set G)) (VM T L I) := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set W := VM T L I with hWdef
  set Q := T ⊓ Subgroup.centralizer (W : Set G) with hQdef
  set C := M ⊓ Subgroup.centralizer (W : Set G) with hCdef
  have hR := isTwoReducedIn_VM h1103 hyp
  have hWT := VM_le_T h1103 hyp
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := hyp.normal.trans hR.2.1
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hTW)
  have hMC : M ≤ Subgroup.normalizer (C : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hR.2.1)
  have hQ := isSylowTwoOf_QM h1103 hyp
  refine ⟨le_inf hR.1 (hWT.trans hTQ), inf_le_left.trans hR.2.1, hR.2.2.1,
    fun D hD hDN hD2 => ?_⟩
  have hDM : D ≤ M := hD.trans inf_le_left
  have hDC : D ≤ Subgroup.normalizer (C : Set G) := hDM.trans hMC
  have hEM : D ⊔ C ≤ M := sup_le hDM inf_le_left
  have hcN : ∀ c ∈ C, c ∈ Subgroup.normalizer ((D ⊔ C : Subgroup G) : Set G) := by
    intro c hc
    refine mem_normalizer_of_map_le ?_
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hMC hc.1)]
    refine sup_le ?_ le_sup_right
    rintro _ ⟨d, hd, rfl⟩
    have h1 : c * d * c⁻¹ * d⁻¹ ∈ C := by
      have : d * c⁻¹ * d⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hDC hd) c⁻¹).mp (C.inv_mem hc)
      have e : c * d * c⁻¹ * d⁻¹ = c * (d * c⁻¹ * d⁻¹) := by group
      rw [e]
      exact C.mul_mem hc this
    have e : (MulAut.conj c).toMonoidHom d = (c * d * c⁻¹ * d⁻¹) * d := by
      simp [MulAut.conj_apply]
    rw [e]
    exact (D ⊔ C).mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hd)
  have hMN : M ≤ Subgroup.normalizer ((D ⊔ C : Subgroup G) : Set G) := by
    intro m hm
    obtain ⟨c, hc, x, hx, rfl⟩ := exists_mul_of_frattini inf_le_left hMC hQ hm
    exact Subgroup.mul_mem _ (hcN c hc)
      (mem_normalizer_sup (hDN hx) (hMC hx.1))
  have hE2 : ∀ e ∈ D ⊔ C, ∃ k : ℕ, e ^ (2 ^ k) ∈ Subgroup.centralizer (W : Set G) := by
    intro e he
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D C hDC] at he
    obtain ⟨d, hd, c, hc, rfl⟩ := Set.mem_mul.mp he
    obtain ⟨k, hk⟩ := hD2 d hd
    refine ⟨k, ?_⟩
    set φ := conjHomL W (Subgroup.normalizer (W : Set G)) le_rfl with hφdef
    have hdN : d ∈ Subgroup.normalizer (W : Set G) := hR.2.1 (hDM hd)
    have hcN' : c ∈ Subgroup.normalizer (W : Set G) := hR.2.1 hc.1
    have hker : ∀ z (hz : z ∈ Subgroup.normalizer (W : Set G)),
        φ ⟨z, hz⟩ = 1 ↔ z ∈ Subgroup.centralizer (W : Set G) := by
      intro z hz
      rw [← MonoidHom.mem_ker, ker_conjHomL, Subgroup.mem_subgroupOf]
      exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
    have hdc : (⟨d * c, Subgroup.mul_mem _ hdN hcN'⟩ : ↥(Subgroup.normalizer (W : Set G))) =
        ⟨d, hdN⟩ * ⟨c, hcN'⟩ := rfl
    have hφc : φ ⟨c, hcN'⟩ = 1 := (hker c hcN').mpr hc.2
    have h1 : φ ⟨(d * c) ^ (2 ^ k), Subgroup.pow_mem _ (Subgroup.mul_mem _ hdN hcN') _⟩ =
        φ ⟨d ^ (2 ^ k), Subgroup.pow_mem _ hdN _⟩ := by
      rw [show (⟨(d * c) ^ (2 ^ k), Subgroup.pow_mem _ (Subgroup.mul_mem _ hdN hcN') _⟩ :
          ↥(Subgroup.normalizer (W : Set G))) = (⟨d, hdN⟩ * ⟨c, hcN'⟩) ^ (2 ^ k) from rfl,
        show (⟨d ^ (2 ^ k), Subgroup.pow_mem _ hdN _⟩ : ↥(Subgroup.normalizer (W : Set G))) =
          (⟨d, hdN⟩) ^ (2 ^ k) from rfl, map_pow, map_pow, map_mul, hφc, mul_one]
    refine (hker _ (Subgroup.pow_mem _ (Subgroup.mul_mem _ hdN hcN') _)).mp ?_
    rw [h1]
    exact (hker _ _).mpr hk
  exact le_sup_left.trans (hR.2.2.2 (D ⊔ C) hEM hMN hE2)

theorem amalgamHypV_VM (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (hyp : Hyp11 G T L I n) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) :
    AmalgamHypV ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (VM T L I : Set G) : Subgroup G) : Set G)) ⊔ H)
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (VM T L I : Set G) : Subgroup G) : Set G)) H T (VM T L I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set W := VM T L I with hWdef
  set Q := T ⊓ Subgroup.centralizer (W : Set G) with hQdef
  set G₁ := M ⊓ Subgroup.normalizer (Q : Set G) with hG₁def
  have hR := isTwoReducedIn_VM h1103 hyp
  have hWT := VM_le_T h1103 hyp
  have hLTW := sup_le_normalizer_VM hyp
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    le_normalizer_inf_centralizer h1102 hyp (le_conjClosure _ _) hLTW
  have hLTM : L ⊔ T ≤ M := sup_le Subgroup.le_normalizer hyp.normal
  have hLTG : L ⊔ T ≤ G₁ := le_inf hLTM hLTQ
  have hTG : T ≤ G₁ := le_sup_right.trans hLTG
  have hQ2 : IsPGroup 2 ↥Q := hyp.fsu.sylow.1.to_le inf_le_left
  have hQG : Q ≤ G₁ := inf_le_left.trans hTG
  have hWQ : W ≤ Q := le_inf hWT fun w hw => Subgroup.mem_centralizer_iff.mpr fun v hv =>
    B2F.isElemAbelian_comm hR.2.2.1 hv hw
  have hQO : Q ≤ pCoreOf 2 G₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQG inf_le_right hQ2
  have hO1 : pCoreOf 2 G₁ ≠ ⊥ := fun h => VM_ne_bot hyp (le_bot_iff.mp (h ▸ hWQ.trans hQO))
  refine ⟨⟨rfl, charTwo_of_inH hyp.fsu.qtke.2.1 (hyp.fsu.sylow.1.toSylow hyp.fsu.sylow.2)
      ⟨hTG, hO1⟩, isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTG,
      isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1, ?_⟩,
    isTwoReducedIn_NQ h1103 hyp, ?_⟩
  · by_contra hne
    have hN : G₁ ⊔ H ≤ Subgroup.normalizer (pCoreOf 2 (G₁ ⊔ H) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    exact hH.2.1 ((le_sup_right.trans hN).trans (normalizer_le_of_isPGroup h331 hyp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hne ((hLTG.trans le_sup_left).trans hN)))
  · have hQS : QuasithinUnique.IsSylowTwoOf Q (G₁ ⊓ Subgroup.centralizer (W : Set G)) :=
      F7.isSylowTwoOf_mono_right (isSylowTwoOf_QM h1103 hyp) (le_inf hQG inf_le_right)
        (inf_le_inf_right _ inf_le_left)
    refine le_antisymm ?_ (B6.pCoreOf_two_le_of_isSylowTwoOf hQS)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hQG inf_le_right)
      (inf_le_left.trans inf_le_right) hQ2

theorem wClos_VM_not_le (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (hyp : Hyp11 G T L I n) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hclaim : ∀ g : G, conjSubgroup (VM T L I) g ≤ T →
      ⁅VM T L I, conjSubgroup (VM T L I) g⁆ ≠ ⊥ →
        ¬ VM T L I ≤ Subgroup.normalizer (conjSubgroup (VM T L I) g : Set G)) :
    ¬ E3.wClos (VM T L I) 0 T ≤ pCoreOf 2 H := by
  intro hW
  obtain ⟨g, hgT, hne, hN⟩ := exists_conj_commutator_of_amalgam
    (amalgamHypV_VM h331 h1102 h1103 hyp hH) (VM_ne_bot hyp) hW
  exact hclaim g hgT hne hN

end CFSG.Quasithin.Vol2.Ch11.SecB
