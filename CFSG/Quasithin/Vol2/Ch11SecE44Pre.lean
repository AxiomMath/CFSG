module

public import CFSG.Quasithin.Vol2.Ch11SecB35
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Vol2.Ch11SecE43Pre

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem kOf_eq_of_cComp' {L V₁ V₀ K₁ : Subgroup G} (hLK : LOf L V₁ ≤ K₁)
    (hK₁ : quasithinIsCComponent K₁ (Subgroup.normalizer (V₀ : Set G)))
    (hN : Subgroup.normalizer (V₀ : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hL₁ : LOf L V₁ ≠ ⊥) : KOf L V₁ V₀ = K₁ := by
  have hK₁G : K₁ ≤ Subgroup.normalizer (V₀ : Set G) := A3.subnormal_le hK₁.2.2.1
  refine le_antisymm
    (conjClosure_le fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hN hg) x).mp (hLK hx)) ?_
  have hK'le : conjClosure (LOf L V₁) K₁ ≤ K₁ :=
    conjClosure_le fun g hg x hx => K₁.mul_mem (K₁.mul_mem hg (hLK hx)) (K₁.inv_mem hg)
  have hsub : IsSubnormal (conjClosure (LOf L V₁) K₁) (Subgroup.normalizer (V₀ : Set G)) :=
    IsSubnormal.step hK'le ((Subgroup.normal_subgroupOf_iff_le_normalizer hK'le).mpr
      (le_normalizer_conjClosure _ _)) hK₁.2.2.1
  have hK'1 : conjClosure (LOf L V₁) K₁ ≠ ⊥ := fun h =>
    hL₁ (le_bot_iff.mp (h ▸ le_conjClosure _ _))
  have hK'eq : conjClosure (LOf L V₁) K₁ = K₁ := by
    by_contra hne
    exact hK₁.2.2.2 _ (lt_of_le_of_ne hK'le hne) hK'1
      (SecD.conjClosure_perfect (perfectCore_perfect _)) hsub
  rw [← hK'eq]
  exact conjClosure_mono le_rfl hK₁G

theorem lOf_mem_cComp_centralizer (hF : Facts43) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1142 : Stmt11_4_2) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hKL : KOf L V₁ V₁ = LOf L V₁) {z : G}
    (hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (hz1 : z ≠ 1) :
    LOf L V₁ ∈ cComp (Subgroup.centralizer ({z} : Set G)) := by
  have hz2 : z ^ 2 = 1 := (SecA.isElemAbelian_fsuV h).2 z hz.1
  have hzV₁ := mem_V₁_of_mem_centralizer hF h1102 h hcV hV₁ hz.1 hz.2
  have hN := normalizer_zpowers_eq_centralizer hz2
  have hTz : T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun t ht => by
    rw [hN]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz.2 t ht)
  have hsyl : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (Subgroup.zpowers z : Set G))
      (Subgroup.normalizer (Subgroup.zpowers z : Set G)) := by
    rw [inf_eq_left.mpr hTz]
    exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz
  have hz0 : Subgroup.zpowers z ≠ ⊥ := fun h0 =>
    hz1 (Subgroup.mem_bot.mp (h0 ▸ Subgroup.mem_zpowers z))
  obtain ⟨K₀, hLK₀, hK₀, hNK₀, -⟩ := h1111 G T L I n 1 V₁ (Subgroup.zpowers z) h hV₁
    (Or.inl ⟨rfl, hz0, (Subgroup.zpowers_le).mpr hzV₁, hsyl⟩)
  have heq := kOf_eq_of_cComp' hLK₀ hK₀ hNK₀ (SecD.lOf_ne_bot h1110 h hV₁)
  rw [h1142 G T L I n V₁ h hV₁ z hz hz1, hKL] at heq
  rw [heq, mem_cComp_iff, ← hN]
  exact hK₀

theorem commutator_le_of_cComp (hK : QuasithinUnique.LocalSQTK G)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) {Gz H I L₁ T : Subgroup G}
    (hGz : pCoreOf 2 Gz ≠ ⊥) (hT : QuasithinUnique.IsSylowTwoOf T Gz) (hHGz : H ≤ Gz)
    (hTH : T ≤ H) (hI : I ∈ cComp H) (hL₁ : L₁ ∈ cComp Gz) (hIL : ¬ I ≤ L₁) :
    ⁅L₁, I⁆ ≤ pCoreOf 2 L₁ := by
  obtain ⟨I₁, hI₁, hII₁⟩ := QuasithinUnique.Vol2Native.lemma_1_2_4_exists hK h37 h39 hGz hT
    ((le_of_mem_cComp hI).trans hHGz) (cComp_subset_lFamily hTH hI)
  have hne : L₁ ≠ I₁ := fun he => hIL (he ▸ hII₁)
  exact (Subgroup.commutator_mono le_rfl hII₁).trans
    ((QuasithinUnique.Vol2Native.lemma_1_2_1_two hK h37 hGz hL₁ hI₁ hne).1.trans inf_le_left)

theorem le_sectionCentralizer_of_le {H I T L₁ B : Subgroup G} (hHI : H = I ⊔ T)
    (hIp : ⁅I, I⁆ = I) (hT2 : IsPGroup 2 T) (hHL : H ≤ Subgroup.normalizer (L₁ : Set G))
    (hIL : ⁅L₁, I⁆ ≤ pCoreOf 2 L₁) (hBH : B ≤ H) (hBodd : Odd (Nat.card B)) :
    B ≤ sectionCentralizer L₁ (pCoreOf 2 L₁) := by
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 L₁ : Set G) :=
    hHL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L₁)
  have hISC : I ≤ sectionCentralizer L₁ (pCoreOf 2 L₁) := by
    intro i hi
    have hiH : i ∈ H := hHI ▸ Subgroup.mem_sup_left hi
    refine ⟨hHL hiH, hHO hiH, fun l hl => ?_⟩
    have h1 := hIL (Subgroup.commutator_mem_commutator hl hi)
    rw [commutatorElement_def] at h1
    have e : i * l * i⁻¹ * l⁻¹ = (l * i * l⁻¹ * i⁻¹)⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 L₁).inv_mem h1
  have hO2 := SecB.oTwoUpper_eq_conjClosure hIp hT2 hHI
  intro b hb
  have hbO : b ∈ oTwoUpper H := by
    refine Subgroup.subset_closure ⟨hBH hb, ?_⟩
    have hd : orderOf b ∣ Nat.card B := by
      have := Subgroup.orderOf_dvd_natCard B hb
      exact this
    exact hBodd.of_dvd_nat hd
  rw [hO2] at hbO
  refine (conjClosure_le fun h hh x hx => ?_) hbO
  exact (Subgroup.mem_normalizer_iff.mp
    (SecD.mem_normalizer_sectionCentralizer (hHL hh) (hHO hh)) x).mp (hISC hx)

theorem le_normalizer_fsuV_of_le (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n) {B : Subgroup G}
    {z : G} (hzV : z ∈ fsuV T I) (hz1 : z ≠ 1) (hBM : B ≤ Subgroup.normalizer (L : Set G))
    (hBz : B ≤ Subgroup.centralizer ({z} : Set G)) :
    B ≤ Subgroup.normalizer (fsuV T I : Set G) := fun _ hb =>
  SecA.mem_normalizer_of_isTISetIn (h1103 G T L I n h).2.2.2.1 ((Subgroup.zpowers_le).mpr hzV)
    (fun h0 => hz1 (Subgroup.mem_bot.mp (h0 ▸ Subgroup.mem_zpowers z))) (hBM hb)
    (centralizer_le_normalizer_zpowers z (hBz hb))

end CFSG.Quasithin.Vol2.Ch11.SecE
