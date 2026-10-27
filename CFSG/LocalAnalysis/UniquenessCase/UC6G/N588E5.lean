module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588E4
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.ABGLocalTools
open CFSG.GorensteinWalter (IsComponentOf generalizedFittingSubgroupOf componentLayerOf)
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem derivedSeries_Hbar_perfect :
    ⁅derivedSeries m.Hbar (Nat.card ↥m.H), derivedSeries m.Hbar (Nat.card ↥m.H)⁆ =
      derivedSeries m.Hbar (Nat.card ↥m.H) := by
  rw [← derivedSeries_succ]
  exact N588.derivedSeries_succ_eq_of_card_le
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective m.OH))

theorem le_derivedSeries_of_perfect {K : Subgroup m.Hbar} (hK : ⁅K, K⁆ = K) (n : ℕ) :
    K ≤ derivedSeries m.Hbar n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ]
    calc K = ⁅K, K⁆ := hK.symm
      _ ≤ ⁅derivedSeries m.Hbar n, derivedSeries m.Hbar n⁆ := Subgroup.commutator_mono ih ih

theorem bar_inftyOf : m.bar (inftyOf m.H) = derivedSeries m.Hbar (Nat.card ↥m.H) := by
  rw [bar, inftyOf, ← map_derivedSeries_eq (QuotientGroup.mk'_surjective m.OH)]
  congr 1
  exact Subgroup.comap_map_eq_self_of_injective m.H.subtype_injective _

theorem L_le_inftyOf : m.L ≤ inftyOf m.H :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem rCoreL_le_OHG : N588.rCore m.r m.L ≤ m.OHG := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hle : N588.rCore m.r m.L ≤ m.H := (N588.rCore_le _ _).trans m.L_le_H
  have hn : ((N588.rCore m.r m.L).subgroupOf m.H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 m.H_le_normalizer_rCoreL
  have hcop : Nat.Coprime m.r (Nat.card ((N588.rCore m.r m.L).subgroupOf m.H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact N588.coprime_card_rCore m.r m.L
  have h1 : (N588.rCore m.r m.L).subgroupOf m.H ≤ m.OH := le_sSup ⟨hn, hcop⟩
  intro x hx
  exact ⟨⟨x, hle hx⟩, h1 hx, rfl⟩

variable (hKM : UCK.KMult) (hK3 : UCK.KMult3) (h69 : R6_9 Dat)
include hKM hK3 h69

theorem derivedSeries_le_component (hSch : UCK.KSch) {K : Subgroup m.Hbar}
    (hK : IsComponentOf K ⊤) : derivedSeries m.Hbar (Nat.card ↥m.H) ≤ K := by
  haveI hKn := m.component_normal hKM hK3 h69 hK
  set D := derivedSeries m.Hbar (Nat.card ↥m.H) with hD
  set C := centralizer (K : Set m.Hbar) with hC
  have hDperf : ⁅D, D⁆ = D := m.derivedSeries_Hbar_perfect
  have hDK : D ≤ normalizer (K : Set m.Hbar) := le_top.trans (normalizer_eq_top (H := K)).ge
  have hKk : CFSG.Open.IsKGroup ↥K := m.isKGroup_Hbar.subgroup K
  obtain ⟨φ, hφ⟩ := N588.exists_inner_of_schreier hSch hK.2.2 hKk hDK hDperf
  have hc := m.center_component_eq_bot hKM hK3 h69 hK
  have hDKC : D ≤ K ⊔ C := by
    intro ℓ hℓ
    obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective (φ ⟨ℓ, hℓ⟩)
    have hcomm : ∀ k ∈ K, ℓ * k * ℓ⁻¹ = (k₀ : m.Hbar) * k * (k₀ : m.Hbar)⁻¹ := by
      intro k hk
      have h1 := hφ ⟨ℓ, hℓ⟩ ⟨k, hk⟩
      rw [← hk₀, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        QuotientGroup.eq, hc, mem_bot] at h1
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one,
        Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      calc ℓ * k * ℓ⁻¹ = ℓ * k * ℓ⁻¹ * ((ℓ * k * ℓ⁻¹)⁻¹ * ((k₀ : m.Hbar) * k *
            (k₀ : m.Hbar)⁻¹)) := by rw [h2, mul_one]
        _ = (k₀ : m.Hbar) * k * (k₀ : m.Hbar)⁻¹ := by group
    have hcent : (k₀ : m.Hbar)⁻¹ * ℓ ∈ C := by
      rw [hC, mem_centralizer_iff]
      intro k hk
      have h1 := hcomm k hk
      calc k * ((k₀ : m.Hbar)⁻¹ * ℓ)
          = (k₀ : m.Hbar)⁻¹ * ((k₀ : m.Hbar) * k * (k₀ : m.Hbar)⁻¹) * ℓ := by group
        _ = (k₀ : m.Hbar)⁻¹ * (ℓ * k * ℓ⁻¹) * ℓ := by rw [h1]
        _ = (k₀ : m.Hbar)⁻¹ * ℓ * k := by group
    have : ℓ = (k₀ : m.Hbar) * ((k₀ : m.Hbar)⁻¹ * ℓ) := by group
    rw [this]
    exact mul_mem_sup k₀.2 hcent
  set J := K ⊔ C with hJ
  haveI hK'n : (K.subgroupOf J).Normal := Subgroup.normal_subgroupOf
  haveI hCs : Group.IsSolvable ↥C := m.isSolvable_centralizer_component hKM hK3 h69 hK
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (K.subgroupOf J)).comp (Subgroup.inclusion (le_sup_right : C ≤ J))) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨k, hk, c, hcC, hx⟩ := (mem_sup_of_normal_left (s := K) (t := C)).mp x.2
    refine ⟨⟨c, hcC⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have : (Subgroup.inclusion (le_sup_right : C ≤ J) ⟨c, hcC⟩)⁻¹ * x =
        ⟨c⁻¹ * k * c, J.mul_mem (J.mul_mem (J.inv_mem (mem_sup_right hcC)) (mem_sup_left hk))
          (mem_sup_right hcC)⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hx]
      group
    rw [this]
    show c⁻¹ * k * c ∈ K
    exact hKn.conj_mem' k hk c
  haveI : Group.IsSolvable (↥J ⧸ K.subgroupOf J) := Group.isSolvable_of_surjective hsurj
  have hψ := N588.eq_one_of_perfect_of_isSolvable (N588.commutator_eq_top_of_perfect hDperf)
    ((QuotientGroup.mk' (K.subgroupOf J)).comp (Subgroup.inclusion hDKC))
  intro ℓ hℓ
  have h1 := congrArg (fun f => f ⟨ℓ, hℓ⟩) hψ
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.one_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem bar_L_eq (hSch : UCK.KSch) {K : Subgroup m.Hbar} (hK : IsComponentOf K ⊤) :
    m.bar m.L = K := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI hKs := m.isSimpleGroup_component hKM hK3 h69 hK
  have hD := m.derivedSeries_le_component hKM hK3 h69 hSch hK
  have hLK : m.bar m.L ≤ K :=
    ((m.bar_mono m.L_le_inftyOf).trans m.bar_inftyOf.le).trans hD
  have hKperf : ⁅K, K⁆ = K := N588.commutator_self_eq_of_perfect hK.2.2.2.1
  have hKD : K ≤ m.bar (inftyOf m.H) := by
    rw [m.bar_inftyOf]
    exact m.le_derivedSeries_of_perfect hKperf _
  have hLn : (m.bar m.L).Normal := by
    have h1 : (m.L.subgroupOf m.H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer m.L_le_H).2 m.H_le_normalizer_L
    exact h1.map _ (QuotientGroup.mk'_surjective m.OH)
  have hL1 : m.bar m.L ≠ ⊥ := by
    intro hbot
    have hnd : ¬ m.r ∣ Nat.card ((inftyOf m.H).subgroupOf m.H) := by
      intro hd
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' m.r hd
      have hxL : ((x : ↥m.H) : G) ∈ m.L := Subgroup.subset_closure
        ⟨x.2, 1, by rw [pow_one, ← hx, Subgroup.orderOf_coe, Subgroup.orderOf_coe]⟩
      have h1 : m.piH (x : ↥m.H) ∈ m.bar m.L := m.mem_bar_of_mem hxL
      rw [hbot, mem_bot] at h1
      have h2 : (x : ↥m.H) ∈ m.OH := (QuotientGroup.eq_one_iff _).1 h1
      have h3 : orderOf (x : ↥m.H) ∣ Nat.card m.OH := Subgroup.orderOf_dvd_natCard _ h2
      rw [Subgroup.orderOf_coe, hx] at h3
      exact (Nat.Prime.coprime_iff_not_dvd m.hr).1 CFSG.pPrimeCore_coprime_card h3
    have hn : ((inftyOf m.H).subgroupOf m.H).Normal := by
      have h1 : (inftyOf m.H).subgroupOf m.H = derivedSeries ↥m.H (Nat.card ↥m.H) :=
        Subgroup.comap_map_eq_self_of_injective m.H.subtype_injective _
      rw [h1]
      infer_instance
    have hle : (inftyOf m.H).subgroupOf m.H ≤ m.OH :=
      le_sSup ⟨hn, (Nat.Prime.coprime_iff_not_dvd m.hr).2 hnd⟩
    have hbar : m.bar (inftyOf m.H) = ⊥ := by
      rw [bar, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_bot).2 ((QuotientGroup.eq_one_iff x).2 (hle hx))
    have hK1 : K = ⊥ := le_bot_iff.1 (hbar ▸ hKD)
    subst hK1
    obtain ⟨a, b, hab⟩ := hK.2.2.1.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  haveI : ((m.bar m.L).subgroupOf K).Normal := Subgroup.normal_subgroupOf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((m.bar m.L).subgroupOf K) with h | h
  · exfalso
    apply hL1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hLK hx⟩ : ↥K) ∈ (m.bar m.L).subgroupOf K := hx
    rw [h, mem_bot] at this
    exact (mem_bot).2 (congrArg Subtype.val this)
  · refine le_antisymm hLK fun x hx => ?_
    have : (⟨x, hx⟩ : ↥K) ∈ (m.bar m.L).subgroupOf K := h ▸ mem_top _
    exact this

theorem nonempty_mulEquiv_Lbar (hSch : UCK.KSch) {K : Subgroup m.Hbar}
    (hK : IsComponentOf K ⊤) : Nonempty (m.Lbar ≃* ↥K) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  let ψ : ↥m.L →* m.Hbar := m.piH.comp (Subgroup.inclusion m.L_le_H)
  have hincl : (Subgroup.inclusion m.L_le_H).range = m.L.subgroupOf m.H := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hrange : ψ.range = K := by
    rw [MonoidHom.range_comp, hincl, ← m.bar_L_eq hKM hK3 h69 hSch hK]
    rfl
  have hker : ψ.ker = CFSG.pPrimeCore m.r ↥m.L := by
    refine le_antisymm ?_ ?_
    ·
      refine le_sSup ⟨MonoidHom.normal_ker ψ, ?_⟩
      have hmap : (ψ.ker).map m.L.subtype ≤ m.OHG := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨Subgroup.inclusion m.L_le_H x,
          (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx), rfl⟩
      have hdvd : Nat.card ψ.ker ∣ Nat.card m.OH := by
        have h1 := Subgroup.card_dvd_of_le hmap
        rwa [Subgroup.card_map_of_injective m.L.subtype_injective, OHG,
          Subgroup.card_map_of_injective m.H.subtype_injective] at h1
      exact Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card
    · intro x hx
      rw [MonoidHom.mem_ker]
      have hxO : ((x : ↥m.L) : G) ∈ m.OHG := m.rCoreL_le_OHG ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hxO
      have : Subgroup.inclusion m.L_le_H x = y := Subtype.ext hyx.symm
      show m.piH (Subgroup.inclusion m.L_le_H x) = 1
      rw [this]
      exact (QuotientGroup.eq_one_iff y).2 hy
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem isSimpleGroup_Lbar_of_inputs (hSch : UCK.KSch) : IsSimpleGroup m.Lbar := by
  obtain ⟨K, hK⟩ := m.exists_component h69
  obtain ⟨e⟩ := m.nonempty_mulEquiv_Lbar hKM hK3 h69 hSch hK
  haveI := m.isSimpleGroup_component hKM hK3 h69 hK
  exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance

theorem c619_of_inputs (hSch : UCK.KSch) : m.C619 := by
  obtain ⟨K, hK⟩ := m.exists_component h69
  obtain ⟨y, hyR, hyK, hy1, hyr⟩ := m.exists_mem_component h69 hK
  obtain ⟨b, hbA, rfl⟩ := m.mem_bar_A_of_pow h69 hyR hyr
  have hW := m.H_eq_sup_of (m.pre_le_H K)
    (m.H_le_normalizer_pre (m.component_normal hKM hK3 h69 hK)) (t := (b : G))
    ((m.mem_pre).2 ⟨b.2, hyK⟩) hbA fun hbZ =>
      hy1 (m.bar_Z_inf_component hKM hK3 h69 hK (m.mem_bar_of_mem hbZ) hyK)
  have hpre : m.pre K ≤ m.L ⊔ m.OHG := by
    have h1 := m.pre_bar_le m.L_le_H
    rwa [m.bar_L_eq hKM hK3 h69 hSch hK] at h1
  have hOHG : m.OHG ≤ m.H ⊓ m.M := le_inf (map_subtype_le _) m.OHG_le_M
  show m.H = m.L ⊔ (m.H ⊓ m.M)
  refine le_antisymm ?_ (sup_le m.L_le_H inf_le_left)
  calc m.H = m.pre K ⊔ (m.H ⊓ m.M) := hW
    _ ≤ m.L ⊔ (m.H ⊓ m.M) :=
      sup_le (hpre.trans (sup_le le_sup_left (hOHG.trans le_sup_right))) le_sup_right

theorem not_L_le_M_of_inputs (hSch : UCK.KSch) : ¬ m.L ≤ m.M := by
  intro hLM
  apply m.hZ.not_le
  have h := m.c619_of_inputs hKM hK3 h69 hSch
  have : m.H ≤ m.M := by
    rw [show m.H = m.L ⊔ (m.H ⊓ m.M) from h]
    exact sup_le hLM inf_le_right
  exact this

theorem not_Z_le_L_of_inputs (hSch : UCK.KSch) : ¬ m.Z ≤ m.L := by
  intro hZL
  obtain ⟨K, hK⟩ := m.exists_component h69
  have hZK : m.bar m.Z ≤ K := (m.bar_mono hZL).trans (m.bar_L_eq hKM hK3 h69 hSch hK).le
  have hbot : m.bar m.Z = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact (mem_bot).2 (m.bar_Z_inf_component hKM hK3 h69 hK hz (hZK hz))
  have h := m.card_bar_Z
  rw [hbot, Subgroup.card_bot] at h
  exact m.hr.one_lt.ne h

theorem mem_Z_of_centralizes_Lbar (hSch : UCK.KSch) {a : G} (ha : a ∈ m.A)
    (hc : ∀ ℓ ∈ m.L, a * ℓ * a⁻¹ * ℓ⁻¹ ∈ N588.rCore m.r m.L) : a ∈ m.Z := by
  obtain ⟨K, hK⟩ := m.exists_component h69
  have haH : a ∈ m.H := m.A_le_H ha
  have hab : m.piH ⟨a, haH⟩ ∈ m.bar m.A := m.mem_bar_of_mem ha
  have hcK : ∀ k ∈ K, m.piH ⟨a, haH⟩ * k = k * m.piH ⟨a, haH⟩ := by
    intro k hk
    rw [← m.bar_L_eq hKM hK3 h69 hSch hK] at hk
    obtain ⟨ℓ, hℓL, rfl⟩ := hk
    have h1 := m.rCoreL_le_OHG (hc ℓ hℓL)
    obtain ⟨o, ho, hoe⟩ := h1
    have hoe' : o = ⟨a, haH⟩ * ℓ * ⟨a, haH⟩⁻¹ * ℓ⁻¹ := Subtype.ext (hoe.trans (by simp))
    have h2 : m.piH (⟨a, haH⟩ * ℓ * ⟨a, haH⟩⁻¹ * ℓ⁻¹) = 1 := by
      rw [← hoe']
      exact (QuotientGroup.eq_one_iff o).2 ho
    simp only [map_mul, map_inv] at h2
    calc m.piH ⟨a, haH⟩ * m.piH ℓ
        = (m.piH ⟨a, haH⟩ * m.piH ℓ * (m.piH ⟨a, haH⟩)⁻¹ * (m.piH ℓ)⁻¹) *
          (m.piH ℓ * m.piH ⟨a, haH⟩) := by group
      _ = m.piH ℓ * m.piH ⟨a, haH⟩ := by rw [h2, one_mul]
  obtain ⟨z, hzZ, hz⟩ := m.mem_bar_Z_of_centralizes hKM hK3 h69 hK hab hcK
  have h1 : z⁻¹ * ⟨a, haH⟩ ∈ m.OH := by
    rw [← QuotientGroup.eq]
    exact hz
  have hAp : IsPGroup m.r (m.A.subgroupOf m.H) :=
    m.isPGroup_A.of_equiv (Subgroup.subgroupOfEquivOfLe m.A_le_H).symm
  have h2 : z⁻¹ * ⟨a, haH⟩ ∈ m.A.subgroupOf m.H ⊓ m.OH :=
    ⟨(m.A.subgroupOf m.H).mul_mem ((m.A.subgroupOf m.H).inv_mem (m.Z_le_A hzZ)) ha, h1⟩
  rw [m.inf_OH_eq_bot hAp, mem_bot] at h2
  have h3 : (⟨a, haH⟩ : ↥m.H) = z := by
    calc (⟨a, haH⟩ : ↥m.H) = z * (z⁻¹ * ⟨a, haH⟩) := by group
      _ = z := by rw [h2, mul_one]
  have : a = (z : G) := congrArg Subtype.val h3
  rw [this]
  exact hzZ

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
