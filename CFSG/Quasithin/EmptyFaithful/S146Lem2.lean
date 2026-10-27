module

public import CFSG.Quasithin.EmptyFaithful.S145Two
public import CFSG.Quasithin.EmptyFaithful.S146Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.inf_centralizer_le_pCoreOf (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) :
    H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) ≤ pCoreOf 2 H := by
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have h4 : centralizerMod (quasithinOmegaOneCenter T) H (conjClosure (VZ T M) H) = pCoreOf 2 H :=
    S.lemma_14_5_15_four hH
  rintro x ⟨hxH, hxc⟩
  rw [← h4]
  refine ⟨hxH, Subgroup.centralizer_le_normalizer _ (hHG hxH), fun u hu => ?_⟩
  have hc : x * u * x⁻¹ * u⁻¹ = 1 := by
    have := Subgroup.mem_centralizer_iff.mp hxc u hu
    calc x * u * x⁻¹ * u⁻¹ = (u * x) * x⁻¹ * u⁻¹ := by rw [this]
      _ = 1 := by group
  rw [hc]
  exact (quasithinOmegaOneCenter T).one_mem

theorem Setting146.lemma_14_6_2 (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    (h5 : oTwoFstarIn H ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G))
    {X : Subgroup G} (hX1 : X ≠ ⊥) (hX2 : oTwoUpper X = X) (hXF : X ≤ oTwoFstarIn H)
    (hQX : pCoreOf 2 H ≤ Subgroup.normalizer (X : Set G)) :
    quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, X⁆ := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hUQ : conjClosure (VZ T M) H ≤ pCoreOf 2 H := h91.conjClosure_Vp_le_pCoreOf
  have hFH : oTwoFstarIn H ≤ H := Subgroup.map_subtype_le _
  have hXH : X ≤ H := hXF.trans hFH
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hXU := hXH.trans hHU
  have hQU := hQH.trans hHU
  have hUXU : ⁅conjClosure (VZ T M) H, X⁆ ≤ conjClosure (VZ T M) H :=
    S145.commutator_le_of_le_normalizer hXU
  have hQUX : pCoreOf 2 H ≤ Subgroup.normalizer ((⁅conjClosure (VZ T M) H, X⁆ : Subgroup G) : Set G) :=
    S145.le_normalizer_commutator hQU hQX
  have hUXQ : ⁅⁅conjClosure (VZ T M) H, X⁆, pCoreOf 2 H⁆ ≤ quasithinOmegaOneCenter T := by
    rw [Subgroup.commutator_le]
    intro u hu q hq
    rw [commutatorElement_def]
    exact h91.commutator_conjClosure_le u (hUXU hu) q hq
  have hUXQ' : ⁅⁅conjClosure (VZ T M) H, X⁆, pCoreOf 2 H⁆ ≤ ⁅conjClosure (VZ T M) H, X⁆ :=
    S145.commutator_le_of_le_normalizer hQUX
  rcases HypF98.eq_bot_or_eq_of_card_eq_two S.card_Z hUXQ with hbot | heq
  · exfalso
    have hQc : ∀ q ∈ pCoreOf 2 H, ∀ y ∈ ⁅conjClosure (VZ T M) H, X⁆, y * q = q * y := by
      intro q hq y hy
      have := Subgroup.commutator_le.mp hbot.le y hy q hq
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hW : ∀ y ∈ ⁅conjClosure (VZ T M) H, X⁆, y ∈ omegaOneCenterOf (pCoreOf 2 H) := by
      intro y hy
      refine Subgroup.subset_closure ⟨⟨hUQ (hUXU hy), Subgroup.mem_centralizer_iff.mpr
        fun q hq => (hQc q hq y hy).symm⟩, isElemAbelian_pow_eq_one hUab (hUXU hy)⟩
    have hXc : ∀ x ∈ X, ∀ y ∈ ⁅conjClosure (VZ T M) H, X⁆, y * x = x * y := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp (h5 (hXF hx)) y (hW y hy)
    have hodd : ∀ x ∈ X, Odd (orderOf x) →
        x ∈ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) := by
      intro x hx hox
      have hPX : Subgroup.zpowers x ≤ X := Subgroup.zpowers_le.mpr hx
      have hPU : Subgroup.zpowers x ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
        hPX.trans hXU
      have hidx : Odd ((Subgroup.zpowers x ⊓
          Subgroup.centralizer (conjClosure (VZ T M) H : Set G)).relIndex (Subgroup.zpowers x)) := by
        have hd := Subgroup.index_dvd_card
          ((Subgroup.zpowers x ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G)).subgroupOf
            (Subgroup.zpowers x))
        rw [Nat.card_zpowers] at hd
        exact Odd.of_dvd_nat hox hd
      have hcomm : ⁅conjClosure (VZ T M) H, Subgroup.zpowers x⁆ = ⊥ := by
        refine eq_bot_iff.mpr fun z hz => ?_
        have hzU := S145.commutator_le_of_le_normalizer hPU hz
        have hzX : z ∈ ⁅conjClosure (VZ T M) H, X⁆ := Subgroup.commutator_mono le_rfl hPX hz
        have hfix : ∀ p ∈ Subgroup.zpowers x, p * z * p⁻¹ = z := by
          intro p hp
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
          have hzx : Commute z x := hXc x hx z hzX
          have hxk : x ^ k * z = z * x ^ k := (hzx.zpow_right k).eq.symm
          calc x ^ k * z * (x ^ k)⁻¹ = z * x ^ k * (x ^ k)⁻¹ := by rw [hxk]
            _ = z := by group
        exact Subgroup.mem_bot.mpr
          (eq_one_of_mem_commutator_of_fixed hUab hPU hidx hzU hz hfix)
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      exact (Subgroup.mem_centralizer_iff.mp (hle hu) x (Subgroup.mem_zpowers x)).symm
    have hXC : X ≤ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) := by
      have : oTwoUpper X ≤ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) :=
        (Subgroup.closure_le _).mpr fun x hx => hodd x hx.1 hx.2
      rwa [hX2] at this
    have hXQ : X ≤ pCoreOf 2 H := fun x hx => S.inf_centralizer_le_pCoreOf hH ⟨hXH hx, hXC hx⟩
    apply hX1
    have hle : oTwoUpper X ≤ ⊥ := oTwoUpper_le_of_pow_mem fun x hx => by
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨x, hXQ hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    rw [hX2] at hle
    exact le_bot_iff.mp hle
  · rw [← heq]
    exact hUXQ'

theorem stage1462_of (h5 : Stage1461Five) :
    ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
      ∀ H : Subgroup G, IsHTM T M H → ∀ X : Subgroup G, X ≠ ⊥ → oTwoUpper X = X →
        X ≤ oTwoFstarIn H → pCoreOf 2 H ≤ Subgroup.normalizer (X : Set G) →
          quasithinOmegaOneCenter T ≤ ⁅conjClosure (VZ T M) H, X⁆ :=
  fun G _ _ T M S H hH _ hX1 hX2 hXF hQX =>
    S.lemma_14_6_2 hH (h5 G T M S H hH) hX1 hX2 hXF hQX

end Main

end CFSG.Quasithin
