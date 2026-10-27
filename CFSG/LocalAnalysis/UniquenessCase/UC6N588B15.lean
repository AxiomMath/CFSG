module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B14
public import CFSG.RankThree.PartOne.KF.U4Ambient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm
open CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588

theorem le_inftyOf_of_perfect_uc6b {G : Type} [Group G] {X E : Subgroup G} (hEX : E ≤ X)
    (hperf : ⁅E, E⁆ = E) : E ≤ inftyOf X := by
  have hcomm : ⁅E.subgroupOf X, E.subgroupOf X⁆ = E.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEX, hperf]
  have key : ∀ k : ℕ, E.subgroupOf X ≤ derivedSeries ↥X k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ]
      calc E.subgroupOf X = ⁅E.subgroupOf X, E.subgroupOf X⁆ := hcomm.symm
        _ ≤ ⁅derivedSeries ↥X k, derivedSeries ↥X k⁆ := Subgroup.commutator_mono ih ih
  calc E = (E.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hEX).symm
    _ ≤ (derivedSeries ↥X (Nat.card ↥X)).map X.subtype := Subgroup.map_mono (key _)
    _ = inftyOf X := rfl

namespace Mz614

variable {G : Type} [Group G] [Finite G]

namespace A10Setup

variable {m : Mz614 G} (D : A10Setup m)

theorem conj_inv_ι_mem_L (hr : m.r = 5) {w : G}
    (hw₁ : m.Z.map (MulAut.conj w).toMonoidHom = line₁.map D.ι) {σ : A10} (hσ : σ ∈ altA T5) :
    w⁻¹ * D.ι σ * w ∈ m.L := by
  set φ : A10 →* G := (MulAut.conj w⁻¹).toMonoidHom.comp D.ι with hφ
  have hφinj : Function.Injective φ := (MulAut.conj w⁻¹).injective.comp D.ι_injective
  have hφapp : ∀ τ, φ τ = w⁻¹ * D.ι τ * w := fun τ => by simp [hφ, MulAut.conj_apply]
  set Y := (altA T5).map φ with hY
  have hYH : Y ≤ m.H := by
    rintro _ ⟨τ, hτ, rfl⟩
    refine mem_centralizer_iff.2 fun z hz => ?_
    obtain ⟨ρ, hρ, hρz⟩ := conj_mem_of_map_eq_uc6b hw₁ hz
    rw [line₁_eq] at hρ
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hρ
    have hcomm : a₁ ^ k * τ = τ * a₁ ^ k := (Commute.zpow_left (a₁_comm_T5 hτ) k).eq
    have hz' : z = w⁻¹ * D.ι (a₁ ^ k) * w := by rw [hρz]; group
    rw [hφapp, hz']
    calc w⁻¹ * D.ι (a₁ ^ k) * w * (w⁻¹ * D.ι τ * w) = w⁻¹ * D.ι (a₁ ^ k * τ) * w := by
          rw [map_mul]; group
      _ = w⁻¹ * D.ι (τ * a₁ ^ k) * w := by rw [hcomm]
      _ = w⁻¹ * D.ι τ * w * (w⁻¹ * D.ι (a₁ ^ k) * w) := by rw [map_mul]; group
  have hT5simple : IsSimpleGroup ↥(altA T5) := isSimpleGroup_altA T5 card_T5.symm.le
  have hT5perf : ⁅altA T5, altA T5⁆ = altA T5 :=
    commutator_eq_self_of_simple hT5simple a₂_mem_T5 (altA_mono T4_le_T5 x₃_mem_T4) a₂_x₃_ne
  have hYperf : ⁅Y, Y⁆ = Y := by rw [hY, ← Subgroup.map_commutator, hT5perf]
  have hYinf : Y ≤ inftyOf m.H := le_inftyOf_of_perfect_uc6b hYH hYperf
  have hYsimple : IsSimpleGroup ↥Y :=
    ((altA T5).equivMapOfInjective φ hφinj).symm.isSimpleGroup
  have ha₂ : φ a₂ ≠ 1 := fun h => a₂_ne (hφinj (h.trans (map_one φ).symm))
  have ha₂o : orderOf (φ a₂) = 5 := orderOf_eq_prime (by rw [← map_pow, a₂_pow, map_one]) ha₂
  have hYp : CFSG.RankThree.PartOne.pElementSubgroup 5 Y = Y :=
    CFSG.RankThree.PartOne.KFU.pElementSubgroup_eq_of_simple hYsimple ⟨a₂, a₂_mem_T5, rfl⟩ ha₂o
      ha₂
  have hYL : Y ≤ m.L := by
    rw [← hYp]
    show Subgroup.closure {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = 5 ^ k} ≤
      Subgroup.closure {x : G | x ∈ inftyOf m.H ∧ ∃ k : ℕ, orderOf x = m.r ^ k}
    rw [hr]
    exact Subgroup.closure_mono fun x hx => ⟨hYinf hx.1, hx.2⟩
  have h := hYL ⟨σ, hσ, rfl⟩
  rwa [hφapp] at h

theorem conj_ι_t₀_mem_Ka (hr : m.r = 5) {w : G}
    (hw₁ : m.Z.map (MulAut.conj w).toMonoidHom = line₁.map D.ι)
    (hw₂ : (line₁.map D.ι).map (MulAut.conj w).toMonoidHom = m.Z) :
    w * D.ι t₀ * w⁻¹ ∈ D.Ka := by
  rw [D.mem_Ka_iff]
  intro x hx
  obtain ⟨ρ, hρ⟩ := D.exists_ι (D.conj_inv_ι_mem_L hr hw₁ (altA_mono T4_le_T5 hx))
  have hx' : D.ι x = w * D.ι ρ * w⁻¹ := by rw [hρ]; group
  have hz : w * D.ι a₁ * w⁻¹ ∈ m.Z :=
    conj_mem_of_map_eq_uc6b hw₂ ⟨a₁, by rw [line₁_eq]; exact mem_zpowers a₁, rfl⟩
  have hc1 : D.ι x * (w * D.ι a₁ * w⁻¹) = (w * D.ι a₁ * w⁻¹) * D.ι x :=
    (m.Z_comm_L hz (D.ι_mem_L x)).symm
  have hρa : ρ * a₁ = a₁ * ρ := by
    apply D.ι_injective
    rw [map_mul, map_mul]
    have h : w * (D.ι ρ * D.ι a₁) * w⁻¹ = w * (D.ι a₁ * D.ι ρ) * w⁻¹ := by
      calc w * (D.ι ρ * D.ι a₁) * w⁻¹ = (w * D.ι ρ * w⁻¹) * (w * D.ι a₁ * w⁻¹) := by group
        _ = D.ι x * (w * D.ι a₁ * w⁻¹) := by rw [hx']
        _ = (w * D.ι a₁ * w⁻¹) * D.ι x := hc1
        _ = (w * D.ι a₁ * w⁻¹) * (w * D.ι ρ * w⁻¹) := by rw [hx']
        _ = w * (D.ι a₁ * D.ι ρ) * w⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h)
  have hρ12 : ρ ^ 12 = 1 := by
    apply D.ι_injective
    rw [map_pow, map_one, hρ, conj_inv_pow_uc6b, ← map_pow, pow_twelve_of_mem_T4 hx, map_one]
    group
  have hρt : ρ * t₀ = t₀ * ρ := commute_t₀_of_fix (fix_of_commute_a₁ hρa hρ12)
  rw [hx']
  calc w * D.ι ρ * w⁻¹ * (w * D.ι t₀ * w⁻¹) = w * D.ι (ρ * t₀) * w⁻¹ := by
        rw [map_mul]; group
    _ = w * D.ι (t₀ * ρ) * w⁻¹ := by rw [hρt]
    _ = w * D.ι t₀ * w⁻¹ * (w * D.ι ρ * w⁻¹) := by rw [map_mul]; group

theorem three_dvd_normalClosure (hr : m.r = 5) {w : G}
    (hw₁ : m.Z.map (MulAut.conj w).toMonoidHom = line₁.map D.ι)
    (hw₂ : (line₁.map D.ι).map (MulAut.conj w).toMonoidHom = m.Z) :
    3 ∣ Nat.card ↥(Subgroup.normalClosure
      ((m.Z.subgroupOf D.Ka : Subgroup ↥D.Ka) : Set ↥D.Ka)) := by
  set φ : A10 →* G := (MulAut.conj w).toMonoidHom.comp D.ι with hφ
  have hφinj : Function.Injective φ := (MulAut.conj w).injective.comp D.ι_injective
  have hφapp : ∀ τ, φ τ = w * D.ι τ * w⁻¹ := fun τ => by simp [hφ, MulAut.conj_apply]
  have hzZ : φ a₁ ∈ m.Z := by
    rw [hφapp]
    exact conj_mem_of_map_eq_uc6b hw₂ ⟨a₁, by rw [line₁_eq]; exact mem_zpowers a₁, rfl⟩
  have hkK : φ t₀ ∈ D.Ka := by
    rw [hφapp]
    exact D.conj_ι_t₀_mem_Ka hr hw₁ hw₂
  set z' : ↥D.Ka := ⟨φ a₁, D.Z_le_Ka hzZ⟩ with hz'
  set k' : ↥D.Ka := ⟨φ t₀, hkK⟩ with hk'
  set N := Subgroup.normalClosure ((m.Z.subgroupOf D.Ka : Subgroup ↥D.Ka) : Set ↥D.Ka) with hN
  have hz'N : z' ∈ N := Subgroup.subset_normalClosure (mem_subgroupOf.2 hzZ)
  have hu : z' * (k' * z' ^ 2 * k'⁻¹) ∈ N :=
    mul_mem hz'N ((Subgroup.normalClosure_normal (s := _)).conj_mem _ (pow_mem hz'N 2) k')
  have horder : orderOf (z' * (k' * z' ^ 2 * k'⁻¹)) = 3 := by
    have h1 : ((z' * (k' * z' ^ 2 * k'⁻¹) : ↥D.Ka) : G) = φ (a₁ * (t₀ * a₁ ^ 2 * t₀⁻¹)) := by
      simp [hz', hk', map_mul, map_pow, map_inv]
    rw [← Subgroup.orderOf_coe, h1, orderOf_injective φ hφinj]
    exact orderOf_eq_prime order_three_check.1 order_three_check.2
  have h := orderOf_dvd_natCard (⟨_, hu⟩ : ↥N)
  rwa [Subgroup.orderOf_mk, horder] at h

end A10Setup

theorem c623_of_A10 (hK2 : UCK.K322) (hK4 : UCK.K324) (m : Mz614 G)
    (h67 : R6_7 (dataOfSetup4 m.hS m.hU m.S)) (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))
    (h619 : m.C619) (h620 : m.C620) (hr : m.r = 5) (hL : UC22.IsAlt ↥m.L 10) : m.C623 := by
  by_contra hne
  obtain ⟨D⟩ := exists_A10Setup m h620 hr hL
  obtain ⟨w, -, hw₁, hw₂⟩ := D.exists_w hK2 h69 h620 hr hne
  obtain ⟨hw₁', hw₂'⟩ := D.conj_Z_le_L hw₁ hw₂
  have hKtop : D.Ka ≠ ⊤ := by
    intro h
    have hx : D.ι x₃ ∈ D.Ka ⊓ D.Xa := ⟨h ▸ mem_top _, ⟨x₃, x₃_mem_T4, rfl⟩⟩
    rw [D.Ka_inf_Xa, mem_bot] at hx
    exact x₃_ne (D.ι_injective (hx.trans (map_one _).symm))
  have hKk : CFSG.Open.IsKGroup ↥D.Ka := m.hS.kProper.isKGroup D.Ka hKtop
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥D.Ka) = 2 := by
    rw [← pRank_map_subtype_uc6 Nat.prime_three D.Ka ⊤, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact D.pRank_Ka h619 h620
  have hle : m.Z ⊔ line₁.map D.ι ≤ D.Ka := sup_le D.Z_le_Ka D.line₁_le_Ka
  have hE'map : ((m.Z ⊔ line₁.map D.ι).subgroupOf D.Ka).map D.Ka.subtype =
      m.Z ⊔ line₁.map D.ι := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
  have hsyl : IsSylowOf 5 ((m.Z ⊔ line₁.map D.ι).subgroupOf D.Ka) ⊤ := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    rw [← isSylowOf_map_subtype_iff D.Ka, hE'map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact D.isSylowOf_Ka h69 h620 hr hw₁' hw₂'
  have hel : CFSG.Open.IsElemAbelian 5 ((m.Z ⊔ line₁.map D.ι).subgroupOf D.Ka) := by
    apply isElemAbelian_subgroupOf_uc6 hle
    have hZel : IsElemAbelian 5 m.Z := by
      rw [← hr]
      exact isElemAbelian_of_card_prime m.hr m.card_Z
    have hYel : IsElemAbelian 5 (line₁.map D.ι) :=
      isElemAbelian_of_card_prime Nat.prime_five (by rw [D.card_map_ι, card_line₁])
    exact hZel.sup_of_commute hYel fun z hz y hy => m.Z_comm_L hz (D.map_ι_le_L _ hy)
  have hcard : Nat.card ((m.Z ⊔ line₁.map D.ι).subgroupOf D.Ka) = 25 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, D.card_Z_sup_line₁ h620 hr]
  have hZE : m.Z.subgroupOf D.Ka ≤ (m.Z ⊔ line₁.map D.ι).subgroupOf D.Ka := fun x hx =>
    mem_subgroupOf.2 (mem_sup_left (mem_subgroupOf.1 hx))
  have hZcard : Nat.card (m.Z.subgroupOf D.Ka) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.Z_le_Ka).toEquiv, m.card_Z, hr]
  exact hK4 ↥D.Ka hKk hrank _ hsyl hel hcard _ hZE hZcard
    (D.isAlt_layer h69 h620 hr hw₁' hw₂') (D.three_dvd_normalClosure hr hw₁ hw₂)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
