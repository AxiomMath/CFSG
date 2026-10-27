module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpHolds
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSpTwo
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerB1
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerA2
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorFactor

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.SeitzReduction.SymplecticPilot
  RootCentSp CFSG.Open

theorem exists_inn_field_of_mem_normalizer {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 3 ≤ n) {G : Type*} [Group G] {ψ : StatedSp n F →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {a : G}
    (ha : a ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ (g : StatedSp n F) (σ : F ≃+* F), ∀ k : StatedSp n F,
      a * ψ k * a⁻¹ = ψ (g * SymplecticHigher.fieldSp n F σ k * g⁻¹) := by
  classical
  let Θ : StatedProj (StatedSp n F) ≃* ψ.range := AutPSp.projEquiv hker hC
  let c : MulAut ψ.range := CFSG.LocalAnalysis.ComponentInitial.conjAut ψ.range ha
  let α : MulAut (StatedProj (StatedSp n F)) := (Θ.trans c).trans Θ.symm
  obtain ⟨i, hi, c', hc', hα⟩ := AutPSp.exists_mul_compl (K := F) hn α
  rw [MonoidHom.mem_range] at hi hc'
  obtain ⟨s, rfl⟩ := hi
  obtain ⟨σ, rfl⟩ := hc'
  obtain ⟨y, rfl⟩ := SymplecticHigher.proj_surjective s
  have hΘ : ∀ x : StatedSp n F,
      Θ (SymplecticFlag.proj n F x) = ⟨ψ x, ⟨x, rfl⟩⟩ :=
    fun x => Subtype.ext (AutPSp.projEquiv_proj hker hC x)
  refine ⟨y, σ, fun k => ?_⟩
  have hmem : a * ψ k * a⁻¹ ∈ ψ.range :=
    (Subgroup.mem_normalizer_iff.mp ha (ψ k)).mp ⟨k, rfl⟩
  have h1 : Θ (α (SymplecticFlag.proj n F k)) = ⟨a * ψ k * a⁻¹, hmem⟩ := by
    change Θ (Θ.symm (c (Θ (SymplecticFlag.proj n F k)))) = _
    rw [hΘ k, MulEquiv.apply_symm_apply]
    exact Subtype.ext (CFSG.LocalAnalysis.ComponentInitial.coe_conjAut ha ⟨ψ k, ⟨k, rfl⟩⟩)
  have h2 : Θ (α (SymplecticFlag.proj n F k)) =
      ⟨ψ (y * SymplecticHigher.fieldSp n F σ k * y⁻¹), ⟨_, rfl⟩⟩ := by
    rw [hα]
    simp only [MulAut.mul_apply, MulAut.conj_apply, SymplecticHigher.fieldAut_proj, map_mul,
      map_inv, hΘ]
    exact Subtype.ext (by simp)
  exact congrArg Subtype.val (h1.symm.trans h2)

private theorem mem_range_of_conj_eq {F : Type} [Field F] {n : ℕ} {G : Type} [Group G]
    {ψ : StatedSp n F →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {a : G} {g : StatedSp n F}
    (ha : a ∈ Subgroup.normalizer (ψ.range : Set G))
    (hg : ∀ k : StatedSp n F, a * ψ k * a⁻¹ = ψ (g * k * g⁻¹)) :
    a ∈ ψ.range := by
  have hinner : ψ.range.normalizerMonoidHom ⟨a, ha⟩ =
      MulAut.conj (⟨ψ g, ⟨g, rfl⟩⟩ : ψ.range) := by
    ext x
    obtain ⟨k, hk⟩ := x.2
    rw [show x = ⟨ψ k, ⟨k, rfl⟩⟩ from Subtype.ext hk.symm]
    rw [GGRootNorm.coe_normalizerMonoidHom, MulAut.conj_apply, hg k, map_mul, map_mul, map_inv]
    simp
  have h := GGRootNorm.mem_sup_centralizer_of_induced_inner ha hinner
  rw [hC] at h
  simpa using h

private theorem pCoreOf_le_range_of_decomp {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 3 ≤ n)
    {G : Type} [Group G] (ψ : StatedSp n F →* G)
    (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    {x₀ : StatedSp n F}
    (hfix : ∀ σ : F ≃+* F, SymplecticHigher.fieldSp n F σ x₀ = x₀)
    {Q L : Subgroup (StatedSp n F)}
    (hCx : Subgroup.centralizer {x₀} = Q ⊔ L)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set (StatedSp n F)))
    (hdisj : Disjoint Q L)
    (hQ : CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer {x₀}) = Q)
    {ρ : TauCeti.GLSymplecticFin.RootSubgroupIndex n}
    (hρ : ∀ c : F, Symplectic.SpExtras.elt ρ c ∈ L) :
    CFSG.Assembly.pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ x₀}) ≤ ψ.range := by
  set M : Subgroup G := Subgroup.normalizer (ψ.range : Set G) ⊓
    Subgroup.centralizer {ψ x₀} with hM
  set P : Subgroup G := CFSG.Assembly.pCoreOf 2 M with hP
  have hPM : P ≤ M := GGRootNorm.pCoreOf_le M
  have hP2 : IsPGroup 2 P := GGRootNorm.isPGroup_pCoreOf M
  have hMN : M ≤ Subgroup.normalizer (P : Set G) := GGRootNorm.le_normalizer_pCoreOf M
  have hLle : L ≤ Subgroup.centralizer {x₀} := hCx ▸ le_sup_right
  have hCxN : Subgroup.centralizer {x₀} ≤ Subgroup.normalizer (Q : Set (StatedSp n F)) := by
    rw [← hQ]
    exact GGRootNorm.le_normalizer_pCoreOf _
  intro a ha
  have haM : a ∈ M := hPM ha
  have haN : a ∈ Subgroup.normalizer (ψ.range : Set G) := haM.1
  have haC : a ∈ Subgroup.centralizer {ψ x₀} := haM.2
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n F) := by
    rw [show ψ.ker = ⊥ from (MonoidHom.ker_eq_bot_iff ψ).mpr hψ]
    exact bot_le
  obtain ⟨g, σ, hg⟩ := exists_inn_field_of_mem_normalizer hn hker hC haN
  have hgCx : g ∈ Subgroup.centralizer {x₀} := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp haC
    have h0 : ψ (g * x₀ * g⁻¹) = a * ψ x₀ * a⁻¹ := by
      have h := hg x₀
      rw [hfix σ] at h
      exact h.symm
    have h1 : ψ (g * x₀ * g⁻¹) = ψ x₀ := by
      rw [h0, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : g * x₀ * g⁻¹ = x₀ := hψ h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * x₀ = (g * x₀ * g⁻¹) * g := by group
      _ = x₀ * g := by rw [h2]
  let N : Subgroup (StatedSp n F) := Subgroup.comap ψ P ⊓ Subgroup.centralizer {x₀}
  have hN2 : IsPGroup 2 N := (hP2.comap_of_injective ψ hψ).to_le inf_le_left
  have hNQ : N ≤ Q := by
    rw [← hQ]
    refine GGRootNorm.le_pCoreOf_of_normalized inf_le_right hN2 ?_
    intro m hm t ht
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hψmM : ψ m ∈ M := by
        rw [hM]
        refine ⟨Subgroup.le_normalizer ⟨m, rfl⟩, ?_⟩
        change ψ m ∈ Subgroup.centralizer ({ψ x₀} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff] at hm ⊢
        rw [← map_mul, ← map_mul, hm]
      have hψtP : ψ t ∈ P := ht.1
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hMN hψmM) (ψ t)).mp hψtP
    · exact (Subgroup.centralizer {x₀}).mul_mem
        ((Subgroup.centralizer {x₀}).mul_mem hm ht.2)
        ((Subgroup.centralizer {x₀}).inv_mem hm)
  have hgQL : g ∈ Q ⊔ L := by rw [← hCx]; exact hgCx
  have hgQL' : g ∈ (↑(Q ⊔ L) : Set (StatedSp n F)) := hgQL
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Q L hLQ] at hgQL'
  obtain ⟨q₀, hq₀, h, hhL, hgeq⟩ := hgQL'
  have hhCx : h ∈ Subgroup.centralizer {x₀} := hLle hhL
  have hψmem : ∀ k : StatedSp n F, k ∈ Subgroup.centralizer {x₀} → ψ k ∈ M := by
    intro k hk
    rw [hM]
    refine ⟨Subgroup.le_normalizer ⟨k, rfl⟩, ?_⟩
    change ψ k ∈ Subgroup.centralizer ({ψ x₀} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    rw [← map_mul, ← map_mul, hk]
  have hkey : ∀ c : F,
      h * SymplecticHigher.fieldSp n F σ (Symplectic.SpExtras.elt ρ c) * h⁻¹ =
        Symplectic.SpExtras.elt ρ c := by
    intro c
    set k : StatedSp n F := Symplectic.SpExtras.elt ρ c with hk
    have hkL : k ∈ L := hρ c
    have hkCx : k ∈ Subgroup.centralizer {x₀} := hLle hkL
    have hsigL : SymplecticHigher.fieldSp n F σ k ∈ L := by
      rw [hk, AutPSp.fieldSp_elt]
      exact hρ (σ c)
    have hsigCx : SymplecticHigher.fieldSp n F σ k ∈ Subgroup.centralizer {x₀} := hLle hsigL
    set A : StatedSp n F := h * SymplecticHigher.fieldSp n F σ k * h⁻¹ with hA
    have hAL : A ∈ L := L.mul_mem (L.mul_mem hhL hsigL) (L.inv_mem hhL)
    have hACx : A ∈ Subgroup.centralizer {x₀} :=
      (Subgroup.centralizer {x₀}).mul_mem
        ((Subgroup.centralizer {x₀}).mul_mem hhCx hsigCx)
        ((Subgroup.centralizer {x₀}).inv_mem hhCx)
    have hdCx : g * SymplecticHigher.fieldSp n F σ k * g⁻¹ * k⁻¹ ∈
        Subgroup.centralizer {x₀} :=
      (Subgroup.centralizer {x₀}).mul_mem
        ((Subgroup.centralizer {x₀}).mul_mem
          ((Subgroup.centralizer {x₀}).mul_mem hgCx hsigCx)
          ((Subgroup.centralizer {x₀}).inv_mem hgCx))
        ((Subgroup.centralizer {x₀}).inv_mem hkCx)
    have hdP : ψ (g * SymplecticHigher.fieldSp n F σ k * g⁻¹ * k⁻¹) ∈ P := by
      have hψkM : ψ k ∈ M := hψmem k hkCx
      have hgkP : ψ k * a * (ψ k)⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hMN hψkM) a).mp ha
      have e : ψ (g * SymplecticHigher.fieldSp n F σ k * g⁻¹ * k⁻¹) =
          a * (ψ k * a * (ψ k)⁻¹)⁻¹ := by
        calc ψ (g * SymplecticHigher.fieldSp n F σ k * g⁻¹ * k⁻¹) =
            ψ (g * SymplecticHigher.fieldSp n F σ k * g⁻¹) * ψ k⁻¹ := by
              rw [map_mul, map_inv]
          _ = (a * ψ k * a⁻¹) * (ψ k)⁻¹ := by
              rw [show ψ (g * SymplecticHigher.fieldSp n F σ k * g⁻¹) =
                a * ψ k * a⁻¹ from (hg k).symm, map_inv]
          _ = a * (ψ k * a * (ψ k)⁻¹)⁻¹ := by group
      rw [e]
      exact P.mul_mem ha (P.inv_mem hgkP)
    have hdN : g * SymplecticHigher.fieldSp n F σ k * g⁻¹ * k⁻¹ ∈ N :=
      Subgroup.mem_inf.mpr ⟨hdP, hdCx⟩
    have hconjQ : A * q₀ * A⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hCxN hACx) q₀).mp hq₀
    have hkeyQ : (g * SymplecticHigher.fieldSp n F σ k * g⁻¹ * k⁻¹) *
        (A * k⁻¹)⁻¹ ∈ Q := by
      have e : (g * SymplecticHigher.fieldSp n F σ k * g⁻¹ * k⁻¹) * (A * k⁻¹)⁻¹ =
          q₀ * (A * q₀ * A⁻¹)⁻¹ := by
        rw [← hgeq, hA]
        group
      rw [e]
      exact Q.mul_mem hq₀ (Q.inv_mem hconjQ)
    have hAkQ : A * k⁻¹ ∈ Q := by
      have h1 : (A * k⁻¹)⁻¹ ∈ Q := by
        have h2 := Q.mul_mem (Q.inv_mem (hNQ hdN)) hkeyQ
        have e : (g * SymplecticHigher.fieldSp n F σ k * g⁻¹ * k⁻¹)⁻¹ *
            ((g * SymplecticHigher.fieldSp n F σ k * g⁻¹ * k⁻¹) * (A * k⁻¹)⁻¹) =
            (A * k⁻¹)⁻¹ := by group
        rwa [e] at h2
      exact Q.inv_mem h1
    have hAkL : A * k⁻¹ ∈ L := L.mul_mem hAL (L.inv_mem hkL)
    have hone : A * k⁻¹ = 1 := by
      have hb := hdisj.le_bot ⟨hAkQ, hAkL⟩
      simpa using hb
    calc h * SymplecticHigher.fieldSp n F σ k * h⁻¹ = A := rfl
      _ = k := by
        have h3 : A = (A * k⁻¹) * k := by group
        rw [h3, hone, one_mul]
  have hcommel : h * Symplectic.SpExtras.elt ρ 1 * h⁻¹ = Symplectic.SpExtras.elt ρ 1 := by
    have := hkey 1
    rwa [AutPSp.fieldSp_elt, map_one] at this
  have hσ1 : σ = 1 := by
    ext c
    have h1 := hkey c
    rw [AutPSp.fieldSp_elt] at h1
    have h2 := AutPSp.commute_elt_of_commute_elt_one hcommel c
    have h3 : Symplectic.SpExtras.elt ρ (σ c) = Symplectic.SpExtras.elt ρ c := by
      have h4 : h * Symplectic.SpExtras.elt ρ (σ c) * h⁻¹ =
          h * Symplectic.SpExtras.elt ρ c * h⁻¹ := by rw [h1, h2]
      exact mul_left_cancel (mul_right_cancel h4)
    exact Symplectic.SpExtras.elt_injective ρ h3
  have hg' : ∀ k : StatedSp n F, a * ψ k * a⁻¹ = ψ (g * k * g⁻¹) := by
    intro k
    have := hg k
    rwa [hσ1] at this
  exact mem_range_of_conj_eq hC haN hg'

private theorem pCoreOf_le_range_of_card_two {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 3 ≤ n) {G : Type} [Group G] (ψ : StatedSp n F →* G)
    (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (hcard : Nat.card F = 2)
    {x₀ : StatedSp n F} :
    CFSG.Assembly.pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ x₀}) ≤ ψ.range := by
  intro a ha
  have haM : a ∈ Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ x₀} := GGRootNorm.pCoreOf_le _ ha
  have haN : a ∈ Subgroup.normalizer (ψ.range : Set G) := haM.1
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n F) := by
    rw [show ψ.ker = ⊥ from (MonoidHom.ker_eq_bot_iff ψ).mpr hψ]
    exact bot_le
  obtain ⟨g, σ, hg⟩ := exists_inn_field_of_mem_normalizer hn hker hC haN
  have hσ1 : σ = 1 := by
    have hcardu : Nat.card Fˣ = 1 := by rw [Nat.card_units, hcard]
    haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.1 hcardu).1
    ext x
    by_cases hx : x = 0
    · rw [hx, map_zero, map_zero]
    · have hx1 : x = 1 := congrArg Units.val (Subsingleton.elim (Units.mk0 x hx) 1)
      rw [hx1, map_one, map_one]
  have hg' : ∀ k : StatedSp n F, a * ψ k * a⁻¹ = ψ (g * k * g⁻¹) := by
    intro k
    have h := hg k
    rw [hσ1] at h
    simpa using h
  exact mem_range_of_conj_eq hC haN hg'

theorem pCoreOf_le_range_of_siegDiag {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 3 ≤ n) {G : Type} [Group G] [Finite G] (ψ : StatedSp n F →* G)
    (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (i : Fin n) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (siegDiag F i 1)}) ≤ ψ.range := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases hcard : Nat.card F = 2
  · exact pCoreOf_le_range_of_card_two (by omega) ψ hψ hC hcard
  · have h4 : 4 ≤ Nat.card F := by
      haveI : Fintype F := Fintype.ofFinite F
      obtain ⟨k, -, hk⟩ := FiniteField.card F 2
      have hk2 : 2 ≤ (k : ℕ) := by
        by_contra h
        have hk1 : (k : ℕ) = 1 := by have := k.pos; omega
        apply hcard
        rw [Nat.card_eq_fintype_card, hk, hk1]
        norm_num
      rw [Nat.card_eq_fintype_card, hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) hk2
    have hm1 : 1 ≤ m := by omega
    have hfix : ∀ σ : F ≃+* F, SymplecticHigher.fieldSp (m + 1) F σ (siegDiag F i 1) =
        siegDiag F i 1 := by
      intro σ
      rw [← RootCentSp.elt_positiveLong_one i, AutPSp.fieldSp_elt, map_one,
        RootCentSp.elt_positiveLong_one]
    have hQ : CFSG.Assembly.pCoreOf 2 (Subgroup.centralizer {siegDiag F i 1}) =
        transvRadical F i := by
      refine ggRCST_pCoreOf_eq centralizer_siegDiag_eq_sup isPGroup_transvRadical
        complSp_le_normalizer_transvRadical ?_
      intro N hN hN2 hNN
      haveI : (N.subgroupOf (complSp F i)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hNN
      have hN'2 : IsPGroup 2 (N.subgroupOf (complSp F i)) :=
        hN2.comap_of_injective (complSp F i).subtype (complSp F i).subtype_injective
      have hbot : N.subgroupOf (complSp F i) = ⊥ :=
        eq_bot_of_normal_of_isPGroup_complSp (K := F) (m := m) h4 hm1
          (N.subgroupOf (complSp F i)) hN'2
      rw [eq_bot_iff]
      intro x hx
      have hxS : x ∈ complSp F i := hN hx
      have hmem : (⟨x, hxS⟩ : ↥(complSp F i)) ∈ N.subgroupOf (complSp F i) := hx
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))
    obtain ⟨j, hji⟩ : ∃ j : Fin (m + 1), j ≠ i := by
      by_cases hi : i = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        rw [hi]
        intro h
        exact absurd (congrArg Fin.val h) (by simp)
      · exact ⟨0, fun h => hi h.symm⟩
    have hρ : ∀ c : F, Symplectic.SpExtras.elt (.positiveLong j) c ∈ complSp F i :=
      fun c => longRootSp2_le_complSp (Ne.symm hji) (elt_positiveLong_mem_longRootSp2 j c)
    exact pCoreOf_le_range_of_decomp (by omega) ψ hψ hC hfix centralizer_siegDiag_eq_sup
      complSp_le_normalizer_transvRadical disjoint_transvRadical_complSp hQ hρ

theorem pCoreOf_le_range_of_twoCentralElt {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    {G : Type} [Group G] [Finite G] (ψ : StatedSp (m + 3) F →* G)
    (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (twoCentralElt (m + 3) 1 2 (0 : F) 1)}) ≤ ψ.range := by
  by_cases hcard : Nat.card F = 2
  · exact pCoreOf_le_range_of_card_two (by omega) ψ hψ hC hcard
  · have h4 : 4 ≤ Nat.card F := by
      haveI : Fintype F := Fintype.ofFinite F
      obtain ⟨k, -, hk⟩ := FiniteField.card F 2
      have hk2 : 2 ≤ (k : ℕ) := by
        by_contra h
        have hk1 : (k : ℕ) = 1 := by have := k.pos; omega
        apply hcard
        rw [Nat.card_eq_fintype_card, hk, hk1]
        norm_num
      rw [Nat.card_eq_fintype_card, hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) hk2
    have h12 : (1 : Fin (m + 3)) < 2 := by
      show (1 : ℕ) < 2 % (m + 3)
      rw [Nat.mod_eq_of_lt (by omega)]
      norm_num
    have hfix : ∀ σ : F ≃+* F,
        SymplecticHigher.fieldSp (m + 3) F σ (twoCentralElt (m + 3) 1 2 (0 : F) 1) =
          twoCentralElt (m + 3) 1 2 (0 : F) 1 := by
      intro σ
      rw [← RootCentSp.elt_positiveSum_one h12, AutPSp.fieldSp_elt, map_one,
        RootCentSp.elt_positiveSum_one h12]
    have hfacts := RCSTSp.centralizer_a2_facts (F := F) (n := m)
    have hLQ : a2Levi F m ≤ Subgroup.normalizer
        (wRadical F (1 : Fin (m + 3)) 2 : Set (StatedSp (m + 3) F)) := by
      simpa only [a2Levi] using sup_le hfacts.2.1 hfacts.2.2.1
    have hdisj : Disjoint (wRadical F (1 : Fin (m + 3)) 2) (a2Levi F m) := by
      simpa only [a2Levi] using RCSTSp2.disjoint_wRadical_levi (F := F) (n := m)
    have hQ : CFSG.Assembly.pCoreOf 2
        (Subgroup.centralizer {twoCentralElt (m + 3) 1 2 (0 : F) 1}) =
        wRadical F (1 : Fin (m + 3)) 2 := by
      refine ggRCST_pCoreOf_eq hfacts.1 (isPGroup_wRadical (one_ne_two_fin (n := m)))
        hLQ ?_
      intro N hN hN2 hNN
      haveI : (N.subgroupOf (a2Levi F m)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hNN
      have hN'2 : IsPGroup 2 (N.subgroupOf (a2Levi F m)) :=
        hN2.comap_of_injective (a2Levi F m).subtype (a2Levi F m).subtype_injective
      have hbot : N.subgroupOf (a2Levi F m) = ⊥ :=
        eq_bot_of_normal_of_isPGroup_a2Levi h4 (N.subgroupOf (a2Levi F m)) hN'2
      rw [eq_bot_iff]
      intro x hx
      have hxS : x ∈ a2Levi F m := hN hx
      have hmem : (⟨x, hxS⟩ : ↥(a2Levi F m)) ∈ N.subgroupOf (a2Levi F m) := hx
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))
    have hρ : ∀ c : F,
        Symplectic.SpExtras.elt (.positiveLong (0 : Fin (m + 3))) c ∈ a2Levi F m := by
      intro c
      have h1 : Symplectic.SpExtras.elt (.positiveLong (0 : Fin (m + 3))) c ∈
          spCompl12 F m :=
        longRootSp2_le_spCompl12 (n := m) (elt_positiveLong_mem_longRootSp2 (0 : Fin (m + 3)) c)
      simpa only [a2Levi] using Subgroup.mem_sup_right h1
    exact pCoreOf_le_range_of_decomp (by omega) ψ hψ hC hfix hfacts.1 hLQ hdisj hQ hρ

section Tags

theorem ggRootCentOTwoTag_PSp : GGRootCentOTwoTag .PSp := by
  intro G _ _ n f ψ hadm hrank hker hcomm hLie hC hBs r hr hnsolv
  let ψs : StatedSp n (GaloisField 2 f) →* G := ψ
  have hn2 : 2 ≤ n := hrank
  obtain ⟨p, Bs, hp, hp2, hBsE, hcard, -, hBsI⟩ := hBs
  have hn4 : 4 ≤ n :=
    AutPSp.four_le_of_bstar (K := GaloisField 2 f) hn2 ψs hker hC hp hp2 hBsE hcard hBsI
  haveI : NeZero n := ⟨by omega⟩
  have hcenter : Subgroup.center (ggU .PSp n f).K = ⊥ := AutPSp.center_eq_bot
  have hψ : Function.Injective ψs :=
    (MonoidHom.ker_eq_bot_iff ψs).mp
      (le_antisymm (hker.trans (by rw [hcenter]; exact bot_le)) bot_le)
  obtain ⟨ρ, w, hw⟩ := AutPSp.exists_conj_elt_of_rootInvolution (K := GaloisField 2 f) (ψ := ψs) hr
  rcases RCSTSp.elt_one_eq_conj (F := GaloisField 2 f) ρ with ⟨g, i, hgi⟩ | ⟨g, i, j, hij, hgij⟩
  · let ψ' : StatedSp n (GaloisField 2 f) →* G := ψs.comp (MulAut.conj (w * g)).toMonoidHom
    have hψ'inj : Function.Injective ψ' := RCSTSp.comp_conj_injective hψ (w * g)
    have hrange : ψ'.range = ψs.range := RCSTSp.range_comp_conj ψs (w * g)
    have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
      rw [hrange]
      exact hC
    have hx : ψ' (siegDiag (GaloisField 2 f) i 1) = r := by
      have h1 : g * siegDiag (GaloisField 2 f) i 1 * g⁻¹ =
          Symplectic.SpExtras.elt ρ (1 : GaloisField 2 f) := hgi.symm
      have h2 : (w * g) * siegDiag (GaloisField 2 f) i 1 * (w * g)⁻¹ =
          w * Symplectic.SpExtras.elt ρ (1 : GaloisField 2 f) * w⁻¹ := by
        calc (w * g) * siegDiag (GaloisField 2 f) i 1 * (w * g)⁻¹ =
            w * (g * siegDiag (GaloisField 2 f) i 1 * g⁻¹) * w⁻¹ := by group
          _ = w * Symplectic.SpExtras.elt ρ (1 : GaloisField 2 f) * w⁻¹ := by rw [h1]
      change ψs ((w * g) * siegDiag (GaloisField 2 f) i 1 * (w * g)⁻¹) = r
      rw [h2, hw, map_mul, map_mul, map_inv]
    have h := pCoreOf_le_range_of_siegDiag (by omega) ψ' hψ'inj hC' i
    rw [hx, hrange] at h
    exact h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    obtain ⟨g', hg'⟩ := RCSTSp.exists_conj_one_two (F := GaloisField 2 f) (n := m) hij
    let ψ' : StatedSp (m + 3) (GaloisField 2 f) →* G :=
      ψs.comp (MulAut.conj (w * g * g')).toMonoidHom
    have hψ'inj : Function.Injective ψ' := RCSTSp.comp_conj_injective hψ (w * g * g')
    have hrange : ψ'.range = ψs.range := RCSTSp.range_comp_conj ψs (w * g * g')
    have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
      rw [hrange]
      exact hC
    have hx : ψ' (twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1) = r := by
      have h1 : (g * g') * twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1 * (g * g')⁻¹ =
          Symplectic.SpExtras.elt ρ (1 : GaloisField 2 f) := by
        calc (g * g') * twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1 * (g * g')⁻¹ =
            g * (g' * twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1 * g'⁻¹) * g⁻¹ := by
              group
          _ = g * twoCentralElt (m + 3) i j (0 : GaloisField 2 f) 1 * g⁻¹ := by rw [hg']
          _ = Symplectic.SpExtras.elt ρ (1 : GaloisField 2 f) := hgij.symm
      have h2 : (w * g * g') * twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1 *
          (w * g * g')⁻¹ = w * Symplectic.SpExtras.elt ρ (1 : GaloisField 2 f) * w⁻¹ := by
        calc (w * g * g') * twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1 * (w * g * g')⁻¹ =
            w * ((g * g') * twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1 * (g * g')⁻¹) *
              w⁻¹ := by group
          _ = w * Symplectic.SpExtras.elt ρ (1 : GaloisField 2 f) * w⁻¹ := by rw [h1]
      change ψs ((w * g * g') * twoCentralElt (m + 3) 1 2 (0 : GaloisField 2 f) 1 *
        (w * g * g')⁻¹) = r
      rw [h2, hw, map_mul, map_mul, map_inv]
    have h := pCoreOf_le_range_of_twoCentralElt (m := m) ψ' hψ'inj hC'
    rw [hx, hrange] at h
    exact h

end Tags

end CFSG.StandardType
