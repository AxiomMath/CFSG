module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
public import CFSG.Timmesfeld.Transvection.ModelSULine
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryPerpCount
import CFSG.Timmesfeld.Transvection.ModelSUBlock
import CFSG.Timmesfeld.ARS.ConjSubComp
import CFSG.Timmesfeld.ARS.CaseMSU
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
open scoped MatrixGroups commutatorElement

namespace SUTrans

variable {F : Type} [Field F] {σ : F ≃+* F} {K : Type} [Group K] {m : ℕ}

private theorem uForm_single_zero_self :
    uForm σ (Pi.single (0 : Fin (m + 2)) 1) (Pi.single 0 1) = 0 :=
  uForm_single_self (by rw [Fin.rev_zero]; exact zero_ne_last)

private theorem uForm_single_last_self :
    uForm σ (Pi.single (Fin.last (m + 1)) 1) (Pi.single (Fin.last (m + 1)) 1) = 0 :=
  uForm_single_self (by rw [Fin.rev_last]; exact zero_ne_last.symm)

theorem exists_pairFrame [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) {Φ : SU σ (m + 2) →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ (m + 2))) (hm : 2 ≤ m + 2)
    {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub
      (Unitary.rootGroup σ hσ (m + 2) (unitaryLongRoot (m + 2) hm)) x).map Φ)
    {A B : Subgroup K} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : ⁅A, B⁆ ≠ ⊥) :
    ∃ Ψ : SU σ (m + 2) →* K, Ψ.ker ≤ Subgroup.center (SU σ (m + 2)) ∧
      Ψ.range = Φ.range ∧
      (∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub
        (Unitary.rootGroup σ hσ (m + 2) (unitaryLongRoot (m + 2) hm)) x).map Ψ) ∧
      ∃ T₀ T₁ : Subgroup (SU σ (m + 2)), IsUTransGroup σ (Pi.single 0 1) T₀ ∧
        IsUTransGroup σ (Pi.single (Fin.last (m + 1)) 1) T₁ ∧
        A = T₀.map Ψ ∧ B = T₁.map Ψ := by
  classical
  obtain ⟨v, Tv, hv, hvv, hTv, hAeq⟩ := exists_eq_map_of_mem hσ hm hΔ hA
  obtain ⟨w, Tw, hw, hww, hTw, hBeq⟩ := exists_eq_map_of_mem hσ hm hΔ hB
  have hvw : uForm σ v w ≠ 0 := by
    intro hzero
    apply hAB
    rw [hAeq, hBeq]
    exact (commutator_map_eq_bot_iff hσ hker hTv hTw hv hvv hww).2 hzero
  set d : Fin (m + 2) → F := (uForm σ v w)⁻¹ • w with hd
  have hdd : uForm σ d d = 0 := by
    rw [hd, uForm_smul_left, uForm_smul_right, hww, mul_zero, mul_zero]
  have hvd : uForm σ v d = 1 := by
    rw [hd, uForm_smul_right, inv_mul_cancel₀ hvw]
  obtain ⟨T₀, hT₀⟩ := exists_isUTransGroup hσ uForm_single_zero_self
  obtain ⟨T₁, hT₁⟩ := exists_isUTransGroup hσ uForm_single_last_self
  obtain ⟨x, l, hl, hx0, hxL⟩ := exists_suMat_mulVec_eq_pair hσ htr hvv hdd hvd
  have hT₀conj : conjSub T₀ x = Tv := by
    have h := hT₀.conjSub x
    rw [hx0] at h
    exact (IsUTransGroup.of_smul hσ hl h).eq hTv
  have hT₁conj : conjSub T₁ x = Tw := by
    have h := hT₁.conjSub x
    rw [hxL] at h
    have hc : (σ l)⁻¹ * (uForm σ v w)⁻¹ ≠ 0 :=
      mul_ne_zero (inv_ne_zero ((map_ne_zero σ).2 hl)) (inv_ne_zero hvw)
    have h' : IsUTransGroup σ (((σ l)⁻¹ * (uForm σ v w)⁻¹) • w) (conjSub T₁ x) := by
      rwa [hd, smul_smul] at h
    exact (IsUTransGroup.of_smul hσ hc h').eq hTw
  let Ψ : SU σ (m + 2) →* K := Φ.comp (MulAut.conj x).toMonoidHom
  refine ⟨Ψ, CaseMSU.ker_comp_conj_le_center hker x, range_comp_conj Φ x, ?_, T₀, T₁,
    hT₀, hT₁, ?_, ?_⟩
  · intro U
    rw [hΔ U]
    exact (exists_eq_map_conjSub_comp_conj_iff Φ
      (Unitary.rootGroup σ hσ (m + 2) (unitaryLongRoot (m + 2) hm)) x U).symm
  · rw [hAeq, ← hT₀conj]
    change (T₀.map (MulAut.conj x).toMonoidHom).map Φ = T₀.map Ψ
    rw [Subgroup.map_map]
  · rw [hBeq, ← hT₁conj]
    change (T₁.map (MulAut.conj x).toMonoidHom).map Φ = T₁.map Ψ
    rw [Subgroup.map_map]

theorem map_le_centralizer_ends (hσ : ∀ c, σ (σ c) = c) (Φ : SU σ (m + 2) →* K)
    {u : Fin (m + 2) → F} {T T₀ T₁ : Subgroup (SU σ (m + 2))}
    (hT : IsUTransGroup σ u T) (hT₀ : IsUTransGroup σ (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single (Fin.last (m + 1)) 1) T₁)
    (hu : u ∈ perpPair σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1)) :
    T.map Φ ≤ Subgroup.centralizer ((T₀.map Φ ⊔ T₁.map Φ : Subgroup K) : Set K) := by
  have h0 : Commuting T T₀ := hT.commuting hσ hT₀ (uForm_eq_zero_comm hσ hu.1)
  have h1 : Commuting T T₁ := hT.commuting hσ hT₁ (uForm_eq_zero_comm hσ hu.2)
  have hcomm : Commuting (T.map Φ) (T₀.map Φ ⊔ T₁.map Φ) := by
    rw [← Subgroup.map_sup]
    exact commuting_map Φ (commuting_sup h0 h1)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hcomm x hx y hy).eq.symm

theorem mem_perpPair_of_map_le_centralizer [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {Φ : SU σ (m + 2) →* K} (hker : Φ.ker ≤ Subgroup.center (SU σ (m + 2)))
    {u : Fin (m + 2) → F} {T T₀ T₁ : Subgroup (SU σ (m + 2))}
    (hT : IsUTransGroup σ u T) (hu : u ≠ 0) (huu : uForm σ u u = 0)
    (hT₀ : IsUTransGroup σ (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single (Fin.last (m + 1)) 1) T₁)
    (hle : T.map Φ ≤ Subgroup.centralizer
      ((T₀.map Φ ⊔ T₁.map Φ : Subgroup K) : Set K)) :
    u ∈ perpPair σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1) := by
  constructor
  · have h0 : ⁅T.map Φ, T₀.map Φ⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hle.trans (Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_left hx))
    exact uForm_eq_zero_comm hσ
      ((commutator_map_eq_bot_iff hσ hker hT hT₀ hu huu uForm_single_zero_self).1 h0)
  · have h1 : ⁅T.map Φ, T₁.map Φ⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hle.trans (Subgroup.centralizer_le (fun x hx => Subgroup.mem_sup_right hx))
    exact uForm_eq_zero_comm hσ
      ((commutator_map_eq_bot_iff hσ hker hT hT₁ hu huu uForm_single_last_self).1 h1)

theorem map_le_perpRoots [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) (hm : 2 ≤ m + 2) {Φ : SU σ (m + 2) →* K}
    {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub
      (Unitary.rootGroup σ hσ (m + 2) (unitaryLongRoot (m + 2) hm)) x).map Φ)
    {u : Fin (m + 2) → F} {T T₀ T₁ : Subgroup (SU σ (m + 2))}
    (hT : IsUTransGroup σ u T) (hu : u ≠ 0) (huu : uForm σ u u = 0)
    (hT₀ : IsUTransGroup σ (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single (Fin.last (m + 1)) 1) T₁)
    (hP : u ∈ perpPair σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1)) :
    T.map Φ ≤ perpRoots Δ (T₀.map Φ ⊔ T₁.map Φ) := by
  refine le_iSup₂_of_le (T.map Φ) ⟨map_mem hσ htr hm hΔ hu huu hT,
    map_le_centralizer_ends hσ Φ hT hT₀ hT₁ hP⟩ le_rfl

theorem commute_of_mem_centralizer_perpRoots [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) (hm : 2 ≤ m + 2) {Φ : SU σ (m + 2) →* K}
    {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub
      (Unitary.rootGroup σ hσ (m + 2) (unitaryLongRoot (m + 2) hm)) x).map Φ)
    {T₀ T₁ : Subgroup (SU σ (m + 2))}
    (hT₀ : IsUTransGroup σ (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single (Fin.last (m + 1)) 1) T₁)
    {y : K} (hy : y ∈ Subgroup.centralizer
      ((perpRoots Δ (T₀.map Φ ⊔ T₁.map Φ) : Subgroup K) : Set K)) :
    ∀ u ∈ perpPair σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1),
      uForm σ u u = 0 → ∀ t : SU σ (m + 2),
        suMat σ (m + 2) t = uTrans σ u 1 → y * Φ t = Φ t * y := by
  intro u hu huu t ht
  by_cases hu0 : u = 0
  · have ht1 : suMat σ (m + 2) t = 1 := by
      rw [ht, hu0]
      simp [uTrans, uNil]
    have ht' : t = 1 := suMat_injective σ (by rw [ht1, map_one])
    rw [ht']
    simp
  · obtain ⟨T, hT⟩ := exists_isUTransGroup hσ huu
    have hmem : Φ t ∈ T.map Φ :=
      Subgroup.mem_map_of_mem Φ ((hT.1 t).mpr ⟨1, by rw [map_one]; exact CharTwo.add_self_eq_zero 1,
        ht⟩)
    exact (Subgroup.mem_centralizer_iff.mp hy (Φ t)
      (map_le_perpRoots hσ htr hm hΔ hT hu0 huu hT₀ hT₁ hu hmem)).symm

theorem exists_mem_lineSL_of_mem_sup [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (Φ : SU σ (m + 2) →* K) {T₀ T₁ : Subgroup (SU σ (m + 2))}
    (hT₀ : IsUTransGroup σ (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single (Fin.last (m + 1)) 1) T₁) {h : K}
    (hh : h ∈ T₀.map Φ ⊔ T₁.map Φ) :
    ∃ s ∈ lineSL σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1), Φ s = h := by
  have hle : T₀ ⊔ T₁ ≤ lineSL σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1) :=
    sup_le (le_lineSL_of_isUTransGroup_left uForm_single_zero_self uForm_single_zero_last hT₀)
      (le_lineSL_of_isUTransGroup_right hσ uForm_single_last_self uForm_single_zero_last hT₁)
  rw [← Subgroup.map_sup, Subgroup.mem_map] at hh
  obtain ⟨s, hs, hsh⟩ := hh
  exact ⟨s, hle hs, hsh⟩

theorem commutator_eq_bot_of_mem_normalizer [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c)
    {Φ : SU (unitaryInvolution F 2 f) (m + 2) →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 2)))
    (hm : 2 ≤ m + 2) {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f) hσ
      (m + 2) (unitaryLongRoot (m + 2) hm)) x).map Φ)
    {T₀ T₁ : Subgroup (SU (unitaryInvolution F 2 f) (m + 2))}
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single (Fin.last (m + 1)) 1) T₁)
    {h : K} (hh : h ∈ T₀.map Φ ⊔ T₁.map Φ) (hord : orderOf h = 2 ^ f + 1)
    {C : Subgroup K} (hC : C ∈ Δ) (hhC : h ∈ Subgroup.normalizer (C : Set K)) :
    ⁅C, T₀.map Φ ⊔ T₁.map Φ⁆ = ⊥ := by
  classical
  have htr : ∀ a, unitaryInvolution F 2 f a = a → ∃ c, c + unitaryInvolution F 2 f c = a :=
    fun a ha => exists_add_unitaryInvolution_eq hF ha
  obtain ⟨s, hs, hΦs⟩ := exists_mem_lineSL_of_mem_sup hσ Φ hT₀ hT₁ hh
  obtain ⟨u, T, hu, huu, hT, hCeq⟩ := exists_eq_map_of_mem hσ hm hΔ hC
  have hconj : conjSubgroup h C = C :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).1 hhC
  have hconj' : conjSubgroup (Φ s) (T.map Φ) = T.map Φ := by
    rw [← hΦs, hCeq] at hconj
    exact hconj
  have hbase : (conjSub T s).map Φ = T.map Φ :=
    (map_conjSubgroup Φ s T).trans hconj'
  have hTconj : IsUTransGroup (unitaryInvolution F 2 f)
      (suMat (unitaryInvolution F 2 f) (m + 2) s *ᵥ u) (conjSub T s) := hT.conjSub s
  have hsu : suMat (unitaryInvolution F 2 f) (m + 2) s *ᵥ u ≠ 0 :=
    suMat_mulVec_ne_zero (unitaryInvolution F 2 f) s hu
  have hsuu : uForm (unitaryInvolution F 2 f)
      (suMat (unitaryInvolution F 2 f) (m + 2) s *ᵥ u)
      (suMat (unitaryInvolution F 2 f) (m + 2) s *ᵥ u) = 0 := by
    rw [uForm_mulVec, huu]
  obtain ⟨l, hl⟩ := (map_eq_map_iff hσ htr hker hT hTconj hu hsu huu hsuu).1 hbase.symm
  by_cases hup : u ∈ perpPair (unitaryInvolution F 2 f)
      (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1)
  · rw [hCeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact map_le_centralizer_ends hσ Φ hT hT₀ hT₁ hup
  · exfalso
    exact (mulVec_ne_smul_of_orderOf hF hf Φ uForm_single_zero_self uForm_single_last_self
      uForm_single_zero_last hs (by rw [hΦs]; exact hord) huu hup l) hl

end SUTrans

theorem IsSUImage.exists_frame {K : Type} [Group K] {X₀ : Subgroup K} {Δ : Set (Subgroup K)}
    {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m + 2} (hX : IsSUImage X₀ Δ f (m + 2) hf hm)
    {A B : Subgroup K} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : ⁅A, B⁆ ≠ ⊥) :
    ∃ Ψ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 2) →* K,
      Ψ.ker ≤ Subgroup.center _ ∧ Ψ.range = X₀ ∧
      (∀ U : Subgroup K, U ∈ Δ ↔ ∃ x, U = (conjSub ((Unitary.rootDatum
        (card_galoisField_two_mul hf) (m + 2)).rootGroup (unitaryLongRoot (m + 2) hm)) x).map Ψ) ∧
      ∃ T₀ T₁ : Subgroup (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 2)),
        IsUTransGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (Pi.single 0 1) T₀ ∧
        IsUTransGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
          (Pi.single (Fin.last (m + 1)) 1) T₁ ∧ A = T₀.map Ψ ∧ B = T₁.map Ψ := by
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  let F := GaloisField 2 (2 * f)
  let σ : F ≃+* F := unitaryInvolution F 2 f
  have hF : Nat.card F = (2 ^ f) ^ 2 := card_galoisField_two_mul hf
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have htr : ∀ a, σ a = a → ∃ c, c + σ c = a := fun a ha => exists_add_unitaryInvolution_eq hF ha
  have hΔ' : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub
      (Unitary.rootGroup σ hσ (m + 2) (unitaryLongRoot (m + 2) hm)) x).map Φ := hΔ
  obtain ⟨Ψ, hkerΨ, hrangeΨ, hΔΨ, T₀, T₁, hT₀, hT₁, hAΨ, hBΨ⟩ :=
    SUTrans.exists_pairFrame hσ htr hker hm hΔ' hA hB hAB
  refine ⟨Ψ, hkerΨ, hrangeΨ.trans hrange, ?_, T₀, T₁, hT₀, hT₁, hAΨ, hBΨ⟩
  intro U
  rw [hΔΨ U]
  exact Iff.rfl

theorem IsSUImage.commutator_eq_bot_of_mem_normalizer {K : Type} [Group K] {X₀ : Subgroup K}
    {Δ : Set (Subgroup K)} {f n : ℕ} {hf : 1 ≤ f} {hn : 2 ≤ n} (hX : IsSUImage X₀ Δ f n hf hn)
    (hf2 : 2 ≤ f) {A B : Subgroup K} (hA : A ∈ Δ) (hB : B ∈ Δ) (hAB : IsL2Gen A B) {h : K}
    (hh : h ∈ A ⊔ B) (hord : orderOf h = 2 ^ f + 1) {C : Subgroup K} (hC : C ∈ Δ)
    (hhC : h ∈ Subgroup.normalizer (C : Set K)) : ⁅C, A ⊔ B⁆ = ⊥ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let F := GaloisField 2 (2 * f)
  let σ : F ≃+* F := unitaryInvolution F 2 f
  have hF : Nat.card F = (2 ^ f) ^ 2 := card_galoisField_two_mul hf
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  obtain ⟨Ψ, hker, -, hΔ, T₀, T₁, hT₀, hT₁, hAΨ, hBΨ⟩ :=
    hX.exists_frame (m := m) hA hB hAB.commutator_ne_bot
  have hΔ' : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub (Unitary.rootGroup σ hσ
      (m + 2) (unitaryLongRoot (m + 2) (by omega))) x).map Ψ := hΔ
  have hh' : h ∈ T₀.map Ψ ⊔ T₁.map Ψ := by rw [← hAΨ, ← hBΨ]; exact hh
  have hres := SUTrans.commutator_eq_bot_of_mem_normalizer hF hf2 hσ hker (by omega) hΔ'
    hT₀ hT₁ hh' hord hC hhC
  simpa only [hAΨ, hBΨ] using hres

end CFSG.RankThree.GF2n.Tim81
