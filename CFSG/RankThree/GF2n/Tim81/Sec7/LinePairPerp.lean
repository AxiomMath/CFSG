module

public import CFSG.RankThree.GF2n.Tim81.Sec7.LinePairFrame
public import CFSG.Timmesfeld.Transvection.ModelSUBlock
import CFSG.Timmesfeld.Transvection.ModelSUGen
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryPerpCount

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.LieEmbed CFSG.Timmesfeld.Transvection CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree
open scoped MatrixGroups commutatorElement

namespace SUTrans

variable {F : Type} [Field F] {σ : F ≃+* F} {K : Type} [Group K] {m : ℕ}

private theorem midExt_ne_zero {v : Fin m → F} (hv : v ≠ 0) : midExt v ≠ 0 := by
  intro h
  apply hv
  funext j
  simpa only [midExt_mid, Pi.zero_apply] using congrFun h (mid j)

private theorem midExt_mem_perpPair (v : Fin m → F) :
    midExt v ∈ perpPair σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1) := by
  rw [mem_perpPair_ends]
  exact ⟨midExt_last v, midExt_zero_apply v⟩

private theorem mem_perpRoots_comp_iotaHom_iff [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) (hm : 2 ≤ m) (hm2 : 2 ≤ m + 2)
    {Φ : SU σ (m + 2) →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ (m + 2)))
    {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub (Unitary.rootGroup σ hσ (m + 2)
      (unitaryLongRoot (m + 2) hm2)) x).map Φ)
    {T₀ T₁ : Subgroup (SU σ (m + 2))}
    (hT₀ : IsUTransGroup σ (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup σ (Pi.single (Fin.last (m + 1)) 1) T₁) :
    ∀ U, U ∈ {C | C ∈ Δ ∧
        C ≤ Subgroup.centralizer ((T₀.map Φ ⊔ T₁.map Φ : Subgroup K) : Set K)} ↔
      ∃ x, U = (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map
        (Φ.comp iotaHom) := by
  intro U
  constructor
  · rintro ⟨hUΔ, hUle⟩
    obtain ⟨u, T, hu, huu, hT, rfl⟩ := exists_eq_map_of_mem hσ hm2 hΔ hUΔ
    have hP : u ∈ perpPair σ (Pi.single 0 1) (Pi.single (Fin.last (m + 1)) 1) :=
      mem_perpPair_of_map_le_centralizer hσ hker hT hu huu hT₀ hT₁ hUle
    have hu0 : u 0 = 0 := ((mem_perpPair_ends (σ := σ)).mp hP).2
    have hul : u (Fin.last (m + 1)) = 0 := ((mem_perpPair_ends (σ := σ)).mp hP).1
    set z : Fin m → F := u ∘ mid with hz
    have huz : midExt z = u := by
      rw [hz]
      exact midExt_comp_mid hu0 hul
    have hz0 : z ≠ 0 := by
      intro h0
      apply hu
      rw [← huz, h0, midExt_zero]
    have hzz : uForm σ z z = 0 := by
      rw [← uForm_midExt (σ := σ) z z, huz, huu]
    obtain ⟨Tz, hTz⟩ := exists_isUTransGroup hσ hzz
    have hTz' : IsUTransGroup σ u (Tz.map iotaHom) := by
      rw [← huz]
      exact isUTransGroup_map_iotaHom hTz
    have hTeq : T = Tz.map iotaHom := hT.eq hTz'
    obtain ⟨x, hx⟩ := exists_eq_conjSub_rootGroup hσ htr hm hz0 hzz hTz
    refine ⟨x, ?_⟩
    rw [hTeq, Subgroup.map_map, hx]
  · rintro ⟨x, rfl⟩
    have hroot : IsUTransGroup σ
        (Pi.single (lowIdx (⟨m / 2 - 1, by omega⟩ : Fin (m / 2))) 1)
        (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) :=
      isUTransGroup_rootGroup_unitaryLongRoot (m := m) hσ hm
    set z : Fin m → F :=
      suMat σ m x *ᵥ Pi.single (lowIdx (⟨m / 2 - 1, by omega⟩ : Fin (m / 2))) 1 with hz
    have hconj : IsUTransGroup σ z
        (conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x) := by
      rw [hz]
      exact hroot.conjSub x
    have hz0 : z ≠ 0 := suMat_mulVec_ne_zero σ x (single_one_ne_zero _)
    have hzz : uForm σ z z = 0 := by
      rw [hz, uForm_mulVec, uForm_single_self (lowIdx_ne_rev _ _)]
    have hmid : IsUTransGroup σ (midExt z)
        ((conjSub (Unitary.rootGroup σ hσ m (unitaryLongRoot m hm)) x).map iotaHom) :=
      isUTransGroup_map_iotaHom hconj
    refine ⟨?_, ?_⟩
    · rw [← Subgroup.map_map]
      exact map_mem hσ htr hm2 hΔ (midExt_ne_zero hz0)
        (by rw [uForm_midExt, hzz]) hmid
    · rw [← Subgroup.map_map]
      exact map_le_centralizer_ends hσ Φ hmid hT₀ hT₁ (midExt_mem_perpPair z)

private theorem comp_iotaHom_range_le_perpRoots [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c)
    (htr : ∀ a, unitaryInvolution F 2 f a = a → ∃ c, c + unitaryInvolution F 2 f c = a)
    (hm : 2 ≤ m) (hm2 : 2 ≤ m + 2)
    {Φ : SU (unitaryInvolution F 2 f) (m + 2) →* K}
    {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f) hσ
      (m + 2) (unitaryLongRoot (m + 2) hm2)) x).map Φ)
    {T₀ T₁ : Subgroup (SU (unitaryInvolution F 2 f) (m + 2))}
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup (unitaryInvolution F 2 f)
      (Pi.single (Fin.last (m + 1)) 1) T₁) :
    (Φ.comp iotaHom).range ≤ perpRoots Δ (T₀.map Φ ⊔ T₁.map Φ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2f : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hm3 : (m, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h' : 2 ^ f = 2 := by simpa using congrArg Prod.snd h
    omega
  rw [MonoidHom.range_eq_map,
    ← ModelRank.closure_uTrans_eq_top (p := 2) (f := f) hF hm hm3,
    MonoidHom.map_closure]
  refine (Subgroup.closure_le (perpRoots Δ (T₀.map Φ ⊔ T₁.map Φ))).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨v, c, hvv, hc, hx⟩ := hx
  by_cases hv : v = 0
  · have hx1 : x = 1 := suMat_injective (unitaryInvolution F 2 f) (by
      rw [hx, hv, map_one]
      simp [uTrans, uNil])
    have h1 : (Φ.comp iotaHom) x = 1 := by rw [hx1, map_one]
    rw [h1]
    exact Subgroup.one_mem _
  · obtain ⟨T, hT⟩ := exists_isUTransGroup hσ hvv
    have hxT : x ∈ T := (hT.1 x).2 ⟨c, hc, hx⟩
    have hmid : IsUTransGroup (unitaryInvolution F 2 f) (midExt v) (T.map iotaHom) :=
      isUTransGroup_map_iotaHom hT
    have hle := map_le_perpRoots hσ htr hm2 hΔ hmid (midExt_ne_zero hv)
      (by rw [uForm_midExt, hvv]) hT₀ hT₁ (midExt_mem_perpPair v)
    exact hle (Subgroup.mem_map_of_mem Φ
      (Subgroup.mem_map_of_mem iotaHom hxT))

theorem comp_iotaHom_perpRoots [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f)
    (hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c)
    (hm : 2 ≤ m) (hm2 : 2 ≤ m + 2)
    {Φ : SU (unitaryInvolution F 2 f) (m + 2) →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 2)))
    {Δ : Set (Subgroup K)}
    (hΔ : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f) hσ
      (m + 2) (unitaryLongRoot (m + 2) hm2)) x).map Φ)
    {T₀ T₁ : Subgroup (SU (unitaryInvolution F 2 f) (m + 2))}
    (hT₀ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single 0 1) T₀)
    (hT₁ : IsUTransGroup (unitaryInvolution F 2 f) (Pi.single (Fin.last (m + 1)) 1) T₁) :
    (Φ.comp iotaHom).ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) ∧
      (Φ.comp iotaHom).range = perpRoots Δ (T₀.map Φ ⊔ T₁.map Φ) ∧
      ∀ U, U ∈ {C | C ∈ Δ ∧
          C ≤ Subgroup.centralizer ((T₀.map Φ ⊔ T₁.map Φ : Subgroup K) : Set K)} ↔
        ∃ x, U = (conjSub (Unitary.rootGroup (unitaryInvolution F 2 f) hσ m
          (unitaryLongRoot m hm)) x).map (Φ.comp iotaHom) := by
  have htr : ∀ a, unitaryInvolution F 2 f a = a → ∃ c, c + unitaryInvolution F 2 f c = a :=
    fun a ha => exists_add_unitaryInvolution_eq hF ha
  have hk : (Φ.comp iotaHom).ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) m) := by
    rw [← MonoidHom.comap_ker]
    exact (Subgroup.comap_mono hker).trans (Subgroup.comap_center_le_center
      (iotaHom_injective (σ := unitaryInvolution F 2 f) (m := m)))
  refine ⟨hk, le_antisymm (comp_iotaHom_range_le_perpRoots hF hf hσ htr hm hm2 hΔ hT₀ hT₁) ?_,
    mem_perpRoots_comp_iotaHom_iff hσ htr hm hm2 hker hΔ hT₀ hT₁⟩
  refine iSup₂_le ?_
  rintro U ⟨hUΔ, hUle⟩
  obtain ⟨x, hx⟩ := (mem_perpRoots_comp_iotaHom_iff hσ htr hm hm2 hker hΔ hT₀ hT₁ U).1
    ⟨hUΔ, hUle⟩
  rw [hx]
  exact Subgroup.map_le_range (Φ.comp iotaHom) _

end SUTrans

theorem IsSUImage.isSUImage_perpRoots {K : Type} [Group K] {X₀ : Subgroup K}
    {Δ : Set (Subgroup K)} {f n : ℕ} {hf : 1 ≤ f} {hn : 2 ≤ n} (hX : IsSUImage X₀ Δ f n hf hn)
    (hf2 : 2 ≤ f) (h5 : 5 ≤ n) {A B : Subgroup K} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hAB : IsL2Gen A B) :
    IsSUImage (perpRoots Δ (A ⊔ B))
      {C | C ∈ Δ ∧ C ≤ Subgroup.centralizer ((A ⊔ B : Subgroup K) : Set K)}
      f (n - 2) hf (Nat.le_sub_of_add_le (Nat.le_trans (Nat.le_succ 4) h5)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let F := GaloisField 2 (2 * f)
  let σ : F ≃+* F := unitaryInvolution F 2 f
  have hF : Nat.card F = (2 ^ f) ^ 2 := card_galoisField_two_mul hf
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  obtain ⟨Ψ, hker, -, hΔ, T₀, T₁, hT₀, hT₁, hA', hB'⟩ :=
    hX.exists_frame (m := m) hA hB hAB.commutator_ne_bot
  have hΔ' : ∀ U, U ∈ Δ ↔ ∃ x, U = (conjSub (Unitary.rootGroup σ hσ (m + 2)
      (unitaryLongRoot (m + 2) (by omega))) x).map Ψ := hΔ
  have hm : 2 ≤ m := by omega
  have hm2 : 2 ≤ m + 2 := by omega
  obtain ⟨hk, hr, hcorr⟩ :=
    SUTrans.comp_iotaHom_perpRoots hF hf2 hσ hm hm2 hker hΔ' hT₀ hT₁
  refine ⟨Ψ.comp iotaHom, hk, ?_, ?_⟩
  · rw [hr, hA', hB']
  · intro U
    rw [hA', hB', hcorr U]
    exact Iff.rfl

end CFSG.RankThree.GF2n.Tim81
