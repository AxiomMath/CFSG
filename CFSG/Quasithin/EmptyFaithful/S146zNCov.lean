module

public import CFSG.Quasithin.EmptyFaithful.S146zNIrr5Def
public import CFSG.Quasithin.EmptyFaithful.S146zNKer
public import CFSG.Quasithin.EmptyFaithful.S146yA6Gen
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.S146zNBrG

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Cov

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem a6c_isElemAbelian_of_le {U V : Subgroup G} (hU : IsElemAbelian 2 U) (hVU : V ≤ U) :
    IsElemAbelian 2 V := CFSG.Open.IsElemAbelian.mono hU hVU

omit [Finite G] in
theorem a6c_nontriv {Z U₁ K : Subgroup G} (hgen : ⁅U₁, K⁆ ⊔ Z = U₁) (hlt : mIdx U₁ Z ≠ 0) :
    ∃ k ∈ K, ∃ e ∈ U₁, k * e * k⁻¹ * e⁻¹ ∉ Z := by
  by_contra hcon
  push Not at hcon
  have h1 : ⁅U₁, K⁆ ≤ Z := by
    rw [Subgroup.commutator_le]
    intro a ha k hk
    have := hcon k hk a ha
    have e : ⁅a, k⁆ = (k * a * k⁻¹ * a⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ this
  have h2 : U₁ ≤ Z := calc U₁ = ⁅U₁, K⁆ ⊔ Z := hgen.symm
    _ ≤ Z := sup_le h1 le_rfl
  have h3 : Z.relIndex U₁ = 1 := Subgroup.relIndex_eq_one.mpr h2
  apply hlt
  unfold mIdx
  rw [h3]
  simp

theorem a6c_not_irr (hNo : A6NoIrr5) {Z U₁ K : Subgroup G} (hKA : KbarIsA6 K)
    (hab : IsElemAbelian 2 U₁) (hZU : Z ≤ U₁) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U₁ : Set G)) (h5 : mIdx U₁ Z = 5) (hgen : ⁅U₁, K⁆ ⊔ Z = U₁)
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Z) :
    ¬ (∀ W : Subgroup G, Z ≤ W → W ≤ U₁ → K ≤ Subgroup.normalizer (W : Set G) →
      W = Z ∨ W = U₁) := by
  intro hirr
  have hU₁N : U₁ ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_forall_commute fun w hw z hz => isElemAbelian_comm hab hw (hZU hz)
  have hU₁2 : IsPGroup 2 U₁ := isPGroup_of_isElemAbelian hab
  have hsimple : IsSimpleGroup (KBar K) := isSimpleGroup_kbar_of_kbarIsA6 hKA
  have hnt := a6c_nontriv hgen (by omega)
  have hker : centralizerMod Z K U₁ = pCoreOf 2 K := by
    refine le_antisymm (a6k_centralizerMod_le hKZ hKU hsimple hQ hnt) ?_
    intro p hp
    exact ⟨pCoreOf_le 2 K hp, hKZ (pCoreOf_le 2 K hp), fun e he => hQ p hp e he⟩
  have hc : ∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ Z := fun x hx y hy => by
    have : x * y * x⁻¹ * y⁻¹ = 1 := by rw [isElemAbelian_comm hab hx hy]; group
    rw [this]; exact Z.one_mem
  have hsq : ∀ x ∈ U₁, x ^ 2 ∈ Z := fun x hx => by
    rw [hab.2 x hx]; exact Z.one_mem
  have hV : IsElemAbelian 2 (tildeOf Z U₁) := isElemAbelian_secImg_normalizer hc hsq
  let _ : CommGroup ↥(tildeOf Z U₁) := commGroupOfElemAbelian hV
  refine hNo ↥(tildeOf Z U₁) (fun v => Subtype.ext (by simpa using hV.2 v v.2))
    (by rw [a6g_card_tilde hZU hU₁N hU₁2 h5]; norm_num)
    (autOn (tildeOf Z K) (tildeOf Z U₁)) (a6g_nonempty_equiv hKZ hKU hU₁N hker hKA) ?_
  intro S hS
  have hS' : S.map (tildeOf Z U₁).subtype ≤ tildeOf Z U₁ := by
    rintro _ ⟨s, -, rfl⟩
    exact s.2
  have key : ∀ y ∈ tildeOf Z K, ∀ h ∈ S.map (tildeOf Z U₁).subtype,
      y * h * y⁻¹ ∈ S.map (tildeOf Z U₁).subtype := by
    intro y hy h hh
    obtain ⟨s, hs, rfl⟩ := hh
    have hyN : y ∈ Subgroup.normalizer (tildeOf Z U₁ : Set _) :=
      secImg_le_normalizer_secImg hKU hy
    have hl : conjAct (tildeOf Z U₁) ⟨y, hyN⟩ ∈ autOn (tildeOf Z K) (tildeOf Z U₁) :=
      Subgroup.mem_map.mpr ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have h1 := hS _ hl s hs
    refine ⟨_, h1, ?_⟩
    simp only [Subgroup.subtype_apply]
    exact conjAct_apply_coe' (tildeOf Z U₁) ⟨y, hyN⟩ s
  have hKS : tildeOf Z K ≤ Subgroup.normalizer ((S.map (tildeOf Z U₁).subtype : Subgroup _) :
      Set _) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key y hy h hh, fun hh => ?_⟩
    have := key y⁻¹ (Subgroup.inv_mem _ hy) _ hh
    simpa [mul_assoc] using this
  rcases a6g_irr hZU hKZ hirr hS' hKS with h | h
  · left
    refine eq_bot_iff.mpr fun s hs => ?_
    have : (s : SecQuot (Subgroup.normalizer (Z : Set G)) Z) ∈ S.map (tildeOf Z U₁).subtype :=
      ⟨s, hs, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · right
    refine eq_top_iff.mpr fun s _ => ?_
    have : (s : SecQuot (Subgroup.normalizer (Z : Set G)) Z) ∈ S.map (tildeOf Z U₁).subtype := by
      rw [h]; exact s.2
    obtain ⟨s', hs', hss'⟩ := this
    have : s' = s := Subtype.ext hss'
    rwa [← this]

theorem a6c_cov (hNo : A6NoIrr5) {Z U₁ K : Subgroup G} (hKA : KbarIsA6 K)
    (hab : IsElemAbelian 2 U₁) (hZU : Z ≤ U₁) (hKZ : K ≤ Subgroup.normalizer (Z : Set G))
    (hKU : K ≤ Subgroup.normalizer (U₁ : Set G)) (h5 : mIdx U₁ Z = 5) (hgen : ⁅U₁, K⁆ ⊔ Z = U₁)
    (hQ : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ Z) :
    mIdx U₁ (centralizerMod Z U₁ K) = 4 ∧
      ∀ W : Subgroup G, centralizerMod Z U₁ K ≤ W → W ≤ U₁ →
        K ≤ Subgroup.normalizer (W : Set G) → W = centralizerMod Z U₁ K ∨ W = U₁ := by
  classical
  have hU₁2 : IsPGroup 2 U₁ := isPGroup_of_isElemAbelian hab
  have hF₁U : centralizerMod Z U₁ K ≤ U₁ := centralizerMod_le_left _ _ _
  have hKF₁ : K ≤ Subgroup.normalizer ((centralizerMod Z U₁ K : Subgroup G) : Set G) :=
    le_normalizer_centralizerMod hKZ hKU Subgroup.le_normalizer
  have hZF : Z ≤ centralizerMod Z U₁ K := fun z hz => by
    refine ⟨hZU hz, Subgroup.le_normalizer hz, fun u hu => ?_⟩
    have h1 : u * z⁻¹ * u⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hKZ hu) z⁻¹).mp
      (Subgroup.inv_mem _ hz)
    have e : z * u * z⁻¹ * u⁻¹ = z * (u * z⁻¹ * u⁻¹) := by group
    rw [e]
    exact Z.mul_mem hz h1
  have hge : ∀ W : Subgroup G, Z ≤ W → W ≤ U₁ → K ≤ Subgroup.normalizer (W : Set G) → W ≠ U₁ →
      4 ≤ mIdx U₁ W := by
    intro W hZW hWU hKW hne
    by_contra h
    push Not at h
    have hlt : W.relIndex U₁ < 16 := by
      rw [HypF98.relIndex_eq_two_pow_mIdx (Y := W) hU₁2]
      calc 2 ^ mIdx U₁ W ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ < 16 := by norm_num
    exact hne (eq_of_relIndex_lt_sixteen hKA hab hZW hWU hgen hKU hKW hQ hlt)
  have hfix : mIdx U₁ (centralizerMod Z U₁ K) ≥ 4 := by
    by_cases hF : centralizerMod Z U₁ K = U₁
    · exfalso
      obtain ⟨k, hk, e, he, hne⟩ := a6c_nontriv hgen (by omega)
      apply hne
      have h1 : e ∈ centralizerMod Z U₁ K := by rw [hF]; exact he
      have h2 := h1.2.2 k hk
      have e' : k * e * k⁻¹ * e⁻¹ = (e * k * e⁻¹ * k⁻¹)⁻¹ := by group
      rw [e']
      exact Subgroup.inv_mem _ h2
    · exact hge _ hZF hF₁U hKF₁ hF
  have hnot := a6c_not_irr hNo hKA hab hZU hKZ hKU h5 hgen hQ
  push Not at hnot
  obtain ⟨W₀, hZW₀, hW₀U, hKW₀, hW₀Z, hW₀U'⟩ := hnot
  have hW₀2 : IsPGroup 2 W₀ := hU₁2.to_le hW₀U
  have h4W := hge W₀ hZW₀ hW₀U hKW₀ hW₀U'
  have hadd := ThreeC.mIdx_add hU₁2 hW₀U hZW₀
  have hposW : 0 < mIdx W₀ Z :=
    mIdx_pos_of_lt_of_isPGroup hW₀2 (lt_of_le_of_ne hZW₀ (Ne.symm hW₀Z))
  have h1W : mIdx W₀ Z = 1 := by omega
  have hrel : Z.relIndex W₀ ∣ 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx (Y := Z) hW₀2, h1W]
    norm_num
  obtain ⟨a₀, ha₀W, ha₀⟩ := Subgroup.relIndex_dvd_two_iff.mp hrel
  have ha₀Z : a₀ ∉ Z := by
    intro h
    apply hW₀Z
    refine le_antisymm (fun b hb => ?_) hZW₀
    rcases ha₀ b hb with h' | h'
    · simpa using Z.mul_mem h' (Z.inv_mem h)
    · exact h'
  have hU₁N : U₁ ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_forall_commute fun w hw z hz => isElemAbelian_comm hab hw (hZU hz)
  have ha₀F : a₀ ∈ centralizerMod Z U₁ K := by
    refine ⟨hW₀U ha₀W, hU₁N (hW₀U ha₀W), fun u hu => ?_⟩
    have hk : u * a₀ * u⁻¹ ∈ W₀ := (Subgroup.mem_normalizer_iff.mp (hKW₀ hu) a₀).mp ha₀W
    rcases ha₀ _ hk with h | h
    · have ha2 : a₀ * a₀ = 1 := by
        have := hab.2 a₀ (hW₀U ha₀W)
        rwa [sq] at this
      have e : a₀ * u * a₀⁻¹ * u⁻¹ = ((u * a₀ * u⁻¹) * a₀)⁻¹ := by
        have : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha2
        simp [mul_inv_rev, this, mul_assoc]
      rw [e]
      exact Subgroup.inv_mem _ h
    · exact absurd ((Subgroup.mem_normalizer_iff.mp (hKZ hu) a₀).mpr h) ha₀Z
  have hlt1 : 0 < mIdx (centralizerMod Z U₁ K) Z :=
    mIdx_pos_of_lt_of_isPGroup (hU₁2.to_le hF₁U)
      (lt_of_le_of_ne hZF (fun h => ha₀Z (h ▸ ha₀F)))
  have hadd2 := ThreeC.mIdx_add hU₁2 hF₁U hZF
  have h4 : mIdx U₁ (centralizerMod Z U₁ K) = 4 := by omega
  refine ⟨h4, fun W hFW hWU hKW => ?_⟩
  by_cases hWU' : W = U₁
  · exact Or.inr hWU'
  · left
    have hZW : Z ≤ W := hZF.trans hFW
    have h4W := hge W hZW hWU hKW hWU'
    have hadd3 := ThreeC.mIdx_add hU₁2 hWU hFW
    have h0 : mIdx W (centralizerMod Z U₁ K) = 0 := by omega
    have hW2 : IsPGroup 2 W := hU₁2.to_le hWU
    have h1 : (centralizerMod Z U₁ K).relIndex W = 1 := by
      rw [HypF98.relIndex_eq_two_pow_mIdx (Y := centralizerMod Z U₁ K) hW2, h0]
      rfl
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hFW

end Cov

end CFSG.Quasithin
