module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2V1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2FixSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2FixOmega
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.Quasithin.Background.C41PfT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem s16c167_stable_of_realizes {W : Type} [CommGroup W] {D : FFModel}
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (h : D.Realizes H U Z) : StableUnder H U := by
  obtain ⟨π, -, -, -, hU, -⟩ := h
  exact fun x hx u hu => hU ⟨x, hx⟩ u hu

theorem s16c167_stable_natSpn {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {n a : ℕ} (h : NatSpn H U Z n a) : StableUnder H U := by
  obtain ⟨-, K, instK, instFin, -, r⟩ := h
  exact s16c167_stable_of_realizes r

theorem s16c167_stable_natOmegaMinus {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {n a : ℕ} (h : NatOmegaMinus H U Z n a) : StableUnder H U := by
  obtain ⟨-, K, instK, instFin, b, c, -, -, r⟩ := h
  exact s16c167_stable_of_realizes r

theorem s16c167_sumOfNat_two {W : Type} [CommGroup W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    (h : SumOfNat N H ⊤ ⊥ 2) :
    ∃ J₀ J₁ : Subgroup W, N H J₀ ⊥ ∧ N H J₁ ⊥ ∧ J₀ ⊓ J₁ = ⊥ ∧ J₀ ⊔ J₁ = ⊤ := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  have hrest : ∀ i j : Fin 2, i ≠ j → (⨆ (k : Fin 2) (_ : k ≠ i), I k) = I j := by
    intro i j hij
    refine le_antisymm (iSup₂_le fun k hk => ?_) (le_iSup₂ (f := fun k (_ : k ≠ i) => I k) j
      (Ne.symm hij))
    have : k = j := by omega
    rw [this]
  refine ⟨I 0, I 1, hnat 0, hnat 1, ?_, ?_⟩
  · have h0 := hind 0
    rw [hrest 0 1 (by decide), bot_sup_eq] at h0
    exact le_bot_iff.1 h0
  · have hall : (⨆ i, I i) = I 0 ⊔ I 1 := by
      refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    rw [hall, bot_sup_eq] at hsup
    exact hsup

theorem s16c167_fixV_eq_bot_of_two {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (hs₀ : StableUnder H J₀) (hs₁ : StableUnder H J₁)
    (hf₀ : J₀ ⊓ fixV H = ⊥) (hf₁ : J₁ ⊓ fixV H = ⊥) (hi : J₀ ⊓ J₁ = ⊥) (hj : J₀ ⊔ J₁ = ⊤) :
    fixV H = ⊥ := by
  refine le_bot_iff.1 fun x hx => ?_
  have hxsup : x ∈ J₀ ⊔ J₁ := by rw [hj]; exact Subgroup.mem_top x
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hxsup
  have hy_eq : ∀ h : MulAut W, h ∈ H → h y = y := by
    intro h hh
    have h1 : h y * h z = y * z := by
      rw [← map_mul]
      exact (mem_fixV.1 hx) h hh
    have hcomm : (h y)⁻¹ * y = h z * z⁻¹ := by
      have h2 : h z = (h y)⁻¹ * (y * z) := by rw [← h1]; group
      rw [h2]; group
    have hmem : (h y)⁻¹ * y ∈ J₀ ⊓ J₁ := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact Subgroup.mul_mem J₀ (Subgroup.inv_mem J₀ (hs₀ h hh y hy)) hy
      · rw [hcomm]
        exact Subgroup.mul_mem J₁ (hs₁ h hh z hz) (Subgroup.inv_mem J₁ hz)
    have hmem' : (h y)⁻¹ * y ∈ (⊥ : Subgroup W) := by rw [← hi]; exact hmem
    exact inv_mul_eq_one.1 (Subgroup.mem_bot.1 hmem')
  have hz_eq : ∀ h : MulAut W, h ∈ H → h z = z := by
    intro h hh
    have h1 : h y * h z = y * z := by
      rw [← map_mul]
      exact (mem_fixV.1 hx) h hh
    rw [hy_eq h hh] at h1
    exact mul_left_cancel_iff.1 h1
  have hyfix : y ∈ fixV H := mem_fixV.2 hy_eq
  have hzfix : z ∈ fixV H := mem_fixV.2 hz_eq
  have hybot : y ∈ (⊥ : Subgroup W) := by
    rw [← hf₀]
    exact Subgroup.mem_inf.2 ⟨hy, hyfix⟩
  have hzbot : z ∈ (⊥ : Subgroup W) := by
    rw [← hf₁]
    exact Subgroup.mem_inf.2 ⟨hz, hzfix⟩
  rw [Subgroup.mem_bot.1 hybot, Subgroup.mem_bot.1 hzbot, one_mul]
  exact Subgroup.one_mem (⊥ : Subgroup W)

theorem s16c167_cfg2_fix_alt {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U : Subgroup W} {n : ℕ} (hn : 5 ≤ n) (h : AlternatingNatural H U ⊥ n) :
    U ⊓ fixV H = ⊥ := by
  have hn0 : 0 < n := by omega
  obtain ⟨π, hπ⟩ := h
  obtain ⟨-, -, -, hUinv, -, hsecinv, -, β, -, hβker, hβeq⟩ := hπ
  let e : (↥(G6.coreMod n) ⧸ (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec) ≃*
      Multiplicative (AltHeart n) := CFSG.Quasithin.C124.altQuotEquiv n hn0
  let β' : ↥U →* Multiplicative (AltHeart n) := e.toMonoidHom.comp β
  have hstab : ∀ x : ↥H, ∀ u ∈ U, (x : MulAut W) u ∈ U := hUinv
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥U) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  have hβinj' : Function.Injective β' := e.injective.comp hβinj
  have hβe' : ∀ (γ : ↥(alternatingGroup (Fin n))) (u : ↥U)
      (hu : ((π γ : ↥H) : MulAut W) (u : W) ∈ U),
      β' ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
          (Multiplicative.toAdd (β' u))) := by
    intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) ∈
        (FFModel.altDn n).sec := hsecinv γ m m.2
    have h1 := hβeq γ u m hu hsec hmu
    change e (β ⟨((π γ : ↥H) : MulAut W) (u : W), hu⟩) =
      Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct n (γ : Equiv.Perm (Fin n))
        (Multiplicative.toAdd (e (β u))))
    rw [h1, hmu]
    rfl
  refine le_bot_iff.1 fun w hw => ?_
  obtain ⟨hwU, hwfix⟩ := Subgroup.mem_inf.1 hw
  have hbeta : β' ⟨w, hwU⟩ = 1 := by
    have h2 : Multiplicative.toAdd (β' ⟨w, hwU⟩) = 0 := by
      apply CFSG.Quasithin.C41Pf.AltN.heart_fixed_eq_zero (by omega)
      intro σ hσ
      have hfixw : ((π ⟨σ, hσ⟩ : ↥H) : MulAut W) w = w :=
        (mem_fixV.1 hwfix) _ (π ⟨σ, hσ⟩).2
      have h3 := hβe' ⟨σ, hσ⟩ ⟨w, hwU⟩ (hstab (π ⟨σ, hσ⟩) w hwU)
      have h4 : β' ⟨((π ⟨σ, hσ⟩ : ↥H) : MulAut W) w,
          hstab (π ⟨σ, hσ⟩) w hwU⟩ = β' ⟨w, hwU⟩ := congrArg β' (Subtype.ext hfixw)
      have h5 := congrArg Multiplicative.toAdd (h3.symm.trans h4)
      simpa using h5
    exact Multiplicative.toAdd.injective (by simpa using h2)
  have h6 : (⟨w, hwU⟩ : ↥U) = 1 := hβinj' (by rw [hbeta]; exact (map_one β').symm)
  simpa using congrArg Subtype.val h6

variable {G : Type} [Group G] [Finite G]

theorem s16c167_cfg2_fix (D : Data G) {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} (h2 : Case168_2 D V₀ V hV L) : fixV (lBar V₀ V hV L) = ⊥ := by
  obtain ⟨-, ⟨L₀, -, hfam⟩, -⟩ := h2
  rcases hfam with ⟨n, hn5, -, -, -, hsum⟩ | ⟨m, hm3, -, -, -, hsum⟩ | ⟨-, -, hsum⟩ |
    ⟨-, -, hsum⟩ | ⟨-, -, hsum⟩
  · obtain ⟨J₀, J₁, h₀, h₁, hi, hj⟩ := s16c167_sumOfNat_two hsum
    exact s16c167_fixV_eq_bot_of_two (s16c167_stable_of_realizes h₀)
      (s16c167_stable_of_realizes h₁) (s16c167_cfg2_fix_alt hn5 h₀)
      (s16c167_cfg2_fix_alt hn5 h₁) hi hj
  · have := s16c167_inf_fixV_eq_bot_of_sumOfNat (by omega : 2 ≤ m) hsum
    rwa [top_inf_eq] at this
  · obtain ⟨J₀, J₁, h₀, h₁, hi, hj⟩ := s16c167_sumOfNat_two hsum
    exact s16c167_fixV_eq_bot_of_two (s16c167_stable_natSpn h₀) (s16c167_stable_natSpn h₁)
      (s16c167_cfg2_fix_sp (by norm_num) h₀) (s16c167_cfg2_fix_sp (by norm_num) h₁) hi hj
  · obtain ⟨J₀, J₁, h₀, h₁, hi, hj⟩ := s16c167_sumOfNat_two hsum
    exact s16c167_fixV_eq_bot_of_two (s16c167_stable_natOmegaMinus h₀)
      (s16c167_stable_natOmegaMinus h₁) (s16c167_cfg2_fix_omegaMinus (Or.inl rfl) h₀)
      (s16c167_cfg2_fix_omegaMinus (Or.inl rfl) h₁) hi hj
  · obtain ⟨J₀, J₁, h₀, h₁, hi, hj⟩ := s16c167_sumOfNat_two hsum
    exact s16c167_fixV_eq_bot_of_two (s16c167_stable_natOmegaMinus h₀)
      (s16c167_stable_natOmegaMinus h₁) (s16c167_cfg2_fix_omegaMinus (Or.inr rfl) h₀)
      (s16c167_cfg2_fix_omegaMinus (Or.inr rfl) h₁) hi hj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
