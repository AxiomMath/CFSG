module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts36K
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModCoord
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldElementary

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups Pointwise
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField (Gamma gammaToMulAut gammaToMulAut_inl
  even_SL2_full_automorphism_semilinear_model original_outer_elementary_card_and_rank linearKernel
  mem_linearKernel_iff char_two_of_card)

theorem factL2Offender_holds : FactL2Offender := by
  intro U _ _ _ Hs Gm P e he4 hGm hP hPN hGP hO A hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨ι⟩⟩ := hGm
  obtain ⟨hAHs, hA1, ⟨hAc, hAsq⟩, hAfix⟩ := hA
  have : Finite (MulAut U) :=
    Finite.of_injective (fun f : MulAut U => (f : U → U)) DFunLike.coe_injective
  have : CharP F 2 := char_two_of_card hF
  have hGmHs : Gm ≤ Hs := le_sup_left.trans hGP.le
  have hA2 : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hAsq a a.2)⟩
  have hAcard : 2 ^ e ≤ Nat.card A := by
    have h1 := E3.relIndex_eq_two_pow hA2 ⊥
    rw [Subgroup.relIndex_bot_left] at h1
    rw [h1]
    apply Nat.pow_le_pow_right (by norm_num)
    by_contra hlt
    push Not at hlt
    have hfix := hAfix ⊥ bot_le hlt
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    ext v
    have hv : v ∈ fixV (⊥ : Subgroup (MulAut U)) := fun x hx => by
      rw [Subgroup.mem_bot.mp hx]
      rfl
    rw [hfix] at hv
    exact hv a ha
  have hHsN : Hs ≤ Subgroup.normalizer (Gm : Set (MulAut U)) := by
    rw [← hGP]
    exact sup_le Subgroup.le_normalizer hPN
  set C : Subgroup (MulAut U) := Hs ⊓ Subgroup.centralizer (Gm : Set (MulAut U)) with hCdef
  have hCGm : ∀ c ∈ C, c ∈ Gm → c = 1 := by
    intro c hc hcG
    have hcent : ι ⟨c, hcG⟩ ∈ Subgroup.center SL(2, F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := ι.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hc.2 g' g'.2
    have h1 := H13.eq_one_of_mem_center hcent
    have h2 : (⟨c, hcG⟩ : ↥Gm) = 1 := ι.injective (h1.trans (map_one ι).symm)
    exact congrArg Subtype.val h2
  have hC2 : IsPGroup 2 C := by
    rintro ⟨c, hc⟩
    have hcHs : c ∈ Hs := hc.1
    rw [← hGP] at hcHs
    have hmem : c ∈ (Gm : Set (MulAut U)) * (P : Set (MulAut U)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Gm P hPN]
      exact hcHs
    obtain ⟨g, hg, p, hp, hgp⟩ := hmem
    obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
    have hpk : p ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcomm : Commute g⁻¹ c := Subgroup.mem_centralizer_iff.mp hc.2 g⁻¹ (inv_mem hg)
    have hp' : p = g⁻¹ * c := by
      rw [← hgp]
      group
    have hck : c ^ 2 ^ k = g ^ 2 ^ k := by
      have h1 : (g⁻¹ * c) ^ 2 ^ k = 1 := by rw [← hp']; exact hpk
      rw [hcomm.mul_pow, inv_pow] at h1
      exact (inv_mul_eq_one.mp h1).symm
    have hcN : c ^ 2 ^ k ∈ C := pow_mem hc _
    have hgN : c ^ 2 ^ k ∈ Gm := by
      rw [hck]
      exact pow_mem hg _
    refine ⟨k, Subtype.ext ?_⟩
    simpa using hCGm _ hcN hgN
  have hHsC : Hs ≤ Subgroup.normalizer (C : Set (MulAut U)) := by
    intro h hh
    apply H13.mem_normalizer_of_conj_mem
    intro c hc
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hh (Subgroup.mem_inf.mp hc).1) (inv_mem hh), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : h⁻¹ * g * h ∈ Gm := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hHsN hh)) g).mp hg
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ hg'
    calc g * (h * c * h⁻¹) = h * ((h⁻¹ * g * h) * c) * h⁻¹ := by group
      _ = h * (c * (h⁻¹ * g * h)) * h⁻¹ := by rw [h1]
      _ = h * c * h⁻¹ * g := by group
  have hCbot : C = ⊥ := by
    have hle : C ≤ pCoreOf 2 Hs :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hHsC hC2
    rw [hO] at hle
    exact le_bot_iff.mp hle
  set θ : ↥Hs →* MulAut ↥Gm := Gm.normalizerMonoidHom.comp (Subgroup.inclusion hHsN) with hθ
  have hθv : ∀ (h : ↥Hs) (g : ↥Gm),
      ((θ h g : ↥Gm) : MulAut U) = (h : MulAut U) * g * (h : MulAut U)⁻¹ :=
    fun h g => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro h hθh
    have hhC : (h : MulAut U) ∈ C := by
      refine Subgroup.mem_inf.mpr ⟨h.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := congrArg (fun φ : MulAut ↥Gm => ((φ ⟨g, hg⟩ : ↥Gm) : MulAut U)) hθh
      simp only [hθv] at h1
      have h2 : (h : MulAut U) * g * (h : MulAut U)⁻¹ = g := h1
      calc g * (h : MulAut U) = ((h : MulAut U) * g * (h : MulAut U)⁻¹) * h := by rw [h2]
        _ = h * g := by group
    rw [hCbot] at hhC
    exact Subtype.ext (Subgroup.mem_bot.mp hhC)
  obtain ⟨hbij, -⟩ := even_SL2_full_automorphism_semilinear_model (by omega : 1 ≤ e) hF
  set eΓ : Gamma F ≃* MulAut SL(2, F) := MulEquiv.ofBijective (gammaToMulAut F) hbij with heΓ
  set Θ : ↥Hs →* Gamma F :=
    eΓ.symm.toMonoidHom.comp ((MulAut.congr ι).toMonoidHom.comp θ) with hΘdef
  have hΘinj : Function.Injective Θ :=
    eΓ.symm.injective.comp ((MulAut.congr ι).injective.comp hθinj)
  have hΘ : ∀ h, gammaToMulAut F (Θ h) = MulAut.congr ι (θ h) := fun h =>
    eΓ.apply_symm_apply _
  set A' : Subgroup (Gamma F) := (A.subgroupOf Hs).map Θ with hA'def
  have hA'card : Nat.card A' = Nat.card A := by
    rw [hA'def, Subgroup.card_map_of_injective hΘinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAHs).toEquiv
  have hA'comm : ∀ x : ↥A', ∀ y : ↥A', x * y = y * x := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
    apply Subtype.ext
    change Θ x * Θ y = Θ y * Θ x
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hAc _ hx _ hy
  have hA'sq : ∀ x : ↥A', x ^ 2 = 1 := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    apply Subtype.ext
    change Θ x ^ 2 = 1
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by simpa using hAsq _ hx)
    rw [this, map_one]
  have : CFSG.IsElementaryAbelian 2 A' :=
    { is_comm := ⟨hA'comm⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hA'sq }
  have hlin : ∀ a (ha : a ∈ A), (Θ ⟨a, hAHs ha⟩).right = 1 := by
    intro a ha
    by_contra hne
    have hmem : Θ ⟨a, hAHs ha⟩ ∈ A' := ⟨⟨a, hAHs ha⟩, ha, rfl⟩
    have hout : Θ ⟨a, hAHs ha⟩ ∉ linearKernel F := by
      rw [mem_linearKernel_iff]
      exact hne
    obtain ⟨s, -, hes, -, -, -, -, -, hcard, -, -, -⟩ :=
      original_outer_elementary_card_and_rank (by omega) hF A' _ hmem hout
    rw [hA'card] at hcard
    have h1 : 2 ^ e ≤ 2 ^ (s + 1) := hAcard.trans hcard
    have h2 : e ≤ s + 1 := by
      by_contra hlt
      push Not at hlt
      exact absurd h1 (not_le.mpr (Nat.pow_lt_pow_right (by norm_num) hlt))
    omega
  have hAGm : A ≤ Gm := by
    intro a ha
    set γ := Θ ⟨a, hAHs ha⟩ with hγdef
    have hγr : γ.right = 1 := hlin a ha
    have hγ : γ = SemidirectProduct.inl γ.left := by
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right γ]
      rw [hγr, map_one, mul_one]
    have h1 : MulAut.congr ι (θ ⟨a, hAHs ha⟩) = MulAut.conj γ.left := by
      rw [← hΘ, ← hγdef, hγ, gammaToMulAut_inl, SemidirectProduct.left_inl]
    set g₀ : ↥Gm := ι.symm γ.left with hg₀
    have h2 : ∀ g : ↥Gm,
        ((θ ⟨a, hAHs ha⟩ g : ↥Gm) : MulAut U) = (g₀ : MulAut U) * g * (g₀ : MulAut U)⁻¹ := by
      intro g
      have h3 := congrArg (fun φ : MulAut SL(2, F) => φ (ι g)) h1
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.conj_apply] at h3
      have h4 : θ ⟨a, hAHs ha⟩ g = g₀ * g * g₀⁻¹ := by
        apply ι.injective
        rw [h3, map_mul, map_mul, map_inv, hg₀, MulEquiv.apply_symm_apply]
      rw [h4]
      rfl
    have hC' : (g₀ : MulAut U)⁻¹ * a ∈ C := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hGmHs g₀.2)) (hAHs ha), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h5 : a * g * a⁻¹ = (g₀ : MulAut U) * g * (g₀ : MulAut U)⁻¹ := by
        have := h2 ⟨g, hg⟩
        rw [hθv] at this
        exact this
      calc g * ((g₀ : MulAut U)⁻¹ * a) =
          (g₀ : MulAut U)⁻¹ * ((g₀ : MulAut U) * g * (g₀ : MulAut U)⁻¹) * a := by group
        _ = (g₀ : MulAut U)⁻¹ * (a * g * a⁻¹) * a := by rw [h5]
        _ = (g₀ : MulAut U)⁻¹ * a * g := by group
    rw [hCbot, Subgroup.mem_bot] at hC'
    have hag : a = g₀ := by
      calc a = (g₀ : MulAut U) * ((g₀ : MulAut U)⁻¹ * a) := by group
        _ = g₀ := by rw [hC', mul_one]
    rw [hag]
    exact g₀.2
  have hGmcard : Nat.card Gm = 2 ^ e * (4 ^ e - 1) := by
    rw [Nat.card_congr ι.toEquiv]
    exact Vol2.Ch10.SecA.card_SL_two_pow hF
  have hodd : Odd (4 ^ e - 1) := Vol2.Ch10.SecA.odd_four_pow_sub_one (by omega)
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := 2)).mp hA2
  have hAdvd : Nat.card A ∣ Nat.card Gm := Subgroup.card_dvd_of_le hAGm
  rw [hr, hGmcard] at hAdvd
  have hre : r ≤ e := by
    have hcop : Nat.Coprime (2 ^ r) (4 ^ e - 1) :=
      Nat.Coprime.pow_left r (Nat.coprime_two_left.mpr hodd)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (hcop.dvd_of_dvd_mul_right hAdvd)
  have hAe : Nat.card A = 2 ^ e :=
    le_antisymm (by rw [hr]; exact Nat.pow_le_pow_right (by norm_num) hre) hAcard
  refine ⟨hAGm, ⟨hAGm, hA2, ?_⟩, hAe⟩
  have hidx := Subgroup.card_mul_index (A.subgroupOf Gm)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAGm).toEquiv, hAe, hGmcard] at hidx
  have hidx' : (A.subgroupOf Gm).index = 4 ^ e - 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity) hidx
  rw [hidx']
  exact Nat.not_even_iff_odd.mpr hodd ∘ even_iff_two_dvd.mpr

end CFSG.Quasithin.Vol2.Ch11.SecB
