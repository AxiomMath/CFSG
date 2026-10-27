module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Par
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3WInner
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Para
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
import CFSG.Quasithin.H13.NQCatRkOneProd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotSpan
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl
import CFSG.Quasithin.Vol2.Ch12Sec5FinC
import TauCeti.Algebra.Group.Subgroup.Pointwise
public import CFSG.LargeExtraspecial.S5Comp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_e3_l3_inner_normalizes_sylow_inf {W : Type} [Group W]
    {T X : Subgroup (MulAut W)} {τ γ : MulAut W}
    (hτT : τ ∈ T) (hγX : γ ∈ X)
    (hact : ∀ l ∈ X, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    γ ∈ Subgroup.normalizer ((T ⊓ X : Subgroup (MulAut W)) : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact ⟨by
        rw [← hact y hy.2]
        exact T.mul_mem (T.mul_mem hτT hy.1) (T.inv_mem hτT),
      X.mul_mem (X.mul_mem hγX hy.2) (X.inv_mem hγX)⟩
  · intro hy
    have hyX : y ∈ X := by
      have : y = γ⁻¹ * (γ * y * γ⁻¹) * γ := by group
      rw [this]
      exact X.mul_mem (X.mul_mem (X.inv_mem hγX) hy.2) hγX
    have hmemT : τ * y * τ⁻¹ ∈ T := by
      rw [hact y hyX]
      exact hy.1
    have heqT : y = τ⁻¹ * (τ * y * τ⁻¹) * τ := by group
    exact ⟨by
        rw [heqT]
        exact T.mul_mem (T.mul_mem (T.inv_mem hτT) hmemT) hτT,
      hyX⟩

private theorem s16h_e3_l3_map_conj_eq_of_inner_on {W : Type} [Group W]
    {X P : Subgroup (MulAut W)} {τ γ : MulAut W}
    (hPX : P ≤ X)
    (hact : ∀ l ∈ X, τ * l * τ⁻¹ = γ * l * γ⁻¹) (hγP : γ ∈ P) :
    P.map (MulAut.conj τ).toMonoidHom = P := by
  have hγnormP : P.map (MulAut.conj γ).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hγP)
  have hτγ : P.map (MulAut.conj τ).toMonoidHom = P.map (MulAut.conj γ).toMonoidHom := by
    apply le_antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact Subgroup.mem_map.mpr ⟨p, hp, (hact p (hPX hp)).symm⟩
    · rintro x ⟨p, hp, rfl⟩
      exact Subgroup.mem_map.mpr ⟨p, hp, (hact p (hPX hp))⟩
  rw [hτγ, hγnormP]

private theorem s16h_e3_l3_pow_three_of_pow_twelve {W : Type} [Group W]
    {x : W} {n : ℕ} (h12 : x ^ 12 = 1) (h3 : x ^ 3 ^ n = 1) : x ^ 3 = 1 := by
  have hdvd : orderOf x ∣ Nat.gcd 12 (3 ^ n) :=
    Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr h12) (orderOf_dvd_iff_pow_eq_one.mpr h3)
  have hg : Nat.gcd 12 (3 ^ n) ∣ 3 := by
    obtain ⟨k, hk, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (Nat.gcd_dvd_right 12 (3 ^ n))
    rw [hk_eq]
    have hk1 : k ≤ 1 := by
      by_contra h
      have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      have hgcd12 : 3 ^ k ∣ 12 := by
        rw [← hk_eq]
        exact Nat.gcd_dvd_left 12 (3 ^ n)
      have h12' : 3 ^ 2 ∣ 12 := h9.trans hgcd12
      norm_num at h12'
    simpa using pow_dvd_pow 3 hk1
  exact orderOf_dvd_iff_pow_eq_one.mp (hdvd.trans hg)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_sl_three_orbit_three_parabolic
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hs : s15 D.M V₀ V hV L = 3)
    (hrow : s16h_H5L3Sum (lBar V₀ V hV L)
      (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    T3Parab
      (⨆ g : ↥(Mbar D.M V₀ V hV),
        (lBar V₀ V hV L).map
          (MulAut.conj (g : MulAut (Vtil V₀ V hV))).toMonoidHom)
      (barSub V₀ V hV D.T) 3 := by
  classical
  set W := Vtil V₀ V hV
  set A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  set H : Subgroup (MulAut W) := lBar V₀ V hV L
  set T : Subgroup (MulAut W) := barSub V₀ V hV D.T
  set B : Subgroup (MulAut W) :=
    ⨆ g : A, H.map (MulAut.conj (g : MulAut W)).toMonoidHom
  set O : Set (Subgroup (MulAut W)) := conjSet H A
  let I : Type := ↥O
  let F : I → Subgroup (MulAut W) := fun i => i.1
  have hcardI : Nat.card I = 3 := by
    change Nat.card ↥O = 3
    rw [Nat.card_coe_set_eq]
    simpa [O, A, H, W, s15, lBar, Mbar, conjSet] using hs
  have hfinI : Finite I := Nat.finite_of_card_ne_zero (by rw [hcardI]; norm_num)
  have : Fintype I := Fintype.ofFinite I
  have hex (i : I) : ∃ g : A, F i = H.map (MulAut.conj (g : MulAut W)).toMonoidHom := by
    obtain ⟨g, hg, hX⟩ := i.2
    exact ⟨⟨g, hg⟩, hX⟩
  let gOf (i : I) : A := Classical.choose (hex i)
  have hFOf (i : I) : F i = H.map (MulAut.conj (gOf i : MulAut W)).toMonoidHom :=
    Classical.choose_spec (hex i)
  have hFcomp : ∀ i : I, IsComponentOf (F i) A := by
    intro i
    rw [hFOf i]
    exact CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hcomp (gOf i).2
  have hne : ∀ i j : I, i ≠ j → F i ≠ F j := by
    intro i j hij h
    exact hij (Subtype.ext h)
  have hcomm : Pairwise fun i j : I =>
      ∀ x y : MulAut W, x ∈ F i → y ∈ F j → Commute x y := by
    intro i j hij x y hx hy
    exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne
      (hFcomp i) (hFcomp j) (hne i j hij) hx hy
  have hHIsL3 : IsL3 ↥H 1 := s16k_isLn_of_isSLn (by norm_num) hrow.1
  have hHcard : Nat.card ↥H = 168 := card_eq_of_isL3 hHIsL3
  let eFi (i : I) : ↥(F i) ≃* ↥H :=
    ((Subgroup.equivMapOfInjective H (MulAut.conj (gOf i : MulAut W)).toMonoidHom
        (MulAut.conj (gOf i : MulAut W)).injective).trans
      (MulEquiv.subgroupCongr (hFOf i).symm)).symm
  have hFiSL (i : I) : IsSLn ↥(F i) 3 1 := by
    obtain ⟨K, hF, hfin, hcard, ⟨eX⟩⟩ := hrow.1
    exact ⟨K, hF, hfin, hcard, ⟨(eFi i).trans eX⟩⟩
  have hFiL3 (i : I) : IsL3 ↥(F i) 1 :=
    s16k_isLn_of_isSLn (by norm_num) (hFiSL i)
  have hFicard (i : I) : Nat.card ↥(F i) = 168 := card_eq_of_isL3 (hFiL3 i)
  have hFicenter (i : I) : Subgroup.center (F i) = ⊥ := center_eq_bot_of_isL3 (hFiL3 i)
  have hZ : ∀ j, ∀ x ∈ F j, (∀ y ∈ F j, Commute x y) → x = 1 := by
    intro j x hx hxc
    have hxcenter : (⟨x, hx⟩ : F j) ∈ Subgroup.center (F j) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((hxc y y.2).symm)
    rw [hFicenter j] at hxcenter
    have h1 := Subgroup.mem_bot.1 hxcenter
    simpa using congrArg Subtype.val h1
  have hind : iSupIndep F :=
    CFSG.Quasithin.H13.NQCat.RkOne.iSupIndep_of_commute F hcomm hZ
  obtain ⟨e, -⟩ := @CFSG.LocalCores.exists_mulEquiv_pi_iSup (MulAut W) _ I hfinI F hcomm hind
  have hB_eq : (⨆ i : I, F i) = B := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rw [hFOf i]
      exact le_iSup (fun g : A => H.map (MulAut.conj (g : MulAut W)).toMonoidHom) (gOf i)
    · refine iSup_le fun g => ?_
      exact le_iSup (fun i : I => F i)
        ⟨H.map (MulAut.conj (g : MulAut W)).toMonoidHom, ⟨g, g.2, rfl⟩⟩
  let eHmodel : (∀ i : I, F i) ≃* (I → ↥H) :=
    MulEquiv.piCongrRight (fun i => eFi i)
  let eB : ↥B ≃* (I → ↥H) :=
    ((e.trans (MulEquiv.subgroupCongr hB_eq)).symm).trans eHmodel
  have hBcard : Nat.card ↥B = 168 ^ 3 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_pi]
    have hprod : (∏ i : I, Nat.card ↥H) = 168 ^ Nat.card I := by
      calc (∏ i : I, Nat.card ↥H) = ∏ _ : I, 168 := by simp [hHcard]
        _ = 168 ^ Fintype.card I := by rw [Finset.prod_const, Finset.card_univ]
        _ = 168 ^ Nat.card I := by rw [Nat.card_eq_fintype_card]
    rw [hprod, hcardI]
  have hT : IsSylowIn 2 D.T D.M :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T A :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).2
      (s16c1_barSub_sylow c.m_le_stabTil hT)
  have hBA : B ≤ A := by
    refine iSup_le fun g => ?_
    calc H.map (MulAut.conj (g : MulAut W)).toMonoidHom
        ≤ A.map (MulAut.conj (g : MulAut W)).toMonoidHom := Subgroup.map_mono hcomp.1
      _ = A := Subgroup.mem_normalizer_iff_map_conj_eq.1
          (Subgroup.le_normalizer (H := A) g.2)
  have hAnormB : A ≤ Subgroup.normalizer (B : Set (MulAut W)) := by
    have hnormal : (B.subgroupOf A).Normal :=
      s15_semiBot_iSup_map_conj_normal hcomp.1
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).1 hnormal
  set S : Subgroup (MulAut W) := T ⊓ B
  have hSsylB : CFSG.ABGLocalTools.IsSylowOf 2 S B :=
    hTsyl.inf_of_le_normalizer hBA hAnormB
  have hfac168 : (168).factorization 2 = 3 := by
    have h1 : 2 ^ 3 ∣ 168 := by norm_num
    have h2 : ¬ 2 ^ 4 ∣ 168 := by norm_num
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)] at h1 h2
    omega
  have hScard : Nat.card S = 8 ^ 3 := by
    have hfac : (168 ^ 3).factorization 2 = 9 := by
      rw [Nat.factorization_pow]
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [hfac168]
    have h := hSsylB.card_eq
    rw [hBcard, hfac] at h
    norm_num at h
    exact h
  have hFiB : ∀ i : I, F i ≤ B := by
    intro i
    rw [← hB_eq]
    exact le_iSup F i
  have hBnormF : ∀ i : I, B ≤ Subgroup.normalizer (F i : Set (MulAut W)) := by
    intro i
    rw [← hB_eq]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · rw [hji]
      exact Subgroup.le_normalizer
    · intro y hy
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply le_antisymm
      · rintro z ⟨x, hx, rfl⟩
        have hc : y * x = x * y := hcomm hji y x hy hx
        have hEq : y * x * y⁻¹ = x := by rw [hc]; group
        simpa [MulAut.conj_apply, hEq] using hx
      · intro x hx
        refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
        have hc : y * x = x * y := hcomm hji y x hy hx
        have hEq : y * x * y⁻¹ = x := by rw [hc]; group
        simp [MulAut.conj_apply, hEq]
  let Si : I → Subgroup (MulAut W) := fun i => T ⊓ F i
  have hSi_eq : ∀ i : I, S ⊓ F i = Si i := by
    intro i
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1.1, hx.2⟩
    · intro x hx
      exact ⟨⟨hx.1, hFiB i hx.2⟩, hx.2⟩
  have hSiSyl : ∀ i : I, CFSG.ABGLocalTools.IsSylowOf 2 (Si i) (F i) := by
    intro i
    have h := hSsylB.inf_of_le_normalizer (hFiB i) (hBnormF i)
    rwa [hSi_eq i] at h
  have hSicard : ∀ i : I, Nat.card (Si i) = 8 := by
    intro i
    have h := (hSiSyl i).card_eq
    rw [hFicard i, hfac168] at h
    norm_num at h
    exact h
  let SiP : (i : I) → Subgroup ↥(F i) := fun i => (Si i).subgroupOf (F i)
  have hSiPcard : ∀ i : I, Nat.card (SiP i) = 8 := by
    intro i
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Si i ≤ F i)).toEquiv]
    exact hSicard i
  have hSiPp : ∀ i : I, IsPGroup 2 (SiP i) := by
    intro i
    exact (hSiSyl i).isPGroup.comap_subtype
  let act : T → I → I := fun t i =>
    ⟨(F i).map (MulAut.conj (t : MulAut W)).toMonoidHom,
      ⟨(t : MulAut W) * (gOf i : MulAut W), A.mul_mem (hTsyl.le t.2) (gOf i).2, by
        rw [hFOf i, Subgroup.map_conj_map_conj]⟩⟩
  have act_one : ∀ i : I, act 1 i = i := by
    intro i
    apply Subtype.ext
    change (F i).map (MulAut.conj (1 : MulAut W)).toMonoidHom = F i
    have h1 : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
      ext y
      simp
    rw [h1, Subgroup.map_id]
  have act_mul : ∀ (a b : T) (i : I), act (a * b) i = act a (act b i) := by
    intro a b i
    apply Subtype.ext
    change (F i).map (MulAut.conj ((a * b : T) : MulAut W)).toMonoidHom =
      ((F i).map (MulAut.conj (b : MulAut W)).toMonoidHom).map
        (MulAut.conj (a : MulAut W)).toMonoidHom
    rw [Subgroup.map_conj_map_conj]
    rfl
  let : MulAction T I :=
    { smul := act, one_smul := act_one, mul_smul := act_mul }
  have act_val : ∀ (t : T) (i : I), (↑(t • i) : Subgroup (MulAut W)) =
      (F i).map (MulAut.conj (t : MulAut W)).toMonoidHom := fun t i => rfl
  let Q : Type := MulAction.orbitRel.Quotient T I
  let qOf (i : I) : Q := Quotient.mk (MulAction.orbitRel T I) i
  let i0 (i : I) : I := Quotient.out (qOf i)
  have hexT : ∀ i : I, ∃ t : T, t • i0 i = i := by
    intro i
    have hq : Quotient.mk (MulAction.orbitRel T I) (i0 i) = qOf i := Quotient.out_eq (qOf i)
    obtain ⟨t, ht⟩ := Quotient.exact hq
    refine ⟨t⁻¹, ?_⟩
    rw [← ht, ← mul_smul, inv_mul_cancel, one_smul]
  let tOf (i : I) : T := Classical.choose (hexT i)
  have tOf_spec : ∀ i : I, tOf i • i0 i = i := fun i => Classical.choose_spec (hexT i)
  let X : Q → Subgroup (MulAut W) := fun q => F (Quotient.out q)
  have hXsubP : ∀ q : Q, IsPGroup 2 (SiP (Quotient.out q)) :=
    fun q => hSiPp (Quotient.out q)
  have hXsub8 : ∀ q : Q, Nat.card (SiP (Quotient.out q)) = 8 :=
    fun q => hSiPcard (Quotient.out q)
  have hP0exists : ∀ q : Q, ∃ P' : Subgroup ↥(X q),
      Subgroup.normalizer (SiP (Quotient.out q) : Set ↥(X q)) ≤ P' ∧
      Nat.card P' = 24 ∧ ∀ p ∈ P', p ^ 12 = 1 := by
    intro q
    exact s16h_e3_l3_parabolic_of_sylow (hFiSL (Quotient.out q))
      (hXsubP q) (hXsub8 q)
  let P0sub (q : Q) : Subgroup ↥(X q) := Classical.choose (hP0exists q)
  have hP0sub_spec : ∀ q : Q,
      Subgroup.normalizer (SiP (Quotient.out q) : Set ↥(X q)) ≤ P0sub q ∧
      Nat.card (P0sub q) = 24 ∧ ∀ p ∈ P0sub q, p ^ 12 = 1 :=
    fun q => Classical.choose_spec (hP0exists q)
  let P0 (q : Q) : Subgroup (MulAut W) := (P0sub q).map (X q).subtype
  have hP0leX : ∀ q : Q, P0 q ≤ X q := fun q => Subgroup.map_subtype_le (P0sub q)
  have hP0card : ∀ q : Q, Nat.card (P0 q) = 24 := by
    intro q
    change Nat.card ↥((P0sub q).map (X q).subtype) = 24
    rw [Subgroup.card_map_of_injective (X q).subtype_injective]
    exact (hP0sub_spec q).2.1
  have hP0pow : ∀ q : Q, ∀ p ∈ P0 q, p ^ 12 = 1 := by
    intro q p hp
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hp
    have h := (hP0sub_spec q).2.2 p' hp'
    simpa using congrArg (fun x : ↥(X q) => (x : MulAut W)) h
  have hP0norm : ∀ q : Q,
      Subgroup.normalizer (Si (Quotient.out q) : Set (MulAut W)) ⊓ X q ≤ P0 q := by
    intro q γ hγ
    have hγX : γ ∈ X q := hγ.2
    have hγN : γ ∈ Subgroup.normalizer (Si (Quotient.out q) : Set (MulAut W)) := hγ.1
    let γ' : ↥(X q) := ⟨γ, hγX⟩
    have hγN' : γ' ∈ Subgroup.normalizer
        (SiP (Quotient.out q) : Set ↥(X q)) := by
      rw [← Subgroup.subgroupOf_normalizer_eq
        (inf_le_right : Si (Quotient.out q) ≤ X q), Subgroup.mem_subgroupOf]
      exact hγN
    exact Subgroup.mem_map.mpr ⟨γ', (hP0sub_spec q).1 hγN', rfl⟩
  have hSileP0 : ∀ q : Q, Si (Quotient.out q) ≤ P0 q := by
    intro q
    exact (le_inf (Subgroup.le_normalizer) inf_le_right).trans (hP0norm q)
  have hInnerF : ∀ i : I, ∀ τ, τ ∈ Subgroup.normalizer (F i : Set (MulAut W)) →
      ∃ γ ∈ F i, ∀ l ∈ F i, τ * l * τ⁻¹ = γ * l * γ⁻¹ := by
    intro i τ hτN
    let g : MulAut W := gOf i
    have hτmap : (F i).map (MulAut.conj τ).toMonoidHom = F i :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hτN
    have hτ'N : g⁻¹ * τ * g ∈ Subgroup.normalizer (H : Set (MulAut W)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hcalc : ((H.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj τ).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
        calc ((H.map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj τ).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
            = ((F i).map (MulAut.conj τ).toMonoidHom).map
                (MulAut.conj g⁻¹).toMonoidHom := by rw [← hFOf i]
          _ = (F i).map (MulAut.conj g⁻¹).toMonoidHom := by rw [hτmap]
          _ = ((H.map (MulAut.conj g).toMonoidHom).map
                (MulAut.conj g⁻¹).toMonoidHom) := by rw [hFOf i]
          _ = H := by
            change g⁻¹ • (g • H) = H
            exact TauCeti.conj_inv_smul_smul g H
      have hinner : (H.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj τ).toMonoidHom = H.map (MulAut.conj (τ * g)).toMonoidHom :=
        Subgroup.map_conj_map_conj H g τ
      have h2 : ((H.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj τ).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom =
          H.map (MulAut.conj (g⁻¹ * τ * g)).toMonoidHom := by
        calc ((H.map (MulAut.conj g).toMonoidHom).map
              (MulAut.conj τ).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
            = (H.map (MulAut.conj (τ * g)).toMonoidHom).map
                (MulAut.conj g⁻¹).toMonoidHom := by rw [hinner]
          _ = H.map (MulAut.conj (g⁻¹ * (τ * g))).toMonoidHom :=
                Subgroup.map_conj_map_conj H (τ * g) g⁻¹
          _ = H.map (MulAut.conj (g⁻¹ * τ * g)).toMonoidHom := by
                congr 1
      change H.map (MulAut.conj (g⁻¹ * τ * g)).toMonoidHom = H
      rw [← h2]
      exact hcalc
    obtain ⟨γ', hγ'H, hγ'act⟩ :=
      s16h_e3_l3_normalizer_inner (s15_Infra_vtil_sq_eq_one V₀ V hV) hrow hτ'N
    refine ⟨g * γ' * g⁻¹, ?_, ?_⟩
    · rw [hFOf i]
      exact Subgroup.mem_map.mpr ⟨γ', hγ'H, rfl⟩
    · intro l hl
      rw [hFOf i] at hl
      obtain ⟨l', hl', rfl⟩ := Subgroup.mem_map.mp hl
      calc τ * (g * l' * g⁻¹) * τ⁻¹
          = g * ((g⁻¹ * τ * g) * l' * (g⁻¹ * τ * g)⁻¹) * g⁻¹ := by group
        _ = g * (γ' * l' * γ'⁻¹) * g⁻¹ := by rw [hγ'act l' hl']
        _ = (g * γ' * g⁻¹) * (g * l' * g⁻¹) * (g * γ' * g⁻¹)⁻¹ := by group
  have hP0stab : ∀ (q : Q) (u : T), u • (Quotient.out q) = Quotient.out q →
      (P0 q).map (MulAut.conj (u : MulAut W)).toMonoidHom = P0 q := by
    intro q u hu
    have huN : (u : MulAut W) ∈ Subgroup.normalizer (X q : Set (MulAut W)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact congrArg Subtype.val hu
    obtain ⟨γ, hγX, hγact⟩ := hInnerF (Quotient.out q) (u : MulAut W) huN
    have hγN : γ ∈ Subgroup.normalizer (Si (Quotient.out q) : Set (MulAut W)) :=
      s16h_e3_l3_inner_normalizes_sylow_inf (X := X q) (T := T) (τ := (u : MulAut W))
        (γ := γ) u.2 hγX hγact
    have hγP : γ ∈ P0 q := hP0norm q ⟨hγN, hγX⟩
    exact s16h_e3_l3_map_conj_eq_of_inner_on (hP0leX q) hγact hγP
  let Pc (i : I) : Subgroup (MulAut W) :=
    (P0 (qOf i)).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom
  have hPcleF : ∀ i : I, Pc i ≤ F i := by
    intro i
    calc Pc i = (P0 (qOf i)).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom := rfl
      _ ≤ (X (qOf i)).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom :=
          Subgroup.map_mono (hP0leX (qOf i))
      _ = F i := by
          have h := congrArg Subtype.val (tOf_spec i)
          rwa [act_val] at h
  have hPccard : ∀ i : I, Nat.card (Pc i) = 24 := by
    intro i
    change Nat.card ↥((P0 (qOf i)).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom) = 24
    rw [Subgroup.card_map_of_injective (MulAut.conj (tOf i : MulAut W)).injective,
      hP0card (qOf i)]
  have hPcpow : ∀ i : I, ∀ p ∈ Pc i, p ^ 12 = 1 := by
    intro i p hp
    obtain ⟨p', hp', rfl⟩ := Subgroup.mem_map.mp hp
    rw [← map_pow, hP0pow (qOf i) p' hp', map_one]
  have hPcsi : ∀ i : I, Si i ≤ Pc i := by
    intro i
    have hTmap : T.map (MulAut.conj (tOf i : MulAut W)).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := T) (tOf i).2)
    have hSimap : (Si (i0 i)).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom = Si i := by
      change (T ⊓ F (i0 i)).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom = T ⊓ F i
      rw [Subgroup.map_inf _ _ _ (MulAut.conj (tOf i : MulAut W)).injective, hTmap]
      rw [show (F (i0 i)).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom = F i from by
        have h := congrArg Subtype.val (tOf_spec i)
        rwa [act_val] at h]
    calc Si i = (Si (i0 i)).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom := hSimap.symm
      _ ≤ (P0 (qOf i)).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom :=
          Subgroup.map_mono (hSileP0 (qOf i))
      _ = Pc i := rfl
  let P : Subgroup (MulAut W) := ⨆ i, Pc i
  have hPleB : P ≤ B := by
    refine iSup_le fun i => ?_
    exact (hPcleF i).trans (hFiB i)
  have hcommP : Pairwise fun i j : I =>
      ∀ x y : MulAut W, x ∈ Pc i → y ∈ Pc j → Commute x y :=
    fun i j hij x y hx hy => hcomm hij x y (hPcleF i hx) (hPcleF j hy)
  have hindP : iSupIndep Pc := hind.mono (fun i => hPcleF i)
  have hPcard : Nat.card P = 24 ^ 3 := by
    change Nat.card ↥(⨆ i, Pc i) = 24 ^ 3
    obtain ⟨ePcard, -⟩ := CFSG.LocalCores.exists_mulEquiv_pi_iSup Pc hcommP hindP
    rw [← Nat.card_congr ePcard.toEquiv, Nat.card_pi]
    calc (∏ i : I, Nat.card ↥(Pc i)) = ∏ _ : I, 24 := by simp [hPccard]
      _ = 24 ^ Fintype.card I := by rw [Finset.prod_const, Finset.card_univ]
      _ = 24 ^ 3 := by rw [← Nat.card_eq_fintype_card, hcardI]
  have hPexp : ∀ x ∈ P, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1 := by
    intro x hx n hn
    obtain ⟨eP, -⟩ := CFSG.LocalCores.exists_mulEquiv_pi_iSup Pc hcommP hindP
    have hx' : x ∈ (⨆ i, Pc i) := by simpa [P] using hx
    let y : (i : I) → ↥(Pc i) := eP.symm ⟨x, hx'⟩
    have hy_pow : y ^ 3 ^ n = 1 := by
      apply eP.injective
      rw [map_pow, MulEquiv.apply_symm_apply, map_one]
      exact Subtype.ext (by simpa using hn)
    have hy3 : y ^ 3 = 1 := by
      funext i
      apply Subtype.ext
      have hi_pow : (y i) ^ 3 ^ n = 1 := by
        simpa using congrFun hy_pow i
      exact s16h_e3_l3_pow_three_of_pow_twelve (hPcpow i (y i) (y i).2)
        (by simpa using congrArg Subtype.val hi_pow)
    have hx3 : (⟨x, hx'⟩ : ↥(⨆ i, Pc i)) ^ 3 = 1 := by
      have hy_image : eP y = ⟨x, hx'⟩ := by
        dsimp only [y]
        exact eP.apply_symm_apply ⟨x, hx'⟩
      rw [← hy_image, ← map_pow, hy3, map_one]
    exact congrArg Subtype.val hx3
  have hPc_map : ∀ (i : I) (u : T),
      (Pc i).map (MulAut.conj (u : MulAut W)).toMonoidHom = Pc (u • i) := by
    intro i u
    let q : Q := qOf i
    have hq : qOf (u • i) = q := by
      apply Quotient.sound
      change MulAction.orbitRel T I (u • i) i
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨u, rfl⟩
    let w : T := (tOf (u • i))⁻¹ * u * tOf i
    have htu : tOf (u • i) • i0 i = u • i := by
      simpa [i0, hq] using tOf_spec (u • i)
    have hti : tOf i • i0 i = i := tOf_spec i
    have hw : w • i0 i = i0 i := by
      calc ((tOf (u • i))⁻¹ * u * tOf i) • i0 i
          = (tOf (u • i))⁻¹ • (u • (tOf i • i0 i)) := by rw [mul_smul, mul_smul]
        _ = (tOf (u • i))⁻¹ • (u • i) := by rw [hti]
        _ = (tOf (u • i))⁻¹ • (tOf (u • i) • i0 i) := by rw [htu]
        _ = ((tOf (u • i))⁻¹ * tOf (u • i)) • i0 i := by rw [mul_smul]
        _ = i0 i := by rw [inv_mul_cancel, one_smul]
    have hP0w : (P0 q).map (MulAut.conj (w : MulAut W)).toMonoidHom = P0 q :=
      hP0stab q w (by simpa [q] using hw)
    have hPcu : Pc (u • i) = (P0 q).map (MulAut.conj (tOf (u • i) : MulAut W)).toMonoidHom := by
      dsimp only [Pc]
      rw [hq]
    rw [hPcu]
    calc (Pc i).map (MulAut.conj (u : MulAut W)).toMonoidHom
        = ((P0 q).map (MulAut.conj (tOf i : MulAut W)).toMonoidHom).map
            (MulAut.conj (u : MulAut W)).toMonoidHom := rfl
      _ = (P0 q).map (MulAut.conj ((u : MulAut W) * (tOf i : MulAut W))).toMonoidHom :=
          Subgroup.map_conj_map_conj (P0 q) (tOf i : MulAut W) (u : MulAut W)
      _ = (P0 q).map (MulAut.conj ((tOf (u • i) : MulAut W) * (w : MulAut W))).toMonoidHom := by
          rw [show (u : MulAut W) * (tOf i : MulAut W) =
              (tOf (u • i) : MulAut W) * (w : MulAut W) by
            simp only [w, Subgroup.coe_mul, Subgroup.coe_inv]
            group]
      _ = ((P0 q).map (MulAut.conj (w : MulAut W)).toMonoidHom).map
            (MulAut.conj (tOf (u • i) : MulAut W)).toMonoidHom :=
          (Subgroup.map_conj_map_conj (P0 q) (w : MulAut W) (tOf (u • i) : MulAut W)).symm
      _ = (P0 q).map (MulAut.conj (tOf (u • i) : MulAut W)).toMonoidHom := by rw [hP0w]
  have hTnormP : T ≤ Subgroup.normalizer (P : Set (MulAut W)) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (⨆ i, Pc i).map (MulAut.conj u).toMonoidHom = ⨆ i, Pc i
    rw [Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      let j : I := (⟨u, hu⟩ : T) • i
      have hj : (Pc i).map (MulAut.conj u).toMonoidHom = Pc j := hPc_map i ⟨u, hu⟩
      rw [hj]
      exact le_iSup (fun k : I => Pc k) j
    · refine iSup_le fun j => ?_
      have hback : Pc j = (Pc ((⟨u, hu⟩ : T)⁻¹ • j)).map
          (MulAut.conj u).toMonoidHom := by
        rw [hPc_map ((⟨u, hu⟩ : T)⁻¹ • j) ⟨u, hu⟩]
        congr 1
        rw [← mul_smul, mul_inv_cancel, one_smul]
      rw [hback]
      exact le_iSup (fun i : I => (Pc i).map (MulAut.conj u).toMonoidHom) ((⟨u, hu⟩ : T)⁻¹ • j)
  have hcommS : Pairwise fun i j : I =>
      ∀ x y : MulAut W, x ∈ Si i → y ∈ Si j → Commute x y :=
    fun i j hij x y hx hy => hcomm hij x y hx.2 hy.2
  have hindS : iSupIndep Si := hind.mono (fun i => inf_le_right)
  have hSjoincard : Nat.card ↥(⨆ i, Si i) = 8 ^ 3 := by
    obtain ⟨eS, -⟩ := CFSG.LocalCores.exists_mulEquiv_pi_iSup Si hcommS hindS
    rw [← Nat.card_congr eS.toEquiv, Nat.card_pi]
    calc (∏ i : I, Nat.card ↥(Si i)) = ∏ _ : I, 8 := by simp [hSicard]
      _ = 8 ^ Fintype.card I := by rw [Finset.prod_const, Finset.card_univ]
      _ = 8 ^ 3 := by rw [← Nat.card_eq_fintype_card, hcardI]
  have hS_join_le : (⨆ i, Si i) ≤ S := by
    refine iSup_le fun i => ?_
    exact le_inf inf_le_left ((inf_le_right : Si i ≤ F i).trans (hFiB i))
  have hjoin_eq_S : (⨆ i, Si i) = S :=
    Subgroup.eq_of_le_of_card_ge hS_join_le (by rw [hScard, hSjoincard])
  have hS_eq_join : S = ⨆ i, Si i := hjoin_eq_S.symm
  have hSleP : S ≤ P := by
    rw [hS_eq_join]
    refine iSup_le fun i => ?_
    exact (hPcsi i).trans (le_iSup (fun j : I => Pc j) i)
  have hTinterP : T ⊓ P = S := by
    apply le_antisymm
    · calc T ⊓ P ≤ T ⊓ B := inf_le_inf le_rfl hPleB
        _ = S := rfl
    · exact le_inf inf_le_left hSleP
  have hPcardS : Nat.card P = 3 ^ 3 * Nat.card S := by
    rw [hPcard, hScard]
    norm_num
  let J : Subgroup (MulAut W) := T ⊔ P
  have hJle : J ≤ B ⊔ T :=
    sup_le le_sup_right (hPleB.trans le_sup_left)
  have hcardJ : Nat.card J = 3 ^ 3 * Nat.card T := by
    have hprod := s16c7_card_sup_mul_card_inf (X := MulAut W) (A := T) (N := P) hTnormP
    rw [hTinterP] at hprod
    have hSpos : 0 < Nat.card S := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hSpos
    calc Nat.card J * Nat.card S = Nat.card T * Nat.card P := hprod
      _ = Nat.card T * (3 ^ 3 * Nat.card S) := by rw [hPcardS]
      _ = (3 ^ 3 * Nat.card T) * Nat.card S := by ring
  have hexpJ : ∀ x ∈ J, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1 := by
    intro x hx n hn
    have hx' : x ∈ P ⊔ T := by
      rw [sup_comm]
      exact hx
    have hxP : x ∈ P :=
      CFSG.Quasithin.H13.S125Fin.mem_of_mem_sup_of_pow
        (X := P) (T := T) hTsyl.isPGroup hTnormP hx' hn
    exact hPexp x hxP n hn
  change T3Parab B T 3
  exact ⟨J, le_sup_left, hJle, hcardJ, hexpJ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
