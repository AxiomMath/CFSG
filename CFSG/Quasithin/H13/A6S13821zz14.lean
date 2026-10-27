module

public import CFSG.Quasithin.H13.A6S13821zz13
public import CFSG.Quasithin.EmptyFaithful.S153DGen3

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

section SecAct

variable {G : Type} [Group G]

theorem conjAct_secMk_apply {J U : Subgroup G} (x u : ↥(Subgroup.normalizer (J : Set G)))
    (hxU : (x : G) ∈ Subgroup.normalizer (U : Set G)) (hu : (u : G) ∈ U) :
    ((conjAct (secImg (Subgroup.normalizer (J : Set G)) J U)
        ⟨secMk _ J x, secMk_mem_normalizer_secImg hxU⟩
        ⟨secMk _ J u, secMk_mem_secImg hu⟩ : ↥(secImg (Subgroup.normalizer (J : Set G)) J U)) :
      SecQuot (Subgroup.normalizer (J : Set G)) J) = secMk _ J (x * u * x⁻¹) := by
  rw [conjAct_apply_coe', map_mul, map_mul, map_inv]

theorem conjAct_secMk_eq_one_iff {J U : Subgroup G} (hUJ : U ≤ Subgroup.normalizer (J : Set G))
    (x : ↥(Subgroup.normalizer (J : Set G))) (hxU : (x : G) ∈ Subgroup.normalizer (U : Set G)) :
    conjAct (secImg (Subgroup.normalizer (J : Set G)) J U)
        ⟨secMk _ J x, secMk_mem_normalizer_secImg hxU⟩ = 1 ↔
      ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ J := by
  constructor
  · intro h u hu
    have h1 := congrArg (fun φ : MulAut ↥(secImg (Subgroup.normalizer (J : Set G)) J U) =>
      ((φ ⟨secMk _ J ⟨u, hUJ hu⟩, secMk_mem_secImg hu⟩ :
        ↥(secImg (Subgroup.normalizer (J : Set G)) J U)) :
          SecQuot (Subgroup.normalizer (J : Set G)) J)) h
    simp only [MulAut.one_apply] at h1
    rw [conjAct_secMk_apply x ⟨u, hUJ hu⟩ hxU hu] at h1
    have h2 : secMk _ J (x * ⟨u, hUJ hu⟩ * x⁻¹ * (⟨u, hUJ hu⟩ :
        ↥(Subgroup.normalizer (J : Set G)))⁻¹) = 1 := by
      rw [map_mul _ (x * ⟨u, hUJ hu⟩ * x⁻¹), h1, map_inv, mul_inv_cancel]
    exact secMk_eq_one_iff.mp h2
  · intro h
    refine MulEquiv.ext fun e => Subtype.ext ?_
    obtain ⟨u, hu, hue⟩ := mem_secImg.mp e.2
    have he : e = ⟨secMk _ J u, secMk_mem_secImg hu⟩ := Subtype.ext hue.symm
    rw [he, MulAut.one_apply, conjAct_secMk_apply x u hxU hu, secMk_eq_secMk_iff]
    have h1 := h (u : G) hu
    have h2 : (u : G)⁻¹ * ((x : G) * u * (x : G)⁻¹ * (u : G)⁻¹)⁻¹ * (u : G)⁻¹⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ u.2) _).mp (J.inv_mem h1)
    have e1 : ((x * u * x⁻¹ : ↥(Subgroup.normalizer (J : Set G))) : G)⁻¹ * (u : G) =
        (u : G)⁻¹ * ((x : G) * u * (x : G)⁻¹ * (u : G)⁻¹)⁻¹ * (u : G)⁻¹⁻¹ := by
      push_cast
      group
    rw [e1]
    exact h2

end SecAct

section Quot

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G]

theorem faithful_autOn_quot {T V L V₁ Vp H K J B : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) (hV₁J : V₁ ≤ J) (hJU : J ≤ conjClosure Vp H)
    (hJN : K ⊔ T ≤ Subgroup.normalizer (J : Set G))
    (hnt : ¬ ∀ k ∈ K, ∀ u ∈ conjClosure Vp H, k * u * k⁻¹ * u⁻¹ ∈ J)
    (hB : IsF918B T L V₁ Vp H (conjClosure K T) B) :
    ∀ a ∈ autOn (secImg (Subgroup.normalizer (J : Set G)) J B)
        (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)),
      (∀ l ∈ autOn (secImg (Subgroup.normalizer (J : Set G)) J K)
          (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)), a * l = l * a) →
        a = 1 := by
  classical
  have h1 := hF.toHypF98.toHypF91
  have hBT : B ≤ T := hB.1.trans hF.pCoreOf_L₁T_le_T
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hUJ : conjClosure Vp H ≤ Subgroup.normalizer (J : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le hF.toHypF98.F911_3 hJU
  have hHU : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := le_normalizer_conjClosure Vp H
  have hJN' : conjClosure K T ⊔ T ≤ Subgroup.normalizer (J : Set G) := by rw [hK₀]; exact hJN
  have hUN' : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure Vp H : Set G) :=
    hF.K₀T_le_normalizer_U
  have hnt' : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ conjClosure Vp H, k * e * k⁻¹ * e⁻¹ ∈ J := by
    rw [hK₀]; exact hnt
  obtain ⟨hcen, -⟩ := hF.central_kernel_and_faithful hBT hB.2.2 hJN' hUN' hnt'
  set N := centralizerMod J (conjClosure K T) (conjClosure Vp H) with hN
  have hNn : conjClosure K T ⊔ T ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_centralizerMod hJN' (HypF918.K₀T_le_normalizer_K₀ T K) hUN'
  set D := centralizerMod N B (conjClosure K T) with hD
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hDQ : ⁅D, conjClosure K T⁆ ≤ pCoreOf 2 H := by
    refine commutator_le_of_commutator_commutator_le
      ((centralizerMod_le_left _ _ _).trans (hBT.trans (hTH.trans hQn)))
      (hF.K₀_le_H.trans hQn) hF.K₀_perfect ?_
    have hKD : ⁅conjClosure K T, D⁆ ≤ N := by
      refine Subgroup.commutator_le.mpr fun k hk d hd => ?_
      have h2 := N.inv_mem (hd.2.2 k hk)
      have e : (d * k * d⁻¹ * k⁻¹)⁻¹ = ⁅k, d⁆ := by rw [commutatorElement_def]; group
      rwa [e] at h2
    have hNK : ⁅N, conjClosure K T⁆ ≤ pCoreOf 2 H :=
      Subgroup.commutator_le.mpr fun x hx k' hk' => hcen x hx.1 hx.2.2 k' hk'
    exact (Subgroup.commutator_mono hKD le_rfl).trans hNK
  intro a ha hal
  obtain ⟨s, hsB, rfl⟩ := mem_autOn_iff.mp ha
  obtain ⟨b, hbB, hbs⟩ := mem_secImg.mp hsB
  have hbU : (b : G) ∈ Subgroup.normalizer (conjClosure Vp H : Set G) := hHU (hTH (hBT hbB))
  have hs : s = ⟨secMk _ J b, secMk_mem_normalizer_secImg hbU⟩ := Subtype.ext hbs.symm
  subst hs
  have hbD : (b : G) ∈ D := by
    refine ⟨hbB, hNn (Subgroup.mem_sup_right (hBT hbB)), fun k hk => ?_⟩
    have hk' : k ∈ K := by rw [← hK₀]; exact hk
    have hkJ : k ∈ Subgroup.normalizer (J : Set G) := hJN (Subgroup.mem_sup_left hk')
    have hkU : k ∈ Subgroup.normalizer (conjClosure Vp H : Set G) := hHU (hKH hk')
    have hl := hal _ (mem_autOn_iff.mpr ⟨⟨secMk _ J ⟨k, hkJ⟩, secMk_mem_normalizer_secImg hkU⟩,
      secMk_mem_secImg hk', rfl⟩)
    have hbkK : (b : G) * k * (b : G)⁻¹ * k⁻¹ ∈ conjClosure K T :=
      (conjClosure K T).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K T (hBT hbB)) k).mp hk)
        ((conjClosure K T).inv_mem hk)
    set y : ↥(Subgroup.normalizer (J : Set G)) := b * ⟨k, hkJ⟩ * b⁻¹ * (⟨k, hkJ⟩)⁻¹ with hy
    have hyU : (y : G) ∈ Subgroup.normalizer (conjClosure Vp H : Set G) := by
      rw [hy]
      push_cast
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbU hkU)
        (Subgroup.inv_mem _ hbU)) (Subgroup.inv_mem _ hkU)
    have hy1 : conjAct (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H))
        ⟨secMk _ J y, secMk_mem_normalizer_secImg hyU⟩ = 1 := by
      have e : (⟨secMk _ J y, secMk_mem_normalizer_secImg hyU⟩ :
          ↥(Subgroup.normalizer (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H) :
            Set (SecQuot (Subgroup.normalizer (J : Set G)) J)))) =
          ⟨secMk _ J b, secMk_mem_normalizer_secImg hbU⟩ *
            ⟨secMk _ J ⟨k, hkJ⟩, secMk_mem_normalizer_secImg hkU⟩ *
            (⟨secMk _ J b, secMk_mem_normalizer_secImg hbU⟩)⁻¹ *
            (⟨secMk _ J ⟨k, hkJ⟩, secMk_mem_normalizer_secImg hkU⟩)⁻¹ := by
        apply Subtype.ext
        simp only [hy, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hl, mul_inv_cancel_right,
        mul_inv_cancel]
    have hyJ := (conjAct_secMk_eq_one_iff hUJ y hyU).mp hy1
    have hyG : (y : G) = (b : G) * k * (b : G)⁻¹ * k⁻¹ := by rw [hy]; push_cast; rfl
    rw [hyG] at hyJ
    exact ⟨hbkK, hJN' (Subgroup.mem_sup_left hbkK), hyJ⟩
  have hbQ : (b : G) ∈ pCoreOf 2 H :=
    hB.2.2 _ hbB fun k hk => hDQ (Subgroup.commutator_mem_commutator hbD hk)
  rw [h1.pCoreOf_eq_centralizerMod] at hbQ
  exact (conjAct_secMk_eq_one_iff hUJ b hbU).mpr fun u hu => hV₁J (hbQ.2.2 u hu)

theorem exists_kappa_quot {T V L V₁ Vp H K J : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hV₁J : V₁ ≤ J) (hJU : J ≤ conjClosure Vp H) (hKJ : K ≤ Subgroup.normalizer (J : Set G)) :
    ∃ κ : ↥K →* ↥(autOn (secImg (Subgroup.normalizer (J : Set G)) J K)
        (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H))),
      Function.Surjective κ ∧ (∀ x ∈ CFSG.pCore 2 ↥K, κ x = 1) ∧
      (∀ x : ↥K, κ x = 1 ↔ ∀ u ∈ conjClosure Vp H, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ J) ∧
      ∀ (x : ↥K) (u : ↥(Subgroup.normalizer (J : Set G))) (hu : (u : G) ∈ conjClosure Vp H),
        ((κ x : MulAut _) ⟨secMk _ J u, secMk_mem_secImg hu⟩ *
            (⟨secMk _ J u, secMk_mem_secImg hu⟩ :
              ↥(secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)))⁻¹ = 1 ↔
          (x : G) * u * (x : G)⁻¹ * (u : G)⁻¹ ∈ J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hHU : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := le_normalizer_conjClosure Vp H
  have hUJ : conjClosure Vp H ≤ Subgroup.normalizer (J : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le hF.toHypF98.F911_3 hJU
  have hLN : secImg (Subgroup.normalizer (J : Set G)) J K ≤
      Subgroup.normalizer (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H) :
        Set (SecQuot (Subgroup.normalizer (J : Set G)) J)) :=
    secImg_le_normalizer_secImg (hKH.trans hHU)
  let σ : ↥K →* ↥(secImg (Subgroup.normalizer (J : Set G)) J K) :=
    ((secMk _ J).comp (Subgroup.inclusion hKJ)).codRestrict _ fun k => secMk_mem_secImg k.2
  have hσs : Function.Surjective σ := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk, rfl⟩ := mem_secImg.mp hy
    exact ⟨⟨k, hk⟩, rfl⟩
  have hcoe : ∀ x : ↥K, (((S153D.autOnHom hLN).comp σ x :
      ↥(autOn (secImg (Subgroup.normalizer (J : Set G)) J K)
        (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)))) :
      MulAut ↥(secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H))) =
      conjAct (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H))
        ⟨secMk _ J ⟨x, hKJ x.2⟩, secMk_mem_normalizer_secImg (hHU (hKH x.2))⟩ := fun x => rfl
  have h1 : ∀ x : ↥K, (S153D.autOnHom hLN).comp σ x = 1 ↔
      ∀ u ∈ conjClosure Vp H, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ J := by
    intro x
    rw [← Subtype.coe_inj, hcoe x]
    exact conjAct_secMk_eq_one_iff hUJ ⟨x, hKJ x.2⟩ (hHU (hKH x.2))
  refine ⟨(S153D.autOnHom hLN).comp σ, (S153D.autOnHom_surjective hLN).comp hσs, ?_, h1, ?_⟩
  · intro x hx
    rw [h1]
    intro u hu
    have hx' : x ∈ CFSG.Open.pCore 2 ↥K := by
      assumption
    have hx1 : (x : G) ∈ pCoreOf 2 K := ⟨x, hx', rfl⟩
    have hxQ : (x : G) ∈ pCoreOf 2 H :=
      A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hF.K_cComp) hx1
    rw [hF.toHypF98.toHypF91.pCoreOf_eq_centralizerMod] at hxQ
    exact hV₁J (hxQ.2.2 u hu)
  · intro x u hu
    rw [← Subtype.coe_inj, Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one, hcoe x,
      conjAct_secMk_apply (J := J) (U := conjClosure Vp H) ⟨x, hKJ x.2⟩ u (hHU (hKH x.2)) hu,
      ← map_inv, ← map_mul,
      secMk_eq_one_iff]
    push_cast
    rfl

theorem fixProp_quot_of_ff (hA21 : AsA21SQTKSection) (hB51 : AsB51)
    {T V L V₁ Vp H K J B T₀ : Subgroup G} (hSQ : SQTKGroup ↥H) (hF : HypF918 T V L V₁ Vp H K)
    (hK₀ : conjClosure K T = K) [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H)))]
    (hV₁J : V₁ ≤ J) (hJU : J ≤ conjClosure Vp H) (hJN : K ⊔ T ≤ Subgroup.normalizer (J : Set G))
    (hnt : ¬ ∀ k ∈ K, ∀ u ∈ conjClosure Vp H, k * u * k⁻¹ * u⁻¹ ∈ J)
    (hB : IsF918B T L V₁ Vp H (conjClosure K T) B)
    (hle : (centralizerMod J (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≤
      (B ⊓ pCoreOf 2 H).relIndex B)
    (hperf : commutator (↥K ⧸ CFSG.pCore 2 ↥K) = ⊤)
    (hs : IsSimpleGroup ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)))
    {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) =
      (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)))
    (hoddZ : Odd (Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))))
    (hsyl : IsSylowTwoOf T₀ K) :
    S1565.FixProp ((actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H)).comp
        (Subgroup.inclusion (le_of_mem_cComp hF.K_cComp)))
      ((K ⊓ Subgroup.normalizer (T₀ : Set G)).subgroupOf K) (subM V₁ (conjClosure Vp H) J) ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBT : B ≤ T := hB.1.trans hF.pCoreOf_L₁T_le_T
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G) := hF.H_le_normalizer_V₁
  have hHU : H ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := le_normalizer_conjClosure Vp H
  have hUN : conjClosure Vp H ≤ Subgroup.normalizer (V₁ : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure Vp H)
  have hUJ : conjClosure Vp H ≤ Subgroup.normalizer (J : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le hF.toHypF98.F911_3 hJU
  have hKJ : K ≤ Subgroup.normalizer (J : Set G) := le_sup_left.trans hJN
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := hBT.trans (le_sup_right.trans hJN)
  have hBU : B ≤ Subgroup.normalizer (conjClosure Vp H : Set G) := hBT.trans (hTH.trans hHU)
  have hKTU : K ⊔ T ≤ Subgroup.normalizer (conjClosure Vp H : Set G) :=
    sup_le (hKH.trans hHU) (hTH.trans hHU)
  have hKTK : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := by
    have := HypF918.K₀T_le_normalizer_K₀ T K
    rwa [hK₀] at this
  have hJN' : conjClosure K T ⊔ T ≤ Subgroup.normalizer (J : Set G) := by rw [hK₀]; exact hJN
  have hnt' : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ conjClosure Vp H, k * e * k⁻¹ * e⁻¹ ∈ J := by
    rw [hK₀]; exact hnt
  obtain ⟨-, hf2⟩ := hF.central_kernel_and_faithful hBT hB.2.2 hJN' hF.K₀T_le_normalizer_U hnt'
  have hC2 : centralizerMod J B (conjClosure Vp H) = B ⊓ pCoreOf 2 H :=
    hF.centralizerMod_eq_inf_pCoreOf hV₁J hBJ le_rfl hf2
  have hnt2 : ¬ ∀ b ∈ B, ∀ e ∈ conjClosure Vp H, b * e * b⁻¹ * e⁻¹ ∈ J := fun hall =>
    hB.2.1.2.2.1 fun b hb => hf2 b hb fun e he => hall b hb e he
  have hE := hF.isElemAbelian_quotient J
  let _ : CommGroup ↥(secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)) :=
    commGroupOfElemAbelian hE
  have hFF := isFFModule_autOn_secImg (K := J) (E := conjClosure Vp H) (X' := B) (B := B) hE hUJ
    hBJ hBU le_rfl hB.2.1.2.1 hnt2 (by rw [hC2]; exact hle)
  obtain ⟨κ, hκs, hκO, hκ1, hκa⟩ := exists_kappa_quot hF hV₁J hJU hKJ
  have hqK : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := Insp9.isQuasisimple_of_open ⟨hperf, hs⟩
  have hker : CFSG.pCore 2 ↥K ≤ κ.ker := fun x hx => hκO x hx
  have hsurj : Function.Surjective (QuotientGroup.lift (CFSG.pCore 2 ↥K) κ hker) := fun y => by
    obtain ⟨x, rfl⟩ := hκs y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hne : ∃ k, QuotientGroup.lift (CFSG.pCore 2 ↥K) κ hker k ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hnt fun k hk u hu => (hκ1 ⟨k, hk⟩).mp (hall (QuotientGroup.mk ⟨k, hk⟩)) u hu
  have hq := CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqK hsurj hne
  have hLG : autOn (secImg (Subgroup.normalizer (J : Set G)) J K)
      (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)) ≤
      autOn (secImg (Subgroup.normalizer (J : Set G)) J (K ⊔ T))
        (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)) :=
    autOn_le_autOn _ (secImg_mono le_sup_left)
  have hBG : autOn (secImg (Subgroup.normalizer (J : Set G)) J B)
      (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)) ≤
      autOn (secImg (Subgroup.normalizer (J : Set G)) J (K ⊔ T))
        (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)) :=
    autOn_le_autOn _ (secImg_mono (hBT.trans le_sup_right))
  have hLn := fun g (hg : g ∈ autOn (secImg (Subgroup.normalizer (J : Set G)) J (K ⊔ T))
      (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H))) l
      (hl : l ∈ autOn (secImg (Subgroup.normalizer (J : Set G)) J K)
        (secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H))) =>
    A4.autOn_conj_mem (secImg_le_normalizer_secImg hKTU) (secImg_mono le_sup_left)
      (secImg_le_normalizer_secImg hKTK) hg hl
  have hfaith := faithful_autOn_quot hF hK₀ hV₁J hJU hJN hnt hB
  have hSQK : SQTKGroup ↥K := B5.sqtk_of_le hSQ hKH
  have hsyl' : IsSylowTwoOf (T₀.subgroupOf K) (⊤ : Subgroup ↥K) := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hsyl.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hsyl.1).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hsyl.1).injective
    · have e : ((T₀.subgroupOf K).subgroupOf (⊤ : Subgroup ↥K)).index =
          (T₀.subgroupOf K).index :=
        Subgroup.index_comap_of_surjective (T₀.subgroupOf K) (f := (⊤ : Subgroup ↥K).subtype)
          (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
      rw [e]
      exact hsyl.2.2
  have hNT : CFSG.pCore 2 ↥K ≤ T₀.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ pCoreOf 2 K := ⟨x, by assumption, rfl⟩
    exact F7.isSylowTwoOf_pCoreOf_le hsyl hx'
  have hV2 : ∀ v : ↥(secImg (Subgroup.normalizer (J : Set G)) J (conjClosure Vp H)), v ^ 2 = 1 :=
    fun v => Subtype.ext (by simpa using F7.isElemAbelian_pow_eq_one hE v.2)
  have hmain := fixProp_of_component hA21 hB51 hV2 hLG hLn hq hBG hFF hfaith hSQK κ hκs
    (CFSG.pCore 2 ↥K) hperf hs hn hcard hoddZ hsyl' hNT hκO
  have hact : ∀ (y : ↥K) (a : G) (ha : a ∈ conjClosure Vp H),
      ∃ hya : (y : G) * a * (y : G)⁻¹ * a⁻¹ ∈ conjClosure Vp H,
        ((actH hHV₁ hHU).comp (Subgroup.inclusion hKH)) y (modMk hUN a ha) *
            (modMk hUN a ha)⁻¹ = modMk hUN ((y : G) * a * (y : G)⁻¹ * a⁻¹) hya := by
    intro y a ha
    have hya : (y : G) * a * (y : G)⁻¹ ∈ conjClosure Vp H :=
      (Subgroup.mem_normalizer_iff.mp (hHU (hKH y.2)) a).mp ha
    refine ⟨(conjClosure Vp H).mul_mem hya ((conjClosure Vp H).inv_mem ha), ?_⟩
    rw [MonoidHom.comp_apply, actH_modMk hHV₁ hUN hHU (Subgroup.inclusion hKH y) ha,
      ← modMk_inv hUN ha, ← modMk_mul hUN _ ((conjClosure Vp H).inv_mem ha)]
    rfl
  intro w _ hwB x _
  obtain ⟨a, haU, haw⟩ := exists_mk_of_mem_tilde w
  have hw : w = modMk hUN (a : G) haU := Subtype.ext haw.symm
  subst hw
  have hfixB : ∀ y ∈ Subgroup.normalizer ((T₀.subgroupOf K : Subgroup ↥K) : Set ↥K),
      (y : G) * a * (y : G)⁻¹ * (a : G)⁻¹ ∈ J := by
    intro y hy
    have hyN : (y : G) ∈ Subgroup.normalizer (T₀ : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun t ht => ?_
      rw [SetLike.mem_coe] at ht ⊢
      have htK : t ∈ K := hsyl.1 ht
      have h2 := (Subgroup.mem_normalizer_iff.mp hy ⟨t, htK⟩).mp (Subgroup.mem_subgroupOf.mpr ht)
      exact Subgroup.mem_subgroupOf.mp h2
    have h2 := hwB y (Subgroup.mem_subgroupOf.mpr ⟨y.2, hyN⟩)
    obtain ⟨hya, e⟩ := hact y a haU
    rw [e, modMk_mem_subM_iff hUN hV₁J] at h2
    exact h2
  have hmx := hmain ⟨secMk _ J ⟨a, hUJ haU⟩, secMk_mem_secImg haU⟩ (Subgroup.mem_top _)
    (fun y hy => by
      rw [Subgroup.mem_bot]
      exact (hκa y ⟨a, hUJ haU⟩ haU).mpr (hfixB y hy)) x (Subgroup.mem_top x)
  rw [Subgroup.mem_bot] at hmx
  obtain ⟨hxa, e⟩ := hact x a haU
  rw [e, modMk_mem_subM_iff hUN hV₁J]
  exact (hκa x ⟨a, hUJ haU⟩ haU).mp hmx

end Quot

end CFSG.Quasithin.H13.A6.A6S20
