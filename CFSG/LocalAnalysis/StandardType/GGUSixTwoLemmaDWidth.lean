module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLemmaD
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModule
public import CFSG.LargeExtraspecial.S3Basic
public import CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset
public import CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open

variable {G : Type*} [Group G] {K : Type} [Field K]

namespace LocalSetting

variable {ω : K} {hω : ω ^ 2 + ω + 1 = 0} {b : G} {L : Subgroup G}
  {φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))} {Bs : Subgroup G}

@[expose] noncomputable def settingOfInvolution [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    (hnA : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ hnL : n * b * n⁻¹ ∈ L,
      φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω ∧ n⁻¹ * t * n ∈
        (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    CFSG.LargeExtraspecial.Setting G := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht_ne_one : t ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at ht2; norm_num at ht2
  have ht_sq : t * t = 1 := by
    rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hnormalizer : Subgroup.centralizer ({t} : Set G) =
      Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h x
      constructor
      · intro hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
          rw [← conj_zpow, show g * t * g⁻¹ = t from by rw [h]; group]⟩
      · intro hx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
        have hconj : g * t * g⁻¹ = t := by rw [h]; group
        have hconj' : g⁻¹ * t * g = t := by
          calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [hconj]
            _ = t := by group
        have hxt : x = t ^ k := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = g⁻¹ * t ^ k * g := by rw [← hk]
            _ = (g⁻¹ * t * g) ^ k := by
              simpa using (conj_zpow (a := g⁻¹) (b := t) (i := k)).symm
            _ = t ^ k := by rw [hconj']
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, hxt.symm⟩
    · intro h
      have hmem : g * t * g⁻¹ ∈ Subgroup.zpowers t := (h t).mp (Subgroup.mem_zpowers t)
      rw [CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self ht_sq] at hmem
      rcases hmem with h1 | h1
      · exfalso
        apply ht_ne_one
        calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h1]
          _ = 1 := by group
      · calc g * t = (g * t * g⁻¹) * g := by group
          _ = t * g := by rw [h1]
  have h2loc : IsTwoLocal (Subgroup.centralizer ({t} : Set G)) := by
    refine ⟨Subgroup.zpowers t, ?_, ?_, hnormalizer⟩
    · intro hbot
      have : t ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.mem_zpowers t
      exact ht_ne_one (by simpa using this)
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, ht2, pow_one]
  exact
    { z := t
      orderOf_z := ht2
      Q := CFSG.pCore 2 (Subgroup.centralizer ({t} : Set G))
      normal := CFSG.pCore_normal
      extraspecial := CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv
        (Subgroup.equivMapOfInjective (CFSG.pCore 2 (Subgroup.centralizer ({t} : Set G)))
          (Subgroup.centralizer ({t} : Set G)).subtype
          (Subgroup.subtype_injective _)).symm
        (isExtraspecialPGroup_pCoreOf_centralizer hG hS ht ht2 htb htL hnA)
      centralizer_le := by
        intro x hx
        have hchar := hG (Subgroup.centralizer ({t} : Set G)) h2loc
        have hxcent : (x : G) ∈ Subgroup.centralizer
            (pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
          exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx q hq)
        have hxin := hchar (Subgroup.mem_inf.mpr ⟨x.2, hxcent⟩)
        have hxin' : (x : G) ∈ (CFSG.pCore 2 (Subgroup.centralizer ({t} : Set G))).map
            (Subgroup.centralizer ({t} : Set G)).subtype := hxin
        rw [Subgroup.mem_map] at hxin'
        obtain ⟨q, hq, hqx⟩ := hxin'
        have hxq : x = q := (Subtype.ext hqx).symm
        rwa [hxq]
      le_of_normal := by
        intro P hP h2
        exact le_sSup ⟨hP, h2⟩ }

theorem settingOfInvolution_width [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    (hnA : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ hnL : n * b * n⁻¹ ∈ L,
      φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω ∧ n⁻¹ * t * n ∈
        (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    (settingOfInvolution hG hS ht ht2 htb htL hnA).width = 10 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : CFSG.LargeExtraspecial.Setting G := settingOfInvolution hG hS ht ht2 htb htL hnA
  change S.width = 10
  obtain ⟨n, hn, hnL, hnφ, htA⟩ := hnA
  set e : G := n * b * n⁻¹ with hedef
  set Me : Subgroup G := L.map (MulAut.conj n : G →* G) with hMedef
  set Qe : Subgroup G := pCoreOf 2 (Me ⊓ Subgroup.centralizer ({t} : Set G)) with hQedef
  have heBs : e ∈ Bs := (Subgroup.mem_normalizer_iff.mp hn b).mp hS.mem
  have he_order : orderOf e = 3 := by
    have h : orderOf e = orderOf b := by
      rw [hedef]
      exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective b
    rw [h, hS.orderOf_b]
  have ht_sq : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hSz : S.z = t := rfl
  have hSQG : S.QG = pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) := rfl
  have hLM : L ≤ S.M := by
    intro x hx
    rw [CFSG.LargeExtraspecial.Setting.mem_M_iff, hSz]
    exact Subgroup.mem_centralizer_iff.mp htL x hx
  have hBM : Bs ⊓ L ≤ S.M := fun x hx => hLM hx.2
  have hQe_eq : S.QG ⊓ Subgroup.centralizer ({e} : Set G) = Qe :=
    pCoreOf_centralizer_inf_centralizer_eq hG hS ht ht2 htb htL hn hnL hnφ htA
  have hQe_le : Qe ≤ S.QG := hQe_eq ▸ inf_le_left
  have hCQe : Subgroup.centralizer ((Bs ⊓ L : Subgroup G) : Set G) ⊓ Qe =
      Subgroup.zpowers t :=
    centralizer_inf_pCoreOf_conj_inf_centralizer hG hS ht ht2 htb htL hn hnL hnφ htA
  have hcardQe : Nat.card ↥Qe = 2 ^ 9 :=
    card_pCoreOf_conj_inf_centralizer hG hS ht ht2 htb htL hn hnL hnφ htA
  let conjH : S.M →* MulAut S.Q := @MulAut.conjNormal S.M _ S.Q S.normal
  have hconjH : ∀ (g : S.M) (x : S.Q), ((conjH g x : S.Q) : S.M) = g * x * g⁻¹ :=
    fun g x => MulAut.conjNormal_apply g x
  have hBp : IsPGroup 3 ↥(Bs ⊓ L) := by
    refine IsPGroup.of_card (n := 4) ?_
    rw [hS.card_Bbar]
  let ρL : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
      (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    (S.O.subtype : S.O →* (S.Qt ≃ₗ[ZMod 2] S.Qt)).comp
      (S.ρ.comp ((Subgroup.inclusion hLM).comp (φ.symm : LargeEvenProj
        (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* L)))
  have hρL_apply : ∀ x : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)), ρL x =
      ((S.ρ ⟨(φ.symm x : L), hLM (φ.symm x).2⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    intro x; rfl
  have ht_QG : t ∈ S.QG := hSz ▸ S.z_mem_QG
  have hzQe : S.z ∈ Qe := by
    rw [← hQe_eq]
    refine Subgroup.mem_inf.mpr ⟨S.z_mem_QG, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp htL e hnL).symm
  have htor : ∀ v : S.Qt, (∀ x ∈ torU K, ρL x v = v) → v = 0 := by
    intro v hv
    obtain ⟨q, hqv⟩ := S.exists_toQt v
    let β : ↥(Bs ⊓ L) →* MulAut S.Q := conjH.comp (Subgroup.inclusion hBM)
    have hβ : ∀ b : ↥(Bs ⊓ L), β b = conjH (Subgroup.inclusion hBM b) := fun b => rfl
    have hmod : ∀ b : ↥(Bs ⊓ L), β b q * q⁻¹ ∈ Subgroup.center S.Q := by
      intro b
      have hu : φ ⟨(b : G), b.2.2⟩ ∈ torU K := by
        rw [← hS.map_inf]
        exact Subgroup.mem_map_of_mem φ.toMonoidHom
          (x := (⟨(b : G), b.2.2⟩ : L)) b.2
      have hv' := hv (φ ⟨(b : G), b.2.2⟩) hu
      rw [← hqv] at hv'
      have hρ : ρL (φ ⟨(b : G), b.2.2⟩) =
          ((S.ρ (Subgroup.inclusion hBM b) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
        rw [hρL_apply]
        have harg : (⟨φ.symm (φ ⟨(b : G), b.2.2⟩),
            hLM (φ.symm (φ ⟨(b : G), b.2.2⟩)).2⟩ : S.M) =
            Subgroup.inclusion hBM b := by
          apply Subtype.ext
          rw [MulEquiv.symm_apply_apply]
          rfl
        rw [harg]
      rw [hρ] at hv'
      have hρto := S.ρ_toQt (Subgroup.inclusion hBM b) q
      rw [hρto] at hv'
      have hzero : S.toQt (β b q * q⁻¹) = 0 := by
        have hv'' : S.toQt (β b q) = S.toQt q := hv'
        rw [S.toQt_mul, S.toQt_inv, hv'']
        exact add_neg_cancel _
      exact (S.toQt_eq_zero_iff _).mp hzero
    have hcent : ¬ 3 ∣ Nat.card ↥(Subgroup.center S.Q) := by
      rw [S.card_center_Q]
      norm_num
    have hR : ∀ b : ↥(Bs ⊓ L), ∀ r ∈ Subgroup.center S.Q, β b r ∈ Subgroup.center S.Q := by
      intro b r hr
      rw [Subgroup.mem_center_iff] at hr ⊢
      intro z
      obtain ⟨z', rfl⟩ := (β b).surjective z
      rw [← map_mul, ← map_mul, hr z']
    obtain ⟨y, hy, hfixy⟩ :=
      CFSG.LinearAlgebra.CoprimeActions.CoprimePGroupFixedCoset.exists_fixed
        (p := 3) hBp β (Subgroup.center S.Q) (inferInstance : (Subgroup.center S.Q).Normal)
        hR hcent q hmod
    have hyT : ((y : S.M) : G) ∈ S.QG := S.coe_mem_QG y
    have hyC : ((y : S.M) : G) ∈ Subgroup.centralizer ((Bs ⊓ L : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 : β ⟨b, hb⟩ y = y := hfixy ⟨b, hb⟩
      have h2 : b * ((y : S.M) : G) * b⁻¹ = ((y : S.M) : G) := by
        have hc := congrArg (fun z : S.Q => ((z : S.M) : G)) h1
        rw [hβ] at hc
        simpa [hconjH] using hc
      calc b * ((y : S.M) : G) = (b * ((y : S.M) : G) * b⁻¹) * b := by group
        _ = ((y : S.M) : G) * b := by rw [h2]
    have hyCe : ((y : S.M) : G) ∈ Subgroup.centralizer ({e} : Set G) := by
      have hb : e ∈ Bs ⊓ L := ⟨heBs, hnL⟩
      have h := hyC e hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.symm
    have hyQe : ((y : S.M) : G) ∈ Qe := by
      rw [← hQe_eq]
      exact Subgroup.mem_inf.mpr ⟨hyT, hyCe⟩
    have hyzp : ((y : S.M) : G) ∈ Subgroup.zpowers t := by
      rw [← hCQe]
      exact Subgroup.mem_inf.mpr ⟨hyC, hyQe⟩
    have hy0 : S.toQt y = 0 := by
      have hz' : ((y : S.M) : G) ∈ Subgroup.zpowers S.z := by
        have h := hyzp
        rw [← hSz] at h
        exact h
      rw [CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self S.z_mul_z] at hz'
      rcases hz' with h1 | h1
      · rw [show y = 1 from Subtype.ext (Subtype.ext h1), S.toQt_one]
      · have hyz : ((y : S.M) : G) = ((S.zQ : S.M) : G) := by
          rw [h1, CFSG.LargeExtraspecial.Setting.coe_zQ]
        rw [show y = S.zQ from Subtype.ext (Subtype.ext hyz), S.toQt_eq_zero_iff']
        exact Or.inr rfl
    have hyq : S.toQt y = S.toQt q := by
      have h0 : S.toQt (y * q⁻¹) = 0 := (S.toQt_eq_zero_iff (y * q⁻¹)).mpr hy
      rw [S.toQt_mul, S.toQt_inv] at h0
      exact add_neg_eq_zero.mp h0
    rw [← hqv, ← hyq]
    exact hy0
  have h8 : Module.finrank (ZMod 2)
      (LinearMap.eqLocus (ρL (threeA hω) : S.Qt →ₗ[ZMod 2] S.Qt) LinearMap.id) = 8 := by
    let eM : S.M := ⟨e, hLM hnL⟩
    let α : MulAut S.Q := conjH eM
    have hα : α = conjH eM := rfl
    have hφe : φ.symm (threeA hω) = (⟨e, hnL⟩ : L) := by
      rw [← hnφ, MulEquiv.symm_apply_apply]
    have hρe : ρL (threeA hω) =
        ((S.ρ eM : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      have harg : (⟨φ.symm (threeA hω), hLM (φ.symm (threeA hω)).2⟩ : S.M) = eM := by
        apply Subtype.ext
        rw [hφe]
      rw [hρL_apply, harg]
    have hα3 : α ^ 3 = 1 := by
      rw [hα]
      rw [← map_pow]
      have h3 : eM ^ 3 = 1 := by
        apply Subtype.ext
        show e ^ 3 = 1
        rw [← he_order, pow_orderOf_eq_one]
      rw [h3, map_one]
    have hcent : ¬ 3 ∣ Nat.card ↥(Subgroup.center S.Q) := by
      rw [S.card_center_Q]
      norm_num
    have hN : ∀ n ∈ Subgroup.center S.Q, α n ∈ Subgroup.center S.Q := by
      intro r hr
      rw [Subgroup.mem_center_iff] at hr ⊢
      intro z
      obtain ⟨z', rfl⟩ := α.surjective z
      rw [← map_mul, ← map_mul, hr z']
    have hW : LinearMap.eqLocus (ρL (threeA hω) : S.Qt →ₗ[ZMod 2] S.Qt) LinearMap.id =
        S.clSub Qe := by
      apply le_antisymm
      · intro v hv
        obtain ⟨q, hqv⟩ := S.exists_toQt v
        have hfix : ((S.ρ eM : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.toQt q) = S.toQt q := by
          rw [hqv, ← hρe]
          exact hv
        have hmod : α q * q⁻¹ ∈ Subgroup.center S.Q := by
          have h := S.ρ_toQt eM q
          rw [h] at hfix
          have hzero : S.toQt (α q * q⁻¹) = 0 := by
            have hfix' : S.toQt (α q) = S.toQt q := hfix
            rw [S.toQt_mul, S.toQt_inv, hfix']
            exact add_neg_cancel _
          exact (S.toQt_eq_zero_iff _).mp hzero
        obtain ⟨y, hy, hfixy⟩ :=
          CFSG.GroupTheory.CoprimeActionSupport.CoprimeAutomorphismFixedQuotientLift.fixed_lift
            (r := 3) α hα3 (Subgroup.center S.Q) (inferInstance : (Subgroup.center S.Q).Normal)
            hN hcent q hmod
        have hyC : ((y : S.M) : G) ∈ Subgroup.centralizer ({e} : Set G) := by
          have h1 : α y = y := hfixy
          have h2 : e * ((y : S.M) : G) * e⁻¹ = ((y : S.M) : G) := by
            have hc := congrArg (fun z : S.Q => ((z : S.M) : G)) h1
            rw [hα] at hc
            simpa [hconjH] using hc
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc ((y : S.M) : G) * e = (e * ((y : S.M) : G) * e⁻¹) * e := by rw [h2]
            _ = e * ((y : S.M) : G) := by group
        have hyQe : ((y : S.M) : G) ∈ Qe := by
          rw [← hQe_eq]
          exact Subgroup.mem_inf.mpr ⟨S.coe_mem_QG y, hyC⟩
        have hycl : S.cl ((y : S.M) : G) ∈ S.clSub Qe :=
          S.cl_mem_clSub hyQe (S.coe_mem_QG y)
        have hyq : S.toQt y = S.toQt q := by
          have h0 : S.toQt (y * q⁻¹) = 0 := (S.toQt_eq_zero_iff (y * q⁻¹)).mpr hy
          rw [S.toQt_mul, S.toQt_inv] at h0
          exact add_neg_eq_zero.mp h0
        rw [← hqv, ← hyq, ← S.cl_coe y]
        exact hycl
      · intro v hv
        obtain ⟨y, hyQe, hyQG, rfl⟩ := S.mem_clSub_iff.mp hv
        show (ρL (threeA hω)) (S.cl y) = S.cl y
        rw [hρe]
        rw [S.ρ_cl eM hyQG]
        have hyC : y ∈ Subgroup.centralizer ({e} : Set G) := by
          have h : y ∈ S.QG ⊓ Subgroup.centralizer ({e} : Set G) := hQe_eq ▸ hyQe
          exact (Subgroup.mem_inf.mp h).2
        have hconj : e * y * e⁻¹ = y := by
          have h := Subgroup.mem_centralizer_iff.mp hyC e rfl
          calc e * y * e⁻¹ = (y * e) * e⁻¹ := by rw [h]
            _ = y := by group
        rw [hconj]
    rw [hW]
    have hpre : S.clPre (S.clSub Qe) = Qe := S.clPre_clSub hQe_le hzQe
    have hcard : Nat.card ↥(S.clPre (S.clSub Qe)) = 2 * Nat.card ↥(S.clSub Qe) :=
      S.card_clPre (S.clSub Qe)
    rw [hpre, hcardQe] at hcard
    have hcard2 : Nat.card ↥(S.clSub Qe) = 2 ^ 8 := by
      rw [show (2 : ℕ) ^ 9 = 2 * 2 ^ 8 by norm_num] at hcard
      omega
    have hcard3 : Nat.card ↥(S.clSub Qe) = 2 ^ Module.finrank (ZMod 2) ↥(S.clSub Qe) :=
      S.card_submodule (S.clSub Qe)
    have hpow : (2 : ℕ) ^ 8 = 2 ^ Module.finrank (ZMod 2) ↥(S.clSub Qe) := by
      rw [← hcard3, hcard2]
    exact Nat.pow_right_injective (a := 2) (by norm_num) hpow.symm
  have hfin : Module.finrank (ZMod 2) S.Qt = 20 :=
    finrank_eq_twenty_of_finrank_fixed_threeA hS.card_K hω ρL htor h8
  have h2w : 2 * S.width = 20 := by
    have h := S.finrank_Qt_eq_two_mul_width
    rw [hfin] at h
    exact h.symm
  omega

theorem exists_setting_width_ten [Finite G] [Finite K] (hG : IsCharTwoType G)
    (hS : LocalSetting hω b L φ Bs)
    {t : G} (ht : t ∈ Subgroup.normalizer (Bs : Set G)) (ht2 : orderOf t = 2)
    (htb : t * b * t⁻¹ = b⁻¹) (htL : t ∈ Subgroup.centralizer (L : Set G))
    (hnA : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ hnL : n * b * n⁻¹ ∈ L,
      φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω ∧ n⁻¹ * t * n ∈
        (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G)) :
    ∃ S : CFSG.LargeExtraspecial.Setting G, S.z = t ∧
      S.QG = pCoreOf 2 (Subgroup.centralizer {t}) ∧ S.width = 10 := by
  exact ⟨settingOfInvolution hG hS ht ht2 htb htL hnA, rfl, rfl,
    settingOfInvolution_width hG hS ht ht2 htb htL hnA⟩

end LocalSetting

end CFSG.StandardType.USixTwo

end
