module

public import CFSG.Quasithin.EmptyFaithful.S151T1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem s151t_altType_three_of_solvable [Finite G] {K : Subgroup G} (hK : IsShort2 K)
    (hsolv : Group.IsSolvable ↥K) : IsAltType K 3 := by
  have h3 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
    rcases hK.2.2.2.1 with hq | h3
    · exfalso
      have hQs : Group.IsSolvable (↥K ⧸ CFSG.pCore 2 ↥K) :=
        Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))
      have : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) := hq.1
      exact Group.IsPerfect.not_isSolvable (↥K ⧸ CFSG.pCore 2 ↥K) hQs
    · exact h3
  exact CFSG.Quasithin.C1Pack.isAltType_three_of_card_three hK h3

theorem s151t_comm_mul_of_central {a x z : G} (hza : z * a = a * z) :
    ⁅a, x * z⁆ = ⁅a, x⁆ := by
  have h1 : z * a⁻¹ = a⁻¹ * z := by
    have := congrArg (fun t => a⁻¹ * t * a⁻¹) hza
    simp only [mul_assoc, inv_mul_cancel_left] at this
    simpa [mul_assoc] using this.symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * (x * z) * a⁻¹ * (z⁻¹ * x⁻¹) = a * x * (z * a⁻¹ * z⁻¹) * x⁻¹ := by group
    _ = a * x * (a⁻¹ * z * z⁻¹) * x⁻¹ := by rw [h1]
    _ = a * x * a⁻¹ * x⁻¹ := by group

namespace WreathCfg

variable {L P S : Subgroup G} {s : G} (c : WreathCfg L P S s)
include c

theorem N_solvable [Finite G] : Group.IsSolvable ↥(P ⊔ B6.conjSub s P) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp c.par.syl.2.1
  have hcardP : Nat.card ↥P = 2 ^ n * 3 := by
    have h := c.par.idx
    rw [hn] at h
    rw [h]; ring
  have hPs : Group.IsSolvable ↥P := zb_isSolvable_of_card hcardP
  have hP's : Group.IsSolvable ↥(B6.conjSub s P) :=
    Group.isSolvable_of_surjective (f := ((MulAut.conj s).subgroupMap P).toMonoidHom)
      ((MulAut.conj s).subgroupMap P).surjective
  have hcomm : ∀ (p : ↥P) (p' : ↥(B6.conjSub s P)),
      Commute (P.subtype p) ((B6.conjSub s P).subtype p') := fun p p' =>
    Subgroup.mem_centralizer_iff.mp (c.P'_le_centralizer p'.2) p p.2
  have hrange : (MonoidHom.noncommCoprod P.subtype (B6.conjSub s P).subtype hcomm).range =
      P ⊔ B6.conjSub s P := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  obtain ⟨f, hf⟩ : ∃ f : ↥P × ↥(B6.conjSub s P) →* G, f.range = P ⊔ B6.conjSub s P := ⟨_, hrange⟩
  rw [← hf]
  exact Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective

theorem not_C126Third [Finite G] : ¬ C126Third (P ⊔ S) S := by
  rintro ⟨r, K, hr, hK, hcommK, hres, hperm, -⟩
  have : Group.IsSolvable ↥(P ⊔ B6.conjSub s P) := c.N_solvable
  have hNH : P ⊔ B6.conjSub s P ≤ P ⊔ S := by
    calc P ⊔ B6.conjSub s P ≤ (P ⊔ B6.conjSub s P) ⊔ S := le_sup_left
      _ = P ⊔ S := c.H_eq.symm
  have hHN : P ⊔ S ≤ Subgroup.normalizer ((P ⊔ B6.conjSub s P : Subgroup G) : Set G) := by
    rw [c.H_eq]
    exact sup_le Subgroup.le_normalizer c.S_le_normalizer_N
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = twoResidual (P ⊔ S) := ⟨_, rfl⟩
  have hres' : W = ⨆ i, K i := by rw [hWdef]; exact hres
  have hWN : W ≤ P ⊔ B6.conjSub s P := by
    rw [hWdef]; exact twoResidual_le_of_isTwoQuotient hNH hHN c.two_pow
  have hHW : P ⊔ S ≤ Subgroup.normalizer (W : Set G) := by
    rw [hWdef]; exact le_normalizer_twoResidual _
  have hKW : ∀ i, K i ≤ W := fun i => by rw [hres']; exact le_iSup K i
  have hKN : ∀ i, K i ≤ P ⊔ B6.conjSub s P := fun i => (hKW i).trans hWN
  have hshort : ∀ i, IsShort2 (K i) := fun i => (hK i).1.1.1
  have hA3 : ∀ i, IsAltType (K i) 3 := fun i =>
    s151t_altType_three_of_solvable (hshort i)
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (hKN i)))
  have hWK : ∀ i, W ≤ Subgroup.normalizer (K i : Set G) := by
    intro i
    rw [hres']
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · subst hij
      exact Subgroup.le_normalizer
    · have h1 : ⁅K i, K j⁆ = ⊥ := hcommK i j (Ne.symm hij)
      have h2 : K j ≤ Subgroup.centralizer (K i : Set G) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
        exact h1
      exact h2.trans (Subgroup.centralizer_le_normalizer _)
  have hQp : IsPGroup 2 ↥(pCoreOf 2 W) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W
  have hQW : pCoreOf 2 W ≤ W := CFSG.LieType.BorelTits.pCoreOf_le 2 W
  have hWQ : W ≤ Subgroup.normalizer ((pCoreOf 2 W : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 W
  have hXp : IsPGroup 2 ↥(pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hXP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hNX : P ⊔ B6.conjSub s P ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) :=
    fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (c.N_le_normalizer_P hg)
  have hWX : W ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) := hWN.trans hNX
  have hRp : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hRL : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hRP : pCoreOf 2 L ≤ P := (c.par.syl.pCoreOf_le).trans c.par.sl
  have hPR : P ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    c.par.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hRX : pCoreOf 2 L ≤ pCoreOf 2 P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRP hPR hRp
  have hP'CR : B6.conjSub s P ≤ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
    (((B6.conjSub s).le_iff_le.mpr c.par.le).trans c.L'_le_centralizer).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRL))
  have hNR : P ⊔ B6.conjSub s P ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    sup_le hPR (hP'CR.trans (Subgroup.centralizer_le_normalizer _))
  have hmain : ∀ j, ∀ x ∈ P, orderOf x = 3 → ∀ p'' ∈ B6.conjSub s P, orderOf (x * p'') = 3 →
      x * p'' ∈ K j → False := by
    intro j x hxP hx3 p'' hp'' hy3 hyK
    have hp''C : p'' ∈ Subgroup.centralizer (P : Set G) := c.P'_le_centralizer hp''
    have hxp'' : x * p'' = p'' * x := Subgroup.mem_centralizer_iff.mp hp''C x hxP
    obtain ⟨y, hydef⟩ : ∃ y : G, y = x * p'' := ⟨_, rfl⟩
    rw [← hydef] at hy3 hyK
    have hyW : y ∈ W := hKW j hyK
    obtain ⟨hcard, hdisj⟩ := zb_commutator_card_le hQp
      ((hKW j).trans hWQ) (hQW.trans (hWK j)) (hshort j) (hA3 j) hyK hy3
    set Py : Subgroup G := Subgroup.zpowers y with hPy
    have hPyW : Py ≤ W := by rw [hPy, Subgroup.zpowers_le]; exact hyW
    have hPyQ : Py ≤ Subgroup.normalizer ((pCoreOf 2 W : Subgroup G) : Set G) := hPyW.trans hWQ
    have hPyX : Py ≤ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) := hPyW.trans hWX
    have hPyR : Py ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
      (hPyW.trans hWN).trans hNR
    have hcopC : ∀ {A : Subgroup G}, IsPGroup 2 ↥A → Nat.Coprime (Nat.card ↥Py) (Nat.card ↥A) := by
      intro A hA
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
      rw [hPy, Nat.card_zpowers, hy3, hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hsolvC : ∀ {A : Subgroup G}, IsPGroup 2 ↥A → Group.IsSolvable ↥A := by
      intro A hA
      have hnil : Group.IsNilpotent ↥A := hA.isNilpotent
      infer_instance
    have e1Q : ⁅⁅pCoreOf 2 W, Py⁆, Py⁆ = ⁅pCoreOf 2 W, Py⁆ :=
      zb_commutator_double_eq_self Py _ hPyQ (hcopC hQp) (hsolvC hQp)
    have hW3 : ⁅⁅⁅pCoreOf 2 W, Py⁆, Py⁆, Py⁆ = ⁅pCoreOf 2 W, Py⁆ := by rw [e1Q, e1Q]
    rw [hW3] at hcard hdisj
    have e1X : ⁅⁅pCoreOf 2 P, Py⁆, Py⁆ = ⁅pCoreOf 2 P, Py⁆ :=
      zb_commutator_double_eq_self Py _ hPyX (hcopC hXp) (hsolvC hXp)
    have hXPyQ : ⁅pCoreOf 2 P, Py⁆ ≤ pCoreOf 2 W := by
      rw [Subgroup.commutator_le]
      intro a ha t ht
      have htW : t ∈ W := hPyW ht
      have haN : a ∈ Subgroup.normalizer (W : Set G) := hHW (Subgroup.mem_sup_left (hXP ha))
      have h1 : ⁅a, t⁆ ∈ W := by
        have e : ⁅a, t⁆ = (a * t * a⁻¹) * t⁻¹ := by simp only [commutatorElement_def, mul_assoc]
        rw [e]
        exact W.mul_mem ((Subgroup.mem_normalizer_iff.mp haN t).mp htW) (W.inv_mem htW)
      have h2 : ⁅a, t⁆ ∈ pCoreOf 2 P := by
        have e : ⁅a, t⁆ = a * (t * a⁻¹ * t⁻¹) := by simp only [commutatorElement_def, mul_assoc]
        rw [e]
        have htN : t ∈ Subgroup.normalizer ((pCoreOf 2 P : Subgroup G) : Set G) := hPyX ht
        exact (pCoreOf 2 P).mul_mem ha ((Subgroup.mem_normalizer_iff.mp htN a⁻¹).mp
          ((pCoreOf 2 P).inv_mem ha))
      have hXW : pCoreOf 2 P ⊓ W ≤ pCoreOf 2 W :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
          (fun g hg => zb_mem_normalizer_inf (hWX hg) (Subgroup.le_normalizer hg))
          (hXp.to_le inf_le_left)
      exact hXW ⟨h2, h1⟩
    have hXV : ⁅pCoreOf 2 P, Py⁆ ≤ ⁅pCoreOf 2 W, Py⁆ := by
      rw [← e1X]
      exact Subgroup.commutator_mono hXPyQ le_rfl
    set Y : Subgroup G := ⁅pCoreOf 2 L, Py⁆ with hYdef
    have hYR : Y ≤ pCoreOf 2 L := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPyR
    have hYX : Y ≤ ⁅pCoreOf 2 P, Py⁆ := Subgroup.commutator_mono hRX le_rfl
    have hYV : Y ≤ ⁅pCoreOf 2 W, Py⁆ := hYX.trans hXV
    have hYC : Y ⊓ Subgroup.centralizer (Py : Set G) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right _ hYV).trans hdisj.le)
    have hY0 : Y ≠ ⊥ := by
      intro hY
      have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have h1 : ⁅q, y⁆ ∈ Y := Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers y)
        rw [hY] at h1
        have h2 : q * y = y * q := commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
        have h3 : q * p'' = p'' * q := Subgroup.mem_centralizer_iff.mp (hP'CR hp'') q hq
        rw [hydef] at h2
        have h4 : q * x * p'' = x * q * p'' := by
          calc q * x * p'' = q * (x * p'') := by group
            _ = (x * p'') * q := h2
            _ = x * (p'' * q) := by group
            _ = x * (q * p'') := by rw [h3]
            _ = x * q * p'' := by group
        exact mul_right_cancel h4
      have hxR : x ∈ pCoreOf 2 L := c.blk.1.2.1 ⟨c.par.le hxP, hxC⟩
      exact zb_not_mem_of_orderOf_three hRp hxR hx3
    have hYp : IsPGroup 2 ↥Y := hRp.to_le hYR
    have hYy : y ∈ Subgroup.normalizer (Y : Set G) :=
      CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPyR (Subgroup.mem_zpowers y)
    have hY4 : 4 ≤ Nat.card ↥Y := zb_card_ge_four hYp hYy hY0 hYC
    have hVcard : Nat.card ↥(⁅pCoreOf 2 P, Py⁆ : Subgroup G) ≤ 4 :=
      (Subgroup.card_le_of_le hXV).trans hcard
    have hYeq : Y = ⁅pCoreOf 2 P, Py⁆ := Subgroup.eq_of_le_of_card_ge hYX (hVcard.trans hY4)
    apply c.big x hxP hx3
    have hgen : ⁅pCoreOf 2 P, Subgroup.zpowers x⁆ ≤ ⁅pCoreOf 2 P, Py⁆ := by
      rw [Subgroup.commutator_le]
      intro a ha t ht
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      have hyk : y ^ k = x ^ k * p'' ^ k := by
        rw [hydef]
        exact Commute.mul_zpow (show Commute x p'' from hxp'') k
      have hzC : p'' ^ k ∈ Subgroup.centralizer (P : Set G) := zpow_mem hp''C k
      have hza : p'' ^ k * a = a * p'' ^ k :=
        (Subgroup.mem_centralizer_iff.mp hzC a (hXP ha)).symm
      have : ⁅a, x ^ k⁆ = ⁅a, y ^ k⁆ := by
        rw [hyk]
        exact (s151t_comm_mul_of_central hza).symm
      rw [this]
      exact Subgroup.commutator_mem_commutator ha (Subgroup.zpow_mem_zpowers y k)
    exact (hgen.trans (le_of_eq hYeq.symm)).trans hYR
  have hr0 : 0 < r := hr
  obtain ⟨y₀, hy₀K, hy₀3⟩ := zb_exists_orderOf_three (hA3 ⟨0, hr0⟩)
  obtain ⟨p, hp, p', hp', hpp'⟩ := c.mem_N (hKN ⟨0, hr0⟩ hy₀K)
  have hcomm : p * p' = p' * p := Subgroup.mem_centralizer_iff.mp (c.P'_le_centralizer hp') p hp
  have hy₀cube : (p * p') ^ 3 = 1 := by
    rw [← hpp']
    simpa [hy₀3] using pow_orderOf_eq_one y₀
  have hpcube : p ^ 3 ∈ pCoreOf 2 L := by
    have h1 : p ^ 3 * p' ^ 3 = 1 := by
      rw [← (show Commute p p' from hcomm).mul_pow]
      exact hy₀cube
    have h2 : p ^ 3 = (p' ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : p ^ 3 ∈ B6.conjSub s P := by
      rw [h2]
      exact (B6.conjSub s P).inv_mem ((B6.conjSub s P).pow_mem hp' 3)
    exact c.PP'_inf_le ⟨P.pow_mem hp 3, h3⟩
  obtain ⟨m, hm⟩ := hRp ⟨p ^ 3, hpcube⟩
  have hm' : (p ^ 3) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hx3pow : (p ^ 2 ^ m) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hm'
  have hy₁ : y₀ ^ 2 ^ m = p ^ 2 ^ m * p' ^ 2 ^ m := by
    rw [hpp']
    exact (show Commute p p' from hcomm).mul_pow _
  have hy₁K : p ^ 2 ^ m * p' ^ 2 ^ m ∈ K ⟨0, hr0⟩ := by
    rw [← hy₁]
    exact (K ⟨0, hr0⟩).pow_mem hy₀K _
  have hy₁3 : orderOf (p ^ 2 ^ m * p' ^ 2 ^ m) = 3 := by
    rw [← hy₁]
    have hcop : Nat.Coprime (orderOf y₀) (2 ^ m) := by
      rw [hy₀3]
      exact Nat.Coprime.pow_right _ (by norm_num)
    rw [Nat.Coprime.orderOf_pow hcop, hy₀3]
  have hxP : p ^ 2 ^ m ∈ P := P.pow_mem hp _
  have hp'' : p' ^ 2 ^ m ∈ B6.conjSub s P := (B6.conjSub s P).pow_mem hp' _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hx1 : p ^ 2 ^ m = 1
  ·
    rw [hx1, one_mul] at hy₁K hy₁3
    have hzP : s⁻¹ * p' ^ 2 ^ m * s ∈ P := B6.mem_conjSub.mp hp''
    have hzo : orderOf (s⁻¹ * p' ^ 2 ^ m * s) = 3 := by
      have := orderOf_injective (MulAut.conj s⁻¹).toMonoidHom (MulAut.conj s⁻¹).injective
        (p' ^ 2 ^ m)
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
        inv_inv] at this
      rw [this]
      exact hy₁3
    obtain ⟨j, hj⟩ := hperm s⁻¹ (S.inv_mem c.hs) ⟨0, hr0⟩
    have hzK : s⁻¹ * p' ^ 2 ^ m * s ∈ K j := by
      rw [← hj, B6.mem_conjSub]
      have e : (s⁻¹)⁻¹ * (s⁻¹ * p' ^ 2 ^ m * s) * s⁻¹ = p' ^ 2 ^ m := by group
      rw [e]
      exact hy₁K
    exact hmain j _ hzP hzo 1 (B6.conjSub s P).one_mem (by simpa using hzo) (by simpa using hzK)
  · have hxo : orderOf (p ^ 2 ^ m) = 3 := orderOf_eq_prime hx3pow hx1
    exact hmain ⟨0, hr0⟩ _ hxP hxo _ hp'' hy₁3 hy₁K

end WreathCfg

end CFSG.Quasithin
