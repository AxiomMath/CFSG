module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitSolvableQuaternion
public import CFSG.ClassicalInvolution.Asc77.AscS16A
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
public import CFSG.RankThree.S4Free.StellmacherThmA
public import CFSG.ClassicalInvolution.Q3.SP3Odd
public import CFSG.ClassicalInvolution.Asc77.AscE186CentB
public import CFSG.ClassicalInvolution.Asc77.AscFusionR4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotGen
public import CFSG.ClassicalInvolution.Q3.TL3DichComm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
open scoped Pointwise

theorem isPGroup_two_of_hypOmegaGen_solvable_threePrime
    {Y : Type} [Group Y] [Finite Y] [Group.IsSolvable Y]
    {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (hO : classicalInvolutionOddCore Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    {K : Subgroup Y} (hK : K ∈ Ω) : IsPGroup 2 K := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hsub := Q3.PhilipHall.QuaternionBridge.CentQ.isSubnormal_centralizer_gen hΩ hK hz
  have hC : centralizer (CFSG.pCore 2 Y : Set Y) ≤ CFSG.pCore 2 Y := by
    apply Q3.Twin.centralizer_pCore_le inferInstance
    intro N hN hNodd
    exact le_bot_iff.mp ((le_sSup ⟨hN, hNodd⟩ : N ≤ classicalInvolutionOddCore Y).trans hO.le)
  have hOK : classicalInvolutionOddCore K = ⊥ :=
    Q3.SP3.oddCore_eq_bot_of_isSubnormal_centralizer CFSG.pCore_isPGroup hC hz.sq hsub
  obtain ⟨_, R, hRK, _⟩ := hΩ.omega1 K hK
  obtain ⟨k, hk, ⟨eR⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ
    (mem_RSet_of_isSylow2In hK hRK)
  let S : Sylow 2 K := AscL62.sylowOfIsSylow2In'' hRK
  let eS : (S : Subgroup K) ≃* QuaternionGroup (2 ^ k) :=
    (Subgroup.subgroupOfEquivOfLe hRK.1).trans eR
  exact isPGroup_two_of_quaternion_of_oddCore_eq_bot_of_threePrime hOK
    (fun hdvd => h3 (hdvd.trans (Subgroup.card_subgroup_dvd_card K))) S hk eS

theorem index_fixV_pair_le_eight_of_commutator_bounds
    {V : Type} [CommGroup V] [Finite V] (α β : MulAut V) (Z : Subgroup V)
    (hZ : Nat.card Z ≤ 2)
    (hD : ∀ v : V, CFSG.Quasithin.commHom β (CFSG.Quasithin.commHom α v) ∈ Z)
    (hker : ∀ v : V, CFSG.Quasithin.commHom β (CFSG.Quasithin.commHom α v) = 1 →
      CFSG.Quasithin.commHom α v ∈ Z ∧ CFSG.Quasithin.commHom β v ∈ Z) :
    (CFSG.Quasithin.fixV (zpowers α ⊔ zpowers β)).index ≤ 8 := by
  let a := CFSG.Quasithin.commHom α
  let b := CFSG.Quasithin.commHom β
  let d := b.comp a
  let f := a.prod b
  have hdZ : d.range ≤ Z := by
    rintro _ ⟨v, rfl⟩
    exact hD v
  have hdcard : Nat.card d.range ≤ 2 :=
    (Subgroup.card_le_of_le hdZ).trans hZ
  have hfd : f.ker ≤ d.ker := by
    intro v hv
    have ha : a v = 1 := congrArg Prod.fst (MonoidHom.mem_ker.mp hv)
    exact MonoidHom.mem_ker.mpr (by change b (a v) = 1; rw [ha, map_one])
  let r := f.domRestrict d.ker
  have hrZ : r.range ≤ Z.prod Z := by
    rintro _ ⟨v, rfl⟩
    exact hker v v.2
  have hrcard : Nat.card r.range ≤ 4 := by
    have h := Subgroup.card_le_of_le hrZ
    have hzprod : Nat.card (Z.prod Z) = Nat.card Z * Nat.card Z :=
      (Nat.card_congr (Subgroup.prodEquiv Z Z).toEquiv).trans (Nat.card_prod Z Z)
    rw [hzprod] at h
    nlinarith
  have hkerEq : r.ker = f.ker.subgroupOf d.ker := rfl
  have hkerCard : Nat.card r.ker = Nat.card f.ker := by
    rw [hkerEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hfd).toEquiv
  have hr := Subgroup.card_ker_mul_card_range r
  rw [hkerCard] at hr
  have hd := Subgroup.card_ker_mul_card_range d
  have hfix : f.ker = CFSG.Quasithin.fixV (zpowers α ⊔ zpowers β) := by
    rw [CFSG.Quasithin.FixVLat.fixV_sup_eq]
    exact (MonoidHom.ker_prod a b).trans (by
      rw [CFSG.Quasithin.ker_commHom, CFSG.Quasithin.ker_commHom])
  have hbound : Nat.card V ≤ Nat.card f.ker * 8 := by
    calc Nat.card V = Nat.card d.ker * Nat.card d.range := hd.symm
      _ ≤ (Nat.card f.ker * 4) * 2 := Nat.mul_le_mul (by nlinarith [hr]) hdcard
      _ = Nat.card f.ker * 8 := by ring
  rw [hfix] at hbound
  have hi := (CFSG.Quasithin.fixV (zpowers α ⊔ zpowers β)).card_mul_index
  have hp : 0 < Nat.card (CFSG.Quasithin.fixV (zpowers α ⊔ zpowers β)) := Nat.card_pos
  nlinarith

private theorem rank_index_le_of_index_le_two_pow
    {V : Type} [Group V] [Finite V] (F : Subgroup V) {n : ℕ} (hF : F.index ≤ 2 ^ n) :
    CFSG.Quasithin.rkIdx F ≤ n := by
  have hd : 2 ^ CFSG.Quasithin.rkIdx F ≤ F.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero F.index_ne_zero_of_finite) pow_padicValNat_dvd
  by_contra h
  have hp : 2 ^ (n + 1) ≤ 2 ^ CFSG.Quasithin.rkIdx F :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have ht : 2 ^ n < 2 ^ (n + 1) := by
    rw [pow_succ]
    have : 0 < 2 ^ n := by positivity
    omega
  omega

private theorem eq_bot_of_index_fixV_le_two
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H A : Subgroup (MulAut V)} (hsol : Group.IsSolvable H)
    (hO2 : CFSG.Open.pCoreOf 2 H = ⊥) (h3 : ¬ 3 ∣ Nat.card H)
    (hAH : A ≤ H) (hA : CFSG.Quasithin.IsElemAbelian2 A)
    (hidx : (CFSG.Quasithin.fixV A).index ≤ 2) : A = ⊥ := by
  have hS3 : ∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 →
      a * y * a⁻¹ = y⁻¹ → y = 1 := by
    intro a ha y hy _ hy3 _
    have hord : orderOf (⟨y, hy⟩ : H) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hy3)
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)
    · exact False.elim (h3 (h ▸ orderOf_dvd_natCard (⟨y, hy⟩ : H)))
  have hb := CFSG.RankThree.S4Free.Stell.two_mul_rk_le_rkIdx_of_isSolvable
    hV hsol hO2 hS3 hAH hA
  have hi : CFSG.Quasithin.rkIdx (CFSG.Quasithin.fixV A) ≤ 1 :=
    rank_index_le_of_index_le_two_pow _ (by simpa using hidx)
  exact (CFSG.Quasithin.rk_eq_zero_iff_of_isPGroup hA.isPGroup).mp (by omega)

private theorem elementary_pair {V : Type} [CommGroup V] (α β : MulAut V)
    (hα : α * α = 1) (hβ : β * β = 1) (hαβ : α * β = β * α) :
    CFSG.Quasithin.IsElemAbelian2 (zpowers α ⊔ zpowers β) := by
  have heq : zpowers α ⊔ zpowers β = Subgroup.closure ({α, β} : Set (MulAut V)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  have he : IsElemAbelian 2 (Subgroup.closure ({α, β} : Set (MulAut V))) :=
    CFSG.ClassicalInvolution.Balance.Theorem5.isElemAbelian_closure_of_commuting_involutions
      (by rintro x (rfl | rfl) <;> assumption)
      (by rintro x (rfl | rfl) y (rfl | rfl) <;> first | rfl | exact hαβ | exact hαβ.symm)
  rw [← heq] at he
  exact ⟨fun x hx y hy => congrArg Subtype.val (he.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩),
    he.2⟩

theorem commutator_pair_bounds_of_hypOmegaGen
    {Y : Type} [Group Y] [Finite Y]
    {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    {K E : Subgroup Y} (hK : K ∈ Ω) (hK2 : IsPGroup 2 K)
    [E.Normal] (hE : ∀ e ∈ E, e * e = 1)
    {z a b : Y} (hz : IsUniqueInvolution K z) (hzE : z ∈ E)
    (ha : a ∈ K) (hb : b ∈ K)
    (hab : a * b = z * (b * a))
    (e : Y) (he : e ∈ E) :
    let δa := a * e * a⁻¹ * e⁻¹
    let δb := b * e * b⁻¹ * e⁻¹
    let δab := b * δa * b⁻¹ * δa⁻¹
    (δab = 1 ∨ δab = z) ∧
      (δab = 1 → (δa = 1 ∨ δa = z) ∧ (δb = 1 ∨ δb = z)) := by
  have he1 : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hE e he)
  have hze : e * z * e⁻¹ = z := by
    have hcomm : e * z = z * e := by
      have hsq := hE (e * z) (E.mul_mem he hzE)
      calc e * z = (e * z)⁻¹ := (inv_eq_of_mul_eq_one_right hsq).symm
        _ = z * e := by rw [mul_inv_rev, he1, inv_eq_of_mul_eq_one_right hz.sq]
    rw [hcomm]
    group
  have hK' : conjSub e K ∈ Ω := hΩ.conjInvariant e K hK
  have hz' : IsUniqueInvolution (conjSub e K) z := by
    simpa [hze] using hz.conj e
  by_cases hn : conjSub e K = K
  · have ha' : a * e * a⁻¹ * e⁻¹ ∈ K ⊓ E := by
      constructor
      · have hc : e * a⁻¹ * e⁻¹ ∈ K := hn ▸ conj_mem_conjSub (K.inv_mem ha)
        simpa [mul_assoc] using K.mul_mem ha hc
      · exact E.mul_mem (Subgroup.Normal.conj_mem inferInstance e he a) (E.inv_mem he)
    have hb' : b * e * b⁻¹ * e⁻¹ ∈ K ⊓ E := by
      constructor
      · have hc : e * b⁻¹ * e⁻¹ ∈ K := hn ▸ conj_mem_conjSub (K.inv_mem hb)
        simpa [mul_assoc] using K.mul_mem hb hc
      · exact E.mul_mem (Subgroup.Normal.conj_mem inferInstance e he b) (E.inv_mem he)
    have haZ := hz.unique _ ha'.1 (hE _ ha'.2)
    have hbZ := hz.unique _ hb'.1 (hE _ hb'.2)
    have hδ : b * (a * e * a⁻¹ * e⁻¹) * b⁻¹ * (a * e * a⁻¹ * e⁻¹)⁻¹ = 1 := by
      rcases haZ with h | h
      · rw [h]; group
      · rw [h]
        calc b * z * b⁻¹ * z⁻¹ = z * b * b⁻¹ * z⁻¹ := by rw [← hz.commute_of_mem hb]
          _ = 1 := by group
    exact ⟨Or.inl hδ, fun _ => ⟨haZ, hbZ⟩⟩
  · have hcomm := Sec6Gen.commutes_of_twin_of_isPGroup hΩ hK hK' (Ne.symm hn) hz hz'
      le_rfl le_rfl (IsPGroup.to_sup_of_normal_left' hK2 (hK2.map (MulAut.conj e).toMonoidHom)
        (Sec6Gen.le_normalizer_of_twin hΩ hK' hK hn hz' hz))
    have hc : b * (e * a * e⁻¹) = (e * a * e⁻¹) * b :=
      hcomm b hb _ (conj_mem_conjSub ha)
    have hδ : b * (a * e * a⁻¹ * e⁻¹) * b⁻¹ * (a * e * a⁻¹ * e⁻¹)⁻¹ = z := by
      have hc' : b * (e * a⁻¹ * e⁻¹) = (e * a⁻¹ * e⁻¹) * b :=
        by simpa only [mul_inv_rev, inv_inv, mul_assoc] using (Commute.inv_right hc).eq
      have hba : b * a * b⁻¹ = z * a := by
        have h1 : b * a = z * (a * b) := by
          calc b * a = z * (z * (b * a)) := by rw [← mul_assoc, hz.sq, one_mul]
            _ = z * (a * b) := by rw [← hab]
        rw [h1]
        group
      calc b * (a * e * a⁻¹ * e⁻¹) * b⁻¹ * (a * e * a⁻¹ * e⁻¹)⁻¹ =
          (b * a * b⁻¹) * (e * a⁻¹ * e⁻¹) * ((e * a⁻¹ * e⁻¹)⁻¹ * a⁻¹) := by
            have hC : b * (e * a⁻¹ * e⁻¹) * b⁻¹ = e * a⁻¹ * e⁻¹ := by rw [hc']; group
            calc _ = (b * a * b⁻¹) * (b * (e * a⁻¹ * e⁻¹) * b⁻¹) *
                ((e * a⁻¹ * e⁻¹)⁻¹ * a⁻¹) := by group
              _ = _ := by rw [hC]
        _ = z := by rw [hba]; group
    exact ⟨Or.inr hδ, fun h => False.elim (hz.ne_one (hδ.symm.trans h))⟩

theorem pair_eq_one_of_commutator_bounds_solvable_threePrime
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} (hsol : Group.IsSolvable H)
    (hO2 : CFSG.Open.pCoreOf 2 H = ⊥) (h3 : ¬ 3 ∣ Nat.card H)
    (α β : MulAut V) (hαH : α ∈ H) (hβH : β ∈ H)
    (hα : α * α = 1) (hβ : β * β = 1) (hαβ : α * β = β * α)
    (Z : Subgroup V) (hZ : Nat.card Z ≤ 2)
    (hD : ∀ v : V, CFSG.Quasithin.commHom β (CFSG.Quasithin.commHom α v) ∈ Z)
    (hker : ∀ v : V, CFSG.Quasithin.commHom β (CFSG.Quasithin.commHom α v) = 1 →
      CFSG.Quasithin.commHom α v ∈ Z ∧ CFSG.Quasithin.commHom β v ∈ Z) :
    α = 1 ∧ β = 1 := by
  let A := zpowers α ⊔ zpowers β
  have hAH : A ≤ H := sup_le (zpowers_le.mpr hαH) (zpowers_le.mpr hβH)
  have hAe : CFSG.Quasithin.IsElemAbelian2 A := elementary_pair α β hα hβ hαβ
  have hS3 : ∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 →
      a * y * a⁻¹ = y⁻¹ → y = 1 := by
    intro a ha y hy _ hy3 _
    have hord : orderOf (⟨y, hy⟩ : H) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hy3)
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
    · exact congrArg Subtype.val (orderOf_eq_one_iff.mp h)
    · exact False.elim (h3 (h ▸ orderOf_dvd_natCard (⟨y, hy⟩ : H)))
  have hidx : (CFSG.Quasithin.fixV A).index ≤ 8 :=
    index_fixV_pair_le_eight_of_commutator_bounds α β Z hZ hD hker
  have hineq := CFSG.RankThree.S4Free.Stell.two_mul_rk_le_rkIdx_of_isSolvable
    hV hsol hO2 hS3 hAH hAe
  have hrank : CFSG.Quasithin.rk A ≤ 1 := by
    have hi := rank_index_le_of_index_le_two_pow (CFSG.Quasithin.fixV A) (n := 3)
      (by simpa using hidx)
    omega
  have hcard : Nat.card A ≤ 2 := by
    rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup hAe.isPGroup]
    calc 2 ^ CFSG.Quasithin.rk A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrank
      _ = 2 := by norm_num
  have hrel : α = 1 ∨ β = 1 ∨ α = β := by
    by_cases h1 : α = 1
    · exact Or.inl h1
    by_cases h2 : β = 1
    · exact Or.inr (Or.inl h2)
    have hm := CFSG.Walter.W67.P56AbData.eq_of_ne_one_of_card_le_two hcard
      (a := (⟨α, mem_sup_left (mem_zpowers α)⟩ : A))
      (b := (⟨β, mem_sup_right (mem_zpowers β)⟩ : A))
      (fun h => h1 (congrArg Subtype.val h)) (fun h => h2 (congrArg Subtype.val h))
    exact Or.inr (Or.inr (congrArg Subtype.val hm))
  have hzero : ∀ v : V, CFSG.Quasithin.commHom β (CFSG.Quasithin.commHom α v) = 1 := by
    intro v
    rcases hrel with h | h | h
    · simp [h, CFSG.Quasithin.commHom_apply]
    · simp [h, CFSG.Quasithin.commHom_apply]
    · subst β
      have hαα : α (α v) = v := by
        have h := congrArg (fun g : MulAut V => g v) hα
        exact h
      simp only [CFSG.Quasithin.commHom_apply, map_mul, map_inv, hαα, mul_inv_rev, inv_inv]
      have h := hV (v * (α v)⁻¹)
      simpa only [pow_two, mul_assoc] using h
  have hαZ : (CFSG.Quasithin.commHom α).range ≤ Z := by
    rintro _ ⟨v, rfl⟩
    exact (hker v (hzero v)).1
  have hβZ : (CFSG.Quasithin.commHom β).range ≤ Z := by
    rintro _ ⟨v, rfl⟩
    exact (hker v (hzero v)).2
  have hαidx : (CFSG.Quasithin.fixV (zpowers α)).index ≤ 2 := by
    rw [← CFSG.Quasithin.ker_commHom, Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hαZ).trans hZ
  have hβidx : (CFSG.Quasithin.fixV (zpowers β)).index ≤ 2 := by
    rw [← CFSG.Quasithin.ker_commHom, Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hβZ).trans hZ
  have haBot := eq_bot_of_index_fixV_le_two hV hsol hO2 h3
    (zpowers_le.mpr hαH) ⟨fun a ha b hb => hAe.1 a (mem_sup_left ha) b (mem_sup_left hb),
      fun a ha => hAe.2 a (mem_sup_left ha)⟩ hαidx
  have hbBot := eq_bot_of_index_fixV_le_two hV hsol hO2 h3
    (zpowers_le.mpr hβH) ⟨fun a ha b hb => hAe.1 a (mem_sup_right ha) b (mem_sup_right hb),
      fun a ha => hAe.2 a (mem_sup_right ha)⟩ hβidx
  exact ⟨by have h := mem_zpowers α; rw [haBot, mem_bot] at h; exact h,
    by have h := mem_zpowers β; rw [hbBot, mem_bot] at h; exact h⟩

theorem le_centralizer_of_hypOmegaGen_of_mem_minimal_normal_two
    {Y : Type} [Group Y] [Finite Y] [Group.IsSolvable Y]
    {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) (h3 : ¬ 3 ∣ Nat.card Y)
    {K E : Subgroup Y} (hK : K ∈ Ω) (hK2 : IsPGroup 2 K)
    [E.Normal] [CFSG.IsMinimalNormal E] (hEne : E ≠ ⊥) (hE2 : IsPGroup 2 E)
    {z : Y} (hz : IsUniqueInvolution K z) (hzE : z ∈ E) :
    K ≤ centralizer (E : Set Y) := by
  have hel := CFSG.Glauberman.minimalNormal_pSubgroup_isElementaryAbelian E hEne hE2
  let : IsMulCommutative E := hel.toIsMulCommutative
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hE : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hel.exponent_dvd_p (⟨e, he⟩ : E)
    have h' : (⟨e, he⟩ : E) ^ 2 = 1 := h
    have h'' := congrArg E.subtype h'
    rw [map_pow, map_one] at h''
    simpa only [Subgroup.subtype_apply, pow_two] using h''
  have hEV : ∀ v : E, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [pow_two] using hE v v.2)
  let ρ : Y →* MulAut E := MulAut.conjNormal
  let H := ρ.range
  have hsol : Group.IsSolvable H := Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  have hker : ρ.ker = centralizer (E : Set Y) :=
    CFSG.RankThreeEvenClassification.Helpers.conjugation_kernel_eq_centralizer E
  have hO2 : CFSG.Open.pCoreOf 2 H = ⊥ := by
    have hQ := CFSG.Glauberman.pCore_quotient_centralizer_eq_bot_of_minimalNormal_pSubgroup E hEne hE2
    have he : (Y ⧸ centralizer (E : Set Y)) ≃* H :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ρ)
    have h := CFSG.pCore_map_iso 2 he
    rw [hQ, Subgroup.map_bot] at h
    rw [CFSG.Open.pCoreOf, ← h, Subgroup.map_bot]
  have hH3 : ¬ 3 ∣ Nat.card H :=
    fun hdvd => h3 (hdvd.trans (Subgroup.card_dvd_of_surjective ρ.rangeRestrict_surjective))
  have hq : IsQuatSub K := by
    have hKK : IsSylow2In K K := ⟨le_rfl, hK2, fun R hR _ hKR => le_antisymm hR hKR⟩
    exact Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hKK)
  obtain ⟨k, hk, ⟨eK⟩⟩ := hq
  have hqK : IsQuatSub K := ⟨k, hk, ⟨eK⟩⟩
  have hρz : ρ z = 1 := by
    ext e
    change z * (e : Y) * z⁻¹ = (e : Y)
    have hc : z * (e : Y) = (e : Y) * z := by
      exact congrArg Subtype.val (mul_comm (⟨z, hzE⟩ : E) e)
    rw [hc]
    group
  have hpair : ∀ a b : Y, a ∈ K → b ∈ K → a * a = z → b * b = z →
      a * b = z * (b * a) → ρ a = 1 := by
    intro a b ha hb ha2 hb2 hab
    let α := ρ a
    let β := ρ b
    have hα : α * α = 1 := by
      change ρ a * ρ a = 1
      rw [← map_mul, ha2, hρz]
    have hβ : β * β = 1 := by
      change ρ b * ρ b = 1
      rw [← map_mul, hb2, hρz]
    have hαβ : α * β = β * α := by
      change ρ a * ρ b = ρ b * ρ a
      rw [← map_mul, hab, map_mul, hρz, one_mul, map_mul]
    let Z := zpowers (⟨z, hzE⟩ : E)
    have hZ : Nat.card Z ≤ 2 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk]
      have hz2 : orderOf z = 2 := orderOf_eq_prime (by simpa [pow_two] using hz.sq) hz.ne_one
      exact hz2.le
    have hval (v : E) :
        ((CFSG.Quasithin.commHom α v : E) : Y) = a * (v : Y) * a⁻¹ * (v : Y)⁻¹ := rfl
    have hbval (v : E) :
        ((CFSG.Quasithin.commHom β v : E) : Y) = b * (v : Y) * b⁻¹ * (v : Y)⁻¹ := rfl
    have hD : ∀ v : E, CFSG.Quasithin.commHom β (CFSG.Quasithin.commHom α v) ∈ Z := by
      intro v
      have ht := commutator_pair_bounds_of_hypOmegaGen hΩ hK hK2 hE hz hzE ha hb hab v v.2
      have hv := hbval (CFSG.Quasithin.commHom α v)
      rw [hval] at hv
      rcases ht.1 with h | h
      · have h1 : CFSG.Quasithin.commHom β (CFSG.Quasithin.commHom α v) = 1 :=
          Subtype.ext (hv.trans h)
        rw [h1]
        exact Z.one_mem
      · have h1 : CFSG.Quasithin.commHom β (CFSG.Quasithin.commHom α v) = (⟨z, hzE⟩ : E) :=
          Subtype.ext (hv.trans h)
        rw [h1]
        exact mem_zpowers _
    have hsmall : ∀ v : E, CFSG.Quasithin.commHom β (CFSG.Quasithin.commHom α v) = 1 →
        CFSG.Quasithin.commHom α v ∈ Z ∧ CFSG.Quasithin.commHom β v ∈ Z := by
      intro v hv
      have ht := commutator_pair_bounds_of_hypOmegaGen hΩ hK hK2 hE hz hzE ha hb hab v v.2
      have hm := hbval (CFSG.Quasithin.commHom α v)
      rw [hval, hv] at hm
      have ht' := ht.2 hm.symm
      constructor
      · rcases ht'.1 with h | h
        · have h1 : CFSG.Quasithin.commHom α v = 1 := Subtype.ext ((hval v).trans h)
          rw [h1]; exact Z.one_mem
        · have h1 : CFSG.Quasithin.commHom α v = (⟨z, hzE⟩ : E) := Subtype.ext ((hval v).trans h)
          rw [h1]; exact mem_zpowers _
      · rcases ht'.2 with h | h
        · have h1 : CFSG.Quasithin.commHom β v = 1 := Subtype.ext ((hbval v).trans h)
          rw [h1]; exact Z.one_mem
        · have h1 : CFSG.Quasithin.commHom β v = (⟨z, hzE⟩ : E) := Subtype.ext ((hbval v).trans h)
          rw [h1]; exact mem_zpowers _
    exact (pair_eq_one_of_commutator_bounds_solvable_threePrime hEV hsol hO2 hH3 α β
      ⟨a, rfl⟩ ⟨b, rfl⟩ hα hβ hαβ Z hZ hD hsmall).1
  have htop : (centralizer (E : Set Y)).subgroupOf K = ⊤ := by
    refine AscFusion.quaternion_generated_by_order_four eK _ ?_
    intro a ha4
    have ha2 : (a : Y) * a = z := by
      have ha4Y : orderOf (a : Y) = 4 := (Subgroup.orderOf_coe a).trans ha4
      have hs : ((a : Y) * a) * ((a : Y) * a) = 1 := by
        have h := pow_orderOf_eq_one (a : Y)
        rw [ha4Y] at h
        simpa [pow_succ, mul_assoc] using h
      have hn : (a : Y) * a ≠ 1 := by
        intro h
        have haPow : (a : Y) ^ 2 = 1 := by rw [pow_two]; exact h
        have hd := orderOf_dvd_of_pow_eq_one haPow
        rw [ha4Y] at hd
        norm_num at hd
      exact (hz.unique _ (K.mul_mem a.2 a.2) hs).resolve_left hn
    obtain ⟨b, hb, hba, hb1, hbsq⟩ := S16.isQuatSub_exists_inv hqK a.2
    have hb2 : b * b = z := (hz.unique _ (K.mul_mem hb hb) hbsq).resolve_left hb1
    have hab : (a : Y) * b = z * (b * a) := by
      have hbain : b * (a : Y) = (a : Y)⁻¹ * b := (mul_inv_eq_iff_eq_mul).mp hba
      have hza : z * (a : Y)⁻¹ = (a : Y) := by rw [← ha2]; group
      rw [hbain]
      rw [← mul_assoc, hza]
    have hρa := hpair a b a.2 hb ha2 hb2 hab
    exact hker ▸ MonoidHom.mem_ker.mpr hρa
  intro a ha
  have hmem : (⟨a, ha⟩ : K) ∈ (centralizer (E : Set Y)).subgroupOf K := by
    rw [htop]
    trivial
  exact hmem

theorem isPGroup_two_of_generated_conjClass_solvable_threePrime_of_involution_mem
    {Y : Type} [Group Y] [Finite Y] [Group.IsSolvable Y]
    {K : Subgroup Y} (hΩ : HypOmegaGen (CoreAssembly.conjClass K))
    (hO : classicalInvolutionOddCore Y = ⊥) (h3 : ¬ 3 ∣ Nat.card Y)
    (hgen : (⨆ g : Y, conjSub g K) = ⊤)
    {z : Y} (hz : IsUniqueInvolution K z) (hz2 : z ∈ CFSG.pCore 2 Y) : IsPGroup 2 Y := by
  have hstep : ∀ n : ℕ, ∀ (X : Type) [Group X] [Finite X] [Group.IsSolvable X],
      Nat.card X = n → ∀ (J : Subgroup X), HypOmegaGen (CoreAssembly.conjClass J) →
      classicalInvolutionOddCore X = ⊥ → ¬ 3 ∣ Nat.card X →
      (⨆ g : X, conjSub g J) = ⊤ → ∀ u : X, IsUniqueInvolution J u →
      u ∈ CFSG.pCore 2 X → IsPGroup 2 X := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X _ _ _ hn J hΩ hO h3 hgen u hu hu2
      have hJ : J ∈ CoreAssembly.conjClass J := CoreAssembly.mem_conjClass_self J
      have hJ2 := isPGroup_two_of_hypOmegaGen_solvable_threePrime hΩ hO h3 hJ
      have hQne : CFSG.pCore 2 X ≠ ⊥ := by
        intro h
        rw [h, mem_bot] at hu2
        exact hu.ne_one hu2
      obtain ⟨E, hEQ, hmin⟩ := CFSG.RankThreeEvenClassification.Helpers.exists_minimal_nontrivial_normal_le
        (CFSG.pCore 2 X) hQne
      let : E.Normal := hmin.1.1
      let : CFSG.IsMinimalNormal E := ⟨fun L hL hLE => by
        by_cases hLbot : L = ⊥
        · exact Or.inl hLbot
        · exact Or.inr (hmin.eq_of_le ⟨hL, hLbot⟩ hLE)⟩
      have hE2 : IsPGroup 2 E := CFSG.pCore_isPGroup.to_le hEQ
      by_cases huE : u ∈ E
      · have hCE : (⊤ : Subgroup X) ≤ centralizer (E : Set X) := by
          rw [← hgen]
          refine iSup_le fun g => ?_
          have hgu : IsUniqueInvolution (conjSub g J) (g * u * g⁻¹) := hu.conj g
          exact le_centralizer_of_hypOmegaGen_of_mem_minimal_normal_two hΩ h3
            (hΩ.conjInvariant g J hJ) (hJ2.map (MulAut.conj g).toMonoidHom)
            hmin.1.2 hE2 hgu (Subgroup.Normal.conj_mem inferInstance u huE g)
        have huc : ∀ x : X, u * x = x * u := fun x =>
          Subgroup.mem_centralizer_iff.mp (hCE (mem_top x)) u huE
        have hJC : IsSubnormal J (centralizer ({u} : Set X)) :=
          Q3.PhilipHall.QuaternionBridge.CentQ.isSubnormal_centralizer_gen hΩ hJ hu
        have hCtop : centralizer ({u} : Set X) = ⊤ := by
          ext x
          simp only [mem_centralizer_singleton_iff, mem_top, iff_true]
          exact (huc x).symm
        have hJN : J.IsSubnormal := by
          rw [hCtop] at hJC
          exact CFSG.Open.IsSubnormal.top_iff.mp hJC
        have hJQ := Q3.Twin.le_pCore_of_isSubnormal hJN hJ2
        have hXQ : (⊤ : Subgroup X) ≤ CFSG.pCore 2 X := by
          rw [← hgen]
          refine iSup_le fun g x hx => ?_
          rw [mem_conjSub_iff] at hx
          have h := Subgroup.Normal.conj_mem (CFSG.pCore_normal (p := 2) (G := X))
            _ (hJQ hx) g
          simpa [mul_assoc] using h
        exact (CFSG.pCore_isPGroup.to_le hXQ).of_equiv Subgroup.topEquiv
      · have hmeet : ∀ L ∈ CoreAssembly.conjClass J, L ⊓ E = ⊥ := by
          rintro L ⟨g, rfl⟩
          by_contra hne
          have hgu : IsUniqueInvolution (conjSub g J) (g * u * g⁻¹) := hu.conj g
          have hmem : g * u * g⁻¹ ∈ conjSub g J ⊓ E := mem_of_isUniqueInvolution_of_isPGroup hgu
            (inf_le_left : conjSub g J ⊓ E ≤ conjSub g J)
            (hJ2.map (MulAut.conj g).toMonoidHom |>.to_le inf_le_left)
            (by have h := (Subgroup.nontrivial_iff_ne_bot _).mpr hne; exact Finite.one_lt_card)
          have h := Subgroup.Normal.conj_mem inferInstance _ hmem.2 g⁻¹
          exact huE (by simpa [mul_assoc] using h)
        have hEC : E ≤ center X := by
          have hCE : (⊤ : Subgroup X) ≤ centralizer (E : Set X) := by
            rw [← hgen]
            refine iSup_le fun g => ?_
            have hL : conjSub g J ∈ CoreAssembly.conjClass J := ⟨g, rfl⟩
            have hc := Q3.comm613Gen_normal hΩ
              (mem_RSet_of_isSylow2In hL ⟨le_rfl, hJ2.map (MulAut.conj g).toMonoidHom,
                fun R hR _ hLR => le_antisymm hR hLR⟩) inferInstance (hmeet _ hL)
            have hOE : oddCoreOf E = ⊥ := AscE186.oddCoreOf_eq_bot_of_isPGroup hE2
            rw [hOE, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
            exact hc
          intro e he
          exact mem_center_iff.mpr fun x => (Subgroup.mem_centralizer_iff.mp (hCE (mem_top x)) e he).symm
        let π := QuotientGroup.mk' E
        let J' := J.map π
        have hΩ' : HypOmegaGen (CoreAssembly.conjClass J') := by
          have hm := Q3.PhilipHall.QuaternionBridge.CentQ.quotient_hypOmegaGen hΩ E hEC
            (fun L hL => by rw [inf_comm, hmeet L hL, Subgroup.card_bot]; exact odd_one)
          have hf : Set.image (fun L : Subgroup X => L.map π) (CoreAssembly.conjClass J) =
              CoreAssembly.conjClass J' := by
            ext L
            constructor
            · rintro ⟨M, ⟨g, rfl⟩, rfl⟩
              exact ⟨π g, (AscQuot.map_conjSub π g J).symm⟩
            · rintro ⟨g', rfl⟩
              obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective E g'
              exact ⟨conjSub g J, ⟨g, rfl⟩, AscQuot.map_conjSub π g J⟩
          exact hf ▸ hm
        have hO' : classicalInvolutionOddCore (X ⧸ E) = ⊥ := by
          rw [QuaternionStructure.classicalInvolutionOddCore_eq_oddCore] at hO ⊢
          exact CFSG.QuasiDihedralFusion.oddCore_quotient_eq_bot_of_le_center hO E hEC hE2
        have h3' : ¬ 3 ∣ Nat.card (X ⧸ E) :=
          fun hd => h3 (hd.trans (Subgroup.card_quotient_dvd_card E))
        have hgen' : (⨆ g : X ⧸ E, conjSub g J') = ⊤ := by
          have hm := congrArg (Subgroup.map π) hgen
          rw [Subgroup.map_iSup, Subgroup.map_top, MonoidHom.range_eq_top.mpr
            (QuotientGroup.mk'_surjective E)] at hm
          apply top_le_iff.mp
          rw [← hm]
          refine iSup_le fun g => ?_
          rw [AscQuot.map_conjSub]
          exact le_iSup (fun g' : X ⧸ E => conjSub g' J') (π g)
        have hv : IsUniqueInvolution J' (π u) := AscQuot.isUniqueInvolution_map_mk (hmeet J hJ) hu
        have hv2 : π u ∈ CFSG.pCore 2 (X ⧸ E) :=
          (CFSG.LieType.BorelTits.map_pCore_le 2 π (QuotientGroup.mk'_surjective E))
            ⟨u, hu2, rfl⟩
        have hlt : Nat.card (X ⧸ E) < n := by
          have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup E
          have hEcard : 1 < Nat.card E := by
            have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hmin.1.2
            exact Finite.one_lt_card
          have hpos : 0 < Nat.card (X ⧸ E) := Nat.card_pos
          rw [← hn, hcard]
          nlinarith
        have hX' : IsPGroup 2 (X ⧸ E) := ih _ hlt (X ⧸ E) rfl J' hΩ' hO' h3' hgen' (π u) hv hv2
        exact CFSG.BenderSuzuki.External.hkt_isPGroup_of_normal_quotient E hE2 hX'
  exact hstep _ Y rfl K hΩ hO h3 hgen z hz hz2

end CFSG.LocalAnalysis.UniquenessCase.UC22
