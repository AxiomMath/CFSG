module

public import CFSG.RankThree.PartTwo.KFacts.K71Coprime
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.RankThree.PartTwo.Sec10.Item102Proof

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item1014Proof

section General

variable {G : Type} [Group G] [Finite G]

theorem twentyseven_dvd_card {Q : Type*} [Group Q]
    (e : Q ≃* GorensteinWalter.PSL2 (GaloisField 3 3)) : 27 ∣ Nat.card Q := by
  rw [Nat.card_congr e.toEquiv]
  have h2 := Subgroup.card_dvd_of_le (le_top : GorensteinWalter.psl2UpperUnipotentSubgroup
    (GaloisField 3 3) ≤ ⊤)
  rwa [GorensteinWalter.psl2UpperUnipotentSubgroup_card, GaloisField.card 3 3 (by norm_num),
    Subgroup.card_top] at h2

theorem isElemAbelian_of_isPGroup_of_le {Y S : Subgroup G}
    (e : Y ⧸ aschbacherSolvableCore 3 Y ≃* GorensteinWalter.PSL2 (GaloisField 3 3))
    (hS : IsPGroup 3 S) (hSY : S ≤ Y) :
    CFSG.Assembly.IsElemAbelian 3 S ∧ Nat.card S ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S' := S.subgroupOf Y with hS'
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  have hS'3 : IsPGroup 3 S' := hS.comap_subtype
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  obtain ⟨hSe, hScard⟩ := KFacts.isElemAbelian_of_isPGroup_three_of_mulEquiv hK e (hS'3.map π)
  rw [hK] at hScard
  have hker : ∀ x ∈ S', π x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨k, hk⟩ := hS'3 ⟨x, hx⟩
    exact Sec11.eq_one_of_mem_theta_of_pow_eq_one ((QuotientGroup.eq_one_iff x).mp hx1) (k := k)
      (by simpa using congrArg Subtype.val hk)
  have hinj : Function.Injective (π.comp S'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    exact Subtype.ext (hker x x.2 hx)
  have hcardS : Nat.card S' = Nat.card (S'.map π) := by
    rw [show S'.map π = (π.comp S'.subtype).range by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hcardSY : Nat.card S = Nat.card S' := by
    rw [hS', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv]
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  ·
    have hxS : (⟨x, hSY x.2⟩ : Y) ∈ S' := Subgroup.mem_subgroupOf.mpr x.2
    have hyS : (⟨y, hSY y.2⟩ : Y) ∈ S' := Subgroup.mem_subgroupOf.mpr y.2
    have h1 : π ⟨x, hSY x.2⟩ * π ⟨y, hSY y.2⟩ = π ⟨y, hSY y.2⟩ * π ⟨x, hSY x.2⟩ :=
      congrArg Subtype.val (hSe.1.is_comm.comm ⟨_, _, hxS, rfl⟩ ⟨_, _, hyS, rfl⟩)
    have h2 : (⟨x, hSY x.2⟩ : Y) * ⟨y, hSY y.2⟩ * (⟨y, hSY y.2⟩ * ⟨x, hSY x.2⟩)⁻¹ ∈ S' :=
      S'.mul_mem (S'.mul_mem hxS hyS) (S'.inv_mem (S'.mul_mem hyS hxS))
    have h3 := hker _ h2 (by rw [map_mul, map_inv, map_mul, map_mul, h1, mul_inv_cancel])
    have h4 : (⟨x, hSY x.2⟩ : Y) * ⟨y, hSY y.2⟩ = ⟨y, hSY y.2⟩ * ⟨x, hSY x.2⟩ :=
      mul_inv_eq_one.mp h3
    have h5 : (x : G) * y = y * x := by simpa using congrArg Subtype.val h4
    exact h5
  ·
    have hxS : (⟨x, hSY hx⟩ : Y) ∈ S' := Subgroup.mem_subgroupOf.mpr hx
    have h1 : π ⟨x, hSY hx⟩ ^ 3 = 1 := hSe.2 _ ⟨_, hxS, rfl⟩
    have h2 := hker _ (S'.pow_mem hxS 3) (by rw [map_pow, h1])
    exact congrArg Subtype.val h2
  · rw [hcardSY, hcardS]
    exact hScard

theorem exists_isElemAbelian_le_of_dvd {Y Q : Subgroup G}
    (e : Y ⧸ aschbacherSolvableCore 3 Y ≃* GorensteinWalter.PSL2 (GaloisField 3 3))
    (hQY : Q ≤ Y) (hQ : 27 ∣ Nat.card Q) :
    ∃ S : Subgroup G, S ≤ Q ∧ CFSG.Assembly.IsElemAbelian 3 S ∧ 27 ≤ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 Q
  refine ⟨S, hS.le, (isElemAbelian_of_isPGroup_of_le e hS.isPGroup (hS.le.trans hQY)).1, ?_⟩
  rw [hS.card_eq]
  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have h3 : 3 ≤ (Nat.card Q).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hQ0).mp (by simpa using hQ)
  calc 27 = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ (Nat.card Q).factorization 3 := Nat.pow_le_pow_right (by norm_num) h3

theorem exists_lift_of_fixed {L P : Subgroup G} (hP : IsPGroup 3 P)
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (yb : L ⧸ aschbacherSolvableCore 3 L)
    (hfix : ∀ (p : G) (hp : p ∈ P),
      Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨p, hPN hp⟩) yb = yb) :
    ∃ y : L, (y : L ⧸ aschbacherSolvableCore 3 L) = yb ∧
      (y : G) ∈ Subgroup.centralizer (P : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  set φ : P →* MulAut L := (Sec4.compAction L).comp (Subgroup.inclusion hPN) with hφ
  have hφN : ∀ g, ∀ n ∈ aschbacherSolvableCore 3 L, φ g n ∈ aschbacherSolvableCore 3 L := by
    intro g n hn
    have h := Sec4.map_aschbacherSolvableCore (φ g)
    rw [← h]
    exact ⟨n, hn, rfl⟩
  have hy : ∀ g, ((φ g y : L) : L ⧸ aschbacherSolvableCore 3 L) =
      (y : L ⧸ aschbacherSolvableCore 3 L) := by
    rintro ⟨g, hg⟩
    have := hfix g hg
    rw [Sec4.thetaQuotMulAut_mk] at this
    exact this
  obtain ⟨y', hy'eq, hy'fix⟩ := KFacts.exists_fixed_of_coprime hP φ (aschbacherSolvableCore 3 L)
    (KFacts.not_three_dvd_card_aschbacherSolvableCore L) hφN y hy
  refine ⟨y', hy'eq, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
  have h1 := congrArg Subtype.val (hy'fix ⟨p, hp⟩)
  change p * (y' : G) * p⁻¹ = y' at h1
  calc p * (y' : G) = p * (y' : G) * p⁻¹ * p := by group
    _ = y' * p := by rw [h1]

theorem card_dvd_card_inf_centralizer {L P : Subgroup G} (hP : IsPGroup 3 P)
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (U : Subgroup (L ⧸ aschbacherSolvableCore 3 L))
    (hU : ∀ u ∈ U, ∀ (p : G) (hp : p ∈ P),
      Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨p, hPN hp⟩) u = u) :
    Nat.card U ∣ Nat.card (L ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
  set Q := L ⊓ Subgroup.centralizer (P : Set G) with hQ
  have hle : U ≤ (Q.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
    intro u hu
    obtain ⟨y, hy, hyc⟩ := exists_lift_of_fixed hP hPN u (hU u hu)
    exact ⟨y, Subgroup.mem_subgroupOf.mpr ⟨y.2, hyc⟩, hy⟩
  refine (Subgroup.card_dvd_of_le hle).trans ((Subgroup.card_map_dvd _ _).trans ?_)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ≤ L)).toEquiv]

theorem conj_injective_of_center_eq_bot {Q : Type*} [Group Q] (hZ : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  intro x y hxy
  have hz : x⁻¹ * y ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := DFunLike.congr_fun hxy g
    simp only [MulAut.conj_apply] at h
    calc g * (x⁻¹ * y) = x⁻¹ * (x * g * x⁻¹) * y := by group
      _ = x⁻¹ * (y * g * y⁻¹) * y := by rw [h]
      _ = x⁻¹ * y * g := by group
  rw [hZ, Subgroup.mem_bot] at hz
  exact inv_mul_eq_one.mp hz

theorem center_eq_bot_of_mulEquiv {Q : Type*} [Group Q]
    (e : Q ≃* GorensteinWalter.PSL2 (GaloisField 3 3)) : Subgroup.center Q = ⊥ :=
  KFacts.center_eq_bot_of_mulEquiv_of_center_eq_bot e (GorensteinWalter.psl2_center_eq_bot _)

theorem exists_eqLocus_mulEquiv_of_mulEquiv_psl2 {Q : Type*} [Group Q] {K : Type} [Field K]
    [Finite K] (e : Q ≃* GorensteinWalter.PSL2 K) {α : MulAut Q} (hα3 : α ^ 3 = 1)
    (hout : ¬ KFacts.IsInnerAut α) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      Nonempty (α.toMonoidHom.eqLocus (MonoidHom.id Q) ≃*
        GorensteinWalter.PSL2 (GH74.GLS.IVK.fixedField σ)) := by
  set β := MulAut.congr e α with hβ
  obtain ⟨σ, hσ3, ⟨f⟩⟩ := KFacts.exists_eqLocus_mulEquiv_psl2 (α := β)
    (by rw [hβ, ← map_pow, hα3, map_one]) (by rwa [hβ, KFacts.isInnerAut_congr])
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id Q)).map e.toMonoidHom =
      β.toMonoidHom.eqLocus (MonoidHom.id (GorensteinWalter.PSL2 K)) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : α y = y := hy
      show e (α (e.symm (e y))) = e y
      rw [MulEquiv.symm_apply_apply, hy']
    · intro hz
      have hz' : e (α (e.symm z)) = z := hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      show α (e.symm z) = e.symm z
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact hz'
  exact ⟨σ, hσ3, ⟨((e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)).trans f⟩⟩

theorem exists_two_subgroup_invariant {Q : Type*} [Group Q]
    (e : Q ≃* GorensteinWalter.PSL2 (GaloisField 3 3)) {P : Subgroup (MulAut Q)}
    (hP3 : IsPGroup 3 P) (hPc : ∀ τ ∈ P, ∀ τ' ∈ P, τ * τ' = τ' * τ)
    (hPe : ∀ τ ∈ P, τ ^ 3 = 1) {σ : MulAut Q} (hσP : σ ∈ P) (hσ : ¬ KFacts.IsInnerAut σ) :
    ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ τ ∈ P, ∀ v ∈ V, τ v ∈ V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ3 := hPe σ hσP
  have hcinj := conj_injective_of_center_eq_bot (center_eq_bot_of_mulEquiv e)
  obtain ⟨s, hs3, ⟨ι⟩⟩ := exists_eqLocus_mulEquiv_of_mulEquiv_psl2 e hσ3 hσ
  set C := σ.toMonoidHom.eqLocus (MonoidHom.id Q) with hC
  set F := GH74.GLS.IVK.fixedField s with hFdef
  have hF3 : Nat.card F = 3 :=
    KFacts.card_fixedField_of_orderOf_eq_three hs3 (q₀ := 3) (GaloisField.card 3 3 (by norm_num))
  set T := P.comap (MulAut.conj : Q →* MulAut Q) with hT
  have hT3 : IsPGroup 3 T := hP3.comap_of_injective _ hcinj
  have hTC : T ≤ C := by
    intro p hp
    have h1 : σ * MulAut.conj p = MulAut.conj p * σ := hPc σ hσP _ hp
    have h2 : MulAut.conj (σ p) = σ * MulAut.conj p * σ⁻¹ := by
      ext x
      simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_def]
    have h3 : MulAut.conj (σ p) = MulAut.conj p := by rw [h2, h1, mul_inv_cancel_right]
    exact hcinj h3
  set T₁ := (T.subgroupOf C).map ι.toMonoidHom with hT₁
  have hT₁3 : IsPGroup 3 T₁ := hT3.comap_subtype.map _
  have hT₁card : Nat.card T₁ ≤ 3 := by
    have := (KFacts.isElemAbelian_of_isPGroup_three_psl2 (K := F) (n := 1)
      (by rw [hF3, pow_one]) hT₁3).2
    rwa [hF3] at this
  obtain ⟨T₀, hT₁T₀, hT₀⟩ : ∃ T₀ : Subgroup (GorensteinWalter.PSL2 F), T₁ ≤ T₀ ∧
      Nat.card T₀ = 3 := by
    obtain ⟨k, hk⟩ := hT₁3.exists_card_eq
    rcases k with _ | _ | k
    · refine ⟨GorensteinWalter.psl2UpperUnipotentSubgroup F, ?_, by
        rw [GorensteinWalter.psl2UpperUnipotentSubgroup_card, hF3]⟩
      rw [pow_zero] at hk
      rw [Subgroup.card_eq_one.mp hk]
      exact bot_le
    · exact ⟨T₁, le_rfl, by rw [hk, zero_add, pow_one]⟩
    · exfalso
      rw [hk] at hT₁card
      have : 3 ^ 2 ≤ 3 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  obtain ⟨V₀, hV₀1, hV₀2, hT₀V₀⟩ :=
    KFacts.exists_two_subgroup_of_card_eq_three_psl2 (K := F) (by rw [hF3]) hT₀
  set V := (V₀.map ι.symm.toMonoidHom).map C.subtype with hV
  refine ⟨V, ?_, (hV₀2.map _).map _, ?_⟩
  · rw [Ne, hV, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ ι.symm.injective]
    exact hV₀1
  · intro τ hτ v hv
    obtain ⟨i, p, hp⟩ := KFacts.exists_pow_mul_isInnerAut_of_mulEquiv_psl2 e hP3 hσP hτ hσ3 hσ
      (hPe τ hτ)
    have hpT : p ∈ T := by
      show MulAut.conj p ∈ P
      rw [hp]
      exact P.mul_mem (P.pow_mem hσP i) hτ
    have hpC : p ∈ C := hTC hpT
    have hτeq : τ = (σ ^ i)⁻¹ * MulAut.conj p := by rw [hp, inv_mul_cancel_left]
    obtain ⟨_, ⟨v₀, hv₀, rfl⟩, rfl⟩ := hv
    have hιp : ι ⟨p, hpC⟩ ∈ T₀ := hT₁T₀ ⟨⟨p, hpC⟩, Subgroup.mem_subgroupOf.mpr hpT, rfl⟩
    have h1 : ι ⟨p, hpC⟩ * v₀ * (ι ⟨p, hpC⟩)⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.mp (hT₀V₀ hιp) v₀).mp hv₀
    set w : C := ι.symm (ι ⟨p, hpC⟩ * v₀ * (ι ⟨p, hpC⟩)⁻¹) with hw
    have hw' : (w : Q) = p * (ι.symm v₀ : Q) * p⁻¹ := by
      rw [hw, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      rfl
    have hwfix : ∀ j : ℕ, (σ ^ j) (w : Q) = w := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [pow_succ, MulAut.mul_apply]
        have : σ (w : Q) = w := w.2
        rw [this, ih]
    have hwfix' : (σ ^ i)⁻¹ (w : Q) = w := by
      rw [MulAut.inv_def]
      apply (σ ^ i).injective
      rw [MulEquiv.apply_symm_apply, hwfix i]
    refine ⟨w, ⟨_, h1, rfl⟩, ?_⟩
    rw [hτeq, MulAut.mul_apply, MulAut.conj_apply]
    change (w : Q) = (σ ^ i)⁻¹ (p * (ι.symm v₀ : Q) * p⁻¹)
    rw [← hw', hwfix']

theorem pow_three_of_mem_autThetaQuot {E L : Subgroup G} (hE : ∀ x ∈ E, x ^ 3 = 1)
    {τ : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hτ : τ ∈ Sec4.autThetaQuot E L) :
    τ ^ 3 = 1 := by
  obtain ⟨z, hzN, hzE, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
  have h1 : (⟨z, hzN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
    Subtype.ext (by simpa using hE z hzE)
  rw [← map_pow, ← map_pow, h1, map_one, map_one]

theorem commute_of_mem_autThetaQuot {E L : Subgroup G} (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    {τ τ' : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hτ : τ ∈ Sec4.autThetaQuot E L)
    (hτ' : τ' ∈ Sec4.autThetaQuot E L) : τ * τ' = τ' * τ := by
  obtain ⟨z, hzN, hzE, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
  obtain ⟨z', hz'N, hz'E, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ'
  set φ := (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hφ
  have h1 : (⟨z, hzN⟩ : Subgroup.normalizer (L : Set G)) * ⟨z', hz'N⟩ =
      ⟨z', hz'N⟩ * ⟨z, hzN⟩ := Subtype.ext (hE z hzE z' hz'E)
  change φ ⟨z, hzN⟩ * φ ⟨z', hz'N⟩ = φ ⟨z', hz'N⟩ * φ ⟨z, hzN⟩
  rw [← map_mul, h1, map_mul]

theorem isPGroup_autThetaQuot {E L : Subgroup G} (hE : ∀ x ∈ E, x ^ 3 = 1) :
    IsPGroup 3 (Sec4.autThetaQuot E L) := fun τ =>
  ⟨1, Subtype.ext (by simpa using pow_three_of_mem_autThetaQuot hE τ.2)⟩

theorem ne_one_of_inducesOuterTheta {y : G} {L : Subgroup G} (hy : Sec4.InducesOuterTheta y L) :
    y ≠ 1 := by
  rintro rfl
  obtain ⟨hN, hout⟩ := hy
  apply hout
  have : (⟨1, hN⟩ : Subgroup.normalizer (L : Set G)) = 1 := rfl
  rw [this, map_one, map_one]
  exact ⟨1, map_one _⟩

theorem mem_thetaQuotCentralizer_of_le_centralizer {d : G} {X : Subgroup G}
    (hXd : X ≤ Subgroup.centralizer ({d} : Set G)) : d ∈ Sec4.thetaQuotCentralizer X := by
  have hcomm : ∀ l ∈ X, d * l * d⁻¹ = l := fun l hl => by
    rw [← (Subgroup.mem_centralizer_singleton_iff.mp (hXd hl)), mul_inv_cancel_right]
  have hdN : d ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hXd hl))
  refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hdN, fun l hl => ?_⟩
  rw [hcomm l hl, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem eq_one_of_mem_thetaQuotCentralizer {X : Subgroup G}
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥) {u : G} (huX : u ∈ X)
    (huC : u ∈ Sec4.thetaQuotCentralizer X) (hu3 : u ^ 3 = 1) : u = 1 := by
  have hθ := Sec11.mem_theta_of_mem_thetaQuotCentralizer hZ huX huC
  have := Sec11.eq_one_of_mem_theta_of_pow_eq_one hθ (k := 1) (Subtype.ext (by simpa using hu3))
  exact congrArg Subtype.val this

theorem not_mem_of_le_centralizer {X : Subgroup G}
    (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) = ⊥) {d : G}
    (hXd : X ≤ Subgroup.centralizer ({d} : Set G)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) : d ∉ X :=
  fun hdX => hd1 (eq_one_of_mem_thetaQuotCentralizer hZ hdX
    (mem_thetaQuotCentralizer_of_le_centralizer hXd) hd3)

omit [Finite G] in
theorem map_conj_omega_le {R R' : Subgroup G} {k : G} (hk : ∀ r ∈ R, k⁻¹ * r * k ∈ R') :
    (Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}).map (MulAut.conj k⁻¹).toMonoidHom ≤
      Subgroup.closure {y | y ∈ R' ∧ y ^ 3 = 1} := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨y, ⟨hyR, hy3⟩, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · change k⁻¹ * y * k⁻¹⁻¹ ∈ R'
    rw [inv_inv]
    exact hk y hyR
  · change (k⁻¹ * y * k⁻¹⁻¹) ^ 3 = 1
    rw [conj_pow, hy3]
    group

omit [Finite G] in
theorem map_conj_commutator_omega_le {R R' : Subgroup G} {k : G}
    (hk : ∀ r ∈ R, k⁻¹ * r * k ∈ R') :
    (⁅⁅Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}, Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}⁆,
      Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}⁆).map (MulAut.conj k⁻¹).toMonoidHom ≤
      ⁅⁅Subgroup.closure {y | y ∈ R' ∧ y ^ 3 = 1}, Subgroup.closure {y | y ∈ R' ∧ y ^ 3 = 1}⁆,
        Subgroup.closure {y | y ∈ R' ∧ y ^ 3 = 1}⁆ := by
  have h := map_conj_omega_le hk
  rw [Subgroup.map_commutator, Subgroup.map_commutator]
  exact Subgroup.commutator_mono (Subgroup.commutator_mono h h) h

theorem invTwoBarNontrivial_of_inducesOuterTheta {A X : Subgroup G}
    (hAe : ∀ x ∈ A, x ^ 3 = 1) (hAc : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x)
    (eX : X ⧸ aschbacherSolvableCore 3 X ≃* GorensteinWalter.PSL2 (GaloisField 3 3)) {y : G}
    (hyA : y ∈ A) (hy : Sec4.InducesOuterTheta y X) : Sec8.InvTwoBarNontrivial A X := by
  obtain ⟨hyN, hyout⟩ := hy
  obtain ⟨V, hV1, hV2, hV⟩ := exists_two_subgroup_invariant eX (isPGroup_autThetaQuot hAe)
    (fun τ hτ τ' hτ' => commute_of_mem_autThetaQuot hAc hτ hτ')
    (fun τ hτ => pow_three_of_mem_autThetaQuot hAe hτ)
    (σ := Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨y, hyN⟩))
    (Sec4.mem_autThetaQuot_iff.mpr ⟨y, hyN, hyA, rfl⟩) hyout
  exact ⟨V, hV1, hV2, hV⟩

end General

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem le_normalizer_of_mem_thetaComponentsAt (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R)
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 d) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h.pow_three u.2)⟩
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun z hz =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm hz hdA)
  exact Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 h.toTheoremFourHyp
    (h.pow_three hdA) hd1 hA3 hAd X hX

theorem inf_thetaQuotCentralizer_eq (h : Sec10Std G A c L a R) {d : G} (hdA : d ∈ A)
    (hdo : orderOf d = 3) {X : Subgroup G} (hXd : X ≤ Subgroup.centralizer ({d} : Set G))
    (hAN : A ≤ Subgroup.normalizer (X : Set G))
    (eX : X ⧸ aschbacherSolvableCore 3 X ≃* GorensteinWalter.PSL2 (GaloisField 3 3)) :
    A ⊓ Sec4.thetaQuotCentralizer X = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd3 : d ^ 3 = 1 := h.pow_three hdA
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    norm_num at hdo
  have hZ := center_eq_bot_of_mulEquiv eX
  have hdC := mem_thetaQuotCentralizer_of_le_centralizer hXd
  have hdX := not_mem_of_le_centralizer hZ hXd hd3 hd1
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hdA, hdC⟩))
  rintro e ⟨heA, heC⟩
  by_contra hed
  have heN : e ∈ Subgroup.normalizer (X : Set G) := hAN heA
  have he3 : e ^ 3 = 1 := h.pow_three heA
  have he1 : e ≠ 1 := fun h1 => hed (h1 ▸ Subgroup.one_mem _)
  have heo : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hP3 : IsPGroup 3 (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, heo, pow_one])
  have hPN : Subgroup.zpowers e ≤ Subgroup.normalizer (X : Set G) := Subgroup.zpowers_le.mpr heN
  have hdvd := card_dvd_card_inf_centralizer hP3 hPN ⊤ (fun u _ p hp => by
    have hpC : p ∈ Sec4.thetaQuotCentralizer X := (Subgroup.zpowers_le.mpr heC) hp
    have h1 : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨p, hPN hp⟩) = 1 :=
      (mem_thetaQuotCentralizer_iff_barAct (hPN hp)).mp hpC
    rw [h1, MulAut.one_apply])
  rw [Subgroup.card_top] at hdvd
  obtain ⟨S, hSQ, hSe, hS27⟩ :=
    exists_isElemAbelian_le_of_dvd eX inf_le_left ((twentyseven_dvd_card eX).trans hdvd)
  have hSX : S ≤ X := hSQ.trans inf_le_left
  have hSe' : ∀ s ∈ S, s * e = e * s := fun s hs =>
    (Subgroup.mem_centralizer_iff.mp (hSQ hs).2 e (Subgroup.mem_zpowers e)).symm
  have hSd : ∀ s ∈ S, s * d = d * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp (hXd (hSX hs))
  obtain ⟨x, hxS, hx1⟩ : ∃ x ∈ S, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have hS1 : S = ⊥ := (Subgroup.eq_bot_iff_forall S).mpr hall
    rw [hS1, Subgroup.card_bot] at hS27
    norm_num at hS27
  have hx3 : x ^ 3 = 1 := hSe.2 x hxS
  have hxX : x ∈ X := hSX hxS
  set B := Subgroup.zpowers d ⊔ Subgroup.zpowers e with hB
  have hde : d * e = e * d := h.comm hdA heA
  have hBC : B ≤ Sec4.thetaQuotCentralizer X :=
    sup_le (Subgroup.zpowers_le.mpr hdC) (Subgroup.zpowers_le.mpr heC)
  have hBcard : Nat.card B = 9 := by
    have hN : Subgroup.zpowers e ≤
        Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left hde k).eq)
    rw [hB, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
      (disjoint_zpowers_of_pow_three he3 hed), Nat.card_zpowers, Nat.card_zpowers, hdo, heo]
  have hxB : x ∉ B := fun hxB => hx1 (eq_one_of_mem_thetaQuotCentralizer hZ hxX (hBC hxB) hx3)
  set E := B ⊔ Subgroup.zpowers x with hE
  have hBx : ∀ b ∈ B, b * x = x * b := by
    have hle : B ≤ Subgroup.centralizer ({x} : Set G) := by
      apply sup_le
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (hSd x hxS).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (hSe' x hxS).symm
    exact fun b hb => Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
  have hEcard : Nat.card E = 27 := by
    have hN : Subgroup.zpowers x ≤ Subgroup.normalizer ((B : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hBx)
    rw [hE, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN
      (disjoint_zpowers_of_pow_three hx3 hxB), hBcard, Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    Sec15.isElemAbelian_sup_zpowers (isElemAbelian_zpowers_of_pow_three hd3) he3 fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left hde k).eq
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := Sec15.isElemAbelian_sup_zpowers hBe hx3 hBx
  set xb : X ⧸ aschbacherSolvableCore 3 X :=
    QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨x, hxX⟩ with hxb
  have hxb3 : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    have : (⟨x, hxX⟩ : X) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hxb1 : xb ≠ 1 := by
    intro h1
    apply hx1
    have hθ : (⟨x, hxX⟩ : X) ∈ aschbacherSolvableCore 3 X := (QuotientGroup.eq_one_iff _).mp h1
    have := Sec11.eq_one_of_mem_theta_of_pow_eq_one hθ (k := 1)
      (Subtype.ext (by simpa using hx3))
    exact congrArg Subtype.val this
  obtain ⟨Vb, hVb1, hVb2, hVbN⟩ := KFacts.exists_two_subgroup_of_card_eq_three eX
    (P := Subgroup.zpowers xb) (by rw [Nat.card_zpowers, orderOf_eq_prime hxb3 hxb1])
  have hEY : E ≤ Subgroup.normalizer ((thetaPreimage X Vb : Subgroup G) : Set G) := by
    refine sup_le (fun b hb => mem_normalizer_thetaPreimage_of_mem_thetaQuotCentralizer
      (hBC hb)) ?_
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_thetaPreimage_of_mem hxX (hVbN (Subgroup.mem_zpowers xb))
  have hE3 : IsPGroup 3 E := fun u => ⟨1, Subtype.ext (by simpa using hEe.2 u u.2)⟩
  obtain ⟨T, -, hT1, hT2, hET⟩ := exists_pGroup_le_normalizer (p := 3) (q := 2) hE3
    (not_three_dvd_card_thetaPreimage hVb2) (two_dvd_card_thetaPreimage hVb2 hVb1) hEY
  have hEmem : E ∈ partTwoE G := ⟨hEe, hEcard, T, hT1, hT2, hET⟩
  rw [h.partTwoE_eq h.card_eq] at hEmem
  have hSee : CFSG.Assembly.IsElemAbelian 3 (S ⊔ Subgroup.zpowers e) :=
    Sec15.isElemAbelian_sup_zpowers hSe he3 hSe'
  have hF : CFSG.Assembly.IsElemAbelian 3 (S ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers d) :=
    Sec15.isElemAbelian_sup_zpowers hSee hd3 fun y hy => by
      have hle : S ⊔ Subgroup.zpowers e ≤ Subgroup.centralizer ({d} : Set G) := by
        refine sup_le (hSX.trans hXd) ?_
        rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact hde.symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hEF : E ≤ S ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
    refine sup_le (sup_le le_sup_right (le_sup_right.trans le_sup_left)) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hxS)
  have hFE := hEmem.2.1 _ hF hEF
  have hSE : S ≤ E := by
    rw [← hFE]
    exact le_sup_left.trans le_sup_left
  have hSE' : S = E := Subgroup.eq_of_le_of_card_ge hSE (by rw [hEcard]; exact hS27)
  have hdE : d ∈ E := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers d))
  rw [← hSE'] at hdE
  exact hdX (hSX hdE)

theorem exists_inducesOuterTheta (h : Sec10Std G A c L a R) {d : G} (hdA : d ∈ A)
    {X : Subgroup G} (hAN : A ≤ Subgroup.normalizer (X : Set G)) (hdX : d ∉ X)
    (eX : X ⧸ aschbacherSolvableCore 3 X ≃* GorensteinWalter.PSL2 (GaloisField 3 3)) :
    ∃ y ∈ A, Sec4.InducesOuterTheta y X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hall
  push Not at hall
  have hA3 : IsPGroup 3 A := fun u => ⟨1, Subtype.ext (by simpa using h.pow_three u.2)⟩
  set P := Sec4.autThetaQuot A X with hP
  have hinner : ∀ τ ∈ P, KFacts.IsInnerAut τ := by
    intro τ hτ
    obtain ⟨z, hzN, hzA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    by_contra hz
    exact hall z hzA ⟨hzN, hz⟩
  have hcinj := conj_injective_of_center_eq_bot (center_eq_bot_of_mulEquiv eX)
  set T := P.comap (MulAut.conj : X ⧸ aschbacherSolvableCore 3 X →* MulAut _) with hT
  have hT3 : IsPGroup 3 T :=
    (isPGroup_autThetaQuot fun x hx => h.pow_three hx).comap_of_injective _ hcinj
  obtain ⟨U, hTU⟩ := hT3.exists_le_sylow
  have hK : Nat.card (GaloisField 3 3) = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  have hUab := (KFacts.isElemAbelian_of_isPGroup_three_of_mulEquiv hK eX U.isPGroup').1
  have h27U : 27 ∣ Nat.card (U : Subgroup (X ⧸ aschbacherSolvableCore 3 X)) := by
    rw [Sylow.card_eq_multiplicity]
    have h0 : Nat.card (X ⧸ aschbacherSolvableCore 3 X) ≠ 0 := Nat.card_pos.ne'
    have h3 : 3 ≤ (Nat.card (X ⧸ aschbacherSolvableCore 3 X)).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three h0).mp
        (by simpa using twentyseven_dvd_card eX)
    exact (pow_dvd_pow 3 h3 : 3 ^ 3 ∣ _)
  have hUfix : ∀ u ∈ (U : Subgroup (X ⧸ aschbacherSolvableCore 3 X)), ∀ (p : G) (hp : p ∈ A),
      Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨p, hAN hp⟩) u = u := by
    intro u hu p hp
    have hτ : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨p, hAN hp⟩) ∈ P :=
      Sec4.mem_autThetaQuot_iff.mpr ⟨p, hAN hp, hp, rfl⟩
    obtain ⟨q, hq⟩ := hinner _ hτ
    have hqT : q ∈ T := by
      show MulAut.conj q ∈ P
      rw [hq]
      exact hτ
    have hqu : q * u = u * q := congrArg Subtype.val (hUab.1.is_comm.comm ⟨q, hTU hqT⟩ ⟨u, hu⟩)
    rw [← hq, MulAut.conj_apply, hqu, mul_inv_cancel_right]
  obtain ⟨S, hSQ, hSe, hS27⟩ := exists_isElemAbelian_le_of_dvd eX inf_le_left
    (h27U.trans (card_dvd_card_inf_centralizer hA3 hAN _ hUfix))
  have hSA : S ≤ A := fun s hs => Sec15.mem_of_mem_partTwoF h.mem_partTwoF (hSe.2 s hs)
    fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hSQ hs).2 z hz)
  have hSAeq : S = A := Subgroup.eq_of_le_of_card_ge hSA (by rw [h.card_eq]; exact hS27)
  have hdS : d ∈ S := by
    rw [hSAeq]
    exact hdA
  exact hdX (hSQ hdS).1

theorem sec10Std_of_mem_thetaComponentsAt (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 d)
    (eX : X ⧸ aschbacherSolvableCore 3 X ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 3 3)) :
    ∃ (y : G) (R' : Subgroup G), Sec10Std G A d X y R' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set eX' := eX.trans (Sec4.projSLEquivPSL _) with heX'
  have hdA := h.d_mem_A hdL
  have hdo : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hdo
    norm_num at hdo
  have hXd := Sec6.le_centralizer_of_mem_thetaComponentsAt hX
  have hAN := le_normalizer_of_mem_thetaComponentsAt h45 h hdA hd1 hX
  have hdX := not_mem_of_le_centralizer (center_eq_bot_of_mulEquiv eX') hXd (h.pow_three hdA) hd1
  have hCA := inf_thetaQuotCentralizer_eq h hdA hdo hXd hAN eX'
  obtain ⟨y, hyA, hy⟩ := exists_inducesOuterTheta h hdA hAN hdX eX'
  have hinv := invTwoBarNontrivial_of_inducesOuterTheta (fun x hx => h.pow_three hx)
    (fun x hx z hz => h.comm hx hz) eX' hyA hy
  obtain ⟨R', hR', hR'W⟩ := Sec11.exists_isSylowOf_inf 3
    (Subgroup.normalizer (Subgroup.zpowers d : Set G)) (Subgroup.normalizer (A : Set G))
  have h81 : Sec8.Hyp81 G A d X y :=
    { h.toHyp81 with
      mem_A := hdA
      ne_one := hd1
      mem_thetaComponentsAt := hX
      sectionCentralizer_eq := by rw [Sec13.sectionCentralizer_eq_inf hAN, hCA]
      a_mem := hyA
      a_ne_one := ne_one_of_inducesOuterTheta hy
      inducesStdKind := Or.inl (KFacts.InducesStdKind.psl2 (GaloisField 3 3)
        ⟨eX', KFacts.inducesKind_field_of_pow_three X (h.pow_three hyA) hy eX'⟩)
      exists_invariant_two := fun h27 => absurd h27 (by rw [h.card_eq]; norm_num) }
  exact ⟨y, R',
    { h81 with
      card_eq := h.card_eq
      invTwo_or_commutator := Or.inl (Or.inl hinv)
      isSylowOf := hR'
      isSylowOf_inf := hR'W
      not_mem_partTwoT_or_mem_partTwoS := h.not_mem_partTwoT_or_mem_partTwoS
      iso := ⟨eX⟩ }⟩

end Std

end Item1014Proof

end CFSG.RankThree.PartTwo.Sec10
