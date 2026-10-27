module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJStatements
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128NotHJTC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Lcbar

variable {G : Type} [Group G] [Finite G] {c : G} {L : Subgroup G}

theorem mul_mem_lcBar (hL : L ∈ thetaComponentsAt 3 c) {l z : G} (hl : l ∈ L)
    (hz : z ∈ Sec4.thetaQuotCentralizer L)
    (hzH : z ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) : l * z ∈ lcBar c L := by
  have hLH : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Sec13.le_normalizer_zpowers_of_mem hL
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hHdef
  set l₁ : H := ⟨l, hLH hl⟩ with hl₁
  set z₁ : H := ⟨z, hzH⟩ with hz₁
  refine ⟨l₁ * z₁, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul]
  refine Subgroup.mul_mem_sup ⟨l₁, Subgroup.mem_subgroupOf.mpr hl, rfl⟩ ?_
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨m, hm, rfl⟩
  have hmL : (m : G) ∈ L := Subgroup.mem_subgroupOf.mp hm
  have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp hz).2 _ hmL
  rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL, Sec13.inSubgroup_theta_centralizer] at h1
  obtain ⟨w, hw, hwe⟩ := h1.2.2
  have hw' : w = m⁻¹ * (z₁ * m * z₁⁻¹) := Subtype.ext (by simpa using hwe)
  have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 H) w = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hw
  rw [hw', map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  have h3 := inv_mul_eq_one.mp h2
  calc QuotientGroup.mk' (aschbacherSolvableCore 3 H) m *
        QuotientGroup.mk' (aschbacherSolvableCore 3 H) z₁ =
      (QuotientGroup.mk' (aschbacherSolvableCore 3 H) z₁ *
        QuotientGroup.mk' (aschbacherSolvableCore 3 H) m *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 H) z₁)⁻¹) *
        QuotientGroup.mk' (aschbacherSolvableCore 3 H) z₁ := by rw [← h3]
    _ = QuotientGroup.mk' (aschbacherSolvableCore 3 H) z₁ *
        QuotientGroup.mk' (aschbacherSolvableCore 3 H) m := by group

theorem thetaQuotMulAut_normalizerMonoidHom_coe (l : L)
    (hl : (l : G) ∈ Subgroup.normalizer (L : Set G)) :
    Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨(l : G), hl⟩) =
      MulAut.conj (l : L ⧸ aschbacherSolvableCore 3 L) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1

end Lcbar

section Inner

theorem centerDescend_conj {S : Type*} [Group S] (g : S) :
    KFacts.centerDescend S (MulAut.conj g) = MulAut.conj (g : S ⧸ Subgroup.center S) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [KFacts.centerDescend_mk, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem mem_range_conj_of_congr_mem {X Y : Type*} [Group X] [Group Y]
    (hXp : Group.IsPerfect X) (e : X ⧸ Subgroup.center X ≃* Y) {σ : MulAut X}
    (hσ : MulAut.congr e (KFacts.centerDescend X σ) ∈ (MulAut.conj : Y →* MulAut Y).range) :
    σ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨y, hy⟩ := hσ
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm y)
  have hdesc : KFacts.centerDescend X σ = KFacts.centerDescend X (MulAut.conj x) := by
    apply (MulAut.congr e).injective
    rw [← hy, centerDescend_conj, KFacts.congr_mulAutConj, hx, MulEquiv.apply_symm_apply]
  have : Group.IsPerfect X := hXp
  refine ⟨x, Sec4.mulAut_eq_of_inv_mul_mem_center fun s => ?_⟩
  have h1 := congrArg (fun τ : MulAut (X ⧸ Subgroup.center X) =>
    τ (s : X ⧸ Subgroup.center X)) hdesc
  simp only [KFacts.centerDescend_mk] at h1
  exact QuotientGroup.eq.mp h1

theorem mem_range_conj_of_isTripleCover
    {X : Type} [Group X] (hXp : Group.IsPerfect X)
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover X (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.M22)
    {σ : MulAut X} (hσ : σ ^ 3 = 1) : σ ∈ (MulAut.conj : X →* MulAut X).range := by
  have hpow : ∀ {Y : Type} [Group Y] (e : X ⧸ Subgroup.center X ≃* Y),
      (MulAut.congr e (KFacts.centerDescend X σ)) ^ 3 = 1 := fun e => by
    rw [← map_pow, ← map_pow, hσ, map_one, map_one]
  rcases hX with ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · exact mem_range_conj_of_congr_mem hXp e (Sec4.Item434Alt.mem_range_conj_of_pow_three (hpow e))
  · have h4 : 4 ≤ Nat.card (Fin 7) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    obtain ⟨y, hy⟩ := KFacts.KS14.exists_conj_of_card_mulAut_le
      (alternatingGroup.center_eq_bot h4)
      (by rw [KFacts.KS14.card_mulAut_alternatingGroup_seven,
        KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]) _
      ⟨1, by rw [pow_one]; exact hpow e⟩
    exact mem_range_conj_of_congr_mem hXp e ⟨y, hy.symm⟩
  · obtain ⟨y, hy⟩ := KFacts.KS14.exists_conj_of_card_mulAut_le
      CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card _
      ⟨1, by rw [pow_one]; exact hpow e⟩
    exact mem_range_conj_of_congr_mem hXp e ⟨y, hy.symm⟩

theorem mem_lcBar_of_pow_three
    {G : Type} [Group G] [Finite G] {c : G} {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 c)
    (hty : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {e : G} (heN : e ∈ Subgroup.normalizer (L : Set G))
    (heH : e ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) (he3 : e ^ 3 = 1) :
    e ∈ lcBar c L := by
  set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, heN⟩) with hσ
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨e, heN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using he3)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hLp : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) :=
    (isQuasisimple_thetaQuot_of_mem hL).1
  obtain ⟨yb, hyb⟩ := mem_range_conj_of_isTripleCover hLp hty hσ3
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective yb
  have hlN : (l : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l.2
  have hzN : (l : G)⁻¹ * e ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hlN) heN
  have hz : (l : G)⁻¹ * e ∈ Sec4.thetaQuotCentralizer L := by
    refine ⟨⟨(l : G)⁻¹ * e, hzN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have e1 : (⟨(l : G)⁻¹ * e, hzN⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨(l : G), hlN⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨e, heN⟩ := rfl
    rw [e1, map_mul, map_mul, map_inv, map_inv, ← hσ, ← hyb,
      thetaQuotMulAut_normalizerMonoidHom_coe l hlN]
    exact inv_mul_cancel _
  have hzH : (l : G)⁻¹ * e ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mul_mem (inv_mem (Sec13.le_normalizer_zpowers_of_mem hL l.2)) heH
  have := mul_mem_lcBar hL l.2 hz hzH
  rwa [mul_inv_cancel_left] at this

end Inner

section Main

variable {G : Type} [Group G] [Finite G]

theorem false_of_mem_normalizer
    (h45 : Sec4.Item4_5)
    (h125 : Item125BarTC) {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hty : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {a : G} (ha3 : a ^ 3 = 1) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (haK : a ∉ K)
    {F : Subgroup G} (hFK : F ≤ K) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hF9 : Nat.card F = 9) (hcF : c ∈ F) {n : G} (hnK : n ∈ K)
    (hnF : n ∈ Subgroup.normalizer (F : Set G)) (hnc : n * c * n⁻¹ ∉ Subgroup.zpowers c) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  obtain ⟨hEab, hE27⟩ := Sec13.isElemAbelian_zpowers_sup_of_card_nine ha3 (S := F) (Y := F)
    (fun haF => haK (hFK haF)) le_rfl hF9 (fun s hs => hF.2 s hs)
    (fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hKa (hFK hy))).symm)
  set E := Subgroup.zpowers a ⊔ F with hEdef
  have hcE : c ∈ E := Subgroup.mem_sup_right hcF
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.isE27.1.2 c h.mem_A) h.ne_one
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Sec13.centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hEcomm x hx c hcE))
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hc3
      h.mem_thetaComponentsAt hEp hEH
  have hEL : E ≤ lcBar c L := fun e he =>
    mem_lcBar_of_pow_three h.mem_thetaComponentsAt hty (hEN he) (hEH he) (hEab.2 e he)
  have hNE := h125 G A c L h hty E ⟨hEab, hE27⟩ hEL hcE
  have hnE : n ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnF ⊢
    rw [hEdef, Subgroup.map_sup, hnF, MonoidHom.map_zpowers]
    congr 2
    change n * a * n⁻¹ = a
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hKa hnK), mul_inv_cancel_right]
  exact hnc ((Subgroup.mem_normalizer_iff.mp (hNE hnE) c).mp (Subgroup.mem_zpowers c))

theorem isPGroup_zpowers_of_pow_three {Λ : Type*} [Group Λ] {c : Λ} (hc : c ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers c) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem false_of_bar
    (h45 : Sec4.Item4_5)
    (h125 : Item125BarTC) {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hty : Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {a : G} (ha3 : a ^ 3 = 1) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (haK : a ∉ K)
    (hcK : c ∈ K) {Fb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)}
    (hFb : CFSG.Assembly.IsElemAbelian 3 Fb) (hFb9 : Nat.card Fb = 9)
    (hcFb : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ ∈ Fb)
    {nb : K ⧸ aschbacherSolvableCore 3 K} (hnb : nb ∈ Subgroup.normalizer (Fb : Set _))
    (hnbc : nb * QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ * nb⁻¹ ∉
      Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩)) : False := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hπ
  set c' : K := ⟨c, hcK⟩ with hc'
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using h.isE27.1.2 c h.mem_A)
  have hFbp : IsPGroup 3 Fb := fun x => ⟨1, Subtype.ext (by simpa using hFb.2 x x.2)⟩
  obtain ⟨S, hcS, -, hS3, hSF⟩ := Sec13.exists_isPGroup_le_map_eq (M := ⊤) hFbp
    (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
    (isPGroup_zpowers_of_pow_three hc'3) le_top
    (by rw [MonoidHom.map_zpowers]; exact Subgroup.zpowers_le.mpr hcFb)
  have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three hS3
  have hSab : CFSG.Assembly.IsElemAbelian 3 S :=
    Sec13.isElemAbelian_of_injOn π hinj (hSF ▸ hFb)
  have hS9 : Nat.card S = 9 := by rw [← Sec13.card_map_eq_of_injOn π hinj, hSF, hFb9]
  have hN := Sec13.normalizer_map_mk_eq hS3
  rw [hSF] at hN
  rw [hN] at hnb
  obtain ⟨n, hn, rfl⟩ := hnb
  refine false_of_mem_normalizer h45 h125 h hty ha3 hK haK (F := S.map K.subtype)
    (Subgroup.map_subtype_le S) (Sec13.isElemAbelian_map hSab K.subtype)
    (by rw [Subgroup.card_map_of_injective K.subtype_injective, hS9])
    ⟨c', hcS (Subgroup.mem_zpowers c'), rfl⟩ n.2 (Sec13.mem_normalizer_map_subtype hn) ?_
  intro hmem
  apply hnbc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have e1 : c' ^ k = n * c' * n⁻¹ := Subtype.ext (by simpa using hk)
  rw [← map_zpow, e1, map_mul, map_mul, map_inv]

end Main

end CFSG.RankThree.PartTwo.Sec12.KS128NotHJTC
