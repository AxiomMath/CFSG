module

public import CFSG.Quasithin.EmptyFaithful.S153EB6D
public import CFSG.Quasithin.Background.SmithD321Q
public import CFSG.Quasithin.Background.SmithD39TwoClif
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D38Pair
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiModule
public import CFSG.Quasithin.Background.SmithD310UCount
public import CFSG.Quasithin.Background.SmithD321StepU

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

section Inner

variable {G : Type} [Group G]

theorem exists_inner_of_isSz (hSzA : H13.SzTwoAutInnerFact) {X : Subgroup G} {n : ℕ}
    (hX : IsSz n ↥X) {a : G} (ha : a ∈ Subgroup.normalizer (X : Set G)) (ha2 : a ^ 2 = 1) :
    ∃ l ∈ X, ∀ x ∈ X, a * x * a⁻¹ = l * x * l⁻¹ := by
  set α : MulAut ↥X := X.normalizerMonoidHom ⟨a, ha⟩ with hα
  have hα2 : α ^ 2 ^ 1 = 1 := by
    rw [pow_one, hα, ← map_pow]
    have : (⟨a, ha⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ 2 = 1 := Subtype.ext ha2
    rw [this, map_one]
  obtain ⟨q, hq⟩ := hSzA ↥X n hX α ⟨1, hα2⟩
  refine ⟨(q : G), q.2, fun x hx => ?_⟩
  have h1 := congrArg (fun β : MulAut ↥X => ((β ⟨x, hx⟩ : ↥X) : G)) hq
  simp only [hα, MulAut.conj_apply] at h1
  exact h1

end Inner

section Tilde

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]

theorem iso_tilde_smul_of_comm {X : Subgroup G} {W I : Subgroup V} {c : G}
    (hcX : ∀ x ∈ X, c * x = x * c) (hcW : ∀ w ∈ W, c • w ∈ W) (hcW' : ∀ w ∈ W, c⁻¹ • w ∈ W) :
    XMod.Iso ↥X (tilde X W (c • I)) (tilde X W I) := by
  set N := modFix X W with hN
  have hcN : ∀ g : G, (∀ x ∈ X, g * x = x * g) → (∀ w ∈ W, g • w ∈ W) →
      ∀ w ∈ N, g • w ∈ N := by
    intro g hgX hgW w hw
    refine XMod.mem_fixed.2 ⟨hgW w (XMod.mem_fixed.1 hw).1, fun x => ?_⟩
    show (x : G) • g • w = g • w
    rw [smul_smul, ← hgX x x.2, mul_smul]
    exact congrArg (g • ·) ((XMod.mem_fixed.1 hw).2 x)
  have hc'X : ∀ x ∈ X, c⁻¹ * x = x * c⁻¹ := fun x hx => by
    have := hcX x hx
    calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * x) * c⁻¹ := by rw [this]
      _ = x * c⁻¹ := by group
  set ψ : V ⧸ N →* V ⧸ N := QuotientGroup.map N N (MulDistribMulAction.toMonoidHom V c⁻¹)
    (fun w hw => hcN c⁻¹ hc'X hcW' w hw) with hψ
  have hψmk : ∀ v : V, ψ (QuotientGroup.mk v) = QuotientGroup.mk (c⁻¹ • v) := fun v => rfl
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H v =>
      rw [MonoidHom.mem_ker, hψmk, QuotientGroup.eq_one_iff] at hq
      rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
      have := hcN c hcX hcW _ hq
      rwa [smul_inv_smul] at this
  have himg : (tilde X W (c • I)).map ψ = tilde X W I := by
    unfold tilde
    rw [Subgroup.map_map]
    ext q
    simp only [Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hw
      exact ⟨c⁻¹ • w, hw, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨c • v, Subgroup.smul_mem_pointwise_smul v c I hv, ?_⟩
      show QuotientGroup.mk (c⁻¹ • c • v) = _
      rw [inv_smul_smul]
      rfl
  have hψX : ∀ (x : ↥X) (q : V ⧸ N), ψ (x • q) = x • ψ q := by
    intro x q
    induction q using QuotientGroup.induction_on with
    | H v =>
      show QuotientGroup.mk (c⁻¹ • (x : G) • v) = QuotientGroup.mk ((x : G) • c⁻¹ • v)
      rw [smul_smul, smul_smul, hc'X x x.2]
  refine ⟨(Subgroup.equivMapOfInjective _ ψ hψinj).trans (MulEquiv.subgroupCongr himg),
    fun x l l' hll' => ?_⟩
  show x • ψ (l : V ⧸ N) = ψ (l' : V ⧸ N)
  rw [← hψX, hll']

end Tilde


section Qhat

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem le_stabSub_of_inv {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) : X ≤ stabSub U :=
  CFSG.Quasithin.S153EB6.le_stabSub_of_inv hU

omit [Finite W] in
theorem conj_mem_autSub_of_normalizes {M X : Subgroup (MulAut W)} {I : Subgroup W}
    (hN : ∀ g ∈ M, g ∈ stabSub I → g ∈ Subgroup.normalizer (X : Set (MulAut W)))
    {e k : MulAut ↥I} (he : e ∈ autSub M I) (hk : k ∈ autSub X I) :
    e * k * e⁻¹ ∈ autSub X I := by
  obtain ⟨g, hgM, rfl⟩ := mem_autSub.1 he
  obtain ⟨x, hxX, rfl⟩ := mem_autSub.1 hk
  refine mem_autSub.2 ⟨g * x * g⁻¹, ?_, by simp only [map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.1 (hN g hgM g.2) x).1 hxX

theorem pCoreOf_two_eq_bot_of_simple' {Y : Type*} [Group Y] [Finite Y] {K : Subgroup Y}
    (hs : IsSimpleGroup ↥K) (hnot : ¬ IsPGroup 2 ↥K) : CFSG.Open.pCoreOf 2 K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hs.eq_bot_or_eq_top_of_normal ((CFSG.Open.pCoreOf 2 K).subgroupOf K) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 K hx⟩ : ↥K) ∈
        (CFSG.Open.pCoreOf 2 K).subgroupOf K := hx
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · exfalso
    apply hnot
    intro x
    have hx : x ∈ (CFSG.Open.pCoreOf 2 K).subgroupOf K := by rw [h]; trivial
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨(x : Y), hx⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩


theorem not_isPGroup_two_of_isQuasisimple {Y : Type*} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) : ¬ IsPGroup 2 Y := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent Y := IsPGroup.isNilpotent h2
  have : Group.IsPerfect Y := hY.1
  have : Nontrivial Y := by
    obtain ⟨a, b, hab⟩ := hY.2.2
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hab
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [Subsingleton.elim x 1, Subsingleton.elim y 1]
  exact Group.IsPerfect.not_isSolvable Y inferInstance

omit [Finite W] in
theorem mem_fixV_iff_of_mem_normalizer {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (X : Set (MulAut W))) {w : W} :
    g w ∈ fixV X ↔ w ∈ fixV X := by
  have key : ∀ h : MulAut W, h ∈ Subgroup.normalizer (X : Set (MulAut W)) →
      ∀ w ∈ fixV X, h w ∈ fixV X := by
    intro h hh w hw
    refine mem_fixV.2 fun x hx => ?_
    have h1 : h⁻¹ * x * h ∈ X := (Subgroup.mem_normalizer_iff''.1 hh x).1 hx
    have h2 := (mem_fixV.1 hw) _ h1
    calc x (h w) = h ((h⁻¹ * x * h) w) := by simp [MulAut.mul_apply]
      _ = h w := by rw [h2]
  refine ⟨fun h => ?_, key g hg w⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ h
  simpa using this


theorem two_le_qhatOf_autSub_of_isSz (hB45 : AsB45)
    (hF : Vol2.Ch10.SecA.Facts10_1) (hA21 : AsA21SQTKSection) (hW : ∀ w : W, w ^ 2 = 1)
    {M X : Subgroup (MulAut W)} (hMq : IsQuotientOfSQTKTC ↥M) (hXM : X ≤ M)
    (hXs : IsSimpleGroup ↥X) (hXq : CFSG.IsQuasisimple ↥X) {n : ℕ} (hXsz : IsSz n ↥X)
    {I : Subgroup W} (hI : I ∈ IrrPlus X (⊤ : Subgroup W))
    (hN : ∀ g ∈ M, g ∈ stabSub I → g ∈ Subgroup.normalizer (X : Set (MulAut W))) :
    ((2 : ℚ) : WithTop ℚ) ≤ qhatOf (autSub M I) := by
  obtain ⟨hXI, hcomm, hlt, hmax⟩ := mem_irrPlus_top_iff.1 hI
  have hXs' : X ≤ stabSub I := le_stabSub_of_inv hXI
  set K := autSub X I with hK
  set C : Subgroup ↥I := (I ⊓ fixV X).subgroupOf I with hC
  have hexp : ∀ w : ↥I, w ^ 2 = 1 := fun w => Subtype.ext (by simp [hW])
  have hne : ¬ X ≤ centSub I := by
    intro h
    apply hlt.not_ge
    intro v hv
    exact ⟨hv, fun x hx => h hx v hv⟩
  have hfaith : X ⊓ centSub I = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hXs hXs' hne
  let eK : ↥X ≃* ↥K := autSubEquivOfFaithful hXs' hfaith
  have hKs : IsSimpleGroup ↥K := eK.symm.isSimpleGroup
  have hKq : CFSG.IsQuasisimple ↥K := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK hXq
  have hKsz : ∃ n, CFSG.Blueprint.SuzukiModel ↥K 2 n := ⟨n, H13.suzukiModel_congr eK.symm hXsz⟩
  obtain ⟨S, _, _, hSQT, hSK, φ, hφ⟩ := hMq
  have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hSK⟩
  have hSX : SQTKGroup ↥X := B69.sqtk_subgroup hA21 hS φ hφ hXM hXq
  have hSKK : SQTKGroup ↥K := B69.sqtk_autSub hA21 hXs' hSX hKq
  have hmemC : ∀ u : ↥I, u ∈ C ↔ (u : W) ∈ fixV X := fun u => by
    rw [hC, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hCfix : C ≤ fixV K := by
    intro u hu k hk
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hk
    apply Subtype.ext
    rw [resHom_apply]
    exact (mem_fixV.1 ((hmemC u).1 hu)) _ hg
  have hstabN : ∀ g : stabSub I,
      (g : MulAut W) ∈ Subgroup.normalizer (X : Set (MulAut W)) → resHom I g ∈ stabSub C := by
    intro g hg u
    rw [hmemC, hmemC, resHom_apply]
    exact mem_fixV_iff_of_mem_normalizer hg
  have hKstab : K ≤ stabSub C := by
    intro k hk
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hk
    exact hstabN g (Subgroup.le_normalizer hg)
  have hKcomm : commV K = ⊤ := insp5a_sec_comm hXs' hcomm
  have hClt : C < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hlt.not_ge
    intro v hv
    have : (⟨v, hv⟩ : ↥I) ∈ C := by rw [h]; trivial
    exact ⟨hv, (hmemC _).1 this⟩
  have hKirr : ∀ J : Subgroup ↥I, C ≤ J → (∀ k ∈ K, ∀ w ∈ J, k w ∈ J) → J = C ∨ J = ⊤ := by
    intro J hCJ hJ
    have hinv : ∀ x ∈ X, ∀ w ∈ J.map I.subtype, x w ∈ J.map I.subtype := by
      rintro x hx _ ⟨w, hw, rfl⟩
      refine ⟨resHom I ⟨x, hXs' hx⟩ w, hJ _ (mem_autSub.2 ⟨⟨x, hXs' hx⟩, hx, rfl⟩) w hw, ?_⟩
      rw [Subgroup.coe_subtype, resHom_apply]
    have hfix : I ⊓ fixV X ≤ J.map I.subtype := by
      intro v hv
      exact ⟨⟨v, hv.1⟩, hCJ ((hmemC ⟨v, hv.1⟩).2 hv.2), rfl⟩
    rcases hmax (J.map I.subtype) hinv hfix (Subgroup.map_subtype_le J) with h | h
    · left
      ext u
      have e1 : u ∈ J ↔ (u : W) ∈ J.map I.subtype :=
        (Subgroup.mem_map_iff_mem I.subtype_injective).symm
      rw [e1, h, hmemC]
      exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
    · right
      rw [eq_top_iff]
      intro u _
      have hu : (u : W) ∈ J.map I.subtype := by rw [h]; exact u.2
      exact (Subgroup.mem_map_iff_mem (x := u) I.subtype_injective).mp hu
  have hO2 : CFSG.Open.pCoreOf 2 K = ⊥ :=
    pCoreOf_two_eq_bot_of_simple' hKs (not_isPGroup_two_of_isQuasisimple hKq)
  have hKfaith : K ⊓ centSec ⊤ C = ⊥ :=
    InternalSec.inf_centSec_eq_bot_of_pCoreOf hexp hKstab hCfix hO2
  refine le_kq_iff.2 fun E hE hE3 => ?_
  have hEK : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ ∈ K := fun e he k hk =>
    conj_mem_autSub_of_normalizes hN (hE.1 he) hk
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := hE.isElemAbelian2.2
  have hEstab : E ≤ stabSub C := by
    intro e he
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 (hE.1 he)
    exact hstabN g (hN _ hg g.2)
  have hQ : InternalSec.QSec (K ⊔ E) K C :=
    { le := le_sup_left
      normal := fun y hy k hk =>
        (Subgroup.mem_normalizer_iff.1 (SmithD39Two.sup_le_normalizer hEK hy) k).1 hk
      two := fun y hy => ⟨1, by simpa using SmithD39Two.sq_mem_of_mem_sup hEK hE2 hy⟩
      stab := sup_le hKstab hEstab
      fix := hCfix
      comm := hKcomm
      lt := hClt
      irr := hKirr
      faithful := hKfaith
      quasi := hKq }
  have h2 : ((2 : ℚ) : WithTop ℚ) ≤ qhatOf (K ⊔ E) := by
    rcases le_or_gt (qhatOf (K ⊔ E)) ((2 : ℚ) : WithTop ℚ) with hq | hq
    · exact (H13.two_le_qhatOf_autSec_of_suzuki hB45 hF hexp hQ hSKK hKs hKsz hq).trans
        (hQ.qhatOf_autSec_le hexp)
    · exact hq.le
  exact le_kq_iff.1 h2 E ⟨le_sup_right, hE.ne_bot, hE.isElemAbelian2⟩ hE3

end Qhat


section Z1

variable {W : Type} [CommGroup W] [Finite W]

theorem le_of_mem_of_isSimpleGroup {G : Type*} [Group G] {X N : Subgroup G}
    (hXs : IsSimpleGroup ↥X) (hXN : X ≤ Subgroup.normalizer (N : Set G)) {a : G}
    (haX : a ∈ Subgroup.normalizer (X : Set G)) (haN : a ∈ N)
    (ha : ¬ ∀ x ∈ X, a * x = x * a) : X ≤ N := by
  have hnorm : ((X ⊓ N).subgroupOf X).Normal := by
    refine ⟨fun n hn y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨X.mul_mem (X.mul_mem y.2 hn.1) (X.inv_mem y.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (hXN y.2) _).1 hn.2
  rcases hXs.eq_bot_or_eq_top_of_normal ((X ⊓ N).subgroupOf X) with h | h
  · exfalso
    apply ha
    intro x hx
    have hc : x * a * x⁻¹ * a⁻¹ ∈ X ⊓ N := by
      refine ⟨?_, ?_⟩
      · have : a * x⁻¹ * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 haX _).1 (X.inv_mem hx)
        have h2 := X.mul_mem hx this
        rwa [← mul_assoc, ← mul_assoc] at h2
      · exact N.mul_mem ((Subgroup.mem_normalizer_iff.1 (hXN hx) a).1 haN) (N.inv_mem haN)
    have hc' : (⟨_, hc.1⟩ : ↥X) ∈ (X ⊓ N).subgroupOf X := hc
    rw [h, Subgroup.mem_bot] at hc'
    have h1 : x * a * x⁻¹ * a⁻¹ = 1 := congrArg Subtype.val hc'
    have h2 : x * a = a * x := by
      calc x * a = x * a * x⁻¹ * a⁻¹ * (a * x) := by group
        _ = a * x := by rw [h1, one_mul]
    exact h2.symm
  · intro x hx
    have : (⟨x, hx⟩ : ↥X) ∈ (X ⊓ N).subgroupOf X := by rw [h]; trivial
    exact this.2

omit [Finite W] in
theorem smul_mem_biSup_of_normalizes {T X : Subgroup (MulAut W)}
    (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut W))) {I : Subgroup W}
    (hI : ∀ x ∈ X, ∀ v ∈ I, x v ∈ I) {x : MulAut W} (hx : x ∈ X) {w : W}
    (hw : w ∈ ⨆ y ∈ T, y • I) : x w ∈ ⨆ y ∈ T, y • I := by
  have hW₁eq : (⨆ y ∈ T, y • I) = ⨆ r : T, (r : MulAut W) • I :=
    (iSup_subtype (p := (· ∈ T)) (f := fun r : T => (r : MulAut W) • I)).symm
  rw [hW₁eq] at hw ⊢
  refine Subgroup.iSup_induction (fun r : T => (r : MulAut W) • I)
    (C := fun w => x w ∈ ⨆ r : T, (r : MulAut W) • I) hw (fun r w hw => ?_) ?_ ?_
  · rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hw
    have h1 : (r : MulAut W)⁻¹ * x * (r : MulAut W) ∈ X :=
      (Subgroup.mem_normalizer_iff''.1 (hTX r.2) x).1 hx
    have h2 := hI _ h1 _ hw
    set ρ : MulAut W := (r : MulAut W) with hρ
    have h3 : x w = ρ • ((ρ⁻¹ * x * ρ) (ρ⁻¹ • w)) := by
      show x w = ρ ((ρ⁻¹ * x * ρ) (ρ⁻¹ w))
      simp [MulAut.mul_apply]
    rw [h3]
    exact (le_iSup (fun r : T => (r : MulAut W) • I) r)
      (Subgroup.smul_mem_pointwise_smul _ _ I h2)
  · rw [map_one]
    exact one_mem _
  · intro w w' hw hw'
    rw [map_mul]
    exact mul_mem hw hw'


omit [Finite W] in
theorem smul_eq_of_mem {X : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : ∀ x ∈ X, ∀ v ∈ J, x v ∈ J) {g : MulAut W} (hg : g ∈ X) : g • J = J := by
  ext w
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · intro h
    have := hJ g hg _ h
    simpa using this
  · intro h
    exact hJ _ (X.inv_mem hg) w h

theorem exists_irrPlus_ge_commV (hSzA : H13.SzTwoAutInnerFact)
    (hB45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1) (hA21 : AsA21SQTKSection)
    (hW : ∀ w : W, w ^ 2 = 1) {M X X' A : Subgroup (MulAut W)} {r : ℚ}
    (hMq : IsQuotientOfSQTKTC ↥M) (hXM : X ≤ M) (hXs : IsSimpleGroup ↥X)
    (hXq : CFSG.IsQuasisimple ↥X) {n : ℕ} (hXsz : IsSz n ↥X)
    (hswap : ∀ g ∈ M, g ∉ Subgroup.normalizer (X : Set (MulAut W)) → conjAutSub g X = X')
    (hX'fix : commV X ≤ fixV X') (hr : qhatOf M = (r : WithTop ℚ)) (hr2 : r ≤ 2)
    (hA : A ∈ QhatStar M) (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hAc : ¬ A ≤ Subgroup.centralizer (X : Set (MulAut W))) {I₀ : Subgroup W}
    (hI₀ : I₀ ∈ IrrPlus X (⊤ : Subgroup W)) :
    ∃ I ∈ IrrPlus X (⊤ : Subgroup W), commV X ≤ I := by
  obtain ⟨-, -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := id hA
  have hAsq : ∀ a ∈ A, a ^ 2 = 1 := hA2.isElemAbelian2.2
  have hAp : IsPGroup 2 ↥A := hA2.isElemAbelian2.isPGroup
  obtain ⟨a₀, ha₀A, ha₀⟩ : ∃ a ∈ A, ¬ ∀ x ∈ X, a * x = x * a := by
    by_contra h
    push Not at h
    exact hAc fun a ha => Subgroup.mem_centralizer_iff.2 fun x hx => (h a ha x hx).symm
  obtain ⟨I, hI⟩ := irrPlusOn_nonempty hW hAX hAp hI₀
  set W₁ := ⨆ y ∈ A, y • I₀ with hW₁
  have hW₁A : ∀ t ∈ A, ∀ w ∈ W₁, t • w ∈ W₁ := fun t ht w hw => smul_mem_biSup_smul ht hw
  obtain ⟨hI₀X, -, -, -⟩ := mem_irrPlus_top_iff.1 hI₀
  have hW₁X : ∀ x ∈ X, ∀ w ∈ W₁, x w ∈ W₁ := fun x hx w hw =>
    smul_mem_biSup_of_normalizes hAX hI₀X hx hw
  have hIplus : I ∈ IrrPlus X (⊤ : Subgroup W) := ⟨le_top, hI.1.2⟩
  obtain ⟨hXI, hcomm, hlt, -⟩ := mem_irrPlus_top_iff.1 hIplus
  have hstab : ∀ a ∈ A, a • I = I := by
    refine (forall_smul_eq_iff_mem_irrPlusOn hAX hW₁A hI.1).2 hI
      |> fun h a ha => h a ⟨ha, ?_⟩
    obtain ⟨l, hlX, hl⟩ := exists_inner_of_isSz hSzA hXsz (hAX ha) (hAsq a ha)
    set c := l⁻¹ * a with hc
    have hcX : ∀ x ∈ X, c * x = x * c := by
      intro x hx
      have h1 := hl x hx
      calc c * x = l⁻¹ * (a * x * a⁻¹) * a := by rw [hc]; group
        _ = l⁻¹ * (l * x * l⁻¹) * a := by rw [h1]
        _ = x * c := by rw [hc]; group
    have hcI : ∀ x ∈ X, ∀ v ∈ c • I, x v ∈ c • I := by
      intro x hx v hv
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hv ⊢
      have h1 : c⁻¹ • x v = x (c⁻¹ • v) := by
        show c⁻¹ (x v) = x (c⁻¹ v)
        have h2 : c⁻¹ * x = x * c⁻¹ := by
          calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
            _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcX x hx]
            _ = x * c⁻¹ := by group
        exact congrArg (fun φ : MulAut W => φ v) h2
      rw [h1]
      exact hXI x hx _ hv
    have haI : a • I = c • I := by
      rw [show a = l * c by rw [hc]; group, mul_smul, smul_eq_of_mem hcI hlX]
    rw [haI]
    refine iso_tilde_smul_of_comm hcX (fun w hw => ?_) (fun w hw => ?_)
    · show (l⁻¹ * a) w ∈ W₁
      rw [MulAut.mul_apply]
      exact hW₁X _ (X.inv_mem hlX) _ (hW₁A a ha w hw)
    · show (l⁻¹ * a)⁻¹ w ∈ W₁
      rw [mul_inv_rev, inv_inv, MulAut.mul_apply]
      exact hW₁A _ (A.inv_mem ha) _ (hW₁X _ hlX w hw)
  have hAI : A ≤ stabSub I := fun a ha => mem_stabSub_iff_map_eq.2 (hstab a ha)
  have hXI' : ∀ a ∈ A, ∀ w ∈ I, a w ∈ I := fun a ha w hw => ((hAI ha) w).2 hw
  have hXs' : X ≤ stabSub I := le_stabSub_of_inv hXI
  have hne : ¬ X ≤ centSub I := by
    intro h
    apply hlt.not_ge
    intro v hv
    exact ⟨hv, fun x hx => h hx v hv⟩
  have hIcomm : I ≤ commV X := by
    calc I = commSub I X := hcomm.symm
      _ ≤ commV X := by rw [commV_eq_commSub]; exact commSub_mono le_top le_rfl
  have hN : ∀ g ∈ M, g ∈ stabSub I → g ∈ Subgroup.normalizer (X : Set (MulAut W)) := by
    intro g hgM hgI
    by_contra hgN
    apply hne
    intro x hx v hv
    have hgx : g * x * g⁻¹ ∈ X' := by
      rw [← hswap g hgM hgN]
      exact ⟨x, hx, rfl⟩
    have hgv : g v ∈ I := (hgI v).2 hv
    have h1 := (mem_fixV.1 (hX'fix (hIcomm hgv))) _ hgx
    have h2 : g (x v) = g v := by simpa [MulAut.mul_apply] using h1
    exact g.injective h2
  have hIA : commSub I A ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    apply hne
    refine le_of_mem_of_isSimpleGroup hXs (fun x hx => ?_) (hAX ha₀A)
      (fun v hv => (mem_fixV.1 (h hv)) a₀ ha₀A) ha₀
    refine SmithD39Two.mem_normalizer_of_conj (fun y hy g hg u hu => ?_) hx
    have hyu : y⁻¹ u ∈ I := ((hXs' (X.inv_mem hy)) u).2 hu
    show y (g (y⁻¹ u)) = u
    rw [hg _ hyu, MulAut.apply_inv_self]
  have hq : (r : WithTop ℚ) ≤ qhatOf (autSub M I) :=
    (WithTop.coe_le_coe.2 hr2).trans
      (two_le_qhatOf_autSub_of_isSz hB45 hF hA21 hW hMq hXM hXs hXq hXsz hIplus hN)
  obtain ⟨-, -, hsup, -⟩ := D2_8 hW hr hA hAI hIA hq
  have hAsec : ∀ a ∈ A, a ∈ centSec ⊤ I := by
    intro a ha
    refine ⟨fun _ => Iff.rfl, fun w _ => ?_⟩
    have hw : w ∈ I ⊔ fixV A := by rw [hsup]; trivial
    obtain ⟨i, hi, f, hf, rfl⟩ := Subgroup.mem_sup.1 hw
    have haf : a f = f := (mem_fixV.1 hf) a ha
    have h1 : a (i * f) * (i * f)⁻¹ = a i * i⁻¹ := by
      rw [map_mul, haf, mul_inv_rev]
      group
    rw [h1]
    exact I.mul_mem (hXI' a ha i hi) (I.inv_mem hi)
  have hXsec : X ≤ centSec ⊤ I := by
    refine le_of_mem_of_isSimpleGroup hXs (fun x hx => ?_) (hAX ha₀A) (hAsec a₀ ha₀A) ha₀
    refine SmithD39Two.mem_normalizer_of_conj (fun y hy g hg => ?_) hx
    refine ⟨fun _ => Iff.rfl, fun w _ => ?_⟩
    have h1 := hg.2 (y⁻¹ w) trivial
    have h2 : (y * g * y⁻¹) w * w⁻¹ = y (g (y⁻¹ w) * (y⁻¹ w)⁻¹) := by
      simp [MulAut.mul_apply]
    rw [h2]
    exact hXI y hy _ h1
  refine ⟨I, hIplus, ?_⟩
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  exact (hXsec hx).2 v trivial

omit [Finite W] in
theorem exists_act_of_mem_sup {X X' : Subgroup (MulAut W)} {J : Subgroup W}
    (hJX : ∀ x ∈ X, ∀ w ∈ J, x w ∈ J) (hJ : J ≤ fixV X') {g : MulAut W} (hg : g ∈ X ⊔ X') :
    ∃ x ∈ X, ∀ w ∈ J, g w = x w := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, fun _ _ => rfl⟩
    · exact ⟨1, X.one_mem, fun w hw => by rw [(mem_fixV.1 (hJ hw)) y hy]; rfl⟩
  | one => exact ⟨1, X.one_mem, fun _ _ => rfl⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, ha, hya⟩ := hy
    obtain ⟨b, hb, hzb⟩ := hz
    refine ⟨a * b, X.mul_mem ha hb, fun w hw => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, hzb w hw, hya _ (hJX b hb w hw)]
  | inv y _ hy =>
    obtain ⟨a, ha, hya⟩ := hy
    refine ⟨a⁻¹, X.inv_mem ha, fun w hw => ?_⟩
    have h2 : y (a⁻¹ w) = w := by
      rw [hya _ (hJX _ (X.inv_mem ha) w hw), MulAut.apply_inv_self]
    calc y⁻¹ w = y⁻¹ (y (a⁻¹ w)) := by rw [h2]
      _ = a⁻¹ w := MulAut.inv_apply_self W y _

omit [Finite W] in
theorem mem_irrPlus_of_sup {X X' : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : J ∈ IrrPlus (X ⊔ X') (⊤ : Subgroup W)) (hX'J : J ≤ fixV X') :
    J ∈ IrrPlus X (⊤ : Subgroup W) := by
  obtain ⟨hinv, hcomm, hlt, hmax⟩ := mem_irrPlus_top_iff.1 hJ
  have hJX : ∀ x ∈ X, ∀ w ∈ J, x w ∈ J := fun x hx w hw =>
    hinv x (Subgroup.mem_sup_left hx) w hw
  have hfix : J ⊓ fixV X = J ⊓ fixV (X ⊔ X') := by
    apply le_antisymm
    · rintro w ⟨hw, hwX⟩
      refine ⟨hw, mem_fixV.2 fun g hg => ?_⟩
      obtain ⟨x, hx, hgx⟩ := exists_act_of_mem_sup hJX hX'J hg
      rw [hgx w hw]
      exact (mem_fixV.1 hwX) x hx
    · exact inf_le_inf_left _ (fixV_anti le_sup_left)
  refine mem_irrPlus_top_iff.2 ⟨hJX, le_antisymm (commSub_le_of_invariant hJX) ?_,
    by rw [hfix]; exact hlt, fun K hK hCK hKJ => ?_⟩
  · calc J = commSub J (X ⊔ X') := hcomm.symm
      _ ≤ commSub J X := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨g, hg, w, hw, rfl⟩
        obtain ⟨x, hx, hgx⟩ := exists_act_of_mem_sup hJX hX'J hg
        rw [hgx w hw]
        exact Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩
  · have hK' : ∀ g ∈ X ⊔ X', ∀ w ∈ K, g w ∈ K := by
      intro g hg w hw
      obtain ⟨x, hx, hgx⟩ := exists_act_of_mem_sup hJX hX'J hg
      rw [hgx w (hKJ hw)]
      exact hK x hx w hw
    rw [hfix]
    exact hmax K hK' (hfix ▸ hCK) hKJ

theorem commV_le_sup_fixV (hSzA : H13.SzTwoAutInnerFact)
    (hB45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1) (hA21 : AsA21SQTKSection)
    (hW : ∀ w : W, w ^ 2 = 1) {M X X' A : Subgroup (MulAut W)} {r : ℚ}
    (hMq : IsQuotientOfSQTKTC ↥M) (hXM : X ≤ M) (hXs : IsSimpleGroup ↥X)
    (hXq : CFSG.IsQuasisimple ↥X) {n : ℕ} (hXsz : IsSz n ↥X)
    (hswap : ∀ g ∈ M, g ∉ Subgroup.normalizer (X : Set (MulAut W)) → conjAutSub g X = X')
    (hX'fix : commV X ≤ fixV X') (hr : qhatOf M = (r : WithTop ℚ)) (hr2 : r ≤ 2)
    (hA : A ∈ QhatStar M) (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hAc : ¬ A ≤ Subgroup.centralizer (X : Set (MulAut W))) {J : Subgroup W}
    (hJ : J ∈ IrrPlus X (⊤ : Subgroup W)) (hJU : J ≤ commV X) :
    commV X ≤ J ⊔ fixV (X ⊔ X') := by
  obtain ⟨I, hI, hUI⟩ := exists_irrPlus_ge_commV hSzA hB45 hF hA21 hW hMq hXM hXs hXq hXsz
    hswap hX'fix hr hr2 hA hAX hAc hJ
  obtain ⟨-, hIc, -, hmax⟩ := mem_irrPlus_top_iff.1 hI
  obtain ⟨hXJ, -, hJlt, -⟩ := mem_irrPlus_top_iff.1 hJ
  have hJI : J ≤ I := hJU.trans hUI
  have hIU : I ≤ commV X := by
    calc I = commSub I X := hIc.symm
      _ ≤ commV X := by rw [commV_eq_commSub]; exact commSub_mono le_top le_rfl
  have hinv : ∀ x ∈ X, ∀ w ∈ J ⊔ (I ⊓ fixV X), x w ∈ J ⊔ (I ⊓ fixV X) := by
    intro x hx w hw
    obtain ⟨j, hj, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul, (mem_fixV.1 hc.2) x hx]
    exact Subgroup.mul_mem_sup (hXJ x hx j hj) hc
  rcases hmax _ hinv le_sup_right (sup_le hJI inf_le_left) with h | h
  · exfalso
    apply hJlt.not_ge
    intro j hj
    have : j ∈ I ⊓ fixV X := by rw [← h]; exact Subgroup.mem_sup_left hj
    exact ⟨hj, this.2⟩
  · rw [fixV_sup]
    calc commV X ≤ I := hUI
      _ = J ⊔ (I ⊓ fixV X) := h.symm
      _ ≤ J ⊔ (fixV X ⊓ fixV X') :=
        sup_le_sup_left (le_inf inf_le_right (inf_le_left.trans (hIU.trans hX'fix))) _

end Z1

section Rank

variable {G : Type} [Group G]

theorem mem_centralizer_sup {H K : Subgroup G} {b : G} (hH : b ∈ Subgroup.centralizer (H : Set G))
    (hK : b ∈ Subgroup.centralizer (K : Set G)) :
    b ∈ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  have hle : H ⊔ K ≤ Subgroup.centralizer ({b} : Set G) :=
    sup_le (fun h hh => Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]
        exact ((Subgroup.mem_centralizer_iff.1 hH) h hh).symm)
      (fun k hk => Subgroup.mem_centralizer_iff.2 fun g hg => by
        rw [Set.mem_singleton_iff.1 hg]
        exact ((Subgroup.mem_centralizer_iff.1 hK) k hk).symm)
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  exact ((Subgroup.mem_centralizer_iff.1 (hle hy)) b rfl).symm

theorem center_eq_bot_of_isSimpleGroup {X : Type*} [Group X] [hs : IsSimpleGroup X]
    (h : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h' | h'
  · exact h'
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have : a ∈ Subgroup.center X := by rw [h']; trivial
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)

theorem card_le_of_isSz (hSzA : H13.SzTwoAutInnerFact)
    {X E : Subgroup G} {n : ℕ} (hX : IsSz n ↥X) (hXs : IsSimpleGroup ↥X)
    (hXq : CFSG.IsQuasisimple ↥X) (hEN : E ≤ Subgroup.normalizer (X : Set G))
    (hE2 : ∀ e ∈ E, e ^ 2 = 1) :
    Nat.card ↥E ≤ 2 ^ n * Nat.card ↥(E ⊓ Subgroup.centralizer (X : Set G)) := by
  classical
  set ρ : ↥E →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hEN) with hρ
  have hker : Nat.card ρ.ker = Nat.card ↥(E ⊓ Subgroup.centralizer (X : Set G)) := by
    refine Nat.card_congr
      { toFun := fun e => ⟨(e : G), e.1.2, ?_⟩
        invFun := fun e => ⟨⟨(e : G), e.2.1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · have h1 := e.2
      rw [MonoidHom.mem_ker] at h1
      refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      have h2 := congrArg (fun φ : MulAut ↥X => ((φ ⟨x, hx⟩ : ↥X) : G)) h1
      simp only [hρ, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply,
        Subgroup.coe_inclusion] at h2
      calc x * ((e : ↥E) : G) = (((e : ↥E) : G) * x * ((e : ↥E) : G)⁻¹) * ((e : ↥E) : G) := by
            rw [h2]
        _ = ((e : ↥E) : G) * x := by group
    · rw [MonoidHom.mem_ker]
      ext x
      simp only [hρ, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply, Subgroup.coe_inclusion]
      rw [(Subgroup.mem_centralizer_iff.1 e.2.2 x x.2).symm]
      group
  have h1 : Nat.card ↥E = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hnc : ∃ a b : ↥X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXq.2.2
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  have hZ : Subgroup.center ↥X = ⊥ := center_eq_bot_of_isSimpleGroup hnc
  set ι : ↥X →* MulAut ↥X := MulAut.conj with hι
  have hιinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    rw [MonoidHom.mem_ker] at hq
    have : q ∈ Subgroup.center ↥X := Subgroup.mem_center_iff.2 fun z => by
      have h2 := congrArg (fun φ : MulAut ↥X => φ z) hq
      simp only [hι, MulAut.conj_apply, MulAut.one_apply] at h2
      calc z * q = q * z * q⁻¹ * q := by rw [h2]
        _ = q * z := by group
    rw [hZ] at this
    exact this
  have hrange : ρ.range ≤ ι.range := by
    rintro _ ⟨e, rfl⟩
    have he2 : ρ e ^ 2 ^ 1 = 1 := by
      rw [pow_one, ← map_pow]
      have : e ^ 2 = 1 := Subtype.ext (hE2 _ e.2)
      rw [this, map_one]
    obtain ⟨q, hq⟩ := hSzA ↥X n hX (ρ e) ⟨1, he2⟩
    exact ⟨q, hq.symm⟩
  set F : Subgroup ↥X := ρ.range.comap ι with hF
  have hFcard : Nat.card ↥F = Nat.card ρ.range := by
    rw [← Subgroup.card_map_of_injective (K := F) hιinj, hF, Subgroup.map_comap_eq,
      inf_eq_right.2 hrange]
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    intro f hf
    obtain ⟨e, he⟩ := hf
    apply hιinj
    rw [map_mul, ← he, ← map_mul, map_one]
    have : e * e = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two]; exact hE2 _ e.2)
    rw [this, map_one]
  obtain ⟨-, a, -, K, _, _, hn, hK, ⟨eX⟩⟩ := hX
  have hFK := CFSG.QuasithinUnique.Setup.Family.suzuki_exponent_two_card_le (hn ▸ hK)
    (F.map eX.toMonoidHom) (by
      rintro _ ⟨f, hf, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, hF2 f hf, map_one])
  rw [Subgroup.card_map_of_injective eX.injective, hFcard, ← hn] at hFK
  rw [h1, hker]
  exact Nat.mul_le_mul_right _ hFK

end Rank

namespace D321Sit

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

theorem V_mem_irrPlus_L (hS : D321Sit M Mp T L V t A r)
    (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) : V ∈ IrrPlus L (⊤ : Subgroup W) :=
  mem_irrPlus_of_sup (X' := conjAutSub t L) (hS.hMp ▸ hS.hD.hyp.irr)
    (fun v hv => mem_fixV.2 fun g hg => hVt v hv g hg)

theorem isSz_Lt (hS : D321Sit M Mp T L V t A r) {n : ℕ} (hSz : IsSz n ↥L) :
    IsSz n ↥(conjAutSub t L) :=
  have _ := hS
  H13.suzukiModel_congr (Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective).symm hSz

theorem le_normalizer_Lt (hS : D321Sit M Mp T L V t A r)
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    A ≤ Subgroup.normalizer (conjAutSub t L : Set (MulAut W)) := fun _ ha =>
  mem_normalizer_iff_conjAutSub.2 (hS.conj_Lt_of_mem_normalizer (hS.A_le ha) (hAN ha))

theorem conjAutSub_Mp (hS : D321Sit M Mp T L V t A r) {g : MulAut W} (hg : g ∈ M) :
    conjAutSub g Mp = Mp :=
  mem_normalizer_iff_conjAutSub.1 (hS.hD.hyp.Mp_normal hg)

theorem false_of_le_normalizer_L (hSzA : H13.SzTwoAutInnerFact)
    (hB45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1) (hA21 : AsA21SQTKSection)
    (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) {n : ℕ}
    (hSz : IsSz n ↥L) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAc : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W))) : False := by
  have h := commV_le_sup_fixV hSzA hB45 hF hA21 hS.exp hS.hD.hyp.qsqtk hS.L_le hS.hsimp
    hS.quasi hSz (fun g hg hgL => (hS.conj_swap hg hgL).1) (hS.commV_le_fixV hVt) hS.hr hS.hr2
    hS.hAQ hAN hAc (hS.V_mem_irrPlus_L hVt) (hS.V_le_commV hVt)
  rw [← hS.hMp] at h
  exact hS.not_le_orbSup hS.htop (h.trans (sup_le_sup_right (le_orbSup T V) _))

theorem false_of_le_normalizer_Lt (hSzA : H13.SzTwoAutInnerFact)
    (hB45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1) (hA21 : AsA21SQTKSection)
    (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) {n : ℕ}
    (hSz : IsSz n ↥L) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hAc : ¬ A ≤ Subgroup.centralizer (conjAutSub t L : Set (MulAut W))) : False := by
  have hswap : ∀ g ∈ M, g ∉ Subgroup.normalizer (conjAutSub t L : Set (MulAut W)) →
      conjAutSub g (conjAutSub t L) = L := by
    intro g hg hgN
    by_cases hgL : g ∈ Subgroup.normalizer (L : Set (MulAut W))
    · exact absurd (mem_normalizer_iff_conjAutSub.2 (hS.conj_Lt_of_mem_normalizer hg hgL)) hgN
    · exact (hS.conj_swap hg hgL).2
  have hJ : V.map t.toMonoidHom ∈ IrrPlus (conjAutSub t L ⊔ L) (⊤ : Subgroup W) := by
    rw [sup_comm, ← hS.hMp]
    refine irrPlus_map (fun x hx => hS.conj_mem_Mp hS.t_mem hx) (fun x hx => ?_) hS.hD.hyp.irr
    simpa using hS.conj_mem_Mp (M.inv_mem hS.t_mem) hx
  have hJU : V.map t.toMonoidHom ≤ commV (conjAutSub t L) := by
    rw [← map_commV_conjAutSub]
    exact Subgroup.map_mono (hS.V_le_commV hVt)
  have h := commV_le_sup_fixV hSzA hB45 hF hA21 hS.exp hS.hD.hyp.qsqtk hS.Lt_le hS.Lt_simp
    hS.Lt_quasi (hS.isSz_Lt hSz) hswap (hS.commV_Lt_le_fixV hVt) hS.hr hS.hr2 hS.hAQ
    (hS.le_normalizer_Lt hAN) hAc (mem_irrPlus_of_sup hJ (hS.map_le_fixV_L hVt hS.t_mem hS.htn))
    hJU
  rw [show conjAutSub t L ⊔ L = Mp by rw [sup_comm, hS.hMp]] at h
  have h2 := Subgroup.map_mono (f := (t⁻¹).toMonoidHom) h
  rw [map_commV_conjAutSub, conjAutSub_inv_conjAutSub, Subgroup.map_sup, Subgroup.map_map,
    map_fixV_conjAutSub, hS.conjAutSub_Mp (M.inv_mem hS.t_mem)] at h2
  have e : (t⁻¹).toMonoidHom.comp t.toMonoidHom = MonoidHom.id W := by
    ext w
    simp
  rw [e, Subgroup.map_id] at h2
  exact hS.not_le_orbSup hS.htop (h2.trans (sup_le_sup_right (le_orbSup T V) _))

theorem smul_tildeU_of_mem (hS : D321Sit M Mp T L V t A r) {g : MulAut W} (hg : g ∈ M)
    (hgL : g ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    letI := qAct hS.hD.hyp.Mp_normal
    (⟨g, hg⟩ : ↥M) • tilde Mp ⊤ (commV L) = tilde Mp ⊤ (commV L) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  rw [smul_tildeQ hS.hD.hyp.Mp_normal]
  congr 1
  show (commV L).map g.toMonoidHom = commV L
  rw [map_commV_conjAutSub, mem_normalizer_iff_conjAutSub.1 hgL]

theorem smul_tildeU_of_not_mem (hS : D321Sit M Mp T L V t A r) {g : MulAut W} (hg : g ∈ M)
    (hgL : g ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    letI := qAct hS.hD.hyp.Mp_normal
    (⟨g, hg⟩ : ↥M) • tilde Mp ⊤ (commV L) = (⟨t, hS.t_mem⟩ : ↥M) • tilde Mp ⊤ (commV L) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  rw [hS.smul_tildeU, smul_tildeQ hS.hD.hyp.Mp_normal]
  congr 1
  show (commV L).map g.toMonoidHom = commV (conjAutSub t L)
  rw [map_commV_conjAutSub, (hS.conj_swap hg hgL).1]

theorem isInv_tildeU (hS : D321Sit M Mp T L V t A r) :
    letI := qAct hS.hD.hyp.Mp_normal
    XMod.IsInv ↥(Mp.subgroupOf M) (tilde Mp ⊤ (commV L)) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  intro x q hq
  have hx : ((x : ↥M) : MulAut W) ∈ Mp := x.2
  have hxN : ((x : ↥M) : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mem_normalizer_iff.2 fun l =>
      ⟨fun hl => hS.conj_mem_L hx hl, fun hl => by
        have := hS.conj_mem_L (Mp.inv_mem hx) hl
        simpa [mul_assoc] using this⟩
  have h := hS.smul_tildeU_of_mem (x : ↥M).2 hxN
  rw [← h]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ hq

theorem card_inf_normalizer_le (hS : D321Sit M Mp T L V t A r)
    (hSzA : H13.SzTwoAutInnerFact) {n : ℕ} (hSz : IsSz n ↥L) {a₀ : MulAut W} (ha₀ : a₀ ∈ A)
    (ha₀N : a₀ ∉ Subgroup.normalizer (L : Set (MulAut W))) :
    Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set (MulAut W))) ≤
      2 ^ n * Nat.card ↥(A ⊓ Subgroup.centralizer (Mp : Set (MulAut W))) := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hS.elemAb.1
  have h1 := card_le_of_isSz hSzA hSz hS.hsimp hS.quasi
    (E := A ⊓ Subgroup.normalizer (L : Set (MulAut W))) inf_le_right
    (fun e he => hS.elemAb.2 e he.1)
  refine h1.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le ?_))
  rintro b ⟨⟨hbA, -⟩, hbL⟩
  refine ⟨hbA, ?_⟩
  have hswap := (hS.conj_swap (hS.A_le ha₀) ha₀N).1
  rw [hS.hMp]
  refine mem_centralizer_sup hbL (Subgroup.mem_centralizer_iff.2 fun y hy => ?_)
  rw [← hswap] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxb := (Subgroup.mem_centralizer_iff.1 hbL) x hx
  have hab := hAc a₀ ha₀ b hbA
  show (MulAut.conj a₀) x * b = b * (MulAut.conj a₀) x
  rw [MulAut.conj_apply]
  calc a₀ * x * a₀⁻¹ * b = a₀ * x * (a₀⁻¹ * b) := by group
    _ = a₀ * x * (b * a₀⁻¹) := by
        rw [show a₀⁻¹ * b = b * a₀⁻¹ by
          calc a₀⁻¹ * b = a₀⁻¹ * (b * a₀) * a₀⁻¹ := by group
            _ = a₀⁻¹ * (a₀ * b) * a₀⁻¹ := by rw [hab]
            _ = b * a₀⁻¹ := by group]
    _ = a₀ * (x * b) * a₀⁻¹ := by group
    _ = a₀ * (b * x) * a₀⁻¹ := by rw [hxb]
    _ = (a₀ * b) * x * a₀⁻¹ := by group
    _ = (b * a₀) * x * a₀⁻¹ := by rw [hab]
    _ = b * (a₀ * x * a₀⁻¹) := by group

theorem false_of_not_le_normalizer (hSzA : H13.SzTwoAutInnerFact)
    (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) {n : ℕ}
    (hSz : IsSz n ↥L)
    (hVrk : letI := qAct hS.hD.hyp.Mp_normal; 2 * n + 3 ≤ rk ↥(tilde Mp ⊤ V))
    (hAN : ¬ A ≤ Subgroup.normalizer (L : Set (MulAut W))) : False := by
  classical
  let _i := qAct hS.hD.hyp.Mp_normal
  obtain ⟨a₀, ha₀, ha₀N⟩ := Set.not_subset.1 hAN
  set A₀ := A ⊓ Subgroup.normalizer (L : Set (MulAut W)) with hA₀def
  set B := A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) with hBdef
  set U := tilde Mp ⊤ (commV L) with hUdef
  set tM : ↥M := ⟨t, hS.t_mem⟩ with htM
  set a₀M : ↥M := ⟨a₀, hS.A_le ha₀⟩ with ha₀Mdef
  set F := XMod.fixed ↥(B.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))
    with hFdef
  set Y := U ⊓ F with hYdef
  have hQ := hS.quot_sq
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hS.elemAb.1
  have hApg : IsPGroup 2 ↥A := hS.isPGroup
  have hBpg : IsPGroup 2 ↥B := hApg.to_le inf_le_left
  have hA₀pg : IsPGroup 2 ↥A₀ := hApg.to_le inf_le_left
  have hsplitA : ∀ x ∈ A, x ∈ A₀ ∨ a₀⁻¹ * x ∈ A₀ := by
    intro x hx
    by_cases hxN : x ∈ Subgroup.normalizer (L : Set (MulAut W))
    · exact Or.inl ⟨hx, hxN⟩
    · exact Or.inr ⟨A.mul_mem (A.inv_mem ha₀) hx,
        hS.inv_mul_mem_normalizer (hS.A_le ha₀) (hS.A_le hx) ha₀N hxN⟩
  have hrk : rk ↥A ≤ rk ↥B + n + 1 := by
    have h1 := SmithD310U.card_le_two_mul_of_split inf_le_left ha₀ hsplitA
    have h2 := hS.card_inf_normalizer_le hSzA hSz ha₀ ha₀N
    rw [card_eq_two_pow_of_isPGroup hApg, card_eq_two_pow_of_isPGroup hA₀pg] at h1
    rw [card_eq_two_pow_of_isPGroup hA₀pg, card_eq_two_pow_of_isPGroup hBpg, ← pow_add] at h2
    have h3 : 2 ^ rk ↥A ≤ 2 ^ (rk ↥B + n + 1) := by
      calc 2 ^ rk ↥A ≤ 2 * 2 ^ rk ↥A₀ := h1
        _ ≤ 2 * 2 ^ (n + rk ↥B) := Nat.mul_le_mul_left _ h2
        _ = 2 ^ (rk ↥B + n + 1) := by rw [← pow_succ']; ring_nf
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3
  have ha₀U : a₀M • U = tM • U := hS.smul_tildeU_of_not_mem (hS.A_le ha₀) ha₀N
  have hinf : U ⊓ a₀M • U = ⊥ := by rw [ha₀U]; exact hS.inf_tildeU hVt
  have hBM : B ≤ M := inf_le_left.trans hS.A_le
  have hBN : ∀ b ∈ B, ∀ x ∈ Mp, b * x = x * b := fun b hb x hx =>
    ((Subgroup.mem_centralizer_iff.1 hb.2) x hx).symm
  have hFA : ∀ a ∈ A.subgroupOf M, ∀ q ∈ F, a • q ∈ F := by
    intro a ha q hq
    refine XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩
    have hb : (((b : ↥M) : MulAut W)) ∈ B := b.2
    have hba : (b : ↥M) * a = a * b := Subtype.ext (hAc _ hb.1 _ ha)
    show (b : ↥M) • a • q = a • q
    rw [smul_smul, hba, mul_smul]
    exact congrArg (a • ·) ((XMod.mem_fixed.1 hq).2 b)
  have ha₀A : a₀M ∈ A.subgroupOf M := ha₀
  have ha₀F : a₀M • F = F := by
    ext q
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro h
      have h1 := hFA a₀M ha₀A _ h
      rwa [smul_inv_smul] at h1
    · intro h
      exact hFA _ ((A.subgroupOf M).inv_mem ha₀A) q h
  have hUA₀ : ∀ a ∈ A₀.subgroupOf M, ∀ q ∈ U, a • q ∈ U := by
    intro a ha q hq
    have ha' : ((a : ↥M) : MulAut W) ∈ A₀ := ha
    have h := hS.smul_tildeU_of_mem (a : ↥M).2 ha'.2
    rw [← hUdef] at h
    rw [← h]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  have hA₀A : A₀.subgroupOf M ≤ A.subgroupOf M := fun x hx =>
    (hx : ((x : ↥M) : MulAut W) ∈ A₀).1
  have hYA₀ : XMod.IsInv ↥(A₀.subgroupOf M) Y := fun a q hq =>
    ⟨hUA₀ a a.2 q hq.1, hFA a (hA₀A a.2) q hq.2⟩
  have hYdis : Y ⊓ a₀M • Y = ⊥ := by
    rw [hYdef, Subgroup.smul_inf, ha₀F]
    exact le_bot_iff.1 (le_trans (inf_le_inf inf_le_left inf_le_left) hinf.le)
  have hAcM : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hAc _ hx _ hy)
  have ha₀2 : a₀M ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hS.elemAb.2 _ ha₀)
  have hsplitM : ∀ x ∈ A.subgroupOf M, x ∈ A₀.subgroupOf M ∨ a₀M⁻¹ * x ∈ A₀.subgroupOf M :=
    fun x hx => hsplitA _ hx
  have hN2 := nB_index_two ha₀A ha₀2 hAcM hA₀A hsplitM hYA₀ hYdis
  have hYF : Y ⊔ a₀M • Y ≤ F := by
    refine sup_le inf_le_right ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hFA a₀M ha₀A y hy.2
  have hnB := nB_mono (A.subgroupOf M) hYF
  have hBA₀ : B ≤ A₀ := fun b hb => ⟨hb.1, Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (fun l hl => hS.L_le_Mp hl) hb.2)⟩
  have hBpgM : IsPGroup 2 ↥(B.subgroupOf M) := hBpg.of_equiv (Subgroup.subgroupOfEquivOfLe hBM).symm
  have hUB : ∀ b ∈ B.subgroupOf M, ∀ y ∈ U, b • y ∈ U := fun b hb y hy =>
    hUA₀ b (hBA₀ hb) y hy
  have hUne : U ≠ ⊥ := fun h =>
    hS.tilde_ne_bot (le_bot_iff.1 (h ▸ hS.tildeV_le_tildeU hVt))
  obtain ⟨y, hyU, hy1, hyB⟩ :=
    SmithD39Two.exists_mem_not_mem_of_lt hQ hBpgM (bot_lt_iff_ne_bot.2 hUne)
    (fun b _ q hq => by rw [Subgroup.mem_bot.1 hq, smul_one]; exact one_mem _) hUB
  have hyF : y ∈ F := XMod.mem_fixed.2 ⟨trivial, fun b => by
    have := hyB b b.2
    rw [Subgroup.mem_bot, mul_inv_eq_one] at this
    exact this⟩
  have hyY : y ∈ Y := ⟨hyU, hyF⟩
  have hYne : Y ≠ ⊥ := fun h => hy1 (h ▸ hyY)
  have hYinv : XMod.IsInv ↥(Mp.subgroupOf M) Y :=
    (hS.isInv_tildeU).inf (SmithD310U.isInv_fixed_of_comm fun b hb l hl =>
      Subtype.ext ((hBN _ hb _ hl)))
  have hdvd := SmithD310U.rk_dvd_of_isInv hQ hS.Λ_normal hS.irr hS.gen hYinv
  have hYpos : 0 < rk ↥Y := by
    rcases Nat.eq_zero_or_pos (rk ↥Y) with h | h
    · exact absurd ((rk_eq_zero_iff hQ).1 h) hYne
    · exact h
  have hVY : rk ↥(tilde Mp ⊤ V) ≤ rk ↥Y := Nat.le_of_dvd hYpos hdvd
  have hcount : nB (A.subgroupOf M) F < 2 * (rk ↥A - rk ↥B) ∨
      (B = ⊥ ∧ nB (A.subgroupOf M) F ≤ 2 * rk ↥A) := by
    by_cases hB1 : B = ⊥
    · right
      refine ⟨hB1, ?_⟩
      have hF : F = ⊤ := by
        rw [hFdef, eq_top_iff]
        intro q _
        refine XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩
        have key : ∀ x : MulAut W, x ∈ B → x = 1 := fun x hx => by
          rw [hB1, Subgroup.mem_bot] at hx
          exact hx
        have : (b : ↥M) = 1 := Subtype.ext (key _ b.2)
        show (b : ↥M) • q = q
        rw [this, one_smul]
      rw [hF]
      exact hS.nB_le
    · left
      have hUA : ¬ fixV B ≤ fixV A := by
        intro hle
        have hT1 := SmithD39Two.map_fixV_eq_fixed hS.hD.hyp.Mp_normal hBM hBN hS.commOf_eq
        have hyF' : y ∈ (fixV B).map (QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W))) := by
          rw [hT1]
          exact hyF
        obtain ⟨w, hw, hwy⟩ := hyF'
        have ha₀y : a₀M • y = y := by
          rw [← hwy]
          show QuotientGroup.mk (a₀ w) = QuotientGroup.mk w
          rw [(mem_fixV.1 (hle hw)) a₀ ha₀]
        have : y ∈ Y ⊓ a₀M • Y := ⟨hyY, by
          rw [← ha₀y]; exact Subgroup.smul_mem_pointwise_smul _ _ _ hyY⟩
        rw [hYdis] at this
        exact hy1 this
      exact SmithD39Two.nB_fixed_lt hS.hD.hyp.Mp_normal hS.exp hS.hAQ inf_le_left hB1 hUA hBM hBN
        hS.commOf_eq
  have hfin : rk ↥(tilde Mp ⊤ V) ≤ nB (A.subgroupOf M) F := by
    calc rk ↥(tilde Mp ⊤ V) ≤ rk ↥Y := hVY
      _ ≤ rk ↥Y + nB (A₀.subgroupOf M) Y := Nat.le_add_right _ _
      _ = nB (A.subgroupOf M) (Y ⊔ a₀M • Y) := hN2.symm
      _ ≤ nB (A.subgroupOf M) F := hnB
  have hBA : rk ↥B ≤ rk ↥A := rk_mono inf_le_left
  rcases hcount with h | ⟨hB1, h⟩
  · omega
  · have hB0 : rk ↥B = 0 := by rw [hB1, rk_bot]
    omega

end D321Sit

section SmallIndex

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q] [Finite Q]

theorem fix_of_nB_lt (hQ : ∀ q : Q, q ^ 2 = 1) {Λ A : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V)
    (hgen : (⨆ g : Γ, g • V) = ⊤) (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l = l * a) {S : Subgroup Q}
    (hS : XMod.IsInv ↥Λ S) (hlt : nB A S < rk ↥V) : ∀ a ∈ A, ∀ s ∈ S, a • s = s := by
  intro a ha
  obtain ⟨Sa, hSa⟩ : ∃ Sa : Subgroup Q,
      Sa = S ⊓ XMod.fixed ↥(Subgroup.zpowers a) (⊤ : Subgroup Q) := ⟨_, rfl⟩
  have hzΛ : ∀ e ∈ Subgroup.zpowers a, ∀ l ∈ Λ, e * l = l * e := by
    intro e he l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact ((Commute.zpow_left (hAΛ a ha l hl) k))
  have hSaΛ : XMod.IsInv ↥Λ Sa := hSa ▸ hS.inf (SmithD310U.isInv_fixed_of_comm hzΛ)
  have h1 := SmithD310U.rk_dvd_of_isInv hQ hΛ hV hgen hS
  have h2 := SmithD310U.rk_dvd_of_isInv hQ hΛ hV hgen hSaΛ
  have hle : S ⊓ XMod.fixed ↥A (⊤ : Subgroup Q) ≤ Sa :=
    hSa ▸ inf_le_inf_left _ (SmithD39Two.fixed_anti ((Subgroup.zpowers_le).2 ha))
  have hSaS' : Sa ≤ S := hSa ▸ inf_le_left
  have h3 := rk_mono hle
  have h4 := rk_mono hSaS'
  have h5 : rk ↥S - rk ↥Sa < rk ↥V := by
    unfold nB at hlt
    omega
  have h6 : rk ↥V ∣ rk ↥S - rk ↥Sa := Nat.dvd_sub h1 h2
  have h7 : rk ↥S - rk ↥Sa = 0 := Nat.eq_zero_of_dvd_of_lt h6 h5
  have hrkeq : rk ↥Sa = rk ↥S := by omega
  have hcard : Nat.card ↥Sa = Nat.card ↥S := by
    rw [card_eq_two_pow hQ Sa, card_eq_two_pow hQ S, hrkeq]
  have hSaS : Sa = S := Subgroup.eq_of_le_of_card_ge hSaS' hcard.ge
  intro s hs
  rw [← hSaS, hSa] at hs
  exact SmithD39Two.mem_fixed_zpowers_iff.1 hs.2

end SmallIndex

namespace D321Sit

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ}

theorem fix_fixed_of_rk_lt (hS : D321Sit M Mp T L V t A r)
    (hAC : A ≤ Subgroup.centralizer (Mp : Set (MulAut W))) {B : Subgroup (MulAut W)}
    (hBA : B ≤ A)
    (hrk : letI := qAct hS.hD.hyp.Mp_normal; 2 * (rk ↥A - rk ↥B) < rk ↥(tilde Mp ⊤ V)) :
    letI := qAct hS.hD.hyp.Mp_normal
    ∀ a ∈ A.subgroupOf M, ∀ q ∈ XMod.fixed ↥(B.subgroupOf M)
      (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))), a • q = q := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hBM : B ≤ M := hBA.trans hS.A_le
  have hBN : ∀ b ∈ B, ∀ x ∈ Mp, b * x = x * b := fun b hb x hx =>
    ((Subgroup.mem_centralizer_iff.1 (hAC (hBA hb))) x hx).symm
  have hAΛ : ∀ a ∈ A.subgroupOf M, ∀ l ∈ Mp.subgroupOf M, a * l = l * a := fun a ha l hl =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.1 (hAC ha)) _ hl).symm
  have hSinv : XMod.IsInv ↥(Mp.subgroupOf M)
      (XMod.fixed ↥(B.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W)))) :=
    SmithD310U.isInv_fixed_of_comm fun b hb l hl => Subtype.ext (hBN _ hb _ hl)
  by_cases hUA : fixV B ≤ fixV A
  · intro a ha q hq
    rw [← SmithD39Two.map_fixV_eq_fixed hS.hD.hyp.Mp_normal hBM hBN hS.commOf_eq] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    show QuotientGroup.mk ((a : MulAut W) w) = QuotientGroup.mk w
    exact congrArg QuotientGroup.mk ((mem_fixV.1 (hUA hw)) _ ha)
  · refine fix_of_nB_lt hS.quot_sq hS.Λ_normal hS.irr hS.gen hAΛ hSinv ?_
    by_cases hB1 : B = ⊥
    · have hF : XMod.fixed ↥(B.subgroupOf M)
          (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) = ⊤ := by
        rw [eq_top_iff]
        intro q _
        refine XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩
        have key : ∀ x : MulAut W, x ∈ B → x = 1 := fun x hx => by
          rw [hB1, Subgroup.mem_bot] at hx
          exact hx
        have : (b : ↥M) = 1 := Subtype.ext (key _ b.2)
        show (b : ↥M) • q = q
        rw [this, one_smul]
      rw [hF]
      have h1 := hS.nB_le
      have h2 : rk ↥B = 0 := by rw [hB1, rk_bot]
      omega
    · have h1 := SmithD39Two.nB_fixed_lt hS.hD.hyp.Mp_normal hS.exp hS.hAQ hBA hB1 hUA hBM hBN
        hS.commOf_eq
      omega

theorem le_centralizer_of_odd (hS : D321Sit M Mp T L V t A r)
    (hAC : A ≤ Subgroup.centralizer (Mp : Set (MulAut W)))
    (hV2 : letI := qAct hS.hD.hyp.Mp_normal; 2 < rk ↥(tilde Mp ⊤ V))
    {X : Subgroup (MulAut W)} (hXM : X ≤ M)
    (hXN : X ≤ Subgroup.centralizer (Mp : Set (MulAut W)))
    (hXA : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X) (hXodd : Odd (Nat.card ↥X)) :
    A ≤ Subgroup.centralizer (X : Set (MulAut W)) := by
  classical
  let _i := qAct hS.hD.hyp.Mp_normal
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hS.elemAb.1
  let act : MulDistribMulAction ↥A ↥X :=
    { smul := fun a x => ⟨(a : MulAut W) * x * (a : MulAut W)⁻¹, hXA _ a.2 _ x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : ↥A) : MulAut W) * x * ((1 : ↥A) : MulAut W)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : ↥A) : MulAut W) * x * ((a * b : ↥A) : MulAut W)⁻¹ =
          (a : MulAut W) * ((b : MulAut W) * x * (b : MulAut W)⁻¹) * (a : MulAut W)⁻¹
        rw [Subgroup.coe_mul]
        group)
      smul_mul := fun a x y => Subtype.ext (by
        show (a : MulAut W) * ((x * y : ↥X) : MulAut W) * (a : MulAut W)⁻¹ =
          ((a : MulAut W) * x * (a : MulAut W)⁻¹) * ((a : MulAut W) * y * (a : MulAut W)⁻¹)
        rw [Subgroup.coe_mul]
        group)
      smul_one := fun a => Subtype.ext (by
        show (a : MulAut W) * ((1 : ↥X) : MulAut W) * (a : MulAut W)⁻¹ = 1
        simp) }
  have hact : ∀ (a : ↥A) (x : ↥X), ((a • x : ↥X) : MulAut W) =
      (a : MulAut W) * x * (a : MulAut W)⁻¹ := fun _ _ => rfl
  have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).2 hS.isA2.ne_bot
  have : IsElementaryAbelian 2 ↥A :=
    { is_comm := ⟨fun a b => Subtype.ext (hAc _ a.2 _ b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by rw [Subgroup.coe_pow]; exact hS.elemAb.2 _ a.2) }
  have hp : ¬ 2 ∣ Nat.card ↥X := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hXodd
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (A := ↥A) (p := 2) (H := ↥X) hp
  by_contra hcon
  obtain ⟨B, hB, hBmov⟩ : ∃ B : Subgroup ↥A, B.index = 2 ∧
      ¬ ∀ y ∈ CFSG.fixedPointSubgroup ↥B ↥X, ∀ a : ↥A, a • y = y := by
    by_contra h
    push Not at h
    apply hcon
    have hle : (⊤ : Subgroup ↥X) ≤ CFSG.fixedPointSubgroup ↥A ↥X := by
      rw [← hgen]
      exact iSup₂_le fun B hB y hy a => h B hB y hy a
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : (⟨a, ha⟩ : ↥A) • (⟨x, hx⟩ : ↥X) = ⟨x, hx⟩ := hle (Subgroup.mem_top _) ⟨a, ha⟩
    have h2 := congrArg Subtype.val h1
    rw [hact] at h2
    calc x * a = (a * x * a⁻¹) * a := by rw [h2]
      _ = a * x := by group
  set B' : Subgroup (MulAut W) := B.map A.subtype with hB'
  have hB'A : B' ≤ A := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hcardB : Nat.card ↥B' = Nat.card ↥B := Subgroup.card_map_of_injective A.subtype_injective
  have hApg : IsPGroup 2 ↥A := hS.isPGroup
  have hB'pg : IsPGroup 2 ↥B' := hApg.to_le hB'A
  have hrk : rk ↥A = rk ↥B' + 1 := by
    have h1 : Nat.card ↥A = 2 * Nat.card ↥B := by
      rw [← hB, mul_comm, Subgroup.card_mul_index]
    rw [← hcardB, card_eq_two_pow_of_isPGroup hApg, card_eq_two_pow_of_isPGroup hB'pg,
      ← pow_succ'] at h1
    exact Nat.pow_right_injective le_rfl h1
  have hGL := hS.fix_fixed_of_rk_lt hAC hB'A (by omega)
  apply hBmov
  intro y hy a
  have hyX : (y : MulAut W) ∈ X := y.2
  have hyB : ∀ b ∈ B', (y : MulAut W) * b = b * y := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : b • y = y := hy ⟨b, hb⟩
    have h2 := congrArg Subtype.val h1
    rw [hact] at h2
    calc (y : MulAut W) * (A.subtype b) = ((b : MulAut W) * y * (b : MulAut W)⁻¹) * b := by
          rw [h2]; rfl
      _ = A.subtype b * y := by simp
  set c : MulAut W := (y : MulAut W) * a * (y : MulAut W)⁻¹ * (a : MulAut W)⁻¹ with hc
  have hcX : c ∈ X := by
    have : (a : MulAut W) * (y : MulAut W)⁻¹ * (a : MulAut W)⁻¹ ∈ X :=
      hXA _ a.2 _ (X.inv_mem hyX)
    have h2 := X.mul_mem hyX this
    rwa [← mul_assoc, ← mul_assoc] at h2
  have hcM : c ∈ M := hXM hcX
  have hcN : ∀ x ∈ Mp, c * x = x * c := fun x hx =>
    ((Subgroup.mem_centralizer_iff.1 (hXN hcX)) x hx).symm
  have hck : c ^ Nat.card ↥X = 1 := by
    have h1 : (⟨c, hcX⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hcB : ∀ b ∈ B', c * b = b * c := by
    intro b hb
    have hy : Commute (y : MulAut W) b := hyB b hb
    have ha : Commute (a : MulAut W) b := hAc _ a.2 _ (hB'A hb)
    exact (((hy.mul_left ha).mul_left hy.inv_left).mul_left ha.inv_left)
  set yM : ↥M := ⟨y, hXM hyX⟩ with hyM
  set aM : ↥M := ⟨a, hS.A_le a.2⟩ with haM
  have haMA : aM ∈ A.subgroupOf M := a.2
  have hcfix : ∀ q ∈ XMod.fixed ↥(B'.subgroupOf M)
      (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))), (⟨c, hcM⟩ : ↥M) • q = q := by
    intro q hq
    have hceq : (⟨c, hcM⟩ : ↥M) = yM * aM * yM⁻¹ * aM⁻¹ := Subtype.ext rfl
    rw [hceq, mul_smul, mul_smul, mul_smul, hGL _ ((A.subgroupOf M).inv_mem haMA) q hq]
    have hyq : yM⁻¹ • q ∈ XMod.fixed ↥(B'.subgroupOf M)
        (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) := by
      refine XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩
      have hb : ((b : ↥M) : MulAut W) ∈ B' := b.2
      have hcomm : (b : ↥M) * yM⁻¹ = yM⁻¹ * b := Subtype.ext (by
        show ((b : ↥M) : MulAut W) * (y : MulAut W)⁻¹ = (y : MulAut W)⁻¹ * b
        exact ((Commute.inv_left (hyB _ hb)).eq).symm)
      show (b : ↥M) • yM⁻¹ • q = yM⁻¹ • q
      rw [smul_smul, hcomm, mul_smul]
      exact congrArg (yM⁻¹ • ·) ((XMod.mem_fixed.1 hq).2 b)
    rw [hGL aM haMA _ hyq, smul_inv_smul]
  have hc1 := SmithD39Two.eq_one_of_fix_fixed hS.hD.hyp.Mp_normal hS.exp hS.commV_eq_top
    (hB'A.trans hS.A_le) hB'pg hcM hcN hXodd hck hcB hcfix
  apply Subtype.ext
  rw [hact]
  have h1 : (y : MulAut W) * a = a * y := by
    calc (y : MulAut W) * a = c * (a * y) := by rw [hc]; group
      _ = a * y := by rw [hc1, one_mul]
  calc (a : MulAut W) * y * (a : MulAut W)⁻¹ = y * a * (a : MulAut W)⁻¹ := by rw [h1]
    _ = y := by group

theorem false_of_le_cent (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hS : D321Sit M Mp T L V t A r)
    (hAC : A ≤ Subgroup.centralizer (Mp : Set (MulAut W)))
    (hV2 : letI := qAct hS.hD.hyp.Mp_normal; 2 < rk ↥(tilde Mp ⊤ V))
    (hK3 : ∀ K : Subgroup (MulAut W), K ∈ cComp M → CFSG.IsQuasisimple ↥K →
      K ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) →
      3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) → A ≤ Subgroup.centralizer (K : Set (MulAut W))) :
    False := by
  set C := M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) with hC
  have hAC' : A ≤ C := le_inf hS.A_le hAC
  rcases SmithD39Two.exists_moved_piece (pCoreOf_two_cent_eq_bot hS.hD) hAC' hS.isPGroup
      hS.isA2.ne_bot hS.hD.hyp.Mp_normal with ⟨p, hp, hp2, hX⟩ | ⟨K, hK, hKq, hKC, hKA⟩
  ·
    have : Fact p.Prime := ⟨hp⟩
    set X := CFSG.Open.pCoreOf p C with hXdef
    have hXC : X ≤ C := CFSG.LieType.BorelTits.pCoreOf_le (r := p) C
    have hXA : ∀ a ∈ A, ∀ x ∈ X, a * x * a⁻¹ ∈ X := by
      intro a ha x hx
      have haN : a ∈ Subgroup.normalizer (C : Set (MulAut W)) :=
        Subgroup.le_normalizer (hAC' ha)
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := p) C haN) x).1 hx
    have hXodd : Odd (Nat.card ↥X) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).1
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := p) C)
      rw [hk]
      exact Odd.pow (hp.odd_of_ne_two hp2)
    have h := hS.le_centralizer_of_odd hAC hV2 (hXC.trans inf_le_left) (hXC.trans inf_le_right)
      hXA hXodd
    apply hX
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.1 (h ha)) x hx).symm
  ·
    by_cases h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)
    · exact hKA (hK3 K hK hKq hKC h3)
    · have hSz := SmithD39Two.suzukiModel_of_le hA23 hSzF hS.hD.hyp.qsqtk
        (hKC.trans inf_le_left) hKq h3
      exact hKA (SmithD39Two.sz_comp_le_centralizer h38 hS.exp hS.hD.hyp.qsqtk
        hS.hD.hyp.Mp_normal hS.Mp_le hS.Mp_perfect hS.commV_eq_top hS.hr hS.hr2 hS.hAQ hK hKq
        (hKC.trans inf_le_right) hSz)

theorem false_of_sz_of_comp (hSzA : H13.SzTwoAutInnerFact)
    (hB45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1) (hA21 : AsA21SQTKSection) (h38 : D38Top)
    (hA23 : A23SQTKListFact) (hSzF : H13.SimpleThreePrimeSuzukiFact)
    (hS : D321Sit M Mp T L V t A r) (hVt : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) {n : ℕ}
    (hSz : IsSz n ↥L)
    (hVrk : letI := qAct hS.hD.hyp.Mp_normal; 2 * n + 3 ≤ rk ↥(tilde Mp ⊤ V))
    (hK3 : A ≤ Subgroup.centralizer (Mp : Set (MulAut W)) →
      ∀ K : Subgroup (MulAut W), K ∈ cComp M → CFSG.IsQuasisimple ↥K →
      K ≤ M ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) →
      3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) → A ≤ Subgroup.centralizer (K : Set (MulAut W))) :
    False := by
  by_cases hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W))
  · by_cases hAL : A ≤ Subgroup.centralizer (L : Set (MulAut W))
    · by_cases hALt : A ≤ Subgroup.centralizer (conjAutSub t L : Set (MulAut W))
      · have hAC : A ≤ Subgroup.centralizer (Mp : Set (MulAut W)) := by
          intro a ha
          rw [hS.hMp]
          exact mem_centralizer_sup (hAL ha) (hALt ha)
        exact hS.false_of_le_cent h38 hA23 hSzF hAC (by omega) (hK3 hAC)
      · exact hS.false_of_le_normalizer_Lt hSzA hB45 hF hA21 hVt hSz hAN hALt
    · exact hS.false_of_le_normalizer_L hSzA hB45 hF hA21 hVt hSz hAN hAL
  · exact hS.false_of_not_le_normalizer hSzA hVt hSz hVrk hAN

end D321Sit

end CFSG.Quasithin.SmithD321
