module

public import CFSG.RankThree.S4Free.Stellmacher29
public import CFSG.Quasithin.Background.B1MoreQuot
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LocalAnalysis.EvenBN.Tits.N.P3ThCount
import CFSG.Blueprint.SourceSuzukiTransport
import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.SignalizerFunctorTheorem.McBride.Models.SchurFamilies.Even
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.S4Free.Stellmacher24Ext
public import CFSG.RankThree.S4Free.StellmacherSzSylow
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs

public section

namespace CFSG.RankThree.S4Free.Stell

open Subgroup CFSG.Quasithin CFSG.Blueprint Suzuki

section L24Sz

variable {H : Type*} [Group H] [Finite H] {S M A L : Subgroup H}

theorem inf_le_oTwo_of_odd (hA : CFSG.Open.IsElemAbelian 2 A) {R : Subgroup L} [R.Normal]
    (hodd : ¬ 2 ∣ (oTwo ↥L).relIndex R) : R ⊓ A.subgroupOf L ≤ oTwo ↥L := by
  rintro g ⟨hgR, hgA⟩
  set ψ := QuotientGroup.mk' (oTwo ↥L) with hψ
  have hcard : ¬ 2 ∣ Nat.card (R.map ψ) := by
    rwa [← relIndex_ker, hψ, QuotientGroup.ker_mk']
  have hg2 : g ^ 2 = 1 := Subtype.ext (by simpa using hA.2 _ hgA)
  have h1 : ψ g = 1 :=
    eq_one_of_sq_eq_one_of_odd hcard (mem_map_of_mem ψ hgR) (by rw [← map_pow, hg2, map_one])
  rwa [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

theorem suzukiGroup_exists_mul_ne {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x y : suzukiGroup a K, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hnt, -⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
  have hbot : commutator (suzukiGroup a K) = ⊥ := by
    rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [mem_centralizer_iff]
    intro y _
    exact hcon y x
  obtain ⟨w, hw⟩ := exists_ne (1 : suzukiGroup a K)
  have hw' : w ∈ (⊥ : Subgroup (suzukiGroup a K)) := by
    rw [← hbot, (CFSG.LieType.Ree.suzuki_perfect ha hK).1]
    exact mem_top w
  exact hw (mem_bot.mp hw')

theorem IsL24Sz.sup_conj_subgroupOf (h : IsL24Sz S M A L) {x : H} (hxL : x ∈ L) (hxM : x ∉ M) :
    A.subgroupOf L ⊔ (A.subgroupOf L).map (MulAut.conj (⟨x, hxL⟩ : L)).toMonoidHom = ⊤ := by
  apply map_injective L.subtype_injective
  rw [Subgroup.map_sup, map_map_conj, subgroupOf_map_subtype, inf_of_le_left h.le,
    ← MonoidHom.range_eq_map, range_subtype]
  exact h.sup_conj x hxL hxM

theorem IsL24Sz.le_of_suzuki (h : IsL24Sz S M A L)
    {R : Subgroup L} [R.Normal] {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : ↥L ⧸ R ≃* suzukiGroup a K)
    (hA : CFSG.Open.IsElemAbelian 2 A) : R.map L.subtype ≤ M := by
  rintro _ ⟨r, hr, rfl⟩
  by_contra hrM
  set φ : ↥L →* suzukiGroup a K := e.toMonoidHom.comp (QuotientGroup.mk' R) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective R)
  have hker : R ≤ φ.ker := fun g hg => by
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff g).mpr hg, map_one]
  have hAr : (A.subgroupOf L).map (MulAut.conj r).toMonoidHom ≤ A.subgroupOf L ⊔ R := by
    rintro _ ⟨b, hb, rfl⟩
    have hrb : r * b * r⁻¹ * b⁻¹ ∈ R := by
      rw [show r * b * r⁻¹ * b⁻¹ = r * (b * r⁻¹ * b⁻¹) by group]
      exact R.mul_mem hr ((inferInstance : R.Normal).conj_mem _ (R.inv_mem hr) b)
    have : (MulAut.conj r).toMonoidHom b = (r * b * r⁻¹ * b⁻¹) * b := by
      simp [MulAut.conj_apply]
    rw [this]
    exact mul_mem (mem_sup_right hrb) (mem_sup_left hb)
  have htop : (⊤ : Subgroup L) ≤ A.subgroupOf L ⊔ R := by
    rw [← h.sup_conj_subgroupOf r.2 hrM]
    exact sup_le le_sup_left hAr
  have hφA : ∀ y : suzukiGroup a K, y ∈ (A.subgroupOf L).map φ := by
    intro y
    obtain ⟨l, rfl⟩ := hφs y
    have hl := htop (mem_top l)
    have hle : A.subgroupOf L ⊔ R ≤ ((A.subgroupOf L).map φ).comap φ :=
      sup_le (le_comap_map φ _) (hker.trans (φ.ker_le_comap _))
    exact hle hl
  obtain ⟨x, y, hxy⟩ := suzukiGroup_exists_mul_ne ha hK
  apply hxy
  obtain ⟨x', hx', rfl⟩ := hφA x
  obtain ⟨y', hy', rfl⟩ := hφA y
  rw [← map_mul, ← map_mul, isElemAbelian_comm (isElemAbelian_subgroupOf hA) hx' hy']

theorem IsL24Sz.exists_mem_not_mem_oTwo (h : IsL24Sz S M A L)
    (hA : CFSG.Open.IsElemAbelian 2 A) : ∃ a ∈ A, a ∉ (oTwo ↥L).map L.subtype := by
  by_contra hcon
  push Not at hcon
  have h4 := h.four_le hA
  have h1 : ((oTwo ↥L).map L.subtype).relIndex A = 1 := relIndex_eq_one.mpr fun a ha => hcon a ha
  omega

theorem IsL24Sz.exists_conj_not_mem (h : IsL24Sz S M A L)
    (hA : CFSG.Open.IsElemAbelian 2 A) {a : H} (haA : a ∈ A)
    (haO : a ∉ (oTwo ↥L).map L.subtype) : ∃ y ∈ L, y * a * y⁻¹ ∉ M := by
  obtain ⟨R, hRn, hOR, hodd, b, hb, K, _, _, hK, ⟨e⟩⟩ := h.suzuki
  by_contra hcon
  push Not at hcon
  have haL : a ∈ L := h.le haA
  set a' : ↥L := ⟨a, haL⟩ with ha'
  set φ : ↥L →* suzukiGroup b K := e.toMonoidHom.comp (QuotientGroup.mk' R) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective R)
  have hker : φ.ker = R := by
    ext g
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have haR : a' ∉ R := fun haR => haO ⟨a', inf_le_oTwo_of_odd hA hodd ⟨haR, haA⟩, rfl⟩
  have hφa : φ a' ≠ 1 := fun h1 => haR (hker ▸ MonoidHom.mem_ker.mpr h1)
  obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple hb hK
  have htop : normalClosure ({φ a'} : Set (suzukiGroup b K)) = ⊤ := by
    rcases (normalClosure_normal (s := ({φ a'} : Set (suzukiGroup b K)))).eq_bot_or_eq_top
      with h1 | h1
    · exact absurd (h1 ▸ subset_normalClosure (Set.mem_singleton _)) (by simpa using hφa)
    · exact h1
  have hN : normalClosure ({a'} : Set ↥L) ≤ M.subgroupOf L := by
    rw [normalClosure, closure_le]
    intro c hc
    obtain ⟨d, hd, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    rw [Set.mem_singleton_iff] at hd
    subst hd
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    rw [SetLike.mem_coe, mem_subgroupOf]
    simpa using hcon g g.2
  have hsup : normalClosure ({a'} : Set ↥L) ⊔ R = ⊤ := by
    rw [← hker, ← comap_map_eq, map_normalClosure _ _ hφs, Set.image_singleton, htop, comap_top]
  have hRM : R ≤ M.subgroupOf L := fun g hg =>
    mem_subgroupOf.mpr (h.le_of_suzuki hb hK e hA ⟨g, hg, rfl⟩)
  apply h.not_le
  intro l hl
  have hle : (⊤ : Subgroup L) ≤ M.subgroupOf L := hsup ▸ sup_le hN hRM
  exact mem_subgroupOf.mp (hle (mem_top (⟨l, hl⟩ : L)))

theorem IsL24Sz.exists_sup_zpowers_eq (h : IsL24Sz S M A L)
    (hA : CFSG.Open.IsElemAbelian 2 A) {a : H} (haA : a ∈ A)
    (haO : a ∉ (oTwo ↥L).map L.subtype) : ∃ y ∈ L, A ⊔ Subgroup.zpowers (y * a * y⁻¹) = L := by
  obtain ⟨y, hyL, hyM⟩ := h.exists_conj_not_mem hA haA haO
  refine ⟨y, hyL, h.eq_of_le (sup_le h.le ?_) le_sup_left fun hM =>
    hyM (hM (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))⟩
  exact Subgroup.zpowers_le.mpr (L.mul_mem (L.mul_mem hyL (h.le haA)) (L.inv_mem hyL))

end L24Sz

variable {V : Type*} [CommGroup V]

structure Hyp25Sz (S M A L : Subgroup (MulAut V)) (Z₀ W : Subgroup V) : Prop where
  isL24Sz : IsL24Sz S M A L
  isPGroup : IsPGroup 2 S
  le_M : S ≤ M
  elemAb : CFSG.Open.IsElemAbelian 2 A
  quadratic : IsQuadratic A
  le_fixV : Z₀ ≤ fixV A
  le_W : Z₀ ≤ W
  le_stabSub : L ≤ stabSub W
  gen : ∀ U : Subgroup V, (∀ l ∈ L, Z₀.map l.toMonoidHom ≤ U) → W ≤ U
  normalizer_le : ∀ l ∈ L, Z₀.map l.toMonoidHom = Z₀ → l ∈ M

namespace Hyp25Sz

variable [Finite V] {S M A L : Subgroup (MulAut V)} {Z₀ W : Subgroup V}

theorem setting (h : Hyp25Sz S M A L Z₀ W) : Setting25 A L Z₀ W where
  le_L := h.isL24Sz.le
  quad := (commSub_mono le_top le_rfl).trans ((commV_eq_commSub A).symm.le.trans h.quadratic)
  le_fixV := h.le_fixV
  le_W := h.le_W
  le_stabSub := h.le_stabSub
  gen := h.gen

theorem fixV_eq (hV : ∀ v : V, v ^ 2 = 1) (h : Hyp25Sz S M A L Z₀ W)
    {a : MulAut V} (haA : a ∈ A) (haO : a ∉ (oTwo ↥L).map L.subtype) :
    W ⊓ fixV A = W ⊓ fixV (Subgroup.zpowers a) ∧
      commSub W (Subgroup.zpowers a) ⊔ (W ⊓ fixV L) = W ⊓ fixV A ∧
      commSub W A ⊔ (W ⊓ fixV L) = W ⊓ fixV A ∧
      commSub W (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥ ∧
      2 * rk ↥(commSub W (Subgroup.zpowers a)) = mRel (W ⊓ fixV L) W := by
  obtain ⟨y, hyL, hy⟩ := h.isL24Sz.exists_sup_zpowers_eq h.elemAb haA haO
  obtain ⟨k1, k2, k3, k4, k5⟩ := h.setting.key hV haA hyL hy
  have haL : a ∈ L := h.isL24Sz.le haA
  have hs := rk_commSub_add_rk_inf_fixV (h.setting.mem_stabSub haL)
  have hm := mRel_add_rk_of_le (inf_le_left : W ⊓ fixV L ≤ W)
  have hfa : W ⊓ fixV A = W ⊓ fixV (Subgroup.zpowers a) := k1.trans (k2.trans k3)
  refine ⟨hfa, k3.trans hfa.symm, k1.symm, k4, ?_⟩
  rw [← hfa] at hs
  omega

theorem sup_fixV_conj_eq (hV : ∀ v : V, v ^ 2 = 1)
    (h : Hyp25Sz S M A L Z₀ W) {x : MulAut V} (hxL : x ∈ L) (hxM : x ∉ M) :
    (W ⊓ fixV A) ⊔ (W ⊓ fixV (A.map (MulAut.conj x).toMonoidHom)) = W := by
  obtain ⟨a, haA, haO⟩ := h.isL24Sz.exists_mem_not_mem_oTwo h.elemAb
  obtain ⟨y, hyL, hy⟩ := h.isL24Sz.exists_sup_zpowers_eq h.elemAb haA haO
  obtain ⟨-, -, -, -, k5⟩ := h.setting.key hV haA hyL hy
  exact h.setting.sup_fixV_conj hV k5 hxL (h.isL24Sz.sup_conj x hxL hxM)

theorem mem_of_comm_mem (hV : ∀ v : V, v ^ 2 = 1)
    (h : Hyp25Sz S M A L Z₀ W) {a x : MulAut V} (haA : a ∈ A)
    (haO : a ∉ (oTwo ↥L).map L.subtype) (hxL : x ∈ L) (hxM : x ∉ M) {w : V} (hw : w ∈ W)
    (hc : (a * (x * a * x⁻¹)) w * w⁻¹ ∈ W ⊓ fixV L) : w ∈ W ⊓ fixV L := by
  obtain ⟨b1, -, -, b4, -⟩ := h.fixV_eq hV haA haO
  exact h.setting.mem_of_comm_mem haA hxL (h.isL24Sz.sup_conj x hxL hxM) b1.symm b4 hw hc

theorem eq_of_commSub_le (hV : ∀ v : V, v ^ 2 = 1)
    (h : Hyp25Sz S M A L Z₀ W) {a : MulAut V} (haA : a ∈ A)
    (haO : a ∉ (oTwo ↥L).map L.subtype) {U₁ U₂ : Subgroup V} (hCU : W ⊓ fixV L ≤ U₂)
    (h21 : U₂ ≤ U₁) (h1W : U₁ ≤ W) (hU₁ : L ≤ stabSub U₁) (hU₂ : L ≤ stabSub U₂)
    (hc : commSub U₁ (Subgroup.zpowers a) ≤ U₂) : U₁ = U₂ := by
  obtain ⟨b1, -, -, b4, -⟩ := h.fixV_eq hV haA haO
  obtain ⟨x, hxL, hxM⟩ := Set.not_subset.mp h.isL24Sz.not_le
  exact h.setting.eq_of_commSub_le hV haA hxL (h.isL24Sz.sup_conj x hxL hxM) b1.symm b4 hCU h21
    h1W hU₁ hU₂ hc

end Hyp25Sz

section Sections

variable [Finite V]

theorem Setting25.mem_of_comm_mem_section (hV : ∀ v : V, v ^ 2 = 1) {A L : Subgroup (MulAut V)}
    {Z₀ W : Subgroup V} (h : Setting25 A L Z₀ W) {a x : MulAut V} (haA : a ∈ A) (hxL : x ∈ L)
    (hx : A ⊔ A.map (MulAut.conj x).toMonoidHom = L)
    (hfix : W ⊓ fixV (Subgroup.zpowers a) = W ⊓ fixV A)
    (hbot : commSub W (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥) {U₁ U₂ : Subgroup V}
    (hCU : W ⊓ fixV L ≤ U₂) (h21 : U₂ ≤ U₁) (h1W : U₁ ≤ W) (hU₁ : L ≤ stabSub U₁)
    (hU₂ : L ≤ stabSub U₂) {w : V} (hw : w ∈ U₁) (hwa : a w * w⁻¹ ∈ U₂) :
    w ∈ (U₁ ⊓ fixV (Subgroup.zpowers a)) ⊔ U₂ := by
  have haL : a ∈ L := h.le_L haA
  have hdec : ∀ U : Subgroup V, W ⊓ fixV L ≤ U → U ≤ W → L ≤ stabSub U →
      commSub U (Subgroup.zpowers a) ⊔ (W ⊓ fixV L) = U ⊓ fixV (Subgroup.zpowers a) := by
    intro U hCU' hUW hUL
    have h2 := h.two_mul_rk_inf_fixV hV haA hxL hx hfix hbot hCU' hUW hUL
    have h3 := rk_commSub_add_rk_inf_fixV (hUL haL)
    have hb : commSub U (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right _ (commSub_mono hUW le_rfl)).trans hbot.le)
    have h4 := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers a)) (W ⊓ fixV L)
    rw [hb, rk_bot] at h4
    have hle : commSub U (Subgroup.zpowers a) ⊔ (W ⊓ fixV L) ≤ U ⊓ fixV (Subgroup.zpowers a) := by
      refine sup_le (le_inf (commSub_le_of_invariant fun g hg u hu => ?_) ?_) (le_inf hCU' ?_)
      · exact ((hUL (Subgroup.zpowers_le.mpr haL hg)) u).mpr hu
      · exact (commSub_mono hUW (Subgroup.zpowers_le.mpr haA)).trans
          (h.quad.trans (fixV_le_fixV_of_le (Subgroup.zpowers_le.mpr haA)))
      · exact inf_le_right.trans (fixV_le_fixV_of_le (Subgroup.zpowers_le.mpr haL))
    refine eq_of_le_of_rk_le hV hle ?_
    omega
  have hwa1 : a w * w⁻¹ ∈ commSub U₁ (Subgroup.zpowers a) :=
    Subgroup.subset_closure ⟨a, Subgroup.mem_zpowers a, w, hw, rfl⟩
  have hwafix : a w * w⁻¹ ∈ fixV (Subgroup.zpowers a) :=
    (commSub_mono h1W (Subgroup.zpowers_le.mpr haA)).trans
      (h.quad.trans (fixV_le_fixV_of_le (Subgroup.zpowers_le.mpr haA))) hwa1
  have hmem : a w * w⁻¹ ∈ commSub U₂ (Subgroup.zpowers a) ⊔ (W ⊓ fixV L) := by
    rw [hdec U₂ hCU (h21.trans h1W) hU₂]
    exact mem_inf.mpr ⟨hwa, hwafix⟩
  obtain ⟨y, hy, c, hc, hyc⟩ := Subgroup.mem_sup.mp hmem
  have hc1 : c = 1 := by
    have hc' : c ∈ commSub U₁ (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) := by
      refine mem_inf.mpr ⟨?_, hc⟩
      have := (commSub U₁ (Subgroup.zpowers a)).mul_mem (Subgroup.inv_mem _
        (commSub_mono h21 le_rfl hy)) hwa1
      rwa [← hyc, inv_mul_cancel_left] at this
    have hb : commSub U₁ (Subgroup.zpowers a) ⊓ (W ⊓ fixV L) = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right _ (commSub_mono h1W le_rfl)).trans hbot.le)
    rw [hb] at hc'
    exact mem_bot.mp hc'
  rw [hc1, mul_one] at hyc
  rw [commSub_zpowers_eq_map_commMulHom (hU₂ haL)] at hy
  obtain ⟨u, hu, hua⟩ := hy
  rw [commMulHom_apply] at hua
  have hwu : w * u⁻¹ ∈ U₁ ⊓ fixV (Subgroup.zpowers a) := by
    refine mem_inf.mpr ⟨U₁.mul_mem hw (U₁.inv_mem (h21 hu)), ?_⟩
    rw [mem_fixV_zpowers_iff_apply, map_mul, map_inv]
    rw [hyc] at hua
    calc a w * (a u)⁻¹ = (a w * w⁻¹) * w * (a u)⁻¹ := by group
      _ = (a u * u⁻¹) * w * (a u)⁻¹ := by rw [hua]
      _ = w * u⁻¹ := by
          rw [mul_comm (a u * u⁻¹) w, mul_assoc, mul_right_comm (a u), mul_inv_cancel, one_mul]
  have : w = (w * u⁻¹) * u := by group
  rw [this]
  exact mul_mem (mem_sup_left hwu) (mem_sup_right hu)

end Sections

theorem nonempty_mulEquiv_open_sz {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : Nonempty (suzukiGroup a K ≃* CFSG.Open.Sz a) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 (2 * a + 1)) := Fintype.ofFinite _
  obtain ⟨e₀⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 (2 * a + 1)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 (2 * a + 1) (by omega)]
  exact ⟨(CFSG.Blueprint.EvenSource.suzukiGroupMapEquiv a
    (FiniteField.ringEquivOfCardEq (K := K) (K' := GaloisField 2 (2 * a + 1)) hcard)).trans
    e₀.symm⟩

section OddNormal

variable [Finite V]

theorem sq_eq_one_of_comm_mem_fixed (hV : ∀ v : V, v ^ 2 = 1) {F : Subgroup V} {g : MulAut V}
    (hgF : ∀ f ∈ F, g f = f) (hg : ∀ v, g v * v⁻¹ ∈ F) : g ^ 2 = 1 := by
  have hinv : ∀ v : V, v⁻¹ = v :=
    fun v => inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV v)
  ext v
  rw [sq, MulAut.mul_apply, MulAut.one_apply]
  have h1 : g v = (g v * v⁻¹) * v := by group
  rw [h1, map_mul, hgF _ (hg v), mul_right_comm, ← sq, hV, one_mul, hinv]

theorem ker_eq_bot_of_isQuadratic
    (hV : ∀ v : V, v ^ 2 = 1) {Y B : Subgroup (MulAut V)} (hBY : B ≤ Y)
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB4 : 4 ≤ Nat.card B) (hq : IsQuadratic B)
    (hfix : ∀ b ∈ B, b ≠ 1 → fixV (Subgroup.zpowers b) ≤ fixV B) {x : MulAut V}
    (hxY : x ∈ Y) (hx : B ⊔ B.map (MulAut.conj x).toMonoidHom = Y) {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ψ : ↥Y →* suzukiGroup a K) (hψ : Function.Surjective ψ) (hodd : ¬ 2 ∣ Nat.card ψ.ker) :
    ψ.ker = ⊥ := by
  classical
  set Q := ψ.ker with hQ
  have hQn : Q.Normal := MonoidHom.normal_ker ψ
  set F := fixV B with hF
  have hBF : ∀ b ∈ B, ∀ f ∈ F, b f = f := fun b hb f hf => hf b hb
  have hFb : ∀ b ∈ B, b ≠ 1 → fixV (Subgroup.zpowers b) = F := fun b hb hb1 =>
    le_antisymm (hfix b hb hb1) (fixV_le_fixV_of_le (Subgroup.zpowers_le.mpr hb))
  have hcomm : ∀ b ∈ B, ∀ v, b v * v⁻¹ ∈ F := fun b hb v =>
    hq (Subgroup.subset_closure ⟨b, hb, v, rfl⟩)
  have hQF : ∀ q ∈ Q, (q : MulAut V) ∈ stabSub F := by
    have hAX : B.subgroupOf Y ≤ normalizer (Q : Set ↥Y) := fun g _ => by
      rw [mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hQn.conj_mem h hh g, fun hh => ?_⟩
      have := hQn.conj_mem _ hh g⁻¹
      rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
    have hcardB : Nat.card (B.subgroupOf Y) = Nat.card B :=
      Nat.card_congr (subgroupOfEquivOfLe hBY).toEquiv
    have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
      Nat.prime_two (isElemAbelian_subgroupOf hB) (by rw [hcardB]; omega) hAX
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    have hle : Q ≤ (stabSub F).comap Y.subtype := by
      rw [← hgen]
      refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
      intro r hr
      obtain ⟨-, hr⟩ := mem_inf.mp hr
      rw [mem_centralizer_singleton_iff] at hr
      rw [mem_comap, Subgroup.coe_subtype, mem_stabSub]
      have hb' : (b : MulAut V) ∈ B := mem_subgroupOf.mp hb
      have hb1' : (b : MulAut V) ≠ 1 := fun h => hb1 (Subtype.ext h)
      have hrb : ∀ v, (r : MulAut V) ((b : MulAut V) v) = (b : MulAut V) ((r : MulAut V) v) :=
        fun v => by
          have := congrArg (fun g : ↥Y => (g : MulAut V) v) hr
          simpa [MulAut.mul_apply] using this
      intro v
      rw [← hFb _ hb' hb1', mem_fixV_zpowers_iff_apply, mem_fixV_zpowers_iff_apply, ← hrb]
      exact (r : MulAut V).injective.eq_iff
    exact fun q hq => hle hq
  set P : Subgroup (MulAut V) := quotTriv ⊤ F ⊓ centSub F with hP
  have hmemP : ∀ g : MulAut V, (∀ f ∈ F, g f = f) → (∀ v, g v * v⁻¹ ∈ F) → g ∈ P :=
    fun g h1 h2 => mem_inf.mpr ⟨mem_quotTriv.mpr ⟨mem_stabSub.mpr fun v => by simp,
      fun w _ => h2 w⟩, mem_centSub.mpr h1⟩
  have hP2 : ∀ g ∈ P, g ^ 2 = 1 := fun g hg =>
    sq_eq_one_of_comm_mem_fixed hV (mem_centSub.mp (mem_inf.mp hg).2)
      fun v => (mem_quotTriv.mp (mem_inf.mp hg).1).2 v (mem_top v)
  have hcommQ : ∀ q ∈ Q, ∀ b ∈ B, (q : MulAut V) * b = b * q := by
    intro q hqQ b hb
    set b' : ↥Y := ⟨b, hBY hb⟩ with hb'
    have hcQ : q * (b' * q⁻¹ * b'⁻¹) ∈ Q := Q.mul_mem hqQ (hQn.conj_mem _ (Q.inv_mem hqQ) b')
    have hqs := hQF q hqQ
    have hqP : (q : MulAut V) * b * (q : MulAut V)⁻¹ ∈ P := by
      refine hmemP _ (fun f hf => ?_) fun v => ?_
      · have hf' : (q : MulAut V)⁻¹ f ∈ F := ((stabSub F).inv_mem hqs f).mpr hf
        rw [MulAut.mul_apply, MulAut.mul_apply, hBF b hb _ hf', MulAut.apply_inv_self]
      · have hv : b ((q : MulAut V)⁻¹ v) * ((q : MulAut V)⁻¹ v)⁻¹ ∈ F := hcomm b hb _
        have e : ((q : MulAut V) * b * (q : MulAut V)⁻¹) v * v⁻¹ =
            (q : MulAut V) (b ((q : MulAut V)⁻¹ v) * ((q : MulAut V)⁻¹ v)⁻¹) := by
          rw [map_mul, map_inv, MulAut.apply_inv_self]
          rfl
        rw [e]
        exact (hqs _).mpr hv
    have hcP : ((q * (b' * q⁻¹ * b'⁻¹) : ↥Y) : MulAut V) ∈ P := by
      have : ((q * (b' * q⁻¹ * b'⁻¹) : ↥Y) : MulAut V) =
          ((q : MulAut V) * b * (q : MulAut V)⁻¹) * b⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hb']
        group
      rw [this]
      exact P.mul_mem hqP (P.inv_mem (hmemP b (hBF b hb) (hcomm b hb)))
    have h1 : q * (b' * q⁻¹ * b'⁻¹) = 1 :=
      eq_one_of_sq_eq_one_of_odd hodd hcQ (Subtype.ext (by simpa using hP2 _ hcP))
    have h2 : q * b' = b' * q := by
      calc q * b' = q * (b' * q⁻¹ * b'⁻¹) * (b' * q) := by group
        _ = b' * q := by rw [h1, one_mul]
    exact congrArg Subtype.val h2
  have hcen : Q ≤ center ↥Y := by
    intro q hqQ
    rw [mem_center_iff]
    intro y
    have hle : B ⊔ B.map (MulAut.conj x).toMonoidHom ≤
        centralizer ({(q : MulAut V)} : Set (MulAut V)) := by
      refine sup_le (fun b hb => mem_centralizer_singleton_iff.mpr (hcommQ q hqQ b hb).symm) ?_
      rintro _ ⟨b, hb, rfl⟩
      rw [mem_centralizer_singleton_iff]
      set x' : ↥Y := ⟨x, hxY⟩ with hx'
      have h1 := hcommQ _ (hQn.conj_mem q hqQ x'⁻¹) b hb
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hx'] at h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc x * b * x⁻¹ * q = x * (b * (x⁻¹ * q * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * q * x) * b) * x⁻¹ := by rw [h1]
        _ = q * (x * b * x⁻¹) := by group
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hle (by rw [hx]; exact y.2)))
  have hD : commutator ↥Y = ⊤ := by
    set D := commutator ↥Y with hDdef
    have hDψ : D.map ψ = ⊤ := by
      rw [hDdef, map_commutator_eq, MonoidHom.range_eq_top.mpr hψ, ← _root_.commutator_def,
        (CFSG.LieType.Ree.suzuki_perfect ha hK).1]
    have hinvD : ∀ t : ↥Y, t ^ 2 = 1 → t ∈ D := by
      intro t ht
      obtain ⟨d, hd, hdt⟩ : ψ t ∈ D.map ψ := hDψ ▸ mem_top _
      set z := d⁻¹ * t with hz
      have hzQ : z ∈ Q := by
        rw [hQ, MonoidHom.mem_ker, hz, map_mul, map_inv, hdt, inv_mul_cancel]
      have hzc : ∀ g : ↥Y, g * z = z * g := mem_center_iff.mp (hcen hzQ)
      have htz : t = d * z := by rw [hz, mul_inv_cancel_left]
      have hz2 : z ^ 2 ∈ D := by
        have h1 : d ^ 2 * z ^ 2 = 1 := by
          rw [← (show Commute d z from hzc d).mul_pow, ← htz, ht]
        rw [eq_inv_of_mul_eq_one_right h1]
        exact D.inv_mem (D.pow_mem hd 2)
      have hord : ¬ 2 ∣ orderOf z := fun h2 => hodd (h2.trans (Q.orderOf_dvd_natCard hzQ))
      obtain ⟨k, hk⟩ : ∃ k, orderOf z = 2 * k + 1 := ⟨orderOf z / 2, by omega⟩
      have hzk : z = (z ^ 2) ^ (k + 1) := by
        rw [← pow_mul, show 2 * (k + 1) = orderOf z + 1 by omega, pow_succ, pow_orderOf_eq_one,
          one_mul]
      rw [htz]
      exact D.mul_mem hd (hzk ▸ D.pow_mem hz2 _)
    have hle : B ⊔ B.map (MulAut.conj x).toMonoidHom ≤ D.map Y.subtype := by
      refine sup_le (fun b hb => ⟨⟨b, hBY hb⟩, hinvD _ (Subtype.ext ?_), rfl⟩) ?_
      · simpa using hB.2 b hb
      · rintro _ ⟨b, hb, rfl⟩
        have hxb : (MulAut.conj x).toMonoidHom b ∈ Y := by
          rw [← hx]
          exact mem_sup_right ⟨b, hb, rfl⟩
        refine ⟨⟨_, hxb⟩, hinvD _ (Subtype.ext ?_), rfl⟩
        simp only [Subgroup.coe_pow, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          OneMemClass.coe_one]
        rw [sq, show x * b * x⁻¹ * (x * b * x⁻¹) = x * (b * b) * x⁻¹ by group, ← sq, hB.2 b hb,
          mul_one, mul_inv_cancel]
    rw [eq_top_iff]
    intro y _
    obtain ⟨d, hd, hdy⟩ := hle (by rw [hx]; exact y.2)
    rwa [show d = y from Subtype.ext hdy] at hd
  haveI : Group.IsPerfect ↥Y := ⟨hD⟩
  haveI : Finite (suzukiGroup a K) := (CFSG.LieType.Ree.suzuki_simple ha hK).1
  exact CFSG.SignalizerFunctorTheorem.McBride.schur_odd_sz (by omega) (nonempty_mulEquiv_open_sz hK)
    ψ hψ hcen (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))

end OddNormal

section SecAct

variable {L : Subgroup (MulAut V)} {U₁ U₂ : Subgroup V}

@[expose] noncomputable def secAct (h₁ : L ≤ stabSub U₁) (h₂ : L ≤ stabSub U₂) :
    ↥L →* MulAut (Sec U₁ U₂) :=
  (quotHom (U₂.subgroupOf U₁)).comp
    (((resHom U₁).comp (Subgroup.inclusion h₁)).codRestrict (stabSub (U₂.subgroupOf U₁))
      fun k y => by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact h₂ k.2 y)

theorem secAct_mk (h₁ : L ≤ stabSub U₁) (h₂ : L ≤ stabSub U₂) (k : ↥L) (y : ↥U₁) :
    secAct h₁ h₂ k (QuotientGroup.mk y) =
      QuotientGroup.mk ⟨(k : MulAut V) y, (h₁ k.2 y).2 y.2⟩ :=
  rfl

theorem sec_mk_eq_mk_iff (y z : ↥U₁) :
    (QuotientGroup.mk y : Sec U₁ U₂) = QuotientGroup.mk z ↔ (y : V) * (z : V)⁻¹ ∈ U₂ := by
  rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv, Subgroup.mem_subgroupOf]
  rfl

theorem sec_mk_eq_one_iff (y : ↥U₁) : (QuotientGroup.mk y : Sec U₁ U₂) = 1 ↔ (y : V) ∈ U₂ := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem secAct_eq_one_iff (h₁ : L ≤ stabSub U₁) (h₂ : L ≤ stabSub U₂) (k : ↥L) :
    secAct h₁ h₂ k = 1 ↔ ∀ y ∈ U₁, (k : MulAut V) y * y⁻¹ ∈ U₂ := by
  constructor
  · intro h y hy
    have h1 := congrArg (fun φ : MulAut (Sec U₁ U₂) => φ (QuotientGroup.mk ⟨y, hy⟩)) h
    simp only [secAct_mk, MulAut.one_apply] at h1
    exact (sec_mk_eq_mk_iff _ _).1 h1
  · intro h
    refine MulEquiv.ext fun z => ?_
    induction z using QuotientGroup.induction_on with
    | H y => exact (sec_mk_eq_mk_iff _ _).2 (h y y.2)

theorem sec_sq_eq_one (hV : ∀ v : V, v ^ 2 = 1) (z : Sec U₁ U₂) : z ^ 2 = 1 := by
  induction z using QuotientGroup.induction_on with
  | H y =>
    rw [← QuotientGroup.mk_pow, show y ^ 2 = 1 from Subtype.ext (by simpa using hV y),
      QuotientGroup.mk_one]

end SecAct

namespace Hyp25Sz

variable [Finite V] {S M A L : Subgroup (MulAut V)} {Z₀ W : Subgroup V}

theorem ker_secAct_eq
    (hV : ∀ v : V, v ^ 2 = 1) (h : Hyp25Sz S M A L Z₀ W) (R : Subgroup ↥L) [R.Normal]
    (hOR : oTwo ↥L ≤ R) (hodd : ¬ 2 ∣ (oTwo ↥L).relIndex R) {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : ↥L ⧸ R ≃* suzukiGroup a K)
    {U₁ U₂ : Subgroup V} (hCU : W ⊓ fixV L ≤ U₂) (h21 : U₂ < U₁) (h1W : U₁ ≤ W)
    (hU₁ : L ≤ stabSub U₁) (hU₂ : L ≤ stabSub U₂)
    (hirr : ∀ X : Subgroup V, U₂ ≤ X → X ≤ U₁ → L ≤ stabSub X → X = U₂ ∨ X = U₁) :
    (secAct hU₁ hU₂).ker = R := by
  classical
  set ρ := secAct hU₁ hU₂ with hρ
  have hρ1 : ∀ l : ↥L, l ∈ ρ.ker ↔ ∀ y ∈ U₁, (l : MulAut V) y * y⁻¹ ∈ U₂ := fun l =>
    MonoidHom.mem_ker.trans (secAct_eq_one_iff hU₁ hU₂ l)
  set φ : ↥L →* suzukiGroup a K := e.toMonoidHom.comp (QuotientGroup.mk' R) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective R)
  have hφk : φ.ker = R := by
    ext g
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hAO : ∀ b (hb : b ∈ A), (⟨b, h.isL24Sz.le hb⟩ : ↥L) ∈ ρ.ker →
      b ∈ (oTwo ↥L).map L.subtype := by
    intro b hb hbk
    by_contra hbO
    have hc : commSub U₁ (Subgroup.zpowers b) ≤ U₂ := by
      rw [commSub_zpowers_eq_map_commMulHom (hU₁ (h.isL24Sz.le hb)), map_le_iff_le_comap]
      intro w hw
      exact (hρ1 _).mp hbk w hw
    exact h21.ne (h.eq_of_commSub_le hV hb hbO hCU h21.le h1W hU₁ hU₂ hc).symm
  have hO : oTwo ↥L ≤ ρ.ker := by
    have hP : IsPGroup 2 ((oTwo ↥L).map ρ) := (oTwo_isPGroup ↥L).map ρ
    obtain ⟨y, hy1, hy0⟩ := Set.not_subset.mp (not_le_of_gt h21)
    have hnt : Nontrivial (Sec U₁ U₂) :=
      ⟨⟨QuotientGroup.mk ⟨y, hy1⟩, 1, fun h0 => hy0 ((sec_mk_eq_one_iff ⟨y, hy1⟩).mp h0)⟩⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : 2 ∣ Nat.card (⊤ : Subgroup (Sec U₁ U₂)) := by
      rw [card_top]
      exact ((isPGroup_two_of_sq_eq_one (sec_sq_eq_one hV)).card_eq_or_dvd).resolve_left
        Finite.one_lt_card.ne'
    obtain ⟨d, -, hd1, hdfix⟩ := CFSG.LocalAnalysis.EvenBN.Tits.N.exists_ne_one_fixed _ hP ⊤
      (fun _ _ _ _ => mem_top _) h2
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective d
    have hz0 : (z : V) ∉ U₂ := fun h0 => hd1 ((sec_mk_eq_one_iff z).mpr h0)
    have hzfix : ∀ o ∈ oTwo ↥L, (o : MulAut V) z * (z : V)⁻¹ ∈ U₂ := by
      intro o ho
      have := hdfix (ρ o) ⟨o, ho, rfl⟩
      rw [hρ, secAct_mk] at this
      exact (sec_mk_eq_mk_iff _ _).mp this
    set Fx : Subgroup V :=
      U₁ ⊓ ⨅ (o : ↥L) (_ : o ∈ oTwo ↥L), U₂.comap (commMulHom (o : MulAut V)) with hFx
    have hmemFx : ∀ w, w ∈ Fx ↔ w ∈ U₁ ∧ ∀ o ∈ oTwo ↥L, (o : MulAut V) w * w⁻¹ ∈ U₂ := by
      intro w
      simp only [hFx, mem_inf, mem_iInf, mem_comap, commMulHom_apply]
    have h2F : U₂ ≤ Fx := fun w hw => (hmemFx w).mpr ⟨h21.le hw, fun o _ =>
      U₂.mul_mem ((hU₂ o.2 w).mpr hw) (U₂.inv_mem hw)⟩
    have hLF : L ≤ stabSub Fx := le_stabSub_of_forall_apply_mem fun l hl w hw => by
      obtain ⟨hw1, hwo⟩ := (hmemFx w).mp hw
      refine (hmemFx _).mpr ⟨(hU₁ hl w).mpr hw1, fun o ho => ?_⟩
      set l' : ↥L := ⟨l, hl⟩ with hl'
      have ho' : l'⁻¹ * o * l'⁻¹⁻¹ ∈ oTwo ↥L :=
        (inferInstance : (oTwo ↥L).Normal).conj_mem o ho l'⁻¹
      have e : (o : MulAut V) (l w) * (l w)⁻¹ =
          l (((l'⁻¹ * o * l'⁻¹⁻¹ : ↥L) : MulAut V) w * w⁻¹) := by
        simp only [hl', Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, MulAut.mul_apply, map_mul,
          map_inv, MulAut.apply_inv_self]
      rw [e]
      exact (hU₂ hl _).mpr (hwo _ ho')
    have hFne : Fx ≠ U₂ := fun hF => hz0 (hF ▸ (hmemFx z).mpr ⟨z.2, hzfix⟩)
    have hFU : Fx = U₁ := (hirr Fx h2F inf_le_left hLF).resolve_left hFne
    intro o ho
    rw [hρ1]
    intro w hw
    exact ((hmemFx w).mp (hFU ▸ hw)).2 o ho
  have hKR : ρ.ker ≤ R := by
    have hN : (ρ.ker.map φ).Normal := (MonoidHom.normal_ker ρ).map φ hφs
    obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Ree.suzuki_simple ha hK
    rcases hN.eq_bot_or_eq_top with hb | ht
    · rw [← hφk]
      exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      obtain ⟨b, hbA, hbO⟩ := h.isL24Sz.exists_mem_not_mem_oTwo h.elemAb
      set b' : ↥L := ⟨b, h.isL24Sz.le hbA⟩ with hb'
      obtain ⟨k, hk, hkb⟩ : φ b' ∈ ρ.ker.map φ := ht ▸ mem_top _
      set r := k⁻¹ * b' with hr
      have hrR : r ∈ R := by
        rw [← hφk, MonoidHom.mem_ker, hr, map_mul, map_inv, hkb, inv_mul_cancel]
      have hρb : ρ b' = ρ r := by
        rw [hr, map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
      have hb2 : ρ b' ^ 2 = 1 := by
        rw [← map_pow, show b' ^ 2 = 1 from Subtype.ext (by simpa using h.elemAb.2 b hbA),
          map_one]
      have hrm : r ^ (oTwo ↥L).relIndex R ∈ oTwo ↥L := by
        have hcard : Nat.card (R.map (QuotientGroup.mk' (oTwo ↥L))) = (oTwo ↥L).relIndex R := by
          rw [← relIndex_ker, QuotientGroup.ker_mk']
        have h1 := (R.map (QuotientGroup.mk' (oTwo ↥L))).orderOf_dvd_natCard
          (mem_map_of_mem _ hrR)
        rw [hcard] at h1
        have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
        rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have hρm : ρ r ^ (oTwo ↥L).relIndex R = 1 := by
        rw [← map_pow]
        exact hO hrm
      have hcop : Nat.Coprime 2 ((oTwo ↥L).relIndex R) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
      have h1 : orderOf (ρ r) = 1 := Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one (hρb ▸ hb2)) (orderOf_dvd_of_pow_eq_one hρm)
      exact hbO (hAO b hbA (MonoidHom.mem_ker.mpr (hρb.trans (orderOf_eq_one_iff.mp h1))))
  refine le_antisymm hKR ?_
  obtain ⟨x, hxL, hxM⟩ := Set.not_subset.mp h.isL24Sz.not_le
  set x' : ↥L := ⟨x, hxL⟩ with hx'
  set A' := A.subgroupOf L with hA'
  set B := A'.map ρ with hB
  have hBel : CFSG.Open.IsElemAbelian 2 B :=
    isElemAbelian_map (isElemAbelian_subgroupOf h.elemAb) ρ
  have hAK : A' ⊓ ρ.ker ≤ oTwo ↥L := by
    intro b hb
    obtain ⟨hbA, hbK⟩ := mem_inf.mp hb
    obtain ⟨o, ho, hob⟩ := hAO b (mem_subgroupOf.mp hbA) hbK
    rwa [show o = b from Subtype.ext hob] at ho
  have hB4 : 4 ≤ Nat.card B := by
    have h4 := h.isL24Sz.four_le h.elemAb
    have e1 : Nat.card B = ρ.ker.relIndex A' := (relIndex_ker A' ρ).symm
    have hKO : ρ.ker ⊓ A' = oTwo ↥L ⊓ A' := le_antisymm
      (le_inf (by rw [inf_comm]; exact hAK) inf_le_right) (inf_le_inf_right _ hO)
    have e2 : ρ.ker.relIndex A' = (oTwo ↥L).relIndex A' := by
      rw [← inf_relIndex_right, hKO, inf_relIndex_right]
    have e3 : (oTwo ↥L).relIndex A' = ((oTwo ↥L).map L.subtype).relIndex A := by
      rw [← relIndex_subgroupOf h.isL24Sz.le]
      congr 1
      exact (comap_map_eq_self_of_injective L.subtype_injective _).symm
    omega
  have hBq : IsQuadratic B := by
    rw [IsQuadratic, commV, closure_le]
    rintro _ ⟨β, ⟨b, hb, rfl⟩, v, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rintro _ ⟨c, hc, rfl⟩
    have hmem : (b : MulAut V) y * (y : V)⁻¹ ∈ fixV A :=
      h.quadratic (subset_closure ⟨b, mem_subgroupOf.mp hb, y, rfl⟩)
    rw [hρ, secAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, secAct_mk]
    congr 1
    exact Subtype.ext (hmem c (mem_subgroupOf.mp hc))
  have hBfix : ∀ β ∈ B, β ≠ 1 → fixV (Subgroup.zpowers β) ≤ fixV B := by
    rintro _ ⟨b, hb, rfl⟩ hb1 v hv
    have hbA : (b : MulAut V) ∈ A := mem_subgroupOf.mp hb
    have hbO : (b : MulAut V) ∉ (oTwo ↥L).map L.subtype := by
      rintro ⟨o, ho, hob⟩
      rw [show o = b from Subtype.ext hob] at ho
      exact hb1 (MonoidHom.mem_ker.mp (hO ho))
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    have hy : (b : MulAut V) y * (y : V)⁻¹ ∈ U₂ := by
      have := mem_fixV_zpowers_iff_apply.mp hv
      rw [hρ, secAct_mk] at this
      exact (sec_mk_eq_mk_iff _ _).mp this
    obtain ⟨b1, -, -, b4, -⟩ := h.fixV_eq hV hbA hbO
    have hmem := h.setting.mem_of_comm_mem_section hV hbA hxL (h.isL24Sz.sup_conj x hxL hxM)
      b1.symm b4 hCU h21.le h1W hU₁ hU₂ y.2 hy
    obtain ⟨f, hf, u, hu, hfu⟩ := mem_sup.mp hmem
    have hfA : f ∈ fixV A := by
      have hfW : f ∈ W ⊓ fixV (Subgroup.zpowers (b : MulAut V)) :=
        mem_inf.mpr ⟨h1W (mem_inf.mp hf).1, (mem_inf.mp hf).2⟩
      rw [← b1] at hfW
      exact (mem_inf.mp hfW).2
    rintro _ ⟨c, hc, rfl⟩
    rw [hρ, secAct_mk]
    refine (sec_mk_eq_mk_iff _ _).mpr ?_
    show (c : MulAut V) y * (y : V)⁻¹ ∈ U₂
    rw [← hfu, map_mul, hfA c (mem_subgroupOf.mp hc), ← div_eq_mul_inv,
      mul_div_mul_left_eq_div, div_eq_mul_inv]
    exact U₂.mul_mem ((hU₂ c.2 u).mpr hu) (U₂.inv_mem hu)
  have hYx : B ⊔ B.map (MulAut.conj (ρ x')).toMonoidHom = ρ.range := by
    have hs := h.isL24Sz.sup_conj_subgroupOf hxL hxM
    rw [MonoidHom.range_eq_map, ← hs, Subgroup.map_sup, hB, map_map, map_map]
    congr 2
    ext g
    simp [MulAut.conj_apply, map_mul, map_inv, hx']
  have hKR' : ρ.ker ≤ φ.ker := hφk ▸ hKR
  set ψ : ↥ρ.range →* suzukiGroup a K := (QuotientGroup.lift ρ.ker φ hKR').comp
    (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom with hψdef
  have hψρ : ∀ l : ↥L, ψ (ρ.rangeRestrict l) = φ l := by
    intro l
    rw [hψdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      show (QuotientGroup.quotientKerEquivRange ρ).symm (ρ.rangeRestrict l) = (l : ↥L ⧸ ρ.ker)
        from (MulEquiv.symm_apply_eq _).mpr rfl, QuotientGroup.lift_mk]
  have hψs : Function.Surjective ψ := fun z => by
    obtain ⟨l, rfl⟩ := hφs z
    exact ⟨_, hψρ l⟩
  have hψk : ψ.ker = R.map ρ.rangeRestrict := by
    ext y
    obtain ⟨l, rfl⟩ := ρ.rangeRestrict_surjective y
    rw [MonoidHom.mem_ker, hψρ, ← MonoidHom.mem_ker, hφk]
    constructor
    · intro hl
      exact ⟨l, hl, rfl⟩
    · rintro ⟨r, hr, hrl⟩
      have hrl' : r⁻¹ * l ∈ ρ.ker := by
        rw [← MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, map_mul, map_inv, hrl,
          inv_mul_cancel]
      have := R.mul_mem hr (hKR hrl')
      rwa [mul_inv_cancel_left] at this
  have hψodd : ¬ 2 ∣ Nat.card ψ.ker := by
    rw [hψk, ← relIndex_ker, MonoidHom.ker_rangeRestrict]
    exact fun h2 => hodd (h2.trans (relIndex_dvd_of_le_left (L := R) hO))
  have hbot := ker_eq_bot_of_isQuadratic (sec_sq_eq_one hV) (map_le_range ρ A') hBel hB4 hBq
    hBfix ⟨x', rfl⟩ hYx ha hK ψ hψs hψodd
  intro r hr
  have h1 : ρ.rangeRestrict r ∈ ψ.ker := hψk ▸ mem_map_of_mem _ hr
  rw [hbot, mem_bot] at h1
  rw [← MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, h1]

theorem eq_bot_of_oTwo_eq_bot
    (hV : ∀ v : V, v ^ 2 = 1) (h : Hyp25Sz S M A L Z₀ ⊤) (hO : oTwo ↥L = ⊥) (R : Subgroup ↥L)
    [R.Normal] (hodd : ¬ 2 ∣ (oTwo ↥L).relIndex R) {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : ↥L ⧸ R ≃* suzukiGroup a K) : R = ⊥ := by
  obtain ⟨x, hxL, hxM⟩ := Set.not_subset.mp h.isL24Sz.not_le
  set φ : ↥L →* suzukiGroup a K := e.toMonoidHom.comp (QuotientGroup.mk' R) with hφ
  have hφk : φ.ker = R := by
    ext g
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hO' : (oTwo ↥L).map L.subtype = ⊥ := by rw [hO, Subgroup.map_bot]
  have hA4 : 4 ≤ Nat.card A := by
    have := h.isL24Sz.four_le h.elemAb
    rwa [hO', relIndex_bot_left] at this
  have hfix : ∀ b ∈ A, b ≠ 1 → fixV (Subgroup.zpowers b) ≤ fixV A := by
    intro b hb hb1
    have hbO : b ∉ (oTwo ↥L).map L.subtype := by
      rw [hO']
      exact fun h' => hb1 (mem_bot.mp h')
    obtain ⟨b1, -⟩ := h.fixV_eq hV hb hbO
    simpa using b1.symm.le
  rw [← hφk]
  exact ker_eq_bot_of_isQuadratic hV h.isL24Sz.le h.elemAb hA4 h.quadratic hfix hxL
    (h.isL24Sz.sup_conj x hxL hxM) ha hK φ (e.surjective.comp (QuotientGroup.mk'_surjective R))
    (by rwa [hφk, ← relIndex_bot_left, ← hO])

end Hyp25Sz

end CFSG.RankThree.S4Free.Stell
