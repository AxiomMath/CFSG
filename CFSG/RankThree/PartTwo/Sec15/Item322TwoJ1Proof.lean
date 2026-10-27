module

public import CFSG.RankThree.PartTwo.Sec15.Item322TwoJ1
import CFSG.Quasithin.Background.SmithB45J2Main
import CFSG.Quasithin.MS93.S38EAQuot
import CFSG.RankThree.PartTwo.Sec3.TwoOfThreeNormal

public section

namespace CFSG.RankThree.PartTwo.Sec15.Item322Scope

open CFSG.Blueprint CFSG.RankThree.PartTwo.Sec3 CFSG.Quasithin CFSG.Quasithin.MS93.S38E
open CFSG.Quasithin.B5

variable {X : Type} [Group X] [Finite X]

theorem relIndex_center_le_of_relIndex_centralizer_le
    {Q V : Subgroup X} [Q.Normal]
    (e : X ⧸ Q ≃* NativeSporadic.J2) (hVn : V.Normal) (hV : IsElemTwo V)
    (hQV : Q ≤ Subgroup.centralizer (V : Set X)) {t : X} (htQ : t ∉ Q)
    (ht2 : t * t ∈ Q) {b : ℕ}
    (hb : (Subgroup.centralizer ({t} : Set X)).relIndex V ≤ b) :
    (Subgroup.center X).relIndex V ≤ b ^ 4 := by
  set π : X →* X ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hτ : orderOf (π t) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two]
      exact (QuotientGroup.eq_one_iff (t * t)).mpr ht2
    · intro h1
      exact htQ ((QuotientGroup.eq_one_iff t).mp h1)
  obtain ⟨c₁, c₂, c₃, c₄, hgen⟩ := exists_four_conj_closure_eq_top_of_equiv e hτ
  obtain ⟨g₁, rfl⟩ := hπs c₁
  obtain ⟨g₂, rfl⟩ := hπs c₂
  obtain ⟨g₃, rfl⟩ := hπs c₃
  obtain ⟨g₄, rfl⟩ := hπs c₄
  set H : Subgroup X := Subgroup.centralizer ({g₁ * t * g₁⁻¹} : Set X) ⊓
    Subgroup.centralizer ({g₂ * t * g₂⁻¹} : Set X) ⊓
    Subgroup.centralizer ({g₃ * t * g₃⁻¹} : Set X) ⊓
    Subgroup.centralizer ({g₄ * t * g₄⁻¹} : Set X) with hH
  have hb' : ∀ g : X, (Subgroup.centralizer ({g * t * g⁻¹} : Set X)).relIndex V ≤ b :=
    fun g => (relIndex_centralizer_conj_le hVn g t).trans hb
  have hHle' : H.relIndex V ≤ b * b * b * b := by
    refine Subgroup.relIndex_inf_le.trans ?_
    refine (Nat.mul_le_mul_right _ Subgroup.relIndex_inf_le).trans ?_
    refine (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ Subgroup.relIndex_inf_le)).trans ?_
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (hb' g₁) (hb' g₂)) (hb' g₃))
      (hb' g₄)
  have hHle : H.relIndex V ≤ b ^ 4 := hHle'.trans_eq (by ring)
  have hHZ : H ⊓ V ≤ Subgroup.center X ⊓ V := by
    rintro v ⟨hvH, hvV⟩
    refine ⟨?_, hvV⟩
    change v ∈ Subgroup.center X
    have hcomm : ∀ g : X, v ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set X) →
        g * t * g⁻¹ ∈ Subgroup.centralizer ({v} : Set X) := fun g hg => by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      exact hg.symm
    have hQv : Q ≤ Subgroup.centralizer ({v} : Set X) := fun q hq => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hQV hq) v hvV).symm
    obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := hvH
    have himg : π '' ({g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹, g₃ * t * g₃⁻¹, g₄ * t * g₄⁻¹} : Set X) =
        {π g₁ * π t * (π g₁)⁻¹, π g₂ * π t * (π g₂)⁻¹, π g₃ * π t * (π g₃)⁻¹,
          π g₄ * π t * (π g₄)⁻¹} := by
      simp only [Set.image_insert_eq, Set.image_singleton, map_mul, map_inv]
    have htop := eq_top_of_closure_image hQv (S := {g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹,
        g₃ * t * g₃⁻¹, g₄ * t * g₄⁻¹}) (by
      rintro _ (rfl | rfl | rfl | rfl)
      · exact hcomm g₁ h₁
      · exact hcomm g₂ h₂
      · exact hcomm g₃ h₃
      · exact hcomm g₄ h₄) (by rw [← hπ, himg]; exact hgen)
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({v} : Set X) := by
      rw [htop]
      exact Subgroup.mem_top g
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact hg
  calc (Subgroup.center X).relIndex V = (Subgroup.center X ⊓ V).relIndex V :=
        (Subgroup.inf_relIndex_right _ _).symm
    _ ≤ (H ⊓ V).relIndex V :=
        Subgroup.relIndex_le_of_le_left hHZ (relIndex_ne_zero_of_finite _ _)
    _ = H.relIndex V := Subgroup.inf_relIndex_right _ _
    _ ≤ b ^ 4 := hHle

private theorem range_equiv_of_ker_eq {Q : Subgroup X} [Q.Normal] {W : Type} [Group W]
    (ρ : X →* MulAut W) (e : X ⧸ Q ≃* NativeSporadic.J2) (hker : ρ.ker = Q) :
    Nonempty (↥ρ.range ≃* NativeSporadic.J2) :=
  ⟨(QuotientGroup.quotientKerEquivRange ρ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans e)⟩

private theorem inf_centSec_eq_bot_of_simple {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} [IsSimpleGroup ↥L] {V N : Subgroup W}
    (hLV : L ≤ stabSub V) (hLN : L ≤ stabSub N) (hnc : NonCent L V N) :
    L ⊓ centSec V N = ⊥ := by
  have hker : (B5.secHom L hLV hLN).ker = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B5.secHom L hLV hLN).ker with h | h
    · exact Subgroup.mem_bot.mpr (by
        have h' : g ∈ (⊥ : Subgroup ↥L) := h ▸ hg
        exact Subgroup.mem_bot.mp h')
    · exfalso
      obtain ⟨l, hl, w, hw, hlw⟩ := hnc
      have h1 : B5.secHom L hLV hLN ⟨l, hl⟩ = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      have h2 := congrArg (fun φ : MulAut (Sec V N) => φ (QuotientGroup.mk ⟨w, hw⟩)) h1
      rw [B5.secHom_mk, MulAut.one_apply] at h2
      have h3 : (l w)⁻¹ * w ∈ N := by
        have h3' := QuotientGroup.eq.mp h2
        rw [Subgroup.mem_subgroupOf] at h3'
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using h3' 
      exact hlw (by simpa [mul_comm] using N.inv_mem h3)
  rw [eq_bot_iff]
  intro x hx
  have hxl : x ∈ L := hx.1
  have hxc : x ∈ centSec V N := hx.2
  have hmem : (⟨x, hxl⟩ : ↥L) ∈ (B5.secHom L hLV hLN).ker :=
    (B5.mem_ker_secHom L hLV hLN ⟨x, hxl⟩).2 hxc
  rw [hker, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

private theorem exists_module_of_relIndex_center_le
    {Q V : Subgroup X} [Q.Normal] (e : X ⧸ Q ≃* NativeSporadic.J2) (hVn : V.Normal)
    (hV : IsElemTwo V) (hQV : Q ≤ Subgroup.centralizer (V : Set X))
    (hVZ : ¬ V ≤ Subgroup.center X) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (ρ : X →* MulAut W) (φ : V →* W),
      ρ.ker = Q ∧ (∀ w : W, w * w = 1) ∧
        Nat.card W = (Subgroup.center X).relIndex V ∧ Function.Surjective φ ∧
        (∀ t : X, φ.ker ≤ (Subgroup.centralizer ({t} : Set X)).comap V.subtype) ∧
        (∀ (t : X) (v : V), ((v : V) : X) ∈ Subgroup.centralizer ({t} : Set X) →
          φ v ∈ fixV (Subgroup.zpowers (ρ t))) := by
  set N : Subgroup X := V ⊓ Subgroup.center X with hN
  have hNn : N.Normal := Subgroup.normal_inf_normal V (Subgroup.center X)
  haveI : N.Normal := hNn
  set W : Subgroup (X ⧸ N) := V.map (QuotientGroup.mk' N) with hW
  have hWn : W.Normal := hVn.map _ (QuotientGroup.mk'_surjective N)
  haveI : W.Normal := hWn
  have hWc : ∀ a b : W, a * b = b * a := by
    rintro ⟨_, v, hv, rfl⟩ ⟨_, w, hw, rfl⟩
    apply Subtype.ext
    change QuotientGroup.mk' N v * QuotientGroup.mk' N w =
      QuotientGroup.mk' N w * QuotientGroup.mk' N v
    rw [← map_mul, ← map_mul, hV.1 v hv w hw]
  letI : CommGroup W := { (inferInstance : Group W) with mul_comm := hWc }
  have hW2 : ∀ w : W, w ^ 2 = 1 := by
    rintro ⟨_, v, hv, rfl⟩
    apply Subtype.ext
    change QuotientGroup.mk' N v ^ 2 = 1
    rw [← map_pow, pow_two, hV.2 v hv, map_one]
  have hWcard : Nat.card W = (Subgroup.center X).relIndex V := by
    rw [hW, ← Subgroup.relIndex_ker, QuotientGroup.ker_mk', hN, inf_comm,
      Subgroup.inf_relIndex_right]
  have hsimple : IsSimpleGroup (X ⧸ Q) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e
  set ρ₀ : X →* MulAut W := (MulAut.conjNormal (H := W)).comp (QuotientGroup.mk' N) with hρ₀
  have hρ₀v : ∀ (x v : X) (hv : v ∈ V),
      ((ρ₀ x ⟨QuotientGroup.mk' N v, v, hv, rfl⟩ : W) : X ⧸ N) =
        QuotientGroup.mk' N (x * v * x⁻¹) := by
    intro x v hv
    rw [hρ₀, MonoidHom.comp_apply, MulAut.conjNormal_apply]
    simp only [map_mul, map_inv]
  have hQρ : Q ≤ ρ₀.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun w => ?_
    obtain ⟨_, v, hv, rfl⟩ := w
    apply Subtype.ext
    rw [hρ₀v q v hv, MulAut.one_apply]
    have hqv : v * q = q * v := Subgroup.mem_centralizer_iff.mp (hQV hq) v hv
    rw [show q * v * q⁻¹ = v by rw [← hqv, mul_inv_cancel_right]]
  have hker : ρ₀.ker ≤ Q := by
    rcases le_or_eq_top_of_normal (MonoidHom.normal_ker ρ₀) hQρ with h | h
    · exact h
    exfalso
    have hsq : ∀ x : X, x * x ∈ Subgroup.centralizer (V : Set X) := by
      intro x
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hx : ρ₀ x = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top x
      have hc := congrArg (fun φ : MulAut W => ((φ ⟨QuotientGroup.mk' N v, v, hv, rfl⟩ : W) :
        X ⧸ N)) hx
      simp only [MulAut.one_apply] at hc
      rw [hρ₀v x v hv] at hc
      have hcN : (x * v * x⁻¹)⁻¹ * v ∈ N := QuotientGroup.eq.mp hc
      set c := (x * v * x⁻¹)⁻¹ * v with hcdef
      have hcV : c⁻¹ ∈ V := V.inv_mem hcN.1
      have hcZ : c⁻¹ ∈ Subgroup.center X := Subgroup.inv_mem _ hcN.2
      have hcc : c⁻¹ * c⁻¹ = 1 := hV.2 _ hcV
      have hxc : x * c⁻¹ * x⁻¹ = c⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hcZ x, mul_inv_cancel_right]
      have hy : x * v * x⁻¹ = v * c⁻¹ := by rw [hcdef]; group
      have key : x * x * v * (x * x)⁻¹ = v := by
        calc x * x * v * (x * x)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by group
          _ = x * (v * c⁻¹) * x⁻¹ := by rw [hy]
          _ = (x * v * x⁻¹) * (x * c⁻¹ * x⁻¹) := by group
          _ = v * (c⁻¹ * c⁻¹) := by rw [hy, hxc]; group
          _ = v := by rw [hcc, mul_one]
      calc v * (x * x) = x * x * v * (x * x)⁻¹ * (x * x) := by rw [key]
        _ = x * x * v := by group
    rcases le_or_eq_top_of_normal (Subgroup.normal_centralizer (H := V)) hQV with hCQ | hCtop
    · have hsq' : ∀ y : NativeSporadic.J2, y * y = 1 := by
        intro y
        obtain ⟨q, rfl⟩ := e.surjective y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q q
        have h1 : QuotientGroup.mk' Q (x * x) = 1 :=
          (QuotientGroup.eq_one_iff (x * x)).mpr (hCQ (hsq x))
        rw [← map_mul, ← map_mul, h1, map_one]
      obtain ⟨a, b, hab⟩ := CFSG.Sporadic.SmallOddCore.j2_not_comm
      apply hab
      have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq' a)
      have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq' b)
      have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hsq' (a * b))
      rw [← hab', mul_inv_rev, ha, hb]
    · apply hVZ
      intro v hv
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer (V : Set X) := by
        rw [hCtop]
        exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg v hv).symm
  have hkerEq : ρ₀.ker = Q := le_antisymm hker hQρ
  let φ : V →* W :=
    { toFun := fun v => ⟨QuotientGroup.mk' N (v : X), ⟨v, v.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp [QuotientGroup.mk'_apply]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp [QuotientGroup.mk'_apply, map_mul] }
  have hφsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨v, hv, hx'⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨v, hv⟩, Subtype.ext hx'⟩
  have hφker : ∀ t : X,
      φ.ker ≤ (Subgroup.centralizer ({t} : Set X)).comap V.subtype := by
    intro t v hv
    rw [MonoidHom.mem_ker] at hv
    have hvN : (v : X) ∈ N := by
      have h : QuotientGroup.mk' N (v : X) = 1 := by
        simpa [φ, QuotientGroup.mk'_apply] using congrArg Subtype.val hv
      exact (QuotientGroup.eq_one_iff (v : X)).mp h
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hvN.2 t).symm
  have hφfix : ∀ (t : X) (v : V),
      ((v : V) : X) ∈ Subgroup.centralizer ({t} : Set X) →
        φ v ∈ fixV (Subgroup.zpowers (ρ₀ t)) := by
    intro t v hv
    rw [mem_fixV_zpowers_iff_apply]
    apply Subtype.ext
    change QuotientGroup.mk' N (t * (v : X) * t⁻¹) = QuotientGroup.mk' N (v : X)
    have hv' : (v : X) * t = t * (v : X) :=
      Subgroup.mem_centralizer_singleton_iff.mp hv
    rw [show t * (v : X) * t⁻¹ = v by rw [← hv']; group]
  exact ⟨W, inferInstance, inferInstance, ρ₀, φ, hkerEq, fun w => by rw [← pow_two]; exact hW2 w,
    hWcard, hφsurj, hφker, hφfix⟩

private theorem module_equiv_and_element
    {W : Type} [CommGroup W]
    [Finite W] (hexp : ∀ w : W, w * w = 1) (hcardW : Nat.card W ≤ 2 ^ 12) {Q : Subgroup X}
    [Q.Normal] (e : X ⧸ Q ≃* NativeSporadic.J2) {ρ : X →* MulAut W} (hker : ρ.ker = Q)
    {t : X} (htQ : t ∉ Q) (ht2 : t * t ∈ Q) :
    ∃ eW : W ≃* J2Row.W6, ∃ u ∈ J2Row.L6, u * u = 1 ∧ u ≠ 1 ∧
      ∀ v : W, eW (ρ t v) = u (eW v) := by
  let L : Subgroup (MulAut W) := ρ.range
  have hLiso : Nonempty (↥L ≃* NativeSporadic.J2) := range_equiv_of_ker_eq ρ e hker
  obtain ⟨eLJ⟩ := hLiso
  haveI : IsSimpleGroup ↥L :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 eLJ
  have hLnc : ¬ IsMulCommutative ↥L := by
    intro hc
    obtain ⟨a, b, hab⟩ := CFSG.Sporadic.SmallOddCore.j2_not_comm
    have hcomm : eLJ.symm a * eLJ.symm b = eLJ.symm b * eLJ.symm a :=
      hc.is_comm.comm _ _
    exact hab (by simpa using congrArg eLJ hcomm)
  haveI : Group.IsPerfect ↥L := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hLnc
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp inferInstance
  have htne : ρ t ≠ 1 := by
    intro h
    apply htQ
    rw [← hker]
    exact MonoidHom.mem_ker.mpr h
  have hnc : NonCent L ⊤ ⊥ := by
    obtain ⟨w, hw⟩ : ∃ w, ρ t w ≠ w := by
      by_contra hcon
      push Not at hcon
      exact htne (MulEquiv.ext hcon)
    refine ⟨ρ t, ⟨t, rfl⟩, w, Subgroup.mem_top w, ?_⟩
    intro hmem
    rw [Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hw hmem
  obtain ⟨W', N', hN'W', hW'le, hirr, hnc'⟩ :=
    CFSG.Quasithin.MS93.S38EA.exists_irrSec_nonCent (X := L) (K := L) le_rfl hLperf
      (Nat.card W) ⊤ ⊥ (by simp) bot_le (fun _ _ _ _ => Subgroup.mem_top _)
      (fun _ _ w hw => by rw [Subgroup.mem_bot] at hw ⊢; rw [hw, map_one]) hnc
  have hLW : L ≤ stabSub W' := B1.le_stabSub_of_invariant hirr.2.1
  have hLN : L ≤ stabSub N' := B1.le_stabSub_of_invariant hirr.2.2.1
  have hfaith : L ⊓ centSec W' N' = ⊥ := inf_centSec_eq_bot_of_simple hLW hLN hnc'
  let L' : Subgroup (MulAut (Sec W' N')) := autSec L W' N'
  have hIrr : XMod.IsIrrSec ↥L' (⊥ : Subgroup (Sec W' N')) ⊤ :=
    B5.isIrrSec_autSec hirr.1 hirr.2.2.2 hLW hLN
  have hSpor : NativeSporadic.IsSporadic ↥L' .J2 :=
    ⟨(B5.secEquiv L hLW hLN hfaith).symm.trans eLJ⟩
  have hsecLe : Nat.card (Sec W' N') ≤ 2 ^ 12 := by
    have h := CFSG.Quasithin.card_sec_mul hirr.1.le
    have hle : Nat.card ↥W' ≤ Nat.card W := by
      simpa [Subgroup.card_top] using Subgroup.card_le_of_le hW'le
    rw [← h] at hle
    exact (Nat.le_mul_of_pos_right _ Nat.card_pos).trans (hle.trans hcardW)
  have hcardSec : Nat.card (Sec W' N') < 2 ^ 24 := by omega
  have hexpSec : ∀ v : Sec W' N', v * v = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_mul]
      have hw : (w : W) * (w : W) = 1 := hexp (w : W)
      rw [show w * w = 1 by exact Subtype.ext hw, QuotientGroup.mk_one]
  have hexpSecPow : ∀ v : Sec W' N', v ^ 2 = 1 := fun v => by
    rw [pow_two]; exact hexpSec v
  have hSmall : J2SmallModules := CFSG.Quasithin.J2Mod.j2SmallModules_holds
  obtain ⟨π, hπ⟩ := hSmall (Sec W' N') hexpSecPow L' hSpor hIrr hcardSec
  obtain ⟨eSec, heSec⟩ := J2Row.exists_equiv_of_zornQ hπ
  have hcardSecEq : Nat.card (Sec W' N') = 4096 := by
    rw [Nat.card_congr eSec.toEquiv, J2Row.card_W6]
  have hcardN : Nat.card ↥N' = 1 := by
    have h := CFSG.Quasithin.card_sec_mul hirr.1.le
    have hle : Nat.card ↥W' ≤ Nat.card W := by
      simpa [Subgroup.card_top] using Subgroup.card_le_of_le hW'le
    rw [hcardSecEq] at h
    rw [← h] at hle
    have hprod : 4096 * Nat.card ↥N' ≤ 4096 := hle.trans hcardW
    have : Nat.card ↥N' ≤ 1 := by
      have := Nat.le_of_mul_le_mul_left (by simpa using hprod) (by norm_num : 0 < 4096)
      simpa using this
    have hpos : 0 < Nat.card ↥N' := Nat.card_pos
    omega
  have hcardW' : Nat.card ↥W' = 4096 := by
    have h := CFSG.Quasithin.card_sec_mul hirr.1.le
    rw [hcardSecEq, hcardN] at h
    simpa using h.symm
  have hW'eq : W' = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge hW'le ?_
    rw [Subgroup.card_top, hcardW']
    exact hcardW
  have hN'eq : N' = ⊥ := Subgroup.card_eq_one.mp hcardN
  subst W'
  subst N' 
  have hLtop : L ≤ stabSub (⊤ : Subgroup W) := by
    intro l hl
    rw [mem_stabSub]
    intro u
    simp
  have hLbot : L ≤ stabSub (⊥ : Subgroup W) := by
    intro l hl
    rw [mem_stabSub]
    intro u
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    exact ⟨fun h => (MulEquiv.map_eq_one_iff l).mp h, fun h => by rw [h, map_one]⟩
  have hfaithTop : L ⊓ centSec (⊤ : Subgroup W) ⊥ = ⊥ :=
    inf_centSec_eq_bot_of_simple hLtop hLbot hnc'
  have hRealL : (FFModel.zornQ J2Model.j2Γ₀).RealizesVia L ⊤ (⊥ : Subgroup W)
      ((B5.secEquiv L hLtop hLbot hfaithTop).symm.toMonoidHom.comp π) :=
    B5.realizesVia_of_autSec bot_le hLtop hLbot hfaithTop hπ
  obtain ⟨eW, heW⟩ := J2Row.exists_equiv_of_zornQ hRealL
  have htL : ρ t ∈ L := ⟨t, rfl⟩
  obtain ⟨γ, hγ⟩ := hRealL.1 ⟨ρ t, htL⟩
  have hγ' : ((((B5.secEquiv L hLtop hLbot hfaithTop).symm) (π γ) : ↥L) : MulAut W) = ρ t :=
    congrArg Subtype.val hγ
  let u : MulAut J2Row.W6 := H.matHom (J2Row.qHomJ γ)
  have huL6 : u ∈ J2Row.L6 := by
    change H.matHom (J2Row.qHomJ γ) ∈ H.natImage J2Row.Γ₆
    rw [H.natImage_eq_map]
    exact ⟨_, J2Row.qHomJ_mem γ, rfl⟩
  have hconj : MulAut.congr eW (ρ t) = u := by
    refine MulEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := eW.surjective w
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [← hγ']
    exact heW γ v
  have ht2' : ρ t * ρ t = 1 := by
    have hmem : t * t ∈ ρ.ker := by rw [hker]; exact ht2
    have h := MonoidHom.mem_ker.mp hmem
    rwa [map_mul] at h
  have hu2 : u * u = 1 := by
    rw [← hconj, ← map_mul, ht2', map_one]
  have hu1 : u ≠ 1 := by
    intro h
    have h1 : MulAut.congr eW (ρ t) = 1 := by rw [hconj]; exact h
    have h2 : ρ t = 1 := (MulAut.congr eW).injective (by rw [h1, map_one])
    exact htne h2
  exact ⟨eW, u, huL6, hu2, hu1, fun v => by rw [← hγ']; exact heW γ v⟩

private theorem card_fixV_zpowers_le_256 {u : MulAut J2Row.W6}
    (huL : u ∈ J2Row.L6) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers u)) ≤ 256 := by
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  set A : Subgroup (MulAut J2Row.W6) := Subgroup.zpowers u with hA
  have hcardA : Nat.card A = 2 := by rw [hA, Nat.card_zpowers, hord]
  have hAL : A ≤ J2Row.L6 := (Subgroup.zpowers_le).2 huL
  set B : Subgroup J2Row.GL6 := A.comap H.matHom with hB
  have hBΓ : B ≤ J2Row.Γ₆ := J2Row.comap_matHom_le hAL
  have hBcard : Nat.card B = Nat.card A := J2Row.card_comap_matHom hAL
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    apply H.matHom_injective
    rw [map_mul, map_mul]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hBsq : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    apply H.matHom_injective
    rw [map_mul, map_one]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hi]
    calc u ^ i * u ^ i = u ^ (i + i) := by rw [← zpow_add]
      _ = u ^ (2 * i) := by congr 1; ring
      _ = (u ^ (2 : ℤ)) ^ i := by rw [zpow_mul]
      _ = 1 := by
        rw [show u ^ (2 : ℤ) = u ^ 2 by norm_num, show u ^ 2 = 1 by rw [pow_two]; exact hu2,
          one_zpow]
  obtain ⟨b2, -, -⟩ := J2Row.inner_bounds J2Row.card_Γ₆ hBΓ hBcomm hBsq
  exact (J2Row.card_fixV_le_mFix A).trans (b2 (by rw [hBcard, hcardA]))

theorem eight_lt_relIndex_centralizer
    {Q V : Subgroup X} [Q.Normal]
    (e : X ⧸ Q ≃* NativeSporadic.J2) (hVn : V.Normal) (hV : IsElemTwo V)
    (hQV : Q ≤ Subgroup.centralizer (V : Set X)) (hVZ : ¬ V ≤ Subgroup.center X) {t : X}
    (htQ : t ∉ Q) (ht2 : t * t ∈ Q) :
    8 < (Subgroup.centralizer ({t} : Set X)).relIndex V := by
  by_contra hle
  rw [not_lt] at hle
  have hcenter : (Subgroup.center X).relIndex V ≤ 8 ^ 4 :=
    relIndex_center_le_of_relIndex_centralizer_le e hVn hV hQV htQ ht2 hle
  have hcenter' : (Subgroup.center X).relIndex V ≤ 2 ^ 12 := by
    have hpow : (8 : ℕ) ^ 4 = 2 ^ 12 := by norm_num
    rwa [hpow] at hcenter
  obtain ⟨W, hWcomm, hWfin, ρ, φ, hker, hexp, hcard, hφsurj, hφker, hφfix⟩ :=
    exists_module_of_relIndex_center_le e hVn hV hQV hVZ
  letI : CommGroup W := hWcomm
  letI : Finite W := hWfin
  have hcardW : Nat.card W ≤ 2 ^ 12 := by rw [hcard]; exact hcenter'
  obtain ⟨eW, u, huL6, hu2, hu1, heW⟩ :=
    module_equiv_and_element hexp hcardW e hker htQ ht2
  have hconj : MulAut.congr eW (ρ t) = u := by
    refine MulEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := eW.surjective w
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact heW v
  have hfixU : Nat.card ↥(fixV (Subgroup.zpowers u)) ≤ 256 :=
    card_fixV_zpowers_le_256 huL6 hu2 hu1
  have hfixT : Nat.card ↥(fixV (Subgroup.zpowers (ρ t))) ≤ 256 := by
    have hmap : (Subgroup.zpowers (ρ t)).map (MulAut.congr eW).toMonoidHom =
        Subgroup.zpowers u := by
      rw [MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers hconj
    rw [← J2Row.card_fixV_map_congr eW (Subgroup.zpowers (ρ t)), hmap]
    exact hfixU
  have hcardW4096 : Nat.card W = 4096 := by
    rw [Nat.card_congr eW.toEquiv, J2Row.card_W6]
  have hrel16 : 16 ≤ (fixV (Subgroup.zpowers (ρ t))).relIndex (⊤ : Subgroup W) := by
    have hprod0 := Subgroup.relIndex_mul_card (H := fixV (Subgroup.zpowers (ρ t)))
      (K := ⊤)
    rw [inf_top_eq, Subgroup.card_top] at hprod0
    have hprod : (fixV (Subgroup.zpowers (ρ t))).relIndex (⊤ : Subgroup W) *
        Nat.card ↥(fixV (Subgroup.zpowers (ρ t))) = 4096 := by
      rw [hprod0, hcardW4096]
    by_contra h
    rw [not_le] at h
    have h15 : (fixV (Subgroup.zpowers (ρ t))).relIndex (⊤ : Subgroup W) ≤ 15 := by omega
    have hle' := Nat.mul_le_mul h15 hfixT
    omega
  let C : Subgroup V := (Subgroup.centralizer ({t} : Set X)).comap V.subtype
  have hker_le_C : φ.ker ≤ C := hφker t
  have hC_le : C.map φ ≤ fixV (Subgroup.zpowers (ρ t)) := by
    rintro _ ⟨v, hv, rfl⟩
    exact hφfix t v hv
  have hrel_eq : (C.map φ).relIndex (⊤ : Subgroup W) =
      (Subgroup.centralizer ({t} : Set X)).relIndex V := by
    have htop : Subgroup.map φ (⊤ : Subgroup V) = ⊤ :=
      Subgroup.map_top_of_surjective φ hφsurj
    rw [← htop, Subgroup.relIndex_map_map, sup_eq_left.mpr hker_le_C, top_sup_eq]
    change ((Subgroup.centralizer ({t} : Set X)).comap V.subtype).relIndex
      (⊤ : Subgroup V) = _
    rw [Subgroup.relIndex_comap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hrel_le : (fixV (Subgroup.zpowers (ρ t))).relIndex (⊤ : Subgroup W) ≤
      (C.map φ).relIndex (⊤ : Subgroup W) :=
    Subgroup.relIndex_le_of_le_left hC_le (relIndex_ne_zero_of_finite _ _)
  have h16 : 16 ≤ (Subgroup.centralizer ({t} : Set X)).relIndex V := by
    rw [← hrel_eq]
    exact hrel16.trans hrel_le
  omega

end CFSG.RankThree.PartTwo.Sec15.Item322Scope

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec3
  CFSG.RankThree.PartTwo.Sec15.Item322Scope

theorem item3_22TwoJ1_holds :
    Item3_22TwoJ1 := by
  intro X _ _ hF ⟨e⟩ R hQR ⟨eR⟩ _ hz
  have hCQ : Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X := by
    rw [← hF]
    exact CFSG.centralizer_generalizedFitting_le X
  set Q := CFSG.pCore 2 X with hQ
  have hQn : Q.Normal := CFSG.pCore_normal
  set V := omegaG Q with hVdef
  have hVn : V.Normal := omegaG_normal hQn
  have hVQ : V ≤ Q := omegaG_le Q
  have hVel : IsElemTwo V := isElemTwo_omegaG Q
  have hQV : Q ≤ Subgroup.centralizer (V : Set X) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hv.2.1 q hq
  have hZR : (omegaOneCenter (⊤ : Subgroup R)).map R.subtype ≤ V := by
    rw [map_omegaOneCenter, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    intro z hz
    have hzQ : z ∈ Q := hCQ (Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (hz.2.1 q (hQR hq)).symm)
    exact ⟨hzQ, fun x hx => hz.2.1 x (hQR hx), hz.2.2⟩
  have hVZ : ¬ V ≤ Subgroup.center X := fun h => hz (hZR.trans h)
  have hRQ : Q.relIndex R = 4 := by
    have h := Subgroup.relIndex_ker R (QuotientGroup.mk' Q)
    rw [QuotientGroup.ker_mk'] at h
    rw [h, Nat.card_congr eR.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hAQ : ∀ A ∈ famG R 1, A ≤ Q := by
    intro A hA a ha
    by_contra haQ
    have h8 := eight_lt_relIndex_centralizer e hVn hVel hQV hVZ haQ
      (by rw [hA.2.1.2 a ha]; exact Q.one_mem)
    have hstd := relIndex_centralizer_le_of_famG (hVQ.trans hQR) hVel hA
    have h1 : (Subgroup.centralizer ({a} : Set X)).relIndex V ≤
        (Subgroup.centralizer (A : Set X)).relIndex V :=
      Subgroup.relIndex_le_of_le_left
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
        (relIndex_ne_zero_of_finite _ _)
    have h2 : (Subgroup.centralizer (V : Set X)).relIndex A ≤ Q.relIndex A :=
      Subgroup.relIndex_le_of_le_left hQV (relIndex_ne_zero_of_finite _ _)
    have h3 : Q.relIndex A ≤ Q.relIndex R :=
      Subgroup.relIndex_le_of_le_right hA.1 (relIndex_ne_zero_of_finite _ _)
    rw [pow_one] at hstd
    have hle : (Subgroup.centralizer ({a} : Set X)).relIndex V ≤ 8 := by
      calc (Subgroup.centralizer ({a} : Set X)).relIndex V
          ≤ (Subgroup.centralizer (A : Set X)).relIndex V := h1
        _ ≤ 2 * (Subgroup.centralizer (V : Set X)).relIndex A := hstd
        _ ≤ 2 * 4 := Nat.mul_le_mul_left 2 (h2.trans (h3.trans_eq hRQ))
        _ = 8 := by norm_num
    omega
  rw [map_higherElemThompson R 1]
  exact jG_normal fun g A hA a ha => hQR (hQn.conj_mem a (hAQ A hA ha) g)

theorem item3_22Two_holds :
    Item3_22Two :=
  item3_22Two_of_J1 item3_22TwoJ1_holds

end CFSG.RankThree.PartTwo.Sec15
