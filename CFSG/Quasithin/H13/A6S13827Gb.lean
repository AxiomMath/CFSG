module

public import CFSG.Quasithin.H13.A6S13827Ga
public import CFSG.Quasithin.H13.A6S13826g
public import CFSG.Quasithin.H13.A6S13821zz26

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.B42U33
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem exists_kst_hom (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hKH : K ≤ H) :
    ∃ f : ↥K →* ↥(S.KSt H K), Function.Surjective f ∧
      ∀ k : ↥K, f k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  have hF1 := (hS.hF H hH).toHypF91
  have hV₁ : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF1.H_normalizes_V₁
  have hIH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have : Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure S.V3 H))) :=
    ⟨hF1.isElemAbelian_tilde⟩
  have hIHN : conjClosure S.V3 H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF1.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)).trans hV₁
  have hker : ∀ x : ↥H, actH hV₁ hIH x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
    intro x
    rw [A6Tv.actH_eq_one_iff hV₁ hIHN hIH x, hF1.pCoreOf_eq_centralizerMod]
    exact ⟨fun h1 => ⟨x.2, hV₁ x.2, h1⟩, fun h1 => h1.2.2⟩
  have hKst : S.KSt H K = (K.subgroupOf H).map (actH hV₁ hIH) :=
    autOn_tilde_eq_map_actH hV₁ hIH hKH
  let f : ↥K →* ↥(S.KSt H K) := ((actH hV₁ hIH).comp (Subgroup.inclusion hKH)).codRestrict _
    fun k => by
      rw [hKst]
      exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
  refine ⟨f, ?_, fun k => ?_⟩
  · rintro ⟨ψ, hψ⟩
    rw [hKst] at hψ
    obtain ⟨x, hx, rfl⟩ := hψ
    exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  · rw [← Subtype.coe_inj]
    exact hker _

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W)
include hs

theorem sub {X₁ X₂ : Subgroup G} (hWX₁ : W ≤ X₁) (hX₁X₂ : X₁ ≤ X₂) (hX₂X : X₂ ≤ X)
    (hHX₂ : H ≤ Subgroup.normalizer (X₂ : Set G)) (hHX₁ : H ≤ Subgroup.normalizer (X₁ : Set G))
    (hKnt : ∃ k ∈ K, ∃ x ∈ X₂, k * x * k⁻¹ * x⁻¹ ∉ X₁) : S.SecHyp H K X₂ X₁ :=
  ⟨hs.hS, hs.hH, hs.hKH, hs.hKn, hs.hHK, hs.hsimp, hs.hnab, hX₁X₂, hX₂X.trans hs.hXH, hHX₂, hHX₁,
    fun q hq x hx => hWX₁ (hs.hQ q hq x (hX₂X hx)), hKnt, fun x hx => hWX₁ (hs.hsq x (hX₂X hx))⟩

variable [IsMulCommutative ↥X]

theorem autSec_le_normalizer :
    autSec (autOn H X) ⊤ (W.subgroupOf X) ≤
      Subgroup.normalizer ((autSec (autOn K X) ⊤ (W.subgroupOf X) :
        Subgroup (MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))) :
          Set (MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))) := by
  intro g hg
  obtain ⟨h, -, rfl⟩ := (hs.mem_autSec_iff le_rfl).1 hg
  have key : ∀ h : ↥H, ∀ l ∈ autSec (autOn K X) ⊤ (W.subgroupOf X),
      hs.act h * l * (hs.act h)⁻¹ ∈ autSec (autOn K X) ⊤ (W.subgroupOf X) := by
    intro h l hl
    obtain ⟨k, hk, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hl
    refine (hs.mem_autSec_iff hs.hKH).2 ⟨h * k * h⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hs.hKn h.2) k).mp hk
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨key h l, fun hl => ?_⟩
  have h1 := key h⁻¹ _ hl
  rwa [map_inv, inv_inv, show (hs.act h)⁻¹ * (hs.act h * l * (hs.act h)⁻¹) * hs.act h = l by
    group] at h1

theorem inf_centralizer_le :
    autSec (autOn H X) ⊤ (W.subgroupOf X) ⊓
        Subgroup.centralizer ((autSec (autOn K X) ⊤ (W.subgroupOf X) :
          Subgroup (MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))) :
            Set (MulAut (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)))) ≤
      autSec (autOn K X) ⊤ (W.subgroupOf X) := by
  rintro g ⟨hg, hgc⟩
  obtain ⟨h, -, rfl⟩ := (hs.mem_autSec_iff le_rfl).1 hg
  have hq : (h : G) ∈ pCoreOf 2 H := by
    refine S.mem_pCoreOf_of_comm hs.hS hs.hH hs.hKH hs.hKn hs.hHK hs.hsimp hs.hnab h.2
      fun k hk => ?_
    have h1 := Subgroup.mem_centralizer_iff.1 hgc _
      ((hs.mem_autSec_iff hs.hKH).2 ⟨⟨k, hs.hKH hk⟩, hk, rfl⟩)
    have h2 : hs.act (h * ⟨k, hs.hKH hk⟩ * h⁻¹ * (⟨k, hs.hKH hk⟩ : ↥H)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    rw [hs.act_eq_one_iff] at h2
    simpa using h2
  rw [(hs.act_eq_one_iff h).2 hq]
  exact Subgroup.one_mem _

theorem exists_hom_autSec :
    ∃ φ : ↥K →* ↥(autSec (autOn K X) ⊤ (W.subgroupOf X)), Function.Surjective φ ∧
      ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ pCoreOf 2 H := by
  let φ : ↥K →* ↥(autSec (autOn K X) ⊤ (W.subgroupOf X)) :=
    (hs.act.comp (Subgroup.inclusion hs.hKH)).codRestrict _ fun k =>
      (hs.mem_autSec_iff hs.hKH).2 ⟨_, k.2, rfl⟩
  refine ⟨φ, ?_, fun k => ?_⟩
  · rintro ⟨ψ, hψ⟩
    obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hψ
    exact ⟨⟨f, hf⟩, rfl⟩
  · rw [← Subtype.coe_inj]
    exact hs.act_eq_one_iff _

theorem nonempty_equiv_kst :
    Nonempty (↥(autSec (autOn K X) ⊤ (W.subgroupOf X)) ≃* ↥(S.KSt H K)) := by
  obtain ⟨φ, hφs, hφk⟩ := hs.exists_hom_autSec
  obtain ⟨f, hfs, hfk⟩ := exists_kst_hom hs.hS hs.hH hs.hKH
  have hker : φ.ker = f.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφk, hfk]
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)⟩

theorem b42TypeU33 (hU : IsPSU 3 3 1 ↥(S.KSt H K)) :
    B42TypeU33 ↥(autSec (autOn K X) ⊤ (W.subgroupOf X)) := by
  obtain ⟨e⟩ := hs.nonempty_equiv_kst
  set LE := autSec (autOn K X) ⊤ (W.subgroupOf X) with hLE
  have : IsSimpleGroup ↥(S.KSt H K) := hs.hsimp
  have hsimpL : IsSimpleGroup ↥LE := e.isSimpleGroup
  have hZ : Subgroup.center ↥LE = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥LE) with h | h
    · exact h
    · exfalso
      obtain ⟨φ, -, hφk⟩ := hs.exists_hom_autSec
      obtain ⟨k, hk, k', hk', hkk⟩ := hs.hnab
      apply hkk
      have hc : φ ⟨k, hk⟩ * φ ⟨k', hk'⟩ = φ ⟨k', hk'⟩ * φ ⟨k, hk⟩ := by
        have hmem : φ ⟨k, hk⟩ ∈ Subgroup.center ↥LE := h ▸ Subgroup.mem_top _
        exact (Subgroup.mem_center_iff.1 hmem _).symm
      have h1 : φ (⟨k, hk⟩ * ⟨k', hk'⟩ * (⟨k, hk⟩ : ↥K)⁻¹ * (⟨k', hk'⟩ : ↥K)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
      simpa using (hφk _).1 h1
  refine ⟨hZ, ?_⟩
  let e0 : ↥LE ⧸ Subgroup.center ↥LE ≃* ↥LE :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact IsPSU.of_mulEquiv (e0.trans e).symm hU

theorem offender_u33
    (hU : IsPSU 3 3 1 ↥(S.KSt H K))
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {F : Subgroup G} (hFH : F ≤ H) (hF : ¬ F ≤ pCoreOf 2 H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H)
    (hle : (centralizerMod W X F).relIndex X ≤ (F ⊓ pCoreOf 2 H).relIndex F) :
    (F ⊓ pCoreOf 2 H).relIndex F = 8 ∧ (centralizerMod W X F).relIndex X = 8 ∧
      W.relIndex X = 2 ^ 6 := by
  set A := autSec (autOn F X) ⊤ (W.subgroupOf X) with hAdef
  have hA : Nat.card A = (F ⊓ pCoreOf 2 H).relIndex F := hs.card_autSec hFH
  have hi := hs.index_fixV_le hFH
  have hV : ∀ v : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X), v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact hs.sec_sq v
  obtain ⟨h8, hf8, h64⟩ := A6G2.offender_eq hV (hs.autSec_le hs.hKH le_rfl)
    hs.autSec_le_normalizer hs.inf_centralizer_le (hs.b42TypeU33 hU) (hs.fixV_eq_bot hirr)
    (hs.autSec_le hFH le_rfl) (hs.autSec_ne_bot hFH hF) (hs.isElemAbelian2_autSec hFH hFc hFs)
    (by rw [hA]; exact hi.trans hle)
  have hidx : (fixV A).index = 8 := by
    have e := (fixV A).card_mul_index
    rw [hf8, h64] at e
    omega
  refine ⟨by rw [← hA, h8], le_antisymm (hle.trans (by rw [← hA, h8])) (hidx ▸ hi), ?_⟩
  rw [← card_sec, h64]

theorem relIndex_le_indexU33
    (hU : IsPSU 3 3 1 ↥(S.KSt H K))
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {F : Subgroup G} (hFH : F ≤ H)
    (hFc : ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ pCoreOf 2 H)
    (hFs : ∀ f ∈ F, f * f ∈ pCoreOf 2 H) :
    (F ⊓ pCoreOf 2 H).relIndex F ≤ (centralizerMod W X F).relIndex X := by
  by_cases hF : F ≤ pCoreOf 2 H
  · rw [Subgroup.relIndex_eq_one.2 (le_inf le_rfl hF)]
    exact Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
  by_contra hlt
  push Not at hlt
  have h := hs.offender_u33 hU hirr hFH hF hFc hFs hlt.le
  omega

theorem mem_pCoreOf_of_transvU33
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) (hperf : ⁅K, K⁆ = K) {f : G} (hfH : f ∈ H) {z : G}
    (hz : ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ W ∨ f * x * f⁻¹ * x⁻¹ * z⁻¹ ∈ W) :
    f ∈ pCoreOf 2 H := by
  by_contra hfQ
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥X) ⟨b, hb⟩)
  obtain ⟨X₁, X₂, hWX₁, hX₁X₂, hX₂X, hHX₁, hHX₂, hirr, hKnt⟩ :=
    exists_chief_sec hs.hKH hperf hs.hWX hXc hs.hHX hs.hHW hs.hKnt
  have hs₂ := hs.sub hWX₁ hX₁X₂.le hX₂X hHX₂ hHX₁ hKnt
  have : IsMulCommutative ↥X₂ :=
    ⟨⟨fun a b => Subtype.ext (hXc a (hX₂X a.2) b (hX₂X b.2))⟩⟩
  set a := hs₂.act ⟨f, hfH⟩ with ha
  have ha1 : a ≠ 1 := fun h => hfQ ((hs₂.act_eq_one_iff _).1 h)
  obtain ⟨x₀, hx₀, hfx₀⟩ : ∃ x ∈ X₂, f * x * f⁻¹ * x⁻¹ ∉ X₁ := by
    by_contra hall
    push Not at hall
    exact hfQ (S.le_pCoreOf_of_triv hs₂.hS hs₂.hH hs₂.hKH hs₂.hKn hs₂.hHK hs₂.hsimp hs₂.hXH
      hs₂.hHX hs₂.hHW hs₂.hQ hs₂.hKnt hfH hall)
  have hfX : ∀ x ∈ X₂, f * x * f⁻¹ ∈ X₂ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHX₂ hfH) x).mp hx
  have hz₀ : f * x₀ * f⁻¹ * x₀⁻¹ * z⁻¹ ∈ X₁ :=
    hWX₁ ((hz x₀ (hX₂X hx₀)).resolve_left fun h => hfx₀ (hWX₁ h))
  have hzX : z ∈ X₂ := by
    have e : z = (f * x₀ * f⁻¹ * x₀⁻¹ * z⁻¹)⁻¹ * (f * x₀ * f⁻¹ * x₀⁻¹) := by group
    rw [e]
    exact X₂.mul_mem (X₂.inv_mem (hX₁X₂.le hz₀)) (X₂.mul_mem (hfX x₀ hx₀) (X₂.inv_mem hx₀))
  set e₀ := InternalSec.secMk (X₁.subgroupOf X₂) ⟨z, hzX⟩ with he₀
  have he : ∀ w, a w * w⁻¹ = 1 ∨ a w * w⁻¹ = e₀ := by
    intro w
    obtain ⟨x, rfl⟩ := InternalSec.secMk_surjective (X₁.subgroupOf X₂) w
    rw [ha, act_secMk]
    rcases hz x (hX₂X x.2) with h | h
    · left
      rw [← map_inv, ← map_mul, A6Mod.secMk_eq_one_iff]
      simpa only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] using hWX₁ h
    · right
      rw [← mul_inv_eq_one, he₀, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
        A6Mod.secMk_eq_one_iff]
      simpa only [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] using hWX₁ h
  have hidx := A6S20.index_fixV_zpowers_le_two he
  have he₀a : a e₀ = e₀ := by
    rcases he e₀ with h | h
    · exact mul_inv_eq_one.1 h
    · have h1 : a e₀ = 1 := by
        have h2 : a e₀ = e₀ * e₀ := mul_inv_eq_iff_eq_mul.mp h
        rw [h2, hs₂.sec_sq]
      have h2 : e₀ = 1 := by
        have h3 : a e₀ = a 1 := by rw [h1, map_one]
        exact a.injective h3
      rw [h2, map_one]
  have ha2 : a * a = 1 := by
    refine MulEquiv.ext fun w => ?_
    show a (a w) = w
    rcases he w with h | h
    · have h1 : a w = w := mul_inv_eq_one.1 h
      rw [h1, h1]
    · have h1 : a w = e₀ * w := mul_inv_eq_iff_eq_mul.mp h
      rw [h1, map_mul, he₀a, h1, ← mul_assoc, hs₂.sec_sq, one_mul]
  set A : Subgroup (MulAut (Sec (⊤ : Subgroup ↥X₂) (X₁.subgroupOf X₂))) :=
    Subgroup.zpowers a with hAdef
  have haG : a ∈ autSec (autOn H X₂) ⊤ (X₁.subgroupOf X₂) :=
    (hs₂.mem_autSec_iff le_rfl).2 ⟨⟨f, hfH⟩, hfH, rfl⟩
  have hAG : A ≤ autSec (autOn H X₂) ⊤ (X₁.subgroupOf X₂) := (Subgroup.zpowers_le).2 haG
  have hA1 : A ≠ ⊥ := fun h => ha1 (by
    have : a ∈ A := Subgroup.mem_zpowers a
    rwa [h, Subgroup.mem_bot] at this)
  have hsq : a ^ 2 = 1 := by rw [pow_two]; exact ha2
  have hAe : IsElemAbelian2 A := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsq, one_zpow]
  have hcard : Nat.card A = 2 := by
    rw [hAdef, Nat.card_zpowers, orderOf_eq_prime hsq ha1]
  have hV : ∀ v : Sec (⊤ : Subgroup ↥X₂) (X₁.subgroupOf X₂), v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact hs₂.sec_sq v
  obtain ⟨h8, -, -⟩ := A6G2.offender_eq hV (hs₂.autSec_le hs₂.hKH le_rfl)
    hs₂.autSec_le_normalizer hs₂.inf_centralizer_le (hs₂.b42TypeU33 hU) (hs₂.fixV_eq_bot hirr)
    hAG hA1 hAe (by rw [hcard]; exact hidx)
  omega

theorem le_pCoreOf_of_transvU33
    (hU : IsPSU 3 3 1 ↥(S.KSt H K)) (hperf : ⁅K, K⁆ = K) {F : Subgroup G} (hFH : F ≤ H) {z : G}
    (hz : ∀ f ∈ F, ∀ x ∈ X, f * x * f⁻¹ * x⁻¹ ∈ W ∨ f * x * f⁻¹ * x⁻¹ * z⁻¹ ∈ W) :
    F ≤ pCoreOf 2 H := fun f hf => hs.mem_pCoreOf_of_transvU33 hU hperf (hFH hf) (hz f hf)

end SecHyp

end Setting4

end CFSG.Quasithin.H13.A6
