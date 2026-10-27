module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Goldschmidt
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4ZCentralizer
import CFSG.Quasithin.Recognition.Stroth.Str83RqT6
import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexL2
import CFSG.Quasithin.Recognition.Stroth.Str83RqTorus
import CFSG.Quasithin.Recognition.Stroth.Str83RqTrackVertex
import CFSG.Quasithin.Recognition.Stroth.Str83Moufang
import CFSG.Quasithin.Vol2.Ch10SecQ3CQ
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.Quasithin.Background.B1MoreTwelveA

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

private theorem brh_exists_of_card {S Q A B : Subgroup G} {x : G} (hSA : S ≤ A) (hSB : S ≤ B)
    (hxA : x ∈ A) (hxB : x ∉ B) (hwd : ∀ q ∈ Q, x⁻¹ * q * x ∈ B)
    (hinj : ∀ s ∈ S, x⁻¹ * s * x ∈ B → s ∈ Q) (hcard : B.relIndex A ≤ Q.relIndex S + 1)
    {g : G} (hg : g ∈ A) (hgB : g ∉ B) : ∃ s ∈ S, (s * x)⁻¹ * g ∈ B := by
  classical
  let φ : ↥S ⧸ Q.subgroupOf S → ↥A ⧸ B.subgroupOf A :=
    Quotient.map' (fun s : S => (⟨(s : G) * x, A.mul_mem (hSA s.2) hxA⟩ : A)) (by
      intro s₁ s₂ h
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      convert hwd _ h using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      group)
  have hφ : ∀ s : S, φ (s : ↥S ⧸ Q.subgroupOf S) =
      ((⟨(s : G) * x, A.mul_mem (hSA s.2) hxA⟩ : A) : ↥A ⧸ B.subgroupOf A) := fun s => rfl
  have hinjφ : Function.Injective φ := by
    intro q₁ q₂ hq
    induction q₁ using QuotientGroup.induction_on with
    | H s₁ =>
      induction q₂ using QuotientGroup.induction_on with
      | H s₂ =>
        rw [hφ, hφ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at hq ⊢
        refine hinj _ (S.mul_mem (S.inv_mem s₁.2) s₂.2) ?_
        convert hq using 1
        group
  have hne : ∀ q, φ q ≠ ((1 : A) : ↥A ⧸ B.subgroupOf A) := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H s =>
      rw [hφ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, OneMemClass.coe_one,
        mul_one] at hq
      apply hxB
      have h := B.mul_mem (B.inv_mem (hSB s.2)) (B.inv_mem hq)
      convert h using 1
      group
  let ψ : Option (↥S ⧸ Q.subgroupOf S) → ↥A ⧸ B.subgroupOf A :=
    fun o => o.elim ((1 : A) : ↥A ⧸ B.subgroupOf A) φ
  have hψ : Function.Injective ψ := by
    rintro (_ | q₁) (_ | q₂) h
    · rfl
    · exact (hne q₂ h.symm).elim
    · exact (hne q₁ h).elim
    · exact congrArg some (hinjφ h)
  have hcardA : Nat.card (↥A ⧸ B.subgroupOf A) = B.relIndex A := rfl
  have hcardS : Nat.card (↥S ⧸ Q.subgroupOf S) = Q.relIndex S := rfl
  have hbij : Function.Bijective ψ := hψ.bijective_of_nat_card_le (by
    rw [Finite.card_option, hcardA, hcardS]
    exact hcard)
  obtain ⟨o, ho⟩ := hbij.2 ((⟨g, hg⟩ : A) : ↥A ⧸ B.subgroupOf A)
  cases o with
  | none =>
    exfalso
    change ((1 : A) : ↥A ⧸ B.subgroupOf A) = ((⟨g, hg⟩ : A) : ↥A ⧸ B.subgroupOf A) at ho
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at ho
    apply hgB
    simpa using ho
  | some q =>
    induction q using QuotientGroup.induction_on with
    | H s =>
      refine ⟨s, s.2, ?_⟩
      change φ (s : ↥S ⧸ Q.subgroupOf S) = ((⟨g, hg⟩ : A) : ↥A ⧸ B.subgroupOf A) at ho
      rw [hφ, QuotientGroup.eq, Subgroup.mem_subgroupOf] at ho
      simpa using ho

section TorusTransitive

open CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement MatrixGroups
open CFSG.Quasithin.RonanF13 (HallTwoPrime)

private theorem l2c_tt_inf_sup_eq {f : ℕ} (hf : 2 ≤ f) (U : Sylow 2 (PSL(2, GaloisField 2 f)))
    {D' : Subgroup (PSL(2, GaloisField 2 f))} (hD'card : Nat.card D' = 2 ^ f - 1)
    (hD'N : D' ≤ Subgroup.normalizer ((U : Subgroup (PSL(2, GaloisField 2 f))) : Set _)) :
    D' ⊓ (U : Subgroup (PSL(2, GaloisField 2 f))) = ⊥ ∧
      D' ⊔ (U : Subgroup (PSL(2, GaloisField 2 f))) =
        Subgroup.normalizer ((U : Subgroup (PSL(2, GaloisField 2 f))) : Set _) := by
  classical
  set V : Subgroup (PSL(2, GaloisField 2 f)) := (U : Subgroup (PSL(2, GaloisField 2 f)))
    with hVdef
  have hVcard : Nat.card V = 2 ^ f := St84.psl2_sylow_two_card (by omega) U
  have hdisj : D' ⊓ V = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hD'card, hVcard]
    exact (Nat.Even.sub_odd (Nat.one_le_two_pow)
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one).coprime_two_right.pow_right f
  have hNcardU : Nat.card (Subgroup.normalizer (V : Set (PSL(2, GaloisField 2 f)))) =
      2 ^ f * (2 ^ f - 1) :=
    CFSG.Walter.psl2_even_card_normalizer_sylow_two (f := f) (by omega) U
  refine ⟨hdisj, Subgroup.eq_of_le_of_card_ge (sup_le hD'N Subgroup.le_normalizer) ?_⟩
  have hrel := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer
    (H := D') (K := V) hD'N).2
  have h1 := Subgroup.relIndex_mul_card (H := V) (K := D' ⊔ V)
  rw [hrel, hdisj, Subgroup.relIndex_bot_left,
    inf_eq_left.mpr (le_sup_right : V ≤ D' ⊔ V)] at h1
  rw [← h1, hD'card, hVcard, hNcardU]
  exact Nat.le_of_eq (mul_comm _ _)

private theorem l2c_exists_conj_mem_of_torus_of_l2 {L T D : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD : HallTwoPrime D (L ⊓ Subgroup.normalizer (T : Set G))) {u u' : G} (hu : u ∈ T)
    (hu' : u' ∈ T) (hu1 : u ∉ pCoreOf 2 L) (hu1' : u' ∉ pCoreOf 2 L) :
    ∃ d ∈ D, (d * u * d⁻¹)⁻¹ * u' ∈ pCoreOf 2 L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ L := hT.le
  let Tq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L T
  let Dq : Subgroup (oTwoQuot ↥L) := imageOTwoQuot L D
  have hDL : D ≤ L := hD.1.trans inf_le_left
  have hDcard : Nat.card D = 2 ^ f - 1 :=
    card_hallTwoPrime_eq_l2 (L := L) (T := T) (D := D) (f := f) hf hL2 hT hD
  have hDqcard : Nat.card Dq = 2 ^ f - 1 := by
    rw [QA12.card_image_of_odd hDL hD.2.1, hDcard]
  obtain ⟨S, hScoe⟩ := exists_sylow_imageOTwoQuot hT
  obtain ⟨e⟩ := hL2
  let U : Sylow 2 (PSL(2, GaloisField 2 f)) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hUcoe : (U : Subgroup (PSL(2, GaloisField 2 f))) = Tq.map e.toMonoidHom := by
    have h := Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
    simpa [U, Tq, hScoe] using h
  let D' : Subgroup (PSL(2, GaloisField 2 f)) := Dq.map e.toMonoidHom
  have hD'card : Nat.card D' = 2 ^ f - 1 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hDqcard]
  have hNDq : Dq ≤ Subgroup.normalizer (Tq : Set (oTwoQuot ↥L)) := by
    rw [show Subgroup.normalizer (Tq : Set (oTwoQuot ↥L)) =
      imageOTwoQuot L (L ⊓ Subgroup.normalizer (T : Set G)) from
        QA12.normalizer_image_eq hTL hT.pCoreOf_le]
    exact imageOTwoQuot_mono hD.1
  have hD'N : D' ≤ Subgroup.normalizer ((U : Subgroup (PSL(2, GaloisField 2 f))) : Set _) := by
    have h := Subgroup.map_mono (f := e.toMonoidHom) hNDq
    rw [Subgroup.map_equiv_normalizer_eq] at h
    rw [← hUcoe] at h
    exact h
  obtain ⟨hdisj, hsup⟩ := l2c_tt_inf_sup_eq hf U hD'card hD'N
  let x : ↥L := ⟨u, hTL hu⟩
  let x' : ↥L := ⟨u', hTL hu'⟩
  have hxU : e (QuotientGroup.mk x) ∈ (U : Subgroup (PSL(2, GaloisField 2 f))) := by
    rw [hUcoe]
    exact Subgroup.mem_map_of_mem e.toMonoidHom (mem_imageOTwoQuot_iff.mpr ⟨u, hTL hu, hu, rfl⟩)
  have hx'U : e (QuotientGroup.mk x') ∈ (U : Subgroup (PSL(2, GaloisField 2 f))) := by
    rw [hUcoe]
    exact Subgroup.mem_map_of_mem e.toMonoidHom
      (mem_imageOTwoQuot_iff.mpr ⟨u', hTL hu', hu', rfl⟩)
  have hx1 : e (QuotientGroup.mk x) ≠ 1 := by
    intro h
    apply hu1
    rw [← map_one e] at h
    exact (mk_eq_one_iff_mem_pCoreOf x).mp (e.injective h)
  have hx1' : e (QuotientGroup.mk x') ≠ 1 := by
    intro h
    apply hu1'
    rw [← map_one e] at h
    exact (mk_eq_one_iff_mem_pCoreOf x').mp (e.injective h)
  obtain ⟨d', hd'D', hd'⟩ :=
    St84.psl2_torus_regular_on_sylow hf hdisj hsup _ hxU hx1 _ hx'U hx1'
  obtain ⟨dq, hdq, hdqe⟩ := Subgroup.mem_map.mp hd'D'
  obtain ⟨d, hdL, hdD, hdmk⟩ := mem_imageOTwoQuot_iff.mp hdq
  refine ⟨d, hdD, ?_⟩
  let y : ↥L := ((⟨d, hdL⟩ : ↥L) * x * (⟨d, hdL⟩ : ↥L)⁻¹)⁻¹ * x'
  have hy : (QuotientGroup.mk y : oTwoQuot ↥L) = 1 := by
    apply e.injective
    have hdqe' : e dq = d' := hdqe
    rw [map_one]
    simp only [y, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    rw [hdmk, hdqe', hd', inv_mul_cancel]
  exact (mk_eq_one_iff_mem_pCoreOf y).mp hy

end TorusTransitive

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem brh_S_le_B {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    S ≤ t.Gv 0 ⊓ t.Gv 1 := by
  have h := t.Gw_add_one 0
  rw [zero_add] at h
  rw [← h, t.Gw_zero_one hfr.hF, ← t.sup_K_eq_bigB]
  exact le_sup_left

private theorem brh_Q_le_S {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ S := by
  rw [t.Qv_one]
  exact Q2_le_S hfr.hF

private theorem brh_Q_le_B {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ t.Gv 0 ⊓ t.Gv 1 :=
  (t.brh_Q_le_S hfr).trans (t.brh_S_le_B hfr)

private theorem brh_relIndex_Q_S {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : (t.Qv 1).relIndex S = 2 ^ f := by
  have h := (t.relIndex_Qv_pCoreOf hfr 1).1
  rw [sub_self, t.pCoreOf_Gw_zero_one hfr, if_neg Int.not_even_one] at h
  exact h

private theorem brh_relIndex_B {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : (t.Gv 0 ⊓ t.Gv 1).relIndex (t.Gv 1) = 2 ^ f + 1 := by
  have hf0 : f ≠ 0 := by have := hfr.hf; omega
  have h := t.Gw_add_one 0
  rw [zero_add] at h
  rw [← h, t.Gw_zero_one hfr.hF, t.Gv_one]
  exact f112_relIndex_right_l2 hfr.hF hf0 hfr.hL2

private theorem brh_S_inf_Gv_two {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : S ⊓ t.Gv 2 ≤ t.Qv 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 S := hfr.hF.1.h1.pgroup
  refine t.le_Qv_of_le_Gw hfr (u := 0) (w := 2) (j := 1) (by norm_num) (by norm_num)
    (hSp.to_le inf_le_left) ?_
  rintro y ⟨hyS, hy2⟩
  have hyB := t.brh_S_le_B hfr hyS
  refine mem_win_iff.mpr fun i h1 h2 => ?_
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
  · exact hyB.1
  · exact hyB.2
  · exact hy2

private theorem brh_exists_S {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {g : G} (hg : g ∈ t.Gv 1) (hg0 : g ∉ t.Gv 0) :
    ∃ s ∈ S, (s * t.x₂)⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 1 := by
  have hx₂N : t.x₂ ∈ normalizer (t.Qv 1 : Set G) := t.Gv_le_normalizer_Qv 1 t.x₂_mem_Gv_one
  refine brh_exists_of_card (Q := t.Qv 1) ((t.brh_S_le_B hfr).trans inf_le_right)
    (t.brh_S_le_B hfr) t.x₂_mem_Gv_one (fun h => t.x₂_not_mem_Gv_zero h.1) ?_ ?_ ?_ hg
    (fun h => hg0 h.1)
  · intro q hq
    have h := (mem_normalizer_iff.mp (inv_mem hx₂N) q).mp hq
    rw [inv_inv] at h
    exact t.brh_Q_le_B hfr h
  · intro s hs hsB
    refine t.brh_S_inf_Gv_two hfr ⟨hs, ?_⟩
    have h0 := t.map_Gv_x₂ 0
    rw [show (2 : ℤ) - 0 = 2 by norm_num] at h0
    rw [← h0]
    exact mem_map_conj_iff.mpr hsB.1
  · rw [t.brh_relIndex_B hfr, t.brh_relIndex_Q_S hfr]

private theorem l2c_exists_inf_L2_mul_x₂ {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {g : G} (hg : g ∈ t.Gv 1) (hg0 : g ∉ t.Gv 0) :
    ∃ u ∈ S ⊓ L2, (u * t.x₂)⁻¹ * g ∈ t.Gv 0 := by
  obtain ⟨s, hs, hsg⟩ := t.brh_exists_S hfr hg hg0
  have hTN : S ⊓ L2 ≤ normalizer (Q2 L1 L2 S : Set G) := by
    rw [← t.Qv_one]
    exact (inf_le_left.trans ((t.brh_S_le_B hfr).trans inf_le_right)).trans
      (t.Gv_le_normalizer_Qv 1)
  have hs' : s ∈ (S ⊓ L2) ⊔ Q2 L1 L2 S := by
    rw [← S_eq_sup_right hfr]
    exact hs
  obtain ⟨u, hu, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hTN).mp hs'
  refine ⟨u, hu, ?_⟩
  have hq1 : q ∈ t.Qv 1 := by rw [t.Qv_one]; exact hq
  have hx₂N : t.x₂ ∈ normalizer (t.Qv 1 : Set G) := t.Gv_le_normalizer_Qv 1 t.x₂_mem_Gv_one
  have hqx : t.x₂⁻¹ * q * t.x₂ ∈ t.Gv 0 := by
    have h := (mem_normalizer_iff.mp (inv_mem hx₂N) q).mp hq1
    rw [inv_inv] at h
    exact (t.brh_Q_le_B hfr h).1
  have e : (u * t.x₂)⁻¹ * g = (t.x₂⁻¹ * q * t.x₂) * ((u * q * t.x₂)⁻¹ * g) := by group
  rw [e]
  exact mul_mem hqx hsg.1

private theorem l2c_Gv_inf_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Gv 0 ⊓ t.Gv 1 = S ⊔ t.K := by
  have h := t.Gw_add_one 0
  rw [zero_add] at h
  rw [← h, t.Gw_zero_one hfr.hF, t.sup_K_eq_bigB]

private theorem l2c_K_le_normalizer_S {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.K ≤ normalizer (S : Set G) :=
  le_sup_right.trans (t.sup_K_eq_bigB.le.trans hfr.hN)

private theorem l2c_Q_le_S {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.Qv 1 ≤ S := by
  rw [t.Qv_one]
  exact Q2_le_S hfr.hF

private theorem l2c_Q_le_Gv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ t.Gv 0 := by
  have h := (t.Qv_le_Gv hfr 1).1
  simpa using h

private theorem l2c_Q_le_Gv_two {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.Qv 1 ≤ t.Gv 2 := by
  have h := (t.Qv_le_Gv hfr 1).2
  simpa using h

private theorem l2c_conj_mem {H : Subgroup G} {g y : G} (hg : g ∈ normalizer (H : Set G))
    (hy : y ∈ H) : g * y * g⁻¹ ∈ H :=
  (mem_normalizer_iff.mp hg y).mp hy

private theorem l2c_conj_inv_mem {H : Subgroup G} {g y : G} (hg : g ∈ normalizer (H : Set G))
    (hy : y ∈ H) : g⁻¹ * y * g ∈ H := by
  have := l2c_conj_mem (inv_mem hg) hy
  rwa [inv_inv] at this

private theorem l2c_mem_Q_of_pow_eq_one {x : G} (hx : x ∈ t.Qv 1 ⊔ t.K) {j : ℕ}
    (hxj : x ^ 2 ^ j = 1) : x ∈ t.Qv 1 := by
  have hKQ : t.K ≤ normalizer (t.Qv 1 : Set G) := t.K_le_normalizer_Qv 1
  obtain ⟨q, hq, k, hk, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hKQ).1 hx
  have hkodd : Odd (orderOf k) :=
    t.hHall.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
  obtain ⟨q', hq', h⟩ := A4.exists_pow_mul_eq hq (hKQ hk) (2 ^ j)
  rw [hxj] at h
  have hkj : k ^ 2 ^ j ∈ t.Qv 1 := by
    have : k ^ 2 ^ j = q'⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    rw [this]
    exact inv_mem hq'
  exact mul_mem hq (B1Red.mem_of_two_pow_mem_of_odd hkj hkodd)

private theorem l2c_inf_B_le {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {H : Subgroup G} (hH : H ≤ t.Gv 1) (hK : t.K ≤ H) (hHS : H ⊓ S ≤ t.Qv 1) :
    (H ⊔ t.Qv 1) ⊓ (t.Gv 0 ⊓ t.Gv 1) ≤ t.Qv 1 ⊔ t.K := by
  intro x ⟨hxH, hxB⟩
  rw [t.l2c_Gv_inf_eq hfr] at hxB
  obtain ⟨s, hs, k, hk, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (t.l2c_K_le_normalizer_S hfr)).1 hxB
  have hQH : H ≤ normalizer (t.Qv 1 : Set G) := hH.trans (t.Gv_le_normalizer_Qv 1)
  have hsHQ : s ∈ H ⊔ t.Qv 1 := by
    have : s = (s * k) * k⁻¹ := by group
    rw [this]
    exact mul_mem hxH (mem_sup_left (inv_mem (hK hk)))
  rw [sup_comm] at hsHQ
  obtain ⟨q, hq, h, hh, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hQH).1 hsHQ
  have hhS : h ∈ S := by
    have : h = q⁻¹ * (q * h) := by group
    rw [this]
    exact mul_mem (inv_mem (t.l2c_Q_le_S hfr hq)) hs
  have hhQ : h ∈ t.Qv 1 := hHS ⟨hh, hhS⟩
  exact mul_mem (mem_sup_left (mul_mem hq hhQ)) (mem_sup_right hk)

private theorem l2c_conj_x₂_inv_mem {y : G} (hy : y ∈ t.Gv 1 ⊓ t.Gv 2) :
    t.x₂⁻¹ * y * t.x₂ ∈ t.Gv 0 ⊓ t.Gv 1 := by
  have h1 := t.map_Gv_x₂ 1
  have h0 := t.map_Gv_x₂ 0
  rw [show (2 : ℤ) - 1 = 1 by norm_num] at h1
  rw [show (2 : ℤ) - 0 = 2 by norm_num] at h0
  refine ⟨?_, ?_⟩
  · have := hy.2
    rw [← h0] at this
    exact mem_map_conj_iff.mp this
  · have := hy.1
    rw [← h1] at this
    exact mem_map_conj_iff.mp this

private theorem l2c_two_elt_mem {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 1) (hK : t.K ≤ H)
    (htr : CosetTrans H (t.Gv 1) (t.Gv 0)) (hHS : H ⊓ S ≤ t.Qv 1) {u : G}
    (hu : u ∈ H ⊔ t.Qv 1) {j : ℕ} (huj : u ^ 2 ^ j = 1) : u ∈ t.Qv 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHQ1 : H ⊔ t.Qv 1 ≤ t.Gv 1 := sup_le hH (t.Qv_le_Gv_self 1)
  have hP : IsPGroup 2 (zpowers u) := by
    have hdvd : orderOf u ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one huj
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hPle : zpowers u ≤ t.Gv 1 := (zpowers_le.mpr hu).trans hHQ1
  obtain ⟨g, hg, hPg⟩ := t.exists_le_conj_of_isPGroup hfr 1 hP hPle
  have hgx : g * t.x₂ ∈ t.Gv 1 := mul_mem hg t.x₂_mem_Gv_one
  obtain ⟨n, ⟨hnH, hn1⟩, hc⟩ := htr (g * t.x₂) hgx
  have hc1 : n⁻¹ * (g * t.x₂) ∈ t.Gv 1 := mul_mem (inv_mem hn1) hgx
  have hcB : n⁻¹ * (g * t.x₂) ∈ t.Gv 0 ⊓ t.Gv 1 := ⟨hc, hc1⟩
  have hu12 : g⁻¹ * u * g ∈ t.Gv 1 ⊓ t.Gv 2 := by
    have := mem_map_conj_iff.mp (hPg (mem_zpowers u))
    simpa using this
  have hw := t.l2c_conj_x₂_inv_mem hu12
  set c : G := n⁻¹ * (g * t.x₂) with hcdef
  have hnu : n⁻¹ * u * n = c * (t.x₂⁻¹ * (g⁻¹ * u * g) * t.x₂) * c⁻¹ := by
    rw [hcdef]; group
  have hnuB : n⁻¹ * u * n ∈ t.Gv 0 ⊓ t.Gv 1 := by
    rw [hnu]
    exact mul_mem (mul_mem hcB hw) (inv_mem hcB)
  have hnuH : n⁻¹ * u * n ∈ H ⊔ t.Qv 1 :=
    mul_mem (mul_mem (mem_sup_left (inv_mem hnH)) hu) (mem_sup_left hnH)
  have hnuQK := t.l2c_inf_B_le hfr hH hK hHS ⟨hnuH, hnuB⟩
  have hnuj : (n⁻¹ * u * n) ^ 2 ^ j = 1 := by
    have h := conj_pow (a := n⁻¹) (b := u) (i := 2 ^ j)
    rw [inv_inv] at h
    rw [h, huj]; group
  have hnuQ := t.l2c_mem_Q_of_pow_eq_one hnuQK hnuj
  have hnN : n ∈ normalizer (t.Qv 1 : Set G) := t.Gv_le_normalizer_Qv 1 hn1
  have := l2c_conj_mem hnN hnuQ
  simpa [mul_assoc] using this

private theorem l2c_exists_mem_not_mem {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 1) (hK : t.K ≤ H)
    (htr : CosetTrans H (t.Gv 1) (t.Gv 0)) : ∃ h ∈ H ⊓ S, h ∉ t.Qv 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hHS : H ⊓ S ≤ t.Qv 1 := fun h hh => hcon h hh
  set Q := t.Qv 1 with hQdef
  obtain ⟨n, ⟨hnH, hn1⟩, hb0⟩ := htr t.x₂ t.x₂_mem_Gv_one
  have hb1 : n⁻¹ * t.x₂ ∈ t.Gv 1 := mul_mem (inv_mem hn1) t.x₂_mem_Gv_one
  have hbB : n⁻¹ * t.x₂ ∈ t.Gv 0 ⊓ t.Gv 1 := ⟨hb0, hb1⟩
  set b : G := n⁻¹ * t.x₂ with hbdef
  have hnb : n = t.x₂ * b⁻¹ := by rw [hbdef]; group
  have hQK2 : Q ⊔ t.K ≤ t.Gv 1 ⊓ t.Gv 2 :=
    sup_le (le_inf (t.Qv_le_Gv_self 1) (t.l2c_Q_le_Gv_two hfr))
      (le_inf (t.K_le_Gv 1) (t.K_le_Gv 2))
  have hle : Q ⊔ t.K ≤ (Q ⊔ t.K).map (MulAut.conj n).toMonoidHom := by
    intro y hy
    refine mem_map_conj_iff.mpr ?_
    have hyH : n⁻¹ * y * n ∈ H ⊔ Q := by
      have hyHQ : y ∈ H ⊔ Q := (sup_le le_sup_right (hK.trans le_sup_left)) hy
      exact mul_mem (mul_mem (mem_sup_left (inv_mem hnH)) hyHQ) (mem_sup_left hnH)
    have hyB : n⁻¹ * y * n ∈ t.Gv 0 ⊓ t.Gv 1 := by
      have h1 := t.l2c_conj_x₂_inv_mem (hQK2 hy)
      have : n⁻¹ * y * n = b * (t.x₂⁻¹ * y * t.x₂) * b⁻¹ := by rw [hnb]; group
      rw [this]
      exact mul_mem (mul_mem hbB h1) (inv_mem hbB)
    exact t.l2c_inf_B_le hfr hH hK hHS ⟨hyH, hyB⟩
  have hcard : Nat.card ((Q ⊔ t.K).map (MulAut.conj n).toMonoidHom) ≤ Nat.card ↥(Q ⊔ t.K) :=
    (Subgroup.card_map_of_injective (MulAut.conj n).injective).le
  have hM : Q ⊔ t.K = (Q ⊔ t.K).map (MulAut.conj n).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hnQ : n ∈ normalizer (Q : Set G) := t.Gv_le_normalizer_Qv 1 hn1
  have hQmap : Q.map (MulAut.conj n).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnQ
  have hsup : Q ⊔ t.K = Q ⊔ t.K.map (MulAut.conj n).toMonoidHom := by
    conv_lhs => rw [hM]
    rw [Subgroup.map_sup, hQmap]
  have hKo : Odd (Nat.card t.K) := t.hHall.2.1
  have hKno : Odd (Nat.card (t.K.map (MulAut.conj n).toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj n).injective]
  have hQp : IsPGroup 2 Q := t.isPGroup_Qv 1
  have hKQ : t.K ≤ normalizer (Q : Set G) := t.K_le_normalizer_Qv 1
  have hKnQ : t.K.map (MulAut.conj n).toMonoidHom ≤ normalizer (Q : Set G) :=
    (le_sup_right.trans hsup.symm.le).trans (sup_le Subgroup.le_normalizer hKQ)
  have hcop : ∀ {M : Subgroup G}, Odd (Nat.card M) → Q ⊓ M = ⊥ := by
    intro M hM
    obtain ⟨m, hm⟩ := hQp.exists_card_eq
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hM)
  obtain ⟨m, hmQ, hmK⟩ := Vol2.Ch10.SecB.C11AmS.exists_conj_of_complement hQp hKo hKQ hKnQ
    (hcop hKo) (hcop hKno) hsup
  set y : G := m * n with hydef
  have hyK : y ∈ normalizer (t.K : Set G) := by
    have e1 : t.K.map (MulAut.conj y).toMonoidHom =
        (t.K.map (MulAut.conj n).toMonoidHom).map (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp [hydef, mul_assoc]
    have e : t.K.map (MulAut.conj y).toMonoidHom = t.K := by
      rw [e1, hmK, Subgroup.map_map]
      conv_rhs => rw [← Subgroup.map_id t.K]
      congr 1
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr e
  have hmG0 : m ∈ t.Gv 0 := t.l2c_Q_le_Gv_zero hfr hmQ
  have hy1 : y ∈ t.Gv 1 := mul_mem (t.Qv_le_Gv_self 1 hmQ) hn1
  have hyP2 : y ∈ P2 L1 L2 S := by rw [← t.Gv_one]; exact hy1
  have hx₂0 : t.x₂ ∉ t.Gv 0 := t.x₂_not_mem_Gv_zero
  have hyn0 : y ∉ t.Gv 0 := by
    intro hy0
    apply hx₂0
    have hn0 : n ∈ t.Gv 0 := by
      have : n = m⁻¹ * y := by rw [hydef]; group
      rw [this]
      exact mul_mem (inv_mem hmG0) hy0
    have : t.x₂ = n * b := by rw [hbdef]; group
    rw [this]
    exact mul_mem hn0 hb0
  have hreg := t.track.reg₂
  have hya : t.x₂⁻¹ * y ∈ t.Gv 0 := by
    rcases hreg y hyP2 hyK with h | h
    · exact (hyn0 (by rw [t.Gv_zero]; exact h)).elim
    · rw [t.Gv_zero]; exact h
  have hyx : y * t.x₂ ∈ t.Gv 0 := by
    have hzP2 : y * t.x₂ ∈ P2 L1 L2 S := by
      rw [← t.Gv_one]; exact mul_mem hy1 t.x₂_mem_Gv_one
    rcases hreg (y * t.x₂) hzP2 (mul_mem hyK t.track.x₂_norm) with h | h
    · rw [t.Gv_zero]; exact h
    · exfalso
      apply hx₂0
      have h' : t.x₂⁻¹ * (y * t.x₂) ∈ t.Gv 0 := by rw [t.Gv_zero]; exact h
      have : t.x₂ = (t.x₂⁻¹ * y)⁻¹ * (t.x₂⁻¹ * (y * t.x₂)) := by group
      rw [this]
      exact mul_mem (inv_mem hya) h'
  have hyy : y * y ∈ t.Gv 0 := by
    have : y * y = (y * t.x₂) * (t.x₂⁻¹ * y) := by group
    rw [this]
    exact mul_mem hyx hya
  have hyHQ : y ∈ H ⊔ Q := mul_mem (mem_sup_right hmQ) (mem_sup_left hnH)
  obtain ⟨k, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hyo : (y ^ o) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hko, pow_orderOf_eq_one]
  have hyoQ : y ^ o ∈ Q :=
    t.l2c_two_elt_mem hfr hH hK htr hHS (pow_mem hyHQ o) hyo
  apply hyn0
  obtain ⟨i, rfl⟩ := ho
  have hyo0 : y ^ (2 * i + 1) ∈ t.Gv 0 := t.l2c_Q_le_Gv_zero hfr hyoQ
  have hy2i : (y * y) ^ i ∈ t.Gv 0 := pow_mem hyy i
  have hpow : y ^ (2 * i + 1) = (y * y) ^ i * y := by rw [pow_succ, pow_mul, sq]
  have : y = ((y * y) ^ i)⁻¹ * y ^ (2 * i + 1) := by rw [hpow]; group
  rw [this]
  exact mul_mem (inv_mem hy2i) hyo0

theorem L2_le_oTwoPrime_sup_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 1) (hK : t.K ≤ H)
    (htr : CosetTrans H (t.Gv 1) (t.Gv 0)) : L2 ≤ oTwoPrime H ⊔ t.Qv 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, ⟨hhH, hhS⟩, hhQ⟩ := t.l2c_exists_mem_not_mem hfr hH hK htr
  have hSp : IsPGroup 2 S := hfr.hF.1.h1.pgroup
  have hD2K : t.D2 ≤ t.K := le_sup_right
  set Y : Subgroup G := oTwoPrime H ⊓ S with hYdef
  have hYS : Y ≤ S := inf_le_right
  have hYD : t.D2 ≤ normalizer (Y : Set G) := by
    intro d hd
    exact A4.mem_normalizer_inf (le_normalizer_oTwoPrime H (hK (hD2K hd)))
      (t.l2c_K_le_normalizer_S hfr (hD2K hd))
  have hhY : h ∈ Y := by
    refine ⟨?_, hhS⟩
    have hP : IsPGroup 2 ↥(H ⊓ S) := hSp.to_le inf_le_right
    exact le_oTwoPrime_of_isPGroup hP inf_le_left ⟨hhH, hhS⟩
  have hYQ : ¬ Y ≤ t.Qv 1 := fun hle => hhQ (hle hhY)
  have hS := t.S_le_sup_Qv_one_of_torus hfr hYS hYD hYQ
  have hT : S ⊓ L2 ≤ oTwoPrime H ⊔ t.Qv 1 :=
    inf_le_left.trans (hS.trans (sup_le_sup_right inf_le_left _))
  obtain ⟨n, ⟨hnH, hn1⟩, hb0⟩ := htr t.x₂ t.x₂_mem_Gv_one
  have hb1 : n⁻¹ * t.x₂ ∈ t.Gv 1 := mul_mem (inv_mem hn1) t.x₂_mem_Gv_one
  have hbB : n⁻¹ * t.x₂ ∈ bigB L1 L2 S := by
    have h := t.Gw_add_one 0
    rw [zero_add] at h
    rw [← t.Gw_zero_one hfr.hF, h]
    exact ⟨hb0, hb1⟩
  have hBL2 : bigB L1 L2 S ≤ normalizer (L2 : Set G) := by
    rw [bigB]
    exact sup_le (sup_le hfr.hF.1.h2.borel_le
      ((F1.borelOf_le L2 S).trans
        (Subgroup.le_normalizer : L2 ≤ normalizer (L2 : Set G)))) hfr.hF.1.h2.normalizes
  have hbT : n⁻¹ * t.x₂ ∈ normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
    A4.mem_normalizer_inf (hfr.hN hbB) (hBL2 hbB)
  have hT' : (S ⊓ L2).map (MulAut.conj t.x₂).toMonoidHom ≤ oTwoPrime H ⊔ t.Qv 1 := by
    intro z hz
    have hz' := mem_map_conj_iff.mp hz
    have hw : (n⁻¹ * t.x₂) * (t.x₂⁻¹ * z * t.x₂) * (n⁻¹ * t.x₂)⁻¹ ∈ S ⊓ L2 :=
      l2c_conj_mem hbT hz'
    have hzn : z = n * ((n⁻¹ * t.x₂) * (t.x₂⁻¹ * z * t.x₂) * (n⁻¹ * t.x₂)⁻¹) * n⁻¹ := by group
    rw [hzn]
    have hnN : n ∈ normalizer ((oTwoPrime H ⊔ t.Qv 1 : Subgroup G) : Set G) :=
      F1.le_normalizer_sup (X := zpowers n)
        (zpowers_le.mpr (le_normalizer_oTwoPrime H hnH))
        (zpowers_le.mpr (t.Gv_le_normalizer_Qv 1 hn1)) (mem_zpowers n)
    exact l2c_conj_mem hnN (hT hw)
  have hQ2 : pCoreOf 2 L2 ≤ t.Qv 1 := by
    have h := Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1.symm
    rw [bigB_comm] at h
    rw [t.Qv_one]
    exact h
  have hfin := le_sup_pCoreOf_of_sylow_ne_of_l2 hfr.hf hfr.hL2 hfr.hF.1.h2.sylow
    (t.isSylowTwoOf_map_x₂ hfr) (t.inf_L2_ne_map_x₂ hfr) (hT.trans le_sup_left)
    (hT'.trans le_sup_left)
  exact hfin.trans (sup_le le_rfl (hQ2.trans le_sup_right))

theorem ArcL.LX_sup_Qv_one_eq {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hX : t.ArcL X) :
    t.LX X 1 ⊔ t.Qv 1 = L2 ⊔ t.Qv 1 := by
  have hH : t.MX X 1 ≤ t.Gv 1 := inf_le_right
  have hK : t.K ≤ t.MX X 1 := le_inf hX.K_le (t.K_le_Gv 1)
  have htr : CosetTrans (t.MX X 1) (t.Gv 1) (t.Gv 0) := by
    intro g hg
    obtain ⟨n, hn, hng⟩ := hX.trans₀ g hg
    exact ⟨n, ⟨hn, hn.2⟩, hng⟩
  refine le_antisymm (sup_le ?_ le_sup_right) ?_
  · rw [← t.oTwoPrime_Gv_one hfr]
    exact Subgroup.closure_mono fun x hx => ⟨hH hx.1, hx.2⟩
  · exact sup_le (t.L2_le_oTwoPrime_sup_Qv_one hfr hH hK htr) le_sup_right

theorem ArcL.L2_le_LX_sup_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hX : t.ArcL X) : L2 ≤ t.LX X 1 ⊔ t.Qv 1 := by
  rw [Track.ArcL.LX_sup_Qv_one_eq t hfr hX]
  exact le_sup_left

private theorem l2c_cosetTrans_two {H : Subgroup G} (htr : CosetTrans H (t.Gv 1) (t.Gv 0)) :
    CosetTrans H (t.Gv 1) (t.Gv (1 + 1)) := by
  intro g hg
  obtain ⟨n₂, ⟨hn₂H, hn₂1⟩, hc₂⟩ := htr t.x₂ t.x₂_mem_Gv_one
  obtain ⟨n, ⟨hnH, hn1⟩, hc⟩ := htr (g * t.x₂) (mul_mem hg t.x₂_mem_Gv_one)
  refine ⟨n * n₂⁻¹,
    ⟨H.mul_mem hnH (H.inv_mem hn₂H), (t.Gv 1).mul_mem hn1 ((t.Gv 1).inv_mem hn₂1)⟩, ?_⟩
  have hmem : (n₂⁻¹ * t.x₂)⁻¹ * (n⁻¹ * (g * t.x₂)) ∈ t.Gv 0 := mul_mem (inv_mem hc₂) hc
  have h0 := t.map_Gv_x₂ 0
  have e : (n * n₂⁻¹)⁻¹ * g =
      t.x₂ * ((n₂⁻¹ * t.x₂)⁻¹ * (n⁻¹ * (g * t.x₂))) * t.x₂⁻¹ := by group
  rw [e, show (1 : ℤ) + 1 = 2 - 0 by norm_num, ← h0]
  exact mem_map_conj_iff.mpr (by simpa [mul_assoc] using hmem)

theorem ArcL.pCoreOf_LX_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hX : t.ArcL X) :
    pCoreOf 2 (t.LX X 1) = t.EX X 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : t.MX X 1 ≤ t.Gv 1 := inf_le_right
  have htr : CosetTrans (t.MX X 1) (t.Gv 1) (t.Gv 0) := by
    intro g hg
    obtain ⟨n, hn, hng⟩ := hX.trans₀ g hg
    exact ⟨n, ⟨hn, hn.2⟩, hng⟩
  have hLM : t.LX X 1 ≤ t.MX X 1 := oTwoPrime_le _
  have hMO : t.MX X 1 ≤ normalizer (pCoreOf 2 (t.LX X 1) : Set G) :=
    (le_normalizer_oTwoPrime (t.MX X 1)).trans (normalizer_le_normalizer_pCoreOf 2 (t.LX X 1))
  refine le_antisymm ?_ ?_
  · have hOp : IsPGroup 2 (pCoreOf 2 (t.LX X 1)) := pCoreOf_isPGroup 2 _
    have hOM : pCoreOf 2 (t.LX X 1) ≤ t.MX X 1 := (pCoreOf_le 2 _).trans hLM
    have hOG := t.le_gnbr_of_cosetTrans hfr 1 hOp hOM hMO hH (t.l2c_cosetTrans_two htr)
    have hOL : pCoreOf 2 (t.LX X 1) ≤ L2 ⊔ t.Qv 1 := by
      rw [← t.oTwoPrime_Gv_one hfr]
      exact (pCoreOf_le 2 _).trans (Subgroup.closure_mono fun x hx => ⟨hH hx.1, hx.2⟩)
    have hOQ : pCoreOf 2 (t.LX X 1) ≤ t.Qv 1 := by
      rw [← t.sup_Qv_inf_Gnbr_one hfr]
      exact le_inf hOL hOG
    exact le_inf hOQ (hOM.trans inf_le_left)
  · have hEp : IsPGroup 2 (t.EX X 1) := (t.isPGroup_Qv 1).to_le inf_le_left
    have hEM : t.EX X 1 ≤ t.MX X 1 := le_inf inf_le_right (inf_le_left.trans (t.Qv_le_Gv_self 1))
    have hEL : t.EX X 1 ≤ t.LX X 1 := le_oTwoPrime_of_isPGroup hEp hEM
    have hLE : t.LX X 1 ≤ normalizer (t.EX X 1 : Set G) := fun l hl =>
      A4.mem_normalizer_inf (t.Gv_le_normalizer_Qv 1 (hH (hLM hl)))
        (Subgroup.le_normalizer (hLM hl).1)
    exact le_pCoreOf_of_le_normalizer 2 hEL hLE hEp

private theorem l2c_mem_pCore_iff {N : Subgroup G} (x : ↥N) :
    x ∈ pCore 2 ↥N ↔ (x : G) ∈ pCoreOf 2 N := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]

theorem ArcL.isL2Quot_LX_one {a f : ℕ} (hfr : Frame L1 L2 S a f)
    {X : Subgroup G} (hX : t.ArcL X) : IsL2Quot f (oTwoQuot ↥(t.LX X 1)) := by
  classical
  have hH : t.MX X 1 ≤ t.Gv 1 := inf_le_right
  have hAN : t.LX X 1 ≤ t.Lv 1 := by
    rw [t.Lv_one, ← t.Qv_one, ← t.oTwoPrime_Gv_one hfr]
    exact Subgroup.closure_mono fun x hx => ⟨hH hx.1, hx.2⟩
  have hNQ : t.Lv 1 = t.LX X 1 ⊔ t.Qv 1 := by
    rw [Track.ArcL.LX_sup_Qv_one_eq t hfr hX, t.Lv_one, t.Qv_one]
  have hAQ : t.LX X 1 ≤ normalizer (t.Qv 1 : Set G) :=
    ((oTwoPrime_le _).trans hH).trans (t.Gv_le_normalizer_Qv 1)
  have hO : pCoreOf 2 (t.Lv 1) = t.Qv 1 := t.pCoreOf_Lv hfr 1
  have hE := Track.ArcL.pCoreOf_LX_one t hfr hX
  let φ : ↥(t.LX X 1) →* oTwoQuot ↥(t.Lv 1) :=
    (QuotientGroup.mk' (pCore 2 ↥(t.Lv 1))).comp (Subgroup.inclusion hAN)
  have hφ : ∀ x : ↥(t.LX X 1), φ x = 1 ↔ (x : G) ∈ t.Qv 1 := by
    intro x
    rw [← hO]
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact l2c_mem_pCore_iff _
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥(t.Lv 1)) y
    have hn : (n : G) ∈ t.LX X 1 ⊔ t.Qv 1 := hNQ ▸ n.2
    obtain ⟨l, hl, q, hq, hlq⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer hAQ).mp hn
    refine ⟨⟨l, hl⟩, ?_⟩
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    apply (l2c_mem_pCore_iff _).mpr
    rw [hO]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [hlq]
    simpa using hq
  have hker : pCore 2 ↥(t.LX X 1) = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, hφ, l2c_mem_pCore_iff, hE]
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, ((oTwoPrime_le _) x.2).1⟩
  obtain ⟨e3⟩ := t.isL2Quot_Lv hfr (odd_one : Odd (1 : ℤ))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)).trans e3⟩

private theorem l2c_mem_normalizer_centralizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) :
    g ∈ normalizer ((centralizer (H : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ y ∈ centralizer (H : Set G),
      g * y * g⁻¹ ∈ centralizer (H : Set G) := by
    intro g hg y hy
    rw [mem_centralizer_iff] at hy ⊢
    intro h hh
    have hh' : g⁻¹ * h * g ∈ H := by
      have := (mem_normalizer_iff.mp (inv_mem hg) h).mp hh
      rwa [inv_inv] at this
    have hcomm := hy _ hh'
    calc h * (g * y * g⁻¹) = g * ((g⁻¹ * h * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm]
      _ = g * y * g⁻¹ * h := by group
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key g hg y hy, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

theorem ArcL.charTwo_LX_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hX : t.ArcL X) (hX2 : IsPGroup 2 X) :
    CharTwo (t.LX X 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := Track.ArcL.pCoreOf_LX_one t hfr hX
  have hH : t.MX X 1 ≤ t.Gv 1 := inf_le_right
  have hLG : t.LX X 1 ≤ t.Gv 1 := (oTwoPrime_le _).trans hH
  have hLN : t.LX X 1 ≤ normalizer (X : Set G) := (oTwoPrime_le _).trans inf_le_left
  have hLV : t.LX X 1 ≤ L2 ⊔ t.Qv 1 := by
    rw [← t.oTwoPrime_Gv_one hfr]
    exact Subgroup.closure_mono fun x hx => ⟨hH hx.1, hx.2⟩
  have hcov := Track.ArcL.L2_le_LX_sup_Qv_one t hfr hX
  unfold CharTwo
  rw [hE]
  set C : Subgroup G := t.LX X 1 ⊓ centralizer (t.EX X 1 : Set G) with hCdef
  have hLC : t.LX X 1 ≤ normalizer (C : Set G) := by
    intro l hl
    have hlE : l ∈ normalizer (t.EX X 1 : Set G) := by
      have h := le_normalizer_pCoreOf 2 (t.LX X 1)
      rw [hE] at h
      exact h hl
    exact A4.mem_normalizer_inf (Subgroup.le_normalizer hl) (l2c_mem_normalizer_centralizer hlE)
  rcases t.le_Qv_or_le_sup_of_le_normalizer_one hfr (inf_le_left.trans hLV) hcov hLC hLG with
    hQ | hL2
  · intro c hc
    exact ⟨hQ hc, hLN hc.1⟩
  · exfalso
    apply t.not_le_centralizer_sup_one hfr
    have hX0 : X ≤ t.Qv 0 := by
      have hXw : X ≤ t.Gw (-1) 1 := by
        intro x hx
        have hle := hX.le hx
        refine mem_win_iff.mpr fun i h1 h2 => ?_
        rcases (show i = -1 ∨ i = 0 ∨ i = 1 by omega) with rfl | rfl | rfl
        · exact hle.2
        · exact hle.1.2
        · exact hle.1.1
      exact t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0) (by norm_num) (by norm_num) hX2 hXw
    have hZE : t.Zv 0 ⊓ t.Qv 1 ≤ t.EX X 1 := by
      intro z hz
      refine ⟨hz.2, ?_⟩
      have hzc : z ∈ centralizer (t.Qv 0 : Set G) := t.Zv_le_centralizer 0 hz.1
      have hzX : z ∈ centralizer (X : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX0) hzc
      exact (Subgroup.centralizer_le_normalizer _) hzX
    calc L2 ≤ C ⊔ t.Qv 1 := hL2
      _ ≤ ((L2 ⊔ t.Qv 1) ⊓ centralizer ((t.Zv 0 ⊓ t.Qv 1 : Subgroup G) : Set G)) ⊔ t.Qv 1 :=
        sup_le_sup_right (le_inf (inf_le_left.trans hLV)
          (inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZE)))) _

private theorem l2c_x₂_mul_x₂_mem : t.x₂ * t.x₂ ∈ t.Gv 0 := by
  have hP2 : t.x₂ * t.x₂ ∈ P2 L1 L2 S := mul_mem t.track.x₂_mem t.track.x₂_mem
  have hN : t.x₂ * t.x₂ ∈ normalizer ((t.D1 ⊔ t.D2 : Subgroup G) : Set G) :=
    mul_mem t.track.x₂_norm t.track.x₂_norm
  rw [t.Gv_zero]
  rcases t.track.reg₂ _ hP2 hN with h | h
  · exact h
  · exact absurd (by simpa using h) t.track.x₂_not_mem

private theorem l2c_mem_Gv_two_iff {y : G} : y ∈ t.Gv 2 ↔ t.x₂⁻¹ * y * t.x₂ ∈ t.Gv 0 := by
  have h0 := t.map_Gv_x₂ 0
  rw [show (2 : ℤ) - 0 = 2 by norm_num] at h0
  rw [← h0]
  exact mem_map_conj_iff

private theorem l2c_pair_or_le_sup_core {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 1) (hK : t.K ≤ H) {s : G}
    (hs : s ∈ H) (hs2 : t.x₂⁻¹ * s ∈ t.Gv 0)
    (T1 : ∀ {g : G}, g ∈ t.Gv 1 → g ∉ t.Gv 0 → ∃ u ∈ S ⊓ L2, (u * t.x₂)⁻¹ * g ∈ t.Gv 0)
    (T2 : ∀ {u u' : G}, u ∈ S ⊓ L2 → u' ∈ S ⊓ L2 → u ∉ pCoreOf 2 L2 → u' ∉ pCoreOf 2 L2 →
      ∃ d ∈ t.D2, (d * u * d⁻¹)⁻¹ * u' ∈ pCoreOf 2 L2) :
    (∀ g ∈ H, g ∈ t.Gv 0 ⊓ t.Gv 2 ∨ t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2) ∨ L2 ≤ H ⊔ t.Qv 1 := by
  have hs0 : s ∉ t.Gv 0 := fun h => t.x₂_not_mem_Gv_zero (by
    have e : t.x₂ = s * (t.x₂⁻¹ * s)⁻¹ := by group
    rw [e]
    exact mul_mem h (inv_mem hs2))
  by_cases hA : ∀ g ∈ H, g ∈ t.Gv 0 ∨ t.x₂⁻¹ * g ∈ t.Gv 0
  · left
    intro g hg
    rcases hA g hg with h0 | h2
    · left
      refine ⟨h0, ?_⟩
      rcases hA (g * s) (mul_mem hg hs) with h | h
      · exact (hs0 (by
          have e : s = g⁻¹ * (g * s) := by group
          rw [e]
          exact mul_mem (inv_mem h0) h)).elim
      · show g ∈ t.Gv 2
        rw [t.l2c_mem_Gv_two_iff]
        have e : t.x₂⁻¹ * g * t.x₂ = (t.x₂⁻¹ * (g * s)) * (t.x₂⁻¹ * s)⁻¹ := by group
        rw [e]
        exact mul_mem h (inv_mem hs2)
    · right
      refine ⟨h2, ?_⟩
      rcases hA (g * s) (mul_mem hg hs) with h | h
      · show t.x₂⁻¹ * g ∈ t.Gv 2
        rw [t.l2c_mem_Gv_two_iff]
        have e : t.x₂⁻¹ * (t.x₂⁻¹ * g) * t.x₂ =
            (t.x₂ * t.x₂)⁻¹ * (g * s) * (t.x₂⁻¹ * s)⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem t.l2c_x₂_mul_x₂_mem) h) (inv_mem hs2)
      · exact (hs0 (by
          have e : s = (t.x₂⁻¹ * g)⁻¹ * (t.x₂⁻¹ * (g * s)) := by group
          rw [e]
          exact mul_mem (inv_mem h2) h)).elim
  · right
    push Not at hA
    obtain ⟨g, hg, hg0, hg2⟩ := hA
    have hQ2 : pCoreOf 2 L2 ≤ t.Qv 1 := by
      have h := Hyp111.pCoreOf_le_pCoreOf_vertex hfr.hF.1.symm
      rw [bigB_comm] at h
      rw [t.Qv_one]
      exact h
    have hQ1G0 : t.Qv 1 ≤ t.Gv 0 := t.l2c_Q_le_Gv_zero hfr
    have hx₂Q : t.x₂ ∈ normalizer (t.Qv 1 : Set G) := t.Gv_le_normalizer_Qv 1 t.x₂_mem_Gv_one
    have hnot : ∀ {g : G} {u : G}, (u * t.x₂)⁻¹ * g ∈ t.Gv 0 → t.x₂⁻¹ * g ∉ t.Gv 0 →
        u ∉ pCoreOf 2 L2 := by
      intro g u hc hg2 hu
      apply hg2
      have hux : t.x₂⁻¹ * u * t.x₂ ∈ t.Qv 1 := l2c_conj_inv_mem hx₂Q (hQ2 hu)
      have e : t.x₂⁻¹ * g = (t.x₂⁻¹ * u * t.x₂) * ((u * t.x₂)⁻¹ * g) := by group
      rw [e]
      exact mul_mem (hQ1G0 hux) hc
    have htr : CosetTrans H (t.Gv 1) (t.Gv 0) := by
      intro g' hg'
      by_cases h0 : g' ∈ t.Gv 0
      · exact ⟨1, ⟨H.one_mem, (t.Gv 1).one_mem⟩, by simpa using h0⟩
      by_cases h2 : t.x₂⁻¹ * g' ∈ t.Gv 0
      · refine ⟨s, ⟨hs, hH hs⟩, ?_⟩
        have e : s⁻¹ * g' = (t.x₂⁻¹ * s)⁻¹ * (t.x₂⁻¹ * g') := by group
        rw [e]
        exact mul_mem (inv_mem hs2) h2
      obtain ⟨u, hu, hgu⟩ := T1 (hH hg) hg0
      obtain ⟨u', hu', hgu'⟩ := T1 hg' h0
      obtain ⟨d, hd, hdu⟩ := T2 hu hu' (hnot hgu hg2) (hnot hgu' h2)
      have hdK : d ∈ t.K := (le_sup_right : t.D2 ≤ t.K) hd
      refine ⟨d * g, ⟨H.mul_mem (hK hdK) hg, (t.Gv 1).mul_mem (t.K_le_Gv 1 hdK) (hH hg)⟩, ?_⟩
      have hmid : d⁻¹ * ((d * u * d⁻¹)⁻¹ * u') ∈ t.Gv 2 :=
        mul_mem (inv_mem (t.K_le_Gv 2 hdK)) (t.l2c_Q_le_Gv_two hfr (hQ2 hdu))
      rw [t.l2c_mem_Gv_two_iff] at hmid
      have e : (d * g)⁻¹ * g' = ((u * t.x₂)⁻¹ * g)⁻¹ *
          (t.x₂⁻¹ * (d⁻¹ * ((d * u * d⁻¹)⁻¹ * u')) * t.x₂) * ((u' * t.x₂)⁻¹ * g') := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hgu) hmid) hgu'
    exact (t.L2_le_oTwoPrime_sup_Qv_one hfr hH hK htr).trans
      (sup_le_sup_right (oTwoPrime_le H) _)

theorem pair_or_le_sup_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {H : Subgroup G} (hH : H ≤ t.Gv 1) (hK : t.K ≤ H) {s : G}
    (hs : s ∈ H) (hs2 : t.x₂⁻¹ * s ∈ t.Gv 0) :
    (∀ g ∈ H, g ∈ t.Gv 0 ⊓ t.Gv 2 ∨ t.x₂⁻¹ * g ∈ t.Gv 0 ⊓ t.Gv 2) ∨ L2 ≤ H ⊔ t.Qv 1 := by
  exact t.l2c_pair_or_le_sup_core hfr hH hK hs hs2
    (fun hg hg0 => t.l2c_exists_inf_L2_mul_x₂ hfr hg hg0)
    (fun hu hu' h1 h1' => l2c_exists_conj_mem_of_torus_of_l2 hfr.hf hfr.hL2
      hfr.hF.1.h2.sylow t.hD2hall hu hu' h1 h1')

end Track

end CFSG.Quasithin.Stroth.Rq

end
