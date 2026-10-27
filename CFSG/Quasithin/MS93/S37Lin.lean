module

public import CFSG.Quasithin.MS93.S37Case
public import CFSG.Quasithin.MS93.MSPLevi

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Geo

variable {F : Type} [Field F]

theorem eq_id_of_sub_mem {f : V4 F →+ V4 F} {σ : F →+* F}
    (hσ : ∀ (c : F) (v : V4 F), f (c • v) = σ c • f v) {W : Submodule F (V4 F)} (hW : W ≠ ⊤)
    (hfW : ∀ v, f v - v ∈ W) : σ = RingHom.id F := by
  obtain ⟨v, hv⟩ : ∃ v, v ∉ W := by
    by_contra h
    push Not at h
    exact hW (eq_top_iff.2 fun v _ => h v)
  ext c
  have h3 : (σ c - c) • v ∈ W := by
    have e : (σ c - c) • v = (f (c • v) - c • v) - σ c • (f v - v) := by
      rw [hσ, smul_sub, sub_smul]
      abel
    rw [e]
    exact W.sub_mem (hfW (c • v)) (W.smul_mem _ (hfW v))
  by_contra hne
  have hne' : σ c - c ≠ 0 := fun h => hne (sub_eq_zero.1 h)
  apply hv
  have := W.smul_mem (σ c - c)⁻¹ h3
  rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this

theorem mulVec_eq_of_normalizes_xPoint [CharP F 2] {x : V4 F} (hx : x ≠ 0) {g : Sp4 F} {n : ℕ}
    (hg : g ^ 2 ^ n = 1) (hn : g ∈ Subgroup.normalizer (xPoint (F ∙ x) : Set (Sp4 F))) :
    mat g *ᵥ x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_xPoint (isPoint_span hx)] at hn
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1
    (mulVec_mem_of_mem_stab hn (Submodule.mem_span_singleton_self x))
  have hpow : ∀ m : ℕ, mat (g ^ m) *ᵥ x = l ^ m • x := by
    intro m
    induction m with
    | zero => simp [mat_one]
    | succ m ih =>
      rw [pow_succ, mat_mul_mulVec, ← hl, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have h1 : l ^ 2 ^ n • x = x := by rw [← hpow, hg, mat_one, Matrix.one_mulVec]
  have h2 : l ^ 2 ^ n = 1 := by
    have h3 : (l ^ 2 ^ n - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hx)
  have h4 : (l - 1) ^ 2 ^ n = 0 := by rw [sub_pow_char_pow, h2, one_pow, sub_self]
  rw [← hl, sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero n two_ne_zero)).1 h4), one_smul]

theorem commute_of_normalizes_xPoint [CharP F 2] {p : Submodule F (V4 F)} (hp : IsPoint p)
    {g : Sp4 F} {n : ℕ} (hg : g ^ 2 ^ n = 1)
    (hn : g ∈ Subgroup.normalizer (xPoint p : Set (Sp4 F))) {y : Sp4 F} (hy : y ∈ xPoint p) :
    g * y = y * g := by
  obtain ⟨x, hx, rfl⟩ := exists_eq_span_of_isPoint hp
  obtain ⟨c, rfl⟩ := (mem_xPoint_span hx).1 hy
  have h := transv_conj g x c
  rw [mulVec_eq_of_normalizes_xPoint hx hg hn] at h
  calc g * transv x c = g * transv x c * g⁻¹ * g := by group
    _ = transv x c * g := by rw [h]

end Geo

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

section Sub

variable {S : Subgroup G}

theorem crit_inv (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S)
    (hcrit : ¬ Uq M T L ≤ Qt M θ) : ¬ Uq M T L ≤ Qt M θ⁻¹ := by
  rw [C.le_Qt_iff hQS hST]
  intro h
  apply hcrit
  have h1 := tImage_mono' θ h
  rwa [tImage_tImage_inv' θ (C.Uq_le_S hQS)] at h1

theorem rhoIm_ne_bot (hQS : pCoreOf 2 M ≤ S) (hST : S ≤ T) (θ : MulAut ↥S)
    (hcrit : ¬ Uq M T L ≤ Qt M θ) (hU : Ut M T L θ ≤ T1 M T L) :
    C.rhoIm (Ut M T L θ) ≠ ⊥ := by
  intro hbot
  apply hcrit
  rw [C.le_Qt_iff hQS hST θ]
  intro x hx
  have hxK := (hU.trans T1_le_sup) hx
  have h1 : C.rho ⟨x, hxK⟩ ∈ C.rhoIm (Ut M T L θ) := (C.mem_rhoIm).2 ⟨x, hxK, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, C.rho_eq_one_iff] at h1
  exact h1

theorem comm_of_xPoint (hST : S ≤ T) (θ : MulAut ↥S) (hU : Ut M T L θ ≤ T1 M T L)
    {p : Submodule F (V4 F)} (hp : IsPoint p) (hE : C.rhoIm (Ut M T L θ) = xPoint p) {t : G}
    (ht : t ∈ T1 M T L) (htS : t ∈ S) {x : G} (hx : x ∈ Ut M T L θ) :
    ⁅t, x⁆ ∈ pCoreOf 2 M := by
  have : CharP F 2 := charP_of_card_eq_prime_pow C.hF
  have htK : t ∈ L ⊔ pCoreOf 2 M := T1_le_sup ht
  have hxK : x ∈ L ⊔ pCoreOf 2 M := T1_le_sup (hU hx)
  have hconj : ∀ {s : G} (hsS : s ∈ S) (hsK : s ∈ L ⊔ pCoreOf 2 M), ∀ y ∈ C.rhoIm (Ut M T L θ),
      C.rho ⟨s, hsK⟩ * y * (C.rho ⟨s, hsK⟩)⁻¹ ∈ C.rhoIm (Ut M T L θ) := by
    intro s hsS hsK y hy
    obtain ⟨z, hzK, hz, rfl⟩ := (C.mem_rhoIm).1 hy
    refine (C.mem_rhoIm).2 ⟨s * z * s⁻¹, (L ⊔ pCoreOf 2 M).mul_mem
      ((L ⊔ pCoreOf 2 M).mul_mem hsK hzK) ((L ⊔ pCoreOf 2 M).inv_mem hsK),
      C.conj_mem_Ut hST θ hsS hz, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hn : C.rho ⟨t, htK⟩ ∈ Subgroup.normalizer (xPoint p : Set (Sp4 F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← hE]
    refine ⟨hconj htS htK y, fun hy => ?_⟩
    have := hconj (S.inv_mem htS) ((L ⊔ pCoreOf 2 M).inv_mem htK) _ hy
    have e : (⟨t⁻¹, (L ⊔ pCoreOf 2 M).inv_mem htK⟩ : ↥(L ⊔ pCoreOf 2 M)) = ⟨t, htK⟩⁻¹ := rfl
    rw [e, map_inv, inv_inv] at this
    simpa [mul_assoc] using this
  obtain ⟨m, hm⟩ := C.h.isPGroup ⟨t, T1_le_T ht⟩
  have htm : (⟨t, htK⟩ : ↥(L ⊔ pCoreOf 2 M)) ^ 2 ^ m = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hm)
  have hρm : C.rho ⟨t, htK⟩ ^ 2 ^ m = 1 := by rw [← map_pow, htm, map_one]
  have hxE : C.rho ⟨x, hxK⟩ ∈ xPoint p := hE ▸ (C.mem_rhoIm).2 ⟨x, hxK, hx, rfl⟩
  have hcomm := commute_of_normalizes_xPoint hp hρm hn hxE
  have hc : ⁅t, x⁆ ∈ L ⊔ pCoreOf 2 M := by
    rw [commutatorElement_def]
    exact (L ⊔ pCoreOf 2 M).mul_mem ((L ⊔ pCoreOf 2 M).mul_mem
      ((L ⊔ pCoreOf 2 M).mul_mem htK hxK) ((L ⊔ pCoreOf 2 M).inv_mem htK))
      ((L ⊔ pCoreOf 2 M).inv_mem hxK)
  have e : (⟨⁅t, x⁆, hc⟩ : ↥(L ⊔ pCoreOf 2 M)) = ⁅(⟨t, htK⟩ : ↥(L ⊔ pCoreOf 2 M)), ⟨x, hxK⟩⁆ :=
    rfl
  rw [← C.rho_eq_one_iff ⟨_, hc⟩, e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hcomm

end Sub

theorem comm_of_abelian (hab : ∀ a ∈ C.T0bar, ∀ b ∈ C.T0bar, a * b = b * a) {t x : G}
    (ht : t ∈ T1 M T L) (hx : x ∈ T1 M T L) : ⁅t, x⁆ ∈ pCoreOf 2 M := by
  have hc : ⁅t, x⁆ ∈ T1 M T L := by
    rw [commutatorElement_def]
    exact (T1 M T L).mul_mem ((T1 M T L).mul_mem ((T1 M T L).mul_mem ht hx)
      ((T1 M T L).inv_mem ht)) ((T1 M T L).inv_mem hx)
  have e : (⟨⁅t, x⁆, hc⟩ : ↥(T1 M T L)) = ⁅(⟨t, ht⟩ : ↥(T1 M T L)), ⟨x, hx⟩⁆ := rfl
  rw [← C.rho1_eq_one_iff ⟨_, hc⟩, e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hab _ ⟨_, rfl⟩ _ ⟨_, rfl⟩

theorem act_sub_mem_of_comm (θ : MulAut ↥T) (hU' : Ut M T L θ⁻¹ ≤ T1 M T L) {t : G}
    (ht : t ∈ T) (hcomm : ∀ x ∈ Ut M T L θ, ⁅t, x⁆ ∈ pCoreOf 2 M) (v : V4 F) :
    C.act (C.h.le (θ⁻¹ ⟨t, ht⟩).2) v - v ∈ fixSp (C.rhoIm (Ut M T L θ⁻¹)) := by
  obtain ⟨u, rfl⟩ := C.N.co_surj v
  set s : G := ((θ⁻¹ ⟨t, ht⟩ : ↥T) : G) with hs
  have hsT : s ∈ T := (θ⁻¹ ⟨t, ht⟩).2
  have huT : (u : G) ∈ T := C.Uq_le_T u.2
  have hc : ⁅s, (u : G)⁆ ∈ Uq M T L := by
    rw [commutatorElement_def]
    exact (Uq M T L).mul_mem
      ((Subgroup.mem_normalizer_iff.1 (C.hMU (C.h.le hsT)) u).1 u.2) ((Uq M T L).inv_mem u.2)
  rw [← C.co_comm (C.h.le hsT) u.2 hc]
  refine (C.co_mem_fixSp_iff (hU'.trans T1_le_sup) ⟨_, hc⟩).2 ?_
  have hQ : ⁅s, (u : G)⁆ ∈ Qt M θ⁻¹ := by
    set θu : G := ((θ ⟨u, huT⟩ : ↥T) : G) with hθu
    have hθuU : θu ∈ Ut M T L θ := mem_tImage.2 ⟨u, huT, u.2, rfl⟩
    have hy := hcomm θu hθuU
    have hyT : ⁅t, θu⁆ ∈ T := by
      rw [commutatorElement_def]
      exact T.mul_mem (T.mul_mem (T.mul_mem ht (θ ⟨u, huT⟩).2) (T.inv_mem ht))
        (T.inv_mem (θ ⟨u, huT⟩).2)
    refine mem_tImage.2 ⟨_, hyT, hy, ?_⟩
    have e : (⟨⁅t, θu⁆, hyT⟩ : ↥T) = ⁅(⟨t, ht⟩ : ↥T), θ ⟨u, huT⟩⁆ := rfl
    rw [e, map_commutatorElement, MulAut.inv_apply_self]
    rfl
  rw [C.Qt_eq C.h.pCore_le le_rfl] at hQ
  exact hQ.2

theorem mem_T1_of_comm (θ : MulAut ↥T) (hcrit : ¬ Uq M T L ≤ Qt M θ)
    (hU' : Ut M T L θ⁻¹ ≤ T1 M T L) {t : G} (ht : t ∈ T)
    (hcomm : ∀ x ∈ Ut M T L θ, ⁅t, x⁆ ∈ pCoreOf 2 M) :
    ((θ⁻¹ ⟨t, ht⟩ : ↥T) : G) ∈ T1 M T L := by
  have hsT : ((θ⁻¹ ⟨t, ht⟩ : ↥T) : G) ∈ T := (θ⁻¹ ⟨t, ht⟩).2
  have hW : fixSp (C.rhoIm (Ut M T L θ⁻¹)) ≠ ⊤ := by
    rw [Ne, fixSp_eq_top_iff]
    exact C.rhoIm_ne_bot C.h.pCore_le le_rfl θ⁻¹ (C.crit_inv C.h.pCore_le le_rfl θ hcrit) hU'
  have hσ := eq_id_of_sub_mem (C.sig_spec (C.h.le hsT)) hW (C.act_sub_mem_of_comm θ hU' ht hcomm)
  exact ⟨hsT, C.mem_sup_of_linear hsT ((C.linear_iff (C.h.le hsT)).2 hσ)⟩

end Cfg

theorem tImage_T1_eq {M T L : Subgroup G} (θ : MulAut ↥T)
    (h : ∀ (t : G) (ht : t ∈ T1 M T L), ((θ⁻¹ ⟨t, T1_le_T ht⟩ : ↥T) : G) ∈ T1 M T L) :
    tImage θ⁻¹ (T1 M T L) = T1 M T L ∧ tImage θ (T1 M T L) = T1 M T L := by
  have hle : tImage θ⁻¹ (T1 M T L) ≤ T1 M T L := by
    intro x hx
    obtain ⟨y, hyT, hy, rfl⟩ := mem_tImage.1 hx
    exact h y hy
  have h1 : tImage θ⁻¹ (T1 M T L) = T1 M T L :=
    Subgroup.eq_of_le_of_card_ge hle (card_tImage θ⁻¹ T1_le_T).ge
  refine ⟨h1, ?_⟩
  calc tImage θ (T1 M T L) = tImage θ (tImage θ⁻¹ (T1 M T L)) := by rw [h1]
    _ = T1 M T L := tImage_tImage_inv' θ T1_le_T


end CFSG.Quasithin.MS93.S37
