module

public import CFSG.Quasithin.H13.L32AC52a
public import CFSG.Quasithin.H13.L32AC38c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

@[expose] def e27Of {X : Type*} [Group X] {P Q R : X} (hP : P ^ 3 = 1) (hQ : Q ^ 3 = 1)
    (hR : R ^ 3 = 1) (hPQ : Commute P Q) (hPR : Commute P R) (hQR : Commute Q R) :
    Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* X where
  toFun x := P ^ (Multiplicative.toAdd x).1.val *
    (Q ^ (Multiplicative.toAdd x).2.1.val * R ^ (Multiplicative.toAdd x).2.2.val)
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    rw [Lin.pow_val_add3 hP, Lin.pow_val_add3 hQ, Lin.pow_val_add3 hR]
    exact Lin.mul_mul_three hPQ hPR hQR _ _ _ _ _ _

theorem three_le_pRank_of_three {X : Type*} [Group X] [Finite X] {P Q R : X}
    (hP : P ^ 3 = 1) (hQ : Q ^ 3 = 1) (hR : R ^ 3 = 1) (hPQ : Commute P Q) (hPR : Commute P R)
    (hQR : Commute Q R)
    (hind : ∀ a b c : ZMod 3, P ^ a.val * (Q ^ b.val * R ^ c.val) = 1 → a = 0 ∧ b = 0 ∧ c = 0) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hinj : Function.Injective (e27Of hP hQ hR hPQ hPR hQR) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨ha, hb, hc⟩ := hind _ _ _ (MonoidHom.mem_ker.mp hx)
    rw [Subgroup.mem_bot]
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    ext
    · exact ha
    · exact hb
    · exact hc
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b)
    Lin.e27_cube Lin.card_e27 _ hinj le_top

theorem eq_zero_of_pow_val {X : Type*} [Group X] {R : X} (hR : R ^ 3 = 1) (hR1 : R ≠ 1)
    {c : ZMod 3} (h : R ^ c.val = 1) : c = 0 := by
  have hlt : c.val < 3 := ZMod.val_lt c
  have hv : c.val = 0 := by
    interval_cases hcv : c.val
    · rfl
    · exact absurd (by simpa using h) hR1
    · exfalso
      apply hR1
      calc R = R ^ 3 * (R ^ 2)⁻¹ := by group
        _ = 1 := by rw [hR, h]; group
  exact (ZMod.val_eq_zero c).mp hv

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem H1_conj {b g h : G} (hg : g ∈ H) (hh : h ∈ Ctx38.H1 H b) : g * h * g⁻¹ ∈ Ctx38.H1 H b :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ H hg) h).mp hh

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem ψ_eq_one_of_mem {q : ↥H} (hq : (q : G) ∈ pCoreOf 2 H) : C.ψ q = 1 := by
  have hc : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨q, C.HN q.2⟩ ∈
      Subgroup.centralizer (tildeOf (fsuV1 T V) (conjClosure V H) :
        Set (SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V))) := by
    have h1 : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨q, C.HN q.2⟩ ∈
        tildeOf (fsuV1 T V) (H ⊓ pCoreOf 2 H) := secMk_mem_secImg ⟨q.2, hq⟩
    rw [← C.hF.toHypF91.tilde_inf_centralizer_pCoreOf (le_refl H)] at h1
    exact h1.2
  refine (convI_eq_one_iff C.hUe _).mpr ?_
  exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
    Subgroup.mem_centralizer_iff.mp hc w (C.Wt_le hw)

theorem mem_H1sup_of_e9 {x : G} (hxH : x ∈ H) (hx3 : x ^ 3 = 1)
    (hxK : C.ψ ⟨x, hxH⟩ ∈ ((H1 H b).subgroupOf H).map C.ψ)
    {e₁ e₂ : MulAut (IntMod C.Wt C.hUe)} (he₁ : e₁ ∈ ((H1 H b).subgroupOf H).map C.ψ)
    (he₂ : e₂ ∈ ((H1 H b).subgroupOf H).map C.ψ) (h31 : e₁ ^ 3 = 1) (h32 : e₂ ^ 3 = 1)
    (hc : Commute e₁ e₂) (hind : ∀ a b : ZMod 3, e₁ ^ a.val * e₂ ^ b.val = 1 → a = 0 ∧ b = 0) :
    x ∈ H1 H b ⊔ pCoreOf 2 H := by
  obtain ⟨h, hh0, hhx⟩ := hxK
  have hh : (h : G) ∈ H1 H b := Subgroup.mem_subgroupOf.mp hh0
  set n : ↥H := h⁻¹ * ⟨x, hxH⟩ with hn
  have hψn : C.ψ n = 1 := by rw [hn, map_mul, map_inv, hhx, inv_mul_cancel]
  by_cases hnQ : (n : G) ∈ pCoreOf 2 H
  · have e : x = (h : G) * n := by rw [hn]; simp
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hnQ)
  exfalso
  set Q := CFSG.pCore 2 ↥H with hQ
  have hmk1 : ∀ g : ↥H, (QuotientGroup.mk g : ↥H ⧸ Q) = 1 ↔ (g : G) ∈ pCoreOf 2 H := by
    intro g
    rw [QuotientGroup.eq_one_iff, hQ]
    constructor
    · intro hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := Subtype.ext hgg'
      rw [← this]
      exact hg'
  have hfaith : ∀ g : ↥H, (g : G) ∈ H1 H b → C.ψ g = 1 → (QuotientGroup.mk g : ↥H ⧸ Q) = 1 :=
    fun g hg h1 => (hmk1 g).mpr (C.mem_pCoreOf_of_mem_H1 hg h1)
  have hQker : Q ≤ C.ψ.ker := fun q hq => by
    rw [MonoidHom.mem_ker]
    exact C.ψ_eq_one_of_mem ((hmk1 q).mp ((QuotientGroup.eq_one_iff q).mpr hq))
  let ψb : ↥H ⧸ Q →* MulAut (IntMod C.Wt C.hUe) := QuotientGroup.lift Q C.ψ hQker
  have hψb : ∀ g : ↥H, ψb (QuotientGroup.mk g) = C.ψ g := fun g => rfl
  obtain ⟨ε₁, hε₁0, rfl⟩ := he₁
  obtain ⟨ε₂, hε₂0, rfl⟩ := he₂
  have hε₁ : (ε₁ : G) ∈ H1 H b := Subgroup.mem_subgroupOf.mp hε₁0
  have hε₂ : (ε₂ : G) ∈ H1 H b := Subgroup.mem_subgroupOf.mp hε₂0
  set P : ↥H ⧸ Q := QuotientGroup.mk ε₁
  set P' : ↥H ⧸ Q := QuotientGroup.mk ε₂
  set R : ↥H ⧸ Q := QuotientGroup.mk n
  set Hh : ↥H ⧸ Q := QuotientGroup.mk h
  have hcommH1 : ∀ g k : ↥H, (g : G) ∈ H1 H b → ((g * k * g⁻¹ * k⁻¹ : ↥H) : G) ∈ H1 H b := by
    intro g k hg
    have h1 : ((k * g⁻¹ * k⁻¹ : ↥H) : G) ∈ H1 H b := by
      have := H1_conj k.2 (inv_mem hg)
      simpa [mul_assoc] using this
    have e : ((g * k * g⁻¹ * k⁻¹ : ↥H) : G) = (g : G) * ((k * g⁻¹ * k⁻¹ : ↥H) : G) := by
      simp [mul_assoc]
    rw [e]
    exact mul_mem hg h1
  have hcommQ : ∀ g k : ↥H, (g : G) ∈ H1 H b → C.ψ g * C.ψ k = C.ψ k * C.ψ g →
      Commute (QuotientGroup.mk g : ↥H ⧸ Q) (QuotientGroup.mk k) := by
    intro g k hg hgk
    have h1 := hfaith _ (hcommH1 g k hg) (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hgk]
      group)
    have h2 : (QuotientGroup.mk g : ↥H ⧸ Q) * QuotientGroup.mk k * (QuotientGroup.mk g)⁻¹ *
        (QuotientGroup.mk k)⁻¹ = 1 := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact h1
    calc (QuotientGroup.mk g : ↥H ⧸ Q) * QuotientGroup.mk k
        = ((QuotientGroup.mk g : ↥H ⧸ Q) * QuotientGroup.mk k * (QuotientGroup.mk g)⁻¹ *
            (QuotientGroup.mk k)⁻¹) * QuotientGroup.mk k * QuotientGroup.mk g := by group
      _ = QuotientGroup.mk k * QuotientGroup.mk g := by rw [h2, one_mul]
  have hpow3 : ∀ g : ↥H, (g : G) ∈ H1 H b → C.ψ g ^ 3 = 1 →
      (QuotientGroup.mk g : ↥H ⧸ Q) ^ 3 = 1 := by
    intro g hg h3
    rw [← QuotientGroup.mk_pow]
    exact hfaith _ (by simpa using pow_mem hg 3) (by rw [map_pow, h3])
  have hP3 : P ^ 3 = 1 := hpow3 ε₁ hε₁ h31
  have hP'3 : P' ^ 3 = 1 := hpow3 ε₂ hε₂ h32
  have hPP' : Commute P P' := hcommQ ε₁ ε₂ hε₁ hc.eq
  have hPR : Commute P R := hcommQ ε₁ n hε₁ (by rw [hψn, mul_one, one_mul])
  have hP'R : Commute P' R := hcommQ ε₂ n hε₂ (by rw [hψn, mul_one, one_mul])
  have hHR : Commute Hh R := hcommQ h n hh (by rw [hψn, mul_one, one_mul])
  have hR3 : R ^ 3 = 1 := by
    have hx : (QuotientGroup.mk ⟨x, hxH⟩ : ↥H ⧸ Q) = Hh * R := by
      rw [← QuotientGroup.mk_mul, hn, mul_inv_cancel_left]
    have hx3' : (QuotientGroup.mk ⟨x, hxH⟩ : ↥H ⧸ Q) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, QuotientGroup.mk_one]
    have hxs : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    have hH3 : Hh ^ 3 = 1 := hpow3 h hh (by rw [hhx, ← map_pow, hxs, map_one])
    rw [hx, hHR.mul_pow, hH3, one_mul] at hx3'
    exact hx3'
  have hR1 : R ≠ 1 := fun h1 => hnQ ((hmk1 n).mp h1)
  have hind' : ∀ a b' c : ZMod 3, P ^ a.val * (P' ^ b'.val * R ^ c.val) = 1 →
      a = 0 ∧ b' = 0 ∧ c = 0 := by
    intro a b' c' h1
    have h2 := congrArg ψb h1
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_one, hψb, hψb, hψb, hψn, one_pow,
      mul_one] at h2
    obtain ⟨ha, hb⟩ := hind a b' h2
    refine ⟨ha, hb, eq_zero_of_pow_val hR3 hR1 ?_⟩
    rw [ha, hb] at h1
    simpa using h1
  have h3 := three_le_pRank_of_three hP3 hP'3 hR3 hPP' hPR hP'R hind'
  have h2 := pRank_quot_le_two C.S
  omega

end Ctx38

end CFSG.Quasithin.H13.L32A.C
