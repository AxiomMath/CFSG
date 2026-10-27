module

public import CFSG.Quasithin.EmptyFaithful.S14612GA0
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.Quasithin

namespace E9Z4Str

variable {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)}

omit [Finite V] in
private theorem le_X_14612 (h : E9Z4Str X Tb P) : P ≤ X := by
  rw [h.eq]
  exact le_sup_left

omit [Finite V] in
private theorem tb_le_X_14612 (h : E9Z4Str X Tb P) : Tb ≤ X := by
  rw [h.eq]
  exact le_sup_right

omit [Finite V] in
private theorem inf_eq_bot_14612 (h : E9Z4Str X Tb P) : P ⊓ Tb = ⊥ := by
  have h1 : Nat.card ↥(P ⊓ Tb) ∣ 9 := h.card_P ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(P ⊓ Tb) ∣ 4 := h.card_Tb ▸ Subgroup.card_dvd_of_le inf_le_right
  exact Subgroup.card_eq_one.mp (by simpa using Nat.dvd_gcd h1 h2)

theorem card_V (h : E9Z4Str X Tb P) : Nat.card V = 16 := by
  rw [card_eq_two_pow_rk h.sq, h.rk_four]
  norm_num

theorem card_X (h : E9Z4Str X Tb P) : Nat.card X = 36 := by
  have hTn : Tb ≤ Subgroup.normalizer (P : Set (MulAut V)) := fun t ht =>
    h.normalP.le_normalizer (h.tb_le_X_14612 ht)
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hTn
  rw [sup_comm, ← h.eq, inf_comm, h.inf_eq_bot_14612, Subgroup.card_bot, h.card_Tb,
    h.card_P] at hprod
  omega

omit [Finite V] in
theorem commV_X (h : E9Z4Str X Tb P) : commV X = ⊤ := by
  obtain ⟨P₁, P₂, hP₁, hP₂, -, -, -, -, hcsup, -⟩ := h.planes
  rw [eq_top_iff, ← hcsup]
  exact sup_le (commV_mono216 (hP₁.trans h.le_X_14612))
    (commV_mono216 (hP₂.trans h.le_X_14612))

private theorem commV_le_of_mul_mem_14612 (hV : ∀ v : V, v ^ 2 = 1) {Q : Subgroup (MulAut V)}
    (hQX : Q ≤ X) (hQ : Nat.card Q = 3) (hrk : rk (commV Q) = 2) {W : Subgroup V}
    (hW : ∀ x ∈ X, ∀ w ∈ W, x w ∈ W) {a b : V} (ha : a ∈ commV Q) (hb : b ∈ fixV Q)
    (hab : a * b ∈ W) (ha1 : a ≠ 1) : commV Q ≤ W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgQ, -, hgz, -⟩ := exists_generator_of_prime_card hQ
  obtain ⟨-, hinf, -, -⟩ := commV_card_three hV hQ
  have hQnil : Group.IsNilpotent ↥Q :=
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hQ)).isNilpotent
  have hQmem : Q ∈ Xk Q 1 := by
    refine ⟨le_fittingOf_of_normal_nilpotent le_rfl
      (fun x hx n hn => Q.mul_mem (Q.mul_mem hx hn) (Q.inv_mem hx)) hQnil, hQ, hrk⟩
  have hgb : g b = b := hb g hgQ
  have hu : g a * a⁻¹ ∈ W := by
    have h1 : g (a * b) ∈ W := hW g (hQX hgQ) _ hab
    have h2 : g (a * b) * (a * b)⁻¹ = g a * a⁻¹ := by
      rw [map_mul, hgb, mul_inv_rev]
      group
    rw [← h2]
    exact W.mul_mem h1 (W.inv_mem hab)
  have hu' : g a * a⁻¹ ∈ commV Q := Subgroup.subset_closure ⟨g, hgQ, a, rfl⟩
  have hu1 : g a * a⁻¹ ≠ 1 := by
    intro h1
    have hga : g a = a := mul_inv_eq_one.mp h1
    have hafix : a ∈ fixV Q := by
      rw [← hgz]
      exact mem_fixV_zpowers_iff.mpr hga
    have : a ∈ commV Q ⊓ fixV Q := ⟨ha, hafix⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact ha1 this
  have hF := Xk_irreducible hV (X := Q) (Or.inl rfl) hQmem (F := W ⊓ commV Q)
    (fun x hx f hf => ⟨hW x (hQX hx) f hf.1,
      commV_smul_mem (fun q hq => Q.mul_mem (Q.mul_mem hx hq) (Q.inv_mem hx)) hf.2⟩)
    inf_le_right
    (fun hbot => by
      have hmem : g a * a⁻¹ ∈ W ⊓ commV Q := ⟨hu, hu'⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hu1 hmem)
  exact inf_eq_right.mp hF

theorem irreducible (h : E9Z4Str X Tb P) {W : Subgroup V} (hW : ∀ x ∈ X, ∀ w ∈ W, x w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨P₁, P₂, hP₁P, hP₂P, hc₁, hc₂, -, hdisj, hcsup, hf₁, hf₂, σ, hσ, hσP⟩ := h.planes
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  have hrkBA : rk (commV P₂) = rk (commV P₁) := by rw [← hσP, rk_commV_conjBy]
  have hinf : commV P₁ ⊓ commV P₂ = ⊥ := disjoint_iff.mp hdisj
  have hsum := rk_sup_add_rk_inf (commV P₁) (commV P₂)
  rw [hcsup, hinf, rk_top, rk_bot, h.rk_four] at hsum
  have hrkA : rk (commV P₁) = 2 := by omega
  have hrkB : rk (commV P₂) = 2 := by omega
  obtain ⟨⟨w, hwW⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hw1' : w ≠ 1 := fun e => hw1 (Subtype.ext e)
  have hwAB : w ∈ commV P₁ ⊔ commV P₂ := by
    rw [hcsup]
    exact Subgroup.mem_top w
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hwAB
  have hAB : commV P₁ ≤ W ∨ commV P₂ ≤ W := by
    by_cases ha1 : a = 1
    · right
      have hb1 : b ≠ 1 := by
        rintro rfl
        exact hw1' (by rw [← hab, ha1, mul_one])
      refine commV_le_of_mul_mem_14612 h.sq (hP₂P.trans h.le_X_14612) hc₂ hrkB hW hb (hf₁ ha) ?_ hb1
      rw [mul_comm, hab]
      exact hwW
    · left
      exact commV_le_of_mul_mem_14612 h.sq (hP₁P.trans h.le_X_14612) hc₁ hrkA hW ha (hf₂ hb)
        (by rw [hab]; exact hwW) ha1
  have hσB : commV P₂ = (commV P₁).map (MulEquiv.toMonoidHom σ) := by
    rw [← hσP, commV_conjBy]
  have hσX : σ ∈ X := h.tb_le_X_14612 hσ
  have hσX' : σ⁻¹ ∈ X := X.inv_mem hσX
  have hboth : commV P₁ ≤ W ∧ commV P₂ ≤ W := by
    rcases hAB with hA | hB
    · refine ⟨hA, ?_⟩
      rw [hσB]
      rintro _ ⟨z, hz, rfl⟩
      exact hW σ hσX z (hA hz)
    · refine ⟨fun z hz => ?_, hB⟩
      have hσz : σ z ∈ commV P₂ := by
        rw [hσB]
        exact ⟨z, hz, rfl⟩
      simpa using hW σ⁻¹ hσX' _ (hB hσz)
  rw [eq_top_iff, ← hcsup]
  exact sup_le hboth.1 hboth.2

private theorem eq_of_orderOf_eq_two_14612 (h : E9Z4Str X Tb P) {s t : MulAut V} (hs : s ∈ Tb)
    (ht : t ∈ Tb) (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) : s = t := by
  have : Fintype ↥Tb := Fintype.ofFinite _
  have hcyc := h.cyclic_Tb
  have hcard : Fintype.card ↥Tb = 4 := by rw [← Nat.card_eq_fintype_card]; exact h.card_Tb
  have hS := IsCyclic.card_orderOf_eq_totient (α := ↥Tb) (d := 2) (by rw [hcard]; norm_num)
  rw [Nat.totient_two] at hS
  have hsmem : (⟨s, hs⟩ : ↥Tb) ∈ (Finset.univ.filter fun a : ↥Tb => orderOf a = 2) := by
    simpa [Subgroup.orderOf_mk] using hs2
  have htmem : (⟨t, ht⟩ : ↥Tb) ∈ (Finset.univ.filter fun a : ↥Tb => orderOf a = 2) := by
    simpa [Subgroup.orderOf_mk] using ht2
  exact congrArg Subtype.val (Finset.card_le_one.mp hS.le _ hsmem _ htmem)

theorem inverts_of_involution (h : E9Z4Str X Tb P) {x : MulAut V} (hx : x ∈ X)
    (hx2 : orderOf x = 2) : ∀ y ∈ P, x * y * x⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htT, ht2, htinv⟩ := h.inv
  have hxsq : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hTn : Tb ≤ Subgroup.normalizer (P : Set (MulAut V)) := fun s hs =>
    h.normalP.le_normalizer (h.tb_le_X_14612 hs)
  have hxmem : x ∈ ((P ⊔ Tb : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [← h.eq]
    exact hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P Tb hTn] at hxmem
  obtain ⟨a, ha, s, hs, rfl⟩ := Set.mem_mul.mp hxmem
  have hs2 : s ^ 2 = 1 := by
    have h1 : s * a * s⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hTn hs) a).mp ha
    have h2 : (a * (s * a * s⁻¹)) * s ^ 2 = 1 := by
      rw [← hxsq, pow_two (a * s)]
      group
    have h3 : s ^ 2 = (a * (s * a * s⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h2
    have h4 : s ^ 2 ∈ P ⊓ Tb := ⟨by rw [h3]; exact P.inv_mem (P.mul_mem ha h1), Tb.pow_mem hs 2⟩
    rw [h.inf_eq_bot_14612, Subgroup.mem_bot] at h4
    exact h4
  have hs1 : s ≠ 1 := by
    rintro rfl
    have h3 : a ^ 3 = 1 := h.exp_P a ha
    have h2 : a ^ 2 = 1 := by simpa using hxsq
    have ha1 : a = 1 := by
      calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    rw [ha1] at hx2
    simp at hx2
  have hst : s = t := h.eq_of_orderOf_eq_two_14612 hs htT (orderOf_eq_prime hs2 hs1) ht2
  subst hst
  intro y hy
  have hc : a * y⁻¹ = y⁻¹ * a := h.comm_P a ha y⁻¹ (P.inv_mem hy)
  calc a * s * y * (a * s)⁻¹ = a * (s * y * s⁻¹) * a⁻¹ := by group
    _ = a * y⁻¹ * a⁻¹ := by rw [htinv y hy]
    _ = y⁻¹ := by rw [hc]; group

theorem exists_fixV_eq_bot (h : E9Z4Str X Tb P) : ∃ y ∈ P, fixV (Subgroup.zpowers y) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₁, P₂, hP₁P, hP₂P, hc₁, hc₂, -, hdisj, hcsup, hf₁, hf₂, -⟩ := h.planes
  obtain ⟨g₁, hg₁, -, hgz₁, -⟩ := exists_generator_of_prime_card hc₁
  obtain ⟨g₂, hg₂, -, hgz₂, -⟩ := exists_generator_of_prime_card hc₂
  obtain ⟨-, hinf₁, -, -⟩ := commV_card_three h.sq hc₁
  obtain ⟨-, hinf₂, -, -⟩ := commV_card_three h.sq hc₂
  refine ⟨g₁ * g₂, P.mul_mem (hP₁P hg₁) (hP₂P hg₂), ?_⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
  have hyv : g₁ (g₂ v) = v := mem_fixV_zpowers_iff.mp hv
  have hv' : v ∈ commV P₁ ⊔ commV P₂ := by
    rw [hcsup]
    exact Subgroup.mem_top v
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv'
  have hinvA : g₁ a ∈ commV P₁ :=
    commV_smul_mem (fun q hq => P₁.mul_mem (P₁.mul_mem hg₁ hq) (P₁.inv_mem hg₁)) ha
  have hinvB : g₂ b ∈ commV P₂ :=
    commV_smul_mem (fun q hq => P₂.mul_mem (P₂.mul_mem hg₂ hq) (P₂.inv_mem hg₂)) hb
  have h2a : g₂ a = a := hf₁ ha g₂ hg₂
  have h1b : g₁ (g₂ b) = g₂ b := hf₂ hinvB g₁ hg₁
  have e : g₁ a * g₂ b = a * b := by
    have : g₁ (g₂ (a * b)) = g₁ a * g₂ b := by rw [map_mul, h2a, map_mul, h1b]
    rw [← this]
    exact hyv
  have hpair := Subgroup.mul_injective_of_disjoint hdisj
    (a₁ := (⟨g₁ a, hinvA⟩, ⟨g₂ b, hinvB⟩)) (a₂ := (⟨a, ha⟩, ⟨b, hb⟩)) e
  have hga : g₁ a = a := congrArg (fun p => (p.1 : V)) hpair
  have hgb : g₂ b = b := congrArg (fun p => (p.2 : V)) hpair
  have ha1 : a = 1 := by
    have : a ∈ commV P₁ ⊓ fixV P₁ := ⟨ha, by rw [← hgz₁]; exact mem_fixV_zpowers_iff.mpr hga⟩
    rw [hinf₁, Subgroup.mem_bot] at this
    exact this
  have hb1 : b = 1 := by
    have : b ∈ commV P₂ ⊓ fixV P₂ := ⟨hb, by rw [← hgz₂]; exact mem_fixV_zpowers_iff.mpr hgb⟩
    rw [hinf₂, Subgroup.mem_bot] at this
    exact this
  rw [ha1, hb1, mul_one]

theorem rk_commV_involution (h : E9Z4Str X Tb P) {x : MulAut V} (hx : x ∈ X)
    (hx2 : orderOf x = 2) : rk (commV (Subgroup.zpowers x)) = 2 := by
  obtain ⟨y, hyP, hy⟩ := h.exists_fixV_eq_bot
  have hxsq : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hrk := rk_eq_two_mul_of_inverts h.sq hy hxsq (h.inverts_of_involution hx hx2 y hyP)
  rw [h.rk_four] at hrk
  omega

end E9Z4Str

end CFSG.Quasithin
