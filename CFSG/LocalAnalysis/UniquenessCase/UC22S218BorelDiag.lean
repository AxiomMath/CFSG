module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Facts
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsDiagMap
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.Quasithin.H13.Sec53F.BA (BorelAutDiag)

structure FieldBorelDiagData {Y : Type} [Group Y] (n E : ℕ) (U H : Subgroup Y)
    (F Eg : Subgroup (MulAut Y)) : Prop where
  borel : BorelAutDiag U H F Eg
  pow : ∀ σ ∈ F, ∃ j : ℕ, ∀ h ∈ H, σ h = h ^ 2 ^ j
  exp : ∀ h ∈ H, h ^ E = 1
  exists_d : ∀ {s : ℕ}, Odd s → s ∣ n → ∃ d ∈ H, orderOf d = 2 ^ s - 1

@[expose] def FieldBorelDiag (Y : Type) [Group Y] (n E : ℕ) : Prop :=
  ∃ (U H : Subgroup Y) (F Eg : Subgroup (MulAut Y)), FieldBorelDiagData n E U H F Eg

section Transport

variable {Y Y' : Type} [Group Y] [Group Y'] {n E : ℕ}

theorem FieldBorelDiagData.map {U H : Subgroup Y} {F Eg : Subgroup (MulAut Y)}
    (D : FieldBorelDiagData n E U H F Eg) (e : Y ≃* Y') :
    FieldBorelDiagData n E (U.map e.toMonoidHom) (H.map e.toMonoidHom)
      (F.map (MulAut.congr e).toMonoidHom) (Eg.map (MulAut.congr e).toMonoidHom) where
  borel := D.borel.map e
  pow := by
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨j, hj⟩ := D.pow σ hσ
    refine ⟨j, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    show e (σ (e.symm (e h))) = e h ^ 2 ^ j
    rw [e.symm_apply_apply, hj h hh, map_pow]
  exp := by
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_pow]
    show e (h ^ E) = 1
    rw [D.exp h hh, map_one]
  exists_d := by
    intro s hs hsn
    obtain ⟨d, hd, hdo⟩ := D.exists_d hs hsn
    exact ⟨e d, ⟨d, hd, rfl⟩, by rw [MulEquiv.orderOf_eq, hdo]⟩

theorem FieldBorelDiag.of_mulEquiv (h : FieldBorelDiag Y n E) (e : Y ≃* Y') :
    FieldBorelDiag Y' n E := by
  obtain ⟨U, H, F, Eg, D⟩ := h
  exact ⟨_, _, _, _, D.map e⟩

theorem FieldBorelDiag.exists_of_sylow [Finite Y] (h : FieldBorelDiag Y n E) {U : Subgroup Y}
    (hU : IsSylowTwoOf U ⊤) : ∃ (H : Subgroup Y) (F Eg : Subgroup (MulAut Y)),
      FieldBorelDiagData n E U H F Eg := by
  obtain ⟨U₀, H₀, F₀, E₀, D₀⟩ := h
  obtain ⟨k, -, hk⟩ := D₀.borel.sylow.exists_conj hU
  have := D₀.map (MulAut.conj k)
  rw [← hk] at this
  exact ⟨_, _, _, this⟩

end Transport

section Derived

variable {Y : Type} [Group Y] {n E : ℕ} {U H : Subgroup Y} {F Eg : Subgroup (MulAut Y)}

open scoped Classical in
private noncomputable def bar (V : Subgroup Y) (x : Y) :
    normalizer (V : Set Y) ⧸ V.subgroupOf (normalizer (V : Set Y)) :=
  if hx : x ∈ normalizer (V : Set Y) then QuotientGroup.mk ⟨x, hx⟩ else 1

private theorem bar_of_mem {x : Y} (hx : x ∈ normalizer (U : Set Y)) :
    bar U x = QuotientGroup.mk ⟨x, hx⟩ := dif_pos hx

private theorem bar_mul {x y : Y} (hx : x ∈ normalizer (U : Set Y))
    (hy : y ∈ normalizer (U : Set Y)) : bar U (x * y) = bar U x * bar U y := by
  rw [bar_of_mem (mul_mem hx hy), bar_of_mem hx, bar_of_mem hy]
  exact QuotientGroup.mk_mul _ (⟨x, hx⟩ : normalizer (U : Set Y)) ⟨y, hy⟩

private theorem bar_one : bar U (1 : Y) = 1 := by
  rw [bar_of_mem (one_mem _)]
  exact QuotientGroup.mk_one _

private theorem bar_inv {x : Y} (hx : x ∈ normalizer (U : Set Y)) :
    bar U x⁻¹ = (bar U x)⁻¹ := by
  rw [bar_of_mem (inv_mem hx), bar_of_mem hx]
  exact QuotientGroup.mk_inv _ (⟨x, hx⟩ : normalizer (U : Set Y))

private theorem bar_pow {x : Y} (hx : x ∈ normalizer (U : Set Y)) (k : ℕ) :
    bar U (x ^ k) = bar U x ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, bar_one]
  | succ k ih => rw [pow_succ, bar_mul (pow_mem hx k) hx, ih, pow_succ]

private theorem bar_eq_iff {x y : Y} (hx : x ∈ normalizer (U : Set Y))
    (hy : y ∈ normalizer (U : Set Y)) : bar U x = bar U y ↔ x * y⁻¹ ∈ U := by
  rw [bar_of_mem hx, bar_of_mem hy, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simp [div_eq_mul_inv]

private theorem bar_eq_iff' {x y : Y} (hx : x ∈ normalizer (U : Set Y))
    (hy : y ∈ normalizer (U : Set Y)) : bar U x = bar U y ↔ x⁻¹ * y ∈ U := by
  rw [bar_of_mem hx, bar_of_mem hy, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

private theorem bar_eq_one_iff {x : Y} (hx : x ∈ normalizer (U : Set Y)) :
    bar U x = 1 ↔ x ∈ U := by
  rw [← bar_one (U := U), bar_eq_iff hx (one_mem _)]
  simp

private theorem bar_of_mem_U {u : Y} (hu : u ∈ U) : bar U u = 1 :=
  (bar_eq_one_iff (le_normalizer hu)).2 hu

private theorem stab_iff {α : MulAut Y} (hα : U.map α.toMonoidHom = U) (x : Y) :
    α x ∈ U ↔ x ∈ U := by
  have : α x ∈ U ↔ α x ∈ U.map α.toMonoidHom := by rw [hα]
  rw [this]
  exact CFSG.Quasithin.H13.Sec53F.BA.mem_map_equiv_iff' α U x

private theorem pow_action_aux (D : FieldBorelDiagData n E U H F Eg) {α : MulAut Y}
    (hα : U.map α.toMonoidHom = U) :
    ∃ j : ℕ, ∀ b ∈ normalizer (U : Set Y), α b * (b ^ 2 ^ j)⁻¹ ∈ U := by
  obtain ⟨e, he, σ, hσ, hασ⟩ := D.borel.normal_form α (stab_iff hα)
  obtain ⟨j, hj⟩ := D.pow σ hσ
  refine ⟨j, fun b hb => ?_⟩
  obtain ⟨u, hu, h, hh, rfl⟩ := D.borel.B_eq b hb
  have hhN : h ∈ normalizer (U : Set Y) := D.borel.H_le hh
  have huN : u ∈ normalizer (U : Set Y) := le_normalizer hu
  have hσb : σ (u * h) = σ u * h ^ 2 ^ j := by rw [map_mul, hj h hh]
  have hσuU : σ u ∈ U := (D.borel.F_U σ hσ u).2 hu
  have hσbN : σ (u * h) ∈ normalizer (U : Set Y) := by
    rw [hσb]; exact mul_mem (le_normalizer hσuU) (pow_mem hhN _)
  have heb : (σ (u * h))⁻¹ * e (σ (u * h)) ∈ U := D.borel.E_triv e he _ hσbN
  have hαb : α (u * h) = e (σ (u * h)) := by rw [hασ]; rfl
  have hαbN : α (u * h) ∈ normalizer (U : Set Y) := by
    rw [hαb]
    have : e (σ (u * h)) = σ (u * h) * ((σ (u * h))⁻¹ * e (σ (u * h))) := by group
    rw [this]
    exact mul_mem hσbN (le_normalizer heb)
  have hαbN' : e (σ (u * h)) ∈ normalizer (U : Set Y) := hαb ▸ hαbN
  have e0 : bar U (e (σ (u * h))) = bar U (σ (u * h)) :=
    ((bar_eq_iff' hσbN hαbN').2 heb).symm
  have e1 : bar U (α (u * h)) = bar U h ^ 2 ^ j := by
    rw [hαb, e0, hσb, bar_mul (le_normalizer hσuU) (pow_mem hhN _), bar_pow hhN,
      bar_of_mem_U hσuU, one_mul]
  have e2 : bar U ((u * h) ^ 2 ^ j) = bar U h ^ 2 ^ j := by
    rw [bar_pow (mul_mem huN hhN), bar_mul huN hhN, bar_of_mem_U hu, one_mul]
  exact (bar_eq_iff hαbN (pow_mem (mul_mem huN hhN) _)).1 (e1.trans e2.symm)

theorem FieldBorelDiagData.pow_action (D : FieldBorelDiagData n E U H F Eg) {α : MulAut Y}
    (hα : U.map α.toMonoidHom = U) :
    ∃ k : ℕ, ∀ b ∈ normalizer (U : Set Y), α b * (b ^ k)⁻¹ ∈ U :=
  let ⟨j, hj⟩ := pow_action_aux D hα
  ⟨2 ^ j, hj⟩

theorem FieldBorelDiagData.exists_mem_centMod (D : FieldBorelDiagData n E U H F Eg) {s : ℕ}
    (hs : Odd s) (hsn : s ∣ n) :
    ∃ d : Y, orderOf d = 2 ^ s - 1 ∧ ∀ α : MulAut Y, (∃ e : ℕ, α ^ 2 ^ e = 1) →
      U.map α.toMonoidHom = U → d ∈ CFSG.Quasithin.H13.L32A.C.SkPf.centMod U α := by
  obtain ⟨d, hdH, hdo⟩ := D.exists_d hs hsn
  refine ⟨d, hdo, ?_⟩
  rintro α ⟨e, he⟩ hα
  have hdN : d ∈ normalizer (U : Set Y) := D.borel.H_le hdH
  obtain ⟨j, hj⟩ := pow_action_aux D hα
  have hstep : ∀ b ∈ normalizer (U : Set Y), α b ∈ normalizer (U : Set Y) ∧
      bar U (α b) = bar U b ^ 2 ^ j := fun b hb => by
    have hαN := CFSG.Quasithin.H13.L32A.C.SkPf.map_mem_normalizer hα hb
    refine ⟨hαN, ?_⟩
    rw [← bar_pow hb]
    exact (bar_eq_iff hαN (pow_mem hb _)).2 (hj b hb)
  have hiter : ∀ m : ℕ, (α ^ m) d ∈ normalizer (U : Set Y) ∧
      bar U ((α ^ m) d) = bar U d ^ (2 ^ j) ^ m := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using hdN, by simp⟩
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := hstep _ h1
      refine ⟨by rw [pow_succ', MulAut.mul_apply]; exact h3, ?_⟩
      rw [pow_succ', MulAut.mul_apply, h4, h2, ← pow_mul, pow_succ]
  obtain ⟨-, h2⟩ := hiter (2 ^ e)
  rw [he, MulAut.one_apply, ← pow_mul] at h2
  have hK1 : d * (d ^ 2 ^ (j * 2 ^ e))⁻¹ ∈ U :=
    (bar_eq_iff hdN (pow_mem hdN _)).1 (by rw [bar_pow hdN]; exact h2)
  have hK2 : d * (d ^ 2 ^ (j * 2 ^ e))⁻¹ = 1 :=
    D.borel.U_inf_H _ hK1 (mul_mem hdH (inv_mem (pow_mem hdH _)))
  have hK3 : d ^ 2 ^ (j * 2 ^ e) = d := (mul_inv_eq_one.1 hK2).symm
  have hKpos : 1 ≤ 2 ^ (j * 2 ^ e) := Nat.one_le_two_pow
  have hK4 : d ^ (2 ^ (j * 2 ^ e) - 1) = 1 := by
    have h5 : d ^ (2 ^ (j * 2 ^ e) - 1 + 1) = d := by rwa [Nat.sub_add_cancel hKpos]
    rw [pow_succ] at h5
    simpa using h5
  have hdvd : 2 ^ s - 1 ∣ 2 ^ (j * 2 ^ e) - 1 := by
    rw [← hdo]; exact orderOf_dvd_of_pow_eq_one hK4
  have hsm : s ∣ j * 2 ^ e := by
    have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 s (j * 2 ^ e)
    rw [Nat.gcd_eq_left hdvd] at hg
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ Nat.gcd s (j * 2 ^ e) := Nat.one_le_two_pow
    have h3 : 2 ^ s = 2 ^ Nat.gcd s (j * 2 ^ e) := by omega
    have h4 := Nat.pow_right_injective (le_refl 2) h3
    have h5 := Nat.gcd_dvd_right s (j * 2 ^ e)
    rwa [← h4] at h5
  have hsj : s ∣ j :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right e hs.coprime_two_right) hsm
  have hd2j : d ^ 2 ^ j = d := by
    have h1 : 2 ^ s - 1 ∣ 2 ^ j - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hsj
    have h2 : d ^ (2 ^ j - 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hdo]; exact h1
    have h3 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    calc d ^ 2 ^ j = d ^ (2 ^ j - 1 + 1) := by rw [Nat.sub_add_cancel h3]
      _ = d := by rw [pow_succ, h2, one_mul]
  rw [CFSG.Quasithin.H13.L32A.C.SkPf.mem_centMod]
  refine ⟨hdN, ?_⟩
  exact (bar_eq_iff (hstep d hdN).1 hdN).1 (by rw [(hstep d hdN).2, ← bar_pow hdN, hd2j])

theorem FieldBorelDiagData.eq_one_of_pow_eq_one (D : FieldBorelDiagData n E U H F Eg) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpE : ¬ p ∣ E) {b : Y} (hb : b ∈ normalizer (U : Set Y))
    (hbp : b ^ p = 1) : b = 1 := by
  obtain ⟨u, hu, h, hh, rfl⟩ := D.borel.B_eq b hb
  have hhN : h ∈ normalizer (U : Set Y) := D.borel.H_le hh
  have huN : u ∈ normalizer (U : Set Y) := le_normalizer hu
  have e1 : bar U (h ^ p) = 1 := by
    have : bar U ((u * h) ^ p) = bar U h ^ p := by
      rw [bar_pow (mul_mem huN hhN), bar_mul huN hhN, bar_of_mem_U hu, one_mul]
    rw [hbp, bar_one] at this
    rw [bar_pow hhN]
    exact this.symm
  have e3 : h ^ p = 1 :=
    D.borel.U_inf_H _ ((bar_eq_one_iff (pow_mem hhN p)).1 e1) (pow_mem hh p)
  have hcop : Nat.Coprime p E := (Nat.Prime.coprime_iff_not_dvd hp).2 hpE
  have e4 : h = 1 := by
    have := pow_gcd_eq_one.2 ⟨e3, D.exp h hh⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  rw [e4, mul_one] at hbp ⊢
  obtain ⟨k, hk⟩ := D.borel.sylow.2.1 ⟨u, hu⟩
  have h5 : (⟨u, hu⟩ : U) ^ p = 1 := Subtype.ext (by simpa using hbp)
  have hcop3 : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).2 hp2).symm
  have h6 := pow_gcd_eq_one.2 ⟨hk, h5⟩
  rw [hcop3.gcd_eq_one, pow_one] at h6
  simpa using congrArg Subtype.val h6

end Derived

theorem torusFacts218_of_fieldBorelDiag {Y : Type} [Group Y] [Finite Y] {n E : ℕ}
    {Tor Out : ℕ → Prop} (hFB : FieldBorelDiag Y n E)
    (hTor : ∀ {s r : ℕ}, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → Tor r)
    (hOut : ∀ {p : ℕ}, p.Prime → p ≠ 2 → Out p → ¬ p ∣ E)
    (hT : ∃ T : Subgroup Y, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      ∀ ℓ : ℕ, ℓ.Prime → Tor ℓ → ∃ A : Subgroup Y, A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2)
    (hrank : ∀ {s r : ℕ}, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 →
      CFSG.Open.pRank r (⊤ : Subgroup Y) = 2)
    (hsyl : ∀ {s r : ℕ}, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → ¬ r ∣ Nat.card (Sylow 2 Y))
    (hle : ∀ {p : ℕ}, p.Prime → p ≠ 2 → Out p → CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2) :
    TorusFacts218 Y n Tor Out where
  tor_of_dvd := hTor
  pRank_eq_two := hrank
  not_dvd_card_sylow := hsyl
  pow_action := fun {U} hU {α} hα {m} _ _ => by
    obtain ⟨H, F, Eg, D⟩ := hFB.exists_of_sylow hU
    exact D.pow_action hα
  exists_mem_centMod := fun {s U} hU hs hsn => by
    obtain ⟨H, F, Eg, D⟩ := hFB.exists_of_sylow hU
    exact D.exists_mem_centMod hs hsn
  exists_pair := by
    obtain ⟨T, hTc, hTE⟩ := hT
    intro s r p hs hsn hr hrd hp hTp _
    obtain ⟨A, hAT, hAe, hAc⟩ := hTE r hr (hTor hs hsn hr hrd)
    obtain ⟨Q, hQT, hQe, hQc⟩ := hTE p hp hTp
    refine ⟨A, Q, hAe, hAc, hQe, hQc, fun x hx => ⟨1, fun e he => ?_⟩⟩
    rw [pow_one, mul_inv_eq_iff_eq_mul]
    exact hTc x (hQT hx) e (hAT he)
  eq_one_of_pow_eq_one := fun {p} hp hp2 hOutp {U} hU {b} hb hbp => by
    obtain ⟨H, F, Eg, D⟩ := hFB.exists_of_sylow hU
    exact D.eq_one_of_pow_eq_one hp hp2 (hOut hp hp2 hOutp) hb hbp
  pRank_le_two := hle

end CFSG.LocalAnalysis.UniquenessCase.UC22
