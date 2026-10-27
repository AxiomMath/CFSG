module

public import CFSG.Quasithin.Background.A1cModuleAut
public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.Quasithin.Background.A1cModuleCoprime

public section

namespace CFSG.Quasithin

namespace XMod

variable {A : Type*} [Group A] {P : Type*} [CommGroup P] [MulDistribMulAction A P]

theorem odd_card_eqvAut [Finite P] (hP : ∀ p : P, p ^ 2 = 1)
    (hcomm : commOf A (⊤ : Subgroup P) = ⊤)
    (hirr : IsIrrSec A (fixed A (⊤ : Subgroup P)) ⊤) (hO2 : IsTwoReduced A (⊤ : Subgroup P)) :
    Odd (Nat.card ↥(eqvAut A P)) := by
  classical
  obtain ⟨Syl⟩ : Nonempty (Sylow 2 ↥(eqvAut A P)) := inferInstance
  let S : Subgroup (MulAut P) := (Syl : Subgroup ↥(eqvAut A P)).map (eqvAut A P).subtype
  have hSΓ : ∀ s ∈ S, s ∈ eqvAut A P := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hSp : IsPGroup 2 ↥S := Syl.isPGroup'.map (eqvAut A P).subtype
  let U : Subgroup P := fixed ↥S ⊤
  have hUinv : IsInv A U := by
    intro a w hw
    refine ⟨trivial, fun s => ?_⟩
    have h1 : (s : MulAut P) (a • w) = a • (s : MulAut P) w := hSΓ s.1 s.2 a w
    have h2 : (s : MulAut P) w = w := hw.2 s
    change (s : MulAut P) (a • w) = a • w
    rw [h1, h2]
  let K : Subgroup A :=
    { carrier := {a | ∀ w ∈ U, a • w = w}
      one_mem' := fun w _ => one_smul A w
      mul_mem' := fun {a b} ha hb w hw => by rw [mul_smul, hb w hw, ha w hw]
      inv_mem' := fun {a} ha w hw => by rw [inv_smul_eq_iff]; exact (ha w hw).symm }
  have hKnormal : K.Normal :=
    ⟨fun a ha g w hw => by
      have h1 : g⁻¹ • w ∈ U := hUinv g⁻¹ w hw
      rw [mul_smul, mul_smul, ha _ h1, smul_inv_smul]⟩
  have hAB : ∀ d ∈ K, Odd (orderOf (MulDistribMulAction.toMulAut A P d)) → ∀ w : P, d • w = w := by
    intro d hdK hodd
    set ρd : MulAut P := MulDistribMulAction.toMulAut A P d with hρd
    have hRP : IsPGroup 2 P := fun p => ⟨1, by simpa using hP p⟩
    have hA : ¬ 2 ∣ Nat.card ↥(Subgroup.zpowers ρd) := by
      rw [Nat.card_zpowers]
      exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd)
    have hcommβ : ∀ (a : ↥(Subgroup.zpowers ρd)) (b : ↥S),
        (Subgroup.zpowers ρd).subtype a * S.subtype b =
          S.subtype b * (Subgroup.zpowers ρd).subtype a := by
      intro a b
      have hb : (b : MulAut P) * ρd = ρd * (b : MulAut P) := by
        ext p
        exact hSΓ b.1 b.2 d p
      have hmem : ρd ∈ Subgroup.centralizer ({(b : MulAut P)} : Set (MulAut P)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hb
      have h1 := Subgroup.zpowers_le.2 hmem a.2
      rw [Subgroup.mem_centralizer_iff] at h1
      exact (h1 _ rfl).symm
    have hfixβ : ∀ (a : ↥(Subgroup.zpowers ρd)) (r : P), (∀ b : ↥S, S.subtype b r = r) →
        (Subgroup.zpowers ρd).subtype a r = r := by
      intro a r hr
      have hrU : r ∈ U := ⟨trivial, fun s => hr s⟩
      have hd : ρd r = r := hdK r hrU
      have hst : Subgroup.zpowers ρd ≤ MulAction.stabilizer (MulAut P) r :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hd)
      exact MulAction.mem_stabilizer_iff.1 (hst a.2)
    have h1 := CFSG.GroupTheory.thompson_A_times_B hRP hA hSp (Subgroup.zpowers ρd).subtype
      S.subtype hcommβ hfixβ ⟨ρd, Subgroup.mem_zpowers ρd⟩
    intro w
    have h2 : ρd = 1 := h1
    exact congrArg (fun φ : MulAut P => φ w) h2
  have hKall : ∀ d ∈ K, ∃ k : ℕ, ∀ w ∈ (⊤ : Subgroup P), (d ^ 2 ^ k) • w = w := by
    intro d hdK
    obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd
      (orderOf_pos (MulDistribMulAction.toMulAut A P d)).ne'
    refine ⟨k, fun w _ => hAB (d ^ 2 ^ k) (pow_mem hdK _) ?_ w⟩
    rw [map_pow, orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hn⟩, hn,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hm
  have hKtriv : ∀ d ∈ K, ∀ w : P, d • w = w :=
    fun d hd w => hO2 K hKnormal hKall d hd w trivial
  have hUtop : U = ⊤ := by
    have hJinv : IsInv A (U ⊔ fixed A (⊤ : Subgroup P)) := hUinv.sup (isInv_fixed _)
    rcases hirr.2 (U ⊔ fixed A (⊤ : Subgroup P)) hJinv le_sup_right le_top with h | h
    · exfalso
      have hUC : U ≤ fixed A (⊤ : Subgroup P) := le_sup_left.trans h.le
      have hAall : ∀ (a : A) (w : P), a • w = w := fun a w =>
        hKtriv a (fun u hu => (hUC hu).2 a) w
      exact hirr.1.ne (fixed_top_eq_top_iff.2 hAall)
    · refine eq_top_iff.2 ?_
      calc (⊤ : Subgroup P) = commOf A (⊤ : Subgroup P) := hcomm.symm
        _ = commOf A (U ⊔ fixed A (⊤ : Subgroup P)) := by rw [h]
        _ = commOf A U := commOf_sup_eq_of_le_fixed le_rfl
        _ ≤ U := commOf_le_of_isInv hUinv
  have hS1 : ∀ s ∈ S, s = 1 := by
    intro s hs
    ext w
    have hw : w ∈ U := by rw [hUtop]; trivial
    exact hw.2 ⟨s, hs⟩
  have hSyl : (Syl : Subgroup ↥(eqvAut A P)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact Subtype.ext (hS1 x.1 ⟨x, hx, rfl⟩)
  have hcard1 : Nat.card ↥(Syl : Subgroup ↥(eqvAut A P)) = 1 := by
    rw [hSyl]; exact Subgroup.card_bot
  rw [Sylow.card_eq_multiplicity] at hcard1
  have hk : (Nat.card ↥(eqvAut A P)).factorization 2 = 0 := by
    rcases Nat.pow_eq_one.1 hcard1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  rw [Nat.factorization_eq_zero_iff] at hk
  rcases hk with h | h | h
  · exact absurd Nat.prime_two h
  · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  · exact absurd h Nat.card_pos.ne'

theorem map_fixed_eq {φ : MulAut P} (hφ : φ ∈ eqvAut A P) :
    (fixed A (⊤ : Subgroup P)).map (φ : P →* P) = fixed A (⊤ : Subgroup P) := by
  have key : ∀ ψ : MulAut P, ψ ∈ eqvAut A P →
      ∀ c ∈ fixed A (⊤ : Subgroup P), ψ c ∈ fixed A (⊤ : Subgroup P) := by
    intro ψ hψ c hc
    refine ⟨trivial, fun a => ?_⟩
    rw [← hψ a c, hc.2 a]
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact key φ hφ c hc
  · intro hx
    exact ⟨φ⁻¹ x, key φ⁻¹ (inv_mem hφ) x hx, MulAut.apply_inv_self P φ x⟩

noncomputable def quotAut (φ : eqvAut A P) : MulAut (P ⧸ fixed A (⊤ : Subgroup P)) :=
  QuotientGroup.congr _ _ (φ : MulAut P) (map_fixed_eq φ.2)

theorem quotAut_mk (φ : eqvAut A P) (x : P) :
    quotAut φ (QuotientGroup.mk x) = QuotientGroup.mk ((φ : MulAut P) x) :=
  QuotientGroup.congr_mk _ _ _ _ x

variable (A P) in
noncomputable def restrQ : eqvAut A P →* eqvAut A (P ⧸ fixed A (⊤ : Subgroup P)) where
  toFun φ := ⟨quotAut φ, fun a q => by
    refine QuotientGroup.induction_on q fun x => ?_
    rw [smul_quotMk, quotAut_mk, quotAut_mk, smul_quotMk, φ.2 a x]⟩
  map_one' := by
    refine Subtype.ext (MulEquiv.ext fun q => ?_)
    refine QuotientGroup.induction_on q fun x => ?_
    exact quotAut_mk 1 x
  map_mul' φ ψ := by
    refine Subtype.ext (MulEquiv.ext fun q => ?_)
    refine QuotientGroup.induction_on q fun x => ?_
    change quotAut (φ * ψ) (QuotientGroup.mk x) = quotAut φ (quotAut ψ (QuotientGroup.mk x))
    rw [quotAut_mk, quotAut_mk, quotAut_mk]
    rfl

theorem restrQ_injective [Finite P] (hP : ∀ p : P, p ^ 2 = 1)
    (hcomm : commOf A (⊤ : Subgroup P) = ⊤) (hodd : Odd (Nat.card ↥(eqvAut A P))) :
    Function.Injective (restrQ A P) := by
  classical
  rw [injective_iff_map_eq_one]
  intro φ hφ
  let Y : Subgroup (MulAut P) := (restrQ A P).ker.map (eqvAut A P).subtype
  have hYΓ : ∀ y ∈ Y, y ∈ eqvAut A P := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hYker : ∀ y ∈ Y, ∀ w : P, y w * w⁻¹ ∈ fixed A (⊤ : Subgroup P) := by
    rintro _ ⟨x, hx, rfl⟩ w
    have h1 : restrQ A P x = 1 := hx
    have h2 : quotAut x (QuotientGroup.mk w) = QuotientGroup.mk w := by
      have := congrArg (fun z : eqvAut A (P ⧸ fixed A (⊤ : Subgroup P)) =>
        (z : MulAut (P ⧸ fixed A (⊤ : Subgroup P))) (QuotientGroup.mk w)) h1
      exact this
    rw [quotAut_mk, QuotientGroup.eq] at h2
    have h3 := inv_mem h2
    rw [mul_inv_rev, inv_inv] at h3
    change (x : MulAut P) w * w⁻¹ ∈ _
    rwa [mul_comm]
  have hYodd : Odd (Nat.card ↥Y) := by
    have h1 : Nat.card ↥Y = Nat.card ↥(restrQ A P).ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [h1]
    exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hcompl := isCompl_fixed_commOf_of_odd (A := ↥Y) (Q := P) hYodd hP
  have hFinv : IsInv A (fixed ↥Y (⊤ : Subgroup P)) := by
    intro a f hf
    refine ⟨trivial, fun y => ?_⟩
    have h1 : (y : MulAut P) (a • f) = a • (y : MulAut P) f := hYΓ y.1 y.2 a f
    have h2 : (y : MulAut P) f = f := hf.2 y
    change (y : MulAut P) (a • f) = a • f
    rw [h1, h2]
  have hKle : commOf ↥Y (⊤ : Subgroup P) ≤ fixed A (⊤ : Subgroup P) := by
    rw [commOf_le_iff]
    intro y l _
    exact hYker y y.2 l
  have hFtop : fixed ↥Y (⊤ : Subgroup P) = ⊤ := by
    refine eq_top_iff.2 ?_
    calc (⊤ : Subgroup P) = commOf A (⊤ : Subgroup P) := hcomm.symm
      _ = commOf A (fixed ↥Y (⊤ : Subgroup P) ⊔ commOf ↥Y (⊤ : Subgroup P)) := by
        rw [hcompl.sup_eq_top]
      _ = commOf A (fixed ↥Y (⊤ : Subgroup P)) := commOf_sup_eq_of_le_fixed hKle
      _ ≤ fixed ↥Y (⊤ : Subgroup P) := commOf_le_of_isInv hFinv
  have hφY : (φ : MulAut P) ∈ Y := ⟨φ, hφ, rfl⟩
  have hφ1 : (φ : MulAut P) = 1 := by
    ext w
    have hw : w ∈ fixed ↥Y (⊤ : Subgroup P) := by rw [hFtop]; trivial
    exact hw.2 ⟨φ, hφY⟩
  exact Subtype.ext hφ1

theorem isIrrSec_quotient (hirr : IsIrrSec A (fixed A (⊤ : Subgroup P)) ⊤) :
    IsIrrSec A (⊥ : Subgroup (P ⧸ fixed A (⊤ : Subgroup P))) ⊤ := by
  refine ⟨?_, fun J hJ _ _ => ?_⟩
  ·
    obtain ⟨x, -, hx⟩ : ∃ x ∈ (⊤ : Subgroup P), x ∉ fixed A (⊤ : Subgroup P) :=
      IsConcreteLE.not_le_iff_exists.1 (not_le_of_gt hirr.1)
    refine lt_of_le_of_ne bot_le fun h => hx ?_
    have h1 : (QuotientGroup.mk x : P ⧸ fixed A (⊤ : Subgroup P)) ∈ (⊤ : Subgroup _) := trivial
    rw [← h] at h1
    exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 h1)
  · have hinv : IsInv A (J.comap (QuotientGroup.mk' (fixed A (⊤ : Subgroup P)))) := by
      intro a x hx
      rw [Subgroup.mem_comap] at hx ⊢
      have : (QuotientGroup.mk' (fixed A (⊤ : Subgroup P))) (a • x) =
          a • (QuotientGroup.mk' (fixed A (⊤ : Subgroup P))) x := rfl
      rw [this]
      exact hJ a _ hx
    have hCle : fixed A (⊤ : Subgroup P) ≤
        J.comap (QuotientGroup.mk' (fixed A (⊤ : Subgroup P))) := by
      intro c hc
      rw [Subgroup.mem_comap]
      change (QuotientGroup.mk c : P ⧸ fixed A (⊤ : Subgroup P)) ∈ J
      rw [(QuotientGroup.eq_one_iff c).2 hc]
      exact J.one_mem
    rcases hirr.2 _ hinv hCle le_top with h | h
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) J, h]
      exact QuotientGroup.map_mk'_self _
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) J, h]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

variable (A P) in
noncomputable def toEqvEnd : eqvAut A P →* ↥(eqvEnd A P) where
  toFun φ := ⟨MonoidHom.toAdditive (φ : MulAut P).toMonoidHom,
    mem_eqvEnd_iff.2 fun a p => φ.2 a p⟩
  map_one' := Subtype.ext (AddMonoidHom.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (AddMonoidHom.ext fun _ => rfl)

theorem toEqvEnd_injective : Function.Injective (toEqvEnd A P) := by
  intro φ ψ h
  apply Subtype.ext
  apply MulEquiv.ext
  intro p
  have h1 := congrArg
    (fun e : ↥(eqvEnd A P) => (e : AddMonoid.End (Additive P)) (Additive.ofMul p)) h
  exact Additive.ofMul.injective h1

theorem eqvAut_cyclic_odd [Finite P] (hP : ∀ p : P, p ^ 2 = 1)
    (hcomm : commOf A (⊤ : Subgroup P) = ⊤)
    (hirr : IsIrrSec A (fixed A (⊤ : Subgroup P)) ⊤) (hO2 : IsTwoReduced A (⊤ : Subgroup P)) :
    (∃ f : eqvAut A P →* eqvAut A (P ⧸ fixed A (⊤ : Subgroup P)), Function.Injective f) ∧
    (Finite ↥(eqvEnd A (P ⧸ fixed A (⊤ : Subgroup P))) ∧
      IsField ↥(eqvEnd A (P ⧸ fixed A (⊤ : Subgroup P))) ∧
      CharP ↥(eqvEnd A (P ⧸ fixed A (⊤ : Subgroup P))) 2) ∧
    IsCyclic ↥(eqvAut A P) ∧ Odd (Nat.card ↥(eqvAut A P)) := by
  have hodd := odd_card_eqvAut hP hcomm hirr hO2
  have hinj := restrQ_injective hP hcomm hodd
  have hsimple := isIrrSec_quotient hirr
  have hP' : ∀ q : P ⧸ fixed A (⊤ : Subgroup P), q ^ 2 = 1 := by
    intro q
    refine QuotientGroup.induction_on q fun x => ?_
    rw [← QuotientGroup.mk_pow, hP x, QuotientGroup.mk_one]
  refine ⟨⟨restrQ A P, hinj⟩, eqvEnd_isField_charTwo hP' hsimple, ?_, hodd⟩
  exact isCyclic_of_injective_eqvEnd hsimple ((toEqvEnd A _).comp (restrQ A P))
    ((toEqvEnd_injective).comp hinj)

end XMod

end CFSG.Quasithin
