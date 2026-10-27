module

public import CFSG.Quasithin.Background.InternalSecSum
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open

theorem exists_fixed_of_two_pow {P : Type} [CommGroup P] [Finite P] [Nontrivial P]
    (hP : ∀ p : P, p ^ 2 = 1) (c : MulAut P) {e : ℕ} (hc : c ^ 2 ^ e = 1) :
    ∃ p : P, p ≠ 1 ∧ c p = p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hc)
  have hD2 : IsPGroup 2 ↥(Subgroup.zpowers c) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have h2P : 2 ∣ Nat.card P := by
    obtain ⟨x, hx⟩ := exists_ne (1 : P)
    have hox : orderOf x = 2 := orderOf_eq_prime (hP x) hx
    exact hox ▸ orderOf_dvd_natCard x
  have h1fix : (1 : P) ∈ MulAction.fixedPoints ↥(Subgroup.zpowers c) P := fun g => smul_one g
  obtain ⟨b, hb, hb1⟩ := hD2.exists_fixed_point_of_prime_dvd_card_of_fixed_point P h2P h1fix
  exact ⟨b, fun h => hb1 h.symm, hb ⟨c, Subgroup.mem_zpowers c⟩⟩

section Sum

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {W₁ W₂ : Subgroup V}

theorem secIsoL_symm (hinv₁ : ∀ k ∈ L, ∀ w ∈ W₁, k w ∈ W₁)
    (hinv₂ : ∀ k ∈ L, ∀ w ∈ W₂, k w ∈ W₂) (h : SecIsoL L W₁ ⊥ W₂ ⊥) : SecIsoL L W₂ ⊥ W₁ ⊥ := by
  obtain ⟨e, he⟩ := equiv_of_secIsoL h
  refine secIsoL_of_equiv hinv₂ hinv₁ e.symm fun k w => ?_
  have h1 := he k (e.symm w) (hinv₁ k k.2 _ (e.symm w).2)
    (by rw [MulEquiv.apply_symm_apply]; exact hinv₂ k k.2 _ w.2)
  have h2 : e.symm ⟨(k : MulAut V) w, hinv₂ k k.2 w w.2⟩ =
      ⟨(k : MulAut V) (e.symm w), hinv₁ k k.2 _ (e.symm w).2⟩ := by
    rw [MulEquiv.symm_apply_eq, h1]
    apply Subtype.ext
    show (k : MulAut V) w = (k : MulAut V) (e (e.symm w))
    rw [MulEquiv.apply_symm_apply]
  rw [h2]

variable (hsum : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = ⊥)
  (hinv₁ : ∀ k ∈ L, ∀ w ∈ W₁, k w ∈ W₁) (hinv₂ : ∀ k ∈ L, ∀ w ∈ W₂, k w ∈ W₂)

include hsum hinf hinv₁ hinv₂

theorem eq_bot_of_diag
    (hirr₁ : ∀ J : Subgroup V, J ≤ W₁ → (∀ k ∈ L, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W₁)
    (hirr₂ : ∀ J : Subgroup V, J ≤ W₂ → (∀ k ∈ L, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W₂)
    (hnoniso : ¬ SecIsoL L W₁ ⊥ W₂ ⊥) {J : Subgroup V} (hJ : ∀ k ∈ L, ∀ w ∈ J, k w ∈ J)
    (h1 : J ⊓ W₁ = ⊥) (h2 : J ⊓ W₂ = ⊥) : J = ⊥ := by
  by_contra hne
  have hinj₁ : ∀ a ∈ J, proj₁ hsum hinf a = 1 → a = 1 := by
    intro a ha h
    have ha2 : a ∈ W₂ := by
      have := proj₁_mul_proj₂ hsum hinf a
      rw [h, one_mul] at this
      rw [← this]
      exact proj₂_mem hsum hinf a
    have : a ∈ J ⊓ W₂ := ⟨ha, ha2⟩
    rwa [h2, Subgroup.mem_bot] at this
  have hinj₂ : ∀ a ∈ J, proj₂ hsum hinf a = 1 → a = 1 := by
    intro a ha h
    have ha1 : a ∈ W₁ := by
      have := proj₁_mul_proj₂ hsum hinf a
      rw [h, mul_one] at this
      rw [← this]
      exact proj₁_mem hsum hinf a
    have : a ∈ J ⊓ W₁ := ⟨ha, ha1⟩
    rwa [h1, Subgroup.mem_bot] at this
  have hstab := fun (k : MulAut V) (hk : k ∈ L) =>
    proj_apply_of_stab hsum hinf (hinv₁ k hk) (hinv₂ k hk)
  have himg₁ : J.map (proj₁ hsum hinf) = W₁ := by
    have hle : J.map (proj₁ hsum hinf) ≤ W₁ := by
      rintro _ ⟨a, -, rfl⟩
      exact proj₁_mem hsum hinf a
    rcases hirr₁ _ hle (by
      rintro k hk _ ⟨a, ha, rfl⟩
      exact ⟨k a, hJ k hk a ha, (hstab k hk a).1⟩) with h | h
    · exfalso
      refine hne (eq_bot_iff.2 fun a ha => ?_)
      have : proj₁ hsum hinf a ∈ J.map (proj₁ hsum hinf) := ⟨a, ha, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (hinj₁ a ha this)
    · exact h
  have himg₂ : J.map (proj₂ hsum hinf) = W₂ := by
    have hle : J.map (proj₂ hsum hinf) ≤ W₂ := by
      rintro _ ⟨a, -, rfl⟩
      exact proj₂_mem hsum hinf a
    rcases hirr₂ _ hle (by
      rintro k hk _ ⟨a, ha, rfl⟩
      exact ⟨k a, hJ k hk a ha, (hstab k hk a).2⟩) with h | h
    · exfalso
      refine hne (eq_bot_iff.2 fun a ha => ?_)
      have : proj₂ hsum hinf a ∈ J.map (proj₂ hsum hinf) := ⟨a, ha, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (hinj₂ a ha this)
    · exact h
  let f₁ : ↥J →* ↥W₁ :=
    ((proj₁ hsum hinf).comp J.subtype).codRestrict W₁ fun a => proj₁_mem hsum hinf a
  let f₂ : ↥J →* ↥W₂ :=
    ((proj₂ hsum hinf).comp J.subtype).codRestrict W₂ fun a => proj₂_mem hsum hinf a
  have hf₁ : Function.Bijective f₁ := by
    refine ⟨(injective_iff_map_eq_one _).2 fun a ha =>
      Subtype.ext (hinj₁ a a.2 (congrArg Subtype.val ha)), ?_⟩
    rintro ⟨w, hw⟩
    rw [← himg₁] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    exact ⟨⟨a, ha⟩, rfl⟩
  have hf₂ : Function.Bijective f₂ := by
    refine ⟨(injective_iff_map_eq_one _).2 fun a ha =>
      Subtype.ext (hinj₂ a a.2 (congrArg Subtype.val ha)), ?_⟩
    rintro ⟨w, hw⟩
    rw [← himg₂] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    exact ⟨⟨a, ha⟩, rfl⟩
  set e₁ := MulEquiv.ofBijective f₁ hf₁ with he₁
  set e₂ := MulEquiv.ofBijective f₂ hf₂ with he₂
  apply hnoniso
  refine secIsoL_of_equiv hinv₁ hinv₂ (e₁.symm.trans e₂) fun k w => ?_
  set j := e₁.symm w with hj
  have hjw : proj₁ hsum hinf (j : V) = w := congrArg Subtype.val (e₁.apply_symm_apply w)
  have hkj : (⟨(k : MulAut V) j, hJ k k.2 j j.2⟩ : ↥J) =
      e₁.symm ⟨(k : MulAut V) w, hinv₁ k k.2 w w.2⟩ := by
    apply e₁.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    show proj₁ hsum hinf ((k : MulAut V) j) = (k : MulAut V) w
    rw [(hstab k k.2 j).1, hjw]
  show ((e₂ (e₁.symm ⟨(k : MulAut V) w, _⟩) : ↥W₂) : V) = (k : MulAut V) ((e₂ j : ↥W₂) : V)
  rw [← hkj]
  exact (hstab k k.2 j).2

theorem eq_one_of_fix₁ [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hirr₁ : ∀ J : Subgroup V, J ≤ W₁ → (∀ k ∈ L, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W₁)
    (hirr₂ : ∀ J : Subgroup V, J ≤ W₂ → (∀ k ∈ L, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W₂)
    (hW₂ : W₂ ≠ ⊥) (hnoniso : ¬ SecIsoL L W₂ ⊥ W₁ ⊥) {c : MulAut V}
    (hcL : ∀ k ∈ L, c * k = k * c) {e : ℕ} (hce : c ^ 2 ^ e = 1) (hc₁ : ∀ w ∈ W₁, c w = w) :
    c = 1 := by
  have hcomm : ∀ k ∈ L, ∀ v, c (k v) = k (c v) := fun k hk v => by
    have := congrArg (fun φ : MulAut V => φ v) (hcL k hk)
    simpa [MulAut.mul_apply] using this
  have hstab : c ∈ stabSub W₁ := fun u => by
    constructor
    · intro h
      have h1 : c⁻¹ (c u) = c u := by
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hc₁ _ h]
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h1
      rw [h1]
      exact h
    · intro h
      rw [hc₁ u h]
      exact h
  have hW₁top : W₁ ≠ ⊤ := by
    intro h
    apply hW₂
    rw [eq_bot_iff]
    intro w hw
    have hw1 : w ∈ W₁ := by rw [h]; trivial
    have : w ∈ W₁ ⊓ W₂ := ⟨hw1, hw⟩
    rwa [hinf] at this
  have : Nontrivial (V ⧸ W₁) := QuotientGroup.nontrivial_iff.2 hW₁top
  have hcq : quotHom W₁ ⟨c, hstab⟩ ^ 2 ^ e = 1 := by
    rw [← map_pow]
    have : (⟨c, hstab⟩ : ↥(stabSub W₁)) ^ 2 ^ e = 1 := Subtype.ext hce
    rw [this, map_one]
  have hVq : ∀ x : V ⧸ W₁, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, hV]
    rfl
  obtain ⟨x, hx1, hxfix⟩ := exists_fixed_of_two_pow hVq _ hcq
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
  have hcv : c v * v⁻¹ ∈ W₁ := (mk_eq_mk_iff (U := W₁) _ _).1 hxfix
  have hvW₁ : v ∉ W₁ := fun h => hx1 ((QuotientGroup.eq_one_iff v).2 h)
  have hcw : ∀ a b : V, c (a * b) * (a * b)⁻¹ = (c a * a⁻¹) * (c b * b⁻¹) := by
    intro a b
    rw [map_mul, mul_inv, mul_mul_mul_comm]
  let F' : Subgroup V :=
    { carrier := {w | w ∈ W₂ ∧ c w * w⁻¹ ∈ W₁}
      one_mem' := ⟨W₂.one_mem, by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨W₂.mul_mem ha.1 hb.1, by
        rw [hcw]
        exact W₁.mul_mem ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨W₂.inv_mem ha.1, by
        have e : c a⁻¹ * a⁻¹⁻¹ = (c a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv_rev, inv_inv, mul_comm]
        rw [e]
        exact W₁.inv_mem ha.2⟩ }
  have hF'inv : ∀ k ∈ L, ∀ w ∈ F', k w ∈ F' := by
    intro k hk w hw
    refine ⟨hinv₂ k hk w hw.1, ?_⟩
    rw [hcomm k hk, ← map_inv, ← map_mul]
    exact hinv₁ k hk _ hw.2
  have hψ : ∀ w ∈ W₂, c w * w⁻¹ ∈ W₁ := by
    rcases hirr₂ F' (fun w hw => hw.1) hF'inv with h | h
    · exfalso
      have hp2 : proj₂ hsum hinf v ∈ F' := by
        refine ⟨proj₂_mem hsum hinf v, ?_⟩
        have e1 := proj₁_mul_proj₂ hsum hinf v
        have e2 : c (proj₂ hsum hinf v) * (proj₂ hsum hinf v)⁻¹ = c v * v⁻¹ := by
          conv_rhs => rw [← e1]
          rw [hcw, hc₁ _ (proj₁_mem hsum hinf v), mul_inv_cancel, one_mul]
        rw [e2]
        exact hcv
      rw [h, Subgroup.mem_bot] at hp2
      apply hvW₁
      rw [← proj₁_mul_proj₂ hsum hinf v, hp2, mul_one]
      exact proj₁_mem hsum hinf v
    · intro w hw
      rw [← h] at hw
      exact hw.2
  let F₂ : Subgroup V :=
    { carrier := {w | w ∈ W₂ ∧ c w = w}
      one_mem' := ⟨W₂.one_mem, map_one c⟩
      mul_mem' := fun {a b} ha hb => ⟨W₂.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      inv_mem' := fun {a} ha => ⟨W₂.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  have hF₂inv : ∀ k ∈ L, ∀ w ∈ F₂, k w ∈ F₂ := fun k hk w hw =>
    ⟨hinv₂ k hk w hw.1, by rw [hcomm k hk, hw.2]⟩
  rcases hirr₂ F₂ (fun w hw => hw.1) hF₂inv with hF | hF
  · exfalso
    let ψ : ↥W₂ →* ↥W₁ :=
      { toFun := fun w => ⟨c w * (w : V)⁻¹, hψ w w.2⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          exact hcw a b }
    have hψinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro w hw
      have h1 : c w * (w : V)⁻¹ = 1 := congrArg Subtype.val hw
      have h2 : (w : V) ∈ F₂ := ⟨w.2, mul_inv_eq_one.1 h1⟩
      rw [hF, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    have hψsurj : Function.Surjective ψ := by
      set R : Subgroup V := ψ.range.map W₁.subtype with hR
      have hRinv : ∀ k ∈ L, ∀ w ∈ R, k w ∈ R := by
        rintro k hk _ ⟨_, ⟨w, rfl⟩, rfl⟩
        refine ⟨⟨_, hψ _ (hinv₂ k hk w w.2)⟩, ⟨⟨k w, hinv₂ k hk w w.2⟩, rfl⟩, ?_⟩
        show c (k w) * (k w)⁻¹ = k (c w * (w : V)⁻¹)
        rw [hcomm k hk, map_mul, map_inv]
      rcases hirr₁ R (Subgroup.map_subtype_le _) hRinv with h | h
      · exfalso
        obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW₂
        have : ((ψ ⟨w, hw⟩ : ↥W₁) : V) ∈ R := ⟨_, ⟨⟨w, hw⟩, rfl⟩, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        have h3 : ψ ⟨w, hw⟩ = 1 := Subtype.ext this
        exact hw1 (hψinj (h3.trans (map_one ψ).symm))
      · intro y
        have : (y : V) ∈ R := by rw [h]; exact y.2
        obtain ⟨_, ⟨w, rfl⟩, hz⟩ := this
        exact ⟨w, Subtype.ext hz⟩
    apply hnoniso
    refine secIsoL_of_equiv hinv₂ hinv₁ (MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩) fun k w => ?_
    show c ((k : MulAut V) w) * ((k : MulAut V) w)⁻¹ = (k : MulAut V) (c w * (w : V)⁻¹)
    rw [hcomm k k.2, map_mul, map_inv]
  · ext v
    rw [MulAut.one_apply, ← proj₁_mul_proj₂ hsum hinf v, map_mul, hc₁ _ (proj₁_mem hsum hinf v)]
    have h2 : proj₂ hsum hinf v ∈ F₂ := by
      rw [hF]
      exact proj₂_mem hsum hinf v
    rw [h2.2]

theorem eq_one_of_commute_of_sum [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hirr₁ : ∀ J : Subgroup V, J ≤ W₁ → (∀ k ∈ L, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W₁)
    (hirr₂ : ∀ J : Subgroup V, J ≤ W₂ → (∀ k ∈ L, ∀ w ∈ J, k w ∈ J) → J = ⊥ ∨ J = W₂)
    (hW₁ : W₁ ≠ ⊥) (hW₂ : W₂ ≠ ⊥) (hnoniso : ¬ SecIsoL L W₁ ⊥ W₂ ⊥) {c : MulAut V}
    (hcL : ∀ k ∈ L, c * k = k * c) {e : ℕ} (hce : c ^ 2 ^ e = 1) : c = 1 := by
  have hcomm : ∀ k ∈ L, ∀ v, c (k v) = k (c v) := fun k hk v => by
    have := congrArg (fun φ : MulAut V => φ v) (hcL k hk)
    simpa [MulAut.mul_apply] using this
  let F : Subgroup V :=
    { carrier := {v | c v = v}
      one_mem' := map_one c
      mul_mem' := fun {a b} ha hb => by
        show c (a * b) = a * b
        rw [map_mul, show c a = a from ha, show c b = b from hb]
      inv_mem' := fun {a} ha => by
        show c a⁻¹ = a⁻¹
        rw [map_inv, show c a = a from ha] }
  have hFinv : ∀ k ∈ L, ∀ v ∈ F, k v ∈ F := fun k hk v hv => by
    show c (k v) = k v
    rw [hcomm k hk, show c v = v from hv]
  have hFne : F ≠ ⊥ := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW₁
    have : Nontrivial V := ⟨⟨w, 1, fun h => hw1 (Subtype.ext h)⟩⟩
    obtain ⟨v, hv1, hvc⟩ := exists_fixed_of_two_pow hV c hce
    intro h
    have hv : v ∈ F := hvc
    rw [h, Subgroup.mem_bot] at hv
    exact hv1 hv
  have hsum' : W₂ ⊔ W₁ = ⊤ := by rw [sup_comm]; exact hsum
  have hinf' : W₂ ⊓ W₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hinvF : ∀ (W : Subgroup V), (∀ k ∈ L, ∀ w ∈ W, k w ∈ W) →
      ∀ k ∈ L, ∀ w ∈ F ⊓ W, k w ∈ F ⊓ W := fun W hW k hk w hw =>
    ⟨hFinv k hk w hw.1, hW k hk w hw.2⟩
  rcases hirr₁ (F ⊓ W₁) inf_le_right (hinvF W₁ hinv₁) with h₁ | h₁
  · rcases hirr₂ (F ⊓ W₂) inf_le_right (hinvF W₂ hinv₂) with h₂ | h₂
    · exact absurd (eq_bot_of_diag hsum hinf hinv₁ hinv₂ hirr₁ hirr₂ hnoniso hFinv h₁ h₂) hFne
    · refine eq_one_of_fix₁ hsum' hinf' hinv₂ hinv₁ hV hirr₂ hirr₁ hW₁ hnoniso hcL hce
        fun w hw => ?_
      have : w ∈ F ⊓ W₂ := by rw [h₂]; exact hw
      exact this.1
  · refine eq_one_of_fix₁ hsum hinf hinv₁ hinv₂ hV hirr₁ hirr₂ hW₂
      (fun h => hnoniso (secIsoL_symm hinv₂ hinv₁ h)) hcL hce fun w hw => ?_
    have : w ∈ F ⊓ W₁ := by rw [h₁]; exact hw
    exact this.1

end Sum

end CFSG.Quasithin.InternalSec
