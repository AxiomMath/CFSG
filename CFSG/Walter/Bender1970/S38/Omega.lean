module

public import CFSG.Walter.Bender1970.S38.Action

public section

namespace CFSG.Walter

variable {Y : Type*} [Group Y]

@[expose] def omegaCenter (p : ℕ) (D : Subgroup Y) : Subgroup Y where
  carrier := {x | x ∈ D ∧ x ^ p = 1 ∧ ∀ d ∈ D, x * d = d * x}
  mul_mem' {a b} ha hb := by
    refine ⟨D.mul_mem ha.1 hb.1, ?_, fun d hd => ?_⟩
    · rw [(Commute.mul_pow (ha.2.2 b hb.1) p), ha.2.1, hb.2.1, one_mul]
    · rw [mul_assoc, hb.2.2 d hd, ← mul_assoc, ha.2.2 d hd, mul_assoc]
  one_mem' := ⟨D.one_mem, one_pow p, fun d _ => by rw [one_mul, mul_one]⟩
  inv_mem' {a} ha := by
    refine ⟨D.inv_mem ha.1, by rw [inv_pow, ha.2.1, inv_one], fun d hd => ?_⟩
    exact (show Commute a d from ha.2.2 d hd).inv_left.eq

theorem mem_omegaCenter {p : ℕ} {D : Subgroup Y} {x : Y} :
    x ∈ omegaCenter p D ↔ x ∈ D ∧ x ^ p = 1 ∧ ∀ d ∈ D, x * d = d * x := Iff.rfl

theorem omegaCenter_le (p : ℕ) (D : Subgroup Y) : omegaCenter p D ≤ D := fun _ hx => hx.1

theorem conj_mem_omegaCenter {p : ℕ} {D : Subgroup Y} {y : Y}
    (hy : ∀ d ∈ D, y * d * y⁻¹ ∈ D) (hy' : ∀ d ∈ D, y⁻¹ * d * y ∈ D) {x : Y}
    (hx : x ∈ omegaCenter p D) : y * x * y⁻¹ ∈ omegaCenter p D := by
  refine ⟨hy x hx.1, ?_, fun d hd => ?_⟩
  · rw [conj_pow, hx.2.1, mul_one, mul_inv_cancel]
  · have h := hx.2.2 _ (hy' d hd)
    calc y * x * y⁻¹ * d = y * (x * (y⁻¹ * d * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * d * y) * x) * y⁻¹ := by rw [h]
      _ = d * (y * x * y⁻¹) := by group

theorem card_mul_card_le_of_inf_eq_bot [Finite Y] {H K L : Subgroup Y} (hHL : H ≤ L)
    (hKL : K ≤ L) (hHK : H ⊓ K = ⊥) : Nat.card H * Nat.card K ≤ Nat.card L := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun x : H × K => (⟨x.1 * x.2,
    L.mul_mem (hHL x.1.2) (hKL x.2.2)⟩ : L)) fun x y h => ?_
  have h1 : (x.1 : Y) * x.2 = y.1 * y.2 := congrArg Subtype.val h
  have h2 : (y.1 : Y)⁻¹ * x.1 = y.2 * (x.2 : Y)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h1, mul_inv_cancel_right]
  have h3 : (y.1 : Y)⁻¹ * x.1 ∈ H ⊓ K :=
    ⟨H.mul_mem (H.inv_mem y.1.2) x.1.2, h2 ▸ K.mul_mem y.2.2 (K.inv_mem x.2.2)⟩
  rw [hHK, Subgroup.mem_bot, inv_mul_eq_one] at h3
  have h4 : (x.2 : Y) = y.2 := by rw [h3] at h1; exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)

theorem map_conj_pow_eq [Finite Y] {S : Subgroup Y} {g : Y}
    (h : S.map (MulAut.conj g).toMonoidHom = S) (n : ℕ) :
    S.map (MulAut.conj (g ^ n)).toMonoidHom = S := by
  refine Subgroup.eq_of_le_of_card_ge ?_
    (Subgroup.card_map_of_injective (MulAut.conj (g ^ n)).injective).ge
  have h1 : ∀ x ∈ S, g * x * g⁻¹ ∈ S := fun x hx => h ▸ ⟨x, hx, rfl⟩
  have h2 : ∀ n : ℕ, ∀ x ∈ S, g ^ n * x * (g ^ n)⁻¹ ∈ S := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      have e : g ^ (n + 1) * x * (g ^ (n + 1))⁻¹ = g ^ n * (g * x * g⁻¹) * (g ^ n)⁻¹ := by
        group
      rw [e]
      exact ih _ (h1 x hx)
  rintro _ ⟨x, hx, rfl⟩
  exact h2 n x hx

variable {A : Type*} [CommGroup A]

@[expose] def kerOn (ρ : Y →* MulAut A) (Q : Subgroup A) : Subgroup Y where
  carrier := {x | ∀ v ∈ Q, ρ x v = v}
  mul_mem' {a b} ha hb v hv := by rw [map_mul, MulAut.mul_apply, hb v hv, ha v hv]
  one_mem' v _ := by rw [map_one, MulAut.one_apply]
  inv_mem' {a} ha v hv := by
    rw [map_inv]
    conv_lhs => rw [← ha v hv]
    exact MulAut.inv_apply_self A (ρ a) v

theorem mem_kerOn {ρ : Y →* MulAut A} {Q : Subgroup A} {x : Y} :
    x ∈ kerOn ρ Q ↔ ∀ v ∈ Q, ρ x v = v := Iff.rfl

namespace Bender38Action

variable {ρ : Y →* MulAut A} {W Q : Subgroup A} {X R : Subgroup Y}
  (hD : Bender38Action ρ W Q X R)
include hD

theorem mul_inv_mem_W {x : Y} (hxX : x ∈ X) (hxQ : x ∈ kerOn ρ Q) (a : A) :
    ρ x a * a⁻¹ ∈ W := by
  obtain ⟨w, hw, v, hv, rfl⟩ := hD.exists_mul a
  have h : ρ x (w * v) * (w * v)⁻¹ = ρ x w * w⁻¹ := by
    rw [map_mul, hxQ v hv, mul_inv_rev, mul_comm v⁻¹ w⁻¹, mul_assoc, ← mul_assoc v,
      mul_comm v w⁻¹, mul_assoc, mul_inv_cancel, mul_one]
  rw [h]
  exact W.mul_mem (hD.map_mem_W x hxX w hw) (W.inv_mem hw)

theorem mem_X_of_normalizes [Finite A] [Finite Y] {F D : Subgroup Y} (hFX : F ≤ X) (hRF : R ≤ F)
    (hF : Group.IsNilpotent F) {p : ℕ} (hp : p.Prime) (hDF : D ≤ F) (hDp : IsPGroup p D)
    (hpelem : ∀ x ∈ F, ∀ k : ℕ, x ^ p ^ k = 1 → x ∈ D) (hP : omegaCenter p D ≠ ⊥) {y : Y}
    (hy : ∀ z ∈ omegaCenter p D, y * z * y⁻¹ ∈ omegaCenter p D) : y ∈ X := by
  classical
  by_contra hyX
  have : Fact p.Prime := ⟨hp⟩
  set P := omegaCenter p D with hPdef
  set K := kerOn ρ Q with hK
  set P₁ := P ⊓ R with hP₁
  set P₂ := P ⊓ K with hP₂
  have hPX : P ≤ X := (omegaCenter_le p D).trans (hDF.trans hFX)
  have hRK : ∀ x ∈ R, x ∈ K → x = 1 := fun x hx hxK => hD.eq_one_of_mem_R_of_fix_Q hx hxK
  have hcardmap : ∀ (g : Y) (S : Subgroup Y),
      Nat.card (S.map (MulAut.conj g).toMonoidHom) = Nat.card S := fun g S =>
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hyP : P.map (MulAut.conj y).toMonoidHom = P := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (hcardmap y P).ge
    rintro _ ⟨z, hz, rfl⟩
    exact hy z hz
  have hy' : ∀ z ∈ P, y⁻¹ * z * y ∈ P := by
    intro z hz
    rw [← hyP] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    simpa [MulAut.conj_apply, mul_assoc] using hx
  have hdecomp : ∀ z ∈ P, ∃ r ∈ P₁, ∃ c ∈ P₂, r * c = z := by
    intro z hz
    have hzF : z ∈ F := hDF hz.1
    obtain ⟨r, hr, hrz⟩ := hD.exists_mem_centralizerQ hFX hRF hF hzF
    set c := r⁻¹ * z with hc
    have hcK : c ∈ K := hrz
    have hrF : r ∈ F := hRF hr
    have hcF : c ∈ F := F.mul_mem (F.inv_mem hrF) hzF
    have hzr : z * r = r * z := hD.commute_of_mem hFX hRF hF hzF hr
    have hrc : Commute r c := by
      show r * (r⁻¹ * z) = r⁻¹ * z * r
      rw [mul_inv_cancel_left, mul_assoc, hzr, inv_mul_cancel_left]
    have hrcz : r * c = z := by rw [hc, mul_inv_cancel_left]
    obtain ⟨k, hk⟩ := hDp ⟨z, hz.1⟩
    have hzk : z ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hpow : ∀ m : ℕ, z ^ m = 1 → r ^ m = 1 ∧ c ^ m = 1 := by
      intro m hm
      rw [← hrcz, hrc.mul_pow] at hm
      have h1 : r ^ m = (c ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hm
      have h2 : r ^ m = 1 := hRK _ (R.pow_mem hr m) (h1 ▸ K.inv_mem (K.pow_mem hcK m))
      refine ⟨h2, ?_⟩
      rw [h2, one_mul] at hm
      exact hm
    obtain ⟨hrk, hck⟩ := hpow _ hzk
    have hrD : r ∈ D := hpelem r hrF k hrk
    have hcD : c ∈ D := hpelem c hcF k hck
    obtain ⟨hrp, hcp⟩ := hpow p hz.2.1
    have hrcomm : ∀ d ∈ D, r * d = d * r := fun d hd =>
      (hD.commute_of_mem hFX hRF hF (hDF hd) hr).symm
    have hccomm : ∀ d ∈ D, c * d = d * c := fun d hd =>
      ((show Commute r d from hrcomm d hd).inv_left.mul_left
        (show Commute z d from hz.2.2 d hd)).eq
    exact ⟨r, ⟨⟨hrD, hrp, hrcomm⟩, hr⟩, c, ⟨⟨hcD, hcp, hccomm⟩, hcK⟩, hrcz⟩
  have hP₁₂ : P₁ ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hxR⟩, ⟨-, hxK⟩⟩
    exact hRK x hxR hxK
  have hcardP : Nat.card P = Nat.card P₁ * Nat.card P₂ := by
    refine le_antisymm ?_ (card_mul_card_le_of_inf_eq_bot inf_le_left inf_le_left hP₁₂)
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_surjective (fun x : P₁ × P₂ => (⟨x.1 * x.2,
      P.mul_mem x.1.2.1 x.2.2.1⟩ : P)) fun z => ?_
    obtain ⟨r, hr, c, hc, hrc⟩ := hdecomp z z.2
    exact ⟨(⟨r, hr⟩, ⟨c, hc⟩), Subtype.ext hrc⟩
  have hP₁le : Nat.card P₁ ≤ p := by
    have : IsCyclic R := hD.isCyclic
    have hcyc : IsCyclic (P₁.subgroupOf R) := inferInstance
    have e := Subgroup.subgroupOfEquivOfLe (show P₁ ≤ R from inf_le_right)
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hgp : g ^ p = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have h1 : (((g : P₁.subgroupOf R) : R) : Y) ∈ P₁ := g.2
      simpa using h1.1.2.1
    have hcard : Nat.card (P₁.subgroupOf R) = orderOf g :=
      (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    rw [← Nat.card_congr e.toEquiv, hcard]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  have hP₁y : (P₁.map (MulAut.conj y).toMonoidHom) ⊓ P₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨x, hx, rfl⟩, hz⟩
    rw [Subgroup.mem_bot]
    by_contra hz1
    have hx1 : x ≠ 1 := by
      rintro rfl
      simp at hz1
    exact hyX (hD.mem_X_of_conj_mem hx.2 hx1 hz.2)
  have hP₂y : (P₂.map (MulAut.conj y).toMonoidHom) ⊓ P₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨⟨x, hx, rfl⟩, hz⟩
    rw [Subgroup.mem_bot]
    apply hD.injective
    rw [map_one]
    ext a
    rw [MulAut.one_apply]
    set a' := ρ y⁻¹ a with ha'
    have h1 : ρ x a' * a'⁻¹ ∈ W := hD.mul_inv_mem_W (hPX hx.1) hx.2 a'
    have h2 : ρ y (ρ x a' * a'⁻¹) = ρ ((MulAut.conj y).toMonoidHom x) a * a⁻¹ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul (ρ y), map_inv (ρ y),
        map_mul ρ, map_mul ρ, MulAut.mul_apply, MulAut.mul_apply, ha', map_inv ρ y,
        MulAut.apply_inv_self]
    have h3 : ρ ((MulAut.conj y).toMonoidHom x) a * a⁻¹ ∈ W :=
      hD.mul_inv_mem_W (hPX hz.1) hz.2 a
    have h4 := hD.eq_one_of_not_mem hyX h1 (h2 ▸ h3)
    rw [h4, map_one] at h2
    exact mul_inv_eq_one.mp h2.symm
  have hP₁P : P₁ ≤ P := inf_le_left
  have hP₂P : P₂ ≤ P := inf_le_left
  have hmapP : ∀ S ≤ P, S.map (MulAut.conj y).toMonoidHom ≤ P := by
    rintro S hS _ ⟨x, hx, rfl⟩
    exact hy x (hS hx)
  have hsq₁ : Nat.card P₁ * Nat.card P₁ ≤ Nat.card P := by
    have h := card_mul_card_le_of_inf_eq_bot (hmapP P₁ hP₁P) hP₁P hP₁y
    rwa [hcardmap] at h
  have hsq₂ : Nat.card P₂ * Nat.card P₂ ≤ Nat.card P := by
    have h := card_mul_card_le_of_inf_eq_bot (hmapP P₂ hP₂P) hP₂P hP₂y
    rwa [hcardmap] at h
  have hP1 : 1 < Nat.card P := (Subgroup.one_lt_card_iff_ne_bot P).mpr hP
  have hpos₁ : 0 < Nat.card P₁ := Nat.card_pos
  have hpos₂ : 0 < Nat.card P₂ := Nat.card_pos
  have heq₁₂ : Nat.card P₁ = Nat.card P₂ := by
    rw [hcardP] at hsq₁ hsq₂
    exact le_antisymm (Nat.le_of_mul_le_mul_left hsq₁ hpos₁)
      (Nat.le_of_mul_le_mul_right hsq₂ hpos₂)
  have hcard₁ : Nat.card P₁ = p := by
    obtain ⟨j, hj⟩ := (hDp.to_le ((inf_le_left : P₁ ≤ P).trans (omegaCenter_le p D))).exists_card_eq
    have hj1 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      rw [hcardP, ← heq₁₂, hj] at hP1
      omega
    have hjle : p ^ j ≤ p ^ 1 := by rw [← hj, pow_one]; exact hP₁le
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hjle
    rw [hj, show j = 1 by omega, pow_one]
  have hcard₂ : Nat.card P₂ = p := heq₁₂ ▸ hcard₁
  have hcardPp : Nat.card P = p * p := by rw [hcardP, hcard₁, hcard₂]
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard₁
    exact hp.one_lt.ne hcard₁
  have hP₂ne : P₂ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard₂
    exact hp.one_lt.ne hcard₂
  have hinf_bot : ∀ S T : Subgroup Y, Nat.card S = p → Nat.card T = p → S ≠ T → S ⊓ T = ⊥ := by
    intro S T hS hT hST
    have hdvd : Nat.card (S ⊓ T : Subgroup Y) ∣ p := hS ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      apply hST
      have h1 : S ⊓ T = S := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hS])
      have h2 : S ⊓ T = T := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hT])
      rw [← h1, h2]
  have hsup_eq : ∀ S T : Subgroup Y, S ≤ P → T ≤ P → Nat.card S = p → Nat.card T = p →
      S ≠ T → S ⊔ T = P := by
    intro S T hSP hTP hS hT hST
    refine Subgroup.eq_of_le_of_card_ge (sup_le hSP hTP) ?_
    calc Nat.card P = Nat.card S * Nat.card T := by rw [hcardPp, hS, hT]
      _ ≤ Nat.card (S ⊔ T : Subgroup Y) :=
        card_mul_card_le_of_inf_eq_bot le_sup_left le_sup_right (hinf_bot S T hS hT hST)
  have hfixP : ∀ a ∈ fixOf ρ P, a = 1 := by
    intro a ha
    obtain ⟨⟨r, hrP₁⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP₁ne
    have haW : a ∈ W := (hD.fix_iff hrP₁.2 (fun h => hr1 (Subtype.ext h)) a).mp (ha r hrP₁.1)
    have hyaW : ρ y a ∈ W := by
      have h1 : ρ y a ∈ fixOf ρ P := fun s hs => map_mem_fixOf_conj ha y (hy' s hs)
      exact (hD.fix_iff hrP₁.2 (fun h => hr1 (Subtype.ext h)) _).mp (h1 r hrP₁.1)
    exact hD.eq_one_of_not_mem hyX haW hyaW
  have hspecial : ∀ S : Subgroup Y, S ≤ P → Nat.card S = p → S ≠ P₁ → S ≠ P₂ →
      ∀ a ∈ fixOf ρ S, a = 1 := by
    intro S hSP hS hS₁ hS₂ a ha
    obtain ⟨w, hw, v, hv, rfl⟩ := hD.exists_mul a
    have hfix : ∀ s ∈ S, ρ s w = w ∧ ρ s v = v := by
      intro s hs
      have hsX : s ∈ X := hPX (hSP hs)
      have h1 := ha s hs
      rw [map_mul] at h1
      exact hD.eq_of_mul_eq (hD.map_mem_W s hsX w hw) hw (hD.map_mem_Q s hsX v hv) hv h1
    have hvP : v ∈ fixOf ρ P := by
      rw [mem_fixOf_iff_le_stabOf, ← hsup_eq S P₂ hSP hP₂P hS hcard₂ hS₂]
      exact sup_le (fun s hs => (hfix s hs).2) (fun c hc => hc.2 v hv)
    have hwP : w ∈ fixOf ρ P := by
      rw [mem_fixOf_iff_le_stabOf, ← hsup_eq S P₁ hSP hP₁P hS hcard₁ hS₁]
      exact sup_le (fun s hs => (hfix s hs).1) (fun r hr => hD.fix_W r hr.2 w hw)
    rw [hfixP v hvP, hfixP w hwP, mul_one]
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD.ne_bot
  have hw₀1' : w₀ ≠ 1 := fun h => hw₀1 (Subtype.ext h)
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v ∈ Q, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr hcon
    have h4 := hD.four_le_card
    rw [this, Subgroup.card_bot] at h4
    omega
  have hyw₀ : ρ y w₀ ≠ 1 := fun h => hw₀1' ((MulEquiv.map_eq_one_iff _).mp h)
  have hyv₀ : ρ y v₀ ≠ 1 := fun h => hv₀1 ((MulEquiv.map_eq_one_iff _).mp h)
  have hconjfix : ∀ S : Subgroup Y, ∀ a ∈ fixOf ρ S,
      ρ y a ∈ fixOf ρ (S.map (MulAut.conj y).toMonoidHom) := by
    rintro S a ha _ ⟨x, hx, rfl⟩
    refine map_mem_fixOf_conj ha y ?_
    simpa [MulAut.conj_apply, mul_assoc] using hx
  have hmap₁ : P₁.map (MulAut.conj y).toMonoidHom = P₂ := by
    by_contra hne₂
    have hne₁ : P₁.map (MulAut.conj y).toMonoidHom ≠ P₁ := by
      intro h
      rw [h, inf_idem] at hP₁y
      exact hP₁ne hP₁y
    exact hyw₀ (hspecial _ (hmapP P₁ hP₁P) (by rw [hcardmap, hcard₁]) hne₁ hne₂ _
      (hconjfix P₁ w₀ fun r hr => hD.fix_W r hr.2 w₀ hw₀))
  have hmap₂ : P₂.map (MulAut.conj y).toMonoidHom = P₁ := by
    by_contra hne₁
    have hne₂ : P₂.map (MulAut.conj y).toMonoidHom ≠ P₂ := by
      intro h
      rw [h, inf_idem] at hP₂y
      exact hP₂ne hP₂y
    exact hyv₀ (hspecial _ (hmapP P₂ hP₂P) (by rw [hcardmap, hcard₂]) hne₁ hne₂ _
      (hconjfix P₂ v₀ fun c hc => hc.2 v₀ hv₀))
  have hmapsq : P₁.map (MulAut.conj (y ^ 2)).toMonoidHom = P₁ := by
    have h1 : (MulAut.conj (y ^ 2)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, pow_two, mul_assoc]
    rw [h1, ← Subgroup.map_map, hmap₁, hmap₂]
  obtain ⟨k, hk⟩ : Odd (orderOf y) :=
    Odd.of_dvd_nat hD.odd_card (orderOf_dvd_natCard y)
  have hyk : (y ^ 2) ^ (k + 1) = y := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hfinal := map_conj_pow_eq hmapsq (k + 1)
  rw [hyk, hmap₁] at hfinal
  have h1 : P₁ ⊓ P₂ = P₁ := by rw [hfinal, inf_idem]
  exact hP₁ne (h1.symm.trans hP₁₂)

end Bender38Action

end CFSG.Walter
