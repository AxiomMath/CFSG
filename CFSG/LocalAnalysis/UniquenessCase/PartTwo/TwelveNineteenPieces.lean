module

public import CFSG.Quasithin.Background.Module
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

namespace TwelveNineteen

variable {W : Type} [CommGroup W] [Finite W]

@[expose] noncomputable def normHom (B : Subgroup (MulAut W)) : W →* W where
  toFun w := ∏ᶠ b ∈ (B : Set (MulAut W)), b w
  map_one' := by simp
  map_mul' v w := by
    haveI : Finite (MulAut W) := MulEquiv.finite_left
    simp only [map_mul]
    exact finprod_mem_mul_distrib (Set.toFinite _)

@[expose] noncomputable def kSub (A H : Subgroup (MulAut W)) : Subgroup W :=
  fixV H ⊓ (normHom A).ker

@[expose] noncomputable def deltaSet (p : ℕ) (A : Subgroup (MulAut W)) :
    Set (Subgroup (MulAut W)) :=
  {H | H ≤ A ∧ H.relIndex A = p ∧ kSub A H ≠ ⊥}

theorem normHom_apply (B : Subgroup (MulAut W)) (w : W) :
    normHom B w = ∏ᶠ b ∈ (B : Set (MulAut W)), b w :=
  rfl

private theorem normHom_eq_prod (B : Subgroup (MulAut W)) [Fintype B] (w : W) :
    normHom B w = ∏ b : B, (b : MulAut W) w := by
  rw [normHom_apply, ← finprod_set_coe_eq_finprod_mem]
  exact finprod_eq_prod_of_fintype (fun b : B => (b : MulAut W) w)

private theorem mem_kSub {A H : Subgroup (MulAut W)} {w : W} :
    w ∈ kSub A H ↔ w ∈ fixV H ∧ normHom A w = 1 := by
  rw [kSub, Subgroup.mem_inf, MonoidHom.mem_ker]

private theorem pow_odd_eq_self (hW : ∀ w : W, w * w = 1) {n : ℕ} (hn : Odd n) (w : W) :
    w ^ n = w := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, sq, hW, one_pow, one_mul]

private theorem odd_card_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B : Subgroup (MulAut W)} (hB : ∀ b ∈ B, b ^ p = 1) : Odd (Nat.card B) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  have hpB : IsPGroup p B := fun b => ⟨1, Subtype.ext (by simpa using hB b b.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hpB
  rw [hn]
  exact (hp.odd_of_ne_two hp2).pow

private theorem mem_fixV_zpowers_of {c : MulAut W} {v : W} (h : c v = v) :
    v ∈ fixV (zpowers c) := by
  have hs : zpowers c ≤ MulAction.stabilizer (MulAut W) v :=
    zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact h)
  rw [mem_fixV]
  intro x hx
  have := hs hx
  rwa [MulAction.mem_stabilizer_iff] at this

private theorem comm_of_mem {p : ℕ} {A : Subgroup (MulAut W)} (hA : IsElemAbelian p A)
    {a b : MulAut W} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem normHom_mem_fixV (B : Subgroup (MulAut W)) (w : W) : normHom B w ∈ fixV B := by
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Fintype B := Fintype.ofFinite B
  rw [mem_fixV]
  intro g hg
  rw [normHom_eq_prod, map_prod]
  have h1 : ∀ d : B, g ((d : MulAut W) w) = ((⟨g, hg⟩ * d : B) : MulAut W) w := fun d => rfl
  simp only [h1]
  exact Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : B)) _ (fun d : B => (d : MulAut W) w)
    fun _ => rfl

theorem normHom_of_mem_fixV (B : Subgroup (MulAut W)) {w : W} (hw : w ∈ fixV B) :
    normHom B w = w ^ Nat.card B := by
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Fintype B := Fintype.ofFinite B
  rw [normHom_eq_prod]
  have h1 : ∀ d : B, (d : MulAut W) w = w := fun d => mem_fixV.1 hw d d.2
  simp only [h1, Finset.prod_const, Finset.card_univ, Fintype.card_eq_nat_card]

theorem normHom_apply_of_mem_normalizer {A : Subgroup (MulAut W)} {s : MulAut W}
    (hs : s ∈ normalizer (A : Set (MulAut W))) (w : W) :
    normHom A (s w) = s (normHom A w) := by
  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Fintype A := Fintype.ofFinite A
  have hconj : ∀ d : A, s * (d : MulAut W) * s⁻¹ ∈ A := fun d =>
    (mem_normalizer_iff.1 hs d).1 d.2
  have hconj' : ∀ d : A, s⁻¹ * (d : MulAut W) * s ∈ A := by
    intro d
    apply (mem_normalizer_iff.1 hs (s⁻¹ * (d : MulAut W) * s)).2
    have e : s * (s⁻¹ * (d : MulAut W) * s) * s⁻¹ = d := by group
    rw [e]
    exact d.2
  let e : A ≃ A :=
    { toFun := fun d => ⟨s * d * s⁻¹, hconj d⟩
      invFun := fun d => ⟨s⁻¹ * d * s, hconj' d⟩
      left_inv := fun d => Subtype.ext (by simp [mul_assoc])
      right_inv := fun d => Subtype.ext (by simp [mul_assoc]) }
  rw [normHom_eq_prod A (s w), normHom_eq_prod A w, map_prod]
  symm
  refine Fintype.prod_equiv e _ _ fun d => ?_
  show s ((d : MulAut W) w) = (s * d * s⁻¹) (s w)
  simp [MulAut.mul_apply]

private theorem normHom_eq_comp {p : ℕ} (hp : p.Prime) {B C : Subgroup (MulAut W)}
    (hB : IsElemAbelian p B) (hCB : C ≤ B) (hC : C.relIndex B = p) {b : MulAut W} (hb : b ∈ B)
    (hbC : b ∉ C) (w : W) : normHom B w = normHom (zpowers b) (normHom C w) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Fintype B := Fintype.ofFinite B
  haveI : Fintype C := Fintype.ofFinite C
  haveI : Fintype (zpowers b) := Fintype.ofFinite _
  have hb1 : b ≠ 1 := fun h => hbC (h ▸ C.one_mem)
  have hbp : orderOf b = p := orderOf_eq_prime (hB.2 b hb) hb1
  have hDB : zpowers b ≤ B := zpowers_le.2 hb
  have hinf : zpowers b ⊓ C = ⊥ := by
    have hdvd : Nat.card (zpowers b ⊓ C : Subgroup (MulAut W)) ∣ p := by
      rw [← hbp, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : zpowers b ⊓ C = zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hbp, h1])
      have hle : zpowers b ≤ C := heq ▸ inf_le_right
      exact hbC (hle (mem_zpowers b))
  have hmem : ∀ z : zpowers b × C, (z.1 : MulAut W) * z.2 ∈ B := fun z =>
    B.mul_mem (hDB z.1.2) (hCB z.2.2)
  let f : zpowers b × C → B := fun z => ⟨(z.1 : MulAut W) * z.2, hmem z⟩
  have hinj : Function.Injective f := by
    rintro ⟨x, c⟩ ⟨x', c'⟩ h
    have h' : (x : MulAut W) * c = x' * c' := congrArg Subtype.val h
    have hx : (x' : MulAut W)⁻¹ * x = c' * (c : MulAut W)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
    have hmem1 : (x' : MulAut W)⁻¹ * x ∈ zpowers b ⊓ C :=
      ⟨(zpowers b).mul_mem ((zpowers b).inv_mem x'.2) x.2,
        hx ▸ C.mul_mem c'.2 (C.inv_mem c.2)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem1
    have hxx : x = x' := Subtype.ext hmem1.symm
    subst hxx
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
  have hcard : Nat.card B ≤ Nat.card (zpowers b × C) := by
    rw [Nat.card_prod, Nat.card_zpowers, hbp]
    have := relIndex_mul_card C B
    rw [hC, inf_eq_left.2 hCB] at this
    exact this.ge
  let e : zpowers b × C ≃ B := Equiv.ofBijective f (hinj.bijective_of_nat_card_le hcard)
  rw [normHom_eq_prod B, normHom_eq_prod C, normHom_eq_prod (zpowers b),
    ← Fintype.prod_equiv e (fun z => ((z.1 : MulAut W) * z.2) w)
      (fun g : B => (g : MulAut W) w) (fun z => rfl),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [map_prod]
  rfl

theorem normHom_eq_normHom_zpowers (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {B C : Subgroup (MulAut W)} (hB : IsElemAbelian p B) (hCB : C ≤ B)
    (hC : C.relIndex B = p) {b : MulAut W} (hb : b ∈ B) (hbC : b ∉ C) {w : W}
    (hw : w ∈ fixV C) : normHom B w = normHom (zpowers b) w := by
  rw [normHom_eq_comp hp hB hCB hC hb hbC w, normHom_of_mem_fixV C hw,
    pow_odd_eq_self hW (odd_card_of_pow_eq_one hp hp2 fun c hc => hB.2 c (hCB hc)) w]

private theorem card_sup_of_inf_eq_bot {K U : Subgroup W} (h : K ⊓ U = ⊥) :
    Nat.card (K ⊔ U : Subgroup W) = Nat.card K * Nat.card U := by
  have hmem : ∀ z : K × U, (z.1 : W) * z.2 ∈ K ⊔ U := fun z =>
    (K ⊔ U).mul_mem (mem_sup_left z.1.2) (mem_sup_right z.2.2)
  let f : K × U → (K ⊔ U : Subgroup W) := fun z => ⟨(z.1 : W) * z.2, hmem z⟩
  have hinj : Function.Injective f := by
    rintro ⟨k, u⟩ ⟨k', u'⟩ hku
    have h' : (k : W) * u = k' * u' := congrArg Subtype.val hku
    have hk : (k' : W)⁻¹ * k ∈ K ⊓ U := by
      refine ⟨K.mul_mem (K.inv_mem k'.2) k.2, ?_⟩
      have e : (k' : W)⁻¹ * k = u' * (u : W)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
      rw [e]
      exact U.mul_mem u'.2 (U.inv_mem u.2)
    rw [h, Subgroup.mem_bot, inv_mul_eq_one] at hk
    have hkk : k = k' := Subtype.ext hk.symm
    subst hkk
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel h'))
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm

theorem card_iSup_kSub (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (𝓗 : Finset (Subgroup (MulAut W)))
    (h𝓗 : ∀ H ∈ 𝓗, H ≤ A ∧ H.relIndex A = p) :
    Nat.card (⨆ H ∈ 𝓗, kSub A H : Subgroup W) = ∏ H ∈ 𝓗, Nat.card (kSub A H) := by
  classical
  induction 𝓗 using Finset.induction_on with
  | empty => simp
  | insert H₀ 𝓗' hH₀ ih =>
    have h𝓗' : ∀ H ∈ 𝓗', H ≤ A ∧ H.relIndex A = p := fun H hH =>
      h𝓗 H (Finset.mem_insert_of_mem hH)
    obtain ⟨hH₀A, hH₀p⟩ := h𝓗 H₀ (Finset.mem_insert_self H₀ 𝓗')
    rw [Finset.iSup_insert, Finset.prod_insert hH₀, ← ih h𝓗']
    refine card_sup_of_inf_eq_bot ?_
    have hker : (⨆ H ∈ 𝓗', kSub A H) ≤ (normHom H₀).ker := by
      refine iSup₂_le fun H hH => ?_
      obtain ⟨hHA, hHp⟩ := h𝓗' H hH
      have hne : H ≠ H₀ := fun h => hH₀ (h ▸ hH)
      obtain ⟨c, hcH, hcH₀⟩ : ∃ c ∈ H, c ∉ H₀ := by
        by_contra hcon
        simp only [not_exists, not_and, not_not] at hcon
        apply hne
        refine Subgroup.eq_of_le_of_card_ge hcon ?_
        have e1 := relIndex_mul_card H A
        have e2 := relIndex_mul_card H₀ A
        rw [hHp, inf_eq_left.2 hHA] at e1
        rw [hH₀p, inf_eq_left.2 hH₀A] at e2
        exact (Nat.eq_of_mul_eq_mul_left hp.pos (e2.trans e1.symm)).le
      have hcA : c ∈ A := hHA hcH
      have hcN : c ∈ normalizer (H₀ : Set (MulAut W)) :=
        Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.2 fun h hh => comm_of_mem hA (hH₀A hh) hcA)
      intro w hw
      obtain ⟨hwH, hwA⟩ := mem_kSub.1 hw
      rw [MonoidHom.mem_ker]
      have hv : normHom H₀ w ∈ fixV (zpowers c) := by
        apply mem_fixV_zpowers_of
        rw [← normHom_apply_of_mem_normalizer hcN, mem_fixV.1 hwH c hcH]
      have hcodd : Odd (Nat.card (zpowers c)) :=
        odd_card_of_pow_eq_one hp hp2 fun x hx => hA.2 x (zpowers_le.2 hcA hx)
      calc normHom H₀ w = normHom H₀ w ^ Nat.card (zpowers c) :=
            (pow_odd_eq_self hW hcodd _).symm
        _ = normHom (zpowers c) (normHom H₀ w) := (normHom_of_mem_fixV _ hv).symm
        _ = normHom A w := (normHom_eq_comp hp hA hH₀A hH₀p hcA hcH₀ w).symm
        _ = 1 := hwA
    rw [eq_bot_iff]
    rintro w ⟨hw₀, hwU⟩
    have h1 : normHom H₀ w = 1 := MonoidHom.mem_ker.1 (hker hwU)
    have hH₀odd : Odd (Nat.card H₀) :=
      odd_card_of_pow_eq_one hp hp2 fun x hx => hA.2 x (hH₀A hx)
    rw [normHom_of_mem_fixV H₀ (mem_kSub.1 hw₀).1, pow_odd_eq_self hW hH₀odd] at h1
    exact Subgroup.mem_bot.2 h1

theorem iSup_kSub_inf_fixV_eq_bot (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup (MulAut W)} (hA : IsElemAbelian p A) {a : MulAut W}
    (ha : a ∈ A) (𝓗 : Finset (Subgroup (MulAut W)))
    (h𝓗 : ∀ H ∈ 𝓗, H ≤ A ∧ H.relIndex A = p ∧ a ∉ H) :
    (⨆ H ∈ 𝓗, kSub A H : Subgroup W) ⊓ fixV (zpowers a) = ⊥ := by
  have hker : (⨆ H ∈ 𝓗, kSub A H) ≤ (normHom (zpowers a)).ker := by
    refine iSup₂_le fun H hH => ?_
    obtain ⟨hHA, hHp, haH⟩ := h𝓗 H hH
    intro w hw
    obtain ⟨hwH, hwA⟩ := mem_kSub.1 hw
    rw [MonoidHom.mem_ker, ← normHom_eq_normHom_zpowers hW hp hp2 hA hHA hHp ha haH hwH]
    exact hwA
  rw [eq_bot_iff]
  rintro w ⟨hwU, hwa⟩
  have h1 : normHom (zpowers a) w = 1 := MonoidHom.mem_ker.1 (hker hwU)
  have haodd : Odd (Nat.card (zpowers a)) :=
    odd_card_of_pow_eq_one hp hp2 fun x hx => hA.2 x (zpowers_le.2 ha hx)
  rw [normHom_of_mem_fixV _ hwa, pow_odd_eq_self hW haodd] at h1
  exact Subgroup.mem_bot.2 h1

theorem prod_card_kSub_le_index (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup (MulAut W)} (hA : IsElemAbelian p A) {a : MulAut W}
    (ha : a ∈ A) (𝓗 : Finset (Subgroup (MulAut W)))
    (h𝓗 : ∀ H ∈ 𝓗, H ≤ A ∧ H.relIndex A = p ∧ a ∉ H) :
    ∏ H ∈ 𝓗, Nat.card (kSub A H) ≤ (fixV (zpowers a)).index := by
  rw [← card_iSup_kSub hW hp hp2 hA 𝓗 fun H hH => ⟨(h𝓗 H hH).1, (h𝓗 H hH).2.1⟩,
    Subgroup.index_eq_card]
  have hbot := iSup_kSub_inf_fixV_eq_bot hW hp hp2 hA ha 𝓗 h𝓗
  set U : Subgroup W := ⨆ H ∈ 𝓗, kSub A H with hU
  refine Nat.card_le_card_of_injective
    (fun u : U => (QuotientGroup.mk (u : W) : W ⧸ fixV (zpowers a))) ?_
  intro u v huv
  have h1 : (u : W)⁻¹ * v ∈ fixV (zpowers a) := QuotientGroup.eq.1 huv
  have h2 : (u : W)⁻¹ * v ∈ U ⊓ fixV (zpowers a) := ⟨U.mul_mem (U.inv_mem u.2) v.2, h1⟩
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact Subtype.ext h2

theorem card_kSub_modEq (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A H : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hH : H ≤ A) (hHA : H.relIndex A = p) :
    Nat.card (kSub A H) ≡ 1 [MOD p] := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, haA, haH⟩ : ∃ a ∈ A, a ∉ H := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have : H = A := le_antisymm hH hcon
    rw [this, relIndex_self] at hHA
    exact hp.one_lt.ne hHA
  set K := kSub A H with hK
  have haK : ∀ w ∈ K, a w ∈ K := by
    intro w hw
    obtain ⟨hwH, hwA⟩ := mem_kSub.1 hw
    refine mem_kSub.2 ⟨?_, ?_⟩
    · rw [mem_fixV]
      intro h hh
      have hc : h * a = a * h := comm_of_mem hA (hH hh) haA
      have := congrArg (fun g : MulAut W => g w) hc
      simp only [MulAut.mul_apply] at this
      rw [this, mem_fixV.1 hwH h hh]
    · rw [normHom_apply_of_mem_normalizer (le_normalizer haA), hwA, map_one]
  let σ : Function.End K := fun w => ⟨a w, haK w w.2⟩
  have hσpow : ∀ (n : ℕ) (w : K), ((σ ^ n) w : W) = (a ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ]
      exact ih (σ w)
  have hσ : σ ^ p ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    rw [pow_one, hσpow, hA.2 a haA]
    rfl
  haveI : Fintype K := Fintype.ofFinite K
  have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) hσ
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at h
  have haodd : Odd (Nat.card (zpowers a)) :=
    odd_card_of_pow_eq_one hp hp2 fun x hx => hA.2 x (zpowers_le.2 haA hx)
  have hfix : Nat.card (Function.fixedPoints σ) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨⟨1, Subtype.ext (map_one a)⟩⟩⟩
    have hone : ∀ z : Function.fixedPoints σ, ((z : K) : W) = 1 := by
      rintro ⟨z, hz⟩
      have hza : a z = z := congrArg Subtype.val hz
      obtain ⟨hzH, hzA⟩ := mem_kSub.1 z.2
      have hza' : (z : W) ∈ fixV (zpowers a) := mem_fixV_zpowers_of hza
      rw [normHom_eq_normHom_zpowers hW hp hp2 hA hH hHA haA haH hzH,
        normHom_of_mem_fixV _ hza', pow_odd_eq_self hW haodd] at hzA
      exact hzA
    exact Subtype.ext (Subtype.ext ((hone x).trans (hone y).symm))
  rw [hfix] at h
  exact h

theorem card_kSub_ge (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A H : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hH : H ∈ deltaSet p A) :
    8 ≤ Nat.card (kSub A H) ∧ (p ≠ 7 → 16 ≤ Nat.card (kSub A H)) := by
  obtain ⟨hHA, hHp, hne⟩ := hH
  have hp2 : p ≠ 2 := by omega
  have hmod := card_kSub_modEq hW hp hp2 hA hHA hHp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (kSub A H) := fun w =>
    ⟨1, Subtype.ext (by simpa [sq] using hW (w : W))⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 h2
  rw [he] at hmod ⊢
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.1 (by rw [he, pow_zero]))
  have hdvd : p ∣ 2 ^ e - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 hmod.symm
  have he3 : 3 ≤ e := by
    by_contra h
    have he' : e = 1 ∨ e = 2 := by omega
    rcases he' with rfl | rfl
    · have := Nat.le_of_dvd (by norm_num) hdvd
      norm_num at this
      omega
    · have := Nat.le_of_dvd (by norm_num) hdvd
      norm_num at this
      omega
  refine ⟨?_, fun h7 => ?_⟩
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he3
  · have he4 : 4 ≤ e := by
      by_contra h
      have : e = 3 := by omega
      subst this
      have h7' : p ∣ 7 := by simpa using hdvd
      exact h7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7')
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he4

private theorem iSup_fixV_hyperplanes (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hA1 : A ≠ ⊥) (w : W) :
    w ∈ ⨆ (H : Subgroup (MulAut W)) (_ : H ≤ A ∧ H.relIndex A = p), fixV H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hA1
  have : CFSG.IsElementaryAbelian p A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hA.2 x x.2) }
  let _ : MulDistribMulAction A W := MulDistribMulAction.compHom W A.subtype
  have hpW : ¬ p ∣ Nat.card W := by
    have h2 : IsPGroup 2 W := fun g => ⟨1, by rw [pow_one, sq]; exact hW g⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 h2
    rw [hm]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hgen := CFSG.SolvableHall.abelian_hyperplane_generation (p := p) (A := A) (H := W) hpW
  have hle : ⨆ (B : Subgroup A) (_ : B.index = p), fixedPointSubgroup B W ≤
      ⨆ (H : Subgroup (MulAut W)) (_ : H ≤ A ∧ H.relIndex A = p), fixV H := by
    refine iSup₂_le fun B hB => ?_
    have hDA : B.map A.subtype ≤ A := Subgroup.map_subtype_le B
    have hDrel : (B.map A.subtype).relIndex A = p := by
      have h : (B.map A.subtype).subgroupOf A = B :=
        Subgroup.comap_map_eq_self_of_injective A.subtype_injective B
      rw [Subgroup.relIndex, h]
      exact hB
    refine le_trans ?_ (le_iSup₂ (f := fun (H : Subgroup (MulAut W))
      (_ : H ≤ A ∧ H.relIndex A = p) => fixV H) (B.map A.subtype) ⟨hDA, hDrel⟩)
    intro v hv
    rw [mem_fixV]
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
    exact hv ⟨b, hb⟩
  exact hle (hgen ▸ Subgroup.mem_top w)

theorem deltaSet_nonempty (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut W)} (hA : IsElemAbelian p A) (hA1 : A ≠ ⊥) :
    (deltaSet p A).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hK : ∀ H, H ≤ A → H.relIndex A = p → kSub A H = ⊥ := by
    intro H hHA hHp
    by_contra hne
    have hmem : H ∈ deltaSet p A := ⟨hHA, hHp, hne⟩
    rw [hcon] at hmem
    exact hmem
  have hAodd : Odd (Nat.card A) := odd_card_of_pow_eq_one hp hp2 hA.2
  have hle : ∀ H, H ≤ A → H.relIndex A = p → fixV H ≤ fixV A := by
    intro H hHA hHp w hw
    have hvA : normHom A w ∈ fixV A := normHom_mem_fixV A w
    have hvH : normHom A w ∈ fixV H := fun h hh => hvA h (hHA hh)
    have hmem : w * (normHom A w)⁻¹ ∈ kSub A H := by
      refine mem_kSub.2 ⟨(fixV H).mul_mem hw ((fixV H).inv_mem hvH), ?_⟩
      rw [map_mul, map_inv, normHom_of_mem_fixV A hvA, pow_odd_eq_self hW hAodd, mul_inv_cancel]
    rw [hK H hHA hHp, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    rw [hmem]
    exact hvA
  apply hA1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  ext w
  have hw : w ∈ fixV A :=
    (iSup₂_le fun H hH => hle H hH.1 hH.2) (iSup_fixV_hyperplanes hW hp hp2 hA hA1 w)
  exact hw a ha

theorem map_conj_mem_deltaSet {p : ℕ} {A : Subgroup (MulAut W)} {s : MulAut W}
    (hs : s ∈ normalizer (A : Set (MulAut W))) {H : Subgroup (MulAut W)}
    (hH : H ∈ deltaSet p A) : H.map (MulAut.conj s).toMonoidHom ∈ deltaSet p A := by
  obtain ⟨hHA, hHp, hne⟩ := hH
  have hAs : A.map (MulAut.conj s).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.1 hs
  refine ⟨?_, ?_, ?_⟩
  · rw [← hAs]
    exact Subgroup.map_mono hHA
  · rw [← hAs, relIndex_map_map_of_injective _ _ (MulAut.conj s).injective]
    exact hHp
  · intro hbot
    apply hne
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwH, hwA⟩ := mem_kSub.1 hw
    have hsw : s w ∈ kSub A (H.map (MulAut.conj s).toMonoidHom) := by
      refine mem_kSub.2 ⟨?_, ?_⟩
      · rw [mem_fixV]
        rintro _ ⟨h, hh, rfl⟩
        show (s * h * s⁻¹) (s w) = s w
        simp only [MulAut.mul_apply, MulAut.inv_apply_self]
        rw [mem_fixV.1 hwH h hh]
      · rw [normHom_apply_of_mem_normalizer hs, hwA, map_one]
    rw [hbot, Subgroup.mem_bot] at hsw
    rw [Subgroup.mem_bot]
    exact (map_eq_one_iff s s.injective).1 hsw

end TwelveNineteen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
