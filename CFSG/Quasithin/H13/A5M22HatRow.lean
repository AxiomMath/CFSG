module

public import CFSG.Quasithin.H13.A5M22HatCent
public import CFSG.Quasithin.H13.A5M22HatAut
public import CFSG.Quasithin.H13.A5Facts1321
public import CFSG.Quasithin.Background.HConj

public section

namespace CFSG.Quasithin.H13.A5.M22Hat

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
open scoped Matrix commutatorElement

section Quasi

variable {Q : Type*} [Group Q]

theorem eq_top_of_not_le_center (hperf : commutator Q = ⊤)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) [N.Normal]
    (hN : ¬ N ≤ Subgroup.center Q) : N = ⊤ := by
  have hmap : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Q)))
    with h | h
  · refine absurd (fun n hn => ?_) hN
    have h1 : QuotientGroup.mk' (Subgroup.center Q) n = 1 := by
      have : QuotientGroup.mk' (Subgroup.center Q) n ∈ N.map (QuotientGroup.mk' _) :=
        ⟨n, hn, rfl⟩
      rw [h] at this
      exact this
    exact (QuotientGroup.eq_one_iff n).mp h1
  ·
    have hdec : ∀ a : Q, ∃ c ∈ Subgroup.center Q,
        (QuotientGroup.mk a : Q ⧸ N) = QuotientGroup.mk c := by
      intro a
      have : QuotientGroup.mk' (Subgroup.center Q) a ∈ N.map (QuotientGroup.mk' _) := by
        rw [h]
        trivial
      obtain ⟨n, hn, hna⟩ := this
      refine ⟨n⁻¹ * a, QuotientGroup.eq.mp hna, ?_⟩
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n⁻¹).mpr (N.inv_mem hn), one_mul]
    rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨c, hc, hac⟩ := hdec a
    obtain ⟨d, -, hbd⟩ := hdec b
    have hcd : ⁅c, d⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hc d).symm
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' N ⁅a, b⁆ = 1
    rw [map_commutatorElement]
    change ⁅(QuotientGroup.mk a : Q ⧸ N), (QuotientGroup.mk b : Q ⧸ N)⁆ = 1
    rw [hac, hbd]
    change ⁅QuotientGroup.mk' N c, QuotientGroup.mk' N d⁆ = 1
    rw [← map_commutatorElement, hcd, map_one]

theorem eq_of_mk_eq (hperf : commutator Q = ⊤) (α : MulAut Q)
    (h : ∀ γ : Q, (QuotientGroup.mk (α γ) : Q ⧸ Subgroup.center Q) = QuotientGroup.mk γ)
    (γ : Q) : α γ = γ := by
  have hc : ∀ γ : Q, α γ * γ⁻¹ ∈ Subgroup.center Q := fun γ => by
    have h1 : γ⁻¹ * α γ ∈ Subgroup.center Q := QuotientGroup.eq.mp (h γ).symm
    have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 γ
    convert h2 using 1
    group
  let c : Q →* ↥(Subgroup.center Q) :=
    { toFun := fun γ => ⟨α γ * γ⁻¹, hc γ⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun γ δ => Subtype.ext (by
        change α (γ * δ) * (γ * δ)⁻¹ = α γ * γ⁻¹ * (α δ * δ⁻¹)
        have hz := Subgroup.mem_center_iff.mp (hc δ) γ⁻¹
        rw [map_mul, mul_inv_rev]
        calc α γ * α δ * (δ⁻¹ * γ⁻¹) = α γ * ((α δ * δ⁻¹) * γ⁻¹) := by group
          _ = α γ * (γ⁻¹ * (α δ * δ⁻¹)) := by rw [hz]
          _ = α γ * γ⁻¹ * (α δ * δ⁻¹) := by group) }
  have hker := Abelianization.commutator_subset_ker c
  rw [hperf] at hker
  have h1 : c γ = 1 := hker (Subgroup.mem_top γ)
  have h2 : α γ * γ⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.mp h2

end Quasi

section Tools

variable {W : Type*} [CommGroup W] [Finite W]

theorem index_two_pow (hW : ∀ w : W, w ^ 2 = 1) (H : Subgroup W) : ∃ k, H.index = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp (show IsPGroup 2 W from
    fun w => ⟨1, by rw [pow_one]; exact hW w⟩)
  have hdvd : H.index ∣ 2 ^ N := by
    rw [← hN]
    exact H.index_dvd_card
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, hk⟩

omit [Finite W] in
theorem rkIdx_of_index {H : Subgroup W} {k : ℕ} (h : H.index = 2 ^ k) : rkIdx H = k := by
  rw [rkIdx, h, padicValNat.prime_pow]

theorem rkIdx_inf_le (hW : ∀ w : W, w ^ 2 = 1) (A B : Subgroup W) :
    rkIdx (A ⊓ B) ≤ rkIdx A + rkIdx B := by
  obtain ⟨a, ha⟩ := index_two_pow hW A
  obtain ⟨b, hb⟩ := index_two_pow hW B
  obtain ⟨c, hc⟩ := index_two_pow hW (A ⊓ B)
  have h := Subgroup.index_inf_le (H := A) (K := B)
  rw [ha, hb, hc, ← pow_add] at h
  rw [rkIdx_of_index ha, rkIdx_of_index hb, rkIdx_of_index hc]
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem rkIdx_le_of_le (hW : ∀ w : W, w ^ 2 = 1) {A B : Subgroup W} (hAB : A ≤ B) :
    rkIdx B ≤ rkIdx A := by
  obtain ⟨a, ha⟩ := index_two_pow hW A
  obtain ⟨b, hb⟩ := index_two_pow hW B
  have h := Subgroup.index_dvd_of_le hAB
  rw [ha, hb] at h
  rw [rkIdx_of_index ha, rkIdx_of_index hb]
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h

omit [Finite W] in
theorem fixV_zpowers_le_mul (a b : MulAut W) :
    fixV (Subgroup.zpowers a) ⊓ fixV (Subgroup.zpowers b) ≤ fixV (Subgroup.zpowers (a * b)) :=
  fun w hw => H.Mathieu.mem_fixV_zpowers_iff.mpr (by
    rw [MulAut.mul_apply, H.Mathieu.mem_fixV_zpowers_iff.mp hw.2,
      H.Mathieu.mem_fixV_zpowers_iff.mp hw.1])

omit [Finite W] in
theorem rkIdx_fixV_conj (g a : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers (g * a * g⁻¹))) = rkIdx (fixV (Subgroup.zpowers a)) := by
  have h : fixV (Subgroup.zpowers (g * a * g⁻¹)) =
      (fixV (Subgroup.zpowers a)).comap (g⁻¹ : MulAut W).toMonoidHom := by
    ext w
    rw [Subgroup.mem_comap, H.Mathieu.mem_fixV_zpowers_iff, H.Mathieu.mem_fixV_zpowers_iff,
      MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.mul_apply]
    constructor
    · intro h1
      have := congrArg (fun x => (g⁻¹ : MulAut W) x) h1
      simpa only [MulAut.inv_apply_self] using this
    · intro h1
      rw [h1, MulAut.apply_inv_self]
  rw [h, rkIdx, rkIdx,
    Subgroup.index_comap_of_surjective _ (g⁻¹ : MulAut W).surjective]

omit [Finite W] in
theorem rkIdx_fixV_inv (a : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers a⁻¹)) = rkIdx (fixV (Subgroup.zpowers a)) := by
  rw [Subgroup.zpowers_inv]

theorem ten_le_rkIdx (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 12) {y : MulAut W}
    (hy : 11 ∣ orderOf y) : 10 ≤ rkIdx (fixV (Subgroup.zpowers y)) := by
  obtain ⟨k, hk⟩ := hy
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact (orderOf_pos y).ne' hk
  set g := y ^ k with hg
  have hg11 : orderOf g = 11 := by
    rw [hg, orderOf_pow_of_dvd hk0 ⟨11, by rw [hk, mul_comm]⟩, hk,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
  have hle : fixV (Subgroup.zpowers y) ≤ fixV (Subgroup.zpowers g) := fun w hw x hx =>
    hw x (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _) hx)
  refine le_trans ?_ (rkIdx_le_of_le hW hle)
  have hmod := card_modEq_fix (MulAut.toPerm W g) (by
    rw [← map_pow, ← hg11, pow_orderOf_eq_one, map_one])
  have hF : Nat.card {x // MulAut.toPerm W g x = x} = Nat.card (fixV (Subgroup.zpowers g)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => H.Mathieu.mem_fixV_zpowers_iff.symm)
  rw [hF, hcard] at hmod
  obtain ⟨c, hc⟩ : ∃ c, Nat.card (fixV (Subgroup.zpowers g)) = 2 ^ c := by
    have hdvd : Nat.card (fixV (Subgroup.zpowers g)) ∣ 2 ^ 12 :=
      hcard ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨c, hc⟩
  have hc12 : c ≤ 12 := by
    have h := Subgroup.card_le_card_group (fixV (Subgroup.zpowers g))
    rw [hc, hcard] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  rw [hc] at hmod
  have key : ∀ c ≤ 12, 2 ^ 12 % 11 = 2 ^ c % 11 → c = 2 ∨ c = 12 := by decide
  have hidx := (fixV (Subgroup.zpowers g)).card_mul_index
  rw [hc, hcard] at hidx
  rcases key c hc12 hmod with rfl | rfl
  · have h10 : (fixV (Subgroup.zpowers g)).index = 2 ^ 10 := by
      have : (2 : ℕ) ^ 12 = 2 ^ 2 * 2 ^ 10 := by norm_num
      rw [this] at hidx
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) hidx
    rw [rkIdx_of_index h10]
  · exfalso
    have h1 : (fixV (Subgroup.zpowers g)).index = 1 := by
      have : (2 : ℕ) ^ 12 = 2 ^ 12 * 1 := by norm_num
      rw [this] at hidx
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) hidx
    have htop := Subgroup.index_eq_one.mp h1
    have hg1 : g = 1 := MulEquiv.ext fun w => by
      have : w ∈ fixV (Subgroup.zpowers g) := by rw [htop]; trivial
      exact H.Mathieu.mem_fixV_zpowers_iff.mp this
    rw [hg1, orderOf_one] at hg11
    omega

theorem rkIdx_fixV_mul_le (hW : ∀ w : W, w ^ 2 = 1) (a b : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers (a * b))) ≤
      rkIdx (fixV (Subgroup.zpowers a)) + rkIdx (fixV (Subgroup.zpowers b)) :=
  le_trans (rkIdx_le_of_le hW (fixV_zpowers_le_mul a b)) (rkIdx_inf_le hW _ _)

end Tools

section Main

variable {K : Type} [Field K] [Finite K] {Γ₀ : Subgroup (GL (Fin 6) K)}

theorem sq_eq_one_stdMod (hK : Nat.card K = 4) (w : StdMod (Fin 6) K) : w ^ 2 = 1 := by
  have h2 := two_eq_zero_of_card hK
  rw [sq]
  apply Multiplicative.toAdd.injective
  funext i
  change Multiplicative.toAdd w i + Multiplicative.toAdd w i = 0
  rw [← two_mul, h2, zero_mul]

omit [Field K] in
theorem card_stdMod_six (hK : Nat.card K = 4) : Nat.card (StdMod (Fin 6) K) = 2 ^ 12 := by
  rw [card_stdMod, hK, Fintype.card_fin]
  norm_num

theorem eq_one_of_commute (hK : Nat.card K = 4) (hperf : commutator ↥Γ₀ = ⊤)
    (hs : IsSimpleGroup (↥Γ₀ ⧸ Subgroup.center ↥Γ₀))
    (hZ3 : Nat.card (Subgroup.center ↥Γ₀) = 3) {z : ↥Γ₀} (hz : z ∈ Subgroup.center ↥Γ₀)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {g : ↥Γ₀} (hg : orderOf g = 11)
    {v : MulAut (StdMod (Fin 6) K)} (hv : ∀ γ : ↥Γ₀, v * natAut Γ₀ γ = natAut Γ₀ γ * v)
    (hrk : rkIdx (fixV (Subgroup.zpowers v)) ≤ 2) : v = 1 := by
  let δ : StdMod (Fin 6) K →* StdMod (Fin 6) K :=
    { toFun := fun w => v w * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have hker : δ.ker = fixV (Subgroup.zpowers v) := by
    ext w
    rw [MonoidHom.mem_ker, H.Mathieu.mem_fixV_zpowers_iff]
    exact mul_inv_eq_one
  have hcardU : Nat.card δ.range ≤ 4 := by
    rw [← Subgroup.index_ker, hker]
    obtain ⟨k, hk⟩ := index_two_pow (sq_eq_one_stdMod hK) (fixV (Subgroup.zpowers v))
    rw [rkIdx_of_index hk] at hrk
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 4 := by norm_num
  have hcomm : ∀ (γ : ↥Γ₀) (w : StdMod (Fin 6) K), v (natAut Γ₀ γ w) = natAut Γ₀ γ (v w) :=
    fun γ w => congrArg (fun φ : MulAut (StdMod (Fin 6) K) => φ w) (hv γ)
  have hinv : ∀ (γ : ↥Γ₀), ∀ u ∈ δ.range, natAut Γ₀ γ u ∈ δ.range := by
    rintro γ _ ⟨w, rfl⟩
    refine ⟨natAut Γ₀ γ w, ?_⟩
    change v (natAut Γ₀ γ w) * (natAut Γ₀ γ w)⁻¹ = natAut Γ₀ γ (v w * w⁻¹)
    rw [map_mul, map_inv, hcomm]
  let N : Subgroup ↥Γ₀ :=
    { carrier := {γ | ∀ u ∈ δ.range, natAut Γ₀ γ u = u}
      mul_mem' := fun {a b} ha hb u hu => by
        rw [map_mul, MulAut.mul_apply, hb u hu, ha u hu]
      one_mem' := fun u _ => by rw [map_one, MulAut.one_apply]
      inv_mem' := fun {a} ha u hu => by
        have h1 := ha (natAut Γ₀ a⁻¹ u) (hinv _ u hu)
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h1
        exact h1.symm }
  have hN : N.Normal := ⟨fun n hn γ u hu => by
    change natAut Γ₀ (γ * n * γ⁻¹) u = u
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hn _ (hinv _ u hu),
      ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]⟩
  have hgN : g ∈ N := by
    intro u hu
    let σ : Equiv.Perm ↥δ.range :=
      { toFun := fun x => ⟨natAut Γ₀ g x, hinv g x x.2⟩
        invFun := fun x => ⟨natAut Γ₀ g⁻¹ x, hinv g⁻¹ x x.2⟩
        left_inv := fun x => Subtype.ext (by
          change natAut Γ₀ g⁻¹ (natAut Γ₀ g x) = x
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
        right_inv := fun x => Subtype.ext (by
          change natAut Γ₀ g (natAut Γ₀ g⁻¹ x) = x
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]) }
    have hpow : ∀ (k : ℕ) (x : ↥δ.range), (((σ ^ k) x : ↥δ.range) : StdMod (Fin 6) K) =
        natAut Γ₀ (g ^ k) x := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ih =>
        intro x
        rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', map_mul, MulAut.mul_apply, ← ih]
        rfl
    have hσ : σ ^ 11 = 1 := Equiv.ext fun x => Subtype.ext (by
      rw [hpow, ← hg, pow_orderOf_eq_one, map_one]
      rfl)
    have h1 : orderOf σ ∣ 11 := orderOf_dvd_of_pow_eq_one hσ
    have h2 : orderOf σ ∣ (Nat.card ↥δ.range).factorial := by
      rw [← Nat.card_perm]
      exact orderOf_dvd_natCard σ
    rcases (Nat.dvd_prime (by norm_num)).mp h1 with h | h
    · have := congrArg (fun τ : Equiv.Perm ↥δ.range => ((τ ⟨u, hu⟩ : ↥δ.range) :
        StdMod (Fin 6) K)) (orderOf_eq_one_iff.mp h)
      exact this
    · rw [h] at h2
      have := (Nat.Prime.dvd_factorial (by norm_num)).mp h2
      omega
  have hgZ : g ∉ Subgroup.center ↥Γ₀ := fun hgc => by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥Γ₀) hgc
    rw [hg, hZ3] at h
    omega
  have hNtop : N = ⊤ := eq_top_of_not_le_center hperf hs N fun h => hgZ (h hgN)
  have hzN : z ∈ N := by rw [hNtop]; trivial
  have hfix := fixV_natAut_eq_bot hK hperf hz hz3 hz1 hg
  refine MulEquiv.ext fun w => ?_
  have hu : δ w ∈ fixV (Subgroup.zpowers (natAut Γ₀ z)) :=
    H.Mathieu.mem_fixV_zpowers_iff.mpr (hzN _ ⟨w, rfl⟩)
  rw [hfix, Subgroup.mem_bot] at hu
  exact mul_inv_eq_one.mp hu

theorem three_le_rkIdx
    (hK : Nat.card K = 4) (hHat : IsHat ↥Γ₀ ↥CFSG.Open.quasithinM22)
    {v : MulAut (StdMod (Fin 6) K)} (hv : v ∈ natNorm Γ₀) (hv2 : orderOf v = 2) :
    3 ≤ rkIdx (fixV (Subgroup.zpowers v)) := by
  obtain ⟨⟨hperf', hs, -⟩, hZ3, ⟨e⟩⟩ := hHat
  have hperf : commutator ↥Γ₀ = ⊤ := hperf'.commutator_eq_top
  have hW := sq_eq_one_stdMod hK
  have : Nontrivial ↥(Subgroup.center ↥Γ₀) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥Γ₀))
  have hz3 : (z : ↥Γ₀) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥Γ₀)) (x := z)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hz1' : (z : ↥Γ₀) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hcard : Nat.card ↥Γ₀ = 3 * 443520 := by
    have h1 := (Subgroup.center ↥Γ₀).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr e.toEquiv, hZ3] at h1
    have h2 : Nat.card ↥CFSG.Open.quasithinM22 = 443520 := CFSG.Sporadic.Schreier.m22_card
    rw [h2] at h1
    omega
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 11 (by rw [hcard]; norm_num)
  by_contra hlt
  have hrk : rkIdx (fixV (Subgroup.zpowers v)) ≤ 2 := by omega
  set α := conjHom Γ₀ ⟨v, hv⟩ with hα
  have hαv : ∀ γ, natAut Γ₀ (α γ) = v * natAut Γ₀ γ * v⁻¹ := natAut_conjHom Γ₀ ⟨v, hv⟩
  have hvv : v * v = 1 := by rw [← sq, ← hv2, pow_orderOf_eq_one]
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hαα : ∀ γ, α (α γ) = γ := fun γ => natAut_injective Γ₀ (by
    rw [hαv, hαv, hvi]
    calc v * (v * natAut Γ₀ γ * v) * v = (v * v) * natAut Γ₀ γ * (v * v) := by group
      _ = natAut Γ₀ γ := by rw [hvv, one_mul, mul_one])
  let e' : ↥Γ₀ ⧸ Subgroup.center ↥Γ₀ ≃* ↥mog22 := e.trans mog22EquivM22.symm
  let π : ↥Γ₀ →* ↥mog22 := e'.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  by_cases htriv : ∀ γ, π (α γ) = π γ
  ·
    have hα1 : ∀ γ, α γ = γ := eq_of_mk_eq hperf α fun γ => e'.injective (htriv γ)
    have hcomm : ∀ γ, v * natAut Γ₀ γ = natAut Γ₀ γ * v := fun γ => by
      have h := hαv γ
      rw [hα1] at h
      calc v * natAut Γ₀ γ = v * natAut Γ₀ γ * v⁻¹ * v := by group
        _ = natAut Γ₀ γ * v := by rw [← h]
    have h1 := eq_one_of_commute hK hperf hs hZ3 z.2 hz3 hz1' hg hcomm hrk
    rw [h1, orderOf_one] at hv2
    omega
  · push Not at htriv
    obtain ⟨γ₀, hγ₀⟩ := htriv
    let β : MulAut ↥mog22 := e'.symm.trans ((QuotientGroup.congr (Subgroup.center ↥Γ₀)
      (Subgroup.center ↥Γ₀) α (Subgroup.map_center_eq α)).trans e')
    have hβ : ∀ γ, β (π γ) = π (α γ) := fun γ => by
      change e' (QuotientGroup.congr _ _ α _ (e'.symm (e' (QuotientGroup.mk γ)))) =
        e' (QuotientGroup.mk (α γ))
      rw [MulEquiv.symm_apply_apply, QuotientGroup.congr_mk]
    have hβ2 : β * β = 1 := MulEquiv.ext fun m => by
      obtain ⟨γ, rfl⟩ := hπ m
      rw [MulAut.mul_apply, hβ, hβ, hαα, MulAut.one_apply]
    have hβ1 : β ≠ 1 := fun h => hγ₀ (by rw [← hβ, h, MulAut.one_apply])
    obtain ⟨m₁, m₂, m₃, h11⟩ := exists_orderOf_eleven β hβ2 hβ1
    obtain ⟨γ₁, rfl⟩ := hπ m₁
    obtain ⟨γ₂, rfl⟩ := hπ m₂
    obtain ⟨γ₃, rfl⟩ := hπ m₃
    set y : ↥Γ₀ := α γ₁ * γ₁⁻¹ * (γ₂ * α (γ₂⁻¹ * γ₃) * γ₃⁻¹) with hy
    have hπy : π y = β (π γ₁) * (π γ₁)⁻¹ * (π γ₂ * β ((π γ₂)⁻¹ * π γ₃) * (π γ₃)⁻¹) := by
      rw [hy, ← map_inv π γ₂, ← map_mul π, hβ, hβ]
      simp only [map_mul, map_inv]
    have h11y : 11 ∣ orderOf (natAut Γ₀ y) := by
      rw [orderOf_injective _ (natAut_injective Γ₀)]
      exact h11 ▸ hπy ▸ orderOf_map_dvd π y
    have h10 := ten_le_rkIdx hW (card_stdMod_six hK) h11y
    have hY : natAut Γ₀ y = v * (natAut Γ₀ γ₁ * v⁻¹ * (natAut Γ₀ γ₁)⁻¹) *
        (natAut Γ₀ γ₂ * v * (natAut Γ₀ γ₂)⁻¹) * (natAut Γ₀ γ₃ * v⁻¹ * (natAut Γ₀ γ₃)⁻¹) := by
      rw [hy]
      simp only [map_mul, map_inv, hαv]
      group
    have h8 : rkIdx (fixV (Subgroup.zpowers (natAut Γ₀ y))) ≤ 8 := by
      rw [hY]
      have h1 := rkIdx_fixV_mul_le hW (v * (natAut Γ₀ γ₁ * v⁻¹ * (natAut Γ₀ γ₁)⁻¹) *
        (natAut Γ₀ γ₂ * v * (natAut Γ₀ γ₂)⁻¹)) (natAut Γ₀ γ₃ * v⁻¹ * (natAut Γ₀ γ₃)⁻¹)
      have h2 := rkIdx_fixV_mul_le hW (v * (natAut Γ₀ γ₁ * v⁻¹ * (natAut Γ₀ γ₁)⁻¹))
        (natAut Γ₀ γ₂ * v * (natAut Γ₀ γ₂)⁻¹)
      have h3 := rkIdx_fixV_mul_le hW v (natAut Γ₀ γ₁ * v⁻¹ * (natAut Γ₀ γ₁)⁻¹)
      rw [rkIdx_fixV_conj, rkIdx_fixV_inv] at h1 h3
      rw [rkIdx_fixV_conj] at h2
      omega
    omega

end Main

end CFSG.Quasithin.H13.A5.M22Hat

namespace CFSG.Quasithin.H13.A5

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13.A5.M22Hat

theorem factM22HatRow1321_holds :
    FactM22HatRow1321 := by
  intro V _ _ G L hLG hGN hM v hvG hv2
  obtain ⟨K, _, _, Γ₀, hK, hHat, -, hReal⟩ := hM
  obtain ⟨e, -, hXN⟩ := exists_transport_natural hReal hLG hGN
  have hvN : congrHom e v ∈ natNorm Γ₀ := hXN ⟨v, hvG, rfl⟩
  have hv2' : orderOf (congrHom e v) = 2 :=
    (orderOf_injective _ (congrHom_injective e) v).trans hv2
  have h3 := three_le_rkIdx hK hHat hvN hv2'
  have hV : rkIdx (fixV (Subgroup.zpowers (congrHom e v))) =
      rkIdx (fixV (Subgroup.zpowers v)) :=
    calc rkIdx (fixV (Subgroup.zpowers (congrHom e v)))
        = rkIdx (fixV ((Subgroup.zpowers v).map (congrHom e))) := by
          rw [MonoidHom.map_zpowers]
      _ = rkIdx (fixV (Subgroup.zpowers v)) := rkIdx_fixV_map_congrHom e _
  omega

end CFSG.Quasithin.H13.A5
