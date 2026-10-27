module

public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

open scoped commutatorElement Pointwise

namespace CFSG.Quasithin.SteinbergCD

open CFSG Subgroup

variable {X : Type*} [Group X]

theorem le_normalizer_of_forall_conj_mem {H K : Subgroup X}
    (h : ∀ k ∈ K, ∀ x ∈ H, k * x * k⁻¹ ∈ H) : K ≤ normalizer (H : Set X) := by
  intro k hk
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h k hk x, fun hx => ?_⟩
  have h1 := h k⁻¹ (K.inv_mem hk) _ hx
  have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem commutatorElement_mem_inf_of_le_normalizer {W Q : Subgroup X} (hQn : Q.Normal)
    (hQW : Q ≤ normalizer (W : Set X)) {w q : X} (hw : w ∈ W) (hq : q ∈ Q) :
    ⁅w, q⁆ ∈ W ⊓ Q := by
  rw [commutatorElement_def]
  refine ⟨?_, Q.mul_mem (hQn.conj_mem q hq w) (Q.inv_mem hq)⟩
  have h1 : q * w⁻¹ * q⁻¹ ∈ W := (mem_normalizer_iff.mp (hQW hq) w⁻¹).mp (W.inv_mem hw)
  have e : w * q * w⁻¹ * q⁻¹ = w * (q * w⁻¹ * q⁻¹) := by group
  rw [e]
  exact W.mul_mem hw h1

theorem exists_subgroup_forall_commutatorElement_mem {N : Subgroup X} (hN : N.Normal)
    (Y : Set X) : ∃ K : Subgroup X, ∀ x, x ∈ K ↔ ∀ y ∈ Y, ⁅x, y⁆ ∈ N := by
  refine ⟨{ carrier := {x | ∀ y ∈ Y, ⁅x, y⁆ ∈ N}
            one_mem' := fun y _ => by rw [commutatorElement_one_left]; exact N.one_mem
            mul_mem' := fun {a b} ha hb y hy => ?_
            inv_mem' := fun {a} ha y hy => ?_ }, fun x => Iff.rfl⟩
  · have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (hN.conj_mem _ (hb y hy) a) (ha y hy)
  · have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hN.conj_mem _ (N.inv_mem (ha y hy)) a⁻¹

theorem commute_of_odd_of_stabilizes {P Q : Subgroup X} (hP : IsPGroup 2 P) {k : X} {m : ℕ}
    (hm : Odd m) (hkm : k ^ m = 1) (hkP : k ∈ centralizer (P : Set X))
    (hkQ : ∀ q ∈ Q, q⁻¹ * (k * q * k⁻¹) ∈ P) {q : X} (hq : q ∈ Q) : k * q * k⁻¹ = q := by
  set p := q⁻¹ * (k * q * k⁻¹) with hp
  have hpP : p ∈ P := hkQ q hq
  have hkp : Commute k p := (mem_centralizer_iff.mp hkP p hpP).symm
  have hqp : k * q * k⁻¹ = q * p := by rw [hp, mul_inv_cancel_left]
  have hiter : ∀ j : ℕ, k ^ j * q * (k ^ j)⁻¹ = q * p ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hkpj : k * p ^ j * k⁻¹ = p ^ j := by
        rw [(hkp.pow_right j).eq, mul_inv_cancel_right]
      calc k ^ (j + 1) * q * (k ^ (j + 1))⁻¹ = k * (k ^ j * q * (k ^ j)⁻¹) * k⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            simp only [mul_assoc]
        _ = (k * q * k⁻¹) * (k * p ^ j * k⁻¹) := by rw [ih]; group
        _ = q * p ^ (j + 1) := by rw [hqp, hkpj, pow_succ', mul_assoc]
  have hpm : p ^ m = 1 := by
    have h := hiter m
    rw [hkm, one_mul, inv_one, mul_one] at h
    exact (mul_eq_left.mp h.symm)
  obtain ⟨e, he⟩ := hP ⟨p, hpP⟩
  have he' : p ^ 2 ^ e = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  have hcop : (2 ^ e).Coprime m := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm)
  have hp1 : p = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨he', hpm⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  rw [hqp, hp1, mul_one]

theorem isPGroup_centralizer_of_commutator_le [Finite X] (hX : IsCharacteristicP 2 X)
    {P : Subgroup X} [hPn : P.Normal] (hP2 : IsPGroup 2 P)
    (hXQ : ⁅(⊤ : Subgroup X), pCore 2 X⁆ ≤ P) : IsPGroup 2 (centralizer (P : Set X)) := by
  have hQ2 : IsPGroup 2 (pCore 2 X) := pCore_isPGroup
  rintro ⟨k, hk⟩
  have hk0 : orderOf k ≠ 0 := (orderOf_pos k).ne'
  obtain ⟨a, m, hm, hkam⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  have hdvd : 2 ^ a ∣ orderOf k := ⟨m, hkam⟩
  have hord : orderOf (k ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a two_ne_zero) hdvd, hkam,
      Nat.mul_div_cancel_left m (pow_pos two_pos a)]
  have hkm : (k ^ 2 ^ a) ^ m = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hkP : k ^ 2 ^ a ∈ centralizer (P : Set X) := (centralizer (P : Set X)).pow_mem hk _
  have hkQ : ∀ q ∈ pCore 2 X, q⁻¹ * (k ^ 2 ^ a * q * (k ^ 2 ^ a)⁻¹) ∈ P := by
    intro q hq
    have hc : ⁅k ^ 2 ^ a, q⁆ ∈ P := hXQ (commutator_mem_commutator (mem_top _) hq)
    have e : q⁻¹ * (k ^ 2 ^ a * q * (k ^ 2 ^ a)⁻¹) = q⁻¹ * ⁅k ^ 2 ^ a, q⁆ * q⁻¹⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact hPn.conj_mem _ hc q⁻¹
  have hcent : k ^ 2 ^ a ∈ centralizer (pCore 2 X : Set X) := by
    rw [mem_centralizer_iff]
    intro q hq
    have h := commute_of_odd_of_stabilizes hP2 hm hkm hkP hkQ hq
    calc q * k ^ 2 ^ a = k ^ 2 ^ a * q * (k ^ 2 ^ a)⁻¹ * k ^ 2 ^ a := by rw [h]
      _ = k ^ 2 ^ a * q := by group
  obtain ⟨b, hb⟩ := hQ2 ⟨_, hX hcent⟩
  have hb' : (k ^ 2 ^ a) ^ 2 ^ b = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  have hcop : (2 ^ b).Coprime m := Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr hm)
  have h1 : k ^ 2 ^ a = 1 := by
    have h := pow_gcd_eq_one.mpr ⟨hb', hkm⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  exact ⟨a, Subtype.ext (by simpa using h1)⟩

end SteinbergCD

open Subgroup SteinbergCD

theorem conjugate_elementary_pair_order_two_core_image_cubic_bound {X : Type*} [Group X]
    [Finite X] (hX : IsCharacteristicP 2 X) {Q S V A B Z P : Subgroup X} {g : X}
    (hQ : Q = pCore 2 X) (hS : IsPGroup 2 S) (hSodd : ¬ 2 ∣ S.index) (_hVS : V ≤ S)
    (hSV : S ≤ normalizer (V : Set X)) [hVe : IsElementaryAbelian 2 V]
    (hgen : V ⊔ conjugate V g = ⊤) (hVQ : Q.relIndex V = 2) (hB : B = V ⊓ Q)
    (hA : A = conjugate V g ⊓ Q) (hZ : Z = V ⊓ conjugate V g) (hP : P = A ⊔ B) :
    Z ≤ center X ∧
    ((P : Set X) = (B : Set X) * (A : Set X) ∧ P.Normal ∧ P ≤ Q) ∧
    (Z ≤ B ∧ Z ≤ A ∧ B ⊓ A = Z ∧ ⁅P, P⁆ ≤ Z ∧ ∀ x ∈ P, x ^ 2 ∈ Z) ∧
    ⁅(⊤ : Subgroup X), Q⁆ ≤ P ∧
    (A ≤ Q ∧ Q ≤ S ∧ A ≤ normalizer (V : Set X)) ∧
    A ⊓ centralizer (V : Set X) = Z ∧ ⁅V, A⁆ ≠ ⊥ ∧ ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧
    IsElementaryAbelian 2 A ∧
    ∃ d r : ℕ, (centralizer (A : Set X)).relIndex V = 2 ^ d ∧
      (centralizer (V : Set X)).relIndex A = 2 ^ r ∧ 0 < d ∧ d ≤ 2 * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : Q.Normal := hQ ▸ pCore_normal
  have hQ2 : IsPGroup 2 Q := hQ ▸ pCore_isPGroup
  have hmem' : ∀ x, x ∈ conjugate V g ↔ g * x * g⁻¹ ∈ V := fun x => by
    rw [conjugate, mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have : IsElementaryAbelian 2 (conjugate V g) := IsElementaryAbelian.map _
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hV'c : ∀ a ∈ conjugate V g, ∀ b ∈ conjugate V g, a * b = b * a := fun a ha b hb =>
    setLike_mul_comm ha hb
  have hV2 : ∀ a ∈ V, a ^ 2 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hV'2 : ∀ a ∈ conjugate V g, a ^ 2 = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian a ha
  have hV2P : IsPGroup 2 V := IsElementaryAbelian.isPGroup 2 V
  have hcen : ∀ d : X, (∀ v ∈ V, v * d = d * v) → (∀ v ∈ conjugate V g, v * d = d * v) →
      d ∈ center X := by
    intro d h1 h2
    have hle : V ⊔ conjugate V g ≤ centralizer ({d} : Set X) :=
      sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (h1 v hv))
        (fun v hv => mem_centralizer_singleton_iff.mpr (h2 v hv))
    rw [mem_center_iff]
    intro x
    exact mem_centralizer_singleton_iff.mp (hle (hgen ▸ mem_top x))
  have hZc : Z ≤ center X := by
    intro z hz
    rw [hZ] at hz
    exact hcen z (fun v hv => hVc v hv z hz.1) (fun v hv => hV'c v hv z hz.2)
  have hZn : Z.Normal := ⟨fun z hz x => by
    have h := mem_center_iff.mp (hZc hz) x
    rwa [h, mul_inv_cancel_right]⟩
  have hZQ : Z ≤ Q := by
    rw [hQ]
    exact le_sSup ⟨hZn, hV2P.to_le (hZ ▸ inf_le_left)⟩
  have hQS : Q ≤ S := by
    have := hQn
    exact IsPGroup.le_sylow_of_normal hQ2 (hS.toSylow hSodd)
  have hQV : Q ≤ normalizer (V : Set X) := hQS.trans hSV
  have hQV' : Q ≤ normalizer (conjugate V g : Set X) := by
    refine le_normalizer_of_forall_conj_mem fun q hq x hx => ?_
    rw [hmem'] at hx ⊢
    have hgq : g * q * g⁻¹ ∈ Q := hQn.conj_mem q hq g
    have h := (mem_normalizer_iff.mp (hQV hgq) _).mp hx
    have e : g * (q * x * q⁻¹) * g⁻¹ =
        g * q * g⁻¹ * (g * x * g⁻¹) * (g * q * g⁻¹)⁻¹ := by group
    rw [e]
    exact h
  have hcomV : ∀ v ∈ V, ∀ q ∈ Q, ⁅v, q⁆ ∈ B := fun v hv q hq => by
    rw [hB]
    exact commutatorElement_mem_inf_of_le_normalizer hQn hQV hv hq
  have hcomV' : ∀ v ∈ conjugate V g, ∀ q ∈ Q, ⁅v, q⁆ ∈ A := fun v hv q hq => by
    rw [hA]
    exact commutatorElement_mem_inf_of_le_normalizer hQn hQV' hv hq
  have hBV : B ≤ V := hB ▸ inf_le_left
  have hBQ : B ≤ Q := hB ▸ inf_le_right
  have hAV' : A ≤ conjugate V g := hA ▸ inf_le_left
  have hAQ : A ≤ Q := hA ▸ inf_le_right
  have hAP : A ≤ P := hP ▸ le_sup_left
  have hBP : B ≤ P := hP ▸ le_sup_right
  have hZB : Z ≤ B := by
    rw [hB]
    exact le_inf (hZ ▸ inf_le_left) hZQ
  have hZA : Z ≤ A := by
    rw [hA]
    exact le_inf (hZ ▸ inf_le_right) hZQ
  have hBA : B ⊓ A = Z := by
    refine le_antisymm (fun x hx => ?_) (le_inf hZB hZA)
    rw [hZ]
    exact ⟨hBV hx.1, hAV' hx.2⟩
  have hcomAB : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ A := hcomV' a (hAV' ha) b (hBQ hb)
    have h2 : ⁅b, a⁆ ∈ B := hcomV b (hBV hb) a (hAQ ha)
    rw [← hBA]
    refine ⟨?_, h1⟩
    rw [← commutatorElement_inv]
    exact B.inv_mem h2
  have hAnB : A ≤ normalizer (B : Set X) := by
    refine hAQ.trans (le_normalizer_of_forall_conj_mem fun q hq x hx => ?_)
    rw [hB] at hx ⊢
    exact ⟨(mem_normalizer_iff.mp (hQV hq) x).mp hx.1, hQn.conj_mem x hx.2 q⟩
  have hPBA : (P : Set X) = (B : Set X) * (A : Set X) := by
    rw [hP, sup_comm]
    exact coe_mul_of_right_le_normalizer_left B A hAnB
  have hPQ : P ≤ Q := hP ▸ sup_le hAQ hBQ
  have hmemP : ∀ x ∈ P, ∃ b ∈ B, ∃ a ∈ A, b * a = x := fun x hx => by
    have hx' : x ∈ (P : Set X) := hx
    rw [hPBA] at hx'
    exact Set.mem_mul.mp hx'
  have hPnorm : ∀ x : X, (∀ a ∈ A, x * a * x⁻¹ ∈ P) → (∀ b ∈ B, x * b * x⁻¹ ∈ P) →
      ∀ y ∈ P, x * y * x⁻¹ ∈ P := by
    intro x hxA hxB y hy
    obtain ⟨b, hb, a, ha, rfl⟩ := hmemP y hy
    have e : x * (b * a) * x⁻¹ = x * b * x⁻¹ * (x * a * x⁻¹) := by group
    rw [e]
    exact P.mul_mem (hxB b hb) (hxA a ha)
  have hVnP : V ≤ normalizer (P : Set X) := by
    refine le_normalizer_of_forall_conj_mem fun v hv => hPnorm v (fun a ha => ?_) (fun b hb => ?_)
    · have e : v * a * v⁻¹ = ⁅v, a⁆ * a := by rw [commutatorElement_def]; group
      rw [e]
      exact P.mul_mem (hBP (hcomV v hv a (hAQ ha))) (hAP ha)
    · have e : v * b * v⁻¹ = b := by rw [hVc v hv b (hBV hb), mul_inv_cancel_right]
      rw [e]
      exact hBP hb
  have hV'nP : conjugate V g ≤ normalizer (P : Set X) := by
    refine le_normalizer_of_forall_conj_mem fun v hv => hPnorm v (fun a ha => ?_) (fun b hb => ?_)
    · have e : v * a * v⁻¹ = a := by rw [hV'c v hv a (hAV' ha), mul_inv_cancel_right]
      rw [e]
      exact hAP ha
    · have e : v * b * v⁻¹ = ⁅v, b⁆ * b := by rw [commutatorElement_def]; group
      rw [e]
      exact P.mul_mem (hAP (hcomV' v hv b (hBQ hb))) (hBP hb)
  have hPn : P.Normal := by
    rw [← normalizer_eq_top_iff, ← top_le_iff, ← hgen]
    exact sup_le hVnP hV'nP
  have hXQ : ⁅(⊤ : Subgroup X), Q⁆ ≤ P := by
    obtain ⟨K, hK⟩ := exists_subgroup_forall_commutatorElement_mem hPn (Q : Set X)
    have hVK : V ≤ K := fun v hv => (hK v).mpr fun q hq => hBP (hcomV v hv q hq)
    have hV'K : conjugate V g ≤ K := fun v hv => (hK v).mpr fun q hq => hAP (hcomV' v hv q hq)
    have htop : (⊤ : Subgroup X) ≤ K := hgen ▸ sup_le hVK hV'K
    rw [commutator_le]
    intro x _ q hq
    exact (hK x).mp (htop (mem_top x)) q hq
  have hPP : ⁅P, P⁆ ≤ Z := by
    obtain ⟨K, hK⟩ := exists_subgroup_forall_commutatorElement_mem hZn (P : Set X)
    have hcomm : ∀ c ∈ A ⊔ B, ∀ y ∈ P, ⁅c, y⁆ ∈ Z := by
      intro c hc
      have hgen' : ∀ c', (c' ∈ A ∨ c' ∈ B) → ∀ y ∈ P, ⁅c', y⁆ ∈ Z := by
        intro c' hc' y hy
        obtain ⟨K', hK'⟩ := exists_subgroup_forall_commutatorElement_mem hZn ({c'} : Set X)
        have hAK' : A ≤ K' := fun a ha => (hK' a).mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          subst hy
          rcases hc' with hc' | hc'
          · rw [commutatorElement_def, hV'c a (hAV' ha) _ (hAV' hc'), mul_inv_cancel_right,
              mul_inv_cancel]
            exact Z.one_mem
          · exact hcomAB a ha _ hc'
        have hBK' : B ≤ K' := fun b hb => (hK' b).mpr fun y hy => by
          rw [Set.mem_singleton_iff] at hy
          subst hy
          rcases hc' with hc' | hc'
          · rw [← commutatorElement_inv]
            exact Z.inv_mem (hcomAB _ hc' b hb)
          · rw [commutatorElement_def, hVc b (hBV hb) _ (hBV hc'), mul_inv_cancel_right,
              mul_inv_cancel]
            exact Z.one_mem
        have hPK' : P ≤ K' := hP ▸ sup_le hAK' hBK'
        rw [← commutatorElement_inv]
        exact Z.inv_mem ((hK' y).mp (hPK' hy) c' (Set.mem_singleton c'))
      have hAK : A ≤ K := fun a ha => (hK a).mpr (hgen' a (Or.inl ha))
      have hBK : B ≤ K := fun b hb => (hK b).mpr (hgen' b (Or.inr hb))
      exact (hK c).mp (sup_le hAK hBK hc)
    rw [commutator_le]
    intro x hx y hy
    exact hcomm x (hP ▸ hx) y hy
  have hsq : ∀ x ∈ P, x ^ 2 ∈ Z := by
    intro x hx
    obtain ⟨b, hb, a, ha, rfl⟩ := hmemP x hx
    have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV2 b (hBV hb))
    have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by
      rw [← pow_two]; exact hV'2 a (hAV' ha))
    have e : (b * a) ^ 2 = ⁅b, a⁆ := by
      rw [commutatorElement_def, hb1, ha1, pow_two]
      group
    rw [e, ← commutatorElement_inv]
    exact Z.inv_mem (hcomAB a ha b hb)
  have hCAV : A ⊓ centralizer (V : Set X) = Z := by
    refine le_antisymm (fun d hd => ?_) (le_inf hZA fun z hz => ?_)
    · obtain ⟨hdA, hdC⟩ := hd
      have hdc : d ∈ center X :=
        hcen d (fun v hv => mem_centralizer_iff.mp hdC v hv) (fun v hv => hV'c v hv d (hAV' hdA))
      have hgd : g * d * g⁻¹ = d := by
        rw [mem_center_iff.mp hdc g, mul_inv_cancel_right]
      rw [hZ]
      exact ⟨by rw [← hgd]; exact (hmem' d).mp (hAV' hdA), hAV' hdA⟩
    · rw [mem_centralizer_iff]
      intro v hv
      exact hVc v hv z (hZ ▸ hz).1
  have hVA : ⁅V, A⁆ ≠ ⊥ := by
    intro hbot
    have hVA' : V ≤ centralizer (A : Set X) := commutator_eq_bot_iff_le_centralizer.mp hbot
    have hPV : P ≤ centralizer (V : Set X) := by
      rw [hP]
      refine sup_le (le_centralizer_iff.mp hVA') fun b hb => ?_
      rw [mem_centralizer_iff]
      intro v hv
      exact hVc v hv b (hBV hb)
    have hVP : V ≤ centralizer (P : Set X) := le_centralizer_iff.mp hPV
    have hP2 : IsPGroup 2 P := hQ2.to_le hPQ
    have hK2 : IsPGroup 2 (centralizer (P : Set X)) := by
      have := hPn
      exact isPGroup_centralizer_of_commutator_le hX hP2 (hQ ▸ hXQ)
    have := hPn
    have hKQ : centralizer (P : Set X) ≤ Q := by
      rw [hQ]
      exact le_sSup ⟨inferInstance, hK2⟩
    have h1 : Q.relIndex V = 1 := relIndex_eq_one.mpr (hVP.trans hKQ)
    omega
  have hVAB : ⁅V, A⁆ ≤ B := commutator_le.mpr fun v hv a ha => hcomV v hv a (hAQ ha)
  have hBAZ : ⁅B, A⁆ ≤ Z := by
    rw [commutator_comm]
    exact commutator_le.mpr fun a ha b hb => hcomAB a ha b hb
  have hZA1 : ⁅Z, A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr fun z hz => by
    rw [mem_centralizer_iff]
    intro a _
    exact mem_center_iff.mp (hZc hz) a
  have hVAAA : ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ :=
    le_bot_iff.mp (hZA1 ▸ commutator_mono (commutator_mono hVAB le_rfl |>.trans hBAZ) le_rfl)
  have hAe : IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hV'c a (hAV' a.2) b (hAV' b.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using hV'2 a (hAV' a.2)) }
  have hVfin : ∃ n, Nat.card V = 2 ^ n := hV2P.exists_card_eq
  have hA2 : IsPGroup 2 A := hQ2.to_le hAQ
  obtain ⟨nV, hnV⟩ := hVfin
  obtain ⟨nA, hnA⟩ := hA2.exists_card_eq
  obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hnV ▸ relIndex_dvd_card (centralizer (A : Set X)) V)
  obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hnA ▸ relIndex_dvd_card (centralizer (V : Set X)) A)
  refine ⟨hZc, ⟨hPBA, hPn, hPQ⟩, ⟨hZB, hZA, hBA, hPP, hsq⟩, hXQ, ⟨hAQ, hQS, hAQ.trans hQV⟩,
    hCAV, hVA, hVAAA, hAe, d, r, hd, hr, ?_, ?_⟩
  ·
    refine Nat.pos_of_ne_zero fun h0 => hVA ?_
    rw [h0, pow_zero, relIndex_eq_one] at hd
    exact commutator_eq_bot_iff_le_centralizer.mpr hd
  ·
    have hr' : Z.relIndex A = 2 ^ r := by
      rw [← hr, ← hCAV, inf_comm, inf_relIndex_right]
    have hr0 : r ≠ 0 := fun h0 => hVA (by
      rw [h0, pow_zero, relIndex_eq_one] at hr
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hr)
    have hAB : Nat.card A = Nat.card B := by
      have hQc : Q.map (MulAut.conj g⁻¹).toMonoidHom = Q :=
        RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
          (by rw [normalizer_eq_top_iff.mpr hQn]; exact mem_top _)
      have hAeq : A = B.map (MulAut.conj g⁻¹).toMonoidHom := by
        rw [hA, hB, Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective, hQc]
        rfl
      rw [hAeq, card_map_of_injective (MulAut.conj g⁻¹).injective]
    have hZBidx : Z.relIndex B = 2 ^ r := by
      have h1 := relIndex_mul_card Z A
      have h2 := relIndex_mul_card Z B
      rw [inf_eq_left.mpr hZA] at h1
      rw [inf_eq_left.mpr hZB] at h2
      have hpos : 0 < Nat.card Z := Nat.card_pos
      rw [← hr']
      exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans (hAB.symm.trans h1.symm))
    have hBV2 : B.relIndex V = 2 := by
      rw [hB, inf_comm, inf_relIndex_right]
      exact hVQ
    have hZV : Z.relIndex V = 2 ^ (r + 1) := by
      rw [← relIndex_mul_relIndex Z B V hZB hBV, hZBidx, hBV2, pow_succ]
    have hle : (centralizer (A : Set X)).relIndex V ≤ Z.relIndex V :=
      relIndex_le_of_le_left (fun z hz => mem_centralizer_iff.mpr fun a _ =>
        (mem_center_iff.mp (hZc hz) a)) index_ne_zero_of_finite
    rw [hd, hZV] at hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega

end CFSG.Quasithin
