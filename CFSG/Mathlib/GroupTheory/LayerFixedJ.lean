module

public import CFSG.Foundations.Basic
import CFSG.Mathlib.GroupTheory.LayerAbelianSylow
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.GroupTheory.Fitting.CharacteristicP

@[expose] public section

namespace CFSG.LayerFixed

structure FixData {X : Type} [Group X] (β : MulAut X) (u : X) (O J : Subgroup X) : Prop where
  pow : β ^ 3 = 1
  u_mem : u ∈ Subgroup.center X
  u_ne : u ≠ 1
  u_pow : u ^ 3 = 1
  fix_u : β u = u
  fix : ∀ x : X, β x = x → ∃ i : ℕ, ∃ o ∈ O, ∃ y ∈ J, x = u ^ i * o * y
  fix_O : ∀ o ∈ O, β o = o
  fix_J : ∀ y ∈ J, β y = y
  coprime : ¬ 3 ∣ Nat.card O
  comm : ∀ o ∈ O, ∀ y ∈ J, o * y = y * o
  simple : IsSimpleGroup J
  nonab : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x
  three_dvd : 3 ∣ Nat.card J

private theorem functionEnd_pow_apply {α : Type*} (f : Function.End α) (n : ℕ) (a : α) :
    (f ^ n) a = f^[n] a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change (f ^ n) (f a) = (fun a => f a)^[n + 1] a
      rw [ih (f a), Function.iterate_succ_apply]

private theorem card_modEq_fixedPoints_fun {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) {p : ℕ} [Fact p.Prime] (hf : f^[p] = id) :
    Fintype.card α ≡ Fintype.card (Function.fixedPoints f) [MOD p] := by
  let F : Function.End α := f
  have hEnd : F ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext a
    rw [functionEnd_pow_apply, hf]
    rfl
  exact Equiv.Perm.card_fixedPoints_modEq (f := F) (p := p) (n := 1) hEnd

private theorem natCard_union_eq {α : Type*} [Finite α] {s t : Set α} (h : Disjoint s t) :
    Nat.card (s ∪ t : Set α) = Nat.card s + Nat.card t := by
  rw [Nat.card_coe_set_eq (s ∪ t), Set.ncard_union_eq h, ← Nat.card_coe_set_eq s,
    ← Nat.card_coe_set_eq t]

private theorem card_modEq_fixedPoints_set {α : Type*} [Fintype α] [DecidableEq α]
    (Z : Set α) (f : α → α) (hfZ : ∀ a, a ∈ Z → f a ∈ Z) {p : ℕ} [Fact p.Prime]
    (hf : f^[p] = id) :
    Nat.card Z ≡ Nat.card (Z ∩ {a | f a = a} : Set α) [MOD p] := by
  classical
  let g : α → α := fun a => if a ∈ Z then f a else a
  have hg : g^[p] = id := by
    funext a
    by_cases ha : a ∈ Z
    · have hmem : ∀ n, f^[n] a ∈ Z := by
        intro n
        induction n with
        | zero => simpa using ha
        | succ n ih => rw [Function.iterate_succ_apply']; exact hfZ _ ih
      have hpow : ∀ n, g^[n] a = f^[n] a := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
            rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
            show g (f^[n] a) = f (f^[n] a)
            simp only [g]
            rw [if_pos (hmem n)]
      rw [hpow p, hf]
    · have hpow : ∀ n, g^[n] a = a := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
            rw [Function.iterate_succ_apply', ih]
            simp only [g]
            rw [if_neg ha]
      rw [hpow p]
      rfl
  have h := card_modEq_fixedPoints_fun g hg
  have hfix : Function.fixedPoints g = (Z ∩ {a | f a = a} : Set α) ∪ (Zᶜ : Set α) := by
    ext a
    by_cases ha : a ∈ Z <;> simp [Function.fixedPoints, Function.IsFixedPt, g, ha]
  have hdisj : Disjoint (Z ∩ {a : α | f a = a} : Set α) (Zᶜ : Set α) :=
    (disjoint_compl_right : Disjoint Z Zᶜ).mono_left Set.inter_subset_left
  have hcardfix : Fintype.card (Function.fixedPoints g)
      = Nat.card (Z ∩ {a | f a = a} : Set α) + Nat.card (Zᶜ : Set α) := by
    rw [← Nat.card_eq_fintype_card]
    rw [hfix]
    exact natCard_union_eq hdisj
  have hcardα : Fintype.card α = Nat.card Z + Nat.card (Zᶜ : Set α) := by
    have h := Set.ncard_add_ncard_compl Z
    rw [← Nat.card_coe_set_eq Z, ← Nat.card_coe_set_eq (Zᶜ : Set α)] at h
    rw [← Nat.card_eq_fintype_card]
    exact h.symm
  rw [hcardfix, hcardα] at h
  exact Nat.ModEq.add_right_cancel' _ h

private def fixedSubgroup {X : Type*} [Group X] (φ : MulAut X) : Subgroup X where
  carrier := {x | φ x = x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha, hb]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha]

private theorem mem_fixedSubgroup {X : Type*} [Group X] (φ : MulAut X) (x : X) :
    x ∈ fixedSubgroup φ ↔ φ x = x := Iff.rfl

private theorem mem_of_characteristic {X : Type*} [Group X] {K : Subgroup X}
    (hK : K.Characteristic) (φ : MulAut X) {x : X} (hx : x ∈ K) : φ x ∈ K := by
  have hmap : K.map (φ : X →* X) = K := (Subgroup.characteristic_iff_map_eq.mp hK) φ
  have : φ x ∈ K.map (φ : X →* X) := Subgroup.mem_map_of_mem (φ : X →* X) hx
  rwa [hmap] at this

private theorem mem_zpowers_mul_of_coprime {X : Type*} [Group X] {a b : X} (hab : Commute a b)
    (hcop : Nat.Coprime (orderOf a) (orderOf b)) : a ∈ Subgroup.zpowers (a * b) := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 0
  have hka : a ^ k = a := by
    rw [← pow_mod_orderOf a k, hk1, pow_mod_orderOf a 1, pow_one]
  have hkb : b ^ k = 1 := by
    rw [← pow_mod_orderOf b k, hk2, pow_mod_orderOf b 0, pow_zero]
  refine Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast, hab.mul_pow, hka, hkb, mul_one]

private theorem center_layer_eq_bot {X : Type} [Group X] [Finite X] (hO : pPrimeCore 3 X = ⊥)
    (hab : ∀ P : Sylow 3 X, ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    Subgroup.center (layer X) = ⊥ := by
  have hmap : (Subgroup.center (layer X)).map (layer X).subtype = ⊥ := by
    rw [(CFSG.LocalCores.layer_center (G := X)).1]
    exact iSup_eq_bot.mpr fun K => by
      rw [(CFSG.LayerAbelianSylow.center_eq_bot_and_three_dvd hO hab K.2).1]
      exact Subgroup.map_bot _
  exact Subgroup.map_injective (Subgroup.subtype_injective (layer X))
    (hmap.trans (Subgroup.map_bot _).symm)

private theorem inf_center_layer_eq_bot {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 3 X = ⊥)
    (hab : ∀ P : Sylow 3 X, ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    layer X ⊓ Subgroup.center X = ⊥ := by
  rw [← le_bot_iff]
  intro x hx
  have hxZ : (⟨x, hx.1⟩ : ↥(layer X)) ∈ Subgroup.center (layer X) := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx.2 (y : X))
  rw [center_layer_eq_bot hO hab] at hxZ
  simpa using hxZ

private theorem three_dvd_layer_of_ne_bot {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 3 X = ⊥)
    (hab : ∀ P : Sylow 3 X, ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hK : layer X ≠ ⊥) :
    3 ∣ Nat.card (layer X) := by
  by_contra h3
  exact hK (CFSG.LocalCores.layer_eq_bot_of_forall fun K hKc =>
    h3 ((CFSG.LayerAbelianSylow.center_eq_bot_and_three_dvd hO hab hKc).2.trans
      (Subgroup.card_dvd_of_le (CFSG.LocalCores.component_le_layer hKc))))

private theorem center_subgroup_eq_bot_of_simple_nonab {X : Type*} [Group X] {J : Subgroup X}
    (hJ : IsSimpleGroup J) (hnab : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) :
    Subgroup.center J = ⊥ := by
  by_contra hne
  rcases hJ.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact hne h
  · obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    have hx' : (⟨x, hx⟩ : J) ∈ Subgroup.center J := by rw [h]; trivial
    exact hxy (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx' ⟨y, hy⟩)).symm

private theorem le_of_inf_ne_bot {X : Type*} [Group X] {J K : Subgroup X}
    (hJ : IsSimpleGroup J) (hK : K.Normal) (hne : J ⊓ K ≠ ⊥) : J ≤ K := by
  have hnormal : ((J ⊓ K).subgroupOf J).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    exact ⟨J.mul_mem (J.mul_mem hk hh.1) (J.inv_mem hk), hK.conj_mem h hh.2 k⟩
  have : ((J ⊓ K).subgroupOf J).Normal := hnormal
  rcases hJ.eq_bot_or_eq_top_of_normal ((J ⊓ K).subgroupOf J) with hbot | htop
  · exact absurd (by
      have hd : Disjoint (J ⊓ K) J := Subgroup.subgroupOf_eq_bot.mp hbot
      have hle : J ⊓ K ≤ J := inf_le_left
      exact (inf_eq_left.mpr hle).symm.trans (disjoint_iff.mp hd)) hne
  · exact (le_inf_iff.mp (Subgroup.subgroupOf_eq_top.mp htop)).2

theorem le_layer_of_fixData {X : Type} [Group X] [Finite X] (hO : pPrimeCore 3 X = ⊥)
    (hab : ∀ P : Sylow 3 X, ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {β : MulAut X} {u : X}
    {O J : Subgroup X} (hF : FixData β u O J) :
    J ≤ layer X ∧ ∀ x ∈ layer X, β x = x ↔ ∃ o ∈ O ⊓ layer X, ∃ y ∈ J, x = o * y := by
  classical
  let : Fintype X := Fintype.ofFinite X
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKchar : (layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  have : (layer X).Characteristic := hKchar
  have hKnormal : (layer X).Normal := inferInstance
  have hinfZ : layer X ⊓ Subgroup.center X = ⊥ := inf_center_layer_eq_bot hO hab
  have hJcenter : Subgroup.center J = ⊥ :=
    center_subgroup_eq_bot_of_simple_nonab hF.simple hF.nonab
  have h3notO : Nat.Coprime 3 (Nat.card O) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr hF.coprime
  have hJK : J ≤ layer X := by
    by_contra hne
    have hbot : J ⊓ layer X = ⊥ := by
      by_contra hb
      exact hne (le_of_inf_ne_bot hF.simple hKnormal hb)
    rcases eq_or_ne (layer X) ⊥ with hKbot | hKne
    ·
      have hFstar : generalizedFitting X = fittingSubgroup X := by
        rw [CFSG.generalizedFitting.eq_sup, hKbot, sup_bot_eq]
      have hBender : Subgroup.centralizer (fittingSubgroup X : Set X) ≤ fittingSubgroup X := by
        rw [← hFstar]
        exact CFSG.centralizer_generalizedFitting_le X
      have hF3 : IsPGroup 3 (fittingSubgroup X) :=
        CFSG.isPGroup_of_nilpotent_normal (fittingSubgroup X) inferInstance inferInstance hO
      obtain ⟨P⟩ : Nonempty (Sylow 3 X) := inferInstance
      have hFP : fittingSubgroup X ≤ (P : Subgroup X) := IsPGroup.le_sylow_of_normal hF3 P
      have hPcent : (P : Subgroup X) ≤ Subgroup.centralizer (fittingSubgroup X : Set X) := by
        intro p hp
        rw [Subgroup.mem_centralizer_iff]
        intro f hf
        exact (hab P p hp f (hFP hf)).symm
      have hCnormal : (Subgroup.centralizer (fittingSubgroup X : Set X)).Normal := inferInstance
      have h3notC : ¬ 3 ∣ (Subgroup.centralizer (fittingSubgroup X : Set X)).index := fun h3 =>
        Sylow.not_dvd_index P (h3.trans (Subgroup.index_dvd_of_le hPcent))
      have hJC : J ≤ Subgroup.centralizer (fittingSubgroup X : Set X) := by
        by_contra hnot
        have hbotC : J ⊓ Subgroup.centralizer (fittingSubgroup X : Set X) = ⊥ := by
          by_contra hb
          exact hnot (le_of_inf_ne_bot hF.simple hCnormal hb)
        have hinj : Function.Injective
            ((QuotientGroup.mk' (Subgroup.centralizer (fittingSubgroup X : Set X))).comp
              J.subtype) := by
          intro a b hab
          obtain ⟨z, hzC, hzab⟩ :=
            (QuotientGroup.mk'_eq_mk' (Subgroup.centralizer (fittingSubgroup X : Set X))).mp hab
          have hzJ : z ∈ J := by
            have hz : z = (J.subtype a)⁻¹ * J.subtype b := by rw [← hzab]; group
            rw [hz]
            exact J.mul_mem (J.inv_mem a.2) b.2
          have hz1 : z = 1 := by
            have hmem : z ∈ J ⊓ Subgroup.centralizer (fittingSubgroup X : Set X) := ⟨hzJ, hzC⟩
            rw [hbotC] at hmem
            simpa using hmem
          apply Subtype.ext
          have h : J.subtype a = J.subtype b := by rw [← hzab, hz1, mul_one]
          exact h
        have hdvd : Nat.card J ∣ (Subgroup.centralizer (fittingSubgroup X : Set X)).index := by
          have h := Subgroup.card_dvd_of_injective
            ((QuotientGroup.mk' (Subgroup.centralizer (fittingSubgroup X : Set X))).comp
              J.subtype) hinj
          rwa [← Subgroup.index_eq_card] at h
        exact h3notC (hF.three_dvd.trans hdvd)
      have hJF : J ≤ fittingSubgroup X := hJC.trans hBender
      have hJ3 : IsPGroup 3 J := hF3.to_le hJF
      have : Group.IsNilpotent ↥J := hJ3.isNilpotent
      have : IsSimpleGroup J := hF.simple
      obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonab
      exact hxy (congrArg Subtype.val (mul_comm (⟨x, hx⟩ : J) ⟨y, hy⟩))
    ·
      have h3K : 3 ∣ Nat.card (layer X) := three_dvd_layer_of_ne_bot hO hab hKne
      let C : Subgroup X := layer X ⊓ fixedSubgroup β
      have hCset : (C : Set X) = (layer X : Set X) ∩ {a : X | β a = a} := by
        ext a
        simp [C, mem_fixedSubgroup]
      have hiter : (β : X → X)^[3] = id := by
        funext a
        change β (β (β a)) = a
        have h : (β ^ 3) a = a := by rw [hF.pow, MulAut.one_apply]
        simpa [pow_succ, MulAut.mul_apply] using h
      have hβZ : ∀ a, a ∈ (layer X : Set X) → β a ∈ layer X :=
        fun a ha => mem_of_characteristic hKchar β ha
      have hmod : Nat.card (layer X) ≡ Nat.card C [MOD 3] := by
        have h := card_modEq_fixedPoints_set (Z := (layer X : Set X)) (f := (β : X → X))
          hβZ hiter
        rwa [← hCset] at h
      have h3C : 3 ∣ Nat.card C :=
        Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3K))
      obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 h3C
      have hcK : (c : X) ∈ layer X := c.2.1
      have hcfix : β (c : X) = (c : X) := (mem_fixedSubgroup β (c : X)).mp c.2.2
      have hcne : (c : X) ≠ 1 := by
        intro h
        have h1 : orderOf c = 1 := by
          rw [← Subgroup.orderOf_coe (c : ↥C), h, orderOf_one]
        omega
      have hCcomm : ∀ z ∈ C, ∀ y ∈ J, z * y = y * z := by
        intro z hz y hy
        have hzK : z ∈ layer X := hz.1
        have hzfix : β z = z := (mem_fixedSubgroup β z).mp hz.2
        obtain ⟨a, o', ho', y', hy', hz_decomp⟩ := hF.fix z hzfix
        have hd : u ^ a * o' ∈ Subgroup.centralizer (J : Set X) :=
          mul_mem (Subgroup.mem_centralizer_iff.mpr fun w _ =>
              Commute.pow_right (Subgroup.mem_center_iff.mp hF.u_mem w) a)
            (Subgroup.mem_centralizer_iff.mpr fun w hw => (hF.comm o' ho' w hw).symm)
        have hzyJ : z * y * z⁻¹ ∈ J := by
          have hconj : z * y * z⁻¹ = y' * y * y'⁻¹ := by
            have hd' : ∀ w ∈ J, (u ^ a * o') * w * (u ^ a * o')⁻¹ = w := by
              intro w hw
              have hcomm := Subgroup.mem_centralizer_iff.mp hd w hw
              rw [hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
            rw [hz_decomp]
            have heq : (u ^ a * o') * y' * y * ((u ^ a * o') * y')⁻¹
                = (u ^ a * o') * (y' * y * y'⁻¹) * (u ^ a * o')⁻¹ := by
              simp only [mul_inv_rev, mul_assoc]
            rw [heq, hd' (y' * y * y'⁻¹)
              (J.mul_mem (J.mul_mem hy' hy) (J.inv_mem hy'))]
          rw [hconj]
          exact J.mul_mem (J.mul_mem hy' hy) (J.inv_mem hy')
        have hcommJ : z * y * z⁻¹ * y⁻¹ ∈ J := J.mul_mem hzyJ (J.inv_mem hy)
        have hcommK : z * y * z⁻¹ * y⁻¹ ∈ layer X := by
          have h1 : y * z * y⁻¹ * z⁻¹ ∈ layer X :=
            (layer X).mul_mem (hKnormal.conj_mem z hzK y) ((layer X).inv_mem hzK)
          have h2 : (y * z * y⁻¹ * z⁻¹)⁻¹ ∈ layer X := (layer X).inv_mem h1
          rwa [show (y * z * y⁻¹ * z⁻¹)⁻¹ = z * y * z⁻¹ * y⁻¹ from by group] at h2
        have hmem : z * y * z⁻¹ * y⁻¹ = 1 := by
          have hmem' : z * y * z⁻¹ * y⁻¹ ∈ J ⊓ layer X := ⟨hcommJ, hcommK⟩
          rw [hbot] at hmem'
          simpa using hmem'
        calc z * y = (z * y * z⁻¹ * y⁻¹) * (y * z) := by group
          _ = 1 * (y * z) := by rw [hmem]
          _ = y * z := one_mul _
      obtain ⟨i, o, ho, y₀, hy₀, hc_decomp⟩ := hF.fix (c : X) hcfix
      have hy₀_center : (⟨y₀, hy₀⟩ : J) ∈ Subgroup.center J := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        change (y : X) * y₀ = y₀ * (y : X)
        have hcy := hCcomm (c : X) c.2 (y : X) y.2
        have hd : u ^ i * o ∈ Subgroup.centralizer (J : Set X) :=
          mul_mem (Subgroup.mem_centralizer_iff.mpr fun w _ =>
              Commute.pow_right (Subgroup.mem_center_iff.mp hF.u_mem w) i)
            (Subgroup.mem_centralizer_iff.mpr fun w hw => (hF.comm o ho w hw).symm)
        have hdy : (y : X) * (u ^ i * o) = (u ^ i * o) * (y : X) :=
          Subgroup.mem_centralizer_iff.mp hd (y : X) y.2
        calc (y : X) * y₀
            = (u ^ i * o)⁻¹ * ((u ^ i * o) * ((y : X) * y₀)) := by group
          _ = (u ^ i * o)⁻¹ * (((u ^ i * o) * (y : X)) * y₀) := by group
          _ = (u ^ i * o)⁻¹ * (((y : X) * (u ^ i * o)) * y₀) := by rw [hdy]
          _ = (u ^ i * o)⁻¹ * ((y : X) * ((u ^ i * o) * y₀)) := by group
          _ = (u ^ i * o)⁻¹ * ((y : X) * (c : X)) := by rw [← hc_decomp]
          _ = (u ^ i * o)⁻¹ * ((c : X) * (y : X)) := by rw [hcy]
          _ = (u ^ i * o)⁻¹ * (((u ^ i * o) * y₀) * (y : X)) := by rw [← hc_decomp]
          _ = (u ^ i * o)⁻¹ * ((u ^ i * o) * y₀) * (y : X) := by group
          _ = y₀ * (y : X) := by group
      have hy₀_one : y₀ = 1 := by
        rw [hJcenter] at hy₀_center
        have h : (⟨y₀, hy₀⟩ : J) = 1 := by simpa using hy₀_center
        simpa using congrArg Subtype.val h
      have hc_eq : (c : X) = u ^ i * o := by rw [hc_decomp, hy₀_one, mul_one]
      have hc3 : (c : X) ^ 3 = 1 := by
        have h : c ^ 3 = 1 := by rw [← hc_ord]; exact pow_orderOf_eq_one c
        simpa using congrArg Subtype.val h
      have huoi : Commute (u ^ i) o :=
        (Commute.pow_right (Subgroup.mem_center_iff.mp hF.u_mem o) i).symm
      have ho_one : o = 1 := by
        have h3 : (u ^ i * o) ^ 3 = 1 := by rw [← hc_eq]; exact hc3
        rw [huoi.mul_pow] at h3
        have hu3 : (u ^ i) ^ 3 = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hF.u_pow, one_pow]
        rw [hu3, one_mul] at h3
        have horder3 : orderOf o ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
        have horderO : orderOf o ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O ho
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3notO horder3 horderO)
      have hc_u : (c : X) = u ^ i := by rw [hc_eq, ho_one, mul_one]
      have huiK : u ^ i ∈ layer X := by rw [← hc_u]; exact hcK
      have huK : u ∈ layer X := by
        have hord_ui : orderOf (u ^ i) = 3 := by rw [← hc_u, Subgroup.orderOf_coe]; exact hc_ord
        have hord_u : orderOf u = 3 := by
          have hdvd : orderOf u ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hF.u_pow
          rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hF.u_ne
          · exact h
        have hle : Subgroup.zpowers (u ^ i) ≤ Subgroup.zpowers u :=
          Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers u i)
        have hcard : Nat.card (Subgroup.zpowers (u ^ i)) = Nat.card (Subgroup.zpowers u) := by
          rw [Nat.card_zpowers, Nat.card_zpowers, hord_ui, hord_u]
        have heq : Subgroup.zpowers (u ^ i) = Subgroup.zpowers u :=
          Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
        have hu_mem : u ∈ Subgroup.zpowers (u ^ i) := by
          rw [heq]; exact Subgroup.mem_zpowers u
        exact Subgroup.zpowers_le.mpr huiK hu_mem
      exact hF.u_ne (by
        have hmem : u ∈ (⊥ : Subgroup X) := by
          rw [← hinfZ]; exact ⟨huK, hF.u_mem⟩
        simpa using hmem)
  refine ⟨hJK, fun x hxK => ⟨?_, ?_⟩⟩
  · intro hβx
    obtain ⟨i, o, ho, y, hy, hxy⟩ := hF.fix x hβx
    have hyK : y ∈ layer X := hJK hy
    have hc_mem : u ^ i * o ∈ layer X := by
      have h : x * y⁻¹ ∈ layer X := (layer X).mul_mem hxK ((layer X).inv_mem hyK)
      rw [hxy] at h
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using h
    have hui3 : (u ^ i) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hF.u_pow, one_pow]
    have hcop : Nat.Coprime (orderOf (u ^ i)) (orderOf o) :=
      Nat.Coprime.of_dvd_left (orderOf_dvd_iff_pow_eq_one.mpr hui3)
        (h3notO.coprime_dvd_right (Subgroup.orderOf_dvd_natCard O ho))
    have hcomm : Commute (u ^ i) o :=
      (Commute.pow_right (Subgroup.mem_center_iff.mp hF.u_mem o) i).symm
    have huiK : u ^ i ∈ layer X :=
      Subgroup.zpowers_le.mpr hc_mem (mem_zpowers_mul_of_coprime hcomm hcop)
    have hui_one : u ^ i = 1 := by
      have hmem : u ^ i ∈ (⊥ : Subgroup X) := by
        rw [← hinfZ]
        exact ⟨huiK, Subgroup.mem_center_iff.mpr fun w =>
          Commute.pow_right (Subgroup.mem_center_iff.mp hF.u_mem w) i⟩
      simpa using hmem
    rw [hui_one, one_mul] at hxy
    refine ⟨o, ⟨ho, ?_⟩, y, hy, hxy⟩
    have hoK : o = x * y⁻¹ := by rw [hxy]; group
    rw [hoK]
    exact (layer X).mul_mem hxK ((layer X).inv_mem hyK)
  · rintro ⟨o, ho, y, hy, rfl⟩
    rw [map_mul, hF.fix_O o ho.1, hF.fix_J y hy]

end CFSG.LayerFixed

end
