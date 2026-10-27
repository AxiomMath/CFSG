module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L2A
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAFin3
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAOdd

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.S3

open CFSG CFSG.RankThree.PartTwo.Sec21 TLn

local notation "Z3" => ZMod 3 × ZMod 3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

@[expose] def idp : Z3 × Z3 := ((1, 0), (0, 1))

@[expose] def negp : Z3 × Z3 := ((2, 0), (0, 2))

@[expose] def R1 : Z3 × Z3 := ((2, 0), (0, 1))

@[expose] def W1 : Z3 × Z3 := ((0, 1), (1, 0))

@[expose] def comp (E F : Z3 × Z3) : Z3 × Z3 := (lin E.1 E.2 F.1, lin E.1 E.2 F.2)

@[expose] def cpow (E : Z3 × Z3) : ℕ → Z3 × Z3
  | 0 => idp
  | n + 1 => comp (cpow E n) E

@[expose] def mpList : List (Z3 × Z3) :=
  [((1, 0), (0, 1)), ((2, 0), (0, 1)), ((1, 0), (0, 2)), ((2, 0), (0, 2)),
   ((0, 1), (1, 0)), ((0, 2), (1, 0)), ((0, 1), (2, 0)), ((0, 2), (2, 0))]

theorem lin_comp (E F : Z3 × Z3) (p : Z3) :
    lin (comp E F).1 (comp E F).2 p = lin E.1 E.2 (lin F.1 F.2 p) := by
  simp only [comp, lin_eq]; ext <;> simp <;> ring

theorem comp_assoc (E F H : Z3 × Z3) : comp (comp E F) H = comp E (comp F H) := by
  show (lin (comp E F).1 (comp E F).2 H.1, lin (comp E F).1 (comp E F).2 H.2) = _
  rw [lin_comp, lin_comp]; rfl

theorem comp_idp (E : Z3 × Z3) : comp E idp = E := by
  simp only [comp, idp, lin_10, lin_01]

theorem lin_idp (p : Z3) : lin idp.1 idp.2 p = p := by
  simp only [idp, lin_eq]; ext <;> simp

theorem cpow_add (E : Z3 × Z3) (a c : ℕ) : cpow E (a + c) = comp (cpow E a) (cpow E c) := by
  induction c with
  | zero => simp [cpow, comp_idp]
  | succ c ih => rw [← add_assoc, cpow, ih, comp_assoc, cpow]

theorem cpow_mod {E : Z3 × Z3} {k : ℕ} (hk : cpow E k = idp) (n : ℕ) :
    cpow E n = cpow E (n % k) := by
  conv_lhs => rw [← Nat.mod_add_div n k]
  generalize n / k = t
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← add_assoc, cpow_add, ih, hk, comp_idp]

set_option maxRecDepth 8000 in
theorem mem_mp : ∀ E : Z3 × Z3, IsMono E.1 → IsMono E.2 →
    (∀ p : Z3, lin E.1 E.2 p = 0 → p = 0) → E ∈ mpList := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem center_check : ∀ Ez ∈ mpList, ∀ E1 ∈ mpList, ∀ E4 ∈ mpList,
    comp E1 E4 ≠ comp E4 E1 → comp Ez E1 = comp E1 Ez → comp Ez E4 = comp E4 Ez →
    Ez ≠ idp → Ez = negp := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem noncomm_D_check : ∀ K ∈ mpList, ∀ Ki ∈ mpList, comp K Ki = idp → ∀ t ∈ [1, 3],
    comp (comp (comp K R1) Ki) (cpow (comp R1 W1) t) ≠
      comp (cpow (comp R1 W1) t) (comp (comp K R1) Ki) := by
  decide +kernel

theorem cpow_R1_two : cpow R1 2 = idp := by decide

theorem cpow_M4_four : cpow (comp R1 W1) 4 = idp := by decide

theorem negp_sq : comp negp negp = idp := by decide

theorem lin_negp (p : Z3) : lin negp.1 negp.2 p = -p := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  simp only [negp, lin_eq]; ext <;> simp [h2]

theorem card_mp : Nat.card {E : Z3 × Z3 // E ∈ mpList} = 8 := by
  rw [Nat.card_eq_fintype_card]; rfl

@[expose] def Act (u v g : G) (E : Z3 × Z3) : Prop :=
  g * u * g⁻¹ = ψ u v E.1 ∧ g * v * g⁻¹ = ψ u v E.2

variable {u v : G}

theorem act_conj (h : E9Data u v) {g : G} {E : Z3 × Z3} (hg : Act u v g E) (p : Z3) :
    g * ψ u v p * g⁻¹ = ψ u v (lin E.1 E.2 p) := conj_ψ h hg.1 hg.2 p

theorem act_mul (h : E9Data u v) {g k : G} {E F : Z3 × Z3} (hg : Act u v g E)
    (hk : Act u v k F) : Act u v (g * k) (comp E F) := by
  constructor
  · calc g * k * u * (g * k)⁻¹ = g * (k * u * k⁻¹) * g⁻¹ := by group
      _ = _ := by rw [hk.1, act_conj h hg]; rfl
  · calc g * k * v * (g * k)⁻¹ = g * (k * v * k⁻¹) * g⁻¹ := by group
      _ = _ := by rw [hk.2, act_conj h hg]; rfl

theorem act_one : Act u v (1 : G) idp := ⟨by simp [idp], by simp [idp]⟩

theorem act_pow (h : E9Data u v) {g : G} {E : Z3 × Z3} (hg : Act u v g E) (n : ℕ) :
    Act u v (g ^ n) (cpow E n) := by
  induction n with
  | zero => simpa [cpow] using act_one
  | succ n ih => rw [pow_succ, cpow]; exact act_mul h ih hg

theorem act_unique (h : E9Data u v) {g : G} {E F : Z3 × Z3} (hE : Act u v g E)
    (hF : Act u v g F) : E = F :=
  Prod.ext (ψ_inj h (hE.1.symm.trans hF.1)) (ψ_inj h (hE.2.symm.trans hF.2))

theorem act_inv_comp (h : E9Data u v) {g : G} {E F : Z3 × Z3} (hE : Act u v g E)
    (hF : Act u v g⁻¹ F) : comp E F = idp := by
  have := act_mul h hE hF
  rw [mul_inv_cancel] at this
  exact act_unique h this act_one

theorem exists_two_part (m : G) : ∃ s a : ℕ, ¬ 2 ∣ s ∧ (m ^ s) ^ (2 ^ a) = 1 := by
  obtain ⟨a, s, hs, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos m).ne' 2 (by norm_num)
  refine ⟨s, a, hs, ?_⟩
  rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]

theorem odd_of_not_dvd {s : ℕ} (hs : ¬ 2 ∣ s) : s % 2 = 1 := by omega

namespace PCtx

variable {b : G} {J B : Subgroup G} {r₁ r₂ w : G} {P : Subgroup G} {x y : G}
  (K : PCtx b J B u v r₁ r₂ w P x y)
include K

theorem H_b {g : G} (hg : g ∈ Cen b ⊓ Nor (Agrp x y u v)) : g * b * g⁻¹ = b := by
  have := Subgroup.mem_centralizer_singleton_iff.mp hg.1
  rw [this]; group

theorem H_R {g : G} (hg : g ∈ Cen b ⊓ Nor (Agrp x y u v)) {r : G} (hr : r ∈ R u v) :
    g * r * g⁻¹ ∈ R u v := by
  have hA : g * r * g⁻¹ ∈ Agrp x y u v :=
    (Subgroup.mem_normalizer_iff.mp hg.2 r).mp (K.R_le_A hr)
  refine K.A_inf_B hA (K.toCtx.P_cen K.hP (K.A_le_P hA) ?_)
  have hgb := K.H_b hg
  have hrb := K.toCtx.comm_bR hr
  calc g * r * g⁻¹ * b = g * r * (g⁻¹ * b * g) * g⁻¹ := by group
    _ = g * r * b * g⁻¹ := by rw [comm_conj hgb]
    _ = g * b * r * g⁻¹ := by rw [mul_assoc g r, ← hrb, ← mul_assoc]
    _ = (g * b * g⁻¹) * (g * r * g⁻¹) := by group
    _ = b * (g * r * g⁻¹) := by rw [hgb]

theorem exists_act {g : G} (hg : g ∈ Cen b ⊓ Nor (Agrp x y u v)) :
    ∃ E ∈ mpList, Act u v g E := by
  have hgJ : g ∈ Nor J := L13b.mem_nor_of_forall (K.toCtx.D.hnormJ g (Or.inl (K.H_b hg)))
  have hgR : g ∈ Nor (R u v) := L13b.mem_nor_of_forall fun r hr => K.H_R hg hr
  obtain ⟨hu, hv⟩ := K.toCtx.mono g hgJ hgR
  obtain ⟨e₁, he₁, h1⟩ := isMono_of_inBlocks hu
  obtain ⟨e₂, he₂, h2⟩ := isMono_of_inBlocks hv
  refine ⟨(e₁, e₂), mem_mp _ he₁ he₂ fun p hp => ?_, h1, h2⟩
  have := act_conj K.toCtx.E (g := g) (E := (e₁, e₂)) ⟨h1, h2⟩ p
  rw [hp, ψ_zero] at this
  exact ψ_eq_one K.toCtx.E (by
    calc ψ u v p = g⁻¹ * (g * ψ u v p * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group)

theorem H_of_realize {m : G} (hmP : m ∈ Nor P) (hmB : m ∈ Nor B) (hmb : m * b * m⁻¹ = b) :
    m ∈ Cen b ⊓ Nor (Agrp x y u v) := by
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, L41.mem_nor_of_forall fun a ha =>
    K.nor_A hmP hmB ha⟩
  calc m * b = (m * b * m⁻¹) * m := by group
    _ = b * m := by rw [hmb]

theorem eq_one_of_act_idp (hodd : Odd (Nat.card (CenS B))) {c : G} (hcb : c * b = b * c)
    (hc : Act u v c idp) {k : ℕ} (hk : c ^ (2 ^ k) = 1) : c = 1 := by
  have hcB : c ∈ CenS B := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨i, p, rfl⟩ := (K.toCtx.mem_B_iff).mp hz
    have h1 : c * ψ u v p * c⁻¹ = ψ u v p := by rw [act_conj K.toCtx.E hc, lin_idp]
    have h2 : Commute c (b ^ i.val) := Commute.pow_right hcb _
    calc b ^ i.val * ψ u v p * c = b ^ i.val * (c * ψ u v p * c⁻¹) * c := by rw [h1]
      _ = (c * b ^ i.val) * ψ u v p := by rw [h2.eq]; group
      _ = c * (b ^ i.val * ψ u v p) := by group
  have h1 : orderOf c ∣ Nat.card (CenS B) := by
    have := orderOf_dvd_natCard (⟨c, hcB⟩ : CenS B)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CenS B)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

theorem exists_D (hodd : Odd (Nat.card (CenS B))) (hJ : J = OUpp 2 (Cen b)) :
    ∃ D : Subgroup G, IsSylowOf 2 D (Cen b ⊓ Nor (Agrp x y u v)) ∧ D ≤ J ∧
      Nat.card D = 8 ∧ ¬ IsMulCommutative D ∧
      ∀ z ∈ Subgroup.center D, z ≠ 1 → (∀ p, z * ψ u v p * z⁻¹ = ψ u v (-p)) ∧ z ^ 2 = 1 ∧
        ∀ a ∈ Agrp x y u v, z * a * z⁻¹ = a⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := K.toCtx.E
  set H := Cen b ⊓ Nor (Agrp x y u v) with hH
  obtain ⟨m₁, hm₁P, hm₁B, hm₁b, hm₁R⟩ := K.toCtx.realize K.hP K.toCtx.r₁N (n := 1)
    (by rw [pow_one]; exact K.toCtx.conj_b_of_J K.toCtx.r₁J)
  obtain ⟨mw, hmwP, hmwB, hmwb, hmwR⟩ := K.toCtx.realize K.hP K.toCtx.wN (n := 1)
    (by rw [pow_one]; exact K.toCtx.conj_b_of_J K.toCtx.wJ)
  rw [pow_one] at hm₁b hmwb
  have hm₁H := K.H_of_realize hm₁P hm₁B hm₁b
  have hmwH := K.H_of_realize hmwP hmwB hmwb
  have c₁₁ := nd_r₁_conj K.toCtx.nd (1, 0)
  have c₁₂ := nd_r₁_conj K.toCtx.nd (0, 1)
  have cw₁ := nd_w_conj K.toCtx.nd (1, 0)
  have cw₂ := nd_w_conj K.toCtx.nd (0, 1)
  rw [ψ_10, lin_10] at c₁₁ cw₁
  rw [ψ_01, lin_01] at c₁₂ cw₂
  have hA₁ : Act u v m₁ R1 :=
    ⟨by rw [hm₁R u K.toCtx.uR]; exact c₁₁, by rw [hm₁R v K.toCtx.vR]; exact c₁₂⟩
  have hAw : Act u v mw W1 :=
    ⟨by rw [hmwR u K.toCtx.uR]; exact cw₁, by rw [hmwR v K.toCtx.vR]; exact cw₂⟩
  have hm₄H : m₁ * mw ∈ H := H.mul_mem hm₁H hmwH
  have hA₄ := act_mul hE hA₁ hAw
  obtain ⟨s₁, a₁, hs₁, h₁⟩ := exists_two_part m₁
  obtain ⟨s₄, a₄, hs₄, h₄⟩ := exists_two_part (m₁ * mw)
  have hA₁' : Act u v (m₁ ^ s₁) R1 := by
    have := act_pow hE hA₁ s₁
    rwa [cpow_mod cpow_R1_two, odd_of_not_dvd hs₁] at this
  have hA₄' := act_pow hE hA₄ s₄
  rw [cpow_mod cpow_M4_four] at hA₄'
  have ht₄ : s₄ % 4 ∈ [1, 3] := by
    have : s₄ % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have : s₄ % 4 ≠ 0 := fun h => hs₄ (by omega)
    have : s₄ % 4 ≠ 2 := fun h => hs₄ (by omega)
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]; omega
  have hQ : IsPGroup 2 (Subgroup.zpowers ((m₁ * mw) ^ s₄)) := isPGroup_zpowers_of_pow h₄
  obtain ⟨D, hD, hQD⟩ := exists_sylowOf_le
    ((Subgroup.zpowers_le).mpr (H.pow_mem hm₄H s₄)) hQ
  have hd₄ : (m₁ * mw) ^ s₄ ∈ D := hQD (Subgroup.mem_zpowers _)
  obtain ⟨k, hk, hkD⟩ := L41.exists_conj_le_sylowOf_p hD
    ((Subgroup.zpowers_le).mpr (H.pow_mem hm₁H s₁)) (isPGroup_zpowers_of_pow h₁)
  have hd₁ : k * m₁ ^ s₁ * k⁻¹ ∈ D := hkD _ (Subgroup.mem_zpowers _)
  obtain ⟨Kk, -, hKk⟩ := K.exists_act hk
  obtain ⟨Ki, hKi, hKi'⟩ := K.exists_act (H.inv_mem hk)
  have hKk_mem : Kk ∈ mpList := (K.exists_act hk).choose_spec.1 |> fun _ => by
    obtain ⟨E, hE', hEa⟩ := K.exists_act hk
    rwa [act_unique hE hKk hEa]
  have hAd₁ := act_mul hE (act_mul hE hKk hA₁') hKi'
  have hDH : D ≤ H := hD.1
  have h2el : ∀ g ∈ D, ∃ n : ℕ, g ^ (2 ^ n) = 1 := fun g hg => by
    obtain ⟨n, hn⟩ := hD.2.1 ⟨g, hg⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hinj : ∀ g ∈ D, ∀ h ∈ D, ∀ E, Act u v g E → Act u v h E → g = h := by
    intro g hg h hh E hgE hhE
    obtain ⟨Fi, -, hFi⟩ := K.exists_act (H.inv_mem (hDH hg))
    have hc := act_mul hE hFi hhE
    have hcomp : comp Fi E = idp := by
      have h1 := act_mul hE hFi hgE
      rw [inv_mul_cancel] at h1
      exact act_unique hE h1 act_one
    rw [hcomp] at hc
    have hcb : (g⁻¹ * h) * b = b * (g⁻¹ * h) := by
      have e1 := K.H_b (H.inv_mem (hDH hg))
      have e2 := K.H_b (hDH hh)
      calc g⁻¹ * h * b = g⁻¹ * (h * b * h⁻¹) * h := by group
        _ = (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * h) := by rw [e2]; group
        _ = b * (g⁻¹ * h) := by rw [e1]
    obtain ⟨n, hn⟩ := h2el _ (D.mul_mem (D.inv_mem hg) hh)
    have := K.eq_one_of_act_idp hodd hcb hc hn
    calc g = g * (g⁻¹ * h) := by rw [this, mul_one]
      _ = h := by group
  have hnc : k * m₁ ^ s₁ * k⁻¹ * (m₁ * mw) ^ s₄ ≠ (m₁ * mw) ^ s₄ * (k * m₁ ^ s₁ * k⁻¹) := by
    intro heq
    have h1 := act_mul hE hAd₁ hA₄'
    have h2 := act_mul hE hA₄' hAd₁
    rw [heq] at h1
    exact noncomm_D_check Kk hKk_mem Ki hKi (act_inv_comp hE hKk hKi') _ ht₄
      (act_unique hE h1 h2)
  have hnab : ¬ IsMulCommutative D := by
    intro hc
    apply hnc
    have := hc.is_comm.comm ⟨_, hd₁⟩ ⟨_, hd₄⟩
    exact congrArg Subtype.val this
  have hle8 : Nat.card D ≤ 8 := by
    have hex : ∀ g : D, ∃ E : {E : Z3 × Z3 // E ∈ mpList}, Act u v g E.1 := fun g => by
      obtain ⟨E, hE', hEa⟩ := K.exists_act (hDH g.2)
      exact ⟨⟨E, hE'⟩, hEa⟩
    choose f hf using hex
    have hfi : Function.Injective f := fun g h hgh => by
      apply Subtype.ext
      refine hinj g g.2 h h.2 (f g).1 (hf g) ?_
      rw [hgh]; exact hf h
    rw [← card_mp]
    exact Nat.card_le_card_of_injective f hfi
  have hcard : Nat.card D = 8 := by
    obtain ⟨n, hn⟩ := hD.2.1.exists_card_eq
    have hn3 : n ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n
    · exfalso; apply hnab
      haveI : Subsingleton D := (Nat.card_eq_one_iff_unique.mp hn).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · exfalso; apply hnab
      haveI : IsCyclic D := isCyclic_of_prime_card (p := 2) (by simpa using hn)
      infer_instance
    · exfalso; apply hnab
      exact ⟨⟨IsPGroup.commutative_of_card_eq_prime_sq (p := 2) hn⟩⟩
    · simpa using hn
  refine ⟨D, hD, fun g hg => ?_, hcard, hnab, ?_⟩
  · obtain ⟨n, hn⟩ := h2el g hg
    rw [hJ]
    exact mem_OUpp_of_pow (hDH hg).1 hn
  intro z hz hz1
  have hzH := hDH z.2
  obtain ⟨Ez, hEz, hAz⟩ := K.exists_act hzH
  obtain ⟨E1, hE1, hA1⟩ := K.exists_act (hDH hd₁)
  obtain ⟨E4, hE4, hA4⟩ := K.exists_act (hDH hd₄)
  have hcommE : ∀ (d : G) (hd : d ∈ D) (Ed : Z3 × Z3), Act u v d Ed →
      comp Ez Ed = comp Ed Ez := fun d hd Ed hEd => by
    have h1 := act_mul hE hAz hEd
    have h2 := act_mul hE hEd hAz
    have hc : (z : G) * d = d * z :=
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨d, hd⟩)).symm
    rw [hc] at h1
    exact act_unique hE h1 h2
  have hnc' : comp E1 E4 ≠ comp E4 E1 := fun heq => hnc (by
    refine hinj _ (D.mul_mem hd₁ hd₄) _ (D.mul_mem hd₄ hd₁) _ (act_mul hE hA1 hA4) ?_
    rw [heq]; exact act_mul hE hA4 hA1)
  have hne : Ez ≠ idp := fun h0 => hz1 (Subtype.ext (by
    rw [h0] at hAz
    exact hinj _ z.2 _ D.one_mem _ hAz act_one))
  have hEzn := center_check Ez hEz E1 hE1 E4 hE4 hnc' (hcommE _ hd₁ E1 hA1)
    (hcommE _ hd₄ E4 hA4) hne
  rw [hEzn] at hAz
  have hneg : ∀ p, (z : G) * ψ u v p * (z : G)⁻¹ = ψ u v (-p) := fun p => by
    rw [act_conj hE hAz p, lin_negp]
  have hz2 : (z : G) ^ 2 = 1 := by
    have h1 := act_mul hE hAz hAz
    rw [negp_sq] at h1
    rw [pow_two]
    exact hinj _ (D.mul_mem z.2 z.2) _ D.one_mem _ h1 act_one
  refine ⟨hneg, Subtype.ext (by simpa using hz2), fun a ha => ?_⟩
  have hzb := K.H_b hzH
  have haT := K.A_le_T ha
  have ha' : (z : G) * a * (z : G)⁻¹ ∈ Agrp x y u v :=
    (Subgroup.mem_normalizer_iff.mp hzH.2 a).mp ha
  obtain ⟨q, hq⟩ := exists_ψ hE (K.toCtx.θ_mem haT)
  have hθ' : θ b ((z : G) * a * (z : G)⁻¹) = (θ b a)⁻¹ := by
    rw [K.toCtx.θ_conj_of_cen _ _ hzb, hq, hneg, ψ_neg hE]
  have hrA : (z : G) * a * (z : G)⁻¹ * a ∈ Agrp x y u v := (Agrp x y u v).mul_mem ha' ha
  have hrR : (z : G) * a * (z : G)⁻¹ * a ∈ R u v := by
    refine K.A_inf_B hrA (K.toCtx.θ_eq_one_mem_B K.hP (K.A_le_P hrA) ?_)
    rw [K.toCtx.θ_mul (K.A_le_T ha') haT, hθ', inv_mul_cancel]
  set r := (z : G) * a * (z : G)⁻¹ * a with hr
  obtain ⟨q', hq'⟩ := exists_ψ hE hrR
  have h1 : (z : G) * r * (z : G)⁻¹ = r⁻¹ := by rw [hq', hneg, ψ_neg hE]
  have h2 : (z : G) * r * (z : G)⁻¹ = r := by
    have hz2' : (z : G) * (z : G) = 1 := by rw [← pow_two]; exact hz2
    have hzi : (z : G)⁻¹ = z := by rw [inv_eq_iff_mul_eq_one]; exact hz2'
    calc (z : G) * r * (z : G)⁻¹ = ((z : G) * (z : G)) * a * ((z : G) * (z : G))⁻¹ *
          ((z : G) * a * (z : G)⁻¹) := by rw [hr]; group
      _ = a * ((z : G) * a * (z : G)⁻¹) := by rw [hz2']; group
      _ = r := by rw [hr, K.A_comm ha ha']
  have hr1 : r = 1 := by
    have h3 := K.toCtx.pow3_R hrR
    have hrr : r * r = 1 := by
      have := h2.symm.trans h1
      calc r * r = r * r⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel r
    calc r = r ^ 3 * (r * r)⁻¹ := by rw [pow_three]; group
      _ = 1 := by rw [h3, hrr]; group
  calc (z : G) * a * (z : G)⁻¹ = r * a⁻¹ := by rw [hr]; group
    _ = a⁻¹ := by rw [hr1, one_mul]

end PCtx

end CFSG.RankThree.PartTwo.Sec21.FF79.S3
