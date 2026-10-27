module

public import CFSG.Quasithin.Vol2.Ch11G2Q8OffA1
public import CFSG.Quasithin.Vol2.Ch11G2Q8OffQr

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_mul uSL_inv)

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem conj_apply_mem_map {Γ : Subgroup ↥(cayleyGroup F)} (x : ↥(cayleyGroup F))
    {g : ↥(cayleyGroup F)} (hg : g ∈ Γ) :
    x * g * x⁻¹ ∈ Γ.map (MulAut.conj x).toMonoidHom :=
  ⟨g, hg, rfl⟩

theorem fixStable_map_conj {k : ℕ} {Γ : Subgroup ↥(cayleyGroup F)} (hP : FixStable k Γ)
    (x : ↥(cayleyGroup F)) : FixStable k (Γ.map (MulAut.conj x).toMonoidHom) := by
  intro B hB hcard w hw γ hγ
  have hB' : B.map (MulAut.conj x⁻¹).toMonoidHom ≤ Γ := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨g, hg, rfl⟩ := hB hb
    change x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ ∈ Γ
    rwa [show x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g by group]
  have hc1 : Nat.card ↥(Γ.map (MulAut.conj x).toMonoidHom) = Nat.card ↥Γ :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hc2 : Nat.card ↥(B.map (MulAut.conj x⁻¹).toMonoidHom) = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
  have h1 := hP _ hB' (by rw [hc2, ← hc1]; exact hcard) (g2Act x⁻¹ w) (by
    rintro _ ⟨b, hb, rfl⟩
    change g2Act (x⁻¹ * b * x⁻¹⁻¹) (g2Act x⁻¹ w) = g2Act x⁻¹ w
    rw [inv_inv, g2Act_mul_apply, g2Act_mul_apply, g2Act_apply_inv, hw b hb])
  obtain ⟨g, hg, rfl⟩ := hγ
  change g2Act (x * g * x⁻¹) w = w
  rw [g2Act_mul_apply, g2Act_mul_apply, h1 g hg, g2Act_apply_inv]

theorem exists_fix_ne_zero [Finite F] {Γ : Subgroup ↥(cayleyGroup F)}
    (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1) : ∃ w : Ix3 → F, w ≠ 0 ∧ ∀ γ ∈ Γ, g2Act γ w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_cayleyGroup (F := F)
  let _ : MulAction ↥Γ (Ix3 → F) :=
    { smul := fun g w => g2Act (g : ↥(cayleyGroup F)) w
      one_smul := fun w => by
        change g2Act 1 w = w
        rw [map_one]
        rfl
      mul_smul := fun g h w => g2Act_mul_apply (g : ↥(cayleyGroup F)) h w }
  have hp : IsPGroup 2 ↥Γ := fun g =>
    ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, pow_one, sq, Subgroup.coe_one]; exact hΓ1 g g.2)⟩
  have h2 : 2 ∣ Nat.card (Ix3 → F) := by
    rw [card_Q]
    refine dvd_pow ?_ (by norm_num)
    have h1 := addOrderOf_dvd_natCard (1 : F)
    rwa [CharP.eq F (CharP.addOrderOf_one F) inferInstance] at h1
  obtain ⟨b, hb, hne⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Ix3 → F) h2
    (a := 0) (fun g => map_zero (g2Act (g : ↥(cayleyGroup F))))
  exact ⟨b, fun h => hne h.symm, fun γ hγ => hb ⟨γ, hγ⟩⟩

open Classical in
@[expose] noncomputable def dirV (v : F × F) : Option F :=
  if v.1 = 0 then none else some (v.2 / v.1)

omit [CharP F 2] in
theorem onLine_dirV_of {v w : F × F} (hv : v ≠ 0) (h : w.1 * v.2 = w.2 * v.1) :
    OnLine (dirV v) w := by
  unfold dirV
  split_ifs with h1
  · show w.1 = 0
    have hv2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
    rw [h1, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hv2
  · show w.2 = v.2 / v.1 * w.1
    rw [div_mul_eq_mul_div, eq_div_iff h1]
    linear_combination -h

omit [CharP F 2] in
theorem onLine_dirV_self {v : F × F} (hv : v ≠ 0) : OnLine (dirV v) v :=
  onLine_dirV_of hv (mul_comm _ _)

omit [CharP F 2] in
theorem card_rootD_le [Finite F] (d : Option F) : Nat.card ↥(rootD d) ≤ Nat.card F := by
  have hs : Function.Surjective (fun t : F =>
      (⟨g2A (uSL (Option.elim d 0 fun _ => t) (Option.elim d t fun s => s * t) 0),
        ⟨(Option.elim d 0 fun _ => t, Option.elim d t fun s => s * t), by
          cases d <;> simp [OnLine], rfl⟩⟩ : ↥(rootD d))) := by
    rintro ⟨_, v, hv, rfl⟩
    cases d with
    | none =>
      refine ⟨v.2, Subtype.ext ?_⟩
      simp only [OnLine] at hv
      simp [hv]
    | some s =>
      refine ⟨v.1, Subtype.ext ?_⟩
      simp only [OnLine] at hv
      simp [hv]
  exact Nat.card_le_card_of_surjective _ hs

theorem card_Z1_le [Finite F] : Nat.card ↥(Z1 F) ≤ Nat.card F ^ 2 := by
  have hs : Function.Surjective (fun v : F × F =>
      (⟨g2A (uSL v.1 v.2 0), v, rfl⟩ : ↥(Z1 F))) := by
    rintro ⟨_, v, rfl⟩
    exact ⟨v, rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hs
  rwa [Nat.card_prod, ← sq] at h1

theorem Z1_le_A1 : Z1 F ≤ A1 F := by
  rintro _ ⟨v, rfl⟩
  have h := kerElt_mem_A1 (0 : F) v.1 v.2
  rwa [show (![(0 : F), 0, 0] : Fin 3 → F) = 0 from funext fun i => by fin_cases i <;> rfl,
    g2X_zero, g2Y_zero, one_mul, one_mul] at h

theorem eq_uSL_of_A1 {p q' : F} :
    g2X ![(0 : F), 0, 0] * g2Y ![0, 0, 0] * g2A (uSL p q' 0) = g2A (uSL p q' 0) := by
  rw [show (![(0 : F), 0, 0] : Fin 3 → F) = 0 from funext fun i => by fin_cases i <;> rfl,
    g2X_zero, g2Y_zero, one_mul, one_mul]

theorem mem_F3_of_fix_short {a b : F} {w : Ix3 → F}
    (h : g2Act (g2X ![1, 0, 0] * g2Y ![0, 0, 0] * g2A (uSL a b 0)) w = w) : w ∈ stdF F 3 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 := h
  conv_lhs at h1 => rw [q6_eta w]
  rw [g2Act_A1] at h1
  have e0 := congrFun h1 (.inl 0)
  have e4 := congrFun h1 (.inr 1)
  have e5 := congrFun h1 (.inr 2)
  simp only [q6_apply_inl0, q6_apply_inr1, q6_apply_inr2] at e0 e4 e5
  have hd : w (.inr 0) = 0 := by
    linear_combination e0 - a * e5 - b * e4 + a * b * w (.inr 0) * h2
  refine mem_stdF_three.mpr ⟨?_, ?_, hd⟩
  · linear_combination e5 - b * hd
  · linear_combination e4 - a * hd

omit [CharP F 2] in
theorem map_map_conj_inv (Γ : Subgroup ↥(cayleyGroup F)) (x : ↥(cayleyGroup F)) :
    (Γ.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = Γ := by
  rw [Subgroup.map_map]
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    change x * (x⁻¹ * h * x⁻¹⁻¹) * x⁻¹ ∈ Γ
    rwa [show x * (x⁻¹ * h * x⁻¹⁻¹) * x⁻¹ = h by group]
  · intro hg
    refine ⟨g, hg, ?_⟩
    change x * (x⁻¹ * g * x⁻¹⁻¹) * x⁻¹ = g
    group

theorem exists_conj_le_A1 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) {k : ℕ}
    (hk1 : Nat.card F < k) (hk2 : Nat.card F ^ 2 ≤ 2 * k)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) (hΓne : Γ ≠ ⊥) (hP : FixStable k Γ) :
    ∃ x : ↥(cayleyGroup F), Γ.map (MulAut.conj x⁻¹).toMonoidHom ≤ A1 F ∧
      ∀ w, (∀ γ ∈ Γ.map (MulAut.conj x⁻¹).toMonoidHom, g2Act γ w = w) → w ∈ stdF F 3 := by
  have := finite_cayleyGroup (F := F)
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hconj1 : ∀ x : ↥(cayleyGroup F), ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom,
      γ * γ = 1 := by
    rintro x _ ⟨g, hg, rfl⟩
    change x * g * x⁻¹ * (x * g * x⁻¹) = 1
    rw [show x * g * x⁻¹ * (x * g * x⁻¹) = x * (g * g) * x⁻¹ by group, hΓ1 g hg]
    group
  have hconjc : ∀ x : ↥(cayleyGroup F), ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom,
      ∀ δ ∈ Γ.map (MulAut.conj x).toMonoidHom, γ * δ = δ * γ := by
    rintro x _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    change x * g * x⁻¹ * (x * h * x⁻¹) = x * h * x⁻¹ * (x * g * x⁻¹)
    rw [show x * g * x⁻¹ * (x * h * x⁻¹) = x * (g * h) * x⁻¹ by group, hΓc g hg h hh]
    group
  have htriv : ∀ x : ↥(cayleyGroup F),
      (∀ w, ∀ γ ∈ Γ.map (MulAut.conj x).toMonoidHom, g2Act γ w = w) → False := by
    intro x h
    apply hΓne
    rw [eq_bot_iff]
    intro g hg
    have h1 : x * g * x⁻¹ = 1 := cayley_eq_one fun w => h w _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_bot]
    calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  by_cases hA : ∃ r ∈ Γ, ∃ x, qr r x ≠ 0
  ·
    obtain ⟨r, hrΓ, x₀, hx₀⟩ := hA
    obtain ⟨p, hp⟩ := exists_qr_eq_sq (hΓ1 r hrΓ)
    have hp0 : p ≠ 0 := by
      rintro rfl
      apply hx₀
      rw [hp]
      simp [polarQ]
    obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hp0
    obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = Γ.map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
    have hP' : FixStable k Γ' := hΓ' ▸ fixStable_map_conj hP g⁻¹
    have hΓ'1 : ∀ γ ∈ Γ', γ * γ = 1 := hΓ' ▸ hconj1 g⁻¹
    have hΓ'c : ∀ γ ∈ Γ', ∀ δ ∈ Γ', γ * δ = δ * γ := hΓ' ▸ hconjc g⁻¹
    have hr' : g⁻¹ * r * g ∈ Γ' := by
      have h1 := hΓ' ▸ conj_apply_mem_map g⁻¹ hrΓ
      rwa [inv_inv] at h1
    have hqr' : ∀ x, qr (g⁻¹ * r * g) x = x (.inr 0) * x (.inr 0) := by
      intro x
      have h1 := qr_conj g⁻¹ r (g2Act g x)
      rw [inv_inv, g2Act_inv_apply] at h1
      rw [h1, hp, ← polarQ_g2Act g⁻¹, g2Act_inv_apply, ← hg, g2Act_inv_apply, polarQ_eu0]
    obtain ⟨a, b, hab⟩ := eq_kerElt_of_qr (hΓ'1 _ hr') hqr'
    have hS : Γ' ≤ stabV0 F := fun s hs =>
      fix_of_qr_sq (r := g⁻¹ * r * g) (p := eu 0 1) (fun x => by rw [hqr', polarQ_eu0])
        (hΓ'c s hs _ hr')
    have hR : Γ' ⊓ pCoreOf 2 (stabV0 F) ≤ A1 F := by
      rintro h ⟨hhΓ', hhR⟩
      obtain ⟨hhS, hM⟩ := mem_pCoreOf_stabV0_iff.mp hhR
      obtain ⟨α, β, γ, p', q', rfl⟩ := eq_of_levi1Mat_eq_one hhS hM
      have hc := hΓ'c _ hhΓ' _ hr'
      rw [hab] at hc
      obtain ⟨rfl, rfl⟩ := kerElt_eq_of_comm hc
      exact kerElt_mem_A1 α p' q'
    have hlt : Nat.card ↥Γ' < k * Nat.card ↥(Γ' ⊓ pCoreOf 2 (stabV0 F)) :=
      (card_le_mul_card_inf_R1 hF hn hS hΓ'1).trans_lt
        (Nat.mul_lt_mul_of_pos_right hk1 Nat.card_pos)
    have hΓ'A1 : Γ' ≤ A1 F := fun γ hγ w hw =>
      hP' _ inf_le_left hlt w (fun h hh => hR hh w hw) γ hγ
    have hfix' : ∀ w, (∀ γ ∈ Γ', g2Act γ w = w) → w ∈ stdF F 3 := by
      intro w hw
      have h1 := hw _ hr'
      rw [hab] at h1
      exact mem_F3_of_fix_short h1
    refine ⟨g, ?_, ?_⟩
    · rw [← hΓ']
      exact hΓ'A1
    · rw [← hΓ']
      exact hfix'
  ·
    have hA' : ∀ r ∈ Γ, ∀ x, qr r x = 0 := fun r hr x => by
      by_contra h
      exact hA ⟨r, hr, x, h⟩
    exfalso
    obtain ⟨w₀, hw₀, hfix₀⟩ := exists_fix_ne_zero hΓ1
    obtain ⟨g, hg⟩ := exists_g2Act_eu_eq hw₀
    obtain ⟨Γ', hΓ'⟩ : ∃ Γ', Γ' = Γ.map (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
    have hP' : FixStable k Γ' := hΓ' ▸ fixStable_map_conj hP g⁻¹
    have hΓ'1 : ∀ γ ∈ Γ', γ * γ = 1 := hΓ' ▸ hconj1 g⁻¹
    have hS : Γ' ≤ stabV0 F := by
      rw [hΓ']
      rintro _ ⟨γ, hγ, rfl⟩
      show g2Act (g⁻¹ * γ * g⁻¹⁻¹) (eu 0 1) = eu 0 1
      rw [inv_inv, g2Act_mul_apply, g2Act_mul_apply, hg, hfix₀ γ hγ, ← hg, g2Act_inv_apply]
    have hq0 : ∀ r ∈ Γ', ∀ x, qr r x = 0 := by
      rw [hΓ']
      rintro _ ⟨γ, hγ, rfl⟩ x
      have h1 := qr_conj g⁻¹ γ (g2Act g x)
      rw [inv_inv, g2Act_inv_apply] at h1
      change qr (g⁻¹ * γ * g⁻¹⁻¹) x = 0
      rw [inv_inv, h1, hA' γ hγ]
    have hR : Γ' ⊓ pCoreOf 2 (stabV0 F) ≤ Z1 F := by
      rintro h ⟨hhΓ', hhR⟩
      obtain ⟨hhS, hM⟩ := mem_pCoreOf_stabV0_iff.mp hhR
      obtain ⟨α, β, γ, p', q', rfl⟩ := eq_of_levi1Mat_eq_one hhS hM
      obtain ⟨rfl, rfl, rfl⟩ := kerElt_eq_of_qr_zero (hq0 _ hhΓ')
      exact ⟨(p', q'), eq_uSL_of_A1⟩
    have hlt : Nat.card ↥Γ' < k * Nat.card ↥(Γ' ⊓ pCoreOf 2 (stabV0 F)) :=
      (card_le_mul_card_inf_R1 hF hn hS hΓ'1).trans_lt
        (Nat.mul_lt_mul_of_pos_right hk1 Nat.card_pos)
    have hfixR := hP' _ inf_le_left hlt
    have hF3 : ∀ γ ∈ Γ', γ ∈ A1 F := fun γ hγ w hw =>
      hfixR w (fun h hh => Z1_le_A1 (hR hh) w hw) γ hγ
    obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ Γ' ⊓ pCoreOf 2 (stabV0 F), z ≠ 1 := by
      by_contra hcon
      apply htriv g⁻¹
      intro w γ hγ
      rw [← hΓ'] at hγ
      refine hfixR w (fun h hh => ?_) γ hγ
      have h1 : h = 1 := by
        by_contra h1
        exact hcon ⟨h, hh, h1⟩
      rw [h1, map_one]
      rfl
    obtain ⟨v₀, hv₀⟩ := hR hz₀
    have hv₀0 : v₀ ≠ 0 := by
      rintro rfl
      apply hz₀1
      rw [hv₀, Prod.fst_zero, Prod.snd_zero,
        CFSG.ClassicalInvolution.ModelFacts.OddCover.uSL_zero, map_one]
    by_cases hall : ∀ h ∈ Γ' ⊓ pCoreOf 2 (stabV0 F), ∀ v : F × F,
        h = g2A (uSL v.1 v.2 0) → v.1 * v₀.2 = v.2 * v₀.1
    ·
      have hw : ∀ γ ∈ Γ', g2Act γ (q6 0 v₀.2 v₀.1 0 0 0) = q6 0 v₀.2 v₀.1 0 0 0 := by
        refine hfixR _ fun h hh => ?_
        obtain ⟨v, hv⟩ := hR hh
        have h1 := hall h hh v hv
        rw [hv, g2Act_g2A_uSL]
        refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_ <;> simp [q6]
        linear_combination h1 + v.2 * v₀.1 * h2
      have hΓ'D : Γ' ≤ rootD (dirV v₀) := by
        intro γ hγ
        obtain ⟨α, p', q', hγeq⟩ := exists_eq_of_mem_A1 (hF3 γ hγ)
        have h1 := hw γ hγ
        rw [hγeq, g2Act_A1] at h1
        obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h1
        have hα : α = 0 := by
          by_contra hα
          apply hv₀0
          exact Prod.ext ((mul_eq_zero.mp (by linear_combination e4)).resolve_left hα)
            ((mul_eq_zero.mp (by linear_combination e5)).resolve_left hα)
        subst hα
        refine ⟨(p', q'), onLine_dirV_of hv₀0 ?_, by rw [hγeq, eq_uSL_of_A1]⟩
        linear_combination e0 - q' * v₀.1 * h2
      apply htriv g⁻¹
      intro w γ hγ
      rw [← hΓ'] at hγ
      refine hP' ⊥ bot_le ?_ w (fun b hb => by rw [Subgroup.mem_bot.mp hb, map_one]; rfl) γ hγ
      rw [Subgroup.card_bot, mul_one]
      exact ((Subgroup.card_le_of_le hΓ'D).trans (card_rootD_le _)).trans_lt hk1
    ·
      obtain ⟨h₁, hh₁, v₁, hv₁, hne⟩ : ∃ h ∈ Γ' ⊓ pCoreOf 2 (stabV0 F), ∃ v : F × F,
          h = g2A (uSL v.1 v.2 0) ∧ v.1 * v₀.2 ≠ v.2 * v₀.1 := by
        by_contra hcon
        apply hall
        intro h hh v hv
        by_contra hne
        exact hcon ⟨h, hh, v, hv, hne⟩
      have hfixF3 : ∀ w, (∀ γ ∈ Γ', g2Act γ w = w) → w ∈ stdF F 3 := by
        intro w hw
        have e₀ := hw _ hz₀.1
        have e₁ := hw _ hh₁.1
        rw [hv₀, g2Act_g2A_uSL] at e₀
        rw [hv₁, g2Act_g2A_uSL] at e₁
        have a0 := congrFun e₀ (.inl 0)
        have a4 := congrFun e₀ (.inr 1)
        have a5 := congrFun e₀ (.inr 2)
        have b0 := congrFun e₁ (.inl 0)
        simp only [q6_apply_inl0, q6_apply_inr1, q6_apply_inr2] at a0 a4 a5 b0
        have hd : w (.inr 0) = 0 := by
          by_contra hd
          apply hv₀0
          exact Prod.ext ((mul_eq_zero.mp (by linear_combination a4)).resolve_right hd)
            ((mul_eq_zero.mp (by linear_combination a5)).resolve_right hd)
        have hdet : v₁.1 * v₀.2 - v₁.2 * v₀.1 ≠ 0 := sub_ne_zero.mpr hne
        have hb : w (.inl 1) = 0 := (mul_eq_zero.mp (show w (.inl 1) *
            (v₁.1 * v₀.2 - v₁.2 * v₀.1) = 0 by
          linear_combination v₀.2 * b0 - v₁.2 * a0)).resolve_right hdet
        have hc : w (.inl 2) = 0 := (mul_eq_zero.mp (show w (.inl 2) *
            (v₁.1 * v₀.2 - v₁.2 * v₀.1) = 0 by
          linear_combination v₁.1 * a0 - v₀.1 * b0)).resolve_right hdet
        exact mem_stdF_three.mpr ⟨hb, hc, hd⟩
      have hZ : Γ' ≤ Z1 F := by
        intro γ hγ
        obtain ⟨α, p', q', hγeq⟩ := exists_eq_of_mem_A1 (hF3 γ hγ)
        have h1 := hq0 γ hγ (q6 0 0 0 1 0 0)
        rw [hγeq, qr_kerElt_v0] at h1
        have hα : α = 0 := mul_self_eq_zero.mp (by linear_combination h1)
        subst hα
        exact ⟨(p', q'), by rw [hγeq, eq_uSL_of_A1]⟩
      have hle2 : Nat.card ↥Γ' ≤ Nat.card F ^ 2 :=
        (Subgroup.card_le_of_le hZ).trans card_Z1_le
      have hB2 : 2 ≤ Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) := by
        have hmem : z₀ ∈ Γ' ⊓ rootD (dirV v₀) := ⟨hz₀.1, v₀, onLine_dirV_self hv₀0, hv₀⟩
        have hne' : Γ' ⊓ rootD (dirV v₀) ≠ ⊥ := fun h => hz₀1 (by
          rw [h] at hmem
          exact Subgroup.mem_bot.mp hmem)
        exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne'
      have hcontra : k * Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) ≤ Nat.card ↥Γ' := by
        by_contra h
        exact rootW_not_mem _ (hfixF3 _ (hP' _ inf_le_left (not_le.mp h) _
          fun b hb => rootD_fix _ hb.2))
      have hΓZ : Γ' = Z1 F := by
        apply Subgroup.eq_of_le_of_card_ge hZ
        calc Nat.card ↥(Z1 F) ≤ Nat.card F ^ 2 := card_Z1_le
          _ ≤ 2 * k := hk2
          _ ≤ k * Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) := by
            rw [mul_comm]
            exact Nat.mul_le_mul_left _ hB2
          _ ≤ Nat.card ↥Γ' := hcontra
      have hmemZ : ∀ t : F, g2A (uSL (t * v₀.1) (t * v₀.2) 0) ∈ Γ' ⊓ rootD (dirV v₀) := by
        intro t
        refine ⟨?_, ⟨(t * v₀.1, t * v₀.2), onLine_dirV_of hv₀0 ?_, rfl⟩⟩
        · rw [hΓZ]
          exact ⟨(t * v₀.1, t * v₀.2), rfl⟩
        · show t * v₀.1 * v₀.2 = t * v₀.2 * v₀.1
          ring
      have hDq : Nat.card F ≤ Nat.card ↥(Γ' ⊓ rootD (dirV v₀)) := by
        have hinj : Function.Injective (fun t : F =>
            (⟨g2A (uSL (t * v₀.1) (t * v₀.2) 0), hmemZ t⟩ : ↥(Γ' ⊓ rootD (dirV v₀)))) := by
          intro t t' h
          have h1 := g2A_uSL_injective (v := (t * v₀.1, t * v₀.2)) (w := (t' * v₀.1, t' * v₀.2))
            (congrArg Subtype.val h)
          obtain ⟨e1, e2⟩ := Prod.mk.inj h1
          by_cases hv : v₀.1 = 0
          · have hv2 : v₀.2 ≠ 0 := fun h0 => hv₀0 (Prod.ext hv h0)
            exact mul_right_cancel₀ hv2 e2
          · exact mul_right_cancel₀ hv e1
        exact Nat.card_le_card_of_injective _ hinj
      have h3 : k * Nat.card F ≤ Nat.card F ^ 2 :=
        (Nat.mul_le_mul_left k hDq).trans (hcontra.trans hle2)
      rw [sq] at h3
      have h4 : k ≤ Nat.card F := Nat.le_of_mul_le_mul_right h3 (by omega)
      omega

theorem eq_conj_A1 [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    {Γ : Subgroup ↥(cayleyGroup F)} (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) (hΓne : Γ ≠ ⊥)
    (hP : FixStable (Nat.card F ^ 2) Γ) :
    ∃ x : ↥(cayleyGroup F), Γ = (A1 F).map (MulAut.conj x).toMonoidHom := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  obtain ⟨x, hle, hfix⟩ := exists_conj_le_A1 hF hn (k := Nat.card F ^ 2)
    (by rw [sq]; exact lt_mul_self hq) (by omega) hΓ1 hΓc hΓne hP
  have hEq := eq_A1_of_le hle hfix (fixStable_map_conj hP x⁻¹)
  refine ⟨x, ?_⟩
  rw [← hEq, map_map_conj_inv]

end CFSG.Quasithin.Vol2.Ch11.G2Q8
