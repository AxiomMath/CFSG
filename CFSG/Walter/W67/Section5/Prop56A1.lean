module

public import CFSG.Walter.W67.Section5.P56Glaub
import CFSG.GroupTheory.Gorenstein.MaxOrderThompson
public import CFSG.Walter.W67.Section5.Prop56N

public section

namespace CFSG.Walter.W67

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec56

omit [Finite G] in
theorem thompsonAbelianSubgroups_eq {R S : Subgroup G} (hRS : R ≤ S)
    (h : ∀ A : Subgroup G, A ≤ S → IsMulCommutative A →
      (∀ B : Subgroup G, B ≤ R → IsMulCommutative B → Nat.card B ≤ Nat.card A) → A ≤ R) :
    thompsonAbelianSubgroups (G := G) S = thompsonAbelianSubgroups (G := G) R := by
  ext A
  constructor
  · rintro ⟨hAS, hAc, hAmax⟩
    refine ⟨h A hAS hAc fun B hBR hBc => hAmax B (hBR.trans hRS) hBc, hAc,
      fun B hBR hBc => hAmax B (hBR.trans hRS) hBc⟩
  · rintro ⟨hAR, hAc, hAmax⟩
    refine ⟨hAR.trans hRS, hAc, fun B hBS hBc => ?_⟩
    by_cases hB : ∀ B' : Subgroup G, B' ≤ R → IsMulCommutative B' → Nat.card B' ≤ Nat.card B
    · exact hAmax B (h B hBS hBc hB) hBc
    · push Not at hB
      obtain ⟨B', hB'R, hB'c, hlt⟩ := hB
      exact hlt.le.trans (hAmax B' hB'R hB'c)

omit [Finite G] in
theorem thompsonSubgroup_eq {R S : Subgroup G} (hRS : R ≤ S)
    (h : ∀ A : Subgroup G, A ≤ S → IsMulCommutative A →
      (∀ B : Subgroup G, B ≤ R → IsMulCommutative B → Nat.card B ≤ Nat.card A) → A ≤ R) :
    thompsonSubgroup (G := G) S = thompsonSubgroup (G := G) R := by
  exact congrArg sSup (thompsonAbelianSubgroups_eq hRS h)

omit [Finite G] in
theorem mem_normalizer_thompsonSubgroup [Finite G] {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer ((thompsonSubgroup (G := G) R : Subgroup G) : Set G) :=
  (Adapters.leanEval_thompsonSubgroup_eq R ▸ Open.normalizer_le_normalizer_thompsonSubgroup R) hg

theorem map_conj_eq {H : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge

theorem mem_normalizer_of_map_conj_le {H : Subgroup G} {g : G}
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) : g ∈ Subgroup.normalizer (H : Set G) :=
  Sec53.mem_normalizer_of_conj_le fun y hy => h ⟨y, hy, rfl⟩

theorem mem_normalizer_commutator {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_conj_le
  rw [Subgroup.map_commutator, map_conj_eq hg]

omit [Finite G] in
theorem map_lpc_one (H : Subgroup G) :
    (lpc 3 H 1).map H.subtype =
      ⁅H, H⁆ ⊔ Subgroup.closure ((fun n : G => n ^ 3) '' (H : Set G)) := by
  rw [lpc_succ, lpc_zero, lpcStep, Subgroup.map_sup, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, MonoidHom.map_closure, Set.image_image]
  congr 2
  ext y
  simp

omit [Finite G] in
theorem isMulCommutative_sup {H K : Subgroup G} (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hHK : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) :
    IsMulCommutative (H ⊔ K : Subgroup G) := by
  have hKN : K ≤ Subgroup.normalizer (H : Set G) := fun k hk =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh =>
      hHK h hh k hk)
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  obtain ⟨h₁, hh₁, k₁, hk₁, hx⟩ := (mem_sup_iff_of_le_normalizer hKN).mp x.2
  obtain ⟨h₂, hh₂, k₂, hk₂, hy⟩ := (mem_sup_iff_of_le_normalizer hKN).mp y.2
  simp only [Subgroup.coe_mul]
  rw [← hx, ← hy]
  calc h₁ * k₁ * (h₂ * k₂) = (h₁ * h₂) * (k₁ * k₂) := by
        rw [mul_assoc, ← mul_assoc k₁, ← hHK h₂ hh₂ k₁ hk₁]; group
    _ = (h₂ * h₁) * (k₂ * k₁) := by rw [hH h₁ hh₁ h₂ hh₂, hK k₁ hk₁ k₂ hk₂]
    _ = h₂ * k₂ * (h₁ * k₁) := by
        rw [mul_assoc, ← mul_assoc h₁, hHK h₁ hh₁ k₂ hk₂]; group

end Sec56

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

structure RData (R : Subgroup G) : Prop where
  isPGroup : IsPGroup 3 R
  le_centralizer : R ≤ Subgroup.centralizer (f5.P₁ : Set G)
  P₁_le : f5.P₁ ≤ R
  normalizer : s.H ⊓ Subgroup.normalizer (f5.P₁ : Set G) ≤ Subgroup.normalizer (R : Set G)
  max : ∀ Q : Subgroup G, IsPGroup 3 Q → Q ≤ Subgroup.centralizer (f5.P₁ : Set G) →
    Nat.card Q ≤ Nat.card R

theorem card_P₁_eq : Nat.card f5.P₁ = s.q ^ 1 := by rw [pow_one, f5.card_P₁]

omit f5 in
theorem _root_.CFSG.Walter.W67.Std.one_lt_q (s : Std G) : 1 < s.q := by
  have := s.three_lt_q
  omega

variable {f5}

namespace RData

variable {R : Subgroup G} (hR : f5.RData R)
include hR

theorem JBE_le : f5.JBE ≤ Subgroup.normalizer (R : Set G) := fun _ hg =>
  hR.normalizer ⟨f5.JBE_le_H hg, f5.JBE_le_normalizer_P₁ hg⟩

theorem B_le : f5.B ≤ Subgroup.normalizer (R : Set G) := fun _ hb =>
  hR.JBE_le (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))

theorem E_le : s.fr.E ≤ Subgroup.normalizer (R : Set G) := fun _ he =>
  hR.JBE_le (Subgroup.mem_sup_right he)

theorem P₁_le_centralizer : f5.P₁ ≤ Subgroup.centralizer (R : Set G) := fun u hu =>
  Subgroup.mem_centralizer_iff.mpr fun _ hr =>
    (Subgroup.mem_centralizer_iff.mp (hR.le_centralizer hr) u hu).symm

theorem card_eq_q_pow
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    {Q : Subgroup G} (hQR : Q ≤ R) (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) : ∃ k, Nat.card Q = s.q ^ k :=
  f5.card_eq_q_pow hp (hR.isPGroup.to_le hQR) hBQ
    (f5.fpf_of_isPGroup h22 h26i hp (hR.isPGroup.to_le hQR) hBQ hEQ)

theorem eq_P₁_of_lt
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hRq : Nat.card R = s.q ^ 2) {Q : Subgroup G} (hP₁Q : f5.P₁ ≤ Q) (hQR : Q < R)
    (hBQ : f5.B ≤ Subgroup.normalizer (Q : Set G))
    (hEQ : s.fr.E ≤ Subgroup.normalizer (Q : Set G)) : Q = f5.P₁ := by
  obtain ⟨k, hk⟩ := hR.card_eq_q_pow h22 h26i hp hQR.le hBQ hEQ
  have h1 := Subgroup.card_le_of_le hP₁Q
  have h2 := Subgroup.card_lt_of_lt hQR
  rw [f5.card_P₁_eq, hk] at h1
  rw [hk, hRq] at h2
  have hq := s.one_lt_q
  have hk1 : 1 ≤ k := (Nat.pow_le_pow_iff_right hq).mp h1
  have hk2 : k < 2 := (Nat.pow_lt_pow_iff_right hq).mp h2
  have hk' : k = 1 := by omega
  symm
  apply Subgroup.eq_of_le_of_card_ge hP₁Q
  rw [hk, hk', pow_one, f5.card_P₁]

theorem Z_eq
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hRq : Nat.card R = s.q ^ 2) (hRna : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) :
    R ⊓ Subgroup.centralizer (R : Set G) = f5.P₁ := by
  apply hR.eq_P₁_of_lt h22 h26i hp hRq (le_inf hR.P₁_le hR.P₁_le_centralizer)
  · refine lt_of_le_of_ne inf_le_left fun h => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := hRna
    apply hab
    have hb' : b ∈ R ⊓ Subgroup.centralizer (R : Set G) := by rw [h]; exact hb
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb').2 a ha)
  · exact fun b hb => Sec54.mem_normalizer_inf (hR.B_le hb)
      (Sec54.mem_normalizer_centralizer (hR.B_le hb))
  · exact fun e he => Sec54.mem_normalizer_inf (hR.E_le he)
      (Sec54.mem_normalizer_centralizer (hR.E_le he))

theorem commutator_eq
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hRq : Nat.card R = s.q ^ 2) (hRna : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) :
    ⁅R, R⁆ = f5.P₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := hR.Z_eq h22 h26i hp hRq hRna
  have hDR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
  have hBD : f5.B ≤ Subgroup.normalizer ((⁅R, R⁆ : Subgroup G) : Set G) := fun b hb =>
    Sec56.mem_normalizer_commutator (hR.B_le hb)
  have hED : s.fr.E ≤ Subgroup.normalizer ((⁅R, R⁆ : Subgroup G) : Set G) := fun e he =>
    Sec56.mem_normalizer_commutator (hR.E_le he)
  have hD1 : ⁅R, R⁆ ⊓ f5.P₁ ≠ ⊥ := by
    have : Group.IsNilpotent R := hR.isPGroup.isNilpotent
    have hDn : (⁅R, R⁆.subgroupOf R).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDR).mpr fun g hg =>
        Sec56.mem_normalizer_commutator (Subgroup.le_normalizer hg)
    have hD0 : ⁅R, R⁆.subgroupOf R ≠ ⊥ := by
      obtain ⟨a, ha, b, hb, hab⟩ := hRna
      intro h
      have hc : (⟨⁅a, b⁆, hDR (Subgroup.commutator_mem_commutator ha hb)⟩ : R) ∈
          ⁅R, R⁆.subgroupOf R := Subgroup.commutator_mem_commutator ha hb
      rw [h, Subgroup.mem_bot] at hc
      apply hab
      have h1 : ⁅a, b⁆ = 1 := congrArg Subtype.val hc
      rw [commutatorElement_def] at h1
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hD0
    obtain ⟨z, hz, hz1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hc
    obtain ⟨hzD, hzZ⟩ := Subgroup.mem_inf.mp hz
    intro hbot
    apply hz1
    have hzP : (z : G) ∈ f5.P₁ := by
      rw [← hZ]
      refine Subgroup.mem_inf.mpr ⟨z.2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have := Subgroup.mem_center_iff.mp hzZ ⟨r, hr⟩
      exact congrArg Subtype.val this
    have : (z : G) ∈ ⁅R, R⁆ ⊓ f5.P₁ := Subgroup.mem_inf.mpr ⟨hzD, hzP⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hP₁D : f5.P₁ ≤ ⁅R, R⁆ := by
    obtain ⟨k, hk⟩ := hR.card_eq_q_pow h22 h26i hp (inf_le_left.trans hDR)
      (fun b hb => Sec54.mem_normalizer_inf (hBD hb) (f5.B_le_normalizer_P₁ hb))
      (fun e he => Sec54.mem_normalizer_inf (hED he) (f5.E_le_normalizer_P₁ he))
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hD1 (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
    have h1 := Subgroup.card_le_of_le (inf_le_right : ⁅R, R⁆ ⊓ f5.P₁ ≤ f5.P₁)
    rw [hk, f5.card_P₁_eq] at h1
    have hk1 : k ≤ 1 := (Nat.pow_le_pow_iff_right s.one_lt_q).mp h1
    have heq : ⁅R, R⁆ ⊓ f5.P₁ = f5.P₁ := Subgroup.eq_of_le_of_card_ge inf_le_right (by
      rw [hk, f5.card_P₁_eq]
      exact Nat.pow_le_pow_right (by have := s.one_lt_q; omega) (by omega))
    rw [← heq]
    exact inf_le_left
  have hDlt : ⁅R, R⁆ < R := by
    refine lt_of_le_of_ne hDR fun h => ?_
    have hc : commutator R = ⊤ := by
      apply Subgroup.map_injective R.subtype_injective
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, h]
    have h1 := Sec56.eq_bot_of_commutator_eq_top hR.isPGroup hc
    apply f5.P₁_ne_bot
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hR.P₁_le hu⟩ : R) ∈ (⊤ : Subgroup R) := Subgroup.mem_top _
    rw [h1, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  exact hR.eq_P₁_of_lt h22 h26i hp hRq hP₁D hDlt hBD hED

theorem lpc_one_eq
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hRq : Nat.card R = s.q ^ 2) (hRna : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) :
    (Sec56.lpc 3 R 1).map R.subtype = f5.P₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := hR.commutator_eq h22 h26i hp hRq hRna
  rw [Sec56.map_lpc_one]
  set L := ⁅R, R⁆ ⊔ Subgroup.closure ((fun n : G => n ^ 3) '' (R : Set G)) with hLdef
  have hLR : L ≤ R := sup_le (hc ▸ hR.P₁_le)
    ((Subgroup.closure_le R).mpr (by rintro _ ⟨n, hn, rfl⟩; exact R.pow_mem hn 3))
  have hLN : ∀ g ∈ Subgroup.normalizer (R : Set G), g ∈ Subgroup.normalizer (L : Set G) := by
    intro g hg
    apply Sec56.mem_normalizer_of_map_conj_le
    rw [hLdef, Subgroup.map_sup, Subgroup.map_commutator, Sec56.map_conj_eq hg,
      MonoidHom.map_closure, Set.image_image]
    refine sup_le le_sup_left (le_sup_of_le_right (Subgroup.closure_mono ?_))
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨g * n * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg n).mp hn, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_pow
  have hLlt : L < R := by
    refine lt_of_le_of_ne hLR fun h => ?_
    have hlpc : Sec56.lpcStep 3 (⊤ : Subgroup R) = ⊤ := by
      apply Subgroup.map_injective R.subtype_injective
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have := Sec56.map_lpc_one R
      rw [Sec56.lpc_succ, Sec56.lpc_zero] at this
      rw [this, ← hLdef, h]
    have h1 := Sec56.eq_bot_of_lpcStep_eq _ R rfl hR.isPGroup ⊤ inferInstance hlpc
    apply f5.P₁_ne_bot
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hR.P₁_le hu⟩ : R) ∈ (⊤ : Subgroup R) := Subgroup.mem_top _
    rw [h1, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  exact hR.eq_P₁_of_lt h22 h26i hp hRq (hc ▸ le_sup_left) hLlt (fun b hb => hLN b (hR.B_le hb))
    (fun e he => hLN e (hR.E_le he))

theorem card_lt_of_not_le
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (hRq : Nat.card R = s.q ^ 2) (hRna : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a)
    {P₀ : Subgroup G} (hP₀E : P₀ ≤ s.fr.E) (hP₀3 : IsPGroup 3 P₀) {A : Subgroup G}
    (hA : A ≤ R ⊔ P₀) (hAc : IsMulCommutative A) (hAR : ¬ A ≤ R) : Nat.card A < s.q * 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRc := hR.commutator_eq h22 h26i hp hRq hRna
  have hL := hR.lpc_one_eq h22 h26i hp hRq hRna
  have hP₀N : P₀ ≤ Subgroup.normalizer (R : Set G) := hP₀E.trans hR.E_le
  obtain ⟨a₀, ha₀A, ha₀R⟩ := Set.not_subset.mp hAR
  obtain ⟨r₀, hr₀, y₀, hy₀, rfl⟩ := (mem_sup_iff_of_le_normalizer hP₀N).mp (hA ha₀A)
  have hy₀1 : y₀ ≠ 1 := by
    rintro rfl
    exact ha₀R (by rw [mul_one]; exact hr₀)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP₀3
  have hoy : orderOf y₀ ∣ 3 ^ k := hk ▸ Subgroup.orderOf_dvd_natCard P₀ hy₀
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hoy
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hy₀1 (orderOf_eq_one_iff.mp (by rw [hj, pow_zero]))
  set m := 3 ^ (j - 1) with hm
  set x := y₀ ^ m with hxdef
  have hox : orderOf x = 3 := by
    rw [hxdef, orderOf_pow_of_dvd (by positivity) (hj ▸ Nat.pow_dvd_pow 3 (Nat.sub_le j 1)), hj,
      hm, Nat.pow_div (Nat.sub_le j 1) (by norm_num),
      Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hj0), pow_one]
  have hxE : x ∈ s.fr.E := hP₀E (P₀.pow_mem hy₀ m)
  have hpow : ∀ i : ℕ, ∃ r ∈ R, (r₀ * y₀) ^ i = r * y₀ ^ i := by
    intro i
    induction i with
    | zero => exact ⟨1, R.one_mem, by simp⟩
    | succ i ih =>
      obtain ⟨r, hr, hri⟩ := ih
      refine ⟨r * (y₀ ^ i * r₀ * (y₀ ^ i)⁻¹), R.mul_mem hr
        ((Subgroup.mem_normalizer_iff.mp (hP₀N (P₀.pow_mem hy₀ i)) r₀).mp hr₀), ?_⟩
      rw [pow_succ, hri]
      group
  obtain ⟨r, hr, hry⟩ := hpow m
  set y := (r₀ * y₀) ^ m with hydef
  have hyA : y ∈ A := A.pow_mem ha₀A m
  have hlift := (f5.card_inf_centralizer_pow_three_and_lift h22 h26i hp hR.isPGroup hR.B_le
    hR.E_le hxE hox).2 0
  have hR0 : (Sec56.lpc 3 R 0).map R.subtype = R := by
    rw [Sec56.lpc_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hR0, hL] at hlift
  set C := A ⊓ R with hCdef
  set Cx := R ⊓ Subgroup.centralizer ({x} : Set G) with hCxdef
  have hcomm : ∀ c ∈ C, c * y = y * c := fun c hc =>
    congrArg Subtype.val (hAc.is_comm.comm ⟨c, (Subgroup.mem_inf.mp hc).1⟩ ⟨y, hyA⟩)
  have hCle : C ≤ Cx ⊔ f5.P₁ := by
    intro c hc
    have hcR : c ∈ R := (Subgroup.mem_inf.mp hc).2
    have h1 : c * (r * x) = (r * x) * c := by rw [← hry]; exact hcomm c hc
    have h2 : c⁻¹ * (x * c * x⁻¹) ∈ f5.P₁ := by
      have h3 : x * c * x⁻¹ = r⁻¹ * c * r := by
        calc x * c * x⁻¹ = r⁻¹ * ((r * x) * c) * x⁻¹ := by group
          _ = r⁻¹ * (c * (r * x)) * x⁻¹ := by rw [h1]
          _ = r⁻¹ * c * r := by group
      rw [h3, ← hRc]
      have : c⁻¹ * (r⁻¹ * c * r) = ⁅c⁻¹, r⁻¹⁆ := by rw [commutatorElement_def]; group
      rw [this]
      exact Subgroup.commutator_mem_commutator (R.inv_mem hcR) (R.inv_mem hr)
    obtain ⟨a', ha', hxa, b, hb, rfl⟩ := hlift c hcR h2
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨ha', ?_⟩))
      (Subgroup.mem_sup_right hb)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxa.symm
  have hCP : f5.P₁ ⊓ C ≤ f5.P₁ ⊓ Cx := by
    intro c hc
    obtain ⟨hcP, hcC⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨hcP, Subgroup.mem_inf.mpr ⟨hR.P₁_le hcP, ?_⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c * (r * x) = (r * x) * c := by rw [← hry]; exact hcomm c hcC
    have h2 : c * r = r * c :=
      (Subgroup.mem_centralizer_iff.mp (hR.P₁_le_centralizer hcP) r hr).symm
    have h3 : r * (c * x) = r * (x * c) := by
      calc r * (c * x) = (c * r) * x := by rw [h2]; group
        _ = c * (r * x) := by group
        _ = r * x * c := h1
        _ = r * (x * c) := by group
    exact mul_left_cancel h3
  have hCN : C ≤ Subgroup.normalizer (f5.P₁ : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hR.P₁_le_centralizer hu) c
        (Subgroup.mem_inf.mp hc).2).symm)
  have hCxN : Cx ≤ Subgroup.normalizer (f5.P₁ : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hR.P₁_le_centralizer hu) c
        (Subgroup.mem_inf.mp hc).1).symm)
  have e1 := Sec52.card_sup_mul_card_inf hCN
  have e2 := Sec52.card_sup_mul_card_inf hCxN
  have i1 : Nat.card (C ⊔ f5.P₁ : Subgroup G) ≤ Nat.card (Cx ⊔ f5.P₁ : Subgroup G) :=
    Subgroup.card_le_of_le (sup_le hCle le_sup_right)
  have i2 := Subgroup.card_le_of_le hCP
  have hP₁pos : 0 < Nat.card f5.P₁ := Nat.card_pos
  have hCcard : Nat.card C ≤ Nat.card Cx := by
    have : Nat.card f5.P₁ * Nat.card C ≤ Nat.card f5.P₁ * Nat.card Cx := by
      rw [← e1, ← e2]
      exact Nat.mul_le_mul i1 i2
    exact Nat.le_of_mul_le_mul_left this hP₁pos
  have h3 := f5.card_inf_centralizer_pow_three h22 h26i hp hR.isPGroup hR.B_le hR.E_le hxE hox
  obtain ⟨t, ht⟩ := IsPGroup.iff_card.mp (hR.isPGroup.to_le (inf_le_left : Cx ≤ R))
  rw [← hCxdef, ht, hRq, Hyp.q, hp, ← pow_mul, ← pow_mul] at h3
  have h3' := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
  have hAN : A ≤ Subgroup.normalizer (R : Set G) :=
    hA.trans (sup_le Subgroup.le_normalizer hP₀N)
  have e3 := Sec52.card_sup_mul_card_inf hAN
  have e4 := Sec52.card_sup_mul_card_inf hP₀N
  have i3 : Nat.card (A ⊔ R : Subgroup G) ≤ Nat.card (P₀ ⊔ R : Subgroup G) :=
    Subgroup.card_le_of_le (sup_le (hA.trans (le_of_eq (sup_comm _ _))) le_sup_right)
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hinf1 : 0 < Nat.card (R ⊓ P₀ : Subgroup G) := Nat.card_pos
  have hAcard : Nat.card A ≤ Nat.card P₀ * Nat.card C := by
    have : Nat.card R * Nat.card A ≤ Nat.card R * (Nat.card P₀ * Nat.card C) := by
      rw [← e3, show (R ⊓ A : Subgroup G) = C from inf_comm _ _]
      calc Nat.card (A ⊔ R : Subgroup G) * Nat.card C
          ≤ Nat.card (P₀ ⊔ R : Subgroup G) * Nat.card C := Nat.mul_le_mul_right _ i3
        _ ≤ Nat.card (P₀ ⊔ R : Subgroup G) * Nat.card (R ⊓ P₀ : Subgroup G) * Nat.card C :=
            Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hinf1)
        _ = Nat.card R * (Nat.card P₀ * Nat.card C) := by rw [e4, mul_assoc]
    exact Nat.le_of_mul_le_mul_left this hRpos
  have h3k := three_mul_le_f h26i hP₀E hk
  rw [hk] at hAcard
  have hfin : Nat.card A ≤ 3 ^ s.f := by
    calc Nat.card A ≤ 3 ^ k * Nat.card C := hAcard
      _ ≤ 3 ^ k * 3 ^ t := Nat.mul_le_mul_left _ (hCcard.trans (le_of_eq ht))
      _ = 3 ^ (k + t) := by rw [pow_add]
      _ ≤ 3 ^ s.f := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Hyp.q, hp]
  calc Nat.card A ≤ 3 ^ s.f := hfin
    _ < 3 ^ s.f * 3 := by
      have : 0 < 3 ^ s.f := by positivity
      omega

open Sec52 in
theorem false_of_nonabelian
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) (hp : s.p = 3)
    (h3 : 3 ∣ Nat.card s.fr.E) (hRq : Nat.card R = s.q ^ 2)
    (hRna : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h54 := lemma_5_4_of h22 h26i
  have hN := h54 G s hp f5 f5.P₁ (f5.isElementaryAbelian_P₁ hp) f5.P₁_ne_bot
    f5.JBE_le_normalizer_P₁ f5.irred_JBE
  have hZ := hR.Z_eq h22 h26i hp hRq hRna
  have hq1 := s.one_lt_q
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 s.fr.E) := inferInstance
  set P₀ := (S₀ : Subgroup s.fr.E).map s.fr.E.subtype with hP₀def
  have hP₀E : P₀ ≤ s.fr.E := Subgroup.map_subtype_le _
  have hP₀3 : IsPGroup 3 P₀ := S₀.isPGroup'.map _
  set a := (Nat.card s.fr.E).factorization 3 with ha
  have hP₀card : Nat.card P₀ = 3 ^ a := by
    rw [hP₀def, Subgroup.card_map_of_injective s.fr.E.subtype_injective,
      Sylow.card_eq_multiplicity]
  have hapos : 0 < a := Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3
  have hP₀N : P₀ ≤ Subgroup.normalizer (R : Set G) := hP₀E.trans hR.E_le
  have hinf : R ⊓ P₀ = ⊥ := by
    have := f5.inf_E_eq_bot h26i hp hR.isPGroup hR.B_le
    rw [eq_bot_iff, ← this]
    exact inf_le_inf_left _ hP₀E
  set S := R ⊔ P₀ with hSdef
  have hScard : Nat.card S = Nat.card R * 3 ^ a := by
    rw [hSdef, Sec54.card_sup_eq_mul hP₀N hinf, hP₀card]
  have hS3 : IsPGroup 3 S := IsPGroup.of_card (n := 2 * s.f + a) (by
    rw [hScard, hRq, Hyp.q, hp, ← pow_mul, ← pow_add, mul_comm])
  have hSN : S ≤ Subgroup.normalizer (R : Set G) := sup_le Subgroup.le_normalizer hP₀N
  obtain ⟨v, hvR, hvP⟩ : ∃ v ∈ R, v ∉ f5.P₁ := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show R ≤ f5.P₁ from h)
    rw [hRq, f5.card_P₁] at this
    nlinarith
  have hP₁c : ∀ a ∈ f5.P₁, ∀ b ∈ f5.P₁, a * b = b * a := f5.P₁_comm
  set B₀ := f5.P₁ ⊔ Subgroup.zpowers v with hB₀def
  have hB₀c : IsMulCommutative B₀ := Sec56.isMulCommutative_sup hP₁c
    (fun a ha b hb => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_add, ← zpow_add, add_comm])
    (fun a ha b hb => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((Commute.zpow_right (show Commute a v from
        (Subgroup.mem_centralizer_iff.mp (hR.P₁_le_centralizer ha) v hvR).symm) j)).eq)
  have hB₀R : B₀ ≤ R := sup_le hR.P₁_le (Subgroup.zpowers_le.mpr hvR)
  have hB₀card : s.q * 3 ≤ Nat.card B₀ := by
    have hlt : f5.P₁ < B₀ := lt_of_le_of_ne le_sup_left fun h =>
      hvP (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hR.isPGroup.to_le hB₀R)
    have h1 := Subgroup.card_lt_of_lt hlt
    rw [f5.card_P₁, Hyp.q, hp, hm] at h1
    have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h1
    rw [hm, Hyp.q, hp, ← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) h2
  have hbig : ∀ A : Subgroup G, A ≤ S → IsMulCommutative A →
      (∀ B : Subgroup G, B ≤ R → IsMulCommutative B → Nat.card B ≤ Nat.card A) → A ≤ R := by
    intro A hAS hAc hAmax
    by_contra hAR
    have h1 := hR.card_lt_of_not_le h22 h26i hp hRq hRna hP₀E hP₀3 hAS hAc hAR
    have h2 := hAmax B₀ hB₀R hB₀c
    omega
  have hJS := Sec56.thompsonSubgroup_eq le_sup_left hbig
  have hJRle : thompsonSubgroup (G := G) R ≤ R := sSup_le fun A hA => hA.1
  obtain ⟨A₁, ⟨hA₁R, hA₁c⟩, hA₁max⟩ := Set.exists_max_image
    {A : Subgroup G | A ≤ R ∧ IsMulCommutative A} (fun A => Nat.card A) (Set.toFinite _)
    ⟨⊥, bot_le, inferInstance⟩
  have hA₁T : A₁ ∈ thompsonAbelianSubgroups (G := G) R :=
    ⟨hA₁R, hA₁c, fun B hBR hBc => hA₁max B ⟨hBR, hBc⟩⟩
  have hA₁J : A₁ ≤ thompsonSubgroup (G := G) R := le_sSup hA₁T
  have hP₁A₁ : f5.P₁ ≤ A₁ := by
    have hc : IsMulCommutative (A₁ ⊔ f5.P₁ : Subgroup G) := Sec56.isMulCommutative_sup
      (fun a ha b hb => congrArg Subtype.val (hA₁c.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hP₁c
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hR.P₁_le_centralizer hb) a
        (hA₁R ha)))
    have h1 := hA₁max (A₁ ⊔ f5.P₁) ⟨sup_le hA₁R hR.P₁_le, hc⟩
    have h2 : A₁ = A₁ ⊔ f5.P₁ := Subgroup.eq_of_le_of_card_ge le_sup_left h1
    rw [h2]
    exact le_sup_right
  have hJR : thompsonSubgroup (G := G) R = R := by
    obtain ⟨k, hk⟩ := hR.card_eq_q_pow h22 h26i hp hJRle
      (fun b hb => Sec56.mem_normalizer_thompsonSubgroup (hR.B_le hb))
      (fun e he => Sec56.mem_normalizer_thompsonSubgroup (hR.E_le he))
    have h1 := Subgroup.card_le_of_le hJRle
    rw [hk, hRq] at h1
    have h2 : s.q * 3 ≤ Nat.card (thompsonSubgroup (G := G) R) :=
      hB₀card.trans ((hA₁max B₀ ⟨hB₀R, hB₀c⟩).trans (Subgroup.card_le_of_le hA₁J))
    rw [hk] at h2
    have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right hq1).mp h1
    have hk1 : 1 < k := by
      by_contra hk1
      push Not at hk1
      have : s.q ^ k ≤ s.q ^ 1 := Nat.pow_le_pow_right (by omega) hk1
      rw [pow_one] at this
      omega
    apply Subgroup.eq_of_le_of_card_ge hJRle
    rw [hRq, hk, show k = 2 by omega]
  have hZJ : Glauberman.ZJ (G := G) S = f5.P₁ := by
    change centerIn (G := G) (thompsonSubgroup (G := G) S) = f5.P₁
    rw [hJS, hJR, centerIn]
    exact hZ
  have hNRP : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (f5.P₁ : Set G) := by
    intro g hg
    rw [← hZ]
    exact Sec54.mem_normalizer_inf hg (Sec54.mem_normalizer_centralizer hg)
  have hQmax : ∀ Q' : Subgroup G, IsPGroup 3 Q' → S ≤ Q' →
      Q' ≤ Subgroup.normalizer (R : Set G) → Q' ≤ S := by
    intro Q' hQ' hSQ' hQ'N
    have h1 := f5.card_le_of_le_normalizer hp hN hQ' (hQ'N.trans hNRP)
    have h2 := hR.max _ (hQ'.to_le inf_le_left) inf_le_right
    have hle : Nat.card Q' ≤ Nat.card S := by
      rw [hScard]
      calc Nat.card Q' ≤ 3 ^ a * Nat.card (Q' ⊓ Subgroup.centralizer (f5.P₁ : Set G) :
            Subgroup G) := h1
        _ ≤ 3 ^ a * Nat.card R := Nat.mul_le_mul_left _ h2
        _ = Nat.card R * 3 ^ a := mul_comm _ _
    exact (Subgroup.eq_of_le_of_card_ge hSQ' hle).ge
  have hweak : ∀ g : G, (∀ w ∈ R, g * w * g⁻¹ ∈ S) → ∀ w ∈ R, g * w * g⁻¹ ∈ R := by
    intro g hg
    have hRgS : R.map (MulAut.conj g).toMonoidHom ≤ S := by
      rintro _ ⟨w, hw, rfl⟩
      exact hg w hw
    have hJg : thompsonSubgroup (G := G) (R.map (MulAut.conj g).toMonoidHom) ≤ R := by
      refine sSup_le fun A hA => ?_
      obtain ⟨hAR', hAc, hAmax⟩ := hA
      refine hbig A (hAR'.trans hRgS) hAc fun B hBR hBc => ?_
      have hBg : IsMulCommutative (B.map (MulAut.conj g).toMonoidHom) := by
        refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
        obtain ⟨x', hx', hxx⟩ := x.2
        obtain ⟨y', hy', hyy⟩ := y.2
        simp only [Subgroup.coe_mul]
        rw [← hxx, ← hyy, ← map_mul, ← map_mul]
        congr 1
        exact congrArg Subtype.val (hBc.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
      have := hAmax _ (Subgroup.map_mono hBR) hBg
      rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at this
    rw [← Adapters.thompsonSubgroup_map_mulEquiv, hJR] at hJg
    intro w hw
    exact hJg ⟨w, hw, rfl⟩
  let P : Sylow 3 G := ⟨S, hS3, fun hS' hle =>
    Sec56.eq_of_le_of_weaklyClosed le_sup_left hSN hQmax hweak hS' hle⟩
  have hres := Sec56.hallPResidual_normalizer_ZJ_eq s.perfect s.abelian_sylow P
  change (BenderSuzuki.External.hallPResidual 3 (Subgroup.normalizer
      ((Glauberman.ZJ (G := G) S : Subgroup G) : Set G))).map _ = _ at hres
  rw [hZJ] at hres
  have h3P₀ : 3 ∣ Nat.card P₀ := by
    rw [hP₀card]
    exact dvd_pow_self 3 hapos.ne'
  obtain ⟨⟨x, hxP₀⟩, hox⟩ := exists_prime_orderOf_dvd_card' (G := P₀) 3 h3P₀
  rw [Subgroup.orderOf_mk] at hox
  have hxE : x ∈ s.fr.E := hP₀E hxP₀
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hox
    norm_num at hox
  apply Frame5.not_mem_hallPResidual h54 hp f5 (f5.isElementaryAbelian_P₁ hp) f5.P₁_ne_bot
    f5.JBE_le_normalizer_P₁ f5.irred_JBE f5.fpf_P₁ hxE hox (f5.exists_not_comm_B h26i hxE hx1)
  rw [hres]
  exact f5.E_le_normalizer_P₁ hxE

end RData

end Frame5

end CFSG.Walter.W67
