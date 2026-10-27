module

public import CFSG.Walter.W67.Section5.Prop52

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec56

theorem eq_of_le_of_weaklyClosed {p : ℕ} [Fact p.Prime] {W Q : Subgroup G} (hWQ : W ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (W : Set G))
    (hQmax : ∀ Q' : Subgroup G, IsPGroup p Q' → Q ≤ Q' →
      Q' ≤ Subgroup.normalizer (W : Set G) → Q' ≤ Q)
    (hweak : ∀ g : G, (∀ w ∈ W, g * w * g⁻¹ ∈ Q) → ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    {S : Subgroup G} (hS : IsPGroup p S) (hQS : Q ≤ S) : S = Q := by
  by_contra hne
  have hlt : Q.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    apply le_antisymm _ hQS
    intro y hy
    have : (⟨y, hy⟩ : S) ∈ Q.subgroupOf S := by rw [h]; exact Subgroup.mem_top _
    exact this
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := S) _ hlt
  obtain ⟨⟨g, hgS⟩, hgN, hgQ⟩ := IsConcreteLE.exists_of_lt hnc
  have hgNQ : ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.mp hgN ⟨y, hQS hy⟩).mp hy
    exact this
  have hgW : g ∈ Subgroup.normalizer (W : Set G) :=
    Sec53.mem_normalizer_of_conj_le (hweak g fun w hw => hgNQ w (hWQ hw))
  have hgQN : g ∈ Subgroup.normalizer (Q : Set G) := Sec53.mem_normalizer_of_conj_le hgNQ
  have hp : IsPGroup p (Q ⊔ Subgroup.zpowers g : Subgroup G) :=
    hS.to_le (sup_le hQS (Subgroup.zpowers_le.mpr hgS))
  have hle := hQmax _ hp le_sup_left (sup_le hQN (Subgroup.zpowers_le.mpr hgW))
  exact hgQ (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers g)))

theorem hallPResidual_normalizer_eq (hperf : commutator G = ⊤) (P : Sylow 3 G) {W : Subgroup G}
    (hweak : BenderSuzuki.External.WeaklyClosedIn (P : Subgroup G) W)
    (hab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) :
    (BenderSuzuki.External.hallPResidual 3 (Subgroup.normalizer (W : Set G))).map
      (Subgroup.normalizer (W : Set G)).subtype = Subgroup.normalizer (W : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hengel : ∀ u z : G, u ∈ W → z ∈ W →
      BenderSuzuki.External.engelSymbol (3 - 1) u z = 1 :=
    fun u z hu hz => Sec52.iterated_eq_one (hab u hu z hz) 0
  have hHW := BenderSuzuki.External.hallWielandt_residual_intersection 3 P W
    (Subgroup.normalizer (W : Set G)) rfl hweak (Or.inr (Or.inl hengel))
  rw [hHW.1, Sec52.hallPResidual_eq_top hperf, inf_top_eq]

end Sec56

namespace Frame5

variable {s : Std G}

noncomputable abbrev JBE (f5 : Frame5 s) : Subgroup G := Subgroup.zpowers s.J ⊔ f5.B ⊔ s.fr.E

open Sec52 in
theorem exists_not_comm_B (h26i : S_lemma_2_6_i) (f5 : Frame5 s) {y : G} (hy : y ∈ s.fr.E)
    (hy1 : y ≠ 1) : ∃ b ∈ f5.B, y * b ≠ b * y := by
  by_contra h
  push Not at h
  set Y := Subgroup.zpowers y with hYdef
  have hYE : Y ≤ s.fr.E := Subgroup.zpowers_le.mpr hy
  have hY1 : Y ≠ ⊥ := by
    intro h1
    apply hy1
    have : y ∈ Y := Subgroup.mem_zpowers y
    rwa [h1, Subgroup.mem_bot] at this
  have heX : s.eX Y = Nat.card Y := by
    rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]
  obtain ⟨hediv, ⟨eKY⟩, -⟩ := h26i G s.toHyp s.fr hYE hY1
  rw [heX] at hediv
  have hY3 : 3 ≤ Nat.card Y := by
    have hodd : Odd (Nat.card Y) := Odd.of_dvd_nat s.fr.odd_card_E (Subgroup.card_dvd_of_le hYE)
    have hne : Nat.card Y ≠ 1 := fun h1 => hY1 (Subgroup.eq_bot_of_card_eq Y h1)
    obtain ⟨k, hk⟩ := hodd
    omega
  set f' := s.f / s.eX Y with hf'
  have hf'eq : f' = s.f / Nat.card Y := by rw [hf', heX]
  have hf'pos : 0 < f' := by
    rw [hf'eq]
    exact Nat.div_pos (Nat.le_of_dvd s.f_pos hediv) (by omega)
  have h3f : 3 * f' ≤ s.f := by
    rw [hf'eq]
    calc 3 * (s.f / Nat.card Y) ≤ Nat.card Y * (s.f / Nat.card Y) :=
          Nat.mul_le_mul_right _ hY3
      _ = s.f := Nat.mul_div_cancel' hediv
  have hBK : f5.B ≤ s.KX Y := by
    intro b hb
    refine Subgroup.mem_inf.mpr ⟨f5.B_le hb, ?_⟩
    rw [hYdef, centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
    exact (h b hb).symm
  have hdvd := Subgroup.card_dvd_of_le hBK
  have hFcard : Nat.card (GaloisField s.p f') = s.p ^ f' := GaloisField.card _ _ hf'pos.ne'
  rw [Nat.card_congr eKY.toEquiv, psl2_card_formula _ ⟨s.p, f', Fact.out, s.odd_p, hf'pos,
    hFcard⟩, hFcard] at hdvd
  have hle := Nat.le_of_dvd (by
    have hp2 : 2 ≤ s.p := (Fact.out : s.p.Prime).two_le
    have h1 : 1 < s.p ^ f' := Nat.one_lt_pow hf'pos.ne' (by omega)
    have h2 : s.p ^ f' ≤ (s.p ^ f') ^ 2 := Nat.le_self_pow (by norm_num) _
    have : 0 < s.p ^ f' * ((s.p ^ f') ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
    have h4 : 2 ≤ s.p ^ f' * ((s.p ^ f') ^ 2 - 1) := by
      have : 1 ≤ (s.p ^ f') ^ 2 - 1 := by nlinarith
      nlinarith
    omega) hdvd
  have hcardB := f5.card_B
  have hpf : s.p ^ f' * ((s.p ^ f') ^ 2 - 1) < s.q - 1 := by
    have hp2 : 2 ≤ s.p := (Fact.out : s.p.Prime).two_le
    have h1 : 1 < s.p ^ f' := Nat.one_lt_pow hf'pos.ne' (by omega)
    have h3 : (s.p ^ f') ^ 3 ≤ s.q := by
      rw [Hyp.q, ← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right (by omega) h3f
    have h4 : s.p ^ f' * ((s.p ^ f') ^ 2 - 1) = (s.p ^ f') ^ 3 - s.p ^ f' := by
      rw [Nat.mul_sub, mul_one, ← pow_succ']
    have h5 : s.p ^ f' ≤ (s.p ^ f') ^ 3 := Nat.le_self_pow (by norm_num) _
    rw [h4]
    generalize s.p ^ f' = x at h1 h3 h5 ⊢
    generalize x ^ 3 = y at h3 h5 ⊢
    omega
  omega

open Sec52 in
theorem not_mem_hallPResidual
    (h54 : S_lemma_5_4) (hp : s.p = 3) (f5 : Frame5 s)
    {P : Subgroup G} (hPel : IsElementaryAbelian 3 P) (hP1 : P ≠ ⊥)
    (hJBE : f5.JBE ≤ Subgroup.normalizer (P : Set G))
    (hirr : ∀ Q : Subgroup G, Q ≤ P → f5.JBE ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥ ∨ Q = P)
    (hBfpf : ∀ b ∈ f5.B, b ≠ 1 → ∀ y ∈ P, b * y = y * b → y = 1)
    {x : G} (hxE : x ∈ s.fr.E) (hox : orderOf x = 3) (hxB : ∃ b ∈ f5.B, x * b ≠ b * x) :
    x ∉ (BenderSuzuki.External.hallPResidual 3 (Subgroup.normalizer (P : Set G))).map
      (Subgroup.normalizer (P : Set G)).subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN := h54 G s hp f5 P hPel hP1 hJBE hirr
  have hJN : s.J ∈ Subgroup.normalizer (P : Set G) :=
    hJBE (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  have hBN : f5.B ≤ Subgroup.normalizer (P : Set G) :=
    fun b hb => hJBE (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))
  have hEN : s.fr.E ≤ Subgroup.normalizer (P : Set G) :=
    fun e he => hJBE (Subgroup.mem_sup_right he)
  have hxC : x ∉ Subgroup.centralizer (P : Set G) := by
    intro hxC
    obtain ⟨b, hb, hxb⟩ := hxB
    apply hxb
    have h1 : x * b * x⁻¹ * b⁻¹ ∈ f5.B := f5.B.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (f5.E_le_normalizer_B hxE) b).mp hb) (f5.B.inv_mem hb)
    have h2 : x * b * x⁻¹ * b⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
      have h3 : b * x⁻¹ * b⁻¹ ∈ Subgroup.centralizer (P : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (Sec54.mem_normalizer_centralizer (hBN hb)) x⁻¹).mp
          (Subgroup.inv_mem _ hxC)
      rw [show x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) by group]
      exact Subgroup.mul_mem _ hxC h3
    by_contra hne
    have hc1 : x * b * x⁻¹ * b⁻¹ ≠ 1 := by
      intro h
      apply hne
      calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
        _ = b * x := by rw [h, one_mul]
    apply hP1
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    exact hBfpf _ h1 hc1 y hy (Subgroup.mem_centralizer_iff.mp h2 y hy).symm
  obtain ⟨g, hgE, hgen⟩ := s.fr.exists_generator_E
  rw [s.F_eq_bot, sup_bot_eq] at hgen
  set e := Nat.card s.fr.E with hedef
  set a := e.factorization 3 with hadef
  set E' := Subgroup.zpowers (g ^ (3 ^ a)) with hE'def
  have hog : orderOf g = e := by rw [← Nat.card_zpowers, hgen]
  have hE'card : Nat.card E' = e / 3 ^ a := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
      (hog ▸ Nat.ordProj_dvd e 3), hog]
  have hE'3 : ¬ 3 ∣ Nat.card E' := by
    rw [hE'card]
    exact Nat.not_dvd_ordCompl Nat.prime_three Nat.card_pos.ne'
  have hE'E : E' ≤ s.fr.E := by
    rw [← hgen]
    exact Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _)
  have hgN : g ∈ Subgroup.normalizer (P : Set G) := hEN hgE
  set H₁ := Subgroup.zpowers s.J ⊔ f5.B with hH₁def
  set H := H₁ ⊔ E' with hHdef
  set M := Subgroup.centralizer (P : Set G) ⊔ H with hMdef
  have hJcomm : ∀ y ∈ s.fr.E, y * s.J = s.J * y := fun y hy => s.commute_J (s.fr.E_le_H hy)
  have hJBc : ∀ b ∈ f5.B, b * s.J = s.J * b := fun b hb => s.commute_J (s.K_le_H (f5.B_le hb))
  have hzJ : ∀ y : G, y * s.J = s.J * y →
      y ∈ Subgroup.normalizer ((Subgroup.zpowers s.J : Subgroup G) : Set G) := by
    intro y hy
    apply Sec53.mem_normalizer_of_conj_le
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [show y * s.J ^ k * y⁻¹ = s.J ^ k by
      rw [(Commute.zpow_right (show Commute y s.J from hy) k).eq, mul_inv_cancel_right]]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hH₁N : ∀ y ∈ s.fr.E, y ∈ Subgroup.normalizer ((H₁ : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_sup (hzJ y (hJcomm y hy)) (f5.E_le_normalizer_B hy)
  have hHcard : ¬ 3 ∣ Nat.card H := by
    have hB3 : ¬ 3 ∣ Nat.card f5.B := by
      intro h3
      have := f5.card_B
      rw [Hyp.q, hp] at this
      have h3' : 3 ∣ 3 ^ s.f := dvd_pow_self 3 s.f_pos.ne'
      have h3'' : 3 ∣ 3 ^ s.f - 1 := this ▸ (Dvd.dvd.mul_left h3 2)
      have := Nat.dvd_sub h3' h3''
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by norm_num))] at this
      norm_num at this
    have h1 := card_sup_mul_card_inf (A := Subgroup.zpowers s.J) (C := f5.B)
      (fun b hb => hzJ b (hJBc b hb))
    rw [Nat.card_zpowers, s.orderOf_J, sup_comm] at h1
    have hH₁3 : ¬ 3 ∣ Nat.card H₁ := by
      intro h3
      have : 3 ∣ 2 * Nat.card f5.B := (h3.trans (Dvd.intro _ h1))
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp this with h | h
      · norm_num at h
      · exact hB3 h
    have h2 := card_sup_mul_card_inf (A := H₁) (C := E') (fun y hy => hH₁N y (hE'E hy))
    rw [sup_comm] at h2
    intro h3
    have : 3 ∣ Nat.card H₁ * Nat.card E' := h3.trans (Dvd.intro _ h2)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp this with h | h
    · exact hH₁3 h
    · exact hE'3 h
  have hHN : H ≤ Subgroup.normalizer (P : Set G) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hJN) hBN) (hE'E.trans hEN)
  have hMN : M ≤ Subgroup.normalizer (P : Set G) :=
    sup_le (Subgroup.centralizer_le_normalizer _) hHN
  have hgE' : g ∈ Subgroup.normalizer ((E' : Subgroup G) : Set G) := by
    apply Sec53.mem_normalizer_of_conj_le
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [(Commute.zpow_right (Commute.pow_right (Commute.refl g) _) k).eq, mul_inv_cancel_right]
    exact hz
  have hgM : g ∈ Subgroup.normalizer ((M : Subgroup G) : Set G) :=
    mem_normalizer_sup (Sec54.mem_normalizer_centralizer hgN)
      (mem_normalizer_sup (hH₁N g hgE) hgE')
  have hzgM : Subgroup.zpowers g ≤ Subgroup.normalizer ((M : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hgM
  have hNPM : Subgroup.normalizer (P : Set G) ≤ M ⊔ Subgroup.zpowers g := by
    rw [hN]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))))
    · exact fun b hb => Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)))
    · rw [← hgen]
      exact le_sup_right
    · exact le_sup_left.trans le_sup_left
  have hNPnM :
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer ((M : Subgroup G) : Set G) := by
    intro h hh
    obtain ⟨m, hm, w, hw, rfl⟩ := (mem_sup_iff_of_le_normalizer hzgM).mp (hNPM hh)
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hm) (hzgM hw)
  set NP := Subgroup.normalizer (P : Set G) with hNPdef
  have hMn : (M.subgroupOf NP).Normal :=
    ⟨fun m hm h => Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp
      (hNPnM h.2) m).mp (Subgroup.mem_subgroupOf.mp hm))⟩
  have hq : IsPGroup 3 (NP ⧸ M.subgroupOf NP) := by
    intro z
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨m, hm, w, hw, hmw⟩ := (mem_sup_iff_of_le_normalizer hzgM).mp (hNPM hh)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨a, ?_⟩
    have hgNP : g ∈ NP := hgN
    have hmNP : m ∈ NP := hMN hm
    have hsplit : (⟨h, hh⟩ : NP) = ⟨m, hmNP⟩ * (⟨g, hgNP⟩ : NP) ^ k := by
      apply Subtype.ext
      simp [hmw]
    have hm1 : (QuotientGroup.mk (⟨m, hmNP⟩ : NP) : NP ⧸ M.subgroupOf NP) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hm)
    have hg1 : (QuotientGroup.mk (⟨g, hgNP⟩ : NP) : NP ⧸ M.subgroupOf NP) ^ (3 ^ a) = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      apply Subgroup.mem_subgroupOf.mpr
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    rw [hsplit, QuotientGroup.mk_mul, hm1, one_mul, QuotientGroup.mk_zpow, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg1, one_zpow]
  have hres : BenderSuzuki.External.hallPResidual 3 NP ≤ M.subgroupOf NP := by
    have := BenderSuzuki.External.hallPResidual_le_ker_of_isPGroup
      (QuotientGroup.mk' (M.subgroupOf NP)) hq
    rwa [QuotientGroup.ker_mk'] at this
  have hxM : x ∉ M := by
    intro hxM
    have hxNC : Subgroup.zpowers x ≤ Subgroup.normalizer
        ((Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (Sec54.mem_normalizer_centralizer (hEN hxE))
    have hinf : Subgroup.centralizer (P : Set G) ⊓ Subgroup.zpowers x = ⊥ := by
      have hdvd : Nat.card (Subgroup.centralizer (P : Set G) ⊓ Subgroup.zpowers x :
          Subgroup G) ∣ 3 := by
        rw [← hox, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hxC
        have heq : Subgroup.centralizer (P : Set G) ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, Nat.card_zpowers, hox])
        have : x ∈ Subgroup.centralizer (P : Set G) ⊓ Subgroup.zpowers x := by
          rw [heq]; exact Subgroup.mem_zpowers x
        exact (Subgroup.mem_inf.mp this).1
    have hc1 := card_sup_mul_card_inf hxNC
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hox] at hc1
    have hle : Subgroup.zpowers x ⊔ Subgroup.centralizer (P : Set G) ≤ M :=
      sup_le (Subgroup.zpowers_le.mpr hxM) le_sup_left
    have hdvd1 : Nat.card (Subgroup.centralizer (P : Set G)) * 3 ∣ Nat.card M :=
      hc1 ▸ Subgroup.card_dvd_of_le hle
    have hCN : H ≤ Subgroup.normalizer
        ((Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
      fun h hh => Sec54.mem_normalizer_centralizer (hHN hh)
    have hc2 := card_sup_mul_card_inf hCN
    have hdvd2 : Nat.card M ∣ Nat.card (Subgroup.centralizer (P : Set G)) * Nat.card H := by
      rw [hMdef, sup_comm]
      exact Dvd.intro _ hc2
    exact hHcard (Nat.dvd_of_mul_dvd_mul_left Nat.card_pos (hdvd1.trans hdvd2))
  intro hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact hxM (Subgroup.mem_subgroupOf.mp (hres hy))

end Frame5

end CFSG.Walter.W67
