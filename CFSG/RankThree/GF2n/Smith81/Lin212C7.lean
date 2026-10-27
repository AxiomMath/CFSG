module

public import CFSG.RankThree.GF2n.Smith81.LinRestCore
public import CFSG.RankThree.GF2n.Smith81.Lin28aThree
public import CFSG.RankThree.GF2n.Smith81.LinC7Aux

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G} {x : G}

theorem p31_of (hb : Smith1981Below (Nat.card G)) (hc : Ctx M Q Z B)
    (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) :
    ∀ v ∈ Q, v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂) := by
  obtain ⟨V₁', V₂', hS', -, h31'⟩ := lin31Statement_holds G M Q Z B n V₁ V₂ hb hc hS (by omega)
  rcases linPair_unique hc hS hS' hn with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · subst e1; subst e2; exact h31'
  · intro v hv hv1
    rw [h31' v hv hv1, e1, e2]
    exact or_comm

theorem lin212C7_core_V₁ (h28c : Lin28CondStatement) (hb : Smith1981Below (Nat.card G))
    (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) (hs : Sit M Q Z X x)
    {A : Subgroup G} (hA : IsZConjugate Z A) (hAQ : A ≤ Q) (hAX : A ≤ QB X) (hAV : A ≤ V₁)
    {g q : G} (hq : q ∈ Q) (hg : g * x * g⁻¹ = x * q) :
    ∃ q' ∈ Q, g * x * g⁻¹ = q' * x * q'⁻¹ := by
  have H := hc.hyp
  have h12 := smith_1_12 hs
  have hZQ : Z ≤ Q := H.Z_normal.1
  obtain ⟨hAZ, -, hXLA⟩ := lin29_of_sit hs hA hAQ hAX
  have hcA : Ctx M Q Z A := ⟨H, hA, hAQ, hAZ⟩
  have hxLB : x ∈ LB M Q A := hXLA hs.mem
  have hx2 := hs.x_sq
  have hx : x ∈ H0 M Z := h12.1 hs.mem
  have hxM : x ∈ M := hx.1
  obtain ⟨-, htr⟩ := LinSetup.transv_of_conj hc hS hn hcA
  obtain ⟨hd₁, hd₂, hAc⟩ := htr x hxLB hs.notQ
  obtain ⟨hcn₁, hcn₂⟩ := LinSetup.conj_eq_of_le_V₁ hc hS hn hcA hAV hxLB
  have hxn₁ : x ∈ Subgroup.normalizer (V₁ : Set G) := conjSubgroup_eq_self_iff.mp hcn₁
  have hxn₂ : x ∈ Subgroup.normalizer (V₂ : Set G) := conjSubgroup_eq_self_iff.mp hcn₂
  have hxLgen : x ∈ Lgen M (LB M Q B) := LinSetup.LB_le_Lgen_of_le_V₁ hc hS hn hcA hAV hxLB
  have hQL : Q ≤ Lgen M (LB M Q B) :=
    (le_sup_left : Q ≤ Q ⊔ (QB B ⊓ M)).trans (le_Lgen_self M (LB M Q B))
  obtain ⟨R⟩ := exists_restModel hc hS hn
  have hx_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hqM : q ∈ M := H.Q_normal.1 hq
  have hqH : q ∈ H0 M Z := ⟨hqM, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    Z_central H hz hq⟩
  have hx'M : g * x * g⁻¹ ∈ M := by rw [hg]; exact M.mul_mem hxM hqM
  have hx'Q : g * x * g⁻¹ ∉ Q := by
    intro h
    apply hs.notQ
    have : x = (g * x * g⁻¹) * q⁻¹ := by rw [hg]; group
    rw [this]; exact Q.mul_mem h (Q.inv_mem hq)
  have hXc : IsZConjugate Z X := hs.conj
  have hX'conj : IsZConjugate Z (conjSubgroup g X) := hXc.conj g
  have hx'mem : g * x * g⁻¹ ∈ conjSubgroup g X := by
    rw [mem_conjSubgroup]
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [this]; exact hs.mem
  have hx'1 : g * x * g⁻¹ ≠ 1 := fun h => hs.ne_one (by
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h]; group)
  have hs' : Sit M Q Z (conjSubgroup g X) (g * x * g⁻¹) :=
    ⟨H, hX'conj, hx'mem, hx'1, hx'M, hx'Q⟩
  have hx'2 : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := hs'.x_sq
  have hx'H : g * x * g⁻¹ ∈ H0 M Z := (smith_1_12 hs').1 hx'mem
  have hqn₁ : q ∈ Subgroup.normalizer (V₁ : Set G) :=
    Q_le_normalizer_of_Z_le H R.ZV₁ R.V₁Q hq
  have hqn₂ : q ∈ Subgroup.normalizer (V₂ : Set G) :=
    Q_le_normalizer_of_Z_le H R.ZV₂ R.V₂Q hq
  have hx'n₁ : g * x * g⁻¹ ∈ Subgroup.normalizer (V₁ : Set G) := by
    rw [hg]; exact (Subgroup.normalizer (V₁ : Set G)).mul_mem hxn₁ hqn₁
  have hx'n₂ : g * x * g⁻¹ ∈ Subgroup.normalizer (V₂ : Set G) := by
    rw [hg]; exact (Subgroup.normalizer (V₂ : Set G)).mul_mem hxn₂ hqn₂
  have hφ' : R.φ ⟨g * x * g⁻¹, hx'H⟩ = R.φ ⟨x, hx⟩ := by
    have h1 : (⟨g * x * g⁻¹, hx'H⟩ : ↥(H0 M Z)) = ⟨x, hx⟩ * ⟨q, hqH⟩ := Subtype.ext hg
    rw [h1, map_mul, (R.φker ⟨q, hqH⟩).mpr hq, mul_one]
  have hNsp : R.Nsp hx'H = R.Nsp hx := by
    ext e
    rw [R.mem_Nsp hx'H, R.mem_Nsp hx, hφ']
  have hZq : 0 < Nat.card Z := Nat.card_pos
  have hne' : Q ⊓ QB (conjSubgroup g X) ≠ ⊥ := by
    by_cases hn3 : n = 3
    · exact lin28a_three hb hc hS hn3 hs'
    · intro hD'
      have hx'L : g * x * g⁻¹ ∈ Lgen M (LB M Q B) := by
        rw [hg]; exact (Lgen M (LB M Q B)).mul_mem hxLgen (hQL hq)
      have hrank := lin115RankStatement_holds G M Q Z B (conjSubgroup g X) (g * x * g⁻¹) n V₁
        V₂ hc hS hn hs' hx'L hD'
      have hcard : Nat.card ↥(⁅V₁, Subgroup.zpowers (g * x * g⁻¹)⁆ ⊔ Z) =
          Nat.card ↥(⁅V₁, Subgroup.zpowers x⁆ ⊔ Z) := by
        rw [R.card_comm_sup_V₁ hx'H hx'2 hx'n₁ hx'n₂, R.card_comm_sup_V₁ hx hx2 hxn₁ hxn₂,
          hNsp]
      have h1 : Nat.card ↥(⁅V₁, Subgroup.zpowers (g * x * g⁻¹)⁆ ⊔ Z) =
          Nat.card Z ^ (1 + 1) := by rw [hcard]; exact hd₁
      have h2 : Nat.card ↥(⁅V₁, Subgroup.zpowers (g * x * g⁻¹)⁆ ⊔ Z) =
          Nat.card Z ^ (n / 2 + 1) := hrank.1
      have hq1 : 2 ≤ Nat.card Z := by have := H.q4; omega
      have := Nat.pow_right_injective hq1 (h2.symm.trans h1)
      omega
  obtain ⟨A', hA', hA'le⟩ := h28c G M Q Z B (conjSubgroup g X) (g * x * g⁻¹) n V₁ V₂ hb hc hS hn
    hs' hne'
  have hA'Q : A' ≤ Q := hA'le.trans inf_le_left
  have hA'X : A' ≤ QB (conjSubgroup g X) := hA'le.trans inf_le_right
  obtain ⟨hA'Z, -, -⟩ := lin29_of_sit hs' hA' hA'Q hA'X
  have hcA' : Ctx M Q Z A' := ⟨H, hA', hA'Q, hA'Z⟩
  have hD'core : ∀ e ∈ R.Nsp hx'H, e ∈ R.M₀.img (Q ⊓ QB (conjSubgroup g X)) := by
    rcases (LinSetup.transv_of_conj hc hS hn hcA').1 with hA'V | hA'V
    · exact rest_first_core_R R hb hc hS hn hs' hx'H hA' hA'Q hA'X hA'V
    · exact rest_first_core_R R.symm hb hc hS.symm hn hs' hx'H hA' hA'Q hA'X hA'V
  obtain ⟨b, hb0, -, hAb, -, -⟩ := hcA.dictB R.gm
  have hbA : b ∈ R.M₀.img A := (hAb b).mpr ⟨1, by rw [one_smul]⟩
  obtain ⟨a₀, ha₀A, ha₀Q, ha₀b⟩ := hbA
  have hbN : b ∈ R.Nsp hx := by
    have := ((R.mem_comm_sup_iff hx hx2).mp (hAc ha₀A)).2
    rwa [ha₀b] at this
  have hbW₁ : b ∈ R.W₁ := (R.memW₁ b).mpr (R.M₀.img_mono hAV ⟨a₀, ha₀A, ha₀Q, ha₀b⟩)
  obtain ⟨d, hd, hdQ, hdb⟩ := hD'core b (by rw [hNsp]; exact hbN)
  have hdV₁ : d ∈ V₁ :=
    (R.M₀.mem_img_iff R.ZV₁ hd.1).mp (by rw [hdb]; exact (R.memW₁ b).mp hbW₁)
  have hdZ : d ∉ Z := fun h => hb0 (by rw [← hdb]; exact (R.M₀.π_ker d hd.1).mpr h)
  have hd1 : d ≠ 1 := fun h => hdZ (h ▸ Z.one_mem)
  have hdcl : InZClass Z d := (p31_of hb hc hS hn d hd.1 hd1).mpr (Or.inl hdV₁)
  obtain ⟨g₁, z₁, hz₁, -, hdz⟩ := hdcl
  obtain ⟨g', hg'Q, hdg'⟩ := stroth_2_6 H hd.1 hdZ ⟨g₁, z₁, hz₁, hdz⟩
  have hA'' : IsZConjugate Z (conjSubgroup g' Z) := ⟨g', rfl⟩
  have hA''X' : conjSubgroup g' Z ≤ QB (conjSubgroup g X) :=
    IsZConjugate.le_QB_of_mem H hX'conj hA'' hd1 hdg' hd.2
  have hA''Z : conjSubgroup g' Z ≠ Z := fun h => hdZ (h ▸ hdg')
  have hcA'' : Ctx M Q Z (conjSubgroup g' Z) := ⟨H, hA'', hg'Q, hA''Z⟩
  have hA''V : conjSubgroup g' Z ≤ V₁ := by
    rcases (LinSetup.transv_of_conj hc hS hn hcA'').1 with h | h
    · exact h
    · exfalso
      apply hdZ
      rw [← R.V₁₂]
      exact ⟨hdV₁, h hdg'⟩
  obtain ⟨b'', hb''0, -, hA''b, -, -⟩ := hcA''.dictB R.gm
  have hA''le : conjSubgroup g' Z ≤ Z ⊔ A := by
    intro u hu
    have huQ : u ∈ Q := hg'Q hu
    have hπu : R.M₀.π u ∈ R.M₀.img (conjSubgroup g' Z) := R.M₀.pi_mem_img hu huQ
    obtain ⟨t, ht⟩ := (hA''b _).mp hπu
    have hbd : b ∈ R.M₀.img (conjSubgroup g' Z) := ⟨d, hdg', hd.1, hdb⟩
    obtain ⟨s, hs⟩ := (hA''b b).mp hbd
    have hs0 : s ≠ 0 := fun h => hb0 (by rw [hs, h, zero_smul])
    have hπA : R.M₀.π u ∈ R.M₀.img A :=
      (hAb _).mpr ⟨t / s, by rw [ht, hs, smul_smul, div_mul_cancel₀ _ hs0]⟩
    obtain ⟨a, haA, haQ, haπ⟩ := hπA
    have hz : a⁻¹ * u ∈ Z := (R.M₀.pi_eq_iff haQ huQ).mp haπ
    have hu' : u = a * (a⁻¹ * u) := by group
    rw [hu', sup_comm]
    exact Subgroup.mul_mem_sup haA hz
  obtain ⟨p, hpQ, hp⟩ := hcA.exists_conj_of_le_ZB hcA'' hA''le
  have hpM : p ∈ M := H.Q_normal.1 hpQ
  have hX''conj : IsZConjugate Z (conjSubgroup p⁻¹ (conjSubgroup g X)) := hX'conj.conj p⁻¹
  have hx''mem : p⁻¹ * (g * x * g⁻¹) * p ∈ conjSubgroup p⁻¹ (conjSubgroup g X) := by
    rw [mem_conjSubgroup]
    have : (p⁻¹)⁻¹ * (p⁻¹ * (g * x * g⁻¹) * p) * p⁻¹ = g * x * g⁻¹ := by group
    rw [this]; exact hx'mem
  have hx''1 : p⁻¹ * (g * x * g⁻¹) * p ≠ 1 := fun h => hx'1 (by
    have : g * x * g⁻¹ = p * (p⁻¹ * (g * x * g⁻¹) * p) * p⁻¹ := by group
    rw [this, h]; group)
  have hx''Q : p⁻¹ * (g * x * g⁻¹) * p ∉ Q := by
    intro h
    apply hx'Q
    have h2 : p * (p⁻¹ * (g * x * g⁻¹) * p) * p⁻¹ ∈ Q :=
      Q.mul_mem (Q.mul_mem hpQ h) (Q.inv_mem hpQ)
    have e : p * (p⁻¹ * (g * x * g⁻¹) * p) * p⁻¹ = g * x * g⁻¹ := by group
    rwa [e] at h2
  have hx''cl : InZClass Z (p⁻¹ * (g * x * g⁻¹) * p) :=
    inZClass_of_mem_root hX''conj hx''mem hx''1
  have hxcl : InZClass Z x := inZClass_of_mem_root hs.conj hs.mem hs.ne_one
  have hAX'' : A ≤ QB (conjSubgroup p⁻¹ (conjSubgroup g X)) := by
    rw [QB_conj_of_isZConjugate H hX'conj p⁻¹]
    intro a ha
    rw [mem_conjSubgroup]
    have hpa : p * a * p⁻¹ ∈ conjSubgroup g' Z := by
      rw [← hp, mem_conjSubgroup]
      have : p⁻¹ * (p * a * p⁻¹) * p = a := by group
      rw [this]; exact ha
    have : (p⁻¹)⁻¹ * a * p⁻¹ = p * a * p⁻¹ := by group
    rw [this]; exact hA''X' hpa
  have hx''A : p⁻¹ * (g * x * g⁻¹) * p ∈ QB A :=
    (IsZConjugate.le_QB_iff H hA hX''conj).mpr hAX'' hx''mem
  have hxA : x ∈ QB A := (IsZConjugate.le_QB_iff H hA hs.conj).mpr hAX hs.mem
  have hxx'' : x⁻¹ * (p⁻¹ * (g * x * g⁻¹) * p) ∈ Q := by
    have hp' : p⁻¹ ∈ Q := Q.inv_mem hpQ
    have e : x⁻¹ * (p⁻¹ * (g * x * g⁻¹) * p) = (x * p⁻¹ * x⁻¹) * q * p := by
      rw [hg, hx_inv]; group
    rw [e]
    exact Q.mul_mem (Q.mul_mem (conj_mem_Q H hxM hp') hq) hpQ
  have hainA := uniq_over_xbar hb hc hS hn hcA hxcl hx''cl hs.notQ hx''Q hxA hx''A hxx''
  obtain ⟨p', hp'V, hp'⟩ :=
    exists_conj_mul_eq hb hc hS hn hcA hAV hxM hs.notQ hxA _ hainA
  refine ⟨p * p', Q.mul_mem hpQ (R.V₁Q hp'V), ?_⟩
  have e1 : p' * x * p'⁻¹ = p⁻¹ * (g * x * g⁻¹) * p := by rw [hp']; group
  calc g * x * g⁻¹ = p * (p⁻¹ * (g * x * g⁻¹) * p) * p⁻¹ := by group
    _ = p * (p' * x * p'⁻¹) * p⁻¹ := by rw [e1]
    _ = (p * p') * x * (p * p')⁻¹ := by group

theorem lin212C7_of (h28c : Lin28CondStatement) : Lin212C7Statement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn X x hs hne g q hq hg
  obtain ⟨A, hA, hAle⟩ := h28c G M Q Z B X x n V₁ V₂ hb hc hS hn hs hne
  have hAQ : A ≤ Q := hAle.trans inf_le_left
  have hAX : A ≤ QB X := hAle.trans inf_le_right
  obtain ⟨hAZ, -, -⟩ := lin29_of_sit hs hA hAQ hAX
  have hcA : Ctx M Q Z A := ⟨hc.hyp, hA, hAQ, hAZ⟩
  rcases (LinSetup.transv_of_conj hc hS hn hcA).1 with h | h
  · exact lin212C7_core_V₁ h28c hb hc hS hn hs hA hAQ hAX h hq hg
  · exact lin212C7_core_V₁ h28c hb hc hS.symm hn hs hA hAQ hAX h hq hg

end CFSG.RankThree.GF2n.Smith81
