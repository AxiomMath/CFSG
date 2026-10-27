module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubType
import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubType2
import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubDet
import CFSG.RankThree.PartTwo.Sec4.LThreePiRank
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree slPi glPi zPi Type123)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

theorem sup_zpowers_eq_top {B : Type} [Group B] [Finite B] (hB9 : Nat.card B = 9)
    (hB3 : ∀ b : B, b ^ 3 = 1) (hBc : ∀ a b : B, a * b = b * a) {u v : B} (hu : u ≠ 1)
    (hv : v ∉ Subgroup.zpowers u) : Subgroup.zpowers u ⊔ Subgroup.zpowers v = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu3 : orderOf u = 3 := orderOf_eq_prime (hB3 u) hu
  have h := Sec4.card_zpowers_sup_zpowers (hB3 v) hu3 hv (hBc v u)
  exact Subgroup.eq_top_of_card_eq _ (h.trans hB9.symm)

theorem false_of_inner_of_cyclic {K : Type} [Group K] [Finite K] (hKs : IsSimpleGroup K)
    {B : Type} [Group B] (ρ : B →* MulAut K) (hρ : Function.Injective ρ) (hB9 : Nat.card B = 9)
    (hB3 : ∀ b : B, b ^ 3 = 1) (hinn : ∀ b : B, ∃ k : K, ρ b = MulAut.conj k)
    (hcyc : ∀ Q : Sylow 3 K, IsCyclic Q) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBf : Finite B := Nat.finite_of_card_ne_zero (by omega)
  have hconj1 : ∀ k : K, MulAut.conj k = 1 → k ∈ Subgroup.center K := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun α : MulAut K => α g) hk
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * k = k * g * k⁻¹ * k := by rw [h1]
      _ = k * g := by group
  have hZ : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · exfalso
      have hall : ∀ b : B, b = 1 := by
        intro b
        obtain ⟨k, hk⟩ := hinn b
        apply hρ
        rw [hk, map_one]
        ext g
        have hkc : k ∈ Subgroup.center K := h ▸ Subgroup.mem_top k
        rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hkc g).symm,
          mul_inv_cancel_right]
      have : Nat.card B = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by
        rw [hall a, hall b]⟩, ⟨1⟩⟩
      omega
  have hconjinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have := hconj1 k hk
    rw [hZ] at this
    exact Subgroup.mem_bot.mp this
  set H := ρ.range.comap (MulAut.conj : K →* MulAut K) with hH
  have hHmap : H.map (MulAut.conj : K →* MulAut K) = ρ.range := by
    rw [hH, Subgroup.map_comap_eq]
    refine inf_eq_right.mpr ?_
    rintro _ ⟨b, rfl⟩
    obtain ⟨k, hk⟩ := hinn b
    exact ⟨k, hk.symm⟩
  have hH9 : Nat.card H = 9 := by
    rw [← Subgroup.card_map_of_injective hconjinj, hHmap, ← hB9]
    exact Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv.symm
  have hH3 : ∀ h ∈ H, h ^ 3 = 1 := by
    intro h hh
    obtain ⟨b, hb⟩ := hh
    apply hconjinj
    rw [map_pow, ← hb, ← map_pow, hB3, map_one, map_one]
  have hHp : IsPGroup 3 H := IsPGroup.of_card (n := 2) (by rw [hH9]; norm_num)
  obtain ⟨Q, hHQ⟩ := hHp.exists_le_sylow
  haveI := hcyc Q
  haveI : IsCyclic H := Subgroup.isCyclic_of_le hHQ
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hH3 g g.2)
  have h1 := orderOf_le_of_pow_eq_one (by norm_num) hg3
  rw [hg, hH9] at h1
  omega

theorem heis_or_pgl_of_modThree {K : Type} [Field K] {π : Bool} {p f : ℕ}
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {B : Type} [Group B] [Finite B] (hB9 : Nat.card B = 9) (hB3 : ∀ b : B, b ^ 3 = 1)
    (hBc : ∀ a b : B, a * b = b * a)
    (β : B →* MulAut (projImage (slPi π 3 (p ^ f) K))) (hβ : Function.Injective β)
    (y : B → GL (Fin 3) K) (hyH : ∀ b, y b ∈ glPi π 3 (p ^ f) K)
    (hy : ∀ b (m : projImage (slPi π 3 (p ^ f) K)),
      (β b m : ProjGenLinGroup (Fin 3) K) = pmk (y b) * m * (pmk (y b))⁻¹)
    (hfixB : ∀ b : B, b ≠ 1 → ∀ m : projImage (slPi π 3 (p ^ f) K), β b m = m → m ^ p = 1 →
      m = 1) :
    (∃ y₁ y₂ : GL (Fin 3) K, Type123 π (p ^ f) K y₁ 1 ∧ y₂ ∈ slPi π 3 (p ^ f) K ∧
      (∃ ζ : Kˣ, ζ ≠ 1 ∧ y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) ∧
      y₁ ^ 3 ∈ StatedScalars (Fin 3) K ∧ y₂ ^ 3 ∈ StatedScalars (Fin 3) K ∧
      (∃ l₁ ∈ slPi π 3 (p ^ f) K, pmk l₁ = pmk y₁) ∧
      ∀ b, ∃ i j : ℤ, ∀ m : projImage (slPi π 3 (p ^ f) K),
        (β b m : ProjGenLinGroup (Fin 3) K) =
          (pmk y₁ ^ i * pmk y₂ ^ j) * m * (pmk y₁ ^ i * pmk y₂ ^ j)⁻¹) ∨
    (∃ y s : GL (Fin 3) K, y ∈ glPi π 3 (p ^ f) K ∧ Type123 π (p ^ f) K y 3 ∧
      s ∈ slPi π 3 (p ^ f) K ∧ s ∉ StatedScalars (Fin 3) K ∧ s ^ 3 ∈ StatedScalars (Fin 3) K ∧
      y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K ∧
      ∀ b, ∃ i j : ℤ, ∀ m : projImage (slPi π 3 (p ^ f) K),
        (β b m : ProjGenLinGroup (Fin 3) K) =
          (pmk s ^ i * pmk y ^ j) * m * (pmk s ^ i * pmk y ^ j)⁻¹) := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.finite
  haveI : Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hβone : ∀ b : B, (∀ m : projImage (slPi π 3 (p ^ f) K), β b m = m) → b = 1 := by
    intro b hb
    apply hβ
    rw [map_one]
    ext m
    rw [MulAut.one_apply, hb m]
  have hcube : ∀ (b : B) (c : GL (Fin 3) K), (∀ m : projImage (slPi π 3 (p ^ f) K),
      (β b m : ProjGenLinGroup (Fin 3) K) = pmk c * m * (pmk c)⁻¹) →
        c ^ 3 ∈ StatedScalars (Fin 3) K := by
    intro b c hc
    have h1 := lift_inv_mul_mem hK hq (y := 1) (y' := c ^ 3) fun m => by
      have h2 := conjAct_pow hc 3 m
      rw [← map_pow, hB3, map_one, MulAut.one_apply] at h2
      rw [map_one, one_mul, inv_one, mul_one, map_pow, ← h2]
    rwa [inv_one, one_mul] at h1
  set Q := GL (Fin 3) K ⧸ StatedScalars (Fin 3) K
  have hyprod : ∀ a b : B, (y a * y b)⁻¹ * y (a * b) ∈ StatedScalars (Fin 3) K := by
    intro a b
    refine lift_inv_mul_mem hK hq fun m => ?_
    have e1 : β (a * b) m = β a (β b m) := by rw [map_mul, MulAut.mul_apply]
    rw [← hy (a * b) m, e1, hy a, hy b, map_mul]
    group
  have hy1 : y 1 ∈ StatedScalars (Fin 3) K := by
    have h1 := lift_inv_mul_mem hK hq (y := 1) (y' := y 1) fun m => by
      rw [← hy 1 m, map_one β, MulAut.one_apply, map_one, one_mul, inv_one, mul_one]
    rwa [inv_one, one_mul] at h1
  let ρ : B →* Q :=
    { toFun := fun b => (y b : Q)
      map_one' := (QuotientGroup.eq_one_iff _).mpr hy1
      map_mul' := fun a b => by
        change ((y (a * b) : GL (Fin 3) K) : Q) = ((y a * y b : GL (Fin 3) K) : Q)
        rw [QuotientGroup.eq]
        have := inv_mem (hyprod a b)
        rwa [_root_.mul_inv_rev, inv_inv] at this }
  have hρ : ∀ b, ρ b = (y b : Q) := fun b => rfl
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h1 : pmk (y b) = 1 :=
      Sec4.mk_eq_one_iff_mem_statedScalars.mpr ((QuotientGroup.eq_one_iff _).mp hb)
    refine hβone b fun m => Subtype.ext ?_
    rw [hy, h1, one_mul, inv_one, mul_one]
  set E := ρ.range with hE
  have hEc : ∀ x ∈ E, ∀ x' ∈ E, x * x' = x' * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hBc]
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hB3, map_one]
  have hE9 : Nat.card E = 9 := by
    rw [hE, ← hB9]
    exact Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv.symm
  have hyZ : ∀ b : B, b ≠ 1 → y b ∉ StatedScalars (Fin 3) K := fun b hb h => hb (hρinj (by
    rw [map_one, hρ]
    exact (QuotientGroup.eq_one_iff _).mpr h))
  have hzPi := Sec4.zPi_eq hπ hq' hτ hτ1
  have htype : ∀ b : B, b ≠ 1 → Type123 π (p ^ f) K (y b) 1 ∨ Type123 π (p ^ f) K (y b) 3 := by
    intro b hb
    have hZ : y b ∉ zPi π 3 (p ^ f) K := by
      rw [hzPi]
      exact fun h => hyZ b hb (Subgroup.mem_inf.mp h).2
    have hZ3 : y b ^ 3 ∈ zPi π 3 (p ^ f) K := by
      rw [hzPi]
      exact Subgroup.mem_inf.mpr ⟨pow_mem (hyH b) 3, hcube b (y b) (hy b)⟩
    rcases Sec4.type123_exhaust hK hq (hyH b) hZ hZ3 with h | h | h
    · exact Or.inl h
    · obtain ⟨m, hm1, hmp, hmfix⟩ := fix_of_type2 hK hq (hy b) h
      exact absurd (hfixB b hb m hmfix hmp) hm1
    · exact Or.inr h
  have hPcase : ∀ ba bb : B, ba ≠ 1 → bb ∉ Subgroup.zpowers ba →
      Type123 π (p ^ f) K (y ba) 3 →
      ∃ y s : GL (Fin 3) K, y ∈ glPi π 3 (p ^ f) K ∧ Type123 π (p ^ f) K y 3 ∧
        s ∈ slPi π 3 (p ^ f) K ∧ s ∉ StatedScalars (Fin 3) K ∧ s ^ 3 ∈ StatedScalars (Fin 3) K ∧
        y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K ∧
        ∀ b, ∃ i j : ℤ, ∀ m : projImage (slPi π 3 (p ^ f) K),
          (β b m : ProjGenLinGroup (Fin 3) K) =
            (pmk s ^ i * pmk y ^ j) * m * (pmk s ^ i * pmk y ^ j)⁻¹ := by
    intro ba bb hba hbb h3
    obtain ⟨k, l, hl, z, hlz⟩ := exists_pow_mul_slPi_mul_scalar hK hq (hyH ba) (hyH bb) h3
    set bs := ba ^ k * bb with hbs
    have hbsl : ∀ m : projImage (slPi π 3 (p ^ f) K),
        (β bs m : ProjGenLinGroup (Fin 3) K) = pmk l * m * (pmk l)⁻¹ := by
      intro m
      have h1 := conjAct_mul (conjAct_pow (hy ba) k) (hy bb) m
      have h2 : pmk (y ba) ^ k * pmk (y bb) = pmk l := by
        rw [← map_pow, ← map_mul, hlz, map_mul,
          Sec4.mk_eq_one_iff_mem_statedScalars.mpr ⟨z, rfl⟩, mul_one]
      rw [hbs, map_mul, map_pow, h1, h2]
    have hbs1 : bs ≠ 1 := by
      intro h
      apply hbb
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_mem (pow_mem (Subgroup.mem_zpowers ba) k)
    have hbsn : bs ∉ Subgroup.zpowers ba := by
      rintro ⟨t, ht⟩
      apply hbb
      have : bb = (ba ^ k)⁻¹ * bs := by rw [hbs]; group
      rw [this, ← ht]
      exact mul_mem (inv_mem (pow_mem (Subgroup.mem_zpowers ba) k))
        (zpow_mem (Subgroup.mem_zpowers ba) t)
    have htop : Subgroup.zpowers bs ⊔ Subgroup.zpowers ba = ⊤ := by
      rw [sup_comm]
      exact sup_zpowers_eq_top hB9 hB3 hBc hba hbsn
    refine ⟨y ba, l, hyH ba, h3, hl, fun hlZ => hbs1 (hβone bs fun m => Subtype.ext ?_),
      hcube bs l hbsl, ?_, fun b => ?_⟩
    · rw [hbsl, Sec4.mk_eq_one_iff_mem_statedScalars.mpr hlZ, one_mul, inv_one, mul_one]
    ·
      have hc := lift_inv_mul_mem hK hq (y := y ba * l) (y' := l * y ba) fun m => by
        have h1 := conjAct_mul (hy ba) hbsl m
        have h2 := conjAct_mul hbsl (hy ba) m
        rw [map_mul, map_mul, ← h1, ← h2, ← map_mul β ba bs, ← map_mul β bs ba, hBc]
      have e1 : y ba * l * (y ba)⁻¹ * l⁻¹ =
          (y ba * l) * ((y ba * l)⁻¹ * (l * y ba))⁻¹ * (y ba * l)⁻¹ := by group
      rw [e1]
      exact Subgroup.Normal.conj_mem inferInstance _ (inv_mem hc) _
    · obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup (hBc bs ba)
        (htop ▸ Subgroup.mem_top b)
      refine ⟨i, j, fun m => ?_⟩
      rw [map_mul, map_zpow, map_zpow]
      exact conjAct_mul (conjAct_zpow hbsl i) (conjAct_zpow (hy ba) j) m
  rcases Sec4.frame_or_heis (hK.three_ne_zero hq) hτ hτ1 E hEc hE3
      (by rw [hE9]; norm_num) with ⟨bs, hbs, hd, -⟩ | ⟨y₁', y₂', hy₁E, hy₂E, ζ, hζ1, hζ⟩
  · exfalso
    set A : Subgroup (GL (Fin 3) K) :=
      E.comap (QuotientGroup.mk' (StatedScalars (Fin 3) K)) ⊓ glPi π 3 (p ^ f) K with hA
    have hAmap : A.map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) = E := by
      apply le_antisymm
      · rintro _ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_inf.mp ha).1
      · rintro _ ⟨b, rfl⟩
        exact ⟨y b, Subgroup.mem_inf.mpr ⟨⟨b, rfl⟩, hyH b⟩, rfl⟩
    have hC : Sec4.IsTypeC π (p ^ f) K A := by
      refine ⟨inf_le_right, fun a ha => ?_, by rw [hAmap, hE9], bs, hbs,
        fun a ha => hd a (Subgroup.mem_inf.mp ha).1⟩
      have h1 : ((a : GL (Fin 3) K) : Q) ^ 3 = 1 := hE3 _ (Subgroup.mem_inf.mp ha).1
      rw [← QuotientGroup.mk_pow] at h1
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨a₁, ha₁A, -, hchar⟩ := Sec4.isTypeC_types hK hq hC
    set m₁ : Q := (a₁ : Q) with hm₁
    have hm₁3 : m₁ ^ 3 = 1 := hE3 _ (Subgroup.mem_inf.mp ha₁A).1
    obtain ⟨b, hb⟩ : ∃ b : B, ρ b ∉ Subgroup.zpowers m₁ := by
      by_contra hcon
      push Not at hcon
      have hle : E ≤ Subgroup.zpowers m₁ := by
        rintro _ ⟨b, rfl⟩
        exact hcon b
      have : Finite (Subgroup.zpowers m₁) :=
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hm₁3⟩).finite_zpowers
      have h1 := Subgroup.card_le_of_le hle
      rw [hE9, Nat.card_zpowers] at h1
      have h2 : orderOf m₁ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hm₁3
      omega
    have hb1 : b ≠ 1 := by
      rintro rfl
      apply hb
      rw [map_one]
      exact Subgroup.one_mem _
    have hbA : y b ∈ A := Subgroup.mem_inf.mpr ⟨⟨b, rfl⟩, hyH b⟩
    have hnot1 : ¬ Type123 π (p ^ f) K (y b) 1 := by
      intro h1
      rcases (hchar (y b) hbA (hyZ b hb1)).1.mp h1 with h | h
      · apply hb
        have : ρ b = m₁ := by
          rw [hρ, hm₁, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
          exact h
        rw [this]
        exact Subgroup.mem_zpowers m₁
      · apply hb
        have : ρ b = m₁⁻¹ := by
          rw [hρ, hm₁, ← QuotientGroup.mk_inv, QuotientGroup.eq_iff_div_mem, div_inv_eq_mul]
          exact h
        rw [this]
        exact inv_mem (Subgroup.mem_zpowers m₁)
    obtain ⟨m, hm1, hmp, hmfix⟩ :=
      fix_of_type2 hK hq (hy b) ((hchar (y b) hbA (hyZ b hb1)).2 hnot1)
    exact hm1 (hfixB b hb1 m hmfix hmp)
  · obtain ⟨b₁, hb₁⟩ := hy₁E
    obtain ⟨b₂, hb₂⟩ := hy₂E
    obtain ⟨u₁, hu₁⟩ : (y₁')⁻¹ * y b₁ ∈ StatedScalars (Fin 3) K := QuotientGroup.eq.mp hb₁.symm
    obtain ⟨u₂, hu₂⟩ : (y₂')⁻¹ * y b₂ ∈ StatedScalars (Fin 3) K := QuotientGroup.eq.mp hb₂.symm
    have hw₁ : y b₁ = y₁' * GeneralLinearGroup.scalar (Fin 3) u₁ := by
      rw [hu₁]
      group
    have hw₂ : y b₂ = y₂' * GeneralLinearGroup.scalar (Fin 3) u₂ := by
      rw [hu₂]
      group
    have hheis : y b₁ * y b₂ * (y b₁)⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y b₂ := by
      rw [hw₁, hw₂]
      calc y₁' * GeneralLinearGroup.scalar (Fin 3) u₁ *
            (y₂' * GeneralLinearGroup.scalar (Fin 3) u₂) *
            (y₁' * GeneralLinearGroup.scalar (Fin 3) u₁)⁻¹ =
          y₁' * (GeneralLinearGroup.scalar (Fin 3) u₁ *
            (y₂' * GeneralLinearGroup.scalar (Fin 3) u₂)) *
            (GeneralLinearGroup.scalar (Fin 3) u₁)⁻¹ * y₁'⁻¹ := by group
        _ = y₁' * ((y₂' * GeneralLinearGroup.scalar (Fin 3) u₂) *
            GeneralLinearGroup.scalar (Fin 3) u₁) *
            (GeneralLinearGroup.scalar (Fin 3) u₁)⁻¹ * y₁'⁻¹ := by rw [← hsc]
        _ = y₁' * y₂' * (GeneralLinearGroup.scalar (Fin 3) u₂ * y₁'⁻¹) := by group
        _ = y₁' * y₂' * (y₁'⁻¹ * GeneralLinearGroup.scalar (Fin 3) u₂) := by rw [hsc]
        _ = (y₁' * y₂' * y₁'⁻¹) * GeneralLinearGroup.scalar (Fin 3) u₂ := by group
        _ = GeneralLinearGroup.scalar (Fin 3) ζ * (y₂' * GeneralLinearGroup.scalar (Fin 3) u₂) := by
            rw [hζ]
            group
    have hnc : y b₁ * y b₂ ≠ y b₂ * y b₁ := by
      intro h
      apply hζ1
      have h1 : GeneralLinearGroup.scalar (Fin 3) ζ * y b₂ = y b₂ := by
        rw [← hheis, h, mul_inv_cancel_right]
      have h2 : GeneralLinearGroup.scalar (Fin 3) ζ = 1 := by
        have := congrArg (fun w => w * (y b₂)⁻¹) h1
        simpa using this
      have h3 := congrArg (fun w : GL (Fin 3) K => (w : Matrix (Fin 3) (Fin 3) K) 0 0) h2
      simp [GeneralLinearGroup.coe_scalar] at h3
      exact h3
    have hnot : ∀ c c' : B, (y c * y c' ≠ y c' * y c) → c' ∉ Subgroup.zpowers c := by
      rintro c c' hcc ⟨t, rfl⟩
      apply hcc
      have h1 : ((y c ^ t)⁻¹ * y (c ^ t)) ∈ StatedScalars (Fin 3) K := by
        rw [← QuotientGroup.eq]
        change ((y c ^ t : GL (Fin 3) K) : Q) = ρ (c ^ t)
        rw [map_zpow, hρ, QuotientGroup.mk_zpow]
      obtain ⟨v, hv⟩ := h1
      have h2 : y (c ^ t) = y c ^ t * GeneralLinearGroup.scalar (Fin 3) v := by
        rw [hv]
        group
      rw [h2]
      calc y c * (y c ^ t * GeneralLinearGroup.scalar (Fin 3) v) =
          y c ^ t * y c * GeneralLinearGroup.scalar (Fin 3) v := by
            rw [← mul_assoc, (Commute.self_zpow (y c) t).eq]
        _ = y c ^ t * (y c * GeneralLinearGroup.scalar (Fin 3) v) := by group
        _ = y c ^ t * (GeneralLinearGroup.scalar (Fin 3) v * y c) := by rw [hsc]
        _ = y c ^ t * GeneralLinearGroup.scalar (Fin 3) v * y c := by group
    have hb₂n : b₂ ∉ Subgroup.zpowers b₁ := hnot b₁ b₂ hnc
    have hb₁n : b₁ ∉ Subgroup.zpowers b₂ := hnot b₂ b₁ (fun h => hnc h.symm)
    have hb₁1 : b₁ ≠ 1 := fun h => hb₁n (h ▸ Subgroup.one_mem _)
    have hb₂1 : b₂ ≠ 1 := fun h => hb₂n (h ▸ Subgroup.one_mem _)
    rcases htype b₁ hb₁1 with h₁ | h₁
    · rcases htype b₂ hb₂1 with h₂ | h₂
      ·
        left
        obtain ⟨l₁, hl₁, hl₁y⟩ := exists_slPi_mk_eq_of_type1 hK hq h₁
        obtain ⟨l₂, hl₂, hl₂y⟩ := exists_slPi_mk_eq_of_type1 hK hq h₂
        obtain ⟨v, hv⟩ : (y b₂)⁻¹ * l₂ ∈ StatedScalars (Fin 3) K := by
          rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, hl₂y, inv_mul_cancel]
        have hl₂w : l₂ = y b₂ * GeneralLinearGroup.scalar (Fin 3) v := by
          rw [hv]
          group
        have htop : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ = ⊤ :=
          sup_zpowers_eq_top hB9 hB3 hBc hb₁1 hb₂n
        refine ⟨y b₁, l₂, h₁, hl₂, ⟨ζ, hζ1, ?_⟩, hcube b₁ (y b₁) (hy b₁), ?_, ⟨l₁, hl₁, hl₁y⟩,
          fun b => ?_⟩
        · rw [hl₂w]
          calc y b₁ * (y b₂ * GeneralLinearGroup.scalar (Fin 3) v) * (y b₁)⁻¹ =
              y b₁ * y b₂ * (GeneralLinearGroup.scalar (Fin 3) v * (y b₁)⁻¹) := by group
            _ = y b₁ * y b₂ * ((y b₁)⁻¹ * GeneralLinearGroup.scalar (Fin 3) v) := by rw [hsc]
            _ = (y b₁ * y b₂ * (y b₁)⁻¹) * GeneralLinearGroup.scalar (Fin 3) v := by group
            _ = _ := by rw [hheis]; group
        · refine hcube b₂ l₂ fun m => ?_
          rw [hy b₂, hl₂y]
        · obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup (hBc b₁ b₂)
            (htop ▸ Subgroup.mem_top b)
          refine ⟨i, j, fun m => ?_⟩
          rw [map_mul, map_zpow, map_zpow, hl₂y]
          exact conjAct_mul (conjAct_zpow (hy b₁) i) (conjAct_zpow (hy b₂) j) m
      · exact Or.inr (hPcase b₂ b₁ hb₂1 hb₁n h₂)
    · exact Or.inr (hPcase b₁ b₂ hb₁1 hb₂n h₁)

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
