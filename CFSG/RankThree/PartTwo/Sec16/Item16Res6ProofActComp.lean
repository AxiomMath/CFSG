module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res6ProofActFit
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res6Act

open CFSG CFSG.Blueprint

theorem three_le_pRank_of_commuting {X : Type} [Group X] [Finite X] {x₁ x₂ x₃ : X}
    (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c23 : Commute x₂ x₃)
    (hind : ∀ e₁ e₂ e₃ : ℤ, x₁ ^ e₁ * x₂ ^ e₂ * x₃ ^ e₃ = 1 →
      (5 : ℤ) ∣ e₁ ∧ (5 : ℤ) ∣ e₂ ∧ (5 : ℤ) ∣ e₃) :
    3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let θf : (Fin 3 → ℤ) → X := fun n => x₁ ^ n 0 * x₂ ^ n 1 * x₃ ^ n 2
  have hθmul : ∀ n m : Fin 3 → ℤ, θf (n + m) = θf n * θf m := by
    intro n m
    simp only [θf, Pi.add_apply, zpow_add]
    have h1 : Commute (x₃ ^ n 2) (x₁ ^ m 0) := (c13.zpow_zpow (m 0) (n 2)).symm
    have h2 : Commute (x₂ ^ n 1) (x₁ ^ m 0) := (c12.zpow_zpow (m 0) (n 1)).symm
    have h3 : Commute (x₃ ^ n 2) (x₂ ^ m 1) := (c23.zpow_zpow (m 1) (n 2)).symm
    calc x₁ ^ n 0 * x₁ ^ m 0 * (x₂ ^ n 1 * x₂ ^ m 1) * (x₃ ^ n 2 * x₃ ^ m 2)
        = x₁ ^ n 0 * (x₁ ^ m 0 * x₂ ^ n 1) * x₂ ^ m 1 * x₃ ^ n 2 * x₃ ^ m 2 := by group
      _ = x₁ ^ n 0 * (x₂ ^ n 1 * x₁ ^ m 0) * x₂ ^ m 1 * x₃ ^ n 2 * x₃ ^ m 2 := by rw [h2.eq]
      _ = x₁ ^ n 0 * x₂ ^ n 1 * x₁ ^ m 0 * (x₂ ^ m 1 * x₃ ^ n 2) * x₃ ^ m 2 := by group
      _ = x₁ ^ n 0 * x₂ ^ n 1 * x₁ ^ m 0 * (x₃ ^ n 2 * x₂ ^ m 1) * x₃ ^ m 2 := by rw [h3.eq]
      _ = x₁ ^ n 0 * x₂ ^ n 1 * (x₁ ^ m 0 * x₃ ^ n 2) * x₂ ^ m 1 * x₃ ^ m 2 := by group
      _ = x₁ ^ n 0 * x₂ ^ n 1 * (x₃ ^ n 2 * x₁ ^ m 0) * x₂ ^ m 1 * x₃ ^ m 2 := by rw [h1.eq]
      _ = x₁ ^ n 0 * x₂ ^ n 1 * x₃ ^ n 2 * (x₁ ^ m 0 * x₂ ^ m 1 * x₃ ^ m 2) := by group
  let θ : Multiplicative (Fin 3 → ℤ) →* X :=
    { toFun := fun n => θf (Multiplicative.toAdd n)
      map_one' := by simp [θf]
      map_mul' := fun a b => hθmul _ _ }
  have hθ : ∀ n : Fin 3 → ℤ, θ (Multiplicative.ofAdd n) = x₁ ^ n 0 * x₂ ^ n 1 * x₃ ^ n 2 :=
    fun _ => rfl
  set A := θ.range with hA
  have hAc : ∀ a b : A, a * b = b * a := by
    rintro ⟨_, n, rfl⟩ ⟨_, m, rfl⟩
    apply Subtype.ext
    change θ n * θ m = θ m * θ n
    rw [← map_mul, ← map_mul, mul_comm n m]
  let pw : A →* A :=
    { toFun := fun a => a ^ 5
      map_one' := one_pow _
      map_mul' := fun a b => (show Commute a b from hAc a b).mul_pow 5 }
  have hθ5 : ∀ n : Fin 3 → ℤ, θ (Multiplicative.ofAdd n) ^ 5 =
      θ (Multiplicative.ofAdd ((5 : ℤ) • n)) := by
    intro n
    rw [← map_pow]
    congr 1
  let emb : (Fin 3 → Fin 5) → A ⧸ pw.range := fun e =>
    ((⟨θ (Multiplicative.ofAdd fun i => ((e i : ℕ) : ℤ)), ⟨_, rfl⟩⟩ : A) : A ⧸ pw.range)
  have hemb : Function.Injective emb := by
    intro e e' hee
    simp only [emb, QuotientGroup.eq] at hee
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hee
    have hn' := congrArg Subtype.val hn
    simp only [pw, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv] at hn'
    obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective n
    rw [hθ5, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add] at hn'
    have h1 : θ (Multiplicative.ofAdd ((5 : ℤ) • n - (-(fun i => ((e i : ℕ) : ℤ)) +
        fun i => ((e' i : ℕ) : ℤ)))) = 1 := by
      rw [sub_eq_add_neg, ofAdd_add, map_mul, hn', ofAdd_neg, map_inv, mul_inv_cancel]
    rw [hθ] at h1
    obtain ⟨d0, d1, d2⟩ := hind _ _ _ h1
    funext i
    apply Fin.ext
    have key : ∀ j : Fin 3, (5 : ℤ) ∣ (5 : ℤ) * n j - (-((e j : ℕ) : ℤ) + ((e' j : ℕ) : ℤ)) := by
      intro j
      fin_cases j
      · simpa using d0
      · simpa using d1
      · simpa using d2
    have hi := key i
    have hi' : (5 : ℤ) ∣ ((e' i : ℕ) : ℤ) - ((e i : ℕ) : ℤ) := by
      have h5 : (5 : ℤ) ∣ (5 : ℤ) * n i := dvd_mul_right 5 _
      have := dvd_sub h5 hi
      simpa [sub_sub_cancel_left, sub_eq_add_neg, add_comm] using this
    have he := (e i).isLt
    have he' := (e' i).isLt
    omega
  have hquot : 125 ≤ Nat.card (A ⧸ pw.range) := by
    have h := Nat.card_le_card_of_injective emb hemb
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin,
      Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h
    norm_num at h
    exact h
  have hker : Nat.card pw.ker = Nat.card (A ⧸ pw.range) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup pw.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup pw.range
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange pw).toEquiv] at h1
    have hpos : 0 < Nat.card pw.range := Nat.card_pos
    rw [h1, mul_comm] at h2
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  set Ω := pw.ker.map A.subtype with hΩ
  have hΩcard : Nat.card Ω = Nat.card pw.ker := by
    rw [hΩ, Subgroup.card_map_of_injective A.subtype_injective]
  have hΩexp : ∀ x ∈ Ω, x ^ 5 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : a ^ 5 = 1 := ha
    simpa using congrArg Subtype.val h1
  have hΩel : CFSG.Assembly.IsElemAbelian 5 Ω := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, hΩexp⟩
    obtain ⟨a', -, ha'⟩ := a.2
    obtain ⟨b', -, hb'⟩ := b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← ha', ← hb']
    exact congrArg Subtype.val (hAc a' b')
  have hΩp : IsPGroup 5 Ω := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hΩexp x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΩp
  have hk3 : 3 ≤ k := by
    have h125 : 5 ^ 3 ≤ 5 ^ k := by
      rw [← hk, hΩcard, hker]
      norm_num
      exact hquot
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h125
  exact hk3.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hΩel hk)

section Components


theorem five_dvd_of_suzukiModel {S : Type} [Group S] {f : ℕ} (h : SuzukiModel S 2 f) :
    5 ∣ Nat.card S := by
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  refine Dvd.dvd.mul_left ?_ _
  have h4 : (2 ^ (2 * a + 1)) ^ 2 = 4 * 16 ^ a := by
    rw [← pow_mul, show (2 * a + 1) * 2 = 4 * a + 2 by ring, pow_add, pow_mul]
    norm_num
    ring
  rw [h4]
  have h16 : 16 ^ a % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

theorem suzukiModel_of_component {X : Type} [Group X] [Finite X] (hK : CFSG.IsKGroup X)
    (h3 : ¬ 3 ∣ Nat.card X) {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    ∃ f : ℕ, SuzukiModel (↥J ⧸ Subgroup.center ↥J) 2 f := by
  have hsimp : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.1.2.1
  have hcat : CFSG.Assembly.InCatalog (↥J ⧸ Subgroup.center ↥J) :=
    hK J (Subgroup.center ↥J) hsimp
  have h3J : ¬ 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := fun h =>
    h3 ((h.trans (Subgroup.card_quotient_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card J))
  exact KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd _ hJ.1.2.2 hcat h3J

theorem exists_five_of_component {X : Type} [Group X] [Finite X] (hK : CFSG.IsKGroup X)
    (h3 : ¬ 3 ∣ Nat.card X) {J : Subgroup X} (hJ : CFSG.IsComponent J) :
    ∃ x : ↥J, orderOf (x : ↥J ⧸ Subgroup.center ↥J) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨f, hf⟩ := suzukiModel_of_component hK h3 hJ
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 (five_dvd_of_suzukiModel hf)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨x, hy⟩

end Components

theorem mk_eq_one_of_commute {X : Type*} [Group X] {J : Subgroup X} {z : X} (hz : z ∈ J)
    (hc : ∀ y ∈ J, z * y = y * z) :
    ((⟨z, hz⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) = 1 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact (hc y y.2).symm

theorem three_le_pRank_of_components {X : Type} [Group X] [Finite X] {J₁ J₂ J₃ : Subgroup X}
    (h1 : CFSG.IsComponent J₁) (h2 : CFSG.IsComponent J₂) (h3 : CFSG.IsComponent J₃)
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃) {x₁ : ↥J₁} {x₂ : ↥J₂} {x₃ : ↥J₃}
    (hx₁ : orderOf (x₁ : ↥J₁ ⧸ Subgroup.center ↥J₁) = 5)
    (hx₂ : orderOf (x₂ : ↥J₂ ⧸ Subgroup.center ↥J₂) = 5)
    (hx₃ : orderOf (x₃ : ↥J₃ ⧸ Subgroup.center ↥J₃) = 5) :
    3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) := by
  have hcomm : ∀ {A B : Subgroup X}, CFSG.IsComponent A → CFSG.IsComponent B → A ≠ B →
      ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro A B hA hB hAB a ha b hb
    rcases CFSG.LocalCores.distinct_components_commute hA hB with h | h
    · exact absurd h hAB
    · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  have c12 : Commute (x₁ : X) x₂ := hcomm h1 h2 h12 _ x₁.2 _ x₂.2
  have c13 : Commute (x₁ : X) x₃ := hcomm h1 h3 h13 _ x₁.2 _ x₃.2
  have c23 : Commute (x₂ : X) x₃ := hcomm h2 h3 h23 _ x₂.2 _ x₃.2
  have hdiv : ∀ {J : Subgroup X} {x : ↥J}, orderOf (x : ↥J ⧸ Subgroup.center ↥J) = 5 →
      ∀ e : ℤ, (∀ y ∈ J, (x : X) ^ e * y = y * (x : X) ^ e) → (5 : ℤ) ∣ e := by
    intro J x hx e hc
    have hz := mk_eq_one_of_commute (J := J) (z := (x : X) ^ e) (zpow_mem x.2 e) hc
    have hz' : ((x ^ e : ↥J) : ↥J ⧸ Subgroup.center ↥J) = 1 := by
      rw [← hz]
      congr 1
    rw [QuotientGroup.mk_zpow] at hz'
    have := orderOf_dvd_iff_zpow_eq_one.mpr hz'
    rwa [hx] at this
  refine three_le_pRank_of_commuting c12 c13 c23 fun e₁ e₂ e₃ he => ⟨?_, ?_, ?_⟩
  ·
    refine hdiv hx₁ e₁ fun y hy => ?_
    have heq : (x₁ : X) ^ e₁ = ((x₂ : X) ^ e₂ * (x₃ : X) ^ e₃)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact he)
    rw [heq]
    have hy2 : (x₂ : X) ^ e₂ * y = y * (x₂ : X) ^ e₂ :=
      (hcomm h1 h2 h12 y hy _ (zpow_mem x₂.2 e₂)).symm
    have hy3 : (x₃ : X) ^ e₃ * y = y * (x₃ : X) ^ e₃ :=
      (hcomm h1 h3 h13 y hy _ (zpow_mem x₃.2 e₃)).symm
    have hc : Commute ((x₂ : X) ^ e₂ * (x₃ : X) ^ e₃) y :=
      (show Commute _ y from hy2).mul_left hy3
    exact hc.inv_left.eq
  ·
    refine hdiv hx₂ e₂ fun y hy => ?_
    have heq : (x₂ : X) ^ e₂ = ((x₁ : X) ^ e₁)⁻¹ * ((x₃ : X) ^ e₃)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact eq_inv_of_mul_eq_one_right (by rw [← mul_assoc]; exact he)
    rw [heq]
    have hy1 : (x₁ : X) ^ e₁ * y = y * (x₁ : X) ^ e₁ :=
      hcomm h1 h2 h12 _ (zpow_mem x₁.2 e₁) y hy
    have hy3 : (x₃ : X) ^ e₃ * y = y * (x₃ : X) ^ e₃ :=
      (hcomm h2 h3 h23 y hy _ (zpow_mem x₃.2 e₃)).symm
    exact ((show Commute _ y from hy1).inv_left.mul_left
      (show Commute _ y from hy3).inv_left).eq
  ·
    refine hdiv hx₃ e₃ fun y hy => ?_
    have heq : (x₃ : X) ^ e₃ = ((x₁ : X) ^ e₁ * (x₂ : X) ^ e₂)⁻¹ :=
      eq_inv_of_mul_eq_one_right he
    rw [heq]
    have hy1 : (x₁ : X) ^ e₁ * y = y * (x₁ : X) ^ e₁ :=
      hcomm h1 h3 h13 _ (zpow_mem x₁.2 e₁) y hy
    have hy2 : (x₂ : X) ^ e₂ * y = y * (x₂ : X) ^ e₂ :=
      hcomm h2 h3 h23 _ (zpow_mem x₂.2 e₂) y hy
    exact ((show Commute _ y from hy1).mul_left (show Commute _ y from hy2)).inv_left.eq

theorem map_eq_of_perfect {X S : Type} [Group X] [Finite X] [Group S] [Group.IsPerfect S]
    (φ : S →* MulAut X) (hrank5 : CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 2)
    (H5 : ∀ J' : Subgroup X, CFSG.IsComponent J' →
      ∃ x : ↥J', orderOf (x : ↥J' ⧸ Subgroup.center ↥J') = 5)
    {J : Subgroup X} (hJ : CFSG.IsComponent J) (s : S) : J.map (φ s).toMonoidHom = J := by
  classical
  by_contra hne
  set J₂ := J.map (φ s).toMonoidHom with hJ₂def
  have hcomp : ∀ t, CFSG.IsComponent (J.map (φ t).toMonoidHom) := fun t =>
    CFSG.LocalCores.isComponent_map_mulEquiv (φ t) hJ
  have hmapmul : ∀ a b : S, J.map (φ (a * b)).toMonoidHom =
      (J.map (φ b).toMonoidHom).map (φ a).toMonoidHom := by
    intro a b
    rw [Subgroup.map_map, map_mul]
    rfl
  have hinj : ∀ (a : S) {A B : Subgroup X}, A.map (φ a).toMonoidHom = B.map (φ a).toMonoidHom →
      A = B := fun a A B h => Subgroup.map_injective (φ a).injective h
  by_cases hthree : ∃ t, J.map (φ t).toMonoidHom ≠ J ∧ J.map (φ t).toMonoidHom ≠ J₂
  · obtain ⟨t, ht1, ht2⟩ := hthree
    obtain ⟨x₁, hx₁⟩ := H5 J hJ
    obtain ⟨x₂, hx₂⟩ := H5 J₂ (hcomp s)
    obtain ⟨x₃, hx₃⟩ := H5 _ (hcomp t)
    have := three_le_pRank_of_components hJ (hcomp s) (hcomp t) (Ne.symm hne) (Ne.symm ht1)
      (Ne.symm ht2) hx₁ hx₂ hx₃
    omega
  · push Not at hthree
    have hpair : ∀ a : S, J₂.map (φ a).toMonoidHom = J ∨ J₂.map (φ a).toMonoidHom = J₂ := by
      intro a
      rw [hJ₂def, ← hmapmul]
      by_cases h : J.map (φ (a * s)).toMonoidHom = J
      · exact Or.inl h
      · exact Or.inr (hthree _ h)
    let g : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1
    let χf : S → Multiplicative (ZMod 2) := fun a =>
      if J.map (φ a).toMonoidHom = J then 1 else g
    have hg2 : g * g = 1 := by decide
    have hχmul : ∀ a b, χf (a * b) = χf a * χf b := by
      intro a b
      simp only [χf]
      by_cases hb : J.map (φ b).toMonoidHom = J
      · rw [hmapmul, hb, ite_eq_left rfl, mul_one]
      · have hb2 : J.map (φ b).toMonoidHom = J₂ := hthree b hb
        rw [hmapmul, hb2, ite_eq_right hne]
        by_cases ha : J.map (φ a).toMonoidHom = J
        · have h1 : J₂.map (φ a).toMonoidHom ≠ J := by
            intro h
            rw [← ha] at h
            exact hne (hinj a h)
          rw [ite_eq_right h1, ite_eq_left ha, one_mul]
        · have ha2 : J.map (φ a).toMonoidHom = J₂ := hthree a ha
          have h1 : J₂.map (φ a).toMonoidHom = J := by
            rcases hpair a with h | h
            · exact h
            · exfalso
              exact hne (hinj a (h.trans ha2.symm))
          rw [ite_eq_left h1, ite_eq_right ha, hg2]
    let χ : S →* Multiplicative (ZMod 2) :=
      { toFun := χf
        map_one' := by
          simp only [χf, map_one]
          rw [ite_eq_left]
          ext x
          simp
        map_mul' := hχmul }
    have h1 := CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one χ
    have h2 : χf s = 1 := by
      have := congrArg (fun f : S →* Multiplicative (ZMod 2) => f s) h1
      exact this
    simp only [χf] at h2
    rw [ite_eq_right (show ¬ J.map (φ s).toMonoidHom = J from hne)] at h2
    exact absurd h2 (by decide)

section FixComponent


theorem fix_component {X S : Type} [Group X] [Finite X] [Group S] [Finite S] (hS : ActHyp S)
    (φ : S →* MulAut X) (hK : CFSG.IsKGroup X) (h3 : ¬ 3 ∣ Nat.card X)
    (hrank5 : CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 2) {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (s : S) {x : X} (hx : x ∈ J) : φ s x = x := by
  obtain ⟨hSp, hS3, -⟩ := hS
  have := hSp
  have hJinv : ∀ t, J.map (φ t).toMonoidHom = J := map_eq_of_perfect φ hrank5
    (fun J' hJ' => exists_five_of_component hK h3 hJ') hJ
  set ρ := restrictAct φ J hJinv with hρ
  refine fix_of_range_eq_bot φ J hJinv ?_ s hx
  obtain ⟨f, hf⟩ := suzukiModel_of_component hK h3 hJ
  have : Group.IsPerfect ↥J := hJ.1.1
  have hcyc := ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity _ 2 f hf).2
    ↥J ⟨MulEquiv.refl _⟩).1
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J) :=
    Group.isSolvable_of_comm fun a b => by
      have := IsCyclic.isMulCommutative
        (α := CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J)
      exact mul_comm' a b
  have hinner : ρ.range ≤ (MulAut.conj : ↥J →* MulAut ↥J).range := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨j, hj⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner ρ t
    exact ⟨j, hj.symm⟩
  refine hS3 _ ρ fun h3ρ => h3 ?_
  have h1 : Nat.card ρ.range ∣ Nat.card (MulAut.conj : ↥J →* MulAut ↥J).range :=
    Subgroup.card_dvd_of_le hinner
  have h2 : Nat.card (MulAut.conj : ↥J →* MulAut ↥J).range ∣ Nat.card ↥J := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  exact (h3ρ.trans h1).trans (h2.trans (Subgroup.card_subgroup_dvd_card J))

end FixComponent

end CFSG.RankThree.PartTwo.Sec16.Res6Act
