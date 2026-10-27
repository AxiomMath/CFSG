module

public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveBase
public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveDih
public import CFSG.LocalAnalysis.WeakClosure81.FiveFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma b5_FiveFiveAb_conj_mem {H X : Subgroup G} (hXH : X ≤ H)
    (hXn : (X.subgroupOf H).Normal) {g x : G} (hg : g ∈ H) (hx : x ∈ X) :
    g * x * g⁻¹ ∈ X := by
  have h := hXn.conj_mem ⟨x, hXH hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

private lemma b5_FiveFiveAb_normal_of_conj_mem {H X A F : Subgroup G} (hXH : X ≤ H)
    (hAH : A ≤ H) (hXn : (X.subgroupOf H).Normal) (hHXA : H = X ⊔ A)
    (hXF : ∀ x ∈ X, ∀ f ∈ F, x * f * x⁻¹ ∈ F)
    (hAF : ∀ b ∈ A, ∀ f ∈ F, b * f * b⁻¹ ∈ F) :
    (F.subgroupOf H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨b, hbA, x, hxX, hg_eq⟩ := exists_mul_of_eq_sup_of_normal hXH hAH hXn hHXA g.2
  have h1 : x * (n : G) * x⁻¹ ∈ F := hXF x hxX (n : G) hn
  have h2 : b * (x * (n : G) * x⁻¹) * b⁻¹ ∈ F := hAF b hbA _ h1
  have key : ((g * n * g⁻¹ : ↥H) : G) = b * (x * (n : G) * x⁻¹) * b⁻¹ := by
    have hg' : (g : G) = b * x := hg_eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg']
    group
  rw [key]
  exact h2

theorem five_five_abelian {H M A X : Subgroup G} (h : Sec5Hyp H M A) (hM : maxOver H A = {M})
    (hA : ¬ A ≤ pCoreOf 2 H) (hK : kerMOf M H = ⊥) (hX : IsMinNormalOver H ⊥ X)
    (hab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    Nat.card A = 2 ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ Nonempty (↥H ≃* DihedralGroup p) := by
  obtain ⟨hXbotlt, hXH, hXn, hmin⟩ := hX
  have hXbot : X ≠ ⊥ := bot_lt_iff_ne_bot.mp hXbotlt
  have hAH : A ≤ H := h.le_group
  have hAM : A ≤ M := h.le_M
  have hO2 : pCoreOf 2 H = ⊥ := pCoreOf_two_eq_bot_of_maxOver_eq_singleton h hM hK
  have hHXA : H = X ⊔ A :=
    five_four_one hM (by rw [hK]; exact ⟨hXbotlt, hXH, hXn, hmin⟩)
  have ha2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have h := h.isElemAbelian.2 a ha
    rwa [pow_two] at h
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA1 : ∃ a ∈ A, a ≠ 1 := by
    rw [hO2] at hA
    obtain ⟨a, haA, ha⟩ := SetLike.not_le_iff_exists.mp hA
    exact ⟨a, haA, fun h1 => ha (Subgroup.mem_bot.mpr h1)⟩
  have hcardX_ne_one : Nat.card X ≠ 1 := fun hc => hXbot (Subgroup.card_eq_one.mp hc)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcardX_ne_one
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₀, hx₀order⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hpdvd
  let Y : Subgroup G :=
    { carrier := {x | x ∈ X ∧ x ^ p = 1}
      one_mem' := ⟨X.one_mem, by simp⟩
      mul_mem' := by
        intro a b ha hb
        exact ⟨X.mul_mem ha.1 hb.1, by
          rw [Commute.mul_pow (hab a ha.1 b hb.1) p, ha.2, hb.2, one_mul]⟩
      inv_mem' := by
        intro a ha
        exact ⟨X.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hYX : Y ≤ X := fun x hx => hx.1
  have hYn : (Y.subgroupOf H).Normal := by
    refine b5_FiveFiveAb_normal_of_conj_mem hXH hAH hXn hHXA ?_ ?_
    · intro x hxX f hfY
      rw [show x * f * x⁻¹ = f by rw [hab x hxX f hfY.1]; group]
      exact hfY
    · intro b hbA f hfY
      refine ⟨b5_FiveFiveAb_conj_mem hXH hXn (hAH hbA) hfY.1, ?_⟩
      rw [conj_pow, hfY.2]
      group
  have hx₀_mem : (x₀ : G) ∈ Y := by
    refine ⟨x₀.2, ?_⟩
    have h1 : x₀ ^ p = 1 := by rw [← hx₀order]; exact pow_orderOf_eq_one x₀
    simpa using congrArg Subtype.val h1
  have hx₀_ne : (x₀ : G) ≠ 1 := by
    intro h1
    have h2 : x₀ = 1 := Subtype.ext h1
    have h3 : orderOf x₀ = 1 := by rw [h2]; exact orderOf_one
    rw [hx₀order] at h3
    exact hp.ne_one h3
  have hYbot : Y ≠ ⊥ := by
    intro h
    have : (x₀ : G) ∈ (⊥ : Subgroup G) := by rw [← h]; exact hx₀_mem
    exact hx₀_ne (Subgroup.mem_bot.mp this)
  have hYXeq : Y = X := by
    rcases hmin Y bot_le hYX hYn with h | h
    · exact absurd h hYbot
    · exact h
  have hXp : ∀ x ∈ X, x ^ p = 1 := by
    intro x hx
    have : x ∈ Y := by rw [hYXeq]; exact hx
    exact this.2
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hXpgroup : IsPGroup 2 X := by
      intro g
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have h : (g : G) ^ 2 = 1 := by rw [← hp2]; exact hXp g g.2
      simpa using h
    have hXle : X ≤ pCoreOf 2 H :=
      le_pCoreOf_of_isPGroup_of_normal hXH hXn hXpgroup
    rw [hO2] at hXle
    exact hXbot (le_bot_iff.mp hXle)
  have hodd : Odd p := hp.odd_of_ne_two hp_ne_two
  have hodd2 : ∀ x : G, x ^ 2 = 1 → x ^ p = 1 → x = 1 := by
    intro x h2 hpx
    obtain ⟨k, rfl⟩ := hodd
    rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hpx
    exact hpx
  have hCA : ∀ c ∈ A, (∀ x ∈ X, c * x = x * c) → c = 1 := by
    intro c hcA hc
    let C : Subgroup G := A ⊓ Subgroup.centralizer (X : Set G)
    have hCH : C ≤ H := inf_le_left.trans hAH
    have hCM : C ≤ M := inf_le_left.trans hAM
    have hCn : (C.subgroupOf H).Normal := by
      refine b5_FiveFiveAb_normal_of_conj_mem hXH hAH hXn hHXA ?_ ?_
      · intro x hxX f hfC
        have hcomm : x * f = f * x := (Subgroup.mem_centralizer_iff.mp hfC.2) x hxX
        rw [show x * f * x⁻¹ = f by rw [hcomm]; group]
        exact hfC
      · intro b hbA f hfC
        rw [show b * f * b⁻¹ = f by rw [hAc b hbA f hfC.1]; group]
        exact hfC
    have hCle : C ≤ kerMOf M H := le_kerMOf_of_normal hCH hCn hCM
    rw [hK] at hCle
    have hcC : c ∈ C :=
      ⟨hcA, Subgroup.mem_centralizer_iff.mpr fun x hx => (hc x hx).symm⟩
    exact Subgroup.mem_bot.mp (hCle hcC)
  have hfix : ∀ a ∈ A, a ≠ 1 → ∀ y ∈ X, a * y = y * a → y = 1 := by
    intro a haA ha1 y hyX hycomm
    let F : Subgroup G := X ⊓ Subgroup.centralizer ({a} : Set G)
    have hFX : F ≤ X := inf_le_left
    have hFn : (F.subgroupOf H).Normal := by
      refine b5_FiveFiveAb_normal_of_conj_mem hXH hAH hXn hHXA ?_ ?_
      · intro x hxX f hfF
        have hcomm : x * f = f * x := hab x hxX f hfF.1
        rw [show x * f * x⁻¹ = f by rw [hcomm]; group]
        exact hfF
      · intro b hbA f hfF
        refine ⟨b5_FiveFiveAb_conj_mem hXH hXn (hAH hbA) hfF.1, ?_⟩
        have hfa : Commute f a := Subgroup.mem_centralizer_singleton_iff.mp hfF.2
        have hba : Commute b a := hAc b hbA a haA
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Commute.mul_left (Commute.mul_left hba hfa) hba.inv_left).eq
    rcases hmin F bot_le hFX hFn with h | h
    · have hyF : y ∈ F :=
        ⟨hyX, Subgroup.mem_centralizer_singleton_iff.mpr hycomm.symm⟩
      have : y ∈ (⊥ : Subgroup G) := by rw [← h]; exact hyF
      exact Subgroup.mem_bot.mp this
    · exfalso
      apply ha1
      apply hCA a haA
      intro x hxX
      have hxF : x ∈ F := by rw [h]; exact hxX
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxF.2).symm
  have hinv : ∀ a ∈ A, a ≠ 1 → ∀ x ∈ X, a * x * a⁻¹ = x⁻¹ := by
    intro a haA ha1 x hxX
    have ha : a * a = 1 := ha2 a haA
    have hzX : a * x * a⁻¹ ∈ X := b5_FiveFiveAb_conj_mem hXH hXn (hAH haA) hxX
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have haz : a * (a * x * a⁻¹) * a⁻¹ = x := by
      rw [hainv]
      calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
        _ = x := by rw [ha]; simp
    have hy : x * (a * x * a⁻¹) = 1 := by
      apply hfix a haA ha1 _ (X.mul_mem hxX hzX)
      have h1 : a * (x * (a * x * a⁻¹)) * a⁻¹ = x * (a * x * a⁻¹) := by
        calc a * (x * (a * x * a⁻¹)) * a⁻¹
            = (a * x * a⁻¹) * (a * (a * x * a⁻¹) * a⁻¹) := by group
          _ = (a * x * a⁻¹) * x := by rw [haz]
          _ = x * (a * x * a⁻¹) := hab _ hzX _ hxX
      exact mul_inv_eq_iff_eq_mul.1 h1
    exact eq_inv_of_mul_eq_one_right hy
  obtain ⟨a, haA, ha1⟩ := hA1
  have hAeq : A = Subgroup.zpowers a := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.mpr haA)
    intro b hbA
    by_cases hb1 : b = 1
    · rw [hb1]; exact Subgroup.one_mem _
    · have hab_ne : a * b = 1 := by
        by_contra hne
        have hmem : a * b ∈ A := A.mul_mem haA hbA
        have hxin : ∀ x ∈ X, x = 1 := by
          intro x hxX
          have hconj1 : (a * b) * x * (a * b)⁻¹ = x⁻¹ := hinv (a * b) hmem hne x hxX
          have hconj2 : (a * b) * x * (a * b)⁻¹ = x := by
            calc (a * b) * x * (a * b)⁻¹
                = a * (b * x * b⁻¹) * a⁻¹ := by group
              _ = a * x⁻¹ * a⁻¹ := by rw [hinv b hbA hb1 x hxX]
              _ = (a * x * a⁻¹)⁻¹ := by group
              _ = (x⁻¹)⁻¹ := by rw [hinv a haA ha1 x hxX]
              _ = x := by simp
          have hx_inv : x⁻¹ = x := by rw [← hconj1, hconj2]
          have hx2 : x ^ 2 = 1 := by
            rw [pow_two]
            calc x * x = x⁻¹ * x := by rw [hx_inv]
              _ = 1 := inv_mul_cancel x
          exact hodd2 x hx2 (hXp x hxX)
        have hXle : X ≤ ⊥ := fun x hx => Subgroup.mem_bot.mpr (hxin x hx)
        exact hXbot (le_bot_iff.mp hXle)
      have hb_eq : b = a := by
        rw [eq_inv_of_mul_eq_one_right hab_ne, inv_eq_of_mul_eq_one_right (ha2 a haA)]
      rw [hb_eq]; exact Subgroup.mem_zpowers a
  have horder_a : orderOf a = 2 := by
    haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
    have ha_sq : a ^ 2 = 1 := by rw [pow_two]; exact ha2 a haA
    exact orderOf_eq_prime ha_sq ha1
  have hcardA : Nat.card A = 2 := by
    rw [hAeq, Nat.card_zpowers, horder_a]
  obtain ⟨x₀, hx₀X, hx₀ne⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    have hXle : X ≤ ⊥ := by
      intro x hx
      rw [Subgroup.mem_bot]
      by_contra hxne
      exact h ⟨x, hx, hxne⟩
    exact hXbot (le_bot_iff.mp hXle)
  let Z : Subgroup G := Subgroup.zpowers x₀
  have hZX : Z ≤ X := Subgroup.zpowers_le.mpr hx₀X
  have hZn : (Z.subgroupOf H).Normal := by
    refine b5_FiveFiveAb_normal_of_conj_mem hXH hAH hXn hHXA ?_ ?_
    · intro x hxX z hzZ
      have hzX : z ∈ X := hZX hzZ
      rw [show x * z * x⁻¹ = z by rw [hab x hxX z hzX]; group]
      exact hzZ
    · intro b hbA z hzZ
      by_cases hb1 : b = 1
      · rw [hb1]; simpa using hzZ
      · have hzX : z ∈ X := hZX hzZ
        rw [hinv b hbA hb1 z hzX]
        exact Z.inv_mem hzZ
  have hZbot : Z ≠ ⊥ := by
    intro h
    have : x₀ ∈ (⊥ : Subgroup G) := by rw [← h]; exact Subgroup.mem_zpowers x₀
    exact hx₀ne (Subgroup.mem_bot.mp this)
  have hZXeq : Z = X := by
    rcases hmin Z bot_le hZX hZn with h | h
    · exact absurd h hZbot
    · exact h
  have hXcard : Nat.card X = p := by
    have horder_x₀ : orderOf x₀ = p := by
      rcases Nat.Prime.eq_one_or_self_of_dvd hp (orderOf x₀)
          (orderOf_dvd_of_pow_eq_one (hXp x₀ hx₀X)) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hx₀ne
      · exact h1
    have hZcard : Nat.card Z = p := by
      show Nat.card (Subgroup.zpowers x₀) = p
      rw [Nat.card_zpowers, horder_x₀]
    rw [← hZXeq]
    exact hZcard
  have haX : a ∉ X := by
    intro haXmem
    refine ha1 (hodd2 a ?_ (hXp a haXmem))
    rw [pow_two]; exact ha2 a haA
  have hH_eq : H = X ⊔ Subgroup.zpowers a := by rw [hHXA, hAeq]
  refine ⟨hcardA, p, hp, hodd, ?_⟩
  exact nonempty_mulEquiv_dihedralGroup_of_inverts (H := H) (X := X) hp hXcard hH_eq
    (ha2 a haA) haX (hinv a haA ha1)

end CFSG.LocalAnalysis.WeakClosure81
