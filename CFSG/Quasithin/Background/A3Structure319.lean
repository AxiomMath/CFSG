module

public import CFSG.Quasithin.Background.A3Structure319Defs
public import CFSG.Quasithin.Background.A3Structure318

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank

theorem A319.three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  have := Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (m := 2) (k := n) (even_iff_two_dvd.1 hn)
  simpa using this

theorem a319 (hF : A318Facts) (hS : A319Facts) {H : Type} [Group H] [Finite H]
    (hH : SQTKGroup H) (h36 : A36Statement (H ⧸ CFSG.pCore 2 H))
    (h38 : A38Part3 (H ⧸ CFSG.pCore 2 H)) {L : Subgroup H} (hL : L ∈ cComp (⊤ : Subgroup H))
    {V : Subgroup H} (hVn : V.Normal) (hV : IsElemAbelian 2 V) (hHyp : A319Hyp L V) :
    L = oPrimeResidualOf 3 (⊤ : Subgroup H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHyp0 := hHyp
  obtain ⟨n, s, K, _, _, φ, hn, hKn, -, -, -⟩ := hHyp
  obtain ⟨hsl1, hsl2, hsl3⟩ := hS.sl3
  have hK4 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hKn
      omega
    obtain ⟨m, hm⟩ := hn
    rw [hKn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3dvd : 3 ∣ Nat.card K - 1 := by
    rw [hKn]
    exact A319.three_dvd_two_pow_sub_one hn
  have hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm (hsl1 K hK4)
  have hrank : 1 < CFSG.Open.pRank 3 L := by
    have h1 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 3 K)) := hsl3 K h3dvd
    have h2 := pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) φ
    have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (G := ↥L) (p := 2))
      rw [hk]
      intro h
      have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    have h3 := pRank_quotient_eq (p := 3) (CFSG.pCore 2 ↥L) hN
    have h4 := pRank_top_subtype (p := 3) L
    omega
  have hLn : L.Normal :=
    A318.normal_of_pRank_gt_one hH h38 hL Nat.prime_three (by norm_num) hrank
  have hconc : A318Conclusion 3 L :=
    a318 hF hH h36 h38 hL hQ Nat.prime_three (by norm_num) hrank
  have hcore := hS.core H hH L V hL hLn hQ hVn hV hHyp0 hconc
  have h3elts : ∀ k : ℕ, ∀ x : H, orderOf x = 3 ^ k → x ∈ L := by
    intro k
    induction k with
    | zero =>
      intro x hx
      rw [pow_zero, orderOf_eq_one_iff] at hx
      rw [hx]
      exact L.one_mem
    | succ k ih =>
      intro x hx
      have hx3 : x ^ 3 ∈ L := by
        apply ih
        rw [orderOf_pow_of_dvd (by norm_num) (hx ▸ dvd_pow_self 3 (Nat.succ_ne_zero k)), hx,
          pow_succ, Nat.mul_div_cancel _ (by norm_num)]
      exact hcore x ⟨k + 1, hx⟩ hx3
  have hle1 : oPrimeResidualOf 3 (⊤ : Subgroup H) ≤ L := by
    refine (Subgroup.closure_le L).2 ?_
    rintro x ⟨-, k, hk⟩
    exact h3elts k x hk
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hL
  have hΛ := A318.closure_orderThree_eq (hsl1 K hK4) (hsl2 K) (hsl3 K h3dvd)
  have hLt : Subgroup.closure {y : ↥L ⧸ CFSG.pCore 2 ↥L | orderOf y = 3} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ Subgroup.closure {y : ↥(StatedSL 3 K) | orderOf y = 3} :=
      hΛ ▸ Subgroup.mem_top _
    have key := Subgroup.closure_induction
      (p := fun (y : ↥(StatedSL 3 K)) _ =>
        φ.symm y ∈ Subgroup.closure {z : ↥L ⧸ CFSG.pCore 2 ↥L | orderOf z = 3})
      (fun y hy => Subgroup.subset_closure (by
        show orderOf (φ.symm y) = 3
        exact (orderOf_injective φ.symm.toMonoidHom φ.symm.injective y).trans hy))
      (by simp)
      (fun y₁ y₂ _ _ h₁ h₂ => by simpa using Subgroup.mul_mem _ h₁ h₂)
      (fun y _ h => by simpa using Subgroup.inv_mem _ h) hx
    simpa using key
  have : L.Normal := hLn
  let Gen : Set H := {x | x ∈ L ∧ ∃ k : ℕ, orderOf x = 3 ^ k}
  have hGenconj : ∀ g x : H, x ∈ Gen → g * x * g⁻¹ ∈ Gen := fun g x hx =>
    A318.conj_mem_pElements g hx
  have hTn : (Subgroup.closure Gen).Normal := A318.normal_closure_of_conj hGenconj
  have hTL : Subgroup.closure Gen ≤ L := (Subgroup.closure_le L).2 fun x hx => hx.1
  have hK2 : Group.IsSolvable ↥((CFSG.pCore 2 ↥L).map L.subtype) := by
    have hP : IsPGroup 2 ↥((CFSG.pCore 2 ↥L).map L.subtype) :=
      IsPGroup.map CFSG.pCore_isPGroup L.subtype
    have : Group.IsNilpotent ↥((CFSG.pCore 2 ↥L).map L.subtype) := hP.isNilpotent
    infer_instance
  have hP : ∀ y ∈ Subgroup.closure {z : ↥L ⧸ CFSG.pCore 2 ↥L | orderOf z = 3},
      ∃ l' : ↥L, QuotientGroup.mk l' = y ∧ (l' : H) ∈ Subgroup.closure Gen := by
    intro y hy
    refine Subgroup.closure_induction
      (p := fun y _ => ∃ l' : ↥L, QuotientGroup.mk l' = y ∧ (l' : H) ∈ Subgroup.closure Gen)
      ?_ ?_ ?_ ?_ hy
    · intro y hy3
      obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨x, ⟨j, hj⟩, hx, -⟩ := A318.exists_pElement_lift (p := 3)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l₀ ⟨1, by simpa using hy3⟩
      refine ⟨x, hx, Subgroup.subset_closure ⟨x.2, j, ?_⟩⟩
      rw [Subgroup.orderOf_coe]
      exact hj
    · exact ⟨1, rfl, Subgroup.one_mem _⟩
    · rintro y₁ y₂ _ _ ⟨a, ha, hat⟩ ⟨b, hb, hbt⟩
      exact ⟨a * b, by rw [QuotientGroup.mk_mul, ha, hb], Subgroup.mul_mem _ hat hbt⟩
    · rintro y _ ⟨a, ha, hat⟩
      exact ⟨a⁻¹, by rw [QuotientGroup.mk_inv, ha], Subgroup.inv_mem _ hat⟩
  have hLle : L ≤ Subgroup.closure Gen ⊔ (CFSG.pCore 2 ↥L).map L.subtype := by
    intro l hl
    obtain ⟨l', hl', hl'T⟩ := hP (QuotientGroup.mk ⟨l, hl⟩) (hLt ▸ Subgroup.mem_top _)
    have hmem : l'⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.1 hl'
    have : l = (l' : H) * ((l'⁻¹ * ⟨l, hl⟩ : ↥L) : H) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hl'T ⟨_, hmem, rfl⟩
  have hLeq : L = Subgroup.closure Gen := A318.eq_of_le_sup_solvable hperf hTL hK2 hLle
  refine le_antisymm ?_ hle1
  rw [hLeq]
  exact Subgroup.closure_mono fun x hx => ⟨Subgroup.mem_top _, hx.2⟩

end CFSG.Quasithin
