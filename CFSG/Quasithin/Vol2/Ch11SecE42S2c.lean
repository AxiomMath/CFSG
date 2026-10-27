module

public import CFSG.Quasithin.Vol2.Ch11SecE42S2b
public import CFSG.Quasithin.Vol2.Ch11SecE42A36

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem inf_lOf_le_pCoreOf (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hn : n = 2) {K : Subgroup G} (hLK : LOf L V₁ ≤ K) :
    oTwoTwoPrime K ⊓ LOf L V₁ ≤ pCoreOf 2 (LOf L V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_lOf_iso h1110 h hV₁ hn
  set L₁ := LOf L V₁ with hL₁
  set O := oTwoTwoPrime K with hO
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥L₁) with hmk
  set A : Subgroup ↥L₁ := (O ⊓ L₁).subgroupOf L₁ with hA
  have hKO : K ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans (SecD.normalizer_le_normalizer_oTwoTwoPrime K)
  have hAn : A.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
    fun l hl => SecD.mem_normalizer_inf (hKO (hLK hl)) (Subgroup.le_normalizer hl)
  have hO2L : pCoreOf 2 K ⊓ L₁ ≤ pCoreOf 2 L₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun l hl => SecD.mem_normalizer_inf
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (hLK hl)) (Subgroup.le_normalizer hl))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left)
  have hmkO2 : ∀ a : ↥L₁, (a : G) ∈ pCoreOf 2 L₁ → mk a = 1 := by
    intro a ha
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← SecD.pCoreOf_subgroupOf]
    exact ha
  set M := A.map mk with hM
  have hMn : M.Normal := hAn.map mk (QuotientGroup.mk'_surjective _)
  have hModd : Odd (Nat.card M) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 2 h2
    obtain ⟨a, ha, hax⟩ := x.2
    obtain ⟨j, o, ho, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
    have hao : mk (a ^ o) = 1 := by
      apply hmkO2
      refine hO2L ⟨SecD.mem_pCoreOf_of_mem_oTwoTwoPrime (k := j) ?_ ?_, (a ^ o).2⟩
      · exact (Subgroup.pow_mem _ (Subgroup.mem_subgroupOf.mp ha) o).1
      · rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
        rfl
    have hx1 : (x : ↥(L₁) ⧸ CFSG.pCore 2 ↥L₁) ^ o = 1 := by
      rw [← hax, ← map_pow, hao]
    have hx2 : (x : ↥(L₁) ⧸ CFSG.pCore 2 ↥L₁) ^ 2 = 1 := by
      have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
      simp only [hx] at h1
      exact congrArg Subtype.val h1
    have hx3 : (x : ↥(L₁) ⧸ CFSG.pCore 2 ↥L₁) = 1 := by
      have hd1 := orderOf_dvd_of_pow_eq_one hx1
      have hd2 := orderOf_dvd_of_pow_eq_one hx2
      have hcop : Nat.Coprime o 2 := Nat.coprime_two_right.mpr ho
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
    have : x = 1 := Subtype.ext hx3
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hNodd : Odd (Nat.card (M.map e.toMonoidHom)) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  have hN := eq_bot_of_normal_odd_sl2_four hF (hMn.map e.toMonoidHom e.surjective) hNodd
  have hM0 : M = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : e x ∈ M.map e.toMonoidHom := ⟨x, hx, rfl⟩
    rw [hN, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (by simpa using this)
  intro x hx
  have hxA : (⟨x, hx.2⟩ : ↥L₁) ∈ A := Subgroup.mem_subgroupOf.mpr hx
  have h1 : mk ⟨x, hx.2⟩ = 1 := by
    have : mk ⟨x, hx.2⟩ ∈ M := ⟨_, hxA, rfl⟩
    rwa [hM0, Subgroup.mem_bot] at this
  rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← SecD.pCoreOf_subgroupOf] at h1
  exact h1

theorem commutator_lOf_eq_top (L V₁ : Subgroup G) : commutator ↥(LOf L V₁) = ⊤ := by
  apply Subgroup.map_injective (LOf L V₁).subtype_injective
  rw [Subgroup.map_subtype_commutator, perfectCore_perfect, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem exists_neg_one_mem_pCoreOf
    (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hn : n = 2) {K : Subgroup G} (hLK : LOf L V₁ ≤ K) {p : ℕ}
    [Fact p.Prime] (h11 : 11 ≤ p) (φ : ↥K →* SL(2, ZMod p))
    (hφk : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoTwoPrime K) :
    ∃ r ∈ pCoreOf 2 (LOf L V₁), ∃ hrK : r ∈ K, φ ⟨r, hrK⟩ = A1c.sl2NegOne p := by
  set ψ : ↥(LOf L V₁) →* SL(2, ZMod p) := φ.comp (Subgroup.inclusion hLK) with hψ
  have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      commutator_lOf_eq_top]
  have hne : ψ.range ≠ ⊥ := by
    intro h0
    apply lOf_not_le_oTwoTwoPrime h1110 h hV₁ (K := K)
    intro l hl
    have h1 : ψ ⟨l, hl⟩ = 1 := by
      have : ψ ⟨l, hl⟩ ∈ ψ.range := ⟨_, rfl⟩
      rwa [h0, Subgroup.mem_bot] at this
    exact (hφk _).mp h1
  have hneg : A1c.sl2NegOne p ∈ ψ.range := by
    rcases Dickson.perfect_subgroup_sl2_prime (by omega) hperf hne with htop | ⟨-, -, -, hneg, -⟩
    · rw [htop]
      exact Subgroup.mem_top _
    · exact hneg
  obtain ⟨l, hl⟩ := hneg
  obtain ⟨j, o, ho, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  have hψl : ψ (l ^ o) = A1c.sl2NegOne p := by
    rw [map_pow, hl]
    obtain ⟨m, rfl⟩ := ho
    rw [pow_succ, pow_mul, pow_two, A1c.sl2NegOne_mul_self, one_pow, one_mul]
  set l₂ : ↥(LOf L V₁) := l ^ o with hl₂
  have hφl₂ : φ ⟨(l₂ : G), hLK l₂.2⟩ = A1c.sl2NegOne p := hψl
  have hsc : (l₂ : G) ∈ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) := by
    refine ⟨Subgroup.le_normalizer l₂.2,
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (Subgroup.le_normalizer l₂.2),
      fun x hx => ?_⟩
    apply inf_lOf_le_pCoreOf h1110 h hV₁ hn hLK
    refine ⟨?_, (LOf L V₁).mul_mem ((LOf L V₁).mul_mem ((LOf L V₁).mul_mem l₂.2 hx)
      ((LOf L V₁).inv_mem l₂.2)) ((LOf L V₁).inv_mem hx)⟩
    have hφc : φ (⟨(l₂ : G), hLK l₂.2⟩ * ⟨x, hLK hx⟩ * ⟨(l₂ : G), hLK l₂.2⟩⁻¹ *
        ⟨x, hLK hx⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hφl₂,
        ← A1c.sl2NegOne_comm (φ ⟨x, hLK hx⟩)]
      group
    exact (hφk _).mp hφc
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_lOf_iso h1110 h hV₁ hn
  have hmem := SecB.inf_sectionCentralizer_le (n := 2) (show Nat.card F = 2 ^ 2 from hF)
    (by norm_num) e ⟨l₂.2, hsc⟩
  exact ⟨l₂, hmem, hLK l₂.2, hφl₂⟩

theorem inf_normalizer_le_rOf (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {p : ℕ} [Fact p.Prime]
    (φ : ↥K →* SL(2, ZMod p))
    (hinv : ∀ k : ↥K, φ k = A1c.sl2NegOne p → ∀ o : ↥K, (o : G) ∈ oTwoTwoPrime K →
      ((k * o * k⁻¹ * o : ↥K) : G) ∈ pCoreOf 2 K)
    {r : G} (hrR : r ∈ ROf T L V₁) (hrK : r ∈ K) (hφr : φ ⟨r, hrK⟩ = A1c.sl2NegOne p) :
    oTwoTwoPrime K ⊓ Subgroup.normalizer (ROf T L V₁ : Set G) ≤ ROf T L V₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro o ho
  obtain ⟨hoO, hoN⟩ := ho
  have hoK : o ∈ K := SecD.oTwoTwoPrime_le K hoO
  set Q := pCoreOf 2 K with hQ
  have hKO : K ≤ Subgroup.normalizer (oTwoTwoPrime K : Set G) :=
    Subgroup.le_normalizer.trans (SecD.normalizer_le_normalizer_oTwoTwoPrime K)
  have hc1 : o * r * o⁻¹ * r⁻¹ ∈ ROf T L V₁ :=
    (ROf T L V₁).mul_mem ((Subgroup.mem_normalizer_iff.mp hoN r).mp hrR) ((ROf T L V₁).inv_mem hrR)
  have hc2 : o * r * o⁻¹ * r⁻¹ ∈ oTwoTwoPrime K := by
    have e : o * r * o⁻¹ * r⁻¹ = o * (r * o⁻¹ * r⁻¹) := by group
    rw [e]
    exact (oTwoTwoPrime K).mul_mem hoO
      ((Subgroup.mem_normalizer_iff.mp (hKO hrK) _).mp ((oTwoTwoPrime K).inv_mem hoO))
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (LOf L V₁ ⊔ T))
    ⟨_, hc1⟩
  have hcQ : o * r * o⁻¹ * r⁻¹ ∈ Q :=
    SecD.mem_pCoreOf_of_mem_oTwoTwoPrime hc2 (k := k) (by simpa using congrArg Subtype.val hk)
  have hi : r * o * r⁻¹ * o ∈ Q := by
    have := hinv ⟨r, hrK⟩ hφr ⟨o, hoK⟩ hoO
    simpa using this
  have ho2 : o ^ 2 ∈ Q := by
    have e : o ^ 2 = (o * r * o⁻¹ * r⁻¹) * (r * o * r⁻¹ * o) := by
      rw [pow_two]
      group
    rw [e]
    exact Q.mul_mem hcQ hi
  obtain ⟨j, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos o).ne'
  have hom : o ^ m ∈ Q := SecD.mem_pCoreOf_of_mem_oTwoTwoPrime
    ((oTwoTwoPrime K).pow_mem hoO m) (k := j)
    (by rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one])
  have hoQ : o ∈ Q := mem_of_pow_mem_of_coprime (Nat.coprime_two_left.mpr hm) ho2 hom
  exact pCoreOf_le_rOf' h hLK hTK hoQ

end CFSG.Quasithin.Vol2.Ch11.SecE
