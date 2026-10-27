module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42A
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42S6
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Sec44
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81Prop33
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81J
public import CFSG.RankThree.PartTwo.Sec21.FF81P51
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open P51 (V e)
open P51T
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem isPGroup_three_zpowers {y : G} {k : ℕ} (h : y ^ 3 ^ k = 1) :
    IsPGroup 3 (Subgroup.zpowers y) := by
  rintro ⟨g, hg⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

theorem exists_three_decomp (d : G) : ∃ d₁ ∈ Subgroup.zpowers d, ∃ d₂ ∈ Subgroup.zpowers d,
    d = d₁ * d₂ ∧ Nat.Coprime 3 (orderOf d₁) ∧ ∃ k : ℕ, d₂ ^ 3 ^ k = 1 := by
  have hn : orderOf d ≠ 0 := (orderOf_pos d).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  have hco : Nat.Coprime (3 ^ a) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)
  have hbez := Nat.gcd_eq_gcd_ab (3 ^ a) m
  rw [hco.gcd_eq_one, Nat.cast_one] at hbez
  set u := Nat.gcdA (3 ^ a) m
  set v := Nat.gcdB (3 ^ a) m
  have hd : d ^ ((orderOf d : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  refine ⟨d ^ ((3 ^ a : ℕ) * u : ℤ), Subgroup.zpow_mem_zpowers _ _,
    d ^ ((m : ℕ) * v : ℤ), Subgroup.zpow_mem_zpowers _ _, ?_, ?_, a, ?_⟩
  · rw [← zpow_add, ← hbez, zpow_one]
  · have h1 : (d ^ ((3 ^ a : ℕ) * u : ℤ)) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul,
        show ((3 ^ a : ℕ) * u : ℤ) * (m : ℤ) = ((orderOf d : ℕ) : ℤ) * u by
          rw [hnm]; push_cast; ring, zpow_mul, hd, one_zpow]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h1)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm)
  · rw [← zpow_natCast, ← zpow_mul,
      show ((m : ℕ) * v : ℤ) * ((3 ^ a : ℕ) : ℤ) = ((orderOf d : ℕ) : ℤ) * v by
        rw [hnm]; push_cast; ring, zpow_mul, hd, one_zpow]

theorem FF81Basis.cen_dec (hB : FF81Basis b L B b₁ b₂ b₃) {y : G} (hy : y ∈ Cen b) :
    ∃ o ∈ Opp 3 (Cen b), ∃ i : ℤ, ∃ l ∈ L, y = o * b ^ i * l := by
  obtain ⟨l, hlL, hd⟩ := hB.hyp.exists_decomp hy
  obtain ⟨d₁, h1, d₂, h2, hdd, hco, k, hk⟩ := exists_three_decomp (l⁻¹ * y)
  have hD : ∀ z ∈ Subgroup.zpowers (l⁻¹ * y), z ∈ Cen b ⊓ CenS L := fun z hz =>
    (Subgroup.zpowers_le.mpr hd) hz
  have hd₁ := hB.mem_opp_of_mem_cen_inf (hD _ h1) hco
  have hd₂ : d₂ ∈ Subgroup.zpowers b :=
    hB.mem_zpowers_of_isPGroup (hD _ h2).1 (hD _ h2).2 (isPGroup_three_zpowers hk)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hd₂
  refine ⟨d₁, hd₁, i, l, hlL, ?_⟩
  have hcomm : l * (l⁻¹ * y) = (l⁻¹ * y) * l := Subgroup.mem_centralizer_iff.mp hd.2 l hlL
  calc y = l * (l⁻¹ * y) := by group
    _ = (l⁻¹ * y) * l := hcomm
    _ = d₁ * b ^ i * l := by rw [hdd, hi]

theorem FF81Basis.b_comm (hB : FF81Basis b L B b₁ b₂ b₃) {l : G} (hl : l ∈ L) : b * l = l * b :=
  (Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hl)).symm

theorem FF81Basis.opp_mem_cen (hB : FF81Basis b L B b₁ b₂ b₃) {o l : G}
    (ho : o ∈ Opp 3 (Cen b)) (hl : l ∈ L) : o ∈ Cen l :=
  Subgroup.mem_centralizer_singleton_iff.mpr (hB.opp_comm ho hl)

section Coord

variable [IsElementaryAbelian 3 B] (β : Module.Basis (Fin 4) (ZMod 3) (Additive B))

theorem cvG_zpow {g : G} (hg : g ∈ B) (k : ℤ) : cvG β (g ^ k) = k • cvG β g := by
  rw [cvG_of_mem β (B.zpow_mem hg k), cvG_of_mem β hg, ← cv_zpow]; rfl

theorem cvG_pow {g : G} (hg : g ∈ B) (k : ℕ) : cvG β (g ^ k) = k • cvG β g := by
  have := cvG_zpow β hg k
  rwa [zpow_natCast, natCast_zsmul] at this

theorem cvG_gens {c₀ c₁ c₂ c₃ : G}
    (hβ : ∀ i, ((Additive.toMul (β i) : B) : G) = ![c₀, c₁, c₂, c₃] i) :
    cvG β c₀ = e 0 ∧ cvG β c₁ = e 1 ∧ cvG β c₂ = e 2 ∧ cvG β c₃ = e 3 := by
  have h : ∀ i, cvG β (![c₀, c₁, c₂, c₃] i) = e i := fun i => by
    rw [← hβ i, cvG_of_mem β (Additive.toMul (β i)).2]
    exact cv_basis β i
  exact ⟨h 0, h 1, h 2, h 3⟩

end Coord

theorem vec_fix_or_swap : ∀ v : V, (∃ i : Fin 4, ∃ c : ZMod 3, v = c • e i) →
    (∃ i : Fin 4, ∃ c : ZMod 3, -v + e 0 + e 2 = c • e i) → v = e 0 ∨ v = e 2 := by
  decide

theorem vec_line_one : ∀ k j : ZMod 3, (∃ i : Fin 4, ∃ c : ZMod 3,
    k • e 1 + j • (e 0 + e 2) = c • e i) → j = 0 := by
  decide

theorem vec_line_three : ∀ k j : ZMod 3, (∃ i : Fin 4, ∃ c : ZMod 3,
    k • e 3 + j • (e 0 + e 2) = c • e i) → j = 0 := by
  decide

theorem vec_mono : ∀ k j : ZMod 3, (∃ i : Fin 4, ∃ c : ZMod 3, k • e 1 + j • e 3 = c • e i) →
    k • e 1 + j • e 3 ≠ 0 →
    k • e 1 + j • e 3 = e 1 ∨ k • e 1 + j • e 3 = -e 1 ∨ k • e 1 + j • e 3 = e 3 ∨
      k • e 1 + j • e 3 = -e 3 := by
  decide

section Sec4

variable {t₀ : G} (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀)
include h4

theorem FF81Sec4.b3 : b ^ 3 = 1 := h4.basis.hyp.b_cube

theorem FF81Sec4.conj_b : (∃ g : G, g * b * g⁻¹ = b₁) ∧ (∃ g : G, g * b * g⁻¹ = b₂) ∧
    ∃ g : G, g * b * g⁻¹ = b₃ := by
  obtain ⟨-, -, -, ⟨τ, -, hτ0, -⟩, ⟨c, -, hc0, hc1, hc2, -⟩⟩ := h4.caseI.1.1
  exact ⟨⟨τ, hτ0⟩, ⟨c * c, by rw [show c * c * b * (c * c)⁻¹ = c * (c * b * c⁻¹) * c⁻¹ by group,
    hc0, hc1]⟩, ⟨c * c * c, by
      rw [show c * c * c * b * (c * c * c)⁻¹ = c * (c * (c * b * c⁻¹) * c⁻¹) * c⁻¹ by group,
        hc0, hc1, hc2]⟩⟩

theorem FF81Sec4.exists_coord : haveI := h4.basis.mono.1.1
    ∃ β : Module.Basis (Fin 4) (ZMod 3) (Additive B),
      cvG β b = e 0 ∧ cvG β b₁ = e 1 ∧ cvG β b₂ = e 2 ∧ cvG β b₃ = e 3 := by
  haveI := h4.basis.mono.1.1
  obtain ⟨β, hβ⟩ := exists_basis (B := B) (by rw [h4.basis.mono.1.2]) h4.basis.mono.2.1
  exact ⟨β, cvG_gens β hβ⟩

theorem FF81Sec4.cvG_line [IsElementaryAbelian 3 B] (β : Module.Basis (Fin 4) (ZMod 3) (Additive B))
    (hβ : cvG β b = e 0 ∧ cvG β b₁ = e 1 ∧ cvG β b₂ = e 2 ∧ cvG β b₃ = e 3)
    {y : G} (hyB : y ∈ B) (hy : ∃ g : G, g * b * g⁻¹ = y) :
    ∃ i : Fin 4, ∃ c : ZMod 3, cvG β y = c • e i := by
  obtain ⟨g, hg⟩ := hy
  have hmem : Subgroup.zpowers y ∈ ConjLines B b :=
    ⟨Subgroup.zpowers_le.mpr hyB, g, by rw [conjBy_zpowers, hg]⟩
  rw [h4.caseI.2] at hmem
  obtain ⟨hbB, hb1B, hb2B, hb3B⟩ := h4.basis.mem
  have key : ∀ (x : G) (i : Fin 4), x ∈ B → cvG β x = e i → Subgroup.zpowers y =
      Subgroup.zpowers x → ∃ i : Fin 4, ∃ c : ZMod 3, cvG β y = c • e i := by
    intro x i hxB hx hyx
    have : y ∈ Subgroup.zpowers x := by rw [← hyx]; exact Subgroup.mem_zpowers y
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp this
    exact ⟨i, (k : ZMod 3), by rw [cvG_zpow β hxB, hx, Int.cast_smul_eq_zsmul]⟩
  rcases hmem with h | h | h | h
  · exact key b 0 hbB hβ.1 h
  · exact key b₁ 1 hb1B hβ.2.1 h
  · exact key b₂ 2 hb2B hβ.2.2.1 h
  · exact key b₃ 3 hb3B hβ.2.2.2 (Set.mem_singleton_iff.mp h)

theorem FF81Sec4.eq_of_conj_pair {y : G} (hyB : y ∈ B) (hy : ∃ g : G, g * b * g⁻¹ = y)
    (hy' : ∃ g : G, g * b * g⁻¹ = y⁻¹ * (b * b₂)) : y = b ∨ y = b₂ := by
  haveI := h4.basis.mono.1.1
  obtain ⟨β, hβ⟩ := h4.exists_coord
  obtain ⟨hbB, -, hb2B, -⟩ := h4.basis.mem
  have hy'B : y⁻¹ * (b * b₂) ∈ B := B.mul_mem (B.inv_mem hyB) (B.mul_mem hbB hb2B)
  have h1 := h4.cvG_line β hβ hyB hy
  have h2 := h4.cvG_line β hβ hy'B hy'
  rw [cvG_mul β (B.inv_mem hyB) (B.mul_mem hbB hb2B), cvG_inv β hyB, cvG_mul β hbB hb2B,
    hβ.1, hβ.2.2.1, ← add_assoc] at h2
  rcases vec_fix_or_swap _ h1 h2 with h | h
  · exact Or.inl (cvG_inj β hyB hbB (by rw [h, hβ.1]))
  · exact Or.inr (cvG_inj β hyB hb2B (by rw [h, hβ.2.2.1]))

theorem FF81Sec4.b2_comm : b * b₂ = b₂ * b := h4.basis.b_comm h4.basis.hb₂

theorem FF81Sec4.fix_or_swap {u : G} (hu : u ∈ Cen (b * b₂))
    (hub : u * b * u⁻¹ ∈ Subgroup.closure {b, b₂}) :
    (u * b * u⁻¹ = b ∧ u * b₂ * u⁻¹ = b₂) ∨ (u * b * u⁻¹ = b₂ ∧ u * b₂ * u⁻¹ = b) := by
  obtain ⟨hbB, -, hb2B, -⟩ := h4.basis.mem
  have hEB : Subgroup.closure ({b, b₂} : Set G) ≤ B :=
    (Subgroup.closure_le B).mpr (by rintro _ (rfl | rfl); exacts [hbB, hb2B])
  have hux : u * (b * b₂) * u⁻¹ = b * b₂ := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hu]; group
  have hy' : u * b₂ * u⁻¹ = (u * b * u⁻¹)⁻¹ * (b * b₂) := by
    rw [← hux]; group
  obtain ⟨-, ⟨g₂, hg₂⟩, -⟩ := h4.conj_b
  have hc : ∃ g : G, g * b * g⁻¹ = (u * b * u⁻¹)⁻¹ * (b * b₂) :=
    ⟨u * g₂, by rw [← hy', ← hg₂]; group⟩
  rcases h4.eq_of_conj_pair (hEB hub) ⟨u, rfl⟩ hc with h | h
  · refine Or.inl ⟨h, ?_⟩
    rw [hy', h]; group
  · refine Or.inr ⟨h, ?_⟩
    rw [hy', h, h4.b2_comm]; group

theorem FF81Sec4.mem_zpowers_of_line {u c : G} (hc : c = b₁ ∨ c = b₃) (hu : u ∈ Cen (b * b₂))
    (huc : u * c * u⁻¹ ∈ Subgroup.closure {c, b * b₂}) : u * c * u⁻¹ ∈ Subgroup.zpowers c := by
  haveI := h4.basis.mono.1.1
  obtain ⟨β, hβ⟩ := h4.exists_coord
  obtain ⟨hbB, hb1B, hb2B, hb3B⟩ := h4.basis.mem
  obtain ⟨h1, -, h3, -, -, -⟩ := h4.basis.b_facts
  have hcB : c ∈ B := by rcases hc with h | h <;> rw [h]; exacts [hb1B, hb3B]
  have hc3 : c ^ 3 = 1 := by rcases hc with h | h <;> rw [h]; exacts [h1, h3]
  have hxB : b * b₂ ∈ B := B.mul_mem hbB hb2B
  have hcx : c * (b * b₂) = (b * b₂) * c := by
    have hcL : c ∈ L := by rcases hc with h | h <;> rw [h]; exacts [h4.basis.hb₁, h4.basis.hb₃]
    have e1 := h4.basis.b_comm hcL
    obtain ⟨-, -, -, h12, -, h23⟩ := h4.basis.b_facts
    rcases hc with h | h <;> rw [h] at e1 ⊢
    · rw [show b₁ * (b * b₂) = (b₁ * b) * b₂ by group, ← e1, mul_assoc, h12]; group
    · rw [show b₃ * (b * b₂) = (b₃ * b) * b₂ by group, ← e1, mul_assoc, ← h23]; group
  have hx3 : (b * b₂) ^ 3 = 1 := by
    rw [(Commute.mul_pow (show Commute b b₂ from h4.b2_comm) 3), h4.b3, h4.basis.b_facts.2.1,
      one_mul]
  obtain ⟨i, j, hij⟩ := exists_pow_mul_pow_of_mem_closure hcx hc3 hx3 huc
  obtain ⟨g, hg⟩ : ∃ g : G, g * b * g⁻¹ = c := by
    rcases hc with h | h <;> rw [h]
    exacts [h4.conj_b.1, h4.conj_b.2.2]
  have hline := h4.cvG_line β hβ (y := u * c * u⁻¹)
    (by rw [hij]; exact B.mul_mem (B.pow_mem hcB _) (B.pow_mem hxB _))
    ⟨u * g, by rw [show u * g * b * (u * g)⁻¹ = u * (g * b * g⁻¹) * u⁻¹ by group, hg]⟩
  rw [hij, cvG_mul β (B.pow_mem hcB _) (B.pow_mem hxB _), cvG_pow β hcB, cvG_pow β hxB,
    cvG_mul β hbB hb2B, hβ.1, hβ.2.2.1] at hline
  have hj : ((j : ℕ) : ZMod 3) = 0 := by
    have hline' : ∃ i' : Fin 4, ∃ c' : ZMod 3, ((i : ℕ) : ZMod 3) • cvG β c +
        ((j : ℕ) : ZMod 3) • (e 0 + e 2) = c' • e i' := by
      simpa only [Nat.cast_smul_eq_nsmul] using hline
    rcases hc with h | h <;> rw [h] at hline'
    · rw [hβ.2.1] at hline'; exact vec_line_one _ _ hline'
    · rw [hβ.2.2.2] at hline'; exact vec_line_three _ _ hline'
  obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff j 3).mp hj
  rw [hij, hm, pow_mul, hx3, one_pow, mul_one]
  exact Subgroup.npow_mem_zpowers c i

theorem FF81Sec4.mono_pair {w : G} (hw : w ∈ Subgroup.closure {b₁, b₃})
    (hwc : ∃ g : G, g * b * g⁻¹ = w) : w ∈ ({b₁, b₁⁻¹, b₃, b₃⁻¹} : Set G) := by
  haveI := h4.basis.mono.1.1
  obtain ⟨β, hβ⟩ := h4.exists_coord
  obtain ⟨hbB, hb1B, hb2B, hb3B⟩ := h4.basis.mem
  obtain ⟨h1, -, h3, -, h13, -⟩ := h4.basis.b_facts
  obtain ⟨i, j, hij⟩ := exists_pow_mul_pow_of_mem_closure h13 h1 h3 hw
  have hwB : w ∈ B := by rw [hij]; exact B.mul_mem (B.pow_mem hb1B _) (B.pow_mem hb3B _)
  have hline := h4.cvG_line β hβ hwB hwc
  have hcv : cvG β w = ((i : ℕ) : ZMod 3) • e 1 + ((j : ℕ) : ZMod 3) • e 3 := by
    rw [hij, cvG_mul β (B.pow_mem hb1B _) (B.pow_mem hb3B _), cvG_pow β hb1B, cvG_pow β hb3B,
      hβ.2.1, hβ.2.2.2]
    simp only [Nat.cast_smul_eq_nsmul]
  have hw1 : w ≠ 1 := by
    obtain ⟨g, rfl⟩ := hwc
    intro h
    have : b = 1 := by
      calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact h4.basis.hyp.b_ne_one this
  have hne : ((i : ℕ) : ZMod 3) • e 1 + ((j : ℕ) : ZMod 3) • e 3 ≠ 0 := by
    rw [← hcv]
    intro h0
    exact hw1 (cvG_inj β hwB B.one_mem (by rw [h0, cvG_one]))
  rw [hcv] at hline
  rcases vec_mono _ _ hline hne with h | h | h | h <;> rw [← hcv] at h
  · exact Or.inl (cvG_inj β hwB hb1B (by rw [h, hβ.2.1]))
  · exact Or.inr (Or.inl (cvG_inj β hwB (B.inv_mem hb1B) (by rw [h, cvG_inv β hb1B, hβ.2.1])))
  · exact Or.inr (Or.inr (Or.inl (cvG_inj β hwB hb3B (by rw [h, hβ.2.2.2]))))
  · exact Or.inr (Or.inr (Or.inr (cvG_inj β hwB (B.inv_mem hb3B)
      (by rw [h, cvG_inv β hb3B, hβ.2.2.2]))))

end Sec4

theorem mem_cen_of_conj {g x : G} (h : g * x * g⁻¹ = x) : g ∈ Cen x :=
  Subgroup.mem_centralizer_singleton_iff.mpr (by
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h])

theorem conj_of_mem_cen {g x : G} (h : g ∈ Cen x) : g * x * g⁻¹ = x := by
  rw [Subgroup.mem_centralizer_singleton_iff.mp h]; group

theorem conj_mem_zpowers {g x y z : G} (h : g * x * g⁻¹ = y) (hz : z ∈ Subgroup.zpowers x) :
    g * z * g⁻¹ ∈ Subgroup.zpowers y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← h]
  exact (map_zpow (MulAut.conj g) x k).symm

theorem eq_or_eq_inv_of_orderOf_three {x y : G} (hx : orderOf x = 3) (hy : y ∈ Subgroup.zpowers x)
    (hy1 : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hx] at hy1 ⊢
  have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  interval_cases h : k % ((3 : ℕ) : ℤ)
  · exact absurd (zpow_zero x) hy1
  · exact Or.inl (zpow_one x)
  · right
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hx3])

set_option maxRecDepth 100000 in
theorem perm_six_eq_one_of_comm : ∀ σ : Equiv.Perm (Fin 6),
    σ * Equiv.swap 0 1 = Equiv.swap 0 1 * σ → σ * Equiv.swap 0 2 = Equiv.swap 0 2 * σ →
    σ * Equiv.swap 0 3 = Equiv.swap 0 3 * σ → σ * Equiv.swap 0 4 = Equiv.swap 0 4 * σ →
    σ * Equiv.swap 0 5 = Equiv.swap 0 5 * σ → σ = 1 := by
  decide

theorem eq_one_of_central {J : Subgroup G} (φ : ↥J ≃* Equiv.Perm (Fin 6)) {z : G} (hz : z ∈ J)
    (hc : ∀ j ∈ J, z * j = j * z) : z = 1 := by
  have key : ∀ σ : Equiv.Perm (Fin 6), φ ⟨z, hz⟩ * σ = σ * φ ⟨z, hz⟩ := fun σ => by
    obtain ⟨⟨j, hj⟩, rfl⟩ := φ.surjective σ
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hc j hj))
  have h1 := perm_six_eq_one_of_comm _ (key _) (key _) (key _) (key _) (key _)
  have : (⟨z, hz⟩ : J) = 1 := φ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val this

theorem le_closure_of_involutions {J : Subgroup G} (φ : ↥J ≃* Equiv.Perm (Fin 6)) {S : Set G}
    (hS : ∀ j ∈ J, j * j = 1 → j ∈ S) : J ≤ Subgroup.closure S := by
  intro j hj
  set f : Equiv.Perm (Fin 6) →* G := J.subtype.comp φ.symm.toMonoidHom
  have h1 : φ ⟨j, hj⟩ ∈ Subgroup.closure {σ : Equiv.Perm (Fin 6) | σ.IsSwap} := by
    rw [Equiv.Perm.closure_isSwap]; trivial
  have h2 : f (φ ⟨j, hj⟩) ∈ (Subgroup.closure {σ : Equiv.Perm (Fin 6) | σ.IsSwap}).map f :=
    ⟨_, h1, rfl⟩
  rw [MonoidHom.map_closure] at h2
  have h3 : f (φ ⟨j, hj⟩) = j := by simp [f]
  rw [h3] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨σ, ⟨a, c, -, rfl⟩, rfl⟩
  refine hS _ (φ.symm _).2 ?_
  show ((φ.symm (Equiv.swap a c) : J) : G) * (φ.symm (Equiv.swap a c) : J) = 1
  rw [← Subgroup.coe_mul, ← map_mul, Equiv.swap_mul_self, map_one, Subgroup.coe_one]

theorem preserve_cen_pair {u : G}
    (h : (u * b * u⁻¹ = b ∧ u * b₂ * u⁻¹ = b₂) ∨ (u * b * u⁻¹ = b₂ ∧ u * b₂ * u⁻¹ = b)) :
    ∀ y ∈ Cen b ⊓ Cen b₂, u * y * u⁻¹ ∈ Cen b ⊓ Cen b₂ := by
  intro y hy
  have c1 := conj_commute (a := u) (Subgroup.mem_centralizer_singleton_iff.mp hy.1)
  have c2 := conj_commute (a := u) (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
  rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at c1; rw [e2] at c2
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr c1,
      Subgroup.mem_centralizer_singleton_iff.mpr c2⟩
  · rw [e1] at c1; rw [e2] at c2
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr c2,
      Subgroup.mem_centralizer_singleton_iff.mpr c1⟩

section Levi

variable {J : Subgroup G} (hJ : J ≤ L ⊓ Cen b₂)
  (hJdec : ∀ y ∈ L ⊓ Cen b₂, ∃ k : ℕ, ∃ j ∈ J, y = b₂ ^ k * j)
include hJ hJdec

theorem FF81Basis.inv_mem_J (hB : FF81Basis b L B b₁ b₂ b₃) {y : G} (hyb : y ∈ Cen b)
    (hyb₂ : y ∈ Cen b₂) (hy2 : y * y = 1) : y ∈ J := by
  have hyL : y ∈ L := hB.mem_of_pow_two hyb (k := 1) (by rw [pow_one, sq]; exact hy2)
  obtain ⟨k, j, hj, rfl⟩ := hJdec y ⟨hyL, hyb₂⟩
  have hjc : Commute j b₂ := Subgroup.mem_centralizer_singleton_iff.mp (hJ hj).2
  have hc : Commute (b₂ ^ k) j := (Commute.pow_left hjc.symm k)
  have h2 : b₂ ^ (k + k) = (j * j)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc b₂ ^ (k + k) * (j * j) = b₂ ^ k * j * (b₂ ^ k * j) := by
          rw [pow_add]; simp only [mul_assoc]; rw [← mul_assoc j, ← hc.eq, mul_assoc]
      _ = 1 := hy2
  have hb3 : b₂ ^ 3 = 1 := hB.b_facts.2.1
  have h4k : b₂ ^ k = b₂ ^ (k + k) * b₂ ^ (k + k) := by
    rw [← pow_add, show k + k + (k + k) = k + 3 * k by ring, pow_add, pow_mul, hb3, one_pow,
      mul_one]
  have hkJ : b₂ ^ k ∈ J := by
    rw [h4k, h2]; exact J.mul_mem (J.inv_mem (J.mul_mem hj hj)) (J.inv_mem (J.mul_mem hj hj))
  exact J.mul_mem hkJ hj

theorem FF81Basis.conj_mem_J (hB : FF81Basis b L B b₁ b₂ b₃) (φ : ↥J ≃* Equiv.Perm (Fin 6))
    {u : G}
    (h : (u * b * u⁻¹ = b ∧ u * b₂ * u⁻¹ = b₂) ∨ (u * b * u⁻¹ = b₂ ∧ u * b₂ * u⁻¹ = b))
    {j : G} (hj : j ∈ J) : u * j * u⁻¹ ∈ J := by
  have hJb : ∀ j ∈ J, j ∈ Cen b ⊓ Cen b₂ := fun j hj => ⟨hB.hyp.hLC (hJ hj).1, (hJ hj).2⟩
  have hle := le_closure_of_involutions φ
    (S := {y | y ∈ Cen b ⊓ Cen b₂ ∧ y * y = 1}) (fun j hj h2 => ⟨hJb j hj, h2⟩)
  refine conj_mem_of_closure (fun y hy => ?_) (hle hj)
  obtain ⟨hyc, hy2⟩ := hy
  have hc := preserve_cen_pair h y hyc
  refine hB.inv_mem_J hJ hJdec hc.1 hc.2 ?_
  calc u * y * u⁻¹ * (u * y * u⁻¹) = u * (y * y) * u⁻¹ := by group
    _ = 1 := by rw [hy2]; group

end Levi

theorem mem_nor_cen_of_conj {g x : G} (h : g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹) :
    g ∈ Nor (Cen x) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have c := conj_commute (a := g) (Subgroup.mem_centralizer_singleton_iff.mp hy)
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases h with e | e <;> rw [e] at c
  · exact c
  · exact (Commute.inv_right_iff.mp (show Commute (g * y * g⁻¹) x⁻¹ from c))

section Sec4T

variable {t₀ : G} (h4 : FF81Sec4 b L B b₁ b₂ b₃ t₀)
include h4

theorem FF81Sec4.b_ne_b₂ : b ≠ b₂ := by
  intro h
  have hb : b ∈ Subgroup.zpowers b ⊓ L := ⟨Subgroup.mem_zpowers b, h ▸ h4.basis.hb₂⟩
  rw [h4.basis.hyp.zpowers_inf_L, Subgroup.mem_bot] at hb
  exact h4.basis.hyp.b_ne_one hb

theorem FF81Sec4.exists_t {J : Subgroup G} (hJ : J ≤ L ⊓ Cen b₂) (φ : ↥J ≃* Equiv.Perm (Fin 6))
    (hb₁J : b₁ ∈ J) (hb₃J : b₃ ∈ J)
    (hJdec : ∀ y ∈ L ⊓ Cen b₂, ∃ k : ℕ, ∃ j ∈ J, y = b₂ ^ k * j) :
    ∃ t : G, orderOf t = 2 ∧ t * b * t⁻¹ = b₂ ∧ t * b₂ * t⁻¹ = b ∧ ∀ j ∈ J, t * j = j * t := by
  have hB := h4.basis
  obtain ⟨σ, hσ2, hσb, hσb₂, hσb₁, hσb₃⟩ := h4.exists_swap
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hσJ : ∀ j ∈ J, σ * j * σ⁻¹ ∈ J := fun j hj =>
    hB.conj_mem_J hJ hJdec φ (Or.inr ⟨hσb, hσb₂⟩) hj
  have hinvol : ∀ y : G, σ * (σ * y * σ⁻¹) * σ⁻¹ = y := fun y => by
    rw [hσinv]
    calc σ * (σ * y * σ) * σ = (σ * σ) * y * (σ * σ) := by group
      _ = y := by rw [hσ2]; group
  let α : ↥J ≃* ↥J :=
    { toFun := fun j => ⟨σ * j * σ⁻¹, hσJ j j.2⟩
      invFun := fun j => ⟨σ * j * σ⁻¹, hσJ j j.2⟩
      left_inv := fun j => Subtype.ext (hinvol j)
      right_inv := fun j => Subtype.ext (hinvol j)
      map_mul' := fun x y => Subtype.ext (by
        show σ * ((x : G) * y) * σ⁻¹ = σ * x * σ⁻¹ * (σ * y * σ⁻¹)
        group) }
  have hαapp : ∀ j : ↥J, ((α j : ↥J) : G) = σ * j * σ⁻¹ := fun j => rfl
  obtain ⟨h1, h2, h3, h12, h13, h23⟩ := hB.b_facts
  have hEJ : Subgroup.closure ({b₁, b₃} : Set G) ≤ J :=
    (Subgroup.closure_le J).mpr (by rintro _ (rfl | rfl); exacts [hb₁J, hb₃J])
  have hE9 : Nat.card (Subgroup.closure ({b₁, b₃} : Set G)) = 9 := by
    refine card_pair_of_card_triple h2 h1 h3 h13 h12.symm h23 ?_
    rw [show ({b₂, b₁, b₃} : Set G) = {b₁, b₂, b₃} from Set.insert_comm _ _ _, hB.elem.2]
    norm_num
  have hcardE : Nat.card ((Subgroup.closure ({b₁, b₃} : Set G)).subgroupOf J) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv, hE9]
  have hσE : Subgroup.closure ({b₁, b₃} : Set G) ≤ Cen σ := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h <;> rw [h]
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (mem_cen_of_conj hσb₁)).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (mem_cen_of_conj hσb₃)).symm
  have hα : ∀ x ∈ (Subgroup.closure ({b₁, b₃} : Set G)).subgroupOf J, α x = x := by
    intro x hx
    refine Subtype.ext ?_
    rw [hαapp]
    exact conj_of_mem_cen (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hσE (Subgroup.mem_subgroupOf.mp hx))).symm)
  obtain ⟨j₀, hj₀⟩ := mulAut_inner_of_fix_card_nine φ _ hcardE α hα
  have hj₀G : ∀ j ∈ J, σ * j * σ⁻¹ = (j₀ : G) * j * (j₀ : G)⁻¹ := fun j hj => by
    have := congrArg Subtype.val (hj₀ ⟨j, hj⟩)
    rw [hαapp] at this
    simpa using this
  have hj₀J : (j₀ : G) ∈ J := j₀.2
  have hj₀b₂ : (j₀ : G) * b₂ * (j₀ : G)⁻¹ = b₂ := conj_of_mem_cen (hJ hj₀J).2
  have hj₀b : (j₀ : G) * b * (j₀ : G)⁻¹ = b := conj_of_mem_cen (by
    have := hB.hyp.hLC (hJ hj₀J).1
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp this))
  have hj₀sq : (j₀ : G) * j₀ = 1 := by
    refine eq_one_of_central φ (J.mul_mem hj₀J hj₀J) fun j hj => ?_
    have e1 := hj₀G (σ * j * σ⁻¹) (hσJ j hj)
    rw [hinvol, hj₀G j hj] at e1
    calc (j₀ : G) * j₀ * j = (j₀ : G) * ((j₀ : G) * j * (j₀ : G)⁻¹) * (j₀ : G)⁻¹ *
          ((j₀ : G) * j₀) := by group
      _ = j * ((j₀ : G) * j₀) := by rw [← e1]
  refine ⟨(j₀ : G)⁻¹ * σ, ?_, ?_, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · have e1 := hj₀G ((j₀ : G)⁻¹) (J.inv_mem hj₀J)
      calc ((j₀ : G)⁻¹ * σ) ^ 2 = (j₀ : G)⁻¹ * (σ * (j₀ : G)⁻¹ * σ⁻¹) * (σ * σ) := by
            rw [sq]; group
        _ = ((j₀ : G) * j₀)⁻¹ := by rw [e1, hσ2]; group
        _ = 1 := by rw [hj₀sq, inv_one]
    · intro h1
      have : b = b₂ := by
        calc b = ((j₀ : G)⁻¹ * σ) * b * ((j₀ : G)⁻¹ * σ)⁻¹ := by rw [h1]; group
          _ = (j₀ : G)⁻¹ * (σ * b * σ⁻¹) * (j₀ : G) := by group
          _ = b₂ := by
              rw [hσb]
              calc (j₀ : G)⁻¹ * b₂ * j₀ = (j₀ : G)⁻¹ * ((j₀ : G) * b₂ * (j₀ : G)⁻¹) * j₀ := by
                    rw [hj₀b₂]
                _ = b₂ := by group
      exact h4.b_ne_b₂ this
  · calc ((j₀ : G)⁻¹ * σ) * b * ((j₀ : G)⁻¹ * σ)⁻¹ = (j₀ : G)⁻¹ * (σ * b * σ⁻¹) * j₀ := by group
      _ = (j₀ : G)⁻¹ * ((j₀ : G) * b₂ * (j₀ : G)⁻¹) * j₀ := by rw [hσb, hj₀b₂]
      _ = b₂ := by group
  · calc ((j₀ : G)⁻¹ * σ) * b₂ * ((j₀ : G)⁻¹ * σ)⁻¹ = (j₀ : G)⁻¹ * (σ * b₂ * σ⁻¹) * j₀ := by
          group
      _ = (j₀ : G)⁻¹ * ((j₀ : G) * b * (j₀ : G)⁻¹) * j₀ := by rw [hσb₂, hj₀b]
      _ = b := by group
  · intro j hj
    have e1 := hj₀G j hj
    calc (j₀ : G)⁻¹ * σ * j = (j₀ : G)⁻¹ * (σ * j * σ⁻¹) * σ := by group
      _ = (j₀ : G)⁻¹ * ((j₀ : G) * j * (j₀ : G)⁻¹) * σ := by rw [e1]
      _ = j * ((j₀ : G)⁻¹ * σ) := by group

theorem FF81Sec4.nor_line {c τ u : G} (hcL : c ∈ L) (hτb : τ * b * τ⁻¹ = c)
    (hτc : τ * c * τ⁻¹ = b) (hτ2 : τ * b₂ * τ⁻¹ = b₂)
    (hLevi : L ⊓ Cen (c * b₂) ≤ Nor (Subgroup.closure {c, b₂}))
    (hu : u ∈ Cen (b * b₂)) (huc : u * c * u⁻¹ ∈ Subgroup.zpowers c) :
    ∃ o ∈ conjBy τ (Opp 3 (Cen b)), ∃ n : G, u = o * n ∧ n ∈ Cen (b * b₂) ∧
      n * c * n⁻¹ ∈ Subgroup.zpowers c ∧ n * b * n⁻¹ ∈ Subgroup.closure {b, b₂} ∧
      n * b₂ * n⁻¹ ∈ Subgroup.closure {b, b₂} := by
  have hB := h4.basis
  have ib : τ⁻¹ * c * τ = b := by
    calc τ⁻¹ * c * τ = τ⁻¹ * (τ * b * τ⁻¹) * τ := by rw [hτb]
      _ = b := by group
  have ic : τ⁻¹ * b * τ = c := by
    calc τ⁻¹ * b * τ = τ⁻¹ * (τ * c * τ⁻¹) * τ := by rw [hτc]
      _ = c := by group
  have i2 : τ⁻¹ * b₂ * τ = b₂ := by
    calc τ⁻¹ * b₂ * τ = τ⁻¹ * (τ * b₂ * τ⁻¹) * τ := by rw [hτ2]
      _ = b₂ := by group
  have hux := conj_of_mem_cen hu
  set m := τ⁻¹ * u * τ with hmdef
  have hm1 : m * (c * b₂) * m⁻¹ = c * b₂ := by
    calc m * (c * b₂) * m⁻¹ = τ⁻¹ * (u * ((τ * c * τ⁻¹) * (τ * b₂ * τ⁻¹)) * u⁻¹) * τ := by
          rw [hmdef]; group
      _ = τ⁻¹ * (b * b₂) * τ := by rw [hτc, hτ2, hux]
      _ = (τ⁻¹ * b * τ) * (τ⁻¹ * b₂ * τ) := by group
      _ = c * b₂ := by rw [ic, i2]
  have hm2 : m * b * m⁻¹ ∈ Subgroup.zpowers b := by
    have : m * b * m⁻¹ = τ⁻¹ * (u * c * u⁻¹) * τ := by
      calc m * b * m⁻¹ = τ⁻¹ * (u * (τ * b * τ⁻¹) * u⁻¹) * τ := by rw [hmdef]; group
        _ = _ := by rw [hτb]
    rw [this]
    have := conj_mem_zpowers (g := τ⁻¹) (x := c) (y := b) (by rw [inv_inv]; exact ib) huc
    rwa [inv_inv] at this
  have hmb1 : m * b * m⁻¹ ≠ 1 := fun h => hB.hyp.b_ne_one (by
    calc b = m⁻¹ * (m * b * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨s, hsb, hsL, hsm⟩ : ∃ s : G, (s * b * s⁻¹ = b ∨ s * b * s⁻¹ = b⁻¹) ∧ s ∈ CenS L ∧
      (s * m) * b * (s * m)⁻¹ = b := by
    rcases eq_or_eq_inv_of_orderOf_three hB.hyp.ord hm2 hmb1 with h | h
    · exact ⟨1, Or.inl (by group), (CenS L).one_mem, by rw [one_mul, h]⟩
    · refine ⟨t₀, Or.inr h4.ht₀b, h4.ht₀L, ?_⟩
      calc t₀ * m * b * (t₀ * m)⁻¹ = t₀ * (m * b * m⁻¹) * t₀⁻¹ := by group
        _ = (t₀ * b * t₀⁻¹)⁻¹ := by rw [h]; group
        _ = b := by rw [h4.ht₀b, inv_inv]
  have hsc : ∀ y ∈ L, s * y * s⁻¹ = y := fun y hy => by
    have := Subgroup.mem_centralizer_iff.mp hsL y hy
    calc s * y * s⁻¹ = (y * s) * s⁻¹ := by rw [this]
      _ = y := by group
  have hcb₂L : c * b₂ ∈ L := L.mul_mem hcL hB.hb₂
  have hm' : s * m ∈ Cen b := mem_cen_of_conj hsm
  obtain ⟨o, ho, i, l, hl, hdec⟩ := hB.cen_dec hm'
  have hbi : b ^ i ∈ Cen (c * b₂) := (Cen (c * b₂)).zpow_mem
    (Subgroup.mem_centralizer_singleton_iff.mpr (hB.b_comm hcb₂L)) i
  have hoC : o ∈ Cen (c * b₂) := hB.opp_mem_cen ho hcb₂L
  have hsC : s ∈ Cen (c * b₂) := mem_cen_of_conj (hsc _ hcb₂L)
  have hsmC : s * m ∈ Cen (c * b₂) := (Cen _).mul_mem hsC (mem_cen_of_conj hm1)
  have hlC : l ∈ Cen (c * b₂) := by
    have : l = (o * b ^ i)⁻¹ * (s * m) := by rw [hdec]; group
    rw [this]; exact (Cen _).mul_mem ((Cen _).inv_mem ((Cen _).mul_mem hoC hbi)) hsmC
  have hlN := hLevi ⟨hl, hlC⟩
  have hsN : s⁻¹ ∈ Nor (Cen b) := Subgroup.inv_mem _ (mem_nor_cen_of_conj hsb)
  have ho' : s⁻¹ * o * s ∈ Opp 3 (Cen b) := by
    have := conj_mem_opp_of_mem_nor hsN ho
    rwa [inv_inv] at this
  set a := s⁻¹ * b ^ i with hadef
  have ha : ∀ y ∈ L, a * y * a⁻¹ = y := fun y hy => by
    have h1 : b ^ i * y * (b ^ i)⁻¹ = y := conj_of_mem_cen ((Cen y).zpow_mem
      (Subgroup.mem_centralizer_singleton_iff.mpr (hB.b_comm hy)) i)
    have h2 : s⁻¹ * y * s⁻¹⁻¹ = y := by
      calc s⁻¹ * y * s⁻¹⁻¹ = s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ := by rw [hsc y hy]
        _ = y := by group
    calc a * y * a⁻¹ = s⁻¹ * (b ^ i * y * (b ^ i)⁻¹) * s⁻¹⁻¹ := by rw [hadef]; group
      _ = y := by rw [h1, h2]
  set w := a * l with hwdef
  have hmow : m = (s⁻¹ * o * s) * w := by
    calc m = s⁻¹ * (s * m) := by group
      _ = (s⁻¹ * o * s) * w := by rw [hdec, hwdef, hadef]; group
  have hwC : w ∈ Cen (c * b₂) :=
    (Cen _).mul_mem ((Cen _).mul_mem ((Cen _).inv_mem hsC) hbi) hlC
  have hwb : w * b * w⁻¹ ∈ Subgroup.zpowers b := by
    have hlb : l * b * l⁻¹ = b := conj_of_mem_cen
      (Subgroup.mem_centralizer_singleton_iff.mpr (hB.b_comm hl).symm)
    have : w * b * w⁻¹ = s⁻¹ * b * s := by
      calc w * b * w⁻¹ = s⁻¹ * b ^ i * (l * b * l⁻¹) * (b ^ i)⁻¹ * s := by
            rw [hwdef, hadef]; group
        _ = s⁻¹ * b * s := by rw [hlb]; group
    rw [this]
    rcases hsb with e | e
    · have : s⁻¹ * b * s = b := by
        calc s⁻¹ * b * s = s⁻¹ * (s * b * s⁻¹) * s := by rw [e]
          _ = b := by group
      rw [this]; exact Subgroup.mem_zpowers b
    · have : s⁻¹ * b * s = b⁻¹ := by
        calc s⁻¹ * b * s = (s⁻¹ * b⁻¹ * s)⁻¹ := by group
          _ = (s⁻¹ * (s * b * s⁻¹) * s)⁻¹ := by rw [e]
          _ = b⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b)
  have hwL : ∀ y ∈ ({c, b₂} : Set G), w * y * w⁻¹ ∈ Subgroup.closure {c, b₂} := by
    intro y hy
    have hyL : y ∈ L := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h <;> rw [h]; exacts [hcL, hB.hb₂]
    have hly : l * y * l⁻¹ ∈ Subgroup.closure {c, b₂} :=
      (Subgroup.mem_normalizer_iff.mp hlN y).mp (Subgroup.subset_closure hy)
    have : w * y * w⁻¹ = a * (l * y * l⁻¹) * a⁻¹ := by rw [hwdef]; group
    rw [this, ha _ (L.mul_mem (L.mul_mem hl hyL) (L.inv_mem hl))]
    exact hly
  have hτS : ∀ y ∈ ({c, b₂} : Set G), τ * y * τ⁻¹ ∈ Subgroup.closure ({b, b₂} : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h <;> rw [h]
    · rw [hτc]; exact Subgroup.subset_closure (by simp)
    · rw [hτ2]; exact Subgroup.subset_closure (by simp)
  refine ⟨τ * (s⁻¹ * o * s) * τ⁻¹, ?_, τ * w * τ⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_conjBy_iff, show τ⁻¹ * (τ * (s⁻¹ * o * s) * τ⁻¹) * τ = s⁻¹ * o * s by group]
    exact ho'
  · calc u = τ * m * τ⁻¹ := by rw [hmdef]; group
      _ = _ := by rw [hmow]; group
  · refine mem_cen_of_conj ?_
    calc τ * w * τ⁻¹ * (b * b₂) * (τ * w * τ⁻¹)⁻¹ =
          τ * (w * ((τ⁻¹ * b * τ) * (τ⁻¹ * b₂ * τ)) * w⁻¹) * τ⁻¹ := by group
      _ = τ * (c * b₂) * τ⁻¹ := by rw [ic, i2, conj_of_mem_cen hwC]
      _ = (τ * c * τ⁻¹) * (τ * b₂ * τ⁻¹) := by group
      _ = b * b₂ := by rw [hτc, hτ2]
  · have : τ * w * τ⁻¹ * c * (τ * w * τ⁻¹)⁻¹ = τ * (w * b * w⁻¹) * τ⁻¹ := by
      calc τ * w * τ⁻¹ * c * (τ * w * τ⁻¹)⁻¹ = τ * (w * (τ⁻¹ * c * τ) * w⁻¹) * τ⁻¹ := by group
        _ = _ := by rw [ib]
    rw [this]; exact conj_mem_zpowers hτb hwb
  · have : τ * w * τ⁻¹ * b * (τ * w * τ⁻¹)⁻¹ = τ * (w * c * w⁻¹) * τ⁻¹ := by
      calc τ * w * τ⁻¹ * b * (τ * w * τ⁻¹)⁻¹ = τ * (w * (τ⁻¹ * b * τ) * w⁻¹) * τ⁻¹ := by group
        _ = _ := by rw [ic]
    rw [this]; exact conj_mem_of_closure hτS (hwL c (by simp))
  · have : τ * w * τ⁻¹ * b₂ * (τ * w * τ⁻¹)⁻¹ = τ * (w * b₂ * w⁻¹) * τ⁻¹ := by
      calc τ * w * τ⁻¹ * b₂ * (τ * w * τ⁻¹)⁻¹ = τ * (w * (τ⁻¹ * b₂ * τ) * w⁻¹) * τ⁻¹ := by
            group
        _ = _ := by rw [i2]
    rw [this]; exact conj_mem_of_closure hτS (hwL b₂ (by simp))

end Sec4T

end CFSG.RankThree.PartTwo.Sec21.FF81
