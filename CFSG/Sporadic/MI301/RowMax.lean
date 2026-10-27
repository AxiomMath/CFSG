module

public import CFSG.Sporadic.MI301.Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Max
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Tools
public import CFSG.GH74.GLS.C3.Layer2.GenLemmas

public section

namespace CFSG.Sporadic.MI301

open CFSG.Open CFSG.Monster.GMS Subgroup

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem le_leechQ_of_le_normalizer (h : GMSLeechCentralizer z) {p k : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hrk : GLATwoLocalRank p CFSG.Blueprint.NativeSporadic.Co1 < k)
    {B₁ P : Subgroup G} (hB : IsElemAbelian p B₁) (hBc : Nat.card B₁ = p ^ k)
    (hBz : B₁ ≤ centralizer ({z} : Set G)) (hP : IsPGroup 2 P)
    (hPz : P ≤ centralizer ({z} : Set G)) (hBP : B₁ ≤ normalizer (P : Set G)) :
    P ≤ leechQ z := by
  set C := centralizer ({z} : Set G) with hC
  obtain ⟨φ, -, hφk⟩ := h.2.2.2.1
  intro x hxP
  by_contra hxQ
  have hxC : x ∈ C := hPz hxP
  have hT : (P.subgroupOf C).map φ ≠ ⊥ := by
    intro hbot
    apply hxQ
    have hx1 : φ ⟨x, hxC⟩ ∈ (P.subgroupOf C).map φ :=
      Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.2 hxP)
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, hφk] at hx1
    exact Subgroup.mem_map.2 ⟨_, hx1, rfl⟩
  have h2 : IsPGroup 2 ((P.subgroupOf C).map φ) :=
    (hP.comap_of_injective C.subtype C.subtype_injective).map φ
  have hinj : Function.Injective (φ.comp (B₁.subgroupOf C).subtype) := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hbk : (b : C) ∈ CFSG.pCore 2 C := by
      rw [← hφk]
      exact MonoidHom.mem_ker.2 hb
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := C) ⟨b, hbk⟩
    have hbp : (b : C) ^ p = 1 :=
      Subtype.ext (by simpa using hB.2 _ (Subgroup.mem_subgroupOf.1 b.2))
    have hb2 : (b : C) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hcop : Nat.Coprime (2 ^ n) p :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb2) (orderOf_dvd_of_pow_eq_one hbp)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact Subtype.ext h3
  have hEc : Nat.card ((B₁.subgroupOf C).map φ) = p ^ k := by
    have e1 : (B₁.subgroupOf C).map φ = (φ.comp (B₁.subgroupOf C).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBz).toEquiv, hBc]
  have hBN : B₁.subgroupOf C ≤ normalizer ((P.subgroupOf C : Subgroup C) : Set C) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro y
    have hy := mem_normalizer_iff.1 (hBP (Subgroup.mem_subgroupOf.1 hb)) y
    simpa [Subgroup.mem_subgroupOf] using hy
  have hEN := (Subgroup.map_mono hBN).trans (Subgroup.le_normalizer_map φ)
  have hk := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
    hp.one_lt hT h2 ((hB.subgroupOf C).map φ) hEN hEc
  exact absurd hk (not_le.2 hrk)

theorem eq_leechQ_of_le (h : GMSLeechCentralizer z) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : GLATwoLocalRank p CFSG.Blueprint.NativeSporadic.Co1 < k) {B₁ : Subgroup G}
    (hB : IsElemAbelian p B₁) (hBc : Nat.card B₁ = p ^ k)
    (hBz : B₁ ≤ centralizer ({z} : Set G)) {R' : Subgroup G} (hR : IsPGroup 2 R')
    (hBR : B₁ ≤ normalizer (R' : Set G)) (hQR : leechQ z ≤ R') : R' = leechQ z := by
  refine le_antisymm ?_ hQR
  by_contra hne
  obtain ⟨y, hyR, hyQ, hyN⟩ :=
    CFSG.GH74.GLS.C3.Layer2.exists_mem_normalizer_not_mem_of_lt hR (lt_of_le_not_ge hQR hne)
  rw [normalizer_leechQ h] at hyN
  set C := centralizer ({z} : Set G) with hC
  have hBN : B₁ ≤ normalizer ((R' ⊓ C : Subgroup G) : Set G) := by
    intro b hb
    have hbz := hBz hb
    rw [mem_normalizer_iff]
    intro n
    have hbR := mem_normalizer_iff.1 (hBR hb) n
    have hbC : n ∈ C ↔ b * n * b⁻¹ ∈ C := by
      refine ⟨fun hn => C.mul_mem (C.mul_mem hbz hn) (C.inv_mem hbz), fun hn => ?_⟩
      have h1 := C.mul_mem (C.mul_mem (C.inv_mem hbz) hn) hbz
      simpa [mul_assoc] using h1
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    rw [← SetLike.mem_coe, ← SetLike.mem_coe (x := b * n * b⁻¹)]
    exact and_congr hbR hbC
  have hle := le_leechQ_of_le_normalizer h hp hp2 hrk hB hBc hBz (hR.to_le inf_le_left)
    inf_le_right hBN
  exact hyQ (hle ⟨hyR, hyN⟩)

theorem hMax_leech (h : GMSLeechCentralizer z) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : GLATwoLocalRank p CFSG.Blueprint.NativeSporadic.Co1 < k)
    (hOut : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) {K₀ B₁ : Subgroup G}
    (hB : IsElemAbelian p B₁) (hBc : Nat.card B₁ = p ^ k)
    (hBz : B₁ ≤ centralizer ({z} : Set G)) :
    ∀ (A : Type) [Group A] [Finite A] (ι : G →* A), Function.Injective ι → ι.range.Normal →
      centralizer (ι.range : Set A) = ⊥ → ∀ R' : Subgroup A, IsPGroup 2 R' →
      (K₀ ⊔ B₁).map ι ≤ normalizer (R' : Set A) → (leechQ z).map ι ≤ R' →
      R' = (leechQ z).map ι := by
  intro A _ _ ι hι hN hC R' hR' hKB hQ
  have htop := CFSG.LocalAnalysis.GLTheoremA.H301.range_eq_top_of_forall_inner hOut ι hι hN hC
  have hR'eq : R' = (R'.comap ι).map ι := by
    rw [Subgroup.map_comap_eq, htop, top_inf_eq]
  rw [hR'eq, eq_leechQ_of_le h hp hp2 hrk hB hBc hBz (hR'.comap_of_injective ι hι)
    ((Subgroup.map_le_iff_le_comap.1 ((Subgroup.map_mono le_sup_right).trans hKB)).trans
      (Subgroup.le_normalizer_comap ι)) (Subgroup.map_le_iff_le_comap.1 hQ)]

end CFSG.Sporadic.MI301
