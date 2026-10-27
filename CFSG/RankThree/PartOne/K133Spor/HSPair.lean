module

public import CFSG.RankThree.PartOne.K133Spor.HSPairSound
public import CFSG.RankThree.Native.HSMcLFiveCentralizers

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open Subgroup

theorem exists_conj_line_zpowers {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P Q : Subgroup M} {ι : Type*} {xs : ι → M}
    (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P)
    (hlines : {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} =
      Set.range (fun i : ι => zpowers (xs i)))
    {y : M} (hyP : y ∈ P) (hord : orderOf y = p) :
    ∃ g : M, g ∈ P ∧ ∃ i : ι, zpowers (g⁻¹ * y * g) = zpowers (xs i) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S₀, hS₀⟩ := hSyl
  have hpgrp : IsPGroup p (zpowers (⟨y, hyP⟩ : P)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord, pow_one])
  obtain ⟨S, hS⟩ := hpgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S₀ S
  have hyS : (⟨y, hyP⟩ : P) ∈ (S : Subgroup P) := hS (Subgroup.mem_zpowers _)
  have hy'Q : (g : M)⁻¹ * y * (g : M) ∈ Q := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
    rw [hS₀, Subgroup.mem_subgroupOf] at hyS
    simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hyS
  have hord' : orderOf ((g : M)⁻¹ * y * (g : M)) = p := by
    have := orderOf_injective (MulAut.conj (g : M)⁻¹).toMonoidHom
      (MulAut.conj (g : M)⁻¹).injective y
    rw [hord] at this
    rw [← this]
    simp [mul_assoc]
  have hmem : zpowers ((g : M)⁻¹ * y * (g : M)) ∈ {H : Subgroup M | H ≤ Q ∧ Nat.card H = p} :=
    ⟨zpowers_le.mpr hy'Q, by rw [Nat.card_zpowers, hord']⟩
  rw [hlines] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact ⟨g, g.2, i, hi.symm⟩


theorem hsRecordFree
    (hcheck : HSPairFreeCheck) (i : Fin 31) (hi : i = 0 ∨ i = 2 ∨ i = 23)
    {u f : Equiv.Perm (Fin 100)}
    (hu : u ∈ centralizer ({hs100FiveLine i} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R)
    (hf : f ∈ centralizer ({hs100FiveLine i} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R)
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (hf5 : f ^ 5 = 1) (hf1 : f ≠ 1)
    (hfi : f ∉ zpowers (hs100FiveLine i)) (hcomm : u * f = f * u) : False := by
  obtain ⟨-, -, -, -, -, ⟨hC0, -⟩, ⟨hC2, -⟩, ⟨hC23, -⟩, -⟩ :=
    R3E_HS_full_five_centralizer_structures
  unfold HSPairFreeCheck hsPairFreeOK at hcheck
  simp only [Bool.and_eq_true] at hcheck
  obtain ⟨⟨h0, h2⟩, h23⟩ := hcheck
  rcases hi with rfl | rfl | rfl
  · rw [← hC0] at hu hf
    exact pairFree_of_check hs100FiveKeys_lt hs100FiveC0_enum (rep_hs100FiveLine 0) h0 hu hf hu2
      hu1 hf5 hf1 hfi hcomm
  · rw [← hC2] at hu hf
    exact pairFree_of_check hs100FiveKeys_lt hs100FiveC2_enum (rep_hs100FiveLine 2) h2 hu hf hu2
      hu1 hf5 hf1 hfi hcomm
  · rw [← hC23] at hu hf
    exact pairFree_of_check hs100FiveKeys_lt hs100FiveC23_enum (rep_hs100FiveLine 23) h23 hu hf
      hu2 hu1 hf5 hf1 hfi hcomm

theorem hsPairFree
    (hcheck : HSPairFreeCheck) {x f u : Equiv.Perm (Fin 100)} (hxP : x ∈ hs100P)
    (hx5 : orderOf x = 5) (hfR : f ∈ hs100R) (hf5 : orderOf f = 5) (hxf : x * f = f * x)
    (hfx : f ∉ zpowers x) (huR : u ∈ hs100R) (hu2 : orderOf u = 2) (hux : u * x = x * u)
    (huf : u * f = f * u) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨⟨-, hSyl, -, -⟩, ⟨hlines, -⟩, htrans, hrecmem, -, -, -, -, -⟩ :=
    R3E_HS_full_five_centralizer_structures
  obtain ⟨g, hgP, j, hgj⟩ := exists_conj_line_zpowers Nat.prime_five hSyl hlines hxP hx5
  obtain ⟨hTR, hTj⟩ := htrans j
  have hmem : (hs100FiveRecordOf j : ℕ) = 0 ∨ (hs100FiveRecordOf j : ℕ) = 2 ∨
      (hs100FiveRecordOf j : ℕ) = 23 := by simpa using hrecmem j
  have hi : hs100FiveRecordOf j = 0 ∨ hs100FiveRecordOf j = 2 ∨ hs100FiveRecordOf j = 23 := by
    rcases hmem with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  generalize hT : hs100FiveTransporter j = T at hTR hTj
  generalize hr : hs100FiveRecordOf j = r at hi hTj
  have hgR : g ∈ hs100R := hs100P_le_R hgP
  have hcR : g * T ∈ hs100R := hs100R.mul_mem hgR hTR
  let φ : MulAut (Equiv.Perm (Fin 100)) := MulAut.conj (g * T)⁻¹
  have hφ : ∀ y, φ y = T⁻¹ * (g⁻¹ * y * g) * T := fun y => by
    simp [φ, mul_assoc]
  have hφR : ∀ y ∈ hs100R, φ y ∈ hs100R := fun y hy => by
    rw [hφ]
    have h1 : T⁻¹ * g⁻¹ * y * (g * T) ∈ hs100R :=
      hs100R.mul_mem (hs100R.mul_mem (hs100R.mul_mem (hs100R.inv_mem hTR) (hs100R.inv_mem hgR)) hy)
        hcR
    simpa [mul_assoc] using h1
  have hline : hs100FiveLine r = T⁻¹ * hs100FiveLine j * T := by
    rw [← hTj]; group
  have hx'line : zpowers (φ x) = zpowers (hs100FiveLine r) := by
    have e1 : φ x = T⁻¹ * (g⁻¹ * x * g) * T := hφ x
    have e2 : ∀ a : Equiv.Perm (Fin 100), zpowers (T⁻¹ * a * T) =
        (zpowers a).map (MulAut.conj T⁻¹).toMonoidHom := fun a => by
      rw [MonoidHom.map_zpowers]
      simp
    rw [e1, e2, hline, e2, hgj]
  have hcomm_x : ∀ y, y * x = x * y → φ y * hs100FiveLine r = hs100FiveLine r * φ y := by
    intro y hy
    have hyx : Commute (φ y) (φ x) := by
      show φ y * φ x = φ x * φ y
      rw [← map_mul, ← map_mul, hy]
    have hl : hs100FiveLine r ∈ zpowers (φ x) := by
      rw [hx'line]; exact mem_zpowers _
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hl
    rw [← hk]
    exact (Commute.zpow_right hyx k).eq
  have hfmem : φ f ∈ centralizer ({hs100FiveLine r} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R :=
    ⟨mem_centralizer_singleton_iff.2 (hcomm_x f hxf.symm), hφR f hfR⟩
  have humem : φ u ∈ centralizer ({hs100FiveLine r} : Set (Equiv.Perm (Fin 100))) ⊓ hs100R :=
    ⟨mem_centralizer_singleton_iff.2 (hcomm_x u hux), hφR u huR⟩
  have hu2sq : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, sq] at this
  have hu1' : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    omega
  have hf5pow : f ^ 5 = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf5] at this
  have hf1' : f ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hf5
    omega
  have hfi : φ f ∉ zpowers (hs100FiveLine r) := by
    intro h
    rw [← hx'line] at h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    apply hfx
    refine ⟨k, ?_⟩
    apply φ.injective
    rw [map_zpow, hk]
  refine hsRecordFree hcheck r hi humem hfmem ?_ ?_ ?_ ?_ hfi ?_
  · rw [← map_mul, hu2sq, map_one]
  · intro h
    exact hu1' (φ.injective (by rw [h, map_one]))
  · rw [← map_pow, hf5pow, map_one]
  · intro h
    exact hf1' (φ.injective (by rw [h, map_one]))
  · rw [← map_mul, ← map_mul, huf]

end CFSG.RankThree.PartOne.K133Spor
