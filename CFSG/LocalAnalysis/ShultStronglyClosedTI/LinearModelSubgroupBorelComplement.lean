module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelSubgroupSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearSubgroup
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.GorensteinWalter
open scoped Pointwise

universe u

variable {K : Type u} [Field K] [Finite K]

theorem le_sylow_normalizer_of_normalizes {f : ℕ} (hcard : Nat.card K = 2 ^ f)
    (P : Sylow 2 (PSL2MatrixGroup K)) {A O : Subgroup (PSL2MatrixGroup K)} (hOP : O ≤ P)
    (hO : O ≠ ⊥) (hAO : A ≤ Subgroup.normalizer (O : Set (PSL2MatrixGroup K))) :
    A ≤ Subgroup.normalizer (P : Set (PSL2MatrixGroup K)) := by
  obtain ⟨⟨x, hxO⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hO
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  intro a ha
  have haxO : a * x * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hAO ha) x).mp hxO
  have hax1 : a * x * a⁻¹ ≠ 1 := by
    intro h
    exact hx1 (conj_eq_one_iff.mp h)
  have haxP : a * x * a⁻¹ ∈ a • P := by
    change a * x * a⁻¹ ∈ (P : Subgroup (PSL2MatrixGroup K)).map (MulAut.conj a).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨x, hOP hxO, rfl⟩
  have heq := TwoCoreGrowth.psl2_nonidentity_unique_sylow f hcard P (a • P) _ hax1
    (hOP haxO) haxP
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm

theorem linear_subgroup_nontrivial_two_core_borel_complement {f : ℕ}
    (hcard : Nat.card K = 2 ^ f) (A : Subgroup (PSL2MatrixGroup K))
    (hcore : CFSG.pCore 2 A ≠ ⊥) :
    IsElementaryAbelian 2 (CFSG.pCore 2 A) ∧
    (∃ S : Sylow 2 A, (S : Subgroup A) = CFSG.pCore 2 A) ∧
    ∃ W : Subgroup A, IsCyclic W ∧ Odd (Nat.card W) ∧ Nat.card W ∣ Nat.card K - 1 ∧
      Subgroup.IsComplement' (CFSG.pCore 2 A) W ∧
      CFSG.pCore 2 A ⊓ W = ⊥ ∧ CFSG.pCore 2 A ⊔ W = ⊤ ∧
      ∀ W₀ : Subgroup A, W₀ ≤ W → W₀ ≠ ⊥ →
        Subgroup.centralizer (W₀ : Set A) = W ∧ Subgroup.normalizer (W₀ : Set A) = W := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 A with hOdef
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  obtain ⟨P, hOP⟩ := (hO2.map A.subtype).exists_le_sylow
  have hOne : O.map A.subtype ≠ ⊥ := by
    intro h
    exact hcore ((Subgroup.map_eq_bot_iff_of_injective O A.subtype_injective).mp h)
  have hAN : A ≤ Subgroup.normalizer (P : Set (PSL2MatrixGroup K)) := by
    refine le_sylow_normalizer_of_normalizes hcard P hOP hOne ?_
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨a, ha⟩ * y * ⟨a, ha⟩⁻¹, (CFSG.pCore_normal).conj_mem y hy _, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx
      refine ⟨⟨a, ha⟩⁻¹ * y * ⟨a, ha⟩, ?_, ?_⟩
      · simpa using (CFSG.pCore_normal).conj_mem y hy (⟨a, ha⟩⁻¹ : A)
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
        rw [hyx]
        group
  let S : Subgroup A := (P : Subgroup (PSL2MatrixGroup K)).comap A.subtype
  have hS2 : IsPGroup 2 S := P.isPGroup'.comap_of_injective A.subtype A.subtype_injective
  have hSnormal : S.Normal := by
    constructor
    intro s hs a
    change ((a * s * a⁻¹ : A) : PSL2MatrixGroup K) ∈ (P : Subgroup (PSL2MatrixGroup K))
    have h := (Subgroup.mem_normalizer_iff.mp (hAN a.property) (s : PSL2MatrixGroup K)).mp hs
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hOS : O ≤ S := fun x hx => hOP (Subgroup.mem_map_of_mem A.subtype hx)
  have hSO : S ≤ O := le_sSup ⟨hSnormal, hS2⟩
  have hOeq : O = S := le_antisymm hOS hSO
  obtain ⟨R, hSR⟩ := hS2.exists_le_sylow
  have hRS : (R : Subgroup A) ≤ S := by
    intro r hr
    have hRmap : ((R : Subgroup A).map A.subtype) ≤ P := by
      refine le_sylow_of_le_normalizer P (R.isPGroup'.map A.subtype) ?_
      exact (Subgroup.map_subtype_le _).trans hAN
    exact hRmap (Subgroup.mem_map_of_mem A.subtype hr)
  have hRS' : (R : Subgroup A) = S := le_antisymm hRS hSR
  have hRO : (R : Subgroup A) = O := hRS'.trans hOeq.symm
  have hOelem : IsElementaryAbelian 2 O := by
    rw [← hRO]
    exact TwoCoreGrowth.psl2_even_subgroup_sylow_elementary f hcard A R
  let : IsMulCommutative O := hOelem.toIsMulCommutative
  have hcop : Nat.Coprime O.index (Nat.card O) := by
    rw [← hRO]
    exact (R.card_coprime_index).symm
  obtain ⟨W, hcompl, hinf, hsup⟩ := CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting
    O O ⊥ hcop (inf_bot_eq O) (sup_bot_eq O)
  have hWN : W.map A.subtype ≤ Subgroup.normalizer (P : Set (PSL2MatrixGroup K)) :=
    (Subgroup.map_subtype_le _).trans hAN
  have hWP : W.map A.subtype ⊓ (P : Subgroup (PSL2MatrixGroup K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxP⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨w, hwW, rfl⟩ := Subgroup.mem_map.mp hxW
    have hwO : w ∈ O := by rw [hOeq]; exact hxP
    have h : w ∈ O ⊓ W := ⟨hwO, hwW⟩
    rw [hinf, Subgroup.mem_bot] at h
    rw [h, map_one]
    exact Subgroup.one_mem _
  obtain ⟨hcycW', hdvdW'⟩ := sylow_normalizer_complement_cyclic hcard P hWN hWP
  let c : W ≃* W.map A.subtype := W.equivMapOfInjective A.subtype A.subtype_injective
  have hWcyc : IsCyclic W := c.isCyclic.mpr hcycW'
  have hWdvd : Nat.card W ∣ Nat.card K - 1 := (Nat.card_congr c.toEquiv).symm ▸ hdvdW'
  have hqodd : Odd (Nat.card K - 1) := by
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact (Nat.ne_of_gt (Finite.one_lt_card (α := K))) (by simpa using hcard)
    have heven : Even (Nat.card K) := by
      rw [hcard]
      exact (Nat.even_pow' hf0).mpr even_two
    exact Nat.Even.sub_odd Nat.card_pos heven odd_one
  have hWodd : Odd (Nat.card W) := hqodd.of_dvd_nat hWdvd
  refine ⟨hOelem, ⟨R, hRO⟩, W, hWcyc, hWodd, hWdvd, hcompl, hinf, hsup, ?_⟩
  intro W₀ hW₀W hW₀
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    have h := (IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  have hWC : W ≤ Subgroup.centralizer (W₀ : Set A) := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hWcomm x (hW₀W hx) w hw)
  have hNW : Subgroup.normalizer (W₀ : Set A) ≤ W := by
    intro g hg
    have hgmem : g ∈ ((O ⊔ W : Subgroup A) : Set A) := by rw [hsup]; exact Set.mem_univ g
    rw [Subgroup.normal_mul] at hgmem
    obtain ⟨s, hsO, w, hwW, rfl⟩ := Set.mem_mul.mp hgmem
    have hwN : w ∈ Subgroup.normalizer (W₀ : Set A) :=
      Subgroup.centralizer_le_normalizer _ (hWC hwW)
    have hsN : s ∈ Subgroup.normalizer (W₀ : Set A) := by
      have h := (Subgroup.normalizer (W₀ : Set A)).mul_mem hg
        ((Subgroup.normalizer (W₀ : Set A)).inv_mem hwN)
      simpa only [mul_inv_cancel_right] using h
    have hscomm : ∀ x ∈ W₀, s * x = x * s := by
      intro x hx
      have hconj : s * x * s⁻¹ ∈ W₀ := (Subgroup.mem_normalizer_iff.mp hsN x).mp hx
      have hcommW : s * x * s⁻¹ * x⁻¹ ∈ W :=
        W.mul_mem (hW₀W hconj) (W.inv_mem (hW₀W hx))
      have hcommO : s * x * s⁻¹ * x⁻¹ ∈ O := by
        have h := O.mul_mem hsO ((CFSG.pCore_normal).conj_mem _ (O.inv_mem hsO) x)
        simpa only [mul_assoc] using h
      have h : s * x * s⁻¹ * x⁻¹ ∈ O ⊓ W := ⟨hcommO, hcommW⟩
      rw [hinf, Subgroup.mem_bot] at h
      calc s * x = s * x * s⁻¹ * x⁻¹ * (x * s) := by group
        _ = x * s := by rw [h, one_mul]
    obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW₀
    by_cases hs : s = 1
    · rw [hs, one_mul]
      exact hwW
    · exfalso
      have hsP : (s : PSL2MatrixGroup K) ∈ P := by
        have h : s ∈ S := hOeq ▸ hsO
        exact h
      have hs1 : (s : PSL2MatrixGroup K) ≠ 1 := fun h => hs (Subtype.ext h)
      have hxC : ((x : A) : PSL2MatrixGroup K) ∈
          Subgroup.centralizer ({(s : PSL2MatrixGroup K)} : Set (PSL2MatrixGroup K)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hscomm x x.property).symm
      rw [sylow_centralizer_eq hcard P hsP hs1] at hxC
      have hxO : (x : A) ∈ O := by
        rw [hOeq]
        exact hxC
      have h : (x : A) ∈ O ⊓ W := ⟨hxO, hW₀W x.property⟩
      rw [hinf, Subgroup.mem_bot] at h
      exact hx1 (Subtype.ext h)
  have hCN : Subgroup.centralizer (W₀ : Set A) ≤ Subgroup.normalizer (W₀ : Set A) :=
    Subgroup.centralizer_le_normalizer _
  exact ⟨le_antisymm (hCN.trans hNW) hWC, le_antisymm hNW (hWC.trans hCN)⟩

end CFSG.ShultStronglyClosedTI.LinearModel
