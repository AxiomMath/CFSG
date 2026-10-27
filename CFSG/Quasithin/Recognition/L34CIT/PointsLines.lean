module

public import CFSG.Quasithin.Recognition.L34CIT.Involutions
public import CFSG.Quasithin.Vol2.Asc94.He42Plane

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise

variable {A : Type} [Group A]

theorem isElemAbelian_conj {p : ℕ} {H : Subgroup A} (h : IsElemAbelian p H) (a : A) :
    IsElemAbelian p (MulAut.conj a • H) := by
  exact CFSG.Open.IsElemAbelian.map h (MulAut.conj a).toMonoidHom

theorem card_conj (a : A) (H : Subgroup A) : Nat.card ↥(MulAut.conj a • H) = Nat.card H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom)
    (fun x y h => (MulAut.conj a).injective h)

namespace Config

theorem normalizer_T_le (C : Config A) [Finite A] :
    normalizer (C.T : Set A) ≤ normalizer (C.L : Set A) ⊓ normalizer (C.M : Set A) := by
  intro n hn
  let N := normalizer (C.T : Set A)
  have hodd : Odd ((C.T : Subgroup A).subgroupOf N).index := by
    let P : Sylow 2 ↥N := C.T.subtype (Subgroup.le_normalizer)
    have hP : ¬ 2 ∣ P.index := P.not_dvd_index
    have hidx : P.index = ((C.T : Subgroup A).subgroupOf N).index := rfl
    rw [hidx] at hP
    exact Nat.not_even_iff_odd.mp fun he => hP (even_iff_two_dvd.mp he)
  have hnpow : n ^ ((C.T : Subgroup A).subgroupOf N).index ∈ C.T := by
    haveI : ((C.T : Subgroup A).subgroupOf N).Normal := Subgroup.normal_in_normalizer
    have hmem : (⟨n, hn⟩ : ↥N) ^ ((C.T : Subgroup A).subgroupOf N).index ∈
        (C.T : Subgroup A).subgroupOf N :=
      Subgroup.pow_index_mem ((C.T : Subgroup A).subgroupOf N) ⟨n, hn⟩
    exact hmem
  have hnpowNormL : MulAut.conj (n ^ ((C.T : Subgroup A).subgroupOf N).index) • C.L = C.L := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (C.T_le_normalizer_L hnpow)
  have hnT : MulAut.conj n • (C.T : Subgroup A) = (C.T : Subgroup A) := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hnLT : MulAut.conj n • C.L ≤ (C.T : Subgroup A) := by
    rw [← hnT]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.L_le
  have hnMT : MulAut.conj n • C.M ≤ (C.T : Subgroup A) := by
    rw [← hnT]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.M_le
  have hnLea : IsElemAbelian 2 (MulAut.conj n • C.L) := isElemAbelian_conj C.isElemAbelian_L n
  have hnMea : IsElemAbelian 2 (MulAut.conj n • C.M) := isElemAbelian_conj C.isElemAbelian_M n
  have hnLcard : Nat.card ↥(MulAut.conj n • C.L) = 16 := by rw [card_conj, C.card_L]
  have hnMcard : Nat.card ↥(MulAut.conj n • C.M) = 16 := by rw [card_conj, C.card_M]
  rcases C.eq_or_eq (MulAut.conj n • C.L) hnLT hnLea hnLcard with hL | hL
  · have hnM : MulAut.conj n • C.M = C.M := by
      rcases C.eq_or_eq (MulAut.conj n • C.M) hnMT hnMea hnMcard with hM | hM
      · exfalso
        apply C.L_ne_M
        have hEq : MulAut.conj n • C.L = MulAut.conj n • C.M := by rw [hL, hM]
        have := congrArg (fun H => MulAut.conj n⁻¹ • H) hEq
        simpa [← mul_smul, ← map_mul] using this
      · exact hM
    exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hL,
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hnM⟩
  · exfalso
    have hnMswap : MulAut.conj n • C.M = C.L := by
      rcases C.eq_or_eq (MulAut.conj n • C.M) hnMT hnMea hnMcard with hM | hM
      · exact hM
      · exfalso
        apply C.L_ne_M
        have hEq : MulAut.conj n • C.L = MulAut.conj n • C.M := by rw [hL, hM]
        have := congrArg (fun H => MulAut.conj n⁻¹ • H) hEq
        simpa [← mul_smul, ← map_mul] using this
    have hfix2 : MulAut.conj (n * n) • C.M = C.M := by
      rw [map_mul, mul_smul, hnMswap, hL]
    have hfixpow : ∀ m : ℕ, MulAut.conj ((n * n) ^ m) • C.M = C.M := by
      intro m
      induction m with
      | zero => simpa using (one_smul (MulAut.conj (1 : A)) C.M)
      | succ m ih =>
          rw [pow_succ, map_mul, mul_smul, hfix2, ih]
    rcases hodd with ⟨m, hm⟩
    have hpow : n ^ ((C.T : Subgroup A).subgroupOf N).index = (n * n) ^ m * n := by
      rw [hm, pow_add, pow_mul, pow_one]
      congr 2
      rw [pow_two]
    have hcontra : MulAut.conj (n ^ ((C.T : Subgroup A).subgroupOf N).index) • C.L = C.M := by
      rw [hpow, map_mul, mul_smul, hL]
      exact hfixpow m
    rw [hcontra] at hnpowNormL
    exact C.L_ne_M hnpowNormL.symm

theorem conj_L_ne_M (C : Config A) [Finite A] (a : A) : MulAut.conj a • C.L ≠ C.M := by
  intro h
  let N₂ := normalizer (C.M : Set A)
  have hTN : MulAut.conj a • (C.T : Subgroup A) ≤ N₂ := by
    have h1 : MulAut.conj a • (C.T : Subgroup A) ≤ MulAut.conj a • normalizer (C.L : Set A) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.T_le_normalizer_L
    have h2 : MulAut.conj a • normalizer (C.L : Set A) =
        normalizer ((MulAut.conj a • C.L : Subgroup A) : Set A) := by
      exact Subgroup.map_equiv_normalizer_eq (C.L) (MulAut.conj a)
    have h3 : normalizer ((MulAut.conj a • C.L : Subgroup A) : Set A) = N₂ := by rw [h]
    rwa [h2, h3] at h1
  have hP₂' : ((a • C.T : Sylow 2 A) : Subgroup A) ≤ N₂ := by
    rw [Sylow.coe_subgroup_smul]
    exact hTN
  let Q₁ : Sylow 2 ↥N₂ := C.T.subtype C.T_le_normalizer_M
  let Q₂ : Sylow 2 ↥N₂ := (a • C.T).subtype hP₂'
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥N₂ Q₁ Q₂
  have hk' : (k • C.T : Sylow 2 A) = a • C.T := by
    have hsub : (k • C.T).subtype (Sylow.smul_le (P := C.T) C.T_le_normalizer_M k) =
        (a • C.T).subtype hP₂' := by
      calc
        (k • C.T).subtype (Sylow.smul_le (P := C.T) C.T_le_normalizer_M k) =
            k • Q₁ := (Sylow.smul_subtype (P := C.T) C.T_le_normalizer_M k).symm
        _ = Q₂ := hk
        _ = (a • C.T).subtype hP₂' := rfl
    exact Sylow.subtype_injective hsub
  have hcoe : MulAut.conj (k : A) • (C.T : Subgroup A) = MulAut.conj a • (C.T : Subgroup A) := by
    have h1 : ((k • C.T : Sylow 2 A) : Subgroup A) = MulAut.conj (k : A) • (C.T : Subgroup A) :=
      Sylow.coe_subgroup_smul (g := (k : A)) (P := C.T)
    have h2 : ((a • C.T : Sylow 2 A) : Subgroup A) = MulAut.conj a • (C.T : Subgroup A) :=
      Sylow.coe_subgroup_smul (g := a) (P := C.T)
    have := congrArg (fun P : Sylow 2 A => (P : Subgroup A)) hk'
    rwa [h1, h2] at this
  have hNT : a⁻¹ * (k : A) ∈ normalizer (C.T : Set A) := by
    have hconj : MulAut.conj (a⁻¹ * (k : A)) • (C.T : Subgroup A) = (C.T : Subgroup A) := by
      rw [map_mul, mul_smul, hcoe]
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj
  have hN₂ : a⁻¹ * (k : A) ∈ N₂ := (normalizer_T_le C hNT).2
  have haN₂ : a⁻¹ ∈ N₂ := by
    have hk₂ : (k : A) ∈ N₂ := k.2
    have h1 : (a⁻¹ * (k : A)) * (k : A)⁻¹ ∈ N₂ := N₂.mul_mem hN₂ (N₂.inv_mem hk₂)
    simpa [mul_assoc] using h1
  have haN₂' : a ∈ N₂ := by simpa using N₂.inv_mem haN₂
  have haNM : MulAut.conj a • C.M = C.M := by
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp haN₂'
  have hEq : MulAut.conj a • C.L = MulAut.conj a • C.M := by rw [h, haNM]
  have := congrArg (fun H => MulAut.conj a⁻¹ • H) hEq
  exact C.L_ne_M (by simpa [← mul_smul, ← map_mul] using this)

theorem conj_M_ne_L (C : Config A) [Finite A] (a : A) : MulAut.conj a • C.M ≠ C.L := by
  intro h
  have := congrArg (fun H => MulAut.conj a⁻¹ • H) h
  simp only [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at this
  exact (conj_L_ne_M C a⁻¹) this.symm

theorem exists_conj_eq (C : Config A) [Finite A] (P : Sylow 2 A) :
    ∃ g : A, (P : Subgroup A) = MulAut.conj g • (C.T : Subgroup A) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A C.T P
  refine ⟨g, ?_⟩
  have := congrArg (fun Q : Sylow 2 A => (Q : Subgroup A)) hg
  rw [Sylow.coe_subgroup_smul] at this
  exact this.symm

theorem conj_eq_of_le_L (C : Config A) [Finite A] {a g : A}
    (h : MulAut.conj a • C.L ≤ MulAut.conj g • (C.T : Subgroup A)) :
    MulAut.conj a • C.L = MulAut.conj g • C.L := by
  have hle : MulAut.conj (g⁻¹ * a) • C.L ≤ (C.T : Subgroup A) := by
    have h' : MulAut.conj g⁻¹ • (MulAut.conj a • C.L) ≤
        MulAut.conj g⁻¹ • (MulAut.conj g • C.T) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h
    have hT : MulAut.conj g⁻¹ • (MulAut.conj g • (C.T : Subgroup A)) = (C.T : Subgroup A) := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    rw [hT] at h'
    have hgm : MulAut.conj (g⁻¹ * a) = MulAut.conj g⁻¹ * MulAut.conj a := map_mul _ _ _
    rw [hgm, mul_smul]
    exact h'
  have hE : MulAut.conj (g⁻¹ * a) • C.L = C.L := by
    rcases C.eq_or_eq (MulAut.conj (g⁻¹ * a) • C.L) hle
        (isElemAbelian_conj C.isElemAbelian_L (g⁻¹ * a))
        (by rw [card_conj, C.card_L]) with h' | h'
    · exact h'
    · exact absurd h' (conj_L_ne_M C (g⁻¹ * a))
  have := congrArg (fun H => MulAut.conj g • H) hE
  simpa [← mul_smul, ← map_mul] using this

theorem conj_eq_of_le_M (C : Config A) [Finite A] {a g : A}
    (h : MulAut.conj a • C.M ≤ MulAut.conj g • (C.T : Subgroup A)) :
    MulAut.conj a • C.M = MulAut.conj g • C.M := by
  have hle : MulAut.conj (g⁻¹ * a) • C.M ≤ (C.T : Subgroup A) := by
    have h' : MulAut.conj g⁻¹ • (MulAut.conj a • C.M) ≤
        MulAut.conj g⁻¹ • (MulAut.conj g • C.T) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h
    have hT : MulAut.conj g⁻¹ • (MulAut.conj g • (C.T : Subgroup A)) = (C.T : Subgroup A) := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    rw [hT] at h'
    have hgm : MulAut.conj (g⁻¹ * a) = MulAut.conj g⁻¹ * MulAut.conj a := map_mul _ _ _
    rw [hgm, mul_smul]
    exact h'
  have hE : MulAut.conj (g⁻¹ * a) • C.M = C.M := by
    rcases C.eq_or_eq (MulAut.conj (g⁻¹ * a) • C.M) hle
        (isElemAbelian_conj C.isElemAbelian_M (g⁻¹ * a))
        (by rw [card_conj, C.card_M]) with h' | h'
    · exact absurd h' (conj_M_ne_L C (g⁻¹ * a))
    · exact h'
  have := congrArg (fun H => MulAut.conj g • H) hE
  simpa [← mul_smul, ← map_mul] using this

theorem inf_eq_bot_of_ne_L (C : Config A) [Finite A] {a b : A}
    (h : MulAut.conj a • C.L ≠ MulAut.conj b • C.L) :
    MulAut.conj a • C.L ⊓ MulAut.conj b • C.L = ⊥ := by
  rw [eq_bot_iff_forall]
  intro e he
  by_contra he1
  have hXea : IsElemAbelian 2 (MulAut.conj a • C.L) := isElemAbelian_conj C.isElemAbelian_L a
  have hYea : IsElemAbelian 2 (MulAut.conj b • C.L) := isElemAbelian_conj C.isElemAbelian_L b
  have he2 : e * e = 1 := by
    have := hXea.2 e he.1
    simpa [pow_two] using this
  have hXc : MulAut.conj a • C.L ≤ centralizer ({e} : Set A) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    haveI := hXea.1
    exact congrArg Subtype.val (mul_comm' (⟨e, he.1⟩ : ↥(MulAut.conj a • C.L)) ⟨x, hx⟩)
  have hYc : MulAut.conj b • C.L ≤ centralizer ({e} : Set A) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    haveI := hYea.1
    exact congrArg Subtype.val (mul_comm' (⟨e, he.2⟩ : ↥(MulAut.conj b • C.L)) ⟨x, hx⟩)
  obtain ⟨P, hP⟩ := C.exists_sylow_eq_centralizer he2 he1
  rw [hP] at hXc hYc
  obtain ⟨g, hg⟩ := C.exists_conj_eq P
  rw [hg] at hXc hYc
  exact h ((C.conj_eq_of_le_L hXc).trans (C.conj_eq_of_le_L hYc).symm)

theorem inf_eq_bot_of_ne_M (C : Config A) [Finite A] {a b : A}
    (h : MulAut.conj a • C.M ≠ MulAut.conj b • C.M) :
    MulAut.conj a • C.M ⊓ MulAut.conj b • C.M = ⊥ := by
  rw [eq_bot_iff_forall]
  intro e he
  by_contra he1
  have hXea : IsElemAbelian 2 (MulAut.conj a • C.M) := isElemAbelian_conj C.isElemAbelian_M a
  have hYea : IsElemAbelian 2 (MulAut.conj b • C.M) := isElemAbelian_conj C.isElemAbelian_M b
  have he2 : e * e = 1 := by
    have := hXea.2 e he.1
    simpa [pow_two] using this
  have hXc : MulAut.conj a • C.M ≤ centralizer ({e} : Set A) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    haveI := hXea.1
    exact congrArg Subtype.val (mul_comm' (⟨e, he.1⟩ : ↥(MulAut.conj a • C.M)) ⟨x, hx⟩)
  have hYc : MulAut.conj b • C.M ≤ centralizer ({e} : Set A) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    haveI := hYea.1
    exact congrArg Subtype.val (mul_comm' (⟨e, he.2⟩ : ↥(MulAut.conj b • C.M)) ⟨x, hx⟩)
  obtain ⟨P, hP⟩ := C.exists_sylow_eq_centralizer he2 he1
  rw [hP] at hXc hYc
  obtain ⟨g, hg⟩ := C.exists_conj_eq P
  rw [hg] at hXc hYc
  exact h ((C.conj_eq_of_le_M hXc).trans (C.conj_eq_of_le_M hYc).symm)

theorem inc_iff (C : Config A) [Finite A] (a b : A) :
    CFSG.Quasithin.A94.He42Plane.Inc (normalizer (C.L : Set A)) (normalizer (C.M : Set A))
        ((a : A) : A ⧸ normalizer (C.L : Set A)) ((b : A) : A ⧸ normalizer (C.M : Set A)) ↔
      ∃ P : Sylow 2 A, MulAut.conj a • C.L ≤ P ∧ MulAut.conj b • C.M ≤ P := by
  constructor
  · rintro ⟨g, hg1, hg2⟩
    have hga : g⁻¹ * a ∈ normalizer (C.L : Set A) := QuotientGroup.eq.mp hg1
    have hgb : g⁻¹ * b ∈ normalizer (C.M : Set A) := QuotientGroup.eq.mp hg2
    have hLa : MulAut.conj a • C.L = MulAut.conj g • C.L := by
      have h1 : MulAut.conj (g⁻¹ * a) • C.L = C.L := by
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hga
      have := congrArg (fun H => MulAut.conj g • H) h1
      simpa [← mul_smul, ← map_mul] using this
    have hMb : MulAut.conj b • C.M = MulAut.conj g • C.M := by
      have h1 : MulAut.conj (g⁻¹ * b) • C.M = C.M := by
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgb
      have := congrArg (fun H => MulAut.conj g • H) h1
      simpa [← mul_smul, ← map_mul] using this
    refine ⟨g • C.T, ?_, ?_⟩
    · rw [hLa, Sylow.coe_subgroup_smul]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.L_le
    · rw [hMb, Sylow.coe_subgroup_smul]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.M_le
  · rintro ⟨P, hX, hY⟩
    obtain ⟨g, hg⟩ := C.exists_conj_eq P
    rw [hg] at hX hY
    have hLa : MulAut.conj a • C.L = MulAut.conj g • C.L := C.conj_eq_of_le_L hX
    have hMb : MulAut.conj b • C.M = MulAut.conj g • C.M := C.conj_eq_of_le_M hY
    have hga : a⁻¹ * g ∈ normalizer (C.L : Set A) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change MulAut.conj (a⁻¹ * g) • C.L = C.L
      rw [map_mul, mul_smul, ← hLa]
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have hgb : b⁻¹ * g ∈ normalizer (C.M : Set A) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change MulAut.conj (b⁻¹ * g) • C.M = C.M
      rw [map_mul, mul_smul, ← hMb]
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have hga' : (a : A ⧸ normalizer (C.L : Set A)) = (g : A ⧸ normalizer (C.L : Set A)) :=
      QuotientGroup.eq.mpr hga
    have hgb' : (b : A ⧸ normalizer (C.M : Set A)) = (g : A ⧸ normalizer (C.M : Set A)) :=
      QuotientGroup.eq.mpr hgb
    exact ⟨g, hga'.symm, hgb'.symm⟩

end Config

end CFSG.Quasithin.L34CIT
