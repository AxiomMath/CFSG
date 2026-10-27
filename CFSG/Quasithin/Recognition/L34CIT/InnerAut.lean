module

public import CFSG.Quasithin.Recognition.L34CIT.Count
public import CFSG.GroupTheory.InnerOfFixSylowTwo

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open CFSG.Quasithin.A94.He42Plane CFSG.ComponentClassification.WittDesign
open scoped Pointwise commutatorElement

variable {Y : Type} [Group Y] {A : Subgroup Y} [Finite A]

namespace Config

private theorem exists_mem_center_sylow_conj_eq_of_normalizer (C : Config ↥A)
    {Q : Subgroup ↥A} (hQ16 : Nat.card Q = 16)
    (hcent : centralizer (Q : Set ↥A) ≤ Q)
    (hQT : Q ≤ C.T)
    (hT_le : (C.T : Subgroup ↥A) ≤ normalizer (Q : Set ↥A))
    (hP960 : Nat.card ↥(normalizer (Q : Set ↥A)) = 960)
    {g : Y} (hg : g ∈ normalizer (A : Set Y))
    (hgT : ∀ t ∈ C.T, g * (t : Y) = (t : Y) * g) :
    ∃ y ∈ ((C.T : Subgroup ↥A).map A.subtype) ⊓
        centralizer (((C.T : Subgroup ↥A).map A.subtype) : Set Y),
      ∀ k ∈ (normalizer (Q : Set ↥A)).map A.subtype,
        g * k * g⁻¹ = y * k * y⁻¹ := by
  classical
  let P : Subgroup ↥A := normalizer (Q : Set ↥A)
  let P' : Subgroup Y := P.map A.subtype
  let Q' : Subgroup Y := Q.map A.subtype
  let T' : Subgroup Y := (C.T : Subgroup ↥A).map A.subtype
  have hP'A : P' ≤ A := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    exact p.2
  haveI : Finite ↥P' :=
    Finite.of_injective (fun x : ↥P' => (⟨(x : Y), hP'A x.2⟩ : ↥A)) (by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : ↥A => (z : Y)) hxy))
  have hQ'P' : Q' ≤ P' := by
    dsimp only [Q', P', P]
    exact Subgroup.map_mono Subgroup.le_normalizer
  have hQn : (Q'.subgroupOf P').Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQ'P']
    intro h k hh hk
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hk
    have hp' : p ∈ normalizer (Q : Set ↥A) := hp
    refine Subgroup.mem_map.mpr ⟨p * q * p⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hp' q).mp hq
    · simp
  have hQ'2 : IsPGroup 2 Q' := by
    refine IsPGroup.of_card (n := 4) ?_
    rw [show Q' = Q.map A.subtype from rfl,
      Subgroup.card_map_of_injective A.subtype_injective, hQ16]
    norm_num
  have hCQ : P' ⊓ centralizer (Q' : Set Y) ≤ Q' := by
    intro z hz
    obtain ⟨hzP, hzC⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hzP
    have hpc : p ∈ centralizer (Q : Set ↥A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC (A.subtype q)
        (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩))
    exact Subgroup.mem_map.mpr ⟨p, hcent hpc, rfl⟩
  have hT'P' : T' ≤ P' := by
    dsimp only [T', P']
    exact Subgroup.map_mono hT_le
  have hT'2 : IsPGroup 2 T' := by
    refine IsPGroup.of_card (n := 6) ?_
    rw [show T' = (C.T : Subgroup ↥A).map A.subtype from rfl,
      Subgroup.card_map_of_injective A.subtype_injective, C.card_T]
    norm_num
  have hT'card : Nat.card ↥(T'.subgroupOf P') = 64 := by
    rw [show Nat.card ↥(T'.subgroupOf P') = Nat.card T' from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT'P').toEquiv]
    rw [show T' = (C.T : Subgroup ↥A).map A.subtype from rfl,
      Subgroup.card_map_of_injective A.subtype_injective, C.card_T]
  have hP'card : Nat.card ↥P' = 960 := by
    rw [show P' = P.map A.subtype from rfl,
      Subgroup.card_map_of_injective A.subtype_injective]
    exact hP960
  have hTodd : Odd (T'.subgroupOf P').index := by
    have hmul := Subgroup.index_mul_card (T'.subgroupOf P')
    rw [hT'card, hP'card] at hmul
    have hidx : (T'.subgroupOf P').index = 15 := by omega
    rw [hidx]
    exact ⟨7, by norm_num⟩
  have hgP' : g ∈ normalizer (P' : Set Y) := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hn
    have hmemA : g * (p : Y) * g⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hg (p : Y)).mp p.2
    refine Subgroup.mem_map.mpr ⟨⟨g * (p : Y) * g⁻¹, hmemA⟩, ?_, rfl⟩
    have hp' : p ∈ normalizer (Q : Set ↥A) := hp
    refine Subgroup.mem_normalizer_fintype ?_
    intro q hq
    have hpq : p * q * p⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hp' q).mp hq
    have hgq : g * (q : Y) = (q : Y) * g := hgT q (hQT hq)
    have hgq' : g⁻¹ * (q : Y) * g = (q : Y) := by
      calc g⁻¹ * (q : Y) * g = g⁻¹ * ((q : Y) * g) := by rw [mul_assoc]
        _ = g⁻¹ * (g * (q : Y)) := by rw [← hgq]
        _ = (q : Y) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    have hgpq : g * ((p * q * p⁻¹ : ↥A) : Y) * g⁻¹ = ((p * q * p⁻¹ : ↥A) : Y) := by
      rw [hgT _ (hQT hpq)]
      group
    have hq' : (⟨g * (p : Y) * g⁻¹, hmemA⟩ : ↥A) * q *
        (⟨g * (p : Y) * g⁻¹, hmemA⟩ : ↥A)⁻¹ = p * q * p⁻¹ := by
      apply Subtype.ext
      show (g * (p : Y) * g⁻¹) * (q : Y) * (g * (p : Y) * g⁻¹)⁻¹ =
        ((p * q * p⁻¹ : ↥A) : Y)
      calc (g * (p : Y) * g⁻¹) * (q : Y) * (g * (p : Y) * g⁻¹)⁻¹
          = g * (p : Y) * (g⁻¹ * (q : Y) * g) * (p : Y)⁻¹ * g⁻¹ := by group
        _ = g * (p : Y) * (q : Y) * (p : Y)⁻¹ * g⁻¹ := by rw [hgq']
        _ = g * ((p * q * p⁻¹ : ↥A) : Y) * g⁻¹ := by
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]
              group
        _ = ((p * q * p⁻¹ : ↥A) : Y) := hgpq
    rw [hq']
    exact hpq
  have hgT' : ∀ t ∈ T', g * t = t * g := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    exact hgT s hs
  exact CFSG.GroupTheory.exists_mem_center_sylow_two_conj_eq
    (Y := Y) (X := P') (Q := Q') (T := T')
    hQ'P' hQn hQ'2 hCQ hT'P' hT'2 hTodd hgP' hgT'

theorem exists_mem_T_inf_centralizer_conj_eq_K₁ (C : Config ↥A) {g : Y}
    (hg : g ∈ normalizer (A : Set Y))
    (hgT : ∀ t ∈ C.T, g * (t : Y) = (t : Y) * g) :
    ∃ y ∈ ((C.T : Subgroup ↥A).map A.subtype) ⊓
        centralizer (((C.T : Subgroup ↥A).map A.subtype) : Set Y),
      ∀ k ∈ C.K₁.map A.subtype, g * k * g⁻¹ = y * k * y⁻¹ :=
  exists_mem_center_sylow_conj_eq_of_normalizer (Q := C.L) C C.card_L C.centralizer_L_le
    C.L_le C.T_le_normalizer_L C.card_normalizer_L hg hgT

theorem exists_mem_T_inf_centralizer_conj_eq_K₂ (C : Config ↥A) {g : Y}
    (hg : g ∈ normalizer (A : Set Y))
    (hgT : ∀ t ∈ C.T, g * (t : Y) = (t : Y) * g) :
    ∃ y ∈ ((C.T : Subgroup ↥A).map A.subtype) ⊓
        centralizer (((C.T : Subgroup ↥A).map A.subtype) : Set Y),
      ∀ k ∈ C.K₂.map A.subtype, g * k * g⁻¹ = y * k * y⁻¹ :=
  C.swap.exists_mem_T_inf_centralizer_conj_eq_K₁ hg hgT

theorem exists_mem_Z_conj_eq (C : Config ↥A) {g : Y}
    (hg : g ∈ normalizer (A : Set Y))
    (hgT : ∀ t ∈ C.T, g * (t : Y) = (t : Y) * g) :
    ∃ y ∈ C.Z, ∀ a : ↥A, g * (a : Y) * g⁻¹ = (y : Y) * a * (y : Y)⁻¹ := by
  classical
  let T' : Subgroup Y := (C.T : Subgroup ↥A).map A.subtype
  obtain ⟨y₁, hy₁, hconj₁⟩ := C.exists_mem_T_inf_centralizer_conj_eq_K₁ hg hgT
  obtain ⟨y₂, hy₂, hconj₂⟩ := C.exists_mem_T_inf_centralizer_conj_eq_K₂ hg hgT
  have hy₁T : y₁ ∈ T' := hy₁.1
  have hy₂T : y₂ ∈ T' := hy₂.1
  have hy₁C : y₁ ∈ centralizer (T' : Set Y) := hy₁.2
  obtain ⟨k, hkT, hk3⟩ := C.exists_orderOf_eq_three
  have hkK₁ : k ∈ C.K₁ := (C.normalizer_T_le hkT).1
  have hkK₂ : k ∈ C.K₂ := (C.normalizer_T_le hkT).2
  have hk₁ : (k : Y) ∈ C.K₁.map A.subtype := Subgroup.mem_map.mpr ⟨k, hkK₁, rfl⟩
  have hk₂ : (k : Y) ∈ C.K₂.map A.subtype := Subgroup.mem_map.mpr ⟨k, hkK₂, rfl⟩
  have hkconj : y₁ * (k : Y) * y₁⁻¹ = y₂ * (k : Y) * y₂⁻¹ :=
    (hconj₁ (k : Y) hk₁).symm.trans (hconj₂ (k : Y) hk₂)
  let u : Y := y₁⁻¹ * y₂
  have huT : u ∈ T' := T'.mul_mem (T'.inv_mem hy₁T) hy₂T
  have hu_comm : u * (k : Y) = (k : Y) * u := by
    have h : u * (k : Y) * u⁻¹ = (k : Y) := by
      calc u * (k : Y) * u⁻¹ = y₁⁻¹ * (y₂ * (k : Y) * y₂⁻¹) * y₁ := by
            simp only [u]
            group
        _ = y₁⁻¹ * (y₁ * (k : Y) * y₁⁻¹) * y₁ := by rw [← hkconj]
        _ = (k : Y) := by group
    calc u * (k : Y) = (u * (k : Y) * u⁻¹) * u := by group
      _ = (k : Y) * u := by rw [h]
  obtain ⟨u', hu'T, hu'Y⟩ :=
    Subgroup.mem_map.mp (show u ∈ (C.T : Subgroup ↥A).map A.subtype from huT)
  have hu'_comm : u' * k = k * u' := by
    apply A.subtype_injective
    rw [map_mul, map_mul, hu'Y]
    exact hu_comm
  obtain ⟨n, hn⟩ := C.T.isPGroup'.exists_pow_pow_eq_one ⟨u', hu'T⟩
  have hu'pow : u' ^ 2 ^ n = 1 := by
    simpa using hn
  have hu'1 : u' = 1 := C.eq_one_of_commute_of_orderOf_eq_three hk3 hu'pow hu'_comm
  have hu1 : y₁⁻¹ * y₂ = 1 := by
    change u = 1
    rw [hu'Y.symm, hu'1, map_one]
  have hy_eq : y₁ = y₂ := by
    calc y₁ = y₁ * 1 := (mul_one y₁).symm
      _ = y₁ * (y₁⁻¹ * y₂) := by rw [hu1]
      _ = y₂ := by group
  obtain ⟨y, hyT, hyY⟩ :=
    Subgroup.mem_map.mp (show y₁ ∈ (C.T : Subgroup ↥A).map A.subtype from hy₁T)
  have hyZ : y ∈ C.Z := by
    rw [C.mem_Z_iff]
    refine ⟨hyT, ?_⟩
    intro s hs
    have hsT' : A.subtype s ∈ (C.T : Subgroup ↥A).map A.subtype :=
      Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
    have hcomm : y₁ * A.subtype s = A.subtype s * y₁ :=
      (Subgroup.mem_centralizer_iff.mp hy₁C (A.subtype s) hsT').symm
    have hcoe : A.subtype (y * s) = A.subtype (s * y) := by
      simpa only [map_mul, hyY] using hcomm
    exact A.subtype_injective hcoe
  refine ⟨y, hyZ, fun a => ?_⟩
  change g * (a : Y) * g⁻¹ = A.subtype y * (a : Y) * (A.subtype y)⁻¹
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, rfl⟩ := C.exists_mul_mul C.card_eq a
  have ha₁' : (a₁ : Y) ∈ C.K₁.map A.subtype := Subgroup.mem_map.mpr ⟨a₁, ha₁, rfl⟩
  have ha₂' : (a₂ : Y) ∈ C.K₂.map A.subtype := Subgroup.mem_map.mpr ⟨a₂, ha₂, rfl⟩
  have ha₃' : (a₃ : Y) ∈ C.K₁.map A.subtype := Subgroup.mem_map.mpr ⟨a₃, ha₃, rfl⟩
  have hc₁ : g * (a₁ : Y) * g⁻¹ = A.subtype y * (a₁ : Y) * (A.subtype y)⁻¹ := by
    simpa only [hyY] using hconj₁ (a₁ : Y) ha₁'
  have hc₂ : g * (a₂ : Y) * g⁻¹ = A.subtype y * (a₂ : Y) * (A.subtype y)⁻¹ := by
    simpa only [hyY, hy_eq] using hconj₂ (a₂ : Y) ha₂'
  have hc₃ : g * (a₃ : Y) * g⁻¹ = A.subtype y * (a₃ : Y) * (A.subtype y)⁻¹ := by
    simpa only [hyY] using hconj₁ (a₃ : Y) ha₃'
  have haY : ((a₁ * a₂ * a₃ : ↥A) : Y) = (a₁ : Y) * (a₂ : Y) * (a₃ : Y) := by simp
  calc g * ((a₁ * a₂ * a₃ : ↥A) : Y) * g⁻¹
      = g * ((a₁ : Y) * (a₂ : Y) * (a₃ : Y)) * g⁻¹ := by rw [haY]
    _ = (g * (a₁ : Y) * g⁻¹) * (g * (a₂ : Y) * g⁻¹) *
          (g * (a₃ : Y) * g⁻¹) := by group
    _ = (A.subtype y * (a₁ : Y) * (A.subtype y)⁻¹) *
          (A.subtype y * (a₂ : Y) * (A.subtype y)⁻¹) *
          (A.subtype y * (a₃ : Y) * (A.subtype y)⁻¹) := by rw [hc₁, hc₂, hc₃]
    _ = A.subtype y * ((a₁ : Y) * (a₂ : Y) * (a₃ : Y)) * (A.subtype y)⁻¹ := by group
    _ = A.subtype y * ((a₁ * a₂ * a₃ : ↥A) : Y) * (A.subtype y)⁻¹ := by rw [haY]

end Config

end CFSG.Quasithin.L34CIT
