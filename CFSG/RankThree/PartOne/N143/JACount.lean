module

public import CFSG.RankThree.PartOne.N143.JDiag
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor IsZeta diagSL tSep tNon ent ent_ext)

section Abstract

theorem card_cube_comap {Δ G : Type*} [CommGroup Δ] [Finite Δ] [Group G] (f : Δ →* G)
    (hker : ∀ z ∈ f.ker, ∃ x : Δ, x ^ 3 = z) :
    Nat.card ((f.ker.comap (powMonoidHom 3 : Δ →* Δ)).map f) =
      Nat.card (powMonoidHom 3 : Δ →* Δ).ker := by
  classical
  set cube : Δ →* Δ := powMonoidHom 3 with hcube
  set Δ' : Subgroup Δ := f.ker.comap cube with hΔ'
  have hmemΔ' : ∀ x, x ∈ Δ' ↔ x ^ 3 ∈ f.ker := fun x => Iff.rfl
  have h1 := Subgroup.card_ker_mul_card_range (cube.comp Δ'.subtype)
  have hrange : (cube.comp Δ'.subtype).range = f.ker := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hz
      obtain ⟨x, hx⟩ := hker z hz
      exact ⟨⟨x, by rw [hmemΔ', hx]; exact hz⟩, hx⟩
  have hkerc : (cube.comp Δ'.subtype).ker = cube.ker.subgroupOf Δ' := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hcube]
  have hle1 : cube.ker ≤ Δ' := fun x hx => by
    rw [hmemΔ']
    have : x ^ 3 = 1 := hx
    rw [this]
    exact f.ker.one_mem
  rw [hkerc, card_subgroupOf_of_le hle1, hrange] at h1
  have h2 := Subgroup.card_ker_mul_card_range (f.comp Δ'.subtype)
  have hker2 : (f.comp Δ'.subtype).ker = f.ker.subgroupOf Δ' := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hle2 : f.ker ≤ Δ' := fun x hx => by
    rw [hmemΔ']
    exact f.ker.pow_mem hx 3
  have hrange2 : (f.comp Δ'.subtype).range = Δ'.map f := by
    ext d
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  rw [hker2, card_subgroupOf_of_le hle2, hrange2] at h2
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have key : Nat.card cube.ker * Nat.card f.ker = Nat.card (Δ'.map f) * Nat.card f.ker := by
    rw [h1, mul_comm (Nat.card (Δ'.map f)), h2]
  exact (Nat.eq_of_mul_eq_mul_right hpos key).symm

end Abstract

section Roots

variable {K : Type} [Field K] [Finite K]

theorem exists_unit_orderOf_nine (h9 : 9 ∣ Nat.card K - 1) : ∃ ε : Kˣ, orderOf ε = 9 := by
  have : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hcard : Fintype.card Kˣ = Nat.card K - 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
  have hd : 9 ∣ Fintype.card Kˣ := hcard ▸ h9
  have hc := IsCyclic.card_orderOf_eq_totient (α := Kˣ) hd
  have hpos : 0 < (Finset.univ.filter fun a : Kˣ => orderOf a = 9).card := by
    rw [hc]
    exact Nat.totient_pos.2 (by norm_num)
  obtain ⟨ε, hε⟩ := Finset.card_pos.1 hpos
  exact ⟨ε, (Finset.mem_filter.1 hε).2⟩

omit [Finite K] in
theorem isPrimitiveRoot_cube {ε : Kˣ} (hε : orderOf ε = 9) : IsPrimitiveRoot (ε ^ 3) 3 := by
  apply IsPrimitiveRoot.iff_orderOf.2
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [hε]; norm_num), hε]

omit [Finite K] in
theorem exists_cube_of_pow_three {ε : Kˣ} (hε : orderOf ε = 9) {a : Kˣ} (ha : a ^ 3 = 1) :
    ∃ x : Kˣ, x ^ 3 = a := by
  have hω := isPrimitiveRoot_cube hε
  have : a ∈ Subgroup.zpowers (ε ^ 3) := by
    rw [hω.zpowers_eq]
    exact (mem_rootsOfUnity 3 a).2 ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 this
  refine ⟨ε ^ i, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

omit [Finite K] in
theorem card_cube_ker_prod {ω : Kˣ} (hω : IsPrimitiveRoot ω 3) :
    Nat.card (powMonoidHom 3 : Kˣ × Kˣ →* Kˣ × Kˣ).ker = 9 := by
  have h3 : Nat.card {a : Kˣ // a ^ 3 = 1} = 3 :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun a => (mem_rootsOfUnity 3 a).symm :
      {a : Kˣ // a ^ 3 = 1} ≃ rootsOfUnity 3 K)).trans hω.card_rootsOfUnity'
  have e1 : (powMonoidHom 3 : Kˣ × Kˣ →* Kˣ × Kˣ).ker ≃
      {c : Kˣ × Kˣ // c.1 ^ 3 = 1 ∧ c.2 ^ 3 = 1} :=
    Equiv.subtypeEquivRight fun c => by simp [MonoidHom.mem_ker, Prod.ext_iff]
  have e2 : {c : Kˣ × Kˣ // c.1 ^ 3 = 1 ∧ c.2 ^ 3 = 1} ≃
      {a : Kˣ // a ^ 3 = 1} × {b : Kˣ // b ^ 3 = 1} :=
    Equiv.subtypeProdEquivProd (p := fun a : Kˣ => a ^ 3 = 1) (q := fun b : Kˣ => b ^ 3 = 1)
  rw [Nat.card_congr e1, Nat.card_congr e2, Nat.card_prod, h3]

end Roots

section Concrete

variable {K : Type} [Field K]

@[expose] def dmVec (a b : Kˣ) : Fin 3 → Kˣ := ![a, b, (a * b)⁻¹]

theorem prod_dmVec (a b : Kˣ) : ∏ i, dmVec a b i = 1 := by
  simp [dmVec, Fin.prod_univ_three]

@[expose] def dm : Kˣ × Kˣ →* SL3 K where
  toFun x := diagSL (dmVec x.1 x.2) (prod_dmVec x.1 x.2)
  map_one' := by
    rw [← diagSL_one']
    refine diagSL_congr ?_ _ _
    funext i
    fin_cases i <;> simp [dmVec]
  map_mul' x y := by
    rw [diagSL_mul]
    refine diagSL_congr ?_ _ _
    funext i
    fin_cases i
    · rfl
    · rfl
    · show ((x.1 * y.1) * (x.2 * y.2))⁻¹ = (x.1 * x.2)⁻¹ * (y.1 * y.2)⁻¹
      rw [← mul_inv, mul_mul_mul_comm]

theorem dm_apply (x : Kˣ × Kˣ) :
    (dm x : SL3 K) = diagSL (dmVec x.1 x.2) (prod_dmVec x.1 x.2) := rfl

theorem dm_mem_CenTor {p : ℕ} (x : Kˣ × Kˣ) : (dm x : SL3 K) ∈ CenTor p K :=
  diagSL_mem_CenTor (dmVec x.1 x.2) (prod_dmVec x.1 x.2)

theorem exists_dm_of_mem_CenTor {p : ℕ} {ζ : Kˣ} (hζ : IsZeta p ζ) {m : SL3 K}
    (hm : m ∈ CenTor p K) : ∃ x : Kˣ × Kˣ, dm x = m := by
  obtain ⟨v, hv, rfl⟩ := exists_diagSL_of_mem_CenTor hζ hm
  refine ⟨(v 0, v 1), ?_⟩
  rw [dm_apply]
  refine diagSL_congr ?_ _ _
  funext i
  have h2 : v 2 = (v 0 * v 1)⁻¹ := by
    rw [Fin.prod_univ_three] at hv
    exact eq_inv_of_mul_eq_one_right hv
  fin_cases i
  · rfl
  · rfl
  · exact h2.symm

end Concrete

section Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  {ρ : SL3 K →* G}

theorem mem_inf_centralizer_iff_dm (hp : p.Prime) (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ)
    {ζ : Kˣ} (hζ : IsZeta p ζ) {x : G} :
    x ∈ J ⊓ Subgroup.centralizer (A : Set G) ↔ x ∈ (ρ.comp dm).range := by
  rw [hρ.mem_inf_centralizer_iff hp h]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨y, rfl⟩ := exists_dm_of_mem_CenTor hζ hm
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨dm y, dm_mem_CenTor y, rfl⟩

theorem Vof_eq (hp : p.Prime) (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) :
    Vof A J = ((ρ.comp dm).ker.comap (powMonoidHom 3 : Kˣ × Kˣ →* Kˣ × Kˣ)).map (ρ.comp dm) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro d ⟨hd, hd3⟩
    obtain ⟨X, rfl⟩ := (mem_inf_centralizer_iff_dm hp h hρ hζ).1 hd
    refine ⟨X, ?_, rfl⟩
    show (ρ.comp dm) (X ^ 3) = 1
    rw [map_pow]
    exact hd3
  · rintro d ⟨X, hX, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨(mem_inf_centralizer_iff_dm hp h hρ hζ).2 ⟨X, rfl⟩, ?_⟩
    have : (ρ.comp dm) (X ^ 3) = 1 := hX
    rwa [map_pow] at this

theorem mem_Vof_iff (hp : p.Prime) (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) {d : G} :
    d ∈ Vof A J ↔ d ∈ J ⊓ Subgroup.centralizer (A : Set G) ∧ d ^ 3 = 1 := by
  constructor
  · intro hd
    rw [Vof_eq hp h hρ hζ] at hd
    obtain ⟨X, hX, rfl⟩ := hd
    refine ⟨(mem_inf_centralizer_iff_dm hp h hρ hζ).2 ⟨X, rfl⟩, ?_⟩
    have : (ρ.comp dm) (X ^ 3) = 1 := hX
    rwa [map_pow] at this
  · intro hd
    exact Subgroup.subset_closure hd

variable [Finite K]

theorem jLemmaA_part1 (hp : p.Prime) (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) (h9 : 9 ∣ Nat.card K - 1) :
    CFSG.IsElementaryAbelian 3 (Vof A J) ∧ Nat.card (Vof A J) = 9 := by
  obtain ⟨ε, hε⟩ := exists_unit_orderOf_nine h9
  have hker : ∀ z ∈ (ρ.comp dm).ker, ∃ x : Kˣ × Kˣ, x ^ 3 = z := by
    intro z hz
    have hzc : diagSL (dmVec z.1 z.2) (prod_dmVec z.1 z.2) ∈ Subgroup.center (SL3 K) :=
      hρ.ker_central (MonoidHom.mem_ker.2 hz)
    have hab : z.1 = z.2 := by
      simpa [dmVec] using KFOUT3.const_of_diagSL_mem_center hzc 0 1
    have h02 : z.1 = (z.1 * z.2)⁻¹ := by
      simpa [dmVec] using KFOUT3.const_of_diagSL_mem_center hzc 0 2
    have h3 : z.1 ^ 3 = 1 := by
      rw [← hab] at h02
      rw [pow_three', mul_assoc]
      exact mul_eq_one_iff_eq_inv.2 h02
    obtain ⟨x, hx⟩ := exists_cube_of_pow_three hε h3
    refine ⟨(x, x), ?_⟩
    ext <;> simp [hx, hab]
  rw [Vof_eq hp h hρ hζ]
  refine ⟨?_, ?_⟩
  · apply Torsion37.isElementaryAbelian_of_forall
    · rintro _ ⟨X, -, rfl⟩ _ ⟨Y, -, rfl⟩
      rw [← map_mul, ← map_mul, mul_comm X Y]
    · rintro _ ⟨X, hX, rfl⟩
      rw [← map_pow]
      exact hX
  · rw [card_cube_comap (ρ.comp dm) hker]
    exact card_cube_ker_prod (isPrimitiveRoot_cube hε)

end Assembly

end CFSG.RankThree.PartOne.N143
