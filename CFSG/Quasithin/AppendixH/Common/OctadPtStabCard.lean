module

public import CFSG.Quasithin.AppendixH.Common.OctadOrbit
public import CFSG.Quasithin.AppendixH.Common.OctadPtStab
public import CFSG.Quasithin.Background.H16TwoM22PfA

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code
open CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def octad0 : Finset (Fin 24) := Finset.univ.filter fun i => (i : ℕ) < 8

theorem isOctad_octad0 : IsOctad octad0 := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · have hbvec : ∀ i : Fin 24, bvec 24 255 i = if (i : ℕ) < 8 then 1 else 0 := by
      intro i
      have htb : (255 : ℕ).testBit (i : ℕ) = decide ((i : ℕ) < 8) := by
        rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
      simp only [bvec, htb]
      by_cases hi : (i : ℕ) < 8 <;> simp [hi]
    rw [mem_golayC_iff']
    have h : Multiplicative.toAdd (eY octad0) = bvec 24 255 := by
      funext i
      rw [toAdd_eY, hbvec i]
      by_cases hi : (i : ℕ) < 8
      · simp [octad0, hi]
      · simp [octad0, hi]
    rw [h]
    exact (bvec_mem_C_iff 255).2 (by decide +kernel)

theorem octFix_octad0 : octFix octad0 = CFSG.Quasithin.H.Mathieu.H16Pf.fixO := by
  ext g
  simp only [mem_octFix_iff, M24g, CFSG.Quasithin.H.Mathieu.H16Pf.fixO]
  constructor
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, fun i hi => hfix i (by simpa [octad0] using hi)⟩
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, fun i hi => hfix i (by simpa [octad0] using hi)⟩

private theorem card_fixO_eq : Nat.card CFSG.Quasithin.H.Mathieu.H16Pf.fixO = 16 := by
  have hinj : Function.Injective koPerm := by
    intro s t h
    have hs := koPerm_eight s
    rw [h, koPerm_eight t] at hs
    exact Fin.ext (by omega)
  have h : (CFSG.Quasithin.H.Mathieu.H16Pf.fixO : Set S24) = Set.range koPerm := by
    ext σ
    simp only [SetLike.mem_coe, mem_fixO_iff, Set.mem_range]
    exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩
  rw [← SetLike.coe_sort_coe, h, Nat.card_range_of_injective hinj,
    Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem card_octFix0 : Nat.card (octFix octad0) = 16 := by
  rw [octFix_octad0, card_fixO_eq]

theorem card_octFix {O : Finset (Fin 24)} (hO : IsOctad O) :
    Nat.card (octFix O) = 16 := by
  obtain ⟨σ, hσ, hσO⟩ := exists_smul_octad_eq isOctad_octad0 hO
  rw [← hσO, octFix_smul hσ]
  rw [Subgroup.card_map_of_injective (MulAut.conj σ).injective]
  exact card_octFix0

private theorem isMulCommutative_fixO : IsMulCommutative CFSG.Quasithin.H.Mathieu.H16Pf.fixO :=
  IsMulCommutative.of_comm fun x y => by
    apply Subtype.ext
    obtain ⟨s, hs⟩ := (mem_fixO_iff (x : S24)).1 x.2
    obtain ⟨t, ht⟩ := (mem_fixO_iff (y : S24)).1 y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs, ht, koPerm_mul, koPerm_mul]
    congr 1
    apply Fin.ext
    simp [xorF, Nat.xor_comm]

private theorem isElemAbelian_fixO : CFSG.Open.IsElemAbelian 2
    CFSG.Quasithin.H.Mathieu.H16Pf.fixO := by
  refine ⟨isMulCommutative_fixO, ?_⟩
  intro x hx
  obtain ⟨t, ht⟩ := (mem_fixO_iff x).1 hx
  rw [ht, pow_two, koPerm_mul_self]

private theorem isElemAbelian_map {G : Type*} [Group G] {E : Subgroup G} (f : MulAut G)
    (hE : CFSG.Open.IsElemAbelian 2 E) :
    CFSG.Open.IsElemAbelian 2 (E.map f.toMonoidHom) := by
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩
  · apply Subtype.ext
    obtain ⟨a', ha', ha⟩ := (Subgroup.mem_map).1 a.2
    obtain ⟨b', hb', hb⟩ := (Subgroup.mem_map).1 b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_map).1 hx
    rw [← hyx, ← map_pow, hE.2 y hy, map_one]

theorem isElemAbelian_octFix {O : Finset (Fin 24)}
    (hO : IsOctad O) : CFSG.Open.IsElemAbelian 2 (octFix O) := by
  obtain ⟨σ, hσ, hσO⟩ := exists_smul_octad_eq isOctad_octad0 hO
  have h0 : CFSG.Open.IsElemAbelian 2 (octFix octad0) := by
    rw [octFix_octad0]
    exact isElemAbelian_fixO
  rw [← hσO, octFix_smul hσ]
  exact isElemAbelian_map (MulAut.conj σ) h0

theorem isPGroup_octFix {O : Finset (Fin 24)} (hO : IsOctad O) :
    IsPGroup 2 (octFix O) := by
  refine IsPGroup.of_card (n := 4) ?_
  rw [card_octFix hO]
  norm_num

private theorem existsUnique_octFix0 {i j : Fin 24} (hi : i ∉ octad0) (hj : j ∉ octad0) :
    ∃! g : ↥(octFix octad0), (g : S24) i = j := by
  have hi8 : 8 ≤ (i : ℕ) := by
    by_contra h
    exact hi (by simp [octad0]; omega)
  have hj8 : 8 ≤ (j : ℕ) := by
    by_contra h
    exact hj (by simp [octad0]; omega)
  let a : Fin 16 := ⟨(i : ℕ) - 8, by omega⟩
  let b : Fin 16 := ⟨(j : ℕ) - 8, by omega⟩
  have hi_eq : i = ⟨8 + a, by omega⟩ := Fin.ext (by simp [a]; omega)
  have hj_eq : j = ⟨8 + b, by omega⟩ := Fin.ext (by simp [b]; omega)
  let t : Fin 16 := xorF a b
  have hlt : (a : ℕ) ^^^ (b : ℕ) < 16 := Nat.xor_lt_two_pow (n := 4) a.isLt b.isLt
  have htval : (t : ℕ) = (a : ℕ) ^^^ (b : ℕ) := by
    show ((a : ℕ) ^^^ (b : ℕ)) % 16 = (a : ℕ) ^^^ (b : ℕ)
    exact Nat.mod_eq_of_lt hlt
  refine ⟨⟨koPerm t, ?_⟩, ?_, ?_⟩
  · rw [octFix_octad0]
    exact (mem_fixO_iff _).2 ⟨t, rfl⟩
  · show koPerm t i = j
    rw [hi_eq, hj_eq]
    apply Fin.ext
    rw [koPerm_val]
    congr 1
    rw [htval, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  · intro g hg
    obtain ⟨s, hs⟩ := (mem_fixO_iff (g : S24)).1 (by rw [← octFix_octad0]; exact g.2)
    apply Subtype.ext
    rw [hs]
    have h1 : koPerm s i = j := by rw [← hs]; exact hg
    rw [hi_eq, hj_eq] at h1
    have h2 : 8 + ((a : ℕ) ^^^ (s : ℕ)) = 8 + (b : ℕ) := by
      have hp := congrArg (fun p : Fin 24 => (p : ℕ)) h1
      simpa [koPerm_val] using hp
    have he : (a : ℕ) ^^^ (s : ℕ) = (b : ℕ) := Nat.add_left_cancel h2
    have hsval : (s : ℕ) = (t : ℕ) := by
      have hs_id : (s : ℕ) = (a : ℕ) ^^^ ((a : ℕ) ^^^ (s : ℕ)) := by
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rw [hs_id, he, htval]
    exact congrArg koPerm (Fin.ext hsval)

theorem octFix_regular {O : Finset (Fin 24)} (hO : IsOctad O)
    {i j : Fin 24} (hi : i ∉ O) (hj : j ∉ O) : ∃! g : ↥(octFix O), (g : S24) i = j := by
  obtain ⟨σ, hσ, hσO⟩ := exists_smul_octad_eq isOctad_octad0 hO
  have hi' : σ⁻¹ i ∉ octad0 := by
    intro h
    apply hi
    rw [← hσO]
    have hm : σ • (σ⁻¹ i) ∈ σ • octad0 := Finset.smul_mem_smul_finset h
    simpa using hm
  have hj' : σ⁻¹ j ∉ octad0 := by
    intro h
    apply hj
    rw [← hσO]
    have hm : σ • (σ⁻¹ j) ∈ σ • octad0 := Finset.smul_mem_smul_finset h
    simpa using hm
  obtain ⟨g₀, hg₀, huniq⟩ := existsUnique_octFix0 hi' hj'
  have heq : (octFix octad0).map (MulAut.conj σ).toMonoidHom = octFix O := by
    rw [← octFix_smul hσ, hσO]
  have mem_conj : ∀ x : ↥(octFix octad0), σ * (x : S24) * σ⁻¹ ∈ octFix O := by
    intro x
    rw [← MulAut.conj_apply]
    have hx : (MulAut.conj σ) x ∈ (octFix octad0).map (MulAut.conj σ).toMonoidHom :=
      Subgroup.mem_map_of_mem _ x.2
    have hx' : (MulAut.conj σ) x ∈ octFix (σ • octad0) := by
      rw [octFix_smul hσ]; exact hx
    rwa [hσO] at hx'
  refine ⟨⟨σ * (g₀ : S24) * σ⁻¹, mem_conj g₀⟩, ?_, ?_⟩
  · show (σ * (g₀ : S24) * σ⁻¹) i = j
    have h1 : (σ * (g₀ : S24) * σ⁻¹) i = σ ((g₀ : S24) (σ⁻¹ i)) := rfl
    rw [h1, hg₀]
    exact Equiv.apply_symm_apply σ j
  · intro g' hg'
    have hg'mem : (g' : S24) ∈ (octFix octad0).map (MulAut.conj σ).toMonoidHom := by
      rw [heq]; exact g'.2
    obtain ⟨x, hx, hxg⟩ := (Subgroup.mem_map).1 hg'mem
    have hxg' : σ * (x : S24) * σ⁻¹ = (g' : S24) := by
      simpa [MulAut.conj_apply] using hxg
    have hxij : (x : S24) (σ⁻¹ i) = σ⁻¹ j := by
      have h1 : (σ * (x : S24) * σ⁻¹) i = j := by rw [hxg']; exact hg'
      have h1' : σ ((x : S24) (σ⁻¹ i)) = j := by
        simpa only [Equiv.Perm.mul_apply] using h1
      have h2 := congrArg σ.symm h1'
      simpa [Equiv.Perm.inv_def] using h2
    have hxg₀ : (⟨x, hx⟩ : ↥(octFix octad0)) = g₀ := huniq ⟨x, hx⟩ hxij
    have hxg₀' : (x : S24) = (g₀ : S24) := congrArg Subtype.val hxg₀
    apply Subtype.ext
    rw [← hxg', hxg₀']

end CFSG.ASVolI.AppH
