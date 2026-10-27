module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SPsl2Cent
public import CFSG.RankThree.PartTwo.Sec8.Hering611SJordan
public import CFSG.RankThree.PartTwo.KFacts.K72FixL2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG.GorensteinWalter

theorem exists_fusion_psl2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3 ^ 6)
    {τ : MulAut (PSL2 F)} (hτ3 : τ ^ 3 = 1) (hτout : ¬ KFacts.IsInnerAut τ)
    {b : PSL2 F} (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) (hτb : τ b = b) :
    ∃ u : PSL2 F, u * b = b * u ∧ (τ u)⁻¹ * u = b := by
  obtain ⟨hUe, hUcard⟩ := centralizer_psl2_of_pow_three (n := 6) (by norm_num) hF hb1 hb3
  set U : Subgroup (PSL2 F) := Subgroup.centralizer ({b} : Set (PSL2 F)) with hUdef
  have hmemU : ∀ y : PSL2 F, y ∈ U ↔ y * b = b * y := fun y => by
    rw [hUdef, Subgroup.mem_centralizer_singleton_iff]
  have hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hU3 : ∀ x ∈ U, x ^ 3 = 1 := hUe.2
  have hbU : b ∈ U := (hmemU b).mpr rfl
  have hτU : ∀ x ∈ U, τ x ∈ U := by
    intro x hx
    have h : τ (x * b) = τ (b * x) := congrArg (⇑τ) ((hmemU x).mp hx)
    rw [map_mul, map_mul, hτb] at h
    exact (hmemU (τ x)).mpr h
  obtain ⟨σ, hσ3, ⟨ι⟩⟩ := KFacts.exists_eqLocus_mulEquiv_psl2 hτ3 hτout
  set E : Subgroup (PSL2 F) := τ.toMonoidHom.eqLocus (MonoidHom.id (PSL2 F)) with hEdef
  have hbE : b ∈ E := by
    rw [hEdef]
    exact hτb
  have hF' : Nat.card F = (3 ^ 2) ^ 3 := by
    rw [hF]
    norm_num
  have hσcard : Nat.card (GH74.GLS.IVK.fixedField σ) = 3 ^ 2 :=
    KFacts.card_fixedField_of_orderOf_eq_three hσ3 hF'
  set b' : PSL2 (GH74.GLS.IVK.fixedField σ) := ι ⟨b, hbE⟩ with hb'def
  have hb'1 : b' ≠ 1 := by
    intro h
    apply hb1
    have h2 : (⟨b, hbE⟩ : E) = 1 := ι.injective (h.trans (map_one ι).symm)
    exact congrArg Subtype.val h2
  have hb'3 : b' ^ 3 = 1 := by
    have h1 : (⟨b, hbE⟩ : E) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [hb'def, ← map_pow, h1, map_one]
  obtain ⟨-, hC'card⟩ := centralizer_psl2_of_pow_three (n := 2) (by norm_num) hσcard hb'1 hb'3
  set CE : Subgroup E := Subgroup.centralizer ({(⟨b, hbE⟩ : E)} : Set E)
  have hmapC : CE.map ι.toMonoidHom =
      Subgroup.centralizer ({b'} : Set (PSL2 (GH74.GLS.IVK.fixedField σ))) := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h : ι (z * (⟨b, hbE⟩ : E)) = ι ((⟨b, hbE⟩ : E) * z) :=
        congrArg (⇑ι) (Subgroup.mem_centralizer_singleton_iff.mp hz)
      rw [map_mul, map_mul] at h
      exact h
    · intro hy
      refine Subgroup.mem_map.mpr ⟨ι.symm y, ?_, ι.apply_symm_apply y⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply ι.injective
      rw [map_mul, map_mul, ι.apply_symm_apply]
      exact Subgroup.mem_centralizer_singleton_iff.mp hy
  have hcardCE : Nat.card (Subgroup.centralizer ({b'} : Set (PSL2 (GH74.GLS.IVK.fixedField σ))))
      = Nat.card CE := by
    rw [← hmapC]
    exact Subgroup.card_map_of_injective (f := ι.toMonoidHom) ι.injective
  have hCE : CE.map E.subtype = U ⊓ E := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_inf.mpr ⟨(hmemU _).mpr ?_, y.2⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    · intro hx
      have hxE : x ∈ E := (Subgroup.mem_inf.mp hx).2
      refine Subgroup.mem_map.mpr ⟨⟨x, hxE⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact (hmemU x).mp (Subgroup.mem_inf.mp hx).1
  have hInf : Nat.card ↥(U ⊓ E : Subgroup (PSL2 F)) = Nat.card CE := by
    rw [← hCE]
    exact Subgroup.card_subtype E CE
  have hInf3 : Nat.card ↥(U ⊓ E : Subgroup (PSL2 F)) = 3 ^ 2 := by
    rw [hInf, ← hcardCE, hC'card]
  have hcard : Nat.card ↥U = Nat.card ↥(U ⊓ E : Subgroup (PSL2 F)) ^ 3 := by
    rw [hUcard, hInf3]
    norm_num
  obtain ⟨u, huU, hu⟩ := exists_div_of_card_fixed U τ hUc hU3 hτU hτ3 hcard hbU hτb
  exact ⟨u, (hmemU u).mp huU, hu⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
