module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Fi22OuterWit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Z3Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Z3OuterEleven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Z3OuterGenIdx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore

private theorem fi22oi_outer_mul_mem_P
    {a b : Equiv.Perm (Fin 3510)} (haR : a ∈ fi22R) (hbR : b ∈ fi22R)
    (haP : a ∉ fi22P) (hbP : b ∉ fi22P) : a * b ∈ fi22P := by
  have haU : fi22U * a ∈ fi22P := (mem_fi22R_iff a).1 haR |>.resolve_left haP
  have hbU : fi22U * b ∈ fi22P := (mem_fi22R_iff b).1 hbR |>.resolve_left hbP
  have h1 : fi22U * (fi22U * a) * fi22U⁻¹ ∈ fi22P := fi22U_conj_mem haU
  have h2 : (fi22U * (fi22U * a) * fi22U⁻¹) * (fi22U * b) ∈ fi22P :=
    fi22P.mul_mem h1 hbU
  have he : (fi22U * (fi22U * a) * fi22U⁻¹) * (fi22U * b) = a * b := by
    calc (fi22U * (fi22U * a) * fi22U⁻¹) * (fi22U * b)
        = (fi22U * fi22U) * a * (fi22U⁻¹ * fi22U) * b := by group
      _ = a * b := by simp [fi22U_mul_self]
  rwa [he] at h2

private theorem fi22oi_conj_not_mem_P
    {c τ : Equiv.Perm (Fin 3510)} (hc : c ∈ fi22P) (hτR : τ ∈ fi22R) (hτP : τ ∉ fi22P) :
    c * τ * c⁻¹ ∉ fi22P := by
  intro h
  apply hτP
  have hc'R : c⁻¹ ∈ fi22R := fi22R.inv_mem (fi22P_le_R hc)
  have hnorm := Subgroup.mem_normalizer_iff.1 (fi22R_le_normalizer hc'R)
  have hmem : c⁻¹ * (c * τ * c⁻¹) * (c⁻¹)⁻¹ ∈ fi22P := (hnorm (c * τ * c⁻¹)).1 h
  have heq : c⁻¹ * (c * τ * c⁻¹) * (c⁻¹)⁻¹ = τ := by group
  rwa [heq] at hmem

private lemma fi22oi_pow_three_of_mem_center {L : Type*} [Group L]
    (hZ : Nat.card (Subgroup.center L) = 3) {y : L} (hy : y ∈ Subgroup.center L) :
    y ^ 3 = 1 := by
  have h := pow_card_eq_one' (G := ↥(Subgroup.center L)) (x := ⟨y, hy⟩)
  rw [hZ] at h
  simpa using congrArg Subtype.val h

theorem fi22_outer_index_ge_sixteen
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hq : IsQuasisimple ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* CFSG.Blueprint.NativeSporadic.Fi22)
    {U : Type} [CommGroup U] [Finite U] (hU : ∀ w : U, w * w = 1) (ρ : ↥Y →* MulAut U)
    (hρL : Function.Injective (ρ.comp (Subgroup.inclusion hLY)))
    {ζ : ↥L} (hζ : ζ ∈ Subgroup.center ↥L) (hζ1 : ζ ≠ 1)
    (hfixL : ∀ u : U, (ρ.comp (Subgroup.inclusion hLY)) ζ u = u → u = 1)
    (h54 : 2 ^ 54 ≤ Nat.card U) {t : MulAut W} (htY : t ∈ Y) (hto : orderOf t = 2)
    (htL : t ∉ L) :
    2 ^ 4 ≤ (fixV (Subgroup.zpowers (ρ ⟨t, htY⟩))).index := by
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨F, hFR, hFP, hsurj, hback, hker⟩ := fi22_outer_transport hLY hLn hF hq e
  let L' : Subgroup ↥Y := L.subgroupOf Y
  let ι : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY
  let t' : ↥Y := ⟨t, htY⟩
  have ht2 : t * t = 1 := by
    rw [← sq, ← hto]
    exact pow_orderOf_eq_one t
  have ht2' : t' * t' = 1 := Subtype.ext ht2
  let τ : Equiv.Perm (Fin 3510) := F t'
  have hτ2mul : τ * τ = 1 := by
    change F t' * F t' = 1
    rw [← map_mul, ht2', map_one]
  have hτP : τ ∉ fi22P := fun h => htL (hback t' h)
  have hτR : τ ∈ fi22R := hFR t'
  have hτ1 : τ ≠ 1 := fun h => hτP (h ▸ fi22P.one_mem)
  have hτ2 : orderOf τ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hτ2mul) hτ1
  have hFP' : ∀ y ∈ L', F y ∈ fi22P := by
    intro y hy
    have hinc : Subgroup.inclusion hLY (ι ⟨y, hy⟩) = y := Subtype.ext rfl
    have := hFP (ι ⟨y, hy⟩)
    rwa [hinc] at this
  have hsurj' : ∀ p ∈ fi22P, ∃ y ∈ L', F y = p := by
    intro p hp
    obtain ⟨l, hl⟩ := hsurj p hp
    exact ⟨Subgroup.inclusion hLY l, l.2, hl⟩
  have hback' : ∀ y : ↥Y, F y ∈ fi22P → y ∈ L' := fun y hy => hback y hy
  have hkerc : ∀ l : ↥L', F (l : ↥Y) = 1 → l ∈ Subgroup.center ↥L' := by
    intro l hlF
    have hinc : Subgroup.inclusion hLY (ι l) = (l : ↥Y) := Subtype.ext rfl
    have hlF' : F (Subgroup.inclusion hLY (ι l)) = 1 := by rw [hinc]; exact hlF
    have hkerl : ι l ∈ Subgroup.center ↥L := hker (ι l) hlF'
    rw [← Subgroup.map_center_eq ι] at hkerl
    obtain ⟨z, hz, hzi⟩ := Subgroup.mem_map.1 hkerl
    have hz_eq : z = l := ι.injective hzi
    exact hz_eq ▸ hz
  have hρ' : ∀ y ∈ L', ρ y = 1 → y = 1 := by
    intro y hy hρy
    have hinc : Subgroup.inclusion hLY (ι ⟨y, hy⟩) = y := Subtype.ext rfl
    have hl : ι ⟨y, hy⟩ = 1 := hρL (by
      rw [map_one]
      change ρ (Subgroup.inclusion hLY (ι ⟨y, hy⟩)) = 1
      rw [hinc]
      exact hρy)
    calc y = Subgroup.inclusion hLY (ι ⟨y, hy⟩) := hinc.symm
      _ = Subgroup.inclusion hLY 1 := by rw [hl]
      _ = 1 := map_one _
  have hker3 : ∀ y ∈ L', F y = 1 → y ^ 3 = 1 := by
    intro y hy hFy
    have hinc : Subgroup.inclusion hLY (ι ⟨y, hy⟩) = y := Subtype.ext rfl
    have hl : ι ⟨y, hy⟩ ∈ Subgroup.center ↥L := hker (ι ⟨y, hy⟩) (by rw [hinc]; exact hFy)
    have hl3 : (ι ⟨y, hy⟩) ^ 3 = 1 := fi22oi_pow_three_of_mem_center hZ hl
    have hmap : (Subgroup.inclusion hLY (ι ⟨y, hy⟩)) ^ 3 = 1 := by
      rw [← map_pow, hl3, map_one]
    rwa [hinc] at hmap
  have hperf' : Group.IsPerfect ↥L' := by
    haveI : Group.IsPerfect ↥L := hq.1
    exact Group.IsPerfect.ofSurjective (f := (ι.symm).toMonoidHom) ι.symm.surjective
  have hζ' : ι.symm ζ ∈ Subgroup.center ↥L' :=
    Subgroup.comap_center_le_center (f := ι.toMonoidHom) ι.injective (by
      change ι (ι.symm ζ) ∈ Subgroup.center ↥L
      rw [ι.apply_symm_apply]
      exact hζ)
  have hfix' : ∀ u : U, ρ (ι.symm ζ : ↥Y) u = u → u = 1 := by
    intro u hu
    have hcoe : (ι.symm ζ : ↥Y) = Subgroup.inclusion hLY ζ := Subtype.ext rfl
    rw [hcoe] at hu
    exact hfixL u hu
  rcases fi22_outerWitness hτR hτ2 hτP with ⟨c, hcP, h11⟩ | ⟨cs, hlen, hcs, hgen⟩
  · obtain ⟨l, hl⟩ := hsurj c hcP
    let l' : ↥Y := Subgroup.inclusion hLY l
    let y : ↥Y := t' * (l' * t' * l'⁻¹)
    have hFy : F y = τ * (c * τ * c⁻¹) := by
      change F (t' * (l' * t' * l'⁻¹)) = F t' * (c * F t' * c⁻¹)
      simp only [map_mul, map_inv]
      rw [show F l' = c from hl]
    have h11' : orderOf (F y) = 11 := by rw [hFy]; exact h11
    have hcτcR : c * τ * c⁻¹ ∈ fi22R :=
      fi22R.mul_mem (fi22R.mul_mem (fi22P_le_R hcP) hτR) (fi22R.inv_mem (fi22P_le_R hcP))
    have hcτcP : c * τ * c⁻¹ ∉ fi22P := fi22oi_conj_not_mem_P hcP hτR hτP
    have hFyP : F y ∈ fi22P := by
      rw [hFy]
      exact fi22oi_outer_mul_mem_P hτR hcτcR hτP hcτcP
    have hyL : y ∈ L' := hback' y hFyP
    have := outer_index_ge_of_order_eleven hU L' F ρ hρ' hker3 ht2' hyL h11'
    exact le_trans (by norm_num) this
  · exact outer_index_ge_of_generation hU L' hperf' F fi22P hFP' hsurj' hback' hkerc ρ
      (ζ := ι.symm ζ) hζ' hfix' h54 ht2' cs hlen hcs hgen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
