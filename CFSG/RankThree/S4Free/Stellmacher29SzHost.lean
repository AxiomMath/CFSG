module

public import CFSG.RankThree.S4Free.Stellmacher25dNat
public import CFSG.RankThree.S4Free.Stellmacher29Sz

public section

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin Subgroup

universe u

theorem IsL24Core.map_oTwo_le_of_isPGroup {H : Type*} [Group H] [Finite H]
    {S M A L : Subgroup H} (h : IsL24Core S M A L) (hS : IsPGroup 2 S) :
    (oTwo ↥L).map L.subtype ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (S.subgroupOf L) := hS.comap_subtype
  have hle : oTwo ↥L ≤ S.subgroupOf L := by
    have h1 := (oTwo_isPGroup ↥L).le_sylow_of_normal
      (hP.toSylow (show ¬ 2 ∣ (S.subgroupOf L).index from h.not_dvd_relIndex))
    rwa [IsPGroup.toSylow_coe] at h1
  calc (oTwo ↥L).map L.subtype ≤ (S.subgroupOf L).map L.subtype := map_mono hle
    _ ≤ S := by
      rw [subgroupOf_map_subtype]
      exact inf_le_left

variable {V : Type u} [CommGroup V] [Finite V]

theorem false_of_isL24Sz_of_agt
    (hV : ∀ v : V, v ^ 2 = 1) {S M A L : Subgroup (MulAut V)} {Z₀ : Subgroup V}
    (hS : IsPGroup 2 S) (hSM : S ≤ M) (hMZ : M ≤ stabSub Z₀) (hLM : L ⊓ stabSub Z₀ ≤ M)
    (hAel : CFSG.Open.IsElemAbelian 2 A) (hq : IsQuadratic A) (hZA : Z₀ ≤ fixV A)
    (hgt : AGt S Z₀ 1) (hL : IsL24Sz S M A L)
    (hAU : codimOn A (spanOrbit L Z₀) ≤ dimOn A (spanOrbit L Z₀)) : False := by
  set U := spanOrbit L Z₀ with hUdef
  have hnorm : ∀ l ∈ L, Z₀.map l.toMonoidHom = Z₀ → l ∈ M := by
    intro l hl hlZ
    refine hLM ⟨hl, fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
    · rw [← hlZ] at hu
      obtain ⟨z, hz, hzu⟩ := hu
      rwa [← l.injective hzu]
    · rw [← hlZ]
      exact ⟨u, hu, rfl⟩
  have h25 : Hyp25Sz S M A L Z₀ U :=
    ⟨hL, hS, hSM, hAel, hq, hZA, le_spanOrbit L Z₀, le_stabSub_spanOrbit L Z₀,
      fun W hW => spanOrbit_le hW, hnorm⟩
  obtain ⟨R, hRn, hOR, hodd, a, ha, K, hKf, hKfin, hK, ⟨e⟩⟩ := hL.suzuki
  obtain ⟨b, hbA, hbO⟩ := hL.exists_mem_not_mem_oTwo hAel
  obtain ⟨-, k2, -, k4, k5⟩ := h25.fixV_eq hV hbA hbO
  have hidx : (A ⊓ (oTwo ↥L).map L.subtype).relIndex A ≤ 2 ^ (2 * a + 1) := by
    rw [Subgroup.inf_relIndex_left]
    exact relIndex_le_two_pow_of_mulEquiv hL.le hAel hOR hodd ha hK e
  exact false_of_szData hV hS hSM hMZ hLM hAel hq hZA hgt hL.le hL.not_le hL.sup_conj
    (hL.toIsL24Core.map_oTwo_le_of_isPGroup hS) (le_spanOrbit L Z₀)
    (le_stabSub_spanOrbit L Z₀) (fun W hW => spanOrbit_le hW) hAU R ha hK e
    (fun x hxL hxM => h25.sup_fixV_conj_eq hV hxL hxM) hbA ⟨k2, k4, k5⟩
    (h25.chief hV R hOR hodd ha hK e) hidx

theorem hyp29_sz
    (hSub : CFSG.LocalAnalysis.WeakClosure81.SuzukiSubgroupInput) : Hyp29.{u} HostClass.sz := by
  intro V _ _ H S A Z₀ hset hcoat hAS hA hAD hq hZA hA0 hAle hgt
  have hV := hset.sq
  have hS := hset.isPGroup
  obtain ⟨L, hLH, hL⟩ := exists_isL24_or_isL24Sz_of_szSections_subgroup hSub hset.holds hS
    hset.le hset.not_dvd inf_le_left hcoat (le_inf hset.le hset.stab) hAS hA hAD
  rcases hL with hL | hL
  · exact Or.inl ⟨L, hLH, hL⟩
  · exfalso
    have hAU : codimOn A (spanOrbit L Z₀) ≤ dimOn A (spanOrbit L Z₀) := by
      have h1 := codimOn_mul_le_of_isMinOff hV hS hA0 (le_top : spanOrbit L Z₀ ≤ ⊤)
      have hd : 0 < dimOn A ⊤ := hA0.1.dimOn_pos hS
      have : codimOn A (spanOrbit L Z₀) * dimOn A ⊤ ≤ dimOn A (spanOrbit L Z₀) * dimOn A ⊤ :=
        h1.trans (Nat.mul_le_mul_left _ hAle)
      exact Nat.le_of_mul_le_mul_right this hd
    exact false_of_isL24Sz_of_agt hV hS (le_inf hset.le hset.stab) inf_le_right
      (fun g hg => ⟨hLH hg.1, hg.2⟩) hA hq hZA hgt hL hAU

end CFSG.RankThree.S4Free.Stell
