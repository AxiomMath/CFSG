module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanC
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Components
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanA
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_map_barImage_inf_proj {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    {e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K}
    (heL : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K))) :
    (((barImage (conjClosure D.M L) (D.T ⊓ conjClosure D.M L)).map e.toMonoidHom).map
        (MonoidHom.fst (Bar2 L) (Bar2 K)) = barImage L (D.T ⊓ L)) ∧
      (((barImage (conjClosure D.M L) (D.T ⊓ conjClosure D.M L)).map e.toMonoidHom).map
        (MonoidHom.snd (Bar2 L) (Bar2 K)) = barImage K (D.T ⊓ K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := conjClosure D.M L
  let P : Subgroup G := D.T ⊓ X
  let E : Subgroup (Bar2 L × Bar2 K) := (barImage X P).map e.toMonoidHom
  let UL : Subgroup (Bar2 L) := barImage L (D.T ⊓ L)
  let UK : Subgroup (Bar2 K) := barImage K (D.T ⊓ K)
  have hLX : L ≤ X := by
    rw [show X = L ⊔ K from conjClosure_eq_sup_of_conjSetOf_eq hset]
    exact le_sup_left
  have hKX : K ≤ X := by
    rw [show X = L ⊔ K from conjClosure_eq_sup_of_conjSetOf_eq hset]
    exact le_sup_right
  have hULsyl : IsSylowTwoOf UL ⊤ := uc22r3e5c_isSylowTwoOf_barImage_inf_T hL
  have hUKsyl : IsSylowTwoOf UK ⊤ := uc22r3e5c_isSylowTwoOf_barImage_inf_T hKC
  have hULle : UL ≤ E.map (MonoidHom.fst (Bar2 L) (Bar2 K)) := by
    intro u hu
    obtain ⟨x, hx, hmk⟩ := Subgroup.mem_map.mp hu
    let xX : ↥X := Subgroup.inclusion hLX x
    have hxP : (xX : G) ∈ P :=
      ⟨by simpa [xX] using (Subgroup.mem_subgroupOf.mp hx).1, xX.2⟩
    have hz : (QuotientGroup.mk xX : Bar2 X) ∈ barImage X P :=
      Subgroup.mem_map.mpr ⟨xX, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
    refine Subgroup.mem_map.mpr ⟨e (QuotientGroup.mk xX),
      Subgroup.mem_map.mpr ⟨QuotientGroup.mk xX, hz, rfl⟩, ?_⟩
    rw [heL xX (by simpa [xX] using x.2)]
    exact hmk
  have hUKle : UK ≤ E.map (MonoidHom.snd (Bar2 L) (Bar2 K)) := by
    intro u hu
    obtain ⟨x, hx, hmk⟩ := Subgroup.mem_map.mp hu
    let xX : ↥X := Subgroup.inclusion hKX x
    have hxP : (xX : G) ∈ P :=
      ⟨by simpa [xX] using (Subgroup.mem_subgroupOf.mp hx).1, xX.2⟩
    have hz : (QuotientGroup.mk xX : Bar2 X) ∈ barImage X P :=
      Subgroup.mem_map.mpr ⟨xX, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
    refine Subgroup.mem_map.mpr ⟨e (QuotientGroup.mk xX),
      Subgroup.mem_map.mpr ⟨QuotientGroup.mk xX, hz, rfl⟩, ?_⟩
    rw [heK xX (by simpa [xX] using x.2)]
    exact hmk
  have hSbarSyl : IsSylowTwoOf (barImage X P) ⊤ :=
    CFSG.Quasithin.H13.S126P31.isSylowTwoOf_map_mk' (Z := CFSG.pCore 2 ↥X)
      (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf (uc22r3e5c_isSylowTwoOf_inf hL))
  have hSbar2 : IsPGroup 2 (barImage X P) := hSbarSyl.2.1
  have hE2 : IsPGroup 2 E := hSbar2.map e.toMonoidHom
  have hprojL : E.map (MonoidHom.fst (Bar2 L) (Bar2 K)) = UL :=
    uc22r3e5c_eq_of_isSylowTwoOf_le hULsyl hULle le_top
      (hE2.map (MonoidHom.fst (Bar2 L) (Bar2 K)))
  have hprojK : E.map (MonoidHom.snd (Bar2 L) (Bar2 K)) = UK :=
    uc22r3e5c_eq_of_isSylowTwoOf_le hUKsyl hUKle le_top
      (hE2.map (MonoidHom.snd (Bar2 L) (Bar2 K)))
  exact ⟨hprojL, hprojK⟩

theorem uc22r3e5c_map_barImage_inf_eq_prod {D : Data G}
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hKC : K ∈ calC D.M) (hKne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n : ℕ} (hSz : IsSz (Bar2 L) n)
    {e : Bar2 (conjClosure D.M L) ≃* Bar2 L × Bar2 K}
    (heL : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ L),
      e (QuotientGroup.mk x) = (QuotientGroup.mk (⟨(x : G), hx⟩ : ↥L), 1))
    (heK : ∀ (x : ↥(conjClosure D.M L)) (hx : (x : G) ∈ K),
      e (QuotientGroup.mk x) = (1, QuotientGroup.mk (⟨(x : G), hx⟩ : ↥K))) :
    (barImage (conjClosure D.M L) (D.T ⊓ conjClosure D.M L)).map e.toMonoidHom =
      (barImage L (D.T ⊓ L)).prod (barImage K (D.T ⊓ K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := conjClosure D.M L
  let P : Subgroup G := D.T ⊓ X
  let E : Subgroup (Bar2 L × Bar2 K) := (barImage X P).map e.toMonoidHom
  let UL : Subgroup (Bar2 L) := barImage L (D.T ⊓ L)
  let UK : Subgroup (Bar2 K) := barImage K (D.T ⊓ K)
  have hproj := uc22r3e5c_map_barImage_inf_proj hL hKC hKne hset hSz heL heK
  have hprojL : E.map (MonoidHom.fst (Bar2 L) (Bar2 K)) = UL := hproj.1
  have hprojK : E.map (MonoidHom.snd (Bar2 L) (Bar2 K)) = UK := hproj.2
  have hLX : L ≤ X := by
    rw [show X = L ⊔ K from conjClosure_eq_sup_of_conjSetOf_eq hset]
    exact le_sup_left
  have hKX : K ≤ X := by
    rw [show X = L ⊔ K from conjClosure_eq_sup_of_conjSetOf_eq hset]
    exact le_sup_right
  change E = UL.prod UK
  refine le_antisymm ?_ ?_
  · intro z hz
    exact Subgroup.mem_prod.mpr
      ⟨hprojL ▸ Subgroup.mem_map_of_mem (MonoidHom.fst (Bar2 L) (Bar2 K)) hz,
        hprojK ▸ Subgroup.mem_map_of_mem (MonoidHom.snd (Bar2 L) (Bar2 K)) hz⟩
  · rintro ⟨u, v⟩ ⟨hu, hv⟩
    obtain ⟨x, hx, hmk⟩ := Subgroup.mem_map.mp hu
    obtain ⟨y, hy, hmk2⟩ := Subgroup.mem_map.mp hv
    have hxP : ((Subgroup.inclusion hLX x : ↥X) : G) ∈ P :=
      ⟨by simpa using (Subgroup.mem_subgroupOf.mp hx).1, (Subgroup.inclusion hLX x).2⟩
    have hyP : ((Subgroup.inclusion hKX y : ↥X) : G) ∈ P :=
      ⟨by simpa using (Subgroup.mem_subgroupOf.mp hy).1, (Subgroup.inclusion hKX y).2⟩
    let xX : ↥X := Subgroup.inclusion hLX x
    let yX : ↥X := Subgroup.inclusion hKX y
    have hxPin : xX ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hxP
    have hyPin : yX ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hyP
    refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk (xX * yX), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨xX * yX, (P.subgroupOf X).mul_mem hxPin hyPin, rfl⟩
    have hxXL : ((xX : ↥X) : G) ∈ L := by
      change (x : G) ∈ L
      exact x.2
    have hyXK : ((yX : ↥X) : G) ∈ K := by
      change (y : G) ∈ K
      exact y.2
    · change e (QuotientGroup.mk (xX * yX)) = (u, v)
      rw [QuotientGroup.mk_mul, map_mul, heL xX hxXL, heK yX hyXK]
      change ((QuotientGroup.mk x : Bar2 L), 1) * (1, QuotientGroup.mk y) = (u, v)
      rw [Prod.mk_mul_mk, mul_one, one_mul]
      exact Prod.ext hmk hmk2

theorem uc22r3e5c_quasithin_isSz_of_isSz {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsSz X n) : CFSG.Quasithin.IsSz n X := by
  obtain ⟨a, ha, hna, ⟨e⟩⟩ := uc22r3e5c_exists_sz_equiv h
  subst hna
  exact CFSG.LieType.SuzukiSubgroups.isSz_of_mulEquiv ha e


end CFSG.LocalAnalysis.UniquenessCase.UC22

end
