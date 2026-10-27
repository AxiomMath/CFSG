module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4GC

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Inj

variable {G H : Type*} [Group G] [Group H]

theorem map_centralizer_of_injective (ι : H →* G) (hι : Function.Injective ι) (S : Set H) :
    (Subgroup.centralizer S).map ι = ι.range ⊓ Subgroup.centralizer (ι '' S) := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc s hs]
  · rintro ⟨⟨c, rfl⟩, hg⟩
    refine ⟨c, Subgroup.mem_centralizer_iff.mpr fun s hs => hι ?_, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hg (ι s) ⟨s, hs, rfl⟩

theorem map_pCoreOf_of_injective (ι : H →* G) (hι : Function.Injective ι) (A : Subgroup H) :
    (pCoreOf 2 A).map ι = pCoreOf 2 (A.map ι) := by
  set eA := A.equivMapOfInjective ι hι with heA
  have h1 : CFSG.Open.pCore 2 ↥(A.map ι) = (CFSG.Open.pCore 2 ↥A).map eA.toMonoidHom := by
    rw [CFSG.pCore_map_iso 2 eA]
  have h2 : (A.map ι).subtype.comp eA.toMonoidHom = ι.comp A.subtype := by
    ext a
    rfl
  rw [pCoreOf, pCoreOf, h1, Subgroup.map_map, Subgroup.map_map, h2]

theorem map_centerOf_of_injective (ι : H →* G) (hι : Function.Injective ι) (A : Subgroup H) :
    (centerOf A).map ι = centerOf (A.map ι) := by
  rw [centerOf, centerOf, Subgroup.map_inf_eq _ _ ι hι, map_centralizer_of_injective ι hι,
    Subgroup.coe_map, ← inf_assoc, inf_of_le_left (Subgroup.map_le_range ι A)]

theorem isSylowTwoOf_map_iff (ι : H →* G) (hι : Function.Injective ι) {S Y : Subgroup H} :
    IsSylowTwoOf (S.map ι) (Y.map ι) ↔ IsSylowTwoOf S Y := by
  have hP : IsPGroup 2 ↥(S.map ι) ↔ IsPGroup 2 ↥S :=
    ⟨fun h => h.of_injective (S.equivMapOfInjective ι hι).toMonoidHom
        (S.equivMapOfInjective ι hι).injective,
      fun h => h.map ι⟩
  have hI : ((S.map ι).subgroupOf (Y.map ι)).index = (S.subgroupOf Y).index :=
    Subgroup.relIndex_map_map_of_injective S Y hι
  rw [IsSylowTwoOf, IsSylowTwoOf, Subgroup.map_le_map_iff_of_injective hι, hP, hI]

end Inj

theorem genM24_of_mulEquiv {X : Type} [Group X] [Finite X] (hX : ModelM24 X) {G : Type}
    [Group G] [Finite G] {K Y V S : Subgroup G} {z : G} (ψ : ↥K ≃* X) (hYK : Y ≤ K)
    (hYp : ⁅Y, Y⁆ = Y) (hYq : IsSporadic .M24 (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hV : V ≤ centerOf (pCoreOf 2 Y)) (hV1 : V ≠ ⊥) (hVY : V = ⁅V, Y⁆) (hS : IsSylowTwoOf S Y)
    (hzV : z ∈ V) (hz1 : z ≠ 1) (hzS : z ∈ Subgroup.centralizer (S : Set G)) :
    IsHat (↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))) ⧸
        CFSG.pCore 2 ↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))))
      (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∧
    K = Y ⊔ perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G)) := by
  set ι : X →* G := K.subtype.comp ψ.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := K.subtype_injective.comp ψ.symm.injective
  have hιr : ι.range = K := by
    rw [hιdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmap : ∀ {A : Subgroup G}, A ≤ K → (A.comap ι).map ι = A := fun hA => by
    rw [Subgroup.map_comap_eq, hιr, inf_of_le_right hA]
  have hVO : V ≤ pCoreOf 2 Y := fun v hv => (hV hv).1
  have hVK : V ≤ K := hVO.trans ((pCoreOf_le 2 Y).trans hYK)
  have hYm : (Y.comap ι).map ι = Y := hmap hYK
  have hVm : (V.comap ι).map ι = V := hmap hVK
  have hSm : (S.comap ι).map ι = S := hmap (hS.1.trans hYK)
  have hzK : z ∈ K := hVK hzV
  have hιz : ι (ψ ⟨z, hzK⟩) = z := by simp [hιdef]
  have hYp' : ⁅Y.comap ι, Y.comap ι⁆ = Y.comap ι :=
    Subgroup.map_injective hι (by rw [Subgroup.map_commutator, hYm, hYp])
  have hYq' : IsSporadic .M24 (↥(Y.comap ι) ⧸ CFSG.pCore 2 ↥(Y.comap ι)) := by
    obtain ⟨e⟩ := hYq
    exact ⟨(J4.pCoreQuotEquiv (((Y.comap ι).equivMapOfInjective ι hι).trans
      (MulEquiv.subgroupCongr hYm))).trans e⟩
  have hV' : V.comap ι ≤ centerOf (pCoreOf 2 (Y.comap ι)) := by
    rw [← Subgroup.map_le_map_iff_of_injective hι, map_centerOf_of_injective ι hι,
      map_pCoreOf_of_injective ι hι, hYm, hVm]
    exact hV
  have hV1' : V.comap ι ≠ ⊥ := fun h => hV1 (by rw [← hVm, h, Subgroup.map_bot])
  have hVY' : V.comap ι = ⁅V.comap ι, Y.comap ι⁆ :=
    Subgroup.map_injective hι (by rw [Subgroup.map_commutator, hYm, hVm]; exact hVY)
  have hS' : IsSylowTwoOf (S.comap ι) (Y.comap ι) :=
    (isSylowTwoOf_map_iff ι hι).mp (by rw [hSm, hYm]; exact hS)
  have hzV' : ψ ⟨z, hzK⟩ ∈ V.comap ι := by
    rw [Subgroup.mem_comap, hιz]
    exact hzV
  have hz1' : ψ ⟨z, hzK⟩ ≠ 1 := fun h => hz1 (by rw [← hιz, h, map_one])
  have hzS' : ψ ⟨z, hzK⟩ ∈ Subgroup.centralizer ((S.comap ι : Subgroup X) : Set X) := by
    refine Subgroup.mem_centralizer_iff.mpr fun s hs => hι ?_
    rw [map_mul, map_mul, hιz]
    exact Subgroup.mem_centralizer_iff.mp hzS (ι s) hs
  obtain ⟨hhat, htop⟩ := hX _ _ _ _ hYp' hYq' hV' hV1' hVY' hS' hzV' hz1' hzS'
  have hKZ : (perfectCore (Subgroup.centralizer ({ψ ⟨z, hzK⟩} : Set X))).map ι =
      perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [map_perfectCore, map_centralizer_of_injective ι hι, hιr, Set.image_singleton, hιz]
  refine ⟨?_, ?_⟩
  · have e : ↥(perfectCore (Subgroup.centralizer ({ψ ⟨z, hzK⟩} : Set X))) ≃*
        ↥(perfectCore (K ⊓ Subgroup.centralizer ({z} : Set G))) :=
      ((perfectCore (Subgroup.centralizer ({ψ ⟨z, hzK⟩} : Set X))).equivMapOfInjective ι
        hι).trans (MulEquiv.subgroupCongr hKZ)
    exact IsHat.of_mulEquiv (J4.pCoreQuotEquiv e) hhat
  · have h1 := congrArg (Subgroup.map ι) htop
    rwa [Subgroup.map_sup, hYm, hKZ, ← MonoidHom.range_eq_map, hιr] at h1

end CFSG.Quasithin.H13.Ch4.G443J4
