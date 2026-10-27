module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.CD.L3YC

section Abstract

variable {K : Type*} [Group K]

theorem le_pCore_two {X : Type*} [Group X] {N : Subgroup X} (hN : N.Normal) (hp : IsPGroup 2 N) :
    N ≤ CFSG.pCore 2 X :=
  le_sSup ⟨hN, hp⟩

theorem modO2_map_equiv {N : Subgroup K} [N.Normal] (hN : IsPGroup 2 N) (L' : Subgroup K) :
    Nonempty (↥(L'.map (QuotientGroup.mk' N)) ⧸ CFSG.pCore 2 ↥(L'.map (QuotientGroup.mk' N)) ≃*
      ↥L' ⧸ CFSG.pCore 2 ↥L') := by
  set B : Subgroup (K ⧸ N) := L'.map (QuotientGroup.mk' N) with hB
  let f : ↥L' →* ↥B := (QuotientGroup.mk' N).subgroupMap L'
  have hf : Function.Surjective f := (QuotientGroup.mk' N).subgroupMap_surjective L'
  let g : ↥L' →* ↥B ⧸ CFSG.pCore 2 ↥B := (QuotientGroup.mk' (CFSG.pCore 2 ↥B)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hmem : ∀ x : ↥L', g x = 1 ↔ f x ∈ CFSG.pCore 2 ↥B := fun x => by
    simp only [g, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff _
  have hker : g.ker = CFSG.pCore 2 ↥L' := by
    apply le_antisymm
    ·
      have hPn : ((CFSG.pCore 2 ↥B).comap f).Normal := (CFSG.pCore_normal).comap f
      have hP2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥B).comap f) := by
        intro x
        obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (G := ↥B) (p := 2)) ⟨f x, x.2⟩
        have hm' : (f x) ^ (2 ^ m) = 1 := congrArg Subtype.val hm
        have hx1 : f ((x : ↥L') ^ (2 ^ m)) = 1 := by rw [map_pow, hm']
        have hxN : (((x : ↥L') ^ (2 ^ m) : ↥L') : K) ∈ N := by
          have h1 : (QuotientGroup.mk' N) (((x : ↥L') ^ (2 ^ m) : ↥L') : K) = 1 :=
            congrArg Subtype.val hx1
          exact (QuotientGroup.eq_one_iff _).mp h1
        obtain ⟨n, hn⟩ := hN ⟨_, hxN⟩
        refine ⟨m + n, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hn
        simpa [pow_add, pow_mul] using this
      intro x hx
      exact le_pCore_two hPn hP2 ((hmem x).mp hx)
    · intro x hx
      refine (hmem x).mpr ?_
      have hn : ((CFSG.pCore 2 ↥L').map f).Normal := (CFSG.pCore_normal).map f hf
      have hp : IsPGroup 2 ↥((CFSG.pCore 2 ↥L').map f) := by
        intro y
        obtain ⟨x', hx', hxy⟩ := y.2
        obtain ⟨n, hn'⟩ := (CFSG.pCore_isPGroup (G := ↥L') (p := 2)) ⟨x', hx'⟩
        refine ⟨n, Subtype.ext ?_⟩
        have h1 : x' ^ (2 ^ n) = 1 := congrArg Subtype.val hn'
        have h2 : ((y : ↥B)) ^ (2 ^ n) = 1 := by rw [← hxy, ← map_pow, h1, map_one]
        simpa using h2
      exact le_pCore_two hn hp ⟨x, hx, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)).symm⟩

end Abstract

section Ambient

variable {G : Type} [Group G]

theorem modO2_modO2Image_equiv {H L : Subgroup G} (hLH : L ≤ H) :
    Nonempty (ModO2 (modO2Image H L) ≃* (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have hN : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  obtain ⟨e1⟩ := modO2_map_equiv (N := CFSG.pCore 2 ↥H) (CFSG.pCore_isPGroup (G := ↥H) (p := 2))
    (L.subgroupOf H)
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  exact ⟨e1.trans (QuotientGroup.congr (CFSG.pCore 2 ↥(L.subgroupOf H)) (CFSG.pCore 2 ↥L) e
    (CFSG.pCore_map_iso 2 e))⟩

end Ambient

end Stellmacher.CD.L3YC

end CFSG.Quasithin
