module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSixB
public import CFSG.LocalAnalysis.WeakClosure81.TwelveQuot
public import CFSG.LocalAnalysis.WeakClosure81.TwelveSection

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {n : ℕ}

theorem Setting12Two.ker_eq_of_irreducible (hMult : SchurMultiplierInput) (h : Setting12Two A M n)
    (ρ : G →* LGL 2 V) (hq : RepQuad ρ A) (hirr : IsChiefFactor ρ ⊤ ⊥)
    (hnt : IsNoncentral ρ ⊤ ⊥) : ρ.ker = CFSG.Quasithin.kerIn M ⊤ := by
  haveI : ρ.ker.Normal := MonoidHom.normal_ker ρ
  have hCK : ρ.ker ≤ CFSG.Quasithin.kerIn M ⊤ := h.ker_le_of_irreducible ρ hirr hnt
  have hCM : ρ.ker ≤ M := hCK.trans CFSG.Quasithin.kerIn_le
  have h' : Setting12Two (A.map (QuotientGroup.mk' ρ.ker))
      (M.map (QuotientGroup.mk' ρ.ker)) n := h.quotient ρ.ker hCK
  have hq' : RepQuad (QuotientGroup.kerLift ρ) (A.map (QuotientGroup.mk' ρ.ker)) :=
    (repQuad_kerLift ρ A).2 hq
  have hirr' : IsChiefFactor (QuotientGroup.kerLift ρ) (⊤ : Submodule (ZMod 2) V) ⊥ :=
    (isChiefFactor_kerLift ρ ⊤ ⊥).2 hirr
  have hnt' : IsNoncentral (QuotientGroup.kerLift ρ) (⊤ : Submodule (ZMod 2) V) ⊥ :=
    (isNoncentral_kerLift ρ ⊤ ⊥).2 hnt
  have hK' : CFSG.Quasithin.kerIn (M.map (QuotientGroup.mk' ρ.ker)) ⊤ = ⊥ :=
    twelveSix_irreducible hMult h' (QuotientGroup.kerLift ρ)
      (QuotientGroup.kerLift_injective ρ) hq' hirr' hnt'
  have hmap : (CFSG.Quasithin.kerIn M ⊤).map (QuotientGroup.mk' ρ.ker) = ⊥ := by
    rw [← kerIn_map_top_eq M ρ.ker hCM, hK']
  have hle : CFSG.Quasithin.kerIn M ⊤ ≤ ρ.ker := by
    have hker := (Subgroup.map_eq_bot_iff (CFSG.Quasithin.kerIn M ⊤)).mp hmap
    rwa [QuotientGroup.ker_mk'] at hker
  exact le_antisymm hCK hle

theorem Setting12Two.trivial_on_chief (hMult : SchurMultiplierInput) (h : Setting12Two A M n)
    (ρ : G →* LGL 2 V) (hq : RepQuad ρ A) {W₁ W₂ : Submodule (ZMod 2) V}
    (hcf : IsChiefFactor ρ W₁ W₂) :
    ∀ x ∈ CFSG.Quasithin.kerIn M ⊤, ∀ w ∈ W₁, ρ x w - w ∈ W₂ := by
  classical
  intro x hx w hw
  by_cases hnc : IsNoncentral ρ W₁ W₂
  · haveI : Finite (SecMod W₁ W₂) :=
      Finite.of_surjective (Submodule.Quotient.mk (p := W₂.comap W₁.subtype))
        (Submodule.Quotient.mk_surjective (p := W₂.comap W₁.subtype))
    have hσker : (sectionRep ρ W₁ W₂ hcf.2.1 hcf.2.2.1).ker = CFSG.Quasithin.kerIn M ⊤ :=
      Setting12Two.ker_eq_of_irreducible hMult h (sectionRep ρ W₁ W₂ hcf.2.1 hcf.2.2.1)
        (repQuad_sectionRep ρ A hq W₁ W₂ hcf.2.1 hcf.2.2.1)
        (isChiefFactor_sectionRep ρ W₁ W₂ hcf)
        (isNoncentral_sectionRep ρ W₁ W₂ hcf hnc)
    have hxker : x ∈ (sectionRep ρ W₁ W₂ hcf.2.1 hcf.2.2.1).ker := by
      rw [hσker]; exact hx
    exact (mem_ker_sectionRep ρ W₁ W₂ hcf.2.1 hcf.2.2.1 x).1 hxker w hw
  · by_contra hcontra
    apply hnc
    unfold IsNoncentral
    exact ⟨x, w, hw, hcontra⟩

theorem Setting12Two.isPGroup_map_ker (hMult : SchurMultiplierInput) (h : Setting12Two A M n)
    (ρ : G →* LGL 2 V) (hq : RepQuad ρ A) :
    IsPGroup 2 ((CFSG.Quasithin.kerIn M ⊤).map ρ) :=
  isPGroup_map_of_trivial_on_chief ρ (CFSG.Quasithin.kerIn M ⊤)
    (fun W₁ W₂ hcf x hx w hw => Setting12Two.trivial_on_chief hMult h ρ hq hcf x hx w hw)

end CFSG.LocalAnalysis.WeakClosure81
