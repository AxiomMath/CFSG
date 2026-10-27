module

public import CFSG.Quasithin.Background.G11Bridge
public import CFSG.Quasithin.Background.G6SQTK

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

theorem assemblyPRank_top_eq (S : Type) [Group S] [Finite S] (p : ℕ) :
    CFSG.Assembly.pRank p (⊤ : Subgroup S) = CFSG.pRank p S := by
  unfold CFSG.Assembly.pRank CFSG.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, -, ⟨hc, hp⟩, hk⟩
    exact ⟨E, { toIsMulCommutative := hc
                exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2
                  fun x => Subtype.ext (hp x x.2) }, hk⟩
  · rintro ⟨E, hE, hk⟩
    exact ⟨E, le_top, ⟨hE.toIsMulCommutative, fun x hx =>
      CFSG.elemPow_eq_one_of_isElementaryAbelian x hx⟩, hk⟩

theorem isStronglyQuasithin_of_tc {S : Type} [Group S] [Finite S]
    (h : CFSG.Open.SQTKTauCeti.StronglyQuasithin S) : CFSG.IsStronglyQuasithin S := by
  intro p hp hp2
  rw [← assemblyPRank_top_eq]
  exact h p hp hp2

theorem tc_of_isStronglyQuasithin {S : Type} [Group S] [Finite S]
    (h : CFSG.IsStronglyQuasithin S) : CFSG.Open.SQTKTauCeti.StronglyQuasithin S := by
  intro p hp hp2
  rw [assemblyPRank_top_eq]
  exact h p hp hp2

end G11

theorem IsQuotientOfSQTKTauCeti.of_surjective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (h : IsQuotientOfSQTKTauCeti X) : IsQuotientOfSQTKTauCeti Y := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := h
  exact ⟨S, inferInstance, inferInstance, hst, hkg, f.comp φ, hf.comp hφ⟩

theorem IsQuotientOfSQTKTauCeti.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsQuotientOfSQTKTauCeti X) : IsQuotientOfSQTKTauCeti Y :=
  h.of_surjective e.toMonoidHom e.surjective

theorem IsQuotientOfSQTKTauCeti.of_le {G : Type*} [Group G] {K X : Subgroup G} (hKX : K ≤ X)
    (h : IsQuotientOfSQTKTauCeti ↥X) : IsQuotientOfSQTKTauCeti ↥K := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := h
  let S' : Subgroup S := (K.subgroupOf X).comap φ
  let ψ : S' →* K :=
    { toFun := fun s => ⟨((φ s : X) : G), Subgroup.mem_subgroupOf.1 s.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hψ : Function.Surjective ψ := by
    intro k
    obtain ⟨s, hs⟩ := hφ ⟨(k : G), hKX k.2⟩
    exact ⟨⟨s, Subgroup.mem_subgroupOf.2 (by rw [hs]; exact k.2)⟩, Subtype.ext (by simp [ψ, hs])⟩
  refine ⟨S', inferInstance, inferInstance, ?_, hkg.subgroup S', ψ, hψ⟩
  intro p hp hp2
  rw [G11.assemblyPRank_top_eq]
  exact (G6.pRank_subgroup_le S' hp).trans (G11.isStronglyQuasithin_of_tc hst p hp hp2)

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem isQuotientOfSQTKTauCeti_toMulSub_iff (K : Subgroup (GLV V)) :
    IsQuotientOfSQTKTauCeti ↥(toMulSub K) ↔ IsQuotientOfSQTKTauCeti ↥K :=
  ⟨fun h => h.of_mulEquiv (toMulSubEquiv K).symm, fun h => h.of_mulEquiv (toMulSubEquiv K)⟩

end G11

end CFSG.Quasithin
