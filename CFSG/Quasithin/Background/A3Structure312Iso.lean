
module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank

variable {X Y : Type} [Group X] [Group Y]

theorem IsAlt.of_mulEquiv {n : ℕ} (e : X ≃* Y) (h : IsAlt n X) : IsAlt n Y :=
  h.elim fun f => ⟨e.symm.trans f⟩

theorem IsSporadic.of_mulEquiv {s : TauCeti.SporadicName} (e : X ≃* Y) (h : IsSporadic s X) :
    IsSporadic s Y :=
  h.elim fun f => ⟨e.symm.trans f⟩

theorem IsPSL.of_mulEquiv {n p f : ℕ} (e : X ≃* Y) (h : IsPSL n p f X) : IsPSL n p f Y :=
  statedClassicalModel_of_mulEquiv e.symm h

theorem IsPSU.of_mulEquiv {n p f : ℕ} (e : X ≃* Y) (h : IsPSU n p f X) : IsPSU n p f Y :=
  statedClassicalModel_of_mulEquiv e.symm h

theorem IsPSLEps3.of_mulEquiv {s : Bool} {p f : ℕ} (e : X ≃* Y) (h : IsPSLEps3 s p f X) :
    IsPSLEps3 s p f Y := by
  cases s
  · exact IsPSU.of_mulEquiv e h
  · exact IsPSL.of_mulEquiv e h

theorem IsPSp4.of_mulEquiv {p f : ℕ} (e : X ≃* Y) (h : IsPSp4 p f X) : IsPSp4 p f Y :=
  statedClassicalModel_of_mulEquiv e.symm h

theorem IsG2.of_mulEquiv {p f : ℕ} (e : X ≃* Y) (h : IsG2 p f X) : IsG2 p f Y :=
  chevalleyExceptionalModel_of_mulEquiv e.symm h

theorem Is3D4.of_mulEquiv {p f : ℕ} (e : X ≃* Y) (h : Is3D4 p f X) : Is3D4 p f Y :=
  chevalleyExceptionalModel_of_mulEquiv e.symm h

theorem Is2F4.of_mulEquiv {f : ℕ} (e : X ≃* Y) (h : Is2F4 f X) : Is2F4 f Y :=
  reeTitsModel_of_mulEquiv e.symm h

theorem IsTits.of_mulEquiv (e : X ≃* Y) (h : IsTits X) : IsTits Y :=
  reeTitsModel_of_mulEquiv e.symm h

theorem IsSz.of_mulEquiv {f : ℕ} (e : X ≃* Y) (h : IsSz f X) : IsSz f Y :=
  suzukiModel_of_mulEquiv e.symm h

theorem IsSL3.of_mulEquiv {q : ℕ} (e : X ≃* Y) (h : IsSL3 q X) : IsSL3 q Y := by
  obtain ⟨K, _, _, hK, ⟨f⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.symm.trans f⟩⟩

theorem IsSU3.of_mulEquiv {q : ℕ} (e : X ≃* Y) (h : IsSU3 q X) : IsSU3 q Y := by
  obtain ⟨K, _, _, hK, ⟨f⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.symm.trans f⟩⟩

theorem IsSLEps3.of_mulEquiv {s : Bool} {q : ℕ} (e : X ≃* Y) (h : IsSLEps3 s q X) :
    IsSLEps3 s q Y := by
  cases s
  · exact IsSU3.of_mulEquiv e h
  · exact IsSL3.of_mulEquiv e h

theorem IsSL2.of_mulEquiv {p : ℕ} (e : X ≃* Y) (h : IsSL2 p X) : IsSL2 p Y :=
  h.elim fun f => ⟨e.symm.trans f⟩

theorem IsHomocyclicRank2.of_mulEquiv {p : ℕ} (e : X ≃* Y) (h : IsHomocyclicRank2 p X) :
    IsHomocyclicRank2 p Y := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  exact ⟨n, hn, ⟨e.symm.trans f⟩⟩

theorem IsHat.of_mulEquiv {S : Type} [Group S] (e : X ≃* Y) (h : IsHat X S) : IsHat Y S := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  have hcen : (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y := Subgroup.map_center_eq e
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_,
    ⟨(QuotientGroup.congr _ _ e hcen).symm.trans f⟩⟩
  rw [← hcen, Subgroup.card_map_of_injective e.injective, hc]

theorem IsE2.of_mulEquiv {n : ℕ} (e : X ≃* Y) (h : IsE2 n X) : IsE2 n Y :=
  h.elim fun f => ⟨e.symm.trans f⟩

theorem IsElemAbelianOfRank.of_mulEquiv {p n : ℕ} (e : X ≃* Y) (h : IsElemAbelianOfRank p n X) :
    IsElemAbelianOfRank p n Y :=
  h.elim fun f => ⟨e.symm.trans f⟩

theorem isElementaryAbelian_of_mulEquiv' {p : ℕ} (e : X ≃* Y) (h : CFSG.IsElementaryAbelian p X) :
    CFSG.IsElementaryAbelian p Y := by
  have hpow : ∀ x : X, x ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p p X)
  have hcomm : IsMulCommutative X := h.toIsMulCommutative
  refine
    { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
      exponent_dvd_p := ?_ }
  · obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, hcomm.is_comm.comm a b]
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_pow, hpow x, map_one]

theorem IsExtraspecial2.of_mulEquiv {m : ℕ} (e : X ≃* Y) (h : IsExtraspecial2 m X) :
    IsExtraspecial2 m Y := by
  obtain ⟨hX, hc⟩ := h
  have hcen : (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y := Subgroup.map_center_eq e
  let e' : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y := QuotientGroup.congr _ _ e hcen
  refine ⟨?_, by rw [← Nat.card_congr e.toEquiv, hc]⟩
  refine
    { center_order_p := ?_
      quotient_elementary_abelian := ?_
      quotient_nontrivial := ?_ }
  · rw [← hcen, Subgroup.card_map_of_injective e.injective]
    exact hX.center_order_p
  · exact isElementaryAbelian_of_mulEquiv' e' (hX.quotient_elementary_abelian)
  · have := hX.quotient_nontrivial
    exact e'.toEquiv.symm.nontrivial

theorem IsZ4StarExtra2.of_mulEquiv (e : X ≃* Y) (h : IsZ4StarExtra2 X) : IsZ4StarExtra2 Y := by
  obtain ⟨Z, E, hZ, hZc, hE, hZX, hZE, hI⟩ := h
  refine ⟨Z.map (e : X →* Y), E.map (e : X →* Y), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hZ]
  · have := hZc
    exact isCyclic_of_surjective (Z.equivMapOfInjective (e : X →* Y) e.injective).toMonoidHom
      (Z.equivMapOfInjective (e : X →* Y) e.injective).surjective
  · exact IsExtraspecial2.of_mulEquiv (E.equivMapOfInjective (e : X →* Y) e.injective) hE
  · rw [← Subgroup.map_center_eq e]
    exact Subgroup.map_mono hZX
  · rw [← Subgroup.map_sup, hZE, Subgroup.map_top_of_surjective _ e.surjective]
  · rw [← Subgroup.map_inf_eq _ _ _ e.injective, Subgroup.card_map_of_injective e.injective, hI]

end CFSG.Quasithin
