module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnStd

public section

namespace CFSG.Quasithin.H13.F431.Un.LL

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

section Map

variable {C C' : Type} [Group C] [Group C'] (ε : C ≃* C')

theorem lmap_mem_iff {H : Subgroup C} {x : C} : ε x ∈ H.map ε.toMonoidHom ↔ x ∈ H :=
  ⟨fun ⟨_, hy, e⟩ => ε.injective e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem lmap_centralizer (t : C) :
    (Subgroup.centralizer ({t} : Set C)).map ε.toMonoidHom =
      Subgroup.centralizer ({ε t} : Set C') := by
  ext y
  obtain ⟨x, rfl⟩ := ε.surjective y
  rw [lmap_mem_iff, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← map_mul, ← map_mul, ε.injective.eq_iff]

theorem lmap_isSylowTwoOf {X Y : Subgroup C} (h : IsSylowTwoOf X Y) :
    IsSylowTwoOf (X.map ε.toMonoidHom) (Y.map ε.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Subgroup.map_mono h1, h2.of_equiv (X.equivMapOfInjective _ ε.injective), ?_⟩
  have e : ((X.map ε.toMonoidHom).subgroupOf (Y.map ε.toMonoidHom)).index =
      (X.subgroupOf Y).index := Subgroup.relIndex_map_map_of_injective X Y ε.injective
  rwa [e]

def lmapAut (φ : MulAut C') : MulAut C := ε.trans (φ.trans ε.symm)

theorem lmapAut_apply (φ : MulAut C') (x : C) : ε (lmapAut ε φ x) = φ (ε x) := by
  simp [lmapAut]

theorem lmapAut_fix {φ : MulAut C'} {t : C} (hφ : φ (ε t) = ε t) : lmapAut ε φ t = t :=
  ε.injective (by rw [lmapAut_apply, hφ])

theorem lmap_coe (x : C) : ε.toMonoidHom x = ε x := rfl

theorem UnStdLoc.map {U : Subgroup C} {z t : C} {V Uc R K : Subgroup C}
    (h : UnStdLoc C U z t V Uc R K) :
    UnStdLoc C' (U.map ε.toMonoidHom) (ε z) (ε t) (V.map ε.toMonoidHom) (Uc.map ε.toMonoidHom)
      (R.map ε.toMonoidHom) (K.map ε.toMonoidHom) := by
  have hc := lmap_centralizer ε t
  have hinj := ε.injective
  refine
    { comm := by rw [← map_mul, ← map_mul, h.comm]
      sylow_t := ?_
      V_le := hc ▸ Subgroup.map_mono h.V_le
      V_aut := ?_
      V_ab := ?_
      V_sq := ?_
      z_V := ⟨z, h.z_V, rfl⟩
      U_le := Subgroup.map_mono h.U_le
      U_aut := ?_
      t_U := ⟨t, h.t_U, rfl⟩
      K_le := hc ▸ Subgroup.map_mono h.K_le
      K_perf := ?_
      V_K := Subgroup.map_mono h.V_K
      K_cent := ?_
      coset := ?_
      nonsolv := ?_
      R_le := Subgroup.map_mono h.R_le
      R_two := ?_
      R_cls := ?_
      R_U := ?_
      z_cent := ?_
      P_U := ?_ }
  · rw [← hc, ← Subgroup.map_inf U _ ε.toMonoidHom hinj]
    exact lmap_isSylowTwoOf ε h.sylow_t
  · rintro φ hφ _ ⟨v, hv, rfl⟩
    have := h.V_aut (lmapAut ε φ) (lmapAut_fix ε hφ) v hv
    change φ (ε v) ∈ _
    rw [← lmapAut_apply ε φ v]
    exact ⟨_, this, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.V_ab a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, h.V_sq a ha, map_one]
  · rintro φ hφ _ ⟨v, hv, rfl⟩
    have := h.U_aut (lmapAut ε φ) (lmapAut_fix ε hφ) v hv
    change φ (ε v) ∈ _
    rw [← lmapAut_apply ε φ v]
    exact ⟨_, this, rfl⟩
  · rw [← Subgroup.map_commutator, h.K_perf]
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, h.K_cent k hk u hu]
  · rintro _ ⟨v, hv, rfl⟩ hvU
    have hvU' : v ∉ Uc := fun hu => hvU ⟨v, hu, rfl⟩
    obtain ⟨x, hx, u, hu, e⟩ := h.coset v hv hvU'
    refine ⟨ε x, ?_, ε u, ⟨u, hu, rfl⟩, ?_⟩
    · rw [← hc]
      exact ⟨x, hx, rfl⟩
    · change ε v = _
      rw [e]
      simp only [map_mul, map_inv]
  · obtain ⟨L, hL, hns, hL'⟩ := h.nonsolv
    refine ⟨L.map ε.toMonoidHom, hc ▸ Subgroup.map_mono hL, ?_, ?_⟩
    · intro hsol
      exact hns (Group.isSolvable_of_isSolvable_injective
        (f := (L.equivMapOfInjective ε.toMonoidHom hinj).toMonoidHom)
        (L.equivMapOfInjective ε.toMonoidHom hinj).injective)
    · intro L' hL'le hcomm
      let L'' : Subgroup C := L'.comap ε.toMonoidHom
      have hL''L : L'' ≤ L := by
        intro x hx
        obtain ⟨y, hy, e⟩ := hL'le hx
        exact hinj e ▸ hy
      have hsol := hL' L'' hL''L fun x hx v hv => by
        have := hcomm (ε x) hx (ε v) ⟨v, hv, rfl⟩
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at this
        exact (lmap_mem_iff ε).1 this
      let φ : L' →* L'' :=
        { toFun := fun x => ⟨ε.symm (x : C'), by
            show ε (ε.symm (x : C')) ∈ L'
            rw [ε.apply_symm_apply]
            exact x.2⟩
          map_one' := Subtype.ext (map_one ε.symm)
          map_mul' := fun a b => Subtype.ext (map_mul ε.symm (a : C') (b : C')) }
      exact Group.isSolvable_of_isSolvable_injective (f := φ) (fun a b e =>
        Subtype.ext (ε.symm.injective (congrArg Subtype.val e)))
  · obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := h.R_two
    exact ⟨ε a, ⟨a, ha, rfl⟩, ε b, ⟨b, hb, rfl⟩, fun e => ha1 (hinj (by rw [e, map_one])),
      fun e => hb1 (hinj (by rw [e, map_one])), fun e => hab (hinj e)⟩
  · rintro _ ⟨r, hr, rfl⟩ hr1
    obtain ⟨x, hx, e⟩ := h.R_cls r hr fun e => hr1 (by rw [lmap_coe, e, map_one])
    refine ⟨ε x, ?_, ?_⟩
    · rw [← hc]
      exact ⟨x, hx, rfl⟩
    · change ε r = _
      rw [e]
      simp only [map_mul, map_inv]
  · rintro _ ⟨r, hr, rfl⟩ hrU
    rw [lmap_coe, h.R_U r hr ((lmap_mem_iff ε).1 hrU), map_one]
  · rintro _ ⟨y, hy, rfl⟩
    rw [lmap_coe, ← map_mul, ← map_mul, h.z_cent y hy]
  · rintro y ⟨⟨y0, hy0, rfl⟩, hyc⟩ _ ⟨u, hu, rfl⟩
    have hy0c : y0 ∈ Subgroup.centralizer ({t} : Set C) := by
      rw [← hc] at hyc
      exact (lmap_mem_iff ε).1 hyc
    rw [lmap_coe, lmap_coe, ← map_mul, ← map_mul, h.P_U y0 ⟨hy0, hy0c⟩ u hu]

end Map

end CFSG.Quasithin.H13.F431.Un.LL
