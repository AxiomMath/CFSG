module

public import CFSG.Quasithin.Vol2.Ch11SecAKE4
public import CFSG.Quasithin.H13.NQCatL2LieParabolic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.H13.NQCat

noncomputable def modO2PerfectCoreMap {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (P : Subgroup X) :
    ModO2 (perfectCore P) ≃* ModO2 (perfectCore (P.map e.toMonoidHom)) :=
  modO2Congr (((perfectCore P).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (CFSG.Quasithin.map_perfectCore _ P)))

theorem param_of_residual {X : Type} [Group X] [Finite X] {U : Subgroup X}
    {Pj : Fin 2 → Subgroup X} {R : ℕ → Prop} (hres : ResidualOvergroupsAt X U Pj)
    (hU : IsSylowTwoOf U ⊤) (hL : ∀ j, LeviParam R (Pj j)) {P : Subgroup X}
    (hP : IsMaxParabolic2 ⊤ P) {m : ℕ} (hm : IsPSL 2 2 m (ModO2 (perfectCore P))) : R m := by
  obtain ⟨⟨-, S, hS, hNP⟩, hPtop, -⟩ := hP
  have hSP : S ≤ P := fun x hx => hNP ⟨Subgroup.mem_top x, Subgroup.le_normalizer hx⟩
  have hpc : perfectCore P ≠ ⊥ := fun h => not_isPSL_modO2_bot h hm
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hS hU
  let φ : X ≃* X := MulAut.conj g
  have hUP : U ≤ P.map φ.toMonoidHom := hg ▸ Subgroup.map_mono hSP
  have hPtop' : P.map φ.toMonoidHom ≠ ⊤ := fun h => hPtop (by
    have h2 := congrArg (Subgroup.map φ.symm.toMonoidHom) h
    rwa [Vol2Native.A312L.map_map_symm, Subgroup.map_top_of_surjective _ φ.symm.surjective]
      at h2)
  have hns : ¬ Group.IsSolvable ↥(P.map φ.toMonoidHom) := by
    rw [isSolvable_iff_perfectCore_eq_bot, ← CFSG.Quasithin.map_perfectCore]
    exact fun h => hpc ((Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h)
  obtain ⟨j, -, hd⟩ := hres.2.2.2.2.1 _ hUP hPtop' hns
  have hpcj : perfectCore (P.map φ.toMonoidHom) = perfectCore (Pj j) := by
    rw [← Vol2Native.A312L.dInf_eq_perfectCore, ← Vol2Native.A312L.dInf_eq_perfectCore, hd]
  have e : ModO2 (perfectCore P) ≃* ModO2 (perfectCore (Pj j)) :=
    (modO2PerfectCoreMap φ P).trans (modO2Congr (MulEquiv.subgroupCongr hpcj))
  rcases hL j with h | ⟨T, _, _, _, hnab, hR, g', hg', hker⟩
  · exact absurd (IsPSL.of_mulEquiv e hm) (not_isPSL_modO2_bot h)
  · exact hR m (IsPSL.of_mulEquiv (e.trans (Vol2Native.A312L.modO2EquivOfHom hnab g' hg' hker))
      hm)

theorem isPSL_of_parConcl {X : Type} [Group X] [Finite X] {k : ℕ}
    (hpar : ∀ U : Subgroup X, IsSylowTwoOf U ⊤ → ParConcl X k U) {P : Subgroup X}
    (hP : IsMaxParabolic2 ⊤ P) : IsPSL 2 2 k (ModO2 (perfectCore P)) := by
  obtain ⟨⟨-, S, hS, hNP⟩, hPtop, hmax⟩ := hP
  obtain ⟨Pj, -, hcoat, hj, -⟩ := hpar S hS
  have hN : Subgroup.normalizer (S : Set X) ≤ P := fun x hx => hNP ⟨Subgroup.mem_top x, hx⟩
  obtain ⟨M, hM, hPM⟩ := (eq_top_or_exists_le_coatom P).resolve_left hPtop
  obtain ⟨j, rfl⟩ := (hcoat M (hN.trans hPM)).mp hM.covBy_top
  rw [← hmax (Pj j) ⟨le_top, S, hS, fun x hx => hPM (hN hx.2)⟩ hM.1 hPM]
  exact (hj j).2.2

theorem maxParabolic_map {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y)
    {P : Subgroup X} (hP : IsMaxParabolic2 ⊤ P) {m : ℕ}
    (hm : IsPSL 2 2 m (ModO2 (perfectCore P))) :
    IsMaxParabolic2 ⊤ (P.map e.toMonoidHom) ∧
      IsPSL 2 2 m (ModO2 (perfectCore (P.map e.toMonoidHom))) :=
  ⟨Vol2Native.A312L.isMaxParabolic2_top_map_equiv e hP,
    IsPSL.of_mulEquiv (modO2PerfectCoreMap e P) hm⟩

theorem maxParabolic_subgroupOf {Q : Type} [Group Q] [Finite Q] {L P : Subgroup Q}
    (hP : IsMaxParabolic2 L P) {m : ℕ} (hm : IsPSL 2 2 m (ModO2 (perfectCore P))) :
    IsMaxParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) ∧
      IsPSL 2 2 m (ModO2 (perfectCore (P.subgroupOf L))) := by
  obtain ⟨hpar, hne, hmax⟩ := hP
  have hPL : P ≤ L := hpar.1
  have hmap : ∀ Q' : Subgroup ↥L, (Q'.map L.subtype).subgroupOf L = Q' := fun Q' =>
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective Q'
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [A312.isParabolic2_top_iff, Subgroup.map_subgroupOf_eq_of_le hPL]
    exact hpar
  · intro htop
    apply hne
    have h := congrArg (Subgroup.map L.subtype) htop
    rwa [Subgroup.map_subgroupOf_eq_of_le hPL, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  · intro Q' hQ' hQ'top hPQ'
    have hQ : IsParabolic2 L (Q'.map L.subtype) := (A312.isParabolic2_top_iff L Q').mp hQ'
    have hQL : Q'.map L.subtype ≠ L := by
      intro h
      apply hQ'top
      rw [← hmap Q', h, Subgroup.subgroupOf_self]
    have hPQ : P ≤ Q'.map L.subtype := by
      have := Subgroup.map_mono (f := L.subtype) hPQ'
      rwa [Subgroup.map_subgroupOf_eq_of_le hPL] at this
    rw [← hmap Q', hmax _ hQ hQL hPQ]
  · refine IsPSL.of_mulEquiv (modO2Congr ?_) hm
    exact (((perfectCore (P.subgroupOf L)).equivMapOfInjective L.subtype
      L.subtype_injective).trans (MulEquiv.subgroupCongr (by
        rw [CFSG.Quasithin.map_perfectCore L.subtype (P.subgroupOf L),
          Subgroup.map_subgroupOf_eq_of_le hPL]))).symm

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
