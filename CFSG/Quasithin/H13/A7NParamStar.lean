module

public import CFSG.Quasithin.H13.A7NParam
public import CFSG.Quasithin.EmptyFaithful.E22QRes

public section

namespace CFSG.Quasithin.H13.A7NP

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem nParam_sup_le_one_alt7_noE {Y : Type} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hnab : ∃ a b : Y, a * b ≠ b * a)
    (hA : Nonempty (Y ≃* alternatingGroup (Fin 7))) (B : Subgroup (MulAut Y)) :
    E1.nParam ((MulAut.conj : Y →* MulAut Y).range ⊔ B) ≤ 1 := by
  obtain ⟨e7⟩ := hA
  rw [E1.nParam_subgroupOf]
  exact nParam_le_one_of_fStar_alt7 ⟨(Vol2.Ch11.SecB.generalizedFittingEquiv hnab B).trans e7⟩

variable {G : Type} [Group G] [Finite G]

private theorem star_pCoreOf_mulEquiv' {H K : Subgroup G} (hKc : K ∈ cComp H) :
    Nonempty (↥(E2.star (pCoreOf 2 H) H K) ≃* (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  set N := (kerIn (pCoreOf 2 H) H).subgroupOf H with hN
  let φ : ↥K →* E2.StarQuot (pCoreOf 2 H) H :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion hKH)
  have hrange : φ.range = E2.star (pCoreOf 2 H) H K := by
    unfold E2.star
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker = CFSG.pCore 2 ↥K := by
    apply le_antisymm
    ·
      have hkp : IsPGroup 2 φ.ker := by
        intro x
        have hx : (x : ↥K) ∈ φ.ker := x.2
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at hx
        have hxO : ((x : ↥K) : G) ∈ pCoreOf 2 H := by simpa using hx 1 H.one_mem
        obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨_, hxO⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        simpa using congrArg Subtype.val hk
      exact le_sSup ⟨inferInstance, hkp⟩
    ·
      intro x hx
      have hxG : (x : G) ∈ pCoreOf 2 K := by
        exact ⟨x, hx, rfl⟩
      have hxH : (x : G) ∈ pCoreOf 2 H :=
        A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc) hxG
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
      intro b hb
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hb) _).mp hxH
  have hnorm : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))).symm⟩

theorem nParam_le_one_of_alt7_noE {X K T : Subgroup G}
    (hTX : IsSylowTwoOf T X) (hKc : K ∈ cComp X) (hXK : X = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))) :
    E1.nParam X ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := pCoreOf 2 X with hM
  have hker : kerIn M X ≤ M := fun x hx => by simpa using hx 1 X.one_mem
  have hJs : Group.IsSolvable ↥(kerIn M X) := by
    have hp : IsPGroup 2 ↥(kerIn M X) := (pCoreOf_isPGroup 2 X).to_le hker
    have := hp.isNilpotent
    infer_instance
  obtain ⟨es⟩ := star_pCoreOf_mulEquiv' hKc
  obtain ⟨e7⟩ := hA
  have h7 : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hKs : IsSimpleGroup ↥(E2.star M X K) := @MulEquiv.isSimpleGroup _ _ _ _ h7 (es.trans e7)
  set P : Vol2.Ch11.SecB.GrpPred := fun (Q : Type) [Group Q] =>
    Nonempty (Q ≃* alternatingGroup (Fin 7)) with hPdef
  have hP : Vol2.Ch11.SecB.IsoInv P := by
    intro A B _ _ e h
    obtain ⟨e'⟩ := h
    exact ⟨e.trans e'⟩
  have h := E2.E22N.nParam_le_of_starC (Q := P) (C := E2.E22N.SolvSimpSolv) (n := 1) hP
    (fun Y _ _ hH hK hC => E2.E22N.e111ForQnC_sss hP le_rfl Y hH hK hC)
    hTX.1 hTX.2.1 hKc hXK hJs hKs ⟨es.trans e7⟩
    (fun Y _ _ _ hnab hY B _ _ => by
      obtain ⟨eY⟩ := hY
      simpa using nParam_sup_le_one_alt7_noE hnab ⟨(eY.trans es).trans e7⟩ B)
    hTX.1 (E2.E22N.solvSimpSolv_of_star hTX.1 hTX.2.1 hKc hXK hTK hJs hKs hTX.1)
  rw [sup_comm, C1Pack12.oTwoUpper_sup_eq_of_sylow hTX] at h
  simpa using h

end CFSG.Quasithin.H13.A7NP

end
