module

public import CFSG.Quasithin.H13.NQCatA314Gen
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSuzuki
public import CFSG.Quasithin.Recognition.Stroth.BenderCaseIIFacts
public import CFSG.Quasithin.Recognition.Stroth.BenderJn
public import CFSG.Quasithin.Vol2.Ch3zSetup
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DSSz

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.QuasithinUnique
open CFSG.ShultStronglyClosedTI.SuzukiLayerKernel
open CFSG.QuasithinUnique.Setup.X7
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem isElemAbelian_chiefMod_bot {W : Subgroup G} (hW : IsElemAbelian 2 W) :
    IsElemAbelian 2 (Ch3z.chiefMod ⊥ W) := by
  refine ⟨IsMulCommutative.of_comm (fun x y => ?_), fun x hx => ?_⟩
  · obtain ⟨u, hu⟩ := Ch3z.chiefIota_surjective (D14.le_normalizer_bot W) x
    obtain ⟨v, hv⟩ := Ch3z.chiefIota_surjective (D14.le_normalizer_bot W) y
    rw [← hu, ← hv, ← map_mul, ← map_mul, hW.1.is_comm.comm u v]
  · obtain ⟨u, hu⟩ := Ch3z.chiefIota_surjective (D14.le_normalizer_bot W) ⟨x, hx⟩
    have hu2 : u ^ 2 = 1 := Subtype.ext (by simpa using hW.2 (u : G) u.2)
    have h2 : ((⟨x, hx⟩ : ↥(Ch3z.chiefMod ⊥ W)) ^ 2) = 1 := by
      rw [← hu, ← map_pow, hu2, map_one]
    simpa using congrArg Subtype.val h2

abbrev szSbar (L1 L2 S : Subgroup G) : Subgroup (oTwoQuot ↥(L1 ⊔ S)) :=
  (S.subgroupOf (L1 ⊔ S)).map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)))

abbrev szX0bar (X0 : Subgroup G) (L1 L2 S : Subgroup G) : Subgroup (oTwoQuot ↥(L1 ⊔ S)) :=
  (X0.subgroupOf (L1 ⊔ S)).map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)))

theorem exists_equiv_z1_sylow
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S) :
    ∃ (X0 : Subgroup G) (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K),
      (∀ t : G, t ∈ X0 ↔ t ∈ S ∧ t ^ 2 ∈ Q1 L1 L2 S) ∧
      (X0 ≤ S) ∧ (Q1 L1 L2 S ≤ X0) ∧
      (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K ∧
      (szX0bar X0 L1 L2 S).map e.toMonoidHom = suzukiZ0 a K := by
  classical
  obtain ⟨eSz⟩ := hSz
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, ⟨eSz⟩⟩)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hSyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hszU3 : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ (2 * a + 1)) :=
    Or.inl ⟨a, ha, rfl, ⟨(oTwoQuotCongr (MulEquiv.subgroupCongr hsup1)).trans
      ((oTwoQuotSupEquiv hF.1).trans eSz)⟩⟩
  obtain ⟨X0, hX0mem, hQ1X0, -, -⟩ := exists_X0 (q := 2 ^ (2 * a + 1)) hszU3 hSyl1
  have hX0S : X0 ≤ S := fun t ht => ((hX0mem t).mp ht).1
  have hX0mem' : ∀ t, t ∈ X0 ↔ t ∈ S ∧ t ^ 2 ∈ Q1 L1 L2 S := by
    intro t
    rw [hX0mem t, hpCore1]
  have e0 : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K :=
    (oTwoQuotCongr (MulEquiv.subgroupCongr hsup1)).trans
      ((oTwoQuotSupEquiv hF.1).trans (eSz.trans (suzukiGroupEquivSz a K hK).symm))
  have hSylTop : IsSylowTwoOf (S.subgroupOf (L1 ⊔ S)) ⊤ :=
    CFSG.Quasithin.H13.NQCat.A314D.isSylowTwoOf_top_subgroupOf hSyl1
  have hP : IsSylowTwoOf ((szSbar L1 L2 S).map e0.toMonoidHom) ⊤ := by
    have h := CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hSylTop
      (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) (QuotientGroup.mk'_surjective _)
    exact CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective h
      e0.toMonoidHom e0.surjective
  have hU : IsSylowTwoOf (suzukiU a K) ⊤ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.suzukiU_isSylowTwoOf hK
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hP hU
  let e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a K := e0.trans (MulAut.conj g)
  have hSmap : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a K := by
    have hmap : (szSbar L1 L2 S).map e.toMonoidHom =
        ((szSbar L1 L2 S).map e0.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [show e.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e0.toMonoidHom from rfl,
        ← Subgroup.map_map]
    rw [hmap, hg]
    rfl
  have hX0char : ∀ x : oTwoQuot ↥(L1 ⊔ S),
      x ∈ szX0bar X0 L1 L2 S ↔ x ∈ szSbar L1 L2 S ∧ x * x = 1 := by
    intro x
    constructor
    · intro hx
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
      have htX : (t : G) ∈ X0 := Subgroup.mem_subgroupOf.mp ht
      obtain ⟨htS, ht2⟩ := (hX0mem' (t : G)).mp htX
      have htbar : QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)) t ∈ szSbar L1 L2 S :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htS)
      refine ⟨htbar, ?_⟩
      change QuotientGroup.mk (t * t) = 1
      have hmemG : ((t * t : ↥(L1 ⊔ S)) : G) ∈ pCoreOf 2 (L1 ⊔ S) := by
        rw [hpCore1]
        simpa [pow_two] using ht2
      have hmem : t * t ∈ pCore 2 (↥(L1 ⊔ S)) :=
        (F1.mem_pCore_iff_coe (t * t)).mpr hmemG
      exact (QuotientGroup.eq_one_iff (N := pCore 2 ↥(L1 ⊔ S))
        (x := t * t)).mpr hmem
    · rintro ⟨hxS, hx2⟩
      obtain ⟨t, htS, rfl⟩ := Subgroup.mem_map.mp hxS
      have htS' : (t : G) ∈ S := Subgroup.mem_subgroupOf.mp htS
      have ht2 : (t : G) ^ 2 ∈ Q1 L1 L2 S := by
        have hq : QuotientGroup.mk (t * t : ↥(L1 ⊔ S)) = 1 := hx2
        have hmem : t * t ∈ pCore 2 (↥(L1 ⊔ S)) :=
          (QuotientGroup.eq_one_iff (N := pCore 2 ↥(L1 ⊔ S))
            (x := t * t)).mp hq
        have h' : ((t * t : ↥(L1 ⊔ S)) : G) ∈ pCoreOf 2 (L1 ⊔ S) :=
          (F1.mem_pCore_iff_coe (t * t)).mp hmem
        rw [hpCore1] at h'
        simpa [pow_two] using h'
      exact Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr ((hX0mem' (t : G)).2 ⟨htS', ht2⟩))
  have hX0map : (szX0bar X0 L1 L2 S).map e.toMonoidHom = suzukiZ0 a K := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxS, hx2⟩ := (hX0char x).1 hx
      have hyU : e x ∈ suzukiU a K := by
        rw [← hSmap]
        exact Subgroup.mem_map_of_mem e.toMonoidHom hxS
      refine (mem_suzukiZ0_iff_sq_eq_one hK).2 ⟨hyU, ?_⟩
      rw [pow_two, ← map_mul, hx2, map_one]
    · intro hy
      obtain ⟨hyU, hy2⟩ := (mem_suzukiZ0_iff_sq_eq_one hK).1 hy
      have hyS : e.symm y ∈ szSbar L1 L2 S := by
        have hyU' : y ∈ (szSbar L1 L2 S).map e.toMonoidHom := by rwa [hSmap]
        obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hyU'
        have hx' : x = e.symm y := by
          rw [← hxy]
          simp
        rwa [hx'] at hx
      have hsq : e.symm y * e.symm y = 1 := by
        apply e.injective
        rw [map_mul, map_one, MulEquiv.apply_symm_apply]
        simpa [pow_two] using hy2
      exact ⟨e.symm y, (hX0char _).2 ⟨hyS, hsq⟩, by simp⟩
  have hQ1X0' : Q1 L1 L2 S ≤ X0 := by rwa [← hpCore1]
  exact ⟨X0, e, hX0mem', hX0S, hQ1X0', hSmap, hX0map⟩


end CFSG.Quasithin.Stroth

end
