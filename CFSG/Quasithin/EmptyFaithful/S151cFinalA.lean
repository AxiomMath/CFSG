module

public import CFSG.Quasithin.EmptyFaithful.S151cFinalB
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S151cOneAux

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem descAt_of_genTop (h : quasithinQTFE14Cat G T Mc) (hM : InM T M)
    (hVe : IsElemAbelian 2 (VZ T M))
    (hgen : GenTop (Jhat (autI hVe M)) (autI hVe T)) : DescAt T M (VZ T M) := by
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_VZ T M
  unfold DescAt
  rw [JhatOn_eq_Jhat_autI M hVe]
  set K := preOn M (VZ T M) (Jhat (autI hVe M)) with hK
  set C := conjClosure (quasithinOmegaOneCenter T ⊓ VZ T M) K with hC
  have hCV : C ≤ VZ T M := by
    refine conjClosure_le fun k hk z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp (hMN (preOn_le _ _ _ hk)) z).mp hz.2
  refine le_antisymm ?_ hCV
  set B : Subgroup (IntMod (VZ T M) hVe) := C.subgroupOf (VZ T M) with hB
  have hgenB : Subgroup.closure
      {x | ∃ ψ ∈ Jhat (autI hVe M), ∃ z ∈ fixV (autI hVe T), ψ z = x} ≤ B := by
    rw [Subgroup.closure_le]
    rintro _ ⟨ψ, hψ, z, hz, rfl⟩
    obtain ⟨m, hm, rfl⟩ := (mem_autI hVe).1 (Jhat_le _ hψ)
    have hmK : (m : G) ∈ K := by
      refine mem_preOn.mpr ⟨hm, m.2, ?_⟩
      exact hψ
    have hzZ : z.val ∈ quasithinOmegaOneCenter T ⊓ VZ T M :=
      ⟨mem_omegaOneCenter_of_fixV h hM hVe hz, z.val_mem⟩
    show (convI hVe m z).val ∈ C
    rw [convI_apply_val]
    exact mem_conjClosure hmK hzZ
  intro v hv
  have h1 : IntMod.mk hVe ⟨v, hv⟩ ∈ B := hgenB (by rw [show Subgroup.closure
      {x | ∃ ψ ∈ Jhat (autI hVe M), ∃ z ∈ fixV (autI hVe T), ψ z = x} = ⊤ from hgen]; trivial)
  exact h1

omit [Finite G] in
theorem commutator_preOn_eq_map_commV (hVe : IsElemAbelian 2 (VZ T M))
    {A : Subgroup (MulAut (IntMod (VZ T M) hVe))} (hA : A ≤ autI hVe M) :
    ⁅VZ T M, preOn M (VZ T M) A⁆ = (commV A).map (S1417.inclMod hVe) := by
  have hN : preOn M (VZ T M) A ≤ Subgroup.normalizer (VZ T M : Set G) := by
    intro x hx
    obtain ⟨-, hxN, -⟩ := mem_preOn.mp hx
    exact hxN
  rw [S1417.commutator_eq_map_commV hVe hN]
  have : autI hVe (preOn M (VZ T M) A) = A := autOn_preOn hA
  rw [this]

omit [Finite G] in
theorem mem_preOn_convI {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {A : Subgroup (MulAut (IntMod V hV))} {x : G} :
    x ∈ preOn M V A ↔
      x ∈ M ∧ ∃ hx : x ∈ Subgroup.normalizer (V : Set G), convI hV ⟨x, hx⟩ ∈ A :=
  mem_preOn

theorem case1517Six_of_aCase6 (hM : InM T M) (hVe : IsElemAbelian 2 (VZ T M)) {p : ℕ}
    (h6 : ACase6 (autI hVe T) (Jhat (autI hVe M)) p) :
    Case1517Six T M (VZ T M) (Jhat (autI hVe M)) p := by
  obtain ⟨hcard, A₁, A₂, hdir, hA₁, hA₂, ⟨t, htT, hconj⟩, hinf, hsup⟩ := h6
  have hle : A₁ ⊔ A₂ ≤ autI hVe M := hdir.1.symm.le.trans (Jhat_le _)
  have hA₁le : A₁ ≤ autI hVe M := le_sup_left.trans hle
  have hA₂le : A₂ ≤ autI hVe M := le_sup_right.trans hle
  refine ⟨hcard, A₁, A₂, hdir, hA₁, hA₂, ?_, ?_⟩
  · obtain ⟨g, hgT, rfl⟩ := (mem_autI hVe).1 htT
    refine ⟨(g : G), hgT, ?_⟩
    have hgM : (g : G) ∈ M := hM.2 hgT
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨hmM, hmN, hmA⟩ := (mem_preOn_convI hVe).mp hm
      have hN' : (g : G) * m * (g : G)⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hmN) (Subgroup.inv_mem _ g.2)
      refine (mem_preOn_convI hVe).mpr ⟨?_, hN', ?_⟩
      · exact M.mul_mem (M.mul_mem hgM hmM) (M.inv_mem hgM)
      · show convI hVe ⟨(g : G) * m * (g : G)⁻¹, hN'⟩ ∈ A₂
        have e : convI hVe ⟨(g : G) * m * (g : G)⁻¹, hN'⟩ =
            convI hVe g * convI hVe ⟨m, hmN⟩ * (convI hVe g)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e, ← hconj, mem_conjBy_iff]
        have e2 : (convI hVe g)⁻¹ * (convI hVe g * convI hVe ⟨m, hmN⟩ * (convI hVe g)⁻¹) *
            convI hVe g = convI hVe ⟨m, hmN⟩ := by group
        rw [e2]
        exact hmA
    · intro hx
      obtain ⟨hxM, hxN, hxA⟩ := (mem_preOn_convI hVe).mp hx
      have hmN : (g : G)⁻¹ * x * (g : G) ∈ Subgroup.normalizer (VZ T M : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ g.2) hxN) g.2
      refine ⟨(g : G)⁻¹ * x * (g : G), (mem_preOn_convI hVe).mpr ⟨?_, hmN, ?_⟩, ?_⟩
      · exact M.mul_mem (M.mul_mem (M.inv_mem hgM) hxM) hgM
      · have e : convI hVe ⟨(g : G)⁻¹ * x * (g : G), hmN⟩ =
            (convI hVe g)⁻¹ * convI hVe ⟨x, hxN⟩ * convI hVe g := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e]
        rw [← hconj, mem_conjBy_iff] at hxA
        exact hxA
      · show (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x
        group
  · unfold IsDirectSumOfCommutators
    rw [commutator_preOn_eq_map_commV hVe hA₁le, commutator_preOn_eq_map_commV hVe hA₂le]
    constructor
    · rw [← Subgroup.map_inf _ _ _ (S1417.inclMod_injective hVe), hinf, Subgroup.map_bot]
    · rw [← Subgroup.map_sup, hsup, S1417.map_inclMod_top]

theorem lemma1517Cases_of (hM : InM T M) (hVe : IsElemAbelian 2 (VZ T M))
    (hc : Cases7Aut (autI hVe M) (autI hVe T) (Jhat (autI hVe M))) :
    Lemma1517Cases T M (VZ T M) (JhatOn M (VZ T M)) := by
  rw [JhatOn_eq_Jhat_autI M hVe]
  rcases hc with h1 | h2 | h3 | h4 | h5 | ⟨p, hp, h6⟩ | h7
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl ⟨h3.1, h3.2.1, hVe, h3.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨p, hp, case1517Six_of_aCase6 hM hVe h6⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h7)))))

theorem facts_of_caseI (h : quasithinQTFE14Cat G T Mc) (hM : InM T M)
    (hVe : IsElemAbelian 2 (VZ T M))
    (hI : CaseI151c (autI hVe M) (autI hVe T) (Jhat (autI hVe M))) :
    DescAt T M (VZ T M) ∧ IsTwoNilpotentOn M (VZ T M) ∧ Lemma1517ConclAt T M (VZ T M) ∧
      Lemma1518ConclAt M (VZ T M) := by
  refine ⟨descAt_of_genTop h hM hVe hI.genTop, hI.twoNilp, ⟨lemma1517Cases_of hM hVe hI.cases,
    fun hlt => absurd hlt (lt_irrefl _)⟩, ?_⟩
  unfold Lemma1518ConclAt
  rw [qhatOn_eq hVe, qOn_eq hVe, JhatOn_eq_Jhat_autI M hVe]
  rcases hI.qdata with ⟨hq1, hq2⟩ | ⟨h3, hq1, hq2⟩
  · refine Or.inl ⟨?_, ?_⟩
    · exact hq1.trans (by norm_num)
    · exact hq2.trans (by norm_num)
  · refine Or.inr ⟨⟨h3.1, h3.2.1, hVe, h3.2.2⟩, hq1, hq2.trans (by norm_num)⟩

end CFSG.Quasithin
