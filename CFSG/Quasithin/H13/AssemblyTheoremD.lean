module

public import CFSG.Quasithin.H13.AssemblyLocal
public import CFSG.Quasithin.SteinbergBKPerfectPrimeKernelSurjection
public import CFSG.Quasithin.SteinbergBMAlternatingFiveProperSolvable
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem alternatingGroup_five_nonabelian : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 2 3, ?_⟩, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    rfl
  · intro h
    have := congrArg (fun x : alternatingGroup (Fin 5) => (x : Equiv.Perm (Fin 5)) 0) h
    simp at this
    revert this
    decide

theorem perfect_subgroup_A5_quotient {E : Type*} [Group E] [Finite E]
    (hE : Nonempty (E ⧸ CFSG.pCore 2 E ≃* alternatingGroup (Fin 5))) {K : Subgroup E}
    (hK1 : K ≠ ⊥) (hKperf : Group.IsPerfect K) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := hE
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup (E ⧸ CFSG.pCore 2 E) := e.isSimpleGroup
  have hnab : ∃ a b : E ⧸ CFSG.pCore 2 E, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alternatingGroup_five_nonabelian
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hsolv : ∀ H : Subgroup (E ⧸ CFSG.pCore 2 E), H ≠ ⊤ → Group.IsSolvable H := by
    intro H hH
    have hlt : H.map e.toMonoidHom < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hH ?_
      rw [← Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective, ← htop,
        Subgroup.map_map]
      convert (Subgroup.map_id H).symm
      ext x
      simp
    have := SteinbergBM.alternating_five_proper_subgroup_solvable (by simp) hlt
    exact Group.isSolvable_of_isSolvable_injective (f := (H.equivMapOfInjective e.toMonoidHom
      e.injective).toMonoidHom) (H.equivMapOfInjective e.toMonoidHom e.injective).injective
  obtain ⟨-, -, e', -⟩ := SteinbergBK.perfect_subgroup_prime_kernel_surjection Nat.prime_two
    (CFSG.pCore 2 E) CFSG.pCore_isPGroup hsimple hnab hsolv K hK1 hKperf
  exact ⟨e'.trans e⟩

theorem nonempty_quotient_pCore_subgroupOf {G : Type*} [Group G] {K I : Subgroup G} (hKI : K ≤ I)
    {H : Type*} [Group H] (h : Nonempty (↥(K.subgroupOf I) ⧸ CFSG.pCore 2 ↥(K.subgroupOf I) ≃* H)) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* H) := by
  obtain ⟨f⟩ := h
  let e : ↥(K.subgroupOf I) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKI
  exact ⟨(QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)).symm.trans f⟩

variable {G : Type} [Group G] [Finite G]

theorem preferred_maximal_faithful_local_exists (hD : LocalDoubleEmbeddingExclusion)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G)
    {T : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hne : ∃ L : Subgroup G, quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L) :
    ∃ L : Subgroup G, (quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L) ∧
      (quasithinO2QuotientIso L (alternatingGroup (Fin 5)) →
        ∀ K : Subgroup G, quasithinIsFaithfulLocal T K →
          quasithinO2QuotientIso K (alternatingGroup (Fin 5))) := by
  by_cases h : ∃ L : Subgroup G, (quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L) ∧
      ¬ quasithinO2QuotientIso L (alternatingGroup (Fin 5))
  · obtain ⟨L, hL, hA⟩ := h
    exact ⟨L, hL, fun h' => absurd h' hA⟩
  · simp only [not_exists, not_and, not_not] at h
    obtain ⟨L, hL⟩ := hne
    refine ⟨L, hL, fun _ K hK => ?_⟩
    obtain ⟨I, hI, hKI⟩ := faithful_maximal_local_exists hD hs hnab hQ hT hK
    have hIA := (quasithinO2QuotientIso_iff I _).1 (h I hI)
    have hK1 : K.subgroupOf I ≠ ⊥ := by
      intro hb
      rw [Subgroup.subgroupOf_eq_bot] at hb
      exact hK.1.2.1.1 (hb.eq_bot_of_le hKI)
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK.1.2.1.2.1
    have hKp : Group.IsPerfect ↥(K.subgroupOf I) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKI).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKI).symm.surjective
    exact (quasithinO2QuotientIso_iff K _).2
      (nonempty_quotient_pCore_subgroupOf hKI (perfect_subgroup_A5_quotient hIA hK1 hKp))

theorem catalog_of_qt13Excluded {X : Type} [Group X] (h : QT13Excluded X) : Catalog X := by
  rcases h with ⟨t, n, f, -, -, h⟩ | (h | h) | h | (h | h | h | h | h)
  · exact lieModel_catalog X _ _ _ _ h
  · exact lieModel_catalog X _ _ _ _ h
  · exact lieModel_catalog X _ _ _ _ h
  · exact Or.inr (Or.inl ⟨9, by norm_num, h⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.M22, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.M23, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.M24, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.He, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.J4, h⟩)))

theorem excluded_or_preferred_local (hD : LocalDoubleEmbeddingExclusion) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hQ : quasithinIsQTKECat G) {T : Subgroup G}
    (hT : quasithinIsSylowTwo T)
    (hne : ∃ L : Subgroup G, quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L) :
    Catalog G ∨ ∃ L : Subgroup G,
      (quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L) ∧ QTH13 G T L := by
  by_cases hx : QT13Excluded G
  · exact Or.inl (catalog_of_qt13Excluded hx)
  · obtain ⟨L, hL, ha5⟩ := preferred_maximal_faithful_local_exists hD hs hnab hQ hT hne
    exact Or.inr ⟨L, hL, ⟨hs, hnab, hQ, hT, hL.2, hx, ha5⟩⟩

end CFSG.Quasithin.H13
