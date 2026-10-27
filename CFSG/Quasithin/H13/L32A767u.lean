module

public import CFSG.Quasithin.H13.L32A767t

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem sl2_exists_three :
    ∃ a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), a ^ 3 = 1 ∧ a ≠ 1 := by
  decide +kernel

theorem sl2_three_eq : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), a ^ 3 = 1 → a ≠ 1 →
    b ^ 3 = 1 → b ≠ 1 → b = a ∨ b = a⁻¹ := by
  decide +kernel

omit [Finite G] in
theorem exists_three_of_actsAsNaturalL2 {W : Type*} [CommGroup W] {Lw : Subgroup (MulAut W)}
    {U : Subgroup W} (h : ActsAsNaturalL2 Lw U) :
    ∃ c ∈ Lw, c ^ 3 = 1 ∧ c ≠ 1 ∧ ∀ d ∈ Lw, d ^ 3 = 1 → d ≠ 1 → d = c ∨ d = c⁻¹ := by
  obtain ⟨e, -, -⟩ := h
  obtain ⟨a, ha3, ha1⟩ := sl2_exists_three
  refine ⟨(e.symm a : ↥Lw), (e.symm a).2, ?_, ?_, fun d hd hd3 hd1 => ?_⟩
  · have : e.symm a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    simpa using congrArg Subtype.val this
  · intro h1
    apply ha1
    rw [← e.apply_symm_apply a, show e.symm a = 1 from Subtype.ext h1, map_one]
  · have hd3' : (⟨d, hd⟩ : ↥Lw) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    have hd1' : (⟨d, hd⟩ : ↥Lw) ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
    have h1 : e ⟨d, hd⟩ ^ 3 = 1 := by rw [← map_pow, hd3', map_one]
    have h2 : e ⟨d, hd⟩ ≠ 1 := fun h0 => hd1' (e.injective (h0.trans (map_one e).symm))
    rcases sl2_three_eq a (e ⟨d, hd⟩) ha3 ha1 h1 h2 with h | h
    · left
      have : (⟨d, hd⟩ : ↥Lw) = e.symm a := by rw [← h, e.symm_apply_apply]
      exact congrArg Subtype.val this
    · right
      have : (⟨d, hd⟩ : ↥Lw) = (e.symm a)⁻¹ := by rw [← map_inv, ← h, e.symm_apply_apply]
      simpa using congrArg Subtype.val this

theorem mK_le_hz (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (hC137 : U3.C137Statement) (h36 : A36ForSQTK)
    (h1434 : Lemma1434One) : mK T V ≤ hz T V := by
  by_contra hN
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set X := dK T V ⊔ R with hX
  have hsolv : Group.IsSolvable ↥X := by
    by_contra hns
    have hne : perfectCore X ≠ ⊥ := fun h0 => hns ((isSolvable_iff_perfectCore_eq_bot X).mpr h0)
    obtain ⟨K', hK'⟩ := (Set.toFinite
      {K : Subgroup G | K ≠ ⊥ ∧ perfectCore K = K ∧ IsSubnormal K X}).exists_minimal
      ⟨perfectCore X, hne, perfectCore_eq_self_of_perfect (perfectCore_perfect X),
        A3.subnormal_perfectCore (IsSubnormal.refl X)⟩
    exact false_of_mem_cComp h hMod h63 h1222 h1332 h1334 hF h36 h1434
      (mem_cComp_iff_minimal.mpr hK')
  have hC := charTwo_dKR1 h hMod h63
  have hSX := isSylowTwoOf_R1_dK h hMod h63
  obtain ⟨hU, -, hcase, -⟩ := B2_16 hsolv hC hSX rfl
  rcases hcase with ⟨hJ, -⟩ | ⟨hJ, I, hSyl, hJI, hcomm, hindep, hnat, -, -, -, hperm⟩
  · exact not_thompsonJ_le h hMod h63 h1222 h1332 h1334 hF hC137 hN hJ
  set E := conjClosure (quasithinOmegaOneCenter R) X with hE
  have hXE : X ≤ Subgroup.normalizer (E : Set G) := le_normalizer_conjClosure _ _
  have hV1E : fsuV1 T V ≤ E :=
    (fsuV1_le_omegaOneCenter_R1 h hMod h63).trans (le_conjClosure _ _)
  have hCR : X ⊓ Subgroup.centralizer (E : Set G) ≤ R := fun x hx =>
    inf_hz_le_R1 h hMod h63 ⟨hx.1, Subgroup.centralizer_le hV1E hx.2⟩
  have h2 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (E : Set G)) :=
    (pCoreOf_isPGroup 2 _).to_le hCR
  have hJX : thompsonJ X ≤ X := iSup₂_le fun _ hA => hA.1
  have hIX : ∀ L' ∈ I, L' ≤ autI hU X := fun L' hL' =>
    (le_iSup₂_of_le L' hL' le_rfl).trans (hJI.symm.le.trans (autI_mono hU hJX))
  have h1X : convI hU ⟨1, hXE (one_mem X)⟩ = 1 := map_one _
  obtain ⟨L₀, hL₀⟩ : I.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hI
    apply hJ
    have h1 : autI hU (thompsonJ X) = ⊥ := by
      rw [hJI, hI]
      simp
    have hJRN : thompsonJ R ≤ Subgroup.normalizer (E : Set G) :=
      (iSup₂_le fun _ hA => hA.1 : thompsonJ R ≤ R).trans (le_sup_right.trans hXE)
    exact (autI_eq_bot_iff hU hJRN).mp (le_bot_iff.mp (h1 ▸ hSyl.1))
  obtain ⟨c₀, hc₀L, hc₀3, hc₀1, hc₀uniq⟩ := exists_three_of_actsAsNaturalL2 (hnat L₀ hL₀)
  have hc₀X := hIX L₀ hL₀ hc₀L
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hI1 : ∀ L' ∈ I, L' = L₀ := by
    intro L' hL'
    by_contra hne
    obtain ⟨c₁, hc₁L, hc₁3, hc₁1, -⟩ := exists_three_of_actsAsNaturalL2 (hnat L' hL')
    have hc₁X := hIX L' hL' hc₁L
    have hcc : Commute c₀ c₁ := hcomm L₀ hL₀ L' hL' (Ne.symm hne) c₀ hc₀L c₁ hc₁L
    have hc₁z : c₁ ∉ Subgroup.zpowers c₀ := by
      intro hz
      apply hc₁1
      have hle : L₀ ≤ ⨆ L'' ∈ I, ⨆ (_ : L'' ≠ L'), L'' :=
        le_iSup₂_of_le L₀ hL₀ (le_iSup_of_le (Ne.symm hne) le_rfl)
      have hmem : c₁ ∈ L' ⊓ ⨆ L'' ∈ I, ⨆ (_ : L'' ≠ L'), L'' :=
        Subgroup.mem_inf.mpr ⟨hc₁L, hle ((Subgroup.zpowers_le.mpr hc₀L) hz)⟩
      rwa [hindep L' hL', Subgroup.mem_bot] at hmem
    obtain ⟨x₀, hx₀X, hx₀c, hx₀3, -⟩ := exists_lift_three_comm hU hXE h2 (one_mem X) (one_pow 3)
      hc₀X hc₀3 (by rw [h1X]; exact Commute.one_left _)
    obtain ⟨x₁, hx₁X, hx₁c, hx₁3, hx₀₁⟩ := exists_lift_three_comm hU hXE h2 hx₀X hx₀3 hc₁X
      hc₁3 (by rw [hx₀c]; exact hcc)
    have hx₀1 : x₀ ≠ 1 := by
      rintro rfl
      exact hc₀1 (by rw [← hx₀c]; exact h1X)
    have hx₁1 : x₁ ≠ 1 := by
      rintro rfl
      exact hc₁1 (by rw [← hx₁c]; exact h1X)
    have ho₀ := orderOf_eq_prime hx₀3 hx₀1
    have ho₁ := orderOf_eq_prime hx₁3 hx₁1
    have hodd₀ : Odd (orderOf x₀) := by
      rw [ho₀]
      decide
    have hodd₁ : Odd (orderOf x₁) := by
      rw [ho₁]
      decide
    refine false_of_commute_three h hMod h63 (mem_dK_of_odd h h63 hx₀X hodd₀)
      (mem_dK_of_odd h h63 hx₁X hodd₁) ho₀ ho₁ hx₀₁ fun hz => hc₁z ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hx₀c, ← hx₁c, ← map_zpow]
    exact congrArg _ (Subtype.ext (by simp))
  refine false_of_conj_eq_or_inv h hMod h63 h1222 h1332 h1334 hF hU hXE hV1E hc₀X hc₀3 hc₀1
    fun r hr hrN => ?_
  have hρX : convI hU ⟨r, hrN⟩ ∈ autI hU X := convI_mem_autI hU (Subgroup.mem_sup_right hr) hrN
  have hconj : B1.conjAut (convI hU ⟨r, hrN⟩) L₀ = L₀ := hI1 _ (hperm _ hρX L₀ hL₀).1
  have hdL : convI hU ⟨r, hrN⟩ * c₀ * (convI hU ⟨r, hrN⟩)⁻¹ ∈ L₀ := by
    rw [← hconj, B1.mem_conjAut]
    rw [show (convI hU ⟨r, hrN⟩)⁻¹ * (convI hU ⟨r, hrN⟩ * c₀ * (convI hU ⟨r, hrN⟩)⁻¹) *
      convI hU ⟨r, hrN⟩ = c₀ by group]
    exact hc₀L
  refine hc₀uniq _ hdL ?_ ?_
  · rw [conj_pow, hc₀3]
    group
  · intro h1
    apply hc₀1
    calc c₀ = (convI hU ⟨r, hrN⟩)⁻¹ * (convI hU ⟨r, hrN⟩ * c₀ * (convI hU ⟨r, hrN⟩)⁻¹) *
          convI hU ⟨r, hrN⟩ := by group
      _ = 1 := by rw [h1]; group

end CFSG.Quasithin.H13.L32A
