module

public import CFSG.RankThree.PartTwo.Sec21.Item226Pre
import CFSG.RankThree.PartOne.FIS.Item74
public import CFSG.RankThree.PartTwo.Sec21.Item229

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

theorem rank3II_22_6_of (h2115 : Item2115) (h2130 : Item2130) (h222 : Item222)
    (h223 : Item223) (hKW : KOfWellDefinedAll) (h73 : Sec7.Item73)
    (hPhan : PhanChain) (hC : Item226CentralReflection) (hS3 : Item226LocalSetS3)
    (hO3 : Item226OThreeCentral) (hZ : CentralExtensionTrivial226)
    (hLR : LocalRankLowerBound226) : Item226 := by
  intro G _ _ A E U c L hpair hA81
  have hK := hKW G A E U c L hpair
  have hAI := le_iGroup h2130 h222 hpair hK
  have hG := hpair.standing.toTheoremFourHyp
  obtain ⟨φ₀, -, hφ₀D, n, hn1, hnodd, ⟨eL⟩, ⟨eK₀⟩, -⟩ := exists_case_five h222 hpair hA81
  have hn2 : 2 ≤ n := hn1
  have hD3 := isThreeTranspositions_dStarIn_of_four h223 hpair hA81 eL
  have htr := transitive_dStar_of_four h2115 h222 h223 hC hpair hA81
  have hS := hS3 G A E U c L hpair hA81 htr
  have hO := hO3 G A E U c L hpair hA81 htr hS
  have hZ5 : Nonempty (Subgroup.closure (dStar A) ≃* Equiv.Perm (Fin 5)) := by
    obtain ⟨e3⟩ := hS φ₀ hφ₀D
    have htrZ : ∀ d ∈ dStarIn A, ∀ e ∈ dStarIn A,
        ∃ g : Subgroup.closure (dStar A), g * d * g⁻¹ = e := by
      intro d hd e he
      obtain ⟨g, hg, hge⟩ := htr _ hd _ he
      exact ⟨⟨g, hg⟩, Subtype.ext hge⟩
    rcases h73 (Subgroup.closure (dStar A)) (dStarIn A) hD3 htrZ
        ⟨φ₀, Subgroup.subset_closure hφ₀D⟩ hφ₀D 3 (Or.inl rfl)
        (nonempty_closure_localSet_dStarIn _ e3) with h | ⟨-, h⟩
    · exact h
    · exact (h hO).elim
  obtain ⟨e5⟩ := hZ5
  have hX5 : e5 '' dStarIn A = ↑transp5 := by
    apply perm_five_eq_transp
    · rintro g _ ⟨y, hy, rfl⟩
      refine ⟨e5.symm g * y * (e5.symm g)⁻¹, hD3.1.1 _ y hy, ?_⟩
      simp
    · rintro _ ⟨y, hy, rfl⟩
      have hy2 := hD3.1.2.1 y hy
      refine ⟨by rw [← map_mul, Sec7.mul_self_eq_one_of_orderOf_eq_two hy2, map_one],
        fun h => ?_⟩
      rw [MulEquiv.map_eq_one_iff] at h
      rw [h, orderOf_one] at hy2
      norm_num at hy2
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, MulEquiv.orderOf_eq]
      exact hD3.2 x hx y hy
    · exact ⟨_, ⟨⟨φ₀, Subgroup.subset_closure hφ₀D⟩, hφ₀D, rfl⟩⟩
  set y : Fin 4 → Subgroup.closure (dStar A) :=
    fun i => e5.symm (Equiv.swap (Fin.castSucc i) (Fin.succ i)) with hydef
  have hye : ∀ i, e5 (y i) = Equiv.swap (Fin.castSucc i) (Fin.succ i) :=
    fun i => e5.apply_symm_apply _
  have hyD : ∀ i, y i ∈ dStarIn A := by
    intro i
    have h : Equiv.swap (Fin.castSucc i) (Fin.succ i) ∈ (↑transp5 : Set (Equiv.Perm (Fin 5))) :=
      swap_castSucc_succ_mem_transp5 i
    rw [← hX5] at h
    obtain ⟨z, hz, hze⟩ := h
    have : y i = z := by rw [hydef]; simp only; rw [← hze, MulEquiv.symm_apply_apply]
    rw [this]
    exact hz
  set t : Fin 4 → MulAut A := fun i => (y i : MulAut A) with htdef
  have ht : ∀ i, t i ∈ dStar A := hyD
  have hinj : Function.Injective t := by
    intro i j h
    have h' := congrArg e5 (Subtype.ext h : y i = y j)
    rw [hye, hye] at h'
    exact swap_castSucc_succ_injective i j h'
  have hrc : ∀ i j : Fin 4, i.val + 1 < j.val → t j * t i = t i * t j := by
    intro i j hij
    have h : y j * y i = y i * y j := e5.injective (by
      rw [map_mul, map_mul, hye, hye]
      exact (swap_castSucc_succ_commute i j hij).symm)
    exact congrArg Subtype.val h
  have hrn : ∀ i j : Fin 4, i.val + 1 = j.val → t j * t i ≠ t i * t j := by
    intro i j hij h
    have h' := congrArg e5 (Subtype.ext h : y j * y i = y i * y j)
    rw [map_mul, map_mul, hye, hye] at h'
    exact swap_castSucc_succ_not_commute i j hij h'
  have hgenY : Subgroup.closure (Set.range y) = ⊤ := by
    have h : (Subgroup.closure (Set.range fun i : Fin 4 =>
        (Equiv.swap (Fin.castSucc i) (Fin.succ i) : Equiv.Perm (Fin 5)))).map
          e5.symm.toMonoidHom = Subgroup.closure (Set.range y) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [← h, closure_swap_castSucc_succ, Subgroup.map_top_of_surjective _ e5.symm.surjective]
  have hgenT : Subgroup.closure (Set.range t) = Subgroup.closure (dStar A) := by
    have h : (Subgroup.closure (Set.range y)).map (Subgroup.closure (dStar A)).subtype =
        Subgroup.closure (Set.range t) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [← h, hgenY, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfuse : ∀ φ ∈ dStar A, ∃ g ∈ Subgroup.closure (Set.range t),
      ∃ τ ∈ Set.range t, g * τ * g⁻¹ = φ := by
    intro φ hφ
    have hx : e5 ⟨φ, Subgroup.subset_closure hφ⟩ ∈ transp5 := by
      have h : e5 ⟨φ, Subgroup.subset_closure hφ⟩ ∈ e5 '' dStarIn A := ⟨_, hφ, rfl⟩
      rw [hX5] at h
      exact h
    obtain ⟨σ, hσ⟩ := perm_five_transp_class _ hx
    refine ⟨((e5.symm σ : Subgroup.closure (dStar A)) : MulAut A),
      by rw [hgenT]; exact (e5.symm σ).2, t 0, ⟨0, rfl⟩, ?_⟩
    have h : e5.symm σ * y 0 * (e5.symm σ)⁻¹ = ⟨φ, Subgroup.subset_closure hφ⟩ :=
      e5.injective (by rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hye,
        swap_castSucc_succ_zero, hσ])
    exact congrArg Subtype.val h
  have hIeq : iGroup A = ⨆ i, kOf A (t i) := by
    rw [iGroup_eq_iSup_of_fuse h222 hpair hK (T := Set.range t)
      (by rintro _ ⟨i, rfl⟩; exact ht i) hfuse, iSup_range]
  have k : ∀ i, kOf A (t i) ≃* projSL 2 (GaloisField 2 n) := fun i => by
    have hK' : Nonempty (kOf A (t i) ≃* projSL 2 (GaloisField 2 n)) := by
      obtain ⟨g, hg, hgφ⟩ := htr φ₀ hφ₀D (t i) (ht i)
      obtain ⟨e⟩ := nonempty_kOf_mulEquiv_of_conj hK hφ₀D (closure_dStar_le_wStar A hg) hgφ
      exact ⟨e.trans eK₀⟩
    exact hK'.some
  have hcK : ∀ i j : Fin 4, i.val + 1 < j.val →
      ∀ x ∈ kOf A (t i), ∀ z ∈ kOf A (t j), x * z = z * x := by
    intro i j hij x hx z hz
    obtain ⟨-, h2, -⟩ := h223 G A E U c L hpair hA81 n ⟨eL⟩ (t i) (ht i) (t j) (ht j)
    have hne : t j ≠ t i := fun h => by
      have := hinj h
      rw [this] at hij
      omega
    have hb := h2 hne (hrc i j hij)
    have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hb
    exact (Subgroup.mem_centralizer_iff.mp (hle hx) z hz).symm
  have hinfK : ∀ i j : Fin 4, i.val + 1 < j.val → kOf A (t i) ⊓ kOf A (t j) = ⊥ :=
    fun i j hij => inf_eq_bot_of_commute (k i) (hcK i j hij)
  have hch := isChainSystem_of_kOf h222 hpair hK ht hinj (hIeq ▸ hAI) hcK hinfK
  have hadj : ∀ i j : Fin 4, i.val + 1 = j.val →
      IsSUThree ((fun i => kOf A (t i)) i ⊔ (fun i => kOf A (t i)) j) n := by
    intro i j hij
    obtain ⟨-, -, h3⟩ := h223 G A E U c L hpair hA81 n ⟨eL⟩ (t i) (ht i) (t j) (ht j)
    exact Or.inl (h3 (hrn i j hij)).1
  obtain ⟨eq⟩ := hPhan G 4 A (fun i => kOf A (t i)) n (by norm_num) hn1 hnodd hch
    (fun i => ⟨k i⟩) hadj
  have hperf : Group.IsPerfect (⨆ i, kOf A (t i) : Subgroup G) :=
    isPerfect_iSup _ fun i => isPerfect_of_mulEquiv_projSL hn2 (k i)
  have hc0 := hZ _ hperf n hn1 hnodd ⟨eq⟩
  obtain ⟨eX⟩ := nonempty_mulEquiv_of_quotient_center hc0 eq
  have eI : iGroup A ≃* projSU 5 2 n := (MulEquiv.subgroupCongr hIeq).trans eX
  have hn3 : n = 3 := by
    by_contra hne
    obtain ⟨p, hp, hp3, hpl⟩ := hLR (iGroup A) n hn1 hnodd hne ⟨eI⟩
    have := (hpl.trans (localRank_subgroup_le hp (iGroup A))).trans_lt (hG.localRank_lt p hp hp3)
    omega
  subst hn3
  exact ⟨⟨e5⟩, ⟨eI⟩⟩

theorem rank3II_22_6_of_item73 (h2115 : Item2115) (h2130 : Item2130) (h222 : Item222)
    (h223 : Item223) (hKW : KOfWellDefinedAll) (hPhan : PhanChain)
    (hC : Item226CentralReflection) (hS3 : Item226LocalSetS3) (hO3 : Item226OThreeCentral)
    (hZ : CentralExtensionTrivial226) (hLR : LocalRankLowerBound226) : Item226 :=
  rank3II_22_6_of h2115 h2130 h222 h223 hKW PartOne.FIS.item73_proved hPhan hC hS3 hO3 hZ hLR

end CFSG.RankThree.PartTwo.Sec21
