module

public import CFSG.Quasithin.Vol2.Ch11SecO1I
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4J
public import CFSG.Quasithin.Vol2.Ch11SecO1B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA SecS SecS.C11P9A
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (blkN blkN_coe blkN_surjective blkIdx sigma2
  spMat_col_zero_of_mem_Q2_zero exists_finset_card_four)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped IsMulCommutative

section Levi

variable {K : Type} [Field K] [Finite K]

theorem proj_mulVec_of_mem_N0 {M : Assembly.LowTwoRank.StatedSp 2 K}
    (hM : M ∈ perfectCore (Q2 K 0)) {y : Fin 2 ⊕ Fin 2 → K} (hy : y (Sum.inr 0) = 0) :
    (fun i : Fin 2 => (mat 2 K M *ᵥ y) (sigma2 0 i)) =
      ((blkN 0 ⟨M, hM⟩ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        fun i : Fin 2 => y (sigma2 0 i) := by
  have hMQ := perfectCore_le _ hM
  have c1 := spMat_col_zero_of_mem_Q2_zero hMQ (Sum.inl 1) (by simp)
  have c3 := spMat_col_zero_of_mem_Q2_zero hMQ (Sum.inr 1) (by simp)
  rw [blkN_coe]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, mat_apply, blkIdx,
      sigma2, hy, c1, c3]

end Levi

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem natV3_sp4 (hS : SecD.NatSetting11 G T L I n) (hk : KindSp4 L (fsuV T I) n)
    {V₁ V₃ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hV₃ : IsVi T L I n 3 V₃) :
    V₁ ≤ V₃ ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
      IsNaturalSection (LOf L V₁) V₃ V₁ (CFSG.pCore 2 ↥(LOf L V₁))
        (Assembly.LowTwoRank.StatedSL 2 F) := by
  have := isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, hK, π, f, hπ, hf⟩ := exists_coord_sp4 hS hk
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := exists_finset_card_four (four_le_card hn hK)
  have hsq := sq_eq_one hS
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf (isSylowTwoOf_P hS)
  have hU₁ := isFlagW_of_isVi hS hV₁
  have hU₃ := isFlagW_of_isVi hS hV₃
  have hU₁' := hU₁
  have hU₃' := hU₃
  rw [← hK] at hU₁' hU₃'
  obtain ⟨S₁, hS₁, hc₁, hE₁⟩ := exists_eq_pre_of_isFlagW_sp hsq hf hg hU₁'
  obtain ⟨S₃, hS₃, hc₃, hE₃⟩ := exists_eq_pre_of_isFlagW_sp hsq hf hg hU₃'
  have e₁ : S₁ = spLine K := (eq_std_of_stable_sp hS₁).1 (by rw [hc₁, pow_one])
  have e₃ : S₃ = spHyp K := (eq_std_of_stable_sp hS₃).2.2 hc₃
  subst e₁ e₃
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hV₃V := SecA.IsVi.le_fsuV hV₃
  have hV₁f : ∀ v : ↥(fsuV T I), (v : G) ∈ V₁ ↔ f v ∈ gmapSp g (spLine K) := fun v => by
    rw [← Subgroup.mem_subgroupOf, hE₁]
    rfl
  have hV₃f : ∀ v : ↥(fsuV T I), (v : G) ∈ V₃ ↔ f v ∈ gmapSp g (spHyp K) := fun v => by
    rw [← Subgroup.mem_subgroupOf, hE₃]
    rfl
  have hV₁₃ : V₁ ≤ V₃ := fun v hv => by
    rw [show v = ((⟨v, hV₁V hv⟩ : ↥(fsuV T I)) : G) from rfl, hV₃f]
    have hle : spLine K ≤ spHyp K := fun x (hx : x ∈ spLine K) => hx.2.1
    exact gmapSp_mono g hle ((hV₁f _).mp hv)
  refine ⟨hV₁₃, ?_⟩
  have hL₁L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hLV : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := hL₁L.trans hS.le_normalizer
  have hC : IsPGroup 2 ↥(LOf L V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    (isPGroup_inf_centralizer hS).to_le (inf_le_inf_right _ hL₁L)
  have hL₁ : autOn (LOf L V₁) (fsuV T I) = (perfectCore (Q2 K 0)).map (psiSp π g) := by
    rw [SecS.autOn_lOf hS.le_normalizer hV₁V, hE₁, gammaW_pre_eq hf g 0 _ flag_one_eq]
  obtain ⟨θ, hθs, hθk, hθ⟩ := exists_levi_of_autOn hLV hC (psiSp_injective hf g) hL₁
  have hLV₃ : LOf L V₁ ≤ Subgroup.normalizer (V₃ : Set G) := by
    intro a ha
    have haL := hL₁L ha
    have haV := hLV ha
    have hτH : ∀ h ∈ autOn L (fsuV T I), conjV (fsuV T I) a haV * h *
        (conjV (fsuV T I) a haV)⁻¹ ∈ autOn L (fsuV T I) :=
      fun h hh => (Subgroup.mem_normalizer_iff.mp (autOn_le_normalizer
        (Subgroup.le_normalizer : L ≤ _) (conjV_mem_autOn haL haV)) h).mp hh
    have h1 : conjV (fsuV T I) a haV ∈ stabW (V₁.subgroupOf (fsuV T I)) :=
      (conjV_mem_stabW_iff hV₁V haV).mpr ((perfectCore_le _ ha).2)
    have h3 := (factN13Sp4_holds K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P hS) _ _ hU₁ hU₃ _
      (mem_stabW_bot _) hτH).mp h1
    exact (conjV_mem_stabW_iff hV₃V haV).mp h3
  set gi := mat 2 K g⁻¹ with hgi
  let β : ↥V₃ →* Multiplicative (Fin 2 → K) :=
    { toFun := fun v => Multiplicative.ofAdd fun i : Fin 2 =>
        (gi *ᵥ f ⟨v, hV₃V v.2⟩) (sigma2 0 i)
      map_one' := by
        rw [show (⟨((1 : ↥V₃) : G), hV₃V (1 : ↥V₃).2⟩ : ↥(fsuV T I)) = 1 from rfl, hf.map_one,
          Matrix.mulVec_zero]
        rfl
      map_mul' := fun u v => by
        rw [show (⟨((u * v : ↥V₃) : G), hV₃V (u * v).2⟩ : ↥(fsuV T I)) =
          ⟨u, hV₃V u.2⟩ * ⟨v, hV₃V v.2⟩ from rfl, hf.map_mul, Matrix.mulVec_add]
        rfl }
  have hβ : ∀ v : ↥V₃, Multiplicative.toAdd (β v) =
      fun i : Fin 2 => (gi *ᵥ f ⟨v, hV₃V v.2⟩) (sigma2 0 i) := fun _ => rfl
  have hy : ∀ v : ↥V₃, (gi *ᵥ f ⟨v, hV₃V v.2⟩) (Sum.inr 0) = 0 := fun v =>
    mem_gmapSp.mp ((hV₃f ⟨v, hV₃V v.2⟩).mp v.2)
  let : Fintype K := Fintype.ofFinite K
  refine ⟨K, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hK],
    isNaturalSection_of_levi hK4 hLV₃ ((blkN 0).comp θ) ((blkN_surjective hK4 0).comp hθs)
      (by rw [← MonoidHom.comap_ker]; exact (isPGroup_ker_blkN 0).comap_of_ker_isPGroup θ hθk)
      β ?_ ?_ ?_⟩
  · intro y
    obtain ⟨v, hv⟩ := hf.surj (mat 2 K g *ᵥ vec4 0 (y 0) 0 (y 1))
    have hv₃ : (v : G) ∈ V₃ := by
      rw [hV₃f, hv, mem_gmapSp, mat_inv_mulVec]
      rfl
    refine ⟨⟨v, hv₃⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ, show (⟨((⟨v, hv₃⟩ : ↥V₃) : G), _⟩ : ↥(fsuV T I)) = v from rfl, hv, hgi,
      mat_inv_mulVec]
    funext i
    fin_cases i <;> rfl
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, show (v : G) = ((⟨v, hV₃V v.2⟩ :
      ↥(fsuV T I)) : G) from rfl, hV₁f, mem_gmapSp, ← Multiplicative.toAdd.injective.eq_iff,
      hβ, toAdd_one]
    constructor
    · intro h
      exact ⟨congrFun h 0, hy v, congrFun h 1⟩
    · rintro ⟨h1, -, h3⟩
      funext i
      fin_cases i
      · exact h1
      · exact h3
  · intro a u v huv
    have hv : (⟨v, hV₃V v.2⟩ : ↥(fsuV T I)) = conjV (fsuV T I) a (hLV a.2) ⟨u, hV₃V u.2⟩ :=
      Subtype.ext (by rw [conjV_apply_coe, huv, InvMemClass.coe_inv])
    rw [hβ, hβ, hv, ← hθ, psiSp_apply, hf.act4, hgi, conj_mulVec_sp,
      proj_mulVec_of_mem_N0 (θ a).2 (hy u), MonoidHom.comp_apply]

theorem _root_.CFSG.Quasithin.Vol2.Ch11.SecD.natV3Fact_holds : SecD.NatV3Fact := by
  intro G _ _ T L I n V₁ V₃ hS hk hV₁ hV₃
  rcases hk with hk | hk
  · exact natV3_sl3 hS hk hV₁ hV₃
  · exact natV3_sp4 hS hk hV₁ hV₃

end CFSG.Quasithin.Vol2.Ch11.SecO1
