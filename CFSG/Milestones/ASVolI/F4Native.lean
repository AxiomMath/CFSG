module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPointSubgroup
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ModelRad
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNGen
public import CFSG.GH74.GLS.SP.Local.SPLFaith
public import CFSG.Quasithin.Recognition.CertG2TwoOuter
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSys
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctRGD2
public import CFSG.LieType.Chevalley.LangRootRankOneTorus
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdTwoCls
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Orient3
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.Centralizers
public import CFSG.Quasithin.Recognition.CertTwoF4AmalgamLocal
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocStd

public section

namespace CFSG.ASVolI

open CFSG.Open
section PartBurnsideF4hCl

section Generic

theorem burnsideF4h_cl_isLieParabolics_top_of {G : Type} [Group G] {p : ℕ}
    {B P₁ P₂ S : Subgroup G} (hS : IsPGroup p S) (hSi : ¬ p ∣ S.index)
    (hB : Subgroup.normalizer (S : Set G) = B) (hne : P₁ ≠ P₂) (hinf : P₁ ⊓ P₂ = B)
    (h₁ : IsCoatom P₁) (h₂ : IsCoatom P₂)
    (hco : ∀ Q : Subgroup G, B ≤ Q → IsCoatom Q → Q = P₁ ∨ Q = P₂) :
    ChF.IsLieParabolics p ⊤ B P₁ P₂ := by
  refine ⟨⟨S, ⟨le_top, hS, ?_⟩, ?_⟩, hne, hinf, fun Q => ⟨?_, ?_⟩⟩
  · rwa [Subgroup.relIndex_top_right]
  · rw [top_inf_eq, hB]
  · rintro ⟨hBQ, -, hQ, hR⟩
    exact hco Q hBQ ⟨hQ, fun R hQR => hR R hQR le_top⟩
  · rintro (rfl | rfl)
    · exact ⟨hinf ▸ inf_le_left, le_top, h₁.1, fun R hR _ => h₁.2 R hR⟩
    · exact ⟨hinf ▸ inf_le_right, le_top, h₂.1, fun R hR _ => h₂.2 R hR⟩

theorem burnsideF4h_cl_isLieParabolics_map {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {p : ℕ} {B P₁ P₂ : Subgroup G} (h : ChF.IsLieParabolics p ⊤ B P₁ P₂) :
    ChF.IsLieParabolics p ⊤ (B.map e.toMonoidHom) (P₁.map e.toMonoidHom)
      (P₂.map e.toMonoidHom) := by
  obtain ⟨⟨S, ⟨-, hS, hSi⟩, hB⟩, hne, hinf, hQ⟩ := h
  have hco : ∀ Q : Subgroup G, B ≤ Q → IsCoatom Q → Q = P₁ ∨ Q = P₂ := fun Q hBQ hQc =>
    (hQ Q).1 ⟨hBQ, le_top, hQc.1, fun R hR _ => hQc.2 R hR⟩
  have hc : ∀ Q : Subgroup G, Q = P₁ ∨ Q = P₂ → IsCoatom Q := fun Q hQ' => by
    obtain ⟨-, -, h3, h4⟩ := (hQ Q).2 hQ'
    exact ⟨h3, fun R hR => h4 R hR le_top⟩
  have hmap : ∀ Q : Subgroup G, IsCoatom (Q.map e.toMonoidHom) ↔ IsCoatom Q := fun Q =>
    OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e) Q
  refine burnsideF4h_cl_isLieParabolics_top_of (S := S.map e.toMonoidHom) (hS.map _) ?_ ?_ ?_ ?_
    ((hmap P₁).2 (hc P₁ (Or.inl rfl))) ((hmap P₂).2 (hc P₂ (Or.inr rfl))) ?_
  · change ¬ p ∣ (S.map (e : G →* G')).index
    rwa [Subgroup.index_map_equiv, ← Subgroup.relIndex_top_right]
  · rw [← Subgroup.map_equiv_normalizer_eq, hB, top_inf_eq]
  · exact fun h' => hne (Subgroup.map_injective e.injective h')
  · rw [← Subgroup.map_inf_eq _ _ _ e.injective, hinf]
  · intro Q hBQ hQc
    have hQ' : (Q.comap e.toMonoidHom).map e.toMonoidHom = Q :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective Q
    have hBQ' : B ≤ Q.comap e.toMonoidHom := Subgroup.map_le_iff_le_comap.1 hBQ
    have hQc' : IsCoatom (Q.comap e.toMonoidHom) := (hmap _).1 (hQ'.symm ▸ hQc)
    rcases hco _ hBQ' hQc' with h' | h'
    · left
      rw [← hQ', h']
    · right
      rw [← hQ', h']

theorem burnsideF4h_cl_map_inf_of_ker_le {G G' : Type} [Group G] [Group G'] (f : G →* G')
    {A C : Subgroup G} (hA : f.ker ≤ A) : (A ⊓ C).map f = A.map f ⊓ C.map f := by
  refine le_antisymm (Subgroup.map_inf_le _ _ _) ?_
  rintro x ⟨⟨a, ha, rfl⟩, ⟨c, hc, hca⟩⟩
  have hk : a⁻¹ * c ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hca, inv_mul_cancel]
  have hcA : c ∈ A := by
    have := A.mul_mem ha (hA hk)
    rwa [mul_inv_cancel_left] at this
  exact ⟨c, ⟨hcA, hc⟩, hca⟩

theorem burnsideF4h_cl_mem_rawStabilizer {index : Type} [Fintype index] [DecidableEq index]
    {K : Type} [Field K] (space : Set (index → K)) (g : GL index K) :
    g ∈ ChF.ClassicalRoots.rawStabilizer space ↔
      ∀ vector : index → K, (g : Matrix index index K).mulVec vector ∈ space ↔
        vector ∈ space := by
  let S : Subgroup (GL index K) :=
    { carrier := {actor | ∀ vector : index → K,
        (actor : Matrix index index K).mulVec vector ∈ space ↔ vector ∈ space}
      one_mem' := by
        intro vector
        simp
      mul_mem' := by
        intro a b ha hb vector
        have h1 := ha ((b : Matrix index index K).mulVec vector)
        have h2 := hb vector
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact h1.trans h2
      inv_mem' := by
        intro a ha vector
        have h1 := ha (((a⁻¹ : GL index K) : Matrix index index K).mulVec vector)
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1
        exact h1.symm }
  have hS : ChF.ClassicalRoots.rawStabilizer space = S := Subgroup.closure_eq S
  rw [hS]
  exact Iff.rfl

theorem burnsideF4h_cl_map_eq_iff {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (W : Submodule K (ι → K)) {A C : Matrix ι ι K} (hCA : C * A = 1) (hAC : A * C = 1) :
    W.map (Matrix.mulVecLin A) = W ↔ ∀ v : ι → K, A.mulVec v ∈ W ↔ v ∈ W := by
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have h2 : A.mulVec w = A.mulVec v := hwv
      have : w = v := by
        calc w = C.mulVec (A.mulVec w) := by rw [Matrix.mulVec_mulVec, hCA, Matrix.one_mulVec]
          _ = C.mulVec (A.mulVec v) := by rw [h2]
          _ = v := by rw [Matrix.mulVec_mulVec, hCA, Matrix.one_mulVec]
      rw [this] at hw
      exact hw
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hx
      have hv : C.mulVec x ∈ W := by
        refine (h _).1 ?_
        rw [Matrix.mulVec_mulVec, hAC, Matrix.one_mulVec]
        exact hx
      refine ⟨_, hv, ?_⟩
      change A.mulVec (C.mulVec x) = x
      rw [Matrix.mulVec_mulVec, hAC, Matrix.one_mulVec]

theorem burnsideF4h_cl_charP {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) : CharP K p := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)

end Generic

section Symplectic

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem burnsideF4h_cl_sp_stab_inf (K : Type) [Field K] :
    stabilizer 2 K (flag 2 K 1) ⊓ stabilizer 2 K (flag 2 K 2) = borelSubgroup 2 K := by
  ext g
  rw [Subgroup.mem_inf, mem_borelSubgroup]
  constructor
  · rintro ⟨h1, h2⟩ i hi1 hi2
    interval_cases i
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 1 le_rfl (by norm_num), h 2 (by norm_num) le_rfl⟩

theorem burnsideF4h_cl_sp_isLieParabolics (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] :
    ChF.IsLieParabolics p ⊤ (projBorel 2 K) (projStabilizer 2 K (flag 2 K 1))
      (projStabilizer 2 K (flag 2 K 2)) := by
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnipotent (K := K) p (r := 2) (by norm_num)
  refine burnsideF4h_cl_isLieParabolics_top_of (S := projUnipotent 2 K) ?_ ?_
    (normalizer_projUnipotent p (by norm_num)) ?_ ?_
    (isCoatom_projStabilizer_flag (by norm_num) (by norm_num))
    (isCoatom_projStabilizer_flag (by norm_num) (by norm_num)) ?_
  · rw [← hSU]
    exact SU.isPGroup'
  · rw [← hSU]
    exact SU.not_dvd_index
  · intro h
    have h' := congrArg (Subgroup.comap (proj 2 K)) h
    rw [comap_projStabilizer, comap_projStabilizer] at h'
    apply weylRep_notMem_stabilizer (K := K) (r := 2) 0
    rw [show ((0 : Fin 2) : ℕ) + 1 = 1 from rfl, h', ← flagStabilizer_singleton]
    exact ((subflag_generation (K := K) (r := 2) {2} (by simp)).2.1 0).2 (by simp)
  · rw [projStabilizer, projStabilizer, ← burnsideF4h_cl_map_inf_of_ker_le _ (by
      rw [ker_proj]; exact spScalars_le_stabilizer _), burnsideF4h_cl_sp_stab_inf]
    rfl
  · intro Q hBQ hQ
    obtain ⟨d, hd1, hd2, rfl⟩ := eq_projStabilizer_of_isCoatom hQ hBQ
    interval_cases d
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem burnsideF4h_cl_sp_coordinateSpace {K : Type} [Field K] (v : Fin 2 ⊕ Fin 2 → K) :
    (v ∈ ChF.ClassicalRoots.coordinateSpace ({Sum.inl 0} : Set (Fin 2 ⊕ Fin 2)) ↔
        v ∈ flag 2 K 1) ∧
      (v ∈ ChF.ClassicalRoots.coordinateSpace ({Sum.inl 0, Sum.inl 1} : Set (Fin 2 ⊕ Fin 2)) ↔
        v ∈ flag 2 K 2) := by
  rw [mem_flag_of_le (by norm_num), mem_flag_of_le (by norm_num), mem_isoFlag, mem_isoFlag]
  simp only [ChF.ClassicalRoots.coordinateSpace, Set.mem_setOf_eq]
  constructor
  · constructor
    · intro h
      refine ⟨fun j => h (Sum.inr j) (by simp), fun j hj => h (Sum.inl j) ?_⟩
      fin_cases j <;> simp_all
    · rintro ⟨h1, h2⟩ pos hpos
      rcases pos with j | j
      · apply h2 j
        fin_cases j <;> simp_all
      · exact h1 j
  · constructor
    · intro h
      refine ⟨fun j => h (Sum.inr j) (by simp), fun j hj => ?_⟩
      exact absurd hj (by have := j.isLt; omega)
    · rintro ⟨h1, -⟩ pos hpos
      rcases pos with j | j
      · exfalso
        apply hpos
        fin_cases j <;> simp
      · exact h1 j

end Symplectic

section SymplecticRoot

open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem burnsideF4h_cl_sp_form_mulVec {K : Type} [Field K] (g : StatedSp 2 K)
    (x y : Fin 2 ⊕ Fin 2 → K) :
    (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) ⬝ᵥ
        ((fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y)) =
      x ⬝ᵥ ((fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y) := by
  have hg := (CFSG.Open.StatedAPI.mem_statedSp_iff).1 g.2
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg, ← Matrix.dotProduct_mulVec]

theorem burnsideF4h_cl_sp_form_e0 {K : Type} [Field K] (c : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (c • Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ⬝ᵥ
        ((fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      c * v (Sum.inr 0) := by
  rw [smul_dotProduct, single_one_dotProduct, fromBlocks_mulVec]
  simp

theorem burnsideF4h_cl_sp_inv_f0 {K : Type} [Field K] {g : StatedSp 2 K} {c : K}
    (hg : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1) (v : Fin 2 ⊕ Fin 2 → K) :
    ((((g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) (Sum.inr 0) = c * v (Sum.inr 0) := by
  set N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    (((g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    with hN
  have h := burnsideF4h_cl_sp_form_mulVec g (Pi.single (Sum.inl 0) 1) (N *ᵥ v)
  have hMN : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (N *ᵥ v) = v := by
    rw [hN, Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  rw [hMN, hg, burnsideF4h_cl_sp_form_e0] at h
  have h1 := burnsideF4h_cl_sp_form_e0 (1 : K) (N *ᵥ v)
  rw [one_smul, one_mul] at h1
  rw [h1] at h
  exact h.symm

theorem burnsideF4h_cl_sp_conj_long {K : Type} [Field K] {g x : StatedSp 2 K} {c t : K}
    (hg : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1)
    (hx : ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      1 + Matrix.single (Sum.inl 0) (Sum.inr 0) t) :
    (((g * x * g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      1 + Matrix.single (Sum.inl 0) (Sum.inr 0) (c ^ 2 * t) := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hw := burnsideF4h_cl_sp_inv_f0 hg v
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx]
  set w := (((g⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v with hwdef
  have hMw :
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w = v := by
    rw [hwdef, Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  have hsingle : ∀ (s : K) (u : Fin 2 ⊕ Fin 2 → K),
      Matrix.single (Sum.inl 0) (Sum.inr 0) s *ᵥ u =
        (s * u (Sum.inr 0)) • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) := by
    intro s u
    rw [single_mulVec]
    funext i
    by_cases hi : i = Sum.inl 0
    · subst hi
      simp
    · simp [Function.update_of_ne hi, Pi.single_apply, hi]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, hsingle, Matrix.mulVec_add, Matrix.mulVec_smul, hMw,
    hg, Matrix.add_mulVec, Matrix.one_mulVec, hsingle, hw, smul_smul]
  congr 2
  ring

theorem burnsideF4h_cl_sp_stab_le_normalizer (K : Type) [Field K] (S : Set (StatedSp 2 K))
    (hS : ∀ g : StatedSp 2 K, g ∈ S ↔ ∃ t : K,
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        1 + Matrix.single (Sum.inl 0) (Sum.inr 0) t) :
    stabilizer 2 K (flag 2 K 1) ≤
      Subgroup.normalizer (Subgroup.closure S : Set (StatedSp 2 K)) := by
  have he0 : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 1 := by
    rw [mem_flag_of_le (by norm_num), mem_isoFlag]
    refine ⟨fun j => by simp, fun j hj => ?_⟩
    have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
    simp [Pi.single_apply, hj0]
  have heig : ∀ g ∈ stabilizer 2 K (flag 2 K 1), ∃ c : K,
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1 := by
    intro g hg
    have hmem : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Pi.single (Sum.inl 0) 1 ∈ flag 2 K 1 := by
      rw [← mem_stabilizer.1 hg]
      exact Submodule.mem_map_of_mem he0
    rw [mem_flag_of_le (by norm_num), mem_isoFlag] at hmem
    obtain ⟨h1, h2⟩ := hmem
    refine ⟨(((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      Pi.single (Sum.inl 0) 1) (Sum.inl 0), ?_⟩
    funext i
    rcases i with j | j
    · by_cases hj : j = 0
      · subst hj
        simp
      · rw [h2 j (Nat.one_le_iff_ne_zero.mpr fun h => hj (Fin.ext h))]
        simp [Pi.single_apply, hj]
    · rw [h1 j]
      simp
  have hconj : ∀ g ∈ stabilizer 2 K (flag 2 K 1), ∀ x ∈ Subgroup.closure S,
      g * x * g⁻¹ ∈ Subgroup.closure S := by
    intro g hg
    obtain ⟨c, hc⟩ := heig g hg
    have hle : Subgroup.closure S ≤
        (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨t, ht⟩ := (hS x).1 hx
      exact Subgroup.subset_closure ((hS _).2 ⟨c ^ 2 * t, burnsideF4h_cl_sp_conj_long hc ht⟩)
    intro x hx
    exact hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj g hg h, fun hh => ?_⟩
  have := hconj g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

end SymplecticRoot

section SymplecticMarking

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem burnsideF4h_cl_Sp4 (p exponent : ℕ) (H : Type) [Group H]
    (marking : ChF.ClassicalRoots.Marking .Sp4 p exponent H) :
    ChF.IsLieParabolics p (⊤ : Subgroup H) marking.borel (marking.parabolic false)
        (marking.parabolic true) ∧
      marking.parabolic false ≤ Subgroup.normalizer (marking.root .longOne false : Set H) := by
  set K := marking.field
  haveI : Fact p.Prime := ⟨marking.prime⟩
  have hK : Nat.card K = p ^ exponent := by simpa using marking.field_card
  haveI : CharP K p := burnsideF4h_cl_charP hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have keym : ∀ (b : Bool) (x : StatedSp 2 K),
      x ∈ ChF.ClassicalRoots.nativeParabolic .Sp4 (p ^ exponent) K marking.basis b ↔
        x ∈ stabilizer 2 K (flag 2 K (if b then 2 else 1)) := by
    intro b x
    rw [hbasis]
    have h1 : x ∈ ChF.ClassicalRoots.nativeParabolic .Sp4 (p ^ exponent) K 1 b ↔
        (x : GL (ChF.ClassicalRoots.Coord .Sp4) K) ∈ ChF.ClassicalRoots.rawStabilizer
          ((fun vector => ((1 : GL (ChF.ClassicalRoots.Coord .Sp4) K) :
            Matrix (ChF.ClassicalRoots.Coord .Sp4) (ChF.ClassicalRoots.Coord .Sp4) K).mulVec
              vector) ''
            ChF.ClassicalRoots.coordinateSpace (if b then ChF.ClassicalRoots.flagTwo .Sp4
              else ChF.ClassicalRoots.flagOne .Sp4)) :=
      Iff.rfl
    rw [h1, burnsideF4h_cl_mem_rawStabilizer, mem_stabilizer,
      burnsideF4h_cl_map_eq_iff _
        (C := (((x⁻¹ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
        (by rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one])
        (by rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          Units.val_one])]
    simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']
    cases b
    · simp only [Bool.false_eq_true, if_false, ChF.ClassicalRoots.flagOne]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sp_coordinateSpace _).1, (burnsideF4h_cl_sp_coordinateSpace _).1]
    · simp only [if_true, ChF.ClassicalRoots.flagTwo]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sp_coordinateSpace _).2, (burnsideF4h_cl_sp_coordinateSpace _).2]
  let e : StatedProj (StatedSp 2 K) ≃* H := marking.identification
  have hpar : ∀ b : Bool, marking.parabolic b =
      (projStabilizer 2 K (flag 2 K (if b then 2 else 1))).map e.toMonoidHom := by
    intro b
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨proj 2 K x, ⟨x, (keym b x).1 hx, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, (keym b x).2 hx, rfl⟩
  have hbor : marking.borel = (projBorel 2 K).map e.toMonoidHom := by
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ∈ stabilizer 2 K (flag 2 K 1) ⊓ stabilizer 2 K (flag 2 K 2) :=
        ⟨(keym false x).1 (Subgroup.mem_inf.1 hx).1, (keym true x).1 (Subgroup.mem_inf.1 hx).2⟩
      rw [burnsideF4h_cl_sp_stab_inf] at hx'
      exact ⟨proj 2 K x, ⟨x, hx', rfl⟩, rfl⟩
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      rw [← burnsideF4h_cl_sp_stab_inf] at hx
      exact ⟨x, Subgroup.mem_inf.2 ⟨(keym false x).2 (Subgroup.mem_inf.1 hx).1,
        (keym true x).2 (Subgroup.mem_inf.1 hx).2⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · have h := burnsideF4h_cl_isLieParabolics_map e (burnsideF4h_cl_sp_isLieParabolics K p)
    rw [hbor, hpar false, hpar true]
    simpa using h
  ·
    have hle : ChF.ClassicalRoots.nativeParabolic .Sp4 (p ^ exponent) K marking.basis false ≤
        Subgroup.normalizer (ChF.ClassicalRoots.nativeRoot .Sp4 (p ^ exponent) marking.basis
          .longOne false : Set (ChF.ClassicalRoots.nativeGroup .Sp4 (p ^ exponent) K)) := by
      intro x hx
      have hx' := (keym false x).1 hx
      simp only [Bool.false_eq_true, if_false] at hx'
      refine burnsideF4h_cl_sp_stab_le_normalizer K _ (fun g => ?_) hx'
      rw [hbasis]
      change (ChF.ClassicalRoots.RootAllowed .Sp4 .longOne ∧ ∃ parameter central : K,
        ChF.ClassicalRoots.ParameterAllowed .Sp4 (p ^ exponent) .longOne parameter central ∧
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          ChF.ClassicalRoots.markedMatrix .Sp4 (p ^ exponent) 1 .longOne false parameter
            central) ↔ _
      have hm : ∀ t c : K, ChF.ClassicalRoots.markedMatrix .Sp4 (p ^ exponent) 1 .longOne false
          t c = 1 + Matrix.single (Sum.inl 0) (Sum.inr 0) t := by
        intro t c
        simp only [ChF.ClassicalRoots.markedMatrix, ChF.ClassicalRoots.positiveMatrix,
          ChF.ClassicalRoots.symplecticRoot, Bool.false_eq_true, if_false, Units.val_one,
          inv_one, Matrix.one_mul, Matrix.mul_one]
        congr 1
        ext i j
        simp only [ChF.ClassicalRoots.matrixUnit, Matrix.single_apply]
        by_cases h1 : i = Sum.inl 0 <;> by_cases h2 : j = Sum.inr 0 <;> simp [h1, h2, eq_comm]
      simp only [hm]
      constructor
      · rintro ⟨-, t, -, -, ht⟩
        exact ⟨t, ht⟩
      · rintro ⟨t, ht⟩
        exact ⟨Or.inr (Or.inr (Or.inl rfl)), t, 0, trivial, ht⟩
    exact (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map _)

end SymplecticMarking

section Linear

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem burnsideF4h_cl_sl_stab_inf (K : Type) [Field K] :
    stabilizer (flagSpace 3 K 1) ⊓ stabilizer (flagSpace 3 K 2) = upperTriangular 3 K := by
  refine le_antisymm ?_ (le_inf (upperTriangular_le_stabilizer_flagSpace 1)
    (upperTriangular_le_stabilizer_flagSpace 2))
  rintro g ⟨h1, h2⟩
  have hcol : ∀ (d : ℕ) (j : Fin 3), g ∈ stabilizer (flagSpace 3 K d) → (j : ℕ) < d →
      ∀ i : Fin 3, d ≤ (i : ℕ) → (g : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro d j hg hjd i hdi
    have hmem : Pi.single j (1 : K) ∈ flagSpace 3 K d := by
      rw [mem_flagSpace]
      intro c hc
      have hcj : c ≠ j := fun h => by subst h; omega
      simp [Pi.single_apply, hcj]
    have himg : Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K) (Pi.single j 1) ∈
        flagSpace 3 K d := by
      rw [← (mem_stabilizer.1 hg)]
      exact Submodule.mem_map_of_mem hmem
    have := mem_flagSpace.1 himg i hdi
    rwa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] at this
  intro i j hij
  have hj : (j : ℕ) < i := hij
  have hi : (i : ℕ) < 3 := i.2
  rcases (show (j : ℕ) = 0 ∨ (j : ℕ) = 1 by omega) with hj0 | hj1
  · exact hcol 1 j h1 (by omega) i (by omega)
  · exact hcol 2 j h2 (by omega) i (by omega)

theorem burnsideF4h_cl_sl_isLieParabolics (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] :
    ChF.IsLieParabolics p ⊤ (projUpperTriangular 3 K) (projStabilizer (flagSpace 3 K 1))
      (projStabilizer (flagSpace 3 K 2)) := by
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  refine burnsideF4h_cl_isLieParabolics_top_of (S := projUnitriangular 3 K) ?_ ?_
    (normalizer_projUnitriangular p) ?_ ?_
    (isCoatom_projStabilizer_flagSpace (by norm_num) (by norm_num))
    (isCoatom_projStabilizer_flagSpace (by norm_num) (by norm_num)) ?_
  · rw [← hSU]
    exact SU.isPGroup'
  · rw [← hSU]
    exact SU.not_dvd_index
  · intro h
    have h' := congrArg (Subgroup.comap (proj 3 K)) h
    rw [comap_projStabilizer, comap_projStabilizer] at h'
    apply reflection_notMem_stabilizer (K := K) (n := 3) (d := 1) le_rfl (by norm_num)
    rw [h']
    exact reflection_mem_stabilizer_of_ne (K := K) (n := 3) (i := 2) (j := 1) le_rfl
      (by norm_num) (by norm_num)
  · rw [projStabilizer, projStabilizer, projUpperTriangular,
      ← burnsideF4h_cl_map_inf_of_ker_le _ (by rw [ker_proj]; exact scalars_le_stabilizer _),
      burnsideF4h_cl_sl_stab_inf]
  · intro Q hBQ hQ
    obtain ⟨d, hd1, hd2, rfl⟩ := eq_projStabilizer_of_isCoatom hQ hBQ
    interval_cases d
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem burnsideF4h_cl_sl_coordinateSpace {K : Type} [Field K] (v : Fin 3 → K) :
    (v ∈ ChF.ClassicalRoots.coordinateSpace ({0} : Set (Fin 3)) ↔ v ∈ flagSpace 3 K 1) ∧
      (v ∈ ChF.ClassicalRoots.coordinateSpace ({0, 1} : Set (Fin 3)) ↔
        v ∈ flagSpace 3 K 2) := by
  rw [mem_flagSpace, mem_flagSpace]
  simp only [ChF.ClassicalRoots.coordinateSpace, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  refine ⟨⟨fun h j hj => h j fun h0 => ?_, fun h j hj => h j ?_⟩,
    ⟨fun h j hj => h j fun h0 => ?_, fun h j hj => h j ?_⟩⟩
  · rw [Fin.ext_iff] at h0
    simp only [Fin.val_zero] at h0
    omega
  · rw [Fin.ext_iff] at hj
    simp only [Fin.val_zero] at hj
    omega
  · rcases h0 with h0 | h0 <;> rw [Fin.ext_iff] at h0 <;> simp at h0 <;> omega
  · simp only [not_or, Fin.ext_iff] at hj
    simp only [Fin.val_zero, Fin.val_one] at hj
    omega

end Linear

section LinearMarking

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank

theorem burnsideF4h_cl_L3 (p exponent : ℕ) (H : Type) [Group H]
    (marking : ChF.ClassicalRoots.Marking .L3 p exponent H) :
    ChF.IsLieParabolics p (⊤ : Subgroup H) marking.borel (marking.parabolic false)
      (marking.parabolic true) := by
  set K := marking.field
  haveI : Fact p.Prime := ⟨marking.prime⟩
  have hK : Nat.card K = p ^ exponent := by simpa using marking.field_card
  haveI : CharP K p := burnsideF4h_cl_charP hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  let s : Matrix.SpecialLinearGroup (Fin 3) K ≃* StatedSL 3 K :=
    specialLinearGroupEquivStatedSL 3 K
  have keym : ∀ (b : Bool) (x : StatedSL 3 K),
      x ∈ ChF.ClassicalRoots.nativeParabolic .L3 (p ^ exponent) K marking.basis b ↔
        s.symm x ∈ stabilizer (flagSpace 3 K (if b then 2 else 1)) := by
    intro b x
    rw [hbasis]
    have h1 : x ∈ ChF.ClassicalRoots.nativeParabolic .L3 (p ^ exponent) K 1 b ↔
        (x : GL (ChF.ClassicalRoots.Coord .L3) K) ∈ ChF.ClassicalRoots.rawStabilizer
          ((fun vector => ((1 : GL (ChF.ClassicalRoots.Coord .L3) K) :
            Matrix (ChF.ClassicalRoots.Coord .L3) (ChF.ClassicalRoots.Coord .L3) K).mulVec
              vector) ''
            ChF.ClassicalRoots.coordinateSpace (if b then ChF.ClassicalRoots.flagTwo .L3
              else ChF.ClassicalRoots.flagOne .L3)) :=
      Iff.rfl
    have hxu : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((s.symm x : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      conv_lhs => rw [← s.apply_symm_apply x]
      rfl
    rw [h1, burnsideF4h_cl_mem_rawStabilizer, mem_stabilizer,
      burnsideF4h_cl_map_eq_iff _
        (C := (((s.symm x)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
        (coe_inv_mul_coe _)
        (by rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one])]
    simp only [Units.val_one, Matrix.one_mulVec, Set.image_id']
    rw [hxu]
    cases b
    · simp only [Bool.false_eq_true, if_false, ChF.ClassicalRoots.flagOne]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sl_coordinateSpace _).1, (burnsideF4h_cl_sl_coordinateSpace _).1]
    · simp only [if_true, ChF.ClassicalRoots.flagTwo]
      exact forall_congr' fun v => by
        rw [(burnsideF4h_cl_sl_coordinateSpace _).2, (burnsideF4h_cl_sl_coordinateSpace _).2]
  let φ : projectiveSL 3 K ≃* StatedProj (StatedSL 3 K) :=
    QuotientGroup.congr (scalars 3 K) ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) s
      (by rw [scalars_eq_center]; exact map_center_eq_statedScalars 3 K)
  let e : projectiveSL 3 K ≃* H := φ.trans marking.identification
  have he : ∀ x : StatedSL 3 K, e (proj 3 K (s.symm x)) = marking.transport x := fun x =>
    congrArg marking.transport (s.apply_symm_apply x)
  have hpar : ∀ b : Bool, marking.parabolic b =
      (projStabilizer (flagSpace 3 K (if b then 2 else 1))).map e.toMonoidHom := by
    intro b
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨proj 3 K (s.symm x), ⟨s.symm x, (keym b x).1 hx, rfl⟩, he x⟩
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨s u, (keym b (s u)).2 (by rwa [MulEquiv.symm_apply_apply]), ?_⟩
      have := he (s u)
      rw [MulEquiv.symm_apply_apply] at this
      exact this.symm
  have hbor : marking.borel = (projUpperTriangular 3 K).map e.toMonoidHom := by
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : s.symm x ∈ stabilizer (flagSpace 3 K 1) ⊓ stabilizer (flagSpace 3 K 2) :=
        ⟨(keym false x).1 (Subgroup.mem_inf.1 hx).1, (keym true x).1 (Subgroup.mem_inf.1 hx).2⟩
      rw [burnsideF4h_cl_sl_stab_inf] at hx'
      exact ⟨proj 3 K (s.symm x), ⟨s.symm x, hx', rfl⟩, he x⟩
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      rw [← burnsideF4h_cl_sl_stab_inf] at hu
      refine ⟨s u, Subgroup.mem_inf.2 ⟨(keym false (s u)).2 (by
        rw [MulEquiv.symm_apply_apply]; exact (Subgroup.mem_inf.1 hu).1),
        (keym true (s u)).2 (by
        rw [MulEquiv.symm_apply_apply]; exact (Subgroup.mem_inf.1 hu).2)⟩, ?_⟩
      have := he (s u)
      rw [MulEquiv.symm_apply_apply] at this
      exact this.symm
  have h := burnsideF4h_cl_isLieParabolics_map e (burnsideF4h_cl_sl_isLieParabolics K p)
  rw [hbor, hpar false, hpar true]
  simpa using h

end LinearMarking

end PartBurnsideF4hCl

section PartBurnsideF4hClU_dedup

section HypParabolics

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {ε : ℕ}

theorem burnsideF4h_clu_isoStabilizer_inf (h : UnitaryFieldData p f K) :
    isoStabilizer h 2 ε (hypFlag h 2 ε 1) ⊓ isoStabilizer h 2 ε (hypFlag h 2 ε 2) =
      hypBorel h 2 ε := by
  ext g
  rw [Subgroup.mem_inf, mem_isoStabilizer, mem_isoStabilizer, mem_hypBorel]
  constructor
  · rintro ⟨h1, h2⟩ i hi1 hi2
    interval_cases i
    · exact h1
    · exact h2
  · intro hg
    exact ⟨hg 1 le_rfl (by norm_num), hg 2 (by norm_num) le_rfl⟩

theorem burnsideF4h_clu_projIsoStabilizer_inf (h : UnitaryFieldData p f K) :
    projIsoStabilizer h 2 ε (hypFlag h 2 ε 1) ⊓ projIsoStabilizer h 2 ε (hypFlag h 2 ε 2) =
      hypProjBorel h 2 ε := by
  rw [projIsoStabilizer, projIsoStabilizer, ← burnsideF4h_cl_map_inf_of_ker_le]
  · rw [burnsideF4h_clu_isoStabilizer_inf]
    rfl
  · rw [ker_hypProj]
    exact hypScalars_le_isoStabilizer _

theorem burnsideF4h_clu_hyp_isLieParabolics (h : UnitaryFieldData p f K) (hε : ε ≤ 1) :
    ChF.IsLieParabolics p (⊤ : Subgroup (hypPSU h 2 ε)) (hypProjBorel h 2 ε)
      (projIsoStabilizer h 2 ε (hypFlag h 2 ε 1))
      (projIsoStabilizer h 2 ε (hypFlag h 2 ε 2)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  haveI := h.finite
  obtain ⟨-, -, -, -, ⟨U₀, hU₀⟩, -, -⟩ :=
    unitary_order_and_Sylow h (r := 2) (ε := ε) (by norm_num) hε
  have hF : ∀ d, d ≤ 2 → hypFlag h 2 ε d = posFlag 2 ε K d := fun d hd =>
    hypFlag_eq_posFlag h hε (by omega)
  have hiso : ∀ d, d ≤ 2 → ∀ x ∈ hypFlag h 2 ε d, ∀ y ∈ hypFlag h 2 ε d,
      hypForm h 2 ε x y = 0 := by
    intro d hd
    rw [hF d hd]
    exact posFlag_isotropic h hd
  have hne0 : ∀ d, 1 ≤ d → d ≤ 2 → hypFlag h 2 ε d ≠ ⊥ := by
    intro d hd1 hd2 h0
    have := finrank_posFlag (K := K) (r := 2) (ε := ε) hd2
    rw [← hF d hd2, h0, finrank_bot] at this
    omega
  refine burnsideF4h_cl_isLieParabolics_top_of (S := hypProjUnitriangular h 2 ε) ?_ ?_
    (normalizer_hypProjUnitriangular h (by norm_num) hε) ?_
    (burnsideF4h_clu_projIsoStabilizer_inf h)
    (isCoatom_projIsoStabilizer_hypFlag h (by norm_num) hε le_rfl (by norm_num))
    (isCoatom_projIsoStabilizer_hypFlag h (by norm_num) hε (by norm_num) le_rfl) ?_
  · rw [← hU₀]
    exact U₀.isPGroup'
  · rw [← hU₀]
    exact U₀.not_dvd_index
  · intro heq
    have hW := (unitary_maximal_parabolics h (r := 2) (ε := ε) (by norm_num) hε).2.2
      ⟨hne0 1 le_rfl (by norm_num), hiso 1 (by norm_num)⟩
      ⟨hne0 2 (by norm_num) le_rfl, hiso 2 le_rfl⟩ heq
    have h1 := finrank_posFlag (K := K) (r := 2) (ε := ε) (d := 1) (by norm_num)
    have h2 := finrank_posFlag (K := K) (r := 2) (ε := ε) (d := 2) le_rfl
    rw [← hF 1 (by norm_num), hW, hF 2 le_rfl, h2] at h1
    omega
  · intro Q hBQ hQ
    obtain ⟨d, hd1, hd2, rfl⟩ := eq_projIsoStabilizer_of_isCoatom h (by norm_num) hε hQ hBQ
    interval_cases d
    · exact Or.inl rfl
    · exact Or.inr rfl

end HypParabolics

section Transport

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] noncomputable def burnsideF4h_clu_R (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) :
    Matrix (Fin (2 * r + ε)) (HypIndex r ε) K :=
  B.submatrix id fullPosEquiv

theorem burnsideF4h_clu_R_mulVec (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    (w : HypIndex r ε → K) :
    burnsideF4h_clu_R B *ᵥ w = B *ᵥ (w ∘ fullPosEquiv.symm) :=
  submatrix_mulVec_equiv B w id fullPosEquiv

theorem burnsideF4h_clu_isHypTransport (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    (hB : (B.map h.bar)ᵀ * B = ChF.ClassicalRoots.hermitianGram (2 * r + ε) K) :
    IsHypTransport h (burnsideF4h_clu_R B) := by
  ext a b
  have h1 : (((burnsideF4h_clu_R B).map h.bar)ᵀ * burnsideF4h_clu_R B) a b =
      ((B.map h.bar)ᵀ * B) (fullPosEquiv a) (fullPosEquiv b) := by
    simp [Matrix.mul_apply, burnsideF4h_clu_R]
  show (((burnsideF4h_clu_R B).map h.bar)ᵀ * burnsideF4h_clu_R B) a b = hypGram r ε K a b
  rw [h1, hB, hypGram_apply]
  unfold ChF.ClassicalRoots.hermitianGram
  have key : ((fullPosEquiv a : Fin (2 * r + ε)) : ℕ) + (fullPosEquiv b : Fin (2 * r + ε)) + 1 =
      2 * r + ε ↔ b = hypPartner a := by
    rw [fullPosEquiv_apply, fullPosEquiv_apply]
    constructor
    · intro hab
      apply fullPos_injective
      rw [fullPos_hypPartner hε]
      omega
    · rintro rfl
      rw [fullPos_hypPartner hε]
      have := fullPos_lt a
      omega
  split_ifs with hc hd hd
  · rfl
  · exact absurd (key.1 hc) hd
  · exact absurd (key.2 hd) hc
  · rfl

theorem burnsideF4h_clu_smul_eq_iff {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K)
    (W : Submodule K (ι → K)) :
    g • W = W ↔ ∀ v, (g : Matrix ι ι K) *ᵥ v ∈ W ↔ v ∈ W := by
  constructor
  · intro hgW v
    constructor
    · intro hgv
      rw [← hgW] at hgv
      obtain ⟨b, hb, hbv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ W).mp hgv
      have : b = v := by
        have h1 : (g : Matrix ι ι K) *ᵥ b = (g : Matrix ι ι K) *ᵥ v := hbv
        have h2 := congrArg (fun x => ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) h1
        simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_mulVec] using h2
      rw [← this]
      exact hb
    · intro hv
      have : g • v ∈ g • W := Submodule.smul_mem_pointwise_smul v g W hv
      rw [hgW] at this
      exact this
  · intro H
    refine smul_eq_of_mulVec_mem (fun v hv => (H v).2 hv) (fun v hv => ?_)
    refine (H _).1 ?_
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    exact hv

variable (h : UnitaryFieldData p f K) {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}

theorem burnsideF4h_clu_mem_image_iff (hR : IsHypTransport h R) (W : Set (HypIndex r ε → K))
    (v : Fin (2 * r + ε) → K) :
    v ∈ (fun w => R *ᵥ w) '' W ↔ transportInv h R *ᵥ v ∈ W := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mulVec_mulVec, transportInv_mul hR, one_mulVec]
    exact hw
  · intro hv
    exact ⟨_, hv, by
      show R *ᵥ (transportInv h R *ᵥ v) = v
      rw [mulVec_mulVec, mul_transportInv hR, one_mulVec]⟩

theorem burnsideF4h_clu_transportInv_mulVec (hR : IsHypTransport h R) (g : hypSU h r ε)
    (v : Fin (2 * r + ε) → K) :
    transportInv h R *ᵥ (((hypTransport h hR g : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v) =
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        (transportInv h R *ᵥ v) := by
  rw [coe_hypTransport, mulVec_mulVec, mulVec_mulVec]
  congr 1
  rw [show transportInv h R * (R * ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) * transportInv h R) =
    (transportInv h R * R) * ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) * transportInv h R by
    simp only [Matrix.mul_assoc], transportInv_mul hR, Matrix.one_mul]

theorem burnsideF4h_clu_stab_iff (hR : IsHypTransport h R) (W : Set (HypIndex r ε → K))
    (g : hypSU h r ε) :
    (∀ v, ((hypTransport h hR g : GL (Fin (2 * r + ε)) K) :
        Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v ∈ (fun w => R *ᵥ w) '' W ↔
          v ∈ (fun w => R *ᵥ w) '' W) ↔
      ∀ w, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈ W ↔
        w ∈ W := by
  simp only [burnsideF4h_clu_mem_image_iff h hR, burnsideF4h_clu_transportInv_mulVec h hR]
  constructor
  · intro H w
    have e : transportInv h R *ᵥ (R *ᵥ w) = w := by
      rw [mulVec_mulVec, transportInv_mul hR, one_mulVec]
    have := H (R *ᵥ w)
    rwa [e] at this
  · intro H v
    exact H _

theorem burnsideF4h_clu_image_posFlag (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) (i : ℕ)
    (S : Set (Fin (2 * r + ε))) (hS : ∀ j : Fin (2 * r + ε), j ∉ S ↔ i ≤ (j : ℕ))
    (v : Fin (2 * r + ε) → K) :
    v ∈ (fun w => burnsideF4h_clu_R B *ᵥ w) ''
        ((posFlag r ε K i : Submodule K (HypIndex r ε → K)) : Set (HypIndex r ε → K)) ↔
      v ∈ (fun u => B *ᵥ u) '' {u : Fin (2 * r + ε) → K | ∀ j, j ∉ S → u j = 0} := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w ∘ fullPosEquiv.symm, fun j hj => ?_, (burnsideF4h_clu_R_mulVec B w).symm⟩
    exact hw (fullPosEquiv.symm j) (by rw [fullPos_fullPosEquiv_symm]; exact (hS j).1 hj)
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u ∘ fullPosEquiv, fun a ha => ?_, ?_⟩
    · exact hu _ ((hS _).2 (by rw [fullPosEquiv_apply]; exact ha))
    · show burnsideF4h_clu_R B *ᵥ (u ∘ fullPosEquiv) = B *ᵥ u
      rw [burnsideF4h_clu_R_mulVec]
      congr 1
      ext j
      simp

theorem burnsideF4h_clu_mem_isoStabilizer_iff (hε : ε ≤ 1)
    (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    (hR : IsHypTransport h (burnsideF4h_clu_R B)) (i : ℕ) (hi : i ≤ 2 * r + ε)
    (S : Set (Fin (2 * r + ε))) (hS : ∀ j : Fin (2 * r + ε), j ∉ S ↔ i ≤ (j : ℕ))
    (g : hypSU h r ε) :
    g ∈ isoStabilizer h r ε (hypFlag h r ε i) ↔
      ∀ v : Fin (2 * r + ε) → K, ((hypTransport h hR g : GL (Fin (2 * r + ε)) K) :
          Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v ∈
            (fun u => B *ᵥ u) '' {u : Fin (2 * r + ε) → K | ∀ j, j ∉ S → u j = 0} ↔
          v ∈ (fun u => B *ᵥ u) '' {u : Fin (2 * r + ε) → K | ∀ j, j ∉ S → u j = 0} := by
  rw [mem_isoStabilizer, hypFlag_eq_posFlag h hε hi, Subgroup.smul_def,
    burnsideF4h_clu_smul_eq_iff]
  have := burnsideF4h_clu_stab_iff h hR
    ((posFlag r ε K i : Submodule K (HypIndex r ε → K)) : Set (HypIndex r ε → K)) g
  simp only [burnsideF4h_clu_image_posFlag B i S hS, SetLike.mem_coe] at this
  exact this.symm

theorem burnsideF4h_clu_rawStabilizer_comap (hε : ε ≤ 1)
    (B : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    (hR : IsHypTransport h (burnsideF4h_clu_R B)) (i : ℕ) (hi : i ≤ 2 * r + ε)
    (S : Set (Fin (2 * r + ε))) (hS : ∀ j : Fin (2 * r + ε), j ∉ S ↔ i ≤ (j : ℕ)) :
    (ChF.ClassicalRoots.rawStabilizer ((fun v => B *ᵥ v) ''
        ChF.ClassicalRoots.coordinateSpace S)).comap (unitarySU p f K (2 * r + ε)).subtype =
      (isoStabilizer h r ε (hypFlag h r ε i)).map (hypTransport h hR).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have key := burnsideF4h_clu_mem_isoStabilizer_iff h hε B hR i hi S hS
    ((hypTransport h hR).symm x)
  rw [MulEquiv.apply_symm_apply] at key
  rw [Subgroup.mem_comap, Subgroup.coe_subtype, burnsideF4h_cl_mem_rawStabilizer]
  exact key.symm

end Transport

section RootGroup

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem burnsideF4h_clu_stdHermForm_col (h : UnitaryFieldData p f K)
    (B : Matrix (Fin n) (Fin n) K)
    (hB : (B.map h.bar)ᵀ * B = ChF.ClassicalRoots.hermitianGram n K)
    (i₀ j₀ : Fin n) (hi₀ : (i₀ : ℕ) = 0) (hj₀ : (j₀ : ℕ) + 1 = n) (w : Fin n → K) :
    stdHermForm h n (fun i => B i i₀) (B *ᵥ w) = w j₀ := by
  have e1 : stdHermForm h n (fun i => B i i₀) (B *ᵥ w) = ((B.map h.bar)ᵀ *ᵥ (B *ᵥ w)) i₀ := by
    simp [stdHermForm_apply, mulVec, dotProduct]
  rw [e1, mulVec_mulVec, hB]
  simp only [mulVec, dotProduct, ChF.ClassicalRoots.hermitianGram, hi₀, zero_add]
  rw [Finset.sum_eq_single j₀]
  · simp [hj₀]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro hb'
    exact hb (Fin.ext (by omega))
  · simp

theorem burnsideF4h_clu_mulVec_single (B : Matrix (Fin n) (Fin n) K) (i₀ : Fin n) (c : K) :
    B *ᵥ Pi.single i₀ c = c • (fun i => B i i₀) := by
  ext i
  simp [mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem burnsideF4h_clu_mulVecLin_root (h : UnitaryFieldData p f K) (B : GL (Fin n) K)
    (hB : ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) =
      ChF.ClassicalRoots.hermitianGram n K)
    (i₀ j₀ : Fin n) (hi₀ : (i₀ : ℕ) = 0) (hj₀ : (j₀ : ℕ) + 1 = n) (t : K) :
    mulVecLin ((B : Matrix (Fin n) (Fin n) K) * (1 + ChF.ClassicalRoots.matrixUnit i₀ j₀ t) *
        ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      hermTransvection (stdHermForm h n) (fun i => (B : Matrix (Fin n) (Fin n) K) i i₀) t := by
  apply LinearMap.ext
  intro v
  rw [mulVecLin_apply, hermTransvection_apply]
  set w := ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v with hw
  have hv : (B : Matrix (Fin n) (Fin n) K) *ᵥ w = v := by
    rw [hw, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hE : ChF.ClassicalRoots.matrixUnit i₀ j₀ t *ᵥ w = Pi.single i₀ (t * w j₀) := by
    ext k
    by_cases hk : k = i₀
    · subst hk
      simp [ChF.ClassicalRoots.matrixUnit, mulVec, dotProduct]
    · simp [ChF.ClassicalRoots.matrixUnit, mulVec, dotProduct, hk]
  rw [← mulVec_mulVec, ← mulVec_mulVec, add_mulVec, one_mulVec, hE, mulVec_add, hv,
    burnsideF4h_clu_mulVec_single, ← hv, burnsideF4h_clu_stdHermForm_col h _ hB i₀ j₀ hi₀ hj₀ w]

theorem burnsideF4h_clu_col_isotropic (h : UnitaryFieldData p f K) (B : Matrix (Fin n) (Fin n) K)
    (hB : (B.map h.bar)ᵀ * B = ChF.ClassicalRoots.hermitianGram n K)
    (i₀ j₀ : Fin n) (hi₀ : (i₀ : ℕ) = 0) (hj₀ : (j₀ : ℕ) + 1 = n) (hn : 2 ≤ n) :
    stdHermForm h n (fun i => B i i₀) (fun i => B i i₀) = 0 := by
  have e := burnsideF4h_clu_stdHermForm_col h B hB i₀ j₀ hi₀ hj₀ (Pi.single i₀ 1)
  rw [burnsideF4h_clu_mulVec_single, one_smul] at e
  rw [e, Pi.single_apply, if_neg]
  intro hji
  have := congrArg Fin.val hji
  omega

theorem burnsideF4h_clu_span_mem_isotropicLines (h : UnitaryFieldData p f K) (B : GL (Fin n) K)
    (hB : ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) =
      ChF.ClassicalRoots.hermitianGram n K)
    (i₀ j₀ : Fin n) (hi₀ : (i₀ : ℕ) = 0) (hj₀ : (j₀ : ℕ) + 1 = n) (hn : 2 ≤ n) :
    (K ∙ (fun i => (B : Matrix (Fin n) (Fin n) K) i i₀)) ∈ isotropicLines h n := by
  have hb0 : (fun i => (B : Matrix (Fin n) (Fin n) K) i i₀) ≠ 0 := by
    intro h0
    have e : (B : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i₀ 1 = 0 := by
      rw [burnsideF4h_clu_mulVec_single, one_smul, h0]
    have e2 := congrArg (fun x => ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) e
    simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
      mulVec_zero] at e2
    have := congrFun e2 i₀
    simp at this
  refine ⟨finrank_span_singleton hb0, fun a ha => ?_⟩
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp ha
  rw [LinearMap.map_smulₛₗ₂, map_smul,
    burnsideF4h_clu_col_isotropic h _ hB i₀ j₀ hi₀ hj₀ hn, smul_zero, smul_zero]

theorem burnsideF4h_clu_closure_root_eq (h : UnitaryFieldData p f K) (B : GL (Fin n) K)
    (hB : ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) =
      ChF.ClassicalRoots.hermitianGram n K)
    (i₀ j₀ : Fin n) (hi₀ : (i₀ : ℕ) = 0) (hj₀ : (j₀ : ℕ) + 1 = n) (hn : 2 ≤ n) :
    Subgroup.closure {x : unitarySU p f K n | ∃ t : K, t + t ^ (p ^ f) = 0 ∧
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (B : Matrix (Fin n) (Fin n) K) * (1 + ChF.ClassicalRoots.matrixUnit i₀ j₀ t) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} =
      isotropicTransvectionGroup h n (K ∙ (fun i => (B : Matrix (Fin n) (Fin n) K) i i₀)) := by
  have htr : ∀ t : K, t + t ^ (p ^ f) = 0 ↔ t ∈ h.traceZero := fun t => by
    rw [h.mem_traceZero, UnitaryFieldData.trace, h.bar_apply]
  unfold isotropicTransvectionGroup
  congr 1
  ext x
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨_, Submodule.mem_span_singleton_self _, t, (htr t).1 ht, ?_⟩
    rw [hx]
    exact burnsideF4h_clu_mulVecLin_root h B hB i₀ j₀ hi₀ hj₀ t
  · rintro ⟨a, ha, c, hc, hx⟩
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have hiso := burnsideF4h_clu_col_isotropic h _ hB i₀ j₀ hi₀ hj₀ hn
    have hscale := (hermitian_unitary_transvection h (stdHermForm_isSymm h n) hiso).2.2.2.2.2
      c hc μ
    refine ⟨h.norm μ * c, (htr _).2 (norm_mul_mem_traceZero h μ hc), ?_⟩
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', Matrix.toLin'_apply', hx, hscale,
      burnsideF4h_clu_mulVecLin_root h B hB i₀ j₀ hi₀ hj₀]

theorem burnsideF4h_clu_image_coordinateSpace (B : Matrix (Fin n) (Fin n) K) (i₀ : Fin n) :
    (fun v => B *ᵥ v) '' ChF.ClassicalRoots.coordinateSpace ({i₀} : Set (Fin n)) =
      ((K ∙ (fun i => B i i₀) : Submodule K (Fin n → K)) : Set (Fin n → K)) := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : u = Pi.single i₀ (u i₀) := by
      ext k
      by_cases hk : k = i₀
      · subst hk
        simp
      · rw [Pi.single_apply, if_neg hk]
        exact hu k hk
    change B *ᵥ u ∈ ((K ∙ (fun i => B i i₀) : Submodule K (Fin n → K)) : Set (Fin n → K))
    rw [hu', burnsideF4h_clu_mulVec_single]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hv
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨Pi.single i₀ μ, fun k hk => ?_, burnsideF4h_clu_mulVec_single B i₀ μ⟩
    rw [Pi.single_apply, if_neg (show ¬ k = i₀ from hk)]

theorem burnsideF4h_clu_rawStabilizer_le_normalizer (h : UnitaryFieldData p f K) (B : GL (Fin n) K)
    (hB : ((B : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (B : Matrix (Fin n) (Fin n) K) =
      ChF.ClassicalRoots.hermitianGram n K)
    (i₀ j₀ : Fin n) (hi₀ : (i₀ : ℕ) = 0) (hj₀ : (j₀ : ℕ) + 1 = n) (hn : 2 ≤ n) :
    (ChF.ClassicalRoots.rawStabilizer ((fun v => (B : Matrix (Fin n) (Fin n) K) *ᵥ v) ''
        ChF.ClassicalRoots.coordinateSpace ({i₀} : Set (Fin n)))).comap
        (unitarySU p f K n).subtype ≤
      Subgroup.normalizer ((Subgroup.closure {x : unitarySU p f K n | ∃ t : K,
        t + t ^ (p ^ f) = 0 ∧ ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (B : Matrix (Fin n) (Fin n) K) * (1 + ChF.ClassicalRoots.matrixUnit i₀ j₀ t) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} : Subgroup (unitarySU p f K n)) :
        Set (unitarySU p f K n)) := by
  intro x hx
  have hL := burnsideF4h_clu_span_mem_isotropicLines h B hB i₀ j₀ hi₀ hj₀ hn
  rw [burnsideF4h_clu_closure_root_eq h B hB i₀ j₀ hi₀ hj₀ hn]
  obtain ⟨-, -, hfix, hnorm⟩ := unitary_point_conjugation h 1 hL
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hfix).mp hnorm ?_
  rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, burnsideF4h_clu_smul_eq_iff]
  have hx' := (burnsideF4h_cl_mem_rawStabilizer _ _).mp (Subgroup.mem_comap.mp hx)
  rw [burnsideF4h_clu_image_coordinateSpace] at hx'
  exact hx'

end RootGroup

section U4

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ASVolI.ChF.ClassicalRoots

variable {p e : ℕ} {H : Type} [Group H] (marking : Marking .U4 p e H)

theorem burnsideF4h_clu_U4_fieldData : UnitaryFieldData p e marking.field :=
  ⟨marking.prime, marking.exponent_pos, by
    have := marking.field_card
    simp only [true_or, if_true] at this
    rw [this, ← pow_mul, mul_comm]⟩

theorem burnsideF4h_clu_U4_gram :
    ((marking.basis : Matrix (Fin 4) (Fin 4) marking.field).map
        (burnsideF4h_clu_U4_fieldData marking).bar)ᵀ *
      (marking.basis : Matrix (Fin 4) (Fin 4) marking.field) = hermitianGram 4 marking.field := by
  have hbar : (⇑(burnsideF4h_clu_U4_fieldData marking).bar : marking.field → marking.field) =
      fun c => c ^ p ^ e := funext (burnsideF4h_clu_U4_fieldData marking).bar_apply
  rw [hbar]
  exact marking.basis_compatible

theorem burnsideF4h_clu_U4_isHypTransport :
    IsHypTransport (burnsideF4h_clu_U4_fieldData marking)
      (burnsideF4h_clu_R (r := 2) (ε := 0)
        (marking.basis : Matrix (Fin 4) (Fin 4) marking.field)) :=
  burnsideF4h_clu_isHypTransport _ (by norm_num) _ (burnsideF4h_clu_U4_gram marking)

noncomputable def burnsideF4h_clu_U4_T :
    hypSU (burnsideF4h_clu_U4_fieldData marking) 2 0 ≃* nativeGroup .U4 (p ^ e) marking.field :=
  hypTransport (burnsideF4h_clu_U4_fieldData marking) (burnsideF4h_clu_U4_isHypTransport marking)

noncomputable def burnsideF4h_clu_U4_Phi : hypPSU (burnsideF4h_clu_U4_fieldData marking) 2 0 ≃* H :=
  (hypPSUEquivStatedProj (burnsideF4h_clu_U4_fieldData marking)
    (burnsideF4h_clu_U4_isHypTransport marking) (by norm_num)).trans marking.identification

theorem burnsideF4h_clu_U4_comp :
    marking.transport.comp (burnsideF4h_clu_U4_T marking).toMonoidHom =
      (burnsideF4h_clu_U4_Phi marking).toMonoidHom.comp
        (hypProj (burnsideF4h_clu_U4_fieldData marking) 2 0) := by
  ext g
  show marking.identification (projectiveMap .U4 (p ^ e) marking.field
      (burnsideF4h_clu_U4_T marking g)) =
    marking.identification (hypPSUEquivStatedProj (burnsideF4h_clu_U4_fieldData marking)
      (burnsideF4h_clu_U4_isHypTransport marking) (by norm_num)
      (hypProj (burnsideF4h_clu_U4_fieldData marking) 2 0 g))
  rw [hypPSUEquivStatedProj_hypProj]
  rfl

theorem burnsideF4h_clu_U4_nativeParabolic (second : Bool) :
    nativeParabolic .U4 (p ^ e) marking.field marking.basis second =
      (isoStabilizer (burnsideF4h_clu_U4_fieldData marking) 2 0
        (hypFlag (burnsideF4h_clu_U4_fieldData marking) 2 0 (if second then 2 else 1))).map
        (burnsideF4h_clu_U4_T marking).toMonoidHom := by
  cases second
  · exact burnsideF4h_clu_rawStabilizer_comap (burnsideF4h_clu_U4_fieldData marking)
      (by norm_num) _ (burnsideF4h_clu_U4_isHypTransport marking) 1 (by norm_num) (flagOne .U4)
      (by intro j; fin_cases j <;> simp [flagOne])
  · exact burnsideF4h_clu_rawStabilizer_comap (burnsideF4h_clu_U4_fieldData marking)
      (by norm_num) _ (burnsideF4h_clu_U4_isHypTransport marking) 2 (by norm_num) (flagTwo .U4)
      (by intro j; fin_cases j <;> simp [flagTwo])

theorem burnsideF4h_clu_U4_parabolic (second : Bool) :
    marking.parabolic second =
      (projIsoStabilizer (burnsideF4h_clu_U4_fieldData marking) 2 0
        (hypFlag (burnsideF4h_clu_U4_fieldData marking) 2 0 (if second then 2 else 1))).map
        (burnsideF4h_clu_U4_Phi marking).toMonoidHom := by
  show (nativeParabolic .U4 (p ^ e) marking.field marking.basis second).map marking.transport = _
  rw [burnsideF4h_clu_U4_nativeParabolic, Subgroup.map_map, burnsideF4h_clu_U4_comp,
    projIsoStabilizer, Subgroup.map_map]

theorem burnsideF4h_clu_U4_borel :
    marking.borel = (hypProjBorel (burnsideF4h_clu_U4_fieldData marking) 2 0).map
      (burnsideF4h_clu_U4_Phi marking).toMonoidHom := by
  show (nativeParabolic .U4 (p ^ e) marking.field marking.basis false ⊓
    nativeParabolic .U4 (p ^ e) marking.field marking.basis true).map marking.transport = _
  rw [burnsideF4h_clu_U4_nativeParabolic, burnsideF4h_clu_U4_nativeParabolic,
    ← Subgroup.map_inf_eq _ _ _ (burnsideF4h_clu_U4_T marking).injective]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [burnsideF4h_clu_isoStabilizer_inf, Subgroup.map_map, burnsideF4h_clu_U4_comp,
    hypProjBorel, Subgroup.map_map]

theorem burnsideF4h_clu_U4_nativeRoot :
    nativeRoot .U4 (p ^ e) marking.basis .longOne false =
      Subgroup.closure {x : nativeGroup .U4 (p ^ e) marking.field | ∃ t : marking.field,
        t + t ^ (p ^ e) = 0 ∧
        ((x : GL (Coord .U4) marking.field) : Matrix (Fin 4) (Fin 4) marking.field) =
          (marking.basis : Matrix (Fin 4) (Fin 4) marking.field) * (1 + matrixUnit 0 3 t) *
            ((marking.basis⁻¹ : GL (Coord .U4) marking.field) :
              Matrix (Fin 4) (Fin 4) marking.field)} := by
  unfold nativeRoot
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, RootAllowed, ParameterAllowed, markedMatrix, positiveMatrix,
    unitaryRootFour, Bool.false_eq_true, if_false]
  constructor
  · rintro ⟨-, t, c, ht, hx⟩
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨by simp, t, 0, ht, hx⟩

theorem burnsideF4h_clu_U4_normalizer :
    marking.parabolic false ≤ Subgroup.normalizer (marking.root .longOne false : Set H) := by
  have hle : nativeParabolic .U4 (p ^ e) marking.field marking.basis false ≤
      Subgroup.normalizer (nativeRoot .U4 (p ^ e) marking.basis .longOne false :
        Set (nativeGroup .U4 (p ^ e) marking.field)) := by
    rw [burnsideF4h_clu_U4_nativeRoot]
    exact burnsideF4h_clu_rawStabilizer_le_normalizer (burnsideF4h_clu_U4_fieldData marking)
      marking.basis (burnsideF4h_clu_U4_gram marking) 0 3 rfl rfl (by norm_num)
  exact (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map _)

end U4

section U5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ASVolI.ChF.ClassicalRoots

variable {p e : ℕ} {H : Type} [Group H] (marking : Marking .U5 p e H)

theorem burnsideF4h_clu_U5_fieldData : UnitaryFieldData p e marking.field :=
  ⟨marking.prime, marking.exponent_pos, by
    have := marking.field_card
    simp only [or_true, if_true] at this
    rw [this, ← pow_mul, mul_comm]⟩

theorem burnsideF4h_clu_U5_gram :
    ((marking.basis : Matrix (Fin 5) (Fin 5) marking.field).map
        (burnsideF4h_clu_U5_fieldData marking).bar)ᵀ *
      (marking.basis : Matrix (Fin 5) (Fin 5) marking.field) = hermitianGram 5 marking.field := by
  have hbar : (⇑(burnsideF4h_clu_U5_fieldData marking).bar : marking.field → marking.field) =
      fun c => c ^ p ^ e := funext (burnsideF4h_clu_U5_fieldData marking).bar_apply
  rw [hbar]
  exact marking.basis_compatible

theorem burnsideF4h_clu_U5_isHypTransport :
    IsHypTransport (burnsideF4h_clu_U5_fieldData marking)
      (burnsideF4h_clu_R (r := 2) (ε := 1)
        (marking.basis : Matrix (Fin 5) (Fin 5) marking.field)) :=
  burnsideF4h_clu_isHypTransport _ (by norm_num) _ (burnsideF4h_clu_U5_gram marking)

noncomputable def burnsideF4h_clu_U5_T :
    hypSU (burnsideF4h_clu_U5_fieldData marking) 2 1 ≃* nativeGroup .U5 (p ^ e) marking.field :=
  hypTransport (burnsideF4h_clu_U5_fieldData marking) (burnsideF4h_clu_U5_isHypTransport marking)

noncomputable def burnsideF4h_clu_U5_Phi : hypPSU (burnsideF4h_clu_U5_fieldData marking) 2 1 ≃* H :=
  (hypPSUEquivStatedProj (burnsideF4h_clu_U5_fieldData marking)
    (burnsideF4h_clu_U5_isHypTransport marking) (by norm_num)).trans marking.identification

theorem burnsideF4h_clu_U5_comp :
    marking.transport.comp (burnsideF4h_clu_U5_T marking).toMonoidHom =
      (burnsideF4h_clu_U5_Phi marking).toMonoidHom.comp
        (hypProj (burnsideF4h_clu_U5_fieldData marking) 2 1) := by
  ext g
  show marking.identification (projectiveMap .U5 (p ^ e) marking.field
      (burnsideF4h_clu_U5_T marking g)) =
    marking.identification (hypPSUEquivStatedProj (burnsideF4h_clu_U5_fieldData marking)
      (burnsideF4h_clu_U5_isHypTransport marking) (by norm_num)
      (hypProj (burnsideF4h_clu_U5_fieldData marking) 2 1 g))
  rw [hypPSUEquivStatedProj_hypProj]
  rfl

theorem burnsideF4h_clu_U5_nativeParabolic (second : Bool) :
    nativeParabolic .U5 (p ^ e) marking.field marking.basis second =
      (isoStabilizer (burnsideF4h_clu_U5_fieldData marking) 2 1
        (hypFlag (burnsideF4h_clu_U5_fieldData marking) 2 1 (if second then 2 else 1))).map
        (burnsideF4h_clu_U5_T marking).toMonoidHom := by
  cases second
  · exact burnsideF4h_clu_rawStabilizer_comap (burnsideF4h_clu_U5_fieldData marking)
      (by norm_num) _ (burnsideF4h_clu_U5_isHypTransport marking) 1 (by norm_num) (flagOne .U5)
      (by intro j; fin_cases j <;> simp [flagOne])
  · exact burnsideF4h_clu_rawStabilizer_comap (burnsideF4h_clu_U5_fieldData marking)
      (by norm_num) _ (burnsideF4h_clu_U5_isHypTransport marking) 2 (by norm_num) (flagTwo .U5)
      (by intro j; fin_cases j <;> simp [flagTwo])

theorem burnsideF4h_clu_U5_parabolic (second : Bool) :
    marking.parabolic second =
      (projIsoStabilizer (burnsideF4h_clu_U5_fieldData marking) 2 1
        (hypFlag (burnsideF4h_clu_U5_fieldData marking) 2 1 (if second then 2 else 1))).map
        (burnsideF4h_clu_U5_Phi marking).toMonoidHom := by
  show (nativeParabolic .U5 (p ^ e) marking.field marking.basis second).map marking.transport = _
  rw [burnsideF4h_clu_U5_nativeParabolic, Subgroup.map_map, burnsideF4h_clu_U5_comp,
    projIsoStabilizer, Subgroup.map_map]

theorem burnsideF4h_clu_U5_borel :
    marking.borel = (hypProjBorel (burnsideF4h_clu_U5_fieldData marking) 2 1).map
      (burnsideF4h_clu_U5_Phi marking).toMonoidHom := by
  show (nativeParabolic .U5 (p ^ e) marking.field marking.basis false ⊓
    nativeParabolic .U5 (p ^ e) marking.field marking.basis true).map marking.transport = _
  rw [burnsideF4h_clu_U5_nativeParabolic, burnsideF4h_clu_U5_nativeParabolic,
    ← Subgroup.map_inf_eq _ _ _ (burnsideF4h_clu_U5_T marking).injective]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [burnsideF4h_clu_isoStabilizer_inf, Subgroup.map_map, burnsideF4h_clu_U5_comp,
    hypProjBorel, Subgroup.map_map]

theorem burnsideF4h_clu_U5_nativeRoot :
    nativeRoot .U5 (p ^ e) marking.basis .longOne false =
      Subgroup.closure {x : nativeGroup .U5 (p ^ e) marking.field | ∃ t : marking.field,
        t + t ^ (p ^ e) = 0 ∧
        ((x : GL (Coord .U5) marking.field) : Matrix (Fin 5) (Fin 5) marking.field) =
          (marking.basis : Matrix (Fin 5) (Fin 5) marking.field) * (1 + matrixUnit 0 4 t) *
            ((marking.basis⁻¹ : GL (Coord .U5) marking.field) :
              Matrix (Fin 5) (Fin 5) marking.field)} := by
  unfold nativeRoot
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, RootAllowed, ParameterAllowed, markedMatrix, positiveMatrix,
    unitaryRootFive, Bool.false_eq_true, if_false]
  constructor
  · rintro ⟨-, t, c, ht, hx⟩
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨by simp, t, 0, ht, hx⟩

theorem burnsideF4h_clu_U5_normalizer :
    marking.parabolic false ≤ Subgroup.normalizer (marking.root .longOne false : Set H) := by
  have hle : nativeParabolic .U5 (p ^ e) marking.field marking.basis false ≤
      Subgroup.normalizer (nativeRoot .U5 (p ^ e) marking.basis .longOne false :
        Set (nativeGroup .U5 (p ^ e) marking.field)) := by
    rw [burnsideF4h_clu_U5_nativeRoot]
    exact burnsideF4h_clu_rawStabilizer_le_normalizer (burnsideF4h_clu_U5_fieldData marking)
      marking.basis (burnsideF4h_clu_U5_gram marking) 0 4 rfl rfl (by norm_num)
  exact (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map _)

end U5

section

theorem burnsideF4h_clu_U4 (p exponent : ℕ) (H : Type) [Group H]
    (marking : ChF.ClassicalRoots.Marking .U4 p exponent H) :
    ChF.IsLieParabolics p (⊤ : Subgroup H) marking.borel (marking.parabolic false)
      (marking.parabolic true) ∧
    marking.parabolic false ≤ Subgroup.normalizer (marking.root .longOne false : Set H) := by
  refine ⟨?_, burnsideF4h_clu_U4_normalizer marking⟩
  rw [burnsideF4h_clu_U4_borel, burnsideF4h_clu_U4_parabolic marking false,
    burnsideF4h_clu_U4_parabolic marking true]
  exact burnsideF4h_cl_isLieParabolics_map _
    (burnsideF4h_clu_hyp_isLieParabolics _ (by norm_num))

end

section

theorem burnsideF4h_clu_U5 (p exponent : ℕ) (H : Type) [Group H]
    (marking : ChF.ClassicalRoots.Marking .U5 p exponent H) :
    ChF.IsLieParabolics p (⊤ : Subgroup H) marking.borel (marking.parabolic false)
      (marking.parabolic true) ∧
    marking.parabolic false ≤ Subgroup.normalizer (marking.root .longOne false : Set H) := by
  refine ⟨?_, burnsideF4h_clu_U5_normalizer marking⟩
  rw [burnsideF4h_clu_U5_borel, burnsideF4h_clu_U5_parabolic marking false,
    burnsideF4h_clu_U5_parabolic marking true]
  exact burnsideF4h_cl_isLieParabolics_map _
    (burnsideF4h_clu_hyp_isLieParabolics _ le_rfl)

end

end PartBurnsideF4hClU_dedup

section PartBurnsideF4hG2

section Words

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def burnsideF4h_g2_reflect (word : List (Fin Tag.G2.rank)) (v : Fin Tag.G2.rank → ℤ) :
    Fin Tag.G2.rank → ℤ :=
  word.foldl (fun root index => reflect Tag.G2 index root) v

theorem burnsideF4h_g2_reflect_eq_wordProd (word : List (Fin Tag.G2.rank))
    (v : Fin Tag.G2.rank → ℤ) :
    burnsideF4h_g2_reflect word v = (coxeterSystem Tag.G2).wordProd word.reverse • v := by
  induction word generalizing v with
  | nil => simp [burnsideF4h_g2_reflect]
  | cons i ω ih =>
    rw [List.reverse_cons, CoxeterSystem.wordProd_append, mul_smul,
      CoxeterSystem.wordProd_singleton, simple_smul, ← ih]
    rfl

theorem burnsideF4h_g2_isRoot_reflect (word : List (Fin Tag.G2.rank))
    {v : Fin Tag.G2.rank → ℤ} (hv : IsRoot Tag.G2 v) :
    IsRoot Tag.G2 (burnsideF4h_g2_reflect word v) := by
  induction word generalizing v with
  | nil => exact hv
  | cons i ω ih => exact ih (IsRoot.reflect i hv)

theorem burnsideF4h_g2_exists_word_of_isRoot {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α) :
    ∃ (word : List (Fin Tag.G2.rank)) (index : Fin Tag.G2.rank),
      burnsideF4h_g2_reflect word (Pi.single index 1) = α := by
  induction hα with
  | basis j => exact ⟨[], j, rfl⟩
  | reflect i _ ih =>
    obtain ⟨word, index, h⟩ := ih
    refine ⟨word ++ [i], index, ?_⟩
    simp only [burnsideF4h_g2_reflect, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at h ⊢
    rw [h]

end Words

section NoCert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

@[expose] noncomputable def burnsideF4h_g2_weylWord (K : Type) [Field K] (word : List (Fin Tag.G2.rank)) :
    Module.End K (RootModule Tag.G2 K) :=
  word.foldl (fun (operator : Module.End K (RootModule Tag.G2 K)) (index : Fin Tag.G2.rank) =>
    ChF.G2Native.weylOperator K index 1 * operator) 1

theorem burnsideF4h_g2_weylWordOperator_eq_weylWord (word : List (Fin Tag.G2.rank)) :
    ChF.G2Native.weylWordOperator K word = burnsideF4h_g2_weylWord K word := by
  unfold ChF.G2Native.weylWordOperator burnsideF4h_g2_weylWord
  rfl

theorem burnsideF4h_g2_height_single (index : Fin Tag.G2.rank) :
    height (τ := Tag.G2) (Pi.single index 1 : Fin Tag.G2.rank → ℤ) = 1 := by
  simp [height]

end NoCert

section Basic

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

@[expose] noncomputable def burnsideF4h_g2_wordUnit (K : Type) [Field K] (word : List (Fin Tag.G2.rank)) :
    ModGL Tag.G2 K :=
  (word.reverse.map fun i => weylElt Tag.G2 K i 1).prod

theorem burnsideF4h_g2_weylWordOperator_eq (word : List (Fin Tag.G2.rank)) :
    ChF.G2Native.weylWordOperator K word =
      ((burnsideF4h_g2_wordUnit K word : ModGL Tag.G2 K) :
        Module.End K (RootModule Tag.G2 K)) := by
  have key : ∀ (word : List (Fin Tag.G2.rank)) (init : Module.End K (RootModule Tag.G2 K)),
      word.foldl (fun (operator : Module.End K (RootModule Tag.G2 K)) (index : Fin Tag.G2.rank) =>
        ChF.G2Native.weylOperator K index 1 * operator) init =
        ((burnsideF4h_g2_wordUnit K word : ModGL Tag.G2 K) :
          Module.End K (RootModule Tag.G2 K)) * init := by
    intro word
    induction word with
    | nil => intro init; simp [burnsideF4h_g2_wordUnit]
    | cons i ω ih =>
      intro init
      rw [List.foldl_cons, ih]
      simp only [burnsideF4h_g2_wordUnit, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, Units.val_mul,
        mul_assoc]
      rfl
  rw [burnsideF4h_g2_weylWordOperator_eq_weylWord]
  unfold burnsideF4h_g2_weylWord
  rw [key word 1, mul_one]

theorem burnsideF4h_g2_mem_rootGenerators (root : Fin Tag.G2.rank → ℤ)
    (x : ChF.G2Native.Parent K) :
    x ∈ ChF.G2Native.rootGenerators K root ↔
      ∃ (word : List (Fin Tag.G2.rank)) (index : Fin Tag.G2.rank) (c : K),
        burnsideF4h_g2_reflect word (Pi.single index 1) = root ∧
        (x : ModGL Tag.G2 K) = burnsideF4h_g2_wordUnit K word * xUnit Tag.G2 K index c *
          (burnsideF4h_g2_wordUnit K word)⁻¹ := by
  unfold ChF.G2Native.rootGenerators ChF.G2Native.simpleGenerators ChF.G2Native.simpleVector
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨word, index, hroot, rep, hrep, g, ⟨c, hc⟩, rfl⟩
    refine ⟨word, index, c, hroot, ?_⟩
    have h1 : (rep : ModGL Tag.G2 K) = burnsideF4h_g2_wordUnit K word :=
      Units.ext (hrep.trans (burnsideF4h_g2_weylWordOperator_eq word))
    have h2 : (g : ModGL Tag.G2 K) = xUnit Tag.G2 K index c := Units.ext hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h1, h2]
  · rintro ⟨word, index, c, hroot, hx⟩
    have hmem : burnsideF4h_g2_wordUnit K word ∈ adjointGroup Tag.G2 K :=
      Subgroup.list_prod_mem _ fun g hg => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
        exact weylElt_mem_adjointGroup i 1
    refine ⟨word, index, hroot, ⟨burnsideF4h_g2_wordUnit K word, hmem⟩,
      (burnsideF4h_g2_weylWordOperator_eq word).symm, ⟨xUnit Tag.G2 K index c,
        xUnit_mem_adjointGroup index c⟩, ⟨c, rfl⟩, ?_⟩
    exact Subtype.ext hx

theorem burnsideF4h_g2_mem_torusGenerators (x : ChF.G2Native.Parent K) :
    x ∈ ChF.G2Native.torusGenerators K ↔
      ∃ (index : Fin Tag.G2.rank) (t : Kˣ),
        (x : ModGL Tag.G2 K) = torusElt Tag.G2 K index t := by
  unfold ChF.G2Native.torusGenerators
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨index, t, h⟩
    exact ⟨index, t, Units.ext h⟩
  · rintro ⟨index, t, h⟩
    exact ⟨index, t, by rw [h]; rfl⟩

theorem burnsideF4h_g2_xUnit_mem_borel (index : Fin Tag.G2.rank) (c : K) :
    xUnit Tag.G2 K index c ∈ borelGroup Tag.G2 K :=
  Subgroup.mem_sup_right
    (le_biSup (fun α => rootSubgroup Tag.G2 K α) (show (Pi.single index 1 : Fin Tag.G2.rank → ℤ) ∈
      {α | IsRoot Tag.G2 α ∧ 0 < height α} from ⟨isRoot_single Tag.G2 index, by
        rw [burnsideF4h_g2_height_single]; exact one_pos⟩)
      (mem_rootSubgroup.2 ⟨c, pinnedX_single Tag.G2 K index c⟩))

end Basic

section Transport

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable
  {K : Type} [Field K]

theorem burnsideF4h_g2_map_conj_wordUnit (word : List (Fin Tag.G2.rank)) (index : Fin Tag.G2.rank) :
    (rootSubgroup Tag.G2 K (Pi.single index 1)).map
        (MulAut.conj (burnsideF4h_g2_wordUnit K word)).toMonoidHom =
      rootSubgroup Tag.G2 K (burnsideF4h_g2_reflect word (Pi.single index 1)) := by
  have h := map_conj_prod_weylElt_rootSubgroup K word.reverse (isRoot_single Tag.G2 index)
  rw [burnsideF4h_g2_reflect_eq_wordProd]
  exact h

theorem burnsideF4h_g2_rootGenerators_mem {root : Fin Tag.G2.rank → ℤ}
    {x : ChF.G2Native.Parent K} (hgen : x ∈ ChF.G2Native.rootGenerators K root) :
    IsRoot Tag.G2 root ∧ (x : ModGL Tag.G2 K) ∈ rootSubgroup Tag.G2 K root := by
  obtain ⟨word, index, c, hroot, hx⟩ := (burnsideF4h_g2_mem_rootGenerators root x).1 hgen
  subst hroot
  refine ⟨burnsideF4h_g2_isRoot_reflect word (isRoot_single Tag.G2 index), ?_⟩
  rw [← burnsideF4h_g2_map_conj_wordUnit, hx]
  exact ⟨xUnit Tag.G2 K index c, mem_rootSubgroup.2 ⟨c, pinnedX_single Tag.G2 K index c⟩, rfl⟩

theorem burnsideF4h_g2_map_rootSubgroup {root : Fin Tag.G2.rank → ℤ} (hroot : IsRoot Tag.G2 root) :
    (ChF.G2Native.rootSubgroup K root).map (adjointGroup Tag.G2 K).subtype =
      rootSubgroup Tag.G2 K root := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    exact (burnsideF4h_g2_rootGenerators_mem hx).2
  · obtain ⟨word, index, h⟩ := burnsideF4h_g2_exists_word_of_isRoot hroot
    subst h
    rw [← burnsideF4h_g2_map_conj_wordUnit]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
    rw [pinnedX_single]
    have hmem : burnsideF4h_g2_wordUnit K word ∈ adjointGroup Tag.G2 K :=
      Subgroup.list_prod_mem _ fun g hg => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
        exact weylElt_mem_adjointGroup i 1
    refine ⟨⟨burnsideF4h_g2_wordUnit K word * xUnit Tag.G2 K index c *
      (burnsideF4h_g2_wordUnit K word)⁻¹, mul_mem (mul_mem hmem (xUnit_mem_adjointGroup index c))
        (inv_mem hmem)⟩, ?_, rfl⟩
    exact Subgroup.subset_closure
      ((burnsideF4h_g2_mem_rootGenerators _ _).2 ⟨word, index, c, rfl, rfl⟩)

theorem burnsideF4h_g2_rootSubgroup_eq {root : Fin Tag.G2.rank → ℤ} (hroot : IsRoot Tag.G2 root) :
    ChF.G2Native.rootSubgroup K root =
      (rootSubgroup Tag.G2 K root).subgroupOf (adjointGroup Tag.G2 K) := by
  rw [← burnsideF4h_g2_map_rootSubgroup hroot]
  exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup Tag.G2 K).subtype_injective _).symm

theorem burnsideF4h_g2_map_positiveBorel :
    (ChF.G2Native.positiveBorel K).map (adjointGroup Tag.G2 K).subtype =
      borelGroup Tag.G2 K := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    unfold ChF.G2Native.positiveBorel
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rcases hx with hx | ⟨root, hpos, hx⟩
    · obtain ⟨index, t, h⟩ := (burnsideF4h_g2_mem_torusGenerators x).1 hx
      show (x : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K
      rw [h]
      exact Subgroup.mem_sup_left (torusElt_mem_torusGroup index t)
    · obtain ⟨hroot, hmem⟩ := burnsideF4h_g2_rootGenerators_mem hx
      exact Subgroup.mem_sup_right
        (le_biSup (fun α => rootSubgroup Tag.G2 K α) (show root ∈ {α | IsRoot Tag.G2 α ∧
          0 < height α} from ⟨hroot, hpos⟩) hmem)
  · refine sup_le ?_ ?_
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨⟨index, t⟩, rfl⟩
      refine ⟨⟨torusElt Tag.G2 K index t, torusElt_mem_adjointGroup index t⟩, ?_, rfl⟩
      unfold ChF.G2Native.positiveBorel
      exact Subgroup.subset_closure (Or.inl
        ((burnsideF4h_g2_mem_torusGenerators _).2 ⟨index, t, rfl⟩))
    · refine iSup₂_le fun root hroot => ?_
      rw [← burnsideF4h_g2_map_rootSubgroup hroot.1]
      refine Subgroup.map_mono ?_
      unfold ChF.G2Native.rootSubgroup ChF.G2Native.positiveBorel
      exact Subgroup.closure_mono fun x hx => Or.inr ⟨root, hroot.2, hx⟩

theorem burnsideF4h_g2_map_parabolic (index : Fin Tag.G2.rank) :
    (ChF.G2Native.positiveBorel K ⊔ ChF.G2Native.rootSubgroup K (-Pi.single index 1)).map
        (adjointGroup Tag.G2 K).subtype = parabolicSubgroup Tag.G2 K {index} := by
  rw [Subgroup.map_sup, burnsideF4h_g2_map_positiveBorel,
    burnsideF4h_g2_map_rootSubgroup (isRoot_neg_single Tag.G2 index)]
  unfold parabolicSubgroup
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    have hn : weylElt Tag.G2 K index 1 ∈ borelGroup Tag.G2 K ⊔
        Subgroup.closure ((fun j => weylElt Tag.G2 K j 1) '' {index}) :=
      Subgroup.mem_sup_right (Subgroup.subset_closure ⟨index, rfl, rfl⟩)
    rw [← reflect_single_self Tag.G2 index,
      ← map_conj_weylElt_rootSubgroup K index (isRoot_single Tag.G2 index)]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
    rw [pinnedX_single]
    exact mul_mem (mul_mem hn (Subgroup.mem_sup_left (burnsideF4h_g2_xUnit_mem_borel index c)))
      (inv_mem hn)
  · refine sup_le le_sup_left ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_singleton_iff] at hj
    subst hj
    show weylElt Tag.G2 K j 1 ∈ _
    rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul]
    have hx : xUnit Tag.G2 K j 1 ∈ borelGroup Tag.G2 K ⊔ rootSubgroup Tag.G2 K (-Pi.single j 1) :=
      Subgroup.mem_sup_left (burnsideF4h_g2_xUnit_mem_borel j 1)
    have hy : yUnit Tag.G2 K j (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) ∈
        borelGroup Tag.G2 K ⊔ rootSubgroup Tag.G2 K (-Pi.single j 1) :=
      Subgroup.mem_sup_right
        (mem_rootSubgroup.2 ⟨_, pinnedX_neg_single Tag.G2 K j _⟩)
    exact mul_mem (mul_mem hx hy) hx

theorem burnsideF4h_g2_eq_Pmin (index : Fin Tag.G2.rank) :
    ChF.G2Native.positiveBorel K ⊔ ChF.G2Native.rootSubgroup K (-Pi.single index 1) =
      CFSG.Quasithin.H13.F431.G2.Pmin K index := by
  unfold CFSG.Quasithin.H13.F431.G2.Pmin
  rw [← burnsideF4h_g2_map_parabolic index]
  exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup Tag.G2 K).subtype_injective _).symm

theorem burnsideF4h_g2_point_eq :
    ChF.G2Native.pointParabolic K = CFSG.Quasithin.H13.F431.G2.Pmin K ⟨1, by decide⟩ := by
  unfold ChF.G2Native.pointParabolic
  rw [show (-ChF.G2Native.simpleVector 1 : ChF.G2Native.Lattice) =
    -Pi.single (⟨1, by decide⟩ : Fin Tag.G2.rank) 1 from rfl, burnsideF4h_g2_eq_Pmin]

theorem burnsideF4h_g2_line_eq :
    ChF.G2Native.lineParabolic K = CFSG.Quasithin.H13.F431.G2.Pmin K ⟨0, by decide⟩ := by
  unfold ChF.G2Native.lineParabolic
  rw [show (-ChF.G2Native.simpleVector 0 : ChF.G2Native.Lattice) =
    -Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1 from rfl, burnsideF4h_g2_eq_Pmin]

end Transport

section System

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Quasithin.H13.F431.G2 CFSG.Quasithin.H13.F431.BN

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem burnsideF4h_g2_torus_eq_bot (hK : Nat.card K = 2) (i : Fin 2) :
    torus (τ := Tag.G2) K i = ⊥ := by
  have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 h1).1
  unfold torus
  rw [eq_bot_iff]
  rintro _ ⟨t, rfl⟩
  rw [Subsingleton.elim t 1, map_one]
  exact Subgroup.one_mem _

theorem burnsideF4h_g2_faithful_two (hK : Nat.card K = 2) :
    FaithfulOnBuilding (hexQuotPre (g2Data K)).B (hexQuotPre (g2Data K)).N
      (hexQuotPre (g2Data K)).w₁ (hexQuotPre (g2Data K)).w₂ := by
  haveI := (hexQuotRGD2 (g2Data K)).cartan_normal
  refine (hexQuotRGD2 (g2Data K)).faithful (hexQuotRGD2_gen (g2Data K)) ?_
  intro g hg _
  have h0 : (⨆ i : Fin 2, torus (τ := Tag.G2) K i) = ⊥ := by
    rw [iSup_eq_bot]
    exact burnsideF4h_g2_torus_eq_bot hK
  rw [h0, Subgroup.map_bot] at hg
  exact Subgroup.mem_bot.1 hg

theorem burnsideF4h_g2_faithful (K : Type) [Field K] [Finite K] :
    FaithfulOnBuilding (hexQuotPre (g2Data K)).B (hexQuotPre (g2Data K)).N
      (hexQuotPre (g2Data K)).w₁ (hexQuotPre (g2Data K)).w₂ := by
  by_cases h2 : Nat.card K = 2
  · exact burnsideF4h_g2_faithful_two h2
  · have hlt : 1 < Nat.card K := Finite.one_lt_card
    have h3 : 3 ≤ Nat.card K := by omega
    haveI := isSimpleGroup_g2Model h3
    exact (hexQuotPre (g2Data K)).faithful_of_isSimpleGroup

@[expose] noncomputable def burnsideF4h_g2_sys (K : Type) [Field K] [Finite K] :
    RankTwoSystem (AdjointQuotient .G2 K) 6 :=
  (hexQuotPre (g2Data K)).toSystem (burnsideF4h_g2_faithful K)

theorem burnsideF4h_g2_sys_B [Finite K] :
    (burnsideF4h_g2_sys K).B =
      ((⨆ i, torus (τ := Tag.G2) K i) ⊔ posUnipotent (g2Datum K)).map (proj K) := by
  rw [Subgroup.map_sup]
  rfl

theorem burnsideF4h_g2_sys_U [Finite K] :
    (burnsideF4h_g2_sys K).U = (posUnipotentSub Tag.G2 K).map (proj K) := by
  rw [posUnipotentSub_eq]
  rfl

theorem burnsideF4h_g2_sys_B_le [Finite K] (i : Fin Tag.G2.rank) :
    (burnsideF4h_g2_sys K).B ≤ (Pmin K i).map (proj K) := by
  rw [burnsideF4h_g2_sys_B]
  refine Subgroup.map_mono (sup_le (iSup_le fun j => ?_) ?_)
  · rintro _ ⟨t, rfl⟩
    exact Subgroup.mem_subgroupOf.2
      (torusGroup_le_parabolicSubgroup _ (torusElt_mem_torusGroup j t))
  · rw [← posUnipotentSub_eq]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (borelGroup_le_parabolicSubgroup _
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hx)))

theorem burnsideF4h_g2_sys_lift [Finite K] (b : Bool) :
    ∃ m : (burnsideF4h_g2_sys K).N, (m : (burnsideF4h_g2_sys K).Weyl) =
        gen (burnsideF4h_g2_sys K).w₁ (burnsideF4h_g2_sys K).w₂ b ∧
      (m : AdjointQuotient .G2 K) = proj K (weylElement .G2 K (idx b)) := by
  cases b
  · exact ⟨(hexQuotRGD2 (g2Data K)).nrep 1, rfl, rfl⟩
  · exact ⟨(hexQuotRGD2 (g2Data K)).nrep 0, rfl, rfl⟩

theorem burnsideF4h_g2_sys_P [Finite K] (b : Bool) :
    (Pmin K (idx b)).map (proj K) = P (burnsideF4h_g2_sys K) b := by
  obtain ⟨m₁, h₁, e₁⟩ := burnsideF4h_g2_sys_lift (K := K) b
  obtain ⟨m₂, h₂, e₂⟩ := burnsideF4h_g2_sys_lift (K := K) (!b)
  refine eq_P_of_lifts _ (burnsideF4h_g2_sys_B_le _) b m₁ m₂ h₁ h₂ ?_ ?_
  · rw [e₁]
    exact ⟨weylElement .G2 K (idx b), Subgroup.mem_subgroupOf.2
      (weylElt_mem_parabolicSubgroup (Set.mem_singleton _)), rfl⟩
  · rw [e₂]
    rintro ⟨y, hy, hyx⟩
    have hy' : y = weylElement .G2 K (idx (!b)) := proj_injective hyx
    subst hy'
    have h3 := weylElt_mem_parabolicSubgroup_iff.1 (Subgroup.mem_subgroupOf.1 hy)
    exact absurd (idx_injective (Set.mem_singleton_iff.1 h3)) (by cases b <;> simp)

theorem burnsideF4h_g2_fullLocal_point [Finite K] :
    ChF.G2Native.fullLocal K (ChF.G2Native.pointParabolic K) = (burnsideF4h_g2_sys K).P₁ := by
  have h := burnsideF4h_g2_sys_P (K := K) true
  show _ = P (burnsideF4h_g2_sys K) true
  rw [← h, burnsideF4h_g2_point_eq]
  rfl

theorem burnsideF4h_g2_fullLocal_line [Finite K] :
    ChF.G2Native.fullLocal K (ChF.G2Native.lineParabolic K) = (burnsideF4h_g2_sys K).P₂ := by
  have h := burnsideF4h_g2_sys_P (K := K) false
  show _ = P (burnsideF4h_g2_sys K) false
  rw [← h, burnsideF4h_g2_line_eq]
  rfl

theorem burnsideF4h_g2_positiveBorel_eq :
    ChF.G2Native.positiveBorel K = (⨆ i, torus (τ := Tag.G2) K i) ⊔ posUnipotent (g2Datum K) := by
  have h : ChF.G2Native.positiveBorel K = borelSub Tag.G2 K := by
    unfold borelSub Subgroup.subgroupOf
    rw [← burnsideF4h_g2_map_positiveBorel]
    exact (Subgroup.comap_map_eq_self_of_injective (adjointGroup Tag.G2 K).subtype_injective
      _).symm
  rw [h, iSup_torus_eq_torusSub, ← posUnipotentSub_eq, ← posUnipotentSub_sup_torusSub, sup_comm]

theorem burnsideF4h_g2_fullLocal_borel [Finite K] :
    ChF.G2Native.fullLocal K (ChF.G2Native.positiveBorel K) = (burnsideF4h_g2_sys K).B := by
  rw [burnsideF4h_g2_sys_B, ← burnsideF4h_g2_positiveBorel_eq]
  rfl

end System

section Generic

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN

theorem burnsideF4h_g2_isLieParabolics {X : Type} [Group X] {n : ℕ} (D : RankTwoSystem X n)
    {p : ℕ} (hU : ChF.IsSylowOf p D.U ⊤) : ChF.IsLieParabolics p ⊤ D.B D.P₁ D.P₂ := by
  have hB1 : D.B ≠ D.P₁ := fun h => not_le_P D true (by
    show D.P₁ ≤ D.P₂
    rw [← h]
    exact B_le_P D false)
  refine ⟨⟨D.U, hU, by rw [top_inf_eq, normalizer_U_eq_B]⟩, P₁_ne_P₂ D, P₁_inf_P₂ D,
    fun Q => ⟨?_, ?_⟩⟩
  · rintro ⟨hBQ, -, hQ, hmax⟩
    rcases eq_B_or_P_or_top D hBQ with h | ⟨i, h⟩ | h
    · exfalso
      subst h
      exact P_ne_top D true (hmax _ (lt_of_le_of_ne (B_le_P D true) hB1) le_top)
    · cases i
      · exact Or.inr h
      · exact Or.inl h
    · exact absurd h hQ
  · have key : ∀ i : Bool, D.B ≤ P D i ∧ P D i ≤ ⊤ ∧ P D i ≠ ⊤ ∧
        ∀ R : Subgroup X, P D i < R → R ≤ ⊤ → R = ⊤ :=
      fun i => ⟨B_le_P D i, le_top, P_ne_top D i, fun R hR _ => (isCoatom_P D i).2 R hR⟩
    rintro (rfl | rfl)
    · exact key true
    · exact key false

end Generic

section Sylow

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Quasithin.H13.F431.G2 CFSG.Quasithin.H13.F431.BN

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem burnsideF4h_g2_sys_U_sylow [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ChF.IsSylowOf p (burnsideF4h_g2_sys K).U ⊤ := by
  obtain ⟨w₀, hw₀⟩ :=
    Finite.exists_max fun w : WeylGroup Tag.G2 => (coxeterSystem Tag.G2).length w
  obtain ⟨S, hS⟩ := (exceptional_ordinary_Sylow_opposition Tag.G2 K p w₀ hw₀).1
  have hU : (burnsideF4h_g2_sys K).U = (S : Subgroup ↥(adjointGroup Tag.G2 K)).map
      (mk K).toMonoidHom := by
    rw [burnsideF4h_g2_sys_U, hS, mk_toMonoidHom]
  rw [hU]
  refine ⟨le_top, S.isPGroup'.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have hidx : ((S : Subgroup ↥(adjointGroup Tag.G2 K)).map (mk K).toMonoidHom).index =
      (S : Subgroup ↥(adjointGroup Tag.G2 K)).index :=
    Subgroup.index_map_equiv _ (mk K)
  rw [hidx]
  exact S.not_dvd_index

end Sylow

section RootData

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem burnsideF4h_g2_cRoot_isRoot : IsRoot Tag.G2 ![2, 3] := by
  have h : IsRoot Tag.G2 (reflect Tag.G2 (0 : Fin 2) (reflect Tag.G2 (1 : Fin 2)
      (Pi.single (0 : Fin 2) 1))) :=
    IsRoot.reflect (τ := Tag.G2) (0 : Fin 2) (IsRoot.reflect (τ := Tag.G2) (1 : Fin 2)
      (IsRoot.basis (τ := Tag.G2) (0 : Fin 2)))
  have e : reflect Tag.G2 (0 : Fin 2) (reflect Tag.G2 (1 : Fin 2) (Pi.single (0 : Fin 2) 1)) =
      ![2, 3] := List.ofFn_injective (by decide +kernel)
  rwa [e] at h

theorem burnsideF4h_g2_height_nsmul_add_nsmul {τ : Tag} (a b : ℕ) (α β : Fin τ.rank → ℤ) :
    height (a • α + b • β) = a * height α + b * height β := by
  simp [height, Finset.sum_add_distrib, Finset.mul_sum]

theorem burnsideF4h_g2_height_le {v : Fin Tag.G2.rank → ℤ} (hv : IsRoot Tag.G2 v) :
    height v ≤ 5 := by
  have key : ∀ w ∈ rootFinset Tag.G2, height (τ := Tag.G2) w ≤ 5 := by decide +kernel
  exact key v (mem_rootFinset.2 hv)

theorem burnsideF4h_g2_mem_normalizer_of_commute {G : Type*} [Group G] {H : Subgroup G} {u : G}
    (hc : ∀ g ∈ H, u * g * u⁻¹ = g) : u ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [hc g hg]
    exact hg
  · intro hg
    have e := hc _ hg
    have : g = u * g * u⁻¹ := by
      calc g = u⁻¹ * (u * (u * g * u⁻¹) * u⁻¹) * u := by rw [e]; group
        _ = u * g * u⁻¹ := by group
    rw [this]
    exact hg

end RootData

section Normalizer

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem burnsideF4h_g2_commute_pinnedX {τ : Tag} (R : Type) [CommRing R]
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β)
    (h : ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot τ (a • α + b • β)) (c d : R) :
    Commute (pinnedX τ R α c) (pinnedX τ R β d) := by
  obtain ⟨-, hmem, -, -, hF⟩ := root_commutator_formula τ hα hβ hne hne'
  have hnil : commPairs τ α β = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp => by
    obtain ⟨h1, h2, hr⟩ := (hmem p).1 hp
    exact h p.1 p.2 h1 h2 hr
  have hF' := hF R c d
  rw [hnil, List.map_nil, List.prod_nil, ← pinnedX_neg, ← pinnedX_neg, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm] at hF'
  exact hF'

theorem burnsideF4h_g2_commute_cRoot {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α)
    (hpos : 0 < height (τ := Tag.G2) α) (x y : K) :
    Commute (pinnedX Tag.G2 K α x) (pinnedX Tag.G2 K ![2, 3] y) := by
  have hc := burnsideF4h_g2_cRoot_isRoot
  have h5 : height (τ := Tag.G2) (![2, 3] : Fin Tag.G2.rank → ℤ) = 5 := by decide +kernel
  have hm5 : height (τ := Tag.G2) (-![2, 3] : Fin Tag.G2.rank → ℤ) = -5 := by decide +kernel
  by_cases hαc : α = ![2, 3]
  · subst hαc
    have h1 := pinnedX_add Tag.G2 K ![2, 3] x y
    have h2 := pinnedX_add Tag.G2 K ![2, 3] y x
    exact h1.symm.trans ((congrArg (pinnedX Tag.G2 K ![2, 3]) (add_comm x y)).trans h2)
  · have hαc' : α ≠ -![2, 3] := by
      rintro rfl
      rw [hm5] at hpos
      omega
    refine burnsideF4h_g2_commute_pinnedX K hα hc hαc hαc' ?_ x y
    intro a b ha hb hr
    have key : ∀ β : Fin Tag.G2.rank → ℤ, height β = 5 → IsRoot Tag.G2 (a • α + b • β) →
        False := by
      intro β hβ hr'
      have h1 := burnsideF4h_g2_height_le hr'
      rw [burnsideF4h_g2_height_nsmul_add_nsmul, hβ] at h1
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    exact key _ h5 hr

theorem burnsideF4h_g2_parabolic_le_normalizer :
    parabolicSubgroup Tag.G2 K {⟨1, by decide⟩} ≤
      Subgroup.normalizer (rootSubgroup Tag.G2 K ![2, 3] : Set (ModGL Tag.G2 K)) := by
  have hc := burnsideF4h_g2_cRoot_isRoot
  unfold parabolicSubgroup
  refine sup_le (sup_le ?_ ?_) ((Subgroup.closure_le _).2 ?_)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (map_conj_torusElt_rootSubgroup i t hc)
  · refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, rfl⟩
    refine burnsideF4h_g2_mem_normalizer_of_commute fun g hg => ?_
    obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hg
    rw [(burnsideF4h_g2_commute_cRoot hα.1 hα.2 x y).eq, mul_inv_cancel_right]
  · rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_singleton_iff] at hj
    subst hj
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff_map_conj_eq]
    have e : reflect Tag.G2 (⟨1, by decide⟩ : Fin Tag.G2.rank) ![2, 3] = ![2, 3] :=
      List.ofFn_injective (by decide +kernel)
    have h := map_conj_weylElt_rootSubgroup K (⟨1, by decide⟩ : Fin Tag.G2.rank) hc
    rw [e] at h
    exact h

theorem burnsideF4h_g2_point_le_normalizer :
    ChF.G2Native.pointParabolic K ≤
      Subgroup.normalizer (ChF.G2Native.longRoot K : Set (ChF.G2Native.Parent K)) := by
  rw [burnsideF4h_g2_point_eq]
  have hL : ChF.G2Native.longRoot K =
      (rootSubgroup Tag.G2 K ![2, 3]).subgroupOf (adjointGroup Tag.G2 K) := by
    unfold ChF.G2Native.longRoot ChF.G2Native.highestLong
    exact burnsideF4h_g2_rootSubgroup_eq burnsideF4h_g2_cRoot_isRoot
  rw [hL]
  intro x hx
  have hxN := burnsideF4h_g2_parabolic_le_normalizer (Subgroup.mem_subgroupOf.1 hx)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have := Subgroup.mem_normalizer_iff.1 hxN (y : ModGL Tag.G2 K)
  simpa [Subgroup.mem_subgroupOf] using this

theorem burnsideF4h_g2_fullLocal_point_le_normalizer :
    ChF.G2Native.fullLocal K (ChF.G2Native.pointParabolic K) ≤
      Subgroup.normalizer (ChF.G2Native.fullLocal K (ChF.G2Native.longRoot K) :
        Set (ChF.G2Native.FullModel K)) :=
  (Subgroup.map_mono burnsideF4h_g2_point_le_normalizer).trans (Subgroup.le_normalizer_map _)

theorem burnsideF4h_g2_smallLocal_point_le_normalizer :
    ChF.G2Native.smallLocal K (ChF.G2Native.pointParabolic K) ≤
      Subgroup.normalizer (ChF.G2Native.smallLocal K (ChF.G2Native.longRoot K) :
        Set (ChF.G2Native.SmallModel K)) :=
  (Subgroup.map_mono ((Subgroup.comap_mono burnsideF4h_g2_point_le_normalizer).trans
    (Subgroup.le_normalizer_comap _))).trans (Subgroup.le_normalizer_map _)

end Normalizer

section


theorem burnsideF4h_g2_full (K : Type) [Field K] : ChF.G2Native.fullCompatibilityGoal K := by
  unfold ChF.G2Native.fullCompatibilityGoal
  intro p e hp he hK
  have hcard : Nat.card K ≠ 0 := by rw [hK]; exact pow_ne_zero _ hp.ne_zero
  haveI : Finite K := Nat.finite_of_card_ne_zero hcard
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hK)
  refine ⟨?_, burnsideF4h_g2_fullLocal_point_le_normalizer, ?_⟩
  · rw [burnsideF4h_g2_fullLocal_borel, burnsideF4h_g2_fullLocal_point,
      burnsideF4h_g2_fullLocal_line]
    exact burnsideF4h_g2_isLieParabolics _ (burnsideF4h_g2_sys_U_sylow p)
  · rw [burnsideF4h_g2_fullLocal_point, burnsideF4h_g2_fullLocal_line]
    exact CFSG.Quasithin.H13.F431.BN.P₁_sup_P₂ _

end

end PartBurnsideF4hG2

section PartBurnsideF4hG2b

section Generic

variable {G G' : Type*} [Group G] [Group G']

theorem burnsideF4h_g2_map_symm_map (e : G ≃* G') (M : Subgroup G) :
    (M.map e.toMonoidHom).map e.symm.toMonoidHom = M := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hg
    exact ⟨e g, ⟨g, hg, rfl⟩, by simp⟩

theorem burnsideF4h_g2_lattice_map (e : G ≃* G') {T A B : Subgroup G}
    (hN : Subgroup.normalizer (T : Set G) = T)
    (hlat : ∀ Q : Subgroup G, T ≤ Q → Q = T ∨ Q = A ∨ Q = B ∨ Q = ⊤) :
    Subgroup.normalizer ((T.map e.toMonoidHom : Subgroup G') : Set G') = T.map e.toMonoidHom ∧
      ∀ Q : Subgroup G', T.map e.toMonoidHom ≤ Q →
        Q = T.map e.toMonoidHom ∨ Q = A.map e.toMonoidHom ∨ Q = B.map e.toMonoidHom ∨ Q = ⊤ := by
  refine ⟨?_, fun Q hQ => ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq, hN]
  · have hQ' : T ≤ Q.map e.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := e.symm.toMonoidHom) hQ
      rwa [burnsideF4h_g2_map_symm_map] at this
    have hback : (Q.map e.symm.toMonoidHom).map e.toMonoidHom = Q := by
      have := burnsideF4h_g2_map_symm_map e.symm Q
      simpa using this
    rcases hlat _ hQ' with h | h | h | h
    · left
      rw [← hback, h]
    · right; left
      rw [← hback, h]
    · right; right; left
      rw [← hback, h]
    · right; right; right
      rw [← hback, h, Subgroup.map_top_of_surjective _ e.surjective]

theorem burnsideF4h_g2_isLie_of_lattice {G : Type} [Group G] {p : ℕ} {S A B P₁ P₂ : Subgroup G}
    (hS : ChF.IsSylowOf p S ⊤) (hN : Subgroup.normalizer (S : Set G) = S)
    (hlat : ∀ Q : Subgroup G, S ≤ Q → Q = S ∨ Q = A ∨ Q = B ∨ Q = ⊤)
    (h1 : S ≤ P₁) (h2 : S ≤ P₂) (h12 : P₁ ≠ P₂) (h1S : P₁ ≠ S) (h2S : P₂ ≠ S)
    (h1T : P₁ ≠ ⊤) (h2T : P₂ ≠ ⊤) (hinf : P₁ ⊓ P₂ = S) :
    ChF.IsLieParabolics p ⊤ S P₁ P₂ ∧ P₁ ⊔ P₂ = ⊤ := by
  have hAB : (A = P₁ ∨ A = P₂) ∧ (B = P₁ ∨ B = P₂) := by
    rcases hlat P₁ h1 with e1 | e1 | e1 | e1
    · exact absurd e1 h1S
    · rcases hlat P₂ h2 with e2 | e2 | e2 | e2
      · exact absurd e2 h2S
      · exact absurd (e1.trans e2.symm) h12
      · exact ⟨Or.inl e1.symm, Or.inr e2.symm⟩
      · exact absurd e2 h2T
    · rcases hlat P₂ h2 with e2 | e2 | e2 | e2
      · exact absurd e2 h2S
      · exact ⟨Or.inr e2.symm, Or.inl e1.symm⟩
      · exact absurd (e1.trans e2.symm) h12
      · exact absurd e2 h2T
    · exact absurd e1 h1T
  have hlat' : ∀ Q : Subgroup G, S ≤ Q → Q = S ∨ Q = P₁ ∨ Q = P₂ ∨ Q = ⊤ := by
    intro Q hQ
    rcases hlat Q hQ with e | e | e | e
    · exact Or.inl e
    · rcases hAB.1 with h | h <;> rw [e, h] <;> simp
    · rcases hAB.2 with h | h <;> rw [e, h] <;> simp
    · exact Or.inr (Or.inr (Or.inr e))
  have hP1S : ¬ P₁ ≤ S := fun h => h1S (le_antisymm h h1)
  have hP2S : ¬ P₂ ≤ S := fun h => h2S (le_antisymm h h2)
  have h12' : ¬ P₁ ≤ P₂ := fun h => hP1S (by rw [← hinf]; exact le_inf le_rfl h)
  have h21' : ¬ P₂ ≤ P₁ := fun h => hP2S (by rw [← hinf]; exact le_inf h le_rfl)
  have hmax : ∀ (P : Subgroup G), S ≤ P → P ≠ ⊤ → ¬ P ≤ S → (P = P₁ ∨ P = P₂) →
      ∀ R : Subgroup G, P < R → R = ⊤ := by
    intro P hSP hPT hPS hP R hR
    rcases hlat' R (hSP.trans hR.le) with e | e | e | e
    · exact absurd (e ▸ hR.le) hPS
    · rcases hP with rfl | rfl
      · exact absurd e (ne_of_gt hR)
      · exact absurd (e ▸ hR.le) h21'
    · rcases hP with rfl | rfl
      · exact absurd (e ▸ hR.le) h12'
      · exact absurd e (ne_of_gt hR)
    · exact e
  refine ⟨⟨⟨S, hS, by rw [top_inf_eq, hN]⟩, h12, hinf, fun Q => ⟨?_, ?_⟩⟩, ?_⟩
  · rintro ⟨hSQ, -, hQ, hQmax⟩
    rcases hlat' Q hSQ with e | e | e | e
    · subst e
      exact absurd (hQmax P₁ (lt_of_le_of_ne h1 (Ne.symm h1S)) le_top) h1T
    · exact Or.inl e
    · exact Or.inr e
    · exact absurd e hQ
  · rintro (rfl | rfl)
    · exact ⟨h1, le_top, h1T, fun R hR _ => hmax _ h1 h1T hP1S (Or.inl rfl) R hR⟩
    · exact ⟨h2, le_top, h2T, fun R hR _ => hmax _ h2 h2T hP2S (Or.inr rfl) R hR⟩
  · rcases hlat' (P₁ ⊔ P₂) (h1.trans le_sup_left) with e | e | e | e
    · exact absurd (e ▸ (le_sup_left : P₁ ≤ P₁ ⊔ P₂)) hP1S
    · exact absurd (e ▸ (le_sup_right : P₂ ≤ P₁ ⊔ P₂)) h21'
    · exact absurd (e ▸ (le_sup_left : P₁ ≤ P₁ ⊔ P₂)) h12'
    · exact e

theorem burnsideF4h_g2_comap_injective {H F : Type*} [Group H] [Group F] (f : H →* F)
    {B X Y : Subgroup F} (hcov : ∀ q : F, ∃ h : H, ∃ b ∈ B, q = f h * b) (hX : B ≤ X)
    (hY : B ≤ Y) (hXY : X.comap f = Y.comap f) : X = Y := by
  have key : ∀ {X Y : Subgroup F}, B ≤ X → X.comap f = Y.comap f → B ≤ Y → X ≤ Y := by
    intro X Y hX hXY hY q hq
    obtain ⟨h, b, hb, rfl⟩ := hcov q
    have hh : h ∈ X.comap f := by
      rw [Subgroup.mem_comap]
      have := X.mul_mem hq (X.inv_mem (hX hb))
      simpa using this
    rw [hXY] at hh
    exact Y.mul_mem hh (hY hb)
  exact le_antisymm (key hX hXY hY) (key hY hXY.symm hX)

theorem burnsideF4h_g2_card_le_two_mul {G : Type*} [Group G] (R U : Subgroup G) (hR : R.index = 2) :
    Nat.card U ≤ 2 * Nat.card ↥(R ⊓ U) := by
  haveI := Subgroup.normal_of_index_eq_two hR
  have hdvd : R.relIndex U ∣ 2 := hR ▸ Subgroup.relIndex_dvd_index_of_normal R U
  have hle : R.relIndex U ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hmul := Subgroup.relIndex_mul_card (H := R) (K := U)
  calc Nat.card U = R.relIndex U * Nat.card ↥(R ⊓ U) := hmul.symm
    _ ≤ 2 * Nat.card ↥(R ⊓ U) := Nat.mul_le_mul_right _ hle

theorem burnsideF4h_g2_relIndex_eq_two {G : Type*} [Group G] {R P : Subgroup G} (hR : R.index = 2)
    (hP : ¬ P ≤ R) : R.relIndex P = 2 := by
  haveI := Subgroup.normal_of_index_eq_two hR
  have hdvd : R.relIndex P ∣ 2 := hR ▸ Subgroup.relIndex_dvd_index_of_normal R P
  have h1 : R.relIndex P ≠ 1 := fun h => hP (Subgroup.relIndex_eq_one.1 h)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd h h1
  · exact h

end Generic

section U33Perm

open CFSG.Quasithin CFSG.Sporadic.Bridge

@[expose] def burnsideF4h_g2_conjWords : List String :=
  ["", "", "", "", "", "ayx", "", "", "sx", "", "", "", "x", "", "", "", "", "", "", "", "",
    "syx", "", "", "yx", "", "", "", "", "", "", "byx"]

@[expose] def burnsideF4h_g2_conjW (i : ℕ) : List (ℕ × Bool) :=
  u33W (burnsideF4h_g2_conjWords.getD i "")

theorem burnsideF4h_g2_invol_perm : ∀ i : Fin 32,
    u33Tel u33GenP i * u33Tel u33GenP i = 1 → u33Tel u33GenP i ≠ 1 →
    wordProd u33GenP (burnsideF4h_g2_conjW i) * u33Z *
      (wordProd u33GenP (burnsideF4h_g2_conjW i))⁻¹ = u33Tel u33GenP i := by
  decide +kernel

end U33Perm

section U33

open CFSG.Quasithin CFSG.Sporadic.Bridge

set_option linter.unusedSectionVars false


theorem burnsideF4h_g2_finite_u33 : Finite U33G :=
  Nat.finite_of_card_ne_zero (by rw [card_u33Pres]; norm_num)

theorem burnsideF4h_g2_invol_T (i : Fin 32) (h1 : u33Tel u33GenPG i * u33Tel u33GenPG i = 1)
    (h2 : u33Tel u33GenPG i ≠ 1) : ∃ g : U33G, g * u33z * g⁻¹ = u33Tel u33GenPG i := by
  refine ⟨wordProd u33GenPG (burnsideF4h_g2_conjW i), u33PresHom_injective ?_⟩
  rw [map_mul, map_mul, map_inv, u33PresHom_wordProd', u33PresHom_z, u33Tel_hom]
  refine burnsideF4h_g2_invol_perm i ?_ ?_
  · rw [← u33Tel_hom, ← map_mul, h1, map_one]
  · intro h
    apply h2
    apply u33PresHom_injective
    rw [u33Tel_hom, h, map_one]

open scoped Pointwise in
theorem burnsideF4h_g2_sylow_conj {G : Type*} [Group G] [Finite G] (S T : Subgroup G)
    (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    ∃ h : G, ∀ g : G, g ∈ T ↔ ∃ s ∈ S, h * s * h⁻¹ = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 G := hS.toSylow hSi
  let T' : Sylow 2 G := hT.toSylow hTi
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S' T'
  refine ⟨h, fun g => ?_⟩
  have hT' : (T : Subgroup G) = MulAut.conj h • S := by
    have := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hh
    simpa [Sylow.coe_subgroup_smul, S', T', IsPGroup.toSylow_coe] using this.symm
  rw [hT', Subgroup.mem_smul_pointwise_iff_exists]
  simp [MulAut.smul_def, MulAut.conj_apply]

theorem burnsideF4h_g2_u33_invol (x : U33G) (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    ∃ g : U33G, g * u33z * g⁻¹ = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := burnsideF4h_g2_finite_u33
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hord, pow_one]
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨h, hh⟩ := burnsideF4h_g2_sylow_conj (P : Subgroup U33G) u33Data.T P.isPGroup'
    P.not_dvd_index u33_syl.1 u33_syl.2
  have hxT : h * x * h⁻¹ ∈ u33Data.T := (hh _).2 ⟨x, hP (Subgroup.mem_zpowers x), rfl⟩
  obtain ⟨i, hi⟩ := (u33Data.mem_T_iff _).1 hxT
  have hi' : u33Tel u33GenPG i = h * x * h⁻¹ := hi
  have hinv1 : u33Tel u33GenPG i * u33Tel u33GenPG i = 1 := by
    rw [hi']
    calc h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hinv2 : u33Tel u33GenPG i ≠ 1 := by
    rw [hi']
    intro h1
    apply hx1
    have e : x = h⁻¹ * (h * x * h⁻¹) * h := by group
    rw [e, h1]
    group
  obtain ⟨g, hg⟩ := burnsideF4h_g2_invol_T i hinv1 hinv2
  refine ⟨h⁻¹ * g, ?_⟩
  rw [hi'] at hg
  calc h⁻¹ * g * u33z * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * u33z * g⁻¹) * h := by group
    _ = h⁻¹ * (h * x * h⁻¹) * h := by rw [hg]
    _ = x := by group

theorem burnsideF4h_g2_u33type_sylow {G : Type} [Group G] (ψ : U33G ≃* G) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) :
    Subgroup.normalizer (S : Set G) = S ∧ ∃ A B : Subgroup G,
      ∀ Q : Subgroup G, S ≤ Q → Q = S ∨ Q = A ∨ Q = B ∨ Q = ⊤ := by
  haveI := burnsideF4h_g2_finite_u33
  haveI : Finite G := Finite.of_equiv _ ψ.toEquiv
  have hT'p : IsPGroup 2 (u33Data.T.map ψ.toMonoidHom) := u33_syl.1.map _
  have hT'i : ¬ 2 ∣ (u33Data.T.map ψ.toMonoidHom).index := by
    have e : (u33Data.T.map ψ.toMonoidHom).index = u33Data.T.index :=
      Subgroup.index_map_equiv _ ψ
    rw [e]
    exact u33_syl.2
  obtain ⟨h, hh⟩ := burnsideF4h_g2_sylow_conj _ S hT'p hT'i hS hSi
  let e : U33G ≃* G := ψ.trans (MulAut.conj h)
  have hSe : S = u33Data.T.map e.toMonoidHom := by
    ext g
    rw [hh g]
    constructor
    · rintro ⟨s, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ψ t, ⟨t, ht, rfl⟩, rfl⟩
  obtain ⟨hN, hlat⟩ := burnsideF4h_g2_lattice_map e u33Extra.normalizer_T u33Data.lattice
  rw [hSe]
  exact ⟨hN, _, _, hlat⟩

theorem burnsideF4h_g2_u33type_invol {G : Type} [Group G] (ψ : U33G ≃* G) {x y : G}
    (hx1 : x ≠ 1) (hx2 : x * x = 1) (hy1 : y ≠ 1) (hy2 : y * y = 1) :
    ∃ c : G, c * x * c⁻¹ = y := by
  have inv1 : ∀ w : G, w ≠ 1 → ψ.symm w ≠ 1 := fun w hw h => hw (by
    have := congrArg ψ h
    simpa using this)
  have inv2 : ∀ w : G, w * w = 1 → ψ.symm w * ψ.symm w = 1 := fun w hw => by
    rw [← map_mul, hw, map_one]
  obtain ⟨g, hg⟩ := burnsideF4h_g2_u33_invol (ψ.symm x) (inv1 x hx1) (inv2 x hx2)
  obtain ⟨k, hk⟩ := burnsideF4h_g2_u33_invol (ψ.symm y) (inv1 y hy1) (inv2 y hy2)
  refine ⟨ψ (k * g⁻¹), ?_⟩
  have e : (k * g⁻¹) * ψ.symm x * (k * g⁻¹)⁻¹ = ψ.symm y := by
    rw [← hg, ← hk]
    group
  have := congrArg ψ e
  simpa [map_mul, map_inv] using this

end U33

section SmallModel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (isSimpleGroup_u33Pres u33GenP u33PresHom u33PresHom_genPG U33G u33GenPG
  g2Hom g2Hom_injective g2_derived_eq_range g2L g2L_one g2L_zero g2L_zero_eq_img g2Img_mem_range
  g2Rho g2Rho_sq g2_cover_mod two_eq_zero_of_card_two eq_zero_or_eq_one_of_card_two u33El
  g2L_mem_adjointGroup g2HomC g2IndexTwoData)

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem burnsideF4h_g2_center_u33 : Subgroup.center U33G = ⊥ := by
  haveI := isSimpleGroup_u33Pres
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center U33G) with h | h
  · exact h
  · exfalso
    have hc : u33GenPG 0 ∈ Subgroup.center U33G := by rw [h]; trivial
    have := Subgroup.mem_center_iff.1 hc (u33GenPG 3)
    have h' := congrArg u33PresHom this
    simp only [map_mul, u33PresHom_genPG] at h'
    exact (by decide +kernel : u33GenP 3 * u33GenP 0 ≠ u33GenP 0 * u33GenP 3) h'

@[expose] noncomputable def burnsideF4h_g2_iota (h2 : (2 : K) = 0)
    (hk2 : ∀ c : K, c = 0 ∨ c = 1) : U33G →* ChF.G2Native.Derived K :=
  (g2Hom h2).codRestrict _ (fun x => by
    rw [g2_derived_eq_range h2 hk2]; exact ⟨x, rfl⟩)

theorem burnsideF4h_g2_iota_injective (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    Function.Injective (burnsideF4h_g2_iota h2 hk2) :=
  fun a b hab => g2Hom_injective h2 (congrArg Subtype.val hab)

theorem burnsideF4h_g2_iota_surjective (h2 : (2 : K) = 0) (hk2 : ∀ c : K, c = 0 ∨ c = 1) :
    Function.Surjective (burnsideF4h_g2_iota h2 hk2) := by
  rintro ⟨d, hd⟩
  rw [g2_derived_eq_range h2 hk2] at hd
  obtain ⟨u, hu⟩ := hd
  exact ⟨u, Subtype.ext hu⟩

theorem burnsideF4h_g2_center_derived [Finite K] (hK : Nat.card K = 2) :
    Subgroup.center (ChF.G2Native.Derived K) = ⊥ := by
  have h2 := two_eq_zero_of_card_two hK
  have hk2 := eq_zero_or_eq_one_of_card_two hK
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨u, rfl⟩ := burnsideF4h_g2_iota_surjective h2 hk2 c
  have hu : u ∈ Subgroup.center U33G := by
    rw [Subgroup.mem_center_iff]
    intro v
    have := Subgroup.mem_center_iff.1 hc (burnsideF4h_g2_iota h2 hk2 v)
    exact burnsideF4h_g2_iota_injective h2 hk2 (by simpa [map_mul] using this)
  rw [burnsideF4h_g2_center_u33, Subgroup.mem_bot] at hu
  rw [hu, map_one]
  exact Subgroup.one_mem _

theorem burnsideF4h_g2_mk_derived_injective [Finite K] (hK : Nat.card K = 2) :
    Function.Injective (QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Derived K))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', burnsideF4h_g2_center_derived hK]

theorem burnsideF4h_g2_psi_bijective [Finite K] (hK : Nat.card K = 2) :
    Function.Bijective ((QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Derived K))).comp
      (burnsideF4h_g2_iota (two_eq_zero_of_card_two hK) (eq_zero_or_eq_one_of_card_two hK))) :=
  ⟨(burnsideF4h_g2_mk_derived_injective hK).comp (burnsideF4h_g2_iota_injective _ _),
    (QuotientGroup.mk'_surjective _).comp (burnsideF4h_g2_iota_surjective _ _)⟩

@[expose] noncomputable def burnsideF4h_g2_psi (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : U33G ≃* ChF.G2Native.SmallModel K :=
  MulEquiv.ofBijective _ (burnsideF4h_g2_psi_bijective hK)

theorem burnsideF4h_g2_card_small [Finite K] (hK : Nat.card K = 2) :
    Nat.card (ChF.G2Native.SmallModel K) = 6048 :=
  (Nat.card_congr (burnsideF4h_g2_psi K hK).toEquiv).symm.trans CFSG.Quasithin.card_u33Pres

@[expose] noncomputable def burnsideF4h_g2_incl (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : ChF.G2Native.SmallModel K →* ChF.G2Native.FullModel K :=
  QuotientGroup.lift (Subgroup.center (ChF.G2Native.Derived K))
    ((QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Parent K))).comp
      (ChF.G2Native.derivedInclusion K))
    (by
      rw [burnsideF4h_g2_center_derived hK]
      intro x hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact Subgroup.one_mem _)

theorem burnsideF4h_g2_incl_mk [Finite K] (hK : Nat.card K = 2) (d : ChF.G2Native.Derived K) :
    burnsideF4h_g2_incl K hK (d : ChF.G2Native.SmallModel K) =
      ((ChF.G2Native.derivedInclusion K d : ChF.G2Native.Parent K) :
        ChF.G2Native.FullModel K) := rfl

theorem burnsideF4h_g2_incl_mem [Finite K] (hK : Nat.card K = 2)
    (L : Subgroup (ChF.G2Native.Parent K)) (s : ChF.G2Native.SmallModel K) :
    burnsideF4h_g2_incl K hK s ∈ ChF.G2Native.fullLocal K L ↔
      s ∈ ChF.G2Native.smallLocal K L := by
  have hP : Subgroup.center (ChF.G2Native.Parent K) = ⊥ := center_adjointGroup_eq_bot
  have hD := burnsideF4h_g2_center_derived hK
  induction s using QuotientGroup.induction_on with
  | H d =>
    rw [burnsideF4h_g2_incl_mk]
    unfold ChF.G2Native.fullLocal ChF.G2Native.smallLocal ChF.G2Native.derivedLocal
    constructor
    · rintro ⟨p, hp, hpd⟩
      rw [QuotientGroup.mk'_apply] at hpd
      have h1 := QuotientGroup.eq.1 hpd
      rw [hP, Subgroup.mem_bot] at h1
      have h2 : p = ChF.G2Native.derivedInclusion K d := by
        have := congrArg (fun z => p * z) h1
        simpa using this.symm
      refine ⟨d, ?_, rfl⟩
      show ChF.G2Native.derivedInclusion K d ∈ L
      rw [← h2]
      exact hp
    · rintro ⟨d', hd', hd'd⟩
      rw [QuotientGroup.mk'_apply] at hd'd
      have h1 := QuotientGroup.eq.1 hd'd
      rw [hD, Subgroup.mem_bot] at h1
      have h2 : d' = d := by
        have := congrArg (fun z => d' * z) h1
        simpa using this.symm
      refine ⟨ChF.G2Native.derivedInclusion K d, ?_, rfl⟩
      rw [← h2]
      exact hd'

theorem burnsideF4h_g2_comap_incl [Finite K] (hK : Nat.card K = 2)
    (L : Subgroup (ChF.G2Native.Parent K)) :
    (ChF.G2Native.fullLocal K L).comap (burnsideF4h_g2_incl K hK) =
      ChF.G2Native.smallLocal K L := by
  ext s
  exact burnsideF4h_g2_incl_mem hK L s

theorem burnsideF4h_g2_smallLocal_bot :
    ChF.G2Native.smallLocal K ⊥ = ⊥ := by
  unfold ChF.G2Native.smallLocal ChF.G2Native.derivedLocal
  have : (⊥ : Subgroup (ChF.G2Native.Parent K)).comap (ChF.G2Native.derivedInclusion K) = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    rw [Subgroup.mem_comap, Subgroup.mem_bot] at hd
    rw [Subgroup.mem_bot]
    have h1 : ((ChF.G2Native.derivedInclusion K d : ChF.G2Native.Parent K) : ModGL Tag.G2 K) =
        ((1 : ChF.G2Native.Parent K) : ModGL Tag.G2 K) := by rw [hd]
    exact Subtype.ext h1
  rw [this, Subgroup.map_bot]

theorem burnsideF4h_g2_incl_injective [Finite K] (hK : Nat.card K = 2) :
    Function.Injective (burnsideF4h_g2_incl K hK) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro s hs
  have h1 : burnsideF4h_g2_incl K hK s ∈ ChF.G2Native.fullLocal K ⊥ := by
    rw [MonoidHom.mem_ker] at hs
    rw [hs]
    exact Subgroup.one_mem _
  rw [burnsideF4h_g2_incl_mem, burnsideF4h_g2_smallLocal_bot] at h1
  exact h1

theorem burnsideF4h_g2_incl_cover [Finite K] (hK : Nat.card K = 2) (q : ChF.G2Native.FullModel K) :
    ∃ s : ChF.G2Native.SmallModel K, ∃ b ∈ ChF.G2Native.fullLocal K (ChF.G2Native.positiveBorel K),
      q = burnsideF4h_g2_incl K hK s * b := by
  have h2 := two_eq_zero_of_card_two hK
  have hk2 := eq_zero_or_eq_one_of_card_two hK
  have hder : ∀ g : ModGL Tag.G2 K, g ∈ (g2Hom h2).range →
      g ∈ ⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆ := fun g hg => by
    rw [g2_derived_eq_range h2 hk2]
    exact hg
  induction q using QuotientGroup.induction_on with
  | H c =>
    rcases g2_cover_mod h2 hk2 c.2 with hA | hB
    · refine ⟨((⟨c.1, hder _ hA⟩ : ChF.G2Native.Derived K) : ChF.G2Native.SmallModel K), 1,
        Subgroup.one_mem _, ?_⟩
      rw [mul_one, burnsideF4h_g2_incl_mk]
      rfl
    · obtain ⟨u, hu⟩ := hB
      have hρ : (g2Rho h2)⁻¹ = g2Rho h2 := inv_eq_of_mul_eq_one_right (g2Rho_sq h2)
      have hc : (c : ModGL Tag.G2 K) =
          g2Hom h2 (u * (u33El "asy")⁻¹) * g2L 1 := by
        have e1 : (c : ModGL Tag.G2 K) = g2Hom h2 u * (g2Rho h2)⁻¹ :=
          eq_mul_inv_of_mul_eq hu.symm
        rw [e1, hρ]
        show _ = _
        simp only [g2Rho, map_mul, map_inv, mul_assoc]
      have hbB : (⟨g2L 1, g2L_mem_adjointGroup 1⟩ : ChF.G2Native.Parent K) ∈
          ChF.G2Native.positiveBorel K := by
        have hmem : (g2L 1 : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
          rw [g2L_one]
          exact burnsideF4h_g2_xUnit_mem_borel _ 1
        rw [← burnsideF4h_g2_map_positiveBorel] at hmem
        obtain ⟨b', hb', hbb'⟩ := hmem
        have : b' = ⟨g2L 1, g2L_mem_adjointGroup 1⟩ := Subtype.ext hbb'
        rw [← this]
        exact hb'
      refine ⟨((⟨g2Hom h2 (u * (u33El "asy")⁻¹), hder _ ⟨_, rfl⟩⟩ : ChF.G2Native.Derived K) :
        ChF.G2Native.SmallModel K), ((⟨g2L 1, g2L_mem_adjointGroup 1⟩ : ChF.G2Native.Parent K) :
          ChF.G2Native.FullModel K), ⟨_, hbB, rfl⟩, ?_⟩
      rw [burnsideF4h_g2_incl_mk, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hc

theorem burnsideF4h_g2_incl_psi [Finite K] (hK : Nat.card K = 2) :
    (burnsideF4h_g2_incl K hK).comp (burnsideF4h_g2_psi K hK).toMonoidHom =
      (QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Parent K))).comp
        (g2HomC (two_eq_zero_of_card_two hK)) := by
  ext u
  rfl

theorem burnsideF4h_g2_incl_index [Finite K] (hK : Nat.card K = 2) :
    (burnsideF4h_g2_incl K hK).range.index = 2 := by
  have h2 := two_eq_zero_of_card_two hK
  have hk2 := eq_zero_or_eq_one_of_card_two hK
  have hrange : (burnsideF4h_g2_incl K hK).range =
      (g2HomC h2).range.map (QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Parent K))) := by
    ext q
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨u, rfl⟩ := (burnsideF4h_g2_psi K hK).surjective s
      have e := congrArg (fun f => f u) (burnsideF4h_g2_incl_psi hK)
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at e
      rw [e]
      exact ⟨g2HomC h2 u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨burnsideF4h_g2_psi K hK u, ?_⟩
      have e := congrArg (fun f => f u) (burnsideF4h_g2_incl_psi hK)
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom] at e
      rw [e]
  rw [hrange]
  have hP : Subgroup.center (ChF.G2Native.Parent K) = ⊥ := center_adjointGroup_eq_bot
  have e : ((g2HomC h2).range.map
      (QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Parent K)))).index =
      (g2HomC h2).range.index :=
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk', hP]; exact bot_le)
  rw [e]
  exact (g2IndexTwoData h2 hk2).index_range

theorem burnsideF4h_g2_borel_not_le_range [Finite K] (hK : Nat.card K = 2) :
    ¬ ChF.G2Native.fullLocal K (ChF.G2Native.positiveBorel K) ≤
      (burnsideF4h_g2_incl K hK).range := by
  intro h
  have htop : (burnsideF4h_g2_incl K hK).range = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨s, b, hb, rfl⟩ := burnsideF4h_g2_incl_cover hK q
    exact mul_mem ⟨s, rfl⟩ (h hb)
  have := burnsideF4h_g2_incl_index hK
  rw [htop, Subgroup.index_top] at this
  norm_num at this

theorem burnsideF4h_g2_torusElt_one (i : Fin Tag.G2.rank) : torusElt Tag.G2 K i 1 = 1 := by
  rw [torusElt, ← weylElt_inv, mul_inv_cancel]

open scoped commutatorElement in
theorem burnsideF4h_g2_xc_mem_derived [Finite K] (hK : Nat.card K = 2) :
    pinnedX Tag.G2 K ![2, 3] 1 ∈ ⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆ := by
  have h2 := two_eq_zero_of_card_two hK
  have hk2 := eq_zero_or_eq_one_of_card_two hK
  have hle : ⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆ ≤ adjointGroup Tag.G2 K :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le le_rfl le_rfl)
  have hconj : ∀ n ∈ adjointGroup Tag.G2 K, ∀ g ∈ ⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆,
      n * g * n⁻¹ ∈ ⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆ := by
    intro n hn g hg
    have e : n * g * n⁻¹ = ⁅n, g⁆ * g := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.commutator_mem_commutator hn (hle hg)) hg
  have hn : burnsideF4h_g2_wordUnit K [⟨1, by decide⟩, ⟨0, by decide⟩] ∈ adjointGroup Tag.G2 K :=
    Subgroup.list_prod_mem _ fun g hg => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
      exact weylElt_mem_adjointGroup i 1
  have hmap := burnsideF4h_g2_map_conj_wordUnit (K := K) [⟨1, by decide⟩, ⟨0, by decide⟩]
    ⟨0, by decide⟩
  have e : burnsideF4h_g2_reflect [⟨1, by decide⟩, ⟨0, by decide⟩]
      (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) = ![2, 3] :=
    List.ofFn_injective (by decide +kernel)
  rw [e] at hmap
  have hmem : pinnedX Tag.G2 K ![2, 3] 1 ∈ (rootSubgroup Tag.G2 K
      (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1)).map
      (MulAut.conj (burnsideF4h_g2_wordUnit K [⟨1, by decide⟩, ⟨0, by decide⟩])).toMonoidHom := by
    rw [hmap]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hy
  have hyA : pinnedX Tag.G2 K (Pi.single (⟨0, by decide⟩ : Fin Tag.G2.rank) 1) t ∈
      ⁅adjointGroup Tag.G2 K, adjointGroup Tag.G2 K⁆ := by
    rcases hk2 t with rfl | rfl
    · rw [pinnedX_zero]
      exact Subgroup.one_mem _
    · rw [pinnedX_single, ← g2L_zero, g2L_zero_eq_img, g2_derived_eq_range h2 hk2]
      exact g2Img_mem_range h2 2
  rw [← hyx]
  exact hconj _ hn _ hyA

theorem burnsideF4h_g2_small_longRoot_invol [Finite K] (hK : Nat.card K = 2) :
    ∃ z ∈ ChF.G2Native.smallLocal K (ChF.G2Native.longRoot K), z ≠ 1 ∧ z * z = 1 := by
  have h2 := two_eq_zero_of_card_two hK
  let d : ChF.G2Native.Derived K := ⟨pinnedX Tag.G2 K ![2, 3] 1, burnsideF4h_g2_xc_mem_derived hK⟩
  have hd : ChF.G2Native.derivedInclusion K d ∈ ChF.G2Native.longRoot K := by
    have hL : ChF.G2Native.longRoot K =
        (rootSubgroup Tag.G2 K ![2, 3]).subgroupOf (adjointGroup Tag.G2 K) := by
      unfold ChF.G2Native.longRoot ChF.G2Native.highestLong
      exact burnsideF4h_g2_rootSubgroup_eq burnsideF4h_g2_cRoot_isRoot
    rw [hL, Subgroup.mem_subgroupOf]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩
  have hd1 : d ≠ 1 := by
    intro h
    have h' := congrArg Subtype.val h
    have h0 : pinnedX Tag.G2 K ![2, 3] 1 = pinnedX Tag.G2 K ![2, 3] 0 :=
      h'.trans (pinnedX_zero Tag.G2 K ![2, 3]).symm
    exact one_ne_zero (pinnedX_injective Tag.G2 K _ h0)
  have hd2 : d * d = 1 := by
    apply Subtype.ext
    have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    have e := pinnedX_add Tag.G2 K (![2, 3] : Fin Tag.G2.rank → ℤ) (1 : K) 1
    have e0 := pinnedX_zero Tag.G2 K (![2, 3] : Fin Tag.G2.rank → ℤ)
    exact e.symm.trans ((congrArg (pinnedX Tag.G2 K (![2, 3] : Fin Tag.G2.rank → ℤ)) h11).trans e0)
  refine ⟨(d : ChF.G2Native.SmallModel K), ⟨d, hd, rfl⟩, ?_, ?_⟩
  · intro h
    apply hd1
    apply burnsideF4h_g2_mk_derived_injective hK
    rw [map_one]
    exact h
  · rw [← QuotientGroup.mk_mul, hd2]
    rfl

end SmallModel

section SmallCard

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

theorem burnsideF4h_g2_card_positiveBorel [Finite K] (hK : Nat.card K = 2) :
    Nat.card (ChF.G2Native.positiveBorel K) = 64 := by
  have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have hsub : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 h1).1
  have htor : torusGroup Tag.G2 K = ⊥ := by
    rw [eq_bot_iff]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    rw [Subsingleton.elim t 1]
    show torusElt Tag.G2 K i 1 ∈ (⊥ : Subgroup (ModGL Tag.G2 K))
    rw [burnsideF4h_g2_torusElt_one]
    exact Subgroup.one_mem _
  have hB : borelGroup Tag.G2 K = posUnipotent Tag.G2 K := by
    show torusGroup Tag.G2 K ⊔ posUnipotent Tag.G2 K = _
    rw [htor, bot_sup_eq]
  have h2 : Nat.card ((ChF.G2Native.positiveBorel K).map (adjointGroup Tag.G2 K).subtype) =
      Nat.card (ChF.G2Native.positiveBorel K) :=
    Subgroup.card_map_of_injective (adjointGroup Tag.G2 K).subtype_injective
  rw [← h2, burnsideF4h_g2_map_positiveBorel, hB, card_posUnipotent, hK,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_G2]
  norm_num

theorem burnsideF4h_g2_card_fullBorel [Finite K] (hK : Nat.card K = 2) :
    Nat.card (ChF.G2Native.fullLocal K (ChF.G2Native.positiveBorel K)) = 64 := by
  have hP : Subgroup.center (ChF.G2Native.Parent K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center (ChF.G2Native.Parent K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hP]
  unfold ChF.G2Native.fullLocal
  rw [Subgroup.card_map_of_injective hinj, burnsideF4h_g2_card_positiveBorel hK]

theorem burnsideF4h_g2_small_sylow [Finite K] (hK : Nat.card K = 2) :
    IsPGroup 2 (ChF.G2Native.smallLocal K (ChF.G2Native.positiveBorel K)) ∧
      ¬ 2 ∣ (ChF.G2Native.smallLocal K (ChF.G2Native.positiveBorel K)).index := by
  set ι := burnsideF4h_g2_incl K hK
  set Bf := ChF.G2Native.fullLocal K (ChF.G2Native.positiveBorel K)
  set S := ChF.G2Native.smallLocal K (ChF.G2Native.positiveBorel K)
  have hS : S = Bf.comap ι := (burnsideF4h_g2_comap_incl hK _).symm
  have hBf : Nat.card Bf = 64 := burnsideF4h_g2_card_fullBorel hK
  have hBp : IsPGroup 2 Bf := IsPGroup.of_card (n := 6) (by rw [hBf]; norm_num)
  have hinj := burnsideF4h_g2_incl_injective hK
  have hSp : IsPGroup 2 S := by
    rw [hS]
    exact hBp.comap_of_injective ι hinj
  have hcardS : Nat.card S = Nat.card ↥(ι.range ⊓ Bf) := by
    rw [← Subgroup.map_comap_eq, ← hS]
    exact (Subgroup.card_map_of_injective hinj).symm
  have h64 := burnsideF4h_g2_card_le_two_mul ι.range Bf (burnsideF4h_g2_incl_index hK)
  rw [hBf, ← hcardS] at h64
  have hcard : Nat.card (ChF.G2Native.SmallModel K) = 6048 := burnsideF4h_g2_card_small hK
  haveI : Finite (ChF.G2Native.SmallModel K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hSle : Nat.card S ∣ 6048 := hcard ▸ Subgroup.card_subgroup_dvd_card S
  obtain ⟨n, hn⟩ := hSp.exists_card_eq
  have hn5 : n = 5 := by
    rw [hn] at hSle h64
    have h1 : 5 ≤ n := by
      by_contra hc
      have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2' : n ≤ 5 := by
      by_contra hc
      have h64' : 2 ^ 6 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have := dvd_trans h64' hSle
      omega
    omega
  have hS32 : Nat.card S = 32 := by rw [hn, hn5]; norm_num
  refine ⟨hSp, ?_⟩
  have h := Subgroup.card_mul_index S
  rw [hS32, hcard] at h
  have : S.index = 189 := by omega
  rw [this]
  norm_num

end SmallCard

section


theorem burnsideF4h_g2_small (K : Type) [Field K] : ChF.G2Native.smallCompatibilityGoal K := by
  unfold ChF.G2Native.smallCompatibilityGoal
  intro hK
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hcomap := burnsideF4h_g2_comap_incl hK
  have hB := burnsideF4h_g2_fullLocal_borel (K := K)
  have hP1 := burnsideF4h_g2_fullLocal_point (K := K)
  have hP2 := burnsideF4h_g2_fullLocal_line (K := K)
  have eS : ChF.G2Native.smallLocal K (ChF.G2Native.positiveBorel K) =
      (burnsideF4h_g2_sys K).B.comap (burnsideF4h_g2_incl K hK) := by
    rw [← hB, hcomap]
  have e1 : ChF.G2Native.smallLocal K (ChF.G2Native.pointParabolic K) =
      (burnsideF4h_g2_sys K).P₁.comap (burnsideF4h_g2_incl K hK) := by
    rw [← hP1, hcomap]
  have e2 : ChF.G2Native.smallLocal K (ChF.G2Native.lineParabolic K) =
      (burnsideF4h_g2_sys K).P₂.comap (burnsideF4h_g2_incl K hK) := by
    rw [← hP2, hcomap]
  have hcov : ∀ q, ∃ s, ∃ b ∈ (burnsideF4h_g2_sys K).B, q = burnsideF4h_g2_incl K hK s * b := by
    intro q
    obtain ⟨s, b, hb, h⟩ := burnsideF4h_g2_incl_cover hK q
    exact ⟨s, b, hB ▸ hb, h⟩
  have hBP1 : (burnsideF4h_g2_sys K).B ≤ (burnsideF4h_g2_sys K).P₁ :=
    CFSG.Quasithin.H13.F431.BN.B_le_P _ true
  have hBP2 : (burnsideF4h_g2_sys K).B ≤ (burnsideF4h_g2_sys K).P₂ :=
    CFSG.Quasithin.H13.F431.BN.B_le_P _ false
  have hinj : ∀ {X Y : Subgroup (ChF.G2Native.FullModel K)}, (burnsideF4h_g2_sys K).B ≤ X →
      (burnsideF4h_g2_sys K).B ≤ Y → X.comap (burnsideF4h_g2_incl K hK) =
        Y.comap (burnsideF4h_g2_incl K hK) → X = Y :=
    fun hX hY h => burnsideF4h_g2_comap_injective _ hcov hX hY h
  have hB1 : (burnsideF4h_g2_sys K).B ≠ (burnsideF4h_g2_sys K).P₁ := fun h =>
    CFSG.Quasithin.H13.F431.BN.not_le_P (burnsideF4h_g2_sys K) true (by
      show (burnsideF4h_g2_sys K).P₁ ≤ (burnsideF4h_g2_sys K).P₂
      rw [← h]
      exact hBP2)
  have hB2 : (burnsideF4h_g2_sys K).B ≠ (burnsideF4h_g2_sys K).P₂ := fun h =>
    CFSG.Quasithin.H13.F431.BN.not_le_P (burnsideF4h_g2_sys K) false (by
      show (burnsideF4h_g2_sys K).P₂ ≤ (burnsideF4h_g2_sys K).P₁
      rw [← h]
      exact hBP1)
  have hsyl := burnsideF4h_g2_small_sylow hK
  obtain ⟨hN, A, B', hlat⟩ :=
    burnsideF4h_g2_u33type_sylow (burnsideF4h_g2_psi K hK) hsyl.1 hsyl.2
  have hS : ChF.IsSylowOf 2 (ChF.G2Native.smallLocal K (ChF.G2Native.positiveBorel K)) ⊤ :=
    ⟨le_top, hsyl.1, by rw [Subgroup.relIndex_top_right]; exact hsyl.2⟩
  obtain ⟨hLie, hsup⟩ := burnsideF4h_g2_isLie_of_lattice
    (P₁ := ChF.G2Native.smallLocal K (ChF.G2Native.pointParabolic K))
    (P₂ := ChF.G2Native.smallLocal K (ChF.G2Native.lineParabolic K)) hS hN hlat
    (by rw [eS, e1]; exact Subgroup.comap_mono hBP1)
    (by rw [eS, e2]; exact Subgroup.comap_mono hBP2)
    (by
      rw [e1, e2]
      intro h
      exact CFSG.Quasithin.H13.F431.BN.P₁_ne_P₂ _ (hinj hBP1 hBP2 h))
    (by
      rw [e1, eS]
      intro h
      exact hB1 (hinj hBP1 le_rfl h).symm)
    (by
      rw [e2, eS]
      intro h
      exact hB2 (hinj hBP2 le_rfl h).symm)
    (by
      rw [e1]
      intro h
      exact CFSG.Quasithin.H13.F431.BN.P_ne_top (burnsideF4h_g2_sys K) true
        (hinj hBP1 le_top (h.trans (Subgroup.comap_top _).symm)))
    (by
      rw [e2]
      intro h
      exact CFSG.Quasithin.H13.F431.BN.P_ne_top (burnsideF4h_g2_sys K) false
        (hinj hBP2 le_top (h.trans (Subgroup.comap_top _).symm)))
    (by rw [e1, e2, eS, ← Subgroup.comap_inf, CFSG.Quasithin.H13.F431.BN.P₁_inf_P₂])
  refine ⟨hLie, hsup, fun x y hx hy => ?_⟩
  unfold ChF.G2Native.smallInvolution at hx hy
  exact burnsideF4h_g2_u33type_invol (burnsideF4h_g2_psi K hK) hx.1 hx.2 hy.1 hy.2

end

section


theorem burnsideF4h_g2_parent (K : Type) [Field K] : ChF.G2Native.smallParentAssemblyGoal K := by
  unfold ChF.G2Native.smallParentAssemblyGoal
  intro hK
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hcomap := burnsideF4h_g2_comap_incl hK
  have hmap : ∀ L : Subgroup (ChF.G2Native.Parent K),
      (ChF.G2Native.smallLocal K L).map (burnsideF4h_g2_incl K hK) =
        (burnsideF4h_g2_incl K hK).range ⊓ ChF.G2Native.fullLocal K L := fun L => by
    rw [← hcomap, Subgroup.map_comap_eq]
  have hidx := burnsideF4h_g2_incl_index hK
  have hnot : ∀ L : Subgroup (ChF.G2Native.Parent K), ChF.G2Native.positiveBorel K ≤ L →
      ¬ ChF.G2Native.fullLocal K L ≤ (burnsideF4h_g2_incl K hK).range := fun L hL h =>
    burnsideF4h_g2_borel_not_le_range hK ((Subgroup.map_mono hL).trans h)
  refine ⟨burnsideF4h_g2_incl K hK, burnsideF4h_g2_incl_injective hK, hidx, fun d => rfl,
    hmap _, hmap _, hmap _, ?_, ?_⟩
  · rw [hmap, Subgroup.inf_relIndex_right]
    exact burnsideF4h_g2_relIndex_eq_two hidx (hnot _ le_sup_left)
  · rw [hmap, Subgroup.inf_relIndex_right]
    exact burnsideF4h_g2_relIndex_eq_two hidx (hnot _ le_sup_left)

end

section


theorem burnsideF4h_inv_G2d (degree : ℕ) (E : Type) [Group E] (core : Subgroup E)
    (chart : ChF.NativeChart .G2d 2 degree core) :
    (∃ representative ∈ chart.longRoot, representative ≠ 1 ∧
        representative * representative = 1) ∧
      ∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element := by
  rcases chart.coordinates with
    ⟨c, hk, -⟩ | ⟨hk, -⟩ | ⟨-, -, -, K, fK, finK, card, marking, -, -, -, h4, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K', fK', finK', charK', scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · exact absurd hk (by cases c <;> decide)
  · exact absurd hk (by decide)
  · letI := fK
    haveI := finK
    obtain ⟨z, hz, hz1, hz2⟩ := burnsideF4h_g2_small_longRoot_invol (K := K) card
    have hmemL : ∀ s ∈ ChF.G2Native.smallLocal K (ChF.G2Native.longRoot K),
        ((marking s : core) : E) ∈ chart.longRoot := by
      intro s hs
      rw [h4]
      exact ⟨marking s, ⟨s, hs, rfl⟩, rfl⟩
    have hinjE : ∀ s t : ChF.G2Native.SmallModel K, ((marking s : core) : E) =
        ((marking t : core) : E) → s = t := fun s t h =>
      marking.injective (Subtype.ext h)
    refine ⟨⟨((marking z : core) : E), hmemL z hz, ?_, ?_⟩, fun e he he1 he2 => ?_⟩
    · intro h
      apply hz1
      apply hinjE
      rw [h, map_one]
      rfl
    · rw [← Subgroup.coe_mul, ← map_mul, hz2, map_one]
      rfl
    · obtain ⟨s, hs⟩ := marking.surjective ⟨e, he⟩
      have hse : ((marking s : core) : E) = e := by rw [hs]
      have hs1 : s ≠ 1 := by
        rintro rfl
        apply he1
        rw [← hse, map_one]
        rfl
      have hs2 : s * s = 1 := by
        apply hinjE
        rw [map_mul, Subgroup.coe_mul, hse, he2, map_one]
        rfl
      obtain ⟨c, hc⟩ := burnsideF4h_g2_u33type_invol (burnsideF4h_g2_psi K card) hs1 hs2 hz1 hz2
      unfold ChF.NativeChart.RootInvolution
      refine ⟨he, he1, he2, fun _ => rfl, ((marking c : core) : E), (marking c).2, ?_⟩
      have key : ((marking c : core) : E) * e * ((marking c : core) : E)⁻¹ =
          ((marking z : core) : E) := by
        rw [← hc, ← hse, map_mul, map_mul, map_inv]
        rfl
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [key]
      exact hmemL z hz
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

end

section


theorem burnsideF4h_g2_small_normalizer (K : Type) [Field K] (hK : Nat.card K = 2) :
    ChF.G2Native.smallLocal K (ChF.G2Native.pointParabolic K) ≤
      Subgroup.normalizer ((ChF.G2Native.smallLocal K (ChF.G2Native.longRoot K) :
        Subgroup (ChF.G2Native.SmallModel K)) : Set (ChF.G2Native.SmallModel K)) :=
  burnsideF4h_g2_smallLocal_point_le_normalizer

end

end PartBurnsideF4hG2b

section PartBurnsideF4hRee

section BNGeneric

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN
open scoped Pointwise

variable {X : Type} [Group X] {n : ℕ}

theorem burnsideF4h_ree_isLieParabolics_of_system [Finite X] (D : RankTwoSystem X n)
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf D.U ⊤) :
    ChF.IsLieParabolics 2 (⊤ : Subgroup X) D.B D.P₁ D.P₂ := by
  refine ⟨⟨D.U, hU, ?_⟩, P₁_ne_P₂ D, P₁_inf_P₂ D, fun Q => ⟨?_, ?_⟩⟩
  · rw [top_inf_eq, normalizer_U_eq_B D]
  · rintro ⟨hBQ, -, hQ, hmax⟩
    have key : ∀ i : Bool, Q ≤ P D i → Q = P D i := by
      intro i h
      by_contra hne
      exact P_ne_top D i (hmax _ (lt_of_le_of_ne h hne) le_top)
    rcases over_of_ne_top D hBQ hQ with h | h
    · exact Or.inl (key true h)
    · exact Or.inr (key false h)
  · have key : ∀ i : Bool, D.B ≤ P D i ∧ P D i ≤ ⊤ ∧ P D i ≠ ⊤ ∧
        ∀ R : Subgroup X, P D i < R → R ≤ ⊤ → R = ⊤ :=
      fun i => ⟨B_le_P D i, le_top, P_ne_top D i, fun R hR _ => (isCoatom_P D i).2 R hR⟩
    rintro (rfl | rfl)
    · exact key true
    · exact key false

theorem burnsideF4h_ree_eq_one_of_conj_mem (D : RankTwoSystem X n) {g : X}
    (h : ∀ x : X, x * g * x⁻¹ ∈ D.B) : g = 1 := by
  apply D.faithful
  have key : ∀ (Pp : Subgroup X), D.B ≤ Pp → ∀ x : X,
      (Pp : Set X) * ({x} : Set X) * ({g} : Set X) = (Pp : Set X) * ({x} : Set X) := by
    intro Pp hPp x
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy
      obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.1 ha
      rw [Set.mem_singleton_iff] at hb hc
      rw [hb, hc]
      exact Set.mem_mul.2 ⟨p * (x * g * x⁻¹), Pp.mul_mem hp (hPp (h x)), x, rfl, by group⟩
    · intro hy
      obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.1 hy
      rw [Set.mem_singleton_iff] at hc
      rw [hc]
      refine Set.mem_mul.2 ⟨p * (x * g * x⁻¹)⁻¹ * x, Set.mem_mul.2
        ⟨p * (x * g * x⁻¹)⁻¹, Pp.mul_mem hp (Pp.inv_mem (hPp (h x))), x, rfl, rfl⟩, g, rfl, ?_⟩
      group
  intro v hv
  rcases hv with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact key D.P₁ (B_le_P D true) x
  · exact key D.P₂ (B_le_P D false) x

theorem burnsideF4h_ree_center_eq_bot (D : RankTwoSystem X n) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hc : ∀ g : X, g * z * g⁻¹ = z := fun g => by
    rw [Subgroup.mem_center_iff.1 hz g, mul_inv_cancel_right]
  have hzN : z ∈ Subgroup.normalizer (D.U : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have e : z * u * z⁻¹ = u := by
      rw [← Subgroup.mem_center_iff.1 hz u, mul_inv_cancel_right]
    rw [e]
  apply burnsideF4h_ree_eq_one_of_conj_mem D
  intro x
  rw [hc x, ← normalizer_U_eq_B D]
  exact hzN

theorem burnsideF4h_ree_intList_self (a : ℤ) : intList a a = [a] := by
  simp [intList]

theorem burnsideF4h_ree_card_P [Finite X] (D : RankTwoSystem X n) (i : Bool) :
    Nat.card (P D i) =
      Nat.card D.B * (1 + Nat.card (D.UwMinusSub (D.lift (gen D.w₁ D.w₂ i)))) := by
  set m := D.lift (gen D.w₁ D.w₂ i) with hm
  have hdc : ∀ (b : D.B) (u : D.UwMinusSub m), (b : X) * (m : X) * u ∈ P D i := fun b u =>
    (mem_P_iff D).2 (Or.inr ((D.mem_dc_iff_coord m (D.lift_mk _)).2 ⟨b, b.2, u, u.2, rfl⟩))
  let f : D.B ⊕ (D.B × D.UwMinusSub m) → P D i := fun s =>
    match s with
    | Sum.inl b => ⟨b, B_le_P D i b.2⟩
    | Sum.inr bu => ⟨(bu.1 : X) * (m : X) * bu.2, hdc bu.1 bu.2⟩
  have hnotB : ∀ (b : D.B) (u : D.UwMinusSub m), (b : X) * (m : X) * u ∉ D.B := fun b u =>
    D.rank2.not_mem_B_of_mem_dc (D.rank2.gen_mem i)
      ((D.mem_dc_iff_coord m (D.lift_mk _)).2 ⟨b, b.2, u, u.2, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun s t hst => ?_, fun x => ?_⟩
    · rcases s with b | ⟨b, u⟩ <;> rcases t with b' | ⟨b', u'⟩
      · have h := congrArg Subtype.val hst
        exact congrArg Sum.inl (Subtype.ext h)
      · exfalso
        have h : (b : X) = (b' : X) * (m : X) * u' := congrArg Subtype.val hst
        exact hnotB b' u' (h ▸ b.2)
      · exfalso
        have h : (b : X) * (m : X) * u = (b' : X) := congrArg Subtype.val hst
        exact hnotB b u (h ▸ b'.2)
      · have h : (b : X) * (m : X) * u = (b' : X) * (m : X) * u' := congrArg Subtype.val hst
        have hu : (u : X) = u' := D.coord_unique m b.2 b'.2 u.2 u'.2 h
        have hb : (b : X) = b' := by
          rw [hu] at h
          exact mul_right_cancel (mul_right_cancel h)
        rw [Subtype.ext hb, Subtype.ext hu]
    · rcases (mem_P_iff D).1 x.2 with hB | hd
      · exact ⟨Sum.inl ⟨x, hB⟩, rfl⟩
      · obtain ⟨b, hb, u, hu, hx⟩ := (D.mem_dc_iff_coord m (D.lift_mk _)).1 hd
        exact ⟨Sum.inr (⟨b, hb⟩, ⟨u, hu⟩), Subtype.ext hx.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum, Nat.card_prod]
  ring

theorem burnsideF4h_ree_UwMinus_true (D : RankTwoSystem X n) :
    ((D.UwMinusSub (D.lift (gen D.w₁ D.w₂ true)) : Subgroup X) : Set X) = (D.root 1 : Set X) := by
  have h := (D.eq30_5_A (i := 1) (by have := D.three_le; omega)
    (D.lift (gen D.w₁ D.w₂ true)) (by rw [D.lift_mk, altWord_one]; rfl)).1
  show D.UwMinus _ = _
  rw [h, show ((1 : ℕ) : ℤ) = 1 by rfl, burnsideF4h_ree_intList_self]
  simp [chainProd, mul_one]

theorem burnsideF4h_ree_UwMinus_false (D : RankTwoSystem X n) :
    ((D.UwMinusSub (D.lift (gen D.w₁ D.w₂ false)) : Subgroup X) : Set X) =
      (D.root n : Set X) := by
  have h := (D.eq30_5_B (i := 1) (by have := D.three_le; omega)
    (D.lift (gen D.w₁ D.w₂ false)) (by rw [D.lift_mk, altWord_one]; rfl)).1
  show D.UwMinus _ = _
  rw [h, show (n : ℤ) - ((1 : ℕ) : ℤ) + 1 = n by push_cast; ring, burnsideF4h_ree_intList_self]
  simp [chainProd, mul_one]

theorem burnsideF4h_ree_relIndex_P [Finite X] (D : RankTwoSystem X n) (i : Bool) :
    D.B.relIndex (P D i) = 1 + Nat.card (D.UwMinusSub (D.lift (gen D.w₁ D.w₂ i))) := by
  have h := Subgroup.relIndex_mul_card D.B (P D i)
  rw [inf_of_le_left (B_le_P D i), burnsideF4h_ree_card_P D i, mul_comm (Nat.card D.B)] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem burnsideF4h_ree_relIndex_P₁ [Finite X] (D : RankTwoSystem X n) :
    D.B.relIndex D.P₁ = 1 + Nat.card (D.root 1) := by
  have h := burnsideF4h_ree_relIndex_P D true
  have e : D.UwMinusSub (D.lift (gen D.w₁ D.w₂ true)) ≃ D.root 1 :=
    Equiv.subtypeEquivRight (fun x => Set.ext_iff.1 (burnsideF4h_ree_UwMinus_true D) x)
  rw [Nat.card_congr e] at h
  exact h

theorem burnsideF4h_ree_relIndex_P₂ [Finite X] (D : RankTwoSystem X n) :
    D.B.relIndex D.P₂ = 1 + Nat.card (D.root n) := by
  have h := burnsideF4h_ree_relIndex_P D false
  have e : D.UwMinusSub (D.lift (gen D.w₁ D.w₂ false)) ≃ D.root n :=
    Equiv.subtypeEquivRight (fun x => Set.ext_iff.1 (burnsideF4h_ree_UwMinus_false D) x)
  rw [Nat.card_congr e] at h
  exact h

end BNGeneric

section Transport

theorem burnsideF4h_ree_isLieParabolics_map {E M : Type} [Group E] [Group M] (φ : M →* E)
    (hφ : Function.Injective φ) {p : ℕ} {B P₁ P₂ : Subgroup M}
    (h : ChF.IsLieParabolics p (⊤ : Subgroup M) B P₁ P₂) :
    ChF.IsLieParabolics p ((⊤ : Subgroup M).map φ) (B.map φ) (P₁.map φ) (P₂.map φ) := by
  obtain ⟨⟨S, ⟨hSle, hSp, hSidx⟩, hB⟩, hne, hinf, hmax⟩ := h
  have hcm : ∀ A : Subgroup E, A ≤ (⊤ : Subgroup M).map φ → A = (A.comap φ).map φ := by
    intro A hA
    rw [Subgroup.map_comap_eq]
    rw [← MonoidHom.range_eq_map] at hA
    exact (inf_eq_right.2 hA).symm
  refine ⟨⟨S.map φ, ⟨Subgroup.map_mono hSle, hSp.map φ, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact hSidx
  · ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine Subgroup.mem_inf.2 ⟨⟨b, Subgroup.mem_top _, rfl⟩, ?_⟩
      have hb' : b ∈ (⊤ : Subgroup M) ⊓ Subgroup.normalizer (S : Set M) := hB ▸ hb
      have hbN : b ∈ Subgroup.normalizer (S : Set M) := (Subgroup.mem_inf.1 hb').2
      exact Subgroup.le_normalizer_map φ ⟨b, hbN, rfl⟩
    · intro hx
      obtain ⟨⟨m, -, rfl⟩, hxN⟩ := Subgroup.mem_inf.1 hx
      refine ⟨m, ?_, rfl⟩
      rw [hB]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro s
      have h1 := Subgroup.mem_normalizer_iff.1 hxN (φ s)
      rw [← map_mul, ← map_inv, ← map_mul] at h1
      have h2 : φ s ∈ S.map φ ↔ s ∈ S := by
        constructor
        · rintro ⟨t, ht, hts⟩
          rwa [← hφ hts]
        · intro hs
          exact ⟨s, hs, rfl⟩
      have h3 : φ (m * s * m⁻¹) ∈ S.map φ ↔ m * s * m⁻¹ ∈ S := by
        constructor
        · rintro ⟨t, ht, hts⟩
          rwa [← hφ hts]
        · intro hs
          exact ⟨_, hs, rfl⟩
      rw [← h2, h1, h3]
  · exact fun e => hne (Subgroup.map_injective hφ e)
  · rw [← Subgroup.map_inf_eq _ _ _ hφ, hinf]
  · intro Q
    have hP1 := (hmax P₁).2 (Or.inl rfl)
    have hP2 := (hmax P₂).2 (Or.inr rfl)
    have hTopInj : ∀ R : Subgroup M, R.map φ = (⊤ : Subgroup M).map φ → R = ⊤ :=
      fun R hR => Subgroup.map_injective hφ hR
    constructor
    · rintro ⟨hBQ, hQH, hQne, hQmax⟩
      have hQe := hcm Q hQH
      set Q₀ := Q.comap φ with hQ₀
      have hBQ₀ : B ≤ Q₀ := Subgroup.map_le_iff_le_comap.1 hBQ
      have hQ₀ne : Q₀ ≠ ⊤ := by
        intro e
        apply hQne
        rw [hQe, e]
      have hQ₀max : ∀ R₀ : Subgroup M, Q₀ < R₀ → R₀ ≤ ⊤ → R₀ = ⊤ := by
        rintro R₀ hR₀ -
        have hlt : Q < R₀.map φ := by
          refine lt_of_le_of_ne ?_ ?_
          · rw [hQe]
            exact Subgroup.map_mono hR₀.le
          · intro e
            have : Q₀ = R₀ := Subgroup.map_injective hφ (by rw [← hQe, e])
            exact hR₀.ne this
        exact hTopInj _ (hQmax _ hlt (Subgroup.map_mono le_top))
      rcases (hmax Q₀).1 ⟨hBQ₀, le_top, hQ₀ne, hQ₀max⟩ with e | e
      · exact Or.inl (by rw [hQe, e])
      · exact Or.inr (by rw [hQe, e])
    · intro hQ
      have key : ∀ P : Subgroup M,
          (B ≤ P ∧ P ≤ ⊤ ∧ P ≠ ⊤ ∧ ∀ R : Subgroup M, P < R → R ≤ ⊤ → R = ⊤) →
          (B.map φ ≤ P.map φ ∧ P.map φ ≤ (⊤ : Subgroup M).map φ ∧
            P.map φ ≠ (⊤ : Subgroup M).map φ ∧
            ∀ R : Subgroup E, P.map φ < R → R ≤ (⊤ : Subgroup M).map φ →
              R = (⊤ : Subgroup M).map φ) := by
        rintro P ⟨hBP, -, hPne, hPmax⟩
        refine ⟨Subgroup.map_mono hBP, Subgroup.map_mono le_top, fun e => hPne (hTopInj _ e), ?_⟩
        intro R hR hRH
        have hRe := hcm R hRH
        have hlt : P < R.comap φ := by
          refine lt_of_le_of_ne (Subgroup.map_le_iff_le_comap.1 hR.le) ?_
          intro e
          apply hR.ne
          rw [hRe, ← e]
        have := hPmax _ hlt le_top
        rw [hRe, this]
      rcases hQ with rfl | rfl
      · exact key _ hP1
      · exact key _ hP2

theorem burnsideF4h_ree_isLieParabolics_equiv {E M : Type} [Group E] [Group M] (Φ : M ≃* E)
    {p : ℕ} {B P₁ P₂ : Subgroup M} (h : ChF.IsLieParabolics p (⊤ : Subgroup M) B P₁ P₂) :
    ChF.IsLieParabolics p (⊤ : Subgroup E) (B.map Φ.toMonoidHom) (P₁.map Φ.toMonoidHom)
      (P₂.map Φ.toMonoidHom) := by
  have h' := burnsideF4h_ree_isLieParabolics_map Φ.toMonoidHom Φ.injective h
  rwa [Subgroup.map_top_of_surjective _ Φ.surjective] at h'

theorem burnsideF4h_ree_le_normalizer_map {E M : Type} [Group E] [Group M] (φ : M →* E)
    {P L : Subgroup M} (h : P ≤ Subgroup.normalizer (L : Set M)) :
    P.map φ ≤ Subgroup.normalizer ((L.map φ : Subgroup E) : Set E) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.le_normalizer_map φ ⟨x, h hx, rfl⟩

theorem burnsideF4h_ree_exists_quotEquiv {G : Type} [Group G] (hz : Subgroup.center G = ⊥) :
    ∃ e : G ≃* (G ⧸ Subgroup.center G), ∀ x : G, e x = (x : G ⧸ Subgroup.center G) :=
  ⟨MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center G))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hz]),
      QuotientGroup.mk'_surjective _⟩, fun _ => rfl⟩

theorem burnsideF4h_ree_le_normalizer_subgroupOf {E : Type} [Group E] {Γ P L : Subgroup E}
    (h : P ≤ Subgroup.normalizer (L : Set E)) :
    P.subgroupOf Γ ≤ Subgroup.normalizer ((L.subgroupOf Γ : Subgroup Γ) : Set Γ) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.1 (h (Subgroup.mem_subgroupOf.1 hx)) (y : E)
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact h1

theorem burnsideF4h_ree_le_normalizer_of_conj {E : Type} [Group E] {P L : Subgroup E}
    (h : ∀ g ∈ P, ∀ x ∈ L, g * x * g⁻¹ ∈ L) : P ≤ Subgroup.normalizer (L : Set E) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (P.inv_mem hg) _ hx
  simpa [mul_assoc] using this

end Transport

local instance burnsideF4h_ree_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

section WeylBasic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable {tag : Tag} {K : Type}
  [Field K]

theorem burnsideF4h_ree_weylWordOperator_eq (word : List (Fin tag.rank)) :
    weylWordOperator tag K word =
      ((((word.map fun i => weylElt tag K i 1).reverse).prod : (Module.End K (RootModule tag K))ˣ) :
        Module.End K (RootModule tag K)) := by
  unfold weylWordOperator
  have h := map_list_prod (Units.coeHom (Module.End K (RootModule tag K)))
    ((word.map fun i => weylElt tag K i 1).reverse)
  simp only [Units.coeHom_apply, List.map_reverse, List.map_map] at h
  rw [h]
  rfl

theorem burnsideF4h_ree_rootSubgroup_le_absoluteRoot {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    rootSubgroup tag K α ≤ absoluteRoot tag K α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine Subgroup.subset_closure ⟨(pinnedData tag α).2.2 • c, (pinnedData tag α).1,
    (pinnedData tag α).2.1.map tag.idx, pinnedWeyl tag K α, ?_, ?_, ?_⟩
  · rw [List.foldl_map]
    exact foldl_reflect_pinnedData hα
  · rw [burnsideF4h_ree_weylWordOperator_eq]
    congr 1
    unfold pinnedWeyl
    rw [List.map_map]
    rfl
  · rfl

theorem burnsideF4h_ree_absoluteTorus_eq : absoluteTorus tag K = torusGroup tag K := by
  unfold absoluteTorus torusGroup
  congr 1
  ext e
  constructor
  · rintro ⟨i, p, h⟩
    exact ⟨(i, p), (Units.ext h).symm⟩
  · rintro ⟨⟨i, p⟩, rfl⟩
    exact ⟨i, p, rfl⟩

theorem burnsideF4h_ree_relativeWeyl_eq (word : List (Fin tag.rank)) :
    relativeWeyl tag K word =
      Subgroup.zpowers ((word.map fun i => weylElt tag K i 1).reverse.prod) := by
  unfold relativeWeyl
  rw [Subgroup.zpowers_eq_closure]
  congr 1
  ext e
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [burnsideF4h_ree_weylWordOperator_eq]
  exact ⟨fun h => Units.ext h, fun h => h ▸ rfl⟩

theorem burnsideF4h_ree_comm_zero_three :
    weylElt Tag.F4 K 3 1 * weylElt Tag.F4 K 0 1 = weylElt Tag.F4 K 0 1 * weylElt Tag.F4 K 3 1 := by
  have h := prod_alternatingWord_weylElt Tag.F4 K (0 : Fin Tag.F4.rank) 3
  have e : Tag.F4.cartan 0 3 * Tag.F4.cartan 3 0 = 0 := by decide
  rw [e] at h
  simp [TauCeti.coxeterOrder_zero, CoxeterSystem.alternatingWord] at h
  exact h.symm

theorem burnsideF4h_ree_braid_one_two :
    (weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1) =
      weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 := by
  have h := prod_alternatingWord_weylElt Tag.F4 K (1 : Fin Tag.F4.rank) 2
  have e : Tag.F4.cartan 1 2 * Tag.F4.cartan 2 1 = 2 := by decide
  rw [e] at h
  simp [TauCeti.coxeterOrder_two, CoxeterSystem.alternatingWord] at h
  simpa only [mul_assoc] using h.symm

theorem burnsideF4h_ree_wordUnit_append (w₁ w₂ : List (Fin tag.rank)) :
    ((w₁ ++ w₂).map fun i => weylElt tag K i 1).reverse.prod =
      (w₂.map fun i => weylElt tag K i 1).reverse.prod *
        (w₁.map fun i => weylElt tag K i 1).reverse.prod := by
  simp [List.map_append, List.reverse_append, List.prod_append]

theorem burnsideF4h_ree_fixedWeylConjugate_eq (model root : Subgroup (ModGL tag K))
    (word : List (Fin tag.rank)) (n : ModGL tag K) (hn : n ∈ model)
    (hop : (n : Module.End K (RootModule tag K)) = weylWordOperator tag K word) :
    fixedWeylConjugate tag K model word root = root.map (MulAut.conj n).toMonoidHom := by
  unfold fixedWeylConjugate
  have h : {element | ∃ actor : ModGL tag K, actor ∈ model ∧
      (actor : Module.End K (RootModule tag K)) = weylWordOperator tag K word ∧
      ∃ generator ∈ root, element = actor * generator * actor⁻¹} =
      ((root.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL tag K)) : Set (ModGL tag K)) := by
    ext x
    constructor
    · rintro ⟨actor, -, hact, g, hg, rfl⟩
      have : actor = n := Units.ext (hact.trans hop.symm)
      subst this
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨n, hn, hop, g, hg, rfl⟩
  rw [h]
  exact Subgroup.closure_eq _

end WeylBasic

section WeylTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable
    {tag : Tag} {K : Type} [Field K]

theorem burnsideF4h_ree_absoluteRoot_le {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    absoluteRoot tag K α ≤ rootSubgroup tag K α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro e ⟨c, seed, word, actor, hfold, hact, he⟩
  have hactor : actor = (word.map fun i => weylElt tag K i 1).reverse.prod :=
    Units.ext (hact.trans (burnsideF4h_ree_weylWordOperator_eq word))
  have he' : e = actor * xUnit tag K seed c * actor⁻¹ := Units.ext he
  have h1 : xUnit tag K seed c ∈ rootSubgroup tag K (Pi.single seed 1) := by
    rw [← pinnedX_single]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  have h2 := map_conj_prod_weylElt_rootSubgroup K word.reverse (isRoot_single tag seed)
  rw [wordProd_reverse_smul, hfold] at h2
  have h3 : e ∈ (rootSubgroup tag K (Pi.single seed 1)).map
      (MulAut.conj (word.reverse.map fun i => weylElt tag K i 1).prod).toMonoidHom := by
    refine ⟨xUnit tag K seed c, h1, ?_⟩
    rw [he', hactor, List.map_reverse]
    rfl
  rw [h2] at h3
  exact h3

theorem burnsideF4h_ree_absoluteRoot_eq {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    absoluteRoot tag K α = rootSubgroup tag K α :=
  le_antisymm (burnsideF4h_ree_absoluteRoot_le hα) (burnsideF4h_ree_rootSubgroup_le_absoluteRoot hα)

theorem burnsideF4h_ree_absoluteBorel_eq : absoluteBorel tag K = borelGroup tag K := by
  unfold absoluteBorel borelGroup absolutePositive posUnipotent rootSpan
  rw [sup_comm, burnsideF4h_ree_absoluteTorus_eq]
  congr 1
  exact iSup_congr fun α => iSup_congr fun hα => burnsideF4h_ree_absoluteRoot_eq hα.1

end WeylTransport

section F4Words

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K]

theorem burnsideF4h_ree_weylOne_eq :
    weylOne K = weylElt Tag.F4 K 0 1 * weylElt Tag.F4 K 3 1 := by
  have hred : (coxeterSystem Tag.F4).IsReduced ([0, 3] : List (Fin Tag.F4.rank)) :=
    CFSG.LieType.Simplicity.isReduced_reeOrbitWord ReeTag.F4 (0 : Fin Tag.F4.rank)
  have h := canonicalRep_wordProd (R := K) (cs := coxeterSystem Tag.F4) hred
  have e : weylOne K =
      canonicalRep (coxeterSystem Tag.F4) K ((coxeterSystem Tag.F4).wordProd [0, 3]) := rfl
  rw [e, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem burnsideF4h_ree_weylTwo_eq :
    weylTwo K = weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 *
      weylElt Tag.F4 K 2 1 := by
  have hred : (coxeterSystem Tag.F4).IsReduced ([1, 2, 1, 2] : List (Fin Tag.F4.rank)) :=
    CFSG.LieType.Simplicity.isReduced_reeOrbitWord ReeTag.F4 (1 : Fin Tag.F4.rank)
  have h := canonicalRep_wordProd (R := K) (cs := coxeterSystem Tag.F4) hred
  have e : weylTwo K =
      canonicalRep (coxeterSystem Tag.F4) K ((coxeterSystem Tag.F4).wordProd [1, 2, 1, 2]) := rfl
  rw [e, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

theorem burnsideF4h_ree_wordUnit_zero :
    (([0, 3] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 K i 1).reverse.prod =
      weylOne K := by
  rw [burnsideF4h_ree_weylOne_eq]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one]
  exact burnsideF4h_ree_comm_zero_three

theorem burnsideF4h_ree_wordUnit_one :
    (([1, 2, 1, 2] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 K i 1).reverse.prod =
      weylTwo K := by
  rw [burnsideF4h_ree_weylTwo_eq]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have h := burnsideF4h_ree_braid_one_two (K := K)
  simp only [mul_assoc] at h
  exact h

theorem burnsideF4h_ree_longActor :
    (([0, 3, 1, 2, 1, 2, 0, 3] : List (Fin Tag.F4.rank)).map
      fun i => weylElt Tag.F4 K i 1).reverse.prod = weylOne K * weylTwo K * weylOne K := by
  have h : ([0, 3, 1, 2, 1, 2, 0, 3] : List (Fin Tag.F4.rank)) = [0, 3] ++ [1, 2, 1, 2] ++ [0, 3] :=
    rfl
  rw [h, burnsideF4h_ree_wordUnit_append, burnsideF4h_ree_wordUnit_append,
    burnsideF4h_ree_wordUnit_zero, burnsideF4h_ree_wordUnit_one, mul_assoc]
  rfl

end F4Words

section BNSup

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN

theorem burnsideF4h_ree_P_eq_sup {X : Type} [Group X] {n : ℕ} (D : RankTwoSystem X n) (i : Bool)
    {m : X} (hm : m ∈ D.N)
    (hw : ((⟨m, hm⟩ : D.N) : WeylGroup D.B D.N) = gen D.w₁ D.w₂ i) :
    P D i = D.B ⊔ Subgroup.zpowers m := by
  apply le_antisymm
  · intro x hx
    rcases (mem_P_iff D).1 hx with hB | hd
    · exact Subgroup.mem_sup_left hB
    · obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hw).1 hd
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hb)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers m))) (Subgroup.mem_sup_left hb')
  · refine sup_le (B_le_P D i) ?_
    rw [Subgroup.zpowers_le]
    exact (mem_P_iff D).2 (Or.inr ((mem_dc_of_lift hw).2
      ⟨1, D.B.one_mem, 1, D.B.one_mem, by simp⟩))

end BNSup

section Main

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4
  CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Quasithin.H13.F431.BN

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_ree_reeGroup_eq : reeGroup K a = F4.reeGamma K a :=
  (reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a)).symm

theorem burnsideF4h_ree_reeBorel_eq : reeBorel K a = F4.reeFixedBorel K a := by
  unfold ChF.ExceptionalRoots.reeBorel
  rw [burnsideF4h_ree_absoluteBorel_eq, burnsideF4h_ree_reeGroup_eq]
  exact inf_comm _ _

theorem burnsideF4h_ree_weylOne_mem : weylOne K ∈ reeGroup K a := by
  have h : weylOne K ∈ F4.reeGamma K a := (octR2 K a).2
  rw [burnsideF4h_ree_reeGroup_eq]
  exact h

theorem burnsideF4h_ree_weylTwo_mem : weylTwo K ∈ reeGroup K a := by
  have h : weylTwo K ∈ F4.reeGamma K a := (octR1 K a).2
  rw [burnsideF4h_ree_reeGroup_eq]
  exact h

theorem burnsideF4h_ree_reeParabolic_one :
    ChF.ExceptionalRoots.reeParabolic K a 1 =
      F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylTwo K) := by
  unfold ChF.ExceptionalRoots.reeParabolic
  rw [burnsideF4h_ree_reeBorel_eq]
  have h1 : (if (1 : Fin 2) = 0 then [0, 3] else [1, 2, 1, 2] : List (Fin Tag.F4.rank)) =
      [1, 2, 1, 2] := by decide
  rw [h1, burnsideF4h_ree_relativeWeyl_eq, burnsideF4h_ree_wordUnit_one]
  congr 1
  exact inf_eq_right.2 (Subgroup.zpowers_le.2 burnsideF4h_ree_weylTwo_mem)

theorem burnsideF4h_ree_reeParabolic_zero :
    ChF.ExceptionalRoots.reeParabolic K a 0 =
      F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylOne K) := by
  unfold ChF.ExceptionalRoots.reeParabolic
  rw [burnsideF4h_ree_reeBorel_eq]
  have h1 : (if (0 : Fin 2) = 0 then [0, 3] else [1, 2, 1, 2] : List (Fin Tag.F4.rank)) =
      [0, 3] := by decide
  rw [h1, burnsideF4h_ree_relativeWeyl_eq, burnsideF4h_ree_wordUnit_zero]
  congr 1
  exact inf_eq_right.2 (Subgroup.zpowers_le.2 burnsideF4h_ree_weylOne_mem)

theorem burnsideF4h_ree_reeLongRoot_eq :
    reeLongRoot K a = (reeMiddleCentralRoot K a).map
      (MulAut.conj (weylOne K * weylTwo K * weylOne K)).toMonoidHom := by
  unfold ChF.ExceptionalRoots.reeLongRoot
  refine burnsideF4h_ree_fixedWeylConjugate_eq _ _ _ _ ?_ ?_
  · exact mul_mem (mul_mem burnsideF4h_ree_weylOne_mem burnsideF4h_ree_weylTwo_mem)
      burnsideF4h_ree_weylOne_mem
  · rw [burnsideF4h_ree_weylWordOperator_eq, burnsideF4h_ree_longActor]

theorem burnsideF4h_ree_mem_sup_iff (y : Gm K a) (r : Gm K a) :
    y ∈ (octH K a ⊔ Ug K a) ⊔ Subgroup.zpowers r ↔
      (y : ModGL F4.tag K) ∈ F4.reeFixedBorel K a ⊔ Subgroup.zpowers (r : ModGL F4.tag K) := by
  have hB : (octH K a ⊔ Ug K a).map (F4.reeGamma K a).subtype = F4.reeFixedBorel K a := by
    rw [sup_octH_Ug]
    exact Subgroup.map_subgroupOf_eq_of_le reeFixedBorel_le_reeGamma
  rw [← Subgroup.mem_map_iff_mem (F4.reeGamma K a).subtype_injective, Subgroup.map_sup, hB,
    MonoidHom.map_zpowers]
  rfl

theorem burnsideF4h_ree_units_subsingleton (hK : Nat.card K = 2) : Subsingleton Kˣ := by
  have h2 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.1 h2).1

theorem burnsideF4h_ree_torusGroup_eq_bot (hK : Nat.card K = 2) {τ : Tag} :
    torusGroup τ K = ⊥ := by
  haveI := burnsideF4h_ree_units_subsingleton hK
  rw [eq_bot_iff, torusGroup, Subgroup.closure_le]
  rintro _ ⟨⟨i, u⟩, rfl⟩
  rw [Subsingleton.elim u 1]
  simp [torusElt_one]

theorem burnsideF4h_ree_octH_eq_bot (hK : Nat.card K = 2) : octH K 0 = ⊥ := by
  unfold octH ReeTag.reeFixedTorus
  rw [burnsideF4h_ree_torusGroup_eq_bot hK, bot_inf_eq, Subgroup.bot_subgroupOf]

theorem burnsideF4h_ree_faithful (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    FaithfulOnBuilding ((octRGD2 hK).toPre (octGen (octRGD2 hK))).B
      ((octRGD2 hK).toPre (octGen (octRGD2 hK))).N
      ((octRGD2 hK).toPre (octGen (octRGD2 hK))).w₁
      ((octRGD2 hK).toPre (octGen (octRGD2 hK))).w₂ := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · haveI := (octRGD2 hK).cartan_normal
    have hK2 : Nat.card K = 2 := by simpa using hK
    exact (octRGD2 hK).faithful (octGen (octRGD2 hK)) (fun g hg _ => by
      rw [burnsideF4h_ree_octH_eq_bot hK2, Subgroup.mem_bot] at hg
      exact hg)
  · haveI : IsSimpleGroup (Gm K a) := isSimpleGroup_gm ha hK
    exact PreRankTwoSystem.faithful_of_isSimpleGroup _

@[expose] noncomputable def burnsideF4h_ree_system (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    RankTwoSystem (Gm K a) 8 :=
  ((octRGD2 hK).toPre (octGen (octRGD2 hK))).toSystem (burnsideF4h_ree_faithful hK)

theorem burnsideF4h_ree_mem_B_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (y : Gm K a) :
    y ∈ (burnsideF4h_ree_system hK).B ↔ (y : ModGL F4.tag K) ∈ reeBorel K a := by
  have e : (burnsideF4h_ree_system hK).B =
      (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) := sup_octH_Ug
  rw [e, burnsideF4h_ree_reeBorel_eq]
  exact Subgroup.mem_subgroupOf

theorem burnsideF4h_ree_mem_P₁_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (y : Gm K a) :
    y ∈ (burnsideF4h_ree_system hK).P₁ ↔
      (y : ModGL F4.tag K) ∈ ChF.ExceptionalRoots.reeParabolic K a 1 := by
  have hm : octR1 K a ∈ (burnsideF4h_ree_system hK).N := (octRGD2 hK).r₁_mem_N
  rw [burnsideF4h_ree_reeParabolic_one]
  have hP := burnsideF4h_ree_P_eq_sup (burnsideF4h_ree_system hK) true (m := octR1 K a) hm rfl
  show y ∈ P (burnsideF4h_ree_system hK) true ↔ _
  rw [hP]
  exact burnsideF4h_ree_mem_sup_iff y (octR1 K a)

theorem burnsideF4h_ree_mem_P₂_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) (y : Gm K a) :
    y ∈ (burnsideF4h_ree_system hK).P₂ ↔
      (y : ModGL F4.tag K) ∈ ChF.ExceptionalRoots.reeParabolic K a 0 := by
  have hm : octR2 K a ∈ (burnsideF4h_ree_system hK).N := (octRGD2 hK).r₂_mem_N
  rw [burnsideF4h_ree_reeParabolic_zero]
  have hP := burnsideF4h_ree_P_eq_sup (burnsideF4h_ree_system hK) false (m := octR2 K a) hm rfl
  show y ∈ P (burnsideF4h_ree_system hK) false ↔ _
  rw [hP]
  exact burnsideF4h_ree_mem_sup_iff y (octR2 K a)

theorem burnsideF4h_ree_center_eq_bot_of_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g => by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.1 hz (e g)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply e z, hz', map_one]

theorem burnsideF4h_ree_center_trivial (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.center ↥(reeGroup K a) = ⊥ := by
  let e0 : Gm K a ≃* ↥(reeGroup K a) := MulEquiv.subgroupCongr burnsideF4h_ree_reeGroup_eq.symm
  exact burnsideF4h_ree_center_eq_bot_of_equiv e0
    (burnsideF4h_ree_center_eq_bot (burnsideF4h_ree_system hK))

theorem burnsideF4h_ree_exists_iso (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ Φ : Gm K a ≃* (reeGroup K a ⧸ Subgroup.center (reeGroup K a)),
      ∀ (P : Subgroup (Gm K a)) (R : Subgroup (ModGL Tag.F4 K)),
        (∀ y : Gm K a, y ∈ P ↔ (y : ModGL F4.tag K) ∈ R) →
          centralImage (reeGroup K a) R = P.map Φ.toMonoidHom := by
  obtain ⟨q, hq⟩ := burnsideF4h_ree_exists_quotEquiv (burnsideF4h_ree_center_trivial hK)
  let e0 : Gm K a ≃* ↥(reeGroup K a) := MulEquiv.subgroupCongr burnsideF4h_ree_reeGroup_eq.symm
  refine ⟨e0.trans q, fun P R hPR => ?_⟩
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨e0.symm g, (hPR _).2 hg, ?_⟩
    show q (e0 (e0.symm g)) = QuotientGroup.mk' _ g
    rw [MulEquiv.apply_symm_apply, hq]
    rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e0 y, (hPR y).1 hy, ?_⟩
    show QuotientGroup.mk' _ (e0 y) = q (e0 y)
    rw [hq]
    rfl

theorem burnsideF4h_ree_card_octRoot_one (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (CFSG.Quasithin.H13.F431.TwoF4.octRoot K a 1) = Nat.card K ^ 2 := by
  have e : CFSG.Quasithin.H13.F431.TwoF4.octRoot K a 1 =
      (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a) := by
    unfold CFSG.Quasithin.H13.F431.TwoF4.octRoot
    rw [octBlock_pos (by norm_num), octPos_one]
    rfl
  have hle : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ≤ F4.reeGamma K a :=
    fun x hx => (Subgroup.mem_inf.1 hx).2
  rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    card_reeFixedOrbitUnipotent_one hK]

theorem burnsideF4h_ree_card_octRoot_eight (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (CFSG.Quasithin.H13.F431.TwoF4.octRoot K a 8) = Nat.card K := by
  have e : CFSG.Quasithin.H13.F431.TwoF4.octRoot K a 8 =
      (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a) := by
    unfold CFSG.Quasithin.H13.F431.TwoF4.octRoot
    rw [octBlock_pos (by norm_num), octPos_eight]
    rfl
  have hle : F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ ≤ F4.reeGamma K a :=
    fun x hx => (Subgroup.mem_inf.1 hx).2
  rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    card_reeFixedOrbitUnipotent_zero hK]

theorem burnsideF4h_ree_relIndex_one (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (burnsideF4h_ree_system hK).B.relIndex (burnsideF4h_ree_system hK).P₁ =
      (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  haveI : Finite (Gm K a) := Subtype.finite
  rw [burnsideF4h_ree_relIndex_P₁]
  have h := burnsideF4h_ree_card_octRoot_one hK
  rw [hK] at h
  rw [show (burnsideF4h_ree_system hK).root 1 = CFSG.Quasithin.H13.F431.TwoF4.octRoot K a 1 from rfl, h, add_comm]

theorem burnsideF4h_ree_relIndex_two (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (burnsideF4h_ree_system hK).B.relIndex (burnsideF4h_ree_system hK).P₂ =
      2 ^ (2 * a + 1) + 1 := by
  haveI : Finite (Gm K a) := Subtype.finite
  rw [burnsideF4h_ree_relIndex_P₂]
  have h := burnsideF4h_ree_card_octRoot_eight hK
  rw [hK] at h
  rw [show (burnsideF4h_ree_system hK).root ((8 : ℕ) : ℤ) = CFSG.Quasithin.H13.F431.TwoF4.octRoot K a 8 from rfl, h, add_comm]

end Main

section LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_ree_reeFourSeed_eq (i : Fin 4) : reeFourSeed i = largeReeRoot i := by
  fin_cases i <;> rfl

open scoped Pointwise in
theorem burnsideF4h_ree_middleCentral_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ModGL Tag.F4 K} (hg : g ∈ reeMiddleCentralRoot K a) :
    ∃ v : K, g = largeReeCoord a K 0 v := by
  obtain ⟨hgΓ, hgJ⟩ := Subgroup.mem_inf.1 hg
  rw [burnsideF4h_ree_reeGroup_eq] at hgΓ
  have e2 : absoluteRoot Tag.F4 K (reeFourSeed 2) = rootSubgroup Tag.F4 K (largeReeRoot 2) := by
    rw [burnsideF4h_ree_reeFourSeed_eq]
    exact burnsideF4h_ree_absoluteRoot_eq (largeReeRoot_pos 2).1
  have e3 : absoluteRoot Tag.F4 K (reeFourSeed 3) = rootSubgroup Tag.F4 K (largeReeRoot 3) := by
    rw [burnsideF4h_ree_reeFourSeed_eq]
    exact burnsideF4h_ree_absoluteRoot_eq (largeReeRoot_pos 3).1
  rw [e2, e3] at hgJ
  have h2 : (2 : K) = 0 := F4_two_eq_zero
  have hcomm : ∀ x ∈ rootSubgroup Tag.F4 K (largeReeRoot 2),
      ∀ y ∈ rootSubgroup Tag.F4 K (largeReeRoot 3), Commute x y :=
    (large_Ree_B2_characteristic_two_commutators K h2).2.1 2 3 (by decide) (by decide)
  have hle : rootSubgroup Tag.F4 K (largeReeRoot 2) ≤
      Subgroup.normalizer (rootSubgroup Tag.F4 K (largeReeRoot 3) : Set (ModGL Tag.F4 K)) := by
    refine burnsideF4h_ree_le_normalizer_of_conj (fun x hx y hy => ?_)
    rw [(hcomm x hx y hy).eq, mul_inv_cancel_right]
    exact hy
  have hmem : g ∈ ((rootSubgroup Tag.F4 K (largeReeRoot 2) : Subgroup (ModGL Tag.F4 K)) :
      Set (ModGL Tag.F4 K)) * (rootSubgroup Tag.F4 K (largeReeRoot 3) : Set (ModGL Tag.F4 K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hgJ
  rw [Set.mem_mul] at hmem
  obtain ⟨x, hx, y, hy, rfl⟩ := hmem
  obtain ⟨C, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨D, rfl⟩ := mem_rootSubgroup.1 hy
  have hP : pinnedX Tag.F4 K (largeReeRoot 2) C * pinnedX Tag.F4 K (largeReeRoot 3) D =
      largeReeP K 0 0 C D := by
    simp [largeReeP, largeReeX, pinnedX_zero]
  have hU : pinnedX Tag.F4 K (largeReeRoot 2) C * pinnedX Tag.F4 K (largeReeRoot 3) D ∈
      F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := by
    refine Subgroup.mem_inf.2 ⟨?_, hgΓ⟩
    rw [F4_fixedOrbitRoots_one, hP]
    exact largeReeP_mem_rootSpan _ _ _ _
  obtain ⟨p, -, hp⟩ := (bijOn_largeReeCoord hK).2.2 hU
  have hp' : largeReeP K p.1 (largeReeSigma a p.1) p.2
      (largeReeSigma a p.2 + p.1 ^ 2 * largeReeSigma a p.1) = largeReeP K 0 0 C D := by
    rw [← hP, ← hp]
    rfl
  obtain ⟨h1, -, -, -⟩ := largeReeP_injective hp'
  refine ⟨p.2, ?_⟩
  rw [← hp]
  show largeReeCoord a K p.1 p.2 = _
  rw [h1]

theorem burnsideF4h_ree_coord_mem_middleCentral (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : K) :
    largeReeCoord a K 0 v ∈ reeMiddleCentralRoot K a := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h : largeReeCoord a K 0 v ∈ F4.reeGamma K a :=
      (Subgroup.mem_inf.1 (largeReeCoord_mem hK 0 v)).2
    rw [burnsideF4h_ree_reeGroup_eq]
    exact h
  · have e : largeReeCoord a K 0 v =
        pinnedX Tag.F4 K (reeFourSeed 2) v *
          pinnedX Tag.F4 K (reeFourSeed 3) (largeReeSigma a v) := by
      simp [largeReeCoord, largeReeP, largeReeX, burnsideF4h_ree_reeFourSeed_eq, pinnedX_zero,
        largeReeSigma_zero]
    rw [e]
    have hr2 : IsRoot Tag.F4 (reeFourSeed 2) := by
      rw [burnsideF4h_ree_reeFourSeed_eq]; exact (largeReeRoot_pos 2).1
    have hr3 : IsRoot Tag.F4 (reeFourSeed 3) := by
      rw [burnsideF4h_ree_reeFourSeed_eq]; exact (largeReeRoot_pos 3).1
    exact mul_mem
      (Subgroup.mem_sup_left (burnsideF4h_ree_rootSubgroup_le_absoluteRoot hr2
        (Subgroup.subset_closure ⟨v, rfl⟩)))
      (Subgroup.mem_sup_right (burnsideF4h_ree_rootSubgroup_le_absoluteRoot hr3
        (Subgroup.subset_closure ⟨largeReeSigma a v, rfl⟩)))

theorem burnsideF4h_ree_reeLongRoot_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ModGL Tag.F4 K} (hy : y ∈ reeLongRoot K a) : ∃ v : K, y = centralZ K a v := by
  rw [burnsideF4h_ree_reeLongRoot_eq] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨v, rfl⟩ := burnsideF4h_ree_middleCentral_coord hK hg
  refine ⟨v, ?_⟩
  have h := weyl_conj_sylowB_zero (m := a) (K := K) v
  rw [sylowH_zero_eq_centralZ, sylowB_eq_largeReeCoord] at h
  exact h

theorem burnsideF4h_ree_centralZ_mem_reeLongRoot (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : K) :
    centralZ K a v ∈ reeLongRoot K a := by
  rw [burnsideF4h_ree_reeLongRoot_eq]
  refine ⟨largeReeCoord a K 0 v, burnsideF4h_ree_coord_mem_middleCentral hK v, ?_⟩
  have h := weyl_conj_sylowB_zero (m := a) (K := K) v
  rw [sylowH_zero_eq_centralZ, sylowB_eq_largeReeCoord] at h
  exact h

theorem burnsideF4h_ree_posUnipotent_commute_centralZ {u : ModGL F4.tag K}
    (hu : u ∈ posUnipotent F4.tag K) (c : K) : u * centralZ K a c = centralZ K a c * u := by
  haveI : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  have h44 := CFSG.LieType.Chevalley.f4x_central (K := K) (k := 44) (Or.inl rfl) c hu
  have h47 := CFSG.LieType.Chevalley.f4x_central (K := K) (k := 47) (Or.inr rfl)
    (c ^ (2 * 2 ^ a)) hu
  rw [CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.f4x_44] at h44
  rw [CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.f4x_47] at h47
  have c44 : Commute u (pinnedX F4.tag K
      CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.largeReeAlpha44 c) := h44
  have c47 : Commute u (pinnedX F4.tag K
      CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.largeReeAlpha47
        (c ^ (2 * 2 ^ a))) := h47
  exact (c44.mul_right c47).eq

theorem burnsideF4h_ree_borel_conj_centralZ (hK : Nat.card K = 2 ^ (2 * a + 1))
    {b : ModGL F4.tag K} (hb : b ∈ F4.reeFixedBorel K a) (c : K) :
    ∃ u : Kˣ, b * centralZ K a c * b⁻¹ = centralZ K a ((u : K) ^ 2 ^ a * c) := by
  have hb' : b ∈ (F4.reeFixedBorel K a : Set (ModGL F4.tag K)) := hb
  rw [reeFixedBorel_eq_mul] at hb'
  obtain ⟨h, hh, x, hx, rfl⟩ := hb'
  obtain ⟨u, v, rfl⟩ := rankOne_exists_torusPair_eq hK hh
  refine ⟨u, ?_⟩
  have hxz := burnsideF4h_ree_posUnipotent_commute_centralZ (a := a) (Subgroup.mem_inf.1 hx).1 c
  calc CFSG.LieType.Ree.LargeReeCover.torusPair a (u, v) * x * centralZ K a c *
        (CFSG.LieType.Ree.LargeReeCover.torusPair a (u, v) * x)⁻¹ =
      CFSG.LieType.Ree.LargeReeCover.torusPair a (u, v) * (x * centralZ K a c * x⁻¹) *
        (CFSG.LieType.Ree.LargeReeCover.torusPair a (u, v))⁻¹ := by group
    _ = CFSG.LieType.Ree.LargeReeCover.torusPair a (u, v) * centralZ K a c *
        (CFSG.LieType.Ree.LargeReeCover.torusPair a (u, v))⁻¹ := by
        rw [hxz, mul_inv_cancel_right]
    _ = _ := torusPair_conj_centralZ hK u v c

theorem burnsideF4h_ree_weylTwo_conj_centralZ (c : K) :
    weylTwo K * centralZ K a c * (weylTwo K)⁻¹ = centralZ K a c :=
  canonicalRep_conj_centralZ (a := a) c

@[expose] noncomputable def burnsideF4h_ree_LR (K : Type) [Field K] (a : ℕ) : Subgroup (ModGL F4.tag K) :=
  reeLongRoot K a

theorem burnsideF4h_ree_borel_sup_le_normalizer (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylTwo K) ≤
      Subgroup.normalizer (burnsideF4h_ree_LR K a : Set (ModGL F4.tag K)) := by
  have hcoord : ∀ {y : ModGL F4.tag K}, y ∈ burnsideF4h_ree_LR K a → ∃ v : K, y = centralZ K a v :=
    fun hy => burnsideF4h_ree_reeLongRoot_coord hK hy
  have hmem : ∀ v : K, centralZ K a v ∈ burnsideF4h_ree_LR K a :=
    fun v => burnsideF4h_ree_centralZ_mem_reeLongRoot hK v
  refine sup_le ?_ (Subgroup.zpowers_le.2 ?_)
  · refine burnsideF4h_ree_le_normalizer_of_conj (fun b hb x hx => ?_)
    obtain ⟨v, rfl⟩ := hcoord hx
    obtain ⟨u, hu⟩ := burnsideF4h_ree_borel_conj_centralZ hK hb v
    rw [hu]
    exact hmem _
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := hcoord hx
      rw [burnsideF4h_ree_weylTwo_conj_centralZ]
      exact hx
    · intro hx
      obtain ⟨v, hv⟩ := hcoord hx
      have hx' : x = centralZ K a v := by
        have h2 := burnsideF4h_ree_weylTwo_conj_centralZ (K := K) (a := a) v
        exact mul_left_cancel (mul_right_cancel (hv.trans h2.symm))
      rw [hx']
      exact hmem v

theorem burnsideF4h_ree_P₁_le_normalizer (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (burnsideF4h_ree_system hK).P₁ ≤ Subgroup.normalizer
      (((burnsideF4h_ree_LR K a).subgroupOf (F4.reeGamma K a) : Subgroup (Gm K a)) :
        Set (Gm K a)) := by
  have hm : octR1 K a ∈ (burnsideF4h_ree_system hK).N := (octRGD2 hK).r₁_mem_N
  have hP := burnsideF4h_ree_P_eq_sup (burnsideF4h_ree_system hK) true (m := octR1 K a) hm rfl
  have e : (burnsideF4h_ree_system hK).P₁ =
      (F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylTwo K)).subgroupOf (F4.reeGamma K a) := by
    ext y
    show y ∈ CFSG.Quasithin.H13.F431.BN.P (burnsideF4h_ree_system hK) true ↔ _
    rw [hP]
    exact (burnsideF4h_ree_mem_sup_iff y (octR1 K a)).trans Subgroup.mem_subgroupOf.symm
  rw [e]
  exact burnsideF4h_ree_le_normalizer_subgroupOf (burnsideF4h_ree_borel_sup_le_normalizer hK)

end LongRoot


section ShortRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_ree_shortActor :
    (([1, 2, 1, 2, 0, 3, 1, 2, 1, 2] : List (Fin Tag.F4.rank)).map
      fun i => weylElt Tag.F4 K i 1).reverse.prod = weylTwo K * weylOne K * weylTwo K := by
  have h : ([1, 2, 1, 2, 0, 3, 1, 2, 1, 2] : List (Fin Tag.F4.rank)) =
      [1, 2, 1, 2] ++ [0, 3] ++ [1, 2, 1, 2] := rfl
  rw [h, burnsideF4h_ree_wordUnit_append, burnsideF4h_ree_wordUnit_append,
    burnsideF4h_ree_wordUnit_zero, burnsideF4h_ree_wordUnit_one, mul_assoc]
  rfl

theorem burnsideF4h_ree_reeShortRoot_eq :
    reeShortRoot K a = (reeTwoRoot K a).map
      (MulAut.conj (weylTwo K * weylOne K * weylTwo K)).toMonoidHom := by
  unfold ChF.ExceptionalRoots.reeShortRoot
  refine burnsideF4h_ree_fixedWeylConjugate_eq _ _ _ _ ?_ ?_
  · exact mul_mem (mul_mem burnsideF4h_ree_weylTwo_mem burnsideF4h_ree_weylOne_mem)
      burnsideF4h_ree_weylTwo_mem
  · rw [burnsideF4h_ree_weylWordOperator_eq, burnsideF4h_ree_shortActor]

open CFSG.LieType.Ree.LargeReeCover in
theorem burnsideF4h_ree_sylowA_eq_stdTwoG (s : K) : sylowA a K s = stdTwoG a s := by
  have h : stdTwoRoot 0 = RootOps.orbitCertRoot F4.tag 24 ∧
      stdTwoRoot 1 = RootOps.orbitCertRoot F4.tag 33 := by
    decide +kernel
  rw [stdTwoG, sylowA, sylowX, sylowX, h.1, h.2]

open scoped Pointwise in
theorem burnsideF4h_ree_reeTwoRoot_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ModGL F4.tag K} (hg : g ∈ reeTwoRoot K a) : ∃ s : K, g = sylowA a K s := by
  obtain ⟨hgΓ0, hgJ⟩ := Subgroup.mem_inf.1 hg
  have hgΓ : g ∈ F4.reeGamma K a := by
    have h : g ∈ reeGroup K a := hgΓ0
    rw [burnsideF4h_ree_reeGroup_eq] at h
    exact h
  have e0 : absoluteRoot Tag.F4 K (Pi.single 0 1) = rootSubgroup Tag.F4 K (Pi.single 0 1) :=
    burnsideF4h_ree_absoluteRoot_eq (isRoot_single Tag.F4 _)
  have e3 : absoluteRoot Tag.F4 K (Pi.single 3 1) = rootSubgroup Tag.F4 K (Pi.single 3 1) :=
    burnsideF4h_ree_absoluteRoot_eq (isRoot_single Tag.F4 _)
  rw [e0, e3] at hgJ
  have hU : g ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
    refine Subgroup.mem_inf.2 ⟨?_, hgΓ⟩
    rw [F4_fixedOrbitRoots_zero]
    have h0 : rootSubgroup Tag.F4 K (Pi.single 0 1) ≤
        rootSpan Tag.F4 K {Pi.single largeReeI1 1, Pi.single largeReeI4 1} :=
      le_iSup₂_of_le (Pi.single largeReeI1 1) (Set.mem_insert _ _) le_rfl
    have h3 : rootSubgroup Tag.F4 K (Pi.single 3 1) ≤
        rootSpan Tag.F4 K {Pi.single largeReeI1 1, Pi.single largeReeI4 1} :=
      le_iSup₂_of_le (Pi.single largeReeI4 1) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        le_rfl
    exact (sup_le h0 h3) hgJ
  obtain ⟨s, hs⟩ := exists_stdTwoG_eq hK hU
  exact ⟨s, by rw [burnsideF4h_ree_sylowA_eq_stdTwoG, hs]⟩

theorem burnsideF4h_ree_sylowA_mem_reeTwoRoot (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : K) :
    sylowA a K s ∈ reeTwoRoot K a := by
  have hU : sylowA a K s ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
    rw [burnsideF4h_ree_sylowA_eq_stdTwoG]
    exact stdTwoG_mem hK s
  have hΓ : sylowA a K s ∈ reeGroup K a := by
    have h : sylowA a K s ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hU).2
    rw [burnsideF4h_ree_reeGroup_eq]
    exact h
  refine ⟨hΓ, ?_⟩
  rw [burnsideF4h_ree_sylowA_eq_stdTwoG, stdTwoG,
    (stdTwoRoot_eq_single).1, (stdTwoRoot_eq_single).2]
  exact mul_mem
    (Subgroup.mem_sup_right (burnsideF4h_ree_rootSubgroup_le_absoluteRoot
      (isRoot_single Tag.F4 _) (Subgroup.subset_closure ⟨s, rfl⟩)))
    (Subgroup.mem_sup_left (burnsideF4h_ree_rootSubgroup_le_absoluteRoot
      (isRoot_single Tag.F4 _) (Subgroup.subset_closure ⟨largeReeSigma a s, rfl⟩)))

@[expose] noncomputable def burnsideF4h_ree_SR (K : Type) [Field K] (a : ℕ) :
    Subgroup (ModGL F4.tag K) :=
  reeShortRoot K a

theorem burnsideF4h_ree_SR_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ModGL F4.tag K} (hy : y ∈ burnsideF4h_ree_SR K a) :
    ∃ s : K, y = (weylTwo K * weylOne K * weylTwo K) * sylowA a K s *
      (weylTwo K * weylOne K * weylTwo K)⁻¹ := by
  have hy' : y ∈ reeShortRoot K a := hy
  rw [burnsideF4h_ree_reeShortRoot_eq] at hy'
  obtain ⟨g, hg, rfl⟩ := hy'
  obtain ⟨s, rfl⟩ := burnsideF4h_ree_reeTwoRoot_coord hK hg
  exact ⟨s, rfl⟩

theorem burnsideF4h_ree_sylowL_mem_SR (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    sylowL a K 1 ∈ burnsideF4h_ree_SR K a := by
  have h : sylowL a K 1 ∈ reeShortRoot K a := by
    rw [burnsideF4h_ree_reeShortRoot_eq]
    exact ⟨sylowA a K 1, burnsideF4h_ree_sylowA_mem_reeTwoRoot hK 1,
      weyl_conj_sylowA_one (m := a) (K := K)⟩
  exact h

theorem burnsideF4h_ree_eq_zero_or_one (hK : Nat.card K = 2) (s : K) : s = 0 ∨ s = 1 := by
  by_cases hs : s = 0
  · exact Or.inl hs
  · right
    haveI := burnsideF4h_ree_units_subsingleton hK
    have h := Subsingleton.elim (Units.mk0 s hs) 1
    exact congrArg Units.val h

theorem burnsideF4h_ree_conj_sylowL_not_mem_SR (hK : Nat.card K = 2) :
    sylowV 0 K 0 1 0 0 0 0 0 0 0 0 0 0 * sylowL 0 K 1 * (sylowV 0 K 0 1 0 0 0 0 0 0 0 0 0 0)⁻¹ ∉
      burnsideF4h_ree_SR K 0 := by
  intro hmem
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  set u := sylowV 0 K 0 1 0 0 0 0 0 0 0 0 0 0 with hu
  set t := sylowL 0 K 1 with ht
  have hcomm : u * t = t * u := by
    obtain ⟨s, hs⟩ := burnsideF4h_ree_SR_coord hK' hmem
    have hconj : u * t * u⁻¹ = t := by
      rcases burnsideF4h_ree_eq_zero_or_one hK s with rfl | rfl
      · rw [sylowA_zero, mul_one, mul_inv_cancel] at hs
        have ht1 : t = 1 := by
          have := congrArg (fun x => u⁻¹ * x * u) hs
          simpa [mul_assoc] using this
        rw [ht1, mul_one, mul_inv_cancel]
      · rw [hs]
        exact weyl_conj_sylowA_one (m := 0) (K := K)
    calc u * t = u * t * u⁻¹ * u := by group
      _ = t * u := by rw [hconj]
  exact one_ne_zero ((sylowV_commute_sylowL_one_iff 0 1 0 0 0 0 0 0 0 0 0 0).1 hcomm).1

theorem burnsideF4h_ree_SR_le : burnsideF4h_ree_SR K a ≤ F4.reeGamma K a := by
  intro y hy
  have hy' : y ∈ reeShortRoot K a := hy
  rw [burnsideF4h_ree_reeShortRoot_eq] at hy'
  obtain ⟨g, hg, rfl⟩ := hy'
  have hn : weylTwo K * weylOne K * weylTwo K ∈ F4.reeGamma K a :=
    mul_mem (mul_mem (octR1 K a).2 (octR2 K a).2) (octR1 K a).2
  have hgΓ : g ∈ F4.reeGamma K a := by
    have h : g ∈ reeGroup K a := (Subgroup.mem_inf.1 hg).1
    rw [burnsideF4h_ree_reeGroup_eq] at h
    exact h
  exact mul_mem (mul_mem hn hgΓ) (inv_mem hn)

theorem burnsideF4h_ree_sylowV_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    sylowV a K 0 1 0 0 0 0 0 0 0 0 0 0 ∈ F4.reeFixedPosUnipotent K a := by
  have h := (bijOn_sylowVec hK).1
    (Set.mem_univ (![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 12 → K))
  have e : sylowVec a K (![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 12 → K) =
      sylowV a K 0 1 0 0 0 0 0 0 0 0 0 0 := rfl
  rw [e] at h
  exact h

theorem burnsideF4h_ree_weyl_conj_sylowA (s : K) :
    (weylTwo K * weylOne K * weylTwo K) * sylowA a K s * (weylTwo K * weylOne K * weylTwo K)⁻¹ =
      sylowL a K s := by
  calc (weylTwo K * weylOne K * weylTwo K) * sylowA a K s *
        (weylTwo K * weylOne K * weylTwo K)⁻¹ =
      weylTwo K * (weylOne K * (weylTwo K * sylowA a K s * (weylTwo K)⁻¹) * (weylOne K)⁻¹) *
        (weylTwo K)⁻¹ := by group
    _ = sylowL a K s := by
      rw [weylTwo_conj_sylowA, weylOne_conj_sylowJ, weylTwo_conj_sylowK]

theorem burnsideF4h_ree_SR_coord_L (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ModGL F4.tag K} (hy : y ∈ burnsideF4h_ree_SR K a) : ∃ s : K, y = sylowL a K s := by
  obtain ⟨s, rfl⟩ := burnsideF4h_ree_SR_coord hK hy
  exact ⟨s, burnsideF4h_ree_weyl_conj_sylowA s⟩

theorem burnsideF4h_ree_sylowL_zero : sylowL a K (0 : K) = 1 := by
  simp [sylowL, sylowX, largeReeSigma_zero, pinnedX_zero]

theorem burnsideF4h_ree_sylowL_eq_sylowVec (s : K) :
    sylowL a K s = sylowVec a K (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, s] : Fin 12 → K) := by
  show _ = sylowV a K 0 0 0 0 0 0 0 0 0 0 0 s
  rw [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_eq_centralZ, centralZ_zero, sylowJ_zero, sylowK_zero]
  simp only [one_mul]

theorem burnsideF4h_ree_centralZ_eq_sylowVec (c : K) :
    centralZ K a c = sylowVec a K (![0, 0, 0, 0, 0, 0, 0, 0, c, 0, 0, 0] : Fin 12 → K) := by
  show _ = sylowV a K 0 0 0 0 0 0 0 0 c 0 0 0
  rw [sylowV, sylowA_zero, sylowB_zero_zero, sylowD_zero_zero, sylowF_zero_zero,
    sylowH_zero_eq_centralZ, sylowJ_zero, sylowK_zero, burnsideF4h_ree_sylowL_zero]
  simp only [one_mul, mul_one]

theorem burnsideF4h_ree_sylowL_one_ne_one : sylowL a K 1 ≠ 1 := by
  intro h1
  have hc : sylowV a K 0 1 0 0 0 0 0 0 0 0 0 0 * sylowL a K 1 =
      sylowL a K 1 * sylowV a K 0 1 0 0 0 0 0 0 0 0 0 0 := by
    rw [h1, mul_one, one_mul]
  exact one_ne_zero ((sylowV_commute_sylowL_one_iff 0 1 0 0 0 0 0 0 0 0 0 0).1 hc).1

theorem burnsideF4h_ree_false_of_U_normalizes_SR (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (E : ∀ {g x : ModGL F4.tag K}, g ∈ F4.reeFixedPosUnipotent K a →
      x ∈ burnsideF4h_ree_SR K a → g * x * g⁻¹ ∈ burnsideF4h_ree_SR K a) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥(F4.reeFixedPosUnipotent K a) :=
    (isPGroup_reeFixedPosUnipotent ha hK).isNilpotent
  let T : Subgroup ↥(F4.reeFixedPosUnipotent K a) :=
    (burnsideF4h_ree_SR K a).subgroupOf (F4.reeFixedPosUnipotent K a)
  haveI hTn : T.Normal := ⟨fun x hx g => by
    refine Subgroup.mem_subgroupOf.2 ?_
    have := E g.2 (Subgroup.mem_subgroupOf.1 hx)
    simpa using this⟩
  have hL1U : sylowL a K 1 ∈ F4.reeFixedPosUnipotent K a := by
    rw [burnsideF4h_ree_sylowL_eq_sylowVec]
    exact (bijOn_sylowVec hK).1 (Set.mem_univ _)
  have hT : T ≠ ⊥ := by
    intro hT
    have hmem : (⟨sylowL a K 1, hL1U⟩ : ↥(F4.reeFixedPosUnipotent K a)) ∈ T :=
      Subgroup.mem_subgroupOf.2 (burnsideF4h_ree_sylowL_mem_SR hK)
    rw [hT, Subgroup.mem_bot] at hmem
    have h1 : ((⟨sylowL a K 1, hL1U⟩ : ↥(F4.reeFixedPosUnipotent K a)) : ModGL F4.tag K) = 1 := by
      rw [hmem, OneMemClass.coe_one]
    exact burnsideF4h_ree_sylowL_one_ne_one h1
  obtain ⟨w, hw1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hT)
  obtain ⟨hwT, hwZ⟩ := Subgroup.mem_inf.1 w.2
  obtain ⟨s, hs⟩ := burnsideF4h_ree_SR_coord_L hK (Subgroup.mem_subgroupOf.1 hwT)
  have hzc : ((w : ↥(F4.reeFixedPosUnipotent K a)) : ModGL F4.tag K) ∈
      (((Subgroup.center ↥(F4.reeFixedPosUnipotent K a)).map
        (F4.reeFixedPosUnipotent K a).subtype : Subgroup (ModGL F4.tag K)) :
          Set (ModGL F4.tag K)) := ⟨w, hwZ, rfl⟩
  rw [coe_center_eq_range_centralZ ha hK] at hzc
  obtain ⟨c, hc⟩ := hzc
  have heq : sylowVec a K (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, s] : Fin 12 → K) =
      sylowVec a K (![0, 0, 0, 0, 0, 0, 0, 0, c, 0, 0, 0] : Fin 12 → K) := by
    rw [← burnsideF4h_ree_sylowL_eq_sylowVec, ← burnsideF4h_ree_centralZ_eq_sylowVec, ← hs, hc]
  have hv := (bijOn_sylowVec hK).2.1 (Set.mem_univ _) (Set.mem_univ _) heq
  have hs0 : s = 0 := by simpa using congrFun hv 11
  apply hw1
  apply Subtype.ext
  apply Subtype.ext
  show ((w : ↥(F4.reeFixedPosUnipotent K a)) : ModGL F4.tag K) = 1
  rw [hs, hs0, burnsideF4h_ree_sylowL_zero]

end ShortRoot

@[expose] def burnsideF4h_ree_OriginalGoal (K : Type) [Field K] : Prop :=
  ∀ exponent : ℕ, ChF.ExceptionalRoots.ReeScope K exponent →
    let native := ChF.NativeFrame.ree K exponent
    let q := 2 ^ (2 * exponent + 1)
    ChF.IsLieParabolics 2 (⊤ : Subgroup
      (ChF.ExceptionalRoots.reeGroup K exponent ⧸
        Subgroup.center (ChF.ExceptionalRoots.reeGroup K exponent)))
      native.borel native.pointParabolic native.lineParabolic ∧
    native.borel.relIndex native.pointParabolic = q ^ 2 + 1 ∧
    native.borel.relIndex native.lineParabolic = q + 1 ∧
    native.pointParabolic ≤ Subgroup.normalizer (native.longRoot : Set _) ∧
    native.lineParabolic ≤ Subgroup.normalizer (native.shortRoot : Set _)

section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4


theorem burnsideF4h_reeOrderedLocals_core (K : Type) [Field K] [Finite K] [CharP K 2] :
    ChF.NativeFrame.reeOrderedLocalsGoal K := by
  intro a hKa
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hKa
  haveI : CharP K F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨Φ, hΦ⟩ := burnsideF4h_ree_exists_iso hK
  have hB := hΦ _ _ (burnsideF4h_ree_mem_B_iff hK)
  have hP1 := hΦ _ _ (burnsideF4h_ree_mem_P₁_iff hK)
  have hP2 := hΦ _ _ (burnsideF4h_ree_mem_P₂_iff hK)
  have hL := hΦ ((burnsideF4h_ree_LR K a).subgroupOf (F4.reeGamma K a))
    (reeLongRoot K a) (fun y => Subgroup.mem_subgroupOf)
  show ChF.IsLieParabolics 2 ⊤ (centralImage (reeGroup K a) (reeBorel K a))
      (centralImage (reeGroup K a) (reeParabolic K a 1))
      (centralImage (reeGroup K a) (reeParabolic K a 0)) ∧
    (centralImage (reeGroup K a) (reeBorel K a)).relIndex
        (centralImage (reeGroup K a) (reeParabolic K a 1)) = (2 ^ (2 * a + 1)) ^ 2 + 1 ∧
    (centralImage (reeGroup K a) (reeBorel K a)).relIndex
        (centralImage (reeGroup K a) (reeParabolic K a 0)) = 2 ^ (2 * a + 1) + 1 ∧
    centralImage (reeGroup K a) (reeParabolic K a 1) ≤
      Subgroup.normalizer (centralImage (reeGroup K a) (reeLongRoot K a) : Set _)
  rw [hB, hP1, hP2, hL]
  haveI : Finite (Gm K a) := Subtype.finite
  refine ⟨burnsideF4h_ree_isLieParabolics_equiv Φ
      (burnsideF4h_ree_isLieParabolics_of_system _ (isSylowTwoOf_Ug hK)), ?_, ?_,
    burnsideF4h_ree_le_normalizer_map _ (burnsideF4h_ree_P₁_le_normalizer hK)⟩
  · rw [Subgroup.relIndex_map_map_of_injective _ _ Φ.injective]
    exact burnsideF4h_ree_relIndex_one hK
  · rw [Subgroup.relIndex_map_map_of_injective _ _ Φ.injective]
    exact burnsideF4h_ree_relIndex_two hK

end

section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4


theorem burnsideF4h_ree_conj_mem_SR {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (h : (ChF.NativeFrame.ree K a).lineParabolic ≤
      Subgroup.normalizer ((ChF.NativeFrame.ree K a).shortRoot : Set _))
    {g x : ModGL F4.tag K} (hg : g ∈ F4.reeFixedPosUnipotent K a)
    (hx : x ∈ burnsideF4h_ree_SR K a) : g * x * g⁻¹ ∈ burnsideF4h_ree_SR K a := by
  obtain ⟨Φ, hΦ⟩ := burnsideF4h_ree_exists_iso hK
  have hP2 := hΦ _ _ (burnsideF4h_ree_mem_P₂_iff hK)
  have hS := hΦ ((burnsideF4h_ree_SR K a).subgroupOf (F4.reeGamma K a)) (reeShortRoot K a)
    (fun y => Subgroup.mem_subgroupOf)
  change centralImage (reeGroup K a) (reeParabolic K a 0) ≤
    Subgroup.normalizer (centralImage (reeGroup K a) (reeShortRoot K a) : Set _) at h
  rw [hP2, hS] at h
  have hgΓ : g ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hg).2
  have hxΓ : x ∈ F4.reeGamma K a := burnsideF4h_ree_SR_le hx
  have hyB : (⟨g, hgΓ⟩ : Gm K a) ∈ (burnsideF4h_ree_system hK).B := by
    show (⟨g, hgΓ⟩ : Gm K a) ∈ octH K a ⊔ Ug K a
    exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hg)
  have hyP : (⟨g, hgΓ⟩ : Gm K a) ∈ (burnsideF4h_ree_system hK).P₂ :=
    CFSG.Quasithin.H13.F431.BN.B_le_P _ false hyB
  have hx' : (⟨x, hxΓ⟩ : Gm K a) ∈ (burnsideF4h_ree_SR K a).subgroupOf (F4.reeGamma K a) :=
    Subgroup.mem_subgroupOf.2 hx
  have hN := h ⟨_, hyP, rfl⟩
  have hmem : Φ.toMonoidHom ((⟨g, hgΓ⟩ : Gm K a) * ⟨x, hxΓ⟩ * (⟨g, hgΓ⟩ : Gm K a)⁻¹) ∈
      ((burnsideF4h_ree_SR K a).subgroupOf (F4.reeGamma K a)).map Φ.toMonoidHom := by
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hN (Φ.toMonoidHom ⟨x, hxΓ⟩)).1 ⟨_, hx', rfl⟩
  obtain ⟨w, hw, hwe⟩ := hmem
  have hw' : w = (⟨g, hgΓ⟩ : Gm K a) * ⟨x, hxΓ⟩ * (⟨g, hgΓ⟩ : Gm K a)⁻¹ := Φ.injective hwe
  rw [hw'] at hw
  have hw2 := Subgroup.mem_subgroupOf.1 hw
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hw2
  exact hw2

theorem burnsideF4h_ree_not_lineParabolic_le_normalizer (K : Type) [Field K] [Finite K]
    [CharP K 2] (a : ℕ) (hKa : ChF.ExceptionalRoots.ReeScope K a) :
    ¬ ((ChF.NativeFrame.ree K a).lineParabolic ≤
      Subgroup.normalizer ((ChF.NativeFrame.ree K a).shortRoot : Set _)) := by
  intro h
  haveI : CharP K F4.prime := inferInstanceAs (CharP K 2)
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hKa
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hK2 : Nat.card K = 2 := by simpa using hK
    exact burnsideF4h_ree_conj_sylowL_not_mem_SR hK2
      (burnsideF4h_ree_conj_mem_SR hK h (burnsideF4h_ree_sylowV_mem hK)
        (burnsideF4h_ree_sylowL_mem_SR hK))
  · exact burnsideF4h_ree_false_of_U_normalizes_SR ha hK
      (fun hg hx => burnsideF4h_ree_conj_mem_SR hK h hg hx)

theorem burnsideF4h_ree_not_reeOrderedLocalsGoal (K : Type) [Field K] [Finite K] [CharP K 2]
    (a : ℕ) (hKa : ChF.ExceptionalRoots.ReeScope K a) :
    ¬ burnsideF4h_ree_OriginalGoal K := fun h =>
  burnsideF4h_ree_not_lineParabolic_le_normalizer K a hKa (h a hKa).2.2.2.2

end

end PartBurnsideF4hRee

section PartBurnsideF4hInvRee

section Abstract

structure burnsideF4h_invree_Datum {G : Type*} [Group G] (L S : Subgroup G) (z t : G) : Prop where
  z_ne : z ≠ 1
  z_sq : z * z = 1
  t_ne : t ≠ 1
  t_sq : t * t = 1
  cls : ∀ x : G, x ≠ 1 → x * x = 1 → IsConj z x ∨ IsConj t x
  not_conj : ¬ IsConj z t
  z_L : z ∈ L
  t_S : t ∈ S
  L_conj : ∀ y ∈ L, y ≠ 1 → IsConj z y
  S_conj : ∀ y ∈ S, y ≠ 1 → IsConj t y

theorem burnsideF4h_invree_isConj_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a b : A} :
    IsConj (e a) (e b) ↔ IsConj a b :=
  ⟨fun h => by simpa using e.symm.toMonoidHom.map_isConj h,
    fun h => e.toMonoidHom.map_isConj h⟩

theorem burnsideF4h_invree_datum_map {G H : Type*} [Group G] [Group H] (Φ : G ≃* H)
    {L S : Subgroup G} {z t : G} (D : burnsideF4h_invree_Datum L S z t) :
    burnsideF4h_invree_Datum (L.map Φ.toMonoidHom) (S.map Φ.toMonoidHom) (Φ z) (Φ t) where
  z_ne h := D.z_ne (Φ.injective (by simpa using h))
  z_sq := by rw [← map_mul, D.z_sq, map_one]
  t_ne h := D.t_ne (Φ.injective (by simpa using h))
  t_sq := by rw [← map_mul, D.t_sq, map_one]
  cls := by
    intro x hx1 hx2
    obtain ⟨y, rfl⟩ := Φ.surjective x
    have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hy2 : y * y = 1 := Φ.injective (by rw [map_mul, hx2, map_one])
    rcases D.cls y hy1 hy2 with h | h
    · exact Or.inl ((burnsideF4h_invree_isConj_map Φ).2 h)
    · exact Or.inr ((burnsideF4h_invree_isConj_map Φ).2 h)
  not_conj h := D.not_conj ((burnsideF4h_invree_isConj_map Φ).1 h)
  z_L := Subgroup.mem_map_of_mem _ D.z_L
  t_S := Subgroup.mem_map_of_mem _ D.t_S
  L_conj := by
    intro y hy hy1
    obtain ⟨y', hy', rfl⟩ := hy
    have : y' ≠ 1 := fun h => hy1 (by rw [h]; exact map_one _)
    exact (burnsideF4h_invree_isConj_map Φ).2 (D.L_conj y' hy' this)
  S_conj := by
    intro y hy hy1
    obtain ⟨y', hy', rfl⟩ := hy
    have : y' ≠ 1 := fun h => hy1 (by rw [h]; exact map_one _)
    exact (burnsideF4h_invree_isConj_map Φ).2 (D.S_conj y' hy' this)

theorem burnsideF4h_invree_conj_rep {E : Type} [Group E] {core : Subgroup E} {L : Subgroup core}
    {z : core} (hL : ∀ y ∈ L, y ≠ 1 → IsConj z y) {x c : E} (hc : c ∈ core) (hx1 : x ≠ 1)
    (hcx : c * x * c⁻¹ ∈ L.map core.subtype) :
    ∃ conjugator ∈ core, conjugator * x * conjugator⁻¹ = z := by
  obtain ⟨y, hy, hyx⟩ := hcx
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hx1
    have h1 : c * x * c⁻¹ = 1 := by rw [← hyx]; rfl
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨d, hd⟩ := isConj_iff.1 (hL y hy hy1)
  have hd' : (d : E) * (z : E) * (d : E)⁻¹ = c * x * c⁻¹ := by
    rw [← hyx, ← hd]
    rfl
  refine ⟨(d : E)⁻¹ * c, core.mul_mem (core.inv_mem d.2) hc, ?_⟩
  calc (d : E)⁻¹ * c * x * ((d : E)⁻¹ * c)⁻¹ = (d : E)⁻¹ * (c * x * c⁻¹) * (d : E) := by group
    _ = (d : E)⁻¹ * ((d : E) * (z : E) * (d : E)⁻¹) * (d : E) := by rw [hd']
    _ = z := by group

theorem burnsideF4h_invree_rootInvolution_iff {kind : ChF.GLKind} {prime degree : ℕ}
    {E : Type} [Group E] {core : Subgroup E} (chart : ChF.NativeChart kind prime degree core)
    (hkind : kind ≠ .G2d) {L S : Subgroup core} {z t : core}
    (D : burnsideF4h_invree_Datum L S z t) (hL : chart.longRoot = L.map core.subtype)
    (hS : chart.shortRoot = S.map core.subtype) (short : Bool) (x : E) :
    chart.RootInvolution short x ↔ x ∈ core ∧ ∃ conjugator ∈ core,
      conjugator * x * conjugator⁻¹ = ((if short then t else z : core) : E) := by
  constructor
  · rintro ⟨hx, hx1, -, -, c, hc, hcx⟩
    refine ⟨hx, ?_⟩
    cases short
    · rw [if_neg (by decide), hL] at hcx
      exact burnsideF4h_invree_conj_rep D.L_conj hc hx1 hcx
    · rw [if_pos rfl, hS] at hcx
      exact burnsideF4h_invree_conj_rep D.S_conj hc hx1 hcx
  · rintro ⟨hx, c, hc, hcx⟩
    have hrep : ∀ w : core, w ≠ 1 → w * w = 1 → c * x * c⁻¹ = (w : E) →
        x ≠ 1 ∧ x * x = 1 := by
      intro w hw1 hw2 hcw
      have hxw : x = c⁻¹ * (w : E) * c := by rw [← hcw]; group
      refine ⟨fun h => hw1 ?_, ?_⟩
      · apply Subtype.ext
        have : (w : E) = c * x * c⁻¹ := hcw.symm
        rw [this, h]
        simp
      · rw [hxw]
        calc c⁻¹ * (w : E) * c * (c⁻¹ * (w : E) * c) = c⁻¹ * ((w * w : core) : E) * c := by
              simp only [Subgroup.coe_mul]; group
          _ = 1 := by rw [hw2]; simp
    cases short
    · obtain ⟨h1, h2⟩ := hrep z D.z_ne D.z_sq (by simpa using hcx)
      refine ⟨hx, h1, h2, fun h => absurd h hkind, c, hc, ?_⟩
      rw [if_neg (by decide), hL]
      simp only [Bool.false_eq_true, ↓reduceIte] at hcx
      rw [hcx]
      exact Subgroup.mem_map_of_mem _ D.z_L
    · obtain ⟨h1, h2⟩ := hrep t D.t_ne D.t_sq (by simpa using hcx)
      refine ⟨hx, h1, h2, fun h => absurd h hkind, c, hc, ?_⟩
      rw [if_pos rfl, hS]
      simp only [↓reduceIte] at hcx
      rw [hcx]
      exact Subgroup.mem_map_of_mem _ D.t_S

theorem burnsideF4h_invree_goal_of_datum {kind : ChF.GLKind} {prime degree : ℕ}
    {E : Type} [Group E] {core : Subgroup E} (chart : ChF.NativeChart kind prime degree core)
    (hkind : kind ≠ .G2d) {L S : Subgroup core} {z t : core}
    (D : burnsideF4h_invree_Datum L S z t) (hL : chart.longRoot = L.map core.subtype)
    (hS : chart.shortRoot = S.map core.subtype) :
    ∃ long ∈ chart.longRoot, ∃ short ∈ chart.shortRoot,
      long ≠ 1 ∧ long * long = 1 ∧ short ≠ 1 ∧ short * short = 1 ∧
      (¬ ∃ conjugator ∈ core, conjugator * long * conjugator⁻¹ = short) ∧
      (∀ element : E, chart.RootInvolution false element ↔
        element ∈ core ∧ ∃ conjugator ∈ core,
          conjugator * element * conjugator⁻¹ = long) ∧
      (∀ element : E, chart.RootInvolution true element ↔
        element ∈ core ∧ ∃ conjugator ∈ core,
          conjugator * element * conjugator⁻¹ = short) ∧
      (∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element ∨ chart.RootInvolution true element) := by
  have hRI := burnsideF4h_invree_rootInvolution_iff chart hkind D hL hS
  refine ⟨z, by rw [hL]; exact Subgroup.mem_map_of_mem _ D.z_L,
    t, by rw [hS]; exact Subgroup.mem_map_of_mem _ D.t_S,
    fun h => D.z_ne (Subtype.ext h), by rw [← Subgroup.coe_mul, D.z_sq]; rfl,
    fun h => D.t_ne (Subtype.ext h), by rw [← Subgroup.coe_mul, D.t_sq]; rfl, ?_,
    fun x => by simpa using hRI false x, fun x => by simpa using hRI true x, ?_⟩
  · rintro ⟨c, hc, hct⟩
    exact D.not_conj (isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hct⟩)
  · intro x hx hx1 hx2
    have hx1' : (⟨x, hx⟩ : core) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hx2' : (⟨x, hx⟩ : core) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rcases D.cls _ hx1' hx2' with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      left
      refine (hRI false x).2 ⟨hx, (c⁻¹ : core), (c⁻¹ : core).2, ?_⟩
      have h' : (c : E) * z * (c : E)⁻¹ = x := congrArg Subtype.val hc
      simp only [Bool.false_eq_true, ↓reduceIte, InvMemClass.coe_inv]
      rw [← h']
      group
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      right
      refine (hRI true x).2 ⟨hx, (c⁻¹ : core), (c⁻¹ : core).2, ?_⟩
      have h' : (c : E) * t * (c : E)⁻¹ = x := congrArg Subtype.val hc
      simp only [↓reduceIte, InvMemClass.coe_inv]
      rw [← h']
      group

end Abstract

local instance burnsideF4h_invree_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

section WeylBasic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable {tag : Tag} {K : Type}
  [Field K]

theorem burnsideF4h_invree_weylWordOperator_eq (word : List (Fin tag.rank)) :
    weylWordOperator tag K word =
      ((((word.map fun i => weylElt tag K i 1).reverse).prod : (Module.End K (RootModule tag K))ˣ) :
        Module.End K (RootModule tag K)) := by
  unfold weylWordOperator
  have h := map_list_prod (Units.coeHom (Module.End K (RootModule tag K)))
    ((word.map fun i => weylElt tag K i 1).reverse)
  simp only [Units.coeHom_apply, List.map_reverse, List.map_map] at h
  rw [h]
  rfl

theorem burnsideF4h_invree_rootSubgroup_le_absoluteRoot {α : Fin tag.rank → ℤ}
    (hα : IsRoot tag α) : rootSubgroup tag K α ≤ absoluteRoot tag K α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine Subgroup.subset_closure ⟨(pinnedData tag α).2.2 • c, (pinnedData tag α).1,
    (pinnedData tag α).2.1.map tag.idx, pinnedWeyl tag K α, ?_, ?_, ?_⟩
  · rw [List.foldl_map]
    exact foldl_reflect_pinnedData hα
  · rw [burnsideF4h_invree_weylWordOperator_eq]
    congr 1
    unfold pinnedWeyl
    rw [List.map_map]
    rfl
  · rfl

theorem burnsideF4h_invree_comm_zero_three :
    weylElt Tag.F4 K 3 1 * weylElt Tag.F4 K 0 1 = weylElt Tag.F4 K 0 1 * weylElt Tag.F4 K 3 1 := by
  have h := prod_alternatingWord_weylElt Tag.F4 K (0 : Fin Tag.F4.rank) 3
  have e : Tag.F4.cartan 0 3 * Tag.F4.cartan 3 0 = 0 := by decide
  rw [e] at h
  simp [TauCeti.coxeterOrder_zero, CoxeterSystem.alternatingWord] at h
  exact h.symm

theorem burnsideF4h_invree_braid_one_two :
    (weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1) =
      weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 *
        weylElt Tag.F4 K 2 1 := by
  have h := prod_alternatingWord_weylElt Tag.F4 K (1 : Fin Tag.F4.rank) 2
  have e : Tag.F4.cartan 1 2 * Tag.F4.cartan 2 1 = 2 := by decide
  rw [e] at h
  simp [TauCeti.coxeterOrder_two, CoxeterSystem.alternatingWord] at h
  simpa only [mul_assoc] using h.symm

theorem burnsideF4h_invree_wordUnit_append (w₁ w₂ : List (Fin tag.rank)) :
    ((w₁ ++ w₂).map fun i => weylElt tag K i 1).reverse.prod =
      (w₂.map fun i => weylElt tag K i 1).reverse.prod *
        (w₁.map fun i => weylElt tag K i 1).reverse.prod := by
  simp [List.map_append, List.reverse_append, List.prod_append]

end WeylBasic

section WeylTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

variable
    {tag : Tag} {K : Type} [Field K]

theorem burnsideF4h_invree_absoluteRoot_le {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    absoluteRoot tag K α ≤ rootSubgroup tag K α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro e ⟨c, seed, word, actor, hfold, hact, he⟩
  have hactor : actor = (word.map fun i => weylElt tag K i 1).reverse.prod :=
    Units.ext (hact.trans (burnsideF4h_invree_weylWordOperator_eq word))
  have he' : e = actor * xUnit tag K seed c * actor⁻¹ := Units.ext he
  have h1 : xUnit tag K seed c ∈ rootSubgroup tag K (Pi.single seed 1) := by
    rw [← pinnedX_single]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  have h2 := map_conj_prod_weylElt_rootSubgroup K word.reverse (isRoot_single tag seed)
  rw [wordProd_reverse_smul, hfold] at h2
  have h3 : e ∈ (rootSubgroup tag K (Pi.single seed 1)).map
      (MulAut.conj (word.reverse.map fun i => weylElt tag K i 1).prod).toMonoidHom := by
    refine ⟨xUnit tag K seed c, h1, ?_⟩
    rw [he', hactor, List.map_reverse]
    rfl
  rw [h2] at h3
  exact h3

theorem burnsideF4h_invree_absoluteRoot_eq {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    absoluteRoot tag K α = rootSubgroup tag K α :=
  le_antisymm (burnsideF4h_invree_absoluteRoot_le hα)
    (burnsideF4h_invree_rootSubgroup_le_absoluteRoot hα)

end WeylTransport

section F4Words

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K]

theorem burnsideF4h_invree_weylOne_eq :
    weylOne K = weylElt Tag.F4 K 0 1 * weylElt Tag.F4 K 3 1 := by
  have hred : (coxeterSystem Tag.F4).IsReduced ([0, 3] : List (Fin Tag.F4.rank)) :=
    CFSG.LieType.Simplicity.isReduced_reeOrbitWord ReeTag.F4 (0 : Fin Tag.F4.rank)
  have h := canonicalRep_wordProd (R := K) (cs := coxeterSystem Tag.F4) hred
  have e : weylOne K =
      canonicalRep (coxeterSystem Tag.F4) K ((coxeterSystem Tag.F4).wordProd [0, 3]) := rfl
  rw [e, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem burnsideF4h_invree_weylTwo_eq :
    weylTwo K = weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 *
      weylElt Tag.F4 K 2 1 := by
  have hred : (coxeterSystem Tag.F4).IsReduced ([1, 2, 1, 2] : List (Fin Tag.F4.rank)) :=
    CFSG.LieType.Simplicity.isReduced_reeOrbitWord ReeTag.F4 (1 : Fin Tag.F4.rank)
  have h := canonicalRep_wordProd (R := K) (cs := coxeterSystem Tag.F4) hred
  have e : weylTwo K =
      canonicalRep (coxeterSystem Tag.F4) K ((coxeterSystem Tag.F4).wordProd [1, 2, 1, 2]) := rfl
  rw [e, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

theorem burnsideF4h_invree_wordUnit_zero :
    (([0, 3] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 K i 1).reverse.prod =
      weylOne K := by
  rw [burnsideF4h_invree_weylOne_eq]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one]
  exact burnsideF4h_invree_comm_zero_three

theorem burnsideF4h_invree_wordUnit_one :
    (([1, 2, 1, 2] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 K i 1).reverse.prod =
      weylTwo K := by
  rw [burnsideF4h_invree_weylTwo_eq]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have h := burnsideF4h_invree_braid_one_two (K := K)
  simp only [mul_assoc] at h
  exact h

end F4Words

section WeylConj

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots

variable {tag : Tag} {K : Type}
  [Field K]

theorem burnsideF4h_invree_fixedWeylConjugate_eq (model root : Subgroup (ModGL tag K))
    (word : List (Fin tag.rank)) (n : ModGL tag K) (hn : n ∈ model)
    (hop : (n : Module.End K (RootModule tag K)) = weylWordOperator tag K word) :
    fixedWeylConjugate tag K model word root = root.map (MulAut.conj n).toMonoidHom := by
  unfold fixedWeylConjugate
  have h : {element | ∃ actor : ModGL tag K, actor ∈ model ∧
      (actor : Module.End K (RootModule tag K)) = weylWordOperator tag K word ∧
      ∃ generator ∈ root, element = actor * generator * actor⁻¹} =
      ((root.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL tag K)) : Set (ModGL tag K)) := by
    ext x
    constructor
    · rintro ⟨actor, -, hact, g, hg, rfl⟩
      have : actor = n := Units.ext (hact.trans hop.symm)
      subst this
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨n, hn, hop, g, hg, rfl⟩
  rw [h]
  exact Subgroup.closure_eq _

end WeylConj

section LongShort

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_invree_reeGroup_eq : reeGroup K a = F4.reeGamma K a :=
  (reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a)).symm

theorem burnsideF4h_invree_weylOne_mem : weylOne K ∈ reeGroup K a := by
  rw [burnsideF4h_invree_reeGroup_eq]
  exact LargeReeInvolution.weylOne_mem

theorem burnsideF4h_invree_weylTwo_mem : weylTwo K ∈ reeGroup K a := by
  rw [burnsideF4h_invree_reeGroup_eq]
  exact LargeReeInvolution.weylTwo_mem

theorem burnsideF4h_invree_longActor :
    (([0, 3, 1, 2, 1, 2, 0, 3] : List (Fin Tag.F4.rank)).map
      fun i => weylElt Tag.F4 K i 1).reverse.prod = weylOne K * weylTwo K * weylOne K := by
  have h : ([0, 3, 1, 2, 1, 2, 0, 3] : List (Fin Tag.F4.rank)) = [0, 3] ++ [1, 2, 1, 2] ++ [0, 3] :=
    rfl
  rw [h, burnsideF4h_invree_wordUnit_append, burnsideF4h_invree_wordUnit_append,
    burnsideF4h_invree_wordUnit_zero, burnsideF4h_invree_wordUnit_one, mul_assoc]
  rfl

theorem burnsideF4h_invree_shortActor :
    (([1, 2, 1, 2, 0, 3, 1, 2, 1, 2] : List (Fin Tag.F4.rank)).map
      fun i => weylElt Tag.F4 K i 1).reverse.prod = weylTwo K * weylOne K * weylTwo K := by
  have h : ([1, 2, 1, 2, 0, 3, 1, 2, 1, 2] : List (Fin Tag.F4.rank)) =
      [1, 2, 1, 2] ++ [0, 3] ++ [1, 2, 1, 2] := rfl
  rw [h, burnsideF4h_invree_wordUnit_append, burnsideF4h_invree_wordUnit_append,
    burnsideF4h_invree_wordUnit_zero, burnsideF4h_invree_wordUnit_one, mul_assoc]
  rfl

theorem burnsideF4h_invree_reeLongRoot_eq :
    reeLongRoot K a = (reeMiddleCentralRoot K a).map
      (MulAut.conj (weylOne K * weylTwo K * weylOne K)).toMonoidHom := by
  unfold ChF.ExceptionalRoots.reeLongRoot
  refine burnsideF4h_invree_fixedWeylConjugate_eq _ _ _ _ ?_ ?_
  · exact mul_mem (mul_mem burnsideF4h_invree_weylOne_mem burnsideF4h_invree_weylTwo_mem)
      burnsideF4h_invree_weylOne_mem
  · rw [burnsideF4h_invree_weylWordOperator_eq, burnsideF4h_invree_longActor]

theorem burnsideF4h_invree_reeShortRoot_eq :
    reeShortRoot K a = (reeTwoRoot K a).map
      (MulAut.conj (weylTwo K * weylOne K * weylTwo K)).toMonoidHom := by
  unfold ChF.ExceptionalRoots.reeShortRoot
  refine burnsideF4h_invree_fixedWeylConjugate_eq _ _ _ _ ?_ ?_
  · exact mul_mem (mul_mem burnsideF4h_invree_weylTwo_mem burnsideF4h_invree_weylOne_mem)
      burnsideF4h_invree_weylTwo_mem
  · rw [burnsideF4h_invree_weylWordOperator_eq, burnsideF4h_invree_shortActor]

end LongShort

theorem burnsideF4h_invree_le_normalizer_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ K, Commute x y) : H ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have e : x * y * x⁻¹ = y := by
      rw [(h x hx y hy).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hy
  · intro hy
    have h2 := (h x⁻¹ (H.inv_mem hx) _ hy).eq
    have e : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = (x * y * x⁻¹) * x⁻¹ * x := by rw [h2]
        _ = x * y * x⁻¹ := by group
    rw [e]
    exact hy

section LongShortB

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_invree_reeFourSeed_eq (i : Fin 4) : reeFourSeed i = largeReeRoot i := by
  fin_cases i <;> rfl

open scoped Pointwise in
theorem burnsideF4h_invree_middleCentral_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ModGL Tag.F4 K} (hg : g ∈ reeMiddleCentralRoot K a) :
    ∃ v : K, g = largeReeCoord a K 0 v := by
  obtain ⟨hgΓ, hgJ⟩ := Subgroup.mem_inf.1 hg
  rw [burnsideF4h_invree_reeGroup_eq] at hgΓ
  have e2 : absoluteRoot Tag.F4 K (reeFourSeed 2) = rootSubgroup Tag.F4 K (largeReeRoot 2) := by
    rw [burnsideF4h_invree_reeFourSeed_eq]
    exact burnsideF4h_invree_absoluteRoot_eq (largeReeRoot_pos 2).1
  have e3 : absoluteRoot Tag.F4 K (reeFourSeed 3) = rootSubgroup Tag.F4 K (largeReeRoot 3) := by
    rw [burnsideF4h_invree_reeFourSeed_eq]
    exact burnsideF4h_invree_absoluteRoot_eq (largeReeRoot_pos 3).1
  rw [e2, e3] at hgJ
  have h2 : (2 : K) = 0 := F4_two_eq_zero
  have hcomm : ∀ x ∈ rootSubgroup Tag.F4 K (largeReeRoot 2),
      ∀ y ∈ rootSubgroup Tag.F4 K (largeReeRoot 3), Commute x y :=
    (large_Ree_B2_characteristic_two_commutators K h2).2.1 2 3 (by decide) (by decide)
  have hle := burnsideF4h_invree_le_normalizer_of_commute hcomm
  have hmem : g ∈ ((rootSubgroup Tag.F4 K (largeReeRoot 2) : Subgroup (ModGL Tag.F4 K)) :
      Set (ModGL Tag.F4 K)) * (rootSubgroup Tag.F4 K (largeReeRoot 3) : Set (ModGL Tag.F4 K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hgJ
  rw [Set.mem_mul] at hmem
  obtain ⟨x, hx, y, hy, rfl⟩ := hmem
  obtain ⟨C, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨D, rfl⟩ := mem_rootSubgroup.1 hy
  have hP : pinnedX Tag.F4 K (largeReeRoot 2) C * pinnedX Tag.F4 K (largeReeRoot 3) D =
      largeReeP K 0 0 C D := by
    simp [largeReeP, largeReeX, pinnedX_zero]
  have hU : pinnedX Tag.F4 K (largeReeRoot 2) C * pinnedX Tag.F4 K (largeReeRoot 3) D ∈
      F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := by
    refine Subgroup.mem_inf.2 ⟨?_, hgΓ⟩
    rw [F4_fixedOrbitRoots_one, hP]
    exact largeReeP_mem_rootSpan _ _ _ _
  obtain ⟨p, -, hp⟩ := (bijOn_largeReeCoord hK).2.2 hU
  have hp' : largeReeP K p.1 (largeReeSigma a p.1) p.2
      (largeReeSigma a p.2 + p.1 ^ 2 * largeReeSigma a p.1) = largeReeP K 0 0 C D := by
    rw [← hP, ← hp]
    rfl
  obtain ⟨h1, -, -, -⟩ := largeReeP_injective hp'
  refine ⟨p.2, ?_⟩
  rw [← hp]
  show largeReeCoord a K p.1 p.2 = _
  rw [h1]

theorem burnsideF4h_invree_coord_mem_middleCentral (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : K) :
    largeReeCoord a K 0 v ∈ reeMiddleCentralRoot K a := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h : largeReeCoord a K 0 v ∈ F4.reeGamma K a :=
      (Subgroup.mem_inf.1 (largeReeCoord_mem hK 0 v)).2
    rw [burnsideF4h_invree_reeGroup_eq]
    exact h
  · have e : largeReeCoord a K 0 v =
        pinnedX Tag.F4 K (reeFourSeed 2) v *
          pinnedX Tag.F4 K (reeFourSeed 3) (largeReeSigma a v) := by
      simp [largeReeCoord, largeReeP, largeReeX, burnsideF4h_invree_reeFourSeed_eq, pinnedX_zero,
        largeReeSigma_zero]
    rw [e]
    have hr2 : IsRoot Tag.F4 (reeFourSeed 2) := by
      rw [burnsideF4h_invree_reeFourSeed_eq]; exact (largeReeRoot_pos 2).1
    have hr3 : IsRoot Tag.F4 (reeFourSeed 3) := by
      rw [burnsideF4h_invree_reeFourSeed_eq]; exact (largeReeRoot_pos 3).1
    exact mul_mem
      (Subgroup.mem_sup_left (burnsideF4h_invree_rootSubgroup_le_absoluteRoot hr2
        (Subgroup.subset_closure ⟨v, rfl⟩)))
      (Subgroup.mem_sup_right (burnsideF4h_invree_rootSubgroup_le_absoluteRoot hr3
        (Subgroup.subset_closure ⟨largeReeSigma a v, rfl⟩)))

open CFSG.LieType.Ree.LargeReeCover in
theorem burnsideF4h_invree_sylowA_eq_stdTwoG (s : K) : sylowA a K s = stdTwoG a s := by
  have h : stdTwoRoot 0 = RootOps.orbitCertRoot F4.tag 24 ∧
      stdTwoRoot 1 = RootOps.orbitCertRoot F4.tag 33 := by
    decide +kernel
  rw [stdTwoG, sylowA, sylowX, sylowX, h.1, h.2]

theorem burnsideF4h_invree_reeLongRoot_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ModGL Tag.F4 K} (hy : y ∈ reeLongRoot K a) : ∃ v : K, y = centralZ K a v := by
  rw [burnsideF4h_invree_reeLongRoot_eq] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨v, rfl⟩ := burnsideF4h_invree_middleCentral_coord hK hg
  refine ⟨v, ?_⟩
  have h := weyl_conj_sylowB_zero (m := a) (K := K) v
  rw [sylowH_zero_eq_centralZ, sylowB_eq_largeReeCoord] at h
  exact h

theorem burnsideF4h_invree_centralZ_mem_reeLongRoot (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : K) :
    centralZ K a v ∈ reeLongRoot K a := by
  rw [burnsideF4h_invree_reeLongRoot_eq]
  refine ⟨largeReeCoord a K 0 v, burnsideF4h_invree_coord_mem_middleCentral hK v, ?_⟩
  have h := weyl_conj_sylowB_zero (m := a) (K := K) v
  rw [sylowH_zero_eq_centralZ, sylowB_eq_largeReeCoord] at h
  exact h

open scoped Pointwise in
theorem burnsideF4h_invree_reeTwoRoot_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ModGL Tag.F4 K} (hg : g ∈ reeTwoRoot K a) : ∃ s : K, g = sylowA a K s := by
  obtain ⟨hgΓ0, hgJ⟩ := Subgroup.mem_inf.1 hg
  have hgΓ : g ∈ F4.reeGamma K a := by
    have h : g ∈ reeGroup K a := hgΓ0
    rw [burnsideF4h_invree_reeGroup_eq] at h
    exact h
  have e0 : absoluteRoot Tag.F4 K (Pi.single 0 1) = rootSubgroup Tag.F4 K (Pi.single 0 1) :=
    burnsideF4h_invree_absoluteRoot_eq (isRoot_single Tag.F4 _)
  have e3 : absoluteRoot Tag.F4 K (Pi.single 3 1) = rootSubgroup Tag.F4 K (Pi.single 3 1) :=
    burnsideF4h_invree_absoluteRoot_eq (isRoot_single Tag.F4 _)
  rw [e0, e3] at hgJ
  have hU : g ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
    refine Subgroup.mem_inf.2 ⟨?_, hgΓ⟩
    rw [F4_fixedOrbitRoots_zero]
    have h0 : rootSubgroup Tag.F4 K (Pi.single 0 1) ≤
        rootSpan Tag.F4 K {Pi.single largeReeI1 1, Pi.single largeReeI4 1} :=
      le_iSup₂_of_le (Pi.single largeReeI1 1) (Set.mem_insert _ _) le_rfl
    have h3 : rootSubgroup Tag.F4 K (Pi.single 3 1) ≤
        rootSpan Tag.F4 K {Pi.single largeReeI1 1, Pi.single largeReeI4 1} :=
      le_iSup₂_of_le (Pi.single largeReeI4 1) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        le_rfl
    exact (sup_le h0 h3) hgJ
  obtain ⟨s, hs⟩ := exists_stdTwoG_eq hK hU
  exact ⟨s, by rw [burnsideF4h_invree_sylowA_eq_stdTwoG, hs]⟩

theorem burnsideF4h_invree_sylowA_mem_reeTwoRoot (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : K) :
    sylowA a K s ∈ reeTwoRoot K a := by
  have hU : sylowA a K s ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
    rw [burnsideF4h_invree_sylowA_eq_stdTwoG]
    exact stdTwoG_mem hK s
  have hΓ : sylowA a K s ∈ reeGroup K a := by
    have h : sylowA a K s ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hU).2
    rw [burnsideF4h_invree_reeGroup_eq]
    exact h
  refine ⟨hΓ, ?_⟩
  · rw [burnsideF4h_invree_sylowA_eq_stdTwoG, stdTwoG,
      (stdTwoRoot_eq_single).1, (stdTwoRoot_eq_single).2]
    exact mul_mem
      (Subgroup.mem_sup_right (burnsideF4h_invree_rootSubgroup_le_absoluteRoot
        (isRoot_single Tag.F4 _) (Subgroup.subset_closure ⟨s, rfl⟩)))
      (Subgroup.mem_sup_left (burnsideF4h_invree_rootSubgroup_le_absoluteRoot
        (isRoot_single Tag.F4 _) (Subgroup.subset_closure ⟨largeReeSigma a s, rfl⟩)))

theorem burnsideF4h_invree_reeShortRoot_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ModGL Tag.F4 K} (hy : y ∈ reeShortRoot K a) :
    ∃ s : K, y = (weylTwo K * weylOne K * weylTwo K) * sylowA a K s *
      (weylTwo K * weylOne K * weylTwo K)⁻¹ := by
  rw [burnsideF4h_invree_reeShortRoot_eq] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨s, rfl⟩ := burnsideF4h_invree_reeTwoRoot_coord hK hg
  exact ⟨s, rfl⟩

theorem burnsideF4h_invree_sylowL_mem_reeShortRoot (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    sylowL a K 1 ∈ reeShortRoot K a := by
  rw [burnsideF4h_invree_reeShortRoot_eq]
  refine ⟨sylowA a K 1, burnsideF4h_invree_sylowA_mem_reeTwoRoot hK 1, ?_⟩
  have h := weyl_conj_sylowA_one (m := a) (K := K)
  exact h

theorem burnsideF4h_invree_reeShortRoot_conj (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ModGL Tag.F4 K} (hy : y ∈ reeShortRoot K a) (hy1 : y ≠ 1) :
    ∃ c ∈ F4.reeGamma K a, c * sylowL a K 1 * c⁻¹ = y := by
  obtain ⟨s, rfl⟩ := burnsideF4h_invree_reeShortRoot_coord hK hy
  have hs : s ≠ 0 := by
    rintro rfl
    apply hy1
    rw [sylowA_zero, mul_one, mul_inv_cancel]
    rfl
  obtain ⟨h, hh, hhs⟩ := exists_torus_conj_sylowA hK one_ne_zero hs
  have hn : weylTwo K * weylOne K * weylTwo K ∈ F4.reeGamma K a :=
    mul_mem (mul_mem LargeReeInvolution.weylTwo_mem LargeReeInvolution.weylOne_mem)
      LargeReeInvolution.weylTwo_mem
  refine ⟨(weylTwo K * weylOne K * weylTwo K) * h * (weylTwo K * weylOne K * weylTwo K)⁻¹,
    mul_mem (mul_mem hn (Subgroup.mem_inf.1 hh).2) (inv_mem hn), ?_⟩
  have h1 := weyl_conj_sylowA_one (m := a) (K := K)
  rw [← h1, ← hhs]
  group

end LongShortB

section GLevel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_invree_of_orderOf_two {G : Type*} [Group G] {x : G} (h : orderOf x = 2) :
    x ≠ 1 ∧ x * x = 1 := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [orderOf_one] at h
    omega
  · rw [← sq]
    have := pow_orderOf_eq_one x
    rwa [h] at this

theorem burnsideF4h_invree_orderOf_eq_two {G : Type*} [Group G] {x : G} (h1 : x ≠ 1)
    (h2 : x * x = 1) : orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact h2) h1

theorem burnsideF4h_invree_coe_zg (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (zg hK : ModGL F4.tag K) = centralZ K a 1 := by
  rw [coe_zg]
  exact (CFSG.LocalAnalysis.EvenBN.TwoF4.invE_eq_centralZ (K := K) (a := a)).1

theorem burnsideF4h_invree_coe_tg (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (tg hK : ModGL F4.tag K) = sylowL a K 1 := by
  rw [coe_tg]
  exact (CFSG.LocalAnalysis.EvenBN.TwoF4.invE_eq_centralZ (K := K) (a := a)).2

theorem burnsideF4h_invree_centralZ_comm {u : ModGL F4.tag K}
    (hu : u ∈ F4.reeFixedPosUnipotent K a) (c : K) :
    u * centralZ K a c = centralZ K a c * u := by
  haveI : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  have hu' : u ∈ posUnipotent Tag.F4 K := (Subgroup.mem_inf.1 hu).1
  have h44 : Commute u (f4x K 44 c) := f4x_central (Or.inl rfl) c hu'
  have h47 : Commute u (f4x K 47 (c ^ (2 * 2 ^ a))) := f4x_central (Or.inr rfl) _ hu'
  have e : centralZ K a c = f4x K 44 c * f4x K 47 (c ^ (2 * 2 ^ a)) := by
    rw [CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.f4x_44,
      CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.f4x_47]
    rfl
  rw [e]
  exact (h44.mul_right h47).eq

theorem burnsideF4h_invree_zg_inv (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    zg hK ≠ 1 ∧ zg hK * zg hK = 1 :=
  burnsideF4h_invree_of_orderOf_two (orderOf_zg hK)

theorem burnsideF4h_invree_tg_inv (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    tg hK ≠ 1 ∧ tg hK * tg hK = 1 :=
  burnsideF4h_invree_of_orderOf_two (orderOf_tg hK)

theorem burnsideF4h_invree_zg_LR (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    zg hK ∈ (reeLongRoot K a).subgroupOf (F4.reeGamma K a) := by
  refine Subgroup.mem_subgroupOf.2 ?_
  rw [burnsideF4h_invree_coe_zg]
  exact burnsideF4h_invree_centralZ_mem_reeLongRoot hK 1

theorem burnsideF4h_invree_tg_SR (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    tg hK ∈ (reeShortRoot K a).subgroupOf (F4.reeGamma K a) := by
  refine Subgroup.mem_subgroupOf.2 ?_
  rw [burnsideF4h_invree_coe_tg]
  exact burnsideF4h_invree_sylowL_mem_reeShortRoot hK

theorem burnsideF4h_invree_SR_conj (hK : Nat.card K = 2 ^ (2 * a + 1))
    (y : Gm K a) (hy : y ∈ (reeShortRoot K a).subgroupOf (F4.reeGamma K a)) (hy1 : y ≠ 1) :
    IsConj (tg hK) y := by
  have hy' := Subgroup.mem_subgroupOf.1 hy
  obtain ⟨c, hc, hcy⟩ := burnsideF4h_invree_reeShortRoot_conj hK hy'
    (fun h => hy1 (Subtype.ext (by rw [h]; rfl)))
  refine isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, burnsideF4h_invree_coe_tg]
  exact hcy

theorem burnsideF4h_invree_cls_large (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (x : Gm K a) (hx1 : x ≠ 1) (hx2 : x * x = 1) : IsConj (zg hK) x ∨ IsConj (tg hK) x :=
  cls_gm ha hK x (burnsideF4h_invree_orderOf_eq_two hx1 hx2)

theorem burnsideF4h_invree_not_conj_large (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ IsConj (zg hK) (tg hK) := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact noconj_gm ha hK (MulAut.conj c) (by rw [MulAut.conj_apply]; exact hc)

theorem burnsideF4h_invree_LR_conj_large (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (y : Gm K a) (hy : y ∈ (reeLongRoot K a).subgroupOf (F4.reeGamma K a)) (hy1 : y ≠ 1) :
    IsConj (zg hK) y := by
  obtain ⟨v, hv⟩ := burnsideF4h_invree_reeLongRoot_coord hK (Subgroup.mem_subgroupOf.1 hy)
  have hyU : y ∈ Ug K a := by
    refine Subgroup.mem_subgroupOf.2 ?_
    rw [hv]
    exact centralZ_mem ha hK v
  have hcomm : ∀ u ∈ Ug K a, u * y = y * u := by
    intro u hu
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hv]
    exact burnsideF4h_invree_centralZ_comm (Subgroup.mem_subgroupOf.1 hu) v
  obtain ⟨h, -, hh⟩ := center_gm ha hK y hyU hcomm hy1
  exact isConj_iff.2 ⟨h, hh⟩

theorem burnsideF4h_invree_datum_large (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    burnsideF4h_invree_Datum (G := Gm K a) ((reeLongRoot K a).subgroupOf (F4.reeGamma K a))
      ((reeShortRoot K a).subgroupOf (F4.reeGamma K a)) (zg hK) (tg hK) where
  z_ne := (burnsideF4h_invree_zg_inv hK).1
  z_sq := (burnsideF4h_invree_zg_inv hK).2
  t_ne := (burnsideF4h_invree_tg_inv hK).1
  t_sq := (burnsideF4h_invree_tg_inv hK).2
  cls := burnsideF4h_invree_cls_large ha hK
  not_conj := burnsideF4h_invree_not_conj_large ha hK
  z_L := burnsideF4h_invree_zg_LR hK
  t_S := burnsideF4h_invree_tg_SR hK
  L_conj := burnsideF4h_invree_LR_conj_large ha hK
  S_conj := burnsideF4h_invree_SR_conj hK

end GLevel

section GroupTools

theorem burnsideF4h_invree_centralizer_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Subgroup.centralizer ({e a} : Set B) =
      (Subgroup.centralizer ({a} : Set A)).map e.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨x, ?_, rfl⟩
    have : e a * e x = e x * e a := h
    exact e.injective (by simpa using this)
  · rintro ⟨x', hx', hx'e⟩
    have hx : x' = x := e.injective hx'e
    subst hx
    have : a * x' = x' * a := hx'
    simpa using congrArg e this

theorem burnsideF4h_invree_card_centralizer_of_isConj {G : Type*} [Group G] {x y : G}
    (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card (Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [← CFSG.Sporadic.Schreier.Tits.map_conj_centralizer,
    Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem burnsideF4h_invree_card_centralizer_map {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (a : A) :
    Nat.card (Subgroup.centralizer ({e a} : Set B)) =
      Nat.card (Subgroup.centralizer ({a} : Set A)) := by
  rw [burnsideF4h_invree_centralizer_map e a, Subgroup.card_map_of_injective e.injective]

theorem burnsideF4h_invree_eq_one_of_ne_zero {L : Type*} [Field L] [Finite L] (hL : Nat.card L = 2)
    {v : L} (hv : v ≠ 0) : v = 1 := by
  have h2 : Nat.card Lˣ = 1 := by rw [Nat.card_units, hL]
  haveI : Subsingleton Lˣ := (Nat.card_eq_one_iff_unique.1 h2).1
  exact congrArg Units.val (Subsingleton.elim (Units.mk0 v hv) 1)

end GroupTools

section TitsModel

open CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false


theorem burnsideF4h_invree_titsZ_mem : titsZ ∈ titsA := titsD_le_titsA titsZ_mem_titsD

theorem burnsideF4h_invree_titsTInv_mem : titsTInv ∈ titsA := titsD_le_titsA titsTInv_mem_titsD

theorem burnsideF4h_invree_card_centralizer_titsZ :
    Nat.card (Subgroup.centralizer
      ({(⟨titsZ, burnsideF4h_invree_titsZ_mem⟩ : ↥titsA)} : Set ↥titsA)) = 20480 := by
  rw [← Subgroup.card_map_of_injective titsA.subtype_injective, map_subtype_centralizer]
  change Nat.card (titsA ⊓ Subgroup.centralizer {titsZ} : Subgroup (Equiv.Perm (Fin 1755))) = _
  rw [CFSG.LocalAnalysis.EvenBN.Tits.Model.centralizer_titsZ_eq,
    CFSG.LocalAnalysis.EvenBN.Tits.Model.card_twoF4H]

theorem burnsideF4h_invree_card_centralizer_titsTInv :
    Nat.card (Subgroup.centralizer
      ({(⟨titsTInv, burnsideF4h_invree_titsTInv_mem⟩ : ↥titsA)} : Set ↥titsA)) = 3072 := by
  rw [← Subgroup.card_map_of_injective titsA.subtype_injective, map_subtype_centralizer]
  exact CFSG.LocalAnalysis.EvenBN.Tits.Model.card_centralizer_titsTInv.1

theorem burnsideF4h_invree_titsA_involution {w : ↥titsA} (hw : orderOf w = 2) :
    IsConj (⟨titsZ, burnsideF4h_invree_titsZ_mem⟩ : ↥titsA) w ∨
      IsConj (⟨titsTInv, burnsideF4h_invree_titsTInv_mem⟩ : ↥titsA) w := by
  have hw' : orderOf (w : Equiv.Perm (Fin 1755)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hw
  obtain ⟨-, d, hd, h⟩ := CFSG.LocalAnalysis.EvenBN.Tits.Model.titsA_involution_conj w.2 hw'
  rcases h with h | h
  · exact Or.inl (isConj_iff.2 ⟨⟨d, titsD_le_titsA hd⟩, Subtype.ext h⟩)
  · exact Or.inr (isConj_iff.2 ⟨⟨d, titsD_le_titsA hd⟩, Subtype.ext h⟩)

theorem burnsideF4h_invree_titsA_not_conj :
    ¬ IsConj (⟨titsZ, burnsideF4h_invree_titsZ_mem⟩ : ↥titsA)
      (⟨titsTInv, burnsideF4h_invree_titsTInv_mem⟩ : ↥titsA) := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have h' := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
  exact CFSG.LocalAnalysis.EvenBN.Tits.Model.titsA_conj_titsZ_ne_titsTInv c.2 h'

theorem burnsideF4h_invree_classes_of_equiv {G : Type*} [Group G] (ψ : G ≃* ↥titsA) :
    ∃ Z T : G, Nat.card (Subgroup.centralizer ({Z} : Set G)) = 20480 ∧
      Nat.card (Subgroup.centralizer ({T} : Set G)) = 3072 ∧
      (∀ x : G, orderOf x = 2 → IsConj Z x ∨ IsConj T x) ∧ ¬ IsConj Z T := by
  refine ⟨ψ.symm ⟨titsZ, burnsideF4h_invree_titsZ_mem⟩,
    ψ.symm ⟨titsTInv, burnsideF4h_invree_titsTInv_mem⟩, ?_, ?_, ?_, ?_⟩
  · rw [← burnsideF4h_invree_card_centralizer_map ψ, MulEquiv.apply_symm_apply]
    exact burnsideF4h_invree_card_centralizer_titsZ
  · rw [← burnsideF4h_invree_card_centralizer_map ψ, MulEquiv.apply_symm_apply]
    exact burnsideF4h_invree_card_centralizer_titsTInv
  · intro x hx
    have hx' : orderOf (ψ x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
    rcases burnsideF4h_invree_titsA_involution hx' with h | h
    · left
      rw [← burnsideF4h_invree_isConj_map ψ, MulEquiv.apply_symm_apply]
      exact h
    · right
      rw [← burnsideF4h_invree_isConj_map ψ, MulEquiv.apply_symm_apply]
      exact h
  · intro h
    apply burnsideF4h_invree_titsA_not_conj
    have h' := (burnsideF4h_invree_isConj_map ψ).2 h
    simpa only [MulEquiv.apply_symm_apply] using h'

end TitsModel

section Small

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_invree_nonempty_equiv (hK : Nat.card K = 2) :
    Nonempty (Gm K 0 ≃* ↥CFSG.Sporadic.Schreier.Tits.titsA) := by
  haveI : Fact (Nat.card K = 2) := ⟨hK⟩
  exact ⟨(reeFixedEquivReeGamma K 0).symm.trans (CFSG.Sporadic.Schreier.Tits.titsIso (K := K))⟩

theorem burnsideF4h_invree_card_reeLocalParabolic (j : Fin F4.fixedOrbitCount) :
    Nat.card (F4.reeLocalParabolic K a j) = Nat.card (F4.reeFixedBorel K a) *
      (Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1) := by
  have hfin : Finite (ModGL F4.tag K) := finite_modGL
  have hBP : F4.reeFixedBorel K a ≤ F4.reeLocalParabolic K a j :=
    reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
  have hidx : (F4.reeFixedBorel K a).relIndex (F4.reeLocalParabolic K a j) =
      Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1 := by
    rw [← CFSG.QuasithinUnique.Setup.X6.ncard_image_coset_eq_relIndex]
    change (F4.reeLocalCosets K a j).ncard = _
    rw [ncard_reeLocalCosets]
  have h := Subgroup.relIndex_mul_card (F4.reeFixedBorel K a) (F4.reeLocalParabolic K a j)
  rw [inf_eq_left.2 hBP, hidx] at h
  rw [mul_comm]
  exact h.symm

theorem burnsideF4h_invree_card_Pg_zero (hK : Nat.card K = 2 ^ (2 * 0 + 1)) :
    Nat.card (Pg K 0 ⟨0, by decide⟩) = 12288 := by
  have hle : F4.reeLocalParabolic K 0 ⟨0, by decide⟩ ≤ F4.reeGamma K 0 := inf_le_left
  rw [Pg, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    burnsideF4h_invree_card_reeLocalParabolic, CFSG.RankThree.LargeReeOrder.card_reeFixedBorel hK,
    card_reeFixedOrbitUnipotent_zero hK, hK]
  norm_num

theorem burnsideF4h_invree_card_Ug (hK : Nat.card K = 2 ^ (2 * 0 + 1)) :
    Nat.card (Ug K 0) = 4096 := by
  have hle : F4.reeFixedPosUnipotent K 0 ≤ F4.reeGamma K 0 := reeFixedPosUnipotent_le_reeGamma
  rw [Ug, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    card_reeFixedPosUnipotent hK]
  norm_num

theorem burnsideF4h_invree_Ug_le_centralizer_zg (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Ug K a ≤ Subgroup.centralizer ({zg hK} : Set (Gm K a)) := by
  intro u hu
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, burnsideF4h_invree_coe_zg]
  exact burnsideF4h_invree_centralZ_comm (Subgroup.mem_subgroupOf.1 hu) 1

theorem burnsideF4h_invree_LR_conj_small (hK : Nat.card K = 2 ^ (2 * 0 + 1))
    (y : Gm K 0) (hy : y ∈ (reeLongRoot K 0).subgroupOf (F4.reeGamma K 0)) (hy1 : y ≠ 1) :
    IsConj (zg hK) y := by
  obtain ⟨v, hv⟩ := burnsideF4h_invree_reeLongRoot_coord hK (Subgroup.mem_subgroupOf.1 hy)
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hy1
    apply Subtype.ext
    rw [hv, centralZ_zero]
    rfl
  have hv1 : v = 1 := burnsideF4h_invree_eq_one_of_ne_zero (by simpa using hK) hv0
  have hyz : y = zg hK := by
    apply Subtype.ext
    rw [hv, hv1, burnsideF4h_invree_coe_zg]
  rw [hyz]

theorem burnsideF4h_invree_datum_small (hK : Nat.card K = 2 ^ (2 * 0 + 1)) :
    burnsideF4h_invree_Datum (G := Gm K 0) ((reeLongRoot K 0).subgroupOf (F4.reeGamma K 0))
      ((reeShortRoot K 0).subgroupOf (F4.reeGamma K 0)) (zg hK) (tg hK) := by
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨ψ⟩ := burnsideF4h_invree_nonempty_equiv hK2
  obtain ⟨Z, T, hZc, hTc, hcls, hnc⟩ := burnsideF4h_invree_classes_of_equiv ψ
  have hz : IsConj Z (zg hK) := by
    rcases hcls (zg hK) (orderOf_zg hK) with h | h
    · exact h
    · exfalso
      have hdvd := Subgroup.card_dvd_of_le (burnsideF4h_invree_Ug_le_centralizer_zg hK)
      rw [burnsideF4h_invree_card_Ug hK, ← burnsideF4h_invree_card_centralizer_of_isConj h,
        hTc] at hdvd
      norm_num at hdvd
  have ht : IsConj T (tg hK) := by
    rcases hcls (tg hK) (orderOf_tg hK) with h | h
    · exfalso
      have hdvd := Subgroup.card_dvd_of_le (centralizer_tg_le hK)
      rw [burnsideF4h_invree_card_Pg_zero hK, ← burnsideF4h_invree_card_centralizer_of_isConj h,
        hZc] at hdvd
      norm_num at hdvd
    · exact h
  exact
    { z_ne := (burnsideF4h_invree_zg_inv hK).1
      z_sq := (burnsideF4h_invree_zg_inv hK).2
      t_ne := (burnsideF4h_invree_tg_inv hK).1
      t_sq := (burnsideF4h_invree_tg_inv hK).2
      cls := fun x hx1 hx2 => by
        rcases hcls x (burnsideF4h_invree_orderOf_eq_two hx1 hx2) with h | h
        · exact Or.inl (hz.symm.trans h)
        · exact Or.inr (ht.symm.trans h)
      not_conj := fun h => hnc (hz.trans (h.trans ht.symm))
      z_L := burnsideF4h_invree_zg_LR hK
      t_S := burnsideF4h_invree_tg_SR hK
      L_conj := burnsideF4h_invree_LR_conj_small hK
      S_conj := burnsideF4h_invree_SR_conj hK }

end Small

section Chart

open CFSG.ASVolI.ChF

theorem burnsideF4h_invree_exists_quotEquiv {G : Type*} [Group G] (hz : Subgroup.center G = ⊥) :
    ∃ e : G ≃* (G ⧸ Subgroup.center G), ∀ x : G, e x = (x : G ⧸ Subgroup.center G) :=
  ⟨MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center G))
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hz]),
      QuotientGroup.mk'_surjective _⟩, fun _ => rfl⟩

theorem burnsideF4h_invree_chart_data {E : Type} [Group E] {degree : ℕ} {core : Subgroup E}
    (chart : NativeChart .F4tw 2 degree core) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (a : ℕ),
      ExceptionalRoots.ReeScope K a ∧
      ∃ marking : (ExceptionalRoots.reeGroup K a ⧸
          Subgroup.center (ExceptionalRoots.reeGroup K a)) ≃* core,
        chart.longRoot = ((ExceptionalRoots.centralImage (ExceptionalRoots.reeGroup K a)
          (ExceptionalRoots.reeLongRoot K a)).map marking.toMonoidHom).map core.subtype ∧
        chart.shortRoot = ((ExceptionalRoots.centralImage (ExceptionalRoots.reeGroup K a)
          (ExceptionalRoots.reeShortRoot K a)).map marking.toMonoidHom).map core.subtype := by
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, hd, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, -⟩⟩
  · exfalso
    cases c <;> exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact ⟨K, fK, finK, charK, exponent, scope, marking, h4, h5⟩
  · exact absurd hk (by decide)

end Chart

section Marking

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_invree_center_trivial (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.center ↥(reeGroup K a) = ⊥ := by
  have e : reeGroup K a = F4.reeGamma K a :=
    (reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a)).symm
  rw [e]
  exact large_Ree_fixed_group_center_trivial a K hK

theorem burnsideF4h_invree_exists_iso (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Type} [Group H]
    (marking : (reeGroup K a ⧸ Subgroup.center (reeGroup K a)) ≃* H) :
    ∃ Φ : Gm K a ≃* H, ∀ (P : Subgroup (Gm K a)) (R : Subgroup (ModGL F4.tag K)),
      (∀ y : Gm K a, y ∈ P ↔ (y : ModGL F4.tag K) ∈ R) →
        (centralImage (reeGroup K a) R).map marking.toMonoidHom = P.map Φ.toMonoidHom := by
  obtain ⟨q, hq⟩ := burnsideF4h_invree_exists_quotEquiv (burnsideF4h_invree_center_trivial hK)
  let e0 : Gm K a ≃* ↥(reeGroup K a) :=
    MulEquiv.subgroupCongr (reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a))
  refine ⟨(e0.trans q).trans marking, fun P R hPR => ?_⟩
  ext z
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨e0.symm g, (hPR _).2 hg, ?_⟩
    show marking (q (e0 (e0.symm g))) = marking (QuotientGroup.mk' _ g)
    rw [MulEquiv.apply_symm_apply, hq]
    rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨_, ⟨e0 y, (hPR y).1 hy, rfl⟩, ?_⟩
    show marking (QuotientGroup.mk' _ (e0 y)) = marking (q (e0 y))
    rw [hq]
    rfl

end Marking

section Final

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4


theorem burnsideF4h_inv_F4tw (degree : ℕ) (E : Type) [Group E] (core : Subgroup E)
    (chart : ChF.NativeChart .F4tw 2 degree core) :
    ∃ long ∈ chart.longRoot, ∃ short ∈ chart.shortRoot,
      long ≠ 1 ∧ long * long = 1 ∧ short ≠ 1 ∧ short * short = 1 ∧
      (¬ ∃ conjugator ∈ core, conjugator * long * conjugator⁻¹ = short) ∧
      (∀ element : E, chart.RootInvolution false element ↔
        element ∈ core ∧ ∃ conjugator ∈ core,
          conjugator * element * conjugator⁻¹ = long) ∧
      (∀ element : E, chart.RootInvolution true element ↔
        element ∈ core ∧ ∃ conjugator ∈ core,
          conjugator * element * conjugator⁻¹ = short) ∧
      (∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element ∨ chart.RootInvolution true element) := by
  obtain ⟨K, fK, finK, charK, a, hKsc, marking, hL, hS⟩ := burnsideF4h_invree_chart_data chart
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hKsc
  haveI : CharP K F4.prime := charK
  obtain ⟨Φ, hΦ⟩ := burnsideF4h_invree_exists_iso hK marking
  have hD : burnsideF4h_invree_Datum (G := Gm K a)
      ((reeLongRoot K a).subgroupOf (F4.reeGamma K a))
      ((reeShortRoot K a).subgroupOf (F4.reeGamma K a)) (zg hK) (tg hK) := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact burnsideF4h_invree_datum_small hK
    · exact burnsideF4h_invree_datum_large ha hK
  refine burnsideF4h_invree_goal_of_datum chart (by decide) (burnsideF4h_invree_datum_map Φ hD)
    ?_ ?_
  · rw [hL]
    exact congrArg (Subgroup.map core.subtype) (hΦ _ _ (fun y => Subgroup.mem_subgroupOf))
  · rw [hS]
    exact congrArg (Subgroup.map core.subtype) (hΦ _ _ (fun y => Subgroup.mem_subgroupOf))

end Final

end PartBurnsideF4hInvRee

section PartBurnsideF4hTits

section LieLattice

theorem burnsideF4h_tits_isLieParabolics {X : Type} [Group X] {p : ℕ} {S H N : Subgroup X}
    (hp : IsPGroup p S) (hidx : ¬ p ∣ S.index)
    (hnorm : Subgroup.normalizer (S : Set X) ≤ S) (hSH : S ≤ H) (hSN : S ≤ N)
    (hHN : ¬ H ≤ N) (hNH : ¬ N ≤ H)
    (hlat : ∀ Y : Subgroup X, S ≤ Y → Y = S ∨ Y = H ∨ Y = N ∨ Y = ⊤) :
    ChF.IsLieParabolics p ⊤ S H N := by
  have hHtop : H ≠ ⊤ := fun h => hNH (h ▸ le_top)
  have hNtop : N ≠ ⊤ := fun h => hHN (h ▸ le_top)
  have hSH' : S ≠ H := fun h => hHN (h ▸ hSN)
  have hSN' : S ≠ N := fun h => hNH (h ▸ hSH)
  refine ⟨⟨S, ⟨le_top, hp, ?_⟩, ?_⟩, fun h => hHN (h ▸ le_rfl), ?_, fun Q => ⟨?_, ?_⟩⟩
  · rwa [Subgroup.relIndex_top_right]
  · rw [top_inf_eq]
    exact le_antisymm Subgroup.le_normalizer hnorm
  · rcases hlat (H ⊓ N) (le_inf hSH hSN) with h | h | h | h
    · exact h
    · exact absurd (inf_eq_left.1 h) hHN
    · exact absurd (inf_eq_right.1 h) hNH
    · exact absurd (inf_eq_top_iff.1 h).1 hHtop
  · rintro ⟨hSQ, -, hQtop, hmax⟩
    rcases hlat Q hSQ with rfl | rfl | rfl | rfl
    · exact absurd (hmax H (lt_of_le_of_ne hSH hSH') le_top) hHtop
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hQtop
  · rintro (rfl | rfl)
    · refine ⟨hSH, le_top, hHtop, fun R hR _ => ?_⟩
      rcases hlat R (hSH.trans hR.le) with rfl | rfl | rfl | rfl
      · exact absurd (lt_of_lt_of_le hR hSH) (lt_irrefl _)
      · exact absurd hR (lt_irrefl _)
      · exact absurd hR.le hHN
      · rfl
    · refine ⟨hSN, le_top, hNtop, fun R hR _ => ?_⟩
      rcases hlat R (hSN.trans hR.le) with rfl | rfl | rfl | rfl
      · exact absurd (lt_of_lt_of_le hR hSN) (lt_irrefl _)
      · exact absurd hR.le hNH
      · exact absurd hR (lt_irrefl _)
      · rfl

theorem burnsideF4h_tits_map_symm_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (A : Subgroup X) : (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A
  ext x
  simp

theorem burnsideF4h_tits_isLieParabolics_map {X Y : Type} [Group X] [Group Y] {p : ℕ}
    (e : X ≃* Y) {S H N : Subgroup X}
    (hp : IsPGroup p S) (hidx : ¬ p ∣ S.index)
    (hnorm : Subgroup.normalizer (S : Set X) ≤ S) (hSH : S ≤ H) (hSN : S ≤ N)
    (hHN : ¬ H ≤ N) (hNH : ¬ N ≤ H)
    (hlat : ∀ Y : Subgroup X, S ≤ Y → Y = S ∨ Y = H ∨ Y = N ∨ Y = ⊤) :
    ChF.IsLieParabolics p ⊤ (S.map e.toMonoidHom) (H.map e.toMonoidHom)
      (N.map e.toMonoidHom) := by
  refine burnsideF4h_tits_isLieParabolics (hp.map e.toMonoidHom) ?_ ?_
    (Subgroup.map_mono hSH) (Subgroup.map_mono hSN)
    (fun h => hHN ((Subgroup.map_le_map_iff_of_injective e.injective).1 h))
    (fun h => hNH ((Subgroup.map_le_map_iff_of_injective e.injective).1 h)) ?_
  · have h : (S.map e.toMonoidHom).index = S.index := Subgroup.index_map_equiv S e
    rw [h]
    exact hidx
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hnorm
  · intro Z hZ
    have hZ' : S ≤ Z.map e.symm.toMonoidHom := by
      rw [← burnsideF4h_tits_map_symm_map e S]
      exact Subgroup.map_mono hZ
    have hback : (Z.map e.symm.toMonoidHom).map e.toMonoidHom = Z :=
      burnsideF4h_tits_map_symm_map e.symm Z
    rcases hlat _ hZ' with h | h | h | h
    · exact Or.inl (by rw [← hback, h])
    · exact Or.inr (Or.inl (by rw [← hback, h]))
    · exact Or.inr (Or.inr (Or.inl (by rw [← hback, h])))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [← hback, h, Subgroup.map_top_of_surjective _ e.surjective]

end LieLattice

section ModelD

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits


theorem burnsideF4h_tits_card_SD : Nat.card titsSD = 2048 := by
  rw [card_subgroupOf_titsD titsS_le_titsD, titsQS_facts.2.2.2]

theorem burnsideF4h_tits_card_HD : Nat.card titsHD = 10240 := by
  rw [card_subgroupOf_titsD titsH_le_titsD, titsQH_facts.2.2.2]

theorem burnsideF4h_tits_card_ND : Nat.card titsND = 6144 := by
  rw [card_subgroupOf_titsD titsN_le_titsD, titsQN_facts.2.2.2]

theorem burnsideF4h_tits_SD_le_HD : titsSD ≤ titsHD := fun _ hx => titsS_le_titsH hx

theorem burnsideF4h_tits_SD_le_ND : titsSD ≤ titsND := fun _ hx => titsS_le_titsN hx

theorem burnsideF4h_tits_not_HD_le_ND : ¬ titsHD ≤ titsND := fun h => by
  have := Subgroup.card_dvd_of_le h
  rw [burnsideF4h_tits_card_HD, burnsideF4h_tits_card_ND] at this
  omega

theorem burnsideF4h_tits_not_ND_le_HD : ¬ titsND ≤ titsHD := fun h => by
  have := Subgroup.card_dvd_of_le h
  rw [burnsideF4h_tits_card_HD, burnsideF4h_tits_card_ND] at this
  omega

theorem burnsideF4h_tits_relIndex_of_card {X : Type} [Group X] {A B : Subgroup X} (h : A ≤ B)
    {a b r : ℕ} (ha : Nat.card A = a) (hb : Nat.card B = b) (ha0 : 0 < a) (hab : b = r * a) :
    A.relIndex B = r := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.2 h, ha, hb, hab] at h1
  exact Nat.eq_of_mul_eq_mul_right ha0 h1

theorem burnsideF4h_tits_relIndex_SD_HD : titsSD.relIndex titsHD = 5 :=
  burnsideF4h_tits_relIndex_of_card burnsideF4h_tits_SD_le_HD burnsideF4h_tits_card_SD
    burnsideF4h_tits_card_HD (by norm_num) (by norm_num)

theorem burnsideF4h_tits_relIndex_SD_ND : titsSD.relIndex titsND = 3 :=
  burnsideF4h_tits_relIndex_of_card burnsideF4h_tits_SD_le_ND burnsideF4h_tits_card_SD
    burnsideF4h_tits_card_ND (by norm_num) (by norm_num)

theorem burnsideF4h_tits_SD_isPGroup : IsPGroup 2 titsSD :=
  IsPGroup.of_card (n := 11) (by rw [burnsideF4h_tits_card_SD]; norm_num)

theorem burnsideF4h_tits_SD_index : ¬ 2 ∣ titsSD.index := by
  change ¬ 2 ∣ (titsS.subgroupOf titsD).index
  rw [titsS_index]
  decide

theorem burnsideF4h_tits_lie_map {X : Type} [Group X] (e : ↥titsD ≃* X) :
    ChF.IsLieParabolics 2 ⊤ (titsSD.map e.toMonoidHom) (titsHD.map e.toMonoidHom)
      (titsND.map e.toMonoidHom) :=
  burnsideF4h_tits_isLieParabolics_map e burnsideF4h_tits_SD_isPGroup burnsideF4h_tits_SD_index
    titsSD_normalizer_le burnsideF4h_tits_SD_le_HD burnsideF4h_tits_SD_le_ND
    burnsideF4h_tits_not_HD_le_ND burnsideF4h_tits_not_ND_le_HD titsD_overgroups

end ModelD

section ModelM

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits


theorem burnsideF4h_tits_Dm_perfect :
    ⁅titsD.subgroupOf twoF4M, titsD.subgroupOf twoF4M⁆ = titsD.subgroupOf twoF4M := by
  apply Subgroup.map_injective twoF4M.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le titsD_le_twoF4M]
  exact titsD_commutator

theorem burnsideF4h_tits_Dm_eq_commutator :
    titsD.subgroupOf twoF4M = ⁅(⊤ : Subgroup ↥twoF4M), (⊤ : Subgroup ↥twoF4M)⁆ := by
  apply le_antisymm
  · calc titsD.subgroupOf twoF4M = ⁅titsD.subgroupOf twoF4M, titsD.subgroupOf twoF4M⁆ :=
          burnsideF4h_tits_Dm_perfect.symm
      _ ≤ ⁅(⊤ : Subgroup ↥twoF4M), (⊤ : Subgroup ↥twoF4M)⁆ :=
          Subgroup.commutator_mono le_top le_top
  · haveI : (titsD.subgroupOf twoF4M).Normal := twoF4D_normal
    have hc2 : Nat.card (↥twoF4M ⧸ titsD.subgroupOf twoF4M) = 2 := by
      rw [← Subgroup.index_eq_card, index_titsD_twoF4M]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI hcyc : IsCyclic (↥twoF4M ⧸ titsD.subgroupOf twoF4M) := isCyclic_of_prime_card hc2
    have hcomm : commutator ↥twoF4M ≤ titsD.subgroupOf twoF4M := by
      rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
      exact ⟨⟨fun a b => hcyc.commGroup.mul_comm a b⟩⟩
    exact hcomm

theorem burnsideF4h_tits_commutator_map {G : Type} [Group G] (Γ : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M) :
    ((⁅Γ, Γ⁆).subgroupOf Γ).map Φ.toMonoidHom = titsD.subgroupOf twoF4M := by
  have h1 : (⁅(⊤ : Subgroup ↥Γ), (⊤ : Subgroup ↥Γ)⁆).map Γ.subtype = ⁅Γ, Γ⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCg : (⁅Γ, Γ⁆).subgroupOf Γ = ⁅(⊤ : Subgroup ↥Γ), (⊤ : Subgroup ↥Γ)⁆ := by
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  rw [hCg, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ Φ.surjective,
    ← burnsideF4h_tits_Dm_eq_commutator]

theorem burnsideF4h_tits_commutator_equiv {G : Type} [Group G] (Γ : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M) :
    ∃ Θ : ↥⁅Γ, Γ⁆ ≃* ↥titsD, ∀ x : ↥⁅Γ, Γ⁆,
      ((Θ x : ↥titsD) : Equiv.Perm (Fin 1755)) =
        ((Φ ⟨x, Subgroup.commutator_le_self Γ x.2⟩ : ↥twoF4M) : Equiv.Perm (Fin 1755)) :=
  ⟨(Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self Γ)).symm.trans
    ((Φ.subgroupMap _).trans ((MulEquiv.subgroupCongr (burnsideF4h_tits_commutator_map Γ Φ)).trans
      (Subgroup.subgroupOfEquivOfLe titsD_le_twoF4M))), fun _ => rfl⟩


theorem burnsideF4h_tits_center_titsD : Subgroup.center ↥titsD = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h := twoF4_centD (⟨x.1, titsD_le_twoF4M x.2⟩ : ↥twoF4M) (fun d hd => by
    have h1 := Subgroup.mem_center_iff.1 hx ⟨d.1, hd⟩
    apply Subtype.ext
    exact (congrArg Subtype.val h1).symm)
  have h2 := congrArg Subtype.val h
  exact Subtype.ext h2

theorem burnsideF4h_tits_center_eq_bot {X : Type} [Group X] (Φ : X ≃* ↥twoF4M) :
    Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : Φ x = 1 := twoF4_centD (Φ x) (fun d _ => by
    obtain ⟨y, rfl⟩ := Φ.surjective d
    calc Φ x * Φ y = Φ (x * y) := (map_mul Φ x y).symm
      _ = Φ (y * x) := by rw [← Subgroup.mem_center_iff.1 hx y]
      _ = Φ y * Φ x := map_mul Φ y x)
  exact Φ.injective (h1.trans (map_one Φ).symm)

theorem burnsideF4h_tits_center_eq_bot_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : e x ∈ Subgroup.center Y := Subgroup.mem_center_iff.2 fun y => by
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y']
  rw [h, Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

end ModelM

section IndexTwo

open CFSG.Quasithin

variable {M : Type*} [Group M] (d : IndexTwoLatticeData M)

theorem burnsideF4h_tits_extSub_inf_D {H : Subgroup M} (hHD : H ≤ d.D)
    {hq : d.q ∈ Subgroup.normalizer (H : Set M)} {hq2 : d.q * d.q ∈ H} :
    extSub H d.q hq hq2 ⊓ d.D = H := by
  ext x
  constructor
  · rintro ⟨hx, hxD⟩
    exact d.mem_of_mem_ext_of_mem_D hHD hx hxD
  · intro hx
    exact ⟨le_extSub hx, hHD hx⟩

theorem burnsideF4h_tits_relIndex_extSub {H : Subgroup M} (hHD : H ≤ d.D)
    {hq : d.q ∈ Subgroup.normalizer (H : Set M)} {hq2 : d.q * d.q ∈ H} :
    H.relIndex (extSub H d.q hq hq2) = 2 :=
  relIndex_extSub fun h => d.q_not_mem (hHD h)

theorem burnsideF4h_tits_D_relIndex_extSub {H : Subgroup M} (hHD : H ≤ d.D)
    {hq : d.q ∈ Subgroup.normalizer (H : Set M)} {hq2 : d.q * d.q ∈ H} :
    d.D.relIndex (extSub H d.q hq hq2) = 2 := by
  rw [← Subgroup.inf_relIndex_right, inf_comm, burnsideF4h_tits_extSub_inf_D d hHD]
  exact burnsideF4h_tits_relIndex_extSub d hHD

end IndexTwo

section Quotient

open CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots

variable {G : Type} [Group G]

theorem burnsideF4h_tits_exists_derivedEquiv (Γ C : Subgroup G) (hD : ⁅Γ, Γ⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) :
    ∃ e : DerivedCentralQuotient Γ ≃* ↥C,
      ∀ x : ↥⁅Γ, Γ⁆, ((e (QuotientGroup.mk x) : ↥C) : G) = (x : G) := by
  subst hD
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot, fun x => rfl⟩

@[expose] noncomputable def burnsideF4h_tits_incl (Γ : Subgroup G)
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆) :
    DerivedCentralQuotient Γ →* (↥Γ ⧸ Subgroup.center ↥Γ) :=
  (QuotientGroup.mk' (Subgroup.center ↥Γ)).comp
    ((Subgroup.inclusion (Subgroup.commutator_le_self Γ)).comp eC.toMonoidHom)

theorem burnsideF4h_tits_incl_mk (Γ : Subgroup G) (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆)
    (heC : ∀ x : ↥⁅Γ, Γ⁆, ((eC (QuotientGroup.mk x) : ↥⁅Γ, Γ⁆) : G) = (x : G))
    (x : ↥⁅Γ, Γ⁆) :
    burnsideF4h_tits_incl Γ eC (QuotientGroup.mk x) =
      (QuotientGroup.mk (⟨(x : G), Subgroup.commutator_le_self Γ x.2⟩ : ↥Γ) :
        ↥Γ ⧸ Subgroup.center ↥Γ) := by
  show QuotientGroup.mk (Subgroup.inclusion (Subgroup.commutator_le_self Γ)
    (eC (QuotientGroup.mk x))) = _
  congr 1
  exact Subtype.ext (heC x)

theorem burnsideF4h_tits_mk_injective (Γ : Subgroup G) (hZ : Subgroup.center ↥Γ = ⊥) :
    Function.Injective (QuotientGroup.mk' (Subgroup.center ↥Γ)) :=
  (MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk', hZ])

theorem burnsideF4h_tits_incl_injective (Γ : Subgroup G) (hZ : Subgroup.center ↥Γ = ⊥)
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆) :
    Function.Injective (burnsideF4h_tits_incl Γ eC) :=
  (burnsideF4h_tits_mk_injective Γ hZ).comp
    ((Subgroup.inclusion_injective (Subgroup.commutator_le_self Γ)).comp eC.injective)

theorem burnsideF4h_tits_map_incl (Γ : Subgroup G) (hZ : Subgroup.center ↥Γ = ⊥)
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆)
    (heC : ∀ x : ↥⁅Γ, Γ⁆, ((eC (QuotientGroup.mk x) : ↥⁅Γ, Γ⁆) : G) = (x : G))
    (X : Subgroup G) :
    (derivedImage Γ X).map (burnsideF4h_tits_incl Γ eC) =
      (burnsideF4h_tits_incl Γ eC).range ⊓ centralImage Γ X := by
  ext y
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨_, rfl⟩, ⟨⟨(x : G), Subgroup.commutator_le_self Γ x.2⟩, hx, ?_⟩⟩
    exact (burnsideF4h_tits_incl_mk Γ eC heC x).symm
  · rintro ⟨⟨q, rfl⟩, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg, hgq⟩ := hy
    rw [burnsideF4h_tits_incl_mk Γ eC heC x] at hgq
    have hgx : g = ⟨(x : G), Subgroup.commutator_le_self Γ x.2⟩ :=
      burnsideF4h_tits_mk_injective Γ hZ hgq
    have hxX : (x : G) ∈ X := by
      have : (g : G) ∈ X := hg
      rw [hgx] at this
      exact this
    exact ⟨QuotientGroup.mk x, ⟨x, hxX, rfl⟩, rfl⟩

theorem burnsideF4h_tits_range_incl (Γ : Subgroup G) (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆) :
    (burnsideF4h_tits_incl Γ eC).range =
      ((⁅Γ, Γ⁆).subgroupOf Γ).map (QuotientGroup.mk' (Subgroup.center ↥Γ)) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨Subgroup.inclusion (Subgroup.commutator_le_self Γ) (eC q), (eC q).2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨eC.symm ⟨(g : G), hg⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion (Subgroup.commutator_le_self Γ)
      (eC (eC.symm ⟨(g : G), hg⟩))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl

theorem burnsideF4h_tits_centralImage_eq (Γ X : Subgroup G) :
    centralImage Γ X = (X.subgroupOf Γ).map (QuotientGroup.mk' (Subgroup.center ↥Γ)) := rfl

end Quotient

section DerivedTransport

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots


theorem burnsideF4h_tits_map_derived {G : Type} [Group G] (Γ X : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M) (Θ : ↥⁅Γ, Γ⁆ ≃* ↥titsD)
    (hΘ : ∀ x : ↥⁅Γ, Γ⁆, ((Θ x : ↥titsD) : Equiv.Perm (Fin 1755)) =
        ((Φ ⟨x, Subgroup.commutator_le_self Γ x.2⟩ : ↥twoF4M) : Equiv.Perm (Fin 1755)))
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆)
    (heC : ∀ x : ↥⁅Γ, Γ⁆, ((eC (QuotientGroup.mk x) : ↥⁅Γ, Γ⁆) : G) = (x : G))
    {Y' : Subgroup ↥twoF4M} {Y : Subgroup (Equiv.Perm (Fin 1755))}
    (hX : (X.subgroupOf Γ).map Φ.toMonoidHom = Y')
    (hY : ∀ m : ↥twoF4M, (m : Equiv.Perm (Fin 1755)) ∈ titsD →
      (m ∈ Y' ↔ (m : Equiv.Perm (Fin 1755)) ∈ Y)) :
    (derivedImage Γ X).map (eC.trans Θ).toMonoidHom = Y.subgroupOf titsD := by
  ext d
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  set x := Θ.symm d with hx
  have hxd : Θ x = d := by rw [hx, MulEquiv.apply_symm_apply]
  have hsymm : (eC.trans Θ).symm d = QuotientGroup.mk x := by
    rw [MulEquiv.symm_trans_apply, ← hx]
    apply eC.injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext (heC x).symm
  rw [hsymm]
  have hmk : QuotientGroup.mk x ∈ derivedImage Γ X ↔ (x : G) ∈ X := by
    constructor
    · rintro ⟨x', hx', hx'x⟩
      have h1 : eC (QuotientGroup.mk x') = eC (QuotientGroup.mk x) := congrArg eC hx'x
      have h2 : (x' : G) = (x : G) := by
        have := congrArg Subtype.val h1
        rwa [heC, heC] at this
      have : (x' : G) ∈ X := hx'
      rwa [h2] at this
    · intro h
      exact ⟨x, h, rfl⟩
  rw [hmk]
  have hΦ : (x : G) ∈ X ↔ Φ ⟨x, Subgroup.commutator_le_self Γ x.2⟩ ∈ Y' := by
    rw [← hX, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact Iff.rfl
  rw [hΦ, hY _ (by rw [← hΘ]; exact (Θ x).2), ← hΘ, hxd]

end DerivedTransport

section Assembly

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots

set_option linter.unusedSectionVars false


theorem burnsideF4h_tits_mem_lattice_S (m : ↥twoF4M) (hm : (m : Equiv.Perm (Fin 1755)) ∈ titsD) :
    m ∈ twoF4Lattice.S ↔ (m : Equiv.Perm (Fin 1755)) ∈ titsS := by
  have h : twoF4Data.Sx ⊓ twoF4Data.D = twoF4Data.S := twoF4Data.toLattice_inf_D_S
  constructor
  · intro hS
    have h1 : m ∈ twoF4Data.Sx ⊓ twoF4Data.D := ⟨hS, hm⟩
    rw [h] at h1
    exact h1
  · intro hS
    exact twoF4Data.S_le_Sx hS

theorem burnsideF4h_tits_mem_lattice_P₁ (m : ↥twoF4M) (hm : (m : Equiv.Perm (Fin 1755)) ∈ titsD) :
    m ∈ twoF4Lattice.P₁ ↔ (m : Equiv.Perm (Fin 1755)) ∈ titsH := by
  have h : twoF4Data.P₁x ⊓ twoF4Data.D = twoF4Data.P₁ :=
    burnsideF4h_tits_extSub_inf_D twoF4Data twoF4Data.P₁_le_D
  constructor
  · intro hS
    have h1 : m ∈ twoF4Data.P₁x ⊓ twoF4Data.D := ⟨hS, hm⟩
    rw [h] at h1
    exact h1
  · intro hS
    show m ∈ twoF4Data.P₁x
    exact mem_extSub.2 (Or.inl hS)

theorem burnsideF4h_tits_mem_lattice_P₂ (m : ↥twoF4M) (hm : (m : Equiv.Perm (Fin 1755)) ∈ titsD) :
    m ∈ twoF4Lattice.P₂ ↔ (m : Equiv.Perm (Fin 1755)) ∈ titsN := by
  have h : twoF4Data.P₂x ⊓ twoF4Data.D = twoF4Data.P₂ :=
    burnsideF4h_tits_extSub_inf_D twoF4Data twoF4Data.P₂_le_D
  constructor
  · intro hS
    have h1 : m ∈ twoF4Data.P₂x ⊓ twoF4Data.D := ⟨hS, hm⟩
    rw [h] at h1
    exact h1
  · intro hS
    show m ∈ twoF4Data.P₂x
    exact mem_extSub.2 (Or.inl hS)

theorem burnsideF4h_tits_relIndex_D_S : (titsD.subgroupOf twoF4M).relIndex twoF4Lattice.S = 2 :=
  burnsideF4h_tits_D_relIndex_extSub twoF4Data twoF4Data.S_le_D (hq := twoF4Data.q_norm_S)
    (hq2 := twoF4Data.q_mul_self_mem_S)

theorem burnsideF4h_tits_relIndex_D_P₁ :
    (titsD.subgroupOf twoF4M).relIndex twoF4Lattice.P₁ = 2 :=
  burnsideF4h_tits_D_relIndex_extSub twoF4Data twoF4Data.P₁_le_D (hq := twoF4Data.q_norm_P₁)
    (hq2 := twoF4Data.q_mul_self_mem_P₁)

theorem burnsideF4h_tits_relIndex_D_P₂ :
    (titsD.subgroupOf twoF4M).relIndex twoF4Lattice.P₂ = 2 :=
  burnsideF4h_tits_D_relIndex_extSub twoF4Data twoF4Data.P₂_le_D (hq := twoF4Data.q_norm_P₂)
    (hq2 := twoF4Data.q_mul_self_mem_P₂)

theorem burnsideF4h_tits_relIndex_range {G : Type} [Group G] (Γ X : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M) (hZ : Subgroup.center ↥Γ = ⊥)
    (eC : DerivedCentralQuotient Γ ≃* ↥⁅Γ, Γ⁆) :
    (burnsideF4h_tits_incl Γ eC).range.relIndex (centralImage Γ X) =
      (titsD.subgroupOf twoF4M).relIndex ((X.subgroupOf Γ).map Φ.toMonoidHom) := by
  rw [burnsideF4h_tits_range_incl, burnsideF4h_tits_centralImage_eq,
    Subgroup.relIndex_map_map_of_injective _ _ (burnsideF4h_tits_mk_injective Γ hZ),
    ← burnsideF4h_tits_commutator_map Γ Φ,
    Subgroup.relIndex_map_map_of_injective _ _ Φ.injective]

theorem burnsideF4h_tits_assembly {G : Type} [Group G] (Γ B P₁ P₂ L Sh : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M)
    (hB : (B.subgroupOf Γ).map Φ.toMonoidHom = twoF4Lattice.S)
    (hP₁ : (P₁.subgroupOf Γ).map Φ.toMonoidHom = twoF4Lattice.P₁)
    (hP₂ : (P₂.subgroupOf Γ).map Φ.toMonoidHom = twoF4Lattice.P₂) :
    ChF.IsLieParabolics 2 (⊤ : Subgroup (DerivedCentralQuotient Γ))
      (derivedImage Γ B) (derivedImage Γ P₁) (derivedImage Γ P₂) ∧
    (derivedImage Γ B).relIndex (derivedImage Γ P₁) = 5 ∧
    (derivedImage Γ B).relIndex (derivedImage Γ P₂) = 3 ∧
    ∃ inclusion : DerivedCentralQuotient Γ →* (↥Γ ⧸ Subgroup.center ↥Γ),
      Function.Injective inclusion ∧ inclusion.range.index = 2 ∧
      (∀ d : ↥⁅Γ, Γ⁆, ∀ p : ↥Γ, (p : G) = d.val →
          inclusion (QuotientGroup.mk d) = QuotientGroup.mk p) ∧
      (derivedImage Γ B).map inclusion = inclusion.range ⊓ centralImage Γ B ∧
      (derivedImage Γ P₁).map inclusion = inclusion.range ⊓ centralImage Γ P₁ ∧
      (derivedImage Γ P₂).map inclusion = inclusion.range ⊓ centralImage Γ P₂ ∧
      (derivedImage Γ L).map inclusion = inclusion.range ⊓ centralImage Γ L ∧
      (derivedImage Γ Sh).map inclusion = inclusion.range ⊓ centralImage Γ Sh ∧
      ((derivedImage Γ B).map inclusion).relIndex (centralImage Γ B) = 2 ∧
      ((derivedImage Γ P₁).map inclusion).relIndex (centralImage Γ P₁) = 2 ∧
      ((derivedImage Γ P₂).map inclusion).relIndex (centralImage Γ P₂) = 2 := by
  obtain ⟨Θ, hΘ⟩ := burnsideF4h_tits_commutator_equiv Γ Φ
  have hZ' : Subgroup.center ↥⁅Γ, Γ⁆ = ⊥ :=
    burnsideF4h_tits_center_eq_bot_of_equiv Θ burnsideF4h_tits_center_titsD
  obtain ⟨eC, heC⟩ := burnsideF4h_tits_exists_derivedEquiv Γ ⁅Γ, Γ⁆ rfl hZ'
  have hZ : Subgroup.center ↥Γ = ⊥ := burnsideF4h_tits_center_eq_bot Φ
  have hBD : (derivedImage Γ B).map (eC.trans Θ).toMonoidHom = titsSD :=
    burnsideF4h_tits_map_derived Γ B Φ Θ hΘ eC heC hB burnsideF4h_tits_mem_lattice_S
  have hP₁D : (derivedImage Γ P₁).map (eC.trans Θ).toMonoidHom = titsHD :=
    burnsideF4h_tits_map_derived Γ P₁ Φ Θ hΘ eC heC hP₁ burnsideF4h_tits_mem_lattice_P₁
  have hP₂D : (derivedImage Γ P₂).map (eC.trans Θ).toMonoidHom = titsND :=
    burnsideF4h_tits_map_derived Γ P₂ Φ Θ hΘ eC heC hP₂ burnsideF4h_tits_mem_lattice_P₂
  have hback := burnsideF4h_tits_map_symm_map (eC.trans Θ)
  have hinj : Function.Injective (eC.trans Θ).toMonoidHom := (eC.trans Θ).injective
  refine ⟨?_, ?_, ?_, burnsideF4h_tits_incl Γ eC, burnsideF4h_tits_incl_injective Γ hZ eC, ?_,
    ?_, burnsideF4h_tits_map_incl Γ hZ eC heC B, burnsideF4h_tits_map_incl Γ hZ eC heC P₁,
    burnsideF4h_tits_map_incl Γ hZ eC heC P₂, burnsideF4h_tits_map_incl Γ hZ eC heC L,
    burnsideF4h_tits_map_incl Γ hZ eC heC Sh, ?_, ?_, ?_⟩
  · have h := burnsideF4h_tits_lie_map (eC.trans Θ).symm
    rwa [← hBD, ← hP₁D, ← hP₂D, hback, hback, hback] at h
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, hBD, hP₁D]
    exact burnsideF4h_tits_relIndex_SD_HD
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, hBD, hP₂D]
    exact burnsideF4h_tits_relIndex_SD_ND
  · rw [burnsideF4h_tits_range_incl, Subgroup.index_map_of_bijective
        ⟨burnsideF4h_tits_mk_injective Γ hZ, QuotientGroup.mk'_surjective _⟩,
      ← Subgroup.index_map_of_bijective (f := Φ.toMonoidHom) Φ.bijective,
      burnsideF4h_tits_commutator_map Γ Φ, index_titsD_twoF4M]
  · intro d p hp
    rw [burnsideF4h_tits_incl_mk Γ eC heC d]
    congr 1
    exact Subtype.ext hp.symm
  · rw [burnsideF4h_tits_map_incl Γ hZ eC heC, Subgroup.inf_relIndex_right,
      burnsideF4h_tits_relIndex_range Γ B Φ hZ eC, hB]
    exact burnsideF4h_tits_relIndex_D_S
  · rw [burnsideF4h_tits_map_incl Γ hZ eC heC, Subgroup.inf_relIndex_right,
      burnsideF4h_tits_relIndex_range Γ P₁ Φ hZ eC, hP₁]
    exact burnsideF4h_tits_relIndex_D_P₁
  · rw [burnsideF4h_tits_map_incl Γ hZ eC heC, Subgroup.inf_relIndex_right,
      burnsideF4h_tits_relIndex_range Γ P₂ Φ hZ eC, hP₂]
    exact burnsideF4h_tits_relIndex_D_P₂

end Assembly


local instance burnsideF4h_tits_neZero_rank : NeZero CFSG.Blueprint.Chevalley.Tag.F4.rank :=
  ⟨by decide⟩

section WeylBasic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

variable {tag : Tag} {K : Type}
  [Field K]

theorem burnsideF4h_tits_weylWordOperator_eq (word : List (Fin tag.rank)) :
    weylWordOperator tag K word =
      ((((word.map fun i => weylElt tag K i 1).reverse).prod : (Module.End K (RootModule tag K))ˣ) :
        Module.End K (RootModule tag K)) := by
  unfold weylWordOperator
  have h := map_list_prod (Units.coeHom (Module.End K (RootModule tag K)))
    ((word.map fun i => weylElt tag K i 1).reverse)
  simp only [Units.coeHom_apply, List.map_reverse, List.map_map] at h
  rw [h]
  rfl

theorem burnsideF4h_tits_rootSubgroup_le_absoluteRoot {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    rootSubgroup tag K α ≤ absoluteRoot tag K α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine Subgroup.subset_closure ⟨(pinnedData tag α).2.2 • c, (pinnedData tag α).1,
    (pinnedData tag α).2.1.map tag.idx, pinnedWeyl tag K α, ?_, ?_, ?_⟩
  · rw [List.foldl_map]
    exact foldl_reflect_pinnedData hα
  · rw [burnsideF4h_tits_weylWordOperator_eq]
    congr 1
    unfold pinnedWeyl
    rw [List.map_map]
    rfl
  · rfl

theorem burnsideF4h_tits_absoluteTorus_eq : absoluteTorus tag K = torusGroup tag K := by
  unfold absoluteTorus torusGroup
  congr 1
  ext e
  constructor
  · rintro ⟨i, p, h⟩
    exact ⟨(i, p), (Units.ext h).symm⟩
  · rintro ⟨⟨i, p⟩, rfl⟩
    exact ⟨i, p, rfl⟩

theorem burnsideF4h_tits_relativeWeyl_eq (word : List (Fin tag.rank)) :
    relativeWeyl tag K word =
      Subgroup.zpowers ((word.map fun i => weylElt tag K i 1).reverse.prod) := by
  unfold relativeWeyl
  rw [Subgroup.zpowers_eq_closure]
  congr 1
  ext e
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [burnsideF4h_tits_weylWordOperator_eq]
  exact ⟨fun h => Units.ext h, fun h => h ▸ rfl⟩

theorem burnsideF4h_tits_comm_zero_three :
    weylElt Tag.F4 K 3 1 * weylElt Tag.F4 K 0 1 = weylElt Tag.F4 K 0 1 * weylElt Tag.F4 K 3 1 := by
  have h := prod_alternatingWord_weylElt Tag.F4 K (0 : Fin Tag.F4.rank) 3
  have e : Tag.F4.cartan 0 3 * Tag.F4.cartan 3 0 = 0 := by decide
  rw [e] at h
  simp [TauCeti.coxeterOrder_zero, CoxeterSystem.alternatingWord] at h
  exact h.symm

theorem burnsideF4h_tits_braid_one_two :
    (weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1) =
      weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 := by
  have h := prod_alternatingWord_weylElt Tag.F4 K (1 : Fin Tag.F4.rank) 2
  have e : Tag.F4.cartan 1 2 * Tag.F4.cartan 2 1 = 2 := by decide
  rw [e] at h
  simp [TauCeti.coxeterOrder_two, CoxeterSystem.alternatingWord] at h
  simpa only [mul_assoc] using h.symm

end WeylBasic

section WeylTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley

variable
    {tag : Tag} {K : Type} [Field K]

theorem burnsideF4h_tits_absoluteRoot_le {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    absoluteRoot tag K α ≤ rootSubgroup tag K α := by
  refine (Subgroup.closure_le _).2 ?_
  rintro e ⟨c, seed, word, actor, hfold, hact, he⟩
  have hactor : actor = (word.map fun i => weylElt tag K i 1).reverse.prod :=
    Units.ext (hact.trans (burnsideF4h_tits_weylWordOperator_eq word))
  have he' : e = actor * xUnit tag K seed c * actor⁻¹ := Units.ext he
  have h1 : xUnit tag K seed c ∈ rootSubgroup tag K (Pi.single seed 1) := by
    rw [← pinnedX_single]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  have h2 := map_conj_prod_weylElt_rootSubgroup K word.reverse (isRoot_single tag seed)
  rw [wordProd_reverse_smul, hfold] at h2
  have h3 : e ∈ (rootSubgroup tag K (Pi.single seed 1)).map
      (MulAut.conj (word.reverse.map fun i => weylElt tag K i 1).prod).toMonoidHom := by
    refine ⟨xUnit tag K seed c, h1, ?_⟩
    rw [he', hactor, List.map_reverse]
    rfl
  rw [h2] at h3
  exact h3

theorem burnsideF4h_tits_absoluteRoot_eq {α : Fin tag.rank → ℤ} (hα : IsRoot tag α) :
    absoluteRoot tag K α = rootSubgroup tag K α :=
  le_antisymm (burnsideF4h_tits_absoluteRoot_le hα) (burnsideF4h_tits_rootSubgroup_le_absoluteRoot hα)

theorem burnsideF4h_tits_absoluteBorel_eq : absoluteBorel tag K = borelGroup tag K := by
  unfold absoluteBorel borelGroup absolutePositive posUnipotent rootSpan
  rw [sup_comm, burnsideF4h_tits_absoluteTorus_eq]
  congr 1
  exact iSup_congr fun α => iSup_congr fun hα => burnsideF4h_tits_absoluteRoot_eq hα.1

end WeylTransport

section F4Words

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution

variable
  {K : Type} [Field K]

theorem burnsideF4h_tits_weylOne_eq :
    weylOne K = weylElt Tag.F4 K 0 1 * weylElt Tag.F4 K 3 1 := by
  have hred : (coxeterSystem Tag.F4).IsReduced ([0, 3] : List (Fin Tag.F4.rank)) :=
    CFSG.LieType.Simplicity.isReduced_reeOrbitWord ReeTag.F4 (0 : Fin Tag.F4.rank)
  have h := canonicalRep_wordProd (R := K) (cs := coxeterSystem Tag.F4) hred
  have e : weylOne K =
      canonicalRep (coxeterSystem Tag.F4) K ((coxeterSystem Tag.F4).wordProd [0, 3]) := rfl
  rw [e, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem burnsideF4h_tits_weylTwo_eq :
    weylTwo K = weylElt Tag.F4 K 1 1 * weylElt Tag.F4 K 2 1 * weylElt Tag.F4 K 1 1 *
      weylElt Tag.F4 K 2 1 := by
  have hred : (coxeterSystem Tag.F4).IsReduced ([1, 2, 1, 2] : List (Fin Tag.F4.rank)) :=
    CFSG.LieType.Simplicity.isReduced_reeOrbitWord ReeTag.F4 (1 : Fin Tag.F4.rank)
  have h := canonicalRep_wordProd (R := K) (cs := coxeterSystem Tag.F4) hred
  have e : weylTwo K =
      canonicalRep (coxeterSystem Tag.F4) K ((coxeterSystem Tag.F4).wordProd [1, 2, 1, 2]) := rfl
  rw [e, h]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl

theorem burnsideF4h_tits_wordUnit_zero :
    (([0, 3] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 K i 1).reverse.prod =
      weylOne K := by
  rw [burnsideF4h_tits_weylOne_eq]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one]
  exact burnsideF4h_tits_comm_zero_three

theorem burnsideF4h_tits_wordUnit_one :
    (([1, 2, 1, 2] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 K i 1).reverse.prod =
      weylTwo K := by
  rw [burnsideF4h_tits_weylTwo_eq]
  simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have h := burnsideF4h_tits_braid_one_two (K := K)
  simp only [mul_assoc] at h
  exact h

end F4Words

section BN

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN

theorem burnsideF4h_tits_P_eq_sup {X : Type} [Group X] {n : ℕ} (D : RankTwoSystem X n) (i : Bool)
    {m : X} (hm : m ∈ D.N)
    (hw : ((⟨m, hm⟩ : D.N) : WeylGroup D.B D.N) = gen D.w₁ D.w₂ i) :
    P D i = D.B ⊔ Subgroup.zpowers m := by
  apply le_antisymm
  · intro x hx
    rcases (mem_P_iff D).1 hx with hB | hd
    · exact Subgroup.mem_sup_left hB
    · obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hw).1 hd
      exact mul_mem (mul_mem (Subgroup.mem_sup_left hb)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers m))) (Subgroup.mem_sup_left hb')
  · refine sup_le (B_le_P D i) ?_
    rw [Subgroup.zpowers_le]
    exact (mem_P_iff D).2 (Or.inr ((mem_dc_of_lift hw).2
      ⟨1, D.B.one_mem, 1, D.B.one_mem, by simp⟩))

end BN

section Main

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_tits_reeGroup_eq : reeGroup K a = F4.reeGamma K a :=
  (reeGamma_eq_reeFixedGroup (t := F4) (K := K) (a := a)).symm

theorem burnsideF4h_tits_reeBorel_eq : reeBorel K a = F4.reeFixedBorel K a := by
  unfold ChF.ExceptionalRoots.reeBorel
  rw [burnsideF4h_tits_absoluteBorel_eq, burnsideF4h_tits_reeGroup_eq]
  exact inf_comm _ _

theorem burnsideF4h_tits_reeParabolic_one :
    ChF.ExceptionalRoots.reeParabolic K a 1 =
      F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylTwo K) := by
  unfold ChF.ExceptionalRoots.reeParabolic
  rw [burnsideF4h_tits_reeBorel_eq]
  have h1 : (if (1 : Fin 2) = 0 then [0, 3] else [1, 2, 1, 2] : List (Fin Tag.F4.rank)) =
      [1, 2, 1, 2] := by decide
  rw [h1, burnsideF4h_tits_relativeWeyl_eq, burnsideF4h_tits_wordUnit_one]
  congr 1
  refine inf_eq_right.2 ?_
  refine Subgroup.zpowers_le.2 ?_
  have h : weylTwo K ∈ F4.reeGamma K a := (octR1 K a).2
  rw [burnsideF4h_tits_reeGroup_eq]
  exact h

theorem burnsideF4h_tits_reeParabolic_zero :
    ChF.ExceptionalRoots.reeParabolic K a 0 =
      F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylOne K) := by
  unfold ChF.ExceptionalRoots.reeParabolic
  rw [burnsideF4h_tits_reeBorel_eq]
  have h1 : (if (0 : Fin 2) = 0 then [0, 3] else [1, 2, 1, 2] : List (Fin Tag.F4.rank)) =
      [0, 3] := by decide
  rw [h1, burnsideF4h_tits_relativeWeyl_eq, burnsideF4h_tits_wordUnit_zero]
  congr 1
  refine inf_eq_right.2 ?_
  refine Subgroup.zpowers_le.2 ?_
  have h : weylOne K ∈ F4.reeGamma K a := (octR2 K a).2
  rw [burnsideF4h_tits_reeGroup_eq]
  exact h

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN in
theorem burnsideF4h_tits_mem_sup_iff (y : Gm K a) (r : Gm K a) :
    y ∈ (octH K a ⊔ Ug K a) ⊔ Subgroup.zpowers r ↔
      (y : ModGL F4.tag K) ∈ F4.reeFixedBorel K a ⊔ Subgroup.zpowers (r : ModGL F4.tag K) := by
  have hB : (octH K a ⊔ Ug K a).map (F4.reeGamma K a).subtype = F4.reeFixedBorel K a := by
    rw [sup_octH_Ug]
    exact Subgroup.map_subgroupOf_eq_of_le reeFixedBorel_le_reeGamma
  rw [← Subgroup.mem_map_iff_mem (F4.reeGamma K a).subtype_injective, Subgroup.map_sup, hB,
    MonoidHom.map_zpowers]
  rfl

end Main

section BNZero

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem burnsideF4h_tits_units_subsingleton (hK : Nat.card K = 2) : Subsingleton Kˣ := by
  have h2 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.1 h2).1

theorem burnsideF4h_tits_torusGroup_eq_bot (hK : Nat.card K = 2) {τ : Tag} :
    torusGroup τ K = ⊥ := by
  haveI := burnsideF4h_tits_units_subsingleton hK
  rw [eq_bot_iff, torusGroup, Subgroup.closure_le]
  rintro _ ⟨⟨i, u⟩, rfl⟩
  rw [Subsingleton.elim u 1]
  simp [torusElt_one]

theorem burnsideF4h_tits_octH_eq_bot (hK : Nat.card K = 2) : octH K 0 = ⊥ := by
  unfold octH ReeTag.reeFixedTorus
  rw [burnsideF4h_tits_torusGroup_eq_bot hK, bot_inf_eq, Subgroup.bot_subgroupOf]

@[expose] noncomputable def burnsideF4h_tits_system (hK : Nat.card K = 2) :
    RankTwoSystem (Gm K 0) 8 :=
  haveI hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  haveI := (octRGD2 hK').cartan_normal
  ((octRGD2 hK').toPre (octGen (octRGD2 hK'))).toSystem
    ((octRGD2 hK').faithful (octGen (octRGD2 hK')) (fun g hg _ => by
      rw [burnsideF4h_tits_octH_eq_bot hK, Subgroup.mem_bot] at hg
      exact hg))

end BNZero

section YamNoSimple

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Sec53F.Yam
open scoped Pointwise

theorem burnsideF4h_tits_eq_one_of_conj_mem {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)
    {g : X} (h : ∀ x : X, x * g * x⁻¹ ∈ D.B) : g = 1 := by
  apply D.faithful
  have key : ∀ (Pp : Subgroup X), D.B ≤ Pp → ∀ x : X,
      (Pp : Set X) * ({x} : Set X) * ({g} : Set X) = (Pp : Set X) * ({x} : Set X) := by
    intro Pp hPp x
    ext y
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy
      obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.1 ha
      rw [Set.mem_singleton_iff] at hb hc
      rw [hb, hc]
      exact Set.mem_mul.2 ⟨p * (x * g * x⁻¹), Pp.mul_mem hp (hPp (h x)), x, rfl, by group⟩
    · intro hy
      obtain ⟨p, hp, c, hc, rfl⟩ := Set.mem_mul.1 hy
      rw [Set.mem_singleton_iff] at hc
      rw [hc]
      refine Set.mem_mul.2 ⟨p * (x * g * x⁻¹)⁻¹ * x, Set.mem_mul.2
        ⟨p * (x * g * x⁻¹)⁻¹, Pp.mul_mem hp (Pp.inv_mem (hPp (h x))), x, rfl, rfl⟩, g, rfl, ?_⟩
      group
  intro v hv
  rcases hv with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact key D.P₁ (B_le_P D true) x
  · exact key D.P₂ (B_le_P D false) x

theorem burnsideF4h_tits_noNormal {X : Type} [Group X] [Finite X] {n : ℕ} (D : RankTwoSystem X n)
    (hU : IsSylowTwoOf D.U ⊤) (R : Subgroup X) (hR : R.Normal) (h2 : IsPGroup 2 R) : R = ⊥ := by
  have hidx : ¬ 2 ∣ D.U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hU.2.2
  let S : Sylow 2 X := hU.2.1.toSylow hidx
  have hUR : D.U ≤ Subgroup.normalizer (R : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hR]
    exact le_top
  have hsup : IsPGroup 2 (R ⊔ D.U : Subgroup X) := h2.to_sup_of_normal_left' hU.2.1 hUR
  have hRU : R ≤ D.U := le_sup_left.trans (S.is_maximal' hsup le_sup_right).le
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  apply burnsideF4h_tits_eq_one_of_conj_mem D
  intro x
  exact D.U_le_B (hRU (hR.conj_mem r hr x))

theorem burnsideF4h_tits_yamStd {X : Type} [Group X] [Finite X] {n : ℕ} (D : RankTwoSystem X n)
    (hU : IsSylowTwoOf D.U ⊤) : YamStd X D.U D.P₁ D.P₂ where
  sylow := hU
  no_normal := burnsideF4h_tits_noNormal D hU
  ne := P₁_ne_P₂ D
  le₀ := (normalizer_U_eq_B D).le.trans (B_le_P D true)
  le₁ := (normalizer_U_eq_B D).le.trans (B_le_P D false)
  coatom₀ := isCoatom_P D true
  coatom₁ := isCoatom_P D false
  above := fun _ hA hne => over_of_ne_top D ((normalizer_U_eq_B D).symm.le.trans hA) hne
  twoLoc₀ := ⟨Q D true, Q_ne_bot D hU true, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P D true),
    (normalizer_Q D hU true).symm⟩
  twoLoc₁ := ⟨Q D false, Q_ne_bot D hU false, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P D false),
    (normalizer_Q D hU false).symm⟩

end YamNoSimple

section YamZero

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem burnsideF4h_tits_mem_P₁_iff (hK : Nat.card K = 2) (y : Gm K 0) :
    y ∈ (burnsideF4h_tits_system hK).P₁ ↔
      (y : ModGL F4.tag K) ∈ ChF.ExceptionalRoots.reeParabolic K 0 1 := by
  haveI hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have hm : octR1 K 0 ∈ (burnsideF4h_tits_system hK).N := (octRGD2 hK').r₁_mem_N
  rw [burnsideF4h_tits_reeParabolic_one]
  have hP := burnsideF4h_tits_P_eq_sup (burnsideF4h_tits_system hK) true (m := octR1 K 0) hm rfl
  show y ∈ CFSG.Quasithin.H13.F431.BN.P (burnsideF4h_tits_system hK) true ↔ _
  rw [hP]
  exact burnsideF4h_tits_mem_sup_iff y (octR1 K 0)

theorem burnsideF4h_tits_mem_P₂_iff (hK : Nat.card K = 2) (y : Gm K 0) :
    y ∈ (burnsideF4h_tits_system hK).P₂ ↔
      (y : ModGL F4.tag K) ∈ ChF.ExceptionalRoots.reeParabolic K 0 0 := by
  haveI hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have hm : octR2 K 0 ∈ (burnsideF4h_tits_system hK).N := (octRGD2 hK').r₂_mem_N
  rw [burnsideF4h_tits_reeParabolic_zero]
  have hP := burnsideF4h_tits_P_eq_sup (burnsideF4h_tits_system hK) false (m := octR2 K 0) hm rfl
  show y ∈ CFSG.Quasithin.H13.F431.BN.P (burnsideF4h_tits_system hK) false ↔ _
  rw [hP]
  exact burnsideF4h_tits_mem_sup_iff y (octR2 K 0)

theorem burnsideF4h_tits_yamPair (hK : Nat.card K = 2) :
    CFSG.Quasithin.IsYAmalgamPair (Ug K 0) (burnsideF4h_tits_system hK).P₁
      (burnsideF4h_tits_system hK).P₂ := by
  haveI hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  haveI : Finite (Gm K 0) := Subtype.finite
  exact (burnsideF4h_tits_yamStd (burnsideF4h_tits_system hK) (isSylowTwoOf_Ug hK')).isYAmalgamPair

end YamZero

section Model

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RuType CFSG.Sporadic.Schreier.Tits
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Quasithin.H13.F431.TwoF4

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

@[expose] noncomputable def burnsideF4h_tits_modelEquiv (hK : Nat.card K = 2) :
    Gm K 0 ≃* ↥twoF4M :=
  haveI : Fact (Nat.card K = 2) := ⟨hK⟩
  ((reeFixedEquivReeGamma K 0).symm.trans (titsIso (K := K))).trans
    (MulEquiv.subgroupCongr twoF4M_eq_titsA.symm)

theorem burnsideF4h_tits_key (hK : Nat.card K = 2) :
    ∃ Φ : Gm K 0 ≃* ↥twoF4M, (Ug K 0).map Φ.toMonoidHom = twoF4Lattice.S ∧
      (((burnsideF4h_tits_system hK).P₁.map Φ.toMonoidHom = twoF4Lattice.P₁ ∧
        (burnsideF4h_tits_system hK).P₂.map Φ.toMonoidHom = twoF4Lattice.P₂) ∨
       ((burnsideF4h_tits_system hK).P₁.map Φ.toMonoidHom = twoF4Lattice.P₂ ∧
        (burnsideF4h_tits_system hK).P₂.map Φ.toMonoidHom = twoF4Lattice.P₁)) := by
  have hY := burnsideF4h_tits_yamPair hK
  let φ := burnsideF4h_tits_modelEquiv hK
  have hpair' := IsYAmalgamPair.map φ hY
  obtain ⟨ρ, hρ⟩ := exists_mulEquiv_map_sylow twoF4Lattice.isSylowTwoOf_top hpair'.1
  let f : Gm K 0 ≃* ↥twoF4M := φ.trans ρ
  have hmap : ∀ M : Subgroup (Gm K 0),
      (M.map φ.toMonoidHom).map ρ.toMonoidHom = M.map f.toMonoidHom := fun M =>
    Subgroup.map_map _ _ _
  have hUf : (Ug K 0).map f.toMonoidHom = twoF4Lattice.S := by
    rw [← hmap]
    exact hρ
  have hpairf := IsYAmalgamPair.map ρ hpair'
  rw [hρ, hmap, hmap] at hpairf
  have hlocal : ∀ M : Subgroup (Gm K 0),
      (M = (burnsideF4h_tits_system hK).P₁ ∨ M = (burnsideF4h_tits_system hK).P₂) →
      (M.map f.toMonoidHom = twoF4Lattice.P₁ ∨ M.map f.toMonoidHom = twoF4Lattice.P₂) := by
    intro M hM
    obtain ⟨hmax, hnorm⟩ := (hpairf.2.2 (M.map f.toMonoidHom)).2
      (by rcases hM with rfl | rfl <;> simp)
    exact twoF4Lattice.eq_P₁_or_P₂_of_maxTwoLocal hmax (Subgroup.le_normalizer.trans hnorm)
  have hne : (burnsideF4h_tits_system hK).P₁.map f.toMonoidHom ≠
      (burnsideF4h_tits_system hK).P₂.map f.toMonoidHom := fun h =>
    hY.2.1 (Subgroup.map_injective f.injective h)
  refine ⟨f, hUf, ?_⟩
  rcases hlocal _ (Or.inl rfl) with h1 | h1 <;> rcases hlocal _ (Or.inr rfl) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

end Model

section Orient

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_tits_reeLocalParabolic_zero :
    F4.reeLocalParabolic K a ⟨0, by decide⟩ =
      F4.reeFixedBorel K a ⊔ Subgroup.zpowers (weylOne K) := by
  rw [← F4.reeParabolic_singleton (K := K) (a := a) (j := ⟨0, by decide⟩)]
  unfold ReeTag.reeParabolic
  rw [Set.image_singleton, ← Subgroup.zpowers_eq_closure]

theorem burnsideF4h_tits_rankOneGroupOne_le (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ≤ F4.reeLocalParabolic K a ⟨0, by decide⟩ := by
  rw [rankOneGroupOne, Subgroup.closure_le]
  rintro g ((hg | hT) | rfl)
  · exact reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
      (reeFixedPosUnipotent_le_reeFixedBorel (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent _ hg))
  · exact reeFixedBorel_le_reeGamma_inf_parabolicSubgroup _
      (reeFixedTorus_le_reeFixedBorel (rankOneTorusOne_le hK hT))
  · exact canonicalRep_fixedOrbitElement_mem_reeGamma_inf _

theorem burnsideF4h_tits_three_dvd_P₂ (hK : Nat.card K = 2) :
    3 ∣ Nat.card (burnsideF4h_tits_system hK).P₂ := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have hR : (rankOneGroupOne K 0).subgroupOf (F4.reeGamma K 0) ≤
      (burnsideF4h_tits_system hK).P₂ := by
    intro y hy
    rw [burnsideF4h_tits_mem_P₂_iff hK y, burnsideF4h_tits_reeParabolic_zero,
      ← burnsideF4h_tits_reeLocalParabolic_zero]
    exact burnsideF4h_tits_rankOneGroupOne_le hK' (Subgroup.mem_subgroupOf.1 hy)
  have hc : Nat.card ((rankOneGroupOne K 0).subgroupOf (F4.reeGamma K 0)) = 6 := by
    have h1 := card_rankOneGroupOne (K := K) (a := 0) hK'
    have h2 := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (rankOneGroupOne_le_reeGamma hK')).toEquiv
    exact h2.trans (h1.trans (by norm_num))
  have h := Subgroup.card_dvd_of_le hR
  rw [hc] at h
  exact dvd_trans (by norm_num) h

end Orient

section OrientModel

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false



theorem burnsideF4h_tits_card_lattice_P₁ : Nat.card twoF4Lattice.P₁ = 20480 := by
  have h1 : twoF4Data.P₁.relIndex twoF4Data.P₁x = 2 :=
    burnsideF4h_tits_relIndex_extSub twoF4Data twoF4Data.P₁_le_D (hq := twoF4Data.q_norm_P₁)
      (hq2 := twoF4Data.q_mul_self_mem_P₁)
  have h2 := Subgroup.relIndex_mul_card (H := twoF4Data.P₁) (K := twoF4Data.P₁x)
  have hle : twoF4Data.P₁ ≤ twoF4Data.P₁x :=
    le_extSub (hq := twoF4Data.q_norm_P₁) (hq2 := twoF4Data.q_mul_self_mem_P₁)
  rw [inf_eq_left.2 hle, h1] at h2
  have h3 : Nat.card twoF4Data.P₁ = 10240 := by
    show Nat.card (titsH.subgroupOf twoF4M) = 10240
    rw [card_subgroupOf_eq titsH_le_twoF4M, titsQH_facts.2.2.2]
  rw [h3] at h2
  show Nat.card twoF4Data.P₁x = 20480
  omega

end OrientModel

section OrientKey

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin
  CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem burnsideF4h_tits_keyOriented (hK : Nat.card K = 2) :
    ∃ Φ : Gm K 0 ≃* ↥twoF4M, (Ug K 0).map Φ.toMonoidHom = twoF4Lattice.S ∧
      (burnsideF4h_tits_system hK).P₁.map Φ.toMonoidHom = twoF4Lattice.P₁ ∧
      (burnsideF4h_tits_system hK).P₂.map Φ.toMonoidHom = twoF4Lattice.P₂ := by
  obtain ⟨Φ, hU, h | h⟩ := burnsideF4h_tits_key hK
  · exact ⟨Φ, hU, h⟩
  · exfalso
    have h3 := burnsideF4h_tits_three_dvd_P₂ hK
    rw [← Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective, h.2,
      burnsideF4h_tits_card_lattice_P₁] at h3
    norm_num at h3

theorem burnsideF4h_tits_map_trans {A B C : Type} [Group A] [Group B] [Group C] (e : A ≃* B)
    (f : B ≃* C) (X : Subgroup A) :
    X.map (e.trans f).toMonoidHom = (X.map e.toMonoidHom).map f.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem burnsideF4h_tits_mem_Ug_iff (hK : Nat.card K = 2) (y : Gm K 0) :
    y ∈ Ug K 0 ↔ (y : ModGL F4.tag K) ∈ reeBorel K 0 := by
  have h1 : y ∈ Ug K 0 ↔ y ∈ (F4.reeFixedBorel K 0).subgroupOf (F4.reeGamma K 0) := by
    rw [← sup_octH_Ug, burnsideF4h_tits_octH_eq_bot hK, bot_sup_eq]
  rw [h1, Subgroup.mem_subgroupOf, burnsideF4h_tits_reeBorel_eq]
  exact Iff.rfl

theorem burnsideF4h_tits_gammaEquiv (hK : Nat.card K = 2) :
    ∃ Φ : ↥(reeGroup K 0) ≃* ↥twoF4M,
      ((reeBorel K 0).subgroupOf (reeGroup K 0)).map Φ.toMonoidHom = twoF4Lattice.S ∧
      ((reeParabolic K 0 1).subgroupOf (reeGroup K 0)).map Φ.toMonoidHom = twoF4Lattice.P₁ ∧
      ((reeParabolic K 0 0).subgroupOf (reeGroup K 0)).map Φ.toMonoidHom = twoF4Lattice.P₂ := by
  obtain ⟨Φ, hU, hP₁, hP₂⟩ := burnsideF4h_tits_keyOriented hK
  let e1 : ↥(reeGroup K 0) ≃* Gm K 0 := MulEquiv.subgroupCongr burnsideF4h_tits_reeGroup_eq
  have hB0 : ((reeBorel K 0).subgroupOf (reeGroup K 0)).map e1.toMonoidHom = Ug K 0 := by
    ext y
    rw [Subgroup.mem_map_equiv, burnsideF4h_tits_mem_Ug_iff hK y]
    exact Iff.rfl
  have hP₁0 : ((reeParabolic K 0 1).subgroupOf (reeGroup K 0)).map e1.toMonoidHom =
      (burnsideF4h_tits_system hK).P₁ := by
    ext y
    rw [Subgroup.mem_map_equiv, burnsideF4h_tits_mem_P₁_iff hK y]
    exact Iff.rfl
  have hP₂0 : ((reeParabolic K 0 0).subgroupOf (reeGroup K 0)).map e1.toMonoidHom =
      (burnsideF4h_tits_system hK).P₂ := by
    ext y
    rw [Subgroup.mem_map_equiv, burnsideF4h_tits_mem_P₂_iff hK y]
    exact Iff.rfl
  refine ⟨e1.trans Φ, ?_, ?_, ?_⟩
  · rw [burnsideF4h_tits_map_trans, hB0, hU]
  · rw [burnsideF4h_tits_map_trans, hP₁0, hP₁]
  · rw [burnsideF4h_tits_map_trans, hP₂0, hP₂]

end OrientKey

section


theorem burnsideF4h_titsParentAssembly (K : Type) [Field K] [Finite K] [CharP K 2] :
    ChF.NativeFrame.titsParentAssemblyGoal K := by
  intro hscope
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  have hK : Nat.card K = 2 := by simpa [ChF.ExceptionalRoots.ReeScope] using hscope
  obtain ⟨Φ, hB, hP₁, hP₂⟩ := burnsideF4h_tits_gammaEquiv hK
  exact burnsideF4h_tits_assembly _ _ _ _ _ _ Φ hB hP₁ hP₂

end


section InvChart

open CFSG.ASVolI.ChF

theorem burnsideF4h_tits_orderOf_two {X : Type} [Group X] {x : X} (h1 : x ≠ 1) (h2 : x * x = 1) :
    orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact h2) h1

theorem burnsideF4h_tits_rootInv_iff {E T : Type} [Group E] [Group T] {core : Subgroup E}
    (ι : T →* E) (hι : Function.Injective ι) (R : Subgroup T) (r : T) (hr : r ∈ R)
    (hr1 : r ≠ 1) (hr2 : r * r = 1) (hR : ∀ x ∈ R, x = 1 ∨ x = r) (x : E) :
    (x ∈ core ∧ x ≠ 1 ∧ x * x = 1 ∧ ∃ c ∈ core, c * x * c⁻¹ ∈ R.map ι) ↔
      (x ∈ core ∧ ∃ c ∈ core, c * x * c⁻¹ = ι r) := by
  constructor
  · rintro ⟨hx, hx1, -, c, hc, l, hl, hlx⟩
    refine ⟨hx, c, hc, ?_⟩
    rcases hR l hl with rfl | rfl
    · exfalso
      apply hx1
      rw [map_one] at hlx
      have : x = c⁻¹ * (c * x * c⁻¹) * c := by group
      rw [this, ← hlx]
      group
    · exact hlx.symm
  · rintro ⟨hx, c, hc, hcx⟩
    refine ⟨hx, ?_, ?_, c, hc, ⟨r, hr, hcx.symm⟩⟩
    · rintro rfl
      apply hr1
      apply hι
      rw [map_one, ← hcx]
      group
    · have h1 : c * (x * x) * c⁻¹ = 1 := by
        calc c * (x * x) * c⁻¹ = (c * x * c⁻¹) * (c * x * c⁻¹) := by group
          _ = ι (r * r) := by rw [hcx, map_mul]
          _ = 1 := by rw [hr2, map_one]
      calc x * x = c⁻¹ * (c * (x * x) * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group

theorem burnsideF4h_tits_rootInvolution_iff {E : Type} [Group E] {core : Subgroup E} {degree : ℕ}
    (chart : NativeChart .Tits 2 degree core) (b : Bool) (x : E) :
    chart.RootInvolution b x ↔ (x ∈ core ∧ x ≠ 1 ∧ x * x = 1 ∧
      ∃ c ∈ core, c * x * c⁻¹ ∈ (if b then chart.shortRoot else chart.longRoot)) := by
  unfold NativeChart.RootInvolution
  constructor
  · rintro ⟨h1, h2, h3, -, h5⟩
    exact ⟨h1, h2, h3, h5⟩
  · rintro ⟨h1, h2, h3, h5⟩
    exact ⟨h1, h2, h3, fun h => absurd h (by decide), h5⟩

theorem burnsideF4h_tits_inv_chart {E T : Type} [Group E] [Group T] {core : Subgroup E}
    {degree : ℕ} (m : T ≃* ↥core) (chart : NativeChart .Tits 2 degree core)
    (L S : Subgroup T)
    (hcL : chart.longRoot = (L.map m.toMonoidHom).map core.subtype)
    (hcS : chart.shortRoot = (S.map m.toMonoidHom).map core.subtype)
    (zT tT : T) (hzL : zT ∈ L) (htS : tT ∈ S) (hz1 : zT ≠ 1) (hz2 : zT * zT = 1)
    (ht1 : tT ≠ 1) (ht2 : tT * tT = 1) (hnc : ¬ IsConj zT tT)
    (hL : ∀ x ∈ L, x = 1 ∨ x = zT) (hS : ∀ x ∈ S, x = 1 ∨ x = tT)
    (hcls : ∀ x : T, x ≠ 1 → x * x = 1 → IsConj zT x ∨ IsConj tT x) :
    ∃ long ∈ chart.longRoot, ∃ short ∈ chart.shortRoot, long ≠ 1 ∧ long * long = 1 ∧
      short ≠ 1 ∧ short * short = 1 ∧
      (¬ ∃ conjugator ∈ core, conjugator * long * conjugator⁻¹ = short) ∧
      (∀ element : E, chart.RootInvolution false element ↔
        element ∈ core ∧ ∃ conjugator ∈ core, conjugator * element * conjugator⁻¹ = long) ∧
      (∀ element : E, chart.RootInvolution true element ↔
        element ∈ core ∧ ∃ conjugator ∈ core, conjugator * element * conjugator⁻¹ = short) ∧
      (∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element ∨ chart.RootInvolution true element) := by
  set ι : T →* E := core.subtype.comp m.toMonoidHom with hιdef
  have hι : Function.Injective ι := core.subtype_injective.comp m.injective
  have hιc : ∀ y : T, ι y ∈ core := fun y => (m y).2
  have hpre : ∀ (c : E) (hc : c ∈ core), ι (m.symm ⟨c, hc⟩) = c := by
    intro c hc
    show ((m (m.symm ⟨c, hc⟩) : ↥core) : E) = c
    rw [MulEquiv.apply_symm_apply]
  have hLι : chart.longRoot = L.map ι := by rw [hcL, Subgroup.map_map]
  have hSι : chart.shortRoot = S.map ι := by rw [hcS, Subgroup.map_map]
  have hRIf : ∀ x : E, chart.RootInvolution false x ↔
      x ∈ core ∧ ∃ c ∈ core, c * x * c⁻¹ = ι zT := by
    intro x
    rw [burnsideF4h_tits_rootInvolution_iff]
    simp only [Bool.false_eq_true, if_false]
    rw [hLι]
    exact burnsideF4h_tits_rootInv_iff ι hι L zT hzL hz1 hz2 hL x
  have hRIt : ∀ x : E, chart.RootInvolution true x ↔
      x ∈ core ∧ ∃ c ∈ core, c * x * c⁻¹ = ι tT := by
    intro x
    rw [burnsideF4h_tits_rootInvolution_iff]
    simp only [if_true]
    rw [hSι]
    exact burnsideF4h_tits_rootInv_iff ι hι S tT htS ht1 ht2 hS x
  refine ⟨ι zT, by rw [hLι]; exact ⟨zT, hzL, rfl⟩, ι tT, by rw [hSι]; exact ⟨tT, htS, rfl⟩,
    fun h => hz1 (hι (by rw [h, map_one])), by rw [← map_mul, hz2, map_one],
    fun h => ht1 (hι (by rw [h, map_one])), by rw [← map_mul, ht2, map_one], ?_, hRIf, hRIt, ?_⟩
  · rintro ⟨c, hc, hct⟩
    apply hnc
    refine isConj_iff.2 ⟨m.symm ⟨c, hc⟩, hι ?_⟩
    rw [map_mul, map_mul, map_inv, hpre c hc, hct]
  · intro x hx hx1 hx2
    set y := m.symm ⟨x, hx⟩ with hy
    have hyx : ι y = x := hpre x hx
    have hy1 : y ≠ 1 := fun h => hx1 (by rw [← hyx, h, map_one])
    have hy2 : y * y = 1 := hι (by rw [map_mul, hyx, hx2, map_one])
    rcases hcls y hy1 hy2 with h | h
    · obtain ⟨g, hg⟩ := isConj_iff.1 h
      left
      refine (hRIf x).2 ⟨hx, (ι g)⁻¹, inv_mem (hιc g), ?_⟩
      rw [← hyx, ← hg, map_mul, map_mul, map_inv]
      group
    · obtain ⟨g, hg⟩ := isConj_iff.1 h
      right
      refine (hRIt x).2 ⟨hx, (ι g)⁻¹, inv_mem (hιc g), ?_⟩
      rw [← hyx, ← hg, map_mul, map_mul, map_inv]
      group

end InvChart

section InvModel

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LocalAnalysis.EvenBN.Tits.Model

set_option linter.unusedSectionVars false


theorem burnsideF4h_tits_twoF4H_le_twoF4M : twoF4H ≤ twoF4M := by
  rintro x (hx | hx)
  · exact titsH_le_twoF4M hx
  · have h := mul_mem (titsH_le_twoF4M hx) tπ_mem_twoF4M
    rwa [inv_mul_cancel_right] at h

theorem burnsideF4h_tits_mem_lattice_P₂_perm (m : ↥twoF4M) :
    m ∈ twoF4Lattice.P₂ ↔ (m : Equiv.Perm (Fin 1755)) ∈ twoF4N := Iff.rfl

theorem burnsideF4h_tits_inv_T {G : Type} [Group G] (Γ B P₂ L Sh : Subgroup G)
    (Φ : ↥Γ ≃* ↥twoF4M)
    (hB : (B.subgroupOf Γ).map Φ.toMonoidHom = twoF4Lattice.S)
    (hP₂ : (P₂.subgroupOf Γ).map Φ.toMonoidHom = twoF4Lattice.P₂)
    (z t : G) (hzΓ : z ∈ Γ) (htΓ : t ∈ Γ) (hzB : z ∈ B)
    (hzc : ∀ u ∈ Γ, u ∈ B → u * z = z * u)
    (hz1 : z ≠ 1) (hz2 : z * z = 1) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (htc : ∀ g ∈ Γ, g * t = t * g → g ∈ P₂)
    (hzL : z ∈ L) (htS : t ∈ Sh)
    (hL : ∀ x ∈ Γ, x ∈ L → x = 1 ∨ x = z) (hS : ∀ x ∈ Γ, x ∈ Sh → x = 1 ∨ x = t) :
    ∃ zT ∈ derivedImage Γ L, ∃ tT ∈ derivedImage Γ Sh,
      zT ≠ 1 ∧ zT * zT = 1 ∧ tT ≠ 1 ∧ tT * tT = 1 ∧ ¬ IsConj zT tT ∧
      (∀ x ∈ derivedImage Γ L, x = 1 ∨ x = zT) ∧ (∀ x ∈ derivedImage Γ Sh, x = 1 ∨ x = tT) ∧
      (∀ x : DerivedCentralQuotient Γ, x ≠ 1 → x * x = 1 → IsConj zT x ∨ IsConj tT x) := by
  obtain ⟨Θ, hΘ⟩ := burnsideF4h_tits_commutator_equiv Γ Φ
  have hZ' : Subgroup.center ↥⁅Γ, Γ⁆ = ⊥ :=
    burnsideF4h_tits_center_eq_bot_of_equiv Θ burnsideF4h_tits_center_titsD
  obtain ⟨eC, heC⟩ := burnsideF4h_tits_exists_derivedEquiv Γ ⁅Γ, Γ⁆ rfl hZ'
  set Ψ := eC.trans Θ with hΨdef
  have hle : ⁅Γ, Γ⁆ ≤ Γ := Subgroup.commutator_le_self Γ
  have hΨ : ∀ y : ↥⁅Γ, Γ⁆, ((Ψ (QuotientGroup.mk y) : ↥titsD) : Equiv.Perm (Fin 1755)) =
      ((Φ ⟨y, hle y.2⟩ : ↥twoF4M) : Equiv.Perm (Fin 1755)) := by
    intro y
    have h1 : eC (QuotientGroup.mk y) = y := Subtype.ext (heC y)
    show ((Θ (eC (QuotientGroup.mk y)) : ↥titsD) : Equiv.Perm (Fin 1755)) = _
    rw [h1, hΘ]
  have hmemD : ∀ g : ↥Γ, ((Φ g : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ titsD →
      (g : G) ∈ ⁅Γ, Γ⁆ := by
    intro g hg
    have h1 : Φ g ∈ titsD.subgroupOf twoF4M := hg
    rw [← burnsideF4h_tits_commutator_map Γ Φ, Subgroup.mem_map_equiv,
      MulEquiv.symm_apply_apply] at h1
    exact h1
  have hval1 : ∀ g : ↥Γ, ((Φ g : ↥twoF4M) : Equiv.Perm (Fin 1755)) = 1 → (g : G) = 1 := by
    intro g hg
    have h1 : Φ g = 1 := Subtype.ext hg
    rw [← map_one Φ] at h1
    exact congrArg Subtype.val (Φ.injective h1)
  have hvalsq : ∀ g : ↥Γ, (g : G) * g = 1 → ((Φ g : ↥twoF4M) : Equiv.Perm (Fin 1755)) *
      ((Φ g : ↥twoF4M) : Equiv.Perm (Fin 1755)) = 1 := by
    intro g hg
    have h1 : g * g = 1 := Subtype.ext hg
    have h2 := congrArg (fun x => ((Φ x : ↥twoF4M) : Equiv.Perm (Fin 1755))) h1
    simpa [map_mul] using h2
  set gz : ↥Γ := ⟨z, hzΓ⟩ with hgz
  have hzval : ((Φ gz : ↥twoF4M) : Equiv.Perm (Fin 1755)) = titsZ := by
    have hcomm : ∀ s ∈ titsS, s * ((Φ gz : ↥twoF4M) : Equiv.Perm (Fin 1755)) =
        ((Φ gz : ↥twoF4M) : Equiv.Perm (Fin 1755)) * s := by
      intro s hs
      have hms : (⟨s, titsS_le_twoF4M hs⟩ : ↥twoF4M) ∈ twoF4Lattice.S :=
        (burnsideF4h_tits_mem_lattice_S _ (titsS_le_titsD hs)).2 hs
      rw [← hB] at hms
      obtain ⟨u, hu, hue⟩ := hms
      have h1 : u * gz = gz * u := Subtype.ext (hzc u u.2 hu)
      have h2 := congrArg (fun x => ((Φ x : ↥twoF4M) : Equiv.Perm (Fin 1755))) h1
      simp only [map_mul, Subgroup.coe_mul] at h2
      have h3 : ((Φ u : ↥twoF4M) : Equiv.Perm (Fin 1755)) = s := congrArg Subtype.val hue
      rwa [h3] at h2
    have hA : ((Φ gz : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈
        CFSG.Sporadic.Schreier.Tits.titsA := RuType.twoF4M_eq_titsA.le (Φ gz).2
    have hzpow : ((Φ gz : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈ Subgroup.zpowers titsZ := by
      rw [← titsA_centralizer_titsS]
      exact ⟨hA, Subgroup.mem_centralizer_iff.2 hcomm⟩
    rcases (mem_zpowers_of_orderOf_two orderOf_titsZ).1 hzpow with h | h
    · exact absurd (hval1 gz h) hz1
    · exact h
  set gt : ↥Γ := ⟨t, htΓ⟩ with hgt
  have htA : ((Φ gt : ↥twoF4M) : Equiv.Perm (Fin 1755)) ∈
      CFSG.Sporadic.Schreier.Tits.titsA := RuType.twoF4M_eq_titsA.le (Φ gt).2
  have hto : orderOf ((Φ gt : ↥twoF4M) : Equiv.Perm (Fin 1755)) = 2 :=
    burnsideF4h_tits_orderOf_two (fun h => ht1 (hval1 gt h)) (hvalsq gt ht2)
  have hnotZ : ∀ d ∈ titsD, d * titsZ * d⁻¹ ≠ ((Φ gt : ↥twoF4M) : Equiv.Perm (Fin 1755)) := by
    intro d hd hdz
    have hle2 : twoF4H.map (MulAut.conj d).toMonoidHom ≤ twoF4N := by
      rintro _ ⟨h, hh, rfl⟩
      show d * h * d⁻¹ ∈ twoF4N
      have hdM : d ∈ twoF4M := titsD_le_twoF4M hd
      have hyM : d * h * d⁻¹ ∈ twoF4M :=
        mul_mem (mul_mem hdM (burnsideF4h_tits_twoF4H_le_twoF4M hh)) (inv_mem hdM)
      have hz : h * titsZ = titsZ * h :=
        Subgroup.mem_centralizer_singleton_iff.1 (twoF4H_le_centralizer_titsZ hh)
      have hyc : (d * h * d⁻¹) * ((Φ gt : ↥twoF4M) : Equiv.Perm (Fin 1755)) =
          ((Φ gt : ↥twoF4M) : Equiv.Perm (Fin 1755)) * (d * h * d⁻¹) := by
        rw [← hdz]
        calc d * h * d⁻¹ * (d * titsZ * d⁻¹) = d * (h * titsZ) * d⁻¹ := by group
          _ = d * (titsZ * h) * d⁻¹ := by rw [hz]
          _ = d * titsZ * d⁻¹ * (d * h * d⁻¹) := by group
      set y' : ↥twoF4M := ⟨d * h * d⁻¹, hyM⟩ with hy'
      have hg : Φ.symm y' * gt = gt * Φ.symm y' := by
        apply Φ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact Subtype.ext hyc
      have hP : ((Φ.symm y' : ↥Γ) : G) ∈ P₂ := htc _ (Φ.symm y').2 (congrArg Subtype.val hg)
      have hy'P : y' ∈ twoF4Lattice.P₂ := by
        rw [← hP₂]
        exact ⟨Φ.symm y', hP, Φ.apply_symm_apply y'⟩
      exact (burnsideF4h_tits_mem_lattice_P₂_perm y').1 hy'P
    have hcard := Subgroup.card_le_of_le hle2
    rw [Subgroup.card_map_of_injective (MulAut.conj d).injective, card_twoF4H,
      card_twoF4N.1] at hcard
    omega
  obtain ⟨htD, d₀, hd₀, hd₀t⟩ := titsA_involution_conj htA hto
  have hd₀t' : d₀ * titsTInv * d₀⁻¹ = ((Φ gt : ↥twoF4M) : Equiv.Perm (Fin 1755)) := by
    rcases hd₀t with h | h
    · exact absurd h (hnotZ d₀ hd₀)
    · exact h
  have hzΓ' : z ∈ ⁅Γ, Γ⁆ := hmemD gz (by rw [hzval]; exact titsZ_mem_titsD)
  have htΓ' : t ∈ ⁅Γ, Γ⁆ := hmemD gt htD
  set zT : DerivedCentralQuotient Γ := QuotientGroup.mk (⟨z, hzΓ'⟩ : ↥⁅Γ, Γ⁆) with hzT
  set tT : DerivedCentralQuotient Γ := QuotientGroup.mk (⟨t, htΓ'⟩ : ↥⁅Γ, Γ⁆) with htT
  have hΨz : ((Ψ zT : ↥titsD) : Equiv.Perm (Fin 1755)) = titsZ := by
    rw [hzT, hΨ]
    exact hzval
  have hΨt : ((Ψ tT : ↥titsD) : Equiv.Perm (Fin 1755)) =
      ((Φ gt : ↥twoF4M) : Equiv.Perm (Fin 1755)) := by
    rw [htT, hΨ]
  have hΨ1 : ∀ x : DerivedCentralQuotient Γ,
      ((Ψ x : ↥titsD) : Equiv.Perm (Fin 1755)) = 1 → x = 1 := by
    intro x hx
    have h1 : Ψ x = 1 := Subtype.ext hx
    rw [← map_one Ψ] at h1
    exact Ψ.injective h1
  have hsq : ∀ (y : ↥⁅Γ, Γ⁆), (y : G) * y = 1 →
      (QuotientGroup.mk y : DerivedCentralQuotient Γ) * QuotientGroup.mk y = 1 := by
    intro y hy
    rw [← QuotientGroup.mk_mul]
    have : y * y = 1 := Subtype.ext hy
    rw [this, QuotientGroup.mk_one]
  have htitsZ1 : titsZ ≠ 1 := fun h => by
    have := orderOf_titsZ
    rw [h, orderOf_one] at this
    omega
  have hbound : ∀ (X : Subgroup G) (w : G) (hw : w ∈ ⁅Γ, Γ⁆),
      (∀ x ∈ Γ, x ∈ X → x = 1 ∨ x = w) →
      ∀ x ∈ derivedImage Γ X, x = 1 ∨ x = QuotientGroup.mk (⟨w, hw⟩ : ↥⁅Γ, Γ⁆) := by
    intro X w hw hX x hx
    obtain ⟨y, hy, rfl⟩ := hx
    rcases hX (y : G) (hle y.2) hy with h | h
    · left
      have : y = 1 := Subtype.ext h
      rw [this]
      rfl
    · right
      have : y = ⟨w, hw⟩ := Subtype.ext h
      rw [this]
      rfl
  refine ⟨zT, ⟨⟨z, hzΓ'⟩, hzL, rfl⟩, tT, ⟨⟨t, htΓ'⟩, htS, rfl⟩, ?_, hsq _ hz2, ?_, hsq _ ht2,
    ?_, hbound L z hzΓ' hL, hbound Sh t htΓ' hS, ?_⟩
  · intro h
    apply htitsZ1
    rw [← hΨz, h, map_one]
    rfl
  · intro h
    apply ht1
    apply hval1 gt
    rw [← hΨt, h, map_one]
    rfl
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    have h1 := congrArg (fun x => ((Ψ x : ↥titsD) : Equiv.Perm (Fin 1755))) hc
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hΨz, hΨt, ← hd₀t'] at h1
    have hcA : (d₀⁻¹ * ((Ψ c : ↥titsD) : Equiv.Perm (Fin 1755))) ∈
        CFSG.Sporadic.Schreier.Tits.titsA :=
      titsD_le_titsA (mul_mem (inv_mem hd₀) (Ψ c).2)
    apply titsA_conj_titsZ_ne_titsTInv hcA
    calc d₀⁻¹ * ((Ψ c : ↥titsD) : Equiv.Perm (Fin 1755)) * titsZ *
          (d₀⁻¹ * ((Ψ c : ↥titsD) : Equiv.Perm (Fin 1755)))⁻¹ =
        d₀⁻¹ * (((Ψ c : ↥titsD) : Equiv.Perm (Fin 1755)) * titsZ *
          ((Ψ c : ↥titsD) : Equiv.Perm (Fin 1755))⁻¹) * d₀ := by group
      _ = titsTInv := by rw [h1]; group
  · intro x hx1 hx2
    have hvA : ((Ψ x : ↥titsD) : Equiv.Perm (Fin 1755)) ∈ CFSG.Sporadic.Schreier.Tits.titsA :=
      titsD_le_titsA (Ψ x).2
    have hvo : orderOf ((Ψ x : ↥titsD) : Equiv.Perm (Fin 1755)) = 2 := by
      refine burnsideF4h_tits_orderOf_two (fun h => hx1 (hΨ1 x h)) ?_
      have := congrArg (fun y => ((Ψ y : ↥titsD) : Equiv.Perm (Fin 1755))) hx2
      simpa [map_mul] using this
    obtain ⟨-, d, hd, hdx⟩ := titsA_involution_conj hvA hvo
    rcases hdx with h | h
    · left
      refine isConj_iff.2 ⟨Ψ.symm ⟨d, hd⟩, Ψ.injective (Subtype.ext ?_)⟩
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [hΨz]
      exact h
    · right
      refine isConj_iff.2 ⟨Ψ.symm (⟨d, hd⟩ * ⟨d₀, hd₀⟩⁻¹), Ψ.injective (Subtype.ext ?_)⟩
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [hΨt, ← hd₀t', ← h]
      group

end InvModel

section WordAppend

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {tag : Tag} {K : Type}
  [Field K]

theorem burnsideF4h_tits_wordUnit_append (w₁ w₂ : List (Fin tag.rank)) :
    ((w₁ ++ w₂).map fun i => weylElt tag K i 1).reverse.prod =
      (w₂.map fun i => weylElt tag K i 1).reverse.prod *
        (w₁.map fun i => weylElt tag K i 1).reverse.prod := by
  simp [List.map_append, List.reverse_append, List.prod_append]

end WordAppend

section WeylConj

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots

variable {tag : Tag} {K : Type}
  [Field K]

theorem burnsideF4h_tits_fixedWeylConjugate_eq (model root : Subgroup (ModGL tag K))
    (word : List (Fin tag.rank)) (n : ModGL tag K) (hn : n ∈ model)
    (hop : (n : Module.End K (RootModule tag K)) = weylWordOperator tag K word) :
    fixedWeylConjugate tag K model word root = root.map (MulAut.conj n).toMonoidHom := by
  unfold fixedWeylConjugate
  have h : {element | ∃ actor : ModGL tag K, actor ∈ model ∧
      (actor : Module.End K (RootModule tag K)) = weylWordOperator tag K word ∧
      ∃ generator ∈ root, element = actor * generator * actor⁻¹} =
      ((root.map (MulAut.conj n).toMonoidHom : Subgroup (ModGL tag K)) : Set (ModGL tag K)) := by
    ext x
    constructor
    · rintro ⟨actor, -, hact, g, hg, rfl⟩
      have : actor = n := Units.ext (hact.trans hop.symm)
      subst this
      exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨n, hn, hop, g, hg, rfl⟩
  rw [h]
  exact Subgroup.closure_eq _

end WeylConj

section LongShort

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_tits_weylOne_mem : weylOne K ∈ reeGroup K a := by
  have h : weylOne K ∈ F4.reeGamma K a := (octR2 K a).2
  rw [burnsideF4h_tits_reeGroup_eq]
  exact h

theorem burnsideF4h_tits_weylTwo_mem : weylTwo K ∈ reeGroup K a := by
  have h : weylTwo K ∈ F4.reeGamma K a := (octR1 K a).2
  rw [burnsideF4h_tits_reeGroup_eq]
  exact h

theorem burnsideF4h_tits_longActor :
    (([0, 3, 1, 2, 1, 2, 0, 3] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 K i 1).reverse.prod =
      weylOne K * weylTwo K * weylOne K := by
  have h : ([0, 3, 1, 2, 1, 2, 0, 3] : List (Fin Tag.F4.rank)) = [0, 3] ++ [1, 2, 1, 2] ++ [0, 3] :=
    rfl
  rw [h, burnsideF4h_tits_wordUnit_append, burnsideF4h_tits_wordUnit_append,
    burnsideF4h_tits_wordUnit_zero, burnsideF4h_tits_wordUnit_one, mul_assoc]
  rfl

theorem burnsideF4h_tits_shortActor :
    (([1, 2, 1, 2, 0, 3, 1, 2, 1, 2] : List (Fin Tag.F4.rank)).map
      fun i => weylElt Tag.F4 K i 1).reverse.prod = weylTwo K * weylOne K * weylTwo K := by
  have h : ([1, 2, 1, 2, 0, 3, 1, 2, 1, 2] : List (Fin Tag.F4.rank)) =
      [1, 2, 1, 2] ++ [0, 3] ++ [1, 2, 1, 2] := rfl
  rw [h, burnsideF4h_tits_wordUnit_append, burnsideF4h_tits_wordUnit_append,
    burnsideF4h_tits_wordUnit_zero, burnsideF4h_tits_wordUnit_one, mul_assoc]
  rfl

theorem burnsideF4h_tits_reeLongRoot_eq :
    reeLongRoot K a = (reeMiddleCentralRoot K a).map
      (MulAut.conj (weylOne K * weylTwo K * weylOne K)).toMonoidHom := by
  unfold ChF.ExceptionalRoots.reeLongRoot
  refine burnsideF4h_tits_fixedWeylConjugate_eq _ _ _ _ ?_ ?_
  · exact mul_mem (mul_mem burnsideF4h_tits_weylOne_mem burnsideF4h_tits_weylTwo_mem)
      burnsideF4h_tits_weylOne_mem
  · rw [burnsideF4h_tits_weylWordOperator_eq, burnsideF4h_tits_longActor]

theorem burnsideF4h_tits_reeShortRoot_eq :
    reeShortRoot K a = (reeTwoRoot K a).map
      (MulAut.conj (weylTwo K * weylOne K * weylTwo K)).toMonoidHom := by
  unfold ChF.ExceptionalRoots.reeShortRoot
  refine burnsideF4h_tits_fixedWeylConjugate_eq _ _ _ _ ?_ ?_
  · exact mul_mem (mul_mem burnsideF4h_tits_weylTwo_mem burnsideF4h_tits_weylOne_mem)
      burnsideF4h_tits_weylTwo_mem
  · rw [burnsideF4h_tits_weylWordOperator_eq, burnsideF4h_tits_shortActor]

end LongShort

theorem burnsideF4h_tits_le_normalizer_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ K, Commute x y) : H ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have e : x * y * x⁻¹ = y := by
      rw [(h x hx y hy).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hy
  · intro hy
    have h2 := (h x⁻¹ (H.inv_mem hx) _ hy).eq
    have e : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = (x * y * x⁻¹) * x⁻¹ * x := by rw [h2]
        _ = x * y * x⁻¹ := by group
    rw [e]
    exact hy

section LongShortB

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem burnsideF4h_tits_reeFourSeed_eq (i : Fin 4) : reeFourSeed i = largeReeRoot i := by
  fin_cases i <;> rfl

open scoped Pointwise in
theorem burnsideF4h_tits_middleCentral_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ModGL Tag.F4 K} (hg : g ∈ reeMiddleCentralRoot K a) :
    ∃ v : K, g = largeReeCoord a K 0 v := by
  obtain ⟨hgΓ, hgJ⟩ := Subgroup.mem_inf.1 hg
  rw [burnsideF4h_tits_reeGroup_eq] at hgΓ
  have e2 : absoluteRoot Tag.F4 K (reeFourSeed 2) = rootSubgroup Tag.F4 K (largeReeRoot 2) := by
    rw [burnsideF4h_tits_reeFourSeed_eq]
    exact burnsideF4h_tits_absoluteRoot_eq (largeReeRoot_pos 2).1
  have e3 : absoluteRoot Tag.F4 K (reeFourSeed 3) = rootSubgroup Tag.F4 K (largeReeRoot 3) := by
    rw [burnsideF4h_tits_reeFourSeed_eq]
    exact burnsideF4h_tits_absoluteRoot_eq (largeReeRoot_pos 3).1
  rw [e2, e3] at hgJ
  have h2 : (2 : K) = 0 := F4_two_eq_zero
  have hcomm : ∀ x ∈ rootSubgroup Tag.F4 K (largeReeRoot 2),
      ∀ y ∈ rootSubgroup Tag.F4 K (largeReeRoot 3), Commute x y :=
    (large_Ree_B2_characteristic_two_commutators K h2).2.1 2 3 (by decide) (by decide)
  have hle := burnsideF4h_tits_le_normalizer_of_commute hcomm
  have hmem : g ∈ ((rootSubgroup Tag.F4 K (largeReeRoot 2) : Subgroup (ModGL Tag.F4 K)) :
      Set (ModGL Tag.F4 K)) * (rootSubgroup Tag.F4 K (largeReeRoot 3) : Set (ModGL Tag.F4 K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hgJ
  rw [Set.mem_mul] at hmem
  obtain ⟨x, hx, y, hy, rfl⟩ := hmem
  obtain ⟨C, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨D, rfl⟩ := mem_rootSubgroup.1 hy
  have hP : pinnedX Tag.F4 K (largeReeRoot 2) C * pinnedX Tag.F4 K (largeReeRoot 3) D =
      largeReeP K 0 0 C D := by
    simp [largeReeP, largeReeX, pinnedX_zero]
  have hU : pinnedX Tag.F4 K (largeReeRoot 2) C * pinnedX Tag.F4 K (largeReeRoot 3) D ∈
      F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ := by
    refine Subgroup.mem_inf.2 ⟨?_, hgΓ⟩
    rw [F4_fixedOrbitRoots_one, hP]
    exact largeReeP_mem_rootSpan _ _ _ _
  obtain ⟨p, -, hp⟩ := (bijOn_largeReeCoord hK).2.2 hU
  have hp' : largeReeP K p.1 (largeReeSigma a p.1) p.2
      (largeReeSigma a p.2 + p.1 ^ 2 * largeReeSigma a p.1) = largeReeP K 0 0 C D := by
    rw [← hP, ← hp]
    rfl
  obtain ⟨h1, -, -, -⟩ := largeReeP_injective hp'
  refine ⟨p.2, ?_⟩
  rw [← hp]
  show largeReeCoord a K p.1 p.2 = _
  rw [h1]

theorem burnsideF4h_tits_coord_mem_middleCentral (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : K) :
    largeReeCoord a K 0 v ∈ reeMiddleCentralRoot K a := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h : largeReeCoord a K 0 v ∈ F4.reeGamma K a :=
      (Subgroup.mem_inf.1 (largeReeCoord_mem hK 0 v)).2
    rw [burnsideF4h_tits_reeGroup_eq]
    exact h
  · have e : largeReeCoord a K 0 v =
        pinnedX Tag.F4 K (reeFourSeed 2) v * pinnedX Tag.F4 K (reeFourSeed 3) (largeReeSigma a v) := by
      simp [largeReeCoord, largeReeP, largeReeX, burnsideF4h_tits_reeFourSeed_eq, pinnedX_zero,
        largeReeSigma_zero]
    rw [e]
    have hr2 : IsRoot Tag.F4 (reeFourSeed 2) := by
      rw [burnsideF4h_tits_reeFourSeed_eq]; exact (largeReeRoot_pos 2).1
    have hr3 : IsRoot Tag.F4 (reeFourSeed 3) := by
      rw [burnsideF4h_tits_reeFourSeed_eq]; exact (largeReeRoot_pos 3).1
    exact mul_mem
      (Subgroup.mem_sup_left (burnsideF4h_tits_rootSubgroup_le_absoluteRoot hr2
        (Subgroup.subset_closure ⟨v, rfl⟩)))
      (Subgroup.mem_sup_right (burnsideF4h_tits_rootSubgroup_le_absoluteRoot hr3
        (Subgroup.subset_closure ⟨largeReeSigma a v, rfl⟩)))

open CFSG.LieType.Ree.LargeReeCover in
theorem burnsideF4h_tits_sylowA_eq_stdTwoG (s : K) : sylowA a K s = stdTwoG a s := by
  have h : stdTwoRoot 0 = RootOps.orbitCertRoot F4.tag 24 ∧
      stdTwoRoot 1 = RootOps.orbitCertRoot F4.tag 33 := by
    decide +kernel
  rw [stdTwoG, sylowA, sylowX, sylowX, h.1, h.2]

theorem burnsideF4h_tits_reeLongRoot_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ModGL Tag.F4 K} (hy : y ∈ reeLongRoot K a) : ∃ v : K, y = centralZ K a v := by
  rw [burnsideF4h_tits_reeLongRoot_eq] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨v, rfl⟩ := burnsideF4h_tits_middleCentral_coord hK hg
  refine ⟨v, ?_⟩
  have h := weyl_conj_sylowB_zero (m := a) (K := K) v
  rw [sylowH_zero_eq_centralZ, sylowB_eq_largeReeCoord] at h
  exact h

theorem burnsideF4h_tits_centralZ_mem_reeLongRoot (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : K) :
    centralZ K a v ∈ reeLongRoot K a := by
  rw [burnsideF4h_tits_reeLongRoot_eq]
  refine ⟨largeReeCoord a K 0 v, burnsideF4h_tits_coord_mem_middleCentral hK v, ?_⟩
  have h := weyl_conj_sylowB_zero (m := a) (K := K) v
  rw [sylowH_zero_eq_centralZ, sylowB_eq_largeReeCoord] at h
  exact h

open scoped Pointwise in
theorem burnsideF4h_tits_reeTwoRoot_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ModGL Tag.F4 K} (hg : g ∈ reeTwoRoot K a) : ∃ s : K, g = sylowA a K s := by
  obtain ⟨hgΓ0, hgJ⟩ := Subgroup.mem_inf.1 hg
  have hgΓ : g ∈ F4.reeGamma K a := by
    have h : g ∈ reeGroup K a := hgΓ0
    rw [burnsideF4h_tits_reeGroup_eq] at h
    exact h
  have e0 : absoluteRoot Tag.F4 K (Pi.single 0 1) = rootSubgroup Tag.F4 K (Pi.single 0 1) :=
    burnsideF4h_tits_absoluteRoot_eq (isRoot_single Tag.F4 _)
  have e3 : absoluteRoot Tag.F4 K (Pi.single 3 1) = rootSubgroup Tag.F4 K (Pi.single 3 1) :=
    burnsideF4h_tits_absoluteRoot_eq (isRoot_single Tag.F4 _)
  rw [e0, e3] at hgJ
  have hU : g ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
    refine Subgroup.mem_inf.2 ⟨?_, hgΓ⟩
    rw [F4_fixedOrbitRoots_zero]
    have h0 : rootSubgroup Tag.F4 K (Pi.single 0 1) ≤
        rootSpan Tag.F4 K {Pi.single largeReeI1 1, Pi.single largeReeI4 1} :=
      le_iSup₂_of_le (Pi.single largeReeI1 1) (Set.mem_insert _ _) le_rfl
    have h3 : rootSubgroup Tag.F4 K (Pi.single 3 1) ≤
        rootSpan Tag.F4 K {Pi.single largeReeI1 1, Pi.single largeReeI4 1} :=
      le_iSup₂_of_le (Pi.single largeReeI4 1) (Set.mem_insert_of_mem _ (Set.mem_singleton _)) le_rfl
    exact (sup_le h0 h3) hgJ
  obtain ⟨s, hs⟩ := exists_stdTwoG_eq hK hU
  exact ⟨s, by rw [burnsideF4h_tits_sylowA_eq_stdTwoG, hs]⟩

theorem burnsideF4h_tits_sylowA_mem_reeTwoRoot (hK : Nat.card K = 2 ^ (2 * a + 1)) (s : K) :
    sylowA a K s ∈ reeTwoRoot K a := by
  have hU : sylowA a K s ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
    rw [burnsideF4h_tits_sylowA_eq_stdTwoG]
    exact stdTwoG_mem hK s
  have hΓ : sylowA a K s ∈ reeGroup K a := by
    have h : sylowA a K s ∈ F4.reeGamma K a := (Subgroup.mem_inf.1 hU).2
    rw [burnsideF4h_tits_reeGroup_eq]
    exact h
  refine ⟨hΓ, ?_⟩
  · rw [burnsideF4h_tits_sylowA_eq_stdTwoG, stdTwoG,
      (stdTwoRoot_eq_single).1, (stdTwoRoot_eq_single).2]
    exact mul_mem
      (Subgroup.mem_sup_right (burnsideF4h_tits_rootSubgroup_le_absoluteRoot
        (isRoot_single Tag.F4 _) (Subgroup.subset_closure ⟨s, rfl⟩)))
      (Subgroup.mem_sup_left (burnsideF4h_tits_rootSubgroup_le_absoluteRoot
        (isRoot_single Tag.F4 _) (Subgroup.subset_closure ⟨largeReeSigma a s, rfl⟩)))

theorem burnsideF4h_tits_reeShortRoot_coord (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y : ModGL Tag.F4 K} (hy : y ∈ reeShortRoot K a) :
    ∃ s : K, y = (weylTwo K * weylOne K * weylTwo K) * sylowA a K s *
      (weylTwo K * weylOne K * weylTwo K)⁻¹ := by
  rw [burnsideF4h_tits_reeShortRoot_eq] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  obtain ⟨s, rfl⟩ := burnsideF4h_tits_reeTwoRoot_coord hK hg
  exact ⟨s, rfl⟩

theorem burnsideF4h_tits_sylowL_mem_reeShortRoot (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    sylowL a K 1 ∈ reeShortRoot K a := by
  rw [burnsideF4h_tits_reeShortRoot_eq]
  refine ⟨sylowA a K 1, burnsideF4h_tits_sylowA_mem_reeTwoRoot hK 1, ?_⟩
  have h := weyl_conj_sylowA_one (m := a) (K := K)
  exact h

end LongShortB

section InvGamma

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4 CFSG.LocalAnalysis.EvenBN.TwoF4

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem burnsideF4h_tits_eq_zero_or_one (hK : Nat.card K = 2) (v : K) : v = 0 ∨ v = 1 := by
  by_cases hv : v = 0
  · exact Or.inl hv
  · right
    haveI := burnsideF4h_tits_units_subsingleton hK
    exact congrArg Units.val (Subsingleton.elim (Units.mk0 v hv) 1)

theorem burnsideF4h_tits_centralZ_one :
    centralZ K 0 1 = f4x K 44 1 * f4x K 47 1 := by
  rw [CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.f4x_44,
    CFSG.ComponentClassification.UnbalancedCatalog.LargeReeCatalog.f4x_47, centralZ, one_pow]
  rfl

theorem burnsideF4h_tits_reeBorel_le_posUnipotent (hK : Nat.card K = 2) :
    reeBorel K 0 ≤ posUnipotent Tag.F4 K := by
  intro u hu
  have h1 : u ∈ absoluteBorel Tag.F4 K := (Subgroup.mem_inf.1 hu).2
  rw [burnsideF4h_tits_absoluteBorel_eq, borelGroup, burnsideF4h_tits_torusGroup_eq_bot hK,
    bot_sup_eq] at h1
  exact h1

theorem burnsideF4h_tits_f4x_comm (hK : Nat.card K = 2) {u : ModGL Tag.F4 K}
    (hu : u ∈ reeBorel K 0) :
    u * (f4x K 44 1 * f4x K 47 1) = (f4x K 44 1 * f4x K 47 1) * u := by
  haveI : CharP K 2 := ‹CharP K F4.prime›
  have hu' := burnsideF4h_tits_reeBorel_le_posUnipotent hK hu
  have h44 := f4x_central (Or.inl rfl : (44 : ℕ) = 44 ∨ (44 : ℕ) = 47) (1 : K) hu'
  have h47 := f4x_central (Or.inr rfl : (47 : ℕ) = 44 ∨ (47 : ℕ) = 47) (1 : K) hu'
  calc u * (f4x K 44 1 * f4x K 47 1) = (u * f4x K 44 1) * f4x K 47 1 := by group
    _ = f4x K 44 1 * (u * f4x K 47 1) := by rw [h44]; group
    _ = f4x K 44 1 * f4x K 47 1 * u := by rw [h47]; group

theorem burnsideF4h_tits_f4x_mem_reeBorel (hK : Nat.card K = 2) :
    f4x K 44 1 * f4x K 47 1 ∈ reeBorel K 0 := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have h : centralZ K 0 1 ∈ reeBorel K 0 := by
    rw [burnsideF4h_tits_reeBorel_eq, ← invE_eq_centralZ.1]
    exact reeFixedPosUnipotent_le_reeFixedBorel (invE_invF_mem hK').2.2.1
  rw [burnsideF4h_tits_centralZ_one] at h
  exact h

theorem burnsideF4h_tits_f4x_mem_reeGroup (hK : Nat.card K = 2) :
    f4x K 44 1 * f4x K 47 1 ∈ reeGroup K 0 := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have h : centralZ K 0 1 ∈ reeGroup K 0 := by
    rw [burnsideF4h_tits_reeGroup_eq, ← invE_eq_centralZ.1]
    exact reeFixedPosUnipotent_le_reeGamma (invE_invF_mem hK').2.2.1
  rw [burnsideF4h_tits_centralZ_one] at h
  exact h

theorem burnsideF4h_tits_sylowL_mem_reeGroup (hK : Nat.card K = 2) :
    sylowL 0 K 1 ∈ reeGroup K 0 := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  rw [burnsideF4h_tits_reeGroup_eq, ← invE_eq_centralZ.2]
  exact reeFixedPosUnipotent_le_reeGamma (invE_invF_mem hK').2.2.2.1

theorem burnsideF4h_tits_of_orderOf_two {X : Type} [Group X] {x : X} (h : orderOf x = 2) :
    x ≠ 1 ∧ x * x = 1 := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [orderOf_one] at h
    omega
  · rw [← sq, ← h, pow_orderOf_eq_one]

theorem burnsideF4h_tits_f4x_inv (hK : Nat.card K = 2) :
    f4x K 44 1 * f4x K 47 1 ≠ 1 ∧
      (f4x K 44 1 * f4x K 47 1) * (f4x K 44 1 * f4x K 47 1) = 1 := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have h := burnsideF4h_tits_of_orderOf_two (invE_invF_mem hK').2.2.2.2.1
  rw [invE_eq_centralZ.1, burnsideF4h_tits_centralZ_one] at h
  exact h

theorem burnsideF4h_tits_sylowL_inv (hK : Nat.card K = 2) :
    sylowL 0 K 1 ≠ 1 ∧ sylowL 0 K 1 * sylowL 0 K 1 = 1 := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have h := burnsideF4h_tits_of_orderOf_two (invE_invF_mem hK').2.2.2.2.2
  rw [invE_eq_centralZ.2] at h
  exact h

theorem burnsideF4h_tits_centralizer_sylowL_le (hK : Nat.card K = 2) {g : ModGL F4.tag K}
    (hg : g ∈ reeGroup K 0) (hgt : g * sylowL 0 K 1 = sylowL 0 K 1 * g) :
    g ∈ reeParabolic K 0 0 := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have hmem : g ∈ F4.reeGamma K 0 ⊓ Subgroup.centralizer {sylowL 0 K 1} := by
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 hgt⟩
    rw [← burnsideF4h_tits_reeGroup_eq]
    exact hg
  have h := reeGamma_inf_centralizer_tOne_le hK' hmem
  rw [burnsideF4h_tits_reeLocalParabolic_zero] at h
  rw [burnsideF4h_tits_reeParabolic_zero]
  exact h

theorem burnsideF4h_tits_f4x_mem_reeLongRoot (hK : Nat.card K = 2) :
    f4x K 44 1 * f4x K 47 1 ∈ reeLongRoot K 0 := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  have h := burnsideF4h_tits_centralZ_mem_reeLongRoot hK' 1
  rw [burnsideF4h_tits_centralZ_one] at h
  exact h

theorem burnsideF4h_tits_reeLongRoot_bound (hK : Nat.card K = 2) {x : ModGL Tag.F4 K}
    (hx : x ∈ reeLongRoot K 0) : x = 1 ∨ x = f4x K 44 1 * f4x K 47 1 := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  obtain ⟨v, hv⟩ := burnsideF4h_tits_reeLongRoot_coord hK' hx
  rcases burnsideF4h_tits_eq_zero_or_one hK v with rfl | rfl
  · left
    rw [hv, centralZ_zero]
    rfl
  · right
    rw [hv, burnsideF4h_tits_centralZ_one]

theorem burnsideF4h_tits_reeShortRoot_bound (hK : Nat.card K = 2) {x : ModGL Tag.F4 K}
    (hx : x ∈ reeShortRoot K 0) : x = 1 ∨ x = sylowL 0 K 1 := by
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  obtain ⟨s, hs⟩ := burnsideF4h_tits_reeShortRoot_coord hK' hx
  rcases burnsideF4h_tits_eq_zero_or_one hK s with rfl | rfl
  · left
    rw [hs, sylowA_zero, mul_one, mul_inv_cancel]
    rfl
  · right
    rw [hs]
    exact weyl_conj_sylowA_one (m := 0) (K := K)

end InvGamma

section InvMain

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin

set_option linter.unusedSectionVars false


theorem burnsideF4h_tits_inv_main (K : Type) [Field K] [Finite K] [CharP K 2]
    (scope : ReeScope K 0) {E : Type} [Group E] {core : Subgroup E} {degree : ℕ}
    (marking : DerivedCentralQuotient (reeGroup K 0) ≃* ↥core)
    (chart : ChF.NativeChart .Tits 2 degree core)
    (h4 : chart.longRoot = ((derivedImage (reeGroup K 0) (reeLongRoot K 0)).map
      marking.toMonoidHom).map core.subtype)
    (h5 : chart.shortRoot = ((derivedImage (reeGroup K 0) (reeShortRoot K 0)).map
      marking.toMonoidHom).map core.subtype) :
    ∃ long ∈ chart.longRoot, ∃ short ∈ chart.shortRoot, long ≠ 1 ∧ long * long = 1 ∧
      short ≠ 1 ∧ short * short = 1 ∧
      (¬ ∃ conjugator ∈ core, conjugator * long * conjugator⁻¹ = short) ∧
      (∀ element : E, chart.RootInvolution false element ↔
        element ∈ core ∧ ∃ conjugator ∈ core, conjugator * element * conjugator⁻¹ = long) ∧
      (∀ element : E, chart.RootInvolution true element ↔
        element ∈ core ∧ ∃ conjugator ∈ core, conjugator * element * conjugator⁻¹ = short) ∧
      (∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element ∨ chart.RootInvolution true element) := by
  haveI : CharP K F4.prime := ‹CharP K 2›
  have hK : Nat.card K = 2 := by simpa [ReeScope] using scope
  obtain ⟨Φ, hB, -, hP₂⟩ := burnsideF4h_tits_gammaEquiv hK
  obtain ⟨hz1, hz2⟩ := burnsideF4h_tits_f4x_inv hK
  obtain ⟨ht1, ht2⟩ := burnsideF4h_tits_sylowL_inv hK
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by simpa using hK
  obtain ⟨zT, hzT, tT, htT, hzT1, hzT2, htT1, htT2, hnc, hL, hS, hcls⟩ :=
    burnsideF4h_tits_inv_T (reeGroup K 0) (reeBorel K 0) (reeParabolic K 0 0) (reeLongRoot K 0)
      (reeShortRoot K 0) Φ hB hP₂ (f4x K 44 1 * f4x K 47 1) (sylowL 0 K 1)
      (burnsideF4h_tits_f4x_mem_reeGroup hK) (burnsideF4h_tits_sylowL_mem_reeGroup hK)
      (burnsideF4h_tits_f4x_mem_reeBorel hK)
      (fun u _ hu => burnsideF4h_tits_f4x_comm hK hu) hz1 hz2 ht1 ht2
      (fun g hg hgt => burnsideF4h_tits_centralizer_sylowL_le hK hg hgt)
      (burnsideF4h_tits_f4x_mem_reeLongRoot hK)
      (burnsideF4h_tits_sylowL_mem_reeShortRoot hK')
      (fun x _ hx => burnsideF4h_tits_reeLongRoot_bound hK hx)
      (fun x _ hx => burnsideF4h_tits_reeShortRoot_bound hK hx)
  exact burnsideF4h_tits_inv_chart marking chart _ _ h4 h5 zT tT hzT htT hzT1 hzT2 htT1 htT2
    hnc hL hS hcls

end InvMain

section


theorem burnsideF4h_inv_Tits (degree : ℕ) (E : Type) [Group E] (core : Subgroup E)
    (chart : ChF.NativeChart .Tits 2 degree core) :
    ∃ long ∈ chart.longRoot, ∃ short ∈ chart.shortRoot, long ≠ 1 ∧ long * long = 1 ∧
      short ≠ 1 ∧ short * short = 1 ∧
      (¬ ∃ conjugator ∈ core, conjugator * long * conjugator⁻¹ = short) ∧
      (∀ element : E, chart.RootInvolution false element ↔
        element ∈ core ∧ ∃ conjugator ∈ core, conjugator * element * conjugator⁻¹ = long) ∧
      (∀ element : E, chart.RootInvolution true element ↔
        element ∈ core ∧ ∃ conjugator ∈ core, conjugator * element * conjugator⁻¹ = short) ∧
      (∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element ∨ chart.RootInvolution true element) := by
  rcases chart.coordinates with
    ⟨c', hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨-, -, he, marking, -, -, -, h4, h5⟩⟩
  · exact absurd hk (by cases c' <;> decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · subst he
    letI := fK
    haveI := finK
    haveI := charK
    exact burnsideF4h_tits_inv_main K scope marking chart h4 h5

end

end PartBurnsideF4hTits

section PartBurnsideF4hTri

section Weyl

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def burnsideF4h_tri_wordUnit (τ : Tag) (K : Type) [Field K]
    (word : List (Fin τ.rank)) : ModGL τ K :=
  ((word.map fun i => weylElt τ K i 1).reverse).prod

theorem burnsideF4h_tri_coe_wordUnit (word : List (Fin τ.rank)) :
    (burnsideF4h_tri_wordUnit τ K word : Module.End K (RootModule τ K)) =
      weylWordOperator τ K word := by
  have h := map_list_prod (Units.coeHom (Module.End K (RootModule τ K)))
    ((word.map fun i => weylElt τ K i 1).reverse)
  simp only [Units.coeHom_apply, List.map_reverse, List.map_map] at h
  exact h

theorem burnsideF4h_tri_eq_wordUnit_iff (word : List (Fin τ.rank)) (g : ModGL τ K) :
    (g : Module.End K (RootModule τ K)) = weylWordOperator τ K word ↔
      g = burnsideF4h_tri_wordUnit τ K word := by
  rw [← burnsideF4h_tri_coe_wordUnit]
  exact ⟨fun h => Units.ext h, fun h => by rw [h]⟩

theorem burnsideF4h_tri_wordUnit_cons (i : Fin τ.rank) (word : List (Fin τ.rank)) :
    burnsideF4h_tri_wordUnit τ K (i :: word) =
      burnsideF4h_tri_wordUnit τ K word * weylElt τ K i 1 := by
  simp [burnsideF4h_tri_wordUnit]

theorem burnsideF4h_tri_absoluteTorus_eq : absoluteTorus τ K = torusGroup τ K := by
  unfold absoluteTorus torusGroup
  congr 1
  ext g
  constructor
  · rintro ⟨i, t, hg⟩
    exact ⟨(i, t), Units.ext hg.symm⟩
  · rintro ⟨⟨i, t⟩, rfl⟩
    exact ⟨i, t, rfl⟩

theorem burnsideF4h_tri_relativeWeyl_eq (word : List (Fin Tag.D4.rank)) :
    relativeWeyl Tag.D4 K word =
      Subgroup.closure {burnsideF4h_tri_wordUnit Tag.D4 K word} := by
  unfold relativeWeyl
  congr 1
  ext g
  exact burnsideF4h_tri_eq_wordUnit_iff word g

end Weyl

section RootGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {τ : Tag} {K : Type} [Field K]

theorem burnsideF4h_tri_conj_mem_rootSubgroup (word : List (Fin τ.rank)) :
    ∀ {β : Fin τ.rank → ℤ}, IsRoot τ β → ∀ {g : ModGL τ K}, g ∈ rootSubgroup τ K β →
      burnsideF4h_tri_wordUnit τ K word * g * (burnsideF4h_tri_wordUnit τ K word)⁻¹ ∈
        rootSubgroup τ K (word.foldl (fun root index => reflect τ index root) β) := by
  induction word with
  | nil =>
    intro β hβ g hg
    simpa [burnsideF4h_tri_wordUnit] using hg
  | cons i w ih =>
    intro β hβ g hg
    have h1 : weylElt τ K i 1 * g * (weylElt τ K i 1)⁻¹ ∈ rootSubgroup τ K (reflect τ i β) := by
      rw [← map_conj_weylElt_rootSubgroup K i hβ]
      exact ⟨g, hg, rfl⟩
    have h2 := ih (IsRoot.reflect i hβ) h1
    rw [List.foldl_cons, burnsideF4h_tri_wordUnit_cons]
    have e : burnsideF4h_tri_wordUnit τ K w * weylElt τ K i 1 * g *
        (burnsideF4h_tri_wordUnit τ K w * weylElt τ K i 1)⁻¹ =
        burnsideF4h_tri_wordUnit τ K w * (weylElt τ K i 1 * g * (weylElt τ K i 1)⁻¹) *
          (burnsideF4h_tri_wordUnit τ K w)⁻¹ := by
      group
    rw [e]
    exact h2

theorem burnsideF4h_tri_absoluteRoot_eq {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    absoluteRoot τ K α = rootSubgroup τ K α := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro e ⟨c, seed, word, actor, hfold, hactor, helem⟩
    have hact : actor = burnsideF4h_tri_wordUnit τ K word :=
      (burnsideF4h_tri_eq_wordUnit_iff word actor).1 hactor
    have he : e = burnsideF4h_tri_wordUnit τ K word * xUnit τ K seed c *
        (burnsideF4h_tri_wordUnit τ K word)⁻¹ := by
      refine Units.ext ?_
      rw [helem, hact]
      rfl
    have hx : xUnit τ K seed c ∈ rootSubgroup τ K (Pi.single seed 1) := by
      rw [← pinnedX_single]
      exact Subgroup.subset_closure ⟨c, rfl⟩
    have h := burnsideF4h_tri_conj_mem_rootSubgroup word (IsRoot.basis seed) hx
    rw [hfold] at h
    rw [he]
    exact h
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine Subgroup.subset_closure ⟨(pinnedData τ α).2.2 • c, (pinnedData τ α).1,
      (pinnedData τ α).2.1.map τ.idx, pinnedWeyl τ K α, ?_, ?_, ?_⟩
    · rw [List.foldl_map]
      exact foldl_reflect_pinnedData hα
    · rw [← burnsideF4h_tri_coe_wordUnit]
      simp [pinnedWeyl, burnsideF4h_tri_wordUnit, List.map_map, Function.comp_def]
    · rfl

theorem burnsideF4h_tri_absoluteBorel_eq : absoluteBorel τ K = borelGroup τ K := by
  have hpos : absolutePositive τ K = posUnipotent τ K := by
    unfold absolutePositive posUnipotent rootSpan
    refine iSup_congr fun α => iSup_congr fun hα => ?_
    exact burnsideF4h_tri_absoluteRoot_eq hα.1
  unfold absoluteBorel borelGroup
  rw [hpos, burnsideF4h_tri_absoluteTorus_eq, sup_comm]

end RootGroups

section Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

local instance burnsideF4h_tri_neZeroRankD4 : NeZero Tag.D4.rank := ⟨by decide⟩

local instance burnsideF4h_tri_neZeroRankD4tag : NeZero TwistTag.D4.tag.rank := ⟨by decide⟩

theorem burnsideF4h_tri_orbitWord_zero :
    TwistTag.D4.orbitWord (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) =
      ([0, 1, 3] : List (Fin TwistTag.D4.tag.rank)) := by
  rfl

theorem burnsideF4h_tri_orbitWord_one :
    TwistTag.D4.orbitWord (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) =
      ([2] : List (Fin TwistTag.D4.tag.rank)) := by
  rfl

section Reps

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def burnsideF4h_tri_orbitRep (a : Fin TwistTag.D4.foldedTag.rank) :
    ModGL TwistTag.D4.tag K :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a)

theorem burnsideF4h_tri_wordUnit_central :
    burnsideF4h_tri_wordUnit Tag.D4 K [2] = burnsideF4h_tri_orbitRep K ⟨1, by decide⟩ := by
  unfold burnsideF4h_tri_orbitRep
  rw [canonicalRep_orbitReflection, burnsideF4h_tri_orbitWord_one, List.map_singleton,
    List.prod_singleton]
  simp only [burnsideF4h_tri_wordUnit, List.map_singleton, List.reverse_singleton,
    List.prod_singleton]
  try rfl

end Reps

section Commute

variable {K : Type} [Field K]

theorem burnsideF4h_tri_commute_outer (l j : Fin TwistTag.D4.tag.rank)
    (hl : l ∈ TwistTag.D4.orbit (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank))
    (hj : j ∈ TwistTag.D4.orbit (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank))
    (hlj : l ≠ j) :
    Commute (weylElt TwistTag.D4.tag K l 1) (weylElt TwistTag.D4.tag K j 1) :=
  commute_weylElt_weylElt (t := TwistTag.D4) K hl hj hlj 1 1

theorem burnsideF4h_tri_wordUnit_outer :
    burnsideF4h_tri_wordUnit Tag.D4 K [0, 1, 3] = burnsideF4h_tri_orbitRep K ⟨0, by decide⟩ := by
  unfold burnsideF4h_tri_orbitRep
  rw [canonicalRep_orbitReflection, burnsideF4h_tri_orbitWord_zero]
  have h01 : Commute (weylElt TwistTag.D4.tag K 0 1) (weylElt TwistTag.D4.tag K 1 1) :=
    burnsideF4h_tri_commute_outer 0 1 (by decide) (by decide) (by decide)
  have h03 : Commute (weylElt TwistTag.D4.tag K 0 1) (weylElt TwistTag.D4.tag K 3 1) :=
    burnsideF4h_tri_commute_outer 0 3 (by decide) (by decide) (by decide)
  have h13 : Commute (weylElt TwistTag.D4.tag K 1 1) (weylElt TwistTag.D4.tag K 3 1) :=
    burnsideF4h_tri_commute_outer 1 3 (by decide) (by decide) (by decide)
  simp only [burnsideF4h_tri_wordUnit, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, List.singleton_append,
    List.cons_append, mul_one]
  change weylElt TwistTag.D4.tag K 3 1 * (weylElt TwistTag.D4.tag K 1 1 *
      weylElt TwistTag.D4.tag K 0 1) = weylElt TwistTag.D4.tag K 0 1 *
        (weylElt TwistTag.D4.tag K 1 1 * weylElt TwistTag.D4.tag K 3 1)
  calc weylElt TwistTag.D4.tag K 3 1 * (weylElt TwistTag.D4.tag K 1 1 *
        weylElt TwistTag.D4.tag K 0 1)
      = weylElt TwistTag.D4.tag K 3 1 * (weylElt TwistTag.D4.tag K 0 1 *
          weylElt TwistTag.D4.tag K 1 1) := by
        rw [h01.eq]
    _ = weylElt TwistTag.D4.tag K 0 1 * (weylElt TwistTag.D4.tag K 3 1 *
          weylElt TwistTag.D4.tag K 1 1) := by
        rw [← mul_assoc, ← mul_assoc, h03.eq.symm]
    _ = weylElt TwistTag.D4.tag K 0 1 * (weylElt TwistTag.D4.tag K 1 1 *
          weylElt TwistTag.D4.tag K 3 1) := by
        rw [h13.eq]

end Commute

section Borel

variable {K : Type} [Field K]

theorem burnsideF4h_tri_trialityBorel_eq (σ : K →+* K)
    (hΓ : twistedFixedGroup TwistTag.D4 K σ = graphFixedRootGroup TwistTag.D4 K σ) :
    trialityBorel K σ = graphFixedRootBorel TwistTag.D4 K σ := by
  ext x
  simp only [trialityBorel, graphFixedRootBorel, graphFixedBorel, Subgroup.mem_inf]
  rw [burnsideF4h_tri_absoluteBorel_eq, hΓ]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h2, h1⟩, h1⟩
  · rintro ⟨⟨h2, h1⟩, -⟩
    exact ⟨h1, h2⟩

end Borel

section Parabolics

variable {K : Type} [Field K]

theorem burnsideF4h_tri_inf_relativeWeyl_outer (σ : K →+* K)
    (hΓ : twistedFixedGroup TwistTag.D4 K σ = graphFixedRootGroup TwistTag.D4 K σ) :
    twistedFixedGroup TwistTag.D4 K σ ⊓ relativeWeyl Tag.D4 K [0, 1, 3] =
      Subgroup.closure {burnsideF4h_tri_orbitRep K ⟨0, by decide⟩} := by
  have hmem : burnsideF4h_tri_orbitRep K ⟨0, by decide⟩ ∈ twistedFixedGroup TwistTag.D4 K σ := by
    rw [hΓ]
    exact canonicalRep_orbitReflection_mem_graphFixedRootGroup (σ := σ) ⟨0, by decide⟩
  rw [burnsideF4h_tri_relativeWeyl_eq, burnsideF4h_tri_wordUnit_outer]
  exact inf_eq_right.2 ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hmem))

theorem burnsideF4h_tri_inf_relativeWeyl_central (σ : K →+* K)
    (hΓ : twistedFixedGroup TwistTag.D4 K σ = graphFixedRootGroup TwistTag.D4 K σ) :
    twistedFixedGroup TwistTag.D4 K σ ⊓ relativeWeyl Tag.D4 K [2] =
      Subgroup.closure {burnsideF4h_tri_orbitRep K ⟨1, by decide⟩} := by
  have hmem : burnsideF4h_tri_orbitRep K ⟨1, by decide⟩ ∈ twistedFixedGroup TwistTag.D4 K σ := by
    rw [hΓ]
    exact canonicalRep_orbitReflection_mem_graphFixedRootGroup (σ := σ) ⟨1, by decide⟩
  rw [burnsideF4h_tri_relativeWeyl_eq, burnsideF4h_tri_wordUnit_central]
  exact inf_eq_right.2 ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hmem))

theorem burnsideF4h_tri_trialityParabolic_zero (σ : K →+* K)
    (hΓ : twistedFixedGroup TwistTag.D4 K σ = graphFixedRootGroup TwistTag.D4 K σ) :
    trialityParabolic K σ 0 =
      graphFixedParabolic TwistTag.D4 K σ
        (({⟨0, by decide⟩} : Set (Fin TwistTag.D4.foldedTag.rank))) := by
  have hB := burnsideF4h_tri_trialityBorel_eq σ hΓ
  have hW := burnsideF4h_tri_inf_relativeWeyl_outer σ hΓ
  have h := congrArg₂ (· ⊔ ·) hB hW
  unfold graphFixedParabolic
  rw [Set.image_singleton]
  exact h

theorem burnsideF4h_tri_trialityParabolic_one (σ : K →+* K)
    (hΓ : twistedFixedGroup TwistTag.D4 K σ = graphFixedRootGroup TwistTag.D4 K σ) :
    trialityParabolic K σ 1 =
      graphFixedParabolic TwistTag.D4 K σ
        (({⟨1, by decide⟩} : Set (Fin TwistTag.D4.foldedTag.rank))) := by
  have hB := burnsideF4h_tri_trialityBorel_eq σ hΓ
  have hW := burnsideF4h_tri_inf_relativeWeyl_central σ hΓ
  have h := congrArg₂ (· ⊔ ·) hB hW
  unfold graphFixedParabolic
  rw [Set.image_singleton]
  exact h

end Parabolics

end Triality

section Quotient

open CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots

variable {M : Type} [Group M]

theorem burnsideF4h_tri_exists_derivedEquiv (Γ C : Subgroup M) (hD : ⁅Γ, Γ⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) :
    ∃ e : DerivedCentralQuotient Γ ≃* ↥C,
      ∀ x : ↥⁅Γ, Γ⁆, ((e (QuotientGroup.mk x) : ↥C) : M) = (x : M) := by
  subst hD
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot, fun x => rfl⟩

theorem burnsideF4h_tri_map_derivedImage (Γ C P : Subgroup M) (hD : ⁅Γ, Γ⁆ = C)
    (e : DerivedCentralQuotient Γ ≃* ↥C)
    (he : ∀ x : ↥⁅Γ, Γ⁆, ((e (QuotientGroup.mk x) : ↥C) : M) = (x : M)) :
    (derivedImage Γ P).map e.toMonoidHom = P.subgroupOf C := by
  ext y
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hxP : (x : M) ∈ P := hx
    exact (he x).symm ▸ hxP
  · intro hy
    have hyP : (y : M) ∈ P := hy
    have hyD : (y : M) ∈ ⁅Γ, Γ⁆ := hD ▸ y.2
    refine ⟨QuotientGroup.mk ⟨(y : M), hyD⟩, ⟨⟨(y : M), hyD⟩, hyP, rfl⟩, ?_⟩
    exact Subtype.ext (he ⟨(y : M), hyD⟩)

end Quotient

section Scope

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {K : Type} [Field K] [Finite K]

theorem burnsideF4h_tri_twisted_eq {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (hK : Nat.card K = (p ^ d) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ d)) :
    twistedFixedGroup TwistTag.D4 K σ.toRingHom =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hchar : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := d * 3) (by omega) (by rw [hK, pow_mul])
  have hpar : ringChar K = 2 ∨ ∃ n, Odd n ∧ ∀ c, σ c = c ^ n := by
    rcases hp.eq_two_or_odd' with h2 | hodd
    · exact Or.inl (by rw [ringChar.eq K p, h2])
    · exact Or.inr ⟨p ^ d, hodd.pow, hσ⟩
  exact twistedFixedGroup_eq_graphFixedRootGroup_triality σ hσ3 hpar

theorem burnsideF4h_tri_commutator_eq {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (hK : Nat.card K = (p ^ d) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ d)) :
    ⁅graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom⁆ =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  by_cases h2 : ringChar K = 2
  · have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
    have hq2 : 2 ≤ p ^ d := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ (p ^ d) ^ 3 := Nat.pow_le_pow_left hq2 3
    exact commutator_graphFixedRootGroup_triality_char_two h2 σ hσ3 h4
  · exact (odd_diagram_fixed_root_group_perfect TwistTag.D4 K h2 σ).1

theorem burnsideF4h_tri_exists_equiv {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (hK : Nat.card K = (p ^ d) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ d)) :
    ∃ e : DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ∀ x : ↥⁅twistedFixedGroup TwistTag.D4 K σ.toRingHom,
          twistedFixedGroup TwistTag.D4 K σ.toRingHom⁆,
        ((e (QuotientGroup.mk x) : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          ModGL TwistTag.D4.tag K) = (x : ModGL TwistTag.D4.tag K) := by
  have hΓ := burnsideF4h_tri_twisted_eq hp hd hK σ hσ
  have hD : ⁅twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      twistedFixedGroup TwistTag.D4 K σ.toRingHom⁆ =
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [hΓ]
    exact burnsideF4h_tri_commutator_eq hp hd hK σ hσ
  exact burnsideF4h_tri_exists_derivedEquiv _ _ hD
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)

end Scope

section Lattice

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem burnsideF4h_tri_fin_cases (a : Fin TwistTag.D4.foldedTag.rank) :
    a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩ := by
  obtain ⟨n, hn⟩ := a
  have hn' : n < 2 := hn
  interval_cases n
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem burnsideF4h_tri_zero_ne_one :
    (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ≠ ⟨1, by decide⟩ := by
  intro h
  exact absurd (congrArg Fin.val h) (by decide)

theorem burnsideF4h_tri_set_cases (J : Set (Fin TwistTag.D4.foldedTag.rank)) :
    J = ∅ ∨ J = {⟨0, by decide⟩} ∨ J = {⟨1, by decide⟩} ∨ J = Set.univ := by
  have h01 := burnsideF4h_tri_zero_ne_one
  by_cases h0 : (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ∈ J <;>
    by_cases h1 : (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ∈ J
  · refine Or.inr (Or.inr (Or.inr (Set.eq_univ_of_forall fun a => ?_)))
    rcases burnsideF4h_tri_fin_cases a with rfl | rfl
    · exact h0
    · exact h1
  · refine Or.inr (Or.inl (Set.ext fun a => ?_))
    rw [Set.mem_singleton_iff]
    rcases burnsideF4h_tri_fin_cases a with rfl | rfl
    · exact iff_of_true h0 rfl
    · exact iff_of_false h1 (Ne.symm h01)
  · refine Or.inr (Or.inr (Or.inl (Set.ext fun a => ?_)))
    rw [Set.mem_singleton_iff]
    rcases burnsideF4h_tri_fin_cases a with rfl | rfl
    · exact iff_of_false h0 h01
    · exact iff_of_true h1 rfl
  · refine Or.inl (Set.eq_empty_of_forall_notMem fun a ha => ?_)
    rcases burnsideF4h_tri_fin_cases a with rfl | rfl
    · exact h0 ha
    · exact h1 ha

variable {K : Type} [Field K]

theorem burnsideF4h_tri_parabolic_univ {t : TwistTag} (σ : K →+* K)
    (hσ : Function.Surjective σ) :
    graphFixedParabolic t K σ Set.univ = graphFixedRootGroup t K σ := by
  refine le_antisymm (graphFixedParabolic_le t K σ Set.univ) ?_
  rw [graphFixedRootGroup_eq_sup_closure hσ, graphFixedParabolic, Set.image_univ]

theorem burnsideF4h_tri_parabolic_inf (σ : K →+* K) (hσ : Function.Surjective σ) :
    graphFixedParabolic TwistTag.D4 K σ {⟨0, by decide⟩} ⊓
        graphFixedParabolic TwistTag.D4 K σ {⟨1, by decide⟩} =
      graphFixedRootBorel TwistTag.D4 K σ := by
  have hB : graphFixedRootBorel TwistTag.D4 K σ ≤
      graphFixedParabolic TwistTag.D4 K σ {⟨0, by decide⟩} ⊓
        graphFixedParabolic TwistTag.D4 K σ {⟨1, by decide⟩} :=
    le_inf (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
      (graphFixedRootBorel_le_graphFixedParabolic _ _ _ _)
  have hA : graphFixedParabolic TwistTag.D4 K σ {⟨0, by decide⟩} ⊓
        graphFixedParabolic TwistTag.D4 K σ {⟨1, by decide⟩} ≤
      graphFixedRootGroup TwistTag.D4 K σ :=
    inf_le_left.trans (graphFixedParabolic_le _ _ _ _)
  have hAJ := eq_graphFixedParabolic_of_le hσ hB hA
  set J := {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈
    graphFixedParabolic TwistTag.D4 K σ {⟨0, by decide⟩} ⊓
      graphFixedParabolic TwistTag.D4 K σ {⟨1, by decide⟩}} with hJdef
  have h0 : J ⊆ {⟨0, by decide⟩} :=
    (graphFixedParabolic_le_iff hσ).1 (by rw [← hAJ]; exact inf_le_left)
  have h1 : J ⊆ {⟨1, by decide⟩} :=
    (graphFixedParabolic_le_iff hσ).1 (by rw [← hAJ]; exact inf_le_right)
  have hJ : J = ∅ := Set.eq_empty_of_forall_notMem fun a ha =>
    burnsideF4h_tri_zero_ne_one (((Set.mem_singleton_iff.1 (h0 ha)).symm).trans
      (Set.mem_singleton_iff.1 (h1 ha)))
  rw [hAJ, hJ, graphFixedParabolic_empty]

theorem burnsideF4h_tri_parabolic_maximal (σ : K →+* K) (hσ : Function.Surjective σ)
    (a : Fin TwistTag.D4.foldedTag.rank) :
    graphFixedRootBorel TwistTag.D4 K σ ≤ graphFixedParabolic TwistTag.D4 K σ {a} ∧
      graphFixedParabolic TwistTag.D4 K σ {a} ≤ graphFixedRootGroup TwistTag.D4 K σ ∧
      graphFixedParabolic TwistTag.D4 K σ {a} ≠ graphFixedRootGroup TwistTag.D4 K σ ∧
      ∀ R : Subgroup (ModGL TwistTag.D4.tag K), graphFixedParabolic TwistTag.D4 K σ {a} < R →
        R ≤ graphFixedRootGroup TwistTag.D4 K σ → R = graphFixedRootGroup TwistTag.D4 K σ := by
  have hne_univ : ({a} : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ := by
    intro h
    have hb : ∃ b : Fin TwistTag.D4.foldedTag.rank, b ≠ a := by
      rcases burnsideF4h_tri_fin_cases a with rfl | rfl
      · exact ⟨⟨1, by decide⟩, burnsideF4h_tri_zero_ne_one.symm⟩
      · exact ⟨⟨0, by decide⟩, burnsideF4h_tri_zero_ne_one⟩
    obtain ⟨b, hb⟩ := hb
    have : b ∈ ({a} : Set (Fin TwistTag.D4.foldedTag.rank)) := by rw [h]; exact Set.mem_univ b
    exact hb (Set.mem_singleton_iff.1 this)
  refine ⟨graphFixedRootBorel_le_graphFixedParabolic _ _ _ _, graphFixedParabolic_le _ _ _ _,
    fun h => hne_univ (graphFixedParabolic_injective hσ
      (h.trans (burnsideF4h_tri_parabolic_univ σ hσ).symm)), fun R hR hRC => ?_⟩
  have hRJ := eq_graphFixedParabolic_of_le hσ
    ((graphFixedRootBorel_le_graphFixedParabolic _ _ _ _).trans hR.le) hRC
  set J := {b | canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection b) ∈ R}
    with hJdef
  have haJ : ({a} : Set (Fin TwistTag.D4.foldedTag.rank)) ⊆ J :=
    (graphFixedParabolic_le_iff hσ).1 (by rw [← hRJ]; exact hR.le)
  have hJa : J ≠ {a} := fun h => hR.ne (by rw [hRJ, h])
  rcases burnsideF4h_tri_set_cases J with h | h | h | h
  · exact absurd (haJ (Set.mem_singleton a)) (by rw [h]; exact Set.notMem_empty a)
  · have : a = ⟨0, by decide⟩ := Set.mem_singleton_iff.1 (h ▸ haJ (Set.mem_singleton a))
    exact absurd (h.trans (by rw [this])) hJa
  · have : a = ⟨1, by decide⟩ := Set.mem_singleton_iff.1 (h ▸ haJ (Set.mem_singleton a))
    exact absurd (h.trans (by rw [this])) hJa
  · rw [hRJ, h, burnsideF4h_tri_parabolic_univ σ hσ]

theorem burnsideF4h_tri_isLieParabolics_graphFixed [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (σ : K →+* K) (hσ : Function.Surjective σ) :
    ChF.IsLieParabolics p (graphFixedRootGroup TwistTag.D4 K σ)
      (graphFixedRootBorel TwistTag.D4 K σ)
      (graphFixedParabolic TwistTag.D4 K σ {⟨0, by decide⟩})
      (graphFixedParabolic TwistTag.D4 K σ {⟨1, by decide⟩}) := by
  refine ⟨⟨graphFixedPosUnipotent TwistTag.D4 K σ,
    ⟨graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _,
      (isPGroup_posUnipotent p TwistTag.D4.tag).to_le
        (inf_le_left : graphFixedPosUnipotent TwistTag.D4 K σ ≤ _),
      not_dvd_index_graphFixedPosUnipotent p hσ⟩,
    (graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ).symm⟩, ?_,
    burnsideF4h_tri_parabolic_inf σ hσ, fun Q => ⟨?_, ?_⟩⟩
  · intro h
    exact burnsideF4h_tri_zero_ne_one
      (Set.singleton_eq_singleton_iff.1 (graphFixedParabolic_injective hσ h))
  · rintro ⟨hBQ, hQC, hQne, hQmax⟩
    have hQJ := eq_graphFixedParabolic_of_le hσ hBQ hQC
    rcases burnsideF4h_tri_set_cases {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection a) ∈ Q} with h | h | h | h
    · exfalso
      have hQB : Q = graphFixedRootBorel TwistTag.D4 K σ := by
        rw [hQJ, h, graphFixedParabolic_empty]
      obtain ⟨-, hPC, hPne, -⟩ := burnsideF4h_tri_parabolic_maximal σ hσ ⟨0, by decide⟩
      have hlt : Q < graphFixedParabolic TwistTag.D4 K σ {⟨0, by decide⟩} := by
        rw [hQB]
        exact graphFixedRootBorel_lt_graphFixedParabolic hσ (Set.singleton_nonempty _)
      exact hPne (hQmax _ hlt hPC)
    · exact Or.inl (by rw [hQJ, h])
    · exact Or.inr (by rw [hQJ, h])
    · exact absurd (by rw [hQJ, h, burnsideF4h_tri_parabolic_univ σ hσ]) hQne
  · rintro (rfl | rfl)
    · exact burnsideF4h_tri_parabolic_maximal σ hσ _
    · exact burnsideF4h_tri_parabolic_maximal σ hσ _

theorem burnsideF4h_tri_relIndex_parabolic [Finite K] {t : TwistTag} (σ : K →+* K)
    (hσ : Function.Surjective σ) (a : Fin t.foldedTag.rank) :
    (graphFixedRootBorel t K σ).relIndex (graphFixedParabolic t K σ {a}) =
      Nat.card (orbitField t K σ a) + 1 := by
  classical
  have : Finite (ModGL t.tag K) := finite_modGL
  set B := graphFixedRootBorel t K σ with hBdef
  set P := graphFixedParabolic t K σ {a} with hPdef
  set D := graphFixedRootBruhatCell t K σ (t.orbitReflection a) with hDdef
  have hB1 : (B : Set (ModGL t.tag K)) = graphFixedRootBruhatCell t K σ 1 := by
    ext x
    rw [mem_graphFixedRootBruhatCell, canonicalRep_one]
    constructor
    · intro hx
      exact ⟨x, hx, 1, one_mem _, by rw [mul_one, mul_one]⟩
    · rintro ⟨b, hb, b', hb', rfl⟩
      rw [mul_one]
      exact mul_mem hb hb'
  have hcells : (P : Set (ModGL t.tag K)) = (B : Set (ModGL t.tag K)) ∪ D := by
    rw [hPdef, graphFixedParabolic_eq_cells hσ, hB1]
    ext x
    simp only [mem_graphFixedParabolicCells, Set.mem_union]
    constructor
    · rintro ⟨w, hw, hx⟩
      rcases mem_foldedParabolicWeylGroup_singleton hw with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact ⟨1, one_mem _, hx⟩
      · exact ⟨t.orbitReflection a, Subgroup.subset_closure ⟨a, rfl, rfl⟩, hx⟩
  have hdisj : Disjoint (B : Set (ModGL t.tag K)) D := by
    rw [hB1]
    exact disjoint_graphFixedRootBruhatCell (t.orbitReflection_ne_one a).symm
  have hU : (graphFixedInversionUnipotent t K σ (t.orbitReflection a) :
      Set (ModGL t.tag K)) =
        Set.range fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K) := by
    rw [← coe_rootSpan_simpleOrbitRoots_inf a, ← inversionSet_orbitReflection a]
    rfl
  have hinj : Function.Injective
      fun c : orbitField t K σ a => (orbitX t K σ a c : ModGL t.tag K) :=
    fun c c' h => orbitX_injective σ a (Subtype.ext h)
  have hcardU : Nat.card (graphFixedInversionUnipotent t K σ (t.orbitReflection a) :
      Set (ModGL t.tag K)) = Nat.card (orbitField t K σ a) := by
    rw [hU]
    exact Nat.card_range_of_injective hinj
  have hcardD : Nat.card D = Nat.card B * Nat.card (orbitField t K σ a) := by
    have hbij := bijOn_graphFixedRootBruhatCell (K := K) (σ := σ) hσ (t.orbitReflection_mem a)
    rw [← Nat.card_congr (Set.BijOn.equiv _ hbij), Nat.card_congr (Equiv.Set.prod _ _),
      Nat.card_prod, hcardU]
    rfl
  have hcardP : Nat.card P = Nat.card B + Nat.card B * Nat.card (orbitField t K σ a) := by
    have h1 : Nat.card P = (P : Set (ModGL t.tag K)).ncard := Nat.card_coe_set_eq _
    rw [h1, hcells, Set.ncard_union_eq hdisj, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
      hcardD]
    rfl
  have hBP : B ≤ P := graphFixedRootBorel_le_graphFixedParabolic t K σ {a}
  have hmul := Subgroup.relIndex_mul_card (H := B) (K := P)
  rw [inf_eq_left.2 hBP, hcardP] at hmul
  have hpos : 0 < Nat.card B := Nat.card_pos
  have key : B.relIndex P * Nat.card B = (Nat.card (orbitField t K σ a) + 1) * Nat.card B := by
    rw [hmul]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

end Lattice

section LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

local instance burnsideF4h_tri_neZeroRankD4' : NeZero Tag.D4.rank := ⟨by decide⟩

@[expose] def burnsideF4h_tri_theta : Fin Tag.D4.rank → ℤ :=
  (![1, 1, 2, 1] : Fin 4 → ℤ)

theorem burnsideF4h_tri_isRoot_highest :
    IsRoot Tag.D4 burnsideF4h_tri_theta :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨22, by decide, by decide⟩

theorem burnsideF4h_tri_height_le_five
    {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) : height α ≤ 5 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range Tag.D4.rootCertificate.roots.length).all fun k =>
      decide (height (Tag.D4.rootCertificate.root k) ≤ 5) := by decide
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

variable {K : Type} [Field K]

theorem burnsideF4h_tri_rootSubgroup_le_centralizer_highest {β : Fin Tag.D4.rank → ℤ}
    (hβ : IsRoot Tag.D4 β) (hβp : 0 < height β) (hβθ : β ≠ burnsideF4h_tri_theta) :
    rootSubgroup Tag.D4 K β ≤
      Subgroup.centralizer
        (rootSubgroup Tag.D4 K burnsideF4h_tri_theta : Set (ModGL Tag.D4 K)) := by
  have hc := commutator_rootSubgroup_le K hβ burnsideF4h_tri_isRoot_highest hβp
    (by decide) hβθ
  have hbot : (⨆ (γ : Fin Tag.D4.rank → ℤ) (_ : IsRoot Tag.D4 γ ∧
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • β + b • burnsideF4h_tri_theta),
        rootSubgroup Tag.D4 K γ) = ⊥ := by
    refine iSup₂_eq_bot.2 ?_
    rintro γ ⟨hγ, a, b, ha, hb, rfl⟩
    exfalso
    have h1 := burnsideF4h_tri_height_le_five hγ
    rw [height_nsmul_add_nsmul] at h1
    have hθ : height (τ := Tag.D4) burnsideF4h_tri_theta = 5 := by decide
    rw [hθ] at h1
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith
  rw [hbot] at hc
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (le_bot_iff.1 hc)

theorem burnsideF4h_tri_borelGroup_le_normalizer_highest :
    borelGroup Tag.D4 K ≤
      Subgroup.normalizer (rootSubgroup Tag.D4 K burnsideF4h_tri_theta : Set (ModGL Tag.D4 K)) := by
  unfold borelGroup
  refine sup_le (torusGroup_le_normalizer_rootSubgroup burnsideF4h_tri_isRoot_highest) ?_
  unfold posUnipotent rootSpan
  refine iSup₂_le fun β hβ => ?_
  by_cases hβθ : β = burnsideF4h_tri_theta
  · subst hβθ
    exact Subgroup.le_normalizer
  · exact (burnsideF4h_tri_rootSubgroup_le_centralizer_highest hβ.1 hβ.2 hβθ).trans
      (Subgroup.centralizer_le_normalizer _)

theorem burnsideF4h_tri_map_conj_wordUnit {τ : Tag} (word : List (Fin τ.rank)) :
    ∀ {β : Fin τ.rank → ℤ}, IsRoot τ β →
      (rootSubgroup τ K β).map (MulAut.conj (burnsideF4h_tri_wordUnit τ K word)).toMonoidHom =
        rootSubgroup τ K (word.foldl (fun root index => reflect τ index root) β) := by
  induction word with
  | nil =>
    intro β _
    ext g
    simp [burnsideF4h_tri_wordUnit]
  | cons i w ih =>
    intro β hβ
    rw [burnsideF4h_tri_wordUnit_cons, map_conj_mul, map_conj_weylElt_rootSubgroup K i hβ,
      ih (IsRoot.reflect i hβ), List.foldl_cons]

theorem burnsideF4h_tri_wordUnit_append {τ : Tag} (w₁ w₂ : List (Fin τ.rank)) :
    burnsideF4h_tri_wordUnit τ K (w₁ ++ w₂) =
      burnsideF4h_tri_wordUnit τ K w₂ * burnsideF4h_tri_wordUnit τ K w₁ := by
  simp [burnsideF4h_tri_wordUnit, List.map_append, List.reverse_append, List.prod_append]

theorem burnsideF4h_tri_fixedWeylConjugate_eq {τ : Tag} (model : Subgroup (ModGL τ K))
    (word : List (Fin τ.rank)) (root : Subgroup (ModGL τ K))
    (hn : burnsideF4h_tri_wordUnit τ K word ∈ model) :
    fixedWeylConjugate τ K model word root =
      root.map (MulAut.conj (burnsideF4h_tri_wordUnit τ K word)).toMonoidHom := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro e ⟨actor, -, hactor, g, hg, rfl⟩
    rw [(burnsideF4h_tri_eq_wordUnit_iff word actor).1 hactor]
    exact ⟨g, hg, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.subset_closure ⟨_, hn, burnsideF4h_tri_coe_wordUnit word, g, hg, rfl⟩

theorem burnsideF4h_tri_wordUnit_long_mem (σ : K →+* K) :
    burnsideF4h_tri_wordUnit Tag.D4 K [0, 1, 3, 2] ∈ twistedFixedGroup TwistTag.D4 K σ := by
  rw [show ([0, 1, 3, 2] : List (Fin Tag.D4.rank)) = [0, 1, 3] ++ [2] from rfl,
    burnsideF4h_tri_wordUnit_append, burnsideF4h_tri_wordUnit_outer,
    burnsideF4h_tri_wordUnit_central]
  exact mul_mem
    (graphFixedRootGroup_le TwistTag.D4 K σ
      (canonicalRep_orbitReflection_mem_graphFixedRootGroup (σ := σ) _))
    (graphFixedRootGroup_le TwistTag.D4 K σ
      (canonicalRep_orbitReflection_mem_graphFixedRootGroup (σ := σ) _))

theorem burnsideF4h_tri_trialityLongRoot_eq (σ : K →+* K) :
    trialityLongRoot K σ =
      twistedFixedGroup TwistTag.D4 K σ ⊓ rootSubgroup Tag.D4 K burnsideF4h_tri_theta := by
  have hn := burnsideF4h_tri_wordUnit_long_mem (K := K) σ
  have hpos : trialityPositiveRoot K σ 1 =
      twistedFixedGroup TwistTag.D4 K σ ⊓ rootSubgroup Tag.D4 K (Pi.single 2 1) := by
    unfold trialityPositiveRoot trialitySingletonRoot
    rw [if_neg (by decide)]
    have hseed : trialitySeed 1 = (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) := by decide
    rw [hseed, burnsideF4h_tri_absoluteRoot_eq (IsRoot.basis 2)]
    rfl
  have hfold : List.foldl (fun root index => reflect Tag.D4 index root)
      (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) [0, 1, 3, 2] = burnsideF4h_tri_theta := by decide
  have hU := burnsideF4h_tri_map_conj_wordUnit (K := K) (τ := Tag.D4) [0, 1, 3, 2]
    (IsRoot.basis (2 : Fin Tag.D4.rank))
  rw [hfold] at hU
  have hΓ := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hn)
  unfold trialityLongRoot
  rw [burnsideF4h_tri_fixedWeylConjugate_eq (τ := Tag.D4) (twistedFixedGroup TwistTag.D4 K σ)
      [0, 1, 3, 2] _ hn]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hpos] at hy
    obtain ⟨hyΓ, hyU⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨(hΓ y).1 hyΓ, ?_⟩
    rw [← hU]
    exact ⟨y, hyU, rfl⟩
  · intro hx
    obtain ⟨hxΓ, hxU⟩ := Subgroup.mem_inf.1 hx
    rw [← hU] at hxU
    obtain ⟨y, hyU, rfl⟩ := hxU
    refine ⟨y, ?_, rfl⟩
    rw [hpos]
    exact Subgroup.mem_inf.2 ⟨(hΓ y).2 hxΓ, hyU⟩

theorem burnsideF4h_tri_mem_normalizer_inf {G : Type*} [Group G] {A C : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hC : x ∈ Subgroup.normalizer (C : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hC ⊢
  intro g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA g, hC g]

theorem burnsideF4h_tri_parabolic_le_normalizer_longRoot (σ : K →+* K) :
    trialityParabolic K σ 0 ≤
      Subgroup.normalizer (trialityLongRoot K σ : Set (ModGL Tag.D4 K)) := by
  rw [burnsideF4h_tri_trialityLongRoot_eq]
  unfold trialityParabolic trialityBorel
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨hxΓ, hxB⟩ := Subgroup.mem_inf.1 hx
    rw [burnsideF4h_tri_absoluteBorel_eq] at hxB
    exact burnsideF4h_tri_mem_normalizer_inf (Subgroup.le_normalizer hxΓ)
      (burnsideF4h_tri_borelGroup_le_normalizer_highest hxB)
  · obtain ⟨hxΓ, hxW⟩ := Subgroup.mem_inf.1 hx
    rw [if_pos rfl, burnsideF4h_tri_relativeWeyl_eq] at hxW
    have hnU : burnsideF4h_tri_wordUnit Tag.D4 K [0, 1, 3] ∈
        Subgroup.normalizer
          (rootSubgroup Tag.D4 K burnsideF4h_tri_theta : Set (ModGL Tag.D4 K)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hfold : List.foldl (fun root index => reflect Tag.D4 index root)
          burnsideF4h_tri_theta [0, 1, 3] = burnsideF4h_tri_theta := by decide
      have h := burnsideF4h_tri_map_conj_wordUnit (K := K) (τ := Tag.D4) [0, 1, 3]
        burnsideF4h_tri_isRoot_highest
      rw [hfold] at h
      exact h
    exact burnsideF4h_tri_mem_normalizer_inf (Subgroup.le_normalizer hxΓ)
      ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hnU) hxW)

end LongRoot


section Transport

theorem burnsideF4h_tri_isLieParabolics_of_map {E M : Type} [Group E] [Group M] (φ : M →* E)
    (hφ : Function.Injective φ) {p : ℕ} {B P₁ P₂ : Subgroup M}
    (h : ChF.IsLieParabolics p φ.range (B.map φ) (P₁.map φ) (P₂.map φ)) :
    ChF.IsLieParabolics p (⊤ : Subgroup M) B P₁ P₂ := by
  obtain ⟨⟨S', ⟨hS'le, hS'p, hS'idx⟩, hB⟩, hne, hinf, hmax⟩ := h
  have hS'eq : (S'.comap φ).map φ = S' := Subgroup.map_comap_eq_self hS'le
  have hrange : (⊤ : Subgroup M).map φ = φ.range := (MonoidHom.range_eq_map φ).symm
  refine ⟨⟨S'.comap φ, ⟨le_top, hS'p.comap_of_injective φ hφ, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ hφ, hS'eq, hrange]
    exact hS'idx
  · rw [top_inf_eq]
    apply Subgroup.map_injective hφ
    rw [hB, ← Subgroup.comap_normalizer_eq_of_le_range hS'le, Subgroup.map_comap_eq]
  · exact fun e => hne (by rw [e])
  · apply Subgroup.map_injective hφ
    rw [Subgroup.map_inf_eq _ _ _ hφ, hinf]
  · intro Q
    have hiff : (B ≤ Q ∧ Q ≤ ⊤ ∧ Q ≠ ⊤ ∧ ∀ R : Subgroup M, Q < R → R ≤ ⊤ → R = ⊤) ↔
        (B.map φ ≤ Q.map φ ∧ Q.map φ ≤ φ.range ∧ Q.map φ ≠ φ.range ∧
          ∀ R : Subgroup E, Q.map φ < R → R ≤ φ.range → R = φ.range) := by
      constructor
      · rintro ⟨hBQ, -, hQne, hQmax⟩
        refine ⟨Subgroup.map_mono hBQ, hrange ▸ Subgroup.map_mono le_top,
          fun e => hQne (Subgroup.map_injective hφ (e.trans hrange.symm)), fun R hR hRH => ?_⟩
        have hRe : (R.comap φ).map φ = R := Subgroup.map_comap_eq_self hRH
        have hlt : Q < R.comap φ := by
          refine lt_of_le_of_ne (Subgroup.map_le_iff_le_comap.1 hR.le) fun e => hR.ne ?_
          rw [← hRe, ← e]
        rw [← hRe, hQmax _ hlt le_top, hrange]
      · rintro ⟨hBQ, -, hQne, hQmax⟩
        refine ⟨(Subgroup.map_le_map_iff_of_injective hφ).1 hBQ, le_top,
          fun e => hQne (by rw [e, hrange]), fun R hR _ => ?_⟩
        have hlt : Q.map φ < R.map φ :=
          lt_of_le_of_ne (Subgroup.map_mono hR.le) fun e => hR.ne (Subgroup.map_injective hφ e)
        exact Subgroup.map_injective hφ
          ((hQmax _ hlt (hrange ▸ Subgroup.map_mono le_top)).trans hrange.symm)
    rw [hiff, hmax (Q.map φ)]
    constructor
    · rintro (e | e)
      · exact Or.inl (Subgroup.map_injective hφ e)
      · exact Or.inr (Subgroup.map_injective hφ e)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem burnsideF4h_tri_normalizer_of_parent {M N : Type} [Group M] [Group N] (incl : M →* N)
    (hinj : Function.Injective incl) {P L : Subgroup M} {P' L' : Subgroup N}
    (hP : P.map incl = incl.range ⊓ P') (hL : L.map incl = incl.range ⊓ L')
    (h : P' ≤ Subgroup.normalizer (L' : Set N)) : P ≤ Subgroup.normalizer (L : Set M) := by
  intro x hx
  have hxP' : incl x ∈ P' := (Subgroup.mem_inf.1 (hP ▸ Subgroup.mem_map_of_mem incl hx)).2
  have hN := Subgroup.mem_normalizer_iff.1 (h hxP')
  have hmem : ∀ y : M, y ∈ L ↔ incl y ∈ L' := by
    intro y
    have h1 : y ∈ L ↔ incl y ∈ L.map incl :=
      ⟨fun hy => Subgroup.mem_map_of_mem incl hy, fun ⟨t, ht, hts⟩ => by rwa [← hinj hts]⟩
    rw [h1, hL, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨⟨y, rfl⟩, h⟩⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [hmem y, hmem (x * y * x⁻¹), map_mul, map_mul, map_inv]
  exact hN (incl y)

end Transport

section Embedding

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {K : Type} [Field K] [Finite K]

theorem burnsideF4h_tri_exists_embedding {p d : ℕ} (hp : p.Prime) (hd : 1 ≤ d)
    (hK : Nat.card K = (p ^ d) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ d)) :
    ∃ f : DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ.toRingHom) →*
        ModGL TwistTag.D4.tag K,
      Function.Injective f ∧ f.range = graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      ∀ P : Subgroup (ModGL TwistTag.D4.tag K),
        (derivedImage (twistedFixedGroup TwistTag.D4 K σ.toRingHom) P).map f =
          P ⊓ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  have hΓ := burnsideF4h_tri_twisted_eq hp hd hK σ hσ
  have hD : ⁅twistedFixedGroup TwistTag.D4 K σ.toRingHom,
      twistedFixedGroup TwistTag.D4 K σ.toRingHom⁆ =
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    rw [hΓ]
    exact burnsideF4h_tri_commutator_eq hp hd hK σ hσ
  obtain ⟨e, he⟩ := burnsideF4h_tri_exists_derivedEquiv _ _ hD
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  refine ⟨(graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp e.toMonoidHom,
    Subtype.coe_injective.comp e.injective, ?_, fun P => ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · rw [← Subgroup.map_map, burnsideF4h_tri_map_derivedImage _ _ P hD e he,
      Subgroup.subgroupOf_map_subtype]

end Embedding

section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots


theorem burnsideF4h_trialityOrderedLocals_core (K : Type) [Field K] [Finite K] :
    ChF.NativeFrame.trialityOrderedLocalsGoal K := by
  intro sigma prime degree hscope
  obtain ⟨hp, hd, hK, hσ⟩ := hscope
  obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = sigma :=
    ⟨RingEquiv.ofBijective sigma ⟨sigma.injective, Finite.surjective_of_injective sigma.injective⟩,
      rfl⟩
  have hσ' : ∀ c, σ c = c ^ (prime ^ degree) := hσ
  haveI : Fact prime.Prime := ⟨hp⟩
  haveI : CharP K prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (k := degree * 3) (by omega) (by rw [hK, pow_mul])
  obtain ⟨f, hf, hrange, hmap⟩ := burnsideF4h_tri_exists_embedding hp hd hK σ hσ'
  have hΓ := burnsideF4h_tri_twisted_eq hp hd hK σ hσ'
  have hB := burnsideF4h_tri_trialityBorel_eq σ.toRingHom hΓ
  have h0 := burnsideF4h_tri_trialityParabolic_zero σ.toRingHom hΓ
  have h1 := burnsideF4h_tri_trialityParabolic_one σ.toRingHom hΓ
  have hmB : (derivedImage (twistedFixedGroup TwistTag.D4 K σ.toRingHom)
      (trialityBorel K σ.toRingHom)).map f = graphFixedRootBorel TwistTag.D4 K σ.toRingHom :=
    (hmap _).trans ((congrArg (· ⊓ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) hB).trans
      (inf_eq_left.2 (graphFixedRootBorel_le _ _ _)))
  have hm0 : (derivedImage (twistedFixedGroup TwistTag.D4 K σ.toRingHom)
      (trialityParabolic K σ.toRingHom 0)).map f =
        graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨0, by decide⟩} :=
    (hmap _).trans ((congrArg (· ⊓ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) h0).trans
      (inf_eq_left.2 (graphFixedParabolic_le _ _ _ _)))
  have hm1 : (derivedImage (twistedFixedGroup TwistTag.D4 K σ.toRingHom)
      (trialityParabolic K σ.toRingHom 1)).map f =
        graphFixedParabolic TwistTag.D4 K σ.toRingHom {⟨1, by decide⟩} :=
    (hmap _).trans ((congrArg (· ⊓ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) h1).trans
      (inf_eq_left.2 (graphFixedParabolic_le _ _ _ _)))
  have hcard : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      Nat.card (orbitField TwistTag.D4 K σ.toRingHom a) =
        (prime ^ degree) ^ (TwistTag.D4.orbit a).card :=
    card_orbitField_D4_orientation hp hd hK (r := 1) (Or.inl rfl)
      (fun c => by rw [pow_one]; exact hσ' c)
  dsimp only [ChF.NativeFrame.triality]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply burnsideF4h_tri_isLieParabolics_of_map f hf
    rw [hrange, hmB, hm0, hm1]
    exact burnsideF4h_tri_isLieParabolics_graphFixed prime σ.toRingHom σ.surjective
  · rw [← Subgroup.relIndex_map_map_of_injective (f := f) _ _ hf, hmB, hm0,
      burnsideF4h_tri_relIndex_parabolic σ.toRingHom σ.surjective, hcard]
    rfl
  · rw [← Subgroup.relIndex_map_map_of_injective (f := f) _ _ hf, hmB, hm1,
      burnsideF4h_tri_relIndex_parabolic σ.toRingHom σ.surjective, hcard,
      show (TwistTag.D4.orbit (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)).card = 1 by
        decide, pow_one]
  · refine burnsideF4h_tri_normalizer_of_parent f hf (P' := trialityParabolic K σ.toRingHom 0)
      (L' := trialityLongRoot K σ.toRingHom) ?_ ?_
      (burnsideF4h_tri_parabolic_le_normalizer_longRoot σ.toRingHom)
    · exact (hmap _).trans (by rw [hrange]; exact inf_comm _ _)
    · exact (hmap _).trans (by rw [hrange]; exact inf_comm _ _)

end

end PartBurnsideF4hTri

section PartBurnsideF4hInvD4

section Abstract

open CFSG.ASVolI.ChF

variable {C : Type} [Group C]

theorem burnsideF4h_invd4_eq_one_of_isConj {x y : C} (h : IsConj x y) (hy : y = 1) : x = 1 :=
  isConj_one_left.1 (hy ▸ h)

theorem burnsideF4h_invd4_mul_self_of_isConj {x y : C} (h : IsConj x y) (hx : x * x = 1) :
    y * y = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
    _ = 1 := by rw [hx]; group

variable {E : Type} [Group E] {core : Subgroup E}

theorem burnsideF4h_invd4_conj_of_isConj (ψ : C ≃* core) {x y : C} (h : IsConj x y) :
    ∃ c ∈ core, c * ((ψ x : core) : E) * c⁻¹ = ((ψ y : core) : E) := by
  obtain ⟨d, rfl⟩ := isConj_iff.1 h
  refine ⟨((ψ d : core) : E), (ψ d).2, ?_⟩
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem burnsideF4h_invd4_isConj_of_conj (ψ : C ≃* core) {x y : C} {c : E} (hc : c ∈ core)
    (h : c * ((ψ x : core) : E) * c⁻¹ = ((ψ y : core) : E)) : IsConj x y := by
  refine isConj_iff.2 ⟨ψ.symm ⟨c, hc⟩, ψ.injective (Subtype.ext ?_)⟩
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  exact h

theorem burnsideF4h_invd4_of_model {kind : GLKind} {prime degree : ℕ}
    (chart : NativeChart kind prime degree core) (hk : kind ≠ .G2d) (ψ : C ≃* core)
    (L S : Subgroup C) (z t : C) (hz2 : z * z = 1) (ht2 : t * t = 1)
    (cover : ∀ x : C, x ≠ 1 → x * x = 1 → IsConj z x ∨ IsConj t x)
    (not_conj : ¬ IsConj z t)
    (L_ne : ∃ a ∈ L, a ≠ 1) (L_conj : ∀ a ∈ L, a ≠ 1 → IsConj z a)
    (S_ne : ∃ b ∈ S, b ≠ 1) (S_conj : ∀ b ∈ S, b ≠ 1 → IsConj t b)
    (hL : chart.longRoot = (L.map ψ.toMonoidHom).map core.subtype)
    (hS : chart.shortRoot = (S.map ψ.toMonoidHom).map core.subtype) :
    ∃ long ∈ chart.longRoot, ∃ short ∈ chart.shortRoot,
      long ≠ 1 ∧ long * long = 1 ∧ short ≠ 1 ∧ short * short = 1 ∧
      (¬ ∃ conjugator ∈ core, conjugator * long * conjugator⁻¹ = short) ∧
      (∀ element : E, chart.RootInvolution false element ↔
        element ∈ core ∧ ∃ conjugator ∈ core,
          conjugator * element * conjugator⁻¹ = long) ∧
      (∀ element : E, chart.RootInvolution true element ↔
        element ∈ core ∧ ∃ conjugator ∈ core,
          conjugator * element * conjugator⁻¹ = short) ∧
      (∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element ∨ chart.RootInvolution true element) := by
  obtain ⟨a, haL, ha1⟩ := L_ne
  obtain ⟨b, hbS, hb1⟩ := S_ne
  have hza := L_conj a haL ha1
  have htb := S_conj b hbS hb1
  have ha2 : a * a = 1 := burnsideF4h_invd4_mul_self_of_isConj hza hz2
  have hb2 : b * b = 1 := burnsideF4h_invd4_mul_self_of_isConj htb ht2
  have hval_one : ∀ x : C, ((ψ x : core) : E) = 1 ↔ x = 1 := by
    intro x
    constructor
    · intro h
      exact ψ.injective (Subtype.ext (by rw [h, map_one]; rfl))
    · rintro rfl
      rw [map_one]
      rfl
  have hval_sq : ∀ x : C, x * x = 1 → ((ψ x : core) : E) * ((ψ x : core) : E) = 1 := by
    intro x hx
    rw [← Subgroup.coe_mul, ← map_mul, hx, map_one]
    rfl
  have hmemL : ∀ y : E, y ∈ chart.longRoot ↔ ∃ x ∈ L, ((ψ x : core) : E) = y := by
    intro y
    rw [hL]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ψ x, ⟨x, hx, rfl⟩, rfl⟩
  have hmemS : ∀ y : E, y ∈ chart.shortRoot ↔ ∃ x ∈ S, ((ψ x : core) : E) = y := by
    intro y
    rw [hS]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ψ x, ⟨x, hx, rfl⟩, rfl⟩
  have hsurj : ∀ y ∈ core, ∃ x : C, ((ψ x : core) : E) = y := by
    intro y hy
    exact ⟨ψ.symm ⟨y, hy⟩, by rw [MulEquiv.apply_symm_apply]⟩
  have hconj_to : ∀ {x x' : C}, IsConj x' x →
      ∃ c ∈ core, c * ((ψ x' : core) : E) * c⁻¹ = ((ψ x : core) : E) :=
    fun h => burnsideF4h_invd4_conj_of_isConj ψ h
  have hclass : ∀ (short : Bool) (X : Subgroup C) (w r : C),
      ((if short then chart.shortRoot else chart.longRoot) =
        (X.map ψ.toMonoidHom).map core.subtype) →
      IsConj w r → r ∈ X → (∀ x ∈ X, x ≠ 1 → IsConj w x) → r ≠ 1 → r * r = 1 →
      ∀ element : E, chart.RootInvolution short element ↔
        element ∈ core ∧ ∃ conjugator ∈ core,
          conjugator * element * conjugator⁻¹ = ((ψ r : core) : E) := by
    intro short X w r hX hwr hrX hXconj hr1 hr2 element
    constructor
    · rintro ⟨hcore, hne, -, -, c, hc, hcx⟩
      refine ⟨hcore, ?_⟩
      rw [hX] at hcx
      obtain ⟨_, ⟨x, hxX, rfl⟩, hx⟩ := hcx
      have hx1 : x ≠ 1 := by
        intro h
        apply hne
        have h' : c * element * c⁻¹ = 1 := by
          rw [← hx, h, map_one]
          rfl
        calc element = c⁻¹ * (c * element * c⁻¹) * c := by group
          _ = 1 := by rw [h']; group
      obtain ⟨d, hd, hdx⟩ := hconj_to ((hXconj x hxX hx1).symm.trans hwr)
      refine ⟨d * c, mul_mem hd hc, ?_⟩
      have hx' : ((ψ x : core) : E) = c * element * c⁻¹ := hx
      rw [hx'] at hdx
      rw [← hdx]
      group
    · rintro ⟨hcore, c, hc, hcx⟩
      have hne : element ≠ 1 := by
        rintro rfl
        apply hr1
        rw [← hval_one]
        rw [← hcx]
        group
      have hsq : element * element = 1 := by
        have h2 := hval_sq r hr2
        rw [← hcx] at h2
        have : c * (element * element) * c⁻¹ = 1 := by
          rw [← h2]
          group
        calc element * element = c⁻¹ * (c * (element * element) * c⁻¹) * c := by group
          _ = 1 := by rw [this]; group
      refine ⟨hcore, hne, hsq, fun h => absurd h hk, c, hc, ?_⟩
      rw [hX, hcx]
      exact ⟨ψ r, ⟨r, hrX, rfl⟩, rfl⟩
  refine ⟨((ψ a : core) : E), (hmemL _).2 ⟨a, haL, rfl⟩, ((ψ b : core) : E),
    (hmemS _).2 ⟨b, hbS, rfl⟩, fun h => ha1 ((hval_one a).1 h), hval_sq a ha2,
    fun h => hb1 ((hval_one b).1 h), hval_sq b hb2, ?_, ?_, ?_, ?_⟩
  · rintro ⟨c, hc, hcab⟩
    exact not_conj ((hza.trans (burnsideF4h_invd4_isConj_of_conj ψ hc hcab)).trans htb.symm)
  · exact hclass false L z a hL hza haL L_conj ha1 ha2
  · exact hclass true S t b hS htb hbS S_conj hb1 hb2
  · intro element hcore hne hsq
    obtain ⟨x, rfl⟩ := hsurj element hcore
    have hx1 : x ≠ 1 := fun h => hne ((hval_one x).2 h)
    have hx2 : x * x = 1 := by
      apply ψ.injective
      apply Subtype.ext
      rw [map_mul, Subgroup.coe_mul, hsq, map_one]
      rfl
    rcases cover x hx1 hx2 with h | h
    · left
      obtain ⟨c, hc, hcx⟩ := hconj_to (h.symm.trans hza)
      refine ⟨hcore, hne, hsq, fun h => absurd h hk, c, hc, ?_⟩
      show c * ((ψ x : core) : E) * c⁻¹ ∈ chart.longRoot
      rw [hcx]
      exact (hmemL _).2 ⟨a, haL, rfl⟩
    · right
      obtain ⟨c, hc, hcx⟩ := hconj_to (h.symm.trans htb)
      refine ⟨hcore, hne, hsq, fun h => absurd h hk, c, hc, ?_⟩
      show c * ((ψ x : core) : E) * c⁻¹ ∈ chart.shortRoot
      rw [hcx]
      exact (hmemS _).2 ⟨b, hbS, rfl⟩

end Abstract

section Weyl

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def burnsideF4h_invd4_wordUnit (τ : Tag) (K : Type) [Field K]
    (word : List (Fin τ.rank)) : ModGL τ K :=
  ((word.map fun i => weylElt τ K i 1).reverse).prod

theorem burnsideF4h_invd4_coe_wordUnit (word : List (Fin τ.rank)) :
    (burnsideF4h_invd4_wordUnit τ K word : Module.End K (RootModule τ K)) =
      weylWordOperator τ K word := by
  have h := map_list_prod (Units.coeHom (Module.End K (RootModule τ K)))
    ((word.map fun i => weylElt τ K i 1).reverse)
  simp only [Units.coeHom_apply, List.map_reverse, List.map_map] at h
  exact h

theorem burnsideF4h_invd4_eq_wordUnit_iff (word : List (Fin τ.rank)) (g : ModGL τ K) :
    (g : Module.End K (RootModule τ K)) = weylWordOperator τ K word ↔
      g = burnsideF4h_invd4_wordUnit τ K word := by
  rw [← burnsideF4h_invd4_coe_wordUnit]
  exact ⟨fun h => Units.ext h, fun h => by rw [h]⟩

theorem burnsideF4h_invd4_wordUnit_cons (i : Fin τ.rank) (word : List (Fin τ.rank)) :
    burnsideF4h_invd4_wordUnit τ K (i :: word) =
      burnsideF4h_invd4_wordUnit τ K word * weylElt τ K i 1 := by
  simp [burnsideF4h_invd4_wordUnit]

theorem burnsideF4h_invd4_wordUnit_append (w w' : List (Fin τ.rank)) :
    burnsideF4h_invd4_wordUnit τ K (w ++ w') =
      burnsideF4h_invd4_wordUnit τ K w' * burnsideF4h_invd4_wordUnit τ K w := by
  simp [burnsideF4h_invd4_wordUnit]

end Weyl

section RootGroups

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

variable {τ : Tag} {K : Type} [Field K]

theorem burnsideF4h_invd4_conj_mem_rootSubgroup (word : List (Fin τ.rank)) :
    ∀ {β : Fin τ.rank → ℤ}, IsRoot τ β → ∀ {g : ModGL τ K}, g ∈ rootSubgroup τ K β →
      burnsideF4h_invd4_wordUnit τ K word * g * (burnsideF4h_invd4_wordUnit τ K word)⁻¹ ∈
        rootSubgroup τ K (word.foldl (fun root index => reflect τ index root) β) := by
  induction word with
  | nil =>
    intro β hβ g hg
    simpa [burnsideF4h_invd4_wordUnit] using hg
  | cons i w ih =>
    intro β hβ g hg
    have h1 : weylElt τ K i 1 * g * (weylElt τ K i 1)⁻¹ ∈ rootSubgroup τ K (reflect τ i β) := by
      rw [← map_conj_weylElt_rootSubgroup K i hβ]
      exact ⟨g, hg, rfl⟩
    have h2 := ih (IsRoot.reflect i hβ) h1
    rw [List.foldl_cons, burnsideF4h_invd4_wordUnit_cons]
    have e : burnsideF4h_invd4_wordUnit τ K w * weylElt τ K i 1 * g *
        (burnsideF4h_invd4_wordUnit τ K w * weylElt τ K i 1)⁻¹ =
        burnsideF4h_invd4_wordUnit τ K w * (weylElt τ K i 1 * g * (weylElt τ K i 1)⁻¹) *
          (burnsideF4h_invd4_wordUnit τ K w)⁻¹ := by
      group
    rw [e]
    exact h2

theorem burnsideF4h_invd4_absoluteRoot_eq {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    absoluteRoot τ K α = rootSubgroup τ K α := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro e ⟨c, seed, word, actor, hfold, hactor, helem⟩
    have hact : actor = burnsideF4h_invd4_wordUnit τ K word :=
      (burnsideF4h_invd4_eq_wordUnit_iff word actor).1 hactor
    have he : e = burnsideF4h_invd4_wordUnit τ K word * xUnit τ K seed c *
        (burnsideF4h_invd4_wordUnit τ K word)⁻¹ := by
      refine Units.ext ?_
      rw [helem, hact]
      rfl
    have hx : xUnit τ K seed c ∈ rootSubgroup τ K (Pi.single seed 1) := by
      rw [← pinnedX_single]
      exact Subgroup.subset_closure ⟨c, rfl⟩
    have h := burnsideF4h_invd4_conj_mem_rootSubgroup word (IsRoot.basis seed) hx
    rw [hfold] at h
    rw [he]
    exact h
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    refine Subgroup.subset_closure ⟨(pinnedData τ α).2.2 • c, (pinnedData τ α).1,
      (pinnedData τ α).2.1.map τ.idx, pinnedWeyl τ K α, ?_, ?_, ?_⟩
    · rw [List.foldl_map]
      exact foldl_reflect_pinnedData hα
    · rw [← burnsideF4h_invd4_coe_wordUnit]
      simp [pinnedWeyl, burnsideF4h_invd4_wordUnit, List.map_map, Function.comp_def]
    · rfl

end RootGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley in
local instance burnsideF4h_invd4_neZeroRankD4 : NeZero Tag.D4.rank := ⟨by decide⟩

open CFSG.Blueprint CFSG.Blueprint.Chevalley in
local instance burnsideF4h_invd4_neZeroRankD4tag : NeZero TwistTag.D4.tag.rank := ⟨by decide⟩

section Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ASVolI.ChF.ExceptionalRoots

theorem burnsideF4h_invd4_orbitWord_zero :
    TwistTag.D4.orbitWord (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) =
      ([0, 1, 3] : List (Fin TwistTag.D4.tag.rank)) := by
  rfl

theorem burnsideF4h_invd4_orbitWord_one :
    TwistTag.D4.orbitWord (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) =
      ([2] : List (Fin TwistTag.D4.tag.rank)) := by
  rfl

section Reps

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def burnsideF4h_invd4_orbitRep (a : Fin TwistTag.D4.foldedTag.rank) :
    ModGL TwistTag.D4.tag K :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a)

theorem burnsideF4h_invd4_wordUnit_central :
    burnsideF4h_invd4_wordUnit Tag.D4 K [2] = burnsideF4h_invd4_orbitRep K ⟨1, by decide⟩ := by
  unfold burnsideF4h_invd4_orbitRep
  rw [canonicalRep_orbitReflection, burnsideF4h_invd4_orbitWord_one, List.map_singleton,
    List.prod_singleton]
  simp only [burnsideF4h_invd4_wordUnit, List.map_singleton, List.reverse_singleton,
    List.prod_singleton]
  try rfl

end Reps

section Commute

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

theorem burnsideF4h_invd4_commute_outer (l j : Fin TwistTag.D4.tag.rank)
    (hl : l ∈ TwistTag.D4.orbit (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank))
    (hj : j ∈ TwistTag.D4.orbit (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank))
    (hlj : l ≠ j) :
    Commute (weylElt TwistTag.D4.tag K l 1) (weylElt TwistTag.D4.tag K j 1) :=
  commute_weylElt_weylElt (t := TwistTag.D4) K hl hj hlj 1 1

theorem burnsideF4h_invd4_wordUnit_outer :
    burnsideF4h_invd4_wordUnit Tag.D4 K [0, 1, 3] =
      burnsideF4h_invd4_orbitRep K ⟨0, by decide⟩ := by
  unfold burnsideF4h_invd4_orbitRep
  rw [canonicalRep_orbitReflection, burnsideF4h_invd4_orbitWord_zero]
  have h01 : Commute (weylElt TwistTag.D4.tag K 0 1) (weylElt TwistTag.D4.tag K 1 1) :=
    burnsideF4h_invd4_commute_outer 0 1 (by decide) (by decide) (by decide)
  have h03 : Commute (weylElt TwistTag.D4.tag K 0 1) (weylElt TwistTag.D4.tag K 3 1) :=
    burnsideF4h_invd4_commute_outer 0 3 (by decide) (by decide) (by decide)
  have h13 : Commute (weylElt TwistTag.D4.tag K 1 1) (weylElt TwistTag.D4.tag K 3 1) :=
    burnsideF4h_invd4_commute_outer 1 3 (by decide) (by decide) (by decide)
  simp only [burnsideF4h_invd4_wordUnit, List.map_cons, List.map_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, List.singleton_append,
    List.cons_append, mul_one]
  change weylElt TwistTag.D4.tag K 3 1 * (weylElt TwistTag.D4.tag K 1 1 *
      weylElt TwistTag.D4.tag K 0 1) = weylElt TwistTag.D4.tag K 0 1 *
        (weylElt TwistTag.D4.tag K 1 1 * weylElt TwistTag.D4.tag K 3 1)
  calc weylElt TwistTag.D4.tag K 3 1 * (weylElt TwistTag.D4.tag K 1 1 *
        weylElt TwistTag.D4.tag K 0 1)
      = weylElt TwistTag.D4.tag K 3 1 * (weylElt TwistTag.D4.tag K 0 1 *
          weylElt TwistTag.D4.tag K 1 1) := by
        rw [h01.eq]
    _ = weylElt TwistTag.D4.tag K 0 1 * (weylElt TwistTag.D4.tag K 3 1 *
          weylElt TwistTag.D4.tag K 1 1) := by
        rw [← mul_assoc, ← mul_assoc, h03.eq.symm]
    _ = weylElt TwistTag.D4.tag K 0 1 * (weylElt TwistTag.D4.tag K 1 1 *
          weylElt TwistTag.D4.tag K 3 1) := by
        rw [h13.eq]

end Commute

end Triality

section Quotient

open CFSG.Blueprint CFSG.ASVolI.ChF.ExceptionalRoots

variable {M : Type} [Group M]

theorem burnsideF4h_invd4_exists_derivedEquiv (Γ C : Subgroup M) (hD : ⁅Γ, Γ⁆ = C)
    (hZ : Subgroup.center ↥C = ⊥) :
    ∃ e : DerivedCentralQuotient Γ ≃* ↥C,
      ∀ x : ↥⁅Γ, Γ⁆, ((e (QuotientGroup.mk x) : ↥C) : M) = (x : M) := by
  subst hD
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot, fun x => rfl⟩

theorem burnsideF4h_invd4_map_derivedImage (Γ C P : Subgroup M) (hD : ⁅Γ, Γ⁆ = C)
    (e : DerivedCentralQuotient Γ ≃* ↥C)
    (he : ∀ x : ↥⁅Γ, Γ⁆, ((e (QuotientGroup.mk x) : ↥C) : M) = (x : M)) :
    (derivedImage Γ P).map e.toMonoidHom = P.subgroupOf C := by
  ext y
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hxP : (x : M) ∈ P := hx
    exact (he x).symm ▸ hxP
  · intro hy
    have hyP : (y : M) ∈ P := hy
    have hyD : (y : M) ∈ ⁅Γ, Γ⁆ := hD ▸ y.2
    refine ⟨QuotientGroup.mk ⟨(y : M), hyD⟩, ⟨⟨(y : M), hyD⟩, hyP, rfl⟩, ?_⟩
    exact Subtype.ext (he ⟨(y : M), hyD⟩)

end Quotient

section Words

set_option linter.unusedSectionVars false

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable (K : Type) [Field K]

@[expose] noncomputable def burnsideF4h_invd4_nL : ModGL TwistTag.D4.tag K :=
  burnsideF4h_invd4_wordUnit Tag.D4 K [0, 1, 3, 2]

@[expose] noncomputable def burnsideF4h_invd4_nS : ModGL TwistTag.D4.tag K :=
  burnsideF4h_invd4_wordUnit Tag.D4 K [2, 0, 1, 3]

end Words

section Model

set_option linter.unusedSectionVars false

open CFSG.ASVolI.ChF CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem burnsideF4h_invd4_cover : ∀ x : Cm σ, x ≠ 1 → x * x = 1 →
    IsConj (zC σ) x ∨ IsConj (tC σ hσ) x := by
  intro x hx1 hx2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact cls_d4 σ hσ x (orderOf_eq_prime (by rw [sq]; exact hx2) hx1)

include hσ in
theorem burnsideF4h_invd4_not_conj : ¬ IsConj (zC σ) (tC σ hσ) := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact no_aut_zC_tC σ hσ (MulAut.conj c) (by simpa [MulAut.conj_apply] using hc)

include hσ in
theorem burnsideF4h_invd4_Gamma_eq :
    twistedFixedGroup TwistTag.D4 K σ.toRingHom =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  twistedFixedGroup_eq_graphFixedRootGroup_triality σ hσ (Or.inl (ringChar.eq K 2))

include hσ in
theorem burnsideF4h_invd4_orbitRep_mem (a : Fin TwistTag.D4.foldedTag.rank) :
    burnsideF4h_invd4_orbitRep K a ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  rw [burnsideF4h_invd4_Gamma_eq σ hσ]
  exact canonicalRep_orbitReflection_mem_graphFixedRootGroup (σ := σ.toRingHom) a

include hσ in
theorem burnsideF4h_invd4_nL_mem :
    burnsideF4h_invd4_nL K ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  have e : ([0, 1, 3, 2] : List (Fin Tag.D4.rank)) = [0, 1, 3] ++ [2] := rfl
  unfold burnsideF4h_invd4_nL
  rw [e, burnsideF4h_invd4_wordUnit_append, burnsideF4h_invd4_wordUnit_outer,
    burnsideF4h_invd4_wordUnit_central]
  exact mul_mem (burnsideF4h_invd4_orbitRep_mem σ hσ _) (burnsideF4h_invd4_orbitRep_mem σ hσ _)

include hσ in
theorem burnsideF4h_invd4_nS_mem :
    burnsideF4h_invd4_nS K ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  have e : ([2, 0, 1, 3] : List (Fin Tag.D4.rank)) = [2] ++ [0, 1, 3] := rfl
  unfold burnsideF4h_invd4_nS
  rw [e, burnsideF4h_invd4_wordUnit_append, burnsideF4h_invd4_wordUnit_outer,
    burnsideF4h_invd4_wordUnit_central]
  exact mul_mem (burnsideF4h_invd4_orbitRep_mem σ hσ _) (burnsideF4h_invd4_orbitRep_mem σ hσ _)

section RootTraces

open CFSG.ASVolI.ChF.ExceptionalRoots CFSG.ComponentClassification.RankTwoExceptional.D4

include hσ in
theorem burnsideF4h_invd4_posRoot_one {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ trialityPositiveRoot K σ.toRingHom 1) :
    ∃ c : K, σ c = c ∧ g = d4x₂ K c := by
  have hne : ¬ ((1 : Fin 6) = 0 ∨ (1 : Fin 6) = 2 ∨ (1 : Fin 6) = 3) := by decide
  rw [trialityPositiveRoot, if_neg hne] at hg
  obtain ⟨hgΓ, hgA⟩ := hg
  have hseed : trialitySeed 1 = Pi.single (2 : Fin Tag.D4.rank) 1 := by
    funext i; fin_cases i <;> rfl
  rw [hseed, burnsideF4h_invd4_absoluteRoot_eq (IsRoot.basis _)] at hgA
  have hspan : g ∈ rootSpan TwistTag.D4.tag K
      ((fun i => (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) ''
        ↑(TwistTag.D4.orbit (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank))) :=
    Subgroup.mem_iSup_of_mem (Pi.single (2 : Fin Tag.D4.rank) 1)
      (Subgroup.mem_iSup_of_mem ⟨2, by decide, rfl⟩ hgA)
  obtain ⟨c, hc⟩ := exists_orbitX_eq (σ := σ.toRingHom) hspan hgΓ.2
  refine ⟨(c : K), (mem_orbitField_D4_one σ).1 c.2, ?_⟩
  rw [← hc]
  exact coe_orbitX_one_d4 σ c

include hσ in
theorem burnsideF4h_invd4_x₂_mem_posRoot :
    d4x₂ K 1 ∈ trialityPositiveRoot K σ.toRingHom 1 := by
  have hne : ¬ ((1 : Fin 6) = 0 ∨ (1 : Fin 6) = 2 ∨ (1 : Fin 6) = 3) := by decide
  rw [trialityPositiveRoot, if_neg hne]
  have hseed : trialitySeed 1 = Pi.single (2 : Fin Tag.D4.rank) 1 := by
    funext i; fin_cases i <;> rfl
  have e : trialityRoot 1 = Pi.single (2 : Fin TwistTag.D4.tag.rank) 1 := by
    funext i; fin_cases i <;> rfl
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [burnsideF4h_invd4_Gamma_eq σ hσ]
    exact (d4x_long_mem σ (map_one σ)).1
  · rw [hseed, burnsideF4h_invd4_absoluteRoot_eq (IsRoot.basis _)]
    have h : d4x₂ K 1 ∈ rootSubgroup TwistTag.D4.tag K (trialityRoot 1) :=
      Subgroup.subset_closure ⟨1, rfl⟩
    rw [e] at h
    exact h

include hσ in
theorem burnsideF4h_invd4_longRoot_elements :
    ∀ a ∈ trialityLongRoot K σ.toRingHom, ∃ c : K, σ c = c ∧
      a = burnsideF4h_invd4_nL K * d4x₂ K c * (burnsideF4h_invd4_nL K)⁻¹ := by
  intro a ha
  unfold trialityLongRoot fixedWeylConjugate at ha
  induction ha using Subgroup.closure_induction with
  | mem e he =>
    obtain ⟨actor, -, hactor, g, hg, rfl⟩ := he
    obtain ⟨c, hc, rfl⟩ := burnsideF4h_invd4_posRoot_one σ hσ hg
    have hact : actor = burnsideF4h_invd4_wordUnit Tag.D4 K [0, 1, 3, 2] :=
      (burnsideF4h_invd4_eq_wordUnit_iff _ actor).1 hactor
    subst hact
    exact ⟨c, hc, rfl⟩
  | one =>
    refine ⟨0, map_zero σ, ?_⟩
    show (1 : ModGL TwistTag.D4.tag K) =
      burnsideF4h_invd4_nL K * d4x₂ K 0 * (burnsideF4h_invd4_nL K)⁻¹
    rw [d4x₂_zero]
    group
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨c', hc', rfl⟩ := hy
    refine ⟨c + c', by rw [map_add, hc, hc'], ?_⟩
    show (burnsideF4h_invd4_nL K * d4x₂ K c * (burnsideF4h_invd4_nL K)⁻¹ *
        (burnsideF4h_invd4_nL K * d4x₂ K c' * (burnsideF4h_invd4_nL K)⁻¹) :
          ModGL TwistTag.D4.tag K) =
      burnsideF4h_invd4_nL K * d4x₂ K (c + c') * (burnsideF4h_invd4_nL K)⁻¹
    rw [d4x₂_add]
    group
  | inv x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine ⟨-c, by rw [map_neg, hc], ?_⟩
    have h : d4x₂ K (-c) = (d4x₂ K c)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by rw [← d4x₂_add, add_neg_cancel, d4x₂_zero])
    show ((burnsideF4h_invd4_nL K * d4x₂ K c * (burnsideF4h_invd4_nL K)⁻¹)⁻¹ :
        ModGL TwistTag.D4.tag K) =
      burnsideF4h_invd4_nL K * d4x₂ K (-c) * (burnsideF4h_invd4_nL K)⁻¹
    rw [h]
    group

theorem burnsideF4h_invd4_x₂_ne_one : d4x₂ K 1 ≠ 1 := fun h =>
  one_ne_zero (pinnedX_injective _ _ _ (h.trans (pinnedX_zero _ _ _).symm))

@[expose] noncomputable def burnsideF4h_invd4_LC : Subgroup (Cm σ) :=
  (trialityLongRoot K σ.toRingHom).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

@[expose] noncomputable def burnsideF4h_invd4_SC : Subgroup (Cm σ) :=
  (trialityShortRoot K σ.toRingHom).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

include hσ in
theorem burnsideF4h_invd4_L_ne : ∃ a ∈ burnsideF4h_invd4_LC σ, a ≠ 1 := by
  have hn := burnsideF4h_invd4_nL_mem σ hσ
  rw [burnsideF4h_invd4_Gamma_eq σ hσ] at hn
  have hx : d4x₂ K 1 ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (d4x_long_mem σ (map_one σ)).1
  refine ⟨⟨burnsideF4h_invd4_nL K * d4x₂ K 1 * (burnsideF4h_invd4_nL K)⁻¹,
    mul_mem (mul_mem hn hx) (inv_mem hn)⟩, ?_, ?_⟩
  · refine Subgroup.mem_subgroupOf.2 ?_
    unfold trialityLongRoot fixedWeylConjugate
    refine Subgroup.subset_closure ⟨burnsideF4h_invd4_nL K,
      burnsideF4h_invd4_nL_mem σ hσ, burnsideF4h_invd4_coe_wordUnit _, d4x₂ K 1,
      burnsideF4h_invd4_x₂_mem_posRoot σ hσ, rfl⟩
  · intro h
    have h1 : burnsideF4h_invd4_nL K * d4x₂ K 1 * (burnsideF4h_invd4_nL K)⁻¹ = 1 :=
      congrArg Subtype.val h
    apply burnsideF4h_invd4_x₂_ne_one (K := K)
    calc d4x₂ K 1 = (burnsideF4h_invd4_nL K)⁻¹ *
          (burnsideF4h_invd4_nL K * d4x₂ K 1 * (burnsideF4h_invd4_nL K)⁻¹) *
            burnsideF4h_invd4_nL K := by group
      _ = 1 := by rw [h1]; group

include hσ in
theorem burnsideF4h_invd4_L_conj :
    ∀ a ∈ burnsideF4h_invd4_LC σ, a ≠ 1 → IsConj (zC σ) a := by
  intro a ha ha1
  obtain ⟨c, hc, hac⟩ :=
    burnsideF4h_invd4_longRoot_elements σ hσ _ (Subgroup.mem_subgroupOf.1 ha)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply ha1
    apply Subtype.ext
    show (a : ModGL TwistTag.D4.tag K) = 1
    rw [hac, d4x₂_zero]
    group
  obtain ⟨g, hg, hgz⟩ := d4Conj_d4x₂ σ hσ hc hc0
  have hn := burnsideF4h_invd4_nL_mem σ hσ
  rw [burnsideF4h_invd4_Gamma_eq σ hσ] at hn
  refine isConj_iff.2 ⟨⟨burnsideF4h_invd4_nL K * g⁻¹, mul_mem hn (inv_mem hg)⟩, ?_⟩
  apply Subtype.ext
  show burnsideF4h_invd4_nL K * g⁻¹ * d4z K * (burnsideF4h_invd4_nL K * g⁻¹)⁻¹ =
    (a : ModGL TwistTag.D4.tag K)
  rw [hac, ← hgz]
  group

include hσ in
theorem burnsideF4h_invd4_posRoot_zero {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ trialityPositiveRoot K σ.toRingHom 0) : ∃ c : K, g = d4x₁ K σ c := by
  have hpos : ((0 : Fin 6) = 0 ∨ (0 : Fin 6) = 2 ∨ (0 : Fin 6) = 3) := Or.inl rfl
  rw [trialityPositiveRoot, if_pos hpos] at hg
  obtain ⟨hgΓ, hgA⟩ := hg
  have hseed : trialitySeed 0 = Pi.single (0 : Fin Tag.D4.rank) 1 := by
    funext i; fin_cases i <;> rfl
  have hspan : g ∈ rootSpan TwistTag.D4.tag K
      ((fun i => (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) ''
        ↑(TwistTag.D4.orbit (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank))) := by
    refine (iSup_le (fun index => ?_) :
      (⨆ index : Fin 3, absoluteRoot Tag.D4 K
        (permLattice (τ := Tag.D4) (TwistTag.D4.perm ^ (index : ℕ)) (trialitySeed 0))) ≤ _) hgA
    have e := permLattice_single (τ := Tag.D4) (TwistTag.D4.perm ^ (index : ℕ)) 0
    rw [← hseed] at e
    have hroot : IsRoot Tag.D4
        (permLattice (τ := Tag.D4) (TwistTag.D4.perm ^ (index : ℕ)) (trialitySeed 0)) := by
      rw [e]
      exact IsRoot.basis _
    rw [burnsideF4h_invd4_absoluteRoot_eq hroot, e]
    exact le_iSup₂_of_le (Pi.single ((TwistTag.D4.perm ^ (index : ℕ)) 0) 1)
      ⟨_, TwistTag.D4.perm_pow_mem_orbit (by decide) _, rfl⟩ le_rfl
  obtain ⟨c, hc⟩ := exists_orbitX_eq (σ := σ.toRingHom) hspan hgΓ.2
  refine ⟨(c : K), ?_⟩
  rw [← hc]
  exact coe_orbitX_zero_d4 σ c

include hσ in
theorem burnsideF4h_invd4_x₁_mem_posRoot :
    d4x₁ K σ 1 ∈ trialityPositiveRoot K σ.toRingHom 0 := by
  have hpos : ((0 : Fin 6) = 0 ∨ (0 : Fin 6) = 2 ∨ (0 : Fin 6) = 3) := Or.inl rfl
  rw [trialityPositiveRoot, if_pos hpos]
  have hσ3 : σ.toRingHom ^ 3 = 1 :=
    RingHom.ext fun c => (ringHom_pow_three_apply σ.toRingHom c).trans (hσ c)
  have hmem := trialityOrbitProd_mem (σ := σ.toRingHom) (j := 0) hpos hσ3 1
  refine Subgroup.mem_inf.2 ⟨hmem.2, ?_⟩
  have hseed : trialitySeed 0 = trialityRoot 0 := by
    funext i; fin_cases i <;> rfl
  have hle : rootSpan TwistTag.D4.tag K
      (trialityOrbit 0 : Set (Fin TwistTag.D4.tag.rank → ℤ)) ≤
      ⨆ index : Fin 3, absoluteRoot Tag.D4 K
        (permLattice (τ := Tag.D4) (TwistTag.D4.perm ^ (index : ℕ)) (trialitySeed 0)) := by
    refine iSup₂_le fun β hβ => ?_
    rw [trialityOrbit, Finset.mem_coe, ← Finset.mem_coe, coe_diagramOrbit_D4] at hβ
    obtain ⟨h, rfl⟩ := hβ
    refine le_iSup_of_le h ?_
    rw [hseed]
    exact le_of_eq (burnsideF4h_invd4_absoluteRoot_eq (isRoot_trialityRoot 0 (h : ℕ)).1).symm
  exact hle hmem.1

include hσ in
theorem burnsideF4h_invd4_shortRoot_elements :
    ∀ a ∈ trialityShortRoot K σ.toRingHom, ∃ c : K,
      a = burnsideF4h_invd4_nS K * d4x₁ K σ c * (burnsideF4h_invd4_nS K)⁻¹ := by
  intro a ha
  unfold trialityShortRoot fixedWeylConjugate at ha
  induction ha using Subgroup.closure_induction with
  | mem e he =>
    obtain ⟨actor, -, hactor, g, hg, rfl⟩ := he
    obtain ⟨c, rfl⟩ := burnsideF4h_invd4_posRoot_zero σ hσ hg
    have hact : actor = burnsideF4h_invd4_wordUnit Tag.D4 K [2, 0, 1, 3] :=
      (burnsideF4h_invd4_eq_wordUnit_iff _ actor).1 hactor
    subst hact
    exact ⟨c, rfl⟩
  | one =>
    refine ⟨0, ?_⟩
    show (1 : ModGL TwistTag.D4.tag K) =
      burnsideF4h_invd4_nS K * d4x₁ K σ 0 * (burnsideF4h_invd4_nS K)⁻¹
    rw [d4x₁_zero]
    group
  | mul x y _ _ hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    refine ⟨c + c', ?_⟩
    show (burnsideF4h_invd4_nS K * d4x₁ K σ c * (burnsideF4h_invd4_nS K)⁻¹ *
        (burnsideF4h_invd4_nS K * d4x₁ K σ c' * (burnsideF4h_invd4_nS K)⁻¹) :
          ModGL TwistTag.D4.tag K) =
      burnsideF4h_invd4_nS K * d4x₁ K σ (c + c') * (burnsideF4h_invd4_nS K)⁻¹
    rw [d4x₁_add]
    group
  | inv x _ hx =>
    obtain ⟨c, rfl⟩ := hx
    refine ⟨-c, ?_⟩
    have h : d4x₁ K σ (-c) = (d4x₁ K σ c)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by rw [← d4x₁_add, add_neg_cancel, d4x₁_zero])
    show ((burnsideF4h_invd4_nS K * d4x₁ K σ c * (burnsideF4h_invd4_nS K)⁻¹)⁻¹ :
        ModGL TwistTag.D4.tag K) =
      burnsideF4h_invd4_nS K * d4x₁ K σ (-c) * (burnsideF4h_invd4_nS K)⁻¹
    rw [h]
    group

include hσ in
theorem burnsideF4h_invd4_d4Conj_x₁ {c : K} (hc : c ≠ 0) :
    d4Conj σ (d4x₁ K σ 1) (d4x₁ K σ c) := by
  obtain ⟨a, ha⟩ := exists_mul_self_eq_d4 c
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ha
    exact hc ha.symm
  refine ⟨_, trialityOuterTorus_mem_d4C σ hσ (Units.mk0 a ha0), ?_⟩
  rw [ho_conj_d4x₁, Units.val_mk0, mul_one, sq, ha]

include hσ in
theorem burnsideF4h_invd4_S_ne : ∃ b ∈ burnsideF4h_invd4_SC σ, b ≠ 1 := by
  have hn := burnsideF4h_invd4_nS_mem σ hσ
  rw [burnsideF4h_invd4_Gamma_eq σ hσ] at hn
  have hx : d4x₁ K σ 1 ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (d4x_short_mem σ (toRingHom_pow_three_d4 σ hσ) 1).1
  refine ⟨⟨burnsideF4h_invd4_nS K * d4x₁ K σ 1 * (burnsideF4h_invd4_nS K)⁻¹,
    mul_mem (mul_mem hn hx) (inv_mem hn)⟩, ?_, ?_⟩
  · refine Subgroup.mem_subgroupOf.2 ?_
    unfold trialityShortRoot fixedWeylConjugate
    exact Subgroup.subset_closure ⟨burnsideF4h_invd4_nS K,
      burnsideF4h_invd4_nS_mem σ hσ, burnsideF4h_invd4_coe_wordUnit _, d4x₁ K σ 1,
      burnsideF4h_invd4_x₁_mem_posRoot σ hσ, rfl⟩
  · intro h
    have h1 : burnsideF4h_invd4_nS K * d4x₁ K σ 1 * (burnsideF4h_invd4_nS K)⁻¹ = 1 := by
      have h' := Subtype.ext_iff.1 h
      exact h'
    have h2 : d4x₁ K σ 1 = 1 :=
      calc d4x₁ K σ 1 = (burnsideF4h_invd4_nS K)⁻¹ *
            (burnsideF4h_invd4_nS K * d4x₁ K σ 1 * (burnsideF4h_invd4_nS K)⁻¹) *
              burnsideF4h_invd4_nS K := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨g, -, hg⟩ := d4Conj_d4x₁_d4x₄ σ hσ (d := 1) one_ne_zero
    apply tC_ne_one σ hσ
    apply Subtype.ext
    show d4x₄ K σ 1 = 1
    rw [← hg, h2]
    group

include hσ in
theorem burnsideF4h_invd4_S_conj :
    ∀ b ∈ burnsideF4h_invd4_SC σ, b ≠ 1 → IsConj (tC σ hσ) b := by
  intro b hb hb1
  obtain ⟨c, hbc⟩ :=
    burnsideF4h_invd4_shortRoot_elements σ hσ _ (Subgroup.mem_subgroupOf.1 hb)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hb1
    apply Subtype.ext
    show (b : ModGL TwistTag.D4.tag K) = 1
    rw [hbc, d4x₁_zero]
    group
  obtain ⟨g, hg, hgt⟩ := d4Conj_trans σ (d4Conj_symm σ (burnsideF4h_invd4_d4Conj_x₁ σ hσ hc0))
    (d4Conj_d4x₁_d4x₄ σ hσ (d := 1) one_ne_zero)
  have hn := burnsideF4h_invd4_nS_mem σ hσ
  rw [burnsideF4h_invd4_Gamma_eq σ hσ] at hn
  refine isConj_iff.2 ⟨⟨burnsideF4h_invd4_nS K * g⁻¹, mul_mem hn (inv_mem hg)⟩, ?_⟩
  apply Subtype.ext
  show burnsideF4h_invd4_nS K * g⁻¹ * d4x₄ K σ 1 * (burnsideF4h_invd4_nS K * g⁻¹)⁻¹ =
    (b : ModGL TwistTag.D4.tag K)
  rw [hbc, ← hgt]
  group

end RootTraces

end Model

section


open CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ExceptionalRoots CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.Quasithin.H13.F431.D4q.Loc CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley in
theorem burnsideF4h_inv_D4tw (degree : ℕ) (E : Type) [Group E] (core : Subgroup E)
    (chart : ChF.NativeChart .D4tw 2 degree core) :
    ∃ long ∈ chart.longRoot, ∃ short ∈ chart.shortRoot,
      long ≠ 1 ∧ long * long = 1 ∧ short ≠ 1 ∧ short * short = 1 ∧
      (¬ ∃ conjugator ∈ core, conjugator * long * conjugator⁻¹ = short) ∧
      (∀ element : E, chart.RootInvolution false element ↔
        element ∈ core ∧ ∃ conjugator ∈ core,
          conjugator * element * conjugator⁻¹ = long) ∧
      (∀ element : E, chart.RootInvolution true element ↔
        element ∈ core ∧ ∃ conjugator ∈ core,
          conjugator * element * conjugator⁻¹ = short) ∧
      (∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
        chart.RootInvolution false element ∨ chart.RootInvolution true element) := by
  rcases chart.coordinates with
    ⟨c, hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, -, -, K, fK, finK, sigma, scope, marking, -, -, -, h4, h5⟩ |
    ⟨-, exponent, K, fK, finK, charK, scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · cases c <;> simp [classicalKind] at hk
  · cases hk
  · cases hk
  · obtain ⟨-, hf, hK, hσ⟩ := scope
    obtain ⟨σ, rfl⟩ : ∃ σ : K ≃+* K, σ.toRingHom = sigma :=
      ⟨RingEquiv.ofBijective sigma
        ⟨sigma.injective, Finite.surjective_of_injective sigma.injective⟩, rfl⟩
    have hσ' : ∀ c, σ c = c ^ (2 ^ degree) := hσ
    have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ'
    have hK3 : Nat.card K = 2 ^ (3 * degree) := by rw [hK, ← pow_mul, mul_comm]
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hK3
    obtain ⟨-, -, -, -, -, hD, hZ, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ'
    obtain ⟨e, he⟩ := burnsideF4h_invd4_exists_derivedEquiv _ _ hD hZ
    let ψ : Cm σ ≃* core := e.symm.trans marking
    have hmap : ∀ P : Subgroup (ModGL TwistTag.D4.tag K),
        (derivedImage (twistedFixedGroup TwistTag.D4 K σ.toRingHom) P).map
            marking.toMonoidHom =
          (P.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map ψ.toMonoidHom := by
      intro P
      have hcomp : ψ.toMonoidHom.comp e.toMonoidHom = marking.toMonoidHom := by
        refine MonoidHom.ext fun q => ?_
        simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]
      rw [← burnsideF4h_invd4_map_derivedImage _ _ P hD e he, Subgroup.map_map, hcomp]
    have hL : chart.longRoot =
        ((burnsideF4h_invd4_LC σ).map ψ.toMonoidHom).map core.subtype :=
      h4.trans (congrArg (fun X => X.map core.subtype) (hmap _))
    have hS : chart.shortRoot =
        ((burnsideF4h_invd4_SC σ).map ψ.toMonoidHom).map core.subtype :=
      h5.trans (congrArg (fun X => X.map core.subtype) (hmap _))
    exact burnsideF4h_invd4_of_model chart (by decide) ψ _ _ (zC σ) (tC σ hσ3)
      (zC_mul_self σ) (tC_mul_self σ hσ3) (burnsideF4h_invd4_cover σ hσ3)
      (burnsideF4h_invd4_not_conj σ hσ3) (burnsideF4h_invd4_L_ne σ hσ3)
      (burnsideF4h_invd4_L_conj σ hσ3) (burnsideF4h_invd4_S_ne σ hσ3)
      (burnsideF4h_invd4_S_conj σ hσ3) hL hS
  · cases hk
  · cases hk

end

end PartBurnsideF4hInvD4

section PartBurnsideF4hAsm

theorem burnsideF4h_isLieParabolics_map {E M : Type} [Group E] [Group M] (φ : M →* E)
    (hφ : Function.Injective φ) {p : ℕ} {B P₁ P₂ : Subgroup M}
    (h : ChF.IsLieParabolics p (⊤ : Subgroup M) B P₁ P₂) :
    ChF.IsLieParabolics p ((⊤ : Subgroup M).map φ) (B.map φ) (P₁.map φ) (P₂.map φ) := by
  obtain ⟨⟨S, ⟨hSle, hSp, hSidx⟩, hB⟩, hne, hinf, hmax⟩ := h
  have hcm : ∀ A : Subgroup E, A ≤ (⊤ : Subgroup M).map φ → A = (A.comap φ).map φ := by
    intro A hA
    rw [Subgroup.map_comap_eq]
    rw [← MonoidHom.range_eq_map] at hA
    exact (inf_eq_right.2 hA).symm
  refine ⟨⟨S.map φ, ⟨Subgroup.map_mono hSle, hSp.map φ, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.relIndex_map_map_of_injective _ _ hφ]
    exact hSidx
  · ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine Subgroup.mem_inf.2 ⟨⟨b, Subgroup.mem_top _, rfl⟩, ?_⟩
      have hb' : b ∈ (⊤ : Subgroup M) ⊓ Subgroup.normalizer (S : Set M) := hB ▸ hb
      have hbN : b ∈ Subgroup.normalizer (S : Set M) := (Subgroup.mem_inf.1 hb').2
      exact Subgroup.le_normalizer_map φ ⟨b, hbN, rfl⟩
    · intro hx
      obtain ⟨⟨m, -, rfl⟩, hxN⟩ := Subgroup.mem_inf.1 hx
      refine ⟨m, ?_, rfl⟩
      rw [hB]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro s
      have h1 := Subgroup.mem_normalizer_iff.1 hxN (φ s)
      rw [← map_mul, ← map_inv, ← map_mul] at h1
      have h2 : φ s ∈ S.map φ ↔ s ∈ S := by
        constructor
        · rintro ⟨t, ht, hts⟩
          rwa [← hφ hts]
        · intro hs
          exact ⟨s, hs, rfl⟩
      have h3 : φ (m * s * m⁻¹) ∈ S.map φ ↔ m * s * m⁻¹ ∈ S := by
        constructor
        · rintro ⟨t, ht, hts⟩
          rwa [← hφ hts]
        · intro hs
          exact ⟨_, hs, rfl⟩
      rw [← h2, h1, h3]
  · exact fun e => hne (Subgroup.map_injective hφ e)
  · rw [← Subgroup.map_inf_eq _ _ _ hφ, hinf]
  · intro Q
    have hP1 := (hmax P₁).2 (Or.inl rfl)
    have hP2 := (hmax P₂).2 (Or.inr rfl)
    have hTopInj : ∀ R : Subgroup M, R.map φ = (⊤ : Subgroup M).map φ → R = ⊤ :=
      fun R hR => Subgroup.map_injective hφ hR
    constructor
    · rintro ⟨hBQ, hQH, hQne, hQmax⟩
      have hQe := hcm Q hQH
      set Q₀ := Q.comap φ with hQ₀
      have hBQ₀ : B ≤ Q₀ := Subgroup.map_le_iff_le_comap.1 hBQ
      have hQ₀ne : Q₀ ≠ ⊤ := by
        intro e
        apply hQne
        rw [hQe, e]
      have hQ₀max : ∀ R₀ : Subgroup M, Q₀ < R₀ → R₀ ≤ ⊤ → R₀ = ⊤ := by
        rintro R₀ hR₀ -
        have hlt : Q < R₀.map φ := by
          refine lt_of_le_of_ne ?_ ?_
          · rw [hQe]
            exact Subgroup.map_mono hR₀.le
          · intro e
            have : Q₀ = R₀ := Subgroup.map_injective hφ (by rw [← hQe, e])
            exact hR₀.ne this
        exact hTopInj _ (hQmax _ hlt (Subgroup.map_mono le_top))
      rcases (hmax Q₀).1 ⟨hBQ₀, le_top, hQ₀ne, hQ₀max⟩ with e | e
      · exact Or.inl (by rw [hQe, e])
      · exact Or.inr (by rw [hQe, e])
    · intro hQ
      have key : ∀ P : Subgroup M, (B ≤ P ∧ P ≤ ⊤ ∧ P ≠ ⊤ ∧ ∀ R : Subgroup M, P < R → R ≤ ⊤ → R = ⊤) →
          (B.map φ ≤ P.map φ ∧ P.map φ ≤ (⊤ : Subgroup M).map φ ∧ P.map φ ≠ (⊤ : Subgroup M).map φ ∧
            ∀ R : Subgroup E, P.map φ < R → R ≤ (⊤ : Subgroup M).map φ → R = (⊤ : Subgroup M).map φ) := by
        rintro P ⟨hBP, -, hPne, hPmax⟩
        refine ⟨Subgroup.map_mono hBP, Subgroup.map_mono le_top, fun e => hPne (hTopInj _ e), ?_⟩
        intro R hR hRH
        have hRe := hcm R hRH
        have hlt : P < R.comap φ := by
          refine lt_of_le_of_ne (Subgroup.map_le_iff_le_comap.1 hR.le) ?_
          intro e
          apply hR.ne
          rw [hRe, ← e]
        have := hPmax _ hlt le_top
        rw [hRe, this]
      rcases hQ with rfl | rfl
      · exact key _ hP1
      · exact key _ hP2

theorem burnsideF4h_le_normalizer_map {E M : Type} [Group E] [Group M] (φ : M →* E)
    {P L : Subgroup M} (h : P ≤ Subgroup.normalizer (L : Set M)) :
    P.map φ ≤ Subgroup.normalizer ((L.map φ : Subgroup E) : Set E) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.le_normalizer_map φ ⟨x, h hx, rfl⟩


theorem burnsideF4h_map_subtype_top {E : Type} [Group E] (core : Subgroup E) :
    (⊤ : Subgroup ↥core).map core.subtype = core := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem burnsideF4h_isLieParabolics_marking {E M : Type} [Group E] [Group M] (core : Subgroup E)
    (marking : M ≃* ↥core) {p : ℕ} {B P₁ P₂ : Subgroup M}
    (h : ChF.IsLieParabolics p (⊤ : Subgroup M) B P₁ P₂) :
    ChF.IsLieParabolics p core ((B.map marking.toMonoidHom).map core.subtype)
      ((P₁.map marking.toMonoidHom).map core.subtype) ((P₂.map marking.toMonoidHom).map core.subtype) := by
  have hinj : Function.Injective (core.subtype.comp marking.toMonoidHom) :=
    core.subtype_injective.comp marking.injective
  have hmap := burnsideF4h_isLieParabolics_map _ hinj h
  have htop : (⊤ : Subgroup M).map (core.subtype.comp marking.toMonoidHom) = core := by
    rw [← Subgroup.map_map, Subgroup.map_top_of_surjective _ marking.surjective,
      burnsideF4h_map_subtype_top]
  rw [htop] at hmap
  simpa only [Subgroup.map_map] using hmap

theorem burnsideF4h_le_normalizer_marking {E M : Type} [Group E] [Group M] (core : Subgroup E)
    (marking : M ≃* ↥core) {P L : Subgroup M} (h : P ≤ Subgroup.normalizer (L : Set M)) :
    (P.map marking.toMonoidHom).map core.subtype ≤
      Subgroup.normalizer (((L.map marking.toMonoidHom).map core.subtype : Subgroup E) : Set E) :=
  burnsideF4h_le_normalizer_map core.subtype (burnsideF4h_le_normalizer_map marking.toMonoidHom h)

theorem burnsideF4h_normalizer_of_parent {M N : Type} [Group M] [Group N] (incl : M →* N)
    (hinj : Function.Injective incl) {P L : Subgroup M} {P' L' : Subgroup N}
    (hP : P.map incl = incl.range ⊓ P') (hL : L.map incl = incl.range ⊓ L')
    (h : P' ≤ Subgroup.normalizer (L' : Set N)) : P ≤ Subgroup.normalizer (L : Set M) := by
  intro x hx
  have hxP' : incl x ∈ P' := (Subgroup.mem_inf.1 (hP ▸ Subgroup.mem_map_of_mem incl hx)).2
  have hN := Subgroup.mem_normalizer_iff.1 (h hxP')
  have hmem : ∀ y : M, y ∈ L ↔ incl y ∈ L' := by
    intro y
    have h1 : y ∈ L ↔ incl y ∈ L.map incl :=
      ⟨fun hy => Subgroup.mem_map_of_mem incl hy, fun ⟨t, ht, hts⟩ => by rwa [← hinj hts]⟩
    rw [h1, hL, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨⟨y, rfl⟩, h⟩⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [hmem y, hmem (x * y * x⁻¹), map_mul, map_mul, map_inv]
  exact hN (incl y)

theorem burnsideF4h_compat_of_models
    (hcl : ∀ (c : ChF.ClassicalRoots.Kind) (p e : ℕ) (H : Type) [Group H]
      (m : ChF.ClassicalRoots.Marking c p e H),
      ChF.IsLieParabolics p (⊤ : Subgroup H) m.borel (m.parabolic false) (m.parabolic true) ∧
      (c ≠ .L3 → m.parabolic false ≤ Subgroup.normalizer (m.root .longOne false : Set H)))
    (hg2 : ∀ (K : Type) [Field K], ChF.G2Native.fullCompatibilityGoal K)
    (hg2s : ∀ (K : Type) [Field K], ChF.G2Native.smallCompatibilityGoal K)
    (hg2n : ∀ (K : Type) [Field K], Nat.card K = 2 →
      ChF.G2Native.smallLocal K (ChF.G2Native.pointParabolic K) ≤
        Subgroup.normalizer ((ChF.G2Native.smallLocal K (ChF.G2Native.longRoot K) :
          Subgroup (ChF.G2Native.SmallModel K)) : Set (ChF.G2Native.SmallModel K)))
    (htri : ∀ (K : Type) [Field K] [Finite K] (sigma : K →+* K) (prime degree : ℕ),
      ChF.ExceptionalRoots.TrialityScope K sigma prime degree →
      ChF.IsLieParabolics prime (⊤ : Subgroup (CFSG.Blueprint.DerivedCentralQuotient
        (CFSG.Blueprint.twistedFixedGroup .D4 K sigma)))
        (ChF.NativeFrame.triality K sigma).borel (ChF.NativeFrame.triality K sigma).pointParabolic
        (ChF.NativeFrame.triality K sigma).lineParabolic ∧
      (ChF.NativeFrame.triality K sigma).pointParabolic ≤
        Subgroup.normalizer (((ChF.NativeFrame.triality K sigma).longRoot : Subgroup _) : Set _))
    (hree : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (exponent : ℕ),
      ChF.ExceptionalRoots.ReeScope K exponent →
      ChF.IsLieParabolics 2 (⊤ : Subgroup (ChF.ExceptionalRoots.reeGroup K exponent ⧸
        Subgroup.center (ChF.ExceptionalRoots.reeGroup K exponent)))
        (ChF.NativeFrame.ree K exponent).borel (ChF.NativeFrame.ree K exponent).pointParabolic
        (ChF.NativeFrame.ree K exponent).lineParabolic ∧
      (ChF.NativeFrame.ree K exponent).pointParabolic ≤
        Subgroup.normalizer (((ChF.NativeFrame.ree K exponent).longRoot : Subgroup _) : Set _))
    (htits : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], ChF.NativeFrame.titsParentAssemblyGoal K) :
    ChF.NativeChartCompatibilityGoal := by
  intro kind prime degree E _ core chart
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, sigma, scope, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hp, exponent, K, fK, finK, charK, scope,
      ⟨hk, hd, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, hd, he, marking, h1, h2, h3, h4, h5⟩⟩
  ·
    subst hk
    obtain ⟨hc1, hc2⟩ := hcl c prime degree ↥core marking
    have hmap := burnsideF4h_isLieParabolics_map core.subtype core.subtype_injective hc1
    rw [burnsideF4h_map_subtype_top] at hmap
    refine ⟨?_, fun hne => ?_⟩
    · rw [h1, h2, h3]
      exact hmap
    · have hc3 : c ≠ .L3 := fun e => hne (by rw [e]; rfl)
      rw [if_neg hc3] at h4
      rw [h2, h4]
      exact burnsideF4h_le_normalizer_map core.subtype (hc2 hc3)
  ·
    subst hk
    letI := fK
    obtain ⟨hl, hn, -⟩ := hg2 K prime degree hp hd card
    refine ⟨?_, fun _ => ?_⟩
    · rw [h1, h2, h3]
      exact burnsideF4h_isLieParabolics_marking core marking hl
    · rw [h2, h4]
      exact burnsideF4h_le_normalizer_marking core marking hn
  ·
    subst hk
    subst hp
    letI := fK
    obtain ⟨hl, -, -⟩ := hg2s K card
    refine ⟨?_, fun _ => ?_⟩
    · rw [h1, h2, h3]
      exact burnsideF4h_isLieParabolics_marking core marking hl
    · rw [h2, h4]
      exact burnsideF4h_le_normalizer_marking core marking (hg2n K card)
  ·
    subst hk
    letI := fK
    letI := finK
    obtain ⟨hl, hn1⟩ := htri K sigma prime degree scope
    refine ⟨?_, fun _ => ?_⟩
    · rw [h1, h2, h3]
      exact burnsideF4h_isLieParabolics_marking core marking hl
    · rw [h2, h4]
      exact burnsideF4h_le_normalizer_marking core marking hn1
  ·
    subst hk
    subst hp
    letI := fK
    letI := finK
    letI := charK
    obtain ⟨hl, hn1⟩ := hree K exponent scope
    refine ⟨?_, fun _ => ?_⟩
    · rw [h1, h2, h3]
      exact burnsideF4h_isLieParabolics_marking core marking hl
    · rw [h2, h4]
      exact burnsideF4h_le_normalizer_marking core marking hn1
  ·
    subst hk
    subst hp
    subst he
    letI := fK
    letI := finK
    letI := charK
    obtain ⟨hl, -, -, incl, hinj, -, -, -, hP, -, hL, -, -, -, -⟩ := htits K scope
    obtain ⟨-, hn1⟩ := hree K 0 scope
    refine ⟨?_, fun _ => ?_⟩
    · rw [h1, h2, h3]
      exact burnsideF4h_isLieParabolics_marking core marking hl
    · rw [h2, h4]
      exact burnsideF4h_le_normalizer_marking core marking
        (burnsideF4h_normalizer_of_parent incl hinj hP hL hn1)


theorem burnsideF4h_hcl_of
    (hL3 : ∀ (p e : ℕ) (H : Type) [Group H] (m : ChF.ClassicalRoots.Marking .L3 p e H),
      ChF.IsLieParabolics p (⊤ : Subgroup H) m.borel (m.parabolic false) (m.parabolic true))
    (hSp4 : ∀ (p e : ℕ) (H : Type) [Group H] (m : ChF.ClassicalRoots.Marking .Sp4 p e H),
      ChF.IsLieParabolics p (⊤ : Subgroup H) m.borel (m.parabolic false) (m.parabolic true) ∧
      m.parabolic false ≤ Subgroup.normalizer (m.root .longOne false : Set H))
    (hU4 : ∀ (p e : ℕ) (H : Type) [Group H] (m : ChF.ClassicalRoots.Marking .U4 p e H),
      ChF.IsLieParabolics p (⊤ : Subgroup H) m.borel (m.parabolic false) (m.parabolic true) ∧
      m.parabolic false ≤ Subgroup.normalizer (m.root .longOne false : Set H))
    (hU5 : ∀ (p e : ℕ) (H : Type) [Group H] (m : ChF.ClassicalRoots.Marking .U5 p e H),
      ChF.IsLieParabolics p (⊤ : Subgroup H) m.borel (m.parabolic false) (m.parabolic true) ∧
      m.parabolic false ≤ Subgroup.normalizer (m.root .longOne false : Set H)) :
    ∀ (c : ChF.ClassicalRoots.Kind) (p e : ℕ) (H : Type) [Group H]
      (m : ChF.ClassicalRoots.Marking c p e H),
      ChF.IsLieParabolics p (⊤ : Subgroup H) m.borel (m.parabolic false) (m.parabolic true) ∧
      (c ≠ .L3 → m.parabolic false ≤ Subgroup.normalizer (m.root .longOne false : Set H)) := by
  intro c p e H _ m
  cases c with
  | L3 => exact ⟨hL3 p e H m, fun h => absurd rfl h⟩
  | Sp4 => exact ⟨(hSp4 p e H m).1, fun _ => (hSp4 p e H m).2⟩
  | U4 => exact ⟨(hU4 p e H m).1, fun _ => (hU4 p e H m).2⟩
  | U5 => exact ⟨(hU5 p e H m).1, fun _ => (hU5 p e H m).2⟩

@[expose] def burnsideF4h_InvB {kind : ChF.GLKind} {degree : ℕ} {E : Type} [Group E]
    {core : Subgroup E} (chart : ChF.NativeChart kind 2 degree core) : Prop :=
  ∃ long ∈ chart.longRoot, ∃ short ∈ chart.shortRoot,
    long ≠ 1 ∧ long * long = 1 ∧ short ≠ 1 ∧ short * short = 1 ∧
    (¬ ∃ conjugator ∈ core, conjugator * long * conjugator⁻¹ = short) ∧
    (∀ element : E, chart.RootInvolution false element ↔
      element ∈ core ∧ ∃ conjugator ∈ core, conjugator * element * conjugator⁻¹ = long) ∧
    (∀ element : E, chart.RootInvolution true element ↔
      element ∈ core ∧ ∃ conjugator ∈ core, conjugator * element * conjugator⁻¹ = short) ∧
    (∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
      chart.RootInvolution false element ∨ chart.RootInvolution true element)

theorem burnsideF4h_involutions_of_kinds
    (hG2d : ∀ (degree : ℕ) (E : Type) [Group E] (core : Subgroup E)
      (chart : ChF.NativeChart .G2d 2 degree core),
      (∃ representative ∈ chart.longRoot, representative ≠ 1 ∧ representative * representative = 1) ∧
        ∀ element : E, element ∈ core → element ≠ 1 → element * element = 1 →
          chart.RootInvolution false element)
    (hD4 : ∀ (degree : ℕ) (E : Type) [Group E] (core : Subgroup E)
      (chart : ChF.NativeChart .D4tw 2 degree core), burnsideF4h_InvB chart)
    (hF4 : ∀ (degree : ℕ) (E : Type) [Group E] (core : Subgroup E)
      (chart : ChF.NativeChart .F4tw 2 degree core), burnsideF4h_InvB chart)
    (hTits : ∀ (degree : ℕ) (E : Type) [Group E] (core : Subgroup E)
      (chart : ChF.NativeChart .Tits 2 degree core), burnsideF4h_InvB chart) :
    ChF.ExceptionalChartInvolutionGoal := by
  intro kind degree E _ core chart
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · subst hk
    exact hG2d degree E core chart
  · rcases hk with rfl | rfl | rfl
    · exact hD4 degree E core chart
    · exact hF4 degree E core chart
    · exact hTits degree E core chart

end PartBurnsideF4hAsm


section


theorem ChF.NativeFrame.reeOrderedLocals (K : Type) [Field K] [Finite K] [CharP K 2] :
    ChF.NativeFrame.reeOrderedLocalsGoal K :=
  burnsideF4h_reeOrderedLocals_core K

end

section


theorem ChF.NativeFrame.trialityOrderedLocals (K : Type) [Field K] [Finite K] :
    ChF.NativeFrame.trialityOrderedLocalsGoal K :=
  burnsideF4h_trialityOrderedLocals_core K

end

section


theorem ChF.NativeFrame.titsParentAssembly (K : Type) [Field K] [Finite K] [CharP K 2] :
    ChF.NativeFrame.titsParentAssemblyGoal K :=
  burnsideF4h_titsParentAssembly K

end

section


theorem ChF.exceptionalChartInvolutions : ChF.ExceptionalChartInvolutionGoal :=
  burnsideF4h_involutions_of_kinds burnsideF4h_inv_G2d burnsideF4h_inv_D4tw
    burnsideF4h_inv_F4tw burnsideF4h_inv_Tits

end

section


theorem ChF.nativeChartCompatibility : ChF.NativeChartCompatibilityGoal :=
  burnsideF4h_compat_of_models
    (burnsideF4h_hcl_of burnsideF4h_cl_L3 burnsideF4h_cl_Sp4 burnsideF4h_clu_U4
      burnsideF4h_clu_U5)
    burnsideF4h_g2_full burnsideF4h_g2_small burnsideF4h_g2_small_normalizer
    (fun K _ _ sigma prime degree scope => by
      obtain ⟨h1, -, -, h4⟩ := burnsideF4h_trialityOrderedLocals_core K sigma prime degree scope
      exact ⟨h1, h4⟩)
    (fun K _ _ _ exponent scope => by
      obtain ⟨h1, -, -, h4⟩ := burnsideF4h_reeOrderedLocals_core K exponent scope
      exact ⟨h1, h4⟩)
    burnsideF4h_titsParentAssembly

end

end CFSG.ASVolI
