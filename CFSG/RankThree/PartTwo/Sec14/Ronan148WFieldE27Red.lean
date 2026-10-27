module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WFieldE27Amb
import CFSG.RankThree.PartTwo.Sec14.Ronan148WFieldE27Cube
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofAut
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldB
import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

local notation "pmk" => Matrix.ProjGenLinGroup.mk

section Stab

variable {S : Type*} [Group S]

def stabSub (T : Subgroup S) : Subgroup (MulAut S) where
  carrier := {α | ∀ t ∈ T, α t ∈ T ∧ α⁻¹ t ∈ T}
  one_mem' t ht := ⟨ht, ht⟩
  mul_mem' {α β} hα hβ t ht := ⟨(hα _ (hβ t ht).1).1, by
    rw [_root_.mul_inv_rev, MulAut.mul_apply]
    exact (hβ _ (hα t ht).2).2⟩
  inv_mem' {α} hα t ht := ⟨(hα t ht).2, by
    rw [inv_inv]
    exact (hα t ht).1⟩

theorem mem_stabSub_of_pow_three {T : Subgroup S} {α : MulAut S} (hα3 : α ^ 3 = 1)
    (hα : ∀ t ∈ T, α t ∈ T) : α ∈ stabSub T := by
  have hinv : α⁻¹ = α * α := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ', hα3]
  intro t ht
  refine ⟨hα t ht, ?_⟩
  rw [hinv, MulAut.mul_apply]
  exact hα _ (hα t ht)

end Stab

section Transport

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal] {S : Type*} [Group S]

theorem slAct_mem_map_of_slAct_mem (e e' : L ≃* S) (T : Subgroup S) (g : G)
    (hg : ∀ t ∈ T, slAct e' ⟨g, mem_normalizer_of_normal g⟩ t ∈ T) :
    ∀ t ∈ (T.map e'.symm.toMonoidHom).map e.toMonoidHom,
      slAct e ⟨g, mem_normalizer_of_normal g⟩ t ∈
        (T.map e'.symm.toMonoidHom).map e.toMonoidHom := by
  rintro _ ⟨_, ⟨t', ht', rfl⟩, rfl⟩
  refine ⟨e'.symm (slAct e' ⟨g, mem_normalizer_of_normal g⟩ t'), ⟨_, hg t' ht', rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, slAct_apply, MulEquiv.symm_apply_apply]

end Transport

section Proj

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_two_subgroup_proj (hK : PiField π p f K) {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {ψ : K ≃+* K} {σ x : G} {y : GL (Fin 3) K}
    (hσψ : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hs⟩) :
        projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk (frobGL ψ s))
    (hy : IsPGLAtP e x y) {U : Subgroup (GL (Fin 3) K)} (hU : U ≤ slPi π 3 (p ^ f) K)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hUs : ∃ u ∈ U, u ∉ StatedScalars (Fin 3) K)
    (hUψ : ∀ u ∈ U, frobGL ψ u ∈ U) (hUy : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    ∃ T : Subgroup (projImage (slPi π 3 (p ^ f) K)), T ≠ ⊥ ∧ IsPGroup 2 T ∧
      (∀ t ∈ T, slAct e ⟨σ, mem_normalizer_of_normal σ⟩ t ∈ T) ∧
      (∀ t ∈ T, slAct e ⟨x, mem_normalizer_of_normal x⟩ t ∈ T) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  refine ⟨(U.subgroupOf (slPi π 3 (p ^ f) K)).map (projOf _), ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu, hus⟩ := hUs
    have hmem : projOf _ ⟨u, hU hu⟩ ∈ (U.subgroupOf (slPi π 3 (p ^ f) K)).map (projOf _) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hus ((mem_ker_projOf _).mp hmem)
  · rintro ⟨t, ht⟩
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    have hs2 : s ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hU2 _ (Subgroup.mem_subgroupOf.mp hs))
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow, hs2, map_one]
  · intro t ht
    obtain ⟨⟨s, hsl⟩, hs, rfl⟩ := Subgroup.mem_map.mp ht
    have h1 : slAct e ⟨σ, mem_normalizer_of_normal σ⟩ (projOf _ ⟨s, hsl⟩) =
        projOf _ ⟨frobGL ψ s, frobGL_mem_slPi hK ψ hsl⟩ :=
      Subtype.ext (by rw [hσψ, coe_projOf])
    rw [h1]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (hUψ s (Subgroup.mem_subgroupOf.mp hs)))
  · intro t ht
    obtain ⟨⟨s, hsl⟩, hs, rfl⟩ := Subgroup.mem_map.mp ht
    rw [slAct_projOf_of_isPGLAtP hπ hy hsl]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (hUy s (Subgroup.mem_subgroupOf.mp hs)))

end Proj

section Model

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_two_local_model_of (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f)
    (hU : ∀ {τ : K}, τ ^ 3 = 1 → τ ≠ 1 → ∀ {ψ : K ≃+* K}, ψ τ = τ → ∀ {y : GL (Fin 3) K},
      y ∈ glPi π 3 (p ^ f) K → y ^ 3 = 1 → y ∉ StatedScalars (Fin 3) K → frobGL ψ y = y →
      ∃ U : Subgroup (GL (Fin 3) K), U ≤ slPi π 3 (p ^ f) K ∧ (∀ u ∈ U, u ^ 2 = 1) ∧
        (∃ u ∈ U, u ∉ StatedScalars (Fin 3) K) ∧ (∀ u ∈ U, frobGL ψ u ∈ U) ∧
        (∀ u ∈ U, y * u * y⁻¹ ∈ U))
    (E : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K))))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) :
    ∃ B : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K))), B ≤ E ∧ Nat.card B = 9 ∧
      ∃ T : Subgroup (projImage (slPi π 3 (p ^ f) K)), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        ∀ b ∈ B, ∀ t ∈ T, b t ∈ T := by
  classical
  have := hK.finite
  haveI : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) (QuotientGroup.mk'_surjective _)
  haveI : Finite (MulAut (projImage (slPi π 3 (p ^ f) K))) :=
    Finite.of_injective (fun α : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
      (α : projImage (slPi π 3 (p ^ f) K) → projImage (slPi π 3 (p ^ f) K)))
      fun _ _ h => MulEquiv.ext (congrFun h)
  haveI := Sec13.isPerfect_projImage_slPi hK hq2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3K := hK.three_ne_zero hq
  set L := CFSG.ComponentClassification.OuterAutomorphisms.inner
    (projImage (slPi π 3 (p ^ f) K)) with hLdef
  set e₀ := innerEquiv hK hq hq2 with he₀
  have hC : ∀ β ∈ Subgroup.centralizer (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K)))),
      β = 1 := by
    intro β hβ
    refine MulEquiv.ext fun m => ?_
    have h1 := Subgroup.mem_centralizer_iff.mp hβ (MulAut.conj m) ⟨m, rfl⟩
    have h2 : MulAut.conj (β m) = MulAut.conj m := by
      rw [mulAut_conj_apply_eq, ← h1, mul_inv_cancel_right]
    exact conj_injective_projImage hK hq hq2 h2
  have hinnerpgl : ∀ (e : L ≃* projImage (slPi π 3 (p ^ f) K)),
      ∀ b ∈ L ⊔ Subgroup.centralizer (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K)))),
        ∃ y, IsPGLAtP e b y := by
    intro e b hb
    obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
    exact ⟨_, isPGLAtP_mul e (isPGLAtP_of_mem e hπ hl hs hse.symm)
      (isPGLAtP_of_mem_centralizer e hu)⟩
  obtain ⟨σ, hσE, hσP⟩ : ∃ σ ∈ E, ¬ ∃ y, IsPGLAtP e₀ σ y := by
    by_contra hall
    push Not at hall
    have hcard := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (e := e₀) (A' := E)
      (hA' := hall)
    have hinf : E ⊓ Subgroup.centralizer (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K)))) =
        ⊥ := by
      rw [eq_bot_iff]
      intro β hβ
      exact Subgroup.mem_bot.mpr (hC β hβ.2)
    rw [hinf, Subgroup.card_bot, one_mul] at hcard
    have hle := card_le_nine_of_comm h3K hτ hτ1 (pglHomP hK hq E hall).range
      (range_pglHomP_comm (hA' := hall) fun a ha b hb =>
        congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      (range_pglHomP_pow (hA' := hall) fun b hb => hE.2 b hb)
    omega
  have hσ3 : σ ^ 3 = 1 := hE.2 σ hσE
  rcases Sec11.KS11LieProof.aut_pgl_or_field hK hq2 (slAct e₀ ⟨σ, mem_normalizer_of_normal σ⟩)
      (slAct_pow_three_of e₀ (mem_normalizer_of_normal σ) hσ3) with
    ⟨y, hy, hys⟩ | ⟨f₀, hf, ψ, hψa, g, hg, hga⟩
  · exact absurd ⟨y, hy, hys⟩ hσP
  obtain ⟨φ, hφ, hφ3⟩ := exists_frob hK hf
  have hψ : ψ = φ ∨ ψ = φ ^ 2 := eq_or_eq_sq_of_pow hφ hψa
  obtain ⟨e', he'⟩ := exists_normalized_fieldP hK hq hf hφ hφ3 hψ e₀ hσ3 hg hga
  have hσB : σ ∉ L ⊔ Subgroup.centralizer (L : Set (MulAut (projImage (slPi π 3 (p ^ f) K)))) :=
    fun h => hσP (hinnerpgl e₀ σ h)
  obtain ⟨hlift, hcardE⟩ :=
    fieldB_structure_of_elemAbelian hK hq hq2 hf hφ hφ3 hψ e' hE hσE hσB he'
  rw [hE27] at hcardE
  obtain ⟨x, hxB₀, hx1, y, hy, hyψ, hy3⟩ :=
    exists_split_lift hK hq hf hφ hφ3 hψ (hE.mono inf_le_left) (by omega) hlift
  have hys : y ∉ StatedScalars (Fin 3) K := fun h =>
    hx1 (hC x (mem_centralizer_of_isPGLAtP_scalar hy h))
  have hψτ : ψ τ = τ := by
    rw [fixed_iff_of_sq hφ3 hψ, hφ]
    have hqq : p ^ f = (p ^ f₀) ^ 3 := by rw [hf, pow_mul']
    have hq₀ : ModThree π (p ^ f₀) := modThree_of_cube (hqq ▸ hq)
    obtain ⟨k, hk⟩ : ∃ k, piCard π (p ^ f₀) = 3 * k + 1 := by
      cases π
      · change p ^ f₀ % 3 = 2 at hq₀
        refine ⟨(p ^ f₀ * p ^ f₀) / 3, ?_⟩
        change (p ^ f₀) ^ 2 = _
        have : (p ^ f₀) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq₀]
        rw [pow_two] at this ⊢
        omega
      · change p ^ f₀ % 3 = 1 at hq₀
        exact ⟨p ^ f₀ / 3, by change p ^ f₀ = _; omega⟩
    rw [hk, pow_succ, pow_mul, hτ, one_pow, one_mul]
  obtain ⟨U, hUsl, hU2, hUs, hUψ, hUy⟩ := hU hτ hτ1 hψτ hy.1 hy3 hys hyψ
  obtain ⟨T', hT'ne, hT'2, hT'σ, hT'x⟩ :=
    exists_two_subgroup_proj hK he' hy hUsl hU2 hUs hUψ hUy
  have hpres : ∀ β : MulAut (projImage (slPi π 3 (p ^ f) K)),
      (∀ t ∈ T', slAct e' ⟨β, mem_normalizer_of_normal β⟩ t ∈ T') →
        ∀ t ∈ (T'.map e'.symm.toMonoidHom).map e₀.toMonoidHom,
          β t ∈ (T'.map e'.symm.toMonoidHom).map e₀.toMonoidHom := by
    intro β hβ t ht
    have h1 := slAct_mem_map_of_slAct_mem e₀ e' T' β hβ t ht
    rwa [he₀, slAct_innerEquiv] at h1
  have hx3 : x ^ 3 = 1 := hE.2 x hxB₀.1
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hσ1 : σ ≠ 1 := fun h =>
    hσP ⟨1, by rw [h]; exact isPGLAtP_of_mem_centralizer e₀ (Subgroup.one_mem _)⟩
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hσx : σ ∉ Subgroup.zpowers x := fun h =>
    hσB ((Subgroup.zpowers_le.mpr hxB₀.2) h)
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers σ = ⊥ := inf_zpowers_eq_bot hσ3 hσx
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers σ, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hE.1.is_comm.comm
      ⟨a, (Subgroup.zpowers_le.mpr hxB₀.1) ha⟩ ⟨b, (Subgroup.zpowers_le.mpr hσE) hb⟩)
  have hcardB := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hxo, hσo] at hcardB
  refine ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers σ,
    sup_le (Subgroup.zpowers_le.mpr hxB₀.1) (Subgroup.zpowers_le.mpr hσE), hcardB,
    (T'.map e'.symm.toMonoidHom).map e₀.toMonoidHom, ?_, (hT'2.map _).map _, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e₀.injective,
      Subgroup.map_eq_bot_iff_of_injective _ e'.symm.injective]
  · have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers σ ≤
        stabSub ((T'.map e'.symm.toMonoidHom).map e₀.toMonoidHom) :=
      sup_le (Subgroup.zpowers_le.mpr (mem_stabSub_of_pow_three hx3 (hpres x hT'x)))
        (Subgroup.zpowers_le.mpr (mem_stabSub_of_pow_three hσ3 (hpres σ hT'σ)))
    intro b hb t ht
    exact (hle hb t ht).1

end Model

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
