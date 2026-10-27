module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ
public import CFSG.LocalAnalysis.StandardType.GGTBJOmTauOm
public import CFSG.LocalAnalysis.StandardType.GGTBJOmPlaneIsometries
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Centralizer
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenSupp
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenConj
public import CFSG.LocalAnalysis.StandardType.GGTBJOmClass
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstarOddBT
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedShape
import CFSG.RankThree.PartOne.S15K.FamilyForms
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof

public section

namespace CFSG.StandardType.OrthTorus

open Module Multiplicative QuadraticMap
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open CFSG.LocalAnalysis.GLTheoremA.T173M

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p r : ℕ} [Fact p.Prime]
  {A : Subgroup (V ≃ₗ[K] V)}

private theorem closure_coordRotations_eq_top :
    Subgroup.closure (Set.range fun i : Fin r =>
      (Pi.mulSingle i (ofAdd 1) : Fin r → Multiplicative (ZMod p))) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  rw [← Finset.univ_prod_mulSingle f]
  refine Subgroup.prod_mem _ fun i _ => ?_
  have hsingle : Pi.mulSingle i (f i) =
      (Pi.mulSingle i (ofAdd 1) : Fin r → Multiplicative (ZMod p)) ^ (toAdd (f i)).val := by
    rw [← Pi.mulSingle_pow]
    congr 1
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    exact (ofAdd_toAdd (f i)).symm
  rw [hsingle]
  apply Subgroup.pow_mem
  exact Subgroup.subset_closure (show Pi.mulSingle i (ofAdd 1) ∈
    Set.range (fun j : Fin r => (Pi.mulSingle j (ofAdd 1) :
      Fin r → Multiplicative (ZMod p))) from ⟨i, rfl⟩)

theorem TBJOmData.isPlaneFrame_qPlus (Δ : TBJOmData Q p A r)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hA : A ≤ orthDerived Q) :
    IsPlaneFrame Q p Δ.F.U
      (fun i => Δ.τΩ hA (Pi.mulSingle i (ofAdd (1 : ZMod p))))
      (Δ.τΩ hA).range := by
  classical
  have hp : p.Prime := Fact.out
  let ρ : Fin r → ↥(orthDerived Q) :=
    fun i => Δ.τΩ hA (Pi.mulSingle i (ofAdd (1 : ZMod p)))
  have hco : ∀ i, (ρ i : V ≃ₗ[K] V) =
      Δ.F.ι (ofAdd (Pi.single i 1)) := by
    intro i
    change Δ.τ _ = _
    rw [Δ.τ_eq]
    congr 1
  have hpow : ∀ i, (ρ i : V ≃ₗ[K] V) ^ p = 1 :=
    fun i => hco i ▸ Δ.F.pow_p _
  have hfree : ∀ i, ∀ v ∈ Δ.F.U i, (ρ i : V ≃ₗ[K] V) v = v → v = 0 := by
    intro i v hv h
    rw [hco i] at h
    exact Δ.F.fpf _ i (by simp) v hv h
  have hmap : ∀ i, ∀ v ∈ Δ.F.U i, (ρ i : V ≃ₗ[K] V) v ∈ Δ.F.U i := by
    intro i v hv
    rw [hco i]
    exact Δ.F.mapsTo _ i v hv
  have hnd : ∀ i, (polarBilin (Q.comp (Δ.F.U i).subtype)).Nondegenerate := by
    intro i
    constructor <;> intro x hx <;> apply Subtype.ext
    · exact Δ.F.nondeg i x x.2 fun v hv => by
        have h := hx ⟨v, hv⟩
        simpa [polarBilin_apply_apply, polar_comp_subtype_cent, polar_comm] using h
    · exact Δ.F.nondeg i x x.2 fun v hv => by
        have h := hx ⟨v, hv⟩
        simpa [polarBilin_apply_apply, polar_comp_subtype_cent] using h
  have haniso : ∀ i, ∀ v ∈ Δ.F.U i, Q v = 0 → v = 0 := by
    intro i
    obtain ⟨_, _, _, ha⟩ := OrthBstarOdd.plane_facts hp hp2
      (fun c hc => eq_one_of_pow_eq_one_of_dvd_card_add_one hp hp2 hpq hc)
      (fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (Subgroup.commutator_le_self _ (ρ i).2) v)
      (hpow i) (Δ.finrank_piece i)
      (fun v hv h => Δ.F.nondeg i v hv fun w hw => by rw [polar_comm]; exact h w hw)
      (hmap i) (fun v hv hv0 h => hv0 (hfree i v hv h))
    intro v hv hQv
    by_contra hv0
    exact ha v hv hv0 hQv
  refine {
    finrank_eq := Δ.finrank_piece
    nondeg := hnd
    not_isPlusType := fun i =>
      CFSG.RankThree.PartOne.S15K.not_isPlusType_of_aniso_plane
        (Δ.finrank_piece i) (haniso i)
    perp := Δ.F.orth
    orderOf_eq := ?_
    apply_of_perp := ?_
    maps_to := hmap
    eq_zero_of_apply_eq := hfree
    isElemAbelian := ?_
    closure_eq := ?_ }
  · intro i
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact hpow i
    · intro h
      have h' := congrArg Subtype.val h
      rw [hco i] at h'
      exact Δ.F.single_ne_one i h'
  · intro i v hv
    change Δ.τ _ v = v
    exact (Δ.tau_mulSingle_apply_iff i v).mpr ((mem_polarPerp_iff).mp hv)
  · constructor
    · rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      obtain ⟨f, hf⟩ := a.2
      obtain ⟨g, hg⟩ := b.2
      change a.1 * b.1 = b.1 * a.1
      rw [← hf, ← hg, ← map_mul, ← map_mul, mul_comm f g]
    · rintro _ ⟨f, rfl⟩
      have hfp : f ^ p = 1 := by
        ext i
        change p • toAdd (f i) = 0
        simp [nsmul_eq_mul]
      rw [← map_pow, hfp, map_one]
  · change Subgroup.closure (Set.range ρ) = (Δ.τΩ hA).range
    have hrange : Set.range ρ = (Δ.τΩ hA) ''
        (Set.range fun i : Fin r => (Pi.mulSingle i (ofAdd 1) :
          Fin r → Multiplicative (ZMod p))) := by
      ext x
      simp [ρ]
    rw [hrange, ← MonoidHom.map_closure, closure_coordRotations_eq_top,
      MonoidHom.range_eq_map]

theorem TBJOmData.exists_mixedFrame_of_twoLocal (Δ : TBJOmData Q p A r)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hA : A ≤ orthDerived Q)
    (hQ : (polarBilin Q).Nondegenerate)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    {H S : Subgroup ↥(orthDerived Q)}
    (hHT : H ≤ (Δ.τΩ hA).range) (hHcard : Nat.card H = p ^ (r - 1))
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hHS : H ≤ Subgroup.normalizer (S : Set ↥(orthDerived Q))) :
    ∃ (i j : Fin r) (c : ℕ), i ≠ j ∧ ¬ p ∣ c ∧
      IsMixedFrame Q p Δ.F.U
        (Function.update
          (fun k => Δ.τΩ hA (Pi.mulSingle k (ofAdd (1 : ZMod p))))
          j (Δ.τΩ hA (Pi.mulSingle j (ofAdd (1 : ZMod p))) ^ c)) i j H := by
  classical
  have hp : p.Prime := Fact.out
  let ρ : Fin r → ↥(orthDerived Q) :=
    fun i => Δ.τΩ hA (Pi.mulSingle i (ofAdd (1 : ZMod p)))
  have hF := Δ.isPlaneFrame_qPlus hp2 hpq hA
  have hF' : IsPlaneFrame Q p Δ.F.U ρ (Subgroup.closure (Set.range ρ)) := by
    change IsPlaneFrame Q p Δ.F.U ρ (Δ.τΩ hA).range at hF
    rwa [← hF.closure_eq] at hF
  have hHT' : H ≤ Subgroup.closure (Set.range ρ) := by rwa [hF.closure_eq]
  have htop : ⨆ k, Δ.F.U k = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨u, hu, heq⟩ := Δ.exists_sum_pieces hfix v
    rw [← heq]
    exact Submodule.sum_mem _ fun k _ => le_iSup (fun k => Δ.F.U k) k (hu k)
  let ι := (orthDerived Q).subtype
  obtain ⟨W, hW1, hWinv, hWTS⟩ := OrthBstarOdd.exists_singular_of_two hQ
    (fun c hc => eq_one_of_pow_eq_one_of_dvd_card_add_one hp hp2 hpq hc)
    (S := S.map ι) (N := H.map ι) (hS2.map ι)
    (fun h => hS1 ((Subgroup.map_eq_bot_iff_of_injective _ (orthDerived Q).subtype_injective).mp h))
    (by
      rintro _ ⟨s, _, rfl⟩ v
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (Subgroup.commutator_le_self _ s.2) v)
    (by
      rintro _ ⟨s, _, rfl⟩
      exact (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp
        (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ s.2)).2)
    (by
      rintro _ ⟨a, _, rfl⟩ v
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (Subgroup.commutator_le_self _ a.2) v)
    (by
      rintro _ ⟨a, ha, rfl⟩
      change (a : V ≃ₗ[K] V) ^ p = 1
      exact congrArg Subtype.val (hF.isElemAbelian.2 a (hHT ha)))
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨s, hs, rfl⟩
      exact ⟨a * s * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hHS ha) s).mp hs,
        by simp only [map_mul, map_inv]⟩)
  have hWinv' : ∀ a ∈ H, ∀ w ∈ W, (a : V ≃ₗ[K] V) w ∈ W :=
    fun a ha w hw => hWinv _ ⟨a, ha, rfl⟩ w hw
  rcases separated_or_pair hp hF' hHT' hHcard with hsep | ⟨i, j, c, hij, hc, hHeq⟩
  · exact (hW1 (eq_bot_of_separated hF' hp hp2 htop hHT' hsep hWTS hWinv')).elim
  · have hFpow := isPlaneFrame_update_pow hp hF' j hc
    have hHeq' : H = Subgroup.closure
        (insert (Function.update ρ j (ρ j ^ c) i * Function.update ρ j (ρ j ^ c) j)
          (Function.update ρ j (ρ j ^ c) '' {k | k ≠ i ∧ k ≠ j})) := by
      have himg : Function.update ρ j (ρ j ^ c) '' {k | k ≠ i ∧ k ≠ j} =
          ρ '' {k | k ≠ i ∧ k ≠ j} :=
        Set.image_congr fun k hk => Function.update_of_ne hk.2 _ _
      rw [himg, Function.update_self, Function.update_of_ne hij]
      exact hHeq
    have hρH : ∀ k, k ≠ i → k ≠ j → Function.update ρ j (ρ j ^ c) k ∈ H := by
      intro k hki hkj
      rw [hHeq']
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨k, ⟨hki, hkj⟩, rfl⟩)
    have hWle := le_sup_of_invariant_totallySingular hp hp2 hFpow htop hρH hWTS hWinv'
    exact ⟨i, j, c, hij, hc, hFpow, htop, hij, hHeq', W, hW1, hWle, hWTS, hWinv'⟩

theorem TBJOmData.mixedFrame_power_eq_one_or_neg_one (Δ : TBJOmData Q p A r)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hA : A ≤ orthDerived Q)
    {H : Subgroup ↥(orthDerived Q)} {i j : Fin r} {c : ℕ}
    (hij : i ≠ j) (hc : ¬ p ∣ c)
    (hM : IsMixedFrame Q p Δ.F.U
      (Function.update
        (fun k => Δ.τΩ hA (Pi.mulSingle k (ofAdd (1 : ZMod p))))
        j (Δ.τΩ hA (Pi.mulSingle j (ofAdd (1 : ZMod p))) ^ c)) i j H) :
    (c : ZMod p) = 1 ∨ (c : ZMod p) = -1 := by
  classical
  have hp : p.Prime := Fact.out
  have hK1 : ∀ z : K, z ^ p = 1 → z = 1 :=
    fun z hz => eq_one_of_pow_eq_one_of_dvd_card_add_one hp hp2 hpq hz
  let ρ : Fin r → ↥(orthDerived Q) :=
    fun k => Δ.τΩ hA (Pi.mulSingle k (ofAdd (1 : ZMod p)))
  let a : ↥(orthDerived Q) := ρ i * ρ j ^ c
  let f₀ : Fin r → Multiplicative (ZMod p) :=
    Pi.mulSingle i (ofAdd 1) * (Pi.mulSingle j (ofAdd 1)) ^ c
  have ha : (a : V ≃ₗ[K] V) = Δ.τ f₀ := by
    change _ = Δ.τ (_ * _ ^ c)
    rw [map_mul, map_pow]
    rfl
  have hfi : toAdd (f₀ i) = 1 := by
    simp [f₀, Pi.mulSingle_apply, hij, hij.symm]
  have hfj : toAdd (f₀ j) = (c : ZMod p) := by
    simp [f₀, Pi.mulSingle_apply, hij, hij.symm, nsmul_eq_mul]
  have he : (c : ZMod p) ≠ 0 := fun h => hc ((ZMod.natCast_eq_zero_iff c p).mp h)
  have hact : ∀ k d, (a : V ≃ₗ[K] V) (Δ.θ k d) =
      Δ.θ k ((Δ.c ^ (toAdd (f₀ k)).val) d) := by
    intro k d
    rw [ha, Δ.τ_eq, Δ.θ_act]
    rfl
  have hacti : ∀ d, (a : V ≃ₗ[K] V) (Δ.θ i d) = Δ.θ i (Δ.c d) := by
    intro d
    simpa [hfi, CoordSL.pow_val_one Δ.c_pow] using hact i d
  have hactj : ∀ d, (a : V ≃ₗ[K] V) (Δ.θ j d) =
      Δ.θ j ((Δ.c ^ (c : ZMod p).val) d) := by
    intro d
    simpa [hfj] using hact j d
  have haH : a ∈ H := by
    simpa [a, ρ, Function.update_of_ne hij] using hM.pair_mem
  have hap : (a : V ≃ₗ[K] V) ^ p = 1 :=
    congrArg Subtype.val (hM.isElemAbelian.2 a haH)
  have hmaps : ∀ v ∈ Δ.F.U i, (a : V ≃ₗ[K] V) v ∈ Δ.F.U i := by
    intro v hv
    obtain ⟨d, rfl⟩ := LinearMap.mem_range.mp ((Δ.θ_range i).symm ▸ hv)
    rw [hacti]
    exact (Δ.θ_range i) ▸ LinearMap.mem_range_self _ _
  have hfree : ∀ v ∈ Δ.F.U i, v ≠ 0 → (a : V ≃ₗ[K] V) v ≠ v := by
    intro v hv hv0 h
    obtain ⟨d, rfl⟩ := LinearMap.mem_range.mp ((Δ.θ_range i).symm ▸ hv)
    rw [hacti] at h
    have hd : d = 0 := Δ.c_fix d (Δ.θ_inj i h)
    exact hv0 (by rw [hd, map_zero])
  obtain ⟨t, _, hrel, _⟩ := OrthBstarOdd.plane_facts hp hp2 hK1
    (fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
      (Subgroup.commutator_le_self _ a.2) v)
    hap (Δ.finrank_piece i)
    (fun v hv h => Δ.F.nondeg i v hv fun w hw => by rw [polar_comm]; exact h w hw)
    hmaps hfree
  have hrelj : ∀ v ∈ Δ.F.U j, (a : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v) =
      t • (a : V ≃ₗ[K] V) v + v := by
    have hi : ∀ v ∈ Δ.F.U i,
        Polynomial.aeval (a : V ≃ₗ[K] V).toLinearMap
          (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X - 1) v = 0 := by
      intro v hv
      simpa [pow_two, Module.End.mul_apply, sub_eq_zero] using
        (show (a : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v) - t • (a : V ≃ₗ[K] V) v = v from
          sub_eq_iff_eq_add.mpr (by rw [add_comm]; exact hrel v hv))
    have hj := (hM.aeval_eq_zero_iff hp hp2 hpq haH
      (Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X - 1)).mp hi
    intro v hv
    have h := hj v hv
    simpa [pow_two, Module.End.mul_apply, sub_eq_zero, sub_eq_iff_eq_add, add_comm] using h
  have hDrel : ∀ d, Δ.c (Δ.c d) = t • Δ.c d + d := by
    intro d
    apply Δ.θ_inj i
    have h := hrel (Δ.θ i d) ((Δ.θ_range i) ▸ LinearMap.mem_range_self _ _)
    simpa only [hacti, map_add, map_smul] using h
  have hDerel : ∀ d, (Δ.c ^ (c : ZMod p).val) ((Δ.c ^ (c : ZMod p).val) d) =
      t • (Δ.c ^ (c : ZMod p).val) d + d := by
    intro d
    apply Δ.θ_inj j
    have h := hrelj (Δ.θ j d) ((Δ.θ_range j) ▸ LinearMap.mem_range_self _ _)
    simpa only [hactj, map_add, map_smul] using h
  have hDne : ∃ d : Δ.D, d ≠ 0 := by
    have hpos : 0 < finrank K Δ.D := by rw [Δ.finrank_D]; omega
    exact Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨d, hd⟩ := hDne
  have hcp : (Δ.c ^ (c : ZMod p).val) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, Δ.c_pow, one_pow]
  have hcfix : (Δ.c ^ (c : ZMod p).val) d ≠ d :=
    fun h => hd (OmMv.pow_fix_eq_zero Δ.c_pow Δ.c_fix he h)
  obtain ⟨θ, hθ⟩ := exists_conj_of_quadratic_relation Δ.finrank_D
    (LinearIndependent.pair_iff.mpr (OrthBstarOdd.indep_of_ne Δ.c_pow hK1
      (fun h => hd (Δ.c_fix d h))))
    (LinearIndependent.pair_iff.mpr (OrthBstarOdd.indep_of_ne hcp hK1 hcfix))
    (alpha := t) (beta := 1)
    (by simpa using hDrel d) (by simpa using hDerel d)
  exact Δ.c_roots (c : ZMod p) θ.toLinearMap θ.injective hθ

theorem TBJOmData.exists_reflFixed_of_twoLocal (Δ : TBJOmData Q p A r)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hA : A ≤ orthDerived Q)
    (hQ : (polarBilin Q).Nondegenerate)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    {H S : Subgroup ↥(orthDerived Q)}
    (hHT : H ≤ (Δ.τΩ hA).range) (hHcard : Nat.card H = p ^ (r - 1))
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hHS : H ≤ Subgroup.normalizer (S : Set ↥(orthDerived Q))) :
    ∃ i j : Fin r, i ≠ j ∧
      (H.map (orthDerived Q).subtype ≤ Δ.reflFixed i j ∨
        H.map (orthDerived Q).subtype ≤ Δ.reflFixedPos i j) := by
  classical
  obtain ⟨i, j, c, hij, hc, hM⟩ :=
    Δ.exists_mixedFrame_of_twoLocal hp2 hpq hA hQ hfix hHT hHcard hS2 hS1 hHS
  have he := Δ.mixedFrame_power_eq_one_or_neg_one hp2 hpq hA hij hc hM
  let ρ : Fin r → ↥(orthDerived Q) :=
    fun k => Δ.τΩ hA (Pi.mulSingle k (ofAdd (1 : ZMod p)))
  have hHeq : H = Subgroup.closure
      (insert (ρ i * ρ j ^ c) (ρ '' {k | k ≠ i ∧ k ≠ j})) := by
    have himg : Function.update ρ j (ρ j ^ c) '' {k | k ≠ i ∧ k ≠ j} =
        ρ '' {k | k ≠ i ∧ k ≠ j} :=
      Set.image_congr fun k hk => Function.update_of_ne hk.2 _ _
    have hEq := hM.eq_closure
    change H = Subgroup.closure (insert
      (Function.update ρ j (ρ j ^ c) i * Function.update ρ j (ρ j ^ c) j)
      (Function.update ρ j (ρ j ^ c) '' {k | k ≠ i ∧ k ≠ j})) at hEq
    simpa [himg, Function.update_of_ne hij] using hEq
  let f₀ : Fin r → Multiplicative (ZMod p) :=
    Pi.mulSingle i (ofAdd 1) * (Pi.mulSingle j (ofAdd 1)) ^ c
  have hpair : ((ρ i * ρ j ^ c : ↥(orthDerived Q)) : V ≃ₗ[K] V) = Δ.τ f₀ := by
    rw [map_mul, map_pow]
    rfl
  have hfi : toAdd (f₀ i) = 1 := by simp [f₀, Pi.mulSingle_apply, hij, hij.symm]
  have hfj : toAdd (f₀ j) = (c : ZMod p) := by
    simp [f₀, Pi.mulSingle_apply, hij, hij.symm, nsmul_eq_mul]
  have hsingle : ∀ k, k ≠ i → k ≠ j →
      Pi.mulSingle k (ofAdd (1 : ZMod p)) ∈ reflFixedCoord p r i j ∧
      Pi.mulSingle k (ofAdd (1 : ZMod p)) ∈ reflFixedCoordPos p r i j := by
    intro k hki hkj
    constructor <;> simp [reflFixedCoord, reflFixedCoordPos, MonoidHom.mem_ker,
      Pi.mulSingle_apply, hki.symm, hkj.symm]
  refine ⟨i, j, hij, ?_⟩
  rcases he with he | he
  · left
    rw [hHeq, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, (rfl | ⟨k, hk, rfl⟩), rfl⟩
    · change ((ρ i * ρ j ^ c : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ Δ.reflFixed i j
      rw [hpair]
      refine ⟨f₀, ?_, rfl⟩
      change f₀ i / f₀ j = 1
      rw [div_eq_one]
      change toAdd (f₀ i) = toAdd (f₀ j)
      rw [hfi, hfj, he]
    · exact ⟨Pi.mulSingle k (ofAdd 1), (hsingle k hk.1 hk.2).1, rfl⟩
  · right
    rw [hHeq, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, (rfl | ⟨k, hk, rfl⟩), rfl⟩
    · change ((ρ i * ρ j ^ c : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ Δ.reflFixedPos i j
      rw [hpair]
      refine ⟨f₀, ?_, rfl⟩
      change f₀ i * f₀ j = 1
      change toAdd (f₀ i) + toAdd (f₀ j) = 0
      simp [hfi, hfj, he]
    · exact ⟨Pi.mulSingle k (ofAdd 1), (hsingle k hk.1 hk.2).2, rfl⟩

theorem TBJOmData.exists_slTwo_centralizing_of_twoLocal (Δ : TBJOmData Q p A r)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) (hA : A ≤ orthDerived Q)
    (hQ : (polarBilin Q).Nondegenerate) (hr : 4 ≤ r) (hq : 4 ≤ Nat.card K)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    {H S : Subgroup ↥(orthDerived Q)}
    (hHT : H ≤ (Δ.τΩ hA).range) (hHcard : Nat.card H = p ^ (r - 1))
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hHS : H ≤ Subgroup.normalizer (S : Set ↥(orthDerived Q))) :
    ∃ θ : Matrix.SpecialLinearGroup (Fin 2) K →* ↥(orthDerived Q),
      Function.Injective θ ∧ ∀ a ∈ H, ∀ g, a * θ g = θ g * a := by
  classical
  obtain ⟨i, j, hij, hH⟩ :=
    Δ.exists_reflFixed_of_twoLocal hp2 hpq hA hQ hfix hHT hHcard hS2 hS1 hHS
  obtain ⟨θ₀, hθ₀, hrange, _⟩ := tbjOm_rankOne_model hp2 hA Δ (by omega) hq hfix i j hij
  have hθC : ∃ θ : Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V),
      Function.Injective θ ∧ θ.range ≤
        Subgroup.centralizer (H.map (orthDerived Q).subtype : Set (V ≃ₗ[K] V)) ⊓
          orthDerived Q := by
    rcases hH with hH | hH
    · refine ⟨θ₀, hθ₀, ?_⟩
      rw [hrange]
      exact (ggOTwoPrime_le _).trans
        (inf_le_inf (Subgroup.centralizer_le hH) le_rfl)
    · have hcard : ({i, j} : Finset (Fin r)).card < (Finset.univ : Finset (Fin r)).card := by
        have := Finset.card_insert_le i ({j} : Finset (Fin r))
        simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at *
        omega
      obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      have hki : k ≠ i := fun h => hk (by simp [h])
      have hkj : k ≠ j := fun h => hk (by simp [h])
      obtain ⟨w, hw, _, hconj⟩ := Δ.dinvMove j k hkj.symm
      let θ := (MulAut.conj w).toMonoidHom.comp θ₀
      refine ⟨θ, (MulAut.conj w).injective.comp hθ₀, ?_⟩
      have hθrange : θ.range = Δ.rankOnePos i j := by
        rw [MonoidHom.range_comp, hrange]
        exact Δ.rankOne_map_dinv hij hkj.symm hki.symm w hw hconj
      rw [hθrange]
      exact (ggOTwoPrime_le _).trans
        (inf_le_inf (Subgroup.centralizer_le hH) le_rfl)
  obtain ⟨θ, hθinj, hθle⟩ := hθC
  let θΩ := θ.codRestrict (orthDerived Q) fun g => (hθle ⟨g, rfl⟩).2
  refine ⟨θΩ, ?_, ?_⟩
  · intro g g' h
    exact hθinj (congrArg Subtype.val h)
  · intro a ha g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hθle ⟨g, rfl⟩).1
      (a : V ≃ₗ[K] V) ⟨a, ha, rfl⟩

end CFSG.StandardType.OrthTorus

end
