module

public import CFSG.RankThree.PartOne.S12.InputsCT
public import CFSG.RankThree.PartOne.CTP.TransferGen

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply
  exists_unitaryInvolution_eq_neg)
open CFSG.LieType.Universal.Unitary (SUid conjTr SUid_eq_statedSU exists_wittMatrix conjEquiv
  isQuasisimple_statedSU_of_card map_center_mulEquiv)
open CFSG.LieType.Steinberg (hypEquiv fixedSubfield card_fixedSubfield)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSU StatedProj StatedScalars)
open scoped MatrixGroups

theorem nonempty_ringEquiv_of_natCard_eq {A B : Type} [Field A] [Field B] [Finite A] [Finite B]
    (h : Nat.card A = Nat.card B) : Nonempty (A ≃+* B) := by
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  exact ⟨FiniteField.ringEquivOfCardEq h⟩

theorem nonempty_sl_equiv_of_ringEquiv {A B : Type} [Field A] [Field B] (e : A ≃+* B) (n : ℕ) :
    Nonempty (SL(n, A) ≃* SL(n, B)) :=
  ⟨{ toFun := fun g => Matrix.SpecialLinearGroup.map e.toRingHom g
     invFun := fun g => Matrix.SpecialLinearGroup.map e.symm.toRingHom g
     left_inv := fun g => Subtype.ext (by ext i j; simp)
     right_inv := fun g => Subtype.ext (by ext i j; simp)
     map_mul' := fun g h => map_mul _ g h }⟩

theorem exists_suid_two_equiv_sl {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {K₀ : Type} [Field K₀] [Finite K₀]
    (hK₀ : Nat.card K₀ = 2 ^ f) :
    Nonempty (SUid (unitaryInvolution K 2 f) 2 ≃* SL(2, K₀)) := by
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨e⟩ := nonempty_ringEquiv_of_natCard_eq
    ((card_fixedSubfield hK).trans hK₀.symm : Nat.card (fixedSubfield K 2 f) = Nat.card K₀)
  obtain ⟨m⟩ := nonempty_sl_equiv_of_ringEquiv e 2
  exact ⟨((conjEquiv P hP).symm.trans (hypEquiv hζ0 hζ).symm).trans m⟩

private theorem map_mem_SUid {A B : Type} [Field A] [Field B] {σA : A ≃+* A} {σB : B ≃+* B}
    (e : A →+* B) (he : ∀ c, e (σA c) = σB (e c)) {n : ℕ} {g : GL (Fin n) A}
    (hg : g ∈ SUid σA n) : Matrix.GeneralLinearGroup.map e g ∈ SUid σB n := by
  obtain ⟨hdet, hiso⟩ := hg
  have hcoe : ((Matrix.GeneralLinearGroup.map e g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) =
      (g : Matrix (Fin n) (Fin n) A).map e := rfl
  refine ⟨?_, ?_⟩
  · rw [hcoe, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · have hc : conjTr σB ((g : Matrix (Fin n) (Fin n) A).map e) =
        (conjTr σA (g : Matrix (Fin n) (Fin n) A)).map e := by
      ext i j
      simp [conjTr, he]
    rw [hcoe, hc, ← Matrix.map_mul, hiso, Matrix.map_one _ (map_zero e) (map_one e)]

private theorem ringEquiv_unitaryInvolution {f : ℕ} {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Field L] [Finite L] [CharP L 2] (φ : K ≃+* L) (c : K) :
    φ (unitaryInvolution K 2 f c) = unitaryInvolution L 2 f (φ c) := by
  rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]

theorem nonempty_suid_equiv_of_ringEquiv {f : ℕ} {K L : Type} [Field K] [Finite K] [CharP K 2]
    [Field L] [Finite L] [CharP L 2] (φ : K ≃+* L) (n : ℕ) :
    Nonempty (SUid (unitaryInvolution K 2 f) n ≃* SUid (unitaryInvolution L 2 f) n) :=
  ⟨{ toFun := fun g => ⟨Matrix.GeneralLinearGroup.map φ.toRingHom g,
                 map_mem_SUid φ.toRingHom (ringEquiv_unitaryInvolution φ) g.2⟩
     invFun := fun g => ⟨Matrix.GeneralLinearGroup.map φ.symm.toRingHom g,
                 map_mem_SUid φ.symm.toRingHom (ringEquiv_unitaryInvolution φ.symm) g.2⟩
     left_inv := fun g => Subtype.ext (Units.ext (by
       ext i j; simp [Matrix.GeneralLinearGroup.map]))
     right_inv := fun g => Subtype.ext (Units.ext (by
       ext i j; simp [Matrix.GeneralLinearGroup.map]))
     map_mul' := fun g h => Subtype.ext (map_mul _ _ _) }⟩

theorem exists_su3_surj_of_centrallyUThree {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {X : Type} [Group X] (hX : CentrallyUThree f X) :
    ∃ θ₀ : SUid (unitaryInvolution K 2 f) 3 →* X, Function.Surjective θ₀ ∧
      θ₀.ker ≤ Subgroup.center (SUid (unitaryInvolution K 2 f) 3) := by
  have key : ∀ (L : Type) [Field L] [Finite L], Nat.card L = (2 ^ f) ^ 2 →
      Nonempty (SUid (unitaryInvolution K 2 f) 3 ≃* ↥(StatedSU 3 (2 ^ f) L)) := by
    intro L _ _ hL
    obtain ⟨φ⟩ := nonempty_ringEquiv_of_natCard_eq (hK.trans hL.symm)
    have : CharP L 2 := charP_of_injective_ringHom φ.toRingHom.injective 2
    obtain ⟨Φ⟩ := nonempty_suid_equiv_of_ringEquiv (f := f) φ 3
    exact ⟨Φ.trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hL 3))⟩
  rcases hX with ⟨L, _, _, hL, ⟨e⟩⟩ | ⟨-, L, _, _, hL, ⟨e⟩⟩
  · obtain ⟨Ψ⟩ := key L hL
    refine ⟨(Ψ.trans e.symm).toMonoidHom, (Ψ.trans e.symm).surjective, ?_⟩
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (Ψ.trans e.symm).injective]
    exact bot_le
  · obtain ⟨Ψ⟩ := key L hL
    set N : Subgroup ↥(StatedSU 3 (2 ^ f) L) :=
      (StatedScalars (Fin 3) L).subgroupOf (StatedSU 3 (2 ^ f) L) with hN
    have hNc : ∀ s ∈ N, ∀ t : ↥(StatedSU 3 (2 ^ f) L), t * s = s * t := by
      intro s hs t
      have hsc : (s : GL (Fin 3) L) ∈ Subgroup.center (GL (Fin 3) L) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact Subgroup.mem_subgroupOf.mp hs
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hsc) (t : GL (Fin 3) L))
    refine ⟨e.symm.toMonoidHom.comp ((QuotientGroup.mk' N).comp Ψ.toMonoidHom),
      e.symm.surjective.comp ((QuotientGroup.mk'_surjective N).comp Ψ.surjective), fun x hx => ?_⟩
    have hx' : e.symm ((QuotientGroup.mk' N) (Ψ x)) = 1 := MonoidHom.mem_ker.mp hx
    have h1 : (QuotientGroup.mk' N) (Ψ x) = 1 := e.symm.map_eq_one_iff.mp hx'
    have h2 : Ψ x ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Ψ.injective
    rw [map_mul, map_mul]
    exact hNc _ h2 _

theorem statedClassicalModel_psu_of_surjective {f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) {n : ℕ} (hn : 3 ≤ n)
    {G : Type} [Group G] (θ : SUid (unitaryInvolution K 2 f) n →* G)
    (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (SUid (unitaryInvolution K 2 f) n)) :
    StatedClassicalModel (G ⧸ Subgroup.center G) .PSU n 2 f := by
  have hnq : (n, 2 ^ f) ≠ (3, 2) := by
    intro h
    have h2 := congrArg Prod.snd h
    simp only at h2
    omega
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  obtain ⟨hQ, hZ⟩ := isQuasisimple_statedSU_of_card (p := 2) (f := f) hK hn hnq
  let Ξ : ↥(SUid (unitaryInvolution K 2 f) n) ≃* ↥(StatedSU n (2 ^ f) K) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hK n)
  have hPT : Group.IsPerfect ↥(StatedSU n (2 ^ f) K) := hQ.1
  have hPS : Group.IsPerfect ↥(SUid (unitaryInvolution K 2 f) n) :=
    Group.IsPerfect.ofSurjective (f := Ξ.symm.toMonoidHom) Ξ.symm.surjective
  refine ⟨⟨Nat.prime_two, hf, hn, hnq⟩, K, inferInstance, inferInstance, hK, ?_⟩
  let e : ↥θ.range ≃* G :=
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_top_of_surjective θ hθ)).trans Subgroup.topEquiv
  let Ψ := projEquivGen θ hker (QuotientGroup.mk'_surjective (Subgroup.center _))
    (QuotientGroup.ker_mk' (Subgroup.center _))
  exact ⟨((Ψ.trans (QuotientGroup.congr (Subgroup.center θ.range) (Subgroup.center G) e
    (map_center_mulEquiv e))).symm).trans
    ((QuotientGroup.congr _ _ Ξ (map_center_mulEquiv Ξ)).trans
      (QuotientGroup.quotientMulEquivOfEq hZ))⟩

end CFSG.RankThree.PartOne.CTP
