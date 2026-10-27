module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldArithmetic
public import CFSG.Quasithin.Vol2.Ch10SecALiftConj
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl
public import CFSG.Quasithin.Vol2.Ch10SecDBasic
public import CFSG.Quasithin.Vol2.Ch5Statements
public import CFSG.Quasithin.Vol2.Ch6SL2Fix

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative MatrixGroups Matrix
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL exists_conj_unip coe_inv_mul_SL)

variable {G : Type} [Group G] {L N : Subgroup G} {n : ℕ}

theorem IsNatQuotCh5.exists_coord (h : IsNatQuotCh5 L N n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(Assembly.LowTwoRank.StatedSL 2 K) →* ↥(autOn L N))
        (Y : ↥N →* Multiplicative (Fin 2 → K)),
        Function.Surjective π ∧ Function.Surjective Y ∧
        (∀ x : ↥N, Y x = 1 ↔ (x : G) ∈ Subgroup.centralizer (L : Set G)) ∧
        ∀ (γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) (x : ↥N),
          Multiplicative.toAdd (Y (((π γ : ↥(autOn L N)) : MulAut ↥N) x)) =
            ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
              (Multiplicative.toAdd (Y x)) := by
  obtain ⟨-, hc, K, _, _, hK, π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hker : (FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).ker.subgroupOf
      (FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).sec = ⊥ := Subgroup.bot_subgroupOf _
  let e₀ : ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).sec ⧸
      (FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).ker.subgroupOf
        (FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).sec ≃*
      ↥(FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).sec :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans QuotientGroup.quotientBot
  have he₀ : ∀ m, e₀ (QuotientGroup.mk m) = m := fun _ => rfl
  have hmk : ∀ q, QuotientGroup.mk (e₀ q) = q := fun q => e₀.injective (he₀ (e₀ q))
  let Y : ↥N →* Multiplicative (Fin 2 → K) :=
    (FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).sec.subtype.comp
      (e₀.toMonoidHom.comp (β.comp (Subgroup.topEquiv (G := ↥N)).symm.toMonoidHom))
  have hY : ∀ x : ↥N, Y x = (e₀ (β ⟨x, Subgroup.mem_top x⟩)).1 := fun _ => rfl
  refine ⟨K, inferInstance, inferInstance, hK, π, Y, hπs, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨y, Subgroup.mem_top y⟩)
    refine ⟨u, ?_⟩
    rw [hY]
    have hu' : β ⟨(u : ↥N), Subgroup.mem_top _⟩ = β u := rfl
    rw [hu', hu, he₀]
  · intro x
    rw [hY]
    constructor
    · intro h1
      have h2 : β ⟨x, Subgroup.mem_top x⟩ = 1 := by
        apply e₀.injective
        rw [map_one]
        exact Subtype.ext h1
      exact (hβk _).mp h2
    · intro h1
      have h2 : β ⟨x, Subgroup.mem_top x⟩ = 1 := (hβk _).mpr h1
      rw [h2, map_one]
      rfl
  · intro γ x
    have hact : (FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).act γ
        (e₀ (β ⟨x, Subgroup.mem_top x⟩)).1 ∈ (FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).sec :=
      Subgroup.mem_top _
    have h1 := hβe γ ⟨x, Subgroup.mem_top x⟩ (e₀ (β ⟨x, Subgroup.mem_top x⟩))
      (Subgroup.mem_top _) hact (hmk _).symm
    have h2 : β ⟨((π γ : ↥(autOn L N)) : MulAut ↥N) x, Subgroup.mem_top _⟩ =
        QuotientGroup.mk ⟨(FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).act γ
          (e₀ (β ⟨x, Subgroup.mem_top x⟩)).1, hact⟩ := h1
    exact congrArg (fun q => Multiplicative.toAdd (e₀ q).1) h2

theorem IsNatQuotCh5.exists_sylowCoord [Finite G] {S : Subgroup G} (h : IsNatQuotCh5 L N n)
    (hS : IsSylowTwoOf S L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      ∃ (ψ : ↥(autOn L N) ≃* SL(2, F)) (Y : ↥N →* Multiplicative (Fin 2 → F)),
        Function.Surjective Y ∧
        (∀ x : ↥N, Y x = 1 ↔ (x : G) ∈ Subgroup.centralizer (L : Set G)) ∧
        (∀ (x : ↥(autOn L N)) (w : ↥N), Multiplicative.toAdd (Y ((x : MulAut ↥N) w)) =
          (ψ x : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (Y w))) ∧
        (∀ x : ↥(autOn L N), (x : MulAut ↥N) ∈ autOn S N ↔ ∃ b : F, ψ x = unipSL b) := by
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := h.1
  obtain ⟨K, _, _, hK, π, Y, hπs, hYs, hYk, hY⟩ := h.exists_coord
  have : CharP K 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card hK
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hfix : ∀ v : Fin 2 → K,
        ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec v = v := by
      intro v
      obtain ⟨x, hx⟩ := hYs (Multiplicative.ofAdd v)
      have := hY γ x
      rw [hγ, Subgroup.coe_one, MulAut.one_apply, hx] at this
      exact this.symm
    apply Subtype.ext
    apply Units.ext
    ext i j
    have := congrFun (hfix (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    rw [show (((1 : ↥(Assembly.LowTwoRank.StatedSL 2 K)) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 from rfl]
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  set eρ : SL(2, K) ≃* ↥(autOn L N) :=
    (specialLinearGroupEquivStatedSL 2 K).trans (MulEquiv.ofBijective π ⟨hπi, hπs⟩) with heρ
  have hE : ∀ (γ : SL(2, K)) (w : ↥N), Multiplicative.toAdd
      (Y (((eρ γ : ↥(autOn L N)) : MulAut ↥N) w)) =
        (γ : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd (Y w)) :=
    fun γ w => hY (specialLinearGroupEquivStatedSL 2 K γ) w
  set P : Subgroup (MulAut ↥N) := autOn S N with hPdef
  have hP : IsSylowTwoOf P (autOn L N) := Vol2.Ch10.SecD.isSylowTwoOf_autOn hS hLN
  set P' : Subgroup SL(2, K) := (P.subgroupOf (autOn L N)).comap eρ.toMonoidHom with hP'def
  have hP'mem : ∀ γ, γ ∈ P' ↔ ((eρ γ : ↥(autOn L N)) : MulAut ↥N) ∈ P := fun γ => Iff.rfl
  have hP'2 : IsPGroup 2 P' :=
    (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).comap_of_injective
      eρ.toMonoidHom eρ.injective
  have hP'idx : ¬ 2 ∣ P'.index := by
    rw [hP'def, Subgroup.index_comap_of_surjective _ eρ.surjective]
    exact hP.2.2
  obtain ⟨g, hgP, hPg⟩ := exists_conj_unip hK hP'2 hP'idx
  let M : Multiplicative (Fin 2 → K) →* Multiplicative (Fin 2 → K) :=
    { toFun := fun v => Multiplicative.ofAdd
        ((g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd v))
      map_one' := by simp
      map_mul' := fun v v' => by
        simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add] }
  have hMv : ∀ v, Multiplicative.toAdd (M v) =
      (g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd v) := fun v => rfl
  have hMinj : Function.Injective M := by
    intro v v' hvv
    have := congrArg (fun y => ((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec
      (Multiplicative.toAdd y)) hvv
    simp only [hMv, inv_mulVec_mulVec] at this
    exact Multiplicative.toAdd.injective this
  have hMsurj : Function.Surjective M := by
    intro v
    refine ⟨Multiplicative.ofAdd (((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec
      (Multiplicative.toAdd v)), ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hMv, toAdd_ofAdd, mulVec_inv_mulVec]
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK,
    eρ.symm.trans (MulAut.conj g), M.comp Y, hMsurj.comp hYs, ?_, ?_, ?_⟩
  · intro x
    rw [← hYk x]
    constructor
    · intro h1
      apply hMinj
      rw [map_one]
      exact h1
    · intro h1
      show M (Y x) = 1
      rw [h1, map_one]
  · intro x w
    have hx : x = eρ (eρ.symm x) := (eρ.apply_symm_apply x).symm
    have h1 := hE (eρ.symm x) w
    rw [← hx] at h1
    have hψ : ((eρ.symm.trans (MulAut.conj g)) x : SL(2, K)) = g * eρ.symm x * g⁻¹ := rfl
    show Multiplicative.toAdd (M (Y ((x : MulAut ↥N) w))) =
      ((eρ.symm.trans (MulAut.conj g)) x : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (M (Y w)))
    rw [hψ, hMv, hMv, h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_assoc _ _ (g : Matrix (Fin 2) (Fin 2) K), coe_inv_mul_SL, Matrix.mul_one]
  · intro x
    have hψ : ((eρ.symm.trans (MulAut.conj g)) x : SL(2, K)) = g * eρ.symm x * g⁻¹ := rfl
    rw [hψ]
    constructor
    · intro hxP
      have hmem : eρ.symm x ∈ P' := by
        rw [hP'mem, eρ.apply_symm_apply]
        exact hxP
      exact hgP _ hmem
    · rintro ⟨b, hb⟩
      have h1 : eρ.symm x = g⁻¹ * unipSL b * g := by
        rw [← hb]
        group
      have h2 := (hP'mem _).mp (hPg b)
      rw [← h1, eρ.apply_symm_apply] at h2
      exact h2

end CFSG.Quasithin.H13
