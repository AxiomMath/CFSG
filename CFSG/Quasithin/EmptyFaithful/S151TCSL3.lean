module

public import CFSG.Quasithin.EmptyFaithful.S151TBDef
public import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree

public section

namespace CFSG.Quasithin.S151TC

theorem exists_mulEquiv_statedSL {n : ℕ} {F K : Type} [Field F] [Field K] (φ : F ≃+* K) :
    ∃ Θ : CFSG.Assembly.LowTwoRank.StatedSL n F ≃* CFSG.Assembly.LowTwoRank.StatedSL n K,
      ∀ g, ((Θ g : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((g : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ := by
  have hmem : ∀ (E : Type) [Field E] (A : Matrix.GeneralLinearGroup (Fin n) E),
      A ∈ CFSG.Assembly.LowTwoRank.StatedSL n E ↔ (A : Matrix (Fin n) (Fin n) E).det = 1 := by
    intro E _ A
    rw [CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL, MonoidHom.mem_range]
    constructor
    · rintro ⟨B, rfl⟩
      exact B.prop
    · intro h
      exact ⟨⟨A, h⟩, Units.ext rfl⟩
  let Ψ : Matrix.GeneralLinearGroup (Fin n) F ≃* Matrix.GeneralLinearGroup (Fin n) K :=
    Units.mapEquiv
      (φ.mapMatrix : Matrix (Fin n) (Fin n) F ≃+* Matrix (Fin n) (Fin n) K).toMulEquiv
  have hΨ : ∀ A, ((Ψ A : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F).map φ :=
    fun A => rfl
  have hdet : ∀ A, ((Ψ A : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det =
      φ ((A : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
    intro A
    rw [hΨ]
    exact (RingHom.map_det (φ : F →+* K) _).symm
  have hmap : (CFSG.Assembly.LowTwoRank.StatedSL n F).map Ψ.toMonoidHom =
      CFSG.Assembly.LowTwoRank.StatedSL n K := by
    ext y
    rw [Subgroup.mem_map, hmem K]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hmem F] at hx
      show ((Ψ x : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1
      rw [hdet, hx, map_one]
    · intro hy
      refine ⟨Ψ.symm y, ?_, Ψ.apply_symm_apply y⟩
      rw [hmem F]
      have h := hdet (Ψ.symm y)
      rw [Ψ.apply_symm_apply, hy] at h
      exact φ.injective (h.symm.trans (map_one φ).symm)
  exact ⟨(MulEquiv.subgroupMap Ψ (CFSG.Assembly.LowTwoRank.StatedSL n F)).trans
    (MulEquiv.subgroupCongr hmap), fun g => rfl⟩

theorem isMatrixBlockType_of_ringEquiv {G : Type} [Group G] {L : Subgroup G} {n : ℕ}
    {F K : Type} [Field F] [Field K] (φ : F ≃+* K)
    (h : CFSG.Quasithin.IsMatrixBlockType L (CFSG.Assembly.LowTwoRank.StatedSL n F)) :
    CFSG.Quasithin.IsMatrixBlockType L (CFSG.Assembly.LowTwoRank.StatedSL n K) := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := h
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_statedSL (n := n) φ
  let Φ : Multiplicative (Fin n → F) ≃* Multiplicative (Fin n → K) :=
    AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => φ.toAddEquiv)
  refine ⟨Θ.toMonoidHom.comp α, Θ.surjective.comp hαs, ?_, Φ.toMonoidHom.comp β,
    Φ.surjective.comp hβs, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective α _ Θ.injective, hαk]
  · rw [MonoidHom.ker_comp_of_injective β _ Φ.injective, hβk]
  · intro ℓ u v huv
    funext i
    have key := congrFun (hβe ℓ u v huv) i
    show φ (Multiplicative.toAdd (β v) i) =
      ((Θ (α ℓ) : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec
        (fun j => φ (Multiplicative.toAdd (β u) j)) i
    rw [key, hΘ]
    exact RingHom.map_mulVec (φ : F →+* K) _ _ i

theorem eq_two_of_card_statedSL_three_eq {F : Type} [Field F] [Finite F]
    (h : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 168) : Nat.card F = 2 := by
  rw [CFSG.SectionRank.OddCover.card_statedSL_three_eq_mul (p := Nat.card F) rfl] at h
  have hp : 2 ≤ Nat.card F := Finite.one_lt_card
  generalize Nat.card F = p at h hp ⊢
  by_contra hne
  have h3 : 3 ≤ p := by omega
  have h1 : 27 ≤ p ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left h3 3
  have h2 : 8 ≤ (p - 1) * (p + 1) := by
    calc 8 = (3 - 1) * (3 + 1) := by norm_num
      _ ≤ (p - 1) * (p + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h4 : 26 ≤ (p - 1) * (p ^ 2 + p + 1) := by
    calc 26 = (3 - 1) * (3 ^ 2 + 3 + 1) := by norm_num
      _ ≤ (p - 1) * (p ^ 2 + p + 1) :=
        Nat.mul_le_mul (by omega) (by nlinarith [Nat.pow_le_pow_left h3 2])
  have h5 := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
  omega

theorem card_eq_card_quotient_of_ker_eq {K H : Type*} [Group K] [Group H] (α : K →* H)
    (hαs : Function.Surjective α) (N : Subgroup K) (hαk : α.ker = N) :
    Nat.card H = Nat.card (K ⧸ N) := by
  rw [← Subgroup.index, ← hαk, Subgroup.index_ker, MonoidHom.range_eq_top.2 hαs,
    Subgroup.card_top]

theorem isLnBlock_three_of_isSL3Block {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.Quasithin.IsSL3Block L) (hcard : Nat.card (CFSG.Quasithin.S151TB.LStar L) = 168) :
    CFSG.Quasithin.IsLnBlock L 3 := by
  obtain ⟨hshort, n, F, _, _, hFcard, hmat⟩ := h
  refine ⟨hshort, ?_⟩
  have hF : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 168 := by
    obtain ⟨α, hαs, hαk, -⟩ := hmat
    rw [card_eq_card_quotient_of_ker_eq α hαs _ hαk]
    exact hcard
  have hF2 : Fintype.card F = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact eq_two_of_card_statedSL_three_eq hF
  let φ : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by rw [hF2, ZMod.card])
  exact isMatrixBlockType_of_ringEquiv φ hmat

end CFSG.Quasithin.S151TC
