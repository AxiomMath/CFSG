module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneRestSUFrame
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlock
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSU

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 Matrix
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

namespace RootPlaneSU

section Pair

variable {H : Type*} [Group H] {p : ℕ}

theorem pow_mod_of_pow_eq_one {x : H} (hx : x ^ p = 1) (k : ℕ) : x ^ (k % p) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hx, one_pow, mul_one]

@[expose] def pairHom [NeZero p] (x y : H) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x * y = y * x) : Multiplicative (ZMod p × ZMod p) →* H where
  toFun a := x ^ (Multiplicative.toAdd a).1.val * y ^ (Multiplicative.toAdd a).2.val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    rw [ZMod.val_add, ZMod.val_add, pow_mod_of_pow_eq_one hx, pow_mod_of_pow_eq_one hy, pow_add,
      pow_add]
    have hc : Commute x y := hxy
    calc x ^ (Multiplicative.toAdd a).1.val * x ^ (Multiplicative.toAdd b).1.val *
          (y ^ (Multiplicative.toAdd a).2.val * y ^ (Multiplicative.toAdd b).2.val) =
        x ^ (Multiplicative.toAdd a).1.val * (x ^ (Multiplicative.toAdd b).1.val *
          y ^ (Multiplicative.toAdd a).2.val) * y ^ (Multiplicative.toAdd b).2.val := by group
      _ = x ^ (Multiplicative.toAdd a).1.val * (y ^ (Multiplicative.toAdd a).2.val *
          x ^ (Multiplicative.toAdd b).1.val) * y ^ (Multiplicative.toAdd b).2.val := by
          rw [(hc.pow_pow _ _).eq]
      _ = _ := by group

theorem pairHom_apply [NeZero p] (x y : H) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hxy : x * y = y * x) (a : Multiplicative (ZMod p × ZMod p)) :
    pairHom x y hx hy hxy a =
      x ^ (Multiplicative.toAdd a).1.val * y ^ (Multiplicative.toAdd a).2.val := rfl

end Pair

section Types

variable {f n : ℕ} {F : Type} [Field F] {p : ℕ}

theorem exists_blocks_of_ne {a₁ a₂ : ↥(unitarySU 2 f F n)} {S₁ S₂ : Finset (Fin n)}
    (hp : p.Prime) (hd : Disjoint S₁ S₂) (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty)
    (ha₁p : a₁ ^ p = 1) (ha₂p : a₂ ^ p = 1) (hb₁ : TableBUE.IsBlockOn S₁ (SUTB.mx a₁))
    (hf₁ : ∀ v : Fin n → F, SUTB.mx a₁ *ᵥ v = v → ∀ k ∈ S₁, v k = 0)
    (hb₂ : TableBUE.IsBlockOn S₂ (SUTB.mx a₂))
    (hf₂ : ∀ v : Fin n → F, SUTB.mx a₂ *ᵥ v = v → ∀ k ∈ S₂, v k = 0) {i j : ℕ}
    (hij : ¬ (p ∣ i ∧ p ∣ j)) :
    ∃ T : Finset (Fin n), T ⊆ S₁ ∪ S₂ ∧ T.Nonempty ∧
      TableBUE.IsBlockOn T (SUTB.mx (a₁ ^ i * a₂ ^ j)) ∧
      ∀ v : Fin n → F, SUTB.mx (a₁ ^ i * a₂ ^ j) *ᵥ v = v → ∀ k ∈ T, v k = 0 := by
  have hpow : ∀ {a : ↥(unitarySU 2 f F n)} {S : Finset (Fin n)}, a ^ p = 1 →
      TableBUE.IsBlockOn S (SUTB.mx a) → (∀ v : Fin n → F, SUTB.mx a *ᵥ v = v → ∀ k ∈ S, v k = 0) →
      ∀ k : ℕ, ¬ p ∣ k → TableBUE.IsBlockOn S (SUTB.mx (a ^ k)) ∧
        ∀ v : Fin n → F, SUTB.mx (a ^ k) *ᵥ v = v → ∀ l ∈ S, v l = 0 := by
    intro a S hap hb hf k hk
    have hmx : SUTB.mx (a ^ k) = SUTB.mx a ^ k := SUTB.mx_pow a k
    have hmxp : SUTB.mx a ^ p = 1 := by rw [← SUTB.mx_pow, hap, SUTB.mx_one]
    refine ⟨by rw [hmx]; exact SUNS.isBlockOn_pow hb k, fun v hv => hf v ?_⟩
    rw [hmx] at hv
    exact fix_of_pow_fix hp hmxp hk hv
  have hone : ∀ {a : ↥(unitarySU 2 f F n)}, a ^ p = 1 → ∀ k : ℕ, p ∣ k → a ^ k = 1 := by
    rintro a hap k ⟨t, rfl⟩
    rw [pow_mul, hap, one_pow]
  by_cases hi : p ∣ i
  · have hj : ¬ p ∣ j := fun hj => hij ⟨hi, hj⟩
    obtain ⟨hb, hf⟩ := hpow ha₂p hb₂ hf₂ j hj
    refine ⟨S₂, Finset.subset_union_right, hne₂, ?_, ?_⟩
    · rw [hone ha₁p i hi, one_mul]
      exact hb
    · rw [hone ha₁p i hi, one_mul]
      exact hf
  · by_cases hj : p ∣ j
    · obtain ⟨hb, hf⟩ := hpow ha₁p hb₁ hf₁ i hi
      refine ⟨S₁, Finset.subset_union_left, hne₁, ?_, ?_⟩
      · rw [hone ha₂p j hj, mul_one]
        exact hb
      · rw [hone ha₂p j hj, mul_one]
        exact hf
    · obtain ⟨hbi, hfi⟩ := hpow ha₁p hb₁ hf₁ i hi
      obtain ⟨hbj, hfj⟩ := hpow ha₂p hb₂ hf₂ j hj
      refine ⟨S₁ ∪ S₂, subset_refl _, hne₁.mono Finset.subset_union_left, ?_, ?_⟩
      · rw [SUTB.mx_mul]
        exact (isBlockOn_mono hbi Finset.subset_union_left).mul
          (isBlockOn_mono hbj Finset.subset_union_right)
      · intro v hv
        rw [SUTB.mx_mul] at hv
        exact fix_mul_of_block hbi hbj hd hfi hfj v hv

end Types

end RootPlaneSU

section Inputs

theorem RootPlaneSU.exists_bstar_frame {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU .PSU n (f + 1)).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hns : ¬ p ∣ 2 ^ (f + 1) + 1) :
    ∃ (P : GL (Fin n) (GaloisField 2 (2 * (f + 1))))
      (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
        (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n)
      (S₁ S₂ : Finset (Fin n)) (a₁ a₂ : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)),
      SURep.ggFrameU (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP a₁ ∈ Bs ∧
      SURep.ggFrameU (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP a₂ ∈ Bs ∧
      Disjoint S₁ S₂ ∧ S₁.Nonempty ∧ S₂.Nonempty ∧ 4 ≤ (S₁ ∪ S₂)ᶜ.card ∧
      TableBUE.IsBlockOn S₁ (SUTB.mx a₁) ∧
      (∀ v : Fin n → GaloisField 2 (2 * (f + 1)), SUTB.mx a₁ *ᵥ v = v → ∀ k ∈ S₁, v k = 0) ∧
      TableBUE.IsBlockOn S₂ (SUTB.mx a₂) ∧
      (∀ v : Fin n → GaloisField 2 (2 * (f + 1)), SUTB.mx a₂ *ᵥ v = v → ∀ k ∈ S₂, v k = 0) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer
        (((TableBUE.blockSU (K := GaloisField 2 (2 * (f + 1))) (n := f + 1) (S₁ ∪ S₂)ᶜ).map
          (SURep.ggFrameU (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) :
            Subgroup G) : Set G) : Subgroup G) ≤ p ^ 2 := by
  classical
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hnq : (n, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : n = 3 := congrArg Prod.fst h'
    omega
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set ψ₁ := SURep.ggFrameU hF ψ P₀ hP₀ with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SURep.range_ggFrameU hF ψ P₀ hP₀
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hFk₁ : SURep.GGFrameKer ψ₁ := SURep.ggFrameKer_of_ker_le_center hF (by omega) hnq hker₁
  have hC : Subgroup.centralizer (ψ₁.range : Set G) = ⊥ := by
    rw [hr₁, hrange]
    exact s1.1
  have hBsel : IsElemAbelian p Bs := hctx.2.1.2.1
  have hEB : ∀ b ∈ Bs, ∃ B', B' ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) ∧
      (b, B') ∈ SUTorus.suPairs ψ₁ := by
    intro b hb
    obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn4 G ψ hker b⁻¹
      (hctx.2.2.2.2.2.2.1.2 b⁻¹ (Bs.inv_mem hb))
    refine ⟨P₀ * A * P₀⁻¹,
      SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP₀ hA),
      SUTorus.mem_suPairs_transfer P₀ hP₀ (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n)
        hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  have hlift : ∀ b ∈ Bs, ∃ X : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
      X ^ p = 1 ∧ ψ₁ X = b := fun b hb => by
    obtain ⟨B', hB'U, hB'⟩ := hEB b hb
    exact SUTB.exists_lift h (by omega) hnq hp hns hker₁ hC (hBsel.2 b hb) hB'U hB'
  have hcomm : ∀ X Y : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n), X ^ p = 1 →
      ψ₁ X ∈ Bs → ψ₁ Y ∈ Bs → X * Y = Y * X := fun X Y hXp hX hY =>
    SUNS.commute_of_frame_commute h hFk₁ hp hns hXp (TableB.IsElemAbelian.comm hBsel hX hY)
  let A : Subgroup ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    { carrier := {X | X ^ p = 1 ∧ ψ₁ X ∈ Bs}
      mul_mem' := fun {X Y} hX hY => ⟨by
        rw [(show Commute X Y from hcomm X Y hX.1 hX.2 hY.2).mul_pow, hX.1, hY.1, one_mul], by
          rw [map_mul]; exact Bs.mul_mem hX.2 hY.2⟩
      one_mem' := ⟨one_pow p, by rw [map_one]; exact Bs.one_mem⟩
      inv_mem' := fun {X} hX => ⟨by rw [inv_pow, hX.1, inv_one], by
        rw [map_inv]; exact Bs.inv_mem hX.2⟩ }
  have hmemA : ∀ X, X ∈ A ↔ X ^ p = 1 ∧ ψ₁ X ∈ Bs := fun X => Iff.rfl
  have hA : SUTB.MaxElemAb p A :=
    { prime := hp
      ne_two := hp2
      not_dvd := hns
      pow := fun a ha => ((hmemA a).mp ha).1
      comm := fun a ha b hb => hcomm a b ((hmemA a).mp ha).1 ((hmemA a).mp ha).2
        ((hmemA b).mp hb).2
      max := fun g hgp hga => by
        refine (hmemA g).mpr ⟨hgp, hctx.2.1.2.2.2 (ψ₁ g) ?_ (by rw [← map_pow, hgp, map_one])⟩
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨X, hXp, rfl⟩ := hlift b hb
        rw [← map_mul, ← map_mul, hga X ((hmemA X).mpr ⟨hXp, hb⟩)] }
  have hcard : p ^ 4 ≤ Nat.card A := by
    have hm4 : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
    have hsurj : Function.Surjective (fun X : A => (⟨ψ₁ X, ((hmemA X).mp X.2).2⟩ : Bs)) := by
      intro b
      obtain ⟨X, hXp, hXb⟩ := hlift b b.2
      exact ⟨⟨X, (hmemA X).mpr ⟨hXp, hXb ▸ b.2⟩⟩, Subtype.ext hXb⟩
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hm4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBle
      _ ≤ Nat.card A := Nat.card_le_card_of_surjective _ hsurj
  obtain ⟨Q, S₁, S₂, a₁, a₂, hQ, ha₁, ha₂, hdisj, hne₁, hne₂, hcard₃, hb₁, hf₁, hb₂, hf₂, hgen⟩ :=
    RootPlaneSU.exists_plane_frame h hA hcard
  have hQi : ((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
      Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) =
      ((Q : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))).map h.bar)ᵀ := by
    have h1 : ((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) * Q = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) =
        ((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) :
          Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (Q * ((Q : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))).map h.bar)ᵀ) := by
          rw [mul_eq_one_comm.mp hQ, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hQQ : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
      (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
      (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = 1 := by
    rw [SURep.conjTr_eq_bar h, hQi]
    have hbb : ((((Q : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))).map h.bar)ᵀ).map
        h.bar)ᵀ = (Q : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) := by
      ext i j
      simp [UnitaryFieldData.bar_bar]
    rw [hbb]
    exact mul_eq_one_comm.mp hQ
  have hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
      (((Q⁻¹ * P₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
      (((Q⁻¹ * P₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
        Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n := by
    rw [Units.val_mul, CFSG.LieType.Universal.Unitary.conjTr_mul]
    calc conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
          (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
            (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
              Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          ((((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
            Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
            (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1))))) =
        conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
          (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
            (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
              Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
          (((Q⁻¹ : GL (Fin n) (GaloisField 2 (2 * (f + 1))))) :
            Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1))))) *
            (P₀ : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) := by
          simp only [Matrix.mul_assoc]
      _ = antidiag n := by rw [hQQ, Matrix.mul_one, hP₀]
  have hφs : ∀ (s₀ u₀ : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)),
      (u₀ : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) = Q * s₀ * Q⁻¹ →
      SURep.ggFrameU hF ψ (Q⁻¹ * P₀) hP s₀ = ψ₁ u₀ := by
    intro s₀ u₀ hu₀
    have hsu : (SURep.ggFrameEquiv hF (Q⁻¹ * P₀) hP).symm s₀ =
        (SURep.ggFrameEquiv hF P₀ hP₀).symm u₀ := by
      apply Subtype.ext
      rw [SURep.coe_ggFrameEquiv_symm, SURep.coe_ggFrameEquiv_symm, hu₀]
      group
    exact (SURep.ggFrameU_apply hF ψ (Q⁻¹ * P₀) hP s₀).trans
      ((congrArg ψ hsu).trans (SURep.ggFrameU_apply hF ψ P₀ hP₀ u₀).symm)
  have hFkφ : SURep.GGFrameKer (SURep.ggFrameU hF ψ (Q⁻¹ * P₀) hP) :=
    SURep.ggFrameKer_ggFrameU hF ψ (Q⁻¹ * P₀) hP (by omega) hnq hker
  have hconj : ∀ X : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
      Q⁻¹ * (X : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) * Q ∈
        unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n :=
    fun X => SUTB.conj_mem_unitarySU h hQ X.2
  have hφc : ∀ X : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
      SURep.ggFrameU hF ψ (Q⁻¹ * P₀) hP ⟨Q⁻¹ * X * Q, hconj X⟩ = ψ₁ X := fun X =>
    hφs _ X (by
      change (X : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) = Q * (Q⁻¹ * X * Q) * Q⁻¹
      group)
  have hmod : ∀ {y : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)}, y ∈ A →
      ∀ k : ℕ, y ^ k = y ^ (k % p) := fun hy k => by
    conv_lhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hA.pow _ hy, one_pow, mul_one]
  refine ⟨Q⁻¹ * P₀, hP, S₁, S₂, ⟨Q⁻¹ * a₁ * Q, hconj a₁⟩, ⟨Q⁻¹ * a₂ * Q, hconj a₂⟩, ?_, ?_,
    hdisj, hne₁, hne₂, hcard₃, hb₁, hf₁, hb₂, hf₂, ?_⟩
  · rw [hφc]
    exact ((hmemA a₁).mp ha₁).2
  · rw [hφc]
    exact ((hmemA a₂).mp ha₂).2
  ·
    refine SUTB.card_le_sq_of_forall _ (ψ₁ a₁) (ψ₁ a₂) fun b hb => ?_
    obtain ⟨hbB, hbC⟩ := Subgroup.mem_inf.mp hb
    obtain ⟨X, hXp, rfl⟩ := hlift b hbB
    have hXA : X ∈ A := (hmemA X).mpr ⟨hXp, hbB⟩
    have hX'p : (⟨Q⁻¹ * X * Q, hconj X⟩ :
        ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)) ^ p = 1 := by
      apply Subtype.ext
      change (Q⁻¹ * (X : GL (Fin n) (GaloisField 2 (2 * (f + 1)))) * Q) ^ p = 1
      have h1 := conj_pow (a := Q⁻¹) (b := (X : GL (Fin n) (GaloisField 2 (2 * (f + 1)))))
        (i := p)
      rw [inv_inv] at h1
      rw [h1, ← SubgroupClass.coe_pow, hXp, OneMemClass.coe_one, mul_one, inv_mul_cancel]
    have hX'c : ∀ s ∈ TableBUE.blockSU (K := GaloisField 2 (2 * (f + 1))) (n := f + 1)
        (S₁ ∪ S₂)ᶜ, (⟨Q⁻¹ * X * Q, hconj X⟩ :
          ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)) * s =
          s * ⟨Q⁻¹ * X * Q, hconj X⟩ := by
      intro s hs
      refine SUNS.commute_of_frame_commute h hFkφ hp hns hX'p ?_
      rw [hφc]
      exact ((Subgroup.mem_centralizer_iff.mp hbC) _ (Subgroup.mem_map_of_mem _ hs)).symm
    have hbl := SUTB.isBlockOn_compl_of_commute_blockSU h hp hns (by omega) hX'p hX'c
    rw [compl_compl] at hbl
    obtain ⟨i, j, hij⟩ := hgen X hXA hbl
    refine ⟨⟨i % p, Nat.mod_lt _ hp.pos⟩, ⟨j % p, Nat.mod_lt _ hp.pos⟩, ?_⟩
    rw [hij, hmod ha₁ i, hmod ha₂ j, map_mul, map_pow, map_pow]

theorem RootPlaneSU.rootPlane_psu_nonsplit {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ}
    {ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) (m + 1) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J
      (Unitary.rootDatum (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) (m + 1))
      .PSU (m + 1) (f + 1) ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hns : ¬ p ∣ 2 ^ (f + 1) + 1) :
    ∃ (E : Subgroup G)
      (γ : Fin (Unitary.rootDatum (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f))
        (m + 1)).rank → ℤ)
      (u : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) (m + 1)) (r : G),
        E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        GGRootClass (Unitary.rootDatum (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f))
          (m + 1)) .PSU γ ∧
        E ≤ Subgroup.centralizer (ggRootSub (Unitary.rootDatum
          (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) (m + 1)) ψ γ u : Set G) ∧
        r ∈ ggRootSub (Unitary.rootDatum
          (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) (m + 1)) ψ γ u ∧
        orderOf r = 2 ∧
        ∀ e ∈ E, e ≠ 1 → e ∈ D ∨ ∃ L₁ : Subgroup G,
          IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
            Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank : 2 ≤ (m + 1) / 2 := hctx.2.2.2.1.2
  have hn : 2 ≤ m + 1 := by omega
  set hK := card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f) with hKdef
  have hdata : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  obtain ⟨P, hP, S₁, S₂, a₁, a₂, hBa₁, hBa₂, hdisj, hne₁, hne₂, hcard₃, hb₁, hf₁, hb₂, hf₂,
    hbound⟩ := RootPlaneSU.exists_bstar_frame (n := m + 1) (f := f) (ψ := ψ) hctx s1 hns
  set φ := SURep.ggFrameU hK ψ P hP with hφ
  have hFk : SURep.GGFrameKer φ := SURep.ggFrameKer_ggFrameU hK ψ P hP (by omega)
    (fun h => by have h1 : m + 1 = 3 := congrArg Prod.fst h; omega) hker
  have hrangeφ : φ.range = ggG0 p B x L D J := (SURep.range_ggFrameU hK ψ P hP).trans hrange
  set M := (S₁ ∪ S₂)ᶜ with hMdef
  have hMc : Mᶜ = S₁ ∪ S₂ := compl_compl _
  obtain ⟨i₃, hi₃⟩ : M.Nonempty := Finset.card_pos.mp (by omega)
  have hi₃' : ∀ {S : Finset (Fin (m + 1))}, S ⊆ S₁ ∪ S₂ → i₃ ∈ Sᶜ := fun hS =>
    Finset.mem_compl.mpr fun h => (Finset.mem_compl.mp hi₃) (hS h)
  have ha₁p : a₁ ^ p = 1 := SUNS.pow_eq_one_of_frame hFk (S := S₁ᶜ)
    (by rw [compl_compl]; exact hb₁) (hi₃' Finset.subset_union_left) (hctx.2.1.2.1.2 _ hBa₁)
  have ha₂p : a₂ ^ p = 1 := SUNS.pow_eq_one_of_frame hFk (S := S₂ᶜ)
    (by rw [compl_compl]; exact hb₂) (hi₃' Finset.subset_union_right) (hctx.2.1.2.1.2 _ hBa₂)
  have h21 : S₂ ⊆ S₁ᶜ := fun k hk => Finset.mem_compl.mpr (Finset.disjoint_right.mp hdisj hk)
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := by
    apply Subtype.ext
    apply Units.ext
    exact (SUTB.mx_mul a₁ a₂).trans ((SUNS.commute_of_isBlockOn_compl hb₁
      (RootPlaneSU.isBlockOn_mono hb₂ h21)).trans (SUTB.mx_mul a₂ a₁).symm)
  set ρ := RootPlaneSU.pairHom a₁ a₂ ha₁p ha₂p ha₁₂ with hρ
  have hρa : ∀ a, ρ a = a₁ ^ (Multiplicative.toAdd a).1.val * a₂ ^ (Multiplicative.toAdd a).2.val :=
    fun a => rfl
  have hρp : ∀ a, ρ a ^ p = 1 := by
    intro a
    rw [hρa]
    have hc : Commute (a₁ ^ (Multiplicative.toAdd a).1.val) (a₂ ^ (Multiplicative.toAdd a).2.val) :=
      (show Commute a₁ a₂ from ha₁₂).pow_pow _ _
    rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm _ p, mul_comm _ p, pow_mul, pow_mul, ha₁p, ha₂p,
      one_pow, one_pow, one_mul]
  have hblockAll : ∀ a, TableBUE.IsBlockOn (S₁ ∪ S₂) (SUTB.mx (ρ a)) := by
    intro a
    rw [hρa, SUTB.mx_mul, SUTB.mx_pow, SUTB.mx_pow]
    exact (SUNS.isBlockOn_pow (RootPlaneSU.isBlockOn_mono hb₁ Finset.subset_union_left) _).mul
      (SUNS.isBlockOn_pow (RootPlaneSU.isBlockOn_mono hb₂ Finset.subset_union_right) _)
  have hnz : ∀ a : Multiplicative (ZMod p × ZMod p), a ≠ 1 →
      ¬ (p ∣ (Multiplicative.toAdd a).1.val ∧ p ∣ (Multiplicative.toAdd a).2.val) := by
    rintro a ha ⟨h1, h2⟩
    apply ha
    have e1 : (Multiplicative.toAdd a).1 = 0 :=
      (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _))
    have e2 : (Multiplicative.toAdd a).2 = 0 :=
      (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt _))
    have h0 : Multiplicative.toAdd a = 0 := Prod.ext e1 e2
    rw [← ofAdd_toAdd a, h0, ofAdd_zero]
  have htype : ∀ a : Multiplicative (ZMod p × ZMod p), a ≠ 1 →
      ∃ T : Finset (Fin (m + 1)), T ⊆ S₁ ∪ S₂ ∧ T.Nonempty ∧
        TableBUE.IsBlockOn T (SUTB.mx (ρ a)) ∧
        ∀ v : Fin (m + 1) → GaloisField 2 (2 * (f + 1)), SUTB.mx (ρ a) *ᵥ v = v →
          ∀ k ∈ T, v k = 0 := fun a ha =>
    RootPlaneSU.exists_blocks_of_ne hp hdisj hne₁ hne₂ ha₁p ha₂p hb₁ hf₁ hb₂ hf₂ (hnz a ha)
  have hinj : Function.Injective (φ.comp ρ) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    by_contra ha1
    obtain ⟨T, hTS, ⟨k, hk⟩, hTb, hTf⟩ := htype a ha1
    exact SUNS.frame_ne_one hFk (S := Tᶜ) (by rw [compl_compl]; exact hTb)
      (fun v hv l hl => hTf v hv l (by simpa using hl)) (hi₃' hTS) (by simpa using hk) ha
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < M.card)
  obtain ⟨g, hg⟩ := RestSU.exists_SU_col_pair hK (by omega : 1 ≤ m) hP hij
  obtain ⟨x₀, hx₀, hx₀c, hx₀2⟩ := RestSU.exists_top_root_elt hK hn
  have hblock : ∀ z ∈ (Unitary.rootDatum hK (m + 1)).rootGroup (ggTopRoot (m + 1)),
      g * z * g⁻¹ ∈ UFusion.suBlock P M := by
    intro z hz
    exact RestSU.conj_mem_suBlock hP g (fun a ha => hg a (fun h => ha (h ▸ hi))
      (fun h => ha (h ▸ hj))) (RestSU.mat_eq_of_mem_rootGroup_top hK hn hz)
  have hcentM : ∀ c : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) (m + 1)),
      TableBUE.IsBlockOn (S₁ ∪ S₂) (SUTB.mx c) → ∀ u ∈ UFusion.suBlock P M,
        ψ u * φ c = φ c * ψ u := by
    intro c hc u hu
    obtain ⟨s, hs⟩ : ∃ s, SURep.ggFrameEquiv hK P hP u = s := ⟨_, rfl⟩
    have hsu : (SURep.ggFrameEquiv hK P hP).symm s = u := by
      rw [← hs, MulEquiv.symm_apply_apply]
    have hψu : ψ u = φ s := by
      rw [hφ, SURep.ggFrameU_apply, hsu]
    have h1 := SURep.coe_ggFrameEquiv_symm hK P hP s
    rw [hsu] at h1
    have hsm : (s : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1)))) =
        P * (u : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1)))) * P⁻¹ := by
      rw [h1]
      group
    have hsb : TableBUE.IsBlockOn M (SUTB.mx s) := by
      have hu' := UFusion.mem_glBlock.mp (UFusion.mem_suBlock.mp hu)
      intro a b hab
      change ((s : GL (Fin (m + 1)) (GaloisField 2 (2 * (f + 1)))) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 (2 * (f + 1)))) a b = _
      rw [hsm]
      exact hu' a b hab
    have hcomm : s * c = c * s := by
      apply Subtype.ext
      apply Units.ext
      exact (SUTB.mx_mul s c).trans ((SUNS.commute_of_isBlockOn_compl hsb
        (by rw [hMc]; exact hc)).trans (SUTB.mx_mul c s).symm)
    rw [hψu, ← map_mul, ← map_mul, hcomm]
  refine ⟨(φ.comp ρ).range, ggTopRoot (m + 1), g, ψ (g * x₀ * g⁻¹), ?_, ?_, ?_,
    ⟨ggTopRoot_mem_roots hn, fun _ => RestSU.ggTopRoot_longRoot hK hn⟩, ?_,
    ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩, ?_, ?_⟩
  ·
    rintro _ ⟨a, rfl⟩
    change φ (ρ a) ∈ Bs
    rw [hρa, map_mul, map_pow, map_pow]
    exact Bs.mul_mem (Bs.pow_mem hBa₁ _) (Bs.pow_mem hBa₂ _)
  ·
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨_, a, rfl⟩ := u
      obtain ⟨_, b, rfl⟩ := v
      apply Subtype.ext
      change φ (ρ a) * φ (ρ b) = φ (ρ b) * φ (ρ a)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm a b]
    · rintro _ ⟨a, rfl⟩
      change φ (ρ a) ^ p = 1
      rw [← map_pow, hρp a, map_one]
  ·
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    change Nat.card (ZMod p × ZMod p) = p ^ 2
    rw [Nat.card_prod, Nat.card_zmod, sq]
  ·
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hcentM (ρ a) (hblockAll a) _ (hblock z hz)
  ·
    apply orderOf_eq_prime
    · rw [← map_pow, conj_pow, hx₀2, mul_one, mul_inv_cancel, map_one]
    · intro h1
      have hc : g * x₀ * g⁻¹ ∈ Subgroup.center _ := hker h1
      apply hx₀c
      have hcg := Subgroup.mem_center_iff.mp hc g
      have e : x₀ = g * x₀ * g⁻¹ := by
        calc x₀ = g⁻¹ * ((g * x₀ * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * x₀ * g⁻¹)) := by rw [← hcg]
          _ = g * x₀ * g⁻¹ := by group
      rw [e]
      exact hc
  ·
    rintro _ ⟨a, rfl⟩ he1
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact he1 (map_one _)
    obtain ⟨T, hTS, ⟨k, hk⟩, hTb, hTf⟩ := htype a ha1
    have hMT : M ⊆ Tᶜ := Finset.compl_subset_compl.mpr hTS
    have hcardT : 4 ≤ Tᶜ.card := hcard₃.trans (Finset.card_le_card hMT)
    have hcomp := SUNS.isComponentOf_map_blockSU_of_fix hK hdata hFk hp hns (hρp a) (S := Tᶜ)
      (by rw [compl_compl]; exact hTb) (fun v hv l hl => hTf v hv l (by simpa using hl))
      (fun v hv l hl => RootPlaneSU.fixRow_of_fix hdata (ρ a) hTf v hv l (by simpa using hl))
      (by omega) (fun h => by have h1 := congrArg Prod.fst h; simp only at h1; omega)
      (i₀ := k) (by simpa using hk)
    rw [hrangeφ] at hcomp
    refine Or.inr ⟨_, hcomp, le_trans (Subgroup.card_le_of_le ?_) hbound⟩
    refine inf_le_inf_left _ (Subgroup.centralizer_le ?_)
    exact SetLike.coe_subset_coe.mpr (Subgroup.map_mono fun s hs =>
      RootPlaneSU.isBlockOn_mono hs hMT)

theorem ggRootPlaneInputOn_PSUNonsplit : GGRootPlaneInputOn GGPSUNonsplit := by
  intro G _ _ p B Bs x L D J t n f
  by_cases ht : t = .PSU
  · subst ht
    by_cases hf : 1 ≤ f
    · obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have e : ggU .PSU n (f' + 1) =
          ⟨SU (unitaryInvolution (GaloisField 2 (2 * (f' + 1))) 2 (f' + 1)) n,
            Unitary.rootDatum (card_galoisField_two_mul 2 (f' + 1) (Nat.le_add_left 1 f')) n⟩ := by
        simp only [ggU, lieUniversal, hf, ↓reduceDIte]
      rw [e]
      intro ψ hP hctx s1
      obtain ⟨-, -, hn, -⟩ := hctx.2.2.2.1.1
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact RootPlaneSU.rootPlane_psu_nonsplit hctx s1 hP.2
    · intro ψ _ hctx
      exact absurd hctx.2.2.2.1.1.2.1 hf
  · intro ψ hP
    exact absurd hP.1 ht

theorem ggRootPlaneAt_PSU : GGRootPlaneAt .PSU :=
  ggRootPlaneAt_PSU_of_nonsplit ggRootPlaneInputOn_PSUNonsplit

end Inputs

end CFSG.StandardType
