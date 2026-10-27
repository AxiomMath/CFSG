module

public import CFSG.Quasithin.Vol2.Ch10SecQ34MD
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.HSz
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Sz
open CFSG.LieType.Ree CFSG.Blueprint
open scoped Matrix

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem quotient_mk_mem_normalizer_map {H S : Subgroup G} {N : Subgroup ↥H} [N.Normal]
    (hSH : S ≤ H) {δ : G} (hδH : δ ∈ H)
    (hδS : δ ∈ Subgroup.normalizer (S : Set G)) :
    QuotientGroup.mk (⟨δ, hδH⟩ : ↥H) ∈
      Subgroup.normalizer (((S.subgroupOf H).map (QuotientGroup.mk' N)) :
        Set (↥H ⧸ N)) := by
  have hsub : (⟨δ, hδH⟩ : ↥H) ∈ Subgroup.normalizer ((S.subgroupOf H) : Set ↥H) := by
    have h1 : (⟨δ, hδH⟩ : ↥H) ∈
        (Subgroup.normalizer (S : Set G)).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr hδS
    rwa [Subgroup.subgroupOf_normalizer_eq hSH] at h1
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' N)
    (Subgroup.mem_map_of_mem _ hsub)

theorem conj_comm_of_commutator {V Q L : Subgroup G} {k : G}
    (hkV : k ∈ Subgroup.normalizer (V : Set G))
    (hQV : Q ≤ Subgroup.centralizer (V : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hcomm : ∀ l ∈ L, k * l * k⁻¹ * l⁻¹ ∈ Q) :
    ∀ h ∈ L ⊔ Q, ∀ z ∈ V,
      h * (k * z * k⁻¹) * h⁻¹ = k * (h * z * h⁻¹) * k⁻¹ := by
  classical
  have hQN : Q ≤ Subgroup.normalizer (V : Set G) :=
    hQV.trans (Subgroup.centralizer_le_normalizer (V : Set G))
  let T : Subgroup G :=
    { carrier := {h | h ∈ Subgroup.normalizer (V : Set G) ∧
        ∀ z ∈ V, h * (k * z * k⁻¹) * h⁻¹ = k * (h * z * h⁻¹) * k⁻¹}
      mul_mem' := by
        rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
        refine ⟨Subgroup.mul_mem _ hxN hyN, ?_⟩
        intro z hz
        have hyz : y * z * y⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp hyN z).mp hz
        calc (x * y) * (k * z * k⁻¹) * (x * y)⁻¹
            = x * (y * (k * z * k⁻¹) * y⁻¹) * x⁻¹ := by group
          _ = x * (k * (y * z * y⁻¹) * k⁻¹) * x⁻¹ := by rw [hy z hz]
          _ = k * (x * (y * z * y⁻¹) * x⁻¹) * k⁻¹ := hx _ hyz
          _ = k * ((x * y) * z * (x * y)⁻¹) * k⁻¹ := by group
      one_mem' := by
        refine ⟨Subgroup.one_mem _, ?_⟩
        intro z hz
        group
      inv_mem' := by
        rintro x ⟨hxN, hx⟩
        have hxN' : x⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
          (Subgroup.normalizer (V : Set G)).inv_mem hxN
        refine ⟨hxN', ?_⟩
        intro z hz
        simp only [inv_inv]
        have hz' : x⁻¹ * z * x ∈ V := by
          have h := (Subgroup.mem_normalizer_iff.mp hxN' z).mp hz
          simpa using h
        have h := hx (x⁻¹ * z * x) hz'
        have h' : x * (k * (x⁻¹ * z * x) * k⁻¹) * x⁻¹ = k * z * k⁻¹ := by
          rw [h]
          group
        calc x⁻¹ * (k * z * k⁻¹) * x
            = x⁻¹ * (x * (k * (x⁻¹ * z * x) * k⁻¹) * x⁻¹) * x := by rw [h']
          _ = k * (x⁻¹ * z * x) * k⁻¹ := by group }
  have hLT : L ≤ T := by
    intro l hl
    refine ⟨hLV hl, ?_⟩
    intro z hz
    set c : G := k * l * k⁻¹ * l⁻¹ with hcdef
    have hc : c ∈ Q := hcomm l hl
    have hc' : k * l * k⁻¹ = c * l := by
      rw [hcdef]
      group
    have hcC : c ∈ Subgroup.centralizer (V : Set G) := hQV hc
    have hkz : l * (k * z * k⁻¹) * l⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hl) (k * z * k⁻¹)).mp
        ((Subgroup.mem_normalizer_iff.mp hkV z).mp hz)
    have hkl : k * l = c * l * k := by
      calc k * l = (k * l * k⁻¹) * k := by group
        _ = (c * l) * k := by rw [hc']
    have hlkinv : l⁻¹ * k⁻¹ = k⁻¹ * l⁻¹ * c⁻¹ := by
      rw [show l⁻¹ * k⁻¹ = (k * l)⁻¹ by group, hkl]
      group
    have hcommc : c * (l * (k * z * k⁻¹) * l⁻¹) =
        (l * (k * z * k⁻¹) * l⁻¹) * c :=
      (Subgroup.mem_centralizer_iff.mp hcC _ hkz).symm
    have hmain : k * (l * z * l⁻¹) * k⁻¹ = l * (k * z * k⁻¹) * l⁻¹ := by
      calc k * (l * z * l⁻¹) * k⁻¹
          = (k * l) * z * (l⁻¹ * k⁻¹) := by group
        _ = (c * l * k) * z * (k⁻¹ * l⁻¹ * c⁻¹) := by rw [hkl, hlkinv]
        _ = c * (l * (k * z * k⁻¹) * l⁻¹) * c⁻¹ := by group
        _ = l * (k * z * k⁻¹) * l⁻¹ := by
              rw [show c * (l * (k * z * k⁻¹) * l⁻¹) =
                (l * (k * z * k⁻¹) * l⁻¹) * c from hcommc]
              group
    exact hmain.symm
  have hQT : Q ≤ T := by
    intro q hq
    have hqC : q ∈ Subgroup.centralizer (V : Set G) := hQV hq
    refine ⟨hQN hq, ?_⟩
    intro z hz
    have hkz : k * z * k⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hkV z).mp hz
    have h1 : q * (k * z * k⁻¹) * q⁻¹ = k * z * k⁻¹ := by
      have h := (Subgroup.mem_centralizer_iff.mp hqC (k * z * k⁻¹) hkz).symm
      rw [h]
      group
    have h2 : k * (q * z * q⁻¹) * k⁻¹ = k * z * k⁻¹ := by
      have h := (Subgroup.mem_centralizer_iff.mp hqC z hz).symm
      rw [h]
      group
    rw [h1, h2]
  have hH : L ⊔ Q ≤ T := sup_le hLT hQT
  intro h hh z hz
  exact (hH hh).2 z hz

@[expose] noncomputable def frobVecAddEquiv (K : Type) [Field K] [Finite K] [CharP K 2]
    [PerfectRing K 2] (c : ℕ) : (Fin 4 → K) ≃+ (Fin 4 → K) where
  toFun v i := (iterateFrobeniusEquiv K 2 c) (v i)
  invFun v i := (iterateFrobeniusEquiv K 2 c).symm (v i)
  left_inv v := by
    funext i
    exact (iterateFrobeniusEquiv K 2 c).symm_apply_apply (v i)
  right_inv v := by
    funext i
    exact (iterateFrobeniusEquiv K 2 c).apply_symm_apply (v i)
  map_add' v w := by
    funext i
    exact map_add _ _ _

theorem frobVecAddEquiv_mulVec {K : Type} [Field K] [Finite K] [CharP K 2] [PerfectRing K 2] (c : ℕ)
    (M : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) :
    frobVecAddEquiv K c (M *ᵥ v) = (M.map (· ^ 2 ^ c)) *ᵥ frobVecAddEquiv K c v := by
  funext i
  change (iterateFrobeniusEquiv K 2 c) (∑ j, M i j * v j) =
    ∑ j, (M i j ^ 2 ^ c) * (iterateFrobeniusEquiv K 2 c) (v j)
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, iterateFrobeniusEquiv_def]

theorem frobVecAddEquiv_symm_mulVec {K : Type} [Field K] [Finite K] [CharP K 2] [PerfectRing K 2]
    (c : ℕ) (M : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) :
    (frobVecAddEquiv K c).symm ((M.map (· ^ 2 ^ c)) *ᵥ v) =
      M *ᵥ (frobVecAddEquiv K c).symm v := by
  funext i
  change (iterateFrobeniusEquiv K 2 c).symm (∑ j, (M i j ^ 2 ^ c) * v j) =
    ∑ j, M i j * (iterateFrobeniusEquiv K 2 c).symm (v j)
  have hsymm : ∀ x : K, (iterateFrobeniusEquiv K 2 c).symm (x ^ 2 ^ c) = x := by
    intro x
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv K 2 c).symm_apply_apply x
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hsymm]

theorem frobVecAddEquiv_smul {K : Type} [Field K] [Finite K] [CharP K 2] [PerfectRing K 2] (c : ℕ)
    (μ : K) (v : Fin 4 → K) :
    frobVecAddEquiv K c (μ • v) = (μ ^ 2 ^ c) • frobVecAddEquiv K c v := by
  funext i
  change (iterateFrobeniusEquiv K 2 c) (μ * v i) =
    μ ^ 2 ^ c * (iterateFrobeniusEquiv K 2 c) (v i)
  rw [map_mul, iterateFrobeniusEquiv_def]

theorem exists_smul_of_comm_twisted_sz {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    [PerfectRing K 2] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {W : Type} [AddGroup W]
    {c : ℕ} {φ : W ≃+ (Fin 4 → K)} (y : W →+ W)
    (hy : ∀ (g : ↥(suzukiGroup a K)) (w : W),
      y (φ.symm ((((g : Matrix.GeneralLinearGroup (Fin 4) K)) :
          Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c) *ᵥ φ w)) =
        φ.symm ((((g : Matrix.GeneralLinearGroup (Fin 4) K)) :
          Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c) *ᵥ φ (y w))) :
    ∃ μ : K, ∀ w : W, φ (y w) = μ • φ w := by
  classical
  let F : (Fin 4 → K) →+ (Fin 4 → K) :=
    φ.toAddMonoidHom.comp (y.comp φ.symm.toAddMonoidHom)
  let Ψ : (Fin 4 → K) ≃+ (Fin 4 → K) := frobVecAddEquiv K c
  let y' : (Fin 4 → K) →+ (Fin 4 → K) :=
    Ψ.symm.toAddMonoidHom.comp (F.comp Ψ.toAddMonoidHom)
  have h1 : ∀ v, y' (suzukiS a 1 0 *ᵥ v) = suzukiS a 1 0 *ᵥ y' v := by
    intro v
    have hy1 := hy (suzukiSElt a K 1 0) (φ.symm (Ψ v))
    have hy1' : y (φ.symm ((suzukiS a 1 0).map (· ^ 2 ^ c) *ᵥ Ψ v)) =
        φ.symm ((suzukiS a 1 0).map (· ^ 2 ^ c) *ᵥ F (Ψ v)) := by
      simpa [F, coe_suzukiSElt] using hy1
    calc y' (suzukiS a 1 0 *ᵥ v)
        = Ψ.symm (F (Ψ (suzukiS a 1 0 *ᵥ v))) := rfl
      _ = Ψ.symm (F ((suzukiS a 1 0).map (· ^ 2 ^ c) *ᵥ Ψ v)) := by
            rw [frobVecAddEquiv_mulVec]
      _ = Ψ.symm (φ (y (φ.symm ((suzukiS a 1 0).map (· ^ 2 ^ c) *ᵥ Ψ v)))) := rfl
      _ = Ψ.symm ((suzukiS a 1 0).map (· ^ 2 ^ c) *ᵥ F (Ψ v)) := by
            rw [hy1', AddEquiv.apply_symm_apply]
      _ = (suzukiS a 1 0) *ᵥ Ψ.symm (F (Ψ v)) := by
            rw [frobVecAddEquiv_symm_mulVec]
      _ = (suzukiS a 1 0) *ᵥ y' v := rfl
  have h2 : ∀ (v : K) (w : Fin 4 → K),
      y' (suzukiS a 0 v *ᵥ w) = suzukiS a 0 v *ᵥ y' w := by
    intro v w
    have hy2 := hy (suzukiSElt a K 0 v) (φ.symm (Ψ w))
    have hy2' : y (φ.symm ((suzukiS a 0 v).map (· ^ 2 ^ c) *ᵥ Ψ w)) =
        φ.symm ((suzukiS a 0 v).map (· ^ 2 ^ c) *ᵥ F (Ψ w)) := by
      simpa [F, coe_suzukiSElt] using hy2
    calc y' (suzukiS a 0 v *ᵥ w)
        = Ψ.symm (F (Ψ (suzukiS a 0 v *ᵥ w))) := rfl
      _ = Ψ.symm (F ((suzukiS a 0 v).map (· ^ 2 ^ c) *ᵥ Ψ w)) := by
            rw [frobVecAddEquiv_mulVec]
      _ = Ψ.symm (φ (y (φ.symm ((suzukiS a 0 v).map (· ^ 2 ^ c) *ᵥ Ψ w)))) := rfl
      _ = Ψ.symm ((suzukiS a 0 v).map (· ^ 2 ^ c) *ᵥ F (Ψ w)) := by
            rw [hy2', AddEquiv.apply_symm_apply]
      _ = (suzukiS a 0 v) *ᵥ Ψ.symm (F (Ψ w)) := by
            rw [frobVecAddEquiv_symm_mulVec]
      _ = (suzukiS a 0 v) *ᵥ y' w := rfl
  have hW : ∀ w, y' (suzukiW K *ᵥ w) = suzukiW K *ᵥ y' w := by
    intro w
    have hyW := hy (suzukiWElt a K) (φ.symm (Ψ w))
    have hyW' : y (φ.symm ((suzukiW K).map (· ^ 2 ^ c) *ᵥ Ψ w)) =
        φ.symm ((suzukiW K).map (· ^ 2 ^ c) *ᵥ F (Ψ w)) := by
      simpa [F, coe_suzukiWElt] using hyW
    calc y' (suzukiW K *ᵥ w)
        = Ψ.symm (F (Ψ (suzukiW K *ᵥ w))) := rfl
      _ = Ψ.symm (F ((suzukiW K).map (· ^ 2 ^ c) *ᵥ Ψ w)) := by
            rw [frobVecAddEquiv_mulVec]
      _ = Ψ.symm (φ (y (φ.symm ((suzukiW K).map (· ^ 2 ^ c) *ᵥ Ψ w)))) := rfl
      _ = Ψ.symm ((suzukiW K).map (· ^ 2 ^ c) *ᵥ F (Ψ w)) := by
            rw [hyW', AddEquiv.apply_symm_apply]
      _ = suzukiW K *ᵥ Ψ.symm (F (Ψ w)) := by
            rw [frobVecAddEquiv_symm_mulVec]
      _ = suzukiW K *ᵥ y' w := rfl
  obtain ⟨μ, hμ⟩ := CFSG.Quasithin.Vol2.Ch10.SecB.C10P34.eq_smul_of_comm_suzuki a y' h1 h2 hW
  refine ⟨μ ^ 2 ^ c, fun w => ?_⟩
  let v : Fin 4 → K := Ψ.symm (φ w)
  have hv : Ψ v = φ w := Ψ.apply_symm_apply (φ w)
  have h := congrArg (fun t => Ψ t) (hμ v)
  have hleft : Ψ (y' v) = φ (y w) := by
    simp [y', F, hv]
  have hright : Ψ (μ • v) = (μ ^ 2 ^ c) • φ w := by
    rw [frobVecAddEquiv_smul, hv]
  rw [hleft, hright] at h
  exact h

theorem matrix_map_pow_mul {K : Type} [Field K] [CharP K 2] [PerfectRing K 2] (c : ℕ)
    (M N : Matrix (Fin 4) (Fin 4) K) :
    ((M * N).map (· ^ 2 ^ c)) = M.map (· ^ 2 ^ c) * N.map (· ^ 2 ^ c) := by
  have h : (fun x : K => x ^ 2 ^ c) = ⇑(iterateFrobeniusEquiv K 2 c) := by
    funext x
    rw [iterateFrobeniusEquiv_def]
  rw [h, Matrix.map_mul]

theorem card_eigenspace_suzukiD_map_pow_le {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ (2 * a + 1)) {l : Kˣ} (hl : l ≠ 1) (c : ℕ) (σ : K) :
    Nat.card {v : Fin 4 → K // (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v = σ • v} ≤
      Nat.card K := by
  have hf : Function.Injective (fun x : K => x ^ 2 ^ c) := by
    intro x y hxy
    exact iterateFrobenius_inj K 2 c (by simpa [iterateFrobenius_def] using hxy)
  have hd : ∀ i j : Fin 4, (dEnt a l i) ^ 2 ^ c = (dEnt a l j) ^ 2 ^ c → i = j := by
    intro i j h
    exact dEnt_injective hK hl i j (hf h)
  have hMdiag : (suzukiD a l).map (· ^ 2 ^ c) =
      Matrix.diagonal (fun i : Fin 4 => (dEnt a l i) ^ 2 ^ c) := by
    rw [suzukiD_eq_diagonal, Matrix.diagonal_map]
    simp
  have hq2 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hdne0 : ∀ i : Fin 4, dEnt a l i ≠ 0 := by
    intro i
    fin_cases i <;> simp [dEnt] <;>
      first
        | exact pow_ne_zero _ (Units.ne_zero l)
        | exact zpow_ne_zero _ (Units.ne_zero l)
  by_cases hσ : σ = 0
  · subst hσ
    have hzero : ∀ v : {v : Fin 4 → K // (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v = (0 : K) • v},
        v.1 = 0 := by
      intro v
      have hv : (Matrix.diagonal (fun i : Fin 4 => (dEnt a l i) ^ 2 ^ c)) *ᵥ v.1 = 0 := by
        simpa [hMdiag] using v.2
      funext i
      have hi := congrFun hv i
      rw [Matrix.mulVec_diagonal] at hi
      exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ (hdne0 i))
    haveI : Subsingleton
        {v : Fin 4 → K // (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v = (0 : K) • v} :=
      ⟨fun a b => Subtype.ext (by rw [hzero a, hzero b])⟩
    haveI : Nonempty
        {v : Fin 4 → K // (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v = (0 : K) • v} :=
      ⟨⟨0, by simp⟩⟩
    rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
    exact hq2
  · have hset : Nat.card
        {v : Fin 4 → K // (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v = σ • v} =
        Nat.card {v : Fin 4 → K // σ⁻¹ • ((suzukiD a l).map (· ^ 2 ^ c) *ᵥ v) = v} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      constructor
      · intro hv
        calc σ⁻¹ • ((suzukiD a l).map (· ^ 2 ^ c) *ᵥ v)
            = σ⁻¹ • (σ • v) := by rw [hv]
          _ = v := by rw [smul_smul, inv_mul_cancel₀ hσ, one_smul]
      · intro hv
        calc (suzukiD a l).map (· ^ 2 ^ c) *ᵥ v
            = σ • (σ⁻¹ • ((suzukiD a l).map (· ^ 2 ^ c) *ᵥ v)) := by
              rw [smul_smul, mul_inv_cancel₀ hσ, one_smul]
          _ = σ • v := by rw [hv]
    rw [hset]
    have h1 : Nat.card {v : Fin 4 → K //
        σ⁻¹ • ((suzukiD a l).map (· ^ 2 ^ c) *ᵥ v) = v} =
        Nat.card {v : Fin 4 → K // ∀ i, σ⁻¹ * ((dEnt a l i) ^ 2 ^ c * v i) = v i} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      constructor
      · intro hv i
        have h := congrFun hv i
        simpa [hMdiag, Matrix.mulVec_diagonal] using h
      · intro hv
        funext i
        simpa [hMdiag, Matrix.mulVec_diagonal] using hv i
    rw [h1]
    exact CFSG.Quasithin.H.card_fix_diag_le _ hd σ⁻¹

end CFSG.Quasithin.Stroth

end
