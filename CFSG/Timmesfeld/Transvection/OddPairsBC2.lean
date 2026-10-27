module

public import CFSG.Timmesfeld.Transvection.OddPairs
import CFSG.Timmesfeld.Transvection.OddPairsCone
import CFSG.Timmesfeld.Transvection.OddPairsModel
import CFSG.Timmesfeld.Transvection.OddModelWeyl
import CFSG.Timmesfeld.Transvection.OddModelSU3
import CFSG.Timmesfeld.Transvection.OddModelHeis
import CFSG.Timmesfeld.Transvection.OddModelBC2Struct
import CFSG.LieType.Universal.Unitary.Extras.Unipotent
import CFSG.Timmesfeld.RankTwo.LevisBCone

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H]
  (Ψ₀ : SU (unitaryInvolution F 2 n) (2 * r) →* H) (θ : SU (unitaryInvolution F 2 n) 3 →* H)

theorem oddFrameMap_conj_levelWeyl_of_even (k : Fin ((2 * r + 1) / 2))
    {γ : Fin ((2 * r + 1) / 2) → ℤ} (hγ : Even (γ (bcLastIdx r (Nat.one_le_of_lt hr))))
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ)
    (y : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl k γ))
    (hy : (y : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ k *
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) *
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ k)⁻¹) :
    Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm k)) * oddFrameMap hFn hr Ψ₀ θ γ x *
      (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm k)))⁻¹ = oddFrameMap hFn hr Ψ₀ θ _ y := by
  obtain ⟨x₀, hx₀⟩ := rootGroup_le_range_oddEmb (σ := unitaryInvolution F 2 n)
    (hσ := unitaryInvolution_involutive hFn) (r := r) (Nat.one_le_of_lt hr)
    (by simpa only [bcLastIdx] using hγ) x.2
  have hodd : oddEmb (unitaryInvolution F 2 n) r
      (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm k)) =
      levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ k := by
    rw [oddEmb_levelWeyl r (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
      ((finCastOdd r).symm k), Equiv.apply_symm_apply]
  have hstep : (y : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      oddEmb (unitaryInvolution F 2 n) r
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            ((finCastOdd r).symm k) * x₀ *
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            ((finCastOdd r).symm k))⁻¹) := by
    rw [hy, ← hx₀, ← hodd]
    simp only [map_mul, map_inv]
  have hEven' : Even (((CFSG.LieType.Steinberg.RootSystem.ofCartan
      (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
      (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl k γ)
      (bcLastIdx r (Nat.one_le_of_lt hr))) := by
    exact (even_reflection_last_iff (Nat.one_le_of_lt hr) k γ).2 hγ
  have hxval : oddFrameMap hFn hr Ψ₀ θ γ x = Ψ₀ x₀ :=
    oddFrameMap_eq_of_even hFn hr Ψ₀ θ hγ x x₀ hx₀
  have hyval : oddFrameMap hFn hr Ψ₀ θ
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
        (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
        (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl k γ) y =
      Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            ((finCastOdd r).symm k) * x₀ *
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            ((finCastOdd r).symm k))⁻¹) :=
    oddFrameMap_eq_of_even hFn hr Ψ₀ θ hEven' y _ hstep.symm
  rw [hxval, hyval]
  simp only [map_mul, map_inv]

private theorem oddFrameMap_conj_levelWeyl_prev_of_idx_last
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (ha : idx a = bcLastIdx r (Nat.one_le_of_lt hr))
    {γ : Fin ((2 * r + 1) / 2) → ℤ} (hγ : toStd (2 * r + 1) γ = wt a)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ)
    (y : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl (bcPrevIdx r hr) γ))
    (hy : (y : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (bcPrevIdx r hr) *
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) *
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (bcPrevIdx r hr))⁻¹) :
    Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm (bcPrevIdx r hr))) * oddFrameMap hFn hr Ψ₀ θ γ x *
      (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm (bcPrevIdx r hr))))⁻¹ =
      oddFrameMap hFn hr Ψ₀ θ _ y := by
  have hPval : (bcPrevIdx r hr).val + 1 = (bcLastIdx r (Nat.one_le_of_lt hr)).val := by
    simp only [bcPrevIdx, bcLastIdx, Fin.val_mk]
    omega
  have hPshort : (bcPrevIdx r hr).val + 1 < (2 * r + 1) / 2 := by
    simp only [bcPrevIdx, Fin.val_mk]
    omega
  have hxmem : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr))).range := by
    have h := rootGroup_le_range_su3Emb (σ := unitaryInvolution F 2 n)
      (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
      (Nat.not_even_two_mul_add_one r) (a := a) hγ x.2
    rwa [ha] at h
  obtain ⟨A, hA⟩ := hxmem
  have hconj := levelWeyl_one_conj_su3Emb (σ := unitaryInvolution F 2 n)
    (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
    (Nat.not_even_two_mul_add_one r) (k := bcPrevIdx r hr) hPshort A
  rw [show (⟨(bcPrevIdx r hr).val + 1, hPshort⟩ : Fin ((2 * r + 1) / 2)) =
    bcLastIdx r (Nat.one_le_of_lt hr) from Fin.ext hPval] at hconj
  have hyval : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcPrevIdx r hr) A = y := by
    rw [← hconj, hA, ← hy]
  have hxval : oddFrameMap hFn hr Ψ₀ θ γ x = θ A :=
    oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ (a := a) ha hγ x A hA
  have hidx : idx (levelPermS (bcPrevIdx r hr) a) = bcPrevIdx r hr := by
    rw [idx_levelPermS_of_val_succ (m := 2 * r + 1) hPval, ha, Equiv.swap_apply_right]
  have hto : toStd (2 * r + 1)
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
        (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
        (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl (bcPrevIdx r hr) γ) =
      wt (levelPermS (bcPrevIdx r hr) a) :=
    toStd_reflection_of_wt (bcPrevIdx r hr) hγ
  have hyval2 : oddFrameMap hFn hr Ψ₀ θ _ y = oddPrevLift hFn hr Ψ₀ θ A :=
    oddFrameMap_eq_of_toStd_prev hFn hr Ψ₀ θ (a := levelPermS (bcPrevIdx r hr) a) hidx hto
      y A hyval
  rw [hxval, hyval2, finCastOdd_symm_bcPrevIdx hr, ← oddPrevLift_apply]

private theorem levelWeyl_prev_conj_su3Emb (A : SU (unitaryInvolution F 2 n) 3) :
    levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (bcPrevIdx r hr) *
        su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r) (bcPrevIdx r hr) A *
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (bcPrevIdx r hr))⁻¹ =
      su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr)) A := by
  have hPval : (bcPrevIdx r hr).val + 1 = (bcLastIdx r (Nat.one_le_of_lt hr)).val := by
    simp only [bcPrevIdx, bcLastIdx, Fin.val_mk]
    omega
  have hPshort : (bcPrevIdx r hr).val + 1 < (2 * r + 1) / 2 := by
    simp only [bcPrevIdx, Fin.val_mk]
    omega
  have hinv : (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
      (bcPrevIdx r hr))⁻¹ =
      levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (bcPrevIdx r hr) :=
    levelWeyl_one_inv (m := 2 * r + 1) (unitaryInvolution_involutive hFn) (bcPrevIdx r hr)
  have hnn : levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
      (bcPrevIdx r hr) * levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        (bcPrevIdx r hr) = 1 := by
    simpa only [hinv] using mul_inv_cancel (levelWeyl (unitaryInvolution_involutive hFn)
      ⟨1, one_mem_traceZero⟩ (bcPrevIdx r hr))
  have hconj := levelWeyl_one_conj_su3Emb (σ := unitaryInvolution F 2 n)
    (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
    (Nat.not_even_two_mul_add_one r) (k := bcPrevIdx r hr) hPshort A
  rw [show (⟨(bcPrevIdx r hr).val + 1, hPshort⟩ : Fin ((2 * r + 1) / 2)) =
    bcLastIdx r (Nat.one_le_of_lt hr) from Fin.ext hPval] at hconj
  rw [← hconj, hinv]
  rw [show levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (bcPrevIdx r hr) *
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
              (bcPrevIdx r hr) * su3Emb (unitaryInvolution F 2 n)
                (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr)) A *
            levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
              (bcPrevIdx r hr)) *
          levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (bcPrevIdx r hr) =
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (bcPrevIdx r hr) * levelWeyl (unitaryInvolution_involutive hFn)
              ⟨1, one_mem_traceZero⟩ (bcPrevIdx r hr)) * su3Emb (unitaryInvolution F 2 n)
              (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr)) A *
          (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (bcPrevIdx r hr) * levelWeyl (unitaryInvolution_involutive hFn)
              ⟨1, one_mem_traceZero⟩ (bcPrevIdx r hr)) from by group]
  rw [hnn, one_mul, mul_one]

private theorem levelWeyl_prev_conj_oddPrevLift (A : SU (unitaryInvolution F 2 n) 3) :
    Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (cPrevIdx r hr)) *
        oddPrevLift hFn hr Ψ₀ θ A *
        (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (cPrevIdx r hr)))⁻¹ = θ A := by
  have hn : levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
      (cPrevIdx r hr) * levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        (cPrevIdx r hr) = 1 := by
    have h := mul_inv_cancel (levelWeyl (unitaryInvolution_involutive hFn)
      ⟨1, one_mem_traceZero⟩ (cPrevIdx r hr))
    rwa [levelWeyl_one_inv (m := 2 * r) (unitaryInvolution_involutive hFn) (cPrevIdx r hr)] at h
  have hu : Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
      (cPrevIdx r hr)) * Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        (cPrevIdx r hr)) = 1 := by
    rw [← map_mul, hn, map_one]
  rw [oddPrevLift_apply, inv_eq_of_mul_eq_one_right hu]
  rw [show Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (cPrevIdx r hr)) *
          (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
              (cPrevIdx r hr)) * θ A *
            Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
              (cPrevIdx r hr))) *
          Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
            (cPrevIdx r hr)) =
        (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
              (cPrevIdx r hr)) * Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn)
                ⟨1, one_mem_traceZero⟩ (cPrevIdx r hr))) * θ A *
            (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
              (cPrevIdx r hr)) * Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn)
                ⟨1, one_mem_traceZero⟩ (cPrevIdx r hr))) from by group]
  rw [hu, one_mul, mul_one]

private theorem oddFrameMap_conj_levelWeyl_prev_of_idx_prev
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (ha : idx a = bcPrevIdx r hr)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} (hγ : toStd (2 * r + 1) γ = wt a)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ)
    (y : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl (bcPrevIdx r hr) γ))
    (hy : (y : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (bcPrevIdx r hr) *
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) *
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (bcPrevIdx r hr))⁻¹) :
    Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm (bcPrevIdx r hr))) * oddFrameMap hFn hr Ψ₀ θ γ x *
      (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm (bcPrevIdx r hr))))⁻¹ =
      oddFrameMap hFn hr Ψ₀ θ _ y := by
  have hPval : (bcPrevIdx r hr).val + 1 = (bcLastIdx r (Nat.one_le_of_lt hr)).val := by
    simp only [bcPrevIdx, bcLastIdx, Fin.val_mk]
    omega
  have hxmem : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcPrevIdx r hr)).range := by
    have h := rootGroup_le_range_su3Emb (σ := unitaryInvolution F 2 n)
      (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
      (Nat.not_even_two_mul_add_one r) (a := a) hγ x.2
    rwa [ha] at h
  obtain ⟨A, hA⟩ := hxmem
  have hyval : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr)) A = y := by
    rw [hy, ← hA, levelWeyl_prev_conj_su3Emb hFn hr A]
  have hxval : oddFrameMap hFn hr Ψ₀ θ γ x = oddPrevLift hFn hr Ψ₀ θ A :=
    oddFrameMap_eq_of_toStd_prev hFn hr Ψ₀ θ (a := a) ha hγ x A hA
  have hidx : idx (levelPermS (bcPrevIdx r hr) a) = bcLastIdx r (Nat.one_le_of_lt hr) := by
    rw [idx_levelPermS_of_val_succ (m := 2 * r + 1) hPval, ha, Equiv.swap_apply_left]
  have hto : toStd (2 * r + 1)
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
        (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
        (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl (bcPrevIdx r hr) γ) =
      wt (levelPermS (bcPrevIdx r hr) a) :=
    toStd_reflection_of_wt (bcPrevIdx r hr) hγ
  have hyval2 : oddFrameMap hFn hr Ψ₀ θ _ y = θ A :=
    oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ (a := levelPermS (bcPrevIdx r hr) a) hidx hto
      y A hyval
  rw [hxval, hyval2, finCastOdd_symm_bcPrevIdx hr]
  exact levelWeyl_prev_conj_oddPrevLift hFn hr Ψ₀ θ A

private theorem oddFrameMap_conj_levelWeyl_last_of_idx_last (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (ha : idx a = bcLastIdx r (Nat.one_le_of_lt hr))
    {γ : Fin ((2 * r + 1) / 2) → ℤ} (hγ : toStd (2 * r + 1) γ = wt a)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ)
    (y : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl
        (bcLastIdx r (Nat.one_le_of_lt hr)) γ))
    (hy : (y : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (bcLastIdx r (Nat.one_le_of_lt hr)) *
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) *
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (bcLastIdx r (Nat.one_le_of_lt hr)))⁻¹) :
    Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm (bcLastIdx r (Nat.one_le_of_lt hr)))) *
        oddFrameMap hFn hr Ψ₀ θ γ x *
      (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm (bcLastIdx r (Nat.one_le_of_lt hr)))))⁻¹ =
      oddFrameMap hFn hr Ψ₀ θ _ y := by
  have hL : ¬ (bcLastIdx r (Nat.one_le_of_lt hr)).val + 1 < (2 * r + 1) / 2 := by
    simp only [bcLastIdx, Fin.val_mk]
    omega
  have hxmem : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcLastIdx r (Nat.one_le_of_lt hr))).range := by
    have h := rootGroup_le_range_su3Emb (σ := unitaryInvolution F 2 n)
      (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
      (Nat.not_even_two_mul_add_one r) (a := a) hγ x.2
    rwa [ha] at h
  obtain ⟨A, hA⟩ := hxmem
  let w₀ : SU (unitaryInvolution F 2 n) 3 :=
    levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (0 : Fin (3 / 2))
  have hsu3w : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr)) w₀ =
      levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        (bcLastIdx r (Nat.one_le_of_lt hr)) :=
    su3Emb_levelWeyl (σ := unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (n := 2 * r + 1) (Nat.not_even_two_mul_add_one r)
      (k := bcLastIdx r (Nat.one_le_of_lt hr)) hL ⟨1, one_mem_traceZero⟩
  have hyval : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr)) (w₀ * A * w₀⁻¹) = y := by
    rw [hy, ← hA, ← hsu3w, ← map_mul, ← map_inv, ← map_mul]
  have hidx : idx (levelPermS (bcLastIdx r (Nat.one_le_of_lt hr)) a) =
      bcLastIdx r (Nat.one_le_of_lt hr) := by
    rw [levelPermS_of_not_lt_of_idx_eq hL ha, idx_swap, ha]
  have hto : toStd (2 * r + 1)
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
        (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
        (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl
          (bcLastIdx r (Nat.one_le_of_lt hr)) γ) =
      wt (levelPermS (bcLastIdx r (Nat.one_le_of_lt hr)) a) :=
    toStd_reflection_of_wt (bcLastIdx r (Nat.one_le_of_lt hr)) hγ
  have hxval : oddFrameMap hFn hr Ψ₀ θ γ x = θ A :=
    oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ (a := a) ha hγ x A hA
  have hyval2 : oddFrameMap hFn hr Ψ₀ θ _ y = θ (w₀ * A * w₀⁻¹) :=
    oddFrameMap_eq_of_toStd_last hFn hr Ψ₀ θ
      (a := levelPermS (bcLastIdx r (Nat.one_le_of_lt hr)) a) hidx hto y (w₀ * A * w₀⁻¹) hyval
  rw [hxval, hyval2, finCastOdd_symm_bcLastIdx hr, hd.map_levelWeyl_last]
  rw [← map_mul, ← map_inv, ← map_mul]

private theorem oddFrameMap_conj_levelWeyl_last_of_idx_prev (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (ha : idx a = bcPrevIdx r hr)
    {γ : Fin ((2 * r + 1) / 2) → ℤ} (hγ : toStd (2 * r + 1) γ = wt a)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ)
    (y : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl
        (bcLastIdx r (Nat.one_le_of_lt hr)) γ))
    (hy : (y : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (bcLastIdx r (Nat.one_le_of_lt hr)) *
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) *
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (bcLastIdx r (Nat.one_le_of_lt hr)))⁻¹) :
    Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm (bcLastIdx r (Nat.one_le_of_lt hr)))) *
        oddFrameMap hFn hr Ψ₀ θ γ x *
      (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm (bcLastIdx r (Nat.one_le_of_lt hr)))))⁻¹ =
      oddFrameMap hFn hr Ψ₀ θ _ y := by
  have hL : ¬ (bcLastIdx r (Nat.one_le_of_lt hr)).val + 1 < (2 * r + 1) / 2 := by
    simp only [bcLastIdx, Fin.val_mk]
    omega
  have hne : idx a ≠ bcLastIdx r (Nat.one_le_of_lt hr) := by
    rw [ha]
    exact bcPrevIdx_ne_bcLastIdx hr
  have hidx : levelPermS (bcLastIdx r (Nat.one_le_of_lt hr)) a = a :=
    levelPermS_of_not_lt_of_idx_ne hL hne
  have hto : toStd (2 * r + 1)
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
        (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
        (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl
          (bcLastIdx r (Nat.one_le_of_lt hr)) γ) = wt a := by
    have h := toStd_reflection_of_wt (bcLastIdx r (Nat.one_le_of_lt hr)) hγ
    rwa [hidx] at h
  have hoddL : ¬Even (((CFSG.LieType.Steinberg.RootSystem.ofCartan
      (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
      (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl
        (bcLastIdx r (Nat.one_le_of_lt hr)) γ) (bcLastIdx r (Nat.one_le_of_lt hr))) :=
    not_even_last_of_toStd_eq_wt hr (Or.inr ha) hto
  have hPne : ((CFSG.LieType.Steinberg.RootSystem.ofCartan
      (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
      (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl
        (bcLastIdx r (Nat.one_le_of_lt hr)) γ) (bcPrevIdx r hr) ≠ 0 := by
    intro h
    exact bcPrevIdx_ne_bcLastIdx hr (ha.symm.trans
      ((prev_eq_zero_iff_of_toStd_eq_wt hr (Or.inr ha) hto).1 h))
  have hxmem : (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) ∈
      (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
        (bcPrevIdx r hr)).range := by
    have h := rootGroup_le_range_su3Emb (σ := unitaryInvolution F 2 n)
      (hσ := unitaryInvolution_involutive hFn) (n := 2 * r + 1)
      (Nat.not_even_two_mul_add_one r) (a := a) hγ x.2
    rwa [ha] at h
  obtain ⟨A, hA⟩ := hxmem
  have hxval : oddFrameMap hFn hr Ψ₀ θ γ x = oddPrevLift hFn hr Ψ₀ θ A :=
    oddFrameMap_eq_of_toStd_prev hFn hr Ψ₀ θ (a := a) ha hγ x A hA
  obtain ⟨u, v, -, hxuv⟩ := (mem_rootGroup_iff_suHeis (unitaryInvolution_involutive hFn)
    (Nat.not_even_two_mul_add_one r) (a := a) (γ := γ) hγ x).mp x.2
  have hfix : levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        (bcLastIdx r (Nat.one_le_of_lt hr)) * (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) *
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (bcLastIdx r (Nat.one_le_of_lt hr)))⁻¹ =
      (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) := by
    rw [← hxuv, levelWeyl_one_conj_suHeis (unitaryInvolution_involutive hFn)
      (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr)) a u v, hidx]
  have hyval : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcPrevIdx r hr) A = y := by
    rw [hy, hfix, hA]
  have hyval2 : oddFrameMap hFn hr Ψ₀ θ _ y = oddPrevLift hFn hr Ψ₀ θ A :=
    oddFrameMap_eq_of_prev hFn hr Ψ₀ θ hoddL hPne y A hyval
  rw [hxval, hyval2, finCastOdd_symm_bcLastIdx hr]
  have hc := hd.commute_levelWeyl_last_oddPrevLift A
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]

namespace OddFrameCompatible

variable {hFn hr Ψ₀ θ}

theorem oddFrameMap_conj_levelWeyl (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {k : Fin ((2 * r + 1) / 2)}
    (hk : k = bcPrevIdx r hr ∨ k = bcLastIdx r (Nat.one_le_of_lt hr))
    {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : γ ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
      (bcLastIdx r (Nat.one_le_of_lt hr)))
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ)
    (y : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      ((CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).refl k γ))
    (hy : (y : SU (unitaryInvolution F 2 n) (2 * r + 1)) =
      levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ k *
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1)) *
        (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ k)⁻¹) :
    Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm k)) * oddFrameMap hFn hr Ψ₀ θ γ x *
      (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        ((finCastOdd r).symm k)))⁻¹ = oddFrameMap hFn hr Ψ₀ θ _ y := by
  by_cases hEven : Even (γ (bcLastIdx r (Nat.one_le_of_lt hr)))
  · exact oddFrameMap_conj_levelWeyl_of_even hFn hr Ψ₀ θ k hEven x y hy
  · obtain ⟨a, ha, hγa⟩ :=
      exists_toStd_eq_wt_of_mem_pairRoots_bc2 (p := 2) (f := n) hFn hr hγ hEven
    rcases ha with haL | haP
    · rcases hk with rfl | rfl
      · exact oddFrameMap_conj_levelWeyl_prev_of_idx_last hFn hr Ψ₀ θ haL hγa x y hy
      · exact oddFrameMap_conj_levelWeyl_last_of_idx_last hFn hr Ψ₀ θ hd haL hγa x y hy
    · rcases hk with rfl | rfl
      · exact oddFrameMap_conj_levelWeyl_prev_of_idx_prev hFn hr Ψ₀ θ haP hγa x y hy
      · exact oddFrameMap_conj_levelWeyl_last_of_idx_prev hFn hr Ψ₀ θ hd haP hγa x y hy

theorem extendsToHom_cone_bc2 (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (hpos : ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
          (bcLastIdx r (Nat.one_le_of_lt hr)) ∩
        (CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).pos)
      (oddFrameMap hFn hr Ψ₀ θ)) :
    ∀ α ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
        (bcLastIdx r (Nat.one_le_of_lt hr)),
      ∀ β ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
        (bcLastIdx r (Nat.one_le_of_lt hr)),
      ¬CFSG.LieType.Universal.IsNegMultiple α β →
      ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
        ((Unitary.rootDatum hFn (2 * r + 1)).cone α β ∩
          pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
            (bcLastIdx r (Nat.one_le_of_lt hr))) (oddFrameMap hFn hr Ψ₀ θ) :=
  extendsToHom_cone_pairRoots (D := Unitary.rootDatum hFn (2 * r + 1))
    (i := bcPrevIdx r hr) (j := bcLastIdx r (Nat.one_le_of_lt hr))
    (n := fun k => levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ k)
    (hn := fun k _ _ _ _ hx => levelWeyl_conj_mem' (m := 2 * r + 1)
      (unitaryInvolution_involutive hFn) k hx)
    (ñ := fun k => Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
      ((finCastOdd r).symm k)))
    (φ := oddFrameMap hFn hr Ψ₀ θ)
    (hñ := fun k hk γ hγ x y hy => oddFrameMap_conj_levelWeyl hd hk hγ x y hy)
    (hpos := hpos)
    (hrank := fun k _ => extendsToHom_rankOne_oddFrameMap hFn hr Ψ₀ θ k)

theorem extendsToHom_cone_of_pos (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (hpos : ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (pairRoots (Unitary.rootDatum hFn (2 * r + 1)) (bcPrevIdx r hr)
          (bcLastIdx r (Nat.one_le_of_lt hr)) ∩
        (CFSG.LieType.Steinberg.RootSystem.ofCartan
          (Unitary.rootDatum hFn (2 * r + 1)).isFiniteType
          (Unitary.rootDatum hFn (2 * r + 1)).divisible).pos)
      (oddFrameMap hFn hr Ψ₀ θ)) :
    ∀ i j, ∀ α ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i j,
      ∀ β ∈ pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i j,
      ¬CFSG.LieType.Universal.IsNegMultiple α β →
      ExtendsToHom (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
        ((Unitary.rootDatum hFn (2 * r + 1)).cone α β ∩
          pairRoots (Unitary.rootDatum hFn (2 * r + 1)) i j) (oddFrameMap hFn hr Ψ₀ θ) :=
  extendsToHom_cone hd (extendsToHom_cone_bc2 hd hpos)

end OddFrameCompatible

end CFSG.Timmesfeld.Transvection
