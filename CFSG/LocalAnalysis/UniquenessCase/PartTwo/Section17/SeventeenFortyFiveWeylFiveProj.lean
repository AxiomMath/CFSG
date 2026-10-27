module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveWeights
import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Matrix CFSG.Open

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem weylFivePower_statedProj [Finite K] (hK : ringChar K ≠ 31) (H : Subgroup (GL ι K))
    (hZ : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ H → c ^ 31 = 1 → c = 1)
    (hdim : Fintype.card ι ≤ 4 ∨ (Fintype.card ι ≤ 9 ∧ ∃ J : Matrix ι ι K, IsUnit J.det ∧
      ∀ x ∈ H, (x : Matrix ι ι K)ᵀ * J * x = J))
    (hnf : ∀ α : MulAut (StatedProj H), α ^ 5 = 1 → ∃ (m : ℕ) (A : GL ι K) (σ : K ≃+* K),
      ¬ 5 ∣ m ∧ ∃ θ : H →* H, (∀ x : H, (θ x : GL ι K) = semilinConjGL A σ x) ∧
        ∀ x : H, (α ^ m) (QuotientGroup.mk x : StatedProj H) = QuotientGroup.mk (θ x)) :
    WeylFivePower (StatedProj H) := by
  classical
  by_cases hι : Nonempty ι
  · intro α Ē hα5 hExp hComm hmap
    let Z : Subgroup H := (StatedScalars ι K).subgroupOf H
    have hZcenter : Z ≤ Subgroup.center H := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      have hz' : (z : GL ι K) ∈ Subgroup.center (GL ι K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        simpa only [Z, Subgroup.mem_subgroupOf, StatedScalars] using hz
      exact Subgroup.mem_center_iff.mp hz' (h : GL ι K)
    have hZcentral : ∀ z ∈ Z, ∀ h : H, z * h = h * z :=
      fun z hz h => (Subgroup.mem_center_iff.mp (hZcenter hz) h).symm
    have hZpow : ∀ z ∈ Z, z ^ 31 = 1 → z = 1 := by
      intro z hz hz31
      have hzrange : (z : GL ι K) ∈ (Matrix.GeneralLinearGroup.scalar ι).range := by
        simpa only [Z, Subgroup.mem_subgroupOf, StatedScalars] using hz
      obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hzrange
      have hmem : Matrix.GeneralLinearGroup.scalar ι c ∈ H := by
        rw [hc]; exact z.2
      have hc31 : c ^ 31 = 1 := by
        apply @CFSG.LinearAlgebra.generalLinearGroup_scalar_injective ι K _ _ hι _
        have hpow : (Matrix.GeneralLinearGroup.scalar ι c : GL ι K) ^ 31 = 1 := by
          rw [hc]
          simpa using congrArg (fun y : H => (y : GL ι K)) hz31
        rwa [map_pow, map_one]
      have hc1 : c = 1 := hZ c hmem hc31
      apply Subtype.ext
      rw [← hc, hc1]
      simp
    have hcomm : ∀ x : H, QuotientGroup.mk x ∈ Ē → x ^ 31 = 1 →
        ∀ y : H, QuotientGroup.mk y ∈ Ē → y ^ 31 = 1 → x * y = y * x := by
      intro x hxb hx31 y hyb hy31
      let c : H := x * y * x⁻¹ * y⁻¹
      have hcZ : c ∈ Z := by
        rw [← QuotientGroup.eq_one_iff c]
        dsimp only [c]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [hComm (QuotientGroup.mk x) hxb (QuotientGroup.mk y) hyb,
          mul_assoc (QuotientGroup.mk y) (QuotientGroup.mk x) ((QuotientGroup.mk x)⁻¹),
          mul_inv_cancel, mul_one, mul_inv_cancel]
      have hc31 : c ^ 31 = 1 := by
        have hcy : c * y = x * y * x⁻¹ := by
          dsimp only [c]; group
        have h1 : (c * y) ^ 31 = 1 := by
          rw [hcy, conj_pow, hy31]
          simp
        have h2 : (c * y) ^ 31 = c ^ 31 := by
          rw [Commute.mul_pow (hZcentral c hcZ y) 31, hy31, mul_one]
        rwa [h2] at h1
      have hc1 : c = 1 := hZpow c hcZ hc31
      have hxyx : x * y * x⁻¹ = y := by
        apply mul_inv_eq_one.mp
        simpa only [c] using hc1
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by rw [hxyx]
    let E : Subgroup H :=
      { carrier := {x : H | QuotientGroup.mk x ∈ Ē ∧ x ^ 31 = 1}
        one_mem' := by
          refine ⟨?_, ?_⟩
          · simp
          · simp
        mul_mem' := by
          intro x y hx hy
          obtain ⟨hxb, hx31⟩ := hx
          obtain ⟨hyb, hy31⟩ := hy
          have hxy := hcomm x hxb hx31 y hyb hy31
          refine ⟨?_, ?_⟩
          · rw [QuotientGroup.mk_mul]
            exact Ē.mul_mem hxb hyb
          · rw [Commute.mul_pow hxy 31, hx31, hy31, mul_one]
        inv_mem' := by
          intro x hx
          obtain ⟨hxb, hx31⟩ := hx
          refine ⟨?_, ?_⟩
          · rw [QuotientGroup.mk_inv]
            exact Ē.inv_mem hxb
          · rw [inv_pow, hx31, inv_one] }
    have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      intro x hx y hy
      exact hcomm x hx.1 hx.2 y hy.1 hy.2
    have hEexp : ∀ x ∈ E.map H.subtype, x ^ 31 = 1 := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
      simpa using congrArg (fun y : H => (y : GL ι K)) he.2
    have hEcomm' : ∀ x ∈ E.map H.subtype, ∀ y ∈ E.map H.subtype, x * y = y * x := by
      intro x hx y hy
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hy
      simpa using congrArg (fun z : H => (z : GL ι K)) (hEcomm e he f hf)
    obtain ⟨m, A, σ, h5m, θ, hθsemilin, hθα⟩ := hnf α hα5
    have hθmem : ∀ x ∈ E, θ x ∈ E := by
      intro x hx
      obtain ⟨hxb, hx31⟩ := hx
      refine ⟨?_, ?_⟩
      · have hmapm : Ē.map (α ^ m).toMonoidHom = Ē := map_pow_of_map_eq hmap m
        have h1 : (α ^ m) (QuotientGroup.mk x : StatedProj H) ∈ Ē := by
          rw [← hmapm]
          exact Subgroup.mem_map_of_mem (α ^ m).toMonoidHom hxb
        rwa [hθα x] at h1
      · rw [← map_pow, hx31, map_one]
    have hθE' : ∀ x ∈ E.map H.subtype, semilinConjGL A σ x ∈ E.map H.subtype := by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
      have h1 : (θ e : GL ι K) ∈ E.map H.subtype :=
        Subgroup.mem_map_of_mem H.subtype (hθmem e he)
      rwa [hθsemilin e] at h1
    have hdim' : Fintype.card ι ≤ 4 ∨ (Fintype.card ι ≤ 9 ∧ ∃ J : Matrix ι ι K, IsUnit J.det ∧
        ∀ x ∈ E.map H.subtype, (x : Matrix ι ι K)ᵀ * J * x = J) := by
      rcases hdim with h | ⟨h9, J, hJ, hJinv⟩
      · exact Or.inl h
      · refine Or.inr ⟨h9, J, hJ, ?_⟩
        intro x hx
        obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
        simpa using hJinv e e.2
    obtain ⟨c, hc⟩ := weylFive_weights hK A σ (E.map H.subtype) hEexp hEcomm' hθE' hdim'
    have hθiter : ∀ k : ℕ, ∀ x : H, ((θ^[k] x : H) : GL ι K) =
        (semilinConjGL A σ)^[k] (x : GL ι K) := by
      intro k
      induction k with
      | zero => intro x; rfl
      | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hθsemilin (θ^[k] x), ih x]
    have hEpow : ∀ x ∈ E, θ^[48] x = x ^ c := by
      intro x hx
      apply Subtype.ext
      calc ((θ^[48] x : H) : GL ι K)
          = (semilinConjGL A σ)^[48] (x : GL ι K) := hθiter 48 x
        _ = (x : GL ι K) ^ c := hc (x : GL ι K) (Subgroup.mem_map_of_mem H.subtype hx)
        _ = ((x ^ c : H) : GL ι K) := rfl
    refine ⟨m * 48, c, ?_, ?_⟩
    · exact (by norm_num : Nat.Prime 5).not_dvd_mul h5m (by norm_num)
    · intro ē hē
      obtain ⟨x, hx_eq⟩ := QuotientGroup.mk_surjective ē
      have hx31Z : x ^ 31 ∈ Z := by
        rw [← QuotientGroup.eq_one_iff (x ^ 31)]
        rw [QuotientGroup.mk_pow, hx_eq, hExp ē hē]
      have hcop : (Nat.card Z).Coprime 31 := by
        have h31 : Nat.Prime 31 := by norm_num
        rw [Nat.coprime_comm, h31.coprime_iff_not_dvd]
        intro hdvd
        obtain ⟨z, hzord⟩ := @exists_prime_orderOf_dvd_card' Z _ _ 31 ⟨h31⟩ hdvd
        have hz31 : z ^ 31 = 1 := by
          rw [← hzord, pow_orderOf_eq_one]
        have hz31H : (z : H) ^ 31 = 1 := by
          rw [← Subgroup.coe_pow, hz31]
          rfl
        have hz1 : z = 1 := Subtype.ext (hZpow (z : H) z.2 hz31H)
        rw [hz1, orderOf_one] at hzord
        norm_num at hzord
      obtain ⟨w, hwpow⟩ := (Nat.Coprime.pow_left_bijective hcop).surjective ⟨x ^ 31, hx31Z⟩
      have hw31 : (w : H) ^ 31 = x ^ 31 := by
        simpa using congrArg (fun z : Z => (z : H)) hwpow
      let e : H := x * (w : H)⁻¹
      have heq : QuotientGroup.mk e = ē := by
        dsimp only [e]
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx_eq,
          (QuotientGroup.eq_one_iff (w : H)).mpr w.2]
        simp
      have he : e ∈ E := by
        refine ⟨?_, ?_⟩
        · rw [heq]; exact hē
        · have hxw : Commute x ((w : H)⁻¹) :=
            Commute.inv_right (show Commute x (w : H) from (hZcentral w w.2 x).symm)
          dsimp only [e]
          rw [hxw.mul_pow 31, inv_pow, hw31, mul_inv_cancel]
      have hαiter : ∀ k : ℕ, ((α ^ m) ^ k) (QuotientGroup.mk e) =
          QuotientGroup.mk (θ^[k] e) := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [pow_succ', MulAut.mul_apply, ih, hθα (θ^[k] e), Function.iterate_succ_apply']
      have hfin : (α ^ (m * 48)) ē = ē ^ c := by
        calc (α ^ (m * 48)) ē
            = ((α ^ m) ^ 48) (QuotientGroup.mk e) := by rw [pow_mul, ← heq]
          _ = QuotientGroup.mk (θ^[48] e) := hαiter 48
          _ = QuotientGroup.mk (e ^ c) := by rw [hEpow e he]
          _ = ē ^ c := by rw [← heq, QuotientGroup.mk_pow]
      exact hfin
  · rw [not_nonempty_iff] at hι
    have hmat : Subsingleton (Matrix ι ι K) := by
      refine ⟨fun A B => ?_⟩
      funext i
      exact (hι.false i).elim
    have hunits : Subsingleton (GL ι K) := by
      refine ⟨fun A B => ?_⟩
      exact Units.ext (hmat.allEq (A : Matrix ι ι K) (B : Matrix ι ι K))
    have hH : Subsingleton H := by
      refine ⟨fun a b => ?_⟩
      exact Subtype.ext (hunits.allEq (a : GL ι K) (b : GL ι K))
    have hquot : Subsingleton (StatedProj H) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [hH.allEq a b]
    intro α Ē hα5 hExp hComm hmap
    exact ⟨1, 0, by norm_num, fun x _ => hquot.allEq _ _⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
