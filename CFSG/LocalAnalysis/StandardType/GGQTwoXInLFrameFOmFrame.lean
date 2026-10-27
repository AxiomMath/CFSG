module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFOmNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFOmFrame2
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.StandardType.TraceFrame
open CFSG.StandardType.QTwoOmFrame

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def frameW {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) : Set V :=
  {v | g (g v) + g v + v = 0}

private noncomputable def frameFix {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (g : V ≃ₗ[K] V) : Subgroup (V ≃ₗ[K] V) :=
  fixingSubgroup (V ≃ₗ[K] V) (frameW g)

private lemma frameW_coord {K M U V : Type} [Field K] [Finite K] [CharP K 2]
    [Field M] [Algebra K M] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {n : ℕ}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} {g : V ≃ₗ[K] V} {a : Fin n → M}
    (hga : ∀ d w, g (Φ (d, w)) = Φ (fun i => a i * d i, w))
    {d : Fin n → M} {w : U} (hv : Φ (d, w) ∈ frameW g) :
    ∀ i, a i = 1 → d i = 0 := by
  classical
  intro i hai
  have hv' : g (g (Φ (d, w))) + g (Φ (d, w)) + Φ (d, w) = 0 := hv
  let π : V →ₗ[K] (Fin n → M) := (LinearMap.fst K (Fin n → M) U).comp Φ.symm.toLinearMap
  have hπ0 : π (g (g (Φ (d, w))) + g (Φ (d, w)) + Φ (d, w)) = 0 := by
    rw [hv', map_zero]
  have h1 : π (g (g (Φ (d, w)))) = fun i => a i * (a i * d i) := by
    change (LinearMap.fst K (Fin n → M) U) (Φ.symm (g (g (Φ (d, w))))) = _
    rw [hga d w, hga (fun i => a i * d i) w]
    simp
  have h2 : π (g (Φ (d, w))) = fun i => a i * d i := by
    change (LinearMap.fst K (Fin n → M) U) (Φ.symm (g (Φ (d, w)))) = _
    rw [hga d w]
    simp
  have h3 : π (Φ (d, w)) = d := by
    change (LinearMap.fst K (Fin n → M) U) (Φ.symm (Φ (d, w))) = _
    simp
  have hsum : (fun i => a i * (a i * d i)) + (fun i => a i * d i) + d = 0 := by
    have h := hπ0
    rw [map_add, map_add, h1, h2, h3] at h
    exact h
  have hi := congrFun hsum i
  simp only [Pi.add_apply] at hi
  rw [hai] at hi
  simp only [one_mul] at hi
  have hdd : d i + d i = 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc d i + d i = (2 : K) • d i := (two_smul K (d i)).symm
      _ = 0 := by rw [h2, zero_smul]
  rw [hdd] at hi
  simpa using hi

private lemma frameW_single_mem {K M U V : Type} [Field K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} {g : V ≃ₗ[K] V} {a : Fin n → M}
    (hga : ∀ d w, g (Φ (d, w)) = Φ (fun i => a i * d i, w))
    (ha3 : ∀ i, a i ^ 3 = 1) {i : Fin n} (hai : a i ≠ 1) :
    Φ (Pi.single i 1, 0) ∈ frameW g := by
  classical
  have hcube : a i ^ 2 + a i + 1 = 0 :=
    QTwoFrameTorus.frame_sq_add_add_one_eq_zero (ha3 i) hai
  let s : Fin n → M := Pi.single i (1 : M)
  have hfun : (fun j => a j * (a j * s j) + a j * s j + s j) = 0 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simpa [s, pow_two] using hcube
    · simp [s, Pi.single_eq_of_ne hj]
  change g (g (Φ (s, 0))) + g (Φ (s, 0)) + Φ (s, 0) = 0
  rw [hga, hga, ← map_add, ← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  have hpair : ((fun i => a i * (a i * s i)) + (fun i => a i * s i)) + s =
      fun j => a j * (a j * s j) + a j * s j + s j := by
    funext j
    simp [Pi.add_apply]
  rw [hpair, hfun]
  exact map_zero Φ

private lemma frame_exists_coeff_ne_one {K M U V : Type} [Field K] [Field M] [Algebra K M]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} {x : V ≃ₗ[K] V} {a : Fin n → M}
    (hxne : x ≠ 1) (hxa : ∀ d w, x (Φ (d, w)) = Φ (fun i => a i * d i, w)) :
    ∃ i, a i ≠ 1 := by
  classical
  by_contra h
  simp only [not_exists, not_not] at h
  have ha1 : a = fun _ => 1 := funext h
  have hx1 : x = 1 := by
    ext v
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [hxa d w]
    simp [ha1]
  exact hxne hx1

private lemma frameW_mem_of_comm {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {g h : V ≃ₗ[K] V} (hcomm : h * g = g * h) {v : V} (hv : v ∈ frameW g) :
    h v ∈ frameW g := by
  change g (g (h v)) + g (h v) + h v = 0
  have hgen : ∀ w : V, g (h w) = h (g w) := by
    intro w
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hcomm]
  have h1 : g (h v) = h (g v) := hgen v
  have h2 : g (g (h v)) = h (g (g v)) := by
    rw [hgen v, hgen (g v)]
  calc g (g (h v)) + g (h v) + h v
      = h (g (g v)) + h (g v) + h v := by rw [h2, h1]
    _ = h (g (g v) + g v + v) := by rw [← map_add, ← map_add]
    _ = h 0 := by rw [show g (g v) + g v + v = 0 from hv]
    _ = 0 := map_zero h

private lemma frame_coeff_ne_one {K M U V : Type} [Field K] [Finite K] [CharP K 2]
    [Field M] [Finite M] [Algebra K M] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {E : Subgroup ↥(orthDerived Q)} {x : ↥(orthDerived Q)}
    {L D J : Subgroup ↥(orthDerived Q)} (hC : GGQTwoFRCfg E x L D J)
    [hfinR : Finite ↥(orthDerived Q)]
    {n : ℕ} {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hM : Nat.card M = 4) {a : Fin n → M} (ha3 : ∀ i, a i ^ 3 = 1)
    (hxa : ∀ d w, (x : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => a i * d i, w))
    (hEtorus : ∀ a : Fin n → M, (∀ i, a i ^ 3 = 1) → ∃ e ∈ E,
      ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => a i * d i, w)) :
    ∀ j, a j ≠ 1 := by
  classical
  obtain ⟨-, -, -, -, hxne, hxL, hLcomp, -, hECL, -⟩ := hC
  intro j hj
  let C : Subgroup ↥(orthDerived Q) := Subgroup.centralizer ({x} : Set ↥(orthDerived Q))
  let N : Subgroup ↥(orthDerived Q) :=
    C ⊓ (frameFix (x : V ≃ₗ[K] V)).comap (Subgroup.subtype (orthDerived Q))
  have hx_not_fix : (x : V ≃ₗ[K] V) ∉ frameFix (x : V ≃ₗ[K] V) := by
    intro hxfix
    have hxne' : (x : V ≃ₗ[K] V) ≠ 1 := fun h => hxne (Subtype.ext h)
    obtain ⟨i, hai⟩ := frame_exists_coeff_ne_one (Φ := Φ) hxne' (fun d w => hxa d w)
    have hvW : Φ (Pi.single i 1, 0) ∈ frameW (x : V ≃ₗ[K] V) :=
      frameW_single_mem (Φ := Φ) (g := (x : V ≃ₗ[K] V)) (fun d w => hxa d w) ha3 hai
    have hfix := (mem_fixingSubgroup_iff (V ≃ₗ[K] V)).mp hxfix
      (Φ (Pi.single i 1, 0)) hvW
    have hfix' : (x : V ≃ₗ[K] V) (Φ (Pi.single i 1, 0)) = Φ (Pi.single i 1, 0) := hfix
    rw [hxa] at hfix'
    have hp := congrArg Prod.fst (Φ.injective hfix')
    have hi := congrFun hp i
    exact hai (by simpa using hi)
  have hx_not_N : x ∉ N := by
    intro hxN
    exact hx_not_fix (Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hxN).2)
  have hL_not_le_N : ¬ L ≤ N := fun hLN => hx_not_N (hLN hxL)
  have hN_le_C : N ≤ C := inf_le_left
  have hN_normal : (N.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN_le_C]
    intro n c hn hc
    have hcC : c * n * c⁻¹ ∈ C :=
      C.mul_mem (C.mul_mem hc (Subgroup.mem_inf.mp hn).1) (C.inv_mem hc)
    have hnFix : (n : V ≃ₗ[K] V) ∈ frameFix (x : V ≃ₗ[K] V) :=
      Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hn).2
    have hcInvC : c⁻¹ ∈ C := C.inv_mem hc
    have hcomm : ((c⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V) =
        (x : V ≃ₗ[K] V) * ((c⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) := by
      have hR : c⁻¹ * x = x * c⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp hcInvC x (by simp)).symm
      simpa using congrArg (Subgroup.subtype (orthDerived Q)) hR
    have hcncFix : ((c * n * c⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈
        frameFix (x : V ≃ₗ[K] V) := by
      rw [frameFix, mem_fixingSubgroup_iff]
      intro v hv
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      change ((c : V ≃ₗ[K] V) * (n : V ≃ₗ[K] V) * (c : V ≃ₗ[K] V)⁻¹) v = v
      have hvW : ((c⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) v ∈
          frameW (x : V ≃ₗ[K] V) := frameW_mem_of_comm hcomm hv
      have hnfix : (n : V ≃ₗ[K] V) (((c⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) v) =
          ((c⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) v :=
        (mem_fixingSubgroup_iff (V ≃ₗ[K] V)).mp hnFix _ hvW
      calc ((c : V ≃ₗ[K] V) * (n : V ≃ₗ[K] V) * (c : V ≃ₗ[K] V)⁻¹) v
          = (c : V ≃ₗ[K] V) ((n : V ≃ₗ[K] V) (((c⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) v)) := by
              simp [LinearEquiv.mul_apply]
        _ = (c : V ≃ₗ[K] V) (((c⁻¹ : ↥(orthDerived Q)) : V ≃ₗ[K] V) v) := by rw [hnfix]
        _ = v := by simp
    exact Subgroup.mem_inf.mpr ⟨hcC, Subgroup.mem_comap.mpr hcncFix⟩
  have hNsub : IsSubnormal N C := IsSubnormal.step hN_le_C hN_normal (IsSubnormal.refl C)
  have hdich := isComponentOf_le_or_commutator_eq_bot hLcomp hNsub
  have hN_le_centralizer : N ≤ Subgroup.centralizer (L : Set ↥(orthDerived Q)) := by
    have hcomm : ⁅L, N⁆ = ⊥ := by
      rcases hdich with hLN | h
      · exact absurd hLN hL_not_le_N
      · exact h
    have h' : ⁅N, L⁆ = ⊥ := by rwa [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h'
  obtain ⟨ζ, hζ3, hζ1⟩ := QTwoFrameTorus.frame_exists_pow_three_eq_one_ne_one hM
  let b : Fin n → M := Function.update (fun _ => 1) j ζ
  have hb3 : ∀ i, b i ^ 3 = 1 := by
    intro i
    by_cases hi : i = j
    · subst hi
      simp [b, hζ3]
    · simp [b, Function.update_of_ne hi]
  obtain ⟨t, htE, htb⟩ := hEtorus b hb3
  have htC : t ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [htb, hxa, hxa, htb]
    exact congrArg Φ (Prod.ext (by ext i; ring) rfl)
  have htFix : (t : V ≃ₗ[K] V) ∈ frameFix (x : V ≃ₗ[K] V) := by
    rw [frameFix, mem_fixingSubgroup_iff]
    intro v hv
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    change (t : V ≃ₗ[K] V) (Φ (d, w)) = Φ (d, w)
    rw [htb]
    have hdj : d j = 0 := frameW_coord (Φ := Φ) (g := (x : V ≃ₗ[K] V)) hxa hv j hj
    have hbd : (fun i => b i * d i) = d := by
      ext i
      by_cases hi : i = j
      · subst hi
        simp [b, Function.update_self, hdj]
      · simp [b, Function.update_of_ne hi]
    rw [hbd]
  have htN : t ∈ N := Subgroup.mem_inf.mpr ⟨htC, Subgroup.mem_comap.mpr htFix⟩
  have htEC : t ∈ E ⊓ Subgroup.centralizer (L : Set ↥(orthDerived Q)) :=
    ⟨htE, hN_le_centralizer htN⟩
  rw [hECL] at htEC
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htEC
  let v₀ : V := Φ (Pi.single j (1 : M), 0)
  let F : Subgroup ↥(orthDerived Q) :=
    (fixingSubgroup (V ≃ₗ[K] V) ({v₀} : Set V)).comap (Subgroup.subtype (orthDerived Q))
  have hxfixv : (x : V ≃ₗ[K] V) v₀ = v₀ := by
    change (x : V ≃ₗ[K] V) (Φ (Pi.single j (1 : M), 0)) =
      Φ (Pi.single j (1 : M), 0)
    rw [hxa]
    have hsingle : (fun i => a i * (((Pi.single j (1 : M)) : Fin n → M) i)) =
        ((Pi.single j (1 : M)) : Fin n → M) := by
      ext i
      by_cases hi : i = j
      · subst hi
        simp [hj]
      · simp [Pi.single_eq_of_ne hi]
    rw [hsingle]
  have hx_in_F : x ∈ F := by
    rw [Subgroup.mem_comap, mem_fixingSubgroup_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simpa using hxfixv
  have ht_in_F : t ∈ F := by
    rw [← hk]
    exact F.zpow_mem hx_in_F k
  have htfixv : (t : V ≃ₗ[K] V) v₀ = v₀ :=
    (mem_fixingSubgroup_iff (V ≃ₗ[K] V)).mp (Subgroup.mem_comap.mp ht_in_F) v₀
      (Set.mem_singleton v₀)
  have htval : (t : V ≃ₗ[K] V) v₀ = Φ (Pi.single j ζ, 0) := by
    change (t : V ≃ₗ[K] V) (Φ (Pi.single j (1 : M), 0)) = _
    rw [htb]
    refine congrArg Φ (Prod.ext ?_ rfl)
    ext i
    by_cases hi : i = j
    · subst hi
      simp [b, Function.update_self]
    · simp [b, Function.update_of_ne hi, Pi.single_eq_of_ne hi]
  have hp := congrArg Prod.fst (Φ.injective (htval.symm.trans htfixv))
  exact hζ1 (by simpa using congrFun hp j)

theorem exists_traceFrame_of_cfg_orth {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {E : Subgroup ↥(orthDerived Q)} {x : ↥(orthDerived Q)} {L D J : Subgroup ↥(orthDerived Q)}
    (hC : GGQTwoFRCfg E x L D J) :
    ∃ (n : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (_ : Algebra K M) (τ : M ≃+* M)
      (U : Type) (_ : AddCommGroup U) (_ : Module K U) (Φ : ((Fin n → M) × U) ≃ₗ[K] V) (c : M),
      Nat.card M = 4 ∧ (∀ y, τ y = y ^ 2) ∧ c ^ 2 ≠ c ∧
      (∀ d d' w w', QuadraticMap.polarBilin Q (Φ (d, w)) (Φ (d', w')) =
        ∑ i, Algebra.trace K M (τ (d i) * d' i) +
          QuadraticMap.polarBilin Q (Φ (0, w)) (Φ (0, w'))) ∧
      (∀ d w, algebraMap K M (Q (Φ (d, w))) =
        ∑ i, τ (d i) * d i + algebraMap K M (Q (Φ (0, w)))) ∧
      (∀ d w, (x : V ≃ₗ[K] V) (Φ (d, w)) = Φ (c • d, w)) ∧
      (∀ e ∈ E, ∃ a : Fin n → M, (∀ i, a i ^ 3 = 1) ∧
        ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => a i * d i, w)) ∧
      ∀ a : Fin n → M, (∀ i, a i ^ 3 = 1) → ∃ e ∈ E,
        ∀ d w, (e : V ≃ₗ[K] V) (Φ (d, w)) = Φ (fun i => a i * d i, w) := by
  classical
  obtain ⟨n, M, hMfield, hMfinite, hMalg, τ, U, hUadd, hUmod, Φ, hMcard, hτ2,
    hpolar, hnorm, hEact, hEtorus⟩ :=
    exists_normFrame_of_isElemAbelian_orth hK hQ hC.1 hC.2.2.1
  have hCcopy := hC
  obtain ⟨-, -, -, hxE, hxne, -, -, -, -, -, -, -, -, -⟩ := hC
  have hfinV : Finite V := Module.finite_of_finite K
  have hfinVV : Finite (V → V) := @Pi.finite V (fun _ => V) hfinV (fun _ => hfinV)
  have hfinR : Finite ↥(orthDerived Q) :=
    @Finite.of_injective ↥(orthDerived Q) (V → V) hfinVV
      (fun z => ((z : V ≃ₗ[K] V) : V → V))
      (fun p q h => Subtype.ext (LinearEquiv.ext (congrFun h)))
  have hτ : ∀ y, τ (τ y) = y :=
    QTwoFrameTorus.frame_tau_tau (τ := τ) hMcard hτ2
  obtain ⟨a, ha3, hxa⟩ := hEact x hxE
  have ha_ne : ∀ i, a i ≠ 1 :=
    frame_coeff_ne_one (K := K) (M := M) (U := U) (V := V) (Q := Q) (E := E) (x := x)
      (L := L) (D := D) (J := J) (hfinR := hfinR) hCcopy hMcard ha3 hxa hEtorus
  have hxne' : (x : V ≃ₗ[K] V) ≠ 1 := fun h => hxne (Subtype.ext h)
  obtain ⟨i0, hi0⟩ := frame_exists_coeff_ne_one (Φ := Φ) hxne' hxa
  let c : M := a i0
  have hc3 : c ^ 3 = 1 := ha3 i0
  have hc1 : c ≠ 1 := hi0
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 3 ≠ 0)] at hc3
    exact zero_ne_one hc3
  have hc2 : c ^ 2 ≠ c := by
    intro h
    have h' : c * c = c * 1 := by simpa [pow_two] using h
    exact hc1 (mul_left_cancel₀ hc0 h')
  have hroots : ∀ i, a i = c ∨ a i = c ^ 2 := by
    intro i
    rcases QTwoFrameTorus.frame_eq_one_or_eq_or_sq hMcard hc3 hc1 (ha3 i) with h | h | h
    · exact absurd h (ha_ne i)
    · exact Or.inl h
    · exact Or.inr h
  let Φ' : ((Fin n → M) × U) ≃ₗ[K] V :=
    ((framePsi (K := K) hK a c τ).prodCongr (LinearEquiv.refl K U)).trans Φ
  have hΦ'a : ∀ d w, Φ' (d, w) = Φ (framePsi (K := K) hK a c τ d, w) := fun d w => rfl
  have hpsi0 : framePsi (K := K) hK a c τ 0 = 0 := by
    ext i
    rw [framePsi_apply]
    simp
  have hΦ'0 : ∀ w, Φ' (0, w) = Φ (0, w) := by
    intro w
    rw [hΦ'a, hpsi0]
  have hxΦ' : ∀ d w, (x : V ≃ₗ[K] V) (Φ' (d, w)) = Φ' (c • d, w) := by
    intro d w
    rw [hΦ'a, hxa, hΦ'a]
    have hmul := framePsi_mul (K := K) hK a c τ (fun _ => c) d
    rw [frameTwist_const hc2 hroots hτ2] at hmul
    have hcd : c • d = fun i => c * d i := by
      ext i
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hcd]
    exact congrArg (fun y => Φ (y, w)) hmul.symm
  have hpolar' : ∀ d d' w w', QuadraticMap.polarBilin Q (Φ' (d, w)) (Φ' (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) +
        QuadraticMap.polarBilin Q (Φ' (0, w)) (Φ' (0, w')) := by
    intro d d' w w'
    rw [hΦ'a, hΦ'a, hpolar]
    simp only [hΦ'0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [framePsi_apply, framePsi_apply]
    by_cases h : a i = c
    · simp [h]
    · simp only [h, if_false]
      rw [hτ, ← trace_tau (K := K) (M := M) (hK := hK) (τ := τ) (τ (d i) * d' i),
        map_mul τ, hτ]
  have hnorm' : ∀ d w, algebraMap K M (Q (Φ' (d, w))) =
      ∑ i, τ (d i) * d i + algebraMap K M (Q (Φ' (0, w))) := by
    intro d w
    rw [hΦ'a, hnorm]
    simp only [hΦ'0]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [framePsi_apply]
    by_cases h : a i = c
    · simp [h]
    · simp only [h, if_false]
      rw [hτ, mul_comm]
  have hEact' : ∀ e ∈ E, ∃ a' : Fin n → M, (∀ i, a' i ^ 3 = 1) ∧
      ∀ d w, (e : V ≃ₗ[K] V) (Φ' (d, w)) = Φ' (fun i => a' i * d i, w) := by
    intro e he
    obtain ⟨ae, hae3, hae⟩ := hEact e he
    refine ⟨frameTwist a c τ ae, frameTwist_cube a c τ hae3, ?_⟩
    intro d w
    rw [hΦ'a, hΦ'a, hae]
    congr 1
    rw [framePsi_mul (b := frameTwist a c τ ae) (d := d), frameTwist_invol a c τ hτ ae]
  have hEtorus' : ∀ a' : Fin n → M, (∀ i, a' i ^ 3 = 1) → ∃ e ∈ E,
      ∀ d w, (e : V ≃ₗ[K] V) (Φ' (d, w)) = Φ' (fun i => a' i * d i, w) := by
    intro a' ha'3
    obtain ⟨e, he, hee⟩ := hEtorus (frameTwist a c τ a') (frameTwist_cube a c τ ha'3)
    refine ⟨e, he, ?_⟩
    intro d w
    rw [hΦ'a, hΦ'a, hee]
    congr 1
    rw [framePsi_mul (b := a') (d := d)]
  refine ⟨n, M, hMfield, hMfinite, hMalg, τ, U, hUadd, hUmod, Φ', c,
    hMcard, hτ2, hc2, hpolar', hnorm', hxΦ', hEact', hEtorus'⟩

end CFSG.StandardType

end
