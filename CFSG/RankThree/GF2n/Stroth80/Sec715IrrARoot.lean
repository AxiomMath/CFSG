module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAZst

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714 Module
open scoped Matrix commutatorElement

section Lin

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

theorem span_isotropic (b : LinearMap.BilinForm K X) {A : Set X}
    (hA : ∀ x ∈ A, ∀ y ∈ A, b x y = 0) :
    ∀ x ∈ Submodule.span K A, ∀ y ∈ Submodule.span K A, b x y = 0 := by
  have h1 : ∀ y ∈ A, ∀ x ∈ Submodule.span K A, b x y = 0 := by
    intro y hy x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hA x hx y hy
    | zero => simp
    | add x x' _ _ ihx ihx' => simp [ihx, ihx']
    | smul c x _ ihx => simp [ihx]
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem y hy => exact h1 y hy x hx
  | zero => simp
  | add y y' _ _ ihy ihy' => simp [ihy, ihy']
  | smul c y _ ihy => simp [ihy]

theorem card_le_pow_finrank_span [Finite K] [FiniteDimensional K X] (A : AddSubgroup X) :
    Nat.card A ≤ Nat.card K ^ finrank K (Submodule.span K (A : Set X)) := by
  haveI : Finite X := Module.finite_of_finite K
  rw [← Module.natCard_eq_pow_finrank]
  exact Nat.card_mono (Set.toFinite _) Submodule.subset_span

theorem exists_smul_of_pureT_eq {L : Type*} [AddCommGroup L] [Module K L] {f f' : Fin 2 → K}
    {y y' : L} (hf : f ≠ 0) (hy : y ≠ 0) (h : pureT f y = pureT f' y') : ∃ c : K, y = c • y' := by
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hf (funext hh)
  have h1 := congrFun h i
  rw [pureT_apply, pureT_apply] at h1
  refine ⟨(f i)⁻¹ * f' i, ?_⟩
  rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hi, one_smul]

end Lin

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

section Root

variable {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {L₃ L₄ : Type}
  [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
  {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
  {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
  {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
  {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
  {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}

theorem exists_conj_delta_ne_zero (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement)
    (hZcard : Sec7ZCardStatement) {n' : ℕ} (hs : Sec7Hyp hc n' t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {g : G} (hgM : g ∈ M) (hV' : conjSubgroup g Z0 ≤ hc.CN t) (hne : conjSubgroup g Z0 ≠ Z0) :
    ∃ u, ∃ huZ : u ∈ Z0, u ∉ Q ∧
      ∃ hv : (QuotientGroup.mk (⟨g, hgM⟩ : ↥M) : Mbar M Q) *
          QuotientGroup.mk (⟨u, hc.centre_le_M t hZ0 huZ⟩ : ↥M) *
          (QuotientGroup.mk (⟨g, hgM⟩ : ↥M) : Mbar M Q)⁻¹ ∈ bar M Q (conjSubgroup g Z0),
        delta hS t _ (mem_bar_H0_of_CN (bar_mono' hV' hv)) ≠ 0 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  obtain ⟨u, huZ, huQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  refine ⟨u, huZ, huQ, ?_⟩
  let gm : ↥M := ⟨g, hgM⟩
  let um : ↥M := ⟨u, hc.centre_le_M t hZ0 huZ⟩
  have hv₀ : (QuotientGroup.mk gm : Mbar M Q) * QuotientGroup.mk um * (QuotientGroup.mk gm)⁻¹ ∈
      bar M Q (conjSubgroup g Z0) := by
    refine mk_mem_bar (gm * um * gm⁻¹) (mem_conjSubgroup.mpr ?_)
    show g⁻¹ * (g * u * g⁻¹) * g ∈ Z0
    rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    exact huZ
  refine ⟨hv₀, fun h0 => ?_⟩
  have hR := bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) (bar_mono' hV' hv₀)
  have hZ := (delta_eq_zero_iff hCRW hMp hS hs hZ0 hR).mp h0
  have hZ' : g * u * g⁻¹ ∈ Z0 := (mk_mem_bar_iff_sec4 hQZ0 (gm * um * gm⁻¹)).mp hZ
  exact hne (conjSubgroup_eq_self_iff.mpr (hTI g hgM u huZ huQ hZ'))

theorem ConfigAData.card_zStar (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hZcard : Sec7ZCardStatement)
    {n' : ℕ} {r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) (hp : OmegaPlusNat hc t 4)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) (T : TrialityFacts q₃ q₄ μ)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = delta hS t g (mem_bar_H0_of_CN hg))
    {g : G} (hg : IsSymNbr hc t Z0 g) :
    Nat.card (zStar hS t g) = Nat.card (bar M Q Z0) * Nat.card K ^ 9 := by
  classical
  obtain ⟨hgM, -, hne, hZN'⟩ := hg
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hy) x).mp hx
  have hgM' : g⁻¹ ∈ M := M.inv_mem hgM
  have hV₁ : conjSubgroup g⁻¹ Z0 ≤ hc.CN t := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ Z0 := by simpa using mem_conjSubgroup.mp hx
    have h2 := mem_conjSubgroup.mp (hZN' h1)
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h2
  have hne₁ : conjSubgroup g⁻¹ Z0 ≠ Z0 := by
    intro h
    apply hne
    have h1 : g⁻¹ ∈ Subgroup.normalizer (Z0 : Set G) := conjSubgroup_eq_self_iff.mp h
    exact conjSubgroup_eq_self_iff.mpr (by simpa using (Subgroup.normalizer _).inv_mem h1)
  obtain ⟨u, huZ, huQ, hv₁, hΔ1⟩ :=
    exists_conj_delta_ne_zero (hS := hS) hCRW hMp hZcard hs hZ0 hTI hgM' hV₁ hne₁
  set v₁ : Mbar M Q := (QuotientGroup.mk (⟨g⁻¹, hgM'⟩ : ↥M) : Mbar M Q) *
    QuotientGroup.mk (⟨u, hc.centre_le_M t hZ0 huZ⟩ : ↥M) *
    (QuotientGroup.mk (⟨g⁻¹, hgM'⟩ : ↥M) : Mbar M Q)⁻¹
  have hv₁N := bar_mono' hV₁ hv₁
  obtain ⟨f₁, y₁, hf₁, hy₁, hqy₁, hx₁⟩ :=
    D.exists_pureT_of_conj h310chi h52a hMp hs hr hp T hZ0 hgM' hv₁ hv₁N hΔ1
  have hcard := D.card_fixSub_range h310chi h52a hCRW hMp hs hr T hZ0 hSΔ hv₁N hf₁ hy₁ hqy₁ hx₁
  rw [← hcard]
  set gb : Mbar M Q := QuotientGroup.mk (⟨g, hgM⟩ : ↥M)
  have hub : (QuotientGroup.mk (⟨u, hc.centre_le_M t hZ0 huZ⟩ : ↥M) : Mbar M Q) ∈ bar M Q Z0 :=
    mk_mem_bar _ huZ
  have hub1 : (QuotientGroup.mk (⟨u, hc.centre_le_M t hZ0 huZ⟩ : ↥M) : Mbar M Q) ≠ 1 := by
    intro h
    exact huQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hgg : ∀ e, (ρ gb).toAdd ((ρ gb⁻¹).toAdd e) = e := fun e => by
    rw [← act_mul_apply, mul_inv_cancel]; exact act_one_apply _
  have hgg' : ∀ e, (ρ gb⁻¹).toAdd ((ρ gb).toAdd e) = e := fun e => by
    rw [← act_mul_apply, inv_mul_cancel]; exact act_one_apply _
  have hrange : ∀ e, e ∈ LinearMap.range (dlin hS v₁ (mem_bar_H0_of_CN hv₁N)) ↔
      (ρ gb).toAdd e ∈ hc.VtSub hS.model t := by
    intro e
    have h1 := mem_range_dlin_conj_iff h310chi h52a hMp hS hs hr hZ0 gb⁻¹ hub hub1
      (mem_bar_H0_of_CN hv₁N) e
    rw [show ρ gb⁻¹⁻¹ = ρ gb by rw [inv_inv]] at h1
    exact h1
  refine card_eq_of_conj gb⁻¹ fun x => ?_
  rw [inv_inv, zStar, Subgroup.mem_inf, Subgroup.mem_inf, mem_fixSub, mem_fixSub,
    mem_bar_conjSubgroup_iff hgM hQN hQM x]
  refine and_congr Iff.rfl ⟨fun h e he => ?_, fun h e he => ?_⟩
  · have he' := (hrange e).mp he
    rw [act_mul_apply, act_mul_apply, h _ he', hgg']
  · have he' : (ρ gb⁻¹).toAdd e ∈ LinearMap.range (dlin hS v₁ (mem_bar_H0_of_CN hv₁N)) := by
      rw [hrange, hgg]
      exact he
    have h1 := h _ he'
    rw [act_mul_apply, act_mul_apply, hgg] at h1
    exact (ρ gb⁻¹).toAdd.injective h1

theorem comm_eq_one_of_mem_Lambda (hCommN : Sec7CommNStatement) {n' : ℕ} (hs : Sec7Hyp hc n' t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {g : G} (hgM : g ∈ M) (hne : conjSubgroup g Z0 ≠ Z0) {x x' : Mbar M Q}
    (hx : x ∈ bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t)))
    (hx' : x' ∈ bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t))) : ⁅x, x'⁆ = 1 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hy) x).mp hx
  obtain ⟨hxN, hxN'⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hx'N, hx'N'⟩ := Subgroup.mem_inf.mp hx'
  obtain ⟨m, hm, rfl⟩ := exists_of_mem_bar hxN
  obtain ⟨m', hm', rfl⟩ := exists_of_mem_bar hx'N
  have hcZ : ⁅(m : G), (m' : G)⁆ ∈ Z0 :=
    hCommN G M Q Z B hc n' t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hm hm')
  set gb : Mbar M Q := QuotientGroup.mk (⟨g, hgM⟩ : ↥M)
  have hc1 := (mem_bar_conjSubgroup_iff hgM hQN hQM _).mp hxN'
  have hc2 := (mem_bar_conjSubgroup_iff hgM hQN hQM _).mp hx'N'
  have e1 : gb⁻¹ * QuotientGroup.mk m * gb =
      QuotientGroup.mk ((⟨g, hgM⟩ : ↥M)⁻¹ * m * ⟨g, hgM⟩) := rfl
  have e2 : gb⁻¹ * QuotientGroup.mk m' * gb =
      QuotientGroup.mk ((⟨g, hgM⟩ : ↥M)⁻¹ * m' * ⟨g, hgM⟩) := rfl
  rw [e1] at hc1
  rw [e2] at hc2
  have hgm : g⁻¹ * (m : G) * g ∈ hc.CN t := (mk_mem_bar_iff_sec4 hQN _).mp hc1
  have hgm' : g⁻¹ * (m' : G) * g ∈ hc.CN t := (mk_mem_bar_iff_sec4 hQN _).mp hc2
  have hcZg : ⁅g⁻¹ * (m : G) * g, g⁻¹ * (m' : G) * g⁆ ∈ Z0 :=
    hCommN G M Q Z B hc n' t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hgm hgm')
  have e3 : ⁅g⁻¹ * (m : G) * g, g⁻¹ * (m' : G) * g⁆ = g⁻¹ * ⁅(m : G), (m' : G)⁆ * g := by
    simp only [commutatorElement_def]; group
  rw [e3] at hcZg
  have hcQ : ⁅(m : G), (m' : G)⁆ ∈ Q := by
    by_contra hcQ
    apply hne
    have h1 := hTI g hgM _ hcZg (by
      intro h
      apply hcQ
      have h2 := hQM g hgM _ h
      rwa [show g * (g⁻¹ * ⁅(m : G), (m' : G)⁆ * g) * g⁻¹ = ⁅(m : G), (m' : G)⁆ by group] at h2)
      (by rwa [show g * (g⁻¹ * ⁅(m : G), (m' : G)⁆ * g) * g⁻¹ = ⁅(m : G), (m' : G)⁆ by group])
    exact conjSubgroup_eq_self_iff.mpr h1
  rw [show ⁅(QuotientGroup.mk m : Mbar M Q), QuotientGroup.mk m'⁆ = QuotientGroup.mk ⁅m, m'⁆ from
    (map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) m m').symm]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hcQ)

theorem ConfigAData.exists_isotropic_Lambda (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement)
    (hCommN : Sec7CommNStatement) {n' : ℕ} {r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {g : G} (hg : IsSymNbr hc t Z0 g) :
    ∃ A : AddSubgroup (Fin 2 → L₄),
      (∀ X, X ∈ A ↔ ∃ x, ∃ hx : x ∈ bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t)),
        X = eN ⟨delta hS t x (mem_bar_H0_of_CN (Subgroup.mem_inf.mp hx).1),
          delta_mem_deltaSub hS (Subgroup.mem_inf.mp hx).1⟩) ∧
      Nat.card ↥(bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t))) =
        Nat.card (bar M Q Z0) * Nat.card A ∧
      ∀ X ∈ A, ∀ X' ∈ A, formT (QuadraticMap.polarBilin q₄) ψ X X' = 0 := by
  classical
  obtain ⟨hgM, -, hne, hZN'⟩ := hg
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZΛ : bar M Q Z0 ≤ bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t)) :=
    le_inf (bar_mono' (sec7ctr_Z0_le_CN hc hs hZ0)) (bar_mono' hZN')
  obtain ⟨A, hA, hcard⟩ := exists_addSubgroup_card_eq h310chi h52a hCRW hMp hS hs hr hZ0 eN hZΛ
    inf_le_left
  refine ⟨A, fun X => ?_, hcard, ?_⟩
  · rw [hA]
  · intro X hX X' hX'
    obtain ⟨x, hx, rfl⟩ := (hA X).mp hX
    obtain ⟨x', hx', rfl⟩ := (hA X').mp hX'
    have hxN := (Subgroup.mem_inf.mp hx).1
    have hx'N := (Subgroup.mem_inf.mp hx').1
    have h1 := D.bN_eq ⟨delta hS t x (mem_bar_H0_of_CN hxN), delta_mem_deltaSub hS hxN⟩
      ⟨delta hS t x' (mem_bar_H0_of_CN hx'N), delta_mem_deltaSub hS hx'N⟩
    rw [bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 hxN hx'N,
      comm_eq_one_of_mem_Lambda hCommN hs hZ0 hTI hgM hne hx hx'] at h1
    have h0 : cscal hc ρ hs.toSec5.mem 1 = 0 :=
      (cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0 (Subgroup.one_mem _)).mpr rfl
    rw [h0, eq_comm, mul_eq_zero] at h1
    have h2 := h1.resolve_left D.κ_ne
    rw [formT_apply]
    simpa only [QuadraticMap.polarBilin_apply_apply] using h2

theorem ConfigAData.card_Lambda_le (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement)
    (hCommN : Sec7CommNStatement) {n' : ℕ} {r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {g : G} (hg : IsSymNbr hc t Z0 g) :
    Nat.card ↥(bar M Q (hc.CN t) ⊓ bar M Q (conjSubgroup g (hc.CN t))) ≤
      Nat.card (bar M Q Z0) * Nat.card K ^ 8 := by
  classical
  haveI : FiniteDimensional K L₄ := Module.finite_of_finrank_pos (by rw [D.finrank₄]; norm_num)
  obtain ⟨A, -, hcard, hiso⟩ :=
    D.exists_isotropic_Lambda h310chi h52a hCRW hMp hCommN hs hr hZ0 hTI hg
  rw [hcard]
  refine Nat.mul_le_mul_left _ ((card_le_pow_finrank_span (K := K) A).trans ?_)
  refine Nat.pow_le_pow_right Nat.card_pos ?_
  have hker : LinearMap.ker (formT (QuadraticMap.polarBilin q₄) ψ) = ⊥ := by
    have hψφ : ψ * φ = 1 := mul_eq_one_comm.mp D.φψ
    exact ker_formT_eq_bot (fun a ha => D.q₄_nd a fun a' => by
      simpa only [QuadraticMap.polarBilin_apply_apply] using ha a') hψφ
  have h1 := two_mul_finrank_le_of_isotropic_of_ker _ hker
    (span_isotropic _ fun x hx y hy => hiso x hx y hy)
  rw [Module.finrank_pi_fintype, Fin.sum_univ_two, D.finrank₄] at h1
  omega


theorem ConfigAData.forall_actsAsRoot (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement)
    (hY : Sec713YStatement) (hCent : Sec715CentStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) {r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    (hp : OmegaPlusNat hc t 4) (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    (T : TrialityFacts q₃ q₄ μ) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = delta hS t g (mem_bar_H0_of_CN hg))
    (hMat : MatActProp hS t eN Z0)
    (hNormFix : ∀ (z : G) (hzH : z ∈ H0 M Z),
      (∀ e ∈ hc.VtSub hS.model t, (ρ (QuotientGroup.mk (⟨z, hzH.1⟩ : ↥M))).toAdd e = e) →
        z ∈ NormH0 M Z Z0)
    {g : G} (hg : IsSymNbr hc t Z0 g) {f : Fin 2 → K} {y : L₄} (hf : f ≠ 0) (hy : y ≠ 0)
    (hl : HasLine hS t eN Z0 g f y) (s : K) :
    ∃ zb ∈ zStar hS t g, ActsAsRoot hS t eN f zb s := by
  classical
  have hZst := D.card_zStar h310chi h52a hCRW hMp hZcard hs hr hp T hZ0 hTI hSΔ hg
  obtain ⟨R, hRcard, hRs⟩ := D.exists_card_zStar h34 h310chi h51 h52a hA hZt hZcard hZc hZV hCommN
    hY hCent hCRW hMp hs hr hp hZ0 hZN hTI hSΔ hMat hNormFix hg hf hy hl
  have hΛ := D.card_Lambda_le h310chi h52a hCRW hMp hCommN hs hr hZ0 hTI hg
  have hc0 : 0 < Nat.card (bar M Q Z0) := Nat.card_pos
  have hq : 0 < Nat.card K := Nat.card_pos
  have hKm : Nat.card (Multiplicative K) = Nat.card K := Nat.card_congr Multiplicative.toAdd
  have hRle : Nat.card R ≤ Nat.card K := hKm ▸ Subgroup.card_le_card_group R
  have hRq : Nat.card R = Nat.card K := by
    refine le_antisymm hRle ?_
    have h1 : Nat.card (bar M Q Z0) * Nat.card K ^ 9 ≤
        Nat.card (bar M Q Z0) * Nat.card K ^ 8 * Nat.card R := by
      rw [← hZst, hRcard]
      exact Nat.mul_le_mul_right _ hΛ
    rw [show Nat.card K ^ 9 = Nat.card K ^ 8 * Nat.card K by ring, ← mul_assoc] at h1
    exact Nat.le_of_mul_le_mul_left h1 (Nat.mul_pos hc0 (Nat.pow_pos hq))
  have hRtop : R = ⊤ := by
    refine Subgroup.eq_top_of_card_eq R ?_
    rw [hRq, hKm]
  exact hRs s (hRtop ▸ Subgroup.mem_top _)

theorem ConfigAData.rootEltProp_of (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement)
    (hY : Sec713YStatement) (hCent : Sec715CentStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) {r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    (hp : OmegaPlusNat hc t 4) (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    (T : TrialityFacts q₃ q₄ μ) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = delta hS t g (mem_bar_H0_of_CN hg))
    (hMat : MatActProp hS t eN Z0)
    (hNormFix : ∀ (z : G) (hzH : z ∈ H0 M Z),
      (∀ e ∈ hc.VtSub hS.model t, (ρ (QuotientGroup.mk (⟨z, hzH.1⟩ : ↥M))).toAdd e = e) →
        z ∈ NormH0 M Z Z0) :
    RootEltProp hS t eN Z0 := by
  intro g f y hg hf hy hl s
  obtain ⟨zb, hzb, hact⟩ := D.forall_actsAsRoot h34 h310chi h51 h52a hA hZt hZcard hZc hZV
    hCommN hY hCent hCRW hMp hs hr hp T hZ0 hZN hTI hSΔ hMat hNormFix hg hf hy hl s
  obtain ⟨⟨z, hzK, hzeq, -⟩, -, -⟩ := D.exists_actsAsRoot h34 h310chi h51 h52a hA hZt hZcard hCRW
    hMp hs hr hZ0 hZN hTI hSΔ hMat hNormFix hg hf hy hl hzb
  exact ⟨z, hzK, hzeq ▸ hact⟩

theorem ConfigAData.isotropic_of_symNbr (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement)
    (hY : Sec713YStatement) (hCent : Sec715CentStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) {r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    (hp : OmegaPlusNat hc t 4) (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    (T : TrialityFacts q₃ q₄ μ) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZN : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    (hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = delta hS t g (mem_bar_H0_of_CN hg))
    (hMat : MatActProp hS t eN Z0)
    (hNormFix : ∀ (z : G) (hzH : z ∈ H0 M Z),
      (∀ e ∈ hc.VtSub hS.model t, (ρ (QuotientGroup.mk (⟨z, hzH.1⟩ : ↥M))).toAdd e = e) →
        z ∈ NormH0 M Z Z0) :
    ∀ (g : G) (f : Fin 2 → K) (y : L₄), IsSymNbr hc t Z0 g → f ≠ 0 → y ≠ 0 →
      HasLine hS t eN Z0 g f y → f ⬝ᵥ (ψ *ᵥ f) = 0 := by
  classical
  intro g f y hg hf hy hl
  haveI : FiniteDimensional K L₄ := Module.finite_of_finrank_pos (by rw [D.finrank₄]; norm_num)
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hy) x).mp hx
  obtain ⟨hgM, hV', hne, hZN'⟩ := hg
  have hZst := D.card_zStar h310chi h52a hCRW hMp hZcard hs hr hp T hZ0 hTI hSΔ
    ⟨hgM, hV', hne, hZN'⟩
  obtain ⟨R, hRcard, -⟩ := D.exists_card_zStar h34 h310chi h51 h52a hA hZt hZcard hZc hZV hCommN
    hY hCent hCRW hMp hs hr hp hZ0 hZN hTI hSΔ hMat hNormFix ⟨hgM, hV', hne, hZN'⟩ hf hy hl
  obtain ⟨A, hA, hΛcard, hiso⟩ :=
    D.exists_isotropic_Lambda h310chi h52a hCRW hMp hCommN hs hr hZ0 hTI ⟨hgM, hV', hne, hZN'⟩
  have hc0 : 0 < Nat.card (bar M Q Z0) := Nat.card_pos
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hKm : Nat.card (Multiplicative K) = Nat.card K := Nat.card_congr Multiplicative.toAdd
  have hRle : Nat.card R ≤ Nat.card K := hKm ▸ Subgroup.card_le_card_group R
  set Tsp := Submodule.span K (A : Set (Fin 2 → L₄)) with hTsp
  have hTA : Nat.card A ≤ Nat.card K ^ finrank K Tsp := card_le_pow_finrank_span (K := K) A
  have hT8 : 8 ≤ finrank K Tsp := by
    have h1 : Nat.card (bar M Q Z0) * Nat.card K ^ 9 ≤
        Nat.card (bar M Q Z0) * (Nat.card K ^ finrank K Tsp * Nat.card K) := by
      rw [← hZst, hRcard, hΛcard, mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hTA hRle)
    have h2 := Nat.le_of_mul_le_mul_left h1 hc0
    rw [← pow_succ] at h2
    have h3 := (Nat.pow_le_pow_iff_right hq1).mp h2
    omega
  have hTiso := span_isotropic _ fun x hx y hy => hiso x hx y hy
  obtain ⟨u, huZ, huQ, hv₀, hΔ0⟩ :=
    exists_conj_delta_ne_zero (hS := hS) hCRW hMp hZcard hs hZ0 hTI hgM hV' hne
  set gb : Mbar M Q := QuotientGroup.mk (⟨g, hgM⟩ : ↥M)
  set ub : Mbar M Q := QuotientGroup.mk (⟨u, hc.centre_le_M t hZ0 huZ⟩ : ↥M)
  have hv₀N := bar_mono' hV' hv₀
  obtain ⟨a₀, ha₀⟩ := hl _ hv₀ hv₀N
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha₀
    apply hΔ0
    exact congrArg Subtype.val (eN.map_eq_zero_iff.mp ha₀)
  have hx₀ : eN ⟨delta hS t (gb * ub * gb⁻¹) (mem_bar_H0_of_CN hv₀N),
      delta_mem_deltaSub hS hv₀N⟩ = pureT (a₀ • f) y := by
    rw [ha₀, show pureT (a₀ • f) y = pureT (a₀ • f) ((1 : K) • y) by rw [one_smul],
      pureT_smul_smul, mul_one]
  have hf₀ : a₀ • f ≠ 0 := smul_ne_zero ha₀0 hf
  obtain ⟨hqy, -⟩ : q₄ y = 0 ∧ True := by
    obtain ⟨f', y', hf', hy', hqy', hx'⟩ :=
      D.exists_pureT_of_conj h310chi h52a hMp hs hr hp T hZ0 hgM hv₀ hv₀N hΔ0
    rw [hx₀] at hx'
    obtain ⟨c, hc⟩ := exists_smul_of_pureT_eq hf₀ hy hx'
    refine ⟨?_, trivial⟩
    have hqc : q₄ (c • y') = c ^ 2 * q₄ y' := by
      rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]
    rw [hc, hqc, hqy', mul_zero]
  have hub : ub ∈ bar M Q Z0 := mk_mem_bar _ huZ
  have hub1 : ub ≠ 1 := by
    intro h
    exact huQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
  have hgg : ∀ e, (ρ gb).toAdd ((ρ gb⁻¹).toAdd e) = e := fun e => by
    rw [← act_mul_apply, mul_inv_cancel]; exact act_one_apply _
  have hAP : ∀ X ∈ A, contr (ψ *ᵥ (a₀ • f)) X ∈ K ∙ y := by
    intro X hX
    obtain ⟨x, hx, rfl⟩ := (hA X).mp hX
    have hxN := (Subgroup.mem_inf.mp hx).1
    have hxN' := (Subgroup.mem_inf.mp hx).2
    refine (D.mem_fixSub_range_iff h310chi h52a hs hr T hv₀N hf₀ hy hqy hx₀ hxN).mp
      fun e he => ?_
    have he' := (mem_range_dlin_conj_iff h310chi h52a hMp hS hs hr hZ0 gb hub hub1
      (mem_bar_H0_of_CN hv₀N) e).mp he
    have hc1 : gb⁻¹ * x * gb ∈ bar M Q (hc.CN t) :=
      (mem_bar_conjSubgroup_iff hgM hQN hQM x).mp hxN'
    obtain ⟨hcV, -, -⟩ := dmap_CN_facts h310chi h52a hS hs hr hc1
    have h1 := hcV _ he'
    rw [dmap, act_mul_apply, act_mul_apply, hgg, sub_eq_zero] at h1
    exact (ρ gb⁻¹).toAdd.injective h1
  have hTP : Tsp ≤ Submodule.comap (contr (ψ *ᵥ (a₀ • f))) (K ∙ y) :=
    Submodule.span_le.mpr fun X hX => hAP X hX
  by_contra hiso'
  have hd : ψ *ᵥ (a₀ • f) ≠ 0 := by
    intro h0
    apply hf₀
    rw [← Matrix.one_mulVec (a₀ • f), ← D.φψ, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  set d := ψ *ᵥ (a₀ • f) with hddef
  set g₁ : Fin 2 → K := ![d 1, -d 0] with hg₁
  have hg₁0 : g₁ ≠ 0 := by
    intro h0
    apply hd
    have h0' := congrFun h0 0
    have h1' := congrFun h0 1
    simp only [hg₁, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply,
      neg_eq_zero] at h0' h1'
    funext i
    fin_cases i
    · exact h1'
    · exact h0'
  have hdg : d ⬝ᵥ g₁ = 0 := by
    simp only [hg₁, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    ring
  have hgg₁ : g₁ ⬝ᵥ (ψ *ᵥ g₁) ≠ 0 := by
    intro h0
    have h1 := dotProduct_mulVec_self_eq_zero_of_isotropic D.φ_symm D.φψ hg₁0 hdg h0
    rw [hddef, Matrix.mulVec_mulVec, D.φψ, Matrix.one_mulVec, Matrix.mulVec_smul,
      dotProduct_smul, smul_dotProduct, smul_smul, smul_eq_mul] at h1
    exact hiso' ((mul_eq_zero.mp h1).resolve_left (mul_ne_zero ha₀0 ha₀0))
  have hP4 : LinearMap.ker (QuadraticMap.polarBilin q₄) = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun a ha => D.q₄_nd a fun a' => by
      rw [← QuadraticMap.polarBilin_apply_apply, ha, LinearMap.zero_apply]
  have hY : finrank K ↥(Submodule.comap (contr d) (K ∙ y)) ≤ finrank K L₄ + 1 :=
    (finrank_comap_contr_span hd hy).le
  have hgY : ∀ m, pureT g₁ m ∈ Submodule.comap (contr d) (K ∙ y) := by
    intro m
    rw [Submodule.mem_comap, contr_pureT]
    have : d 0 * g₁ 0 + d 1 * g₁ 1 = 0 := by
      simpa [dotProduct, Fin.sum_univ_two] using hdg
    rw [this, zero_smul]
    exact Submodule.zero_mem _
  have h5 := two_mul_finrank_le_of_isotropic_pureT hP4 ψ hgg₁ hY hgY hTP hTiso
  rw [D.finrank₄] at h5
  omega

end Root

end CFSG.RankThree.GF2n.Stroth80.S715L
