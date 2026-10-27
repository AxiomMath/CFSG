module

public import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3Torus
import CFSG.Timmesfeld.Transvection.RelBuildNorm
import CFSG.Timmesfeld.Transvection.OddModelSU3
import CFSG.Timmesfeld.Transvection.OddModelShortTorus
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.Timmesfeld.RankOne
import Certificates.Certificate43

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.Transvection.Pres CFSG.LocalAnalysis.UniquenessCase UC22
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.LieType.Universal.Unitary.SUExtras (toStd_last_odd)
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)

section

private theorem not_even_three : ¬ Even 3 := Nat.not_even_iff_odd.mpr ⟨1, rfl⟩

local notation "heis₃" => suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
  not_even_three (Sum.inl (0 : Fin (3 / 2)))
private def heisValid (n : ℕ) (u v : F) : Prop :=
  v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0

theorem suHeis_three_mem_uc22pwsu3X (u v : F) :
    suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v ∈
      UC22.uc22pwsu3X (unitaryInvolution_involutive hFn) :=
  suHeis_mem (unitaryInvolution_involutive hFn)
    not_even_three Pres.toStd_three_single u v

private theorem heis_mul_self {u v : F} (hv : heisValid n u v) :
    heis₃ u v * heis₃ u v = heis₃ 0 (unitaryInvolution F 2 n u * u) := by
  rw [suHeis_mul (unitaryInvolution_involutive hFn)
    not_even_three hv hv]
  have h1 : u + u = 0 := CharTwo.add_self_eq_zero u
  have h2 : v + v - u * unitaryInvolution F 2 n u =
      unitaryInvolution F 2 n u * u := by
    rw [CharTwo.add_self_eq_zero, zero_sub, CharTwo.neg_eq, mul_comm]
  rw [h1, h2]

private theorem heis_mul_inv {u v v' : F} (hv : heisValid n u v) (hv' : heisValid n u v') :
    heis₃ u v * (heis₃ u v')⁻¹ = heis₃ 0 (v - v') := by
  rw [suHeis_inv (unitaryInvolution_involutive hFn)
    not_even_three hv']
  rw [suHeis_mul (unitaryInvolution_involutive hFn)
    not_even_three hv (Pres.heis_neg_valid (unitaryInvolution_involutive hFn) hv')]
  have h1 : u + -u = 0 := add_neg_cancel u
  have h2 : v + (-v' - u * unitaryInvolution F 2 n u) -
      u * unitaryInvolution F 2 n (-u) = v - v' := by
    rw [map_neg]
    ring
  rw [h1, h2]


section Image

variable {H : Type*} [Group H] {θ : SU (unitaryInvolution F 2 n) 3 →* H}

private theorem exists_conj_heis {g : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    {u v : F} :
    ∃ p : F × F, heisValid n p.1 p.2 ∧
      g * θ (heis₃ u v) * g⁻¹ = θ (heis₃ p.1 p.2) := by
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp (hg _ (suHeis_three_mem_uc22pwsu3X hFn u v))
  obtain ⟨u', v', hv', hx'⟩ :=
    (mem_rootGroup_iff_suHeis (unitaryInvolution_involutive hFn) not_even_three
      toStd_three_single x).mp hx
  refine ⟨(u', v'), hv', ?_⟩
  dsimp only
  rw [hx', hxeq]

private noncomputable def heisImage (hθk : Odd (Nat.card θ.ker)) {g : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (u v : F) : F × F := by
  classical
  exact if hv : heisValid n u v then
    Classical.choose (exists_conj_heis hFn hg (u := u) (v := v))
  else (0, 0)

private theorem heisImage_valid (hθk : Odd (Nat.card θ.ker)) {g : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    {u v : F} (hv : heisValid n u v) :
    heisValid n (heisImage hFn hθk hg u v).1 (heisImage hFn hθk hg u v).2 := by
  rw [heisImage, dif_pos hv]
  exact (Classical.choose_spec (exists_conj_heis hFn hg (u := u) (v := v))).1

private theorem conj_heis_eq_heisImage (hθk : Odd (Nat.card θ.ker)) {g : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    {u v : F} (hv : heisValid n u v) :
    g * θ (heis₃ u v) * g⁻¹ =
      θ (heis₃ (heisImage hFn hθk hg u v).1 (heisImage hFn hθk hg u v).2) := by
  rw [heisImage, dif_pos hv]
  exact (Classical.choose_spec (exists_conj_heis hFn hg (u := u) (v := v))).2

private theorem heis_eq_of_map_eq {u v u' v' : F} (hθk : Odd (Nat.card θ.ker))
    (hv : heisValid n u v) (hv' : heisValid n u' v')
    (he : θ (heis₃ u v) = θ (heis₃ u' v')) : u = u' ∧ v = v' :=
  eq_and_eq_of_map_suHeis_eq hFn hθk hv hv' he

private theorem conj_heis_zero_one_ne_one {g : H}
    (hθk : Odd (Nat.card θ.ker)) :
    g * θ (heis₃ 0 (1 : F)) * g⁻¹ ≠ 1 := by
  intro h
  have hx : θ (heis₃ 0 (1 : F)) = 1 := by
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using this
  have h00 : heis₃ (0 : F) 0 = 1 := by
    rw [suHeis_zero_left (unitaryInvolution_involutive hFn) not_even_three,
      suLong_zero]
  have hv01 : heisValid n 0 (1 : F) := by
    simp only [heisValid]
    rw [map_one, map_zero, mul_zero, add_zero]
    exact CharTwo.add_self_eq_zero 1
  have hv00 : heisValid n 0 (0 : F) := by
    simp only [heisValid]
    simp
  have hbad := heis_eq_of_map_eq hFn hθk hv01 hv00 (by rw [hx, h00, map_one])
  exact one_ne_zero hbad.2

private theorem map_suLong_fixed (hFn : Nat.card F = (2 ^ n) ^ 2) {g : H}
    (hθk : Odd (Nat.card θ.ker)) {μ : F} (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c))) :
    unitaryInvolution F 2 n μ = μ := by
  have hne := conj_heis_zero_one_ne_one (g := g) hFn hθk
  have hμ1 : g * θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
      (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) 0 (1 : F)) * g⁻¹ =
      θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) μ) := by
    have h := hμ 1 (map_one (unitaryInvolution F 2 n))
    rw [mul_one] at h
    rwa [← suHeis_zero_left (unitaryInvolution_involutive hFn) not_even_three] at h
  have hsu : suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) μ ≠ 1 := by
    intro h
    exact hne (hμ1.trans (by rw [h, map_one]))
  have hsum : μ + unitaryInvolution F 2 n μ = 0 := by
    by_contra h
    exact hsu (by rw [suLong, dite_eq_right h])
  exact add_map_eq_zero_iff.mp hsum

private theorem map_suLong_ne_zero (hFn : Nat.card F = (2 ^ n) ^ 2) {g : H}
    (hθk : Odd (Nat.card θ.ker)) {μ : F} (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c))) :
    μ ≠ 0 := by
  intro hμ0
  have hne := conj_heis_zero_one_ne_one (g := g) hFn hθk
  have h := hμ 1 (map_one (unitaryInvolution F 2 n))
  rw [hμ0, zero_mul, suLong_zero, map_one] at h
  rw [← suHeis_zero_left (unitaryInvolution_involutive hFn) not_even_three] at h
  exact hne h

private theorem conj_heis_zero {g : H} {μ : F}
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ) {c : F}
    (hc : c + unitaryInvolution F 2 n c = 0) :
    g * θ (heis₃ 0 c) * g⁻¹ = θ (heis₃ 0 (μ * c)) := by
  have hc' : μ * c + unitaryInvolution F 2 n (μ * c) = 0 := by
    rw [map_mul, hμfix]
    calc μ * c + μ * unitaryInvolution F 2 n c = μ * (c + unitaryInvolution F 2 n c) := by
          ring
      _ = 0 := by rw [hc, mul_zero]
  have h := hμ c (add_map_eq_zero_iff.mp hc)
  rwa [← suHeis_zero_left (unitaryInvolution_involutive hFn) not_even_three,
    ← suHeis_zero_left (unitaryInvolution_involutive hFn) not_even_three] at h


private theorem heisValid_zero_of_trace {c : F}
    (hc : c + unitaryInvolution F 2 n c = 0) : heisValid n 0 c := by
  simp only [heisValid]
  simpa using hc

private theorem trace_sub {u v v' : F} (hv : heisValid n u v) (hv' : heisValid n u v') :
    (v - v') + unitaryInvolution F 2 n (v - v') = 0 := by
  simp only [heisValid] at hv hv'
  rw [map_sub]
  linear_combination hv - hv'

private theorem heisValid_zero_mul {μ c : F} (hμ : unitaryInvolution F 2 n μ = μ)
    (hc : c + unitaryInvolution F 2 n c = 0) : heisValid n 0 (μ * c) := by
  simp only [heisValid]
  rw [map_mul, hμ]
  have h : μ * c + μ * unitaryInvolution F 2 n c = 0 := by
    calc μ * c + μ * unitaryInvolution F 2 n c =
        μ * (c + unitaryInvolution F 2 n c) := by ring
      _ = 0 := by rw [hc, mul_zero]
  simpa [map_zero, mul_zero] using h

private theorem heisImage_fst_eq {g : H} {μ : F}
    (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ) {u v v' : F}
    (hv : heisValid n u v) (hv' : heisValid n u v') :
    (heisImage hFn hθk hg u v).1 = (heisImage hFn hθk hg u v').1 := by
  let C := MulAut.conj g
  set p := heisImage hFn hθk hg u v with hp
  set p' := heisImage hFn hθk hg u v' with hp'
  have hpv : heisValid n p.1 p.2 := by
    rw [hp]
    exact heisImage_valid hFn hθk hg hv
  have hp'v : heisValid n p'.1 p'.2 := by
    rw [hp']
    exact heisImage_valid hFn hθk hg hv'
  have hpe : C (θ (heis₃ u v)) = θ (heis₃ p.1 p.2) := by
    rw [hp]
    simpa only [C, MulAut.conj_apply] using conj_heis_eq_heisImage hFn hθk hg hv
  have hp'e : C (θ (heis₃ u v')) = θ (heis₃ p'.1 p'.2) := by
    rw [hp']
    simpa only [C, MulAut.conj_apply] using conj_heis_eq_heisImage hFn hθk hg hv'
  have htrace : (v - v') + unitaryInvolution F 2 n (v - v') = 0 :=
    trace_sub hv hv'
  have hleft : C (θ (heis₃ u v * (heis₃ u v')⁻¹)) = θ (heis₃ 0 (μ * (v - v'))) := by
    rw [heis_mul_inv hFn hv hv']
    simpa only [C, MulAut.conj_apply] using conj_heis_zero hFn hμ hμfix htrace
  have hright : C (θ (heis₃ u v * (heis₃ u v')⁻¹)) =
      θ (heis₃ (p.1 + -p'.1)
        (p.2 + (-p'.2 - p'.1 * unitaryInvolution F 2 n p'.1) -
          p.1 * unitaryInvolution F 2 n (-p'.1))) := by
    rw [map_mul θ, map_inv θ, map_mul C, map_inv C, hpe, hp'e, ← map_inv θ, ← map_mul θ]
    congr 1
    rw [suHeis_inv (unitaryInvolution_involutive hFn) not_even_three hp'v,
      suHeis_mul (unitaryInvolution_involutive hFn) not_even_three hpv
        (Pres.heis_neg_valid (unitaryInvolution_involutive hFn) hp'v)]
  have heq : θ (heis₃ 0 (μ * (v - v'))) =
      θ (heis₃ (p.1 + -p'.1)
        (p.2 + (-p'.2 - p'.1 * unitaryInvolution F 2 n p'.1) -
          p.1 * unitaryInvolution F 2 n (-p'.1))) := hleft.symm.trans hright
  have hv0 : heisValid n 0 (μ * (v - v')) := heisValid_zero_mul hμfix htrace
  have hvR : heisValid n (p.1 + -p'.1)
      (p.2 + (-p'.2 - p'.1 * unitaryInvolution F 2 n p'.1) -
        p.1 * unitaryInvolution F 2 n (-p'.1)) :=
    Pres.heis_add_valid (unitaryInvolution_involutive hFn) hpv
      (Pres.heis_neg_valid (unitaryInvolution_involutive hFn) hp'v)
  have h0 : p.1 - p'.1 = 0 := by
    simpa [sub_eq_add_neg] using (heis_eq_of_map_eq hFn hθk hv0 hvR heq).1.symm
  exact sub_eq_zero.mp h0

private theorem heisImage_snd_sub_eq {g : H} {μ : F}
    (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ) {u v v' : F}
    (hv : heisValid n u v) (hv' : heisValid n u v') :
    (heisImage hFn hθk hg u v).2 - μ * v =
      (heisImage hFn hθk hg u v').2 - μ * v' := by
  let C := MulAut.conj g
  set p := heisImage hFn hθk hg u v with hp
  set p' := heisImage hFn hθk hg u v' with hp'
  have hpv : heisValid n p.1 p.2 := by
    rw [hp]
    exact heisImage_valid hFn hθk hg hv
  have hp'v : heisValid n p'.1 p'.2 := by
    rw [hp']
    exact heisImage_valid hFn hθk hg hv'
  have hpe : C (θ (heis₃ u v)) = θ (heis₃ p.1 p.2) := by
    rw [hp]
    simpa only [C, MulAut.conj_apply] using conj_heis_eq_heisImage hFn hθk hg hv
  have hp'e : C (θ (heis₃ u v')) = θ (heis₃ p'.1 p'.2) := by
    rw [hp']
    simpa only [C, MulAut.conj_apply] using conj_heis_eq_heisImage hFn hθk hg hv'
  have htrace : (v - v') + unitaryInvolution F 2 n (v - v') = 0 :=
    trace_sub hv hv'
  have hleft : C (θ (heis₃ u v * (heis₃ u v')⁻¹)) = θ (heis₃ 0 (μ * (v - v'))) := by
    rw [heis_mul_inv hFn hv hv']
    simpa only [C, MulAut.conj_apply] using conj_heis_zero hFn hμ hμfix htrace
  have hright : C (θ (heis₃ u v * (heis₃ u v')⁻¹)) =
      θ (heis₃ (p.1 + -p'.1)
        (p.2 + (-p'.2 - p'.1 * unitaryInvolution F 2 n p'.1) -
          p.1 * unitaryInvolution F 2 n (-p'.1))) := by
    rw [map_mul θ, map_inv θ, map_mul C, map_inv C, hpe, hp'e, ← map_inv θ, ← map_mul θ]
    congr 1
    rw [suHeis_inv (unitaryInvolution_involutive hFn) not_even_three hp'v,
      suHeis_mul (unitaryInvolution_involutive hFn) not_even_three hpv
        (Pres.heis_neg_valid (unitaryInvolution_involutive hFn) hp'v)]
  have heq : θ (heis₃ 0 (μ * (v - v'))) =
      θ (heis₃ (p.1 + -p'.1)
        (p.2 + (-p'.2 - p'.1 * unitaryInvolution F 2 n p'.1) -
          p.1 * unitaryInvolution F 2 n (-p'.1))) := hleft.symm.trans hright
  have hv0 : heisValid n 0 (μ * (v - v')) := heisValid_zero_mul hμfix htrace
  have hvR : heisValid n (p.1 + -p'.1)
      (p.2 + (-p'.2 - p'.1 * unitaryInvolution F 2 n p'.1) -
        p.1 * unitaryInvolution F 2 n (-p'.1)) :=
    Pres.heis_add_valid (unitaryInvolution_involutive hFn) hpv
      (Pres.heis_neg_valid (unitaryInvolution_involutive hFn) hp'v)
  have hres := heis_eq_of_map_eq hFn hθk hv0 hvR heq
  have hfirst : p.1 = p'.1 := by
    have h0 : p.1 - p'.1 = 0 := by
      simpa [sub_eq_add_neg] using hres.1.symm
    exact sub_eq_zero.mp h0
  have hsecond : μ * (v - v') =
      p.2 + (-p'.2 - p'.1 * unitaryInvolution F 2 n p'.1) -
        p.1 * unitaryInvolution F 2 n (-p'.1) := hres.2
  rw [hfirst] at hsecond
  have hsecond' : μ * (v - v') = p.2 - p'.2 := by
    rw [hsecond, map_neg]
    ring
  rw [mul_sub] at hsecond'
  linear_combination -hsecond'


private noncomputable def heisPartner (u : F) : F :=
  Classical.choose (exists_add_unitaryInvolution_eq (p := 2) (f := n) hFn
    (a := unitaryInvolution F 2 n u * u) (by
      rw [map_mul, unitaryInvolution_involutive hFn, mul_comm]))

private theorem heisPartner_add_involution (u : F) :
    heisPartner hFn u + unitaryInvolution F 2 n (heisPartner hFn u) =
      unitaryInvolution F 2 n u * u :=
  Classical.choose_spec (exists_add_unitaryInvolution_eq (p := 2) (f := n) hFn
    (a := unitaryInvolution F 2 n u * u) (by
      rw [map_mul, unitaryInvolution_involutive hFn, mul_comm]))

private theorem valid_heisPartner (u : F) : heisValid n u (heisPartner hFn u) := by
  simp only [heisValid]
  rw [heisPartner_add_involution]
  exact CharTwo.add_self_eq_zero _

private noncomputable def heisAutPair (hθk : Odd (Nat.card θ.ker)) {g : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (u : F) : F × F :=
  heisImage hFn hθk hg u (heisPartner hFn u)

private noncomputable def heisAutU (hθk : Odd (Nat.card θ.ker)) {g : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (u : F) : F :=
  (heisAutPair hFn hθk hg u).1

private noncomputable def heisAutV (hθk : Odd (Nat.card θ.ker)) {g : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (u : F) : F :=
  (heisAutPair hFn hθk hg u).2

private theorem heisImage_fst_eq_heisAutU {g : H} {μ : F}
    (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ) {u v : F} (hv : heisValid n u v) :
    (heisImage hFn hθk hg u v).1 = heisAutU hFn hθk hg u :=
  heisImage_fst_eq hFn hθk hg hμ hμfix hv (valid_heisPartner hFn u)

private theorem heisImage_snd_sub_eq_heisAutV {g : H} {μ : F}
    (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ) {u v : F} (hv : heisValid n u v) :
    (heisImage hFn hθk hg u v).2 - μ * v =
      heisAutV hFn hθk hg u - μ * heisPartner hFn u :=
  heisImage_snd_sub_eq hFn hθk hg hμ hμfix hv (valid_heisPartner hFn u)


private theorem heisImage_add (hθk : Odd (Nat.card θ.ker)) {g : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    {u v u' v' : F} (hv : heisValid n u v) (hv' : heisValid n u' v') :
    (heisImage hFn hθk hg (u + u')
        (v + v' - u * unitaryInvolution F 2 n u')).1 =
      (heisImage hFn hθk hg u v).1 + (heisImage hFn hθk hg u' v').1 ∧
    (heisImage hFn hθk hg (u + u')
        (v + v' - u * unitaryInvolution F 2 n u')).2 =
      (heisImage hFn hθk hg u v).2 + (heisImage hFn hθk hg u' v').2 -
        (heisImage hFn hθk hg u v).1 *
          unitaryInvolution F 2 n (heisImage hFn hθk hg u' v').1 := by
  let C := MulAut.conj g
  set p := heisImage hFn hθk hg u v with hp
  set p' := heisImage hFn hθk hg u' v' with hp'
  set q := heisImage hFn hθk hg (u + u')
    (v + v' - u * unitaryInvolution F 2 n u') with hq
  have hpv : heisValid n p.1 p.2 := by
    rw [hp]
    exact heisImage_valid hFn hθk hg hv
  have hp'v : heisValid n p'.1 p'.2 := by
    rw [hp']
    exact heisImage_valid hFn hθk hg hv'
  have hw : heisValid n (u + u') (v + v' - u * unitaryInvolution F 2 n u') :=
    Pres.heis_add_valid (unitaryInvolution_involutive hFn) hv hv'
  have hqv : heisValid n q.1 q.2 := by
    rw [hq]
    exact heisImage_valid hFn hθk hg hw
  have hpe : C (θ (heis₃ u v)) = θ (heis₃ p.1 p.2) := by
    rw [hp]
    simpa only [C, MulAut.conj_apply] using conj_heis_eq_heisImage hFn hθk hg hv
  have hp'e : C (θ (heis₃ u' v')) = θ (heis₃ p'.1 p'.2) := by
    rw [hp']
    simpa only [C, MulAut.conj_apply] using conj_heis_eq_heisImage hFn hθk hg hv'
  have hqe : C (θ (heis₃ (u + u')
      (v + v' - u * unitaryInvolution F 2 n u'))) = θ (heis₃ q.1 q.2) := by
    rw [hq]
    simpa only [C, MulAut.conj_apply] using conj_heis_eq_heisImage hFn hθk hg hw
  have hprod : C (θ (heis₃ (u + u')
      (v + v' - u * unitaryInvolution F 2 n u'))) =
      θ (heis₃ (p.1 + p'.1) (p.2 + p'.2 - p.1 *
        unitaryInvolution F 2 n p'.1)) := by
    rw [← suHeis_mul (unitaryInvolution_involutive hFn) not_even_three hv hv']
    rw [map_mul θ, map_mul C, hpe, hp'e, ← map_mul θ]
    congr 1
    rw [suHeis_mul (unitaryInvolution_involutive hFn) not_even_three hpv hp'v]
  have heq : θ (heis₃ q.1 q.2) =
      θ (heis₃ (p.1 + p'.1) (p.2 + p'.2 - p.1 *
        unitaryInvolution F 2 n p'.1)) := hqe.symm.trans hprod
  have hres := heis_eq_of_map_eq hFn hθk hqv
    (Pres.heis_add_valid (unitaryInvolution_involutive hFn) hpv hp'v) heq
  exact ⟨hres.1, hres.2⟩

private theorem heisAutU_add {g : H} {μ : F} (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ) (u u' : F) :
    heisAutU hFn hθk hg (u + u') =
      heisAutU hFn hθk hg u + heisAutU hFn hθk hg u' := by
  have hv : heisValid n u (heisPartner hFn u) := valid_heisPartner hFn u
  have hv' : heisValid n u' (heisPartner hFn u') := valid_heisPartner hFn u'
  have h := (heisImage_add hFn hθk hg hv hv').1
  rw [heisImage_fst_eq_heisAutU hFn hθk hg hμ hμfix
      (Pres.heis_add_valid (unitaryInvolution_involutive hFn) hv hv'),
    heisImage_fst_eq_heisAutU hFn hθk hg hμ hμfix hv,
    heisImage_fst_eq_heisAutU hFn hθk hg hμ hμfix hv'] at h
  exact h


private theorem heisValid_mul_left {ρ u v : F}
    (hρ : unitaryInvolution F 2 n ρ * ρ = 1) (hv : heisValid n u v) :
    heisValid n (ρ * u) v := by
  have hN : unitaryInvolution F 2 n (ρ * u) * (ρ * u) =
      unitaryInvolution F 2 n u * u := by
    rw [map_mul]
    calc (unitaryInvolution F 2 n ρ * unitaryInvolution F 2 n u) * (ρ * u)
        = (unitaryInvolution F 2 n ρ * ρ) * (unitaryInvolution F 2 n u * u) := by ring
      _ = unitaryInvolution F 2 n u * u := by rw [hρ, one_mul]
  simp only [heisValid] at hv ⊢
  rw [hN]
  exact hv

private theorem heisAutU_norm {g : H} {μ : F} (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ) (u : F) :
    unitaryInvolution F 2 n (heisAutU hFn hθk hg u) * heisAutU hFn hθk hg u =
      μ * (unitaryInvolution F 2 n u * u) := by
  let C := MulAut.conj g
  have hu : heisValid n u (heisPartner hFn u) := valid_heisPartner hFn u
  have hpv : heisValid n (heisImage hFn hθk hg u (heisPartner hFn u)).1
      (heisImage hFn hθk hg u (heisPartner hFn u)).2 :=
    heisImage_valid hFn hθk hg hu
  have hNtrace : (unitaryInvolution F 2 n u * u) +
      unitaryInvolution F 2 n (unitaryInvolution F 2 n u * u) = 0 := by
    rw [map_mul, unitaryInvolution_involutive hFn, mul_comm u (unitaryInvolution F 2 n u)]
    exact CharTwo.add_self_eq_zero _
  have hpe : C (θ (heis₃ u (heisPartner hFn u))) =
      θ (heis₃ (heisImage hFn hθk hg u (heisPartner hFn u)).1
        (heisImage hFn hθk hg u (heisPartner hFn u)).2) := by
    simpa only [C, MulAut.conj_apply] using
      conj_heis_eq_heisImage hFn hθk hg hu
  have hleft : C (θ (heis₃ u (heisPartner hFn u) *
      heis₃ u (heisPartner hFn u))) =
      θ (heis₃ 0 (μ * (unitaryInvolution F 2 n u * u))) := by
    rw [heis_mul_self hFn hu]
    simpa only [C, MulAut.conj_apply] using conj_heis_zero hFn hμ hμfix hNtrace
  have hright : C (θ (heis₃ u (heisPartner hFn u) *
      heis₃ u (heisPartner hFn u))) =
      θ (heis₃ 0 (unitaryInvolution F 2 n
        (heisImage hFn hθk hg u (heisPartner hFn u)).1 *
        (heisImage hFn hθk hg u (heisPartner hFn u)).1)) := by
    rw [map_mul θ, map_mul C, hpe, ← map_mul θ]
    congr 1
    rw [heis_mul_self hFn hpv]
  have heq : θ (heis₃ 0 (μ * (unitaryInvolution F 2 n u * u))) =
      θ (heis₃ 0 (unitaryInvolution F 2 n
        (heisImage hFn hθk hg u (heisPartner hFn u)).1 *
        (heisImage hFn hθk hg u (heisPartner hFn u)).1)) :=
    hleft.symm.trans hright
  have h1 : heisValid n 0 (μ * (unitaryInvolution F 2 n u * u)) :=
    heisValid_zero_mul hμfix hNtrace
  have hNptrace : (unitaryInvolution F 2 n
      (heisImage hFn hθk hg u (heisPartner hFn u)).1 *
      (heisImage hFn hθk hg u (heisPartner hFn u)).1) +
      unitaryInvolution F 2 n (unitaryInvolution F 2 n
        (heisImage hFn hθk hg u (heisPartner hFn u)).1 *
        (heisImage hFn hθk hg u (heisPartner hFn u)).1) = 0 := by
    rw [map_mul, unitaryInvolution_involutive hFn,
      mul_comm (heisImage hFn hθk hg u (heisPartner hFn u)).1
        (unitaryInvolution F 2 n (heisImage hFn hθk hg u (heisPartner hFn u)).1)]
    exact CharTwo.add_self_eq_zero _
  have h2 : heisValid n 0 (unitaryInvolution F 2 n
      (heisImage hFn hθk hg u (heisPartner hFn u)).1 *
      (heisImage hFn hθk hg u (heisPartner hFn u)).1) :=
    heisValid_zero_of_trace hNptrace
  have hres := (heis_eq_of_map_eq hFn hθk h1 h2 heq).2
  rw [heisImage_fst_eq_heisAutU hFn hθk hg hμ hμfix hu] at hres
  exact hres.symm


private theorem heisAutU_mul_norm_one {g t : H} {μ ρ : F}
    (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ)
    (hρ : unitaryInvolution F 2 n ρ * ρ = 1)
    (ht : ∀ u v : F, heisValid n u v →
      t * θ (heis₃ u v) * t⁻¹ = θ (heis₃ (ρ * u) v))
    (hgt : Commute g t) (u : F) :
    heisAutU hFn hθk hg (ρ * u) = ρ * heisAutU hFn hθk hg u := by
  let C := MulAut.conj g
  let T := MulAut.conj t
  have hu : heisValid n u (heisPartner hFn u) := valid_heisPartner hFn u
  have hρu : heisValid n (ρ * u) (heisPartner hFn u) := heisValid_mul_left hρ hu
  set p := heisImage hFn hθk hg u (heisPartner hFn u) with hp
  set q := heisImage hFn hθk hg (ρ * u) (heisPartner hFn u) with hq
  have hpv : heisValid n p.1 p.2 := by
    rw [hp]
    exact heisImage_valid hFn hθk hg hu
  have hqv : heisValid n q.1 q.2 := by
    rw [hq]
    exact heisImage_valid hFn hθk hg hρu
  have hgte : g * t = t * g := hgt.eq
  have hgtinv : t⁻¹ * g⁻¹ = g⁻¹ * t⁻¹ := by
    rw [← mul_inv_rev, hgte, mul_inv_rev]
  have hCT : ∀ x : H, C (T x) = T (C x) := by
    intro x
    simp only [C, T, MulAut.conj_apply]
    calc g * (t * x * t⁻¹) * g⁻¹
        = g * t * x * t⁻¹ * g⁻¹ := by group
      _ = t * g * x * t⁻¹ * g⁻¹ := by rw [hgte]
      _ = t * g * x * (t⁻¹ * g⁻¹) := by group
      _ = t * g * x * (g⁻¹ * t⁻¹) := by rw [hgtinv]
      _ = t * g * x * g⁻¹ * t⁻¹ := by group
      _ = t * (g * x * g⁻¹) * t⁻¹ := by group
  have hT : T (θ (heis₃ u (heisPartner hFn u))) =
      θ (heis₃ (ρ * u) (heisPartner hFn u)) := by
    simpa only [T, MulAut.conj_apply] using ht u (heisPartner hFn u) hu
  have hTp : T (θ (heis₃ p.1 p.2)) = θ (heis₃ (ρ * p.1) p.2) := by
    simpa only [T, MulAut.conj_apply] using ht p.1 p.2 hpv
  have hpe : C (θ (heis₃ u (heisPartner hFn u))) = θ (heis₃ p.1 p.2) := by
    rw [hp]
    simpa only [C, MulAut.conj_apply] using
      conj_heis_eq_heisImage hFn hθk hg hu
  have hqe : C (θ (heis₃ (ρ * u) (heisPartner hFn u))) = θ (heis₃ q.1 q.2) := by
    rw [hq]
    simpa only [C, MulAut.conj_apply] using
      conj_heis_eq_heisImage hFn hθk hg hρu
  have hL : C (T (θ (heis₃ u (heisPartner hFn u)))) = θ (heis₃ q.1 q.2) := by
    rw [hT, hqe]
  have hR : T (C (θ (heis₃ u (heisPartner hFn u)))) =
      θ (heis₃ (ρ * p.1) p.2) := by
    rw [hpe, hTp]
  have heq : θ (heis₃ q.1 q.2) = θ (heis₃ (ρ * p.1) p.2) := by
    rw [← hL, hCT, hR]
  have hres := (heis_eq_of_map_eq hFn hθk hqv (heisValid_mul_left hρ hpv) heq).1
  rw [heisImage_fst_eq_heisAutU hFn hθk hg hμ hμfix hρu,
    heisImage_fst_eq_heisAutU hFn hθk hg hμ hμfix hu] at hres
  exact hres


private noncomputable def heisLambda (hθk : Odd (Nat.card θ.ker)) {g : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (μ : F) (u : F) : F :=
  heisAutV hFn hθk hg u - μ * heisPartner hFn u

private theorem heisLambda_add {g : H} {μ κ : F} (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ)
    (hκ : ∀ u : F, heisAutU hFn hθk hg u = κ * u)
    (hNκ : unitaryInvolution F 2 n κ * κ = μ) (u u' : F) :
    heisLambda hFn hθk hg μ (u + u') =
      heisLambda hFn hθk hg μ u + heisLambda hFn hθk hg μ u' := by
  have hu : heisValid n u (heisPartner hFn u) := valid_heisPartner hFn u
  have hu' : heisValid n u' (heisPartner hFn u') := valid_heisPartner hFn u'
  have hw : heisValid n (u + u') (heisPartner hFn u + heisPartner hFn u' -
      u * unitaryInvolution F 2 n u') :=
    Pres.heis_add_valid (unitaryInvolution_involutive hFn) hu hu'
  have h := (heisImage_add hFn hθk hg hu hu').2
  have h1 : (heisImage hFn hθk hg u (heisPartner hFn u)).1 = κ * u := by
    rw [heisImage_fst_eq_heisAutU hFn hθk hg hμ hμfix hu, hκ u]
  have h1' : (heisImage hFn hθk hg u' (heisPartner hFn u')).1 = κ * u' := by
    rw [heisImage_fst_eq_heisAutU hFn hθk hg hμ hμfix hu', hκ u']
  rw [h1, h1'] at h
  have hN : (κ * u) * unitaryInvolution F 2 n (κ * u') =
      μ * (u * unitaryInvolution F 2 n u') := by
    rw [map_mul]
    calc κ * u * (unitaryInvolution F 2 n κ * unitaryInvolution F 2 n u')
        = (κ * unitaryInvolution F 2 n κ) * (u * unitaryInvolution F 2 n u') := by ring
      _ = μ * (u * unitaryInvolution F 2 n u') := by
        rw [mul_comm κ (unitaryInvolution F 2 n κ), hNκ]
  rw [hN] at h
  have hq := heisImage_snd_sub_eq_heisAutV hFn hθk hg hμ hμfix hw
  have huV := heisImage_snd_sub_eq_heisAutV hFn hθk hg hμ hμfix hu
  have hu'V := heisImage_snd_sub_eq_heisAutV hFn hθk hg hμ hμfix hu'
  simp only [heisLambda]
  rw [← hq, h]
  rw [← huV, ← hu'V]
  ring


private theorem heisImage_snd_mul_norm_one {g t : H} {ρ : F}
    (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hρ : unitaryInvolution F 2 n ρ * ρ = 1)
    (ht : ∀ u v : F, heisValid n u v →
      t * θ (heis₃ u v) * t⁻¹ = θ (heis₃ (ρ * u) v))
    (hgt : Commute g t) (u : F) :
    (heisImage hFn hθk hg (ρ * u) (heisPartner hFn u)).2 =
      (heisImage hFn hθk hg u (heisPartner hFn u)).2 := by
  let C := MulAut.conj g
  let T := MulAut.conj t
  have hu : heisValid n u (heisPartner hFn u) := valid_heisPartner hFn u
  have hρu : heisValid n (ρ * u) (heisPartner hFn u) := heisValid_mul_left hρ hu
  set p := heisImage hFn hθk hg u (heisPartner hFn u) with hp
  set q := heisImage hFn hθk hg (ρ * u) (heisPartner hFn u) with hq
  have hpv : heisValid n p.1 p.2 := by
    rw [hp]
    exact heisImage_valid hFn hθk hg hu
  have hqv : heisValid n q.1 q.2 := by
    rw [hq]
    exact heisImage_valid hFn hθk hg hρu
  have hgte : g * t = t * g := hgt.eq
  have hgtinv : t⁻¹ * g⁻¹ = g⁻¹ * t⁻¹ := by
    rw [← mul_inv_rev, hgte, mul_inv_rev]
  have hCT : ∀ x : H, C (T x) = T (C x) := by
    intro x
    simp only [C, T, MulAut.conj_apply]
    calc g * (t * x * t⁻¹) * g⁻¹
        = g * t * x * t⁻¹ * g⁻¹ := by group
      _ = t * g * x * t⁻¹ * g⁻¹ := by rw [hgte]
      _ = t * g * x * (t⁻¹ * g⁻¹) := by group
      _ = t * g * x * (g⁻¹ * t⁻¹) := by rw [hgtinv]
      _ = t * g * x * g⁻¹ * t⁻¹ := by group
      _ = t * (g * x * g⁻¹) * t⁻¹ := by group
  have hT : T (θ (heis₃ u (heisPartner hFn u))) =
      θ (heis₃ (ρ * u) (heisPartner hFn u)) := by
    simpa only [T, MulAut.conj_apply] using ht u (heisPartner hFn u) hu
  have hTp : T (θ (heis₃ p.1 p.2)) = θ (heis₃ (ρ * p.1) p.2) := by
    simpa only [T, MulAut.conj_apply] using ht p.1 p.2 hpv
  have hpe : C (θ (heis₃ u (heisPartner hFn u))) = θ (heis₃ p.1 p.2) := by
    rw [hp]
    simpa only [C, MulAut.conj_apply] using
      conj_heis_eq_heisImage hFn hθk hg hu
  have hqe : C (θ (heis₃ (ρ * u) (heisPartner hFn u))) = θ (heis₃ q.1 q.2) := by
    rw [hq]
    simpa only [C, MulAut.conj_apply] using
      conj_heis_eq_heisImage hFn hθk hg hρu
  have hL : C (T (θ (heis₃ u (heisPartner hFn u)))) = θ (heis₃ q.1 q.2) := by
    rw [hT, hqe]
  have hR : T (C (θ (heis₃ u (heisPartner hFn u)))) =
      θ (heis₃ (ρ * p.1) p.2) := by
    rw [hpe, hTp]
  have heq : θ (heis₃ q.1 q.2) = θ (heis₃ (ρ * p.1) p.2) := by
    rw [← hL, hCT, hR]
  exact (heis_eq_of_map_eq hFn hθk hqv (heisValid_mul_left hρ hpv) heq).2

private theorem heisLambda_mul_norm_one {g t : H} {μ ρ : F}
    (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ)
    (hρ : unitaryInvolution F 2 n ρ * ρ = 1)
    (ht : ∀ u v : F, heisValid n u v →
      t * θ (heis₃ u v) * t⁻¹ = θ (heis₃ (ρ * u) v))
    (hgt : Commute g t) (u : F) :
    heisLambda hFn hθk hg μ (ρ * u) = heisLambda hFn hθk hg μ u := by
  have hu : heisValid n u (heisPartner hFn u) := valid_heisPartner hFn u
  have hρu : heisValid n (ρ * u) (heisPartner hFn u) := heisValid_mul_left hρ hu
  have h2 := heisImage_snd_mul_norm_one hFn hθk hg hρ ht hgt u
  have hq := heisImage_snd_sub_eq_heisAutV hFn hθk hg hμ hμfix hρu
  have huV := heisImage_snd_sub_eq_heisAutV hFn hθk hg hμ hμfix hu
  simp only [heisLambda]
  rw [← hq, ← huV, h2]

private theorem heisLambda_eq_zero {g t : H} {μ ρ κ : F}
    (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ)
    (hρ : unitaryInvolution F 2 n ρ * ρ = 1) (hρ1 : ρ ≠ 1)
    (ht : ∀ u v : F, heisValid n u v →
      t * θ (heis₃ u v) * t⁻¹ = θ (heis₃ (ρ * u) v))
    (hgt : Commute g t)
    (hκ : ∀ u : F, heisAutU hFn hθk hg u = κ * u)
    (hNκ : unitaryInvolution F 2 n κ * κ = μ) :
    ∀ x : F, heisLambda hFn hθk hg μ x = 0 := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hzero : ∀ u : F, heisLambda hFn hθk hg μ ((ρ - 1) * u) = 0 := by
    intro u
    have hmul := heisLambda_mul_norm_one hFn hθk hg hμ hμfix hρ ht hgt u
    have hadd := heisLambda_add hFn hθk hg hμ hμfix hκ hNκ u ((ρ - 1) * u)
    have hρu : ρ * u = u + (ρ - 1) * u := by ring
    rw [hρu] at hmul
    rw [hadd] at hmul
    have h' : heisLambda hFn hθk hg μ u + heisLambda hFn hθk hg μ ((ρ - 1) * u) =
        heisLambda hFn hθk hg μ u + 0 := by simpa using hmul
    exact add_left_cancel h'
  intro x
  have hx : (ρ - 1) * (x * (ρ - 1)⁻¹) = x := by
    rw [← mul_assoc, mul_comm (ρ - 1) x, mul_assoc, mul_inv_cancel₀ hρ1', mul_one]
  have := hzero (x * (ρ - 1)⁻¹)
  rwa [hx] at this


private theorem exists_tw_heisAutU {g : H} {μ : F} (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ) :
    ∃ e : Bool, ∀ u : F, heisAutU hFn hθk hg u =
      heisAutU hFn hθk hg 1 * RelBuild.tw (unitaryInvolution F 2 n) e u := by
  obtain ⟨e, he⟩ := RelBuild.exists_tw_of_add_of_norm
    (σ := unitaryInvolution F 2 n) (φ := heisAutU hFn hθk hg)
    (fun s t => heisAutU_add hFn hθk hg hμ hμfix s t)
    (m := μ) (fun s => heisAutU_norm hFn hθk hg hμ hμfix s)
  exact ⟨e, he⟩

private theorem exists_heisAutU_eq_mul {g t : H} {μ ρ : F}
    (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ)
    (hρ : unitaryInvolution F 2 n ρ * ρ = 1) (hρ1 : ρ ≠ 1)
    (ht : ∀ u v : F, heisValid n u v →
      t * θ (heis₃ u v) * t⁻¹ = θ (heis₃ (ρ * u) v))
    (hgt : Commute g t) :
    ∃ κ : F, κ ≠ 0 ∧ (∀ u : F, heisAutU hFn hθk hg u = κ * u) ∧
      unitaryInvolution F 2 n κ * κ = μ := by
  have hμne : μ ≠ 0 := map_suLong_ne_zero hFn hθk hμ
  obtain ⟨e, he⟩ := exists_tw_heisAutU hFn hθk hg hμ hμfix
  let κ := heisAutU hFn hθk hg 1
  have hκnorm : unitaryInvolution F 2 n κ * κ = μ := by
    simpa [κ] using heisAutU_norm hFn hθk hg hμ hμfix 1
  have hκne : κ ≠ 0 := by
    intro h0
    have h := hκnorm
    rw [h0, map_zero, zero_mul] at h
    exact hμne h.symm
  cases e with
  | false =>
    refine ⟨κ, hκne, ?_, hκnorm⟩
    intro u
    rw [he u, RelBuild.tw_false]
  | true =>
    exfalso
    have hmul := heisAutU_mul_norm_one hFn hθk hg hμ hμfix hρ ht hgt 1
    rw [mul_one] at hmul
    have hσρ : unitaryInvolution F 2 n ρ = ρ := by
      have h := hmul
      rw [he ρ, he 1] at h
      simp only [RelBuild.tw_true, map_one, mul_one] at h
      rw [mul_comm ρ κ] at h
      exact mul_left_cancel₀ hκne h
    have hsq : ρ * ρ = 1 := by
      simpa [hσρ] using hρ
    rcases sq_eq_one_iff.mp (by simpa [pow_two] using hsq) with h | h
    · exact hρ1 h
    · rw [h, CharTwo.neg_eq] at hρ1
      exact hρ1 rfl

private theorem heisAut_action {g : H} {μ κ : F} (hθk : Odd (Nat.card θ.ker))
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    (hμfix : unitaryInvolution F 2 n μ = μ)
    (hκ : ∀ u : F, heisAutU hFn hθk hg u = κ * u)
    (hlam : ∀ x : F, heisLambda hFn hθk hg μ x = 0)
    {u v : F} (hv : heisValid n u v) :
    g * θ (heis₃ u v) * g⁻¹ = θ (heis₃ (κ * u) (μ * v)) := by
  have hp := conj_heis_eq_heisImage hFn hθk hg hv
  have h1 : (heisImage hFn hθk hg u v).1 = κ * u := by
    rw [heisImage_fst_eq_heisAutU hFn hθk hg hμ hμfix hv, hκ u]
  have h2 : (heisImage hFn hθk hg u v).2 = μ * v := by
    have hs := heisImage_snd_sub_eq_heisAutV hFn hθk hg hμ hμfix hv
    have hl := hlam u
    simp only [heisLambda] at hl
    rw [hl] at hs
    exact sub_eq_zero.mp hs
  rw [h1, h2] at hp
  exact hp

end Image

theorem exists_conj_map_suHeis_eq_of_commute {H : Type*} [Group H]
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθk : Odd (Nat.card θ.ker)) {g t : H}
    (hg : ∀ x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn),
      g * θ x * g⁻¹ ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ)
    {μ : F} (hμ : ∀ c : F, unitaryInvolution F 2 n c = c →
      g * θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) * g⁻¹ =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) (μ * c)))
    {ρ : F} (hρ : ρ ≠ 1) (hρσ : unitaryInvolution F 2 n ρ * ρ = 1)
    (ht : ∀ u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      t * θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v) * t⁻¹ =
        θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) (ρ * u) v))
    (hgt : Commute g t) :
    ∃ κ : F, unitaryInvolution F 2 n κ * κ = μ ∧
      ∀ u v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        g * θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v) * g⁻¹ =
          θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) (κ * u) (μ * v)) := by
  have hμfix := map_suLong_fixed hFn hθk hμ
  obtain ⟨κ, -, hκ, hκnorm⟩ :=
    exists_heisAutU_eq_mul hFn hθk hg hμ hμfix hρσ hρ ht hgt
  refine ⟨κ, hκnorm, ?_⟩
  intro u v hv
  exact heisAut_action hFn hθk hg hμ hμfix hκ
    (heisLambda_eq_zero hFn hθk hg hμ hμfix hρσ hρ ht hgt hκ hκnorm) hv
end

end CFSG.Timmesfeld.Transvection
