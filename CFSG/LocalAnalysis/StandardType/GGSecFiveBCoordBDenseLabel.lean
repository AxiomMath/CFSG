module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRes
public import Certificates.Certificate13657
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBQTwoLinDense
public import CFSG.LocalAnalysis.StandardType.GGSecFivePermNbrLabelOfJ
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseCoords
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGRowKFrame
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import Certificates.Certificate12621

public section

namespace CFSG.StandardType

open CFSG.Assembly
open Multiplicative

private theorem false_of_dvd_two_pow_sub_and_add {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1 : p ∣ 2 ^ f - 1) (h2 : p ∣ 2 ^ f + 1) : False := by
  have hdvd : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h2 h1
  have hpow : 1 ≤ 2 ^ f := Nat.one_le_pow f 2 (by norm_num)
  have h2eq : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
  rw [h2eq] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)

private theorem GGSecFiveBCoordBLabel.n_eq_one_of_tag_A {n p : ℕ} {lab : LargeEvenLabel}
    (h : GGSecFiveBCoordBLabel n p lab) (ht : lab.tag = .A) : lab.n = 1 := by
  obtain ⟨t, r, f⟩ := lab
  simp only at ht
  subst ht
  simp only [GGSecFiveBCoordBLabel] at h
  rcases h with ⟨hB, -, -⟩ | ⟨hD, -, -⟩ | ⟨hD, -, -, -, -⟩ | ⟨-, -, h1, -⟩
  · rcases hB with hB | hB <;> exact absurd hB (by decide)
  · exact absurd hD (by decide)
  · exact absurd hD (by decide)
  · exact h1

private theorem GGSecFiveBCoordBLabel.n_eq_of_labelIso {n p : ℕ} (hn : 4 ≤ n)
    {lab lab' : LargeEvenLabel} (h : GGSecFiveBCoordBLabel n p lab)
    (hiso : GGLabelIso lab lab') : lab'.n = lab.n := by
  obtain ⟨t, r, f⟩ := lab
  obtain ⟨t', r', f'⟩ := lab'
  simp only [GGLabelIso] at hiso
  simp only [GGSecFiveBCoordBLabel] at h
  rcases hiso with h | h | h | h | h | h | h | h
  · exact (congrArg LargeEvenLabel.n h).symm
  · exact h.2.2.2.symm
  · rw [h.2]
  · rw [h.2]
  · rw [h.2]
  · rw [h.2]
  · obtain ⟨h1, -⟩ := h
    exfalso
    have h1_tag : t = .twD := congrArg LargeEvenLabel.tag h1
    have h1_rank : r = 2 := congrArg LargeEvenLabel.rank h1
    subst h1_tag
    subst h1_rank
    rcases h with ⟨hB, -, -⟩ | ⟨-, hr, -⟩ | ⟨hD, -, -, -, -⟩ | ⟨hA, -⟩
    · rcases hB with hB | hB <;> exact absurd hB (by decide)
    · omega
    · exact absurd hD (by decide)
    · exact absurd hA (by decide)
  · obtain ⟨-, h2⟩ := h
    exfalso
    have h2_tag : t = .A := congrArg LargeEvenLabel.tag h2
    have h2_rank : r = 1 := congrArg LargeEvenLabel.rank h2
    have h2_n : f = 2 * f' := congrArg LargeEvenLabel.n h2
    subst h2_tag
    subst h2_rank
    subst h2_n
    rcases h with ⟨hB, -, -⟩ | ⟨hD, -, -⟩ | ⟨hD, -, -, -, -⟩ | ⟨-, -, h1, -⟩
    · rcases hB with hB | hB <;> exact absurd hB (by decide)
    · exact absurd hD (by decide)
    · exact absurd hD (by decide)
    · omega

private theorem GGSecFiveBCoordBLabel.eq_of_labelIso {n p : ℕ} (hn : 4 ≤ n)
    {lab lab' : LargeEvenLabel} (h' : GGSecFiveBCoordBLabel n p lab')
    (hiso : GGLabelIso lab lab') (ht' : lab'.tag = .A) : lab = lab' := by
  obtain ⟨t, r, f⟩ := lab
  obtain ⟨t', r', f'⟩ := lab'
  have ht'A : t' = .A := ht'
  subst ht'A
  simp only [GGSecFiveBCoordBLabel] at h'
  have hr' : r' = 2 * n - 3 ∨ r' = 2 * n - 2 := by
    rcases h' with h' | h' | h' | h'
    · exact absurd h'.1 (by decide)
    · exact absurd h'.1 (by decide)
    · exact absurd h'.1 (by decide)
    · exact h'.2.1
  simp only [GGLabelIso] at hiso
  rcases hiso with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact h1
  · exact absurd h2.2.1 (by decide)
  · obtain ⟨-, h3⟩ := h3
    have hr3 : r' = 3 := congrArg LargeEvenLabel.rank h3
    omega
  · exact absurd (show LargeEvenLieTag.A = .D from congrArg LargeEvenLabel.tag h4.2)
      (by decide)
  · exact absurd (show LargeEvenLieTag.A = .twA from congrArg LargeEvenLabel.tag h5.2)
      (by decide)
  · exact absurd (show LargeEvenLieTag.A = .twD from congrArg LargeEvenLabel.tag h6.2)
      (by decide)
  · obtain ⟨-, h7⟩ := h7
    have hr1 : r' = 1 := congrArg LargeEvenLabel.rank h7
    omega
  · exact absurd (show LargeEvenLieTag.A = .twD from congrArg LargeEvenLabel.tag h8.1)
      (by decide)

private theorem exists_pow_mul_coord {G : Type} [Group G] {Bs : Subgroup G} {p n : ℕ}
    (hp : p.Prime) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n} {xb yb : ↥Bs}
    (hxne : (xb : G) ≠ 1) (hxoff : ∀ j, j ≠ i0 → eta xb j = 1)
    (hyconst : ∀ a b, eta yb a = eta yb b) (hc : eta yb i0 ≠ 1) :
    ∃ k : ℕ, (yb * xb ^ k) ≠ 1 ∧ eta (yb * xb ^ k) i0 = 1 ∧
      ∀ j, j ≠ i0 → eta (yb * xb ^ k) j = eta yb i0 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hx0ne : eta xb i0 ≠ 1 := by
    intro h0
    have h1 : eta xb = 1 := by
      funext j
      simp only [Pi.one_apply]
      by_cases hj : j = i0
      · rw [hj]
        exact h0
      · exact hxoff j hj
    have h2 : xb = 1 := eta.injective (by simpa using h1)
    exact hxne (by simpa using congrArg (fun z : ↥Bs => (z : G)) h2)
  have hu : toAdd (eta xb i0) ≠ 0 := by
    intro h0
    exact hx0ne (by simpa [h0] using (ofAdd_toAdd (eta xb i0)).symm)
  let k : ℕ := (-(toAdd (eta yb i0)) * (toAdd (eta xb i0))⁻¹).val
  have hk : (k : ZMod p) = -(toAdd (eta yb i0)) * (toAdd (eta xb i0))⁻¹ :=
    ZMod.natCast_zmod_val _
  have hpow : (eta xb i0) ^ k = (eta yb i0)⁻¹ := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_inv]
    rw [nsmul_eq_mul, hk, mul_assoc, inv_mul_cancel₀ hu, mul_one]
  have hzmap : eta (yb * xb ^ k) = eta yb * eta xb ^ k := by
    rw [map_mul, map_pow]
  have hoff : ∀ j, j ≠ i0 → eta (yb * xb ^ k) j = eta yb i0 := by
    intro j hj
    rw [hzmap, Pi.mul_apply, Pi.pow_apply, hxoff j hj, one_pow, mul_one, hyconst j i0]
  have hi0 : eta (yb * xb ^ k) i0 = 1 := by
    rw [hzmap, Pi.mul_apply, Pi.pow_apply, hpow]
    exact mul_inv_cancel _
  refine ⟨k, ?_, hi0, hoff⟩
  intro h1
  obtain ⟨j0, hj0, -⟩ := Fin.exists_ne_and_ne_of_two_lt i0 i0 (by omega)
  have h2 := hoff j0 hj0
  rw [h1, map_one, Pi.one_apply] at h2
  exact hc h2.symm

theorem ggSecFiveBCoordBDenseNbr_not_sparse {G : Type} [Group G] [Finite G]
    {p n : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs) (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n}
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    (hKδ : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    ¬ GGSecFiveBCoordSparse eta i0 D := by
  intro hsp
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  obtain ⟨hp, -, hxBs, -, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hxD : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hyD : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hxoff : ∀ j, j ≠ i0 → eta ⟨x, hxBs⟩ j = 1 :=
    fun j hj => CommonJ.eta_x_eq_one hcfg hB eta i0 hL ⟨x, hxBs⟩ rfl hj
  have hfixK := ggRC_automizer_fixes_y hyBs hnb.1.2.2.2.1
  have hfixK' : ∀ w ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom,
      w (eta ⟨y, hyBs⟩) = eta ⟨y, hyBs⟩ :=
    (forall_map_congr_fix_iff eta (ggAutomizer K Bs) ⟨y, hyBs⟩).mpr hfixK
  have hconst : ∀ a b, eta ⟨y, hyBs⟩ a = eta ⟨y, hyBs⟩ b := by
    rw [hKδ] at hfixK'
    exact (forall_aPermutationFull_fix_iff (n := n) (p := p) _).mp hfixK'
  have hc : eta ⟨y, hyBs⟩ i0 ≠ 1 := by
    intro h0
    have h1 : eta ⟨y, hyBs⟩ = 1 := by
      funext j
      simp only [Pi.one_apply]
      rw [hconst j i0, h0]
    have h2 : (⟨y, hyBs⟩ : ↥Bs) = 1 := eta.injective (by simpa using h1)
    exact hy1 (by simpa using congrArg (fun z : ↥Bs => (z : G)) h2)
  obtain ⟨k, hzk_ne, hzk_i0, hzk_off⟩ :=
    exists_pow_mul_coord hp hn eta hx1 hxoff hconst hc
  have hzD : ((⟨y, hyBs⟩ * ⟨x, hxBs⟩ ^ k : ↥Bs) : G) ∈ D := by
    have h1 : ((⟨y, hyBs⟩ * ⟨x, hxBs⟩ ^ k : ↥Bs) : G) = y * x ^ k := rfl
    rw [h1]
    exact D.mul_mem hyD (D.pow_mem hxD k)
  obtain ⟨i, hi0, hiz⟩ := hsp (⟨y, hyBs⟩ * ⟨x, hxBs⟩ ^ k) hzD hzk_ne hzk_i0
  obtain ⟨j, hj0, hji⟩ := Fin.exists_ne_and_ne_of_two_lt i0 i (by omega)
  have h1 := hiz j hj0 hji
  rw [hzk_off j hj0] at h1
  exact hc h1

private theorem denseLabelCore_eq_linear {G : Type} [Group G] {L : Subgroup G} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 2 ≤ f) {lab labJ : LargeEvenLabel}
    (hBC : GGSecFiveBCoordBLabel n p lab) (hln : lab.n = f)
    (hJ : GGSecFiveBCoordBJDenseLabelCore L n p lab labJ) (hdiv : p ∣ 2 ^ f - 1) :
    labJ = ⟨.A, n - 2, f⟩ := by
  rcases hJ with hJ | hJ
  · rcases hJ with ⟨-, hd, hJeq⟩ | ⟨-, hd, hJeq, -⟩ | ⟨htA, hJeq⟩
    · rw [hJeq, hln]
    · exact (false_of_dvd_two_pow_sub_and_add hp hp2 (hln.symm ▸ hdiv)
        (hln.symm ▸ hd)).elim
    · have h1 := GGSecFiveBCoordBLabel.n_eq_one_of_tag_A hBC htA
      omega
  · obtain ⟨-, -, hln1, -, -⟩ := hJ
    omega

private theorem denseLabelCore_eq_unitary {G : Type} [Group G] {L : Subgroup G} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {lab labJ : LargeEvenLabel} (htA : lab.tag ≠ .A)
    (hln : lab.n = f) (hJ : GGSecFiveBCoordBJDenseLabelCore L n p lab labJ)
    (hdiv : p ∣ 2 ^ f + 1) : labJ = ⟨.twA, n - 2, f⟩ := by
  rcases hJ with hJ | hJ
  · rcases hJ with ⟨-, hd, hJeq⟩ | ⟨-, hd, hJeq, -⟩ | ⟨htA', -⟩
    · exact (false_of_dvd_two_pow_sub_and_add hp hp2 (hln ▸ hd) hdiv).elim
    · rw [hJeq, hln]
    · exact absurd htA' htA
  · obtain ⟨-, rfl, hln1, hJeq, -⟩ := hJ
    rw [hJeq, ← hln, hln1]

private theorem denseLabelCore_eq_linear_qtwo {G : Type} [Group G] {L : Subgroup G} {n p : ℕ}
    {lab labJ : LargeEvenLabel} (ht : lab.tag = .A)
    (hJ : GGSecFiveBCoordBJDenseLabelCore L n p lab labJ) :
    labJ = ⟨.A, n - 2, 2⟩ := by
  rcases hJ with hJ | hJ
  · rcases hJ with ⟨hd, -, hEq⟩ | ⟨hd, -, hEq, -⟩ | ⟨-, hEq⟩
    · rcases hd with hB | hC | htwD
      · exact absurd (hB.symm.trans ht) (by decide)
      · exact absurd (hC.symm.trans ht) (by decide)
      · exact absurd (htwD.symm.trans ht) (by decide)
    · rcases hd with hB | hC | htwD | hD
      · exact absurd (hB.symm.trans ht) (by decide)
      · exact absurd (hC.symm.trans ht) (by decide)
      · exact absurd (htwD.symm.trans ht) (by decide)
      · exact absurd (hD.symm.trans ht) (by decide)
    · exact hEq
  · obtain ⟨hd, -, -, hEq, -⟩ := hJ
    rcases hd with hB | hC | hD
    · exact absurd (hB.symm.trans ht) (by decide)
    · exact absurd (hC.symm.trans ht) (by decide)
    · exact absurd (hD.symm.trans ht) (by decide)

private theorem largeEvenInLambda2_twA_one_iff {r : ℕ} :
    LargeEvenInLambda2 ⟨.twA, r, 1⟩ ↔ 3 ≤ r := by
  show 1 ≤ 1 ∧ 2 ≤ r ∧ (r = 2 → 2 ≤ 1) ↔ 3 ≤ r
  refine ⟨fun ⟨_, h2, h3⟩ => ?_, fun hr => ⟨le_rfl, by omega, fun h => by omega⟩⟩
  rcases Nat.lt_or_ge r 3 with h | h
  · exact absurd (h3 (by omega)) (by norm_num)
  · exact h

private theorem GGSecFiveBCoordBLabel.dvd_two_pow_one_add_one {n p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (h : GGSecFiveBCoordBLabel n p lab) (hln : lab.n = 1) :
    p ∣ 2 ^ 1 + 1 := by
  have h1 : ¬ p ∣ 2 ^ lab.n - 1 := fun hd =>
    hp.ne_one (Nat.dvd_one.mp (by simpa [hln] using hd))
  unfold GGSecFiveBCoordBLabel at h
  rcases h with ⟨-, -, hd | ⟨-, rfl⟩⟩ | ⟨-, -, hd | ⟨-, hd⟩⟩ | ⟨-, -, -, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact absurd hd h1
  · norm_num
  · exact absurd hd h1
  · rwa [hln] at hd
  · norm_num
  · norm_num

theorem GGSecFiveRouteCfg.qTwoOrth_denseNbr_J_label (hRig : GGLabelRigidInput) {G : Type}
    [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hB : B = Bs)
    (hn : 4 ≤ n) {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    (hAjoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) p Bs L)
    {K : Subgroup G} (hK : GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K) :
    5 ≤ n ∧ GGHasLabel ⟨.twA, n - 2, 1⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨eta', -, hAL', hAK'⟩ := GGSecFiveBCoordBDenseNbr.exists_coords hAjoin hAL hK
  have hnotSparse := ggSecFiveBCoordBDenseNbr_not_sparse hR hB hn eta' hAL' hK.1 hAK'
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ LargeEvenBeta 4 G)
  have hBC : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨h.1.1, h.2⟩) hLab
  obtain ⟨lab, hΛlab, hlabHas, _, _, _, _, _, hP⟩ := largeEvenMarking_exists_hasLabel
    (ggSecFiveBCoordBCommonJCoreInput_holds G p B Bs x L D J hR.1.1 hB n hn eta' i0 hAL' hBC)
  obtain ⟨hlabBC, hbranch⟩ := hP.1
  obtain ⟨lab', hΛlab', hlabHas', _, _, _, _, _, hP'⟩ := largeEvenMarking_exists_hasLabel hLab
  obtain ⟨-, hfn, ht'⟩ := hP'.1
  have hlabn : lab.n = 1 := (GGSecFiveBCoordBLabel.n_eq_of_labelIso hn hlabBC
    (hRig lab lab' _ hΛlab hΛlab' hlabHas hlabHas')).symm.trans hfn
  have htA : lab.tag ≠ .A := by
    intro htA
    have hEq := GGSecFiveBCoordBLabel.eq_of_labelIso hn hlabBC
      (hRig lab' lab _ hΛlab' hΛlab hlabHas' hlabHas) htA
    rw [hEq, htA] at ht'
    rcases ht' with h | h <;> exact absurd h (by decide)
  have hdense : LargeEvenMarking J
      (fun labJ _ _ _ _ _ => GGSecFiveBCoordBJDenseLabelCore L n p lab labJ) := by
    rcases hbranch with h | h
    · exact h.2
    · exact absurd h.1 hnotSparse
  obtain ⟨labJ, hΛlabJ, hlabJHas, _, _, _, _, _, hlabJ⟩ := largeEvenMarking_exists_hasLabel hdense
  obtain rfl : labJ = ⟨.twA, n - 2, 1⟩ := denseLabelCore_eq_unitary hp hp2 htA hlabn hlabJ
    (GGSecFiveBCoordBLabel.dvd_two_pow_one_add_one hp hlabBC hlabn)
  have h3 := largeEvenInLambda2_twA_one_iff.mp hΛlabJ
  exact ⟨by omega, hlabJHas⟩

theorem GGSecFiveRouteCfg.qTwoOrth_denseNbr_marking (hLJ : GGSecFivePermNbrLabelOfJInput)
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {n : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hn : 5 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hAjoin : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hAL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {K : Subgroup G} (hK : GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K)
    (hJ : GGHasLabel ⟨.twA, n - 2, 1⟩ (↥J ⧸ Subgroup.center ↥J)) :
    GGInnerDiagOnLabel (fun p lab => lab.tag = .twA ∧ lab.rank = n - 1 ∧ lab.n = 1 ∧
      p ∣ 2 ^ lab.n + 1) 3 Bs K := by
  obtain ⟨eta', -, -, hAK'⟩ := GGSecFiveBCoordBDenseNbr.exists_coords hAjoin hAL hK
  have hKlab := hLJ G 3 B Bs x L D J 𝒦 hR n (by omega) eta' K hK.1 hAK' .twA 1 (Or.inr rfl)
    (largeEvenInLambda2_twA_one_iff.mpr (by omega)) hJ
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK.1
  refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig (hR.1.2.2.1.2 y K hnb)
    ((largeEvenInLambda2_twA_one_iff (r := n - 1)).mpr (by omega)) hKlab)
  rintro lab R _ I F θ ⟨rfl, hN, hI⟩
  exact ⟨⟨rfl, rfl, rfl, by norm_num⟩, hN, hI⟩

section Holds


theorem ggSecFiveBCoordBDenseNbrLabelInput_holds : GGSecFiveBCoordBDenseNbrLabelInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hCox hn eta i0 hA𝒦 hAL f hf hLabel hB hRM hG0 K hK
  obtain ⟨eta', hA𝒦', hAL', hAK'⟩ := GGSecFiveBCoordBDenseNbr.exists_coords hA𝒦 hAL hK
  obtain ⟨hK𝒦, -⟩ := hK
  have hnotSparse := ggSecFiveBCoordBDenseNbr_not_sparse hR hB hn eta' hAL' hK𝒦 hAK'
  obtain ⟨hp, hp2, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ LargeEvenBeta 4 G)
  have hBC : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨h.1.1, h.2⟩) hLabel
  have hcore := ggSecFiveBCoordBCommonJCoreInput_holds G p B Bs x L D J hR.1.1 hB n hn eta'
    i0 hAL' hBC
  obtain ⟨lab, hΛlab, hlabHas, R, hGR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcore
  obtain ⟨hlabBC, hbranch⟩ := hP.1
  obtain ⟨lab', hΛlab', hlabHas', R', hGR', I', F', θ', hP'⟩ :=
    largeEvenMarking_exists_hasLabel hLabel
  obtain ⟨-, hfn⟩ := hP'.1
  have hiso : GGLabelIso lab lab' :=
    ggLabelRigidInput_holds lab lab' (↥L ⧸ Subgroup.center ↥L) hΛlab hΛlab' hlabHas hlabHas'
  have hlabn : lab.n = f :=
    (GGSecFiveBCoordBLabel.n_eq_of_labelIso hn hlabBC hiso).symm.trans hfn
  have hdense : LargeEvenMarking J
      (fun labJ _ _ _ _ _ => GGSecFiveBCoordBJDenseLabelCore L n p lab labJ) := by
    rcases hbranch with h | h
    · exact h.2
    · exact absurd h.1 hnotSparse
  obtain ⟨labJ, hΛlabJ, hlabJHas, Rj, hGRj, Ij, Fj, θj, hlabJ⟩ :=
    largeEvenMarking_exists_hasLabel hdense
  constructor
  · intro hpd
    have hEq : labJ = ⟨.A, n - 2, f⟩ :=
      denseLabelCore_eq_linear hp hp2 hf hlabBC hlabn hlabJ hpd
    exact GGSecFiveRouteCfg.permNbr_label_of_J hR hn eta' hK𝒦 hAK' (Or.inl rfl)
      (hEq ▸ hΛlabJ) (hEq ▸ hlabJHas)
  · intro hpd
    have htA : lab.tag ≠ .A := fun h => by
      have := GGSecFiveBCoordBLabel.n_eq_one_of_tag_A hlabBC h
      omega
    have hEq : labJ = ⟨.twA, n - 2, f⟩ := denseLabelCore_eq_unitary hp hp2 htA hlabn hlabJ hpd
    exact GGSecFiveRouteCfg.permNbr_label_of_J hR hn eta' hK𝒦 hAK' (Or.inr rfl)
      (hEq ▸ hΛlabJ) (hEq ▸ hlabJHas)

theorem ggSecFiveBCoordBDenseNbrLinQTwoLabelInput_holds :
    GGSecFiveBCoordBDenseNbrLinQTwoLabelInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hCox hn eta i0 hA𝒦 hAL hLabel hB hRM hG0 K hK
  obtain ⟨eta', hA𝒦', hAL', hAK'⟩ := GGSecFiveBCoordBDenseNbr.exists_coords hA𝒦 hAL hK
  obtain ⟨hK𝒦, -⟩ := hK
  have hnotSparse := ggSecFiveBCoordBDenseNbr_not_sparse hR hB hn eta' hAL' hK𝒦 hAK'
  have hBC : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab) p Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ h => ⟨h.1.1, h.2⟩) hLabel
  have hcore := ggSecFiveBCoordBCommonJCoreInput_holds G p B Bs x L D J hR.1.1 hB n hn eta'
    i0 hAL' hBC
  obtain ⟨lab, hΛlab, hlabHas, R, hGR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hcore
  obtain ⟨hlabBC, hbranch⟩ := hP.1
  obtain ⟨lab', hΛlab', hlabHas', R', hGR', I', F', θ', hP'⟩ :=
    largeEvenMarking_exists_hasLabel hLabel
  obtain ⟨hlabBC', -, ht'⟩ := hP'.1
  have hiso : GGLabelIso lab lab' :=
    ggLabelRigidInput_holds lab lab' (↥L ⧸ Subgroup.center ↥L) hΛlab hΛlab' hlabHas hlabHas'
  have hlabA : lab.tag = .A := by
    rw [GGSecFiveBCoordBLabel.eq_of_labelIso hn hlabBC' hiso ht']
    exact ht'
  have hdense : LargeEvenMarking J
      (fun labJ _ _ _ _ _ => GGSecFiveBCoordBJDenseLabelCore L n p lab labJ) := by
    rcases hbranch with h | h
    · exact h.2
    · exact absurd h.1 hnotSparse
  obtain ⟨labJ, hΛlabJ, hlabJHas, Rj, hGRj, Ij, Fj, θj, hlabJ⟩ :=
    largeEvenMarking_exists_hasLabel hdense
  have hEq : labJ = ⟨.A, n - 2, 2⟩ := denseLabelCore_eq_linear_qtwo hlabA hlabJ
  exact GGSecFiveRouteCfg.permNbr_label_of_J hR hn eta' hK𝒦 hAK' (Or.inl rfl)
    (hEq ▸ hΛlabJ) (hEq ▸ hlabJHas)

end Holds

end CFSG.StandardType

end
