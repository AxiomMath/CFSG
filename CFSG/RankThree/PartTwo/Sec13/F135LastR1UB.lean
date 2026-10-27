module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR1U0
public import CFSG.RankThree.PartTwo.Sec13.F135LastR1UA
public import CFSG.RankThree.PartTwo.Sec13.F135LastR1Z
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven
public import CFSG.RankThree.PartTwo.Sec13.F135LastAct
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open Equiv Equiv.Perm Subgroup

@[expose] noncomputable def u1Phi {M : Type} [Group M] (J : Subgroup M) [J.Normal]
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) : M →* Equiv.Perm (Fin 7) :=
  (u1AltEquiv e).toMonoidHom.comp
    ((CFSG.RankThree.PartTwo.Sec13.F135Last.centerQuotMulAut J).comp
      (MulAut.conjNormal (H := J)))

theorem u1b1_centerQuot_conj {M : Type} [Group M] (J : Subgroup M) (j : J) :
    centerQuotMulAut J (MulAut.conj j) = MulAut.conj (QuotientGroup.mk j : J ⧸ Subgroup.center J) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x => rfl

theorem u1Phi_mem {M : Type} [Group M] (J : Subgroup M) [J.Normal]
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) (j : J) :
    u1Phi J e (j : M) = u1Psi e (QuotientGroup.mk j) := by
  show u1AltEquiv e (centerQuotMulAut J (MulAut.conjNormal (H := J) (j : M))) =
    u1Psi e (QuotientGroup.mk j)
  rw [MulAut.conjNormal_val, u1b1_centerQuot_conj, u1AltEquiv_conj]

theorem u1Phi_ker {M : Type} [Group M] (J : Subgroup M) [J.Normal] (hJ : Group.IsPerfect J)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) (m : M) :
    u1Phi J e m = 1 ↔ m ∈ Subgroup.centralizer (J : Set M) := by
  have hm : m ∈ Subgroup.normalizer (J : Set M) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top m
  have key : MulAut.conjNormal (H := J) m = J.normalizerMonoidHom ⟨m, hm⟩ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  have h1 : u1Phi J e m = 1 ↔ centerQuotMulAut J (MulAut.conjNormal (H := J) m) = 1 := by
    show u1AltEquiv e (centerQuotMulAut J (MulAut.conjNormal (H := J) m)) = 1 ↔ _
    exact (u1AltEquiv e).map_eq_one_iff
  have h2 : centerQuotMulAut J (MulAut.conjNormal (H := J) m) = actS J ⟨m, hm⟩ :=
    congrArg (fun φ : MulAut J => centerQuotMulAut J φ) key
  rw [h1, h2]
  exact actS_eq_one_iff hJ ⟨m, hm⟩

theorem u1Phi_range_alt {M : Type} [Group M] (J : Subgroup M) [J.Normal]
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) {σ : Perm (Fin 7)}
    (hσ : σ ∈ alternatingGroup (Fin 7)) : σ ∈ (u1Phi J e).range := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
  rw [MonoidHom.mem_range]
  refine ⟨(x : M), ?_⟩
  rw [u1Phi_mem, hx, u1Psi_apply, MulEquiv.apply_symm_apply]

theorem u1_exists_sqrt {E : Type} [Group E] [Finite E] (hE : Group.IsPerfect E)
    (hZ : Nat.card (Subgroup.center E) = 2)
    (e : E ⧸ Subgroup.center E ≃* alternatingGroup (Fin 7))
    {z : E} (hz : z ∈ Subgroup.center E) (hz1 : z ≠ 1) : ∃ x : E, x * x = z := by
  haveI := hE
  have hd2 : CFSG.ComponentClassification.Sol78.dtA ^ 2 = 1 := by
    have h := pow_orderOf_eq_one CFSG.ComponentClassification.Sol78.dtA
    rwa [CFSG.ComponentClassification.Sol78.orderOf_dtA] at h
  have hdd : CFSG.ComponentClassification.Sol78.dtA * CFSG.ComponentClassification.Sol78.dtA = 1 := by
    rw [← pow_two]
    exact hd2
  have hd1 : CFSG.ComponentClassification.Sol78.dtA ≠ 1 := by
    intro h
    have h2 := CFSG.ComponentClassification.Sol78.orderOf_dtA
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  obtain ⟨q, hq⟩ := e.surjective CFSG.ComponentClassification.Sol78.dtA
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hsq : e (QuotientGroup.mk (y * y)) = 1 := by
    rw [QuotientGroup.mk_mul, map_mul, hq]
    exact hdd
  have hyy : y * y ∈ Subgroup.center E :=
    (QuotientGroup.eq_one_iff (y * y)).mp (e.injective (hsq.trans (map_one e).symm))
  have hyy1 : y * y ≠ 1 := by
    intro h
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hd1
      rw [← hq]
      simp
    have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact h) hy1
    have hyc : y ∈ Subgroup.center E :=
      CFSG.ComponentClassification.Sol78.mem_center_of_orderOf_eq_two_of_alternating_seven hZ e hy2
    apply hd1
    rw [← hq, (QuotientGroup.eq_one_iff y).mpr hyc, map_one]
  exact ⟨y, (CFSG.RankThree.PartTwo.Sec13.Res7Proof.r1c_eq_one_or_eq_of_natCard_two
    (Subgroup.center E) hZ hz hz1 hyy).resolve_left hyy1⟩

theorem u1_center_central {M : Type} [Group M] (J : Subgroup M) [J.Normal]
    (hZ : Nat.card (Subgroup.center J) = 2) {z : J} (hz : z ∈ Subgroup.center J) (m : M) :
    m * (z : M) = (z : M) * m := by
  by_cases hz1 : z = 1
  · subst hz1
    simp
  obtain ⟨w, hw⟩ : ∃ w : J, (w : M) = m * (z : M) * m⁻¹ :=
    ⟨⟨m * (z : M) * m⁻¹, Subgroup.Normal.conj_mem ‹J.Normal› (z : M) z.2 m⟩, rfl⟩
  have hw1 : w ≠ 1 := by
    intro h
    have h1 : (w : M) = 1 := by simp [h]
    have h2 : m * (z : M) * m⁻¹ = 1 := by rw [← hw, h1]
    have h3 : (z : M) = 1 := by
      calc (z : M) = m⁻¹ * (m * (z : M) * m⁻¹) * m := by group
        _ = 1 := by rw [h2]; group
    exact hz1 (Subtype.ext h3)
  have hwc : w ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hk : m⁻¹ * (g : M) * m ∈ J := by
      have h := Subgroup.Normal.conj_mem ‹J.Normal› (g : M) g.2 m⁻¹
      rwa [inv_inv] at h
    have hkz : m⁻¹ * (g : M) * m * (z : M) = (z : M) * (m⁻¹ * (g : M) * m) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨m⁻¹ * (g : M) * m, hk⟩)
    show (g : M) * (w : M) = (w : M) * (g : M)
    rw [hw]
    calc (g : M) * (m * (z : M) * m⁻¹) = m * (m⁻¹ * (g : M) * m * (z : M)) * m⁻¹ := by group
      _ = m * ((z : M) * (m⁻¹ * (g : M) * m)) * m⁻¹ := by rw [hkz]
      _ = m * (z : M) * m⁻¹ * (g : M) := by group
  have hwz : w = z :=
    (CFSG.RankThree.PartTwo.Sec13.Res7Proof.r1c_eq_one_or_eq_of_natCard_two
      (Subgroup.center J) hZ hz hz1 hwc).resolve_left hw1
  have h3 : m * (z : M) * m⁻¹ = (z : M) := by rw [← hw, hwz]
  calc m * (z : M) = m * (z : M) * m⁻¹ * m := by group
    _ = (z : M) * m := by rw [h3]

theorem u1b3_mul_self_eq_one {G : Type} [Group G] (S : Subgroup G) (hS : Nat.card S = 2)
    {z : G} (hz : z ∈ S) (hz1 : z ≠ 1) : z * z = 1 := by
  rcases CFSG.RankThree.PartTwo.Sec13.Res7Proof.r1c_eq_one_or_eq_of_natCard_two S hS hz hz1
    (Subgroup.mul_mem S hz hz) with h | h
  · exact h
  · have h' : z * z = z * 1 := by rw [mul_one]; exact h
    exact absurd (mul_left_cancel h') hz1

theorem u1b3_sq_ne {G : Type} [Group G] (S : Subgroup G) (hS : Nat.card S = 2)
    {c z : G} (hc : c ∈ S) (hz : z ∈ S) (hz1 : z ≠ 1) (hcc : c * c = z) : False := by
  rcases CFSG.RankThree.PartTwo.Sec13.Res7Proof.r1c_eq_one_or_eq_of_natCard_two S hS hz hz1 hc
    with h | h
  · rw [h, one_mul] at hcc
    exact hz1 hcc.symm
  · rw [h] at hcc
    exact hz1 (hcc.symm.trans (u1b3_mul_self_eq_one S hS hz hz1))

theorem u1b3_chain {M : Type} [Group M] (Z C : Subgroup M) (k : ℕ) :
    ∀ g : M, g ∈ C → g ^ 2 ^ k = 1 → g ∉ Z → ∃ h ∈ C, h ∉ Z ∧ h * h ∈ Z := by
  induction k with
  | zero =>
    intro g _ hk hgZ
    exfalso
    apply hgZ
    rw [pow_zero, pow_one] at hk
    rw [hk]
    exact Z.one_mem
  | succ k ih =>
    intro g hg hk hgZ
    by_cases hgg : g * g ∈ Z
    · exact ⟨g, hg, hgZ, hgg⟩
    · refine ih (g * g) (C.mul_mem hg hg) ?_ hgg
      have e : (g * g) ^ 2 ^ k = g ^ 2 ^ (k + 1) := by
        rw [← sq, ← pow_mul, ← pow_succ']
      rw [e]
      exact hk

theorem u1b3_mem_zc {M : Type} [Group M] (J : Subgroup M) {x : J}
    (hx : (x : M) ∈ Subgroup.centralizer (J : Set M)) :
    (x : M) ∈ (Subgroup.center J).map J.subtype := by
  refine Subgroup.mem_map_of_mem J.subtype ?_
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  have hw := Subgroup.mem_centralizer_iff.mp hx (w : M) w.2
  simpa using hw

theorem u1_K {M : Type} [Group M] [Finite M] (J : Subgroup M) [J.Normal] (hJ : Group.IsPerfect J)
    (hZ : Nat.card (Subgroup.center J) = 2)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7))
    {g : M} (hg : g ∈ Subgroup.centralizer (J : Set M)) (hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1)
    (hgZ : g ∉ (Subgroup.center J).map J.subtype) :
    ∃ u : M, u * u = 1 ∧ u ∉ (Subgroup.center J).map J.subtype := by
  have hZc2 : Nat.card ((Subgroup.center J).map J.subtype) = 2 :=
    (Subgroup.card_map_of_injective (Subgroup.subtype_injective J)).trans hZ
  obtain ⟨k, hk⟩ := hg2
  obtain ⟨h, hh, hhZ, hhh⟩ :=
    u1b3_chain ((Subgroup.center J).map J.subtype) (Subgroup.centralizer (J : Set M)) k g hg hk hgZ
  by_cases hz1 : h * h = 1
  · exact ⟨h, hz1, hhZ⟩
  · obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hhh
    have hc1 : c ≠ 1 := by
      rintro rfl
      apply hz1
      rw [← hcz, map_one]
    obtain ⟨x, hx⟩ := u1_exists_sqrt hJ hZ e hc hc1
    have hxM : (x : M) * (x : M) = h * h := by
      rw [← hcz, ← hx]
      exact rfl
    have hcomm : h * (x : M) = (x : M) * h :=
      (Subgroup.mem_centralizer_iff.mp hh (x : M) x.2).symm
    refine ⟨h * (x : M), ?_, ?_⟩
    · have e1 : h * (x : M) * (h * (x : M)) = h * ((x : M) * h) * (x : M) := by
        simp only [mul_assoc]
      have e2 : h * (h * (x : M)) * (x : M) = (h * h) * ((x : M) * (x : M)) := by
        simp only [mul_assoc]
      rw [e1, ← hcomm, e2, hxM]
      exact u1b3_mul_self_eq_one _ hZc2 hhh hz1
    · intro hu
      rcases CFSG.RankThree.PartTwo.Sec13.Res7Proof.r1c_eq_one_or_eq_of_natCard_two _ hZc2 hhh hz1 hu
        with h1 | h1
      · have hxinv : (x : M) = h⁻¹ := eq_inv_of_mul_eq_one_right h1
        have hcent : (x : M) ∈ Subgroup.centralizer (J : Set M) := by
          rw [hxinv]
          exact Subgroup.inv_mem _ hh
        exact u1b3_sq_ne _ hZc2 (u1b3_mem_zc J hcent) hhh hz1 hxM
      · have hxh : (x : M) = h := mul_left_cancel h1
        have hcent : (x : M) ∈ Subgroup.centralizer (J : Set M) := by
          rw [hxh]
          exact hh
        exact u1b3_sq_ne _ hZc2 (u1b3_mem_zc J hcent) hhh hz1 hxM

theorem u1b4_sq_conj {G : Type*} [Group G] (s d : G) (h : s * d * s⁻¹ = d⁻¹) :
    s ^ 2 * d * (s ^ 2)⁻¹ = d := by
  calc s ^ 2 * d * (s ^ 2)⁻¹ = s * (s * d * s⁻¹) * s⁻¹ := by
        simp only [sq, mul_inv_rev, mul_assoc]
    _ = s * d⁻¹ * s⁻¹ := by rw [h]
    _ = (s * d * s⁻¹)⁻¹ := by group
    _ = d := by rw [h, inv_inv]

theorem u1b4_conj_mul {G : Type*} [Group G] (p q d : G) (hp : p * d * p⁻¹ = d⁻¹)
    (hq : q * d * q⁻¹ = d) : p * q * d * (p * q)⁻¹ = d⁻¹ := by
  calc p * q * d * (p * q)⁻¹ = p * (q * d * q⁻¹) * p⁻¹ := by group
    _ = p * d * p⁻¹ := by rw [hq]
    _ = d⁻¹ := hp

theorem u1b4_odd_pow_conj {G : Type*} [Group G] (s d : G) (h : s * d * s⁻¹ = d⁻¹) (n : ℕ) :
    s ^ (2 * n + 1) * d * (s ^ (2 * n + 1))⁻¹ = d⁻¹ := by
  induction n with
  | zero => simpa using h
  | succ k ih =>
    have e1 : s ^ (2 * (k + 1) + 1) = s ^ (2 * k + 1) * s ^ 2 := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add s (2 * k + 1) 2]
    rw [e1]
    exact u1b4_conj_mul _ _ d ih (u1b4_sq_conj s d h)

theorem u1b4_exists_nontriv {G : Type*} [Group G] (S : Subgroup G) (hS : Nat.card S = 2) :
    ∃ a : G, a ∈ S ∧ a ≠ 1 := by
  obtain ⟨u, hu1, -⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hS
  exact ⟨(u : G), u.2, fun h => hu1 (Subtype.ext h)⟩

theorem u1b4_sq_eq_one {M : Type} [Group M] (J : Subgroup M)
    (hZ : Nat.card (Subgroup.center J) = 2) {z : J} (hz : z ∈ Subgroup.center J) (hz1 : z ≠ 1) :
    z * z = 1 := by
  rcases CFSG.RankThree.PartTwo.Sec13.Res7Proof.r1c_eq_one_or_eq_of_natCard_two
      (Subgroup.center J) hZ hz hz1 (mul_mem hz hz) with h | h
  · exact h
  · have h' : z * z = z * 1 := by rw [mul_one]; exact h
    exact absurd (mul_left_cancel h') hz1

theorem u1b4_comm_of_mem_Zc {M : Type} [Group M] (J : Subgroup M) [J.Normal]
    (hZ : Nat.card (Subgroup.center J) = 2) {w : M}
    (hw : w ∈ (Subgroup.center J).map J.subtype) (m : M) : m * w = w * m := by
  obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
  exact u1_center_central J hZ hw' m

theorem u1b4_mem_centralizer_of_mem_center {M : Type} [Group M] (J : Subgroup M) {w : J}
    (hw : w ∈ Subgroup.center J) : (w : M) ∈ Subgroup.centralizer (J : Set M) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have h2 := Subgroup.mem_center_iff.mp hw ⟨h, hh⟩
  exact congrArg Subtype.val h2

theorem u1b4_no_inv_central {G : Type*} [Group G] (d g : G) (hc : d * g = g * d)
    (hinv : g * d * g⁻¹ = d⁻¹) (hd : d * d ≠ 1) : False := by
  apply hd
  have hdd : d = d⁻¹ := by
    calc d = d * g * g⁻¹ := by group
      _ = g * d * g⁻¹ := by rw [hc]
      _ = d⁻¹ := hinv
  calc d * d = d * d⁻¹ := by rw [← hdd]
    _ = 1 := mul_inv_cancel d

theorem u1b4_swap_range {M : Type} [Group M] (J : Subgroup M) [J.Normal]
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7))
    {τ σ : Equiv.Perm (Fin 7)} (hτR : τ ∈ (u1Phi J e).range)
    (hτA : τ ∉ alternatingGroup (Fin 7)) (hσ : Equiv.Perm.sign σ = -1) :
    σ ∈ (u1Phi J e).range := by
  have hτs : Equiv.Perm.sign τ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h1 | h1
    · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h1) hτA
    · exact h1
  have hA : τ⁻¹ * σ ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hτs, hσ] <;>
      first | decide | rfl | simp
  have hR := u1Phi_range_alt J e hA
  have hm := mul_mem hτR hR
  rwa [mul_inv_cancel_left] at hm

theorem u1b4_not_alt {M : Type} [Group M] [Finite M] (J : Subgroup M) [J.Normal]
    (hJ : Group.IsPerfect J) (hZ : Nat.card (Subgroup.center J) = 2)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7))
    {t d : M} (hdJ : d ∈ Subgroup.centralizer (J : Set M))
    (hd : d * d ≠ 1) (htd : t * d * t⁻¹ = d⁻¹)
    (hK : ¬ ∃ g ∈ Subgroup.centralizer (J : Set M),
      (∃ k : ℕ, g ^ 2 ^ k = 1) ∧ g ∉ (Subgroup.center J).map J.subtype)
    (h : u1Phi J e t ∈ alternatingGroup (Fin 7)) : False := by
  obtain ⟨q, hq⟩ := e.surjective (⟨u1Phi J e t, h⟩ : alternatingGroup (Fin 7))
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hy : u1Phi J e (y : M) = u1Phi J e t := by
    simp only [u1Phi_mem, u1Psi_apply, hq]
  have hs₀C : (y : M)⁻¹ * t ∈ Subgroup.centralizer (J : Set M) := by
    refine (u1Phi_ker J hJ e _).mp ?_
    rw [map_mul, map_inv, hy, inv_mul_cancel]
  have hyd : (y : M) * d = d * (y : M) := Subgroup.mem_centralizer_iff.mp hdJ (y : M) y.2
  have hyd' : d⁻¹ * (y : M) = (y : M) * d⁻¹ := by
    calc d⁻¹ * (y : M) = d⁻¹ * ((y : M) * d) * d⁻¹ := by group
      _ = d⁻¹ * (d * (y : M)) * d⁻¹ := by rw [hyd]
      _ = (y : M) * d⁻¹ := by group
  have hconj : (y : M)⁻¹ * t * d * ((y : M)⁻¹ * t)⁻¹ = d⁻¹ := by
    calc (y : M)⁻¹ * t * d * ((y : M)⁻¹ * t)⁻¹ = (y : M)⁻¹ * (t * d * t⁻¹) * (y : M) := by group
      _ = (y : M)⁻¹ * d⁻¹ * (y : M) := by rw [htd]
      _ = d⁻¹ := by rw [mul_assoc, hyd', inv_mul_cancel_left]
  obtain ⟨o, ho, e', he'⟩ := u1_two_part ((y : M)⁻¹ * t)
  obtain ⟨n, rfl⟩ := ho
  apply hK
  refine ⟨((y : M)⁻¹ * t) ^ (2 * n + 1), pow_mem hs₀C _, ⟨e', he'⟩, fun hgZ => ?_⟩
  exact u1b4_no_inv_central d _ (u1b4_comm_of_mem_Zc J hZ hgZ d)
    (u1b4_odd_pow_conj _ d hconj n) hd

theorem u1_main {M : Type} [Group M] [Finite M] (J : Subgroup M) [J.Normal] (hJ : Group.IsPerfect J)
    (hZ : Nat.card (Subgroup.center J) = 2)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7))
    {t d : M} (hdJ : d ∈ Subgroup.centralizer (J : Set M))
    (hd : d * d ≠ 1) (htd : t * d * t⁻¹ = d⁻¹) :
    ∃ u : M, u * u = 1 ∧ u ∉ (Subgroup.center J).map J.subtype := by
  obtain ⟨z₀, hz₀, hz₀1⟩ := u1b4_exists_nontriv (Subgroup.center J) hZ
  have hz₀2 : z₀ * z₀ = 1 := u1b4_sq_eq_one J hZ hz₀ hz₀1
  have hzM2 : (z₀ : M) * (z₀ : M) = 1 := by
    rw [← Subgroup.coe_mul, hz₀2, Subgroup.coe_one]
  have hzMc : ∀ m : M, m * (z₀ : M) = (z₀ : M) * m := fun m => u1_center_central J hZ hz₀ m
  have hZc_one_or : ∀ w : M, w ∈ (Subgroup.center J).map J.subtype → w = 1 ∨ w = (z₀ : M) := by
    intro w hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
    rcases CFSG.RankThree.PartTwo.Sec13.Res7Proof.r1c_eq_one_or_eq_of_natCard_two
        (Subgroup.center J) hZ hz₀ hz₀1 hw' with h1 | h1
    · exact Or.inl ((congrArg J.subtype h1).trans (map_one J.subtype))
    · exact Or.inr (congrArg J.subtype h1)
  by_cases hK : ∃ g ∈ Subgroup.centralizer (J : Set M),
      (∃ k : ℕ, g ^ 2 ^ k = 1) ∧ g ∉ (Subgroup.center J).map J.subtype
  · obtain ⟨g, hg, hg2, hgZ⟩ := hK
    exact u1_K J hJ hZ e hg hg2 hgZ
  · have hτR : u1Phi J e t ∈ (u1Phi J e).range := MonoidHom.mem_range.mpr ⟨t, rfl⟩
    have htA : u1Phi J e t ∉ alternatingGroup (Fin 7) :=
      fun h => u1b4_not_alt J hJ hZ e hdJ hd htd hK h
    have hker : ∀ g : M, (∃ k : ℕ, g ^ 2 ^ k = 1) → u1Phi J e g = 1 →
        g = 1 ∨ g = (z₀ : M) := by
      intro g hg2 hg1
      have hgC : g ∈ Subgroup.centralizer (J : Set M) := (u1Phi_ker J hJ e g).mp hg1
      have hgZ : g ∈ (Subgroup.center J).map J.subtype := by
        by_contra hgZ
        exact hK ⟨g, hgC, hg2, hgZ⟩
      exact hZc_one_or g hgZ
    have ha : Equiv.swap (0 : Fin 7) 1 ∈ (u1Phi J e).range :=
      u1b4_swap_range J e hτR htA (Equiv.Perm.sign_swap (by decide))
    have hb : Equiv.swap (2 : Fin 7) 3 ∈ (u1Phi J e).range :=
      u1b4_swap_range J e hτR htA (Equiv.Perm.sign_swap (by decide))
    have hc : Equiv.swap (4 : Fin 7) 5 ∈ (u1Phi J e).range :=
      u1b4_swap_range J e hτR htA (Equiv.Perm.sign_swap (by decide))
    obtain ⟨u, hu2, hu1⟩ := u1_O (u1Phi J e) (z₀ : M) hzM2 hzMc hker ha hb hc
    refine ⟨u, hu2, fun hmem => hu1 ?_⟩
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp hmem
    rw [← hwu]
    exact (u1Phi_ker J hJ e _).mpr (u1b4_mem_centralizer_of_mem_center J hw)

end CFSG.RankThree.PartTwo.Sec13.F135Last
