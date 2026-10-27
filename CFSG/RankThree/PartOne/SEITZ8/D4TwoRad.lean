module

public import CFSG.RankThree.PartOne.SEITZ8.D4TwoAct
public import CFSG.LieType.Steinberg.BruhatWeyl

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

@[expose] def qbList : List ℕ := [1, 4, 8, 3, 7]

theorem mem_qbList {p : ℕ} (hp : p ∈ qbList) : p = 1 ∨ p = 4 ∨ p = 8 ∨ p = 3 ∨ p = 7 := by
  simpa [qbList] using hp

variable {K : Type} [Field K] {σ : K →+* K}

variable (σ) in
@[expose] noncomputable def Qb : Subgroup (adjointGroup d4 K) :=
  ⨆ p ∈ qbList, twistedRootSubgroupD4 σ (rt p)

theorem Qb_le_Uhat : Qb σ ≤ Uhat σ := by
  refine iSup₂_le fun p hp => ?_
  refine le_iSup₂_of_le p ?_ le_rfl
  rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl <;> simp [posT]

theorem mem_Qb_of {p : ℕ} (hp : p ∈ qbList) {y : adjointGroup d4 K}
    (hy : y ∈ twistedRootSubgroupD4 σ (rt p)) : y ∈ Qb σ :=
  (le_iSup₂_of_le (f := fun p (_ : p ∈ qbList) => twistedRootSubgroupD4 σ (rt p)) p hp le_rfl) hy

section Gens

variable [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem xA_mem_Qb (a : K) : xA σ a ∈ Qb σ :=
  mem_Qb_of (p := 1) (by simp [qbList]) ((mem_XA hσ _).2 ⟨a, rfl⟩)

theorem xAB_mem_Qb (c : K) : xAB σ c ∈ Qb σ :=
  mem_Qb_of (p := 4) (by simp [qbList]) ((mem_XAB hσ _).2 ⟨c, rfl⟩)

theorem xAAB_mem_Qb (c : K) : xAAB σ c ∈ Qb σ :=
  mem_Qb_of (p := 8) (by simp [qbList]) ((mem_XAAB hσ _).2 ⟨c, rfl⟩)

omit [CharP K 2] in
theorem xN_mem_Qb {c : K} (hc : σ c = c) : xN c ∈ Qb σ :=
  mem_Qb_of (p := 3) (by simp [qbList]) ((mem_XN hσ _).2 ⟨c, hc, rfl⟩)

omit [CharP K 2] in
theorem xH_mem_Qb {c : K} (hc : σ c = c) : xH c ∈ Qb σ :=
  mem_Qb_of (p := 7) (by simp [qbList]) ((mem_XH hσ _).2 ⟨c, hc, rfl⟩)

end Gens

section ConjB

variable [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem xA_conj_xB {d : K} (hd : σ d = d) (a : K) :
    xA σ a * xB d * (xA σ a)⁻¹ = xB d * xAB σ (d * a) * xAAB σ (d * a * σ a) *
      xN (d * (a * σ a * σ (σ a))) * xH (d ^ 2 * (a * σ a * σ (σ a))) := by
  have h := conj_xB σ hσ (mkT 0 a 0 0 0 0) d hd
  rw [ordT_mkT] at h
  simp [mkT, xB, xAB, xAAB, xN, xH, xd_zero] at h
  simpa [mkT, xB, xAB, xAAB, xN, xH] using h

theorem xB_conj_xA_mem {d : K} (hd : σ d = d) (a : K) : xB d * xA σ a * (xB d)⁻¹ ∈ Qb σ := by
  have h := xA_conj_xB hσ hd a
  have hB : (xB d)⁻¹ = xB d := xd_inv 2 d
  have hN : σ (d * (a * σ a * σ (σ a))) = d * (a * σ a * σ (σ a)) := by
    simp only [map_mul, hd, hσ]
    ring
  have hHs : σ (d ^ 2 * (a * σ a * σ (σ a))) = d ^ 2 * (a * σ a * σ (σ a)) := by
    simp only [map_mul, map_pow, hd, hσ]
    ring
  set R := xAB σ (d * a) * xAAB σ (d * a * σ a) * xN (d * (a * σ a * σ (σ a))) *
    xH (d ^ 2 * (a * σ a * σ (σ a))) with hR
  have h' : xA σ a * xB d * (xA σ a)⁻¹ = xB d * R := by
    rw [h, hR]
    simp only [mul_assoc]
  have e : xB d * xA σ a * (xB d)⁻¹ = R * xA σ a := by
    calc xB d * xA σ a * (xB d)⁻¹ = (xB d)⁻¹ * (xA σ a * xB d * (xA σ a)⁻¹) * xA σ a := by
          rw [hB]
          group
      _ = (xB d)⁻¹ * (xB d * R) * xA σ a := by rw [h']
      _ = R * xA σ a := by group
  rw [e, hR]
  exact mul_mem (mul_mem (mul_mem (mul_mem (xAB_mem_Qb hσ _) (xAAB_mem_Qb hσ _))
    (xN_mem_Qb hσ hN)) (xH_mem_Qb hσ hHs)) (xA_mem_Qb hσ a)

omit hσ in
theorem commute_xB_xAB (d c : K) : Commute (xB d) (xAB σ c) := by
  unfold xB xAB
  exact ((commute_5_2 c d).symm.mul_right (commute_7_2 (σ c) d).symm).mul_right
    (commute_9_2 (σ (σ c)) d).symm

omit hσ in
theorem commute_xB_xAAB (d c : K) : Commute (xB d) (xAAB σ c) := by
  unfold xB xAAB
  exact ((commute_12_2 c d).symm.mul_right (commute_15_2 (σ c) d).symm).mul_right
    (commute_13_2 (σ (σ c)) d).symm

omit hσ in
theorem commute_xB_xH (d c : K) : Commute (xB d) (xH c) := (commute_22_2 c d).symm

omit hσ in
theorem xB_conj_xN (d e : K) : xB d * xN e * (xB d)⁻¹ = xN e * xH (d * e) := by
  have h := conj_xN (RingHom.id K) (mkT d 0 0 0 0 0) e
  rw [ordT_mkT] at h
  simpa [mkT, xA, xAB, xAAB, xN, xH, xd_zero] using h

theorem xB_conj_Qb {d : K} (hd : σ d = d) {u : adjointGroup d4 K} (hu : u ∈ Qb σ) :
    xB d * u * (xB d)⁻¹ ∈ Qb σ := by
  refine CFSG.LieType.Steinberg.conj_mem_of_forall_mem
    (X := fun p => twistedRootSubgroupD4 σ (rt p)) (P := {p | p ∈ qbList})
    (fun p hp y hy => ?_) hu
  rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, rfl⟩ := (mem_XA hσ y).1 hy
    exact xB_conj_xA_mem hσ hd a
  · obtain ⟨c, rfl⟩ := (mem_XAB hσ y).1 hy
    rw [(commute_xB_xAB d c).eq, mul_inv_cancel_right]
    exact xAB_mem_Qb hσ c
  · obtain ⟨c, rfl⟩ := (mem_XAAB hσ y).1 hy
    rw [(commute_xB_xAAB d c).eq, mul_inv_cancel_right]
    exact xAAB_mem_Qb hσ c
  · obtain ⟨e, he, rfl⟩ := (mem_XN hσ y).1 hy
    rw [xB_conj_xN]
    exact mul_mem (xN_mem_Qb hσ he) (xH_mem_Qb hσ (by simp [map_mul, hd, he]))
  · obtain ⟨e, he, rfl⟩ := (mem_XH hσ y).1 hy
    rw [(commute_xB_xH d e).eq, mul_inv_cancel_right]
    exact xH_mem_Qb hσ he

theorem nB_conj_Qb {u : adjointGroup d4 K} (hu : u ∈ Qb σ) : nB K * u * (nB K)⁻¹ ∈ Qb σ := by
  refine CFSG.LieType.Steinberg.conj_mem_of_forall_mem
    (X := fun p => twistedRootSubgroupD4 σ (rt p)) (P := {p | p ∈ qbList})
    (fun p hp y hy => ?_) hu
  rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, rfl⟩ := (mem_XA hσ y).1 hy
    rw [nB_xA]
    exact xAB_mem_Qb hσ a
  · obtain ⟨c, rfl⟩ := (mem_XAB hσ y).1 hy
    rw [nB_xAB]
    exact xA_mem_Qb hσ c
  · obtain ⟨c, rfl⟩ := (mem_XAAB hσ y).1 hy
    rw [nB_xAAB]
    exact xAAB_mem_Qb hσ c
  · obtain ⟨e, he, rfl⟩ := (mem_XN hσ y).1 hy
    rw [nB_xN]
    exact xH_mem_Qb hσ he
  · obtain ⟨e, he, rfl⟩ := (mem_XH hσ y).1 hy
    rw [nB_xH]
    exact xN_mem_Qb hσ he

theorem nB_inv_conj_Qb {u : adjointGroup d4 K} (hu : u ∈ Qb σ) :
    (nB K)⁻¹ * u * nB K ∈ Qb σ := by
  have := CFSG.LieType.Steinberg.conj_mem_of_forall_mem (c := (nB K)⁻¹)
    (X := fun p => twistedRootSubgroupD4 σ (rt p)) (P := {p | p ∈ qbList}) (M := Qb σ)
    (fun p hp y hy => ?_) hu
  · simpa using this
  · rw [inv_inv]
    rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨a, rfl⟩ := (mem_XA hσ y).1 hy
      rw [conj_inv_eq (nB_xAB σ a)]
      exact xAB_mem_Qb hσ a
    · obtain ⟨c, rfl⟩ := (mem_XAB hσ y).1 hy
      rw [conj_inv_eq (nB_xA σ c)]
      exact xA_mem_Qb hσ c
    · obtain ⟨c, rfl⟩ := (mem_XAAB hσ y).1 hy
      rw [conj_inv_eq (nB_xAAB σ c)]
      exact xAAB_mem_Qb hσ c
    · obtain ⟨e, he, rfl⟩ := (mem_XN hσ y).1 hy
      rw [conj_inv_eq (nB_xH e)]
      exact xH_mem_Qb hσ he
    · obtain ⟨e, he, rfl⟩ := (mem_XH hσ y).1 hy
      rw [conj_inv_eq (nB_xN e)]
      exact xN_mem_Qb hσ he

end ConjB

section Normalizer

variable [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem x8_conj_Qb {c : K} (hc : σ c = c) {u : adjointGroup d4 K} (hu : u ∈ Qb σ) :
    xd 8 c * u * (xd 8 c)⁻¹ ∈ Qb σ := by
  have e : xd 8 c * u * (xd 8 c)⁻¹ =
      nB K * (xB c * ((nB K)⁻¹ * u * nB K) * (xB c)⁻¹) * (nB K)⁻¹ := by
    rw [← nB_xB c]
    group
  rw [e]
  exact nB_conj_Qb hσ (xB_conj_Qb hσ hc (nB_inv_conj_Qb hσ hu))

omit [CharP K 2] hσ in
theorem mem_normalizer_Qb_of_inv {Q : Subgroup (adjointGroup d4 K)} {g : adjointGroup d4 K}
    (hg : g⁻¹ = g) (h : ∀ u ∈ Q, g * u * g⁻¹ ∈ Q) :
    g ∈ Subgroup.normalizer (Q : Set (adjointGroup d4 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => h u hu, fun hu => ?_⟩
  have e : u = g * (g * u * g⁻¹) * g⁻¹ := by
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g * (g * u * g⁻¹) * g⁻¹ := by rw [hg]
  rw [e]
  exact h _ hu

theorem range_rhoB_le_normalizer :
    (rhoB σ).range ≤ Subgroup.normalizer ((Qb σ : Subgroup (adjointGroup d4 K)) :
      Set (adjointGroup d4 K)) := by
  rintro _ ⟨A, rfl⟩
  have hS : (Subgroup.normalizer ((Qb σ : Subgroup (adjointGroup d4 K)) :
      Set (adjointGroup d4 K))).comap (rhoB σ) = ⊤ := sl2_top_of_upper_lower
    (fun c => by
      rw [Subgroup.mem_comap, rhoB_u2]
      exact mem_normalizer_Qb_of_inv (xd_inv 2 _) fun u hu => xB_conj_Qb hσ c.2 hu)
    (fun c => by
      rw [Subgroup.mem_comap, rhoB_l2]
      exact mem_normalizer_Qb_of_inv (xd_inv 8 _) fun u hu => x8_conj_Qb hσ c.2 hu)
  have : A ∈ (Subgroup.normalizer ((Qb σ : Subgroup (adjointGroup d4 K)) :
      Set (adjointGroup d4 K))).comap (rhoB σ) := hS ▸ Subgroup.mem_top A
  exact this

theorem rhoB_conj_Qb (A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ))
    {u : adjointGroup d4 K} (hu : u ∈ Qb σ) : rhoB σ A * u * (rhoB σ A)⁻¹ ∈ Qb σ :=
  (Subgroup.mem_normalizer_iff.1 (range_rhoB_le_normalizer hσ ⟨A, rfl⟩) u).1 hu

theorem mem_PL {g : adjointGroup d4 K} (hg : g ∈ (rhoB σ).range ⊔ Qb σ) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ), ∃ q ∈ Qb σ, g = rhoB σ A * q := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (rhoB σ).range (Qb σ)
    (range_rhoB_le_normalizer hσ)
  have hg' : g ∈ ((((rhoB σ).range ⊔ Qb σ : Subgroup (adjointGroup d4 K))) :
    Set (adjointGroup d4 K)) := hg
  rw [h, Set.mem_mul] at hg'
  obtain ⟨x, ⟨A, rfl⟩, y, hy, rfl⟩ := hg'
  exact ⟨A, y, hy, rfl⟩

end Normalizer

section Central

variable [CharP K 2]

omit [CharP K 2] in
theorem commute_xd_same (p : ℕ) (a b : K) : Commute (xd p a) (xd p b) := by
  show xd p a * xd p b = xd p b * xd p a
  rw [← xd_add, ← xd_add, add_comm]

theorem commute_xA_xH (a e : K) : Commute (xA σ a) (xH e) := by
  unfold xA xH
  exact ((commute_22_0 e a).symm.mul_left (commute_22_1 e (σ a)).symm).mul_left
    (commute_22_3 e (σ (σ a))).symm

theorem commute_xA_xN (a e : K) : Commute (xA σ a) (xN e) := by
  unfold xA xN
  exact ((commute_19_0 e a).symm.mul_left (commute_19_1 e (σ a)).symm).mul_left
    (commute_19_3 e (σ (σ a))).symm

theorem commute_xAB_xH (a e : K) : Commute (xAB σ a) (xH e) := by
  unfold xAB xH
  exact ((commute_22_5 e a).symm.mul_left (commute_22_7 e (σ a)).symm).mul_left
    (commute_22_9 e (σ (σ a))).symm

theorem commute_xAB_xN (a e : K) : Commute (xAB σ a) (xN e) := by
  unfold xAB xN
  exact ((commute_19_5 e a).symm.mul_left (commute_19_7 e (σ a)).symm).mul_left
    (commute_19_9 e (σ (σ a))).symm

theorem commute_xAAB_xH (a e : K) : Commute (xAAB σ a) (xH e) := by
  unfold xAAB xH
  exact ((commute_22_12 e a).symm.mul_left (commute_22_15 e (σ a)).symm).mul_left
    (commute_22_13 e (σ (σ a))).symm

theorem commute_xAAB_xN (a e : K) : Commute (xAAB σ a) (xN e) := by
  unfold xAAB xN
  exact ((commute_19_12 e a).symm.mul_left (commute_19_15 e (σ a)).symm).mul_left
    (commute_19_13 e (σ (σ a))).symm

variable (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem commute_gen_dv {p : ℕ} (hp : p ∈ qbList) {y : adjointGroup d4 K}
    (hy : y ∈ twistedRootSubgroupD4 σ (rt p)) (a b : fixedField σ) : Commute y (dv a b) := by
  unfold dv
  apply Commute.mul_right
  · rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨c, rfl⟩ := (mem_XA hσ y).1 hy
      exact commute_xA_xH c a
    · obtain ⟨c, rfl⟩ := (mem_XAB hσ y).1 hy
      exact commute_xAB_xH c a
    · obtain ⟨c, rfl⟩ := (mem_XAAB hσ y).1 hy
      exact commute_xAAB_xH c a
    · obtain ⟨c, -, rfl⟩ := (mem_XN hσ y).1 hy
      exact (commute_xH_xN (a : K) c).symm
    · obtain ⟨c, -, rfl⟩ := (mem_XH hσ y).1 hy
      exact commute_xd_same 22 c a
  · rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨c, rfl⟩ := (mem_XA hσ y).1 hy
      exact commute_xA_xN c b
    · obtain ⟨c, rfl⟩ := (mem_XAB hσ y).1 hy
      exact commute_xAB_xN c b
    · obtain ⟨c, rfl⟩ := (mem_XAAB hσ y).1 hy
      exact commute_xAAB_xN c b
    · obtain ⟨c, -, rfl⟩ := (mem_XN hσ y).1 hy
      exact commute_xd_same 19 c b
    · obtain ⟨c, -, rfl⟩ := (mem_XH hσ y).1 hy
      exact commute_xH_xN c (b : K)

theorem Qb_commute_dv {q : adjointGroup d4 K} (hq : q ∈ Qb σ) (a b : fixedField σ) :
    q * dv a b = dv a b * q := by
  have hle : Qb σ ≤ Subgroup.centralizer ({dv a b} : Set (adjointGroup d4 K)) := by
    refine iSup₂_le fun p hp y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (commute_gen_dv hσ hp hy a b).symm.eq
  have := Subgroup.mem_centralizer_iff.1 (hle hq) (dv a b) (Set.mem_singleton _)
  exact this.symm

theorem Qb_conj_dvv {q : adjointGroup d4 K} (hq : q ∈ Qb σ) (v : Fin 2 → fixedField σ) :
    q * dvv v * q⁻¹ = dvv v := by
  rw [dvv, Qb_commute_dv hσ hq]
  group

theorem ActsAs.mul_Qb {g q : adjointGroup d4 K}
    {A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)} (hg : ActsAs g A) (hq : q ∈ Qb σ) :
    ActsAs (g * q) A := fun v => by
  rw [show g * q * dvv v * (g * q)⁻¹ = g * (q * dvv v * q⁻¹) * g⁻¹ by group, Qb_conj_dvv hσ hq,
    hg v]

theorem ActsAs.Qb_mul {g q : adjointGroup d4 K}
    {A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)} (hg : ActsAs g A) (hq : q ∈ Qb σ) :
    ActsAs (q * g) A := fun v => by
  rw [show q * g * dvv v * (q * g)⁻¹ = q * (g * dvv v * g⁻¹) * q⁻¹ by group, hg v,
    Qb_conj_dvv hσ hq]

theorem exists_actsAs_of_mem_PL {g : adjointGroup d4 K} (hg : g ∈ (rhoB σ).range ⊔ Qb σ) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ), ∃ q ∈ Qb σ,
      g = rhoB σ A * q ∧ ActsAs g A := by
  obtain ⟨A, q, hq, rfl⟩ := mem_PL hσ hg
  exact ⟨A, q, hq, rfl, (actsAs_rhoB A).mul_Qb hσ hq⟩

end Central

end CFSG.RankThree.PartOne.SEITZ8
