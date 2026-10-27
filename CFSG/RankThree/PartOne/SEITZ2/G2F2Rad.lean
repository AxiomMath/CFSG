module

public import CFSG.RankThree.PartOne.SEITZ2.G2F2Act
public import CFSG.LieType.Steinberg.BruhatWeyl

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ6
  CFSG.RankThree.PartOne.CTP
open scoped commutatorElement Matrix

variable {K : Type} [Field K]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) K

@[expose] def qbList : List ℕ := [1, 4, 8, 3, 7]

theorem mem_qbList {p : ℕ} (hp : p ∈ qbList) : p = 1 ∨ p = 4 ∨ p = 8 ∨ p = 3 ∨ p = 7 := by
  simpa [qbList] using hp

theorem lt_twelve_of_mem_qbList {p : ℕ} (hp : p ∈ qbList) : p < 12 := by
  rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl <;> norm_num


@[expose] noncomputable def Qb (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  ⨆ p ∈ qbList, Xp K p

theorem xp_mem_Qb {p : ℕ} (hp : p ∈ qbList) (c : K) : xp p c ∈ Qb K :=
  (le_iSup₂_of_le (f := fun p (_ : p ∈ qbList) => Xp K p) p hp le_rfl)
    (xp_mem_Xp p (lt_twelve_of_mem_qbList hp) c)

theorem Qb_le_Ug : Qb K ≤ Ug K := by
  refine iSup₂_le fun p hp => ?_
  refine le_iSup₂_of_le p ?_ le_rfl
  rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl <;> simp [posList]

theorem xp_mem_Ug {p : ℕ} (hp : p ∈ posList) (c : K) : xp p c ∈ Ug K :=
  (le_iSup₂_of_le (f := fun p (_ : p ∈ posList) => Xp K p) p hp le_rfl)
    (xp_mem_Xp p (lt_twelve_of_mem_posList hp) c)

theorem conj_Qb_of_gens {c : adjointGroup .G2 K}
    (h : ∀ p ∈ qbList, ∀ y ∈ Xp K p, c * y * c⁻¹ ∈ Qb K) {u : adjointGroup .G2 K}
    (hu : u ∈ Qb K) : c * u * c⁻¹ ∈ Qb K :=
  CFSG.LieType.Steinberg.conj_mem_of_forall_mem (X := fun p => Xp K p) (P := {p | p ∈ qbList}) h hu

variable [CharP K 2]

theorem x0_conj_Qb (c : K) {u : adjointGroup .G2 K} (hu : u ∈ Qb K) :
    xp 0 c * u * (xp 0 c)⁻¹ ∈ Qb K := by
  refine conj_Qb_of_gens (fun p hp y hy => ?_) hu
  obtain ⟨d, rfl⟩ := (mem_Xp_iff (lt_twelve_of_mem_qbList hp) y).1 hy
  have q1 := xp_mem_Qb (K := K) (p := 1) (by simp [qbList])
  have q4 := xp_mem_Qb (K := K) (p := 4) (by simp [qbList])
  have q8 := xp_mem_Qb (K := K) (p := 8) (by simp [qbList])
  have q3 := xp_mem_Qb (K := K) (p := 3) (by simp [qbList])
  have q7 := xp_mem_Qb (K := K) (p := 7) (by simp [qbList])
  rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
  · have e : xp 0 c * xp 1 d * (xp 0 c)⁻¹ =
        (xp 4 (d * c) * xp 8 (d ^ 2 * c) * xp 3 (d ^ 3 * c))⁻¹ * xp 1 d := by
      rw [swap_inv _ _ _ (swap_10 d c)]
      group
    rw [e]
    exact mul_mem (inv_mem (mul_mem (mul_mem (q4 _) (q8 _)) (q3 _))) (q1 _)
  · rw [(commute_04 c d).eq]
    simpa using q4 d
  · rw [(commute_08 c d).eq]
    simpa using q8 d
  · rw [swap_03]
    simpa [mul_assoc] using mul_mem (q7 (c * d)) (q3 d)
  · rw [(commute_07 c d).eq]
    simpa using q7 d

theorem nB_conj_Qb {u : adjointGroup .G2 K} (hu : u ∈ Qb K) :
    nB K * u * (nB K)⁻¹ ∈ Qb K := by
  refine conj_Qb_of_gens (fun p hp y hy => ?_) hu
  obtain ⟨d, rfl⟩ := (mem_Xp_iff (lt_twelve_of_mem_qbList hp) y).1 hy
  rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
  · rw [nB_x1]; exact xp_mem_Qb (by simp [qbList]) _
  · rw [nB_x4]; exact xp_mem_Qb (by simp [qbList]) _
  · rw [nB_x8]; exact xp_mem_Qb (by simp [qbList]) _
  · rw [nB_x3]; exact xp_mem_Qb (by simp [qbList]) _
  · rw [nB_x7]; exact xp_mem_Qb (by simp [qbList]) _

theorem nB_inv_conj_Qb {u : adjointGroup .G2 K} (hu : u ∈ Qb K) :
    (nB K)⁻¹ * u * nB K ∈ Qb K := by
  have := conj_Qb_of_gens (c := (nB K)⁻¹) (fun p hp y hy => ?_) hu
  · simpa using this
  · obtain ⟨d, rfl⟩ := (mem_Xp_iff (lt_twelve_of_mem_qbList hp) y).1 hy
    rw [inv_inv]
    rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
    · rw [conj_inv_eq (nB_x4 d)]; exact xp_mem_Qb (by simp [qbList]) _
    · rw [conj_inv_eq (nB_x1 d)]; exact xp_mem_Qb (by simp [qbList]) _
    · rw [conj_inv_eq (nB_x8 d)]; exact xp_mem_Qb (by simp [qbList]) _
    · rw [conj_inv_eq (nB_x7 d)]; exact xp_mem_Qb (by simp [qbList]) _
    · rw [conj_inv_eq (nB_x3 d)]; exact xp_mem_Qb (by simp [qbList]) _

theorem x2_conj_Qb (c : K) {u : adjointGroup .G2 K} (hu : u ∈ Qb K) :
    xp 2 c * u * (xp 2 c)⁻¹ ∈ Qb K := by
  have e : xp 2 c * u * (xp 2 c)⁻¹ =
      nB K * (xp 0 c * ((nB K)⁻¹ * u * nB K) * (xp 0 c)⁻¹) * (nB K)⁻¹ := by
    rw [← nB_x0 c]
    group
  rw [e]
  exact nB_conj_Qb (x0_conj_Qb c (nB_inv_conj_Qb hu))

omit [CharP K 2] in
theorem mem_normalizer_Qb_of_inv {g : adjointGroup .G2 K} (hg : g⁻¹ = g)
    (h : ∀ u ∈ Qb K, g * u * g⁻¹ ∈ Qb K) :
    g ∈ Subgroup.normalizer
      ((Qb K : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => h u hu, fun hu => ?_⟩
  have e : u = g * (g * u * g⁻¹) * g⁻¹ := by
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g * (g * u * g⁻¹) * g⁻¹ := by rw [hg]
  rw [e]
  exact h _ hu

theorem range_rhoB_le_normalizer :
    (rhoB K).range ≤ Subgroup.normalizer ((Qb K : Subgroup (adjointGroup .G2 K)) :
      Set (adjointGroup .G2 K)) := by
  rintro _ ⟨A, rfl⟩
  have hS : (Subgroup.normalizer ((Qb K : Subgroup (adjointGroup .G2 K)) :
      Set (adjointGroup .G2 K))).comap (rhoB K) = ⊤ := sl2_top_of_upper_lower
    (fun c => by
      rw [Subgroup.mem_comap, rhoB_u2]
      exact mem_normalizer_Qb_of_inv (xp_inv 0 c) fun u hu => x0_conj_Qb c hu)
    (fun c => by
      rw [Subgroup.mem_comap, rhoB_l2]
      exact mem_normalizer_Qb_of_inv (xp_inv 2 c) fun u hu => x2_conj_Qb c hu)
  have : A ∈ (Subgroup.normalizer ((Qb K : Subgroup (adjointGroup .G2 K)) :
      Set (adjointGroup .G2 K))).comap (rhoB K) := hS ▸ Subgroup.mem_top A
  exact this

theorem rhoB_conj_Qb (A : SL2) {u : adjointGroup .G2 K} (hu : u ∈ Qb K) :
    rhoB K A * u * (rhoB K A)⁻¹ ∈ Qb K :=
  (Subgroup.mem_normalizer_iff.1 (range_rhoB_le_normalizer ⟨A, rfl⟩) u).1 hu

theorem mem_PL {g : adjointGroup .G2 K} (hg : g ∈ (rhoB K).range ⊔ Qb K) :
    ∃ A : SL2, ∃ q ∈ Qb K, g = rhoB K A * q := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right (rhoB K).range (Qb K)
    range_rhoB_le_normalizer
  have hg' : g ∈ ((((rhoB K).range ⊔ Qb K : Subgroup (adjointGroup .G2 K))) :
    Set (adjointGroup .G2 K)) := hg
  rw [h, Set.mem_mul] at hg'
  obtain ⟨x, ⟨A, rfl⟩, y, hy, rfl⟩ := hg'
  exact ⟨A, y, hy, rfl⟩

omit [CharP K 2] in
theorem commute_xp_same (p : ℕ) (a b : K) : Commute (xp p a) (xp p b) := by
  show xp p a * xp p b = xp p b * xp p a
  rw [← xp_add, ← xp_add, add_comm]

theorem commute_gen_dv {p : ℕ} (hp : p ∈ qbList) (c a b : K) : Commute (xp p c) (dv a b) := by
  unfold dv
  apply Commute.mul_right
  · rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
    · exact commute_17 c a
    · exact commute_47 c a
    · exact commute_87 c a
    · exact commute_37 c a
    · exact commute_xp_same 7 c a
  · rcases mem_qbList hp with rfl | rfl | rfl | rfl | rfl
    · exact commute_13 c b
    · exact commute_43 c b
    · exact commute_83 c b
    · exact commute_xp_same 3 c b
    · exact (commute_37 b c).symm

theorem Qb_commute_dv {q : adjointGroup .G2 K} (hq : q ∈ Qb K) (a b : K) :
    q * dv a b = dv a b * q := by
  have hle : Qb K ≤ Subgroup.centralizer ({dv a b} : Set (adjointGroup .G2 K)) := by
    refine iSup₂_le fun p hp y hy => ?_
    obtain ⟨c, rfl⟩ := (mem_Xp_iff (lt_twelve_of_mem_qbList hp) y).1 hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (commute_gen_dv hp c a b).symm.eq
  have := Subgroup.mem_centralizer_iff.1 (hle hq) (dv a b) (Set.mem_singleton _)
  exact this.symm

theorem Qb_conj_dvv {q : adjointGroup .G2 K} (hq : q ∈ Qb K) (v : Fin 2 → K) :
    q * dvv v * q⁻¹ = dvv v := by
  rw [dvv, Qb_commute_dv hq]
  group

theorem ActsAs.mul_Qb {g q : adjointGroup .G2 K} {A : SL2} (hg : ActsAs g A) (hq : q ∈ Qb K) :
    ActsAs (g * q) A := fun v => by
  rw [show g * q * dvv v * (g * q)⁻¹ = g * (q * dvv v * q⁻¹) * g⁻¹ by group, Qb_conj_dvv hq,
    hg v]

end CFSG.RankThree.PartOne.SEITZ2
