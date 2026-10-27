module

public import CFSG.Walter.J1Props.Facts
public import CFSG.Walter.W67.CentralExt

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1Recog CFSG.Open Word
open scoped Pointwise

section Central

variable {E : Type*} [Group E]

theorem isMulCommutative_of_map_cyclic {G : Type*} [Group G] (π : E →* G)
    (hZ : π.ker ≤ Subgroup.center E) (P : Subgroup E) (hc : IsCyclic (P.map π)) :
    IsMulCommutative P := by
  obtain ⟨⟨_, g, hg, rfl⟩, hgen⟩ := hc.exists_generator
  have hform : ∀ a ∈ P, ∃ (k : ℤ) (z : E), z ∈ π.ker ∧ a = z * g ^ k := by
    intro a ha
    obtain ⟨k, hk⟩ := hgen ⟨π a, a, ha, rfl⟩
    refine ⟨k, a * (g ^ k)⁻¹, ?_, by group⟩
    have hk' : π g ^ k = π a := congrArg Subtype.val hk
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk', mul_inv_cancel]
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨i, z, hz, ha⟩ := hform a a.2
  obtain ⟨j, w, hw, hb⟩ := hform b b.2
  have hzc := Subgroup.mem_center_iff.mp (hZ hz)
  have hwc := Subgroup.mem_center_iff.mp (hZ hw)
  change (a : E) * b = b * a
  rw [ha, hb]
  calc z * g ^ i * (w * g ^ j) = z * (g ^ i * w) * g ^ j := by group
    _ = z * (w * g ^ i) * g ^ j := by rw [hwc]
    _ = z * w * (g ^ i * g ^ j) := by group
    _ = w * z * (g ^ i * g ^ j) := by rw [← hzc w]
    _ = w * z * (g ^ j * g ^ i) := by rw [← zpow_add, ← zpow_add, add_comm]
    _ = w * (z * g ^ j) * g ^ i := by group
    _ = w * (g ^ j * z) * g ^ i := by rw [← hzc (g ^ j)]
    _ = w * g ^ j * (z * g ^ i) := by group

@[expose] def comm (x y : E) : E := x * y * x⁻¹ * y⁻¹

omit [Group E] in
theorem comm_def [Group E] (x y : E) : comm x y = x * y * x⁻¹ * y⁻¹ := rfl

theorem comm_mul_central_left {x y z : E} (hz : z ∈ Subgroup.center E) :
    comm (x * z) y = comm x y := by
  have hzc := Subgroup.mem_center_iff.mp hz
  rw [comm_def, comm_def, mul_inv_rev]
  calc x * z * y * (z⁻¹ * x⁻¹) * y⁻¹ = x * (z * y) * z⁻¹ * x⁻¹ * y⁻¹ := by group
    _ = x * (y * z) * z⁻¹ * x⁻¹ * y⁻¹ := by rw [hzc]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_mul_central_right {x y z : E} (hz : z ∈ Subgroup.center E) :
    comm x (y * z) = comm x y := by
  have hzc := Subgroup.mem_center_iff.mp hz
  rw [comm_def, comm_def, mul_inv_rev]
  calc x * (y * z) * x⁻¹ * (z⁻¹ * y⁻¹) = x * y * (z * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z) * z⁻¹ * y⁻¹ := by rw [hzc]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_conj {x y v : E} (h : comm x y ∈ Subgroup.center E) :
    comm (v⁻¹ * x * v) (v⁻¹ * y * v) = comm x y := by
  have hc := Subgroup.mem_center_iff.mp h
  calc comm (v⁻¹ * x * v) (v⁻¹ * y * v) = v⁻¹ * comm x y * v := by simp only [comm_def]; group
    _ = comm x y * v⁻¹ * v := by rw [hc v⁻¹]
    _ = comm x y := by group

theorem comm_swap (x y : E) : comm y x = (comm x y)⁻¹ := by
  rw [comm_def, comm_def]
  group

theorem comm_self (x : E) : comm x x = 1 := by
  rw [comm_def]
  group

theorem comm_mul_right {x y w : E} (h : comm x w ∈ Subgroup.center E) :
    comm x (y * w) = comm x y * comm x w := by
  have hc := Subgroup.mem_center_iff.mp h
  calc comm x (y * w) = comm x y * (y * comm x w * y⁻¹) := by simp only [comm_def]; group
    _ = comm x y * (comm x w * y * y⁻¹) := by rw [hc y]
    _ = comm x y * comm x w := by group

theorem commute_of_lift {Z : Subgroup E} (hZ : Z ≤ Subgroup.center E) {a₁ a₂ a₃ v : E}
    (h12 : comm a₁ a₂ ∈ Z) (h13 : comm a₁ a₃ ∈ Z) (h23 : comm a₂ a₃ ∈ Z)
    (hv1 : a₂⁻¹ * (v⁻¹ * a₁ * v) ∈ Z) (hv2 : a₃⁻¹ * (v⁻¹ * a₂ * v) ∈ Z)
    (hv3 : (a₁ * a₃)⁻¹ * (v⁻¹ * a₃ * v) ∈ Z) :
    a₁ * a₂ = a₂ * a₁ ∧ a₁ * a₃ = a₃ * a₁ ∧ a₂ * a₃ = a₃ * a₂ := by
  have e1 : v⁻¹ * a₁ * v = a₂ * (a₂⁻¹ * (v⁻¹ * a₁ * v)) := by group
  have e2 : v⁻¹ * a₂ * v = a₃ * (a₃⁻¹ * (v⁻¹ * a₂ * v)) := by group
  have e3 : v⁻¹ * a₃ * v = a₁ * a₃ * ((a₁ * a₃)⁻¹ * (v⁻¹ * a₃ * v)) := by group
  have k12 : comm a₁ a₂ = comm a₂ a₃ := by
    rw [← comm_conj (v := v) (hZ h12), e1, e2, comm_mul_central_left (hZ hv1),
      comm_mul_central_right (hZ hv2)]
  have k13 : comm a₁ a₃ = 1 := by
    have h21 : comm a₂ a₁ ∈ Subgroup.center E := by
      rw [comm_swap]
      exact Subgroup.inv_mem _ (hZ h12)
    rw [← comm_conj (v := v) (hZ h13), e1, e3, comm_mul_central_left (hZ hv1),
      comm_mul_central_right (hZ hv3), comm_mul_right (hZ h23), comm_swap, k12,
      inv_mul_cancel]
  have k23 : comm a₂ a₃ = 1 := by
    have h33 : comm a₃ a₃ ∈ Subgroup.center E := by
      rw [comm_self]
      exact Subgroup.one_mem _
    rw [← comm_conj (v := v) (hZ h23), e2, e3, comm_mul_central_left (hZ hv2),
      comm_mul_central_right (hZ hv3), comm_mul_right h33, comm_self, mul_one, comm_swap, k13,
      inv_one]
  have hc : ∀ x y : E, comm x y = 1 → x * y = y * x := fun x y h => by
    rw [comm_def] at h
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h, one_mul]
  exact ⟨hc _ _ (k12.trans k23), hc _ _ k13, hc _ _ k23⟩

end Central

noncomputable abbrev t2J : walterJ1 := elt (Word.conj wt wn)

noncomputable abbrev t3J : walterJ1 := elt (Word.conj wt (Word.pow wn 2))

theorem rels_S : tJ * t2J = t2J * tJ ∧ tJ * t3J = t3J * tJ ∧ t2J * t3J = t3J * t2J ∧
    nJ⁻¹ * tJ * nJ = t2J ∧ nJ⁻¹ * t2J * nJ = t3J ∧ nJ⁻¹ * t3J * nJ = tJ * t3J ∧
    xJ = tJ * t2J ∧ x'J = tJ * t3J := by
  simp only [← elt_inv, ← elt_append, elt_eq_elt_iff]
  decide +kernel

noncomputable abbrev S₀ : Subgroup walterJ1 :=
  Subgroup.zpowers tJ ⊔ GorensteinWalter.kleinFourOfCommutingInvolutions xJ x'J
    rels_F.1 rels_F.2.1 rels_F.2.2.2.1

theorem card_S₀ : Nat.card S₀ = 8 := by
  obtain ⟨n1, n2, n3, -⟩ := ne_one_F
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions xJ x'J rels_F.1 rels_F.2.1
    rels_F.2.2.2.1
  have hV : Nat.card V = 4 := (GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    xJ x'J rels_F.1 rels_F.2.1 n1 n2 n3 rels_F.2.2.2.1).card_four
  have hVF : V ≤ FJ := by
    intro y hy
    change y ∈ ({xJ * x'J, xJ, x'J, 1} : Set walterJ1) at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact FJ.mul_mem mem_F.1 mem_F.2.1
    · exact mem_F.1
    · exact mem_F.2.1
    · exact FJ.one_mem
  show Nat.card ↥(Subgroup.zpowers tJ ⊔ V) = 8
  rw [sup_comm, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ ?_ ?_, hV,
    Nat.card_zpowers, orderOf_tJ]
  · rw [Subgroup.zpowers_le]
    refine J1.mem_normalizer_of_conj_mem fun y hy => ?_
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (F_le_centralizer (hVF hy)),
      mul_inv_cancel_right]
    exact hy
  · rw [Subgroup.disjoint_def]
    intro y hyV hy
    rcases (J1.mem_zpowers_of_orderOf_eq_two orderOf_tJ).mp hy with rfl | rfl
    · rfl
    · exact absurd (hVF hyV) tJ_not_mem_F

theorem isPGroup_S₀ : IsPGroup 2 S₀ := IsPGroup.of_card (n := 3) (by rw [card_S₀]; norm_num)

theorem not_two_dvd_index_S₀ : ¬ 2 ∣ S₀.index := by
  have := S₀.card_mul_index
  rw [card_S₀, card_walterJ1] at this
  omega

noncomputable abbrev sylowS₀ : Sylow 2 walterJ1 := isPGroup_S₀.toSylow not_two_dvd_index_S₀

theorem S₀_le_closure : S₀ ≤ Subgroup.closure {tJ, t2J, t3J} := by
  obtain ⟨-, -, -, -, -, -, hx, hx'⟩ := rels_S
  have h1 : tJ ∈ Subgroup.closure {tJ, t2J, t3J} := Subgroup.subset_closure (by simp)
  have h2 : t2J ∈ Subgroup.closure {tJ, t2J, t3J} := Subgroup.subset_closure (by simp)
  have h3 : t3J ∈ Subgroup.closure {tJ, t2J, t3J} := Subgroup.subset_closure (by simp)
  have hx1 : xJ ∈ Subgroup.closure {tJ, t2J, t3J} := hx ▸ Subgroup.mul_mem _ h1 h2
  have hx2 : x'J ∈ Subgroup.closure {tJ, t2J, t3J} := hx' ▸ Subgroup.mul_mem _ h1 h3
  refine sup_le (Subgroup.zpowers_le.mpr h1) ?_
  intro y hy
  change y ∈ ({xJ * x'J, xJ, x'J, 1} : Set walterJ1) at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact Subgroup.mul_mem _ hx1 hx2
  · exact hx1
  · exact hx2
  · exact Subgroup.one_mem _

theorem exists_sylow_two_isMulCommutative {E : Type*} [Group E] [Finite E] (π : E →* walterJ1)
    (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center E) :
    ∃ Q : Sylow 2 E, IsMulCommutative (Q : Subgroup E) := by
  obtain ⟨c12, c13, c23, hn1, hn2, hn3, -, -⟩ := rels_S
  obtain ⟨a₁, ha₁⟩ := hπ tJ
  obtain ⟨a₂, ha₂⟩ := hπ t2J
  obtain ⟨a₃, ha₃⟩ := hπ t3J
  obtain ⟨v, hv⟩ := hπ nJ
  have hcomm : ∀ {x y : E} {x' y' : walterJ1}, π x = x' → π y = y' → x' * y' = y' * x' →
      comm x y ∈ π.ker := by
    intro x y x' y' hx hy hxy
    rw [MonoidHom.mem_ker, comm_def, map_mul, map_mul, map_mul, map_inv, map_inv, hx, hy, hxy]
    group
  obtain ⟨k12, k13, k23⟩ := commute_of_lift (v := v) hZ (hcomm ha₁ ha₂ c12) (hcomm ha₁ ha₃ c13)
    (hcomm ha₂ ha₃ c23)
    (by rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ha₁, ha₂, hv, hn1,
      inv_mul_cancel])
    (by rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ha₂, ha₃, hv, hn2,
      inv_mul_cancel])
    (by rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, ha₁, ha₃,
      hv, hn3, inv_mul_cancel])
  set K := Subgroup.closure ({a₁, a₂, a₃} ∪ (π.ker : Set E)) with hK
  have hKc : IsMulCommutative K := by
    apply Subgroup.isMulCommutative_closure
    have hz : ∀ z ∈ (π.ker : Set E), ∀ y : E, Commute z y := fun z hz y =>
      (Subgroup.mem_center_iff.mp (hZ hz) y).symm
    rintro x hx y hy -
    rcases hx with (rfl | rfl | rfl) | hx
    · rcases hy with (rfl | rfl | rfl) | hy
      · exact Commute.refl _
      · exact k12
      · exact k13
      · exact (hz y hy x).symm
    · rcases hy with (rfl | rfl | rfl) | hy
      · exact k12.symm
      · exact Commute.refl _
      · exact k23
      · exact (hz y hy x).symm
    · rcases hy with (rfl | rfl | rfl) | hy
      · exact k13.symm
      · exact k23.symm
      · exact Commute.refl _
      · exact (hz y hy x).symm
    · exact hz x hx y
  have hpre : ∀ w : E, π w ∈ S₀ → w ∈ K := by
    intro w hw
    have hmap : Subgroup.closure ({tJ, t2J, t3J} : Set walterJ1) =
        (Subgroup.closure ({a₁, a₂, a₃} : Set E)).map π := by
      rw [MonoidHom.map_closure]
      congr 1
      simp [Set.image_insert_eq, ha₁, ha₂, ha₃]
    obtain ⟨k, hk, hkw⟩ := (hmap ▸ S₀_le_closure hw : π w ∈ _)
    have hkK : k ∈ K := Subgroup.closure_mono Set.subset_union_left hk
    have hker : k⁻¹ * w ∈ K := Subgroup.subset_closure (Or.inr (by
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hkw, inv_mul_cancel]))
    have : w = k * (k⁻¹ * w) := by group
    rw [this]
    exact K.mul_mem hkK hker
  obtain ⟨Q⟩ : Nonempty (Sylow 2 E) := inferInstance
  obtain ⟨S', hS'⟩ := (Q.isPGroup'.map π).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq walterJ1 S' sylowS₀
  obtain ⟨ĝ, hĝ⟩ := hπ g
  refine ⟨ĝ • Q, ⟨⟨fun a b => Subtype.ext ?_⟩⟩⟩
  have hmem : ∀ q ∈ ((ĝ • Q : Sylow 2 E) : Subgroup E), q ∈ K := by
    intro q hq
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hq
    apply hpre
    have h1 : π (ĝ⁻¹ * q * ĝ) ∈ (S' : Subgroup walterJ1) := hS' ⟨_, hq, rfl⟩
    have h2 : g * π (ĝ⁻¹ * q * ĝ) * g⁻¹ ∈ ((g • S' : Sylow 2 walterJ1) : Subgroup walterJ1) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_inv_apply]
      convert h1 using 1
      group
    rw [hg] at h2
    have h3 : g * π (ĝ⁻¹ * q * ĝ) * g⁻¹ = π q := by
      rw [map_mul, map_mul, map_inv, hĝ]
      group
    rw [h3] at h2
    exact h2
  have := congrArg Subtype.val (hKc.is_comm.comm ⟨a, hmem a a.2⟩ ⟨b, hmem b b.2⟩)
  change (a : E) * b = b * a
  exact this

theorem isCyclic_of_isPGroup {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {H : Subgroup walterJ1}
    (hH : IsPGroup p H) : IsCyclic H := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hdvd : p ^ k ∣ 175560 := hk ▸ card_walterJ1 ▸ Subgroup.card_subgroup_dvd_card H
  have hk1 : k ≤ 1 := by
    by_contra h
    have hp2d : p ^ 2 ∣ 175560 := (pow_dvd_pow p (by omega)).trans hdvd
    have hpd : p ∣ 175560 := (dvd_pow_self p two_ne_zero).trans hp2d
    rcases prime_dvd_card hp.out hpd with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp2 rfl
    all_goals norm_num at hp2d
  interval_cases k
  · rw [pow_zero] at hk
    have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hk).1
    exact isCyclic_of_subsingleton
  · rw [pow_one] at hk
    exact isCyclic_of_prime_card hk

theorem J3_multiplier {E : Type*} [Group E] [Finite E] (π : E →* walterJ1)
    (hπ : Function.Surjective π) (hZ : π.ker ≤ Subgroup.center E) (hE : commutator E = ⊤) :
    π.ker = ⊥ := by
  have h := W67.inf_commutator_eq_bot hZ (fun p hp _ => ?_)
  · rwa [hE, inf_top_eq] at h
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨this, ?_⟩
  by_cases hp2 : p = 2
  · subst hp2
    exact exists_sylow_two_isMulCommutative π hπ hZ
  · obtain ⟨P⟩ : Nonempty (Sylow p E) := inferInstance
    exact ⟨P, isMulCommutative_of_map_cyclic π hZ P
      (isCyclic_of_isPGroup hp2 (P.isPGroup'.map π))⟩

end CFSG.Walter.J1Props
