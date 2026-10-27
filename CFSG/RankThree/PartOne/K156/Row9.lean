module

public import CFSG.RankThree.PartOne.K159G.PlaneGen
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KF.U4Final

public section

namespace CFSG.RankThree.PartOne.K156

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.Sec12Three CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

theorem exists_u4Ctx (hZ : PSUFourEvenCenterTrivial) {G : Type} [Group G] [Finite G] {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ} (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hpq : p ∣ 2 ^ f + 1)
    (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 f)
    (hE4 : Nat.card E = p ^ 4) :
    ∃ (K : Type) (_ : Field K), Nonempty (U4Ctx p A c L E f K) := by
  have h3 := h.three_lt
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 ∨ f = 0 := by omega
    have h0 : p ∣ 3 ∨ p ∣ 2 := by
      rcases hf1 with rfl | rfl
      · exact Or.inl (by simpa using hpq)
      · exact Or.inr (by simpa using hpq)
    rcases h0 with h0 | h0
    · have := Nat.le_of_dvd (by norm_num) h0
      omega
    · have := Nat.le_of_dvd (by norm_num) h0
      omega
  have hqs : CFSG.IsQuasisimple L :=
    hF.two.elim (fun hG => hG.quasisimple) (fun hS => hS.quasisimple)
  have hZL : Subgroup.center L = ⊥ := hZ L f hf2 hqs hmodel
  have hG : Sec12TwoGeneric p c L E := by
    rcases hF.two with hG | hS
    · exact hG
    · exfalso
      have h5 := hS.center_card
      rw [hZL] at h5
      simp at h5
  have hcomm : ∀ l ∈ L, c * l = l * c := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      ((mem_thetaComponentsAt_iff.mp h.L_mem.2).1 hl)).symm
  have hcL : c ∉ L := by
    intro hcL
    have hc1 : (⟨c, hcL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2).symm
    rw [hZL, Subgroup.mem_bot] at hc1
    exact h.c_ne_one (congrArg Subtype.val hc1)
  have R : Restr c L E (E ⊓ L) := ⟨rfl, hG.E_eq, hcomm⟩
  have hcp : c ^ p = 1 := by
    have := h.A_elem
    exact elemPow_eq_one_of_isElementaryAbelian c h.c_mem
  have hco : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hFcard : Nat.card (E ⊓ L : Subgroup G) = p ^ 3 := by
    have h1 := R.card_E hp hco hcL
    rw [hE4] at h1
    have h2 : p ^ 3 * p = p ^ 4 := by ring
    exact mul_right_cancel₀ hp.ne_zero (h1.symm.trans h2.symm)
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hFexp : ∀ x ∈ (E ⊓ L).subgroupOf L, x ^ p = 1 := by
    intro x hx
    have hxE : (x : G) ∈ E := (Subgroup.mem_inf.mp hx).1
    apply Subtype.ext
    have := h.E_elem
    simpa using elemPow_eq_one_of_isElementaryAbelian (x : G) hxE
  have hFcomm : ∀ x ∈ (E ⊓ L).subgroupOf L, ∀ y ∈ (E ⊓ L).subgroupOf L, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val (h.E_elem.is_comm.comm ⟨(x : G), (Subgroup.mem_inf.mp hx).1⟩
      ⟨(y : G), (Subgroup.mem_inf.mp hy).1⟩)
  have hFcard' : Nat.card ((E ⊓ L).subgroupOf L) = p ^ 3 := by
    rw [← hFcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  obtain ⟨ψ, hψ⟩ := exists_diag_iso (K := K) (by omega) hK hp hpq hZL e _ hFexp hFcomm hFcard'
  exact ⟨K, hKf, ⟨⟨h, hE4, R, hcL, hU, hf2, hpq, ψ, fun g => by
    have h1 := hψ g
    rw [Subgroup.mem_subgroupOf] at h1
    rw [← h1]
    exact ⟨fun hx => Subgroup.mem_inf.mpr ⟨hx, (ψ g).2⟩, fun hx => (Subgroup.mem_inf.mp hx).1⟩⟩⟩⟩

theorem mul_inv_mul_aux {M : Type*} [CommGroup M] (φ : M ≃* M) (a b : M) :
    φ (a * b) * (a * b)⁻¹ = (φ a * a⁻¹) * (φ b * b⁻¹) := by
  rw [map_mul, mul_inv_rev]
  simp only [mul_assoc, mul_comm, mul_left_comm]

section Gen

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] (C : U4Ctx p A c L E f K)

include C in
theorem exists_permData_of_mem {y : MulAut E} (hy : y ∈ torusImage E L) :
    ∃ P : C.PermData, P.t = y := by
  obtain ⟨w, hwL, hwE, rfl⟩ := mem_torusImage_iff.mp hy
  obtain ⟨g, τ, hg, hτ⟩ := C.exists_perm hwL hwE
  subst hg
  exact ⟨⟨g, τ, hτ, hwE⟩, rfl⟩

include C in
theorem exists_permData_tau (hcard : Nat.card (torusImage E L) = 24) (σ : Equiv.Perm (Fin 4)) :
    ∃ P : C.PermData, P.τ = σ := by
  classical
  let F : ↥(torusImage E L) → Equiv.Perm (Fin 4) := fun y =>
    (Classical.choose (exists_permData_of_mem C y.2)).τ
  have hinj : Function.Injective F := by
    intro y₁ y₂ h12
    have h1 := Classical.choose_spec (exists_permData_of_mem C y₁.2)
    have h2 := Classical.choose_spec (exists_permData_of_mem C y₂.2)
    apply Subtype.ext
    rw [← h1, ← h2]
    exact (U4Ctx.PermData.t_eq_iff C _ _).2 h12
  have hcard' : Nat.card (Equiv.Perm (Fin 4)) ≤ Nat.card ↥(torusImage E L) := by
    rw [hcard, Nat.card_perm, Nat.card_fin]
    decide
  obtain ⟨y, hy⟩ := (hinj.bijective_of_nat_card_le hcard').2 σ
  exact ⟨Classical.choose (exists_permData_of_mem C y.2), hy⟩

include C in
theorem card_autMoved_refl (R : C.Refl) : Nat.card (autMoved E R.t) = p := by
  have hp := C.h.prime
  have hEel : IsElementaryAbelian p ↥E := C.h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  let _ : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := hEc }
  obtain ⟨ζ, hζ⟩ := C.exists_unit_root
  have hzeE : C.phi (R.zElt hζ) ∈ E := R.phi_zElt_mem_E hζ
  set z' : ↥E := ⟨C.phi (R.zElt hζ), hzeE⟩ with hz'
  set m : ↥E := R.t z' * z'⁻¹ with hm
  have hEp : ∀ e : ↥E, e ^ p = 1 := fun e => Subtype.ext (by
    simpa using elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (e : G) e.2)
  have hmp : m ^ p = 1 := hEp m
  have hle : autMoved E R.t ≤ Subgroup.zpowers m := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨e, rfl⟩
    obtain ⟨u, hu, i, hui⟩ := R.exists_decomp_fixed hζ e.2
    obtain ⟨u', hu'fix, hu'⟩ := Subgroup.mem_map.1 hu
    have hu'fix' : R.t u' = u' := hu'fix
    have hee : e = u' * z' ^ i := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow, hz']
      rw [hui, ← hu']
      rfl)
    have hmi : R.t e * e⁻¹ = m ^ i := by
      rw [hee, mul_inv_mul_aux (R.t : ↥E ≃* ↥E) u' (z' ^ i), hu'fix', mul_inv_cancel, one_mul,
        map_zpow, hm, mul_zpow, inv_zpow', zpow_neg]
    show R.t e * e⁻¹ ∈ Subgroup.zpowers m
    rw [hmi]
    exact Subgroup.zpow_mem_zpowers m i
  have hdvd : Nat.card (autMoved E R.t) ∣ p := by
    refine (Subgroup.card_dvd_of_le hle).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hmp
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exfalso
    have hbot : autMoved E R.t = ⊥ := Subgroup.card_eq_one.1 h1
    have ht1 : R.t = 1 := by
      refine MulEquiv.ext fun e => ?_
      have h2 : R.t e * e⁻¹ ∈ autMoved E R.t := Subgroup.subset_closure ⟨e, rfl⟩
      rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h2
      simpa using h2
    have hord : orderOf R.t = 2 := by
      have h2 : orderOf R.t = orderOf R.toPermData.τ := R.toPermData.orderOf_t
      rw [h2, R.hτ']
      exact Equiv.Perm.IsSwap.orderOf ⟨R.a, R.b, R.hab, rfl⟩
    rw [ht1, orderOf_one] at hord
    omega
  · exact h1

include C in
theorem isAutReflection_of_refl (R : C.Refl) : IsAutReflection p E R.t := by
  refine ⟨?_, card_autMoved_refl C R⟩
  have h2 : orderOf R.t = orderOf R.toPermData.τ := R.toPermData.orderOf_t
  rw [h2, R.hτ']
  exact Equiv.Perm.IsSwap.orderOf ⟨R.a, R.b, R.hab, rfl⟩

include C in
theorem blkG_le_lieGenerated (hL : L ∈ thetaCompZeroStarE p E)
    (hcard : Nat.card (torusImage E L) = 24) {a b : Fin 4} (hab : a ≠ b) :
    C.blkG hab ≤ lieGenerated p E := by
  obtain ⟨P, hP⟩ := exists_permData_tau C hcard (Equiv.swap a b)
  let R : C.Refl := ⟨P, a, b, hab, hP⟩
  have htD : R.t ∈ reflectionSet p E :=
    ⟨isAutReflection_of_refl C R, L, hL,
      mem_torusImage_iff.mpr ⟨R.w, R.w_mem_L, R.hwE, rfl⟩⟩
  obtain ⟨hqs, hz, -⟩ := blk_model C.hU C.hf2 hab
  have hK : kZero p E R.t = C.blkG hab := R.kZero_eq_blkG hqs hz
  have hne := (C.refl_conclusions R).1
  have hIKt : IsKt p E R.t (kZero p E R.t) := ⟨fun f hf => absurd ⟨f, hf⟩ hne, fun _ => rfl⟩
  rw [← hK]
  exact le_sSup ⟨R.t, htD, hIKt⟩

include C in
theorem le_lieGenerated_of_u4Ctx (hL : L ∈ thetaCompZeroStarE p E)
    (hcard : Nat.card (torusImage E L) = 24) : L ≤ lieGenerated p E := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) C.hf2
  intro l hl
  obtain ⟨g, rfl⟩ := C.exists_phi_eq hl
  have hgp : (g : GL (Fin 4) K) ∈ K159G.planeGen C.hU Finset.univ :=
    K159G.mem_planeGen_of_fixOut (h := C.hU) (n := 4) hq 4 Finset.univ (by simp) g g.2
      (fun i hi => absurd (Finset.mem_univ i) hi)
  have key := K159G.planeGen_induction (h := C.hU)
    (C := fun x : GL (Fin 4) K => ∃ hx : x ∈ unitarySU 2 f K 4,
      C.phi ⟨x, hx⟩ ∈ lieGenerated p E) (B := Finset.univ) ?_ ?_ ?_ hgp
  · obtain ⟨hx, hmem⟩ := key
    exact hmem
  · intro i _ j _ hij x hx
    refine ⟨blk_le_unitarySU hij hx, ?_⟩
    exact blkG_le_lieGenerated C hL hcard hij ⟨⟨x, blk_le_unitarySU hij hx⟩,
      Subgroup.mem_subgroupOf.2 hx, rfl⟩
  · refine ⟨one_mem _, ?_⟩
    have : (⟨1, one_mem _⟩ : unitarySU 2 f K 4) = 1 := rfl
    rw [this, map_one]
    exact one_mem _
  · rintro a b ⟨ha, hIa⟩ ⟨hb, hIb⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have : (⟨a * b, mul_mem ha hb⟩ : unitarySU 2 f K 4) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul]
    exact mul_mem hIa hIb

end Gen

theorem row9_le (hZ : PSUFourEvenCenterTrivial) {G : Type} [Group G] [Finite G] {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hE4 : Nat.card E = p ^ 4) (hrow : RowModel p L 9)
    (hcard : Nat.card (torusImage E L) = 24) (hL : L ∈ thetaCompZeroStarE p E) :
    L ≤ lieGenerated p E := by
  obtain ⟨f, -, hpq, hmodel⟩ := hrow
  obtain ⟨K, hKf, ⟨C⟩⟩ := exists_u4Ctx hZ h hF hpq hmodel hE4
  exact le_lieGenerated_of_u4Ctx C hL hcard

end CFSG.RankThree.PartOne.K156
