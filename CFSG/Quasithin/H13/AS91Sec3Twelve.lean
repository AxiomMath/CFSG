module

public import CFSG.Quasithin.H13.AS91Sec3TwelveDefs
public import CFSG.Quasithin.H13.AS91Sec3XiKappa
public import Certificates.Certificate89018

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

theorem fix_of_odd_transitive {G α : Type*} [Group G] [MulAction G α] {N S : Subgroup G}
    (hNS : N ≤ S) (hN : IsPGroup 2 N) (hnorm : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) {X : Set α}
    (hX : ∀ s ∈ S, ∀ x ∈ X, s • x ∈ X) {b : α} (hb : b ∈ X)
    (htrans : ∀ y ∈ X, ∃ s ∈ S, s • b = y) (hodd : ¬ 2 ∣ X.ncard) :
    ∀ n ∈ N, ∀ x ∈ X, n • x = x := by
  let P : SubMulAction N α :=
    { carrier := X
      smul_mem' := fun n x hx => by
        rw [Subgroup.smul_def]
        exact hX n (hNS n.2) x hx }
  have hP : ¬ 2 ∣ Nat.card P := by
    have e : Nat.card P = X.ncard := Nat.card_congr (Equiv.refl _)
    rwa [e]
  obtain ⟨z, hz⟩ := hN.nonempty_fixed_point_of_prime_not_dvd_card P hP
  intro n hn x hx
  obtain ⟨s₁, hs₁, hs₁z⟩ := htrans z.1 z.2
  obtain ⟨s₂, hs₂, hs₂x⟩ := htrans x hx
  have hxz : x = (s₂ * s₁⁻¹) • (z : α) := by rw [mul_smul, ← hs₁z, inv_smul_smul, hs₂x]
  have hsS : s₂ * s₁⁻¹ ∈ S := S.mul_mem hs₂ (S.inv_mem hs₁)
  have hconj : (s₂ * s₁⁻¹)⁻¹ * n * (s₂ * s₁⁻¹) ∈ N := by
    simpa using hnorm _ (S.inv_mem hsS) n hn
  have hfix : ((s₂ * s₁⁻¹)⁻¹ * n * (s₂ * s₁⁻¹)) • (z : α) = z := by
    have h := MulAction.mem_fixedPoints.1 hz ⟨_, hconj⟩
    have h' := congrArg Subtype.val h
    rwa [SubMulAction.val_smul, Subgroup.smul_def] at h'
  calc n • x = n • (s₂ * s₁⁻¹) • (z : α) := by rw [← hxz]
    _ = (s₂ * s₁⁻¹) • (((s₂ * s₁⁻¹)⁻¹ * n * (s₂ * s₁⁻¹)) • (z : α)) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
    _ = (s₂ * s₁⁻¹) • (z : α) := by rw [hfix]
    _ = x := hxz.symm

theorem mem_of_fix_of_card_le {G X : Type*} [Group G] [Finite G] [MulAction G X]
    {S N : Subgroup G} (hNS : N ≤ S) {x : X} (hN : ∀ n ∈ N, n • x = x)
    (hcard : Nat.card S ≤ (MulAction.orbit S x).ncard * Nat.card N) :
    ∀ s ∈ S, s • x = x → s ∈ N := by
  have hos : Nat.card (MulAction.orbit S x) * Nat.card (MulAction.stabilizer S x) =
      Nat.card S := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S x)]
  rw [← Nat.card_coe_set_eq] at hcard
  have hpos : 0 < Nat.card (MulAction.orbit S x) := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hcard
    exact absurd hcard (Nat.not_le.2 Nat.card_pos)
  have hle : N.subgroupOf S ≤ MulAction.stabilizer S x := by
    intro s hs
    rw [MulAction.mem_stabilizer_iff]
    exact hN s (Subgroup.mem_subgroupOf.1 hs)
  have hNcard : Nat.card (N.subgroupOf S) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNS).toEquiv
  have hge : Nat.card (MulAction.stabilizer S x) ≤ Nat.card (N.subgroupOf S) := by
    rw [hNcard]
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    rw [hos]
    exact hcard
  have heq := Subgroup.eq_of_le_of_card_ge hle hge
  intro s hs hsx
  have hmem : (⟨s, hs⟩ : S) ∈ MulAction.stabilizer S x := by
    rw [MulAction.mem_stabilizer_iff]
    exact hsx
  rw [← heq] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem smul_one_quotient_iff (N : Subgroup S24) (σ : S24) :
    σ • ((1 : S24) : S24 ⧸ N) = ((1 : S24) : S24 ⧸ N) ↔ σ ∈ N := by
  rw [← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]

@[expose] def tPerm0 : Equiv.Perm (Fin 24) where
  toFun := ![5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15, 21, 20, 23, 22, 17, 16, 19, 18]
  invFun := ![5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11, 12, 13, 14, 15, 21, 20, 23, 22, 17, 16, 19, 18]
  left_inv := by decide
  right_inv := by decide

@[expose] def tPerm1 : Equiv.Perm (Fin 24) where
  toFun := ![3, 2, 1, 0, 7, 6, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15, 19, 18, 17, 16, 23, 22, 21, 20]
  invFun := ![3, 2, 1, 0, 7, 6, 5, 4, 8, 9, 10, 11, 12, 13, 14, 15, 19, 18, 17, 16, 23, 22, 21, 20]
  left_inv := by decide
  right_inv := by decide

@[expose] def tPerm2 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 16, 17, 22, 23, 20, 21]
  invFun := ![2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11, 12, 13, 14, 15, 18, 19, 16, 17, 22, 23, 20, 21]
  left_inv := by decide
  right_inv := by decide

@[expose] def tPerm3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 13, 12, 15, 14, 9, 8, 11, 10, 21, 20, 23, 22, 17, 16, 19, 18]
  left_inv := by decide
  right_inv := by decide

@[expose] def tPerm4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 12, 13, 14, 15, 8, 9, 10, 11, 20, 21, 22, 23, 16, 17, 18, 19]
  left_inv := by decide
  right_inv := by decide

@[expose] def tPerm5 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9, 14, 15, 12, 13, 18, 19, 16, 17, 22, 23, 20, 21]
  left_inv := by decide
  right_inv := by decide

@[expose] def tPerm : Fin 6 → Equiv.Perm (Fin 24) :=
  ![tPerm0, tPerm1, tPerm2, tPerm3, tPerm4, tPerm5]

theorem repT_tPerm (j : Fin 6) : RepT (Native.tTabs.getD j #[]) (tPerm j) := by
  revert j
  unfold RepT
  decide +kernel

theorem tTabs_getD_mem (j : Fin 6) : Native.tTabs.getD j #[] ∈ Native.tTabs := by
  revert j
  decide +kernel

private theorem tPerm_basis :
    ∀ (j : Fin 6) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(tPerm j) ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem tPerm_basis' :
    ∀ (j : Fin 6) (i : Fin 12), CFSG.Monster.Code.B i ∘ ⇑(tPerm j)⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem tPerm_mem (j : Fin 6) : tPerm j ∈ M24g :=
  CFSG.Monster.Code.mem_AutPerm_of_basis (tPerm_basis j) (tPerm_basis' j)

section Read


theorem trio12Check_true : Native.trio12Check () = true := Certificates.certificate89018

theorem genFix_spec :
    (Native.sextsOfBase ()).length = 7 ∧ ∀ t ∈ Native.tTabs, Native.img t 255 = 255 ∧
      Native.img t 65280 = 65280 ∧ Native.img t 16711680 = 16711680 ∧
      ∀ q ∈ Native.sextsOfBase (),
        Native.imgSext t (Native.sextList ())[q]! = (Native.sextList ())[q]! := by
  have h := trio12Check_true
  simp only [Native.trio12Check, Bool.and_eq_true] at h
  have h1 := h.1.1.1
  simp only [Native.genFixCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h1
  refine ⟨h1.1, fun t ht => ?_⟩
  obtain ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩ := h1.2 t ht
  exact ⟨e1, e2, e3, e4⟩

theorem baseSext_spec : ∀ U ∈ [Native.baseSext, Native.sextU2, Native.sextU3],
    Native.trioIn Native.baseTrio U = true ∧ Native.sextIdx U < 1771 := by
  have h := trio12Check_true
  simp only [Native.trio12Check, Bool.and_eq_true] at h
  have h1 := h.1.1.2
  simp only [Native.baseSextCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1

theorem trioOrbit_spec {p : ℕ} (hp : p < 3795)
    (hz : ¬ 1 < Native.zc (Native.trioList ())[0]! (Native.trioList ())[p]!) :
    (Native.orbitFive (Native.trioSteps Native.tTabs) p).length = 5 ∧
      (Native.orbitFive (Native.trioSteps Native.tTabs) p).Nodup ∧
      (∀ q ∈ Native.orbitFive (Native.trioSteps Native.tTabs) p, q < 3795) ∧
      Native.reachOK 3795 (Native.trioSteps Native.tTabs) p
        (Native.orbitFive (Native.trioSteps Native.tTabs) p) = true := by
  have h := trio12Check_true
  simp only [Native.trio12Check, Bool.and_eq_true] at h
  have h1 := h.1.2
  simp only [Native.trioOrbitCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1
  rcases h1 p hp with h2 | ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩
  · exact absurd h2 hz
  · exact ⟨h3, h4, h5, h6⟩

theorem tupOrbit_spec :
    Native.x0Code () < Native.nTup ∧
      1008 ≤ (Native.orbitTup (Native.tupSteps Native.lTabs) (Native.x0Code ())).length ∧
      (Native.orbitTup (Native.tupSteps Native.lTabs) (Native.x0Code ())).Nodup ∧
      (∀ q ∈ Native.orbitTup (Native.tupSteps Native.lTabs) (Native.x0Code ()),
        q < Native.nTup) ∧
      Native.reachOK Native.nTup (Native.tupSteps Native.lTabs) (Native.x0Code ())
        (Native.orbitTup (Native.tupSteps Native.lTabs) (Native.x0Code ())) = true := by
  have h := trio12Check_true
  simp only [Native.trio12Check, Bool.and_eq_true] at h
  have h1 := h.2
  simp only [Native.tupOrbitCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
  obtain ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩ := h1
  exact ⟨e1, e2, e3, e4, e5⟩

end Read

@[expose] def StabTrio0 : Subgroup S24 := M24g ⊓ MulAction.stabilizer S24 (trioFin 0)

theorem mem_StabTrio0 {σ : S24} : σ ∈ StabTrio0 ↔ σ ∈ M24g ∧ σ • trioFin 0 = trioFin 0 := by
  rw [StabTrio0, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]

structure IsBaseNormal (N : Subgroup S24) : Prop where
  le : N ≤ M24g
  fix : ∀ σ ∈ N, σ • trioFin 0 = trioFin 0
  norm : ∀ σ ∈ M24g, σ • trioFin 0 = trioFin 0 → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N
  card : Nat.card N = 64

theorem IsBaseNormal.le_stab {N : Subgroup S24} (hN : IsBaseNormal N) : N ≤ StabTrio0 :=
  fun n hn => mem_StabTrio0.2 ⟨hN.le hn, hN.fix n hn⟩

theorem IsBaseNormal.norm_stab {N : Subgroup S24} (hN : IsBaseNormal N) :
    ∀ s ∈ StabTrio0, ∀ n ∈ N, s * n * s⁻¹ ∈ N :=
  fun s hs n hn => hN.norm s (mem_StabTrio0.1 hs).1 (mem_StabTrio0.1 hs).2 n hn

theorem IsBaseNormal.isPGroup {N : Subgroup S24} (hN : IsBaseNormal N) : IsPGroup 2 N :=
  IsPGroup.of_card (n := 6) (by rw [hN.card]; norm_num)

abbrev Tup5 : Type :=
  Finset (Fin 24) × Finset (Fin 24) × Finset (Finset (Fin 24)) × Finset (Finset (Fin 24)) ×
    Finset (Finset (Fin 24))

@[expose] def tupFin (c : ℕ) : Tup5 :=
  (octFin (c % 759), octFin (c / 759 % 759), sextFin (c / 759 / 759 % 1771),
    sextFin (c / 759 / 759 / 1771 % 1771), sextFin (c / 759 / 759 / 1771 / 1771 % 1771))

theorem tupFin_encTup {a b u v w : ℕ} (ha : a < 759) (hb : b < 759) (hu : u < 1771)
    (hv : v < 1771) (hw : w < 1771) :
    tupFin (Native.encTup a b u v w) = (octFin a, octFin b, sextFin u, sextFin v, sextFin w) := by
  have e1 : Native.encTup a b u v w % 759 = a := by unfold Native.encTup; omega
  have e2 : Native.encTup a b u v w / 759 % 759 = b := by unfold Native.encTup; omega
  have e3 : Native.encTup a b u v w / 759 / 759 % 1771 = u := by unfold Native.encTup; omega
  have e4 : Native.encTup a b u v w / 759 / 759 / 1771 % 1771 = v := by
    unfold Native.encTup; omega
  have e5 : Native.encTup a b u v w / 759 / 759 / 1771 / 1771 % 1771 = w := by
    unfold Native.encTup; omega
  simp only [tupFin, e1, e2, e3, e4, e5]

section Base


theorem trioFin_zero_eq : trioFin 0 = {maskFin 255, maskFin 65280, maskFin 16711680} := by
  rw [trioFin, trioList_zero]
  rfl

theorem ncard_orbit_trioFin : (MulAction.orbit ↥M24g (trioFin 0)).ncard = 3795 := by
  have h : MulAction.orbit ↥M24g (trioFin 0) = {t | IsTrio t} := by
    ext t
    rw [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, rfl⟩
      exact (isTrio_smul_iff g.2).2 (isTrio_trioFin (by norm_num))
    · intro ht
      obtain ⟨g, hg, hgt⟩ := trio_transitive ht
      refine ⟨⟨g⁻¹, M24g.inv_mem hg⟩, ?_⟩
      show g⁻¹ • trioFin 0 = t
      rw [← hgt, inv_smul_smul]
  rw [h]
  have key := ncard_eq_length_filter (F := trioFin) (n := 3795)
    (fun p hp p' hp' he => trioFin_injective hp hp' he) (P := IsTrio) isTrio_iff
    (fun _ => true) (Q := fun _ => True) (fun _ _ => by simp)
  simpa using key

theorem card_StabTrio0 : Nat.card StabTrio0 = 64512 := by
  have hos : Nat.card (MulAction.orbit ↥M24g (trioFin 0)) *
      Nat.card (MulAction.stabilizer ↥M24g (trioFin 0)) = Nat.card ↥M24g := by
    rw [← Nat.card_prod,
      Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥M24g (trioFin 0))]
  rw [Nat.card_coe_set_eq, ncard_orbit_trioFin] at hos
  have hG : Nat.card ↥M24g = 244823040 := CFSG.Monster.Code.card_AutPerm
  rw [hG] at hos
  have hst : Nat.card (MulAction.stabilizer ↥M24g (trioFin 0)) = 64512 := by omega
  let e : ↥StabTrio0 ≃ ↥(MulAction.stabilizer ↥M24g (trioFin 0)) :=
    { toFun := fun σ => ⟨⟨σ.1, (mem_StabTrio0.1 σ.2).1⟩, (mem_StabTrio0.1 σ.2).2⟩
      invFun := fun g => ⟨g.1.1, mem_StabTrio0.2 ⟨g.1.2, g.2⟩⟩
      left_inv := fun σ => rfl
      right_inv := fun g => rfl }
  rw [Nat.card_congr e, hst]

theorem imgTrio_lTabs (j : Fin 4) :
    Native.imgTrio (Native.lTabs.getD j #[]) Native.baseTrio = Native.baseTrio := by
  revert j
  decide +kernel

theorem lPerm_fix (j : Fin 4) : lPerm j • trioFin 0 = trioFin 0 := by
  rw [smul_trioFin (repT_lPerm j) (by norm_num : 0 < 3795), trioList_zero, imgTrio_lTabs, trioFin,
    trioList_zero]

theorem lPerm_mem_stab (j : Fin 4) : lPerm j ∈ StabTrio0 :=
  mem_StabTrio0.2 ⟨lPerm_mem j, lPerm_fix j⟩

theorem lPerm_zero_brick1 : lPerm 0 • maskFin 255 = maskFin 65280 := by
  rw [← maskFin_img (repT_lPerm 0) 255]
  have h : Native.img (Native.lTabs.getD ((0 : Fin 4) : ℕ) #[]) 255 = 65280 := by decide +kernel
  rw [h]

theorem lPerm_zero_brick2 : lPerm 0 • maskFin 65280 = maskFin 16711680 := by
  rw [← maskFin_img (repT_lPerm 0) 65280]
  have h : Native.img (Native.lTabs.getD ((0 : Fin 4) : ℕ) #[]) 65280 = 16711680 := by
    decide +kernel
  rw [h]

theorem IsBaseNormal.fix_octad {N : Subgroup S24} (hN : IsBaseNormal N) :
    ∀ n ∈ N, ∀ O ∈ trioFin 0, n • O = O := by
  have hX : ∀ s ∈ StabTrio0, ∀ x ∈ ((trioFin 0 : Finset (Finset (Fin 24))) :
      Set (Finset (Fin 24))), s • x ∈ ((trioFin 0 : Finset (Finset (Fin 24))) :
      Set (Finset (Fin 24))) := by
    intro s hs x hx
    have h := Finset.smul_mem_smul_finset (a := s) hx
    rwa [(mem_StabTrio0.1 hs).2] at h
  have hb : maskFin 255 ∈ ((trioFin 0 : Finset (Finset (Fin 24))) : Set (Finset (Fin 24))) := by
    rw [Finset.mem_coe, trioFin_zero_eq]
    simp
  have htrans : ∀ y ∈ ((trioFin 0 : Finset (Finset (Fin 24))) : Set (Finset (Fin 24))),
      ∃ s ∈ StabTrio0, s • maskFin 255 = y := by
    intro y hy
    rw [Finset.mem_coe, trioFin_zero_eq] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨1, StabTrio0.one_mem, one_smul _ _⟩
    · exact ⟨lPerm 0, lPerm_mem_stab 0, lPerm_zero_brick1⟩
    · exact ⟨lPerm 0 * lPerm 0, StabTrio0.mul_mem (lPerm_mem_stab 0) (lPerm_mem_stab 0), by
        rw [mul_smul, lPerm_zero_brick1, lPerm_zero_brick2]⟩
  have hodd : ¬ 2 ∣ ((trioFin 0 : Finset (Finset (Fin 24))) : Set (Finset (Fin 24))).ncard := by
    rw [Set.ncard_coe_finset, (isTrio_trioFin (by norm_num : 0 < 3795)).1]
    decide
  exact fix_of_odd_transitive hN.le_stab hN.isPGroup hN.norm_stab hX hb htrans hodd

theorem tupFin_injOn {c c' : ℕ} (hc : c < Native.nTup) (hc' : c' < Native.nTup)
    (h : tupFin c = tupFin c') : c = c' := by
  simp only [tupFin, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e1 := octFin_injective (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
  have e2 := octFin_injective (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h2
  have e3 := sextFin_injective (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h3
  have e4 := sextFin_injective (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h4
  have e5 := sextFin_injective (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h5
  unfold Native.nTup at hc hc'
  omega

theorem tup_step (j : Fin 4) (i : ℕ)
    (hji : (Native.tupSteps Native.lTabs).getD j id i < Native.nTup) :
    tupFin ((Native.tupSteps Native.lTabs).getD j id i) = lPerm j • tupFin i := by
  have e : (Native.tupSteps Native.lTabs).getD j id i =
      Native.stepTup (Native.octList ()) (Native.sextList ()) (Native.lTabs.getD j #[]) i := by
    simp only [Native.tupSteps]
    rw [getD_map_of_lt _ Native.lTabs #[] id j.2]
  rw [e] at hji ⊢
  have hrep := repT_lPerm j
  generalize Native.lTabs.getD j #[] = t at hji hrep ⊢
  simp only [Native.stepTup] at hji ⊢
  split_ifs at hji ⊢ with hc
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨ha, hb⟩, hu⟩, hv⟩, hw⟩ := hc
    rw [tupFin_encTup ha hb hu hv hw]
    simp only [tupFin, Prod.smul_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [octFin_octIdx ha, smul_octFin hrep (Nat.mod_lt _ (by norm_num))]
    · rw [octFin_octIdx hb, smul_octFin hrep (Nat.mod_lt _ (by norm_num))]
    · rw [sextOfL_sextIdx hu, smul_sextFin hrep (Nat.mod_lt _ (by norm_num))]
    · rw [sextOfL_sextIdx hv, smul_sextFin hrep (Nat.mod_lt _ (by norm_num))]
    · rw [sextOfL_sextIdx hw, smul_sextFin hrep (Nat.mod_lt _ (by norm_num))]
  · exact absurd hji (lt_irrefl _)

end Base

section Sext


theorem exists_smul_fix_trio_sextet' {l U U' : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hU : IsSextet U) (hU' : IsSextet U') (hlU : TrioIn l U) (hlU' : TrioIn l U') :
    ∃ g ∈ M24g, g • l = l ∧ g • U = U' := by
  obtain ⟨a, ha, haU⟩ := sextet_transitive hU
  obtain ⟨b, hb, hbU⟩ := sextet_transitive hU'
  set g := b⁻¹ * a with hg
  have hgm : g ∈ M24g := M24g.mul_mem (M24g.inv_mem hb) ha
  have hgU : g • U = U' := by rw [hg, mul_smul, haU, ← hbU, inv_smul_smul]
  have hgl : TrioIn (g • l) U' := by
    rw [← hgU]
    exact (trioIn_smul_iff g).2 hlU
  obtain ⟨k, hk, hkU, hkl⟩ := kappa_orbit hU' ((isTrio_smul_iff hgm).2 hl) hl (i := 0) hgl hlU'
  exact ⟨k * g, M24g.mul_mem hk hgm, by rw [mul_smul, hkl], by rw [mul_smul, hgU, hkU]⟩

end Sext

section Facts


theorem mem_sextsOfBase {q : ℕ} :
    q ∈ Native.sextsOfBase () ↔ q < 1771 ∧ TrioIn (trioFin 0) (sextFin q) := by
  unfold Native.sextsOfBase
  simp only [List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hq, h⟩
    refine ⟨hq, (trioIn_iff zero_lt_3795 hq).1 ?_⟩
    rw [trioList_zero]
    exact h
  · rintro ⟨hq, h⟩
    refine ⟨hq, ?_⟩
    have h' := (trioIn_iff zero_lt_3795 hq).2 h
    rwa [trioList_zero] at h'

theorem trioIn_base : TrioIn (trioFin 0) (sextFin 0) := by
  have h := (baseSext_spec Native.baseSext (by simp)).1
  refine (trioIn_iff zero_lt_3795 zero_lt_1771).1 ?_
  rw [trioList_zero, sextList_zero]
  exact h

theorem ncard_sextets_base : {U | IsSextet U ∧ TrioIn (trioFin 0) U}.ncard = 7 := by
  have key := ncard_eq_length_filter (F := sextFin) (n := 1771)
    (fun p hp p' hp' he => sextFin_injective hp hp' he) (P := IsSextet) isSextet_iff
    (fun q => Native.trioIn (Native.trioList ())[0]! (Native.sextList ())[q]!)
    (Q := fun U => TrioIn (trioFin 0) U) (fun q hq => (trioIn_iff zero_lt_3795 hq).symm)
  rw [key, trioList_zero]
  exact genFix_spec.1

theorem octIdx_brick (m : ℕ) (hm : m = 255 ∨ m = 65280) :
    Native.octIdx m < 759 ∧ octFin (Native.octIdx m) ∈ trioFin 0 := by
  obtain ⟨-, -, h3, h4, -, -⟩ := trioList_get zero_lt_3795 trioList_zero
  have h3' : Native.octIdx 255 < 759 := h3
  have h4' : Native.octIdx 65280 < 759 := h4
  rw [trioFin_zero_eq]
  rcases hm with rfl | rfl
  · exact ⟨h3', by rw [octFin_octIdx h3']; simp⟩
  · exact ⟨h4', by rw [octFin_octIdx h4']; simp⟩

theorem sextIdx_x0 {U : List ℕ} (hU : U ∈ [Native.baseSext, Native.sextU2, Native.sextU3]) :
    Native.sextIdx U < 1771 ∧ IsSextet (sextFin (Native.sextIdx U)) ∧
      TrioIn (trioFin 0) (sextFin (Native.sextIdx U)) := by
  obtain ⟨h1, h2⟩ := baseSext_spec U hU
  refine ⟨h2, isSextet_sextFin h2, (trioIn_iff zero_lt_3795 h2).1 ?_⟩
  rw [trioList_zero, sextList_sextIdx h2]
  exact h1

theorem tupFin_x0 : tupFin (Native.x0Code ()) =
    (octFin (Native.octIdx 255), octFin (Native.octIdx 65280),
      sextFin (Native.sextIdx Native.baseSext), sextFin (Native.sextIdx Native.sextU2),
      sextFin (Native.sextIdx Native.sextU3)) := by
  unfold Native.x0Code
  exact tupFin_encTup (octIdx_brick 255 (Or.inl rfl)).1 (octIdx_brick 65280 (Or.inr rfl)).1
    (sextIdx_x0 (by simp)).1 (sextIdx_x0 (by simp)).1 (sextIdx_x0 (by simp)).1

theorem tPerm_fix_trio (j : Fin 6) : tPerm j • trioFin 0 = trioFin 0 := by
  obtain ⟨-, hfix⟩ := genFix_spec
  obtain ⟨e1, e2, e3, -⟩ := hfix _ (tTabs_getD_mem j)
  rw [trioFin_zero_eq, Finset.smul_finset_insert, Finset.smul_finset_insert,
    Finset.smul_finset_singleton, ← maskFin_img (repT_tPerm j) 255,
    ← maskFin_img (repT_tPerm j) 65280, ← maskFin_img (repT_tPerm j) 16711680, e1, e2, e3]

theorem tPerm_mem_stab (j : Fin 6) : tPerm j ∈ StabTrio0 :=
  mem_StabTrio0.2 ⟨tPerm_mem j, tPerm_fix_trio j⟩

theorem tPerm_fix_tup (j : Fin 6) :
    tPerm j • tupFin (Native.x0Code ()) = tupFin (Native.x0Code ()) := by
  obtain ⟨-, hfix⟩ := genFix_spec
  obtain ⟨e1, e2, -, e4⟩ := hfix _ (tTabs_getD_mem j)
  rw [tupFin_x0]
  simp only [Prod.smul_mk, Prod.mk.injEq]
  have hsext : ∀ U ∈ [Native.baseSext, Native.sextU2, Native.sextU3],
      tPerm j • sextFin (Native.sextIdx U) = sextFin (Native.sextIdx U) := by
    intro U hU
    obtain ⟨hq, -, hin⟩ := sextIdx_x0 hU
    rw [smul_sextFin (repT_tPerm j) hq, e4 _ (mem_sextsOfBase.2 ⟨hq, hin⟩)]
    rfl
  refine ⟨?_, ?_, hsext _ (by simp), hsext _ (by simp), hsext _ (by simp)⟩
  · rw [octFin_octIdx (octIdx_brick 255 (Or.inl rfl)).1, ← maskFin_img (repT_tPerm j) 255, e1]
  · rw [octFin_octIdx (octIdx_brick 65280 (Or.inr rfl)).1, ← maskFin_img (repT_tPerm j) 65280, e2]

theorem five_le_ncard_image {N : Subgroup S24} (hT : ∀ j : Fin 6, tPerm j ∈ N) {p : ℕ}
    (hp : p < 3795)
    (hz : ¬ 1 < Native.zc (Native.trioList ())[0]! (Native.trioList ())[p]!) :
    5 ≤ ((fun σ : S24 => σ • trioFin p) '' (N : Set S24)).ncard := by
  obtain ⟨hlen, hnd, hlt, hreach⟩ := trioOrbit_spec hp hz
  set c := Native.orbitFive (Native.trioSteps Native.tTabs) p with hc
  have key := reachOK_trio_fix (((1 : S24) : S24 ⧸ N)) Native.tTabs tPerm repT_tPerm tPerm_mem
    (fun j => (smul_one_quotient_iff N _).2 (hT j)) hreach hp
  have hsub : (((c.map trioFin).toFinset : Finset (Finset (Finset (Fin 24)))) :
      Set (Finset (Finset (Fin 24)))) ⊆ (fun σ : S24 => σ • trioFin p) '' (N : Set S24) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 (Finset.mem_coe.1 hx))
    obtain ⟨σ, -, hσy, hσ⟩ := key q hq
    exact ⟨σ, (smul_one_quotient_iff N σ).1 hσy, hσ⟩
  have hcard : (c.map trioFin).toFinset.card = 5 := by
    rw [List.toFinset_card_of_nodup, List.length_map, hlen]
    exact hnd.map_on fun x hx y hy h => trioFin_injective (hlt x hx) (hlt y hy) h
  calc 5 = (↑((c.map trioFin).toFinset) : Set (Finset (Finset (Fin 24)))).ncard := by
        rw [Set.ncard_coe_finset, hcard]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end Facts

section Orbit


theorem IsBaseNormal.fix_sextet {N : Subgroup S24} (hN : IsBaseNormal N) :
    ∀ n ∈ N, ∀ U, IsSextet U → TrioIn (trioFin 0) U → n • U = U := by
  have hX : ∀ s ∈ StabTrio0, ∀ U ∈ {U | IsSextet U ∧ TrioIn (trioFin 0) U},
      s • U ∈ {U | IsSextet U ∧ TrioIn (trioFin 0) U} := by
    intro s hs U hU
    obtain ⟨hsM, hsl⟩ := mem_StabTrio0.1 hs
    refine ⟨(isSextet_smul_iff hsM).2 hU.1, ?_⟩
    have h := (trioIn_smul_iff s).2 hU.2
    rwa [hsl] at h
  have hb : sextFin 0 ∈ {U | IsSextet U ∧ TrioIn (trioFin 0) U} :=
    ⟨isSextet_sextFin zero_lt_1771, trioIn_base⟩
  have htrans : ∀ U ∈ {U | IsSextet U ∧ TrioIn (trioFin 0) U},
      ∃ s ∈ StabTrio0, s • sextFin 0 = U := by
    rintro U ⟨hU, hUt⟩
    obtain ⟨g, hg, hgl, hgU⟩ := exists_smul_fix_trio_sextet' (isTrio_trioFin zero_lt_3795)
      (isSextet_sextFin zero_lt_1771) hU trioIn_base hUt
    exact ⟨g, mem_StabTrio0.2 ⟨hg, hgl⟩, hgU⟩
  have hodd : ¬ 2 ∣ {U | IsSextet U ∧ TrioIn (trioFin 0) U}.ncard := by
    rw [ncard_sextets_base]
    decide
  intro n hn U hU hUt
  exact fix_of_odd_transitive hN.le_stab hN.isPGroup hN.norm_stab hX hb htrans hodd n hn U
    ⟨hU, hUt⟩

theorem IsBaseNormal.fix_tup {N : Subgroup S24} (hN : IsBaseNormal N) :
    ∀ n ∈ N, n • tupFin (Native.x0Code ()) = tupFin (Native.x0Code ()) := by
  intro n hn
  rw [tupFin_x0]
  simp only [Prod.smul_mk, Prod.mk.injEq]
  refine ⟨hN.fix_octad n hn _ (octIdx_brick 255 (Or.inl rfl)).2,
    hN.fix_octad n hn _ (octIdx_brick 65280 (Or.inr rfl)).2, ?_, ?_, ?_⟩
  · exact hN.fix_sextet n hn _ (sextIdx_x0 (by simp)).2.1 (sextIdx_x0 (by simp)).2.2
  · exact hN.fix_sextet n hn _ (sextIdx_x0 (by simp)).2.1 (sextIdx_x0 (by simp)).2.2
  · exact hN.fix_sextet n hn _ (sextIdx_x0 (by simp)).2.1 (sextIdx_x0 (by simp)).2.2

theorem ncard_orbit_tup :
    1008 ≤ (MulAction.orbit StabTrio0 (tupFin (Native.x0Code ()))).ncard := by
  obtain ⟨hx0, hlen, hnd, hlt, hreach⟩ := tupOrbit_spec
  have key := reachOK_smul_fix (trioFin 0) tupFin Native.nTup (Native.tupSteps Native.lTabs)
    (m := 4) (by simp only [Native.tupSteps, List.length_map]; rfl) lPerm lPerm_mem lPerm_fix
    (fun j i _ hji => tup_step j i hji) hreach hx0
  set c := Native.orbitTup (Native.tupSteps Native.lTabs) (Native.x0Code ()) with hc
  have hsub : ((c.toFinset.image tupFin : Finset Tup5) : Set Tup5) ⊆
      MulAction.orbit StabTrio0 (tupFin (Native.x0Code ())) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    obtain ⟨σ, hσM, hσy, hσ⟩ := key q (List.mem_toFinset.1 hq)
    exact ⟨⟨σ, mem_StabTrio0.2 ⟨hσM, hσy⟩⟩, hσ⟩
  have hcard : (c.toFinset.image tupFin).card = c.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd]
    intro x hx y hy hxy
    exact tupFin_injOn (hlt x (List.mem_toFinset.1 hx)) (hlt y (List.mem_toFinset.1 hy)) hxy
  calc 1008 ≤ c.length := hlen
    _ = (↑(c.toFinset.image tupFin) : Set Tup5).ncard := by
        rw [Set.ncard_coe_finset, hcard]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

end Orbit

section Main


theorem IsBaseNormal.tPerm_mem {N : Subgroup S24} (hN : IsBaseNormal N) (j : Fin 6) :
    tPerm j ∈ N := by
  refine mem_of_fix_of_card_le hN.le_stab hN.fix_tup ?_ (tPerm j) (tPerm_mem_stab j)
    (tPerm_fix_tup j)
  rw [card_StabTrio0, hN.card]
  calc 64512 = 1008 * 64 := by norm_num
    _ ≤ _ := Nat.mul_le_mul_right 64 ncard_orbit_tup

theorem stmt3_12_base {N : Subgroup S24} (hN : IsBaseNormal N) {k : Finset (Finset (Fin 24))}
    (hk : IsTrio k) (hD : Delta (trioFin 0) k 3 ∨ Delta (trioFin 0) k 4) :
    4 < ((fun σ : S24 => σ • k) '' (N : Set S24)).ncard := by
  obtain ⟨p, hp, rfl⟩ := (isTrio_iff k).1 hk
  have hz : ¬ 1 < Native.zc (Native.trioList ())[0]! (Native.trioList ())[p]! := by
    rw [zc_eq zero_lt_3795 hp]
    rcases hD with h | h
    · have h' : ((trioFin p).filter (InZeta (trioFin 0))).card = 1 := h
      omega
    · have h' : ((trioFin p).filter (InZeta (trioFin 0))).card = 0 := h
      omega
  have h5 := five_le_ncard_image (fun j => hN.tPerm_mem j) hp hz
  omega

theorem stmt3_12M24 : Stmt3_12M24 := by
  intro l k N hl hk hD hNM hfix hnorm _hp2 hcard
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  let N' : Subgroup S24 := N.map (MulAut.conj g).toMonoidHom
  have hmem : ∀ σ, σ ∈ N' ↔ g⁻¹ * σ * g ∈ N := by
    intro σ
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      have e : g⁻¹ * (MulAut.conj g).toMonoidHom n * g = n := by
        simp [MulAut.conj_apply, mul_assoc]
      rwa [e]
    · intro h
      refine ⟨g⁻¹ * σ * g, h, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hlg : g⁻¹ • trioFin 0 = l := by rw [← hgl, inv_smul_smul]
  have hN' : IsBaseNormal N' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro σ hσ
      have h1 : g * (g⁻¹ * σ * g) * g⁻¹ ∈ M24g :=
        M24g.mul_mem (M24g.mul_mem hg (hNM ((hmem σ).1 hσ))) (M24g.inv_mem hg)
      have e : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
      rwa [e] at h1
    · intro σ hσ
      have h1 := hfix _ ((hmem σ).1 hσ)
      have e : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      calc σ • trioFin 0 = (g * (g⁻¹ * σ * g) * g⁻¹) • trioFin 0 := by rw [← e]
        _ = g • ((g⁻¹ * σ * g) • (g⁻¹ • trioFin 0)) := by simp only [mul_smul]
        _ = trioFin 0 := by rw [hlg, h1, ← hgl]
    · intro s hs hsl n' hn'
      have hn : g⁻¹ * n' * g ∈ N := (hmem n').1 hn'
      have hs₁ : g⁻¹ * s * g ∈ M24g := M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hg) hs) hg
      have hs₁l : (g⁻¹ * s * g) • l = l := by
        calc (g⁻¹ * s * g) • l = g⁻¹ • (s • (g • l)) := by simp only [mul_smul]
          _ = l := by rw [hgl, hsl, hlg]
      have h1 := hnorm _ hs₁ hs₁l _ hn
      refine (hmem _).2 ?_
      have e : g⁻¹ * (s * n' * s⁻¹) * g = (g⁻¹ * s * g) * (g⁻¹ * n' * g) * (g⁻¹ * s * g)⁻¹ := by
        group
      rwa [e]
    · rw [Subgroup.card_map_of_injective (fun a b h => (MulAut.conj g).injective h), hcard]
  have hD' : Delta (trioFin 0) (g • k) 3 ∨ Delta (trioFin 0) (g • k) 4 := by
    rw [← hgl]
    rcases hD with h | h
    · exact Or.inl ((delta_smul_iff hg 3).2 h)
    · exact Or.inr ((delta_smul_iff hg 4).2 h)
  have key := stmt3_12_base hN' ((isTrio_smul_iff hg).2 hk) hD'
  have himg : (fun σ : S24 => σ • g • k) '' (N' : Set S24) =
      (fun x => g • x) '' ((fun σ : S24 => σ • k) '' (N : Set S24)) := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨(g⁻¹ * σ * g) • k, ⟨g⁻¹ * σ * g, (hmem σ).1 hσ, rfl⟩, ?_⟩
      simp only [← mul_smul]
      congr 1
      group
    · rintro ⟨y, ⟨n, hn, rfl⟩, rfl⟩
      refine ⟨g * n * g⁻¹, (hmem _).2 ?_, ?_⟩
      · have e : g⁻¹ * (g * n * g⁻¹) * g = n := by group
        rwa [e]
      · simp only [← mul_smul]
        congr 1
        group
  rw [himg, Set.ncard_image_of_injective _ (MulAction.injective g)] at key
  exact key

end Main

end CFSG.Quasithin.H13.AS91.M24G
