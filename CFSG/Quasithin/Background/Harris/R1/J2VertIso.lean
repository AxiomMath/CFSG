module

public import CFSG.Quasithin.Background.Harris.R1.J2VertIdentMain
public import CFSG.Quasithin.Background.Harris.R1.J2VertHom
public import CFSG.Quasithin.Background.Harris.R1.J2VertPres

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Quasithin CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.F2 CFSG.Quasithin.J2Cz.QM Equiv
  CFSG.CosetTable

namespace VertGens

variable {H : Type} [Group H] {g : VertGens H}

theorem a_mem_L : g.a ∈ g.L := Subgroup.subset_closure (Set.mem_insert _ _)

theorem b_mem_L : g.b ∈ g.L := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem commute_z_of_mem_L {l : H} (hl : l ∈ g.L) : Commute l g.z := by
  have hle : g.L ≤ Subgroup.centralizer {g.z} := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr g.za.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr g.zb.symm
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hl)

@[expose] def wB (g : VertGens H) : H := g.a⁻¹ * g.b⁻¹ * g.a⁻¹ * g.b * g.a * g.b⁻¹

theorem wB_mem : g.wB ∈ g.L :=
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (inv_mem a_mem_L) (inv_mem b_mem_L))
    (inv_mem a_mem_L)) b_mem_L) a_mem_L) (inv_mem b_mem_L)

theorem card_QM' : Nat.card QM = 32 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem liftT_mem' {K : Subgroup H} {w : H} {y : Fin 4 → H} (hw : w ∈ K) (hy : ∀ j, y j ∈ K)
    (p : QM) : liftT w y p 1 ∈ K := by
  have hpw : ∀ (h : H) (s : F2), h ∈ K → pw h s ∈ K := fun h s hh => by
    cases s
    · exact K.one_mem
    · exact hh
  simp only [liftT, mul_one]
  exact K.mul_mem (hpw _ _ hw) (K.mul_mem (hpw _ _ (hy 0)) (K.mul_mem (hpw _ _ (hy 1))
    (K.mul_mem (hpw _ _ (hy 2)) (hpw _ _ (hy 3)))))

theorem sup_le_closure_gens (t : H) : g.Q ⊔ g.L ≤ Subgroup.closure (Set.range (gens g t)) := by
  have hg : ∀ i, gens g t i ∈ Subgroup.closure (Set.range (gens g t)) :=
    fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hy : ∀ j, g.y j ∈ Subgroup.closure (Set.range (gens g t)) := by
    intro j
    fin_cases j
    exacts [hg 1, hg 2, hg 3, hg 4]
  refine sup_le ?_ ?_
  · rintro _ ⟨p, rfl⟩
    exact liftT_mem' (hg 0) hy p
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hg 5, hg 6]

variable (hχ : Function.Injective g.chi)

include hχ in
theorem z_ne_one' : g.z ≠ 1 := fun h => QM.z_ne_one (hχ (by rw [g.chi_z, h, map_one]))

include hχ in
theorem card_Q : Nat.card g.Q = 32 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hχ).toEquiv, card_QM']

variable [g.Q.Normal]

theorem kappa_wB : kappa hχ g.wB = tau * phiB * tau⁻¹ := by
  rw [tau_phiB, wB]
  simp only [map_mul, map_inv, kappa_a, kappa_b]

@[expose] noncomputable def sgnHom : H →* ℤˣ := Perm.sign.comp (linePermHom.comp (kappa hχ))

theorem sgnHom_apply (h : H) : sgnHom hχ h = Perm.sign (linePerm (kappa hχ h)) := rfl

theorem sup_le_ker_sgnHom : g.Q ⊔ g.L ≤ (sgnHom hχ).ker := by
  refine sup_le ?_ ?_
  · rintro _ ⟨p, rfl⟩
    rw [MonoidHom.mem_ker, sgnHom_apply, kappa_chi, linePerm_conj, map_one]
  · intro l hl
    rw [MonoidHom.mem_ker, sgnHom_apply]
    exact Perm.mem_alternatingGroup.mp (linePerm_mem_alternatingGroup (kappa_mem_L0 hχ hl))

theorem not_mem_sup_of_kappa_eq_tau {t : H} (ht : kappa hχ t = tau) : t ∉ g.Q ⊔ g.L := by
  intro h
  have h1 := sup_le_ker_sgnHom hχ h
  rw [MonoidHom.mem_ker, sgnHom_apply, ht, sign_linePerm_tau] at h1
  exact absurd h1 (by decide)

variable (hC : ∀ h : H, (∀ q ∈ g.Q, h * q = q * h) → h = 1 ∨ h = g.z) (hLQ : g.L ⊓ g.Q = ⊥)

include hC hLQ in
theorem eq_one_of_kappa_L {l : H} (hl : l ∈ g.L) (hk : kappa hχ l = 1) : l = 1 :=
  kappa_injOn_L hχ hC hLQ hl (one_mem _) (by rw [hk, map_one])

include hχ hC hLQ in
theorem card_L : Nat.card g.L = 60 := by
  rw [← card_L0]
  refine Nat.card_congr (Equiv.ofBijective
    (fun l : g.L => (⟨kappa hχ l, kappa_mem_L0 hχ l.2⟩ : L0)) ⟨?_, ?_⟩)
  · intro l m h
    exact Subtype.ext (kappa_injOn_L hχ hC hLQ l.2 m.2 (congrArg Subtype.val h))
  · rintro ⟨φ, hφ⟩
    obtain ⟨l, hl, hlφ⟩ := exists_mem_L hχ hφ
    exact ⟨⟨l, hl⟩, Subtype.ext hlφ⟩

include hχ hC hLQ in
theorem card_sup : Nat.card ↥(g.Q ⊔ g.L) = 1920 := by
  have h1 := Subgroup.relIndex_mul_card (H := g.Q) (K := g.L ⊔ g.Q)
  rw [inf_eq_left.mpr le_sup_right, Subgroup.relIndex_sup_right] at h1
  have h2 := Subgroup.relIndex_mul_card (H := g.Q) (K := g.L)
  rw [inf_comm, hLQ, Subgroup.card_bot, mul_one, card_L hχ hC hLQ] at h2
  rw [sup_comm, ← h1, h2, card_Q hχ]

include hC hLQ in
theorem exists_mulEquiv [Finite H] (hH : Nat.card H = 3840)
    {s : H} (hs : s ∉ g.Q ⊔ g.L) :
    ∃ (ε : Bool) (t : H) (e : PG 8 (vRels ε) ≃* H),
      kappa hχ t = tau ∧ ∀ i, e (PresentedGroup.of i) = gens g t i := by
  have hz := z_ne_one' hχ
  have hz2 : g.z * g.z = 1 := g.lift.w_sq
  obtain ⟨t, ht⟩ := exists_kappa_eq_tau hχ hC hs
  have htz : t * g.z = g.z * t := by
    have h1 := kappa_spec hχ ht QM.z
    rw [aut_z, g.chi_z] at h1
    calc t * g.z = t * g.z * t⁻¹ * t := by group
      _ = g.z * t := by rw [h1]
  have htx : ∀ j : Fin 4, t * g.y j * t⁻¹ = g.chi (tauImg j) := fun j => by
    have h1 := kappa_spec hχ ht (x j.succ)
    rwa [chi_xsucc, tau_x] at h1
  have hkconj : ∀ h : H, kappa hχ (t * h * t⁻¹) = tau * kappa hχ h * tau⁻¹ := fun h => by
    rw [map_mul, map_mul, map_inv, ht]
  have hta0 : t * g.a * t⁻¹ = g.a⁻¹ ∨ t * g.a * t⁻¹ = g.a⁻¹ * g.z := by
    have h1 : kappa hχ (g.a * (t * g.a * t⁻¹)) = 1 := by
      rw [map_mul, hkconj, kappa_a, tau_phiA, mul_inv_cancel]
    have e : t * g.a * t⁻¹ = g.a⁻¹ * (g.a * (t * g.a * t⁻¹)) := by group
    rcases hC _ (kappa_eq_one hχ h1) with h2 | h2
    · left; rw [e, h2, mul_one]
    · right; rw [e, h2]
  have htb0 : t * g.b * t⁻¹ = g.wB ∨ t * g.b * t⁻¹ = g.wB * g.z := by
    have h1 : kappa hχ (g.wB⁻¹ * (t * g.b * t⁻¹)) = 1 := by
      rw [map_mul, map_inv, hkconj, kappa_b, kappa_wB, inv_mul_cancel]
    have e : t * g.b * t⁻¹ = g.wB * (g.wB⁻¹ * (t * g.b * t⁻¹)) := by group
    rcases hC _ (kappa_eq_one hχ h1) with h2 | h2
    · left; rw [e, h2, mul_one]
    · right; rw [e, h2]
  have hw3 : g.wB ^ 3 = 1 := by
    apply eq_one_of_kappa_L hχ hC hLQ (pow_mem wB_mem 3)
    rw [map_pow, kappa_wB, conj_pow, pow_succ, pow_two, phiB_cube, mul_one, mul_inv_cancel]
  have haw5 : (g.a⁻¹ * g.wB) ^ 5 = 1 := by
    apply eq_one_of_kappa_L hχ hC hLQ (pow_mem (mul_mem (inv_mem a_mem_L) wB_mem) 5)
    have h1 : kappa hχ (g.a⁻¹ * g.wB) = tau * (phiA * phiB) * tau⁻¹ := by
      rw [map_mul, map_inv, kappa_a, kappa_wB, ← tau_phiA]
      group
    rw [map_pow, h1, conj_pow, phiA_phiB_five, mul_one, mul_inv_cancel]
  have htb : t * g.b * t⁻¹ = g.wB := by
    rcases htb0 with h | h
    · exact h
    · exfalso
      apply hz
      have hb3 : g.b ^ 3 = 1 := by rw [pow_succ, pow_two]; exact g.b_cube
      have h1 : (t * g.b * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hb3, mul_one, mul_inv_cancel]
      rw [h, (commute_z_of_mem_L wB_mem).mul_pow, hw3, one_mul, pow_succ, pow_two, hz2,
        one_mul] at h1
      exact h1
  have hta : t * g.a * t⁻¹ = g.a⁻¹ := by
    rcases hta0 with h | h
    · exact h
    · exfalso
      apply hz
      have h1 : (t * (g.a * g.b) * t⁻¹) ^ 5 = 1 := by
        rw [conj_pow, g.ab_five, mul_one, mul_inv_cancel]
      have e : t * (g.a * g.b) * t⁻¹ = g.a⁻¹ * g.wB * g.z := by
        calc t * (g.a * g.b) * t⁻¹ = (t * g.a * t⁻¹) * (t * g.b * t⁻¹) := by group
          _ = g.a⁻¹ * (g.z * g.wB) := by rw [h, htb, mul_assoc]
          _ = g.a⁻¹ * g.wB * g.z := by rw [← (commute_z_of_mem_L wB_mem).eq, mul_assoc]
      rw [e, (commute_z_of_mem_L (mul_mem (inv_mem a_mem_L) wB_mem)).mul_pow, haw5, one_mul,
        pow_succ, pow_succ, pow_succ, pow_two, hz2, one_mul, hz2, one_mul] at h1
      exact h1
  obtain ⟨ε, hε⟩ : ∃ ε : Bool, t * t = if ε then g.z else 1 := by
    have h1 : kappa hχ (t * t) = 1 := by rw [map_mul, ht, tau_mul_tau]
    rcases hC _ (kappa_eq_one hχ h1) with h | h
    · exact ⟨false, by simpa using h⟩
    · exact ⟨true, by simpa using h⟩
  have hp := rels_hold t ε htz htx hta htb hε
  obtain ⟨hfin, hle⟩ := card_PG_le ε
  have hsupC := sup_le_closure_gens (g := g) t
  have htC : t ∈ Subgroup.closure (Set.range (gens g t)) := Subgroup.subset_closure ⟨7, rfl⟩
  have htQL := not_mem_sup_of_kappa_eq_tau hχ ht
  have h1920 := card_sup hχ hC hLQ
  have hdvd1 := Subgroup.card_dvd_of_le hsupC
  have hdvd2 := Subgroup.card_subgroup_dvd_card (Subgroup.closure (Set.range (gens g t)))
  rw [h1920] at hdvd1
  rw [hH] at hdvd2
  have hne : Nat.card (Subgroup.closure (Set.range (gens g t))) ≠ 1920 := by
    intro h
    apply htQL
    rw [Subgroup.eq_of_le_of_card_ge hsupC (h.trans h1920.symm).le]
    exact htC
  have hpos : 0 < Nat.card (Subgroup.closure (Set.range (gens g t))) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd1
  have hle' := Nat.le_of_dvd (by norm_num) hdvd2
  have hcl : Nat.card (Subgroup.closure (Set.range (gens g t))) = 3840 := by omega
  have hinj := pgHom_injective hp hfin hle hcl.ge
  have hcard := card_range_pgHom hp hfin hle hcl.ge
  have hsurj : Function.Surjective (pgHom hp) :=
    MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ (by rw [hcard, hH]))
  exact ⟨ε, t, MulEquiv.ofBijective (pgHom hp) ⟨hinj, hsurj⟩, ht, fun i => pgHom_of hp i⟩

end VertGens

end CFSG.Quasithin.Background.Harris.R1.J2Vert
