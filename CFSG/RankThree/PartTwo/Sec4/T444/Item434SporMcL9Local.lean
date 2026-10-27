module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporMcL27
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporMcL9Lift
public import Certificates.Certificate9561

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporMcL9

open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Sporadic.Schreier (mclP)
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem mcl9_check : mcl9Check = true :=
  Certificates.certificate9561

theorem conj_eq_of_eqA {q t w : Array ℕ} {g h k : mclP} (hq : Rep 275 q (g : Equiv.Perm (Fin 275)))
    (hqi : Rep 275 (invCand 275 q) (g : Equiv.Perm (Fin 275))⁻¹)
    (ht : Rep 275 t (h : Equiv.Perm (Fin 275))) (hw : Rep 275 w (k : Equiv.Perm (Fin 275)))
    (hc : eqA 275 (conjN 275 q t) w = true) : g * h * g⁻¹ = k :=
  Subtype.ext (eq_of_eqA (rep_conjN hq hqi ht) hw hc)

theorem sq_eq_inv_of_cube {Y : Type*} [Group Y] {x : Y} (hx : x ^ 3 = 1) : x ^ 2 = x⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx)

theorem exists_klein_basis :
    ∃ (s t h : mclP) (e : Fin 4 → mclP), (∀ a, e a ∈ mclD) ∧
      81 ≤ Nat.card (Subgroup.closure (Set.range e)) ∧
      (s * e 0 * s⁻¹ = e 0 ∧ s * e 1 * s⁻¹ = e 1 ∧ s * e 2 * s⁻¹ = (e 2)⁻¹ ∧
        s * e 3 * s⁻¹ = (e 3)⁻¹) ∧
      (t * e 0 * t⁻¹ = e 0 ∧ t * e 1 * t⁻¹ = (e 1)⁻¹ ∧ t * e 2 * t⁻¹ = e 2 ∧
        t * e 3 * t⁻¹ = (e 3)⁻¹) ∧
      h * e 1 * h⁻¹ = e 0 * e 2 ^ 2 * e 3 ^ 2 := by
  have hc := mcl9_check
  simp only [mcl9Check, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsift, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩ := hc
  have hs : ∀ k < 3, mclSift (mcl9Arr k) = true := fun k hk => allLt_spec hsift hk
  have hdist : ∀ u < 81, ∀ v < 81, u = v ∨ eqA 275 (mcl9Prod u) (mcl9Prod v) = false := by
    intro u hu v hv
    have := allLt_spec (allLt_spec c10 hu) hv
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    exact this
  obtain ⟨hs0, hs0i⟩ := rep_of_mclSift (hs 0 (by norm_num))
  obtain ⟨ht0, ht0i⟩ := rep_of_mclSift (hs 1 (by norm_num))
  obtain ⟨hh0, hh0i⟩ := rep_of_mclSift (hs 2 (by norm_num))
  set sM : mclP := ⟨permOfArr 275 (mcl9Arr 0), mem_mclP_of_mclSift (hs 0 (by norm_num))⟩
    with hsM
  set tM : mclP := ⟨permOfArr 275 (mcl9Arr 1), mem_mclP_of_mclSift (hs 1 (by norm_num))⟩
    with htM
  set hM : mclP := ⟨permOfArr 275 (mcl9Arr 2), mem_mclP_of_mclSift (hs 2 (by norm_num))⟩
    with hhM
  set eM : ℕ → mclP := fun a => prodM (mcl9Code a) with heM
  have hcube : ∀ a, eM a ^ 3 = 1 := fun a => isElemAbelian_mclD.2 _ (prodM_mem _)
  have hsq : ∀ a, eM a ^ 2 = (eM a)⁻¹ := fun a => sq_eq_inv_of_cube (hcube a)
  have rE : ∀ a, Rep 275 (mcl9E a) (eM a : Equiv.Perm (Fin 275)) := fun a =>
    rep_mclDProd (mcl9Code a)
  set prodE : ℕ → mclP := fun u =>
    eM 0 ^ (u % 3) * eM 1 ^ (u / 3 % 3) * eM 2 ^ (u / 9 % 3) * eM 3 ^ (u / 27 % 3) with hprodE
  have rP : ∀ u, Rep 275 (mcl9Prod u) (prodE u : Equiv.Perm (Fin 275)) := by
    intro u
    simp only [hprodE, mcl9Prod, Subgroup.coe_mul, Subgroup.coe_pow]
    exact rep_compA (rep_compA (rep_compA (rep_powN (rE 0) _) (rep_powN (rE 1) _))
      (rep_powN (rE 2) _)) (rep_powN (rE 3) _)
  have rSq : ∀ a, Rep 275 (powN 275 (mcl9E a) 2) ((eM a ^ 2 : mclP) : Equiv.Perm (Fin 275)) :=
    fun a => by
      rw [Subgroup.coe_pow]
      exact rep_powN (rE a) 2
  have r1 : sM * eM 0 * sM⁻¹ = eM 0 := conj_eq_of_eqA hs0 hs0i (rE 0) (rE 0) c1
  have r2 : sM * eM 1 * sM⁻¹ = eM 1 := conj_eq_of_eqA hs0 hs0i (rE 1) (rE 1) c2
  have r3 : sM * eM 2 * sM⁻¹ = (eM 2)⁻¹ := by
    rw [← hsq 2]; exact conj_eq_of_eqA hs0 hs0i (rE 2) (rSq 2) c3
  have r4 : sM * eM 3 * sM⁻¹ = (eM 3)⁻¹ := by
    rw [← hsq 3]; exact conj_eq_of_eqA hs0 hs0i (rE 3) (rSq 3) c4
  have r5 : tM * eM 0 * tM⁻¹ = eM 0 := conj_eq_of_eqA ht0 ht0i (rE 0) (rE 0) c5
  have r6 : tM * eM 1 * tM⁻¹ = (eM 1)⁻¹ := by
    rw [← hsq 1]; exact conj_eq_of_eqA ht0 ht0i (rE 1) (rSq 1) c6
  have r7 : tM * eM 2 * tM⁻¹ = eM 2 := conj_eq_of_eqA ht0 ht0i (rE 2) (rE 2) c7
  have r8 : tM * eM 3 * tM⁻¹ = (eM 3)⁻¹ := by
    rw [← hsq 3]; exact conj_eq_of_eqA ht0 ht0i (rE 3) (rSq 3) c8
  have r9 : hM * eM 1 * hM⁻¹ = eM 0 * eM 2 ^ 2 * eM 3 ^ 2 := by
    have this : hM * eM 1 * hM⁻¹ = prodE 73 := conj_eq_of_eqA hh0 hh0i (rE 1) (rP 73) c9
    rw [this]
    simp only [hprodE]
    norm_num
  refine ⟨sM, tM, hM, fun a => eM a, fun a => prodM_mem _, ?_, ⟨r1, r2, r3, r4⟩,
    ⟨r5, r6, r7, r8⟩, r9⟩
  have hmem : ∀ u, prodE u ∈ Subgroup.closure (Set.range fun a : Fin 4 => eM a) := by
    intro u
    have hg : ∀ a : Fin 4, eM a ∈ Subgroup.closure (Set.range fun a : Fin 4 => eM a) :=
      fun a => Subgroup.subset_closure ⟨a, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (hg 0) _) (Subgroup.pow_mem _ (hg 1) _))
      (Subgroup.pow_mem _ (hg 2) _)) (Subgroup.pow_mem _ (hg 3) _)
  set f : Fin 81 → Subgroup.closure (Set.range fun a : Fin 4 => eM a) :=
    fun u => ⟨prodE u, hmem u⟩ with hf
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : (prodE u : Equiv.Perm (Fin 275)) = prodE v :=
      congrArg (fun w : Subgroup.closure (Set.range fun a : Fin 4 => eM a) =>
        ((w : mclP) : Equiv.Perm (Fin 275))) huv
    rcases hdist u u.2 v v.2 with h | h
    · exact Fin.ext h
    · rw [(eqA_iff (rP u) (rP v)).2 h1] at h
      exact absurd h Bool.noConfusion
  have := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

theorem exists_conj_mem_mclD_of_cube
    {u : mclP} (hu : u ^ 3 = 1) :
    ∃ c : mclP, c * u * c⁻¹ ∈ mclD := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hu1 : u = 1
  · refine ⟨1, ?_⟩
    rw [hu1, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hu3 : orderOf u = 3 := orderOf_eq_prime hu hu1
  have hPp : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu3]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card card_mclQ hPp
  have hle := Item434AltPerm.map_conj_inv_le hg
  have hmem : g⁻¹ * u * g ∈ mclQ := by
    refine hle ⟨u, Subgroup.mem_zpowers u, ?_⟩
    change g⁻¹ * u * g⁻¹⁻¹ = g⁻¹ * u * g
    rw [inv_inv]
  have hcube : (g⁻¹ * u * g) ^ 3 = 1 := by
    have h1 : (g⁻¹ * u * g⁻¹⁻¹) ^ 3 = g⁻¹ * u ^ 3 * g⁻¹⁻¹ := conj_pow
    rw [inv_inv, hu] at h1
    rw [h1]
    group
  obtain ⟨t, hts, -⟩ := exists_conj_mem_mclD hmem hcube
  refine ⟨t * g⁻¹, ?_⟩
  have : t * g⁻¹ * u * (t * g⁻¹)⁻¹ = t * (g⁻¹ * u * g) * t⁻¹ := by group
  rw [this]
  exact hts

theorem exists_lift_e81
    {Y : Type*} [Group Y] [Finite Y] (ρ : Y →* mclP) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center Y) (hZ3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {u : mclP}
    (hu : u ^ 3 = 1) :
    ∃ E : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
      ∀ x ∈ E, ρ x * u = u * ρ x := by
  obtain ⟨s, t, h, e, heD, hcard, ⟨hs0, hs1, hs2, hs3⟩, ⟨ht0, ht1, ht2, ht3⟩, hh⟩ :=
    exists_klein_basis
  obtain ⟨c, hcu⟩ := exists_conj_mem_mclD_of_cube hu
  set ρ' : Y →* mclP := (MulAut.conj c).toMonoidHom.comp ρ with hρ'
  have hρ'apply : ∀ y, ρ' y = c * ρ y * c⁻¹ := fun y => rfl
  have hρ'surj : Function.Surjective ρ' := (MulAut.conj c).surjective.comp hρ
  have hker' : ρ'.ker ≤ ρ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz ⊢
    have h1 : (MulAut.conj c) (ρ z) = (MulAut.conj c) 1 := by
      rw [map_one]; exact hz
    exact (MulAut.conj c).injective h1
  choose x hx using fun a => hρ'surj (e a)
  obtain ⟨ss, hss⟩ := hρ'surj s
  obtain ⟨tt, htt⟩ := hρ'surj t
  obtain ⟨hh', hhh⟩ := hρ'surj h
  have hcommD : ∀ a b, e a * e b = e b * e a := fun a b =>
    congrArg Subtype.val (isElemAbelian_mclD.1.is_comm.comm ⟨e a, heD a⟩ ⟨e b, heD b⟩)
  have hcubeD : ∀ a, e a ^ 3 = 1 := fun a => isElemAbelian_mclD.2 _ (heD a)
  obtain ⟨hcommY, hcubeY⟩ := lift_commute_cube ρ' (fun z hz => hker (hker' hz))
    (fun z hz => hZ3 z (hker' hz)) x ss tt hh'
    (fun a b => by rw [hx a, hx b]; exact hcommD a b)
    (fun a => by rw [hx a]; exact hcubeD a)
    (by rw [hss, hx 0]; exact hs0) (by rw [hss, hx 1]; exact hs1)
    (by rw [hss, hx 2]; exact hs2) (by rw [hss, hx 3]; exact hs3)
    (by rw [htt, hx 0]; exact ht0) (by rw [htt, hx 1]; exact ht1)
    (by rw [htt, hx 2]; exact ht2) (by rw [htt, hx 3]; exact ht3)
    (by rw [hhh, hx 1, hx 0, hx 2, hx 3]; exact hh)
  refine ⟨Subgroup.closure (Set.range x), ?_, ?_, ?_⟩
  · refine isElemAbelian_closure_of_comm ?_ ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact hcommY a b
    · rintro _ ⟨a, rfl⟩
      exact hcubeY a
  · have hle : Subgroup.closure (Set.range e) ≤
        (Subgroup.closure (Set.range x)).map ρ' := by
      rw [Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      exact ⟨x a, Subgroup.subset_closure ⟨a, rfl⟩, hx a⟩
    exact hcard.trans ((Subgroup.card_le_of_le hle).trans
      (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)))
  · intro y hy
    have hyD : ρ' y ∈ mclD := by
      have hle : Subgroup.closure (Set.range x) ≤ mclD.comap ρ' := by
        rw [Subgroup.closure_le]
        rintro _ ⟨a, rfl⟩
        change ρ' (x a) ∈ mclD
        rw [hx a]
        exact heD a
      exact hle hy
    have hcomm : ρ' y * (c * u * c⁻¹) = c * u * c⁻¹ * ρ' y :=
      congrArg Subtype.val (isElemAbelian_mclD.1.is_comm.comm ⟨ρ' y, hyD⟩ ⟨_, hcu⟩)
    rw [hρ'apply] at hcomm
    have h2 : c * (ρ y * u) * c⁻¹ = c * (u * ρ y) * c⁻¹ := by
      calc c * (ρ y * u) * c⁻¹ = c * ρ y * c⁻¹ * (c * u * c⁻¹) := by group
        _ = c * u * c⁻¹ * (c * ρ y * c⁻¹) := hcomm
        _ = c * (u * ρ y) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

end CFSG.RankThree.PartTwo.Sec4.Item434SporMcL9
