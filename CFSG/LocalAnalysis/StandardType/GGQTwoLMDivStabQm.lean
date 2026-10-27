module
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod

public section

namespace CFSG.StandardType.QTwo
open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

private def qTwoLMDivStab_e {m : ℕ} (i j : Fin m) : Fin m → Multiplicative (ZMod 3) :=
  Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3)) *
    (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3)))⁻¹

private lemma qTwoLMDivStab_permAut_e {m : ℕ} (σ : Equiv.Perm (Fin m)) (i j : Fin m) :
    SpCoord.permAut σ (qTwoLMDivStab_e i j) =
      qTwoLMDivStab_e (σ i) (σ j) := by
  funext k
  unfold qTwoLMDivStab_e
  simp only [SpCoord.permAut_apply, Function.comp_apply, Pi.mul_apply, Pi.inv_apply,
    Pi.mulSingle_apply, Equiv.Perm.inv_eq_iff_eq]

private lemma qTwoLMDivStab_permAut_mulSingle {m : ℕ} (σ : Equiv.Perm (Fin m))
    (i : Fin m) (g : Multiplicative (ZMod 3)) :
    SpCoord.permAut σ (Pi.mulSingle i g) = Pi.mulSingle (σ i) g := by
  funext k
  simp only [SpCoord.permAut_apply, Function.comp_apply, Pi.mulSingle_apply,
    Equiv.Perm.inv_eq_iff_eq]

private lemma qTwoLMDivStab_e_inv {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    (qTwoLMDivStab_e i j)⁻¹ = qTwoLMDivStab_e j i := by
  funext k
  simp only [qTwoLMDivStab_e, Pi.inv_apply, Pi.mul_apply, Pi.mulSingle_apply]
  by_cases hki : k = i
  · subst k; simp [hij, Ne.symm hij]; decide
  · by_cases hkj : k = j
    · subst k; simp [hij, Ne.symm hij]; decide
    · simp [hki, hkj]; decide

private lemma qTwoLMDivStab_vec_pow {m : ℕ} (w : Fin m → Multiplicative (ZMod 3)) :
    w ^ 3 = 1 := by
  ext i
  rw [Pi.pow_apply, Pi.one_apply,
    show w i = Multiplicative.ofAdd (Multiplicative.toAdd (w i)) from (ofAdd_toAdd _).symm,
    ← ofAdd_nsmul, toAdd_ofAdd, toAdd_one]
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private lemma qTwoLMDivStab_e_self {m : ℕ} (i : Fin m) : qTwoLMDivStab_e i i = 1 := by
  rw [qTwoLMDivStab_e]; exact mul_inv_cancel _

private lemma qTwoLMDivStab_e_apply_self {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    qTwoLMDivStab_e i j i = Multiplicative.ofAdd (1 : ZMod 3) := by
  have hone : (1 : Multiplicative (ZMod 3))⁻¹ = 1 := inv_one
  rw [qTwoLMDivStab_e, Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same,
    Pi.mulSingle_eq_of_ne (i := j) (i' := i) hij, hone, mul_one]

private lemma qTwoLMDivStab_e_apply_right {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    qTwoLMDivStab_e i j j = Multiplicative.ofAdd (-1 : ZMod 3) := by
  rw [qTwoLMDivStab_e, Pi.mul_apply, Pi.inv_apply,
    Pi.mulSingle_eq_of_ne (i := i) (i' := j) hij.symm,
    Pi.mulSingle_eq_same, one_mul, ← ofAdd_neg]

private lemma qTwoLMDivStab_e_apply_of_ne {m : ℕ} {i j l : Fin m}
    (hli : l ≠ i) (hlj : l ≠ j) : qTwoLMDivStab_e i j l = 1 := by
  have hone : (1 : Multiplicative (ZMod 3))⁻¹ = 1 := inv_one
  rw [qTwoLMDivStab_e, Pi.mul_apply, Pi.inv_apply,
    Pi.mulSingle_eq_of_ne (i := i) (i' := l) hli,
    Pi.mulSingle_eq_of_ne (i := j) (i' := l) hlj, hone, mul_one]

private lemma qTwoLMDivStab_exists_four {m : ℕ} (hm : 5 ≤ m) (a b c d : Fin m) :
    ∃ l : Fin m, l ≠ a ∧ l ≠ b ∧ l ≠ c ∧ l ≠ d := by
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, d} : Finset (Fin m))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact Finset.card_le_four.trans_lt (by omega))
  exact ⟨l, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hl⟩

private lemma qTwoLMDivStab_exists_three {m : ℕ} (hm : 5 ≤ m) (a b c : Fin m) :
    ∃ l : Fin m, l ≠ a ∧ l ≠ b ∧ l ≠ c := by
  obtain ⟨l, hla, hlb, hlc, -⟩ := qTwoLMDivStab_exists_four hm a b c a
  exact ⟨l, hla, hlb, hlc⟩

private lemma qTwoLMDivStab_e_injective {m : ℕ} {a b i j : Fin m}
    (hab : a ≠ b) (hij : i ≠ j)
    (h : qTwoLMDivStab_e a b = qTwoLMDivStab_e i j) : a = i ∧ b = j := by
  have haeq : qTwoLMDivStab_e i j a = Multiplicative.ofAdd (1 : ZMod 3) := by
    rw [← h, qTwoLMDivStab_e_apply_self hab]
  have hai : a = i := by
    by_contra hne
    by_cases haj : a = j
    · subst haj
      have hright := qTwoLMDivStab_e_apply_right hij
      have hcontra : (1 : ZMod 3) = -1 := by
        simpa using congrArg Multiplicative.toAdd (haeq.symm.trans hright)
      exact absurd hcontra (by decide)
    · have hother := qTwoLMDivStab_e_apply_of_ne hne haj
      have hcontra : (1 : ZMod 3) = 0 := by
        simpa using congrArg Multiplicative.toAdd (haeq.symm.trans hother)
      exact absurd hcontra (by decide)
  refine ⟨hai, ?_⟩
  by_contra hbj
  by_cases hbi : b = i
  · exact hab (hai.trans hbi.symm)
  · have hbeq : qTwoLMDivStab_e i j b = Multiplicative.ofAdd (-1 : ZMod 3) := by
      rw [← h, qTwoLMDivStab_e_apply_right hab]
    have hother := qTwoLMDivStab_e_apply_of_ne hbi hbj
    have hcontra : (-1 : ZMod 3) = 0 := by
      simpa using congrArg Multiplicative.toAdd (hbeq.symm.trans hother)
    exact absurd hcontra (by decide)

private lemma qTwoLMDivStab_threeCycle_left {m : ℕ} {i j k : Fin m}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Equiv.swap i j * Equiv.swap j k) i = j := by
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik, Equiv.swap_apply_left]

private lemma qTwoLMDivStab_threeCycle_other {m : ℕ} {i j k l : Fin m}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hli : l ≠ i) (hlj : l ≠ j) (hlk : l ≠ k) :
    (Equiv.swap i j * Equiv.swap j k) l = l := by
  rw [Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hlj hlk,
    Equiv.swap_apply_of_ne_of_ne hli hlj]

private lemma qTwoLMDivStab_threeCycle_cube {m : ℕ} {i j k : Fin m}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (Equiv.swap i j * Equiv.swap j k) ^ 3 = 1 := by
  have hcyc : (Equiv.swap i j * Equiv.swap j k).IsThreeCycle := by
    have h := Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := j) (b := i) (c := k)
      (Ne.symm hij) hjk hik
    simpa [Equiv.swap_comm] using h
  exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hcyc.orderOf])

private lemma qTwoLMDivStab_ker_const {m : ℕ} {i₀ : Fin m}
    (x : Fin m → Multiplicative (ZMod 3)) :
    x ∈ Subgroup.zpowers (fun _ => Multiplicative.ofAdd (1 : ZMod 3)) ↔
      ∀ j, x j = x i₀ := by
  constructor
  · intro hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨n, rfl⟩ := hx
    intro j
    simp only [Pi.pow_apply]
  · intro hx
    have hxeq : (fun _ => Multiplicative.ofAdd (1 : ZMod 3)) ^
        (Multiplicative.toAdd (x i₀)).val = x := by
      funext j
      rw [Pi.pow_apply, hx j, ← ofAdd_nsmul, nsmul_eq_mul, mul_one,
        ZMod.natCast_zmod_val, ofAdd_toAdd]
    rw [← hxeq]
    exact Subgroup.npow_mem_zpowers _ _

private lemma qTwoLMDivStab_mem_zpowers_three {G : Type} [Group G] [Finite G] {w z : G}
    (hw : w ^ 3 = 1) (hw1 : w ≠ 1) (hz : z ∈ Subgroup.zpowers w) :
    z = 1 ∨ z = w ∨ z = w⁻¹ := by
  classical
  have hword : orderOf w = 3 := orderOf_eq_prime hw hw1
  rw [mem_zpowers_iff_mem_range_orderOf, hword] at hz
  obtain ⟨a, ha, hza⟩ := Finset.mem_image.mp hz
  rw [Finset.mem_range] at ha
  have h2 : w ^ 2 = w⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, show 2 + 1 = 3 by norm_num, hw]
  have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha3 with rfl | rfl | rfl
  · left; rw [← hza]; simp
  · right; left; rw [← hza]; simp
  · right; right; rw [← hza, h2]

private lemma qTwoLMDivStab_endo_cube {Q : Type} [Group Q] [Finite Q]
    (hcard : Nat.card Q ≤ 3) (h3 : ∀ q : Q, q ^ 3 = 1) (f : Q →* Q)
    (hf : ∀ q, f (f (f q)) = q) : ∀ q, f q = q := by
  intro q
  by_cases hq : q = 1
  · subst hq; exact map_one f
  have hq3 : q ^ 3 = 1 := h3 q
  have hqord : orderOf q = 3 := orderOf_eq_prime hq3 hq
  have hcard3 : Nat.card Q = 3 := by
    have hle : 3 ≤ Nat.card Q := by rw [← hqord]; exact orderOf_le_card
    omega
  have htop : Subgroup.zpowers q = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hqord]
    exact hcard3.symm
  have hfq : f q ≠ 1 := by
    intro h
    exact hq (by simpa [h] using (hf q).symm)
  have hmem : f q ∈ Subgroup.zpowers q := by rw [htop]; exact Subgroup.mem_top _
  rcases qTwoLMDivStab_mem_zpowers_three hq3 hq hmem with h | h | h
  · exact absurd h hfq
  · exact h
  · exfalso
    have h1 : q = q⁻¹ := by
      calc q = f (f (f q)) := (hf q).symm
        _ = f (f (q⁻¹)) := by rw [h]
        _ = f ((f q)⁻¹) := by rw [map_inv]
        _ = f ((q⁻¹)⁻¹) := by rw [h]
        _ = f q := by rw [inv_inv]
        _ = q⁻¹ := h
    have h2 : q ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp h1
    have hdvd : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hqord] at hdvd
    norm_num at hdvd

theorem qTwoLMDivStab_qm_rigid {m : ℕ} (hm : 5 ≤ m) {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (hV : IsQmModel m V ρ) {U : Subgroup V}
    (hUst : ∀ (σ : Equiv.Perm (Fin m)) (u : V), u ∈ U → ρ σ u ∈ U)
    (hUcard : Nat.card V ≤ 3 * Nat.card U) {ψ : MulAut V}
    (hψ : ∀ σ : Equiv.Perm (Fin m), ∃ σ' : Equiv.Perm (Fin m), ψ * ρ σ * ψ⁻¹ = ρ σ')
    (hfix : ∀ u ∈ U, ψ u = u) : ψ = 1 := by
  classical
  obtain ⟨π, hπsurj, hπker, hπequiv⟩ := hV.ex
  haveI : Finite V := Finite.of_surjective π hπsurj
  letI : CommGroup V := MonoidHom.commGroupOfSurjective π hπsurj
  have hVexp : ∀ v : V, v ^ 3 = 1 := by
    intro v
    obtain ⟨w, rfl⟩ := hπsurj v
    calc π w ^ 3 = π (w ^ 3) := (map_pow π w 3).symm
      _ = π 1 := by rw [qTwoLMDivStab_vec_pow]
      _ = 1 := map_one π
  have hroot_mem : ∀ i j : Fin m, π (qTwoLMDivStab_e i j) ∈ U := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [qTwoLMDivStab_e_self, map_one]
      exact one_mem U
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    have hik : i ≠ k := fun h => hki h.symm
    have hjk : j ≠ k := fun h => hkj h.symm
    let c : Equiv.Perm (Fin m) := Equiv.swap i j * Equiv.swap j k
    have hc3 : c ^ 3 = 1 := qTwoLMDivStab_threeCycle_cube hij hjk hik
    have hci : c i = j := qTwoLMDivStab_threeCycle_left hij hjk hik
    have hVUcard : Nat.card (V ⧸ U) ≤ 3 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup U] at hUcard
      exact le_of_mul_le_mul_right hUcard (Nat.card_pos)
    have hVUexp : ∀ q : V ⧸ U, q ^ 3 = 1 := by
      intro q
      refine QuotientGroup.induction_on q ?_
      intro v
      change (QuotientGroup.mk' U v) ^ 3 = 1
      rw [← map_pow (QuotientGroup.mk' U) v 3, hVexp v, map_one]
    have hUle : U ≤ U.comap ((ρ c).toMonoidHom) := hUst c
    let f : V ⧸ U →* V ⧸ U :=
      QuotientGroup.map (N := U) (M := U) (ρ c).toMonoidHom hUle
    have hρc3 : (ρ c) ^ 3 = 1 := by simpa [hc3] using (map_pow ρ c 3).symm
    have hf_apply : ∀ x : V,
        f (QuotientGroup.mk x) = QuotientGroup.mk ((ρ c) x) := by
      intro x
      exact QuotientGroup.map_mk (N := U) (M := U) ((ρ c).toMonoidHom) hUle x
    have hf : ∀ q, f (f (f q)) = q := by
      intro q
      refine QuotientGroup.induction_on q ?_
      intro v
      have h3v : (ρ c) ((ρ c) ((ρ c) v)) = v := by
        simpa [pow_succ] using congrArg (fun g : MulAut V => g v) hρc3
      calc f (f (f (QuotientGroup.mk v)))
          = QuotientGroup.mk ((ρ c) ((ρ c) ((ρ c) v))) := by
            rw [hf_apply, hf_apply, hf_apply]
        _ = QuotientGroup.mk v := by rw [h3v]
    have hfixf : ∀ q, f q = q := qTwoLMDivStab_endo_cube hVUcard hVUexp f hf
    have hQuot : ∀ v : V, (ρ c) v * v⁻¹ ∈ U := by
      intro v
      have hq : (QuotientGroup.mk ((ρ c) v) : V ⧸ U) = QuotientGroup.mk v := by
        simpa [f, QuotientGroup.map_mk] using hfixf (QuotientGroup.mk v)
      have hq' : (ρ c) v / v ∈ U := QuotientGroup.eq_iff_div_mem.mp hq
      simpa [div_eq_mul_inv] using hq' 
    let g : Multiplicative (ZMod 3) := Multiplicative.ofAdd (1 : ZMod 3)
    have hstep : (ρ c) (π (Pi.mulSingle i g)) * (π (Pi.mulSingle i g))⁻¹ ∈ U :=
      hQuot _
    have heq1 : (ρ c) (π (Pi.mulSingle i g)) = π (Pi.mulSingle j g) := by
      calc (ρ c) (π (Pi.mulSingle i g))
          = π (SpCoord.permAut c (Pi.mulSingle i g)) :=
            (hπequiv c (Pi.mulSingle i g)).symm
        _ = π (Pi.mulSingle (c i) g) := by
            rw [qTwoLMDivStab_permAut_mulSingle]
        _ = π (Pi.mulSingle j g) := by rw [hci]
    have hmemji : π (qTwoLMDivStab_e j i) ∈ U := by
      have h : π (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))) *
          (π (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3))))⁻¹ ∈ U := by
        simpa [g, heq1] using hstep
      have h2 : π (qTwoLMDivStab_e j i) =
          π (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))) *
            (π (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 3))))⁻¹ := by
        rw [qTwoLMDivStab_e, map_mul]
        congr 1
        exact map_inv π _
      rwa [h2] 
    have he : qTwoLMDivStab_e i j = (qTwoLMDivStab_e j i)⁻¹ := by
      rw [← qTwoLMDivStab_e_inv hij]
      exact (inv_inv _).symm
    have hπinv : π (qTwoLMDivStab_e i j) = (π (qTwoLMDivStab_e j i))⁻¹ := by
      calc π (qTwoLMDivStab_e i j) = π ((qTwoLMDivStab_e j i)⁻¹) := by rw [he]
        _ = (π (qTwoLMDivStab_e j i))⁻¹ := map_inv π _
    rw [hπinv]
    exact U.inv_mem hmemji
  have hcomm : ∀ σ : Equiv.Perm (Fin m), ψ * ρ σ = ρ σ * ψ := by
    intro σ
    obtain ⟨σ', hσ'⟩ := hψ σ
    let τ : Equiv.Perm (Fin m) := σ⁻¹ * σ'
    have hτfix : ∀ u ∈ U, ρ τ u = u := by
      intro u hu
      have hψinv : ψ⁻¹ u = u := by
        calc ψ⁻¹ u = ψ⁻¹ (ψ u) := by rw [hfix u hu]
          _ = u := by simp
      have hσ'u : ρ σ' u = ρ σ u := by
        have h := congrArg (fun g : MulAut V => g u) hσ'
        simpa [MulAut.mul_apply, hψinv, hfix (ρ σ u) (hUst σ u hu)] using h.symm
      change (ρ (σ⁻¹ * σ')) u = u
      rw [map_mul, MulAut.mul_apply, hσ'u, ← MulAut.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, MulAut.one_apply]
    have hτ : τ = 1 := by
      ext i
      obtain ⟨j, hji, -⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by omega)
      have hij : i ≠ j := hji.symm
      obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
      have hik : i ≠ k := fun h => hki h.symm
      have hjk : j ≠ k := fun h => hkj h.symm
      let c : Equiv.Perm (Fin m) := Equiv.swap i j * Equiv.swap j k
      have hc3 : c ^ 3 = 1 := qTwoLMDivStab_threeCycle_cube hij hjk hik
      have hci : c i = j := qTwoLMDivStab_threeCycle_left hij hjk hik
      obtain ⟨l, hli, hlj, hlτi, hlτj⟩ :=
        qTwoLMDivStab_exists_four hm i j (τ i) (τ j)
      have hπτ : π (qTwoLMDivStab_e (τ i) (τ j)) = π (qTwoLMDivStab_e i j) := by
        calc π (qTwoLMDivStab_e (τ i) (τ j))
            = ρ τ (π (qTwoLMDivStab_e i j)) := by
              rw [← qTwoLMDivStab_permAut_e τ i j]
              exact hπequiv τ (qTwoLMDivStab_e i j)
          _ = π (qTwoLMDivStab_e i j) := hτfix _ (hroot_mem i j)
      have hτne : τ i ≠ τ j := fun h => hij (τ.injective h)
      have hker : qTwoLMDivStab_e (τ i) (τ j) * (qTwoLMDivStab_e i j)⁻¹ ∈
          Subgroup.zpowers (fun _ => Multiplicative.ofAdd (1 : ZMod 3)) := by
        rw [← hπker]
        calc π (qTwoLMDivStab_e (τ i) (τ j) * (qTwoLMDivStab_e i j)⁻¹)
            = π (qTwoLMDivStab_e (τ i) (τ j)) *
                π ((qTwoLMDivStab_e i j)⁻¹) := map_mul π _ _
          _ = π (qTwoLMDivStab_e (τ i) (τ j)) *
                (π (qTwoLMDivStab_e i j))⁻¹ :=
              congrArg (fun y => π (qTwoLMDivStab_e (τ i) (τ j)) * y)
                (map_inv π (qTwoLMDivStab_e i j))
          _ = π (qTwoLMDivStab_e i j) * (π (qTwoLMDivStab_e i j))⁻¹ := by rw [hπτ]
          _ = 1 := mul_inv_cancel _
      have hconst := (qTwoLMDivStab_ker_const (i₀ := l) _).mp hker
      have hlval : (qTwoLMDivStab_e (τ i) (τ j) *
          (qTwoLMDivStab_e i j)⁻¹) l = 1 := by
        rw [Pi.mul_apply, Pi.inv_apply,
          qTwoLMDivStab_e_apply_of_ne hlτi hlτj,
          qTwoLMDivStab_e_apply_of_ne hli hlj]
        exact mul_inv_cancel _
      have heq : qTwoLMDivStab_e (τ i) (τ j) = qTwoLMDivStab_e i j := by
        funext x
        have hx := hconst x
        rw [hlval] at hx
        rw [Pi.mul_apply, Pi.inv_apply] at hx
        exact mul_inv_eq_one.mp hx
      exact congrArg Fin.val (qTwoLMDivStab_e_injective hτne hij heq).1
    have hτ' : σ⁻¹ * σ' = 1 := by simpa [τ] using hτ
    have hσ'eq : σ' = σ := by
      rw [← mul_one σ, ← hτ', ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hσ'eq] at hσ'
    calc ψ * ρ σ = (ψ * ρ σ * ψ⁻¹) * ψ := by group
      _ = ρ σ * ψ := by rw [hσ']
  let χ : V →* V :=
    { toFun := fun v => ψ v * v⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        simp [map_mul, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] }
  have hχ_triv : ∀ u ∈ U, χ u = 1 := by
    intro u hu
    simpa [χ, hfix u hu]
  have hχ_equiv : ∀ (σ : Equiv.Perm (Fin m)) (v : V), χ (ρ σ v) = ρ σ (χ v) := by
    intro σ v
    dsimp [χ]
    rw [← MulAut.mul_apply, hcomm σ, MulAut.mul_apply]; simp [map_mul, map_inv]
  have hχ_range_le : Nat.card χ.range ≤ 3 := by
    have hker_le : U ≤ χ.ker := by
      intro u hu
      rw [MonoidHom.mem_ker]
      exact hχ_triv u hu
    have hcard_quot : Nat.card (V ⧸ χ.ker) ≤ Nat.card (V ⧸ U) := by
      have hindex_dvd : (χ.ker).index ∣ U.index := Subgroup.index_dvd_of_le hker_le
      rw [Subgroup.index_eq_card, Subgroup.index_eq_card] at hindex_dvd
      exact Nat.le_of_dvd (Nat.card_pos) hindex_dvd
    have hiso : Nat.card χ.range = Nat.card (V ⧸ χ.ker) := by
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv.symm
    rw [hiso]
    have hVU : Nat.card (V ⧸ U) ≤ 3 := by
      have hmul : Nat.card V = Nat.card (V ⧸ U) * Nat.card U :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup U
      rw [hmul] at hUcard
      exact le_of_mul_le_mul_right hUcard (Nat.card_pos)
    exact le_trans hcard_quot hVU
  have hχ_range_stable : ∀ (σ : Equiv.Perm (Fin m)) (x : V), x ∈ χ.range → ρ σ x ∈ χ.range := by
    intro σ x hx
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨ρ σ v, hχ_equiv σ v⟩
  have hχ_range_bot : χ.range = ⊥ := by
    have hRexp : ∀ q : χ.range, q ^ 3 = 1 := by
      intro q
      obtain ⟨x, hx⟩ := q.2
      apply Subtype.ext
      change (q : V) ^ 3 = 1
      rw [← hx, ← map_pow, hVexp x, map_one]
    have hfix_cycle : ∀ (c : Equiv.Perm (Fin m)), c ^ 3 = 1 →
        ∀ x ∈ χ.range, ρ c x = x := by
      intro c hc3 x hx
      let f : χ.range →* χ.range :=
        ((ρ c).toMonoidHom.comp χ.range.subtype).codRestrict χ.range
          (fun y => hχ_range_stable c y y.2)
      have hρc3 : (ρ c) ^ 3 = 1 := by simpa [hc3] using (map_pow ρ c 3).symm
      have hf : ∀ q, f (f (f q)) = q := by
        intro q
        apply Subtype.ext
        change (ρ c) ((ρ c) ((ρ c) (q : V))) = (q : V)
        have h := congrArg (fun g : MulAut V => g (q : V)) hρc3
        simpa [pow_succ] using h
      have hfixf : ∀ q, f q = q := qTwoLMDivStab_endo_cube hχ_range_le hRexp f hf
      have hfx : f ⟨x, hx⟩ = ⟨x, hx⟩ := hfixf ⟨x, hx⟩
      simpa [f, MonoidHom.codRestrict_apply] using congrArg Subtype.val hfx
    apply le_antisymm _ bot_le
    intro w hw
    rw [Subgroup.mem_bot]
    obtain ⟨v, rfl⟩ := hπsurj w
    have hvconst : ∀ i j : Fin m, v i = v j := by
      intro i j
      by_cases hij : i = j
      · subst hij; rfl
      obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
      have hik : i ≠ k := fun h => hki h.symm
      have hjk : j ≠ k := fun h => hkj h.symm
      obtain ⟨l, hli, hlj, hlk⟩ := qTwoLMDivStab_exists_three hm i j k
      let c : Equiv.Perm (Fin m) := Equiv.swap i j * Equiv.swap j k
      have hc3 : c ^ 3 = 1 := qTwoLMDivStab_threeCycle_cube hij hjk hik
      have hci : c i = j := qTwoLMDivStab_threeCycle_left hij hjk hik
      have hcl : c l = l := qTwoLMDivStab_threeCycle_other hij hjk hik hli hlj hlk
      have hfixc : ρ c (π v) = π v := hfix_cycle c hc3 (π v) hw
      have hequiv : π (fun x => v (c⁻¹ x)) = π v := (hπequiv c v).trans hfixc
      have hker : (fun x => v (c⁻¹ x)) * v⁻¹ ∈
          Subgroup.zpowers (fun _ => Multiplicative.ofAdd (1 : ZMod 3)) := by
        rw [← hπker]
        calc π ((fun x => v (c⁻¹ x)) * v⁻¹)
            = π (fun x => v (c⁻¹ x)) * π (v⁻¹) := map_mul π _ _
          _ = π (fun x => v (c⁻¹ x)) * (π v)⁻¹ :=
              congrArg (fun y => π (fun x => v (c⁻¹ x)) * y) (map_inv π v)
          _ = π v * (π v)⁻¹ := by rw [hequiv]
          _ = 1 := mul_inv_cancel _
      have hconst := (qTwoLMDivStab_ker_const (i₀ := l) _).mp hker
      have hcl_inv : c⁻¹ l = l := (Equiv.Perm.inv_eq_iff_eq).mpr hcl.symm
      have hlval : ((fun x => v (c⁻¹ x)) * v⁻¹) l = 1 := by
        rw [Pi.mul_apply, Pi.inv_apply, hcl_inv]; exact mul_inv_cancel _
      have hveq : (fun x => v (c⁻¹ x)) = v := by
        funext x
        have hx := hconst x
        rw [hlval, Pi.mul_apply, Pi.inv_apply] at hx
        exact mul_inv_eq_one.mp hx
      have hc_inv_j : c⁻¹ j = i := (Equiv.Perm.inv_eq_iff_eq).mpr hci.symm
      have := congrFun hveq j
      simpa [hc_inv_j] using this
    let i₀ : Fin m := ⟨0, by omega⟩
    have hvmem : v ∈ Subgroup.zpowers (fun _ => Multiplicative.ofAdd (1 : ZMod 3)) :=
      (qTwoLMDivStab_ker_const (i₀ := i₀) v).mpr (fun j => hvconst j i₀)
    exact (hπker v).mpr hvmem
  ext v
  have hχv : χ v = 1 := by
    have hmem : χ v ∈ χ.range := ⟨v, rfl⟩
    rw [hχ_range_bot] at hmem
    simpa using hmem
  have hψv : ψ v = v := by
    have h := congrArg (fun z => z * v) hχv
    dsimp [χ] at h
    simpa [mul_assoc] using h
  exact hψv

end CFSG.StandardType.QTwo

end
