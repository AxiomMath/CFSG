module

public import CFSG.RankThree.GF2n.Tim79aCitedSp
public import CFSG.RankThree.GF2n.Tim79aCitedSp62
public import CFSG.Timmesfeld.ARS.CaseMSkeleton
public import CFSG.Timmesfeld.ARS.CaseMSp

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Open Matrix CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.ARS.CaseM
open scoped commutatorElement

theorem tw_mul_conj_mem {Γ : Type} [Group Γ] {d₀ c : Γ} (hd₀ : d₀ * d₀ = 1) :
    d₀ * (c * d₀ * c⁻¹) ∈ commutator Γ := by
  have h : ⁅d₀, c⁆ ∈ commutator Γ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have e : d₀ * (c * d₀ * c⁻¹) = ⁅d₀, c⁆ := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hd₀]
    group
  rw [e]
  exact h

theorem tw_d0_mem {Γ : Type} [Group Γ] {d₀ d : Γ} (hd₀ : d₀ * d₀ = 1) (hd : IsConj d₀ d) :
    d₀ * d ∈ commutator Γ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hd
  rw [← hc]
  exact tw_mul_conj_mem hd₀

theorem tw_coset {Γ : Type} [Group Γ] (D : Set Γ) (d₀ : Γ) (hd₀ : d₀ * d₀ = 1)
    (hD : ∀ g, g ∈ D ↔ IsConj d₀ g) (hgen : Subgroup.closure D = ⊤) (g : Γ) :
    g ∈ commutator Γ ∨ d₀ * g ∈ commutator Γ := by
  have key : ∀ x ∈ Subgroup.closure D, x ∈ commutator Γ ∨ d₀ * x ∈ commutator Γ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Or.inr (tw_d0_mem hd₀ ((hD x).1 hx))
    | one => exact Or.inl (one_mem _)
    | mul x y _ _ hx hy =>
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (mul_mem hx hy)
      · refine Or.inr ?_
        have h1 := (inferInstance : (commutator Γ).Normal).conj_mem x hx d₀
        have e : d₀ * (x * y) = d₀ * x * d₀⁻¹ * (d₀ * y) := by group
        rw [e]
        exact mul_mem h1 hy
      · refine Or.inr ?_
        rw [← mul_assoc]
        exact mul_mem hx hy
      · refine Or.inl ?_
        have h1 := (inferInstance : (commutator Γ).Normal).conj_mem (d₀ * x) hx d₀
        have e : x * y = d₀ * (d₀ * x) * d₀⁻¹ * (d₀ * y) := by
          calc x * y = (d₀ * d₀) * x * y := by rw [hd₀, one_mul]
            _ = d₀ * (d₀ * x) * d₀⁻¹ * (d₀ * y) := by group
        rw [e]
        exact mul_mem h1 hy
    | inv x _ hx =>
      rcases hx with hx | hx
      · exact Or.inl (inv_mem hx)
      · refine Or.inr ?_
        have h1 := (inferInstance : (commutator Γ).Normal).conj_mem _ (inv_mem hx) d₀
        have e : d₀ * (d₀ * x)⁻¹ * d₀⁻¹ = d₀ * x⁻¹ := by
          calc d₀ * (d₀ * x)⁻¹ * d₀⁻¹ = d₀ * x⁻¹ * (d₀⁻¹ * d₀⁻¹) := by group
            _ = d₀ * x⁻¹ := by rw [← _root_.mul_inv_rev, hd₀, inv_one, mul_one]
        rw [← e]
        exact h1
  exact key g (by rw [hgen]; exact Subgroup.mem_top g)

theorem tw_comm_left {Γ : Type} [Group Γ] {c : Γ} (hc : ∀ g : Γ, c * g = g * c) (x y : Γ) :
    ⁅c * x, y⁆ = ⁅x, y⁆ := by
  have h : ∀ m : Γ, c * m * c⁻¹ = m := fun m => by
    rw [hc m, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅c * x, y⁆ = c * (x * y * x⁻¹) * c⁻¹ * y⁻¹ := by
        rw [commutatorElement_def]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem tw_comm_right {Γ : Type} [Group Γ] {c : Γ} (hc : ∀ g : Γ, c * g = g * c) (x y : Γ) :
    ⁅x, c * y⁆ = ⁅x, y⁆ := by
  have h : ∀ m : Γ, c * m * c⁻¹ = m := fun m => by
    rw [hc m, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅x, c * y⁆ = c * (x * y * x⁻¹ * y⁻¹) * c⁻¹ := by
        rw [commutatorElement_def, ← mul_assoc x c y, ← hc x]; group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem tw_commutator_top {Γ : Type} [Group Γ] (Z : Subgroup Γ) (hZ : Z ≤ Subgroup.center Γ)
    (hZG : ∀ g : Γ, ∃ c ∈ Z, ∃ y ∈ commutator Γ, g = c * y) :
    commutator (commutator Γ) = ⊤ := by
  have hK : commutator Γ ≤ (commutator (commutator Γ)).map (commutator Γ).subtype := by
    refine Subgroup.commutator_le.2 ?_
    intro x _ y _
    obtain ⟨c, hc, x', hx', rfl⟩ := hZG x
    obtain ⟨c', hc', y', hy', rfl⟩ := hZG y
    have hcc : ∀ g : Γ, c * g = g * c := fun g => (Subgroup.mem_center_iff.1 (hZ hc) g).symm
    have hcc' : ∀ g : Γ, c' * g = g * c' := fun g => (Subgroup.mem_center_iff.1 (hZ hc') g).symm
    rw [tw_comm_left hcc, tw_comm_right hcc']
    exact Subgroup.mem_map.2 ⟨⁅(⟨x', hx'⟩ : ↥(commutator Γ)), ⟨y', hy'⟩⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), rfl⟩
  rw [eq_top_iff]
  intro w _
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 (hK w.2)
  have huw : u = w := Subtype.ext hu'
  rw [← huw]
  exact hu

theorem tw_orderOf_four {G : Type} [Group G] {z w t s : G} (hz : ∀ g : G, z * g = g * z)
    (hw : ∀ g : G, w * g = g * w) (hw1 : w ≠ 1) (hw2 : w * w = 1) (ht : t * t = w)
    (hs : s * s = w) (hts : t * s = w * (s * t)) (hd : z * t * (z * t) = 1) :
    orderOf (z * t * (z * s)) = 4 := by
  have hwc : ∀ X Y : G, X * (w * Y) = w * (X * Y) := fun X Y => by
    rw [← mul_assoc, ← hw X, mul_assoc]
  have hzz : z * z = w := by
    have e1 : z * t * (z * t) = z * z * (t * t) := by
      calc z * t * (z * t) = z * (t * z) * t := by simp only [mul_assoc]
        _ = z * (z * t) * t := by rw [← hz t]
        _ = z * z * (t * t) := by simp only [mul_assoc]
    have h1 : z * z * w = 1 := by rw [← ht, ← e1, hd]
    calc z * z = z * z * (w * w) := by rw [hw2, mul_one]
      _ = z * z * w * w := by simp only [mul_assoc]
      _ = w := by rw [h1, one_mul]
  have hst : s * t = w * (t * s) := by
    rw [hts, ← mul_assoc, hw2, one_mul]
  have hts2 : t * s * (t * s) = w := by
    calc t * s * (t * s) = t * (s * t) * s := by simp only [mul_assoc]
      _ = t * (w * (t * s)) * s := by rw [hst]
      _ = w * (t * (t * s)) * s := by rw [hwc]
      _ = w * (t * t) * (s * s) := by simp only [mul_assoc]
      _ = w * w * w := by rw [ht, hs]
      _ = w := by rw [hw2, one_mul]
  have hu : z * t * (z * s) = w * (t * s) := by
    calc z * t * (z * s) = z * (t * z) * s := by simp only [mul_assoc]
      _ = z * (z * t) * s := by rw [← hz t]
      _ = z * z * (t * s) := by simp only [mul_assoc]
      _ = w * (t * s) := by rw [hzz]
  have hu2 : (z * t * (z * s)) * (z * t * (z * s)) = w := by
    rw [hu]
    calc w * (t * s) * (w * (t * s)) = w * ((t * s) * (w * (t * s))) := by simp only [mul_assoc]
      _ = w * (w * ((t * s) * (t * s))) := by rw [hwc]
      _ = w * w * ((t * s) * (t * s)) := by simp only [mul_assoc]
      _ = w := by rw [hw2, one_mul, hts2]
  have hu2' : (z * t * (z * s)) ^ 2 = w := by
    rw [sq]
    exact hu2
  have hnot : ¬ (z * t * (z * s)) ^ 2 ^ 1 = 1 := by
    rw [pow_one, hu2']
    exact hw1
  have hfin : (z * t * (z * s)) ^ 2 ^ (1 + 1) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hu2', sq, hw2]
  have h4 := orderOf_eq_prime_pow hnot hfin
  exact h4.trans (by norm_num)

theorem tw_spTrans_one (v : Fin 3 ⊕ Fin 3 → GaloisField 2 1) :
    spTrans v 1 = 1 + vecMulVec v (v ᵥ* (fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1))) := by
  simp [spTrans, spNil, spGram]

theorem tw_orth_pair : ∃ v v' : Fin 3 ⊕ Fin 3 → GaloisField 2 1, v ≠ 0 ∧ v' ≠ 0 ∧ v ≠ v' ∧
    spForm v v' = 0 := by
  refine ⟨Pi.single (Sum.inl 0) 1, Pi.single (Sum.inl 1) 1, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h (Sum.inl 0)
    simp at this
  · intro h
    have := congrFun h (Sum.inl 1)
    simp at this
  · intro h
    have := congrFun h (Sum.inl 0)
    simp at this
  · simp [spForm, spGram, dotProduct, Matrix.mulVec, Pi.single_apply, fromBlocks]

theorem tw_ker_n3 {Γ : Type} [Group Γ] [Finite Γ] (D : Set Γ)
    (hdeg : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4) (hinv : ∀ d ∈ D, d * d = 1)
    (φ₀ : Γ →* StatedSp 3 (GaloisField 2 1)) (hsurj : Function.Surjective φ₀)
    (hker : φ₀.ker = Subgroup.center Γ)
    (hD2 : ∀ v : Fin 3 ⊕ Fin 3 → GaloisField 2 1, v ≠ 0 →
      ∃ d ∈ D, SpExtras.mat 3 (GaloisField 2 1) (φ₀ d) = spTrans v 1)
    (hGrE : GriessSpMultiplierExceptionStatement) (hS : Sp62CoverLiftStatement)
    (ψ : commutator Γ →* StatedSp 3 (GaloisField 2 1)) (hψ : ∀ x, ψ x = φ₀ x.1)
    (hZG : ∀ g : Γ, ∃ c ∈ Subgroup.center Γ, ∃ y ∈ commutator Γ, g = c * y)
    (hperf : commutator (commutator Γ) = ⊤)
    (z : Γ) (hzZ : z ∈ Subgroup.center Γ) (hzt : ∀ d ∈ D, z⁻¹ * d ∈ commutator Γ) :
    ψ.ker = ⊥ := by
  have hZmem : ∀ x : Γ, φ₀ x = 1 ↔ x ∈ Subgroup.center Γ := fun x => by
    rw [← hker, MonoidHom.mem_ker]
  have hKmem : ∀ x : ↥(commutator Γ), ψ x = 1 ↔ x.1 ∈ Subgroup.center Γ := fun x => by
    rw [hψ, hZmem]
  have hsurjψ : Function.Surjective ψ := by
    intro g
    obtain ⟨x, rfl⟩ := hsurj g
    obtain ⟨c, hc, y, hy, rfl⟩ := hZG x
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hψ, map_mul, (hZmem c).2 hc, one_mul]
  have hcenter : ψ.ker ≤ Subgroup.center (commutator Γ) := by
    intro x hx
    rw [MonoidHom.mem_ker, hKmem] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hx g.1
  have hle : ψ.ker ≤ commutator (commutator Γ) := by
    rw [hperf]
    exact le_top
  by_contra hne
  have hle1 : Nat.card ψ.ker ≤ 2 :=
    (hGrE 3 1 (Or.inr (Or.inr rfl))).1 (commutator Γ) ψ hsurjψ hcenter hle
  have hgt : 1 < Nat.card ψ.ker := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hcard : Nat.card ψ.ker = 2 := by omega
  obtain ⟨y, hy1, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥ψ.ker)).1 hcard
  have hyZ : y.1.1 ∈ Subgroup.center Γ := (hKmem y.1).1 (MonoidHom.mem_ker.1 y.2)
  have hyne : y.1.1 ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  obtain ⟨a, ha⟩ : ∃ a : Γ, a = y.1.1 := ⟨_, rfl⟩
  have haZ : a ∈ Subgroup.center Γ := by
    rw [ha]
    exact hyZ
  have hw1 : a ≠ 1 := by
    rw [ha]
    exact hyne
  have huniq : ∀ k : ↥(commutator Γ), ψ k = 1 → k.1 ≠ 1 → k.1 = a := by
    intro k hk hk1
    have hkmem : k ∈ ψ.ker := MonoidHom.mem_ker.2 hk
    have h1 : (⟨k, hkmem⟩ : ↥ψ.ker) ≠ 1 := by
      intro h
      exact hk1 (congrArg (fun q : ↥ψ.ker => q.1.1) h)
    have h3 := hyuniq ⟨k, hkmem⟩ h1
    rw [ha]
    exact congrArg (fun q : ↥ψ.ker => q.1.1) h3
  have hzi : ∀ g : Γ, z⁻¹ * g = g * z⁻¹ := fun g =>
    (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hzZ) g).symm
  have hsq : ∀ (u : ↥(commutator Γ)) (x : Γ), (u : Γ) = z⁻¹ * x → x * x = 1 →
      orderOf u = 4 → (u : Γ) * (u : Γ) = a := by
    intro u x hux hxx hord
    have hcalc : (u : Γ) * (u : Γ) = z⁻¹ * z⁻¹ := by
      rw [hux]
      calc z⁻¹ * x * (z⁻¹ * x) = z⁻¹ * (x * (z⁻¹ * x)) := by simp only [mul_assoc]
        _ = z⁻¹ * ((x * z⁻¹) * x) := by simp only [mul_assoc]
        _ = z⁻¹ * ((z⁻¹ * x) * x) := by rw [← hzi x]
        _ = z⁻¹ * (z⁻¹ * (x * x)) := by simp only [mul_assoc]
        _ = z⁻¹ * z⁻¹ := by rw [hxx, mul_one]
    have hmemZ : (u * u : ↥(commutator Γ)).1 ∈ Subgroup.center Γ := by
      show (u : Γ) * (u : Γ) ∈ Subgroup.center Γ
      rw [hcalc]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzZ) (Subgroup.inv_mem _ hzZ)
    have hmemK : u * u ∈ ψ.ker := MonoidHom.mem_ker.2 ((hKmem (u * u)).2 hmemZ)
    have hpow : u ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf two_ne_zero (by rw [hord]; norm_num)
    have hne' : u * u ≠ 1 := by
      rw [← sq]
      exact hpow
    have h1 : (⟨u * u, hmemK⟩ : ↥ψ.ker) ≠ 1 := by
      intro h
      exact hne' (congrArg (fun q : ↥ψ.ker => q.1) h)
    have h2 := hyuniq ⟨u * u, hmemK⟩ h1
    rw [ha]
    exact congrArg (fun q : ↥ψ.ker => q.1.1) h2
  obtain ⟨v, v', hv, hv', hvv', hB⟩ := tw_orth_pair
  obtain ⟨d, hdD, hdmat⟩ := hD2 v hv
  obtain ⟨e, heD, hemat⟩ := hD2 v' hv'
  obtain ⟨t, ht⟩ : ∃ t : ↥(commutator Γ), (t : Γ) = z⁻¹ * d :=
    ⟨⟨z⁻¹ * d, hzt d hdD⟩, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ↥(commutator Γ), (s : Γ) = z⁻¹ * e :=
    ⟨⟨z⁻¹ * e, hzt e heD⟩, rfl⟩
  have hφzi : φ₀ z⁻¹ = 1 := by
    rw [map_inv, (hZmem z).2 hzZ, inv_one]
  have hψt : SpExtras.mat 3 (GaloisField 2 1) (ψ t) = spTrans v 1 := by
    rw [hψ, ht, map_mul, hφzi, one_mul]
    exact hdmat
  have hψs : SpExtras.mat 3 (GaloisField 2 1) (ψ s) = spTrans v' 1 := by
    rw [hψ, hs, map_mul, hφzi, one_mul]
    exact hemat
  have hcond_t := hψt.trans (tw_spTrans_one v)
  have hcond_s := hψs.trans (tw_spTrans_one v')
  have hS1 := hS (commutator Γ) ψ hsurjψ hcenter hcard hperf t s v v' hv hv' hcond_t hcond_s
  have hS2 := hS (commutator Γ) ψ hsurjψ hcenter hcard hperf s t v' v hv' hv hcond_s hcond_t
  have hordt : orderOf t = 4 := hS1.1
  have hords : orderOf s = 4 := hS2.1
  have hnc : t * s ≠ s * t := hS1.2 hvv' hB
  have hcomm_ts : ψ (t * s) = ψ (s * t) := by
    apply SpExtras.mat_injective
    simp only [map_mul]
    rw [hψt, hψs]
    exact CFSG.Timmesfeld.ARS.CaseM.spTrans_commute_of_spForm_eq_zero hB 1 1
  have hc_one : ψ (t * s * (s * t)⁻¹) = 1 := by
    rw [map_mul ψ (t * s), map_inv ψ, hcomm_ts, mul_inv_cancel]
  have hcne : (t * s * (s * t)⁻¹ : ↥(commutator Γ)).1 ≠ 1 := fun h =>
    hnc (mul_inv_eq_one.1 (Subtype.ext h))
  have hcy := huniq _ hc_one hcne
  have hcy' : (t : Γ) * (s : Γ) = a * ((s : Γ) * (t : Γ)) := by
    have h := hcy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hzt_d : z * (t : Γ) = d := by
    rw [ht, mul_inv_cancel_left]
  have hzs_e : z * (s : Γ) = e := by
    rw [hs, mul_inv_cancel_left]
  have htt : (t : Γ) * (t : Γ) = a := hsq t d ht (hinv d hdD) hordt
  have hss : (s : Γ) * (s : Γ) = a := hsq s e hs (hinv e heD) hords
  have hw2 : a * a = 1 := by
    have h4 : (t : Γ) ^ 4 = 1 := by
      have h := pow_orderOf_eq_one t
      rw [hordt] at h
      simpa using congrArg Subtype.val h
    rw [← htt]
    calc (t : Γ) * (t : Γ) * ((t : Γ) * (t : Γ)) = (t : Γ) ^ 4 := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
      _ = 1 := h4
  have hd : z * (t : Γ) * (z * (t : Γ)) = 1 := by
    rw [hzt_d]
    exact hinv d hdD
  have hP1 := tw_orderOf_four (z := z) (w := a) (t := (t : Γ)) (s := (s : Γ))
    (fun g => (Subgroup.mem_center_iff.1 hzZ g).symm)
    (fun g => (Subgroup.mem_center_iff.1 haZ g).symm) hw1 hw2 htt hss hcy' hd
  have hde : d * e = z * (t : Γ) * (z * (s : Γ)) := by
    rw [hzt_d, hzs_e]
  exact hdeg d hdD e heD (by rw [hde]; exact hP1)

theorem twisted_split
    {Γ : Type} [Group Γ] [Finite Γ] (D : Set Γ) {n : ℕ} (hn : 2 ≤ n)
    (hcls : ∃ d₀, D = {g | IsConj d₀ g}) (hinv : ∀ d ∈ D, d * d = 1)
    (hgen : Subgroup.closure D = ⊤) (hdeg : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≠ 4)
    (φ₀ : Γ →* StatedSp n (GaloisField 2 1)) (hsurj : Function.Surjective φ₀)
    (hker : φ₀.ker = Subgroup.center Γ)
    (hD2 : ∀ v : Fin n ⊕ Fin n → GaloisField 2 1, v ≠ 0 →
      ∃ d ∈ D, SpExtras.mat n (GaloisField 2 1) (φ₀ d) = spTrans v 1)
    (hcomm : ¬ Subgroup.center Γ ≤ commutator Γ)
    (hP2 : commutator (StatedSp 2 (GaloisField 2 1)) ≠ ⊤)
    (hGr : GriessSpMultiplierStatement) (hGrE : GriessSpMultiplierExceptionStatement)
    (hS : Sp62CoverLiftStatement) :
    3 ≤ n ∧ ∃ z₀ : Γ, z₀ ∈ Subgroup.center Γ ∧ z₀ ≠ 1 ∧ z₀ * z₀ = 1 ∧
      Subgroup.center Γ = Subgroup.zpowers z₀ ∧
      Subgroup.center Γ ⊓ commutator Γ = ⊥ ∧ Subgroup.center Γ ⊔ commutator Γ = ⊤ ∧
      (∀ d ∈ D, d ∉ commutator Γ ∧ z₀ * d ∈ commutator Γ) ∧
      (∀ d ∈ D, ∀ e ∈ D, φ₀ d = φ₀ e → d = e) := by
  obtain ⟨d₀, hD⟩ := hcls
  have hmem : ∀ g, g ∈ D ↔ IsConj d₀ g := by
    intro g
    rw [hD]
    rfl
  have hd₀D : d₀ ∈ D := (hmem d₀).2 (IsConj.refl d₀)
  have hd₀ : d₀ * d₀ = 1 := hinv d₀ hd₀D
  have hD0 : ∀ d ∈ D, d₀ * d ∈ commutator Γ := fun d hd => tw_d0_mem hd₀ ((hmem d).1 hd)
  have hcos : ∀ g : Γ, g ∈ commutator Γ ∨ d₀ * g ∈ commutator Γ :=
    fun g => tw_coset D d₀ hd₀ hmem hgen g
  have hDnot : ∀ d ∈ D, d ∉ commutator Γ := by
    intro d hd hdG
    have hDsub : D ⊆ commutator Γ := by
      intro e he
      have hde : IsConj d e := ((hmem d).1 hd).symm.trans ((hmem e).1 he)
      obtain ⟨c, hc⟩ := isConj_iff.1 hde
      rw [← hc]
      exact (inferInstance : (commutator Γ).Normal).conj_mem d hdG c
    have htop : Subgroup.closure D ≤ commutator Γ := (Subgroup.closure_le _).2 hDsub
    rw [hgen] at htop
    exact hcomm (by intro x _; exact htop (Subgroup.mem_top x))
  obtain ⟨z, hzZ, hzG⟩ : ∃ z ∈ Subgroup.center Γ, z ∉ commutator Γ := by
    by_contra h
    push Not at h
    exact hcomm (by intro x hx; exact h x hx)
  have hzc : ∀ g : Γ, z * g = g * z := fun g => (Subgroup.mem_center_iff.1 hzZ g).symm
  have hdz : d₀ * z ∈ commutator Γ := (hcos z).resolve_left hzG
  have hkey : ∀ g : Γ, (d₀ * z) * (d₀ * g) = z * g := by
    intro g
    calc (d₀ * z) * (d₀ * g) = (z * d₀) * (d₀ * g) := by rw [← hzc d₀]
      _ = z * (d₀ * d₀) * g := by simp only [mul_assoc]
      _ = z * g := by rw [hd₀, mul_one]
  have hZG : ∀ g : Γ, ∃ c ∈ Subgroup.center Γ, ∃ y ∈ commutator Γ, g = c * y := by
    intro g
    rcases hcos g with hg | hg
    · exact ⟨1, Subgroup.one_mem _, g, hg, (one_mul g).symm⟩
    · refine ⟨z, hzZ, z⁻¹ * g, ?_, (mul_inv_cancel_left z g).symm⟩
      have e : z⁻¹ * g = (d₀ * z)⁻¹ * (d₀ * g) := by group
      rw [e]
      exact mul_mem (inv_mem hdz) hg
  have hzt : ∀ d ∈ D, z⁻¹ * d ∈ commutator Γ := fun d hd => by
    have e : z⁻¹ * d = (d₀ * z)⁻¹ * (d₀ * d) := by group
    rw [e]
    exact mul_mem (inv_mem hdz) (hD0 d hd)
  have hZmem : ∀ x : Γ, φ₀ x = 1 ↔ x ∈ Subgroup.center Γ := fun x => by
    rw [← hker, MonoidHom.mem_ker]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : commutator Γ →* StatedSp n (GaloisField 2 1), ∀ x, ψ x = φ₀ x.1 :=
    ⟨φ₀.comp (commutator Γ).subtype, fun x => rfl⟩
  have hKmem : ∀ x : ↥(commutator Γ), ψ x = 1 ↔ x.1 ∈ Subgroup.center Γ := fun x => by
    rw [hψ, hZmem]
  have hsurjψ : Function.Surjective ψ := by
    intro g
    obtain ⟨x, rfl⟩ := hsurj g
    obtain ⟨c, hc, y, hy, rfl⟩ := hZG x
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hψ, map_mul, (hZmem c).2 hc, one_mul]
  have hcenter : ψ.ker ≤ Subgroup.center (commutator Γ) := by
    intro x hx
    rw [MonoidHom.mem_ker, hKmem] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hx g.1
  have hperf : commutator (commutator Γ) = ⊤ :=
    tw_commutator_top (Subgroup.center Γ) le_rfl hZG
  have hle : ψ.ker ≤ commutator (commutator Γ) := by
    rw [hperf]
    exact le_top
  have hn3 : 3 ≤ n := by
    by_contra hlt
    obtain rfl : n = 2 := by omega
    have hT : (⊤ : Subgroup (StatedSp 2 (GaloisField 2 1))) = (⊤ : Subgroup Γ).map φ₀ :=
      (Subgroup.map_top_of_surjective φ₀ hsurj).symm
    have h1 : (commutator Γ).map φ₀ = ⊤ := by
      rw [eq_top_iff]
      intro g _
      obtain ⟨x, rfl⟩ := hsurj g
      obtain ⟨c, hc, y, hy, rfl⟩ := hZG x
      refine Subgroup.mem_map.2 ⟨y, hy, ?_⟩
      rw [map_mul, (hZmem c).2 hc, one_mul]
    have h2 := Subgroup.map_commutator (f := φ₀) (H₁ := ⊤) (H₂ := ⊤)
    rw [← hT] at h2
    apply hP2
    rw [← h1]
    exact h2.symm
  have hbot : ψ.ker = ⊥ := by
    rcases (show n = 3 ∨ 4 ≤ n by omega) with h3 | h4
    · subst h3
      exact tw_ker_n3 D hdeg hinv φ₀ hsurj hker hD2 hGrE hS ψ hψ hZG hperf z hzZ hzt
    · exact hGr n 1 (by omega) le_rfl
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
        (by intro h; simp only [Prod.mk.injEq] at h; omega)
        (commutator Γ) ψ hsurjψ hcenter hle
  have hZ_inf : Subgroup.center Γ ⊓ commutator Γ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxZ, hxG⟩ := Subgroup.mem_inf.1 hx
    have hxk : (⟨x, hxG⟩ : ↥(commutator Γ)) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hψ]
      exact (hZmem x).2 hxZ
    rw [hbot, Subgroup.mem_bot] at hxk
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxk
  have hZ_sup : Subgroup.center Γ ⊔ commutator Γ = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨c, hc, y, hy, rfl⟩ := hZG g
    exact mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hy)
  have hz1 : z ≠ 1 := fun h => hzG (by rw [h]; exact Subgroup.one_mem _)
  have hzz : z * z = 1 := by
    have h1 : z * z ∈ Subgroup.center Γ ⊓ commutator Γ :=
      Subgroup.mem_inf.2 ⟨mul_mem hzZ hzZ, by rw [← hkey z]; exact mul_mem hdz hdz⟩
    rw [hZ_inf, Subgroup.mem_bot] at h1
    exact h1
  have hZ_zpow : Subgroup.center Γ = Subgroup.zpowers z := by
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_zpowers_iff]
      by_cases hyG : y ∈ commutator Γ
      · have hy1 : y = 1 := by
          have h1 : y ∈ Subgroup.center Γ ⊓ commutator Γ := Subgroup.mem_inf.2 ⟨hy, hyG⟩
          rw [hZ_inf, Subgroup.mem_bot] at h1
          exact h1
        exact ⟨0, by rw [zpow_zero, hy1]⟩
      · have hyc := (hcos y).resolve_left hyG
        have hzy : z⁻¹ * y ∈ commutator Γ := by
          have e : z⁻¹ * y = (d₀ * z)⁻¹ * (d₀ * y) := by group
          rw [e]
          exact mul_mem (inv_mem hdz) hyc
        have hzy' : z⁻¹ * y ∈ Subgroup.center Γ := mul_mem (inv_mem hzZ) hy
        have h1 : z⁻¹ * y = 1 := by
          have h2 : z⁻¹ * y ∈ Subgroup.center Γ ⊓ commutator Γ :=
            Subgroup.mem_inf.2 ⟨hzy', hzy⟩
          rw [hZ_inf, Subgroup.mem_bot] at h2
          exact h2
        exact ⟨1, by rw [zpow_one]; exact inv_mul_eq_one.1 h1⟩
    · exact Subgroup.zpowers_le.2 hzZ
  refine ⟨hn3, z, hzZ, hz1, hzz, hZ_zpow, hZ_inf, hZ_sup, ?_, ?_⟩
  · intro d hd
    refine ⟨hDnot d hd, ?_⟩
    rw [← hkey d]
    exact mul_mem hdz (hD0 d hd)
  · intro d hd e he hde
    have h1 : d⁻¹ * e ∈ Subgroup.center Γ := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hde, inv_mul_cancel]
    have h2 : d⁻¹ * e ∈ commutator Γ := by
      have e' : d⁻¹ * e = (d₀ * d)⁻¹ * (d₀ * e) := by group
      rw [e']
      exact mul_mem (inv_mem (hD0 d hd)) (hD0 e he)
    have h3 : d⁻¹ * e = 1 := by
      have h4 : d⁻¹ * e ∈ Subgroup.center Γ ⊓ commutator Γ := Subgroup.mem_inf.2 ⟨h1, h2⟩
      rw [hZ_inf, Subgroup.mem_bot] at h4
      exact h4
    exact inv_mul_eq_one.1 h3

end CFSG.RankThree.GF2n.Tim79a
