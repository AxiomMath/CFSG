module

public import CFSG.Quasithin.Recognition.SzR1Kernel

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem Zs_eq_one_or (C : FamCtx K1 L2 S Zs Ω) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) {x : G}
    (hx : x ∈ Zs) : x = 1 ∨ x = C.cm i₀ j₀ := by
  obtain ⟨e, he⟩ := C.exists_pow_zU hij hx
  have hsq := C.Zs_sq (C.cm_mem i₀ j₀)
  rcases Nat.even_or_odd e with ⟨r, hr⟩ | ⟨r, hr⟩
  · left
    rw [he, hr, ← two_mul, pow_mul, pow_two, hsq, one_pow]
  · right
    rw [he, hr, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]

theorem exists_inner_of_kerM [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hodd : Odd (Fintype.card Ω)) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) (l₀ : List Ω) (hl₀ : l₀.Nodup)
    (hall : ∀ i, i ∈ l₀)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    {m : G} (hm : m ∈ C.kerM) :
    ∃ w ∈ vBeta K1 L2 S Zs, w⁻¹ * m ∈ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) := by
  classical
  have hG := C.gramRel hij
  have hz : C.zU i₀ j₀ ≠ 1 := fun h => C.cm_ne_one hij (congrArg Subtype.val h)
  have hne : C.cm i₀ j₀ ≠ 1 := C.cm_ne_one hij
  have hz0Z : C.cm i₀ j₀ ∈ Zs := C.cm_mem i₀ j₀
  have hz2 : C.cm i₀ j₀ * C.cm i₀ j₀ = 1 := C.Zs_sq hz0Z
  have hpe : ∀ r : ℕ, C.cm i₀ j₀ ^ (r + r) = 1 := fun r => by
    rw [← two_mul, pow_mul, pow_two, hz2, one_pow]
  have hpo : ∀ r : ℕ, C.cm i₀ j₀ ^ (r + r + 1) = C.cm i₀ j₀ := fun r => by
    rw [pow_succ, hpe, one_mul]
  have hmH : m ∈ K1 ⊔ S := C.kerM_le_sup hm
  have hmc : m ∈ Subgroup.centralizer (Zs : Set G) := C.sup_le_centralizer_Zs hmH
  have hmZ : ∀ x ∈ Zs, m * x = x * m := fun x hx => (Subgroup.mem_centralizer_iff.mp hmc x hx).symm
  set c : Ω → G := fun i => m * C.zf i * m⁻¹ * (C.zf i)⁻¹ with hc
  have hcZ : ∀ i, c i ∈ Zs := fun i => C.commutator_kerM_vBeta_mem hm (C.zf_mem_U i)
  have hc01 : ∀ i, c i = 1 ∨ c i = C.cm i₀ j₀ := fun i => Zs_eq_one_or C hij (hcZ i)
  have hmz : ∀ i, m * C.zf i = c i * C.zf i * m := by
    intro i
    simp only [hc]
    group
  have hzW : ∀ g : ↥(vBeta K1 L2 S Zs), ∀ x ∈ Zs, (g : G) * x = x * g :=
    fun g x hx => C.Zs_central g.2 hx
  have hconj : ∀ l : List Ω, m * ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G) * m⁻¹ =
      C.cm i₀ j₀ ^ (l.countP (fun i => decide (c i ≠ 1))) *
        ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G) := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      have hgi : ((gprod C.wU (i :: l) : ↥(vBeta K1 L2 S Zs)) : G) =
          C.zf i * ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G) := by
        rw [gprod_cons]
        rfl
      have e1 : m * (C.zf i * ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G)) * m⁻¹ =
          (m * C.zf i * m⁻¹) * (m * ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G) * m⁻¹) := by
        group
      have e2 : m * C.zf i * m⁻¹ = c i * C.zf i := by
        simp only [hc]
        group
      have hpz : ∀ n : ℕ, C.zf i * C.cm i₀ j₀ ^ n = C.cm i₀ j₀ ^ n * C.zf i := fun n =>
        hzW (C.wU i) _ (Zs.pow_mem hz0Z n)
      rw [hgi, e1, e2, ih]
      rcases hc01 i with h1 | h1
      · have hcnt : (i :: l).countP (fun i => decide (c i ≠ 1)) =
            l.countP (fun i => decide (c i ≠ 1)) := by
          simp [h1]
        rw [hcnt, h1, one_mul]
        calc C.zf i * (C.cm i₀ j₀ ^ (l.countP (fun i => decide (c i ≠ 1))) *
              ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G))
            = (C.zf i * C.cm i₀ j₀ ^ (l.countP (fun i => decide (c i ≠ 1)))) *
              ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G) := by rw [mul_assoc]
          _ = _ := by rw [hpz, mul_assoc]
      · have hcnt : (i :: l).countP (fun i => decide (c i ≠ 1)) =
            l.countP (fun i => decide (c i ≠ 1)) + 1 := by
          simp [h1, hne]
        rw [hcnt, h1, pow_succ']
        calc C.cm i₀ j₀ * C.zf i * (C.cm i₀ j₀ ^ (l.countP (fun i => decide (c i ≠ 1))) *
              ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G))
            = C.cm i₀ j₀ * ((C.zf i * C.cm i₀ j₀ ^ (l.countP (fun i => decide (c i ≠ 1)))) *
              ((gprod C.wU l : ↥(vBeta K1 L2 S Zs)) : G)) := by simp only [mul_assoc]
          _ = _ := by rw [hpz]; simp only [mul_assoc]
  have hclos : ∀ g : ↥(vBeta K1 L2 S Zs),
      g ∈ Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) := by
    intro g
    rw [C.closure_wU hij]
    exact Subgroup.mem_top g
  have hyUc : ∀ g : ↥(vBeta K1 L2 S Zs),
      g * gprod C.wU l₀ = gprod C.wU l₀ * g := fun g =>
    hG.commute_gprod_univ_closure hodd l₀ hl₀ hall (hclos g)
  have hyZ : ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) ∈ Zs := by
    refine hcen _ (gprod C.wU l₀).2 fun u hu => ?_
    have := congrArg Subtype.val (hyUc ⟨u, hu⟩)
    exact this.symm
  set p : Ω → Bool := fun i => decide (c i ≠ 1) with hp
  have hN : Even (l₀.countP p) := by
    have h1 := hconj l₀
    have hmy : m * ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) * m⁻¹ =
        ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) := by
      rw [hmZ _ hyZ]
      group
    rw [hmy] at h1
    have h2 : C.cm i₀ j₀ ^ (l₀.countP p) = 1 := by
      have := h1.symm
      exact (mul_eq_right.mp this)
    have h3 : (C.zU i₀ j₀) ^ (l₀.countP p) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact h2
    exact (hG.z_pow_eq_one_iff hz _).mp h3
  set Sm : List Ω := l₀.filter p with hSm
  have hSmnd : Sm.Nodup := hl₀.filter _
  have hSmlen : Sm.length = l₀.countP p := (List.countP_eq_length_filter).symm
  set w : ↥(vBeta K1 L2 S Zs) := gprod C.wU Sm with hw
  have hmemSm : ∀ j, j ∈ Sm ↔ c j ≠ 1 := fun j => by
    simp [hSm, hp, hall j]
  have hcomm : ∀ j, C.zf j * (w : G) = c j * ((w : G) * C.zf j) := by
    intro j
    have h1 := hG.mul_gprod j Sm
    have h1' : C.zf j * (w : G) =
        C.cm i₀ j₀ ^ (Sm.countP (fun i => decide (i ≠ j))) * ((w : G) * C.zf j) := by
      exact congrArg Subtype.val h1
    rw [h1']
    congr 1
    have h2 := countP_ne_add_count j Sm
    by_cases hj : c j = 1
    · have hjn : j ∉ Sm := fun h => (hmemSm j).mp h hj
      have h3 : Sm.count j = 0 := List.count_eq_zero.mpr hjn
      rw [h3] at h2
      obtain ⟨r, hr⟩ := hN
      have : Sm.countP (fun i => decide (i ≠ j)) = r + r := by omega
      rw [this, hpe, hj]
    · have hjm : j ∈ Sm := (hmemSm j).mpr hj
      have h3 : Sm.count j = 1 := List.count_eq_one_of_mem hSmnd hjm
      rw [h3] at h2
      obtain ⟨r, hr⟩ := hN
      have h4 : c j = C.cm i₀ j₀ := (hc01 j).resolve_left hj
      have hr1 : 1 ≤ r := by
        have : 0 < Sm.length := List.length_pos_of_mem hjm
        omega
      have h5 : Sm.countP (fun i => decide (i ≠ j)) = (r - 1) + (r - 1) + 1 := by omega
      rw [h5, hpo, h4]
  have hzW' : ∀ x ∈ Zs, (w : G)⁻¹ * x = x * (w : G)⁻¹ := fun x hx => hzW w⁻¹ x hx
  have hcw : ∀ j, c j * (w : G)⁻¹ = (w : G)⁻¹ * c j := fun j => (hzW' _ (hcZ j)).symm
  have hn : ∀ j, C.zf j * ((w : G)⁻¹ * m) = ((w : G)⁻¹ * m) * C.zf j := by
    intro j
    have hcc : c j * c j = 1 := C.Zs_sq (hcZ j)
    have E1 : (w : G)⁻¹ * C.zf j = c j * (C.zf j * (w : G)⁻¹) := by
      have h := hcomm j
      calc (w : G)⁻¹ * C.zf j = (w : G)⁻¹ * (C.zf j * (w : G)) * (w : G)⁻¹ := by group
        _ = (w : G)⁻¹ * (c j * ((w : G) * C.zf j)) * (w : G)⁻¹ := by rw [h]
        _ = ((w : G)⁻¹ * c j) * ((w : G) * C.zf j) * (w : G)⁻¹ := by simp only [mul_assoc]
        _ = (c j * (w : G)⁻¹) * ((w : G) * C.zf j) * (w : G)⁻¹ := by rw [← hcw j]
        _ = c j * (C.zf j * (w : G)⁻¹) := by group
    calc C.zf j * ((w : G)⁻¹ * m)
        = (C.zf j * (w : G)⁻¹) * m := by rw [mul_assoc]
      _ = (c j * c j) * (C.zf j * (w : G)⁻¹) * m := by rw [hcc, one_mul]
      _ = c j * (c j * (C.zf j * (w : G)⁻¹)) * m := by simp only [mul_assoc]
      _ = c j * ((w : G)⁻¹ * C.zf j) * m := by rw [← E1]
      _ = (c j * (w : G)⁻¹) * C.zf j * m := by simp only [mul_assoc]
      _ = ((w : G)⁻¹ * c j) * C.zf j * m := by rw [hcw j]
      _ = (w : G)⁻¹ * (c j * C.zf j * m) := by simp only [mul_assoc]
      _ = (w : G)⁻¹ * (m * C.zf j) := by rw [hmz j]
      _ = ((w : G)⁻¹ * m) * C.zf j := by rw [mul_assoc]
  refine ⟨(w : G), w.2, ?_⟩
  have hgen : vBeta K1 L2 S Zs ≤ Subgroup.centralizer ({(w : G)⁻¹ * m} : Set G) := by
    refine (C.U_eq_closure hz0Z hne).le.trans ((Subgroup.closure_le _).mpr ?_)
    rintro x (rfl | ⟨j, rfl⟩)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 : (w : G)⁻¹ * m * C.cm i₀ j₀ = C.cm i₀ j₀ * ((w : G)⁻¹ * m) := by
        calc (w : G)⁻¹ * m * C.cm i₀ j₀ = (w : G)⁻¹ * (m * C.cm i₀ j₀) := by rw [mul_assoc]
          _ = (w : G)⁻¹ * (C.cm i₀ j₀ * m) := by rw [hmZ _ hz0Z]
          _ = ((w : G)⁻¹ * C.cm i₀ j₀) * m := by rw [mul_assoc]
          _ = (C.cm i₀ j₀ * (w : G)⁻¹) * m := by rw [← hzW' _ hz0Z]
          _ = C.cm i₀ j₀ * ((w : G)⁻¹ * m) := by rw [mul_assoc]
      exact h1
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hn j).symm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have := Subgroup.mem_centralizer_iff.mp (hgen hx) ((w : G)⁻¹ * m) (Set.mem_singleton _)
  exact this.symm

end CFSG.Quasithin.Background.Harris.R1
