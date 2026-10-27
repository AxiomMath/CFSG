module

public import CFSG.Timmesfeld.Bridge.Asc72WAct
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.BenderSuzuki

private abbrev Base (f : ℕ) := CFSG.Theory.Comparator.PSL2Model f

private abbrev WreathBase (f n : ℕ) := Fin n → Base f

private theorem exists_ne_zero_sq_ne_one_charTwo {F : Type*} [Field F] [CharP F 2] [Finite F]
    (h : 4 ≤ Nat.card F) : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  have h1 : 1 < Nat.card Fˣ := by
    rw [Nat.card_units]
    omega
  obtain ⟨u, hu⟩ := @exists_ne Fˣ (Finite.one_lt_card_iff_nontrivial.1 h1) 1
  refine ⟨u, u.ne_zero, fun h2 => hu (Units.ext ?_)⟩
  apply frobenius_inj F 2
  simpa [frobenius_def] using h2

theorem base_isMinimalNormal (f n : ℕ) (hf : 2 ≤ f) (hn : 2 ≤ n) :
    CFSG.Timmesfeld.Bridge.Asc72.IsMinimalNormal
      (SemidirectProduct.inl.range :
        Subgroup (CFSG.Timmesfeld.Bridge.Asc72.L2Wreath f n)) := by
  classical
  let F := GaloisField 2 f
  let inlK : (WreathBase f n) →* L2Wreath f n := SemidirectProduct.inl
  have hcard : Nat.card F = 2 ^ f := by
    simpa [F] using GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI : IsSimpleGroup (Base f) := by
    simpa [Base, F, CFSG.Theory.Comparator.PSL2Model] using
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  haveI : CharP F 2 := by
    simpa [F] using (inferInstance : CharP (GaloisField 2 f) 2)
  have hfield : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := exists_ne_zero_sq_ne_one_charTwo h4
  have hperfect : Group.IsPerfect (Base f) := ⟨SL2Simple.PSL_commutator_eq_top hfield⟩
  have hnc : ¬ IsMulCommutative (Base f) := Group.IsPerfect.not_isMulCommutative (G := (Base f))
  have hbaseNormal : (SemidirectProduct.inl.range : Subgroup (L2Wreath f n)).Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hbaseNeBot : (SemidirectProduct.inl.range : Subgroup (L2Wreath f n)) ≠ ⊥ := by
    intro hbot
    have hnt : Nontrivial (Base f) := IsSimpleGroup.toNontrivial
    obtain ⟨a, ha⟩ := exists_ne (1 : (Base f))
    let i0 : Fin n := ⟨0, by omega⟩
    let k : (WreathBase f n) := Pi.mulSingle i0 a
    have hk1 : k ≠ 1 := by
      intro hk
      have h := congrFun hk i0
      rw [show k i0 = a by simp [k], Pi.one_apply] at h
      exact ha h
    have hmem : (SemidirectProduct.inl k : L2Wreath f n) ∈
        (⊥ : Subgroup (L2Wreath f n)) := by
      rw [← hbot]
      exact ⟨k, rfl⟩
    rw [Subgroup.mem_bot] at hmem
    exact hk1 (SemidirectProduct.inl_injective (by simpa using hmem))
  refine ⟨hbaseNormal, hbaseNeBot, ?_⟩
  intro N hNnorm hNle
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · right
    let N0 : Subgroup (WreathBase f n) := N.comap inlK
    have hN0normal : N0.Normal := Subgroup.Normal.comap hNnorm inlK
    have hN0neBot : N0 ≠ ⊥ := by
      intro hN0bot
      obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
      have hxbase : (x : L2Wreath f n) ∈
          (SemidirectProduct.inl.range : Subgroup (L2Wreath f n)) := hNle x.2
      rcases hxbase with ⟨k, hk⟩
      have hk0 : k ∈ N0 := Subgroup.mem_comap.mpr (hk ▸ x.2)
      have hk1 : k = 1 := by rw [hN0bot] at hk0; exact Subgroup.mem_bot.mp hk0
      apply hxne
      apply Subtype.ext
      change (x : L2Wreath f n) = 1
      rw [← hk, hk1, map_one]
    have hperm (σ : Equiv.Perm (Fin n)) {k : (WreathBase f n)} (hk : k ∈ N0) :
        permAct (Fin n) (Base f) σ k ∈ N0 := by
      let φ := permAct (Fin n) (Base f)
      have hkin : (SemidirectProduct.inl (φ := φ) k :
          (WreathBase f n) ⋊[φ] Equiv.Perm (Fin n)) ∈ N := Subgroup.mem_comap.mp hk
      have hconj : (SemidirectProduct.inr (φ := φ) σ *
          SemidirectProduct.inl (φ := φ) k *
          (SemidirectProduct.inr (φ := φ) σ)⁻¹ :
            (WreathBase f n) ⋊[φ] Equiv.Perm (Fin n)) ∈ N := hNnorm.conj_mem _ hkin _
      have hEq : (SemidirectProduct.inr (φ := φ) σ *
          SemidirectProduct.inl (φ := φ) k *
          (SemidirectProduct.inr (φ := φ) σ)⁻¹ :
            (WreathBase f n) ⋊[φ] Equiv.Perm (Fin n)) =
          SemidirectProduct.inl (φ := φ) (permAct (Fin n) (Base f) σ k) := by
        simpa using (SemidirectProduct.inl_aut (φ := φ) σ k).symm
      rw [hEq] at hconj
      exact Subgroup.mem_comap.mpr hconj
    let evalAt (i : Fin n) : (WreathBase f n) →* (Base f) := Pi.evalMonoidHom (fun _ : Fin n => (Base f)) i
    have hevalSurj (i : Fin n) : Function.Surjective (evalAt i) :=
      fun y => ⟨(Pi.mulSingle i y : (WreathBase f n)), by
        change (Pi.mulSingle i y : (WreathBase f n)) i = y
        exact Pi.mulSingle_eq_same (M := fun _ : Fin n => (Base f)) i y⟩
    let Proj (i : Fin n) : Subgroup (Base f) := N0.map (evalAt i)
    have hProjNormal (i : Fin n) : (Proj i).Normal :=
      Subgroup.Normal.map hN0normal (evalAt i) (hevalSurj i)
    have hProjNeBot (i : Fin n) : Proj i ≠ ⊥ := by
      intro hProjbot
      obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN0neBot
      have hxne' : (x : (WreathBase f n)) ≠ 1 := fun h => hxne (Subtype.ext h)
      have hex : ∃ j : Fin n, (x : (WreathBase f n)) j ≠ 1 := by
        by_contra h
        push Not at h
        exact hxne' (funext h)
      obtain ⟨j, hj⟩ := hex
      let σ : Equiv.Perm (Fin n) := Equiv.swap i j
      have hσ : σ⁻¹ i = j := by
        dsimp [σ]
        exact Equiv.swap_apply_left i j
      have hmem : permAct (Fin n) (Base f) σ (x : (WreathBase f n)) ∈ N0 := hperm σ x.2
      have hval : permAct (Fin n) (Base f) σ (x : (WreathBase f n)) i = (x : (WreathBase f n)) j := by
        rw [WreathAct.permAct_apply', hσ]
      have hxproj : (x : (WreathBase f n)) j ∈ Proj i := by
        refine Subgroup.mem_map.mpr ⟨permAct (Fin n) (Base f) σ (x : (WreathBase f n)), hmem, ?_⟩
        exact hval
      rw [hProjbot, Subgroup.mem_bot] at hxproj
      exact hj hxproj
    have hProjTop (i : Fin n) : Proj i = ⊤ := by
      haveI := hProjNormal i
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Proj i) with h | h
      · exact absurd h (hProjNeBot i)
      · exact h
    let C (i : Fin n) : Subgroup (WreathBase f n) := (MonoidHom.mulSingle (fun _ : Fin n => (Base f)) i).range
    have hCnormal (i : Fin n) : (C i).Normal := by
      refine Subgroup.Normal.mk fun y hy g => ?_
      rcases hy with ⟨y0, rfl⟩
      refine ⟨g i * y0 * (g i)⁻¹, ?_⟩
      simp only [MonoidHom.coe_mulSingle]
      exact (WreathAct.conj_mulSingle (L := Base f) g i y0).symm
    have hMeq (i : Fin n) : N0 ⊓ C i = C i := by
      refine le_antisymm inf_le_right ?_
      have hMiNeBot : N0 ⊓ C i ≠ ⊥ := by
        intro hbot
        have hcentral : ∀ a ∈ N0, ∀ b ∈ C i, a * b = b * a := by
          intro a ha b hb
          have hcomm : a * b * a⁻¹ * b⁻¹ ∈ N0 ⊓ C i := by
            constructor
            · have : b * a⁻¹ * b⁻¹ ∈ N0 := hN0normal.conj_mem a⁻¹ (N0.inv_mem ha) b
              simpa [mul_assoc] using N0.mul_mem ha this
            · have : a * b * a⁻¹ ∈ C i := hCnormal i |>.conj_mem b hb a
              exact C i |>.mul_mem this (C i |>.inv_mem hb)
          rw [hbot, Subgroup.mem_bot] at hcomm
          have hcomm' : a * b = b * a := by
            calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
              _ = 1 * (b * a) := by rw [hcomm]
              _ = b * a := by simp
          exact hcomm'
        have hcommL : ∀ x y : (Base f), x * y = y * x := by
          intro x y
          have hxproj : x ∈ Proj i := by rw [hProjTop i]; trivial
          rcases Subgroup.mem_map.mp hxproj with ⟨a, ha, hai⟩
          have hb : Pi.mulSingle i y ∈ C i := by
            simpa only [MonoidHom.coe_mulSingle] using
              (MonoidHom.mem_range (f := MonoidHom.mulSingle (fun _ : Fin n => (Base f)) i)).mpr
                ⟨y, rfl⟩
          have hcomm := hcentral a ha _ hb
          have hai' : a i = x := hai
          have hthis : a i * y = y * a i := by
            have h := congrFun hcomm i
            have hl : (a * (Pi.mulSingle i y : (WreathBase f n))) i = a i * y := by
              rw [Pi.mul_apply (f := a) (g := (Pi.mulSingle i y : (WreathBase f n)))]
              rw [Pi.mulSingle_eq_same (M := fun _ : Fin n => Base f)]
            have hr : ((Pi.mulSingle i y : (WreathBase f n)) * a) i = y * a i := by
              rw [Pi.mul_apply (f := (Pi.mulSingle i y : (WreathBase f n))) (g := a)]
              rw [Pi.mulSingle_eq_same (M := fun _ : Fin n => Base f)]
            rwa [hl, hr] at h
          simpa [hai'] using hthis
        exact hnc ⟨⟨hcommL⟩⟩
      obtain ⟨m, hmne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMiNeBot
      have hmC : (m : (WreathBase f n)) ∈ C i := m.2.2
      have hmsupport : (m : (WreathBase f n)) = Pi.mulSingle i ((m : (WreathBase f n)) i) := by
        rcases hmC with ⟨y0, hy0⟩
        rw [← hy0, MonoidHom.coe_mulSingle, Pi.mulSingle_eq_same]
      have hmi : (m : (WreathBase f n)) i ≠ 1 := by
        intro hmi1
        apply hmne
        apply Subtype.ext
        rw [hmsupport, hmi1]
        exact Pi.mulSingle_one i
      have hMprojNeBot : (N0 ⊓ C i).map (evalAt i) ≠ ⊥ := by
        intro hbot
        have : (m : (WreathBase f n)) i ∈ (N0 ⊓ C i).map (evalAt i) :=
          Subgroup.mem_map.mpr ⟨m, m.2, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact hmi this
      have hMprojNormal : ((N0 ⊓ C i).map (evalAt i)).Normal :=
        Subgroup.Normal.map (Subgroup.normal_inf_normal N0 (C i)) (evalAt i) (hevalSurj i)
      have hMprojTop : (N0 ⊓ C i).map (evalAt i) = ⊤ := by
        haveI := hMprojNormal
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          ((N0 ⊓ C i).map (evalAt i)) with h | h
        · exact absurd h hMprojNeBot
        · exact h
      intro c hc
      have hci : (c : (WreathBase f n)) i ∈ (N0 ⊓ C i).map (evalAt i) := by
        rw [hMprojTop]
        trivial
      rcases Subgroup.mem_map.mp hci with ⟨m, hm, hmi'⟩
      have hmi'' : (m : (WreathBase f n)) i = (c : (WreathBase f n)) i := hmi'
      have hmC : (m : (WreathBase f n)) ∈ C i := hm.2
      have hcsupport : (c : (WreathBase f n)) = Pi.mulSingle i ((c : (WreathBase f n)) i) := by
        rcases hc with ⟨y0, hy0⟩
        rw [← hy0, MonoidHom.coe_mulSingle, Pi.mulSingle_eq_same]
      have hmsupport : (m : (WreathBase f n)) = Pi.mulSingle i ((m : (WreathBase f n)) i) := by
        rcases hmC with ⟨y0, hy0⟩
        rw [← hy0, MonoidHom.coe_mulSingle, Pi.mulSingle_eq_same]
      have hmc : (m : (WreathBase f n)) = (c : (WreathBase f n)) := by
        rw [hmsupport, hcsupport, hmi'']
      rw [← hmc]
      exact hm
    have hCiLeN0 (i : Fin n) : C i ≤ N0 := by
      rw [← hMeq i]
      exact inf_le_left
    have hN0top : N0 = ⊤ := by
      refine le_antisymm le_top fun x _ => ?_
      refine Subgroup.pi_mem_of_mulSingle_mem (H := N0) x fun i => ?_
      have hmem : Pi.mulSingle i (x i) ∈ C i := by
        simpa only [MonoidHom.coe_mulSingle] using
          (MonoidHom.mem_range (f := MonoidHom.mulSingle (fun _ : Fin n => (Base f)) i)).mpr
            ⟨x i, rfl⟩
      exact hCiLeN0 i hmem
    have hbaseLeN : (SemidirectProduct.inl.range : Subgroup (L2Wreath f n)) ≤ N := by
      rintro _ ⟨k, rfl⟩
      have hk : k ∈ N0 := by rw [hN0top]; trivial
      exact Subgroup.mem_comap.mp hk
    exact le_antisymm hNle hbaseLeN

end CFSG.OddTranspositions
