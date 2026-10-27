module

public import CFSG.Quasithin.AppendixH.H9.PairStabilizer.CentralizerOfV

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.PairStab

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH.AutPair

variable {m : ℕ}

abbrev W1sub (m : ℕ) : Subgroup (PairN (m + 1)) :=
  V1n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0) ⊔ Subgroup.zpowers (pairVec 0 (ez m)))

abbrev W2sub (m : ℕ) : Subgroup (PairN (m + 1)) :=
  V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0) ⊔ Subgroup.zpowers (pairVec 0 (ez m)))

private theorem zmod_two_eq_zero_or_one (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private theorem eq_one_or_eq_of_mem_zpowers_sq {G : Type*} [Group G] {v x : G}
    (hv : v ^ 2 = 1) (hx : x ∈ Subgroup.zpowers v) : x = 1 ∨ x = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨t, ht | ht⟩ := Int.even_or_odd' k
  · left
    rw [ht, zpow_mul, zpow_ofNat, hv, one_zpow]
  · right
    rw [ht, zpow_add, zpow_mul, zpow_one, zpow_ofNat, hv, one_zpow, one_mul]

private def polarAnn (x : PairN (m + 1)) : Subgroup (PairN (m + 1)) where
  carrier := {y | polarN (m + 1) x y = 0}
  mul_mem' := by
    intro y z hy hz
    simp only [Set.mem_setOf_eq] at hy hz ⊢
    rw [polarN_comm x (y * z), polarN_mul_left y z x, polarN_comm y x,
      polarN_comm z x, hy, hz, add_zero]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    simp [polarN]
  inv_mem' := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy ⊢
    calc polarN (m + 1) x y⁻¹ = polarN (m + 1) y⁻¹ x := polarN_comm x y⁻¹
      _ = polarN (m + 1) y x := polarN_inv_left y x
      _ = polarN (m + 1) x y := polarN_comm y x
      _ = 0 := hy

private theorem polarN_eq_zero_of_mem_zpowers {x v y : PairN (m + 1)}
    (hv : polarN (m + 1) x v = 0) (hy : y ∈ Subgroup.zpowers v) :
    polarN (m + 1) x y = 0 :=
  Subgroup.zpowers_le.mpr (show v ∈ polarAnn x from hv) hy

private theorem smul_ez_mem_zpowers (t : ZMod 2) :
    pairVec (t • ez m) 0 ∈ Subgroup.zpowers (pairVec (ez m) 0) := by
  rcases zmod_two_eq_zero_or_one t with rfl | rfl
  · rw [zero_smul, ← pairVec_one]
    exact Subgroup.one_mem _
  · rw [one_smul]
    exact Subgroup.mem_zpowers _

private theorem smul_ez_mem_zpowers_v2 (t : ZMod 2) :
    pairVec 0 (t • ez m) ∈ Subgroup.zpowers (pairVec 0 (ez m)) := by
  rcases zmod_two_eq_zero_or_one t with rfl | rfl
  · rw [zero_smul, ← pairVec_one]
    exact Subgroup.one_mem _
  · rw [one_smul]
    exact Subgroup.mem_zpowers _

theorem mem_perp_iff (a b : Fin (m + 1) → ZMod 2) :
    pairVec a b ∈ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0) ⊔
      Subgroup.zpowers (pairVec 0 (ez m))) ↔ a 0 = 0 ∧ b 0 = 0 := by
  constructor
  · intro h
    rw [mem_perpN] at h
    have h1 := h (pairVec (ez m) 0) (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have h2 := h (pairVec 0 (ez m)) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    rw [polarN_pairVec] at h1 h2
    exact ⟨by simpa [ez] using h2, by simpa [ez] using h1⟩
  · rintro ⟨ha, hb⟩
    rw [mem_perpN]
    intro s hs
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hs
    have hv1 : polarN (m + 1) (pairVec a b) (pairVec (ez m) 0) = 0 := by
      rw [polarN_pairVec]; simpa [ez] using hb
    have hv2 : polarN (m + 1) (pairVec a b) (pairVec 0 (ez m)) = 0 := by
      rw [polarN_pairVec]; simpa [ez] using ha
    have hy0 := polarN_eq_zero_of_mem_zpowers hv1 hy
    have hz0 := polarN_eq_zero_of_mem_zpowers hv2 hz
    have h3 : polarN (m + 1) (pairVec a b) (y * z) =
        polarN (m + 1) (pairVec a b) y + polarN (m + 1) (pairVec a b) z := by
      rw [polarN_comm, polarN_mul_left, polarN_comm y, polarN_comm z]
    exact h3.trans (by rw [hy0, hz0, add_zero])

theorem mem_W1sub_iff {x : PairN (m + 1)} :
    x ∈ W1sub m ↔ ∃ a : Fin (m + 1) → ZMod 2, a 0 = 0 ∧ x = pairVec a 0 := by
  constructor
  · intro hx
    rw [W1sub, Subgroup.mem_inf, mem_V1n] at hx
    obtain ⟨hx2, hxp⟩ := hx
    obtain ⟨a, b, rfl⟩ := pairVec_surj x
    have hb : b = 0 := by simpa [pairVec] using hx2
    refine ⟨a, ((mem_perp_iff a b).mp hxp).1, ?_⟩
    rw [hb]
  · rintro ⟨a, ha, rfl⟩
    rw [W1sub, Subgroup.mem_inf, mem_V1n]
    exact ⟨by simp [pairVec], (mem_perp_iff a 0).mpr ⟨ha, rfl⟩⟩

theorem mem_W2sub_iff {x : PairN (m + 1)} :
    x ∈ W2sub m ↔ ∃ b : Fin (m + 1) → ZMod 2, b 0 = 0 ∧ x = pairVec 0 b := by
  constructor
  · intro hx
    rw [W2sub, Subgroup.mem_inf, mem_V2n] at hx
    obtain ⟨hx1, hxp⟩ := hx
    obtain ⟨a, b, rfl⟩ := pairVec_surj x
    have ha : a = 0 := by simpa [pairVec] using hx1
    refine ⟨b, ((mem_perp_iff a b).mp hxp).2, ?_⟩
    rw [ha]
  · rintro ⟨b, hb, rfl⟩
    rw [W2sub, Subgroup.mem_inf, mem_V2n]
    exact ⟨by simp [pairVec], (mem_perp_iff 0 b).mpr ⟨rfl, hb⟩⟩

private def betaHom (m : ℕ) : ↥(W1sub m) →* Multiplicative (Fin m → ZMod 2) where
  toFun u := Multiplicative.ofAdd
    (fun i : Fin m => Multiplicative.toAdd (u : PairN (m + 1)).1 i.succ)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    simp
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    ext i
    simp [Prod.fst_mul, toAdd_mul, Pi.add_apply]

private theorem betaHom_equiv (B : GL (Fin m) (ZMod 2)) :
    ∀ u u' : ↥(W1sub m), (u' : PairN (m + 1)) = leviAct m B (u : PairN (m + 1)) →
      betaHom m u' = natHom m (ZMod 2) B (betaHom m u) := by
  intro u u' hu'
  obtain ⟨a, ha0, hax⟩ := (mem_W1sub_iff).mp u.2
  obtain ⟨a', ha'0, ha'x⟩ := (mem_W1sub_iff).mp u'.2
  have hUg : (u' : PairN (m + 1)) =
      pairVec (leviMat (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ a) 0 := by
    rw [hu', hax, leviAct_apply, pairActN_pairVec, levi_val, Matrix.mulVec_zero]
  have ha'eq : a' = leviMat (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ a :=
    (pairVec_inj.mp (ha'x.symm.trans hUg)).1
  have hbeta_u : Multiplicative.toAdd (betaHom m u) = fun i : Fin m => a i.succ := by
    ext i
    have hfst : (u : PairN (m + 1)).1 = Multiplicative.ofAdd a := by rw [hax]; rfl
    simp [betaHom, hfst]
  have hbeta_u' : Multiplicative.toAdd (betaHom m u') = fun i : Fin m => a' i.succ := by
    ext i
    have hfst : (u' : PairN (m + 1)).1 = Multiplicative.ofAdd a' := by rw [ha'x]; rfl
    simp [betaHom, hfst]
  have hgamma : Multiplicative.toAdd (natHom m (ZMod 2) B (betaHom m u)) =
      (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ (fun i : Fin m => a i.succ) := by
    simp [natHom, hbeta_u]
  apply Multiplicative.toAdd.injective
  ext i
  simp only [hbeta_u', hgamma, ha'eq, leviMat_mulVec_succ]

theorem V1n_decomp :
    V1n (m + 1) = Subgroup.zpowers (pairVec (ez m) 0) ⊔ W1sub m ∧
      Subgroup.zpowers (pairVec (ez m) 0) ⊓ W1sub m = ⊥ := by
  constructor
  · apply le_antisymm
    · intro x hx
      rw [mem_V1n] at hx
      obtain ⟨a, b, rfl⟩ := pairVec_surj x
      have hb : b = 0 := by simpa [pairVec] using hx
      rw [hb]
      have h1 : (a 0 • ez m) + (a - a 0 • ez m) = a := by abel
      have hsplit : pairVec a 0 =
          pairVec (a 0 • ez m) 0 * pairVec (a - a 0 • ez m) 0 := by
        rw [pairVec_mul, h1]
        simp
      rw [hsplit]
      refine Subgroup.mul_mem_sup (smul_ez_mem_zpowers (a 0))
        ((mem_W1sub_iff).mpr ⟨a - a 0 • ez m, ?_, rfl⟩)
      simp [Pi.sub_apply, Pi.smul_apply, ez]
    · exact sup_le (Subgroup.zpowers_le.mpr (pairVec_mem_V1n (ez m))) inf_le_left
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases eq_one_or_eq_of_mem_zpowers_sq (pairN_sq (pairVec (ez m) 0)) hx1 with h | h
      · rw [h]; exact Subgroup.mem_bot.mpr rfl
      · exfalso
        obtain ⟨a, ha, hax⟩ := (mem_W1sub_iff).mp hx2
        have haz : a = ez m := (pairVec_inj.mp (hax.symm.trans h)).1
        rw [haz, ez_zero] at ha
        exact one_ne_zero ha
    · exact bot_le

theorem V2n_decomp :
    V2n (m + 1) = Subgroup.zpowers (pairVec 0 (ez m)) ⊔ W2sub m ∧
      Subgroup.zpowers (pairVec 0 (ez m)) ⊓ W2sub m = ⊥ := by
  constructor
  · apply le_antisymm
    · intro x hx
      rw [mem_V2n] at hx
      obtain ⟨a, b, rfl⟩ := pairVec_surj x
      have ha : a = 0 := by simpa [pairVec] using hx
      rw [ha]
      have h1 : (b 0 • ez m) + (b - b 0 • ez m) = b := by abel
      have hsplit : pairVec 0 b =
          pairVec 0 (b 0 • ez m) * pairVec 0 (b - b 0 • ez m) := by
        rw [pairVec_mul, h1]
        simp
      rw [hsplit]
      refine Subgroup.mul_mem_sup (smul_ez_mem_zpowers_v2 (b 0))
        ((mem_W2sub_iff).mpr ⟨b - b 0 • ez m, ?_, rfl⟩)
      simp [Pi.sub_apply, Pi.smul_apply, ez]
    · exact sup_le (Subgroup.zpowers_le.mpr (pairVec_mem_V2n (ez m))) inf_le_left
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rcases eq_one_or_eq_of_mem_zpowers_sq (pairN_sq (pairVec 0 (ez m))) hx1 with h | h
      · rw [h]; exact Subgroup.mem_bot.mpr rfl
      · exfalso
        obtain ⟨b, hb, hbx⟩ := (mem_W2sub_iff).mp hx2
        have hbz : b = ez m := (pairVec_inj.mp (hbx.symm.trans h)).2
        rw [hbz, ez_zero] at hb
        exact one_ne_zero hb
    · exact bot_le

private theorem betaHom_apply (u : ↥(W1sub m)) (i : Fin m) :
    Multiplicative.toAdd (betaHom m u) i = Multiplicative.toAdd (u : PairN (m + 1)).1 i.succ :=
  rfl

private theorem betaHom_surjective : Function.Surjective (betaHom m) := by
  intro c
  refine ⟨⟨pairVec (Fin.cons 0 (Multiplicative.toAdd c)) 0,
    (mem_W1sub_iff).mpr ⟨Fin.cons 0 (Multiplicative.toAdd c), Fin.cons_zero _ _, rfl⟩⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  rw [betaHom_apply]
  exact Fin.cons_succ (α := fun _ => ZMod 2) 0 (Multiplicative.toAdd c) i

private theorem betaHom_eq_one_iff (u : ↥(W1sub m)) :
    betaHom m u = 1 ↔ (u : PairN (m + 1)) ∈ (⊥ : Subgroup (PairN (m + 1))) := by
  rw [Subgroup.mem_bot]
  obtain ⟨a, ha0, hax⟩ := (mem_W1sub_iff).mp u.2
  have hfst : (u : PairN (m + 1)).1 = Multiplicative.ofAdd a := by rw [hax]; rfl
  constructor
  · intro h
    have hzero : (fun i : Fin m => a i.succ) = 0 := by
      funext i
      have h1 := congrArg (fun c : Multiplicative (Fin m → ZMod 2) => Multiplicative.toAdd c i) h
      rw [betaHom_apply, hfst] at h1
      exact h1
    have ha : a = 0 := by
      funext i
      exact Fin.cases ha0 (fun i => congrFun hzero i) i
    rw [hax, ha]
    exact pairVec_one.symm
  · intro h
    have h1 : (u : PairN (m + 1)).1 = 1 := by rw [h]; rfl
    apply Multiplicative.toAdd.injective
    funext i
    rw [betaHom_apply, h1]
    rfl

private theorem leviAct_mem_W1sub (B : GL (Fin m) (ZMod 2)) {u : PairN (m + 1)}
    (hu : u ∈ W1sub m) : leviAct m B u ∈ W1sub m := by
  obtain ⟨a, ha0, rfl⟩ := (mem_W1sub_iff).mp hu
  refine (mem_W1sub_iff).mpr ⟨leviMat (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ a, ?_, ?_⟩
  · rw [leviMat_mulVec_zero]
    exact ha0
  · rw [leviAct_apply, pairActN_pairVec, levi_val, Matrix.mulVec_zero]

private theorem mulAut_mem_bot (g : MulAut (PairN (m + 1))) {z : PairN (m + 1)}
    (hz : z ∈ (⊥ : Subgroup (PairN (m + 1)))) : g z ∈ (⊥ : Subgroup (PairN (m + 1))) := by
  rw [Subgroup.mem_bot] at hz ⊢
  rw [hz]
  exact map_one g

theorem inducesOn_W1sub :
    InducesOn (leviAct m).range (W1sub m) ⊥ (Multiplicative (Fin m → ZMod 2))
      (natSub m (ZMod 2) ⊤) := by
  refine ⟨bot_le, ?_, ?_, betaHom m, betaHom_surjective, betaHom_eq_one_iff, ?_, ?_⟩
  · intro g hg u hu
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hg
    exact leviAct_mem_W1sub B hu
  · intro g _ z hz
    exact mulAut_mem_bot g hz
  · intro g hg
    obtain ⟨B, rfl⟩ := MonoidHom.mem_range.mp hg
    exact ⟨natHom m (ZMod 2) B, Subgroup.mem_map.mpr ⟨B, Subgroup.mem_top B, rfl⟩,
      betaHom_equiv B⟩
  · intro γ hγ
    obtain ⟨B, -, hB⟩ := Subgroup.mem_map.mp hγ
    refine ⟨leviAct m B, MonoidHom.mem_range.mpr ⟨B, rfl⟩, ?_⟩
    intro u u' hu'
    rw [← hB]
    exact betaHom_equiv B u u' hu'

theorem polar_W1_W2 : ∀ w ∈ W1sub m, w ≠ 1 → ∃ w' ∈ W2sub m, polarN (m + 1) w w' ≠ 0 := by
  intro w hw hw1
  obtain ⟨a, ha0, rfl⟩ := (mem_W1sub_iff).mp hw
  have ha : a ≠ 0 := by
    intro h
    apply hw1
    rw [h]
    exact pairVec_one.symm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hai : a i = 1 := by
    rcases zmod_two_eq_zero_or_one (a i) with h | h
    · exact absurd h hi
    · exact h
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hi ha0
  refine ⟨pairVec 0 (Pi.single i 1), (mem_W2sub_iff).mpr ⟨Pi.single i 1, ?_, rfl⟩, ?_⟩
  · simp [Pi.single_apply, hi0]
  · rw [polarN_pairVec]
    simp [dotProduct_single, hai]

theorem polar_W2_W1 : ∀ w' ∈ W2sub m, w' ≠ 1 → ∃ w ∈ W1sub m, polarN (m + 1) w w' ≠ 0 := by
  intro w' hw' hw'1
  obtain ⟨b, hb0, rfl⟩ := (mem_W2sub_iff).mp hw'
  have hb : b ≠ 0 := by
    intro h
    apply hw'1
    rw [h]
    exact pairVec_one.symm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
  have hbi : b i = 1 := by
    rcases zmod_two_eq_zero_or_one (b i) with h | h
    · exact absurd h hi
    · exact h
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hi hb0
  refine ⟨pairVec (Pi.single i 1) 0, (mem_W1sub_iff).mpr ⟨Pi.single i 1, ?_, rfl⟩, ?_⟩
  · simp [Pi.single_apply, hi0]
  · rw [polarN_pairVec]
    simp [single_dotProduct, hbi]

end CFSG.ASVolI.ChH.PairStab
