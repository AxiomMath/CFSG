module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AENineBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase9B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_nine_map_conj_map_conj {W : Type*} [Group W]
    (A : Subgroup (MulAut W)) (x y : MulAut W) :
    (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      A.map (MulAut.conj (y * x)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem s1611e3_nine_map_conj_one {W : Type*} [Group W] (A : Subgroup (MulAut W)) :
    A.map (MulAut.conj (1 : MulAut W)).toMonoidHom = A := by
  ext z
  simp [Subgroup.mem_map, MulAut.conj_apply]

theorem s1611e3_nine_eq_pair_of_ncard_two {α : Type*} {s : Set α} {a b : α}
    (hs : s.ncard = 2) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : s = {a, b} := by
  obtain ⟨Y₁, Y₂, -, hYset⟩ := Set.ncard_eq_two.1 hs
  rw [hYset] at ha hb ⊢
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · rw [ha, ← hb]
  · rw [← ha, ← hb, Set.pair_comm]
  · exact absurd (ha.trans hb.symm) hab

theorem s1611e3_nine_two (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV)
    (hv1 : v1Sub D.M V₀ V hV L = V₀)
    (h9 : Case168_9 D V₀ V hV L) :
    ∃ g : MulAut (Vtil V₀ V hV),
      s16n9b_case9Two (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g := by
  classical
  have hS : Setting16 D V₀ V L := hc.setting
  have hH : Hyp151 D V₀ V L := hS.hyp151
  obtain ⟨-, hL3, hs15, hsum, -⟩ := h9
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  obtain ⟨g₂, hg₂M, hg₂ne⟩ : ∃ g ∈ Mbar D.M V₀ V hV,
      (lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom ≠ lBar V₀ V hV L := by
    by_contra hcon
    have hsingle : {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV,
          Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = {lBar V₀ V hV L} := by
      ext Y
      constructor
      · rintro ⟨φ, hφM, rfl⟩
        by_contra hne
        exact hcon ⟨φ, hφM, hne⟩
      · rintro rfl
        exact ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩
    rw [hsingle] at hcls
    simp at hcls
  obtain ⟨x, hxM, hxg₂⟩ := (mem_barSub V₀ V hV D.M g₂).1 hg₂M
  have hgne : (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom ≠ lBar V₀ V hV L := by
    intro h
    apply hg₂ne
    have h' := congrArg (fun X : Subgroup (MulAut (Vtil V₀ V hV)) =>
      X.map (MulAut.conj g₂).toMonoidHom) h
    rw [s1611e3_nine_map_conj_map_conj, mul_inv_cancel, s1611e3_nine_map_conj_one] at h'
    exact h'.symm
  have hgM : g₂⁻¹ ∈ Mbar D.M V₀ V hV := (Mbar D.M V₀ V hV).inv_mem hg₂M
  have hconjinv : ((MulAut.conj g₂)⁻¹).toMonoidHom =
      (MulAut.conj g₂⁻¹).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply]
  have hbar : barSub V₀ V hV (conjSubgroup L (x : G)) =
      (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV x.2 L, hxg₂]
    exact congrArg (fun f : MulAut (Vtil V₀ V hV) →* MulAut (Vtil V₀ V hV) =>
      (barSub V₀ V hV L).map f) hconjinv
  have hxnbar : (x : G) ∉ nBar D.M V₀ V hV L := by
    intro hx
    rw [s15_Infra_mem_nBar_iff hS.hyp16.hyp125 hV hxM] at hx
    rw [hbar] at hx
    exact hgne hx
  have hcomm := hH.commute (x : G) hxM hxnbar
  rw [hbar] at hcomm
  have hABne : lBar V₀ V hV L ≠
      (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := fun h => hgne h.symm
  have hpair : {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} =
      {lBar V₀ V hV L, (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom} :=
    s1611e3_nine_eq_pair_of_ncard_two hcls
      ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩ ⟨g₂⁻¹, hgM, rfl⟩ hABne
  have hrk0 : rk ↥(wTil V₀ V hV L) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrktop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 :=
    s16t_case9_rk_top D h1217 hV hH hv1 hc.ne_bot hs15 hsum
  obtain ⟨hind, hsup⟩ := s16t_case9_directSum D h1217 hV hH hv1 hc.ne_bot
  have hn2 : (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)).ncard = 2 :=
    s16n9b_case9_conjSubs_ncard hV hind hsup hrk0 hrktop
  have hWmem : (wTil V₀ V hV L) ∈ conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) :=
    ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩
  have hW'mem : (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom ∈
      conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) := ⟨g₂⁻¹, hgM, rfl⟩
  have hWne : (wTil V₀ V hV L) ≠ (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom := by
    intro h
    apply hgne
    have hmem : lBar V₀ V hV L ∈ {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV, Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
      ⟨1, (Mbar D.M V₀ V hV).one_mem, by ext y; simp⟩
    have hstab : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)).map
        g₂⁻¹.toMonoidHom = commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) := by
      show (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom = wTil V₀ V hV L
      exact h.symm
    exact s16c167_normalizes_of_stab hcls hn2 (lBar V₀ V hV L) hmem g₂⁻¹ hgM hstab
  have hpairW : conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L) =
      {wTil V₀ V hV L, (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom} :=
    s1611e3_nine_eq_pair_of_ncard_two hn2 hWmem hW'mem hWne
  have hdisj : wTil V₀ V hV L ⊓ (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom = ⊥ :=
    disjoint_iff.mp ((sSupIndep_pair hWne).mp (hpairW ▸ hind))
  have hsup' : wTil V₀ V hV L ⊔ (wTil V₀ V hV L).map g₂⁻¹.toMonoidHom = ⊤ := by
    have h := hpairW ▸ hsup
    rwa [sSup_pair] at h
  refine ⟨g₂⁻¹, ⟨barSub_mono V₀ V hV hH.le, hgM, hgne, hcomm.1, ?_, ?_, ?_, hdisj, hsup'⟩⟩
  · intro φ hφM
    have hmem : (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∈
        ({lBar V₀ V hV L, (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom} :
          Set (Subgroup (MulAut (Vtil V₀ V hV)))) := by
      rw [← hpair]
      exact ⟨φ, hφM, rfl⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro b hb w hw
    have hle : wTil V₀ V hV L ≤
        fixV ((lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom) :=
      commSub_eq_bot_iff.mp hcomm.2
    exact (mem_fixV.mp (hle hw)) b hb
  · intro a ha w hw
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    have hmemg : g₂ * a * g₂⁻¹ ∈ (lBar V₀ V hV L).map (MulAut.conj g₂).toMonoidHom :=
      Subgroup.mem_map.2 ⟨a, ha, rfl⟩
    have hAg : (lBar V₀ V hV L).map (MulAut.conj g₂).toMonoidHom =
        (lBar V₀ V hV L).map (MulAut.conj g₂⁻¹).toMonoidHom := by
      have hσ : (lBar V₀ V hV L).map (MulAut.conj g₂).toMonoidHom ∈
          {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
            ∃ φ ∈ Mbar D.M V₀ V hV,
              Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
        ⟨g₂, hg₂M, rfl⟩
      rw [hpair] at hσ
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
      rcases hσ with h | h
      · exact absurd h hg₂ne
      · exact h
    rw [hAg] at hmemg
    have hfix := (mem_fixV.mp (commSub_eq_bot_iff.mp hcomm.2 hw₀)) (g₂ * a * g₂⁻¹) hmemg
    calc a (g₂⁻¹ w₀) = g₂⁻¹ ((g₂ * a * g₂⁻¹) w₀) := by simp [MulAut.mul_apply]
      _ = g₂⁻¹ w₀ := by rw [hfix]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
