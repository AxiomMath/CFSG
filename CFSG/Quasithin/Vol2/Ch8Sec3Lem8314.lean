module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem835

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open
open scoped Matrix

theorem relIndex_stabilizer_eq_two {W : Type*} [CommGroup W] {A : Subgroup (MulAut W)} {e : W}
    (he1 : e ≠ 1) (he2 : e * e = 1) (he : ∀ y ∈ A, y e = e) {g : MulAut W} (hgA : g ∈ A)
    {D : W} (hgD : g D = D * e) (hAD : ∀ y ∈ A, y D = D ∨ y D = D * e) :
    (A ⊓ MulAction.stabilizer (MulAut W) D).relIndex A = 2 := by
  have hDe : D * e ≠ D := fun h => he1 (mul_left_cancel (h.trans (mul_one D).symm))
  have hmem : ∀ c : ↥A, c ∈ (A ⊓ MulAction.stabilizer (MulAut W) D).subgroupOf A ↔
      (c : MulAut W) D = D := fun c => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => h.2, fun h => ⟨c.2, h⟩⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨g, hgA⟩, fun b => ?_⟩
  rw [hmem, hmem]
  have hbg : ((b * ⟨g, hgA⟩ : ↥A) : MulAut W) D = (b : MulAut W) D * e := by
    change (b : MulAut W) (g D) = _
    rw [hgD, map_mul, he _ b.2]
  rw [hbg]
  rcases hAD _ b.2 with h | h
  · rw [h]
    exact Or.inr ⟨rfl, hDe⟩
  · rw [h, mul_assoc, he2, mul_one]
    exact Or.inl ⟨rfl, hDe⟩

theorem exists_eW_of_mem_Shat {g : MulAut WMod} (hg : g ∈ Shat) (hg1 : g ≠ 1) :
    ∃ D : WMod, g D = D * eW 0 0 ∧ ∀ s ∈ Shat, s D = D ∨ s D = D * eW 0 0 := by
  obtain ⟨⟨a, b⟩, ⟨⟨x, y, ha⟩, ⟨x', y', hb⟩⟩, rfl⟩ := hg
  have key : ∀ (i j : Fin 3) (f : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2),
      (∀ u v u' v' : ZMod 2, scenMat u v * Matrix.single i j 1 * (scenMat u' v')ᵀ =
        Matrix.single i j 1 + Matrix.single 0 0 (f u v u' v')) → f x y x' y' = 1 →
      ∃ D : WMod, rho (a, b) D = D * eW 0 0 ∧
        ∀ s ∈ Shat, s D = D ∨ s D = D * eW 0 0 := by
    intro i j f hf h1
    refine ⟨eW i j, ?_, ?_⟩
    · apply Multiplicative.toAdd.injective
      rw [toAdd_rho_eW ha hb, hf, h1]
      rfl
    · rintro _ ⟨⟨a', b'⟩, ⟨⟨u, v, ha'⟩, ⟨u', v', hb'⟩⟩, rfl⟩
      exact eq_or_eq_mul_eW (by rw [toAdd_rho_eW ha' hb', hf]; rfl)
  by_cases hx : x = 1
  · exact key 1 0 (fun u _ _ _ => u) scenMat_E10 hx
  by_cases hy : y = 1
  · exact key 2 0 (fun _ v _ _ => v) scenMat_E20 hy
  by_cases hx' : x' = 1
  · exact key 0 1 (fun _ _ u' _ => u') scenMat_E01 hx'
  by_cases hy' : y' = 1
  · exact key 0 2 (fun _ _ _ v' => v') scenMat_E02 hy'
  exfalso
  apply hg1
  have h0 : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
  rw [h0 x hx, h0 y hy, scenMat_zero] at ha
  rw [h0 x' hx', h0 y' hy', scenMat_zero] at hb
  have ha1 : a = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact ha
  have hb1 : b = 1 := by
    apply Subtype.ext
    apply Units.ext
    exact hb
  rw [ha1, hb1]
  exact map_one rho

end L3Wr

end H

namespace H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative

@[expose] def Stmt8_3_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
      (3 : ℕ∞) < E3.rParam (fsuV T I)

@[expose] def Stmt8_3_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ z : G, orderOf z = 2 →
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z →
      ∀ g x h : G, x ∈ conjSubgroup (fsuV T I) g → x ∈ fsuV T I → x = h * z * h⁻¹ →
        conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (fsuV T I : Set G)

theorem stmt8_3_14_of (hmod : StmtFSUModule) (h8311 : Stmt8_3_11) (h8313 : Stmt8_3_13) :
    Stmt8_3_14 := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hr := h8311 G T L I hyp h731 hc hrow
  have h13 := h8313 G T L I hyp h731 hc hrow z hz2 hzV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    ⟨hTK, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hST : ch83S T L z ≤ T := pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzz : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  obtain ⟨e, he, hz, hez⟩ := exists_model_eW00 hyp hV hrow hz1 hzV
  have hSh := map_autI_ch83S_le_Shat hyp hV hN hzmem.2 e he hz hez
  have hezs : e.symm (eW 0 0) = IntMod.mk hV ⟨z, hz⟩ := by
    rw [← hez, MulEquiv.symm_apply_apply]
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAS, g, hAg, hAm⟩ := hA
  by_contra hAC
  have hAT : A ≤ T := hAS.trans hST
  have hAN : A ≤ Subgroup.normalizer (fsuV T I : Set G) := hAT.trans (le_sup_right.trans hN)
  have hAbot : autI hV A ≠ ⊥ := (autI_eq_bot_iff hV hAN).not.2 hAC
  obtain ⟨⟨ψ, hψA⟩, hψ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAbot
  have hψ1' : ψ ≠ 1 := fun h => hψ1 (Subtype.ext h)
  have hShat : ∀ y ∈ autI hV A, congrHom e y ∈ Shat := fun y hy =>
    hSh ⟨y, autI_mono hV hAS hy, rfl⟩
  have hφ1 : congrHom e ψ ≠ 1 := fun h =>
    hψ1' (congrHom_injective e (h.trans (map_one _).symm))
  obtain ⟨D, hψD, hShD⟩ := exists_eW_of_mem_Shat (hShat ψ hψA) hφ1
  have htr : ∀ y : MulAut (IntMod (fsuV T I) hV), y (e.symm D) = e.symm (congrHom e y D) :=
    fun y => by
      change y (e.symm D) = e.symm (e (y (e.symm D)))
      rw [MulEquiv.symm_apply_apply]
  have hmulz : e.symm (D * eW 0 0) = e.symm D * IntMod.mk hV ⟨z, hz⟩ := by
    rw [map_mul, hezs]
  have hψv : ψ (e.symm D) = e.symm D * IntMod.mk hV ⟨z, hz⟩ :=
    ((htr ψ).trans (congrArg e.symm hψD)).trans hmulz
  have hAD : ∀ y ∈ autI hV A, y (e.symm D) = e.symm D ∨
      y (e.symm D) = e.symm D * IntMod.mk hV ⟨z, hz⟩ := fun y hy => by
    rcases hShD _ (hShat y hy) with h | h
    · exact Or.inl ((htr y).trans (congrArg e.symm h))
    · exact Or.inr (((htr y).trans (congrArg e.symm h)).trans hmulz)
  have hfz : ∀ y ∈ autI hV A, y (IntMod.mk hV ⟨z, hz⟩) = IntMod.mk hV ⟨z, hz⟩ := by
    intro y hy
    obtain ⟨t, htA, rfl⟩ := (mem_autI hV).1 hy
    apply IntMod.val_injective
    rw [convI_apply_val]
    change (t : G) * z * (t : G)⁻¹ = z
    rw [Subgroup.mem_centralizer_iff.mp hzmem.2 t (hAT htA), mul_inv_cancel_right]
  have hz1' : IntMod.mk hV ⟨z, hz⟩ ≠ 1 := fun h => hz1 (congrArg IntMod.val h)
  have hzz' : IntMod.mk hV ⟨z, hz⟩ * IntMod.mk hV ⟨z, hz⟩ = 1 :=
    IntMod.val_injective hzz
  have hidx := relIndex_stabilizer_eq_two hz1' hzz' hfz hψA hψv hAD
  have hB''A : autI hV A ⊓ MulAction.stabilizer (MulAut (IntMod (fsuV T I) hV)) (e.symm D) ≤
      autI hV A := inf_le_left
  set B := preI hV A hAN
    (autI hV A ⊓ MulAction.stabilizer (MulAut (IntMod (fsuV T I) hV)) (e.symm D)) with hBdef
  have hBA : B ≤ A := preI_le hV
  have hBN : B ≤ Subgroup.normalizer (fsuV T I : Set G) := hBA.trans hAN
  have hpre : autI hV B =
      autI hV A ⊓ MulAction.stabilizer (MulAut (IntMod (fsuV T I) hV)) (e.symm D) :=
    autI_preI hV hB''A
  have hm1 : mQuot A B = 1 := by
    rw [hBdef, ← mQuot_autI_preI hV hAN hB''A, mQuot, hidx, padicValNat.self (by norm_num)]
  have hadd := mQuot_add (V := conjSubgroup (fsuV T I) g) hBA hAg
  rw [hm1, hAm] at hadd
  have hCB : Subgroup.centralizer (B : Set G) ≤
      Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
    by_contra hC
    have h1 := rParam_le_mQuot (hBA.trans hAg) hC
    rw [rParam_conj, hadd] at h1
    exact absurd (lt_of_lt_of_le hr h1) (by norm_num)
  have hvB : (e.symm D).val ∈ Subgroup.centralizer (B : Set G) := by
    have hfix : e.symm D ∈ fixV (autI hV B) := by
      rw [hpre]
      exact fun y hy => hy.2
    exact (mem_fixV_autI hV hBN (e.symm D)).1 hfix
  obtain ⟨a, haA, rfl⟩ := (mem_autI hV).1 hψA
  have hav : (a : G) * (e.symm D).val * (a : G)⁻¹ = (e.symm D).val * z := by
    have h1 := congrArg IntMod.val hψv
    rw [convI_apply_val] at h1
    exact h1
  have hvz : (e.symm D).val * z = z * (e.symm D).val :=
    setLike_mul_comm (e.symm D).val_mem hz
  have hzVg : z ∈ conjSubgroup (fsuV T I) g := by
    have haVg : (a : G) ∈ conjSubgroup (fsuV T I) g := hAg haA
    have h1 : (e.symm D).val * a * ((e.symm D).val)⁻¹ ∈ conjSubgroup (fsuV T I) g :=
      (Subgroup.mem_normalizer_iff.mp (hCB hvB) a).mp haVg
    have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ haVg)
    have heq : (e.symm D).val * a * ((e.symm D).val)⁻¹ * (a : G)⁻¹ = z := by
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
      calc (e.symm D).val * a * ((e.symm D).val)⁻¹ * (a : G)⁻¹
          = (e.symm D).val * ((a : G) * (e.symm D).val * (a : G)⁻¹)⁻¹ := by group
        _ = (e.symm D).val * ((e.symm D).val * z)⁻¹ := by rw [hav]
        _ = (e.symm D).val * (z * (e.symm D).val)⁻¹ := by rw [hvz]
        _ = z⁻¹ := by group
        _ = z := hzi
    rwa [heq] at h2
  exact hAC (hAg.trans (h13 g z 1 hzVg hz (by group)))

end H13

end CFSG.Quasithin
