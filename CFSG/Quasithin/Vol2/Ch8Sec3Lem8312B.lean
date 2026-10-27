module

public import CFSG.Quasithin.Background.HL3WrV5
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem837E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative

namespace Ch8312

variable {G : Type} [Group G]

@[expose] def ch83V5 {V : Subgroup G} {hV : IsElemAbelian 2 V} (e : IntMod V hV ≃* WMod) :
    Subgroup G :=
  (V5.comap e.toMonoidHom).map (ch83Val hV)

@[expose] def modelImg {V : Subgroup G} {hV : IsElemAbelian 2 V} (e : IntMod V hV ≃* WMod)
    (W : Subgroup G) : Subgroup WMod :=
  (W.comap (ch83Val hV)).map e.toMonoidHom

variable {V : Subgroup G} {hV : IsElemAbelian 2 V} (e : IntMod V hV ≃* WMod)

theorem mem_ch83V5 {g : G} : g ∈ ch83V5 e ↔ ∃ w : IntMod V hV, e w ∈ V5 ∧ w.val = g := by
  unfold ch83V5
  simp only [Subgroup.mem_map, Subgroup.mem_comap]
  rfl

theorem mem_modelImg {W : Subgroup G} {X : WMod} : X ∈ modelImg e W ↔ (e.symm X).val ∈ W := by
  unfold modelImg
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (e.symm (e w)).val ∈ W
    rw [MulEquiv.symm_apply_apply]
    exact hw
  · intro h
    exact ⟨e.symm X, h, by simp⟩

theorem ch83V5_le : ch83V5 e ≤ V := by
  rintro _ ⟨w, -, rfl⟩
  exact w.val_mem

theorem mem_ch83V5_iff_of_mem {g : G} (hg : g ∈ V) :
    g ∈ ch83V5 e ↔ e (IntMod.mk hV ⟨g, hg⟩) ∈ V5 := by
  rw [mem_ch83V5]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro h
    exact ⟨_, h, rfl⟩

theorem congrHom_convI_apply (g : Subgroup.normalizer (V : Set G)) (w : IntMod V hV) :
    congrHom e (convI hV g) (e w) = e (convI hV g w) := by
  change e (convI hV g (e.symm (e w))) = e (convI hV g w)
  rw [MulEquiv.symm_apply_apply]

theorem act_mem_modelImg {W : Subgroup G} (g : Subgroup.normalizer (V : Set G))
    (hgW : (g : G) ∈ Subgroup.normalizer (W : Set G)) {X : WMod} (hX : X ∈ modelImg e W) :
    congrHom e (convI hV g) X ∈ modelImg e W := by
  rw [mem_modelImg] at hX ⊢
  change (e.symm (e (convI hV g (e.symm X)))).val ∈ W
  rw [MulEquiv.symm_apply_apply, convI_apply_val]
  exact (Subgroup.mem_normalizer_iff.mp hgW _).mp hX

section Setting

variable {T L I : Subgroup G} {hV : IsElemAbelian 2 (fsuV T I)}
  (e : IntMod (fsuV T I) hV ≃* WMod) {z : G}

theorem act_fix_iff (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0)
    (g : Subgroup.normalizer (fsuV T I : Set G)) :
    congrHom e (convI hV g) (eW 0 0) = eW 0 0 ↔
      (g : G) ∈ Subgroup.centralizer ({z} : Set G) := by
  have key : congrHom e (convI hV g) (eW 0 0) = eW 0 0 ↔ (g : G) * z * (g : G)⁻¹ = z := by
    rw [← hez, congrHom_convI_apply, e.injective.eq_iff]
    constructor
    · intro h
      have h3 := congrArg IntMod.val h
      rw [convI_apply_val] at h3
      exact h3
    · intro h
      apply IntMod.val_injective
      rw [convI_apply_val]
      exact h
  rw [key, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    rw [Set.mem_singleton_iff.1 hk]
    calc z * (g : G) = ((g : G) * z * (g : G)⁻¹) * g := by rw [h]
      _ = g * z := by group
  · intro h
    rw [← h z rfl, mul_inv_cancel_right]

theorem act_mem_stabE (he : (autI hV (fsuL0 T L)).map (congrHom e) = img) (hz : z ∈ fsuV T I)
    (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) {g : G}
    (hgN : g ∈ Subgroup.normalizer (fsuV T I : Set G)) (hgM : g ∈ fsuM T L)
    (hgz : g ∈ Subgroup.centralizer ({z} : Set G)) :
    congrHom e (convI hV ⟨g, hgN⟩) ∈ stabE :=
  mem_stabE_iff.2 ⟨congrHom_mem_norm e he (convI_mem_normalizer_autI hV (g := ⟨g, hgN⟩) hgM),
    (act_fix_iff e hz hez ⟨g, hgN⟩).2 hgz⟩

theorem le_normalizer_ch83V5 (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0)
    (hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    fsuM T L ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (ch83V5 e : Set G) := by
  intro g hg
  have key : ∀ g ∈ fsuM T L ⊓ Subgroup.centralizer ({z} : Set G), ∀ v ∈ ch83V5 e,
      g * v * g⁻¹ ∈ ch83V5 e := by
    intro g hg v hv
    obtain ⟨w, hw, rfl⟩ := (mem_ch83V5 e).1 hv
    refine (mem_ch83V5 e).2 ⟨convI hV ⟨g, hMV hg.1⟩ w, ?_, convI_apply_val _ _ _⟩
    rw [← congrHom_convI_apply]
    exact map_mem_V5_of_mem_stabE (act_mem_stabE e he hz hez _ hg.1 hg.2) hw
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => key g hg v hv, fun hv => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hv
  simpa [mul_assoc] using this

theorem exists_act_eq [Finite G]
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    (hY : (U3.prod U3).map rho ≤ (autI hV T).map (congrHom e)) (hz : z ∈ fsuV T I)
    (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) :
    (∃ g ∈ ch83X T L z, ∃ hg : g ∈ Subgroup.normalizer (fsuV T I : Set G),
        congrHom e (convI hV ⟨g, hg⟩) = rho (c3, 1)) ∧
      (∃ g ∈ ch83X T L z, ∃ hg : g ∈ Subgroup.normalizer (fsuV T I : Set G),
        congrHom e (convI hV ⟨g, hg⟩) = rho (1, c3)) ∧
      (∃ t ∈ T, ∃ ht : t ∈ Subgroup.normalizer (fsuV T I : Set G),
        congrHom e (convI hV ⟨t, ht⟩) = rho (u0, 1)) ∧
      ∃ t ∈ T, ∃ ht : t ∈ Subgroup.normalizer (fsuV T I : Set G),
        congrHom e (convI hV ⟨t, ht⟩) ∉ img := by
  have hXL : ch83X T L z ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have hXN : ch83X T L z ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    hXL.trans (le_sup_left.trans hN)
  have hXimg : ∀ c : MulAut WMod, c ∈ img → c (eW 0 0) = eW 0 0 → orderOf c = 3 →
      ∃ g ∈ ch83X T L z, ∃ hg : g ∈ Subgroup.normalizer (fsuV T I : Set G),
        congrHom e (convI hV ⟨g, hg⟩) = c := by
    intro c hc hcE hc3
    have hc' : c ∈ (autI hV (fsuL0 T L)).map (congrHom e) := by
      rw [he]
      exact hc
    obtain ⟨ψ, hψ, rfl⟩ := hc'
    obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hψ
    have hlz : (l : G) ∈ Subgroup.centralizer ({z} : Set G) := (act_fix_iff e hz hez l).1 hcE
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient
      (fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G)) (l : G) ⟨hlL, hlz⟩
    have hpow : congrHom e (convI hV l) ^ 2 ^ k ∈ (Ch837.actOn hV e hXN).range := by
      refine ⟨⟨(l : G) ^ 2 ^ k, hk⟩, ?_⟩
      rw [Ch837.actOn_apply, ← map_pow, ← map_pow]
      rfl
    obtain ⟨⟨g, hgX⟩, hg⟩ := mem_of_two_pow_mem hc3 hpow
    exact ⟨g, hgX, hXN hgX, hg⟩
  refine ⟨hXimg _ (rho_mem_img _) (rho_fix_E00 c3_mem_P1 P1.one_mem)
      (by rw [orderOf_injective rho rho_injective]; exact orderOf_c3_one),
    hXimg _ (rho_mem_img _) (rho_fix_E00 P1.one_mem c3_mem_P1)
      (by rw [orderOf_injective rho rho_injective]; exact orderOf_one_c3), ?_, ?_⟩
  · obtain ⟨ψ, hψ, hψe⟩ := hY ⟨(u0, 1), ⟨u0_mem_U3, U3.one_mem⟩, rfl⟩
    obtain ⟨t, htT, rfl⟩ := (mem_autI hV).1 hψ
    exact ⟨t, htT, t.2, hψe⟩
  · exact Ch837.exists_not_mem_img h37 h38 h326 hyp hV hrow hN e he

theorem symm_eW00 (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) :
    (e.symm (eW 0 0)).val = z := by
  rw [← hez, MulEquiv.symm_apply_apply]
  rfl

theorem mk_val (w : IntMod (fsuV T I) hV) : IntMod.mk hV ⟨w.val, w.val_mem⟩ = w := rfl

theorem le_zpowers_of_modelImg_le (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0)
    {W : Subgroup G} (hWV : W ≤ fsuV T I) (h : modelImg e W ≤ Z00) : W ≤ Subgroup.zpowers z := by
  intro w hw
  have hX : e (IntMod.mk hV ⟨w, hWV hw⟩) ∈ modelImg e W := by
    rw [mem_modelImg, MulEquiv.symm_apply_apply]
    exact hw
  rcases mem_Z00_iff.1 (h hX) with h0 | h1
  · have h2 : e (IntMod.mk hV ⟨w, hWV hw⟩) = 1 := Multiplicative.toAdd.injective h0
    have h3 := congrArg (fun X => (e.symm X).val) h2
    simp only [MulEquiv.symm_apply_apply, map_one] at h3
    change w = 1 at h3
    rw [h3]
    exact Subgroup.one_mem _
  · have h2 : e (IntMod.mk hV ⟨w, hWV hw⟩) = eW 0 0 := Multiplicative.toAdd.injective h1
    have h3 := congrArg (fun X => (e.symm X).val) h2
    simp only [MulEquiv.symm_apply_apply] at h3
    rw [symm_eW00 e hz hez] at h3
    change w = z at h3
    rw [h3]
    exact Subgroup.mem_zpowers z

theorem eq_of_le_ch83V5 [Finite G]
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    (hY : (U3.prod U3).map rho ≤ (autI hV T).map (congrHom e)) (hz : z ∈ fsuV T I)
    (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) {W : Subgroup G}
    (hzW : Subgroup.zpowers z ≤ W) (hW5 : W ≤ ch83V5 e)
    (hWn : ch83X T L z ⊔ T ≤ Subgroup.normalizer (W : Set G)) :
    W = Subgroup.zpowers z ∨ W = ch83V5 e := by
  obtain ⟨⟨g₁, hg₁X, hg₁N, hg₁⟩, ⟨g₂, hg₂X, hg₂N, hg₂⟩, -, ⟨t, htT, htN, hti⟩⟩ :=
    exists_act_eq e h37 h38 h326 hyp hrow hN he hY hz hez
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hWV : W ≤ fsuV T I := hW5.trans (ch83V5_le e)
  have inv : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (fsuV T I : Set G)),
      g ∈ ch83X T L z ⊔ T → ∀ X ∈ modelImg e W, congrHom e (convI hV ⟨g, hg⟩) X ∈ modelImg e W :=
    fun g hg hgXT X hX => act_mem_modelImg e ⟨g, hg⟩ (hWn hgXT) hX
  have hz' : eW 0 0 ∈ modelImg e W := by
    rw [mem_modelImg, symm_eW00 e hz hez]
    exact hzW (Subgroup.mem_zpowers z)
  have h5 : modelImg e W ≤ V5 := by
    intro X hX
    rw [mem_modelImg] at hX
    have := (mem_ch83V5_iff_of_mem e (hWV hX)).1 (hW5 hX)
    rwa [mk_val, MulEquiv.apply_symm_apply] at this
  by_cases hWz : modelImg e W ≤ Z00
  · exact Or.inl (le_antisymm (le_zpowers_of_modelImg_le e hz hez hWV hWz) hzW)
  · right
    refine le_antisymm hW5 fun v hv => ?_
    obtain ⟨w, hw, rfl⟩ := (mem_ch83V5 e).1 hv
    have h := V5_le_of_irred hz' h5 hWz
      (fun X hX => by rw [← hg₁]; exact inv g₁ hg₁N (Subgroup.mem_sup_left hg₁X) X hX)
      (fun X hX => by rw [← hg₂]; exact inv g₂ hg₂N (Subgroup.mem_sup_left hg₂X) X hX)
      (act_mem_stabE e he hz hez htN (hTM htT) (hTz htT)) hti
      (fun X hX => inv t htN (Subgroup.mem_sup_right htT) X hX) hw
    rw [mem_modelImg, MulEquiv.symm_apply_apply] at h
    exact h

theorem eq_of_ch83V5_le [Finite G]
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    (hY : (U3.prod U3).map rho ≤ (autI hV T).map (congrHom e)) (hz : z ∈ fsuV T I)
    (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) {W : Subgroup G}
    (h5W : ch83V5 e ≤ W) (hWV : W ≤ fsuV T I)
    (hWn : ch83X T L z ⊔ T ≤ Subgroup.normalizer (W : Set G)) :
    W = ch83V5 e ∨ W = fsuV T I := by
  obtain ⟨⟨g₁, hg₁X, hg₁N, hg₁⟩, ⟨g₂, hg₂X, hg₂N, hg₂⟩, ⟨t, htT, htN, htu⟩, -⟩ :=
    exists_act_eq e h37 h38 h326 hyp hrow hN he hY hz hez
  have inv : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (fsuV T I : Set G)),
      g ∈ ch83X T L z ⊔ T → ∀ X ∈ modelImg e W, congrHom e (convI hV ⟨g, hg⟩) X ∈ modelImg e W :=
    fun g hg hgXT X hX => act_mem_modelImg e ⟨g, hg⟩ (hWn hgXT) hX
  have h5 : V5 ≤ modelImg e W := by
    intro X hX
    rw [mem_modelImg]
    refine h5W ((mem_ch83V5 e).2 ⟨e.symm X, ?_, rfl⟩)
    rwa [MulEquiv.apply_symm_apply]
  by_cases hW5 : modelImg e W ≤ V5
  · left
    refine le_antisymm (fun w hw => ?_) h5W
    refine (mem_ch83V5_iff_of_mem e (hWV hw)).2 (hW5 ?_)
    rw [mem_modelImg, MulEquiv.symm_apply_apply]
    exact hw
  · right
    have htop := eq_top_of_irred h5 hW5
      (fun X hX => by rw [← hg₁]; exact inv g₁ hg₁N (Subgroup.mem_sup_left hg₁X) X hX)
      (fun X hX => by rw [← hg₂]; exact inv g₂ hg₂N (Subgroup.mem_sup_left hg₂X) X hX)
      (fun X hX => by rw [← htu]; exact inv t htN (Subgroup.mem_sup_right htT) X hX)
    refine le_antisymm hWV fun v hv => ?_
    have h : e (IntMod.mk hV ⟨v, hv⟩) ∈ modelImg e W := by rw [htop]; trivial
    rw [mem_modelImg, MulEquiv.symm_apply_apply] at h
    exact h

theorem mem_zpowers_of_orderOf_two {w : G} [Finite G] (hz2 : orderOf z = 2)
    (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz2] at hw
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
  have hn' : n < 2 := Finset.mem_range.mp hn
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · exact Or.inl (pow_zero z)
  · exact Or.inr (pow_one z)

theorem mem_ch83V5_z (hz : z ∈ fsuV T I) (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) :
    z ∈ ch83V5 e := by
  rw [mem_ch83V5_iff_of_mem e hz, hez]
  exact eW00_mem_V5

theorem zpowers_lt_ch83V5 [Finite G] (hz2 : orderOf z = 2) (hz : z ∈ fsuV T I)
    (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) : Subgroup.zpowers z < ch83V5 e := by
  refine lt_of_le_of_ne ((Subgroup.zpowers_le).mpr (mem_ch83V5_z e hz hez)) fun h => ?_
  have hv : (e.symm (eW 0 1)).val ∈ ch83V5 e := by
    refine (mem_ch83V5 e).2 ⟨e.symm (eW 0 1), ?_, rfl⟩
    rw [MulEquiv.apply_symm_apply]
    exact eW_mem_V5_row 1
  rw [← h] at hv
  rcases mem_zpowers_of_orderOf_two hz2 hv with h1 | h1
  · have h2 : e.symm (eW 0 1) = 1 := IntMod.val_injective h1
    have h3 := congrArg (fun X => Multiplicative.toAdd (e X)) h2
    simp only [MulEquiv.apply_symm_apply, map_one, toAdd_one, toAdd_eW] at h3
    exact absurd h3 (by decide)
  · have h2 : e.symm (eW 0 1) = IntMod.mk hV ⟨z, hz⟩ := IntMod.val_injective h1
    have h3 := congrArg (fun X => Multiplicative.toAdd (e X)) h2
    simp only [MulEquiv.apply_symm_apply, hez, toAdd_eW] at h3
    exact absurd h3 (by decide)

theorem almostSpecialHyp [Finite G]
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h326 : Stmt3_2_6C)
    (hyp : Hyp7_0_2 G T L I) [IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G)) (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z)
    (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    (hY : (U3.prod U3).map rho ≤ (autI hV T).map (congrHom e)) (hz : z ∈ fsuV T I)
    (hez : e (IntMod.mk hV ⟨z, hz⟩) = eW 0 0) :
    AlmostSpecialHyp (ch83V5 e) (Subgroup.zpowers z) (fsuL0 T L) T
      (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hXL : ch83X T L z ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have hXz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hXT : ch83X T L z ⊔ T ≤ fsuM T L ⊓ Subgroup.centralizer ({z} : Set G) :=
    sup_le (le_inf (hXL.trans Subgroup.le_normalizer) hXz) (le_inf hTM hTz)
  have hNz : Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := Ch8313.normalizer_zpowers_eq hz2
  have hlOne : lOne (fsuL0 T L) (Subgroup.zpowers z) = ch83X T L z := by
    unfold lOne
    rw [hNz, ← F6.twoResidual_eq_oTwoUpper]
    rfl
  have hnn := Ch837.not_le_normalizer_of_row hrow
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hnn
  have hL := Vol2.Ch10.SecA.perfect_L hyp.fsu.maximal.1
  have hLt : ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ = CFSG.conjugate L t := by
    rw [Vol2.Ch10.SecA.conjugate_eq_map, ← Subgroup.map_commutator, hL]
  have hL0 : ⁅fsuL0 T L, fsuL0 T L⁆ = fsuL0 T L := by
    rw [Vol2.Ch10.SecA.fsuL0_eq_sup_of_fsu h37 h38 hyp.fsu hnn ht htn]
    exact Ch837.commutator_sup_eq hL hLt
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    Ch837.zpowers_le_pCoreOf hz2 (Subgroup.mem_centralizer_singleton_iff.mpr rfl) le_rfl
  have hPGz : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  refine
    { elemAbelian := B2F.isElemAbelian_mono (ch83V5_le e) hV
      ne_bot := fun h => hz1 (Subgroup.zpowers_eq_bot.mp h)
      le_V := (Subgroup.zpowers_le).mpr (mem_ch83V5_z e hz hez)
      oTwo_eq := eq_oTwoUpper_of_perfect hL0
      V_le_T := (ch83V5_le e).trans hVT
      T_le_normV₁ := by rw [hNz]; exact hTz
      T_le_normV := (le_inf hTM hTz).trans (le_normalizer_ch83V5 e he hz hez hMV)
      T_le_normL := le_normalizer_conjClosure L T
      sylow_LT := Ch837.isSylowTwoOf_of_le hyp.fsu.sylow le_sup_right
      H_le := by rw [hNz]
      lOne_sup_le := by rw [hlOne]; exact sup_le hXz hTz
      sylow_H := Ch837.isSylowTwoOf_of_le hyp.fsu.sylow hTz
      charTwo := charTwo_of_inH' hyp.fsu.qtke hyp.fsu.sylow ⟨hTz, hPGz⟩
      irred := ?_ }
  rw [hlOne]
  refine ⟨zpowers_lt_ch83V5 e hz2 hz hez, hXT.trans (le_normalizer_ch83V5 e he hz hez hMV),
    by rw [hNz]; exact sup_le hXz hTz, fun W h1 h2 h3 => ?_⟩
  exact eq_of_le_ch83V5 e h37 h38 h326 hyp hrow hN hTz he hY hz hez h1 h2 h3

end Setting

end Ch8312

end CFSG.Quasithin.H13
