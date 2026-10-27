module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Lat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3OuterA
import CFSG.Quasithin.Background.StabSubBasics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_l3_iSup_erase_eq {k : ℕ} (f : Fin k → Subgroup W) (i₀ : Fin k) :
    (⨆ j ∈ Finset.univ.erase i₀, f j) = ⨆ (j : Fin k) (_ : j ≠ i₀), f j := by
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun hj => ?_
    exact le_iSup₂ (f := fun j (_ : j ≠ i₀) => f j) j (Finset.mem_erase.mp hj).1
  · refine iSup_le fun j => iSup_le fun hj => ?_
    exact le_iSup₂ (f := fun j (_ : j ∈ Finset.univ.erase i₀) => f j) j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)

theorem s16h_e3_l3_not_fix_of_not_inner (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {k : ℕ} (S : S16hL3Split L k) (hk : 1 ≤ k) {τ : MulAut W}
    (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hout : ¬ ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    ∃ z ∈ commSub ⊤ L ⊓ fixV L, τ z ≠ z := by
  classical
  by_contra hcon
  rw [not_exists] at hcon
  have hfix : ∀ z ∈ commSub ⊤ L ⊓ fixV L, τ z = z := by
    intro z hz
    by_contra hne
    exact hcon z ⟨hz, hne⟩
  have hτU : ∀ u ∈ commSub ⊤ L, τ u ∈ commSub ⊤ L := by
    intro u hu
    have h : τ ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
      StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := τ)
        (mem_stabSub.2 fun u => by simp) hτN
    exact (mem_stabSub.mp h u).mpr hu
  have hτF : ∀ z ∈ fixV L, τ z ∈ fixV L :=
    fun z hz => fixV_apply_mem_of_mem_normalizer (L := L) hτN hz
  have hτZ : ∀ z ∈ commSub ⊤ L ⊓ fixV L, τ z ∈ commSub ⊤ L ⊓ fixV L := by
    intro z hz
    exact ⟨hτU z hz.1, hτF z hz.2⟩
  let i₀ : Fin k := ⟨0, by omega⟩
  let J₀' : Subgroup W := (S.J i₀).map τ.toMonoidHom
  let P : Subgroup W := ⨆ (j : Fin k) (_ : j ≠ i₀), S.J j
  have hJ₀'inv : ∀ l ∈ L, ∀ y ∈ J₀', l y ∈ J₀' := by
    intro l hl y hy
    change y ∈ (S.J i₀).map τ.toMonoidHom at hy
    obtain ⟨x, hx, rfl⟩ := hy
    change l (τ x) ∈ (S.J i₀).map τ.toMonoidHom
    refine ⟨(τ⁻¹ * l * τ) x,
      S.J_inv i₀ (τ⁻¹ * l * τ) ((Subgroup.mem_normalizer_iff''.1 hτN l).1 hl) x hx, ?_⟩
    show τ ((τ⁻¹ * l * τ) x) = l (τ x)
    simp [MulAut.mul_apply]
  have hao : ¬ J₀' ≤ S.J i₀ := by
    intro hle
    have hτJ : ∀ x ∈ S.J i₀, τ x ∈ S.J i₀ := by
      intro x hx
      exact hle (Subgroup.mem_map_of_mem τ.toMonoidHom hx)
    have hτI : ∀ u ∈ S.I i₀, τ u ∈ S.I i₀ := by
      intro u hu
      have hI : S.I i₀ = S.J i₀ ⊔ (commSub ⊤ L ⊓ fixV L) := (S.J_sup_Z i₀).symm
      rw [hI] at hu ⊢
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
      rw [map_mul]
      exact Subgroup.mul_mem_sup (hτJ a ha) (hτZ b hb)
    exact hout (s16h_e3_l3_inner_of_stab (S.I_nat i₀) hτN hτI hτZ)
  have hYF : S.J i₀ ⊓ J₀' ≤ S.J i₀ ⊓ fixV L := by
    by_contra hY
    have hYJ : S.J i₀ ⊓ J₀' ≤ S.J i₀ := inf_le_left
    have hYinv : ∀ l ∈ L, ∀ y ∈ S.J i₀ ⊓ J₀', l y ∈ S.J i₀ ⊓ J₀' := by
      intro l hl y hy
      rw [Subgroup.mem_inf] at hy ⊢
      exact ⟨S.J_inv i₀ l hl y hy.1, hJ₀'inv l hl y hy.2⟩
    have heq : S.J i₀ ⊓ J₀' = S.J i₀ :=
      s16h_e3_l3_eq_of_not_le_fixV (S.J_nat i₀) (S.J_comm i₀) hYJ hYinv hY
    have hle : S.J i₀ ≤ J₀' := by
      intro x hx
      have hx' : x ∈ S.J i₀ ⊓ J₀' := by rw [heq]; exact hx
      exact (Subgroup.mem_inf.mp hx').2
    have hcard : Nat.card ↥J₀' = Nat.card ↥(S.J i₀) :=
      Subgroup.card_map_of_injective (f := τ.toMonoidHom) τ.injective
    have heqJ : J₀' = S.J i₀ :=
      (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
    exact hao (le_of_eq heqJ)
  have hU_split : (⨆ i, S.J i) = S.J i₀ ⊔ P := by
    change (⨆ i, S.J i) = S.J i₀ ⊔ ⨆ (j : Fin k) (_ : j ≠ i₀), S.J j
    exact iSup_split_single (fun i => S.J i) i₀
  have hJ₀'U : J₀' ≤ commSub ⊤ L := by
    intro v hv
    change v ∈ (S.J i₀).map τ.toMonoidHom at hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact hτU x (by rw [← S.J_iSup]; exact le_iSup (fun i => S.J i) i₀ hx)
  have hXbot : (S.J i₀ ⊔ J₀') ⊓ P ≠ ⊥ := by
    intro hbot
    apply hao
    intro v hv
    have hvsup : v ∈ S.J i₀ ⊔ P := by
      rw [← hU_split, S.J_iSup]; exact hJ₀'U hv
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hvsup
    have hbX : b ∈ (S.J i₀ ⊔ J₀') ⊓ P := by
      refine ⟨?_, hb⟩
      have hbval : b = a⁻¹ * v := by rw [← hab]; group
      rw [hbval]
      exact Subgroup.mul_mem_sup ((S.J i₀).inv_mem ha) hv
    rw [hbot] at hbX
    have hb1 : b = 1 := Subgroup.mem_bot.mp hbX
    have hv' : v = a := by rw [← hab, hb1, mul_one]
    rw [hv']; exact ha
  have hPinv : ∀ l ∈ L, ∀ x ∈ P, l x ∈ P := by
    intro l hl x hx
    change x ∈ ⨆ (j : Fin k) (_ : j ≠ i₀), S.J j at hx
    change l x ∈ ⨆ (j : Fin k) (_ : j ≠ i₀), S.J j
    refine Subgroup.iSup_induction (C := fun z =>
        l z ∈ ⨆ (j : Fin k) (_ : j ≠ i₀), S.J j)
      (fun j : Fin k => ⨆ (_ : j ≠ i₀), S.J j) hx ?_ ?_ ?_
    · intro j y hy
      refine Subgroup.iSup_induction (C := fun z =>
          l z ∈ ⨆ (j : Fin k) (_ : j ≠ i₀), S.J j)
        (fun (_ : j ≠ i₀) => S.J j) hy ?_ ?_ ?_
      · intro hj w hw
        exact le_iSup₂ (f := fun j (_ : j ≠ i₀) => S.J j) j hj (S.J_inv j l hl w hw)
      · rw [map_one]
        exact Subgroup.one_mem _
      · intro a b ha hb
        rw [map_mul]
        exact mul_mem ha hb
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro a b ha hb
      rw [map_mul]
      exact mul_mem ha hb
  have hXinv : ∀ l ∈ L, ∀ x ∈ (S.J i₀ ⊔ J₀') ⊓ P,
      l x ∈ (S.J i₀ ⊔ J₀') ⊓ P := by
    intro l hl x hx
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨?_, hPinv l hl x hx.2⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx.1
    rw [map_mul]
    exact Subgroup.mul_mem_sup (S.J_inv i₀ l hl a ha) (hJ₀'inv l hl b hb)
  have hXfix : (S.J i₀ ⊔ J₀') ⊓ P ⊓ fixV L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyX, hyF⟩ := hy
    rw [Subgroup.mem_inf] at hyX
    obtain ⟨hyJ, hyP⟩ := hyX
    obtain ⟨a, ha, v, hv, hav⟩ := Subgroup.mem_sup.mp hyJ
    have hmemF : ∀ l ∈ L, l v * v⁻¹ ∈ S.J i₀ ⊓ fixV L := by
      intro l hl
      refine hYF ⟨?_, ?_⟩
      · have h1 : l a * l v = a * v := by
          rw [hav]
          have h2 := congrArg l hav
          rwa [map_mul, (mem_fixV.mp hyF) l hl] at h2
        have h3 : l v = (l a)⁻¹ * a * v := by
          calc l v = (l a)⁻¹ * (l a * l v) := by group
            _ = (l a)⁻¹ * (a * v) := by rw [h1]
            _ = (l a)⁻¹ * a * v := by group
        have heq : l v * v⁻¹ = a * (l a)⁻¹ := by
          calc l v * v⁻¹ = (l a)⁻¹ * a * (v * v⁻¹) := by rw [h3]; group
            _ = (l a)⁻¹ * a := by rw [mul_inv_cancel, mul_one]
            _ = a * (l a)⁻¹ := mul_comm _ _
        rw [heq]
        exact (S.J i₀).mul_mem ha ((S.J i₀).inv_mem (S.J_inv i₀ l hl a ha))
      · exact J₀'.mul_mem (hJ₀'inv l hl v hv) (J₀'.inv_mem hv)
    set x : W := τ⁻¹ v with hx
    have hxJ : x ∈ S.J i₀ := by
      change v ∈ (S.J i₀).map τ.toMonoidHom at hv
      obtain ⟨w, hw, hwv⟩ := hv
      rw [hx, ← hwv]
      simpa using hw
    have hσ : ∀ l' ∈ L, l' x * x⁻¹ ∈ S.J i₀ ⊓ fixV L := by
      intro l' hl'
      have hτinvN : τ⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
        (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hτN
      have hl : τ * l' * τ⁻¹ ∈ L := by
        have hmem' := (Subgroup.mem_normalizer_iff''.1 hτinvN l').1 hl'
        simpa using hmem'
      have hmem := hmemF (τ * l' * τ⁻¹) hl
      have hfixinv : ∀ z ∈ S.J i₀ ⊓ fixV L, τ⁻¹ z = z := by
        intro z hz
        have hzZ : z ∈ commSub ⊤ L ⊓ fixV L :=
          ⟨(by rw [← S.J_iSup]; exact le_iSup (fun i => S.J i) i₀ hz.1), hz.2⟩
        calc τ⁻¹ z = τ⁻¹ (τ z) := by rw [hfix z hzZ]
          _ = z := by simp
      have hcomp : l' x * x⁻¹ = τ⁻¹ ((τ * l' * τ⁻¹) v * v⁻¹) := by
        rw [hx]
        simp [MulAut.mul_apply]
      rw [hcomp, hfixinv _ hmem]
      exact hmem
    have hxF : x ∈ S.J i₀ ⊓ fixV L :=
      s16h_e3_l3_mem_of_comm_mem (S.J_nat i₀) hxJ hσ
    have hxZ : x ∈ commSub ⊤ L ⊓ fixV L :=
      ⟨(by rw [← S.J_iSup]; exact le_iSup (fun i => S.J i) i₀ hxF.1), hxF.2⟩
    have hvx : v = x := by
      calc v = τ x := by rw [hx]; simp
        _ = x := hfix x hxZ
    have hvJ : v ∈ S.J i₀ := by rw [hvx]; exact hxF.1
    have hyJ₀ : y ∈ S.J i₀ := by
      rw [← hav]
      exact (S.J i₀).mul_mem ha hvJ
    have hybot : y ∈ (⊥ : Subgroup W) := by
      have hmem : y ∈ S.J i₀ ⊓ P := ⟨hyJ₀, hyP⟩
      rwa [show S.J i₀ ⊓ P = ⊥ from S.J_ind i₀] at hmem
    exact Subgroup.mem_bot.mp hybot
  have hP_er : P = ⨆ j ∈ Finset.univ.erase i₀, S.J j := by
    change (⨆ (j : Fin k) (_ : j ≠ i₀), S.J j) = ⨆ j ∈ Finset.univ.erase i₀, S.J j
    exact (s16h_e3_l3_iSup_erase_eq (S.J) i₀).symm
  have hXT : (S.J i₀ ⊔ J₀') ⊓ P ≤ ⨆ j ∈ Finset.univ.erase i₀, S.J j := by
    rw [← hP_er]
    exact inf_le_right
  exact s16h_e3_l3_inf_fixV_ne_bot hW S (Finset.univ.erase i₀) hXT hXinv hXbot hXfix

theorem s16h_e3_l3_rank_outer (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {k : ℕ}
    (S : S16hL3Split L k) (hk : 1 ≤ k) {τ : MulAut W}
    (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hout : ¬ ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    4 ≤ rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers τ)) := by
  classical
  let i₀ : Fin k := ⟨0, by omega⟩
  let Z : Subgroup W := commSub ⊤ L ⊓ fixV L
  let I₀ : Subgroup W := S.I i₀
  have hτU : ∀ u ∈ commSub ⊤ L, τ u ∈ commSub ⊤ L := by
    intro u hu
    have h : τ ∈ stabSub (commSub (⊤ : Subgroup W) L) :=
      StabLat.mem_stabSub_commSub (X := L) (Y := ⊤) (g := τ)
        (mem_stabSub.2 fun u => by simp) hτN
    exact (mem_stabSub.mp h u).mpr hu
  have hτF : ∀ z ∈ fixV L, τ z ∈ fixV L :=
    fun z hz => fixV_apply_mem_of_mem_normalizer (L := L) hτN hz
  have hτZ : ∀ z ∈ Z, τ z ∈ Z := by
    intro z hz
    exact ⟨hτU z hz.1, hτF z hz.2⟩
  have hI₀nat : BinaryNaturalSL L I₀ Z 3 1 := S.I_nat i₀
  have hinf : I₀ ⊓ I₀.map τ.toMonoidHom = Z :=
    s16h_e3_l3_inf_map_eq_of_not_inner hI₀nat hτN hτZ hout
  let φ : W →* W :=
    { toFun := fun w => τ w * w⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  let A : Subgroup W := I₀.map φ
  have hI₀U : I₀ ≤ commSub ⊤ L := by
    rw [show I₀ = S.J i₀ ⊔ (commSub ⊤ L ⊓ fixV L) from (S.J_sup_Z i₀).symm]
    refine sup_le ?_ inf_le_left
    rw [← S.J_iSup]
    exact le_iSup (fun i => S.J i) i₀
  have hA_le : A ≤ commSub (commSub ⊤ L) (Subgroup.zpowers τ) := by
    change I₀.map φ ≤ commSub (commSub ⊤ L) (Subgroup.zpowers τ)
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    show τ u * u⁻¹ ∈ commSub (commSub ⊤ L) (Subgroup.zpowers τ)
    exact Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, u, hI₀U hu, rfl⟩
  have hker_le : I₀ ⊓ φ.ker ≤ Z ⊓ φ.ker := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨?_, hu.2⟩
    have htu : τ u = u := by
      have h1 : φ u = 1 := MonoidHom.mem_ker.mp hu.2
      change τ u * u⁻¹ = 1 at h1
      exact mul_inv_eq_one.mp h1
    have hmem : τ u ∈ I₀ ⊓ I₀.map τ.toMonoidHom :=
      ⟨by rw [htu]; exact hu.1, Subgroup.mem_map_of_mem τ.toMonoidHom hu.1⟩
    rw [hinf] at hmem
    rwa [htu] at hmem
  obtain ⟨z₀, hz₀Z, hz₀ne⟩ := s16h_e3_l3_not_fix_of_not_inner hW S hk hτN hout
  have hz₀ker : z₀ ∉ φ.ker := by
    intro h
    apply hz₀ne
    have h1 : φ z₀ = 1 := MonoidHom.mem_ker.mp h
    change τ z₀ * z₀⁻¹ = 1 at h1
    exact mul_inv_eq_one.mp h1
  have hker_lt : Z ⊓ φ.ker < Z := by
    rw [lt_iff_le_and_ne]
    refine ⟨inf_le_left, fun h => hz₀ker ?_⟩
    have hmem : z₀ ∈ Z ⊓ φ.ker := by rw [h]; exact hz₀Z
    exact (Subgroup.mem_inf.mp hmem).2
  have hker_leZ : I₀ ⊓ φ.ker ≤ Z := hker_le.trans inf_le_left
  have hrk1 : rk ↥(I₀ ⊓ φ.ker) + 1 ≤ rk ↥Z := by
    by_contra h
    have hle : rk ↥Z ≤ rk ↥(I₀ ⊓ φ.ker) := by omega
    have heq : I₀ ⊓ φ.ker = Z := eq_of_le_of_rk_le hW hker_leZ hle
    have hlt : Z < Z := lt_of_le_of_lt (heq ▸ hker_le) hker_lt
    exact lt_irrefl Z hlt
  have hcard := B1More.card_map_mul_card_inf_ker I₀ φ
  have hcard' : Nat.card ↥A * Nat.card ↥(I₀ ⊓ φ.ker) = Nat.card I₀ := hcard
  obtain ⟨D⟩ := BinaryNaturalSL.toL3Coord hI₀nat
  have hI₀card : Nat.card I₀ = 8 * Nat.card Z := D.card_U
  have hrank : rk ↥A + rk ↥(I₀ ⊓ φ.ker) = rk ↥Z + 3 := by
    unfold rk
    rw [← padicValNat.mul (card_subgroup_pos A).ne' (card_subgroup_pos (I₀ ⊓ φ.ker)).ne',
      hcard', hI₀card, show (8 : ℕ) = 2 ^ 3 by norm_num,
      padicValNat.mul (by norm_num) (card_subgroup_pos Z).ne', padicValNat.prime_pow]
    omega
  have hrkA : 4 ≤ rk ↥A := by omega
  exact hrkA.trans (rk_mono hA_le)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
