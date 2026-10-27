module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FW
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5Even7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

section Abstract

theorem index_stab_le_ch615 {X W : Type*} [Group X] [Group W] [Finite W] (ψ : X →* MulAut W)
    {v : W} (hv : v ≠ 1) :
    ((MulAction.stabilizer (MulAut W) v).comap ψ).index ≤ Nat.card W - 1 := by
  classical
  let _ : MulAction X W := MulAction.compHom W ψ
  have hstab : (MulAction.stabilizer (MulAut W) v).comap ψ = MulAction.stabilizer X v := rfl
  rw [hstab, MulAction.index_stabilizer]
  have hsub : MulAction.orbit X v ⊆ {w : W | w ≠ 1} := by
    rintro _ ⟨x, rfl⟩
    show ψ x v ≠ 1
    intro h
    exact hv ((ψ x).injective (h.trans (map_one (ψ x)).symm))
  have hcard1 : {w : W | w ≠ 1}.ncard = Nat.card W - 1 := by
    have h1 : {w : W | w ≠ 1} = Set.univ \ {1} := by
      ext w
      simp
    rw [h1, Set.ncard_sdiff (by simp), Set.ncard_univ, Set.ncard_singleton]
  exact hcard1 ▸ Set.ncard_le_ncard hsub


theorem fix_or_fix_of_alt7_four_ch615 {V : Type} [CommGroup V] [Finite V]
    {F : Subgroup (MulAut V)} (e : ↥F ≃* ↥(alternatingGroup (Fin 7)))
    {W : Subgroup V} (hW : ∀ h : ↥F, ∀ w ∈ W, (h : MulAut V) w ∈ W) (h16 : Nat.card ↥W = 16)
    {S : Subgroup (MulAut V)} (hS : IsSylowTwoOf S F) (htr : ∀ w, (∀ s ∈ S, s w = w) → w ∈ W)
    {R₁ R₂ : Subgroup (MulAut V)} (h1S : S ≤ R₁) (h1F : R₁ ≤ F) (h1ne : R₁ ≠ S)
    (h1s : Group.IsSolvable ↥R₁) (h2S : S ≤ R₂) (h2F : R₂ ≤ F) (h2ne : R₂ ≠ S)
    (h2s : Group.IsSolvable ↥R₂) (hgen : F ≤ R₁ ⊔ R₂) :
    (∀ w, (∀ s ∈ S, s w = w) → ∀ x ∈ R₁, x w = w) ∨
      (∀ w, (∀ s ∈ S, s w = w) → ∀ x ∈ R₂, x w = w) := by
  classical
  have hSF : S ≤ F := hS.1
  obtain ⟨h₀, -, hh₀⟩ := Even7.isSylow_D.exists_conj (isSylowTwoOf_map_ch615 e hS)
  set D' := Even7.D.subgroupOf (alternatingGroup (Fin 7)) with hD'
  set φ : ↥(alternatingGroup (Fin 7)) ≃* ↥F := (MulAut.conj h₀).trans e.symm with hφ
  set img : Subgroup (MulAut V) → Subgroup (Equiv.Perm (Fin 7)) := fun R =>
    ((R.subgroupOf F).map φ.symm.toMonoidHom).map (alternatingGroup (Fin 7)).subtype with himg
  have hmem : ∀ (R : Subgroup (MulAut V)) (y : ↥(alternatingGroup (Fin 7))),
      (y : Equiv.Perm (Fin 7)) ∈ img R ↔ ((φ y : ↥F) : MulAut V) ∈ R := by
    intro R y
    constructor
    · rintro ⟨y', ⟨r, hr, hry⟩, hy'⟩
      have hy : y' = y := Subtype.ext hy'
      subst hy
      have : φ y' = r := by rw [← hry]; exact φ.apply_symm_apply r
      rw [this]
      exact Subgroup.mem_subgroupOf.mp hr
    · intro hy
      exact ⟨y, ⟨φ y, Subgroup.mem_subgroupOf.mpr hy, φ.symm_apply_apply y⟩, rfl⟩
  have himgA : ∀ R, img R ≤ alternatingGroup (Fin 7) := fun R => by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hof : ∀ (R : Subgroup (MulAut V)) (z : Equiv.Perm (Fin 7)), z ∈ img R →
      ∃ y : ↥(alternatingGroup (Fin 7)), (y : Equiv.Perm (Fin 7)) = z ∧
        ((φ y : ↥F) : MulAut V) ∈ R := by
    intro R z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, rfl, (hmem R y).mp ⟨y, hy, rfl⟩⟩
  have hle_iff : ∀ R R' : Subgroup (MulAut V), R ≤ F → (img R ≤ img R' ↔ R ≤ R') := by
    intro R R' hRF
    constructor
    · intro h x hx
      have h1 := (hmem R (φ.symm ⟨x, hRF hx⟩)).mpr (by rw [φ.apply_symm_apply]; exact hx)
      have h2 := (hmem R' _).mp (h h1)
      rwa [φ.apply_symm_apply] at h2
    · intro h z hz
      obtain ⟨y, rfl, hy⟩ := hof R z hz
      exact (hmem R' y).mpr (h hy)
  have hSD : ∀ y : ↥(alternatingGroup (Fin 7)),
      ((φ y : ↥F) : MulAut V) ∈ S ↔ (y : Equiv.Perm (Fin 7)) ∈ Even7.D := by
    intro y
    constructor
    · intro hy
      have h1 : e (φ y) ∈ (S.subgroupOf F).map e.toMonoidHom :=
        ⟨φ y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      rw [hh₀] at h1
      obtain ⟨t, ht, hte⟩ := h1
      have h2 : e (φ y) = MulAut.conj h₀ y := by simp [hφ]
      have h3 : y = t := by
        rw [h2] at hte
        exact (MulAut.conj h₀).injective hte.symm
      rw [h3]
      exact Subgroup.mem_subgroupOf.mp ht
    · intro hy
      have h1 : MulAut.conj h₀ y ∈ (S.subgroupOf F).map e.toMonoidHom := by
        rw [hh₀]
        exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      obtain ⟨s, hs, hse⟩ := h1
      have h2 : φ y = s := by
        simp only [hφ, MulEquiv.trans_apply]
        rw [← hse]
        exact e.symm_apply_apply s
      rw [h2]
      exact Subgroup.mem_subgroupOf.mp hs
  have hDimg : ∀ R, S ≤ R → Even7.D ≤ img R := fun R hSR d hd =>
    (hmem R ⟨d, Even7.D_le hd⟩).mpr (hSR ((hSD ⟨d, Even7.D_le hd⟩).mpr hd))
  have himgS : img S = Even7.D := by
    refine le_antisymm (fun z hz => ?_) (hDimg S le_rfl)
    obtain ⟨y, rfl, hy⟩ := hof S z hz
    exact (hSD y).mp hy
  have hcard : ∀ R : Subgroup (MulAut V), R ≤ F → Nat.card ↥(img R) = Nat.card ↥R :=
    fun R hRF => by
      rw [himg, Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective,
        Subgroup.card_map_of_injective φ.symm.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv]
  have hsolv : ∀ R : Subgroup (MulAut V), R ≤ F → Group.IsSolvable ↥R →
      Group.IsSolvable ↥(img R) := fun R hRF hR => by
    have := isSolvable_map_ch615 φ.symm hRF hR
    exact Group.isSolvable_of_surjective
      ((alternatingGroup (Fin 7)).subtype.subgroupMap_surjective _)
  have hne : ∀ R : Subgroup (MulAut V), S ≤ R → R ≤ F → R ≠ S → img R ≠ Even7.D := by
    intro R hSR hRF hRS h
    apply hRS
    refine le_antisymm ((hle_iff R S hRF).mp ?_) hSR
    rw [h, himgS]
  have hgen' : alternatingGroup (Fin 7) ≤ img R₁ ⊔ img R₂ := by
    have hsup : img (R₁ ⊔ R₂) = img R₁ ⊔ img R₂ := by
      simp only [himg]
      rw [Subgroup.subgroupOf_sup h1F h2F, Subgroup.map_sup, Subgroup.map_sup]
    rw [← hsup]
    intro z hz
    exact (hmem _ ⟨z, hz⟩).mpr (hgen (φ ⟨z, hz⟩).2)
  have h5 := Even7.eq_five_of_gen_ch615 (hDimg R₁ h1S) (himgA R₁) (hne R₁ h1S h1F h1ne)
    (hsolv R₁ h1F h1s) (hDimg R₂ h2S) (himgA R₂) (hne R₂ h2S h2F h2ne) (hsolv R₂ h2F h2s) hgen'
  set ψ : ↥F →* MulAut ↥W := resAct_ch615 F W hW with hψ
  have hcardF : Nat.card ↥F = 2520 := by rw [Nat.card_congr e.toEquiv, Even7.card_alt]
  have hfixR : ∀ R : Subgroup (MulAut V), R ≤ F → img R = Even7.Lm 5 →
      ∀ w, (∀ s ∈ S, s w = w) → ∀ x ∈ R, x w = w := by
    intro R hRF hR w hw x hx
    by_cases hw1 : w = 1
    · rw [hw1, map_one]
    have hwW := htr w hw
    have hv1 : (⟨w, hwW⟩ : ↥W) ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
    set St := (MulAction.stabilizer (MulAut ↥W) (⟨w, hwW⟩ : ↥W)).comap ψ with hSt
    set P := St.map F.subtype with hP
    have hPmem : ∀ y : MulAut V, y ∈ P ↔ y ∈ F ∧ y w = w := by
      intro y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨y'.2, congrArg Subtype.val (hy' : ψ y' ⟨w, hwW⟩ = ⟨w, hwW⟩)⟩
      · rintro ⟨hyF, hyw⟩
        exact ⟨⟨y, hyF⟩, (Subtype.ext hyw : ψ ⟨y, hyF⟩ ⟨w, hwW⟩ = ⟨w, hwW⟩), rfl⟩
    have hPF : P ≤ F := fun y hy => ((hPmem y).mp hy).1
    have hSP : S ≤ P := fun s hs => (hPmem s).mpr ⟨hSF hs, hw s hs⟩
    have hidx := index_stab_le_ch615 ψ hv1
    rw [← hSt, h16] at hidx
    have hmul := Subgroup.card_mul_index St
    rw [hcardF] at hmul
    have hPcard : Nat.card ↥P = Nat.card ↥St :=
      Subgroup.card_map_of_injective F.subtype_injective
    have h168 : 168 ≤ Nat.card ↥(img P) := by
      rw [hcard P hPF, hPcard]
      by_contra hlt
      have : Nat.card ↥St * St.index ≤ 167 * 15 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have h5P := Even7.five_le_of_card_ch615 (hDimg P hSP) (himgA P) h168
    rw [← hR] at h5P
    exact ((hPmem x).mp ((hle_iff R P hRF).mp h5P hx)).2
  rcases h5 with h | h
  · exact Or.inl (hfixR R₁ h1F h)
  · exact Or.inr (hfixR R₂ h2F h)

end Abstract

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_two_overgroups_gen_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    {F : Subgroup (MulAut (IntMod (UX615 T L H) hU))} (hFX : F ≤ autI hU (borelL T L ⊔ H))
    (hXF : autI hU (borelL T L ⊔ H) ≤ Subgroup.normalizer (F : Set (MulAut _)))
    (hdl : DLemmaFacts_ch615 F) (hZ : ∀ g ∈ F, (∀ x ∈ F, g * x = x * g) → g = 1)
    (hKF : autI hU (oTwoUpper H) ≤ F)
    (hpar : ∀ R₁ R₂ : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      autI hU T ⊓ F ≤ R₁ → R₁ ≤ F → R₁ ≠ autI hU T ⊓ F → Group.IsSolvable ↥R₁ →
      autI hU T ⊓ F ≤ R₂ → R₂ ≤ F → R₂ ≠ autI hU T ⊓ F → Group.IsSolvable ↥R₂ → R₁ ≠ R₂ →
      F ≤ R₁ ⊔ R₂ →
      (∀ w, (∀ s ∈ autI hU T ⊓ F, s w = w) → ∀ x ∈ R₁, x w = w) ∨
      (∀ w, (∀ s ∈ autI hU T ⊓ F, s w = w) → ∀ x ∈ R₂, x w = w)) : False := by
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  obtain ⟨d, hdD, hd1, hdPD, hSD, hDS, hDs, hKF', hKS, hKs, hne⟩ :=
    c.exists_overgroups_ch615 hU hN hD hFX hXF hdl hZ hKF
  have hgen := c.le_sup_overgroups_ch615 hU hFX hXF hdl hZ hKF
  rcases hpar _ _ le_sup_right hKF' hKS hKs hSD inf_le_right hDS hDs hne hgen with h | h
  · exact c.not_fix_oTwoUpper_ch615 hU fun w hw k hk =>
      h w (fun s hs => hw s hs.1) k (Subgroup.mem_sup_left hk)
  · exact c.not_fix_hall_ch615 hU hD hdD hd1 fun w hw => h w (fun s hs => hw s hs.1) d hdPD


theorem false_of_case1_alt_seven_four_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))))
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃* ↥(alternatingGroup (Fin 7)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥)
    (h4 : A7Four (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))
      (commV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))) ⊥) : False := by
  have hs : IsSimpleGroup ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hdl := dLemmaFacts_of_smallAlt_ch615 hs
    (CFSG.Quasithin.InternalSec.exists_noncomm_of_isQuasisimple hq) (Or.inl ⟨7, by norm_num, ⟨e⟩⟩)
  have hS := c.isSylowTwoOf_genFitting_ch615 hU
  obtain ⟨α, π, hπ⟩ := h4
  have h16 : Nat.card ↥(commV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))))) = 16 := by
    have h2 := G64.RealizesVia.card_eq hπ
    rw [Subgroup.card_bot, mul_one] at h2
    rw [h2]
    show Nat.card (↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) ⧸
      (⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))).subgroupOf ⊤) = 16
    rw [Subgroup.bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot).toEquiv,
      Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
    norm_num
  refine c.false_of_two_overgroups_gen_ch615 hU hN
    ((quasithinGenFitting_le _).trans (B6.ffJ_le _)) (le_normalizer_genFitting_ch615 hU) hdl
    (center_of_isSimpleGroup_ch615 hs hdl.1) (c.autI_oTwoUpper_le_genFitting_ch615 hU hdl.2.1)
    fun R₁ R₂ h1S h1F h1ne h1s h2S h2F h2ne h2s _ hgen =>
      fix_or_fix_of_alt7_four_ch615 e hπ.2.2.2.1 h16 hS (fun w hw => by
          have := mem_commV_sup_fixV_ch615 IntMod.sq_eq_one hS.2.2 hw
          rwa [hfix, sup_bot_eq] at this)
        h1S h1F h1ne h1s h2S h2F h2ne h2s hgen

end Cx615C

end CFSG.Quasithin.H13
