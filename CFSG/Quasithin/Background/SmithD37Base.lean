module

public import CFSG.Quasithin.Background.SmithD37Fix
public import CFSG.Quasithin.Background.SmithD37Core
public import CFSG.Quasithin.Background.F918J2
public import CFSG.Quasithin.Background.F918M5
public import CFSG.Quasithin.Background.B1MoreTwelve

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.Open

section Conj

variable {W : Type} [CommGroup W]

private theorem conj_mul_b (a b : MulAut W) (X : Subgroup (MulAut W)) :
    conjAutSub (a * b) X = conjAutSub a (conjAutSub b X) := by
  ext x
  simp only [mem_conjAutSub_iff]
  have : (a * b)⁻¹ * x * (a * b) = b⁻¹ * (a⁻¹ * x * a) * b := by group
  rw [this]

private theorem conj_one_b (X : Subgroup (MulAut W)) : conjAutSub 1 X = X := by
  ext x
  simp [mem_conjAutSub_iff]

private def pairStab (A B : Subgroup (MulAut W)) : Subgroup (MulAut W) where
  carrier := {g | (conjAutSub g A = A ∧ conjAutSub g B = B) ∨
    (conjAutSub g A = B ∧ conjAutSub g B = A)}
  one_mem' := Or.inl ⟨conj_one_b A, conj_one_b B⟩
  mul_mem' := by
    rintro a b (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩) (⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩) <;>
      simp only [Set.mem_ofPred_eq, conj_mul_b, ha₁, ha₂, hb₁, hb₂, and_self, true_or, or_true]
  inv_mem' := by
    rintro a (⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩)
    · have h₁ := conjAutSub_inv_conjAutSub A a
      have h₂ := conjAutSub_inv_conjAutSub B a
      rw [ha₁] at h₁
      rw [ha₂] at h₂
      exact Or.inl ⟨h₁, h₂⟩
    · have h₁ := conjAutSub_inv_conjAutSub A a
      have h₂ := conjAutSub_inv_conjAutSub B a
      rw [ha₁] at h₁
      rw [ha₂] at h₂
      exact Or.inr ⟨h₂, h₁⟩

private theorem mem_pairStab {A B : Subgroup (MulAut W)} {g : MulAut W} :
    g ∈ pairStab A B ↔ (conjAutSub g A = A ∧ conjAutSub g B = B) ∨
      (conjAutSub g A = B ∧ conjAutSub g B = A) := Iff.rfl

private theorem le_pairStab {Mp T L : Subgroup (MulAut W)} {t : MulAut W} (htT : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L)
    (hc : ⁅L, conjAutSub t L⁆ = ⊥)
    (hT : ∀ s ∈ T, conjAutSub s L = L ∨ conjAutSub s L = conjAutSub t L) :
    Mp ⊔ T ≤ pairStab L (conjAutSub t L) := by
  have hne : conjAutSub t L ≠ L := fun h =>
    htn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hcL : L ≤ Subgroup.centralizer (conjAutSub t L : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hcL' : conjAutSub t L ≤ Subgroup.centralizer (L : Set (MulAut W)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hc)
  rw [hMp]
  refine sup_le (sup_le (fun l hl => ?_) (fun y hy => ?_)) (fun s hs => ?_)
  · exact Or.inl ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ (hcL hl))⟩
  · exact Or.inl ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ (hcL' hy)),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hy)⟩
  · have h₂ : conjAutSub s (conjAutSub t L) = conjAutSub (s * t) L := (conj_mul_b s t L).symm
    have hinj : ∀ X Y : Subgroup (MulAut W), conjAutSub s X = conjAutSub s Y → X = Y :=
      fun X Y h => by rw [← conjAutSub_inv_conjAutSub X s, h, conjAutSub_inv_conjAutSub]
    rcases hT s hs with h₁ | h₁ <;> rcases hT (s * t) (T.mul_mem hs htT) with h₃ | h₃
    · exact absurd (hinj _ _ (h₂.trans (h₃.trans h₁.symm))) hne
    · exact Or.inl ⟨h₁, h₂.trans h₃⟩
    · exact Or.inr ⟨h₁, h₂.trans h₃⟩
    · exact absurd (hinj _ _ (h₂.trans (h₃.trans h₁.symm))) hne

end Conj

section Restrict

variable {W : Type} [CommGroup W]

private theorem autSub_sup_b {A B : Subgroup (MulAut W)} {U : Subgroup W} (hA : A ≤ stabSub U)
    (hB : B ≤ stabSub U) : autSub (A ⊔ B) U = autSub A U ⊔ autSub B U := by
  unfold autSub
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

private theorem irr_autSub_b {H : Subgroup (MulAut W)} {V : Subgroup W} (hH : H ≤ stabSub V)
    (hirr : ∀ J : Subgroup W, (∀ x ∈ H, ∀ w ∈ J, x w ∈ J) → V ⊓ fixV H ≤ J → J ≤ V →
      J = V ⊓ fixV H ∨ J = V) :
    ∀ J : Subgroup ↥V, IsInvBy (autSub H V) J → fixV (autSub H V) ≤ J →
      J = fixV (autSub H V) ∨ J = ⊤ := by
  intro J hJ hCJ
  have hinv : ∀ x ∈ H, ∀ w ∈ J.map V.subtype, x w ∈ J.map V.subtype := by
    rintro x hx _ ⟨w, hw, rfl⟩
    exact ⟨resHom V ⟨x, hH hx⟩ w, hJ _ (mem_autSub.mpr ⟨⟨x, hH hx⟩, hx, rfl⟩) w hw, rfl⟩
  have hfix : V ⊓ fixV H ≤ J.map V.subtype := by
    rw [← map_subtype_fixV_autSub hH]
    exact Subgroup.map_mono hCJ
  rcases hirr _ hinv hfix (Subgroup.map_subtype_le J) with h | h
  · left
    apply Subgroup.map_injective V.subtype_injective
    rw [h, map_subtype_fixV_autSub hH]
  · right
    apply Subgroup.map_injective V.subtype_injective
    rw [h, ← MonoidHom.range_eq_map, V.range_subtype]

omit [CommGroup W] in
private theorem center_eq_bot_b {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hq : CFSG.IsQuasisimple Q) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hq
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp ha b).symm]

omit [CommGroup W] in
private theorem exists_disp_not_mem_b {U : Type*} [CommGroup U] {K : Subgroup (MulAut U)}
    [Group.IsPerfect ↥K] [Nontrivial ↥K] {C : Subgroup U} (hC : C ≤ fixV K) :
    ∃ l ∈ K, ∃ u, disp l u ∉ C := by
  by_contra hcon
  push Not at hcon
  have htriv := trivial_of_perfect hC fun l hl u => by rw [← disp_apply]; exact hcon l hl u
  obtain ⟨⟨k, hk⟩, hk1⟩ := exists_ne (1 : ↥K)
  apply hk1
  apply Subtype.ext
  ext u
  exact htriv k hk u

end Restrict

section Faithful

variable {W : Type} [CommGroup W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

private theorem faithful_b [IsSimpleGroup ↥L] (hD : D31 M Mp T L V) (htV : t ∈ stabSub V)
    (hMp : Mp = L ⊔ conjAutSub t L) :
    Function.Injective (resHomOn V (insp5a_le_stabSub hD)) := by
  have hLs := insp5a_le_stabSub hD
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (resHomOn V hLs).ker with hk | hk
  · exact hk
  · exfalso
    have hL : L ≤ centSub V := by
      intro l hl u hu
      have hmem : (⟨l, hl⟩ : ↥L) ∈ (resHomOn V hLs).ker := by rw [hk]; trivial
      rw [MonoidHom.mem_ker] at hmem
      exact congrArg (fun φ : MulAut ↥V => ((φ ⟨u, hu⟩ : ↥V) : W)) hmem
    have hLt : conjAutSub t L ≤ centSub V := by
      rintro _ ⟨l, hl, rfl⟩ u hu
      have hu' : t⁻¹ u ∈ V := (((stabSub V).inv_mem htV) u).2 hu
      have h1 : ((MulAut.conj t).toMonoidHom l) u = t (l (t⁻¹ u)) := rfl
      rw [h1, hL hl _ hu']
      simp
    have hMpc : Mp ≤ centSub V := hMp ▸ sup_le hL hLt
    obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.mp hD.irr
    exact hlt.not_ge fun v hv => ⟨hv, fun x hx => hMpc hx v hv⟩

private theorem equiv_b [IsSimpleGroup ↥L] (hD : D31 M Mp T L V) (htV : t ∈ stabSub V)
    (hMp : Mp = L ⊔ conjAutSub t L) : Nonempty (↥L ≃* ↥(autSub L V)) :=
  ⟨(MonoidHom.ofInjective (faithful_b hD htV hMp)).trans
    (MulEquiv.subgroupCongr (autSub_eq_range_resHomOn (insp5a_le_stabSub hD)).symm)⟩

end Faithful

theorem core_of_d3Std (hL38 : D3L38) (hA21 : AsA21SQTKSection)
    {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (std : D3Std M Mp T L V) (hVT : V = orbSup T V) {t : MulAut W} (htT : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W))) (hMp : Mp = L ⊔ conjAutSub t L) :
    ∃ htV : t ∈ stabSub V,
      Core (autSub (Mp ⊔ T) V) (autSub L V) (autSub (conjAutSub t L) V) (resHom V ⟨t, htV⟩) ∧
        autSub Mp V = autSub L V ⊔ autSub (conjAutSub t L) V := by
  obtain ⟨hA38, hc, -, hTL⟩ := hL38 W M Mp T L V std t htT htn hMp
  have hD := std.hyp
  have htV : t ∈ stabSub V := stab_of_orbSup_eq hVT.symm t htT
  have hMpV : Mp ≤ stabSub V := insp5a_sec_Mp_le_stabSub hD
  have hLV : L ≤ stabSub V := insp5a_le_stabSub hD
  have hLMp : L ≤ Mp := insp5a_sec_L_le_Mp hD
  have hLtMp : conjAutSub t L ≤ Mp := hMp ▸ le_sup_right
  have hLtV : conjAutSub t L ≤ stabSub V := hLtMp.trans hMpV
  have hsup : autSub Mp V = autSub L V ⊔ autSub (conjAutSub t L) V := by
    rw [hMp]
    exact autSub_sup_b hLV hLtV
  refine ⟨htV, ?_, hsup⟩
  obtain ⟨-, hcommV, hlt, hirrV⟩ := mem_irrPlus_top_iff.mp hD.irr
  have : IsSimpleGroup ↥L := insp5a_sec_isSimpleGroup hA38
  obtain ⟨e⟩ := equiv_b hD htV hMp
  have : IsSimpleGroup ↥(autSub L V) := e.symm.isSimpleGroup
  have hLq : CFSG.IsQuasisimple ↥L := insp5a_sec_isQuasisimple hD hA38
  have hq₁ : CFSG.IsQuasisimple ↥(autSub L V) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hLq
  have hpair := le_pairStab htT htn hMp hc hTL
  have hswap₁ : (autSub L V).map (MulAut.conj (resHom V ⟨t, htV⟩)).toMonoidHom =
      autSub (conjAutSub t L) V := (B1Red.autSub_map_conj hLV htV).symm
  have htt : conjAutSub t (conjAutSub t L) = L := by
    rcases mem_pairStab.mp (hpair (Subgroup.mem_sup_right htT)) with h | h
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.1) htn
    · exact h.2
  have hswap₂ : (autSub (conjAutSub t L) V).map (MulAut.conj (resHom V ⟨t, htV⟩)).toMonoidHom =
      autSub L V := (B1Red.autSub_map_conj hLtV htV).symm.trans (congrArg (autSub · V) htt)
  have hq₂ : CFSG.IsQuasisimple ↥(autSub (conjAutSub t L) V) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (((autSub L V).equivMapOfInjective
      (MulAut.conj (resHom V ⟨t, htV⟩)).toMonoidHom (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hswap₁)) hq₁
  have hcomm : ∀ x ∈ autSub L V, ∀ y ∈ autSub (conjAutSub t L) V, x * y = y * x := by
    intro x hx y hy
    obtain ⟨⟨a, has⟩, ha, rfl⟩ := mem_autSub.mp hx
    obtain ⟨⟨b, hbs⟩, hb, rfl⟩ := mem_autSub.mp hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc ha) b hb).symm
  have hinf : autSub L V ⊓ autSub (conjAutSub t L) V = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx₁, hx₂⟩
    have hZ : (⟨x, hx₁⟩ : ↥(autSub L V)) ∈ Subgroup.center ↥(autSub L V) :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hcomm y y.2 x hx₂)
    rw [center_eq_bot_b hq₁, Subgroup.mem_bot] at hZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hZ)
  have hperm : ∀ x ∈ autSub (Mp ⊔ T) V,
      ((autSub L V).map (MulAut.conj x).toMonoidHom = autSub L V ∧
        (autSub (conjAutSub t L) V).map (MulAut.conj x).toMonoidHom =
          autSub (conjAutSub t L) V) ∨
      ((autSub L V).map (MulAut.conj x).toMonoidHom = autSub (conjAutSub t L) V ∧
        (autSub (conjAutSub t L) V).map (MulAut.conj x).toMonoidHom = autSub L V) := by
    intro x hx
    obtain ⟨⟨g, hgs⟩, hg, rfl⟩ := mem_autSub.mp hx
    rw [← B1Red.autSub_map_conj hLV hgs, ← B1Red.autSub_map_conj hLtV hgs]
    rcases mem_pairStab.mp (hpair hg) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Or.inl ⟨congrArg (autSub · V) h₁, congrArg (autSub · V) h₂⟩
    · exact Or.inr ⟨congrArg (autSub · V) h₁, congrArg (autSub · V) h₂⟩
  have htwo : ∀ x ∈ autSub (Mp ⊔ T) V, ∃ e : ℕ,
      x ^ 2 ^ e ∈ autSub L V ⊔ autSub (conjAutSub t L) V := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hx
    have hg' : (g : MulAut W) ∈ ((Mp ⊔ T : Subgroup (MulAut W)) : Set (MulAut W)) := hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Mp T (insp5a_sec_T_le_normalizer hD)] at hg'
    obtain ⟨m, hm, s, hs, hms⟩ := hg'
    obtain ⟨k, hk⟩ := (hD.sylow.2.1 : IsPGroup 2 ↥T) ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨m', hm', hpow⟩ :=
      insp5a_sec_mul_pow_mem hm (insp5a_sec_T_le_normalizer hD hs) (2 ^ k)
    refine ⟨k, ?_⟩
    rw [← hsup, ← map_pow]
    refine mem_autSub.mpr ⟨g ^ 2 ^ k, ?_, rfl⟩
    rw [Subgroup.coe_pow, ← hms, hpow, hk', mul_one]
    exact hm'
  have hirr' := irr_autSub_b hMpV hirrV
  rw [hsup] at hirr'
  have : Group.IsPerfect ↥(autSub L V) := hq₁.1
  have : Nontrivial ↥(autSub L V) := CFSG.LocalCores.isQuasisimple_nontrivial hq₁
  have : Group.IsPerfect ↥(autSub (conjAutSub t L) V) := hq₂.1
  have : Nontrivial ↥(autSub (conjAutSub t L) V) := CFSG.LocalCores.isQuasisimple_nontrivial hq₂
  have hC : fixV (autSub L V ⊔ autSub (conjAutSub t L) V) = ⊥ := by
    refine fixV_sup_eq_bot hcomm hirr' ?_ ?_ ?_
    · rw [← hsup]
      exact insp5a_sec_comm hMpV hcommV
    · exact exists_disp_not_mem_b fun u hu x hx => hu x (le_sup_left (a := autSub L V) hx)
    · exact exists_disp_not_mem_b fun u hu x hx => hu x (le_sup_right (a := autSub L V) hx)
  have ho2 : pCoreOf 2 (autSub (Mp ⊔ T) V) = ⊥ := by
    have h := hD.pCoreOf_autSub_orbSup_eq_bot
    rwa [← hVT] at h
  have hq : qhatOf (autSub (Mp ⊔ T) V) ≤ ((2 : ℚ) : WithTop ℚ) := by
    have h := std.qhat
    rwa [← hVT] at h
  have hsqtk : SQTKGroup ↥(autSub L V) := by
    obtain ⟨S, _, _, hSQT, hK, φ, hφ⟩ := hD.qsqtk
    have hS : SQTKGroup S := ⟨fun p hp hp2 => hSQT p hp hp2, hK⟩
    exact B69.sqtk_autSub hA21 hLV
      (B69.sqtk_subgroup hA21 hS φ hφ (le_of_mem_cComp hD.comp) hLq) hq₁
  exact
    { exp := fun u => Subtype.ext (by simp [hD.exp])
      nt := (Subgroup.nontrivial_iff_ne_bot V).mpr fun h => by
        rw [h, bot_inf_eq] at hlt
        exact lt_irrefl _ hlt
      a38 := a38Types_congr e hA38
      simple := inferInstance
      sqtk := hsqtk
      comm := hcomm
      inf := hinf
      le₁ := autSub_mono (hLMp.trans le_sup_left) V
      le₂ := autSub_mono (hLtMp.trans le_sup_left) V
      mem := mem_autSub.mpr ⟨⟨t, htV⟩, Subgroup.mem_sup_right htT, rfl⟩
      swap₁ := hswap₁
      swap₂ := hswap₂
      perm := hperm
      two := htwo
      o2 := ho2
      irr := fun J hJ => by
        have h := hirr' J hJ (by rw [hC]; exact bot_le)
        rwa [hC] at h
      qhat := hq }

end CFSG.Quasithin.SmithD37
