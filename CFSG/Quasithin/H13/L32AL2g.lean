module

public import CFSG.Quasithin.H13.L32AL2f
public import CFSG.Quasithin.H13.L32AM50b

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative Pointwise

section General

variable {W' : Type} [CommGroup W'] [Finite W']

theorem exists_mem_irrPlus {X : Subgroup (MulAut W')} (hfix : fixV X = ⊥)
    (hne : (⊤ : Subgroup W') ≠ ⊥) : ∃ I : Subgroup W', I ∈ IrrPlus X (⊤ : Subgroup W') := by
  classical
  set 𝒮 : Set (Subgroup W') := {J | J ≠ ⊥ ∧ IsModInv X J} with h𝒮
  obtain ⟨J, hJ⟩ := 𝒮.toFinite.exists_minimal ⟨⊤, hne, XMod.isInv_top⟩
  have hJfix : ∀ J' : Subgroup W', J' ≤ XMod.fixed ↥X ⊤ → J' = ⊥ := by
    intro J' hJ'
    rw [eq_bot_iff, ← hfix]
    intro w hw y hy
    exact (hJ' hw).2 ⟨y, hy⟩
  refine ⟨J, le_top, hJ.1.2, ?_, ?_⟩
  · refine le_antisymm (XMod.commOf_le_of_isInv hJ.1.2)
      (hJ.2 ⟨fun h => hJ.1.1 ?_, XMod.isInv_commOf _⟩ (XMod.commOf_le_of_isInv hJ.1.2))
    exact hJfix J (XMod.commOf_eq_bot_iff.mp h)
  · have hfJ : XMod.fixed ↥X J = ⊥ := hJfix _ (XMod.fixed_mono le_top)
    rw [hfJ]
    refine ⟨bot_lt_iff_ne_bot.mpr hJ.1.1, fun J' hJ'inv _ hJ'J => ?_⟩
    by_cases h : J' = ⊥
    · exact Or.inl h
    · exact Or.inr (le_antisymm hJ'J (hJ.2 ⟨h, hJ'inv⟩ hJ'J))

theorem alt5_noncomm : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide +kernel⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by decide +kernel⟩, fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide +kernel

end General

variable {G : Type} [Group G] [Finite G] {T L V K W : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K W t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

@[expose] noncomputable def img (A : Subgroup G) : Subgroup (MulAut (Hat V (A6.g1 T V) W)) :=
  (A.subgroupOf (A6.g1 T V)).map X.top.act

theorem img_eq_map (A : Subgroup G) : X.img A = (modO2Image (A6.g1 T V) A).map X.actDot := by
  rw [img, modO2Image, Subgroup.map_map]
  rfl

theorem img_g1 : X.img (A6.g1 T V) = X.top.act.range := map_subgroupOf_self_eq_range _

theorem img_K₀_sup_T : X.img (conjClosure K T) ⊔ X.img T = X.img (A6.g1 T V) := by
  have hK₀H : conjClosure K T ≤ A6.g1 T V := by rw [X.R.hG1]; exact le_sup_left
  have hTH : T ≤ A6.g1 T V := by rw [X.R.hG1]; exact le_sup_right
  rw [img, img, img, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hK₀H hTH, ← X.R.hG1]

omit [IsMulCommutative ↥(conjClosure V (A6.g1 T V))] in
include X in
theorem le_normalizer_K₀ : A6.g1 T V ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  rw [X.R.hG1]
  exact sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T)

theorem img_g1_le_normalizer :
    X.img (A6.g1 T V) ≤ Subgroup.normalizer (X.img (conjClosure K T) :
      Set (MulAut (Hat V (A6.g1 T V) W))) := by
  have hK₀H : conjClosure K T ≤ A6.g1 T V := by rw [X.R.hG1]; exact le_sup_left
  exact map_le_normalizer_map_of_le_normalizer X.top.act hK₀H X.le_normalizer_K₀

theorem eq_top_of_inv {J : Subgroup (Hat V (A6.g1 T V) W)} (hJ : J ≠ ⊥)
    (h1 : ∀ m ∈ X.img (conjClosure K T), ∀ w ∈ J, m w ∈ J)
    (h2 : ∀ m ∈ X.img T, ∀ w ∈ J, m w ∈ J) : J = ⊤ := by
  have hstab : ∀ Y : Subgroup (MulAut (Hat V (A6.g1 T V) W)),
      (∀ m ∈ Y, ∀ w ∈ J, m w ∈ J) → Y ≤ stabSub J := by
    intro Y hY m hm u
    constructor
    · intro hu
      have := hY m⁻¹ (inv_mem hm) _ hu
      simpa using this
    · intro hu
      exact hY m hm u hu
  have hM : X.img (A6.g1 T V) ≤ stabSub J := by
    rw [← X.img_K₀_sup_T]
    exact sup_le (hstab _ h1) (hstab _ h2)
  rcases X.top.irr J (fun h w hw =>
      ((hM ⟨h, Subgroup.mem_subgroupOf.mpr h.2, rfl⟩) w).mpr hw) with h | h
  · exact absurd h hJ
  · exact h

theorem fixV_img_K₀ (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : fixV (X.img (conjClosure K T)) = ⊥ := by
  set F := fixV (X.img (conjClosure K T)) with hF
  have hinv : ∀ h : ↥(A6.g1 T V), ∀ w ∈ F, X.top.act h w ∈ F := by
    intro h w hw y hy
    have hn := X.img_g1_le_normalizer ⟨h, Subgroup.mem_subgroupOf.mpr h.2, rfl⟩
    have hy' : (X.top.act h)⁻¹ * y * X.top.act h ∈ X.img (conjClosure K T) := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) y).mp hy
      simpa using this
    have := hw _ hy'
    simp only [MulAut.mul_apply] at this
    have h2 := congrArg (X.top.act h) this
    simpa using h2
  rcases X.top.irr F hinv with h | h
  · exact h
  · exfalso
    refine X.not_kb_le_ker hA37 h1222 h1332 h1334 fun a ha => ?_
    obtain ⟨κ, hκ, rfl⟩ := mem_modO2Image'.mp ha
    rw [MonoidHom.mem_ker, actDot_mk]
    apply MulEquiv.ext
    intro w
    have hw : w ∈ F := by rw [h]; exact Subgroup.mem_top w
    exact hw _ ⟨κ, Subgroup.mem_subgroupOf.mpr (le_conjClosure K T hκ), rfl⟩

theorem img_K_ne_bot (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : X.img K ≠ ⊥ := by
  intro h
  refine X.not_kb_le_ker hA37 h1222 h1332 h1334 fun a ha => ?_
  obtain ⟨κ, hκ, rfl⟩ := mem_modO2Image'.mp ha
  rw [MonoidHom.mem_ker, actDot_mk]
  have : X.top.act κ ∈ X.img K := ⟨κ, Subgroup.mem_subgroupOf.mpr hκ, rfl⟩
  rw [h, Subgroup.mem_bot] at this
  exact this

theorem nonempty_equiv_img_K (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    Nonempty (↥(X.img K) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e₁⟩ := X.R.hA5
  obtain ⟨e₂⟩ := X.C.nonempty_equiv
  have hinj := X.actDot_injective hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  exact ⟨(MulEquiv.subgroupCongr (X.img_eq_map K)).trans
    ((Subgroup.equivMapOfInjective _ _ hinj).symm.trans (e₂.symm.trans e₁))⟩

theorem isQuasisimple_img_K (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) : CFSG.IsQuasisimple ↥(X.img K) := by
  obtain ⟨φ⟩ := X.nonempty_equiv_img_K hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥(X.img K) := (MulEquiv.isSimpleGroup_congr φ).mpr hs
  obtain ⟨a, b, hab⟩ := alt5_noncomm
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ⟨φ.symm a, φ.symm b, fun h => hab ?_⟩).1
  have := congrArg φ h
  simpa using this

theorem img_T_le : X.img T ≤ X.img (A6.g1 T V) :=
  Subgroup.map_mono (by rw [Subgroup.subgroupOf_self]; exact le_top)

theorem img_K₀_le : X.img (conjClosure K T) ≤ X.img (A6.g1 T V) :=
  Subgroup.map_mono (by rw [Subgroup.subgroupOf_self]; exact le_top)

theorem isSylowTwoOf_img_T : IsSylowTwoOf (X.img T) (X.img (A6.g1 T V)) := by
  have hTH : T ≤ A6.g1 T V := by rw [X.R.hG1]; exact le_sup_right
  exact isSylowTwoOf_map_subgroupOf X.top.act
    (isSylowTwoOf_of_quasithinIsSylowTwo X.R.S.hyp.fsu.sylow hTH)

theorem d31 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {V' : Subgroup (Hat V (A6.g1 T V) W)}
    (hV' : V' ∈ IrrPlus (X.img (conjClosure K T)) ⊤) :
    D31 (X.img (A6.g1 T V)) (X.img (conjClosure K T)) (X.img T) (X.img K) V' := by
  have hTH : T ≤ A6.g1 T V := by rw [X.R.hG1]; exact le_sup_right
  have hKH : K ≤ A6.g1 T V := le_of_mem_cComp X.R.hK
  have hK₀H : conjClosure K T ≤ A6.g1 T V := by rw [X.R.hG1]; exact le_sup_left
  have hV'ne : V' ≠ ⊥ := (bot_le.trans_lt hV'.2.2.2.1).ne'
  refine ⟨fun w => by rw [pow_two]; exact X.top.sec_sq w, ?_, X.isSylowTwoOf_img_T,
    map_subgroupOf_mem_cComp X.top.act X.R.hK (X.img_K_ne_bot hA37 h1222 h1332 h1334),
    X.isQuasisimple_img_K hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334,
    map_subgroupOf_conjClosure X.top.act hKH hTH,
    map_le_normalizer_map_of_le_normalizer X.top.act hK₀H X.le_normalizer_K₀,
    ⟨le_top, hV'.2⟩, ?_, ?_⟩
  · rw [X.img_g1]
    exact isQuotientOfSQTK_range _ (sqtkGroup_of_setting X.top.S)
  · intro g hg v hv
    rw [X.img_K₀_sup_T, X.img_g1,
      X.pCoreOf_range_eq_bot hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334,
      Subgroup.mem_bot] at hg
    rw [hg]
    exact hv
  · set J := ⨆ m ∈ X.img (A6.g1 T V), V'.map (m : MulAut (Hat V (A6.g1 T V) W)).toMonoidHom
      with hJ
    have hinv : ∀ n ∈ X.img (A6.g1 T V), ∀ w ∈ J, n w ∈ J := by
      intro n hn w hw
      have hle : J.map n.toMonoidHom ≤ J := by
        rw [hJ, Subgroup.map_iSup]
        refine iSup_le fun m => ?_
        rw [Subgroup.map_iSup]
        refine iSup_le fun hm => ?_
        rw [Subgroup.map_map]
        exact le_iSup₂_of_le (n * m) (mul_mem hn hm) (le_of_eq rfl)
      exact hle ⟨w, hw, rfl⟩
    have hV'J : V' ≤ J := by
      have := le_iSup₂_of_le (f := fun (m : MulAut (Hat V (A6.g1 T V) W)) (_ : m ∈ X.img
        (A6.g1 T V)) => V'.map m.toMonoidHom) 1 (one_mem _) le_rfl
      intro v hv
      exact this ⟨v, hv, rfl⟩
    exact X.eq_top_of_inv (fun h => hV'ne (le_bot_iff.mp (h ▸ hV'J)))
      (fun m hm => hinv m (X.img_K₀_le hm)) (fun m hm => hinv m (X.img_T_le hm))

theorem isInv_map_of_mem_T {I : Subgroup (Hat V (A6.g1 T V) W)}
    (hI : IsModInv (X.img (conjClosure K T)) I) {y : MulAut (Hat V (A6.g1 T V) W)}
    (hy : y ∈ X.img T) : IsModInv (X.img (conjClosure K T)) (I.map y.toMonoidHom) := by
  rintro ⟨m, hm⟩ _ ⟨i, hi, rfl⟩
  have hn := X.img_g1_le_normalizer (X.img_T_le hy)
  have hm' : y⁻¹ * m * y ∈ X.img (conjClosure K T) := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) m).mp hm
    simpa using this
  refine ⟨(y⁻¹ * m * y) i, hI ⟨_, hm'⟩ i hi, ?_⟩
  show y ((y⁻¹ * m * y) i) = m (y i)
  simp [MulAut.mul_apply]

theorem orbSup_eq_top {I : Subgroup (Hat V (A6.g1 T V) W)} (hne : I ≠ ⊥)
    (hI : IsModInv (X.img (conjClosure K T)) I) : orbSup (X.img T) I = ⊤ := by
  refine X.eq_top_of_inv (fun h => hne ?_) (fun m hm w hw => ?_) (fun t ht w hw => ?_)
  · rw [eq_bot_iff, ← h]
    intro v hv
    exact (le_iSup₂_of_le (f := fun (t : MulAut (Hat V (A6.g1 T V) W)) (_ : t ∈ X.img T) =>
      I.map t.toMonoidHom) 1 (one_mem _) le_rfl) ⟨v, hv, rfl⟩
  · have hinv : IsModInv (X.img (conjClosure K T)) (orbSup (X.img T) I) :=
      XMod.isInv_iSup fun t => XMod.isInv_iSup fun ht => X.isInv_map_of_mem_T hI ht
    exact hinv ⟨m, hm⟩ w hw
  · have hle : (orbSup (X.img T) I).map t.toMonoidHom ≤ orbSup (X.img T) I := by
      rw [orbSup, Subgroup.map_iSup]
      refine iSup_le fun s => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hs => ?_
      rw [Subgroup.map_map]
      exact le_iSup₂_of_le (f := fun (t : MulAut (Hat V (A6.g1 T V) W)) (_ : t ∈ X.img T) =>
        I.map t.toMonoidHom) (t * s) (mul_mem ht hs) (le_of_eq rfl)
    exact hle ⟨w, hw, rfl⟩

theorem exists_irrPlusOn (hA37 : A37ForSQTK) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : ∃ V' : Subgroup (Hat V (A6.g1 T V) W),
      V' ∈ IrrPlusOn (X.img (conjClosure K T)) ⊤ (X.img T) := by
  have hV : ∀ w : Hat V (A6.g1 T V) W, w ^ 2 = 1 := fun w => by
    rw [pow_two]; exact X.top.sec_sq w
  obtain ⟨I₀, hI₀⟩ := exists_mem_irrPlus (X.fixV_img_K₀ hA37 h1222 h1332 h1334) X.top.top_ne_bot
  have hTX : X.img T ≤ Subgroup.normalizer (X.img (conjClosure K T) :
      Set (MulAut (Hat V (A6.g1 T V) W))) := X.img_T_le.trans X.img_g1_le_normalizer
  obtain ⟨V', hV'⟩ := irrPlusOn_nonempty hV hTX X.isSylowTwoOf_img_T.2.1 hI₀
  have hsup : (⨆ y ∈ X.img T, y • I₀) = ⊤ := by
    have hne : I₀ ≠ ⊥ := (bot_le.trans_lt hI₀.2.2.2.1).ne'
    have h1 : (⨆ y ∈ X.img T, y • I₀) = orbSup (X.img T) I₀ := rfl
    rw [h1]
    exact X.orbSup_eq_top hne hI₀.2.1
  rw [hsup] at hV'
  exact ⟨V', hV'⟩

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
