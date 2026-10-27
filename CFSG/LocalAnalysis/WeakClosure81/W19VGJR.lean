module

public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenTwo
public import CFSG.Quasithin.Background.E1Sec7
public import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem exists_eq_of_card_two {H : Type*} [Group H] {A : Subgroup H}
    (hA : Nat.card A = 2) : ∃ b ∈ A, b * b = 1 ∧ ∀ x ∈ A, x = 1 ∨ x = b := by
  classical
  have hAne : A ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hA
    exact absurd hA (by norm_num)
  obtain ⟨⟨b, hbA⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
  refine ⟨b, hbA, ?_, ?_⟩
  · have hd : orderOf (⟨b, hbA⟩ : ↥A) ∣ 2 := by
      have h0 := orderOf_dvd_natCard (⟨b, hbA⟩ : ↥A)
      rwa [hA] at h0
    have h2 : (⟨b, hbA⟩ : ↥A) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
    simpa [pow_two] using congrArg Subtype.val h2
  · intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · refine Or.inr ?_
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).1 hA
      have e1 : (⟨x, hx⟩ : ↥A) = y := hy _ (fun h' => hx1 (congrArg Subtype.val h'))
      have e2 : (⟨b, hbA⟩ : ↥A) = y := hy _ hb1
      exact congrArg Subtype.val (e1.trans e2.symm)

theorem commSub_le_fixSub_of_card_two {A : Subgroup (LGL 2 V)} (hA2 : Nat.card A = 2) :
    commSub A ≤ fixSub A := by
  obtain ⟨b, hbA, hbb, huniq⟩ := exists_eq_of_card_two hA2
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hfix : ∀ u ∈ commSub A, b u = u := by
    intro u hu
    refine Submodule.span_induction (p := fun u _ => b u = u) ?_ ?_ ?_ ?_ hu
    · rintro w ⟨a, ha, v, rfl⟩
      rcases huniq a ha with h1 | h1
      · rw [h1]
        simp
      · rw [h1]
        have hbbv : b (b v) = v := by
          have := congrArg (fun z : LGL 2 V => z v) hbb
          simpa using this
        have hx : (b v - v) + (b v - v) = 0 := h2 _
        have h6 : -(b v - v) = b v - v := neg_eq_of_add_eq_zero_left hx
        rw [map_sub, hbbv, ← h6]
        abel
    · exact map_zero b
    · intro x y _ _ hx hy
      rw [map_add, hx, hy]
    · intro c x _ hx
      rw [map_smul, hx]
  intro u hu
  refine (mem_fixSub A).2 fun a ha => ?_
  rcases huniq a ha with h1 | h1
  · rw [h1]
    simp
  · rw [h1]
    exact hfix u hu

theorem mRank_cj_le_one {A : Subgroup (LGL 2 V)} (hA2 : Nat.card A = 2) (g : LGL 2 V) :
    mRank (cj g A) ≤ 1 := by
  unfold mRank
  rw [card_cj, hA2]
  have : Nat.log 2 2 = 1 := (Nat.log_eq_iff (Or.inl one_ne_zero)).mpr ⟨by norm_num, by norm_num⟩
  omega

theorem orbit_trans' {G A : Subgroup (LGL 2 V)} :
    ∀ B ∈ {B | ∃ g ∈ G, B = cj g A}, ∀ B' ∈ {B | ∃ g ∈ G, B = cj g A}, ∃ g ∈ G, B' = cj g B := by
  rintro B ⟨g₀, hg₀, rfl⟩ B' ⟨g₁, hg₁, rfl⟩
  refine ⟨g₁ * g₀⁻¹, G.mul_mem hg₁ (G.inv_mem hg₀), ?_⟩
  rw [← cj_mul]
  simp [cj_one, mul_assoc]

variable {G : Subgroup (LGL 2 V)}

@[expose] def JR (G : Subgroup (LGL 2 V)) : Subgroup (VG G) :=
  (pCoreOf 2 G).comap (projG G)

theorem mem_JR {x : VG G} : x ∈ JR G ↔ projG G x ∈ pCoreOf 2 G := Iff.rfl

theorem normal_JR : (JR G).Normal := by
  refine ⟨fun x hx y => ?_⟩
  rw [mem_JR] at hx ⊢
  rw [map_mul, map_mul, map_inv]
  have hy : projG G y ∈ G := (SemidirectProduct.rightHom y).2
  exact (Subgroup.mem_normalizer_iff.1
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G hy) _).1 hx

theorem vHat_le_JR : vHat G ≤ JR G := by
  intro x hx
  obtain ⟨v, -, rfl⟩ := mem_wHat.mp hx
  rw [mem_JR, projG_inl]
  exact Subgroup.one_mem _

theorem inr_mem_JR {r : G} (hr : (r : LGL 2 V) ∈ pCoreOf 2 G) :
    (SemidirectProduct.inr r : VG G) ∈ JR G := by
  rw [mem_JR, projG_inr]
  exact hr

theorem ker_projG_le_vHat : (projG G).ker ≤ vHat G := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx1 : x.right = 1 := Subtype.ext (by simpa [projG] using hx)
  refine mem_wHat.mpr ⟨Multiplicative.toAdd x.left, Submodule.mem_top, ?_⟩
  rw [ofAdd_toAdd]
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [hx1, map_one, mul_one]

theorem isPGroup_JR : IsPGroup 2 (JR G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 ↥(projG G).ker :=
    (isElemAbelian_wHat (G := G) ⊤).isPGroup.to_le ker_projG_le_vHat
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G).comap_of_ker_isPGroup (projG G) hker

theorem JR_le_pCoreOf : JR G ≤ pCoreOf 2 (⊤ : Subgroup (VG G)) :=
  CFSG.LieType.BorelTits.le_pCoreOf 2 le_top (normal_JR.subgroupOf _) isPGroup_JR

theorem inf_UAOf_JR {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {A : Subgroup (LGL 2 V)}
    (hstab : ∀ a ∈ A, conjSub a (VA A) = VA A) (hAG : A ≤ G) (hA : A ⊓ pCoreOf 2 G = ⊥) :
    UAOf G VA A ⊓ JR G = wHat G (VA A) := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨v, hv, g, hg, rfl⟩ := (mem_wHat_sup_aHat hstab).mp hx1
    have hπ : projG G (SemidirectProduct.inl (Multiplicative.ofAdd v) *
        SemidirectProduct.inr g) ∈ pCoreOf 2 G := hx2
    simp only [map_mul, projG_inl, projG_inr, one_mul] at hπ
    have hg1 : (g : LGL 2 V) ∈ A ⊓ pCoreOf 2 G := ⟨hg, hπ⟩
    rw [hA, Subgroup.mem_bot] at hg1
    have : g = 1 := Subtype.ext hg1
    rw [this, map_one, mul_one]
    exact mem_wHat.mpr ⟨v, hv, rfl⟩
  · exact le_inf le_sup_left ((wHat_le_vHat _).trans vHat_le_JR)

theorem exists_mul_of_mem_normalizer_sup {A : Subgroup (LGL 2 V)}
    (h : Assumption131 G {B | ∃ g ∈ G, B = cj g A} commSub 1) (hA2 : Nat.card A = 2)
    {x : LGL 2 V} (hx : x ∈ G)
    (hxn : x ∈ normalizer ((A ⊔ pCoreOf 2 G : Subgroup (LGL 2 V)) : Set (LGL 2 V))) :
    ∃ m ∈ G ⊓ normalizer (A : Set (LGL 2 V)), ∃ r ∈ pCoreOf 2 G, x = m * r := by
  classical
  have hA : A ∈ {B | ∃ g ∈ G, B = cj g A} := ⟨1, G.one_mem, (cj_one A).symm⟩
  have hAG : A ≤ G := h.le_G A hA
  have hrank : ∀ B ∈ {B | ∃ g ∈ G, B = cj g A}, mRank B ≤ 1 := by
    rintro B ⟨g, hg, rfl⟩
    exact mRank_cj_le_one hA2 g
  have hV7 := hyp7_UAOf h hrank hA (commSub_le_fixSub_of_card_two hA2)
  obtain ⟨hΩ, hI⟩ := thirteen_two_three h hrank orbit_trans' hA
  obtain ⟨hVel, -, hVTI⟩ := hV7
  have hUΩ : UAOf G commSub A ∈
      omegaSet (UAOf G commSub A) (⊤ : Subgroup (VG G)) (vHat G) := by
    rw [hΩ]
    exact ⟨A, hA, rfl⟩
  have hUJ : UAOf G commSub A ⊔ JR G = (A ⊔ pCoreOf 2 G).comap (projG G) := by
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        obtain ⟨v, -, rfl⟩ := mem_wHat.mp hy
        rw [Subgroup.mem_comap, projG_inl]
        exact Subgroup.one_mem _
      · intro y hy
        obtain ⟨g, hg, rfl⟩ := mem_aHat.mp hy
        rw [Subgroup.mem_comap, projG_inr]
        exact Subgroup.mem_sup_left hg
      · intro y hy
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_right hy
    · intro y hy
      obtain ⟨v, g, rfl⟩ := exists_eq_inl_mul_inr y
      rw [Subgroup.mem_comap] at hy
      simp only [map_mul, projG_inl, projG_inr, one_mul] at hy
      have hAn : A ≤ normalizer ((pCoreOf 2 G : Subgroup (LGL 2 V)) : Set (LGL 2 V)) :=
        hAG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A (pCoreOf 2 G) hAn]
        at hy
      obtain ⟨a, ha, r, hr, har⟩ := hy
      have hrG : r ∈ G := (CFSG.LieType.BorelTits.pCoreOf_le 2 G) hr
      have hg : g = ⟨a, hAG ha⟩ * ⟨r, hrG⟩ := Subtype.ext har.symm
      have e : (SemidirectProduct.inl (Multiplicative.ofAdd v) * SemidirectProduct.inr g : VG G) =
          SemidirectProduct.inl (Multiplicative.ofAdd v) *
            SemidirectProduct.inr (⟨a, hAG ha⟩ : G) * SemidirectProduct.inr (⟨r, hrG⟩ : G) := by
        rw [hg, map_mul, mul_assoc]
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
      · exact Subgroup.mem_sup_right
          (vHat_le_JR (mem_wHat.mpr ⟨v, Submodule.mem_top, rfl⟩))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_aHat.mpr ⟨_, ha, rfl⟩))
      · exact Subgroup.mem_sup_right (inr_mem_JR hr)
  have hNh : (SemidirectProduct.inr (⟨x, hx⟩ : G) : VG G) ∈
      normalizer ((UAOf G commSub A ⊔ JR G : Subgroup (VG G)) : Set (VG G)) := by
    rw [hUJ, Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv, projG_inr]
    exact Subgroup.mem_normalizer_iff.1 hxn _
  obtain ⟨m, hm, j, hj, hmj⟩ := seven_three_four_normalizer (G := VG G)
    (V := UAOf G commSub A) (H := ⊤) (E := vHat G) (J := JR G)
    hVel hVTI (isElemAbelian_wHat ⊤).1 le_top (normal_vHat.subgroupOf _) hUΩ
    (fun _ _ => le_top) JR_le_pCoreOf (normal_JR.subgroupOf _)
    (hI.le.trans (iSup₂_le fun B _ => (wHat_le_vHat _).trans vHat_le_JR))
    (Subgroup.mem_top _) hNh
  have hm' : m ∈ normalizer ((UAOf G commSub A : Subgroup (VG G)) : Set (VG G)) := hm.2
  refine ⟨projG G m, ⟨(SemidirectProduct.rightHom m).2, ?_⟩, projG G j, hj, ?_⟩
  · have hπ : (UAOf G commSub A).map (projG G) = A := map_projG_wHat_sup_aHat hAG
    apply E1.mem_normalizer_of_conj_mem
    intro y hy
    rw [← hπ] at hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    have h1 : m * u * m⁻¹ ∈ UAOf G commSub A := (Subgroup.mem_normalizer_iff.1 hm' u).1 hu
    rw [← hπ]
    refine Subgroup.mem_map.2 ⟨m * u * m⁻¹, h1, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · have := congrArg (projG G) hmj
    rw [projG_inr, map_mul] at this
    exact this

end CFSG.LocalAnalysis.WeakClosure81

end
