module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Line
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Lin2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Space

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

section Geo2

variable {W : Type} [CommGroup W]

structure Geo2 (S : OmegaModel W) (E : Subgroup (MulAut W)) : Prop where
  lin : ∀ g ∈ E, ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w)
  iso : ∀ g ∈ E, ∀ w : W, S.Q (g w) = S.Q w
  elem : IsElemAbelian2 E
  ne_bot : E ≠ ⊥
  a2 : ∀ B : Subgroup (MulAut W), B ≤ E → E3.mQuot E B < 2 → fixV B = fixV E

theorem Geo2.of_aSet {S : OmegaModel W} {X E : Subgroup (MulAut W)}
    (hX : X ≤ Subgroup.normalizer (S.omega : Set (MulAut W))) (hE : E ∈ E3.aSet 2 X) :
    Geo2 S E :=
  ⟨S.linear_of_mem_aSet_two hX hE, S.isometry_of_mem_aSet_two hX hE, hE.2.2.1, hE.2.1,
    hE.2.2.2⟩

namespace OmegaModel

variable (S : OmegaModel W)

theorem finite_carrier (S : OmegaModel W) : Finite W := Finite.of_injective S.vec S.vec_injective

theorem isSub_line (w : W) : S.IsSub (S.line w) := by
  rintro c _ ⟨a, rfl⟩
  exact ⟨c * a, by rw [S.smul_smul_eq]⟩

theorem isSub_sup {U V : Subgroup W} (hU : S.IsSub U) (hV : S.IsSub V) : S.IsSub (U ⊔ V) := by
  intro c x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.1 hx
  exact Subgroup.mem_sup.2
    ⟨S.smul c u, hU c u hu, S.smul c v, hV c v hv, (S.smul_mul_eq c u v).symm⟩

theorem card_isSub_cases (hSK : Nat.card S.K = 4) {U : Subgroup W} (hU : S.IsSub U) :
    Nat.card U = 1 ∨ Nat.card U = 4 ∨ Nat.card U = 16 ∨ Nat.card U = 64 ∨ Nat.card U = 256 := by
  obtain ⟨d, hd⟩ := S.exists_card_eq_pow hU
  haveI := S.finite_carrier
  have hle : Nat.card U ≤ Nat.card W := Subgroup.card_le_card_group U
  rw [S.card_eq, hd, hSK] at hle
  have hd4 : d ≤ 4 := by
    by_contra h
    push Not at h
    have : 4 ^ 5 ≤ 4 ^ d := Nat.pow_le_pow_right (by norm_num) h
    have h4 : 4 ^ 5 ≤ 4 ^ 4 := le_trans this hle
    norm_num at h4
  rw [hd, hSK]
  interval_cases d <;> simp

theorem exists_smul_eq_of_card_eq {F : Subgroup W} (hF : S.IsSub F)
    (hcard : Nat.card F = Nat.card S.K) {z : W} (hz : z ∈ F) (hz1 : z ≠ 1) :
    ∀ f ∈ F, ∃ c : S.K, f = S.smul c z := by
  haveI := S.finite_carrier
  have hle : S.line z ≤ F := by
    rintro _ ⟨c, rfl⟩
    exact hF c z hz
  have heq : S.line z = F :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, S.card_line hz1])
  intro f hf
  rw [← heq] at hf
  exact hf

end OmegaModel

variable {S : OmegaModel W} {E : Subgroup (MulAut W)}

theorem Geo2.isSub_fixV (hE : Geo2 S E) : S.IsSub (fixV E) := fun c u hu =>
  mem_fixV.2 fun g hg => by rw [hE.lin g hg c u, mem_fixV.1 hu g hg]

theorem Geo2.two_le_mQuot_stabAt (hE : Geo2 S E) {w : W} (hw : w ∉ fixV E) :
    2 ≤ E3.mQuot E (stabAt E w) := by
  by_contra hlt
  push Not at hlt
  have h := hE.a2 (stabAt E w) (stabAt_le E w) hlt
  apply hw
  rw [← h]
  exact mem_fixV.2 fun a ha => (mem_stabAt.1 ha).2

theorem Geo2.mQuot_stabAt_le_two (hE : Geo2 S E) {U : Subgroup W} {w : W}
    (hw : ∀ e ∈ E, e w * w⁻¹ ∈ U) (hU : Nat.card U ≤ 4) : E3.mQuot E (stabAt E w) ≤ 2 := by
  haveI := S.finite_carrier
  have h := two_pow_mQuot_stabAt_le hE.elem hw
  by_contra hlt
  push Not at hlt
  have h8 : 2 ^ 3 ≤ 2 ^ E3.mQuot E (stabAt E w) := Nat.pow_le_pow_right (by norm_num) hlt
  omega

theorem mem_gammaCheck_of_mQuot_stabAt_le {w : W}
    (h : E3.mQuot E (stabAt E w) ≤ 2) : w ∈ E3.gammaCheck 2 E :=
  (le_iSup_of_le (stabAt E w) (le_iSup_of_le (stabAt_le E w) (le_iSup_of_le h le_rfl)) :
    fixV (stabAt E w) ≤ E3.gammaCheck 2 E) (mem_fixV.2 fun a ha => (mem_stabAt.1 ha).2)

theorem eq_top_of_forall_notMem {G : Type*} [Group G] {H T : Subgroup G} (hT : T ≠ ⊤)
    (h : ∀ x, x ∉ T → x ∈ H) : H = ⊤ := by
  obtain ⟨w, hw⟩ : ∃ w, w ∉ T := by
    by_contra hcon
    push Not at hcon
    exact hT (Subgroup.eq_top_iff' T |>.2 hcon)
  rw [Subgroup.eq_top_iff']
  intro g
  by_cases hg : g ∈ T
  · have hgw : g * w ∉ T := fun hgw => hw (by simpa using T.mul_mem (T.inv_mem hg) hgw)
    have := H.mul_mem (h _ hgw) (H.inv_mem (h w hw))
    simpa using this
  · exact h g hg

theorem Geo2.card_fixV_cases (hE : Geo2 S E) (hSK : Nat.card S.K = 4) :
    Nat.card (fixV E) = 4 ∨ Nat.card (fixV E) = 16 ∨ Nat.card (fixV E) = 64 := by
  haveI := S.finite_carrier
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact S.mul_self_eq_one w
  haveI : Nontrivial W := ⟨⟨1, S.ofVec (Pi.single (Sum.inl 0) 1), fun h => by
    have h1 := congrArg S.vec h
    rw [S.vec_one, S.vec_ofVec] at h1
    have h2 := congrFun h1 (Sum.inl 0)
    simp at h2⟩⟩
  have hbot : fixV E ≠ ⊥ := fixV_ne_bot hW2 hE.elem
  have htop : fixV E ≠ ⊤ := fixV_ne_top hE.ne_bot
  rcases S.card_isSub_cases hSK hE.isSub_fixV with h | h | h | h | h
  · exact absurd (Subgroup.card_eq_one.1 h) hbot
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    apply htop
    rw [← Subgroup.card_eq_iff_eq_top, h, S.card_eq, hSK]
    norm_num

theorem exists_comm_eq_of_card_le [Finite W] {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A)
    {U : Subgroup W} {w : W} (hw : ∀ a ∈ A, a w * w⁻¹ ∈ U)
    (hge : Nat.card U ≤ 2 ^ E3.mQuot A (stabAt A w)) : ∀ u ∈ U, ∃ a ∈ A, a w * w⁻¹ = u := by
  letI : MulAction A W := MulAction.compHom W A.subtype
  have hstab : MulAction.stabilizer A w = (stabAt A w).subgroupOf A := by
    ext a
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_stabAt,
      MulAction.compHom_smul_def, MulAut.smul_def]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  let f : MulAction.orbit A w → U := fun x =>
    let a : A := Classical.choose (MulAction.mem_orbit_iff.mp x.2)
    ⟨x.1 * w⁻¹, by
      have ha : a • w = x.1 := Classical.choose_spec (MulAction.mem_orbit_iff.mp x.2)
      rw [← ha, MulAction.compHom_smul_def, MulAut.smul_def]
      exact hw (a : MulAut W) a.2⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : x.1 * w⁻¹ = y.1 * w⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_right_cancel h1)
  have hcard : Nat.card (MulAction.orbit A w) = 2 ^ E3.mQuot A (stabAt A w) :=
    calc Nat.card (MulAction.orbit A w) = (MulAction.orbit A w).ncard :=
          Nat.card_coe_set_eq _
      _ = (MulAction.stabilizer A w).index := (MulAction.index_stabilizer A w).symm
      _ = ((stabAt A w).subgroupOf A).index := by rw [hstab]
      _ = (stabAt A w).relIndex A := rfl
      _ = 2 ^ E3.mQuot A (stabAt A w) := E3.relIndex_eq_two_pow (E3.isPGroup_of_isElemAbelian2 hA) _
  have hbij : Function.Bijective f :=
    hf_inj.bijective_of_nat_card_le (by rw [hcard]; exact hge)
  intro u hu
  obtain ⟨x, hx⟩ := hbij.2 ⟨u, hu⟩
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp x.2
  refine ⟨(a : MulAut W), a.2, ?_⟩
  have h1 : x.1 * w⁻¹ = u := congrArg Subtype.val hx
  rw [← h1, ← ha, MulAction.compHom_smul_def, MulAut.smul_def]
  rfl

end Geo2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
