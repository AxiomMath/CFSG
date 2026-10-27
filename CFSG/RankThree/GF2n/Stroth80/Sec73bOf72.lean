module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Normalizer
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trans
public import CFSG.RankThree.GF2n.Stroth80.Sec37CommTrans
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem sec73b_core {H : Type*} [Group H] (A L F : Subgroup H) {t : H}
    (htA : t ∈ A) (ht1 : t ≠ 1) (hAL : A ≤ L)
    (hLab : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) (hLsq : ∀ x ∈ L, x * x = 1)
    (hF1 : ∀ x ∈ L, (∃ s ∈ A, IsConj s x) → x ∈ F)
    (hF2 : ∀ T : Subgroup H, (∀ x ∈ L, (∃ s ∈ A, IsConj s x) → x ∈ T) → F ≤ T)
    (hFL : F ≤ L)
    (h72 : ∀ u ∈ A, u ≠ 1 → ∀ x ∈ L, IsConj u x → x ∉ A → ∀ z ∈ A, IsConj x (x * z))
    (hTI : ∀ u ∈ A, u ≠ 1 → ∀ g : H, g * u * g⁻¹ ∈ A → g ∈ Subgroup.normalizer (A : Set H))
    (hConj : ∀ s ∈ A, ∀ x ∈ L, IsConj s x →
      ∃ h ∈ Subgroup.normalizer (L : Set H), h * s * h⁻¹ = x)
    (hFN : ∀ h ∈ Subgroup.normalizer (L : Set H), ∀ x ∈ F, h * x * h⁻¹ ∈ F)
    (hFA : F ≠ A) :
    ∀ a ∈ F, ∀ b ∈ F, a ≠ 1 → b ≠ 1 → IsConj a b := by
  have hAF : A ≤ F := fun a ha => hF1 a (hAL ha) ⟨a, ha, IsConj.refl a⟩
  have hLinv : ∀ x ∈ L, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hLsq x hx)
  have hex : ∃ z ∈ A, z ≠ 1 ∧ ∃ s₀ ∈ L, s₀ ∉ A ∧ IsConj z s₀ := by
    by_contra hcon
    apply hFA
    refine le_antisymm (hF2 A fun x hxL hx => ?_) hAF
    obtain ⟨s, hsA, hsx⟩ := hx
    by_contra hxA
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [isConj_one_right] at hsx
      exact hxA (by rw [hsx]; exact A.one_mem)
    exact hcon ⟨s, hsA, hs1, x, hxL, hxA, hsx⟩
  obtain ⟨z, hzA, hz1, s₀, hs₀L, hs₀A, hzs₀⟩ := hex
  have hAz : ∀ u ∈ A, u ≠ 1 → IsConj u z := by
    intro u huA hu1
    have huL : u ∈ L := hAL huA
    obtain ⟨ν, hνN, hν⟩ := hConj z hzA s₀ hs₀L hzs₀
    have hνN' : ν⁻¹ ∈ Subgroup.normalizer (L : Set H) := Subgroup.inv_mem _ hνN
    have hz' : ν⁻¹ * s₀ * ν⁻¹⁻¹ = z := by rw [← hν]; group
    have hu'L : ν⁻¹ * u * ν⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hνN' u).mp huL
    have hu'A : ν⁻¹ * u * ν⁻¹⁻¹ ∉ A := by
      intro hu'A
      have hN := hTI u huA hu1 ν⁻¹ hu'A
      exact hs₀A ((Subgroup.mem_normalizer_iff.mp hN s₀).mpr (by rw [hz']; exact hzA))
    have hcu : IsConj u (ν⁻¹ * u * ν⁻¹⁻¹) := isConj_iff.mpr ⟨ν⁻¹, rfl⟩
    have h1 := h72 u huA hu1 _ hu'L hcu hu'A z hzA
    have hz2 : ν⁻¹ * u * ν⁻¹⁻¹ * z = ν⁻¹ * (u * s₀) * ν⁻¹⁻¹ := by
      rw [← hz']; group
    rw [hz2] at h1
    have h3 : IsConj u (u * s₀) :=
      (hcu.trans h1).trans (isConj_iff.mpr ⟨ν, by group⟩)
    have h4 := h72 z hzA hz1 s₀ hs₀L hzs₀ hs₀A u huA
    rw [hLab s₀ hs₀L u huL] at h4
    exact h3.trans (h4.symm.trans hzs₀.symm)
  have ht_class : ∀ u ∈ A, u ≠ 1 → IsConj u t := fun u huA hu1 =>
    (hAz u huA hu1).trans (hAz t htA ht1).symm
  have hkey : ∀ t₁ ∈ F, ∀ t₂ ∈ F, t₁ ≠ t₂ → IsConj t₁ t → IsConj t₂ t →
      IsConj (t₁ * t₂) t := by
    intro t₁ ht₁ t₂ ht₂ hne h₁ h₂
    obtain ⟨g₀, hg₀N, hg₀⟩ := hConj t htA t₂ (hFL ht₂) h₂.symm
    obtain ⟨h, hhN, hht₂⟩ : ∃ h ∈ Subgroup.normalizer (L : Set H), h * t₂ * h⁻¹ = t :=
      ⟨g₀⁻¹, Subgroup.inv_mem _ hg₀N, by rw [← hg₀]; group⟩
    have ht₁'F : h * t₁ * h⁻¹ ∈ F := hFN h hhN t₁ ht₁
    have hconj₁' : IsConj (h * t₁ * h⁻¹) t :=
      (isConj_iff.mpr ⟨h⁻¹, by group⟩ : IsConj (h * t₁ * h⁻¹) t₁).trans h₁
    have hne' : h * t₁ * h⁻¹ ≠ t := by
      intro heq
      apply hne
      calc t₁ = h⁻¹ * (h * t₁ * h⁻¹) * h := by group
        _ = h⁻¹ * (h * t₂ * h⁻¹) * h := by rw [heq, hht₂]
        _ = t₂ := by group
    have hprod : h * (t₁ * t₂) * h⁻¹ = (h * t₁ * h⁻¹) * t := by
      calc h * (t₁ * t₂) * h⁻¹ = (h * t₁ * h⁻¹) * (h * t₂ * h⁻¹) := by group
        _ = (h * t₁ * h⁻¹) * t := by rw [hht₂]
    by_cases hA' : h * t₁ * h⁻¹ ∈ A
    · have hw : h * t₁ * h⁻¹ * t ∈ A := A.mul_mem hA' htA
      have hw1 : h * t₁ * h⁻¹ * t ≠ 1 := by
        intro h1
        apply hne'
        rw [eq_inv_of_mul_eq_one_left h1, hLinv t (hAL htA)]
      exact (isConj_iff.mpr ⟨h, hprod⟩).trans (ht_class _ hw hw1)
    · have h72' := h72 t htA ht1 (h * t₁ * h⁻¹) (hFL ht₁'F) hconj₁'.symm hA' t htA
      exact (isConj_iff.mpr ⟨h, hprod⟩).trans (h72'.symm.trans hconj₁')
  have hall : ∀ x ∈ F, x ≠ 1 → IsConj x t := by
    let T : Subgroup H :=
      { carrier := {x | x ∈ F ∧ (x = 1 ∨ IsConj x t)}
        mul_mem' := by
          rintro a b ⟨haF, ha⟩ ⟨hbF, hb⟩
          refine ⟨F.mul_mem haF hbF, ?_⟩
          rcases ha with rfl | ha
          · rw [one_mul]; exact hb
          rcases hb with rfl | hb
          · rw [mul_one]; exact Or.inr ha
          by_cases hab : a = b
          · subst hab
            exact Or.inl (hLsq a (hFL haF))
          · exact Or.inr (hkey a haF b hbF hab ha hb)
        one_mem' := ⟨F.one_mem, Or.inl rfl⟩
        inv_mem' := by
          rintro a ⟨haF, ha⟩
          refine ⟨F.inv_mem haF, ?_⟩
          rw [hLinv a (hFL haF)]
          exact ha }
    have hFT : F ≤ T := hF2 T fun x hxL hx => by
      obtain ⟨s, hsA, hsx⟩ := hx
      refine ⟨hF1 x hxL ⟨s, hsA, hsx⟩, ?_⟩
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · right
        have hs1 : s ≠ 1 := by
          rintro rfl
          rw [isConj_one_right] at hsx
          exact hx1 hsx
        exact hsx.symm.trans (ht_class s hsA hs1)
    intro x hxF hx1
    have hxT : x ∈ T := hFT hxF
    exact hxT.2.resolve_left hx1
  intro a ha b hb ha1 hb1
  exact (hall a ha ha1).trans (hall b hb hb1).symm

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem s73b_bar_mono [(Q.subgroupOf M).Normal] {S T : Subgroup G} (hST : S ≤ T) :
    bar M Q S ≤ bar M Q T := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr
    ⟨y, Subgroup.mem_subgroupOf.mpr (hST (Subgroup.mem_subgroupOf.mp hy)), rfl⟩

theorem s73b_mk_eq_one [(Q.subgroupOf M).Normal] {y : G} (hy : y ∈ M) (hyQ : y ∈ Q) :
    QuotientGroup.mk' (Q.subgroupOf M) (⟨y, hy⟩ : M) = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr hyQ

theorem s73b_mk_ne_one [(Q.subgroupOf M).Normal] {y : G} (hy : y ∈ M) (hyQ : y ∉ Q) :
    QuotientGroup.mk' (Q.subgroupOf M) (⟨y, hy⟩ : M) ≠ 1 := by
  intro h
  apply hyQ
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  exact Subgroup.mem_subgroupOf.mp h

theorem s73b_mk_eq_of_mem [(Q.subgroupOf M).Normal] {a b : M}
    (h : ((a⁻¹ * b : M) : G) ∈ Q) :
    QuotientGroup.mk' (Q.subgroupOf M) a = QuotientGroup.mk' (Q.subgroupOf M) b := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf.mpr h

theorem s73b_inv_mul_mem (hc : Ctx M Q Z B) {x y : G} (hx : x ∈ M) (h : y * x⁻¹ ∈ Q) :
    x⁻¹ * y ∈ Q := by
  have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hx)) (y * x⁻¹)).mp h
  have e : x⁻¹ * (y * x⁻¹) * x⁻¹⁻¹ = x⁻¹ * y := by group
  rwa [e] at h1

theorem s73b_mul_inv_mem (hc : Ctx M Q Z B) {x y : G} (hx : x ∈ M) (h : x⁻¹ * y ∈ Q) :
    y * x⁻¹ ∈ Q := by
  have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hx) (x⁻¹ * y)).mp h
  have e : x * (x⁻¹ * y) * x⁻¹ = y * x⁻¹ := by group
  rwa [e] at h1

theorem s73b_isConj_iff [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {σ y : G}
    (hσ : σ ∈ M) (hy : y ∈ M) :
    IsConj (QuotientGroup.mk' (Q.subgroupOf M) (⟨σ, hσ⟩ : M) : Mbar M Q)
      (QuotientGroup.mk' (Q.subgroupOf M) (⟨y, hy⟩ : M)) ↔ ConjMod M Q σ y := by
  constructor
  · intro h
    obtain ⟨c, hc'⟩ := isConj_iff.mp h
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) c
    rw [← map_inv, ← map_mul, ← map_mul] at hc'
    have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hc')
    have hxM : (g : G) * σ * (g : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem g.2 hσ) (M.inv_mem g.2)
    unfold ConjMod
    refine ⟨hy, g, g.2, s73b_mul_inv_mem hc hxM ?_⟩
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  · intro h
    unfold ConjMod at h
    obtain ⟨-, g, hg, hq⟩ := h
    refine isConj_iff.mpr ⟨QuotientGroup.mk' (Q.subgroupOf M) (⟨g, hg⟩ : M), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    apply s73b_mk_eq_of_mem
    have hxM : g * σ * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hσ) (M.inv_mem hg)
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using s73b_inv_mul_mem hc hxM hq

theorem s73b_mem_normalizer_bar [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S)
    (γ : M) (hγ : (γ : G) ∈ Subgroup.normalizer (S : Set G)) :
    QuotientGroup.mk' (Q.subgroupOf M) γ ∈
      Subgroup.normalizer ((bar M Q S : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  try simp only [SetLike.mem_coe]
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
  rw [← map_inv, ← map_mul, ← map_mul, Tim37.mk_mem_bar_iff' hQS, Tim37.mk_mem_bar_iff' hQS]
  have h1 := Subgroup.mem_normalizer_iff.mp hγ (y : G)
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1

theorem s73b_mem_normalizer_of_bar [(Q.subgroupOf M).Normal] {S : Subgroup G} (hQS : Q ≤ S)
    (hSM : S ≤ M) (γ : M)
    (hN : QuotientGroup.mk' (Q.subgroupOf M) γ ∈
      Subgroup.normalizer ((bar M Q S : Subgroup (Mbar M Q)) : Set (Mbar M Q))) :
    (γ : G) ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  try simp only [SetLike.mem_coe]
  by_cases hxM : x ∈ M
  · have h1 := Subgroup.mem_normalizer_iff.mp hN (QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩)
    try simp only [SetLike.mem_coe] at h1
    rw [← map_inv, ← map_mul, ← map_mul, Tim37.mk_mem_bar_iff' hQS,
      Tim37.mk_mem_bar_iff' hQS] at h1
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1
  · constructor
    · intro hx
      exact absurd (hSM hx) hxM
    · intro hx
      exfalso
      apply hxM
      have h2 : (γ : G)⁻¹ * ((γ : G) * x * (γ : G)⁻¹) * (γ : G) ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem γ.2) (hSM hx)) γ.2
      have e : (γ : G)⁻¹ * ((γ : G) * x * (γ : G)⁻¹) * (γ : G) = x := by group
      rwa [e] at h2

theorem s73b_conc71a_congr (hc : Ctx M Q Z B) {s t : G}
    (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t) (hCN : hc.CN s = hc.CN t) :
    Conc71a hc s ↔ Conc71a hc t := by
  unfold Conc71a
  rw [hR, hCN]

theorem s73b_conc71abcd_congr (hc : Ctx M Q Z B) {n : ℕ} {s t : G}
    (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) :
    Conc71abcd hc n s ↔ Conc71abcd hc n t := by
  have hCN := hc.CN_congr hR hV
  unfold Conc71abcd Conc71b Conc71c Conc71d
  rw [s73b_conc71a_congr hc hR hCN, OmegaMinusNat_congr hc hR hV 3,
    OmegaPlusNat_congr hc hR hV 3, OmegaPlusNat_congr hc hR hV 4]

theorem s73b_conjMod_mul (h72 : Stroth72Statement) (hZt : Sec7ZtStatement)
    (hZc : Sec7CentreMpStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hno : ¬ Conc71abcd hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {σ y ζ : G} (hσ : σ ∈ Z0) (hσQ : σ ∉ Q)
    (hyL : y ∈ LB M Q B) (hcm : ConjMod M Q σ y) (hyZ : y ∉ Z0) (hζ : ζ ∈ Z0) :
    ConjMod M Q y (y * ζ) := by
  obtain ⟨hR, hV⟩ := hZt G M Q Z B hc n t hs Z0 hZ0 σ hσ hσQ
  have hσL : σ ∈ LB M Q B := (hZc G M Q Z B hc n t hs Z0 hZ0 σ hσ).1
  have hs' : Sec7Hyp hc n σ := hs.congr hσL hσQ hR hV
  have hno' : ¬ Conc71abcd hc n σ := fun h => hno ((s73b_conc71abcd_congr hc hR hV).mp h)
  have hZ0' : IsCentrePre Z0 (Rt M (LB M Q B) σ) Q := by rw [hR]; exact hZ0
  obtain ⟨ν, hνCN, hνrel⟩ := h72 G M Q Z B hc n σ hs' hno' Z0 hZ0' y hyL hcm hyZ ζ hζ
  have hνM : ν ∈ M := hc.Rt_le_M σ (Ctx.mem_CN.mp hνCN).1
  unfold ConjMod
  refine ⟨M.mul_mem (hc.LB_le_M hyL) (hc.centre_le_M t hZ0 hζ), ν, hνM, ?_⟩
  have e : y * ζ * (ν * y * ν⁻¹)⁻¹ = ((ν * y * ν⁻¹) * (y * ζ)⁻¹)⁻¹ := by group
  rw [e]
  exact Q.inv_mem hνrel

theorem stroth73b_of_72 (h72 : Stroth72Statement) (h73a : Stroth73aStatement)
    (hZV : Sec7ZVStatement) (hZt : Sec7ZtStatement) (hZc : Sec7CentreMpStatement)
    (hNC : Sec7ConjStatement) (hNC4 : Sec7ConjOm4Statement) : Stroth73bStatement := by
  intro G _ _ M Q Z B hc n t hs hno Z0 hZ0
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  by_cases hF : Fgen M Q (LB M Q B) Z0 = Z0
  · exact Or.inl hF
  refine Or.inr ?_
  have htL : t ∈ LB M Q B := hs.toSec5.mem
  have htQ : t ∉ Q := hs.toSec5.notQ
  have htM : t ∈ M := hc.LB_le_M htL
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) htL hZ0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre htL hZ0
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hZ0L : Z0 ≤ LB M Q B := fun z hz => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).1
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hLM : LB M Q B ≤ M := hc.LB_le_M
  have hQF : Q ≤ Fgen M Q (LB M Q B) Z0 := Q_le_Fgen hQL hc.hyp.Q_normal.1
  have hFM : Fgen M Q (LB M Q B) Z0 ≤ M := (Fgen_le M Q (LB M Q B) Z0).trans hLM
  have htA : QuotientGroup.mk' (Q.subgroupOf M) (⟨t, htM⟩ : M) ∈ bar M Q Z0 :=
    (Tim37.mk_mem_bar_iff' hQZ0 ⟨t, htM⟩).mpr htZ0
  have ht1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨t, htM⟩ : M) ≠ 1 :=
    s73b_mk_ne_one htM htQ
  have hAL : bar M Q Z0 ≤ bar M Q (LB M Q B) := s73b_bar_mono hZ0L
  have hFL : bar M Q (Fgen M Q (LB M Q B) Z0) ≤ bar M Q (LB M Q B) :=
    s73b_bar_mono (Fgen_le M Q (LB M Q B) Z0)
  have hLab : ∀ x ∈ bar M Q (LB M Q B), ∀ y ∈ bar M Q (LB M Q B), x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val
      (hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hLsq : ∀ x ∈ bar M Q (LB M Q B), x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hc.isElemAbelian_bar_LB.2 x hx
  have hF1 : ∀ x ∈ bar M Q (LB M Q B),
      (∃ s ∈ bar M Q Z0, IsConj s x) → x ∈ bar M Q (Fgen M Q (LB M Q B) Z0) := by
    intro x hxL hsx
    obtain ⟨s, hsA, hsx'⟩ := hsx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
    obtain ⟨σ, hσZ, rfl⟩ := Subgroup.mem_map.mp hsA
    have hyL : (y : G) ∈ LB M Q B := (Tim37.mk_mem_bar_iff' hQL y).mp hxL
    have hσZ' : (σ : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hσZ
    have hcm : ConjMod M Q (σ : G) (y : G) := (s73b_isConj_iff hc σ.2 y.2).mp hsx'
    have hyF : (y : G) ∈ Fgen M Q (LB M Q B) Z0 :=
      Subgroup.subset_closure ⟨hyL, (σ : G), hσZ', hcm⟩
    exact (Tim37.mk_mem_bar_iff' hQF y).mpr hyF
  have hF2 : ∀ T : Subgroup (Mbar M Q), (∀ x ∈ bar M Q (LB M Q B),
      (∃ s ∈ bar M Q Z0, IsConj s x) → x ∈ T) → bar M Q (Fgen M Q (LB M Q B) Z0) ≤ T := by
    intro T hT
    have hgen : Fgen M Q (LB M Q B) Z0 ≤
        (T.comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨hxL, s, hsZ, hcm⟩
      have hxM : x ∈ M := hLM hxL
      have hmem : QuotientGroup.mk' (Q.subgroupOf M) (⟨x, hxM⟩ : M) ∈ T := by
        apply hT
        · exact (Tim37.mk_mem_bar_iff' hQL ⟨x, hxM⟩).mpr hxL
        · exact ⟨QuotientGroup.mk' (Q.subgroupOf M) (⟨s, hZ0M hsZ⟩ : M),
            (Tim37.mk_mem_bar_iff' hQZ0 ⟨s, hZ0M hsZ⟩).mpr hsZ,
            (s73b_isConj_iff hc (hZ0M hsZ) hxM).mpr hcm⟩
      exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, Subgroup.mem_comap.mpr hmem, rfl⟩
    intro f hf
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hf
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hgen (Subgroup.mem_subgroupOf.mp hy))
    have hzy' : z = y := Subtype.ext hzy
    subst hzy'
    exact Subgroup.mem_comap.mp hz
  have h72c : ∀ u ∈ bar M Q Z0, u ≠ 1 → ∀ x ∈ bar M Q (LB M Q B), IsConj u x →
      x ∉ bar M Q Z0 → ∀ z ∈ bar M Q Z0, IsConj x (x * z) := by
    intro u huA hu1 x hxL hux hxA z hzA
    obtain ⟨σ, hσA, rfl⟩ := Subgroup.mem_map.mp huA
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
    obtain ⟨ζ, hζA, rfl⟩ := Subgroup.mem_map.mp hzA
    have hσZ : (σ : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hσA
    have hζZ : (ζ : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hζA
    have hσQ : (σ : G) ∉ Q := fun hq => hu1 (s73b_mk_eq_one σ.2 hq)
    have hyL : (y : G) ∈ LB M Q B := (Tim37.mk_mem_bar_iff' hQL y).mp hxL
    have hyZ : (y : G) ∉ Z0 := fun h => hxA ((Tim37.mk_mem_bar_iff' hQZ0 y).mpr h)
    have hcm : ConjMod M Q (σ : G) (y : G) := (s73b_isConj_iff hc σ.2 y.2).mp hux
    have hyζ := s73b_conjMod_mul h72 hZt hZc hc hs hno hZ0 hσZ hσQ hyL hcm hyZ hζZ
    rw [← map_mul]
    exact (s73b_isConj_iff hc y.2 (M.mul_mem y.2 ζ.2)).mpr hyζ
  have hTIc : ∀ u ∈ bar M Q Z0, u ≠ 1 → ∀ g : Mbar M Q, g * u * g⁻¹ ∈ bar M Q Z0 →
      g ∈ Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := by
    intro u huA hu1 g hgA
    obtain ⟨σ, hσA, rfl⟩ := Subgroup.mem_map.mp huA
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) g
    rw [← map_inv, ← map_mul, ← map_mul, Tim37.mk_mem_bar_iff' hQZ0] at hgA
    have hσZ : (σ : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hσA
    have hσQ : (σ : G) ∉ Q := fun hq => hu1 (s73b_mk_eq_one σ.2 hq)
    have hγ : (γ : G) ∈ Subgroup.normalizer (Z0 : Set G) :=
      Z0_normalizes_of_ZV h73a hZV G M Q Z B hc n t hs hno Z0 hZ0 (γ : G) γ.2 (σ : G) hσZ hσQ
        (by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hgA)
    exact s73b_mem_normalizer_bar hQZ0 γ hγ
  have hConjc : ∀ s ∈ bar M Q Z0, ∀ x ∈ bar M Q (LB M Q B), IsConj s x →
      ∃ h ∈ Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set (Mbar M Q)),
        h * s * h⁻¹ = x := by
    intro s hsA x hxL hsx
    obtain ⟨σ, hσA, rfl⟩ := Subgroup.mem_map.mp hsA
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) x
    have hσZ : (σ : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hσA
    have hyL : (y : G) ∈ LB M Q B := (Tim37.mk_mem_bar_iff' hQL y).mp hxL
    have hcm : ConjMod M Q (σ : G) (y : G) := (s73b_isConj_iff hc σ.2 y.2).mp hsx
    obtain ⟨ν, hνM, hνN, hνq⟩ : ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
        (y : G) * ((ν : G) * (σ : G) * (ν : G)⁻¹)⁻¹ ∈ Q := by
      by_cases hom : OmegaMinusNat hc t 2
      · exact hNC4 G M Q Z B hc n t hs hom Z0 hZ0 (σ : G) hσZ (y : G) hyL hcm
      · exact hNC G M Q Z B hc n t hs hom Z0 hZ0 (σ : G) hσZ (y : G) hyL hcm
    refine ⟨QuotientGroup.mk' (Q.subgroupOf M) (⟨ν, hνM⟩ : M),
      s73b_mem_normalizer_bar hQL ⟨ν, hνM⟩ hνN, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    apply s73b_mk_eq_of_mem
    have hxM : (ν : G) * (σ : G) * (ν : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem hνM σ.2) (M.inv_mem hνM)
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using s73b_inv_mul_mem hc hxM hνq
  have hFNc : ∀ h ∈ Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) :
        Set (Mbar M Q)), ∀ x ∈ bar M Q (Fgen M Q (LB M Q B) Z0),
        h * x * h⁻¹ ∈ bar M Q (Fgen M Q (LB M Q B) Z0) := by
    intro h hhN x hxF
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) h
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxF
    have hγN : (γ : G) ∈ Subgroup.normalizer (LB M Q B : Set G) :=
      s73b_mem_normalizer_of_bar hQL hLM γ hhN
    have hyF : (y : G) ∈ Fgen M Q (LB M Q B) Z0 := Subgroup.mem_subgroupOf.mp hy
    have hcon : (γ : G) * (y : G) * (γ : G)⁻¹ ∈ Fgen M Q (LB M Q B) Z0 :=
      Fgen_conj_mem hc γ.2 hγN hyF
    rw [← map_inv, ← map_mul, ← map_mul, Tim37.mk_mem_bar_iff' hQF]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hcon
  have hFAc : bar M Q (Fgen M Q (LB M Q B) Z0) ≠ bar M Q Z0 := by
    intro hEq
    apply hF
    refine le_antisymm (fun x hx => ?_) (Z0_le_Fgen hZ0L hZ0M Q)
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨x, hFM hx⟩ : M) ∈
        bar M Q (Fgen M Q (LB M Q B) Z0) := (Tim37.mk_mem_bar_iff' hQF ⟨x, hFM hx⟩).mpr hx
    rw [hEq] at h1
    exact (Tim37.mk_mem_bar_iff' hQZ0 ⟨x, hFM hx⟩).mp h1
  have key := sec73b_core (H := Mbar M Q) (bar M Q Z0) (bar M Q (LB M Q B))
    (bar M Q (Fgen M Q (LB M Q B) Z0)) htA ht1 hAL hLab hLsq hF1 hF2 hFL h72c hTIc hConjc
    hFNc hFAc
  intro a ha b hb haQ hbQ _ _
  have haM : a ∈ M := hLM (Fgen_le M Q (LB M Q B) Z0 ha)
  have hbM : b ∈ M := hLM (Fgen_le M Q (LB M Q B) Z0 hb)
  have hma : QuotientGroup.mk' (Q.subgroupOf M) (⟨a, haM⟩ : M) ∈
      bar M Q (Fgen M Q (LB M Q B) Z0) := (Tim37.mk_mem_bar_iff' hQF ⟨a, haM⟩).mpr ha
  have hmb : QuotientGroup.mk' (Q.subgroupOf M) (⟨b, hbM⟩ : M) ∈
      bar M Q (Fgen M Q (LB M Q B) Z0) := (Tim37.mk_mem_bar_iff' hQF ⟨b, hbM⟩).mpr hb
  exact (s73b_isConj_iff hc haM hbM).mp
    (key _ hma _ hmb (s73b_mk_ne_one haM haQ) (s73b_mk_ne_one hbM hbQ))

end CFSG.RankThree.GF2n.Stroth80
