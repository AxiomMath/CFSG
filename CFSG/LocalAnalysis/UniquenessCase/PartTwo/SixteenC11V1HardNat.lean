module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c11_v1_hard_nat_section (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M ⊥ V hV L)} (hF : s16e_two_Fam D ⊥ V L hV P)
    {Q : FFModel → Prop}
    (hP : ∀ (H : Subgroup (MulAut (vStar D.M ⊥ V hV L)))
      (U Z : Subgroup (vStar D.M ⊥ V hV L)), P H U Z →
        ∃ D' : FFModel, Q D' ∧ D'.Realizes H U Z)
    (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) {J₀ : Subgroup (Vtil ⊥ V hV)}
    (hM : S16C11Model (Mbar D.M ⊥ V hV) (kBar D.M ⊥ V hV L) J₀) :
    ∃ φ : ↥(lBar ⊥ V hV L) →* MulAut ↥J₀,
      (∀ (x : ↥(lBar ⊥ V hV L)) (j : ↥J₀),
        (((φ x : MulAut ↥J₀) j : ↥J₀) : Vtil ⊥ V hV) =
          (x : MulAut (Vtil ⊥ V hV)) (j : Vtil ⊥ V hV)) ∧
      commV φ.range = ⊤ ∧ fixV φ.range ≠ ⊥ ∧
      ∃ D' : FFModel, Q D' ∧ D'.Realizes φ.range ⊤ (fixV φ.range) := by
  obtain ⟨κ, e, I₀, I₁, hκsurj, hesurj, hκequiv, hκker, hcomm, hfix, hv1, hinf, hsup,
    hP₀, hP₁, hirr₀, hirr₁⟩ := s16c11_v1_setup_data D hin h1217 hc hs hF
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := s16e_two_lBar_le D hc.setting.hyp151 hV
  have hLK : ∀ l ∈ (lBar ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))),
      ∀ k ∈ (kBar D.M ⊥ V hV L : Subgroup (MulAut (Vtil ⊥ V hV))), l * k = k * l := by
    intro l hl k hk
    rw [kBar] at hk
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2) l hl
  obtain ⟨hJ, Θ, hΘ⟩ := s16c11_v1_model_pair hM hLX hLK
  let φ : ↥(lBar ⊥ V hV L) →* MulAut ↥J₀ :=
    CFSG.Quasithin.H13.VolI.resHom (lBar ⊥ V hV L) J₀ hJ
  let e' : ↥(lStar D.M ⊥ V hV L) →* ↥(φ.range) := φ.rangeRestrict.comp e
  let κ' : ↥J₀ × ↥J₀ →* vStar D.M ⊥ V hV L := κ.comp Θ.toMonoidHom
  have he' : Function.Surjective e' := (MonoidHom.rangeRestrict_surjective φ).comp hesurj
  have hκ' : Function.Surjective κ' := hκsurj.comp (MulEquiv.surjective Θ)
  have hequiv' : ∀ (b : ↥(lStar D.M ⊥ V hV L)) (x : ↥J₀ × ↥J₀),
      κ' (((e' b : ↥(φ.range)) : MulAut ↥J₀) x.1,
          ((e' b : ↥(φ.range)) : MulAut ↥J₀) x.2) =
        (b : MulAut (vStar D.M ⊥ V hV L)) (κ' x) := by
    intro b x
    have h1 : ((e' b : ↥(φ.range)) : MulAut ↥J₀) = φ (e b) := rfl
    rw [h1]
    change κ (Θ (φ (e b) x.1, φ (e b) x.2)) = (b : MulAut (vStar D.M ⊥ V hV L)) (κ (Θ x))
    rw [← hΘ (e b) x]
    exact hκequiv b (Θ x)
  have hker' : ∀ x : ↥J₀ × ↥J₀, κ' x = 1 →
      x.1 ∈ fixV (φ.range) ∧ x.2 ∈ fixV (φ.range) := by
    intro x hx
    have hx' : κ (Θ x) = 1 := hx
    have hxfix : Θ x ∈ fixV (lBar ⊥ V hV L) := hκker (Θ x) hx'
    constructor
    · intro h hh
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hh
      have h1 : Θ (φ l x.1, φ l x.2) = Θ x :=
        (hΘ l x).symm.trans (hxfix l l.2)
      exact congrArg Prod.fst (Θ.injective h1)
    · intro h hh
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hh
      have h1 : Θ (φ l x.1, φ l x.2) = Θ x :=
        (hΘ l x).symm.trans (hxfix l l.2)
      exact congrArg Prod.snd (Θ.injective h1)
  have hcommH : commV (φ.range) = ⊤ := by
    let f : Vtil ⊥ V hV →* ↥J₀ :=
      (MonoidHom.fst (↥J₀) (↥J₀)).comp Θ.symm.toMonoidHom
    have hf : Function.Surjective f := by
      intro a
      refine ⟨Θ (a, 1), ?_⟩
      simp [f]
    refine s16c11_v1_commV_of_surj (A := lBar ⊥ V hV L) (H := φ.range) f hf ?_ hcomm
    intro a ha
    refine ⟨φ ⟨a, ha⟩, MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩, fun w => ?_⟩
    have hww : Θ.symm (a w) =
        (φ ⟨a, ha⟩ (Θ.symm w).1, φ ⟨a, ha⟩ (Θ.symm w).2) := by
      have h := hΘ ⟨a, ha⟩ (Θ.symm w)
      rw [MulEquiv.apply_symm_apply] at h
      rw [h, MulEquiv.symm_apply_apply]
    show (Θ.symm (a w)).1 = (φ ⟨a, ha⟩) ((Θ.symm w).1)
    rw [hww]
  have hfixHne : fixV (φ.range) ≠ ⊥ := by
    intro hfixH
    have hkerbot : κ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_bot]
      have hx : κ' (Θ.symm w) = 1 := by
        show κ (Θ (Θ.symm w)) = 1
        rw [MulEquiv.apply_symm_apply]
        exact MonoidHom.mem_ker.mp hw
      have hk := hker' (Θ.symm w) hx
      have h1 : (Θ.symm w).1 = 1 := by simpa [hfixH] using hk.1
      have h2 : (Θ.symm w).2 = 1 := by simpa [hfixH] using hk.2
      have hx1 : Θ.symm w = 1 := Prod.ext h1 h2
      calc w = Θ (Θ.symm w) := (MulEquiv.apply_symm_apply Θ w).symm
        _ = Θ 1 := by rw [hx1]
        _ = 1 := map_one Θ
    exact hV1 (hv1 hkerbot)
  obtain ⟨D₀, hQ₀, hR₀⟩ := hP (lStar D.M ⊥ V hV L) I₀ ⊥ hP₀
  obtain ⟨D₁, hQ₁, hR₁⟩ := hP (lStar D.M ⊥ V hV L) I₁ ⊥ hP₁
  have hcover := s16c11_v1_two_summand_cover e' he' κ' hκ' hequiv' hker' hfix hinf hsup
    hirr₀ hirr₁ hR₀ hR₁
  refine ⟨φ, ?_, hcommH, hfixHne, ?_⟩
  · intro x j
    exact CFSG.Quasithin.H13.VolI.coe_resHom_apply (lBar ⊥ V hV L) J₀ hJ x j
  · rcases hcover with h | h
    · exact ⟨D₀, hQ₀, h⟩
    · exact ⟨D₁, hQ₁, h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
