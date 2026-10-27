module

public import CFSG.Milestones.ASVolI.F431.L33
public import CFSG.Milestones.ASVolI.F431.BOut
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Conjugacy

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def burnsideF4m_Core1 {E : Type} [Group E] (Gp M₁ : Subgroup E) : Prop :=
  ∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))

@[expose] def burnsideF4m_Core2 (κ : GLKind) {E : Type} [Group E] (Gp M₂ : Subgroup E) : Prop :=
  ∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 → κ = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))

@[expose] def burnsideF4m_LieCoreInput : Prop :=
  (∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → 2 ≤ f → (κ = .G2 ∨ κ = .D4tw) → ¬ Odd Gp.index →
    burnsideF4m_Core1 Gp M₁ ∧ burnsideF4m_Core2 κ Gp M₂) ∧
  (∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ 2 f Gp M₁ M₂ → 2 ≤ f → (κ = .U4 ∨ κ = .U5) → ¬ Odd Gp.index →
    burnsideF4m_Core1 Gp M₁ ∧ burnsideF4m_Core2 κ Gp M₂ ∧ pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂)) ∧
  (∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 .Sp4 2 f Gp M₁ M₂ → 2 ≤ f → ¬ Odd Gp.index →
    burnsideF4m_Core1 Gp M₁ ∧ burnsideF4m_Core2 .Sp4 Gp M₂ ∧
      pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁) ∧ pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) ∧
      pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))

section GLevel

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_centerOf_perfectCore_MiOne (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) :
    centerOf (perfectCore (MiOne β ε)) =
      subImg (burnsideF4d_bOne β ε) (centerOf (perfectCore M₁)) := by
  have hb := burnsideF4j_bOne_injective hyp
  rw [burnsideF4d_MiOne_eq, subImg_perfectCore hb le_rfl,
    subImg_centerOf hb (perfectCore_le M₁)]

theorem burnsideF4m_centerOf_perfectCore_MiTwo (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) :
    centerOf (perfectCore (MiTwo β ε)) =
      subImg (burnsideF4d_bTwo β ε) (centerOf (perfectCore M₂)) := by
  have hb := burnsideF4j_bTwo_injective hyp
  rw [burnsideF4d_MiTwo_eq, subImg_perfectCore hb le_rfl,
    subImg_centerOf hb (perfectCore_le M₂)]

theorem burnsideF4m_cent_MiOne (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL3 : κ ≠ .L3)
    (hZ1 : ∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)))
    {x : M} (hx : x ∈ centerOf (perfectCore (MiOne β ε))) (hx2 : orderOf x = 2) :
    Subgroup.centralizer ({x} : Set M) ≤ MiOne β ε := by
  have hb := burnsideF4j_bOne_injective hyp
  rw [burnsideF4m_centerOf_perfectCore_MiOne hyp] at hx
  obtain ⟨y, hyN, hyZ, rfl⟩ := mem_subImg.mp hx
  have hy1 : y ≠ 1 := by
    rintro rfl
    have : burnsideF4d_bOne β ε ⟨1, hyN⟩ = 1 := map_one _
    rw [this, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  have hy2 : y * y = 1 := by
    have h1 : orderOf y = 2 := (orderOf_img hb hyN).symm.trans hx2
    have := pow_orderOf_eq_one y
    rw [h1, pow_two] at this
    exact this
  have hyZ1 : y ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) := hZ1 y hyZ hy1 hy2
  have hw : burnsideF4d_bOne β ε ⟨y, hyN⟩ ∈ ctr (oPPrime 2 (GiOne Gp β ε)) := by
    rw [burnsideF4j_Z1_eq hyp]
    exact mem_subImg_of_mem _ hyN hyZ1
  have hw1 : burnsideF4d_bOne β ε ⟨y, hyN⟩ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  exact burnsideF4j_centralizer_Z1_le hyp hL3 hw hw1

theorem burnsideF4m_no_inv_MiTwo (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hSp : κ ≠ .Sp4)
    (hZ2 : ∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      κ = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂)))
    {x : M} (hx : x ∈ centerOf (perfectCore (MiTwo β ε))) (hx2 : orderOf x = 2) : False := by
  have hb := burnsideF4j_bTwo_injective hyp
  rw [burnsideF4m_centerOf_perfectCore_MiTwo hyp] at hx
  obtain ⟨y, hyN, hyZ, rfl⟩ := mem_subImg.mp hx
  have hy1 : y ≠ 1 := by
    rintro rfl
    have : burnsideF4d_bTwo β ε ⟨1, hyN⟩ = 1 := map_one _
    rw [this, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  have hy2 : y * y = 1 := by
    have h1 : orderOf y = 2 := (orderOf_img hb hyN).symm.trans hx2
    have := pow_orderOf_eq_one y
    rw [h1, pow_two] at this
    exact this
  exact hSp (hZ2 y hyZ hy1 hy2).1

theorem burnsideF4m_cent_MiTwo (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z)
    (hZ2 : ∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      GLKind.Sp4 = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂)))
    {x : M} (hx : x ∈ centerOf (perfectCore (MiTwo β ε))) (hx2 : orderOf x = 2) :
    Subgroup.centralizer ({x} : Set M) ≤ MiTwo β ε := by
  have hb := burnsideF4j_bTwo_injective hyp
  rw [burnsideF4m_centerOf_perfectCore_MiTwo hyp] at hx
  obtain ⟨y, hyN, hyZ, rfl⟩ := mem_subImg.mp hx
  have hy1 : y ≠ 1 := by
    rintro rfl
    have : burnsideF4d_bTwo β ε ⟨1, hyN⟩ = 1 := map_one _
    rw [this, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  have hy2 : y * y = 1 := by
    have h1 : orderOf y = 2 := (orderOf_img hb hyN).symm.trans hx2
    have := pow_orderOf_eq_one y
    rw [h1, pow_two] at this
    exact this
  have hyZ2 : y ∈ ctr (oPPrime 2 (Gp ⊓ M₂)) := (hZ2 y hyZ hy1 hy2).2
  have hw : burnsideF4d_bTwo β ε ⟨y, hyN⟩ ∈ ctr (oPPrime 2 (GiTwo Gp β ε)) := by
    rw [burnsideF4j_Z2_eq hyp]
    exact mem_subImg_of_mem _ hyN hyZ2
  have hw1 : burnsideF4d_bTwo β ε ⟨y, hyN⟩ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  exact (hyp.hc rfl).1 _ hw hw1

theorem burnsideF4m_centerOf_pCore_MiOne (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z)
    (hQ : pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁)) :
    centerOf (pCoreOf 2 (MiOne β ε)) = ctr (pCoreOf 2 (GiOne Gp β ε)) := by
  have hb := burnsideF4j_bOne_injective hyp
  rw [burnsideF4d_MiOne_eq, subImg_pCoreOf hb le_rfl, hQ, burnsideF4d_GiOne_eq,
    subImg_pCoreOf hb inf_le_right]
  rfl

theorem burnsideF4m_centerOf_pCore_MiTwo (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z)
    (hQ : pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂)) :
    centerOf (pCoreOf 2 (MiTwo β ε)) = ctr (pCoreOf 2 (GiTwo Gp β ε)) := by
  have hb := burnsideF4j_bTwo_injective hyp
  rw [burnsideF4d_MiTwo_eq, subImg_pCoreOf hb le_rfl, hQ, burnsideF4d_GiTwo_eq,
    subImg_pCoreOf hb inf_le_right]
  rfl

theorem burnsideF4m_charTwo_of_fstar {H : Subgroup M} [Finite M] (h : FstarEqO2 H) :
    CharTwo H := by
  rintro y ⟨hyH, hyc⟩
  have hc : (⟨y, hyH⟩ : ↥H) ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥H : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : (w : M) ∈ pCoreOf 2 H := by
      rw [← h]
      exact Subgroup.mem_map_of_mem _ hw
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hyc) _ hw')
  have := CFSG.centralizer_generalizedFitting_le ↥H hc
  rw [← h]
  exact ⟨_, this, rfl⟩

end GLevel


section KLevel

set_option linter.unusedSectionVars false


variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

@[expose] noncomputable def burnsideF4m_psi {K' : Type} [Group K'] (θ : E ≃* K') {N : Subgroup K'}
    {P : Subgroup E} (h : ∀ e, θ e ∈ N ↔ e ∈ P) : ↥N →* ↥P :=
  ((θ.symm.toMonoidHom).comp N.subtype).codRestrict P (fun x => by
    have hx := (h (θ.symm x)).1
    simp only [MulEquiv.apply_symm_apply] at hx
    exact hx x.2)

theorem burnsideF4m_psi_apply {K' : Type} [Group K'] (θ : E ≃* K') {N : Subgroup K'}
    {P : Subgroup E} (h : ∀ e, θ e ∈ N ↔ e ∈ P) (x : ↥N) :
    ((burnsideF4m_psi θ h x : ↥P) : E) = θ.symm x := rfl

theorem burnsideF4m_psi_injective {K' : Type} [Group K'] (θ : E ≃* K') {N : Subgroup K'}
    {P : Subgroup E} (h : ∀ e, θ e ∈ N ↔ e ∈ P) : Function.Injective (burnsideF4m_psi θ h) := by
  intro x y hxy
  have := congrArg Subtype.val hxy
  rw [burnsideF4m_psi_apply, burnsideF4m_psi_apply] at this
  exact Subtype.ext (θ.symm.injective this)

theorem burnsideF4m_psi_surjective {K' : Type} [Group K'] (θ : E ≃* K') {N : Subgroup K'}
    {P : Subgroup E} (h : ∀ e, θ e ∈ N ↔ e ∈ P) : Function.Surjective (burnsideF4m_psi θ h) := by
  intro p
  refine ⟨⟨θ p, (h p).2 p.2⟩, Subtype.ext ?_⟩
  rw [burnsideF4m_psi_apply]
  simp

theorem burnsideF4m_bOne_eq_bTwo (β : Cpl M₁ M₂ Y) (ε : Y →* M) (x : E) (h1 : x ∈ M₁)
    (h2 : x ∈ M₂) : burnsideF4d_bOne β ε ⟨x, h1⟩ = burnsideF4d_bTwo β ε ⟨x, h2⟩ := by
  have e1 : β.φ1 (⟨x, h1⟩ : ↥M₁) = β.φ2 (⟨x, h2⟩ : ↥M₂) := by
    have a1 := β.comm1 (⟨x, h1, h2⟩ : ↥(M₁ ⊓ M₂))
    have a2 := β.comm2 (⟨x, h1, h2⟩ : ↥(M₁ ⊓ M₂))
    exact a1.trans a2.symm
  show epsG β ε (f1 (c := β) ⟨x, h1⟩) = epsG β ε (f2 (c := β) ⟨x, h2⟩)
  congr 1
  exact Subtype.ext e1

theorem burnsideF4m_comp_data {K' : Type} [Group K'] (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z)
    (θ : E ≃* K') {N1 N2 : Subgroup K'} (h1 : ∀ e, θ e ∈ N1 ↔ e ∈ M₁)
    (h2 : ∀ e, θ e ∈ N2 ↔ e ∈ M₂) :
    F431Comp N1 N2 ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
        ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) ∧
      ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1)).range = MiOne β ε ∧
      ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)).range = MiTwo β ε ∧
      ∀ g : M, g ∈ MiOne β ε → g ∈ MiTwo β ε → ∃ n : K', ∃ (hn1 : n ∈ N1) (_ : n ∈ N2),
        ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1)) ⟨n, hn1⟩ = g := by
  have hb1 := burnsideF4j_bOne_injective hyp
  have hb2 := burnsideF4j_bTwo_injective hyp
  refine ⟨⟨hb1.comp (burnsideF4m_psi_injective θ h1), hb2.comp (burnsideF4m_psi_injective θ h2),
    fun g hg1 hg2 => ?_⟩, ?_, ?_, ?_⟩
  · show burnsideF4d_bOne β ε (burnsideF4m_psi θ h1 ⟨g, hg1⟩) =
      burnsideF4d_bTwo β ε (burnsideF4m_psi θ h2 ⟨g, hg2⟩)
    have e1 : burnsideF4m_psi θ h1 ⟨g, hg1⟩ = ⟨θ.symm g, (burnsideF4m_psi θ h1 ⟨g, hg1⟩).2⟩ := rfl
    have e2 : burnsideF4m_psi θ h2 ⟨g, hg2⟩ = ⟨θ.symm g, (burnsideF4m_psi θ h2 ⟨g, hg2⟩).2⟩ := rfl
    rw [e1, e2]
    exact burnsideF4m_bOne_eq_bTwo β ε _ _ _
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (burnsideF4m_psi_surjective θ h1),
      ← MonoidHom.range_eq_map, burnsideF4d_MiOne_eq, subImg_self]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (burnsideF4m_psi_surjective θ h2),
      ← MonoidHom.range_eq_map, burnsideF4d_MiTwo_eq, subImg_self]
  · intro g hg1 hg2
    have hg : g ∈ MiOne β ε ⊓ MiTwo β ε := ⟨hg1, hg2⟩
    rw [burnsideF4d_inter_eq β hyp.faithful ε hyp.inj] at hg
    obtain ⟨e, he1, ⟨-, he2⟩, rfl⟩ := mem_subImg.mp hg
    refine ⟨θ e, (h1 e).2 he1, (h2 e).2 he2, ?_⟩
    show burnsideF4d_bOne β ε (burnsideF4m_psi θ h1 ⟨θ e, (h1 e).2 he1⟩) = _
    congr 1
    exact Subtype.ext (by rw [burnsideF4m_psi_apply]; simp)

theorem burnsideF4m_exists_theta [Finite E] (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {TD : Subgroup ↥Gp}
    (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp)) :
    ∃ θ : E ≃* ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K,
      (∀ e, θ e ∈ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb1 ↔ e ∈ M₁) ∧
      (∀ e, θ e ∈ (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).Mb2 ↔ e ∈ M₂) := by
  haveI := hyp.normal
  have hinj : Function.Injective (burnsideF4d_rho Gp) :=
    burnsideF4d_rho_injective hyp.centralizer_trivial
  have hK : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K = (burnsideF4d_rho Gp).range :=
    burnsideF4d_K_eq hyp.toHypF_4_4g hyam
  let θ : E ≃* ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hK.symm)
  have hθ : ∀ e : E, ((θ e : ↥(burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).K) : MulAut ↥Gp) =
      burnsideF4d_rho Gp e := fun e => rfl
  have hN1 : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).N1 = M₁.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N1_eq hyp.toHypF_4_4g hyam
  have hN2 : (burnsideF4d_lieExtE hyp.toHypF_4_4g hyam).N2 = M₂.map (burnsideF4d_rho Gp) :=
    burnsideF4d_N2_eq hyp.toHypF_4_4g hyam
  refine ⟨θ, fun e => ?_, fun e => ?_⟩
  · rw [Subgroup.mem_subgroupOf, hθ, hN1]
    constructor
    · rintro ⟨e', he', hee'⟩
      rw [← hinj hee']
      exact he'
    · intro he
      exact ⟨e, he, rfl⟩
  · rw [Subgroup.mem_subgroupOf, hθ, hN2]
    constructor
    · rintro ⟨e', he', hee'⟩
      rw [← hinj hee']
      exact he'
    · intro he
      exact ⟨e, he, rfl⟩

theorem burnsideF4m_hres (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) :
    oTwoRes (⊤ : Subgroup M) = ⊤ :=
  hyp.he.resolve_right fun h => by have := h.1; omega

theorem burnsideF4m_false_of_twoOut [Finite E] (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hf : 2 ≤ f)
    (hL3 : κ ≠ .L3) (hSp : κ ≠ .Sp4)
    (hZ1 : ∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)))
    (hZ2 : ∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      κ = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂)))
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp))
    (hO : ∃ (T S : Subgroup ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K)
      (g z' : ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K)
      (I : Finset ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K),
      F431TwoOut T S g (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb1
          (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb2 z' I ∨
        F431TwoOut T S g (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb2
          (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb1 z' I) : False := by
  haveI := hyp.finite_M
  obtain ⟨θ, h1, h2⟩ := burnsideF4m_exists_theta hyp.amalgam hyam
  haveI : Finite ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K :=
    Finite.of_equiv E θ.toEquiv
  obtain ⟨hC, hr1, hr2, -⟩ := burnsideF4m_comp_data hyp θ h1 h2
  obtain ⟨T, S, g, z', I, hO | hO⟩ := hO
  · exact burnsideF4m_TwoGSetup_out_false (burnsideF4m_hres hyp hf)
      ⟨hC, hr1, fun x hx hx2 => burnsideF4m_cent_MiOne hyp hL3 hZ1 hx hx2⟩ hO
  · have hzN : z' ∈ (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb2 := hO.T_le hO.z_mem
    have hmem := map_mem_centerOf_perfectCore hC.inj₂ hr2 hzN hO.z_ZN
    exact burnsideF4m_no_inv_MiTwo hyp hSp hZ2 hmem ((orderOf_img hC.inj₂ hzN).trans hO.z_two)

theorem burnsideF4m_false_of_unOut [Finite E] (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hf : 2 ≤ f)
    (hU : κ = .U4 ∨ κ = .U5)
    (hZ1 : ∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)))
    (hZ2 : ∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      κ = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂)))
    (hQ2 : pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂))
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp))
    (hO : ∃ (T S : Subgroup ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K)
      (g z' t : ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K)
      (V : Subgroup ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K),
      Un.F431UnOut T S g (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb1
          (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb2 z' t V ∨
        Un.F431UnOut T S g (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb2
          (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb1 z' t V) : False := by
  haveI := hyp.finite_M
  have hL3 : κ ≠ .L3 := by rcases hU with rfl | rfl <;> decide
  have hSp : κ ≠ .Sp4 := by rcases hU with rfl | rfl <;> decide
  obtain ⟨θ, h1, h2⟩ := burnsideF4m_exists_theta hyp.amalgam hyam
  haveI : Finite ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K :=
    Finite.of_equiv E θ.toEquiv
  obtain ⟨hC, hr1, hr2, -⟩ := burnsideF4m_comp_data hyp θ h1 h2
  obtain ⟨T, S, g, z', t, V, hO | hO⟩ := hO
  · refine Un.burnsideF4m_UnGSetup_out_false (burnsideF4m_hres hyp hf)
      ⟨hC, hr1, hr2, fun x hx hx2 => burnsideF4m_cent_MiOne hyp hL3 hZ1 hx hx2, ?_⟩ hO
    rw [burnsideF4m_centerOf_pCore_MiTwo hyp hQ2]
    exact (hyp.ha (Or.inr hU)).2
  · have hzN : z' ∈ (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb2 :=
      hO.T_le (hO.S_le hO.z_mem)
    have hmem := map_mem_centerOf_perfectCore hC.inj₂ hr2 hzN hO.z_ZN
    exact burnsideF4m_no_inv_MiTwo hyp hSp hZ2 hmem ((orderOf_img hC.inj₂ hzN).trans hO.z_two)

theorem burnsideF4m_false_of_spOut [Finite E] (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z)
    (hf : 2 ≤ f)
    (hZ1 : ∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)))
    (hZ2 : ∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      GLKind.Sp4 = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂)))
    (hQ1 : pCoreOf 2 M₁ = pCoreOf 2 (Gp ⊓ M₁)) (hQ2 : pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂))
    (hQ12 : pCoreOf 2 (M₁ ⊓ M₂) = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    {TD : Subgroup ↥Gp} (hyam : IsYAmalgamPair TD (M₁.subgroupOf Gp) (M₂.subgroupOf Gp))
    (hO : (∃ (T S : Subgroup ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K)
      (g : ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K)
      (I : Finset ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K),
      F431SpOut T S g (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb1
          (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb2 I) ∨
      (∃ (T S : Subgroup ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K)
        (g : ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K)
        (I : Finset ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K)
        (i0 i1 : ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K),
        F431SpOut4 T S g (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb1
          (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb2 I i0 i1)) : False := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.normal
  obtain ⟨θ, h1, h2⟩ := burnsideF4m_exists_theta hyp.amalgam hyam
  haveI : Finite ↥(burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).K :=
    Finite.of_equiv E θ.toEquiv
  obtain ⟨hC, hr1, hr2, hint⟩ := burnsideF4m_comp_data hyp θ h1 h2
  have hle : pCoreOf 2 (M₁ ⊓ M₂) ≤ Gp := by
    rw [hQ12]
    exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hSinM : SinM Gp β ε = pCoreOf 2 (MiOne β ε ⊓ MiTwo β ε) :=
    burnsideF4d_SinM_eq_pCore Gp β hyp.faithful ε hyp.inj hle
  have hS : SpGSetup (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb1
      (burnsideF4d_lieExtE hyp.amalgam.toHypF_4_4g hyam).Mb2
      ((burnsideF4d_bOne β ε).comp (burnsideF4m_psi θ h1))
      ((burnsideF4d_bTwo β ε).comp (burnsideF4m_psi θ h2)) (MiOne β ε) (MiTwo β ε) := by
    refine ⟨hC, hr1, hr2, hint, ?_, ?_, fun x hx hx2 => burnsideF4m_cent_MiOne hyp (by decide)
      hZ1 hx hx2, fun x hx hx2 => burnsideF4m_cent_MiTwo hyp hZ2 hx hx2, ?_, ?_⟩
    · rw [burnsideF4m_centerOf_pCore_MiOne hyp hQ1]
      exact (hyp.ha (Or.inl rfl)).1
    · rw [burnsideF4m_centerOf_pCore_MiTwo hyp hQ2]
      exact (hyp.ha (Or.inl rfl)).2
    · intro u hu hu2
      have hu' : u ∈ ctr (SinM Gp β ε) := by rw [hSinM]; exact hu
      have hu1 : u ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hu2
        exact absurd hu2 (by decide)
      have huu : u * u = 1 := by
        have := pow_orderOf_eq_one u
        rw [hu2, pow_two] at this
        exact this
      exact burnsideF4m_charTwo_of_fstar ((hyp.hc rfl).2 u hu' hu1 huu)
    · intro h
      exact (Nat.not_even_iff_odd.mpr (hyp.hd rfl)) (even_iff_two_dvd.mpr h)
  rcases hO with ⟨T, S, g, I, hO⟩ | ⟨T, S, g, I, i0, i1, hO⟩
  · exact burnsideF4m_SpGSetup_out_false (burnsideF4m_hres hyp hf) hS hO
  · exact burnsideF4m_SpGSetup_out_false4 (burnsideF4m_hres hyp hf) hS hO

end KLevel


section Kinds

set_option linter.unusedSectionVars false


variable {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
  {β : Cpl M₁ M₂ Y} {M : Type} [Group M] {ε : Y →* M} {z : M}

theorem burnsideF4m_odd_index_G2_lie (hlie : burnsideF4m_LieCoreInput)
    (hyp : HypF_4_31 .G2 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) : Odd Gp.index := by
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  by_contra hodd
  obtain ⟨hZ1, hZ2⟩ := hlie.1 _ f E Gp M₁ M₂ hyp.amalgam hf (Or.inl rfl) hodd
  obtain ⟨K, fK, finK, hcard, marking, h1, h2⟩ := burnsideF4g_chart_G2 hyp.amalgam.toHypF_4_4g
  letI := fK
  haveI := finK
  haveI : CharP K 2 := burnsideF4f_charP_of_card (by omega) hcard
  have hK3 : 3 ≤ Nat.card K := by
    rw [hcard]
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamG2 hK3 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_G2 hf hyp.amalgam.model
  exact burnsideF4m_false_of_twoOut hyp hf (by decide) (by decide) hZ1 hZ2 hTD
    (G2.f431TwoOutLieProp_g2 f ↥Gp hmodel _ (burnsideF4m_not_odd hyp.amalgam hTD hodd))

theorem burnsideF4m_odd_index_D4tw_lie (hlie : burnsideF4m_LieCoreInput)
    (hyp : HypF_4_31 .D4tw f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) : Odd Gp.index := by
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  by_contra hodd
  obtain ⟨hZ1, hZ2⟩ := hlie.1 _ f E Gp M₁ M₂ hyp.amalgam hf (Or.inr rfl) hodd
  obtain ⟨K, fK, finK, sigma, hscope, marking, h1, h2⟩ :=
    burnsideF4g_chart_D4tw hyp.amalgam.toHypF_4_4g
  letI := fK
  haveI := finK
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamD4 sigma hscope marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_D4tw hyp.amalgam.model
  exact burnsideF4m_false_of_twoOut hyp hf (by decide) (by decide) hZ1 hZ2 hTD
    (D4q.f431TwoOutLieProp_d4q f (by omega) ↥Gp hmodel _
      (burnsideF4m_not_odd hyp.amalgam hTD hodd))

theorem burnsideF4m_odd_index_U4_lie (hlie : burnsideF4m_LieCoreInput)
    (hyp : HypF_4_31 .U4 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) : Odd Gp.index := by
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  by_contra hodd
  obtain ⟨hZ1, hZ2, hQ2⟩ := hlie.2.1 _ f E Gp M₁ M₂ hyp.amalgam hf (Or.inl rfl) hodd
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.amalgam.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU4 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U4 hyp.amalgam.model
  exact burnsideF4m_false_of_unOut hyp hf (Or.inl rfl) hZ1 hZ2 hQ2 hTD
    (Un.f431UnOutLieProp_four f hf ↥Gp hmodel _ (burnsideF4m_not_odd hyp.amalgam hTD hodd))

theorem burnsideF4m_odd_index_U5_lie (hlie : burnsideF4m_LieCoreInput)
    (hyp : HypF_4_31 .U5 2 Gp M₁ M₂ β ε z) : Odd Gp.index := by
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  by_contra hodd
  obtain ⟨hZ1, hZ2, hQ2⟩ := hlie.2.1 _ 2 E Gp M₁ M₂ hyp.amalgam le_rfl (Or.inr rfl) hodd
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.amalgam.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamU5 marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_U5 hyp.amalgam.model
  exact burnsideF4m_false_of_unOut hyp le_rfl (Or.inr rfl) hZ1 hZ2 hQ2 hTD
    (Un.f431UnOutLieProp_five ↥Gp hmodel _ (burnsideF4m_not_odd hyp.amalgam hTD hodd))

theorem burnsideF4m_odd_index_Sp4_lie (hlie : burnsideF4m_LieCoreInput)
    (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) (hf : 2 ≤ f) : Odd Gp.index := by
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  by_contra hodd
  obtain ⟨hZ1, hZ2, hQ1, hQ2, hQ12⟩ := hlie.2.2 f E Gp M₁ M₂ hyp.amalgam hf hodd
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp.amalgam.toHypF_4_4g
  obtain ⟨TD, hTD⟩ := burnsideF4g_yamSp4 hf marking
  rw [← h1, ← h2] at hTD
  have hmodel := burnsideF4g_lieModel_Sp4 hf hyp.amalgam.model
  have hnodd := burnsideF4m_not_odd hyp.amalgam hTD hodd
  refine burnsideF4m_false_of_spOut hyp hf hZ1 hZ2 hQ1 hQ2 hQ12 hTD ?_
  by_cases hf2 : f = 2
  · subst hf2
    exact Or.inr (f431SpOut4Lie ↥Gp hmodel _ hnodd)
  · exact Or.inl (f431SpOutLieProp (by omega) ↥Gp hmodel _ hnodd)

@[expose] def burnsideF4m_OddIndexSmall : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M →
    ((κ = .Sp4 ∧ f = 1) ∨ (κ = .U4 ∧ f = 1) ∨ (κ = .U5 ∧ f ≠ 2)) → Odd Gp.index

theorem burnsideF4m_oddIndexInputRest_of_lie (hlie : burnsideF4m_LieCoreInput)
    (hsmall : burnsideF4m_OddIndexSmall) : burnsideF4m_OddIndexInputRest := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hκ
  rcases hκ with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | rfl | rfl
  · have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
    rcases hf with hf | hf
    · exact burnsideF4m_odd_index_Sp4_lie hlie hyp (by obtain ⟨k, rfl⟩ := hf; omega)
    · exact hsmall _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inl ⟨rfl, hf⟩)
  · have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
    exact burnsideF4m_odd_index_G2_lie hlie hyp (by obtain ⟨k, rfl⟩ := hf; omega)
  · have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
    exact burnsideF4m_odd_index_D4tw_lie hlie hyp (by obtain ⟨k, rfl⟩ := hf; omega)
  · have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
    by_cases hf2 : 2 ≤ f
    · exact burnsideF4m_odd_index_U4_lie hlie hyp hf2
    · exact hsmall _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inr (Or.inl ⟨rfl, by omega⟩))
  · by_cases hf2 : f = 2
    · subst hf2
      exact burnsideF4m_odd_index_U5_lie hlie hyp
    · exact hsmall _ f E Gp M₁ M₂ Y β M ε z hyp hL43 (Or.inr (Or.inr ⟨rfl, hf2⟩))

theorem burnsideF4m_F_4_38_of_lie (hlie : burnsideF4m_LieCoreInput)
    (hsmall : burnsideF4m_OddIndexSmall) : F_4_38 :=
  burnsideF4m_F_4_38_of_rest (burnsideF4m_oddIndexInputRest_of_lie hlie hsmall)

end Kinds

end CFSG.ASVolI
