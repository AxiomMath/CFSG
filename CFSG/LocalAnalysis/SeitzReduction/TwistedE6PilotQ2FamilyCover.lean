module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup

section Cover

variable {G M : Type*} [Group G] [Group M]

structure QCover (G M : Type*) [Group G] [Group M] where
  E : Subgroup G
  p : E →* M
  ker_le : p.ker ≤ center E

@[expose] def QCover.IsSection (c : QCover G M) {H : Subgroup M} (s : H →* G) : Prop :=
  ∀ h : H, ∃ z : c.E, (z : G) = s h ∧ c.p z = h

theorem QCover.IsSection.mem {c : QCover G M} {H : Subgroup M} {s : H →* G} (hs : c.IsSection s)
    (h : H) : s h ∈ c.E := by
  obtain ⟨z, hz, -⟩ := hs h
  exact hz ▸ z.2

theorem QCover.IsSection.p_apply {c : QCover G M} {H : Subgroup M} {s : H →* G}
    (hs : c.IsSection s) (h : H) : c.p ⟨s h, hs.mem h⟩ = h := by
  obtain ⟨z, hz, hpz⟩ := hs h
  have : (⟨s h, hs.mem h⟩ : c.E) = z := Subtype.ext hz.symm
  rw [this, hpz]

theorem QCover.IsSection.restrict {c : QCover G M} {H : Subgroup M} {s : H →* G}
    (hs : c.IsSection s) {H' : Subgroup M} (hH : H' ≤ H) :
    c.IsSection (s.comp (Subgroup.inclusion hH)) := fun h => hs (Subgroup.inclusion hH h)

@[expose] def QCover.IsSection.toE {c : QCover G M} {H : Subgroup M} {s : H →* G}
    (hs : c.IsSection s) : H →* c.E :=
  s.codRestrict c.E hs.mem

theorem QCover.IsSection.coe_toE {c : QCover G M} {H : Subgroup M} {s : H →* G}
    (hs : c.IsSection s) (h : H) : ((hs.toE h : c.E) : G) = s h :=
  rfl

theorem QCover.IsSection.p_toE {c : QCover G M} {H : Subgroup M} {s : H →* G}
    (hs : c.IsSection s) (h : H) : c.p (hs.toE h) = h :=
  hs.p_apply h

theorem QCover.IsSection.eq_of_perfect {c : QCover G M} {H : Subgroup M} (hH : ⁅H, H⁆ = H)
    {s s' : H →* G} (hs : c.IsSection s) (hs' : c.IsSection s') : s = s' := by
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  have heq : hs.toE = hs'.toE := LinearPilot.eq_of_comp_eq_of_ker_le_center c.ker_le fun h => by
    rw [hs.p_toE, hs'.p_toE]
  ext h
  exact congrArg Subtype.val (DFunLike.congr_fun heq h)

theorem QCover.IsSection.mem_centralizer {c : QCover G M} {H : Subgroup M} (hH : ⁅H, H⁆ = H)
    {s : H →* G} (hs : c.IsSection s) {X : Subgroup G} (hXE : X ≤ c.E)
    (hXH : ∀ x (hx : x ∈ X) (h : H), Commute (c.p ⟨x, hXE hx⟩) (h : M)) (h : H) :
    s h ∈ centralizer (X : Set G) := by
  have : Group.IsPerfect H := Subgroup.isPerfect_iff.mpr hH
  rw [mem_centralizer_iff]
  intro x hx
  set xe : c.E := ⟨x, hXE hx⟩ with hxe
  have heq : hs.toE = (MulAut.conj xe).toMonoidHom.comp hs.toE :=
    LinearPilot.eq_of_comp_eq_of_ker_le_center c.ker_le fun h' => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv, hs.p_toE]
      rw [(hXH x hx h').eq, mul_inv_cancel_right]
  have h1 := congrArg Subtype.val (DFunLike.congr_fun heq h)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_mul, Subgroup.coe_inv, hs.coe_toE] at h1
  rw [eq_mul_inv_iff_mul_eq] at h1
  exact h1.symm

end Cover

section Param

variable {G M S : Type*} [Group G] [Group M] [Group S]

@[expose] noncomputable def QCover.ofParam (Φ : S →* G) (ρ : S →* M) (hker : Φ.ker ≤ ρ.ker)
    (hZ : ρ.ker ≤ center S) : QCover G M where
  E := Φ.range
  p := (QuotientGroup.lift Φ.ker ρ hker).comp
    (QuotientGroup.quotientKerEquivRange Φ).symm.toMonoidHom
  ker_le := by
    rintro ⟨_, x, rfl⟩ hx
    have hx' : ρ x = 1 := by
      have h1 : (QuotientGroup.quotientKerEquivRange Φ).symm ⟨Φ x, x, rfl⟩ =
          (x : S ⧸ Φ.ker) := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1] at hx
      exact hx
    have hxZ := mem_center_iff.1 (hZ hx')
    rw [mem_center_iff]
    rintro ⟨_, y, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, hxZ y]

theorem QCover.ofParam_p (Φ : S →* G) (ρ : S →* M) (hker : Φ.ker ≤ ρ.ker)
    (hZ : ρ.ker ≤ center S) (x : S) (h : Φ x ∈ (QCover.ofParam Φ ρ hker hZ).E) :
    (QCover.ofParam Φ ρ hker hZ).p ⟨Φ x, h⟩ = ρ x := by
  have h1 : (QuotientGroup.quotientKerEquivRange Φ).symm ⟨Φ x, h⟩ = (x : S ⧸ Φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change (QuotientGroup.lift Φ.ker ρ hker)
    ((QuotientGroup.quotientKerEquivRange Φ).symm ⟨Φ x, h⟩) = ρ x
  rw [h1]
  rfl

theorem QCover.exists_isSection_ofParam (Φ : S →* G) (ρ : S →* M) (hker : Φ.ker ≤ ρ.ker)
    (hZ : ρ.ker ≤ center S) {T : Subgroup S} (hinj : Function.Injective (ρ.comp T.subtype))
    {H : Subgroup M} (hH : H ≤ T.map ρ) :
    ∃ s : H →* G, (QCover.ofParam Φ ρ hker hZ).IsSection s ∧
      ∀ h : H, ∃ x ∈ T, ρ x = h ∧ s h = Φ x := by
  have hrange : (ρ.comp T.subtype).range = T.map ρ := by
    rw [MonoidHom.range_comp, range_subtype]
  set eT := MonoidHom.ofInjective hinj with heT
  let ι : H →* (ρ.comp T.subtype).range :=
    Subgroup.inclusion (hH.trans hrange.symm.le)
  let s : H →* G := Φ.comp (T.subtype.comp (eT.symm.toMonoidHom.comp ι))
  have hval : ∀ h : H, ρ ((eT.symm (ι h) : T) : S) = h := fun h => by
    have h1 := eT.apply_symm_apply (ι h)
    have h2 := congrArg Subtype.val h1
    rw [heT, MonoidHom.ofInjective_apply] at h2
    exact h2
  refine ⟨s, fun h => ⟨⟨Φ ((eT.symm (ι h) : T) : S), (show Φ _ ∈ Φ.range from ⟨_, rfl⟩)⟩, rfl, ?_⟩,
    fun h => ⟨_, (eT.symm (ι h)).2, hval h, rfl⟩⟩
  exact (QCover.ofParam_p Φ ρ hker hZ _ _).trans (hval h)

end Param

section Twist

variable {G M : Type*} [Group G] [Group M]

@[expose] def QCover.TwistOn (c c' : QCover G M) (Q : Subgroup G) (ε : M →* M) : Prop :=
  ∃ (hQ : Q ≤ c.E) (hQ' : Q ≤ c'.E), ∀ y (hy : y ∈ Q), c'.p ⟨y, hQ' hy⟩ = ε (c.p ⟨y, hQ hy⟩)

theorem QCover.TwistOn.apply {c c' : QCover G M} {Q : Subgroup G} {ε : M →* M}
    (h : c.TwistOn c' Q ε) {y : G} (hy : y ∈ Q) (hyE : y ∈ c.E) (hyE' : y ∈ c'.E) :
    c'.p ⟨y, hyE'⟩ = ε (c.p ⟨y, hyE⟩) := by
  obtain ⟨hQ, hQ', h⟩ := h
  exact h y hy

theorem QCover.TwistOn.mono {c c' : QCover G M} {Q Q' : Subgroup G} {ε : M →* M}
    (h : c.TwistOn c' Q ε) (hQQ : Q' ≤ Q) : c.TwistOn c' Q' ε := by
  obtain ⟨hQ, hQ', h⟩ := h
  exact ⟨hQQ.trans hQ, hQQ.trans hQ', fun y hy => h y (hQQ hy)⟩

theorem QCover.TwistOn.trans {c c' c'' : QCover G M} {Q : Subgroup G} {ε ε' : M →* M}
    (h : c.TwistOn c' Q ε) (h' : c'.TwistOn c'' Q ε') : c.TwistOn c'' Q (ε'.comp ε) := by
  obtain ⟨hQ, hQ', h₁⟩ := h
  obtain ⟨_, hQ'', h₂⟩ := h'
  exact ⟨hQ, hQ'', fun y hy => by rw [h₂ y hy, MonoidHom.comp_apply, ← h₁ y hy]⟩

theorem QCover.TwistOn.le_left {c c' : QCover G M} {Q : Subgroup G} {ε : M →* M}
    (h : c.TwistOn c' Q ε) : Q ≤ c.E :=
  h.1

theorem QCover.TwistOn.le_right {c c' : QCover G M} {Q : Subgroup G} {ε : M →* M}
    (h : c.TwistOn c' Q ε) : Q ≤ c'.E :=
  h.2.1

theorem QCover.TwistOn.congr_fun {c c' : QCover G M} {Q : Subgroup G} {ε ε' : M →* M}
    (h : c.TwistOn c' Q ε) (hε : ∀ x, ε x = ε' x) : c.TwistOn c' Q ε' := by
  obtain ⟨hQ, hQ', h₁⟩ := h
  exact ⟨hQ, hQ', fun y hy => by rw [h₁ y hy, hε]⟩

theorem QCover.TwistOn.symm {c c' : QCover G M} {Q : Subgroup G} {ε ε' : M →* M}
    (h : c.TwistOn c' Q ε) (hε : ∀ x, ε' (ε x) = x) : c'.TwistOn c Q ε' := by
  obtain ⟨hQ, hQ', h⟩ := h
  exact ⟨hQ', hQ, fun y hy => by rw [h y hy, hε]⟩

theorem QCover.IsSection.of_twistOn {c c' : QCover G M} {Q : Subgroup G}
    (hagr : c.TwistOn c' Q (MonoidHom.id M)) {H : Subgroup M} {s : H →* G} (hs : c.IsSection s)
    (hsQ : ∀ h, s h ∈ Q) : c'.IsSection s := by
  obtain ⟨hE, hE', heq⟩ := hagr
  intro h
  refine ⟨⟨s h, hE' (hsQ h)⟩, rfl, ?_⟩
  rw [heq _ (hsQ h), MonoidHom.id_apply]
  exact hs.p_apply h

theorem QCover.exists_mulEquiv_of_overlap {c c' : QCover G M} {Q : Subgroup G} (hQ : Q ≤ c.E)
    (hQ' : Q ≤ c'.E) {Λ : Subgroup M} (hZ : center Λ = ⊥)
    (hpQ : ∀ y (hy : y ∈ Q), c.p ⟨y, hQ hy⟩ ∈ Λ) (hpQ' : ∀ y (hy : y ∈ Q), c'.p ⟨y, hQ' hy⟩ ∈ Λ)
    {s s' : Λ →* G} (hs : c.IsSection s) (hs' : c'.IsSection s') (hsQ : ∀ h, s h ∈ Q)
    (hs'Q : ∀ h, s' h ∈ Q) :
    ∃ τ : Λ ≃* Λ, ∀ y (hy : y ∈ Q), c'.p ⟨y, hQ' hy⟩ = τ ⟨c.p ⟨y, hQ hy⟩, hpQ y hy⟩ := by
  let τ₀ : Λ →* Λ := (c'.p.comp (s.codRestrict c'.E fun h => hQ' (hsQ h))).codRestrict Λ
    (fun h => hpQ' _ (hsQ h))
  have hτ₀ : ∀ h, (τ₀ h : M) = c'.p ⟨s h, hQ' (hsQ h)⟩ := fun h => rfl
  have hcen : ∀ w (hw : w ∈ Q), (∀ q ∈ Q, q * w = w * q) → c'.p ⟨w, hQ' hw⟩ = 1 := by
    intro w hw hcomm
    have hmem : (⟨c'.p ⟨w, hQ' hw⟩, hpQ' w hw⟩ : Λ) ∈ center Λ := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hs'.p_apply g, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm _ (hs'Q g))
    rw [hZ, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hkey : ∀ y (hy : y ∈ Q), c'.p ⟨y, hQ' hy⟩ = τ₀ ⟨c.p ⟨y, hQ hy⟩, hpQ y hy⟩ := by
    intro y hy
    set h : Λ := ⟨c.p ⟨y, hQ hy⟩, hpQ y hy⟩ with hhdef
    rw [hτ₀]
    have hsh : s h ∈ Q := hsQ h
    have hw : y⁻¹ * s h ∈ Q := Q.mul_mem (Q.inv_mem hy) hsh
    have hwker : (⟨y⁻¹ * s h, hQ hw⟩ : c.E) ∈ c.p.ker := by
      rw [MonoidHom.mem_ker]
      have e1 : (⟨y⁻¹ * s h, hQ hw⟩ : c.E) = (⟨y, hQ hy⟩ : c.E)⁻¹ * ⟨s h, hs.mem h⟩ := rfl
      rw [e1, map_mul, map_inv, hs.p_apply h, hhdef, inv_mul_cancel]
    have hwc := mem_center_iff.1 (c.ker_le hwker)
    have h1 := hcen _ hw fun q hq => congrArg Subtype.val (hwc ⟨q, hQ hq⟩)
    have h2 : (⟨s h, hQ' hsh⟩ : c'.E) = ⟨y, hQ' hy⟩ * ⟨y⁻¹ * s h, hQ' hw⟩ :=
      Subtype.ext (by simp)
    rw [h2, map_mul, h1, mul_one]
  have hinj : Function.Injective τ₀ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h1 : c'.p ⟨s h, hQ' (hsQ h)⟩ = 1 := congrArg Subtype.val hh
    have hcz := mem_center_iff.1 (c'.ker_le (MonoidHom.mem_ker.2 h1))
    have hmem : h ∈ center Λ := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hs.p_apply g, ← hs.p_apply h, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have h2 := congrArg Subtype.val (hcz ⟨s g, hQ' (hsQ g)⟩)
      simp only [Subgroup.coe_mul] at h2 ⊢
      exact h2
    rw [hZ, mem_bot] at hmem
    exact hmem
  have hsurj : Function.Surjective τ₀ := by
    intro g
    refine ⟨⟨c.p ⟨s' g, hQ (hs'Q g)⟩, hpQ _ (hs'Q g)⟩, Subtype.ext ?_⟩
    rw [← hkey _ (hs'Q g)]
    exact hs'.p_apply g
  exact ⟨MulEquiv.ofBijective τ₀ ⟨hinj, hsurj⟩, fun y hy => by rw [hkey y hy]; rfl⟩

theorem QCover.mulEquiv_fix_of_overlap {c c' : QCover G M} {Q : Subgroup G} (hQ : Q ≤ c.E)
    (hQ' : Q ≤ c'.E) {Λ : Subgroup M} (hpQ : ∀ y (hy : y ∈ Q), c.p ⟨y, hQ hy⟩ ∈ Λ)
    {τ : Λ ≃* Λ} (hτ : ∀ y (hy : y ∈ Q), c'.p ⟨y, hQ' hy⟩ = τ ⟨c.p ⟨y, hQ hy⟩, hpQ y hy⟩)
    {s : Λ →* G} (hs : c.IsSection s) (hsQ : ∀ h, s h ∈ Q) {U : Subgroup M} (hUΛ : U ≤ Λ)
    (hU : ⁅U, U⁆ = U) {r : U →* G} (hr : c.IsSection r) (hr' : c'.IsSection r) (u : U) :
    τ ⟨u, hUΛ u.2⟩ = ⟨u, hUΛ u.2⟩ := by
  have hsr : s.comp (Subgroup.inclusion hUΛ) = r := (hs.restrict hUΛ).eq_of_perfect hU hr
  have hru : r u ∈ Q := by
    rw [← hsr]
    exact hsQ _
  have h1 := hτ (r u) hru
  have h2 : c'.p ⟨r u, hQ' hru⟩ = u := hr'.p_apply u
  have h3 : (⟨c.p ⟨r u, hQ hru⟩, hpQ _ hru⟩ : Λ) = ⟨u, hUΛ u.2⟩ :=
    Subtype.ext (hr.p_apply u)
  rw [h3] at h1
  exact Subtype.ext (h1.symm.trans h2)

theorem QCover.eq_or_eq_of_overlap {c c' : QCover G M} {Q : Subgroup G} (hQ : Q ≤ c.E)
    (hQ' : Q ≤ c'.E) {Λ : Subgroup M} (hZ : center Λ = ⊥)
    (hpQ : ∀ y (hy : y ∈ Q), c.p ⟨y, hQ hy⟩ ∈ Λ) (hpQ' : ∀ y (hy : y ∈ Q), c'.p ⟨y, hQ' hy⟩ ∈ Λ)
    {s s' : Λ →* G} (hs : c.IsSection s) (hs' : c'.IsSection s') (hsQ : ∀ h, s h ∈ Q)
    (hs'Q : ∀ h, s' h ∈ Q) {U : Subgroup M} (hUΛ : U ≤ Λ) (hU : ⁅U, U⁆ = U) {r : U →* G}
    (hr : c.IsSection r) (hr' : c'.IsSection r) (β : Λ ≃* Λ)
    (hrig : ∀ α : Λ ≃* Λ, (∀ u : U, α ⟨u, hUΛ u.2⟩ = ⟨u, hUΛ u.2⟩) → α = 1 ∨ α = β) :
    (∀ y (hy : y ∈ Q), c'.p ⟨y, hQ' hy⟩ = c.p ⟨y, hQ hy⟩) ∨
      ∀ y (hy : y ∈ Q), c'.p ⟨y, hQ' hy⟩ = β ⟨c.p ⟨y, hQ hy⟩, hpQ y hy⟩ := by
  obtain ⟨τ, hτ⟩ := QCover.exists_mulEquiv_of_overlap hQ hQ' hZ hpQ hpQ' hs hs' hsQ hs'Q
  rcases hrig τ (QCover.mulEquiv_fix_of_overlap hQ hQ' hpQ hτ hs hsQ hUΛ hU hr hr') with h | h
  · left
    intro y hy
    rw [hτ y hy, h]
    rfl
  · right
    intro y hy
    rw [hτ y hy, h]

theorem QCover.exists_aligned_triangle {F : M →* M} (hFF : ∀ x, F (F x) = x)
    {c₁ c₂ c₃ c₂F c₃F : QCover G M} {Q₁₂ Q₁₃ Q₂₃ : Subgroup G}
    (h₂F : c₂.TwistOn c₂F c₂.E F) (h₃F : c₃.TwistOn c₃F c₃.E F)
    (h₁₂ : c₁.TwistOn c₂ Q₁₂ (MonoidHom.id M) ∨ c₁.TwistOn c₂ Q₁₂ F)
    (h₁₃ : c₁.TwistOn c₃ Q₁₃ (MonoidHom.id M) ∨ c₁.TwistOn c₃ Q₁₃ F)
    (h₂₃ : c₂.TwistOn c₃ Q₂₃ (MonoidHom.id M) ∨ c₂.TwistOn c₃ Q₂₃ F)
    {y : G} (hy₁₂ : y ∈ Q₁₂) (hy₁₃ : y ∈ Q₁₃) (hy₂₃ : y ∈ Q₂₃) (hy₁ : y ∈ c₁.E)
    (hFy : F (c₁.p ⟨y, hy₁⟩) ≠ c₁.p ⟨y, hy₁⟩) :
    ∃ c₂' c₃', (c₂' = c₂ ∨ c₂' = c₂F) ∧ (c₃' = c₃ ∨ c₃' = c₃F) ∧
      c₁.TwistOn c₂' Q₁₂ (MonoidHom.id M) ∧ c₁.TwistOn c₃' Q₁₃ (MonoidHom.id M) ∧
        c₂'.TwistOn c₃' Q₂₃ (MonoidHom.id M) := by
  have hy₂ : y ∈ c₂.E := by rcases h₁₂ with h | h <;> exact h.le_right hy₁₂
  have hy₃ : y ∈ c₃.E := by rcases h₁₃ with h | h <;> exact h.le_right hy₁₃
  have hcomp : ∀ {a b c : QCover G M} {Q : Subgroup G} {ε ε' : M →* M}, a.TwistOn b Q ε →
      b.TwistOn c Q ε' → (∀ x, ε' (ε x) = x) → a.TwistOn c Q (MonoidHom.id M) :=
    fun h h' hεε => (h.trans h').congr_fun fun x => hεε x
  have hFid : ∀ x, F ((MonoidHom.id M) x) = F x := fun x => rfl
  have hidF : ∀ x, (MonoidHom.id M) (F x) = F x := fun x => rfl
  rcases h₁₂ with h12 | h12 <;> rcases h₁₃ with h13 | h13 <;> rcases h₂₃ with h23 | h23 <;>
    have e12 := h12.apply hy₁₂ hy₁ hy₂ <;> have e13 := h13.apply hy₁₃ hy₁ hy₃ <;>
    have e23 := h23.apply hy₂₃ hy₂ hy₃ <;> try simp only [MonoidHom.id_apply] at e12 e13 e23
  · exact ⟨c₂, c₃, Or.inl rfl, Or.inl rfl, h12, h13, h23⟩
  · exact absurd (by rw [← e12, ← e23, e13, e12]) hFy
  · exact absurd (by rw [← e13, e23, e12]) hFy
  · exact ⟨c₂, c₃F, Or.inl rfl, Or.inr rfl, h12, hcomp h13 (h₃F.mono h13.le_right) hFF,
      hcomp h23 (h₃F.mono h23.le_right) hFF⟩
  · exact absurd (by rw [← e12, ← e23, e13]) hFy
  · exact ⟨c₂F, c₃, Or.inr rfl, Or.inl rfl, hcomp h12 (h₂F.mono h12.le_right) hFF, h13,
      hcomp ((h₂F.mono h23.le_left).symm hFF) h23 hFF⟩
  · exact ⟨c₂F, c₃F, Or.inr rfl, Or.inr rfl, hcomp h12 (h₂F.mono h12.le_right) hFF,
      hcomp h13 (h₃F.mono h13.le_right) hFF,
      hcomp ((h₂F.mono h23.le_left).symm hFF) (h23.trans (h₃F.mono h23.le_right))
        fun x => by rw [MonoidHom.comp_apply, MonoidHom.id_apply, hFF]⟩
  · exact absurd (by rw [← e13, e23, e12, hFF]) hFy

end Twist

end CFSG.SeitzReduction.TwistedE6Pilot
