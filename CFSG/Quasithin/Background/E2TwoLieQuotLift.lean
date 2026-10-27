module

public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

theorem exists_eq_of_isComponent_of_le_iSup {Q : Type} [Group Q] [Finite Q] {S : Subgroup Q}
    (hS : CFSG.IsComponent S) {ι : Type} (F : ι → Subgroup Q)
    (hF : ∀ i, F i = ⊥ ∨ CFSG.IsComponent (F i)) (N : Subgroup Q) [N.Normal]
    (hsol : Group.IsSolvable (Q ⧸ N)) (hNF : N ≤ ⨆ i, F i) : ∃ i, S = F i := by
  by_contra hne
  push Not at hne
  have hc : ∀ i, F i ≤ Subgroup.centralizer (S : Set Q) := by
    intro i
    rcases hF i with h | h
    · rw [h]
      exact bot_le
    · rcases CFSG.LocalCores.distinct_components_commute hS h with h' | h'
      · exact absurd h' (hne i)
      · rw [Subgroup.commutator_comm] at h'
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h'
  have hNc : N ≤ Subgroup.centralizer (S : Set Q) := hNF.trans (iSup_le hc)
  obtain ⟨hperf, -, a, b, hab⟩ := hS.1
  set φ : ↥S →* Q ⧸ N := (QuotientGroup.mk' N).comp S.subtype with hφ
  have hSN : S ≤ N := by
    have hR : Group.IsPerfect ↥φ.range :=
      Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    have hRs : Group.IsSolvable ↥φ.range := by
      have := hsol
      exact subgroup_solvable_of_solvable _
    have hbot : φ.range = ⊥ := by
      by_contra hne'
      have : Nontrivial ↥φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne'
      exact Group.IsPerfect.not_isSolvable (G := ↥φ.range) hRs
    intro s hs
    have hmem : φ ⟨s, hs⟩ ∈ φ.range := ⟨⟨s, hs⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    simpa [hφ] using hmem
  have hcomm : ∀ x y : ↥S, x * y = y * x := by
    intro x y
    have hy : (y : Q) ∈ Subgroup.centralizer (S : Set Q) := hNc (hSN y.2)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hy (x : Q) x.2)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm a b])

theorem isQuasisimple_of_open {X : Type} [Group X] (h : CFSG.Open.IsQuasisimple X) :
    CFSG.IsQuasisimple X := by
  obtain ⟨hc, hs⟩ := h
  have hperf : Group.IsPerfect X := Group.isPerfect_def.mpr hc
  refine ⟨hperf, hs, ?_⟩
  by_contra hab
  push Not at hab
  have hperfQ : Group.IsPerfect (X ⧸ Subgroup.center X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _)
  have hbot : commutator (X ⧸ Subgroup.center X) = ⊥ := by
    rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hab x y
  have htop : commutator (X ⧸ Subgroup.center X) = ⊤ := Group.isPerfect_def.mp hperfQ
  have hnt : Nontrivial (X ⧸ Subgroup.center X) := hs.toNontrivial
  obtain ⟨x, y, hxy⟩ := hnt
  apply hxy
  have hx : x ∈ commutator (X ⧸ Subgroup.center X) := htop ▸ Subgroup.mem_top x
  have hy : y ∈ commutator (X ⧸ Subgroup.center X) := htop ▸ Subgroup.mem_top y
  rw [hbot, Subgroup.mem_bot] at hx hy
  rw [hx, hy]

theorem isSubnormal_subgroupOf_of_open {X : Type} [Group X] {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) : (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isComponent_or_eq_bot_map {H K₀ : Subgroup G} (hK₀H : K₀ ≤ H)
    (hK₀s : (K₀.subgroupOf H).IsSubnormal)
    (hq : CFSG.Open.IsQuasisimple (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀))
    {Q : Type} [Group Q] (f : ↥H →* Q) (hf : Function.Surjective f)
    (hO2 : ∀ x : ↥K₀, x ∈ CFSG.Open.pCore 2 ↥K₀ → f (Subgroup.inclusion hK₀H x) = 1) :
    (K₀.subgroupOf H).map f = ⊥ ∨ CFSG.IsComponent ((K₀.subgroupOf H).map f) := by
  set F₁ := (K₀.subgroupOf H).map f with hF₁
  by_cases hbot : F₁ = ⊥
  · exact Or.inl hbot
  right
  refine ⟨?_, hK₀s.map hf⟩
  set g : ↥K₀ →* Q := f.comp (Subgroup.inclusion hK₀H) with hg
  have hgk : CFSG.Open.pCore 2 ↥K₀ ≤ g.ker := fun x hx => hO2 x hx
  set gbar : ↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀ →* Q := QuotientGroup.lift _ g hgk with hgbar
  have hrange : gbar.range = F₁ := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨Subgroup.inclusion hK₀H k, by
        simp [Subgroup.mem_subgroupOf], rfl⟩
    · rintro ⟨h, hh, rfl⟩
      refine ⟨QuotientGroup.mk ⟨(h : G), Subgroup.mem_subgroupOf.mp hh⟩, ?_⟩
      simp only [hgbar, hg, QuotientGroup.lift_mk, MonoidHom.comp_apply]
      exact congrArg f (Subtype.ext rfl)
  have hsurj : Function.Surjective ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp
      gbar.rangeRestrict) :=
    (MulEquiv.subgroupCongr hrange).surjective.comp gbar.rangeRestrict_surjective
  have hne : ∃ k, ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp gbar.rangeRestrict) k ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hbot
    rw [eq_bot_iff]
    intro q hq'
    obtain ⟨k, hk⟩ := hsurj ⟨q, hq'⟩
    have := hall k
    rw [hk] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  exact CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (isQuasisimple_of_open hq) hsurj hne

theorem exists_surjective_of_isComponent {H T K₀ : Subgroup G} (hTH : T ≤ H)
    (hT : IsPGroup 2 T) (hK₀H : K₀ ≤ H) (hK₀s : (K₀.subgroupOf H).IsSubnormal)
    (hHK : H = K₀ ⊔ T) (hq : CFSG.Open.IsQuasisimple (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀))
    {Q : Type} [Group Q] [Finite Q] (f : ↥H →* Q) (hf : Function.Surjective f)
    (hO2 : ∀ x : ↥K₀, x ∈ CFSG.Open.pCore 2 ↥K₀ → f (Subgroup.inclusion hK₀H x) = 1)
    {S : Subgroup Q} (hS : CFSG.IsComponent S) :
    ∃ g : ↥K₀ →* ↥S, Function.Surjective g := by
  set F₁ := (K₀.subgroupOf H).map f with hF₁
  have hF₁c := isComponent_or_eq_bot_map hK₀H hK₀s hq f hf hO2
  set F : ↥H → Subgroup Q := fun h => F₁.map (MulAut.conj (f h)).toMonoidHom with hFdef
  have hF : ∀ h, F h = ⊥ ∨ CFSG.IsComponent (F h) := by
    intro h
    rcases hF₁c with h0 | h1
    · left
      show F₁.map (MulAut.conj (f h)).toMonoidHom = ⊥
      rw [show F₁ = ⊥ from h0, Subgroup.map_bot]
    · right
      exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (f h)) h1
  have hFn : (⨆ h, F h).Normal := by
    constructor
    intro n hn q
    obtain ⟨x, rfl⟩ := hf q
    refine Subgroup.iSup_induction F (C := fun n => f x * n * (f x)⁻¹ ∈ ⨆ h, F h) hn ?_ ?_ ?_
    · intro h n hn
      obtain ⟨a, ha, rfl⟩ := hn
      refine Subgroup.mem_iSup_of_mem (x * h) ⟨a, ha, ?_⟩
      simp [MulAut.conj_apply, map_mul, mul_assoc]
    · simp
    · intro n₁ n₂ ih₁ ih₂
      have e : f x * (n₁ * n₂) * (f x)⁻¹ = (f x * n₁ * (f x)⁻¹) * (f x * n₂ * (f x)⁻¹) := by
        group
      rw [e]
      exact Subgroup.mul_mem _ ih₁ ih₂
  set N₀ : Subgroup ↥H := Subgroup.normalClosure (K₀.subgroupOf H : Set ↥H) with hN₀
  set N : Subgroup Q := N₀.map f with hN
  have hNn : N.Normal := Subgroup.Normal.map inferInstance f hf
  have hNF : N ≤ ⨆ h, F h := by
    rw [hN, Subgroup.map_le_iff_le_comap]
    have : ((⨆ h, F h).comap f).Normal := Subgroup.Normal.comap hFn f
    refine Subgroup.normalClosure_le_normal ?_
    intro k hk
    refine Subgroup.mem_iSup_of_mem 1 ⟨f k, ⟨k, hk, rfl⟩, ?_⟩
    simp
  have hsol : Group.IsSolvable (Q ⧸ N) := by
    set ψ : ↥H →* Q ⧸ N := (QuotientGroup.mk' N).comp f with hψ
    set T' : Subgroup ↥H := T.subgroupOf H with hT'
    have hK₀ψ : (K₀.subgroupOf H).map ψ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_bot, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact ⟨k, Subgroup.le_normalClosure hk, rfl⟩
    have htop : K₀.subgroupOf H ⊔ T' = ⊤ := by
      rw [hT', ← Subgroup.subgroupOf_sup hK₀H hTH, ← hHK, Subgroup.subgroupOf_self]
    have hrange : T'.map ψ = ⊤ := by
      have h1 : (⊤ : Subgroup ↥H).map ψ = ⊤ := by
        rw [Subgroup.map_top_of_surjective ψ
          ((QuotientGroup.mk'_surjective N).comp hf)]
      rw [← htop, Subgroup.map_sup, hK₀ψ, bot_sup_eq] at h1
      exact h1
    have hT'p : IsPGroup 2 ↥T' :=
      IsPGroup.of_injective hT (Subgroup.subgroupOfEquivOfLe hTH).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hTH).injective
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite ↥T' := inferInstance
    have hTn : Group.IsNilpotent ↥T' := hT'p.isNilpotent
    have hTs : Group.IsSolvable ↥T' := inferInstance
    refine Group.isSolvable_of_surjective (f := ψ.comp T'.subtype) ?_
    intro q
    have hq : q ∈ T'.map ψ := hrange ▸ Subgroup.mem_top q
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨h, hSh⟩ := exists_eq_of_isComponent_of_le_iSup hS F hF N hsol hNF
  set g₀ : ↥K₀ →* ↥F₁ := (f.comp (Subgroup.inclusion hK₀H)).codRestrict F₁
    (fun k => ⟨Subgroup.inclusion hK₀H k, by simp [Subgroup.mem_subgroupOf], rfl⟩) with hg₀
  have hg₀s : Function.Surjective g₀ := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    show f (Subgroup.inclusion hK₀H ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩) = f y
    exact congrArg f (Subtype.ext rfl)
  set e : ↥F₁ ≃* ↥S := ((MulAut.conj (f h)).subgroupMap F₁).trans
    (MulEquiv.subgroupCongr hSh.symm) with he
  exact ⟨e.toMonoidHom.comp g₀, e.surjective.comp hg₀s⟩

end E2

end CFSG.Quasithin
