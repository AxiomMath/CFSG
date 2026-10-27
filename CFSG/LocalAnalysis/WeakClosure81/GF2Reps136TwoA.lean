module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136FixDecomp
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Cost1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoQ

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def Strong3 (L X : Subgroup (MulAut W)) : Prop :=
  GL3Case L X (Wd L) (Cd L) ∧
    ∃ J : Subgroup W, Cd L ≤ J ∧ J ≤ Wd L ∧ IsIrrOn L J (Cd L) ∧
      Nat.card (Sect J (Cd L)) ^ 3 = Nat.card (Sect (Wd L) (Cd L)) ∧
      McLShape (secSub J (Cd L) L) ∧
      ∀ l ∈ L, (∀ u ∈ J, l u * u⁻¹ ∈ Cd L) → ∀ u ∈ Wd L, l u * u⁻¹ ∈ Cd L


private theorem w1369_mem_stabSub_of_stable {U : Subgroup W} {X : Subgroup (MulAut W)}
    (h : StableUnder X U) {x : MulAut W} (hx : x ∈ X) : x ∈ stabSub U := by
  rw [mem_stabSub]
  intro u
  constructor
  · intro hu
    have h1 := h x⁻¹ (X.inv_mem hx) (x u) hu
    simpa using h1
  · exact h x hx u

private theorem w1369_resHom_mem_stabSub {U Z : Subgroup W} {X : Subgroup (MulAut W)}
    (hZ : StableUnder X Z) (hU : StableUnder X U) {x : MulAut W} (hx : x ∈ X) :
    resHom U ⟨x, w1369_mem_stabSub_of_stable hU hx⟩ ∈ stabSub (Z.subgroupOf U) := by
  intro z
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
  constructor
  · intro hz
    have h1 := hZ x⁻¹ (X.inv_mem hx) (x (z : W)) hz
    simpa using h1
  · intro hz
    exact hZ x hx (z : W) hz

private theorem w1369_quotHom_mem_secSub {U Z : Subgroup W} {Λ : Subgroup (MulAut W)}
    {x : MulAut W} (hx : x ∈ Λ)
    (hU : StableUnder Λ U) (hZ : StableUnder Λ Z) :
    quotHom (Z.subgroupOf U)
      ⟨resHom U ⟨x, w1369_mem_stabSub_of_stable hU hx⟩,
        w1369_resHom_mem_stabSub hZ hU hx⟩ ∈ secSub U Z Λ := by
  rw [secSub, CFSG.Quasithin.autSec, CFSG.Quasithin.autQuot, Subgroup.mem_map]
  refine ⟨⟨resHom U ⟨x, w1369_mem_stabSub_of_stable hU hx⟩,
      w1369_resHom_mem_stabSub hZ hU hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.autSub, Subgroup.mem_map]
  exact ⟨⟨x, w1369_mem_stabSub_of_stable hU hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

private noncomputable def w1369_secEquiv {A A₀ B B₀ : Subgroup W} {Λ : Subgroup (MulAut W)}
    (h : SecIsoOn Λ A A₀ B B₀) : Sect A A₀ ≃* Sect B B₀ := by
  classical
  let β : ↥A →* W := h.2.2.2.2.2.2.choose
  let β' : ↥A →* ↥B := β.codRestrict B h.2.2.2.2.2.2.choose_spec.1
  let φ : Sect A A₀ →* Sect B B₀ :=
    QuotientGroup.map (A₀.subgroupOf A) (B₀.subgroupOf B) β' (by
      intro a ha
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact (h.2.2.2.2.2.2.choose_spec.2.1 a).mpr (Subgroup.mem_subgroupOf.mp ha))
  refine MulEquiv.ofBijective φ ⟨?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff]
    rw [QuotientGroup.ker_map]
    have hker : (B₀.subgroupOf B).comap β' = A₀.subgroupOf A := by
      ext a
      change β a ∈ B₀ ↔ (a : W) ∈ A₀
      exact h.2.2.2.2.2.2.choose_spec.2.1 a
    rw [hker, QuotientGroup.map_mk'_self]
  · intro y
    induction y using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨a, ha⟩ := h.2.2.2.2.2.2.choose_spec.2.2.1 b b.2
      refine ⟨QuotientGroup.mk a, ?_⟩
      rw [QuotientGroup.map_mk, mk_eq_mk_iff, Subgroup.mem_subgroupOf]
      change β a * (b : W)⁻¹ ∈ B₀
      exact ha

private theorem w1369_secEquiv_mk {A A₀ B B₀ : Subgroup W} {Λ : Subgroup (MulAut W)}
    (h : SecIsoOn Λ A A₀ B B₀) (a : ↥A) :
    w1369_secEquiv h (QuotientGroup.mk a) =
      QuotientGroup.mk ((h.2.2.2.2.2.2.choose).codRestrict B
        h.2.2.2.2.2.2.choose_spec.1 a) := by
  rfl

private theorem w1369_secEquiv_quotHom {A A₀ B B₀ : Subgroup W} {Λ : Subgroup (MulAut W)}
    (h : SecIsoOn Λ A A₀ B B₀) {x : MulAut W} (hx : x ∈ Λ)
    (hxA : x ∈ stabSub A) (hxB : x ∈ stabSub B)
    (hx0A : resHom A ⟨x, hxA⟩ ∈ stabSub (A₀.subgroupOf A))
    (hx0B : resHom B ⟨x, hxB⟩ ∈ stabSub (B₀.subgroupOf B)) :
    MulAut.congr (w1369_secEquiv h)
        (quotHom (A₀.subgroupOf A) ⟨resHom A ⟨x, hxA⟩, hx0A⟩) =
      quotHom (B₀.subgroupOf B) ⟨resHom B ⟨x, hxB⟩, hx0B⟩ := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨z, rfl⟩ := (w1369_secEquiv h).surjective y
  have hcongr : ∀ (ψ : MulAut (Sect A A₀)) (z : Sect A A₀),
      (MulAut.congr (w1369_secEquiv h) ψ) ((w1369_secEquiv h) z) =
        (w1369_secEquiv h) (ψ z) := by
    intro ψ z
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply]
  rw [hcongr]
  induction z using QuotientGroup.induction_on with
  | H w =>
    rw [w1369_secEquiv_mk, quotHom_mk, w1369_secEquiv_mk, quotHom_mk]
    have hxwA : x (w : W) ∈ A := (mem_stabSub.mp hxA (w : W)).2 w.2
    have hwA : (resHom A ⟨x, hxA⟩) w = ⟨x (w : W), hxwA⟩ :=
      Subtype.ext (resHom_apply A ⟨x, hxA⟩ w)
    have key := h.2.2.2.2.2.2.choose_spec.2.2.2 x hx w ⟨x (w : W), hxwA⟩ rfl
    rw [CFSG.Quasithin.mk_eq_mk_iff, Subgroup.mem_subgroupOf]
    rw [hwA]
    simp only [MonoidHom.codRestrict_apply, Subgroup.coe_mul, Subgroup.coe_inv, resHom_apply]
    exact key

private theorem w1369_quotHom_eq_one_iff {U Z : Subgroup W} {x : MulAut W}
    (hxU : x ∈ stabSub U) (hxZ : resHom U ⟨x, hxU⟩ ∈ stabSub (Z.subgroupOf U)) :
    quotHom (Z.subgroupOf U) ⟨resHom U ⟨x, hxU⟩, hxZ⟩ = 1 ↔
      ∀ u : ↥U, x (u : W) * (u : W)⁻¹ ∈ Z := by
  constructor
  · intro h u
    have := congrArg (fun φ : MulAut (Sect U Z) => φ (QuotientGroup.mk u)) h
    rw [MulAut.one_apply, quotHom_mk] at this
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at this
    simpa [resHom_apply, div_eq_mul_inv] using this
  · intro h
    refine MulEquiv.ext fun y => ?_
    induction y using QuotientGroup.induction_on with
    | H u =>
      rw [MulAut.one_apply, quotHom_mk, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
      simpa [resHom_apply, div_eq_mul_inv] using h u


private theorem w1369_mem_secSub_quotHom_iff {U Z : Subgroup W} {Λ : Subgroup (MulAut W)}
    (hU : StableUnder Λ U) (hZ : StableUnder Λ Z) {φ : MulAut (Sect U Z)} :
    φ ∈ secSub U Z Λ ↔ ∃ (x : MulAut W) (hx : x ∈ Λ),
      quotHom (Z.subgroupOf U)
        ⟨resHom U ⟨x, w1369_mem_stabSub_of_stable hU hx⟩,
          w1369_resHom_mem_stabSub hZ hU hx⟩ = φ := by
  rw [secSub, CFSG.Quasithin.autSec, CFSG.Quasithin.autQuot, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.autSub, Subgroup.mem_map] at hg
    obtain ⟨x', hx', hx'g⟩ := hg
    refine ⟨(x' : MulAut W), Subgroup.mem_subgroupOf.mp hx', ?_⟩
    apply congrArg (quotHom (Z.subgroupOf U))
    refine Subtype.ext ?_
    change (resHom U
      ⟨(x' : MulAut W), w1369_mem_stabSub_of_stable hU (Subgroup.mem_subgroupOf.mp hx')⟩ :
        MulAut ↥U) = (g : MulAut ↥U)
    exact (congrArg (resHom U) (Subtype.ext rfl)).trans hx'g
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨resHom U ⟨x, w1369_mem_stabSub_of_stable hU hx⟩,
      w1369_resHom_mem_stabSub hZ hU hx⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.autSub, Subgroup.mem_map]
    exact ⟨⟨x, w1369_mem_stabSub_of_stable hU hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

private theorem w1369_map_centralizer_of_injective {G H : Type*} [Group G] [Group H]
    (f : G ≃* H) (S : Subgroup G) :
    Subgroup.centralizer (S.map f.toMonoidHom : Set H) =
      (Subgroup.centralizer (S : Set G)).map f.toMonoidHom := by
  apply le_antisymm
  · intro h hh
    refine Subgroup.mem_map.mpr ⟨f.symm h, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff] at hh ⊢
    intro s hs
    apply f.injective
    have h2 := hh (f s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h2
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hh
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro s hs
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hs
    rw [← map_mul, ← map_mul, hg s' hs']

private theorem w1369_map_secSub {A A₀ B B₀ : Subgroup W} {Λ : Subgroup (MulAut W)}
    (h : SecIsoOn Λ A A₀ B B₀) :
    (secSub A A₀ Λ).map (MulAut.congr (w1369_secEquiv h)).toMonoidHom = secSub B B₀ Λ := by
  apply le_antisymm
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (w1369_mem_secSub_quotHom_iff h.2.2.1 h.2.2.2.1).mp hψ
    change MulAut.congr (w1369_secEquiv h)
      (quotHom (A₀.subgroupOf A)
        ⟨resHom A ⟨x, w1369_mem_stabSub_of_stable h.2.2.1 hx⟩,
          w1369_resHom_mem_stabSub h.2.2.2.1 h.2.2.1 hx⟩) ∈ secSub B B₀ Λ
    rw [w1369_secEquiv_quotHom h hx (w1369_mem_stabSub_of_stable h.2.2.1 hx)
      (w1369_mem_stabSub_of_stable h.2.2.2.2.1 hx)
      (w1369_resHom_mem_stabSub h.2.2.2.1 h.2.2.1 hx)
      (w1369_resHom_mem_stabSub h.2.2.2.2.2.1 h.2.2.2.2.1 hx)]
    exact w1369_quotHom_mem_secSub hx h.2.2.2.2.1 h.2.2.2.2.2.1
  · intro φ hφ
    obtain ⟨x, hx, rfl⟩ := (w1369_mem_secSub_quotHom_iff h.2.2.2.2.1 h.2.2.2.2.2.1).mp hφ
    refine ⟨quotHom (A₀.subgroupOf A)
      ⟨resHom A ⟨x, w1369_mem_stabSub_of_stable h.2.2.1 hx⟩,
        w1369_resHom_mem_stabSub h.2.2.2.1 h.2.2.1 hx⟩, ?_, ?_⟩
    · exact w1369_quotHom_mem_secSub hx h.2.2.1 h.2.2.2.1
    · change MulAut.congr (w1369_secEquiv h)
        (quotHom (A₀.subgroupOf A)
          ⟨resHom A ⟨x, w1369_mem_stabSub_of_stable h.2.2.1 hx⟩,
            w1369_resHom_mem_stabSub h.2.2.2.1 h.2.2.1 hx⟩) = _
      rw [w1369_secEquiv_quotHom h hx (w1369_mem_stabSub_of_stable h.2.2.1 hx)
        (w1369_mem_stabSub_of_stable h.2.2.2.2.1 hx)
        (w1369_resHom_mem_stabSub h.2.2.2.1 h.2.2.1 hx)
        (w1369_resHom_mem_stabSub h.2.2.2.2.2.1 h.2.2.2.2.1 hx)]

private theorem w1369_centralizer_eq_bot_of_secIsoOn {A A₀ B B₀ : Subgroup W}
    {Λ : Subgroup (MulAut W)} (h : SecIsoOn Λ A A₀ B B₀)
    (hbot : Subgroup.centralizer
      ((secSub B B₀ Λ : Subgroup (MulAut (Sect B B₀))) : Set (MulAut (Sect B B₀))) = ⊥) :
    Subgroup.centralizer
      ((secSub A A₀ Λ : Subgroup (MulAut (Sect A A₀))) : Set (MulAut (Sect A A₀))) = ⊥ := by
  have hmapc := w1369_map_centralizer_of_injective (MulAut.congr (w1369_secEquiv h))
    (secSub A A₀ Λ)
  have hbot' : Subgroup.centralizer
      (((secSub A A₀ Λ).map (MulAut.congr (w1369_secEquiv h)).toMonoidHom :
        Subgroup (MulAut (Sect B B₀))) : Set (MulAut (Sect B B₀))) = ⊥ := by
    rw [w1369_map_secSub h]; exact hbot
  rw [hmapc] at hbot'
  rw [Subgroup.map_eq_bot_iff] at hbot'
  rw [show (MulAut.congr (w1369_secEquiv h)).toMonoidHom.ker = ⊥ from
    (MonoidHom.ker_eq_bot_iff _).mpr (MulAut.congr (w1369_secEquiv h)).injective] at hbot'
  exact le_bot_iff.mp hbot'

private theorem w1369_triv_of_secIsoOn {A A₀ B B₀ : Subgroup W} {Λ : Subgroup (MulAut W)}
    (h : SecIsoOn Λ A A₀ B B₀) {l : MulAut W} (hl : l ∈ Λ)
    (hlA : ∀ a ∈ A, l a * a⁻¹ ∈ A₀) : ∀ b ∈ B, l b * b⁻¹ ∈ B₀ := by
  have hlA' : l ∈ stabSub A := w1369_mem_stabSub_of_stable h.2.2.1 hl
  have hlB' : l ∈ stabSub B := w1369_mem_stabSub_of_stable h.2.2.2.2.1 hl
  have hlA0 : resHom A ⟨l, hlA'⟩ ∈ stabSub (A₀.subgroupOf A) :=
    w1369_resHom_mem_stabSub h.2.2.2.1 h.2.2.1 hl
  have hlB0 : resHom B ⟨l, hlB'⟩ ∈ stabSub (B₀.subgroupOf B) :=
    w1369_resHom_mem_stabSub h.2.2.2.2.2.1 h.2.2.2.2.1 hl
  have hAl : quotHom (A₀.subgroupOf A) ⟨resHom A ⟨l, hlA'⟩, hlA0⟩ = 1 := by
    rw [w1369_quotHom_eq_one_iff hlA' hlA0]
    intro u
    exact hlA u.1 u.2
  have hBl : quotHom (B₀.subgroupOf B) ⟨resHom B ⟨l, hlB'⟩, hlB0⟩ = 1 := by
    rw [← w1369_secEquiv_quotHom h hl hlA' hlB' hlA0 hlB0, hAl, map_one]
  intro b hb
  exact (w1369_quotHom_eq_one_iff hlB' hlB0).mp hBl ⟨b, hb⟩


private theorem w1369_stable_commSub_self (L : Subgroup (MulAut W)) :
    StableUnder L (commSub ⊤ L) := by
  intro l hl c hc
  rw [commSub] at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨m, hm, v, -, rfl⟩ := hz
      refine Subgroup.subset_closure ⟨l * m * l⁻¹,
        L.mul_mem (L.mul_mem hl hm) (L.inv_mem hl), l v, trivial, ?_⟩
      simp [MulAut.mul_apply, map_mul, map_inv]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

private theorem w1369_stable_fixV_self (L : Subgroup (MulAut W)) : StableUnder L (fixV L) := by
  intro l hl z hz
  rw [mem_fixV] at hz ⊢
  intro l' hl'
  rw [hz l hl, hz l' hl']

private theorem w1369_stabPair_self (L : Subgroup (MulAut W)) : StabPair L (Wd L) (Cd L) :=
  fun l hl => ⟨w1369_stable_commSub_self L l hl,
    fun z hz => ⟨w1369_stable_commSub_self L l hl z hz.1, w1369_stable_fixV_self L l hl z hz.2⟩⟩

private theorem w1369_stabPair_comm {X L : Subgroup (MulAut W)} (hXL : ⁅X, L⁆ = ⊥) :
    StabPair X (Wd L) (Cd L) := by
  have hcomm : ∀ x ∈ X, ∀ l ∈ L, x * l = l * x := by
    intro x hx l hl
    have h1 : x ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXL) hx
    exact (Subgroup.mem_centralizer_iff.mp h1 l hl).symm
  have hW : StableUnder X (commSub ⊤ L) := by
    intro x hx c hc
    rw [commSub] at hc ⊢
    induction hc using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨m, hm, v, -, rfl⟩ := hz
        refine Subgroup.subset_closure ⟨m, hm, x v, trivial, ?_⟩
        have h1 : x (m v) = m (x v) := by
          rw [← MulAut.mul_apply, hcomm x hx m hm, MulAut.mul_apply]
        rw [map_mul, map_inv, h1]
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  have hF : StableUnder X (fixV L) := by
    intro x hx z hz
    rw [mem_fixV] at hz ⊢
    intro l hl
    rw [← MulAut.mul_apply, ← hcomm x hx l hl, MulAut.mul_apply, hz l hl]
  intro x hx
  exact ⟨hW x hx, fun z hz => ⟨hW x hx z hz.1, hF x hx z hz.2⟩⟩

private theorem w1369_commSub_le_of_forall {U C : Subgroup W} {X : Subgroup (MulAut W)}
    (h : ∀ x ∈ X, ∀ u ∈ U, x u * u⁻¹ ∈ C) : commSub U X ≤ C := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, u, hu, rfl⟩
  exact h x hx u hu

private theorem w1369_pair_sum_le {r : ℕ} {f : Fin r → ℕ} {i j : Fin r} (hij : j ≠ i) :
    f i + f j ≤ ∑ k, f k := by
  have hsub : ({i, j} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun x _ _ => Nat.zero_le (f x))
  have h2 : ({i, j} : Finset (Fin r)).sum f = f i + f j := by
    rw [Finset.sum_insert (by simp [hij.symm]), Finset.sum_singleton]
  rwa [h2] at h

private theorem w1369_cost_eq_one {f : Fin 3 → ℕ} (hle : ∑ i, f i ≤ 3) (h1 : ∀ i, 1 ≤ f i)
    (i : Fin 3) : f i = 1 := by
  have hle' : f 0 + f 1 + f 2 ≤ 3 := by simpa [Fin.sum_univ_three] using hle
  have h0 := h1 0
  have h1' := h1 1
  have h2 := h1 2
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
  rcases hi with rfl | rfl | rfl <;> omega


theorem fix_hend (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    {r : ℕ} {J : Fin r → Subgroup W} (hD : FixDec t L r J) :
    ∀ i, (∃ j, j ≠ i ∧ SecIsoOn L (J i) (Cd L) (J j) (Cd L)) →
      Subgroup.centralizer ((secSub (J i) (Cd L) L : Subgroup (MulAut (Sect (J i) (Cd L)))) :
        Set (MulAut (Sect (J i) (Cd L)))) = ⊥ := by
  intro i ⟨j, hji, hiso⟩
  have hle : ∑ k, tcost t L (J k) ≤ 3 := hD.2.2.2.2.2
  have h1 : ∀ k, 1 ≤ tcost t L (J k) := fun k => (hD.2.2.1 k).2.2.2.2.2
  have hpair : tcost t L (J i) + tcost t L (J j) ≤ 3 :=
    (w1369_pair_sum_le (f := fun k => tcost t L (J k)) hji).trans hle
  by_cases hi1 : tcost t L (J i) = 1
  · exact (cost_one_summand hw2 c (hD.2.2.1 i).1 (hD.2.2.1 i).2.1
      (hD.2.2.1 i).2.2.1 (hD.2.2.1 i).2.2.2.1 (hD.2.2.1 i).2.2.2.2.1 hi1).1
  · have hj1 : tcost t L (J j) = 1 := by
      have := h1 i
      have := h1 j
      omega
    exact w1369_centralizer_eq_bot_of_secIsoOn hiso
      (cost_one_summand hw2 c (hD.2.2.1 j).1 (hD.2.2.1 j).2.1
        (hD.2.2.1 j).2.2.1 (hD.2.2.1 j).2.2.2.1 (hD.2.2.1 j).2.2.2.2.1 hj1).1

theorem perfect_cent_dichotomy (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) {X : Subgroup (MulAut W)} (hXY : X ≤ Y)
    (hXp : ⁅X, X⁆ = X) (hXL : ⁅X, L⁆ = ⊥) :
    (∀ x ∈ X, ∀ u ∈ Wd L, x u * u⁻¹ ∈ Cd L) ∨ Strong3 L X := by
  obtain ⟨r, J, hD⟩ := fix_decomp hw2 c hfix
  rcases perfect_cent_sec hw2 (inf_le_left) (w1369_stabPair_self L) (w1369_stabPair_comm hXL) hD.2.1
      (fun i => (hD.2.2.1 i).1) (fun i => (hD.2.2.1 i).2.1) (fun i => (hD.2.2.1 i).2.2.1)
      hD.2.2.2.1 hD.2.2.2.2.1 (fix_hend hw2 c hD) hXL hXp with htriv | hrest
  · exact Or.inl htriv
  · obtain ⟨hr3, hiso, hcard, hgl3⟩ := hrest
    right
    subst hr3
    refine ⟨hgl3, J 0, (hD.2.2.1 0).1, (hD.2.2.1 0).2.1, (hD.2.2.1 0).2.2.1,
      hcard 0, ?_, ?_⟩
    · have h0 : tcost t L (J 0) = 1 :=
        w1369_cost_eq_one hD.2.2.2.2.2 (fun k => (hD.2.2.1 k).2.2.2.2.2) 0
      exact (cost_one_summand hw2 c (hD.2.2.1 0).1 (hD.2.2.1 0).2.1
        (hD.2.2.1 0).2.2.1 (hD.2.2.1 0).2.2.2.1 (hD.2.2.1 0).2.2.2.2.1 h0).2
    · intro l hl hl0 u hu
      let S : Subgroup W :=
        { carrier := {u | l u * u⁻¹ ∈ Cd L}
          one_mem' := by simp
          mul_mem' := by
            intro a b ha hb
            change l (a * b) * (a * b)⁻¹ ∈ Cd L
            have h : l (a * b) * (a * b)⁻¹ = (l a * a⁻¹) * (l b * b⁻¹) := by
              rw [map_mul, mul_inv_rev]
              ac_rfl
            rw [h]
            exact (Cd L).mul_mem ha hb
          inv_mem' := by
            intro a ha
            change l a⁻¹ * (a⁻¹)⁻¹ ∈ Cd L
            have h : l a⁻¹ * (a⁻¹)⁻¹ = (l a * a⁻¹)⁻¹ := by
              rw [map_inv, inv_inv, mul_inv_rev, inv_inv]
              ac_rfl
            rw [h]
            exact (Cd L).inv_mem ha }
      have hCdS : Cd L ≤ S := by
        intro z hz
        have hzfix : l z = z := (mem_fixV.mp hz.2) l hl
        simp [S, hzfix]
      have hJS : ∀ k : Fin 3, J k ≤ S := by
        intro k b hb
        exact w1369_triv_of_secIsoOn (hiso 0 k) hl hl0 b hb
      have hWS : Wd L ≤ S := by
        rw [← hD.2.2.2.2.1]
        exact sup_le hCdS (iSup_le hJS)
      exact hWS hu

theorem perfCentTriv_of_fixes (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) : PerfCentTriv Y L := by
  intro X hXY hXp hXL M hCM hMW hMstab hcomm
  rcases perfect_cent_dichotomy hw2 c hfix hXY hXp hXL with htriv | hstrong
  · exact w1369_commSub_le_of_forall htriv
  · exfalso
    obtain ⟨hgl3, -⟩ := hstrong
    exact hgl3.2.1 M hCM hMW hMstab hcomm

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
