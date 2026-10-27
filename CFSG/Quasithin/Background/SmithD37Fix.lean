module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.SmithD37

variable {U : Type*} [CommGroup U]

@[expose] def disp (x : MulAut U) : U →* U where
  toFun u := x u * u⁻¹
  map_one' := by simp
  map_mul' a b := by rw [map_mul, mul_inv, mul_mul_mul_comm]

theorem disp_apply (x : MulAut U) (u : U) : disp x u = x u * u⁻¹ := rfl

theorem disp_eq_one_iff (x : MulAut U) (u : U) : disp x u = 1 ↔ x u = u := by
  rw [disp_apply, mul_inv_eq_one]

theorem disp_comm {x l : MulAut U} (h : x * l = l * x) (u : U) :
    disp x (l u) = l (disp x u) := by
  have h1 : x (l u) = l (x u) := by
    have := congrArg (fun φ : MulAut U => φ u) h
    simpa [MulAut.mul_apply] using this
  rw [disp_apply, disp_apply, h1, map_mul, map_inv]

@[expose] def IsInvBy (L : Subgroup (MulAut U)) (Y : Subgroup U) : Prop :=
  ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y

@[expose] def NoFix (L : Subgroup (MulAut U)) (Y : Subgroup U) : Prop :=
  ∀ y ∈ Y, (∀ l ∈ L, l y = y) → y = 1

theorem noFix_bot (L : Subgroup (MulAut U)) : NoFix L (⊥ : Subgroup U) :=
  fun _ hy _ => (Subgroup.mem_bot).mp hy

theorem isInvBy_bot (L : Subgroup (MulAut U)) : IsInvBy L (⊥ : Subgroup U) := by
  intro l _ y hy
  rw [Subgroup.mem_bot] at hy ⊢
  rw [hy, map_one]

theorem IsInvBy.sup {L : Subgroup (MulAut U)} {Y Z : Subgroup U} (hY : IsInvBy L Y)
    (hZ : IsInvBy L Z) : IsInvBy L (Y ⊔ Z) := by
  intro l hl d hd
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hd
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hY l hl y hy) (hZ l hl z hz)

theorem IsInvBy.inf {L : Subgroup (MulAut U)} {Y Z : Subgroup U} (hY : IsInvBy L Y)
    (hZ : IsInvBy L Z) : IsInvBy L (Y ⊓ Z) :=
  fun l hl d hd => ⟨hY l hl d hd.1, hZ l hl d hd.2⟩

theorem noFix_sup_of_inf {L : Subgroup (MulAut U)} {Y Z : Subgroup U} (hY : IsInvBy L Y)
    (hZ : IsInvBy L Z) (hYf : NoFix L Y) (hZf : NoFix L Z) (hYZ : Y ⊓ Z = ⊥) :
    NoFix L (Y ⊔ Z) := by
  intro d hd hfix
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hd
  have key : ∀ l ∈ L, l y = y := by
    intro l hl
    have h1 : l y * l z = y * z := by rw [← map_mul]; exact hfix l hl
    have h2 : l y * y⁻¹ = z * (l z)⁻¹ := by
      rw [mul_inv_eq_mul_inv_iff_mul_eq_mul, h1, mul_comm]
    have hmem : l y * y⁻¹ ∈ Y ⊓ Z :=
      ⟨Y.mul_mem (hY l hl y hy) (Y.inv_mem hy), h2 ▸ Z.mul_mem hz (Z.inv_mem (hZ l hl z hz))⟩
    rw [hYZ, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  have hy1 : y = 1 := hYf y hy key
  subst hy1
  rw [one_mul] at hfix ⊢
  exact hZf z hz (fun l hl => by simpa using hfix l hl)

@[expose] def IsIrrPiece (L : Subgroup (MulAut U)) (Z : Subgroup U) : Prop :=
  IsInvBy L Z ∧ (Z = ⊥ ∨ ((∀ Y : Subgroup U, IsInvBy L Y → Y ≤ Z → Y = ⊥ ∨ Y = Z) ∧
    ∃ z ∈ Z, ∃ l ∈ L, l z ≠ z))

@[expose] def fixIn (L : Subgroup (MulAut U)) (Z : Subgroup U) : Subgroup U where
  carrier := {z | z ∈ Z ∧ ∀ l ∈ L, l z = z}
  one_mem' := ⟨Z.one_mem, fun l _ => map_one l⟩
  mul_mem' := fun ha hb => ⟨Z.mul_mem ha.1 hb.1, fun l hl => by rw [map_mul, ha.2 l hl, hb.2 l hl]⟩
  inv_mem' := fun ha => ⟨Z.inv_mem ha.1, fun l hl => by rw [map_inv, ha.2 l hl]⟩

theorem isInvBy_fixIn (L : Subgroup (MulAut U)) (Z : Subgroup U) : IsInvBy L (fixIn L Z) := by
  intro l hl z hz
  rw [hz.2 l hl]
  exact hz

theorem IsIrrPiece.noFix {L : Subgroup (MulAut U)} {Z : Subgroup U} (h : IsIrrPiece L Z) :
    NoFix L Z := by
  rcases h.2 with h0 | ⟨hirr, z₀, hz₀, l₀, hl₀, hne⟩
  · subst h0
    exact noFix_bot L
  · rcases hirr (fixIn L Z) (isInvBy_fixIn L Z) (fun _ hz => hz.1) with h1 | h1
    · intro y hy hfix
      have : y ∈ fixIn L Z := ⟨hy, hfix⟩
      rwa [h1, Subgroup.mem_bot] at this
    · exfalso
      have : z₀ ∈ fixIn L Z := by rw [h1]; exact hz₀
      exact hne (this.2 l₀ hl₀)

theorem noFix_sup_piece {L : Subgroup (MulAut U)} {Y Z : Subgroup U} (hY : IsInvBy L Y)
    (hYf : NoFix L Y) (hZ : IsIrrPiece L Z) : NoFix L (Y ⊔ Z) := by
  rcases hZ.2 with h0 | ⟨hirr, -⟩
  · rw [h0, sup_bot_eq]
    exact hYf
  · rcases hirr (Y ⊓ Z) (hY.inf hZ.1) inf_le_right with h1 | h1
    · exact noFix_sup_of_inf hY hZ.1 hYf hZ.noFix h1
    · rw [sup_eq_left.mpr (h1 ▸ inf_le_left : Z ≤ Y)]
      exact hYf

theorem noFix_iSup {L : Subgroup (MulAut U)} {ι : Type*} [Finite ι] (Z : ι → Subgroup U)
    (hZ : ∀ i, IsIrrPiece L (Z i)) : NoFix L (⨆ i, Z i) ∧ IsInvBy L (⨆ i, Z i) := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, NoFix L (s.sup Z) ∧ IsInvBy L (s.sup Z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨noFix_bot L, isInvBy_bot L⟩
    | insert i s _ ih =>
      rw [Finset.sup_insert, sup_comm]
      exact ⟨noFix_sup_piece ih.2 ih.1 (hZ i), ih.2.sup (hZ i).1⟩
  have h := key Finset.univ
  have heq : (Finset.univ : Finset ι).sup Z = ⨆ i, Z i := by
    rw [Finset.sup_eq_iSup]
    simp
  rw [heq] at h
  exact h

theorem trivial_of_perfect {L : Subgroup (MulAut U)} [Group.IsPerfect ↥L] {C : Subgroup U}
    (hC : C ≤ fixV L) (h : ∀ l ∈ L, ∀ u, l u * u⁻¹ ∈ C) : ∀ l ∈ L, ∀ u, l u = u := by
  let θ : ↥L →* (U → U) :=
    { toFun := fun l u => disp (l : MulAut U) u
      map_one' := by funext u; simp [disp_apply]
      map_mul' := by
        intro a b
        funext u
        have hb : (b : MulAut U) u = disp (b : MulAut U) u * u := by
          rw [disp_apply, inv_mul_cancel_right]
        have hfix : (a : MulAut U) (disp (b : MulAut U) u) = disp (b : MulAut U) u :=
          hC (h b b.2 u) a a.2
        show disp ((a : MulAut U) * (b : MulAut U)) u =
          disp (a : MulAut U) u * disp (b : MulAut U) u
        rw [disp_apply, MulAut.mul_apply, hb, map_mul, hfix, disp_apply (a : MulAut U),
          mul_comm (disp _ u), mul_assoc, mul_assoc, mul_comm u⁻¹] }
  intro l hl u
  have hker : (⟨l, hl⟩ : ↥L) ∈ θ.ker :=
    Abelianization.commutator_subset_ker θ Group.IsPerfect.mem_commutator
  have := congrFun (MonoidHom.mem_ker.mp hker) u
  exact (disp_eq_one_iff l u).mp this

theorem isInvBy_of_le_stabSub {L : Subgroup (MulAut U)} {J : Subgroup U} (h : L ≤ stabSub J) :
    IsInvBy L J := fun _ hl y hy => (h hl y).2 hy

theorem isInvBy_fixV (L : Subgroup (MulAut U)) : IsInvBy L (fixV L) := by
  intro l hl y hy
  rw [hy l hl]
  exact hy

variable [Finite U]

theorem mem_stabSub_of_maps {J : Subgroup U} {g : MulAut U} (h : ∀ y ∈ J, g y ∈ J) :
    g ∈ stabSub J := by
  intro u
  refine ⟨fun hu => ?_, h u⟩
  let f : ↥J → ↥J := fun y => ⟨g y, h y y.2⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (g.injective (congrArg Subtype.val hab))
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨g u, hu⟩
  have : g y = g u := congrArg Subtype.val hy
  rw [← g.injective this]
  exact y.2

theorem le_stabSub_of_isInvBy {L : Subgroup (MulAut U)} {J : Subgroup U} (h : IsInvBy L J) :
    L ≤ stabSub J := fun l hl => mem_stabSub_of_maps (h l hl)

theorem isInvBy_sup {L₁ L₂ : Subgroup (MulAut U)} {J : Subgroup U} (h₁ : IsInvBy L₁ J)
    (h₂ : IsInvBy L₂ J) : IsInvBy (L₁ ⊔ L₂) J :=
  isInvBy_of_le_stabSub (sup_le (le_stabSub_of_isInvBy h₁) (le_stabSub_of_isInvBy h₂))

@[expose] def MinOver (L : Subgroup (MulAut U)) (C I : Subgroup U) : Prop :=
  IsInvBy L I ∧ C < I ∧ ∀ J : Subgroup U, IsInvBy L J → C < J → J ≤ I → J = I

omit [Finite U] in
theorem MinOver.eq_or_eq {L : Subgroup (MulAut U)} {C I J : Subgroup U} (h : MinOver L C I)
    (hJ : IsInvBy L J) (hCJ : C ≤ J) (hJI : J ≤ I) : J = C ∨ J = I := by
  rcases hCJ.lt_or_eq with hlt | heq
  · exact Or.inr (h.2.2 J hJ hlt hJI)
  · exact Or.inl heq.symm

omit [Finite U] in
theorem IsInvBy.map_of_comm {L : Subgroup (MulAut U)} {J : Subgroup U} (hJ : IsInvBy L J)
    {y : MulAut U} (hy : ∀ l ∈ L, l * y = y * l) : IsInvBy L (J.map y.toMonoidHom) := by
  rintro l hl _ ⟨w, hw, rfl⟩
  refine ⟨l w, hJ l hl w hw, ?_⟩
  have := congrArg (fun φ : MulAut U => φ w) (hy l hl)
  simp only [MulAut.mul_apply] at this
  exact this.symm

omit [Finite U] in
theorem map_eq_of_fix {C : Subgroup U} {z : MulAut U} (hz : ∀ c ∈ C, z c = c) :
    C.map z.toMonoidHom = C := by
  ext c
  constructor
  · rintro ⟨c', hc', rfl⟩
    simpa [hz c' hc'] using hc'
  · intro hc
    exact ⟨c, hc, hz c hc⟩

omit [Finite U] in
theorem inv_fix_of_fix {C : Subgroup U} {z : MulAut U} (hz : ∀ c ∈ C, z c = c) :
    ∀ c ∈ C, z⁻¹ c = c := fun c hc => (MulEquiv.symm_apply_eq z).mpr (hz c hc).symm

omit [Finite U] in
theorem map_lt_map_of_injective {f : U →* U} (hf : Function.Injective f) {A B : Subgroup U}
    (h : A < B) : A.map f < B.map f :=
  lt_of_le_of_ne (Subgroup.map_mono h.le) fun he => h.ne (Subgroup.map_injective hf he)

omit [Finite U] in
theorem MinOver.map {L : Subgroup (MulAut U)} {C I : Subgroup U} (h : MinOver L C I)
    {y : MulAut U} (hy : ∀ l ∈ L, l * y = y * l) (hyC : ∀ c ∈ C, y c = c) :
    MinOver L C (I.map y.toMonoidHom) := by
  have hCmap : C.map y.toMonoidHom = C := map_eq_of_fix hyC
  have hyi : ∀ l ∈ L, l * y⁻¹ = y⁻¹ * l := by
    intro l hl
    have := hy l hl
    calc l * y⁻¹ = y⁻¹ * (y * l) * y⁻¹ := by group
      _ = y⁻¹ * (l * y) * y⁻¹ := by rw [this]
      _ = y⁻¹ * l := by group
  refine ⟨h.1.map_of_comm hy, ?_, fun J hJ hCJ hJI => ?_⟩
  · rw [← hCmap]
    exact map_lt_map_of_injective y.injective h.2.1
  · have hJ' : IsInvBy L (J.map y⁻¹.toMonoidHom) := hJ.map_of_comm hyi
    have hback : (J.map y⁻¹.toMonoidHom).map y.toMonoidHom = J := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id J
      ext u
      simp
    have hCJ' : C < J.map y⁻¹.toMonoidHom := by
      have h1 := map_lt_map_of_injective (f := (y⁻¹).toMonoidHom) (y⁻¹).injective hCJ
      have hC' : C.map y⁻¹.toMonoidHom = C := map_eq_of_fix (inv_fix_of_fix hyC)
      rwa [hC'] at h1
    have hJI' : J.map y⁻¹.toMonoidHom ≤ I := by
      intro u hu
      obtain ⟨w, hw, rfl⟩ := hu
      obtain ⟨i, hi, rfl⟩ := hJI hw
      simpa using hi
    have := h.2.2 _ hJ' hCJ' hJI'
    rw [← hback, this]

omit [Finite U] in
theorem isIrrPiece_map_disp {L : Subgroup (MulAut U)} {C J : Subgroup U} (hJ : MinOver L C J)
    {x : MulAut U} (hx : ∀ l ∈ L, l * x = x * l) (hxC : ∀ c ∈ C, x c = c)
    (hnt : ∃ w ∈ J, ∃ l ∈ L, l w * w⁻¹ ∉ C) : IsIrrPiece L (J.map (disp x)) := by
  have hd : ∀ l ∈ L, ∀ w, disp x (l w) = l (disp x w) := fun l hl w =>
    disp_comm (hx l hl).symm w
  have hinv : IsInvBy L (J.map (disp x)) := by
    rintro l hl _ ⟨w, hw, rfl⟩
    exact ⟨l w, hJ.1 l hl w hw, hd l hl w⟩
  refine ⟨hinv, ?_⟩
  set K : Subgroup U := J ⊓ (disp x).ker with hK
  have hKinv : IsInvBy L K := by
    intro l hl w hw
    refine ⟨hJ.1 l hl w hw.1, ?_⟩
    have hw2 : disp x w = 1 := hw.2
    show disp x (l w) = 1
    rw [hd l hl, hw2, map_one]
  have hCK : C ≤ K := fun c hc =>
    ⟨hJ.2.1.le hc, show disp x c = 1 from (disp_eq_one_iff x c).mpr (hxC c hc)⟩
  rcases hJ.eq_or_eq hKinv hCK inf_le_left with hKC | hKJ
  · right
    refine ⟨fun Y hY hYle => ?_, ?_⟩
    · set P : Subgroup U := J ⊓ Y.comap (disp x)
      have hPinv : IsInvBy L P := by
        intro l hl w hw
        refine ⟨hJ.1 l hl w hw.1, ?_⟩
        have hw2 : disp x w ∈ Y := hw.2
        show disp x (l w) ∈ Y
        rw [hd l hl]
        exact hY l hl _ hw2
      have hCP : C ≤ P := fun c hc => ⟨hJ.2.1.le hc, show disp x c ∈ Y by
        rw [(disp_eq_one_iff x c).mpr (hxC c hc)]; exact Y.one_mem⟩
      rcases hJ.eq_or_eq hPinv hCP inf_le_left with hPC | hPJ
      · left
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨w, hw, rfl⟩ := hYle hy
        have hwP : w ∈ P := ⟨hw, hy⟩
        rw [hPC] at hwP
        rw [Subgroup.mem_bot, disp_eq_one_iff]
        exact hxC w hwP
      · right
        refine le_antisymm hYle ?_
        rintro _ ⟨w, hw, rfl⟩
        have hwP : w ∈ P := hPJ ▸ hw
        exact hwP.2
    · by_contra hall
      push Not at hall
      obtain ⟨w, hw, l, hl, hlw⟩ := hnt
      apply hlw
      have hmem : l w * w⁻¹ ∈ K := by
        refine ⟨J.mul_mem (hJ.1 l hl w hw) (J.inv_mem hw), ?_⟩
        show disp x (l w * w⁻¹) = 1
        rw [map_mul, map_inv, hd l hl, hall _ ⟨w, hw, rfl⟩ l hl, mul_inv_cancel]
      rwa [hKC] at hmem
  · left
    rw [eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    have : w ∈ K := hKJ ▸ hw
    exact (MonoidHom.mem_ker).mp this.2

omit [Finite U] in
theorem IsInvBy.iSup {L : Subgroup (MulAut U)} {ι : Sort*} {T : ι → Subgroup U}
    (h : ∀ i, IsInvBy L (T i)) : IsInvBy L (⨆ i, T i) := by
  intro l hl s hs
  refine Subgroup.iSup_induction T (C := fun x => l x ∈ ⨆ i, T i) hs
    (fun i x hx => Subgroup.mem_iSup_of_mem i (h i l hl x hx)) ?_ ?_
  · rw [map_one]; exact one_mem _
  · intro x y hx hy
    rw [map_mul]
    exact mul_mem hx hy

omit [Finite U] in
theorem isInvBy_commV_self (L : Subgroup (MulAut U)) : IsInvBy L (commV L) := by
  intro l hl s hs
  have h1 : (commV L).map l.toMonoidHom ≤ commV L := by
    rw [commV, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨_, ⟨x, hx, v, rfl⟩, rfl⟩
    refine ⟨l * x * l⁻¹, L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl), l v, ?_⟩
    simp [MulAut.mul_apply, map_mul, map_inv]
  exact h1 ⟨s, hs, rfl⟩

omit [Finite U] in
theorem disp_mem_commV {L : Subgroup (MulAut U)} {x : MulAut U} (hx : x ∈ L) (v : U) :
    disp x v ∈ commV L :=
  Subgroup.subset_closure ⟨x, hx, v, rfl⟩

@[expose] def trivOn (L : Subgroup (MulAut U)) (C : Subgroup U) : Subgroup U :=
  ⨅ l : ↥L, C.comap (disp (l : MulAut U))

omit [Finite U] in
theorem mem_trivOn {L : Subgroup (MulAut U)} {C : Subgroup U} {u : U} :
    u ∈ trivOn L C ↔ ∀ l ∈ L, disp l u ∈ C := by
  simp [trivOn, Subgroup.mem_iInf]

theorem fixV_sup_eq_bot {L₁ L₂ : Subgroup (MulAut U)}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (hirr : ∀ J : Subgroup U, IsInvBy (L₁ ⊔ L₂) J → fixV (L₁ ⊔ L₂) ≤ J →
      J = fixV (L₁ ⊔ L₂) ∨ J = ⊤)
    (hcV : commV (L₁ ⊔ L₂) = ⊤)
    (hnt₁ : ∃ l ∈ L₁, ∃ u, disp l u ∉ fixV (L₁ ⊔ L₂))
    (hnt₂ : ∃ l ∈ L₂, ∃ u, disp l u ∉ fixV (L₁ ⊔ L₂)) :
    fixV (L₁ ⊔ L₂) = ⊥ := by
  set C := fixV (L₁ ⊔ L₂) with hC
  have hfix : ∀ g ∈ L₁ ⊔ L₂, ∀ c ∈ C, g c = c := fun g hg c hc => hc g hg
  have hfix₂ : ∀ y ∈ L₂, ∀ c ∈ C, y c = c := fun y hy => hfix y ((le_sup_right : L₂ ≤ L₁ ⊔ L₂) hy)
  have hc₂ : ∀ y ∈ L₂, ∀ l ∈ L₁, l * y = y * l := fun y hy l hl => hcomm l hl y hy
  have hCtop : C < ⊤ := lt_of_le_of_ne le_top fun h => by
    obtain ⟨l, -, u, hu⟩ := hnt₁
    exact hu (h ▸ Subgroup.mem_top _)
  obtain ⟨I, hImin⟩ := exists_minimal_of_wellFoundedLT
    (fun J : Subgroup U => IsInvBy L₁ J ∧ C < J) ⟨⊤, fun _ _ _ _ => trivial, hCtop⟩
  have hI : MinOver L₁ C I :=
    ⟨hImin.1.1, hImin.1.2, fun J hJ hCJ hJI => le_antisymm hJI (hImin.2 ⟨hJ, hCJ⟩ hJI)⟩
  set T : ↥L₂ → Subgroup U := fun y => I.map (y : MulAut U).toMonoidHom with hT
  have hTmin : ∀ y : ↥L₂, MinOver L₁ C (T y) := fun y =>
    hI.map (hc₂ y y.2) (hfix₂ y y.2)
  set S := ⨆ y : ↥L₂, T y with hS
  have hS₁ : IsInvBy L₁ S := IsInvBy.iSup fun y => (hTmin y).1
  have hS₂ : IsInvBy L₂ S := by
    intro y' hy' s hs
    refine Subgroup.iSup_induction T (C := fun x => y' x ∈ S) hs ?_ ?_ ?_
    · rintro y _ ⟨u, hu, rfl⟩
      refine Subgroup.mem_iSup_of_mem ⟨y' * y, L₂.mul_mem hy' y.2⟩ ⟨u, hu, ?_⟩
      simp [MulAut.mul_apply]
    · rw [map_one]; exact one_mem _
    · intro x z hx hz
      rw [map_mul]
      exact mul_mem hx hz
  have hItop : S = ⊤ := by
    have h1 : I ≤ S := by
      have : T 1 = I := by
        simp only [hT, OneMemClass.coe_one]
        convert Subgroup.map_id I using 2
        ext u
        rfl
      exact this ▸ le_iSup T 1
    rcases hirr S (isInvBy_sup hS₁ hS₂) (hI.2.1.le.trans h1) with h | h
    · exact absurd (h ▸ h1) (not_le_of_gt hI.2.1)
    · exact h
  have hinvT : IsInvBy L₂ (trivOn L₁ C) := by
    intro y hy u hu
    rw [mem_trivOn] at hu ⊢
    intro l hl
    rw [disp_comm (hc₂ y hy l hl) u, hfix₂ y hy _ (hu l hl)]
    exact hu l hl
  have hntT : ∀ y : ↥L₂, ∃ w ∈ T y, ∃ l ∈ L₁, disp l w ∉ C := by
    intro y
    by_contra hall
    push Not at hall
    have hIle : I ≤ trivOn L₁ C := by
      intro u hu
      have h1 : (y : MulAut U) u ∈ trivOn L₁ C :=
        mem_trivOn.mpr fun l hl => hall _ ⟨u, hu, rfl⟩ l hl
      have h2 := hinvT _ (L₂.inv_mem y.2) _ h1
      simpa using h2
    have hSle : S ≤ trivOn L₁ C := iSup_le fun y' => by
      rintro _ ⟨u, hu, rfl⟩
      exact hinvT _ y'.2 _ (hIle hu)
    obtain ⟨l, hl, u, hu⟩ := hnt₁
    exact hu (mem_trivOn.mp (hSle (hItop ▸ Subgroup.mem_top u)) l hl)
  set D := commV L₂ with hD
  have hDeq : D = ⨆ p : ↥L₂ × ↥L₂, (T p.2).map (disp (p.1 : MulAut U)) := by
    apply le_antisymm
    · rw [hD, commV, Subgroup.closure_le]
      rintro _ ⟨x, hx, v, rfl⟩
      have hv : v ∈ S := hItop ▸ Subgroup.mem_top v
      have h1 : disp x v ∈ S.map (disp x) := ⟨v, hv, rfl⟩
      rw [hS, Subgroup.map_iSup] at h1
      exact (iSup_le fun y => le_iSup
        (fun p : ↥L₂ × ↥L₂ => (T p.2).map (disp (p.1 : MulAut U))) (⟨x, hx⟩, y)) h1
    · refine iSup_le fun p => ?_
      rintro _ ⟨w, -, rfl⟩
      exact disp_mem_commV p.1.2 w
  have hpieces : ∀ p : ↥L₂ × ↥L₂,
      IsIrrPiece L₁ ((T p.2).map (disp (p.1 : MulAut U))) := fun p =>
    isIrrPiece_map_disp (hTmin p.2) (hc₂ p.1 p.1.2) (hfix₂ p.1 p.1.2) (hntT p.2)
  obtain ⟨hDfix, hD₁⟩ := noFix_iSup _ hpieces
  rw [← hDeq] at hDfix hD₁
  have hDM : IsInvBy (L₁ ⊔ L₂) D := isInvBy_sup hD₁ (isInvBy_commV_self L₂)
  have hDC : D ⊔ C = ⊤ := by
    rcases hirr (D ⊔ C) (hDM.sup (isInvBy_fixV _)) le_sup_right with h | h
    · exfalso
      obtain ⟨l, hl, u, hu⟩ := hnt₂
      exact hu ((le_sup_left.trans h.le) (disp_mem_commV hl u))
    · exact h
  have hDinfC : D ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    exact hDfix c hc.1 fun l hl => hfix l ((le_sup_left : L₁ ≤ L₁ ⊔ L₂) hl) c hc.2
  have hMD : commV (L₁ ⊔ L₂) ≤ D := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨g, hg, v, rfl⟩
    obtain ⟨d, hd, c, hc, rfl⟩ := Subgroup.mem_sup.mp (hDC ▸ Subgroup.mem_top v)
    have h1 : g (d * c) * (d * c)⁻¹ = g d * d⁻¹ := by
      rw [map_mul, hfix g hg c hc, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    show g (d * c) * (d * c)⁻¹ ∈ D
    rw [h1]
    exact D.mul_mem (hDM g hg d hd) (D.inv_mem hd)
  rw [hcV] at hMD
  rw [eq_bot_iff, ← hDinfC]
  exact le_inf (le_top.trans hMD) le_rfl

end CFSG.Quasithin.SmithD37
