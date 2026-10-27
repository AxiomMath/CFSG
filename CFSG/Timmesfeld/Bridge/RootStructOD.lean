module

public import CFSG.Timmesfeld.Bridge.RootStructBasic
public import CFSG.Timmesfeld.Bridge.RootStructQD
public import CFSG.Timmesfeld.Bridge.RootStructUpper

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped commutatorElement

variable {G : Type*} [Group G] {D : Set G}

@[expose] def opposites (D : Set G) (a : G) : Set G :=
  {x | x ∈ D ∧ ¬ Commute a x ∧ Odd (orderOf (a * x))}

theorem conj_mem_opposites_iff (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (g : G) {a x : G} :
    g * x * g⁻¹ ∈ opposites D (g * a * g⁻¹) ↔ x ∈ opposites D a := by
  have hmem : g * x * g⁻¹ ∈ D ↔ x ∈ D := by
    refine ⟨fun h => ?_, conj_mem_of_isClass hclass g⟩
    have := conj_mem_of_isClass hclass g⁻¹ h
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  have hmul : g * a * g⁻¹ * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
  simp only [opposites, Set.mem_ofPred_eq, hmul, orderOf_conj_eq, Commute.conj_iff, hmem]

theorem opposites_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (g a : G) :
    opposites D (g * a * g⁻¹) = (fun x => g * x * g⁻¹) '' opposites D a := by
  ext y
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    rw [← conj_mem_opposites_iff hclass g]
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
  · rintro ⟨x, hx, rfl⟩
    exact (conj_mem_opposites_iff hclass g).2 hx

theorem opposites_conj_eq (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a b : G}
    (h : opposites D a = opposites D b) (g : G) :
    opposites D (g * a * g⁻¹) = opposites D (g * b * g⁻¹) := by
  rw [opposites_conj hclass, opposites_conj hclass, h]

theorem ncard_opposites_eq (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a b : G} (ha : a ∈ D)
    (hb : b ∈ D) : (opposites D a).ncard = (opposites D b).ncard := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass ha hb)
  rw [opposites_conj hclass, Set.ncard_image_of_injective]
  intro x y hxy
  have hxy' : g * x * g⁻¹ = g * y * g⁻¹ := hxy
  calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hxy']
    _ = y := by group

theorem opposites_eq_of_subset [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) (h : opposites D a ⊆ opposites D b) :
    opposites D a = opposites D b :=
  Set.eq_of_subset_of_ncard_le h (ncard_opposites_eq hclass hb ha).le

theorem exists_collinear (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) {a : G} (ha : a ∈ D) :
    ∃ c ∈ D, Commute a c ∧ a * c ∈ D := by
  obtain ⟨d, hd, e, he, h4⟩ := hnd
  obtain ⟨hsq, hdsq, -, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have hdsqD := mul_sq_mem_of_orderOf_eq_four hclass hD hd he h4
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass hd ha)
  refine ⟨g * (d * e) ^ 2 * g⁻¹, conj_mem_of_isClass hclass g hsq, (Commute.conj_iff g).2 hdsq,
    ?_⟩
  rw [show g * d * g⁻¹ * (g * (d * e) ^ 2 * g⁻¹) = g * (d * (d * e) ^ 2) * g⁻¹ by group]
  exact conj_mem_of_isClass hclass g hdsqD

private theorem eq_one_of_odd_of_dvd_four {m : ℕ} (hm : Odd m) (h : m ∣ 4) : m = 1 :=
  Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hm)) h

theorem opposites_mul_eq [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : Commute a b)
    (habD : a * b ∈ D) (hAB : opposites D a = opposites D b) :
    opposites D (a * b) = opposites D a := by
  have hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have ha2 := hD.mul_self_eq_one ha
  have hca : Commute (a * b) a := (Commute.refl a).mul_left hab.symm
  have hcab : a * b * a = b := by rw [hab.eq, mul_assoc, ha2, mul_one]
  have hcaD : a * b * a ∈ D := by rwa [hcab]
  refine opposites_eq_of_subset hclass habD ha fun x hx => ?_
  obtain ⟨hxD, hcx, hodd⟩ := hx
  have hax : ¬ Commute a x :=
    (not_commute_of_opposite_of_line hD habD ha hca hcaD hxD hcx hodd).1
  by_contra hxa
  have h4 : orderOf (a * x) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD ha hxD with h | h | ⟨h, h'⟩
    · exact absurd h hax
    · exact h
    · exact absurd ⟨hxD, h', h⟩ hxa
  obtain ⟨y, hyD, -, hxy, -, hyc⟩ := exists_conj_eq_mul_of_odd_special hD hN habD hxD ha hcx
    hodd ((orderOf_mul_comm_eq a x).trans h4) hca hcaD
  have h1 := (conj_mem_opposites_iff hclass y).2
    (show x ∈ opposites D (a * b) from ⟨hxD, hcx, hodd⟩)
  have e1 : y * x * y⁻¹ = x := by
    rw [hD.inv_eq hyD, ← hxy.eq, mul_assoc, hD.mul_self_eq_one hyD, mul_one]
  have e2 : y * (a * b) * y⁻¹ = b := by rw [hD.inv_eq hyD, hyc, hcab]
  rw [e1, e2, ← hAB] at h1
  exact hxa h1

theorem not_opposite_of_opposites_eq [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hX : ∀ a ∈ D, ∃ c ∈ D, Commute a c ∧ a * c ∈ D) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) (hAB : opposites D a = opposites D b) :
    ¬ (¬ Commute a b ∧ Odd (orderOf (a * b))) := by
  rintro ⟨hab, hodd⟩
  have hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have ha2 := hD.mul_self_eq_one ha
  obtain ⟨c, hcD, hac, hacD⟩ := hX a ha
  have hcb : ¬ Commute c b := (not_commute_of_opposite_of_line hD ha hcD hac hacD hb hab hodd).1
  have hcA : c ∉ opposites D b := by
    rw [← hAB]
    exact fun h => h.2.1 hac
  have h4 : orderOf (b * c) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hb hcD with h | h | ⟨h, h'⟩
    · exact absurd h.symm hcb
    · exact h
    · exact absurd ⟨hcD, h', h⟩ hcA
  obtain ⟨y, hyD, -, hby, -, hya⟩ :=
    exists_conj_eq_mul_of_odd_special hD hN ha hb hcD hab hodd h4 hac hacD
  have h1 : opposites D (a * c) = opposites D a := by
    have := opposites_conj_eq hclass hAB y
    rw [hD.inv_eq hyD, hya, ← hby.eq, mul_assoc, hD.mul_self_eq_one hyD, mul_one] at this
    rw [this, hAB]
  have h2 := opposites_mul_eq hclass hD ha hacD ((Commute.refl a).mul_right hac)
    (by rwa [← mul_assoc, ha2, one_mul]) h1.symm
  rw [← mul_assoc, ha2, one_mul] at h2
  have h3 : b ∈ opposites D c := by
    rw [h2]
    exact ⟨hb, hab, hodd⟩
  have h5 := h3.2.2
  rw [orderOf_mul_comm_eq b c, h4] at h5
  exact absurd h5 (by decide)

theorem opposites_sq_eq [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {a b : G} (ha : a ∈ D) (hb : b ∈ D) (h4 : orderOf (a * b) = 4)
    (hAB : opposites D a = opposites D b) : opposites D ((a * b) ^ 2) = opposites D a := by
  have ha2 := hD.mul_self_eq_one ha
  have hb2 := hD.mul_self_eq_one hb
  obtain ⟨hsq, hasq, -, hbab⟩ := sq_mem_of_orderOf_eq_four hD ha hb h4
  have hbabD : b * a * b ∈ D := by
    have := conj_mem_of_isClass hclass b ha
    rwa [hD.inv_eq hb] at this
  have hA' : opposites D a = opposites D (b * a * b) := by
    have := opposites_conj_eq hclass hAB b
    rw [hD.inv_eq hb, show b * b * b = b by rw [hb2, one_mul]] at this
    rw [this, hAB]
  have hcomm : Commute a (b * a * b) := by
    rw [hbab]
    exact (Commute.refl a).mul_right hasq
  have hmul : a * (b * a * b) = (a * b) ^ 2 := by rw [hbab, ← mul_assoc, ha2, one_mul]
  have := opposites_mul_eq hclass hD ha hbabD hcomm (by rw [hmul]; exact hsq) hA'
  rwa [hmul] at this

theorem isPGroup_closure_of_isPGroup_pair [Finite G] {F : Set G}
    (hinv : ∀ m ∈ Subgroup.closure F, ∀ x ∈ F, m * x * m⁻¹ ∈ F)
    (hpair : ∀ x ∈ F, ∀ y ∈ F, IsPGroup 2 (Subgroup.closure ({x, y} : Set G))) :
    IsPGroup 2 (Subgroup.closure F) := by
  set M := Subgroup.closure F
  set P : Subgroup G := (CFSG.pCore 2 M).map M.subtype
  have hP : IsPGroup 2 P := (CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2).map M.subtype
  refine hP.to_le ?_
  rw [Subgroup.closure_le]
  intro x hx
  have hxM : x ∈ M := Subgroup.subset_closure hx
  refine ⟨⟨x, hxM⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, CFSG.BaerSuzuki.baer_suzuki_iff]
  intro g
  have hpg := hpair x hx _ (hinv g g.2 x hx)
  have hle : (Subgroup.closure ({⟨x, hxM⟩, g * ⟨x, hxM⟩ * g⁻¹} : Set M)).map M.subtype ≤
      Subgroup.closure ({x, (g : G) * x * (g : G)⁻¹} : Set G) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  exact (hpg.to_le hle).of_equiv (Subgroup.equivMapOfInjective _ M.subtype
    M.subtype_injective).symm

theorem commute_of_opposites_eq [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hX : ∀ a ∈ D, ∃ c ∈ D, Commute a c ∧ a * c ∈ D) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) (hAB : opposites D a = opposites D b) : Commute a b := by
  set F : Set G := {x | x ∈ D ∧ opposites D x = opposites D a} with hF
  have hconj : ∀ x ∈ F, ∀ y ∈ F, x * y * x⁻¹ ∈ F := by
    rintro x ⟨hxD, hxA⟩ y ⟨hyD, hyA⟩
    refine ⟨conj_mem_of_isClass hclass x hyD, ?_⟩
    rw [opposites_conj_eq hclass (hyA.trans hxA.symm) x, hD.inv_eq hxD,
      show x * x * x = x by rw [hD.mul_self_eq_one hxD, one_mul], hxA]
  have hinv : ∀ m ∈ Subgroup.closure F, ∀ x ∈ F, m * x * m⁻¹ ∈ F := by
    intro m hm
    suffices h : (∀ x ∈ F, m * x * m⁻¹ ∈ F) ∧ (∀ x ∈ F, m⁻¹ * x * m ∈ F) from h.1
    induction hm using Subgroup.closure_induction with
    | mem y hy =>
      refine ⟨fun x hx => hconj y hy x hx, fun x hx => ?_⟩
      have := hconj y hy x hx
      rw [hD.inv_eq hy.1] at this ⊢
      exact this
    | one => exact ⟨fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩
    | mul y z _ _ ihy ihz =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [show y * z * x * (y * z)⁻¹ = y * (z * x * z⁻¹) * y⁻¹ by group]
        exact ihy.1 _ (ihz.1 x hx)
      · rw [show (y * z)⁻¹ * x * (y * z) = z⁻¹ * (y⁻¹ * x * y) * z by group]
        exact ihz.2 _ (ihy.2 x hx)
    | inv y _ ihy =>
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [inv_inv]
        exact ihy.2 x hx
      · rw [inv_inv]
        exact ihy.1 x hx
  have hpair : ∀ x ∈ F, ∀ y ∈ F, IsPGroup 2 (Subgroup.closure ({x, y} : Set G)) := by
    rintro x ⟨hxD, hxA⟩ y ⟨hyD, hyA⟩
    have hx2 := hD.mul_self_eq_one hxD
    have hy2 := hD.mul_self_eq_one hyD
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hxD hyD with h | h | ⟨h, h'⟩
    · exact isPGroup_two_closure_pair (k := 1) hx2 hy2
        (by rw [pow_one]; exact (commute_iff_mul_sq_eq_one hx2 hy2).1 h)
    · exact isPGroup_two_closure_pair (k := 2) hx2 hy2
        (by rw [show 2 ^ 2 = 4 by norm_num, ← h, pow_orderOf_eq_one])
    · exact absurd ⟨h', h⟩ (not_opposite_of_opposites_eq hclass hD hX hxD hyD (hxA.trans hyA.symm))
  have hM : IsPGroup 2 (Subgroup.closure F) := isPGroup_closure_of_isPGroup_pair hinv hpair
  have : Group.IsNilpotent (Subgroup.closure F) := hM.isNilpotent
  have hcomm : ∀ s ∈ F, ∀ t ∈ F, ⁅s, t⁆ = 1 ∨ ⁅s, t⁆ ∈ F := by
    rintro s ⟨hsD, hsA⟩ t ⟨htD, htA⟩
    have hs2 := hD.mul_self_eq_one hsD
    have ht2 := hD.mul_self_eq_one htD
    have e : ⁅s, t⁆ = (s * t) ^ 2 := by
      rw [commutatorElement_def, hD.inv_eq hsD, hD.inv_eq htD, sq]
      simp only [mul_assoc]
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hsD htD with h | h | ⟨h, h'⟩
    · exact Or.inl (e.trans ((commute_iff_mul_sq_eq_one hs2 ht2).1 h))
    · refine Or.inr ⟨e ▸ hD.sq_mem hsD htD h, ?_⟩
      rw [e, opposites_sq_eq hclass hD hsD htD h (hsA.trans htA.symm), hsA]
    · exact absurd ⟨h', h⟩ (not_opposite_of_opposites_eq hclass hD hX hsD htD (hsA.trans htA.symm))
  have hne : Subgroup.closure F ≠ ⊥ := by
    intro hbot
    have haF : a ∈ Subgroup.closure F := Subgroup.subset_closure ⟨ha, rfl⟩
    rw [hbot, Subgroup.mem_bot] at haF
    exact hD.ne_one ha haF
  obtain ⟨s, hs, hsM, hcen, -⟩ :=
    exists_mem_center_of_ne_bot (Subgroup.subset_closure (k := F)) rfl hcomm hne
  have hsF : ∀ y ∈ F, Commute s y := by
    intro y hy
    have := Subgroup.mem_center_iff.1 hcen ⟨y, Subgroup.subset_closure hy⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_isClass hclass hs.1 ha)
  have hy : g⁻¹ * b * g ∈ F := by
    refine ⟨?_, ?_⟩
    · have := conj_mem_of_isClass hclass g⁻¹ hb
      rwa [inv_inv] at this
    · have h1 := opposites_conj_eq hclass hAB g⁻¹
      rw [inv_inv] at h1
      have h2 : g⁻¹ * a * g = s := by rw [← hg]; group
      rw [← h1, h2, hs.2]
  have := (Commute.conj_iff g).2 (hsF _ hy)
  rwa [hg, show g * (g⁻¹ * b * g) * g⁻¹ = b by group] at this

theorem commute_of_normalizes [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hX : ∀ a ∈ D, ∃ c ∈ D, Commute a c ∧ a * c ∈ D) {d x a : G}
    (hx : x ∈ D)
    (hxF : ∀ y ∈ D, opposites D y = opposites D d → opposites D (x * y * x⁻¹) = opposites D d)
    (ha : a ∈ D) (haF : opposites D a = opposites D d) : Commute x a := by
  have hN : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D := fun g x hx => conj_mem_of_isClass hclass g hx
  have hx2 := hD.mul_self_eq_one hx
  have ha2 := hD.mul_self_eq_one ha
  by_contra hxa
  have ha'D : x * a * x ∈ D := by
    have := hN x a ha
    rwa [hD.inv_eq hx] at this
  have ha'F : opposites D (x * a * x) = opposites D d := by
    have := hxF a ha haF
    rwa [hD.inv_eq hx] at this
  have hcomm : Commute a (x * a * x) :=
    commute_of_opposites_eq hclass hD hX ha ha'D (haF.trans ha'F.symm)
  have haa' : a * (x * a * x) = (a * x) ^ 2 := by rw [sq]; simp only [mul_assoc]
  have h4 : orderOf (a * x) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD ha hx with h | h | ⟨h, -⟩
    · exact absurd h.symm hxa
    · exact h
    · have h1 : (a * x) ^ 4 = 1 := by
        rw [show 4 = 2 * 2 from rfl, pow_mul, ← haa']
        exact (commute_iff_mul_sq_eq_one ha2 (hD.mul_self_eq_one ha'D)).1 hcomm
      have h2 := eq_one_of_odd_of_dvd_four h (orderOf_dvd_of_pow_eq_one h1)
      refine absurd ?_ hxa
      rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h2), hD.inv_eq ha]
  obtain ⟨htD, hat, -, hxax⟩ := sq_mem_of_orderOf_eq_four hD ha hx h4
  have htF : opposites D ((a * x) ^ 2) = opposites D d := by
    have := opposites_mul_eq hclass hD ha ha'D hcomm (by rw [haa']; exact htD)
      (haF.trans ha'F.symm)
    rw [haa'] at this
    rw [this, haF]
  have hxd : opposites D x ≠ opposites D d := fun h =>
    hxa (commute_of_opposites_eq hclass hD hX hx ha (h.trans haF.symm))
  have h4' : orderOf (x * a) = 4 := (orderOf_mul_comm_eq a x).trans h4
  obtain ⟨-, hxsq, -, haxa⟩ := sq_mem_of_orderOf_eq_four hD hx ha h4'
  have hsq : (x * a) ^ 2 = (a * x) ^ 2 := by
    have hinv : (a * x)⁻¹ = x * a := by rw [mul_inv_rev, hD.inv_eq hx, hD.inv_eq ha]
    have h1 : (a * x) ^ 2 * (a * x) ^ 2 = 1 := by
      rw [← pow_add, show 2 + 2 = orderOf (a * x) by rw [h4], pow_orderOf_eq_one]
    rw [← hinv, inv_pow, inv_eq_of_mul_eq_one_right h1]
  have hxaD : a * x * a ∈ D := by
    have := hN a x hx
    rwa [hD.inv_eq ha] at this
  have hxxa : Commute x (a * x * a) := by
    rw [haxa]
    exact (Commute.refl x).mul_right hxsq
  have hxxa' : x * (a * x * a) = (a * x) ^ 2 := by rw [haxa, ← mul_assoc, hx2, one_mul, hsq]
  have hxaF : opposites D (a * x * a) ≠ opposites D x := by
    intro h
    have := opposites_mul_eq hclass hD hx hxaD hxxa (by rw [hxxa']; exact htD) h.symm
    rw [hxxa'] at this
    exact hxd (this.symm.trans htF)
  obtain ⟨y, hyx, hyxa⟩ : ∃ y, y ∈ opposites D x ∧ y ∉ opposites D (a * x * a) := by
    by_contra! h
    exact hxaF (opposites_eq_of_subset hclass hx hxaD h).symm
  obtain ⟨hyD, hxy, hodd⟩ := hyx
  have hxay : ¬ Commute (a * x * a) y :=
    (not_commute_of_opposite_of_line hD hx hxaD hxxa (by rw [hxxa']; exact htD) hyD hxy hodd).1
  have h4y : orderOf (y * (a * x * a)) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hxaD hyD with h | h | ⟨h, h'⟩
    · exact absurd h hxay
    · exact (orderOf_mul_comm_eq _ _).trans h
    · exact absurd ⟨hyD, h', h⟩ hyxa
  obtain ⟨e, heD, -, -, -, hexe⟩ := exists_conj_eq_mul_of_odd_special hD hN hx hyD hxaD hxy hodd
    h4y hxxa (by rw [hxxa']; exact htD)
  rw [hxxa'] at hexe
  have he2 := hD.mul_self_eq_one heD
  have hee : ∀ w : G, e * (e * w) = w := fun w => by rw [← mul_assoc, he2, one_mul]
  have hfD : e * a * e ∈ D := by
    have := hN e a ha
    rwa [hD.inv_eq heD] at this
  have hfF : opposites D (e * a * e) = opposites D x := by
    have := opposites_conj_eq hclass (haF.trans htF.symm) e
    rw [hD.inv_eq heD, ← hexe, show e * (e * x * e) * e = x by simp only [mul_assoc, hee, he2,
      mul_one]] at this
    exact this
  have hxe : ¬ (¬ Commute x e ∧ Odd (orderOf (x * e))) := by
    rintro ⟨-, hodd'⟩
    have hxe2 : (x * e) ^ 2 = a * x * a := by
      have : (x * e) ^ 2 = x * (e * x * e) := by rw [sq]; simp only [mul_assoc]
      rw [this, hexe, ← hxxa', ← mul_assoc, hx2, one_mul]
    have h1 : (x * e) ^ 4 = 1 := by
      rw [show 4 = 2 * 2 from rfl, pow_mul, hxe2, sq, hD.mul_self_eq_one hxaD]
    have h2 := eq_one_of_odd_of_dvd_four hodd' (orderOf_dvd_of_pow_eq_one h1)
    rw [orderOf_eq_one_iff] at h2
    rw [h2, one_pow] at hxe2
    exact hD.ne_one hxaD hxe2.symm
  have hfe : ¬ Commute (e * a * e) e := by
    intro h
    have hfa : e * (e * a * e) * e = a := by simp only [mul_assoc, hee, he2, mul_one]
    rw [← h.eq, mul_assoc, he2, mul_one] at hfa
    exact hxd ((hfF.symm.trans (by rw [hfa])).trans haF)
  have hfe4 : orderOf (e * a * e * e) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hfD heD with h | h | ⟨h, h'⟩
    · exact absurd h hfe
    · exact h
    · have : e ∈ opposites D x := hfF ▸ ⟨heD, h', h⟩
      exact absurd ⟨this.2.1, this.2.2⟩ hxe
  obtain ⟨-, hfsq, -, hefe⟩ := sq_mem_of_orderOf_eq_four hD hfD heD hfe4
  have hfa : Commute (e * a * e) a := by
    have h1 : e * (e * a * e) * e = a := by simp only [mul_assoc, hee, he2, mul_one]
    have h2 : Commute (e * a * e) (e * (e * a * e) * e) := by
      rw [hefe]
      exact (Commute.refl _).mul_right hfsq
    rwa [h1] at h2
  apply hxaF
  have := opposites_conj_eq hclass hfF.symm a
  rw [hD.inv_eq ha, show a * (e * a * e) * a = e * a * e by
    rw [← hfa.eq, mul_assoc, ha2, mul_one]] at this
  rw [this, hfF]

theorem oppositeDetermines_of_isClass [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hX : ∀ a ∈ D, ∃ c ∈ D, Commute a c ∧ a * c ∈ D) :
    OppositeDetermines D := by
  intro d hd e he hde
  have hA : opposites D d = opposites D e := by
    ext x
    exact ⟨fun ⟨hx, h⟩ => ⟨hx, (hde x hx).1 h⟩, fun ⟨hx, h⟩ => ⟨hx, (hde x hx).2 h⟩⟩
  have key : ∀ u ∈ D, ∀ v ∈ D, opposites D u = opposites D v → ∀ f ∈ D, Commute u f →
      Commute v f := by
    intro u hu v hv huv f hf huf
    have hnorm : ∀ y ∈ D, opposites D y = opposites D u →
        opposites D (f * y * f⁻¹) = opposites D u := by
      intro y _ hyu
      rw [opposites_conj_eq hclass hyu f, ← huf.eq, mul_inv_cancel_right]
    exact (commute_of_normalizes hclass hD hX hf hnorm hv huv.symm).symm
  exact ⟨he, fun f hf => ⟨key e he d hd hA.symm f hf, key d hd e he hA f hf⟩⟩

theorem oppositeDetermines_of_hyp (h : Hyp G D) : OppositeDetermines D := by
  have := h.finite
  exact oppositeDetermines_of_isClass h.isClass h.root
    fun a ha => exists_collinear h.isClass h.root h.nondeg ha

theorem oppositeDeterminesStep : OppositeDeterminesStep :=
  fun _ _ _ h _ => oppositeDetermines_of_hyp h

end CFSG.Timmesfeld.Bridge
