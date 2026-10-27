module

public import CFSG.Quasithin.AppendixH.Common.OctadAltHom
public import CFSG.Quasithin.AppendixH.Common.OctadAltFix

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

private theorem smul_finset_eq_map_perm {α : Type*} [DecidableEq α]
    (g : Equiv.Perm α) (s : Finset α) : g • s = s.map g.toEmbedding := by
  rw [Finset.smul_finset_def, Finset.map_eq_image]
  rfl

private def restrictPermHom {K α : Type*} [Group K] [DecidableEq α] {p : α → Prop}
    [DecidablePred p] (act : K →* Equiv.Perm α)
    (hinv : ∀ g : K, ∀ x, p (act g x) ↔ p x) : K →* Equiv.Perm (Subtype p) where
  toFun g := (act g).subtypePerm (hinv g)
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change act 1 ↑x = (x : α)
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change act (g * h) ↑x = act g (act h ↑x)
    rw [map_mul]
    rfl

private theorem subtypePerm_eq_one_iff {α : Type*} [DecidableEq α] {p : α → Prop}
    [DecidablePred p] {f : Equiv.Perm α} (h₁ : ∀ x, p (f x) ↔ p x)
    (h₂ : ∀ x, f x ≠ x → p x) : f.subtypePerm h₁ = 1 ↔ f = 1 := by
  constructor
  · intro h
    have h' := congrArg (Equiv.Perm.ofSubtype (p := p)) h
    rwa [Equiv.Perm.ofSubtype_subtypePerm h₁ h₂, map_one] at h'
  · intro h
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change f ↑x = (x : α)
    rw [h]
    rfl

private noncomputable def octEquiv {O : Finset (Fin 24)} {o : Fin 8 → Fin 24}
    (ho : Function.Injective o) (hoO : ∀ x, x ∈ O ↔ ∃ p, o p = x) : Fin 8 ≃ ↥O :=
  Equiv.ofBijective (fun p => (⟨o p, (hoO (o p)).mpr ⟨p, rfl⟩⟩ : ↥O)) (by
    constructor
    · intro p q h
      exact ho (Subtype.ext_iff.mp h)
    · intro x
      obtain ⟨p, hp⟩ := (hoO x.1).mp x.2
      exact ⟨p, Subtype.ext hp⟩)

private theorem exists_hom_alt_compl {O : Finset (Fin 24)}
    (hO : IsOctad O) {H : Subgroup S24} {Z : Finset ↥O}
    (hHex : ∀ g, g ∈ H ↔ g ∈ octStab O ∧ ∀ z ∈ Z, (g : S24) ↑z = ↑z)
    {n : ℕ} (hcard : Fintype.card {x : ↥O // x ∉ Z} = n) :
    ∃ π : ↥H →* ↥(alternatingGroup (Fin n)), Function.Surjective π ∧
      π.ker = (octFix O).subgroupOf H := by
  classical
  have hHle : H ≤ octStab O := fun g hg => ((hHex g).mp hg).1
  let incl : ↥H →* ↥(octStab O) := Subgroup.inclusion hHle
  let act : ↥H →* Equiv.Perm ↥O := (octAct O).comp incl
  have hact_apply : ∀ (g : ↥H) (x : ↥O), (act g x : Fin 24) = (g : S24) (x : Fin 24) := by
    intro g x
    show (octAct O (incl g) x : Fin 24) = (g : S24) (x : Fin 24)
    rw [octAct_apply, Subgroup.coe_inclusion]
  let p : ↥O → Prop := fun x => x ∉ Z
  have hfixZ : ∀ g : ↥H, ∀ z ∈ Z, act g z = z := by
    intro g z hz
    apply Subtype.ext
    rw [hact_apply]
    exact ((hHex (g : S24)).mp g.2).2 z hz
  have hinv : ∀ g : ↥H, ∀ x, p (act g x) ↔ p x := by
    intro g x
    have hZg : act g x ∈ Z ↔ x ∈ Z := by
      constructor
      · intro hy
        have h2 : act g x = x := (act g).injective (hfixZ g (act g x) hy)
        exact h2 ▸ hy
      · intro hx
        rw [hfixZ g x hx]
        exact hx
    exact not_congr hZg
  let φ : ↥H →* Equiv.Perm {x : ↥O // p x} := restrictPermHom act hinv
  let e : {x : ↥O // p x} ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let π' : ↥H →* Equiv.Perm (Fin n) := (e.permCongrHom).toMonoidHom.comp φ
  have hsign_act : ∀ g : ↥H, Equiv.Perm.sign (act g) = 1 := by
    intro g
    have hmem : octAct O ⟨(g : S24), hHle g.2⟩ ∈ alternatingGroup ↥O := by
      have h := (octActAlt hO ⟨(g : S24), hHle g.2⟩).2
      rwa [octActAlt_apply] at h
    show Equiv.Perm.sign (octAct O ⟨(g : S24), hHle g.2⟩) = 1
    exact Equiv.Perm.mem_alternatingGroup.mp hmem
  have hmem_alt : ∀ g : ↥H, π' g ∈ alternatingGroup (Fin n) := by
    intro g
    change e.permCongr (φ g) ∈ alternatingGroup (Fin n)
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
    show Equiv.Perm.sign ((act g).subtypePerm (hinv g)) = 1
    rw [Equiv.Perm.sign_subtypePerm (act g) (hinv g) (fun x hx hxZ => hx (hfixZ g x hxZ))]
    exact hsign_act g
  let π : ↥H →* ↥(alternatingGroup (Fin n)) :=
    π'.codRestrict (alternatingGroup (Fin n)) hmem_alt
  have hsurj : Function.Surjective π := by
    intro c
    let d : Equiv.Perm {x : ↥O // p x} := e.permCongr.symm (c : Equiv.Perm (Fin n))
    have hed : e.permCongr d = (c : Equiv.Perm (Fin n)) := Equiv.apply_symm_apply _ _
    have hdmem : d ∈ alternatingGroup {x : ↥O // p x} := by
      rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_permCongr e d, hed]
      exact Equiv.Perm.mem_alternatingGroup.mp c.2
    let s : Equiv.Perm ↥O := Equiv.Perm.ofSubtype d
    have hs1 : Equiv.Perm.sign s = 1 := by
      rw [Equiv.Perm.sign_ofSubtype]
      exact Equiv.Perm.mem_alternatingGroup.mp hdmem
    obtain ⟨g, hg⟩ := octActAlt_surjective hO ⟨s, Equiv.Perm.mem_alternatingGroup.mpr hs1⟩
    have hgact : octAct O g = s := by
      have h := congrArg Subtype.val hg
      rwa [octActAlt_apply] at h
    have hgH : (g : S24) ∈ H := by
      rw [hHex]
      refine ⟨g.2, fun z hz => ?_⟩
      have hsz : s z = z :=
        Equiv.Perm.ofSubtype_apply_of_not_mem d (by simpa [p] using hz)
      have h1 : octAct O g z = z := by rw [hgact]; exact hsz
      have h2 := congrArg (fun w : ↥O => (w : Fin 24)) h1
      simpa [octAct_apply] using h2
    refine ⟨⟨(g : S24), hgH⟩, ?_⟩
    apply Subtype.ext
    show π' ⟨(g : S24), hgH⟩ = (c : Equiv.Perm (Fin n))
    have hφ : φ ⟨(g : S24), hgH⟩ = d := by
      have hact : act ⟨(g : S24), hgH⟩ = s := by
        change octAct O (incl ⟨(g : S24), hgH⟩) = s
        rw [show incl ⟨(g : S24), hgH⟩ = g from Subtype.ext rfl, hgact]
      apply Equiv.ext
      intro x
      apply Subtype.ext
      change act ⟨(g : S24), hgH⟩ ↑x = ↑(d x)
      rw [hact]
      change Equiv.Perm.ofSubtype d ↑x = ↑(d x)
      exact Equiv.Perm.ofSubtype_apply_of_mem d x.2
    have hF : π' ⟨(g : S24), hgH⟩ = e.permCongr (φ ⟨(g : S24), hgH⟩) := rfl
    rw [hF, hφ, hed]
  refine ⟨π, hsurj, ?_⟩
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hh
    have hπ' : π' h = 1 := by
      have hval := congrArg (fun x : ↥(alternatingGroup (Fin n)) => (x : Equiv.Perm (Fin n))) hh
      change π' h = 1 at hval
      exact hval
    have hφ : φ h = 1 := (e.permCongrHom.map_eq_one_iff).mp hπ'
    have hsub : (act h).subtypePerm (hinv h) = 1 := hφ
    have hact : act h = 1 :=
      (subtypePerm_eq_one_iff (hinv h) (fun x hx hxZ => hx (hfixZ h x hxZ))).mp hsub
    have hmem : incl h ∈ (octFix O).subgroupOf (octStab O) := by
      rw [← ker_octAct O, MonoidHom.mem_ker]
      exact hact
    exact Subgroup.mem_subgroupOf.mp hmem
  · intro hh
    have hact : act h = 1 := by
      change octAct O (incl h) = 1
      rw [← MonoidHom.mem_ker, ker_octAct O]
      exact Subgroup.mem_subgroupOf.mpr (by rw [Subgroup.coe_inclusion hHle h]; exact hh)
    have hφ : φ h = 1 := by
      apply Equiv.ext
      intro x
      apply Subtype.ext
      change act h ↑x = (x : ↥O)
      rw [hact]
      rfl
    have hπ' : π' h = 1 := by
      show e.permCongrHom (φ h) = 1
      rw [hφ, map_one]
    exact Subtype.ext hπ'

theorem exists_perm_of_octStab {O : Finset (Fin 24)}
    (hO : IsOctad O) {o : Fin 8 → Fin 24} (ho : Function.Injective o)
    (hoO : ∀ x, x ∈ O ↔ ∃ p, o p = x) {g : S24} (hg : g ∈ octStab O) :
    ∃ σ ∈ alternatingGroup (Fin 8), ∀ p, g (o p) = o (σ p) := by
  classical
  let e : Fin 8 ≃ ↥O := octEquiv ho hoO
  have he : ∀ p, (e p : Fin 24) = o p := fun p => rfl
  let σ : Equiv.Perm (Fin 8) := e.symm.permCongr (octAct O ⟨g, hg⟩)
  have hσ : σ ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.mp (by
      have h := (octActAlt hO ⟨g, hg⟩).2
      rwa [octActAlt_apply] at h)
  refine ⟨σ, hσ, fun p => ?_⟩
  have h1 : e (σ p) = octAct O ⟨g, hg⟩ (e p) := by
    show e (e.symm (octAct O ⟨g, hg⟩ (e p))) = _
    rw [Equiv.apply_symm_apply]
  have h2 : o (σ p) = (g : S24) (o p) := by
    have h := congrArg (fun x : ↥O => (x : Fin 24)) h1
    rw [he (σ p), octAct_apply, he p] at h
    exact h
  exact h2.symm

theorem exists_octStab_of_perm {O : Finset (Fin 24)}
    (hO : IsOctad O) {o : Fin 8 → Fin 24} (ho : Function.Injective o)
    (hoO : ∀ x, x ∈ O ↔ ∃ p, o p = x) {σ : Equiv.Perm (Fin 8)}
    (hσ : σ ∈ alternatingGroup (Fin 8)) :
    ∃ g ∈ octStab O, ∀ p, g (o p) = o (σ p) := by
  classical
  let e : Fin 8 ≃ ↥O := octEquiv ho hoO
  have he : ∀ p, (e p : Fin 24) = o p := fun p => rfl
  let σ' : Equiv.Perm ↥O := e.permCongr σ
  have hσ' : σ' ∈ alternatingGroup ↥O := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
    exact Equiv.Perm.mem_alternatingGroup.mp hσ
  obtain ⟨g, hg⟩ := octActAlt_surjective hO ⟨σ', hσ'⟩
  have hgact : octAct O g = σ' := by
    have h := congrArg Subtype.val hg
    rwa [octActAlt_apply] at h
  refine ⟨g, g.2, fun p => ?_⟩
  have h1 : octAct O g (e p) = e (σ p) := by
    rw [hgact]
    show e (σ (e.symm (e p))) = e (σ p)
    rw [Equiv.symm_apply_apply]
  have h2 : (g : S24) (o p) = o (σ p) := by
    have h := congrArg (fun x : ↥O => (x : Fin 24)) h1
    rw [octAct_apply, he p, he (σ p)] at h
    exact h
  exact h2

theorem exists_hom_alt8 {O : Finset (Fin 24)} (hO : IsOctad O)
    {H : Subgroup S24} (hH : H = octStab O) :
    ∃ π : ↥H →* ↥(alternatingGroup (Fin 8)), Function.Surjective π ∧
      π.ker = (octFix O).subgroupOf H := by
  classical
  subst hH
  have hcard : Fintype.card ↥O = 8 := by rw [Fintype.card_coe, hO.1]
  let e : ↥O ≃ Fin 8 := Fintype.equivFinOfCardEq hcard
  refine ⟨(Equiv.altCongrHom e).toMonoidHom.comp (octActAlt hO), ?_, ?_⟩
  · intro c
    obtain ⟨a, ha⟩ := (Equiv.altCongrHom e).surjective c
    obtain ⟨g, hg⟩ := octActAlt_surjective hO a
    exact ⟨g, by rw [MonoidHom.comp_apply, hg]; simpa using ha⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ (Equiv.altCongrHom e).injective, ker_octActAlt hO]

theorem exists_hom_alt7 {O : Finset (Fin 24)} (hO : IsOctad O)
    {a : Fin 24} (ha : a ∈ O) {H : Subgroup S24} (hH : ∀ g, g ∈ H ↔ g ∈ octStab O ∧ g a = a) :
    ∃ π : ↥H →* ↥(alternatingGroup (Fin 7)), Function.Surjective π ∧
      π.ker = (octFix O).subgroupOf H := by
  classical
  let Z : Finset ↥O := {(⟨a, ha⟩ : ↥O)}
  have hHex : ∀ g, g ∈ H ↔ g ∈ octStab O ∧ ∀ z ∈ Z, (g : S24) ↑z = ↑z := by
    intro g
    rw [hH g]
    constructor
    · rintro ⟨hgM, hga⟩
      exact ⟨hgM, fun z hz => by
        rw [show z = (⟨a, ha⟩ : ↥O) by simpa [Z] using hz]
        exact hga⟩
    · rintro ⟨hgM, hfix⟩
      exact ⟨hgM, hfix ⟨a, ha⟩ (by simp [Z])⟩
  have hcardZ : Z.card = 1 := by simp [Z]
  have hcardO : Fintype.card ↥O = 8 := by rw [Fintype.card_coe, hO.1]
  have hcard : Fintype.card {x : ↥O // x ∉ Z} = 7 := by
    rw [Fintype.card_subtype_compl (fun x : ↥O => x ∈ Z), Fintype.card_coe Z, hcardZ, hcardO]
  exact exists_hom_alt_compl hO hHex hcard

theorem exists_hom_alt6 {O : Finset (Fin 24)} (hO : IsOctad O)
    {a b : Fin 24} (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b) {H : Subgroup S24}
    (hH : ∀ g, g ∈ H ↔ g ∈ octStab O ∧ g a = a ∧ g b = b) :
    ∃ π : ↥H →* ↥(alternatingGroup (Fin 6)), Function.Surjective π ∧
      π.ker = (octFix O).subgroupOf H := by
  classical
  let za : ↥O := ⟨a, ha⟩
  let zb : ↥O := ⟨b, hb⟩
  have hzab : za ≠ zb := fun h => hab (Subtype.ext_iff.mp h)
  let Z : Finset ↥O := {za, zb}
  have hHex : ∀ g, g ∈ H ↔ g ∈ octStab O ∧ ∀ z ∈ Z, (g : S24) ↑z = ↑z := by
    intro g
    rw [hH g]
    constructor
    · rintro ⟨hgM, hga, hgb⟩
      exact ⟨hgM, fun z hz => by
        simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hga
        · exact hgb⟩
    · rintro ⟨hgM, hfix⟩
      exact ⟨hgM, hfix za (by simp [Z]), hfix zb (by simp [Z])⟩
  have hcardZ : Z.card = 2 := by simp [Z, hzab]
  have hcardO : Fintype.card ↥O = 8 := by rw [Fintype.card_coe, hO.1]
  have hcard : Fintype.card {x : ↥O // x ∉ Z} = 6 := by
    rw [Fintype.card_subtype_compl (fun x : ↥O => x ∈ Z), Fintype.card_coe Z, hcardZ, hcardO]
  exact exists_hom_alt_compl hO hHex hcard

theorem exists_hom_perm6 {O : Finset (Fin 24)} (hO : IsOctad O)
    {a b : Fin 24} (ha : a ∈ O) (hb : b ∈ O) (hab : a ≠ b) {H : Subgroup S24}
    (hH : ∀ g, g ∈ H ↔ g ∈ octStab O ∧ ((g a = a ∧ g b = b) ∨ (g a = b ∧ g b = a))) :
    ∃ π : ↥H →* Equiv.Perm (Fin 6), Function.Surjective π ∧
      π.ker = (octFix O).subgroupOf H := by
  classical
  have hHle : H ≤ octStab O := fun g hg => ((hH g).mp hg).1
  let incl : ↥H →* ↥(octStab O) := Subgroup.inclusion hHle
  let act : ↥H →* Equiv.Perm ↥O := (octAct O).comp incl
  let za : ↥O := ⟨a, ha⟩
  let zb : ↥O := ⟨b, hb⟩
  have hzab : za ≠ zb := fun h => hab (Subtype.ext_iff.mp h)
  let Z : Finset ↥O := {za, zb}
  let p : ↥O → Prop := fun x => x ∉ Z
  have hact_apply : ∀ (g : ↥H) (x : ↥O), (act g x : Fin 24) = (g : S24) (x : Fin 24) := by
    intro g x
    show (octAct O (incl g) x : Fin 24) = (g : S24) (x : Fin 24)
    rw [octAct_apply, Subgroup.coe_inclusion]
  have hZact : ∀ g : ↥H,
      (act g za = za ∧ act g zb = zb) ∨ (act g za = zb ∧ act g zb = za) := by
    intro g
    rcases ((hH (g : S24)).mp g.2).2 with ⟨hga, hgb⟩ | ⟨hga, hgb⟩
    · left
      constructor
      · apply Subtype.ext; rw [hact_apply]; exact hga
      · apply Subtype.ext; rw [hact_apply]; exact hgb
    · right
      constructor
      · apply Subtype.ext; rw [hact_apply]; exact hga
      · apply Subtype.ext; rw [hact_apply]; exact hgb
  have himage : ∀ g : ↥H, ∀ z ∈ Z, act g z ∈ Z := by
    intro g z hz
    simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl
    · rcases hZact g with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · rcases hZact g with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact Or.inr h2
      · exact Or.inl h2
  have hZsmul : ∀ g : ↥H, act g • Z = Z := by
    intro g
    rw [smul_finset_eq_map_perm]
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rw [Finset.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact himage g z hz
    · rw [Finset.card_map]
  have hZmem : ∀ g : ↥H, ∀ x, act g x ∈ Z ↔ x ∈ Z := by
    intro g x
    have h : Z.map (act g).toEmbedding = Z := by
      rw [← smul_finset_eq_map_perm (act g) Z]
      exact hZsmul g
    constructor
    · intro hx
      have hx' : act g x ∈ Z.map (act g).toEmbedding := by rw [h]; exact hx
      rwa [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hx'
    · intro hx
      have hx' : act g x ∈ Z.map (act g).toEmbedding := by
        rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
        exact hx
      rwa [h] at hx'
  have hinv : ∀ g : ↥H, ∀ x, p (act g x) ↔ p x := fun g x => not_congr (hZmem g x)
  let φ : ↥H →* Equiv.Perm {x : ↥O // p x} := restrictPermHom act hinv
  have hcardZ : Z.card = 2 := by simp [Z, hzab]
  have hcardO : Fintype.card ↥O = 8 := by rw [Fintype.card_coe, hO.1]
  have hcard6 : Fintype.card {x : ↥O // p x} = 6 := by
    rw [Fintype.card_subtype_compl (fun x : ↥O => x ∈ Z), Fintype.card_coe Z, hcardZ, hcardO]
  let e6 : {x : ↥O // p x} ≃ Fin 6 := Fintype.equivFinOfCardEq hcard6
  let π : ↥H →* Equiv.Perm (Fin 6) := (e6.permCongrHom).toMonoidHom.comp φ
  have hsurj : Function.Surjective π := by
    intro c
    let d : Equiv.Perm {x : ↥O // p x} := e6.permCongr.symm c
    have hed : e6.permCongr d = c := Equiv.apply_symm_apply _ _
    have hsp_of_image : ∀ u : Equiv.Perm ↥O, (∀ z ∈ Z, u z ∈ Z) → ∀ x, p (u x) ↔ p x := by
      intro u him x
      have hZsmul_u : u • Z = Z := by
        rw [smul_finset_eq_map_perm]
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          rw [Finset.mem_map] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          exact him z hz
        · rw [Finset.card_map]
      have h : Z.map u.toEmbedding = Z := by
        rw [← smul_finset_eq_map_perm u Z]
        exact hZsmul_u
      have hZu : u x ∈ Z ↔ x ∈ Z := by
        constructor
        · intro hx
          have hx' : u x ∈ Z.map u.toEmbedding := by rw [h]; exact hx
          rwa [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hx'
        · intro hx
          have hx' : u x ∈ Z.map u.toEmbedding := by
            rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
            exact hx
          rwa [h] at hx'
      exact not_congr hZu
    have key : ∀ s : Equiv.Perm ↥O, Equiv.Perm.sign s = 1 →
        ∀ (hsp : ∀ x, p (s x) ↔ p x), s.subtypePerm hsp = d →
        ∃ g : ↥H, π g = c := by
      intro s hs1 hsp hsr
      have hZpres : ∀ x, s x ∈ Z ↔ x ∈ Z := fun x => by
        simpa only [p, not_not] using not_congr (hsp x)
      have hsalt : s ∈ alternatingGroup ↥O := Equiv.Perm.mem_alternatingGroup.mpr hs1
      obtain ⟨g, hg⟩ := octActAlt_surjective hO ⟨s, hsalt⟩
      have hgact : octAct O g = s := by
        have h := congrArg Subtype.val hg
        rwa [octActAlt_apply] at h
      have hgH : (g : S24) ∈ H := by
        rw [hH (g : S24)]
        refine ⟨g.2, ?_⟩
        have hza_img : s za ∈ Z := (hZpres za).mpr (by simp [Z])
        have hzb_img : s zb ∈ Z := (hZpres zb).mpr (by simp [Z])
        simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hza_img hzb_img
        rcases hza_img with h1 | h1
        · left
          have h2 : s zb = zb := by
            rcases hzb_img with h2 | h2
            · exact absurd (s.injective (h2.trans h1.symm)) hzab.symm
            · exact h2
          constructor
          · have h1' : octAct O g za = za := by rw [hgact]; exact h1
            have h := congrArg (fun w : ↥O => (w : Fin 24)) h1'
            simpa [octAct_apply] using h
          · have h2' : octAct O g zb = zb := by rw [hgact]; exact h2
            have h := congrArg (fun w : ↥O => (w : Fin 24)) h2'
            simpa [octAct_apply] using h
        · right
          have h2 : s zb = za := by
            rcases hzb_img with h2 | h2
            · exact h2
            · exact absurd (s.injective (h2.trans h1.symm)) hzab.symm
          constructor
          · have h1' : octAct O g za = zb := by rw [hgact]; exact h1
            have h := congrArg (fun w : ↥O => (w : Fin 24)) h1'
            simpa [octAct_apply] using h
          · have h2' : octAct O g zb = za := by rw [hgact]; exact h2
            have h := congrArg (fun w : ↥O => (w : Fin 24)) h2'
            simpa [octAct_apply] using h
      refine ⟨⟨(g : S24), hgH⟩, ?_⟩
      have hφ_eq : φ ⟨(g : S24), hgH⟩ = d := by
        have hact : act ⟨(g : S24), hgH⟩ = s := by
          change octAct O (incl ⟨(g : S24), hgH⟩) = s
          rw [show incl ⟨(g : S24), hgH⟩ = g from Subtype.ext rfl, hgact]
        have h1 : φ ⟨(g : S24), hgH⟩ = s.subtypePerm hsp := by
          apply Equiv.ext
          intro x
          apply Subtype.ext
          change act ⟨(g : S24), hgH⟩ ↑x = s ↑x
          rw [hact]
        rw [h1, hsr]
      show π ⟨(g : S24), hgH⟩ = c
      show e6.permCongr (φ ⟨(g : S24), hgH⟩) = c
      rw [hφ_eq, hed]
    by_cases hd : Equiv.Perm.sign d = 1
    · let s₀ : Equiv.Perm ↥O := Equiv.Perm.ofSubtype d
      have hs0_fix : ∀ z ∈ Z, s₀ z = z := fun z hz =>
        Equiv.Perm.ofSubtype_apply_of_not_mem d (by simpa [p] using hz)
      have hsp0 : ∀ x, p (s₀ x) ↔ p x :=
        hsp_of_image s₀ (fun z hz => by rw [hs0_fix z hz]; exact hz)
      have hsr0 : s₀.subtypePerm hsp0 = d := by
        refine Equiv.ext fun x => Subtype.ext ?_
        change s₀ ↑x = ↑(d x)
        change Equiv.Perm.ofSubtype d ↑x = ↑(d x)
        exact Equiv.Perm.ofSubtype_apply_of_mem d x.2
      have hs0_sign : Equiv.Perm.sign s₀ = 1 := by
        rw [Equiv.Perm.sign_ofSubtype]
        exact hd
      exact key s₀ hs0_sign hsp0 hsr0
    · have hsign_d : Equiv.Perm.sign d = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign d) with h | h
        · exact absurd h hd
        · exact h
      let s₀ : Equiv.Perm ↥O := Equiv.Perm.ofSubtype d
      let t : Equiv.Perm ↥O := Equiv.swap za zb
      have ht_image : ∀ z ∈ Z, t z ∈ Z := by
        intro z hz
        simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
        rcases hz with rfl | rfl
        · exact Or.inr (Equiv.swap_apply_left za zb)
        · exact Or.inl (Equiv.swap_apply_right za zb)
      have hs0_fix : ∀ z ∈ Z, s₀ z = z := fun z hz =>
        Equiv.Perm.ofSubtype_apply_of_not_mem d (by simpa [p] using hz)
      have hsp_t : ∀ x, p ((t * s₀) x) ↔ p x :=
        hsp_of_image (t * s₀) (fun z hz => by
          rw [Equiv.Perm.mul_apply, hs0_fix z hz]
          exact ht_image z hz)
      have hsr_t : (t * s₀).subtypePerm hsp_t = d := by
        refine Equiv.ext fun x => Subtype.ext ?_
        change (t * s₀) ↑x = ↑(d x)
        rw [Equiv.Perm.mul_apply]
        have hs0x : s₀ ↑x = ↑(d x) := by
          change Equiv.Perm.ofSubtype d ↑x = ↑(d x)
          exact Equiv.Perm.ofSubtype_apply_of_mem d x.2
        rw [hs0x]
        exact Equiv.swap_apply_of_ne_of_ne (fun h => (d x).2 (by rw [h]; simp [Z]))
          (fun h => (d x).2 (by rw [h]; simp [Z]))
      have ht_sign : Equiv.Perm.sign (t * s₀) = 1 := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hzab, Equiv.Perm.sign_ofSubtype, hsign_d]
        decide
      exact key (t * s₀) ht_sign hsp_t hsr_t
  have hker : π.ker = (octFix O).subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hh
      have hφ : φ h = 1 := (e6.permCongrHom.map_eq_one_iff).mp (by
        change e6.permCongrHom (φ h) = 1
        exact hh)
      have hsub : (act h).subtypePerm (hinv h) = 1 := hφ
      have hact_fix : ∀ x, x ∉ Z → act h x = x := by
        intro x hx
        have h := congrArg (fun u : Equiv.Perm {y : ↥O // p y} => (u ⟨x, hx⟩ : ↥O)) hsub
        simpa [Equiv.Perm.subtypePerm_apply, Equiv.Perm.one_apply] using h
      have heven : act h ∈ alternatingGroup ↥O := by
        have h := (octActAlt hO (incl h)).2
        rwa [octActAlt_apply] at h
      have hZle : Z.card ≤ 2 := by
        rw [show Z = ({za, zb} : Finset ↥O) from rfl]
        calc ({za, zb} : Finset ↥O).card ≤ ({zb} : Finset ↥O).card + 1 :=
              Finset.card_insert_le za _
          _ = 2 := by simp
      have hact1 : act h = 1 := eq_one_of_even_of_fix_compl Z hZle heven hact_fix
      have hmem : incl h ∈ (octFix O).subgroupOf (octStab O) := by
        rw [← ker_octAct O, MonoidHom.mem_ker]
        exact hact1
      exact Subgroup.mem_subgroupOf.mp hmem
    · intro hh
      have hact : act h = 1 := by
        change octAct O (incl h) = 1
        rw [← MonoidHom.mem_ker, ker_octAct O]
        exact Subgroup.mem_subgroupOf.mpr (by rw [Subgroup.coe_inclusion hHle h]; exact hh)
      have hφ : φ h = 1 := by
        apply Equiv.ext
        intro x
        apply Subtype.ext
        change act h ↑x = (x : ↥O)
        rw [hact]
        rfl
      have hπ : π h = 1 := by
        show e6.permCongrHom (φ h) = 1
        rw [hφ, map_one]
      exact hπ
  exact ⟨π, hsurj, hker⟩

theorem nonempty_alt_stab_equiv (p : Fin 8) :
    Nonempty (↥(alternatingGroup (Fin 8) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) p) ≃*
      ↥(alternatingGroup (Fin 7))) := by
  classical
  let G : Subgroup (Equiv.Perm (Fin 8)) :=
    alternatingGroup (Fin 8) ⊓ MulAction.stabilizer (Equiv.Perm (Fin 8)) p
  let Z : Finset (Fin 8) := {p}
  let q : Fin 8 → Prop := fun x => x ∉ Z
  have hcard : Fintype.card {x : Fin 8 // q x} = 7 := by
    rw [Fintype.card_subtype_compl (fun x : Fin 8 => x ∈ Z), Fintype.card_coe Z,
      Fintype.card_fin]
    norm_num [Z]
  let e : {x : Fin 8 // q x} ≃ Fin 7 := Fintype.equivFinOfCardEq hcard
  have hfixp : ∀ g : ↥G, (g : Equiv.Perm (Fin 8)) p = p := by
    intro g
    have h := (Subgroup.mem_inf.mp g.2).2
    rwa [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at h
  have hZmem : ∀ g : ↥G, ∀ x, (g : Equiv.Perm (Fin 8)) x ∈ Z ↔ x ∈ Z := by
    intro g x
    simp only [Z, Finset.mem_singleton]
    constructor
    · intro h
      exact (g : Equiv.Perm (Fin 8)).injective (by rw [h, hfixp g])
    · intro h
      rw [h]
      exact hfixp g
  have hinv : ∀ g : ↥G, ∀ x, q ((g : Equiv.Perm (Fin 8)) x) ↔ q x :=
    fun g x => not_congr (hZmem g x)
  let φ : ↥G →* Equiv.Perm {x : Fin 8 // q x} := restrictPermHom G.subtype hinv
  let F' : ↥G →* Equiv.Perm (Fin 7) := (e.permCongrHom).toMonoidHom.comp φ
  have h2 : ∀ g : ↥G, ∀ x, (g : Equiv.Perm (Fin 8)) x ≠ x → q x := by
    intro g x hx hxZ
    exact hx (by rw [show x = p by simpa [Z] using hxZ, hfixp g])
  have hmem : ∀ g : ↥G, F' g ∈ alternatingGroup (Fin 7) := by
    intro g
    change e.permCongr (φ g) ∈ alternatingGroup (Fin 7)
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_permCongr]
    show Equiv.Perm.sign (((g : Equiv.Perm (Fin 8))).subtypePerm (hinv g)) = 1
    rw [Equiv.Perm.sign_subtypePerm (g : Equiv.Perm (Fin 8)) (hinv g) (h2 g)]
    exact Equiv.Perm.mem_alternatingGroup.mp (Subgroup.mem_inf.mp g.2).1
  let F : ↥G →* ↥(alternatingGroup (Fin 7)) := F'.codRestrict (alternatingGroup (Fin 7)) hmem
  have hsurj : Function.Surjective F := by
    intro c
    let d : Equiv.Perm {x : Fin 8 // q x} := e.permCongr.symm (c : Equiv.Perm (Fin 7))
    have hed : e.permCongr d = (c : Equiv.Perm (Fin 7)) := Equiv.apply_symm_apply _ _
    have hdmem : d ∈ alternatingGroup {x : Fin 8 // q x} := by
      rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_permCongr e d, hed]
      exact Equiv.Perm.mem_alternatingGroup.mp c.2
    let s : Equiv.Perm (Fin 8) := Equiv.Perm.ofSubtype d
    have hsalt : s ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
      exact Equiv.Perm.mem_alternatingGroup.mp hdmem
    have hsp : s p = p := Equiv.Perm.ofSubtype_apply_of_not_mem d (by simp [q, Z])
    have hsstab : s ∈ MulAction.stabilizer (Equiv.Perm (Fin 8)) p := by
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact hsp
    have hsG : s ∈ G := Subgroup.mem_inf.mpr ⟨hsalt, hsstab⟩
    refine ⟨⟨s, hsG⟩, ?_⟩
    apply Subtype.ext
    show F' ⟨s, hsG⟩ = (c : Equiv.Perm (Fin 7))
    have hφ : φ ⟨s, hsG⟩ = d := by
      show s.subtypePerm (hinv ⟨s, hsG⟩) = d
      change (Equiv.Perm.ofSubtype d).subtypePerm (hinv ⟨s, hsG⟩) = d
      refine Equiv.ext fun x => Subtype.ext ?_
      change Equiv.Perm.ofSubtype d ↑x = ↑(d x)
      exact Equiv.Perm.ofSubtype_apply_of_mem d x.2
    show e.permCongr (φ ⟨s, hsG⟩) = (c : Equiv.Perm (Fin 7))
    rw [hφ, hed]
  have hinj : Function.Injective F := by
    intro a b hab
    have hab' : F' a = F' b := by
      have h := congrArg (fun x : ↥(alternatingGroup (Fin 7)) => (x : Equiv.Perm (Fin 7))) hab
      change F' a = F' b at h
      exact h
    have hφ : φ a = φ b := (Equiv.permCongrHom e).injective (by simpa [F'] using hab')
    have hA : Equiv.Perm.ofSubtype ((a : Equiv.Perm (Fin 8)).subtypePerm (hinv a)) =
        (a : Equiv.Perm (Fin 8)) :=
      Equiv.Perm.ofSubtype_subtypePerm (hinv a) (h2 a)
    have hB : Equiv.Perm.ofSubtype ((b : Equiv.Perm (Fin 8)).subtypePerm (hinv b)) =
        (b : Equiv.Perm (Fin 8)) :=
      Equiv.Perm.ofSubtype_subtypePerm (hinv b) (h2 b)
    have hφ' : (a : Equiv.Perm (Fin 8)).subtypePerm (hinv a) =
        (b : Equiv.Perm (Fin 8)).subtypePerm (hinv b) := hφ
    have hEq : (a : Equiv.Perm (Fin 8)) = (b : Equiv.Perm (Fin 8)) := by
      rw [← hA, hφ', hB]
    exact Subtype.ext hEq
  exact ⟨MulEquiv.ofBijective F ⟨hinj, hsurj⟩⟩

end CFSG.ASVolI.AppH
