module

public import CFSG.Quasithin.EmptyFaithful.S152Z6A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S152Z6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSubgroup_le_conjClosure {V H : Subgroup G} {h : G} (hh : h ∈ H) :
    conjSubgroup V h ≤ conjClosure V H := by
  intro y hy
  have hz : h * y * h⁻¹ ∈ V := mem_conjSubgroup_iff.1 hy
  have := mem_conjClosure (H.inv_mem hh) hz
  simpa [mul_assoc] using this

omit [Finite G] in
theorem card_conjSubgroup (V : Subgroup G) (h : G) :
    Nat.card ↥(conjSubgroup V h) = Nat.card ↥V :=
  card_cjSub h⁻¹ V

theorem le_normalizer_conjSubgroup {T Mc M H : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) {h : G} (hh : h ∈ H) :
    pCoreOf 2 H ≤ Subgroup.normalizer (conjSubgroup (V154 T Mc M) h : Set G) := by
  have hQT := B6.pCoreOf_two_le_of_isSylowTwoOf (S152N.isSylowTwoOf_hStar hs hH)
  have hTM : T ≤ M := hs.mf.1.1.2
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  have hx' : h * x * h⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H hh) x).1 hx
  have hn : h * x * h⁻¹ ∈ Subgroup.normalizer (V154 T Mc M : Set G) :=
    le_normalizer_V154 T Mc M (hTM (hQT hx'))
  intro y
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  have e : h * (x * y * x⁻¹) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) * (h * x * h⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.1 hn (h * y * h⁻¹)

omit [Finite G] in
theorem commutator_le_of_le_normalizer' {X B V : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (V : Set G)) (hX : X ≤ V) : ⁅B, X⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro b hb x hx
  rw [commutatorElement_def]
  exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hB hb) x).1 (hX hx)) (inv_mem (hX hx))

omit [Finite G] in
theorem commutator_le_inf_centralizer {U A B X : Subgroup G} (hquad : ⁅⁅U, A⁆, A⁆ = ⊥)
    (hBA : B ≤ A) (hXU : X ≤ U) (hBX : B ≤ Subgroup.normalizer (X : Set G)) :
    ⁅B, X⁆ ≤ X ⊓ Subgroup.centralizer (B : Set G) := by
  refine le_inf (commutator_le_of_le_normalizer' hBX le_rfl) ?_
  have h1 : ⁅⁅X, B⁆, B⁆ = ⊥ := by
    refine eq_bot_iff.2 ?_
    rw [← hquad]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono hXU hBA) hBA
  rw [Subgroup.commutator_comm B X]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1

theorem active_facts {T Mc M H A : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (hV16 : Nat.card (V154 T Mc M) = 16) (hD : Data4 (V154 T Mc M) H A) {h : G} (hh : h ∈ H)
    (hact : ⁅A ⊓ pCoreOf 2 H, conjSubgroup (V154 T Mc M) h⁆ ≠ ⊥) :
    (A ⊓ pCoreOf 2 H ⊓ Subgroup.centralizer (conjSubgroup (V154 T Mc M) h : Set G)).relIndex
        (A ⊓ pCoreOf 2 H) = 2 ∧
      Nat.card ↥(conjSubgroup (V154 T Mc M) h) =
        4 * Nat.card ↥(conjSubgroup (V154 T Mc M) h ⊓
          Subgroup.centralizer ((A ⊓ pCoreOf 2 H : Subgroup G) : Set G)) := by
  set X := conjSubgroup (V154 T Mc M) h with hX
  set B := A ⊓ pCoreOf 2 H with hB
  have hBN : B ≤ Subgroup.normalizer (X : Set G) :=
    inf_le_right.trans (le_normalizer_conjSubgroup hs hH hh)
  have hXU : X ≤ conjClosure (V154 T Mc M) H := conjSubgroup_le_conjClosure hh
  have hcomm := commutator_le_inf_centralizer hD.quad (inf_le_left : B ≤ A) hXU hBN
  have hcount := hD.count_three h hh hact
  set CB := B ⊓ Subgroup.centralizer (X : Set G) with hCB
  set CX := X ⊓ Subgroup.centralizer (B : Set G) with hCX
  have hBc : CB.relIndex B * Nat.card ↥CB = Nat.card ↥B := by
    have := Subgroup.relIndex_mul_card CB B
    rwa [inf_eq_left.2 inf_le_left] at this
  have hXc : CX.relIndex X * Nat.card ↥CX = Nat.card ↥X := by
    have := Subgroup.relIndex_mul_card CX X
    rwa [inf_eq_left.2 inf_le_left] at this
  have hX16 : Nat.card ↥X = 16 := by rw [hX, card_conjSubgroup, hV16]
  have hCBpos : 0 < Nat.card ↥CB := Nat.card_pos
  have hCXpos : 0 < Nat.card ↥CX := Nat.card_pos
  have hij : CB.relIndex B ^ 2 = CX.relIndex X := by
    rw [← hBc, ← hXc] at hcount
    refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos hCBpos 2) hCXpos) ?_
    calc Nat.card ↥CB ^ 2 * Nat.card ↥CX * CB.relIndex B ^ 2
        = (CB.relIndex B * Nat.card ↥CB) ^ 2 * Nat.card ↥CX := by ring
      _ = Nat.card ↥CB ^ 2 * (CX.relIndex X * Nat.card ↥CX) := hcount
      _ = _ := by ring
  have h16 : CX.relIndex X * Nat.card ↥CX = 16 := by rw [hXc, hX16]
  have hile : CB.relIndex B ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have h25 : 25 ≤ CX.relIndex X := by
      rw [← hij]; nlinarith
    nlinarith
  have hipos : 0 < CB.relIndex B := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  generalize hi : CB.relIndex B = i at hij hile hipos
  rw [← hij] at h16
  interval_cases i
  · exfalso
    apply hact
    have hle : B ≤ CB := Subgroup.relIndex_eq_one.1 hi
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hle.trans inf_le_right)
  · refine ⟨rfl, ?_⟩
    have h5 : Nat.card ↥X = 4 * Nat.card ↥CX := by
      rw [← hXc, ← hij]
      norm_num
    exact h5
  · exfalso
    have h9 : 9 * Nat.card ↥CX = 16 := by simpa using h16
    omega
  · exfalso
    have hc1 : Nat.card ↥CX = 1 := by
      have h9 : 16 * Nat.card ↥CX = 16 := by simpa using h16
      omega
    have hbot : CX = ⊥ := Subgroup.card_eq_one.1 hc1
    exact hact (eq_bot_iff.2 (hbot ▸ hcomm))

omit [Finite G] in
private theorem cjSub_eq_self_of_comm {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hBA : B ≤ A) {g : G} (hg : g ∈ A) : cjSub g B = B := by
  ext x
  rw [mem_cjSub]
  constructor
  · intro hx
    have hxA : x ∈ A := by
      have := A.mul_mem (A.mul_mem hg (hBA hx)) (A.inv_mem hg)
      simpa [mul_assoc] using this
    have : g⁻¹ * x * g = x := by
      rw [mul_assoc, ← hcomm g hg x hxA]
      group
    rwa [this] at hx
  · intro hx
    have hxA : x ∈ A := hBA hx
    have : g⁻¹ * x * g = x := by
      rw [mul_assoc, ← hcomm g hg x hxA]
      group
    rwa [this]

omit [Finite G] in
theorem commutator_conjClosure_le {V H A : Subgroup G} (hD : Data4 V H A) :
    ⁅conjClosure V H, A⁆ ≤ conjClosure V H ⊓ Subgroup.centralizer (A : Set G) := by
  refine le_inf ?_ (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hD.quad)
  rw [Subgroup.commutator_comm (conjClosure V H) A]
  exact commutator_le_of_le_normalizer' (hD.maxA.1.trans (le_normalizer_conjClosure V H)) le_rfl

theorem card_conjSubgroup_sup_UB {T Mc M H A : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) (hV16 : Nat.card (V154 T Mc M) = 16) (hD : Data4 (V154 T Mc M) H A)
    {h : G} (hh : h ∈ H) (hact : ⁅A ⊓ pCoreOf 2 H, conjSubgroup (V154 T Mc M) h⁆ ≠ ⊥) :
    Nat.card ↥(conjSubgroup (V154 T Mc M) h ⊔
        (conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (A : Set G))) =
      4 * Nat.card ↥(conjClosure (V154 T Mc M) H ⊓ Subgroup.centralizer (A : Set G)) := by
  set V := V154 T Mc M with hVdef
  set B := A ⊓ pCoreOf 2 H with hB
  set U := conjClosure V H with hU
  set UB := U ⊓ Subgroup.centralizer (A : Set G) with hUB
  have hUBfix : UB = U ⊓ Subgroup.centralizer (B : Set G) := hD.fix
  have hUcomm : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := fun u hu u' hu' =>
    B2F.isElemAbelian_comm hD.uElem hu hu'
  obtain ⟨-, h4⟩ := active_facts hs hH hV16 hD hh hact
  have h4' : Nat.card ↥(conjSubgroup V h) =
      4 * Nat.card ↥(conjSubgroup V h ⊓ Subgroup.centralizer (B : Set G)) := h4
  have hVU : conjSubgroup V h ≤ U := conjSubgroup_le_conjClosure hh
  have hcomm : ∀ x ∈ conjSubgroup V h, ∀ y ∈ UB, x * y = y * x := fun x hx y hy =>
    hUcomm x (hVU hx) y hy.1
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hinf : conjSubgroup V h ⊓ UB = conjSubgroup V h ⊓ Subgroup.centralizer (B : Set G) := by
    rw [hUBfix]
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hVU hx.1, hx.2⟩⟩
  rw [hinf] at hcard
  have h16 : Nat.card ↥(conjSubgroup V h) = 16 := by rw [card_conjSubgroup, hV16]
  have hc4 : Nat.card ↥(conjSubgroup V h ⊓ Subgroup.centralizer (B : Set G)) = 4 := by
    rw [h16] at h4'
    omega
  rw [hc4, h16] at hcard
  omega

theorem exists_active_stabilized_of_reg {T Mc M H A : Subgroup G} (hs : Setting152 T Mc M)
    (hH : IsHStar T M H) (hV16 : Nat.card (V154 T Mc M) = 16) (hD : Data4 (V154 T Mc M) H A)
    (hreg : ∀ S : Finset (Subgroup G), (∀ V' ∈ S, (∃ h ∈ H, V' = conjSubgroup (V154 T Mc M) h) ∧
        A ⊓ Subgroup.normalizer (V' : Set G) ≤ pCoreOf 2 H) → S.card ≤ 4) :
    ∃ h ∈ H, ⁅A ⊓ pCoreOf 2 H, conjSubgroup (V154 T Mc M) h⁆ ≠ ⊥ ∧
      ∃ x ∈ A, x ∉ pCoreOf 2 H ∧
        x ∈ Subgroup.normalizer (conjSubgroup (V154 T Mc M) h : Set G) := by
  classical
  by_contra hno
  push Not at hno
  set V := V154 T Mc M with hVdef
  set Q := pCoreOf 2 H with hQ
  set B := A ⊓ Q with hB
  set U := conjClosure V H with hU
  set UB := U ⊓ Subgroup.centralizer (A : Set G) with hUB
  have hAmax := hD.maxA
  have hAH : A ≤ H := hAmax.1
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hAmax.2.1 ha hb
  have hUcomm : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := fun u hu u' hu' =>
    B2F.isElemAbelian_comm hD.uElem hu hu'
  have hUBfix : UB = U ⊓ Subgroup.centralizer (B : Set G) := hD.fix
  have hBA : B ≤ A := inf_le_left
  have hUBpos : 0 < Nat.card ↥UB := Nat.card_pos
  have hU16 : Nat.card ↥U = 16 * Nat.card ↥UB := hD.idxU
  have hUA : ⁅U, A⁆ ≤ UB := commutator_conjClosure_le hD
  have hF3 : ∀ X : Subgroup G, X ≤ U → ∀ a ∈ A, conjSubgroup X a ≤ X ⊔ UB := by
    intro X hXU a ha y hy
    have hx : a * y * a⁻¹ ∈ X := mem_conjSubgroup_iff.1 hy
    have hxU : a * y * a⁻¹ ∈ U := hXU hx
    have e : y = (a * y * a⁻¹) * ⁅(a * y * a⁻¹)⁻¹, a⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem_sup hx
      (hUA (Subgroup.commutator_mem_commutator (U.inv_mem hxU) (A.inv_mem ha)))
  have hF4 : ∀ h ∈ H, ⁅B, conjSubgroup V h⁆ = ⊥ → conjSubgroup V h ≤ UB := by
    intro h hh hbot
    rw [hUBfix]
    refine le_inf (conjSubgroup_le_conjClosure hh) ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rwa [Subgroup.commutator_comm] at hbot)
  have hF5 : ∀ h ∈ H, ⁅B, conjSubgroup V h⁆ ≠ ⊥ →
      Nat.card ↥(conjSubgroup V h ⊔ UB) = 4 * Nat.card ↥UB := fun h hh hact =>
    card_conjSubgroup_sup_UB hs hH hV16 hD hh hact
  by_cases hex : ∃ h ∈ H, ⁅B, conjSubgroup V h⁆ ≠ ⊥
  · obtain ⟨h₁, hh₁, hact₁⟩ := hex
    let 𝒞 : Set (Subgroup G) := {V' | ∃ h ∈ H, V' = conjSubgroup V h ∧ ⁅B, V'⁆ ≠ ⊥}
    have h𝒞fin : 𝒞.Finite := Set.toFinite _
    let R : Finset (Subgroup G) := h𝒞fin.toFinset
    have hRmem : ∀ V', V' ∈ R ↔ V' ∈ 𝒞 := fun V' => Set.Finite.mem_toFinset h𝒞fin
    have hRreg : ∀ V' ∈ R, (∃ h ∈ H, V' = conjSubgroup V h) ∧
        A ⊓ Subgroup.normalizer (V' : Set G) ≤ Q := by
      intro V' hV'
      obtain ⟨h, hh, rfl, hact⟩ := (hRmem V').1 hV'
      refine ⟨⟨h, hh, rfl⟩, fun x hx => ?_⟩
      by_contra hxQ
      exact hno h hh hact x hx.1 hxQ hx.2
    have hR4 : R.card ≤ 4 := hreg R hRreg
    set X₁ := conjSubgroup V h₁ with hX₁
    have hX₁U : X₁ ≤ U := conjSubgroup_le_conjClosure hh₁
    have hX₁R : X₁ ∈ R := (hRmem X₁).2 ⟨h₁, hh₁, rfl, hact₁⟩
    have hX₁reg := (hRreg X₁ hX₁R).2
    let B' : Subgroup ↥A := B.subgroupOf A
    let rep : (↥A ⧸ B') → ↥A := Function.surjInv QuotientGroup.mk_surjective
    have hrep : ∀ q, (rep q : ↥A ⧸ B') = q := Function.surjInv_eq QuotientGroup.mk_surjective
    let f : (↥A ⧸ B') → Subgroup G := fun q => conjSubgroup X₁ ((rep q : ↥A) : G)
    have hinj : Function.Injective f := by
      intro q q' hqq
      set a := rep q with ha
      set a' := rep q' with ha'
      have hg : (a' : G) * (a : G)⁻¹ ∈ Subgroup.normalizer (X₁ : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h1 : ∀ z : G, (a : G) * z * (a : G)⁻¹ ∈ X₁ ↔ (a' : G) * z * (a' : G)⁻¹ ∈ X₁ := fun z =>
          (mem_conjSubgroup_iff (A := X₁) (g := (a : G)) (x := z)).symm.trans
            ((SetLike.ext_iff.1 hqq z).trans
              (mem_conjSubgroup_iff (A := X₁) (g := (a' : G)) (x := z)))
        have h2 := h1 ((a : G)⁻¹ * y * a)
        have e1 : (a : G) * ((a : G)⁻¹ * y * a) * (a : G)⁻¹ = y := by group
        have e2 : (a' : G) * ((a : G)⁻¹ * y * a) * (a' : G)⁻¹ =
            ((a' : G) * (a : G)⁻¹) * y * ((a' : G) * (a : G)⁻¹)⁻¹ := by group
        rw [e1, e2] at h2
        exact h2
      have hgA : (a' : G) * (a : G)⁻¹ ∈ A := A.mul_mem a'.2 (A.inv_mem a.2)
      have hgQ : (a' : G) * (a : G)⁻¹ ∈ Q := hX₁reg ⟨hgA, hg⟩
      have hcm : (a : G)⁻¹ * (a' : G) = (a' : G) * (a : G)⁻¹ := by
        have := hAcomm (a : G)⁻¹ (A.inv_mem a.2) a' a'.2
        exact this
      have hmem : (a⁻¹ * a' : ↥A) ∈ B' := by
        rw [Subgroup.mem_subgroupOf]
        show (a : G)⁻¹ * (a' : G) ∈ B
        rw [hcm]
        exact ⟨hgA, hgQ⟩
      have hq : (a : ↥A ⧸ B') = (a' : ↥A ⧸ B') := QuotientGroup.eq.2 hmem
      rw [← hrep q, ← hrep q']
      exact hq
    have hcardQ : Nat.card (↥A ⧸ B') = 4 := hD.rel
    have : Fintype (↥A ⧸ B') := Fintype.ofFinite _
    let I : Finset (Subgroup G) := Finset.univ.image f
    have hIcard : I.card = 4 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_eq_nat_card]
      exact hcardQ
    have hIR : I ⊆ R := by
      intro V' hV'
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hV'
      rw [hRmem]
      have haA : ((rep q : ↥A) : G) ∈ A := (rep q).2
      refine ⟨h₁ * ((rep q : ↥A) : G), H.mul_mem hh₁ (hAH haA), ?_, ?_⟩
      · exact (conjSubgroup_conjSubgroup V h₁ _)
      · have hBa : cjSub ((rep q : ↥A) : G)⁻¹ B = B :=
          cjSub_eq_self_of_comm hAcomm hBA (A.inv_mem haA)
        have e : ⁅B, f q⁆ = cjSub ((rep q : ↥A) : G)⁻¹ ⁅B, X₁⁆ := by
          have := S152N.cjSub_commutator ((rep q : ↥A) : G)⁻¹ B X₁
          rw [hBa] at this
          exact this.symm
        rw [e]
        intro hbot
        exact hact₁ ((S152N.cjSub_eq_bot_iff _).mp hbot)
    have hIeq : I = R := Finset.eq_of_subset_of_card_le hIR (by omega)
    have hact_le : ∀ h ∈ H, ⁅B, conjSubgroup V h⁆ ≠ ⊥ → conjSubgroup V h ≤ X₁ ⊔ UB := by
      intro h hh hact
      have hmem : conjSubgroup V h ∈ I := by
        rw [hIeq, hRmem]
        exact ⟨h, hh, rfl, hact⟩
      obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hmem
      rw [← hq]
      exact hF3 X₁ hX₁U _ (rep q).2
    have hUW : U ≤ X₁ ⊔ UB := by
      refine conjClosure_le fun h hh z hz => ?_
      have hy : h * z * h⁻¹ ∈ conjSubgroup V h⁻¹ := by
        rw [mem_conjSubgroup_iff]
        have e : h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z := by group
        rw [e]
        exact hz
      by_cases hact : ⁅B, conjSubgroup V h⁻¹⁆ = ⊥
      · exact Subgroup.mem_sup_right (hF4 h⁻¹ (H.inv_mem hh) hact hy)
      · exact hact_le h⁻¹ (H.inv_mem hh) hact hy
    have hcard1 := Subgroup.card_le_of_le hUW
    have hcard2 : Nat.card ↥(X₁ ⊔ UB) = 4 * Nat.card ↥UB := hF5 h₁ hh₁ hact₁
    omega
  · push Not at hex
    have hUle : U ≤ UB := by
      refine conjClosure_le fun h hh z hz => ?_
      have hy : h * z * h⁻¹ ∈ conjSubgroup V h⁻¹ := by
        rw [mem_conjSubgroup_iff]
        have e : h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z := by group
        rw [e]
        exact hz
      exact hF4 h⁻¹ (H.inv_mem hh) (hex h⁻¹ (H.inv_mem hh)) hy
    have := Subgroup.card_le_of_le hUle
    omega

end S152Z6

end CFSG.Quasithin
