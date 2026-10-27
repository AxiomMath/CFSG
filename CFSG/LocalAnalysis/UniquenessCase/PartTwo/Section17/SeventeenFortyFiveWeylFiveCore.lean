module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseProps
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup
open scoped commutatorElement

@[expose] def WeylFiveInner (L : Type) [Group L] : Prop :=
  ∀ (Â : Subgroup (MulAut L)) (β : MulAut L), (∀ α ∈ Â, α ^ 31 = 1) →
    ⁅Â, zpowers β⁆ = Â → Â ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner L

@[expose] def WeylFivePower (G : Type) [Group G] : Prop :=
  ∀ (α : MulAut G) (E : Subgroup G), α ^ 5 = 1 → (∀ x ∈ E, x ^ 31 = 1) →
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → E.map α.toMonoidHom = E →
    ∃ N k : ℕ, ¬ 5 ∣ N ∧ ∀ x ∈ E, (α ^ N) x = x ^ k

theorem WeylFiveInner.of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : WeylFiveInner L) : WeylFiveInner L' := by
  intro Â' β' hexp hcomm
  let φ : MulAut L' ≃* MulAut L := (MulAut.congr e).symm
  let Â : Subgroup (MulAut L) := Â'.map φ.toMonoidHom
  let β : MulAut L := φ β'
  have hexp' : ∀ α ∈ Â, α ^ 31 = 1 := by
    rintro _ ⟨α', hα', rfl⟩
    rw [← map_pow φ.toMonoidHom α' 31, hexp α' hα', map_one]
  have hcomm' : ⁅Â, zpowers β⁆ = Â := by
    have hmap := congrArg (Subgroup.map φ.toMonoidHom) hcomm
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at hmap
    simpa [Â, β] using hmap
  have hle : Â ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner L :=
    h Â β hexp' hcomm'
  have hinner : (CFSG.ComponentClassification.OuterAutomorphisms.inner L).map
      φ.symm.toMonoidHom = CFSG.ComponentClassification.OuterAutomorphisms.inner L' := by
    have hφ : φ.symm = MulAut.congr e := by ext; rfl
    rw [hφ]
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  intro x' hx'
  have hmem : φ x' ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner L :=
    hle (Subgroup.mem_map_of_mem φ.toMonoidHom hx')
  have hmem' : φ.symm (φ x') ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner L' := by
    rw [← hinner]
    exact Subgroup.mem_map_of_mem φ.symm.toMonoidHom hmem
  simpa using hmem'

theorem WeylFivePower.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (h : WeylFivePower G) : WeylFivePower G' := by
  intro α' E' hα' hexp' hcomm' hmap'
  let φ : MulAut G' ≃* MulAut G := (MulAut.congr e).symm
  let α : MulAut G := φ α'
  let E : Subgroup G := E'.map (e.symm : G' →* G)
  have hα : α ^ 5 = 1 := by
    show (φ α') ^ 5 = 1
    rw [← map_pow φ α' 5, hα', map_one]
  have hexp : ∀ x ∈ E, x ^ 31 = 1 := by
    rintro _ ⟨x', hx', rfl⟩
    rw [← map_pow (e.symm : G' →* G) x' 31, hexp' x' hx', map_one]
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x', hx', rfl⟩ _ ⟨y', hy', rfl⟩
    calc e.symm x' * e.symm y' = e.symm (x' * y') := (map_mul (e.symm : G' →* G) x' y').symm
      _ = e.symm (y' * x') := by rw [hcomm' x' hx' y' hy']
      _ = e.symm y' * e.symm x' := map_mul (e.symm : G' →* G) y' x'
  have hmap : E.map α.toMonoidHom = E := by
    show (E'.map (e.symm : G' →* G)).map (φ α').toMonoidHom = E'.map (e.symm : G' →* G)
    have hcomp : ((φ α').toMonoidHom).comp (e.symm : G' →* G) =
        (e.symm : G' →* G).comp α'.toMonoidHom := by
      ext x
      change φ α' (e.symm x) = e.symm (α' x)
      rw [show φ α' = (MulAut.congr e).symm α' from rfl, MulAut.congr_symm_apply]
      simp
    calc (E'.map (e.symm : G' →* G)).map (φ α').toMonoidHom
        = E'.map (((φ α').toMonoidHom).comp (e.symm : G' →* G)) := by
          rw [Subgroup.map_map]
      _ = E'.map ((e.symm : G' →* G).comp α'.toMonoidHom) := by rw [hcomp]
      _ = (E'.map α'.toMonoidHom).map (e.symm : G' →* G) := by rw [Subgroup.map_map]
      _ = E'.map (e.symm : G' →* G) := by rw [hmap']
  obtain ⟨N, k, hN, hNk⟩ := h α E hα hexp hcomm hmap
  refine ⟨N, k, hN, ?_⟩
  intro x' hx'
  have hxE : e.symm x' ∈ E := Subgroup.mem_map_of_mem _ hx'
  have h1 := hNk (e.symm x') hxE
  have hαN : α ^ N = φ (α' ^ N) := (map_pow φ α' N).symm
  have h2 : (α ^ N) (e.symm x') = e.symm ((α' ^ N) x') := by
    rw [hαN]
    change ((MulAut.congr e).symm (α' ^ N)) (e.symm x') = e.symm ((α' ^ N) x')
    rw [MulAut.congr_symm_apply]
    simp
  have h3 : (e.symm x') ^ k = e.symm (x' ^ k) :=
    (map_pow (e.symm : G' →* G) x' k).symm
  exact e.symm.injective (by rw [← h2, ← h3]; exact h1)

theorem weylFiveInner_of_outPNice {L : Type} [Group L]
    (h : CFSG.RankThree.PartOne.OutStructure.OutPNice 31 L) : WeylFiveInner L := by
  obtain ⟨D, E, hInnD, hDpow, hE, hED, -⟩ := h
  intro Â β hexp hcomm
  have hAE : Â ≤ E := by
    intro α hα
    refine hE α ⟨1, ?_⟩
    rw [pow_one, hexp α hα]
    exact D.one_mem
  have hcommD : ⁅Â, zpowers β⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    have hyD : ⁅y, a⁆ ∈ D := hED y a (hAE ha)
    rw [← Subgroup.inv_mem_iff]
    simpa using hyD
  have hAD : Â ≤ D := by
    rw [← hcomm]
    exact hcommD
  intro α hα
  refine hDpow α (hAD hα) 1 ?_
  rw [pow_one, hexp α hα]
  exact (CFSG.RankThree.PartOne.OutStructure.Inn L).one_mem

theorem map_pow_of_map_eq {G : Type} [Group G] {α : MulAut G} {E : Subgroup G}
    (h : E.map α.toMonoidHom = E) (m : ℕ) : E.map (α ^ m).toMonoidHom = E := by
  induction m with
  | zero =>
    rw [pow_zero]
    have hone : ((1 : MulAut G).toMonoidHom : G →* G) = MonoidHom.id G := by
      rw [MulAut.one_def]
      exact MulEquiv.toMonoidHom_refl
    rw [hone]
    exact Subgroup.map_id E
  | succ m ih =>
    have hstep : (α ^ (m + 1)).toMonoidHom = (α ^ m).toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp [pow_succ, MulAut.mul_apply]
    rw [hstep, ← Subgroup.map_map, h, ih]

theorem le_of_weylFiveInner {X : Type} [Group X] {L A : Subgroup X} [L.Normal]
    (hC : centralizer (L : Set X) = ⊥) (hI : WeylFiveInner L) (hA : ∀ a ∈ A, a ^ 31 = 1)
    (b : X) (hAB : ⁅A, zpowers b⁆ = A) : A ≤ L := by
  let c : X →* MulAut ↥L := MulAut.conjNormal (H := L)
  have hexp : ∀ α ∈ A.map c, α ^ 31 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow c a 31, hA a ha, map_one]
  have hcomm : ⁅A.map c, zpowers (c b)⁆ = A.map c := by
    have hmap := congrArg (Subgroup.map c) hAB
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at hmap
    simpa using hmap
  have hle : A.map c ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
    hI (A.map c) (c b) hexp hcomm
  intro a ha
  have hmem : c a ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
    hle (Subgroup.mem_map_of_mem c ha)
  obtain ⟨l, hl⟩ := hmem
  have hcent : (l : X)⁻¹ * a ∈ centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : (l : X) * x * (l : X)⁻¹ = a * x * a⁻¹ := by
      have hval := congrArg (fun φ : MulAut ↥L => ((φ ⟨x, hx⟩ : ↥L) : X)) hl
      simpa [c, MulAut.conj_apply, MulAut.conjNormal_apply] using hval
    calc x * ((l : X)⁻¹ * a) = (l : X)⁻¹ * ((l : X) * x * (l : X)⁻¹) * a := by group
      _ = (l : X)⁻¹ * (a * x * a⁻¹) * a := by rw [h1]
      _ = ((l : X)⁻¹ * a) * x := by group
  rw [hC] at hcent
  have hz : (l : X)⁻¹ * a = 1 := Subgroup.mem_bot.mp hcent
  have haeq : a = (l : X) := by
    calc a = (l : X) * ((l : X)⁻¹ * a) := by group
      _ = (l : X) := by rw [hz, mul_one]
  rw [haeq]
  exact l.2

theorem false_of_power_lines {X : Type} [Group X] {A₁ A₂ B : Subgroup X}
    (h₁ : Nat.card A₁ = 31) (h₂ : Nat.card A₂ = 31) (h₁₂ : A₁ ⊓ A₂ = ⊥)
    (hc : A₁ ≤ centralizer (A₂ : Set X)) (hB : Nat.card B = 5) {b : X} (hb : b ∈ B)
    (hb1 : b ≠ 1) {N k : ℕ} (hN : ¬ 5 ∣ N)
    (hpow : ∀ a ∈ A₁ ⊔ A₂, b ^ N * a * (b ^ N)⁻¹ = a ^ k)
    (hlines : ∀ D : Subgroup X, D ≤ A₁ ⊔ A₂ → Nat.card D = 31 → B ≤ normalizer (D : Set X) →
      D = A₁ ∨ D = A₂) : False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have : Finite ↥A₁ := Nat.finite_of_card_ne_zero (by rw [h₁]; norm_num)
  have : Finite ↥A₂ := Nat.finite_of_card_ne_zero (by rw [h₂]; norm_num)
  have : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  have : Nontrivial ↥A₁ := (Finite.one_lt_card_iff_nontrivial).mp (by rw [h₁]; norm_num)
  have : Nontrivial ↥A₂ := (Finite.one_lt_card_iff_nontrivial).mp (by rw [h₂]; norm_num)
  obtain ⟨a₁, ha₁, ha₁1⟩ := Subgroup.exists_ne_one_of_nontrivial A₁
  obtain ⟨a₂, ha₂, ha₂1⟩ := Subgroup.exists_ne_one_of_nontrivial A₂
  have hord₁ : orderOf a₁ = 31 := by
    have hdvd : orderOf a₁ ∣ 31 := by simpa [h₁] using Subgroup.orderOf_dvd_natCard A₁ ha₁
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha₁1
    · exact h
  have hord₂ : orderOf a₂ = 31 := by
    have hdvd : orderOf a₂ ∣ 31 := by simpa [h₂] using Subgroup.orderOf_dvd_natCard A₂ ha₂
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha₂1
    · exact h
  have hpow₁ : a₁ ^ 31 = 1 := by
    rw [← hord₁]
    exact pow_orderOf_eq_one a₁
  have hpow₂ : a₂ ^ 31 = 1 := by
    rw [← hord₂]
    exact pow_orderOf_eq_one a₂
  have hcomm₁₂ : Commute a₁ a₂ := by
    have h : a₂ * a₁ = a₁ * a₂ := Subgroup.mem_centralizer_iff.mp (hc ha₁) a₂ ha₂
    exact h.symm
  have hprod_ne : a₁ * a₂ ≠ 1 := by
    intro h
    have ha₂A₁ : a₂ ∈ A₁ := by
      have h' : a₂ = a₁⁻¹ := by
        calc a₂ = a₁⁻¹ * (a₁ * a₂) := by group
          _ = a₁⁻¹ := by rw [h, mul_one]
      rw [h']
      exact A₁.inv_mem ha₁
    have : a₂ ∈ A₁ ⊓ A₂ := ⟨ha₂A₁, ha₂⟩
    rw [h₁₂] at this
    exact ha₂1 (Subgroup.mem_bot.mp this)
  have hprod31 : (a₁ * a₂) ^ 31 = 1 := by
    rw [hcomm₁₂.mul_pow, hpow₁, hpow₂, one_mul]
  have hordprod : orderOf (a₁ * a₂) = 31 := orderOf_eq_prime hprod31 hprod_ne
  let D : Subgroup X := zpowers (a₁ * a₂)
  have hDcard : Nat.card D = 31 := by
    show Nat.card (zpowers (a₁ * a₂)) = 31
    rw [Nat.card_zpowers, hordprod]
  have hDle : D ≤ A₁ ⊔ A₂ := by
    show zpowers (a₁ * a₂) ≤ A₁ ⊔ A₂
    rw [Subgroup.zpowers_le]
    exact Subgroup.mul_mem_sup ha₁ ha₂
  have hDne1 : D ≠ A₁ := by
    intro h
    have hmem : a₁ * a₂ ∈ A₁ := by
      rw [← h]
      exact Subgroup.mem_zpowers (a₁ * a₂)
    have ha₂A₁ : a₂ ∈ A₁ := by
      have h' : a₂ = a₁⁻¹ * (a₁ * a₂) := by group
      rw [h']
      exact A₁.mul_mem (A₁.inv_mem ha₁) hmem
    have : a₂ ∈ A₁ ⊓ A₂ := ⟨ha₂A₁, ha₂⟩
    rw [h₁₂] at this
    exact ha₂1 (Subgroup.mem_bot.mp this)
  have hDne2 : D ≠ A₂ := by
    intro h
    have hmem : a₁ * a₂ ∈ A₂ := by
      rw [← h]
      exact Subgroup.mem_zpowers (a₁ * a₂)
    have ha₁A₂ : a₁ ∈ A₂ := by
      have h' : a₁ = (a₁ * a₂) * a₂⁻¹ := by group
      rw [h']
      exact A₂.mul_mem hmem (A₂.inv_mem ha₂)
    have : a₁ ∈ A₁ ⊓ A₂ := ⟨ha₁, ha₁A₂⟩
    rw [h₁₂] at this
    exact ha₁1 (Subgroup.mem_bot.mp this)
  have hb5 : b ^ 5 = 1 := by
    have hdvd : orderOf b ∣ 5 := by simpa [hB] using Subgroup.orderOf_dvd_natCard B hb
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · rw [← h]
      exact pow_orderOf_eq_one b
  have hordb : orderOf b = 5 := by
    have hdvd : orderOf b ∣ 5 := by simpa [hB] using Subgroup.orderOf_dvd_natCard B hb
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hbN1 : b ^ N ≠ 1 := by
    intro h
    have hdvd : orderOf b ∣ N := orderOf_dvd_of_pow_eq_one h
    rw [hordb] at hdvd
    exact hN hdvd
  have hbN5 : (b ^ N) ^ 5 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hb5, one_pow]
  have hordbN : orderOf (b ^ N) = 5 := orderOf_eq_prime hbN5 hbN1
  have hbgens : B = zpowers (b ^ N) := by
    have hgen : zpowers (b ^ N) ≤ B := Subgroup.zpowers_le.mpr (B.pow_mem hb N)
    have hcard : Nat.card B ≤ Nat.card (zpowers (b ^ N)) := by
      rw [Nat.card_zpowers, hordbN, hB]
    exact (Subgroup.eq_of_le_of_card_ge hgen hcard).symm
  have hbNnorm : b ^ N ∈ normalizer (D : Set X) := by
    have : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [hDcard]; norm_num)
    have hmap_le : D.map (MulAut.conj (b ^ N)).toMonoidHom ≤ D := by
      intro y hy
      obtain ⟨x, hxD, rfl⟩ := Subgroup.mem_map.mp hy
      have hx : x ∈ A₁ ⊔ A₂ := hDle hxD
      have h := hpow x hx
      have hconj : (MulAut.conj (b ^ N)).toMonoidHom x = b ^ N * x * (b ^ N)⁻¹ := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hconj, h]
      exact D.pow_mem hxD k
    have hmap_eq : D.map (MulAut.conj (b ^ N)).toMonoidHom = D := by
      refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj (b ^ N)).injective]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hmap_eq
  have hBnorm : B ≤ normalizer (D : Set X) := by
    rw [hbgens]
    exact Subgroup.zpowers_le.mpr hbNnorm
  rcases hlines D hDle hDcard hBnorm with h | h
  · exact hDne1 h
  · exact hDne2 h

theorem k45WeylFive_of_types
    (h : ∀ d : TauCeti.ValidLieTypeIndex, SmallWeylIndex45 d.1 → d.1.characteristic ≠ 2 →
      d.1.characteristic ≠ 31 → WeylFiveInner (TauCeti.CFSGIndex.lie d).Group ∧
        WeylFivePower (TauCeti.CFSGIndex.lie d).Group) : K45WeylFive := by
  intro X _ _ L A₁ A₂ B d hLn hC hLie hSmall h2 h31 hA₁ hA₂ h12 hc hB hBA₁ hBA₂ hAB hlines
  obtain ⟨e⟩ := hLie
  obtain ⟨hInner, hPower⟩ := h d hSmall h2 h31
  have hI : WeylFiveInner ↥L := WeylFiveInner.of_mulEquiv e.symm hInner
  have hP : WeylFivePower ↥L := WeylFivePower.of_mulEquiv e.symm hPower
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have : Nontrivial ↥B := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hB]; norm_num)
  obtain ⟨b, hb, hb1⟩ := Subgroup.exists_ne_one_of_nontrivial B
  have hordb : orderOf b = 5 := by
    have hdvd : orderOf b ∣ 5 := by simpa [hB] using Subgroup.orderOf_dvd_natCard B hb
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hb5 : b ^ 5 = 1 := by
    rw [← hordb]
    exact pow_orderOf_eq_one b
  have hBgen : B = zpowers b := by
    have hle : zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
    have hcard : Nat.card B ≤ Nat.card (zpowers b) := by
      rw [Nat.card_zpowers, hordb, hB]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hAB' : ⁅A₁ ⊔ A₂, zpowers b⁆ = A₁ ⊔ A₂ := by
    rw [← hBgen]
    exact hAB
  have : IsCyclic ↥A₁ := isCyclic_of_prime_card (by simpa using hA₁)
  have : IsCyclic ↥A₂ := isCyclic_of_prime_card (by simpa using hA₂)
  have hcommA₁ : ∀ x ∈ A₁, ∀ y ∈ A₁, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A₁)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcommA₂ : ∀ x ∈ A₂, ∀ y ∈ A₂, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥A₂)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAcomm : ∀ x ∈ A₁ ⊔ A₂, ∀ y ∈ A₁ ⊔ A₂, x * y = y * x := by
    intro x hx y hy
    rw [Subgroup.sup_eq_closure] at hx hy
    refine Subgroup.closure_induction₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro x y (hx | hx) (hy | hy)
      · exact hcommA₁ x hx y hy
      · exact (Subgroup.mem_centralizer_iff.mp (hc hx) y hy).symm
      · exact Subgroup.mem_centralizer_iff.mp (hc hy) x hx
      · exact hcommA₂ x hx y hy
    · intro x hx
      simp
    · intro x hx
      simp
    · intro x y z hx hy hz hxz hyz
      calc (x * y) * z = x * (y * z) := by group
        _ = x * (z * y) := by rw [hyz]
        _ = (x * z) * y := by group
        _ = (z * x) * y := by rw [hxz]
        _ = z * (x * y) := by group
    · intro y z x hy hz hx hxy hxz
      calc x * (y * z) = (x * y) * z := by group
        _ = (y * x) * z := by rw [hxy]
        _ = y * (x * z) := by group
        _ = y * (z * x) := by rw [hxz]
        _ = (y * z) * x := by group
    · intro x y hx hy hxy
      exact (show Commute x y from hxy).inv_left
    · intro x y hx hy hxy
      exact (show Commute x y from hxy).inv_right
  have hAexp : ∀ x ∈ A₁ ⊔ A₂, x ^ 31 = 1 := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun x _ => x ^ 31 = 1) ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hx with hx | hx
      · have hdvd : orderOf x ∣ 31 := by simpa [hA₁] using Subgroup.orderOf_dvd_natCard A₁ hx
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd with h | h
        · rw [orderOf_eq_one_iff.mp h, one_pow]
        · rw [← h]
          exact pow_orderOf_eq_one x
      · have hdvd : orderOf x ∣ 31 := by simpa [hA₂] using Subgroup.orderOf_dvd_natCard A₂ hx
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd with h | h
        · rw [orderOf_eq_one_iff.mp h, one_pow]
        · rw [← h]
          exact pow_orderOf_eq_one x
    · exact one_pow 31
    · intro x y hx hy hx31 hy31
      have hxA : x ∈ A₁ ⊔ A₂ := by rwa [Subgroup.sup_eq_closure]
      have hyA : y ∈ A₁ ⊔ A₂ := by rwa [Subgroup.sup_eq_closure]
      have hcomm : Commute x y := hAcomm x hxA y hyA
      rw [hcomm.mul_pow, hx31, hy31, one_mul]
    · intro x hx hx31
      rw [inv_pow, hx31, inv_one]
  have hAleL : A₁ ⊔ A₂ ≤ L := le_of_weylFiveInner hC hI hAexp b hAB'
  let α : MulAut ↥L := MulAut.conjNormal (H := L) b
  let E : Subgroup ↥L := (A₁ ⊔ A₂).subgroupOf L
  have hα5 : α ^ 5 = 1 := by
    show (MulAut.conjNormal (H := L) b) ^ 5 = 1
    rw [← map_pow (MulAut.conjNormal (H := L)) b 5, hb5, map_one]
  have hEexp : ∀ x ∈ E, x ^ 31 = 1 := by
    intro x hx
    have hx' : (x : X) ∈ A₁ ⊔ A₂ := by
      simpa [E, Subgroup.mem_subgroupOf] using hx
    have h := hAexp (x : X) hx'
    exact Subtype.ext (by simpa using h)
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    have hx' : (x : X) ∈ A₁ ⊔ A₂ := by
      simpa [E, Subgroup.mem_subgroupOf] using hx
    have hy' : (y : X) ∈ A₁ ⊔ A₂ := by
      simpa [E, Subgroup.mem_subgroupOf] using hy
    have h := hAcomm (x : X) hx' (y : X) hy'
    exact Subtype.ext (by simpa using h)
  have hbA₁ : b ∈ normalizer (A₁ : Set X) := hBA₁ hb
  have hbA₂ : b ∈ normalizer (A₂ : Set X) := hBA₂ hb
  have hbA : b ∈ normalizer ((A₁ ⊔ A₂ : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_sup]
    rw [(Subgroup.mem_normalizer_iff_map_conj_eq).mp hbA₁,
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hbA₂]
  have hEmap_le : E.map α.toMonoidHom ≤ E := by
    intro y hy
    obtain ⟨x, hxE, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_subgroupOf] at hxE ⊢
    have hmem : b * (x : X) * b⁻¹ ∈ (A₁ ⊔ A₂ : Subgroup X) :=
      (Subgroup.mem_normalizer_iff.mp hbA (x : X)).mp hxE
    simpa [α, MulAut.conjNormal_apply] using hmem
  have hEmap : E.map α.toMonoidHom = E := by
    refine Subgroup.eq_of_le_of_card_ge hEmap_le ?_
    rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) (K := E) α.injective]
  obtain ⟨N, k, hN, hNk⟩ := hP α E hα5 hEexp hEcomm hEmap
  have hpow : ∀ a ∈ A₁ ⊔ A₂, b ^ N * a * (b ^ N)⁻¹ = a ^ k := by
    intro a ha
    let x : ↥L := ⟨a, hAleL ha⟩
    have hxE : x ∈ E := by
      rw [Subgroup.mem_subgroupOf]
      exact ha
    have h := hNk x hxE
    have hαN : α ^ N = MulAut.conjNormal (H := L) (b ^ N) := by
      show (MulAut.conjNormal (H := L) b) ^ N = MulAut.conjNormal (H := L) (b ^ N)
      rw [← map_pow (MulAut.conjNormal (H := L)) b N]
    have hval := congrArg (fun y : ↥L => (y : X)) h
    rw [hαN] at hval
    have hconj : ((MulAut.conjNormal (H := L) (b ^ N)) x : X) =
        b ^ N * (x : X) * (b ^ N)⁻¹ :=
      MulAut.conjNormal_apply (H := L) (b ^ N) x
    rw [hconj] at hval
    simpa [x] using hval
  exact false_of_power_lines hA₁ hA₂ h12 hc hB hb hb1 hN hpow hlines

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
