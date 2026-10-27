module

public import CFSG.Quasithin.Background.OperatorJordanHolderJH1

public section

namespace CFSG.Quasithin.CubicCount

open CFSG.Quasithin.OperatorJH
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def midExp (b : Bool) : ℕ := cond b 2 1

@[expose] def cubAct (b : Bool) (g y : G) : G :=
  g ^ 3 * y * (g ^ 3)⁻¹ * (g ^ midExp b * y * (g ^ midExp b)⁻¹) * y

@[expose] def Kills (b : Bool) (g : G) (C S : Subgroup G) : Prop := ∀ s ∈ S, cubAct b g s ∈ C

@[expose] def Fixes (g : G) (C S : Subgroup G) : Prop := ∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ C

open Classical in
@[expose] noncomputable def wt (b : Bool) (g : G) (C S : Subgroup G) : ℕ :=
  if Kills b g C S then C.relIndex S else 1

open Classical in
@[expose] noncomputable def kappa (b : Bool) (g : G) (C D : Subgroup G) : ℕ :=
  if h : ∃ l, IsYSeries (Subgroup.zpowers g) C l D then (facMultiset (wt b g) h.choose D).prod
  else 1

theorem mul_mul_inv_mem {S : Subgroup G} {x x' y y' : G}
    (hx : x ∈ Subgroup.normalizer (S : Set G)) (h : x * y⁻¹ ∈ S) (h' : x' * y'⁻¹ ∈ S) :
    x * x' * (y * y')⁻¹ ∈ S := by
  have e : x * x' * (y * y')⁻¹ = (x * (x' * y'⁻¹) * x⁻¹) * (x * y⁻¹) := by group
  rw [e]
  exact S.mul_mem ((Subgroup.mem_normalizer_iff.mp hx _).mp h') h

theorem pow_conj_mem {S : Subgroup G} {g y : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    (hy : y ∈ S) (k : ℕ) : g ^ k * y * (g ^ k)⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set G)).pow_mem hg k) y).mp hy

theorem cubAct_mem {S : Subgroup G} {g y : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    (hy : y ∈ S) (b : Bool) : cubAct b g y ∈ S :=
  S.mul_mem (S.mul_mem (pow_conj_mem hg hy 3) (pow_conj_mem hg hy _)) hy

theorem cubAct_mul_mem {C S : Subgroup G} {g y c : G} (hCS : C ≤ S)
    (hSC : S ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgS : g ∈ Subgroup.normalizer (S : Set G)) (hy : y ∈ S) (hc : c ∈ C) (b : Bool) :
    cubAct b g (y * c) * (cubAct b g y)⁻¹ ∈ C := by
  have hyc : y * c * y⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hSC hy) c).mp hc
  have hycS : y * c ∈ S := S.mul_mem hy (hCS hc)
  have hpow : ∀ k : ℕ, g ^ k * (y * c) * (g ^ k)⁻¹ * (g ^ k * y * (g ^ k)⁻¹)⁻¹ ∈ C := by
    intro k
    have e : g ^ k * (y * c) * (g ^ k)⁻¹ * (g ^ k * y * (g ^ k)⁻¹)⁻¹ =
        g ^ k * (y * c * y⁻¹) * (g ^ k)⁻¹ := by group
    rw [e]
    exact pow_conj_mem hgC hyc k
  have hN : ∀ k : ℕ, g ^ k * (y * c) * (g ^ k)⁻¹ ∈ Subgroup.normalizer (C : Set G) := fun k =>
    hSC (pow_conj_mem hgS hycS k)
  exact mul_mul_inv_mem ((Subgroup.normalizer (C : Set G)).mul_mem (hN 3) (hN _))
    (mul_mul_inv_mem (hN 3) (hpow 3) (hpow _)) hyc

theorem kills_iff_inf {g : G} {S S' D : Subgroup G} (hSD : S ≤ D) (hS'D : S' ≤ D)
    (hDS : D ≤ Subgroup.normalizer (S : Set G)) (hgS : g ∈ Subgroup.normalizer (S : Set G))
    (hgS' : g ∈ Subgroup.normalizer (S' : Set G)) (hgD : g ∈ Subgroup.normalizer (D : Set G))
    (hD : (D : Set G) = (S' : Set G) * (S : Set G)) (b : Bool) :
    Kills b g S D ↔ Kills b g (S ⊓ S') S' := by
  constructor
  · intro h s hs
    exact ⟨h s (hS'D hs), cubAct_mem hgS' hs b⟩
  · intro h d hd
    have hd' : d ∈ (S' : Set G) * (S : Set G) := by
      rw [← hD]
      exact hd
    obtain ⟨s', hs', s, hs, rfl⟩ := hd'
    have h1 := cubAct_mul_mem hSD hDS hgS hgD (hS'D hs') hs b
    have h2 : cubAct b g s' ∈ S := (h s' hs').1
    have h3 := S.mul_mem h1 h2
    rwa [inv_mul_cancel_right] at h3

theorem wt_inf [Finite G] {g : G} {S S' D : Subgroup G}
    (hS : IsYSimple (Subgroup.zpowers g) S D) (hS' : IsYSimple (Subgroup.zpowers g) S' D)
    (hne : S ≠ S') (b : Bool) : wt b g S D = wt b g (S ⊓ S') S' := by
  have hgS : g ∈ Subgroup.normalizer (S : Set G) := hS.2.2.1 (Subgroup.mem_zpowers g)
  have hgS' : g ∈ Subgroup.normalizer (S' : Set G) := hS'.2.2.1 (Subgroup.mem_zpowers g)
  have hgD : g ∈ Subgroup.normalizer (D : Set G) := hS.2.2.2.1 (Subgroup.mem_zpowers g)
  have hS'N : S' ≤ Subgroup.normalizer (S : Set G) := hS'.1.le.trans hS.2.1
  have hsup : S ⊔ S' = D := hS.sup_eq hS' hne
  have hD : (D : Set G) = (S' : Set G) * (S : Set G) := by
    rw [← hsup, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right S' S hS'N
  have hidx : S.relIndex D = (S ⊓ S').relIndex S' := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hS'N
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hS'N
    rw [Subgroup.inf_relIndex_right, ← hsup, sup_comm]
    exact Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient S' S hS'N).toEquiv.symm
  have hk := kills_iff_inf hS.1.le hS'.1.le hS.2.1 hgS hgS' hgD hD b
  unfold wt
  by_cases h : Kills b g S D
  · rw [ite_eq_left h, ite_eq_left (hk.mp h), hidx]
  · rw [ite_eq_right h, ite_eq_right (mt hk.mpr h)]

theorem kappa_eq [Finite G] {g : G} {C D : Subgroup G} {l : List (Subgroup G)}
    (hl : IsYSeries (Subgroup.zpowers g) C l D) (b : Bool) :
    kappa b g C D = (facMultiset (wt b g) l D).prod := by
  have hex : ∃ l, IsYSeries (Subgroup.zpowers g) C l D := ⟨l, hl⟩
  rw [kappa, dite_eq_left hex,
    facMultiset_eq (wt b g) (fun S S' D hS hS' hne => wt_inf hS hS' hne b) _ C D rfl _ _
      hex.choose_spec hl]

theorem exists_series [Finite G] {g : G} {C D : Subgroup G} (hCD : C ≤ D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) : ∃ l, IsYSeries (Subgroup.zpowers g) C l D :=
  exists_ySeries _ rfl hCD hDC (Subgroup.zpowers_le.2 hgC) (Subgroup.zpowers_le.2 hgD)

theorem kappa_trans [Finite G] {g : G} {C E D : Subgroup G} (hCE : C ≤ E) (hED : E ≤ D)
    (hEC : E ≤ Subgroup.normalizer (C : Set G)) (hDE : D ≤ Subgroup.normalizer (E : Set G))
    (hgC : g ∈ Subgroup.normalizer (C : Set G)) (hgE : g ∈ Subgroup.normalizer (E : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (b : Bool) :
    kappa b g C D = kappa b g C E * kappa b g E D := by
  obtain ⟨l₁, hl₁⟩ := exists_series hCE hEC hgC hgE
  obtain ⟨l₂, hl₂⟩ := exists_series hED hDE hgE hgD
  rw [kappa_eq (hl₂.append hl₁) b, kappa_eq hl₁ b, kappa_eq hl₂ b, facMultiset_append _ hl₂,
    Multiset.prod_add, mul_comm]

theorem prod_wt_of_kills {g : G} {b : Bool} {C : Subgroup G} :
    ∀ (l : List (Subgroup G)) (D : Subgroup G), IsYSeries (Subgroup.zpowers g) C l D →
      Kills b g C D → (facMultiset (wt b g) l D).prod = C.relIndex D := by
  intro l
  induction l with
  | nil =>
    intro D hl _
    have hCD : C = D := hl
    subst hCD
    simp [facMultiset, Subgroup.relIndex_self]
  | cons S l ih =>
    intro D hl hk
    have hCS : C ≤ S := hl.2.le
    have hSD : S ≤ D := hl.1.1.le
    have hkS : Kills b g S D := fun d hd => hCS (hk d hd)
    have hk' : Kills b g C S := fun s hs => hk s (hSD hs)
    simp only [facMultiset, Multiset.prod_cons]
    rw [ih S hl.2 hk', wt, ite_eq_left hkS, mul_comm, Subgroup.relIndex_mul_relIndex C S D hCS hSD]

theorem kappa_of_kills [Finite G] {g : G} {C D : Subgroup G} (hCD : C ≤ D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) {b : Bool} (hk : Kills b g C D) :
    kappa b g C D = C.relIndex D := by
  obtain ⟨l, hl⟩ := exists_series hCD hDC hgC hgD
  rw [kappa_eq hl b, prod_wt_of_kills l D hl hk]

theorem sq_mem_of_isYSimple [Finite G] {Y C S : Subgroup G} (h : IsYSimple Y C S)
    (h2 : IsPGroup 2 S) : ∀ y ∈ S, y ^ 2 ∈ C ∧ ∀ z ∈ S, y * z * y⁻¹ * z⁻¹ ∈ C := by
  obtain ⟨hlt, hSC, hYC, hYS, hmax⟩ := h
  have hC : ∀ {a : G}, a ∈ Subgroup.normalizer (C : Set G) → ∀ {x : G}, x ∈ C →
      a * x * a⁻¹ ∈ C := fun ha x hx => (Subgroup.mem_normalizer_iff.mp ha x).mp hx
  let W : Subgroup G :=
    { carrier := {y | y ∈ S ∧ y ^ 2 ∈ C ∧ ∀ z ∈ S, y * z * y⁻¹ * z⁻¹ ∈ C}
      one_mem' := ⟨S.one_mem, by simp, fun z _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁S, h₁2, h₁c⟩ ⟨h₂S, h₂2, h₂c⟩
        refine ⟨S.mul_mem h₁S h₂S, ?_, fun z hz => ?_⟩
        · have e : (y₁ * y₂) ^ 2 =
              (y₁ * (y₂ * y₁ * y₂⁻¹ * y₁⁻¹) * y₁⁻¹) * (y₁ ^ 2 * y₂ ^ 2) := by
            simp only [sq]
            group
          rw [e]
          exact C.mul_mem (hC (hSC h₁S) (h₂c y₁ h₁S)) (C.mul_mem h₁2 h₂2)
        · have e : y₁ * y₂ * z * (y₁ * y₂)⁻¹ * z⁻¹ =
              y₁ * (y₂ * z * y₂⁻¹ * z⁻¹) * y₁⁻¹ * (y₁ * z * y₁⁻¹ * z⁻¹) := by group
          rw [e]
          exact C.mul_mem (hC (hSC h₁S) (h₂c z hz)) (h₁c z hz)
      inv_mem' := by
        rintro y ⟨hyS, hy2, hyc⟩
        refine ⟨S.inv_mem hyS, by rw [inv_pow]; exact C.inv_mem hy2, fun z hz => ?_⟩
        have e : y⁻¹ * z * y⁻¹⁻¹ * z⁻¹ = y⁻¹ * (y * z * y⁻¹ * z⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact hC (hSC (S.inv_mem hyS)) (C.inv_mem (hyc z hz)) }
  have hmem : ∀ y, y ∈ W ↔ y ∈ S ∧ y ^ 2 ∈ C ∧ ∀ z ∈ S, y * z * y⁻¹ * z⁻¹ ∈ C := fun _ =>
    Iff.rfl
  have hCW : C ≤ W := by
    intro c hc
    refine ⟨hlt.le hc, by rw [sq]; exact C.mul_mem hc hc, fun z hz => ?_⟩
    have e : c * z * c⁻¹ * z⁻¹ = c * (z * c⁻¹ * z⁻¹) := by group
    rw [e]
    exact C.mul_mem hc (hC (hSC hz) (C.inv_mem hc))
  have hWS : W ≤ S := fun y hy => hy.1
  have hconj : ∀ a ∈ Subgroup.normalizer (S : Set G), a ∈ Subgroup.normalizer (C : Set G) →
      ∀ y ∈ W, a * y * a⁻¹ ∈ W := by
    rintro a haS haC y ⟨hyS, hy2, hyc⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp haS y).mp hyS, ?_, fun z hz => ?_⟩
    · have e : (a * y * a⁻¹) ^ 2 = a * y ^ 2 * a⁻¹ := by
        simp only [sq]
        group
      rw [e]
      exact hC haC hy2
    · have hz' : a⁻¹ * z * a⁻¹⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set G)).inv_mem haS) z).mp hz
      have e : a * y * a⁻¹ * z * (a * y * a⁻¹)⁻¹ * z⁻¹ =
          a * (y * (a⁻¹ * z * a⁻¹⁻¹) * y⁻¹ * (a⁻¹ * z * a⁻¹⁻¹)⁻¹) * a⁻¹ := by group
      rw [e]
      exact hC haC (hyc _ hz')
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := fun s hs =>
    mem_normalizer_of_conj_mem_of fun y hy =>
      hconj s (Subgroup.le_normalizer hs) (hSC hs) y hy
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem_of fun y hy => hconj a (hYS ha) (hYC ha) y hy
  rcases hmax W hCW hWS hSW hYW with hWC | hWS'
  ·
    exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hN : (C.subgroupOf S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hlt.le).mpr hSC
    obtain ⟨s, hsS, hsC⟩ := IsConcreteLE.exists_of_lt hlt
    have hP : IsPGroup 2 (↥S ⧸ C.subgroupOf S) := h2.to_quotient _
    have hnt : Nontrivial (↥S ⧸ C.subgroupOf S) := by
      refine nontrivial_of_ne (QuotientGroup.mk ⟨s, hsS⟩) 1 fun h1 => hsC ?_
      rw [QuotientGroup.eq_one_iff] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    have hZ := hP.center_nontrivial
    obtain ⟨n, hn0, hcard⟩ :=
      (hP.to_subgroup (Subgroup.center (↥S ⧸ C.subgroupOf S))).nontrivial_iff_card.mp hZ
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2
      (hcard ▸ dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn0))
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (z : ↥S ⧸ C.subgroupOf S)
    have hz2 : (z : ↥S ⧸ C.subgroupOf S) ^ 2 = 1 := by
      rw [← Subgroup.orderOf_coe] at hz
      rw [← hz]
      exact pow_orderOf_eq_one _
    have hz1 : (z : ↥S ⧸ C.subgroupOf S) ≠ 1 := by
      intro h1
      rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hyW : (y : G) ∈ W := by
      refine ⟨y.2, ?_, fun w hw => ?_⟩
      · have h1 : (QuotientGroup.mk (y ^ 2) : ↥S ⧸ C.subgroupOf S) = 1 := by
          rw [QuotientGroup.mk_pow, hy, hz2]
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
        simpa using h1
      · have hcen := Subgroup.mem_center_iff.mp z.2 (QuotientGroup.mk ⟨w, hw⟩)
        have h1 : (QuotientGroup.mk (y * ⟨w, hw⟩ * y⁻¹ * (⟨w, hw⟩ : ↥S)⁻¹) :
            ↥S ⧸ C.subgroupOf S) = 1 := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
            QuotientGroup.mk_inv, QuotientGroup.mk_inv, hy, ← hcen]
          group
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
        simpa using h1
    rw [hWC] at hyW
    apply hz1
    rw [← hy, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hyW
  · intro y hy
    have hyW : y ∈ W := hWS' ▸ hy
    exact ⟨hyW.2.1, hyW.2.2⟩

theorem le_of_fixes_of_kills {g : G} {C S : Subgroup G}
    (hSC : S ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgS : g ∈ Subgroup.normalizer (S : Set G)) (hsq : ∀ y ∈ S, y ^ 2 ∈ C) (hf : Fixes g C S)
    {b : Bool} (hk : Kills b g C S) : S ≤ C := by
  intro y hy
  have hpow : ∀ k : ℕ, g ^ k * y * (g ^ k)⁻¹ * y⁻¹ ∈ C := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : g ^ (k + 1) * y * (g ^ (k + 1))⁻¹ * y⁻¹ =
          g * (g ^ k * y * (g ^ k)⁻¹ * y⁻¹) * g⁻¹ * (g * y * g⁻¹ * y⁻¹) := by group
      rw [e]
      exact C.mul_mem ((Subgroup.mem_normalizer_iff.mp hgC _).mp ih) (hf y hy)
  have h3 : cubAct b g y * y⁻¹ ∈ C := by
    have e : cubAct b g y * y⁻¹ =
        (g ^ 3 * y * (g ^ 3)⁻¹ * (g ^ midExp b * y * (g ^ midExp b)⁻¹)) * (y * y)⁻¹ * y ^ 2 := by
      unfold cubAct
      group
    rw [e]
    exact C.mul_mem (mul_mul_inv_mem (hSC (pow_conj_mem hgS hy 3)) (hpow 3) (hpow _))
      (hsq y hy)
  have h4 := C.mul_mem (C.inv_mem h3) (hk y hy)
  have e : (cubAct b g y * y⁻¹)⁻¹ * cubAct b g y = y := by group
  rwa [e] at h4

theorem fixes_of_kills_kills {g : G} {C S : Subgroup G}
    (hSC : S ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgS : g ∈ Subgroup.normalizer (S : Set G)) (h1 : Kills false g C S)
    (h2 : Kills true g C S) : Fixes g C S := by
  intro y hy
  have k1 : g ^ 3 * y * (g ^ 3)⁻¹ * (g ^ 1 * y * (g ^ 1)⁻¹) * y ∈ C := h1 y hy
  have k2 : g ^ 3 * y * (g ^ 3)⁻¹ * (g ^ 2 * y * (g ^ 2)⁻¹) * y ∈ C := h2 y hy
  have hA : g ^ 3 * y * (g ^ 3)⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
    hSC (pow_conj_mem hgS hy 3)
  have h3 := C.mul_mem k2 (C.inv_mem k1)
  have e : g ^ 3 * y * (g ^ 3)⁻¹ * (g ^ 2 * y * (g ^ 2)⁻¹) * y *
      (g ^ 3 * y * (g ^ 3)⁻¹ * (g ^ 1 * y * (g ^ 1)⁻¹) * y)⁻¹ =
      g ^ 3 * y * (g ^ 3)⁻¹ * (g * (g * y * g⁻¹ * y⁻¹) * g⁻¹) * (g ^ 3 * y * (g ^ 3)⁻¹)⁻¹ := by
    group
  rw [e] at h3
  exact (Subgroup.mem_normalizer_iff.mp hgC _).mpr
    ((Subgroup.mem_normalizer_iff.mp hA _).mpr h3)

theorem prod_wt_eq_one {g : G} {b : Bool} {C D₀ : Subgroup G}
    (hno : ∀ S S' : Subgroup G, IsYSimple (Subgroup.zpowers g) S S' → C ≤ S → S' ≤ D₀ →
      ¬ Kills b g S S') :
    ∀ (l : List (Subgroup G)) (D : Subgroup G), IsYSeries (Subgroup.zpowers g) C l D → D ≤ D₀ →
      (facMultiset (wt b g) l D).prod = 1 := by
  intro l
  induction l with
  | nil =>
    intro D _ _
    simp [facMultiset]
  | cons S l ih =>
    intro D hl hD
    simp only [facMultiset, Multiset.prod_cons]
    rw [ih S hl.2 (hl.1.1.le.trans hD), wt, ite_eq_right (hno S D hl.1 hl.2.le hD), one_mul]

theorem kappa_eq_one_of_kills [Finite G] {g : G} {C D : Subgroup G} (hCD : C ≤ D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hD2 : IsPGroup 2 D) {b : Bool}
    (hk : Kills (!b) g C D) : kappa b g C D = 1 := by
  obtain ⟨l, hl⟩ := exists_series hCD hDC hgC hgD
  rw [kappa_eq hl b]
  refine prod_wt_eq_one (D₀ := D) (fun S S' hS hCS hS'D hkS => ?_) l D hl le_rfl
  have hgS : g ∈ Subgroup.normalizer (S : Set G) := hS.2.2.1 (Subgroup.mem_zpowers g)
  have hgS' : g ∈ Subgroup.normalizer (S' : Set G) := hS.2.2.2.1 (Subgroup.mem_zpowers g)
  have hsq := sq_mem_of_isYSimple hS (hD2.to_le hS'D)
  have hk' : Kills (!b) g S S' := fun s hs => hCS (hk s (hS'D hs))
  have hfix : Fixes g S S' := by
    cases b with
    | false => exact fixes_of_kills_kills hS.2.1 hgS hgS' hkS hk'
    | true => exact fixes_of_kills_kills hS.2.1 hgS hgS' hk' hkS
  exact not_le_of_gt hS.1
    (le_of_fixes_of_kills hS.2.1 hgS hgS' (fun y hy => (hsq y hy).1) hfix hkS)

theorem kappa_eq_one_of_fixes [Finite G] {g : G} {C D : Subgroup G} (hCD : C ≤ D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hD2 : IsPGroup 2 D) (hf : Fixes g C D)
    (b : Bool) : kappa b g C D = 1 := by
  obtain ⟨l, hl⟩ := exists_series hCD hDC hgC hgD
  rw [kappa_eq hl b]
  refine prod_wt_eq_one (D₀ := D) (fun S S' hS hCS hS'D hkS => ?_) l D hl le_rfl
  have hgS : g ∈ Subgroup.normalizer (S : Set G) := hS.2.2.1 (Subgroup.mem_zpowers g)
  have hgS' : g ∈ Subgroup.normalizer (S' : Set G) := hS.2.2.2.1 (Subgroup.mem_zpowers g)
  have hsq := sq_mem_of_isYSimple hS (hD2.to_le hS'D)
  have hf' : Fixes g S S' := fun s hs => hCS (hf s (hS'D hs))
  exact not_le_of_gt hS.1
    (le_of_fixes_of_kills hS.2.1 hgS hgS' (fun y hy => (hsq y hy).1) hf' hkS)

theorem kappa_ne_zero [Finite G] (b : Bool) (g : G) (C D : Subgroup G) : kappa b g C D ≠ 0 := by
  have key : ∀ (l : List (Subgroup G)) (D : Subgroup G), (facMultiset (wt b g) l D).prod ≠ 0 := by
    intro l
    induction l with
    | nil =>
      intro D
      simp [facMultiset]
    | cons S l ih =>
      intro D
      simp only [facMultiset, Multiset.prod_cons]
      refine mul_ne_zero ?_ (ih S)
      unfold wt
      split_ifs
      · exact Subgroup.index_ne_zero_of_finite
      · exact one_ne_zero
  unfold kappa
  split_ifs with h
  · exact key _ _
  · exact one_ne_zero

section Map

variable {G' : Type} [Group G'] (e : G ≃* G')

theorem cubAct_map (b : Bool) (g y : G) : cubAct b (e g) (e y) = e (cubAct b g y) := by
  simp only [cubAct, map_mul, map_pow, map_inv]

theorem wt_map (b : Bool) (g : G) (S D : Subgroup G) :
    wt b (e g) (S.map e.toMonoidHom) (D.map e.toMonoidHom) = wt b g S D := by
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hk : Kills b (e g) (S.map e.toMonoidHom) (D.map e.toMonoidHom) ↔ Kills b g S D := by
    constructor
    · intro h d hd
      have h1 := h (e d) ⟨d, hd, rfl⟩
      rw [cubAct_map] at h1
      exact (Subgroup.mem_map_iff_mem hinj).mp h1
    · rintro h _ ⟨d, hd, rfl⟩
      have h1 := cubAct_map e b g d
      simp only [MulEquiv.coe_toMonoidHom] at h1 ⊢
      rw [h1]
      exact ⟨_, h d hd, rfl⟩
  unfold wt
  by_cases h : Kills b g S D
  · rw [ite_eq_left (hk.mpr h), ite_eq_left h, Subgroup.relIndex_map_map_of_injective S D hinj]
  · rw [ite_eq_right (mt hk.mp h), ite_eq_right h]

theorem isYSimple_map {Y C S : Subgroup G} (h : IsYSimple Y C S) :
    IsYSimple (Y.map e.toMonoidHom) (C.map e.toMonoidHom) (S.map e.toMonoidHom) := by
  obtain ⟨hlt, hSC, hYC, hYS, hmax⟩ := h
  have hinj : Function.Injective e.toMonoidHom := e.injective
  refine ⟨(Subgroup.map_lt_map_iff_of_injective hinj).2 hlt, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hSC
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hYC
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hYS
  · intro J hCJ hJS hSJ hYJ
    obtain ⟨J₀, rfl⟩ : ∃ J₀ : Subgroup G, J₀.map e.toMonoidHom = J :=
      ⟨J.comap e.toMonoidHom, Subgroup.map_comap_eq_self_of_surjective e.surjective J⟩
    rw [← Subgroup.map_equiv_normalizer_eq] at hSJ hYJ
    rw [Subgroup.map_le_map_iff_of_injective hinj] at hCJ hJS hSJ hYJ
    rcases hmax J₀ hCJ hJS hSJ hYJ with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

theorem isYSeries_map {Y C : Subgroup G} :
    ∀ (l : List (Subgroup G)) (D : Subgroup G), IsYSeries Y C l D →
      IsYSeries (Y.map e.toMonoidHom) (C.map e.toMonoidHom) (l.map (Subgroup.map e.toMonoidHom))
        (D.map e.toMonoidHom) := by
  intro l
  induction l with
  | nil =>
    intro D h
    have hCD : C = D := h
    subst hCD
    exact rfl
  | cons S l ih =>
    intro D h
    exact ⟨isYSimple_map e h.1, ih S h.2⟩

theorem facMultiset_map (b : Bool) (g : G) :
    ∀ (l : List (Subgroup G)) (D : Subgroup G),
      facMultiset (wt b (e g)) (l.map (Subgroup.map e.toMonoidHom)) (D.map e.toMonoidHom) =
        facMultiset (wt b g) l D := by
  intro l
  induction l with
  | nil =>
    intro D
    rfl
  | cons S l ih =>
    intro D
    simp only [List.map_cons, facMultiset]
    rw [ih S, wt_map e]

theorem kappa_map [Finite G] [Finite G'] (b : Bool) (g : G) {C D : Subgroup G} (hCD : C ≤ D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) :
    kappa b (e g) (C.map e.toMonoidHom) (D.map e.toMonoidHom) = kappa b g C D := by
  obtain ⟨l, hl⟩ := exists_series hCD hDC hgC hgD
  have hl' := isYSeries_map e l D hl
  rw [MonoidHom.map_zpowers] at hl'
  rw [kappa_eq hl b, ← facMultiset_map e b g l D]
  exact kappa_eq hl' b

end Map

theorem kappa_conj [Finite G] (t : G) (b : Bool) (g : G) {C D : Subgroup G} (hCD : C ≤ D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) :
    kappa b (t * g * t⁻¹) (C.map (MulAut.conj t).toMonoidHom)
      (D.map (MulAut.conj t).toMonoidHom) = kappa b g C D :=
  kappa_map (MulAut.conj t) b g hCD hDC hgC hgD

theorem kappa_conj_of_mem [Finite G] {t : G} (b : Bool) (g : G) {C D : Subgroup G} (hCD : C ≤ D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) (hgC : g ∈ Subgroup.normalizer (C : Set G))
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (htC : t ∈ Subgroup.normalizer (C : Set G))
    (htD : t ∈ Subgroup.normalizer (D : Set G)) :
    kappa b (t * g * t⁻¹) C D = kappa b g C D := by
  have h := kappa_conj t b g hCD hDC hgC hgD
  have hC : C.map (MulAut.conj t).toMonoidHom = C := by
    rw [MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp htC
  have hD : D.map (MulAut.conj t).toMonoidHom = D := by
    rw [MulEquiv.toMonoidHom_eq_coe]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp htD
  rwa [hC, hD] at h

end CFSG.Quasithin.CubicCount
