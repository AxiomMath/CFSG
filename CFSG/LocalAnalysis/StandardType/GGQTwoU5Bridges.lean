module

public import CFSG.Models
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52Bridge

public section

namespace CFSG.StandardType.QTwo.U5

open Subgroup CFSG.Open CFSG.Models
open CFSG.GGQ2Prime (outThree_of_equiv conjAut U52OrderThreeAutInner lieModel_PSU_five)

section Abstract

variable {L : Type*} [Group L]

theorem conj_central_eq {c : L} (hc : c ∈ center L) (g : L) : c * g * c⁻¹ = g := by
  rw [mem_center_iff] at hc
  rw [← hc g]; group

theorem eq_of_mul_inv_mem_center (hperf : commutator L = ⊤) (α : MulAut L)
    (h : ∀ y, α y * y⁻¹ ∈ center L) (y : L) : α y = y := by
  have key : commutator L ≤ MonoidHom.eqLocus (α : L →* L) (MonoidHom.id L) := by
    rw [commutator_def, commutator_le]
    intro x _ z _
    have hx := h x
    have hz := h z
    set c := α x * x⁻¹ with hcdef
    set d := α z * z⁻¹ with hddef
    have hax : α x = c * x := by rw [hcdef]; group
    have haz : α z = d * z := by rw [hddef]; group
    show α (x * z * x⁻¹ * z⁻¹) = x * z * x⁻¹ * z⁻¹
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hax, haz]
    have hdx : x * d = d * x := (mem_center_iff.1 hz x)
    calc c * x * (d * z) * (c * x)⁻¹ * (d * z)⁻¹
        = c * (x * (d * z) * x⁻¹) * c⁻¹ * (z⁻¹ * d⁻¹) := by group
      _ = x * (d * z) * x⁻¹ * (z⁻¹ * d⁻¹) := by rw [conj_central_eq hx]
      _ = d * (x * z * x⁻¹ * z⁻¹) * d⁻¹ := by
          rw [show x * (d * z) = x * d * z by group, hdx]; group
      _ = x * z * x⁻¹ * z⁻¹ := conj_central_eq hz _
  have : y ∈ MonoidHom.eqLocus (α : L →* L) (MonoidHom.id L) := key (hperf ▸ mem_top y)
  exact this

theorem eq_conj_of_mod_center (hperf : commutator L = ⊤) (α : MulAut L) (r : L)
    (h : ∀ y, α y * (r * y * r⁻¹)⁻¹ ∈ center L) (y : L) : α y = r * y * r⁻¹ := by
  have hβ := eq_of_mul_inv_mem_center hperf ((MulAut.conj r)⁻¹ * α) (fun y => by
    have hy := h y
    rw [MulAut.mul_apply, MulAut.conj_inv_apply]
    have : r⁻¹ * α y * r * y⁻¹ = r⁻¹ * (α y * (r * y * r⁻¹)⁻¹) * r := by group
    rw [this]
    have hc := mem_center_iff.1 hy
    rw [show r⁻¹ * (α y * (r * y * r⁻¹)⁻¹) * r = α y * (r * y * r⁻¹)⁻¹ by
      rw [mul_assoc, ← hc r]; group]
    exact hy) y
  rw [MulAut.mul_apply, MulAut.conj_inv_apply] at hβ
  calc α y = r * (r⁻¹ * α y * r) * r⁻¹ := by group
    _ = r * y * r⁻¹ := by rw [hβ]

@[expose] noncomputable def quotAut (α : MulAut L) : MulAut (L ⧸ center L) :=
  QuotientGroup.congr (center L) (center L) α
    (characteristic_iff_map_eq.mp inferInstance α)

theorem quotAut_mk (α : MulAut L) (y : L) :
    quotAut α (y : L ⧸ center L) = ((α y : L) : L ⧸ center L) :=
  QuotientGroup.congr_mk _ _ _ _ y

theorem quotAut_pow_three (α : MulAut L) (h : α ^ 3 = 1) : quotAut α ^ 3 = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    have hy : α (α (α y)) = y := by
      have := congrArg (fun φ : MulAut L => φ y) h
      simpa [pow_succ, MulAut.mul_apply] using this
    simp [pow_succ, MulAut.mul_apply, quotAut_mk, hy]

theorem inner_of_pow_three (hperf : commutator L = ⊤)
    (hout : ∀ φ : MulAut (L ⧸ center L), φ ^ 3 = 1 → ∃ r, φ = MulAut.conj r)
    (α : MulAut L) (h3 : α ^ 3 = 1) : ∃ l : L, ∀ y, α y = l * y * l⁻¹ := by
  obtain ⟨r, hr⟩ := hout (quotAut α) (quotAut_pow_three α h3)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective r
  refine ⟨l, eq_conj_of_mod_center hperf α l fun y => ?_⟩
  have := congrArg (fun φ : MulAut (L ⧸ center L) => φ (y : L ⧸ center L)) hr
  simp only [quotAut_mk, MulAut.conj_apply] at this
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at this
  rw [← div_eq_mul_inv]
  exact (QuotientGroup.eq_iff_div_mem).1 this

end Abstract

section InG

variable {G : Type*} [Group G]

theorem inner_of_normalizer_pow_three (L : Subgroup G) (hperf : commutator L = ⊤)
    (hout : ∀ φ : MulAut (L ⧸ center L), φ ^ 3 = 1 → ∃ r, φ = MulAut.conj r)
    {b : G} (hb : b ∈ normalizer (L : Set G)) (hb3 : b ^ 3 = 1) :
    ∃ l ∈ L, ∀ y ∈ L, b * y * b⁻¹ = l * y * l⁻¹ := by
  have h3 : conjAut L hb ^ 3 = 1 := by
    ext t
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply]
    show b * (b * (b * (t : G) * b⁻¹) * b⁻¹) * b⁻¹ = t
    have : b * (b * (b * (t : G) * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * t * (b * b * b)⁻¹ := by
      group
    rw [this, show b * b * b = b ^ 3 by rw [pow_succ, pow_succ, pow_one], hb3]; group
  obtain ⟨l, hl⟩ := inner_of_pow_three hperf hout (conjAut L hb) h3
  exact ⟨l, l.2, fun y hy => congrArg Subtype.val (hl ⟨y, hy⟩)⟩

end InG

section Models

@[expose] def U52MultiplierTrivial : Prop :=
  ∀ (E : Type) [Group E] [Finite E], commutator E = ⊤ →
    LieModel (E ⧸ center E) .PSU 5 2 1 → Nat.card (center E) = 1

variable {G : Type} [Group G]

theorem bridge_inner_U52 (hU : U52OrderThreeAutInner) (L : Subgroup G)
    (hperf : commutator L = ⊤) (hL : LieModel (L ⧸ center L) .PSU 5 2 1)
    {b : G} (hb : b ∈ normalizer (L : Set G)) (hb3 : b ^ 3 = 1) :
    ∃ l ∈ L, ∀ y ∈ L, b * y * b⁻¹ = l * y * l⁻¹ := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := lieModel_PSU_five hL
  exact inner_of_normalizer_pow_three L hperf (outThree_of_equiv e (hU K hF hfin hK)) hb hb3

theorem bridge_center_U52 [Finite G] (hM : U52MultiplierTrivial) (L : Subgroup G)
    (hperf : commutator L = ⊤) (hL : LieModel (L ⧸ center L) .PSU 5 2 1) :
    ¬ 3 ∣ Nat.card (center L) := by
  rw [hM L hperf hL]; norm_num

section Noncyclic

variable {L : Type} [Group L]

theorem lift_pow_three (hZ : ∀ z ∈ center L, z ^ 2 = 1) (xb : L ⧸ center L) (hx : xb ^ 3 = 1) :
    ∃ x : L, (x : L ⧸ center L) = xb ∧ x ^ 3 = 1 := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xb
  have hc : x₀ ^ 3 ∈ center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hx]
  refine ⟨x₀ ^ 4, ?_, ?_⟩
  · rw [show x₀ ^ 4 = x₀ * x₀ ^ 3 by group, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 hc, mul_one]
  · rw [show (x₀ ^ 4) ^ 3 = ((x₀ ^ 3) ^ 2) ^ 2 by group, hZ _ hc, one_pow]

theorem commute_of_pow_three (hZ : ∀ z ∈ center L, z ^ 2 = 1) {x y : L} (hx : x ^ 3 = 1)
    (hxy : (x : L ⧸ center L) * y = y * x) : x * y = y * x := by
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hc : c ∈ center L := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxy]
    group
  have hcc := mem_center_iff.1 hc
  have h1 : x * y * x⁻¹ = c * y := by rw [hcdef]; group
  have hconj : ∀ k : ℕ, x ^ k * y * (x ^ k)⁻¹ = c ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * y * (x ^ (k + 1))⁻¹ = x * (x ^ k * y * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * (c ^ k * y) * x⁻¹ := by rw [ih]
        _ = c ^ k * (x * y * x⁻¹) := by
            rw [show x * (c ^ k * y) * x⁻¹ = (x * c ^ k) * y * x⁻¹ by group,
              (mem_center_iff.1 (pow_mem hc k) x)]; group
        _ = c ^ (k + 1) * y := by rw [h1]; group
  have h3 : c ^ 3 = 1 := by
    have := hconj 3
    rw [hx, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.1 this.symm)
  have hc1 : c = 1 := by
    have h2 := hZ c hc
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  calc x * y = c * (y * x) := by rw [hcdef]; group
    _ = y * x := by rw [hc1, one_mul]

theorem exists_noncyclic_three [Finite L] (hZ : ∀ z ∈ center L, z ^ 2 = 1) {xb yb : L ⧸ center L}
    (hx : xb ^ 3 = 1) (hy : yb ^ 3 = 1) (hxy : xb * yb = yb * xb) (hx1 : xb ≠ 1)
    (hyx : yb ∉ zpowers xb) : ∃ S : Subgroup L, IsPGroup 3 S ∧ ¬ IsCyclic S := by
  obtain ⟨x, rfl, hx3⟩ := lift_pow_three hZ xb hx
  obtain ⟨y, rfl, hy3⟩ := lift_pow_three hZ yb hy
  have hcomm : x * y = y * x := commute_of_pow_three hZ hx3 hxy
  set S := closure ({x, y} : Set L) with hSdef
  have hk : ∀ a ∈ ({x, y} : Set L), ∀ b ∈ ({x, y} : Set L), a * b = b * a := by
    rintro a (rfl | rfl) b (rfl | rfl) <;> first | rfl | exact hcomm | exact hcomm.symm
  have hcube : ∀ g ∈ S, g ^ 3 = 1 := by
    letI : CommGroup S := closureCommGroupOfComm (fun a ha b hb _ => (hk a ha b hb : Commute a b))
    have htop : closure (((↑) : S → L) ⁻¹' {x, y}) ≤ (powMonoidHom 3 : S →* S).ker := by
      rw [closure_le]
      rintro ⟨g, hg⟩ (hg' | hg')
      · simp only at hg'; subst hg'; ext; simp [hx3]
      · simp only [Set.mem_singleton_iff] at hg'; subst hg'; ext; simp [hy3]
    rw [closure_closure_coe_preimage] at htop
    intro g hg
    have := htop (mem_top ⟨g, hg⟩)
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at this
    exact congrArg Subtype.val this
  refine ⟨S, fun g => ⟨1, by ext; simpa using hcube g g.2⟩, ?_⟩
  rintro ⟨⟨g, hgS⟩, hg⟩
  have hxS : x ∈ S := subset_closure (by simp)
  have hyS : y ∈ S := subset_closure (by simp)
  have hg3 : g ^ 3 = 1 := hcube g hgS
  have hmem : ∀ h ∈ S, h ∈ zpowers g := by
    intro h hh
    obtain ⟨k, hk⟩ := hg ⟨h, hh⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hxne : x ≠ 1 := by rintro rfl; exact hx1 (by simp)
  have hox : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hxne
    · exact h
  have hzp : zpowers x = zpowers g := by
    apply eq_of_le_of_card_ge ((zpowers_le).2 (hmem x hxS))
    rw [Nat.card_zpowers, Nat.card_zpowers, hox]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
  have hyx' : y ∈ zpowers x := hzp ▸ hmem y hyS
  obtain ⟨k, hk⟩ := hyx'
  exact hyx ⟨k, by rw [← hk, QuotientGroup.mk_zpow]⟩

end Noncyclic

@[expose] def U52NoncyclicPair : Prop :=
  ∀ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ 1) ^ 2 →
    ∃ x y : StatedProj (StatedSU 5 (2 ^ 1) K), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧
      y ∉ zpowers x

theorem noncyclic_of_model [Finite G] (L : Subgroup G) {M : Type} [Group M]
    (e : (L ⧸ center L) ≃* M) (hZ : Nat.card (center L) ∣ 2)
    (hW : ∃ x y : M, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ x ≠ 1 ∧ y ∉ zpowers x) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  obtain ⟨x, y, hx, hy, hxy, hx1, hyx⟩ := hW
  have hZ2 : ∀ z ∈ center L, z ^ 2 = 1 := by
    intro z hz
    have : orderOf (⟨z, hz⟩ : center L) ∣ 2 := (_root_.orderOf_dvd_natCard _).trans hZ
    have h := orderOf_dvd_iff_pow_eq_one.1 this
    simpa using congrArg Subtype.val h
  obtain ⟨S, hS3, hSc⟩ := exists_noncyclic_three hZ2 (xb := e.symm x) (yb := e.symm y)
    (by rw [← map_pow, hx, map_one]) (by rw [← map_pow, hy, map_one])
    (by rw [← map_mul, ← map_mul, hxy])
    (by intro h; exact hx1 (by simpa using congrArg e h))
    (by
      rintro ⟨k, hk⟩
      exact hyx ⟨k, by simpa using congrArg e hk⟩)
  refine ⟨S.map L.subtype, map_subtype_le S, hS3.map _, ?_⟩
  intro hc
  apply hSc
  exact (S.equivMapOfInjective L.subtype Subtype.val_injective).isCyclic.mpr hc

theorem bridge_noncyclic_U52 [Finite G] (hM : U52MultiplierTrivial) (hW : U52NoncyclicPair)
    (L : Subgroup G) (hperf : commutator L = ⊤) (hL : LieModel (L ⧸ center L) .PSU 5 2 1) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := lieModel_PSU_five hL
  exact noncyclic_of_model L e (by rw [hM L hperf hL]; norm_num) (hW K hF hfin hK)

end Models

end CFSG.StandardType.QTwo.U5

end
