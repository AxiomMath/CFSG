module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly

section CenterQuot

variable (H : Type*) [Group H]

@[expose] noncomputable def centerQuotAut : MulAut H →* MulAut (H ⧸ Subgroup.center H) where
  toFun f := QuotientGroup.congr (Subgroup.center H) (Subgroup.center H) f
    (Subgroup.characteristic_iff_map_eq.mp inferInstance f)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' f g := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

variable {H}

@[simp]
theorem centerQuotAut_mk (f : MulAut H) (h : H) :
    centerQuotAut H f (h : H ⧸ Subgroup.center H) = (f h : H ⧸ Subgroup.center H) :=
  rfl

end CenterQuot

section Induced

variable {G : Type*} [Group G] (L : Subgroup G) {R : Type} [Group R]
  (θ : L ⧸ Subgroup.center L ≃* R)

@[expose] noncomputable def ggLAut : Subgroup.normalizer (L : Set G) →* MulAut R :=
  (MulAut.congr θ).toMonoidHom.comp ((centerQuotAut L).comp L.normalizerMonoidHom)

theorem normalizerMonoidHom_coe (g : Subgroup.normalizer (L : Set G)) (l : L) :
    ((L.normalizerMonoidHom g l : L) : G) = (g : G) * l * (g : G)⁻¹ :=
  rfl

theorem ggLAut_apply (g : Subgroup.normalizer (L : Set G)) (l : L) :
    ggLAut L θ g (θ (l : L ⧸ Subgroup.center L)) =
      θ ((L.normalizerMonoidHom g l : L) : L ⧸ Subgroup.center L) := by
  simp [ggLAut, MulAut.congr_apply]

theorem eq_ggLAut_of_induces {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G)) {φ : MulAut R}
    (h : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    φ = ggLAut L θ ⟨b⁻¹, inv_mem hb⟩ := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [ggLAut_apply]
    apply h
    rw [normalizerMonoidHom_coe]
    simp

theorem ggLAut_mem_of_induces {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {I : Set (MulAut R)}
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    {b : G} (hb : b ∈ B) : ggLAut L θ ⟨b, hBN hb⟩ ∈ I := by
  obtain ⟨φ, hφ, hind⟩ := h3 b⁻¹ (inv_mem hb)
  rw [eq_ggLAut_of_induces L θ (hBN (inv_mem hb)) hind] at hφ
  convert hφ using 3
  simp

theorem mem_centralizer_of_ggLAut_eq_one (hL : commutator L = ⊤)
    {g : Subgroup.normalizer (L : Set G)} (hg : ggLAut L θ g = 1) :
    (g : G) ∈ Subgroup.centralizer (L : Set G) := by
  set c := L.normalizerMonoidHom g
  have hz : ∀ l : L, c l * l⁻¹ ∈ Subgroup.center L := by
    intro l
    have h1 := congrArg (fun φ => φ (θ (l : L ⧸ Subgroup.center L))) hg
    simp only [ggLAut_apply, MulAut.one_apply] at h1
    have h2 : l⁻¹ * c l ∈ Subgroup.center L := by
      have := inv_mem (QuotientGroup.eq.mp (θ.injective h1))
      simpa [mul_inv_rev] using this
    have h3 : c l * l⁻¹ = l⁻¹ * c l := by
      have := (Subgroup.mem_center_iff.mp h2) l
      calc c l * l⁻¹ = (l * (l⁻¹ * c l)) * l⁻¹ := by group
        _ = ((l⁻¹ * c l) * l) * l⁻¹ := by rw [this]
        _ = l⁻¹ * c l := by group
    rw [h3]
    exact h2
  let f : L →* L :=
    { toFun := fun l => c l * l⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have h := (Subgroup.mem_center_iff.mp (hz b)) a⁻¹
        simp only [map_mul, mul_inv_rev]
        calc c a * c b * (b⁻¹ * a⁻¹) = c a * ((c b * b⁻¹) * a⁻¹) := by group
          _ = c a * (a⁻¹ * (c b * b⁻¹)) := by rw [h]
          _ = c a * a⁻¹ * (c b * b⁻¹) := by group }
  have hker : commutator L ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hz b)) (f a)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : f ⟨y, hy⟩ = 1 := hker (by rw [hL]; exact Subgroup.mem_top _)
  have h2 : c ⟨y, hy⟩ = ⟨y, hy⟩ := mul_inv_eq_one.mp h1
  have h3 : (g : G) * y * (g : G)⁻¹ = y := congrArg Subtype.val h2
  calc y * g = (g : G) * y * (g : G)⁻¹ * g := by rw [h3]
    _ = g * y := by group

end Induced

namespace TableB

variable {G : Type*} [Group G]

theorem isElemAbelian_mono {p : ℕ} {E F : Subgroup G} (hF : IsElemAbelian p F) (hEF : E ≤ F) :
    IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hF hEF

theorem isPGroup_of_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem IsElemAbelian.comm {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem card_le_of_isCyclic {p : ℕ} (hp : 0 < p) {E : Subgroup G} [Finite E] (hc : IsCyclic E)
    (he : ∀ y ∈ E, y ^ p = 1) : Nat.card E ≤ p := by
  obtain ⟨e, he'⟩ := hc.exists_generator
  rw [← orderOf_eq_card_of_forall_mem_zpowers he']
  exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using he _ e.2)))

theorem not_isCyclic_of_card {p : ℕ} (hp : 1 < p) {E : Subgroup G} [Finite E]
    (he : ∀ y ∈ E, y ^ p = 1) (hcard : p ^ 2 ≤ Nat.card E) : ¬ IsCyclic E := by
  intro hc
  have := card_le_of_isCyclic (by omega) hc he
  nlinarith

theorem card_range_mul_card_ker {H M : Type*} [Group H] [Group M] [Finite H] (f : H →* M) :
    Nat.card f.range * Nat.card f.ker = Nat.card H := by
  rw [mul_comm]
  exact Subgroup.card_ker_mul_card_range f

end TableB

open TableB

section SStar

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_of_le_centralizer {x : G} {L : Subgroup G}
    (h : L ≤ Subgroup.centralizer ({x} : Set G)) : x ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact Subgroup.mem_centralizer_singleton_iff.mp (h hl)

theorem inf_centralizer_eq_zpowers_of_sstar {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) :
    B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  have := Fact.mk hp
  obtain ⟨⟨hBe, -, -⟩, hxB, hx1, hLC, hcyc⟩ := hS
  have hxC := mem_centralizer_of_le_centralizer hLC.1
  have hE : IsElemAbelian p (B ⊓ Subgroup.centralizer (L : Set G)) :=
    isElemAbelian_mono hBe inf_le_left
  have hcE := hcyc _ inf_le_right (isPGroup_of_isElemAbelian hE)
  have hle : Subgroup.zpowers x ≤ B ⊓ Subgroup.centralizer (L : Set G) :=
    (Subgroup.zpowers_le).mpr ⟨hxB, hxC⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, orderOf_eq_prime (hBe.2 x hxB) hx1]
  exact card_le_of_isCyclic hp.pos hcE hE.2

end SStar

section Beta

variable {G : Type} [Group G] (L : Subgroup G) {R : Type} [Group R]
  (θ : L ⧸ Subgroup.center L ≃* R)

@[expose] noncomputable def ggBeta {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    B →* MulAut R :=
  (ggLAut L θ).comp (Subgroup.inclusion hBN)

theorem ggBeta_eq {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G)) (b : B) :
    ggBeta L θ hBN b = ggLAut L θ ⟨b, hBN b.2⟩ :=
  rfl

theorem ggBeta_mem {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    {I : Set (MulAut R)}
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) (b : B) :
    ggBeta L θ hBN b ∈ I :=
  ggLAut_mem_of_induces L θ hBN h3 b.2

theorem ggLAut_eq_one_of_mem_centralizer {g : Subgroup.normalizer (L : Set G)}
    (hg : (g : G) ∈ Subgroup.centralizer (L : Set G)) : ggLAut L θ g = 1 := by
  ext r
  obtain ⟨q, rfl⟩ := θ.surjective r
  induction q using QuotientGroup.induction_on with
  | H l =>
    rw [ggLAut_apply, MulAut.one_apply]
    congr 2
    apply Subtype.ext
    rw [normalizerMonoidHom_coe]
    have h := Subgroup.mem_centralizer_iff.mp hg l l.2
    calc (g : G) * l * (g : G)⁻¹ = l * g * (g : G)⁻¹ := by rw [h]
      _ = l := by group

variable [Finite G]

theorem ggBeta_eq_one_iff {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    (hS : LargeEvenSStar p B x L) (hL : commutator L = ⊤)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (b : B) :
    ggBeta L θ hBN b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := by
  rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
  constructor
  · intro h
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one L θ hL h⟩
  · rintro ⟨-, hc⟩
    exact ggLAut_eq_one_of_mem_centralizer L θ hc

theorem ker_ggBeta {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    (hS : LargeEvenSStar p B x L) (hL : commutator L = ⊤)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    (ggBeta L θ hBN).ker = (Subgroup.zpowers x).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ggBeta_eq_one_iff L θ hp hS hL hBN b

theorem card_range_ggBeta_mul {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    (hS : LargeEvenSStar p B x L) (hL : commutator L = ⊤)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggBeta L θ hBN).range * p = Nat.card B := by
  have := Fact.mk hp
  have h1 := card_range_mul_card_ker (ggBeta L θ hBN)
  rw [ker_ggBeta L θ hp hS hL hBN] at h1
  have hxB : x ∈ B := hS.2.1
  have h2 : Nat.card ((Subgroup.zpowers x).subgroupOf B) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 x hxB) hS.2.2.1]
  rwa [h2] at h1

end Beta

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_noncyclic_of_noncyclic_quot {p : ℕ} [Fact p.Prime] {L : Subgroup G} {R : Type}
    [Group R] (ψ : L →* R) (hψ : Function.Surjective ψ) {F : Subgroup R} (hF : IsPGroup p F)
    (hnc : ¬ IsCyclic F) : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  set H : Subgroup L := F.comap ψ
  let f : H →* F := (ψ.comp H.subtype).codRestrict F (fun h => h.2)
  have hf : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨⟨l, hr⟩, rfl⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p H))
  have htop : (⊤ : Subgroup F) = P.map f := by
    have h := (P.mapSurjective hf).is_maximal' (Q := ⊤)
      (hF.of_equiv Subgroup.topEquiv.symm) le_top
    rwa [Sylow.coe_mapSurjective] at h
  have hPnc : ¬ IsCyclic P := by
    intro hc
    apply hnc
    refine isCyclic_of_surjective (f.comp (P : Subgroup H).subtype) ?_
    intro y
    have hy : y ∈ (P : Subgroup H).map f := htop ▸ Subgroup.mem_top y
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨⟨z, hz⟩, rfl⟩
  refine ⟨((P : Subgroup H).map H.subtype).map L.subtype, Subgroup.map_subtype_le _,
    (P.isPGroup'.map _).map _, fun hc => hPnc ?_⟩
  have e := ((P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective).trans
    (((P : Subgroup H).map H.subtype).equivMapOfInjective L.subtype L.subtype_injective)
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end Lift

end CFSG.StandardType
