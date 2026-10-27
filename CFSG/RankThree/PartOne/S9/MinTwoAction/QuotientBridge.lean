module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.GroupTheory.SteinbergBYMinimalCoprimeAction

public section

namespace CFSG.RankThree.PartOne.Quotient36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY SemidirectProduct
open scoped IsMulCommutative commutatorElement

section Conj

variable {G : Type*} [Group G]

@[expose] noncomputable def conjHom {H N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) : H →* MulAut N :=
  N.normalizerMonoidHom.comp (Subgroup.inclusion h)

theorem conjHom_apply_coe {H N : Subgroup G} (h : H ≤ Subgroup.normalizer (N : Set G)) (x : H)
    (n : N) : ((conjHom h x n : N) : G) = x * n * (x : G)⁻¹ := rfl

theorem mem_ker_conjHom {H N : Subgroup G} (h : H ≤ Subgroup.normalizer (N : Set G)) (x : H) :
    x ∈ (conjHom h).ker ↔ (x : G) ∈ Subgroup.centralizer (N : Set G) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx n hn
    have h1 := congrArg (fun f : MulAut N => ((f ⟨n, hn⟩ : N) : G)) hx
    simp only [conjHom_apply_coe, MulAut.one_apply] at h1
    have h2 : (x : G) * n = n * (x : G) := by
      calc (x : G) * n = ((x : G) * n * (x : G)⁻¹) * x := by group
        _ = n * x := by rw [h1]
    exact h2.symm
  · intro hx
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    rw [conjHom_apply_coe, MulAut.one_apply]
    have h1 := hx (n : G) n.2
    calc (x : G) * n * (x : G)⁻¹ = (n * x) * (x : G)⁻¹ := by rw [← h1]
      _ = n := by group

theorem ker_conjHom_eq {H N : Subgroup G} (h : H ≤ Subgroup.normalizer (N : Set G)) :
    (conjHom h).ker = (Subgroup.centralizer (N : Set G)).subgroupOf H := by
  ext x
  rw [mem_ker_conjHom, Subgroup.mem_subgroupOf]

end Conj

section Semidirect

variable {S A X : Type*} [Group S] [Group A] [Group X]

@[expose] noncomputable def semidirectToAut (φ : A →* MulAut S) (fS : S →* MulAut X)
    (fA : A →* MulAut X) (h : ∀ (a : A) (s : S), fA a * fS s * (fA a)⁻¹ = fS (φ a s)) :
    S ⋊[φ] A →* MulAut X :=
  SemidirectProduct.lift fS fA fun a => by
    ext s x
    simp [h]

theorem semidirectToAut_inl (φ : A →* MulAut S) (fS : S →* MulAut X) (fA : A →* MulAut X)
    (h : ∀ (a : A) (s : S), fA a * fS s * (fA a)⁻¹ = fS (φ a s)) (s : S) :
    semidirectToAut φ fS fA h (inl s) = fS s := by
  simp [semidirectToAut]

theorem semidirectToAut_inr (φ : A →* MulAut S) (fS : S →* MulAut X) (fA : A →* MulAut X)
    (h : ∀ (a : A) (s : S), fA a * fS s * (fA a)⁻¹ = fS (φ a s)) (a : A) :
    semidirectToAut φ fS fA h (inr a) = fA a := by
  simp [semidirectToAut]

end Semidirect

structure Compat (R A X : Type*) [Group R] [Group A] [Group X] where
  ψ : A →* MulAut R
  fR : R →* MulAut X
  fA : A →* MulAut X
  compat : ∀ (a : A) (r : R), fA a * fR r * (fA a)⁻¹ = fR (ψ a r)

namespace Compat

variable {R A X : Type*} [Group R] [Group A] [Group X] (C : Compat R A X)

theorem ker_invariant (a : A) (r : R) (hr : r ∈ C.fR.ker) : C.ψ a r ∈ C.fR.ker := by
  rw [MonoidHom.mem_ker] at hr ⊢
  rw [← C.compat, hr]
  simp

abbrev Q : Type _ := R ⧸ C.fR.ker

@[expose] noncomputable def φ : A →* MulAut C.Q :=
  Semidihedral.Principal.CoprimeFixedPoint.quotientAction C.ψ C.fR.ker C.ker_invariant

theorem φ_mk (a : A) (r : R) : C.φ a (r : C.Q) = ((C.ψ a r : R) : C.Q) := rfl

@[expose] noncomputable def fS : C.Q →* MulAut X :=
  QuotientGroup.lift C.fR.ker C.fR fun _ hr => hr

theorem fS_mk (r : R) : C.fS (r : C.Q) = C.fR r := rfl

theorem fS_injective : Function.Injective C.fS := by
  rw [injective_iff_map_eq_one]
  intro s hs
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
  rw [fS_mk] at hs
  exact (QuotientGroup.eq_one_iff r).mpr hs

theorem compatS (a : A) (s : C.Q) : C.fA a * C.fS s * (C.fA a)⁻¹ = C.fS (C.φ a s) := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
  exact C.compat a r

@[expose] noncomputable def fE : C.Q ⋊[C.φ] A →* MulAut X :=
  semidirectToAut C.φ C.fS C.fA C.compatS

@[expose, instance_reducible] noncomputable def actE : MulDistribMulAction (C.Q ⋊[C.φ] A) X :=
  MulDistribMulAction.compHom X C.fE

theorem actE_inl (s : C.Q) (x : X) : letI := C.actE; (inl s : C.Q ⋊[C.φ] A) • x = C.fS s x := by
  change C.fE (inl s) x = _
  simp [fE, semidirectToAut_inl]

theorem actE_inr (a : A) (x : X) : letI := C.actE; (inr a : C.Q ⋊[C.φ] A) • x = C.fA a x := by
  change C.fE (inr a) x = _
  simp [fE, semidirectToAut_inr]

end Compat

section OfSubgroups

variable {G : Type*} [Group G]

@[expose] noncomputable def Compat.ofSubgroups {R A X : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) : Compat ↥R ↥A ↥X where
  ψ := conjHom hAR
  fR := conjHom hRX
  fA := conjHom hAX
  compat a r := by
    ext x
    rw [← map_inv]
    simp only [MulAut.mul_apply, conjHom_apply_coe, Subgroup.coe_inv, inv_inv]
    group

end OfSubgroups

section Lift

variable {G : Type*} [Group G] (X : Subgroup G)

theorem le_normalizer_of_conj_mem {H M : Subgroup G}
    (h : ∀ c ∈ H, ∀ x ∈ M, c * x * c⁻¹ ∈ M) : H ≤ Subgroup.normalizer (M : Set G) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h c hc x, fun hx => ?_⟩
  have h1 := h c⁻¹ (H.inv_mem hc) _ hx
  have h2 : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
  rwa [h2] at h1

@[expose] def liftSub (T : Subgroup (↥X ⧸ frattini ↥X)) : Subgroup G :=
  (T.comap (QuotientGroup.mk' (frattini ↥X))).map X.subtype

variable {X}

theorem mem_liftSub {T : Subgroup (↥X ⧸ frattini ↥X)} {g : G} :
    g ∈ liftSub X T ↔ ∃ h : g ∈ X, ((⟨g, h⟩ : ↥X) : ↥X ⧸ frattini ↥X) ∈ T := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem liftSub_le (T : Subgroup (↥X ⧸ frattini ↥X)) : liftSub X T ≤ X := by
  intro g hg
  exact (mem_liftSub.mp hg).1

theorem frattini_le_liftSub (T : Subgroup (↥X ⧸ frattini ↥X)) :
    inSubgroup frattini X ≤ liftSub X T := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_liftSub.mpr ⟨x.2, ?_⟩
  have h1 : ((x : ↥X) : ↥X ⧸ frattini ↥X) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  change ((x : ↥X) : ↥X ⧸ frattini ↥X) ∈ T
  rw [h1]
  exact T.one_mem

theorem liftSub_eq_frattini_iff (T : Subgroup (↥X ⧸ frattini ↥X)) :
    liftSub X T = inSubgroup frattini X ↔ T = ⊥ := by
  constructor
  · intro h
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    have hx : (x : G) ∈ liftSub X T := mem_liftSub.mpr ⟨x.2, hv⟩
    rw [h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    subst this
    exact (QuotientGroup.eq_one_iff y).mpr hy
  · intro h
    refine le_antisymm ?_ (h ▸ frattini_le_liftSub T)
    intro g hg
    obtain ⟨hgX, hgT⟩ := mem_liftSub.mp hg
    rw [h, Subgroup.mem_bot] at hgT
    exact ⟨⟨g, hgX⟩, (QuotientGroup.eq_one_iff _).mp hgT, rfl⟩

theorem liftSub_eq_top_iff (T : Subgroup (↥X ⧸ frattini ↥X)) :
    liftSub X T = X ↔ T = ⊤ := by
  constructor
  · intro h
    rw [Subgroup.eq_top_iff']
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    have hx : (x : G) ∈ liftSub X T := by rw [h]; exact x.2
    exact (mem_liftSub.mp hx).2
  · intro h
    refine le_antisymm (liftSub_le T) ?_
    intro g hg
    exact mem_liftSub.mpr ⟨hg, by rw [h]; exact Subgroup.mem_top _⟩

theorem le_normalizer_liftSub {H : Subgroup G} (hHX : H ≤ Subgroup.normalizer (X : Set G))
    (T : Subgroup (↥X ⧸ frattini ↥X))
    (hT : ∀ h : ↥H, ∀ x : ↥X, (x : ↥X ⧸ frattini ↥X) ∈ T →
      ((conjHom hHX h x : ↥X) : ↥X ⧸ frattini ↥X) ∈ T) :
    H ≤ Subgroup.normalizer (liftSub X T : Set G) := by
  refine le_normalizer_of_conj_mem fun c hc g hg => ?_
  obtain ⟨hgX, hgT⟩ := mem_liftSub.mp hg
  have hcg : c * g * c⁻¹ ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (hHX hc) g).mp hgX
    exact this
  refine mem_liftSub.mpr ⟨hcg, ?_⟩
  have h1 := hT ⟨c, hc⟩ ⟨g, hgX⟩ hgT
  exact h1

end Lift

section Misc

theorem isElementaryAbelian_two_quotient {R : Type*} [Group R] (N : Subgroup R) [N.Normal]
    (hcomm : commutator R ≤ N) (hsq : ∀ r : R, r ^ 2 ∈ N) :
    IsElementaryAbelian 2 (R ⧸ N) := by
  have hc : IsMulCommutative (R ⧸ N) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  refine { toIsMulCommutative := hc, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (hsq r)

theorem pRank_congr_mulEquiv {q : ℕ} (hq : 1 < q) {H H' : Type*} [Group H] [Group H']
    [Finite H] [Finite H'] (e : H ≃* H') : CFSG.pRank q H = CFSG.pRank q H' := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq e

theorem pRank_le_of_injective' {q : ℕ} (hq : 1 < q) {H H' : Type*} [Group H] [Group H']
    [Finite H] [Finite H'] (f : H →* H') (hf : Function.Injective f) :
    CFSG.pRank q H ≤ CFSG.pRank q H' := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_le_of_injective hq f hf

theorem pRank_map_subtype {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : 1 < q)
    {X : Subgroup G} (Y : Subgroup ↥X) :
    CFSG.pRank q ↥(Y.map X.subtype) = CFSG.pRank q ↥Y :=
  (pRank_congr_mulEquiv hq (Y.equivMapOfInjective X.subtype X.subtype_injective)).symm

theorem pRank_mono_subgroup {G : Type*} [Group G] [Finite G] {q : ℕ} (hq : 1 < q)
    {Y Z : Subgroup G} (h : Y ≤ Z) : CFSG.pRank q ↥Y ≤ CFSG.pRank q ↥Z :=
  pRank_le_of_injective' hq (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

end Misc

end CFSG.RankThree.PartOne.Quotient36
