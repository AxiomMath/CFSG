module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.ClassicalInvolution.Q3.TL4ConnBendOut
import CFSG.RankThree.PartOne.K133.KillL2
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Quasithin.Background.OperatorJordanHolder
import CFSG.Quasithin.EmptyFaithful.S153QPC1
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.CommLemmas
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.Adapters.LieModelSimple
import CFSG.Quasithin.Background.Harris.L2.Numerics
import CFSG.Quasithin.Background.Harris.L2.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped Matrix

@[expose] def uc22p22g_OpEq (p : ℕ) (H : Type) [Group H] : Prop :=
  ∀ (Q : Type) [Group Q] (f : H →* Q), IsPGroup p ↥f.range → f.range = ⊥

theorem uc22p22g_opEq_mbar {G : Type} [Group G] [Finite G] (M V : Subgroup G) {p : ℕ}
    (hp : p.Prime) (h : UC22.F10.OpRes p M = M) : uc22p22g_OpEq p (MBar M V) := by
  intro Q _ f hf
  let π : ↥M →* MBar M V := QuotientGroup.mk' (kerAct M V).normalCore
  let g : ↥M →* Q := f.comp π
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hrange : g.range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hπ, ← MonoidHom.range_eq_map]
  have hf' : IsPGroup p ↥g.range := by rw [hrange]; exact hf
  have hN : IsPGroup p (↥M ⧸ g.ker) :=
    hf'.of_equiv (QuotientGroup.quotientKerEquivRange g).symm
  have hker : g.ker = ⊤ := UC6.eq_top_of_isPGroup_quotient_of_opRes_eq_uc6 hp h g.ker hN
  rw [MonoidHom.range_eq_bot_iff]
  ext y
  have : y ∈ g.ker := by rw [hker]; trivial
  exact MonoidHom.mem_ker.1 this

theorem uc22p22g_finite_outer (X : Type) [Group X] [Finite X] : Finite (Outer X) := by
  have : Finite (MulAut X) :=
    Finite.of_injective (fun α : MulAut X => (α : X → X)) DFunLike.coe_injective
  infer_instance

theorem uc22p22g_inner_of_pElement {H : Type} [Group H] [Finite H] (L : Subgroup H) [L.Normal]
    {p : ℕ} (hp : p.Prime)
    (hcomm : ∀ a b : Outer ↥L, a * b = b * a) (hOp : uc22p22g_OpEq p H)
    {h : H} {b : ℕ} (hh : h ^ (p ^ b) = 1) :
    ∃ l ∈ L, l⁻¹ * h ∈ Subgroup.centralizer (L : Set H) := by
  classical
  haveI : Finite ↥L := Finite.of_injective _ Subtype.val_injective
  haveI : Finite (Outer ↥L) := uc22p22g_finite_outer ↥L
  let ψ : H →* Outer ↥L :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp
      (MulAut.conjNormal (H := L))
  let Q : Subgroup (Outer ↥L) := ψ.range
  haveI : Finite Q := Finite.of_injective _ Subtype.val_injective
  obtain ⟨a, m, hm, hcard⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := Q)).ne' p hp.ne_one
  let r : H →* Q := ψ.rangeRestrict
  have hrcomm : ∀ x y : H, Commute (r x) (r y) := fun x y =>
    Subtype.ext (hcomm (ψ x) (ψ y))
  let f : H →* Q :=
    { toFun := fun x => (r x) ^ m
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, (hrcomm x y).mul_pow] }
  have hf : IsPGroup p ↥f.range := by
    intro z
    obtain ⟨x, hx⟩ := z.2
    refine ⟨a, ?_⟩
    have hz : (z : Q) = (r x) ^ m := hx.symm
    have h0 : (z : Q) ^ (p ^ a) = 1 := by
      rw [hz, ← pow_mul, show m * p ^ a = Nat.card Q by rw [hcard, mul_comm]]
      exact pow_card_eq_one'
    exact Subtype.ext (by simpa using h0)
  have hf1 := hOp Q f hf
  have h1 : (r h) ^ m = 1 := by
    have : f h ∈ f.range := ⟨h, rfl⟩
    rw [hf1] at this
    exact Subgroup.mem_bot.1 this
  have h2 : (r h) ^ (p ^ b) = 1 := by rw [← map_pow, hh, map_one]
  have hcop : Nat.Coprime (p ^ b) m :=
    Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have h3 : r h = 1 := by
    have h4 : orderOf (r h) ∣ Nat.gcd (p ^ b) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
    rw [hcop.gcd_eq_one] at h4
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  have h5 : ψ h = 1 := congrArg Subtype.val h3
  have h6 : MulAut.conjNormal (H := L) h ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
    (QuotientGroup.eq_one_iff _).1 h5
  obtain ⟨l, hl⟩ := h6
  refine ⟨l, l.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hlx := congrArg (fun α : MulAut ↥L => ((α ⟨x, hx⟩ : ↥L) : H)) hl
  simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at hlx
  have hlx' : (l : H) * x * (l : H)⁻¹ = h * x * h⁻¹ := hlx
  calc x * ((l : H)⁻¹ * h) = (l : H)⁻¹ * ((l : H) * x * (l : H)⁻¹) * h := by group
    _ = (l : H)⁻¹ * (h * x * h⁻¹) * h := by rw [hlx']
    _ = (l : H)⁻¹ * h * x := by group

theorem uc22p22g_card_le {H : Type} [Group H] [Finite H] (L : Subgroup H) [L.Normal] {p : ℕ}
    (hLC : L ⊓ Subgroup.centralizer (L : Set H) = ⊥)
    (hrank : ∀ E : Subgroup ↥L, CFSG.IsElementaryAbelian p ↥E → Nat.card E ≤ p)
    (hC : ∀ c ∈ Subgroup.centralizer (L : Set H), (∃ k : ℕ, c ^ (p ^ k) = 1) → c = 1)
    (hinn : ∀ h : H, (∃ k : ℕ, h ^ (p ^ k) = 1) →
      ∃ l ∈ L, l⁻¹ * h ∈ Subgroup.centralizer (L : Set H))
    (E : Subgroup H) [hE : CFSG.IsElementaryAbelian p ↥E] : Nat.card E ≤ p := by
  classical
  set C : Subgroup H := Subgroup.centralizer (L : Set H) with hCdef
  have hEp : ∀ x : E, (x : H) ^ p = 1 := fun x => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (x : H) x.2
    exact this
  have spec : ∀ x : E, ∃ l : ↥L, ((l : H))⁻¹ * (x : H) ∈ C := fun x => by
    obtain ⟨l, hl, hlC⟩ := hinn x ⟨1, by rw [pow_one]; exact hEp x⟩
    exact ⟨⟨l, hl⟩, hlC⟩
  have uniq : ∀ (l₁ l₂ : ↥L) (w : H), ((l₁ : H))⁻¹ * w ∈ C → ((l₂ : H))⁻¹ * w ∈ C → l₁ = l₂ := by
    intro l₁ l₂ w h1 h2
    have h3 : ((l₂ : H))⁻¹ * (l₁ : H) ∈ L ⊓ C := by
      refine ⟨L.mul_mem (L.inv_mem l₂.2) l₁.2, ?_⟩
      have := C.mul_mem h2 (C.inv_mem h1)
      have e : ((l₂ : H))⁻¹ * w * (((l₁ : H))⁻¹ * w)⁻¹ = ((l₂ : H))⁻¹ * (l₁ : H) := by group
      rwa [e] at this
    rw [hLC, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 h3).symm
  let π : ↥E → ↥L := fun x => Classical.choose (spec x)
  have hπ : ∀ x : E, ((π x : ↥L) : H)⁻¹ * (x : H) ∈ C := fun x => Classical.choose_spec (spec x)
  have hπmul : ∀ x y : E, π (x * y) = π x * π y := by
    intro x y
    apply uniq _ _ ((x * y : E) : H) (hπ (x * y))
    have hx := hπ x
    have hy := hπ y
    have hcomm : ∀ c ∈ C, ∀ l ∈ L, c * l = l * c := fun c hc l hl =>
      (Subgroup.mem_centralizer_iff.1 hc l hl).symm
    have key : (((π x * π y : ↥L) : H))⁻¹ * ((x * y : E) : H) =
        (((π x : ↥L) : H)⁻¹ * (x : H)) * (((π y : ↥L) : H)⁻¹ * (y : H)) := by
      have e1 := hcomm _ hx ((π y : ↥L) : H)⁻¹ (L.inv_mem (π y).2)
      show ((π x : H) * (π y : H))⁻¹ * ((x : H) * (y : H)) = _
      calc ((π x : H) * (π y : H))⁻¹ * ((x : H) * (y : H))
          = (π y : H)⁻¹ * (((π x : H)⁻¹ * (x : H)) * (y : H)) := by group
        _ = ((π x : H)⁻¹ * (x : H)) * ((π y : H)⁻¹ * (y : H)) := by
            rw [← mul_assoc, ← e1]; group
    rw [key]
    exact C.mul_mem hx hy
  let φ : ↥E →* ↥L := MonoidHom.mk' π hπmul
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π x = 1 := hx
    have h2 : (x : H) ∈ C := by
      have := hπ x
      rwa [h1, Subgroup.coe_one, inv_one, one_mul] at this
    exact Subtype.ext (hC _ h2 ⟨1, by rw [pow_one]; exact hEp x⟩)
  let e : ↥E ≃* ↥φ.range := MonoidHom.ofInjective hinj
  haveI : CFSG.IsElementaryAbelian p ↥φ.range := CFSG.IsElementaryAbelian.of_mulEquiv e hE
  have := hrank φ.range inferInstance
  rwa [← Nat.card_congr e.toEquiv] at this

theorem uc22p22g_isL2_psl {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧ CharP F 2 ∧
      Nonempty (X ≃* CFSG.GorensteinWalter.PSL2 F) := by
  have h1 := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨⟨-, hn1, -, h22, -⟩, F, hF1, hF2, hFcard, ⟨e⟩⟩ := h1
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact h22 (by simp)
  haveI : CharP F 2 := uc22p22d_charP_two (by omega) hFcard
  exact ⟨hn2, F, hF1, hF2, hFcard, inferInstance,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩

theorem uc22p22g_outer_comm {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    ∀ a b : Outer X, a * b = b * a := by
  obtain ⟨-, F, hF1, hF2, hFcard, -, ⟨e⟩⟩ := uc22p22g_isL2_psl h
  haveI : IsCyclic (Outer (CFSG.GorensteinWalter.PSL2 F)) :=
    CFSG.ClassicalInvolution.Q3.TL4.Bend.isCyclic_outer_psl2_even hFcard
  haveI : IsCyclic (Outer X) :=
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).isCyclic.2 inferInstance
  intro a b
  exact IsMulCommutative.is_comm.comm a b

theorem uc22p22g_center_bot {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    Subgroup.center X = ⊥ := by
  obtain ⟨-, F, hF1, hF2, hFcard, hchar, ⟨e⟩⟩ := uc22p22g_isL2_psl h
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have h1 : e' x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e' (Subgroup.mem_center_iff.1 hx y)
  rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.mem_bot] at h1
  exact e'.injective (h1.trans (map_one e').symm)

theorem uc22p22g_rank {X : Type} [Group X] {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : IsL2 X n)
    (E : Subgroup X) [CFSG.IsElementaryAbelian p ↥E] : Nat.card E ≤ p := by
  obtain ⟨-, F, hF1, hF2, hFcard, hchar, ⟨e⟩⟩ := uc22p22g_isL2_psl h
  haveI : NeZero (p : F) := ⟨CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2⟩
  have hA : CFSG.IsElementaryAbelian p ↥(E.map e.toMonoidHom) :=
    CFSG.IsElementaryAbelian.of_mulEquiv (E.equivMapOfInjective e.toMonoidHom e.injective)
      inferInstance
  have := CFSG.RankThree.PartOne.K133.psl2_elemAb_card_le hp hp2 (E.map e.toMonoidHom) hA
  rwa [Subgroup.card_map_of_injective e.injective] at this

theorem uc22p22g_pRank_le_one {H : Type} [Group H] [Finite H] (L : Subgroup H) [L.Normal]
    {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hL : IsL2 ↥L n) (hOp : uc22p22g_OpEq p H)
    (hC : ∀ c ∈ Subgroup.centralizer (L : Set H), ∀ k : ℕ, c ^ (p ^ k) = 1 → c = 1) :
    CFSG.pRank p H ≤ 1 := by
  have hLC : L ⊓ Subgroup.centralizer (L : Set H) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxL, hxC⟩
    have hz : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC (g : H) g.2)
    rw [uc22p22g_center_bot hL, Subgroup.mem_bot] at hz
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)
  have hcard : ∀ E : Subgroup H, CFSG.IsElementaryAbelian p ↥E → Nat.card E ≤ p := by
    intro E hE
    haveI := hE
    exact uc22p22g_card_le L hLC (fun E' hE' => by haveI := hE'; exact uc22p22g_rank hp hp2 hL E')
      (fun c hc ⟨k, hk⟩ => hC c hc k hk)
      (fun h ⟨k, hk⟩ => uc22p22g_inner_of_pElement L hp (uc22p22g_outer_comm hL) hOp hk) E
  refine csSup_le' ?_
  rintro r ⟨A, hA, hAr⟩
  have h1 := hcard A hA
  rw [hAr] at h1
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (by simpa using h1)

theorem uc22p22g_isSz_isL2_false {X : Type} [Group X] {n : ℕ} (hS : IsSz X n) (hL : IsL2 X n) :
    False :=
  CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hS
    (CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two
      (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)))

theorem uc22p22g_not_dvd_pred {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : ¬ p ∣ 2 ^ n - 1 := by
  intro hd
  have h1 : (p : ℤ) ∣ -1 - 2 ^ n := (Int.modEq_iff_dvd.1 h)
  have h2 : (p : ℤ) ∣ ((2 ^ n - 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 hd
  have h3 : ((2 ^ n - 1 : ℕ) : ℤ) = 2 ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [h3] at h2
  have h4 : (p : ℤ) ∣ 2 := by
    have := dvd_add h1 h2
    have e : (-1 - 2 ^ n : ℤ) + (2 ^ n - 1) = -2 := by ring
    rw [e] at this
    exact (dvd_neg).1 this
  have h5 : p ∣ 2 := by exact_mod_cast h4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h5)

section Modules

variable {H : Type} [Group H] [Finite H] {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem uc22p22g_map_conj_eq_of_normal (L : Subgroup H) [L.Normal] (h : H) :
    L.map (MulAut.conj h).toMonoidHom = L := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ‹L.Normal›.conj_mem y hy h
  · intro hx
    exact ⟨h⁻¹ * x * h, by simpa using ‹L.Normal›.conj_mem x hx h⁻¹, by group⟩

theorem uc22p22g_commOn_top (ρ : Representation (ZMod 2) H W) (hirr : ρ.IsIrreducible)
    (hfaith : Function.Injective ρ) {L : Subgroup H} [L.Normal] (hL : L ≠ ⊥) :
    commOn ρ L ⊤ = ⊤ := by
  have hS : ∀ h : H, ∀ x ∈ commOn ρ L ⊤, ρ h x ∈ commOn ρ L ⊤ := by
    intro h x hx
    have := uc22p22d_apply_commOn_le ρ L h hx
    rwa [uc22p22g_map_conj_eq_of_normal] at this
  rcases uc22p22d_inv_dichotomy hirr _ hS with h | h
  · exfalso
    apply hL
    rw [eq_bot_iff]
    intro a ha
    have h1 : ρ a = 1 := by
      refine LinearMap.ext fun u => ?_
      have hmem : ρ a u - u ∈ commOn ρ L ⊤ := sub_mem_commOn ha Submodule.mem_top
      rw [h, Submodule.mem_bot, sub_eq_zero] at hmem
      simpa using hmem
    have h2 : a = 1 := hfaith (h1.trans (map_one ρ).symm)
    rw [h2]
    exact Subgroup.one_mem _
  · exact h

theorem uc22p22g_cent_nat (ρ : Representation (ZMod 2) H W) (hfaith : Function.Injective ρ)
    {L : Subgroup H} {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ 2 ^ n - 1)
    (hnat : NatL2 ρ L ⊤ ⊥ n) {c : H} (hc : c ∈ Subgroup.centralizer (L : Set H)) {k : ℕ}
    (hck : c ^ (p ^ k) = 1) : c = 1 := by
  classical
  obtain ⟨F, hF1, hF2, hFcard, -, -, -, φ, ψ, -, hker, hsurj, hψ⟩ := hnat
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h0 : ψ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have := hker (x - y) trivial h0
    rw [Submodule.mem_bot, sub_eq_zero] at this
    exact this
  let ψe : W ≃+ (Fin 2 → F) :=
    AddEquiv.ofBijective ψ ⟨hψinj, fun y => by
      obtain ⟨x, -, hx⟩ := hsurj y
      exact ⟨x, hx⟩⟩
  let T : (Fin 2 → F) →+ (Fin 2 → F) :=
    ψ.comp (((ρ c).toAddMonoidHom).comp ψe.symm.toAddMonoidHom)
  have hTapp : ∀ y, T y = ψ (ρ c (ψe.symm y)) := fun y => rfl
  have hcomm : ∀ h : ↥L, ∀ x : W, ρ c (ρ (h : H) x) = ρ (h : H) (ρ c x) := by
    intro h x
    have h1 := Subgroup.mem_centralizer_iff.1 hc (h : H) h.2
    have h2 : ρ ((h : H) * c) = ρ (c * (h : H)) := by rw [h1]
    have h3 := congrArg (fun f : W →ₗ[ZMod 2] W => f x) h2
    simp only [map_mul, Module.End.mul_apply] at h3
    exact h3.symm
  have hTcomm : ∀ g : ↥(StatedSL 2 F), ∀ y,
      T (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y) =
        ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T y := by
    intro g y
    obtain ⟨h, rfl⟩ := φ.surjective g
    set x : W := ψe.symm y with hx
    have hψx : ψ x = y := by
      show ψe x = y
      rw [hx]; exact ψe.apply_symm_apply y
    have h1 : ψ (ρ (h : H) x) =
        ((((φ h : ↥(StatedSL 2 F)) : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ y := by
      rw [hψ h x trivial, hψx]
    have h2 : ψe.symm (((((φ h : ↥(StatedSL 2 F)) : GL (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) *ᵥ y) = ρ (h : H) x := by
      apply ψe.injective
      rw [ψe.apply_symm_apply]
      exact h1.symm
    rw [hTapp, h2, hcomm h x, hψ h _ trivial, hTapp, ← hx]
  obtain ⟨μ, hμ⟩ := CFSG.Quasithin.exists_smul_of_comm_sl (n := 2) le_rfl T hTcomm
  have hψc : ∀ x : W, ψ (ρ c x) = μ • ψ x := by
    intro x
    have := hμ (ψ x)
    rw [hTapp] at this
    have hx : ψe.symm (ψ x) = x := ψe.symm_apply_apply x
    rw [hx] at this
    exact this
  have hψpow : ∀ (j : ℕ) (x : W), ψ ((ρ c ^ j) x) = μ ^ j • ψ x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, hψc, smul_smul, ← pow_succ]
  have hρ1 : (ρ c) ^ (p ^ k) = 1 := by rw [← map_pow, hck, map_one]
  have hμ1 : μ ^ (p ^ k) = 1 := by
    obtain ⟨x, -, hx⟩ := hsurj ![1, 0]
    have h1 := hψpow (p ^ k) x
    rw [hρ1, Module.End.one_apply, hx] at h1
    have h2 := congrFun h1 0
    simp at h2
    exact h2.symm
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero k hp.ne_zero)] at hμ1
    exact zero_ne_one hμ1
  letI : Fintype F := Fintype.ofFinite F
  have hμ2 : μ ^ (2 ^ n - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rwa [← Nat.card_eq_fintype_card, hFcard] at this
  have hcop : Nat.Coprime (p ^ k) (2 ^ n - 1) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
  have hμ3 : μ = 1 := by
    have := (pow_gcd_eq_one (a := μ)).2 ⟨hμ1, hμ2⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hρc : ρ c = 1 := by
    refine LinearMap.ext fun x => ?_
    apply hψinj
    rw [hψc, hμ3, one_smul]
    rfl
  exact hfaith (hρc.trans (map_one ρ).symm)

theorem uc22p22g_numConj_le_one (L : Subgroup H) [L.Normal] : F05.numConj L ≤ 1 := by
  unfold F05.numConj
  have : {K : Subgroup H | ∃ g : H, K = L.map (MulAut.conj g).toMonoidHom} ⊆ {L} := by
    rintro K ⟨g, rfl⟩
    rw [uc22p22g_map_conj_eq_of_normal]
    rfl
  exact (Set.ncard_le_ncard this (Set.toFinite _)).trans (by simp)

@[expose] def uc22p22g_CentOmega4m : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) H W), Function.Injective ρ → ∀ (L : Subgroup H) (k p : ℕ),
    p.Prime → p ≠ 2 → (2 : ℤ) ^ (2 * k) ≡ -1 [ZMOD (p : ℤ)] →
    (SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 ⊤ ⊥ ∨
      SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 ⊤ ⊥) →
    ∀ c ∈ Subgroup.centralizer (L : Set H), ∀ j : ℕ, c ^ (p ^ j) = 1 → c = 1

theorem uc22p22g_centRank8_holds :
    ∀ (H : Type) [Group H] [Finite H] (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (ρ : Representation (ZMod 2) H W), Function.Injective ρ → ∀ L : Subgroup H, IsL2 ↥L 3 →
      SecIrr ρ L ⊤ ⊥ 8 → ∀ c ∈ Subgroup.centralizer (L : Set H), ∀ j : ℕ, c ^ (3 ^ j) = 1 → c = 1 := by
  intro H _ _ W _ _ _ ρ hfaith L hL hirr8 c hc j hcj
  classical
  obtain ⟨-, F, hF1, hF2, hFcard, hchar, ⟨e⟩⟩ := uc22p22g_isL2_psl hL
  letI : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 ^ 3 := by rw [← Nat.card_eq_fintype_card, hFcard]
  let eSL : ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  let ρ' : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) W :=
    ρ.comp (L.subtype.comp eSL.symm.toMonoidHom)
  have hρ' : ∀ g, ρ' g = ρ ((eSL.symm g : ↥L) : H) := fun g => rfl
  obtain ⟨hinvA, hinvB, hle, hcard, hsimple⟩ := hirr8
  have hWcard : Nat.card W = 2 ^ 8 := by
    have h1 : Nat.card ↥(⊤ : Submodule (ZMod 2) W) = Nat.card W :=
      Nat.card_congr Submodule.topEquiv.toEquiv
    have h2 : Nat.card ↥(⊥ : Submodule (ZMod 2) W) = 1 := Nat.card_unique
    rw [h1, h2, mul_one] at hcard
    exact hcard
  haveI : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hWcard]; norm_num)
  haveI : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  obtain ⟨l₀, hl₀⟩ := exists_ne (1 : ↥L)
  have hnt' : ∃ g, ρ' g ≠ 1 := by
    refine ⟨eSL l₀, fun h => hl₀ ?_⟩
    have h1 : ρ ((l₀ : ↥L) : H) = ρ 1 := by
      have := h
      rw [hρ', eSL.symm_apply_apply] at this
      rw [this, map_one]
    exact Subtype.ext (hfaith h1)
  have hirr' : ρ'.IsIrreducible := by
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    refine ⟨inferInstance, fun U hU => ?_⟩
    refine hsimple U bot_le le_top ?_
    intro a ha u hu
    have := hU (eSL ⟨a, ha⟩) u hu
    rwa [hρ', eSL.symm_apply_apply] at this
  haveI : Fact ρ'.IsIrreducible := ⟨hirr'⟩
  obtain ⟨d, hd1, hDcard, hb⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := 3) (by norm_num) hF ρ' hnt'
  haveI : Finite (EndRing ρ') := finite_endRing ρ'
  haveI : Module.Finite (EndRing ρ') W := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, J, hJne, hJn, -, hshift, hdim⟩ :=
    hb (Module.finBasis (EndRing ρ') W)
  have hfinrank : Module.finrank (ZMod 2) W = 8 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [Nat.card_zmod, hWcard] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have h1 : Module.finrank (ZMod 2) W = d * 2 ^ J.card := by
    rw [CFSG.Quasithin.G11.Harris.L2.finrank_eq_mul_of_card hDcard, hdim]
  have hnum := CFSG.Quasithin.G11.Harris.L2.l2_numerics (n := 3) (by norm_num) hd1 hJne hJn hshift
    (by omega)
  have hd : d = 1 := by
    rcases hnum with ⟨hJ1, hd3⟩ | ⟨hJ2, hn⟩ | ⟨-, -, hd⟩
    · exfalso
      rw [hJ1, hd3] at h1
      norm_num at h1
      omega
    · omega
    · exact hd
  have hcard2 : Nat.card (EndRing ρ') = 2 := by rw [hDcard, hd]; rfl
  letI : Fintype (EndRing ρ') := Fintype.ofFinite _
  have hkey : ∀ x : EndRing ρ', x = 0 ∨ x = 1 := by
    intro x
    by_contra hx
    push Not at hx
    have h3 : ({0, 1, x} : Finset (EndRing ρ')).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hx.2.symm
      · simp [zero_ne_one, hx.1.symm]
    have := Finset.card_le_univ ({0, 1, x} : Finset (EndRing ρ'))
    rw [h3, ← Nat.card_eq_fintype_card, hcard2] at this
    omega
  have hcomm : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : W),
      ρ c (ρ' g v) = ρ' g (ρ c v) := by
    intro g v
    have h1 := Subgroup.mem_centralizer_iff.1 hc ((eSL.symm g : ↥L) : H) (eSL.symm g).2
    have h2 : ρ (((eSL.symm g : ↥L) : H) * c) = ρ (c * ((eSL.symm g : ↥L) : H)) := by rw [h1]
    have h3 := congrArg (fun f : W →ₗ[ZMod 2] W => f v) h2
    simp only [map_mul, Module.End.mul_apply] at h3
    rw [hρ']
    exact h3.symm
  obtain ⟨ψ, hψ⟩ := (mem_endRing_iff ρ' (ρ c)).2 hcomm
  have hψ0 : ψ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply hv
    have h1 : ρ c v = 0 := by
      have := congrFun hψ v
      rw [h0] at this
      simpa using this.symm
    have h2 : ρ (c⁻¹) (ρ c v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [h1, map_zero] at h2
    exact h2.symm
  have hψ1 : ψ = 1 := (hkey ψ).resolve_left hψ0
  have hρc : ρ c = 1 := by
    refine LinearMap.ext fun v => ?_
    have := congrFun hψ v
    rw [hψ1] at this
    simpa using this.symm
  exact hfaith (hρc.trans (map_one ρ).symm)

theorem uc22p22g_cent_trivial (ρ : Representation (ZMod 2) H W) (hfaith : Function.Injective ρ)
    (hirr : ρ.IsIrreducible) {L : Subgroup H} [L.Normal] {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : IsL2 ↥L n) (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) (hcent : uc22p22g_CentOmega4m)
    (hmods : NatL2 ρ L (commOn ρ L ⊤) ⊥ n ∨
      (∃ k : ℕ, n = 2 * k ∧
        (SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 1 (commOn ρ L ⊤) ⊥ ∨
          SecSum (fun A B => NatOmegaMinus4 ρ L A B k) 2 (commOn ρ L ⊤) ⊥)) ∨
      (n = 3 ∧ IsL2 ↥L 3 ∧ SecIrr ρ L (commOn ρ L ⊤) ⊥ 8)) :
    ∀ c ∈ Subgroup.centralizer (L : Set H), ∀ j : ℕ, c ^ (p ^ j) = 1 → c = 1 := by
  haveI : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  have hLne : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance
  have htop := uc22p22g_commOn_top ρ hirr hfaith hLne
  rw [htop] at hmods
  intro c hc j hcj
  rcases hmods with hnat | ⟨k, rfl, hs⟩ | ⟨rfl, hL3, hirr8⟩
  · exact uc22p22g_cent_nat ρ hfaith hp (uc22p22g_not_dvd_pred hp hp2 hpn) hnat hc hcj
  · exact hcent H W ρ hfaith L k p hp hp2 hpn hs c hc j hcj
  · have h9 : (p : ℤ) ∣ 9 := by
      have h1 : (p : ℤ) ∣ -1 - 2 ^ 3 := Int.modEq_iff_dvd.1 hpn
      have h2 : (-1 - 2 ^ 3 : ℤ) = -9 := by norm_num
      rw [h2] at h1
      exact (dvd_neg).1 h1
    have h9' : p ∣ 3 ^ 2 := by exact_mod_cast h9
    have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h9')
    subst hp3
    exact uc22p22g_centRank8_holds H W ρ hfaith L hL3 hirr8 c hc j hcj

theorem uc22p22g_prod_not_simple {A B : Type} [Group A] [Group B] [Nontrivial A] [Nontrivial B] :
    ¬ IsSimpleGroup (A × B) := by
  intro hs
  rcases (MonoidHom.normal_ker (MonoidHom.snd A B)).eq_bot_or_eq_top with h | h
  · obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have : ((a, 1) : A × B) ∈ (MonoidHom.snd A B).ker := MonoidHom.mem_ker.2 rfl
    rw [h, Subgroup.mem_bot] at this
    exact ha (congrArg Prod.fst this)
  · obtain ⟨b, hb⟩ := exists_ne (1 : B)
    have : ((1, b) : A × B) ∈ (MonoidHom.snd A B).ker := by rw [h]; trivial
    exact hb (MonoidHom.mem_ker.1 this)

theorem uc22p22g_not_natOmegaPlus4 (ρ : Representation (ZMod 2) H W) {L : Subgroup H} {n : ℕ}
    (hL : IsL2 ↥L n) (hLg : lgConj L = L) : ¬ NatOmegaPlus4 ρ (lgConj L) ⊤ ⊥ n := by
  rw [hLg]
  rintro ⟨F, hF1, hF2, hFcard, -, -, -, φ, -⟩
  obtain ⟨hn2, -⟩ := uc22p22g_isL2_psl hL
  haveI : CharP F 2 := uc22p22d_charP_two (by omega) hFcard
  have h4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨ψ⟩ := uc22p22d_omegaPlus4_equiv h4
  haveI : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  haveI hsimp := CFSG.Quasithin.QP.sl2_isSimpleGroup h4
  haveI : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := hsimp.toNontrivial
  exact uc22p22g_prod_not_simple
    ((φ.trans ψ.symm).isSimpleGroup_congr.1 inferInstance)

end Modules

section Main

variable {G : Type} [Group G] [Finite G]

theorem s22_16_of_s15 (D : Data G) (Ch : Choice2011 G) (hK147 : K147) (h22V : S22_V D Ch)
    (h9 : S22_9 D Ch) (h14 : S22_14 D Ch) (h15 : S22_15 D Ch)
    (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) (h638 : UC6.R6_38 D)
    (hcent : uc22p22g_CentOmega4m) : S22_16 D Ch := by
  intro h1930 c p hp K n hK hnorm
  have hL2 : IsL2 ↥(mbarImage D.M c.V K) n := h15 h1930 c p hp K n hK
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have hKC : K ∈ calC D.M := hK.1
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  have hred : TwoReduced D.M c.V := (h22V h1930 c).1.2.2
  have hel : CFSG.Open.IsElemAbelian 2 c.V := (h22V h1930 c).1.1.1.2.2.2
  have hn : c.n ≤ n := h14 h1930 c p hp K n hK
  have h9' : ¬ MBarGT D.M ⊥ c.V (c.n + 1) := h9 h1930 c
  have hgt : ¬ MBarGT D.M ⊥ c.V (n + 1) := fun h =>
    h9' (uc22br4_mBarGT_mono D.M ⊥ c.V h (by omega))
  have hn3' : 3 ≤ n := le_trans (hn3 c) hn
  haveI : IsSimpleGroup ↥(mbarImage D.M c.V K) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have hKV : ¬ K ≤ centralizer (c.V : Set G) := fun hle =>
    (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
      ((uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM).2 hle)
  have hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] := by
    rcases hK.2.1 with ⟨-, -, -, hJL⟩ | h | ⟨hSz, -⟩
    · exact (hJL hL2).elim
    · exact h
    · exact (uc22p22g_isSz_isL2_false hSz hL2).elim
  haveI hMnorm : (mbarImage D.M c.V K).Normal :=
    uc22br4_mbarImage_normal D.M c.V K hKM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hnorm)
  have hlg : lgConj (mbarImage D.M c.V K) = mbarImage D.M c.V K :=
    uc22br4_lgConj_eq_of_normal _
  have hnum : F05.numConj (mbarImage D.M c.V K) ≤ 2 :=
    (uc22p22g_numConj_le_one _).trans (by norm_num)
  have hcase : Case147 (mbarImage D.M c.V K) n :=
    Or.inr (Or.inr ⟨Or.inl ⟨by omega, Or.inl hL2⟩, hnum⟩)
  obtain ⟨Vmod, i1, i2, i3, e, ρ, hc, hconcl⟩ :=
    uc22br4_k147_exists hK147 D c.hVM hel c.hVne c.hVirr hred hKC hKV hcase hgt
  have hirr : ρ.IsIrreducible :=
    (uc22br4_isIrreducible_iff D.M c.V c.hVM e ρ hc).2 ⟨c.hVne, c.hVirr⟩
  have hfaith : Function.Injective ρ := uc22br4_injective D.M c.V c.hVM e ρ hc
  rcases hconcl with ⟨-, hmods⟩ | hOm
  · have hC := uc22p22g_cent_trivial ρ hfaith hirr hpP hp2 hL2 hpn hcent hmods
    have hOp := uc22p22g_opEq_mbar D.M c.V hpP (h638 p hpP hp2 (Or.inl hp))
    have hle := uc22p22g_pRank_le_one (mbarImage D.M c.V K) hpP hp2 hL2 hOp hC
    have hlt := ((h22V h1930 c).2 p hp).1
    omega
  · exact (uc22p22g_not_natOmegaPlus4 ρ hL2 hlg hOm).elim

theorem s22_16_given (D : Data G) (Ch : Choice2011 G) (hK147 : K147) (h22V : S22_V D Ch)
    (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) (h638 : UC6.R6_38 D) (hcent : uc22p22g_CentOmega4m) :
    S22_9 D Ch → S22_14 D Ch → S22_15 D Ch → S22_16 D Ch :=
  fun h9 h14 h15 => s22_16_of_s15 D Ch hK147 h22V h9 h14 h15 hn3 h638 hcent

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
