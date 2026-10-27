module

public import CFSG.Quasithin.H13.NQRigidFitting2
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Quasithin.H13.NQRigidConjugate

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj exists_conj_eq_of_isSylowOf)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped IsMulCommutative commutatorElement

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem le_of_noPQuotient_two {Y K D : Subgroup H} (hY : NoPQuotient 2 Y) (hYD : Y ≤ D)
    (hKD : K ≤ D) (hDK : D ≤ normalizer (K : Set H)) (h2 : ∃ k : ℕ, K.relIndex D ∣ 2 ^ k) :
    Y ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : (K.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hKD).mpr hDK
  set φ : Y →* D ⧸ K.subgroupOf D := (QuotientGroup.mk' _).comp (inclusion hYD) with hφ
  obtain ⟨k, hk⟩ := h2
  have hq : IsPGroup 2 (Y ⧸ φ.ker) := by
    apply isPGroup_two_of_card_dvd (k := k)
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact (Subgroup.card_subgroup_dvd_card φ.range).trans hk
  have htop := hY _ hq
  intro y hy
  have h1 : (⟨y, hy⟩ : Y) ∈ φ.ker := htop ▸ mem_top _
  rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  exact h1

omit [Finite H] in
theorem noPQuotient_conjugate {p : ℕ} {X : Subgroup H} (hX : NoPQuotient p X) (g : H) :
    NoPQuotient p (X.map (MulAut.conj g).toMonoidHom) :=
  NoPQuotient.of_surjective
    (X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toMonoidHom
    (MulEquiv.surjective _) hX

theorem index_dvd_two_pow_of_sylow_le {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (P₀ : Sylow p X) {N : Subgroup X}
    (hPN : (P₀ : Subgroup X) ≤ N) : ∃ k : ℕ, N.index ∣ 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e₀ := MulEquiv.ofBijective _ (NQTerm.sylow_bijective_coreQuot hp2 hXp P₀)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  refine ⟨k, ?_⟩
  have hidx : (P₀ : Subgroup X).index = Nat.card (CFSG.pCore 2 X) := by
    have h1 := (P₀ : Subgroup X).card_mul_index
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 X)
    rw [Nat.card_congr e₀.toEquiv, h2] at h1
    have hpos : 0 < Nat.card (X ⧸ CFSG.pCore 2 X) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  rw [← hk, ← hidx]
  exact index_dvd_of_le hPN

theorem Sylow_containing_normalizer_lifts_quotient_Fitting_control
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r H ≤ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X A : Subgroup H} (hXA : X ≤ A) (hXn : (X.subgroupOf A).Normal)
    (hAS : ∃ S : Sylow 2 H, (S : Subgroup H) ≤ A) (hX2 : NoPQuotient 2 X)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrkX : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) (hirr : IsFrattiniIrreducible X A) :
    CFSG.pCore 2 H ≤ A ∧
      (CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H)).comap (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤
        normalizer (X : Set H) ∧
      (X.Normal ∨ (⁅X.map (QuotientGroup.mk' (CFSG.pCore 2 H)),
          CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H)⁆ = ⊥ ∧
        IsCyclic (CFSG.pCore p (H ⧸ CFSG.pCore 2 H)))) ∧
      (normalizer (X : Set H) = A → A < ⊤ →
        (CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H)).comap (QuotientGroup.mk' (CFSG.pCore 2 H))
          ≤ A ∧
        ⁅X.map (QuotientGroup.mk' (CFSG.pCore 2 H)), CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H)⁆ =
          ⊥ ∧
        IsCyclic (CFSG.pCore p (H ⧸ CFSG.pCore 2 H))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := CFSG.pCore 2 H with hC
  have hCn : C.Normal := CFSG.pCore_normal
  have hC2 : IsPGroup 2 C := CFSG.pCore_isPGroup
  set π := QuotientGroup.mk' C with hπ
  obtain ⟨S, hSA⟩ := hAS
  have hCA : C ≤ A := (hC2.le_sylow_of_normal S).trans hSA
  have hAX : A ≤ normalizer (X : Set H) := (normal_subgroupOf_iff_le_normalizer hXA).mp hXn
  have hCX : C ≤ normalizer (X : Set H) := hCA.trans hAX
  have hO2E : CFSG.pCore 2 (H ⧸ C) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hrkE : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r (H ⧸ C) ≤ 2 := by
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    have hrC : ¬ r ∣ Nat.card C := by
      obtain ⟨k, hk⟩ := hC2.exists_card_eq
      rw [hk]
      intro hd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_quotient_eq C hrC,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrk r hr hr2
  have hpow : ∀ w : X ⧸ CFSG.pCore 2 X, w ^ p = 1 := fun w => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one w
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := fun w => ⟨1, by rw [pow_one, hpow]⟩
  have hXnt : Nontrivial (X ⧸ CFSG.pCore 2 X) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h1 : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = 1 := Monoid.exp_eq_one_iff.mpr hnt
    rw [hexp] at h1
    exact hp.one_lt.ne' h1
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p X))
  set P : Subgroup H := (P₀ : Subgroup X).map X.subtype with hP
  have hPsyl : IsSylowOf p P X := ⟨P₀, rfl⟩
  have hPX : P ≤ X := map_subtype_le _
  have hPp : IsPGroup p P := hPsyl.isPGroup
  have hPC : Disjoint P C := IsPGroup.disjoint_of_ne p 2 hp2 P C hPp hC2
  set e₀ : (P₀ : Subgroup X) ≃* X ⧸ CFSG.pCore 2 X :=
    MulEquiv.ofBijective _ (NQTerm.sylow_bijective_coreQuot hp2 hXp P₀) with he₀
  set ψ : (P₀ : Subgroup X) →* H ⧸ C := π.comp (X.subtype.comp (P₀ : Subgroup X).subtype)
    with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    have h1 : ((y : X) : H) ∈ P ⊓ C := ⟨⟨y, y.2, rfl⟩, hy⟩
    rw [disjoint_iff.mp hPC, mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  set Pbar : Subgroup (H ⧸ C) := P.map π with hPbar
  have hrangeψ : ψ.range = Pbar := by
    rw [hψ, MonoidHom.range_comp, MonoidHom.range_comp, range_subtype]
  let eP : (P₀ : Subgroup X) ≃* Pbar :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hrangeψ)
  have heP : ∀ y : (P₀ : Subgroup X), ((eP y : Pbar) : H ⧸ C) = ψ y := fun _ => rfl
  have hPbarp : IsPGroup p Pbar := hPp.map π
  have hPrk : CFSG.pRank p Pbar = 2 := by
    rw [pRank_congr hp.one_lt (eP.symm.trans e₀), hrkX]
  have hPexp : ∀ x ∈ Pbar, x ^ p = 1 := pow_eq_one_of_mulEquiv (eP.symm.trans e₀) hpow
  have hPnt : Nontrivial Pbar := (eP.symm.trans e₀).toEquiv.nontrivial
  have hΦlt : (frattini Pbar).map Pbar.subtype < Pbar := by
    refine lt_of_le_of_ne (map_subtype_le _) fun heq => (frattini_lt_top (A := Pbar)).ne ?_
    rw [eq_top_iff]
    intro x _
    have h1 : (x : H ⧸ C) ∈ (frattini Pbar).map Pbar.subtype := by rw [heq]; exact x.2
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [← Subtype.ext hyx]
  set S' : Subgroup (H ⧸ C) := (A ⊓ normalizer (P : Set H)).map π with hS'
  have hSP : S' ≤ normalizer (Pbar : Set (H ⧸ C)) :=
    (map_mono inf_le_right).trans (le_normalizer_map π)
  set θ : Pbar →* (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) :=
    ((QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))).comp e₀.toMonoidHom).comp
      eP.symm.toMonoidHom with hθ
  have hθker : θ.ker = frattini Pbar := by
    rw [hθ, ker_comp_symm]
    have h1 := ker_comp_symm (QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))) e₀.symm
    rw [MulEquiv.symm_symm, QuotientGroup.ker_mk', map_frattini_mulEquiv] at h1
    rw [h1, map_frattini_mulEquiv]
  have hθψ : ∀ y : (P₀ : Subgroup X), θ (eP y) =
      ((((y : X) : X ⧸ CFSG.pCore 2 X)) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := by
    intro y
    rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      MonoidHom.comp_apply]
    rfl
  have hirrS : ∀ Y : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ s ∈ S', ∀ y z : Pbar, (z : H ⧸ C) = s * y * s⁻¹ → θ y ∈ Y → θ z ∈ Y) →
      Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    apply hirr Y
    intro h hhA w hw
    obtain ⟨x, hxX, hx⟩ := exists_conj_eq_of_isSylowOf hPsyl (isSylowOf_map_conj hPsyl h.2)
    set n : H := x⁻¹ * h with hn
    have hnA : n ∈ A := A.mul_mem (A.inv_mem (hXA hxX)) hhA
    have hnPeq : P.map (MulAut.conj n).toMonoidHom = P := by
      have h1 := congrArg (fun K : Subgroup H => K.map (MulAut.conj x⁻¹).toMonoidHom) hx
      simp only [map_map] at h1
      have e1 : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id H := by
        ext y
        change x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y
        group
      have e2 : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj (h : H)).toMonoidHom =
          (MulAut.conj n).toMonoidHom := by
        ext y
        simp [MulAut.conj_apply, hn, mul_assoc]
      rw [e1, e2, map_id] at h1
      exact h1.symm
    have hnP : n ∈ normalizer (P : Set H) := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [← hnPeq]
        exact ⟨y, hy, rfl⟩
      · intro hy
        rw [← hnPeq] at hy
        obtain ⟨y', hy', hyy⟩ := hy
        have : y' = y := by
          have h1 : n * y' * n⁻¹ = n * y * n⁻¹ := hyy
          simpa using h1
        rwa [← this]
    have hxN : x ∈ normalizer (X : Set H) := hAX (hXA hxX)
    have hnN : n ∈ normalizer (X : Set H) := mul_mem (inv_mem hxN) h.2
    have hsplit : normalizerFrattiniConj X h = normalizerFrattiniConj X ⟨n, hnN⟩ := by
      have : h = ⟨x, hxN⟩ * ⟨n, hnN⟩ := Subtype.ext (by simp [hn])
      rw [this, map_mul, normalizerFrattiniConj_eq_one_of_mem hXp _ hxX, one_mul]
    rw [hsplit]
    obtain ⟨y₀, rfl⟩ : ∃ y₀ : (P₀ : Subgroup X), θ (eP y₀) = w := by
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
      obtain ⟨y₀, hy₀⟩ := e₀.surjective q
      exact ⟨y₀, by rw [hθψ, ← hy₀]; rfl⟩
    have hnyP : n * ((y₀ : X) : H) * n⁻¹ ∈ P :=
      (mem_normalizer_iff.mp hnP _).mp ⟨y₀, y₀.2, rfl⟩
    obtain ⟨z₀, hz₀, hz₀y⟩ := hnyP
    set z : (P₀ : Subgroup X) := ⟨z₀, hz₀⟩ with hz
    have hsS : π n ∈ S' := ⟨n, mem_inf.mpr ⟨hnA, hnP⟩, rfl⟩
    have hconj : ((eP z : Pbar) : H ⧸ C) =
        π n * ((eP y₀ : Pbar) : H ⧸ C) * (π n)⁻¹ := by
      rw [heP, heP]
      change π (X.subtype z₀) = π n * π ((y₀ : X) : H) * (π n)⁻¹
      rw [hz₀y, ← map_inv, ← map_mul, ← map_mul]
    have h1 := hY _ hsS (eP y₀) (eP z) hconj hw
    rw [hθψ] at h1 ⊢
    have h2 : X.normalizerMonoidHom ⟨n, hnN⟩ (y₀ : X) = z₀ := Subtype.ext hz₀y.symm
    change (((X.normalizerMonoidHom ⟨n, hnN⟩ (y₀ : X) : X) : X ⧸ CFSG.pCore 2 X) :
      (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) ∈ Y
    rw [h2]
    exact h1
  have hirrP : (frattini Pbar).map Pbar.subtype < Pbar ∧ ∀ Y : Subgroup (H ⧸ C),
      (frattini Pbar).map Pbar.subtype ≤ Y → Y ≤ Pbar →
      normalizer (Pbar : Set (H ⧸ C)) ≤ normalizer (Y : Set (H ⧸ C)) →
      Y = (frattini Pbar).map Pbar.subtype ∨ Y = Pbar :=
    ⟨hΦlt, fun Y hΦY hYP hYn => frattini_lattice_irreducible hSP θ hθker hirrS Y hΦY hYP hYn⟩
  obtain ⟨-, -, -, hdich⟩ :=
    rank_two_odd_Fitting_normalizer_dichotomy hO2E hrkE hp hp2 hPbarp hPrk hPexp hirrP
  have hidx2 : ∀ N : Subgroup X, (P₀ : Subgroup X) ≤ N → ∃ k : ℕ, N.index ∣ 2 ^ k :=
    fun N hPN => index_dvd_two_pow_of_sylow_le hp2 hXp P₀ hPN
  have hXC2 : ∃ k : ℕ, X.relIndex (C ⊔ X) ∣ 2 ^ k := by
    obtain ⟨k, hk⟩ := hC2.exists_card_eq
    refine ⟨k, ?_⟩
    rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal C X, ← hk]
    exact relIndex_dvd_card X C
  have hCXN : C ⊔ X ≤ normalizer (X : Set H) := sup_le hCX le_normalizer
  have hconjX : ∀ g : H, X.map (MulAut.conj g).toMonoidHom ≤ C ⊔ X →
      g ∈ normalizer (X : Set H) := by
    intro g hg
    have hle := le_of_noPQuotient_two (noPQuotient_conjugate hX2 g) hg le_sup_right hCXN hXC2
    have heq : X.map (MulAut.conj g).toMonoidHom = X :=
      eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← heq]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← heq] at hy
      obtain ⟨y', hy', hyy⟩ := hy
      have : y' = y := by
        have h1 : g * y' * g⁻¹ = g * y * g⁻¹ := hyy
        simpa using h1
      rwa [← this]
  have hmain : X.Normal ∨ (⁅X.map π, CFSG.fittingSubgroup (H ⧸ C)⁆ = ⊥ ∧
      IsCyclic (CFSG.pCore p (H ⧸ C))) := by
    rcases hdich with ⟨-, -, hPn⟩ | ⟨hcyc, hPF⟩
    · left
      have hXK : X ≤ Pbar.comap π := by
        have hN : ((Pbar.comap π).subgroupOf X).Normal := by
          have : (Pbar.comap π).Normal := hPn.comap π
          infer_instance
        have hPN : (P₀ : Subgroup X) ≤ (Pbar.comap π).subgroupOf X := by
          intro y hy
          rw [mem_subgroupOf, mem_comap]
          exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        obtain ⟨k, hk⟩ := hidx2 _ hPN
        have h1 := hX2 _ (isPGroup_two_of_card_dvd (k := k) hk)
        intro x hx
        have : (⟨x, hx⟩ : X) ∈ (Pbar.comap π).subgroupOf X := h1 ▸ mem_top _
        exact this
      have hpre : Pbar.comap π = C ⊔ X := by
        have h1 : X.map π = Pbar :=
          le_antisymm (map_le_iff_le_comap.mpr hXK) (map_mono hPX)
        rw [← h1, comap_map_eq, QuotientGroup.ker_mk', sup_comm]
      refine ⟨fun x hx g => ?_⟩
      have hgN := hconjX g (by
        rw [← hpre]
        rintro _ ⟨y, hy, rfl⟩
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]
        have h1 := (mem_normalizer_iff.mp (normalizer_eq_top_iff.mpr hPn ▸ mem_top (π g))
          (π y)).mp (hXK hy)
        exact h1)
      exact (mem_normalizer_iff.mp hgN x).mp hx
    · right
      refine ⟨?_, hcyc⟩
      set F := CFSG.fittingSubgroup (H ⧸ C) with hF
      have hFn : F.Normal := CFSG.fittingSubgroup_normal
      have hCF : (centralizer (F : Set (H ⧸ C))).Normal := inferInstance
      have hN₁ : ((centralizer (F : Set (H ⧸ C))).comap π).subgroupOf X |>.Normal := by
        have : ((centralizer (F : Set (H ⧸ C))).comap π).Normal := hCF.comap π
        infer_instance
      have hPN : (P₀ : Subgroup X) ≤ ((centralizer (F : Set (H ⧸ C))).comap π).subgroupOf X := by
        intro y hy
        rw [mem_subgroupOf, mem_comap]
        have h1 : π ((y : X) : H) ∈ Pbar := ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        rw [commutator_eq_bot_iff_le_centralizer] at hPF
        exact hPF h1
      obtain ⟨k, hk⟩ := hidx2 _ hPN
      have h1 := hX2 _ (isPGroup_two_of_card_dvd (k := k) hk)
      rw [commutator_eq_bot_iff_le_centralizer]
      rintro _ ⟨x, hx, rfl⟩
      have : (⟨x, hx⟩ : X) ∈ ((centralizer (F : Set (H ⧸ C))).comap π).subgroupOf X :=
        h1 ▸ mem_top _
      exact this
  have hB : (CFSG.fittingSubgroup (H ⧸ C)).comap π ≤ normalizer (X : Set H) := by
    rcases hmain with hXn' | ⟨hXF, -⟩
    · rw [normalizer_eq_top_iff.mpr hXn']
      exact le_top
    · intro b hb
      apply hconjX b
      rintro _ ⟨x, hx, rfl⟩
      have hc : (MulAut.conj b) x * x⁻¹ ∈ C := by
        rw [← QuotientGroup.ker_mk' C, MonoidHom.mem_ker]
        change π (b * x * b⁻¹ * x⁻¹) = 1
        have hxb : π x * π b = π b * π x := by
          rw [commutator_eq_bot_iff_le_centralizer] at hXF
          exact (mem_centralizer_iff.mp (hXF ⟨x, hx, rfl⟩) (π b) hb).symm
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hxb]
        group
      have : (MulAut.conj b) x = ((MulAut.conj b) x * x⁻¹) * x := by group
      rw [MulEquiv.coe_toMonoidHom, this]
      exact (C ⊔ X).mul_mem (le_sup_left (a := C) hc) (le_sup_right (a := C) hx)
  refine ⟨hCA, hB, hmain, fun hNA hAtop => ?_⟩
  rcases hmain with hXn' | ⟨hXF, hcyc⟩
  · exfalso
    apply hAtop.ne
    rw [← hNA, normalizer_eq_top_iff.mpr hXn']
  · exact ⟨hNA ▸ hB, hXF, hcyc⟩

end CFSG.Quasithin.H13.NQRigid
