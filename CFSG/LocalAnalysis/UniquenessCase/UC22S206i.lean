module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (i1020_adjoin i1020_isElemAbelian_zpowers
  i1020_coprime_lift)
open CFSG.HardMathSupport.Solomon.Coordinator.Generation228 (exists_fixed_mem_coset)

section D

variable {H : Type} [Group H]

theorem uc22s206i_conj {Q : Subgroup H} [Q.Normal] {R : Subgroup ↥Q} [R.Characteristic]
    {p d : ℕ} (e : ↥R ⧸ frattini ↥R ≃* Multiplicative (Fin d → ZMod p))
    (φ : H →* GL (Fin d) (ZMod p))
    (hφ : ∀ (g : H) (x y : ↥R), ((y : ↥Q) : H) = g * ((x : ↥Q) : H) * g⁻¹ →
      (φ g : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ
          Multiplicative.toAdd (e (x : ↥R ⧸ frattini ↥R)) =
        Multiplicative.toAdd (e (y : ↥R ⧸ frattini ↥R)))
    (g : H) (x : ↥R) :
    ∃ y : ↥R, ((y : ↥Q) : H) = g * ((x : ↥Q) : H) * g⁻¹ ∧
      Multiplicative.toAdd (e (y : ↥R ⧸ frattini ↥R)) =
        (φ g : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ
          Multiplicative.toAdd (e (x : ↥R ⧸ frattini ↥R)) :=
  ⟨⟨MulAut.conjNormal g (x : ↥Q), (MulAut.characteristic R (MulAut.conjNormal g) x).2⟩,
    MulAut.conjNormal_apply g (x : ↥Q),
    (hφ g x ⟨MulAut.conjNormal g (x : ↥Q), (MulAut.characteristic R (MulAut.conjNormal g) x).2⟩
      (MulAut.conjNormal_apply g (x : ↥Q))).symm⟩

theorem uc22s206i_elem [Finite H] {Q : Subgroup H} [Q.Normal] {R : Subgroup ↥Q}
    [R.Characteristic] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hRexp : ∀ x ∈ R, x ^ p = 1)
    {d : ℕ} (e : ↥R ⧸ frattini ↥R ≃* Multiplicative (Fin d → ZMod p))
    (φ : H →* GL (Fin d) (ZMod p))
    (hφ : ∀ (g : H) (x y : ↥R), ((y : ↥Q) : H) = g * ((x : ↥Q) : H) * g⁻¹ →
      (φ g : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ
          Multiplicative.toAdd (e (x : ↥R ⧸ frattini ↥R)) =
        Multiplicative.toAdd (e (y : ↥R ⧸ frattini ↥R)))
    {h : H} (hh3 : h ^ 3 = 1)
    (h1 : 1 < Module.finrank (ZMod p) (LinearMap.ker
      ((Matrix.mulVecLin ((φ h : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) :
        Module.End (ZMod p) (Fin d → ZMod p)) - 1))) :
    ∃ E : Subgroup H, CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      E ≤ centralizer (zpowers h : Set H) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set ι : ↥R →* H := Q.subtype.comp R.subtype with hι
  have hιinj : Function.Injective ι := fun a b hab => Subtype.ext (Subtype.ext hab)
  obtain ⟨W, hWfix, hW1⟩ : ∃ W : Submodule (ZMod p) (Fin d → ZMod p),
      (∀ w ∈ W, ((φ h : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ w = w) ∧
        1 < Module.finrank (ZMod p) W := by
    refine ⟨_, fun w hw => ?_, h1⟩
    have h0 : Matrix.mulVecLin ((φ h : GL (Fin d) (ZMod p)) :
        Matrix (Fin d) (Fin d) (ZMod p)) w - w = 0 := LinearMap.mem_ker.mp hw
    rwa [sub_eq_zero, Matrix.mulVecLin_apply] at h0
  have hexp : ∀ r : ↥R, r ^ p = 1 := fun r => Subtype.ext (by simpa using hRexp r r.2)
  have hRp : IsPGroup p ↥R := fun r => ⟨1, by rw [pow_one]; exact hexp r⟩
  have hψ0 : ∀ r : ↥R,
      Multiplicative.toAdd (e (r : ↥R ⧸ frattini ↥R)) = 0 ↔ r ∈ frattini ↥R := by
    intro r
    rw [toAdd_eq_zero, e.map_eq_one_iff, QuotientGroup.eq_one_iff]
  haveI hNormal : ((frattini ↥R).map ι).Normal := by
    constructor
    rintro _ ⟨o, ho, rfl⟩ g
    obtain ⟨o', ho'1, ho'2⟩ := uc22s206i_conj e φ hφ g o
    refine ⟨o', (hψ0 o').mp ?_, ho'1⟩
    rw [ho'2, (hψ0 o).mpr ho, Matrix.mulVec_zero]
  have hN3 : ¬ 3 ∣ Nat.card ((frattini ↥R).map ι) := by
    obtain ⟨k, hk⟩ := ((hRp.to_subgroup (frattini ↥R)).map ι).exists_card_eq
    rw [hk]
    intro h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have hA : IsPGroup 3 (zpowers h) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hh3)
  have hlift : ∀ w ∈ W, ∃ r : ↥R, Multiplicative.toAdd (e (r : ↥R ⧸ frattini ↥R)) = w ∧
      ι r ∈ centralizer (zpowers h : Set H) := by
    intro w hw
    have hfixn : ∀ n : ℕ,
        ((φ (h ^ n) : GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ w = w := by
      intro n
      induction n with
      | zero => rw [pow_zero, map_one, Units.val_one, Matrix.one_mulVec]
      | succ n ih =>
        rw [pow_succ, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hWfix w hw, ih]
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd w)
    obtain ⟨r₀, rfl⟩ := QuotientGroup.mk_surjective q
    have hr₀ : Multiplicative.toAdd (e (r₀ : ↥R ⧸ frattini ↥R)) = w := by rw [hq, toAdd_ofAdd]
    obtain ⟨n, hn, hcent⟩ := exists_fixed_mem_coset Nat.prime_three hA le_normalizer_of_normal
      hN3 (y := ι r₀) (by
        intro a ha
        obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr ha)
        obtain ⟨r', hr'1, hr'2⟩ := uc22s206i_conj e φ hφ (h ^ k) r₀
        have heq : ((r₀ : ↥R) : ↥R ⧸ frattini ↥R) = (r' : ↥R ⧸ frattini ↥R) := by
          apply e.injective
          apply Multiplicative.toAdd.injective
          rw [hr'2, hr₀, hfixn k]
        refine ⟨r₀⁻¹ * r', QuotientGroup.eq.mp heq, ?_⟩
        rw [map_mul, map_inv]
        congr 1)
    obtain ⟨o, ho, rfl⟩ := hn
    refine ⟨r₀ * o, ?_, ?_⟩
    · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).mpr ho, mul_one, hr₀]
    · rw [map_mul]
      exact hcent
  set C : Subgroup ↥R := (centralizer (zpowers h : Set H)).comap ι with hC
  have hCp : IsPGroup p C := hRp.to_subgroup C
  have hspan : ∀ v : Fin d → ZMod p,
      Module.finrank (ZMod p) (Submodule.span (ZMod p) {v}) ≤ 1 := by
    intro v
    have h' := finrank_span_le_card (R := ZMod p) ({v} : Set (Fin d → ZMod p))
    rwa [Set.toFinset_singleton, Finset.card_singleton] at h'
  have hout : ∀ v : Fin d → ZMod p, ∃ w ∈ W, w ∉ Submodule.span (ZMod p) {v} := by
    intro v
    refine SetLike.not_le_iff_exists.mp fun hle => ?_
    have h' := (Submodule.finrank_mono hle).trans (hspan v)
    omega
  obtain ⟨w₀, hw₀, hw₀0⟩ := hout 0
  obtain ⟨r₁, hr₁ψ, hr₁C⟩ := hlift w₀ hw₀
  have hCne : C ≠ ⊥ := by
    intro hbot
    have hr₁ : r₁ ∈ C := hr₁C
    rw [hbot, mem_bot] at hr₁
    apply hw₀0
    rw [← hr₁ψ, hr₁, QuotientGroup.mk_one, map_one, toAdd_one]
    exact Submodule.zero_mem _
  haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).2 hCne
  obtain ⟨z₀, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hCp.bot_lt_center.ne'
  set z : ↥R := ((z₀ : C) : ↥R) with hz
  have hzC : z ∈ C := (z₀ : C).2
  have hz1 : z ≠ 1 := fun h' => hz₀1 (Subtype.ext (Subtype.ext h'))
  have hzcomm : ∀ c ∈ C, c * z = z * c := fun c hc =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 z₀.2 ⟨c, hc⟩)
  obtain ⟨w, hw, hwv⟩ := hout (Multiplicative.toAdd (e (z : ↥R ⧸ frattini ↥R)))
  obtain ⟨r, hrψ, hrC⟩ := hlift w hw
  have hrz : r ∉ zpowers z := by
    intro hmem
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
    apply hwv
    rw [← hrψ, ← hk, QuotientGroup.mk_pow, map_pow, toAdd_pow]
    exact Submodule.smul_of_tower_mem _ k (Submodule.mem_span_singleton_self _)
  have hzp : orderOf z = p := orderOf_eq_prime (hexp z) hz1
  have hr1 : r ≠ 1 := fun h' => hrz (by rw [h']; exact (zpowers z).one_mem)
  have hrp : orderOf r = p := orderOf_eq_prime (hexp r) hr1
  obtain ⟨hE₀, hE₀card⟩ := i1020_adjoin hp (i1020_isElemAbelian_zpowers (hexp z)) (m := 1)
    (by rw [Nat.card_zpowers, hzp, pow_one]) hrp hrz (by
      intro a ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (show Commute z r from (hzcomm r hrC).symm) k).eq)
  have hE₀C : zpowers z ⊔ zpowers r ≤ C :=
    sup_le (zpowers_le.mpr hzC) (zpowers_le.mpr hrC)
  refine ⟨(zpowers z ⊔ zpowers r).map ι, hE₀.map ι, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hιinj, hE₀card]
  · rw [Subgroup.map_le_iff_le_comap]
    exact hE₀C

end D

theorem uc22s206i_lift {G : Type} [Group G] [Finite G] {M : Subgroup G} {x : ↥M} (hx3 : x ^ 3 = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hE' : CFSG.Open.IsElemAbelian p E') (hcard : Nat.card E' = p ^ 2)
    (hE'C : E' ≤ centralizer (zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) x) :
      Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ E : Subgroup ↥M, E ≤ centralizer (zpowers x : Set ↥M) ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (CFSG.pCore 2 ↥M) := CFSG.pCore_isPGroup
  have hA : IsPGroup 3 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hx3)
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk]
    intro h3
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)) (by decide)
  have hle : E' ≤ (centralizer (zpowers x : Set ↥M)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
    intro ē hē
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) ē
    have hyc := hE'C hē
    obtain ⟨n, hn, hyn⟩ := exists_fixed_mem_coset Nat.prime_three hA le_normalizer_of_normal hN3
      (y := y) (by
        intro a ha
        have hac : QuotientGroup.mk' (CFSG.pCore 2 ↥M) a ∈
            zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) x) := by
          rw [← MonoidHom.map_zpowers]
          exact mem_map_of_mem _ ha
        rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥M), MonoidHom.mem_ker, map_mul, map_inv,
          map_mul, map_mul, map_inv, mem_centralizer_iff.mp hyc _ hac]
        group)
    refine ⟨y * n, hyn, ?_⟩
    rw [map_mul, show QuotientGroup.mk' (CFSG.pCore 2 ↥M) n = 1 from
      (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
  have hker : ¬ p ∣ Nat.card (centralizer (zpowers x : Set ↥M) ⊓
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).ker : Subgroup ↥M) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (h2.to_le inf_le_right :
      IsPGroup 2 ↥(centralizer (zpowers x : Set ↥M) ⊓ CFSG.pCore 2 ↥M)).exists_card_eq
    rw [hk]
    intro hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd))
  exact i1020_coprime_lift (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) _ hker hle hE' hcard

theorem uc22s206i_two_le_pRank {G : Type} [Group G] [Finite G] {M K : Subgroup G} (hKM : K ≤ M)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {R : Subgroup ↥(CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M))} [R.Characteristic]
    (hRexp : ∀ x ∈ R, x ^ p = 1) {d : ℕ}
    (e : ↥R ⧸ frattini ↥R ≃* Multiplicative (Fin d → ZMod p))
    (φ : (↥M ⧸ CFSG.pCore 2 ↥M) →* GL (Fin d) (ZMod p))
    (hφ : ∀ (g : ↥M ⧸ CFSG.pCore 2 ↥M) (x y : ↥R),
      ((y : ↥(CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M))) : ↥M ⧸ CFSG.pCore 2 ↥M) =
          g * ((x : ↥(CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M))) : ↥M ⧸ CFSG.pCore 2 ↥M) * g⁻¹ →
        (φ g : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ
            Multiplicative.toAdd (e (x : ↥R ⧸ frattini ↥R)) =
          Multiplicative.toAdd (e (y : ↥R ⧸ frattini ↥R)))
    {x : ↥K} (hx3 : orderOf x = 3)
    (h1 : 1 < Module.finrank (ZMod p) (LinearMap.ker
      ((Matrix.mulVecLin
        (((φ.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM))) x :
          GL (Fin d) (ZMod p)) : Matrix (Fin d) (Fin d) (ZMod p)) :
        Module.End (ZMod p) (Fin d → ZMod p)) - 1))) :
    2 ≤ CFSG.Open.pRank p (M ⊓ centralizer (zpowers (x : G) : Set G)) := by
  set xM : ↥M := Subgroup.inclusion hKM x with hxM
  have hxM3 : xM ^ 3 = 1 := by
    rw [← hx3, ← orderOf_injective _ (Subgroup.inclusion_injective hKM) x]
    exact pow_orderOf_eq_one _
  obtain ⟨E', hE', hE'card, hE'C⟩ := uc22s206i_elem hp hp3 hRexp e φ hφ
    (h := QuotientGroup.mk' (CFSG.pCore 2 ↥M) xM) (by rw [← map_pow, hxM3, map_one]) h1
  obtain ⟨E, hEC, hE, hEcard⟩ := uc22s206i_lift hxM3 hp hp2 hE' hE'card hE'C
  refine CFSG.SectionRank.le_pRank hp.one_lt (E := E.map M.subtype) ?_ (hE.map M.subtype) ?_
  · rintro _ ⟨m, hm, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨m.2, mem_centralizer_iff.mpr ?_⟩
    intro s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hc := congrArg Subtype.val
      (mem_centralizer_iff.mp (hEC hm) (xM ^ k) (zpow_mem_zpowers xM k))
    simpa [hxM] using hc
  · rw [Subgroup.card_map_of_injective M.subtype_injective, hEcard]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
