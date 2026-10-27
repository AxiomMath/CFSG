module

public import CFSG.Quasithin.Vol2.E2NineTI2bDefs
public import CFSG.Quasithin.Vol2.E2NineTIPair

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open scoped commutatorElement

namespace E2

namespace TI2b

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem commutator_kerIn_mem_pCoreOf (hmp : MinParabolic H T M) {g : G} (hg : g ∈ H) {x a : G}
    (hx : x ∈ kerIn M H) (ha : a ∈ conjSub g (pCoreOf 2 M)) : ⁅x, a⁆ ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMH : M ≤ H := hmp.maximal.1.le
  have hbO : g⁻¹ * a * g ∈ pCoreOf 2 M := mem_conjSub.mp ha
  have hbM : g⁻¹ * a * g ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hbO
  have hx'J : g⁻¹ * x * g ∈ kerIn M H := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M H (H.inv_mem hg)) x).mp hx
    simpa [mul_assoc] using this
  have hx'M : g⁻¹ * x * g ∈ M := kerIn_le hx'J
  have hcO : ⁅g⁻¹ * x * g, g⁻¹ * a * g⁆ ∈ pCoreOf 2 M := by
    rw [commutatorElement_def]
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hbO)
    exact (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hx'M)
      _).mp hbO
  have hcJ : ⁅g⁻¹ * x * g, g⁻¹ * a * g⁆ ∈ kerIn M H := by
    rw [commutatorElement_def]
    have h1 : (g⁻¹ * a * g) * (g⁻¹ * x * g)⁻¹ * (g⁻¹ * a * g)⁻¹ ∈ kerIn M H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M H (hMH hbM)) _).mp
        (Subgroup.inv_mem _ hx'J)
      simpa [mul_assoc] using this
    simpa [mul_assoc] using Subgroup.mul_mem _ hx'J h1
  have hcH : ⁅g⁻¹ * x * g, g⁻¹ * a * g⁆ ∈ pCoreOf 2 H := by
    have hz : Subgroup.zpowers ⁅g⁻¹ * x * g, g⁻¹ * a * g⁆ ≤ pCoreOf 2 H :=
      hmp.le_pCoreOf_of_isPGroup_of_le_kerIn
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (Subgroup.zpowers_le.mpr hcO))
        (Subgroup.zpowers_le.mpr hcJ)
    exact hz (Subgroup.mem_zpowers _)
  have hxa : ⁅x, a⁆ = g * ⁅g⁻¹ * x * g, g⁻¹ * a * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hxa]
  exact (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg)
    _).mp hcH

theorem card_barRad_le_card_barO2 {Q : Type} [Group Q] [Finite Q] (B : Subgroup Q) :
    Nat.card (E1.barRad Q B) ≤ Nat.card (E1.barO2 Q B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.Open.pCore 2 Q ≤ CFSG.solvableRadical Q := by
    have h2 := (CFSG.LieType.BorelTits.pCore_isPGroup (G := Q) 2).isNilpotent
    exact A3.le_solvableRadical (CFSG.LieType.BorelTits.pCore_normal 2) inferInstance
  let φ : (Q ⧸ CFSG.Open.pCore 2 Q) →* (Q ⧸ CFSG.solvableRadical Q) :=
    QuotientGroup.map _ _ (MonoidHom.id Q) (by simpa using hle)
  have hmap : (E1.barO2 Q B).map φ = E1.barRad Q B := by
    unfold E1.barO2 E1.barRad
    rw [Subgroup.map_map]
    rfl
  rw [← hmap]
  exact Nat.card_le_card_of_surjective (φ.subgroupMap _) (φ.subgroupMap_surjective _)

theorem false_of_eOne_aux {Q : Type} [Group Q] [Finite Q] {B R N : Subgroup Q} [R.Normal]
    (hNR : N ≤ R) (hBR : B ≤ R) (hRN : ∀ r ∈ R, ∃ j : ℕ, r ^ 2 ^ j ∈ N)
    (hNB : ∀ n ∈ N, ∀ b ∈ B, ⁅n, b⁆ ∈ CFSG.Open.pCore 2 Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h0 : CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) ≠ ⊥)
    (h1 : CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) =
      ⁅CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q), E1.barO2 Q B⁆) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 Q) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set P := CFSG.Open.pCore p (Q ⧸ CFSG.Open.pCore 2 Q) with hP
  haveI hPn : P.Normal := CFSG.LieType.BorelTits.pCore_normal p
  haveI hRn : (R.map π).Normal := Subgroup.Normal.map ‹R.Normal› π hπs
  have hBbar : E1.barO2 Q B = B.map π := rfl
  have hPR : P ≤ R.map π := by
    calc P = ⁅P, E1.barO2 Q B⁆ := h1
      _ ≤ ⁅P, R.map π⁆ := by
        rw [hBbar]
        exact Subgroup.commutator_mono le_rfl (Subgroup.map_mono hBR)
      _ ≤ R.map π := Subgroup.commutator_le_right P (R.map π)
  have hPN : P ≤ N.map π := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hPR hx
    obtain ⟨j, hj⟩ := hRN r hr
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := Q ⧸ CFSG.Open.pCore 2 Q) p)
      ⟨π r, hx⟩
    have hm' : (π r) ^ (p ^ m) = 1 := congrArg Subtype.val hm
    have hcop : IsCoprime ((2 ^ j : ℕ) : ℤ) ((p ^ m : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow j m ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    obtain ⟨a, b, hab⟩ := hcop
    have hrN : (π r) ^ (2 ^ j) ∈ N.map π := ⟨r ^ 2 ^ j, hj, by simp⟩
    have hx1 : π r = ((π r) ^ (2 ^ j)) ^ a * ((π r) ^ (p ^ m)) ^ b := by
      have e : (π r) ^ (a * ((2 ^ j : ℕ) : ℤ) + b * ((p ^ m : ℕ) : ℤ)) =
          ((π r) ^ (2 ^ j)) ^ a * ((π r) ^ (p ^ m)) ^ b := by
        rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      rw [← e, hab, zpow_one]
    rw [hx1, hm', one_zpow, mul_one]
    exact Subgroup.zpow_mem _ hrN a
  have hP1 : P ≤ ⊥ := by
    calc P = ⁅P, E1.barO2 Q B⁆ := h1
      _ ≤ ⁅N.map π, E1.barO2 Q B⁆ := Subgroup.commutator_mono hPN le_rfl
      _ = (⁅N, B⁆).map π := by rw [hBbar, Subgroup.map_commutator]
      _ ≤ ⊥ := by
        rw [Subgroup.map_le_iff_le_comap, Subgroup.commutator_le]
        intro n hn b hb
        rw [Subgroup.mem_comap, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact hNB n hn b hb
  exact h0 (le_bot_iff.mp hP1)

theorem not_eOne_of_star_le_pGroup (hmp : MinParabolic H T M) {K' A : Subgroup G} (hK'H : K' ≤ H)
    (hAK' : A ≤ K') {g : G} (hg : g ∈ H) (hA : A ≤ conjSub g (pCoreOf 2 M))
    {U : Subgroup (StarQuot M H)} (hU2 : IsPGroup 2 U)
    (hK'U : star M H K' ≤ Subgroup.normalizer (U : Set (StarQuot M H)))
    (hAU : star M H A ≤ U) : ¬ E1.EOne ↥K' (A.subgroupOf K') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨p, hp, hp2, -, h0, h1, -⟩
  set ψ : ↥K' →* StarQuot M H := (E2P.starMap M H).comp (Subgroup.inclusion hK'H) with hψ
  have hψk : ∀ k : ↥K', ψ k ∈ star M H K' := fun k => starMap_mem_star (hK'H k.2) k.2
  set R : Subgroup ↥K' := U.comap ψ with hR
  haveI hRn : R.Normal := ⟨fun r hr k => by
    show ψ (k * r * k⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hK'U (hψk k)) (ψ r)).mp hr⟩
  have hker : ∀ n : ↥K', ψ n = 1 → (n : G) ∈ kerIn M H := fun n hn => by
    have h2 : (Subgroup.inclusion hK'H n) ∈ (E2P.starMap M H).ker := hn
    rw [E2P.ker_starMap, Subgroup.mem_subgroupOf] at h2
    exact h2
  refine false_of_eOne_aux (B := A.subgroupOf K') (R := R) (N := ψ.ker) (p := p) ?_ ?_ ?_ ?_ hp hp2
    h0 h1
  · intro n hn
    show ψ n ∈ U
    rw [MonoidHom.mem_ker.mp hn]
    exact U.one_mem
  · intro b hb
    exact hAU (starMap_mem_star (hK'H b.2) (Subgroup.mem_subgroupOf.mp hb))
  · intro r hr
    obtain ⟨j, hj⟩ := hU2 ⟨ψ r, hr⟩
    refine ⟨j, ?_⟩
    rw [MonoidHom.mem_ker, map_pow]
    exact congrArg Subtype.val hj
  · intro n hn b hb
    have hnJ := hker n (MonoidHom.mem_ker.mp hn)
    have hbA : (b : G) ∈ A := Subgroup.mem_subgroupOf.mp hb
    have hcomm := commutator_kerIn_mem_pCoreOf hmp hg hnJ (hA hbA)
    have hN' : ((pCoreOf 2 H).subgroupOf K').Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (hK'H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
    have hp' : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf K') :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_subtype
    refine CFSG.LieType.BorelTits.le_pCore 2 hN' hp' ?_
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hcomm

theorem le_solvRad_of_normalized {Y S : Subgroup G} (hSY : S ≤ Y) (hsol : Group.IsSolvable ↥S)
    (hN : Y ≤ Subgroup.normalizer (S : Set G)) : S ≤ (CFSG.solvableRadical ↥Y).map Y.subtype := by
  have hn : (S.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSY).mpr hN
  have hs : Group.IsSolvable ↥(S.subgroupOf Y) := Group.isSolvable_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe hSY).symm.toMonoidHom) (MulEquiv.surjective _)
  have h1 := A3.le_solvableRadical hn hs
  intro s hs'
  exact ⟨⟨s, hSY hs'⟩, h1 (Subgroup.mem_subgroupOf.mpr hs'), rfl⟩

theorem card_star_le_card_barRad_of_dich {K' A : Subgroup G} (hK'H : K' ≤ H) (hAK' : A ≤ K')
    {K : Subgroup (StarQuot M H)} (hKn : K.Normal) (hAK : star M H A ≤ K)
    (hA : star M H A ⊓ (CFSG.solvableRadical ↥(star M H K' ⊓ K)).map
      (star M H K' ⊓ K).subtype = ⊥) :
    Nat.card (star M H A) ≤ Nat.card (E1.barRad ↥K' (A.subgroupOf K')) := by
  have := E2P.finite_starQuot M H
  set X := star M H K' with hX
  refine card_star_le_card_barRad_of_inf hK'H hAK' fun a haA haR => ?_
  have haH : a ∈ H := hK'H (hAK' haA)
  obtain ⟨k, hk, hka⟩ := haR
  set π' : ↥K' →* ↥X := ((E2P.starMap M H).subgroupMap (K'.subgroupOf H)).comp
    (Subgroup.subgroupOfEquivOfLe hK'H).symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := ((E2P.starMap M H).subgroupMap_surjective _).comp
    (MulEquiv.surjective _)
  have hrad : (CFSG.solvableRadical ↥K').map π' ≤ CFSG.solvableRadical ↥X := by
    refine A3.le_solvableRadical (Subgroup.Normal.map inferInstance π' hπ's) ?_
    have h1 : Group.IsSolvable ↥(CFSG.solvableRadical ↥K') := A3.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective (f := π'.subgroupMap (CFSG.solvableRadical ↥K'))
      (π'.subgroupMap_surjective _)
  have hxX : E2P.starMap M H ⟨a, haH⟩ ∈ (CFSG.solvableRadical ↥X).map X.subtype := by
    refine ⟨π' k, hrad ⟨k, hk, rfl⟩, ?_⟩
    have : (⟨a, haH⟩ : ↥H) = Subgroup.inclusion hK'H k := Subtype.ext hka.symm
    rw [this]
    rfl
  have hxA : E2P.starMap M H ⟨a, haH⟩ ∈ star M H A := starMap_mem_star haH haA
  have hxK : E2P.starMap M H ⟨a, haH⟩ ∈ K := hAK hxA
  have hsolX : Group.IsSolvable ↥((CFSG.solvableRadical ↥X).map X.subtype) := by
    have h' : Group.IsSolvable ↥(CFSG.solvableRadical ↥X) := A3.solvableRadical_isSolvable
    exact Group.isSolvable_of_surjective (f := (Subgroup.equivMapOfInjective _ _
      X.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hKN : Subgroup.normalizer (K : Set (StarQuot M H)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hKn
  have hS : (CFSG.solvableRadical ↥X).map X.subtype ⊓ K ≤
      (CFSG.solvableRadical ↥(X ⊓ K)).map (X ⊓ K).subtype := by
    refine le_solvRad_of_normalized (Y := X ⊓ K) (fun y hy => ⟨?_, hy.2⟩) ?_ ?_
    · obtain ⟨w, -, rfl⟩ := hy.1
      exact w.2
    · exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective _)
    · intro y hy
      refine mem_normalizer_inf_of_mem (le_normalizer_map_subtype (CFSG.solvableRadical ↥X) hy.1)
        ?_
      rw [hKN]
      exact Subgroup.mem_top y
  have h1 : E2P.starMap M H ⟨a, haH⟩ ∈ star M H A ⊓ (CFSG.solvableRadical ↥(X ⊓ K)).map
      (X ⊓ K).subtype := ⟨hxA, hS ⟨hxX, hxK⟩⟩
  rw [hA, Subgroup.mem_bot] at h1
  have h2 : (⟨a, haH⟩ : ↥H) ∈ (E2P.starMap M H).ker := h1
  rw [E2P.ker_starMap, Subgroup.mem_subgroupOf] at h2
  exact h2

theorem le_nParam_of_starDich (h : Hyp28 H T M V) (hTI : IsTISetIn V M)
    {K : Subgroup (StarQuot M H)} (hKn : K.Normal) {R₀ : Subgroup (StarQuot M H)}
    (hR₀E : R₀ ≤ star M H (tiClosure M V)) (hR₀K : R₀ ≤ K) {n : ℕ}
    (hcard : Nat.card R₀ = 2 ^ n) (hdich : StarDich K (star M H T) R₀) :
    (n : ℕ∞) ≤ E1.nParam H := by
  have := E2P.finite_starQuot M H
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  have hTH : T ≤ H := h.minParabolic.isSylow.1
  set E := tiClosure M V with hEdef
  have hEel := h.isElemAbelian_tiClosure hTI
  have hEO := h.tiClosure_le_pCoreOf
  have hET : E ≤ T := hEO.trans h.pCoreOf_M_le_T
  set F := E ⊓ (R₀.comap (E2P.starMap M H)).map H.subtype with hFdef
  have hFE : F ≤ E := inf_le_left
  have hFT : F ≤ T := hFE.trans hET
  have hFel : IsElemAbelian 2 F := by
    have := hEel.1
    exact ⟨⟨⟨fun a b => Subtype.ext (setLike_mul_comm (hFE a.2) (hFE b.2))⟩⟩,
      fun x hx => hEel.2 x (hFE hx)⟩
  have hFs : star M H F = R₀ := by
    ext x
    constructor
    · rintro ⟨⟨f, hfH⟩, hf, rfl⟩
      have hf' : f ∈ F := Subgroup.mem_subgroupOf.mp hf
      obtain ⟨y, hy, hyf⟩ := hf'.2
      have hy' : y = ⟨f, hfH⟩ := Subtype.ext hyf
      rw [← hy']
      exact hy
    · intro hx
      obtain ⟨⟨e, heH⟩, he, rfl⟩ := hR₀E hx
      exact ⟨⟨e, heH⟩, Subgroup.mem_subgroupOf.mpr
        ⟨Subgroup.mem_subgroupOf.mp he, ⟨⟨e, heH⟩, hx, rfl⟩⟩, rfl⟩
  have hFJ : ¬ F ≤ kerIn M H := by
    intro hle
    have h1 : star M H F = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨⟨f, hfH⟩, hf, rfl⟩
      rw [Subgroup.mem_bot]
      show QuotientGroup.mk' _ _ = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hle (Subgroup.mem_subgroupOf.mp hf)
    rw [hFs] at h1
    rw [h1, Subgroup.card_bot] at hcard
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  have hKN : Subgroup.normalizer (K : Set (StarQuot M H)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hKn
  refine le_nParam_of_forall_isE h.minParabolic hFT hFel hFJ ?_
  intro i hi0 hin g hg hAT K' hE'
  exfalso
  obtain ⟨hK'H, hτ, -, hEE⟩ := hE'
  set A := A1b.conjSub g F with hAdef
  have hAeq : A = conjSub g F := a1bConjSub_eq g F
  have hAH : A ≤ H := hAT.trans hTH
  have hAel : IsElemAbelian 2 A := isElemAbelian_cjSub hFel
  set g' := E2P.starMap M H ⟨g, hg⟩ with hg'
  have hAs : star M H A = conjSub g' R₀ := by
    rw [hAeq, star_conjSub hg, hFs]
  have hAsT : star M H A ≤ star M H T := star_mono hAT
  have hAK' : A ≤ K' := fun a ha => (hτ (mem_tauOf_of_commutator_mem_kerIn h.minParabolic hAT
    (hAT ha) fun a' ha' => by
      have := hAel.1
      have hc : a * a' = a' * a := setLike_mul_comm ha ha'
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
      exact (kerIn M H).one_mem)).2
  have hCK' : star M H T ⊓ Subgroup.centralizer (star M H A : Set (StarQuot M H)) ≤
      star M H K' := by
    intro y hy
    obtain ⟨hyT, hyC⟩ := hy
    obtain ⟨⟨t, htH⟩, ht, rfl⟩ := hyT
    have htT : t ∈ T := Subgroup.mem_subgroupOf.mp ht
    refine starMap_mem_star htH ((hτ (mem_tauOf_of_commutator_mem_kerIn h.minParabolic hAT htT
      fun a ha => ?_)).2)
    have has : E2P.starMap M H ⟨a, hAH ha⟩ ∈ star M H A := starMap_mem_star (hAH ha) ha
    exact commutator_mem_kerIn_of_commute (hTH htT) (hAH ha)
      ((Subgroup.mem_centralizer_iff.mp hyC) _ has).symm
  set X := star M H K' with hX
  have hAK : star M H A ≤ K := by
    rw [hAs]
    intro y hy
    have h1 := hR₀K (mem_conjSub.mp hy)
    have h2 := hKn.conj_mem _ h1 g'
    simpa [mul_assoc] using h2
  have hCY : star M H T ⊓ K ⊓ Subgroup.centralizer (conjSub g' R₀ : Set (StarQuot M H)) ≤
      X ⊓ K := by
    intro y hy
    refine ⟨hCK' ⟨hy.1.1, ?_⟩, hy.1.2⟩
    rw [hAs]
    exact hy.2
  have hd := hdich g' (by rw [← hAs]; exact hAsT) (X ⊓ K) inf_le_right hCY
  rw [← hAs] at hd
  rcases hd with hd | hd
  ·
    have hU2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊓ K)
    have hXY : X ≤ Subgroup.normalizer ((X ⊓ K : Subgroup (StarQuot M H)) : Set _) :=
      fun x hx => mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx) (by rw [hKN]; trivial)
    have hXU := hXY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (X ⊓ K))
    have hA' : A ≤ conjSub g (pCoreOf 2 M) := fun a ha =>
      mem_conjSub.mpr (hEO (hFE (mem_conjSub.mp (hAeq ▸ ha))))
    rcases hEE with ⟨hE1, -⟩ | ⟨hE2, -⟩
    · exact not_eOne_of_star_le_pGroup h.minParabolic hK'H hAK' hg hA' hU2 hXU hd hE1
    · exact not_eTwo_of_le_solvableRadical
        (le_solvableRadical_of_star_le h.minParabolic hK'H hAK' hU2 hXU hd) hE2
  ·
    have hcardle := card_star_le_card_barRad_of_dich hK'H hAK' hKn hAK hd
    have hcardA : Nat.card ↥(star M H A) = 2 ^ n := by
      rw [hAs, B6.card_conjSub, hcard]
    rw [hcardA] at hcardle
    have hlt : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hin
    rcases hEE with ⟨hE1, -⟩ | ⟨-, hle⟩
    · obtain ⟨p, -, -, -, -, -, hc2⟩ := hE1
      have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := card_barRad_le_card_barO2 (A.subgroupOf K')
      omega
    · omega

end TI2b

end E2

end CFSG.Quasithin
