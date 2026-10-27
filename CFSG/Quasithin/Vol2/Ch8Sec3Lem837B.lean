module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem838C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E1.LiftS5
open scoped IsMulCommutative

namespace Ch837

variable {G : Type} [Group G]

theorem quotConj_eq_one_of_commutator_mem {K : Subgroup G}
    {g : ↥(Subgroup.normalizer (K : Set G))}
    (h : ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K) : quotConj K g = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    change ((K.normalizerMonoidHom g k : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) =
      ((k : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)
    rw [QuotientGroup.eq]
    have hval : ((K.normalizerMonoidHom g k : ↥K) : G) = (g : G) * k * (g : G)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe K g k
    have h1 := h k k.2
    have h2 : ((K.normalizerMonoidHom g k : ↥K) * k⁻¹ : ↥K) ∈ CFSG.pCore 2 ↥K := by
      rw [← Vol2.Ch10.SecA.subgroupOf_pCoreOf, Subgroup.mem_subgroupOf]
      simpa [hval] using h1
    have h3 := (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem _ (inv_mem h2)
      (K.normalizerMonoidHom g k)⁻¹
    simpa [mul_assoc] using h3

theorem nonempty_quot_conjugate_equiv (K : Subgroup G) (g : G) :
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃*
      ↥(CFSG.conjugate K g) ⧸ CFSG.pCore 2 ↥(CFSG.conjugate K g)) := by
  let e : ↥K ≃* ↥(CFSG.conjugate K g) := MulEquiv.subgroupMap (MulAut.conj g⁻¹) K
  exact ⟨QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)⟩

variable [Finite G]

theorem mem_normalizer_of_mem_centralizerSection {M K X : Subgroup G} (hXK : X ≤ K)
    (hX : twoResidual X = X) (hOX : pCoreOf 2 K ≤ Subgroup.normalizer (X : Set G)) {c : G}
    (hc : c ∈ centralizerSection M K (pCoreOf 2 K)) : c ∈ Subgroup.normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 K with hOdef
  set R := X ⊔ O with hRdef
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hOX
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hres : twoResidual R = X := by
    apply le_antisymm
    · exact twoResidual_le_of_isTwoQuotient le_sup_left hRX
        (B6.isTwoQuotient_of_sup_eq hO2 hRX (sup_comm O X))
    · calc X = twoResidual X := hX.symm
        _ ≤ twoResidual R := F6.twoResidual_mono le_sup_left
  have key : ∀ d ∈ centralizerSection M K O, R ≤ R.comap (MulAut.conj d).toMonoidHom := by
    intro d hd
    obtain ⟨-, -, hdO, hdc⟩ := hd
    refine sup_le (fun x hx => ?_) (fun o ho => ?_)
    · change d * x * d⁻¹ ∈ R
      have h1 : x⁻¹ * d * x⁻¹⁻¹ * d⁻¹ ∈ O := hdc x⁻¹ (K.inv_mem (hXK hx))
      have e : d * x * d⁻¹ = x * (x⁻¹ * d * x⁻¹⁻¹ * d⁻¹) := by group
      rw [e]
      exact R.mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right h1)
    · change d * o * d⁻¹ ∈ R
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hdO o).mp ho)
  have hcR : c ∈ Subgroup.normalizer (R : Set G) := by
    refine B6.mem_normalizer_of_forall_mem (fun r hr => key c hc hr) (fun r hr => ?_)
    have := key c⁻¹ (Subgroup.inv_mem _ hc) hr
    simpa using this
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hcR ⊢
  rw [← hres, E1.map_twoResidual, hcR]

theorem le_sup_inf_normalizer {Gz Kz X T : Subgroup G} (hKz : Kz ≤ Gz)
    (hGzKz : Gz ≤ Subgroup.normalizer (Kz : Set G)) (hXK : X ≤ Kz) (hX : twoResidual X = X)
    (hOX : pCoreOf 2 Kz ≤ Subgroup.normalizer (X : Set G)) (hT : IsSylowTwoOf T Gz)
    (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hpow : ∀ g ∈ Gz, ∃ m : ℕ, g ^ 2 ^ m ∈ Kz ⊔ centralizerSection Gz Kz (pCoreOf 2 Kz)) :
    Gz ≤ Kz ⊔ (Gz ⊓ Subgroup.normalizer (X : Set G)) := by
  set C := centralizerSection Gz Kz (pCoreOf 2 Kz) with hCdef
  have hCGz : C ≤ Gz := centralizerSection_le_left _ _ _
  have hDGz : Kz ⊔ C ≤ Gz := sup_le hKz hCGz
  have hGzC : Gz ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    le_normalizer_centralizerSection Gz Kz ⟨hg, hGzKz hg⟩
  have hGzD : Gz ≤ Subgroup.normalizer ((Kz ⊔ C : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hGzKz hg),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hGzC hg)]
  have hsup := B6.sup_eq_of_isTwoQuotient hDGz hGzD hpow hT
  have hCX : C ≤ Gz ⊓ Subgroup.normalizer (X : Set G) := fun c hc =>
    ⟨hCGz hc, mem_normalizer_of_mem_centralizerSection hXK hX hOX hc⟩
  calc Gz = Kz ⊔ C ⊔ T := hsup.symm
    _ ≤ Kz ⊔ (Gz ⊓ Subgroup.normalizer (X : Set G)) :=
      sup_le (sup_le le_sup_left (hCX.trans le_sup_right))
        ((le_inf hT.1 hTX).trans le_sup_right)

omit [Finite G] in
theorem mem_centralizerSection_of_quotConj {M K : Subgroup G} {c : G} (hcM : c ∈ M)
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) (h : quotConj K ⟨c, hcK⟩ = 1) :
    c ∈ centralizerSection M K (pCoreOf 2 K) := by
  refine ⟨hcM, hcK, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hcK,
    fun x hx => ?_⟩
  have h1 := Ch838.commutator_mem_of_quotConj_eq_one h x hx
  have h2 := (pCoreOf 2 K).inv_mem h1
  have e : (c * x * c⁻¹ * x⁻¹)⁻¹ = x * c * x⁻¹ * c⁻¹ := by group
  rwa [e] at h2

omit [Finite G] in
theorem pow_mem_of_outIsTwoGroup {Gz Kz : Subgroup G} (hKz : Kz ≤ Gz)
    (hGzKz : Gz ≤ Subgroup.normalizer (Kz : Set G))
    (hOut : OutIsTwoGroup (↥Kz ⧸ CFSG.pCore 2 ↥Kz)) :
    ∀ g ∈ Gz, ∃ m : ℕ, g ^ 2 ^ m ∈ Kz ⊔ centralizerSection Gz Kz (pCoreOf 2 Kz) := by
  intro g hg
  set gN : ↥(Subgroup.normalizer (Kz : Set G)) := ⟨g, hGzKz hg⟩ with hgN
  obtain ⟨m, y, hy⟩ := hOut (quotConj Kz gN)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have hkN : (k : G) ∈ Subgroup.normalizer (Kz : Set G) := Subgroup.le_normalizer k.2
  set c : G := g ^ 2 ^ m * (k : G)⁻¹ with hc
  have hcN : c ∈ Subgroup.normalizer (Kz : Set G) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (hGzKz hg) _) (Subgroup.inv_mem _ hkN)
  have hcGz : c ∈ Gz :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hg _) (Subgroup.inv_mem _ (hKz k.2))
  have hq : quotConj Kz ⟨c, hcN⟩ = 1 := by
    have e : (⟨c, hcN⟩ : ↥(Subgroup.normalizer (Kz : Set G))) =
        gN ^ 2 ^ m * (⟨(k : G), hkN⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, map_pow, ← hy, quotConj_of_mem Kz _ k.2]
    exact mul_inv_cancel _
  refine ⟨m, ?_⟩
  have e : g ^ 2 ^ m = c * k := by rw [hc, inv_mul_cancel_right]
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right
    (mem_centralizerSection_of_quotConj hcGz hcN hq)) (Subgroup.mem_sup_left k.2)

omit [Finite G] in
theorem le_normalizer_of_commutator_le {K K' : Subgroup G} (h : ⁅K, K'⁆ ≤ K) :
    K' ≤ Subgroup.normalizer (K : Set G) := by
  have key : ∀ y ∈ K', ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    have h1 : k * y * k⁻¹ * y⁻¹ ∈ K := by
      have := h (Subgroup.commutator_mem_commutator hk hy)
      rwa [commutatorElement_def] at this
    have e : y * k * y⁻¹ = (k * y * k⁻¹ * y⁻¹)⁻¹ * k := by group
    rw [e]
    exact K.mul_mem (K.inv_mem h1) hk
  intro y hy
  exact B6.mem_normalizer_of_forall_mem (fun k hk => key y hy k hk)
    (fun k hk => by simpa using key y⁻¹ (K'.inv_mem hy) k hk)

omit [Finite G] in
theorem quotConj_eq_one_of_mem_of_commutator {K K' : Subgroup G} (h : ⁅K, K'⁆ ≤ pCoreOf 2 K)
    {y : G} (hy : y ∈ K') (hyN : y ∈ Subgroup.normalizer (K : Set G)) :
    quotConj K ⟨y, hyN⟩ = 1 := by
  refine quotConj_eq_one_of_commutator_mem fun k hk => ?_
  have h1 : k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
    have := h (Subgroup.commutator_mem_commutator hk hy)
    rwa [commutatorElement_def] at this
  have e : y * k * y⁻¹ * k⁻¹ = (k * y * k⁻¹ * y⁻¹)⁻¹ := by group
  change y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 K
  rw [e]
  exact inv_mem h1

omit [Finite G] in
theorem sq_mem_normalizer_of_pair {Gz K K' : Subgroup G} (hne : K ≠ K')
    (h : ∀ g ∈ Gz, (conjByElt g K = K ∨ conjByElt g K = K') ∧
      (conjByElt g K' = K ∨ conjByElt g K' = K')) {g : G} (hg : g ∈ Gz) :
    g ^ 2 ∈ Subgroup.normalizer (K : Set G) ∧ g ^ 2 ∈ Subgroup.normalizer (K' : Set G) := by
  have hsq : ∀ Y : Subgroup G, conjByElt (g ^ 2) Y = conjByElt g (conjByElt g Y) := fun Y => by
    unfold conjByElt
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc, sq]
  have hinj : Function.Injective (conjByElt g) :=
    Subgroup.map_injective (MulAut.conj g).injective
  have hN : ∀ Y : Subgroup G, conjByElt (g ^ 2) Y = Y →
      g ^ 2 ∈ Subgroup.normalizer (Y : Set G) := fun Y hY => A38.map_conj_eq_iff.mp hY
  obtain ⟨h1 | h1, h2 | h2⟩ := h g hg
  · exact absurd (hinj (h1.trans h2.symm)) hne
  · exact ⟨hN K (by rw [hsq, h1, h1]), hN K' (by rw [hsq, h2, h2])⟩
  · exact ⟨hN K (by rw [hsq, h1, h2]), hN K' (by rw [hsq, h2, h1])⟩
  · exact absurd (hinj (h1.trans h2.symm)) hne

theorem pow_mem_of_pair {Gz K K' : Subgroup G} (hKGz : K ≤ Gz) (hK'Gz : K' ≤ Gz)
    (hGzN : Gz ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G))
    (hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K ⊓ pCoreOf 2 K')
    (hOut : OutIsTwoGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hOut' : OutIsTwoGroup (↥K' ⧸ CFSG.pCore 2 ↥K'))
    (hsq : ∀ g ∈ Gz, g ^ 2 ∈ Subgroup.normalizer (K : Set G) ∧
      g ^ 2 ∈ Subgroup.normalizer (K' : Set G)) :
    ∀ g ∈ Gz, ∃ m : ℕ, g ^ 2 ^ m ∈ (K ⊔ K') ⊔
      centralizerSection Gz (K ⊔ K') (pCoreOf 2 (K ⊔ K')) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm' : ⁅K', K⁆ ≤ pCoreOf 2 K' := by
    rw [Subgroup.commutator_comm]
    exact hcomm.trans inf_le_right
  have hK'NK : K' ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_commutator_le
    (hcomm.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)))
  have hKNK' : K ≤ Subgroup.normalizer (K' : Set G) :=
    le_normalizer_of_commutator_le (hcomm'.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K'))
  have hO₁ : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ K') :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
        (hK'NK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hO₂ : pCoreOf 2 K' ≤ pCoreOf 2 (K ⊔ K') :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K').trans le_sup_right)
      (sup_le (hKNK'.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K'))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K'))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K')
  intro g hg
  obtain ⟨hgK, hgK'⟩ := hsq g hg
  set hN : ↥(Subgroup.normalizer (K : Set G)) := ⟨g ^ 2, hgK⟩ with hhN
  set hN' : ↥(Subgroup.normalizer (K' : Set G)) := ⟨g ^ 2, hgK'⟩ with hhN'
  obtain ⟨a, y₁, hy₁⟩ := hOut (quotConj K hN)
  obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective y₁
  obtain ⟨b, y₂, hy₂⟩ := hOut' (quotConj K' (hN' ^ 2 ^ a))
  obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective y₂
  have hk₁N : (k₁ : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k₁.2
  have hk₁N' : (k₁ : G) ∈ Subgroup.normalizer (K' : Set G) := hKNK' k₁.2
  have hk₂N : (k₂ : G) ∈ Subgroup.normalizer (K : Set G) := hK'NK k₂.2
  have hk₂N' : (k₂ : G) ∈ Subgroup.normalizer (K' : Set G) := Subgroup.le_normalizer k₂.2
  set w : G := ((g ^ 2) ^ 2 ^ a) ^ 2 ^ b * ((k₁ : G) ^ 2 ^ b)⁻¹ * (k₂ : G)⁻¹ with hw
  set wN : ↥(Subgroup.normalizer (K : Set G)) :=
    (hN ^ 2 ^ a) ^ 2 ^ b * (⟨(k₁ : G), hk₁N⟩ ^ 2 ^ b)⁻¹ * (⟨(k₂ : G), hk₂N⟩)⁻¹ with hwN
  set wN' : ↥(Subgroup.normalizer (K' : Set G)) :=
    (hN' ^ 2 ^ a) ^ 2 ^ b * (⟨(k₁ : G), hk₁N'⟩ ^ 2 ^ b)⁻¹ * (⟨(k₂ : G), hk₂N'⟩)⁻¹ with hwN'
  have hwv : (wN : G) = w := rfl
  have hwv' : (wN' : G) = w := rfl
  have hq₁ : quotConj K wN = 1 := by
    rw [hwN, map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, map_pow, ← hy₁,
      quotConj_of_mem K _ k₁.2,
      quotConj_eq_one_of_mem_of_commutator (hcomm.trans inf_le_left) k₂.2 hk₂N]
    simp
  have hq₂ : quotConj K' wN' = 1 := by
    have hc₁ : quotConj K' ⟨(k₁ : G), hk₁N'⟩ = 1 :=
      quotConj_eq_one_of_mem_of_commutator hcomm' k₁.2 hk₁N'
    rw [hwN', map_mul, map_mul, map_inv, map_inv, map_pow, ← hy₂, map_pow, hc₁,
      quotConj_of_mem K' _ k₂.2]
    simp
  have hwGz : w ∈ Gz := Gz.mul_mem (Gz.mul_mem (Gz.pow_mem (Gz.pow_mem (Gz.pow_mem hg _) _) _)
    (Gz.inv_mem (Gz.pow_mem (hKGz k₁.2) _))) (Gz.inv_mem (hK'Gz k₂.2))
  have hwC : w ∈ centralizerSection Gz (K ⊔ K') (pCoreOf 2 (K ⊔ K')) := by
    refine ⟨hwGz, hGzN hwGz,
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hGzN hwGz), fun x hx => ?_⟩
    have h1 := Ch838.commutator_mem_of_sup (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (fun d hd => hO₁ (hwv ▸ Ch838.commutator_mem_of_quotConj_eq_one hq₁ d hd))
      (fun d hd => hO₂ (hwv' ▸ Ch838.commutator_mem_of_quotConj_eq_one hq₂ d hd)) x hx
    have e : x * w * x⁻¹ * w⁻¹ = (w * x * w⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  refine ⟨a + b + 1, ?_⟩
  have e : g ^ 2 ^ (a + b + 1) = w * ((k₂ : G) * (k₁ : G) ^ 2 ^ b) := by
    have e1 : ((g ^ 2) ^ 2 ^ a) ^ 2 ^ b = g ^ 2 ^ (a + b + 1) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [hw, ← e1]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hwC) (Subgroup.mem_sup_left
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right k₂.2) (Subgroup.pow_mem _
      (Subgroup.mem_sup_left k₁.2) _)))

end Ch837

end CFSG.Quasithin.H13
