module

public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenLocalCoreCommutator
public import CFSG.RankThree.Chevalley.SteinbergBMG2NoninnerLocalCore

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups

namespace EvenG2

theorem localCore_eq_bot_of_noninner {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) {B : Subgroup (MulAut (adjointGroup .G2 K))}
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B) {b : B}
    (hbinn : (b : MulAut (adjointGroup .G2 K)) ∉
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range)
    (hbp : orderOf b = p) :
    inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set B)) = ⊥ := by
  have hNF := conj_normalForm_of_pointwise (even_G2_exact_automorphism_normal_form hf K hK).1
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF b
  have hcore := (even_G2_noninner_prime_local_core_trivial hf hK hp B hB b hbinn hbp x σ
    hxσ).2.2.2
  rw [inSubgroup, hcore, Subgroup.map_bot]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem derived_centralizer_root_data_of_charTwo {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K - 1) {u g : adjointGroup .G2 K} {c : Fin Tag.G2.rank → Kˣ}
    (hu : ((g * u * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 c)
    (hcp : c ^ p = 1) (hc1 : c ≠ 1) (i : Fin Tag.G2.rank) (hci : c i = 1) :
    (⁅centralizer ({u} : Set (adjointGroup .G2 K)), centralizer ({u} : Set (adjointGroup .G2 K))⁆ :
        Subgroup (adjointGroup .G2 K)).map
        ((adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom) =
      rootSubgroup .G2 K (Pi.single i 1) ⊔ rootSubgroup .G2 K (-Pi.single i 1) ∧
    CFSG.IsQuasisimple (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
      centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hq6 := six_le_card_of_dvd hp hp3 hpq
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1
  have hao : orderOf (rootDiagUnit .G2 c) = p := by rw [orderOf_rootDiagUnit, hco]
  have hiker : (Pi.single i 1 : Fin Tag.G2.rank → ℤ) ∈ rootCharKernel c :=
    ⟨isRoot_single .G2 i, by rw [rootChar_pi_single, hci]⟩
  rcases toral_centralizer_cases_G2_of_charTwo K hp hp3 hpq c hao with ⟨hker, -⟩ |
    ⟨α, hα, hkerα, -, -, hcomm, hZ, hZH⟩
  · rw [hker] at hiker
    exact absurd hiker (Set.notMem_empty _)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfin⟩ := even_Chevalley_pinned_root_SL2_maps .G2 K hα
  obtain ⟨hsimple, -, hnonab⟩ := hfin inferInstance (by omega)
  have := hsimple
  have hQq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
  obtain ⟨hRmap, hRq, -⟩ := derived_centralizer_data hu hcomm hQq hZ hZH
  refine ⟨hRmap.trans ?_, hRq⟩
  rw [hkerα] at hiker
  rcases hiker with h | h
  · rw [h]
  · rw [show α = -Pi.single i 1 by rw [h, neg_neg], neg_neg, sup_comm]

theorem thetaT_eq_bot_split_of_charTwo {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K - 1) {B : Subgroup (MulAut (adjointGroup .G2 K))}
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    {E : Subgroup B} {P : Subgroup (adjointGroup .G2 K)}
    (hPE : ∀ u ∈ P, (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ∈ E) (hPcard : Nat.card P = p ^ 2)
    (hPpow : ∀ u ∈ P, u ^ p = 1) :
    thetaT p E = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hPp : IsPGroup p P := IsPGroup.of_card hPcard
  obtain ⟨g, hg⟩ :=
    exists_conj_map_le_of_not_dvd_index (not_dvd_index_torusGroup_G2 hp hp3 hpq) hPp
  set F := (adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom with hFdef
  have hF : Function.Injective F := Subtype.val_injective.comp (MulAut.conj g).injective
  have hPH : P.map F = torusTorsion K p := by
    have : NeZero p := ⟨hp.ne_zero⟩
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      rw [mem_torusTorsion_iff]
      refine ⟨hg ⟨u, hu, rfl⟩, ?_⟩
      rw [← map_pow, hPpow u hu, map_one]
    · rw [natCard_torusTorsion hpq, Subgroup.card_map_of_injective hF, hPcard]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hpq)
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have key : ∀ i : Fin Tag.G2.rank, ∃ u ∈ P, u ≠ 1 ∧
      (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
          centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)).map F =
        rootSubgroup .G2 K (Pi.single i 1) ⊔ rootSubgroup .G2 K (-Pi.single i 1) ∧
      CFSG.IsQuasisimple (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
        centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) := by
    intro i
    obtain ⟨j, hji⟩ : ∃ j : Fin Tag.G2.rank, j ≠ i := by
      rcases fin_G2_cases i with rfl | rfl
      · exact ⟨g2ir, by decide⟩
      · exact ⟨g2ia, by decide⟩
    set c : Fin Tag.G2.rank → Kˣ := fun k => if k = i then 1 else ζ with hc
    have hcp : c ^ p = 1 := funext fun k => by
      by_cases hk : k = i <;> simp [hc, hk, hζp]
    have hc1 : c ≠ 1 := fun h => hζ1 (by simpa [hc, hji] using congrFun h j)
    have hci : c i = 1 := by simp [hc]
    have hdc : rootDiagUnit .G2 c ∈ P.map F := by
      rw [hPH]
      exact (rootDiagUnit_mem_torusTorsion_iff p c).2 hcp
    obtain ⟨u, hu, hdu⟩ := hdc
    have hu1 : u ≠ 1 := fun h => hc1 (rootDiagUnit_injective (by
      rw [← hdu, h, map_one, rootDiagUnit_one]))
    obtain ⟨hRmap, hRq⟩ := derived_centralizer_root_data_of_charTwo hp hp3 hpq hdu hcp hc1 i hci
    exact ⟨u, hu, hu1, hRmap, hRq⟩
  obtain ⟨u₁, hu₁, hu₁1, hR₁, hq₁⟩ := key g2ia
  obtain ⟨u₂, hu₂, hu₂1, hR₂, hq₂⟩ := key g2ir
  have htop : (⁅centralizer ({u₁} : Set (adjointGroup .G2 K)),
        centralizer ({u₁} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ⊔
      ⁅centralizer ({u₂} : Set (adjointGroup .G2 K)),
        centralizer ({u₂} : Set (adjointGroup .G2 K))⁆ = ⊤ := by
    apply Subgroup.map_injective hF
    rw [Subgroup.map_sup, hR₁, hR₂, rootSubgroup_simple_sup_eq_adjointGroup]
    ext z
    refine ⟨fun hz => ⟨g⁻¹ * (⟨z, hz⟩ : adjointGroup .G2 K) * g, Subgroup.mem_top _, ?_⟩, ?_⟩
    · change ((g * (g⁻¹ * (⟨z, hz⟩ : adjointGroup .G2 K) * g) * g⁻¹ : adjointGroup .G2 K) :
        ModGL .G2 K) = z
      rw [show g * (g⁻¹ * (⟨z, hz⟩ : adjointGroup .G2 K) * g) * g⁻¹ =
        (⟨z, hz⟩ : adjointGroup .G2 K) by group]
    · rintro ⟨y, -, rfl⟩
      exact ((MulAut.conj g) y).2
  have hb1 : ∀ u : adjointGroup .G2 K, u ≠ 1 → (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ≠ 1 :=
    fun u hu h => hu (hinj (congrArg Subtype.val h))
  have hRY : ∀ u : adjointGroup .G2 K, (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
      centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ≤
      centralizer ({u} : Set (adjointGroup .G2 K)) := fun u =>
    Subgroup.commutator_le.2 fun v hv w hw => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hv hw) (inv_mem hv)) (inv_mem hw)
  have hfix₁ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₁ (hRY u₁)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₁
  have hfix₂ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₂ (hRY u₂)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₂
  rw [eq_bot_iff]
  intro s hs
  have hmem : ∀ a ∈ E, a ≠ 1 → s ∈ inSubgroup (aschbacherSolvableCore p)
      (centralizer ({a} : Set B)) := by
    simp only [thetaT, Subgroup.mem_iInf] at hs
    exact hs
  have hs₁ := hmem _ (hPE u₁ hu₁) (hb1 u₁ hu₁1)
  have hs₂ := hmem _ (hPE u₂ hu₂) (hb1 u₂ hu₂1)
  have hle : (⁅centralizer ({u₁} : Set (adjointGroup .G2 K)),
        centralizer ({u₁} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ⊔
      ⁅centralizer ({u₂} : Set (adjointGroup .G2 K)),
        centralizer ({u₂} : Set (adjointGroup .G2 K))⁆ ≤
      MonoidHom.eqLocus (s : MulAut (adjointGroup .G2 K)).toMonoidHom (MonoidHom.id _) :=
    sup_le (fun r hr => hfix₁ s hs₁ r hr) (fun r hr => hfix₂ s hs₂ r hr)
  rw [htop] at hle
  rw [Subgroup.mem_bot]
  exact Subtype.ext (MulEquiv.ext fun y => hle (Subgroup.mem_top y))

omit [Finite K] [CharP K 2] in
theorem mem_torusGroup_or_monomial_neg_of_conj_eq_pow {L : Type} [Field L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card L - 1) {v : ModGL .G2 L}
    (hv : v ∈ adjointGroup .G2 L) {m : ℕ} (hm : m.Coprime p)
    (hvV : ∀ x ∈ torusTorsion L p, v * x * v⁻¹ = x ^ m) :
    v ∈ torusGroup .G2 L ∨ ∃ hv : v ∈ monomialSubgroup .G2 L,
      ∀ w : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 L ⟨v, hv⟩ • w = -w := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, hVnorm, -, -, hVscal, -⟩ :=
    G2_toral_prime_plane_centralizer_and_scalar_normalizers L hp hp3 hpq
  have hpow : ∀ x ∈ torusTorsion L p, ∀ n : ℕ, x ^ n = x ^ (n % p) := fun x hx n => by
    have hxp : x ^ p = 1 := (mem_torusTorsion_iff.1 hx).2
    conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hxp, one_pow, one_mul]
  have hvN : v ∈ Subgroup.normalizer (torusTorsion L p : Set (ModGL .G2 L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hvV y hy]
      exact pow_mem hy m
    · intro hy
      obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hp.one_lt
      have hg := hvV _ (pow_mem hy m')
      have e : ((v * y * v⁻¹) ^ m') ^ m = v * y * v⁻¹ := by
        rw [← pow_mul, mul_comm m' m, hpow _ hy, hm', pow_one]
      rw [e] at hg
      have hy' : (v * y * v⁻¹) ^ m' = y :=
        calc (v * y * v⁻¹) ^ m' = v⁻¹ * (v * (v * y * v⁻¹) ^ m' * v⁻¹) * v := by group
          _ = v⁻¹ * (v * y * v⁻¹) * v := by rw [hg]
          _ = y := by group
      rw [← hy']
      exact pow_mem hy m'
  obtain ⟨h, hh, w, rfl⟩ := hVnorm v ⟨hv, hvN⟩
  have hscal : ∀ x ∈ torusTorsion L p, h * canonicalRep (coxeterSystem .G2) L w * x *
      (h * canonicalRep (coxeterSystem .G2) L w)⁻¹ = x ^ (m : ZMod p).val := fun x hx => by
    rw [hvV x hx, ZMod.val_natCast, ← hpow x hx]
  rcases hVscal h hh w _ hscal with ⟨rfl, -⟩ | ⟨hw, -⟩
  · left
    rw [canonicalRep_one, mul_one]
    exact hh
  · right
    have hN : h * canonicalRep (coxeterSystem .G2) L w ∈ monomialSubgroup .G2 L :=
      mul_mem (Subgroup.mem_sup_left hh) (canonicalRep_mem_monomialSubgroup L w)
    refine ⟨hN, fun u => ?_⟩
    have hπ : weylQuotientHom .G2 L ⟨h * canonicalRep (coxeterSystem .G2) L w, hN⟩ = w :=
      weylQuotientHom_eq (by
        simpa using (mapsRootLines_of_mem_torusGroup hh).mul (mapsRootLines_canonicalRep w))
    rw [hπ]
    exact hw u

omit [Finite K] [CharP K 2] in
theorem thetaT_eq_bot_qplus_of_charTwo {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1) (K₂ : Type) [Field K₂]
    [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {B : Subgroup (MulAut (adjointGroup .G2 K))}
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    {E : Subgroup B} {P : Subgroup (adjointGroup .G2 K)}
    (hPE : ∀ u ∈ P, (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ∈ E) (hPcard : Nat.card P = p ^ 2)
    (hPpow : ∀ u ∈ P, u ^ p = 1) :
    thetaT p E = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Fact p.Prime := ⟨hp⟩
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hNF0 := (even_G2_exact_automorphism_normal_form hf K hK).1
  have hPp : IsPGroup p P := IsPGroup.of_card hPcard
  have : Module.Finite K K₂ := Module.finite_of_finrank_pos (by omega)
  have : Finite K₂ := Module.finite_of_finite K
  have : CharP K₂ 2 := charP_of_injective_algebraMap (algebraMap K K₂).injective 2
  have hq2 : Nat.card K₂ = Nat.card K ^ 2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpq₂ : p ∣ Nat.card K₂ - 1 := by
    refine hpq.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  obtain ⟨g, z, hg, -, hzdef, ⟨hzN, hw⟩, hΓfix, -, -, -, ⟨S₀, hS₀T⟩, ⟨V, hV, -, hVcard, -, -⟩,
    hroot, -, hcases⟩ :=
    even_G2_qplus_torus_and_fixed_root_centralizers K hp hp3 hpq K₂ hdeg σ hσ
  have hVt : V = torusTorsion K₂ p :=
    Subgroup.ext fun h => (hV h).trans mem_torusTorsion_iff.symm
  set ψ : ModGL .G2 K →* ModGL .G2 K₂ :=
    (MulAut.conj g).toMonoidHom.comp (baseChangeGL (algebraMap K K₂)) with hψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp (baseChangeGL_injective (τ := .G2) (algebraMap K K₂))
  let ε : adjointGroup .G2 K ≃* conjEntrywiseImage K g :=
    (adjointGroup .G2 K).equivMapOfInjective ψ hψinj
  obtain ⟨u, hu⟩ : ∃ u : conjEntrywiseImage K g,
      (P.map ε.toMonoidHom).map (MulAut.conj u).toMonoidHom ≤ S₀ := by
    obtain ⟨Q', hQ'⟩ := (hPp.map ε.toMonoidHom).exists_le_sylow
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq (conjEntrywiseImage K g) Q' S₀
    refine ⟨u, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 : MulAut.conj u • y ∈ MulAut.conj u • (Q' : Subgroup (conjEntrywiseImage K g)) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hQ' hy)
    rwa [← Sylow.coe_subgroup_smul, hu] at h1
  set F : adjointGroup .G2 K →* ModGL .G2 K₂ := (conjEntrywiseImage K g).subtype.comp
    ((MulAut.conj u).toMonoidHom.comp ε.toMonoidHom) with hFdef
  have hF : Function.Injective F := (conjEntrywiseImage K g).subtype_injective.comp
    ((MulAut.conj u).injective.comp ε.injective)
  have hFrange : F.range = conjEntrywiseImage K g := by
    rw [hFdef, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _
      ((MulAut.conj u).surjective.comp ε.surjective), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hFapp : ∀ h : adjointGroup .G2 K, F h = (u : ModGL .G2 K₂) *
      (g * baseChangeGL (algebraMap K K₂) (h : ModGL .G2 K) * g⁻¹) * (u : ModGL .G2 K₂)⁻¹ :=
    fun h => rfl
  have hFP : P.map F = torusTorsion K₂ p := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_torusTorsion_iff]
      refine ⟨(Subgroup.mem_subgroupOf.1 (hS₀T (hu ⟨ε y, ⟨y, hy, rfl⟩, rfl⟩))).1, ?_⟩
      rw [← map_pow, hPpow y hy, map_one]
    · rw [← hVt, hVcard, Subgroup.card_map_of_injective hF, hPcard]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := K₂ˣ) p
    (by rw [Nat.card_units]; exact hpq₂)
  have hζ1 : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have key : ∀ i : Fin Tag.G2.rank, ∃ ui ∈ P, ui ≠ 1 ∧ ∃ α : Fin Tag.G2.rank → ℤ,
      IsRoot .G2 α ∧ (α = Pi.single i 1 ∨ α = -Pi.single i 1) ∧
      (⁅centralizer ({ui} : Set (adjointGroup .G2 K)),
          centralizer ({ui} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)).map F =
        rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g ∧
      CFSG.IsQuasisimple (⁅centralizer ({ui} : Set (adjointGroup .G2 K)),
        centralizer ({ui} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ∧
      ∀ y ∈ centralizer ({ui} : Set (adjointGroup .G2 K)),
        (∀ r ∈ (⁅centralizer ({ui} : Set (adjointGroup .G2 K)),
          centralizer ({ui} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)),
            y * r = r * y) → F y ∈ torusGroup .G2 K₂ := by
    intro i
    obtain ⟨j, hji⟩ : ∃ j : Fin Tag.G2.rank, j ≠ i := by
      rcases fin_G2_cases i with rfl | rfl
      · exact ⟨g2ir, by decide⟩
      · exact ⟨g2ia, by decide⟩
    set c : Fin Tag.G2.rank → K₂ˣ := fun k => if k = i then 1 else ζ with hc
    have hcp : c ^ p = 1 := funext fun k => by
      by_cases hk : k = i <;> simp [hc, hk, hζp]
    have hc1 : c ≠ 1 := fun h => hζ1 (by simpa [hc, hji] using congrFun h j)
    have hci : c i = 1 := by simp [hc]
    have hdc : rootDiagUnit .G2 c ∈ P.map F := by
      rw [hFP]
      exact (rootDiagUnit_mem_torusTorsion_iff p c).2 hcp
    obtain ⟨ui, hui, hdu⟩ := hdc
    have hui1 : ui ≠ 1 := fun h => hc1 (rootDiagUnit_injective (by
      rw [← hdu, h, map_one, rootDiagUnit_one]))
    have hTc : rootDiagUnit .G2 c ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g :=
      ⟨rootDiagUnit_mem_torusGroup_G2 c, hFrange ▸ ⟨ui, hdu⟩⟩
    have hco : orderOf c = p := orderOf_eq_prime hcp hc1
    have hao : orderOf (rootDiagUnit .G2 c) = p := by rw [orderOf_rootDiagUnit, hco]
    have hiker : (Pi.single i 1 : Fin Tag.G2.rank → ℤ) ∈ rootCharKernel c :=
      ⟨isRoot_single .G2 i, by rw [rootChar_pi_single, hci]⟩
    have hne : rootCharKernel c ≠ ∅ := fun h => by
      rw [h] at hiker
      exact Set.notMem_empty _ hiker
    obtain ⟨α, hα, hkerα, hcomm, hZ, hZH⟩ := (hcases c hTc hao).2.1 hne
    obtain ⟨_, -, hsimple, -, hnonab⟩ := hroot α hα
    have := hsimple
    have hQq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
    have hmapF : (centralizer ({ui} : Set (adjointGroup .G2 K))).map F =
        conjEntrywiseImage K g ⊓ centralizer {rootDiagUnit .G2 c} := by
      rw [SteinbergBN.map_centralizer_singleton_of_injective F hF ui, hFrange, hdu]
    obtain ⟨hRmap, hRq, -⟩ :=
      SteinbergBN.derived_centralizer_data_of_map F hF hmapF hcomm hQq hZ hZH
    refine ⟨ui, hui, hui1, α, hα, ?_, hRmap, hRq, fun y hy hyR => ?_⟩
    · rw [hkerα] at hiker
      rcases hiker with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by rw [show (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = -α from h, neg_neg])
    · refine hZH (hZ ▸ Subgroup.mem_inf.2 ⟨hmapF ▸ ⟨y, hy, rfl⟩,
        Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩)
      rw [← hRmap] at hw
      obtain ⟨r, hr, rfl⟩ := hw
      rw [← map_mul, ← map_mul, hyR r hr]
  obtain ⟨u₁, hu₁, hu₁1, α₁, hα₁, hα₁e, hR₁, hq₁, hZ₁⟩ := key g2ia
  obtain ⟨u₂, hu₂, hu₂1, α₂, hα₂, hα₂e, hR₂, hq₂, hZ₂⟩ := key g2ir
  have hb1 : ∀ u : adjointGroup .G2 K, u ≠ 1 → (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ≠ 1 :=
    fun u hu h => hu (hinj (congrArg Subtype.val h))
  have hRY : ∀ u : adjointGroup .G2 K, (⁅centralizer ({u} : Set (adjointGroup .G2 K)),
      centralizer ({u} : Set (adjointGroup .G2 K))⁆ : Subgroup (adjointGroup .G2 K)) ≤
      centralizer ({u} : Set (adjointGroup .G2 K)) := fun u =>
    Subgroup.commutator_le.2 fun v hv w hw => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hv hw) (inv_mem hv)) (inv_mem hw)
  have hfix₁ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₁ (hRY u₁)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₁
  have hfix₂ := aschbacherSolvableCore_fixes_quasisimple hinj hp hB u₂ (hRY u₂)
    (fun η hη r hr => apply_mem_commutator_centralizer_of_apply_eq hη hr) hq₂
  rw [eq_bot_iff]
  intro s hs
  have hmem : ∀ a ∈ E, a ≠ 1 → s ∈ inSubgroup (aschbacherSolvableCore p)
      (centralizer ({a} : Set B)) := by
    simp only [thetaT, Subgroup.mem_iInf] at hs
    exact hs
  have hsR₁ := hfix₁ s (hmem _ (hPE u₁ hu₁) (hb1 u₁ hu₁1))
  have hsR₂ := hfix₂ s (hmem _ (hPE u₂ hu₂) (hb1 u₂ hu₂1))
  have hsP : ∀ u' ∈ P, (s : MulAut (adjointGroup .G2 K)) u' = u' := by
    intro u' hu'
    by_cases h1 : u' = 1
    · rw [h1, map_one]
    · have hsC := Subgroup.map_subtype_le _ (hmem _ (hPE u' hu') (hb1 u' h1))
      exact apply_eq_of_commute_conj hinj
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hsC))
  obtain ⟨⟨y, σ'⟩, hyσ, -⟩ := hNF0 (s : MulAut (adjointGroup .G2 K))
  obtain ⟨j, hj⟩ := SteinbergBN.exists_eq_pow_prime_pow Nat.prime_two (by omega) hK σ'
  have hK₂card : Nat.card K₂ = 2 ^ (2 * f) := by rw [hq2, hK, ← pow_mul, mul_comm]
  obtain ⟨σ₂, hσ₂⟩ :=
    SteinbergBN.exists_ringEquiv_eq_pow_prime_pow Nat.prime_two (by omega : 1 ≤ 2 * f) hK₂card j
  have hcomm₂ : ∀ c, σ₂ (algebraMap K K₂ c) = algebraMap K K₂ (σ' c) := fun c => by
    rw [hσ₂, hj, map_pow]
  have huC : (u : ModGL .G2 K₂) ∈ adjointGroup .G2 K₂ := (hΓfix.le u.2).1
  obtain ⟨v, hvdef⟩ : ∃ v : ModGL .G2 K₂, v = (u : ModGL .G2 K₂) * g *
      baseChangeGL (algebraMap K K₂) (y : ModGL .G2 K) *
      (Units.map (entrywiseHom (σ₂ : K₂ →+* K₂)) g)⁻¹ *
      (Units.map (entrywiseHom (σ₂ : K₂ →+* K₂)) (u : ModGL .G2 K₂))⁻¹ := ⟨_, rfl⟩
  have hvC : v ∈ adjointGroup .G2 K₂ := by
    rw [hvdef]
    exact mul_mem (mul_mem (mul_mem (mul_mem huC hg) (baseChangeGL_mem_adjointGroup _ y.2))
      (inv_mem (SteinbergBN.units_map_entrywiseHom_mem_adjointGroup _ hg)))
      (inv_mem (SteinbergBN.units_map_entrywiseHom_mem_adjointGroup _ huC))
  have hFs : ∀ h : adjointGroup .G2 K, F ((s : MulAut (adjointGroup .G2 K)) h) =
      twistedEntrywise v (σ₂ : K₂ →+* K₂) (F h) := by
    intro h
    rw [hFapp, hFapp, hyσ h, map_mul, map_mul, map_inv,
      SteinbergBN.baseChangeGL_entrywise_comm σ' σ₂ hcomm₂, twistedEntrywise_apply, hvdef]
    simp only [map_mul, map_inv]
    group
  have hvV : ∀ x ∈ torusTorsion K₂ p, v⁻¹ * x * v⁻¹⁻¹ = x ^ (2 ^ j) := by
    intro x hx
    rw [← hFP] at hx
    obtain ⟨u', hu', rfl⟩ := hx
    have hxH : F u' ∈ torusGroup .G2 K₂ :=
      (mem_torusTorsion_iff.1 (hFP ▸ Subgroup.mem_map_of_mem F hu')).1
    obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxH
    have h1 := hFs u'
    rw [hsP u' hu', twistedEntrywise_apply, hc,
      entrywise_frob_rootDiagUnit (σ₂ : K₂ →+* K₂) hσ₂ c] at h1
    have h2 : rootDiagUnit .G2 (c ^ 2 ^ j) = rootDiagUnit .G2 c ^ 2 ^ j :=
      map_pow (rootDiagUnitHom .G2 K₂) c _
    rw [hc, ← h2]
    calc v⁻¹ * rootDiagUnit .G2 c * v⁻¹⁻¹ =
        v⁻¹ * (v * rootDiagUnit .G2 (c ^ 2 ^ j) * v⁻¹) * v := by rw [← h1, inv_inv]
      _ = rootDiagUnit .G2 (c ^ 2 ^ j) := by group
  have hm : (2 ^ j).Coprime p :=
    Nat.Coprime.pow_left j ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin 2) K₂, ∀ A, rootSL2 .G2 K₂ α₁ (semilinearConj M σ₂ A) =
      twistedEntrywise v (σ₂ : K₂ →+* K₂) (rootSL2 .G2 K₂ α₁ A) := by
    rcases mem_torusGroup_or_monomial_neg_of_conj_eq_pow hp hp3 hpq₂ (inv_mem hvC) hm hvV with
      hvH | ⟨hvN, hvw⟩
    · have hvH' : v ∈ torusGroup .G2 K₂ := by simpa using inv_mem hvH
      obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hvH'
      refine ⟨diagUnitOne (rootChar c α₁), fun A => ?_⟩
      rw [twistedEntrywise_apply, entrywise_rootSL2_of_field, hc, rootDiagUnit_conj_rootSL2 c hα₁]
      rfl
    · have hvN' : v ∈ monomialSubgroup .G2 K₂ := by simpa using inv_mem hvN
      have hvw' : ∀ w : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨v, hvN'⟩ • w = -w := by
        intro w
        have e : (⟨v, hvN'⟩ : monomialSubgroup .G2 K₂) = (⟨v⁻¹, hvN⟩)⁻¹ :=
          Subtype.ext (by simp)
        have h1 := hvw (-w)
        rw [neg_neg] at h1
        rw [e, map_inv]
        calc (weylQuotientHom .G2 K₂ ⟨v⁻¹, hvN⟩)⁻¹ • w =
            (weylQuotientHom .G2 K₂ ⟨v⁻¹, hvN⟩)⁻¹ • (weylQuotientHom .G2 K₂ ⟨v⁻¹, hvN⟩ • -w) := by
              rw [h1]
          _ = -w := inv_smul_smul _ _
      exact exists_semilinearConj_rootSL2 hvN' hvw' σ₂ hα₁
  obtain ⟨P₁, hP₁, -⟩ := hroot α₁ hα₁
  have hfixK : ∀ c : K, σ₂ (algebraMap K K₂ c) = algebraMap K K₂ c := by
    intro c
    obtain ⟨X, hX, htr⟩ := SteinbergBN.exists_trace_eq_algebraMap P₁ c
    rw [← hP₁, Subgroup.mem_comap, ← hR₁] at hX
    obtain ⟨r, hr, hrX⟩ := hX
    have h1 : twistedEntrywise v (σ₂ : K₂ →+* K₂) (rootSL2 .G2 K₂ α₁ X) =
        rootSL2 .G2 K₂ α₁ X := by
      rw [← hrX, ← hFs r, hsR₁ r hr]
    have h2 : semilinearConj M σ₂ X = X := rootSL2_injective_of_field α₁ (by rw [hM, h1])
    have h3 := congrArg (fun Y : SL(2, K₂) => Matrix.trace (Y : Matrix (Fin 2) (Fin 2) K₂)) h2
    rwa [SteinbergBN.trace_semilinearConj, htr] at h3
  have hσ'1 : σ' = 1 := RingEquiv.ext fun c => (algebraMap K K₂).injective (by
    rw [← hcomm₂, hfixK]
    rfl)
  have hsy : ∀ h : adjointGroup .G2 K, (s : MulAut (adjointGroup .G2 K)) h = y * h * y⁻¹ := by
    intro h
    apply Subtype.ext
    rw [hyσ h, hσ'1]
    have e : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL .G2 K) = h :=
      Units.ext (entrywise_id _)
    rw [e]
    rfl
  have hcommy : ∀ r : adjointGroup .G2 K, (s : MulAut (adjointGroup .G2 K)) r = r →
      y * r = r * y := fun r hr => by
    rw [hsy] at hr
    calc y * r = y * r * y⁻¹ * y := by group
      _ = r * y := by rw [hr]
  have hyu₁ : y ∈ centralizer ({u₁} : Set (adjointGroup .G2 K)) :=
    mem_centralizer_singleton_iff.2 (hcommy u₁ (hsP u₁ hu₁))
  have hFyH : F y ∈ torusGroup .G2 K₂ := hZ₁ y hyu₁ fun r hr => hcommy r (hsR₁ r hr)
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hFyH
  have hχ : ∀ (α : Fin Tag.G2.rank → ℤ), IsRoot .G2 α → ∀ R' : Subgroup (adjointGroup .G2 K),
      R'.map F = rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g →
      (∀ r ∈ R', (s : MulAut (adjointGroup .G2 K)) r = r) → rootChar c α = 1 := by
    intro α hα R' hR' hsR'
    obtain ⟨_, -, hcent⟩ := rootSL2_comap_fixed_eq_of_charTwo hdeg σ hσ hg hzdef hzN hw hα
    have hcomm := commute_rootSL2_of_commute_fixed hα hcent (y := F y)
      ⟨F y, hFyH, 1, one_mem _, mul_one _⟩ (fun A hA => by
        rw [Subgroup.mem_comap, ← hR'] at hA
        obtain ⟨r, hr, hrA⟩ := hA
        rw [← hrA, ← map_mul, ← map_mul, hcommy r (hsR' r hr)]) (uSL 1)
    have h1 : rootSL2 .G2 K₂ α (conjSL (diagUnitOne (rootChar c α)) (uSL 1)) =
        rootSL2 .G2 K₂ α (uSL 1) := by
      rw [← rootDiagUnit_conj_rootSL2 c hα, ← hc, hcomm, mul_inv_cancel_right]
    have h2 : sl2Upper K₂ ((rootChar c α : K₂) * 1) = sl2Upper K₂ 1 := by
      rw [← conjSL_sl2Upper]
      exact rootSL2_injective_of_field α h1
    have h3 := congrArg (fun Y : SL(2, K₂) => (Y : Matrix (Fin 2) (Fin 2) K₂) 0 1) h2
    simp [sl2Upper] at h3
    exact h3
  have hci : ∀ (i : Fin Tag.G2.rank) (α : Fin Tag.G2.rank → ℤ),
      (α = Pi.single i 1 ∨ α = -Pi.single i 1) → rootChar c α = 1 → c i = 1 := by
    intro i α hαe hcα
    rw [← rootChar_pi_single c i]
    rcases hαe with rfl | rfl
    · exact hcα
    · rw [rootChar_neg'] at hcα
      exact inv_eq_one.mp hcα
  have hc1 : c = 1 := funext fun i => by
    rcases fin_G2_cases i with rfl | rfl
    · exact hci _ _ hα₁e (hχ α₁ hα₁ _ hR₁ hsR₁)
    · exact hci _ _ hα₂e (hχ α₂ hα₂ _ hR₂ hsR₂)
  have hy1 : y = 1 := hF (by rw [hc, hc1, rootDiagUnit_one, map_one])
  rw [Subgroup.mem_bot]
  exact Subtype.ext (MulEquiv.ext fun h => by rw [hsy h, hy1, one_mul, inv_one, mul_one]; rfl)

theorem false_of_cyclotomic_plane_of_charTwo {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {ε : ℤ}
    (hε : ε = -1 ∨ ε = 1) {d : ℕ} (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1)
    (hpd : p ∣ d) {P : Subgroup (adjointGroup .G2 K)} (hPcard : Nat.card P = p ^ 2)
    (hPpow : ∀ u ∈ P, u ^ p = 1) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, -, -, -, hcyc, -⟩ :=
    even_G2_cyclotomic_three_six_tori_and_prime_centralizers K ε hε d hd hp hp3 hpd
  have := hcyc P (IsPGroup.of_card hPcard)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hPpow g g.2))
  rw [hg, hPcard] at h1
  have := Nat.le_of_dvd hp.pos h1
  nlinarith [hp.two_le]

end EvenG2

open EvenG2

theorem even_G2_thetaT_eq_bot {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (B : Subgroup (MulAut (adjointGroup .G2 K)))
    (hB : (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ≤ B)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    thetaT p E = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hE
  set R := (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range with hR
  have hinj :
      Function.Injective (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hEpow : ∀ a ∈ E, a ^ p = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p E) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  by_cases hEinn : E.map B.subtype ≤ R
  swap
  ·
    obtain ⟨b, hbE, hbinn⟩ : ∃ b ∈ E, (b : MulAut (adjointGroup .G2 K)) ∉ R := by
      by_contra h
      push Not at h
      exact hEinn (by rintro _ ⟨b, hb, rfl⟩; exact h b hb)
    have hb1 : b ≠ 1 := fun h => hbinn (by rw [h]; exact one_mem _)
    have hbp : orderOf b = p := orderOf_eq_prime (hEpow b hbE) hb1
    refine eq_bot_iff.2 (iInf_le_of_le b (iInf_le_of_le hbE (iInf_le_of_le hb1 ?_)))
    rw [localCore_eq_bot_of_noninner hf hK hp hB hbinn hbp]
  set P : Subgroup (adjointGroup .G2 K) := (E.map B.subtype).comap MulAut.conj with hPdef
  have hPmap : P.map MulAut.conj = E.map B.subtype := Subgroup.map_comap_eq_self hEinn
  have eP : E ≃* P := (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective).trans
    ((MulEquiv.subgroupCongr hPmap.symm).trans (Subgroup.equivMapOfInjective P _ hinj).symm)
  have hPcard : Nat.card P = p ^ 2 := by rw [← Nat.card_congr eP.toEquiv, hEcard]
  have hPpow : ∀ u ∈ P, u ^ p = 1 := fun u hu => by
    obtain ⟨e, he, hee⟩ := hu
    apply hinj
    rw [map_pow, ← hee, map_one]
    exact congrArg Subtype.val (hEpow e he)
  have hPE : ∀ u ∈ P, (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) ∈ E := fun u hu => by
    obtain ⟨e, he, hee⟩ := hu
    rwa [show (⟨MulAut.conj u, hB ⟨u, rfl⟩⟩ : B) = e from Subtype.ext hee.symm]
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
  have hpC : p ∣ CFSG.Open.ordG2 (Nat.card K) := by
    rw [← card_adjointGroup_G2]
    exact (dvd_pow_self p two_ne_zero).trans (hPcard ▸ Subgroup.card_subgroup_dvd_card P)
  have hp2 : ¬ p ∣ Nat.card K := fun h => by
    rw [hK] at h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
    omega
  rcases dvd_cases_of_dvd_ordG2 hq1 hp hpC hp2 with h | h | h | h
  · exact thetaT_eq_bot_split_of_charTwo hp hp3 h hB hPE hPcard hPpow
  · exact thetaT_eq_bot_qplus_of_charTwo hf hK hp hp3 h (FiniteField.Extension K 2 2)
      (FiniteField.finrank_extension K 2 2) (FiniteField.Extension.frob K 2 2).toRingEquiv
      (fun c => FiniteField.Extension.frob_apply K 2 2 (x := c)) hB hPE hPcard hPpow
  · exact (false_of_cyclotomic_plane_of_charTwo hp hp3 (Or.inr rfl)
      (d := Nat.card K ^ 2 + Nat.card K + 1) (by push_cast; ring) h hPcard hPpow).elim
  · exact (false_of_cyclotomic_plane_of_charTwo hp hp3 (Or.inl rfl)
      (d := Nat.card K ^ 2 - Nat.card K + 1) (by push_cast [Nat.cast_sub hq2]; ring) h hPcard
      hPpow).elim

end CFSG.RankThree.Chevalley
