module

public import CFSG.LieType.SeitzGeneration.QuasiHighClassical

public section

namespace CFSG.LocalAnalysis.WeakClosure81.OSeitz

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Rad

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_one_of_sq_eq_one_qRad {X : Submodule K V} {hX : ∀ x ∈ X, Q x = 0}
    (h2K : (2 : K) ≠ 0) {g : V ≃ₗ[K] V} (hg : g ∈ qRad Q X hX) (hg2 : g ^ 2 = 1) : g = 1 := by
  obtain ⟨hg1, hg2', hg3⟩ := hg
  set N : Module.End K V := autToEnd K V g - 1 with hNdef
  have hNx : ∀ x, N x = g x - x := fun x => by simp [hNdef, autToEnd_apply]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ qPerp Q X := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ X := by rw [hNx]; exact hg2' _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : autToEnd K V g = 1 + N := by rw [hNdef]; abel
  have hpow := congrArg (autToEnd K V) hg2
  rw [map_pow, map_one, hg1', unip_pow_of_cube_eq_zero (K := K) hN3 2, Nat.choose_self,
    Nat.cast_one, one_smul, Nat.cast_ofNat, add_assoc] at hpow
  have h0 : (2 : K) • N + N * N = 0 := add_eq_left.1 hpow
  have h3 : N * N = 0 := by
    have h := congrArg (fun X => N * X) h0
    simp only [mul_add, mul_zero, mul_smul_comm, ← mul_assoc, hN3, add_zero] at h
    exact (smul_eq_zero.1 h).resolve_left h2K
  have h4 : N = 0 := by
    rw [h3, add_zero] at h0
    exact (smul_eq_zero.1 h0).resolve_left h2K
  have h5 : autToEnd K V g = 1 := by rw [hg1', h4, add_zero]
  refine LinearEquiv.ext fun v => ?_
  have := LinearMap.congr_fun h5 v
  simpa [autToEnd_apply] using this

theorem not_dvd_card_comap_qRad_any [Finite (V ≃ₗ[K] V)] {X : Submodule K V}
    {hX : ∀ x ∈ X, Q x = 0} {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (G : Subgroup (V ≃ₗ[K] V)) : ¬ p ∣ Nat.card ((qRad Q X hX).comap G.subtype) := by
  by_cases hp2 : p = 2
  · subst hp2
    intro hdvd
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have h1 : ((g : G) : V ≃ₗ[K] V) ^ 2 = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      exact congrArg (fun y : G => (y : V ≃ₗ[K] V)) (congrArg Subtype.val this)
    have h3 : g = 1 := Subtype.ext (Subtype.ext (eq_one_of_sq_eq_one_qRad (hX := hX)
      (by exact_mod_cast hpK) g.2 h1))
    rw [h3, orderOf_one] at hg
    exact absurd hg (by norm_num)
  · exact not_dvd_card_comap_qRad hp hp2 hpK G

end Rad

section Orthogonal

theorem hyperGen_top_of_singular_stable_of_lift {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    {G : Subgroup (V ≃ₗ[K] V)} (hGE : G = elementaryGroup Q) {P : Type} [Group P] (π : G →* P)
    (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {E : Subgroup P} (hE : IsElemAbelian p E) {k : ℕ} (hk : 1 ≤ k)
    (hcard : Nat.card E = p ^ k) {W : Submodule K V} (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, Q x = 0)
    (hstab : ∀ g : G, π g ∈ E → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W)
    (hlift : ∃ A : Subgroup G, A.map π = E ∧ Disjoint A π.ker ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      (∀ a ∈ A, a ^ p = 1) ∧ Nat.card A = Nat.card E) :
    (⊤ : Subgroup P) ≤ Subgroup.closure {k : P | k ∈ (⊤ : Subgroup P) ∧
      ∃ F₀ : Subgroup P, F₀ ≤ E ∧ F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f} := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hfinV : Finite V := Module.finite_of_finite K
  have hfinGL : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  have hfinP : Finite P := Finite.of_surjective π hπ
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hcard
    have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hGO : G ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hGE]
    exact elementaryGroup_le_orthogonalGroup Q
  have hEG : ∀ u w, eichler Q u w ∈ G := fun u w => by
    rw [hGE]
    exact eichler_mem_elementaryGroup Q u w
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ := hlift
  have hAcardp : Nat.card A = p ^ k := hAcard.trans hcard
  let ρ : A →* Module.End K V := (autToEnd K V).comp (G.subtype.comp A.subtype)
  have hAc : ∀ a b : A, a * b = b * a := fun a b => Subtype.ext (hAcomm a a.2 b b.2)
  have hAp : ∀ a : A, a ^ p = 1 := fun a => Subtype.ext (hAexp a a.2)
  have hAmem : ∀ a : A, π a.1 ∈ E := fun a => by
    rw [← hAE]
    exact Subgroup.mem_map_of_mem _ a.2
  have hAstab : ∀ a : A, ∀ w ∈ W, ρ a w ∈ W := fun a w hw => hstab a.1 (hAmem a) w hw
  obtain ⟨F', hF'idx, hW1⟩ : ∃ F' : Subgroup A, F'.index = p ∧ hyperFixed ρ F' ⊓ W ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hmem := mem_iSup_hyperFixed_top hpK hAc hAp ρ W hAstab (k := k) hk hAcardp hm
    have hbot : (⨆ (F' : Subgroup A) (_ : F'.index = p), hyperFixed ρ F' ⊓ W) = ⊥ :=
      iSup_eq_bot.2 fun F' => iSup_eq_bot.2 fun hF' => hcon F' hF'
    rw [hbot] at hmem
    exact hm0 (by simpa using hmem)
  set C : Submodule K V := hyperFixed ρ F' with hC
  set X₁ : Submodule K V := hyperFixed ρ F' ⊓ W with hX₁
  have hX₁mem : ∀ v, v ∈ X₁ ↔ (∀ f ∈ F', ρ f v = v) ∧ v ∈ W := fun v => by
    rw [hX₁, Submodule.mem_inf, mem_hyperFixed]
  have hX₁C : X₁ ≤ C := inf_le_left
  have hX₁Q : ∀ x ∈ X₁, Q x = 0 := fun x hx => hW x ((hX₁mem x).1 hx).2
  set Kset : Subgroup P := Subgroup.closure {k : P | k ∈ (⊤ : Subgroup P) ∧
    ∃ F₀ : Subgroup P, F₀ ≤ E ∧ F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f} with hKset
  set H : Subgroup G := Kset.comap π with hH
  set HV : Subgroup (V ≃ₗ[K] V) := H.map G.subtype with hHV
  have hHVO : HV ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact hGO x.2
  have hmemHV : ∀ x : G, π x ∈ Kset → (x : V ≃ₗ[K] V) ∈ HV := fun x hx => ⟨x, hx, rfl⟩
  have hF₀E : F'.map (π.comp A.subtype) ≤ E := by
    rintro _ ⟨f, -, rfl⟩
    exact hAmem f
  have hF₀rel := relIndex_map_lift hAE hAdis hF'idx
  have hcent : ∀ x : G, (∀ f : F', ((f.1 : G) : V ≃ₗ[K] V) * (x : V ≃ₗ[K] V) =
      (x : V ≃ₗ[K] V) * ((f.1 : G) : V ≃ₗ[K] V)) → (x : V ≃ₗ[K] V) ∈ HV := by
    intro x hx
    refine hmemHV x (Subgroup.subset_closure ⟨Subgroup.mem_top _, F'.map (π.comp A.subtype),
      hF₀E, hF₀rel, ?_⟩)
    rintro _ ⟨f, hf, rfl⟩
    show π f.1 * π x = π x * π f.1
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hx ⟨f, hf⟩))
  let φ : F' →* (V ≃ₗ[K] V) := (G.subtype.comp A.subtype).comp F'.subtype
  have hφ : ∀ f, φ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun f => hGO f.1.1.2
  have hqfix : qFix φ = C := by
    ext v
    rw [mem_qFix, hC, mem_hyperFixed]
    exact ⟨fun h n hn => h ⟨n, hn⟩, fun h f => h f.1 f.2⟩
  have : Fintype F' := Fintype.ofFinite F'
  have hcardF' : Nat.card F' * p = p ^ k := by
    have h := Subgroup.card_mul_index F'
    rw [hF'idx, hAcardp] at h
    exact h
  have hF : ((Fintype.card F' : ℕ) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    intro h0
    apply pow_ne_zero k hpK
    rw [← Nat.cast_pow, ← hcardF', Nat.cast_mul, h0, zero_mul]
  have hS : RootSetup Q HV C := by
    refine ⟨hHVO, hqfix ▸ polarNondegOn_qFix hQ hφ hF, fun v => ?_, fun u hu w hw => ?_⟩
    · exact ⟨qAvg φ v, hqfix ▸ qAvg_mem φ v, hqfix ▸ sub_qAvg_mem_qPerp hφ hF v⟩
    · by_cases h : Q u = 0 ∧ polar Q u w = 0
      · refine hcent ⟨eichler Q u w, hEG u w⟩ fun f => ?_
        refine commute_eichler_of_fix (hGO f.1.1.2) ?_ ?_
        · exact mem_hyperFixed.1 hu f.1 f.2
        · exact mem_hyperFixed.1 hw f.1 f.2
      · rw [eichler_of_not h]
        exact HV.one_mem
  set 𝒜 : Subgroup (V ≃ₗ[K] V) := A.map G.subtype with h𝒜
  have h𝒜O : 𝒜 ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact hGO x.2
  have hC𝒜 : ∀ a ∈ 𝒜, ∀ c ∈ C, a c ∈ C := by
    rintro _ ⟨x, hx, rfl⟩ c hc
    exact apply_mem_hyperFixed hAc ⟨x, hx⟩ hc
  have hX₁𝒜 : ∀ a ∈ 𝒜, ∀ x ∈ X₁, a x ∈ X₁ := by
    rintro _ ⟨y, hy, rfl⟩ x hx
    rw [hX₁mem] at hx ⊢
    exact ⟨fun f hf => mem_hyperFixed.1 (apply_mem_hyperFixed hAc ⟨y, hy⟩
      (mem_hyperFixed.2 hx.1)) f hf, hAstab ⟨y, hy⟩ x hx.2⟩
  have hrad : ∀ X : Submodule K V, X ≤ C → (∀ x ∈ X, Q x = 0) →
      (∀ a ∈ 𝒜, ∀ x ∈ X, a x ∈ X) → ∀ x ∈ X, ∀ d ∈ qPerp Q X, eichler Q x d ∈ HV := by
    intro X _ hXQ hX𝒜 x hx d hd
    set Qx : Subgroup G := (qRad Q X hXQ).comap G.subtype with hQx
    have hnorm : ∀ e ∈ E, ∀ v ∈ Qx.map π, e * v * e⁻¹ ∈ Qx.map π := by
      intro e he v hv
      rw [← hAE] at he
      obtain ⟨a, ha, rfl⟩ := he
      obtain ⟨q, hq, rfl⟩ := hv
      refine ⟨a * q * a⁻¹, ?_, by simp⟩
      have haS : ∀ y ∈ X, ((a : G) : V ≃ₗ[K] V) y ∈ X := fun y hy => hX𝒜 _ ⟨a, ha, rfl⟩ y hy
      have haS' : ∀ y ∈ X, ((a : G) : V ≃ₗ[K] V)⁻¹ y ∈ X := fun y hy =>
        hX𝒜 _ ⟨a⁻¹, A.inv_mem ha, rfl⟩ y hy
      exact qRad_conj_mem (hX := hXQ) (hGO a.2) haS haS' hq
    have hQp : ¬ p ∣ Nat.card (Qx.map π) := fun hd' =>
      not_dvd_card_comap_qRad_any (hX := hXQ) hp hpK G (hd'.trans (Subgroup.card_map_dvd _ π))
    have hle := le_hyperClosure_of_normalized' hp hE hE1 hnorm hQp
    have hmem : (⟨eichler Q x d, hEG x d⟩ : G) ∈ Qx :=
      eichler_mem_qRad (hX := hXQ) hx hd
    exact hmemHV _ (hle (Subgroup.mem_map_of_mem _ hmem))
  obtain ⟨e₀, he₀, he₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW1
  obtain ⟨a, b, ha, hb, hab⟩ := exists_rootCenter_pair hS h𝒜O hC𝒜 hrad hX₁C hX₁Q hX₁𝒜 he₀ he₀0
  let P₀ : HypPair Q :=
    { e := a
      f := (polar Q a b)⁻¹ • b
      Q_e := ha.2.1
      Q_f := by rw [map_smul_eq_sq, hb.2.1, mul_zero]
      polar_ef := by rw [polar_smul_right_eq, inv_mul_cancel₀ hab] }
  have hle : elementaryGroup Q ≤ HV :=
    elementaryGroup_le_of_hypPair hQ hHVO P₀ ha (hb.smul (inv_ne_zero hab))
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  obtain ⟨x, hx, hxg⟩ := hle (by rw [← hGE]; exact g.2)
  have : x = g := Subtype.ext hxg
  rw [this] at hx
  exact hx

@[expose] def HasElemLift {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P : Type} [Group P] (π : elementaryGroup Q →* P) (E : Subgroup P) :
    Prop :=
  ∃ A : Subgroup (elementaryGroup Q), A.map π = E ∧ Disjoint A π.ker ∧
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧ Nat.card A = Nat.card E

theorem top_le_iSup_centralizer_of_singular {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {P : Type} [Group P] [Finite P]
    {π : elementaryGroup Q →* P} (hc : IsOrthogonalCover Q π) (h2K : (2 : K) ≠ 0)
    {E : Subgroup P} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) {W : Submodule K V}
    (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, Q x = 0)
    (hstab : ∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W)
    (hlift : HasElemLift π E) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  classical
  have h := hyperGen_top_of_singular_stable_of_lift hc.nondegenerate rfl π hc.surjective
    Nat.prime_two (by exact_mod_cast h2K) hE (k := 2) (by norm_num) h4 hW0 hW hstab hlift
  refine h.trans ((Subgroup.closure_le _).2 ?_)
  rintro k ⟨-, F₀, hF₀E, hF₀, hk⟩
  have hF₀ne : F₀ ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.relIndex_bot_left, h4] at hF₀
    exact absurd hF₀ (by norm_num)
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF₀ne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hsub : (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} :=
    le_iSup₂_of_le a (hF₀E ha) (le_iSup_of_le ha1' le_rfl)
  exact hsub ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.mpr (hk a ha).symm⟩

@[expose] def HasCentralInvLift {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {P : Type} [Group P] (π : elementaryGroup Q →* P) (E : Subgroup P) :
    Prop :=
  ∃ t : elementaryGroup Q, π t ∈ E ∧ π t ≠ 1 ∧ t * t = 1 ∧
    ∀ g : elementaryGroup Q, π g ∈ E → g * t = t * g

theorem top_le_iSup_centralizer_of_singular_central {K V : Type} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {P : Type}
    [Group P] [Finite P] {π : elementaryGroup Q →* P} (hc : IsOrthogonalCover Q π)
    (h2K : (2 : K) ≠ 0) {E : Subgroup P} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    {W : Submodule K V} (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, Q x = 0)
    (hstab : ∀ g : elementaryGroup Q, π g ∈ E → ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W)
    {t : elementaryGroup Q} (ht : π t ∈ E) (ht1 : π t ≠ 1) (htt : t * t = 1)
    (htc : ∀ g : elementaryGroup Q, π g ∈ E → g * t = t * g) :
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 E := hE.isElementaryAbelian
  have hfinV : Finite V := Module.finite_of_finite K
  have hfinGL : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  have hGO : elementaryGroup Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q
  have hQ := hc.nondegenerate
  set T : V ≃ₗ[K] V := (t : V ≃ₗ[K] V) with hTdef
  have hTO : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hGO t.2
  have hTT : ∀ v, T (T v) = v := fun v => by
    have h := congrArg (fun g : elementaryGroup Q => ((g : V ≃ₗ[K] V) v)) htt
    simpa using h
  have hpolT : ∀ x y, polar Q (T x) (T y) = polar Q x y := fun x y => polar_map_of_mem hTO x y
  set M : Subgroup P :=
    ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer {a} with hM
  set HV : Subgroup (V ≃ₗ[K] V) := (M.comap π).map (elementaryGroup Q).subtype with hHV
  have hHVO : HV ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact hGO x.2
  have hmemHV : ∀ x : elementaryGroup Q, π x ∈ M → (x : V ≃ₗ[K] V) ∈ HV :=
    fun x hx => ⟨x, hx, rfl⟩
  have hsplit : ∀ v, v = (2 : K)⁻¹ • (v + T v) + (2 : K)⁻¹ • (v - T v) := fun v => by
    rw [← smul_add, show v + T v + (v - T v) = (2 : K) • v by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2K, one_smul]
  obtain ⟨ε, hε, w₀, hw₀W, hw₀0, hTw₀⟩ : ∃ ε : K, (ε = 1 ∨ ε = -1) ∧ ∃ w ∈ W, w ≠ 0 ∧
      T w = ε • w := by
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hTw : T w ∈ W := hstab t ht w hwW
    by_cases h1 : w + T w = 0
    · refine ⟨-1, Or.inr rfl, w, hwW, hw0, ?_⟩
      rw [neg_one_smul]
      exact eq_neg_of_add_eq_zero_right h1
    · refine ⟨1, Or.inl rfl, w + T w, W.add_mem hwW hTw, h1, ?_⟩
      rw [one_smul, map_add, hTT, add_comm]
  set C : Submodule K V := LinearMap.ker ((T : V →ₗ[K] V) - ε • LinearMap.id) with hC
  have hmemC : ∀ v, v ∈ C ↔ T v = ε • v := fun v => by
    rw [hC, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero]
    rfl
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hTd : ∀ v, T (v - ε • T v) = -ε • (v - ε • T v) := fun v => by
    rw [map_sub, map_smul, hTT]
    linear_combination (norm := module) (-hεε) • T v
  have horth : ∀ c ∈ C, ∀ v, polar Q c (v - ε • T v) = 0 := by
    intro c hc v
    have h := hpolT c (v - ε • T v)
    rw [(hmemC c).1 hc, hTd, polar_smul_left_eq, polar_smul_right_eq] at h
    have h' : polar Q c (v - ε • T v) * 2 = 0 := by
      linear_combination -h - polar Q c (v - ε • T v) * hεε
    exact (mul_eq_zero.mp h').resolve_right h2K
  have hdec : ∀ y, (2 : K)⁻¹ • (y + ε • T y) ∈ C ∧
      y - (2 : K)⁻¹ • (y + ε • T y) = (2 : K)⁻¹ • (y - ε • T y) := fun y => by
    have h2 : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2K]
    refine ⟨(hmemC _).2 ?_, by linear_combination (norm := module) (-h2) • y⟩
    rw [map_smul, map_add, map_smul, hTT]
    linear_combination (norm := module) (-(2 : K)⁻¹ * hεε) • T y
  have hreg : PolarNondegOn Q C := by
    intro x hx hxy
    refine eq_zero_of_polar_eq_zero hQ fun y => ?_
    have hy : y = (2 : K)⁻¹ • (y + ε • T y) + (2 : K)⁻¹ • (y - ε • T y) := by
      rw [← (hdec y).2]; abel
    rw [hy, polar_add_right, hxy _ (hdec y).1, polar_smul_right_eq, horth x hx y, mul_zero,
      add_zero]
  have hcommM : ∀ g : elementaryGroup Q, g * t = t * g → π g ∈ M := fun g hg => by
    have hsub : (⊤ : Subgroup P) ⊓ Subgroup.centralizer {π t} ≤ M :=
      le_iSup₂_of_le (π t) ht (le_iSup_of_le ht1 le_rfl)
    refine hsub ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul, hg]
  have hS : RootSetup Q HV C := by
    refine ⟨hHVO, hreg, fun v => ⟨_, (hdec v).1, ?_⟩, fun u hu w hw => ?_⟩
    · rw [(hdec v).2]
      exact mem_qPerp.2 fun x hx => by rw [polar_smul_right_eq, horth x hx v, mul_zero]
    · refine hmemHV ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩ (hcommM _ ?_)
      have h := eichler_conj hTO u w
      rw [(hmemC u).1 hu, (hmemC w).1 hw, eichler_smul_left, smul_smul, hεε, one_smul] at h
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp h).symm
  set 𝒜 : Subgroup (V ≃ₗ[K] V) := (E.comap π).map (elementaryGroup Q).subtype with h𝒜
  have h𝒜O : 𝒜 ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact hGO x.2
  have hC𝒜 : ∀ a ∈ 𝒜, ∀ c ∈ C, a c ∈ C := by
    rintro _ ⟨g, hg, rfl⟩ c hc
    rw [hmemC]
    have h := congrArg (fun k : elementaryGroup Q => ((k : V ≃ₗ[K] V) c)) (htc g hg)
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h
    change T ((g : V ≃ₗ[K] V) c) = ε • (g : V ≃ₗ[K] V) c
    rw [← h, (hmemC c).1 hc, map_smul]
  set X₁ : Submodule K V := W ⊓ C with hX₁
  have hX₁C : X₁ ≤ C := inf_le_right
  have hX₁Q : ∀ x ∈ X₁, Q x = 0 := fun x hx => hW x hx.1
  have hX₁𝒜 : ∀ a ∈ 𝒜, ∀ x ∈ X₁, a x ∈ X₁ := by
    rintro _ ⟨g, hg, rfl⟩ x hx
    exact ⟨hstab g hg x hx.1, hC𝒜 _ ⟨g, hg, rfl⟩ x hx.2⟩
  have he₀ : w₀ ∈ X₁ := ⟨hw₀W, (hmemC w₀).2 hTw₀⟩
  have hrad : ∀ X : Submodule K V, X ≤ C → (∀ x ∈ X, Q x = 0) →
      (∀ a ∈ 𝒜, ∀ x ∈ X, a x ∈ X) → ∀ x ∈ X, ∀ d ∈ qPerp Q X, eichler Q x d ∈ HV := by
    intro X _ hXQ hX𝒜 x hx d hd
    set Qx : Subgroup (elementaryGroup Q) := (qRad Q X hXQ).comap (elementaryGroup Q).subtype
      with hQx
    have key : ∀ e ∈ E, ∀ v ∈ Qx.map π, e * v * e⁻¹ ∈ Qx.map π := by
      intro e he v hv
      obtain ⟨g, rfl⟩ := hc.surjective e
      obtain ⟨q, hq, rfl⟩ := hv
      refine ⟨g * q * g⁻¹, ?_, by simp⟩
      have hg : g ∈ E.comap π := he
      have haS : ∀ y ∈ X, ((g : elementaryGroup Q) : V ≃ₗ[K] V) y ∈ X := fun y hy =>
        hX𝒜 _ ⟨g, hg, rfl⟩ y hy
      have haS' : ∀ y ∈ X, ((g : elementaryGroup Q) : V ≃ₗ[K] V)⁻¹ y ∈ X := fun y hy =>
        hX𝒜 _ ⟨g⁻¹, (E.comap π).inv_mem hg, rfl⟩ y hy
      exact qRad_conj_mem (hX := hXQ) (hGO g.2) haS haS' hq
    have hnorm : E ≤ Subgroup.normalizer ((Qx.map π : Subgroup P) : Set P) := by
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨key e he h, fun hh => ?_⟩
      have := key e⁻¹ (E.inv_mem he) _ hh
      simpa [mul_assoc] using this
    have hQp : ¬ 2 ∣ Nat.card (Qx.map π) := fun hd' =>
      not_dvd_card_comap_qRad_any (hX := hXQ) Nat.prime_two (by exact_mod_cast h2K) _
        (hd'.trans (Subgroup.card_map_dvd _ π))
    have hle := CFSG.LieType.Chevalley.le_iSup_inf_centralizer_of_coprime
      (by rw [h4]; norm_num) hQp hnorm (le_top : Qx.map π ≤ ⊤)
    have hmem : (⟨eichler Q x d, eichler_mem_elementaryGroup Q x d⟩ : elementaryGroup Q) ∈ Qx :=
      eichler_mem_qRad (hX := hXQ) hx hd
    exact hmemHV _ (hle (Subgroup.mem_map_of_mem _ hmem))
  obtain ⟨a, b, ha, hb, hab⟩ := exists_rootCenter_pair hS h𝒜O hC𝒜 hrad hX₁C hX₁Q hX₁𝒜 he₀ hw₀0
  let P₀ : HypPair Q :=
    { e := a
      f := (polar Q a b)⁻¹ • b
      Q_e := ha.2.1
      Q_f := by rw [map_smul_eq_sq, hb.2.1, mul_zero]
      polar_ef := by rw [polar_smul_right_eq, inv_mul_cancel₀ hab] }
  have hle : elementaryGroup Q ≤ HV :=
    elementaryGroup_le_of_hypPair hQ hHVO P₀ ha (hb.smul (inv_ne_zero hab))
  intro k _
  obtain ⟨g, rfl⟩ := hc.surjective k
  obtain ⟨x, hx, hxg⟩ := hle g.2
  have : x = g := Subtype.ext hxg
  rw [this] at hx
  exact hx

end Orthogonal

end CFSG.LocalAnalysis.WeakClosure81.OSeitz

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LieType.SeitzGeneration QuadraticMap CFSG.ClassicalGroups.Orthogonal OSeitz

abbrev IsOddOrthogonal (X : Type) [Group X] : Prop :=
  ∃ n p f : ℕ, p ≠ 2 ∧ (CFSG.Models.LieModel X .POmegaOdd n p f ∨
    CFSG.Models.LieModel X .POmegaPlus n p f ∨ CFSG.Models.LieModel X .POmegaMinus n p f)

end CFSG.LocalAnalysis.WeakClosure81
