module

public import CFSG.Quasithin.Background.Harris.R1.L28Borel
public import CFSG.Quasithin.Background.Harris.R1.SignChoice
public import CFSG.Quasithin.Background.Harris.R1.Q8L2BFacts

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7

open scoped Pointwise commutatorElement

section Generic

variable {X Y : Type*} [Group X] [Group Y]

theorem lift28_vec_map (f : X →* Y) (a b : X) :
    (fun i => f (![a, b] i)) = ![f a, f b] := by
  funext i
  fin_cases i <;> rfl

theorem lift28_evalWord_map (f : X →* Y) {m : ℕ} (g : Fin m → X) (r : List (Fin m × Bool)) :
    D4Vert.evalWord (fun i => f (g i)) r = f (D4Vert.evalWord g r) := by
  induction r with
  | nil => simp [D4Vert.evalWord_nil]
  | cons p r ih =>
    rw [D4Vert.evalWord_cons, D4Vert.evalWord_cons, ih]
    obtain ⟨i, s⟩ := p
    cases s <;> simp

theorem lift28_evalWord_map₂ (f : X →* Y) (a b : X) (r : List (Fin 2 × Bool)) :
    D4Vert.evalWord ![f a, f b] r = f (D4Vert.evalWord ![a, b] r) := by
  rw [← lift28_vec_map]
  exact lift28_evalWord_map f _ r

theorem lift28_evalWord_mem (H : Subgroup X) {a b : X} (ha : a ∈ H) (hb : b ∈ H)
    (r : List (Fin 2 × Bool)) : D4Vert.evalWord ![a, b] r ∈ H := by
  induction r with
  | nil => exact H.one_mem
  | cons p r ih =>
    rw [D4Vert.evalWord_cons]
    obtain ⟨i, s⟩ := p
    refine H.mul_mem ?_ ih
    fin_cases i <;> cases s <;> simp [ha, hb]

variable {K : Type*} [Group K]

theorem lift28_mem_map_iff (θ : K →* X) {H : Subgroup K} (hker : θ.ker ≤ H) (x : K) :
    θ x ∈ H.map θ ↔ x ∈ H := by
  refine ⟨fun h => ?_, fun h => Subgroup.mem_map_of_mem θ h⟩
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h
  have : y⁻¹ * x ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
  have h2 := hker this
  have := H.mul_mem hy h2
  simpa using this

theorem lift28_card_eq [Finite K] (θ : K →* X) (H : Subgroup K) (hker : θ.ker ≤ H) :
    Nat.card H = Nat.card (H.map θ) * Nat.card θ.ker := by
  have h := Subgroup.card_ker_mul_card_range (θ.domRestrict H)
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h
  have hk : Nat.card (θ.ker.subgroupOf H) = Nat.card θ.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv
  rw [hk] at h
  rw [← h, mul_comm]

theorem lift28_exists_conj [Finite X] (hX : Nat.card X = 504) {E T : Subgroup X}
    (hE : Nat.card E = 8) (hT : Nat.card T = 8) :
    ∃ g : X, ∀ x, x ∈ T ↔ g⁻¹ * x * g ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : (Nat.card X).factorization 2 = 3 := by
    rw [hX, show (504 : ℕ) = 2 ^ 3 * 63 by norm_num,
      Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 63 by norm_num)]
    rfl
  have hE' : Nat.card E = 2 ^ (Nat.card X).factorization 2 := by rw [hf, hE]; norm_num
  have hT' : Nat.card T = 2 ^ (Nat.card X).factorization 2 := by rw [hf, hT]; norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (Sylow.ofCard E hE') (Sylow.ofCard T hT')
  have h1 : MulAut.conj g • E = T := by
    have := congrArg (fun P : Sylow 2 X => (P : Subgroup X)) hg
    simpa [Sylow.coe_subgroup_smul] using this
  refine ⟨g, fun x => ?_⟩
  rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp

theorem lift28_exists_conj_borel [Finite X] (hX : Nat.card X = 504) {B0 E T B' : Subgroup X}
    (hE : Nat.card E = 8) (hNE : Subgroup.normalizer (E : Set X) = B0) (hB0 : Nat.card B0 = 56)
    (hT : Nat.card T = 8) (hB' : B' ≤ Subgroup.normalizer (T : Set X)) (hB'c : Nat.card B' = 56) :
    ∃ g : X, ∀ x, x ∈ B' ↔ g⁻¹ * x * g ∈ B0 := by
  obtain ⟨g, hg⟩ := lift28_exists_conj hX hE hT
  have hmem : ∀ x, x ∈ B0.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ B0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show g⁻¹ * (g * y * g⁻¹) * g ∈ B0
      rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    · intro h
      exact ⟨_, h, by show g * (g⁻¹ * x * g) * g⁻¹ = x; group⟩
  have hN : ∀ x, x ∈ Subgroup.normalizer (T : Set X) →
      g⁻¹ * x * g ∈ Subgroup.normalizer (E : Set X) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro h
    have e1 : h ∈ E ↔ g * h * g⁻¹ ∈ T := by
      rw [hg, show g⁻¹ * (g * h * g⁻¹) * g = h by group]
    have e2 := hx (g * h * g⁻¹)
    have e3 : x * (g * h * g⁻¹) * x⁻¹ ∈ T ↔ g⁻¹ * x * g * h * (g⁻¹ * x * g)⁻¹ ∈ E := by
      rw [hg]
      have : g⁻¹ * (x * (g * h * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * h * (g⁻¹ * x * g)⁻¹ := by group
      rw [this]
    rw [e1, e2, e3]
  have hle : B' ≤ B0.map (MulAut.conj g).toMonoidHom := fun x hx => by
    rw [hmem, ← hNE]
    exact hN x (hB' hx)
  have hcard : Nat.card (B0.map (MulAut.conj g).toMonoidHom) = 56 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hB0]
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hB'c])
  refine ⟨g, fun x => ?_⟩
  rw [← hmem, ← heq]

end Generic

section Core

variable {K X : Type} [Group K] [Group X] [Finite K]

theorem lift28_core (θ : K →* X) (hθ : Function.Surjective θ)
    {z : K} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzc : ∀ k, z * k = k * z) (hzθ : θ z = 1)
    {Sg : Subgroup K} (hzS : z ∈ Sg)
    (hsplit : ∀ k : K, ∃ q ∈ θ.ker, ∃ k' ∈ Sg, k = q * k')
    (hker : ∀ x ∈ Sg, θ x = 1 → x = 1 ∨ x = z)
    (hX : Nat.card X = 504) {a b : X}
    (hrel : ∀ r ∈ D4Vert.l28Rels, D4Vert.evalWord ![a, b] r = 1)
    (hgen : Subgroup.closure ({a, b} : Set X) = ⊤) :
    ∃ a' b' : K, a' ∈ Sg ∧ b' ∈ Sg ∧ θ a' = a ∧ θ b' = b ∧
      ∀ r ∈ D4Vert.l28Rels, D4Vert.evalWord ![a', b'] r = 1 := by
  have hpre : ∀ x : X, ∃ y ∈ Sg, θ y = x := by
    intro x
    obtain ⟨k, rfl⟩ := hθ x
    obtain ⟨q, hq, k', hk', rfl⟩ := hsplit k
    refine ⟨k', hk', ?_⟩
    rw [map_mul, MonoidHom.mem_ker.1 hq, one_mul]
  obtain ⟨a₁, ha₁, hθa⟩ := hpre a
  obtain ⟨b₁, hb₁, hθb⟩ := hpre b
  have hrelz : ∀ r ∈ D4Vert.l28Rels,
      D4Vert.evalWord ![a₁, b₁] r = 1 ∨ D4Vert.evalWord ![a₁, b₁] r = z := by
    intro r hr
    apply hker _ (lift28_evalWord_mem Sg ha₁ hb₁ r)
    rw [← lift28_evalWord_map₂ θ a₁ b₁ r, hθa, hθb]
    exact hrel r hr
  have hbig : 504 < Nat.card (Subgroup.closure ({a₁, b₁, z} : Set K)) := by
    set A := Subgroup.closure ({a₁, b₁, z} : Set K) with hA
    have hsurj : Function.Surjective (θ.domRestrict A) := by
      intro x
      have hx : x ∈ A.map θ := by
        have : Subgroup.closure ({a, b} : Set X) ≤ A.map θ := by
          rw [Subgroup.closure_le]
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact ⟨a₁, Subgroup.subset_closure (by simp), hθa⟩
          · exact ⟨b₁, Subgroup.subset_closure (by simp), hθb⟩
        exact this (by rw [hgen]; exact Subgroup.mem_top x)
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨⟨y, hy⟩, rfl⟩
    have hninj : ¬ Function.Injective (θ.domRestrict A) := by
      intro hinj
      have hzA : z ∈ A := Subgroup.subset_closure (by simp)
      have := @hinj ⟨z, hzA⟩ 1 (by simp [hzθ])
      exact hz1 (congrArg Subtype.val this)
    by_contra hle
    push Not at hle
    exact hninj (hsurj.bijective_of_nat_card_le (by rw [hX]; exact hle)).1
  obtain ⟨a', b', ha', hb', hrel'⟩ :=
    D4Vert.exists_l28_lift hz2 hz1 (hzc a₁) (hzc b₁) hrelz hbig
  have hmul : ∀ {x : K}, x ∈ Sg → x * z ∈ Sg := fun hx => Sg.mul_mem hx hzS
  refine ⟨a', b', ?_, ?_, ?_, ?_, hrel'⟩
  · rcases ha' with rfl | rfl
    · exact ha₁
    · exact hmul ha₁
  · rcases hb' with rfl | rfl
    · exact hb₁
    · exact hmul hb₁
  · rcases ha' with rfl | rfl
    · exact hθa
    · rw [map_mul, hzθ, mul_one, hθa]
  · rcases hb' with rfl | rfl
    · exact hθb
    · rw [map_mul, hzθ, mul_one, hθb]

end Core

section Main

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

omit [Finite G] in
theorem lift28_exists_theta (hL : IsL2Quot 3 (OTwoQuot K1))
    (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) :
    ∃ θ : ↥K1 →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3),
      Function.Surjective θ ∧ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
        (GaloisField 2 3)) = 504 ∧ ∀ k : ↥K1, θ k = 1 ↔ (k : G) ∈ vBeta K1 L2 S Zs := by
  have hc : Nat.card (OTwoQuot K1) = 504 := by
    rw [IsL2Quot.card (by norm_num) hL]
    norm_num
  obtain ⟨e⟩ := hL
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_, fun k => ?_⟩
  · rw [← Nat.card_congr e.toEquiv, hc]
  · show e (QuotientGroup.mk' _ k) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← hQK]
    constructor
    · intro h
      exact Subgroup.mem_map_of_mem K1.subtype h
    · intro h
      obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.1 h
      have : k' = k := Subtype.ext hkk
      rwa [this] at hk'

omit [Finite G] in
theorem lift28_coe_mem_closure {a b y : ↥K1} (hy : y ∈ Subgroup.closure ({a, b} : Set ↥K1)) :
    (y : G) ∈ Subgroup.closure ({(a : G), (b : G)} : Set G) := by
  have := Subgroup.mem_map_of_mem K1.subtype hy
  rw [MonoidHom.map_closure, Set.image_pair] at this
  exact this

end Main

theorem exists_l28_signStab
    {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type} [Fintype Ω]
    [DecidableEq Ω]
    (C : SzR1.FamCtx K1 L2 S Zs Ω) (hM : L28BorelModel) (hΩ : Fintype.card Ω = 9)
    (hL : IsL2Quot 3 (OTwoQuot K1)) (hQK : pCoreOf 2 K1 = vBeta K1 L2 S Zs) (hSK : S ≤ K1)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    {z : G} (hz : z ∈ Zs) (hz1 : z ≠ 1) {σ : Ω → G} (hσ : IsSignChoice C z σ) :
    ∃ a b : G, a ∈ signStab C σ ∧ b ∈ signStab C σ ∧
      (∀ r ∈ D4Vert.l28Rels, D4Vert.evalWord ![a, b] r = 1) ∧
      l28Borel a b ≤ borelOf K1 S ∧ a ∉ borelOf K1 S ∧
      (∀ i j : Fin 9, i ≠ j → (D4Vert.evalWord ![a, b] (D4Vert.l28H.getD i []))⁻¹ *
        D4Vert.evalWord ![a, b] (D4Vert.l28H.getD j []) ∉ borelOf K1 S) ∧
      vBeta K1 L2 S Zs ⊔ Subgroup.closure ({a, b} : Set G) = K1 := by
  classical
  have hWK : vBeta K1 L2 S Zs ≤ K1 := by rw [← hQK]; exact pCoreOf_le 2 K1
  obtain ⟨θ, hθs, hX, hθk⟩ := lift28_exists_theta hL hQK
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hna : ⁅vBeta K1 L2 S Zs, vBeta K1 L2 S Zs⁆ ≠ ⊥ := by
    rw [C.hcomm]
    intro h
    have := C.h.card_Z
    rw [h, Subgroup.card_bot] at this
    omega
  have hsp : IsSpecialPow 2 2 4 ↥(pCoreOf 2 K1) := by
    rw [hQK]; exact vBeta_special_of_L28 G K1 L2 S Zs C.h hL hna
  have hK : Nat.card ↥K1 = 258048 := S1421QA27.card_K1_of_survivor4 hL hsp
  have hS : Nat.card ↥S = 2 ^ 12 := card_S_of_sylow C.h.hyp.h1.sylow hSK hK
  have hB : 9 * Nat.card ↥(borelOf K1 S) = Nat.card ↥K1 := card_borelOf C hΩ
  have hker512 : Nat.card θ.ker = 512 := by
    have := Subgroup.card_ker_mul_card_of_surjective hθs
    rw [hX, hK] at this
    omega
  have hVS : vBeta K1 L2 S Zs ≤ S := C.vBeta_le_S
  have hSB : S ≤ borelOf K1 S := by
    have := F1.sylow_le_borelOf K1 S
    rwa [inf_eq_left.mpr hSK] at this
  have hkS : θ.ker ≤ S.subgroupOf K1 := fun k hk => hVS ((hθk k).1 (MonoidHom.mem_ker.1 hk))
  have hkB : θ.ker ≤ (borelOf K1 S).subgroupOf K1 := fun k hk => hSB (hkS hk)
  have hS'c : Nat.card (S.subgroupOf K1) = 4096 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hS]
    norm_num
  have hB1c : Nat.card ((borelOf K1 S).subgroupOf K1) = 28672 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (F1.borelOf_le K1 S)).toEquiv]
    omega
  have hTc : Nat.card ((S.subgroupOf K1).map θ) = 8 := by
    have := lift28_card_eq θ _ hkS
    rw [hS'c, hker512] at this
    omega
  have hBpc : Nat.card (((borelOf K1 S).subgroupOf K1).map θ) = 56 := by
    have := lift28_card_eq θ _ hkB
    rw [hB1c, hker512] at this
    omega
  have hB1N : (borelOf K1 S).subgroupOf K1 ≤ Subgroup.normalizer ((S.subgroupOf K1 : Subgroup ↥K1) : Set ↥K1) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb s hs
    have hbN := borelOf_le_normalizer_S hSK hb
    rw [Subgroup.mem_normalizer_iff] at hbN
    exact (hbN (s : G)).1 hs
  have hBpN := (Subgroup.map_mono (f := θ) hB1N).trans (Subgroup.le_normalizer_map θ)
  obtain ⟨a0, b0, hrel0, hgen0, hB0c, ⟨E, hEc, hNE⟩, ha0, hh0⟩ := hM
  obtain ⟨g, hgB⟩ := lift28_exists_conj_borel hX hEc hNE hB0c hTc hBpN hBpc
  let φ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) := (MulAut.conj g).toMonoidHom
  have hφ : ∀ x, φ x = g * x * g⁻¹ := fun x => rfl
  have hrelφ : ∀ r ∈ D4Vert.l28Rels, D4Vert.evalWord ![φ a0, φ b0] r = 1 := by
    intro r hr
    rw [lift28_evalWord_map₂, hrel0 r hr, map_one]
  have hgenφ : Subgroup.closure ({φ a0, φ b0} : Set _) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : g⁻¹ * x * g ∈ Subgroup.closure ({a0, b0} : Set _) := by rw [hgen0]; trivial
    have h2 := Subgroup.mem_map_of_mem φ h1
    rw [MonoidHom.map_closure, Set.image_pair] at h2
    have h3 : φ (g⁻¹ * x * g) = x := by rw [hφ]; group
    rwa [h3] at h2
  have hzW := F112J2.Zs_le_vBeta K1 L2 S Zs hz
  have hzK : z ∈ K1 := hWK hzW
  obtain ⟨z0, hz0⟩ : ∃ z0 : ↥K1, (z0 : G) = z := ⟨⟨z, hzK⟩, rfl⟩
  have hz2 : z0 * z0 = 1 := Subtype.ext (by
    simp only [Subgroup.coe_mul, hz0, Subgroup.coe_one]; exact C.Zs_sq hz)
  have hz1' : z0 ≠ 1 := fun h => hz1 (by rw [← hz0, h]; rfl)
  have hzc : ∀ k : ↥K1, z0 * k = k * z0 := fun k => Subtype.ext (by
    simp only [Subgroup.coe_mul, hz0]; exact Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z k.2) z hz)
  have hzθ : θ z0 = 1 := (hθk z0).2 (by rw [hz0]; exact hzW)
  have hzsig : z ∈ signStab C σ := ((signStab_inf_vBeta C hz hz1 hσ hcen hWK).ge hz).2
  have hzS : z0 ∈ (signStab C σ).subgroupOf K1 := by
    rw [Subgroup.mem_subgroupOf, hz0]; exact hzsig
  have hsplit : ∀ k : ↥K1, ∃ q ∈ θ.ker, ∃ k' ∈ (signStab C σ).subgroupOf K1, k = q * k' := by
    intro k
    obtain ⟨q, hqW, k', hk', hkq⟩ :=
      exists_mul_signStab C hz hz1 hσ (by omega) hWK k.2
    refine ⟨⟨q, hWK hqW⟩, (hθk _).2 hqW, ⟨k', signStab_le C σ hk'⟩, hk', Subtype.ext hkq⟩
  have hker : ∀ x ∈ (signStab C σ).subgroupOf K1, θ x = 1 → x = 1 ∨ x = z0 := by
    intro x hx hθx
    have hxW := (hθk x).1 hθx
    have hxZ : (x : G) ∈ Zs := (signStab_inf_vBeta C hz hz1 hσ hcen hWK).le ⟨hxW, hx⟩
    rcases Zs_cases C hz hz1 hxZ with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (by rw [h, hz0]))
  obtain ⟨a', b', ha'S, hb'S, hθa, hθb, hrel'⟩ :=
    lift28_core θ hθs hz2 hz1' hzc hzθ hzS hsplit hker hX hrelφ hgenφ
  have hθw : ∀ w, θ (D4Vert.evalWord ![a', b'] w) =
      g * D4Vert.evalWord ![a0, b0] w * g⁻¹ := by
    intro w
    rw [← lift28_evalWord_map₂ θ a' b' w, hθa, hθb, lift28_evalWord_map₂ φ a0 b0 w]
    rfl
  have hBmem : ∀ (x : ↥K1) (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)),
      θ x = g * y * g⁻¹ → ((x : G) ∈ borelOf K1 S ↔ y ∈ l28Borel a0 b0) := by
    intro x y hxy
    have h1 : (x : G) ∈ borelOf K1 S ↔ x ∈ (borelOf K1 S).subgroupOf K1 := Iff.rfl
    rw [h1, ← lift28_mem_map_iff θ hkB x, hgB, hxy]
    have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [this]
  have hcoe : ∀ w, D4Vert.evalWord ![(a' : G), (b' : G)] w =
      ((D4Vert.evalWord ![a', b'] w : ↥K1) : G) := fun w =>
    lift28_evalWord_map₂ K1.subtype a' b' w
  refine ⟨(a' : G), (b' : G), ha'S, hb'S, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [hcoe, hrel' r hr]
    rfl
  · rw [l28Borel, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · rw [SetLike.mem_coe, hcoe]
      exact (hBmem _ _ (hθw _)).2 (Subgroup.subset_closure (Set.mem_insert _ _))
    · rw [SetLike.mem_coe, hcoe]
      exact (hBmem _ _ (hθw _)).2 (Subgroup.subset_closure (by simp))
  · intro h
    exact ha0 ((hBmem a' a0 (by rw [hθa]; rfl)).1 h)
  · intro i j hij h
    rw [hcoe, hcoe] at h
    have hx : θ ((D4Vert.evalWord ![a', b'] (D4Vert.l28H.getD i []))⁻¹ *
        D4Vert.evalWord ![a', b'] (D4Vert.l28H.getD j [])) =
        g * ((D4Vert.evalWord ![a0, b0] (D4Vert.l28H.getD i []))⁻¹ *
          D4Vert.evalWord ![a0, b0] (D4Vert.l28H.getD j [])) * g⁻¹ := by
      rw [map_mul, map_inv, hθw, hθw]
      group
    exact hh0 i j hij ((hBmem _ _ hx).1 h)
  · apply le_antisymm
    · refine sup_le hWK ?_
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact a'.2
      · exact b'.2
    · intro k hk
      have hmapA : (Subgroup.closure ({a', b'} : Set ↥K1)).map θ = ⊤ := by
        rw [MonoidHom.map_closure, Set.image_pair, hθa, hθb, hgenφ]
      have hmem : θ ⟨k, hk⟩ ∈ (Subgroup.closure ({a', b'} : Set ↥K1)).map θ := by
        rw [hmapA]; exact Subgroup.mem_top _
      obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.1 hmem
      have hq : (⟨k, hk⟩ : ↥K1) * y⁻¹ ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyk, mul_inv_cancel]
      have hqW := (hθk _).1 (MonoidHom.mem_ker.1 hq)
      have hyG := lift28_coe_mem_closure hy
      have e : k = (((⟨k, hk⟩ : ↥K1) * y⁻¹ : ↥K1) : G) * (y : G) := by
        simp
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hqW) (Subgroup.mem_sup_right hyG)

end CFSG.Quasithin.Background.Harris.R1
