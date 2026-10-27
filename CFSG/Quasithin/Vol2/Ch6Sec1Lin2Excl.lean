module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19T

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin
open scoped Matrix commutatorElement

theorem mul_self_eq_one_of_mulVec_ch6 {F : Type*} [Field F] (h2 : (2 : F) = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) {v : Fin 2 → F} (hv : v ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : g * g = 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact g.2
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  set a := (g : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (g : Matrix (Fin 2) (Fin 2) F) 1 1
  have e0 : (a + d) * v 0 = 0 := by
    linear_combination (1 - d) * h0 + b * h1 + v 0 * hdet + v 0 * h2
  have e1 : (a + d) * v 1 = 0 := by
    linear_combination c * h0 + (1 - a) * h1 + v 1 * hdet + v 1 * h2
  have hs : a + d = 0 := by
    by_contra hs
    apply hv
    funext i
    fin_cases i
    · exact (mul_eq_zero.mp e0).resolve_left hs
    · exact (mul_eq_zero.mp e1).resolve_left hs
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true]
  · linear_combination a * hs - hdet - h2
  · linear_combination b * hs
  · linear_combination c * hs
  · linear_combination d * hs - hdet - h2

theorem eq_one_of_mulVec_ch6 {F : Type*} [Field F] (h2 : (2 : F) = 0)
    {g : Matrix.SpecialLinearGroup (Fin 2) F} {k : ℕ} (hk : g ^ 3 ^ k = 1) {v : Fin 2 → F}
    (hv : v ≠ 0) (hg : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) : g = 1 := by
  have h1 : g ^ 2 = 1 := by rw [sq]; exact mul_self_eq_one_of_mulVec_ch6 h2 g hv hg
  have h3 : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h4 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h1
  have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left _ (by norm_num)
  have h5 : orderOf g ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h3 h4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h5)

@[expose] def u0Ch6 : G6.coreMod 5 :=
  ⟨Multiplicative.ofAdd ![1, 0, 0, 0, 1], by rw [G6.mem_coreMod]; decide⟩

@[expose] def dCh6 (σ : Equiv.Perm (Fin 5)) (u : G6.coreMod 5) : G6.coreMod 5 :=
  u * (G6.coreAct 5 σ u)⁻¹

abbrev sigmaACh6 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

abbrev sigmaBCh6 : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 3 4

theorem coreAct_sigmaA_ch6 : G6.coreAct 5 sigmaACh6 (dCh6 sigmaBCh6 (dCh6 sigmaBCh6 u0Ch6)) =
    dCh6 sigmaBCh6 (dCh6 sigmaBCh6 u0Ch6) := by
  decide

theorem coreAct_sigmaB_ne_ch6 :
    G6.coreAct 5 sigmaBCh6 (dCh6 sigmaBCh6 (dCh6 sigmaBCh6 u0Ch6)) ≠
      dCh6 sigmaBCh6 (dCh6 sigmaBCh6 u0Ch6) := by
  decide

theorem sigma_facts_ch6 : sigmaACh6 ^ 3 = 1 ∧ sigmaBCh6 ^ 3 = 1 ∧ sigmaACh6 ≠ 1 := by
  decide

variable {G : Type} [Group G] [Finite G]

namespace L619

omit [Finite G] in
theorem mkW_congr_ch6 {W Z : Subgroup G} (hW : IsElemAbelian 2 W) {a b : G} (ha : a ∈ W)
    (hb : b ∈ W) (h : a = b) : mkW hW Z ha = mkW hW Z hb := by
  subst h
  rfl

variable {W Z P : Subgroup G} (hW : IsElemAbelian 2 W)
  {K : Subgroup (MulAut ↥(V0 hW Z P))} (θ : ↥K ≃* Equiv.Perm (Fin 5))
  (β₀ : G6.coreMod 5 →* ↥(V0 hW Z P))

omit [Finite G] in
theorem mkW_conj_ch6
    (hβeq : ∀ (x : ↥K) (u : G6.coreMod 5),
      β₀ (G6.coreAct 5 (θ x) u) = (x : MulAut ↥(V0 hW Z P)) (β₀ u))
    {g : G} (hg : g ∈ normWZX W Z P) {k : ↥K}
    (hk : act0 hW Z P ⟨g, hg⟩ = (k : MulAut ↥(V0 hW Z P))) {w : G} (hw : w ∈ W)
    {u : G6.coreMod 5} (hu : mkW hW Z hw = ((β₀ u : ↥(V0 hW Z P)) : IntMod W hW ⧸ modSub hW Z))
    (hc : g * w * g⁻¹ ∈ W) :
    mkW hW Z hc = ((β₀ (G6.coreAct 5 (θ k) u) : ↥(V0 hW Z P)) : IntMod W hW ⧸ modSub hW Z) := by
  have h1 := actQ_mkW hW (Z := Z) ⟨g, hg.1⟩ hw
  rw [hu] at h1
  rw [← h1, hβeq, ← hk, act0_apply, actQX_apply]

omit [Finite G] in
theorem mkW_commutator_ch6
    (hβeq : ∀ (x : ↥K) (u : G6.coreMod 5),
      β₀ (G6.coreAct 5 (θ x) u) = (x : MulAut ↥(V0 hW Z P)) (β₀ u))
    {g : G} (hg : g ∈ normWZX W Z P) {k : ↥K}
    (hk : act0 hW Z P ⟨g, hg⟩ = (k : MulAut ↥(V0 hW Z P))) {w : G} (hw : w ∈ W)
    {u : G6.coreMod 5} (hu : mkW hW Z hw = ((β₀ u : ↥(V0 hW Z P)) : IntMod W hW ⧸ modSub hW Z)) :
    ∃ hc : ⁅w, g⁆ ∈ W, mkW hW Z hc =
      ((β₀ (u * (G6.coreAct 5 (θ k) u)⁻¹) : ↥(V0 hW Z P)) : IntMod W hW ⧸ modSub hW Z) := by
  have hgW : g ∈ Subgroup.normalizer (W : Set G) := hg.1.1
  have hw' : g * w⁻¹ * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgW _).mp (W.inv_mem hw)
  have e : ⁅w, g⁆ = w * (g * w⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
  have hc : ⁅w, g⁆ ∈ W := e ▸ W.mul_mem hw hw'
  refine ⟨hc, ?_⟩
  have hinv : mkW hW Z (W.inv_mem hw) =
      ((β₀ u⁻¹ : ↥(V0 hW Z P)) : IntMod W hW ⧸ modSub hW Z) := by
    rw [← mkW_inv hW hw, hu, map_inv, Subgroup.coe_inv]
  rw [mkW_congr_ch6 hW hc (W.mul_mem hw hw') e, ← mkW_mul hW hw hw',
    mkW_conj_ch6 hW θ β₀ hβeq hg hk (W.inv_mem hw) hinv hw', hu]
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

end L619

omit [Finite G] in
theorem conj_mem_blockU_ch6 {A : Subgroup G} {a u : G} (ha : a ∈ A) (hu : u ∈ blockU A) :
    a * u * a⁻¹ ∈ blockU A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : (blockQ A).map (MulAut.conj a).toMonoidHom = blockQ A :=
    map_conj_eq_of_mem_normalizer_ch6 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A ha)
  have hA : A.map (MulAut.conj a).toMonoidHom = A :=
    map_conj_eq_of_mem_normalizer_ch6 (Subgroup.le_normalizer ha)
  have h1 : (blockU A).map (MulAut.conj a).toMonoidHom = blockU A := by
    unfold blockU
    rw [Subgroup.map_commutator, hQ, hA]
  rw [← h1]
  exact Subgroup.mem_map_of_mem _ hu

theorem natKer_five_eq_bot_ch6 : G6.natKer 5 = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  have hu' : (u : G6.PermMod 5) ∈ Subgroup.zpowers (G6.allOnes 5) := hu
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu'
  have hk' : (u : G6.PermMod 5) = Multiplicative.ofAdd (fun _ : Fin 5 => (k : ZMod 2)) := by
    rw [← hk, G6.allOnes, ← ofAdd_zsmul]
    congr 1
    funext i
    simp
  have hs := u.2
  rw [G6.mem_coreMod, hk'] at hs
  have h2 : (k : ZMod 2) = 0 := by
    simp only [toAdd_ofAdd, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hs
    have h5 : ((5 : ℕ) : ZMod 2) = 1 := by decide
    rwa [h5, one_mul] at hs
  apply Subtype.ext
  rw [hk', h2]
  rfl

theorem isSymNatural_five_of_card_ch6 {V : Type*} [CommGroup V] {X : Subgroup (MulAut V)}
    {Y : Subgroup V} (h : G6.IsG64Type X Y) (hX : Nat.card X = 120) : G6.IsSymNatural X Y 5 := by
  rcases h with ⟨m, hm2, hm5, hLn⟩ | ⟨m, hm5, hm8, hSym⟩ | ⟨m, hm, hCore⟩
  · exfalso
    obtain ⟨e⟩ := hLn.1
    have h1 := Nat.card_congr e.toEquiv
    rw [hX, Matrix.card_GL_field, ZMod.card] at h1
    interval_cases m <;> simp [Fin.prod_univ_succ] at h1
  · obtain ⟨θ, β, h1, h2, h3⟩ := hSym
    have h4 := Nat.card_congr θ.toEquiv
    rw [hX, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h4
    have hm : m = 5 := by
      interval_cases m <;> simp [Nat.factorial] at h4 ⊢
    subst hm
    exact ⟨θ, β, h1, h2, h3⟩
  · exfalso
    obtain ⟨θ, -⟩ := hCore
    have h4 := Nat.card_congr θ.toEquiv
    rw [hX, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h4
    rcases hm with rfl | rfl <;> simp [Nat.factorial] at h4

theorem false_of_isLin2Type_threePart_ch6 {W Z P : Subgroup G} (hW : IsElemAbelian 2 W)
    (hPN : P ≤ L619.normWZX W Z P) (hPZ : P ≤ Subgroup.centralizer (Z : Set G))
    (hWP : W ≤ Subgroup.normalizer (P : Set G))
    (θ : ↥(L619.img0 hW Z P) ≃* Equiv.Perm (Fin 5))
    (β₀ : G6.coreMod 5 →* ↥(L619.V0 hW Z P))
    (hβeq : ∀ (x : ↥(L619.img0 hW Z P)) (u : G6.coreMod 5),
      β₀ (G6.coreAct 5 (θ x) u) = (x : MulAut ↥(L619.V0 hW Z P)) (β₀ u))
    (hβinj : Function.Injective β₀) {f : ℕ} (hlin : IsLin2Type (L619.threePart P) f) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := L619.threePart P with hA
  obtain ⟨F, _, _, hF, α, -, hαk, β', -, hβ'k, hβ'e⟩ := hlin
  have hAP : A ≤ P := L619.threePart_le P
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun x hx => (hPN (hAP hx)).1.1
  have hWA : W ≤ Subgroup.normalizer (A : Set G) :=
    hWP.trans (L619.normalizer_le_normalizer_threePart P)
  set ψ := L619.actOn hW Z P hPN (fun x => L619.act0_mem_img0 hW Z P x.2) with hψ
  have hψs : Function.Surjective ψ := L619.actOn_surjective hW Z P hPN
  set ρ : ↥P →* Equiv.Perm (Fin 5) := θ.toMonoidHom.comp ψ with hρ
  have hρs : Function.Surjective ρ := θ.surjective.comp hψs
  obtain ⟨hσA3, hσB3, hσA1⟩ := sigma_facts_ch6
  obtain ⟨a, haA, haρ, ka, hka⟩ := L619.exists_threePart_lift ρ hρs (k := sigmaACh6) (j := 1)
    (by simpa using hσA3)
  obtain ⟨b, hbA, hbρ, -, -⟩ := L619.exists_threePart_lift ρ hρs (k := sigmaBCh6) (j := 1)
    (by simpa using hσB3)
  have haP : a ∈ P := hAP haA
  have hbP : b ∈ P := hAP hbA
  have hak : L619.act0 hW Z P ⟨a, hPN haP⟩ =
      ((ψ ⟨a, haP⟩ : ↥(L619.img0 hW Z P)) : MulAut ↥(L619.V0 hW Z P)) := rfl
  have hbk : L619.act0 hW Z P ⟨b, hPN hbP⟩ =
      ((ψ ⟨b, hbP⟩ : ↥(L619.img0 hW Z P)) : MulAut ↥(L619.V0 hW Z P)) := rfl
  have hθa : θ (ψ ⟨a, haP⟩) = sigmaACh6 := haρ
  have hθb : θ (ψ ⟨b, hbP⟩) = sigmaBCh6 := hbρ
  obtain ⟨w₀, hw₀, hw₀e⟩ := L619.mkW_surjective hW Z
    ((β₀ u0Ch6 : ↥(L619.V0 hW Z P)) : IntMod W hW ⧸ L619.modSub hW Z)
  obtain ⟨hu₁, hu₁e⟩ := L619.mkW_commutator_ch6 hW θ β₀ hβeq (hPN hbP) hbk hw₀ hw₀e
  rw [hθb] at hu₁e
  obtain ⟨hu₂, hu₂e⟩ := L619.mkW_commutator_ch6 hW θ β₀ hβeq (hPN hbP) hbk hu₁ hu₁e
  rw [hθb] at hu₂e
  set u₁ := ⁅w₀, b⁆ with hu₁def
  set u₂ := ⁅u₁, b⁆ with hu₂def
  set x₀ := dCh6 sigmaBCh6 (dCh6 sigmaBCh6 u0Ch6) with hx₀
  have hu₂e' : L619.mkW hW Z hu₂ = ((β₀ x₀ : ↥(L619.V0 hW Z P)) : IntMod W hW ⧸ L619.modSub hW Z) :=
    hu₂e
  have hu₁A : u₁ ∈ A := by
    rw [hu₁def, commutatorElement_def]
    exact A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hWA hw₀) b).mp hbA) (A.inv_mem hbA)
  have hu₁Q : u₁ ∈ blockQ A := by
    have hle : A ⊓ W ≤ pCoreOf 2 A :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, hAW hx⟩)
        ((B2F.isPGroup_of_isElemAbelian hW).to_le inf_le_right)
    exact hle ⟨hu₁A, hu₁⟩
  have hu₂U : u₂ ∈ blockU A := Subgroup.commutator_mem_commutator hu₁Q hbA
  have hbu : b * u₂ * b⁻¹ ≠ u₂ := by
    intro he
    have hc : b * u₂ * b⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hAW hbA) u₂).mp hu₂
    have h1 := L619.mkW_conj_ch6 hW θ β₀ hβeq (hPN hbP) hbk hu₂ hu₂e' hc
    rw [L619.mkW_congr_ch6 hW hc hu₂ he, hu₂e', hθb] at h1
    exact coreAct_sigmaB_ne_ch6 (hβinj (Subtype.ext h1)).symm
  have hc : a * u₂ * a⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hAW haA) u₂).mp hu₂
  have haZ : a * u₂ * a⁻¹ * u₂⁻¹ ∈ Z := by
    have h1 := L619.mkW_conj_ch6 hW θ β₀ hβeq (hPN haP) hak hu₂ hu₂e' hc
    rw [hθa, coreAct_sigmaA_ch6, ← hu₂e'] at h1
    exact (L619.mkW_eq_mkW_iff hW hc hu₂).mp h1
  have hvU : a * u₂ * a⁻¹ ∈ blockU A := conj_mem_blockU_ch6 haA hu₂U
  have hZA : ∀ x ∈ Z, x ∈ Subgroup.centralizer (A : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun g hg =>
      (Subgroup.mem_centralizer_iff.mp (hPZ (hAP hg)) x hx).symm
  have hker : ∀ {x : G} (hx : x ∈ blockU A), x ∈ Subgroup.centralizer (A : Set G) →
      β' ⟨x, hx⟩ = 1 := by
    intro x hx hxc
    rw [← MonoidHom.mem_ker, hβ'k, Subgroup.mem_subgroupOf]
    exact ⟨hx, hxc⟩
  have hβ'v : β' ⟨a * u₂ * a⁻¹, hvU⟩ = β' ⟨u₂, hu₂U⟩ := by
    have h1 := hker ((blockU A).mul_mem hvU ((blockU A).inv_mem hu₂U)) (hZA _ haZ)
    have h2 : (⟨a * u₂ * a⁻¹ * u₂⁻¹, (blockU A).mul_mem hvU ((blockU A).inv_mem hu₂U)⟩ :
        ↥(blockU A)) = ⟨a * u₂ * a⁻¹, hvU⟩ * ⟨u₂, hu₂U⟩⁻¹ := rfl
    rw [h2, map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  have hξ : Multiplicative.toAdd (β' ⟨u₂, hu₂U⟩) ≠ 0 := by
    intro h0
    have h1 : β' ⟨u₂, hu₂U⟩ = 1 := h0
    rw [← MonoidHom.mem_ker, hβ'k, Subgroup.mem_subgroupOf] at h1
    exact hbu (Subgroup.mem_centralizer_iff.mp h1.2 b hbA ▸ by group)
  have hfix := hβ'e ⟨a, haA⟩ ⟨u₂, hu₂U⟩ ⟨a * u₂ * a⁻¹, hvU⟩ rfl
  rw [hβ'v] at hfix
  have h2F : (2 : F) = 0 := by
    have hc0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
    rw [hF, Nat.cast_pow, Nat.cast_ofNat] at hc0
    exact pow_eq_zero_iff (by rintro rfl; simp at hF; exact absurd hF Fintype.one_lt_card.ne')
      |>.mp hc0
  have hpow : (⟨a, haA⟩ : ↥A) ^ 3 ^ ka = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hka)
  have hα1 : α ⟨a, haA⟩ = 1 :=
    eq_one_of_mulVec_ch6 h2F (by rw [← map_pow, hpow, map_one]) hξ hfix.symm
  have ha1 : (⟨a, haA⟩ : ↥A) = 1 := by
    have hmem : (⟨a, haA⟩ : ↥A) ∈ CFSG.pCore 2 ↥A := by rw [← hαk]; exact hα1
    exact L619.eq_one_of_two_three CFSG.pCore_isPGroup hmem hpow
  have ha1' : a = 1 := congrArg Subtype.val ha1
  have : (⟨a, haP⟩ : ↥P) = 1 := Subtype.ext ha1'
  rw [show ρ ⟨a, haP⟩ = θ (ψ ⟨a, haP⟩) from rfl, this, map_one, map_one] at haρ
  exact hσA1 haρ.symm

theorem lin2Excl619_holds :
    ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ) (y z : G)
      (T' D' : Subgroup G), Hyp6116 G T M L V n → Hyp611 G T' M L V n →
      Dat619 T M L V H n y z T' D' →
      ∀ (hW : IsElemAbelian 2 (ch619W T L V z))
        (Ks : Fin 1 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
          (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))),
        G6.IsTransvectionDecomposition (L619.img0 hW (ch6ZS T L V)
          (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks →
        Nonempty (↥(Ks 0) ≃* Equiv.Perm (Fin 5)) →
        ¬ (IsBlock2 (L619.threePart (conjClosure (conjSub y V) (ch619I T L V ⊔ T')))
            (L619.threePart (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) ∧
          ∃ f : ℕ, IsLin2Type (L619.threePart (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) f) := by
  intro G _ _ T M L V H n y z T' D' h hT' hd hW Ks hdec hK hlin
  obtain ⟨-, f, hf⟩ := hlin
  have c := hd.cfg
  have hY := hd.isY
  have hK0 : Ks 0 = L619.img0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) := by
    rw [← hdec.iSup_eq]
    refine le_antisymm (le_iSup Ks 0) (iSup_le fun j => ?_)
    rw [Subsingleton.elim j 0]
  obtain ⟨eK⟩ := hK
  have hcard : Nat.card (Ks 0) = 120 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have htype := hdec.type 0
  rw [hK0] at hcard htype
  obtain ⟨θ, β₀, hβeq, -, hβk⟩ := isSymNatural_five_of_card_ch6 htype hcard
  have hβinj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, natKer_five_eq_bot_ch6]
  have hVI : V ≤ ch619I T L V := fun x hx => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hw.1 hx
  have hWI : ch619W T L V z ≤ ch619I T L V := inf_le_left.trans
    (CFSG.Quasithin.conjClosure_le fun g hg v hv => (ch619I T L V).mul_mem
      ((ch619I T L V).mul_mem hg (hVI hv)) ((ch619I T L V).inv_mem hg))
  exact false_of_isLin2Type_threePart_ch6 hW (c.conjClosure_E_le_normWZX hY)
    (c.conjClosure_E_le_I hY) (hWI.trans (hY.I_le.trans (le_normalizer_conjClosure _ _))) θ β₀
    hβeq hβinj hf

end CFSG.Quasithin.H13
