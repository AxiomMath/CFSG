module

public import CFSG.Quasithin.H13.L32NLem1442a
public import CFSG.Quasithin.H13.L32NLem14324b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

open CFSG.Quasithin.F6.L28Res

theorem gb_word : ∀ k : G8, k.1.2.2.1 ≠ 0 →
    uHom (Multiplicative.ofAdd (GF8.ofNat' 3)) *
      (uHom (Multiplicative.ofAdd (k.1.1 / k.1.2.2.1)) * k *
        uHom (Multiplicative.ofAdd (GF8.ofNat' 6 / (k.1.2.2.1 * k.1.2.2.1))) * k⁻¹ *
        uHom (Multiplicative.ofAdd (k.1.1 / k.1.2.2.1))) = gb := by
  decide +kernel

theorem card_B : Fintype.card {k : G8 // k.1.2.2.1 = 0} = 56 := by
  decide +kernel

theorem B_two : ∀ k : G8, k.1.2.2.1 = 0 → k ^ 8 = 1 →
    k = uHom (Multiplicative.ofAdd k.1.2.1) := by
  decide +kernel

theorem ga_eq : ga = uHom (Multiplicative.ofAdd (GF8.ofNat' 1)) := rfl

theorem closure_eq_top_of_c {H : Subgroup G8} (hU : uHom.range ≤ H) {k : G8} (hkH : k ∈ H)
    (hk : k.1.2.2.1 ≠ 0) : H = ⊤ := by
  have hu : ∀ t, uHom t ∈ H := fun t => hU ⟨t, rfl⟩
  have hgb : gb ∈ H := by
    rw [← gb_word k hk]
    exact H.mul_mem (hu _) (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hu _) hkH) (hu _))
      (H.inv_mem hkH)) (hu _))
  have hga : ga ∈ H := by rw [ga_eq]; exact hu _
  rw [eq_top_iff, ← closure_eq_top, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact hga
  · exact hgb

theorem u_sq (t : Multiplicative GF8) : uHom t * uHom t = 1 := by
  rw [← map_mul]
  have : t * t = 1 := by
    revert t
    decide
  rw [this, map_one]

theorem exists_conj_U {X₈ : Subgroup G8} (hX : Nat.card X₈ = 8) :
    ∃ g : G8, ∀ x ∈ X₈, g * x * g⁻¹ ∈ uHom.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ∀ P : Subgroup G8, Nat.card P = 8 → IsPGroup 2 P ∧ ¬ 2 ∣ P.index := by
    intro P hP
    refine ⟨IsPGroup.of_card (n := 3) (by rw [hP]; norm_num), ?_⟩
    have h1 := P.card_mul_index
    rw [hP, card_G8] at h1
    have h2 : P.index = 63 := by omega
    rw [h2]
    decide
  have hUc : Nat.card uHom.range = 8 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective uHom_injective, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G8 ((hsyl X₈ hX).1.toSylow (hsyl X₈ hX).2)
    ((hsyl _ hUc).1.toSylow (hsyl _ hUc).2)
  have hS : (hsyl X₈ hX).1.toSylow (hsyl X₈ hX).2 = g⁻¹ • (hsyl _ hUc).1.toSylow (hsyl _ hUc).2 :=
    eq_inv_smul_iff.mpr hg
  refine ⟨g, fun x hx => ?_⟩
  have hx' : x ∈ (((hsyl X₈ hX).1.toSylow (hsyl X₈ hX).2 : Sylow 2 G8) : Subgroup G8) := hx
  rw [hS, Sylow.coe_subgroup_smul] at hx'
  obtain ⟨u, hu, he⟩ := hx'
  have he' : g⁻¹ * u * g⁻¹⁻¹ = x := by simpa [MulAut.conj_apply] using he
  rw [← he', show g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ = u by group]
  exact hu

@[expose] def stabSub {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (S : Submodule (ZMod 2) W) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {γ | ∀ w ∈ S, γ w ∈ S}
  mul_mem' {γ δ} hγ hδ w hw := hγ _ (hδ w hw)
  one_mem' w hw := hw
  inv_mem' {γ} hγ := by
    intro w hw
    have := Finite.of_injective (fun v : ↥S => (v : W)) Subtype.val_injective
    let f : ↥S → ↥S := fun v => ⟨γ v, hγ v v.2⟩
    have hf : Function.Injective f := fun v v' h => Subtype.ext (γ.injective (congrArg
      Subtype.val h))
    obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w, hw⟩
    have hv' : γ v = w := congrArg Subtype.val hv
    have e1 : γ⁻¹ w = v := by
      rw [← hv', ← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    rw [e1]
    exact v.2

theorem core11 {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (χ : G8 →* (W ≃ₗ[ZMod 2] W)) (hχ : Function.Injective χ)
    {X : Subgroup (W ≃ₗ[ZMod 2] W)} (hX : ∀ t, χ (uHom t) ∈ X)
    (hXχ : ∀ x ∈ X, ∃ t, χ (uHom t) = x)
    {y : W ≃ₗ[ZMod 2] W} (hyN : ∀ f : G8, ∃ f' : G8, y * χ f * y⁻¹ = χ f')
    {va vc : W} (hva : va ≠ 0) (hXa : ∀ x ∈ X, x va = va)
    (hXc : ∀ x ∈ X, x vc = vc ∨ x vc = vc + va) (hx₀ : ∃ x ∈ X, x vc = vc + va)
    (hya : y va = vc) (hyc : y vc = va + vc) (hfix : (∀ f, χ f va = va) → False) : False := by
  classical
  have : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun e => (e : W → W)) fun _ _ h => LinearEquiv.ext (congrFun h)
  set P : Submodule (ZMod 2) W := Submodule.span (ZMod 2) {va, vc} with hP
  have hvaP : va ∈ P := Submodule.subset_span (by simp)
  have hvcP : vc ∈ P := Submodule.subset_span (by simp)
  set St := stabSub P with hSt
  have hgenSt : ∀ γ : W ≃ₗ[ZMod 2] W, γ va ∈ P → γ vc ∈ P → γ ∈ St := by
    intro γ ha hc w hw
    refine Submodule.span_induction (p := fun w _ => γ w ∈ P) ?_ ?_ ?_ ?_ hw
    · rintro w (rfl | rfl)
      · exact ha
      · exact hc
    · rw [map_zero]; exact P.zero_mem
    · intro u v _ _ hu hv; rw [map_add]; exact P.add_mem hu hv
    · intro c u _ hu; rw [map_smul]; exact P.smul_mem c hu
  have hySt : y ∈ St := hgenSt y (by rw [hya]; exact hvcP) (by rw [hyc]; exact P.add_mem hvaP hvcP)
  have hXSt : X ≤ St := fun x hx => hgenSt x (by rw [hXa x hx]; exact hvaP) (by
    rcases hXc x hx with h | h
    · rw [h]; exact hvcP
    · rw [h]; exact P.add_mem hvcP hvaP)
  set M := Subgroup.closure ((X : Set (W ≃ₗ[ZMod 2] W)) ∪ {y}) with hM
  have hXM : X ≤ M := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hyM : y ∈ M := Subgroup.subset_closure (Or.inr rfl)
  have hMSt : M ≤ St := (Subgroup.closure_le _).mpr fun w hw => by
    rcases hw with hw | hw
    · exact hXSt hw
    · rw [Set.mem_singleton_iff.mp hw]; exact hySt
  have hPv : ∀ v ∈ P, v = 0 ∨ v = va ∨ v = vc ∨ v = va + vc := by
    intro v hv
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hv
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c₁ with rfl | rfl <;>
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c₂ with rfl | rfl <;> simp
  have hU8 : uHom.range ≤ M.comap χ := by
    rintro _ ⟨t, rfl⟩
    exact hXM (hX t)
  have hne : M.comap χ ≠ ⊤ := by
    intro htop
    apply hfix
    let _ : MulAction G8 W := MulAction.compHom W χ
    have hsmul : ∀ (f : G8) (w : W), f • w = χ f w := fun _ _ => rfl
    set S := MulAction.stabilizer G8 va with hS
    have horb : ∀ w ∈ MulAction.orbit G8 va, w = va ∨ w = vc ∨ w = va + vc := by
      rintro _ ⟨f, rfl⟩
      have hfM : χ f ∈ M := by
        have : f ∈ M.comap χ := by rw [htop]; trivial
        exact this
      have hP' : χ f va ∈ P := (hMSt hfM : ∀ w ∈ P, χ f w ∈ P) va hvaP
      dsimp only
      rw [hsmul]
      rcases hPv _ hP' with h | h | h | h
      · exact absurd ((χ f).injective (h.trans (map_zero _).symm)) hva
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hcardorb : Nat.card (MulAction.orbit G8 va) ≤ 3 := by
      have hsub : MulAction.orbit G8 va ⊆ ({va, vc, va + vc} : Finset W) := fun w hw => by
        rcases horb w hw with h | h | h <;> simp [h]
      calc Nat.card (MulAction.orbit G8 va)
          ≤ Nat.card ((({va, vc, va + vc} : Finset W) : Set W)) :=
            Nat.card_mono (Set.toFinite _) hsub
        _ = ({va, vc, va + vc} : Finset W).card := Nat.card_coe_set_eq _ |>.trans
            (Set.ncard_coe_finset _)
        _ ≤ 3 := Finset.card_le_three
    have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G8 va)
    rw [Nat.card_prod, card_G8] at hos
    have hScard : 504 ≤ 3 * Nat.card S := by
      rw [← hos]
      exact Nat.mul_le_mul_right _ hcardorb
    have hUS : uHom.range ≤ S := by
      rintro _ ⟨t, rfl⟩
      show χ (uHom t) va = va
      exact hXa _ (hX t)
    obtain ⟨k, hkS, hk⟩ : ∃ k ∈ S, k.1.2.2.1 ≠ 0 := by
      by_contra hall
      push Not at hall
      have hle : Nat.card S ≤ Fintype.card {k : G8 // k.1.2.2.1 = 0} := by
        rw [← Nat.card_eq_fintype_card]
        exact Nat.card_le_card_of_injective (fun s => ⟨s.1, hall s.1 s.2⟩)
          (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
      rw [card_B] at hle
      omega
    have hStop := closure_eq_top_of_c hUS hkS hk
    intro f
    have : f ∈ S := by rw [hStop]; trivial
    exact this
  have hB : ∀ f ∈ M.comap χ, f.1.2.2.1 = 0 := by
    intro f hf
    by_contra hc
    exact hne (closure_eq_top_of_c hU8 hf hc)
  have hyX : ∀ x ∈ X, y * x * y⁻¹ ∈ X := by
    intro x hx
    obtain ⟨t, rfl⟩ := hXχ x hx
    obtain ⟨f', hf'⟩ := hyN (uHom t)
    have hf'M : f' ∈ M.comap χ := by
      show χ f' ∈ M
      rw [← hf']
      exact M.mul_mem (M.mul_mem hyM (hXM (hX t))) (M.inv_mem hyM)
    have hf'8 : f' ^ 8 = 1 := by
      apply hχ
      rw [map_pow, ← hf', map_one]
      have h2 : (uHom t) ^ 8 = 1 := by
        rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, sq, u_sq, one_pow]
      rw [show (y * χ (uHom t) * y⁻¹) ^ 8 = y * χ (uHom t ^ 8) * y⁻¹ by
        rw [map_pow]; exact conj_pow, h2, map_one]
      group
    rw [hf', B_two f' (hB f' hf'M) hf'8]
    exact hX _
  have hyX' : ∀ x ∈ X, y⁻¹ * x * y ∈ X := by
    intro x hx
    have hinj : Function.Injective (fun z : X => (⟨y * z * y⁻¹, hyX z z.2⟩ : X)) := by
      intro z z' h
      have := congrArg Subtype.val h
      exact Subtype.ext (by simpa using this)
    obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨x, hx⟩
    have hz' : y * z * y⁻¹ = x := congrArg Subtype.val hz
    rw [← hz', show y⁻¹ * (y * (z : W ≃ₗ[ZMod 2] W) * y⁻¹) * y = z by group]
    exact z.2
  obtain ⟨x₀, hx₀X, hx₀⟩ := hx₀
  have h1 : x₀ vc = vc := by
    have h2 := hXa _ (hyX' x₀ hx₀X)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h2
    have h3 : x₀ (y va) = y va := by
      have := congrArg y h2
      rw [← LinearEquiv.mul_apply, mul_inv_cancel] at this
      exact this
    rwa [hya] at h3
  rw [h1] at hx₀
  apply hva
  have := congrArg (· - vc) hx₀
  simpa using this.symm

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx G T L V V₂ g a D)
include C

theorem false_of_concl11 (h12813 : Lemma12_8_13)
    (h11 : G112Concl11 (D.img (l32nH T V))) : False := by
  classical
  have hB := C.g111.toG101Hyp
  have H := C.g111
  set Γ := D.img (l32nH T V) with hΓ
  set X := D.img (CFSG.conjugate (l32nW T V V₂) g) with hX
  have : Finite (D.V ≃ₗ[ZMod 2] D.V) :=
    Finite.of_injective (fun e => (e : D.V → D.V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  have h11' := h11
  obtain ⟨hd8, ⟨φ⟩⟩ := h11
  set N : Subgroup ↥Γ := genFittingFStar ↥Γ with hN
  have hNn : N.Normal := A7Mod.genFittingFStar_normal' ↥Γ
  have : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 3) = Fintype.card CFSG.Quasithin.GF8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    rfl
  let ψ : ↥N ≃* G8 :=
    φ.trans ((CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hcard)).trans slEquiv)
  have hNcard : Nat.card N = 504 := by rw [Nat.card_congr ψ.toEquiv, card_G8]
  have hZ : Subgroup.center ↥N = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : ψ z ∈ Subgroup.center G8 := Subgroup.mem_center_iff.mpr fun y => by
      obtain ⟨y', rfl⟩ := ψ.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y']
    have h2 : Subgroup.center G8 = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have h3 : slEquiv.symm w ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
          CFSG.Quasithin.GF8) := Subgroup.mem_center_iff.mpr fun y => by
        obtain ⟨y', rfl⟩ := slEquiv.symm.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw y']
      rw [sl_center_eq_bot, Subgroup.mem_bot] at h3
      rw [Subgroup.mem_bot]
      simpa using congrArg slEquiv h3
    rw [h2, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact ψ.injective (h1.trans (map_one ψ).symm)
  let cN : ↥Γ →* MulAut ↥N := MulAut.conjNormal
  have hc : Function.Injective cN := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have hγC : γ ∈ Subgroup.centralizer (N : Set ↥Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := congrArg (fun f : MulAut ↥N => ((f ⟨n, hn⟩ : ↥N) : ↥Γ)) hγ
      simp only [cN, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc n * γ = γ * n * γ⁻¹ * γ := by rw [h1]
        _ = γ * n := by group
    have hγN : γ ∈ N := CFSG.Adapters.generalized_fitting_self_centralizing ↥Γ hγC
    have hγZ : (⟨γ, hγN⟩ : ↥N) ∈ Subgroup.center ↥N := Subgroup.mem_center_iff.mpr fun n =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hγC n n.2)
    rw [hZ, Subgroup.mem_bot] at hγZ
    exact congrArg Subtype.val hγZ
  have hAut : Nat.card (MulAut ↥N) = 1512 := by
    rw [Nat.card_congr (MulAut.congr ψ).toEquiv, card_mulAut]
  have hdvdΓ : Nat.card ↥Γ ∣ 1512 := by
    have h1 := Subgroup.card_subgroup_dvd_card cN.range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hc).toEquiv, hAut] at h1
  have hidx : N.index ∣ 3 := by
    have h1 := N.card_mul_index
    rw [hNcard] at h1
    obtain ⟨r, hr⟩ := hdvdΓ
    have h2 : 504 * N.index * r = 504 * 3 := by rw [h1]; linarith
    exact Dvd.intro r (by nlinarith)
  have hxN : ∀ x (hx : x ∈ X), (⟨x, C.X_le hx⟩ : ↥Γ) ∈ N := by
    intro x hx
    set q := QuotientGroup.mk' N (⟨x, C.X_le hx⟩ : ↥Γ) with hq
    have h2 : q ^ 2 = 1 := by
      rw [hq, ← map_pow, sq]
      have : (⟨x, C.X_le hx⟩ : ↥Γ) * ⟨x, C.X_le hx⟩ = 1 := Subtype.ext (hB.X_sq x hx)
      rw [this, map_one]
    have h3 : orderOf q ∣ N.index := by
      rw [Subgroup.index]
      exact orderOf_dvd_natCard q
    have h4 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h5 : orderOf q = 1 := by
      have := Nat.dvd_gcd h4 (h3.trans hidx)
      simpa using this
    rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5
    exact h5
  set χ₀ : G8 →* (D.V ≃ₗ[ZMod 2] D.V) :=
    Γ.subtype.comp (N.subtype.comp ψ.symm.toMonoidHom) with hχ₀
  have hχ₀inj : Function.Injective χ₀ :=
    Γ.subtype_injective.comp (N.subtype_injective.comp ψ.symm.injective)
  have hχ₀X : ∀ x ∈ X, ∃ f, χ₀ f = x := fun x hx =>
    ⟨ψ ⟨⟨x, C.X_le hx⟩, hxN x hx⟩, by simp [hχ₀]⟩
  have hNorm : ∀ γ ∈ Γ, ∀ f, ∃ f', γ * χ₀ f * γ⁻¹ = χ₀ f' := by
    intro γ hγ f
    have h1 : (⟨γ, hγ⟩ : ↥Γ) * (ψ.symm f : ↥Γ) * (⟨γ, hγ⟩ : ↥Γ)⁻¹ ∈ N :=
      hNn.conj_mem _ (ψ.symm f).2 _
    refine ⟨ψ ⟨_, h1⟩, ?_⟩
    simp [hχ₀]
  have hX8 : Nat.card X = 8 := by
    obtain ⟨k, hk⟩ := C.exists_card_X
    have hlt := L14324.lt_of_concl11 C.X_le hk h11'
    have hlow := C.lower
    rw [hd8] at hlow
    norm_num at hlow
    rw [hk] at hlt hlow ⊢
    have hk3 : 3 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hlow)
    have hk4 : k < 4 := by
      by_contra h4
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 4 ≤ k by omega)
      omega
    rw [show k = 3 by omega]
    norm_num
  set X₈ := X.comap χ₀ with hX₈
  have hX₈c : Nat.card X₈ = 8 := by
    rw [← hX8, hX₈, ← Subgroup.card_map_of_injective hχ₀inj, Subgroup.map_comap_eq,
      inf_eq_right.mpr fun x hx => (hχ₀X x hx).imp fun f hf => hf]
  obtain ⟨g₈, hg₈⟩ := exists_conj_U hX₈c
  set χ : G8 →* (D.V ≃ₗ[ZMod 2] D.V) := χ₀.comp (MulAut.conj g₈⁻¹).toMonoidHom with hχ
  have hχinj : Function.Injective χ := hχ₀inj.comp (MulAut.conj g₈⁻¹).injective
  have hχapp : ∀ f, χ f = χ₀ (g₈⁻¹ * f * g₈⁻¹⁻¹) := fun f => rfl
  have hsurjU : ∀ t, ∃ x ∈ X₈, g₈ * x * g₈⁻¹ = uHom t := by
    have hinj : Function.Injective (fun x : X₈ => (⟨g₈ * x * g₈⁻¹, hg₈ x x.2⟩ : uHom.range)) := by
      intro x x' h
      have := congrArg Subtype.val h
      exact Subtype.ext (by simpa using this)
    have hUc : Nat.card uHom.range = 8 := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective uHom_injective,
        Subgroup.card_top, Nat.card_eq_fintype_card]
      rfl
    have hbij : Function.Bijective (fun x : X₈ => (⟨g₈ * x * g₈⁻¹, hg₈ x x.2⟩ : uHom.range)) :=
      (Function.Injective.bijective_of_nat_card_le hinj (by rw [hUc, hX₈c]))
    intro t
    obtain ⟨x, hx⟩ := hbij.2 ⟨uHom t, t, rfl⟩
    exact ⟨x, x.2, congrArg Subtype.val hx⟩
  have hXU : ∀ t, χ (uHom t) ∈ X := by
    intro t
    obtain ⟨x, hx, hxe⟩ := hsurjU t
    rw [hχapp, ← hxe, show g₈⁻¹ * (g₈ * x * g₈⁻¹) * g₈⁻¹⁻¹ = x by group]
    exact hx
  have hXχ : ∀ x ∈ X, ∃ t, χ (uHom t) = x := by
    intro x hx
    obtain ⟨f, rfl⟩ := hχ₀X x hx
    obtain ⟨t, ht⟩ := hg₈ f hx
    refine ⟨t, ?_⟩
    rw [hχapp, ht, show g₈⁻¹ * (g₈ * f * g₈⁻¹) * g₈⁻¹⁻¹ = f by group]
  obtain ⟨_, S⟩ := C.base.set14
  have hV₂ := C.base.plane
  have hV₂4 : Nat.card V₂ = 4 := hV₂.1.2.1
  have hlt2 : V₂ < V := lt_of_le_of_ne hV₂.1.1 fun he => by rw [he, S.card_V] at hV₂4; omega
  obtain ⟨c, hcV, hc2⟩ := IsConcreteLE.exists_of_lt hlt2
  have haV₂ := C.aV₂
  have ha1 := C.a1
  have haV : a ∈ V := hV₂.1.1 haV₂
  obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
  have hzV₂ : z ∈ V₂ := hV₂.2 hz
  obtain ⟨l, -, -, hlz, hla, hlc⟩ := S.exists_rot (Subgroup.mem_inf.mp hz).1 haV hcV
    (fun he => ha1 (by rw [he]; exact one_mem _)) (fun he => hc2 (by rw [he]; exact one_mem _))
    (fun he => ha1 (by rw [he]; exact hz)) (fun he => hc2 (by rw [he]; exact hzV₂))
    (fun he => hc2 (by rw [← he]; exact haV₂))
    (fun he => hc2 (by rw [he]; exact V₂.mul_mem hzV₂ haV₂))
  have hlH : l ∈ l32nH T V := S.mem_g1 hz hz1 hlz
  set y : D.V ≃ₗ[ZMod 2] D.V := D.ρ ⟨l, H_N hlH⟩ with hy
  have hyΓ : y ∈ Γ := L128A.HatU.rho_mem_img D hlH (H_N hlH)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hya : y (D.π a) = D.π c := by
    rw [hy, D.ρ_π _ a (hVU haV)]
    exact congrArg D.π hla
  have hyc : y (D.π c) = D.π a + D.π c := by
    rw [hy, D.ρ_π _ c (hVU hcV)]
    rw [show l * c * l⁻¹ = a * c from hlc, D.π_mul a (hVU haV) c (hVU hcV)]
  have hcE : c ∈ l32nE T V V₂ g :=
    (h12813 G T L V 3 (fsuV1 T V) V₂ C.base.s1282 g C.base.gP C.base.gH).1 hcV
  have hcÊ : D.π c ∈ D.hat (l32nE T V V₂ g) := L128A.HatU.π_mem_hat D hcE (hVU hcV)
  have hπc0 : D.π c ≠ 0 := by
    rw [Ne, L128A.HatU.π_eq_zero_iff D (hVU hcV), C.base.zU]
    exact fun h => hc2 (hV₂.2 h)
  have hπca : D.π c ≠ D.π a := by
    intro he
    have h1 : D.π (a⁻¹ * c) = 0 := by
      rw [D.π_mul _ (hVU (V.inv_mem haV)) _ (hVU hcV), L128A.HatU.π_inv D (hVU haV), he,
        neg_add_cancel]
    rw [L128A.HatU.π_eq_zero_iff D (hVU (V.mul_mem (V.inv_mem haV) hcV)), C.base.zU] at h1
    apply hc2
    have : c = a * (a⁻¹ * c) := by group
    rw [this]
    exact V₂.mul_mem haV₂ (hV₂.2 h1)
  have hXc : ∀ x ∈ X, x (D.π c) = D.π c ∨ x (D.π c) = D.π c + D.π a := by
    intro x hx
    obtain ⟨f, -, hf⟩ := H.transvection x hx
    have h1 := hf ⟨D.π c, hcÊ⟩
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (f ⟨D.π c, hcÊ⟩) with h | h
    · left
      rw [h, zero_smul, add_zero] at h1
      exact h1
    · right
      rw [h, one_smul] at h1
      exact h1
  have hx₀ : ∃ x ∈ X, x (D.π c) = D.π c + D.π a := by
    have hspan : (⟨D.π c, hcÊ⟩ : D.hat (l32nE T V V₂ g)) ∉
        (ZMod 2) ∙ (⟨D.π a, H.mem_W⟩ : D.hat (l32nE T V V₂ g)) := by
      intro hmem
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
      have hr' : r • D.π a = D.π c := by
        have := congrArg Subtype.val hr
        simpa using this
      rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) r with rfl | rfl
      · exact hπc0 (by rw [← hr', zero_smul])
      · exact hπca (by rw [← hr', one_smul])
    obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hspan
    have hfv : f ⟨D.π a, H.mem_W⟩ = 0 :=
      LinearMap.mem_ker.1 (hker (Submodule.mem_span_singleton_self _))
    obtain ⟨x, hxX, hx⟩ := H.transvection_full f hfv
    have h1 := hx ⟨D.π c, hcÊ⟩
    have hf1 : f ⟨D.π c, hcÊ⟩ = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hf
    rw [hf1, one_smul] at h1
    exact ⟨x, hxX, h1⟩
  have hyN : ∀ f, ∃ f', y * χ f * y⁻¹ = χ f' := by
    intro f
    obtain ⟨f₁, hf₁⟩ := hNorm y hyΓ (g₈⁻¹ * f * g₈⁻¹⁻¹)
    refine ⟨g₈ * f₁ * g₈⁻¹, ?_⟩
    rw [hχapp, hχapp, hf₁, show g₈⁻¹ * (g₈ * f₁ * g₈⁻¹) * g₈⁻¹⁻¹ = f₁ by group]
  have hfix : (∀ f, χ f (D.π a) = D.π a) → False := by
    intro hall
    have hall₀ : ∀ f, χ₀ f (D.π a) = D.π a := fun f => by
      have := hall (g₈ * f * g₈⁻¹)
      rwa [hχapp, show g₈⁻¹ * (g₈ * f * g₈⁻¹) * g₈⁻¹⁻¹ = f by group] at this
    have horb : ∀ f, ∀ w ∈ MulAction.orbit Γ (D.π a), χ₀ f w = w := by
      rintro f _ ⟨γ, rfl⟩
      obtain ⟨f', hf'⟩ := hNorm (γ⁻¹ : ↥Γ) (γ⁻¹).2 f
      have h1 : (γ : D.V ≃ₗ[ZMod 2] D.V)⁻¹ * χ₀ f * γ = χ₀ f' := by simpa using hf'
      have h2 := hall₀ f'
      rw [← h1, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h2
      have h3 := congrArg (γ : D.V ≃ₗ[ZMod 2] D.V) h2
      rw [← LinearEquiv.mul_apply (γ : D.V ≃ₗ[ZMod 2] D.V), mul_inv_cancel] at h3
      exact h3
    have hone : ∀ f, χ₀ f = 1 := by
      intro f
      have hle : Submodule.span (ZMod 2) (MulAction.orbit Γ (D.π a)) ≤
          LinearMap.ker ((χ₀ f).toLinearMap - LinearMap.id) := by
        rw [Submodule.span_le]
        intro w hw
        simp [horb f w hw]
      rw [H.span_orbit] at hle
      ext w
      have := hle (Submodule.mem_top (x := w))
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe,
        LinearMap.id_apply, sub_eq_zero] at this
      simpa using this
    have h1 := hχ₀inj ((hone gb).trans (hone 1).symm)
    exact gen_facts_ab.2.2.1 h1
  exact core11 χ hχinj hXU hXχ hyN C.πa_ne (fun x hx => hB.X_fixes x hx) hXc hx₀ hya hyc hfix

end Ctx

end L1442

end CFSG.Quasithin.H13
