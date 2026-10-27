module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergJoint

public section

namespace CFSG.StandardType.ClassicalPosition.HeisRank

private lemma heisAb_pow_apply_of_forall {F V : Type} [Semiring F] [AddCommMonoid V]
    [Module F V] (e : V ≃ₗ[F] V) (c : F) (W : Submodule F V) (h : ∀ v ∈ W, e v = c • v) :
    ∀ n (v : V), v ∈ W → (e ^ n) v = c ^ n • v := by
  intro n
  induction n with
  | zero => intro v _; simp
  | succ n ih =>
      intro v hv
      rw [pow_succ', LinearEquiv.mul_apply, ih v hv, map_smul, h v hv, smul_smul, pow_succ]

private lemma heisAb_eq_of_le_iSup {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {ι : Type} {W : ι → Submodule F V} (htop : ⨆ i, W i = ⊤)
    (f : V →ₗ[F] V) (c : F) (h : ∀ i v, v ∈ W i → f v = c • v) (v : V) :
    f v = c • v := by
  have hle : (⨆ i, W i) ≤ LinearMap.ker (f - c • LinearMap.id) := by
    rw [iSup_le_iff]
    intro i x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      h i x hx, sub_self]
  have hv : v ∈ (⨆ i, W i) := by rw [htop]; exact Submodule.mem_top
  have := hle hv
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at this

theorem index_le_of_commute {F V G : Type} [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Group G] {p : ℕ} (hp : (p : F) ≠ 0)
    (φ : G →* (V ≃ₗ[F] V)) (hpow : ∀ g, φ g ^ p ∈ scalarAut F V)
    (hc : ∀ g h, φ g * φ h = φ h * φ g) :
    ((scalarAut F V).comap φ).index ≠ 0 ∧
      ((scalarAut F V).comap φ).index ≤ p ^ (Module.finrank F V - 1) := by
  classical
  obtain ⟨T, hT, W, χ, hne, hind, htop, hact⟩ := exists_joint_eigen hp φ hpow hc
  haveI : Fintype T := Fintype.ofFinite T
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hp (Nat.cast_zero)
  haveI : NeZero p := ⟨hp0⟩
  have hchi_ne : ∀ t (g : G), χ t g ≠ 0 := by
    intro t g hg
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne t)
    apply hw0
    have h := hact t g w hw
    rw [hg, zero_smul] at h
    exact (φ g).injective (by rw [h, map_zero])
  have hchi_mul : ∀ t (g h : G), χ t (g * h) = χ t g * χ t h := by
    intro t g h
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne t)
    have h2 : φ (g * h) w = (χ t g * χ t h) • w := by
      rw [map_mul, LinearEquiv.mul_apply, hact t h w hw, map_smul, hact t g w hw, smul_smul,
        mul_comm]
    rw [hact t (g * h) w hw] at h2
    exact (smul_left_injective F hw0) h2
  have hchi_one : ∀ t, χ t 1 = 1 := by
    intro t
    have h := hchi_mul t 1 1
    rw [mul_one] at h
    exact mul_left_cancel₀ (hchi_ne t 1) (by rw [mul_one]; exact h.symm)
  have hchi_pow_eq : ∀ t t' (g : G), (χ t g) ^ p = (χ t' g) ^ p := by
    intro t t' g
    obtain ⟨c, hc'⟩ := (mem_scalarAut_iff (g := φ g ^ p)).mp (hpow g)
    have key : ∀ t, (χ t g) ^ p = c := by
      intro t
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne t)
      have h1 : (φ g ^ p) w = (χ t g) ^ p • w :=
        heisAb_pow_apply_of_forall (φ g) (χ t g) (W t) (fun v hv => hact t g v hv) p w hw
      have h2 : (φ g ^ p) w = c • w := hc' w
      rw [h1] at h2
      exact (smul_left_injective F hw0) h2
    rw [key t, key t']
  let χ' : T → G →* Fˣ := fun t =>
    MonoidHom.mk' (fun g => Units.mk0 (χ t g) (hchi_ne t g)) fun g h =>
      Units.ext (by
        rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]
        exact hchi_mul t g h)
  have hχ'_val : ∀ t (g : G), ((χ' t g : Fˣ) : F) = χ t g := by
    intro t g
    rfl
  by_cases hTne : Nonempty T
  ·
    obtain ⟨t₀⟩ := hTne
    let ρ : G →* (T → Fˣ) :=
      { toFun := fun g t => χ' t g / χ' t₀ g
        map_one' := by
          funext t
          simp only [Pi.one_apply, map_one, div_eq_one]
        map_mul' := by
          intro g h
          funext t
          rw [Pi.mul_apply, map_mul, map_mul, div_mul_div_comm] }
    have hρ_t₀ : ∀ g, ρ g t₀ = 1 := by
      intro g
      change χ' t₀ g / χ' t₀ g = 1
      exact div_eq_one.mpr rfl
    have hρpow : ∀ g (t : T), (ρ g t) ^ p = 1 := by
      intro g t
      have hχp : (χ' t g) ^ p = (χ' t₀ g) ^ p := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hχ'_val t g, hχ'_val t₀ g]
        exact hchi_pow_eq t t₀ g
      change (χ' t g / χ' t₀ g) ^ p = 1
      rw [div_pow, hχp, div_eq_one]
    have hker_le : ρ.ker ≤ (scalarAut F V).comap φ := by
      intro g hg
      rw [Subgroup.mem_comap]
      have hg1 : ρ g = 1 := MonoidHom.mem_ker.mp hg
      have hχeq : ∀ t, χ t g = χ t₀ g := by
        intro t
        have h1 : (ρ g) t = 1 := by rw [hg1]; rfl
        have h2 : χ' t g = χ' t₀ g := div_eq_one.mp h1
        calc χ t g = ((χ' t g : Fˣ) : F) := (hχ'_val t g).symm
          _ = ((χ' t₀ g : Fˣ) : F) := congrArg (fun u : Fˣ => (u : F)) h2
          _ = χ t₀ g := hχ'_val t₀ g
      refine mem_scalarAut_iff.mpr ⟨χ t₀ g, fun v => ?_⟩
      change (φ g : V →ₗ[F] V) v = χ t₀ g • v
      exact heisAb_eq_of_le_iSup htop (φ g : V →ₗ[F] V) (χ t₀ g)
        (fun t v hv => by rw [LinearEquiv.coe_coe, ← hχeq t]; exact hact t g v hv) v
    have hcomap_le : (scalarAut F V).comap φ ≤ ρ.ker := by
      intro g hg
      rw [Subgroup.mem_comap] at hg
      obtain ⟨c, hc'⟩ := mem_scalarAut_iff.mp hg
      have hχall : ∀ t, χ t g = c := by
        intro t
        obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne t)
        have hthis := hc' w
        rw [hact t g w hw] at hthis
        exact (smul_left_injective F hw0) hthis
      rw [MonoidHom.mem_ker]
      funext t
      have hχ'eq : χ' t g = χ' t₀ g := by
        apply Units.ext
        rw [hχ'_val t g, hχ'_val t₀ g, hχall t, hχall t₀]
      change χ' t g / χ' t₀ g = 1
      rw [hχ'eq, div_eq_one]
    have hker_eq : (scalarAut F V).comap φ = ρ.ker := le_antisymm hcomap_le hker_le
    have hidx : ((scalarAut F V).comap φ).index = Nat.card ρ.range := by
      rw [hker_eq, Subgroup.index_ker]
    let μ : Subgroup Fˣ := rootsOfUnity p F
    have hμcard : Nat.card μ ≤ p := by
      change Nat.card (rootsOfUnity p F) ≤ p
      exact card_rootsOfUnity F p
    haveI : Fintype μ := Fintype.ofFinite μ
    have hρ_at_t₀ : ∀ f : ρ.range, f.1 t₀ = 1 := by
      intro f
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp f.2
      rw [← hg]
      exact hρ_t₀ g
    let σ : ρ.range → ({t : T // t ≠ t₀} → μ) := fun f t =>
      ⟨f.1 t, by
        rw [mem_rootsOfUnity]
        obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp f.2
        rw [← hg]
        exact hρpow g t⟩
    have hσinj : Function.Injective σ := by
      intro f f' hff'
      apply Subtype.ext
      funext t
      by_cases ht : t = t₀
      · have hf : f.1 t = 1 := by rw [ht]; exact hρ_at_t₀ f
        have hf' : f'.1 t = 1 := by rw [ht]; exact hρ_at_t₀ f'
        rw [hf, hf']
      · have h := congrFun hff' ⟨t, ht⟩
        exact congrArg Subtype.val h
    have hcard_ne : Nat.card {t : T // t ≠ t₀} = Fintype.card T - 1 := by
      rw [Nat.card_eq_fintype_card]
      have h := Fintype.card_subtype_compl (fun t : T => t = t₀)
      rw [Fintype.card_subtype_eq t₀] at h
      simpa using h
    have hcard_bound : Nat.card ρ.range ≤ p ^ (Fintype.card T - 1) := by
      calc Nat.card ρ.range ≤ Nat.card ({t : T // t ≠ t₀} → μ) :=
            Nat.card_le_card_of_injective σ hσinj
        _ = Nat.card μ ^ Nat.card {t : T // t ≠ t₀} := Nat.card_fun
        _ ≤ p ^ Nat.card {t : T // t ≠ t₀} := Nat.pow_le_pow_left hμcard _
        _ = p ^ (Fintype.card T - 1) := by rw [hcard_ne]
    have hdim : Fintype.card T ≤ Module.finrank F V := by
      haveI : Fintype {t : T // W t ≠ ⊥} := Fintype.ofFinite _
      have hle := hind.subtype_ne_bot_le_finrank
      have hcard : Fintype.card {t : T // W t ≠ ⊥} = Fintype.card T :=
        Fintype.card_congr (Equiv.subtypeUnivEquiv hne)
      rwa [hcard] at hle
    refine ⟨?_, ?_⟩
    · rw [hidx]
      exact Nat.card_ne_zero.mpr ⟨⟨1, ρ.range.one_mem⟩, Finite.of_injective σ hσinj⟩
    · rw [hidx]
      calc Nat.card ρ.range ≤ p ^ (Fintype.card T - 1) := hcard_bound
        _ ≤ p ^ (Module.finrank F V - 1) :=
            Nat.pow_le_pow_right (Nat.pos_of_ne_zero hp0) (Nat.sub_le_sub_right hdim 1)
  ·
    haveI : IsEmpty T := not_nonempty_iff.mp hTne
    have hbot : (⊤ : Submodule F V) = ⊥ := by rw [← htop, iSup_of_empty]
    haveI : Subsingleton V := ⟨fun a b => by
      have ha : a = 0 := by
        have : a ∈ (⊥ : Submodule F V) := by rw [← hbot]; exact Submodule.mem_top
        simpa using this
      have hb : b = 0 := by
        have : b ∈ (⊥ : Submodule F V) := by rw [← hbot]; exact Submodule.mem_top
        simpa using this
      rw [ha, hb]⟩
    have hcomap : (scalarAut F V).comap φ = ⊤ := by
      apply le_antisymm le_top
      intro g _
      rw [Subgroup.mem_comap]
      exact mem_scalarAut_iff.mpr ⟨1, fun v => Subsingleton.elim _ _⟩
    have hidx : ((scalarAut F V).comap φ).index = 1 := by
      rw [hcomap, Subgroup.index_top]
    have hfr : Module.finrank F V = 0 := Module.finrank_zero_of_subsingleton
    refine ⟨?_, ?_⟩
    · rw [hidx]; exact one_ne_zero
    · rw [hidx, hfr]; simp

end CFSG.StandardType.ClassicalPosition.HeisRank
