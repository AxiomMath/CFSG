module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LK
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LMod
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LW

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem key_of_rep
    (hG1 : Leaf_G1) (hG2 : Leaf_G2) (hG3 : Leaf_G3)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t a : G} (ctx : KCtx c t) (hd : AData c t a)
    {N₀ N₁ A Z₀ : Subgroup G} (hc : IsChiefPair (a2G2 K T) N₀ N₁)
    (hh : SecHyp (a2G2 K T) N₀ N₁)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (s : SecRep (a2G2 K T) N₀ N₁ W)
    (hA2 : IsPGroup 2 ↥A) (hN₁A : N₁ ≤ A) (hZ₀ : Z₀ ≤ N₀)
    {x : G} (hxK : x ∈ K) (hxn : ∃ n ∈ N₁, x * n * x⁻¹ * n⁻¹ ∉ N₀) :
    (∀ r ∈ pCoreOf 2 H, r ∉ a2TC K T →
      4 ≤ mIdx A (centralizerMod Z₀ A (Subgroup.zpowers r))) ∧
    (∀ r ∈ pCoreOf 2 H, r ∉ a2TC K T ⊔ K → r ∉ a2TC K T ⊔ K.map (MulAut.conj t).toMonoidHom →
      5 ≤ mIdx A (centralizerMod Z₀ A (Subgroup.zpowers r))) := by
  classical
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'def
  set a' := t * a * t⁻¹ with ha'
  have hKX : K ≤ a2G2 K T := (le_conjClosure K T).trans le_sup_left
  have hTX : t ∈ a2G2 K T := Subgroup.mem_sup_right ctx.tT
  have hK0X : conjClosure K T ≤ a2G2 K T := le_sup_left
  have hXN₀ : a2G2 K T ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T)
  have hTCX : a2TC K T ≤ a2G2 K T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hTC2 : IsPGroup 2 ↥(a2TC K T) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTCn : ∀ y ∈ a2G2 K T, ∀ p ∈ a2TC K T, y * p * y⁻¹ ∈ a2TC K T := fun y hy p hp =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (a2G2 K T) hy) p).mp hp
  have hρTC : ∀ p : ↥(a2G2 K T), (p : G) ∈ a2TC K T → s.ρ p = 1 :=
    SecRep.ρ_eq_one_of_normal_pgroup hc hh s hTCX hTC2 hTCn
  have hker₁ : CFSG.pCore 2 ↥K ≤ (s.ρ.comp (Subgroup.inclusion hKX)).ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hkO : (k : G) ∈ pCoreOf 2 K := Subgroup.mem_map_of_mem K.subtype hk
    exact hρTC (Subgroup.inclusion hKX k) (c.pCoreOf_K_le_TC h37 h38 hkO)
  let ρ₁ : (↥K ⧸ CFSG.pCore 2 ↥K) →* (W ≃ₗ[ZMod 2] W) :=
    QuotientGroup.lift _ (s.ρ.comp (Subgroup.inclusion hKX)) hker₁
  have hρ₁ : ∀ k : ↥K, ρ₁ (k : ↥K ⧸ CFSG.pCore 2 ↥K) = s.ρ (Subgroup.inclusion hKX k) :=
    fun k => rfl
  let τ : W ≃ₗ[ZMod 2] W := s.ρ ⟨t, hTX⟩
  let ρ₂ : (↥K ⧸ CFSG.pCore 2 ↥K) →* (W ≃ₗ[ZMod 2] W) := (MulAut.conj τ).toMonoidHom.comp ρ₁
  have hconjmem : ∀ l : ↥K, t * (l : G) * t⁻¹ ∈ a2G2 K T := fun l =>
    (a2G2 K T).mul_mem ((a2G2 K T).mul_mem hTX (hKX l.2)) ((a2G2 K T).inv_mem hTX)
  have hρ₂ : ∀ l : ↥K, ρ₂ (l : ↥K ⧸ CFSG.pCore 2 ↥K) =
      s.ρ ⟨t * (l : G) * t⁻¹, hconjmem l⟩ := by
    intro l
    show τ * ρ₁ (l : ↥K ⧸ CFSG.pCore 2 ↥K) * τ⁻¹ = _
    rw [hρ₁]
    show s.ρ ⟨t, hTX⟩ * s.ρ (Subgroup.inclusion hKX l) * (s.ρ ⟨t, hTX⟩)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hcomm : ∀ k l : ↥K ⧸ CFSG.pCore 2 ↥K, ρ₁ k * ρ₂ l = ρ₂ l * ρ₁ k := by
    intro k l
    induction k using QuotientGroup.induction_on with
    | H k =>
      induction l using QuotientGroup.induction_on with
      | H l =>
        rw [hρ₁, hρ₂]
        set g : ↥(a2G2 K T) := Subgroup.inclusion hKX k with hg
        set g' : ↥(a2G2 K T) := ⟨t * (l : G) * t⁻¹, hconjmem l⟩ with hg'
        have hl' : t * (l : G) * t⁻¹ ∈ K' := ⟨l, l.2, by simp [MulAut.conj_apply]⟩
        have he : ((g * g' * g⁻¹ * g'⁻¹ : ↥(a2G2 K T)) : G) ∈ a2TC K T := by
          have h1 : ⁅(k : G), t * (l : G) * t⁻¹⁆ ∈ ⁅K, K'⁆ :=
            Subgroup.commutator_mem_commutator k.2 hl'
          have h2 := c.pCoreOf_K_le_TC h37 h38 (ctx.comm h1)
          simpa [hg, hg', commutatorElement_def] using h2
        have h3 : s.ρ (g * g' * g⁻¹ * g'⁻¹) = 1 := hρTC _ he
        have e : g * g' = (g * g' * g⁻¹ * g'⁻¹) * (g' * g) := by group
        calc s.ρ g * s.ρ g' = s.ρ (g * g') := (map_mul _ _ _).symm
          _ = s.ρ ((g * g' * g⁻¹ * g'⁻¹) * (g' * g)) := by rw [← e]
          _ = s.ρ g' * s.ρ g := by rw [map_mul, h3, one_mul, map_mul]
  let FB : Subgroup G → W → Prop := fun J w =>
    ∀ j : ↥(a2G2 K T), (j : G) ∈ J → s.ρ j w = w
  have hF1 : ∀ w : W, w ∈ nfa2Fix ρ₁ ↔ FB K w := by
    intro w
    constructor
    · intro hw j hj
      have h1 := nfa2_mem_fix.mp hw ((⟨(j : G), hj⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)
      rw [hρ₁] at h1
      exact h1
    · intro hw
      rw [nfa2_mem_fix]
      intro k
      induction k using QuotientGroup.induction_on with
      | H k =>
        rw [hρ₁]
        exact hw _ k.2
  have hF2 : ∀ w : W, w ∈ nfa2Fix ρ₂ ↔ FB K' w := by
    intro w
    constructor
    · intro hw j hj
      obtain ⟨l, hl, hjl⟩ := hj
      have h1 := nfa2_mem_fix.mp hw ((⟨l, hl⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)
      rw [hρ₂] at h1
      have e : (⟨t * l * t⁻¹, hconjmem ⟨l, hl⟩⟩ : ↥(a2G2 K T)) = j := by
        apply Subtype.ext
        rw [← hjl]
        simp [MulAut.conj_apply]
      rw [← e]
      exact h1
    · intro hw
      rw [nfa2_mem_fix]
      intro k
      induction k using QuotientGroup.induction_on with
      | H l =>
        rw [hρ₂]
        exact hw _ ⟨l, l.2, by simp [MulAut.conj_apply]⟩
  have hF3 : ∀ (J : Subgroup G) (t₁ : G) (ht₁ : t₁ ∈ a2G2 K T), J ≤ a2G2 K T → ∀ w : W,
      FB J w → FB (J.map (MulAut.conj t₁).toMonoidHom) (s.ρ ⟨t₁, ht₁⟩ w) := by
    intro J t₁ ht₁ hJX w hw j hj
    obtain ⟨j₀, hj₀, hjj₀⟩ := hj
    set j₀' : ↥(a2G2 K T) := ⟨j₀, hJX hj₀⟩ with hj₀'
    have e : j * ⟨t₁, ht₁⟩ = ⟨t₁, ht₁⟩ * j₀' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hjj₀]
      simp [hj₀', MulAut.conj_apply, mul_assoc]
    calc s.ρ j (s.ρ ⟨t₁, ht₁⟩ w) = s.ρ (j * ⟨t₁, ht₁⟩) w := by rw [map_mul]; rfl
      _ = s.ρ (⟨t₁, ht₁⟩ * j₀') w := by rw [e]
      _ = s.ρ ⟨t₁, ht₁⟩ (s.ρ j₀' w) := by rw [map_mul]; rfl
      _ = s.ρ ⟨t₁, ht₁⟩ w := by rw [hw j₀' hj₀]
  obtain ⟨n, hnN₁, hxn'⟩ := hxn
  have hxne : s.ρ (Subgroup.inclusion hKX ⟨x, hxK⟩) ≠ 1 := by
    intro h1
    have h2 : s.ρ (Subgroup.inclusion hKX ⟨x, hxK⟩) (s.cl ⟨n, hnN₁⟩) = s.cl ⟨n, hnN₁⟩ := by
      rw [h1]; rfl
    exact hxn' ((SecRep.fix_iff hh s _ ⟨n, hnN₁⟩).mp h2)
  have h₁ : ∃ k, ρ₁ k ≠ 1 := ⟨(⟨x, hxK⟩ : ↥K), by rw [hρ₁]; exact hxne⟩
  have h₂ : ∃ k, ρ₂ k ≠ 1 := by
    refine ⟨(⟨x, hxK⟩ : ↥K), fun h1 => ?_⟩
    have h3 : ρ₁ (⟨x, hxK⟩ : ↥K) = 1 := by
      have : (MulAut.conj τ).toMonoidHom (ρ₁ (⟨x, hxK⟩ : ↥K)) = 1 := h1
      exact (map_eq_one_iff _ (MulAut.conj τ).injective).mp this
    rw [hρ₁] at h3
    exact hxne h3
  let Fp : Submodule (ZMod 2) W :=
    { carrier := {w | ∀ z : ↥(a2G2 K T), (z : G) ∈ conjClosure K T → s.ρ z w = w}
      add_mem' := fun {a b} ha hb z hz => by
        show s.ρ z (a + b) = a + b
        rw [map_add, ha z hz, hb z hz]
      zero_mem' := fun z hz => by
        show s.ρ z (0 : W) = 0
        exact map_zero _
      smul_mem' := fun c w hw z hz => by
        show s.ρ z (c • w) = c • w
        rw [map_smul, hw z hz] }
  have hFpinv : ∀ y : ↥(a2G2 K T), ∀ w ∈ Fp, s.ρ y w ∈ Fp := by
    intro y w hw z hz
    have hz' : ((y⁻¹ * z * y : ↥(a2G2 K T)) : G) ∈ conjClosure K T := by
      have := (Subgroup.mem_normalizer_iff.mp (hXN₀ ((a2G2 K T).inv_mem y.2)) (z : G)).mp hz
      simpa using this
    calc s.ρ z (s.ρ y w) = s.ρ (z * y) w := by rw [map_mul]; rfl
      _ = s.ρ (y * (y⁻¹ * z * y)) w := by congr 2; group
      _ = s.ρ y (s.ρ (y⁻¹ * z * y) w) := by rw [map_mul]; rfl
      _ = s.ρ y w := by rw [hw _ hz']
  have hFp : Fp = ⊥ ∨ Fp = ⊤ := SecRep.irreducible hc hh s Fp hFpinv
  have hFp_ne : Fp ≠ ⊤ := by
    intro h
    apply hxne
    refine LinearEquiv.ext fun w => ?_
    have hw : w ∈ Fp := by rw [h]; trivial
    exact hw _ (le_conjClosure K T hxK)
  have hfix : ∀ w : W, (∀ k, ρ₁ k w = w) → (∀ k, ρ₂ k w = w) → w = 0 := by
    intro w h1 h2
    have hw1 := (hF1 w).mp (nfa2_mem_fix.mpr h1)
    have hw2 := (hF2 w).mp (nfa2_mem_fix.mpr h2)
    have hw : w ∈ Fp := by
      intro z hz
      have hz' : (z : G) ∈ ((K ⊔ K' : Subgroup G) : Set G) := by rw [← ctx.K0]; exact hz
      rw [Subgroup.coe_mul_of_right_le_normalizer_left K K' ctx.K'N, Set.mem_mul] at hz'
      obtain ⟨k, hk, k', hk', hkk'⟩ := hz'
      have hkX : k ∈ a2G2 K T := hKX hk
      have hk'X : k' ∈ a2G2 K T := z.2 |> fun _ => by
        have : k' = k⁻¹ * (z : G) := by rw [← hkk']; group
        rw [this]
        exact (a2G2 K T).mul_mem ((a2G2 K T).inv_mem hkX) z.2
      have e : z = ⟨k, hkX⟩ * ⟨k', hk'X⟩ := Subtype.ext (by simpa using hkk'.symm)
      rw [e, map_mul]
      show s.ρ ⟨k, hkX⟩ (s.ρ ⟨k', hk'X⟩ w) = w
      rw [hw2 ⟨k', hk'X⟩ hk', hw1 ⟨k, hkX⟩ hk]
    rcases hFp with h | h
    · have := h ▸ hw
      exact (Submodule.mem_bot _).mp this
    · exact absurd h hFp_ne
  let S : Submodule (ZMod 2) W := nfa2Fix ρ₁ ⊔ nfa2Fix ρ₂
  have hmapB : ∀ k, (nfa2Fix ρ₂).map (ρ₁ k : W →ₗ[ZMod 2] W) = nfa2Fix ρ₂ :=
    nfa2_map_fix_eq (fun k l => (hcomm l k).symm)
  have hmapA : ∀ l, (nfa2Fix ρ₁).map (ρ₂ l : W →ₗ[ZMod 2] W) = nfa2Fix ρ₁ :=
    nfa2_map_fix_eq hcomm
  have hK'X : K' ≤ a2G2 K T := by
    have : K' ≤ conjClosure K T := by rw [ctx.K0]; exact le_sup_right
    exact this.trans hK0X
  have hP1 : ∀ k : ↥K, ∀ w ∈ S, s.ρ (Subgroup.inclusion hKX k) w ∈ S := by
    intro k w hw
    obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    refine S.add_mem ?_ ?_
    · have h1 : s.ρ (Subgroup.inclusion hKX k) a₀ = a₀ := by
        have := (nfa2_mem_fix.mp ha₀) (k : ↥K ⧸ CFSG.pCore 2 ↥K)
        rwa [hρ₁] at this
      rw [h1]
      exact Submodule.mem_sup_left ha₀
    · have h1 : (ρ₁ (k : ↥K ⧸ CFSG.pCore 2 ↥K) : W →ₗ[ZMod 2] W) b₀ ∈ nfa2Fix ρ₂ := by
        rw [← hmapB (k : ↥K ⧸ CFSG.pCore 2 ↥K)]
        exact Submodule.mem_map_of_mem hb₀
      have h2 : s.ρ (Subgroup.inclusion hKX k) b₀ ∈ nfa2Fix ρ₂ := by
        have h3 : ρ₁ (k : ↥K ⧸ CFSG.pCore 2 ↥K) b₀ ∈ nfa2Fix ρ₂ := h1
        rwa [hρ₁] at h3
      exact Submodule.mem_sup_right h2
  have hP2 : ∀ l : ↥K, ∀ w ∈ S, s.ρ ⟨t * (l : G) * t⁻¹, hconjmem l⟩ w ∈ S := by
    intro l w hw
    obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    refine S.add_mem ?_ ?_
    · have h1 : (ρ₂ (l : ↥K ⧸ CFSG.pCore 2 ↥K) : W →ₗ[ZMod 2] W) a₀ ∈ nfa2Fix ρ₁ := by
        rw [← hmapA (l : ↥K ⧸ CFSG.pCore 2 ↥K)]
        exact Submodule.mem_map_of_mem ha₀
      have h2 : s.ρ ⟨t * (l : G) * t⁻¹, hconjmem l⟩ a₀ ∈ nfa2Fix ρ₁ := by
        have h3 : ρ₂ (l : ↥K ⧸ CFSG.pCore 2 ↥K) a₀ ∈ nfa2Fix ρ₁ := h1
        rwa [hρ₂] at h3
      exact Submodule.mem_sup_left h2
    · have h1 : s.ρ ⟨t * (l : G) * t⁻¹, hconjmem l⟩ b₀ = b₀ := by
        have := (nfa2_mem_fix.mp hb₀) (l : ↥K ⧸ CFSG.pCore 2 ↥K)
        rwa [hρ₂] at this
      rw [h1]
      exact Submodule.mem_sup_right hb₀
  have hP3 : ∀ (t₁ : G) (ht₁ : t₁ ∈ T), ∀ w ∈ S,
      s.ρ ⟨t₁, Subgroup.mem_sup_right ht₁⟩ w ∈ S := by
    intro t₁ ht₁ w hw
    have ht₁X : t₁ ∈ a2G2 K T := Subgroup.mem_sup_right ht₁
    obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    have hA' := (hF1 a₀).mp ha₀
    have hB' := (hF2 b₀).mp hb₀
    have hA'' := hF3 K t₁ ht₁X hKX a₀ hA'
    have hB'' := hF3 K' t₁ ht₁X hK'X b₀ hB'
    refine S.add_mem ?_ ?_
    · rcases ctx.perm t₁ ht₁ with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1] at hA''
        exact Submodule.mem_sup_left ((hF1 _).mpr hA'')
      · rw [h1] at hA''
        exact Submodule.mem_sup_right ((hF2 _).mpr hA'')
    · rcases ctx.perm t₁ ht₁ with ⟨-, h1⟩ | ⟨-, h1⟩
      · rw [h1] at hB''
        exact Submodule.mem_sup_right ((hF2 _).mpr hB'')
      · rw [h1] at hB''
        exact Submodule.mem_sup_left ((hF1 _).mpr hB'')
  have hSinv : ∀ y : ↥(a2G2 K T), ∀ w ∈ S, s.ρ y w ∈ S := by
    intro y w hw
    have hy : (y : G) ∈ ((conjClosure K T ⊔ T : Subgroup G) : Set G) := y.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (conjClosure K T) T
      (le_normalizer_conjClosure K T), Set.mem_mul] at hy
    obtain ⟨z, hz, t₁, ht₁, hyzt⟩ := hy
    have hz' : z ∈ ((K ⊔ K' : Subgroup G) : Set G) := by rw [← ctx.K0]; exact hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K K' ctx.K'N, Set.mem_mul] at hz'
    obtain ⟨k, hk, k', hk', hzkk⟩ := hz'
    obtain ⟨l, hl, hll⟩ := hk'
    have hk'eq : k' = t * l * t⁻¹ := by rw [← hll]; simp [MulAut.conj_apply]
    have hyeq : y = Subgroup.inclusion hKX ⟨k, hk⟩ * ⟨t * l * t⁻¹, hconjmem ⟨l, hl⟩⟩ *
        ⟨t₁, Subgroup.mem_sup_right ht₁⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]
      rw [← hyzt, ← hzkk, hk'eq]
    rw [hyeq, map_mul, map_mul]
    exact hP1 ⟨k, hk⟩ _ (hP2 ⟨l, hl⟩ _ (hP3 t₁ ht₁ w hw))
  have hdich : ((∀ w : W, (∀ k, ρ₁ k w = w) → w = 0) ∧ (∀ w : W, (∀ k, ρ₂ k w = w) → w = 0)) ∨
      (∀ w : W, ∃ a b : W, (∀ k, ρ₁ k a = a) ∧ (∀ k, ρ₂ k b = b) ∧ w = a + b) := by
    rcases SecRep.irreducible hc hh s S hSinv with h | h
    · left
      have hA : nfa2Fix ρ₁ ≤ ⊥ := h ▸ le_sup_left
      have hB : nfa2Fix ρ₂ ≤ ⊥ := h ▸ le_sup_right
      exact ⟨fun w hw => (Submodule.mem_bot _).mp (hA (nfa2_mem_fix.mpr hw)),
        fun w hw => (Submodule.mem_bot _).mp (hB (nfa2_mem_fix.mpr hw))⟩
    · right
      intro w
      have hw : w ∈ S := by rw [h]; trivial
      obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := Submodule.mem_sup.mp hw
      exact ⟨a₀, b₀, nfa2_mem_fix.mp ha₀, nfa2_mem_fix.mp hb₀, hab.symm⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let abar : ↥K ⧸ CFSG.pCore 2 ↥K := ((⟨a, hd.aK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)
  have hab1 : abar ≠ 1 := by
    intro h1
    exact hd.a_not (CFSG.Quasithin.EmptyFaithfulMultiple.L15420.mk_eq_one_iff.mp h1)
  have hab2 : abar ^ 2 = 1 := by
    have : (QuotientGroup.mk ((⟨a, hd.aK⟩ : ↥K) ^ 2) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 :=
      CFSG.Quasithin.EmptyFaithfulMultiple.L15420.mk_eq_one_iff.mpr hd.a_sq
    rw [QuotientGroup.mk_pow] at this
    exact this
  have hord : orderOf abar = 2 := orderOf_eq_prime hab2 hab1
  obtain ⟨b1, b2, b3⟩ := nfa2_two_factor_bounds hG1 hG2 hG3 q c.q_prime c.q_mod
    (↥K ⧸ CFSG.pCore 2 ↥K) c.model W ρ₁ ρ₂ hcomm h₁ h₂ hfix hdich abar hord
  have hRX : ∀ r ∈ pCoreOf 2 H, r ∈ a2G2 K T := fun r hr =>
    c.H_le_G2 (CFSG.LieType.BorelTits.pCoreOf_le 2 H hr)
  have haX : a ∈ a2G2 K T := hKX hd.aK
  have ha'X : t * a * t⁻¹ ∈ a2G2 K T := hconjmem ⟨a, hd.aK⟩
  have hact1 : ρ₁ abar = s.ρ ⟨a, haX⟩ := rfl
  have hact2 : ρ₂ abar = s.ρ ⟨t * a * t⁻¹, ha'X⟩ := hρ₂ ⟨a, hd.aK⟩
  have hL4 : ∀ (r : G) (hr : r ∈ pCoreOf 2 H),
      Module.finrank (ZMod 2) (LinearMap.range ((s.ρ ⟨r, hRX r hr⟩).toLinearMap - LinearMap.id)) ≤
        mIdx A (centralizerMod Z₀ A (Subgroup.zpowers r)) :=
    fun r hr => SecRep.finrank_range_le_mIdx hh s hA2 hN₁A hZ₀ ⟨r, hRX r hr⟩
  have hTC1 : ∀ (u : G) (hu : u ∈ a2G2 K T), u ∈ a2TC K T → s.ρ ⟨u, hu⟩ = 1 :=
    fun u hu h => hρTC ⟨u, hu⟩ h
  constructor
  · intro r hr hrT
    rcases hd.R_cases h37 h38 ctx.tT ctx.tK hr with h | h | h | h
    · exact absurd h hrT
    ·
      have e : s.ρ ⟨r, hRX r hr⟩ = ρ₁ abar := by
        have e1 : (⟨r, hRX r hr⟩ : ↥(a2G2 K T)) = ⟨a, haX⟩ * ⟨a⁻¹ * r, (a2G2 K T).mul_mem
            ((a2G2 K T).inv_mem haX) (hRX r hr)⟩ := Subtype.ext (by simp)
        rw [e1, map_mul, hTC1 _ _ h, mul_one, hact1]
      have := hL4 r hr
      rw [e] at this
      omega
    ·
      have e : s.ρ ⟨r, hRX r hr⟩ = ρ₂ abar := by
        have e1 : (⟨r, hRX r hr⟩ : ↥(a2G2 K T)) = ⟨t * a * t⁻¹, ha'X⟩ *
            ⟨(t * a * t⁻¹)⁻¹ * r, (a2G2 K T).mul_mem ((a2G2 K T).inv_mem ha'X) (hRX r hr)⟩ :=
          Subtype.ext (by simp only [Subgroup.coe_mul]; group)
        rw [e1, map_mul, hTC1 _ _ h, mul_one, hact2]
      have := hL4 r hr
      rw [e] at this
      omega
    ·
      have e : s.ρ ⟨r, hRX r hr⟩ = ρ₁ abar * ρ₂ abar := by
        have hu : (t * a * t⁻¹)⁻¹ * (a⁻¹ * r) ∈ a2G2 K T :=
          (a2G2 K T).mul_mem ((a2G2 K T).inv_mem ha'X)
            ((a2G2 K T).mul_mem ((a2G2 K T).inv_mem haX) (hRX r hr))
        have e1 : (⟨r, hRX r hr⟩ : ↥(a2G2 K T)) = ⟨a, haX⟩ * ⟨t * a * t⁻¹, ha'X⟩ * ⟨_, hu⟩ :=
          Subtype.ext (by simp [mul_assoc])
        rw [e1, map_mul, map_mul, hTC1 _ _ h, mul_one, hact1, hact2]
      have := hL4 r hr
      rw [e] at this
      omega
  · intro r hr h1 h2
    have h := hd.mem_of_not_sup h37 h38 ctx.tT ctx.tK hr h1 h2
    have e : s.ρ ⟨r, hRX r hr⟩ = ρ₁ abar * ρ₂ abar := by
      have hu : (t * a * t⁻¹)⁻¹ * (a⁻¹ * r) ∈ a2G2 K T :=
        (a2G2 K T).mul_mem ((a2G2 K T).inv_mem ha'X)
          ((a2G2 K T).mul_mem ((a2G2 K T).inv_mem haX) (hRX r hr))
      have e1 : (⟨r, hRX r hr⟩ : ↥(a2G2 K T)) = ⟨a, haX⟩ * ⟨t * a * t⁻¹, ha'X⟩ * ⟨_, hu⟩ :=
        Subtype.ext (by simp [mul_assoc])
      rw [e1, map_mul, map_mul, hTC1 _ _ h, mul_one, hact1, hact2]
    have := hL4 r hr
    rw [e] at this
    omega

theorem a2_keyBounds
    (hG1 : Leaf_G1) (hG2 : Leaf_G2) (hG3 : Leaf_G3)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G))
    {A Z₀ : Subgroup G} (hA2 : IsPGroup 2 ↥A) (hAX : A ≤ a2G2 K T)
    (hXA : a2G2 K T ≤ Subgroup.normalizer (A : Set G))
    (hXZ : a2G2 K T ≤ Subgroup.normalizer (Z₀ : Set G)) (hZA : Z₀ ≤ A)
    {x : G} (hxK : x ∈ K) (hxodd : Odd (orderOf x)) (hx : ∃ a ∈ A, x * a * x⁻¹ * a⁻¹ ∉ Z₀) :
    (∀ r ∈ pCoreOf 2 H, r ∉ a2TC K T →
      4 ≤ mIdx A (centralizerMod Z₀ A (Subgroup.zpowers r))) ∧
    (∀ r ∈ pCoreOf 2 H, r ∉ a2TC K T ⊔ K → r ∉ a2TC K T ⊔ K.map (MulAut.conj t).toMonoidHom →
      5 ≤ mIdx A (centralizerMod Z₀ A (Subgroup.zpowers r))) := by
  obtain ⟨a, hd⟩ := c.exists_AData h5 h7 h9 h128 h37 h38 h39 ht
  have ctx := c.kctx h37 h38 ht htK
  have hKX : K ≤ a2G2 K T := (le_conjClosure K T).trans le_sup_left
  obtain ⟨N₀, N₁, hc, hZ₀, hN₁A, hn⟩ := exists_chiefPair hA2 hXA hXZ (hAX.trans hXZ) hZA
    (fun N _ hN => hAX.trans hN) (hKX hxK) hxodd hx
  have hh : SecHyp (a2G2 K T) N₀ N₁ := hc.secHyp (hA2.to_le hN₁A)
  obtain ⟨W, _, _, _, ⟨s⟩⟩ := exists_secRep hh
  exact key_of_rep hG1 hG2 hG3 h37 h38 c ctx hd hc hh s hA2 hN₁A hZ₀ hxK hn

end CFSG.Quasithin.H13.NFa2
