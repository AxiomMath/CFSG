module

public import CFSG.Quasithin.Vol2.Ch3Sec3Par32

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Par32
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

namespace CZCore

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_odd {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hT : IsPGroup 2 T) {y : G} (hy : y ∈ L ⊔ T) (ho : Odd (orderOf y)) : y ∈ L := by
  obtain ⟨ℓ, hℓ, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp hy
  obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
  have ha' : t ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hstep : ∀ n : ℕ, ∃ ℓ' ∈ L, (ℓ * t) ^ n = ℓ' * t ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨ℓ', hℓ', e⟩ := ih
      refine ⟨ℓ' * (t ^ n * ℓ * (t ^ n)⁻¹), L.mul_mem hℓ' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht n)) ℓ).mp hℓ
      · rw [pow_succ, e]
        group
  obtain ⟨ℓ', hℓ', e⟩ := hstep (2 ^ a)
  rw [ha', mul_one] at e
  have hcop : Nat.Coprime (2 ^ a) (orderOf (ℓ * t)) :=
    Nat.Coprime.pow_left a ((Nat.coprime_two_left).mpr ho)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, e]
  exact L.pow_mem hℓ' m

theorem cZ_core
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hshort : IsShort2 L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {Γ : Type} [Group Γ]
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Γ) {W : Type} [AddCommGroup W]
    (β : ↥(blockU L) →* Multiplicative W) (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (act : Γ → W → W) (hact0 : ∀ x, act x 0 = 0)
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ → Multiplicative.toAdd (β u') = act (ρ g) (Multiplicative.toAdd (β u)))
    {w₀ : W} {p : Subgroup Γ}
    (hfixT : ∀ v : W, (∀ t (ht : t ∈ T), act (ρ ⟨t, hTL ht⟩) v = v) → v = 0 ∨ v = w₀)
    (hstab : ∀ x : Γ, act x w₀ = w₀ → x ∈ p) (hp : ∀ x ∈ p, act x w₀ = w₀) :
    oTwoUpper (L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) =
      oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) p) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hUV : blockU L ≤ vPlus L T := h.blockU_le_vPlus h38 h39 hshort hTL
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  set Z := quasithinOmegaOneCenter T with hZdef
  have hMp := Hyp331.mPlus_eq_of_le hTL
  obtain ⟨-, -, -, ⟨-, hV4⟩⟩ := stmt3_3_7_of h38 h39 G T M L D h
  rw [hMp] at hV4
  have hVL : ⁅vPlus L T, L⁆ ≤ blockU L :=
    (Subgroup.commutator_mono hVQ le_rfl).trans (Hyp331.commutator_qL_le_blockU hshort hTL)
  have hZV : Z ≤ vPlus L T := le_conjClosure _ _
  have hUL : blockU L ≤ L := commutator_le_right_of_le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
  have hCZU : Z ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (blockU L : Set G) :=
    fun c hc => Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hUL hc.2)
  have hZdec : ∀ z ∈ Z, ∃ u ∈ Z ⊓ blockU L, ∃ c ∈ Z ⊓ Subgroup.centralizer (L : Set G),
      z = u * c := by
    intro z hz
    have h1 : z ∈ blockU L ⊔ Z ⊓ Subgroup.centralizer (L : Set G) := by
      have h2 := hZV hz
      rw [hV4] at h2
      exact (sup_le_sup_right hVL _) h2
    obtain ⟨u, hu, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCZU).mp h1
    refine ⟨u, ⟨?_, hu⟩, c, hc, rfl⟩
    have := Z.mul_mem hz (Z.inv_mem hc.1)
    rwa [mul_inv_cancel_right] at this
  have hcentZ : ∀ y ∈ L, (∀ u ∈ Z ⊓ blockU L, u * y = y * u) →
      y ∈ Subgroup.centralizer (Z : Set G) := by
    intro y hy hyU
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨u, hu, c, hc, rfl⟩ := hZdec z hz
    have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.mp hc.2 y hy).symm
    calc u * c * y = u * (c * y) := mul_assoc _ _ _
      _ = u * (y * c) := by rw [hcy]
      _ = (u * y) * c := (mul_assoc _ _ _).symm
      _ = (y * u) * c := by rw [hyU u hu]
      _ = y * (u * c) := mul_assoc _ _ _
  have hnot : ¬ Z ⊓ blockU L ≤ blockZ L := by
    intro hle
    apply h.not_L_le_centralizer h38 h39
    have hZL : Z ≤ Subgroup.centralizer (L : Set G) := by
      intro z hz
      obtain ⟨u, hu, c, hc, rfl⟩ := hZdec z hz
      exact Subgroup.mul_mem _ (hle hu).2 hc.2
    have hVc : vPlus L T ≤ Subgroup.centralizer (L : Set G) := by
      show conjClosure Z (mPlus L T) ≤ _
      rw [hMp]
      refine conjClosure_le fun ℓ hℓ z hz => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp (hZL hz) ℓ hℓ
      have e : ℓ * z * ℓ⁻¹ = z := by rw [h1]; group
      rw [e]
      exact hZL hz
    exact Subgroup.le_centralizer_iff.mp hVc
  obtain ⟨u₀, hu₀, hu₀Z⟩ := Set.not_subset.mp hnot
  let θ : ↥(blockU L) → W := fun u => Multiplicative.toAdd (β u)
  have hθb : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)),
      θ ⟨g * u * g⁻¹, Mod32.conj_mem_blockU g.2 u⟩ = act (ρ g) (θ u) :=
    fun g u => hβe g u ⟨g * u * g⁻¹, Mod32.conj_mem_blockU g.2 u⟩ rfl
  have hθ0 : ∀ u : ↥(blockU L), θ u = 0 → (u : G) ∈ blockZ L := by
    intro u hu
    have h1 : β u = 1 := Multiplicative.toAdd.injective (by rw [toAdd_one]; exact hu)
    have h2 : u ∈ β.ker := h1
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have hfixZ : ∀ (u : ↥(blockU L)), (u : G) ∈ Z → θ u = 0 ∨ θ u = w₀ := by
    intro u huZ
    apply hfixT
    intro t ht
    rw [← hθb ⟨t, hTL ht⟩ u]
    congr 2
    show t * u * t⁻¹ = u
    have h1 := Subgroup.mem_centralizer_iff.mp (hTZ ht) u huZ
    rw [← h1]
    group
  have hθu₀ : θ ⟨u₀, hu₀.2⟩ = w₀ := by
    rcases hfixZ ⟨u₀, hu₀.2⟩ hu₀.1 with h0 | h0
    · exact absurd (hθ0 _ h0) hu₀Z
    · exact h0
  have hle : L ⊓ Subgroup.centralizer (Z : Set G) ≤ pre ρ hLTN p := by
    intro y ⟨hyL, hyZ⟩
    refine (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_left hyL, ?_⟩
    apply hstab
    rw [← hθu₀, ← hθb ⟨y, hLTN (Subgroup.mem_sup_left hyL)⟩ ⟨u₀, hu₀.2⟩]
    congr 2
    show y * u₀ * y⁻¹ = u₀
    have h1 := Subgroup.mem_centralizer_iff.mp hyZ u₀ hu₀.1
    rw [← h1]
    group
  have hodd : ∀ y ∈ pre ρ hLTN p, Odd (orderOf y) →
      y ∈ L ⊓ Subgroup.centralizer (Z : Set G) := by
    intro y hy ho
    obtain ⟨hyLT, hyp⟩ := (mem_pre ρ hLTN).mp hy
    have hyL : y ∈ L := mem_of_odd hTL hT2 hyLT ho
    refine ⟨hyL, hcentZ y hyL fun u hu => ?_⟩
    have hfixw : act (ρ ⟨y, hLTN hyLT⟩) (θ ⟨u, hu.2⟩) = θ ⟨u, hu.2⟩ := by
      rcases hfixZ ⟨u, hu.2⟩ hu.1 with h0 | h0
      · rw [h0]
        exact hact0 _
      · rw [h0]
        exact hp _ hyp
    have hθeq : θ ⟨y * u * y⁻¹, Mod32.conj_mem_blockU (hLTN hyLT) ⟨u, hu.2⟩⟩ = θ ⟨u, hu.2⟩ :=
      (hθb ⟨y, hLTN hyLT⟩ ⟨u, hu.2⟩).trans hfixw
    have hβeq : β ⟨y * u * y⁻¹, Mod32.conj_mem_blockU (hLTN hyLT) ⟨u, hu.2⟩⟩ = β ⟨u, hu.2⟩ :=
      Multiplicative.toAdd.injective hθeq
    have hz' : y * u * y⁻¹ * u⁻¹ ∈ blockZ L := by
      have h1 : (⟨y * u * y⁻¹, Mod32.conj_mem_blockU (hLTN hyLT) ⟨u, hu.2⟩⟩ : ↥(blockU L)) *
          (⟨u, hu.2⟩ : ↥(blockU L))⁻¹ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hβeq, mul_inv_cancel]
      rw [hβk, Subgroup.mem_subgroupOf] at h1
      exact h1
    set z' := y * u * y⁻¹ * u⁻¹ with hz'def
    have hyz : y * z' = z' * y := Subgroup.mem_centralizer_iff.mp hz'.2 y hyL
    have hyu : y * u * y⁻¹ = z' * u := by
      rw [hz'def]
      group
    have hpow : ∀ k : ℕ, y ^ k * u * (y ^ k)⁻¹ = z' ^ k * u := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hc : y * z' ^ k = z' ^ k * y := ((show Commute y z' from hyz).pow_right k)
        calc y ^ (k + 1) * u * (y ^ (k + 1))⁻¹ = y * (y ^ k * u * (y ^ k)⁻¹) * y⁻¹ := by group
          _ = y * (z' ^ k * u) * y⁻¹ := by rw [ih]
          _ = (y * z' ^ k) * u * y⁻¹ := by group
          _ = (z' ^ k * y) * u * y⁻¹ := by rw [hc]
          _ = z' ^ k * (y * u * y⁻¹) := by group
          _ = z' ^ (k + 1) * u := by rw [hyu, pow_succ]; group
    have h1 := hpow (orderOf y)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
    have hz1 : z' ^ orderOf y = 1 := by
      have h2 := congrArg (· * u⁻¹) h1
      simp only [mul_inv_cancel, mul_inv_cancel_right] at h2
      exact h2.symm
    have hz2 : z' ^ 2 = 1 := hred.2.1.2 z' (hUV hz'.1)
    obtain ⟨j, hj⟩ := ho
    have hz'1 : z' = 1 := by
      rw [hj, pow_succ, pow_mul, hz2, one_pow, one_mul] at hz1
      exact hz1
    rw [hz'1, one_mul] at hyu
    calc u * y = (y * u * y⁻¹) * y := by rw [hyu]
      _ = y * u := by group
  refine le_antisymm (oTwoUpper_mono hle) ?_
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hx, ho⟩
  exact mem_oTwoUpper_of_odd (hodd x hx ho) ho

end CZCore

end CFSG.Quasithin.H13
