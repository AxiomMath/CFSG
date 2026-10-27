module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8210B
public import CFSG.Quasithin.Vol2.Ch8Sec2L8212A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8212C

variable {G : Type} [Group G]

theorem le_of_le_normalizer_82 [Finite G] {T X : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hX : IsPGroup 2 ↥X) (hTX : T ≤ Subgroup.normalizer (X : Set G)) : X ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(X ⊔ T) := IsPGroup.to_sup_of_normal_left' hX hT.1 hTX
  let S : Sylow 2 G := hT.1.toSylow hT.2
  have hS : (S : Subgroup G) = T := rfl
  have h2 : (S : Subgroup G) ≤ X ⊔ T := by
    rw [hS]
    exact le_sup_right
  have h3 := S.is_maximal' hp h2
  calc X ≤ X ⊔ T := le_sup_left
    _ = S := h3
    _ = T := hS

theorem mem_normalizer_commutator_82 {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_commutator, hA, hB]

theorem exists_mem_center_mod_82 [Finite G] {T N : Subgroup G} {z : G} (hT : IsPGroup 2 ↥T)
    (hNT : N ≤ T) (hTN : T ≤ Subgroup.normalizer (N : Set G))
    (hzc : z ∈ Subgroup.centralizer (T : Set G)) (hzN : Subgroup.zpowers z < N) :
    ∃ n ∈ N, n ∉ Subgroup.zpowers z ∧ ∀ t ∈ T, ⁅n, t⁆ ∈ Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Zq := (Subgroup.zpowers z).subgroupOf T with hZq
  have hZn : Zq.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : ∀ k : ℤ, (g : G) * z ^ k * (g : G)⁻¹ = z ^ k := by
      intro k
      have h1 : (g : G) * z = z * g := Subgroup.mem_centralizer_iff.mp hzc g g.2
      rw [(Commute.zpow_right h1 k).eq, mul_inv_cancel_right]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hk, hc]
    exact Subgroup.zpow_mem_zpowers z k
  set mk := QuotientGroup.mk' Zq with hmk
  have hQp : IsPGroup 2 (↥T ⧸ Zq) := hT.to_quotient Zq
  have : Group.IsNilpotent (↥T ⧸ Zq) := hQp.isNilpotent
  set Nb := (N.subgroupOf T).map mk with hNb
  have hNbn : Nb.Normal := by
    have : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTN
    exact this.map mk (QuotientGroup.mk'_surjective _)
  obtain ⟨n₀, hn₀N, hn₀z⟩ : ∃ n ∈ N, n ∉ Subgroup.zpowers z := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hzN) h
  have hNb1 : Nb ≠ ⊥ := by
    intro h
    have h1 : mk ⟨n₀, hNT hn₀N⟩ ∈ Nb := ⟨⟨n₀, hNT hn₀N⟩, hn₀N, rfl⟩
    rw [h, Subgroup.mem_bot, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at h1
    exact hn₀z h1
  obtain ⟨ν, hν1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hNb1)
  obtain ⟨hνN, hνZ⟩ := ν.2
  obtain ⟨n, hnN, hnν⟩ := hνN
  refine ⟨n, hnN, ?_, ?_⟩
  · intro hn
    apply hν1
    have h3 : (ν : ↥T ⧸ Zq) = 1 := by
      rw [← hnν, hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hn
    exact Subtype.ext h3
  · intro t ht
    have h1 := Subgroup.mem_center_iff.mp hνZ (mk ⟨t, ht⟩)
    rw [← hnν, ← map_mul, ← map_mul, hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    rw [Subgroup.mem_subgroupOf] at h1
    have e : (((⟨t, ht⟩ * n)⁻¹ * (n * ⟨t, ht⟩) : ↥T) : G) = (n : G)⁻¹ * t⁻¹ * n * t := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hnt : ((n : G) * t) * z = z * ((n : G) * t) :=
      Subgroup.mem_centralizer_iff.mp hzc _ (T.mul_mem n.2 ht)
    have h2 : ⁅(n : G), t⁆ = ((n : G) * t) * ((n : G)⁻¹ * t⁻¹ * n * t) * ((n : G) * t)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h2, ← hk, (Commute.zpow_right hnt k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers z k

variable {V : Subgroup G}

theorem mem_of_deriv_82 {T L K : Subgroup G} {z : ↥V}
    {W : Subgroup ↥V} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hCLV : L ⊓ Subgroup.centralizer (V : Set G) = V)
    (hTCL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hVT : V ≤ T) (hKL : K ≤ L)
    (hcoc : ∀ δ : MulAut ↥V → ↥V, (∀ g ∈ autOn L V, ∀ k ∈ autOn L V, δ (g * k) = δ g * g (δ k)) →
      (∀ r ∈ autOn K V, δ r ∈ Subgroup.zpowers z) →
      ∃ w ∈ W, ∀ g ∈ autOn L V, δ g = w * (g w)⁻¹)
    {x : G} (hx : x ∈ T ⊓ Subgroup.centralizer (V : Set G))
    (hxK : ∀ k ∈ K, ⁅x, k⁆ ∈ Subgroup.zpowers (z : G)) : ∃ w ∈ W, x = (w : G) := by
  classical
  have hcV : ∀ n : ↥(Subgroup.normalizer (V : Set G)), (n : G) ∈ L → ⁅x, (n : G)⁆ ∈ V :=
    fun n hn => commutator_mem_of_inf_centralizer_82 hTL hLV hCLV hx hn
  let δ : MulAut ↥V → ↥V := fun φ =>
    if h : φ ∈ autOn L V then ⟨⁅x, ((Classical.choose h : ↥(Subgroup.normalizer (V : Set G))) : G)⁆,
      hcV _ (Classical.choose_spec h).1⟩ else 1
  have hwd : ∀ n m : ↥(Subgroup.normalizer (V : Set G)), (n : G) ∈ L → (m : G) ∈ L →
      conjAct V n = conjAct V m → ⁅x, (n : G)⁆ = ⁅x, (m : G)⁆ := by
    intro n m hn hm hnm
    have hc1 : conjAct V (n⁻¹ * m) = 1 := by rw [map_mul, map_inv, hnm, inv_mul_cancel]
    have hcm : ((n⁻¹ * m : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ V :=
      hCLV.le ⟨L.mul_mem (L.inv_mem hn) hm, (conjAct_eq_one_iff_82 _).mp hc1⟩
    set c : G := ((n⁻¹ * m : ↥(Subgroup.normalizer (V : Set G))) : G) with hcdef
    have hm' : (m : G) = n * c := by
      rw [hcdef]
      simp
    have hxc : ⁅x, c⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hx.2 c hcm).symm
    rw [hm']
    have e : ⁅x, (n : G) * c⁆ = ⁅x, (n : G)⁆ * ((n : G) * ⁅x, c⁆ * (n : G)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, hxc, mul_one, mul_inv_cancel, mul_one]
  have hδ : ∀ n : ↥(Subgroup.normalizer (V : Set G)), ∀ hn : (n : G) ∈ L,
      δ (conjAct V n) = ⟨⁅x, (n : G)⁆, hcV n hn⟩ := by
    intro n hn
    have h : conjAct V n ∈ autOn L V := ⟨n, hn, rfl⟩
    simp only [δ, h, ↓reduceDIte]
    apply Subtype.ext
    exact hwd _ _ (Classical.choose_spec h).1 hn (Classical.choose_spec h).2
  have hcoc1 : ∀ g ∈ autOn L V, ∀ k ∈ autOn L V, δ (g * k) = δ g * g (δ k) := by
    rintro _ ⟨n, hn, rfl⟩ _ ⟨m, hm, rfl⟩
    have hn' : (n : G) ∈ L := hn
    have hm' : (m : G) ∈ L := hm
    rw [← map_mul, hδ (n * m) (L.mul_mem hn' hm'), hδ n hn', hδ m hm']
    apply Subtype.ext
    simp only [Subgroup.coe_mul, CFSG.QuasithinUnique.Setup.coe_conjAct_apply,
      commutatorElement_def]
    group
  have hcoc2 : ∀ r ∈ autOn K V, δ r ∈ Subgroup.zpowers z := by
    rintro _ ⟨n, hn, rfl⟩
    have hn' : (n : G) ∈ K := hn
    rw [hδ n (hKL hn')]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hxK _ hn')
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_zpow]
    exact hk
  obtain ⟨w, hwW, hw⟩ := hcoc δ hcoc1 hcoc2
  refine ⟨w, hwW, ?_⟩
  have hwl : ∀ l ∈ L, ⁅x, l⁆ = ⁅(w : G), l⁆ := by
    intro l hl
    have h1 := hw (conjAct V ⟨l, hLV hl⟩) ⟨⟨l, hLV hl⟩, hl, rfl⟩
    rw [hδ ⟨l, hLV hl⟩ hl] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv,
      CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h2
    rw [h2, commutatorElement_def]
    group
  have hmem : (w : G)⁻¹ * x ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨T.mul_mem (T.inv_mem (hVT w.2)) hx.1, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have h1 := hwl l hl
    simp only [commutatorElement_def] at h1
    have h2 : x * l * x⁻¹ = (w : G) * l * (w : G)⁻¹ := by
      have := congrArg (· * l) h1
      simpa [mul_assoc] using this
    calc l * ((w : G)⁻¹ * x) = (w : G)⁻¹ * ((w : G) * l * (w : G)⁻¹) * x := by group
      _ = (w : G)⁻¹ * (x * l * x⁻¹) * x := by rw [h2]
      _ = (w : G)⁻¹ * x * l := by group
  rw [hTCL, Subgroup.mem_bot] at hmem
  have := congrArg ((w : G) * ·) hmem
  simpa using this

end L8212C

end CFSG.Quasithin.H13
