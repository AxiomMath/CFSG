module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec11

open scoped commutatorElement

theorem eq_one_of_mem_closure_of_coprime {M : Type*} [Group M] [Finite M]
    (hM : ∀ u w : M, u * w = w * u)
    (K : Subgroup (MulAut M)) (hcop : Nat.Coprime (Nat.card K) (Nat.card M)) {m : M}
    (hmK : m ∈ Subgroup.closure {y : M | ∃ k ∈ K, ∃ z : M, y = k z * z⁻¹})
    (hm : ∀ k ∈ K, k m = m) : m = 1 := by
  let _ : CommGroup M := { ‹Group M› with mul_comm := hM }
  have : Finite (MulAut M) := Finite.of_injective (fun e : MulAut M => (e : M → M))
    (fun e f h => MulEquiv.ext (congrFun h))
  have : Fintype K := Fintype.ofFinite K
  let e : M →* M :=
    { toFun := fun y => ∏ k : K, (k : MulAut M) y
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul]
        exact Finset.prod_mul_distrib }
  have he : ∀ k ∈ K, ∀ z : M, e (k z * z⁻¹) = 1 := by
    intro k hk z
    have hshift : ∏ j : K, (j : MulAut M) (k z) = ∏ j : K, (j : MulAut M) z :=
      Fintype.prod_equiv (Equiv.mulRight ⟨k, hk⟩) _ _ (fun j => by simp [MulAut.mul_apply])
    simp only [e, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv, hshift, mul_inv_cancel]
  have hle : Subgroup.closure {y : M | ∃ k ∈ K, ∃ z : M, y = k z * z⁻¹} ≤ e.ker := by
    rw [Subgroup.closure_le]
    rintro y ⟨k, hk, z, rfl⟩
    exact he k hk z
  have h1 : e m = 1 := hle hmK
  have h2 : e m = m ^ Nat.card K := by
    simp only [e, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Finset.prod_congr rfl (fun (k : K) _ => hm k k.2), Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  rw [h2] at h1
  have hdK : orderOf m ∣ Nat.card K := orderOf_dvd_of_pow_eq_one h1
  have hdM : orderOf m ∣ Nat.card M := orderOf_dvd_natCard m
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdK hdM)

variable {G : Type*} [Group G]

theorem mem_of_commutator_mem_of_coprime [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {P V N S : Subgroup G} (hP : IsPGroup p P) (hVP : V ≤ P) (hPP : ⁅P, P⁆ ≤ V)
    (hNP : N ≤ Subgroup.normalizer (P : Set G)) (hNV : N ≤ Subgroup.normalizer (V : Set G))
    (hS : CFSG.ABGLocalTools.IsSylowOf p S N) (hSP : S ≤ P) (htop : P ≤ V ⊔ ⁅N, P⁆)
    {y : G} (hy : y ∈ P) (hfix : ∀ n ∈ N, n * y * n⁻¹ * y⁻¹ ∈ V) : y ∈ V := by
  have hVnorm : ∀ q ∈ P, ∀ v ∈ V, q * v * q⁻¹ ∈ V := by
    intro q hq v hv
    have hc : q * v * q⁻¹ * v⁻¹ ∈ V := hPP (Subgroup.commutator_mem_commutator hq (hVP hv))
    have e : q * v * q⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact V.mul_mem hc hv
  have hVn : (V.subgroupOf P).Normal := by
    constructor
    rintro ⟨v, hvP⟩ hv ⟨q, hq⟩
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact hVnorm q hq v hv
  have hcomm : ∀ u w : P ⧸ V.subgroupOf P, u * w = w * u := by
    intro u w
    induction u using QuotientGroup.induction_on with
    | H u =>
      induction w using QuotientGroup.induction_on with
      | H w =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have hc : (w : G)⁻¹ * (u : G)⁻¹ * ((w : G)⁻¹)⁻¹ * ((u : G)⁻¹)⁻¹ ∈ V :=
          hPP (Subgroup.commutator_mem_commutator (P.inv_mem w.2) (P.inv_mem u.2))
        simpa [mul_assoc] using hc
  set V' := V.subgroupOf P with hV'
  have hmap : ∀ n : N,
      V'.map ((P.normalizerMonoidHom ⟨n, hNP n.2⟩ : P ≃* P) : P →* P) = V' := by
    intro n
    ext ⟨z, hz⟩
    rw [Subgroup.mem_map, hV', Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨w, hw⟩, hwV, hwz⟩
      rw [Subgroup.mem_subgroupOf] at hwV
      have hz' : z = n * w * (n : G)⁻¹ := (congrArg Subtype.val hwz).symm
      show z ∈ V
      rw [hz']
      exact (Subgroup.mem_normalizer_iff.mp (hNV n.2) w).mp hwV
    · intro hzV
      have hw : (n : G)⁻¹ * z * n ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hNP n.2)) z).mp hz
        simpa using this
      refine ⟨⟨(n : G)⁻¹ * z * n, hw⟩, ?_, Subtype.ext (by simp [mul_assoc])⟩
      rw [Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hNV n.2)) z).mp hzV
      simpa using this
  let φ : N →* MulAut (P ⧸ V') :=
    { toFun := fun n => QuotientGroup.congr V' V' (P.normalizerMonoidHom ⟨n, hNP n.2⟩) (hmap n)
      map_one' := by
        ext u
        induction u using QuotientGroup.induction_on with
        | H u =>
          change ((⟨1 * (u : G) * 1⁻¹, _⟩ : P) : P ⧸ V') = (u : P ⧸ V')
          congr 1
          exact Subtype.ext (by simp)
      map_mul' := fun n₁ n₂ => by
        ext u
        induction u using QuotientGroup.induction_on with
        | H u =>
          change ((⟨(n₁ * n₂ : G) * u * (n₁ * n₂ : G)⁻¹, _⟩ : P) : P ⧸ V') =
            ((⟨(n₁ : G) * ((n₂ : G) * u * (n₂ : G)⁻¹) * (n₁ : G)⁻¹, _⟩ : P) : P ⧸ V')
          congr 1
          exact Subtype.ext (by simp only; group) }
  have hφ : ∀ (n : N) (z : P), φ n (z : P ⧸ V') =
      ((⟨n * z * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hNP n.2) z).mp z.2⟩ : P) :
        P ⧸ V') := fun _ _ => rfl
  have hker : S.subgroupOf N ≤ φ.ker := by
    intro n hn
    rw [Subgroup.mem_subgroupOf] at hn
    rw [MonoidHom.mem_ker]
    ext u
    induction u using QuotientGroup.induction_on with
    | H u =>
      rw [hφ, MulAut.one_apply, QuotientGroup.eq, hV', Subgroup.mem_subgroupOf]
      have hc : (n : G) * (u : G)⁻¹ * (n : G)⁻¹ * ((u : G)⁻¹)⁻¹ ∈ V :=
        hPP (Subgroup.commutator_mem_commutator (hSP hn) (P.inv_mem u.2))
      simpa [mul_assoc] using hc
  have hKcard : ¬ p ∣ Nat.card φ.range := by
    intro hdvd
    have h1 : Nat.card φ.range = φ.ker.index :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
    have h2 : φ.ker.index ∣ S.relIndex N := Subgroup.index_dvd_of_le hker
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).2.2 ((h1 ▸ hdvd).trans h2)
  have hMp : IsPGroup p (P ⧸ V') := hP.to_quotient V'
  obtain ⟨k, hk⟩ := hMp.exists_card_eq
  have hcop : Nat.Coprime (Nat.card φ.range) (Nat.card (P ⧸ V')) := by
    rw [hk]
    exact ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hKcard).symm.pow_right k
  set C := Subgroup.closure {u : P ⧸ V' | ∃ k ∈ φ.range, ∃ z : P ⧸ V', u = k z * z⁻¹} with hC
  have hT : P ≤ (C.comap (QuotientGroup.mk' V')).map P.subtype := by
    refine htop.trans (sup_le ?_ ?_)
    · intro v hv
      refine ⟨⟨v, hVP hv⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff _).mpr (by rw [hV', Subgroup.mem_subgroupOf]; exact hv)]
      exact C.one_mem
    · rw [Subgroup.commutator_le]
      intro n hn q hq
      have hnq : n * q * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hNP hn) q).mp hq
      refine ⟨⟨⁅n, q⁆, ?_⟩, ?_, rfl⟩
      · rw [commutatorElement_def]
        exact P.mul_mem hnq (P.inv_mem hq)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, QuotientGroup.mk'_apply]
        refine Subgroup.subset_closure ⟨φ ⟨n, hn⟩, ⟨⟨n, hn⟩, rfl⟩, ((⟨q, hq⟩ : P) : P ⧸ V'), ?_⟩
        rw [hφ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        congr 1
  have hyC : ((⟨y, hy⟩ : P) : P ⧸ V') ∈ C := by
    obtain ⟨w, hw, hwy⟩ := hT hy
    have : w = ⟨y, hy⟩ := Subtype.ext hwy
    rw [← this]
    exact hw
  have hfixK : ∀ k ∈ φ.range, k ((⟨y, hy⟩ : P) : P ⧸ V') = ((⟨y, hy⟩ : P) : P ⧸ V') := by
    rintro k ⟨n, rfl⟩
    rw [hφ, QuotientGroup.eq, hV', Subgroup.mem_subgroupOf]
    have hc := hfix n n.2
    have hc' : y⁻¹ * (n * y * (n : G)⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ ∈ V :=
      hVnorm y⁻¹ (P.inv_mem hy) _ (V.inv_mem hc)
    have e : ((n : G) * y * (n : G)⁻¹)⁻¹ * y = y⁻¹ * (n * y * (n : G)⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by
      group
    simpa [e] using hc'
  have h1 := eq_one_of_mem_closure_of_coprime hcomm φ.range hcop hyC hfixK
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [hV', Subgroup.mem_subgroupOf] at h2
  exact h2

end CFSG.RankThree.PartTwo.Sec11
