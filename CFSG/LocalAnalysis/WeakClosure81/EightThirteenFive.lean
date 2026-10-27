module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

open Finset

namespace CFSG.LocalAnalysis.WeakClosure81.Five

theorem perm_five_eq_one {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 5)
    (σ : Equiv.Perm Ω) (h2 : σ ^ 2 = 1) (hs : Equiv.Perm.sign σ = 1) (p q : Ω) (hpq : p ≠ q)
    (hp : σ p = p) (hq : σ q = q) : σ = 1 := by
  have hcyc : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) (by simpa using h2)
  obtain ⟨c, hc⟩ : ∃ c, σ.cycleType.card = c := ⟨_, rfl⟩
  rw [hc] at hcyc
  have hsum : σ.cycleType.sum = 2 * c := by
    rw [hcyc]; simp [mul_comm]
  have hsupp : σ.support.card = 2 * c := by rw [← Equiv.Perm.sum_cycleType, hsum]
  have hsub : σ.support ⊆ (Finset.univ \ {p, q}) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    refine ⟨fun hxp => ?_, fun hxq => ?_⟩
    · subst hxp; exact (Equiv.Perm.mem_support.mp hx) hp
    · subst hxq; exact (Equiv.Perm.mem_support.mp hx) hq
  have hcard : (Finset.univ \ {p, q} : Finset Ω).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hΩ,
      Finset.card_pair hpq]
  have hle : 2 * c ≤ 3 := hsupp ▸ (hcard ▸ Finset.card_le_card hsub)
  have hsgn := Equiv.Perm.sign_of_cycleType σ
  rw [hsum, hc, hs] at hsgn
  have hc01 : c = 0 ∨ c = 1 := by omega
  rcases hc01 with h0 | h1
  · have : σ.cycleType = 0 := by
      rw [hcyc, h0]; rfl
    exact Equiv.Perm.cycleType_eq_zero.mp this
  · exfalso
    rw [h1] at hsgn
    exact absurd hsgn (by decide)

theorem five_point_const {Ω W : Type*} [Fintype Ω] [DecidableEq Ω] [CommGroup W]
    (hcard : Fintype.card Ω = 5) (hW2 : ∀ w : W, w * w = 1) (f : Ω → W) (ω₁ : Ω)
    (htrans : ∀ ω₀ : Ω, ∃ (φ : W ≃* W) (π : Equiv.Perm Ω), π ω₁ = ω₀ ∧
      ∀ ω, f (π ω) = φ (f ω))
    (σa σb : Equiv.Perm Ω) (θa θb : W ≃* W)
    (hfa : ∀ ω, f (σa ω) = θa (f ω)) (hfb : ∀ ω, f (σb ω) = θb (f ω))
    (hσa : σa * σa = 1) (hcomm : σa * σb = σb * σa)
    (ha1 : σa ω₁ = ω₁) (hb1 : σb ω₁ = ω₁)
    (hua : ∀ ω, σa ω = ω → ω = ω₁) (hub : ∀ ω, σb ω = ω → ω = ω₁)
    (huab : ∀ ω, (σa * σb) ω = ω → ω = ω₁)
    (hfixed : ∀ x : W, θa x = x → θb x = x) :
    ∀ ω, f ω = f ω₁ := by
  classical
  have haa : ∀ ω : Ω, σa (σa ω) = ω := fun ω => by
    have := congrArg (fun σ : Equiv.Perm Ω => σ ω) hσa
    simpa [Equiv.Perm.mul_apply] using this
  have hab_apply : ∀ ω, (σa * σb) ω = σa (σb ω) := fun ω => rfl
  have hba_apply : ∀ ω, (σa * σb) ω = σb (σa ω) := fun ω => by
    rw [hcomm]; rfl
  have hrel : ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₁, f ω = 1 := by
    have hne : ∃ ω₂ : Ω, ω₂ ≠ ω₁ := by
      by_contra hcon
      push Not at hcon
      have : Fintype.card Ω ≤ 1 := Fintype.card_le_one_iff.mpr (fun x y => by
        rw [hcon x, hcon y])
      omega
    obtain ⟨ω₂, hω₂⟩ := hne
    have hfa' : σa ω₂ ≠ ω₂ := fun h => hω₂ (hua ω₂ h)
    have hfb' : σb ω₂ ≠ ω₂ := fun h => hω₂ (hub ω₂ h)
    have hfab' : (σa * σb) ω₂ ≠ ω₂ := fun h => hω₂ (huab ω₂ h)
    have h12 : σa ω₂ ≠ σb ω₂ := by
      intro h
      apply hfab'
      rw [hab_apply, ← h, haa]
    have h13 : σa ω₂ ≠ (σa * σb) ω₂ := by
      intro h
      rw [hab_apply] at h
      exact hfb' (σa.injective h).symm
    have h23 : σb ω₂ ≠ (σa * σb) ω₂ := by
      intro h
      rw [hba_apply] at h
      exact hfa' (σb.injective h).symm
    have hne1a : σa ω₂ ≠ ω₁ := fun h => hω₂ (σa.injective (h.trans ha1.symm))
    have hne1b : σb ω₂ ≠ ω₁ := fun h => hω₂ (σb.injective (h.trans hb1.symm))
    have hne1ab : (σa * σb) ω₂ ≠ ω₁ := by
      intro h
      apply hω₂
      have h' : (σa * σb) ω₂ = (σa * σb) ω₁ := by
        rw [h, hab_apply, hb1, ha1]
      exact (σa * σb).injective h'
    set S : Finset Ω := {ω₂, σa ω₂, σb ω₂, (σa * σb) ω₂} with hS
    have hSsub : S ⊆ (Finset.univ : Finset Ω).erase ω₁ := by
      intro x hx
      rw [hS] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rcases hx with rfl | rfl | rfl | rfl
      · exact hω₂
      · exact hne1a
      · exact hne1b
      · exact hne1ab
    have hScard : S.card = 4 := by
      rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using h23
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, h13⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hfa'.symm, hfb'.symm, hfab'.symm⟩
    have herase : (Finset.univ : Finset Ω).erase ω₁ = S := by
      refine (Finset.eq_of_subset_of_card_le hSsub ?_).symm
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard, hScard]
    rw [herase, hS]
    rw [Finset.prod_insert, Finset.prod_insert, Finset.prod_insert, Finset.prod_singleton]
    · set u : W := f ω₂ * f (σa ω₂) with hu
      have hau : θa u = u := by
        rw [hu, map_mul, ← hfa, ← hfa, haa, mul_comm]
      have hbu : θb u = u := hfixed u hau
      have hbu' : θb u = f (σb ω₂) * f ((σa * σb) ω₂) := by
        rw [hu, map_mul, ← hfb, ← hfb, hba_apply]
      have h4 : f ω₂ * (f (σa ω₂) * (f (σb ω₂) * f ((σa * σb) ω₂))) = u * u := by
        have h5 : u * (f (σb ω₂) * f ((σa * σb) ω₂)) = u * u := by rw [← hbu', hbu]
        rw [← h5, hu, mul_assoc]
      rw [h4, hW2]
    · simp only [Finset.mem_singleton]
      exact h23
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, h13⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hfa'.symm, hfb'.symm, hfab'.symm⟩
  have hrel' : ∀ ω₀ : Ω, ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₀, f ω = 1 := by
    intro ω₀
    obtain ⟨φ, π, hπ, hfπ⟩ := htrans ω₀
    have hprod : ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₁, f (π ω) =
        ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₀, f ω := by
      refine Finset.prod_equiv π ?_ ?_
      · intro i
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        rw [← hπ]
        exact not_congr π.injective.eq_iff.symm
      · intro i _
        rfl
    rw [← hprod]
    have h1 : ∏ ω ∈ (Finset.univ : Finset Ω).erase ω₁, f (π ω) =
        φ (∏ ω ∈ (Finset.univ : Finset Ω).erase ω₁, f ω) := by
      rw [map_prod]
      exact Finset.prod_congr rfl fun ω _ => hfπ ω
    rw [h1, hrel, map_one]
  intro ω
  have h1 := Finset.mul_prod_erase (Finset.univ : Finset Ω) f (Finset.mem_univ ω)
  have h2 := Finset.mul_prod_erase (Finset.univ : Finset Ω) f (Finset.mem_univ ω₁)
  rw [hrel' ω, mul_one] at h1
  rw [hrel' ω₁, mul_one] at h2
  rw [h1, h2]

section Setup

variable {G : Type*} [Group G]

structure FiveSetup (K K₁ N : Subgroup G) : Prop where
  le : K₁ ≤ K
  nle : N ≤ K₁
  normal : (N.subgroupOf K).Normal
  index : K₁.relIndex K = 5
  kn1 : ∀ B : Subgroup G, N ≤ B → B ≤ K → (B.subgroupOf K).Normal → B = N ∨ B = K
  kn2 : ∃ k₁ ∈ K, ∃ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∉ N

abbrev Cosets (K K₁ : Subgroup G) : Type _ := ↥K ⧸ K₁.subgroupOf K

variable {K K₁ N : Subgroup G}

theorem FiveSetup.card_cosets (S : FiveSetup K K₁ N) : Nat.card (Cosets K K₁) = 5 := by
  rw [← Subgroup.index_eq_card]
  exact S.index

theorem FiveSetup.core (S : FiveSetup K K₁ N) {y : G} (hy : y ∈ K)
    (h : ∀ g ∈ K, g * y * g⁻¹ ∈ K₁) : y ∈ N := by
  have hmem : ∀ x : ↥K, x ∈ (K₁.subgroupOf K).normalCore ↔ ∀ g ∈ K, g * (x : G) * g⁻¹ ∈ K₁ := by
    intro x
    constructor
    · intro hx g hg
      exact hx ⟨g, hg⟩
    · intro hx b
      exact hx b b.2
  set Nc : Subgroup ↥K := (K₁.subgroupOf K).normalCore with hNc
  set B : Subgroup G := Nc.map K.subtype with hB
  have hBK : B ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hBsub : B.subgroupOf K = Nc :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective Nc
  have hBnorm : (B.subgroupOf K).Normal := by
    rw [hBsub]
    infer_instance
  have hNK : N ≤ K := S.nle.trans S.le
  have hNnorm : K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp S.normal
  have hNB : N ≤ B := by
    intro n hn
    refine ⟨⟨n, hNK hn⟩, (hmem ⟨n, hNK hn⟩).mpr fun g hg => ?_, rfl⟩
    exact S.nle ((Subgroup.mem_normalizer_iff.mp (hNnorm hg) n).1 hn)
  rcases S.kn1 B hNB hBK hBnorm with hBN | hBK'
  · have hyB : y ∈ B := ⟨⟨y, hy⟩, (hmem ⟨y, hy⟩).mpr h, rfl⟩
    rw [hBN] at hyB
    exact hyB
  · exfalso
    have hK1 : K ≤ K₁ := by
      intro x hx
      have hxB : x ∈ B := hBK' ▸ hx
      obtain ⟨x', hx', rfl⟩ := hxB
      have := (hmem x').mp hx' 1 K.one_mem
      simpa using this
    have h1 := Subgroup.relIndex_eq_one.mpr hK1
    rw [S.index] at h1
    norm_num at h1

theorem FiveSetup.toPerm_eq_one_iff (S : FiveSetup K K₁ N) (k : ↥K) :
    (MulAction.toPerm k : Equiv.Perm (Cosets K K₁)) = 1 ↔ (k : G) ∈ N := by
  have hNK : N ≤ K := S.nle.trans S.le
  have hNnorm : K ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp S.normal
  constructor
  · intro h
    refine S.core k.2 fun g hg => ?_
    have h1 : k • (QuotientGroup.mk (⟨g, hg⟩⁻¹ : ↥K) : Cosets K K₁) =
        QuotientGroup.mk (⟨g, hg⟩⁻¹ : ↥K) := by
      have := congrArg (fun σ : Equiv.Perm (Cosets K K₁) =>
        σ (QuotientGroup.mk (⟨g, hg⟩⁻¹ : ↥K))) h
      simpa using this
    have h2 : (QuotientGroup.mk (k * (⟨g, hg⟩⁻¹ : ↥K)) : Cosets K K₁) =
        QuotientGroup.mk (⟨g, hg⟩⁻¹ : ↥K) := h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    have h3 : g * (k : G)⁻¹ * g⁻¹ ∈ K₁ := by simpa [mul_assoc] using h2
    have h4 := K₁.inv_mem h3
    simpa [mul_assoc] using h4
  · intro hk
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk (k * g) : Cosets K K₁) = QuotientGroup.mk g
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 : (g : G)⁻¹ * (k : G)⁻¹ * (g : G)⁻¹⁻¹ ∈ N :=
        (Subgroup.mem_normalizer_iff.mp (hNnorm (K.inv_mem g.2)) (k : G)⁻¹).1
          (N.inv_mem hk)
      have h2 := S.nle h1
      simpa [mul_assoc] using h2

theorem FiveSetup.sign_eq_one [Fintype (Cosets K K₁)] [DecidableEq (Cosets K K₁)]
    (S : FiveSetup K K₁ N) (k : ↥K) :
    Equiv.Perm.sign (MulAction.toPerm k : Equiv.Perm (Cosets K K₁)) = 1 := by
  set ε : ↥K →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom ↥K (Cosets K K₁)) with hε
  have hεapp : ∀ x : ↥K, ε x = Equiv.Perm.sign (MulAction.toPerm x : Equiv.Perm (Cosets K K₁)) :=
    fun x => rfl
  set B : Subgroup G := ε.ker.map K.subtype with hB
  have hBK : B ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hBsub : B.subgroupOf K = ε.ker :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective ε.ker
  have hBnorm : (B.subgroupOf K).Normal := by
    rw [hBsub]
    exact MonoidHom.normal_ker ε
  have hNK : N ≤ K := S.nle.trans S.le
  have hNB : N ≤ B := by
    intro n hn
    have h1 : ε ⟨n, hNK hn⟩ = 1 := by
      rw [hεapp, (S.toPerm_eq_one_iff ⟨n, hNK hn⟩).mpr hn]
      exact map_one _
    exact ⟨⟨n, hNK hn⟩, h1, rfl⟩
  rcases S.kn1 B hNB hBK hBnorm with hBN | hBK'
  · exfalso
    obtain ⟨k₁, hk₁, k₂, hk₂, hnot⟩ := S.kn2
    apply hnot
    rw [← hBN]
    have h1 : ε (⟨k₁, hk₁⟩ * ⟨k₂, hk₂⟩ * ⟨k₁, hk₁⟩⁻¹ * ⟨k₂, hk₂⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [mul_comm (ε ⟨k₁, hk₁⟩) (ε ⟨k₂, hk₂⟩)]
      group
    exact ⟨_, h1, rfl⟩
  · have hkB : (k : G) ∈ B := by
      rw [hBK']
      exact k.2
    obtain ⟨x, hx, hxk⟩ := hkB
    have hxk' : x = k := Subtype.ext hxk
    have h1 : ε x = 1 := hx
    rw [hxk'] at h1
    exact h1

theorem FiveSetup.mem_of_two_fixed [Fintype (Cosets K K₁)] [DecidableEq (Cosets K K₁)]
    (S : FiveSetup K K₁ N) (k : ↥K) (hk2 : ((k * k : ↥K) : G) ∈ N) (p q : Cosets K K₁)
    (hpq : p ≠ q) (hp : k • p = p) (hq : k • q = q) : (k : G) ∈ N := by
  have hcard : Fintype.card (Cosets K K₁) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.card_cosets
  have h2 : (MulAction.toPerm k : Equiv.Perm (Cosets K K₁)) ^ 2 = 1 := by
    rw [pow_two]
    have h3 := (S.toPerm_eq_one_iff (k * k)).mpr hk2
    have h4 : (MulAction.toPermHom ↥K (Cosets K K₁)) (k * k) = 1 := h3
    rw [map_mul] at h4
    exact h4
  have h1 := perm_five_eq_one hcard (MulAction.toPerm k) h2 (S.sign_eq_one k) p q hpq hp hq
  exact (S.toPerm_eq_one_iff k).mp h1

end Setup

section Conj

variable {G : Type*} [Group G]

@[expose] def conjAut (U : Subgroup G) (k : G) (hk : k ∈ Subgroup.normalizer (U : Set G)) :
    ↥U ≃* ↥U where
  toFun u := ⟨k * u * k⁻¹, (Subgroup.mem_normalizer_iff.mp hk u).1 u.2⟩
  invFun u := ⟨k⁻¹ * u * k, by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (U : Set G)).inv_mem hk) u).1
      u.2
    simpa using this⟩
  left_inv u := by ext; simp [mul_assoc]
  right_inv u := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem coe_conjAut (U : Subgroup G) (k : G) (hk : k ∈ Subgroup.normalizer (U : Set G))
    (u : ↥U) : ((conjAut U k hk u : ↥U) : G) = k * u * k⁻¹ := rfl

variable {K K₁ : Subgroup G}

@[expose] def conjPerm (K K₁ : Subgroup G) (a : G) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (haK₁ : a ∈ Subgroup.normalizer (K₁ : Set G)) : Equiv.Perm (Cosets K K₁) where
  toFun := Quotient.map' (conjAut K a haK) (fun x y h => QuotientGroup.leftRel_apply.mpr (by
    have h' := QuotientGroup.leftRel_apply.mp h
    rw [Subgroup.mem_subgroupOf] at h' ⊢
    have h'' := (Subgroup.mem_normalizer_iff.mp haK₁ _).1 h'
    simpa [coe_conjAut, mul_assoc] using h''))
  invFun := Quotient.map' (conjAut K a⁻¹ ((Subgroup.normalizer (K : Set G)).inv_mem haK))
    (fun x y h => QuotientGroup.leftRel_apply.mpr (by
    have h' := QuotientGroup.leftRel_apply.mp h
    rw [Subgroup.mem_subgroupOf] at h' ⊢
    have h'' := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K₁ : Set G)).inv_mem haK₁)
      _).1 h'
    simpa [coe_conjAut, mul_assoc] using h''))
  left_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk g
      congr 1
      ext
      simp [coe_conjAut, mul_assoc]
  right_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk g
      congr 1
      ext
      simp [coe_conjAut, mul_assoc]

theorem conjPerm_mk (a : G) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (haK₁ : a ∈ Subgroup.normalizer (K₁ : Set G)) (k : ↥K) :
    conjPerm K K₁ a haK haK₁ (QuotientGroup.mk k) =
      QuotientGroup.mk (⟨a * k * a⁻¹, (Subgroup.mem_normalizer_iff.mp haK k).1 k.2⟩ : ↥K) :=
  rfl

theorem conjPerm_mul (a b : G) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (haK₁ : a ∈ Subgroup.normalizer (K₁ : Set G)) (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hbK₁ : b ∈ Subgroup.normalizer (K₁ : Set G))
    (habK : a * b ∈ Subgroup.normalizer (K : Set G))
    (habK₁ : a * b ∈ Subgroup.normalizer (K₁ : Set G)) :
    conjPerm K K₁ (a * b) habK habK₁ = conjPerm K K₁ a haK haK₁ * conjPerm K K₁ b hbK hbK₁ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk _
    congr 1
    ext
    simp [coe_conjAut, mul_assoc]

end Conj

section Vec

variable {G : Type*} [Group G] {K K₁ N : Subgroup G}

@[expose] def vecFun (K K₁ U : Subgroup G) (v : G) (hU : ∀ k ∈ K, k * v * k⁻¹ ∈ U)
    (hfix : ∀ k ∈ K₁, k * v * k⁻¹ = v) : Cosets K K₁ → ↥U :=
  Quotient.lift (fun k : ↥K => (⟨k * v * k⁻¹, hU k k.2⟩ : ↥U)) (fun x y h => by
    have h' := QuotientGroup.leftRel_apply.mp h
    rw [Subgroup.mem_subgroupOf] at h'
    have h1 := hfix _ h'
    have h1' : ((x : G)⁻¹ * y) * v * ((x : G)⁻¹ * y)⁻¹ = v := by simpa using h1
    apply Subtype.ext
    change (x : G) * v * (x : G)⁻¹ = (y : G) * v * (y : G)⁻¹
    calc (x : G) * v * (x : G)⁻¹
        = (x : G) * (((x : G)⁻¹ * y) * v * ((x : G)⁻¹ * y)⁻¹) * (x : G)⁻¹ := by rw [h1']
      _ = (y : G) * v * (y : G)⁻¹ := by group)

theorem vecFun_smul (U : Subgroup G) (v : G) (hU : ∀ k ∈ K, k * v * k⁻¹ ∈ U)
    (hfix : ∀ k ∈ K₁, k * v * k⁻¹ = v) (g : ↥K)
    (hgU : (g : G) ∈ Subgroup.normalizer (U : Set G)) (ω : Cosets K K₁) :
    vecFun K K₁ U v hU hfix (g • ω) = conjAut U g hgU (vecFun K K₁ U v hU hfix ω) := by
  induction ω using QuotientGroup.induction_on with
  | H k =>
    apply Subtype.ext
    change ((g * k : ↥K) : G) * v * ((g * k : ↥K) : G)⁻¹ = g * (k * v * k⁻¹) * (g : G)⁻¹
    simp [mul_assoc]

theorem vecFun_conjPerm (U : Subgroup G) (v : G) (hU : ∀ k ∈ K, k * v * k⁻¹ ∈ U)
    (hfix : ∀ k ∈ K₁, k * v * k⁻¹ = v) (a : G) (haK : a ∈ Subgroup.normalizer (K : Set G))
    (haK₁ : a ∈ Subgroup.normalizer (K₁ : Set G)) (haU : a ∈ Subgroup.normalizer (U : Set G))
    (hav : a * v = v * a) (ω : Cosets K K₁) :
    vecFun K K₁ U v hU hfix (conjPerm K K₁ a haK haK₁ ω) =
      conjAut U a haU (vecFun K K₁ U v hU hfix ω) := by
  induction ω using QuotientGroup.induction_on with
  | H k =>
    apply Subtype.ext
    change a * (k : G) * a⁻¹ * v * (a * (k : G) * a⁻¹)⁻¹ = a * ((k : G) * v * (k : G)⁻¹) * a⁻¹
    have h1 : a⁻¹ * v * a = v := by
      calc a⁻¹ * v * a = a⁻¹ * (v * a) := by group
        _ = a⁻¹ * (a * v) := by rw [hav]
        _ = v := by group
    calc a * (k : G) * a⁻¹ * v * (a * (k : G) * a⁻¹)⁻¹
        = a * (k : G) * (a⁻¹ * v * a) * (k : G)⁻¹ * a⁻¹ := by group
      _ = a * ((k : G) * v * (k : G)⁻¹) * a⁻¹ := by rw [h1]; group

end Vec

section Fixed

variable {G : Type*} [Group G] {K K₁ N : Subgroup G}

theorem conjPerm_eq_toPerm (S : FiveSetup K K₁ N) {a k t : G} (hk : k ∈ K₁) (hat : a = k * t)
    (ht : ∀ x ∈ K, t * x * t⁻¹ * x⁻¹ ∈ N)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haK₁ : a ∈ Subgroup.normalizer (K₁ : Set G)) :
    conjPerm K K₁ a haK haK₁ = MulAction.toPerm (⟨k, S.le hk⟩ : ↥K) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := ht (g : G)⁻¹ (K.inv_mem g.2)
    have h2 : (k : G) * (t * (g : G)⁻¹ * t⁻¹ * (g : G)⁻¹⁻¹) ∈ K₁ := K₁.mul_mem hk (S.nle h1)
    convert h2 using 1
    subst hat
    change ((k * t) * (g : G) * (k * t)⁻¹)⁻¹ * (k * (g : G)) =
      k * (t * (g : G)⁻¹ * t⁻¹ * (g : G)⁻¹⁻¹)
    group

theorem conjPerm_unique_fixed [Fintype (Cosets K K₁)] [DecidableEq (Cosets K K₁)]
    (S : FiveSetup K K₁ N)
    {a k t : G} (hk : k ∈ K₁) (hat : a = k * t) (ht : ∀ x ∈ K, t * x * t⁻¹ * x⁻¹ ∈ N)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haK₁ : a ∈ Subgroup.normalizer (K₁ : Set G))
    (ha2 : a * a = 1) (hkN : k ∉ N) (ω : Cosets K K₁)
    (hω : conjPerm K K₁ a haK haK₁ ω = ω) : ω = QuotientGroup.mk 1 := by
  by_contra hne
  have hperm := conjPerm_eq_toPerm S hk hat ht haK haK₁
  have hsq : conjPerm K K₁ a haK haK₁ * conjPerm K K₁ a haK haK₁ = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk g
      congr 1
      ext
      change a * (a * (g : G) * a⁻¹) * a⁻¹ = g
      calc a * (a * (g : G) * a⁻¹) * a⁻¹ = (a * a) * (g : G) * (a * a)⁻¹ := by group
        _ = g := by rw [ha2]; group
  rw [hperm] at hsq hω
  have hk2 : (((⟨k, S.le hk⟩ : ↥K) * ⟨k, S.le hk⟩ : ↥K) : G) ∈ N := by
    refine (S.toPerm_eq_one_iff _).mp ?_
    have h4 : (MulAction.toPermHom ↥K (Cosets K K₁)) (⟨k, S.le hk⟩ * ⟨k, S.le hk⟩) = 1 := by
      rw [map_mul]
      exact hsq
    exact h4
  have hfix1 : (⟨k, S.le hk⟩ : ↥K) • (QuotientGroup.mk 1 : Cosets K K₁) = QuotientGroup.mk 1 := by
    change (QuotientGroup.mk (⟨k, S.le hk⟩ * 1) : Cosets K K₁) = QuotientGroup.mk 1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using K₁.inv_mem hk
  exact hkN (S.mem_of_two_fixed ⟨k, S.le hk⟩ hk2 ω (QuotientGroup.mk 1) hne hω hfix1)

end Fixed

section Data

variable {G : Type*} [Group G]

structure FiveData (V K N T R A U : Subgroup G) : Prop where
  setup : FiveSetup K (K ⊓ Subgroup.normalizer (V : Set G)) N
  ti : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) → ∀ v ∈ V, g * v * g⁻¹ ∈ V → v = 1
  a_card : Nat.card A = 4
  a_sq : ∀ a ∈ A, a * a = 1
  a_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  a_le_T : A ≤ T
  a_normV : A ≤ Subgroup.normalizer (V : Set G)
  a_normK : A ≤ Subgroup.normalizer (K : Set G)
  r_le_T : R ≤ T
  r_comm : ∀ t ∈ R, ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ N
  inf_le_R : ∀ x ∈ N, x ∈ T → x ∈ R
  decomp : ∀ a ∈ A, ∃ k ∈ K ⊓ Subgroup.normalizer (V : Set G), ∃ t ∈ R, a = k * t
  alpha : A ⊓ R = ⊥
  u_comm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x
  u_sq : ∀ x ∈ U, x * x = 1
  u_normK : K ≤ Subgroup.normalizer (U : Set G)
  u_normA : A ≤ Subgroup.normalizer (U : Set G)
  u_gen : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ U
  u_cent : ∀ a ∈ A, a ≠ 1 →
    U ⊓ Subgroup.centralizer (A : Set G) = U ⊓ Subgroup.centralizer ({a} : Set G)

theorem mem_normalizer_inf_normalizer {K V : Subgroup G} {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haV : a ∈ Subgroup.normalizer (V : Set G)) :
    a ∈ Subgroup.normalizer ((K ⊓ Subgroup.normalizer (V : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxK, hxV⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp haK x).1 hxK, ?_⟩
    exact (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem haV hxV)
      ((Subgroup.normalizer (V : Set G)).inv_mem haV)
  · rintro ⟨h1, h2⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp haK x).2 h1, ?_⟩
    have := (Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).mul_mem ((Subgroup.normalizer (V : Set G)).inv_mem haV)
        h2) haV
    simpa [mul_assoc] using this

theorem exists_two_ne_one {A : Subgroup G} (h : Nat.card A = 4) :
    ∃ a ∈ A, a ≠ 1 ∧ ∃ b ∈ A, b ≠ 1 ∧ a ≠ b := by
  have hne : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
    rw [hbot, Subgroup.card_bot] at h
    omega
  obtain ⟨a, haA, ha1⟩ := hne
  refine ⟨a, haA, ha1, ?_⟩
  by_contra hcon
  push Not at hcon
  have hsub : (A : Set G) ⊆ {1, a} := by
    intro x hx
    by_cases hx1 : x = 1
    · simp [hx1]
    · simp [(hcon x hx hx1).symm]
  have hcard : Nat.card A ≤ 2 := by
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, a} : Set G).ncard ≤ 2 := by
      refine (Set.ncard_insert_le 1 {a}).trans ?_
      rw [Set.ncard_singleton]
    rw [← Nat.card_coe_set_eq] at h1 h2
    exact h1.trans h2
  omega

theorem FiveData.unique_fixed [Finite G] {V K N T R A U : Subgroup G}
    [Fintype (Cosets K (K ⊓ Subgroup.normalizer (V : Set G)))]
    [DecidableEq (Cosets K (K ⊓ Subgroup.normalizer (V : Set G)))]
    (D : FiveData V K N T R A U) {c : G} (hc : c ∈ A) (hc1 : c ≠ 1)
    (ω : Cosets K (K ⊓ Subgroup.normalizer (V : Set G)))
    (hω : conjPerm K (K ⊓ Subgroup.normalizer (V : Set G)) c (D.a_normK hc)
      (mem_normalizer_inf_normalizer (D.a_normK hc) (D.a_normV hc)) ω = ω) :
    ω = QuotientGroup.mk 1 := by
  obtain ⟨k, hk, t, ht, hct⟩ := D.decomp c hc
  have hkT : k ∈ T := by
    have h1 : k = c * t⁻¹ := by rw [hct]; group
    rw [h1]
    exact T.mul_mem (D.a_le_T hc) (T.inv_mem (D.r_le_T ht))
  have hkN : k ∉ N := by
    intro hkN
    have hkR : k ∈ R := D.inf_le_R k hkN hkT
    have hcR : c ∈ R := by rw [hct]; exact R.mul_mem hkR ht
    have hcAR : c ∈ A ⊓ R := Subgroup.mem_inf.mpr ⟨hc, hcR⟩
    rw [D.alpha] at hcAR
    exact hc1 (Subgroup.mem_bot.mp hcAR)
  exact conjPerm_unique_fixed D.setup hk hct (D.r_comm t ht) (D.a_normK hc)
    (mem_normalizer_inf_normalizer (D.a_normK hc) (D.a_normV hc)) (D.a_sq c hc) hkN ω hω

end Data

section Main

variable {G : Type*} [Group G] [Finite G]

theorem five_conjugates {V K N T R A U : Subgroup G} (D : FiveData V K N T R A U) {v : G}
    (hvV : v ∈ V) (hv1 : v ≠ 1)
    (hfix : ∀ k ∈ K ⊓ Subgroup.normalizer (V : Set G), k * v * k⁻¹ = v) :
    ∃ a ∈ A, ∃ w ∈ V, a * w ≠ w * a := by
  classical
  by_contra hcon
  push Not at hcon
  set K₁ : Subgroup G := K ⊓ Subgroup.normalizer (V : Set G) with hK₁
  have S : FiveSetup K K₁ N := D.setup
  haveI : Fintype (Cosets K K₁) := Fintype.ofFinite _
  have hcard : Fintype.card (Cosets K K₁) = 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact S.card_cosets
  letI : CommGroup ↥U := { (inferInstance : Group ↥U) with
    mul_comm := fun x y => Subtype.ext (D.u_comm x x.2 y y.2) }
  have hW2 : ∀ w : ↥U, w * w = 1 := fun w => Subtype.ext (D.u_sq w w.2)
  have hU : ∀ k ∈ K, k * v * k⁻¹ ∈ U := fun k hk => D.u_gen k hk v hvV
  set f : Cosets K K₁ → ↥U := vecFun K K₁ U v hU hfix with hf
  set ω₁ : Cosets K K₁ := QuotientGroup.mk 1 with hω₁
  have htrans : ∀ ω₀ : Cosets K K₁, ∃ (φ : ↥U ≃* ↥U) (π : Equiv.Perm (Cosets K K₁)),
      π ω₁ = ω₀ ∧ ∀ ω, f (π ω) = φ (f ω) := by
    intro ω₀
    induction ω₀ using QuotientGroup.induction_on with
    | H g =>
      refine ⟨conjAut U g (D.u_normK g.2), MulAction.toPerm g, ?_, fun ω => ?_⟩
      · change (QuotientGroup.mk (g * 1) : Cosets K K₁) = QuotientGroup.mk g
        simp
      · exact vecFun_smul U v hU hfix g (D.u_normK g.2) ω
  obtain ⟨a, haA, ha1, b, hbA, hb1, hab⟩ := exists_two_ne_one D.a_card
  have haK := D.a_normK haA
  have hbK := D.a_normK hbA
  have haK₁ := mem_normalizer_inf_normalizer haK (D.a_normV haA)
  have hbK₁ := mem_normalizer_inf_normalizer hbK (D.a_normV hbA)
  have habA : a * b ∈ A := A.mul_mem haA hbA
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    calc a = a * (b * b) := by rw [D.a_sq b hbA, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul]
  have habK := D.a_normK habA
  have habK₁ := mem_normalizer_inf_normalizer habK (D.a_normV habA)
  have hmul := conjPerm_mul (K := K) (K₁ := K₁) a b haK haK₁ hbK hbK₁ habK habK₁
  have hcomm : conjPerm K K₁ a haK haK₁ * conjPerm K K₁ b hbK hbK₁ =
      conjPerm K K₁ b hbK hbK₁ * conjPerm K K₁ a haK haK₁ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk _
      congr 1
      ext
      change a * (b * (g : G) * b⁻¹) * a⁻¹ = b * (a * (g : G) * a⁻¹) * b⁻¹
      have hba : b * a = a * b := (D.a_comm b hbA a haA)
      calc a * (b * (g : G) * b⁻¹) * a⁻¹ = (a * b) * (g : G) * (a * b)⁻¹ := by group
        _ = (b * a) * (g : G) * (b * a)⁻¹ := by rw [hba]
        _ = b * (a * (g : G) * a⁻¹) * b⁻¹ := by group
  have hsq : conjPerm K K₁ a haK haK₁ * conjPerm K K₁ a haK haK₁ = 1 := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk g
      congr 1
      ext
      change a * (a * (g : G) * a⁻¹) * a⁻¹ = g
      calc a * (a * (g : G) * a⁻¹) * a⁻¹ = (a * a) * (g : G) * (a * a)⁻¹ := by group
        _ = g := by rw [D.a_sq a haA]; group
  have hfix1 : ∀ (c : G) (hcK : c ∈ Subgroup.normalizer (K : Set G))
      (hcK₁ : c ∈ Subgroup.normalizer (K₁ : Set G)), conjPerm K K₁ c hcK hcK₁ ω₁ = ω₁ := by
    intro c hcK hcK₁
    change (QuotientGroup.mk _ : Cosets K K₁) = QuotientGroup.mk 1
    congr 1
    ext
    change c * (1 : G) * c⁻¹ = 1
    group
  have hua : ∀ ω, conjPerm K K₁ a haK haK₁ ω = ω → ω = ω₁ := fun ω hω =>
    D.unique_fixed haA ha1 ω hω
  have hub : ∀ ω, conjPerm K K₁ b hbK hbK₁ ω = ω → ω = ω₁ := fun ω hω =>
    D.unique_fixed hbA hb1 ω hω
  have huab : ∀ ω, (conjPerm K K₁ a haK haK₁ * conjPerm K K₁ b hbK hbK₁) ω = ω → ω = ω₁ :=
    fun ω hω => D.unique_fixed habA hab1 ω (by rw [hmul]; exact hω)
  have hfixed : ∀ x : ↥U, conjAut U a (D.u_normA haA) x = x →
      conjAut U b (D.u_normA hbA) x = x := by
    intro x hx
    have hax : a * (x : G) = (x : G) * a := by
      have h1 : a * (x : G) * a⁻¹ = (x : G) := congrArg Subtype.val hx
      calc a * (x : G) = a * (x : G) * a⁻¹ * a := by group
        _ = (x : G) * a := by rw [h1]
    have hxc : (x : G) ∈ U ⊓ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]; exact hax⟩
    rw [← D.u_cent a haA ha1] at hxc
    have hbx : b * (x : G) = (x : G) * b :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxc).2 b hbA
    apply Subtype.ext
    change b * (x : G) * b⁻¹ = (x : G)
    calc b * (x : G) * b⁻¹ = (x : G) * b * b⁻¹ := by rw [hbx]
      _ = (x : G) := by group
  have key := five_point_const hcard hW2 f ω₁ htrans
    (conjPerm K K₁ a haK haK₁) (conjPerm K K₁ b hbK hbK₁)
    (conjAut U a (D.u_normA haA)) (conjAut U b (D.u_normA hbA))
    (fun ω => vecFun_conjPerm U v hU hfix a haK haK₁ (D.u_normA haA) (hcon a haA v hvV) ω)
    (fun ω => vecFun_conjPerm U v hU hfix b hbK hbK₁ (D.u_normA hbA) (hcon b hbA v hvV) ω)
    hsq hcomm (hfix1 a haK haK₁) (hfix1 b hbK hbK₁) hua hub huab hfixed
  have hex : ∃ k ∈ K, k ∉ K₁ := by
    by_contra hno
    push Not at hno
    have h1 : K ≤ K₁ := hno
    have h2 := Subgroup.relIndex_eq_one.mpr h1
    rw [S.index] at h2
    norm_num at h2
  obtain ⟨k, hkK, hkK₁⟩ := hex
  have hkV : k ∉ Subgroup.normalizer (V : Set G) := fun hkN =>
    hkK₁ (Subgroup.mem_inf.mpr ⟨hkK, hkN⟩)
  have h1 := key (QuotientGroup.mk ⟨k, hkK⟩)
  have h2 : k * v * k⁻¹ = v := by
    have h3 := congrArg Subtype.val h1
    change k * v * k⁻¹ = (1 : G) * v * (1 : G)⁻¹ at h3
    simpa using h3
  exact hv1 (D.ti k hkV v hvV (by rw [h2]; exact hvV))

end Main

end CFSG.LocalAnalysis.WeakClosure81.Five

end
