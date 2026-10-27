module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec11.R2No

theorem mem_normalizer_of_inv_conj_le {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hle : H.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    show g⁻¹ * x * g⁻¹⁻¹ ∈ H
    rw [inv_inv]
    exact h x hx
  have hcard : Nat.card H ≤ Nat.card (H.map (MulAut.conj g⁻¹).toMonoidHom) :=
    (Subgroup.card_map_of_injective hinj).ge
  have heq : H.map (MulAut.conj g⁻¹).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  have hg : g⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact heq
  have hg' := inv_mem hg
  rwa [inv_inv] at hg'

theorem exists_mem_normalizer_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf p R K) {m : G}
    (hm : m ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k⁻¹ * m ∈ Subgroup.normalizer (R : Set G) := by
  have hRK : R ≤ K := hR.le
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : Subgroup G, R₂ = R.map (MulAut.conj m).toMonoidHom := ⟨_, rfl⟩
  have hR₂K : R₂ ≤ K := by
    rw [hR₂]
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hm y).mp (hRK hy)
  have hcR₂ : Nat.card R₂ = Nat.card R := by
    rw [hR₂]
    exact Subgroup.card_map_of_injective (MulAut.conj m).injective
  have hR₂S : CFSG.ABGLocalTools.IsSylowOf p R₂ K :=
    CFSG.ABGLocalTools.isSylowOf_of_card hR₂K (hcR₂.trans hR.card_eq)
  obtain ⟨P₁, hP₁⟩ := hR.exists_sylow_eq_subgroupOf
  obtain ⟨P₂, hP₂⟩ := hR₂S.exists_sylow_eq_subgroupOf
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K P₁ P₂
  refine ⟨(c : G), c.2, mem_normalizer_of_inv_conj_le fun y hy => ?_⟩
  have h1 : (⟨y, hRK hy⟩ : K) ∈ (P₁ : Subgroup K) := by
    rw [hP₁, Subgroup.mem_subgroupOf]
    exact hy
  have h2 : MulAut.conj c (⟨y, hRK hy⟩ : K) ∈ (P₂ : Subgroup K) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [hP₂, Subgroup.mem_subgroupOf, hR₂, Subgroup.mem_map] at h2
  obtain ⟨z, hz, hzy⟩ := h2
  have hzy' : m * z * m⁻¹ = (c : G) * y * (c : G)⁻¹ := hzy
  have e : ((c : G)⁻¹ * m)⁻¹ * y * ((c : G)⁻¹ * m) = z := by
    rw [show z = m⁻¹ * (m * z * m⁻¹) * m by group, hzy']
    group
  rw [e]
  exact hz

theorem exists_conj_mem_of_isSylowOf {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {W R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf p R W) {w : G} (hw : w ∈ W)
    (hw3 : ∃ k : ℕ, w ^ p ^ k = 1) : ∃ g ∈ W, g * w * g⁻¹ ∈ R := by
  obtain ⟨k, hk⟩ := hw3
  obtain ⟨Q, hQ⟩ := hR
  obtain ⟨x, hxw⟩ : ∃ x : W, (x : G) = w := ⟨⟨w, hw⟩, rfl⟩
  have hxk : x ^ p ^ k = 1 := Subtype.ext (by simpa [hxw] using hk)
  have hpp : p.Prime := Fact.out
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hpp).mp (orderOf_dvd_of_pow_eq_one hxk)
  have hP : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers]; exact hm)
  obtain ⟨Q', hQ'⟩ := hP.exists_le_sylow
  have hxQ' : x ∈ (Q' : Subgroup W) := hQ' (Subgroup.mem_zpowers x)
  have hex : ∃ g : W, g • Q' = Q := MulAction.IsPretransitive.exists_smul_eq Q' Q
  obtain ⟨g, hg⟩ := hex
  have hmem : MulAut.conj g • x ∈ (Q : Subgroup W) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q' : Subgroup W) hxQ'
  have hmem' : g * x * g⁻¹ ∈ (Q : Subgroup W) := hmem
  refine ⟨(g : G), g.2, ?_⟩
  rw [← hQ, Subgroup.mem_map]
  exact ⟨g * x * g⁻¹, hmem', by simp [hxw]⟩

theorem conj_mem_closure_pow_three {G : Type*} [Group G] {R : Subgroup G} {g : G} (hg : g ∈ R)
    {x : G} (hx : x ∈ Subgroup.closure {y : G | y ∈ R ∧ y ^ 3 = 1}) :
    g * x * g⁻¹ ∈ Subgroup.closure {y : G | y ∈ R ∧ y ^ 3 = 1} := by
  have hle : Subgroup.closure {y : G | y ∈ R ∧ y ^ 3 = 1} ≤
      (Subgroup.closure {y : G | y ∈ R ∧ y ^ 3 = 1}).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyR, hy3⟩
    have hmem : g * y * g⁻¹ ∈ {y : G | y ∈ R ∧ y ^ 3 = 1} := by
      refine ⟨R.mul_mem (R.mul_mem hg hyR) (R.inv_mem hg), ?_⟩
      rw [conj_pow, hy3]
      simp
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact Subgroup.subset_closure hmem
  exact hle hx

theorem le_normalizer_closure_pow_three {G : Type*} [Group G] {R : Subgroup G} :
    R ≤ Subgroup.normalizer
      ((Subgroup.closure {y : G | y ∈ R ∧ y ^ 3 = 1} : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  show h ∈ Subgroup.closure {y : G | y ∈ R ∧ y ^ 3 = 1} ↔
    g * h * g⁻¹ ∈ Subgroup.closure {y : G | y ∈ R ∧ y ^ 3 = 1}
  constructor
  · intro hh
    exact conj_mem_closure_pow_three hg hh
  · intro hh
    have h' := conj_mem_closure_pow_three (R.inv_mem hg) hh
    have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e] at h'
    exact h'

theorem conj_inv_eq_of_conj_eq {G : Type*} [Group G] {w b : G} (h : w * b * w⁻¹ = b) :
    w⁻¹ * b * w = b := by
  calc w⁻¹ * b * w = w⁻¹ * (w * b * w⁻¹) * w := by rw [h]
    _ = b := by group

@[expose] def K0 {G : Type*} [Group G] (A B : Subgroup G) : Subgroup G where
  carrier := {w | w ∈ Subgroup.normalizer (A : Set G) ∧ (∀ b ∈ B, w * b * w⁻¹ = b) ∧
    ∀ t ∈ A, t⁻¹ * (w⁻¹ * t * w) ∈ B}
  mul_mem' := by
    rintro w1 w2 ⟨hN1, hC1, hB1⟩ ⟨hN2, hC2, hB2⟩
    refine ⟨mul_mem hN1 hN2, ?_, ?_⟩
    · intro b hb
      calc w1 * w2 * b * (w1 * w2)⁻¹ = w1 * (w2 * b * w2⁻¹) * w1⁻¹ := by group
        _ = w1 * b * w1⁻¹ := by rw [hC2 b hb]
        _ = b := hC1 b hb
    · intro t ht
      have h1 : t⁻¹ * (w1⁻¹ * t * w1) ∈ B := hB1 t ht
      have h2 : t⁻¹ * (w2⁻¹ * t * w2) ∈ B := hB2 t ht
      have h3 : w2⁻¹ * (t⁻¹ * (w1⁻¹ * t * w1)) * w2 = t⁻¹ * (w1⁻¹ * t * w1) :=
        conj_inv_eq_of_conj_eq (hC2 _ h1)
      have h4 : (t⁻¹ * (w2⁻¹ * t * w2)) * (w2⁻¹ * (t⁻¹ * (w1⁻¹ * t * w1)) * w2) ∈ B := by
        rw [h3]
        exact mul_mem h2 h1
      have h5 : t⁻¹ * ((w1 * w2)⁻¹ * t * (w1 * w2)) =
          (t⁻¹ * (w2⁻¹ * t * w2)) * (w2⁻¹ * (t⁻¹ * (w1⁻¹ * t * w1)) * w2) := by
        group
      rw [h5]
      exact h4
  one_mem' := by
    refine ⟨one_mem _, ?_, ?_⟩
    · intro b _
      simp
    · intro t _
      simp
  inv_mem' := by
    rintro w ⟨hN, hC, hB⟩
    refine ⟨inv_mem hN, ?_, ?_⟩
    · intro b hb
      rw [inv_inv]
      exact conj_inv_eq_of_conj_eq (hC b hb)
    · intro t ht
      have ht' : w * t * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hN t).mp ht
      have h1 : (w * t * w⁻¹)⁻¹ * (w⁻¹ * (w * t * w⁻¹) * w) ∈ B := hB _ ht'
      have h2 : (w * t * w⁻¹)⁻¹ * (w⁻¹ * (w * t * w⁻¹) * w) = w * t⁻¹ * w⁻¹ * t := by
        group
      rw [h2] at h1
      have h3 := inv_mem h1
      have h4 : (w * t⁻¹ * w⁻¹ * t)⁻¹ = t⁻¹ * ((w⁻¹)⁻¹ * t * w⁻¹) := by group
      rw [h4] at h3
      exact h3

theorem mem_K0 {G : Type*} [Group G] {A B : Subgroup G} {w : G} :
    w ∈ K0 A B ↔ w ∈ Subgroup.normalizer (A : Set G) ∧ (∀ b ∈ B, w * b * w⁻¹ = b) ∧
      ∀ t ∈ A, t⁻¹ * (w⁻¹ * t * w) ∈ B := Iff.rfl

theorem conj_mem_K0 {G : Type*} [Group G] {A B : Subgroup G}
    (hWB : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ b ∈ B, w * b * w⁻¹ ∈ B)
    {w k : G} (hw : w ∈ Subgroup.normalizer (A : Set G)) (hk : k ∈ K0 A B) :
    w * k * w⁻¹ ∈ K0 A B := by
  obtain ⟨hkN, hkC, hkB⟩ := hk
  have hwinv : w⁻¹ ∈ Subgroup.normalizer (A : Set G) := inv_mem hw
  refine mem_K0.2 ⟨mul_mem (mul_mem hw hkN) hwinv, ?_, ?_⟩
  · intro b hb
    have hb' : w⁻¹ * b * w ∈ B := by
      have h := hWB w⁻¹ hwinv b hb
      rwa [inv_inv] at h
    have hk' : k * (w⁻¹ * b * w) * k⁻¹ = w⁻¹ * b * w := hkC _ hb'
    calc w * k * w⁻¹ * b * (w * k * w⁻¹)⁻¹ = w * (k * (w⁻¹ * b * w) * k⁻¹) * w⁻¹ := by
          group
      _ = w * (w⁻¹ * b * w) * w⁻¹ := by rw [hk']
      _ = b := by group
  · intro t ht
    have ht' : w⁻¹ * t * w ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hw (w⁻¹ * t * w)).mpr (by
        rw [show w * (w⁻¹ * t * w) * w⁻¹ = t by group]
        exact ht)
    have hb'' : (w⁻¹ * t * w)⁻¹ * (k⁻¹ * (w⁻¹ * t * w) * k) ∈ B := hkB _ ht'
    have key : t⁻¹ * ((w * k * w⁻¹)⁻¹ * t * (w * k * w⁻¹)) =
        w * ((w⁻¹ * t * w)⁻¹ * (k⁻¹ * (w⁻¹ * t * w) * k)) * w⁻¹ := by
      group
    rw [key]
    exact hWB w hw _ hb''

theorem normalizer_le_normalizer_K0 {G : Type*} [Group G] {A B : Subgroup G}
    (hWB : ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ b ∈ B, w * b * w⁻¹ ∈ B) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (K0 A B : Set G) := by
  intro w hw
  refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · have hk' : k ∈ K0 A B := hk
    exact conj_mem_K0 hWB hw hk'
  · have hk' : w * k * w⁻¹ ∈ K0 A B := hk
    have hwinv : w⁻¹ ∈ Subgroup.normalizer (A : Set G) := inv_mem hw
    have h : w⁻¹ * (w * k * w⁻¹) * w⁻¹⁻¹ ∈ K0 A B := conj_mem_K0 hWB hwinv hk'
    have e : w⁻¹ * (w * k * w⁻¹) * w⁻¹⁻¹ = k := by group
    rw [e] at h
    exact h

end CFSG.RankThree.PartTwo.Sec11.R2No
