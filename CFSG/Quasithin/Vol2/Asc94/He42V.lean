module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private theorem he42v_inv_invol :
    ∀ g a : GL2, g ^ 3 = 1 → g ≠ 1 → a * g * a⁻¹ = g⁻¹ → a * a = 1 := by
  decide +kernel

private theorem he42v_fix : ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → ∀ M : M2, (g : M2) * M = M → M = 0 := by
  decide +kernel

private theorem he42v_pow_inj : ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 → ∀ i j : Fin 3,
    g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem he42v_B_conj : ∀ g a c : GL2, ∀ M : M2, g ^ 3 = 1 → g ≠ 1 → a * g * a⁻¹ = g⁻¹ →
    c * g * c⁻¹ = g⁻¹ → (g : M2) * M = M * g →
    (g : M2) * ((a : M2) * M * (c : M2)ᵀ) = ((a : M2) * M * (c : M2)ᵀ) * g := by
  decide +kernel

@[expose] def he42vYbar (g : GL2) : Subgroup (GL2 × GL2) := (zpowers g).prod (zpowers g)

private theorem he42v_zpowers_comm {g x : GL2} (hx : x ∈ zpowers g) : x * g = g * x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  exact ((Commute.refl g).zpow_left k).eq

private theorem he42v_conj_zpowers {g c x : GL2} (hc : c * g * c⁻¹ = g ∨ c * g * c⁻¹ = g⁻¹)
    (hx : x ∈ zpowers g) : c * x * c⁻¹ ∈ zpowers g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← conj_zpow]
  rcases hc with h | h
  · rw [h]; exact (zpowers g).zpow_mem (mem_zpowers g) k
  · rw [h, _root_.inv_zpow]; exact (zpowers g).inv_mem ((zpowers g).zpow_mem (mem_zpowers g) k)

private theorem he42v_Ybar_normal {g : GL2} (hg : g ^ 3 = 1) (c : GL2 × GL2) {p : GL2 × GL2}
    (hp : p ∈ he42vYbar g) : c * p * c⁻¹ ∈ he42vYbar g := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_prod.1 hp
  show c * p * c⁻¹ ∈ (zpowers g).prod (zpowers g)
  rw [Subgroup.mem_prod]
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  exact ⟨he42v_conj_zpowers (gl2_conj_pow_three c.1 g hg) h1,
    he42v_conj_zpowers (gl2_conj_pow_three c.2 g hg) h2⟩

private theorem he42v_Ybar_card {g : GL2} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    Nat.card (he42vYbar g) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h3 : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  unfold he42vYbar
  rw [Nat.card_congr (Subgroup.prodEquiv (zpowers g) (zpowers g)).toEquiv, Nat.card_prod,
    Nat.card_zpowers, h3]

private theorem he42v_Ybar_index {g : GL2} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    (he42vYbar g).index = 4 := by
  have h := Subgroup.card_mul_index (he42vYbar g)
  rw [he42v_Ybar_card hg3 hg1, Nat.card_prod, card_GL2] at h
  omega

private theorem he42v_inv_of_zpowers {g h s : GL2} (hs : s * g * s⁻¹ = g⁻¹) (hh : h ∈ zpowers g) :
    h * s * g * (h * s)⁻¹ = g⁻¹ := by
  have hcomm : Commute h g := he42v_zpowers_comm hh
  calc h * s * g * (h * s)⁻¹ = h * (s * g * s⁻¹) * h⁻¹ := by group
    _ = h * g⁻¹ * h⁻¹ := by rw [hs]
    _ = g⁻¹ * h * h⁻¹ := by rw [hcomm.inv_right.eq]
    _ = g⁻¹ := by group

private theorem he42v_conj_pair (R : GL2 × GL2) (g : GL2) (h : R.1 * g * R.1⁻¹ = g⁻¹) :
    R * (g, 1) * R⁻¹ = (g, 1)⁻¹ := by
  refine Prod.ext ?_ ?_
  · simpa using h
  · simp

private theorem he42v_conj_pair' (R : GL2 × GL2) (g : GL2) (h : R.2 * g * R.2⁻¹ = g⁻¹) :
    R * (1, g) * R⁻¹ = (1, g)⁻¹ := by
  refine Prod.ext ?_ ?_
  · simp
  · simpa using h

private theorem he42v_pow_mod' {X : Type} [Group X] (x : X) (hx : orderOf x = 3) (n : ℕ) :
    x ^ (n % 3) = x ^ n := by
  rw [← hx]
  exact pow_mod_orderOf x n

private theorem he42v_pow3 {X : Type} [Group X] (x : X) (hx : orderOf x = 3) : x ^ 3 = 1 := by
  rw [← hx]
  exact pow_orderOf_eq_one x

private theorem he42v_closure_param {y₁ y₂ : G} (hc : y₁ * y₂ = y₂ * y₁) (o₁ : y₁ ^ 3 = 1)
    (o₂ : y₂ ^ 3 = 1) :
    ∀ z ∈ Subgroup.closure ({y₁, y₂} : Set G), ∃ i j : ℕ, z = y₁ ^ i * y₂ ^ j := by
  have hcm : Commute y₁ y₂ := hc
  have hcomm : ∀ a b c d : ℕ, y₁ ^ a * y₂ ^ b * (y₁ ^ c * y₂ ^ d) =
      y₁ ^ (a + c) * y₂ ^ (b + d) := by
    intro a b c d
    have h : y₂ ^ b * y₁ ^ c = y₁ ^ c * y₂ ^ b := (hcm.pow_pow c b).eq.symm
    calc y₁ ^ a * y₂ ^ b * (y₁ ^ c * y₂ ^ d) = y₁ ^ a * (y₂ ^ b * y₁ ^ c) * y₂ ^ d := by group
      _ = y₁ ^ a * (y₁ ^ c * y₂ ^ b) * y₂ ^ d := by rw [h]
      _ = y₁ ^ (a + c) * y₂ ^ (b + d) := by rw [pow_add, pow_add]; group
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    exact ⟨i + k, j + l, hcomm i j k l⟩
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨2 * i, 2 * j, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [hcomm]
    have e1 : y₁ ^ (i + 2 * i) = 1 := by
      rw [show i + 2 * i = 3 * i by ring, pow_mul, o₁, one_pow]
    have e2 : y₂ ^ (j + 2 * j) = 1 := by
      rw [show j + 2 * j = 3 * j by ring, pow_mul, o₂, one_pow]
    rw [e1, e2, one_mul]

private theorem he42v_factor_eq {X : Type} [Group X] {A A' : Subgroup X} {a₁ a₂ b₁ b₂ : X}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A') (hb₁ : b₁ ∈ A) (hb₂ : b₂ ∈ A')
    (hprod : b₁ * b₂ = a₁ * a₂) : a₁⁻¹ * b₁ ∈ A ⊓ A' := by
  have hz : a₁⁻¹ * b₁ = a₂ * b₂⁻¹ := by
    calc a₁⁻¹ * b₁ = a₁⁻¹ * (b₁ * b₂) * b₂⁻¹ := by group
      _ = a₁⁻¹ * (a₁ * a₂) * b₂⁻¹ := by rw [hprod]
      _ = a₂ * b₂⁻¹ := by group
  refine ⟨A.mul_mem (A.inv_mem ha₁) hb₁, ?_⟩
  rw [hz]
  exact A'.mul_mem ha₂ (A'.inv_mem hb₂)

private theorem he42v_g_facts (S : HeSetup G) : S.g ^ 3 = 1 ∧ S.g ≠ 1 :=
  ⟨S.hD.g_pow_three S.hxN S.hxa S.hx3, S.hD.g_ne_one S.hxN S.hxa S.hx3⟩

private theorem he42v_rhoG_one (S : HeSetup G) : S.rhoG 1 = 1 := by
  rw [S.rhoG_of_mem S.N.one_mem]
  exact map_one S.rho

private theorem he42v_rhoG_mul (S : HeSetup G) {a b : G} (ha : a ∈ S.N) (hb : b ∈ S.N) :
    S.rhoG (a * b) = S.rhoG a * S.rhoG b := by
  rw [S.rhoG_of_mem ha, S.rhoG_of_mem hb, S.rhoG_of_mem (S.N.mul_mem ha hb)]
  exact map_mul S.rho ⟨a, ha⟩ ⟨b, hb⟩

private theorem he42v_rhoG_inv (S : HeSetup G) {a : G} (ha : a ∈ S.N) :
    S.rhoG a⁻¹ = (S.rhoG a)⁻¹ := by
  have h := he42v_rhoG_mul S ha (S.N.inv_mem ha)
  rw [mul_inv_cancel, he42v_rhoG_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem he42v_rhoG_pow (S : HeSetup G) {a : G} (ha : a ∈ S.N) (i : ℕ) :
    S.rhoG (a ^ i) = S.rhoG a ^ i := by
  induction i with
  | zero => simp [he42v_rhoG_one]
  | succ i ih =>
    rw [pow_succ, pow_succ, he42v_rhoG_mul S (S.N.pow_mem ha i) ha, ih]

private theorem he42v_rhoG_closure (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) (i j : ℕ) :
    S.rhoG (y₁ ^ i * y₂ ^ j) = (S.g ^ i, S.g ^ j) := by
  rw [he42v_rhoG_mul S (S.N.pow_mem hY.mem₁ i) (S.N.pow_mem hY.mem₂ j),
    he42v_rhoG_pow S hY.mem₁ i, he42v_rhoG_pow S hY.mem₂ j, hY.rho₁, hY.rho₂]
  simp

private theorem he42v_rhoG_eq_one_iff (S : HeSetup G) {z : G} (hz : z ∈ S.N) :
    S.rhoG z = 1 ↔ z ∈ S.A ⊔ S.A' := by
  rw [S.rhoG_of_mem hz]
  have e : (⟨z, hz⟩ : S.N) ∈ (S.hD.hT.rho S.N S.hD.hK.norm).ker ↔ z ∈ S.A ⊔ S.A' := by
    rw [S.hD.hT.ker_rho S.hD.hK]
    exact Subgroup.mem_subgroupOf
  exact MonoidHom.mem_ker.symm.trans e

private theorem he42v_closure_le_N (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    Subgroup.closure ({y₁, y₂} : Set G) ≤ S.N := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hY.mem₁
  · exact hY.mem₂

private theorem he42v_rho_Y_mem (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {z : G}
    (hz : z ∈ Subgroup.closure ({y₁, y₂} : Set G)) : S.rhoG z ∈ he42vYbar S.g := by
  obtain ⟨i, j, rfl⟩ := he42v_closure_param hY.comm (he42v_pow3 y₁ hY.ord₁)
    (he42v_pow3 y₂ hY.ord₂) z hz
  rw [he42v_rhoG_closure S hY]
  exact Subgroup.mem_prod.2 ⟨(zpowers S.g).pow_mem (mem_zpowers S.g) i,
    (zpowers S.g).pow_mem (mem_zpowers S.g) j⟩

private theorem he42v_Y_card (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    Nat.card (Subgroup.closure ({y₁, y₂} : Set G)) = 9 := by
  obtain ⟨hg3, hg1⟩ := he42v_g_facts S
  have hmem : ∀ i j : ℕ, y₁ ^ i * y₂ ^ j ∈ Subgroup.closure ({y₁, y₂} : Set G) := fun i j =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) i)
      (Subgroup.pow_mem _ (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ (Set.mem_singleton _))) j)
  let f : Fin 3 × Fin 3 → Subgroup.closure ({y₁, y₂} : Set G) :=
    fun p => ⟨y₁ ^ (p.1 : ℕ) * y₂ ^ (p.2 : ℕ), hmem _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j⟩ ⟨k, l⟩ hpq
      have h : y₁ ^ (i : ℕ) * y₂ ^ (j : ℕ) = y₁ ^ (k : ℕ) * y₂ ^ (l : ℕ) :=
        congrArg Subtype.val hpq
      have hr := congrArg S.rhoG h
      rw [he42v_rhoG_closure S hY, he42v_rhoG_closure S hY, Prod.mk.injEq] at hr
      have hik := he42v_pow_inj S.g hg3 hg1 i k hr.1
      have hjl := he42v_pow_inj S.g hg3 hg1 j l hr.2
      rw [hik, hjl]
    · intro z
      obtain ⟨i, j, hij⟩ := he42v_closure_param hY.comm (he42v_pow3 y₁ hY.ord₁)
        (he42v_pow3 y₂ hY.ord₂) z.1 z.2
      refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      show y₁ ^ (i % 3) * y₂ ^ (j % 3) = z.1
      rw [he42v_pow_mod' y₁ hY.ord₁ i, he42v_pow_mod' y₂ hY.ord₂ j]
      exact hij.symm
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

private theorem he42v_rhoG_inj_Y (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {z z' : G}
    (hz : z ∈ Subgroup.closure ({y₁, y₂} : Set G))
    (hz' : z' ∈ Subgroup.closure ({y₁, y₂} : Set G)) (h : S.rhoG z = S.rhoG z') : z = z' := by
  obtain ⟨hg3, hg1⟩ := he42v_g_facts S
  obtain ⟨i, j, rfl⟩ := he42v_closure_param hY.comm (he42v_pow3 y₁ hY.ord₁)
    (he42v_pow3 y₂ hY.ord₂) z hz
  obtain ⟨k, l, rfl⟩ := he42v_closure_param hY.comm (he42v_pow3 y₁ hY.ord₁)
    (he42v_pow3 y₂ hY.ord₂) z' hz'
  rw [he42v_rhoG_closure S hY, he42v_rhoG_closure S hY, Prod.mk.injEq] at h
  have hgo : orderOf S.g = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hg3 hg1
  have hi : S.g ^ (i % 3) = S.g ^ (k % 3) := by
    rw [he42v_pow_mod' S.g hgo, he42v_pow_mod' S.g hgo]
    exact h.1
  have hj : S.g ^ (j % 3) = S.g ^ (l % 3) := by
    rw [he42v_pow_mod' S.g hgo, he42v_pow_mod' S.g hgo]
    exact h.2
  have hik : i % 3 = k % 3 :=
    congrArg Fin.val (he42v_pow_inj S.g hg3 hg1 ⟨i % 3, Nat.mod_lt _ (by norm_num)⟩
      ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩ hi)
  have hjl : j % 3 = l % 3 :=
    congrArg Fin.val (he42v_pow_inj S.g hg3 hg1 ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩
      ⟨l % 3, Nat.mod_lt _ (by norm_num)⟩ hj)
  have e1 : y₁ ^ i = y₁ ^ k := by
    rw [← he42v_pow_mod' y₁ hY.ord₁ i, ← he42v_pow_mod' y₁ hY.ord₁ k, hik]
  have e2 : y₂ ^ j = y₂ ^ l := by
    rw [← he42v_pow_mod' y₂ hY.ord₂ j, ← he42v_pow_mod' y₂ hY.ord₂ l, hjl]
  rw [e1, e2]

@[expose] noncomputable def he42vP (S : HeSetup G) : Subgroup G :=
  ((he42vYbar S.g).comap S.rho).map S.N.subtype

private theorem he42v_mem_P (S : HeSetup G) {z : G} :
    z ∈ he42vP S ↔ ∃ h : z ∈ S.N, S.rho ⟨z, h⟩ ∈ he42vYbar S.g := by
  constructor
  · intro hz
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hz
    exact ⟨n.2, hn⟩
  · rintro ⟨h, hz⟩
    exact Subgroup.mem_map.2 ⟨⟨z, h⟩, hz, rfl⟩

private theorem he42v_card_P (S : HeSetup G) (hB : S.BaseFacts) : Nat.card (he42vP S) = 2304 := by
  obtain ⟨hg3, hg1⟩ := he42v_g_facts S
  have hsurj : Function.Surjective S.rho := S.hD.hT.rho_surjective S.hD.hK
  have hidx : ((he42vYbar S.g).comap S.rho).index = 4 := by
    rw [Subgroup.index_comap_of_surjective _ hsurj]
    exact he42v_Ybar_index hg3 hg1
  have h := Subgroup.card_mul_index ((he42vYbar S.g).comap S.rho)
  rw [hidx, hB.card_N] at h
  unfold he42vP
  rw [Subgroup.card_subtype]
  omega

private theorem he42v_conj_mem_P (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {n : G}
    (hn : n ∈ S.N) {z : G} (hz : z ∈ Subgroup.closure ({y₁, y₂} : Set G)) :
    n * z * n⁻¹ ∈ he42vP S := by
  obtain ⟨hg3, -⟩ := he42v_g_facts S
  have hzN : z ∈ S.N := he42v_closure_le_N S hY hz
  have hcN : n * z * n⁻¹ ∈ S.N := S.N.mul_mem (S.N.mul_mem hn hzN) (S.N.inv_mem hn)
  rw [he42v_mem_P]
  refine ⟨hcN, ?_⟩
  have e : S.rho ⟨n * z * n⁻¹, hcN⟩ = S.rho ⟨n, hn⟩ * S.rho ⟨z, hzN⟩ * (S.rho ⟨n, hn⟩)⁻¹ := by
    have h : (⟨n * z * n⁻¹, hcN⟩ : S.N) = ⟨n, hn⟩ * ⟨z, hzN⟩ * (⟨n, hn⟩)⁻¹ := Subtype.ext rfl
    rw [h, map_mul, map_mul, map_inv]
  rw [e]
  apply he42v_Ybar_normal hg3
  rw [← S.rhoG_of_mem hzN]
  exact he42v_rho_Y_mem S hY hz

private theorem he42v_sylow_conj {X : Type} [Group X] [Finite X] (P H K : Subgroup X)
    (hHP : H ≤ P) (hKP : K ≤ P) (hH : Nat.card H = 9) (hK : Nat.card K = 9)
    (hP : Nat.card P = 2304) : ∃ c ∈ P, ∀ z ∈ K, c * z * c⁻¹ ∈ H := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcH : Nat.card (H.subgroupOf P) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv, hH]
  have hcK : Nat.card (K.subgroupOf P) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKP).toEquiv, hK]
  have hiH : ¬ 3 ∣ (H.subgroupOf P).index := by
    have h := (H.subgroupOf P).card_mul_index
    rw [hcH, hP] at h
    have hidx : (H.subgroupOf P).index = 256 := by omega
    rw [hidx]
    norm_num
  have hiK : ¬ 3 ∣ (K.subgroupOf P).index := by
    have h := (K.subgroupOf P).card_mul_index
    rw [hcK, hP] at h
    have hidx : (K.subgroupOf P).index = 256 := by omega
    rw [hidx]
    norm_num
  have hpH : IsPGroup 3 (H.subgroupOf P) := IsPGroup.of_card (n := 2) (by rw [hcH]; norm_num)
  have hpK : IsPGroup 3 (K.subgroupOf P) := IsPGroup.of_card (n := 2) (by rw [hcK]; norm_num)
  obtain ⟨SH, hSH⟩ : ∃ Q : Sylow 3 P, (Q : Subgroup P) = H.subgroupOf P :=
    ⟨hpH.toSylow hiH, IsPGroup.toSylow_coe hpH hiH⟩
  obtain ⟨SK, hSK⟩ : ∃ Q : Sylow 3 P, (Q : Subgroup P) = K.subgroupOf P :=
    ⟨hpK.toSylow hiK, IsPGroup.toSylow_coe hpK hiK⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq P SK SH
  refine ⟨(c : X), c.2, fun z hz => ?_⟩
  have hzP : z ∈ P := hKP hz
  have hk : (⟨z, hzP⟩ : P) ∈ (SK : Subgroup P) := by
    rw [hSK, Subgroup.mem_subgroupOf]
    exact hz
  have h1 : c * ⟨z, hzP⟩ * c⁻¹ ∈ (SH : Subgroup P) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ hk
  rw [hSH, Subgroup.mem_subgroupOf] at h1
  simpa using h1

private theorem he42v_CJ_one (S : HeSetup G) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) {j : G}
    (hj : j ∈ S.A ⊔ S.A') (h1 : y₁ * j = j * y₁) (h2 : y₂ * j = j * y₂) : j = 1 := by
  obtain ⟨hg3, hg1⟩ := he42v_g_facts S
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := S.hD.exists_mul_of_mem_sup hj
  have hr1 : S.rho ⟨y₁, hY.mem₁⟩ = (S.g, 1) := (S.rhoG_of_mem hY.mem₁).symm.trans hY.rho₁
  have hr2 : S.rho ⟨y₂, hY.mem₂⟩ = (1, S.g) := (S.rhoG_of_mem hY.mem₂).symm.trans hY.rho₂
  have hn1 := S.hD.hK.norm y₁ hY.mem₁
  have hb₁ : y₁ * a₁ * y₁⁻¹ ∈ S.A := hn1.1 a₁ ha₁
  have hb₂ : y₁ * a₂ * y₁⁻¹ ∈ S.A' := hn1.2 a₂ ha₂
  have hprod : (y₁ * a₁ * y₁⁻¹) * (y₁ * a₂ * y₁⁻¹) = a₁ * a₂ := by
    calc (y₁ * a₁ * y₁⁻¹) * (y₁ * a₂ * y₁⁻¹) = y₁ * (a₁ * a₂) * y₁⁻¹ := by group
      _ = a₁ * a₂ := by rw [h1]; group
  have hzZ := he42v_factor_eq ha₁ ha₂ hb₁ hb₂ hprod
  have hu_z : S.u (a₁⁻¹ * (y₁ * a₁ * y₁⁻¹)) = 0 := (S.hD.hT.cu.zero _ hzZ.1).2 hzZ.2
  have hu_eq : S.u (y₁ * a₁ * y₁⁻¹) = S.u a₁ := by
    have h := S.hD.hT.cu.mul a₁ ha₁ _ hzZ.1
    rw [hu_z, add_zero, mul_inv_cancel_left] at h
    exact h
  have hu_conj : S.u (y₁ * a₁ * y₁⁻¹) = (S.g : M2) *ᵥ S.u a₁ := by
    have h : S.u (y₁ * a₁ * y₁⁻¹) = ((S.rho ⟨y₁, hY.mem₁⟩).1 : M2) *ᵥ S.u a₁ :=
      S.hD.hT.u_conj S.N S.hD.hK.norm ⟨y₁, hY.mem₁⟩ ha₁
    rw [hr1] at h
    exact h
  have hu0 : S.u a₁ = 0 := by
    apply gl2_order_three_fpf S.g hg3 hg1 (S.u a₁)
    exact hu_conj.symm.trans hu_eq
  have ha₁' : a₁ ∈ S.A' := (S.hD.hT.cu.zero a₁ ha₁).1 hu0
  have hj' : a₁ * a₂ ∈ S.A' := S.A'.mul_mem ha₁' ha₂
  have hy2 : y₂ * (a₁ * a₂) * y₂⁻¹ = a₁ * a₂ := by rw [h2, mul_inv_cancel_right]
  have hw_conj : S.w (y₂ * (a₁ * a₂) * y₂⁻¹) = (S.g : M2) *ᵥ S.w (a₁ * a₂) := by
    have h : S.w (y₂ * (a₁ * a₂) * y₂⁻¹) = ((S.rho ⟨y₂, hY.mem₂⟩).2 : M2) *ᵥ S.w (a₁ * a₂) :=
      S.hD.hT.w_conj S.N S.hD.hK.norm ⟨y₂, hY.mem₂⟩ hj'
    rw [hr2] at h
    exact h
  have hw0 : S.w (a₁ * a₂) = 0 := by
    apply gl2_order_three_fpf S.g hg3 hg1 (S.w (a₁ * a₂))
    have h := hw_conj
    rw [hy2] at h
    exact h.symm
  have hjZ : a₁ * a₂ ∈ S.A ⊓ S.A' := ⟨(S.hD.hT.cw.zero _ hj').1 hw0, hj'⟩
  have hy1 : y₁ * (a₁ * a₂) * y₁⁻¹ = a₁ * a₂ := by rw [h1, mul_inv_cancel_right]
  have hm_conj : S.m (y₁ * (a₁ * a₂) * y₁⁻¹) = (S.g : M2) * S.m (a₁ * a₂) := by
    have h : S.m (y₁ * (a₁ * a₂) * y₁⁻¹) = ((S.rho ⟨y₁, hY.mem₁⟩).1 : M2) * S.m (a₁ * a₂) *
        ((S.rho ⟨y₁, hY.mem₁⟩).2 : M2)ᵀ := S.hD.hT.m_conj S.N S.hD.hK.norm ⟨y₁, hY.mem₁⟩ hjZ
    rw [hr1] at h
    simpa using h
  have hm0 : S.m (a₁ * a₂) = 0 := by
    apply he42v_fix S.g hg3 hg1
    rw [← hm_conj, hy1]
  exact S.hD.hT.minj _ hjZ 1 (S.A ⊓ S.A').one_mem (by rw [hm0, S.hD.hT.m_one])

theorem HeSetup.stepV (S : HeSetup G) (hB : S.BaseFacts) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    S.StepV y₁ y₂ := by
  unfold HeSetup.StepV
  obtain ⟨hg3, hg1⟩ := he42v_g_facts S
  obtain ⟨s, hs⟩ := gl2_exists_inverting S.g hg3
  obtain ⟨d, hd⟩ := S.hD.hT.rho_surjective S.hD.hK (s, s)
  have hrd : S.rhoG (d : G) = (s, s) := by
    rw [S.rhoG_of_mem d.2]
    exact hd
  set Y : Subgroup G := Subgroup.closure ({y₁, y₂} : Set G) with hYdef
  have hY1 : y₁ ∈ Y := Subgroup.subset_closure (Set.mem_insert _ _)
  have hY2 : y₂ ∈ Y := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hYN : Y ≤ S.N := he42v_closure_le_N S hY
  have hYcard : Nat.card Y = 9 := he42v_Y_card S hY
  have hPcard : Nat.card (he42vP S) = 2304 := he42v_card_P S hB
  have hYP : Y ≤ he42vP S := by
    intro z hz
    rw [he42v_mem_P]
    refine ⟨hYN hz, ?_⟩
    rw [← S.rhoG_of_mem (hYN hz)]
    exact he42v_rho_Y_mem S hY hz
  set K : Subgroup G := Y.map (MulAut.conj (d : G)).toMonoidHom with hKdef
  have hKP : K ≤ he42vP S := by
    rintro _ ⟨z, hz, rfl⟩
    exact he42v_conj_mem_P S hY d.2 hz
  have hinj : Function.Injective (MulAut.conj (d : G)).toMonoidHom :=
    (MulAut.conj (d : G)).injective
  have hKcard : Nat.card K = 9 := by
    rw [hKdef, Subgroup.card_map_of_injective hinj, hYcard]
  obtain ⟨p, hpP, hpK⟩ := he42v_sylow_conj (he42vP S) Y K hYP hKP hYcard hKcard hPcard
  rw [he42v_mem_P] at hpP
  obtain ⟨hpN, hpY⟩ := hpP
  have hp' : S.rhoG p ∈ he42vYbar S.g := by
    rw [S.rhoG_of_mem hpN]
    exact hpY
  obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.1 hp'
  set v : G := p * (d : G) with hvdef
  have hvN : v ∈ S.N := S.N.mul_mem hpN d.2
  have hRv : S.rhoG v = S.rhoG p * (s, s) := by
    rw [hvdef, he42v_rhoG_mul S hpN d.2, hrd]
  have hRa : (S.rhoG v).1 = (S.rhoG p).1 * s := by
    rw [hRv]; rfl
  have hRc : (S.rhoG v).2 = (S.rhoG p).2 * s := by
    rw [hRv]; rfl
  have ha : (S.rhoG v).1 * S.g * (S.rhoG v).1⁻¹ = S.g⁻¹ := by
    rw [hRa]; exact he42v_inv_of_zpowers hs hp1
  have hc : (S.rhoG v).2 * S.g * (S.rhoG v).2⁻¹ = S.g⁻¹ := by
    rw [hRc]; exact he42v_inv_of_zpowers hs hp2
  have ha2 : (S.rhoG v).1 * (S.rhoG v).1 = 1 := he42v_inv_invol S.g _ hg3 hg1 ha
  have hc2 : (S.rhoG v).2 * (S.rhoG v).2 = 1 := he42v_inv_invol S.g _ hg3 hg1 hc
  have hvvN : v * v ∈ S.N := S.N.mul_mem hvN hvN
  have hvv_rho : S.rhoG (v * v) = 1 := by
    rw [he42v_rhoG_mul S hvN hvN]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.fst_one]
      exact ha2
    · simp only [Prod.snd_mul, Prod.snd_one]
      exact hc2
  have hvvJ : v * v ∈ S.A ⊔ S.A' := (he42v_rhoG_eq_one_iff S hvvN).1 hvv_rho
  have hconjY : ∀ z ∈ Y, v * z * v⁻¹ ∈ Y := by
    intro z hz
    have h := hpK ((MulAut.conj (d : G)).toMonoidHom z) (Subgroup.mem_map.2 ⟨z, hz, rfl⟩)
    have e : v * z * v⁻¹ = p * ((MulAut.conj (d : G)).toMonoidHom z) * p⁻¹ := by
      show v * z * v⁻¹ = p * ((d : G) * z * (d : G)⁻¹) * p⁻¹
      rw [hvdef]
      group
    rw [e]
    exact h
  have hyc1 : v * y₁ * v⁻¹ = y₁⁻¹ := by
    have hmem : v * y₁ * v⁻¹ ∈ Y := hconjY y₁ hY1
    refine he42v_rhoG_inj_Y S hY hmem (Y.inv_mem hY1) ?_
    rw [he42v_rhoG_mul S (S.N.mul_mem hvN hY.mem₁) (S.N.inv_mem hvN),
      he42v_rhoG_mul S hvN hY.mem₁, he42v_rhoG_inv S hvN, he42v_rhoG_inv S hY.mem₁, hY.rho₁]
    exact he42v_conj_pair _ _ ha
  have hyc2 : v * y₂ * v⁻¹ = y₂⁻¹ := by
    have hmem : v * y₂ * v⁻¹ ∈ Y := hconjY y₂ hY2
    refine he42v_rhoG_inj_Y S hY hmem (Y.inv_mem hY2) ?_
    rw [he42v_rhoG_mul S (S.N.mul_mem hvN hY.mem₂) (S.N.inv_mem hvN),
      he42v_rhoG_mul S hvN hY.mem₂, he42v_rhoG_inv S hvN, he42v_rhoG_inv S hY.mem₂, hY.rho₂]
    exact he42v_conj_pair' _ _ hc
  have hvv : v * v = 1 := by
    have hcomm1 : v * v * y₁ = y₁ * (v * v) := by
      have h1 : v * v * y₁ * (v * v)⁻¹ = y₁ := by
        calc v * v * y₁ * (v * v)⁻¹ = v * (v * y₁ * v⁻¹) * v⁻¹ := by group
          _ = v * y₁⁻¹ * v⁻¹ := by rw [hyc1]
          _ = (v * y₁ * v⁻¹)⁻¹ := by group
          _ = y₁ := by rw [hyc1, inv_inv]
      exact mul_inv_eq_iff_eq_mul.mp h1
    have hcomm2 : v * v * y₂ = y₂ * (v * v) := by
      have h1 : v * v * y₂ * (v * v)⁻¹ = y₂ := by
        calc v * v * y₂ * (v * v)⁻¹ = v * (v * y₂ * v⁻¹) * v⁻¹ := by group
          _ = v * y₂⁻¹ * v⁻¹ := by rw [hyc2]
          _ = (v * y₂ * v⁻¹)⁻¹ := by group
          _ = y₂ := by rw [hyc2, inv_inv]
      exact mul_inv_eq_iff_eq_mul.mp h1
    exact he42v_CJ_one S hY hvvJ hcomm1.symm hcomm2.symm
  refine ⟨v, hvv, hyc1, hyc2, ?_⟩
  intro b hb
  obtain ⟨hbZ, hbm⟩ := (S.hD.mem_B_iff S.hxN S.hxa S.hx3).1 hb
  have hmv : S.m (v * b * v⁻¹) = ((S.rho ⟨v, hvN⟩).1 : M2) * S.m b *
      ((S.rho ⟨v, hvN⟩).2 : M2)ᵀ := S.hD.hT.m_conj S.N S.hD.hK.norm ⟨v, hvN⟩ hbZ
  have hRv' : S.rho ⟨v, hvN⟩ = S.rhoG v := (S.rhoG_of_mem hvN).symm
  have ha' : (S.rho ⟨v, hvN⟩).1 * S.g * (S.rho ⟨v, hvN⟩).1⁻¹ = S.g⁻¹ := by
    rw [hRv']; exact ha
  have hc' : (S.rho ⟨v, hvN⟩).2 * S.g * (S.rho ⟨v, hvN⟩).2⁻¹ = S.g⁻¹ := by
    rw [hRv']; exact hc
  refine (S.hD.mem_B_iff S.hxN S.hxa S.hx3).2 ⟨S.hD.mem_Z_conj hvN hbZ, ?_⟩
  rw [hmv]
  exact he42v_B_conj S.g _ _ (S.m b) hg3 hg1 ha' hc' hbm

end CFSG.Quasithin.A94.He42
