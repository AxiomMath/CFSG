module

public import CFSG.Quasithin.Recognition.G2AmalE8Model
public import CFSG.Quasithin.Recognition.G2AmalE8Check
public import CFSG.Quasithin.Recognition.M12AmalE8Iso

public section

namespace CFSG.Quasithin.G2AmalE8

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.AmalTransport

@[expose] noncomputable def genP (k : ℕ) : Equiv.Perm (Fin 28) := if k = 5 then u33Pi else u33GenP k

theorem genP_of_ne {k : ℕ} (h : k ≠ 5) : genP k = u33GenP k := by simp [genP, h]

theorem genP_five : genP 5 = u33Pi := by simp [genP]

theorem genP_mem
    (k : ℕ) : genP k ∈ g2CG := by
  by_cases h : k = 5
  · subst h
    rw [genP_five]
    exact u33Pi_mem_g2CG
  · rw [genP_of_ne h]
    by_cases h5 : k < 5
    · rw [← u33PresHom_genPG k]
      exact u33PresHom_mem_g2CG _
    · have : u33GenP k = 1 := by simp [u33GenP, h5]
      rw [this]
      exact g2CG.one_mem

@[expose] noncomputable def genG
    (k : ℕ) : G2P := if k < 6 then ⟨genP k, genP_mem k⟩ else 1

theorem genG_coe
    (k : ℕ) (hk : k < 6) : ((genG k : G2P) : Equiv.Perm (Fin 28)) = genP k := by
  simp [genG, hk]

theorem genG_eq_g2F
    (k : ℕ) (hk : k < 5) : genG k = g2F (u33GenPG k) := by
  apply Subtype.ext
  rw [genG_coe k (by omega), g2F_coe, u33PresHom_genPG, genP_of_ne (by omega)]

theorem genG_five
    : genG 5 = g2E8Rho := by
  apply Subtype.ext
  rw [genG_coe 5 (by norm_num), g2E8Rho_coe, genP_five]

abbrev ReprN
    (l : List ℕ) (g : G2P) : Prop := RepL (n := 28) l (g : Equiv.Perm (Fin 28))

theorem reprN_mul
    {l m : List ℕ} {g h : G2P} (hl : ReprN l g) (hm : ReprN m h) :
    ReprN (compL l m) (g * h) := repL_mul hl hm

theorem eq_of_reprN
    {l : List ℕ} {g h : G2P} (hg : ReprN l g) (hh : ReprN l h) : g = h :=
  Subtype.ext (eq_of_repL hg hh)

theorem reprN_one
    : ReprN idl 1 := repL_one 28

theorem genTab_rep : ∀ k < 6, RepL (gl k) (genP k) := by
  unfold gl genP
  decide +kernel

theorem genInvTab_rep : ∀ k < 6, RepL (gil k) (genP k)⁻¹ := by
  unfold gil genP
  decide +kernel

theorem telTab_rep
    : ∀ i < 32, RepL (telTab.getD i []) (u33Tel u33GenP i) := by
  have h : telTab = u33TelTab := by decide +kernel
  rw [h]
  exact u33_telTab_rep

theorem piTab_rep : RepL piTab u33Pi := by
  have h : piTab = u33PiTab := by decide +kernel
  rw [h]
  exact u33_pi_rep

theorem reprN_gen
    (k : ℕ) (hk : k < 6) : ReprN (gl k) (genG k) := by
  have := genTab_rep k hk
  unfold ReprN
  rwa [genG_coe k hk]

theorem reprN_inv_gen
    (k : ℕ) (hk : k < 6) : ReprN (gil k) (genG k)⁻¹ := by
  have := genInvTab_rep k hk
  unfold ReprN
  rwa [Subgroup.coe_inv, genG_coe k hk]

@[expose] noncomputable def sG
    (i : ℕ) : G2P :=
  g2F (u33Tel u33GenPG (i % 32)) * g2E8Rho ^ (i / 32)

theorem sG_coe
    (i : ℕ) : ((sG i : G2P) : Equiv.Perm (Fin 28)) =
    u33Tel u33GenP (i % 32) * u33Pi ^ (i / 32) := by
  simp only [sG, Subgroup.coe_mul, Subgroup.coe_pow, g2F_coe, g2E8Rho_coe, u33Tel_hom]

theorem reprN_s
    (i : ℕ) (hi : i < 64) : ReprN (sl i) (sG i) := by
  unfold ReprN
  rw [sG_coe, sTab_chk i hi]
  by_cases h : i < 32
  · have e1 : i / 32 = 0 := Nat.div_eq_of_lt h
    simp only [h, ↓reduceIte, e1, pow_zero, mul_one]
    have := repL_mul (telTab_rep (i % 32) (by omega)) (repL_one 28)
    simpa [idl] using this
  · have e1 : i / 32 = 1 := by omega
    simp only [h, ↓reduceIte, e1, pow_one]
    exact repL_mul (telTab_rep (i % 32) (by omega)) piTab_rep

theorem sG_mul
    {i j : ℕ} (hi : i < 64) (hj : j < 64) : sG i * sG j = sG (smul i j) := by
  obtain ⟨hk, he⟩ := smul_chk i hi j hj
  exact eq_of_reprN (reprN_mul (reprN_s i hi) (reprN_s j hj))
    (show ReprN (compL (sl i) (sl j)) (sG (smul i j)) by rw [he]; exact reprN_s _ hk)

theorem sG_inv
    {i : ℕ} (hi : i < 64) : (sG i)⁻¹ = sG (sinv i) := by
  obtain ⟨hk, he⟩ := sinv_chk i hi
  have : sG i * sG (sinv i) = 1 :=
    eq_of_reprN (reprN_mul (reprN_s i hi) (reprN_s _ hk))
      (show ReprN (compL (sl i) (sl (sinv i))) 1 by rw [he]; exact reprN_one)
  exact inv_eq_of_mul_eq_one_right this

theorem sG_inj
    {i j : ℕ} (hi : i < 64) (hj : j < 64) (h : sG i = sG j) : i = j :=
  sl_inj_chk i hi j hj (repL_unique (reprN_s i hi) (h ▸ reprN_s j hj))

theorem sG_zero :
    sG 0 = 1 := by
  simp [sG, u33Tel_zero]

theorem sG_sq_eq_one_iff
    {i : ℕ} (hi : i < 64) : sG i ^ 2 = 1 ↔ smul i i = 0 := by
  rw [pow_two, sG_mul hi hi, ← sG_zero]
  exact ⟨fun h => sG_inj (smul_chk i hi i hi).1 (by norm_num) h, fun h => by rw [h]⟩

theorem g2E8Rho_inv
    : g2E8Rho⁻¹ = g2E8Rho := inv_eq_of_mul_eq_one_right g2_indexTwo.sq

theorem sG_mem_S
    {i : ℕ} (hi : i < 64) : sG i ∈ g2AmalL.S := by
  rw [g2L_S]
  have hT : g2F (u33Tel u33GenPG (i % 32)) ∈ g2_indexTwo.ext u33Data.T u33Phi'_T :=
    g2_indexTwo.map_le_ext u33Phi'_T
      ⟨u33Tel u33GenPG (i % 32), u33Data.Tel_mem_T ⟨i % 32, by omega⟩, rfl⟩
  by_cases h : i < 32
  · have e1 : i / 32 = 0 := Nat.div_eq_of_lt h
    unfold sG
    rw [e1, pow_zero, mul_one]
    exact hT
  · have e1 : i / 32 = 1 := by omega
    unfold sG
    rw [e1, pow_one]
    exact (g2_indexTwo.mem_ext).2 (Or.inr (by
      rw [mul_assoc, g2_indexTwo.sq, mul_one]
      exact ⟨_, u33Data.Tel_mem_T ⟨i % 32, by omega⟩, rfl⟩))

theorem exists_idx_of_mem_S
    {g : G2P} (hg : g ∈ g2AmalL.S) : ∃ i : ℕ, i < 64 ∧ g = sG i := by
  rw [g2L_S] at hg
  rcases (g2_indexTwo.mem_ext).1 hg with ⟨t, ht, rfl⟩ | ⟨t, ht, hgt⟩
  · obtain ⟨i, hi⟩ := (u33Data.mem_T_iff t).1 ht
    refine ⟨i, by omega, ?_⟩
    have e1 : (i : ℕ) % 32 = i := Nat.mod_eq_of_lt (by omega)
    have e2 : (i : ℕ) / 32 = 0 := Nat.div_eq_of_lt (by omega)
    unfold sG
    rw [e1, e2, pow_zero, mul_one]
    rw [← hi]
    rfl
  · obtain ⟨i, hi⟩ := (u33Data.mem_T_iff t).1 ht
    refine ⟨i + 32, by omega, ?_⟩
    have e1 : ((i : ℕ) + 32) % 32 = i := by omega
    have e2 : ((i : ℕ) + 32) / 32 = 1 := by omega
    unfold sG
    rw [e1, e2, pow_one]
    have : g = g2F t * g2E8Rho⁻¹ := by rw [hgt]; simp
    rw [this, g2E8Rho_inv, ← hi]
    rfl

theorem pCoreOf_le_S
    {H : Subgroup G2P} (hH : g2AmalL.S ≤ H) : pCoreOf 2 H ≤ g2AmalL.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S0 : Sylow 2 G2P := g2AmalL.sylow.1.toSylow g2AmalL.sylow.2
  have hP : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hnorm : g2AmalL.S ≤ Subgroup.normalizer (pCoreOf 2 H : Set G2P) :=
    hH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hsup : IsPGroup 2 (pCoreOf 2 H ⊔ g2AmalL.S : Subgroup G2P) :=
    hP.to_sup_of_normal_left' g2AmalL.sylow.1 hnorm
  have h1 : pCoreOf 2 H ⊔ g2AmalL.S = (S0 : Subgroup G2P) := S0.is_maximal' hsup le_sup_right
  have h2 : (S0 : Subgroup G2P) = g2AmalL.S := rfl
  rw [h2] at h1
  exact le_sup_left.trans h1.le

theorem conj_mem_pCoreOf_g2
    {H : Subgroup G2P} {g : G2P} (hg : g ∈ H) {p : G2P}
    (hp : p ∈ pCoreOf 2 H) : g * p * g⁻¹ ∈ pCoreOf 2 H ∧ g⁻¹ * p * g ∈ pCoreOf 2 H := by
  refine ⟨(Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg) p).1 hp, ?_⟩
  have h2 := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hg)) p).1 hp
  simpa using h2

@[expose] def idxSubgroup
    (L : List ℕ) (h0 : 0 ∈ L) (hlt : ∀ i ∈ L, i < 64)
    (hmul : ∀ i ∈ L, ∀ j ∈ L, smul i j ∈ L) (hinv : ∀ i ∈ L, sinv i ∈ L) : Subgroup G2P where
  carrier := {g | ∃ i ∈ L, g = sG i}
  one_mem' := ⟨0, h0, sG_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    exact ⟨smul i j, hmul i hi j hj, sG_mul (hlt i hi) (hlt j hj)⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨sinv i, hinv i hi, sG_inv (hlt i hi)⟩

theorem idxSubgroup_le_S
    {L : List ℕ} {h0 : 0 ∈ L} {hlt : ∀ i ∈ L, i < 64}
    {hmul : ∀ i ∈ L, ∀ j ∈ L, smul i j ∈ L} {hinv : ∀ i ∈ L, sinv i ∈ L} :
    idxSubgroup L h0 hlt hmul hinv ≤ g2AmalL.S := by
  rintro _ ⟨i, hi, rfl⟩
  exact sG_mem_S (hlt i hi)

theorem card_mem_list (X : List ℕ) (hX : X.Nodup) : Nat.card {i // i ∈ X} = X.length := by
  have e : Fin X.attach.length ≃ {i // i ∈ X} :=
    List.Nodup.getEquivOfForallMemList X.attach (hX.attach) (fun x => List.mem_attach X x)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin, List.length_attach]

theorem card_of_idx
    {B : Subgroup G2P} {X : List ℕ} (hX : X.Nodup) (hlt : ∀ i ∈ X, i < 64)
    (hB : ∀ g, g ∈ B ↔ ∃ i ∈ X, g = sG i) : Nat.card B = X.length := by
  have hinj : Function.Injective (fun i : {i // i ∈ X} => sG i.1) := fun i j h =>
    Subtype.ext (sG_inj (hlt _ i.2) (hlt _ j.2) h)
  have hrange : Set.range (fun i : {i // i ∈ X} => sG i.1) = (B : Set G2P) := by
    ext g
    simp only [Set.mem_range, SetLike.mem_coe, hB]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have h1 : Nat.card B = Nat.card (Set.range (fun i : {i // i ∈ X} => sG i.1)) := by
    rw [hrange]
    rfl
  rw [h1, Nat.card_range_of_injective hinj, card_mem_list X hX]

theorem closure_le_normalizer_of_conj_g2
    {K : Subgroup G2P} (S : Set G2P)
    (h : ∀ s ∈ S, ∀ k ∈ K, s * k * s⁻¹ ∈ K ∧ s⁻¹ * k * s ∈ K) :
    Subgroup.closure S ≤ Subgroup.normalizer (K : Set G2P) :=
  (Subgroup.closure_le _).2 fun s hs =>
    mem_normalizer_of_conj (fun k hk => (h s hs k hk).1) (fun k hk => (h s hs k hk).2)

theorem conj_gen_idx
    {k : ℕ} (hk : k < 6) {j i : ℕ} (hj : j < 64) (hi : i < 64)
    (h : genG k * sG j * (genG k)⁻¹ = sG i) :
    compL (compL (gl k) (sl j)) (gil k) = sl i := by
  have r1 : ReprN (compL (compL (gl k) (sl j)) (gil k)) (genG k * sG j * (genG k)⁻¹) :=
    reprN_mul (reprN_mul (reprN_gen k hk) (reprN_s j hj)) (reprN_inv_gen k hk)
  rw [h] at r1
  exact repL_unique r1 (reprN_s i hi)

theorem normFwd_of_le_normalizer
    {H Q : Subgroup G2P} {L : List ℕ} (hlt : ∀ i ∈ L, i < 64)
    (hQL : ∀ g, g ∈ Q ↔ ∃ i ∈ L, g = sG i) {gs : List ℕ}
    (hgs : ∀ k ∈ gs, k < 6 ∧ genG k ∈ H) (hN : H ≤ Subgroup.normalizer (Q : Set G2P)) :
    NormFwd gs L := by
  intro k hk j hj
  obtain ⟨hk6, hkH⟩ := hgs k hk
  have hjQ : sG j ∈ Q := (hQL _).2 ⟨j, hj, rfl⟩
  have h1 : genG k * sG j * (genG k)⁻¹ ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 (hN hkH) (sG j)).1 hjQ
    exact this
  obtain ⟨i', hi', hi'e⟩ := (hQL _).1 h1
  exact ⟨i', hi', conj_gen_idx hk6 (hlt j hj) (hlt i' hi') hi'e⟩

theorem closure_le_normalizer_idx
    {gs : List ℕ} (hgs : ∀ k ∈ gs, k < 6) {L : List ℕ} {h0 : 0 ∈ L}
    {hlt : ∀ i ∈ L, i < 64} {hmul : ∀ i ∈ L, ∀ j ∈ L, smul i j ∈ L} {hinv : ∀ i ∈ L, sinv i ∈ L}
    (hN : NormBoth gs L) :
    Subgroup.closure {g : G2P | ∃ k ∈ gs, g = genG k} ≤
      Subgroup.normalizer (idxSubgroup L h0 hlt hmul hinv : Set G2P) := by
  refine closure_le_normalizer_of_conj_g2 _ ?_
  rintro s ⟨g, hg, rfl⟩ k ⟨j, hj, rfl⟩
  have hj64 := hlt j hj
  have hg6 := hgs g hg
  obtain ⟨⟨k₁, hk₁, hl₁⟩, ⟨k₂, hk₂, hl₂⟩⟩ := hN g hg j hj
  have r1 : ReprN (compL (compL (gl g) (sl j)) (gil g)) (genG g * sG j * (genG g)⁻¹) :=
    reprN_mul (reprN_mul (reprN_gen g hg6) (reprN_s j hj64)) (reprN_inv_gen g hg6)
  have r2 : ReprN (compL (compL (gil g) (sl j)) (gl g)) ((genG g)⁻¹ * sG j * genG g) :=
    reprN_mul (reprN_mul (reprN_inv_gen g hg6) (reprN_s j hj64)) (reprN_gen g hg6)
  exact ⟨⟨k₁, hk₁, eq_of_reprN r1 (by rw [hl₁]; exact reprN_s k₁ (hlt k₁ hk₁))⟩,
    ⟨k₂, hk₂, eq_of_reprN r2 (by rw [hl₂]; exact reprN_s k₂ (hlt k₂ hk₂))⟩⟩

theorem genG_mem_S
    {k : ℕ} (hk : k ∈ [0, 1, 2, 5]) : genG k ∈ g2AmalL.S := by
  rw [g2L_S]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · rw [genG_eq_g2F 0 (by norm_num)]
    exact g2_indexTwo.map_le_ext u33Phi'_T ⟨_, u33Data.a_mem_T, rfl⟩
  · rw [genG_eq_g2F 1 (by norm_num)]
    exact g2_indexTwo.map_le_ext u33Phi'_T ⟨_, u33Data.b_mem_T, rfl⟩
  · rw [genG_eq_g2F 2 (by norm_num)]
    exact g2_indexTwo.map_le_ext u33Phi'_T ⟨_, u33Data.s_mem_T, rfl⟩
  · rw [genG_five]
    exact g2_indexTwo.rho_mem_ext u33Phi'_T

theorem genG_mem_P₁
    {k : ℕ} (hk : k ∈ [0, 1, 2, 3, 5]) : genG k ∈ g2AmalL.P₁ := by
  by_cases h3 : k = 3
  · subst h3
    rw [g2L_P₁, genG_eq_g2F 3 (by norm_num)]
    exact g2_indexTwo.map_le_ext u33Phi'_A ⟨_, u33Data.x_mem_A, rfl⟩
  · have hS : genG k ∈ g2AmalL.S := genG_mem_S (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      omega)
    exact g2AmalL.S_le_P₁ hS

theorem genG_mem_P₂
    {k : ℕ} (hk : k ∈ [0, 1, 2, 4, 5]) : genG k ∈ g2AmalL.P₂ := by
  by_cases h4 : k = 4
  · subst h4
    rw [g2L_P₂, genG_eq_g2F 4 (by norm_num)]
    exact g2_indexTwo.map_le_ext u33Phi'_B ⟨_, u33Data.y_mem_B, rfl⟩
  · have hS : genG k ∈ g2AmalL.S := genG_mem_S (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
      omega)
    exact g2AmalL.S_le_P₂ hS

theorem ext_le_closure
    {H₀ : Subgroup U33G} {hH : ∀ x ∈ H₀, u33Phi' x ∈ H₀} {gs : List ℕ}
    {gens : Set U33G} (hH₀ : H₀ = Subgroup.closure gens)
    (hgens : ∀ u ∈ gens, ∃ k ∈ gs, g2F u = genG k) (hρ : ∃ k ∈ gs, g2E8Rho = genG k) :
    g2_indexTwo.ext H₀ hH ≤ Subgroup.closure {g : G2P | ∃ k ∈ gs, g = genG k} := by
  intro g hg
  have hmap : H₀.map g2F ≤ Subgroup.closure {g : G2P | ∃ k ∈ gs, g = genG k} := by
    rw [hH₀, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨k, hk, hke⟩ := hgens u hu
    exact Subgroup.subset_closure ⟨k, hk, hke⟩
  rcases (g2_indexTwo.mem_ext).1 hg with h | h
  · exact hmap h
  · have hrho : g2E8Rho ∈ Subgroup.closure {g : G2P | ∃ k ∈ gs, g = genG k} := by
      obtain ⟨k, hk, hke⟩ := hρ
      exact Subgroup.subset_closure ⟨k, hk, hke⟩
    have : g = (g * g2E8Rho) * g2E8Rho⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (hmap h) (Subgroup.inv_mem _ hrho)

theorem P₁_le_closure
    : g2AmalL.P₁ ≤ Subgroup.closure {g : G2P | ∃ k ∈ ([0, 1, 2, 3, 5] : List ℕ), g = genG k} := by
  rw [g2L_P₁]
  refine ext_le_closure (gs := [0, 1, 2, 3, 5]) (gens := {u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3}) rfl ?_ ?_
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp, (genG_eq_g2F 0 (by norm_num)).symm⟩
    · exact ⟨1, by simp, (genG_eq_g2F 1 (by norm_num)).symm⟩
    · exact ⟨2, by simp, (genG_eq_g2F 2 (by norm_num)).symm⟩
    · exact ⟨3, by simp, (genG_eq_g2F 3 (by norm_num)).symm⟩
  · exact ⟨5, by simp, genG_five.symm⟩

theorem P₂_le_closure
    : g2AmalL.P₂ ≤ Subgroup.closure {g : G2P | ∃ k ∈ ([0, 1, 2, 4, 5] : List ℕ), g = genG k} := by
  rw [g2L_P₂]
  refine ext_le_closure (gs := [0, 1, 2, 4, 5]) (gens := {u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 4}) rfl ?_ ?_
  · intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp, (genG_eq_g2F 0 (by norm_num)).symm⟩
    · exact ⟨1, by simp, (genG_eq_g2F 1 (by norm_num)).symm⟩
    · exact ⟨2, by simp, (genG_eq_g2F 2 (by norm_num)).symm⟩
    · exact ⟨4, by simp, (genG_eq_g2F 4 (by norm_num)).symm⟩
  · exact ⟨5, by simp, genG_five.symm⟩

theorem P₁_le_normalizer_idx
    {L : List ℕ} {h0 : 0 ∈ L} {hlt : ∀ i ∈ L, i < 64}
    {hmul : ∀ i ∈ L, ∀ j ∈ L, smul i j ∈ L} {hinv : ∀ i ∈ L, sinv i ∈ L}
    (hN : NormBoth [0, 1, 2, 3, 5] L) :
    g2AmalL.P₁ ≤ Subgroup.normalizer (idxSubgroup L h0 hlt hmul hinv : Set G2P) :=
  P₁_le_closure.trans (closure_le_normalizer_idx (by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega) hN)

theorem P₂_le_normalizer_idx
    {L : List ℕ} {h0 : 0 ∈ L} {hlt : ∀ i ∈ L, i < 64}
    {hmul : ∀ i ∈ L, ∀ j ∈ L, smul i j ∈ L} {hinv : ∀ i ∈ L, sinv i ∈ L}
    (hN : NormBoth [0, 1, 2, 4, 5] L) :
    g2AmalL.P₂ ≤ Subgroup.normalizer (idxSubgroup L h0 hlt hmul hinv : Set G2P) :=
  P₂_le_closure.trans (closure_le_normalizer_idx (by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega) hN)

@[expose] noncomputable def Qsub
    : Subgroup G2P :=
  idxSubgroup qIdx qIdx_chk.2.2.2.1 qIdx_chk.2.2.1 qIdx_chk.2.2.2.2 qIdx_inv_chk

@[expose] noncomputable def Csub
    : Subgroup G2P :=
  idxSubgroup cIdx cIdx_chk.2.2.2.1 cIdx_chk.2.2.1 cIdx_chk.2.2.2.2 cIdx_inv_chk

theorem pCoreOf_eq_idx
    {H : Subgroup G2P} (hSH : g2AmalL.S ≤ H) {k : ℕ} (hk : k < 6) (hkH : genG k ∈ H)
    {L : List ℕ} {h0 : 0 ∈ L} {hlt : ∀ i ∈ L, i < 64} {hmul : ∀ i ∈ L, ∀ j ∈ L, smul i j ∈ L}
    {hinv : ∀ i ∈ L, sinv i ∈ L} (hiff : ∀ i < 64, LX k i ↔ i ∈ L)
    (hnorm : H ≤ Subgroup.normalizer (idxSubgroup L h0 hlt hmul hinv : Set G2P)) :
    pCoreOf 2 H = idxSubgroup L h0 hlt hmul hinv := by
  apply le_antisymm
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := exists_idx_of_mem_S (pCoreOf_le_S hSH hg)
    obtain ⟨h1, h2⟩ := conj_mem_pCoreOf_g2 hkH hg
    obtain ⟨j₁, hj₁, hj₁e⟩ := exists_idx_of_mem_S (pCoreOf_le_S hSH h1)
    obtain ⟨j₂, hj₂, hj₂e⟩ := exists_idx_of_mem_S (pCoreOf_le_S hSH h2)
    have r1 : ReprN (compL (compL (gl k) (sl i)) (gil k)) (genG k * sG i * (genG k)⁻¹) :=
      reprN_mul (reprN_mul (reprN_gen k hk) (reprN_s i hi)) (reprN_inv_gen k hk)
    have r2 : ReprN (compL (compL (gil k) (sl i)) (gl k)) ((genG k)⁻¹ * sG i * genG k) :=
      reprN_mul (reprN_mul (reprN_inv_gen k hk) (reprN_s i hi)) (reprN_gen k hk)
    rw [hj₁e] at r1
    rw [hj₂e] at r2
    have hLX : LX k i := by
      refine ⟨?_, ?_⟩
      · rw [repL_unique r1 (reprN_s j₁ hj₁)]
        exact sl_mem_chk j₁ hj₁
      · rw [repL_unique r2 (reprN_s j₂ hj₂)]
        exact sl_mem_chk j₂ hj₂
    exact ⟨i, (hiff i hi).1 hLX, rfl⟩
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (idxSubgroup_le_S.trans hSH) hnorm (g2AmalL.sylow.1.to_le idxSubgroup_le_S)

theorem pCoreOf_P₂_eq
    : pCoreOf 2 g2AmalL.P₂ = Qsub :=
  pCoreOf_eq_idx g2AmalL.S_le_P₂ (by norm_num) (genG_mem_P₂ (by simp)) qIdx_iff_chk
    (P₂_le_normalizer_idx qIdx_norm_chk)

theorem pCoreOf_P₁_eq
    : pCoreOf 2 g2AmalL.P₁ = Csub :=
  pCoreOf_eq_idx g2AmalL.S_le_P₁ (by norm_num) (genG_mem_P₁ (by simp)) cIdx_iff_chk
    (P₁_le_normalizer_idx cIdx_norm_chk)

theorem pCoreOf_P₂_le_inf
    : pCoreOf 2 g2AmalL.P₂ ≤ g2AmalL.P₂ ⊓ g2AmalL.P₁ := by
  rw [pCoreOf_P₂_eq]
  exact le_inf (idxSubgroup_le_S.trans g2AmalL.S_le_P₂) (idxSubgroup_le_S.trans g2AmalL.S_le_P₁)

@[expose] noncomputable def q8Hom
    (A X : List ℕ) (h : Q8Tab A X) : QuaternionGroup 2 →* G2P where
  toFun g := sG (q8Idx' A X g)
  map_one' := by
    show sG (q8Idx' A X 1) = 1
    rw [h.2.2]
    exact sG_zero
  map_mul' g g' := by
    obtain ⟨hg, hg', he⟩ := h.1 g g'
    have hgg := (h.1 (g * g') 1).1
    have key : sG (q8Idx' A X g) * sG (q8Idx' A X g') = sG (q8Idx' A X (g * g')) := by
      refine eq_of_reprN (reprN_mul (reprN_s _ hg) (reprN_s _ hg')) ?_
      rw [he]
      exact reprN_s _ hgg
    exact key.symm

theorem q8Hom_apply
    (A X : List ℕ) (h : Q8Tab A X) (g : QuaternionGroup 2) :
    q8Hom A X h g = sG (q8Idx' A X g) := rfl

theorem q8Hom_injective
    (A X : List ℕ) (h : Q8Tab A X) : Function.Injective (q8Hom A X h) := by
  intro g g' he
  exact h.2.1 g g' (sG_inj ((h.1 g 1).1) ((h.1 g' 1).1) he)

theorem isQ8Sq_of_homs
    {W : Subgroup G2P} (f₁ f₂ : QuaternionGroup 2 →* G2P)
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂)
    (h₁W : ∀ g, f₁ g ∈ W) (h₂W : ∀ g, f₂ g ∈ W)
    (hcomm : ∀ g h, f₁ g * f₂ h = f₂ h * f₁ g)
    (hgen : ∀ w ∈ W, ∃ g h, w = f₁ g * f₂ h) (hcard : Nat.card W = 32) : IsQ8Sq ↥W := by
  have hle₁ : f₁.range ≤ W := by
    rintro _ ⟨g, rfl⟩
    exact h₁W g
  have hle₂ : f₂.range ≤ W := by
    rintro _ ⟨g, rfl⟩
    exact h₂W g
  refine ⟨hcard, f₁.range.subgroupOf W, f₂.range.subgroupOf W, ⟨?_, ?_⟩,
    ⟨(Subgroup.subgroupOfEquivOfLe hle₁).trans (MonoidHom.ofInjective hf₁).symm⟩,
    ⟨(Subgroup.subgroupOfEquivOfLe hle₂).trans (MonoidHom.ofInjective hf₂).symm⟩⟩
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨g, hg⟩ : ∃ g, f₁ g = a.1 := ha
    obtain ⟨h, hh⟩ : ∃ h, f₂ h = b.1 := hb
    apply Subtype.ext
    show b.1 * a.1 = a.1 * b.1
    rw [← hg, ← hh]
    exact (hcomm g h).symm
  · rw [eq_top_iff]
    intro w _
    obtain ⟨g, h, hw⟩ := hgen w.1 w.2
    have e : w = ⟨f₁ g, h₁W g⟩ * ⟨f₂ h, h₂W h⟩ := Subtype.ext hw
    rw [e]
    exact Subgroup.mul_mem_sup (show (⟨f₁ g, h₁W g⟩ : ↥W) ∈ f₁.range.subgroupOf W from ⟨g, rfl⟩)
      (show (⟨f₂ h, h₂W h⟩ : ↥W) ∈ f₂.range.subgroupOf W from ⟨h, rfl⟩)

theorem isQ8Sq_Qsub
    : IsQ8Sq ↥Qsub := by
  obtain ⟨hinc_a, hinc_b⟩ := q8_incl_chk
  obtain ⟨hsa, hsb, hra, hrb⟩ := q8_surj_chk
  have hlt : ∀ (A X : List ℕ) (h : Q8Tab A X) (g : QuaternionGroup 2), q8Idx' A X g < 64 :=
    fun A X h g => (h.1 g 1).1
  have hcard : Nat.card Qsub = 32 := by
    rw [card_of_idx qIdx_chk.2.1 qIdx_chk.2.2.1 (fun g => Iff.rfl)]
    exact qIdx_chk.1
  refine isQ8Sq_of_homs (q8Hom q8aA q8aX q8a_chk) (q8Hom q8bA q8bX q8b_chk)
    (q8Hom_injective _ _ _) (q8Hom_injective _ _ _) (fun g => ?_) (fun g => ?_) (fun g h => ?_)
    (fun w hw => ?_) hcard
  · exact ⟨q8Idx' q8aA q8aX g, hinc_a _ (hra g), rfl⟩
  · exact ⟨q8Idx' q8bA q8bX g, hinc_b _ (hrb g), rfl⟩
  · rw [q8Hom_apply, q8Hom_apply, sG_mul (hlt _ _ q8a_chk g) (hlt _ _ q8b_chk h),
      sG_mul (hlt _ _ q8b_chk h) (hlt _ _ q8a_chk g)]
    exact congrArg sG (q8_comm_chk _ (hra g) _ (hrb h))
  · obtain ⟨i, hi, rfl⟩ := hw
    obtain ⟨a, ha, b, hb, hab⟩ := q8_gen_chk i hi
    obtain ⟨g, rfl⟩ := hsa a ha
    obtain ⟨h, rfl⟩ := hsb b hb
    refine ⟨g, h, ?_⟩
    rw [q8Hom_apply, q8Hom_apply, sG_mul (hlt _ _ q8a_chk g) (hlt _ _ q8b_chk h), hab]

theorem isQ8Sq_pCoreOf_P₂
    : IsQ8Sq ↥(pCoreOf 2 g2AmalL.P₂) := by
  rw [pCoreOf_P₂_eq]
  exact isQ8Sq_Qsub

@[expose] noncomputable def Esub
    : Subgroup G2P :=
  idxSubgroup eIdx eIdx_chk.2.2.2.1 (fun i hi => qIdx_chk.2.2.1 i (eIdx_chk.2.2.1 i hi))
    (fun i hi j hj => (eIdx_chk.2.2.2.2 i hi j hj).1) eIdx_inv_chk

theorem Esub_le_Qsub
    : Esub ≤ Qsub := by
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, eIdx_chk.2.2.1 i hi, rfl⟩

theorem Esub_elem
    : IsElemAbelian 2 Esub := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨x, i, hi, rfl⟩ := x
    obtain ⟨y, j, hj, rfl⟩ := y
    apply Subtype.ext
    show sG i * sG j = sG j * sG i
    have hi' := qIdx_chk.2.2.1 i (eIdx_chk.2.2.1 i hi)
    have hj' := qIdx_chk.2.2.1 j (eIdx_chk.2.2.1 j hj)
    rw [sG_mul hi' hj', sG_mul hj' hi', (eIdx_chk.2.2.2.2 i hi j hj).2.1]
  · rintro _ ⟨i, hi, rfl⟩
    have hi' := qIdx_chk.2.2.1 i (eIdx_chk.2.2.1 i hi)
    rw [pow_two, sG_mul hi' hi', (eIdx_chk.2.2.2.2 i hi i hi).2.2]
    exact sG_zero

theorem card_Esub
    : Nat.card Esub = 8 := by
  rw [card_of_idx eIdx_chk.2.1 (fun i hi => qIdx_chk.2.2.1 i (eIdx_chk.2.2.1 i hi)) (fun g => Iff.rfl)]
  exact eIdx_chk.1

theorem P₁_le_normalizer_Esub
    : g2AmalL.P₁ ≤ Subgroup.normalizer (Esub : Set G2P) :=
  P₁_le_normalizer_idx eIdx_norm_chk

theorem V4_le_Esub
    (V : Subgroup G2P) (hVQ : V ≤ Qsub) (hV4 : Nat.card V = 4)
    (hN : g2AmalL.P₁ ≤ Subgroup.normalizer (V : Set G2P)) : V ≤ Esub := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ : ∃ a : ↥V, orderOf a = 2 :=
    exists_prime_orderOf_dvd_card' 2 (by rw [hV4]; norm_num)
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  obtain ⟨b, hb1, hba⟩ : ∃ b : ↥V, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (fun t : Bool => if t then (1 : ↥V) else a) := by
      intro v
      by_cases hv : v = 1
      · exact ⟨true, by simp [hv]⟩
      · exact ⟨false, by simp [hcon v hv]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hV4, Nat.card_eq_fintype_card, Fintype.card_bool] at this
    omega
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    have h1 : a⁻¹ = b := mul_eq_one_iff_inv_eq.1 h
    have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    exact h1.symm.trans h2
  have hab2 : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab3 : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hall : ∀ v : ↥V, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
    have : Fintype ↥V := Fintype.ofFinite _
    have hcard : Fintype.card ↥V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hV4
    have n1 : (1 : ↥V) ∉ ({a, b, a * b} : Finset ↥V) := by
      simp [ha1.symm, hb1.symm, hab1.symm]
    have n2 : a ∉ ({b, a * b} : Finset ↥V) := by
      simp [hba.symm, hab2.symm]
    have hs : ({1, a, b, a * b} : Finset ↥V).card = 4 := by
      rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
        Finset.card_pair (Ne.symm hab3)]
    have := Finset.eq_univ_of_card ({1, a, b, a * b} : Finset ↥V) (by rw [hs, hcard])
    intro v
    have hv : v ∈ ({1, a, b, a * b} : Finset ↥V) := by rw [this]; exact Finset.mem_univ v
    simpa using hv
  obtain ⟨ia, hia, hae⟩ := hVQ a.2
  obtain ⟨ib, hib, hbe⟩ := hVQ b.2
  have hia64 := qIdx_chk.2.2.1 ia hia
  have hib64 := qIdx_chk.2.2.1 ib hib
  have hiab64 := (smul_chk ia hia64 ib hib64).1
  have hX : ∀ g, g ∈ V ↔ ∃ k ∈ [0, ia, ib, smul ia ib], g = sG k := by
    intro g
    constructor
    · intro hg
      rcases hall ⟨g, hg⟩ with h | h | h | h
      · refine ⟨0, by simp, ?_⟩
        rw [sG_zero]
        exact congrArg Subtype.val h
      · exact ⟨ia, by simp, (congrArg Subtype.val h).trans hae⟩
      · exact ⟨ib, by simp, (congrArg Subtype.val h).trans hbe⟩
      · refine ⟨smul ia ib, by simp, ?_⟩
        rw [← sG_mul hia64 hib64, ← hae, ← hbe]
        exact congrArg Subtype.val h
    · rintro ⟨k, hk, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · rw [sG_zero]
        exact V.one_mem
      · rw [← hae]
        exact a.2
      · rw [← hbe]
        exact b.2
      · rw [← sG_mul hia64 hib64, ← hae, ← hbe]
        exact V.mul_mem a.2 b.2
  have hXlt : ∀ k ∈ [0, ia, ib, smul ia ib], k < 64 := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · norm_num
    · exact hia64
    · exact hib64
    · exact hiab64
  have hclosure : ∀ i ∈ [0, ia, ib, smul ia ib], ∀ j ∈ [0, ia, ib, smul ia ib],
      smul i j ∈ [0, ia, ib, smul ia ib] := by
    intro i hi j hj
    have hi' := hXlt i hi
    have hj' := hXlt j hj
    have hmem : sG (smul i j) ∈ V := by
      rw [← sG_mul hi' hj']
      exact V.mul_mem ((hX _).2 ⟨i, hi, rfl⟩) ((hX _).2 ⟨j, hj, rfl⟩)
    obtain ⟨k, hk, hke⟩ := (hX _).1 hmem
    rw [sG_inj (smul_chk i hi' j hj').1 (hXlt k hk) hke]
    exact hk
  have hnorm : NormFwd [0, 1, 2, 3, 5] [0, ia, ib, smul ia ib] :=
    normFwd_of_le_normalizer (H := g2AmalL.P₁) hXlt hX
      (fun k hk => ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega,
        genG_mem_P₁ hk⟩) hN
  have hia0 : ia ≠ 0 := by
    intro h
    apply ha1
    apply Subtype.ext
    show (a : G2P) = 1
    rw [hae, h]
    exact sG_zero
  have hib0 : ib ≠ 0 := by
    intro h
    apply hb1
    apply Subtype.ext
    show (b : G2P) = 1
    rw [hbe, h]
    exact sG_zero
  have hibia : ib ≠ ia := by
    intro h
    apply hba
    apply Subtype.ext
    show (b : G2P) = a
    rw [hae, hbe, h]
  have hiasq : smul ia ia = 0 := by
    apply (sG_sq_eq_one_iff hia64).1
    have : (a : G2P) ^ 2 = 1 := by
      have := congrArg Subtype.val ha2
      simpa using this
    rwa [hae] at this
  obtain ⟨h1, h2, h3⟩ := V4_chk ia ((invQIdx_chk.2 ia hia hia0 hiasq)) ib hib hib0 hibia hclosure hnorm
  intro g hg
  obtain ⟨k, hk, rfl⟩ := (hX g).1 hg
  refine ⟨k, ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact eIdx_chk.2.2.2.1
  · exact h1
  · exact h2
  · exact h3

theorem g2E8Concl_model
    : E8Concl g2AmalL.P₂ g2AmalL.P₁ := by
  unfold E8Concl
  rw [pCoreOf_P₂_eq]
  exact ⟨Esub, Esub_le_Qsub, Esub_elem, card_Esub, P₁_le_normalizer_Esub,
    fun V hVQ hV4 hN => V4_le_Esub V hVQ hV4 hN⟩

theorem card_center_pCoreOf_P₁_ne_two
    : Nat.card ↥(centerOf (pCoreOf 2 g2AmalL.P₁)) ≠ 2 := by
  intro h2
  obtain ⟨h8, h12, hn8, hn12, hne, hcen⟩ := cIdx_central_chk
  have h8' : sG 8 ∈ pCoreOf 2 g2AmalL.P₁ := by
    rw [pCoreOf_P₁_eq]
    exact ⟨8, h8, rfl⟩
  have h12' : sG 12 ∈ pCoreOf 2 g2AmalL.P₁ := by
    rw [pCoreOf_P₁_eq]
    exact ⟨12, h12, rfl⟩
  have hc : ∀ (m : ℕ), m = 8 ∨ m = 12 → sG m ∈ centerOf (pCoreOf 2 g2AmalL.P₁) := by
    intro m hm
    have hm' : m ∈ cIdx := by rcases hm with rfl | rfl <;> assumption
    have hm64 := cIdx_chk.2.2.1 m hm'
    refine Subgroup.mem_inf.2 ⟨by rw [pCoreOf_P₁_eq]; exact ⟨m, hm', rfl⟩,
      Subgroup.mem_centralizer_iff.2 ?_⟩
    intro p hp
    rw [pCoreOf_P₁_eq] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    have hi64 := cIdx_chk.2.2.1 i hi
    have hcm : smul m i = smul i m := by rcases hm with rfl | rfl
                                         · exact (hcen i hi).1
                                         · exact (hcen i hi).2
    rw [sG_mul hi64 hm64, sG_mul hm64 hi64, hcm]
  have hne1 : ∀ m : ℕ, m < 64 → sl m ≠ idl → sG m ≠ 1 := fun m hm hl h =>
    hl (repL_unique (reprN_s m hm) (h ▸ reprN_one))
  have h0 : sG 8 ≠ 1 := hne1 8 (by norm_num) hn8
  have h1 : sG 12 ≠ 1 := hne1 12 (by norm_num) hn12
  have h01 : sG 8 ≠ sG 12 := fun h => hne (repL_unique (reprN_s 8 (by norm_num)) (h ▸ reprN_s 12 (by norm_num)))
  obtain ⟨w, hw, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(centerOf (pCoreOf 2 g2AmalL.P₁)))).1 h2
  have hu0 : (⟨sG 8, hc 8 (Or.inl rfl)⟩ : ↥(centerOf (pCoreOf 2 g2AmalL.P₁))) ≠ 1 := by
    intro h
    apply h0
    have := congrArg Subtype.val h
    exact this
  have hu1 : (⟨sG 12, hc 12 (Or.inr rfl)⟩ : ↥(centerOf (pCoreOf 2 g2AmalL.P₁))) ≠ 1 := by
    intro h
    apply h1
    have := congrArg Subtype.val h
    exact this
  have e0 := huniq _ hu0
  have e1 := huniq _ hu1
  have key := congrArg Subtype.val (e0.trans e1.symm)
  exact h01 key

end CFSG.Quasithin.G2AmalE8
