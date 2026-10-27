module

public import CFSG.Quasithin.Recognition.Kleidman.VBOdd.Ctx
public import CFSG.Quasithin.Recognition.SzVBOddL24Master

public section

namespace CFSG.Quasithin.Kleidman.VBOdd

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.SzVB

section Aux

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_closed {N : Subgroup G} {g : G} (h1 : ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (h2 : ∀ n ∈ N, g⁻¹ * n * g ∈ N) : g ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h1 n, fun h => ?_⟩
  have := h2 _ h
  have e : g⁻¹ * (g * n * g⁻¹) * g = n := by group
  rwa [e] at this

omit [Finite G] in
theorem conj_mem_pCoreOf {P : Subgroup G} {p z : G} (hp : p ∈ P) (hz : z ∈ pCoreOf 2 P) :
    p * z * p⁻¹ ∈ pCoreOf 2 P := by
  have : (CFSG.Open.pCore 2 ↥P).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  exact KerAux.conj_mem_map_subtype (CFSG.Open.pCore 2 ↥P) hp hz

theorem pCoreOf_inf_le {K P : Subgroup G} (hKP : K ≤ P) :
    pCoreOf 2 P ⊓ K ≤ pCoreOf 2 K := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).to_le inf_le_left)
  intro k hk
  refine mem_normalizer_of_closed (fun n hn => ?_) (fun n hn => ?_)
  · exact ⟨conj_mem_pCoreOf (hKP hk) hn.1, K.mul_mem (K.mul_mem hk hn.2) (K.inv_mem hk)⟩
  · have := conj_mem_pCoreOf (P := P) (hKP (K.inv_mem hk)) hn.1
    exact ⟨by simpa using this, K.mul_mem (K.mul_mem (K.inv_mem hk) hn.2) hk⟩

theorem pCoreOf_le_pCoreOf {K P : Subgroup G} (hKP : K ≤ P)
    (hPN : P ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 K ≤ pCoreOf 2 P := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKP) (fun p hp => ?_)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have : (CFSG.Open.pCore 2 ↥K).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (CFSG.Open.pCore 2 ↥K) (hPN hp)

omit [Finite G] in
theorem mem_pCore_of_mem_pCoreOf {K : Subgroup G} {x : G} (hx : x ∈ pCoreOf 2 K) (hxK : x ∈ K) :
    (⟨x, hxK⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact hy

omit [Finite G] in
theorem le_pCoreOf_or_le_sup {K M : Subgroup G} [Group.IsPerfect ↥K]
    (hS : IsSimpleGroup (↥K ⧸ CFSG.Open.pCore 2 ↥K)) (hMK : M ≤ K)
    (hM : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M) :
    M ≤ pCoreOf 2 K ∨ K ≤ M ⊔ pCoreOf 2 K := by
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) with hπ
  have hN : ((M.subgroupOf K).map π).Normal := by
    refine Subgroup.Normal.map ?_ π (QuotientGroup.mk'_surjective _)
    exact ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hM g g.2 x hx⟩
  have := hN
  rcases hS.eq_bot_or_eq_top_of_normal ((M.subgroupOf K).map π) with h | h
  · left
    intro m hm
    have hmK := hMK hm
    have h1 : π ⟨m, hmK⟩ ∈ (M.subgroupOf K).map π :=
      ⟨⟨m, hmK⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
    rw [h] at h1
    have h2 : (⟨m, hmK⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := by
      rw [← QuotientGroup.ker_mk' (CFSG.Open.pCore 2 ↥K)]
      exact (Subgroup.mem_bot.mp h1)
    exact ⟨_, h2, rfl⟩
  · right
    intro k hk
    have h1 : π ⟨k, hk⟩ ∈ (M.subgroupOf K).map π := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨m', hm', hm'k⟩ := h1
    have h2 : m'⁻¹ * ⟨k, hk⟩ ∈ CFSG.Open.pCore 2 ↥K := by
      have h0 : π (m'⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hm'k, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥K) (m'⁻¹ * (⟨k, hk⟩ : ↥K))).mp h0
    have h3 : ((m'⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K := ⟨_, h2, rfl⟩
    have h4 : (m' : G) ∈ M := Subgroup.mem_subgroupOf.mp hm'
    have e : k = (m' : G) * ((m'⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by
      simp
    rw [e]
    exact Subgroup.mul_mem_sup h4 h3

omit [Finite G] in
theorem isSimple_of_isL2Quot_two {X : Type} [Group X] (h : IsL2Quot 2 X) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  have hF4 : 4 ≤ Nat.card (GaloisField 2 2) := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF4
  exact e.isSimpleGroup

omit [Finite G] in
theorem mem_pCoreOf_of_comm {K : Subgroup G} [Group.IsPerfect ↥K]
    (hS : IsSimpleGroup (↥K ⧸ CFSG.Open.pCore 2 ↥K)) {k0 : G} (hk0 : k0 ∈ K)
    (hc : ∀ k ∈ K, k0 * k * k0⁻¹ * k⁻¹ ∈ pCoreOf 2 K) : k0 ∈ pCoreOf 2 K := by
  set π := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) with hπ
  have hz : π ⟨k0, hk0⟩ ∈ Subgroup.center (↥K ⧸ CFSG.Open.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : (⟨k0, hk0⟩ : ↥K) * k * (⟨k0, hk0⟩ : ↥K)⁻¹ * k⁻¹ ∈ CFSG.Open.pCore 2 ↥K :=
      mem_pCore_of_mem_pCoreOf (hc k k.2) _
    have h0 : π ((⟨k0, hk0⟩ : ↥K) * k * (⟨k0, hk0⟩ : ↥K)⁻¹ * k⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥K) _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h0
    have h2 := mul_inv_eq_one.mp h0
    show π k * π ⟨k0, hk0⟩ = π ⟨k0, hk0⟩ * π k
    symm
    calc π ⟨k0, hk0⟩ * π k = (π ⟨k0, hk0⟩ * π k * (π ⟨k0, hk0⟩)⁻¹) * π ⟨k0, hk0⟩ := by group
      _ = π k * π ⟨k0, hk0⟩ := by rw [h2]
  have hbot : Subgroup.center (↥K ⧸ CFSG.Open.pCore 2 ↥K) = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center (↥K ⧸ CFSG.Open.pCore 2 ↥K)) with h | h
    · exact h
    · exfalso
      have : IsMulCommutative (↥K ⧸ CFSG.Open.pCore 2 ↥K) :=
        ⟨⟨fun a b => ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a)) b).symm⟩⟩
      have : Group.IsPerfect (↥K ⧸ CFSG.Open.pCore 2 ↥K) := inferInstance
      have := hS.toNontrivial
      exact (not_subsingleton (↥K ⧸ CFSG.Open.pCore 2 ↥K)) inferInstance
  rw [hbot, Subgroup.mem_bot] at hz
  exact ⟨⟨k0, hk0⟩, (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥K) _).mp hz, rfl⟩

theorem perm_even_involution_fixed {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (hΩ : Nat.card Ω = 5)
    (σ : Equiv.Perm Ω) (h2 : σ * σ = 1) (h1 : σ ≠ 1) (hs : Equiv.Perm.sign σ = 1) :
    ∃ ω, σ ω = ω ∧ ∀ U, σ U = U → U = ω := by
  have hc : Fintype.card Ω = 5 := by rw [← Nat.card_eq_fintype_card]; exact hΩ
  let e : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hc
  let φ : Equiv.Perm Ω ≃* Equiv.Perm (Fin 5) := e.permCongrHom
  have hφ : ∀ (p : Equiv.Perm Ω) (x : Ω), φ p (e x) = e (p x) := by
    intro p x
    simp [φ, Equiv.permCongr_apply]
  have hfin : ∀ τ : Equiv.Perm (Fin 5), τ * τ = 1 → τ ≠ 1 → Equiv.Perm.sign τ = 1 →
      ∃ ω, τ ω = ω ∧ ∀ U, τ U = U → U = ω := by decide +kernel
  have hsign : Equiv.Perm.sign (φ σ) = 1 := by
    rw [← hs]
    exact Equiv.Perm.sign_permCongr e σ
  obtain ⟨ω', hω', hu'⟩ := hfin (φ σ) (by rw [← map_mul, h2, map_one])
    (fun h => h1 (φ.injective (by rw [h, map_one]))) hsign
  obtain ⟨x, rfl⟩ := e.surjective ω'
  refine ⟨x, ?_, ?_⟩
  · apply e.injective
    rw [← hφ]
    exact hω'
  · intro U hU
    apply e.injective
    apply hu'
    rw [hφ, hU]

end Aux

section Setting

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem sup_le_normalizer_K1 (h : R1SettingLegacyBare K1 L2 S Zs) :
    K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) :=
  sup_le Subgroup.le_normalizer h.hyp.h1.normalizes

theorem exists_mul_of_mem_sup (h : R1SettingLegacyBare K1 L2 S Zs) (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S))
    {p : G} (hp : p ∈ K1 ⊔ S) : ∃ k ∈ K1, ∃ q ∈ pCoreOf 2 (K1 ⊔ S), p = k * q := by
  have hle : K1 ⊔ S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S) := sup_le le_sup_left hA5
  exact (F1.mem_sup_iff_exists_mul_of_normalizes
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_normalizer_K1 h))).mp (hle hp)

theorem pCoreOf_le_S (h : R1SettingLegacyBare K1 L2 S Zs) : pCoreOf 2 (K1 ⊔ S) ≤ S :=
  F7.isSylowTwoOf_pCoreOf_le
    (F112J2.isSylowTwoOf_K1S (F112J2.hyp111R_of_setting rankOneListedFacts h))

theorem mem_kerAct_of_mem_pCoreOf (h : R1SettingLegacyBare K1 L2 S Zs) {x : ↥(K1 ⊔ S)}
    (hx : (x : G) ∈ pCoreOf 2 (K1 ⊔ S)) : x ∈ kerAct (K1 ⊔ S) (conjClosure Zs L2) := by
  rw [OddAux.mem_kerAct]
  intro U
  obtain ⟨y, hy, hU⟩ := U.2
  apply Subtype.ext
  show conjSub (x : G) U.1 = U.1
  have hp : y⁻¹ * (x : G) * y⁻¹⁻¹ ∈ pCoreOf 2 (K1 ⊔ S) :=
    conj_mem_pCoreOf ((K1 ⊔ S).inv_mem hy) hx
  have hpN := S_le_normalizer_conjClosure rankOneListedFacts h (pCoreOf_le_S h hp)
  have e : (x : G) * y = y * (y⁻¹ * (x : G) * y⁻¹⁻¹) := by group
  rw [hU, ← conjSub_mul, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer hpN]

theorem ker_le_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1))
    (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S)) :
    ∀ x : ↥(K1 ⊔ S), x ∈ kerAct (K1 ⊔ S) (conjClosure Zs L2) →
      (x : G) ∈ pCoreOf 2 (K1 ⊔ S) := by
  intro x hx
  have hRO : RankOneListedFacts.{0} := rankOneListedFacts
  have hK1P : K1 ≤ K1 ⊔ S := le_sup_left
  have hPN := sup_le_normalizer_K1 h
  have : Group.IsPerfect ↥K1 := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp h.cComp_mem)
  have hcomm : ∀ k ∈ K1, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K1 := fun k hk =>
    comm_mem_pCoreOf_of_mem_kerAct hRO h (n := 2) le_rfl (Or.inl hL) hK1P hPN
      ⟨x, hx, rfl⟩ hk
  obtain ⟨k0, hk0, q, hq, hxe⟩ := exists_mul_of_mem_sup h hA5 x.2
  have hqP : q ∈ K1 ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  have hk0O : k0 ∈ pCoreOf 2 K1 := by
    refine mem_pCoreOf_of_comm (isSimple_of_isL2Quot_two hL) hk0 fun k hk => ?_
    have hc : q * k * q⁻¹ * k⁻¹ ∈ pCoreOf 2 K1 := by
      refine pCoreOf_inf_le hK1P ⟨?_, ?_⟩
      · have := (pCoreOf 2 (K1 ⊔ S)).mul_mem hq (conj_mem_pCoreOf (hK1P hk)
          ((pCoreOf 2 (K1 ⊔ S)).inv_mem hq))
        have e : q * (k * q⁻¹ * k⁻¹) = q * k * q⁻¹ * k⁻¹ := by group
        rwa [e] at this
      · exact K1.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPN hqP) k).mp hk) (K1.inv_mem hk)
    have h2 := conj_mem_pCoreOf (P := K1) hk0 hc
    have e : k0 * k * k0⁻¹ * k⁻¹ = (k0 * (q * k * q⁻¹ * k⁻¹) * k0⁻¹)⁻¹ *
        ((x : G) * k * (x : G)⁻¹ * k⁻¹) := by
      rw [hxe]; group
    rw [e]
    exact (pCoreOf 2 K1).mul_mem ((pCoreOf 2 K1).inv_mem h2) (hcomm k hk)
  rw [hxe]
  exact (pCoreOf 2 (K1 ⊔ S)).mul_mem (pCoreOf_le_pCoreOf hK1P hPN hk0O) hq

theorem inv_one_fixed_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1))
    (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S)) :
    ∀ x : ↥(K1 ⊔ S), x * x = 1 → x ∉ kerAct (K1 ⊔ S) (conjClosure Zs L2) →
      ∃ ω : ConjSet (K1 ⊔ S) (conjClosure Zs L2), x • ω = ω ∧
        ∀ U : ConjSet (K1 ⊔ S) (conjClosure Zs L2), x • U = U → U = ω := by
  classical
  intro x hx2 hxk
  have hK1P : K1 ≤ K1 ⊔ S := le_sup_left
  have : Group.IsPerfect ↥K1 := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp h.cComp_mem)
  have : Fintype (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) := Fintype.ofFinite _
  set ρ := MulAction.toPermHom ↥(K1 ⊔ S) (ConjSet (K1 ⊔ S) (conjClosure Zs L2)) with hρ
  obtain ⟨k0, hk0, q, hq, hxe⟩ := exists_mul_of_mem_sup h hA5 x.2
  have hxab : x = (⟨k0, hK1P hk0⟩ : ↥(K1 ⊔ S)) *
      (⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq⟩ : ↥(K1 ⊔ S)) := Subtype.ext hxe
  have hb : (⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq⟩ : ↥(K1 ⊔ S)) ∈
      kerAct (K1 ⊔ S) (conjClosure Zs L2) := mem_kerAct_of_mem_pCoreOf h hq
  have hρb : ρ ⟨q, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq⟩ = 1 := hb
  have hρx : ρ x = ρ ⟨k0, hK1P hk0⟩ := by rw [hxab, map_mul, hρb, mul_one]
  let φ : ↥K1 →* ℤˣ := Equiv.Perm.sign.comp (ρ.comp (Subgroup.inclusion hK1P))
  have hφ : φ ⟨k0, hk0⟩ = 1 := by
    have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    have hsub : Subsingleton φ.range := inferInstance
    have := congrArg Subtype.val (Subsingleton.elim (⟨φ ⟨k0, hk0⟩, ⟨_, rfl⟩⟩ : φ.range) 1)
    simpa using this
  have hsign : Equiv.Perm.sign (ρ x) = 1 := by rw [hρx]; exact hφ
  have hσ2 : ρ x * ρ x = 1 := by rw [← map_mul, hx2, map_one]
  have hσ1 : ρ x ≠ 1 := fun h1 => hxk h1
  obtain ⟨ω, hω, hu⟩ := perm_even_involution_fixed
    (l24Facts_of_setting rankOneListedFacts h hL).card_five (ρ x) hσ2 hσ1 hsign
  exact ⟨ω, hω, fun U hU => hu U hU⟩

theorem simple_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1))
    (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S)) : ∀ C : Subgroup G, C ≤ K1 ⊔ S →
    K1 ⊔ S ≤ Subgroup.normalizer (C : Set G) → ¬ C ≤ pCoreOf 2 (K1 ⊔ S) →
    C ⊔ pCoreOf 2 (K1 ⊔ S) = K1 ⊔ S := by
  intro C hCP hCN hCnot
  have hK1P : K1 ≤ K1 ⊔ S := le_sup_left
  have hPN := sup_le_normalizer_K1 h
  have : Group.IsPerfect ↥K1 := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp h.cComp_mem)
  have hSimple := isSimple_of_isL2Quot_two hL
  have hO2P : pCoreOf 2 (K1 ⊔ S) ≤ K1 ⊔ S := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hNconj : ∀ p ∈ K1 ⊔ S, ∀ x ∈ C ⊔ pCoreOf 2 (K1 ⊔ S),
      p * x * p⁻¹ ∈ C ⊔ pCoreOf 2 (K1 ⊔ S) := by
    intro p hp x hx
    obtain ⟨c, hc, q, hq, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (fun a ha => hCN (hO2P ha))).mp hx
    have e : p * (c * q) * p⁻¹ = (p * c * p⁻¹) * (p * q * p⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hCN hp) c).mp hc))
      (Subgroup.mem_sup_right (conj_mem_pCoreOf hp hq))
  have hM : ∀ k ∈ K1, ∀ m ∈ (C ⊔ pCoreOf 2 (K1 ⊔ S)) ⊓ K1,
      k * m * k⁻¹ ∈ (C ⊔ pCoreOf 2 (K1 ⊔ S)) ⊓ K1 := fun k hk m hm =>
    ⟨hNconj k (hK1P hk) m hm.1, K1.mul_mem (K1.mul_mem hk hm.2) (K1.inv_mem hk)⟩
  rcases le_pCoreOf_or_le_sup hSimple inf_le_right hM with hM1 | hM2
  · exfalso
    apply hCnot
    intro c hc
    obtain ⟨k0, hk0, q, hq, rfl⟩ := exists_mul_of_mem_sup h hA5 (hCP hc)
    have hk0N : k0 ∈ C ⊔ pCoreOf 2 (K1 ⊔ S) := by
      have e : k0 = (k0 * q) * q⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc)
        (Subgroup.mem_sup_right ((pCoreOf 2 (K1 ⊔ S)).inv_mem hq))
    exact (pCoreOf 2 (K1 ⊔ S)).mul_mem
      (pCoreOf_le_pCoreOf hK1P hPN (hM1 ⟨hk0N, hk0⟩)) hq
  · have hK1N : K1 ≤ C ⊔ pCoreOf 2 (K1 ⊔ S) :=
      hM2.trans (sup_le inf_le_left ((pCoreOf_le_pCoreOf hK1P hPN).trans le_sup_right))
    exact le_antisymm (sup_le hCP hO2P) (sup_le hK1N (hA5.trans (sup_le hK1N le_sup_right)))

theorem twin_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) : ∀ t ∈ K1 ⊔ S,
    t ∈ Subgroup.normalizer (conjClosure Zs L2 : Set G) →
    ∀ l ∈ L2 ⊔ S, ∃ l' ∈ L2 ⊔ S, l'⁻¹ * (t * l) ∈ K1 ⊔ S := by
  intro t htP htN l hl
  have htL := mem_normalizer_L2_of_mem_normalizer_V rankOneListedFacts h htP htN
  obtain ⟨m, hm, σ, hσ, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes h.hyp.h2.normalizes).mp hl
  have hm' : t * m * t⁻¹ ∈ L2 := (Subgroup.mem_normalizer_iff.mp htL m).mp hm
  refine ⟨t * m * t⁻¹, Subgroup.mem_sup_left hm', ?_⟩
  have e : (t * m * t⁻¹)⁻¹ * (t * (m * σ)) = t * σ := by group
  rw [e]
  exact (K1 ⊔ S).mul_mem htP (Subgroup.mem_sup_right hσ)

theorem prim_of_setting (h : R1SettingLegacyBare K1 L2 S Zs) (hL : IsL2Quot 2 (OTwoQuot K1))
    (hA5 : S ≤ K1 ⊔ pCoreOf 2 (K1 ⊔ S))
    (hab : IsElemAbelian 2 (conjClosure (conjClosure Zs L2) (K1 ⊔ S))) {z : G}
    (hK : KleinData (K1 ⊔ S) (conjClosure Zs L2) z) :
    Prim (K1 ⊔ S) S (conjClosure Zs L2) z where
  klein := hK
  l24 := l24Facts_of_setting rankOneListedFacts h hL
  abel := hab
  ker_le := ker_le_of_setting h hL hA5
  inv_one_fixed := inv_one_fixed_of_setting h hL hA5

end Setting

end CFSG.Quasithin.Kleidman.VBOdd
