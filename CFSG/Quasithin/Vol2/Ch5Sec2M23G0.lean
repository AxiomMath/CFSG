module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23L34
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Local
import CFSG.Quasithin.Vol2.Ch5Sec2M23Gamma
import CFSG.Quasithin.Vol2.Ch5Sec2M23G0Data
public import CFSG.Quasithin.Vol2.Ch5Sec2M23G0DataInputs

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

variable {G : Type} [Group G]

section Elements

theorem coe_map_mul_self {P : Subgroup M22} {A : Subgroup G} (φ : ↥P ≃* ↥A) {x : M22}
    (hx : x ∈ P) (hxx : x * x = 1) : ((φ ⟨x, hx⟩ : ↥A) : G) * ((φ ⟨x, hx⟩ : ↥A) : G) = 1 := by
  have e : (⟨x, hx⟩ : ↥P) * ⟨x, hx⟩ = 1 := Subtype.ext hxx
  have h := congrArg (fun z => ((φ z : ↥A) : G)) e
  simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at h
  exact h

theorem coe_map_conj_eq_inv {P : Subgroup M22} {A : Subgroup G} (φ : ↥P ≃* ↥A) {x y : M22}
    (hx : x ∈ P) (hy : y ∈ P) (hxx : x * x = 1) (hxy : x * y * x * y = 1) :
    ((φ ⟨x, hx⟩ : ↥A) : G) * ((φ ⟨y, hy⟩ : ↥A) : G) * ((φ ⟨x, hx⟩ : ↥A) : G)⁻¹ =
      ((φ ⟨y, hy⟩ : ↥A) : G)⁻¹ := by
  have e : (⟨x, hx⟩ : ↥P) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥P)⁻¹ = (⟨y, hy⟩ : ↥P)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [inv_eq_of_mul_eq_one_right hxx]
    exact eq_inv_of_mul_eq_one_left hxy
  have h := congrArg (fun z => ((φ z : ↥A) : G)) e
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h
  exact h

theorem exists_elements_of_isParabolicIsoData_of {A1 A2 : Subgroup G}
    (h : IsParabolicIsoData A1 A2) {b₀ s₀ t₀ : M22}
    (hb0 : (b₀ : Equiv.Perm (Fin 22)) 0 = 0) (hb1 : (b₀ : Equiv.Perm (Fin 22)) 1 = 1)
    (hbP : PresHex b₀) (hb3 : b₀ ^ 3 = 1) (hbne : b₀ ≠ 1)
    (hs0 : (s₀ : Equiv.Perm (Fin 22)) 0 = 0) (hs1 : (s₀ : Equiv.Perm (Fin 22)) 1 = 1)
    (hsP : ¬ PresHex s₀) (hss : s₀ * s₀ = 1) (hsb : s₀ * b₀ * s₀ * b₀ = 1)
    (ht0 : (t₀ : Equiv.Perm (Fin 22)) 0 = 0) (ht1 : (t₀ : Equiv.Perm (Fin 22)) 1 = 19)
    (htP : PresHex t₀) (htt : t₀ * t₀ = 1) (htb : t₀ * b₀ * t₀ * b₀ = 1) :
    ∃ b s t : G, b ∈ A1 ∧ b ∈ A2 ∧ s ∈ A1 ∧ s ∉ A2 ∧ t ∈ A2 ∧ t ∉ A1 ∧ orderOf b = 3 ∧
      s * s = 1 ∧ t * t = 1 ∧ s * b * s⁻¹ = b⁻¹ ∧ t * b * t⁻¹ = b⁻¹ := by
  obtain ⟨φ₁, φ₂, hagree, hmem⟩ := h
  have hbT : b₀ ∈ m22TwoStab :=
    Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr hb0,
      MulAction.mem_stabilizer_iff.mpr hb1⟩
  have hbH : b₀ ∈ m22PtHexStab :=
    Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr hb0, mem_m22HexStab_iff.mpr hbP⟩
  have hsT : s₀ ∈ m22TwoStab :=
    Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr hs0,
      MulAction.mem_stabilizer_iff.mpr hs1⟩
  have hsH : s₀ ∉ m22PtHexStab := fun h =>
    hsP (mem_m22HexStab_iff.mp (Subgroup.mem_inf.mp h).2)
  have htH : t₀ ∈ m22PtHexStab :=
    Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr ht0, mem_m22HexStab_iff.mpr htP⟩
  have htT : t₀ ∉ m22TwoStab := fun h => by
    have h1 : (t₀ : Equiv.Perm (Fin 22)) 1 = 1 :=
      MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp h).2
    rw [ht1] at h1
    exact absurd h1 (by decide)
  have hb' : ((φ₁ ⟨b₀, hbT⟩ : ↥A1) : G) = ((φ₂ ⟨b₀, hbH⟩ : ↥A2) : G) := hagree _ hbT hbH
  refine ⟨(φ₁ ⟨b₀, hbT⟩ : ↥A1), (φ₁ ⟨s₀, hsT⟩ : ↥A1), (φ₂ ⟨t₀, htH⟩ : ↥A2),
    (φ₁ _).2, hb' ▸ (φ₂ _).2, (φ₁ _).2, fun h => hsH ((hmem _).mp h), (φ₂ _).2, ?_, ?_,
    coe_map_mul_self φ₁ hsT hss, coe_map_mul_self φ₂ htH htt,
    coe_map_conj_eq_inv φ₁ hsT hbT hss hsb, ?_⟩
  ·
    intro ht
    set q := φ₁.symm ⟨_, ht⟩ with hqdef
    have hq : ((φ₁ q : ↥A1) : G) = ((φ₂ ⟨t₀, htH⟩ : ↥A2) : G) := by
      rw [hqdef, MulEquiv.apply_symm_apply]
    have hqH : (q : M22) ∈ m22PtHexStab := (hmem q).mp (hq ▸ (φ₂ _).2)
    have h2 := hagree q q.2 hqH
    rw [hq] at h2
    have h3 : (⟨t₀, htH⟩ : ↥m22PtHexStab) = ⟨q, hqH⟩ := φ₂.injective (Subtype.ext h2)
    have h4 : t₀ = (q : M22) := congrArg Subtype.val h3
    apply htT
    rw [h4]
    exact q.2
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime hb3 hbne
  · rw [hb']
    exact coe_map_conj_eq_inv φ₂ htH hbH htt htb

theorem exists_elements_of_isParabolicIsoData
    {A1 A2 : Subgroup G}
    (h : IsParabolicIsoData A1 A2) :
    ∃ b s t : G, b ∈ A1 ∧ b ∈ A2 ∧ s ∈ A1 ∧ s ∉ A2 ∧ t ∈ A2 ∧ t ∉ A1 ∧ orderOf b = 3 ∧
      s * s = 1 ∧ t * t = 1 ∧ s * b * s⁻¹ = b⁻¹ ∧ t * b * t⁻¹ = b⁻¹ := by
  obtain ⟨hb0, hb1, hbP, hb3, hbne⟩ := m22Bt3_spec
  obtain ⟨hs0, hs1, hsP, hss, hsb⟩ := m22Inv1_spec
  obtain ⟨-, -, -, ⟨ht0, ht1, htP⟩⟩ := m22Fix_spec
  obtain ⟨htt, htb⟩ := m22Fix19_inv_spec
  exact exists_elements_of_isParabolicIsoData_of (b₀ := m22Bt3) (s₀ := m22Inv1)
    (t₀ := m22Fix19) h hb0 hb1 hbP hb3 hbne hs0 hs1 hsP hss hsb ht0 ht1 htP htt htb

theorem exists_elements_of_isAmalgamOfGroup
    {G1 G2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G1 G2) (IsLieOverTwo .PSL 3 2)) :
    ∃ b s1 s2 : G, b ∈ G1 ∧ b ∈ G2 ∧ s1 ∈ G1 ∧ s1 ∉ G2 ∧ s2 ∈ G2 ∧ s2 ∉ G1 ∧
      orderOf b = 3 ∧ s1 * s1 = 1 ∧ s2 * s2 = 1 ∧ s1 * b * s1⁻¹ = b⁻¹ ∧
      s2 * b * s2⁻¹ = b⁻¹ := by
  rcases isParabolicIsoData_of_isAmalgamOfGroup hα with h | h
  · exact exists_elements_of_isParabolicIsoData h
  · obtain ⟨b, s, t, hb2, hb1, hs2, hs1, ht1, ht2, hb3, hss, htt, hsb, htb⟩ :=
      exists_elements_of_isParabolicIsoData h
    exact ⟨b, t, s, hb1, hb2, ht1, ht2, hs2, hs1, hb3, htt, hss, htb, hsb⟩

end Elements

theorem ne_top_of_hyp5_0_1 [Finite G] {T M L : Subgroup G} {n : ℕ} (h : Hyp5_0_1 G T M L n) :
    M ≠ ⊤ := by
  intro hM
  have : IsSimpleGroup G := h.simple
  obtain ⟨P, hP1, hP2, hPM⟩ := h.maxTwoLocal.1
  have hn : P.Normal := Subgroup.normalizer_eq_top_iff.mp (hPM.symm.trans hM)
  rcases hn.eq_bot_or_eq_top with hb | ht
  · exact hP1 hb
  · subst ht
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : IsPGroup 2 G := hP2.of_equiv Subgroup.topEquiv
    have hnt := h2.center_nontrivial
    have hc : Subgroup.center G = ⊤ := by
      rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hb | ht
      · exact ((Subgroup.nontrivial_iff_ne_bot _).mp hnt hb).elim
      · exact ht
    obtain ⟨a, b, hab⟩ := h.nonabelian
    have hb : b ∈ Subgroup.center G := hc ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem mem_normalizer_zpowers_of_conj_eq_inv {x s : G} (h : s * x * s⁻¹ = x⁻¹) :
    s ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
  have h' : s⁻¹ * x * s = x⁻¹ := by
    calc s⁻¹ * x * s = s⁻¹ * (x⁻¹)⁻¹ * s := by rw [inv_inv]
      _ = s⁻¹ * (s * x * s⁻¹)⁻¹ * s := by rw [h]
      _ = x⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow, h]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) k
  · intro hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hy' : y = (s⁻¹ * x * s) ^ k := by
      have e := conj_zpow (a := s⁻¹) (b := x) (i := k)
      rw [inv_inv] at e
      rw [e, hk]
      group
    rw [hy', h']
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) k

@[expose] def M23Fusion3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfTypeM23 M L H B D T →
      ∀ b x : G, b ∈ D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H → x ∈ M ⊓ centralizerModO2 L →
        orderOf b = 3 → orderOf x = 3 → ∃ c : G, c * b * c⁻¹ = x

variable [Finite G]

theorem exists_involutions_m23_of
    (hset : Stmt5_2_10_setting) (hfus : M23Fusion3)
    (h515 : Stmt5_2_15) {T M L V H B D L₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T) :
    ∃ s t : G, s ∈ L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) ∧
      s ∉ D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H ∧ t ∈ D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H ∧
      t ∉ L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) ∧ s * s = 1 ∧ t * t = 1 ∧
      orderOf (s * t) ≤ 3 := by
  obtain ⟨M2, π, hS⟩ := hset G T M L V H B D L₂ n hyp hM23
  have hα := hM23.1
  obtain ⟨b, s1, s2, hb1, hb2, hs11, hs12, hs22, hs21, hb3, hs1s1, hs2s2, hs1b, hs2b⟩ :=
    exists_elements_of_isAmalgamOfGroup hα
  have hG1M : L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) ≤ M :=
    sup_le (sup_le hyp.L_le (inf_le_right.trans hyp.L_le))
      (inf_le_left.trans (hyp.notation59.1.1.trans inf_le_left))
  have hbM : b ∈ M := hG1M hb1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X, hX, -⟩ := exists_isSylowIn_ge 3 (bot_le : ⊥ ≤ M ⊓ centralizerModO2 L)
    IsPGroup.of_bot
  obtain ⟨hNM, K, _, _, hK, ⟨Ψ⟩⟩ := h515 G T M L V H B D L₂ n M2 π hyp hM23 hS X hX
  have hXM : X ≤ M := hX.le.trans inf_le_left
  have hXMN : X ≤ M ⊓ Subgroup.normalizer (X : Set G) := le_inf hXM Subgroup.le_normalizer
  have hcardX : Nat.card X ≤ 3 := by
    have h := card_le_three_of_mulEquiv Ψ hK
      (Y := X.subgroupOf (M ⊓ Subgroup.normalizer (X : Set G)))
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXMN).mpr inf_le_right)
      (fun y hy => by
        obtain ⟨k, hk⟩ := hX.isPGroup ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
        refine ⟨k, Subtype.ext ?_⟩
        have := congrArg Subtype.val hk
        simpa using this)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXMN).toEquiv] at h
  have hXne : X ≠ ⊥ := by
    intro hXb
    have h1 : Subgroup.normalizer (X : Set G) = ⊤ := by
      rw [hXb]
      exact Subgroup.normalizer_eq_top_iff.mpr inferInstance
    exact ne_top_of_hyp5_0_1 hyp.toHyp5_0_1 (eq_top_iff.mpr (h1 ▸ hNM))
  have hcard3 : Nat.card X = 3 := by
    obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hX.isPGroup
    have hne1 : Nat.card X ≠ 1 := fun h1 => hXne (Subgroup.card_eq_one.mp h1)
    have he1 : e ≤ 1 := by
      by_contra hlt
      have h9 : 3 ^ 2 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← he] at h9
      omega
    interval_cases e
    · exact absurd (by rw [he, pow_zero]) hne1
    · rw [he, pow_one]
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx3 : orderOf x = 3 := by
    have hd : orderOf x ∣ 3 := hcard3 ▸ Subgroup.orderOf_dvd_natCard X hxX
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1'
    · exact h
  have hXeq : Subgroup.zpowers x = X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX)
      (by rw [hcard3, Nat.card_zpowers, hx3])
  obtain ⟨c, hc⟩ := hfus G T M L V H B D L₂ n hyp hM23 b x hb2 (hX.le hxX) hb3 hx3
  have hconj : ∀ s : G, s * b * s⁻¹ = b⁻¹ → (c * s * c⁻¹) * x * (c * s * c⁻¹)⁻¹ = x⁻¹ := by
    intro s hs
    rw [← hc]
    calc c * s * c⁻¹ * (c * b * c⁻¹) * (c * s * c⁻¹)⁻¹ = c * (s * b * s⁻¹) * c⁻¹ := by group
      _ = (c * b * c⁻¹)⁻¹ := by rw [hs]; group
  have hsq : ∀ s : G, s * s = 1 → (c * s * c⁻¹) * (c * s * c⁻¹) = 1 := by
    intro s hs
    calc c * s * c⁻¹ * (c * s * c⁻¹) = c * (s * s) * c⁻¹ := by group
      _ = 1 := by rw [hs]; group
  set N := M ⊓ Subgroup.normalizer (X : Set G) with hNdef
  have hmemN : ∀ s : G, s * x * s⁻¹ = x⁻¹ → s ∈ N := by
    intro s hs
    have hsN : s ∈ Subgroup.normalizer (X : Set G) := by
      rw [← hXeq]
      exact mem_normalizer_zpowers_of_conj_eq_inv hs
    exact Subgroup.mem_inf.mpr ⟨hNM hsN, hsN⟩
  have hxN : x ∈ N := hXMN hxX
  have hs1N := hmemN _ (hconj s1 hs1b)
  have hs2N := hmemN _ (hconj s2 hs2b)
  obtain ⟨j, hj⟩ := exists_orderOf_mul_le_three_of_mulEquiv Ψ hK (x := ⟨x, hxN⟩)
    (s := ⟨_, hs1N⟩) (t := ⟨_, hs2N⟩) (by rw [Subgroup.orderOf_mk, hx3])
    (fun h => by
      have hh : (h : G) * x * (h : G)⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp h.2).2 x).mp hxX
      rw [← hXeq] at hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩)
    (Subtype.ext (hsq s1 hs1s1)) (Subtype.ext (hsq s2 hs2s2)) (Subtype.ext (hconj s1 hs1b))
    (Subtype.ext (hconj s2 hs2b))
  have hj' : orderOf (b ^ j * s1 * s2) ≤ 3 := by
    have e : ((⟨x, hxN⟩ ^ j * ⟨_, hs1N⟩ * ⟨_, hs2N⟩ : ↥N) : G) =
        c * (b ^ j * s1 * s2) * c⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_pow]
      rw [← hc, conj_pow]
      group
    have hsc : SemiconjBy c (b ^ j * s1 * s2) (c * (b ^ j * s1 * s2) * c⁻¹) := by
      unfold SemiconjBy
      group
    rw [← Subgroup.orderOf_coe, e, ← hsc.orderOf_eq] at hj
    exact hj
  have hbj1 : b ^ j * s1 ∈ L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H) :=
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hb1 j) hs11
  have hbj2 : b ^ j * s1 ∉ D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H := fun h => hs12 (by
    have h' := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hb2 j)) h
    rwa [inv_mul_cancel_left] at h')
  have hbjsq : (b ^ j * s1) * (b ^ j * s1) = 1 := by
    have h1 : s1 * b ^ j * s1⁻¹ = (b ^ j)⁻¹ := by rw [← conj_pow, hs1b, inv_pow]
    calc b ^ j * s1 * (b ^ j * s1) = b ^ j * (s1 * b ^ j * s1⁻¹) * (s1 * s1) := by group
      _ = 1 := by rw [h1, hs1s1]; group
  exact ⟨_, _, hbj1, hbj2, hs22, hs21, hbjsq, hs2s2, hj'⟩

theorem lieModel_m23G0_of
    (hset : Stmt5_2_10_setting) (hfus : M23Fusion3) (h515 : Stmt5_2_15)
    {T M L V H B D L₂ : Subgroup G} {n : ℕ} (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hM23 : IsOfTypeM23 M L H B D T) : LieModel ↥(m23G0 M L H B D) .PSL 3 2 2 := by
  obtain ⟨s, t, hs1, hs2, ht2, ht1, hss, htt, hst⟩ :=
    exists_involutions_m23_of hset hfus h515 hyp hM23
  exact lieModel_sup_of_isAmalgamOfGroup hM23.1 hs1 hs2 ht2 ht1 hss htt hst

end CFSG.Quasithin.H13
