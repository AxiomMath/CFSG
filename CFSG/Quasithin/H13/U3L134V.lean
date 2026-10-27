module

public import CFSG.Quasithin.H13.A6S134V1
public import CFSG.Quasithin.H13.A5Setting
public import CFSG.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers' {t x : G} (htt : t * t = 1) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  have hm : m = 2 * (m / 2) + m % 2 := (Int.mul_ediv_add_emod m 2).symm
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [hm, h, add_zero, zpow_mul, h2, one_zpow]
  · right
    rw [hm, h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem sq_eq_one_of_card_two {W : Subgroup G} (hW : Nat.card W = 2) {w : G} (hw : w ∈ W) :
    w ^ 2 = 1 := by
  have := pow_card_eq_one' (G := ↥W) (x := ⟨w, hw⟩)
  rw [hW] at this
  simpa using congrArg Subtype.val this

theorem le_fsuV1_of_card_two {T V W : Subgroup G} (hVT : V ≤ T) (hWV : W ≤ V)
    (hTW : T ≤ normalizer (W : Set G)) (hW : Nat.card W = 2) : W ≤ fsuV1 T V := by
  rw [normalizer_eq_centralizer_of_card_eq_two hW] at hTW
  intro w hw
  refine mem_inf.2 ⟨hWV hw, mem_quasithinOmegaOneCenter_iff.2 ⟨hVT (hWV hw), ?_, ?_⟩⟩
  · rw [mem_centralizer_iff]
    intro t ht
    exact ((mem_centralizer_iff.1 (hTW ht)) w hw).symm
  · exact sq_eq_one_of_card_two hW hw

theorem part1_of_card_two [Finite G] {T L V : Subgroup G} (hVT : V ≤ T)
    (hZV : V ⊓ centralizer (L : Set G) = ⊥) (hc : Nat.card (fsuV1 T V) = 2) :
    V ⊓ centralizer (L : Set G) ≤ fsuV1 T V ∧
      Nat.card ↥(fsuV1 T V) = 2 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
      ∀ W : Subgroup G, V ⊓ centralizer (L : Set G) ≤ W → W ≤ V →
        T ≤ normalizer (W : Set G) →
        Nat.card W = 2 * Nat.card ↥(V ⊓ centralizer (L : Set G)) → W = fsuV1 T V := by
  rw [hZV, card_bot, mul_one]
  refine ⟨bot_le, hc, fun W _ hWV hTW hW => ?_⟩
  exact Subgroup.eq_of_le_of_card_ge (le_fsuV1_of_card_two hVT hWV hTW hW) (by rw [hc, hW])

theorem card_fsuV1_of_a5Frame [Finite G] {T L V : Subgroup G} (F : A5.Frame T L V)
    (hVT : V ≤ T) : Nat.card (fsuV1 T V) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ (g : ↥(normalizer (V : Set G))) (v : ↥V),
      (g : G) * v * (g : G)⁻¹ = v ↔ A5Model.pact (F.ρ g) (F.ψ v) = F.ψ v := by
    intro g v
    have h1 : F.ψ ⟨(g : G) * v * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 v).mp v.2⟩ =
        A5Model.pact (F.ρ g) (F.ψ v) := by
      rw [← F.equiv]
      congr 1
    rw [← h1]
    constructor
    · intro h
      congr 1
      exact Subtype.ext h
    · intro h
      have := congrArg Subtype.val (F.ψ.injective h)
      simpa using this
  set z : G := (F.ψ.symm A5Model.W4 : G) with hz
  have hzV : z ∈ V := (F.ψ.symm A5Model.W4).2
  have hψz : F.ψ ⟨z, hzV⟩ = A5Model.W4 := by
    have : (⟨z, hzV⟩ : ↥V) = F.ψ.symm A5Model.W4 := Subtype.ext rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : F.ψ ⟨z, hzV⟩ = 1 := by
      have : (⟨z, hzV⟩ : ↥V) = 1 := Subtype.ext h
      rw [this, map_one]
    rw [hψz] at h1
    exact A5Model.W4_ne_one h1
  have hz2 : z ^ 2 = 1 := by
    have h1 : (⟨z, hzV⟩ : ↥V) ^ 2 = 1 := by
      apply F.ψ.injective
      rw [map_pow, hψz, map_one, pow_two]
      show Multiplicative.ofAdd
        (Multiplicative.toAdd A5Model.W4 + Multiplicative.toAdd A5Model.W4) = 1
      rw [A5Model.Ev_add_self]
      rfl
    exact congrArg Subtype.val h1
  have hmem : ∀ x : G, x ∈ fsuV1 T V ↔ x = 1 ∨ x = z := by
    intro x
    constructor
    · rintro ⟨hxV, hxZ⟩
      obtain ⟨-, hxC, -⟩ := mem_quasithinOmegaOneCenter_iff.1 hxZ
      have hfix : ∀ σ : Equiv.Perm (Fin 5), A5.InK4 σ →
          A5Model.pact σ (F.ψ ⟨x, hxV⟩) = F.ψ ⟨x, hxV⟩ := by
        intro σ hσ
        obtain ⟨g, hgT, rfl⟩ := F.K4_T σ hσ
        refine (hconj g ⟨x, hxV⟩).1 ?_
        rw [(mem_centralizer_iff.1 hxC) (g : G) hgT, mul_inv_cancel_right]
      rcases A5.fixed_K4 _ hfix with h | h
      · left
        have : (⟨x, hxV⟩ : ↥V) = 1 := F.ψ.injective (by rw [h, map_one])
        exact congrArg Subtype.val this
      · right
        have : (⟨x, hxV⟩ : ↥V) = ⟨z, hzV⟩ := F.ψ.injective (by rw [h, hψz])
        exact congrArg Subtype.val this
    · rintro (rfl | rfl)
      · exact one_mem _
      · refine mem_inf.2 ⟨hzV, mem_quasithinOmegaOneCenter_iff.2 ⟨hVT hzV, ?_, hz2⟩⟩
        rw [mem_centralizer_iff]
        intro t ht
        have h1 := (hconj ⟨t, F.T_le ht⟩ ⟨z, hzV⟩).2 (by
          rw [hψz]
          exact A5Model.pact_W4 (F.T_D ⟨t, F.T_le ht⟩ ht).1)
        calc t * z = t * z * t⁻¹ * t := by group
          _ = z * t := by rw [h1]
  have heq : fsuV1 T V = zpowers z := by
    apply le_antisymm
    · intro x hx
      rcases (hmem x).1 hx with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · rw [zpowers_le]
      exact (hmem z).2 (Or.inr rfl)
  rw [heq, Nat.card_zpowers]
  exact orderOf_eq_prime hz2 hz1

theorem card_fsuV1_of_L32 [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hLV : L ≤ normalizer (V : Set G))
    (hTV : T ≤ normalizer (V : Set G)) (hVT : V ≤ T) (hV1 : V ≠ ⊥)
    (hnat : BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1) : Nat.card (fsuV1 T V) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, hsq⟩ := card_and_sq_of_binaryNaturalSL hnat
  have hsq' : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    simpa using congrArg Subtype.val (hsq ⟨v, hv⟩)
  have hle := card_autOn_le hsq' hcard hT (T := T)
  have hL : 2 ^ Flag.tri 3 ∣ Nat.card (autOn L V) := by
    rw [card_eq_of_binaryNaturalSL hnat (by norm_num)]
    decide
  have hLT : 2 ^ Flag.tri 3 ∣ Nat.card (autOn (L ⊔ T) V) :=
    hL.trans (Subgroup.card_dvd_of_le (autOn_mono le_sup_left))
  have hodd : ¬ 2 ∣ (autOn T V).relIndex (autOn (L ⊔ T) V) := by
    intro h2
    apply hTi
    have hAB : T.subgroupOf (normalizer (V : Set G)) ≤
        (L ⊔ T).subgroupOf (normalizer (V : Set G)) := fun x hx =>
      mem_subgroupOf.2 ((le_sup_right : T ≤ L ⊔ T) (mem_subgroupOf.1 hx))
    have e1 := relIndex_map_dvd (conjAct V) hAB
    rw [Subgroup.relIndex_subgroupOf (sup_le hLV hTV)] at e1
    exact h2.trans (e1.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))
  have hmul := Subgroup.relIndex_mul_card (autOn T V) (autOn (L ⊔ T) V)
  rw [inf_eq_left.2 (autOn_mono le_sup_right)] at hmul
  have hcop : Nat.Coprime (2 ^ Flag.tri 3) ((autOn T V).relIndex (autOn (L ⊔ T) V)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have hdvd : 2 ^ Flag.tri 3 ∣ Nat.card (autOn T V) := by
    rw [← hmul] at hLT
    exact hcop.dvd_of_dvd_mul_left hLT
  have hS : Nat.card (autOn T V) = 2 ^ Flag.tri 3 :=
    le_antisymm hle (Nat.le_of_dvd Nat.card_pos hdvd)
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hN : (V.subgroupOf T).Normal := by
    constructor
    intro n hn t
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.1 (hTV t.2) n).1 hn
  have hVne : V.subgroupOf T ≠ ⊥ := by
    intro h
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hVT hv⟩ : ↥T) ∈ V.subgroupOf T := mem_subgroupOf.2 hv
    rw [h, mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨⟨⟨a, haT⟩, hamem⟩, ha1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hVne)
  obtain ⟨haV, haZ⟩ := mem_inf.1 hamem
  have haV' : a ∈ V := mem_subgroupOf.1 haV
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext (Subtype.ext h))
  have haC : a ∈ centralizer (T : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    have := mem_center_iff.1 haZ ⟨t, ht⟩
    exact congrArg Subtype.val this
  have hTz : ∀ x : G, x ∈ centralizer (T : Set G) →
      T ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
    intro x hx
    have h1 : zpowers x ≤ centralizer (T : Set G) := zpowers_le.2 hx
    rw [le_centralizer_iff] at h1
    exact h1.trans (Subgroup.centralizer_le_normalizer _)
  have hall : ∀ b ∈ fsuV1 T V, b = 1 ∨ b = a := by
    intro b hb
    obtain ⟨hbV, hbZ⟩ := mem_inf.1 hb
    obtain ⟨-, hbC, hb2⟩ := mem_quasithinOmegaOneCenter_iff.1 hbZ
    have hb2' : b * b = 1 := by rw [← pow_two]; exact hb2
    have ha2' : a * a = 1 := by rw [← pow_two]; exact hsq' a haV'
    rcases tinv_comparable hsq' hcard hT hS (zpowers_le.2 haV') (zpowers_le.2 hbV) (hTz a haC)
        (hTz b hbC) with h | h
    · rcases eq_one_or_eq_of_mem_zpowers' hb2' (h (mem_zpowers a)) with h1 | h1
      · exact absurd h1 ha1'
      · exact Or.inr h1.symm
    · exact eq_one_or_eq_of_mem_zpowers' ha2' (h (mem_zpowers b))
  have heq : fsuV1 T V = zpowers a := by
    apply le_antisymm
    · intro b hb
      rcases hall b hb with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · rw [zpowers_le]
      exact mem_inf.2 ⟨haV', mem_quasithinOmegaOneCenter_iff.2 ⟨haT, haC, hsq' a haV'⟩⟩
  rw [heq, Nat.card_zpowers]
  exact orderOf_eq_prime (hsq' a haV') ha1'

theorem mem_zpowers_conj_iff {t z y : G} (h : t * z * t⁻¹ = z) :
    y ∈ zpowers z ↔ t * y * t⁻¹ ∈ zpowers z := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← conj_zpow, h]
    exact zpow_mem (mem_zpowers z) k
  · intro hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
    have h' : t⁻¹ * z * t⁻¹⁻¹ = z := by
      rw [inv_inv]
      calc t⁻¹ * z * t = t⁻¹ * (t * z * t⁻¹) * t := by rw [h]
        _ = z := by group
    have : y = t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ := by group
    rw [this, ← hk, ← conj_zpow, h']
    exact zpow_mem (mem_zpowers z) k

theorem w1_codes : ∀ x : A6.P6, x ∈ G6.coreMod 6 →
    (G6.permAct 6 (swap 0 1 * swap 2 3) x = x ∨
      G6.permAct 6 (swap 0 1 * swap 2 3) x = x * G6.allOnes 6) →
    (G6.permAct 6 (swap 0 2 * swap 1 3) x = x ∨
      G6.permAct 6 (swap 0 2 * swap 1 3) x = x * G6.allOnes 6) →
    (G6.permAct 6 (swap 0 1 * swap 4 5) x = x ∨
      G6.permAct 6 (swap 0 1 * swap 4 5) x = x * G6.allOnes 6) → A6.InW1 x := by
  decide +kernel

theorem le_fsuV1_of_setting134 [Finite G] {T L V : Subgroup G} (S : A6.Setting134 G T L V)
    {W : Subgroup G} (hZW : V ⊓ centralizer (L : Set G) ≤ W) (hWV : W ≤ V)
    (hTW : T ≤ normalizer (W : Set G)) (hW : Nat.card W = 4) : W ≤ fsuV1 T V := by
  set Z := V ⊓ centralizer (L : Set G) with hZdef
  have hZc : Nat.card Z = 2 := S.card_ZV
  have hidx : (Z.subgroupOf W).index = 2 := by
    have h1 := relIndex_mul_card Z W
    rw [inf_eq_left.2 hZW, hZc, hW] at h1
    have : Z.relIndex W = 2 := by omega
    exact this
  have hmod : ∀ t ∈ T, ∀ w ∈ W, t * w * t⁻¹ * w⁻¹ ∈ Z := by
    intro t ht w hw
    have htw : t * w * t⁻¹ ∈ W := (mem_normalizer_iff.1 (hTW ht) w).1 hw
    have hZt : ∀ y : G, y ∈ Z ↔ t * y * t⁻¹ ∈ Z := by
      intro y
      rw [hZdef, S.ZV_eq_zpowers]
      exact mem_zpowers_conj_iff (S.conj_zV ⟨t, S.frame.T_le ht⟩)
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t * w * t⁻¹, htw⟩)
      (b := ⟨w⁻¹, inv_mem hw⟩))
    have h3 : (⟨t * w * t⁻¹, htw⟩ : ↥W) ∈ Z.subgroupOf W ↔
        (⟨w⁻¹, inv_mem hw⟩ : ↥W) ∈ Z.subgroupOf W := by
      rw [mem_subgroupOf, mem_subgroupOf]
      show t * w * t⁻¹ ∈ Z ↔ w⁻¹ ∈ Z
      rw [← hZt w, inv_mem_iff]
    have h4 := key.2 h3
    rw [mem_subgroupOf] at h4
    exact h4
  intro w hw
  have hwV := hWV hw
  rw [S.mem_V1_iff]
  refine ⟨hwV, ?_⟩
  have hcore : (S.frame.ψ ⟨w, hwV⟩ : A6.P6) ∈ G6.coreMod 6 := (S.frame.ψ ⟨w, hwV⟩).2
  have hσ : ∀ σ : Perm (Fin 6), A6.InD6 σ → σ ∈ alternatingGroup (Fin 6) →
      G6.permAct 6 σ (S.frame.ψ ⟨w, hwV⟩ : A6.P6) = (S.frame.ψ ⟨w, hwV⟩ : A6.P6) ∨
        G6.permAct 6 σ (S.frame.ψ ⟨w, hwV⟩ : A6.P6) =
          (S.frame.ψ ⟨w, hwV⟩ : A6.P6) * G6.allOnes 6 := by
    intro σ hD hA
    obtain ⟨g, hgT, rfl⟩ := S.frame.DA_T σ hD hA
    have hc := hmod g hgT w hw
    rw [hZdef, S.ZV_eq_zpowers] at hc
    have hzz : S.zV * S.zV = 1 := by rw [← pow_two]; exact S.zV_sq
    have hconj := congrArg Subtype.val (S.psi_conj g ⟨w, hwV⟩)
    rw [G6.coreAct_coe] at hconj
    rcases eq_one_or_eq_of_mem_zpowers' hzz hc with h | h
    · left
      have h1 : (g : G) * w * (g : G)⁻¹ = w := by
        calc (g : G) * w * (g : G)⁻¹ = (g : G) * w * (g : G)⁻¹ * w⁻¹ * w := by group
          _ = w := by rw [h, one_mul]
      rw [← hconj]
      congr 2
      exact Subtype.ext h1
    · right
      have h1 : (g : G) * w * (g : G)⁻¹ = S.zV * w := by
        calc (g : G) * w * (g : G)⁻¹ = (g : G) * w * (g : G)⁻¹ * w⁻¹ * w := by group
          _ = S.zV * w := by rw [h]
      have h2 : S.frame.ψ ⟨(g : G) * w * (g : G)⁻¹,
          (mem_normalizer_iff.mp g.2 w).mp hwV⟩ =
          S.frame.ψ ⟨S.zV, S.zV_mem_V⟩ * S.frame.ψ ⟨w, hwV⟩ := by
        rw [← map_mul]
        congr 1
        exact Subtype.ext h1
      rw [← hconj, h2, S.psi_zV]
      show G6.allOnes 6 * (S.frame.ψ ⟨w, hwV⟩ : A6.P6) = _
      rw [mul_comm]
  obtain ⟨⟨d1, a1⟩, ⟨d2, a2⟩, ⟨d3, a3⟩⟩ := A6.gens_DA
  exact w1_codes _ hcore (hσ _ d1 a1) (hσ _ d2 a2) (hσ _ d3 a3)

theorem part1_of_setting134 [Finite G] {T L V : Subgroup G} (S : A6.Setting134 G T L V) :
    V ⊓ centralizer (L : Set G) ≤ fsuV1 T V ∧
      Nat.card ↥(fsuV1 T V) = 2 * Nat.card ↥(V ⊓ centralizer (L : Set G)) ∧
      ∀ W : Subgroup G, V ⊓ centralizer (L : Set G) ≤ W → W ≤ V →
        T ≤ normalizer (W : Set G) →
        Nat.card W = 2 * Nat.card ↥(V ⊓ centralizer (L : Set G)) → W = fsuV1 T V := by
  have hZc := S.card_ZV
  have hTZ : T ≤ normalizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro y
    rw [S.ZV_eq_zpowers]
    exact mem_zpowers_conj_iff (S.conj_zV ⟨t, S.frame.T_le ht⟩)
  rw [hZc]
  refine ⟨le_fsuV1_of_card_two S.V_le_T inf_le_left hTZ hZc, by rw [S.card_V1], ?_⟩
  intro W hZW hWV hTW hW
  exact Subgroup.eq_of_le_of_card_ge (le_fsuV1_of_setting134 S hZW hWV hTW hW)
    (by rw [S.card_V1, hW])

end CFSG.Quasithin.H13.U3
