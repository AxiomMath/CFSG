module

public import CFSG.RankThree.PartTwo.Sec3.Item321
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open CFSG CFSG.RankThree.PartTwo

variable {G : Type*} [Group G] [Finite G] {X L T : Subgroup G}

omit [Finite G] in
private theorem mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hB h]

omit [Finite G] in
private theorem omegaZOf_eq (Q : Subgroup G) : omegaZOf Q = omegaG Q := by
  unfold omegaZOf
  rw [map_omegaOneCenter, Subgroup.map_top, Subgroup.range_subtype]

omit [Finite G] in
private theorem mem_omegaZOf_iff (Q : Subgroup G) {z : G} :
    z ∈ omegaZOf Q ↔ z ∈ Q ∧ (∀ x ∈ Q, z * x = x * z) ∧ z * z = 1 := by
  rw [omegaZOf_eq, mem_omegaG]

omit [Finite G] in
private theorem normalizer_le_normalizer_omegaZOf (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (omegaZOf Q : Set G) := by
  refine Subgroup.le_normalizer_iff.mpr fun g hg z hz => ?_
  rw [mem_omegaZOf_iff] at hz ⊢
  obtain ⟨hzQ, hzc, hz2⟩ := hz
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzQ, fun x hx => ?_, ?_⟩
  · have hx' : g⁻¹ * x * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
      simpa using this
    have h := hzc _ hx'
    calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [h]
      _ = x * (g * z * g⁻¹) := by group
  · calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]

omit [Finite G] in
private theorem mem_pCore_iff_mem_pCoreOf {N : Subgroup G} (z : N) :
    z ∈ CFSG.pCore 2 N ↔ (z : G) ∈ CFSG.Open.pCoreOf 2 N := by
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    rwa [← Subtype.ext hwz]

omit [Finite G] in
private theorem exists_pow_eq_mul {K : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (K : Set G)) {k : G} (hk : k ∈ K) (m : ℕ) :
    ∃ k' ∈ K, (d * k) ^ m = d ^ m * k' := by
  induction m with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨k', hk', he⟩ := ih
    refine ⟨d⁻¹ * k' * d * k, K.mul_mem ?_ hk, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hd) k').mp hk'
      simpa using this
    · rw [pow_succ, he, pow_succ]
      group

omit [Finite G] in
private theorem exists_pow_mem_of_sup {K T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K ⊔ T) :
    ∃ a : ℕ, x ^ 2 ^ a ∈ K := by
  have hx' : x ∈ ((T ⊔ K : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T K hTK] at hx'
  obtain ⟨t, ht, k, hk, rfl⟩ := hx'
  obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
  have ha' : t ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  obtain ⟨k', hk', he⟩ := exists_pow_eq_mul (hTK ht) hk (2 ^ a)
  refine ⟨a, ?_⟩
  rw [he, ha', one_mul]
  exact hk'

omit [Finite G] in
private def commCore (X L P : Subgroup G) (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) : Subgroup G where
  carrier := {y | y ∈ X ∧ ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ P}
  one_mem' := ⟨X.one_mem, fun l _ => by simpa using P.one_mem⟩
  mul_mem' := by
    rintro y z ⟨hyX, hy⟩ ⟨hzX, hz⟩
    refine ⟨X.mul_mem hyX hzX, fun l hl => ?_⟩
    have h1 : y * z * l * (y * z)⁻¹ * l⁻¹ =
        (y * (z * l * z⁻¹ * l⁻¹) * y⁻¹) * (y * l * y⁻¹ * l⁻¹) := by group
    rw [h1]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXP hyX) _).mp (hz l hl)) (hy l hl)
  inv_mem' := by
    rintro y ⟨hyX, hy⟩
    refine ⟨X.inv_mem hyX, fun l hl => ?_⟩
    have hl' : y⁻¹ * l * y ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hXL (X.inv_mem hyX)) l).mp hl
      simpa using this
    have h1 : y⁻¹ * l * y⁻¹⁻¹ * l⁻¹ = (y * (y⁻¹ * l * y) * y⁻¹ * (y⁻¹ * l * y)⁻¹)⁻¹ := by group
    rw [h1]
    exact P.inv_mem (hy _ hl')

omit [Finite G] in
private theorem conj_mem_commCore {X L P : Subgroup G} {hXL : X ≤ Subgroup.normalizer (L : Set G)}
    {hXP : X ≤ Subgroup.normalizer (P : Set G)} {g y : G} (hg : g ∈ X)
    (hy : y ∈ commCore X L P hXL hXP) : g * y * g⁻¹ ∈ commCore X L P hXL hXP := by
  obtain ⟨hyX, hy⟩ := hy
  refine ⟨X.mul_mem (X.mul_mem hg hyX) (X.inv_mem hg), fun l hl => ?_⟩
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hXL (X.inv_mem hg)) l).mp hl
    simpa using this
  have h1 : g * y * g⁻¹ * l * (g * y * g⁻¹)⁻¹ * l⁻¹ =
      g * (y * (g⁻¹ * l * g) * y⁻¹ * (g⁻¹ * l * g)⁻¹) * g⁻¹ := by group
  rw [h1]
  exact (Subgroup.mem_normalizer_iff.mp (hXP hg) _).mp (hy _ hl')

theorem pCoreOf_inf_eq (hL : L ∈ oTwoComponentsIn X)
    (hLN : X ≤ Subgroup.normalizer (L : Set G)) :
    L ⊓ CFSG.Open.pCoreOf 2 X = CFSG.Open.pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  apply le_antisymm
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun k hk => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact mem_normalizer_inf (Subgroup.le_normalizer hk)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hLX hk))
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLX)
      (hLN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem mem_pCoreOf_of_centralizes_quotient (hL : L ∈ oTwoComponentsIn X)
    (hLN : X ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hLT : L ⊔ T = X) (hZ : Subgroup.center (L ⧸ CFSG.pCore 2 L) = ⊥) {x : G} (hx : x ∈ X)
    (hxc : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    x ∈ CFSG.Open.pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  set P := CFSG.Open.pCoreOf 2 L
  have hXP : X ≤ Subgroup.normalizer (P : Set G) :=
    hLN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  set C := commCore X L P hLN hXP
  have hCL : ∀ y ∈ C, y ∈ L → y ∈ P := by
    intro y hyC hyL
    have hmk : (QuotientGroup.mk ⟨y, hyL⟩ : L ⧸ CFSG.pCore 2 L) ∈
        Subgroup.center (L ⧸ CFSG.pCore 2 L) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        mem_pCore_iff_mem_pCoreOf]
      have hp := hyC.2 (g : G)⁻¹ (L.inv_mem g.2)
      have hyP : y⁻¹ ∈ Subgroup.normalizer (P : Set G) := hXP (hLX (L.inv_mem hyL))
      have := (Subgroup.mem_normalizer_iff.mp hyP _).mp (P.inv_mem hp)
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hmk
    exact hmk
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hT.le.trans hLN
  have hpow : ∀ y : C, ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    rintro ⟨y, hyC⟩
    obtain ⟨a, ha⟩ := exists_pow_mem_of_sup hT.isPGroup hTL
      (show y ∈ L ⊔ T by rw [hLT]; exact hyC.1)
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
      ⟨y ^ 2 ^ a, hCL _ (C.pow_mem hyC _) ha⟩
    refine ⟨a + k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul, this]
  have hC2 : IsPGroup 2 C := hpow
  have hCN : X ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun g hg y hy => conj_mem_commCore hg hy
  have hCQ : C ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun y hy => hy.1) hCN hC2
  exact hCQ ⟨hx, hxc⟩

theorem mem_pCoreOf_of_centralizes_omegaZOf (hL : L ∈ oTwoComponentsIn X)
    (hLN : X ≤ Subgroup.normalizer (L : Set G)) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hLT : L ⊔ T = X) (hS : IsSimpleGroup (L ⧸ CFSG.pCore 2 L))
    (hV : ⁅omegaZOf (CFSG.Open.pCoreOf 2 X), L⁆ ≠ ⊥) {x : G} (hx : x ∈ X)
    (hxV : ∀ v ∈ omegaZOf (CFSG.Open.pCoreOf 2 X), x * v * x⁻¹ = v) :
    x ∈ CFSG.Open.pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := le_of_mem_oTwoComponentsIn hL
  set Q := CFSG.Open.pCoreOf 2 X
  set V := omegaZOf Q
  set P := CFSG.Open.pCoreOf 2 L
  have hZ : Subgroup.center (L ⧸ CFSG.pCore 2 L) = ⊥ := by
    have hperf : Group.IsPerfect L := isPerfect_of_mem_oTwoComponentsIn hL
    have : Group.IsPerfect (L ⧸ CFSG.pCore 2 L) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 L))
        (QuotientGroup.mk'_surjective _)
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center (L ⧸ CFSG.pCore 2 L)) with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.mp h)
        (Group.IsPerfect.not_isMulCommutative (L ⧸ CFSG.pCore 2 L))
  have hXV : X ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X).trans
      (normalizer_le_normalizer_omegaZOf Q)
  set C' : Subgroup G := X ⊓ Subgroup.centralizer (V : Set G)
  have hC'conj : ∀ g ∈ X, ∀ y ∈ C', g * y * g⁻¹ ∈ C' := by
    intro g hg y hy
    refine ⟨X.mul_mem (X.mul_mem hg hy.1) (X.inv_mem hg), fun v hv => ?_⟩
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hXV (X.inv_mem hg)) v).mp hv
      simpa using this
    have h := hy.2 _ hv'
    calc v * (g * y * g⁻¹) = g * ((g⁻¹ * v * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * v * g)) * g⁻¹ := by rw [h]
      _ = g * y * g⁻¹ * v := by group
  have hPQ : P ≤ Q := (pCoreOf_inf_eq hL hLN).symm.le.trans inf_le_right
  have hPC' : ∀ p ∈ P, p ∈ C' := fun p hp =>
    ⟨hLX (CFSG.LieType.BorelTits.pCoreOf_le 2 L hp), fun v hv =>
      (((mem_omegaZOf_iff Q).mp hv).2.1) p (hPQ hp)⟩
  have hDL : ∀ y ∈ C', y ∈ L → y ∈ P := by
    set D : Subgroup G := C' ⊓ L
    have hDN : L ≤ Subgroup.normalizer (D : Set G) :=
      Subgroup.le_normalizer_iff.mpr fun g hg d hd =>
        ⟨hC'conj g (hLX hg) d hd.1, L.mul_mem (L.mul_mem hg hd.2) (L.inv_mem hg)⟩
    have hE : (D.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hDN
    set π := QuotientGroup.mk' (CFSG.pCore 2 L) with hπ
    have hN : ((D.subgroupOf L).map π).Normal := hE.map π (QuotientGroup.mk'_surjective _)
    rcases hS.eq_bot_or_eq_top_of_normal ((D.subgroupOf L).map π) with h | h
    · intro y hyC hyL
      have h1 : (⟨y, hyL⟩ : L) ∈ D.subgroupOf L := ⟨hyC, hyL⟩
      have h2 : π ⟨y, hyL⟩ ∈ (D.subgroupOf L).map π := ⟨_, h1, rfl⟩
      rw [h, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        mem_pCore_iff_mem_pCoreOf] at h2
      exact h2
    · exfalso
      apply hV
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv l hl
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      have h2 : π ⟨l, hl⟩ ∈ (D.subgroupOf L).map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨e, he, hel⟩ := h2
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        mem_pCore_iff_mem_pCoreOf] at hel
      have hlC' : l ∈ C' := by
        have h3 := C'.mul_mem (he.1 : (e : G) ∈ C') (hPC' _ hel)
        simpa using h3
      exact hlC'.2 v hv
  have hxC' : x ∈ C' := ⟨hx, fun v hv => (mul_inv_eq_iff_eq_mul.mp (hxV v hv)).symm⟩
  refine mem_pCoreOf_of_centralizes_quotient hL hLN hT hLT hZ hx fun l hl => hDL _ ?_ ?_
  · have h1 : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [h1]
    exact C'.mul_mem hxC' (hC'conj l (hLX hl) x⁻¹ (C'.inv_mem hxC'))
  · exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLN hx) l).mp hl) (L.inv_mem hl)

theorem le_normalizer_jG_of_le (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X)
    (hJ : jG T 0 ≤ CFSG.Open.pCoreOf 2 X) : X ≤ Subgroup.normalizer (jG T 0 : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : CFSG.Open.pCoreOf 2 X ≤ T := by
    obtain ⟨S, hS⟩ := hT
    rw [← hS]
    have := CFSG.LieType.BorelTits.pCore_normal (G := X) 2
    exact Subgroup.map_mono
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2).le_sylow_of_normal S)
  refine Subgroup.le_normalizer_iff.mpr fun g hg h hh => ?_
  have hle : (jG T 0).map (MulAut.conj g).toMonoidHom ≤ jG T 0 := by
    rw [jG, (Subgroup.gc_map_comap (MulAut.conj g).toMonoidHom).l_sSup]
    refine iSup₂_le fun A hA => le_sSup (map_conj_mem_famG hA g fun a ha => hQT ?_)
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hg) a).mp (hJ (le_jG hA ha))
  exact hle ⟨h, hh, rfl⟩

theorem relIndex_le_of_famG {V A : Subgroup G} (hVT : V ≤ T)
    (hVc : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hA : A ∈ famG T 0) :
    (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
      (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
  obtain ⟨hAT, hAe, hAcard⟩ := hA
  set D := A ⊓ Subgroup.centralizer (V : Set G) with hD
  have hDe : IsElemTwo D := ⟨fun a ha b hb => hAe.1 a ha.1 b hb.1, fun a ha => hAe.2 a ha.1⟩
  have hDV : ∀ d ∈ D, ∀ v ∈ V, d * v = v * d := fun d hd v hv => (hd.2 v hv).symm
  have hsup : IsElemTwo (D ⊔ V) := isElemTwo_sup hDe ⟨hVc, hV2⟩ hDV
  have hsupT : D ⊔ V ≤ T := sup_le (inf_le_left.trans hAT) hVT
  have hs : Nat.card ↥(D ⊔ V) ≤ Nat.card A := by
    have := card_le_two_pow_pRank hsupT hsup
    rwa [hAcard, Nat.sub_zero]
  have hDVinf : D ⊓ V = A ⊓ V := by
    ext z
    simp only [hD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, fun v hv => hVc v hv z h.2⟩, h.2⟩⟩
  have hle : A ⊓ V ≤ V ⊓ Subgroup.centralizer (A : Set G) := by
    intro z hz
    refine ⟨hz.2, fun a ha => hAe.1 a ha z hz.1⟩
  have hprod := card_sup_mul_card_inf_of_commute hDV
  rw [hDVinf] at hprod
  have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (A : Set G)) V
  rw [inf_eq_left.mpr (inf_le_left : V ⊓ Subgroup.centralizer (A : Set G) ≤ V)] at h1
  have h2 := Subgroup.relIndex_mul_card D A
  rw [inf_eq_left.mpr (inf_le_left : D ≤ A)] at h2
  have hi : 0 < Nat.card ↥(A ⊓ V) := Nat.card_pos
  have hd : 0 < Nat.card D := Nat.card_pos
  have hic : Nat.card ↥(A ⊓ V) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G)) :=
    Subgroup.card_le_of_le hle
  refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥(A ⊓ V) * Nat.card D) ?_ (Nat.mul_pos hi hd)
  calc (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V * (Nat.card ↥(A ⊓ V) * Nat.card D)
      = ((V ⊓ Subgroup.centralizer (A : Set G)).relIndex V * Nat.card ↥(A ⊓ V)) * Nat.card D := by
        ring
    _ ≤ ((V ⊓ Subgroup.centralizer (A : Set G)).relIndex V *
          Nat.card ↥(V ⊓ Subgroup.centralizer (A : Set G))) * Nat.card D := by gcongr
    _ = Nat.card V * Nat.card D := by rw [h1]
    _ = Nat.card ↥(D ⊔ V) * Nat.card ↥(A ⊓ V) := by rw [hprod, mul_comm]
    _ ≤ Nat.card A * Nat.card ↥(A ⊓ V) := by gcongr
    _ = D.relIndex A * Nat.card D * Nat.card ↥(A ⊓ V) := by rw [h2]
    _ = D.relIndex A * (Nat.card ↥(A ⊓ V) * Nat.card D) := by ring

theorem relIndex_centralizer_sup_le (V H K : Subgroup G) :
    (V ⊓ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G)).relIndex V ≤
      (V ⊓ Subgroup.centralizer (H : Set G)).relIndex V *
        (V ⊓ Subgroup.centralizer (K : Set G)).relIndex V := by
  have h : Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) =
      Subgroup.centralizer (H : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
    refine le_antisymm (le_inf (Subgroup.centralizer_le ?_) (Subgroup.centralizer_le ?_)) ?_
    · exact SetLike.coe_subset_coe.mpr le_sup_left
    · exact SetLike.coe_subset_coe.mpr le_sup_right
    · intro g hg
      have hsup : H ⊔ K ≤ Subgroup.centralizer {g} :=
        sup_le (fun h hh => Subgroup.mem_centralizer_singleton_iff.mpr (hg.1 h hh))
          (fun h hh => Subgroup.mem_centralizer_singleton_iff.mpr (hg.2 h hh))
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hh)
  rw [h, inf_inf_distrib_left]
  exact Subgroup.relIndex_inf_le

theorem relIndex_centralizer_conj {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (H : Subgroup G) :
    (V ⊓ Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).relIndex V
      = (V ⊓ Subgroup.centralizer (H : Set G)).relIndex V := by
  have hV : V.map (MulAut.conj g).toMonoidHom = V := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have h : V ⊓ Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (V ⊓ Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext y
    constructor
    · rintro ⟨hyV, hyc⟩
      refine ⟨g⁻¹ * y * g, ⟨?_, fun h hh => ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
      · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) y).mp hyV
        simpa using this
      · have := hyc (g * h * g⁻¹) ⟨h, hh, rfl⟩
        calc h * (g⁻¹ * y * g) = g⁻¹ * ((g * h * g⁻¹) * y) * g := by group
          _ = g⁻¹ * (y * (g * h * g⁻¹)) * g := by rw [this]
          _ = g⁻¹ * y * g * h := by group
    · rintro ⟨x, ⟨hxV, hxc⟩, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxV, ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      have := hxc h hh
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * h * g⁻¹ * (g * x * g⁻¹) = g * (h * x) * g⁻¹ := by group
        _ = g * (x * h) * g⁻¹ := by rw [this]
        _ = g * x * g⁻¹ * (g * h * g⁻¹) := by group
  rw [h]
  calc ((V ⊓ Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom).relIndex V
      = ((V ⊓ Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom).relIndex
          (V.map (MulAut.conj g).toMonoidHom) := by rw [hV]
    _ = (V ⊓ Subgroup.centralizer (H : Set G)).relIndex V :=
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective

end CFSG.RankThree.PartTwo.Sec3.Sims321
