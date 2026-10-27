module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BCFalse

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open Equiv Equiv.Perm
open CFSG.QuasithinUnique.Setup.X3E (Vec lin wmap papply toVec toVec_papply toVec_xor
  exists_toVec toVec_injOn toVec_zero wmap_cons papply_lt)
open CFSG.Quasithin.B45Alt7 (gen7 eval7 indBlk closure_gen7)
open scoped Pointwise

namespace BCHat

@[expose] def affT (j sa sb : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: w => papply 4 (indBlk true j b) (affT j sa sb w) ^^^ (if b then sb else sa)

@[expose] def relB7 : List Bool := [true, true, true, true, true, true, true]

@[expose] def relAB7 : List Bool :=
  [false, true, false, true, false, true, false, true, false, true, false, true, false, true]

@[expose] def relABB3 : List Bool := [false, true, true, false, true, true, false, true, true]

theorem eval7_rel_apply : ∀ i : Fin 7,
    ((eval7 relB7 : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = i ∧
      ((eval7 relAB7 : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = i ∧
      ((eval7 relABB3 : alternatingGroup (Fin 7)) : Perm (Fin 7)) i = i := by
  decide +kernel

theorem eval7_rel : eval7 relB7 = 1 ∧ eval7 relAB7 = 1 ∧ eval7 relABB3 = 1 :=
  ⟨Subtype.ext (Equiv.ext fun i => (eval7_rel_apply i).1),
    Subtype.ext (Equiv.ext fun i => (eval7_rel_apply i).2.1),
    Subtype.ext (Equiv.ext fun i => (eval7_rel_apply i).2.2)⟩

theorem cols_lt : ∀ j < 2, ∀ b : Bool, ∀ i < 4, (indBlk true j b).getD i 0 < 2 ^ 4 := by
  decide +kernel

@[expose] def fixOK : Bool :=
  (List.range 2).all fun j => (List.range 16).all fun sa => (List.range 16).all fun sb =>
    !(affT j sa sb relB7 == 0 && affT j sa sb relAB7 == 0 && affT j sa sb relABB3 == 0) ||
      (List.range 16).any fun x => papply 4 (indBlk true j false) x ^^^ x == sa &&
        papply 4 (indBlk true j true) x ^^^ x == sb

theorem fixOK_eq : fixOK = true := by
  decide +kernel

theorem fix_check {j sa sb : ℕ} (hj : j < 2) (ha : sa < 16) (hb : sb < 16)
    (h1 : affT j sa sb relB7 = 0) (h2 : affT j sa sb relAB7 = 0)
    (h3 : affT j sa sb relABB3 = 0) : ∃ x < 16,
      papply 4 (indBlk true j false) x ^^^ x = sa ∧ papply 4 (indBlk true j true) x ^^^ x = sb := by
  have h := fixOK_eq
  rw [fixOK, List.all_eq_true] at h
  have h' := h j (List.mem_range.mpr hj)
  rw [List.all_eq_true] at h'
  have h'' := h' sa (List.mem_range.mpr ha)
  rw [List.all_eq_true] at h''
  have h4 := h'' sb (List.mem_range.mpr hb)
  rw [h1, h2, h3] at h4
  simp only [beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or] at h4
  obtain ⟨x, hx, hxab⟩ := List.any_eq_true.mp h4
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hxab
  exact ⟨x, List.mem_range.mp hx, hxab⟩

theorem e56_mem_coreMod : (Multiplicative.ofAdd (Pi.single (5 : Fin 7) (1 : ZMod 2) +
    Pi.single 6 1) : G6.PermMod 7) ∈ G6.coreMod 7 := by
  rw [G6.mem_coreMod]
  decide

theorem affT_lt {j sa sb : ℕ} (hj : j < 2) (ha : sa < 2 ^ 4) (hb : sb < 2 ^ 4) :
    ∀ w : List Bool, affT j sa sb w < 2 ^ 4
  | [] => by show 0 < 2 ^ 4; norm_num
  | b :: w => by
    show papply 4 (indBlk true j b) (affT j sa sb w) ^^^ (if b then sb else sa) < 2 ^ 4
    have h1 := papply_lt (fun i hi => cols_lt j hj b i hi) (affT j sa sb w)
    have h2 : (if b then sb else sa) < 2 ^ 4 := by
      cases b
      · exact ha
      · exact hb
    exact Nat.xor_lt_two_pow h1 h2

theorem toVec_affT_cons (j sa sb : ℕ) (b : Bool) (w : List Bool) :
    toVec 4 (affT j sa sb (b :: w)) =
      lin 4 (indBlk true j b) (toVec 4 (affT j sa sb w)) + toVec 4 (if b then sb else sa) := by
  show toVec 4 (papply 4 (indBlk true j b) (affT j sa sb w) ^^^ (if b then sb else sa)) = _
  rw [toVec_xor, toVec_papply]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_fixed {Y U : Subgroup G} (e : O2Q Y ≃* alternatingGroup (Fin 7))
    (hYU : Y ≤ Subgroup.normalizer (U : Set G))
    (hO : pCoreOf 2 Y ≤ Subgroup.centralizer (U : Set G)) {j : ℕ} (hj : j < 2) {Ψ : Vec 4 ≃ ↥U}
    (hΨ0 : Ψ 0 = 1)
    (hΨ : ∀ (w : List Bool) (y : ↥Y), e (QuotientGroup.mk y) = eval7 w → ∀ s : Vec 4,
      Ψ (wmap (fun b => lin 4 (indBlk true j b)) w s) = A7ZK.conjAut hYU y (Ψ s))
    (hΨadd : ∀ s t : Vec 4, Ψ (s + t) = Ψ s * Ψ t) (hU2 : ∀ u ∈ U, u * u = 1) {r : G}
    (hrU : ∀ u ∈ U, r * u = u * r) (hrO : ∀ p ∈ pCoreOf 2 Y, p * r = r * p)
    (hrY : ∀ y ∈ Y, y * r * y⁻¹ * r⁻¹ ∈ U) :
    ∃ u ∈ U, ∀ y ∈ Y, y * (r * u) = r * u * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen : ∀ b : Bool, ∃ y : ↥Y, e (QuotientGroup.mk y) = gen7 b := fun b => by
    obtain ⟨q, hq⟩ := e.surjective (gen7 b)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨y, hq⟩
  choose yg hyg using hgen
  obtain ⟨yw, hyw0, hywc⟩ : ∃ yw : List Bool → ↥Y, yw [] = 1 ∧
      ∀ b w, yw (b :: w) = yg b * yw w :=
    ⟨fun w => w.foldr (fun b acc => yg b * acc) 1, rfl, fun _ _ => rfl⟩
  have heyw : ∀ w, e (QuotientGroup.mk (yw w)) = eval7 w := by
    intro w
    induction w with
    | nil => rw [hyw0, QuotientGroup.mk_one, map_one]; rfl
    | cons b w ih =>
      rw [hywc, QuotientGroup.mk_mul, map_mul, ih, hyg]
      rfl
  obtain ⟨c, hc⟩ : ∃ c : ↥Y → ↥U, ∀ y, (c y : G) = (y : G) * r * (y : G)⁻¹ * r⁻¹ :=
    ⟨fun y => ⟨_, hrY y y.2⟩, fun _ => rfl⟩
  have hn : ∀ b : Bool, ∃ m, m < 2 ^ 4 ∧ toVec 4 m = Ψ.symm (c (yg b)) := fun b =>
    exists_toVec _
  choose n hn16 hnv using hn
  have hΨn : ∀ b : Bool, Ψ (toVec 4 (if b then n true else n false)) = c (yg b) := by
    intro b
    cases b
    · show Ψ (toVec 4 (n false)) = c (yg false)
      rw [hnv, Equiv.apply_symm_apply]
    · show Ψ (toVec 4 (n true)) = c (yg true)
      rw [hnv, Equiv.apply_symm_apply]
  have hΨgen : ∀ (b : Bool) (s : Vec 4),
      Ψ (lin 4 (indBlk true j b) s) = A7ZK.conjAut hYU (yg b) (Ψ s) := by
    intro b s
    have h1 := hΨ [b] (yg b) (by rw [hyg]; rfl) s
    rw [wmap_cons] at h1
    exact h1
  have key : ∀ w, Ψ (toVec 4 (affT j (n false) (n true) w)) = c (yw w) := by
    intro w
    induction w with
    | nil =>
      apply Subtype.ext
      rw [hc, hyw0]
      show ((Ψ (toVec 4 0) : ↥U) : G) = _
      rw [toVec_zero, hΨ0]
      simp
    | cons b w ih =>
      rw [toVec_affT_cons, hΨadd, hΨgen, ih, hΨn]
      apply Subtype.ext
      rw [Subgroup.coe_mul, A7ZK.coe_conjAut, hc, hc, hc, hywc, Subgroup.coe_mul]
      group
  have hrel : ∀ w, eval7 w = 1 → affT j (n false) (n true) w = 0 := by
    intro w hw
    have h1 : QuotientGroup.mk (yw w) = (1 : O2Q Y) :=
      e.injective (by rw [heyw, hw, map_one])
    rw [QuotientGroup.eq_one_iff] at h1
    have h2 : ((yw w : ↥Y) : G) ∈ pCoreOf 2 Y := (mem_pCore_iff_mem_pCoreOf Y _).mp h1
    have h3 : c (yw w) = 1 := by
      apply Subtype.ext
      rw [hc, hrO _ h2, Subgroup.coe_one]
      group
    have h4 := key w
    rw [h3, ← hΨ0] at h4
    have h5 := Ψ.injective h4
    rw [← toVec_zero 4] at h5
    exact toVec_injOn (affT_lt hj (hn16 false) (hn16 true) w) (by norm_num) h5
  obtain ⟨hr1, hr2, hr3⟩ := eval7_rel
  obtain ⟨x, -, hxa, hxb⟩ := fix_check hj (by simpa using hn16 false)
    (by simpa using hn16 true) (hrel _ hr1) (hrel _ hr2) (hrel _ hr3)
  obtain ⟨u, hu⟩ : ∃ u : ↥U, u = Ψ (toVec 4 x) := ⟨_, rfl⟩
  have hfix : ∀ b : Bool, (yg b : G) * (r * u) = r * u * yg b := by
    intro b
    have h1 : toVec 4 (papply 4 (indBlk true j b) x ^^^ x) =
        toVec 4 (if b then n true else n false) := by
      cases b
      · rw [hxa]; rfl
      · rw [hxb]; rfl
    rw [toVec_xor, toVec_papply] at h1
    have h2 := congrArg Ψ h1
    rw [hΨadd, hΨgen, hΨn, ← hu] at h2
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.coe_mul, A7ZK.coe_conjAut, hc] at h3
    obtain ⟨d, hd⟩ : ∃ d : G, d = (yg b : G) * r * (yg b : G)⁻¹ * r⁻¹ := ⟨_, rfl⟩
    have hdU : d ∈ U := hd ▸ hrY _ (yg b).2
    have hyr : (yg b : G) * r * (yg b : G)⁻¹ = d * r := by rw [hd]; group
    have hyu : (yg b : G) * u * (yg b : G)⁻¹ = d * u := by
      have h4 : (yg b : G) * u * (yg b : G)⁻¹ = d * (u : G)⁻¹ := by
        rw [hd, ← h3]; group
      rw [h4, inv_eq_of_mul_eq_one_right (hU2 _ u.2)]
    have hdr : d * r = r * d := (hrU d hdU).symm
    have hd2 : d * d = 1 := hU2 d hdU
    calc (yg b : G) * (r * u) =
        ((yg b : G) * r * (yg b : G)⁻¹) * ((yg b : G) * u * (yg b : G)⁻¹) * yg b := by group
      _ = d * r * (d * u) * yg b := by rw [hyr, hyu]
      _ = r * (d * d) * u * yg b := by rw [hdr]; group
      _ = r * u * yg b := by rw [hd2, mul_one]
  refine ⟨u, u.2, fun y hy => ?_⟩
  set C : Subgroup G := Y ⊓ Subgroup.centralizer ({r * (u : G)} : Set G) with hCdef
  have hmemC : ∀ g ∈ Y, g * (r * u) = r * u * g → g ∈ C := fun g hg hgc =>
    ⟨hg, Subgroup.mem_centralizer_iff.mpr fun z hz => by
      rw [Set.mem_singleton_iff.mp hz]
      exact hgc.symm⟩
  have hOC : pCoreOf 2 Y ≤ C := by
    intro p hp
    refine hmemC p (CFSG.LieType.BorelTits.pCoreOf_le 2 Y hp) ?_
    have hpu : p * u = u * p := (Subgroup.mem_centralizer_iff.mp (hO hp) u u.2).symm
    calc p * (r * u) = (p * r) * u := by group
      _ = r * (p * u) := by rw [hrO p hp]; group
      _ = r * u * p := by rw [hpu]; group
  have htop : (⊤ : Subgroup (alternatingGroup (Fin 7))) ≤
      ((C.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map e.toMonoidHom := by
    rw [← closure_gen7, Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact ⟨QuotientGroup.mk (yg b), ⟨yg b, Subgroup.mem_subgroupOf.mpr
      (hmemC _ (yg b).2 (hfix b)), rfl⟩, hyg b⟩
  obtain ⟨q, ⟨y', hy', rfl⟩, hq⟩ := htop (Subgroup.mem_top (e (QuotientGroup.mk ⟨y, hy⟩)))
  have h1 : (QuotientGroup.mk y' : O2Q Y) = QuotientGroup.mk ⟨y, hy⟩ := e.injective hq
  rw [QuotientGroup.eq] at h1
  have h2 : ((y'⁻¹ * ⟨y, hy⟩ : ↥Y) : G) ∈ C := hOC ((mem_pCore_iff_mem_pCoreOf Y _).mp h1)
  have h3 : (y' : G) ∈ C := Subgroup.mem_subgroupOf.mp hy'
  have h4 : y ∈ C := by
    have e1 : y = (y' : G) * ((y'⁻¹ * ⟨y, hy⟩ : ↥Y) : G) := by simp
    rw [e1]
    exact C.mul_mem h3 h2
  have h5 := Subgroup.mem_centralizer_iff.mp h4.2 (r * u) (Set.mem_singleton _)
  exact h5.symm

theorem inf_centralizer_eq_bot {T K : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) :
    T ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hN : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_of_conj_mem fun x hx =>
      ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer K (hTK ht))
          x).mp hx.2⟩
  have h1 := inf_centralizer_ne_bot_of_two hT2 (hT2.to_le inf_le_left) hN hne
  have hX2 : IsPGroup 2 ↥((T ⊓ Subgroup.centralizer (K : Set G)) ⊓
      Subgroup.centralizer (T : Set G)) := hT2.to_le (inf_le_left.trans inf_le_left)
  have hcard : 2 ∣ Nat.card ↥((T ⊓ Subgroup.centralizer (K : Set G)) ⊓
      Subgroup.centralizer (T : Set G)) := by
    rcases hX2.card_eq_or_dvd with h1' | h2'
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1') h1
    · exact h2'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyZ : (y : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) :=
    ⟨mem_quasithinOmegaOneCenter_iff.mpr
      ⟨y.2.1.1, y.2.2, by rw [← hy']; exact pow_orderOf_eq_one _⟩, y.2.1.2⟩
  rw [hZK, Subgroup.mem_bot] at hyZ
  rw [hyZ, orderOf_one] at hy'
  exact absurd hy' (by norm_num)

omit [Finite G] in
theorem eq_of_not_le_pCoreOf {H K N : Subgroup G} (hK : oTwoUpper H = K)
    (hs : IsSimpleGroup (O2Q K)) (hNK : N ≤ K) (hN : K ≤ Subgroup.normalizer (N : Set G))
    (hNQ : ¬ N ≤ pCoreOf 2 K) : N = K := by
  refine le_antisymm hNK ?_
  have hN' : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hN
  have hNb : ((N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).Normal :=
    hN'.map _ (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal ((N.subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hb | ht
  · exfalso
    apply hNQ
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    intro x hx
    have hxN : (⟨x, hNK hx⟩ : ↥K) ∈ N.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    exact (mem_pCore_iff_mem_pCoreOf K _).mp (hb hxN)
  ·
    have h2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
      intro x hx
      have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) ⟨x, hx⟩ ∈
          (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
        rw [ht]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, hcx⟩ := hmem
      have ho' : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (c⁻¹ * ⟨x, hx⟩) = 1 := by
        rw [map_mul, map_inv, hcx, inv_mul_cancel]
      have ho : c⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥K := by
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ho'
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, ho⟩
      have hk' : (c⁻¹ * ⟨x, hx⟩) ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      refine ⟨k, ?_⟩
      have hσc : (QuotientGroup.mk' (N.subgroupOf K)) c = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hc
      have hσx : (QuotientGroup.mk' (N.subgroupOf K)) ⟨x, hx⟩ =
          (QuotientGroup.mk' (N.subgroupOf K)) (c⁻¹ * ⟨x, hx⟩) := by
        rw [map_mul, map_inv, hσc, inv_one, one_mul]
      have hpow : (QuotientGroup.mk' (N.subgroupOf K)) ((⟨x, hx⟩ : ↥K) ^ 2 ^ k) = 1 := by
        rw [map_pow, hσx, ← map_pow, hk', map_one]
      have hmemN' : (⟨x, hx⟩ : ↥K) ^ 2 ^ k ∈ N.subgroupOf K := by
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hpow
      rw [Subgroup.mem_subgroupOf] at hmemN'
      simpa using hmemN'
    rw [← hK]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxK : x ∈ K := hK ▸ Subgroup.subset_closure hx
    obtain ⟨k, hk⟩ := h2 x hxK
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx.2)
    exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)

theorem sup_inf_centralizer_le {T Y V : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hsyl : IsSylowTwoOf T (Y ⊔ T))
    (hYTV : Y ⊔ T ≤ Subgroup.normalizer (V : Set G))
    (hCY : Y ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 Y) :
    (Y ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC2 : IsPGroup 2 ↥((Y ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    rintro ⟨x, hxYT, hxC⟩
    have hx : x ∈ ((Y : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY]
      exact hxYT
    obtain ⟨l, hl, t, ht, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := pow_mul_mem_of_mem_normalizer hl (hTY ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hC : (l * t) ^ 2 ^ a ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.pow_mem _ hxC _
    rw [he] at hC
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 Y ⟨l', hCY ⟨hl', hC⟩⟩
    have hk' : l' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨a + k, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, he, hk']
  have hle : (Y ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (Y ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left (Hyp5_0_1.le_normalizer_inf_centralizer hYTV) hC2
  exact hle.trans (F7.isSylowTwoOf_pCoreOf_le hsyl)

omit [Finite G] in
theorem isElemAbelian_of_comm {T L V R : Subgroup G}
    (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hRT : R ≤ T)
    (hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v) (hV2 : ∀ v ∈ V, v * v = 1)
    (hRV : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r)
    (hRL : ∀ r ∈ R, ∀ ℓ ∈ L, r * ℓ * r⁻¹ * ℓ⁻¹ ∈ V) : IsElemAbelian 2 R := by
  have hRcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
    intro r hr s hs
    have hmem : (s * r)⁻¹ * (r * s) ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_inf.mpr
        ⟨T.mul_mem (T.inv_mem (T.mul_mem (hRT hs) (hRT hr))) (T.mul_mem (hRT hr) (hRT hs)), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro ℓ hℓ
      obtain ⟨a, ha⟩ : ∃ a, a = r * ℓ * r⁻¹ * ℓ⁻¹ := ⟨_, rfl⟩
      obtain ⟨b, hb⟩ : ∃ b, b = s * ℓ * s⁻¹ * ℓ⁻¹ := ⟨_, rfl⟩
      have haV : a ∈ V := ha ▸ hRL r hr ℓ hℓ
      have hbV : b ∈ V := hb ▸ hRL s hs ℓ hℓ
      have hra : r * ℓ = a * ℓ * r := by rw [ha]; group
      have hsb : s * ℓ = b * ℓ * s := by rw [hb]; group
      have hrb : r * b = b * r := hRV r hr b hbV
      have hsa : s * a = a * s := hRV s hs a haV
      have hab : a * b = b * a := hVcomm a haV b hbV
      have h1 : r * s * ℓ = b * a * ℓ * (r * s) := by
        calc r * s * ℓ = r * (s * ℓ) := by group
          _ = r * (b * ℓ * s) := by rw [hsb]
          _ = r * b * ℓ * s := by group
          _ = b * r * ℓ * s := by rw [hrb]
          _ = b * (r * ℓ) * s := by group
          _ = b * (a * ℓ * r) * s := by rw [hra]
          _ = b * a * ℓ * (r * s) := by group
      have h2 : s * r * ℓ = a * b * ℓ * (s * r) := by
        calc s * r * ℓ = s * (r * ℓ) := by group
          _ = s * (a * ℓ * r) := by rw [hra]
          _ = s * a * ℓ * r := by group
          _ = a * s * ℓ * r := by rw [hsa]
          _ = a * (s * ℓ) * r := by group
          _ = a * (b * ℓ * s) * r := by rw [hsb]
          _ = a * b * ℓ * (s * r) := by group
      calc ℓ * ((s * r)⁻¹ * (r * s)) = (s * r)⁻¹ * (s * r * ℓ) * (s * r)⁻¹ * (r * s) := by group
        _ = (s * r)⁻¹ * (a * b * ℓ) * (r * s) := by rw [h2]; group
        _ = (s * r)⁻¹ * (b * a * ℓ) * (r * s) := by rw [hab]
        _ = (s * r)⁻¹ * (r * s * ℓ) * (r * s)⁻¹ * (r * s) := by rw [h1]; group
        _ = (s * r)⁻¹ * (r * s) * ℓ := by group
    rw [hCTL, Subgroup.mem_bot] at hmem
    calc r * s = (s * r) * ((s * r)⁻¹ * (r * s)) := by group
      _ = s * r := by rw [hmem, mul_one]
  have hRsq : ∀ r ∈ R, r * r = 1 := by
    intro r hr
    have hmem : r * r ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨T.mul_mem (hRT hr) (hRT hr), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro ℓ hℓ
      obtain ⟨a, ha⟩ : ∃ a, a = r * ℓ * r⁻¹ * ℓ⁻¹ := ⟨_, rfl⟩
      have haV : a ∈ V := ha ▸ hRL r hr ℓ hℓ
      have hra : r * ℓ = a * ℓ * r := by rw [ha]; group
      have hrav : r * a = a * r := hRV r hr a haV
      have ha2 : a * a = 1 := hV2 a haV
      have h1 : r * r * ℓ = ℓ * (r * r) := by
        calc r * r * ℓ = r * (r * ℓ) := by group
          _ = r * (a * ℓ * r) := by rw [hra]
          _ = r * a * ℓ * r := by group
          _ = a * r * ℓ * r := by rw [hrav]
          _ = a * (r * ℓ) * r := by group
          _ = a * (a * ℓ * r) * r := by rw [hra]
          _ = (a * a) * ℓ * (r * r) := by group
          _ = ℓ * (r * r) := by rw [ha2, one_mul]
      exact h1.symm
    rw [hCTL, Subgroup.mem_bot] at hmem
    exact hmem
  exact ⟨⟨⟨fun x y => Subtype.ext (hRcomm x x.2 y y.2)⟩⟩, fun x hx => by
    rw [sq]; exact hRsq x hx⟩

theorem relIndex_le_eight {T K V : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hlie : LieModel (O2Q K) .PSL 2 2 2)
    (hV2 : IsPGroup 2 V) (hV : V ≠ ⊥) (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hQV : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    (hirr : ∀ W : Subgroup G, W ≤ V → K ≤ Subgroup.normalizer (W : Set G) → W ≠ ⊥ → V ≤ W) :
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T ≤ 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerT : ∀ t ∈ T, (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 K) →
      t ∈ Subgroup.centralizer (V : Set G) := by
    intro t ht htk
    have hcommt : ∀ x : G, x ∈ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) ↔
        t * x = x * t := by
      intro x
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · intro hx
        exact hx t (Subgroup.mem_zpowers t)
      · intro hx y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact (Commute.zpow_left hx k).eq
    have hzT : Subgroup.zpowers t ≤ T := Subgroup.zpowers_le.mpr ht
    have hW1 := inf_centralizer_ne_bot_of_two (hT2.to_le hzT) hV2 (hzT.trans hTV) hV
    have hKW : K ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer
        ((Subgroup.zpowers t : Subgroup G) : Set G) : Subgroup G) : Set G) := by
      intro l hl
      refine mem_normalizer_of_conj_mem fun w hw =>
        Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hKV hl) w).mp hw.1, ?_⟩
      rw [hcommt]
      have hw' := (hcommt w).mp hw.2
      have htw : t * w * t⁻¹ = w := by rw [hw', mul_inv_cancel_right]
      have hlw : l * w * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hKV hl) w).mp hw.1
      have hq' := Subgroup.mem_centralizer_iff.mp (hQV (htk l hl)) _ hlw
      calc t * (l * w * l⁻¹) = (t * l * t⁻¹ * l⁻¹) * (l * (t * w * t⁻¹) * l⁻¹) *
          (t * l * t⁻¹ * l⁻¹)⁻¹ * t := by group
        _ = (t * l * t⁻¹ * l⁻¹) * (l * w * l⁻¹) * (t * l * t⁻¹ * l⁻¹)⁻¹ * t := by rw [htw]
        _ = (l * w * l⁻¹) * (t * l * t⁻¹ * l⁻¹) * (t * l * t⁻¹ * l⁻¹)⁻¹ * t := by rw [← hq']
        _ = l * w * l⁻¹ * t := by group
    have hVW := hirr _ inf_le_left hKW hW1
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((hcommt v).mp (hVW hv).2).symm
  set ρ : ↥T →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (conjQuotPCore K).comp (Subgroup.inclusion hTK) with hρ
  have hkerρ : ρ.ker ≤ (T ⊓ Subgroup.centralizer (V : Set G)).subgroupOf T := by
    intro t ht
    rw [MonoidHom.mem_ker] at ht
    rw [Subgroup.mem_subgroupOf]
    refine ⟨t.2, hkerT t t.2 fun k hk => ?_⟩
    have h1 := congrArg (fun φ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) =>
      φ (QuotientGroup.mk (⟨k⁻¹, K.inv_mem hk⟩ : ↥K))) ht
    simp only [hρ, MonoidHom.comp_apply, MulAut.one_apply] at h1
    rw [conjQuotPCore_mk, QuotientGroup.eq] at h1
    have h2 := (mem_pCore_iff_mem_pCoreOf K _).mp h1
    convert h2 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    group
  have h120 : Nat.card (MulAut (↥K ⧸ CFSG.pCore 2 ↥K)) = 120 := by
    obtain ⟨e0⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 2) 2 2
      (by norm_num) (GaloisField.card 2 2 (by norm_num)) hlie
    have := CFSG.Walter.JT.isSimpleGroup_of_psl24 e0
    have h60 := CFSG.Walter.JT.card_of_psl24 e0
    obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60
    rw [Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_congr (Equiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
        (by norm_num))), Nat.card_perm, Nat.card_fin]
    rfl
  have h1 : ((T ⊓ Subgroup.centralizer (V : Set G)).subgroupOf T).index ≤ ρ.ker.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hkerρ)
  rw [Subgroup.index_ker] at h1
  have hp : IsPGroup 2 ρ.range := hT2.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : Nat.card ρ.range ∣ 120 := h120 ▸ Subgroup.card_subgroup_dvd_card ρ.range
  rw [hk] at hdvd
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have h3 := dvd_trans h16 hdvd
    norm_num at h3
  have h2 : Nat.card ρ.range ≤ 8 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  exact h1.trans h2

theorem card_le_of_block {H T K Kh W : Subgroup G} {e : O2Q Kh ≃* alternatingGroup (Fin 7)}
    (hT2 : IsPGroup 2 T) (hK : oTwoUpper H = K) (hlie : LieModel (O2Q K) .PSL 2 2 2)
    (pk : A7Pack T K Kh W e) (hCTK : T ⊓ Subgroup.centralizer (K : Set G) = ⊥)
    (hKb : C126Third H T) : Nat.card T ≤ 2 ^ 7 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup G, ⁅W, Kh⁆ = U := ⟨_, rfl⟩
  have hKhU : Kh ≤ Subgroup.normalizer (U : Set G) := hUdef ▸ pk.le_normalizer
  have hTU : T ≤ Subgroup.normalizer (U : Set G) := hUdef ▸ pk.T_le_normalizer
  have hUe : IsElemAbelian 2 U := hUdef ▸ pk.elemAbelian
  have hOU : pCoreOf 2 Kh ≤ Subgroup.centralizer (U : Set G) := hUdef ▸ pk.pCoreOf_le
  have hirrU : ∀ J : Subgroup G, J ≤ U → Kh ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = U := hUdef ▸ pk.irr
  have hntU : ¬ Kh ≤ Subgroup.centralizer (U : Set G) := hUdef ▸ pk.not_le_centralizer
  have hUcard : Nat.card U = 2 ^ 4 ∨ Nat.card U = 2 ^ 6 := hUdef ▸ pk.card
  have hUT : U ≤ T := hUdef ▸ pk.U_le.trans pk.le_T
  have hKKh : K ≤ Kh := pk.K_le
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := pk.T_le_K
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := hKKh.trans hKhU
  have hUcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hUe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hU2 : ∀ u ∈ U, u * u = 1 := fun u hu => by rw [← sq]; exact hUe.2 u hu
  have hU2grp : IsPGroup 2 U := hT2.to_le hUT
  obtain ⟨x, hxK, hx5, hxU⟩ :=
    A7ZK.exists_pow_five_not_mem_centralizer pk.perf pk.simple hKhU hntU hKKh pk.five
  have hs : IsSimpleGroup (O2Q K) := isSimpleGroup_of_lieModel_PSL2 hlie
  have hKQ : ¬ K ≤ pCoreOf 2 K := by
    intro hle
    obtain ⟨q, hq⟩ := exists_ne (1 : O2Q K)
    apply hq
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [QuotientGroup.eq_one_iff]
      exact (mem_pCore_iff_mem_pCoreOf K y).mpr (hle y.2)
  obtain ⟨nb, Kf, -, hKf, hKc, hres, -, -⟩ := hKb
  have hKeq : K = ⨆ i, Kf i := by rw [← hres, F6.twoResidual_eq_oTwoUpper, hK]
  obtain ⟨j, hj⟩ : ∃ j, ¬ Kf j ≤ pCoreOf 2 K := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hKQ (hKeq.le.trans (iSup_le hall))
  have hKjK : Kf j ≤ K := (le_iSup Kf j).trans hKeq.ge
  have hKKj : K ≤ Subgroup.normalizer (Kf j : Set G) := by
    rw [hKeq]
    refine iSup_le fun i => ?_
    by_cases hij : i = j
    · rw [hij]
      exact Subgroup.le_normalizer
    · have hle : Kf i ≤ Subgroup.centralizer (Kf j : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hKc i j hij)
      exact fun y hy => mem_normalizer_of_conj_mem fun z hz => by
        rw [← Subgroup.mem_centralizer_iff.mp (hle hy) z hz, mul_inv_cancel_right]
        exact hz
  have hKjeq : Kf j = K := eq_of_not_le_pCoreOf hK hs hKjK hKKj hj
  obtain ⟨hblk, -⟩ := hKf j
  rw [hKjeq] at hblk
  obtain ⟨⟨hsh, -, -⟩, -⟩ := hblk
  have hsylK : IsSylowTwoOf T (K ⊔ T) := by
    refine ⟨le_sup_right, hT2, fun hd => pk.sylow.2.2 ?_⟩
    have h := Subgroup.relIndex_mul_relIndex T (K ⊔ T) (Kh ⊔ T) le_sup_right
      (sup_le_sup_right hKKh T)
    have h2 : T.relIndex (K ⊔ T) ∣ T.relIndex (Kh ⊔ T) := h ▸ dvd_mul_right _ _
    exact dvd_trans hd h2
  have hQT : pCoreOf 2 K ≤ T := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
        (sup_le (le_normalizer_pCoreOf 2 _) (hTK.trans (normalizer_le_normalizer_pCoreOf 2 _)))
        (pCoreOf_isPGroup 2 _)
    exact h1.trans (F7.isSylowTwoOf_pCoreOf_le hsylK)
  have hZK : blockZ K = ⊥ := by
    rw [eq_bot_iff, ← hCTK]
    exact inf_le_inf_right _ ((C1.blockU_le_blockQ hsh).trans hQT)
  have hirrK := hsh.2.2.2.2.2
  have hZU := hsh.2.2.2.2.1
  rw [hZK] at hirrK hZU
  have hUKQ : ∀ u ∈ U, ∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ blockQ K := by
    intro u hu k hk
    have h1 : u * k * u⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTK (hUT hu)) k).mp hk) (K.inv_mem hk)
    have h2 : u * k * u⁻¹ * k⁻¹ ∈ U := by
      have h3 : k * u⁻¹ * k⁻¹ ∈ U :=
        (Subgroup.mem_normalizer_iff.mp (hKU hk) _).mp (U.inv_mem hu)
      have e1 : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
      rw [e1]
      exact U.mul_mem hu h3
    have hUKn : K ≤ Subgroup.normalizer ((U ⊓ K : Subgroup G) : Set G) := fun l hl =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKU hl, Subgroup.le_normalizer hl⟩
    exact C1.le_pCoreOf_of_normalized inf_le_right hUKn (hU2grp.to_le inf_le_left) ⟨h2, h1⟩
  have hcomm_le : ⁅U, K⁆ ≤ blockU K := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    rw [commutatorElement_def]
    exact C1.commutator_mem_blockU_of_mem_blockQ hsh (hUKQ u hu) k hk
  have hcomm_ne : ⁅U, K⁆ ≠ ⊥ := by
    intro hb
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
    apply hxU
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (hb hu) x hxK).symm
  have hUKeq : ⁅U, K⁆ = blockU K :=
    (hirrK _ bot_le hcomm_le
      (A7ZK.le_normalizer_commutator hKU Subgroup.le_normalizer)).resolve_left hcomm_ne
  have hUKle : blockU K ≤ U := hUKeq ▸ A7ZK.commutator_le_left_of_le_normalizer hKU
  have hU16 : Nat.card U = 2 ^ 4 := by
    rcases hUcard with h | h
    · exact h
    · exfalso
      obtain ⟨β, hβ⟩ := A7ZK.exists_coreMod_equiv e hKhU hUe hOU hirrU hntU h
      have hvc := e56_mem_coreMod
      obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ↥U, β u₀ = ⟨_, hvc⟩ :=
        ⟨β.symm ⟨_, hvc⟩, MulEquiv.apply_symm_apply _ _⟩
      have hfix : ∀ σ : Perm (Fin 7), σ 5 = 5 → σ 6 = 6 →
          G6.permAct 7 σ (Multiplicative.ofAdd (Pi.single (5 : Fin 7) (1 : ZMod 2) +
            Pi.single 6 1)) =
          Multiplicative.ofAdd (Pi.single (5 : Fin 7) (1 : ZMod 2) + Pi.single 6 1) := by
        intro σ h5 h6
        apply Multiplicative.toAdd.injective
        funext i
        rw [G6.permAct_apply]
        have e5 : σ⁻¹ i = 5 ↔ i = 5 := by rw [Equiv.Perm.inv_eq_iff_eq, h5]
        have e6 : σ⁻¹ i = 6 ↔ i = 6 := by rw [Equiv.Perm.inv_eq_iff_eq, h6]
        simp only [toAdd_ofAdd, Pi.add_apply, Pi.single_apply, e5, e6]
      have hu₀K : ∀ k ∈ K, k * (u₀ : G) * k⁻¹ = u₀ := by
        intro k hk
        have hmem : e (QuotientGroup.mk (⟨k, hKKh hk⟩ : ↥Kh)) ∈ A7Std.r0 := by
          rw [← pk.r0]
          exact ⟨QuotientGroup.mk ⟨k, hKKh hk⟩,
            ⟨⟨k, hKKh hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩
        obtain ⟨h5, h6⟩ := (A7Std.mem_r0 _).mp hmem
        have h1 := hβ ⟨k, hKKh hk⟩ u₀
        have h2 : β (A7ZK.conjAut hKhU ⟨k, hKKh hk⟩ u₀) = β u₀ := by
          apply Subtype.ext
          rw [h1, hu₀]
          exact hfix _ h5 h6
        have h3 := congrArg Subtype.val (β.injective h2)
        rw [A7ZK.coe_conjAut] at h3
        exact h3
      have hu₀mem : (u₀ : G) ∈ T ⊓ Subgroup.centralizer (K : Set G) := by
        refine ⟨hUT u₀.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        have h1 := hu₀K k hk
        calc k * (u₀ : G) = k * u₀ * k⁻¹ * k := by group
          _ = u₀ * k := by rw [h1]
      rw [hCTK, Subgroup.mem_bot] at hu₀mem
      have hu₀1 : u₀ = 1 := Subtype.ext hu₀mem
      rw [hu₀1, map_one] at hu₀
      have h1 := congrArg (fun w : ↥(G6.coreMod 7) =>
        Multiplicative.toAdd (w : G6.PermMod 7) 5) hu₀
      simp at h1
  have hUKU : blockU K = U := by
    have hmodU := card_modEq_card_inf_centralizer (hKU hxK) hx5
    have hCx : U ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
      rw [hU16] at hmodU
      have hdvd : Nat.card ↥(U ⊓ Subgroup.centralizer ({x} : Set G)) ∣ 2 ^ 4 := by
        rw [← hU16]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rw [hi'] at hmodU
      interval_cases i
      · exact Subgroup.eq_bot_of_card_eq _ (by rw [hi']; rfl)
      · exact absurd hmodU (by decide)
      · exact absurd hmodU (by decide)
      · exact absurd hmodU (by decide)
      · exfalso
        apply hxU
        have heq : U ⊓ Subgroup.centralizer ({x} : Set G) = U :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hi', hU16])
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have hu' := (heq.ge hu).2
        exact (Subgroup.mem_centralizer_iff.mp hu' x (Set.mem_singleton x)).symm
    have hxUK : x ∈ Subgroup.normalizer (blockU K : Set G) :=
      C1.mem_normalizer_blockU (Subgroup.le_normalizer hxK)
    have hmod := card_modEq_card_inf_centralizer hxUK hx5
    have hbotK : blockU K ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ :=
      eq_bot_iff.mpr ((inf_le_inf_right _ hUKle).trans hCx.le)
    rw [hbotK, Subgroup.card_bot] at hmod
    have hdvd : Nat.card (blockU K) ∣ 2 ^ 4 := hU16 ▸ Subgroup.card_dvd_of_le hUKle
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hi'] at hmod
    interval_cases i
    · exfalso
      have hb : blockU K = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hi']; rfl)
      rw [hb] at hZU
      exact lt_irrefl _ hZU
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)
    · exact Subgroup.eq_of_le_of_card_ge hUKle (by rw [hi', hU16])
  have hQU : pCoreOf 2 K ≤ Subgroup.centralizer (U : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ blockU K := hUKU ▸ hu
    exact (Subgroup.mem_centralizer_iff.mp (hsh.2.2.1.1 hu').2 q hq).symm
  have hirrK' : ∀ J : Subgroup G, J ≤ U → K ≤ Subgroup.normalizer (J : Set G) → J ≠ ⊥ →
      U ≤ J := by
    intro J hJU hKJ hJ
    rw [← hUKU] at hJU ⊢
    exact ((hirrK J bot_le hJU hKJ).resolve_left hJ).ge
  have hUne : U ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hU16
    norm_num at hU16
  have hR8 := relIndex_le_eight hT2 hTK hlie hU2grp hUne hKU hTU hQU hirrK'
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup G, T ⊓ Subgroup.centralizer (U : Set G) = R := ⟨_, rfl⟩
  rw [hRdef] at hR8
  have hRT : R ≤ T := hRdef ▸ inf_le_left
  have hRU : R ≤ Subgroup.centralizer (U : Set G) := hRdef ▸ inf_le_right
  have hCKhU : Kh ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 Kh :=
    A7ZK.inf_centralizer_le_pCoreOf pk.perf pk.simple hKhU hntU
  have hCT := sup_inf_centralizer_le hT2 pk.T_le pk.sylow (sup_le hKhU hTU) hCKhU
  have hRn : ∀ g ∈ Kh, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
    intro g hg r hr
    have h1 : g * r * g⁻¹ ∈ (Kh ⊔ T) ⊓ Subgroup.centralizer (U : Set G) := by
      refine ⟨(Kh ⊔ T).mul_mem ((Kh ⊔ T).mul_mem (Subgroup.mem_sup_left hg)
        (Subgroup.mem_sup_right (hRT hr))) ((Kh ⊔ T).inv_mem (Subgroup.mem_sup_left hg)), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp
        (F7.normalizer_le_normalizer_centralizer U (hKhU hg)) r).mp (hRU hr)
    rw [← hRdef]
    exact ⟨hCT h1, h1.2⟩
  have hRL : ∀ r ∈ R, ∀ k ∈ K, r * k * r⁻¹ * k⁻¹ ∈ U := by
    intro r hr
    have h1 : ∀ k ∈ K, r * k * r⁻¹ * k⁻¹ ∈ blockQ K := by
      intro k hk
      refine C1.inf_centralizer_blockU_le hsh ⟨?_, ?_⟩
      · exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTK (hRT hr)) k).mp hk) (K.inv_mem hk)
      · rw [hUKU]
        have h2 : k * r⁻¹ * k⁻¹ ∈ Subgroup.centralizer (U : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (F7.normalizer_le_normalizer_centralizer U (hKU hk))
            _).mp (Subgroup.inv_mem _ (hRU hr))
        have e1 : r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) := by group
        rw [e1]
        exact Subgroup.mul_mem _ (hRU hr) h2
    intro k hk
    have h3 := C1.commutator_mem_blockU_of_mem_blockQ hsh h1 k hk
    rwa [hUKU] at h3
  have hRV : ∀ r ∈ R, ∀ u ∈ U, r * u = u * r := fun r hr u hu =>
    (Subgroup.mem_centralizer_iff.mp (hRU hr) u hu).symm
  have hRe : IsElemAbelian 2 R := isElemAbelian_of_comm hCTK hRT hUcomm hU2 hRV hRL
  have hRcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := fun r hr s hs =>
    congrArg Subtype.val (hRe.1.is_comm.comm ⟨r, hr⟩ ⟨s, hs⟩)
  have hPR : pCoreOf 2 Kh ≤ R := by
    rw [← hRdef]
    exact le_inf pk.pCoreOf_le_T hOU
  have hRKh : ∀ g ∈ Kh, ∀ r ∈ R, g * r * g⁻¹ * r⁻¹ ∈ U := by
    let N : Subgroup G :=
      { carrier := {g | g ∈ Kh ∧ ∀ r ∈ R, g * r * g⁻¹ * r⁻¹ ∈ U}
        one_mem' := ⟨Kh.one_mem, fun r _ => by simp⟩
        mul_mem' := fun {a b} ha hb => ⟨Kh.mul_mem ha.1 hb.1, fun r hr => by
          have h1 : a * (b * r * b⁻¹ * r⁻¹) * a⁻¹ ∈ U :=
            (Subgroup.mem_normalizer_iff.mp (hKhU ha.1) _).mp (hb.2 r hr)
          have e1 : a * b * r * (a * b)⁻¹ * r⁻¹ =
              (a * (b * r * b⁻¹ * r⁻¹) * a⁻¹) * (a * r * a⁻¹ * r⁻¹) := by group
          rw [e1]
          exact U.mul_mem h1 (ha.2 r hr)⟩
        inv_mem' := fun {a} ha => ⟨Kh.inv_mem ha.1, fun r hr => by
          have h1 : a⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * a⁻¹⁻¹ ∈ U :=
            (Subgroup.mem_normalizer_iff.mp (hKhU (Kh.inv_mem ha.1)) _).mp
              (U.inv_mem (ha.2 r hr))
          have e1 : a⁻¹ * r * a⁻¹⁻¹ * r⁻¹ = a⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * a⁻¹⁻¹ := by group
          rw [e1]
          exact h1⟩ }
    have hmemN : ∀ g : G, g ∈ N ↔ g ∈ Kh ∧ ∀ r ∈ R, g * r * g⁻¹ * r⁻¹ ∈ U := fun _ => Iff.rfl
    have hNKh : N ≤ Kh := fun g hg => ((hmemN g).mp hg).1
    have hKN : K ≤ N := fun k hk => (hmemN k).mpr ⟨hKKh hk, fun r hr => by
      have h1 := U.inv_mem (hRL r hr k hk)
      have e1 : k * r * k⁻¹ * r⁻¹ = (r * k * r⁻¹ * k⁻¹)⁻¹ := by group
      rw [e1]
      exact h1⟩
    have hPN : pCoreOf 2 Kh ≤ N := fun p hp =>
      (hmemN p).mpr ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 Kh hp, fun r hr => by
        rw [hRcomm p (hPR hp) r hr, mul_inv_cancel_right, mul_inv_cancel]
        exact U.one_mem⟩
    have hNn : Kh ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
      mem_normalizer_of_conj_mem fun n hn => (hmemN _).mpr
        ⟨Kh.mul_mem (Kh.mul_mem hg ((hmemN n).mp hn).1) (Kh.inv_mem hg), fun r hr => by
          have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R := hRn g⁻¹ (Kh.inv_mem hg) r hr
          have h1 : g * (n * (g⁻¹ * r * g⁻¹⁻¹) * n⁻¹ * (g⁻¹ * r * g⁻¹⁻¹)⁻¹) * g⁻¹ ∈ U :=
            (Subgroup.mem_normalizer_iff.mp (hKhU hg) _).mp (((hmemN n).mp hn).2 _ hr')
          have e1 : g * n * g⁻¹ * r * (g * n * g⁻¹)⁻¹ * r⁻¹ =
              g * (n * (g⁻¹ * r * g⁻¹⁻¹) * n⁻¹ * (g⁻¹ * r * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
          rw [e1]
          exact h1⟩
    have hN' : (N.subgroupOf Kh).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNKh).mpr hNn
    have hKhN : Kh ≤ N := by
      have hNb : ((N.subgroupOf Kh).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh))).Normal :=
        hN'.map _ (QuotientGroup.mk'_surjective _)
      rcases pk.simple.eq_bot_or_eq_top_of_normal ((N.subgroupOf Kh).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh))) with hb | ht
      · exfalso
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
        apply hxU
        have h1 : (⟨x, hKKh hxK⟩ : ↥Kh) ∈ N.subgroupOf Kh :=
          Subgroup.mem_subgroupOf.mpr (hKN hxK)
        exact hOU ((mem_pCore_iff_mem_pCoreOf Kh _).mp (hb h1))
      · intro g hg
        have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh)) ⟨g, hg⟩ ∈
            (N.subgroupOf Kh).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh)) := by
          rw [ht]
          exact Subgroup.mem_top _
        obtain ⟨c, hc, hcg⟩ := hmem
        have ho' : (QuotientGroup.mk' (CFSG.pCore 2 ↥Kh)) (c⁻¹ * ⟨g, hg⟩) = 1 := by
          rw [map_mul, map_inv, hcg, inv_mul_cancel]
        have ho : c⁻¹ * ⟨g, hg⟩ ∈ CFSG.pCore 2 ↥Kh := by
          rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ho'
        have h3 : ((c⁻¹ * ⟨g, hg⟩ : ↥Kh) : G) ∈ N :=
          hPN ((mem_pCore_iff_mem_pCoreOf Kh _).mp ho)
        have h4 : (c : G) ∈ N := Subgroup.mem_subgroupOf.mp hc
        have e1 : g = (c : G) * ((c⁻¹ * ⟨g, hg⟩ : ↥Kh) : G) := by simp
        rw [e1]
        exact N.mul_mem h4 h3
    exact fun g hg => ((hmemN g).mp (hKhN hg)).2
  obtain ⟨j', hj', Ψ, hΨ0, hΨ, hΨadd⟩ := A7ZK.exists_four_addEquiv e hKhU hUe hOU hirrU hntU hU16
  have hRle : R ≤ U := by
    intro r hr
    obtain ⟨u, hu, hfix⟩ := exists_fixed e hKhU hOU hj' hΨ0 hΨ hΨadd hU2
      (fun u hu => hRV r hr u hu) (fun p hp => hRcomm p (hPR hp) r hr)
      (fun y hy => hRKh y hy r hr)
    have h1 : r * u ∈ T ⊓ Subgroup.centralizer (K : Set G) :=
      ⟨T.mul_mem (hRT hr) (hUT hu), Subgroup.mem_centralizer_iff.mpr fun k hk =>
        hfix k (hKKh hk)⟩
    rw [hCTK, Subgroup.mem_bot] at h1
    rw [eq_inv_of_mul_eq_one_left h1]
    exact U.inv_mem hu
  have hR16 : Nat.card R ≤ 16 :=
    (Subgroup.card_le_of_le hRle).trans (by rw [hU16]; norm_num)
  have hTR := Subgroup.relIndex_mul_card R T
  rw [inf_of_le_left hRT] at hTR
  rw [← hTR]
  calc R.relIndex T * Nat.card R ≤ 8 * 16 := Nat.mul_le_mul hR8 hR16
    _ = 2 ^ 7 := by norm_num

end BCHat

theorem stmt5_1_13_bc_hat_of (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51) : Stmt5_1_13_bc_hat := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 _ hX hnZ hA7 _ hZK hKb
  obtain ⟨e, pk⟩ := m.exists_a7Pack h5171 h51 hc5 hX hnZ hA7
  have hT2 : IsPGroup 2 T := m.hyp.toHyp5_0_1.sylow.1
  exact BCHat.card_le_of_block hT2 rfl hc5.1 pk
    (BCHat.inf_centralizer_eq_bot hT2 pk.T_le_K hZK) hKb

theorem stmt5_1_13_four_block_bc_of_inputs (h5171 : A5.Stmt5_1_7_one) (h51 : AsB51)
    (h510 : Stmt5_1_10) : Stmt5_1_13_four_block_bc :=
  stmt5_1_13_four_block_bc_of_hat h5171 h51 h510 (stmt5_1_13_bc_hat_of h5171 h51)

end CFSG.Quasithin.H13
