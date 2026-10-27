module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXH

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.P31X

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits S126 S126P31
  S126P F126 Equiv
open scoped IsMulCommutative

section Aux

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

noncomputable abbrev psiP (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ↥L →* Perm (Fin 8) :=
  (alternatingGroup (Fin 8)).subtype.comp (S126L19a.psi F hH)

theorem E9_le_image (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    E9 ≤ ((Li L F.V1).subgroupOf L).map (psiP F hH) := by
  have hmem : ∀ c : Perm (Fin 8), c ∈ alternatingGroup (Fin 8) → c ^ 3 = 1 →
      (∀ i : Fin 8, (i.val < 4 ↔ (c i).val < 4)) →
      c ∈ ((Li L F.V1).subgroupOf L).map (psiP F hH) := by
    intro c hc hc3 hcb
    obtain ⟨l, hl1, hlV, hl⟩ := S126L1b.exists_mem_L1 F hc hc3 hcb
    exact ⟨⟨l, F126.L1_le_L hl1⟩, hl1,
      (S126L19a.actsAs_psi F hH ⟨l, F126.L1_le_L hl1⟩).unique hl hlV⟩
  rintro _ ⟨i, j, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (hmem aP aP_mem aP_pow_three aP_block) _)
    (Subgroup.pow_mem _ (hmem bP bP_mem bP_pow_three bP_block) _)

theorem exists_subgroup_nine (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    ∃ S₀ : Subgroup ↥L, Nat.card S₀ = 3 ^ 2 ∧ S₀ ≤ (Li L F.V1).subgroupOf L ∧
      ∀ l ∈ S₀, psiP F hH l ∈ E9 := by
  set P : Subgroup ↥L := (Li L F.V1).subgroupOf L ⊓ E9.comap (psiP F hH) with hP
  let φ : ↥P →* ↥E9 := ((psiP F hH).comp P.subtype).codRestrict E9 fun x => x.2.2
  have hφ : Function.Surjective φ := by
    rintro ⟨e, he⟩
    obtain ⟨l, hl, hle⟩ := E9_le_image F hH he
    exact ⟨⟨l, hl, show psiP F hH l ∈ E9 by rw [hle]; exact he⟩, Subtype.ext hle⟩
  have h9 : 3 ^ 2 ∣ Nat.card ↥P := by
    have := Subgroup.card_dvd_of_surjective hφ
    rw [F126.card_E9] at this
    simpa using this
  obtain ⟨K, hK, -, hKP⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three (n := 2)
    (H := ⊥) (L := P) (by simp) h9 bot_le
  exact ⟨K, hK, hKP.trans inf_le_left, fun l hl => (hKP hl).2⟩

end Aux

@[expose] def tauInv : Perm (Fin 8) := swap 0 1 * swap 4 5

theorem tauInv_mem_Q8 : tauInv ∈ S126L1c.Q8 := by
  refine ⟨?_, ?_⟩
  · show tauInv ∈ CFSG.QuasithinUnique.Claim2526.P8
    have h : tauInv = S126L1c.g1 * (S126L1c.bsw * S126L1c.g1 * S126L1c.bsw⁻¹) := by decide
    rw [h]
    exact Subgroup.mul_mem _ S126L1c.g1_mem (Subgroup.mul_mem _
      (Subgroup.mul_mem _ S126L1c.bsw_mem S126L1c.g1_mem) (Subgroup.inv_mem _ S126L1c.bsw_mem))
  · show tauInv ∈ alternatingGroup (Fin 8)
    rw [Perm.mem_alternatingGroup]
    decide

theorem tauInv_conj_E9 : ∀ i j : Fin 3, tauInv * (aP ^ i.val * bP ^ j.val) * tauInv⁻¹ *
    (aP ^ i.val * bP ^ j.val) = 1 := by
  decide +kernel

section Facts

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem mem_normalizer_inf_centralizer {A V : Subgroup G} {l : G}
    (hA : l ∈ Subgroup.normalizer (A : Set G)) (hV : l ∈ Subgroup.normalizer (V : Set G)) :
    l ∈ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  have key : ∀ l : G, l ∈ Subgroup.normalizer (A : Set G) → l ∈ Subgroup.normalizer (V : Set G) →
      ∀ x ∈ A ⊓ Subgroup.centralizer (V : Set G),
        l * x * l⁻¹ ∈ A ⊓ Subgroup.centralizer (V : Set G) := by
    intro l hA hV x hx
    refine ⟨(Subgroup.mem_normalizer_iff.1 hA x).1 hx.1, ?_⟩
    show l * x * l⁻¹ ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : l⁻¹ * v * l ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hV) v).1 hv
      simpa using this
    have hx' := Subgroup.mem_centralizer_iff.1 hx.2 _ hv'
    calc v * (l * x * l⁻¹) = l * ((l⁻¹ * v * l) * x) * l⁻¹ := by group
      _ = l * (x * (l⁻¹ * v * l)) * l⁻¹ := by rw [hx']
      _ = l * x * l⁻¹ * v := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key l hA hV x, fun hx => ?_⟩
  have := key l⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hV) _ hx
  simpa [mul_assoc] using this

theorem mem_pCoreOf_L1 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) {g : G}
    (hg1 : g ∈ Li L F.V1) (hgC : g ∈ Subgroup.centralizer (V : Set G)) :
    g ∈ pCoreOf 2 (Li L F.V1) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  set C : Subgroup G := Li L F.V1 ⊓ Subgroup.centralizer (V : Set G) with hC
  have hp : IsPGroup 2 C := by
    obtain ⟨a, ha⟩ := S126L19a.card_inf_eq_pow h1222 hH (F126.L1_le_L : Li L F.V1 ≤ L)
    exact IsPGroup.of_card ha
  have hnorm : Li L F.V1 ≤ Subgroup.normalizer (C : Set G) := by
    intro l hl
    have hlL : l ∈ L := F126.L1_le_L hl
    have hlX : l ∈ L ⊓ Subgroup.normalizer (F.V1 : Set G) :=
      oTwoRes_le (L ⊓ Subgroup.normalizer (F.V1 : Set G)) hl
    exact mem_normalizer_inf_centralizer (le_normalizer_oTwoRes _ hlX) (hLV hlL)
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm hp ⟨hg1, hgC⟩

theorem star_L1_eq_closure (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {H : Subgroup G} (hL1H : Li L F.V1 ≤ H) :
    star H (Li L F.V1) = Subgroup.closure {x | x ∈ star H (Li L F.V1) ∧ x ^ 3 = 1} := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 fun x hx => hx.1)
  set Λ := Subgroup.closure {x : HStar H | x ∈ star H (Li L F.V1) ∧ x ^ 3 = 1} with hΛ
  have key : ∀ g : G, g ∈ Li L F.V1 → ∀ hgH : g ∈ H,
      (QuotientGroup.mk ⟨g, hgH⟩ : HStar H) ∈ Λ := by
    intro g hg
    refine Subgroup.closure_induction
      (p := fun g _ => ∀ hgH : g ∈ H, (QuotientGroup.mk ⟨g, hgH⟩ : HStar H) ∈ Λ) ?_ ?_ ?_ ?_ hg
    · intro x hx hxH
      obtain ⟨⟨hxL, hx1⟩, m, hm, hxm⟩ := hx
      have h3 := S126L19b.pow_three_of_mem h1222 F hH hxL hx1 hm hxm
      refine Subgroup.subset_closure ⟨mk_mem_star (h := ⟨x, hxH⟩)
        (Subgroup.subset_closure ⟨⟨hxL, hx1⟩, m, hm, hxm⟩), ?_⟩
      rw [← QuotientGroup.mk_pow]
      have : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using h3)
      rw [this, QuotientGroup.mk_one]
    · intro hgH
      have : (⟨1, hgH⟩ : ↥H) = 1 := rfl
      rw [this, QuotientGroup.mk_one]
      exact Λ.one_mem
    · intro x y hx hy ihx ihy hxyH
      have hxH : x ∈ H := hL1H hx
      have hyH : y ∈ H := hL1H hy
      have : (⟨x * y, hxyH⟩ : ↥H) = ⟨x, hxH⟩ * ⟨y, hyH⟩ := rfl
      rw [this, QuotientGroup.mk_mul]
      exact Λ.mul_mem (ihx hxH) (ihy hyH)
    · intro x hx ihx hxH'
      have hxH : x ∈ H := hL1H hx
      have : (⟨x⁻¹, hxH'⟩ : ↥H) = (⟨x, hxH⟩ : ↥H)⁻¹ := rfl
      rw [this, QuotientGroup.mk_inv]
      exact Λ.inv_mem (ihx hxH)
  rintro _ ⟨h, hh, rfl⟩
  exact key h.1 (Subgroup.mem_subgroupOf.1 hh) h.2

theorem exists_inverting_pair (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    {H : Subgroup G} (hL1H : Li L F.V1 ≤ H) (hTH : T ≤ H)
    (hT1 : T ≤ Subgroup.normalizer (F.V1 : Set G)) :
    ∃ r ∈ star H (T ⊓ L), ∃ S : Subgroup (HStar H), S ≤ star H (Li L F.V1) ∧
      IsElemAbelian 3 S ∧ Nat.card S = 9 ∧
      ∀ s ∈ S, r * s * r⁻¹ * s ∈ pCoreOf 2 (star H (Li L F.V1)) := by
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hH.hyp.irrPlus.2.2.1
  obtain ⟨S₀, hS₀, hS₀L1, hS₀E⟩ := exists_subgroup_nine F hH
  obtain ⟨t, ⟨htT, htL⟩, ht⟩ := S126T2.exists_TL_of_Q8 F hH tauInv tauInv_mem_Q8
  set S₁ : Subgroup G := S₀.map L.subtype with hS₁
  have hS₁card : Nat.card S₁ = 9 := by
    rw [hS₁, Subgroup.card_map_of_injective L.subtype_injective, hS₀]
    norm_num
  have hS₁L1 : S₁ ≤ Li L F.V1 := by
    rintro _ ⟨l, hl, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hS₀L1 hl)
  have hS₁H : S₁ ≤ H := hS₁L1.trans hL1H
  have hpow9 : ∀ x ∈ S₁, x ^ 9 = 1 := by
    intro x hx
    have := pow_card_eq_one' (G := ↥S₁) (x := ⟨x, hx⟩)
    rw [hS₁card] at this
    exact congrArg Subtype.val this
  have hS₁1 : S₁ ⊓ pCoreOf 2 H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have h9 := hpow9 x hx.1
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨x, hx.2⟩
    have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h9) (orderOf_dvd_of_pow_eq_one hk')
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 9 2)),
      Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  have hScard : Nat.card (star H S₁) = 9 := by
    have h := F126.card_star hS₁H
    rw [hS₁1, Subgroup.card_bot, mul_one, hS₁card] at h
    exact h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSelem : IsElemAbelian 3 (star H S₁) := by
    refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      (by rw [hScard]; norm_num), ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    have hy : (h : G) ∈ S₁ := hh
    have hyL1 : (h : G) ∈ Li L F.V1 := hS₁L1 hy
    have h3 := S126L19b.pow_three_of_mem h1222 F hH (F126.L1_le_L hyL1)
      (F126.L1_le_normalizer hyL1) (m := 9) (by decide) (hpow9 _ hy)
    rw [← map_pow]
    have : h ^ 3 = 1 := Subtype.ext (by simpa using h3)
    rw [this, map_one]
  refine ⟨QuotientGroup.mk ⟨t, hTH htT⟩, mk_mem_star (h := ⟨t, hTH htT⟩) ⟨htT, htL⟩, star H S₁,
    star_mono hS₁L1, hSelem, hScard, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  have hy : (h : G) ∈ S₁ := hh
  obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.1 hy
  have hly' : (l : G) = (h : G) := hly
  have hyL1 : (h : G) ∈ Li L F.V1 := hS₁L1 hy
  have htN : t ∈ Subgroup.normalizer (Li L F.V1 : Set G) :=
    le_normalizer_oTwoRes (L ⊓ Subgroup.normalizer (F.V1 : Set G)) ⟨htL, hT1 htT⟩
  have hg1 : t * (h : G) * t⁻¹ * (h : G) ∈ Li L F.V1 :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 htN (h : G)).1 hyL1) hyL1
  have hgC : t * (h : G) * t⁻¹ * (h : G) ∈ Subgroup.centralizer (V : Set G) := by
    set tl : ↥L := ⟨t, htL⟩ with htl
    have hψt : psiP F hH tl = tauInv := (S126L19a.actsAs_psi F hH tl).unique ht (hLV htL)
    obtain ⟨i, j, hij⟩ := hS₀E l hl
    have h1 : S126L19a.psi F hH (tl * l * tl⁻¹ * l) = 1 := by
      apply Subtype.ext
      show psiP F hH (tl * l * tl⁻¹ * l) = 1
      rw [map_mul, map_mul, map_mul, map_inv, hψt, hij]
      exact tauInv_conj_E9 i j
    have h2 := (S126L19a.psi_eq_one_iff F hH _).1 h1
    have h3 : (((tl * l * tl⁻¹ * l : ↥L)) : G) = t * (h : G) * t⁻¹ * (h : G) := by
      simp [htl, hly']
    rw [← h3]
    exact h2
  have hgH : t * (h : G) * t⁻¹ * (h : G) ∈ H := hL1H hg1
  have hmem : t * (h : G) * t⁻¹ * (h : G) ∈ pCoreOf 2 (Li L F.V1) :=
    mem_pCoreOf_L1 h1222 F hH hg1 hgC
  have hXH : pCoreOf 2 (Li L F.V1) ≤ H := (pCoreOf_le 2 _).trans hL1H
  have hQ : star H (pCoreOf 2 (Li L F.V1)) ≤ pCoreOf 2 (star H (Li L F.V1)) :=
    le_pCoreOf_of_le_normalizer 2 (star_mono (pCoreOf_le 2 _))
      (star_le_normalizer_star hXH hL1H (le_normalizer_pCoreOf 2 _))
      (isPGroup_star (pCoreOf_isPGroup 2 _) hXH)
  have hfin := hQ (mk_mem_star (h := ⟨t * (h : G) * t⁻¹ * (h : G), hgH⟩) hmem)
  have e : (QuotientGroup.mk ⟨t, hTH htT⟩ : HStar H) * QuotientGroup.mk h *
      (QuotientGroup.mk ⟨t, hTH htT⟩)⁻¹ * QuotientGroup.mk h =
      QuotientGroup.mk ⟨t * (h : G) * t⁻¹ * (h : G), hgH⟩ := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    rfl
  exact e ▸ hfin

end Facts

theorem l1StarFacts_holds (h1222 : Stmt12_2_2) : L1StarFacts := by
  intro G _ _ T L V _ F hH hZ H K hIs h918
  have h := h918.toHypF98.toHypF91
  have hL1H : Li L F.V1 ≤ H := le_sup_left.trans h.L₁T_le_H
  exact ⟨star_L1_eq_closure h1222 F hH hL1H,
    exists_inverting_pair h1222 F hH hL1H h.T_le_H h.T_normalizes_V₁⟩

theorem noL2PairF_w31_final
    (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (hNP : NoPermL_w31) : NoL2PairF_w31 :=
  noL2PairF_w31_holds h1222 h1228 (l1StarFacts_holds h1222) hNP

end CFSG.Quasithin.H13.P31X
