module

public import CFSG.Quasithin.Background.F6NoncyclicClass
public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Quasithin.Background.A1cA131
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
public import CFSG.Quasithin.Background.F6NoncyclicCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.SectionRank
open CFSG.RankThreeEvenClassification.Helpers
open scoped commutatorElement

namespace F6

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem perm_three_center : ∀ σ : Equiv.Perm (Fin 3), (∀ τ : Equiv.Perm (Fin 3),
    σ * τ = τ * σ) → σ = 1 := by
  decide +kernel

theorem pCoreOf_eq_bot_of_card_inf (h : IsGoldschmidtTriple G₁ G₂)
    (hT : Nat.card ↥(G₁ ⊓ G₂) = 2) : pCoreOf 2 G₁ = ⊥ := by
  have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 G₁) (K := G₁ ⊓ G₂)
  rw [relIndex_pCoreOf_left h, inf_eq_left.mpr (pCoreOf_le_inf_left h), hT] at h1
  exact Subgroup.eq_bot_of_card_eq _ (by omega)

theorem conj_eq_inv_of_not_mem (h : IsGoldschmidtTriple G₁ G₂)
    (hL : Nat.card ↥(twoResidual G₁) = 3) {t : D} (htT : t ∈ G₁ ⊓ G₂) (htQ : t ∉ pCoreOf 2 G₁)
    (hQc : ∀ q ∈ pCoreOf 2 G₁, ∀ l ∈ twoResidual G₁, q * l = l * q) :
    ∀ l ∈ twoResidual G₁, t * l * t⁻¹ = l⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := twoResidual G₁ with hLdef
  set Q := pCoreOf 2 G₁ with hQdef
  obtain ⟨x, hx⟩ : ∃ x : ↥L, x ≠ 1 := by
    have : Nontrivial ↥L := Finite.one_lt_card_iff_nontrivial.mp (by rw [hL]; norm_num)
    exact exists_ne 1
  have hLx : Subgroup.zpowers x = ⊤ := zpowers_eq_top_of_prime_card hL hx
  have hx3 : (x : D) ^ 3 = 1 := by
    have h1 : x ^ Nat.card ↥L = 1 := pow_card_eq_one'
    rw [hL] at h1
    simpa using congrArg Subtype.val h1
  have htn : t ∈ Subgroup.normalizer (L : Set D) :=
    le_normalizer_twoResidual G₁ (Subgroup.mem_inf.mp htT).1
  have htx : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htn x).mp x.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hLx ▸ Subgroup.mem_top (⟨_, htx⟩ : ↥L))
  have hk' : (x : D) ^ k = t * x * t⁻¹ := by simpa using congrArg Subtype.val hk
  have hk3 : (x : D) ^ k = (x : D) ^ (k % 3) := by
    rw [← zpow_mod_orderOf]
    have hord : orderOf (x : D) = 3 := orderOf_eq_prime hx3 (fun h1 => hx (Subtype.ext h1))
    rw [hord]
    rfl
  have hx1 : (x : D) ≠ 1 := fun h1 => hx (Subtype.ext h1)
  have hcent : t * x * t⁻¹ ≠ x := by
    intro htx'
    have hTx : ∀ u ∈ G₁ ⊓ G₂, u * x = x * u := by
      intro u hu
      by_cases huQ : u ∈ Q
      · exact hQc u huQ x x.2
      ·
        have hidx := relIndex_pCoreOf_left h
        obtain ⟨q, hq, rfl⟩ : ∃ q ∈ Q, t * q = u := by
          have hn : (Q.subgroupOf (G₁ ⊓ G₂)).Normal := Subgroup.normal_of_index_eq_two hidx
          have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t, htT⟩⁻¹)
            (b := ⟨u, hu⟩)).mpr (by
              rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
              exact iff_of_false (fun h' => htQ (by simpa using Q.inv_mem h')) huQ)
          rw [Subgroup.mem_subgroupOf] at this
          exact ⟨t⁻¹ * u, by simpa using this, by group⟩
        calc t * q * x = t * (q * x) := by group
          _ = t * (x * q) := by rw [hQc q hq x x.2]
          _ = (t * x * t⁻¹) * t * q := by group
          _ = x * (t * q) := by rw [htx']; group
    have hG : G₁ ≤ Subgroup.centralizer ({(x : D)} : Set D) := by
      rw [← inf_sup_twoResidual_left h]
      refine sup_le (fun u hu => ?_) (fun l hl => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hTx u hu)
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hLx ▸ Subgroup.mem_top (⟨l, hl⟩ : ↥L))
        have hm' : (x : D) ^ m = l := by simpa using congrArg Subtype.val hm
        rw [← hm']
        exact (Commute.self_zpow (x : D) m).eq.symm
    obtain ⟨e⟩ := h.quotient₁
    set φ : ↥G₁ →* Equiv.Perm (Fin 3) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Open.pCore 2 ↥G₁)) with hφ
    have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hxG : (x : D) ∈ G₁ := twoResidual_le G₁ x.2
    have hφx : φ ⟨x, hxG⟩ = 1 := by
      refine perm_three_center _ fun τ => ?_
      obtain ⟨g, rfl⟩ := hφs τ
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hG g.2)).symm
    have hxQ : (⟨x, hxG⟩ : ↥G₁) ∈ Open.pCore 2 ↥G₁ := by
      rw [← QuotientGroup.eq_one_iff]
      apply e.injective
      rw [map_one]
      exact hφx
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥G₁) 2) ⟨_, hxQ⟩
    have hn' : (x : D) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 := orderOf_dvd_of_pow_eq_one hn'
    have h3 : orderOf (x : D) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hc : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    exact hx1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h3 hc) h1))
  have htxinv : t * x * t⁻¹ = (x : D)⁻¹ := by
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · exfalso
      rw [hk3, h0, zpow_zero] at hk'
      apply hx1
      calc (x : D) = t⁻¹ * (t * x * t⁻¹) * t := by group
        _ = 1 := by rw [← hk']; group
    · exact absurd (by rw [← hk', hk3, h1, zpow_one]) hcent
    · rw [← hk', hk3, h2]
      calc (x : D) ^ (2 : ℤ) = (x : D) ^ (3 : ℤ) * (x : D)⁻¹ := by group
        _ = (x : D)⁻¹ := by rw [show (x : D) ^ (3 : ℤ) = 1 by exact_mod_cast hx3, one_mul]
  intro l hl
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hLx ▸ Subgroup.mem_top (⟨l, hl⟩ : ↥L))
  have hm' : (x : D) ^ m = l := by simpa using congrArg Subtype.val hm
  rw [← hm']
  calc t * (x : D) ^ m * t⁻¹ = (t * x * t⁻¹) ^ m := by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    _ = ((x : D) ^ m)⁻¹ := by rw [htxinv, inv_zpow]

omit [Finite D] in
theorem eq_bot_of_le_commutator {L H : Subgroup D} [hL : Group.IsNilpotent ↥L] (hHL : H ≤ L)
    (h : H ≤ ⁅H, L⁆) : H = ⊥ := by
  have key : ∀ n : ℕ, H ≤ L.lowerCentralSeries n := by
    intro n
    induction n with
    | zero => exact hHL
    | succ n ih => exact h.trans (Subgroup.commutator_mono ih le_rfl)
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries L).mp hL
  exact le_bot_iff.mp (hn ▸ key n)

section Klein

variable (h : IsGoldschmidtTriple G₁ G₂)

include h in
theorem sup_inf_eq_top : twoResidual (⊤ : Subgroup D) ⊔ G₁ ⊓ G₂ = ⊤ := by
  refine top_le_iff.mp ?_
  have h1 : G₁ ≤ twoResidual (⊤ : Subgroup D) ⊔ G₁ ⊓ G₂ := by
    calc G₁ = G₁ ⊓ G₂ ⊔ twoResidual G₁ := (inf_sup_twoResidual_left h).symm
      _ ≤ _ := sup_le le_sup_right ((twoResidual_mono le_top).trans le_sup_left)
  have h2 : G₂ ≤ twoResidual (⊤ : Subgroup D) ⊔ G₁ ⊓ G₂ := by
    calc G₂ = G₁ ⊓ G₂ ⊔ twoResidual G₂ := (inf_sup_twoResidual_right h).symm
      _ ≤ _ := sup_le le_sup_right ((twoResidual_mono le_top).trans le_sup_left)
  calc (⊤ : Subgroup D) = G₁ ⊔ G₂ := h.gen.symm
    _ ≤ _ := sup_le h1 h2

include h in
theorem centralizer_le_of_isPGroup (hL3 : IsPGroup 3 ↥(twoResidual (⊤ : Subgroup D)))
    (hT2 : ∀ s ∈ G₁ ⊓ G₂, s ^ 2 = 1)
    (hTL : ∀ s ∈ G₁ ⊓ G₂, (∀ x ∈ twoResidual (⊤ : Subgroup D), s * x = x * s) → s = 1) :
    Subgroup.centralizer (twoResidual (⊤ : Subgroup D) : Set D) ≤
      twoResidual (⊤ : Subgroup D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := twoResidual (⊤ : Subgroup D) with hLdef
  have hLn : L.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  intro c hc
  have hcD : c ∈ L ⊔ G₁ ⊓ G₂ := by rw [sup_inf_eq_top h]; exact Subgroup.mem_top c
  obtain ⟨ℓ, hℓ, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hcD
  have hcx : ∀ x ∈ L, ℓ * s * x = x * (ℓ * s) := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hc x hx).symm
  have hsx : ∀ x ∈ L, s * x * s⁻¹ = ℓ⁻¹ * x * ℓ := by
    intro x hx
    calc s * x * s⁻¹ = ℓ⁻¹ * (ℓ * s * x) * s⁻¹ := by group
      _ = ℓ⁻¹ * (x * (ℓ * s)) * s⁻¹ := by rw [hcx x hx]
      _ = ℓ⁻¹ * x * ℓ := by group
  have hs2 : s * s = 1 := by rw [← pow_two]; exact hT2 s hs
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hℓ2 : ∀ x ∈ L, ℓ ^ 2 * x = x * ℓ ^ 2 := by
    intro x hx
    have h1 : s * (s * x * s⁻¹) * s⁻¹ = x := by
      calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s * s)⁻¹ := by group
        _ = x := by rw [hs2]; group
    have hℓx : ℓ⁻¹ * x * ℓ ∈ L := by
      have := hLn.conj_mem x hx ℓ⁻¹
      simpa using this
    rw [hsx x hx, hsx _ hℓx] at h1
    calc ℓ ^ 2 * x = ℓ ^ 2 * (ℓ⁻¹ * (ℓ⁻¹ * x * ℓ) * ℓ) := by rw [h1]
      _ = x * ℓ ^ 2 := by rw [pow_two]; group
  have hℓc : ∀ x ∈ L, ℓ * x = x * ℓ := by
    intro x hx
    obtain ⟨k, hk⟩ := hL3 ⟨ℓ, hℓ⟩
    have hk' : ℓ ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime 2 (orderOf ℓ) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk')
        (Nat.Coprime.pow_right k (by norm_num))
    have hmem : ℓ ∈ Subgroup.zpowers (ℓ ^ 2) := by
      have := A4.mem_zpowers_pow_of_coprime (x := ℓ) hcop
      exact this
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hm]
    exact ((Commute.zpow_left (hℓ2 x hx) m)).eq
  have hs1 : s = 1 := by
    refine hTL s hs fun x hx => ?_
    have h1 := hsx x hx
    rw [show ℓ⁻¹ * x * ℓ = x by
      calc ℓ⁻¹ * x * ℓ = ℓ⁻¹ * (x * ℓ) := by group
        _ = ℓ⁻¹ * (ℓ * x) := by rw [hℓc x hx]
        _ = x := by group] at h1
    calc s * x = s * x * s⁻¹ * s := by group
      _ = x * s := by rw [h1]
  rw [hs1, mul_one]
  exact hℓ

end Klein

omit [Finite D] in
theorem centralizer_zpowers_eq (t : D) :
    Subgroup.centralizer (Subgroup.zpowers t : Set D) = Subgroup.centralizer ({t} : Set D) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem isCyclic_map_inf_centralizer {L N : Subgroup D} [N.Normal] (hNL : N ≤ L)
    (hN : ¬ 2 ∣ Nat.card ↥N) {t : D} (ht : t ^ 2 = 1)
    (hcyc : IsCyclic ↥(L ⊓ Subgroup.centralizer ({t} : Set D))) :
    IsCyclic ↥(L.map (QuotientGroup.mk' N) ⊓
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (D ⧸ N))) := by
  set π := QuotientGroup.mk' N with hπ
  have ht2 : IsPGroup 2 ↥(Subgroup.zpowers t) := fun g => ⟨1, by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine Subtype.ext ?_
    rw [pow_one, Subgroup.coe_pow, ← hk, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]⟩
  have hmap := centralizer_map_eq_of_pGroup_prime_complement_kernel 2 Nat.prime_two π
    (QuotientGroup.mk'_surjective N) (by rwa [QuotientGroup.ker_mk']) (Subgroup.zpowers t) ht2
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at hmap
  have hle : L.map π ⊓ Subgroup.centralizer ({π t} : Set (D ⧸ N)) ≤
      (L ⊓ Subgroup.centralizer ({t} : Set D)).map π := by
    rintro _ ⟨⟨ℓ, hℓ, rfl⟩, hyc'⟩
    rw [← hmap] at hyc'
    obtain ⟨y, hyc, hyℓ⟩ := hyc'
    have hyL : y ∈ L := by
      have h1 : ℓ⁻¹ * y ∈ N := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have : (QuotientGroup.mk y : D ⧸ N) = QuotientGroup.mk ℓ := hyℓ
        rw [this, inv_mul_cancel]
      have := L.mul_mem hℓ (hNL h1)
      rwa [mul_inv_cancel_left] at this
    exact ⟨y, ⟨hyL, hyc⟩, hyℓ⟩
  have hc2 : IsCyclic ↥((L ⊓ Subgroup.centralizer ({t} : Set D)).map π) :=
    isCyclic_of_surjective (toMapMk _ N) (toMapMk_surjective _ N)
  exact Subgroup.isCyclic_of_le hle

theorem commutator_commutator_eq_bot {L : Subgroup D} [hLn : L.Normal] {x₁ x₂ a b : D}
    (hL : L = Subgroup.closure {x₁, x₂}) (hL3 : IsPGroup 3 ↥L)
    (hx₁ : x₁ ^ 3 = 1) (hx₂ : x₂ ^ 3 = 1)
    (ha₁ : a * x₁ * a⁻¹ = x₁) (ha₂ : a * x₂ * a⁻¹ = x₂⁻¹)
    (hb₁ : b * x₁ * b⁻¹ = x₁⁻¹) (hb₂ : b * x₂ * b⁻¹ = x₂)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hcyc : ∀ t : D, t ^ 2 = 1 → t ≠ 1 → IsCyclic ↥(L ⊓ Subgroup.centralizer ({t} : Set D))) :
    ⁅⁅L, L⁆, L⁆ = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent ↥L := hL3.isNilpotent
  set V := ⁅⁅L, L⁆, L⁆ with hVdef
  set N := ⁅V, L⁆ with hNdef
  have hγn : (⁅L, L⁆).Normal := Subgroup.commutator_normal L L
  have hVn : V.Normal := Subgroup.commutator_normal _ L
  have hNn : N.Normal := Subgroup.commutator_normal V L
  have hVL : V ≤ L := (Subgroup.commutator_le_left _ L).trans (Subgroup.commutator_le_left L L)
  have hNL : N ≤ L := (Subgroup.commutator_le_left V L).trans hVL
  by_contra hV
  have hVN : ¬ V ≤ N := fun hle => hV (eq_bot_of_le_commutator hVL hle)
  have hNodd : ¬ 2 ∣ Nat.card ↥N := by
    obtain ⟨k, hk⟩ := (hL3.to_le hNL).exists_card_eq
    rw [hk]
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)
    omega
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set L' := L.map π with hL'def
  have hL' : L' = Subgroup.closure {π x₁, π x₂} := by
    rw [hL'def, hL, MonoidHom.map_closure, Set.image_pair]
  have hL'n : L'.Normal := hLn.map π hπs
  have hconj : ∀ {u v w : D}, u * v * u⁻¹ = w → π u * π v * (π u)⁻¹ = π w := by
    intro u v w huv
    rw [← map_inv, ← map_mul, ← map_mul, huv]
  have hV' : ⁅⁅L', L'⁆, L'⁆ = V.map π := by
    rw [hL'def, ← Subgroup.map_commutator, ← Subgroup.map_commutator]
  have hVc : ⁅⁅L', L'⁆, L'⁆ ≤ Subgroup.centralizer (L' : Set (D ⧸ N)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, hV', hL'def, ← Subgroup.map_commutator,
      ← hNdef, QuotientGroup.map_mk'_self]
  have hVbot : ⁅⁅L', L'⁆, L'⁆ ≠ ⊥ := by
    rw [hV']
    intro h0
    apply hVN
    intro v hv
    have : π v = 1 := by
      have : π v ∈ V.map π := ⟨v, hv, rfl⟩
      rwa [h0, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff v).mp this
  exact false_of_class_three hL' (by rw [← map_pow, hx₁, map_one])
    (by rw [← map_pow, hx₂, map_one]) (hconj ha₁) (by rw [hconj ha₂, map_inv])
    (by rw [hconj hb₁, map_inv]) (hconj hb₂) (by rw [← map_pow, ha, map_one])
    (by rw [← map_pow, hb, map_one]) (hL3.map π) hVc hVbot
    (isCyclic_map_inf_centralizer hNL hNodd ha (hcyc a ha ha1))
    (isCyclic_map_inf_centralizer hNL hNodd hb (hcyc b hb hb1))

omit [Finite D] in
theorem nonempty_mulEquiv_prod_of_commute {A B : Subgroup D} (hAB : A ⊔ B = ⊤)
    (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (eA : ↥A ≃* Equiv.Perm (Fin 3))
    (eB : ↥B ≃* Equiv.Perm (Fin 3)) : Nonempty (D ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  have hinf : ∀ z ∈ A, z ∈ B → z = 1 := by
    intro z hzA hzB
    have h1 : eA ⟨z, hzA⟩ = 1 := by
      refine perm_three_center _ fun τ => ?_
      obtain ⟨w, rfl⟩ := eA.surjective τ
      rw [← map_mul, ← map_mul]
      exact congrArg eA (Subtype.ext (hc w w.2 z hzB).symm)
    have := eA.injective (h1.trans (map_one eA).symm)
    exact congrArg Subtype.val this
  have hAn : A.Normal := by
    have : (⊤ : Subgroup D) ≤ Subgroup.normalizer (A : Set D) := by
      rw [← hAB]
      refine sup_le Subgroup.le_normalizer fun y hy => ?_
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact hc x hx y hy
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp this)
  let φ : ↥A × ↥B →* D :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hc x x.2 y y.2
  have hφ : Function.Bijective φ := by
    refine ⟨fun p q hpq => ?_, fun d => ?_⟩
    · have h1 : (p.1 : D) * (q.1 : D)⁻¹ = (q.2 : D) * (p.2 : D)⁻¹ := by
        have e : (p.1 : D) * p.2 = q.1 * q.2 := hpq
        calc (p.1 : D) * (q.1 : D)⁻¹ = (p.1 : D) * p.2 * (p.2 : D)⁻¹ * (q.1 : D)⁻¹ := by group
          _ = q.1 * q.2 * (p.2 : D)⁻¹ * (q.1 : D)⁻¹ := by rw [e]
          _ = q.1 * ((q.2 : D) * (p.2 : D)⁻¹) * (q.1 : D)⁻¹ := by group
          _ = (q.2 : D) * (p.2 : D)⁻¹ * q.1 * (q.1 : D)⁻¹ := by
            rw [hc _ q.1.2 _ (B.mul_mem q.2.2 (B.inv_mem p.2.2))]
          _ = (q.2 : D) * (p.2 : D)⁻¹ := by rw [mul_inv_cancel_right]
      have h2 := hinf _ (A.mul_mem p.1.2 (A.inv_mem q.1.2)) (h1 ▸ B.mul_mem q.2.2 (B.inv_mem p.2.2))
      have h3 : (q.2 : D) * (p.2 : D)⁻¹ = 1 := h1 ▸ h2
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact mul_inv_eq_one.mp h2
      · exact (mul_inv_eq_one.mp h3).symm
    · have hd : d ∈ A ⊔ B := by rw [hAB]; exact Subgroup.mem_top d
      obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hd
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  exact ⟨(MulEquiv.ofBijective φ hφ).symm.trans (MulEquiv.prodCongr eA eB)⟩

theorem nonempty_mulEquiv_perm_of_le (h : IsGoldschmidtTriple G₁ G₂) {A : Subgroup D}
    (hA : A ≤ G₁) (hcard : Nat.card ↥A = 6) {x b : D} (hxA : x ∈ A) (hbA : b ∈ A)
    (hx : orderOf x = 3) (hbT : b ∈ G₁ ⊓ G₂) (hbQ : b ∉ pCoreOf 2 G₁) :
    Nonempty (↥A ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h.quotient₁
  set ψ : ↥A →* Equiv.Perm (Fin 3) :=
    ((e.toMonoidHom.comp (QuotientGroup.mk' (Open.pCore 2 ↥G₁))).comp
      (Subgroup.inclusion hA)) with hψ
  have hmemQ : ∀ g : ↥A, ψ g = 1 → (g : D) ∈ pCoreOf 2 G₁ := by
    intro g hg
    have h1 : (Subgroup.inclusion hA g) ∈ Open.pCore 2 ↥G₁ := by
      rw [← QuotientGroup.eq_one_iff]
      apply e.injective
      rw [map_one]
      exact hg
    exact ⟨_, h1, rfl⟩
  have hx3 : (⟨x, hxA⟩ : ↥A) ^ 3 = 1 := Subtype.ext (by simp [← hx])
  have hψx : orderOf (ψ ⟨x, hxA⟩) = 3 := by
    refine orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) fun h1 => ?_
    have hq := hmemQ _ h1
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁) ⟨x, hq⟩
    have : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 := orderOf_dvd_of_pow_eq_one this
    rw [hx] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega
  have hb2 : b * b ∈ pCoreOf 2 G₁ := by
    have hidx := relIndex_pCoreOf_left h
    have := Subgroup.mul_self_mem_of_index_two hidx ⟨b, hbT⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hψb : orderOf (ψ ⟨b, hbA⟩) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => hbQ (hmemQ _ h1)
    obtain ⟨⟨q, hqG⟩, hq, hqe⟩ := hb2
    rw [pow_two, ← map_mul]
    have h1 : Subgroup.inclusion hA (⟨b, hbA⟩ * ⟨b, hbA⟩) = ⟨q, hqG⟩ :=
      Subtype.ext (by simpa using hqe.symm)
    rw [hψ, MonoidHom.comp_apply, h1]
    show e (QuotientGroup.mk' (Open.pCore 2 ↥G₁) ⟨q, hqG⟩) = 1
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hq, map_one]
  have h6 : 6 ∣ Nat.card ↥ψ.range := by
    have h3 : 3 ∣ Nat.card ↥ψ.range := by
      have h1 := orderOf_dvd_natCard (⟨ψ ⟨x, hxA⟩, ⟨_, rfl⟩⟩ : ↥ψ.range)
      have h2 := Subgroup.orderOf_coe (⟨ψ ⟨x, hxA⟩, ⟨_, rfl⟩⟩ : ↥ψ.range)
      rw [← h2] at h1
      have h1' : orderOf (ψ ⟨x, hxA⟩) ∣ Nat.card ↥ψ.range := h1
      rwa [hψx] at h1'
    have h2 : 2 ∣ Nat.card ↥ψ.range := by
      have h1 := orderOf_dvd_natCard (⟨ψ ⟨b, hbA⟩, ⟨_, rfl⟩⟩ : ↥ψ.range)
      have h2 := Subgroup.orderOf_coe (⟨ψ ⟨b, hbA⟩, ⟨_, rfl⟩⟩ : ↥ψ.range)
      rw [← h2] at h1
      have h1' : orderOf (ψ ⟨b, hbA⟩) ∣ Nat.card ↥ψ.range := h1
      rwa [hψb] at h1'
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hS3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin]
    rfl
  have hrange : ψ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm ?_ ?_)
    · exact Subgroup.card_le_card_group _
    · rw [hS3]
      exact Nat.le_of_dvd Nat.card_pos h6
  have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp hrange
  have hbij : Function.Bijective ψ := hsurj.bijective_of_nat_card_le (by rw [hcard, hS3])
  exact ⟨MulEquiv.ofBijective ψ hbij⟩

theorem isPOnePlusTwo_of_classLeTwo {L : Subgroup D} {x₁ x₂ : D}
    (hL : L = Subgroup.closure {x₁, x₂}) (hL3 : IsPGroup 3 ↥L) (hx₁ : x₁ ^ 3 = 1)
    (hx₂ : x₂ ^ 3 = 1) (hm : Open.pRank 3 (⊤ : Subgroup D) ≤ 2) (hcl : ⁅⁅L, L⁆, L⁆ = ⊥)
    (hna : ⁅L, L⁆ ≠ ⊥) : IsPOnePlusTwo 3 ↥L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp1 : 1 < 3 := Nat.prime_three.one_lt
  have hΩ : Subgroup.closure {x : ↥L | x ^ 3 = 1} = ⊤ := by
    refine A1c.closure_pow_eq_top_of_closure_eq (le_antisymm ?_ ?_)
    · exact (Subgroup.closure_le _).mpr fun x hx => hx.1
    · have hx₁L : x₁ ∈ L := hL ▸ Subgroup.subset_closure (Set.mem_insert _ _)
      have hx₂L : x₂ ∈ L := hL ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      have hsub : ({x₁, x₂} : Set D) ⊆ {x | x ∈ L ∧ x ^ 3 = 1} := by
        rintro y (rfl | rfl)
        · exact ⟨hx₁L, hx₁⟩
        · exact ⟨hx₂L, hx₂⟩
      calc L = Subgroup.closure {x₁, x₂} := hL
        _ ≤ _ := Subgroup.closure_mono hsub
  have hcomm : ¬ ∀ a b : ↥L, a * b = b * a := by
    intro hc
    apply hna
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hc ⟨a, ha⟩ ⟨b, hb⟩)
  have hrank : Open.pRank 3 (⊤ : Subgroup ↥L) = 2 := by
    refine le_antisymm ?_ ?_
    · rw [pRank_top_subtype]
      exact (pRank_mono hp1 le_top).trans hm
    · have hnc : ¬ IsCyclic ↥(⊤ : Subgroup ↥L) := fun hc => by
        apply hcomm
        intro a b
        have := hc.isMulCommutative
        exact congrArg Subtype.val (mul_comm' (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup ↥L))
          ⟨b, Subgroup.mem_top b⟩)
      obtain ⟨E, -, hE, hEc⟩ := A1c.exists_isElemAbelian_card_sq (p := 3) (by norm_num)
        (hL3.to_subgroup ⊤) hnc
      exact CFSG.SectionRank.le_pRank hp1 le_top hE hEc
  rcases isElemAbelianOfRank_two_or_isPOnePlusTwo (p := 3) (by norm_num) hL3 hΩ hrank
    (classLeTwo_top_of hcl) with ⟨⟨e⟩⟩ | h12
  · exact absurd (fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])) hcomm
  · exact h12

theorem isF618CaseTwo_of_isPOnePlusTwo (h : IsGoldschmidtTriple G₁ G₂)
    (hL3 : IsPGroup 3 ↥(twoResidual (⊤ : Subgroup D)))
    (h12 : IsPOnePlusTwo 3 ↥(twoResidual (⊤ : Subgroup D)))
    (eT : ↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    IsF618CaseTwo D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := twoResidual (⊤ : Subgroup D) with hLdef
  set T := G₁ ⊓ G₂ with hTdef
  have hLn : L.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hTL : ∀ t ∈ T, t ∈ L → t = 1 := by
    intro t htT htL
    obtain ⟨i, hi⟩ := h.isPGroup_inf ⟨t, htT⟩
    obtain ⟨j, hj⟩ := hL3 ⟨t, htL⟩
    have hi' : t ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
    have hj' : t ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hc : Nat.Coprime (2 ^ i) (3 ^ j) := Nat.Coprime.pow i j (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
      (orderOf_dvd_of_pow_eq_one hi') hc) (orderOf_dvd_of_pow_eq_one hj'))
  set ι : ↥T →* D ⧸ L := (QuotientGroup.mk' L).comp T.subtype with hι
  have hιb : Function.Bijective ι := by
    refine ⟨fun u v huv => ?_, fun y => ?_⟩
    · have h1 : ((u : D))⁻¹ * v ∈ L := by
        rw [← QuotientGroup.eq]
        exact huv
      have := hTL _ (T.mul_mem (T.inv_mem u.2) v.2) h1
      exact Subtype.ext (inv_mul_eq_one.mp this)
    · obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective L y
      have hd : d ∈ L ⊔ T := by rw [sup_inf_eq_top h]; exact Subgroup.mem_top d
      obtain ⟨ℓ, hℓ, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hd
      refine ⟨⟨t, ht⟩, ?_⟩
      show (QuotientGroup.mk' L) t = (QuotientGroup.mk' L) (ℓ * t)
      have hℓ1 : QuotientGroup.mk' L ℓ = 1 := (QuotientGroup.eq_one_iff ℓ).mpr hℓ
      rw [map_mul, hℓ1, one_mul]
  set φ : D →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    (eT.toMonoidHom.comp (MulEquiv.ofBijective ι hιb).symm.toMonoidHom).comp
      (QuotientGroup.mk' L) with hφ
  have hφs : Function.Surjective φ :=
    (eT.surjective.comp (MulEquiv.ofBijective ι hιb).symm.surjective).comp
      (QuotientGroup.mk'_surjective L)
  have hker : φ.ker = L := by
    ext d
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, MonoidHom.comp_apply]
    constructor
    · intro h1
      have h2 := (MulEquiv.ofBijective ι hιb).symm.injective
        (eT.injective (h1.trans (map_one eT).symm) |>.trans (map_one _).symm)
      exact (QuotientGroup.eq_one_iff d).mp h2
    · intro h1
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff d).mpr h1, map_one, map_one]
  refine Or.inr ⟨φ, hφs, ?_⟩
  rw [hker]
  exact h12

omit [Finite D] in
theorem card_zpowers_sup_zpowers {x b : D} (hx : orderOf x = 3) (hb : orderOf b = 2)
    (hbx : b * x * b⁻¹ = x⁻¹) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers b) = 6 := by
  set N := Subgroup.zpowers x with hN
  set K := Subgroup.zpowers b with hK
  have hNc : Nat.card ↥N = 3 := by rw [hN, Nat.card_zpowers, hx]
  have hKc : Nat.card ↥K = 2 := by rw [hK, Nat.card_zpowers, hb]
  have hbN : b ∈ Subgroup.normalizer (N : Set D) := by
    rw [mem_normalizer_iff_map_conj, hN, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hbx, Subgroup.zpowers_inv]
  have hKN : K ≤ Subgroup.normalizer (N : Set D) := Subgroup.zpowers_le.mpr hbN
  have hNK : N ⊓ K = ⊥ := by
    refine Subgroup.eq_bot_of_card_eq _ ?_
    have h1 : Nat.card ↥(N ⊓ K) ∣ 3 := hNc ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(N ⊓ K) ∣ 2 := hKc ▸ Subgroup.card_dvd_of_le inf_le_right
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (by norm_num)) h2
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' hKN
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := K)
  rw [hNK, Subgroup.card_bot, mul_one, hKc] at h2
  have h3 := Subgroup.relIndex_mul_card (H := N) (K := K ⊔ N)
  rw [inf_eq_left.mpr le_sup_right, hNc, h1, h2] at h3
  rw [sup_comm, ← h3]

theorem klein_sq : ∀ u : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), u ^ 2 = 1 := by
  decide +kernel

theorem klein_comm : ∀ u v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), u * v = v * u := by
  decide +kernel

theorem exists_eq_zpowers_of_card_prime {p : ℕ} [Fact p.Prime] {K : Subgroup D}
    (hK : Nat.card ↥K = p) : ∃ x ∈ K, K = Subgroup.zpowers x ∧ orderOf x = p := by
  have hne : K ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hK
    exact (Fact.out : p.Prime).one_lt.ne' hK.symm
  obtain ⟨⟨x, hxK⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxp : x ^ p = 1 := by
    have h1 : (⟨x, hxK⟩ : ↥K) ^ Nat.card ↥K = 1 := pow_card_eq_one'
    rw [hK] at h1
    simpa using congrArg Subtype.val h1
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1'
  refine ⟨x, hxK, ?_, hord⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxK) ?_).symm
  rw [Nat.card_zpowers, hord, hK]

theorem isF618CaseTwo_of_klein (h : IsGoldschmidtTriple G₁ G₂) (hO : CFSG.pPrimeCore 3 D = ⊥)
    (hm : Open.pRank 3 (⊤ : Subgroup D) ≤ 2) (hL3 : IsPGroup 3 ↥(twoResidual (⊤ : Subgroup D)))
    (e₁ : ↥(pCoreOf 2 G₁) ≃* Multiplicative (ZMod 2))
    (e₂ : ↥(pCoreOf 2 G₂) ≃* Multiplicative (ZMod 2))
    (eT : ↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    IsF618CaseTwo D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Open.pCore 2 D = ⊥ := le_bot_iff.mp (hO ▸ pCore_le_pPrimeCore)
  set L := twoResidual (⊤ : Subgroup D) with hLdef
  set T := G₁ ⊓ G₂ with hTdef
  set Q₁ := pCoreOf 2 G₁ with hQ₁def
  set Q₂ := pCoreOf 2 G₂ with hQ₂def
  have hLn : L.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hodd : Odd (Nat.card ↥L) := by
    obtain ⟨k, hk⟩ := hL3.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hL₁c := card_twoResidual_eq_three_of_le h hL3 (twoResidual_mono le_top)
  have hL₂c := card_twoResidual_eq_three_of_le h.symm hL3 (twoResidual_mono le_top)
  obtain ⟨x₁, hx₁L, hL₁x, hx₁3⟩ := exists_eq_zpowers_of_card_prime hL₁c
  obtain ⟨x₂, hx₂L, hL₂x, hx₂3⟩ := exists_eq_zpowers_of_card_prime hL₂c
  have hQ₁c : Nat.card ↥Q₁ = 2 := by rw [Nat.card_congr e₁.toEquiv]; simp
  have hQ₂c : Nat.card ↥Q₂ = 2 := by rw [Nat.card_congr e₂.toEquiv]; simp
  obtain ⟨a, haQ, hQ₁a, ha2⟩ := exists_eq_zpowers_of_card_prime hQ₁c
  obtain ⟨b, hbQ, hQ₂b, hb2⟩ := exists_eq_zpowers_of_card_prime hQ₂c
  have haT : a ∈ T := pCoreOf_le_inf_left h haQ
  have hbT : b ∈ T := pCoreOf_le_inf_right h hbQ
  have hT2 : ∀ s ∈ T, s ^ 2 = 1 := fun s hs => by
    have h1 : (⟨s, hs⟩ : ↥T) ^ 2 = 1 := eT.injective (by rw [map_pow, klein_sq, map_one])
    simpa using congrArg Subtype.val h1
  have hTc : ∀ s ∈ T, ∀ s' ∈ T, s * s' = s' * s := fun s hs s' hs' => by
    have h1 : (⟨s, hs⟩ : ↥T) * ⟨s', hs'⟩ = ⟨s', hs'⟩ * ⟨s, hs⟩ :=
      eT.injective (by rw [map_mul, map_mul, klein_comm])
    simpa using congrArg Subtype.val h1
  have hQne : Q₁ ≠ Q₂ := by
    intro heq
    have hn : Q₁.Normal := by
      have htop : G₁ ⊔ G₂ ≤ Subgroup.normalizer (Q₁ : Set D) := by
        refine sup_le (le_normalizer_pCoreOf 2 G₁) ?_
        rw [heq]
        exact le_normalizer_pCoreOf 2 G₂
      rw [h.gen] at htop
      exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)
    have hle : Q₁ ≤ Open.pCore 2 D :=
      le_pCore 2 hn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G₁)
    rw [hQ, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hQ₁c
    omega
  have haQ₂ : a ∉ Q₂ := by
    intro haQ₂
    apply hQne
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hQ₁c, hQ₂c])
    rw [hQ₁a]
    exact Subgroup.zpowers_le.mpr haQ₂
  have hbQ₁ : b ∉ Q₁ := by
    intro hbQ₁
    apply hQne
    refine (Subgroup.eq_of_le_of_card_ge ?_ (by rw [hQ₁c, hQ₂c])).symm
    rw [hQ₂b]
    exact Subgroup.zpowers_le.mpr hbQ₁
  have hcom₁ : ∀ q ∈ Q₁, ∀ l ∈ twoResidual G₁, q * l = l * q := by
    have h1 := commutator_eq_bot_of_odd (X := L) (G₁ := G₁) (twoResidual_mono le_top) hodd
    intro q hq l hl
    have h2 := Subgroup.commutator_mem_commutator hq hl
    rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hcom₂ : ∀ q ∈ Q₂, ∀ l ∈ twoResidual G₂, q * l = l * q := by
    have h1 := commutator_eq_bot_of_odd (X := L) (G₁ := G₂) (twoResidual_mono le_top) hodd
    intro q hq l hl
    have h2 := Subgroup.commutator_mem_commutator hq hl
    rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hinv₁ := conj_eq_inv_of_not_mem h hL₁c hbT hbQ₁ hcom₁
  have hinv₂ := conj_eq_inv_of_not_mem h.symm hL₂c (by rw [inf_comm]; exact haT) haQ₂ hcom₂
  have ha₁ : a * x₁ * a⁻¹ = x₁ := by rw [hcom₁ a haQ x₁ hx₁L, mul_inv_cancel_right]
  have hb₂ : b * x₂ * b⁻¹ = x₂ := by rw [hcom₂ b hbQ x₂ hx₂L, mul_inv_cancel_right]
  have ha₂ : a * x₂ * a⁻¹ = x₂⁻¹ := hinv₂ x₂ hx₂L
  have hb₁ : b * x₁ * b⁻¹ = x₁⁻¹ := hinv₁ x₁ hx₁L
  have hx₁c : x₁ ^ 3 = 1 := hx₁3 ▸ pow_orderOf_eq_one x₁
  have hx₂c : x₂ ^ 3 = 1 := hx₂3 ▸ pow_orderOf_eq_one x₂
  have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha2; omega
  have hb1 : b ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hb2; omega
  have hLgen : L = Subgroup.closure {x₁, x₂} := by
    rw [hLdef, twoResidual_top_eq h, hL₁x, hL₂x, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure, ← Subgroup.closure_union, Set.insert_eq]
  have hTL : ∀ s ∈ T, (∀ x ∈ L, s * x = x * s) → s = 1 := by
    intro s hs hsL
    have hmemQ : ∀ {G G' : Subgroup D} (hG : IsGoldschmidtTriple G G'),
        Nat.card ↥(twoResidual G) = 3 → s ∈ G ⊓ G' →
        (∀ q ∈ pCoreOf 2 G, ∀ l ∈ twoResidual G, q * l = l * q) →
        ∀ x ∈ twoResidual G, orderOf x = 3 → s * x = x * s → s ∈ pCoreOf 2 G := by
      intro G G' hG hc hsG hcom x hx hx3 hsx
      by_contra hsQ
      have h1 := conj_eq_inv_of_not_mem hG hc hsG hsQ hcom x hx
      rw [hsx, mul_inv_cancel_right] at h1
      have h2 : x ^ 2 = 1 := by
        calc x ^ 2 = x * x := pow_two x
          _ = x * x⁻¹ := by rw [← h1]
          _ = 1 := mul_inv_cancel x
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hx3] at this
      omega
    have hs₁ := hmemQ h hL₁c hs hcom₁ x₁ hx₁L hx₁3 (hsL x₁ (twoResidual_mono le_top hx₁L))
    have hs₂ := hmemQ h.symm hL₂c (by rw [inf_comm]; exact hs) hcom₂ x₂ hx₂L hx₂3
      (hsL x₂ (twoResidual_mono le_top hx₂L))
    have hQQ : Q₁ ⊓ Q₂ = ⊥ := by
      refine Subgroup.eq_bot_of_card_eq _ ?_
      have hd : Nat.card ↥(Q₁ ⊓ Q₂) ∣ 2 := hQ₁c ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact h1
      · exfalso
        apply hQne
        have e₁' := Subgroup.eq_of_le_of_card_ge (inf_le_left : Q₁ ⊓ Q₂ ≤ Q₁) (by rw [h2, hQ₁c])
        have e₂' := Subgroup.eq_of_le_of_card_ge (inf_le_right : Q₁ ⊓ Q₂ ≤ Q₂) (by rw [h2, hQ₂c])
        rw [← e₁', e₂']
    have : s ∈ Q₁ ⊓ Q₂ := ⟨hs₁, hs₂⟩
    rw [hQQ, Subgroup.mem_bot] at this
    exact this
  have hF : Subgroup.centralizer (L : Set D) ≤ L := centralizer_le_of_isPGroup h hL3 hT2 hTL
  have hLP : L = Open.pCore 3 D := by
    refine le_antisymm (le_pCore 3 hLn hL3) fun x hx => ?_
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := D) 3) ⟨x, hx⟩
    have hk' : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine mem_twoResidual_of_odd (Subgroup.mem_top x) ?_
    exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hk')
  have hA := A1c.A131Concl_of_surjective (p := 3) (by norm_num) (hLP ▸ hF) (Nat.card D) D
    (MonoidHom.id D) Function.surjective_id rfl hm
  have hcyc : ∀ t : D, t ^ 2 = 1 → t ≠ 1 →
      IsCyclic ↥(L ⊓ Subgroup.centralizer ({t} : Set D)) := by
    intro t ht ht1
    have ht2 : IsPGroup 2 ↥(Subgroup.zpowers t) := fun g => ⟨1, by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine Subtype.ext ?_
      rw [pow_one, Subgroup.coe_pow, ← hk, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]⟩
    have ht1' : Subgroup.zpowers t ≠ ⊥ := by rwa [ne_eq, Subgroup.zpowers_eq_bot]
    have := hA.1 (Subgroup.zpowers t) ht2 ht1'
    rwa [← hLP, centralizer_zpowers_eq] at this
  have hcl := commutator_commutator_eq_bot hLgen hL3 hx₁c hx₂c ha₁ ha₂ hb₁ hb₂
    (by rw [← ha2]; exact pow_orderOf_eq_one a) (by rw [← hb2]; exact pow_orderOf_eq_one b)
    ha1 hb1 hcyc
  by_cases hab : ⁅L, L⁆ = ⊥
  ·
    left
    have hx : x₁ * x₂ = x₂ * x₁ := by
      have h1 := Subgroup.commutator_mem_commutator (twoResidual_mono le_top hx₁L)
        (twoResidual_mono le_top hx₂L)
      rwa [hab, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    set A := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers b with hAdef
    set B := Subgroup.zpowers x₂ ⊔ Subgroup.zpowers a with hBdef
    have hAG : A ≤ G₁ := sup_le (Subgroup.zpowers_le.mpr (twoResidual_le G₁ hx₁L))
      (Subgroup.zpowers_le.mpr hbT.1)
    have hBG : B ≤ G₂ := sup_le (Subgroup.zpowers_le.mpr (twoResidual_le G₂ hx₂L))
      (Subgroup.zpowers_le.mpr haT.2)
    have hAc := card_zpowers_sup_zpowers hx₁3 hb2 hb₁
    have hBc := card_zpowers_sup_zpowers hx₂3 ha2 ha₂
    obtain ⟨eA⟩ := nonempty_mulEquiv_perm_of_le h hAG hAc
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) hx₁3 hbT hbQ₁
    obtain ⟨eB⟩ := nonempty_mulEquiv_perm_of_le h.symm hBG hBc
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₂))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)) hx₂3 (by rw [inf_comm]; exact haT)
      haQ₂
    have hBcl : B = Subgroup.closure ({x₂} ∪ {a}) := by
      rw [hBdef, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        Subgroup.closure_union]
    have hAB : A ≤ Subgroup.centralizer (B : Set D) := by
      rw [hBcl, Subgroup.centralizer_closure]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro y (hy | hy) <;> rw [Set.mem_singleton_iff.mp hy]
        · exact hx.symm
        · exact hcom₁ a haQ x₁ hx₁L
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro y (hy | hy) <;> rw [Set.mem_singleton_iff.mp hy]
        · exact (hcom₂ b hbQ x₂ hx₂L).symm
        · exact hTc a haT b hbT
    have hsup : A ⊔ B = ⊤ := by
      refine top_le_iff.mp ?_
      rw [← sup_inf_eq_top h]
      refine sup_le ?_ ?_
      · rw [← hLdef, hLgen, Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      ·
        have hTQ : T ≤ Q₁ ⊔ Q₂ := by
          have hTc4 : Nat.card ↥T = 4 := by rw [Nat.card_congr eT.toEquiv]; simp
          have hle : Q₁ ⊔ Q₂ ≤ T := sup_le (pCoreOf_le_inf_left h) (pCoreOf_le_inf_right h)
          have hd : Nat.card ↥(Q₁ ⊔ Q₂) ∣ 4 := hTc4 ▸ Subgroup.card_dvd_of_le hle
          have hgt : 2 < Nat.card ↥(Q₁ ⊔ Q₂) := by
            have h1 : Q₁ < Q₁ ⊔ Q₂ := lt_of_le_of_ne le_sup_left fun heq =>
              haQ₂ (by
                have : Q₂ ≤ Q₁ := heq ▸ le_sup_right
                exact (Subgroup.eq_of_le_of_card_ge this (by rw [hQ₁c, hQ₂c])) ▸ haQ)
            have := Subgroup.card_lt_of_lt h1
            rwa [hQ₁c] at this
          have h4 : Nat.card ↥(Q₁ ⊔ Q₂) = 4 := by
            have hle4 := Nat.le_of_dvd (by norm_num) hd
            interval_cases (Nat.card ↥(Q₁ ⊔ Q₂)) <;> omega
          exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hTc4])).ge
        refine hTQ.trans (sup_le ?_ ?_)
        · rw [hQ₁a]
          exact le_sup_right.trans le_sup_right
        · rw [hQ₂b]
          exact le_sup_right.trans le_sup_left
    exact nonempty_mulEquiv_prod_of_commute hsup
      (fun x hx y hy => Subgroup.mem_centralizer_iff.mp (hAB hx) y hy |>.symm) eA eB
  ·
    exact isF618CaseTwo_of_isPOnePlusTwo h hL3
      (isPOnePlusTwo_of_classLeTwo hLgen hL3 hx₁c hx₂c hm hcl hab) eT

theorem f6_16 (h : IsGoldschmidtTriple G₁ G₂) (hO : CFSG.pPrimeCore 3 D = ⊥)
    (hm : Open.pRank 3 (⊤ : Subgroup D) ≤ 2) (hnc : ¬ IsCyclic ↥(Open.pCore 3 D)) :
    IsPGroup 3 ↥(twoResidual (⊤ : Subgroup D)) ∧
      ((Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2)) ∧ pCoreOf 2 G₁ = ⊥ ∧
          pCoreOf 2 G₂ = ⊥) ∨ IsF618CaseTwo D) := by
  have hL3 := isPGroup_twoResidual_of_noncyclic h hO hm hnc
  refine ⟨hL3, ?_⟩
  have hQ : Open.pCore 2 D = ⊥ := le_bot_iff.mp (hO ▸ pCore_le_pPrimeCore)
  have hodd : Odd (Nat.card ↥(twoResidual (⊤ : Subgroup D))) := by
    obtain ⟨k, hk⟩ := hL3.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  rcases f6_14 h hodd hQ with ⟨⟨e⟩⟩ | ⟨⟨e₁⟩, ⟨e₂⟩, ⟨eT⟩⟩
  · have hT : Nat.card ↥(G₁ ⊓ G₂) = 2 := by rw [Nat.card_congr e.toEquiv]; simp
    refine Or.inl ⟨⟨e⟩, pCoreOf_eq_bot_of_card_inf h hT, ?_⟩
    exact pCoreOf_eq_bot_of_card_inf h.symm (by rw [inf_comm]; exact hT)
  · exact Or.inr (isF618CaseTwo_of_klein h hO hm hL3 e₁ e₂ eT)

theorem pPrimeCore_eq_bot_and_pRank_le {X : Type*} [Group X] [Finite X]
    (hX : Open.pRank 3 (⊤ : Subgroup X) ≤ 2) (e : D ≃* X ⧸ CFSG.pPrimeCore 3 X) :
    CFSG.pPrimeCore 3 D = ⊥ ∧ Open.pRank 3 (⊤ : Subgroup D) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨(remark_f6_15 e).1, ?_⟩
  have hcop : ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  rw [pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e, pRank_quotient_eq _ hcop]
  exact hX

theorem f6_16_of_sqtk {X : Type} [Group X] [Finite X] (hX : SQTKTauCeti.StronglyQuasithin X)
    (e : D ≃* X ⧸ CFSG.pPrimeCore 3 X) (h : IsGoldschmidtTriple G₁ G₂)
    (hnc : ¬ IsCyclic ↥(Open.pCore 3 D)) :
    IsPGroup 3 ↥(twoResidual (⊤ : Subgroup D)) ∧
      ((Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2)) ∧ pCoreOf 2 G₁ = ⊥ ∧
          pCoreOf 2 G₂ = ⊥) ∨ IsF618CaseTwo D) := by
  obtain ⟨hO, hm⟩ := pPrimeCore_eq_bot_and_pRank_le (hX 3 Nat.prime_three (by norm_num)) e
  exact f6_16 h hO hm hnc

theorem isF618CaseOne_or_two_of_noncyclic {D : Type} [Group D] [Finite D] {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtTriple G₁ G₂) (hO : CFSG.pPrimeCore 3 D = ⊥)
    (hm : Open.pRank 3 (⊤ : Subgroup D) ≤ 2) (hnc : ¬ IsCyclic ↥(Open.pCore 3 D)) :
    IsF618CaseOne G₁ G₂ ∨ IsF618CaseTwo D := by
  rcases (f6_16 h hO hm hnc).2 with ⟨he, h₁, h₂⟩ | h2
  · exact Or.inl ⟨he, h₁, h₂, hnc⟩
  · exact Or.inr h2

@[expose] def TheoremF618Cyclic : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtTriple G₁ G₂ →
    (∃ (X : Type) (_ : Group X) (_ : Finite X), SQTKTauCeti.StronglyQuasithin X ∧
      CFSG.SectionRank.IsKGroupCat X ∧ Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X)) →
    IsCyclic ↥(Open.pCore 3 D) → F618Conclusion G₁ G₂

theorem theoremF618_of_cyclic (hcyc : TheoremF618Cyclic) : TheoremF618 := by
  intro D _ _ G₁ G₂ h hX
  by_cases hc : IsCyclic ↥(Open.pCore 3 D)
  · exact hcyc D G₁ G₂ h hX hc
  · obtain ⟨X, _, _, hsq, -, ⟨e⟩⟩ := hX
    obtain ⟨hO, hm⟩ := pPrimeCore_eq_bot_and_pRank_le (hsq 3 Nat.prime_three (by norm_num)) e
    rcases isF618CaseOne_or_two_of_noncyclic h hO hm hc with h1 | h2
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inl h2))

end F6

end CFSG.Quasithin
