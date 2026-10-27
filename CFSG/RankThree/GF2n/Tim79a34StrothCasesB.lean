module

public import CFSG.RankThree.GF2n.Tim79a34QaFacts
public import CFSG.RankThree.GF2n.Tim79a34Lemma13

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open CFSG.LargeExtraspecial.Timmesfeld (Qa fStar)

variable {G : Type} [Group G] [Finite G]

theorem sc_normal_of_omega {K : Type} [Group K] {A C : Subgroup K} {x : K}
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c) (hCcard : Nat.card C = 3)
    (hspan : A ⊔ C ⊔ Subgroup.zpowers x = ⊤)
    (hperm : Nonempty (↥(C ⊔ Subgroup.zpowers x) ≃* Equiv.Perm (Fin 3))) : C.Normal := by
  obtain ⟨e⟩ := hperm
  have hS6 : Nat.card ↥(C ⊔ Subgroup.zpowers x) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hCsub : Nat.card ↥(C.subgroupOf (C ⊔ Subgroup.zpowers x)) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : C ≤ C ⊔ Subgroup.zpowers x)).toEquiv, hCcard]
  have hidx : (C.subgroupOf (C ⊔ Subgroup.zpowers x)).index = 2 := by
    have h := Subgroup.card_mul_index (H := C.subgroupOf (C ⊔ Subgroup.zpowers x))
    rw [hCsub, hS6] at h
    omega
  have hSN : (C.subgroupOf (C ⊔ Subgroup.zpowers x)).Normal :=
    Subgroup.normal_of_index_eq_two hidx
  have hxS : x ∈ C ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hSn : ∀ g ∈ C ⊔ Subgroup.zpowers x, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    have h := hSN.conj_mem (⟨c, Subgroup.mem_sup_left hc⟩ : ↥(C ⊔ Subgroup.zpowers x))
      (Subgroup.mem_subgroupOf.mpr hc) (⟨g, hg⟩ : ↥(C ⊔ Subgroup.zpowers x))
    exact Subgroup.mem_subgroupOf.mp h
  have hnorm : ∀ s : K, (∀ c ∈ C, s * c * s⁻¹ ∈ C) → (∀ c ∈ C, s⁻¹ * c * s ∈ C) →
      s ∈ Subgroup.normalizer (C : Set K) := by
    intro s h1 h2
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact h1 g
    · intro hg
      have h := h2 (s * g * s⁻¹) hg
      have e' : s⁻¹ * (s * g * s⁻¹) * s = g := by group
      rw [e'] at h
      exact h
  have hAn : ∀ a ∈ A, a ∈ Subgroup.normalizer (C : Set K) := by
    intro a ha
    apply hnorm a
    · intro c hc
      have h := hcomm a ha c hc
      rw [h.eq, mul_inv_cancel_right]
      exact hc
    · intro c hc
      have h := (hcomm a ha c hc).inv_left
      rw [h.eq, inv_mul_cancel_right]
      exact hc
  have hxN : x ∈ Subgroup.normalizer (C : Set K) := by
    apply hnorm x
    · exact hSn x hxS
    · intro c hc
      have h := hSn x⁻¹ (Subgroup.inv_mem _ hxS) c hc
      rwa [inv_inv] at h
  have htop : (⊤ : Subgroup K) ≤ Subgroup.normalizer (C : Set K) := by
    rw [← hspan]
    exact sup_le (sup_le hAn C.le_normalizer) (Subgroup.zpowers_le.mpr hxN)
  exact ⟨fun c hc g => (Subgroup.mem_normalizer_iff.mp (htop (Subgroup.mem_top g)) c).mp hc⟩

theorem sc_conj_fix {K : Type} [Group K] [Finite K] (V : Subgroup K)
    (hcard : Nat.card V = 4) {a ρ : K} (ha : a ∈ V) (ha1 : a ≠ 1)
    (hρV : ∀ x ∈ V, ρ * x * ρ⁻¹ ∈ V) (hρa : ρ * a * ρ⁻¹ = a) (hρ3 : ρ ^ 3 = 1) :
    ∀ x ∈ V, ρ * x * ρ⁻¹ = x := by
  have hinj : ∀ p q : K, ρ * p * ρ⁻¹ = ρ * q * ρ⁻¹ → p = q := fun p q h =>
    mul_left_cancel (mul_right_cancel h)
  have hρ3' : ρ * ρ * ρ = 1 := by rw [← pow_three']; exact hρ3
  have hρinv : ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = 1 := by
    rw [show ρ⁻¹ * ρ⁻¹ * ρ⁻¹ = (ρ * ρ * ρ)⁻¹ by simp [mul_assoc], hρ3', inv_one]
  have hcube : ∀ g : K, ρ * (ρ * (ρ * g * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = g := fun g => by
    calc ρ * (ρ * (ρ * g * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = (ρ * ρ * ρ) * g * (ρ⁻¹ * ρ⁻¹ * ρ⁻¹) := by
          simp only [mul_assoc]
      _ = g := by rw [hρ3', hρinv, one_mul, mul_one]
  intro x hx
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, y = ρ * x * ρ⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = ρ * y * ρ⁻¹ := ⟨_, rfl⟩
  have hyV : y ∈ V := hy ▸ hρV x hx
  have hzV : z ∈ V := hz ▸ hρV y hyV
  have hzx : ρ * z * ρ⁻¹ = x := by rw [hz, hy]; exact hcube x
  have hyx : y ≠ x := fun h => hne (hy.symm.trans h)
  have hx1 : x ≠ 1 := fun h => hne (by rw [h]; simp)
  have hxa : x ≠ a := fun h => hne (by rw [h]; exact hρa)
  have hy1 : y ≠ 1 := fun h => hx1 (hinj x 1 (by rw [← hy, h]; simp))
  have hya : y ≠ a := fun h => hxa (hinj x a (by rw [← hy, h, hρa]))
  have hz1 : z ≠ 1 := fun h => hy1 (hinj y 1 (by rw [← hz, h]; simp))
  have hza : z ≠ a := fun h => hya (hinj y a (by rw [← hz, h, hρa]))
  have hxz : x ≠ z := fun h => by
    rw [← h] at hzx
    exact hne hzx
  have hyz : y ≠ z := fun h => hyx (hinj y x (by rw [← hz, ← hy]; exact h.symm))
  have hsub : ({1, a, x, y, z} : Set K) ⊆ (V : Set K) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h | h | h <;> rw [h]
    · exact V.one_mem
    · exact ha
    · exact hx
    · exact hyV
    · exact hzV
  have n1 : (1 : K) ∉ ({a, x, y, z} : Set K) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha1.symm, hx1.symm, hy1.symm, hz1.symm⟩
  have n2 : a ∉ ({x, y, z} : Set K) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hxa.symm, hya.symm, hza.symm⟩
  have n3 : x ∉ ({y, z} : Set K) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hyx.symm, hxz⟩
  have hcount : ({1, a, x, y, z} : Set K).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_pair hyz]
  have hle := Set.ncard_le_ncard hsub
  have hVn : (V : Set K).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  omega

theorem sc_lift {M Q : Subgroup G} [(Q.subgroupOf M).Normal]
    (hQ2 : IsPGroup 2 ↥Q) {C : Subgroup (↥M ⧸ Q.subgroupOf M)} (hC3 : Nat.card C = 3) :
    ∃ ρ : G, ∃ hρ : ρ ∈ M, orderOf ρ = 3 ∧
      (QuotientGroup.mk (⟨ρ, hρ⟩ : ↥M) : ↥M ⧸ Q.subgroupOf M) ∈ C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnt : Nontrivial C := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨⟨c, hcC⟩, hc1⟩ := exists_ne (1 : C)
  have hc1' : c ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hc3 : c ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := (⟨c, hcC⟩ : C))
    rw [hC3] at h
    have h' := congrArg Subtype.val h
    simpa using h'
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective c
  have hq3 : (g0 : G) ^ 3 ∈ Q := by
    have h1 : (QuotientGroup.mk (g0 ^ 3) : ↥M ⧸ Q.subgroupOf M) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hc3
    have h2 := (QuotientGroup.eq_one_iff (g0 ^ 3)).mp h1
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa using h3
  obtain ⟨k, hk⟩ := hQ2 (⟨(g0 : G) ^ 3, hq3⟩ : ↥Q)
  have hk' : ((g0 : G) ^ 3) ^ (2 ^ k) = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hρM : (g0 : G) ^ (2 ^ k) ∈ M := pow_mem g0.2 _
  refine ⟨(g0 : G) ^ (2 ^ k), hρM, ?_, ?_⟩
  · have h3 : ((g0 : G) ^ (2 ^ k)) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hk']
    have h1 : (g0 : G) ^ (2 ^ k) ≠ 1 := by
      intro h1
      have h1' : g0 ^ (2 ^ k) = 1 := Subtype.ext (by simpa using h1)
      have hpow : (QuotientGroup.mk g0 : ↥M ⧸ Q.subgroupOf M) ^ (2 ^ k) = 1 := by
        rw [← QuotientGroup.mk_pow, h1', QuotientGroup.mk_one]
      have hdvd := orderOf_dvd_of_pow_eq_one hpow
      rw [orderOf_eq_prime hc3 hc1'] at hdvd
      have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      norm_num at h32
    exact orderOf_eq_prime h3 h1
  · have hmk : (QuotientGroup.mk (⟨(g0 : G) ^ (2 ^ k), hρM⟩ : ↥M) :
        ↥M ⧸ Q.subgroupOf M) = (QuotientGroup.mk g0 : ↥M ⧸ Q.subgroupOf M) ^ (2 ^ k) := by
      rw [← QuotientGroup.mk_pow]
      rfl
    rw [hmk]
    exact C.pow_mem hcC _

theorem strothCaseII_false {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h11b : Lemma11bStatement) (h12 : Lemma12Statement)
    (h13 : Lemma13Statement) (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ) :
    ¬ StrothCaseII cfg.aG w := by
  intro h
  obtain ⟨⟨R, hRc, hRcard, hnot⟩, -⟩ := h
  have hH := cfg.hyp
  have hcent : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H hH cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hcV : centerIn (Qa cfg.aG) = V := by
    rw [qa_aG_eq h12 cfg, centerIn_Q_eq h11b cfg]
  have hV4 : Nat.card ↥V = 4 := qpCfg_card_V cfg
  rw [hcV] at hRc hRcard
  rw [hV4] at hRcard
  have hR2 : Nat.card ↥R = 2 := by omega
  have hRnt : Nontrivial ↥R := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨r, hr1⟩ := exists_ne (1 : ↥R)
  have hr : (r : G) ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrV : (r : G) ∈ V := hRc r.2
  have haV : cfg.aG ∈ V := qpCfg_aG_mem_V cfg
  have haW : cfg.aG ∈ wOf V H := (Additive.toMul (ψ a)).2
  have haG1 : cfg.aG ≠ 1 := qpCfg_aG_ne_one cfg
  have hVW : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hle : Subgroup.centralizer (R : Set G) ≤ Subgroup.centralizer ({cfg.aG} : Set G) := by
    intro g hg
    have hgr : (r : G) * g = g * (r : G) := Subgroup.mem_centralizer_iff.mp hg (r : G) r.2
    by_cases hW : (r : G) ∈ wOf V H
    · have hreq : (r : G) = cfg.aG :=
        l13_eq_of_natCard_two hVW (Subgroup.mem_inf.mpr ⟨hrV, hW⟩)
          (Subgroup.mem_inf.mpr ⟨haV, haW⟩) hr haG1
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rw [Set.mem_singleton_iff.mp hk, ← hreq]
      exact hgr
    · have hgr' : g ∈ Subgroup.centralizer ({(r : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        rw [Set.mem_singleton_iff.mp hk]
        exact hgr
      rw [(h13 G M V Q P H hH cfg.centre cfg.iw (r : G) hrV hW).1] at hgr'
      rw [hcent]
      exact (Subgroup.mem_inf.mp hgr').1
  exact hnot (fun g hg => Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hle hg, hg⟩))

theorem strothCaseVI_false {M V Q P H : Subgroup G} {n : ℕ}
    {Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 1) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 1} {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    (h12 : Lemma12Statement) (h11b : Lemma11bStatement)
    (cfg : QPCfg M V Q P H Φ ψ a T) (w : ℕ) : ¬ StrothCaseVI cfg.aG w := by
  intro h
  obtain ⟨-, ⟨hN, hOm, hpc⟩, -⟩ := h
  have hH := cfg.hyp
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcent : Subgroup.centralizer ({cfg.aG} : Set G) = M :=
    (h12 G M V Q P H hH cfg.centre Φ ψ cfg.nat a T cfg.ne cfg.trans cfg.point).1
  have hQa : Qa cfg.aG = Q := qa_aG_eq h12 cfg
  have hcV : centerIn (Qa cfg.aG) = V := by
    rw [hQa, centerIn_Q_eq h11b cfg]
  have hV4 : Nat.card ↥V = 4 := qpCfg_card_V cfg
  have haV : cfg.aG ∈ V := qpCfg_aG_mem_V cfg
  have haG1 : cfg.aG ≠ 1 := qpCfg_aG_ne_one cfg
  have hQ2 : IsPGroup 2 ↥(Qa cfg.aG) := by
    rw [hQa, hc.hQ]
    exact (inSubgroup_pCore_two M).1
  have hNV : ∀ g ∈ Subgroup.centralizer ({cfg.aG} : Set G), ∀ x ∈ V, g * x * g⁻¹ ∈ V := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq, ← hcent]
      exact hg
    exact fun x hx => (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
  obtain ⟨A, C, x, hcomm, -, -, hCcard, hspan, -, hperm⟩ := hOm
  have hCnorm : C.Normal := sc_normal_of_omega hcomm hCcard hspan hperm
  have hCpg : IsPGroup 3 ↥C := IsPGroup.of_card (n := 1) (by rw [hCcard]; norm_num)
  have hCle : C ≤ pCore 3 _ := le_sSup ⟨hCnorm, hCpg⟩
  obtain ⟨ρ, hρC, hord, hmem⟩ :=
    sc_lift (M := Subgroup.centralizer ({cfg.aG} : Set G)) hQ2 hCcard
  have hρ3 : ρ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one ρ
    rwa [hord] at h
  have hρa : ρ * cfg.aG * ρ⁻¹ = cfg.aG := by
    have h := Subgroup.mem_centralizer_iff.mp hρC cfg.aG (Set.mem_singleton _)
    rw [← h, mul_inv_cancel_right]
  have hcentV := sc_conj_fix V hV4 haV haG1 (hNV ρ hρC) hρa hρ3
  have hset : {y : G | ∃ x ∈ centerIn (Qa cfg.aG), y = ρ * x * ρ⁻¹ * x⁻¹} = {1} := by
    rw [hcV]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hcentV x hx, mul_inv_cancel]
    · rintro rfl
      exact ⟨1, V.one_mem, by simp⟩
  have hcard := hpc ρ hρC hord (hCle hmem)
  rw [hset, Subgroup.closure_singleton_one, Subgroup.card_bot] at hcard
  omega

end CFSG.RankThree.GF2n.Tim79a
