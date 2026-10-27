module

public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

omit [Finite D] in
theorem le_pPrimeCore_of_normal {p : ℕ} {N : Subgroup D} [hN : N.Normal]
    (hc : Nat.Coprime p (Nat.card N)) : N ≤ CFSG.pPrimeCore p D :=
  le_sSup ⟨hN, hc⟩

theorem pCore_le_pPrimeCore : Open.pCore 2 D ≤ CFSG.pPrimeCore 3 D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (Open.pCore 2 D).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  refine le_pPrimeCore_of_normal ?_
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := D) 2).exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem inf_pPrimeCore_le_pCoreOf_left (h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ⊓ CFSG.pPrimeCore 3 D ≤ pCoreOf 2 G₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (le_normalizer_inf_of_normal G₁) ?_
  obtain ⟨a, ha⟩ := exists_card_inf_eq h
  have h1 : Nat.card ↥(G₁ ⊓ CFSG.pPrimeCore 3 D) ∣ 3 * 2 ^ a := by
    rw [← ha, ← card_left h]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.Coprime (Nat.card ↥(G₁ ⊓ CFSG.pPrimeCore 3 D)) 3 := by
    have hc := CFSG.pPrimeCore_coprime_card (p := 3) (G := D)
    have hdvd : Nat.card ↥(G₁ ⊓ CFSG.pPrimeCore 3 D) ∣ Nat.card ↥(CFSG.pPrimeCore 3 D) :=
      Subgroup.card_dvd_of_le inf_le_right
    exact Nat.Coprime.coprime_dvd_left hdvd hc.symm
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (h2.dvd_of_dvd_mul_left h1)
  exact IsPGroup.of_card hm

theorem inf_pPrimeCore_eq_pCore_left (h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ⊓ CFSG.pPrimeCore 3 D = Open.pCore 2 D := by
  have hX : IsSubnormal (CFSG.pPrimeCore 3 D) ⊤ := isSubnormal_top_of_normal
  have h₁ := inf_pPrimeCore_le_pCoreOf_left h
  have h₂ := inf_pPrimeCore_le_pCoreOf_left h.symm
  have hT := inf_le_pCore_of_normal h h₁ h₂
  obtain ⟨e₁, e₂, -⟩ := ((tfae_inf_le_pCoreOf h hX).out 1 2).mp h₁
  rw [e₁, e₂]
  exact le_antisymm hT (le_inf h.pCore_le_inf pCore_le_pPrimeCore)

theorem inf_pPrimeCore_eq_pCore_right (h : IsGoldschmidtTriple G₁ G₂) :
    G₂ ⊓ CFSG.pPrimeCore 3 D = Open.pCore 2 D :=
  inf_pPrimeCore_eq_pCore_left h.symm

theorem inf_inf_pPrimeCore_eq_pCore (h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ⊓ G₂ ⊓ CFSG.pPrimeCore 3 D = Open.pCore 2 D := by
  apply le_antisymm
  · rw [← inf_pPrimeCore_eq_pCore_left h]
    exact inf_le_inf_right _ inf_le_left
  · exact le_inf h.pCore_le_inf pCore_le_pPrimeCore

theorem isSylowTwoOf_pCore_pPrimeCore (h : IsGoldschmidtTriple G₁ G₂) :
    IsSylowTwoOf (Open.pCore 2 D) (CFSG.pPrimeCore 3 D) := by
  have hX : IsSubnormal (CFSG.pPrimeCore 3 D) ⊤ := isSubnormal_top_of_normal
  have hs := isSylowIn_inf_of_isSubnormal hX (isSylowTwoOf_inf_top h)
  rwa [inf_inf_pPrimeCore_eq_pCore h] at hs

theorem isSolvable_pPrimeCore (h : IsGoldschmidtTriple G₁ G₂) :
    Group.IsSolvable ↥(CFSG.pPrimeCore 3 D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := CFSG.pPrimeCore 3 D
  set Q := Open.pCore 2 D
  have hQX : Q ≤ X := pCore_le_pPrimeCore
  have hQn : (Q.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_top.trans
      (Subgroup.normalizer_eq_top_iff.mpr (CFSG.LieType.BorelTits.pCore_normal (G := D) 2)).ge)
  have hsyl := isSylowTwoOf_pCore_pPrimeCore h
  have hQ2 : IsPGroup 2 ↥(Q.subgroupOf X) :=
    hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQX).symm
  have : Group.IsNilpotent ↥(Q.subgroupOf X) := hQ2.isNilpotent
  have hodd : Odd (Nat.card (↥X ⧸ Q.subgroupOf X)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.not_even_iff_odd.mp fun he => hsyl.2.2 (even_iff_two_dvd.mp he)
  have : Group.IsSolvable (↥X ⧸ Q.subgroupOf X) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_subgroup_quotient (Q.subgroupOf X)

omit [Finite D] in
theorem card_map_mk (H N : Subgroup D) [N.Normal] :
    Nat.card ↥(H.map (QuotientGroup.mk' N)) = N.relIndex H := by
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']

omit [Finite D] in
@[expose] def toMapMk (H N : Subgroup D) [N.Normal] : ↥H →* ↥(H.map (QuotientGroup.mk' N)) :=
  ((QuotientGroup.mk' N).comp H.subtype).codRestrict (H.map (QuotientGroup.mk' N))
    (fun x => ⟨x, x.2, rfl⟩)

omit [Finite D] in
@[simp] theorem coe_toMapMk (H N : Subgroup D) [N.Normal] (x : H) :
    (toMapMk H N x : D ⧸ N) = QuotientGroup.mk' N (x : D) := rfl

omit [Finite D] in
theorem toMapMk_surjective (H N : Subgroup D) [N.Normal] : Function.Surjective (toMapMk H N) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite D] in
theorem ker_toMapMk (H N : Subgroup D) [N.Normal] : (toMapMk H N).ker = N.subgroupOf H := by
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    exact (QuotientGroup.eq_one_iff (x : D)).mp (congrArg Subtype.val hx)
  · intro hx
    exact Subtype.ext ((QuotientGroup.eq_one_iff (x : D)).mpr hx)

theorem isoS3_map_mk {G N : Subgroup D} [N.Normal] (hGN : IsPGroup 2 ↥(G ⊓ N))
    (e : ↥G ⧸ Open.pCore 2 ↥G ≃* Equiv.Perm (Fin 3)) :
    Nonempty (↥(G.map (QuotientGroup.mk' N)) ⧸ Open.pCore 2 ↥(G.map (QuotientGroup.mk' N)) ≃*
      Equiv.Perm (Fin 3)) := by
  refine gold_isoS3_of_surjective_kernel (toMapMk G N) (toMapMk_surjective G N) ?_ e
  rw [ker_toMapMk, ← Subgroup.inf_subgroupOf_left]
  exact hGN.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm

omit [Finite D] in
theorem exists_mulEquiv_map_mk {H N₁ N₂ : Subgroup D} [N₁.Normal] [N₂.Normal]
    (hN : H ⊓ N₁ = H ⊓ N₂) :
    ∃ ψ : ↥(H.map (QuotientGroup.mk' N₁)) ≃* ↥(H.map (QuotientGroup.mk' N₂)),
      ∀ x : H, ψ (toMapMk H N₁ x) = toMapMk H N₂ x := by
  have hker : (toMapMk H N₁).ker = (toMapMk H N₂).ker := by
    rw [ker_toMapMk, ker_toMapMk, ← Subgroup.inf_subgroupOf_left, hN,
      Subgroup.inf_subgroupOf_left]
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective _ (toMapMk_surjective H N₁)
  let e₂ := QuotientGroup.quotientKerEquivOfSurjective _ (toMapMk_surjective H N₂)
  refine ⟨e₁.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans e₂), fun x => ?_⟩
  have h1 : e₁.symm (toMapMk H N₁ x) = QuotientGroup.mk x := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MulEquiv.trans_apply, h1]
  rfl

theorem pCore_quotient_pPrimeCore : Open.pCore 2 (D ⧸ CFSG.pPrimeCore 3 D) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := CFSG.pPrimeCore 3 D
  set P := Open.pCore 2 (D ⧸ X)
  have hP : P.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hY : (P.comap (QuotientGroup.mk' X)).Normal := hP.comap _
  have hXY : X ≤ P.comap (QuotientGroup.mk' X) := by
    intro x hx
    rw [Subgroup.mem_comap]
    have : (QuotientGroup.mk' X) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [this]
    exact P.one_mem
  have hmap : (P.comap (QuotientGroup.mk' X)).map (QuotientGroup.mk' X) = P :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective X) P
  have hcard : Nat.card ↥(P.comap (QuotientGroup.mk' X)) = Nat.card ↥P * Nat.card ↥X := by
    have h1 := Subgroup.relIndex_mul_card (H := X) (K := P.comap (QuotientGroup.mk' X))
    rw [inf_eq_left.mpr hXY, ← card_map_mk, hmap] at h1
    exact h1.symm
  have hcop : Nat.Coprime 3 (Nat.card ↥(P.comap (QuotientGroup.mk' X))) := by
    rw [hcard]
    refine Nat.Coprime.mul_right ?_ (CFSG.pPrimeCore_coprime_card (p := 3) (G := D))
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := D ⧸ X) 2).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hle : P.comap (QuotientGroup.mk' X) ≤ X := le_pPrimeCore_of_normal hcop
  rw [eq_bot_iff, ← hmap, ← QuotientGroup.map_mk'_self X]
  exact Subgroup.map_mono hle

theorem swap_mul_mul_inv_mul_eq_one (σ : Equiv.Perm (Fin 3)) (hσ : σ ^ 3 = 1) :
    Equiv.swap 0 1 * σ * (Equiv.swap 0 1)⁻¹ * σ = 1 := by
  revert σ
  decide

omit [Finite D] in
theorem mulAut_comm_of_isCyclic {N : Type*} [Group N] [IsCyclic N] (a b : MulAut N) :
    a * b = b * a := by
  apply (IsCyclic.mulAutMulEquiv N).injective
  rw [map_mul, map_mul, mul_comm]

omit [Finite D] in
theorem commute_of_isCyclic (h : IsGoldschmidtTriple G₁ G₂) {X : Subgroup D} [X.Normal]
    (hQ₂ : pCoreOf 2 G₂ = Open.pCore 2 D)
    (hcyc : IsCyclic ↥(X.map (QuotientGroup.mk' (Open.pCore 2 D)))) {d : D} (hd : d ∈ G₂)
    (hd3 : d ^ 3 = 1) {n : D ⧸ Open.pCore 2 D}
    (hn : n ∈ X.map (QuotientGroup.mk' (Open.pCore 2 D))) :
    QuotientGroup.mk' (Open.pCore 2 D) d * n = n * QuotientGroup.mk' (Open.pCore 2 D) d := by
  have hNn : (X.map (QuotientGroup.mk' (Open.pCore 2 D))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e⟩ := h.quotient₂
  obtain ⟨tq, htq⟩ := e.surjective (Equiv.swap 0 1)
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective tq
  have hσ : (e (QuotientGroup.mk (⟨d, hd⟩ : G₂))) ^ 3 = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow]
    have : (⟨d, hd⟩ : G₂) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [this, QuotientGroup.mk_one, map_one]
  have hinv : (t : D) * d * (t : D)⁻¹ * d ∈ Open.pCore 2 D := by
    have h1 : e (QuotientGroup.mk (t * ⟨d, hd⟩ * t⁻¹ * ⟨d, hd⟩)) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, htq]
      exact swap_mul_mul_inv_mul_eq_one _ hσ
    have h2 : t * ⟨d, hd⟩ * t⁻¹ * ⟨d, hd⟩ ∈ Open.pCore 2 ↥G₂ := by
      rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff e e.injective]
      exact h1
    rw [← hQ₂]
    exact ⟨_, h2, rfl⟩
  let ρ := QuotientGroup.mk' (Open.pCore 2 D)
  have hρ : ρ t * ρ d * (ρ t)⁻¹ = (ρ d)⁻¹ := by
    have : ρ ((t : D) * d * (t : D)⁻¹ * d) = 1 := (QuotientGroup.eq_one_iff _).mpr hinv
    rw [map_mul, map_mul, map_mul, map_inv] at this
    exact eq_inv_of_mul_eq_one_left this
  let φ : D ⧸ Open.pCore 2 D →* MulAut ↥(X.map ρ) := MulAut.conjNormal
  have hφ2 : φ (ρ d) * φ (ρ d) = 1 := by
    have h1 : φ (ρ t) * φ (ρ d) * (φ (ρ t))⁻¹ = (φ (ρ d))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hρ, map_inv]
    rw [mulAut_comm_of_isCyclic (φ (ρ t)) (φ (ρ d)), mul_assoc, mul_inv_cancel, mul_one] at h1
    exact (congrArg (φ (ρ d) * ·) h1).trans (mul_inv_cancel _)
  have hφ3 : φ (ρ d) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hd3, map_one, map_one]
  have hφ : φ (ρ d) = 1 := by
    have : φ (ρ d) = φ (ρ d) ^ 3 * (φ (ρ d) * φ (ρ d))⁻¹ := by group
    rw [this, hφ3, hφ2, one_mul, inv_one]
  have hfix := congrArg (fun a : MulAut ↥(X.map ρ) => ((a ⟨n, hn⟩ : ↥(X.map ρ)) :
    D ⧸ Open.pCore 2 D)) hφ
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at hfix
  calc ρ d * n = ρ d * n * (ρ d)⁻¹ * ρ d := by group
    _ = n * ρ d := by rw [hfix]

theorem not_isCyclic_map_mk (h : IsGoldschmidtTriple G₁ G₂) {X : Subgroup D} [X.Normal]
    (hX3 : Nat.Coprime 3 (Nat.card X)) (hsyl : IsSylowTwoOf (Open.pCore 2 D) X)
    (h₁ : G₁ ⊔ X = ⊤) (hQ₂ : pCoreOf 2 G₂ = Open.pCore 2 D) :
    ¬ IsCyclic ↥(X.map (QuotientGroup.mk' (Open.pCore 2 D))) := by
  intro hcyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := Open.pCore 2 D
  set ρ := QuotientGroup.mk' Q
  set N := X.map ρ
  have hN2 : ¬ 2 ∣ Nat.card N := by
    rw [card_map_mk]
    exact hsyl.2.2
  have hN3 : Nat.Coprime 3 (Nat.card N) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ ρ) hX3
  obtain ⟨a, ha⟩ := exists_card_inf_eq h
  have key : ∀ d ∈ G₂, d ^ 3 = 1 → d ∈ G₁ := by
    intro d hd hd3
    have hdx : d ∈ ((G₁ ⊔ X : Subgroup D) : Set D) := by rw [h₁]; exact Subgroup.mem_top d
    rw [Subgroup.mul_normal] at hdx
    obtain ⟨g, hg, n, hn, rfl⟩ := hdx
    have hρn : ρ n ∈ N := ⟨n, hn, rfl⟩
    have hc0 : Commute (ρ (g * n)) (ρ n) := commute_of_isCyclic h hQ₂ hcyc hd hd3 hρn
    have hcomm : Commute (ρ (g * n)) (ρ n)⁻¹ := hc0.inv_right
    have hcop : Nat.Coprime (orderOf (ρ (g * n))) (orderOf (ρ n)⁻¹) := by
      rw [orderOf_inv]
      have h1 : orderOf (ρ (g * n)) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hd3,
        map_one])
      exact Nat.Coprime.coprime_dvd_left h1
        (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hρn) hN3)
    have hg' : ρ g = ρ (g * n) * (ρ n)⁻¹ := by rw [map_mul, mul_inv_cancel_right]
    have hord : orderOf (ρ n)⁻¹ ∣ orderOf (ρ g) := by
      rw [hg', hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop]
      exact dvd_mul_left _ _
    have hdvd : orderOf (ρ n) ∣ 3 * 2 ^ a := by
      rw [← orderOf_inv, ← ha, ← card_left h]
      exact hord.trans ((orderOf_map_dvd ρ g).trans (Subgroup.orderOf_dvd_natCard G₁ hg))
    have hc6 : Nat.Coprime (orderOf (ρ n)) (3 * 2 ^ a) := by
      have hdN := Subgroup.orderOf_dvd_natCard N hρn
      refine Nat.Coprime.mul_right ?_ ?_
      · exact Nat.Coprime.coprime_dvd_left hdN hN3.symm
      · exact Nat.Coprime.pow_right a (Nat.Coprime.coprime_dvd_left hdN
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hN2).symm)
    have h1 : orderOf (ρ n) = 1 := Nat.Coprime.eq_one_of_dvd hc6 hdvd
    have hnQ : n ∈ Q := (QuotientGroup.eq_one_iff n).mp (orderOf_eq_one_iff.mp h1)
    exact G₁.mul_mem hg ((h.pCore_le_inf.trans inf_le_left) hnQ)
  have hL : twoResidual G₂ ≤ G₁ := by
    rw [twoResidual_eq_oTwoUpper]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact key x hx.1 (orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_three_of_odd h.symm hx.1 hx.2))
  have hG : G₂ ≤ G₁ := by
    rw [← inf_sup_twoResidual_right h]
    exact sup_le inf_le_left hL
  have hc := card_right h
  rw [inf_eq_right.mpr hG] at hc
  have hpos : 0 < Nat.card G₂ := Nat.card_pos
  omega

theorem goldschmidt_mod_pPrimeCore (h : IsGoldschmidtTriple G₁ G₂) :
    (G₁.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)) ⊓
          G₂.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)) =
        (G₁ ⊓ G₂).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)) ∧
      IsGoldschmidtAmalgam (G₁.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)))
        (G₂.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D))) ∧
      IsAmalgamIso (G₁.map (QuotientGroup.mk' (Open.pCore 2 D)))
        (G₂.map (QuotientGroup.mk' (Open.pCore 2 D)))
        (G₁.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)))
        (G₂.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)))) ∨
    (pCoreOf 2 G₁ = Open.pCore 2 D ∧ pCoreOf 2 G₂ = Open.pCore 2 D ∧
      Nonempty (D ⧸ CFSG.pPrimeCore 3 D ≃* Equiv.Perm (Fin 3)) ∧
      G₁ ⊔ CFSG.pPrimeCore 3 D = ⊤ ∧
      ¬ IsCyclic ↥((CFSG.pPrimeCore 3 D).map (QuotientGroup.mk' (Open.pCore 2 D)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e₁ := inf_pPrimeCore_eq_pCore_left h
  have e₂ := inf_pPrimeCore_eq_pCore_right h
  have eT := inf_inf_pPrimeCore_eq_pCore h
  have hQX : Open.pCore 2 D ≤ CFSG.pPrimeCore 3 D := pCore_le_pPrimeCore
  have hO := pCore_quotient_pPrimeCore (D := D)
  have hcT : Nat.card ↥((G₁ ⊓ G₂).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D))) =
      (Open.pCore 2 D).relIndex (G₁ ⊓ G₂) := by
    rw [card_map_mk, ← Subgroup.inf_relIndex_right, inf_comm, eT]
  have hcG : ∀ {G : Subgroup D}, G ⊓ CFSG.pPrimeCore 3 D = Open.pCore 2 D →
      (G₁ ⊓ G₂).relIndex G = 3 → G₁ ⊓ G₂ ≤ G →
      Nat.card ↥(G.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D))) =
        3 * Nat.card ↥((G₁ ⊓ G₂).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D))) := by
    intro G hG h3 hTG
    rw [hcT, card_map_mk, ← Subgroup.inf_relIndex_right, inf_comm, hG,
      ← Subgroup.relIndex_mul_relIndex _ _ _ h.pCore_le_inf hTG, h3, mul_comm]
  have hc₁ := hcG e₁ h.relIndex_inf_left inf_le_left
  have hc₂ := hcG e₂ h.relIndex_inf_right inf_le_right
  set X := CFSG.pPrimeCore 3 D with hXdef
  set π := QuotientGroup.mk' X
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective X
  have hTle : (G₁ ⊓ G₂).map π ≤ G₁.map π ⊓ G₂.map π := Subgroup.map_inf_le _ _ _
  have hgen : G₁.map π ⊔ G₂.map π = ⊤ := by
    rw [← Subgroup.map_sup, h.gen, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hπ
  have hT0 : 0 < Nat.card ↥((G₁ ⊓ G₂).map π) := Nat.card_pos
  have hidx : ((G₁ ⊓ G₂).map π).relIndex (G₁.map π) = 3 := by
    have h1 := Subgroup.relIndex_mul_card (H := (G₁ ⊓ G₂).map π) (K := G₁.map π)
    rw [inf_eq_left.mpr (hTle.trans inf_le_left), hc₁] at h1
    exact Nat.eq_of_mul_eq_mul_right hT0 h1
  have hsplit := Subgroup.relIndex_mul_relIndex ((G₁ ⊓ G₂).map π) (G₁.map π ⊓ G₂.map π)
    (G₁.map π) hTle inf_le_left
  rw [hidx] at hsplit
  by_cases hcase : G₁.map π ⊓ G₂.map π = (G₁ ⊓ G₂).map π
  ·
    left
    refine ⟨hcase, ?_, ?_⟩
    · refine
        { gen := hgen
          quotient₁ := isoS3_map_mk ?_ h.quotient₁.some
          quotient₂ := isoS3_map_mk ?_ h.quotient₂.some
          sylow := ?_
          pCore_eq_bot := hO }
      · rw [e₁]; exact CFSG.LieType.BorelTits.pCore_isPGroup 2
      · rw [e₂]; exact CFSG.LieType.BorelTits.pCore_isPGroup 2
      · obtain ⟨T, hT⟩ := h.sylow
        refine ⟨T.mapSurjective hπ, ?_⟩
        rw [Sylow.coe_mapSurjective, hT, hcase]
    ·
      have hQ₁ : G₁ ⊓ Open.pCore 2 D = G₁ ⊓ X := by
        rw [e₁, inf_eq_right.mpr (h.pCore_le_inf.trans inf_le_left)]
      have hQ₂ : G₂ ⊓ Open.pCore 2 D = G₂ ⊓ X := by
        rw [e₂, inf_eq_right.mpr (h.pCore_le_inf.trans inf_le_right)]
      obtain ⟨φ₁, hφ₁⟩ := exists_mulEquiv_map_mk hQ₁
      obtain ⟨φ₂, hφ₂⟩ := exists_mulEquiv_map_mk hQ₂
      refine ⟨φ₁, φ₂, ?_, ?_⟩
      · intro y hy₁ hy₂
        obtain ⟨g₁, hg₁, rfl⟩ := hy₁
        obtain ⟨g₂, hg₂, hg⟩ := hy₂
        have hy : (⟨QuotientGroup.mk' (Open.pCore 2 D) g₁, g₂, hg₂, hg⟩ :
            ↥(G₂.map (QuotientGroup.mk' (Open.pCore 2 D)))) =
            toMapMk G₂ (Open.pCore 2 D) ⟨g₂, hg₂⟩ := Subtype.ext hg.symm
        have k1 := congrArg Subtype.val (hφ₁ ⟨g₁, hg₁⟩)
        have k2 := congrArg Subtype.val (hφ₂ ⟨g₂, hg₂⟩)
        rw [← hy] at k2
        refine k1.trans (Eq.trans ?_ k2.symm)
        simp only [coe_toMapMk, QuotientGroup.mk'_apply]
        rw [QuotientGroup.eq]
        apply hQX
        rw [← QuotientGroup.eq]
        simpa [QuotientGroup.mk'_apply] using hg.symm
      · intro z hz₁ hz₂
        have hz : z ∈ (G₁ ⊓ G₂).map π := hcase ▸ ⟨hz₁, hz₂⟩
        obtain ⟨t, ht, rfl⟩ := hz
        have h1 : φ₁.symm ⟨π t, hz₁⟩ = toMapMk G₁ (Open.pCore 2 D) ⟨t, ht.1⟩ := by
          rw [MulEquiv.symm_apply_eq, hφ₁]
          rfl
        have h2 : φ₂.symm ⟨π t, hz₂⟩ = toMapMk G₂ (Open.pCore 2 D) ⟨t, ht.2⟩ := by
          rw [MulEquiv.symm_apply_eq, hφ₂]
          rfl
        rw [h1, h2]
        rfl
  ·
    right
    have h1 : ((G₁ ⊓ G₂).map π).relIndex (G₁.map π ⊓ G₂.map π) ≠ 1 := by
      intro h1
      exact hcase (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hTle)
    have h2 : (G₁.map π ⊓ G₂.map π).relIndex (G₁.map π) = 1 := by
      have hdvd : ((G₁ ⊓ G₂).map π).relIndex (G₁.map π ⊓ G₂.map π) ∣ 3 := ⟨_, hsplit.symm⟩
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h3 | h3
      · exact absurd h3 h1
      · rw [h3] at hsplit
        omega
    have hle : G₁.map π ≤ G₂.map π := (Subgroup.relIndex_eq_one.mp h2).trans inf_le_right
    have heq : G₁.map π = G₂.map π :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc₁, hc₂])
    have htop₁ : G₁.map π = ⊤ := by rw [← hgen, heq, sup_idem]
    have htop₂ : G₂.map π = ⊤ := heq ▸ htop₁
    have hQi : ∀ {G : Subgroup D}, G.map π = ⊤ → G ⊓ X = Open.pCore 2 D →
        Open.pCore 2 D ≤ G → pCoreOf 2 G = Open.pCore 2 D := by
      intro G hG hGX hQG
      apply le_antisymm
      · have hn : ((pCoreOf 2 G).map π).Normal := by
          rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← hG]
          exact (Subgroup.map_mono (le_normalizer_pCoreOf 2 G)).trans
            (Subgroup.le_normalizer_map π)
        have hle' : (pCoreOf 2 G).map π ≤ Open.pCore 2 (D ⧸ X) :=
          CFSG.LieType.BorelTits.le_pCore 2 hn ((pCoreOf_isPGroup 2 G).map π)
        have hle'' : pCoreOf 2 G ≤ X := by
          intro x hx
          have hx' : π x ∈ Open.pCore 2 (D ⧸ X) := hle' ⟨x, hx, rfl⟩
          rw [hO, Subgroup.mem_bot] at hx'
          exact (QuotientGroup.eq_one_iff x).mp hx'
        rw [← hGX]
        exact le_inf (pCoreOf_le 2 G) hle'' 
      · refine le_pCoreOf_of_le_normalizer 2 hQG ?_ (CFSG.LieType.BorelTits.pCore_isPGroup 2)
        exact le_top.trans (Subgroup.normalizer_eq_top_iff.mpr
          (CFSG.LieType.BorelTits.pCore_normal 2)).ge
    have hQ₁ := hQi htop₁ e₁ (h.pCore_le_inf.trans inf_le_left)
    have hQ₂ := hQi htop₂ e₂ (h.pCore_le_inf.trans inf_le_right)
    have hsup : G₁ ⊔ X = ⊤ := by
      rw [← QuotientGroup.ker_mk' X, ← Subgroup.comap_map_eq, htop₁, Subgroup.comap_top]
    refine ⟨hQ₁, hQ₂, ?_, hsup, ?_⟩
    ·
      obtain ⟨e⟩ := h.quotient₁
      let ψ : ↥G₁ →* D ⧸ X := π.comp G₁.subtype
      have hψ : Function.Surjective ψ := by
        intro y
        have hy : y ∈ G₁.map π := htop₁ ▸ Subgroup.mem_top y
        obtain ⟨g, hg, rfl⟩ := hy
        exact ⟨⟨g, hg⟩, rfl⟩
      have hker : ψ.ker = Open.pCore 2 ↥G₁ := by
        ext x
        simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, Subgroup.coe_subtype]
        rw [show π (x : D) = ((x : D) : D ⧸ X) from rfl, QuotientGroup.eq_one_iff]
        constructor
        · intro hx
          have hx' : (x : D) ∈ pCoreOf 2 G₁ := by
            rw [hQ₁, ← e₁]
            exact ⟨x.2, hx⟩
          obtain ⟨y, hy, hyx⟩ := hx'
          rwa [← Subtype.ext hyx]
        · intro hx
          have : (x : D) ∈ pCoreOf 2 G₁ := ⟨x, hx, rfl⟩
          rw [hQ₁] at this
          exact hQX this
      exact ⟨((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker)).trans e⟩
    · exact not_isCyclic_map_mk h (CFSG.pPrimeCore_coprime_card (p := 3) (G := D))
        (isSylowTwoOf_pCore_pPrimeCore h) hsup hQ₂

omit [Finite D] in
@[expose] def IsGoldschmidtTripleIn (I G₁ G₂ : Subgroup D) : Prop :=
  G₁ ⊔ G₂ = I ∧ Nonempty (↥G₁ ⧸ Open.pCore 2 ↥G₁ ≃* Equiv.Perm (Fin 3)) ∧
    Nonempty (↥G₂ ⧸ Open.pCore 2 ↥G₂ ≃* Equiv.Perm (Fin 3)) ∧ IsSylowTwoOf (G₁ ⊓ G₂) I

theorem IsGoldschmidtTripleIn.subgroupOf {I : Subgroup D} (h : IsGoldschmidtTripleIn I G₁ G₂) :
    IsGoldschmidtTriple (G₁.subgroupOf I) (G₂.subgroupOf I) := by
  obtain ⟨hgen, ⟨e₁⟩, ⟨e₂⟩, hsyl⟩ := h
  have h₁ : G₁ ≤ I := hgen ▸ le_sup_left
  have h₂ : G₂ ≤ I := hgen ▸ le_sup_right
  have hiso : ∀ {G : Subgroup D}, G ≤ I → (↥G ⧸ Open.pCore 2 ↥G ≃* Equiv.Perm (Fin 3)) →
      Nonempty (↥(G.subgroupOf I) ⧸ Open.pCore 2 ↥(G.subgroupOf I) ≃* Equiv.Perm (Fin 3)) := by
    intro G hG e
    let ψ := (Subgroup.subgroupOfEquivOfLe hG).symm
    refine gold_isoS3_of_surjective_kernel ψ.toMonoidHom ψ.surjective ?_ e
    rw [MonoidHom.ker_eq_bot_iff _ |>.mpr ψ.injective]
    exact IsPGroup.of_bot
  refine ⟨?_, hiso h₁ e₁, hiso h₂ e₂, ?_⟩
  · rw [← Subgroup.subgroupOf_sup h₁ h₂, hgen, Subgroup.subgroupOf_self]
  · refine ⟨A4.toSylow hsyl, ?_⟩
    rw [A4.toSylow_coe]
    ext x
    simp [Subgroup.mem_subgroupOf]

theorem IsGoldschmidtTripleIn.isSylowTwoOf_pCore_pPrimeCore {I : Subgroup D}
    (h : IsGoldschmidtTripleIn I G₁ G₂) :
    IsSylowTwoOf (Open.pCore 2 ↥I) (CFSG.pPrimeCore 3 ↥I) :=
  F6.isSylowTwoOf_pCore_pPrimeCore h.subgroupOf

theorem IsGoldschmidtTripleIn.isSolvable_pPrimeCore {I : Subgroup D}
    (h : IsGoldschmidtTripleIn I G₁ G₂) : Group.IsSolvable ↥(CFSG.pPrimeCore 3 ↥I) :=
  F6.isSolvable_pPrimeCore h.subgroupOf

theorem IsGoldschmidtTripleIn.goldschmidt_mod_pPrimeCore {I : Subgroup D}
    (h : IsGoldschmidtTripleIn I G₁ G₂) :
    ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
          (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) =
        (G₁.subgroupOf I ⊓ G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ∧
      IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ∧
      IsAmalgamIso ((G₁.subgroupOf I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))
        ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))) ∨
    (pCoreOf 2 (G₁.subgroupOf I) = Open.pCore 2 ↥I ∧
      pCoreOf 2 (G₂.subgroupOf I) = Open.pCore 2 ↥I ∧
      Nonempty (↥I ⧸ CFSG.pPrimeCore 3 ↥I ≃* Equiv.Perm (Fin 3)) ∧
      G₁.subgroupOf I ⊔ CFSG.pPrimeCore 3 ↥I = ⊤ ∧
      ¬ IsCyclic ↥((CFSG.pPrimeCore 3 ↥I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))) :=
  F6.goldschmidt_mod_pPrimeCore h.subgroupOf

end F6

end CFSG.Quasithin
