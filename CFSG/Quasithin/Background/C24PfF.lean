module

public import CFSG.Quasithin.Background.C24PfE
public import CFSG.Quasithin.Background.C24PfA
public import CFSG.Quasithin.Background.C24PfB
public import CFSG.Quasithin.Background.C22PfD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace C24Pf

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_normalizer_of_isSylowTwoOf {P K : Subgroup G} (hP : IsSylowTwoOf P K)
    {g : G} (hgK : g ∈ K) (hgN : g ∈ Subgroup.normalizer (P : Set G))
    (hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1) : g ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzN : Subgroup.zpowers g ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le).mpr hgN
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers g) := by
    obtain ⟨k, hk⟩ := hg2
    rintro ⟨_, ⟨i, rfl⟩⟩
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  have hPz : IsPGroup 2 ↥(P ⊔ Subgroup.zpowers g) :=
    IsPGroup.to_sup_of_normal_left' hP.2.1 hz2 hzN
  have hle : P ⊔ Subgroup.zpowers g ≤ K :=
    sup_le hP.1 ((Subgroup.zpowers_le).mpr hgK)
  have hmax := ((A4.isSylowTwoOf_iff_maximal).mp hP).2.2 _ hle hPz le_sup_left
  exact hmax (Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

omit [Finite G] in
theorem pow_mul_mem {P : Subgroup G} {u v : G} (hu : u ∈ Subgroup.normalizer (P : Set G))
    (hv : v ∈ Subgroup.normalizer (P : Set G)) (huv : u * v * u⁻¹ * v⁻¹ ∈ P) (n : ℕ) :
    (u ^ n * v ^ n)⁻¹ * (u * v) ^ n ∈ P := by
  set N := Subgroup.normalizer (P : Set G) with hN
  have hPN : (P.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  set π := QuotientGroup.mk' (P.subgroupOf N) with hπ
  have hc : Commute (π ⟨u, hu⟩) (π ⟨v, hv⟩) := by
    show π ⟨u, hu⟩ * π ⟨v, hv⟩ = π ⟨v, hv⟩ * π ⟨u, hu⟩
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have huvN : (u * v)⁻¹ ∈ N := N.inv_mem (N.mul_mem hu hv)
    have h3 := (Subgroup.mem_normalizer_iff.mp huvN _).mp (P.inv_mem huv)
    have e : (u * v)⁻¹ * (u * v * u⁻¹ * v⁻¹)⁻¹ * (u * v)⁻¹⁻¹ = (u * v)⁻¹ * (v * u) := by group
    rw [e] at h3
    simpa using h3
  have hpow : π (⟨u, hu⟩ ^ n * ⟨v, hv⟩ ^ n) = π ((⟨u, hu⟩ * ⟨v, hv⟩) ^ n) := by
    rw [map_mul, map_pow, map_pow, map_pow, map_mul, hc.mul_pow]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hpow
  simpa using hpow

theorem mem_pCoreOf_of_commute {L : Subgroup G} {b : G} (hb : b ∈ L)
    (hc : ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 L) (hb2 : ∃ k : ℕ, b ^ 2 ^ k ∈ pCoreOf 2 L) :
    b ∈ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 L with hO
  have hOL : O ≤ L := pCoreOf_le 2 L
  have hLO : L ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 L
  have hzO : Subgroup.zpowers b ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.zpowers_le).mpr (hLO hb)
  set N := Subgroup.zpowers b ⊔ O with hNdef
  have hNL : N ≤ L := sup_le ((Subgroup.zpowers_le).mpr hb) hOL
  have hN2 : IsPGroup 2 ↥N := by
    obtain ⟨k, hk⟩ := hb2
    rintro ⟨g, hg⟩
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzO] at hg
    obtain ⟨a, ⟨i, rfl⟩, q, hq, rfl⟩ := Set.mem_mul.mp hg
    have h1 := C22Pf.pow_mem_of_mul (hzO ⟨i, rfl⟩) hq (2 ^ k)
    have h2 : (b ^ i) ^ 2 ^ k ∈ O := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      exact O.zpow_mem hk i
    have h3 : (b ^ i * q) ^ 2 ^ k ∈ O := by
      have e : (b ^ i * q) ^ 2 ^ k =
          (b ^ i) ^ 2 ^ k * (((b ^ i) ^ 2 ^ k)⁻¹ * (b ^ i * q) ^ 2 ^ k) := by group
      rw [e]
      exact O.mul_mem h2 h1
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 L) ⟨_, h3⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val hm
  have hLN : L ≤ Subgroup.normalizer (N : Set G) := by
    intro l hl
    refine C22Pf.mem_normalizer_of_conj_mem fun n hn => ?_
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzO] at hn
    obtain ⟨a, ⟨i, rfl⟩, q, hq, rfl⟩ := Set.mem_mul.mp hn
    have hlb : l * b * l⁻¹ ∈ N := by
      have e : l * b * l⁻¹ = (l * b * l⁻¹ * b⁻¹) * b := by group
      rw [e]
      refine N.mul_mem (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
      have := O.inv_mem (hc l hl)
      simpa [mul_assoc] using this
    have hlbi : l * b ^ i * l⁻¹ ∈ N := by
      have e : l * b ^ i * l⁻¹ = (l * b * l⁻¹) ^ i := by
        rw [conj_zpow]
      rw [e]
      exact N.zpow_mem hlb i
    have e : l * (b ^ i * q) * l⁻¹ = (l * b ^ i * l⁻¹) * (l * q * l⁻¹) := by group
    rw [e]
    exact N.mul_mem hlbi (Subgroup.mem_sup_right
      ((Subgroup.mem_normalizer_iff.mp (hLO hl) q).mp hq))
  have hNO : N ≤ O := le_pCoreOf_of_le_normalizer 2 hNL hLN hN2
  exact hNO (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))


theorem le_conjClosure_of_moved {H R M L : Subgroup G} (hyp : HypC23 H R M) (hL : L ∈ cComp H)
    {ρ : G} (hρR : ρ ∈ R) (hc : ⁅L, conjByElt ρ L⁆ ≤ pCoreOf 2 H) (hLM : L ≤ M) :
    L ≤ conjClosure R M := by
  set W := conjClosure R M with hW
  have hRW : R ≤ W := le_conjClosure R M
  have hQW : pCoreOf 2 H ≤ W := (c2_1_pCore_le hyp.radical).trans hRW
  have hMW : M ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure R M
  have hLH : L ≤ H := le_of_mem_cComp hL
  rw [← perfect_of_mem_cComp hL, Subgroup.commutator_le]
  intro a ha l hl
  have hd : l * ρ * l⁻¹ * ρ⁻¹ ∈ W :=
    W.mul_mem (mem_conjClosure (hLM hl) hρR) (W.inv_mem (hRW hρR))
  have hy : ρ * l⁻¹ * ρ⁻¹ ∈ conjByElt ρ L := by
    rw [mem_conjByElt]
    simpa [mul_assoc] using L.inv_mem hl
  have h1 : a * (l * ρ * l⁻¹ * ρ⁻¹) * a⁻¹ * (l * ρ * l⁻¹ * ρ⁻¹)⁻¹ ∈ W :=
    W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMW (hLM ha)) _).mp hd) (W.inv_mem hd)
  have h2 : a * (ρ * l⁻¹ * ρ⁻¹) * a⁻¹ * (ρ * l⁻¹ * ρ⁻¹)⁻¹ ∈ pCoreOf 2 H :=
    hc (Subgroup.commutator_mem_commutator ha hy)
  have h3 : l * (a * (ρ * l⁻¹ * ρ⁻¹) * a⁻¹ * (ρ * l⁻¹ * ρ⁻¹)⁻¹) * l⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hLH hl)) _).mp h2
  have e : ⁅a, l⁆ = (a * (l * ρ * l⁻¹ * ρ⁻¹) * a⁻¹ * (l * ρ * l⁻¹ * ρ⁻¹)⁻¹) *
      (l * (a * (ρ * l⁻¹ * ρ⁻¹) * a⁻¹ * (ρ * l⁻¹ * ρ⁻¹)⁻¹) * l⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact W.mul_mem h1 (W.inv_mem (hQW h3))

theorem asc24TwoChar_of (h82 : Asc82Thm2)
    (hA37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) : ASC24TwoChar G := by
  intro H R M L hyp hHc hL hLc hLq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hns, hRN⟩ := hcon
  have hR := hyp.radical
  have hRH : R ≤ H := hR.1
  have hR2 : IsPGroup 2 ↥R := hR.isPGroup
  have hLH : L ≤ H := le_of_mem_cComp hL
  set Q := pCoreOf 2 H with hQdef
  have hQR : Q ≤ R := c2_1_pCore_le hR
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hRM : R ≤ M := fun x hx =>
    hyp.cgs (inf_normalizer_le_cgsIn hR.2.1 ⟨hRH hx, Subgroup.le_normalizer hx⟩)
  set W := conjClosure R M with hW
  have hRW : R ≤ W := le_conjClosure R M
  have hMW : M ≤ Subgroup.normalizer (W : Set G) := le_normalizer_conjClosure R M
  have hWH : W ≤ H := conjClosure_le fun m hm r hr =>
    H.mul_mem (H.mul_mem (hyp.le hm) (hRH hr)) (H.inv_mem (hyp.le hm))
  obtain ⟨ρ, hρR, hρN⟩ := IsConcreteLE.not_le_iff_exists.mp hRN
  obtain ⟨T, hT, hRT⟩ := EscapingLocal.exists_isSylowTwoOf_ge hRH hR2
  obtain ⟨hHT, hcase⟩ := a3Orbits_of_a37_a38 (G := G) hA37 hA38 H T L hyp.sqtk hT hL
  rcases hcase with hTN | ⟨t, -, -, hTL, hcomm, hint, -⟩
  · exact hρN (hTN ρ (hRT hρR))
  set L' := conjByElt ρ L with hL'def
  have hρne : L' ≠ L := fun he => hρN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
  have hmemH : ∀ σ ∈ H, conjByElt σ L = L ∨ conjByElt σ L = conjByElt t L := fun σ hσ => by
    have h1 : conjByElt σ L ∈ conjSubgroupsBy H L := ⟨σ, hσ, rfl⟩
    rw [hHT, hTL] at h1
    exact h1
  have hρt : L' = conjByElt t L := (hmemH ρ (hRH hρR)).resolve_left hρne
  have hmem : ∀ σ ∈ H, conjByElt σ L = L ∨ conjByElt σ L = L' := fun σ hσ =>
    (hmemH σ hσ).imp id fun h => h.trans hρt.symm
  have hc : ⁅L, L'⁆ ≤ Q := hρt ▸ hcomm
  have hint' : (L ⊔ Q) ⊓ (L' ⊔ Q) = Q := hρt ▸ hint
  have hL'c : L' ∈ cComp H := by
    have h1 := cComp_map_mulEquiv (MulAut.conj ρ) hL
    have h2 : H.map (MulAut.conj ρ).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hRH hρR))
    rwa [h2] at h1
  have hL'H : L' ≤ H := le_of_mem_cComp hL'c
  have hN1 : L' ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_commutator_le hL hc
  have hN2 : L ≤ Subgroup.normalizer (L' : Set G) :=
    le_normalizer_of_commutator_le hL'c (by rw [Subgroup.commutator_comm]; exact hc)
  have hconj' : ∀ σ ∈ H, conjByElt σ L' = L ∨ conjByElt σ L' = L' := fun σ hσ => by
    have e : conjByElt σ L' = conjByElt (σ * ρ) L := C22Pf.map_conj_map_conj L ρ σ
    rw [e]
    exact hmem _ (H.mul_mem hσ (hRH hρR))
  have hinj : ∀ σ : G, conjByElt σ L ≠ conjByElt σ L' := by
    intro σ he
    apply hρne
    have := congrArg (conjByElt σ⁻¹) he
    rw [conjByElt_inv_conjByElt, conjByElt_inv_conjByElt] at this
    exact this.symm
  set X := L ⊔ L' with hXdef
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    intro σ hσ
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (L ⊔ L').map (MulAut.conj σ).toMonoidHom = L ⊔ L'
    rw [Subgroup.map_sup]
    change conjByElt σ L ⊔ conjByElt σ L' = L ⊔ L'
    rcases hmem σ hσ with h1 | h1 <;> rcases hconj' σ hσ with h2 | h2
    · exact absurd (h1.trans h2.symm) (hinj σ)
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
    · exact absurd (h1.trans h2.symm) (hinj σ)
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hN1
  set RL := R ⊓ Subgroup.normalizer (L : Set G) with hRLdef
  have hRL2 : IsPGroup 2 ↥RL := hR2.to_le inf_le_left
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := P134.pCoreOf_le_normalizer_of_mem_cComp hL
  have hQRL : Q ≤ RL := le_inf hQR hQN
  have hRLL' : RL ≤ Subgroup.normalizer (L' : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjByElt r L' = L'
    rcases hconj' r (hRH hr.1) with h | h
    · exact absurd ((Subgroup.mem_normalizer_iff_map_conj_eq.mp hr.2).trans h.symm) (hinj r)
    · exact h
  have hRRL : R ≤ Subgroup.normalizer (RL : Set G) := by
    intro r hr
    refine C22Pf.mem_normalizer_of_conj_mem fun x hx =>
      ⟨R.mul_mem (R.mul_mem hr hx.1) (R.inv_mem hr), ?_⟩
    show r * x * r⁻¹ ∈ Subgroup.normalizer (L : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjByElt (r * x * r⁻¹) L = L
    have hK : conjByElt x (conjByElt r⁻¹ L) = conjByElt r⁻¹ L := by
      rcases hmem r⁻¹ (H.inv_mem (hRH hr)) with h | h
      · rw [h]; exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hx.2
      · rw [h]; exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRLL' hx)
    have e1 : conjByElt (r * x * r⁻¹) L = conjByElt r (conjByElt x (conjByElt r⁻¹ L)) := by
      simp only [conjByElt]
      rw [C22Pf.map_conj_map_conj, C22Pf.map_conj_map_conj, mul_assoc]
    rw [e1, hK]
    have := conjByElt_inv_conjByElt r⁻¹ L
    rwa [inv_inv] at this
  have hLM : ¬ L ≤ M := by
    intro hLM
    apply hns
    have hLW : L ≤ W := le_conjClosure_of_moved hyp hL hρR hc hLM
    have hsub : IsSubnormal L W := by
      have h1 := B113.isSubnormal_inf_of_le (subnormal_of_mem_cComp hL) hWH
      rwa [inf_eq_right.mpr hLW] at h1
    exact C2Push.isSylowTwoOf_inf_of_isSubnormal hsub hyp.sylow
  set V := omegaOneCenterOf Q with hVdef
  set Z := omegaOneCenterOf R with hZdef
  have hZV : Z ≤ V := by
    refine (Subgroup.closure_le _).mpr fun z hz => ?_
    have hzR : z ∈ R := hz.1.1
    have hzC : z ∈ Subgroup.centralizer (R : Set G) := hz.1.2
    have hzCQ : z ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQR) hzC
    have hzQ : z ∈ Q := hHc ⟨hRH hzR, hzCQ⟩
    exact Subgroup.subset_closure ⟨⟨hzQ, hzCQ⟩, hz.2⟩
  have hZne : Z ≠ ⊥ := quasithinOmegaOneCenter_ne_bot hR2 hR.2.1
  have hZchar : (Z.subgroupOf R).Characteristic :=
    CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf R
  have hLV : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hLV
    apply hLM
    intro l hl
    have hlZ : l ∈ Subgroup.normalizer (Z : Set G) := by
      have hlC : l ∈ Subgroup.centralizer (Z : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZV) (hLV hl)
      refine Subgroup.mem_normalizer_iff.mpr fun z => ⟨fun hz => ?_, fun hz => ?_⟩
      · have h := Subgroup.mem_centralizer_iff.mp hlC z hz
        rw [← h, mul_inv_cancel_right]
        exact hz
      · have h := Subgroup.mem_centralizer_iff.mp hlC _ hz
        have e : z = l * z * l⁻¹ := by
          calc z = l⁻¹ * ((l * z * l⁻¹) * l) := by group
            _ = l⁻¹ * (l * (l * z * l⁻¹)) := by rw [h]
            _ = l * z * l⁻¹ := by group
        rw [e]
        exact hz
    have hle : H ⊓ Subgroup.normalizer (Z : Set G) ≤ cgsIn H R :=
      le_iSup_of_le Z (le_iSup_of_le (A4.omegaOneCenterOf_le R)
        (le_iSup_of_le hZne (le_iSup_of_le hZchar le_rfl)))
    exact hyp.cgs (hle ⟨hLH hl, hlZ⟩)
  have hJN : thompsonJ R ≤ Subgroup.normalizer (L : Set G) :=
    thompsonJ_le_normalizer h82 hyp.sqtk hRH hQR hL hLq hLV fun r hr hrN => by
      rcases hmem r (hRH hr) with h | h
      · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h) hrN
      · rw [h]
        exact hc
  have hJRL : thompsonJ R ≤ RL := le_inf (B6.thompsonJ_le R) hJN
  have hJeq : thompsonJ RL = thompsonJ R := B6.thompsonJ_eq_of_le hJRL inf_le_left
  have hJne : thompsonJ R ≠ ⊥ := by
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian R
    intro hbot
    have hAb : A = ⊥ := le_bot_iff.mp (hbot ▸ B6.le_thompsonJ hA)
    have hZe : IsElemAbelian 2 Z := B2F.isElemAbelian_omegaOneCenterOf R
    have h1 := hA.2.2 Z (A4.omegaOneCenterOf_le R) hZe
    rw [hAb, Subgroup.card_bot] at h1
    exact hZne (Subgroup.eq_bot_of_card_le Z h1)
  have hJchar : ((thompsonJ R).subgroupOf R).Characteristic :=
    CFSG.QuasithinUnique.Setup.characteristic_thompsonJ R
  have hYM : (L ⊔ RL) ⊓ Subgroup.normalizer (RL : Set G) ≤ M := by
    intro y hy
    have hyJ : y ∈ Subgroup.normalizer (thompsonJ R : Set G) := by
      rw [← hJeq, Subgroup.mem_normalizer_iff_map_conj_eq]
      have e : B6.conjSub y RL = RL := B6.conjSub_eq_self hy.2
      have h1 := B6.thompsonJ_conjSub RL y
      rw [e] at h1
      exact h1.symm
    have hyH : y ∈ H := sup_le hLH (inf_le_left.trans hRH) hy.1
    have hle : H ⊓ Subgroup.normalizer (thompsonJ R : Set G) ≤ cgsIn H R :=
      le_iSup_of_le (thompsonJ R) (le_iSup_of_le (B6.thompsonJ_le R)
        (le_iSup_of_le hJne (le_iSup_of_le hJchar le_rfl)))
    exact hyp.cgs (hle ⟨hyH, hyJ⟩)
  obtain ⟨T₁, hT₁, hRLT₁⟩ := EscapingLocal.exists_isSylowTwoOf_ge (le_sup_right : RL ≤ L ⊔ RL)
    hRL2
  have hlt : RL < T₁ := by
    refine lt_of_le_of_ne hRLT₁ fun he => hns ?_
    have hsyl : IsSylowTwoOf RL (L ⊔ RL) := he ▸ hT₁
    have h1 := A4.isSylowTwoOf_inf_normal hsyl le_sup_left
      (sup_le Subgroup.le_normalizer inf_le_right)
    have e : RL ⊓ L = R ⊓ L := by
      rw [hRLdef, inf_assoc, inf_eq_right.mpr Subgroup.le_normalizer]
    rwa [e] at h1
  obtain ⟨y, hyT₁, hyN, hyRL⟩ := A4.exists_mem_normalizer_not_mem hT₁.2.1 hlt
  have hyY : y ∈ (L ⊔ RL) ⊓ Subgroup.normalizer (RL : Set G) := ⟨hT₁.1 hyT₁, hyN⟩
  have hyM : y ∈ M := hYM hyY
  obtain ⟨k, hk⟩ := C1.exists_pow_eq_one_of_isPGroup hT₁.2.1 hyT₁
  have hyLR : y ∈ ((RL : Set G) * (L : Set G)) := by
    have h1 : y ∈ RL ⊔ L := by
      rw [sup_comm]
      exact hT₁.1 hyT₁
    rwa [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right RL L inf_le_right] at h1
  obtain ⟨r, hr, u, hu, hru⟩ := Set.mem_mul.mp hyLR
  set NR := Subgroup.normalizer (RL : Set G) with hNR
  have huN : u ∈ NR := by
    have e : u = r⁻¹ * y := by rw [← hru]; group
    rw [e]
    exact NR.mul_mem (NR.inv_mem (Subgroup.le_normalizer hr)) hyN
  have hρN' : ρ ∈ NR := hRRL hρR
  set v := ρ * u⁻¹ * ρ⁻¹ with hvdef
  have hvL' : v ∈ L' := by
    rw [hL'def, mem_conjByElt]
    simpa [v, mul_assoc] using L.inv_mem hu
  have hvN : v ∈ NR := NR.mul_mem (NR.mul_mem hρN' (NR.inv_mem huN)) (NR.inv_mem hρN')
  set c := y * ρ * y⁻¹ * ρ⁻¹ with hcdef
  have hr' : ρ * r⁻¹ * ρ⁻¹ ∈ RL := (Subgroup.mem_normalizer_iff.mp hρN' _).mp (RL.inv_mem hr)
  have hce : c = r * (u * v) * (ρ * r⁻¹ * ρ⁻¹) := by
    rw [hcdef, hvdef, ← hru]
    group
  have hcW : c ∈ W := W.mul_mem (mem_conjClosure hyM hρR) (W.inv_mem (hRW hρR))
  have hcN : c ∈ NR :=
    NR.mul_mem (NR.mul_mem (NR.mul_mem hyN hρN') (NR.inv_mem hyN)) (NR.inv_mem hρN')
  have huv : u * v * u⁻¹ * v⁻¹ ∈ RL := hQRL (hc (Subgroup.commutator_mem_commutator hu hvL'))
  have hu2 : u ^ 2 ^ k ∈ RL := by
    have h1 := C22Pf.pow_mem_of_mul hyN (show y⁻¹ * r⁻¹ * y ∈ RL from by
      have := (Subgroup.mem_normalizer_iff.mp (NR.inv_mem hyN) _).mp (RL.inv_mem hr)
      simpa [mul_assoc] using this) (2 ^ k)
    have e : y * (y⁻¹ * r⁻¹ * y) = u := by rw [← hru]; group
    rw [e, hk, inv_one, one_mul] at h1
    exact h1
  have hv2 : v ^ 2 ^ k ∈ RL := by
    have e : v ^ 2 ^ k = ρ * (u ^ 2 ^ k)⁻¹ * ρ⁻¹ := by
      rw [hvdef, conj_pow, inv_pow]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hρN' _).mp (RL.inv_mem hu2)
  have huv2 : (u * v) ^ 2 ^ k ∈ RL := by
    have h1 := pow_mul_mem huN hvN huv (2 ^ k)
    have e : (u * v) ^ 2 ^ k = (u ^ 2 ^ k * v ^ 2 ^ k) *
        ((u ^ 2 ^ k * v ^ 2 ^ k)⁻¹ * (u * v) ^ 2 ^ k) := by group
    rw [e]
    exact RL.mul_mem (RL.mul_mem hu2 hv2) h1
  have huvN : u * v ∈ NR := NR.mul_mem huN hvN
  have hc2 : ∃ j : ℕ, c ^ 2 ^ j = 1 := by
    have hn : (u * v)⁻¹ * r * (u * v) * (ρ * r⁻¹ * ρ⁻¹) ∈ RL := by
      refine RL.mul_mem ?_ hr'
      have := (Subgroup.mem_normalizer_iff.mp (NR.inv_mem huvN) _).mp hr
      simpa [mul_assoc] using this
    have h1 := C22Pf.pow_mem_of_mul huvN hn (2 ^ k)
    have e : (u * v) * ((u * v)⁻¹ * r * (u * v) * (ρ * r⁻¹ * ρ⁻¹)) = c := by
      rw [hce]; group
    rw [e] at h1
    have h2 : c ^ 2 ^ k ∈ RL := by
      have e2 : c ^ 2 ^ k = (u * v) ^ 2 ^ k * (((u * v) ^ 2 ^ k)⁻¹ * c ^ 2 ^ k) := by group
      rw [e2]
      exact RL.mul_mem huv2 h1
    obtain ⟨m, hm⟩ := C1.exists_pow_eq_one_of_isPGroup hRL2 h2
    exact ⟨k + m, by rw [pow_add, pow_mul, hm]⟩
  have hWXW : W ≤ Subgroup.normalizer ((X ⊓ W : Subgroup G) : Set G) := fun w hw =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHX (hWH hw), Subgroup.le_normalizer hw⟩
  have hsylXW : IsSylowTwoOf (R ⊓ (X ⊓ W)) (X ⊓ W) :=
    A4.isSylowTwoOf_inf_normal hyp.sylow inf_le_right hWXW
  have he' : RL ⊓ (X ⊓ W) = R ⊓ (X ⊓ W) := by
    refine le_antisymm (inf_le_inf_right _ inf_le_left) fun x hx => ⟨⟨hx.1, hXN hx.2.1⟩, hx.2⟩
  have hRLXW : RL ≤ Subgroup.normalizer ((X ⊓ W : Subgroup G) : Set G) := fun x hx =>
    hWXW (hRW hx.1)
  have hsylK : IsSylowTwoOf RL ((X ⊓ W) ⊔ RL) :=
    isSylowTwoOf_sup hRL2 hRLXW (he' ▸ hsylXW)
  have hcK : c ∈ (X ⊓ W) ⊔ RL := by
    have huvX : u * v ∈ X := X.mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hvL')
    have hx : r * (u * v) * r⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hHX (hRH hr.1)) _).mp huvX
    have hrr : r * (ρ * r⁻¹ * ρ⁻¹) ∈ RL := RL.mul_mem hr hr'
    have e : c = (r * (u * v) * r⁻¹) * (r * (ρ * r⁻¹ * ρ⁻¹)) := by rw [hce]; group
    have hxW : r * (u * v) * r⁻¹ ∈ W := by
      have e2 : r * (u * v) * r⁻¹ = c * (r * (ρ * r⁻¹ * ρ⁻¹))⁻¹ := by rw [e]; group
      rw [e2]
      exact W.mul_mem hcW (W.inv_mem (hRW hrr.1))
    rw [e]
    exact Subgroup.mul_mem_sup ⟨hx, hxW⟩ hrr
  have hcRL : c ∈ RL := mem_of_mem_normalizer_of_isSylowTwoOf hsylK hcK hcN hc2
  have huvRL : u * v ∈ RL := by
    have e : u * v = r⁻¹ * c * (ρ * r⁻¹ * ρ⁻¹)⁻¹ := by rw [hce]; group
    rw [e]
    exact RL.mul_mem (RL.mul_mem (RL.inv_mem hr) hcRL) (RL.inv_mem hr')
  set Ob := pCoreOf 2 L with hOb
  have hOL : Ob ≤ Q := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hL)
  have hvC : v ∈ centralizerSection H L Ob := by
    refine ⟨hL'H hvL', hN1 hvL', normalizer_le_normalizer_pCoreOf 2 L (hN1 hvL'), fun x hx => ?_⟩
    have h1 : x * v * x⁻¹ * v⁻¹ ∈ L := by
      have h2 : v * x⁻¹ * v⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hN1 hvL') _).mp (L.inv_mem hx)
      have e : x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) := by group
      rw [e]
      exact L.mul_mem hx h2
    exact inf_pCoreOf_le hLH ⟨h1, hc (Subgroup.commutator_mem_commutator hx hvL')⟩
  have hmem1 : u * v ∈ (R : Set G) ∩ ((L : Set G) * (centralizerSection H L Ob : Set G)) :=
    ⟨huvRL.1, Set.mem_mul.mpr ⟨u, hu, v, hvC, rfl⟩⟩
  rw [C22Pf.asc22One_of hA37 H R L hyp.sqtk hR hL] at hmem1
  obtain ⟨a, ha, c₀, hc₀, hac⟩ := Set.mem_mul.mp hmem1
  set b := a⁻¹ * u with hbdef
  have hbL : b ∈ L := L.mul_mem (L.inv_mem ha.2) hu
  have hc₀e : c₀ = b * v := by
    have e : c₀ = a⁻¹ * (a * c₀) := by group
    rw [e, hac, hbdef, mul_assoc]
  have hbC : b ∈ centralizerSection H L Ob := by
    have h1 : c₀ ∈ centralizerSection H L Ob := centralizerSection_mono hRH _ _ hc₀
    have e : b = c₀ * v⁻¹ := by rw [hc₀e]; group
    rw [e]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hvC)
  have hbcomm : ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ Ob := by
    intro l hl
    have h1 := hbC.2.2.2 l hl
    have e : b * l * b⁻¹ * l⁻¹ = (l * b * l⁻¹ * b⁻¹)⁻¹ := by group
    rw [e]
    exact Ob.inv_mem h1
  have hb2 : ∃ j : ℕ, b ^ 2 ^ j ∈ Ob := by
    obtain ⟨j, hj⟩ := C1.exists_pow_eq_one_of_isPGroup hR2 hc₀.1
    have hbN : b ∈ Subgroup.normalizer (Q : Set G) := hHQ (hLH hbL)
    have hvNQ : v ∈ Subgroup.normalizer (Q : Set G) := hHQ (hL'H hvL')
    have hbv : b * v * b⁻¹ * v⁻¹ ∈ Q := hc (Subgroup.commutator_mem_commutator hbL hvL')
    have h1 := pow_mul_mem hbN hvNQ hbv (2 ^ j)
    rw [← hc₀e, hj, mul_one] at h1
    have h2 : b ^ 2 ^ j * v ^ 2 ^ j ∈ Q := by simpa using Q.inv_mem h1
    have h3 : b ^ 2 ^ j ∈ (L ⊔ Q) ⊓ (L' ⊔ Q) := by
      refine ⟨Subgroup.mem_sup_left (L.pow_mem hbL _), ?_⟩
      have e : b ^ 2 ^ j = (b ^ 2 ^ j * v ^ 2 ^ j) * (v ^ 2 ^ j)⁻¹ := by group
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup h2 (L'.inv_mem (L'.pow_mem hvL' _))
    rw [hint'] at h3
    exact ⟨j, inf_pCoreOf_le hLH ⟨L.pow_mem hbL _, h3⟩⟩
  have hbO := mem_pCoreOf_of_commute hbL hbcomm hb2
  have huR : u ∈ R := by
    have e : u = a * b := by rw [hbdef]; group
    rw [e]
    exact R.mul_mem ha.1 (hQR (hOL hbO))
  exact hyRL (by
    rw [← hru]
    exact RL.mul_mem hr ⟨huR, Subgroup.le_normalizer hu⟩)

end C24Pf

end CFSG.Quasithin
