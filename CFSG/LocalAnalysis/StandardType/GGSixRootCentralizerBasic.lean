module

public import CFSG.LocalAnalysis.StandardType.GGSixFusion
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type*} [Group G]

namespace GGControlsStrongFusion

theorem of_le {H E : Subgroup G} (h : GGControlsStrongFusion H E) {E' : Subgroup G}
    (hE' : E' ≤ E) : GGControlsStrongFusion H E' := by
  rw [ggControlsStrongFusion_iff] at h ⊢
  exact ⟨hE'.trans h.1, fun e he he1 g hg => h.2 e (hE' he) he1 g hg⟩

theorem conj_zpowers {H : Subgroup G} {f m : G} (h : GGControlsStrongFusion H (Subgroup.zpowers f))
    (hm : m ∈ H) : GGControlsStrongFusion H (Subgroup.zpowers (m * f * m⁻¹)) := by
  rw [ggControlsStrongFusion_iff] at h ⊢
  refine ⟨Subgroup.zpowers_le.mpr ?_, fun y hy hy1 g hg => ?_⟩
  · exact H.mul_mem (H.mul_mem hm (h.1 (Subgroup.mem_zpowers f))) (H.inv_mem hm)
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk : (m * f * m⁻¹) ^ k = m * f ^ k * m⁻¹ := by
      have := map_zpow (MulAut.conj m) f k
      simpa only [MulAut.conj_apply] using this.symm
    have hfk : f ^ k ≠ 1 := by
      intro h1
      apply hy1
      rw [hk, h1, mul_one, mul_inv_cancel]
    have hg' : (m⁻¹ * g)⁻¹ * f ^ k * (m⁻¹ * g) ∈ H := by
      have : (m⁻¹ * g)⁻¹ * f ^ k * (m⁻¹ * g) = g⁻¹ * (m * f * m⁻¹) ^ k * g := by
        rw [hk]; group
      rw [this]
      exact hg
    have := H.mul_mem hm (h.2 (f ^ k) (Subgroup.zpow_mem_zpowers f k) hfk (m⁻¹ * g) hg')
    simpa using this

end GGControlsStrongFusion

theorem ggControlsStrongFusion_of_forall_zpowers {H E : Subgroup G} (hEH : E ≤ H)
    (h : ∀ f ∈ E, f ≠ 1 → GGControlsStrongFusion H (Subgroup.zpowers f)) :
    GGControlsStrongFusion H E := by
  rw [ggControlsStrongFusion_iff]
  exact ⟨hEH, fun f hf hf1 g hg =>
    (h f hf hf1).mem_of_conj_mem (Subgroup.mem_zpowers f) hf1 hg⟩

theorem ggNormalizer_zpowers_eq_centralizer {r : G} (hr : orderOf r = 2) :
    Subgroup.normalizer (Subgroup.zpowers r : Set G) = Subgroup.centralizer {r} := by
  have hr2 : r ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hr, pow_orderOf_eq_one]
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * r * g⁻¹ ∈ Subgroup.zpowers r :=
      (Subgroup.mem_normalizer_iff.mp hg r).mp (Subgroup.mem_zpowers r)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [zpow_eq_zpow_emod k hr2] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · rw [h0, zpow_zero] at hk
      have hr1 : r = 1 := by
        have h' := congrArg (fun y => g⁻¹ * y * g) hk
        simp only [mul_one, inv_mul_cancel] at h'
        rw [h']
        group
      rw [hr1, orderOf_one] at hr
      exact absurd hr (by norm_num)
    · rw [h0, zpow_one] at hk
      calc g * r = g * r * g⁻¹ * g := by group
        _ = r * g := by rw [← hk]
  · intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    have hc : ∀ k : ℤ, g * r ^ k * g⁻¹ = r ^ k := by
      intro k
      have hcomm : Commute g (r ^ k) := Commute.zpow_right hg k
      rw [hcomm.eq, mul_inv_cancel_right]
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hc k]
      exact Subgroup.zpow_mem_zpowers r k
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : Commute g (r ^ k) := Commute.zpow_right hg k
      have : y = r ^ k := by
        calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
          _ = g⁻¹ * (r ^ k * g) := by rw [← hk, mul_assoc]
          _ = r ^ k := by rw [← hcomm.eq]; group
      rw [this]
      exact Subgroup.zpow_mem_zpowers r k

theorem ggIsTwoLocal_centralizer {r : G} (hr : orderOf r = 2) :
    IsTwoLocal (Subgroup.centralizer {r}) := by
  refine ⟨Subgroup.zpowers r, ?_, ?_, (ggNormalizer_zpowers_eq_centralizer hr).symm⟩
  · intro h
    have h1 : r = 1 := by
      have := Subgroup.mem_zpowers r
      rw [h, Subgroup.mem_bot] at this
      exact this
    rw [h1, orderOf_one] at hr
    exact absurd hr (by norm_num)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr, pow_one])

theorem ggMem_normalizer_pCoreOf {p : ℕ} {H : Subgroup G} {n : G} (hn : n ∈ H) :
    n ∈ Subgroup.normalizer (pCoreOf p H : Set G) := by
  have key : ∀ m ∈ H, ∀ h ∈ pCoreOf p H, m * h * m⁻¹ ∈ pCoreOf p H := by
    intro m hm h hh
    obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨⟨m, hm⟩ * h' * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    exact (Dichotomy.CentralizerContainment.pCore_normal_assembly p H).conj_mem h' hh' _
  refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨key n hn h, fun hh => ?_⟩
  have := key n⁻¹ (H.inv_mem hn) _ hh
  simpa [mul_assoc] using this

theorem ggIsPGroup_pCoreOf (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) :=
  (Dichotomy.CentralizerContainment.pCore_isPGroup_assembly p H).map H.subtype

theorem ggNot_dvd_card_of_isPGroup_two [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup 2 P) : ¬ p ∣ Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem ggLe_of_plane_centralizers [Finite G] {p : ℕ} (hp : p.Prime) {E P M : Subgroup G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEP : E ≤ Subgroup.normalizer (P : Set G)) (hcop : ¬ p ∣ Nat.card P)
    (hC : ∀ e ∈ E, e ≠ 1 → P ⊓ Subgroup.centralizer {e} ≤ M) : P ≤ M := by
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p hp E P
    (fun e => Subtype.ext (by simpa using hE.2 e e.2)) hEcard hcop hEP]
  exact iSup_le fun e => iSup_le fun he => hC e e.2 fun h => he (Subtype.ext h)

theorem ggPCoreOf_centralizer_le [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E M : Subgroup G} {r : G} (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hfus : GGControlsStrongFusion M E) (hEr : E ≤ Subgroup.centralizer {r}) :
    pCoreOf 2 (Subgroup.centralizer {r}) ≤ M :=
  ggLe_of_plane_centralizers hp hE hEcard (fun _ he => ggMem_normalizer_pCoreOf (hEr he))
    (ggNot_dvd_card_of_isPGroup_two hp hp2 (ggIsPGroup_pCoreOf 2 _))
    fun _ he he1 => inf_le_right.trans (hfus.centralizer_le he he1)

theorem ggPCoreOf_le_pCoreOf_of_le {p : ℕ} {N V : Subgroup G} (hVN : V ≤ N)
    (hPV : pCoreOf p N ≤ V) : pCoreOf p N ≤ pCoreOf p V := by
  have hnorm : ((pCoreOf p N).subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPV).mpr fun _ hv =>
      ggMem_normalizer_pCoreOf (hVN hv)
  have hpg : IsPGroup p ((pCoreOf p N).subgroupOf V) :=
    (ggIsPGroup_pCoreOf p N).comap_of_injective V.subtype Subtype.coe_injective
  have hle := Dichotomy.CentralizerContainment.le_pCore_assembly hnorm hpg
  intro x hx
  exact ⟨⟨x, hPV hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem ggPCoreOf_le_pCoreOf_inf {N M : Subgroup G} (hPM : pCoreOf 2 N ≤ M) :
    pCoreOf 2 N ≤ pCoreOf 2 (N ⊓ M) :=
  ggPCoreOf_le_pCoreOf_of_le inf_le_left (le_inf (Subgroup.map_subtype_le _) hPM)

theorem ggInf_centralizer_pCoreOf_le (hchar : IsCharTwoType G) {r : G} (hr : orderOf r = 2) :
    Subgroup.centralizer {r} ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer {r}) : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer {r}) :=
  hchar _ (ggIsTwoLocal_centralizer hr)

theorem ggInf_centralizer_le_pCoreOf (hchar : IsCharTwoType G) {r : G} (hr : orderOf r = 2)
    {Q : Subgroup G} (hQN : Q ≤ Subgroup.centralizer {r})
    (hPQ : pCoreOf 2 (Subgroup.centralizer {r}) ≤ Q) :
    Q ⊓ Subgroup.centralizer (Q : Set G) ≤ pCoreOf 2 (Subgroup.centralizer {r}) := by
  intro z hz
  exact ggInf_centralizer_pCoreOf_le hchar hr
    ⟨hQN hz.1, Subgroup.centralizer_le (fun _ hx => hPQ hx) hz.2⟩

@[expose] def ggOTwoPrime (Y : Subgroup G) : Subgroup G :=
  Subgroup.closure {y | y ∈ Y ∧ ∃ k : ℕ, y ^ (2 ^ k) = 1}

theorem ggOTwoPrime_le (Y : Subgroup G) : ggOTwoPrime Y ≤ Y :=
  (Subgroup.closure_le Y).mpr fun _ hy => hy.1

theorem ggMem_normalizer_oTwoPrime {Y : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (Y : Set G)) :
    c ∈ Subgroup.normalizer (ggOTwoPrime Y : Set G) := by
  have key : ∀ d ∈ Subgroup.normalizer (Y : Set G),
      (ggOTwoPrime Y).map (MulAut.conj d).toMonoidHom ≤ ggOTwoPrime Y := by
    intro d hd
    rw [ggOTwoPrime, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, ⟨hyY, k, hk⟩, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hd y).mp hyY, k, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply le_antisymm (key c hc)
  intro y hy
  have h1 : (MulAut.conj c⁻¹) y ∈ ggOTwoPrime Y :=
    key c⁻¹ (Subgroup.inv_mem _ hc) ⟨y, hy, rfl⟩
  exact ⟨_, h1, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem ggMem_normalizer_oTwoPrime_inf_centralizer {G₀ : Subgroup G} {r c : G}
    (hc : c ∈ Subgroup.normalizer (G₀ : Set G)) (hcr : c ∈ Subgroup.centralizer {r}) :
    c ∈ Subgroup.normalizer (ggOTwoPrime (G₀ ⊓ Subgroup.centralizer {r}) : Set G) :=
  ggMem_normalizer_oTwoPrime
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hc, Subgroup.le_normalizer hcr⟩)

theorem ggNot_isCyclic_of_card_sq {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) : ¬ IsCyclic E := by
  intro hcyc
  have hexp : Monoid.exponent E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun e => Subtype.ext (by simpa using hE.2 e e.2)
  rw [IsCyclic.exponent_eq_card, hEcard] at hexp
  have h1 := Nat.le_of_dvd hp.pos hexp
  have h2 : p < p ^ 2 := by nlinarith [hp.two_le]
  omega

theorem ggIsCyclic_sup_zpowers_quotient {K : Subgroup G} {y : G}
    [(K.subgroupOf (Subgroup.zpowers y ⊔ K)).Normal] :
    IsCyclic (↥(Subgroup.zpowers y ⊔ K) ⧸ K.subgroupOf (Subgroup.zpowers y ⊔ K)) := by
  set W := Subgroup.zpowers y ⊔ K with hW
  let π : W →* W ⧸ K.subgroupOf W := QuotientGroup.mk' _
  let y' : W := ⟨y, le_sup_left (a := Subgroup.zpowers y) (Subgroup.mem_zpowers y)⟩
  set T : Subgroup W := (Subgroup.zpowers (π y')).comap π with hT
  have hle : W ≤ T.map W.subtype := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨y', Subgroup.mem_comap.mpr
      (Subgroup.mem_zpowers _), rfl⟩) fun k hk => ?_
    refine ⟨⟨k, le_sup_right (a := Subgroup.zpowers y) hk⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    have h1 : π ⟨k, le_sup_right (a := Subgroup.zpowers y) hk⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hk)
    rw [h1]
    exact Subgroup.one_mem _
  refine ⟨⟨π y', fun q => ?_⟩⟩
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf W) q
  obtain ⟨t, ht, htw⟩ := hle w.2
  have : t = w := Subtype.ext htw
  rw [← this]
  exact ht

theorem ggExists_mem_inf_of_le_sup_zpowers {p : ℕ} (hp : p.Prime) {E K : Subgroup G} {y : G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (hEK : E ≤ Subgroup.zpowers y ⊔ K) :
    ∃ e ∈ E, e ≠ 1 ∧ e ∈ K := by
  by_contra hcon
  push Not at hcon
  set W := Subgroup.zpowers y ⊔ K with hW
  have hKW : K ≤ W := le_sup_right
  have hWN : W ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hy) Subgroup.le_normalizer
  have : (K.subgroupOf W).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKW).mpr hWN
  have := ggIsCyclic_sup_zpowers_quotient (K := K) (y := y)
  let φ : E →* W ⧸ K.subgroupOf W := (QuotientGroup.mk' _).comp (Subgroup.inclusion hEK)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hmem : Subgroup.inclusion hEK e ∈ K.subgroupOf W := (QuotientGroup.eq_one_iff _).mp he
    have heK : (e : G) ∈ K := Subgroup.mem_subgroupOf.mp hmem
    by_contra he1
    exact hcon e e.2 (fun h => he1 (Subtype.ext h)) heK
  exact ggNot_isCyclic_of_card_sq hp hE hEcard (isCyclic_of_injective φ hinj)

theorem ggIsSubnormal_comap {H : Type*} [Group H] (φ : G →* H) {A B : Subgroup H}
    (h : IsSubnormal A B) : IsSubnormal (A.comap φ) (B.comap φ) :=
  h.comap φ

theorem ggIsSubnormal_map {H : Type*} [Group H] (φ : G →* H) {A B : Subgroup G}
    (h : IsSubnormal A B) : IsSubnormal (A.map φ) (B.map φ) :=
  h.map φ

theorem ggControlsStrongFusion_quotient {H E N : Subgroup G} (h : GGControlsStrongFusion H E)
    (K : Subgroup N) [K.Normal] (hK : K ≤ H.subgroupOf N) :
    GGControlsStrongFusion ((H.subgroupOf N).map (QuotientGroup.mk' K))
      ((E.subgroupOf N).map (QuotientGroup.mk' K)) := by
  rw [ggControlsStrongFusion_iff]
  refine ⟨Subgroup.map_mono fun e he => h.1 he, ?_⟩
  intro _ hē hē1 q hq
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hē
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective K q
  obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.mp hq
  have h2 : (QuotientGroup.mk' K) v = (QuotientGroup.mk' K) (n⁻¹ * e * n) := by
    rw [hveq, map_mul, map_mul, map_inv]
  have hk : v⁻¹ * (n⁻¹ * e * n) ∈ K := QuotientGroup.eq.mp h2
  have hvH : (v : G) ∈ H := Subgroup.mem_subgroupOf.mp hv
  have hkH : ((v⁻¹ * (n⁻¹ * e * n) : N) : G) ∈ H := Subgroup.mem_subgroupOf.mp (hK hk)
  have hconj : (n : G)⁻¹ * e * n ∈ H := by
    have := H.mul_mem hvH hkH
    simpa [mul_assoc] using this
  have he1 : (e : G) ≠ 1 := by
    intro h1
    apply hē1
    rw [show e = 1 from Subtype.ext h1, map_one]
  have hnH : (n : G) ∈ H := h.mem_of_conj_mem (Subgroup.mem_subgroupOf.mp he) he1 hconj
  exact Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr hnH, rfl⟩

theorem ggExists_subnormal_of_quotient {N M : Subgroup G} (hPM : pCoreOf 2 N ≤ M)
    (X : Subgroup (↥N ⧸ CFSG.Assembly.pCore 2 ↥N))
    (hXM : X ≤ (M.subgroupOf N).map (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)))
    (hX : IsSubnormal X ⊤) :
    (X.comap (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N))).map N.subtype ≤ M ∧
      IsSubnormal ((X.comap (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N))).map N.subtype) N := by
  constructor
  · rintro _ ⟨n, hn, rfl⟩
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp (hXM (Subgroup.mem_comap.mp hn))
    have hk : m⁻¹ * n ∈ CFSG.Assembly.pCore 2 ↥N := QuotientGroup.eq.mp hmn
    have hkM : ((m⁻¹ * n : N) : G) ∈ M := hPM ⟨m⁻¹ * n, hk, rfl⟩
    have hmM : (m : G) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have := M.mul_mem hmM hkM
    simpa using this
  · have h1 := ggIsSubnormal_map N.subtype (ggIsSubnormal_comap (QuotientGroup.mk' _) hX)
    rwa [Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1

end CFSG.StandardType
