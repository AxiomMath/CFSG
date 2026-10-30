module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddSeitz
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Frame
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

namespace Odd

section Psi

variable {G : Type} [Group G] [Finite G] (L : Subgroup G) [L.Normal] {K : Type} [Group K]
  (φ : ↥L ⧸ Subgroup.center ↥L ≃* K)

@[expose] def psi : G →* MulAut K := (MulAut.congr φ).toMonoidHom.comp (actHom L)

theorem psi_apply_mk (g y : G) (hy : y ∈ L) :
    psi L φ g (φ (QuotientGroup.mk ⟨y, hy⟩)) = φ (actHom L g (QuotientGroup.mk ⟨y, hy⟩)) := by
  change (MulAut.congr φ) (actHom L g) (φ _) = _
  simp [MulAut.congr_apply]

theorem psi_mk_eq_iff (g y : G) (hy : y ∈ L) :
    psi L φ g (φ (QuotientGroup.mk ⟨y, hy⟩)) = φ (QuotientGroup.mk ⟨y, hy⟩) ↔
      g * y * g⁻¹ * y⁻¹ ∈ centerOf L := by
  rw [psi_apply_mk, φ.injective.eq_iff, actHom_mk_eq_iff]

theorem psi_eq_conj {y : G} (hy : y ∈ L) :
    psi L φ y = MulAut.conj (φ (QuotientGroup.mk ⟨y, hy⟩)) := by
  ext k
  obtain ⟨c, rfl⟩ := φ.surjective k
  obtain ⟨⟨y', hy'⟩, rfl⟩ := QuotientGroup.mk_surjective c
  rw [psi_apply_mk, actHom_apply_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem psi_eq_one_of_mem_centerOf {z : G} (hz : z ∈ centerOf L) : psi L φ z = 1 := by
  have hzL := centerOf_le L hz
  rw [psi_eq_conj L φ hzL]
  have : (QuotientGroup.mk ⟨z, hzL⟩ : ↥L ⧸ Subgroup.center ↥L) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ((mem_center_iff_mem_centerOf L _).2 hz)
  rw [this, map_one, map_one]

@[expose] def mImage (M : Subgroup G) : Subgroup K :=
  ((M.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map φ.toMonoidHom

theorem mem_mImage_iff {M : Subgroup G} {y : G} (hy : y ∈ L) :
    φ (QuotientGroup.mk ⟨y, hy⟩) ∈ mImage L φ M ↔ ∃ m ∈ M ⊓ L, ∃ z ∈ centerOf L, y = m * z := by
  constructor
  · intro h1
    obtain ⟨c', ⟨m', hm', rfl⟩, hφ⟩ := Subgroup.mem_map.1 h1
    have hc' : QuotientGroup.mk' (Subgroup.center ↥L) m' = QuotientGroup.mk ⟨y, hy⟩ :=
      φ.injective hφ
    have hz : (m'⁻¹ * ⟨y, hy⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [← QuotientGroup.eq]
      exact hc'
    refine ⟨m', ⟨hm', m'.2⟩, ((m'⁻¹ * ⟨y, hy⟩ : ↥L) : G),
      (mem_center_iff_mem_centerOf L _).1 hz, ?_⟩
    change y = (m' : G) * ((m'⁻¹ : ↥L) * ⟨y, hy⟩ : ↥L)
    simp
  · rintro ⟨m, hm, z, hz, hyz⟩
    refine ⟨QuotientGroup.mk ⟨m, hm.2⟩, ⟨⟨m, hm.2⟩, hm.1, rfl⟩, ?_⟩
    change φ (QuotientGroup.mk ⟨m, hm.2⟩) = φ (QuotientGroup.mk ⟨y, hy⟩)
    rw [φ.injective.eq_iff, QuotientGroup.eq, mem_center_iff_mem_centerOf]
    have : (((⟨m, hm.2⟩ : ↥L)⁻¹ * ⟨y, hy⟩ : ↥L) : G) = m⁻¹ * y := rfl
    rw [this, hyz, inv_mul_cancel_left]
    exact hz

theorem le_of_mImage_eq_top {M : Subgroup G} (hLc : commutator ↥L = ⊤) (htop : mImage L φ M = ⊤) :
    L ≤ M := by
  refine le_of_mul_centerOf L hLc fun y hy => ?_
  rw [← mem_mImage_iff L φ hy, htop]
  exact Subgroup.mem_top _

theorem commute_conj_of_fix {ε : MulAut K} {k : K} (hk : ε k = k) : Commute ε (MulAut.conj k) := by
  ext x
  change ε (k * x * k⁻¹) = k * ε x * k⁻¹
  rw [map_mul, map_mul, map_inv, hk]

end Psi

end Odd

namespace Hyp36

open Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem le_of_not_faithful (h : Hyp36 G M p E) (L : Subgroup G) [L.Normal] (hLc : commutator ↥L = ⊤)
    {e : G} (he : e ∈ E) (he1 : e ≠ 1) (hall : ∀ y ∈ L, e * y * e⁻¹ * y⁻¹ ∈ centerOf L) : L ≤ M := by
  have hcent := centralizes_of_forall_comm_mem L hLc hall
  intro y hy
  exact h.centralizer_le_of_ne_one he he1 (Subgroup.mem_centralizer_singleton_iff.2 (hcent y hy).symm)

theorem exists_mem_of_fixed (h : Hyp36 G M p E) (L : Subgroup G) [L.Normal] {K : Type} [Group K]
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* K) {e : G} (he : e ∈ E) (he1 : e ≠ 1) {k : K}
    (hk : psi L φ e k = k) :
    k ∈ mImage L φ M ∧ ∃ m ∈ M ⊓ L, MulAut.conj k = psi L φ m := by
  obtain ⟨c, rfl⟩ := φ.surjective k
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨m, hm, z, hz, hyz⟩ := h.mem_mul_centerOf_of_fixed L he he1 hy ((psi_mk_eq_iff L φ e y hy).1 hk)
  refine ⟨(mem_mImage_iff L φ hy).2 ⟨m, hm, z, hz, hyz⟩, m, hm, ?_⟩
  rw [← psi_eq_conj L φ hy, hyz, map_mul, psi_eq_one_of_mem_centerOf L φ hz, mul_one]

theorem le_of_forall_centralizer_le (h : Hyp36 G M p E) {N : Subgroup G}
    (hN : ∀ e ∈ E, e ≠ 1 → ∀ q ∈ pCoreOf 2 M, q * e = e * q → q ∈ N) : pCoreOf 2 M ≤ N := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  set Q := pCoreOf 2 M with hQ
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) :=
    h.E_le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  letI : MulDistribMulAction E Q :=
    MulDistribMulAction.compHom Q (Q.normalizerMonoidHom.comp (Subgroup.inclusion hEQ))
  have hact : ∀ (a : E) (x : Q), ((a • x : Q) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  haveI : IsElementaryAbelian p E := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp h.elem
  have hQ2 : IsPGroup 2 Q := by
    rw [hQ, pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  have hpQ : ¬ p ∣ Nat.card Q := by
    obtain ⟨a, ha⟩ := hQ2.exists_card_eq
    rw [ha]
    intro hd
    exact h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1
      (h.prime.dvd_of_dvd_pow hd))
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := E) (H := Q)
    (by rw [h.card]) hpQ
  intro q hq
  have hmem : (⟨q, hq⟩ : Q) ∈ (⊤ : Subgroup Q) := Subgroup.mem_top _
  rw [← hgen] at hmem
  have hle : (⨆ (a : E) (_ : a ≠ 1), fixedPointSubgroup (Subgroup.zpowers a) Q) ≤ N.subgroupOf Q := by
    refine iSup₂_le fun a ha1 x hx => ?_
    rw [Subgroup.mem_subgroupOf]
    have h1 := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a x).1 hx
    have h2 : (a : G) * (x : G) * (a : G)⁻¹ = (x : G) := by
      have := congrArg (fun z : Q => (z : G)) h1
      simpa [hact a x] using this
    refine hN a a.2 (fun h1' => ha1 (Subtype.ext h1')) x x.2 ?_
    calc (x : G) * a = (a : G) * (x : G) * (a : G)⁻¹ * a := by rw [h2]
      _ = (a : G) * x := by group
  exact hle hmem

theorem exists_centralizer_act_nontrivially (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal]
    (hLc : commutator ↥L = ⊤) (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ q ∈ pCoreOf 2 M, q * e = e * q ∧
      ∃ y ∈ L, q * y * q⁻¹ * y⁻¹ ∉ centerOf L := by
  by_contra hcon
  push Not at hcon
  have hker : ∀ g : G, g ∈ (actHom L).ker ↔ ∀ y ∈ L, g * y * g⁻¹ * y⁻¹ ∈ centerOf L := by
    intro g
    rw [MonoidHom.mem_ker]
    constructor
    · intro hg y hy
      rw [← actHom_mk_eq_iff L g hy, hg]
      rfl
    · intro hg
      ext x
      induction x using QuotientGroup.induction_on with
      | H y => exact (actHom_mk_eq_iff L g y.2).2 (hg y y.2)
  have hQN : pCoreOf 2 M ≤ (actHom L).ker := h.le_of_forall_centralizer_le fun e he he1 q hq hqe =>
    (hker q).2 (hcon e he he1 q hq hqe)
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  exact centralizes_of_forall_comm_mem L hLc ((hker q).1 (hQN hq)) x hx

theorem false_of_seitz (hS : AGLEmbeddingD2.KFactSeitzRankTwo) (h : Hyp36 G M p E) {L : Subgroup G}
    [L.Normal] (hL : CFSG.IsComponent L) (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) (d : TauCeti.ValidLieTypeIndex)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hp : p ≠ d.1.characteristic) (hex : ¬ AGLEmbeddingD2.IsD2SeitzException p d.1) : False :=
  h.false_of_component_le hL hne (h.le_of_seitz hS hL.1.1 d φ hp hex)

theorem false_of_seitz_odd (hS : AGLEmbeddingD2.KFactSeitzRankTwo) (h : Hyp36 G M p E)
    {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L) (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥)
    (d : TauCeti.ValidLieTypeIndex)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hodd : d.1.characteristic ≠ 2) (hp : p ≠ d.1.characteristic) : False :=
  h.false_of_seitz hS hL hne d φ hp fun hex =>
    hodd (characteristic_eq_two_of_isD2SeitzException hex)

end Hyp36

abbrev CatGrp (d : TauCeti.ValidLieTypeIndex) : Type := (TauCeti.CFSGIndex.lie d).Group

@[expose] def OddDefCharCentralizer : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ 2 →
    ∀ ε : MulAut (CatGrp d), ε ^ d.1.characteristic = 1 → ε ≠ 1 →
    ∀ R : Subgroup (MulAut (CatGrp d)), R ≠ ⊥ → IsPGroup 2 R → (∀ r ∈ R, r * ε = ε * r) →
      (∀ k : CatGrp d, ε k = k → ∀ r ∈ R, MulAut.conj k * r * (MulAut.conj k)⁻¹ ∈ R) →
      d.1.characteristic = 3 ∧
        Nonempty (CatGrp d ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) ∧
        ε ∉ (MulAut.conj : CatGrp d →* MulAut (CatGrp d)).range

@[expose] def L227Generation : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    Nonempty (CatGrp d ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) →
    ∀ ε : MulAut (CatGrp d), ε ^ 3 = 1 → ε ∉ (MulAut.conj : CatGrp d →* MulAut (CatGrp d)).range →
      ∀ S : Sylow 3 (CatGrp d), Subgroup.closure ((S : Set (CatGrp d)) ∪ {k | ε k = k}) = ⊤

@[expose] def K36OddDefChar : Prop := OddDefCharCentralizer ∧ L227Generation

namespace Hyp36

open Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem false_of_oddDefChar (hR : OddDefCharCentralizer) (hR' : L227Generation) (h : Hyp36 G M p E)
    {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L) (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥)
    (d : TauCeti.ValidLieTypeIndex)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hodd : d.1.characteristic ≠ 2) (hp : p = d.1.characteristic) :
    False := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hLc : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hLM : ¬ L ≤ M := fun hLM => h.false_of_component_le hL hne hLM
  have hfaith : ∀ e ∈ E, e ≠ 1 → ∃ y ∈ L, e * y * e⁻¹ * y⁻¹ ∉ centerOf L := by
    intro e he he1
    by_contra hcon
    push Not at hcon
    exact hLM (h.le_of_not_faithful L hLc he he1 hcon)
  obtain ⟨e, he, he1, q, hq, hqe, y₀, hy₀, hy₀'⟩ := h.exists_centralizer_act_nontrivially hLc hne
  set Ψ : G →* MulAut (TauCeti.CFSGIndex.lie d).Group := psi L φ with hΨ
  set ε : MulAut (TauCeti.CFSGIndex.lie d).Group := Ψ e with hεdef
  have hε1 : ε ≠ 1 := by
    obtain ⟨y, hy, hy'⟩ := hfaith e he he1
    intro hε
    apply hy'
    rw [← psi_mk_eq_iff L φ e y hy]
    change ε _ = _
    rw [hε]
    rfl
  have hεp : ε ^ p = 1 := by rw [hεdef, ← map_pow, h.elem.2 e he, map_one]
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := by
    rw [pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  set Qb : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group) := (pCoreOf 2 M).map Ψ with hQb
  set Rb : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group) :=
    Qb ⊓ Subgroup.centralizer ({ε} : Set (MulAut (TauCeti.CFSGIndex.lie d).Group)) with hRb
  have hΨq : Ψ q ≠ 1 := by
    intro h1
    apply hy₀'
    rw [← psi_mk_eq_iff L φ q y₀ hy₀]
    change Ψ q _ = _
    rw [h1]
    rfl
  have hqc : ε * Ψ q = Ψ q * ε := by
    calc ε * Ψ q = Ψ (e * q) := (map_mul Ψ e q).symm
      _ = Ψ (q * e) := by rw [hqe]
      _ = Ψ q * ε := map_mul Ψ q e
  have hRb_ne : Rb ≠ ⊥ := by
    intro hbot
    have hmem : Ψ q ∈ Rb := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem Ψ hq, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hqc
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hΨq hmem
  have hRb2 : IsPGroup 2 Rb := (hQ2.map Ψ).to_le inf_le_left
  have hRbcomm : ∀ r ∈ Rb, r * ε = ε * r := fun r hr =>
    (Subgroup.mem_centralizer_iff.1 hr.2 ε rfl).symm
  have hRbnorm : ∀ k : (TauCeti.CFSGIndex.lie d).Group, ε k = k → ∀ r ∈ Rb,
      MulAut.conj k * r * (MulAut.conj k)⁻¹ ∈ Rb := by
    intro k hk r hr
    obtain ⟨-, m, hm, hconj⟩ := h.exists_mem_of_fixed L φ he he1 hk
    have hc : Commute ε (MulAut.conj k) := commute_conj_of_fix hk
    have hr' : Commute ε r := (hRbcomm r hr).symm
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.1 hr.1
      rw [hconj, ← map_inv, ← map_mul, ← map_mul]
      refine Subgroup.mem_map.2 ⟨m * q' * m⁻¹, ?_, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm.1) q').1 hq'
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (hc.mul_right hr').mul_right hc.inv_right
  have hp' : ε ^ d.1.characteristic = 1 := by rw [← hp]; exact hεp
  obtain ⟨hp3, he27, hout⟩ := hR d hodd ε hp' hε1 Rb hRb_ne hRb2 hRbcomm hRbnorm
  have hp3' : p = 3 := hp.trans hp3
  subst hp3'
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow h.isPGroup
  have hPM : (P : Subgroup G) ≤ M := h.le_of_isPGroup P.isPGroup' hEP
  obtain ⟨R, hRP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hL.2
  have hRmem : ∀ r : ↥L, r ∈ (R : Subgroup ↥L) → (r : G) ∈ (P : Subgroup G) ⊓ L := fun r hr => by
    rw [← hRP]
    exact Subgroup.mem_map_of_mem L.subtype hr
  let S₁ : Sylow 3 (↥L ⧸ Subgroup.center ↥L) :=
    R.mapSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
  let S : Sylow 3 (TauCeti.CFSGIndex.lie d).Group :=
    S₁.mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hSeq : (S : Subgroup (TauCeti.CFSGIndex.lie d).Group) =
      ((R : Subgroup ↥L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map φ.toMonoidHom := rfl
  have hS : ∀ s ∈ (S : Subgroup (TauCeti.CFSGIndex.lie d).Group),
      ∃ r ∈ (R : Subgroup ↥L), φ (QuotientGroup.mk r) = s := by
    intro s hs
    rw [hSeq] at hs
    obtain ⟨c, ⟨r, hr, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hs
    exact ⟨r, hr, rfl⟩
  have hgen := hR' d he27 ε hεp hout S
  have hsub : ((S : Set (TauCeti.CFSGIndex.lie d).Group) ∪ {k | ε k = k}) ⊆
      (mImage L φ M : Set (TauCeti.CFSGIndex.lie d).Group) := by
    rintro k (hk | hk)
    · obtain ⟨r, hr, rfl⟩ := hS k hk
      exact ⟨QuotientGroup.mk r, ⟨r, hPM (hRmem r hr).1, rfl⟩, rfl⟩
    · exact (h.exists_mem_of_fixed L φ he he1 hk).1
  have htop : mImage L φ M = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le (mImage L φ M)).2 hsub
  exact hLM (le_of_mImage_eq_top L φ hLc htop)

theorem false_of_oddLie (hS : AGLEmbeddingD2.KFactSeitzRankTwo) (hR : K36OddDefChar) (h : Hyp36 G M p E)
    {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L) (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥)
    (d : TauCeti.ValidLieTypeIndex)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hodd : d.1.characteristic ≠ 2) : False := by
  by_cases hp : p = d.1.characteristic
  · exact h.false_of_oddDefChar hR.1 hR.2 hL hne d φ hodd hp
  · exact h.false_of_seitz_odd hS hL hne d φ hodd hp

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
