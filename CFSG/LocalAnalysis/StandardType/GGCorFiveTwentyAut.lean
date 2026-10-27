module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
public import CFSG.GroupTheory.SteinbergBSQuotientLifting
public import CFSG.GroupTheory.CoprimeCentralizerTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

section TransvectionTransport

variable {p : ℕ}

theorem GGIsTransvection.of_mulEquiv {G G' : Type} [Group G] [Group G'] {E : Subgroup G}
    {E' : Subgroup G'} (f : ↥E ≃* ↥E') {ψ : MulAut ↥E} {ψ' : MulAut ↥E'}
    (hf : ∀ e, ψ' (f e) = f (ψ e)) (h : GGIsTransvection p ψ) : GGIsTransvection p ψ' := by
  refine ⟨?_, fun e' => ?_⟩
  · rw [← Nat.card_congr f.toEquiv, ← h.1]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquiv f.symm.toEquiv fun e' => ?_)
    change ψ' e' = e' ↔ ψ (f.symm e') = f.symm e'
    conv_lhs => rw [← f.apply_symm_apply e', hf]
    exact f.injective.eq_iff.trans Iff.rfl
  · obtain ⟨e, rfl⟩ := f.surjective e'
    rw [hf, ← map_inv, ← map_mul, hf, h.2 e]

end TransvectionTransport

variable {G : Type} [Group G]

section ConjAut

@[expose] def ggConjAut (Bs : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G)) :
    MulAut ↥Bs where
  toFun b := ⟨g * b * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg b).mp b.2⟩
  invFun b := ⟨g⁻¹ * b * g, (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * b * g)).mpr
    (by rw [show g * (g⁻¹ * (b : G) * g) * g⁻¹ = b by group]; exact b.2)⟩
  left_inv b := Subtype.ext (by simp only; group)
  right_inv b := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem ggConjAut_apply (Bs : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (b : ↥Bs) : ((ggConjAut Bs hg b : ↥Bs) : G) = g * b * g⁻¹ :=
  rfl

theorem ggConjAut_pow_apply (Bs : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (n : ℕ) (b : ↥Bs) : (((ggConjAut Bs hg ^ n) b : ↥Bs) : G) = g ^ n * b * (g ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ggConjAut_apply, ih, pow_succ']
    group

theorem inv_apply_of_forall {Bs : Subgroup G} {φ : MulAut ↥Bs} {h : G}
    (hφ : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = h * b * h⁻¹) (b : ↥Bs) :
    ((φ⁻¹ b : ↥Bs) : G) = h⁻¹ * b * h := by
  have h1 : ((φ (φ⁻¹ b) : ↥Bs) : G) = b := by rw [MulAut.apply_inv_self]
  rw [hφ] at h1
  rw [← h1]
  group

theorem ggConjAut_mem_ggInduced {H Bs : Subgroup G} {g : G} (hgH : g ∈ H)
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) : ggConjAut Bs hg ∈ ggInduced H Bs :=
  ⟨g, hgH, hg, fun _ => rfl⟩

@[expose] def ggInducedSubgroup (H Bs : Subgroup G) : Subgroup (MulAut ↥Bs) where
  carrier := ggInduced H Bs
  mul_mem' := by
    rintro φ ψ ⟨g, hgH, hgN, hφ⟩ ⟨h, hhH, hhN, hψ⟩
    refine ⟨g * h, H.mul_mem hgH hhH, Subgroup.mul_mem _ hgN hhN, fun b => ?_⟩
    rw [MulAut.mul_apply, hφ, hψ]
    group
  one_mem' := ⟨1, H.one_mem, Subgroup.one_mem _, fun b => by simp⟩
  inv_mem' := by
    rintro φ ⟨g, hgH, hgN, hφ⟩
    exact ⟨g⁻¹, H.inv_mem hgH, Subgroup.inv_mem _ hgN, fun b => by
      rw [inv_apply_of_forall hφ, inv_inv]⟩

theorem ggAutomizer_eq (H Bs : Subgroup G) : ggAutomizer H Bs = ggInducedSubgroup H Bs :=
  le_antisymm ((Subgroup.closure_le _).mpr fun _ h => h) fun _ h => Subgroup.subset_closure h

theorem mem_ggAutomizer_iff {H Bs : Subgroup G} {φ : MulAut ↥Bs} :
    φ ∈ ggAutomizer H Bs ↔ ∃ g ∈ H, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := by
  rw [ggAutomizer_eq]
  rfl

theorem ggConjAut_mem_ggAutomizer {H Bs : Subgroup G} {g : G} (hgH : g ∈ H)
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) : ggConjAut Bs hg ∈ ggAutomizer H Bs :=
  Subgroup.subset_closure (ggConjAut_mem_ggInduced hgH hg)

theorem ggAutomizer_mono {H H' : Subgroup G} (Bs : Subgroup G) (h : H ≤ H') :
    ggAutomizer H Bs ≤ ggAutomizer H' Bs :=
  Subgroup.closure_mono fun _ ⟨g, hg, hgN, hφ⟩ => ⟨g, h hg, hgN, hφ⟩

end ConjAut

section CoprimeQuotient

variable {N : Subgroup G} [N.Normal] {p : ℕ} [Fact p.Prime] {H Bs : Subgroup G}

@[expose] noncomputable def coprimeQuotientSubgroupEquiv
    (hpN : ¬ p ∣ Nat.card N) (hBs : IsPGroup p Bs) :
    ↥Bs ≃* ↥(Bs.map (QuotientGroup.mk' N)) :=
  (MonoidHom.ofInjective (f := (QuotientGroup.mk' N).comp Bs.subtype)
    (CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype hpN hBs)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

@[simp] theorem coe_coprimeQuotientSubgroupEquiv
    (hpN : ¬ p ∣ Nat.card N) (hBs : IsPGroup p Bs) (b : ↥Bs) :
    ((coprimeQuotientSubgroupEquiv hpN hBs b :
      ↥(Bs.map (QuotientGroup.mk' N))) : G ⧸ N) =
      QuotientGroup.mk' N (b : G) :=
  rfl

variable [Finite G]

theorem bstar_selfCent_map_mk'_of_coprime
    (hpN : ¬ p ∣ Nat.card N) {Bs : Subgroup G} (hBs : IsPGroup p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    ∀ y ∈ Subgroup.centralizer
      ((Bs.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)),
      y ^ p = 1 → y ∈ Bs.map (QuotientGroup.mk' N) := by
  intro y hyC hyp
  by_cases hy1 : y = 1
  · simp [hy1]
  · have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
    obtain ⟨x, hxC, hxord, hxeq⟩ :=
      CFSG.GroupTheory.CoprimeTransport.exists_mem_centralizer_orderOf_eq_prime_mk_eq
        (s := p) (p := p) hpN hpN hBs hyC hyord
    have hx : x ∈ Bs := hSC x hxC (by simpa [hxord] using pow_orderOf_eq_one x)
    rw [← hxeq]
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hx

theorem normalizer_map_mk'_inf_eq
    (hpN : ¬ p ∣ Nat.card N) (hBs : IsPGroup p Bs) (hNH : N ≤ H) :
    (Subgroup.normalizer (Bs : Set G) ⊓ H).map (QuotientGroup.mk' N) =
      Subgroup.normalizer ((Bs.map (QuotientGroup.mk' N) :
        Subgroup (G ⧸ N)) : Set (G ⧸ N)) ⊓ H.map (QuotientGroup.mk' N) := by
  classical
  have hglobal := CFSG.GroupTheory.normal_coprime_quotient_normalizer p N hpN Bs hBs
  refine le_antisymm ?_ ?_
  · calc (Subgroup.normalizer (Bs : Set G) ⊓ H).map (QuotientGroup.mk' N)
        ≤ (Subgroup.normalizer (Bs : Set G)).map (QuotientGroup.mk' N) ⊓
            H.map (QuotientGroup.mk' N) :=
          Subgroup.map_inf_le _ _ _
      _ = _ := by rw [hglobal]
  · intro q hq
    rw [Subgroup.mem_inf] at hq
    obtain ⟨hqN, hqH⟩ := hq
    rw [Subgroup.mem_map] at hqH
    obtain ⟨h, hhH, rfl⟩ := hqH
    have hmem : QuotientGroup.mk' N h ∈
        (Subgroup.normalizer (Bs : Set G)).map (QuotientGroup.mk' N) := by
      rw [hglobal]
      exact hqN
    obtain ⟨g, hgN, hgEq⟩ := hmem
    have hgH : g ∈ H := by
      have hker : h⁻¹ * g ∈ N := by
        refine (QuotientGroup.eq_one_iff (h⁻¹ * g)).mp ?_
        have hgEq' : (g : G ⧸ N) = (h : G ⧸ N) := hgEq
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hgEq', inv_mul_cancel]
      have hg : g = h * (h⁻¹ * g) := by group
      rw [hg]
      exact H.mul_mem hhH (hNH hker)
    exact Subgroup.mem_map.mpr ⟨g, ⟨hgN, hgH⟩, hgEq⟩

theorem ggAutomizer_map_mk'_of_coprime
    (hpN : ¬ p ∣ Nat.card N) (hBs : IsPGroup p Bs) (hNH : N ≤ H) :
    ggAutomizer (H.map (QuotientGroup.mk' N)) (Bs.map (QuotientGroup.mk' N)) =
      (ggAutomizer H Bs).map
        (MulAut.congr (coprimeQuotientSubgroupEquiv hpN hBs)).toMonoidHom := by
  classical
  set e : ↥Bs ≃* ↥(Bs.map (QuotientGroup.mk' N)) := coprimeQuotientSubgroupEquiv hpN hBs
  have hnorm := normalizer_map_mk'_inf_eq (H := H) (Bs := Bs) hpN hBs hNH
  have hcongr : ∀ (φ : MulAut ↥Bs) (b : ↥Bs),
      MulAut.congr e φ (e b) = e (φ b) := by
    intro φ b
    change (e.symm.trans (φ.trans e)) (e b) = e (φ b)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  refine le_antisymm ?_ ?_
  · intro φ' hφ'
    obtain ⟨g', hg'H, hg'N, hφ'g'⟩ := mem_ggAutomizer_iff.mp hφ'
    have hg' : g' ∈ Subgroup.normalizer (Bs.map (QuotientGroup.mk' N)) ⊓
        H.map (QuotientGroup.mk' N) := ⟨hg'N, hg'H⟩
    rw [← hnorm] at hg'
    obtain ⟨g, hg, hgEq⟩ := Subgroup.mem_map.mp hg'
    obtain ⟨hgN, hgH⟩ := Subgroup.mem_inf.mp hg
    refine Subgroup.mem_map.mpr ⟨ggConjAut Bs hgN, ?_, ?_⟩
    · exact ggConjAut_mem_ggAutomizer hgH hgN
    · ext b'
      obtain ⟨b, rfl⟩ := e.surjective b'
      calc ((MulAut.congr e (ggConjAut Bs hgN)) (e b) : G ⧸ N)
          = (e (ggConjAut Bs hgN b) : G ⧸ N) := by rw [hcongr]
        _ = QuotientGroup.mk' N (g * b * g⁻¹) := by
            rw [coe_coprimeQuotientSubgroupEquiv, ggConjAut_apply]
        _ = QuotientGroup.mk' N g * QuotientGroup.mk' N b *
              (QuotientGroup.mk' N g)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = g' * (e b) * g'⁻¹ := by
            rw [hgEq, coe_coprimeQuotientSubgroupEquiv]
        _ = (φ' (e b) : G ⧸ N) := by rw [hφ'g' (e b)]
  · intro φ' hφ'
    obtain ⟨φ, hφA, rfl⟩ := Subgroup.mem_map.mp hφ'
    obtain ⟨g, hgH, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφA
    refine mem_ggAutomizer_iff.mpr ⟨QuotientGroup.mk' N g, ?_, ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hgH
    · exact Subgroup.le_normalizer_map (QuotientGroup.mk' N)
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' N) hgN)
    · intro b'
      obtain ⟨b, rfl⟩ := e.surjective b'
      calc ((MulAut.congr e φ) (e b) : G ⧸ N)
          = (e (φ b) : G ⧸ N) := by rw [hcongr]
        _ = QuotientGroup.mk' N (g * b * g⁻¹) := by
            rw [coe_coprimeQuotientSubgroupEquiv, hφg b]
        _ = QuotientGroup.mk' N g * QuotientGroup.mk' N b *
              (QuotientGroup.mk' N g)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = QuotientGroup.mk' N g * (e b) * (QuotientGroup.mk' N g)⁻¹ := by
            rw [coe_coprimeQuotientSubgroupEquiv]

theorem card_ggAutomizer_map_mk'_of_coprime
    (hpN : ¬ p ∣ Nat.card N) (hBs : IsPGroup p Bs) (hNH : N ≤ H) :
    Nat.card (ggAutomizer (H.map (QuotientGroup.mk' N))
        (Bs.map (QuotientGroup.mk' N))) = Nat.card (ggAutomizer H Bs) := by
  rw [ggAutomizer_map_mk'_of_coprime hpN hBs hNH]
  exact Subgroup.card_map_of_injective (MulAut.congr _).injective

theorem noTransvection_map_mk'_of_coprime
    (hpN : ¬ p ∣ Nat.card N) {Bs : Subgroup G} (hBs : IsPGroup p Bs)
    (hNT : GGNoTransvection p Bs) :
    GGNoTransvection p (Bs.map (QuotientGroup.mk' N)) := by
  classical
  intro φ' hφ' hT'
  obtain ⟨g', -, hg'N, hφ'g'⟩ := hφ'
  have hg'mem : g' ∈ (Subgroup.normalizer (Bs : Set G)).map (QuotientGroup.mk' N) := by
    rw [CFSG.GroupTheory.normal_coprime_quotient_normalizer p N hpN Bs hBs]
    exact hg'N
  obtain ⟨g, hgN, hgg'⟩ := Subgroup.mem_map.mp hg'mem
  let φ : MulAut ↥Bs := ggConjAut Bs hgN
  have hφ_apply : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * (b : G) * g⁻¹ := by
    intro b
    exact ggConjAut_apply Bs hgN b
  have hφI : φ ∈ ggInduced (⊤ : Subgroup G) Bs :=
    ggConjAut_mem_ggInduced (Subgroup.mem_top g) hgN
  let e : ↥Bs ≃* ↥(Bs.map (QuotientGroup.mk' N)) := coprimeQuotientSubgroupEquiv hpN hBs
  have he_coe : ∀ b : ↥Bs,
      ((e b : ↥(Bs.map (QuotientGroup.mk' N))) : G ⧸ N) =
        QuotientGroup.mk' N (b : G) :=
    fun b => coe_coprimeQuotientSubgroupEquiv hpN hBs b
  have hcongr : ∀ b : ↥Bs, e (φ b) = φ' (e b) := by
    intro b
    apply Subtype.ext
    rw [he_coe, hφ_apply, map_mul, map_mul, map_inv, hφ'g' (e b), ← hgg', he_coe]
  have hTφ : GGIsTransvection p φ := by
    refine GGIsTransvection.of_mulEquiv (f := e.symm) (ψ := φ')
      (ψ' := φ) ?_ hT'
    intro x
    apply e.injective
    rw [hcongr (e.symm x), MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact hNT φ hφI hTφ

end CoprimeQuotient

theorem noTransvection_subgroupOf {p : ℕ} [Fact p.Prime] {H Bs : Subgroup G}
    (hBH : Bs ≤ H) (hNT : GGNoTransvection p Bs) :
    GGNoTransvection p (Bs.subgroupOf H) := by
  classical
  intro φ hφ hT
  obtain ⟨g, -, hgN, hφg⟩ := hφ
  have hgN' : (g : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hgN ⊢
    intro b
    constructor
    · intro hb
      have hbH : b ∈ H := hBH hb
      have hb' : (⟨b, hbH⟩ : ↥H) ∈ Bs.subgroupOf H := Subgroup.mem_subgroupOf.mpr hb
      have h := (hgN ⟨b, hbH⟩).mp hb'
      exact Subgroup.mem_subgroupOf.mp h
    · intro hb
      have hbH : (g : G) * b * (g : G)⁻¹ ∈ H := hBH hb
      have hb' : (⟨(g : G) * b * (g : G)⁻¹, hbH⟩ : ↥H) ∈ Bs.subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr hb
      have hgNinv : (g : ↥H)⁻¹ ∈ Subgroup.normalizer
          ((Bs.subgroupOf H : Subgroup ↥H) : Set ↥H) := Subgroup.inv_mem _ hgN
      have h := (Subgroup.mem_normalizer_iff.mp hgNinv
        ⟨(g : G) * b * (g : G)⁻¹, hbH⟩).mp hb'
      have h' : ((g : G)⁻¹ * ((g : G) * b * (g : G)⁻¹) * (g : G)) ∈ Bs := by
        simpa using Subgroup.mem_subgroupOf.mp h
      simpa [mul_assoc] using h'
  let e : ↥(Bs.subgroupOf H) ≃* ↥Bs := Subgroup.subgroupOfEquivOfLe hBH
  let ψ : MulAut ↥Bs := ggConjAut Bs hgN'
  have hcongr : ∀ x : ↥(Bs.subgroupOf H), ψ (e x) = e (φ x) := by
    intro x
    apply Subtype.ext
    change ((ggConjAut Bs hgN') (e x) : G) = ((e (φ x) : ↥Bs) : G)
    rw [ggConjAut_apply]
    have hx : ((e x : ↥Bs) : G) = (x : G) := by
      rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
    have hphi : ((e (φ x) : ↥Bs) : G) = ((φ x : ↥(Bs.subgroupOf H)) : G) := by
      rw [Subgroup.subgroupOfEquivOfLe_apply_coe]
    rw [hx, hphi]
    exact (congrArg (fun y : ↥H => (y : G)) (hφg x)).symm
  have hTψ : GGIsTransvection p ψ := by
    refine GGIsTransvection.of_mulEquiv (f := e) (ψ := φ) (ψ' := ψ) ?_ hT
    intro x
    rw [hcongr x]
  have hφI : ψ ∈ ggInduced (⊤ : Subgroup G) Bs :=
    ggConjAut_mem_ggInduced (Subgroup.mem_top (g : G)) hgN'
  exact hNT ψ hφI hTψ

section PseudoReflection

@[expose] def GGIsPseudoReflection (p : ℕ) {Bs : Subgroup G} (φ : MulAut ↥Bs) : Prop :=
  φ ^ (p - 1) = 1 ∧ Nat.card {b : ↥Bs // φ b = b} * p = Nat.card ↥Bs

theorem GGIsReflection.isPseudoReflection {p : ℕ} (hp : Odd p) {Bs : Subgroup G}
    {φ : MulAut ↥Bs} (h : GGIsReflection p φ) : GGIsPseudoReflection p φ := by
  obtain ⟨k, rfl⟩ := hp
  refine ⟨?_, h.2⟩
  rw [show 2 * k + 1 - 1 = 2 * k by omega, pow_mul, h.1, one_pow]

theorem GGIsPseudoReflection.conj {p : ℕ} {Bs : Subgroup G} {φ : MulAut ↥Bs}
    (h : GGIsPseudoReflection p φ) (ψ : MulAut ↥Bs) : GGIsPseudoReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨by rw [conj_pow, h.1, mul_one, mul_inv_cancel], ?_⟩
  rw [← h.2]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (ψ⁻¹ : MulAut ↥Bs).toEquiv fun b => ?_)
  show ψ (φ (ψ⁻¹ b)) = b ↔ φ (ψ⁻¹ b) = ψ⁻¹ b
  constructor
  · intro hb
    have h1 := congrArg (ψ⁻¹ : MulAut ↥Bs) hb
    rwa [MulAut.inv_apply_self] at h1
  · intro hb
    rw [hb, MulAut.apply_inv_self]

theorem le_normalizer_of_pseudoReflection {p : ℕ} {Bs : Subgroup G}
    {A W : Subgroup (MulAut ↥Bs)} (hWA : W ≤ A)
    (hgen : W = Subgroup.closure {φ | φ ∈ W ∧ GGIsPseudoReflection p φ})
    (hR : ∀ φ ∈ A, GGIsPseudoReflection p φ → φ ∈ W) :
    A ≤ Subgroup.normalizer (W : Set (MulAut ↥Bs)) := by
  have hS : {φ | φ ∈ W ∧ GGIsPseudoReflection p φ} =
      {φ | φ ∈ A ∧ GGIsPseudoReflection p φ} := by
    ext φ
    exact ⟨fun h => ⟨hWA h.1, h.2⟩, fun h => ⟨hR φ h.1 h.2, h.2⟩⟩
  rw [hS] at hgen
  refine le_normalizer_of_map_conj_le fun a ha => ?_
  rw [hgen, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨φ, ⟨hφA, hφ⟩, rfl⟩
  exact ⟨A.mul_mem (A.mul_mem ha hφA) (A.inv_mem ha), hφ.conj a⟩

end PseudoReflection

section Scalar

@[expose] def GGIsScalar {Bs : Subgroup G} (φ : MulAut ↥Bs) : Prop :=
  ∃ k : ℕ, ∀ b : ↥Bs, φ b = b ^ k

variable [Finite G]

theorem mem_normalizer_of_ggIsScalar {Bs H : Subgroup G} (hH : H ≤ Bs) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hs : GGIsScalar (ggConjAut Bs hg)) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  obtain ⟨k, hk⟩ := hs
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨h, hh, rfl⟩
    have h1 : ((ggConjAut Bs hg ⟨h, hH hh⟩ : ↥Bs) : G) = h ^ k := by
      rw [hk]
      rfl
    rw [ggConjAut_apply] at h1
    show g * h * g⁻¹ ∈ H
    rw [h1]
    exact H.pow_mem hh k
  have hcard : Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  exact mem_normalizer_iff_map_conj.mpr (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

omit [Finite G] in
theorem ggConjAut_inv_mul_apply {Bs : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hh : h ∈ Subgroup.normalizer (Bs : Set G))
    {w : MulAut ↥Bs} (hw : ∀ b : ↥Bs, ((w b : ↥Bs) : G) = h * b * h⁻¹) (b : ↥Bs) :
    ggConjAut Bs (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg) b = (w⁻¹ * ggConjAut Bs hg) b := by
  apply Subtype.ext
  rw [MulAut.mul_apply, inv_apply_of_forall hw, ggConjAut_apply, ggConjAut_apply]
  group

end Scalar

theorem normalizer_orderOf_eq_of_coordinate {C : Type*} [Group C] {G : Type} [Group G]
    {E : Subgroup G} {τ : C →* G}
    (hτinj : Function.Injective τ) (hτrange : τ.range = E)
    (w : G) (wcoord : MulAut C)
    (hact : ∀ f, w * τ f * w⁻¹ = τ (wcoord f)) :
    ∃ (n : G) (hn : n ∈ Subgroup.normalizer (E : Set G)),
      orderOf (E.normalizerMonoidHom ⟨n, hn⟩) = orderOf wcoord := by
  classical
  have hmem : ∀ f, τ f ∈ E := by
    intro f
    rw [← hτrange]
    exact ⟨f, rfl⟩
  let eτ : C ≃* E :=
    MulEquiv.ofBijective (τ.codRestrict E hmem)
      ⟨fun f g h => hτinj (Subtype.ext_iff.mp h), fun e => by
        have he : (e : G) ∈ τ.range := by
          rw [hτrange]
          exact e.2
        obtain ⟨f, hf⟩ := he
        exact ⟨f, Subtype.ext hf⟩⟩
  have hmap : E.map (MulAut.conj w).toMonoidHom = E := by
    apply le_antisymm
    · rintro _ ⟨e, he, rfl⟩
      have he' : e ∈ τ.range := by rwa [hτrange]
      obtain ⟨f, rfl⟩ := he'
      change (MulAut.conj w) (τ f) ∈ E
      rw [MulAut.conj_apply, hact f]
      exact hmem (wcoord f)
    · intro e he
      have he' : e ∈ τ.range := by rwa [hτrange]
      obtain ⟨f, rfl⟩ := he'
      refine ⟨τ (wcoord.symm f), hmem _, ?_⟩
      change (MulAut.conj w) (τ (wcoord.symm f)) = τ f
      rw [MulAut.conj_apply, hact (wcoord.symm f)]
      simp
  have hnorm : w ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  let c : MulAut E := E.normalizerMonoidHom ⟨w, hnorm⟩
  have hc : c = MulAut.congr eτ wcoord := by
    apply MulEquiv.ext
    intro e
    obtain ⟨f, rfl⟩ := eτ.surjective e
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change w * τ f * w⁻¹ =
      ((MulAut.congr eτ wcoord) (eτ f) : ↥E)
    have heτ_apply : ∀ f, (eτ f : G) = τ f := by
      intro f
      dsimp only [eτ]
      rfl
    rw [hact f, MulAut.congr_apply]
    simp [MulEquiv.trans_apply, heτ_apply]
  refine ⟨w, hnorm, ?_⟩
  change orderOf c = orderOf wcoord
  rw [hc, MulEquiv.orderOf_eq]


end CFSG.StandardType
