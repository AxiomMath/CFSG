module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartOne.S12.Sec12Three
public import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartOne.KF.SpQuad
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.S12.Facts
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.KFQ
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.Sec12Three CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PerfectCover CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Planes

theorem card_multiplier_psp_three {f : ℕ} (hf : 2 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .PSp 3 2 f ×
      Blueprint.Multiplier.exceptional .PSp 3 2 f) = 1 := by
  have hcop : Nat.Coprime 2 (2 ^ f - 1) := by
    rw [Nat.coprime_two_left]
    simpa using CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one (f := f) (n := 1)
      (by omega) le_rfl
  have hgen : Blueprint.Multiplier.genericOrders .PSp 3 2 f = (1, 1) := by
    change (Nat.gcd 2 (2 ^ f - 1), 1) = (1, 1)
    rw [Nat.Coprime.gcd_eq_one hcop]
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSp 3 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem psp_three_center_trivial
    (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {f : ℕ} (hf : 2 ≤ f) (hqs : CFSG.IsQuasisimple X)
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSp 3 2 f) :
    Subgroup.center X = ⊥ := by
  have hm : Models.LieModel (X ⧸ Subgroup.center X) .PSp 3 2 f := ⟨hmodel.1, .inl hmodel⟩
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA _ .PSp 3 2 f hm
  have : Group.IsPerfect (X ⧸ Subgroup.center X) := ⟨hcomm⟩
  have : Group.IsPerfect X := hqs.1
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker ≤ Subgroup.center X :=
    (QuotientGroup.ker_mk' _).le
  obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
    perfect_central_kernel_quotient_of_schur_multiplier (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _) hker
  have hdvd : Nat.card (QuotientGroup.mk' (Subgroup.center X)).ker ∣
      Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rw [Nat.card_congr (hopfMultiplierEquivGriess _).symm.toEquiv, Nat.card_congr e.toEquiv,
    card_multiplier_psp_three hf, Nat.dvd_one, QuotientGroup.ker_mk'] at hdvd
  rw [← Subgroup.card_eq_one]
  exact hdvd

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def IsTor (p : ℕ) (g : ↥(M10 K)) : Prop :=
  ∃ x : Fin 3 → (Qext K)ˣ, (∀ i, x i ^ p = 1) ∧ g.1 = torusEquiv x

theorem IsTor.one {p : ℕ} : IsTor p (1 : ↥(M10 K)) :=
  ⟨1, fun _ => one_pow _, torusEquiv_one.symm⟩

theorem IsTor.mul {p : ℕ} {g h : ↥(M10 K)} (hg : IsTor p g) (hh : IsTor p h) : IsTor p (g * h) := by
  obtain ⟨x, hx, hgx⟩ := hg
  obtain ⟨y, hy, hhy⟩ := hh
  refine ⟨x * y, fun i => ?_, ?_⟩
  · simp [mul_pow, hx i, hy i]
  · change g.1 * h.1 = _
    rw [hgx, hhy, torusEquiv_mul]

theorem IsTor.inv {p : ℕ} {g : ↥(M10 K)} (hg : IsTor p g) : IsTor p g⁻¹ := by
  obtain ⟨x, hx, hgx⟩ := hg
  refine ⟨x⁻¹, fun i => ?_, ?_⟩
  · simp [inv_pow, hx i]
  · change g.1⁻¹ = _
    rw [hgx]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← torusEquiv_mul, mul_inv_cancel, torusEquiv_one]

theorem isTor_iff_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (g : ↥(M10 K)) :
    IsTor p g ↔ g ∈ (emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K) := by
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, hgx⟩
    obtain ⟨d, hd⟩ := sqCoords_surjective hp hp2 x hx
    refine ⟨d, ?_⟩
    change torusHom (sqCoords d) = g.1
    rw [hd, hgx]
    rfl
  · rintro ⟨d, hd⟩
    exact ⟨sqCoords d, sqCoords_pow d, by rw [← hd]; rfl⟩

structure Sp6Ctx {G : Type} [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G)
    (L E : Subgroup G) (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] where
  h : Sec12Hyp G p A c L E
  hE4 : Nat.card E = p ^ 4
  R : Restr c L E (E ⊓ L)
  hcL : c ∉ L
  hK : Nat.card K = 2 ^ f
  hf2 : 2 ≤ f
  hpq : p ∣ 2 ^ f + 1
  ψ : ↥(M10 K) ≃* ↥L
  hψ : ∀ g : ↥(M10 K), ((ψ g : ↥L) : G) ∈ E ↔ IsTor p g

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} (C : Sp6Ctx p A c L E f K)

include C in
theorem hpq' : p ∣ Nat.card K + 1 := by rw [C.hK]; exact C.hpq

include C in
theorem hp2 : p ≠ 2 := by
  have := C.h.three_lt
  omega

@[expose] noncomputable def phi : ↥(M10 K) →* G := L.subtype.comp C.ψ.toMonoidHom

theorem coe_phi (g : ↥(M10 K)) : (C.phi g : G) = ((C.ψ g : ↥L) : G) := rfl

theorem phi_injective : Function.Injective C.phi := fun _ _ hxy =>
  C.ψ.injective (Subtype.ext hxy)

theorem phi_mem_L (g : ↥(M10 K)) : C.phi g ∈ L := (C.ψ g).2

theorem phi_mem_E_iff (g : ↥(M10 K)) : C.phi g ∈ E ↔ IsTor p g := C.hψ g

theorem exists_phi_eq {l : G} (hl : l ∈ L) : ∃ g : ↥(M10 K), C.phi g = l :=
  ⟨C.ψ.symm ⟨l, hl⟩, by rw [coe_phi, MulEquiv.apply_symm_apply]⟩

theorem exists_decomp {e : G} (he : e ∈ E) :
    ∃ x : ↥(M10 K), IsTor p x ∧ ∃ i : ℤ, e = C.phi x * c ^ i := by
  obtain ⟨f', hf', i, hfi⟩ := C.R.exists_mul_zpow he
  obtain ⟨hf'E, hf'L⟩ := Subgroup.mem_inf.mp hf'
  obtain ⟨x, hx⟩ := C.exists_phi_eq hf'L
  exact ⟨x, (C.phi_mem_E_iff x).mp (hx ▸ hf'E), i, by rw [hx]; exact hfi⟩

theorem phi_mul_zpow_mem {x : ↥(M10 K)} (hx : IsTor p x) (i : ℤ) : C.phi x * c ^ i ∈ E :=
  E.mul_mem ((C.phi_mem_E_iff x).mpr hx) (E.zpow_mem C.R.c_mem i)

theorem c_comm_phi (g : ↥(M10 K)) : c * C.phi g = C.phi g * c :=
  C.R.comm _ (C.phi_mem_L g)

theorem conj_phi_mul_zpow (g x : ↥(M10 K)) (i : ℤ) :
    C.phi g * (C.phi x * c ^ i) * (C.phi g)⁻¹ = C.phi (g * x * g⁻¹) * c ^ i := by
  have h1 : C.phi g * c ^ i * (C.phi g)⁻¹ = c ^ i := C.R.conj_zpow (C.phi_mem_L g) i
  calc C.phi g * (C.phi x * c ^ i) * (C.phi g)⁻¹
      = (C.phi g * C.phi x * (C.phi g)⁻¹) * (C.phi g * c ^ i * (C.phi g)⁻¹) := by group
    _ = C.phi (g * x * g⁻¹) * c ^ i := by rw [h1]; simp [map_mul, map_inv]

theorem mem_normalizer {g : ↥(M10 K)} (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹))
    (hg2 : ∀ x, IsTor p x → IsTor p (g⁻¹ * x * g)) :
    C.phi g ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    obtain ⟨x, hx, i, rfl⟩ := C.exists_decomp he
    rw [C.conj_phi_mul_zpow]
    exact C.phi_mul_zpow_mem (hg1 x hx) i
  · intro he'
    obtain ⟨y, hy, i, hyi⟩ := C.exists_decomp he'
    have h1 := C.conj_phi_mul_zpow g⁻¹ y i
    rw [← hyi, map_inv] at h1
    have h2 : (C.phi g)⁻¹ * (C.phi g * e * (C.phi g)⁻¹) * ((C.phi g)⁻¹)⁻¹ = e := by group
    rw [h2] at h1
    rw [h1]
    simpa using C.phi_mul_zpow_mem (hg2 y hy) i

end Sp6Ctx

theorem exists_r10frame {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) (hpq : p ∣ 2 ^ f + 1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSp 3 K)) :
    ∃ (q : ↥(M10 K) →* StatedProj (StatedSp 3 K)) (ε : ↥L →* StatedProj (StatedSp 3 K)),
      Function.Bijective q ∧ IsCentralPQuot p ε ∧
      (∀ t ∈ (emb10 : torusVec p 4 (Qext K) →*
          (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K),
        ∃ x : F, ε (Subgroup.inclusion h.F_le x) = q t) ∧
      ∀ x : F, ∃ t ∈ (emb10 : torusVec p 4 (Qext K) →*
          (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K),
        ε (Subgroup.inclusion h.F_le x) = q t := by
  classical
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  obtain ⟨e10⟩ := nonempty_m10Equiv (K := K)
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
  have hε₀ := isCentralPQuot_center e hcop
  let N : Subgroup ↥(StatedSp 3 K) := (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K)
  have hN : N = ⊥ :=
    CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by norm_num)
  let q : ↥(M10 K) →* StatedProj (StatedSp 3 K) := (QuotientGroup.mk' N).comp e10.toMonoidHom
  have hqbij : Function.Bijective q := by
    refine ⟨fun x y hxy => ?_, (QuotientGroup.mk'_surjective N).comp e10.surjective⟩
    have h1 : (QuotientGroup.mk' N) (e10 x) = (QuotientGroup.mk' N) (e10 y) := hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact e10.injective h1
  have hq : IsCentralPQuot p q := SymCtx.isCentralPQuot_of_bijective q hqbij p
  have hTexp : ∀ t ∈ (emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K), t ^ p = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) ^ p = 1
    rw [← hv]
    exact emb10_pow v
  have hTcomm : ∀ s ∈ (emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K),
      ∀ t ∈ (emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K), s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) *
      (t : QV K (Fin 3) ≃ₗ[K] _) = (t : QV K (Fin 3) ≃ₗ[K] _) * (s : QV K (Fin 3) ≃ₗ[K] _)
    rw [← hv, ← hw]
    exact emb10_comm v w
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot q hq _ hε₀ hTexp hTcomm
    (fun X hexp _ => exists_conj_into_T10 hp h5 hpq' X hexp) h.F_le h.F_exp h.F_comm h.maximal
  exact ⟨q, ε, hqbij, hε, hFT₁, hFT₂⟩

theorem exists_sp6ctx (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E ≠ A) (hf : 1 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (hmodel : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 3 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nonempty (Sp6Ctx p A c L E f K) := by
  have hp := h.prime
  have h5 : 5 ≤ p := five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by omega
    subst hf1
    have h3' : p ∣ 3 := by simpa using hpq
    have := Nat.le_of_dvd (by norm_num) h3'
    omega
  obtain ⟨-, r, -, -, -, -, hr8, hr9⟩ := hF.three
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEA (hr8 (by omega))
  have hE4 : Nat.card E = p ^ 4 := hr9 hr9'
  have hqs : CFSG.IsQuasisimple L :=
    hF.two.elim (fun hG => hG.quasisimple) (fun hS => hS.quasisimple)
  have hZL : Subgroup.center L = ⊥ := psp_three_center_trivial hGA hf2 hqs hmodel
  have hG : Sec12TwoGeneric p c L E := by
    rcases hF.two with hG | hS
    · exact hG
    · exfalso
      have h5' := hS.center_card
      rw [hZL] at h5'
      simp at h5'
  have hcL : c ∉ L := c_not_mem_L h hG.center_pPrime
  have R : Restr c L E (E ⊓ L) := restr_of_generic h hG
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) :=
    { prime := hp
      five_le := h5
      quasisimple := hG.quasisimple
      center_pPrime := hG.center_pPrime
      A₀_le := inf_le_right
      A₀_elem := CFSG.IsElementaryAbelian.of_le h.A_elem inf_le_left
      A₀_card := card_A_inf_L h hG hcL
      A₀_invariant := invariant_A_inf_L h hG
      F_le := inf_le_right
      F_elem := CFSG.IsElementaryAbelian.of_le h.E_elem inf_le_left
      A₀_le_F := inf_le_inf_right L h.A_le_E
      F_le_centralizer := fun f hf a ha => by
        have hfE := (Subgroup.mem_inf.1 hf).1
        have haA := (Subgroup.mem_inf.1 ha).1
        exact (Subgroup.mem_centralizer_iff.1 (h.E_le hfE) a haA)
      F_max := fun F' hF'L hF'el hF'c hFF' => F_max_generic h hG F' hF'L hF'el hF'c hFF' }
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)
  obtain ⟨q, ε, hqbij, hε, hFT₁, hFT₂⟩ := exists_r10frame hcore hK hpq e
  have hεinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact eq_bot_iff.mpr (fun x hx => by
      have := hε.central hx
      rw [hZL] at this
      exact this)
  let εe : ↥L ≃* StatedProj (StatedSp 3 K) := MulEquiv.ofBijective ε ⟨hεinj, hε.surjective⟩
  let qe : ↥(M10 K) ≃* StatedProj (StatedSp 3 K) := MulEquiv.ofBijective q hqbij
  let ψ : ↥(M10 K) ≃* ↥L := qe.trans εe.symm
  have hψε : ∀ g, ε (ψ g) = q g := fun g => by
    change εe (εe.symm (qe g)) = q g
    rw [MulEquiv.apply_symm_apply]
    rfl
  refine ⟨K, hKf, hKfin, hchar, ⟨⟨h, hE4, R, hcL, hK, hf2, hpq, ψ, fun g => ?_⟩⟩⟩
  rw [isTor_iff_mem hp hp2]
  constructor
  · intro hgE
    have hmem : (ψ g : G) ∈ E ⊓ L := Subgroup.mem_inf.mpr ⟨hgE, (ψ g).2⟩
    obtain ⟨t, ht, hεt⟩ := hFT₂ ⟨(ψ g : G), hmem⟩
    have h1 : Subgroup.inclusion hcore.F_le ⟨(ψ g : G), hmem⟩ = ψ g := rfl
    rw [h1, hψε] at hεt
    have := hqbij.1 hεt.symm
    rw [← this]
    exact ht
  · intro hg
    obtain ⟨x, hx⟩ := hFT₁ g hg
    rw [← hψε] at hx
    have h1 := hεinj hx
    have h2 : ((ψ g : ↥L) : G) = (x : G) := by
      rw [← h1]
      rfl
    rw [h2]
    exact (Subgroup.mem_inf.mp x.2).1

end CFSG.RankThree.PartOne.S13K
