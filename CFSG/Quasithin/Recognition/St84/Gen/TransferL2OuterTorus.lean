module

public import CFSG.Quasithin.Recognition.St84.Gen.SL2TorusAut
public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
public import CFSG.Quasithin.EmptyFaithful.S1421F112
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Torus
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
import CFSG.Quasithin.EmptyFaithful.R3c18P

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

private theorem exists_conj_borel_sl2FieldAut_of_map_utri {F : Type} [Field F] [Finite F]
    [CharP F 2] (θ : SL(2, F) ≃* SL(2, F))
    (hU : ∀ x, θ x ∈ utri F ↔ x ∈ utri F) :
    ∃ (g : SL(2, F)) (σ : F ≃+* F), g ∈ borel F ∧
      ∀ x, θ x = g * sl2FieldAut σ x * g⁻¹ := by
  obtain ⟨g, σ, hg⟩ := exists_eq_conj_sl2FieldAut θ
  refine ⟨g, σ, ?_, hg⟩
  rw [mem_borel_iff]
  have h1 : g * utriElt (1 : F) * g⁻¹ ∈ utri F := by
    have h := (hU (utriElt (1 : F))).2 (utriElt_mem_utri 1)
    rw [hg, sl2FieldAut_utriElt] at h
    simpa using h
  have h2 : g 1 0 ^ 2 = 0 := by
    have h := h1.1
    rw [conj_utriElt_apply_10, mul_one] at h
    linear_combination (-1) * h
  exact pow_eq_zero_iff two_ne_zero |>.1 h2

private theorem sl2FieldAut_mul_conj {F : Type} [Field F] (σ : F ≃+* F) (x : SL(2, F)) :
    sl2FieldAut σ * MulAut.conj x =
      MulAut.conj (sl2FieldAut σ x) * sl2FieldAut σ := by
  apply MulEquiv.ext
  intro y
  show sl2FieldAut σ ((MulAut.conj x) y) =
    (MulAut.conj (sl2FieldAut σ x)) (sl2FieldAut σ y)
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem conj_injective_sl2 {F : Type} [Field F] [CharP F 2] :
    Function.Injective (MulAut.conj : SL(2, F) → MulAut (SL(2, F))) := by
  intro x y hxy
  have hc : y⁻¹ * x ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h := congrArg (fun f : MulAut (SL(2, F)) => f z) hxy
    rw [MulAut.conj_apply, MulAut.conj_apply] at h
    calc z * (y⁻¹ * x) = y⁻¹ * (y * z * y⁻¹) * x := by group
      _ = y⁻¹ * (x * z * x⁻¹) * x := by rw [← h]
      _ = (y⁻¹ * x) * z := by group
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at hc
  calc x = y * (y⁻¹ * x) := by group
    _ = y * 1 := by rw [hc]
    _ = y := mul_one y

private noncomputable def torusAutHom (F : Type*) [Field F] :
    Fˣ →* MulAut (SL(2, F)) :=
  MulAut.conj.comp (CFSG.Glauberman.Dickson.splitTorusSLHom F)

private theorem torusAutHom_injective {F : Type} [Field F] [CharP F 2] :
    Function.Injective (torusAutHom F) := by
  intro a b h
  have h' : MulAut.conj (torusElt a) = MulAut.conj (torusElt b) := h
  exact torusElt_injective (conj_injective_sl2 h')

private theorem conj_fixes_torus_of_commute {F : Type} [Field F] [Finite F] [CharP F 2]
    {φ ψ : MulAut (SL(2, F))} (hU : ∀ x, φ x ∈ utri F ↔ x ∈ utri F)
    {a : Fˣ} (hψ : ψ = MulAut.conj (torusElt a)) (hcomm : φ * ψ = ψ * φ) :
    φ (torusElt a) = torusElt a := by
  obtain ⟨g, σ, hg_borel, hg⟩ := exists_conj_borel_sl2FieldAut_of_map_utri φ hU
  obtain ⟨b, hb⟩ :=
    CFSG.Glauberman.Dickson.eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero g
      (mem_borel_iff.1 hg_borel)
  let s : F := g 0 1 * g 0 0
  have hg' : g = utriElt s * torusElt b := hb
  have hφ : φ = MulAut.conj g * sl2FieldAut σ := by
    apply MulEquiv.ext
    intro x
    rw [hg x, MulAut.mul_apply, MulAut.conj_apply]
  have hσψ : sl2FieldAut σ * ψ =
      MulAut.conj (sl2FieldAut σ (torusElt a)) * sl2FieldAut σ := by
    rw [hψ, sl2FieldAut_mul_conj, sl2FieldAut_torusElt]
  have hmid : sl2FieldAut σ * ψ * (sl2FieldAut σ)⁻¹ =
      MulAut.conj (sl2FieldAut σ (torusElt a)) := by
    rw [hσψ]
    group
  have hexp : φ * ψ * φ⁻¹ =
      MulAut.conj (g * sl2FieldAut σ (torusElt a) * g⁻¹) := by
    rw [hφ, mul_inv_rev]
    calc MulAut.conj g * sl2FieldAut σ * ψ * ((sl2FieldAut σ)⁻¹ * (MulAut.conj g)⁻¹)
        = MulAut.conj g * (sl2FieldAut σ * ψ * (sl2FieldAut σ)⁻¹) *
            (MulAut.conj g)⁻¹ := by group
      _ = MulAut.conj g * MulAut.conj (sl2FieldAut σ (torusElt a)) *
            (MulAut.conj g)⁻¹ := by rw [hmid]
      _ = MulAut.conj (g * sl2FieldAut σ (torusElt a) * g⁻¹) := by
        rw [← map_mul (MulAut.conj) g (sl2FieldAut σ (torusElt a)),
          ← map_inv (MulAut.conj) g,
          ← map_mul (MulAut.conj) (g * sl2FieldAut σ (torusElt a)) g⁻¹]
  have h_eq : MulAut.conj (torusElt a) =
      MulAut.conj (g * sl2FieldAut σ (torusElt a) * g⁻¹) := by
    rw [← hψ, ← hexp]
    rw [hcomm]
    group
  have hEq : g * sl2FieldAut σ (torusElt a) * g⁻¹ = torusElt a :=
    conj_injective_sl2 h_eq.symm
  rw [sl2FieldAut_torusElt] at hEq
  have hc : torusElt b * torusElt (Units.map (σ : F →* F) a) * (torusElt b)⁻¹ =
      torusElt (Units.map (σ : F →* F) a) := by
    rw [← torusElt_mul, mul_comm b (Units.map (σ : F →* F) a), torusElt_mul]
    group
  have hEq' : utriElt s * torusElt (Units.map (σ : F →* F) a) * (utriElt s)⁻¹ =
      torusElt a := by
    calc utriElt s * torusElt (Units.map (σ : F →* F) a) * (utriElt s)⁻¹
        = utriElt s *
            (torusElt b * torusElt (Units.map (σ : F →* F) a) * (torusElt b)⁻¹) *
            (utriElt s)⁻¹ := by rw [hc]
      _ = (utriElt s * torusElt b) * torusElt (Units.map (σ : F →* F) a) *
            (utriElt s * torusElt b)⁻¹ := by group
      _ = g * torusElt (Units.map (σ : F →* F) a) * g⁻¹ := by rw [← hg']
      _ = torusElt a := hEq
  have h00 := congrArg (fun g : SL(2, F) => g 0 0) hEq'
  sl2_simp at h00
  have hσa : Units.map (σ : F →* F) a = a := Units.ext (by simpa using h00)
  rw [hσa] at hEq
  rw [hφ, MulAut.mul_apply, sl2FieldAut_torusElt, hσa, MulAut.conj_apply]
  exact hEq

private theorem sl2FieldAut_mul {F : Type} [Field F] (σ σ' : F ≃+* F) :
    sl2FieldAut σ * sl2FieldAut σ' = sl2FieldAut (σ * σ') := by
  calc sl2FieldAut σ * sl2FieldAut σ'
      = (sl2FieldAut σ').trans (sl2FieldAut σ) := rfl
    _ = sl2FieldAut (σ'.trans σ) := (sl2FieldAut_trans σ' σ).symm
    _ = sl2FieldAut (σ * σ') := by
        congr 1

private theorem conj_torus_mul_conj_torus {F : Type} [Field F] [CharP F 2]
    (b b' : Fˣ) (σ σ' : F ≃+* F) :
    (MulAut.conj (torusElt b) * sl2FieldAut σ) *
        (MulAut.conj (torusElt b') * sl2FieldAut σ') =
      MulAut.conj (torusElt (b * Units.map (σ : F →* F) b')) *
        sl2FieldAut (σ * σ') := by
  calc
    (MulAut.conj (torusElt b) * sl2FieldAut σ) *
        (MulAut.conj (torusElt b') * sl2FieldAut σ')
      = MulAut.conj (torusElt b) *
          (sl2FieldAut σ * MulAut.conj (torusElt b')) * sl2FieldAut σ' := by group
    _ = MulAut.conj (torusElt b) *
          (MulAut.conj (sl2FieldAut σ (torusElt b')) * sl2FieldAut σ) *
          sl2FieldAut σ' := by
        rw [sl2FieldAut_mul_conj]
    _ = MulAut.conj (torusElt b) *
          (MulAut.conj (torusElt (Units.map (σ : F →* F) b')) * sl2FieldAut σ) *
          sl2FieldAut σ' := by
        rw [sl2FieldAut_torusElt]
    _ = (MulAut.conj (torusElt b) *
          MulAut.conj (torusElt (Units.map (σ : F →* F) b'))) *
          (sl2FieldAut σ * sl2FieldAut σ') := by group
    _ = MulAut.conj (torusElt b * torusElt (Units.map (σ : F →* F) b')) *
          (sl2FieldAut σ * sl2FieldAut σ') := by rw [← map_mul]
    _ = MulAut.conj (torusElt (b * Units.map (σ : F →* F) b')) *
          sl2FieldAut (σ * σ') := by rw [← torusElt_mul, sl2FieldAut_mul]

private theorem eq_of_conj_sl2FieldAut_eq {F : Type} [Field F] [CharP F 2]
    {b b' : Fˣ} {σ σ' : F ≃+* F}
    (h : MulAut.conj (torusElt b) * sl2FieldAut σ =
      MulAut.conj (torusElt b') * sl2FieldAut σ') :
    b = b' ∧ σ = σ' := by
  have h1 := congrArg (fun f : MulAut (SL(2, F)) => f (utriElt 1)) h
  have h1' : (b : F) ^ 2 = (b' : F) ^ 2 := by
    simpa [MulAut.mul_apply, MulAut.conj_apply, torusElt_mul_utriElt_mul_inv,
      sl2FieldAut_utriElt, utriElt_apply_01] using
      congrArg (fun g : SL(2, F) => g 0 1) h1
  have hb : b = b' := Units.ext (CharTwo.sq_injective h1')
  have hσ : σ = σ' := by
    ext x
    have hx := congrArg (fun f : MulAut (SL(2, F)) => f (utriElt x)) h
    have hx' : (b : F) ^ 2 * σ x = (b' : F) ^ 2 * σ' x := by
      simpa [MulAut.mul_apply, MulAut.conj_apply, torusElt_mul_utriElt_mul_inv,
        sl2FieldAut_utriElt, utriElt_apply_01] using
        congrArg (fun g : SL(2, F) => g 0 1) hx
    rw [hb] at hx'
    exact mul_left_cancel₀ (pow_ne_zero 2 (Units.ne_zero b')) hx'
  exact ⟨hb, hσ⟩

theorem exists_torusElt_conj_sl2FieldAut_of_fix {F : Type} [Field F] [Finite F] [CharP F 2]
    (θ : SL(2, F) ≃* SL(2, F)) (hU : ∀ x, θ x ∈ utri F ↔ x ∈ utri F) {A : Set Fˣ}
    (hA : ∃ a ∈ A, a ≠ 1) (hT : ∀ a ∈ A, θ (torusElt a) = torusElt a) :
    ∃ (b : Fˣ) (σ : F ≃+* F), (∀ a ∈ A, σ (a : F) = a) ∧
      ∀ x, θ x = torusElt b * sl2FieldAut σ x * (torusElt b)⁻¹ := by
  obtain ⟨g, σ, hg_borel, hg⟩ :=
    exists_conj_borel_sl2FieldAut_of_map_utri θ hU
  obtain ⟨b, hb⟩ :=
    CFSG.Glauberman.Dickson.eq_unipotentSLAddChar_mul_splitTorusSLHom_of_lowerLeft_eq_zero g
      (mem_borel_iff.1 hg_borel)
  let s : F := g 0 1 * g 0 0
  have hg' : g = utriElt s * torusElt b := hb
  have hkey : ∀ a ∈ A, g * torusElt (Units.map (σ : F →* F) a) * g⁻¹ = torusElt a := by
    intro a ha
    have h := hT a ha
    rwa [hg, sl2FieldAut_torusElt] at h
  have hconj : ∀ a ∈ A,
      utriElt s * torusElt (Units.map (σ : F →* F) a) * (utriElt s)⁻¹ = torusElt a := by
    intro a ha
    have hcomm : torusElt b * torusElt (Units.map (σ : F →* F) a) =
        torusElt (Units.map (σ : F →* F) a) * torusElt b := by
      rw [← torusElt_mul, ← torusElt_mul, mul_comm b (Units.map (σ : F →* F) a)]
    have hcomm' : torusElt b * torusElt (Units.map (σ : F →* F) a) * (torusElt b)⁻¹ =
        torusElt (Units.map (σ : F →* F) a) := by
      rw [hcomm]
      group
    calc utriElt s * torusElt (Units.map (σ : F →* F) a) * (utriElt s)⁻¹
        = utriElt s * (torusElt b * torusElt (Units.map (σ : F →* F) a) * (torusElt b)⁻¹) *
            (utriElt s)⁻¹ := by rw [hcomm']
      _ = (utriElt s * torusElt b) * torusElt (Units.map (σ : F →* F) a) *
            (utriElt s * torusElt b)⁻¹ := by group
      _ = g * torusElt (Units.map (σ : F →* F) a) * g⁻¹ := by rw [← hg']
      _ = torusElt a := hkey a ha
  have hdiag : ∀ a ∈ A, Units.map (σ : F →* F) a = a := by
    intro a ha
    have h := congrArg (fun g : SL(2, F) => g 0 0) (hconj a ha)
    sl2_simp at h
    exact Units.ext (by simpa using h)
  have hs : s = 0 := by
    obtain ⟨a0, ha0A, ha0ne⟩ := hA
    have h01 := congrArg (fun g : SL(2, F) => g 0 1) (hconj a0 ha0A)
    rw [hdiag a0 ha0A] at h01
    sl2_simp at h01
    rw [Units.val_inv_eq_inv_val] at h01
    rw [CharTwo.neg_eq] at h01
    have h01' : (a0 : F) * s + s * (a0 : F)⁻¹ = 0 := by simpa using h01
    have ha01 : (a0 : F) ≠ 1 := fun h => ha0ne (Units.ext h)
    have ha02 : (a0 : F) ^ 2 ≠ 1 := by
      intro h
      exact ha01 (CharTwo.sq_injective (by simpa using h))
    have hbinv : (a0 : F)⁻¹ - (a0 : F) ≠ 0 := by
      intro h0
      apply ha02
      have h1 : (a0 : F)⁻¹ = (a0 : F) := sub_eq_zero.1 h0
      have h2 : (a0 : F) * (a0 : F) = 1 := by
        calc (a0 : F) * (a0 : F) = (a0 : F) * (a0 : F)⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel₀ (Units.ne_zero a0)
      simpa [pow_two] using h2
    have h2 : s * ((a0 : F)⁻¹ - (a0 : F)) = 0 := by
      rw [CharTwo.sub_eq_add]
      calc s * ((a0 : F)⁻¹ + (a0 : F)) = s * (a0 : F)⁻¹ + s * (a0 : F) := by ring
        _ = (a0 : F) * s + s * (a0 : F)⁻¹ := by ring
        _ = 0 := h01'
    exact (mul_eq_zero.mp h2).resolve_right hbinv
  refine ⟨b, σ, ?_, ?_⟩
  · intro a ha
    exact congrArg Units.val (hdiag a ha)
  · intro x
    rw [hg x, hg', hs, utriElt_zero]
    group

private theorem exists_torusElt_fieldAut_pair {F : Type} [Field F] [Finite F] [CharP F 2]
    (θ : SL(2, F) ≃* SL(2, F)) (hU : ∀ x, θ x ∈ utri F ↔ x ∈ utri F) {A : Set Fˣ}
    (hA : ∃ a ∈ A, a ≠ 1) (hT : ∀ a ∈ A, θ (torusElt a) = torusElt a) :
    ∃ p : Fˣ × (F ≃+* F), (∀ a ∈ A, p.2 (a : F) = a) ∧
      ∀ x, θ x = torusElt p.1 * sl2FieldAut p.2 x * (torusElt p.1)⁻¹ := by
  obtain ⟨b, σ, hσ, hθ⟩ := exists_torusElt_conj_sl2FieldAut_of_fix θ hU hA hT
  exact ⟨(b, σ), hσ, hθ⟩

private theorem rho_eq_conj_of_mem_L {G : Type} [Group G] {L : Subgroup G} [Finite ↥L]
    {F : Type} [Field F] [Finite F] [CharP F 2] (γ : ↥L →* SL(2, F))
    (hγ : Function.Surjective γ)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (hρ : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L),
      ρ g (γ l) = γ ⟨(g : G) * (l : G) * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp g.2 (l : G)).mp l.2⟩)
    {g : G} (hgN : g ∈ Subgroup.normalizer (L : Set G)) (hgL : g ∈ L) :
    ρ ⟨g, hgN⟩ = MulAut.conj (γ ⟨g, hgL⟩) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨l, rfl⟩ := hγ x
  rw [hρ]
  have harg : (⟨(g : G) * (l : G) * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (show g ∈ Subgroup.normalizer (L : Set G) from hgN)
        (l : G)).mp l.2⟩ : ↥L) = ⟨g, hgL⟩ * l * ⟨g, hgL⟩⁻¹ := by
    apply Subtype.ext
    rfl
  rw [harg, map_mul, map_mul, map_inv, MulAut.conj_apply]

private theorem exists_conjAction_data {G : Type} [Group G] {L T D' : Subgroup G}
    [Finite ↥L] {n : ℕ} (hn : 1 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L))
    (hT : IsSylowTwoOf T L) (hD' : D' ≤ L ⊓ Subgroup.normalizer (T : Set G))
    (hD'card : Nat.card D' = 2 ^ n - 1) :
    ∃ (γ : ↥L →* SL(2, GaloisField 2 n))
      (ρ : ↥(Subgroup.normalizer (L : Set G)) →*
        MulAut (SL(2, GaloisField 2 n))),
      Function.Surjective γ ∧ γ.ker = (pCoreOf 2 L).subgroupOf L ∧
      (T.subgroupOf L).map γ = utri (GaloisField 2 n) ∧
      (D'.subgroupOf L).map γ = torus (GaloisField 2 n) ∧
      (∀ (g : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L),
        ρ g (γ l) = γ ⟨(g : G) * (l : G) * (g : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp g.2 (l : G)).mp l.2⟩) ∧
      ρ.ker.map (Subgroup.normalizer (L : Set G)).subtype = trivOTwoQuot L ∧
      (∀ g : ↥(Subgroup.normalizer (L : Set G)),
        (g : G) ∈ Subgroup.normalizer (T : Set G) →
        ∀ x, ρ g x ∈ utri (GaloisField 2 n) ↔ x ∈ utri (GaloisField 2 n)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 n
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  obtain ⟨γ, hγsurj, hγker, hTγ, hD'γ⟩ :=
    exists_conj_SL2_of_isL2Quot hn hq hT hD' hD'card
  let QL : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hγker' : γ.ker = QL := by
    rw [hγker, CFSG.openPCoreOf_subgroupOf]
  let e : (↥L ⧸ QL) ≃* SL(2, F) :=
    QuotientGroup.liftEquiv QL hγsurj hγker'.symm
  have he : ∀ l : ↥L, e (QuotientGroup.mk l) = γ l := fun l =>
    QuotientGroup.liftEquiv_mk QL hγsurj hγker'.symm l
  let φ : ↥N →* MulAut (↥L ⧸ QL) :=
    CFSG.GroupTheory.conjModPCore 2 L N le_rfl
  let ρ : ↥N →* MulAut (SL(2, F)) := (MulAut.congr e).toMonoidHom.comp φ
  have hρ : ∀ (g : ↥N) (l : ↥L),
      ρ g (γ l) = γ ⟨(g : G) * (l : G) * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp g.2 (l : G)).mp l.2⟩ := by
    intro g l
    calc ρ g (γ l)
        = MulAut.congr e (φ g) (γ l) := rfl
      _ = MulAut.congr e (φ g) (e (QuotientGroup.mk l)) := by rw [he l]
      _ = e (φ g (QuotientGroup.mk l)) := by
          rw [MulAut.congr_apply]
          simp [MulEquiv.trans_apply]
      _ = e (QuotientGroup.mk ⟨(g : G) * (l : G) * (g : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp g.2 (l : G)).mp l.2⟩) := by
          rw [CFSG.GroupTheory.conjModPCore_mk]
      _ = γ ⟨(g : G) * (l : G) * (g : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp g.2 (l : G)).mp l.2⟩ := he _
  have hkerρ : ρ.ker = φ.ker :=
    MonoidHom.ker_comp_of_injective φ (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective
  have hker : ρ.ker.map N.subtype = trivOTwoQuot L := by
    rw [hkerρ]
    ext m
    rw [CFSG.GroupTheory.mem_map_ker_conjModPCore_iff, mem_trivOTwoQuot]
  have hU : ∀ g : ↥N, (g : G) ∈ Subgroup.normalizer (T : Set G) →
      ∀ x, ρ g x ∈ utri F ↔ x ∈ utri F := by
    intro g hgT x
    have hmap_le : (utri F).map (ρ g).toMonoidHom ≤ utri F := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [← hTγ] at hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
      change ρ g (γ l) ∈ utri F
      rw [hρ, ← hTγ]
      refine Subgroup.mem_map_of_mem γ (Subgroup.mem_subgroupOf.mpr ?_)
      exact (Subgroup.mem_normalizer_iff.mp hgT (l : G)).mp
        (Subgroup.mem_subgroupOf.mp hl)
    have hcard : Nat.card ↥((utri F).map (ρ g).toMonoidHom) = Nat.card ↥(utri F) :=
      Subgroup.card_map_of_injective (ρ g).injective
    have heq : (utri F).map (ρ g).toMonoidHom = utri F :=
      Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)
    exact mem_iff_of_map_mulEquiv_eq (ρ g) heq x
  exact ⟨γ, ρ, hγsurj, hγker, hTγ, hD'γ, hρ, hker, hU⟩

private theorem relIndex_trivOTwoQuot_eq_card_map {G : Type} [Group G] {L : Subgroup G}
    [Finite ↥L] {F : Type} [Field F] [Finite F] [CharP F 2]
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (hker : ρ.ker.map (Subgroup.normalizer (L : Set G)).subtype = trivOTwoQuot L)
    {X : Subgroup G} (hX : X ≤ Subgroup.normalizer (L : Set G)) :
    (trivOTwoQuot L).relIndex X =
      Nat.card ↥((X.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ) := by
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let XN : Subgroup ↥N := X.subgroupOf N
  have hK : (trivOTwoQuot L).subgroupOf N = ρ.ker := by
    rw [← hker]
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective ρ.ker
  calc (trivOTwoQuot L).relIndex X
      = ((trivOTwoQuot L).subgroupOf N).relIndex XN :=
        (Subgroup.relIndex_subgroupOf hX).symm
    _ = ρ.ker.relIndex XN := by rw [hK]
    _ = Nat.card ↥(XN.map ρ) := Subgroup.relIndex_ker XN ρ

private theorem exists_outerTorus_image {G : Type} [Group G] {L T D D' : Subgroup G}
    [Finite ↥L] {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF4 : 4 ≤ Nat.card F) (γ : ↥L →* SL(2, F)) (hγ : Function.Surjective γ)
    (hγker : γ.ker = (pCoreOf 2 L).subgroupOf L)
    (hTγ : (T.subgroupOf L).map γ = utri F)
    (hD'γ : (D'.subgroupOf L).map γ = torus F)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (hρ : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (l : ↥L),
      ρ g (γ l) = γ ⟨(g : G) * (l : G) * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp g.2 (l : G)).mp l.2⟩)
    (hρker : ρ.ker.map (Subgroup.normalizer (L : Set G)).subtype = trivOTwoQuot L)
    {D : Subgroup G} (hDL : D ≤ Subgroup.normalizer (L : Set G))
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) (hD'leL : D' ≤ L)
    (hDD' : ∀ d ∈ D, ∀ t ∈ D', d * t = t * d) :
    ∃ A : Subgroup Fˣ,
      Nat.card A = Nat.card ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ) ∧
      (∀ a ∈ A, MulAut.conj (torusElt a) ∈
        (D.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ) ∧
      (∀ d : ↥(D.subgroupOf (Subgroup.normalizer (L : Set G))), ∃ a ∈ A,
        ρ d = MulAut.conj (torusElt a)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let K : Subgroup (MulAut (SL(2, F))) := (D.subgroupOf N).map ρ
  let f : Fˣ →* MulAut (SL(2, F)) := torusAutHom F
  let A : Subgroup Fˣ := K.comap f
  have hKle : K ≤ f.range := by
    rintro _ ⟨d, hd, rfl⟩
    have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
    have hdN : (d : G) ∈ N := d.2
    have hQ : (d : G) ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hDL hdD)
    have hTfix : ∀ t ∈ D', (d : G) * t * (d : G)⁻¹ = t := by
      intro t ht
      rw [hDD' (d : G) hdD t ht]
      group
    obtain ⟨t, htD', ht⟩ := exists_mem_torus_conj_mem_of_normalizes (F := F) hF4
      (L := L) (Q := pCoreOf 2 L) (U' := T) (T' := D') γ hγ hγker hTγ hD'leL hD'γ
      (hDL hdD) hQ (hDT hdD) hTfix
    have htL : t ∈ L := hD'leL htD'
    have htN : t ∈ N := Subgroup.le_normalizer htL
    have huN : t⁻¹ * (d : G) ∈ N :=
      N.mul_mem (N.inv_mem htN) (hDL hdD)
    have huK : t⁻¹ * (d : G) ∈ trivOTwoQuot L :=
      mem_trivOTwoQuot.mpr ⟨huN, ht⟩
    have huKer : (⟨t⁻¹ * (d : G), huN⟩ : ↥N) ∈ ρ.ker := by
      rw [← Subgroup.mem_map_iff_mem (Subgroup.subtype_injective N)]
      rw [hρker]
      exact huK
    have hd_eq : d = ⟨t, htN⟩ * ⟨t⁻¹ * (d : G), huN⟩ := by
      apply Subtype.ext
      change (d : G) = t * (t⁻¹ * (d : G))
      group
    have hρd : ρ d = ρ ⟨t, htN⟩ := by
      rw [hd_eq, map_mul, MonoidHom.mem_ker.mp huKer, mul_one]
    have hρt : ρ ⟨t, htN⟩ = MulAut.conj (γ ⟨t, htL⟩) :=
      rho_eq_conj_of_mem_L γ hγ ρ hρ htN htL
    have hγt : γ ⟨t, htL⟩ ∈ torus F := by
      rw [← hD'γ]
      exact Subgroup.mem_map_of_mem γ (Subgroup.mem_subgroupOf.mpr htD')
    obtain ⟨a, ha⟩ := eq_torusElt_of_mem_torus hγt
    refine ⟨a, ?_⟩
    calc f a = MulAut.conj (torusElt a) := rfl
      _ = MulAut.conj (γ ⟨t, htL⟩) := by rw [ha]
      _ = ρ ⟨t, htN⟩ := hρt.symm
      _ = ρ d := hρd.symm
  have hAcard : Nat.card A = Nat.card K := by
    have hmap : A.map f = K := Subgroup.map_comap_eq_self hKle
    rw [← hmap, Subgroup.card_map_of_injective (torusAutHom_injective (F := F))]
  refine ⟨A, hAcard, ?_, ?_⟩
  · intro a ha
    exact Subgroup.mem_comap.mp ha
  · intro d
    have hmemK : ρ d ∈ K := Subgroup.mem_map_of_mem ρ d.2
    obtain ⟨a, ha⟩ := hKle hmemK
    refine ⟨a, ?_, ?_⟩
    · rw [Subgroup.mem_comap]
      rwa [ha]
    · rw [← ha]
      rfl

private theorem eq_one_of_conj_torus_pow_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {b : Fˣ} {m : ℕ} (hodd : Odd (Nat.card Fˣ))
    (h : (MulAut.conj (torusElt b)) ^ (2 ^ m) = 1) : b = 1 := by
  have hpow : (MulAut.conj (torusElt b)) ^ (2 ^ m) =
      MulAut.conj ((torusElt b) ^ (2 ^ m)) :=
    (map_pow (MulAut.conj) (torusElt b) (2 ^ m)).symm
  rw [hpow] at h
  have hcentral : (torusElt b) ^ (2 ^ m) ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hxy := congrArg (fun f : MulAut (SL(2, F)) => f y) h
    rw [MulAut.conj_apply, MulAut.one_apply] at hxy
    calc y * ((torusElt b) ^ (2 ^ m)) =
        (((torusElt b) ^ (2 ^ m)) * y * ((torusElt b) ^ (2 ^ m))⁻¹) *
          ((torusElt b) ^ (2 ^ m)) := by rw [hxy]
      _ = ((torusElt b) ^ (2 ^ m)) * y := by group
  rw [center_sl2_eq_bot, Subgroup.mem_bot] at hcentral
  have hbpow : b ^ (2 ^ m) = 1 := by
    have h1 : torusElt (b ^ (2 ^ m)) = (torusElt b) ^ (2 ^ m) := by
      simpa [torusElt] using
        map_pow (CFSG.Glauberman.Dickson.splitTorusSLHom F) b (2 ^ m)
    refine torusElt_injective ?_
    rw [h1, hcentral, torusElt_one]
  have hdvd : orderOf b ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.mpr hbpow
  have hbodd : Odd (orderOf b) := Odd.of_dvd_nat hodd (orderOf_dvd_natCard b)
  have hcop : Nat.Coprime (orderOf b) (2 ^ m) :=
    (Nat.coprime_two_left.mpr hbodd).symm.pow_right m
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl (orderOf b)) hdvd)

private theorem pow_two_mul_eq_self {F : Type} [Field F] [Fintype F] {N m : ℕ}
    (hF : Fintype.card F = 2 ^ N) (h : N ∣ m) (x : F) : x ^ (2 ^ m) = x := by
  obtain ⟨k, rfl⟩ := h
  have hbase : x ^ (2 ^ N) = x := by
    rw [← hF, FiniteField.pow_card]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, hbase]

private theorem fieldAut_pow_r_eq_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {r e : ℕ} (he : 2 ≤ e) (hr : 1 ≤ r) (hFcard : Nat.card F = 2 ^ (r * e))
    (A : Subgroup Fˣ) (hAcard : Nat.card A = 2 ^ e - 1)
    (σ : F ≃+* F) (hfix : ∀ a ∈ A, σ (a : F) = a) : σ ^ r = 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨j, hσ⟩ := CFSG.Quasithin.R3c18.exists_frob_pow σ
  haveI : IsCyclic ↥A := isCyclic_subgroup_units A
  obtain ⟨g, hgord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
  have horder : orderOf g = 2 ^ e - 1 := by rw [hgord, hAcard]
  let gu : Fˣ := (g : Fˣ)
  have hguord : orderOf gu = 2 ^ e - 1 := by
    change orderOf (g : Fˣ) = 2 ^ e - 1
    rw [Subgroup.orderOf_coe g]
    exact horder
  have hfix_gu : σ (gu : F) = (gu : F) := hfix gu g.2
  have hgu_pow : gu ^ (2 ^ j) = gu := by
    apply Units.ext
    have h := hfix_gu
    rw [hσ] at h
    simpa using h
  have hgu_pow' : gu ^ (2 ^ j - 1) = 1 := by
    apply mul_right_cancel (b := gu)
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow), hgu_pow, one_mul]
  have hdvd : 2 ^ e - 1 ∣ 2 ^ j - 1 := by
    rw [← hguord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hgu_pow'
  have hej : e ∣ j := by
    have hg := Nat.gcd_eq_left_iff_dvd.mpr hdvd
    rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
    have h2 : 2 ^ e - 1 + 1 = 2 ^ Nat.gcd e j - 1 + 1 := by rw [hg]
    rw [Nat.sub_add_cancel (Nat.one_le_two_pow (n := e)),
      Nat.sub_add_cancel (Nat.one_le_two_pow (n := Nat.gcd e j))] at h2
    have heq : e = Nat.gcd e j := Nat.pow_right_injective (by norm_num) h2
    rw [heq]
    exact Nat.gcd_dvd_right e j
  apply RingEquiv.ext
  intro x
  rw [CFSG.Quasithin.R3c18.pow_iter_frob σ hσ r x, ← pow_mul 2 j r]
  have hFint : Fintype.card F = 2 ^ (r * e) := by
    rw [Fintype.card_eq_nat_card, hFcard]
  have hdvd_exp : r * e ∣ j * r := by
    rw [mul_comm r e]
    exact Nat.mul_dvd_mul_right hej r
  simpa using pow_two_mul_eq_self hFint hdvd_exp x

private theorem exists_ne_one_of_card_units {F : Type} [Field F] [Finite F]
    (A : Subgroup Fˣ) {e : ℕ} (he : 2 ≤ e) (hcard : Nat.card A = 2 ^ e - 1) :
    ∃ a ∈ A, a ≠ 1 := by
  haveI : Finite ↥A := inferInstance
  have hgt : 1 < Nat.card A := by
    rw [hcard]
    have h4 : 4 ≤ 2 ^ e := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  haveI : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.mp hgt
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥A)
  exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩

private theorem torus_action_fixes {G : Type} [Group G] {L T D P : Subgroup G}
    [Finite ↥L] {F : Type} [Field F] [Finite F] [CharP F 2]
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (hUρ : ∀ g : ↥(Subgroup.normalizer (L : Set G)),
      (g : G) ∈ Subgroup.normalizer (T : Set G) →
      ∀ x, ρ g x ∈ utri F ↔ x ∈ utri F)
    {A : Subgroup Fˣ}
    (hAmem : ∀ a ∈ A, MulAut.conj (torusElt a) ∈
      (D.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ)
    (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hPD : ∀ c ∈ P, ∀ d ∈ D, c * d = d * c) :
    ∀ c : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))), ∀ a ∈ A,
      ρ c.1 (torusElt a) = torusElt a := by
  intro c a ha
  obtain ⟨d, hd, hda⟩ := Subgroup.mem_map.mp (hAmem a ha)
  have hcP : (c.1 : G) ∈ P := Subgroup.mem_subgroupOf.mp c.2
  have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
  have hcommG : (c.1 : G) * (d : G) = (d : G) * (c.1 : G) :=
    hPD (c.1 : G) hcP (d : G) hdD
  have hcommN : c.1 * d = d * c.1 := Subtype.ext hcommG
  have hcomm : ρ c.1 * ρ d = ρ d * ρ c.1 := by
    rw [← map_mul, ← map_mul, hcommN]
  have hU : ∀ x, ρ c.1 x ∈ utri F ↔ x ∈ utri F := hUρ c.1 (hPT hcP)
  exact conj_fixes_torus_of_commute hU hda hcomm

private theorem exists_torus_pair_data {G : Type} [Group G] {L T D P : Subgroup G}
    [Finite ↥L] {F : Type} [Field F] [Finite F] [CharP F 2] {e : ℕ} (he : 2 ≤ e)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (hUρ : ∀ g : ↥(Subgroup.normalizer (L : Set G)),
      (g : G) ∈ Subgroup.normalizer (T : Set G) →
      ∀ x, ρ g x ∈ utri F ↔ x ∈ utri F)
    {A : Subgroup Fˣ} (hAcard : Nat.card A = 2 ^ e - 1)
    (hAmem : ∀ a ∈ A, MulAut.conj (torusElt a) ∈
      (D.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ)
    (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hPD : ∀ c ∈ P, ∀ d ∈ D, c * d = d * c) :
    ∃ pairOf : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))) → Fˣ × (F ≃+* F),
      (∀ c, ∀ a ∈ A, (pairOf c).2 (a : F) = a) ∧
      (∀ c x, ρ c.1 x = torusElt (pairOf c).1 * sl2FieldAut (pairOf c).2 x *
        (torusElt (pairOf c).1)⁻¹) ∧
      pairOf 1 = (1, RingEquiv.refl F) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let P_N : Subgroup ↥N := P.subgroupOf N
  have hAne : ∃ a ∈ A, a ≠ 1 := exists_ne_one_of_card_units A he hAcard
  have hFix : ∀ c : ↥P_N, ∀ a ∈ A, ρ c.1 (torusElt a) = torusElt a :=
    torus_action_fixes (D := D) (A := A) ρ hUρ hAmem hPT hPD
  let pairOf : ↥P_N → Fˣ × (F ≃+* F) := fun c =>
    Classical.choose (exists_torusElt_fieldAut_pair (ρ c.1) (hUρ c.1 (hPT (by
      exact Subgroup.mem_subgroupOf.mp c.2))) hAne (hFix c))
  have pair_spec : ∀ c : ↥P_N,
      (∀ a ∈ A, (pairOf c).2 (a : F) = a) ∧
      ∀ x, ρ c.1 x = torusElt (pairOf c).1 * sl2FieldAut (pairOf c).2 x *
        (torusElt (pairOf c).1)⁻¹ := fun c =>
    Classical.choose_spec (exists_torusElt_fieldAut_pair (ρ c.1)
      (hUρ c.1 (hPT (by exact Subgroup.mem_subgroupOf.mp c.2))) hAne (hFix c))
  have pair_one : pairOf 1 = (1, RingEquiv.refl F) := by
    have hforms : MulAut.conj (torusElt (pairOf 1).1) * sl2FieldAut (pairOf 1).2 =
        MulAut.conj (torusElt (1 : Fˣ)) * sl2FieldAut (RingEquiv.refl F) := by
      have hL : MulAut.conj (torusElt (pairOf 1).1) * sl2FieldAut (pairOf 1).2 =
          ρ (1 : ↥N) := by
        apply MulEquiv.ext
        intro x
        rw [MulAut.mul_apply, MulAut.conj_apply]
        exact ((pair_spec 1).2 x).symm
      have hR : MulAut.conj (torusElt (1 : Fˣ)) * sl2FieldAut (RingEquiv.refl F) = 1 := by
        simp [torusElt_one, sl2FieldAut_refl]
        rfl
      rw [hL, map_one ρ, hR]
    obtain ⟨h1, h2⟩ := eq_of_conj_sl2FieldAut_eq hforms
    exact Prod.ext h1 h2
  exact ⟨pairOf, fun c a ha => (pair_spec c).1 a ha, fun c x => (pair_spec c).2 x,
    pair_one⟩

private theorem exists_sigmaOf_of_pair_data {G : Type} [Group G] {L T D P : Subgroup G}
    {F : Type} [Field F] [CharP F 2]
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (pairOf : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))) → Fˣ × (F ≃+* F))
    (hpair : ∀ c x, ρ c.1 x = torusElt (pairOf c).1 * sl2FieldAut (pairOf c).2 x *
      (torusElt (pairOf c).1)⁻¹)
    (pair_one : pairOf 1 = (1, RingEquiv.refl F)) :
    ∃ σOf : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))) →* (F ≃+* F),
      ∀ c, σOf c = (pairOf c).2 := by
  let σOf : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))) →* (F ≃+* F) :=
    { toFun := fun c => (pairOf c).2
      map_one' := by
        show (pairOf 1).2 = 1
        rw [pair_one]
        rfl
      map_mul' := by
        intro c c'
        show (pairOf (c * c')).2 = (pairOf c).2 * (pairOf c').2
        let p := pairOf c
        let q := pairOf c'
        let qq := pairOf (c * c')
        have hprod := conj_torus_mul_conj_torus p.1 q.1 p.2 q.2
        have hforms : MulAut.conj (torusElt qq.1) * sl2FieldAut qq.2 =
            MulAut.conj (torusElt (p.1 * Units.map (p.2 : F →* F) q.1)) *
              sl2FieldAut (p.2 * q.2) := by
          have hL : MulAut.conj (torusElt qq.1) * sl2FieldAut qq.2 = ρ (c * c').1 := by
            apply MulEquiv.ext
            intro x
            rw [MulAut.mul_apply, MulAut.conj_apply]
            exact (hpair (c * c') x).symm
          have hR : MulAut.conj (torusElt (p.1 * Units.map (p.2 : F →* F) q.1)) *
              sl2FieldAut (p.2 * q.2) = ρ c.1 * ρ c'.1 := by
            dsimp only [p, q]
            rw [← hprod]
            have hc_form : MulAut.conj (torusElt (pairOf c).1) * sl2FieldAut (pairOf c).2 =
                ρ c.1 := by
              apply MulEquiv.ext
              intro x
              rw [MulAut.mul_apply, MulAut.conj_apply]
              exact (hpair c x).symm
            have hc'_form : MulAut.conj (torusElt (pairOf c').1) * sl2FieldAut (pairOf c').2 =
                ρ c'.1 := by
              apply MulEquiv.ext
              intro x
              rw [MulAut.mul_apply, MulAut.conj_apply]
              exact (hpair c' x).symm
            rw [hc_form, hc'_form]
          calc MulAut.conj (torusElt qq.1) * sl2FieldAut qq.2 = ρ (c * c').1 := hL
            _ = ρ c.1 * ρ c'.1 := by rw [show (c * c').1 = c.1 * c'.1 from rfl, map_mul]
            _ = _ := hR.symm
        obtain ⟨-, h2⟩ := eq_of_conj_sl2FieldAut_eq hforms
        simpa [p, q, qq] using h2 }
  exact ⟨σOf, fun c => rfl⟩

private theorem exists_sigmaOf {G : Type} [Group G] {L T D P : Subgroup G}
    [Finite ↥L] {F : Type} [Field F] [Finite F] [CharP F 2] {e : ℕ} (he : 2 ≤ e)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (hUρ : ∀ g : ↥(Subgroup.normalizer (L : Set G)),
      (g : G) ∈ Subgroup.normalizer (T : Set G) →
      ∀ x, ρ g x ∈ utri F ↔ x ∈ utri F)
    {A : Subgroup Fˣ} (hAcard : Nat.card A = 2 ^ e - 1)
    (hAmem : ∀ a ∈ A, MulAut.conj (torusElt a) ∈
      (D.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ)
    (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hPD : ∀ c ∈ P, ∀ d ∈ D, c * d = d * c) :
    ∃ (pairOf : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))) → Fˣ × (F ≃+* F))
      (σOf : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))) →* (F ≃+* F)),
      (∀ c, σOf c = (pairOf c).2) ∧
      (∀ c, ∀ a ∈ A, (pairOf c).2 (a : F) = a) ∧
      (∀ c x, ρ c.1 x = torusElt (pairOf c).1 * sl2FieldAut (pairOf c).2 x *
        (torusElt (pairOf c).1)⁻¹) := by
  obtain ⟨pairOf, hfix, hpair, pair_one⟩ :=
    exists_torus_pair_data (T := T) (D := D) (A := A) he ρ hUρ hAcard hAmem hPT hPD
  obtain ⟨σOf, hσ⟩ := exists_sigmaOf_of_pair_data (T := T) (D := D) ρ pairOf hpair pair_one
  exact ⟨pairOf, σOf, hσ, hfix, hpair⟩

private theorem sigmaOf_ker_eq {G : Type} [Group G] {L T D P : Subgroup G}
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (pairOf : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))) → Fˣ × (F ≃+* F))
    (σOf : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))) →* (F ≃+* F))
    (hσ : ∀ c, σOf c = (pairOf c).2)
    (hspec : ∀ c x, ρ c.1 x = torusElt (pairOf c).1 * sl2FieldAut (pairOf c).2 x *
      (torusElt (pairOf c).1)⁻¹)
    (hP : IsPGroup 2 P) (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hoddUnits : Odd (Nat.card Fˣ)) :
    σOf.ker = (ρ.ker).subgroupOf (P.subgroupOf (Subgroup.normalizer (L : Set G))) := by
  ext c
  rw [MonoidHom.mem_ker]
  constructor
  · intro hσc
    have hp : (pairOf c).2 = 1 := by rw [← hσ c]; exact hσc
    have hform : ρ c.1 = MulAut.conj (torusElt (pairOf c).1) := by
      apply MulEquiv.ext
      intro x
      rw [hspec c x, hp,
        show (1 : F ≃+* F) = RingEquiv.refl F from rfl, sl2FieldAut_refl]
      rw [MulAut.conj_apply]
      simp
    have hcP : (c.1 : G) ∈ P := Subgroup.mem_subgroupOf.mp c.2
    obtain ⟨m, hm⟩ := hP.exists_pow_pow_eq_one ⟨(c.1 : G), hcP⟩
    have hpow : (ρ c.1) ^ (2 ^ m) = 1 := by
      have hm' : (c.1 : ↥(Subgroup.normalizer (L : Set G))) ^ (2 ^ m) = 1 := by
        apply Subtype.ext
        simpa using hm
      calc (ρ c.1) ^ (2 ^ m) = ρ ((c.1) ^ (2 ^ m)) :=
            (map_pow ρ c.1 (2 ^ m)).symm
        _ = ρ 1 := by rw [hm']
        _ = 1 := map_one ρ
    have hb : (pairOf c).1 = 1 := by
      apply eq_one_of_conj_torus_pow_two hoddUnits
      rw [← hform]
      exact hpow
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hform, hb, torusElt_one]
    simp
  · intro hc
    have hcρ : c.1 ∈ ρ.ker := Subgroup.mem_subgroupOf.mp hc
    have hforms : MulAut.conj (torusElt (pairOf c).1) * sl2FieldAut (pairOf c).2 =
        MulAut.conj (torusElt (1 : Fˣ)) * sl2FieldAut (RingEquiv.refl F) := by
      have hL : MulAut.conj (torusElt (pairOf c).1) * sl2FieldAut (pairOf c).2 =
          ρ c.1 := by
        apply MulEquiv.ext
        intro x
        rw [MulAut.mul_apply, MulAut.conj_apply]
        exact (hspec c x).symm
      rw [hL, MonoidHom.mem_ker.mp hcρ]
      simp [torusElt_one, sl2FieldAut_refl]
      rfl
    obtain ⟨-, h2⟩ := eq_of_conj_sl2FieldAut_eq hforms
    rw [hσ c]
    rw [show (1 : F ≃+* F) = RingEquiv.refl F from rfl]
    exact h2

private theorem exists_fieldAutHom_of_torus_action {G : Type} [Group G]
    {L T D D' P : Subgroup G} [Finite ↥L] {F : Type} [Field F] [Finite F] [CharP F 2]
    {e r : ℕ} (he : 2 ≤ e) (hr1 : 1 ≤ r) (hFcard : Nat.card F = 2 ^ (r * e))
    (γ : ↥L →* SL(2, F)) (hγ : Function.Surjective γ)
    (hγker : γ.ker = (pCoreOf 2 L).subgroupOf L)
    (hTγ : (T.subgroupOf L).map γ = utri F)
    (hD'γ : (D'.subgroupOf L).map γ = torus F)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (hρker  : ρ.ker.map (Subgroup.normalizer (L : Set G)).subtype = trivOTwoQuot L)
    (hUρ : ∀ g : ↥(Subgroup.normalizer (L : Set G)),
      (g : G) ∈ Subgroup.normalizer (T : Set G) →
      ∀ x, ρ g x ∈ utri F ↔ x ∈ utri F)
    {A : Subgroup Fˣ} (hAcard : Nat.card A = 2 ^ e - 1)
    (hAmem : ∀ a ∈ A, MulAut.conj (torusElt a) ∈
      (D.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ)
    (hP : IsPGroup 2 P) (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hPD : ∀ c ∈ P, ∀ d ∈ D, c * d = d * c) :
    ∃ σOf : ↥(P.subgroupOf (Subgroup.normalizer (L : Set G))) →* (F ≃+* F),
      (∀ c, ∀ a ∈ A, σOf c (a : F) = a) ∧
      σOf.ker = (ρ.ker).subgroupOf (P.subgroupOf (Subgroup.normalizer (L : Set G))) ∧
      Nat.card ((P.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ) =
        Nat.card σOf.range := by
  classical
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let P_N : Subgroup ↥N := P.subgroupOf N
  have hoddUnits : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units, hFcard]
    have hpos : r * e ≠ 0 := by
      have : 0 < r * e := Nat.mul_pos (by omega) (by omega)
      omega
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two hpos) odd_one
  obtain ⟨pairOf, σOf, hσ, hpairfix, hspec⟩ :=
    exists_sigmaOf (D := D) (A := A) he ρ hUρ hAcard hAmem hPT hPD
  have hker : σOf.ker = (ρ.ker).subgroupOf P_N :=
    sigmaOf_ker_eq (D := D) ρ pairOf σOf hσ hspec hP hPT hoddUnits
  refine ⟨σOf, fun c a ha => by rw [hσ c]; exact hpairfix c a ha, hker, ?_⟩
  let ρP : ↥P_N →* MulAut (SL(2, F)) := ρ.comp P_N.subtype
  have hkerρP : ρP.ker = (ρ.ker).subgroupOf P_N := by
    ext x
    rfl
  calc Nat.card (P_N.map ρ) = Nat.card ρP.range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
    _ = ρP.ker.index := (Subgroup.index_ker ρP).symm
    _ = σOf.ker.index := by rw [hkerρP, hker]
    _ = Nat.card σOf.range := Subgroup.index_ker σOf

private theorem card_image_dvd_of_torus_action {G : Type} [Group G]
    {L T D D' P : Subgroup G} [Finite ↥L] {F : Type} [Field F] [Finite F] [CharP F 2]
    {e r : ℕ} (he : 2 ≤ e) (hr1 : 1 ≤ r) (hFcard : Nat.card F = 2 ^ (r * e))
    (γ : ↥L →* SL(2, F)) (hγ : Function.Surjective γ)
    (hγker : γ.ker = (pCoreOf 2 L).subgroupOf L)
    (hTγ : (T.subgroupOf L).map γ = utri F)
    (hD'γ : (D'.subgroupOf L).map γ = torus F)
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (SL(2, F)))
    (hρker : ρ.ker.map (Subgroup.normalizer (L : Set G)).subtype = trivOTwoQuot L)
    (hUρ : ∀ g : ↥(Subgroup.normalizer (L : Set G)),
      (g : G) ∈ Subgroup.normalizer (T : Set G) →
      ∀ x, ρ g x ∈ utri F ↔ x ∈ utri F)
    {A : Subgroup Fˣ} (hAcard : Nat.card A = 2 ^ e - 1)
    (hAmem : ∀ a ∈ A, MulAut.conj (torusElt a) ∈
      (D.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ)
    (hP : IsPGroup 2 P) (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hPD : ∀ c ∈ P, ∀ d ∈ D, c * d = d * c) :
    Nat.card ((P.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ) ∣ r := by
  classical
  obtain ⟨σOf, hfix, hker, hcard⟩ :=
    exists_fieldAutHom_of_torus_action he hr1 hFcard γ hγ hγker hTγ hD'γ ρ hρker hUρ
      hAcard hAmem hP hPT hPD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (F ≃+* F) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      Nat.prime_two F hFcard).2
  letI : IsCyclic (F ≃+* F) := hcyc
  haveI : IsCyclic ↥σOf.range := Subgroup.isCyclic _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥σOf.range)
  have hgr : g ^ r = 1 := by
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp g.2
    have h : (σOf c) ^ r = 1 := fieldAut_pow_r_eq_one he hr1 hFcard A hAcard (σOf c) (hfix c)
    apply Subtype.ext
    change ((g : F ≃+* F) ^ r) = 1
    rw [← hc]
    exact h
  have hdvd : orderOf g ∣ r := orderOf_dvd_iff_pow_eq_one.mpr hgr
  rw [hcard]
  simpa [hg] using hdvd

theorem relIndex_trivOTwoQuot_dvd_of_commute_outer_torus {G : Type} [Group G]
    {L T D' D P : Subgroup G} [Finite ↥L] {e r : ℕ} (he : 2 ≤ e)
    (hq : IsL2Quot (r * e) (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD' : D' ≤ L ⊓ Subgroup.normalizer (T : Set G)) (hD'card : Nat.card D' = 2 ^ (r * e) - 1)
    (hDL : D ≤ Subgroup.normalizer (L : Set G)) (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hDD' : ∀ d ∈ D, ∀ t ∈ D', d * t = t * d)
    (hDidx : (trivOTwoQuot L).relIndex D = 2 ^ e - 1)
    (hP : IsPGroup 2 P) (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (hPT : P ≤ Subgroup.normalizer (T : Set G)) (hPD : ∀ c ∈ P, ∀ d ∈ D, c * d = d * c) :
    (trivOTwoQuot L).relIndex P ∣ r := by
  by_cases hr0 : r = 0
  · subst r
    exact dvd_zero _
  have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (r * e)
  have hre1 : 1 ≤ r * e := by
    calc 1 = 1 * 1 := by norm_num
      _ ≤ r * e := Nat.mul_le_mul hr1 (by omega)
  have hre2 : 2 ≤ r * e := by
    calc 2 = 1 * 2 := by norm_num
      _ ≤ r * e := Nat.mul_le_mul hr1 he
  have hFcard : Nat.card F = 2 ^ (r * e) :=
    GaloisField.card 2 (r * e) (by omega)
  have hF4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (r * e) := Nat.pow_le_pow_right (by norm_num) hre2
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  obtain ⟨γ, ρ, hγ, hγker, hTγ, hD'γ, hρ, hρker, hUρ⟩ :=
    exists_conjAction_data (n := r * e) hre1 hq hT hD' hD'card
  have hD'leL : D' ≤ L := fun x hx => (Subgroup.mem_inf.mp (hD' hx)).1
  obtain ⟨A, hAcardK, hAmem, -⟩ :=
    exists_outerTorus_image (F := F) (T := T) (D := D) (D' := D')
      hF4 γ hγ hγker hTγ hD'γ ρ hρ hρker hDL hDT hD'leL hDD'
  have hDcardρ : Nat.card ((D.subgroupOf N).map ρ) = 2 ^ e - 1 := by
    rw [← relIndex_trivOTwoQuot_eq_card_map ρ hρker hDL, hDidx]
  have hAcard : Nat.card A = 2 ^ e - 1 := by rw [hAcardK, hDcardρ]
  have hdvd : Nat.card ((P.subgroupOf N).map ρ) ∣ r :=
    card_image_dvd_of_torus_action (F := F) (T := T) (D := D) (D' := D')
      he hr1 hFcard γ hγ hγker hTγ hD'γ ρ hρker hUρ hAcard hAmem hP hPT hPD
  rw [relIndex_trivOTwoQuot_eq_card_map ρ hρker hPL]
  exact hdvd

theorem le_trivOTwoQuot_of_commute_outer_torus {G : Type} [Group G]
    {L T D' D P : Subgroup G} [Finite ↥L] {e r : ℕ} (he : 2 ≤ e) (hr : Odd r)
    (hq : IsL2Quot (r * e) (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD' : D' ≤ L ⊓ Subgroup.normalizer (T : Set G)) (hD'card : Nat.card D' = 2 ^ (r * e) - 1)
    (hDL : D ≤ Subgroup.normalizer (L : Set G)) (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hDD' : ∀ d ∈ D, ∀ t ∈ D', d * t = t * d)
    (hDidx : (trivOTwoQuot L).relIndex D = 2 ^ e - 1)
    (hP : IsPGroup 2 P) (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (hPT : P ≤ Subgroup.normalizer (T : Set G)) (hPD : ∀ c ∈ P, ∀ d ∈ D, c * d = d * c) :
    P ≤ trivOTwoQuot L := by
  have hrOdd : Odd r := hr
  obtain ⟨k, hk⟩ := hr
  have hr1 : 1 ≤ r := by omega
  have hdvd := relIndex_trivOTwoQuot_dvd_of_commute_outer_torus he hq hT hD' hD'card hDL hDT
    hDD' hDidx hP hPL hPT hPD
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (r * e)
  have hre1 : 1 ≤ r * e := by
    calc 1 = 1 * 1 := by norm_num
      _ ≤ r * e := Nat.mul_le_mul hr1 (by omega)
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let P_N : Subgroup ↥N := P.subgroupOf N
  obtain ⟨γ, ρ, -, -, -, -, -, hρker, -⟩ :=
    exists_conjAction_data (n := r * e) hre1 hq hT hD' hD'card
  have hPN : IsPGroup 2 ↥P_N :=
    IsPGroup.of_equiv hP (Subgroup.subgroupOfEquivOfLe hPL).symm
  have hImg : IsPGroup 2 ↥(P_N.map ρ) := hPN.map ρ
  haveI : Finite ↥(P_N.map ρ) := inferInstance
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(P_N.map ρ))).mp hImg
  have hrel : (trivOTwoQuot L).relIndex P = Nat.card ↥(P_N.map ρ) :=
    relIndex_trivOTwoQuot_eq_card_map ρ hρker hPL
  have hcarddvd : Nat.card ↥(P_N.map ρ) ∣ r := by
    rw [← hrel]
    exact hdvd
  have hodd : Odd (Nat.card ↥(P_N.map ρ)) := Odd.of_dvd_nat hrOdd hcarddvd
  have hn0 : n = 0 := by
    by_contra hne
    rw [hn] at hodd
    exact hodd.not_two_dvd_nat (dvd_pow_self 2 hne)
  have hone : Nat.card ↥(P_N.map ρ) = 1 := by
    rw [hn, hn0]
    norm_num
  exact Subgroup.relIndex_eq_one.mp (by rw [hrel, hone])

theorem commutator_mem_pCoreOf_of_commute_outer_torus {G : Type} [Group G]
    {L T D' D : Subgroup G} [Finite ↥L] {e r : ℕ} (he : 2 ≤ e) (hr : Odd r)
    (hq : IsL2Quot (r * e) (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD' : D' ≤ L ⊓ Subgroup.normalizer (T : Set G)) (hD'card : Nat.card D' = 2 ^ (r * e) - 1)
    (hDL : D ≤ Subgroup.normalizer (L : Set G)) (hDT : D ≤ Subgroup.normalizer (T : Set G))
    (hDD' : ∀ d ∈ D, ∀ t ∈ D', d * t = t * d)
    (hDidx : (trivOTwoQuot L).relIndex D = 2 ^ e - 1)
    {c : G} (hc2 : ∃ m, c ^ (2 ^ m) = 1) (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hcT : c ∈ Subgroup.normalizer (T : Set G)) (hcD : ∀ d ∈ D, c * d = d * c) :
    ∀ l ∈ L, ⁅c, l⁆ ∈ pCoreOf 2 L := by
  have hzp : IsPGroup 2 (Subgroup.zpowers c) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    obtain ⟨m, hm⟩ := hc2
    have hg : orderOf g ∣ orderOf c := by
      rw [← Subgroup.orderOf_coe g]
      exact orderOf_dvd_of_mem_zpowers g.2
    have hcvd : orderOf c ∣ 2 ^ m := orderOf_dvd_iff_pow_eq_one.mpr hm
    exact ⟨m, orderOf_dvd_iff_pow_eq_one.mp (hg.trans hcvd)⟩
  have hcommZ : ∀ x ∈ Subgroup.zpowers c, ∀ d ∈ D, x * d = d * x := by
    intro x hx d hd
    have hsub : Subgroup.zpowers c ≤ Subgroup.centralizer ({d} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcD d hd)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsub hx)
  have hle := le_trivOTwoQuot_of_commute_outer_torus he hr hq hT hD' hD'card hDL hDT hDD'
    hDidx hzp (Subgroup.zpowers_le.mpr hcL) (Subgroup.zpowers_le.mpr hcT) hcommZ
  have hcK : c ∈ trivOTwoQuot L := hle (Subgroup.mem_zpowers c)
  intro l hl
  simpa [commutatorElement_def] using (mem_trivOTwoQuot.mp hcK).2 l hl

end CFSG.Quasithin.F112R.St84
