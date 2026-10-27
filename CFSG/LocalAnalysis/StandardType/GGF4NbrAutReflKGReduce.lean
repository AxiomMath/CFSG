module

public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGF4Refl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LieType.Steinberg.CentralExt.F4TwoMultiplier
import CFSG.LocalAnalysis.SeitzReduction.RankOneLemmaS
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGInnLocalDichotomy
import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley

namespace F4AutRefl

private theorem mem_normalizer_of_conj_mem_inv_conj_mem {M : Type} [Group M] {H : Subgroup M}
    {g : M} (h₁ : ∀ k ∈ H, g * k * g⁻¹ ∈ H) (h₂ : ∀ k ∈ H, g⁻¹ * k * g⁻¹⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h₁ k, fun hk => ?_⟩
  have h := h₂ _ hk
  rwa [show g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k by group] at h

private theorem inv_mul_mem_centralizer_of_conj {G : Type} [Group G] {X : Subgroup G} {b x : G}
    (h : ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹) :
    x⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  calc l * (x⁻¹ * b) = x⁻¹ * (x * l * x⁻¹) * b := by group
    _ = x⁻¹ * (b * l * b⁻¹) * b := by rw [h l hl]
    _ = (x⁻¹ * b) * l := by group

private theorem conj_mul_centralizer_eq {G : Type} [Group G] {X : Subgroup G} {g y c : G}
    (hgX : g ∈ X) (hc : c ∈ Subgroup.centralizer (X : Set G)) :
    g * (y * c) * g⁻¹ = g * y * g⁻¹ * c := by
  have h := Subgroup.mem_centralizer_iff.mp hc g hgX
  calc g * (y * c) * g⁻¹ = g * y * g⁻¹ * (g * c) * g⁻¹ := by group
    _ = g * y * g⁻¹ * (c * g) * g⁻¹ := by rw [h]
    _ = g * y * g⁻¹ * c := by group

theorem card_ker_dvd_two_of_adjointF4
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {L' : Type} [Group L'] [Finite L'] (hperf : commutator L' = ⊤)
    (η : L' →* ↥(adjointGroup .F4 K)) (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center L') :
    Nat.card η.ker ∣ 2 := by
  have : Group.IsPerfect L' := ⟨hperf⟩
  have : CharP K 2 := charP_two_of_card hK
  have hsec : (∃ σ : ↥(adjointGroup .F4 K) →* L', ∀ g, η (σ g) = g) → Nat.card η.ker ∣ 2 := by
    rintro ⟨σ, hσ⟩
    rw [CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section η hker σ hσ,
      Subgroup.card_bot]
    exact one_dvd 2
  rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3
  · have h2 := CFSG.LieType.Steinberg.CentralExt.F4Two.f4_two_card_ker_le_two
      (by simpa using hK) η hη hker
    have h1 : 0 < Nat.card η.ker := Nat.card_pos
    interval_cases Nat.card η.ker <;> norm_num
  · exact hsec (CFSG.LieType.Steinberg.CentralExt.FieldFour.f4_four_exists_section hK L' η hη hker)
  · refine hsec (CFSG.LieType.Steinberg.CentralExt.AdjointClosed.f4_exists_section_of_central ?_
      hη hker)
    rw [hK]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3

theorem exists_conj_of_inn {G : Type} [Group G] {X Bs : Subgroup G}
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hind : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ b ∈ Bs, ∃ x ∈ X, ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹ := by
  intro b hb
  obtain ⟨φ, hφI, hφ⟩ := hind b hb
  obtain ⟨r, hr⟩ := hI hφI
  obtain ⟨q, hq⟩ := θ.surjective r
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hφeq := eq_ggLAut_of_induces X θ (hBsN hb) hφ
  have hxN : (x : G) ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer x.2
  have hbN : b⁻¹ ∈ Subgroup.normalizer (X : Set G) := inv_mem (hBsN hb)
  have hcN : (x : G)⁻¹ * b⁻¹ ∈ Subgroup.normalizer (X : Set G) := mul_mem (inv_mem hxN) hbN
  have hc1 : ggLAut X θ ⟨(x : G)⁻¹ * b⁻¹, hcN⟩ = 1 := by
    have e : (⟨(x : G)⁻¹ * b⁻¹, hcN⟩ : Subgroup.normalizer (X : Set G)) =
        (⟨x, hxN⟩ : Subgroup.normalizer (X : Set G))⁻¹ * ⟨b⁻¹, hbN⟩ := Subtype.ext rfl
    rw [e, map_mul, map_inv, ← hφeq, ← hr, ggLAut_le_normalizer_eq_conj, hq, inv_mul_cancel]
  have hcC := mem_centralizer_of_ggLAut_eq_one X θ hX hc1
  refine ⟨(x : G)⁻¹, inv_mem x.2, fun l hl => ?_⟩
  have h1 : (x : G)⁻¹ * l * x ∈ X := mul_mem (mul_mem (inv_mem x.2) hl) x.2
  have h2 := Subgroup.mem_centralizer_iff.mp hcC _ h1
  calc b * l * b⁻¹ = ((x : G)⁻¹ * b⁻¹)⁻¹ * (((x : G)⁻¹ * l * x) * ((x : G)⁻¹ * b⁻¹)) := by
        group
    _ = ((x : G)⁻¹ * b⁻¹)⁻¹ * (((x : G)⁻¹ * b⁻¹) * ((x : G)⁻¹ * l * x)) := by rw [h2]
    _ = (x : G)⁻¹ * l * (x : G)⁻¹⁻¹ := by group

private theorem exists_pow_eq_one_conj_of_conj {G : Type} [Group G] {p : ℕ} (hp : Odd p)
    {X : Subgroup G} (hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1)
    {b x : G} (hbp : b ^ p = 1) (hxX : x ∈ X) (hx : ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹) :
    ∃ y ∈ X, y ^ p = 1 ∧ ∀ l ∈ X, b * l * b⁻¹ = y * l * y⁻¹ := by
  have hpow : ∀ n : ℕ, ∀ l ∈ X, b ^ n * l * (b ^ n)⁻¹ = x ^ n * l * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro l _; simp
    | succ n ih =>
      intro l hl
      have hm : x ^ n * l * (x ^ n)⁻¹ ∈ X :=
        mul_mem (mul_mem (pow_mem hxX n) hl) (inv_mem (pow_mem hxX n))
      calc b ^ (n + 1) * l * (b ^ (n + 1))⁻¹ = b * (b ^ n * l * (b ^ n)⁻¹) * b⁻¹ := by group
        _ = b * (x ^ n * l * (x ^ n)⁻¹) * b⁻¹ := by rw [ih l hl]
        _ = x * (x ^ n * l * (x ^ n)⁻¹) * x⁻¹ := hx _ hm
        _ = x ^ (n + 1) * l * (x ^ (n + 1))⁻¹ := by group
  have hzC : x ^ p ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hpow p l hl
    rw [hbp, inv_one, one_mul, mul_one] at h1
    calc l * x ^ p = (x ^ p * l * (x ^ p)⁻¹) * x ^ p := by rw [← h1]
      _ = x ^ p * l := by group
  have hzp := CFSG.SeitzReduction.RankOne.pow_eq_self_of_sq_eq_one (hZ2 _ (pow_mem hxX p) hzC) hp
  refine ⟨x * (x ^ p)⁻¹, mul_mem hxX (inv_mem (pow_mem hxX p)), ?_, fun l hl => ?_⟩
  · rw [((Commute.self_pow x p).inv_right).mul_pow, inv_pow, hzp, mul_inv_cancel]
  · have hc := Subgroup.mem_centralizer_iff.mp hzC l hl
    rw [hx l hl]
    calc x * l * x⁻¹ = x * (x ^ p)⁻¹ * (x ^ p * l) * x⁻¹ := by group
      _ = x * (x ^ p)⁻¹ * (l * x ^ p) * x⁻¹ := by rw [← hc]
      _ = x * (x ^ p)⁻¹ * l * (x * (x ^ p)⁻¹)⁻¹ := by group

private theorem commute_of_conj_actions {G : Type} [Group G] {p : ℕ} (hp : Odd p)
    {X : Subgroup G} (hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1)
    {b b' y y' : G} (hbb' : b * b' = b' * b) (hyX : y ∈ X) (hy'X : y' ∈ X) (hy'p : y' ^ p = 1)
    (hy : ∀ l ∈ X, b * l * b⁻¹ = y * l * y⁻¹) (hy' : ∀ l ∈ X, b' * l * b'⁻¹ = y' * l * y'⁻¹) :
    y * y' = y' * y := by
  have hact : ∀ l ∈ X, (y * y') * l * (y * y')⁻¹ = (y' * y) * l * (y' * y)⁻¹ := by
    intro l hl
    have hl1 : b' * l * b'⁻¹ ∈ X := by
      rw [hy' l hl]
      exact mul_mem (mul_mem hy'X hl) (inv_mem hy'X)
    have hl2 : y * l * y⁻¹ ∈ X := mul_mem (mul_mem hyX hl) (inv_mem hyX)
    calc (y * y') * l * (y * y')⁻¹ = y * (y' * l * y'⁻¹) * y⁻¹ := by group
      _ = y * (b' * l * b'⁻¹) * y⁻¹ := by rw [hy' l hl]
      _ = b * (b' * l * b'⁻¹) * b⁻¹ := (hy _ hl1).symm
      _ = (b * b') * l * (b * b')⁻¹ := by group
      _ = (b' * b) * l * (b' * b)⁻¹ := by rw [hbb']
      _ = b' * (b * l * b⁻¹) * b'⁻¹ := by group
      _ = b' * (y * l * y⁻¹) * b'⁻¹ := by rw [hy l hl]
      _ = y' * (y * l * y⁻¹) * y'⁻¹ := hy' _ hl2
      _ = (y' * y) * l * (y' * y)⁻¹ := by group
  have hwC := inv_mul_mem_centralizer_of_conj hact
  set w := (y' * y)⁻¹ * (y * y') with hw
  have hwX : w ∈ X := mul_mem (inv_mem (mul_mem hy'X hyX)) (mul_mem hyX hy'X)
  have hyw : y * w = w * y := Subgroup.mem_centralizer_iff.mp hwC y hyX
  have hy'w : y' * w = w * y' := Subgroup.mem_centralizer_iff.mp hwC y' hy'X
  have hconj : y * y' * y⁻¹ = y' * w := by
    calc y * y' * y⁻¹ = y' * (y * w) * y⁻¹ := by rw [hw]; group
      _ = y' * (w * y) * y⁻¹ := by rw [hyw]
      _ = y' * w := by group
  have hwp : w ^ p = 1 := by
    have h1 : (y * y' * y⁻¹) ^ p = 1 := by rw [conj_pow, hy'p, mul_one, mul_inv_cancel]
    rwa [hconj, (show Commute y' w from hy'w).mul_pow, hy'p, one_mul] at h1
  have hw1 : w = 1 :=
    (CFSG.SeitzReduction.RankOne.pow_eq_self_of_sq_eq_one (hZ2 w hwX hwC) hp).symm.trans hwp
  calc y * y' = (y' * y) * w := by rw [hw]; group
    _ = y' * y := by rw [hw1, mul_one]

theorem exists_mul_split_of_inner {G : Type} [Group G] {p : ℕ} (hp : Odd p)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹)
    (hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1) :
    ∀ b ∈ Bs, ∃ y ∈ Bs ⊓ X, ∃ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), b = y * c := by
  intro b hb
  obtain ⟨x, hxX, hx⟩ := hinner b hb
  obtain ⟨y, hyX, hyp, hy⟩ := exists_pow_eq_one_conj_of_conj hp hZ2 (hBs.2 b hb) hxX hx
  have hyC : y ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    obtain ⟨x', hx'X, hx'⟩ := hinner b' hb'
    obtain ⟨y', hy'X, hy'p, hy'⟩ :=
      exists_pow_eq_one_conj_of_conj hp hZ2 (hBs.2 b' hb') hx'X hx'
    have hyy' := commute_of_conj_actions hp hZ2 (hBs.comm hb hb') hyX hy'X hy'p hy hy'
    have hyc' : y * (y'⁻¹ * b') = (y'⁻¹ * b') * y :=
      Subgroup.mem_centralizer_iff.mp (inv_mul_mem_centralizer_of_conj hy') y hyX
    calc b' * y = y' * ((y'⁻¹ * b') * y) := by group
      _ = y' * (y * (y'⁻¹ * b')) := by rw [hyc']
      _ = (y' * y) * (y'⁻¹ * b') := by group
      _ = (y * y') * (y'⁻¹ * b') := by rw [hyy']
      _ = y * b' := by group
  have hyBs : y ∈ Bs := hSC y hyC hyp
  exact ⟨y, Subgroup.mem_inf.mpr ⟨hyBs, hyX⟩, y⁻¹ * b,
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hyBs) hb, inv_mul_mem_centralizer_of_conj hy⟩,
    by group⟩

theorem exists_mulEquiv_prod_of_split {G : Type} [Group G] {Bs B₀ C₀ : Subgroup G}
    (hB₀ : B₀ ≤ Bs) (hC₀ : C₀ ≤ Bs) (hcomm : ∀ y ∈ B₀, ∀ c ∈ C₀, y * c = c * y)
    (hdisj : ∀ y ∈ B₀, y ∈ C₀ → y = 1) (hsplit : ∀ b ∈ Bs, ∃ y ∈ B₀, ∃ c ∈ C₀, b = y * c) :
    ∃ μ : ↥B₀ × ↥C₀ ≃* ↥Bs, ∀ q, (μ q : G) = q.1 * q.2 := by
  let f : ↥B₀ × ↥C₀ →* ↥Bs := MonoidHom.noncommCoprod (Subgroup.inclusion hB₀)
    (Subgroup.inclusion hC₀) fun y c => Subtype.ext (hcomm y y.2 c c.2)
  have hf : ∀ q, (f q : G) = q.1 * q.2 := fun q => rfl
  have hinj : Function.Injective f := by
    rintro ⟨y, c⟩ ⟨y', c'⟩ h
    have h' : (y : G) * c = y' * c' := congrArg Subtype.val h
    have hz : (y' : G)⁻¹ * y = c' * (c : G)⁻¹ := by
      calc (y' : G)⁻¹ * y = (y' : G)⁻¹ * (y * c) * (c : G)⁻¹ := by group
        _ = (y' : G)⁻¹ * (y' * c') * (c : G)⁻¹ := by rw [h']
        _ = c' * (c : G)⁻¹ := by group
    have h1 : (y' : G)⁻¹ * y = 1 :=
      hdisj _ (mul_mem (inv_mem y'.2) y.2) (by rw [hz]; exact mul_mem c'.2 (inv_mem c.2))
    have hyy : (y : G) = y' := (inv_mul_eq_one.mp h1).symm
    have hcc : (c : G) = c' := by rw [hyy] at h'; exact mul_left_cancel h'
    exact Prod.ext (Subtype.ext hyy) (Subtype.ext hcc)
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨y, hy, c, hc, hbc⟩ := hsplit b b.2
    exact ⟨(⟨y, hy⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

def ggExtAut {G : Type} [Group G] {Bs B₀ C₀ : Subgroup G}
    (μ : ↥B₀ × ↥C₀ ≃* ↥Bs) : MulAut ↥B₀ →* MulAut ↥Bs where
  toFun ψ := MulAut.congr μ (ψ.prodCongr (MulEquiv.refl _))
  map_one' := MulEquiv.ext fun b => μ.apply_symm_apply b
  map_mul' ψ ψ' := MulEquiv.ext fun b => by
    rw [MulAut.mul_apply]
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl

theorem ggExtAut_apply {G : Type} [Group G] {Bs B₀ C₀ : Subgroup G}
    (μ : ↥B₀ × ↥C₀ ≃* ↥Bs) (ψ : MulAut ↥B₀) (q : ↥B₀ × ↥C₀) :
    ggExtAut μ ψ (μ q) = μ (ψ q.1, q.2) := by
  show μ ((ψ.prodCongr (MulEquiv.refl _)) (μ.symm (μ q))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem ggExtAut_injective {G : Type} [Group G] {Bs B₀ C₀ : Subgroup G}
    (μ : ↥B₀ × ↥C₀ ≃* ↥Bs) : Function.Injective (ggExtAut μ) := by
  intro ψ ψ' h
  ext y
  have h1 := congrArg (fun φ : MulAut ↥Bs => φ (μ (y, 1))) h
  simp only [ggExtAut_apply] at h1
  have h2 := congrArg Prod.fst (μ.injective h1)
  exact congrArg Subtype.val h2

theorem ggIsReflection_ggExtAut_iff {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs B₀ C₀ : Subgroup G} (μ : ↥B₀ × ↥C₀ ≃* ↥Bs) (ψ : MulAut ↥B₀) :
    GGIsReflection p (ggExtAut μ ψ) ↔ GGIsReflection p ψ := by
  refine ggIsReflection_iff_of_card ?_ (Nat.card_pos (α := ↥C₀)) ?_ ?_
  · rw [← map_pow, ← map_one (ggExtAut μ), (ggExtAut_injective μ).eq_iff]
  · rw [← Nat.card_prod]
    refine (Nat.card_congr (Equiv.subtypeEquiv μ.symm.toEquiv fun b => ?_)).trans
      (Nat.card_congr Equiv.prodSubtypeFstEquivSubtypeProd)
    obtain ⟨q, rfl⟩ := μ.surjective b
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.symm_apply_apply,
      ggExtAut_apply]
    constructor
    · intro h
      exact congrArg Prod.fst (μ.injective h)
    · intro h
      rw [h]
  · rw [← Nat.card_prod]
    exact Nat.card_congr μ.toEquiv.symm

private theorem ggReflGenerated_map_iff {M M' : Type} [Group M] [Group M'] {p : ℕ}
    {Bs : Subgroup M} {Bs' : Subgroup M'} (ρ : MulAut ↥Bs →* MulAut ↥Bs')
    (hρ : Function.Injective ρ) (hrefl : ∀ φ, GGIsReflection p (ρ φ) ↔ GGIsReflection p φ)
    (A : Subgroup (MulAut ↥Bs)) : GGReflGenerated p (A.map ρ) ↔ GGReflGenerated p A := by
  have hS : {ψ | ψ ∈ A.map ρ ∧ GGIsReflection p ψ} =
      ρ '' {φ | φ ∈ A ∧ GGIsReflection p φ} := by
    ext ψ
    constructor
    · rintro ⟨⟨φ, hφ, rfl⟩, hr⟩
      exact ⟨φ, ⟨hφ, (hrefl φ).mp hr⟩, rfl⟩
    · rintro ⟨φ, ⟨hφ, hr⟩, rfl⟩
      exact ⟨⟨φ, hφ, rfl⟩, (hrefl φ).mpr hr⟩
  unfold GGReflGenerated
  rw [hS, ← MonoidHom.map_closure]
  exact (Subgroup.map_injective hρ).eq_iff

theorem ggAutomizer_eq_map_ggExtAut {G : Type} [Group G] {Bs X : Subgroup G}
    (μ : ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≃* ↥Bs)
    (hμ : ∀ q, (μ q : G) = q.1 * q.2) :
    ggAutomizer X Bs = (ggAutomizer X (Bs ⊓ X)).map (ggExtAut μ) := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨g, hgX, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    have hgN₀ : g ∈ Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr (Subgroup.mem_normalizer_iff.mp hgN h)
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hgX) h)
    refine ⟨ggConjAut _ hgN₀, ggConjAut_mem_ggAutomizer hgX hgN₀, ?_⟩
    ext b
    obtain ⟨q, rfl⟩ := μ.surjective b
    simp only [ggExtAut_apply, hμ, hφg, ggConjAut_apply]
    exact (conj_mul_centralizer_eq hgX q.2.2.2).symm
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hgX, hgN, hψg⟩ := mem_ggAutomizer_iff.mp hψ
    have hconj : ∀ g' ∈ X, g' ∈ Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) →
        ∀ k ∈ Bs, g' * k * g'⁻¹ ∈ Bs := by
      intro g' hg'X hg'N k hk
      obtain ⟨q, hq⟩ := μ.surjective ⟨k, hk⟩
      have hk' : k = q.1 * q.2 := by rw [← hμ q, hq]
      rw [hk', conj_mul_centralizer_eq hg'X q.2.2.2]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp hg'N q.1).mp q.1.2).1 q.2.2.1
    have hgBs : g ∈ Subgroup.normalizer (Bs : Set G) :=
      mem_normalizer_of_conj_mem_inv_conj_mem (hconj g hgX hgN)
        (hconj g⁻¹ (inv_mem hgX) (inv_mem hgN))
    rw [mem_ggAutomizer_iff]
    refine ⟨g, hgX, hgBs, fun b => ?_⟩
    obtain ⟨q, rfl⟩ := μ.surjective b
    simp only [ggExtAut_apply, hμ, hψg]
    exact (conj_mul_centralizer_eq hgX q.2.2.2).symm

private theorem conj_mem_of_ggConj {G S : Type} [Group G] [Group S] {X B₀ : Subgroup G}
    {E : Subgroup S} (f : ↥X →* S) (hB₀X : B₀ ≤ X) (e : ↥B₀ ≃* ↥E)
    (he : ∀ b, (e b : S) = f (Subgroup.inclusion hB₀X b)) {g : ↥X} {ψ : MulAut ↥B₀}
    (hψ : ∀ b : ↥B₀, (ψ b : G) = g * b * g⁻¹) {k : S} (hk : k ∈ E) :
    f g * k * (f g)⁻¹ ∈ E := by
  have hk' : k = e (e.symm ⟨k, hk⟩) := by rw [MulEquiv.apply_symm_apply]
  have hconj : g * Subgroup.inclusion hB₀X (e.symm ⟨k, hk⟩) * g⁻¹ =
      Subgroup.inclusion hB₀X (ψ (e.symm ⟨k, hk⟩)) :=
    Subtype.ext (by simp [hψ])
  rw [hk', he, ← map_inv, ← map_mul, ← map_mul, hconj, ← he]
  exact (e _).2

theorem ggAutomizer_top_eq_map_congr {G S : Type} [Group G] [Group S]
    {X B₀ : Subgroup G} {E : Subgroup S} (f : ↥X →* S) (hf : Function.Surjective f)
    (hB₀X : B₀ ≤ X) (e : ↥B₀ ≃* ↥E) (he : ∀ b, (e b : S) = f (Subgroup.inclusion hB₀X b))
    (hN : ∀ g : ↥X, f g ∈ Subgroup.normalizer (E : Set S) →
      (g : G) ∈ Subgroup.normalizer (B₀ : Set G)) :
    ggAutomizer ⊤ E = (ggAutomizer X B₀).map (MulAut.congr e).toMonoidHom := by
  apply le_antisymm
  · intro φ' hφ'
    obtain ⟨g', -, hg'N, hφ'g⟩ := mem_ggAutomizer_iff.mp hφ'
    obtain ⟨g, rfl⟩ := hf g'
    have hgN := hN g hg'N
    refine ⟨ggConjAut B₀ hgN, ggConjAut_mem_ggAutomizer g.2 hgN, ?_⟩
    ext b'
    obtain ⟨b, rfl⟩ := e.surjective b'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rw [he, hφ'g, he, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (by simp [ggConjAut_apply]))
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨g, hgX, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    have hφg' : ∀ b : ↥B₀, (φ b : G) = (⟨g, hgX⟩ : ↥X) * b * (⟨g, hgX⟩ : ↥X)⁻¹ := hφg
    have hφi : ∀ b : ↥B₀, (φ⁻¹ b : G) =
        (⟨g, hgX⟩ : ↥X)⁻¹ * b * ((⟨g, hgX⟩ : ↥X)⁻¹)⁻¹ := by
      intro b
      rw [inv_apply_of_forall hφg b]
      simp
    have hfN : f ⟨g, hgX⟩ ∈ Subgroup.normalizer (E : Set S) := by
      refine mem_normalizer_of_conj_mem_inv_conj_mem
        (fun k hk => conj_mem_of_ggConj f hB₀X e he hφg' hk) fun k hk => ?_
      have h := conj_mem_of_ggConj f hB₀X e he hφi hk
      rwa [map_inv] at h
    rw [mem_ggAutomizer_iff]
    refine ⟨f ⟨g, hgX⟩, Subgroup.mem_top _, hfN, fun b' => ?_⟩
    obtain ⟨b, rfl⟩ := e.surjective b'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rw [he, he, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (by simp [hφg]))

theorem mem_normalizer_of_image_mem_normalizer {G S : Type} [Group G] [Group S] {p : ℕ}
    {X B₀ : Subgroup G} (hB₀ : IsElemAbelian p B₀) (hB₀X : B₀ ≤ X) (f : ↥X →* S)
    (hker : ∀ x : ↥X, f x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G))
    (hZp : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ p = 1 → z = 1) (g : ↥X)
    (hg : f g ∈ Subgroup.normalizer ((f.comp (Subgroup.inclusion hB₀X)).range : Set S)) :
    (g : G) ∈ Subgroup.normalizer (B₀ : Set G) := by
  have key : ∀ g : ↥X,
      f g ∈ Subgroup.normalizer ((f.comp (Subgroup.inclusion hB₀X)).range : Set S) →
      ∀ h ∈ B₀, (g : G) * h * (g : G)⁻¹ ∈ B₀ := by
    intro g hg h hh
    have hhX : h ∈ X := hB₀X hh
    have hu : f (g * ⟨h, hhX⟩ * g⁻¹) ∈ (f.comp (Subgroup.inclusion hB₀X)).range := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hg _).mp ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨y, hy⟩ := hu
    have hz : f ((Subgroup.inclusion hB₀X y)⁻¹ * (g * ⟨h, hhX⟩ * g⁻¹)) = 1 := by
      rw [map_mul, map_inv, ← hy]
      simp
    have hzC := hker _ hz
    set z : ↥X := (Subgroup.inclusion hB₀X y)⁻¹ * (g * ⟨h, hhX⟩ * g⁻¹) with hzdef
    have hzX : (z : G) ∈ X := z.2
    have hyz : (g : G) * h * (g : G)⁻¹ = y * z := by
      simp [hzdef]
    have hcomm : (y : G) * z = z * y :=
      (Subgroup.mem_centralizer_iff.mp hzC y (hB₀X y.2))
    have hzp : (z : G) ^ p = 1 := by
      have h1 : ((g : G) * h * (g : G)⁻¹) ^ p = 1 := by
        rw [conj_pow, hB₀.2 h hh, mul_one, mul_inv_cancel]
      rwa [hyz, (show Commute (y : G) z from hcomm).mul_pow, hB₀.2 _ y.2, one_mul] at h1
    have hz1 : (z : G) = 1 := hZp _ hzX hzC hzp
    rw [hyz, hz1, mul_one]
    exact y.2
  refine mem_normalizer_of_conj_mem_inv_conj_mem (key g hg) fun h hh => ?_
  have h1 := key g⁻¹ (by rw [map_inv]; exact inv_mem hg) h hh
  simpa using h1

theorem ggF4AutRefl_of_quotient {G S : Type} [Group G] [Finite G] [Group S] {p : ℕ}
    (hp : Odd p) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ l ∈ X, b * l * b⁻¹ = x * l * x⁻¹)
    (hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1)
    (hcard : Nat.card Bs = p ^ 4 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    (f : ↥X →* S) (hf : Function.Surjective f)
    (hker : ∀ x : ↥X, f x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G))
    (hcore : ∀ E : Subgroup S, IsElemAbelian p E → Nat.card E = p ^ 4 →
      2 ^ 4 * Nat.factorial 4 ≤ Nat.card (ggAutomizer ⊤ E) ∧
        GGReflGenerated p (ggAutomizer ⊤ E) ∧
        ∀ e : ↥E, (∀ φ ∈ ggAutomizer ⊤ E, φ e = e) → e = 1) :
    2 ^ 4 * Nat.factorial 4 ≤ Nat.card (ggAutomizer X Bs) ∧
      GGReflGenerated p (ggAutomizer X Bs) ∧
      ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer X Bs, φ b = b) →
        (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  have hZp : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ p = 1 → z = 1 :=
    fun z hzX hzC hzp =>
      (CFSG.SeitzReduction.RankOne.pow_eq_self_of_sq_eq_one (hZ2 z hzX hzC) hp).symm.trans hzp
  have hB₀ : IsElemAbelian p (Bs ⊓ X) := hBs.mono inf_le_left
  obtain ⟨μ, hμ⟩ := exists_mulEquiv_prod_of_split (Bs := Bs) (B₀ := Bs ⊓ X)
    (C₀ := Bs ⊓ Subgroup.centralizer (X : Set G)) inf_le_left inf_le_left
    (fun y hy c hc => hBs.comm hy.1 hc.1) (fun y hy hyC => hZp y hy.2 hyC.2 (hBs.2 y hy.1))
    (exists_mul_split_of_inner hp hBs hSC hinner hZ2)
  have hB₀card : Nat.card ↥(Bs ⊓ X) = p ^ 4 := by
    have h1 : Nat.card Bs =
        Nat.card ↥(Bs ⊓ X) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr μ.toEquiv.symm
    rw [h1] at hcard
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard
  have hB₀X : Bs ⊓ X ≤ X := inf_le_right
  have hinj : Function.Injective (f.comp (Subgroup.inclusion hB₀X)) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    exact Subtype.ext (hZp _ y.2.2 (hker _ hy) (hB₀.2 _ y.2))
  let e : ↥(Bs ⊓ X) ≃* ↥(f.comp (Subgroup.inclusion hB₀X)).range := MonoidHom.ofInjective hinj
  have he : ∀ b, (e b : S) = f (Subgroup.inclusion hB₀X b) := fun b => rfl
  have hE : IsElemAbelian p (f.comp (Subgroup.inclusion hB₀X)).range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul,
        show x * y = y * x from Subtype.ext (hB₀.comm x.2 y.2)]
    · obtain ⟨x, rfl⟩ := hz
      rw [← map_pow, show x ^ p = 1 from Subtype.ext (hB₀.2 _ x.2), map_one]
  have hEcard : Nat.card (f.comp (Subgroup.inclusion hB₀X)).range = p ^ 4 := by
    rw [← hB₀card]
    exact Nat.card_congr e.toEquiv.symm
  obtain ⟨h384, hrefl, hfix⟩ := hcore _ hE hEcard
  have hA := ggAutomizer_eq_map_ggExtAut μ hμ
  have hA' := ggAutomizer_top_eq_map_congr f hf hB₀X e he
    (mem_normalizer_of_image_mem_normalizer hB₀ hB₀X f hker hZp)
  have hcardA : Nat.card (ggAutomizer X Bs) =
      Nat.card (ggAutomizer ⊤ (f.comp (Subgroup.inclusion hB₀X)).range) := by
    rw [hA, hA', Subgroup.card_map_of_injective (ggExtAut_injective μ),
      Subgroup.card_map_of_injective (f := (MulAut.congr e).toMonoidHom)
        (MulAut.congr e).injective]
  refine ⟨by rw [hcardA]; exact h384, ?_, ?_⟩
  · rw [hA, ggReflGenerated_map_iff _ (ggExtAut_injective μ) (ggIsReflection_ggExtAut_iff μ),
      ← ggReflGenerated_map_iff (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
        (ggIsReflection_congr_iff e), ← hA']
    exact hrefl
  · intro b hb
    obtain ⟨q, rfl⟩ := μ.surjective b
    have hy : ∀ ψ ∈ ggAutomizer X (Bs ⊓ X), ψ q.1 = q.1 := by
      intro ψ hψ
      have h1 := hb (ggExtAut μ ψ) (by rw [hA]; exact ⟨ψ, hψ, rfl⟩)
      rw [ggExtAut_apply] at h1
      exact congrArg Prod.fst (μ.injective h1)
    have hy' : ∀ φ ∈ ggAutomizer ⊤ (f.comp (Subgroup.inclusion hB₀X)).range,
        φ (e q.1) = e q.1 := by
      intro φ hφ
      rw [hA'] at hφ
      obtain ⟨ψ, hψ, rfl⟩ := hφ
      simp [MulAut.congr_apply, hy ψ hψ]
    have hq1 : q.1 = 1 := by simpa using hfix (e q.1) hy'
    rw [hμ, hq1]
    simpa using q.2.2.2

end F4AutRefl

theorem ggF4NbrAutReflKGInput_of_adjoint
    (hcore : ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
      ∀ E : Subgroup (adjointGroup .F4 K), IsElemAbelian p E → Nat.card E = p ^ 4 →
        2 ^ 4 * Nat.factorial 4 ≤ Nat.card (ggAutomizer ⊤ E) ∧
          GGReflGenerated p (ggAutomizer ⊤ E) ∧
          ∀ e : ↥E, (∀ φ ∈ ggAutomizer ⊤ E, φ e = e) → e = 1) :
    GGF4NbrAutReflKGInput := by
  intro G _ _ p Bs X hp hp2 hBs hSC hmk hcard
  obtain ⟨hX, lab, hlab, hraw⟩ := hmk
  obtain ⟨_, _, _, _, _, _, _, htag, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨t, l, n⟩ := lab
  obtain rfl : t = .F4 := htag
  obtain ⟨K, _, _, hK, -, -, θ, -, hBsN, hind⟩ := hraw
  have : CharP K 2 := charP_two_of_card hK
  set η : ↥X →* ↥(adjointGroup .F4 K) := (TableBF4.recipeEquiv K).toMonoidHom.comp (ggQuotHom θ)
  have hηs : Function.Surjective η :=
    (TableBF4.recipeEquiv K).surjective.comp (ggQuotHom_surjective θ)
  have hηk : η.ker = Subgroup.center ↥X := by
    rw [MonoidHom.ker_comp_of_injective _ _ (TableBF4.recipeEquiv K).injective, ker_ggQuotHom]
  have hZ := F4AutRefl.card_ker_dvd_two_of_adjointF4 hlab.1 hK hX η hηs hηk.le
  rw [hηk] at hZ
  have hZ2 : ∀ z ∈ X, z ∈ Subgroup.centralizer (X : Set G) → z ^ 2 = 1 := by
    intro z hzX hzC
    have hz : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := Subgroup.mem_center_iff.mpr fun w =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC w w.2)
    exact congrArg Subtype.val
      (orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard _ hz).trans hZ))
  have hker : ∀ x : ↥X, η x = 1 → (x : G) ∈ Subgroup.centralizer (X : Set G) := by
    intro x hx
    have hx' : x ∈ Subgroup.center ↥X := hηk ▸ hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx' ⟨h, hh⟩)
  exact F4AutRefl.ggF4AutRefl_of_quotient (hp.odd_of_ne_two hp2) hBs hSC
    (F4AutRefl.exists_conj_of_inn hX θ (TableBF4.idImage_subset_inn K) hBsN hind) hZ2 hcard η
    hηs hker (hcore K p hp hp2)

end CFSG.StandardType
