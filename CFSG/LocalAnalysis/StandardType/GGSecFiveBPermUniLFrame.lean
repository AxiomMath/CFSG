module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameAlign
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag Matrix
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def GGSecFiveBPermUniLFrame {G : Type} [Group G] {p n f : ℕ} {K : Type} [Field K]
    (Bs X : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (π : Equiv.Perm (Fin n)) (σ : ↥(unitarySU 2 f K n) →* G)
    (χ : Multiplicative (ZMod p) →* Kˣ) : Prop :=
  σ.range = X ∧
    (∀ g : ↥(unitarySU 2 f K n), σ g = 1 →
      ∃ c : K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun _ => c) ∧
    Function.Injective χ ∧
    ∀ b : ↥Bs, ∃ (D : GL (Fin n) K)
      (hD : D ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K))),
      (D : Matrix (Fin n) (Fin n) K) = diagonal (fun k => ((χ (eta b (π k)) : Kˣ) : K)) ∧
        ∀ s : ↥(unitarySU 2 f K n), (b : G) * σ s * (b : G)⁻¹ = σ (LineU.conjN D hD s)

private theorem ulf_exists_perm_of_mem_aPermutationFull {n p : ℕ}
    {a : MulAut (Fin n → Multiplicative (ZMod p))} (ha : a ∈ aPermutationFull n p) :
    ∃ τ : Equiv.Perm (Fin n), a = SpCoord.permAut τ := by
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, j, -, rfl⟩ := ha
    exact ⟨Equiv.swap i j, rfl⟩
  | one => exact ⟨1, by ext f k; rfl⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨σ, rfl⟩ := iha
    obtain ⟨τ, rfl⟩ := ihb
    exact ⟨σ * τ, by ext f k; rfl⟩
  | inv a _ iha =>
    obtain ⟨σ, rfl⟩ := iha
    exact ⟨σ⁻¹, by ext f k; rfl⟩

private theorem ulf_ggAutomizer_fix {G : Type} [Group G] {Bs X : Subgroup G} {a : MulAut ↥Bs}
    (ha : a ∈ ggAutomizer X Bs) (c : ↥Bs) (hc : (c : G) ∈ Subgroup.centralizer (X : Set G)) :
    a c = c := by
  have hle : ggAutomizer X Bs ≤ MulAction.stabilizer (MulAut ↥Bs) c := by
    refine (Subgroup.closure_le _).2 ?_
    rintro a ⟨g, hgX, -, hg⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    apply Subtype.ext
    rw [hg c, Subgroup.mem_centralizer_iff.mp hc g hgX, mul_inv_cancel_right]
  exact MulAction.mem_stabilizer_iff.mp (hle ha)

private theorem ulf_eta_const {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    (c : ↥Bs) (hc : (c : G) ∈ Subgroup.centralizer (X : Set G)) (k k' : Fin n) :
    eta c k = eta c k' := by
  by_cases hkk : k = k'
  · rw [hkk]
  have hmem : SpCoord.permAut (p := p) (Equiv.swap k k') ∈ aPermutationFull n p :=
    Subgroup.subset_closure ⟨k, k', hkk, rfl⟩
  rw [← hA] at hmem
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.mp hmem
  have h1 : (MulAut.congr eta a) (eta c) = eta c := by
    change eta (a (eta.symm (eta c))) = eta c
    rw [MulEquiv.symm_apply_apply, ulf_ggAutomizer_fix ha c hc]
  have h3 : SpCoord.permAut (p := p) (Equiv.swap k k') (eta c) = eta c := by
    have h4 := congrArg (fun φ : MulAut _ => φ (eta c)) hae
    rw [← h4]
    exact h1
  have h2 := congrFun h3 k
  rw [SpCoord.permAut_apply, Function.comp_apply, Equiv.Perm.inv_def, Equiv.symm_swap,
    Equiv.swap_apply_left] at h2
  exact h2.symm

theorem card_inf_centralizer_le_of_aPermutationFull {G : Type} [Group G] {p n : ℕ} [NeZero p]
    {Bs X : Subgroup G} (hn : 0 < n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p := by
  let k0 : Fin n := ⟨0, hn⟩
  let f : ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) → Multiplicative (ZMod p) :=
    fun b => eta ⟨(b : G), b.2.1⟩ k0
  have hf : Function.Injective f := by
    intro a b hab
    change eta ⟨(a : G), a.2.1⟩ k0 = eta ⟨(b : G), b.2.1⟩ k0 at hab
    have hcoords : eta ⟨(a : G), a.2.1⟩ = eta ⟨(b : G), b.2.1⟩ := by
      funext k
      exact (ulf_eta_const eta hA ⟨(a : G), a.2.1⟩ a.2.2 k k0).trans
        (hab.trans (ulf_eta_const eta hA ⟨(b : G), b.2.1⟩ b.2.2 k k0).symm)
    exact Subtype.ext (congrArg (fun c : ↥Bs => (c : G)) (eta.injective hcoords))
  calc
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤
        Nat.card (Multiplicative (ZMod p)) := Nat.card_le_card_of_injective f hf
    _ = p := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

section Log

variable {F : Type} [Field F] {p : ℕ} [NeZero p] {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ p)

private noncomputable def ulfExp (a : ZMod p) : Fˣ :=
  ((Additive.toMul (hζ.zmodEquivZPowers a) : Subgroup.zpowers ζ) : Fˣ)

private noncomputable def ulfLog (z : Fˣ) : ZMod p :=
  if hz : z ∈ Subgroup.zpowers ζ then hζ.zmodEquivZPowers.symm (Additive.ofMul ⟨z, hz⟩) else 0

include hζ in
private theorem ulf_mem_zpowers {z : Fˣ} (hz : z ^ p = 1) : z ∈ Subgroup.zpowers ζ := by
  rw [hζ.zpowers_eq]
  exact (mem_rootsOfUnity p z).mpr hz

omit [NeZero p] in
private theorem ulfExp_add (a b : ZMod p) : ulfExp hζ (a + b) = ulfExp hζ a * ulfExp hζ b := by
  unfold ulfExp
  rw [map_add, toMul_add, Subgroup.coe_mul]

omit [NeZero p] in
private theorem ulfExp_zero : ulfExp hζ 0 = 1 := by
  unfold ulfExp
  rw [map_zero]
  rfl

private theorem ulfExp_pow (a : ZMod p) : ulfExp hζ a ^ p = 1 := by
  have h : ulfExp hζ a ∈ rootsOfUnity p F := by
    rw [← hζ.zpowers_eq]
    exact (Additive.toMul (hζ.zmodEquivZPowers a)).2
  exact (mem_rootsOfUnity p _).mp h

omit [NeZero p] in
private theorem ulfExp_injective : Function.Injective (ulfExp hζ) := by
  intro a b h
  apply hζ.zmodEquivZPowers.injective
  apply Additive.toMul.injective
  exact Subtype.ext h

private theorem ulfExp_ulfLog {z : Fˣ} (hz : z ^ p = 1) : ulfExp hζ (ulfLog hζ z) = z := by
  have hm := ulf_mem_zpowers hζ hz
  unfold ulfLog
  rw [dif_pos hm]
  unfold ulfExp
  rw [AddEquiv.apply_symm_apply]
  rfl

private theorem ulfLog_ulfExp (a : ZMod p) : ulfLog hζ (ulfExp hζ a) = a :=
  ulfExp_injective hζ (ulfExp_ulfLog hζ (ulfExp_pow hζ a))

private theorem ulfLog_mul {z z' : Fˣ} (hz : z ^ p = 1) (hz' : z' ^ p = 1) :
    ulfLog hζ (z * z') = ulfLog hζ z + ulfLog hζ z' := by
  apply ulfExp_injective hζ
  rw [ulfExp_add, ulfExp_ulfLog hζ hz, ulfExp_ulfLog hζ hz',
    ulfExp_ulfLog hζ (by rw [mul_pow, hz, hz', one_mul])]

private theorem ulfLog_one : ulfLog hζ (1 : Fˣ) = 0 := by
  have h := ulfLog_mul hζ (z := 1) (z' := 1) (one_pow p) (one_pow p)
  rw [mul_one] at h
  linear_combination -h

end Log

theorem exists_uniLFrame_of_model {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : CFSG.Open.IsElemAbelian p Bs)
    (hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hA : (ggAutomizer X Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K : Type} [Field K] [Finite K] {f : ℕ}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (φ : ↥(unitarySU 2 f K n) →* ↥X)
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma X hN).range, ∃ t : Fin n → K, LineU.ActsDiagU φ a t)
    (π : Equiv.Perm (Fin n)) :
    ∃ (σ : ↥(unitarySU 2 f K n) →* G) (χ : Multiplicative (ZMod p) →* Kˣ),
      GGSecFiveBPermUniLFrame Bs X eta π σ χ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hK : UnitaryFieldData 2 f K := hM.field
  have h3n : 3 ≤ n := by omega
  let h0 : Fin n := ⟨0, by omega⟩
  choose t ht using fun b : ↥Bs =>
    hdiag ((ggGamma X hN) b) ⟨b, rfl⟩
  let r : ↥Bs → Fin n → K := fun b k => t b k * (t b h0)⁻¹
  have hbp : ∀ b : ↥Bs, b ^ p = 1 := fun b => Subtype.ext (by
    simpa using hBs.2 b b.2)
  have hap : ∀ b : ↥Bs, (ggGamma X hN b) ^ p = 1 := fun b => by
    rw [← map_pow, hbp b, map_one]
  have r_pow : ∀ (b : ↥Bs) (k : Fin n), r b k ^ p = 1 := by
    intro b k
    have h := (ht b).ratio_pow hK h3n hM.ker (hap b) k h0
    simpa [r] using h
  have r_mul : ∀ (b b' : ↥Bs) (k : Fin n), r (b * b') k = r b k * r b' k := by
    intro b b' k
    have hact : LineU.ActsDiagU φ (ggGamma X hN (b * b')) (t (b * b')) := ht (b * b')
    have hprod : LineU.ActsDiagU φ (ggGamma X hN b * ggGamma X hN b')
        (fun k => t b k * t b' k) := UnitTB.actsDiagU_mul (ht b) (ht b')
    rw [map_mul] at hact
    have h := LineU.ActsDiagU.ratio_eq hK h3n hM.ker hact hprod k h0
    simp only [r] at h ⊢
    rw [h, _root_.mul_inv_rev]
    ring
  have r_one : ∀ k : Fin n, r 1 k = 1 := by
    intro k
    have ht1 : LineU.ActsDiagU φ (1 : MulAut ↥X) (t 1) := by
      have h := ht 1
      rwa [map_one] at h
    have h := LineU.ActsDiagU.ratio_eq hK h3n hM.ker ht1 (LineU.actsDiagU_one φ) k h0
    simpa [r] using h
  have r_ne_zero : ∀ b k, r b k ≠ 0 := fun b k =>
    mul_ne_zero ((ht b).ne_zero k) (inv_ne_zero ((ht b).ne_zero h0))
  let ru : ↥Bs → Fin n → Kˣ := fun b k => Units.mk0 (r b k) (r_ne_zero b k)
  have ru_coe : ∀ b k, (ru b k : K) = r b k := by
    intro b k
    change (Units.mk0 (r b k) (r_ne_zero b k) : K) = r b k
    rfl
  have ru_pow : ∀ (b : ↥Bs) (k : Fin n), (ru b k) ^ p = 1 := by
    intro b k
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ru_coe]
    exact r_pow b k
  have ru_one : ∀ k : Fin n, ru 1 k = 1 := by
    intro k
    apply Units.ext
    rw [ru_coe, Units.val_one]
    exact r_one k
  have ru_mul : ∀ (b b' : ↥Bs) (k : Fin n), ru (b * b') k = ru b k * ru b' k := by
    intro b b' k
    apply Units.ext
    rw [ru_coe, Units.val_mul, ru_coe, ru_coe]
    exact r_mul b b' k
  have hcardBs : Nat.card ↥Bs = p ^ n := by
    rw [Nat.card_congr eta.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun,
      Fintype.card_multiplicative, ZMod.card, Fintype.card_fin]
  have hbig : p < p ^ n := by
    have h := Nat.pow_lt_pow_right hp.one_lt (show 1 < n by omega)
    simpa using h
  have hb_exists : ∃ b : ↥Bs, ggGamma X hN b ≠ 1 := by
    by_contra h
    push Not at h
    have hle : Bs ≤ Subgroup.centralizer (X : Set G) := by
      intro x hx
      exact (ggGamma_eq_one_iff X hN ⟨x, hx⟩).mp (h ⟨x, hx⟩)
    have hcard_le : Nat.card ↥Bs ≤ p := by
      have h1 := hC
      rw [inf_eq_left.mpr hle] at h1
      exact h1
    rw [hcardBs] at hcard_le
    omega
  obtain ⟨b0, hb0⟩ := hb_exists
  have hnc : ∃ k : Fin n, t b0 k ≠ t b0 h0 := by
    by_contra h
    push Not at h
    exact hb0 ((ht b0).eq_one_of_const hM.surj h0 (fun i j => (h i).trans (h j).symm))
  obtain ⟨k0, hk0⟩ := hnc
  have hr_ne : r b0 k0 ≠ 1 := by
    intro h
    apply hk0
    exact (mul_inv_eq_one₀ ((ht b0).ne_zero h0)).mp (by simpa [r] using h)
  let ζ : Kˣ := Units.mk0 (r b0 k0) (r_ne_zero b0 k0)
  have hζp : ζ ^ p = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
    exact r_pow b0 k0
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hr_ne
    exact congrArg (fun u : Kˣ => (u : K)) h
  have hord : orderOf ζ = p := orderOf_eq_prime hζp hζ1
  have hζ : IsPrimitiveRoot ζ p := by
    simpa [hord] using IsPrimitiveRoot.orderOf ζ
  let Ev : (Fin n → ZMod p) → ↥Bs := fun v => eta.symm (fun k => Multiplicative.ofAdd (v k))
  have hEv_eta : ∀ b : ↥Bs, Ev (fun k => Multiplicative.toAdd (eta b k)) = b := fun b => by
    simp only [Ev, ofAdd_toAdd]
    exact eta.symm_apply_apply b
  have hEta_Ev : ∀ v k, Multiplicative.toAdd (eta (Ev v) k) = v k := fun v k => by
    simp only [Ev, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hEv_add : ∀ v w, Ev (v + w) = Ev v * Ev w := fun v w => by
    simp only [Ev, ← map_mul]
    rfl
  have hEv_zero : Ev 0 = 1 := by
    simp only [Ev]
    exact map_one eta.symm
  let M : (Fin n → ZMod p) →+ (Fin n → ZMod p) :=
    { toFun := fun v k => ulfLog hζ (ru (Ev v) k)
      map_zero' := by
        funext k
        rw [hEv_zero, ru_one k, ulfLog_one]
        rfl
      map_add' := fun v w => by
        funext k
        rw [hEv_add, ru_mul, ulfLog_mul hζ (ru_pow (Ev v) k) (ru_pow (Ev w) k)]
        rfl }
  have hMdef : ∀ v k, M v k = ulfLog hζ (ru (Ev v) k) := fun _ _ => rfl
  have hinj : ∀ v, (∃ s, ∀ k, M v k = s) → ∃ s, ∀ k, v k = s := by
    rintro v ⟨s, hs⟩
    have hruconst : ∀ k, ru (Ev v) k = ulfExp hζ s := by
      intro k
      have hlog : ulfLog hζ (ru (Ev v) k) = s := by
        rw [← hMdef]
        exact hs k
      rw [show ru (Ev v) k = ulfExp hζ (ulfLog hζ (ru (Ev v) k)) from
        (ulfExp_ulfLog hζ (ru_pow (Ev v) k)).symm, hlog]
    have hrconst : ∀ k, r (Ev v) k = (ulfExp hζ s : K) := by
      intro k
      rw [← ru_coe (Ev v) k, hruconst k]
    have htconst : ∀ k, t (Ev v) k = t (Ev v) h0 * (ulfExp hζ s : K) := by
      intro k
      have hne : t (Ev v) h0 ≠ 0 := (ht (Ev v)).ne_zero h0
      calc t (Ev v) k = (t (Ev v) k * (t (Ev v) h0)⁻¹) * t (Ev v) h0 := by
            field_simp
          _ = (ulfExp hζ s : K) * t (Ev v) h0 := by
            rw [show t (Ev v) k * (t (Ev v) h0)⁻¹ = (ulfExp hζ s : K) from hrconst k]
          _ = t (Ev v) h0 * (ulfExp hζ s : K) := mul_comm _ _
    have hconst : ∀ i j, t (Ev v) i = t (Ev v) j := by
      intro i j
      rw [htconst i, htconst j]
    have hγ : ggGamma X hN (Ev v) = 1 :=
      (ht (Ev v)).eq_one_of_const hM.surj h0 hconst
    have hc : ((Ev v : ↥Bs) : G) ∈ Subgroup.centralizer (X : Set G) :=
      (ggGamma_eq_one_iff X hN (Ev v)).mp hγ
    refine ⟨v h0, fun k => ?_⟩
    rw [← hEta_Ev v k, ← hEta_Ev v h0, ulf_eta_const eta hA (Ev v) hc k h0]
  have hsurj : ∀ y : Fin n → ZMod p, ∃ v s, ∀ k, y k = M v k + s := by
    let constAddHom : ZMod p →+ (Fin n → ZMod p) :=
      { toFun := fun s _ => s
        map_zero' := rfl
        map_add' := fun a b => rfl }
    let C : AddSubgroup (Fin n → ZMod p) := constAddHom.range
    have hconst_inj : Function.Injective
        (fun s : ZMod p => (constAddHom s : Fin n → ZMod p)) := by
      intro a b h
      have := congrFun h h0
      simpa [constAddHom] using this
    have hCcard : Nat.card ↥C = p := by
      change Nat.card (Set.range (fun s : ZMod p =>
        (constAddHom s : Fin n → ZMod p))) = p
      rw [Nat.card_range_of_injective hconst_inj, Nat.card_eq_fintype_card, ZMod.card]
    have hcardV : Nat.card (Fin n → ZMod p) = p ^ n := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hkerC : M.ker ≤ C := by
      intro v hv
      have hv0 : M v = 0 := AddMonoidHom.mem_ker.mp hv
      obtain ⟨s, hs⟩ := hinj v ⟨0, fun k => by rw [hv0]; rfl⟩
      exact AddMonoidHom.mem_range.mpr ⟨s, by ext k; exact (hs k).symm⟩
    have hcard_ker_mul : Nat.card ↥M.ker * Nat.card ↥M.range = Nat.card (Fin n → ZMod p) :=
      AddSubgroup.card_ker_mul_card_range M
    intro y
    by_cases hsurjM : Function.Surjective M
    · obtain ⟨v, hv⟩ := hsurjM y
      exact ⟨v, 0, fun k => by rw [hv]; simp⟩
    · have hrange_ne_top : M.range ≠ ⊤ := fun h =>
        hsurjM (AddMonoidHom.range_eq_top.mp h)
      have hrange_lt_top : M.range < (⊤ : AddSubgroup (Fin n → ZMod p)) :=
        lt_of_le_of_ne le_top hrange_ne_top
      have hcard_range_lt : Nat.card ↥M.range < Nat.card (Fin n → ZMod p) := by
        have h := AddSubgroup.card_lt_of_lt hrange_lt_top
        simpa [AddSubgroup.card_top] using h
      have hprod := hcard_ker_mul
      have hker_gt_one : 1 < Nat.card ↥M.ker := by
        by_contra h
        have hle1 : Nat.card ↥M.ker ≤ 1 := by omega
        have hpos : 0 < Nat.card ↥M.ker := Nat.card_pos
        have hker1 : Nat.card ↥M.ker = 1 := by omega
        rw [hker1, one_mul] at hprod
        omega
      have hker_le_p : Nat.card ↥M.ker ≤ p := by
        calc Nat.card ↥M.ker ≤ Nat.card ↥C := AddSubgroup.card_le_of_le hkerC
          _ = p := hCcard
      have hker_card : Nat.card ↥M.ker = p := by
        have hker_dvd : Nat.card ↥M.ker ∣ p ^ n := by
          rw [← hcardV, ← hcard_ker_mul]
          exact ⟨_, rfl⟩
        obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp hker_dvd
        have hk_ge_one : 1 ≤ k := by
          by_contra h
          have hk0 : k = 0 := by omega
          rw [hk0, pow_zero] at hk_eq
          omega
        have hk_le_one : k ≤ 1 := by
          by_contra h
          have hk2 : 2 ≤ k := by omega
          have hle : p ^ k ≤ p := by rw [← hk_eq]; exact hker_le_p
          have hlt : p < p ^ k := by
            calc p = p ^ 1 := by rw [pow_one]
              _ < p ^ k := Nat.pow_lt_pow_right hp.one_lt hk2
          omega
        have hk1 : k = 1 := by omega
        rw [hk_eq, hk1, pow_one]
      have hrange_card : Nat.card ↥M.range = p ^ (n - 1) := by
        have hpn : p ^ n = p * p ^ (n - 1) := by
          calc p ^ n = p ^ ((n - 1) + 1) := by
                rw [Nat.sub_add_cancel (show 1 ≤ n by omega)]
            _ = p ^ (n - 1) * p := pow_succ _ _
            _ = p * p ^ (n - 1) := mul_comm _ _
        have h1 : p * Nat.card ↥M.range = p * p ^ (n - 1) := by
          calc p * Nat.card ↥M.range =
              Nat.card ↥M.ker * Nat.card ↥M.range := by rw [hker_card]
            _ = Nat.card (Fin n → ZMod p) := hcard_ker_mul
            _ = p ^ n := hcardV
            _ = p * p ^ (n - 1) := hpn
        exact mul_left_cancel₀ hp.ne_zero h1
      have hindex : M.range.index = p := by
        have h1 := AddSubgroup.index_mul_card M.range
        rw [hrange_card, hcardV] at h1
        have hpn : p ^ n = p ^ (n - 1) * p := by
          calc p ^ n = p ^ ((n - 1) + 1) := by
                rw [Nat.sub_add_cancel (show 1 ≤ n by omega)]
            _ = p ^ (n - 1) * p := pow_succ _ _
        rw [hpn] at h1
        have h1' : M.range.index * p ^ (n - 1) = p * p ^ (n - 1) := by
          rw [h1, mul_comm (p ^ (n - 1)) p]
        exact mul_right_cancel₀ (pow_ne_zero (n - 1) hp.ne_zero) h1'
      have hC_not_le : ¬ C ≤ M.range := by
        intro hle
        have hker_eq_C : M.ker = C := by
          apply AddSubgroup.eq_of_le_of_card_ge hkerC
          rw [hker_card, hCcard]
        have hltC : 1 < Nat.card ↥C := by rw [hCcard]; exact hp.one_lt
        haveI : Nontrivial ↥C := by
          rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]
          exact hltC
        obtain ⟨c, hcC, hc0⟩ := AddSubgroup.exists_ne_zero_of_nontrivial C
        have hcRange : c ∈ M.range := hle hcC
        obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp hcRange
        obtain ⟨s, hs⟩ := AddMonoidHom.mem_range.mp hcC
        have hvconst : ∃ s, ∀ k, M v k = s := by
          refine ⟨s, fun k => ?_⟩
          rw [hv, ← hs]
          rfl
        obtain ⟨s', hs'⟩ := hinj v hvconst
        have hvC : v ∈ C := AddMonoidHom.mem_range.mpr ⟨s', by ext k; exact (hs' k).symm⟩
        have hvker : v ∈ M.ker := hker_eq_C ▸ hvC
        have hMv0 : M v = 0 := AddMonoidHom.mem_ker.mp hvker
        exact hc0 (by rw [← hv, hMv0])
      let K := M.range ⊔ C
      have hK_ne : K ≠ M.range := by
        intro h
        exact hC_not_le (h ▸ le_sup_right)
      have hrel : M.range.relIndex K * K.index = M.range.index :=
        AddSubgroup.relIndex_mul_index le_sup_left
      have hrel_ne_one : M.range.relIndex K ≠ 1 := by
        intro h
        exact hK_ne (le_antisymm (AddSubgroup.relIndex_eq_one.mp h) le_sup_left)
      have hrel_gt : 1 < M.range.relIndex K := by
        have hpos : 0 < M.range.relIndex K := by
          by_contra h
          have h0 : M.range.relIndex K = 0 := by omega
          rw [h0, zero_mul, hindex] at hrel
          omega
        omega
      have hrel_eq : M.range.relIndex K = p := by
        have hdvd : M.range.relIndex K ∣ p := ⟨K.index, (hrel.trans hindex).symm⟩
        rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
        · exact (hrel_ne_one h).elim
        · exact h
      have hKindex : K.index = 1 := by
        have h1 : p * K.index = p := (hrel_eq ▸ hrel).trans hindex
        exact mul_left_cancel₀ hp.ne_zero (by simpa using h1)
      have hKtop : K = ⊤ := AddSubgroup.index_eq_one.mp hKindex
      have hy : y ∈ M.range ⊔ C := by
        change y ∈ K
        rw [hKtop]
        exact AddSubgroup.mem_top y
      obtain ⟨a, ha, b, hb, hab⟩ := AddSubgroup.mem_sup.mp hy
      obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp ha
      obtain ⟨s, hs⟩ := AddMonoidHom.mem_range.mp hb
      refine ⟨v, s, fun k => ?_⟩
      calc y k = (a + b) k := by rw [← hab]; rfl
        _ = a k + b k := rfl
        _ = M v k + s := by rw [← hv, ← hs]; rfl
  let gfun : Equiv.Perm (Fin n) → G :=
    fun w => ((φ (LineU.permSU hK w) : ↥X) : G)
  have hg_inv : ∀ w, gfun w.symm = (gfun w)⁻¹ := by
    intro w
    have hperm : LineU.permSU hK w.symm = (LineU.permSU hK w)⁻¹ := by
      apply Subtype.ext
      rw [LineU.coe_permSU, Subgroup.coe_inv, LineU.coe_permSU]
      simpa only [Equiv.Perm.inv_def] using
        map_inv (CFSG.RankThree.Classical.permGL (ι := Fin n) (K := K)) w
    change ((φ (LineU.permSU hK w.symm) : ↥X) : G) = _
    rw [hperm, map_inv, Subgroup.coe_inv]
  have hforward : ∀ (w : Equiv.Perm (Fin n)) (b : G), b ∈ Bs →
      gfun w * b * (gfun w)⁻¹ ∈ Bs := by
    intro w b hb
    let n' : ↥X := φ (LineU.permSU hK w)
    let a : MulAut ↥X := ggGamma X hN ⟨b, hb⟩
    let z : ↥X := n' * (a n')⁻¹
    have hW := LineU.weyl_W_prop hK h3n hM.ker
      (A := (ggGamma X hN).range)
      (fun a ha => by
        obtain ⟨b', rfl⟩ := ha
        exact hap b')
      hdiag
    have hzpowX : z ^ p = 1 := by
      simpa [z, n', a] using
        (hW (φ (LineU.permSU hK w)) ⟨w, rfl⟩ (ggGamma X hN ⟨b, hb⟩)
          ⟨_, rfl⟩).1
    have hzfix : ∀ a' ∈ (ggGamma X hN).range, a' z = z := by
      intro a' ha'
      simpa [z, n', a] using
        (hW (φ (LineU.permSU hK w)) ⟨w, rfl⟩ (ggGamma X hN ⟨b, hb⟩)
          ⟨_, rfl⟩).2 a' ha'
    have hcentral : (z : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hfix := hzfix (ggGamma X hN ⟨c, hc⟩) ⟨⟨c, hc⟩, rfl⟩
      have h1 := congrArg (fun y : ↥X => (y : G)) hfix
      rw [ggGamma_coe] at h1
      calc c * (z : G) = (c * (z : G) * c⁻¹) * c := by group
        _ = (z : G) * c := by rw [h1]
    have hzpowG : (z : G) ^ p = 1 := by
      simpa using congrArg (fun y : ↥X => (y : G)) hzpowX
    have hzBs : (z : G) ∈ Bs := hBsC z hcentral hzpowG
    have hzval : (z : G) = (n' : G) * b * (n' : G)⁻¹ * b⁻¹ := by
      have hagg : (((ggGamma X hN ⟨b, hb⟩) n' : ↥X) : G) = b * (n' : G) * b⁻¹ :=
        ggGamma_coe X hN ⟨b, hb⟩ n'
      change (n' : G) * (((ggGamma X hN ⟨b, hb⟩) n' : ↥X) : G)⁻¹ = _
      rw [hagg]
      group
    have heq : gfun w * b * (gfun w)⁻¹ = (z : G) * b := by
      change (n' : G) * b * (n' : G)⁻¹ = (z : G) * b
      rw [hzval]
      group
    rw [heq]
    exact Bs.mul_mem hzBs hb
  have hnorm : ∀ w, gfun w ∈ Subgroup.normalizer (Bs : Set G) := by
    intro w
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact hforward w b hb
    · intro hb
      have hb' : gfun w * b * (gfun w)⁻¹ ∈ Bs := hb
      have h2 := hforward w.symm _ hb'
      rw [hg_inv w] at h2
      have heq : (gfun w)⁻¹ * (gfun w * b * (gfun w)⁻¹) * ((gfun w)⁻¹)⁻¹ = b := by
        group
      rwa [heq] at h2
  have hΦ : ∀ w : Equiv.Perm (Fin n), ∃ τ : Equiv.Perm (Fin n),
      ∀ v, ∃ s, ∀ k, M (v ∘ τ.symm) k = M v (w.symm k) + s := by
    intro w
    have hgX : gfun w ∈ X := (φ (LineU.permSU hK w)).2
    have hα : ggConjAut Bs (hnorm w) ∈ ggAutomizer X Bs :=
      ggConjAut_mem_ggAutomizer hgX (hnorm w)
    have hmem : (MulAut.congr eta).toMonoidHom (ggConjAut Bs (hnorm w)) ∈
        aPermutationFull n p := by
      rw [← hA]
      exact Subgroup.mem_map_of_mem _ hα
    obtain ⟨τ, hτ⟩ := ulf_exists_perm_of_mem_aPermutationFull hmem
    refine ⟨τ, fun v => ?_⟩
    have hconj : Ev (v ∘ τ.symm) = ggConjAut Bs (hnorm w) (Ev v) := by
      apply eta.injective
      have h1 := congrArg (fun φ : MulAut _ => φ (eta (Ev v))) hτ
      change eta (ggConjAut Bs (hnorm w) (eta.symm (eta (Ev v)))) =
        SpCoord.permAut τ (eta (Ev v)) at h1
      rw [MulEquiv.symm_apply_apply] at h1
      rw [h1]
      funext k
      apply Multiplicative.toAdd.injective
      rw [hEta_Ev, SpCoord.permAut_apply]
      exact (hEta_Ev v (τ.symm k)).symm
    have haut : ggGamma X hN (Ev (v ∘ τ.symm)) =
        MulAut.conj (φ (LineU.permSU hK w)) * ggGamma X hN (Ev v) *
          (MulAut.conj (φ (LineU.permSU hK w)))⁻¹ := by
      rw [hconj]
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply,
        ggGamma_coe, ggConjAut_apply, Subgroup.coe_mul, Subgroup.coe_inv, gfun]
      group
    have hconjActs : LineU.ActsDiagU φ (ggGamma X hN (Ev (v ∘ τ.symm)))
        (fun k => t (Ev v) (w.symm k)) := by
      rw [haut]
      have h := LineU.ActsDiagU.conj_perm hK (ht (Ev v)) w
      simpa [Equiv.Perm.inv_def] using h
    refine ⟨ulfLog hζ ((ru (Ev v) (w.symm h0))⁻¹), fun k => ?_⟩
    have hratio := LineU.ActsDiagU.ratio_eq hK h3n hM.ker
      (ht (Ev (v ∘ τ.symm))) hconjActs k h0
    have hru_eq : ru (Ev (v ∘ τ.symm)) k =
        ru (Ev v) (w.symm k) * (ru (Ev v) (w.symm h0))⁻¹ := by
      apply Units.ext
      change (ru (Ev (v ∘ τ.symm)) k : K) =
        (ru (Ev v) (w.symm k) : K) * ((ru (Ev v) (w.symm h0) : K))⁻¹
      rw [ru_coe, ru_coe, ru_coe]
      simp only [r]
      rw [show t (Ev (v ∘ τ.symm)) k * (t (Ev (v ∘ τ.symm)) h0)⁻¹ =
        t (Ev v) (w.symm k) * (t (Ev v) (w.symm h0))⁻¹ from hratio]
      field_simp [(ht (Ev v)).ne_zero h0, (ht (Ev v)).ne_zero (w.symm h0)]
    have hlogeq : ulfLog hζ (ru (Ev (v ∘ τ.symm)) k) =
        ulfLog hζ (ru (Ev v) (w.symm k)) +
          ulfLog hζ ((ru (Ev v) (w.symm h0))⁻¹) := by
      rw [hru_eq]
      rw [← ulfLog_mul hζ (ru_pow (Ev v) (w.symm k)) (by
        rw [inv_pow, ru_pow, inv_one])]
    simpa only [hMdef] using hlogeq
  obtain ⟨f₀, c, hc0, hfc⟩ :=
    LFrameAlign.exists_perm_smul_of_modConst hp2 (by omega) M hinj hsurj hΦ
  let χ : Multiplicative (ZMod p) →* Kˣ :=
    { toFun := fun a => ulfExp hζ (c * Multiplicative.toAdd a)
      map_one' := by
        rw [toAdd_one, mul_zero, ulfExp_zero]
      map_mul' := fun a b => by
        rw [toAdd_mul, mul_add, ulfExp_add] }
  have hχinj : Function.Injective χ := fun a b h =>
    Multiplicative.toAdd.injective (mul_left_cancel₀ hc0 (ulfExp_injective hζ h))
  have hframe0 : ∀ b : ↥Bs, LineU.ActsDiagU φ (ggGamma X hN b)
      (fun k => ((χ (eta b (f₀ k)) : Kˣ) : K)) := by
    intro b
    obtain ⟨s, hs⟩ := hfc (fun k => Multiplicative.toAdd (eta b k))
    have hlog : ∀ k, ulfLog hζ (ru b k) =
        c * Multiplicative.toAdd (eta b (f₀ k)) + s := by
      intro k
      have h1 := hs k
      rw [hMdef, hEv_eta] at h1
      exact h1
    have hru : ∀ k, ru b k =
        ulfExp hζ (c * Multiplicative.toAdd (eta b (f₀ k)) + s) := by
      intro k
      rw [show ru b k = ulfExp hζ (ulfLog hζ (ru b k)) from
        (ulfExp_ulfLog hζ (ru_pow b k)).symm, hlog k]
    have hr : ∀ k, r b k = ((χ (eta b (f₀ k)) : Kˣ) : K) *
        (ulfExp hζ s : K) := by
      intro k
      rw [← ru_coe b k, hru k, ulfExp_add]
      rfl
    have ht' : ∀ k, t b k = ((χ (eta b (f₀ k)) : Kˣ) : K) *
        (t b h0 * (ulfExp hζ s : K)) := by
      intro k
      have hfac : t b k = (t b k * (t b h0)⁻¹) * t b h0 := by
        rw [mul_assoc, inv_mul_cancel₀ ((ht b).ne_zero h0), mul_one]
      rw [hfac, show t b k * (t b h0)⁻¹ = r b k from rfl, hr k]
      ring
    have hC' : ((t b h0 * (ulfExp hζ s : K)) ≠ 0) :=
      mul_ne_zero ((ht b).ne_zero h0) (Units.ne_zero _)
    have hscaled := UnitTB.actsDiagU_mul_const (ht b) (inv_ne_zero hC')
    have hfun : (fun k => t b k * (t b h0 * (ulfExp hζ s : K))⁻¹) =
        fun k => ((χ (eta b (f₀ k)) : Kˣ) : K) := by
      funext k
      rw [ht' k, mul_assoc, mul_inv_cancel₀ hC', mul_one]
    rwa [hfun] at hscaled
  let ρ : Equiv.Perm (Fin n) := f₀⁻¹ * π
  let P : ↥(unitarySU 2 f K n) := LineU.permSU hK ρ
  have hρk : ∀ k, f₀ (ρ k) = π k := by
    intro k
    change f₀ ((f₀⁻¹ * π) k) = π k
    rw [Equiv.Perm.mul_apply]
    exact Equiv.apply_symm_apply f₀ (π k)
  let σ : ↥(unitarySU 2 f K n) →* G :=
    X.subtype.comp (φ.comp (MulAut.conj P).toMonoidHom)
  refine ⟨σ, χ, ?_, ?_, hχinj, fun b => ?_⟩
  ·
    have hsurjconj : Function.Surjective (φ.comp (MulAut.conj P).toMonoidHom) :=
      hM.surj.comp (MulAut.conj P).surjective
    change (X.subtype.comp (φ.comp (MulAut.conj P).toMonoidHom)).range = X
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurjconj,
      Subgroup.map_top, Subgroup.range_subtype]
  ·
    intro z hz
    have hz' : φ ((MulAut.conj P) z) = 1 := by
      apply Subgroup.subtype_injective X
      simpa [σ] using hz
    obtain ⟨c, hc⟩ := hM.ker _ hz'
    have hc0 : c ≠ 0 := LineU.diag_ne_zero_of_eq hc h0
    let Z : GL (Fin n) K := Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 c hc0)
    have hZcenter : Z ∈ Subgroup.center (GL (Fin n) K) :=
      TableB.scalar_mem_center (ι := Fin n) (Units.mk0 c hc0)
    have hZdiagMat : (Z : Matrix (Fin n) (Fin n) K) = diagonal (fun _ => c) := by
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]
    have hcz : (((MulAut.conj P) z : ↥(unitarySU 2 f K n)) : GL (Fin n) K) =
        (P : GL (Fin n) K) * (z : GL (Fin n) K) * (P : GL (Fin n) K)⁻¹ := by
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    have hconjmat : ((((P : GL (Fin n) K) * (z : GL (Fin n) K) *
        (P : GL (Fin n) K)⁻¹) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        diagonal (fun _ => c) := by
      rw [← hcz]
      exact hc
    have hconjGL : ((P : GL (Fin n) K) * (z : GL (Fin n) K) * (P : GL (Fin n) K)⁻¹) = Z := by
      apply Units.ext
      rw [hconjmat, hZdiagMat]
    have hzZ : (z : GL (Fin n) K) = Z := by
      calc (z : GL (Fin n) K)
          = (P : GL (Fin n) K)⁻¹ *
              ((P : GL (Fin n) K) * (z : GL (Fin n) K) * (P : GL (Fin n) K)⁻¹) *
              (P : GL (Fin n) K) := by group
        _ = (P : GL (Fin n) K)⁻¹ * Z * (P : GL (Fin n) K) := by rw [hconjGL]
        _ = Z := by
          calc (P : GL (Fin n) K)⁻¹ * Z * (P : GL (Fin n) K)
              = (P : GL (Fin n) K)⁻¹ * (Z * (P : GL (Fin n) K)) := by group
            _ = (P : GL (Fin n) K)⁻¹ * ((P : GL (Fin n) K) * Z) := by
                rw [Subgroup.mem_center_iff.mp hZcenter (P : GL (Fin n) K)]
            _ = Z := by group
    refine ⟨c, ?_⟩
    rw [show ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Z : Matrix (Fin n) (Fin n) K) from
      congrArg (fun y : GL (Fin n) K => (y : Matrix (Fin n) (Fin n) K)) hzZ,
      hZdiagMat]
  ·
    obtain ⟨D_t, hD_t, hDt, hact⟩ := hframe0 b
    let D : GL (Fin n) K := (P : GL (Fin n) K)⁻¹ * D_t * (P : GL (Fin n) K)
    have hPN : (P : GL (Fin n) K) ∈
        Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)) :=
      Subgroup.le_normalizer P.2
    have hD : D ∈ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K)) := by
      change (P : GL (Fin n) K)⁻¹ * D_t * (P : GL (Fin n) K) ∈ _
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hD_t) hPN
    have hPmat : ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ρ⁻¹.permMatrix K := by
      change ((((LineU.permSU hK ρ : ↥(unitarySU 2 f K n)) : GL (Fin n) K)) :
        Matrix (Fin n) (Fin n) K) = _
      rw [LineU.coe_permSU]
      exact LineU.coe_permGL_matrix (K := K) ρ
    have hPinvmat : (((P : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) =
        ρ.permMatrix K := by
      change (((((LineU.permSU hK ρ : ↥(unitarySU 2 f K n)) : GL (Fin n) K))⁻¹) :
        Matrix (Fin n) (Fin n) K) = _
      rw [LineU.coe_permSU]
      simpa only [Matrix.coe_units_inv] using LineU.coe_permGL_inv_matrix (K := K) ρ
    have hDmat : (D : Matrix (Fin n) (Fin n) K) =
        diagonal (fun k => ((χ (eta b (π k)) : Kˣ) : K)) := by
      have h1 : (D : Matrix (Fin n) (Fin n) K) =
          ρ.permMatrix K * diagonal (fun k => ((χ (eta b (f₀ k)) : Kˣ) : K)) *
            ρ⁻¹.permMatrix K := by
        change (((P : GL (Fin n) K)⁻¹ * D_t * (P : GL (Fin n) K) :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
        rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hPinvmat, hDt, hPmat]
      rw [h1]
      have hconj := LineU.permMatrix_conj_diag (σ := ρ⁻¹)
        (t := fun k => ((χ (eta b (f₀ k)) : Kˣ) : K))
      have h2 : ρ.permMatrix K * diagonal (fun k => ((χ (eta b (f₀ k)) : Kˣ) : K)) *
          ρ⁻¹.permMatrix K =
          diagonal (fun k => ((χ (eta b (f₀ (ρ k))) : Kˣ) : K)) := by
        simpa [Equiv.Perm.inv_def, inv_inv] using hconj
      rw [h2]
      congr 1
      funext k
      rw [hρk k]
    refine ⟨D, hD, hDmat, fun s => ?_⟩
    have hσs : σ s = ((φ (LineU.conjN P hPN s) : ↥X) : G) := rfl
    have hL : (b : G) * σ s * (b : G)⁻¹ =
        ((φ (LineU.conjN D_t hD_t (LineU.conjN P hPN s)) : ↥X) : G) := by
      rw [hσs]
      have h := congrArg (fun y : ↥X => (y : G)) (hact (LineU.conjN P hPN s))
      rw [ggGamma_coe] at h
      exact h
    have hR : σ (LineU.conjN D hD s) =
        ((φ (LineU.conjN D_t hD_t (LineU.conjN P hPN s)) : ↥X) : G) := by
      have hSU : (MulAut.conj P) (LineU.conjN D hD s) =
          LineU.conjN D_t hD_t (LineU.conjN P hPN s) := by
        apply Subtype.ext
        simp only [MulAut.conj_apply, LineU.coe_conjN]
        change (P : GL (Fin n) K) * ((D : GL (Fin n) K) * (s : GL (Fin n) K) *
            (D : GL (Fin n) K)⁻¹) * (P : GL (Fin n) K)⁻¹ =
          D_t * ((P : GL (Fin n) K) * (s : GL (Fin n) K) *
            (P : GL (Fin n) K)⁻¹) * D_t⁻¹
        rw [show D = (P : GL (Fin n) K)⁻¹ * D_t * (P : GL (Fin n) K) from rfl]
        group
      change ((φ ((MulAut.conj P) (LineU.conjN D hD s)) : ↥X) : G) =
        ((φ (LineU.conjN D_t hD_t (LineU.conjN P hPN s)) : ↥X) : G)
      rw [hSU]
    rw [hL, hR]

end CFSG.StandardType

end
