module

public import CFSG.OddTranspositions.WreathBaseMinimal
public import CFSG.OddTranspositions.WreathBase
import CFSG.Timmesfeld.Bridge.OddTranspGenL2
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72WreathL2
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

theorem center_psl2Model_eq_bot {f : ℕ} (hf : 2 ≤ f) : Subgroup.center (PSL2Model f) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (PSL2Model f) :=
    IsBenderGroup.isSimpleGroup (IsBenderGroup.isPSL2 f hf (MulEquiv.refl _))
  rcases (Subgroup.center (PSL2Model f)).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : PSL2Model f, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have : IsMulCommutative (PSL2Model f) := ⟨⟨hcomm⟩⟩
    have hp := IsSimpleGroup.prime_card (α := PSL2Model f)
    rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega)] at hp
    have h2 : 2 ∣ 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hne : 2 ^ f * ((2 ^ f) ^ 2 - 1) ≠ 2 := by
      have h16 : 16 ≤ (2 ^ f) ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h4 2
      have h3 : 3 ≤ (2 ^ f) ^ 2 - 1 := by omega
      have : 12 ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
        calc 12 = 4 * 3 := by norm_num
          _ ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := Nat.mul_le_mul h4 h3
      omega
    exact hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm

theorem centralizer_l2WreathBase {f n : ℕ} (hf : 2 ≤ f) :
    Subgroup.centralizer (l2WreathBase f n : Set (L2Wreath f n)) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  have hcomm : ∀ b : Fin n → PSL2Model f,
      SemidirectProduct.inl b * w = w * SemidirectProduct.inl b := fun b =>
    Subgroup.mem_centralizer_iff.mp hw _ ⟨b, rfl⟩
  have key : ∀ (b : Fin n → PSL2Model f) (i : Fin n),
      b i * w.left i = w.left i * b (w.right.symm i) := by
    intro b i
    have h1 := congrArg SemidirectProduct.left (hcomm b)
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply] at h1
    have h2 := congrFun h1 i
    exact h2
  have : Nontrivial (PSL2Model f) := CFSG.OddTranspositions.psl2Model_nontrivial hf
  obtain ⟨x, hx⟩ := exists_ne (1 : PSL2Model f)
  have hsymm : ∀ i, w.right.symm i = i := by
    intro i
    by_contra hne'
    have := key (Pi.mulSingle (w.right.symm i) x) i
    rw [Pi.mulSingle_eq_of_ne (Ne.symm hne'), Pi.mulSingle_eq_same, one_mul] at this
    exact hx (by simpa using this.symm)
  have hσ : w.right = 1 := by
    ext i
    have := hsymm (w.right i)
    rw [Equiv.symm_apply_apply] at this
    simp only [Equiv.Perm.coe_one, id_eq]
    exact congrArg _ this.symm
  have hleft : w.left = 1 := by
    funext i
    have hc : w.left i ∈ Subgroup.center (PSL2Model f) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := key (Pi.mulSingle i y) i
      rwa [hσ, Equiv.Perm.one_symm, Equiv.Perm.coe_one, id, Pi.mulSingle_eq_same] at this
    rw [center_psl2Model_eq_bot hf, Subgroup.mem_bot] at hc
    exact hc
  exact SemidirectProduct.ext hleft hσ

theorem eq_l2WreathBase_of_isMinimalNormal {f n : ℕ} (hf : 2 ≤ f) (hn : 2 ≤ n)
    {K : Subgroup (L2Wreath f n)} (hK : Asc72.IsMinimalNormal K) : K = l2WreathBase f n := by
  obtain ⟨hKn, hK0, hKmin⟩ := hK
  obtain ⟨hBn, hB0, hBmin⟩ := CFSG.OddTranspositions.base_isMinimalNormal f n hf hn
  have hKB : K ⊓ l2WreathBase f n ≠ ⊥ := by
    intro h
    apply hK0
    rw [eq_bot_iff, ← centralizer_l2WreathBase (n := n) hf]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hc : k * b * k⁻¹ * b⁻¹ ∈ K ⊓ l2WreathBase f n := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := K.mul_mem hk (hKn.conj_mem _ (K.inv_mem hk) b)
        simpa [mul_assoc] using this
      · exact (l2WreathBase f n).mul_mem (hBn.conj_mem b hb k)
          ((l2WreathBase f n).inv_mem hb)
    rw [h, Subgroup.mem_bot] at hc
    have : k * b * k⁻¹ = b := mul_inv_eq_one.mp hc
    calc b * k = k * b * k⁻¹ * k := by rw [this]
      _ = k * b := by group
  rcases hKmin (K ⊓ l2WreathBase f n) (@Subgroup.normal_inf_normal _ _ K _ hKn hBn)
      inf_le_left with h | h
  · exact absurd h hKB
  · have hle : K ≤ l2WreathBase f n := h ▸ inf_le_right
    rcases hBmin K hKn hle with h' | h'
    · exact absurd h' hK0
    · exact h'

theorem card_l2WreathBase (f n : ℕ) :
    Nat.card (l2WreathBase f n) = Nat.card (PSL2Model f) ^ n := by
  rw [l2WreathBase, MonoidHom.range_eq_map, Subgroup.card_map_of_injective
    SemidirectProduct.inl_injective, Subgroup.card_top, Nat.card_fun, Nat.card_fin]

theorem l2Wreath_params_eq {f n f' n' : ℕ} (hf : 2 ≤ f) (hf' : 2 ≤ f') (hn : 2 ≤ n)
    (hn' : 2 ≤ n') (e : L2Wreath f n ≃* L2Wreath f' n') : f = f' ∧ n = n' := by
  classical
  have hmin := CFSG.OddTranspositions.base_isMinimalNormal f n hf hn
  have hmap : Asc72.IsMinimalNormal ((l2WreathBase f n).map e.toMonoidHom) := by
    obtain ⟨hBn, hB0, hBmin⟩ := hmin
    refine ⟨@Subgroup.Normal.map _ _ _ _ _ hBn e.toMonoidHom e.surjective, ?_,
      fun N hN hNle => ?_⟩
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    · have hNc : N.comap e.toMonoidHom ≤ l2WreathBase f n := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := hNle hx
        have : y = x := e.injective hyx
        exact this ▸ hy
      rcases hBmin (N.comap e.toMonoidHom) (hN.comap _) hNc with h | h
      · left
        rw [eq_bot_iff]
        intro z hz
        obtain ⟨x, rfl⟩ := e.surjective z
        have : x ∈ N.comap e.toMonoidHom := hz
        rw [h, Subgroup.mem_bot] at this
        simp [this]
      · right
        apply le_antisymm hNle
        rintro _ ⟨x, hx, rfl⟩
        have : x ∈ N.comap e.toMonoidHom := h ▸ hx
        exact this
  have hbase : (l2WreathBase f n).map e.toMonoidHom = l2WreathBase f' n' :=
    eq_l2WreathBase_of_isMinimalNormal hf' hn' hmap
  have hcardB : Nat.card (PSL2Model f) ^ n = Nat.card (PSL2Model f') ^ n' := by
    rw [← card_l2WreathBase, ← card_l2WreathBase, ← hbase,
      Subgroup.card_map_of_injective e.injective]
  have hcardW : Nat.card (PSL2Model f) ^ n * n.factorial =
      Nat.card (PSL2Model f') ^ n' * n'.factorial := by
    have h1 := Nat.card_congr e.toEquiv
    rw [SemidirectProduct.card, SemidirectProduct.card, Nat.card_fun, Nat.card_fun,
      Nat.card_perm, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
      Nat.card_eq_fintype_card (α := Fin n'), Fintype.card_fin, Fintype.card_fin] at h1
    simpa [Nat.card_eq_fintype_card] using h1
  have hpos : 0 < Nat.card (PSL2Model f) ^ n := pow_pos Nat.card_pos n
  have hfact : n.factorial = n'.factorial := by
    rw [hcardB] at hcardW
    exact Nat.eq_of_mul_eq_mul_left (hcardB ▸ hpos) hcardW
  have hnn : n = n' := (Nat.factorial_inj (by omega)).mp hfact
  subst hnn
  have hL : Nat.card (PSL2Model f) = Nat.card (PSL2Model f') :=
    Nat.pow_left_injective (by omega) hcardB
  rw [CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega),
    CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega)] at hL
  refine ⟨?_, rfl⟩
  have hmono : StrictMono fun k : ℕ => 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h2]
    have h3 : (2 ^ k) ^ 2 - 1 < (2 * 2 ^ k) ^ 2 - 1 := by
      have : (2 ^ k) ^ 2 < (2 * 2 ^ k) ^ 2 := by nlinarith
      have : 1 ≤ (2 ^ k) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    calc 2 ^ k * ((2 ^ k) ^ 2 - 1) ≤ 2 ^ k * ((2 * 2 ^ k) ^ 2 - 1) := Nat.mul_le_mul_left _ h3.le
      _ < 2 * 2 ^ k * ((2 * 2 ^ k) ^ 2 - 1) := by
          have : 0 < (2 * 2 ^ k) ^ 2 - 1 := by
            have : 4 ≤ (2 * 2 ^ k) ^ 2 := by nlinarith
            omega
          nlinarith
  exact hmono.injective hL

end CFSG.OddTranspositions.PartThree

end
