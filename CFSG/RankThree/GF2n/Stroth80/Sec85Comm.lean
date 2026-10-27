module

public import CFSG.RankThree.GF2n.Stroth80.Sec85CommEnd
public import CFSG.RankThree.GF2n.Stroth80.Sec85CommMod
public import CFSG.RankThree.GF2n.Stroth80.Sec85CommOdd
public import CFSG.RankThree.GF2n.Stroth80.Sec8RtPerfect
public import CFSG.RankThree.GF2n.Stroth80.Sec86Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec86MinOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec51Of34
public import CFSG.RankThree.GF2n.Stroth80.Sec8Canon
public import CFSG.RankThree.GF2n.Stroth80.Sec8FixedPoint

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GroupTheory.SteinbergBY (isPGroup_inSubgroup_pCore)
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q : Subgroup G}

theorem sec85_centre_le {R N Zc : Subgroup G} (hQn : ∀ g ∈ M, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hRM : R ≤ M) (hNR : N ≤ R) (hNn : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hZN : Zc ≤ N)
    (hZc : ∀ z ∈ Zc, ∀ b ∈ N, ⁅z, b⁆ ∈ Q)
    (hirr : ∀ U : Subgroup G, Zc ≤ U → U ≤ N → (∀ ρ ∈ R, conjSubgroup ρ U = U) →
      U = Zc ∨ U = N) (hnon : ¬ ⁅N, N⁆ ≤ Q) :
    ∀ a ∈ N, (∀ b ∈ N, ⁅a, b⁆ ∈ Q) → a ∈ Zc := by
  classical
  let U : Subgroup G :=
    { carrier := {a | a ∈ N ∧ ∀ b ∈ N, ⁅a, b⁆ ∈ Q}
      mul_mem' := by
        rintro a₁ a₂ ⟨ha₁, h₁⟩ ⟨ha₂, h₂⟩
        refine ⟨N.mul_mem ha₁ ha₂, fun b hb => ?_⟩
        have e : ⁅a₁ * a₂, b⁆ = a₁ * ⁅a₂, b⁆ * a₁⁻¹ * ⁅a₁, b⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Q.mul_mem (hQn a₁ (hRM (hNR ha₁)) _ (h₂ b hb)) (h₁ b hb)
      one_mem' := ⟨N.one_mem, fun b _ => by
        rw [show ⁅(1 : G), b⁆ = 1 by simp [commutatorElement_def]]
        exact Q.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, h⟩
        refine ⟨N.inv_mem ha, fun b hb => ?_⟩
        have e : ⁅a⁻¹, b⁆ = a⁻¹ * (⁅a, b⁆)⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact hQn a⁻¹ (hRM (hNR (N.inv_mem ha))) _ (Q.inv_mem (h b hb)) }
  have hZU : Zc ≤ U := fun z hz => ⟨hZN hz, hZc z hz⟩
  have hUN : U ≤ N := fun a ha => ha.1
  have hinv : ∀ ρ ∈ R, conjSubgroup ρ U = U := by
    intro ρ hρ
    refine conjSubgroup_eq_self_iff.mpr (Subgroup.mem_normalizer_fintype fun a ha => ?_)
    obtain ⟨haN, h⟩ := ha
    refine ⟨hNn ρ hρ a haN, fun b hb => ?_⟩
    have e : ⁅ρ * a * ρ⁻¹, b⁆ = ρ * ⁅a, ρ⁻¹ * b * ρ⁻¹⁻¹⁆ * ρ⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hQn ρ (hRM hρ) _ (h _ (hNn ρ⁻¹ (R.inv_mem hρ) b hb))
  rcases hirr U hZU hUN hinv with h | h
  · intro a ha hab
    have h1 : a ∈ U := ⟨ha, hab⟩
    rw [h] at h1
    exact h1
  · exfalso
    apply hnon
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have h1 : a ∈ U := by
      rw [h]
      exact ha
    exact h1.2 b hb

theorem step85Comm_of (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement) (hzt : Sec8ZtStatement)
    (hA : Sec8AExistsStatement) (h83 : Stroth83Statement) (h84 : Stroth84Statement) :
    Step85CommStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 x hx hconc hxN hxZ
  classical
  have hRoot := stroth310Root_of_34 h34
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have hxK : x ∈ NormH0 M Z Z0 := by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  obtain ⟨k, hxk⟩ : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := isPGroup_inSubgroup_pCore 2 (NormH0 M Z Z0) ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hxH : x ∈ H0 M Z := hxK.1
  have hxM : x ∈ M := hxH.1
  have hxZ0n : x ∈ Subgroup.normalizer (Z0 : Set G) := hxK.2
  have hxR : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅x, ρ⁆ ∈ hc.CN t := hconc.1
  obtain ⟨hxV₁c, hxW₁c⟩ := hconc.2
  obtain ⟨-, hxVt⟩ := sec8_normalizes_of_zt hzt h51 hA hc hs hZ0 hxK
  have hxV : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp hxVt
  have hxV₁ : x ∈ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) :=
    sec8Canon_of h34 hRoot G M Q Z B hc n t hs r hr x hxM hxV
  have hxcz : ∀ z ∈ Z, x * z * x⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.mp hxH.2 z hz, mul_inv_cancel_right]
  have hQn : ∀ a ∈ M, ∀ y ∈ Q, a * y * a⁻¹ ∈ Q := fun a ha y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ha) y).mp hy
  have hRM := hc.Rt_le_M t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun y hy => (Ctx.mem_CN.1 hy).1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0N : Z0 ≤ hc.CN t := sec8_Z0_le_CN hc hs hZ0
  have hN2 : IsPGroup 2 ↥(hc.CN t) := sec8_isPGroup_CN h34 h51 hA hc hs hZ0
  have hPts : Sec5NatPointsSpStatement := sec5NatPointsSp_of_34 h34
  have hMin : Sec86MinOrderStatement := sec86MinOrder_of h51 hA hPts
  have hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 :=
    sec86Irred_of_inputs h83 h51 hA hMin G M Q Z B hc n t hs Z0 hZ0
  obtain ⟨hNN, hNsq, -, hirr'⟩ := hirr
  have hNn : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ hc.CN t, ρ * y * ρ⁻¹ ∈ hc.CN t :=
    fun ρ hρ y hy => hc.CN_conj_mem ht hρ hy
  have hxNn : ∀ y ∈ hc.CN t, x * y * x⁻¹ ∈ hc.CN t := by
    intro y hy
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by simp [commutatorElement_def]
    rw [e]
    exact (hc.CN t).mul_mem (hxR y (hNR hy)) hy
  have hZI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ z ∈ Z0, ρ * z * ρ⁻¹ ∈ Z0 := fun ρ hρ z hz =>
    (Subgroup.mem_normalizer_iff.mp
      (hZ0.mem_normalizer (fun σ hσ y hy => hQn σ (hRM hσ) y hy) hρ) z).mp hz
  have hxZI : ∀ y ∈ Z0, x * y * x⁻¹ ∈ Z0 := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hxZ0n y).mp hy
  have hsec : SecHyp (Rt M (LB M Q B) t) (hc.CN t) Z0 := ⟨hZ0N, hNN, hNsq, hNn, hZI⟩
  have hxR' : ∀ ρ ∈ Rt M (LB M Q B) t, ρ * x * ρ⁻¹ * x⁻¹ ∈ hc.CN t := fun ρ hρ => by
    have h1 := (hc.CN t).inv_mem (hxR ρ hρ)
    rwa [commutatorElement_inv, commutatorElement_def] at h1
  have hxNZ : ∀ y ∈ hc.CN t, ⁅x, y⁆ ∈ Z0 :=
    sec8_isol hsec hxNn hxZI hxR' (fun a ha b hb => hNN a ha b hb) hxk hirr'
  have hZc : ∀ z ∈ Z0, ∀ ρ ∈ Rt M (LB M Q B) t, ⁅z, ρ⁆ ∈ Q := fun z hz ρ hρ =>
    hZ0.comm_mem hz hρ
  have hZ : ∀ a ∈ hc.CN t, (∀ b ∈ hc.CN t, ⁅a, b⁆ ∈ Q) → a ∈ Z0 :=
    sec85_centre_le hQn hRM hNR hNn hZ0N (fun z hz b hb => hZc z hz b (hNR hb)) hirr'
      (h84 G M Q Z B hc n t hs)
  obtain ⟨y, hyR, hy3, hfpf⟩ := sec85_exists_fpf h34 h51 hA hc hs hZ0
  have hxR'' : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ, x⁆ ∈ hc.CN t := fun ρ hρ => by
    rw [← commutatorElement_inv]
    exact (hc.CN t).inv_mem (hxR ρ hρ)
  have hxZ' : ∀ z ∈ Z0, ⁅x, z⁆ ∈ Q := fun z hz => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hxZ z hz)
  obtain ⟨n₀, hn₀, hn₀R⟩ := sec85_comm_core_mod hQn hRM hNR hQZ0 hZ0N hNn hN2 hZc hNN hNsq hZ
    (sec8_Rt_eq_comm_mul_CN hc hs) hxM hxNn hxR'' hxZ' hxNZ hyR hy3 hfpf
  have hn₀H : n₀ ∈ H0 M Z := (sec8_Rt_le_NormH0 hc hZ0 (hNR hn₀)).1
  have hwH : x * n₀ ∈ H0 M Z := (H0 M Z).mul_mem hxH hn₀H
  have hwR : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅x * n₀, ρ⁆ ∈ Q := fun ρ hρ => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hn₀R ρ hρ)
  have h53b := h53.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl
  have h53d := h53.2.2.2.1 G M Q Z B hc n t h5 hs.spNat r hr.mem hr.plane (conjSubgroup r B)
    (hc.CN t) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hwV₁ : ∀ v ∈ Sec8V1 M Q Z B t r, ⁅x * n₀, v⁆ ∈ Z := by
    intro v hv
    have e : ⁅x * n₀, v⁆ = x * ⁅n₀, v⁆ * x⁻¹ * ⁅x, v⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hz := h53d.1 n₀ hn₀ v hv
    rw [hxcz _ hz]
    exact Z.mul_mem hz (hxV₁c v hv)
  have hwW₁ : ∀ w ∈ Sec8W1 M Q Z B t r, ⁅x * n₀, w⁆ ∈ Sec8V1 M Q Z B t r := by
    intro w hw
    have e : ⁅x * n₀, w⁆ = x * ⁅n₀, w⁆ * x⁻¹ * ⁅x, w⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Sec8V1 M Q Z B t r).mul_mem
      ((Subgroup.mem_normalizer_iff.mp hxV₁ _).mp (h53b.2 n₀ hn₀ w hw)) (hxW₁c w hw)
  have hC := h83 G M Q Z B hc n t hs.toSec5 hs.sp
  have hw := sec85_centralizer_le_Z0 h34 h51 h53 h310chi hzt hA hc hs hr hC hZ0 hwH hwR hwV₁
    hwW₁
  apply hxN
  have hx' : x = (x * n₀) * n₀⁻¹ := by group
  rw [hx']
  exact (hc.CN t).mul_mem (hZ0N hw) ((hc.CN t).inv_mem hn₀)

end CFSG.RankThree.GF2n.Stroth80
