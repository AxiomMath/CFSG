module

public import CFSG.Quasithin.H13.A6S13821zh
public import CFSG.Quasithin.H13.A6S13821zk

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

attribute [local instance] commGroupOfFact

namespace A6S20

variable {G : Type} [Group G] [Finite G]

theorem exists_two_part {H Q K : Subgroup G} (hQ : H ≤ Subgroup.normalizer (Q : Set G))
    (hKH : K ≤ H) {t c : G} (htH : t ∈ H) (hcH : c ∈ H) (htc : t * c * t⁻¹ * c ∈ Q)
    (htK : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ Q) :
    ∃ s ∈ H, (∃ e : ℕ, s ^ 2 ^ e = 1) ∧ s * c * s⁻¹ * c ∈ Q ∧
      ∀ k ∈ K, s * k * s⁻¹ * k⁻¹ ∈ Q := by
  have hconj : ∀ g ∈ H, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hQ hg) q).mp hq
  have hCmul : ∀ y ∈ H, ∀ u ∈ H, ∀ v ∈ H, u * y * u⁻¹ * y⁻¹ ∈ Q → v * y * v⁻¹ * y⁻¹ ∈ Q →
      (u * v) * y * (u * v)⁻¹ * y⁻¹ ∈ Q := by
    intro y _ u hu v _ h1 h2
    have e : (u * v) * y * (u * v)⁻¹ * y⁻¹ =
        u * (v * y * v⁻¹ * y⁻¹) * u⁻¹ * (u * y * u⁻¹ * y⁻¹) := by group
    rw [e]
    exact Q.mul_mem (hconj u hu _ h2) h1
  have hCpow : ∀ y ∈ H, ∀ u ∈ H, u * y * u⁻¹ * y⁻¹ ∈ Q → ∀ j : ℕ,
      u ^ j * y * (u ^ j)⁻¹ * y⁻¹ ∈ Q := by
    intro y hy u hu h j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      exact hCmul y hy _ (H.pow_mem hu j) u hu ih h
  have hPP : t * t * c * (t * t)⁻¹ * c⁻¹ ∈ Q := by
    have e : t * t * c * (t * t)⁻¹ * c⁻¹ =
        t * (t * c * t⁻¹ * c) * t⁻¹ * (c * (t * c * t⁻¹ * c)⁻¹ * c⁻¹) := by group
    rw [e]
    exact Q.mul_mem (hconj t htH _ htc) (hconj c hcH _ (Q.inv_mem htc))
  obtain ⟨a, b, hb, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos t).ne'
  obtain ⟨j, rfl⟩ := hb
  refine ⟨t ^ (2 * j + 1), H.pow_mem htH _, ⟨a, ?_⟩, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  ·
    have e : t ^ (2 * j + 1) = t * (t * t) ^ j := by
      rw [pow_succ', pow_mul, sq]
    rw [e]
    have h1 := hCpow c hcH (t * t) (H.mul_mem htH htH) hPP j
    have e' : t * (t * t) ^ j * c * (t * (t * t) ^ j)⁻¹ * c =
        t * ((t * t) ^ j * c * ((t * t) ^ j)⁻¹ * c⁻¹) * t⁻¹ * (t * c * t⁻¹ * c) := by group
    rw [e']
    exact Q.mul_mem (hconj t htH _ h1) htc
  · intro k hk
    have hkH := hKH hk
    exact hCpow k hkH t htH (htK k hk) _

end A6S20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_ff_13820a
    (h36c : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4) (h13 : Lem13813)
    (hD310 : D310) (hD391 : D391) (hI4 : Insp4) {H K : Subgroup G} {n : ℕ}
    (hC : S.Ctx13820 H K n) (ha : S.Case13820aHyp H K) :
    ∃ hF : HypF918 T V L (fsuV1 T V) S.V3 H K, ∃ I : Subgroup G, fsuV1 T V ≤ I ∧
      ∃ hIU : I ≤ conjClosure S.V3 H, IsIrrPlusTildeT hF hIU ∧
      T ≤ Subgroup.normalizer (I : Set G) ∧
      (haveI := factElem hF hIU
       IsFFModule (autSec (autIH (fsuV1 T V) I H K ⊔ autIH (fsuV1 T V) I H T)
        (subM (fsuV1 T V) (conjClosure I H) I)
        (fixV (autIH (fsuV1 T V) I H (conjClosure K T))))) := by
  obtain ⟨hS, hH, hK, hKn, hHK, -, -⟩ := hC
  obtain ⟨-, hXc, hHX, t, htH, htK, htX⟩ := ha
  obtain ⟨-, -, hF⟩ := S.hypF918_K0 h36c h37 h38 h139 h1334 h13 hS hH hK
  have e : (K ⊔ T) ⊔ S.L1 = H := by
    rw [hHK, sup_assoc, sup_comm T S.L1]
  rw [e] at hF
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTK : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.mp (hKn (hTH ht)) k).mp hk) (le_conjClosure K T)
  obtain ⟨c, hcX, hc3, hθ, -⟩ := S.exists_c_13820a hS hH hHX
  have P := S.plusData_X13820
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hcH : c ∈ H := hL1H (P.le_L1 hcX)
  have hXO : pCoreOf 2 S.X13820 ≤ pCoreOf 2 H := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hchar : (CFSG.Open.pCore 2 ↥S.X13820).Characteristic := by
      infer_instance
    have hHO : H ≤ Subgroup.normalizer ((pCoreOf 2 S.X13820 : Subgroup G) : Set G) :=
      hHX.trans (normalizer_le_normalizer_map_of_characteristic (CFSG.Open.pCore 2 ↥S.X13820))
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (P.le_L1.trans hL1H)) hHO
      (pCoreOf_isPGroup 2 _)
  obtain ⟨s, hsH, ⟨e₂, hs2⟩, hsc, hsK⟩ := A6S20.exists_two_part (le_normalizer_pCoreOf 2 H)
    hKH htH hcH (hXO (htX c hcX)) htK
  obtain ⟨I, hV₁I, hIU, hirrT, hTI, hFF⟩ := A6S20.exists_ff_of_cube hF
    (S.sqtkGroup_of_mem_Hz hH) hTK hD310 hD391 hI4 hcH hc3 hθ (hXc c hcX) hsH hsK hsc hs2
  exact ⟨hF, I, hV₁I, hIU, hirrT, hTI, hFF⟩

end Setting4

end CFSG.Quasithin.H13.A6
