module

public import CFSG.Quasithin.H13.U3S1347C
public import CFSG.Quasithin.H13.U3S1348R

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem conj_mem_closure_of_gen {s : Set G} {g : G} (h : ∀ x ∈ s, g * x * g⁻¹ ∈ closure s)
    {x : G} (hx : x ∈ closure s) : g * x * g⁻¹ ∈ closure s := by
  induction hx using closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem s1347_le_normalizer_of_comm (S : A6.Setting134 G T L V) {H₁ H₂ Hi Hj : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) (hi : Hi ≤ H₁ ⊔ H₂) (hj : Hj ≤ H₁ ⊔ H₂)
    (hTi : T ≤ Hi) (h3i : T.relIndex Hi = 3)
    (hCN : (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) ≤ normalizer (oTwoRes Hi : Set G))
    (hcomm : ⁅oTwoRes Hi, oTwoRes Hj⁆ ≤ centralizer (v0Of T H₁ H₂ : Set G)) :
    oTwoRes Hj ≤ normalizer (oTwoRes Hi : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun k hk y hy => ?_
  refine conj_mem_closure_of_gen (fun x hx => ?_) hy
  obtain ⟨hxH, m, hm, hxm⟩ := hx
  have hx3 := pow_three_of_relIndex_three S.h13.sylow.1 hTi h3i hxH hm hxm
  have hxK : x ∈ oTwoRes Hi := subset_closure ⟨hxH, m, hm, hxm⟩
  have hkH : k ∈ H₁ ⊔ H₂ := hj (oTwoRes_le Hj hk)
  have hxH₀ : x ∈ H₁ ⊔ H₂ := hi hxH
  have hcC : x⁻¹ * (k * x * k⁻¹) ∈ (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) := by
    refine mem_inf.2 ⟨mul_mem (inv_mem hxH₀) (mul_mem (mul_mem hkH hxH₀) (inv_mem hkH)),
      hcomm ?_⟩
    have e : x⁻¹ * (k * x * k⁻¹) = x⁻¹ * k * x⁻¹⁻¹ * k⁻¹ := by group
    rw [e]
    exact commutator_mem_commutator (inv_mem hxK) hk
  set c := x⁻¹ * (k * x * k⁻¹) with hc
  have e : k * x * k⁻¹ = x * c := by rw [hc]; group
  have hxc3 : x * c * (x * c) * (x * c) = 1 := by
    rw [← e]
    have e3 : k * x * k⁻¹ * (k * x * k⁻¹) * (k * x * k⁻¹) = k * (x * x * x) * k⁻¹ := by group
    rw [e3, ← pow_three', hx3, mul_one, mul_inv_cancel]
  have ha : c * x * c⁻¹ ∈ oTwoRes Hi := (mem_normalizer_iff.mp (hCN hcC) x).mp hxK
  have hb : c * (c * x * c⁻¹) * c⁻¹ ∈ oTwoRes Hi :=
    (mem_normalizer_iff.mp (hCN hcC) _).mp ha
  have hc3 : c ^ 3 ∈ oTwoRes Hi := by
    have e3 : c ^ 3 = (c * (c * x * c⁻¹) * c⁻¹)⁻¹ * (c * x * c⁻¹)⁻¹ * x⁻¹ *
        (x * c * (x * c) * (x * c)) := by group
    rw [e3, hxc3, mul_one]
    exact mul_mem (mul_mem (inv_mem hb) (inv_mem ha)) (inv_mem hxK)
  have hco : Nat.Coprime 3 (orderOf c) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    rintro ⟨d, hd⟩
    have hpos : 0 < orderOf c := orderOf_pos c
    have hcd : (c ^ d) ^ 3 = 1 := by
      rw [← pow_mul, show d * 3 = orderOf c by omega, pow_orderOf_eq_one]
    exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
      (s1347_eq_one_of_threePow S h hH₀ ⟨pow_mem hcC.1 d, pow_mem hcC.2 d⟩ (k := 1)
        (by rwa [pow_one]))
  rw [e]
  exact mul_mem hxK (mem_of_pow_mem_of_coprime hc3 hco)

theorem s1347_normal_of_comm (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂))
    (hcomm : ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ centralizer (v0Of T H₁ H₂ : Set G)) :
    H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₁ : Set G) ∧ H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₂ : Set G) := by
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  obtain ⟨hCN₁, hCN₂⟩ := s1347_centralizer_le_normalizer h hH₀
  have hK₂ := s1347_le_normalizer_of_comm S h hH₀ le_sup_left le_sup_right h.inH₁.1 h3₁ hCN₁
    hcomm
  have hK₁ := s1347_le_normalizer_of_comm S h hH₀ le_sup_right le_sup_left h.inH₂.1 h3₂ hCN₂
    (by rwa [commutator_comm])
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have hsyl₂ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₂.1
  refine ⟨sup_le (le_normalizer_oTwoRes H₁) ?_, sup_le ?_ (le_normalizer_oTwoRes H₂)⟩
  · exact (le_oTwoRes_sup_of_isSylowTwoOf hsyl₂).trans
      (sup_le hK₂ (h.inH₁.1.trans (le_normalizer_oTwoRes H₁)))
  · exact (le_oTwoRes_sup_of_isSylowTwoOf hsyl₁).trans
      (sup_le hK₁ (h.inH₂.1.trans (le_normalizer_oTwoRes H₂)))

omit [Finite G] in
theorem s1347_mul_of_normal {H₁ H₂ : Subgroup G} (hTH₂ : T ≤ H₂) (hH₁ : H₁ ≤ oTwoRes H₁ ⊔ T)
    (hN : H₁ ⊔ H₂ ≤ normalizer (oTwoRes H₁ : Set G)) :
    ∀ x ∈ H₁ ⊔ H₂, ∃ a ∈ H₁, ∃ b ∈ H₂, x = a * b := by
  intro x hx
  have hle : H₁ ⊔ H₂ ≤ oTwoRes H₁ ⊔ H₂ :=
    sup_le (hH₁.trans (sup_le le_sup_left (hTH₂.trans le_sup_right))) le_sup_right
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    Vol2.Ch11.SecC.mem_sup_of_le_normalizer (le_sup_right.trans hN) (hle hx)
  exact ⟨a, oTwoRes_le H₁ ha, b, hb, rfl⟩

theorem s1347_comm_le_of_normal (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hN₁ : oTwoRes H₂ ≤ normalizer (oTwoRes H₁ : Set G))
    (hN₂ : oTwoRes H₁ ≤ normalizer (oTwoRes H₂ : Set G)) :
    ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ pCoreOf 2 (oTwoRes H₁) ⊓ pCoreOf 2 (oTwoRes H₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hle : ⁅oTwoRes H₁, oTwoRes H₂⁆ ≤ oTwoRes H₁ ⊓ oTwoRes H₂ := by
    refine le_inf (le_normalizer_iff_commutator_le_left.mp hN₁) ?_
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hN₂
  have hsup : ∀ {H : Subgroup G} {y : G}, T ≤ H → T.relIndex H = 3 → y ∈ H → y ^ 3 = 1 →
      y ≠ 1 → T ⊔ zpowers y = H := by
    intro H y hTH h3 hyH hy3 hy1
    rcases eq_or_eq_of_relIndex_three h3 le_sup_left (sup_le hTH (zpowers_le.2 hyH)) with e | e
    · exact absurd (eq_one_of_mem_of_cube S.h13.sylow.1 (e ▸ mem_sup_right
        (mem_zpowers y)) hy3) hy1
    · exact e
  have hp : IsPGroup 2 ↥(oTwoRes H₁ ⊓ oTwoRes H₂) := by
    rintro ⟨x, hx⟩
    obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, Subtype.ext ?_⟩
    show x ^ 2 ^ a = 1
    have hy₁ : x ^ 2 ^ a ∈ H₁ := oTwoRes_le H₁ (pow_mem hx.1 _)
    have hy₂ : x ^ 2 ^ a ∈ H₂ := oTwoRes_le H₂ (pow_mem hx.2 _)
    have hy3 := pow_three_of_relIndex_three S.h13.sylow.1 h.inH₁.1 h3₁ hy₁ hm
      (by rw [← pow_mul, ← hxm, pow_orderOf_eq_one])
    by_contra hy1
    exact h.ne ((hsup h.inH₁.1 h3₁ hy₁ hy3 hy1).symm.trans (hsup h.inH₂.1 h3₂ hy₂ hy3 hy1))
  refine hle.trans (le_inf ?_ ?_)
  · exact le_pCoreOf_of_le_normalizer inf_le_left (fun k hk =>
      mem_normalizer_inf_of (le_normalizer hk) (hN₂ hk)) hp
  · exact le_pCoreOf_of_le_normalizer inf_le_right (fun k hk =>
      mem_normalizer_inf_of (hN₁ hk) (le_normalizer hk)) hp

end CFSG.Quasithin.H13.U3
