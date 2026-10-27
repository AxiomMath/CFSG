module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Cop
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Om4
public import CFSG.Quasithin.EmptyFaithful.S14117Basic

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

abbrev Rg (T V : Subgroup G) : Subgroup G := T ⊓ Subgroup.centralizer (V : Set G)

abbrev Ng (T V M : Subgroup G) : Subgroup G := M ⊓ Subgroup.normalizer (Rg T V : Set G)

theorem Ng_le_normalizer (T V M : Subgroup G) :
    Ng T V M ≤ Subgroup.normalizer (Rg T V : Set G) := inf_le_right

structure P1Hyp (T V M : Subgroup G) : Prop where
  VT : V ≤ T
  T2 : IsPGroup 2 T
  TM : T ≤ M
  NV : Subgroup.normalizer (V : Set G) = M
  Om : IsOmegaFourPlusOn M V
  pN : pCoreOf 2 (Ng T V M) = Rg T V
  ch : CharTwo (Ng T V M)
  aut : autOn (Ng T V M) V = autOn M V

namespace P1Hyp

variable {T V M : Subgroup G} (h : P1Hyp T V M)

include h

theorem elem : IsElemAbelian 2 V := by
  obtain ⟨hV, -⟩ := h.Om
  exact hV

theorem sq (v : G) (hv : v ∈ V) : v * v = 1 := by
  simpa [pow_two] using h.elem.2 v hv

theorem R2 : IsPGroup 2 (Rg T V) := h.T2.to_le inf_le_left

theorem TN [Finite G] : T ≤ Ng T V M := by
  refine le_inf h.TM fun t ht => ?_
  have htN : t ∈ Subgroup.normalizer (V : Set G) := h.NV ▸ h.TM ht
  have h1 : t ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer ht
  have h2 := mem_normalizer_centralizer htN
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [h1 x, h2 x]

theorem NVn : Ng T V M ≤ Subgroup.normalizer (V : Set G) := h.NV ▸ inf_le_left

abbrev A : Subgroup G := cenMod (Ng T V M) (Rg T V) V h.NVn (Ng_le_normalizer T V M)

abbrev Ak : Subgroup G := h.A ⊓ Subgroup.centralizer (V : Set G)

variable [Finite G]

theorem exists_c {a : G} (haT : a ∈ T) (ha2 : a * a = 1)
    (haC : a ∉ Subgroup.centralizer (V : Set G)) (haR : ∀ r ∈ Rg T V, a * r * a⁻¹ * r⁻¹ ∈ V) :
    ∃ (α : MulAut ↥V) (c : G) (hc : c ∈ Subgroup.normalizer (V : Set G)),
      c ∈ h.A ∧ Odd (orderOf c) ∧ conjAct V ⟨c, hc⟩ = α ∧ α ^ 3 = 1 ∧ α ≠ 1 ∧
      (∀ v : V, v ≠ 1 → α v ≠ v) ∧
      (∀ g ∈ autOn M V, g * α * g⁻¹ = α ∨ g * α * g⁻¹ = α⁻¹) ∧
      ∃ haN : a ∈ Subgroup.normalizer (V : Set G),
        conjAct V ⟨a, haN⟩ * α * (conjAct V ⟨a, haN⟩)⁻¹ = α⁻¹ := by
  classical
  have haN : a ∈ Subgroup.normalizer (V : Set G) := h.NV ▸ h.TM haT
  have hāM : conjAct V ⟨a, haN⟩ ∈ autOn M V := mem_autOn_iff_exists.mpr ⟨a, haN, h.TM haT, rfl⟩
  have hā1 : conjAct V ⟨a, haN⟩ ≠ 1 := fun h1 => haC (A4.conjAct_eq_one_iff.mp h1)
  have hā2 : conjAct V ⟨a, haN⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨a, haN⟩ : Subgroup.normalizer (V : Set G)) ^ 2 = 1 :=
      Subtype.ext (by simpa [pow_two] using ha2)
    rw [this, map_one]
  obtain ⟨α, hαM, hα3, hα1, hαfree, hinv, hnorm⟩ := om4_free_three_on h.Om hāM hā1 hā2
  have hαN : α⁻¹ ∈ autOn (Ng T V M) V := h.aut ▸ (autOn M V).inv_mem hαM
  obtain ⟨n, hnN', hnN, hnρ⟩ := mem_autOn_iff_exists.mp hαN
  have haA : a ∈ h.A := ⟨h.TN haT, haR⟩
  have hyA : n * a * n⁻¹ * a⁻¹ ∈ h.A :=
    h.A.mul_mem (conj_mem_cenMod hnN haA) (h.A.inv_mem haA)
  have hyN : n * a * n⁻¹ * a⁻¹ ∈ Subgroup.normalizer (V : Set G) := h.NVn (cenMod_le hyA)
  have hα2 : α⁻¹ = α ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hα3)
  have hyρ : conjAct V ⟨n * a * n⁻¹ * a⁻¹, hyN⟩ = α := by
    have e : (⟨n * a * n⁻¹ * a⁻¹, hyN⟩ : Subgroup.normalizer (V : Set G)) =
        ⟨n, hnN'⟩ * ⟨a, haN⟩ * ⟨n, hnN'⟩⁻¹ * ⟨a, haN⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hnρ, inv_inv]
    calc α⁻¹ * conjAct V ⟨a, haN⟩ * α * (conjAct V ⟨a, haN⟩)⁻¹
        = α⁻¹ * (conjAct V ⟨a, haN⟩ * α * (conjAct V ⟨a, haN⟩)⁻¹) := by group
      _ = α⁻¹ * α⁻¹ := by rw [hinv]
      _ = α := by rw [hα2, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_add, hα3, one_mul, pow_one]
  obtain ⟨y2, c, hyy, hy2z, hcz, ⟨k, hk⟩, hcodd⟩ := E2.exists_two_part_odd_part (n * a * n⁻¹ * a⁻¹)
  have hcA : c ∈ h.A := (Subgroup.zpowers_le.mpr hyA) hcz
  have hcN : c ∈ Subgroup.normalizer (V : Set G) := h.NVn (cenMod_le hcA)
  have hy2N : y2 ∈ Subgroup.normalizer (V : Set G) :=
    h.NVn (cenMod_le ((Subgroup.zpowers_le.mpr hyA) hy2z))
  have hy2ρ : conjAct V ⟨y2, hy2N⟩ = 1 := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy2z
    have e : (⟨y2, hy2N⟩ : Subgroup.normalizer (V : Set G)) =
        (⟨n * a * n⁻¹ * a⁻¹, hyN⟩ : Subgroup.normalizer (V : Set G)) ^ m :=
      Subtype.ext (by simp [hm])
    have hord : orderOf (conjAct V ⟨y2, hy2N⟩) ∣ 3 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [e, map_zpow, hyρ, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα3,
        one_zpow]
    have h2k : conjAct V ⟨y2, hy2N⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨y2, hy2N⟩ : Subgroup.normalizer (V : Set G)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have hord2 : orderOf (conjAct V ⟨y2, hy2N⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2k
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord hord2 |> fun h => by omega)
  have hcρ : conjAct V ⟨c, hcN⟩ = α := by
    have e : (⟨n * a * n⁻¹ * a⁻¹, hyN⟩ : Subgroup.normalizer (V : Set G)) = ⟨c, hcN⟩ * ⟨y2, hy2N⟩ :=
      Subtype.ext hyy
    rw [← hyρ, e, map_mul, hy2ρ, mul_one]
  refine ⟨α, c, hcN, hcA, hcodd, hcρ, hα3, hα1, hαfree, hnorm, haN, hinv⟩

end P1Hyp

end Y15111

end CFSG.Quasithin
