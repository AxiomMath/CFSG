module

public import CFSG.Quasithin.H13.L32A764d
public import CFSG.Quasithin.H13.L32A767f

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_le_two_of {P R : Subgroup G}
    (h : ∀ a ∈ R, ∀ b ∈ R, a ∉ P → b ∉ P → a⁻¹ * b ∈ P) : P.relIndex R ≤ 2 := by
  by_cases hRP : R ≤ P
  · rw [Subgroup.relIndex_eq_one.mpr hRP]
    norm_num
  obtain ⟨a, haR, haP⟩ := Set.not_subset.mp hRP
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  let f : Bool → ↥R ⧸ P.subgroupOf R := fun b =>
    if b then QuotientGroup.mk ⟨a, haR⟩ else QuotientGroup.mk (1 : ↥R)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective x
    by_cases hr : (r : G) ∈ P
    · refine ⟨false, ?_⟩
      show QuotientGroup.mk (1 : ↥R) = (QuotientGroup.mk r : ↥R ⧸ P.subgroupOf R)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hr
    · refine ⟨true, ?_⟩
      show QuotientGroup.mk ⟨a, haR⟩ = (QuotientGroup.mk r : ↥R ⧸ P.subgroupOf R)
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using h a haR r r.2 haP hr
  have hle := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hle

omit [Finite G] in
theorem mulAut_mul_conj {Q : Type} [Group Q] (α : MulAut Q) (w : Q) :
    α * MulAut.conj w * α⁻¹ = MulAut.conj (α w) :=
  MulEquiv.ext fun x => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem exists_normalizing_odd {K' R : Subgroup G} {Q : Type} [Group Q] [Finite Q]
    (π : ↥K' →* Q) (hπs : Function.Surjective π) (hπk : π.ker = (pCoreOf 2 K').subgroupOf K')
    (hRK : R ≤ Subgroup.normalizer (K' : Set G))
    (hOR : pCoreOf 2 K' ≤ R) {S W : Subgroup Q} (hS : ∀ k : ↥K', π k ∈ S ↔ (k : G) ∈ R)
    (hWS : W ≤ S) {c : Q} (hcW : c ∈ Subgroup.normalizer (W : Set Q)) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1)
    (hRW : ∀ r : ↥R, ∀ w ∈ W,
      autHom π hπs hπk (Subgroup.inclusion hRK r) w ∈ W)
    (hcrit : ∀ a b : ↥R, autHom π hπs hπk (Subgroup.inclusion hRK a) ∉ W.map MulAut.conj →
      autHom π hπs hπk (Subgroup.inclusion hRK b) ∉ W.map MulAut.conj →
      autHom π hπs hπk (Subgroup.inclusion hRK (a⁻¹ * b)) ∈ W.map MulAut.conj) :
    ∃ P : Subgroup G, P ≤ R ∧ R ≤ Subgroup.normalizer (P : Set G) ∧ P.relIndex R ≤ 2 ∧
      ∃ y ∈ K', y ^ 3 = 1 ∧ y ≠ 1 ∧ y ∈ Subgroup.normalizer (P : Set G) := by
  set Φ := autHom π hπs hπk with hΦ
  set ΦR := Φ.comp (Subgroup.inclusion hRK) with hΦR
  set cW := W.map (MulAut.conj : Q →* MulAut Q) with hcW'
  set P := (cW.comap ΦR).map R.subtype with hP
  have hmemP : ∀ x : G, x ∈ P ↔ ∃ hx : x ∈ R, ΦR ⟨x, hx⟩ ∈ cW := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r.2, hr⟩
    · rintro ⟨hx, hΦx⟩
      exact ⟨⟨x, hx⟩, hΦx, rfl⟩
  have hPR : P ≤ R := Subgroup.map_subtype_le _
  have hRP : R ≤ Subgroup.normalizer (P : Set G) := by
    intro r hr
    refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
    obtain ⟨hxR, hxW⟩ := (hmemP x).mp hx
    refine (hmemP _).mpr ⟨mul_mem (mul_mem hr hxR) (inv_mem hr), ?_⟩
    obtain ⟨w, hw, hwx⟩ := hxW
    have e : ΦR ⟨r * x * r⁻¹, mul_mem (mul_mem hr hxR) (inv_mem hr)⟩ =
        ΦR ⟨r, hr⟩ * ΦR ⟨x, hxR⟩ * (ΦR ⟨r, hr⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e, ← hwx, mulAut_mul_conj]
    exact ⟨_, hRW ⟨r, hr⟩ w hw, rfl⟩
  have hidx : P.relIndex R ≤ 2 := by
    refine relIndex_le_two_of fun a ha b hb haP hbP => ?_
    refine (hmemP _).mpr ⟨mul_mem (inv_mem ha) hb, ?_⟩
    have h1 : ΦR ⟨a, ha⟩ ∉ cW := fun h => haP ((hmemP a).mpr ⟨ha, h⟩)
    have h2 : ΦR ⟨b, hb⟩ ∉ cW := fun h => hbP ((hmemP b).mpr ⟨hb, h⟩)
    exact hcrit ⟨a, ha⟩ ⟨b, hb⟩ h1 h2
  obtain ⟨y₀, hy₀⟩ := hπs c
  have hy₀3 : (y₀ ^ 3 : ↥K') ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hy₀, hc3]
  rw [hπk, Subgroup.mem_subgroupOf] at hy₀3
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 K') ⟨_, hy₀3⟩
  have hn' : ((y₀ : G) ^ 3) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  set y : ↥K' := y₀ ^ 4 ^ n with hy
  have hpow : ∀ k : ℕ, c ^ 4 ^ k = c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, show 4 = 3 + 1 by rfl, pow_succ, hc3, one_mul]
  have hπy : π y = c := by rw [hy, map_pow, hy₀, hpow]
  have hy3 : (y : G) ^ 3 = 1 := by
    rw [hy, SubgroupClass.coe_pow, ← pow_mul, mul_comm, pow_mul,
      show (4 : ℕ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num, pow_mul, hn', one_pow]
  have hy1 : (y : G) ≠ 1 := by
    intro h1
    apply hc1
    rw [← hπy, show y = 1 from Subtype.ext h1, map_one]
  refine ⟨P, hPR, hRP, hidx, y, y.2, hy3, hy1, ?_⟩
  have hyN : (y : G) ∈ Subgroup.normalizer (K' : Set G) := Subgroup.le_normalizer y.2
  have hΦy : Φ ⟨y, hyN⟩ = MulAut.conj c := by rw [← hπy]; exact autHom_coe π hπs hπk y
  refine mem_normalizer_of_forall_conj_mem fun x hx => ?_
  obtain ⟨hxR, w, hw, hwx⟩ := (hmemP x).mp hx
  obtain ⟨s, hsw⟩ := hπs w
  have hsR : (s : G) ∈ R := (hS s).mp (hsw ▸ hWS hw)
  have hsN : (s : G) ∈ Subgroup.normalizer (K' : Set G) := Subgroup.le_normalizer s.2
  have hc'R : (s : G)⁻¹ * x ∈ R := mul_mem (inv_mem hsR) hxR
  have hΦc' : Φ ⟨(s : G)⁻¹ * x, mul_mem (inv_mem hsN) (hRK hxR)⟩ = 1 := by
    have e : (⟨(s : G)⁻¹ * x, mul_mem (inv_mem hsN) (hRK hxR)⟩ :
        ↥(Subgroup.normalizer (K' : Set G))) = (⟨s, hsN⟩)⁻¹ * Subgroup.inclusion hRK ⟨x, hxR⟩ :=
      rfl
    rw [e, map_mul, map_inv, autHom_coe π hπs hπk s, hsw]
    have : Φ (Subgroup.inclusion hRK ⟨x, hxR⟩) = MulAut.conj w := hwx.symm
    rw [this, inv_mul_cancel]
  have hcomm := (autHom_eq_one_iff π hπs hπk _).mp hΦc'
  have hxR' : (y : G) * x * (y : G)⁻¹ ∈ R := by
    have h1 : (y : G) * s * (y : G)⁻¹ ∈ R := by
      have hmem : (y : G) * s * (y : G)⁻¹ ∈ K' := mul_mem (mul_mem y.2 s.2) (inv_mem y.2)
      refine (hS ⟨_, hmem⟩).mp ?_
      have e : π ⟨_, hmem⟩ = c * w * c⁻¹ := by
        rw [← hπy, ← hsw, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact hWS ((Subgroup.mem_normalizer_iff.mp hcW w).mp hw)
    have h2 : (y : G) * ((s : G)⁻¹ * x) * (y : G)⁻¹ * ((s : G)⁻¹ * x)⁻¹ ∈ R := by
      have h3 := hcomm _ (inv_mem y.2)
      have h4 : (y : G) * (((s : G)⁻¹ * x) * (y : G)⁻¹⁻¹⁻¹ * ((s : G)⁻¹ * x)⁻¹ *
          (y : G)⁻¹⁻¹) * (y : G)⁻¹ ∈ pCoreOf 2 K' :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K' y.2) _).mp
          (by simpa using h3)
      refine hOR ?_
      rwa [show (y : G) * (((s : G)⁻¹ * x) * (y : G)⁻¹⁻¹⁻¹ * ((s : G)⁻¹ * x)⁻¹ *
        (y : G)⁻¹⁻¹) * (y : G)⁻¹ = (y : G) * ((s : G)⁻¹ * x) * (y : G)⁻¹ *
          ((s : G)⁻¹ * x)⁻¹ by group] at h4
    rw [show (y : G) * x * (y : G)⁻¹ = ((y : G) * s * (y : G)⁻¹) *
      (((y : G) * ((s : G)⁻¹ * x) * (y : G)⁻¹ * ((s : G)⁻¹ * x)⁻¹) * ((s : G)⁻¹ * x)) by group]
    exact mul_mem h1 (mul_mem h2 hc'R)
  refine (hmemP _).mpr ⟨hxR', ?_⟩
  have e : ΦR ⟨(y : G) * x * (y : G)⁻¹, hxR'⟩ =
      Φ ⟨y, hyN⟩ * ΦR ⟨x, hxR⟩ * (Φ ⟨y, hyN⟩)⁻¹ := by
    rw [hΦR, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e, hΦy, ← hwx, mulAut_mul_conj, MulAut.conj_apply]
  exact ⟨_, (Subgroup.mem_normalizer_iff.mp hcW w).mp hw, rfl⟩

end CFSG.Quasithin.H13.L32A
