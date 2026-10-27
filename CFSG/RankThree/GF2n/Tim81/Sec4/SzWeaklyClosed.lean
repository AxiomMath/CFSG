module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedCentre
public import CFSG.Quasithin.Vol2.Ch8Sec2L828E34Suz
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedLemma11

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec4

open CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI.SuzukiModel
open CFSG.CGT.Timmesfeld75
open CFSG.RankThree.GF2n.Tim81.Sec2
open scoped LinearAlgebra.Projectivization Pointwise

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]

private theorem suzukiT_le_normalizer_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiT a K ≤ Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) := by
  intro d hd
  obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hd
  rw [mem_normalizer_iff_conjSubgroup_eq]
  have hle : conjSubgroup (suzukiDElt a K l) (suzukiZ0 a K) ≤ suzukiZ0 a K := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
    change suzukiDElt a K l * suzukiSElt a K 0 v * (suzukiDElt a K l)⁻¹ ∈ suzukiZ0 a K
    rw [suzukiDElt_conj' hK]
    exact (mem_suzukiZ0_iff hK).mpr ⟨((↑l : K) ^ (2 ^ (a + 1) + 1))⁻¹ * v, by simp⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup, card_suzukiZ0 hK])

private theorem suzukiDElt_fixed_eq_one (hK : Nat.card K = 2 ^ (2 * a + 1))
    {l : Kˣ} {v : K} (hv : v ≠ 0)
    (h : suzukiDElt a K l * suzukiSElt a K 0 v * (suzukiDElt a K l)⁻¹ =
      suzukiSElt a K 0 v) : l = 1 := by
  rw [suzukiDElt_conj' hK] at h
  have h2 := (suzukiSElt_inj.1 h).2
  have hpow : ((l⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) = 1 := by
    exact mul_right_cancel₀ hv (by simpa using h2)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -, -⟩ := suzuki_frobenius_exponents a K hK
  have hunit : (l⁻¹) ^ (2 ^ (a + 1) + 1 : ℕ) = 1 := by
    apply Units.ext
    simpa using hpow
  have h1 : l⁻¹ = 1 := by
    refine hbij.1 ?_
    show (l⁻¹) ^ (2 ^ (a + 1) + 1) = (1 : Kˣ) ^ (2 ^ (a + 1) + 1)
    exact hunit.trans (one_pow (2 ^ (a + 1) + 1)).symm
  exact inv_eq_one.mp h1

private theorem conjSubgroup_eq_self_of_mem_normalizer
    {T₀ P Z : Subgroup ↥(suzukiGroup a K)}
    (hsq : ∀ t ∈ T₀, t * t = 1)
    (hwc : ∀ g : ↥(suzukiGroup a K), conjSubgroup g T₀ ≤
      Subgroup.normalizer (T₀ : Set ↥(suzukiGroup a K)) → conjSubgroup g T₀ = T₀)
    (hTP : T₀ ≤ P) (hZinv : ∀ x ∈ P, x * x = 1 → x ∈ Z)
    (hZN : Z ≤ Subgroup.normalizer (T₀ : Set ↥(suzukiGroup a K))) :
    ∀ g ∈ Subgroup.normalizer (P : Set ↥(suzukiGroup a K)),
      conjSubgroup g T₀ = T₀ := by
  intro g hg
  apply hwc g
  have hTgP : conjSubgroup g T₀ ≤ P := by
    have h1 : conjSubgroup g T₀ ≤ conjSubgroup g P :=
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hTP
    have h2 : conjSubgroup g P = (P : Subgroup ↥(suzukiGroup a K)) :=
      mem_normalizer_iff_conjSubgroup_eq.1 hg
    exact h2 ▸ h1
  have hTgZ : conjSubgroup g T₀ ≤ Z := by
    intro x hx
    have hxP := hTgP hx
    have hx2 : x * x = 1 := by
      have h1 : g⁻¹ * x * g ∈ T₀ := mem_conjSubgroup.1 hx
      have h2 : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := hsq _ h1
      have h2' : g⁻¹ * (x * x) * g = 1 := by
        calc g⁻¹ * (x * x) * g = (g⁻¹ * x * g) * (g⁻¹ * x * g) := by group
          _ = 1 := h2
      calc x * x = g * (g⁻¹ * (x * x) * g) * g⁻¹ := by group
        _ = 1 := by rw [h2']; group
    exact hZinv x hxP (by simpa [pow_two] using hx2)
  exact hTgZ.trans hZN

private theorem le_of_forall_conj_eq_self
    {T₀ P Z : Subgroup ↥(suzukiGroup a K)}
    (hT1 : T₀ ≠ ⊥) (hTZ : T₀ ≤ Z)
    (hZtrans : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ 1 → z' ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (P : Set ↥(suzukiGroup a K)), g * z * g⁻¹ = z')
    (hNT : ∀ g ∈ Subgroup.normalizer (P : Set ↥(suzukiGroup a K)),
      conjSubgroup g T₀ = T₀) :
    Z ≤ T₀ := by
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]; exact T₀.one_mem
  · obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT1
    have htT : (t : suzukiGroup a K) ∈ T₀ := t.2
    have htZ : (t : suzukiGroup a K) ∈ Z := hTZ htT
    have ht1' : (t : suzukiGroup a K) ≠ 1 := fun h => ht1 (Subtype.ext h)
    obtain ⟨g, hgN, hgz⟩ := hZtrans (t : suzukiGroup a K) htZ z hz ht1' hz1
    have hmem : g * (t : suzukiGroup a K) * g⁻¹ ∈ T₀ := by
      have h1 : g * (t : suzukiGroup a K) * g⁻¹ ∈ conjSubgroup g T₀ :=
        conj_mem_conjSubgroup g htT
      rwa [hNT g hgN] at h1
    rw [← hgz]
    exact hmem

private theorem exists_conj_eq_suzukiZ0_aux {T₀ : Subgroup ↥(suzukiGroup a K)}
    (hT : IsPGroup 2 T₀) (hT1 : T₀ ≠ ⊥)
    (hsq : ∀ t ∈ T₀, t * t = 1)
    (hwc : ∀ g : ↥(suzukiGroup a K), conjSubgroup g T₀ ≤
      Subgroup.normalizer (T₀ : Set ↥(suzukiGroup a K)) → conjSubgroup g T₀ = T₀)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ (c : ↥(suzukiGroup a K)) (P : Sylow 2 ↥(suzukiGroup a K)),
      (P : Subgroup ↥(suzukiGroup a K)) = conjSubgroup c (suzukiU a K) ∧
      T₀ = conjSubgroup c (suzukiZ0 a K) ∧ Nat.card T₀ = 2 ^ (2 * a + 1) := by
  classical
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  obtain ⟨c, hPc⟩ := CFSG.Quasithin.H13.sylow_map_conj_e34 hK (MulEquiv.refl ↥(suzukiGroup a K)) P
  have hPc' : (P : Subgroup ↥(suzukiGroup a K)) = conjSubgroup c (suzukiU a K) := by
    simpa [conjSubgroup] using hPc
  obtain ⟨⟨Z, hZP, hZcard, hZsq, hZinv, hZtrans⟩, hTI, C, hCN, hCcyc, hCdec⟩ :=
    CFSG.Quasithin.H13.good_sylow_e34 hK (MulEquiv.refl ↥(suzukiGroup a K)) P
  have hTZ : T₀ ≤ Z := fun t ht =>
    hZinv t (hTP ht) (by simpa [pow_two] using hsq t ht)
  have hZ_Uc : Z ≤ conjSubgroup c (suzukiU a K) := hPc' ▸ hZP
  have hZ_Z0c : Z ≤ conjSubgroup c (suzukiZ0 a K) := by
    intro z hz
    have hzc : c⁻¹ * z * c ∈ suzukiU a K := mem_conjSubgroup.1 (hZ_Uc hz)
    have huz : (c⁻¹ * z * c) ^ 2 = 1 := by
      have hz2 : z ^ 2 = 1 := hZsq z hz
      have := congrArg (fun w : ↥(suzukiGroup a K) => c⁻¹ * w * c) hz2
      simpa [pow_two, mul_assoc] using this
    have huZ0 : c⁻¹ * z * c ∈ suzukiZ0 a K :=
      CFSG.Quasithin.H13.suzukiU_involution_e34 hK _ hzc huz
    have h1 : c * (c⁻¹ * z * c) * c⁻¹ ∈ conjSubgroup c (suzukiZ0 a K) :=
      conj_mem_conjSubgroup c huZ0
    simpa [mul_assoc] using h1
  have hZeq : Z = conjSubgroup c (suzukiZ0 a K) := by
    refine Subgroup.eq_of_le_of_card_ge hZ_Z0c ?_
    rw [card_conjSubgroup, card_suzukiZ0 hK, hZcard]
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := by
    intro x hx y hy
    have hx0 : c⁻¹ * x * c ∈ suzukiZ0 a K := mem_conjSubgroup.1 (hZ_Z0c hx)
    have hy0 : c⁻¹ * y * c ∈ suzukiZ0 a K := mem_conjSubgroup.1 (hZ_Z0c hy)
    have hcomm0 : (c⁻¹ * x * c) * (c⁻¹ * y * c) = (c⁻¹ * y * c) * (c⁻¹ * x * c) :=
      CFSG.Open.IsElemAbelian.comm (isElemAbelian_suzukiZ0 hK) hx0 hy0
    have := congrArg (fun w : ↥(suzukiGroup a K) => c * w * c⁻¹) hcomm0
    simpa [mul_assoc] using this
  have hZcent : Z ≤ Subgroup.centralizer (T₀ : Set ↥(suzukiGroup a K)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (hZcomm z hz t (hTZ ht)).symm
  have hZN : Z ≤ Subgroup.normalizer (T₀ : Set ↥(suzukiGroup a K)) :=
    hZcent.trans (Subgroup.centralizer_le_normalizer (G := ↥(suzukiGroup a K)) (T₀ : Set _))
  have hNT := conjSubgroup_eq_self_of_mem_normalizer (Z := Z) hsq hwc hTP
    (fun x hx hx2 => hZinv x hx (by simpa [pow_two] using hx2)) hZN
  have hZT := le_of_forall_conj_eq_self hT1 hTZ hZtrans hNT
  have hTZeq : T₀ = Z := le_antisymm hTZ hZT
  refine ⟨c, P, hPc', hTZeq.trans hZeq, ?_⟩
  rw [hTZeq, hZcard]

theorem exists_conj_eq_szZ (hK : Nat.card K = 2 ^ (2 * a + 1))
    {T₀ : Subgroup ↥(suzukiGroup a K)} (hT : IsPGroup 2 T₀) (hT1 : T₀ ≠ ⊥)
    (hsq : ∀ t ∈ T₀, t * t = 1)
    (hwc : ∀ g : ↥(suzukiGroup a K), conjSubgroup g T₀ ≤
      Subgroup.normalizer (T₀ : Set ↥(suzukiGroup a K)) → conjSubgroup g T₀ = T₀) :
    ∃ x : ↥(suzukiGroup a K), T₀ = conjSubgroup x (szZ a K) ∧
      Nat.card T₀ = 2 ^ (2 * a + 1) := by
  obtain ⟨c, P, hP, hT₀, hcard⟩ := exists_conj_eq_suzukiZ0_aux hT hT1 hsq hwc hK
  refine ⟨c * (suzukiWElt a K)⁻¹, ?_, hcard⟩
  have hszZ : szZ a K = conjSubgroup (suzukiWElt a K) (suzukiZ0 a K) := rfl
  calc T₀ = conjSubgroup c (suzukiZ0 a K) := hT₀
    _ = conjSubgroup (c * (suzukiWElt a K)⁻¹)
          (conjSubgroup (suzukiWElt a K) (suzukiZ0 a K)) := by
        rw [conjSubgroup_conjSubgroup]
        congr 1
        group
    _ = conjSubgroup (c * (suzukiWElt a K)⁻¹) (szZ a K) := by rw [hszZ]

private theorem frobeniusComplement_conj (hK : Nat.card K = 2 ^ (2 * a + 1))
    {T₀ : Subgroup ↥(suzukiGroup a K)} {c : ↥(suzukiGroup a K)}
    (hT₀ : T₀ = conjSubgroup c (suzukiZ0 a K))
    (hcardT : Nat.card T₀ = 2 ^ (2 * a + 1)) :
    conjSubgroup c (suzukiT a K) ≤
        Subgroup.normalizer (T₀ : Set ↥(suzukiGroup a K)) ∧
      Nat.card (conjSubgroup c (suzukiT a K)) = Nat.card T₀ - 1 ∧
      (∀ x ∈ conjSubgroup c (suzukiT a K), ∀ y ∈ conjSubgroup c (suzukiT a K),
        x * y = y * x) ∧
      (∀ d ∈ conjSubgroup c (suzukiT a K), d ≠ 1 → ∀ x ∈ T₀,
        d * x * d⁻¹ = x → x = 1) := by
  have hTcomm : ∀ x ∈ suzukiT a K, ∀ y ∈ suzukiT a K, x * y = y * x :=
    (suzuki_borel_structure hK).2.1
  have hTcard : Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 :=
    (suzuki_borel_structure hK).2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    have htT : c⁻¹ * d * c ∈ suzukiT a K := mem_conjSubgroup.1 hd
    have htN : c⁻¹ * d * c ∈
        Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) :=
      suzukiT_le_normalizer_suzukiZ0 hK htT
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom htN
    rw [Subgroup.map_equiv_normalizer_eq] at h1
    rw [hT₀]
    simpa [conjSubgroup, MulAut.conj_apply, mul_assoc] using h1
  · rw [card_conjSubgroup, hTcard, hcardT]
  · intro x hx y hy
    have hxT : c⁻¹ * x * c ∈ suzukiT a K := mem_conjSubgroup.1 hx
    have hyT : c⁻¹ * y * c ∈ suzukiT a K := mem_conjSubgroup.1 hy
    have hcomm : (c⁻¹ * x * c) * (c⁻¹ * y * c) = (c⁻¹ * y * c) * (c⁻¹ * x * c) :=
      hTcomm _ hxT _ hyT
    have := congrArg (fun w : ↥(suzukiGroup a K) => c * w * c⁻¹) hcomm
    simpa [mul_assoc] using this
  · intro d hd hd1 y hy hfix
    have htT : c⁻¹ * d * c ∈ suzukiT a K := mem_conjSubgroup.1 hd
    have hzZ0 : c⁻¹ * y * c ∈ suzukiZ0 a K := by
      rw [hT₀] at hy
      exact mem_conjSubgroup.1 hy
    have hfix' : (c⁻¹ * d * c) * (c⁻¹ * y * c) * (c⁻¹ * d * c)⁻¹ = c⁻¹ * y * c := by
      have := congrArg (fun w : ↥(suzukiGroup a K) => c⁻¹ * w * c) hfix
      simpa [mul_assoc] using this
    by_cases hz1 : c⁻¹ * y * c = 1
    · have := congrArg (fun w : ↥(suzukiGroup a K) => c * w * c⁻¹) hz1
      simpa [mul_assoc] using this
    · exfalso
      obtain ⟨l, hl⟩ := mem_suzukiT_iff.1 htT
      obtain ⟨v, hv0⟩ := (mem_suzukiZ0_iff hK).1 hzZ0
      rw [← hl, ← hv0] at hfix'
      have hv : v ≠ 0 := by
        rintro rfl
        apply hz1
        rw [← hv0, suzukiSElt_zero_zero hK]
      have hl1 : l = 1 := suzukiDElt_fixed_eq_one hK hv hfix'
      apply hd1
      have hzc : c⁻¹ * d * c = 1 := by rw [← hl, hl1, suzukiDElt_one]
      calc d = c * (c⁻¹ * d * c) * c⁻¹ := by group
        _ = 1 := by rw [hzc]; group

theorem exists_frobeniusComplement_sz (hK : Nat.card K = 2 ^ (2 * a + 1))
    {T₀ : Subgroup ↥(suzukiGroup a K)} (hT : IsPGroup 2 T₀) (hT1 : T₀ ≠ ⊥)
    (hsq : ∀ t ∈ T₀, t * t = 1)
    (hwc : ∀ g : ↥(suzukiGroup a K), conjSubgroup g T₀ ≤
      Subgroup.normalizer (T₀ : Set ↥(suzukiGroup a K)) → conjSubgroup g T₀ = T₀) :
    ∃ D : Subgroup ↥(suzukiGroup a K),
      D ≤ Subgroup.normalizer (T₀ : Set ↥(suzukiGroup a K)) ∧
      Nat.card D = Nat.card T₀ - 1 ∧
      (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) ∧
      (∀ d ∈ D, d ≠ 1 → ∀ x ∈ T₀, d * x * d⁻¹ = x → x = 1) := by
  obtain ⟨c, P, hP, hT₀, hcard⟩ := exists_conj_eq_suzukiZ0_aux hT hT1 hsq hwc hK
  exact ⟨conjSubgroup c (suzukiT a K), frobeniusComplement_conj hK hT₀ hcard⟩

private theorem suzukiB_le_normalizer_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiB a K ≤ Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) := by
  have hUcent : suzukiU a K ≤
      Subgroup.centralizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact suzukiZ0_comm_suzukiU hK hz hu
  exact sup_le (hUcent.trans (Subgroup.centralizer_le_normalizer
    (G := ↥(suzukiGroup a K)) (suzukiZ0 a K : Set _)))
    (suzukiT_le_normalizer_suzukiZ0 hK)

theorem conj_smul_eq_conjSubgroup {G : Type*} [Group G] (g : G) (S : Subgroup G) :
    MulAut.conj g • S = conjSubgroup g S := by
  ext y
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  rfl

private theorem suzukiU_smul_suzukiInfty (hK : Nat.card K = 2 ^ (2 * a + 1))
    {u : ↥(suzukiGroup a K)} (hu : u ∈ suzukiU a K) :
    u • suzukiInfty K = suzukiInfty K := by
  have h := suzukiB_le_stabilizer hK (suzukiU_le_suzukiB a K hu)
  rwa [MulAction.mem_stabilizer_iff] at h

private theorem le_suzukiU_of_le_suzukiB (hK : Nat.card K = 2 ^ (2 * a + 1))
    {Q : Subgroup ↥(suzukiGroup a K)} (hQ : IsPGroup 2 Q) (hQB : Q ≤ suzukiB a K) :
    Q ≤ suzukiU a K := by
  have hUB : suzukiU a K ≤ suzukiB a K := suzukiU_le_suzukiB a K
  have hBN : suzukiB a K ≤ Subgroup.normalizer (suzukiU a K : Set ↥(suzukiGroup a K)) := by
    rw [suzukiB]
    exact sup_le Subgroup.le_normalizer (suzukiT_le_normalizer hK)
  let UB := (suzukiU a K).subgroupOf (suzukiB a K)
  have hUBn : UB.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mpr hBN
  have hcardq : Nat.card (↥(suzukiB a K) ⧸ UB) = 2 ^ (2 * a + 1) - 1 := by
    have hBcard : Nat.card (suzukiB a K) =
        (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) :=
      (suzuki_borel_structure hK).2.2.2.2.2.2.2
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup UB
    rw [hBcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUB).toEquiv,
      (suzuki_unipotent_structure hK).2.1, mul_comm] at h
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm
  have hodd : Odd (Nat.card (↥(suzukiB a K) ⧸ UB)) := by
    rw [hcardq]
    exact odd_two_pow_sub_one (2 * a + 1) (by omega)
  set QB := Q.subgroupOf (suzukiB a K)
  have hQB2 : IsPGroup 2 (QB.map (QuotientGroup.mk' UB)) :=
    (hQ.comap_of_injective _ (suzukiB a K).subtype_injective).map _
  have hbot : QB.map (QuotientGroup.mk' UB) = ⊥ := by
    rw [← Subgroup.card_eq_one]
    rcases hQB2.card_eq_or_dvd with h | h
    · exact h
    · exfalso
      have := h.trans (Subgroup.card_subgroup_dvd_card _)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  intro x hx
  have hxB : x ∈ suzukiB a K := hQB hx
  have h1 : QuotientGroup.mk' UB (⟨x, hxB⟩ : suzukiB a K) ∈ QB.map (QuotientGroup.mk' UB) :=
    ⟨⟨x, hxB⟩, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

private theorem conj_le_stabilizer {G X : Type*} [Group G] [MulAction G X]
    {S : Subgroup G} {x y : X} {t : G} (hS : S ≤ MulAction.stabilizer G x)
    (htx : t • x = y) : conjSubgroup t S ≤ MulAction.stabilizer G y := by
  rintro q ⟨s, hs, rfl⟩
  rw [MulAction.mem_stabilizer_iff]
  have hsfix : s • x = x := by
    have := hS hs
    rwa [MulAction.mem_stabilizer_iff] at this
  have htinv : t⁻¹ • y = x := by rw [← htx]; simp
  calc (t * s * t⁻¹) • y = t • (s • (t⁻¹ • y)) := by rw [mul_smul, mul_smul]
    _ = t • (s • x) := by rw [htinv]
    _ = t • x := by rw [hsfix]
    _ = y := htx

private theorem smul_infty_ne (hK : Nat.card K = 2 ^ (2 * a + 1))
    {c c' : ↥(suzukiGroup a K)} {T₀ T₀' : Subgroup ↥(suzukiGroup a K)}
    (hT₀ : T₀ = conjSubgroup c (suzukiZ0 a K))
    (hT₀' : T₀' = conjSubgroup c' (suzukiZ0 a K)) (hne : T₀ ≠ T₀') :
    c • suzukiInfty K ≠ c' • suzukiInfty K := by
  intro hxy
  apply hne
  have hg0B : c'⁻¹ * c ∈ suzukiB a K := by
    have hg0 : c'⁻¹ * c ∈ MulAction.stabilizer (↥(suzukiGroup a K)) (suzukiInfty K) := by
      rw [MulAction.mem_stabilizer_iff]
      calc (c'⁻¹ * c) • suzukiInfty K = c'⁻¹ • (c • suzukiInfty K) := mul_smul _ _ _
        _ = c'⁻¹ • (c' • suzukiInfty K) := by rw [hxy]
        _ = suzukiInfty K := inv_smul_smul c' _
    rwa [(suzuki_ovoid_stabilizer hK).1] at hg0
  have hZeq : conjSubgroup c (suzukiZ0 a K) = conjSubgroup c' (suzukiZ0 a K) := by
    rw [conjSubgroup_eq_conjSubgroup_iff]
    exact suzukiB_le_normalizer_suzukiZ0 hK (by
      simpa [mul_inv_rev] using (suzukiB a K).inv_mem hg0B)
  rw [hT₀, hT₀', hZeq]

private theorem exists_involution_swap (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : ℙ K (Fin 4 → K)}
    (hxΩ : x ∈ suzukiOmega a K) (hyΩ : y ∈ suzukiOmega a K) (hxy : x ≠ y) :
    ∃ t : ↥(suzukiGroup a K), t * t = 1 ∧ t ≠ 1 ∧ t • x = y ∧ t • y = x := by
  obtain ⟨-, h2tr, -, -, -⟩ := suzuki_ovoid_double_transitivity hK
  obtain ⟨g, hgx, hgy⟩ := h2tr
    (suzukiInfty K) (suzukiInfty_mem_suzukiOmega a K)
    (suzukiLine a K 0 0) (suzukiLine_mem_suzukiOmega a K 0 0)
    x hxΩ y hyΩ (suzukiLine_ne_suzukiInfty (a := a) 0 0).symm hxy
  let t : ↥(suzukiGroup a K) := g * suzukiWElt a K * g⁻¹
  have htt : t * t = 1 := by
    change g * suzukiWElt a K * g⁻¹ * (g * suzukiWElt a K * g⁻¹) = 1
    calc g * suzukiWElt a K * g⁻¹ * (g * suzukiWElt a K * g⁻¹) =
        g * (suzukiWElt a K * suzukiWElt a K) * g⁻¹ := by group
      _ = 1 := by rw [suzukiWElt_mul_self]; group
  have ht1 : t ≠ 1 := by
    intro ht
    apply suzukiWElt_ne_one (a := a) (K := K)
    have := congrArg (fun z : ↥(suzukiGroup a K) => g⁻¹ * z * g) ht
    simpa [t, mul_assoc] using this
  have htx : t • x = y := by
    change (g * suzukiWElt a K * g⁻¹) • x = y
    rw [← hgx, ← hgy]
    calc (g * suzukiWElt a K * g⁻¹) • (g • suzukiInfty K)
        = g • (suzukiWElt a K • (g⁻¹ • (g • suzukiInfty K))) := by rw [mul_smul, mul_smul]
      _ = g • (suzukiWElt a K • suzukiInfty K) := by rw [inv_smul_smul]
      _ = g • suzukiLine a K 0 0 := by rw [suzukiWElt_smul_suzukiInfty hK]
  have hty : t • y = x := by
    change (g * suzukiWElt a K * g⁻¹) • y = x
    rw [← hgy, ← hgx]
    calc (g * suzukiWElt a K * g⁻¹) • (g • suzukiLine a K 0 0)
        = g • (suzukiWElt a K • (g⁻¹ • (g • suzukiLine a K 0 0))) := by rw [mul_smul, mul_smul]
      _ = g • (suzukiWElt a K • suzukiLine a K 0 0) := by rw [inv_smul_smul]
      _ = g • suzukiInfty K := by rw [suzukiWElt_smul_suzukiLine_zero hK]
  exact ⟨t, htt, ht1, htx, hty⟩

private theorem conjSubgroup_eq_suzukiU_of_transport (hK : Nat.card K = 2 ^ (2 * a + 1))
    {c c' : ↥(suzukiGroup a K)} {P : Sylow 2 ↥(suzukiGroup a K)}
    (hP : (P : Subgroup ↥(suzukiGroup a K)) = conjSubgroup c (suzukiU a K))
    {x y : ℙ K (Fin 4 → K)} (hx : x = c • suzukiInfty K)
    (hy : y = c' • suzukiInfty K) {t : ↥(suzukiGroup a K)} (htx : t • x = y) :
    conjSubgroup c'⁻¹ (conjSubgroup t (P : Subgroup ↥(suzukiGroup a K))) = suzukiU a K := by
  let Q : Subgroup ↥(suzukiGroup a K) :=
    conjSubgroup c'⁻¹ (conjSubgroup t (P : Subgroup ↥(suzukiGroup a K)))
  have hUfix : suzukiU a K ≤
      MulAction.stabilizer (↥(suzukiGroup a K)) (suzukiInfty K) := by
    intro u hu
    rw [MulAction.mem_stabilizer_iff]
    exact suzukiU_smul_suzukiInfty hK hu
  have hPfix : (P : Subgroup ↥(suzukiGroup a K)) ≤
      MulAction.stabilizer (↥(suzukiGroup a K)) x := by
    rw [hP]
    simpa [hx] using conj_le_stabilizer (t := c) (x := suzukiInfty K)
      (y := c • suzukiInfty K) hUfix rfl
  have htPfix : conjSubgroup t (P : Subgroup ↥(suzukiGroup a K)) ≤
      MulAction.stabilizer (↥(suzukiGroup a K)) y :=
    conj_le_stabilizer hPfix htx
  have hQfix : Q ≤ MulAction.stabilizer (↥(suzukiGroup a K)) (suzukiInfty K) := by
    have hy' : c'⁻¹ • y = suzukiInfty K := by
      rw [hy]
      exact inv_smul_smul c' _
    have h := conj_le_stabilizer (t := c'⁻¹) (x := y) (y := suzukiInfty K) htPfix hy'
    simpa [Q, hy'] using h
  have hQB : Q ≤ suzukiB a K := by
    intro q hq
    have h := hQfix hq
    rwa [(suzuki_ovoid_stabilizer hK).1] at h
  have hQ2 : IsPGroup 2 Q := by
    dsimp [Q]
    exact ((P.isPGroup').map (MulAut.conj t).toMonoidHom).map (MulAut.conj c'⁻¹).toMonoidHom
  have hQU : Q ≤ suzukiU a K := le_suzukiU_of_le_suzukiB hK hQ2 hQB
  have hQcard : Nat.card Q = Nat.card (suzukiU a K) := by
    dsimp [Q]
    rw [card_conjSubgroup, card_conjSubgroup, hP, card_conjSubgroup,
      (suzuki_unipotent_structure hK).2.1]
  exact Subgroup.eq_of_le_of_card_ge hQU (by rw [hQcard])

private theorem conjZ0_conj_of_transport (hK : Nat.card K = 2 ^ (2 * a + 1))
    {c c' : ↥(suzukiGroup a K)} {P P' : Sylow 2 ↥(suzukiGroup a K)}
    {T₀ T₀' : Subgroup ↥(suzukiGroup a K)}
    (hP : (P : Subgroup ↥(suzukiGroup a K)) = conjSubgroup c (suzukiU a K))
    (hP' : (P' : Subgroup ↥(suzukiGroup a K)) = conjSubgroup c' (suzukiU a K))
    (hT₀ : T₀ = conjSubgroup c (suzukiZ0 a K))
    (hT₀' : T₀' = conjSubgroup c' (suzukiZ0 a K))
    {x y : ℙ K (Fin 4 → K)} (hx : x = c • suzukiInfty K)
    (hy : y = c' • suzukiInfty K) {t : ↥(suzukiGroup a K)}
    (htt : t * t = 1) (htx : t • x = y) :
    conjSubgroup t T₀ = T₀' ∧ conjSubgroup t T₀' = T₀ := by
  have hQeq : conjSubgroup c'⁻¹ (conjSubgroup t (P : Subgroup ↥(suzukiGroup a K))) =
      suzukiU a K := conjSubgroup_eq_suzukiU_of_transport hK hP hx hy htx
  have hPtP : conjSubgroup t (P : Subgroup ↥(suzukiGroup a K)) =
      (P' : Subgroup ↥(suzukiGroup a K)) := by
    have h := congrArg (conjSubgroup c') hQeq
    rw [show conjSubgroup c' (conjSubgroup c'⁻¹
        (conjSubgroup t (P : Subgroup ↥(suzukiGroup a K)))) =
        conjSubgroup t (P : Subgroup ↥(suzukiGroup a K)) by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]] at h
    rw [← hP'] at h
    exact h
  have hPU : conjSubgroup (t * c) (suzukiU a K) = conjSubgroup c' (suzukiU a K) := by
    calc conjSubgroup (t * c) (suzukiU a K)
        = conjSubgroup t (conjSubgroup c (suzukiU a K)) :=
            (conjSubgroup_conjSubgroup t c (suzukiU a K)).symm
      _ = conjSubgroup t (P : Subgroup ↥(suzukiGroup a K)) := by rw [← hP]
      _ = (P' : Subgroup ↥(suzukiGroup a K)) := hPtP
      _ = conjSubgroup c' (suzukiU a K) := hP'
  have hmemN : (t * c)⁻¹ * c' ∈
      Subgroup.normalizer (suzukiU a K : Set ↥(suzukiGroup a K)) :=
    conjSubgroup_eq_conjSubgroup_iff.1 hPU
  have hmemB : (t * c)⁻¹ * c' ∈ suzukiB a K := by
    rwa [CFSG.Quasithin.H13.normalizer_suzukiU_e34 hK] at hmemN
  have hmemZ : (t * c)⁻¹ * c' ∈
      Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) :=
    suzukiB_le_normalizer_suzukiZ0 hK hmemB
  have hTt : conjSubgroup t T₀ = T₀' := by
    rw [hT₀, hT₀']
    calc conjSubgroup t (conjSubgroup c (suzukiZ0 a K))
        = conjSubgroup (t * c) (suzukiZ0 a K) := conjSubgroup_conjSubgroup t c _
      _ = conjSubgroup c' (suzukiZ0 a K) := conjSubgroup_eq_conjSubgroup_iff.2 hmemZ
  have hTt' : conjSubgroup t T₀' = T₀ := by
    rw [← hTt, conjSubgroup_conjSubgroup, htt, conjSubgroup_one]
  exact ⟨hTt, hTt'⟩

theorem exists_involution_conj_eq_of_weaklyClosed_ne_sz (hK : Nat.card K = 2 ^ (2 * a + 1))
    {T₀ T₀' : Subgroup ↥(suzukiGroup a K)}
    (hT : IsPGroup 2 T₀) (hT1 : T₀ ≠ ⊥) (hsq : ∀ t ∈ T₀, t * t = 1)
    (hwc : ∀ g : ↥(suzukiGroup a K), conjSubgroup g T₀ ≤
      Subgroup.normalizer (T₀ : Set ↥(suzukiGroup a K)) → conjSubgroup g T₀ = T₀)
    (hT' : IsPGroup 2 T₀') (hT1' : T₀' ≠ ⊥) (hsq' : ∀ t ∈ T₀', t * t = 1)
    (hwc' : ∀ g : ↥(suzukiGroup a K), conjSubgroup g T₀' ≤
      Subgroup.normalizer (T₀' : Set ↥(suzukiGroup a K)) → conjSubgroup g T₀' = T₀')
    (hne : T₀ ≠ T₀') :
    ∃ t : ↥(suzukiGroup a K), t * t = 1 ∧ t ≠ 1 ∧
      conjSubgroup t T₀ = T₀' ∧ conjSubgroup t T₀' = T₀ := by
  obtain ⟨c, P, hP, hT₀, hcard⟩ := exists_conj_eq_suzukiZ0_aux hT hT1 hsq hwc hK
  obtain ⟨c', P', hP', hT₀', hcard'⟩ := exists_conj_eq_suzukiZ0_aux hT' hT1' hsq' hwc' hK
  let x : ℙ K (Fin 4 → K) := c • suzukiInfty K
  let y : ℙ K (Fin 4 → K) := c' • suzukiInfty K
  have hxΩ : x ∈ suzukiOmega a K :=
    suzuki_smul_mem_suzukiOmega hK c (suzukiInfty_mem_suzukiOmega a K)
  have hyΩ : y ∈ suzukiOmega a K :=
    suzuki_smul_mem_suzukiOmega hK c' (suzukiInfty_mem_suzukiOmega a K)
  have hxy : x ≠ y := smul_infty_ne hK hT₀ hT₀' hne
  obtain ⟨t, htt, ht1, htx, -⟩ := exists_involution_swap hK hxΩ hyΩ hxy
  obtain ⟨hTt, hTt'⟩ := conjZ0_conj_of_transport hK hP hP' hT₀ hT₀' rfl rfl htt htx
  exact ⟨t, htt, ht1, hTt, hTt'⟩

end CFSG.RankThree.GF2n.Tim81.Sec4
