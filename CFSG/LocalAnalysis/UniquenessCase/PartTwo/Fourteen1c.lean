module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf_of_le_normalizer {A C : Subgroup G}
    (hC : C ≤ normalizer (A : Set G)) :
    Nat.card (C ⊔ A : Subgroup G) * Nat.card (A ⊓ C : Subgroup G) =
      Nat.card A * Nat.card C := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hC
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hC
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C A hC
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (C ⊔ A))
  have h3 : Nat.card (A.subgroupOf (C ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h5 := Nat.card_congr e.toEquiv
  rw [h2, h3, ← h5, ← h4, mul_comm (Nat.card _) (Nat.card A), mul_assoc, ← h1]

theorem commutator_mem_pCoreOf_of_ne {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : L ≠ K) {l k : G} (hl : l ∈ L) (hk : k ∈ K) :
    ⁅l, k⁆ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ M := hL.1.le
  have hKM : K ≤ M := hK.1.le
  let Q : Subgroup ↥M := CFSG.pCore 2 ↥M
  let π : ↥M →* Bar2 M := QuotientGroup.mk' Q
  haveI hQn : Q.Normal := CFSG.pCore_normal
  let l' : ↥M := ⟨l, hLM hl⟩
  let k' : ↥M := ⟨k, hKM hk⟩
  have hlbar : π l' ∈ barImage M L := by
    rw [barImage]
    exact Subgroup.mem_map_of_mem π (by simpa [l', Subgroup.mem_subgroupOf] using hl)
  have hkbar : π k' ∈ barImage M K := by
    rw [barImage]
    exact Subgroup.mem_map_of_mem π (by simpa [k', Subgroup.mem_subgroupOf] using hk)
  have hcomm : π l' * π k' = π k' * π l' :=
    uc22p22l_barImage_commute hL hK hne _ hlbar _ hkbar
  have hker : ⁅l', k'⁆ ∈ Q := by
    rw [← QuotientGroup.eq_one_iff]
    show π ⁅l', k'⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hmem : ((⁅l', k'⁆ : ↥M) : G) ∈ pCoreOf 2 M := by
    rw [pCoreOf]
    exact Subgroup.mem_map.mpr ⟨⁅l', k'⁆, hker, rfl⟩
  have hval : ((⁅l', k'⁆ : ↥M) : G) = ⁅l, k⁆ := by
    change M.subtype ⁅l', k'⁆ = ⁅l, k⁆
    rw [map_commutatorElement]
    rfl
  rwa [hval] at hmem

theorem calC_le_normalizer_of_ne {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : L ≠ K) : K ≤ normalizer (L : Set G) := by
  intro k hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ M := hL.1.le
  have hKM : K ≤ M := hK.1.le
  let Q : Subgroup ↥M := CFSG.pCore 2 ↥M
  let π : ↥M →* Bar2 M := QuotientGroup.mk' Q
  haveI hQn : Q.Normal := CFSG.pCore_normal
  let k' : ↥M := ⟨k, hKM hk⟩
  have hcomm : ∀ a ∈ barImage M L, a * π k' = π k' * a := by
    intro a ha
    exact uc22p22l_barImage_commute hL hK hne a ha (π k') (by
      rw [barImage]
      exact Subgroup.mem_map_of_mem π (by simpa [k', Subgroup.mem_subgroupOf] using hk))
  have hcomap : (barImage M L).comap π = L.subgroupOf M ⊔ Q := by
    rw [barImage, Subgroup.comap_map_eq]
    simp [π, Q]
  have hk'norm : k' ∈ normalizer ((L.subgroupOf M ⊔ Q : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxbar : π x ∈ barImage M L := by
        have hx' : x ∈ (barImage M L).comap π := by rwa [hcomap]
        exact hx'
      have hconj : π (k' * x * k'⁻¹) = π x := by
        rw [map_mul, map_mul, map_inv]
        have hc : Commute (π k') (π x) := (hcomm (π x) hxbar).symm
        rw [hc.eq]
        group
      rw [← hcomap]
      show π (k' * x * k'⁻¹) ∈ barImage M L
      rw [hconj]
      exact hxbar
    · intro hx
      have hxbar : π (k' * x * k'⁻¹) ∈ barImage M L := by
        have hx' : k' * x * k'⁻¹ ∈ (barImage M L).comap π := by rwa [hcomap]
        exact hx'
      have hconj : π x = π (k' * x * k'⁻¹) := by
        set y := π (k' * x * k'⁻¹)
        have hcinv : (π k')⁻¹ * y = y * (π k')⁻¹ := by
          calc (π k')⁻¹ * y = (π k')⁻¹ * (y * π k') * (π k')⁻¹ := by group
            _ = (π k')⁻¹ * (π k' * y) * (π k')⁻¹ := by rw [hcomm y hxbar]
            _ = y * (π k')⁻¹ := by group
        calc π x = π (k'⁻¹ * (k' * x * k'⁻¹) * k') := by
              rw [show k'⁻¹ * (k' * x * k'⁻¹) * k' = x by group]
          _ = (π k')⁻¹ * π (k' * x * k'⁻¹) * π k' := by simp only [map_mul, map_inv]
          _ = y := by
              rw [show π (k' * x * k'⁻¹) = y from rfl, hcinv]
              group
      rw [← hcomap]
      show π x ∈ barImage M L
      rw [hconj]
      exact hxbar
  obtain ⟨hAsn, hAperf, -, -⟩ := UC6S846.calC_subgroupOf hL
  have hQp : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hpc : perfectCore (L.subgroupOf M ⊔ Q) = L.subgroupOf M :=
    UC6S846.perfectCore_sup_eq hQp hAsn hAperf
  have hk'perf : k' ∈ normalizer (perfectCore (L.subgroupOf M ⊔ Q) : Set ↥M) :=
    normalizer_le_normalizer_perfectCore _ hk'norm
  rw [hpc] at hk'perf
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hxM : x ∈ M := hLM hx
    have hx' : (⟨x, hxM⟩ : ↥M) ∈ L.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hconj' : k' * ⟨x, hxM⟩ * k'⁻¹ ∈ L.subgroupOf M :=
      (Subgroup.mem_normalizer_iff.1 hk'perf ⟨x, hxM⟩).1 hx'
    simpa [k', Subgroup.mem_subgroupOf] using hconj'
  · intro hx
    have hxM : k * x * k⁻¹ ∈ M := hLM hx
    have hxL : (⟨k * x * k⁻¹, hxM⟩ : ↥M) ∈ L.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxM' : x ∈ M := by
      have hmem : k⁻¹ * (k * x * k⁻¹) * k ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem (hKM hk)) hxM) (hKM hk)
      simpa [mul_assoc] using hmem
    have hx'' : (⟨x, hxM'⟩ : ↥M) ∈ L.subgroupOf M := by
      have hconj' : k' * ⟨x, hxM'⟩ * k'⁻¹ ∈ L.subgroupOf M := by
        have heq : k' * ⟨x, hxM'⟩ * k'⁻¹ = ⟨k * x * k⁻¹, hxM⟩ := by
          ext
          simp [k']
        rw [heq]
        exact hxL
      exact (Subgroup.mem_normalizer_iff.1 hk'perf ⟨x, hxM'⟩).2 hconj'
    simpa [Subgroup.mem_subgroupOf] using hx''

theorem calC_commutator_le_of_ne {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : L ≠ K) : ⁅L, K⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLK := calC_le_normalizer_of_ne hL hK hne
  have hKL := calC_le_normalizer_of_ne hK hL hne.symm
  have hLM : L ≤ M := hL.1.le
  have hKM : K ≤ M := hK.1.le
  rw [Subgroup.commutator_le]
  intro l hl k hk
  have hpn : ⁅l, k⁆ ∈ pCoreOf 2 M := commutator_mem_pCoreOf_of_ne hL hK hne hl hk
  have hLmem : ⁅l, k⁆ ∈ L := by
    have hconj : k * l⁻¹ * k⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hLK hk) l⁻¹).1 (L.inv_mem hl)
    have := L.mul_mem hl hconj
    simpa [commutatorElement_def, mul_assoc] using this
  have hKmem : ⁅l, k⁆ ∈ K := by
    have hconj : l * k * l⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hKL hl) k).1 hk
    have := K.mul_mem hconj (K.inv_mem hk)
    simpa [commutatorElement_def, mul_assoc] using this
  have hNL : ⁅l, k⁆ ∈ L ⊓ pCoreOf 2 M := ⟨hLmem, hpn⟩
  have hNK : ⁅l, k⁆ ∈ K ⊓ pCoreOf 2 M := ⟨hKmem, hpn⟩
  constructor
  · have hle : L ⊓ pCoreOf 2 M ≤ pCoreOf 2 L := by
      apply CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      · intro x hx
        have hxL := hx
        exact Subgroup.inf_normalizer_le_normalizer_inf (H := L) (K := pCoreOf 2 M)
          ⟨Subgroup.le_normalizer hxL,
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M) (hLM hxL)⟩
      · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right
    exact hle hNL
  · have hle : K ⊓ pCoreOf 2 M ≤ pCoreOf 2 K := by
      apply CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      · intro x hx
        have hxK := hx
        exact Subgroup.inf_normalizer_le_normalizer_inf (H := K) (K := pCoreOf 2 M)
          ⟨Subgroup.le_normalizer hxK,
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M) (hKM hxK)⟩
      · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right
    exact hle hNK

theorem calC_inf_le_pCore_of_ne {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : L ≠ K) (hLc : Subgroup.center (Bar2 L) = ⊥) (hKc : Subgroup.center (Bar2 K) = ⊥) :
    L ⊓ K ≤ pCoreOf 2 L ⊓ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKLcomm := calC_commutator_le_of_ne hK hL hne.symm
  have hLKcomm := calC_commutator_le_of_ne hL hK hne
  intro z hz
  obtain ⟨hzL, hzK⟩ := hz
  have hzLmem : z ∈ pCoreOf 2 L := by
    let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
    haveI hQn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
    have hcenter : π ⟨z, hzL⟩ ∈ Subgroup.center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H l =>
        have hmem : ⁅(l : G), z⁆ ∈ pCoreOf 2 L :=
          (hLKcomm (Subgroup.commutator_mem_commutator l.2 hzK)).1
        rw [pCoreOf] at hmem
        obtain ⟨w, hw, hwval⟩ := Subgroup.mem_map.mp hmem
        have hw' : w = ⁅l, ⟨z, hzL⟩⁆ := by
          apply Subtype.ext
          change L.subtype w = L.subtype ⁅l, ⟨z, hzL⟩⁆
          rw [hwval, map_commutatorElement]
          rfl
        have hmem' : ⁅l, ⟨z, hzL⟩⁆ ∈ CFSG.pCore 2 ↥L := by rwa [hw'] at hw
        change π l * π ⟨z, hzL⟩ = π ⟨z, hzL⟩ * π l
        rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr hmem'
    rw [hLc] at hcenter
    have hq : π ⟨z, hzL⟩ = 1 := Subgroup.mem_bot.mp hcenter
    have hz' : (⟨z, hzL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff (⟨z, hzL⟩ : ↥L)).1 hq
    rw [pCoreOf]
    exact Subgroup.mem_map.mpr ⟨⟨z, hzL⟩, hz', rfl⟩
  have hzKmem : z ∈ pCoreOf 2 K := by
    let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
    haveI hQn : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
    have hcenter : π ⟨z, hzK⟩ ∈ Subgroup.center (Bar2 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        have hmem : ⁅(k : G), z⁆ ∈ pCoreOf 2 K :=
          (hKLcomm (Subgroup.commutator_mem_commutator k.2 hzL)).1
        rw [pCoreOf] at hmem
        obtain ⟨w, hw, hwval⟩ := Subgroup.mem_map.mp hmem
        have hw' : w = ⁅k, ⟨z, hzK⟩⁆ := by
          apply Subtype.ext
          change K.subtype w = K.subtype ⁅k, ⟨z, hzK⟩⁆
          rw [hwval, map_commutatorElement]
          rfl
        have hmem' : ⁅k, ⟨z, hzK⟩⁆ ∈ CFSG.pCore 2 ↥K := by rwa [hw'] at hw
        change π k * π ⟨z, hzK⟩ = π ⟨z, hzK⟩ * π k
        rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr hmem'
    rw [hKc] at hcenter
    have hq : π ⟨z, hzK⟩ = 1 := Subgroup.mem_bot.mp hcenter
    have hz' : (⟨z, hzK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
      (QuotientGroup.eq_one_iff (⟨z, hzK⟩ : ↥K)).1 hq
    rw [pCoreOf]
    exact Subgroup.mem_map.mpr ⟨⟨z, hzK⟩, hz', rfl⟩
  exact ⟨hzLmem, hzKmem⟩

theorem calC_card_sup_mul_card_inf {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : L ≠ K) :
    Nat.card (L ⊔ K : Subgroup G) * Nat.card (L ⊓ K : Subgroup G) = Nat.card L * Nat.card K := by
  rw [sup_comm]
  exact card_sup_mul_card_inf_of_le_normalizer (calC_le_normalizer_of_ne hL hK hne)

theorem isL3_bar2_map_conj {L : Subgroup G} (f : MulAut G) (h : IsL3 (Bar2 L) 1) :
    IsL3 (Bar2 (L.map f.toMonoidHom)) 1 := by
  unfold IsL3 at h ⊢
  let e : ↥L ≃* ↥(L.map f.toMonoidHom) :=
    Subgroup.equivMapOfInjective L f.toMonoidHom f.injective
  exact CFSG.Blueprint.LieModel.of_mulEquiv (UC6S846.bar2Equiv e) h

theorem Hyp141.symm {D : Data G} {L₁ L₂ X : Subgroup G} (h : Hyp141 D L₁ L₂ X) :
    Hyp141 D L₂ L₁ X :=
  ⟨h.sig, h.rank, h.mem₂, h.mem₁, h.ne.symm, h.shape₂, h.shape₁, by rw [sup_comm]; exact h.sylow,
    h.permutes⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
