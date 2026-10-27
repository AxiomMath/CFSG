module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourElevenCommon
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenClosing
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenPermThree
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenOuterThree
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenOuterMember
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenFrameSD
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenCentralizerThree
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.GroupTheory.ElementaryAbelianBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.WeakClosure81.FourEleven (PermThreeMember)

variable {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {p : ℕ}

theorem FourElevenSetting.inCalEi_centralizer_three (h : FourElevenSetting Q L p) (hp : p = 3)
    {T A : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A) {z u : Q}
    (hzL : z ∈ L) (hz2 : orderOf z = 2) (hzT : ∀ t ∈ T, t * z = z * t) (huA : u ∈ A)
    (huL : u ∈ L) (hu2 : orderOf u = 2) (huz : u ≠ z) :
    InCalEi 1 T A (centralizer ({z} : Set Q)) := by
  subst hp
  have hLnorm : L.Normal := h.normal
  have hL3 : LieModel ↥L .PSL 3 3 1 := by
    rcases h.isL3 with h1 | h2
    · exact h1
    · exact absurd h2 (h.not_psu33 rfl)
  have hbar := CFSG.LocalAnalysis.WeakClosure81.FourEleven.centralizer_bar2_three
    (Q := Q) hL3 hzL hz2
  set K : Subgroup Q := centralizer ({z} : Set Q) with hK
  set X : Subgroup Q := L ⊓ K with hX
  have hXK : X ≤ K := inf_le_right
  have hTC : T ≤ K := fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (hzT t ht)
  have hXn : K ≤ normalizer (X : Set Q) := by
    rw [hX]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer_inf (H := L) (K := K)).mp
      (hLnorm.subgroupOf K)
  have hidx : X.relIndex K ≤ 2 := by
    rw [hX, hK, Subgroup.inf_relIndex_right]
    have hne0 : L.relIndex (⊤ : Subgroup Q) ≠ 0 := by
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.index_ne_zero_of_finite
    refine (Subgroup.relIndex_le_of_le_right (H := L) (K := K) le_top hne0).trans ?_
    rw [Subgroup.relIndex_top_right]
    exact h.index_le_two
  have hKbar : Nonempty (Bar2 K ≃* Equiv.Perm (Fin 3)) :=
    CFSG.LocalAnalysis.WeakClosure81.FourEleven.bar2_perm_three_of_relIndex_le_two
      inf_le_right hXn hidx hbar.1
  have hτ : UniquenessCase.PartTwo.tA T A ≤ T ⊓ K := by
    rw [CFSG.LocalAnalysis.WeakClosure81.FourEleven.tA_eq_inf_centralizer h.pCoreOf_two_top]
    exact le_inf inf_le_left (inf_le_left.trans hTC)
  have hSyl : IsSylowIn 2 (T ⊓ K) K := by
    have hTK : T ⊓ K = T := inf_eq_left.mpr hTC
    rw [hTK]
    refine ⟨hTC, hT.2.1, ?_⟩
    have h1 : T.relIndex K * K.relIndex (⊤ : Subgroup Q) = T.relIndex ⊤ :=
      Subgroup.relIndex_mul_relIndex T K ⊤ hTC le_top
    intro hdvd
    exact hT.2.2 (h1 ▸ dvd_mul_of_dvd_left hdvd _)
  have hAO : ¬ A ≤ pCoreOf 2 K := by
    intro hle
    have huK : u ∈ pCoreOf 2 K := hle huA
    have huX : u ∈ X := ⟨huL, CFSG.LieType.BorelTits.pCoreOf_le 2 K huK⟩
    have hle' : X ⊓ pCoreOf 2 K ≤ pCoreOf 2 X :=
      CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hXK
    exact huz (hbar.2 u (hle' ⟨huX, huK⟩) hu2)
  exact CFSG.LocalAnalysis.WeakClosure81.inCalEi_of_bar2_mulEquiv_perm_three
    hAT hA le_rfl hτ hSyl hKbar hAO

theorem FourElevenSetting.exists_involution_not_mem_of_unique [L.Normal] (hidx : L.index ≤ 2)
    {A : Subgroup Q} (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) {z : Q} (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hzInv : ∀ u ∈ A ⊓ L, orderOf u = 2 → u = z) :
    A ⊓ L = Subgroup.zpowers z ∧ Nat.card A = 4 ∧ ∃ b ∈ A, b ∉ L ∧ orderOf b = 2 := by
  have hAne : A ⊓ L ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(A ⊓ L) = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h2 := CFSG.LocalAnalysis.WeakClosure81.FourEleven.card_le_two_mul_card_inf hidx A
    rw [h1] at h2
    omega
  have hnt : Nontrivial ↥(A ⊓ L) := (Subgroup.nontrivial_iff_ne_bot (A ⊓ L)).mpr hAne
  obtain ⟨x, hx, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial (A ⊓ L)
  have hx2 : orderOf x = 2 := orderOf_eq_prime (hA.2 x hx.1) hx1
  have hxz : x = z := hzInv x hx hx2
  have hzA : z ∈ A := hxz ▸ hx.1
  have hzAL : z ∈ A ⊓ L := ⟨hzA, hzL⟩
  have hAle : A ⊓ L ≤ Subgroup.zpowers z := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]; exact Subgroup.one_mem _
    · have hy2 : orderOf y = 2 := orderOf_eq_prime (hA.2 y hy.1) hy1
      rw [hzInv y hy hy2]
      exact Subgroup.mem_zpowers z
  have hAinf : A ⊓ L = Subgroup.zpowers z :=
    le_antisymm hAle (Subgroup.zpowers_le.mpr hzAL)
  have hcardInf : Nat.card ↥(A ⊓ L) = 2 := by
    rw [hAinf, Nat.card_zpowers, hz2]
  have hcardA : Nat.card A = 4 := by
    have h2 := CFSG.LocalAnalysis.WeakClosure81.FourEleven.card_le_two_mul_card_inf hidx A
    rw [hcardInf] at h2
    omega
  have hnotle : ¬ A ≤ L := by
    intro hAL
    have h : A ⊓ L = A := inf_eq_left.mpr hAL
    rw [h] at hcardInf
    omega
  have hbex : ∃ b, b ∈ A ∧ b ∉ L := by
    by_contra hcon
    exact hnotle fun y hy => by
      by_contra hyL
      exact hcon ⟨y, hy, hyL⟩
  obtain ⟨b, hbA, hbL⟩ := hbex
  have hb1 : b ≠ 1 := by rintro rfl; exact hbL L.one_mem
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hA.2 b hbA) hb1
  exact ⟨hAinf, hcardA, b, hbA, hbL, hb2⟩

theorem FourElevenSetting.exists_conj_mem_three [L.Normal]
    (hL3 : LieModel ↥L .PSL 3 3 1) (hC : centralizer (L : Set Q) = ⊥)
    {T : Subgroup Q} {b' z : Q}
    (hSyl : IsSylowIn 2 (T ⊓ centralizer ({b'} : Set Q))
      (centralizer ({b'} : Set Q)))
    (hb'L : b' ∉ L) (hb'2 : orderOf b' = 2) (hzT : z ∈ T) (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hzC : z ∈ centralizer ({b'} : Set Q))
    (hzComm : ∀ t ∈ T, t * z = z * t) :
    ∃ c ∈ L ⊓ centralizer ({b'} : Set Q), c * z * c⁻¹ ≠ z ∧ c * z * c⁻¹ ∈ T := by
  set X : Subgroup Q := L ⊓ centralizer ({b'} : Set Q) with hXdef
  set D : Subgroup Q := T ⊓ X with hDdef
  have hXN : (X.subgroupOf (centralizer ({b'} : Set Q))).Normal := by
    rw [hXdef, Subgroup.inf_subgroupOf_right L (centralizer ({b'} : Set Q))]
    exact Subgroup.Normal.subgroupOf (inferInstance : L.Normal) _
  have hD : IsSylowIn 2 D X := by
    have h := IsSylowIn.inf_normal hSyl (N := X) inf_le_right hXN
    have heq : (T ⊓ centralizer ({b'} : Set Q)) ⊓ X = D := by
      rw [hDdef, hXdef]
      ext y
      simp only [Subgroup.mem_inf]
      tauto
    rwa [heq] at h
  have hzD : z ∈ D := ⟨hzT, hzL, hzC⟩
  have hzc : ∀ d ∈ D, d * z = z * d := fun d hd => hzComm d hd.1
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz2
  obtain ⟨e⟩ := CFSG.LocalAnalysis.WeakClosure81.FourEleven.nonempty_mulEquiv_pgl2_three
    hC hL3 hb'L hb'2
  obtain ⟨c, hcX, hcne, hcD⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.FourEleven.exists_conj_mem_of_mulEquiv_pgl2_three
      e inf_le_right hD hzD hz1 hzc
  exact ⟨c, hcX, hcne, hcD.1⟩

theorem FourElevenSetting.exists_member_of_conj_three [L.Normal] {T A : Subgroup Q}
    {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω) (hAΩ : A ∈ Ω) (hA : IsElemAbelian 2 A)
    (hcardA : Nat.card A = 4) (hAT : A ≤ T) {z b c : Q} (hzA : z ∈ A) (hbA : b ∈ A)
    (hbL : b ∉ L) (hb2 : orderOf b = 2) (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hcX : c ∈ L ⊓ centralizer ({b} : Set Q)) (hcT : c * z * c⁻¹ ∈ T)
    (hcne : c * z * c⁻¹ ≠ z) :
    ∃ A' ∈ Ω, A' ≤ T ∧ ∃ u ∈ A' ⊓ L, orderOf u = 2 ∧ u ≠ z := by
  have hLnorm : L.Normal := inferInstance
  have hzb : z * b = b * z :=
    congrArg Subtype.val (hA.1.is_comm.comm (⟨z, hzA⟩ : ↥A) (⟨b, hbA⟩ : ↥A))
  have hzcL : c * z * c⁻¹ ∈ L := hLnorm.conj_mem z hzL c
  have hzc2 : orderOf (c * z * c⁻¹) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h
    rw [h, hz2]
  have hzcC : c * z * c⁻¹ ∈ centralizer ({b} : Set Q) := by
    have hzC : z ∈ centralizer ({b} : Set Q) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hzb
    exact (centralizer ({b} : Set Q)).mul_mem
      ((centralizer ({b} : Set Q)).mul_mem hcX.2 hzC)
      ((centralizer ({b} : Set Q)).inv_mem hcX.2)
  have hcomm : (c * z * c⁻¹) * b = b * (c * z * c⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hzcC
  have hbT : b ∈ T := hAT hbA
  have hbNormalizer : b ∈ Subgroup.normalizer (Subgroup.zpowers (c * z * c⁻¹) : Set Q) := by
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm' : Commute b (c * z * c⁻¹) := hcomm.symm
    have hfix : b * (c * z * c⁻¹) ^ n * b⁻¹ = (c * z * c⁻¹) ^ n := by
      calc b * (c * z * c⁻¹) ^ n * b⁻¹
          = (c * z * c⁻¹) ^ n * b * b⁻¹ := by rw [(hcomm'.zpow_right n).eq]
        _ = (c * z * c⁻¹) ^ n := by simp [mul_assoc]
    rw [hfix]
    exact Subgroup.zpow_mem (K := Subgroup.zpowers (c * z * c⁻¹))
      (Subgroup.mem_zpowers (c * z * c⁻¹)) n
  have hWcard : Nat.card ↥(Subgroup.zpowers (c * z * c⁻¹) ⊔ Subgroup.zpowers b) = 4 := by
    have hsq : b * b ∈ Subgroup.zpowers (c * z * c⁻¹) := by
      have hbsq : b * b = 1 := by
        have h := (orderOf_eq_prime_iff (x := b) (p := 2)).mp hb2
        simpa [pow_two] using h.1
      rw [hbsq]; exact Subgroup.one_mem _
    have hg : b ∉ Subgroup.zpowers (c * z * c⁻¹) := fun hmem =>
      hbL (Subgroup.zpowers_le.mpr hzcL hmem)
    have h := CFSG.GroupTheory.card_sup_zpowers_of_sq_mem hbNormalizer hsq hg
    rw [h, Nat.card_zpowers, hzc2]
  have hAcard : Nat.card ↥(conjSubgroup A c⁻¹) = 4 := by
    unfold CFSG.Quasithin.conjSubgroup
    rw [Subgroup.card_map_of_injective (MulAut.conj (c⁻¹)⁻¹).injective, hcardA]
  have hAeq : Subgroup.zpowers (c * z * c⁻¹) ⊔ Subgroup.zpowers b =
      conjSubgroup A c⁻¹ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, mem_conjSubgroup_iff]
        have h1 : c⁻¹ * (c * z * c⁻¹) * (c⁻¹)⁻¹ = z := by group
        rw [h1]; exact hzA
      · rw [Subgroup.zpowers_le, mem_conjSubgroup_iff]
        have h4 : c⁻¹ * b = b * c⁻¹ :=
          Subgroup.mem_centralizer_singleton_iff.mp
            ((centralizer ({b} : Set Q)).inv_mem hcX.2)
        have h1 : c⁻¹ * b * (c⁻¹)⁻¹ = b := by
          calc c⁻¹ * b * (c⁻¹)⁻¹ = b * c⁻¹ * (c⁻¹)⁻¹ := by rw [h4]
            _ = b := by simp [mul_assoc]
        rw [h1]; exact hbA
    · rw [hWcard, hAcard]
  refine ⟨Subgroup.zpowers (c * z * c⁻¹) ⊔ Subgroup.zpowers b, ?_, ?_,
    c * z * c⁻¹, ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers _), hzcL⟩, hzc2, hcne⟩
  · rw [hAeq]
    exact hΩ.conj _ hAΩ c⁻¹
  · exact sup_le (Subgroup.zpowers_le.mpr hcT) (Subgroup.zpowers_le.mpr hbT)

theorem FourElevenSetting.exists_inner_involution_of_pgl2_three [L.Normal]
    (hL3 : LieModel ↥L .PSL 3 3 1) (hC : centralizer (L : Set Q) = ⊥)
    {T A : Subgroup Q} {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω) (hAΩ : A ∈ Ω)
    (hA : IsElemAbelian 2 A) (hcardA : Nat.card A = 4) (hAT : A ≤ T) {z b : Q}
    (hzA : z ∈ A) (hbA : b ∈ A) (hbL : b ∉ L) (hb2 : orderOf b = 2) (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hzT : z ∈ T) (hzComm : ∀ t ∈ T, t * z = z * t)
    (hSyl : IsSylowIn 2 (T ⊓ centralizer ({b} : Set Q)) (centralizer ({b} : Set Q))) :
    ∃ A' ∈ Ω, A' ≤ T ∧ ∃ u ∈ A' ⊓ L, orderOf u = 2 ∧ u ≠ z := by
  have hzC : z ∈ centralizer ({b} : Set Q) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm (⟨z, hzA⟩ : ↥A) (⟨b, hbA⟩ : ↥A)))
  obtain ⟨c, hcX, hcne, hcT⟩ :=
    FourElevenSetting.exists_conj_mem_three hL3 hC hSyl hbL hb2 hzT hzL hz2 hzC hzComm
  exact FourElevenSetting.exists_member_of_conj_three hΩ hAΩ hA hcardA hAT hzA hbA hbL hb2
    hzL hz2 hcX hcT hcne

theorem FourElevenSetting.exists_inner_involution_three (h : FourElevenSetting Q L p)
    (hp : p = 3) {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) (hcard : ∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A) {z : Q} (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hzT : ∀ t ∈ T, t * z = z * t) :
    ∃ A ∈ Ω, A ≤ T ∧ ∃ u ∈ A ⊓ L, orderOf u = 2 ∧ u ≠ z := by
  subst hp
  have hLnorm : L.Normal := h.normal
  have hL3 : LieModel ↥L .PSL 3 3 1 := by
    rcases h.isL3 with h1 | h2
    · exact h1
    · exact absurd h2 (h.not_psu33 rfl)
  obtain ⟨A, hAΩ, hAT⟩ := hΩ.exists_mem_le hT
  have hAe : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  have hA4 : 4 ≤ Nat.card A := hcard A hAΩ hAT
  by_cases hex : ∃ u ∈ A ⊓ L, orderOf u = 2 ∧ u ≠ z
  · exact ⟨A, hAΩ, hAT, hex⟩
  push Not at hex
  obtain ⟨hAinf, hcardA, b, hbA, hbL, hb2⟩ :=
    FourElevenSetting.exists_involution_not_mem_of_unique h.index_le_two hAe hA4 hzL hz2 hex
  have hzAL : z ∈ A ⊓ L := by rw [hAinf]; exact Subgroup.mem_zpowers z
  have hzA : z ∈ A := hzAL.1
  obtain ⟨g, hA'Ω, hA'T, hSyl⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.FourEleven.exists_conj_isSylowIn_centralizer
      hT hΩ hAΩ hAT hbA
  set b' : Q := g⁻¹ * b * g with hb'def
  set z' : Q := g⁻¹ * z * g with hz'def
  have hz'A : z' ∈ conjSubgroup A g := by
    rw [mem_conjSubgroup_iff, hz'def]
    have h1 : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
    rw [h1]; exact hzA
  have hz'L : z' ∈ L := by
    rw [hz'def]
    have h1 := h.normal.conj_mem z hzL g⁻¹
    have h2 : g⁻¹ * z * (g⁻¹)⁻¹ = g⁻¹ * z * g := by group
    rwa [h2] at h1
  have hz'2 : orderOf z' = 2 := by
    rw [hz'def]
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    rw [MulAut.conj_apply] at h
    simpa [hz2] using h
  by_cases hzz : z' = z
  · have hzA' : z ∈ conjSubgroup A g := hzz ▸ hz'A
    have hb'A' : b' ∈ conjSubgroup A g := by
      rw [mem_conjSubgroup_iff, hb'def]
      have h1 : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      rw [h1]; exact hbA
    have hb'L : b' ∉ L := by
      intro hmem
      apply hbL
      have h1 := h.normal.conj_mem b' hmem g
      have h2 : g * b' * g⁻¹ = b := by rw [hb'def]; group
      rwa [h2] at h1
    have hb'2 : orderOf b' = 2 := by
      rw [hb'def]
      have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) b
      rw [MulAut.conj_apply] at h
      simpa [hb2] using h
    have hcard' : Nat.card (conjSubgroup A g) = 4 := by
      unfold CFSG.Quasithin.conjSubgroup
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcardA]
    have hA'e : IsElemAbelian 2 (conjSubgroup A g) := hΩ.elemAbelian _ hA'Ω
    exact FourElevenSetting.exists_inner_involution_of_pgl2_three hL3 h.centralizer_eq_bot
      hΩ hA'Ω hA'e hcard' hA'T hzA' hb'A' hb'L hb'2 hzL hz2 (hA'T hzA') hzT hSyl
  · exact ⟨conjSubgroup A g, hA'Ω, hA'T, z', ⟨hz'A, hz'L⟩, hz'2, hzz⟩

theorem FourElevenSetting.exists_member_three (h : FourElevenSetting Q L p) (hp : p = 3)
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω)
    (hcard : ∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A) {z : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzT : ∀ t ∈ T, t * z = z * t) :
    ∃ A ∈ Ω, A ≤ T ∧ (∃ u ∈ A ⊓ L, orderOf u = 2 ∧ u ≠ z) ∧
      ∃ X : Subgroup Q, PermThreeMember L T A z X := by
  subst hp
  have hLnorm : L.Normal := h.normal
  have hL3 : LieModel ↥L .PSL 3 3 1 := by
    rcases h.isL3 with h1 | h2
    · exact h1
    · exact absurd h2 (h.not_psu33 rfl)
  have hLmodel : LieModel ↥L .PSL 3 3 1 ∨ LieModel ↥L .PSU 3 3 1 := Or.inl hL3
  obtain ⟨A, hAΩ, hAT, u, hu, hu2, huz⟩ :=
    h.exists_inner_involution_three rfl hT hΩ hcard hzL hz2 hzT
  have huT : u ∈ T := hAT hu.1
  have huL : u ∈ L := hu.2
  obtain ⟨W, hWL, hWe, hW4, hzW, hTN, huW, hSylW⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.FourEleven.exists_frame_four_sd
      (p := 3) h.prime (by norm_num) (Or.inl ⟨hL3, by norm_num⟩) hT hzL hz2 hzT huT huL
      hu2 huz
  obtain ⟨hab, h6, X₀, hX₀, hX₀M, hX₀sup⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.FourEleven.exists_monomial_frame
      (p := 3) h.prime (by norm_num) hLmodel hWL hWe hW4
  have hCA : centralizer (A : Set Q) ≤ centralizer ({u} : Set Q) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hx u hu.1
  have hR : UniquenessCase.PartTwo.tA T A ≤ normalizer (W : Set Q) := by
    rw [CFSG.LocalAnalysis.WeakClosure81.FourEleven.tA_eq_inf_centralizer
      h.pCoreOf_two_top T A]
    exact (inf_le_inf_left T hCA).trans hTN
  have hAW : ¬ A ⊓ L ≤ centralizer (W : Set Q) := fun hle => huW (hle hu)
  obtain ⟨X, hX⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.FourEleven.exists_permThreeMember_of_frame
      hT hAT hWL hWe hW4 hzW hz2 hab h6 hX₀ hX₀M hX₀sup hSylW hR hAW
  exact ⟨A, hAΩ, hAT, ⟨u, hu, hu2, huz⟩, X, hX⟩

theorem fourElevenThree_holds : FourElevenThree := by
  intro Q _ _ L p hS hp T hT Ω hΩ hcard
  subst hp
  have hLnorm : L.Normal := hS.normal
  have hL3 : LieModel ↥L .PSL 3 3 1 := by
    rcases hS.isL3 with h1 | h2
    · exact h1
    · exact absurd h2 (hS.not_psu33 rfl)
  obtain ⟨z, hzL, hz2, hzT⟩ := hS.exists_central_involution hT
  have hcard' : ∀ A ∈ Ω, A ≤ T → 4 ≤ Nat.card A := by
    intro A hAΩ hAT
    simpa using hcard A hAΩ hAT
  obtain ⟨A, hAΩ, hAT, ⟨u, hu, hu2, huz⟩, X, hX⟩ :=
    hS.exists_member_three rfl hT hΩ hcard' hzL hz2 hzT
  have hAe : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  have h1 : InCalEi 1 T A (centralizer ({z} : Set Q)) :=
    hS.inCalEi_centralizer_three rfl hT hAT hAe hzL hz2 hzT hu.1 hu.2 hu2 huz
  have hCQ : centralizer ({z} : Set Q) ≤ genEi 1 T Ω ⊔ T :=
    (CFSG.LocalAnalysis.WeakClosure81.le_genEi_of_inCalEi hAΩ hAT h1).trans le_sup_left
  have h2 : InCalEi 1 T A (X ⊔ UniquenessCase.PartTwo.tA T A) :=
    hX.inCalEi le_rfl hS.index_le_two hT hAT hAe
  have hXT : X ⊔ UniquenessCase.PartTwo.tA T A ≤ genEi 1 T Ω ⊔ T :=
    (CFSG.LocalAnalysis.WeakClosure81.le_genEi_of_inCalEi hAΩ hAT h2).trans le_sup_left
  obtain ⟨c, hcX, hcne, hcComm⟩ := hX.exists_conj
  have hLK : L ≤ genEi 1 T Ω ⊔ T := by
    refine CFSG.LocalAnalysis.WeakClosure81.FourEleven.le_of_centralizer_le_of_commuting_conj_three
      hL3 hzL hz2 ?_ ?_ hcne hcComm
    · exact inf_le_right.trans hCQ
    · exact (le_sup_left.trans hXT) hcX
  exact hS.eq_top_of_le hT hLK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
