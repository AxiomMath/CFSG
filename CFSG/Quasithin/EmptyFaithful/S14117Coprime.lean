module

public import CFSG.Quasithin.EmptyFaithful.S14117Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

section Abstract

variable {A : Type*} [Group A]

theorem le_normalizer_commutator_of_le {B P Q : Subgroup A} (hQB : Q ≤ Subgroup.normalizer (B : Set A))
    (hQP : Q ≤ Subgroup.normalizer (P : Set A)) :
    Q ≤ Subgroup.normalizer ((⁅B, P⁆ : Subgroup A) : Set A) := by
  have key : ∀ q ∈ Q, ∀ x ∈ ⁅B, P⁆, q * x * q⁻¹ ∈ ⁅B, P⁆ := by
    intro q hq
    have hle : ⁅B, P⁆ ≤ (⁅B, P⁆).comap (MulAut.conj q).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun b hb p hp => ?_
      show (MulAut.conj q) ⁅b, p⁆ ∈ ⁅B, P⁆
      rw [MulAut.conj_apply]
      have e : q * ⁅b, p⁆ * q⁻¹ = ⁅q * b * q⁻¹, q * p * q⁻¹⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.mp (hQB hq) b).mp hb)
        ((Subgroup.mem_normalizer_iff.mp (hQP hq) p).mp hp)
    intro x hx
    exact hle hx
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key q hq x, fun hx => ?_⟩
  have := key q⁻¹ (Q.inv_mem hq) _ hx
  simpa [mul_assoc] using this

theorem conjClosure_sup_eq_commutator_sup {B P S : Subgroup A}
    (hSB : S ≤ Subgroup.normalizer (B : Set A)) (hSP : S ≤ Subgroup.normalizer (P : Set A)) :
    conjClosure P (B ⊔ S) = ⁅B, P⁆ ⊔ P := by
  apply le_antisymm
  · refine conjClosure_le fun g hg z hz => ?_
    have hgmul : ((B ⊔ S : Subgroup A) : Set A) = (B : Set A) * (S : Set A) :=
      Subgroup.coe_mul_of_right_le_normalizer_left B S hSB
    have hg' : g ∈ (B : Set A) * (S : Set A) := by rw [← hgmul]; exact hg
    obtain ⟨b, hb, s, hs, rfl⟩ := hg'
    set z' : A := s * z * s⁻¹ with hz'
    have hz'P : z' ∈ P := (Subgroup.mem_normalizer_iff.mp (hSP hs) z).mp hz
    have e : b * s * z * (b * s)⁻¹ = ⁅b, z'⁆ * z' := by
      simp only [commutatorElement_def, hz']
      group
    rw [e]
    exact (⁅B, P⁆ ⊔ P).mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hb hz'P))
      (Subgroup.mem_sup_right hz'P)
  · refine sup_le (Subgroup.commutator_le.mpr fun b hb z hz => ?_) (le_conjClosure P (B ⊔ S))
    have h1 : b * z * b⁻¹ ∈ conjClosure P (B ⊔ S) :=
      mem_conjClosure (Subgroup.mem_sup_left hb) hz
    have h2 : z⁻¹ ∈ conjClosure P (B ⊔ S) := le_conjClosure P (B ⊔ S) (P.inv_mem hz)
    have := (conjClosure P (B ⊔ S)).mul_mem h1 h2
    simpa [commutatorElement_def, mul_assoc] using this

theorem oTwoUpper_commutator_sup {B P : Subgroup A} (hB : Odd (Nat.card B)) (hP : IsPGroup 2 P)
    (hPB : P ≤ Subgroup.normalizer (B : Set A)) :
    oTwoUpper (⁅B, P⁆ ⊔ P) = ⁅B, P⁆ := by
  have hcomm : ⁅B, P⁆ ≤ B := Subgroup.le_normalizer_iff_commutator_le_left.mp hPB
  have hnormK : P ≤ Subgroup.normalizer ((⁅B, P⁆ : Subgroup A) : Set A) :=
    le_normalizer_commutator_of_le hPB Subgroup.le_normalizer
  have hmul : ((⁅B, P⁆ ⊔ P : Subgroup A) : Set A) = ((⁅B, P⁆ : Subgroup A) : Set A) * (P : Set A) :=
    Subgroup.coe_mul_of_right_le_normalizer_left ⁅B, P⁆ P hnormK
  apply le_antisymm
  · refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    have hx' : x ∈ ((⁅B, P⁆ : Subgroup A) : Set A) * (P : Set A) := by rw [← hmul]; exact hx
    obtain ⟨c, hc, p, hp, rfl⟩ := hx'
    obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
    have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨x', hx', hxe⟩ := A4.exists_pow_mul_eq hc (hnormK hp) (2 ^ k)
    exact ⟨k, by rw [hxe, hk', mul_one]; exact hx'⟩
  · intro x hx
    refine mem_oTwoUpper_of_odd (Subgroup.mem_sup_left hx) ?_
    have hxB : x ∈ B := hcomm hx
    have hd : orderOf (⟨x, hxB⟩ : B) ∣ Nat.card B := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    exact Odd.of_dvd_nat hB hd

end Abstract

section Transfer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conjClosure_eq {G' : Type*} [Group G'] (f : G →* G') (Z H : Subgroup G) :
    (conjClosure Z H).map f = conjClosure (Z.map f) (H.map f) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine conjClosure_le fun h hh z hz => ?_
    show f (h * z * h⁻¹) ∈ conjClosure (Z.map f) (H.map f)
    rw [map_mul, map_mul, map_inv]
    exact mem_conjClosure (Subgroup.mem_map_of_mem f hh) (Subgroup.mem_map_of_mem f hz)
  · refine conjClosure_le fun h' hh' z' hz' => ?_
    obtain ⟨h, hh, rfl⟩ := hh'
    obtain ⟨z, hz, rfl⟩ := hz'
    exact ⟨h * z * h⁻¹, mem_conjClosure hh hz, by simp⟩

omit [Finite G] in
theorem autOn_sup {V X Y : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) :
    autOn (X ⊔ Y) V = autOn X V ⊔ autOn Y V :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hX hY

omit [Finite G] in
theorem autOn_conjClosure {V Z H : Subgroup G} (hZ : Z ≤ Subgroup.normalizer (V : Set G))
    (hH : H ≤ Subgroup.normalizer (V : Set G)) :
    autOn (conjClosure Z H) V = conjClosure (autOn Z V) (autOn H V) := by
  have hle : conjClosure Z H ≤ Subgroup.normalizer (V : Set G) :=
    conjClosure_le fun h hh z hz =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hH hh) (hZ hz)) (Subgroup.inv_mem _ (hH hh))
  have h1 : (conjClosure Z H).subgroupOf (Subgroup.normalizer (V : Set G)) =
      conjClosure (Z.subgroupOf (Subgroup.normalizer (V : Set G)))
        (H.subgroupOf (Subgroup.normalizer (V : Set G))) := by
    apply Subgroup.map_injective (Subgroup.normalizer (V : Set G)).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hle, map_conjClosure_eq,
      Subgroup.map_subgroupOf_eq_of_le hZ, Subgroup.map_subgroupOf_eq_of_le hH]
  unfold autOn
  rw [h1, map_conjClosure_eq]

omit [Finite G] in
theorem autOn_le_normalizer_autOn {V X Z : Subgroup G}
    (_hXV : X ≤ Subgroup.normalizer (V : Set G)) (hZV : Z ≤ Subgroup.normalizer (V : Set G))
    (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) :
    autOn X V ≤ Subgroup.normalizer (autOn Z V : Set (MulAut V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hXZ

end Transfer

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ V Y₀ : Subgroup G}

theorem lemma_14_1_17_two (h : quasithinQTFE14Cat G T Mc) (hyp : Hyp14117 T Mc M M₁ V)
    (hY₀M : Y₀ ≤ M) (hY₀T : T ≤ Subgroup.normalizer (Y₀ : Set G))
    (hodd : Odd (Nat.card (autOn Y₀ V))) :
    autOn (oTwoUpper (conjClosure (pCoreOf 2 (M₁ ⊓ M)) (Y₀ ⊔ T))) V =
      ⁅autOn Y₀ V, autOn (pCoreOf 2 (M₁ ⊓ M)) V⁆ := by
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hyp.le_normalizer
  have hTM : T ≤ M := hyp.inM.2
  have hRT : pCoreOf 2 (M₁ ⊓ M) ≤ T := hyp.pCoreOf_le_sylow h
  have hRM : pCoreOf 2 (M₁ ⊓ M) ≤ M := hRT.trans hTM
  have hJM : Y₀ ⊔ T ≤ M := sup_le hY₀M hTM
  have hWM : conjClosure (pCoreOf 2 (M₁ ⊓ M)) (Y₀ ⊔ T) ≤ M :=
    conjClosure_le fun g hg z hz =>
      M.mul_mem (M.mul_mem (hJM hg) (hRM hz)) (M.inv_mem (hJM hg))
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 (M₁ ⊓ M) : Set G) :=
    hyp.le_inf.trans (le_normalizer_pCoreOf 2 (M₁ ⊓ M))
  rw [← A4.oTwoUpper_autOn (hWM.trans hMV),
    autOn_conjClosure (hRM.trans hMV) (hJM.trans hMV), autOn_sup (hY₀M.trans hMV) (hTM.trans hMV)]
  have hP : autOn (pCoreOf 2 (M₁ ⊓ M)) V ≤ autOn T V := A4.autOn_mono hRT
  have hS2 : IsPGroup 2 (autOn T V) := by
    unfold autOn
    exact (h.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe (hTM.trans hMV)).symm).map _
  have hSB : autOn T V ≤ Subgroup.normalizer (autOn Y₀ V : Set (MulAut V)) :=
    autOn_le_normalizer_autOn (hTM.trans hMV) (hY₀M.trans hMV) hY₀T
  have hSP : autOn T V ≤ Subgroup.normalizer (autOn (pCoreOf 2 (M₁ ⊓ M)) V : Set (MulAut V)) :=
    autOn_le_normalizer_autOn (hTM.trans hMV) (hRM.trans hMV) hTN
  rw [conjClosure_sup_eq_commutator_sup hSB hSP]
  exact oTwoUpper_commutator_sup hodd (hS2.to_le hP) (hP.trans hSB)

end Main

end CFSG.Quasithin
