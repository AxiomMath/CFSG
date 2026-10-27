module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7Rep
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerZpowers
import CFSG.RankThree.PartTwo.Sec16.Item162Res7PushA7
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_normalizer_of_mem_normalizer_sup {p : ℕ} [Fact p.Prime]
    {A Q : Subgroup G} (hA : IsPGroup p A) (hQ : Nat.Coprime (Nat.card Q) p)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) {x : G}
    (hxQ : x ∈ Subgroup.normalizer (Q : Set G))
    (hx : x ∈ Subgroup.normalizer ((A ⊔ Q : Subgroup G) : Set G)) :
    ∃ q ∈ Q, q * x ∈ Subgroup.normalizer (A : Set G) := by
  classical
  let H : Subgroup G := A ⊔ Q
  let B : Subgroup G := A.map (MulAut.conj x).toMonoidHom
  have hAH : A ≤ H := le_sup_left
  have hBH : B ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx a).mp (hAH ha)
  have hcopAQ : Nat.Coprime (Nat.card A) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hA.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n hQ.symm
  have hdisj : Disjoint A Q := Subgroup.disjoint_of_coprime_natCard hcopAQ
  have hHcard : Nat.card H = Nat.card A * Nat.card Q := by
    have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q A hAQ hdisj.symm
    rw [sup_comm] at h
    rw [h, Nat.mul_comm]
  have hcardA : Nat.card (A.subgroupOf H) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  have hcardB : Nat.card (B.subgroupOf H) = Nat.card A := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv]
    exact Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hindexA : (A.subgroupOf H).index = Nat.card Q := by
    have h1 : Nat.card (A.subgroupOf H) * (A.subgroupOf H).index = Nat.card ↥H :=
      Subgroup.card_mul_index (A.subgroupOf H)
    rw [hcardA, hHcard] at h1
    exact Nat.mul_left_cancel Nat.card_pos h1
  have hindexB : (B.subgroupOf H).index = Nat.card Q := by
    have h1 : Nat.card (B.subgroupOf H) * (B.subgroupOf H).index = Nat.card ↥H :=
      Subgroup.card_mul_index (B.subgroupOf H)
    rw [hcardB, hHcard] at h1
    exact Nat.mul_left_cancel Nat.card_pos h1
  have hpQ : ¬ p ∣ Nat.card Q :=
    (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hQ.symm
  let P : Sylow p H := hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm |>.toSylow
    (by rw [hindexA]; exact hpQ)
  let P' : Sylow p H := hA.map (MulAut.conj x).toMonoidHom |>.of_equiv
    (Subgroup.subgroupOfEquivOfLe hBH).symm |>.toSylow (by rw [hindexB]; exact hpQ)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq H P P'
  have hset : (P : Subgroup H).map (MulAut.conj y).toMonoidHom = (P' : Subgroup H) := by
    have h2 : ((y • P : Sylow p H) : Subgroup H) = (P' : Subgroup H) :=
      congrArg (fun S : Sylow p H => (S : Subgroup H)) hy
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h2
    exact h2
  have hconjB : ∀ a ∈ A, (y : G) * a * (y : G)⁻¹ ∈ B := by
    intro a ha
    have haH : a ∈ H := hAH ha
    have hmemP : (⟨a, haH⟩ : H) ∈ (P : Subgroup H) := by
      simpa [P] using (Subgroup.mem_subgroupOf.mpr ha)
    have hmapmem : (MulAut.conj y) ⟨a, haH⟩ ∈
        (P : Subgroup H).map (MulAut.conj y).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hmemP
    rw [hset] at hmapmem
    have hPB : (P' : Subgroup H) = B.subgroupOf H := by simp [P', B]
    rw [hPB] at hmapmem
    have := Subgroup.mem_subgroupOf.mp hmapmem
    simpa [MulAut.conj_apply, B] using this
  have hB : ∀ b ∈ B, ∃ a' ∈ A, (y : G) * a' * (y : G)⁻¹ = b := by
    intro b hb
    have hbH : b ∈ H := hBH hb
    have hbP' : (⟨b, hbH⟩ : H) ∈ (P' : Subgroup H) := by
      have hPB : (P' : Subgroup H) = B.subgroupOf H := by simp [P', B]
      rw [hPB]
      exact Subgroup.mem_subgroupOf.mpr hb
    rw [← hset] at hbP'
    obtain ⟨a', ha'P, ha'eq⟩ := Subgroup.mem_map.mp hbP'
    refine ⟨(a' : G), ?_, ?_⟩
    · simpa [P] using (Subgroup.mem_subgroupOf.mp ha'P)
    · simpa [MulAut.conj_apply] using congrArg Subtype.val ha'eq
  have hyx : (y : G)⁻¹ * x ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    obtain ⟨a', ha', ha'eq⟩ := hB _ (Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom ha)
    have e : ((y : G)⁻¹ * x) * a * ((y : G)⁻¹ * x)⁻¹ = a' := by
      calc ((y : G)⁻¹ * x) * a * ((y : G)⁻¹ * x)⁻¹
          = (y : G)⁻¹ * (x * a * x⁻¹) * y := by group
        _ = (y : G)⁻¹ * ((MulEquiv.toMonoidHom (MulAut.conj x)) a) * y := by
          simp [MulAut.conj_apply]
        _ = (y : G)⁻¹ * ((y : G) * a' * (y : G)⁻¹) * y := by rw [← ha'eq]
        _ = a' := by group
    rw [e]
    exact ha'
  have hyinv : (y : G)⁻¹ ∈ (A : Set G) * (Q : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A Q hAQ]
    exact H.inv_mem y.2
  obtain ⟨a0, ha0, q0, hq0, haq⟩ := hyinv
  refine ⟨q0, hq0, ?_⟩
  have hprod : a0 * (q0 * x) ∈ Subgroup.normalizer (A : Set G) := by
    have h1 : a0 * (q0 * x) = (y : G)⁻¹ * x := by rw [← haq]; group
    rw [h1]
    exact hyx
  have h2 : q0 * x = a0⁻¹ * (a0 * (q0 * x)) := by group
  rw [h2]
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer (A.inv_mem ha0)) hprod


private theorem conj_mem_sup_of_a7Rep_mem_normalizer {A K Q : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hOQ : CFSG.Open.pCoreOf 2 K ≤ Q)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) {y d : G}
    (hyK : y ∈ K) (hd : d ∈ A ⊓ K) {π : Equiv.Perm (Fin 7)}
    (hρy : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
      ⟨y, Subgroup.le_normalizer hyK⟩ = π)
    (hπ : π ∈ Subgroup.normalizer
      ((((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) : Subgroup (Equiv.Perm (Fin 7))) :
          Set (Equiv.Perm (Fin 7)))) :
    y * d * y⁻¹ ∈ A ⊔ Q := by
  classical
  let N := Subgroup.normalizer (K : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
  let D := A ⊓ K
  let P : Subgroup (Equiv.Perm (Fin 7)) := (D.subgroupOf N).map ρ
  have hdK : d ∈ K := (Subgroup.mem_inf.mp hd).2
  have hdA : d ∈ A := (Subgroup.mem_inf.mp hd).1
  have hmemK : y * d * y⁻¹ ∈ K := K.mul_mem (K.mul_mem hyK hdK) (K.inv_mem hyK)
  have hρmem : ρ ⟨y * d * y⁻¹, Subgroup.le_normalizer hmemK⟩ ∈ P := by
    have e : (⟨y * d * y⁻¹, Subgroup.le_normalizer hmemK⟩ : ↥N) =
        ⟨y, Subgroup.le_normalizer hyK⟩ * ⟨d, hAK hdA⟩ *
          ⟨y, Subgroup.le_normalizer hyK⟩⁻¹ := Subtype.ext (by simp)
    rw [e, map_mul, map_mul, map_inv, hρy]
    have hdP : ρ ⟨d, hAK hdA⟩ ∈ P :=
      Subgroup.mem_map.mpr ⟨⟨d, hAK hdA⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hπ _).mp hdP
  have hρmem' : ρ ⟨y * d * y⁻¹, Subgroup.le_normalizer hmemK⟩ ∈
      (D.subgroupOf N).map ρ := by simpa [P] using hρmem
  obtain ⟨d', hd'D, hd'eq⟩ := Subgroup.mem_map.mp hρmem'
  have hd'D' : (d' : G) ∈ D := Subgroup.mem_subgroupOf.mp hd'D
  have hmemO : (d' : G)⁻¹ * (y * d * y⁻¹) ∈ CFSG.Open.pCoreOf 2 K := by
    have hmemK2 : (d' : G)⁻¹ * (y * d * y⁻¹) ∈ K :=
      K.mul_mem (K.inv_mem (Subgroup.mem_inf.mp hd'D').2) hmemK
    refine (a7Rep_eq_one_iff_mem_pCoreOf φ hmemK2).mp ?_
    have e : (⟨(d' : G)⁻¹ * (y * d * y⁻¹), Subgroup.le_normalizer hmemK2⟩ : ↥N) =
        (d')⁻¹ * ⟨y * d * y⁻¹, Subgroup.le_normalizer hmemK⟩ := Subtype.ext rfl
    rw [e, map_mul, map_inv, hd'eq, inv_mul_cancel]
  have hmemQ : (d' : G)⁻¹ * (y * d * y⁻¹) ∈ Q := hOQ hmemO
  have heq : y * d * y⁻¹ = (d' : G) * ((d' : G)⁻¹ * (y * d * y⁻¹)) := by group
  rw [heq]
  exact (A ⊔ Q).mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mp hd'D').1)
    (Subgroup.mem_sup_right hmemQ)

private theorem y0_mem_normalizer_sup_of_a7Rep {A K S Q : Subgroup G} {k y : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hk : k ∈ A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hQdef : Q = CFSG.Open.pCoreOf 2 (K ⊔ S))
    (hck : ∀ x ∈ K ⊔ S, k * x * k⁻¹ * x⁻¹ ∈ Q)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {σ : Equiv.Perm (Fin 7)} (hyK : y ∈ K)
    (hρy : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
      ⟨y, Subgroup.le_normalizer hyK⟩ = σ)
    (hσP : σ ∈ Subgroup.normalizer
      ((((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) : Subgroup (Equiv.Perm (Fin 7))) :
          Set (Equiv.Perm (Fin 7)))) :
    y ∈ Subgroup.normalizer ((A ⊔ Q : Subgroup G) : Set G) := by
  classical
  let N := Subgroup.normalizer (K : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
  let D := A ⊓ K
  let P : Subgroup (Equiv.Perm (Fin 7)) := (D.subgroupOf N).map ρ
  have hAKS : A ≤ Subgroup.normalizer ((K ⊔ S : Subgroup G) : Set G) :=
    fun a ha => Subgroup.inf_normalizer_le_normalizer_sup K S ⟨hAK ha, hAS ha⟩
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]
    exact hAKS.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ S))
  have hQn : K ⊔ S ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ S)
  have hyQ : y ∈ Subgroup.normalizer (Q : Set G) := hQn (Subgroup.mem_sup_left hyK)
  have hOQ : CFSG.Open.pCoreOf 2 K ≤ Q := by
    rw [hQdef]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hSK).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
  have hkQ : ρ ⟨k, hAK hk⟩ = 1 := by
    rw [CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_eq_one_iff]
    change ∀ z ∈ K, k * z * k⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 K
    intro z hz
    have hmemK : k * z * k⁻¹ * z⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAK hk) z).mp hz) (K.inv_mem hz)
    have hmemQ : k * z * k⁻¹ * z⁻¹ ∈ Q := hck z (Subgroup.mem_sup_left hz)
    exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (le_sup_left : K ≤ K ⊔ S)
      ⟨hmemK, by simpa [hQdef] using hmemQ⟩
  have hcommK : y * k * y⁻¹ * k⁻¹ ∈ K := by
    have h1 : k * y⁻¹ * k⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hAK hk) y⁻¹).mp (K.inv_mem hyK)
    simpa [mul_assoc] using K.mul_mem hyK h1
  have hquot : ρ ⟨y * k * y⁻¹ * k⁻¹, Subgroup.le_normalizer hcommK⟩ = 1 := by
    have e : (⟨y * k * y⁻¹ * k⁻¹, Subgroup.le_normalizer hcommK⟩ : ↥N) =
        ⟨y, Subgroup.le_normalizer hyK⟩ * ⟨k, hAK hk⟩ *
          ⟨y, Subgroup.le_normalizer hyK⟩⁻¹ * ⟨k, hAK hk⟩⁻¹ := Subtype.ext (by simp)
    rw [e]
    simp only [map_mul, map_inv, hρy, hkQ]
    group
  have hcommQ : y * k * y⁻¹ * k⁻¹ ∈ Q :=
    hOQ ((a7Rep_eq_one_iff_mem_pCoreOf φ hcommK).mp hquot)
  have hyQinv : y⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).inv_mem hyQ
  obtain ⟨q, hqQ, hyq⟩ : ∃ q ∈ Q, y * k * y⁻¹ = k * q := by
    refine ⟨k⁻¹ * (y * k * y⁻¹ * k⁻¹) * k, ?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Q : Set G)).inv_mem (hAQ hk)) _).mp hcommQ
    · calc y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k := by group
        _ = k * (k⁻¹ * (y * k * y⁻¹ * k⁻¹) * k) := by group
  have hDk : D ≤ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup G) : Set G) := by
    intro d hd
    refine CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers k ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (hA.1.is_comm.comm ⟨d, (Subgroup.mem_inf.mp hd).1⟩ ⟨k, hk⟩))
  have hdecomp : ∀ a ∈ A, ∃ d ∈ D, ∃ m : ℤ, d * k ^ m = a := by
    intro a ha
    have ha' : a ∈ D ⊔ Subgroup.zpowers k := by rw [hAk]; exact ha
    have ha'' : a ∈ (D : Set G) * (Subgroup.zpowers k : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right D (Subgroup.zpowers k) hDk]
      exact ha'
    obtain ⟨d, hd, z, hz, hdz⟩ := ha''
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨d, hd, m, hdz⟩
  have hkq_sup : y * k * y⁻¹ ∈ A ⊔ Q := by
    rw [hyq]
    exact (A ⊔ Q).mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hqQ)
  have hpow_sup : ∀ m : ℤ, y * k ^ m * y⁻¹ ∈ A ⊔ Q := by
    intro m
    have e : y * k ^ m * y⁻¹ = (y * k * y⁻¹) ^ m := by
      simpa [MulAut.conj_apply] using (map_zpow (MulAut.conj y) k m)
    rw [e]
    exact (A ⊔ Q).zpow_mem hkq_sup m
  have hy_A_le : ∀ a ∈ A, y * a * y⁻¹ ∈ A ⊔ Q := by
    intro a ha
    obtain ⟨d, hd, m, rfl⟩ := hdecomp a ha
    have h1 : y * (d * k ^ m) * y⁻¹ = (y * d * y⁻¹) * (y * k ^ m * y⁻¹) := by group
    rw [h1]
    exact (A ⊔ Q).mul_mem
      (conj_mem_sup_of_a7Rep_mem_normalizer hA hAK hOQ φ hyK hd hρy hσP) (hpow_sup m)
  have hy_sup_le : ∀ x ∈ A ⊔ Q, y * x * y⁻¹ ∈ A ⊔ Q := by
    intro x hx
    have hx' : x ∈ (A : Set G) * (Q : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A Q hAQ]
      exact hx
    obtain ⟨a, ha, q0, hq0, rfl⟩ := hx'
    have h1 : y * (a * q0) * y⁻¹ = (y * a * y⁻¹) * (y * q0 * y⁻¹) := by group
    rw [h1]
    exact (A ⊔ Q).mul_mem (hy_A_le a ha)
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hyQ q0).mp hq0))
  have hρyinv : ρ ⟨y⁻¹, Subgroup.le_normalizer (K.inv_mem hyK)⟩ = σ⁻¹ := by
    have e : (⟨y⁻¹, Subgroup.le_normalizer (K.inv_mem hyK)⟩ : ↥N) =
        (⟨y, Subgroup.le_normalizer hyK⟩ : ↥N)⁻¹ := Subtype.ext (by simp)
    rw [e, map_inv, hρy]
  have hσPinv : σ⁻¹ ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin 7))) :=
    (Subgroup.normalizer (P : Set (Equiv.Perm (Fin 7)))).inv_mem hσP
  have hyinv_A_le : ∀ a ∈ A, y⁻¹ * a * y ∈ A ⊔ Q := by
    intro a ha
    obtain ⟨d, hd, m, rfl⟩ := hdecomp a ha
    have h1 : y⁻¹ * (d * k ^ m) * y = (y⁻¹ * d * y) * (y⁻¹ * k ^ m * y) := by group
    rw [h1]
    have hd' : y⁻¹ * d * y ∈ A ⊔ Q := by
      simpa using conj_mem_sup_of_a7Rep_mem_normalizer hA hAK hOQ φ
        (K.inv_mem hyK) hd hρyinv hσPinv
    have hk' : y⁻¹ * k * y ∈ A ⊔ Q := by
      have hq' : y⁻¹ * q * y ∈ Q := by
        simpa using (Subgroup.mem_normalizer_iff.mp hyQinv q).mp hqQ
      have hk_eq : k = (y⁻¹ * k * y) * (y⁻¹ * q * y) := by
        calc k = y⁻¹ * (y * k * y⁻¹) * y := by group
          _ = y⁻¹ * (k * q) * y := by rw [hyq]
          _ = (y⁻¹ * k * y) * (y⁻¹ * q * y) := by group
      have hk'eq : y⁻¹ * k * y = k * (y⁻¹ * q * y)⁻¹ := by
        conv_rhs => rw [hk_eq]
        group
      rw [hk'eq]
      exact (A ⊔ Q).mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right (Q.inv_mem hq'))
    have hpow : y⁻¹ * k ^ m * y ∈ A ⊔ Q := by
      have e : y⁻¹ * k ^ m * y = (y⁻¹ * k * y) ^ m := by
        simpa [MulAut.conj_apply] using (map_zpow (MulAut.conj y⁻¹) k m)
      rw [e]
      exact (A ⊔ Q).zpow_mem hk' m
    exact (A ⊔ Q).mul_mem hd' hpow
  have hyinv_sup_le : ∀ x ∈ A ⊔ Q, y⁻¹ * x * y ∈ A ⊔ Q := by
    intro x hx
    have hx' : x ∈ (A : Set G) * (Q : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A Q hAQ]
      exact hx
    obtain ⟨a, ha, q0, hq0, rfl⟩ := hx'
    have h1 : y⁻¹ * (a * q0) * y = (y⁻¹ * a * y) * (y⁻¹ * q0 * y) := by group
    rw [h1]
    exact (A ⊔ Q).mul_mem (hyinv_A_le a ha)
      (Subgroup.mem_sup_right (by
        simpa using (Subgroup.mem_normalizer_iff.mp hyQinv q0).mp hq0))
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hy_sup_le x hx
  · intro x hx
    have h := hyinv_sup_le x hx
    have hmem : (MulAut.conj y) (y⁻¹ * x * y) ∈
        (A ⊔ Q).map (MulAut.conj y).toMonoidHom := Subgroup.mem_map_of_mem _ h
    rwa [show (MulAut.conj y) (y⁻¹ * x * y) = x by
      simp [MulAut.conj_apply]; group] at hmem

private theorem exists_conj_k_eq_mul_of_a7Rep {A K S Q : Subgroup G} {k y : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hk : k ∈ A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hQdef : Q = CFSG.Open.pCoreOf 2 (K ⊔ S))
    (hck : ∀ x ∈ K ⊔ S, k * x * k⁻¹ * x⁻¹ ∈ Q)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {σ : Equiv.Perm (Fin 7)} (hyK : y ∈ K)
    (hρy : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
      ⟨y, Subgroup.le_normalizer hyK⟩ = σ) :
    ∃ q ∈ Q, y * k * y⁻¹ = k * q := by
  classical
  let N := Subgroup.normalizer (K : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
  have hAKS : A ≤ Subgroup.normalizer ((K ⊔ S : Subgroup G) : Set G) :=
    fun a ha => Subgroup.inf_normalizer_le_normalizer_sup K S ⟨hAK ha, hAS ha⟩
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]
    exact hAKS.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ S))
  have hQn : K ⊔ S ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ S)
  have hOQ : CFSG.Open.pCoreOf 2 K ≤ Q := by
    rw [hQdef]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hSK).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
  have hkQ : ρ ⟨k, hAK hk⟩ = 1 := by
    rw [CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_eq_one_iff]
    change ∀ z ∈ K, k * z * k⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 K
    intro z hz
    have hmemK : k * z * k⁻¹ * z⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAK hk) z).mp hz) (K.inv_mem hz)
    have hmemQ : k * z * k⁻¹ * z⁻¹ ∈ Q := hck z (Subgroup.mem_sup_left hz)
    exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (le_sup_left : K ≤ K ⊔ S)
      ⟨hmemK, by simpa [hQdef] using hmemQ⟩
  have hcommK : y * k * y⁻¹ * k⁻¹ ∈ K := by
    have h1 : k * y⁻¹ * k⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hAK hk) y⁻¹).mp (K.inv_mem hyK)
    simpa [mul_assoc] using K.mul_mem hyK h1
  have hquot : ρ ⟨y * k * y⁻¹ * k⁻¹, Subgroup.le_normalizer hcommK⟩ = 1 := by
    have e : (⟨y * k * y⁻¹ * k⁻¹, Subgroup.le_normalizer hcommK⟩ : ↥N) =
        ⟨y, Subgroup.le_normalizer hyK⟩ * ⟨k, hAK hk⟩ *
          ⟨y, Subgroup.le_normalizer hyK⟩⁻¹ * ⟨k, hAK hk⟩⁻¹ := Subtype.ext (by simp)
    rw [e]
    simp only [map_mul, map_inv, hρy, hkQ]
    group
  have hcommQ : y * k * y⁻¹ * k⁻¹ ∈ Q :=
    hOQ ((a7Rep_eq_one_iff_mem_pCoreOf φ hcommK).mp hquot)
  have hyQ : y ∈ Subgroup.normalizer (Q : Set G) := hQn (Subgroup.mem_sup_left hyK)
  have hyQinv : y⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q : Set G)).inv_mem hyQ
  refine ⟨k⁻¹ * (y * k * y⁻¹ * k⁻¹) * k, ?_, ?_⟩
  · simpa using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (Q : Set G)).inv_mem (hAQ hk)) _).mp hcommQ
  · calc y * k * y⁻¹ = (y * k * y⁻¹ * k⁻¹) * k := by group
      _ = k * (k⁻¹ * (y * k * y⁻¹ * k⁻¹) * k) := by group

theorem exists_lift_of_a7 {A K S : Subgroup G} {k : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hk : k ∈ A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hQS : CFSG.Open.pCoreOf 2 (K ⊔ S) ≤ S)
    (hck : ∀ x ∈ K ⊔ S, k * x * k⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S))
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ alternatingGroup (Fin 7))
    (hσP : σ ∈ Subgroup.normalizer ((((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) : Subgroup (Equiv.Perm (Fin 7))) :
        Set (Equiv.Perm (Fin 7)))) :
    ∃ x ∈ K ⊔ S, ∃ hxK : x ∈ Subgroup.normalizer (K : Set G),
      x ∈ Subgroup.normalizer (A : Set G) ∧
      x * k = k * x ∧ CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨x, hxK⟩ = σ ∧
      (σ ∈ Subgroup.normalizer (((S.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) : Subgroup (Equiv.Perm (Fin 7))) :
          Set (Equiv.Perm (Fin 7))) →
        x ∈ Subgroup.normalizer (S : Set G)) := by
  classical
  let Q := CFSG.Open.pCoreOf 2 (K ⊔ S)
  let N := Subgroup.normalizer (K : Set G)
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
  let D := A ⊓ K
  let P : Subgroup (Equiv.Perm (Fin 7)) := (D.subgroupOf N).map ρ
  let V : Subgroup (Equiv.Perm (Fin 7)) := (S.subgroupOf N).map ρ
  have hZN : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    (CFSG.RankThree.PartTwo.KFacts.KS14.a7_facts _ ⟨φ⟩).2.1
  obtain ⟨y₀, hy₀K, hy₀⟩ : ∃ y : G, ∃ hyK : y ∈ K,
      ρ ⟨y, Subgroup.le_normalizer hyK⟩ = σ := by
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) (φ.symm ⟨σ, hσ⟩)
    refine ⟨y, y.2, ?_⟩
    rw [CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_of_mem]
    have hy' : φ (y : ↥K ⧸ CFSG.pCore 2 ↥K) = ⟨σ, hσ⟩ := by
      have := congrArg φ hy
      simpa using this
    simp [hy']
  have hAKS : A ≤ Subgroup.normalizer ((K ⊔ S : Subgroup G) : Set G) :=
    fun a ha => Subgroup.inf_normalizer_le_normalizer_sup K S ⟨hAK ha, hAS ha⟩
  have hQn : K ⊔ S ≤ Subgroup.normalizer (Q : Set G) := by
    change K ⊔ S ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ S) : Set G)
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ S)
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := by
    change A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ S) : Set G)
    exact hAKS.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ S))
  have hOQ : CFSG.Open.pCoreOf 2 K ≤ Q := by
    change CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 (K ⊔ S)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hSK).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
  have hy₀Q : y₀ ∈ Subgroup.normalizer (Q : Set G) :=
    hQn (Subgroup.mem_sup_left hy₀K)
  have hy₀AQ : y₀ ∈ Subgroup.normalizer ((A ⊔ Q : Subgroup G) : Set G) :=
    y0_mem_normalizer_sup_of_a7Rep hA hk hAK hAS hSK rfl (by exact hck) hAk φ hy₀K hy₀
      (by simpa [P, D, N, ρ] using hσP)
  have hQ2 : IsPGroup 2 Q := hS.to_le hQS
  have hpQ : Nat.Coprime (Nat.card Q) 3 := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ2
    rw [hm]
    exact Nat.Coprime.pow_left m (by decide : Nat.Coprime 2 3)
  obtain ⟨q, hqQ, hqx⟩ :=
    exists_mul_mem_normalizer_of_mem_normalizer_sup (p := 3)
      (CFSG.Open.IsElemAbelian.isPGroup hA) hpQ hAQ hy₀Q hy₀AQ
  let x := q * y₀
  have hqK : q ∈ Subgroup.normalizer (K : Set G) := hSK (hQS hqQ)
  have hxK : x ∈ Subgroup.normalizer (K : Set G) :=
    N.mul_mem hqK (Subgroup.le_normalizer hy₀K)
  have hxKS : x ∈ K ⊔ S :=
    (K ⊔ S).mul_mem (Subgroup.mem_sup_right (hQS hqQ)) (Subgroup.mem_sup_left hy₀K)
  have hqρ : ρ ⟨q, hqK⟩ = 1 := by
    rw [CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_eq_one_iff]
    change ∀ z ∈ K, q * z * q⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 K
    intro z hz
    have hmemK : q * z * q⁻¹ * z⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp hqK z).mp hz) (K.inv_mem hz)
    have hconjQ : z * q * z⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hQn (Subgroup.mem_sup_left hz)) q).mp hqQ
    have hmemQ : q * z * q⁻¹ * z⁻¹ ∈ Q := by
      have e : q * z * q⁻¹ * z⁻¹ = q * (z * q * z⁻¹)⁻¹ := by group
      rw [e]
      exact Q.mul_mem hqQ (Q.inv_mem hconjQ)
    exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (le_sup_left : K ≤ K ⊔ S)
      ⟨hmemK, by simpa using hmemQ⟩
  have hxρ : ρ ⟨x, hxK⟩ = σ := by
    have e : (⟨x, hxK⟩ : ↥N) = ⟨q, hqK⟩ * ⟨y₀, Subgroup.le_normalizer hy₀K⟩ :=
      Subtype.ext rfl
    rw [e, map_mul, hqρ, hy₀, one_mul]
  obtain ⟨q₀, hq₀Q, hy₀k⟩ :=
    exists_conj_k_eq_mul_of_a7Rep hA hk hAK hAS hSK rfl hck φ hy₀K hy₀
  have hqkQ : (k⁻¹ * q * k) * q⁻¹ ∈ Q := by
    have h1 : k⁻¹ * q * k ∈ Q := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Q : Set G)).inv_mem (hAQ hk)) q).mp hqQ
    exact Q.mul_mem h1 (Q.inv_mem hqQ)
  have hqq₀Q : q * q₀ * q⁻¹ ∈ Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hqQ) q₀).mp hq₀Q
  obtain ⟨q₁, hq₁Q, hxconj⟩ : ∃ q₁ ∈ Q, x * k * x⁻¹ = k * q₁ := by
    refine ⟨((k⁻¹ * q * k) * q⁻¹) * (q * q₀ * q⁻¹), Q.mul_mem hqkQ hqq₀Q, ?_⟩
    calc x * k * x⁻¹ = q * (y₀ * k * y₀⁻¹) * q⁻¹ := by simp [x]; group
      _ = q * (k * q₀) * q⁻¹ := by rw [hy₀k]
      _ = k * (((k⁻¹ * q * k) * q⁻¹) * (q * q₀ * q⁻¹)) := by group
  have hkxA : x * k * x⁻¹ * k⁻¹ ∈ A :=
    A.mul_mem ((Subgroup.mem_normalizer_iff.mp hqx k).mp hk) (A.inv_mem hk)
  have hkxQ : x * k * x⁻¹ * k⁻¹ ∈ Q := by
    have h := (Subgroup.mem_normalizer_iff.mp (hAQ hk) q₁).mp hq₁Q
    rw [hxconj]
    simpa [mul_assoc] using h
  have hcopAQ : Nat.Coprime (Nat.card A) (Nat.card Q) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) A Q (CFSG.Open.IsElemAbelian.isPGroup hA) hQ2
  have hdisj : Disjoint A Q := Subgroup.disjoint_of_coprime_natCard hcopAQ
  have hkx1 : x * k * x⁻¹ * k⁻¹ = 1 := by
    have hmem : x * k * x⁻¹ * k⁻¹ ∈ A ⊓ Q := ⟨hkxA, hkxQ⟩
    rwa [disjoint_iff.mp hdisj, Subgroup.mem_bot] at hmem
  have hxk : x * k = k * x := by
    apply mul_inv_eq_one.mp
    simpa [mul_inv_rev, mul_assoc] using hkx1
  have hker : ∀ z ∈ K ⊔ S, ∀ hzN : z ∈ N, ρ ⟨z, hzN⟩ = 1 → z ∈ Q := by
    intro z hz hzN h1
    have hcomm : ∀ y ∈ K, z * y * z⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) := by
      intro y hy
      exact hOQ ((CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_eq_one_iff K φ
        ⟨z, hzN⟩).mp h1 y hy)
    exact mem_pCoreOf_sup_of_commutator_mem hS hSK hZN hz hcomm
  have hy₀S_of (hσV : σ ∈ Subgroup.normalizer (V : Set (Equiv.Perm (Fin 7)))) :
      y₀ ∈ Subgroup.normalizer (S : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    have hsN : s ∈ N := hSK hs
    have hmemKS : y₀ * s * y₀⁻¹ ∈ K ⊔ S :=
      (K ⊔ S).mul_mem ((K ⊔ S).mul_mem (Subgroup.mem_sup_left hy₀K)
        (Subgroup.mem_sup_right hs)) ((K ⊔ S).inv_mem (Subgroup.mem_sup_left hy₀K))
    have hmemN : y₀ * s * y₀⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (Subgroup.le_normalizer hy₀K) hsN)
        (N.inv_mem (Subgroup.le_normalizer hy₀K))
    have hρmem : ρ ⟨y₀ * s * y₀⁻¹, hmemN⟩ ∈ V := by
      have e : (⟨y₀ * s * y₀⁻¹, hmemN⟩ : ↥N) =
          ⟨y₀, Subgroup.le_normalizer hy₀K⟩ * ⟨s, hsN⟩ *
            ⟨y₀, Subgroup.le_normalizer hy₀K⟩⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_mul, map_inv, hy₀]
      have hsV : ρ ⟨s, hsN⟩ ∈ V :=
        Subgroup.mem_map.mpr ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hσV _).mp hsV
    have hρmem' : ρ ⟨y₀ * s * y₀⁻¹, hmemN⟩ ∈ (S.subgroupOf N).map ρ := by
      simpa [V] using hρmem
    obtain ⟨s', hs'D, hs'eq⟩ := Subgroup.mem_map.mp hρmem'
    have hs'S : (s' : G) ∈ S := Subgroup.mem_subgroupOf.mp hs'D
    have hmemKS2 : (s' : G)⁻¹ * (y₀ * s * y₀⁻¹) ∈ K ⊔ S :=
      (K ⊔ S).mul_mem ((K ⊔ S).inv_mem (Subgroup.mem_sup_right hs'S)) hmemKS
    have hmemN2 : (s' : G)⁻¹ * (y₀ * s * y₀⁻¹) ∈ N :=
      N.mul_mem (N.inv_mem (hSK hs'S)) hmemN
    have hquot : ρ ⟨(s' : G)⁻¹ * (y₀ * s * y₀⁻¹), hmemN2⟩ = 1 := by
      have e : (⟨(s' : G)⁻¹ * (y₀ * s * y₀⁻¹), hmemN2⟩ : ↥N) =
          (s')⁻¹ * ⟨y₀ * s * y₀⁻¹, hmemN⟩ := Subtype.ext rfl
      rw [e, map_mul, map_inv, hs'eq, inv_mul_cancel]
    have hmemQ : (s' : G)⁻¹ * (y₀ * s * y₀⁻¹) ∈ Q := hker _ hmemKS2 hmemN2 hquot
    have hmemS : (s' : G)⁻¹ * (y₀ * s * y₀⁻¹) ∈ S := hQS hmemQ
    have heq : y₀ * s * y₀⁻¹ = (s' : G) * ((s' : G)⁻¹ * (y₀ * s * y₀⁻¹)) := by group
    rw [heq]
    exact S.mul_mem hs'S hmemS
  refine ⟨x, hxKS, hxK, hqx, hxk, hxρ, ?_⟩
  intro hσV'
  have hqS : q ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer (hQS hqQ)
  have hy₀S : y₀ ∈ Subgroup.normalizer (S : Set G) :=
    hy₀S_of (by simpa [V, N, ρ] using hσV')
  exact (Subgroup.normalizer (S : Set G)).mul_mem hqS hy₀S

end CFSG.RankThree.PartTwo.Sec16
