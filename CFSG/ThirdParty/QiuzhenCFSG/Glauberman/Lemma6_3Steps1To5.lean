module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.PStableIso
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.MinimalNormalPCoreCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.CentralizerInfPCorePreimageIsPGroup
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.QuotientConjugationSquareZero

import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_1

namespace CFSG
end CFSG
open CFSG

/-!
# Glauberman Lemma 6.3, Steps 1–5

This module contains the minimal-counterexample reduction through the
construction of two quadratic generators of `Q / C_Q(H)`.  It deliberately
stops before Lemma 6.2, so the public endpoint can feed the aligned Step-6
classification theorem while retaining the original conjugation
representation and evaluation equation.
-/

noncomputable section

namespace CFSG.Glauberman

universe u

open scoped Pointwise commutatorElement IsMulCommutative

private theorem minimal_bad_core_ne_bot_and_not_local {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hbad : ¬ pStable p Q)
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B)) :
    pCore p Q ≠ ⊥ ∧ ¬ pStableLocal p Q := by
  classical
  have hexM : ∃ M : Subgroup Q, M ∈ MpSet p Q ∧ ¬ pStableLocal p (G := ↥M) := by
    by_contra h
    apply hbad
    intro M hM
    by_contra hlocal
    exact h ⟨M, hM, hlocal⟩
  rcases hexM with ⟨M, hM, hMlocal⟩
  have hMtop : M = ⊤ := by
    by_contra hMne
    have hMlt : M < (⊤ : Subgroup Q) := lt_top_iff_ne_top.mpr hMne
    have hMcard : Nat.card M < Nat.card Q := by
      simpa using natCard_lt_of_subgroup_lt hMlt
    have hMquotcard : Nat.card (M ⧸ (⊥ : Subgroup M)) < Nat.card Q := by
      calc
        Nat.card (M ⧸ (⊥ : Subgroup M)) = Nat.card M :=
          Nat.card_congr (QuotientGroup.quotientBot (G := ↥M)).toEquiv
        _ < Nat.card Q := hMcard
    have hMquotstable : pStable p (M ⧸ (⊥ : Subgroup M)) :=
      hmin M (⊥ : Subgroup M) hMquotcard
    have hMstable : pStable p ↥M :=
      (pStable_iso (QuotientGroup.quotientBot (G := ↥M))).mp hMquotstable
    exact hMlocal (pStableLocal_of_core_ne_bot (G := ↥M) p hMstable hM.1)
  subst M
  constructor
  · intro hcore
    apply hM.1
    have hmap := pCore_map_iso (G := ↥(⊤ : Subgroup Q)) (G' := Q) (p := p)
      (f := (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q))
    apply (Subgroup.map_eq_bot_iff_of_injective
      (H := pCore p ↥(⊤ : Subgroup Q))
      (f := (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom)
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).injective).mp
    simpa [hcore] using hmap
  · intro hlocal
    apply hMlocal
    exact (pStableLocal_congr (p := p)
      (e := (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q))).mpr hlocal

private theorem exists_local_instability_witness {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (hnotlocal : ¬ pStableLocal p Q) :
    ∃ H : Subgroup Q,
      IsPGroup p H ∧
        (pPrimeCore p Q ⊔ H).Normal ∧
          ∃ (x : Q) (hx : x ∈ Subgroup.normalizer (H : Set Q)),
            ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ ∧
              QuotientGroup.mk'
                ((Subgroup.centralizer (H : Set Q)).subgroupOf
                  (Subgroup.normalizer (H : Set Q))) ⟨x, hx⟩ ∉
                pCore p ((Subgroup.normalizer (H : Set Q)) ⧸
                  (Subgroup.centralizer (H : Set Q)).subgroupOf
                    (Subgroup.normalizer (H : Set Q))) := by
  rw [pStableLocal] at hnotlocal
  push Not at hnotlocal
  exact hnotlocal

private def LocalBad (p : ℕ) [Fact p.Prime] (Q : Type u) [Group Q]
    (H : Subgroup Q) : Prop :=
  IsPGroup p H ∧
    (pPrimeCore p Q ⊔ H).Normal ∧
      ∃ (x : Q) (hx : x ∈ Subgroup.normalizer (H : Set Q)),
        ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ ∧
          QuotientGroup.mk'
            ((Subgroup.centralizer (H : Set Q)).subgroupOf
              (Subgroup.normalizer (H : Set Q))) ⟨x, hx⟩ ∉
            pCore p ((Subgroup.normalizer (H : Set Q)) ⧸
              (Subgroup.centralizer (H : Set Q)).subgroupOf
                (Subgroup.normalizer (H : Set Q)))

private theorem exists_minimal_local_instability_witness {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (hnotlocal : ¬ pStableLocal p Q) :
    ∃ H : Subgroup Q, LocalBad p Q H ∧
      ∀ K : Subgroup Q, Nat.card K < Nat.card H → ¬ LocalBad p Q K := by
  classical
  have hexH : ∃ H : Subgroup Q, LocalBad p Q H := by
    rcases exists_local_instability_witness hnotlocal with
      ⟨H, hHp, hnorm, x, hx, hcomm, hout⟩
    exact ⟨H, hHp, hnorm, x, hx, hcomm, hout⟩
  let BadCard : ℕ → Prop := fun n =>
    ∃ H : Subgroup Q, Nat.card H = n ∧ LocalBad p Q H
  have hBadCard : ∃ n, BadCard n := by
    rcases hexH with ⟨H, hH⟩
    exact ⟨Nat.card H, H, rfl, hH⟩
  rcases Nat.find_spec hBadCard with ⟨H, hHcard, hHbad⟩
  refine ⟨H, hHbad, ?_⟩
  intro K hKcard hKbad
  have hKentry : BadCard (Nat.card K) := ⟨K, rfl, hKbad⟩
  have hfind_le : Nat.find hBadCard ≤ Nat.card K :=
    Nat.find_min' hBadCard hKentry
  have hfind_eq : Nat.find hBadCard = Nat.card H := hHcard.symm
  rw [hfind_eq] at hfind_le
  exact (not_le_of_gt hKcard) hfind_le

private theorem relIndex_sup_eq_relIndex_inf {G : Type u} [Group G]
    [Finite G] {H K : Subgroup G}
    (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    H.relIndex (H ⊔ K) = (H ⊓ K).relIndex K := by
  have hKrel : K.relIndex (H ⊔ K) = (H ⊓ K).relIndex H := by
    let NG : Subgroup G := Subgroup.normalizer (K : Set G)
    have hHleNG : H ≤ NG := hK
    have hKleNG : K ≤ NG := Subgroup.le_normalizer
    have hHKleNG : H ⊔ K ≤ NG := sup_le hHleNG hKleNG
    let : (K.subgroupOf NG).Normal := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := K) (K := NG) hKleNG).2 le_rfl
    calc
      K.relIndex (H ⊔ K) =
          (K.subgroupOf NG).relIndex ((H ⊔ K).subgroupOf NG) := by
            exact (Subgroup.relIndex_subgroupOf
              (H := K) (K := H ⊔ K) (L := NG) hHKleNG).symm
      _ = (K.subgroupOf NG).relIndex
          ((H.subgroupOf NG) ⊔ (K.subgroupOf NG)) := by
            rw [Subgroup.subgroupOf_sup
              (A := H) (A' := K) (B := NG) hHleNG hKleNG]
      _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex
          (H.subgroupOf NG) := by
            calc
              (K.subgroupOf NG).relIndex
                    ((H.subgroupOf NG) ⊔ (K.subgroupOf NG)) =
                  (K.subgroupOf NG).relIndex (H.subgroupOf NG) := by
                    exact Subgroup.relIndex_sup_right
                      (H := H.subgroupOf NG) (K := K.subgroupOf NG)
              _ = ((H.subgroupOf NG) ⊓ (K.subgroupOf NG)).relIndex
                    (H.subgroupOf NG) := by
                    symm
                    exact Subgroup.inf_relIndex_left
                      (H := H.subgroupOf NG) (K := K.subgroupOf NG)
      _ = ((H ⊓ K).subgroupOf NG).relIndex (H.subgroupOf NG) := by
            rw [show (H.subgroupOf NG) ⊓ (K.subgroupOf NG) =
                (H ⊓ K).subgroupOf NG by
              ext x
              simp [Subgroup.mem_subgroupOf]]
      _ = (H ⊓ K).relIndex H := by
            exact Subgroup.relIndex_subgroupOf
              (H := H ⊓ K) (K := H) (L := NG) hHleNG
  have hmul :
      (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
        (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by
    calc
      (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
          (H ⊓ K).relIndex (H ⊔ K) := by
            exact Subgroup.relIndex_mul_relIndex
              (H := H ⊓ K) (K := H) (L := H ⊔ K) inf_le_left le_sup_left
      _ = (H ⊓ K).relIndex K * K.relIndex (H ⊔ K) := by
            symm
            exact Subgroup.relIndex_mul_relIndex
              (H := H ⊓ K) (K := K) (L := H ⊔ K) inf_le_right le_sup_right
      _ = (H ⊓ K).relIndex K * (H ⊓ K).relIndex H := by rw [hKrel]
  have hpos : 0 < (H ⊓ K).relIndex H := by
    have hne : (H ⊓ K).relIndex H ≠ 0 := by
      dsimp [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
        (H := (H ⊓ K).subgroupOf H)
    exact Nat.pos_of_ne_zero hne
  have hmul' :
      (H ⊓ K).relIndex H * H.relIndex (H ⊔ K) =
        (H ⊓ K).relIndex H * (H ⊓ K).relIndex K := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact Nat.eq_of_mul_eq_mul_left hpos hmul'

private theorem exists_sylow_sup_pPrimeCore {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHp : IsPGroup p H) :
    let M : Subgroup Q := pPrimeCore p Q
    let L : Subgroup Q := M ⊔ H
    ∃ P : Sylow p ↥L, (P : Subgroup ↥L).map L.subtype = H := by
  classical
  dsimp only
  let M : Subgroup Q := pPrimeCore p Q
  let L : Subgroup Q := M ⊔ H
  have hHleL : H ≤ L := le_sup_right
  let T : Subgroup ↥L := H.subgroupOf L
  have hTp : IsPGroup p T :=
    hHp.of_equiv (Subgroup.subgroupOfEquivOfLe hHleL).symm
  have hcop : Nat.Coprime (Nat.card H) (Nat.card M) := by
    rcases IsPGroup.iff_card.mp hHp with ⟨a, ha⟩
    rw [ha]
    exact (pPrimeCore_coprime_card (G := Q) (p := p)).pow_left a
  have hinf : H ⊓ M = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hHleNM : H ≤ Subgroup.normalizer (M : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr
      (show M.Normal by dsimp [M]; infer_instance)]
    exact le_top
  have hrel : H.relIndex L = (H ⊓ M).relIndex M := by
    simpa [L, sup_comm] using
      (relIndex_sup_eq_relIndex_inf (H := H) (K := M) hHleNM)
  have hTindex : T.index = H.relIndex L := by rfl
  have hnotM : ¬ p ∣ Nat.card M := by
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (G := Q) (p := p))
  have hnotT : ¬ p ∣ T.index := by
    rw [hTindex, hrel, hinf, Subgroup.relIndex_bot_left]
    exact hnotM
  let P : Sylow p ↥L := IsPGroup.toSylow hTp hnotT
  refine ⟨P, ?_⟩
  change T.map L.subtype = H
  exact Subgroup.map_subgroupOf_eq_of_le hHleL

private theorem pPrimeCore_sup_normalizer_eq_top {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHp : IsPGroup p H)
    (hnorm : (pPrimeCore p Q ⊔ H).Normal) :
    pPrimeCore p Q ⊔ Subgroup.normalizer (H : Set Q) = ⊤ := by
  classical
  let M : Subgroup Q := pPrimeCore p Q
  let L : Subgroup Q := M ⊔ H
  let : L.Normal := by simpa [L, M] using hnorm
  obtain ⟨P, hPmap⟩ := exists_sylow_sup_pPrimeCore (p := p) H hHp
  have hfr : Subgroup.normalizer (H : Set Q) ⊔ L = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (G := Q) (N := L) P
    change Subgroup.normalizer
      (((P : Subgroup ↥L).map L.subtype : Subgroup Q) : Set Q) ⊔ L = ⊤ at h
    rw [hPmap] at h
    exact h
  calc
    M ⊔ Subgroup.normalizer (H : Set Q) =
        (M ⊔ H) ⊔ Subgroup.normalizer (H : Set Q) := by
          rw [sup_assoc, sup_eq_right.mpr
            (Subgroup.le_normalizer : H ≤ Subgroup.normalizer (H : Set Q))]
    _ = L ⊔ Subgroup.normalizer (H : Set Q) := by rfl
    _ = ⊤ := by simpa [sup_comm] using hfr

private theorem quotient_centralizer_inf_normalizer_eq
    {Q : Type u} [Group Q]
    (M H : Subgroup Q) [M.Normal] (hinf : H ⊓ M = ⊥) :
    let q : Q →* Q ⧸ M := QuotientGroup.mk' M
    let C : Subgroup Q :=
      (Subgroup.centralizer ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M))).comap q
    C ⊓ Subgroup.normalizer (H : Set Q) = Subgroup.centralizer (H : Set Q) := by
  classical
  dsimp only
  let q : Q →* Q ⧸ M := QuotientGroup.mk' M
  let C : Subgroup Q :=
    (Subgroup.centralizer ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M))).comap q
  apply le_antisymm
  · intro x hx
    have hxC : q x ∈ Subgroup.centralizer
        ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M)) := hx.1
    have hxN : x ∈ Subgroup.normalizer (H : Set Q) := hx.2
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hqh : q h ∈ H.map q := Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    have hqcomm : q h * q x = q x * q h :=
      Subgroup.mem_centralizer_iff.mp hxC (q h) hqh
    have hqone : q (h * x * h⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hqcomm]
      group
    have hM : h * x * h⁻¹ * x⁻¹ ∈ M :=
      (QuotientGroup.eq_one_iff (N := M)
        (x := h * x * h⁻¹ * x⁻¹)).mp hqone
    have hHconj : x * h⁻¹ * x⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp hxN h⁻¹).mp (H.inv_mem hh)
    have hH : h * x * h⁻¹ * x⁻¹ ∈ H := by
      simpa [mul_assoc] using H.mul_mem hh hHconj
    have hbot : h * x * h⁻¹ * x⁻¹ ∈ (⊥ : Subgroup Q) := by
      rw [← hinf]
      exact ⟨hH, hM⟩
    have hone : h * x * h⁻¹ * x⁻¹ = 1 := by simpa using hbot
    calc
      h * x = (h * x * h⁻¹ * x⁻¹) * (x * h) := by group
      _ = x * h := by rw [hone]; simp
  · intro x hx
    refine ⟨?_, Subgroup.centralizer_le_normalizer (H : Set Q) hx⟩
    change q x ∈ Subgroup.centralizer
      ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨h, hh, rfl⟩
    exact congrArg q (Subgroup.mem_centralizer_iff.mp hx h hh)

private theorem quotient_centralizer_eq_sup
    {Q : Type u} [Group Q]
    (M H : Subgroup Q) [M.Normal]
    (hinf : H ⊓ M = ⊥)
    (hMN : M ⊔ Subgroup.normalizer (H : Set Q) = ⊤) :
    let q : Q →* Q ⧸ M := QuotientGroup.mk' M
    let C : Subgroup Q :=
      (Subgroup.centralizer ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M))).comap q
    C = M ⊔ Subgroup.centralizer (H : Set Q) := by
  classical
  dsimp only
  let q : Q →* Q ⧸ M := QuotientGroup.mk' M
  let C : Subgroup Q :=
    (Subgroup.centralizer ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M))).comap q
  have hMC : M ≤ C := by
    intro m hm
    change q m ∈ Subgroup.centralizer
      ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M))
    have hqm : q m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    rw [hqm]
    exact (Subgroup.centralizer
      ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M))).one_mem
  have hCN : C ⊓ Subgroup.normalizer (H : Set Q) =
      Subgroup.centralizer (H : Set Q) := by
    exact quotient_centralizer_inf_normalizer_eq M H hinf
  have hmod : C ⊓ (M ⊔ Subgroup.normalizer (H : Set Q)) =
      M ⊔ (C ⊓ Subgroup.normalizer (H : Set Q)) := by
    apply le_antisymm
    · intro x hx
      have hxC : x ∈ C := hx.1
      rcases (Subgroup.mem_sup_of_normal_left
        (s := M) (t := Subgroup.normalizer (H : Set Q)) (x := x)).mp hx.2 with
        ⟨m, hm, n, hn, hmn⟩
      have hmC : m ∈ C := hMC hm
      have hnC : n ∈ C := by
        have hprod := C.mul_mem (C.inv_mem hmC) hxC
        have heq : m⁻¹ * x = n := by rw [← hmn]; group
        rwa [heq] at hprod
      have hmSup : m ∈ M ⊔ (C ⊓ Subgroup.normalizer (H : Set Q)) :=
        (le_sup_left :
          M ≤ M ⊔ (C ⊓ Subgroup.normalizer (H : Set Q))) hm
      have hnSup : n ∈ M ⊔ (C ⊓ Subgroup.normalizer (H : Set Q)) :=
        (le_sup_right :
          C ⊓ Subgroup.normalizer (H : Set Q) ≤
            M ⊔ (C ⊓ Subgroup.normalizer (H : Set Q))) ⟨hnC, hn⟩
      have hprod :=
        (M ⊔ (C ⊓ Subgroup.normalizer (H : Set Q))).mul_mem hmSup hnSup
      rwa [hmn] at hprod
    · intro x hx
      have hleC : M ⊔ (C ⊓ Subgroup.normalizer (H : Set Q)) ≤ C :=
        sup_le hMC inf_le_left
      have hleMN : M ⊔ (C ⊓ Subgroup.normalizer (H : Set Q)) ≤
          M ⊔ Subgroup.normalizer (H : Set Q) :=
        sup_le le_sup_left (le_trans inf_le_right le_sup_right)
      exact ⟨hleC hx, hleMN hx⟩
  calc
    C = C ⊓ (⊤ : Subgroup Q) := by simp
    _ = C ⊓ (M ⊔ Subgroup.normalizer (H : Set Q)) := by rw [hMN]
    _ = M ⊔ (C ⊓ Subgroup.normalizer (H : Set Q)) := hmod
    _ = M ⊔ Subgroup.centralizer (H : Set Q) := by rw [hCN]

private theorem quotient_local_instability {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHp : IsPGroup p H)
    (hnorm : (pPrimeCore p Q ⊔ H).Normal)
    (x : Q) (hx : x ∈ Subgroup.normalizer (H : Set Q))
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hout :
      QuotientGroup.mk'
          ((Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q))) ⟨x, hx⟩ ∉
        pCore p ((Subgroup.normalizer (H : Set Q)) ⧸
          (Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q)))) :
    ¬ pStableLocal p (Q ⧸ pPrimeCore p Q) := by
  classical
  let M : Subgroup Q := pPrimeCore p Q
  let q : Q →* Q ⧸ M := QuotientGroup.mk' M
  let Hbar : Subgroup (Q ⧸ M) := H.map q
  let N : Subgroup Q := Subgroup.normalizer (H : Set Q)
  let C0 : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let Nbar : Subgroup (Q ⧸ M) := Subgroup.normalizer (Hbar : Set (Q ⧸ M))
  let Cbar : Subgroup (Q ⧸ M) := Subgroup.centralizer (Hbar : Set (Q ⧸ M))
  have hMnormal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hMnormal
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := Q) (p := p))
  let : Fact (IsPGroup p H) := ⟨hHp⟩
  have hNmap : Nbar = N.map q := by
    simpa [Nbar, N, Hbar, q] using
      (normalizer_map_quotient_eq_map_normalizer
        (G := Q) (p := p) H M hMnormal hcop)
  have hCmap : Cbar = C0.map q := by
    simpa [Cbar, C0, Hbar, q] using
      (centralizer_map_quotient_eq_map_centralizer
        (G := Q) (p := p) H M hMnormal hcop)
  have hHbarp : IsPGroup p Hbar := by
    exact IsPGroup.map (p := p) (H := H) hHp q
  have hHbarNormal : Hbar.Normal := by
    have hmapNormal : ((M ⊔ H).map q).Normal :=
      Subgroup.Normal.map hnorm q hqsurj
    have hmapEq : (M ⊔ H).map q = Hbar := by
      rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    rw [← hmapEq]
    exact hmapNormal
  have hquotCore : pPrimeCore p (Q ⧸ M) = ⊥ := by
    simpa [M] using
      (pPrimeCore_quotient_pPrimeCore_eq_bot (G := Q) (p := p))
  have hHbarCondition : (pPrimeCore p (Q ⧸ M) ⊔ Hbar).Normal := by
    rw [hquotCore, bot_sup_eq]
    exact hHbarNormal
  let xbar : Q ⧸ M := q x
  have hxbar : xbar ∈ Nbar := by
    rw [hNmap]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hcommbar :
      ⁅⁅Hbar, Subgroup.zpowers xbar⁆, Subgroup.zpowers xbar⁆ = ⊥ := by
    have hmap := congrArg (fun K : Subgroup Q => K.map q) hcomm
    simpa [Hbar, xbar, Subgroup.map_commutator, MonoidHom.map_zpowers] using hmap
  have hcopHM : Nat.Coprime (Nat.card H) (Nat.card M) := by
    rcases IsPGroup.iff_card.mp hHp with ⟨a, ha⟩
    rw [ha]
    exact hcop.pow_left a
  have hinf : H ⊓ M = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcopHM).eq_bot
  have hpreInf : Cbar.comap q ⊓ N = C0 := by
    simpa [Cbar, C0, Hbar, N, q] using
      (quotient_centralizer_inf_normalizer_eq M H hinf)
  let qN : N →* Nbar :=
    (q.comp N.subtype).codRestrict Nbar (by
      intro n
      rw [hNmap]
      exact Subgroup.mem_map.mpr ⟨(n : Q), n.2, rfl⟩)
  have hqNsurj : Function.Surjective qN := by
    intro y
    have hy : (y : Q ⧸ M) ∈ N.map q := by
      rw [← hNmap]
      exact y.2
    rcases Subgroup.mem_map.mp hy with ⟨n, hn, hny⟩
    refine ⟨⟨n, hn⟩, ?_⟩
    apply Subtype.ext
    simpa [qN] using hny
  let C0N : Subgroup N := C0.subgroupOf N
  let CbarNbar : Subgroup Nbar := Cbar.subgroupOf Nbar
  let theta : N →* Nbar ⧸ CbarNbar :=
    (QuotientGroup.mk' CbarNbar).comp qN
  have hthetaSurj : Function.Surjective theta :=
    (QuotientGroup.mk'_surjective CbarNbar).comp hqNsurj
  have hker : C0N = theta.ker := by
    ext n
    constructor
    · intro hnC0
      change theta n = 1
      apply (QuotientGroup.eq_one_iff (N := CbarNbar) (x := qN n)).2
      change q ((n : N) : Q) ∈ Cbar
      rw [hCmap]
      exact Subgroup.mem_map.mpr
        ⟨((n : N) : Q), Subgroup.mem_subgroupOf.mp hnC0, rfl⟩
    · intro hnker
      have hnCbar : q ((n : N) : Q) ∈ Cbar := by
        apply (QuotientGroup.eq_one_iff (N := CbarNbar) (x := qN n)).1
        exact hnker
      have hnC0 : ((n : N) : Q) ∈ C0 := by
        have hnInf : ((n : N) : Q) ∈ Cbar.comap q ⊓ N :=
          ⟨hnCbar, n.2⟩
        rw [hpreInf] at hnInf
        exact hnInf
      exact Subgroup.mem_subgroupOf.mpr hnC0
  let e : N ⧸ C0N ≃* Nbar ⧸ CbarNbar :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective theta hthetaSurj)
  have he_mk (n : N) :
      e (QuotientGroup.mk' C0N n) = QuotientGroup.mk' CbarNbar (qN n) := by
    rfl
  intro hlocal
  have htarget := hlocal Hbar hHbarp hHbarCondition xbar hxbar hcommbar
  have htarget' : QuotientGroup.mk' CbarNbar ⟨xbar, hxbar⟩ ∈
      pCore p (Nbar ⧸ CbarNbar) := by
    simpa [Nbar, Cbar, CbarNbar] using htarget
  have hcoreMap : (pCore p (N ⧸ C0N)).map e.toMonoidHom =
      pCore p (Nbar ⧸ CbarNbar) :=
    pCore_map_iso (G := N ⧸ C0N) (G' := Nbar ⧸ CbarNbar) (p := p) e
  rw [← hcoreMap] at htarget'
  rcases Subgroup.mem_map.mp htarget' with ⟨z, hz, hzeq⟩
  have he_orig :
      e (QuotientGroup.mk' C0N ⟨x, hx⟩) =
        QuotientGroup.mk' CbarNbar ⟨xbar, hxbar⟩ := by
    simpa [xbar, qN] using he_mk (⟨x, hx⟩ : N)
  have hzorig : z = QuotientGroup.mk' C0N ⟨x, hx⟩ := by
    apply e.injective
    exact hzeq.trans he_orig.symm
  apply hout
  simpa [N, C0, C0N, hzorig] using hz

private def top_quotient_congr {Q : Type u} [Group Q]
    (M : Subgroup Q) [M.Normal] :
    (↥(⊤ : Subgroup Q) ⧸ M.subgroupOf (⊤ : Subgroup Q)) ≃* (Q ⧸ M) := by
  let e : ↥(⊤ : Subgroup Q) ≃* Q := Subgroup.topEquiv
  have he : (M.subgroupOf (⊤ : Subgroup Q)).map e.toMonoidHom = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, by simp⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  exact QuotientGroup.congr
    (G := ↥(⊤ : Subgroup Q)) (H := Q)
    (G' := M.subgroupOf (⊤ : Subgroup Q)) (H' := M) e he

private theorem minimal_pprime_core_reduction {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) (hHbad : LocalBad p Q H) :
    pPrimeCore p Q = ⊥ ∧
      let M : Subgroup Q := pPrimeCore p Q
      let q : Q →* Q ⧸ M := QuotientGroup.mk' M
      let C : Subgroup Q :=
        (Subgroup.centralizer ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M))).comap q
      C = Subgroup.centralizer (H : Set Q) ∧ H.Normal := by
  classical
  rcases hHbad with ⟨hHp, hnorm, x, hx, hcomm, hout⟩
  let M : Subgroup Q := pPrimeCore p Q
  have hMnormal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hMnormal
  have hMbot : M = ⊥ := by
    by_contra hMne
    have hnotlocal : ¬ pStableLocal p (Q ⧸ M) := by
      simpa [M] using
        (quotient_local_instability
          (p := p) H hHp hnorm x hx hcomm hout)
    have hquotlt : Nat.card (Q ⧸ M) < Nat.card Q :=
      natCard_quotient_lt_natCard_of_ne_bot M hMne
    have htopquotlt :
        Nat.card ((⊤ : Subgroup Q) ⧸ M.subgroupOf (⊤ : Subgroup Q)) <
          Nat.card Q := by
      calc
        Nat.card ((⊤ : Subgroup Q) ⧸ M.subgroupOf (⊤ : Subgroup Q)) =
            Nat.card (Q ⧸ M) :=
          Nat.card_congr (top_quotient_congr M).toEquiv
        _ < Nat.card Q := hquotlt
    have hstableTop :
        pStable p ((⊤ : Subgroup Q) ⧸ M.subgroupOf (⊤ : Subgroup Q)) :=
      hmin (⊤ : Subgroup Q) (M.subgroupOf (⊤ : Subgroup Q)) htopquotlt
    have hstableQuot : pStable p (Q ⧸ M) :=
      (pStable_iso (top_quotient_congr M)).mp hstableTop
    let q : Q →* Q ⧸ M := QuotientGroup.mk' M
    let Hbar : Subgroup (Q ⧸ M) := H.map q
    have hHne : H ≠ ⊥ := by
      intro hHbot
      subst H
      apply hout
      have hone :
          QuotientGroup.mk'
              ((Subgroup.centralizer ((⊥ : Subgroup Q) : Set Q)).subgroupOf
                (Subgroup.normalizer ((⊥ : Subgroup Q) : Set Q))) ⟨x, hx⟩ = 1 := by
        apply (QuotientGroup.eq_one_iff
          (N := (Subgroup.centralizer ((⊥ : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((⊥ : Subgroup Q) : Set Q)))
          (x := ⟨x, hx⟩)).2
        apply Subgroup.mem_subgroupOf.mpr
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy1 : y = 1 := by simpa using hy
        subst y
        simp
      rw [hone]
      exact (pCore p
        ((Subgroup.normalizer ((⊥ : Subgroup Q) : Set Q)) ⧸
          (Subgroup.centralizer ((⊥ : Subgroup Q) : Set Q)).subgroupOf
            (Subgroup.normalizer ((⊥ : Subgroup Q) : Set Q)))).one_mem
    have hcop : Nat.Coprime p (Nat.card M) := by
      simpa [M] using (pPrimeCore_coprime_card (G := Q) (p := p))
    have hcopHM : Nat.Coprime (Nat.card H) (Nat.card M) := by
      rcases IsPGroup.iff_card.mp hHp with ⟨a, ha⟩
      rw [ha]
      exact hcop.pow_left a
    have hinf : H ⊓ M = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcopHM).eq_bot
    have hHbarne : Hbar ≠ ⊥ := by
      intro hbarbot
      have hleM : H ≤ M := by
        simpa [Hbar, q, QuotientGroup.ker_mk'] using
          (Subgroup.map_eq_bot_iff (f := q) (H := H)).1 hbarbot
      have hHbot : H = ⊥ := by
        have hinfleft : H ⊓ M = H := inf_eq_left.mpr hleM
        rw [hinfleft] at hinf
        exact hinf
      exact hHne hHbot
    have hHbarp : IsPGroup p Hbar :=
      IsPGroup.map (p := p) (H := H) hHp q
    have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
    have hHbarNormal : Hbar.Normal := by
      have hmapNormal : ((M ⊔ H).map q).Normal :=
        Subgroup.Normal.map hnorm q hqsurj
      have hmapEq : (M ⊔ H).map q = Hbar := by
        rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
      rw [← hmapEq]
      exact hmapNormal
    have hcoreQuotNe : pCore p (Q ⧸ M) ≠ ⊥ := by
      intro hcorebot
      have hle : Hbar ≤ pCore p (Q ⧸ M) :=
        le_sSup ⟨hHbarNormal, hHbarp⟩
      rw [hcorebot] at hle
      exact hHbarne (le_bot_iff.mp hle)
    exact hnotlocal
      (pStableLocal_of_core_ne_bot (G := Q ⧸ M) p hstableQuot hcoreQuotNe)
  have hMbot' : pPrimeCore p Q = ⊥ := by simpa [M] using hMbot
  refine ⟨hMbot', ?_⟩
  dsimp only
  let q : Q →* Q ⧸ M := QuotientGroup.mk' M
  let C : Subgroup Q :=
    (Subgroup.centralizer ((H.map q : Subgroup (Q ⧸ M)) : Set (Q ⧸ M))).comap q
  change C = Subgroup.centralizer (H : Set Q) ∧ H.Normal
  have hcopHM : Nat.Coprime (Nat.card H) (Nat.card M) := by
    rcases IsPGroup.iff_card.mp hHp with ⟨a, ha⟩
    rw [ha]
    exact (pPrimeCore_coprime_card (G := Q) (p := p)).pow_left a
  have hinf : H ⊓ M = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcopHM).eq_bot
  have hMN : M ⊔ Subgroup.normalizer (H : Set Q) = ⊤ :=
    pPrimeCore_sup_normalizer_eq_top H hHp hnorm
  have hCeq : C = M ⊔ Subgroup.centralizer (H : Set Q) := by
    simpa [C, q] using
      (quotient_centralizer_eq_sup M H hinf hMN)
  constructor
  · rw [hCeq, hMbot, bot_sup_eq]
  · simpa [M, hMbot] using hnorm

private theorem normal_ambient_quotient_failure {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    (x : Q) (hx : x ∈ Subgroup.normalizer (H : Set Q))
    (hout :
      QuotientGroup.mk'
          ((Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q))) ⟨x, hx⟩ ∉
        pCore p ((Subgroup.normalizer (H : Set Q)) ⧸
          (Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q)))) :
    let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
    QuotientGroup.mk' C x ∉ pCore p (Q ⧸ C) := by
  classical
  dsimp only
  let N : Subgroup Q := Subgroup.normalizer (H : Set Q)
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  have hNtop : N = ⊤ := by
    exact Subgroup.normalizer_eq_top_iff.mpr hHnormal
  let eN : N ≃* Q :=
    (MulEquiv.subgroupCongr hNtop).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  have hCmap : (C.subgroupOf N).map eN.toMonoidHom = C := by
    ext z
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hnC : ((n : N) : Q) ∈ C := Subgroup.mem_subgroupOf.mp hn
      simpa [eN, MulEquiv.subgroupCongr_apply] using hnC
    · intro hz
      have hzN : z ∈ N := by rw [hNtop]; simp
      let n : N := ⟨z, hzN⟩
      refine ⟨n, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
      simp [eN, n, MulEquiv.subgroupCongr_apply]
  let e : N ⧸ C.subgroupOf N ≃* Q ⧸ C :=
    QuotientGroup.congr
      (G := N) (H := Q) (G' := C.subgroupOf N) (H' := C) eN hCmap
  have he_mk :
      e (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩) =
        QuotientGroup.mk' C x := by
    rfl
  intro htarget
  have hcoreMap : (pCore p (N ⧸ C.subgroupOf N)).map e.toMonoidHom =
      pCore p (Q ⧸ C) :=
    pCore_map_iso (G := N ⧸ C.subgroupOf N) (G' := Q ⧸ C) (p := p) e
  rw [← hcoreMap] at htarget
  rcases Subgroup.mem_map.mp htarget with ⟨z, hz, hzeq⟩
  have hzorig : z = QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩ := by
    apply e.injective
    exact hzeq.trans he_mk.symm
  apply hout
  simpa [N, C, hzorig] using hz

private theorem normal_ambient_quotient_core_membership_iff
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    (x : Q) (hx : x ∈ Subgroup.normalizer (H : Set Q)) :
    QuotientGroup.mk'
          ((Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q))) ⟨x, hx⟩ ∈
        pCore p ((Subgroup.normalizer (H : Set Q)) ⧸
          (Subgroup.centralizer (H : Set Q)).subgroupOf
            (Subgroup.normalizer (H : Set Q))) ↔
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∈
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)) := by
  classical
  let N : Subgroup Q := Subgroup.normalizer (H : Set Q)
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  have hNtop : N = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hHnormal
  let eN : N ≃* Q :=
    (MulEquiv.subgroupCongr hNtop).trans
      (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)
  have hCmap : (C.subgroupOf N).map eN.toMonoidHom = C := by
    ext z
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hnC : ((n : N) : Q) ∈ C := Subgroup.mem_subgroupOf.mp hn
      simpa [eN, MulEquiv.subgroupCongr_apply] using hnC
    · intro hz
      have hzN : z ∈ N := by rw [hNtop]; simp
      let n : N := ⟨z, hzN⟩
      refine ⟨n, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
      simp [eN, n, MulEquiv.subgroupCongr_apply]
  let e : N ⧸ C.subgroupOf N ≃* Q ⧸ C :=
    QuotientGroup.congr
      (G := N) (H := Q) (G' := C.subgroupOf N) (H' := C) eN hCmap
  have he_mk :
      e (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩) =
        QuotientGroup.mk' C x := by
    rfl
  have hcoreMap : (pCore p (N ⧸ C.subgroupOf N)).map e.toMonoidHom =
      pCore p (Q ⧸ C) :=
    pCore_map_iso (G := N ⧸ C.subgroupOf N) (G' := Q ⧸ C) (p := p) e
  constructor
  · intro hlocal
    have hmap : e (QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩) ∈
        (pCore p (N ⧸ C.subgroupOf N)).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hlocal
    rw [hcoreMap, he_mk] at hmap
    simpa [N, C] using hmap
  · intro hambient
    have hambient' : QuotientGroup.mk' C x ∈ pCore p (Q ⧸ C) := by
      simpa [C] using hambient
    rw [← hcoreMap] at hambient'
    rcases Subgroup.mem_map.mp hambient' with ⟨z, hz, hzeq⟩
    have hzorig : z = QuotientGroup.mk' (C.subgroupOf N) ⟨x, hx⟩ := by
      apply e.injective
      exact hzeq.trans he_mk.symm
    simpa [N, C, hzorig] using hz

private theorem subgroup_local_instability_of_ambient_failure
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHp : IsPGroup p H) (hHnormal : H.Normal)
    (K : Subgroup Q) (hHK : H ≤ K)
    (hCK : Subgroup.centralizer (H : Set Q) ⊔ K = ⊤)
    (y : K)
    (hcommY :
      ⁅⁅H, Subgroup.zpowers (y : Q)⁆, Subgroup.zpowers (y : Q)⁆ = ⊥)
    (hyout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) (y : Q) ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q))) :
    ¬ pStableLocal p K := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  have hCnormal : C.Normal := by
    dsimp [C]
    infer_instance
  let : C.Normal := hCnormal
  let P : Subgroup K := H.subgroupOf K
  have hPnormal : P.Normal := by
    dsimp [P]
    exact Subgroup.Normal.subgroupOf hHnormal K
  let : P.Normal := hPnormal
  have hPp : IsPGroup p P :=
    hHp.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm
  have hPcondition : (pPrimeCore p K ⊔ P).Normal := by infer_instance
  let Nloc : Subgroup K := Subgroup.normalizer (P : Set K)
  let Cloc : Subgroup K := Subgroup.centralizer (P : Set K)
  have hNtop : Nloc = ⊤ := by
    exact Subgroup.normalizer_eq_top_iff.mpr hPnormal
  have hCloc : Cloc = C.subgroupOf K := by
    ext k
    constructor
    · intro hk
      apply Subgroup.mem_subgroupOf.mpr
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      let hK : K := ⟨h, hHK hh⟩
      have hhP : hK ∈ P := Subgroup.mem_subgroupOf.mpr hh
      exact congrArg Subtype.val
        (Subgroup.mem_centralizer_iff.mp hk hK hhP)
    · intro hk
      rw [Subgroup.mem_centralizer_iff]
      intro hK hhP
      apply Subtype.ext
      have hhH : (hK : Q) ∈ H := Subgroup.mem_subgroupOf.mp hhP
      exact Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_subgroupOf.mp hk) (hK : Q) hhH
  have hyN : y ∈ Nloc := by rw [hNtop]; simp
  have hcommLocal :
      ⁅⁅P, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ = ⊥ := by
    apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_commutator]
    rw [Subgroup.map_subgroupOf_eq_of_le hHK]
    simpa using hcommY
  let qC : Q →* Q ⧸ C := QuotientGroup.mk' C
  let theta : Nloc →* Q ⧸ C :=
    qC.comp (K.subtype.comp Nloc.subtype)
  have hthetaSurj : Function.Surjective theta := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro g
    have hg : g ∈ C ⊔ K := by
      rw [show C ⊔ K = ⊤ by simpa [C] using hCK]
      simp
    rcases (Subgroup.mem_sup_of_normal_left
      (s := C) (t := K) (x := g)).mp hg with ⟨c, hc, k, hk, hck⟩
    let kK : K := ⟨k, hk⟩
    have hkN : kK ∈ Nloc := by rw [hNtop]; simp
    refine ⟨⟨kK, hkN⟩, ?_⟩
    change qC k = qC g
    rw [← hck, map_mul]
    have hqc : qC c = 1 :=
      (QuotientGroup.eq_one_iff (N := C) (x := c)).2 hc
    rw [hqc, one_mul]
  let ClocN : Subgroup Nloc := Cloc.subgroupOf Nloc
  have hker : ClocN = theta.ker := by
    ext n
    constructor
    · intro hn
      change theta n = 1
      apply (QuotientGroup.eq_one_iff
        (N := C) (x := ((n : Nloc) : K))).2
      have hnCloc : ((n : Nloc) : K) ∈ Cloc :=
        Subgroup.mem_subgroupOf.mp hn
      rw [hCloc] at hnCloc
      exact Subgroup.mem_subgroupOf.mp hnCloc
    · intro hn
      apply Subgroup.mem_subgroupOf.mpr
      rw [hCloc]
      apply Subgroup.mem_subgroupOf.mpr
      apply (QuotientGroup.eq_one_iff
        (N := C) (x := (((n : Nloc) : K) : Q))).1
      exact hn
  let e : Nloc ⧸ ClocN ≃* Q ⧸ C :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective theta hthetaSurj)
  have he_mk :
      e (QuotientGroup.mk' ClocN ⟨y, hyN⟩) =
        QuotientGroup.mk' C (y : Q) := by
    rfl
  intro hlocal
  have htarget := hlocal P hPp hPcondition y hyN hcommLocal
  have htarget' : QuotientGroup.mk' ClocN ⟨y, hyN⟩ ∈
      pCore p (Nloc ⧸ ClocN) := by
    simpa [Nloc, Cloc, ClocN] using htarget
  have hmapmem : e (QuotientGroup.mk' ClocN ⟨y, hyN⟩) ∈
      (pCore p (Nloc ⧸ ClocN)).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom htarget'
  have hcoreMap : (pCore p (Nloc ⧸ ClocN)).map e.toMonoidHom =
      pCore p (Q ⧸ C) :=
    pCore_map_iso (G := Nloc ⧸ ClocN) (G' := Q ⧸ C) (p := p) e
  rw [hcoreMap, he_mk] at hmapmem
  exact hyout (by simpa [C] using hmapmem)

private theorem double_commutator_zpowers_of_central_factor
    {Q : Type u} [Group Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    {c x y : Q}
    (hc : c ∈ Subgroup.centralizer (H : Set Q))
    (hcy : c * y = x)
    (hcommX :
      ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥) :
    ⁅⁅H, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ = ⊥ := by
  let : H.Normal := hHnormal
  have hphi :
      MulAut.conjNormal (H := H) x = MulAut.conjNormal (H := H) y := by
    ext h
    have hyh : y * (h : Q) * y⁻¹ ∈ H :=
      hHnormal.conj_mem (h : Q) h.2 y
    have hccomm : (y * (h : Q) * y⁻¹) * c =
        c * (y * (h : Q) * y⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hc _ hyh
    simp only [MulAut.conjNormal_apply]
    calc
      x * (h : Q) * x⁻¹ =
          c * (y * (h : Q) * y⁻¹) * c⁻¹ := by rw [← hcy]; group
      _ = y * (h : Q) * y⁻¹ := by rw [← hccomm]; group
  have hphiZpow (n : ℤ) :
      MulAut.conjNormal (H := H) (x ^ n) =
        MulAut.conjNormal (H := H) (y ^ n) := by
    simpa using congrArg (fun a : MulAut H => a ^ n) hphi
  have hconj (n : ℤ) (h : Q) (hh : h ∈ H) :
      x ^ n * h * (x ^ n)⁻¹ = y ^ n * h * (y ^ n)⁻¹ := by
    have heval := congrArg
      (fun a : MulAut H => a ⟨h, hh⟩) (hphiZpow n)
    exact congrArg Subtype.val heval
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [Subgroup.commutator_le]
  intro h hh ym hym
  rw [Subgroup.mem_centralizer_iff]
  intro yn hyn
  rcases Subgroup.mem_zpowers_iff.mp hym with ⟨m, rfl⟩
  rcases Subgroup.mem_zpowers_iff.mp hyn with ⟨n, rfl⟩
  have hcommEq : ⁅h, y ^ m⁆ = ⁅h, x ^ m⁆ := by
    have hcj := hconj m h⁻¹ (H.inv_mem hh)
    calc
      ⁅h, y ^ m⁆ = h * (y ^ m * h⁻¹ * (y ^ m)⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      _ = h * (x ^ m * h⁻¹ * (x ^ m)⁻¹) := by rw [← hcj]
      _ = ⁅h, x ^ m⁆ := by
        simp [commutatorElement_def, mul_assoc]
  let z : Q := ⁅h, x ^ m⁆
  have hzH : z ∈ H := by
    apply (Subgroup.commutator_le_left H (Subgroup.zpowers x))
    exact Subgroup.commutator_mem_commutator hh
      (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)
  have hzcent : z ∈ Subgroup.centralizer (Subgroup.zpowers x : Set Q) := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommX)
    exact Subgroup.commutator_mem_commutator hh
      (Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)
  have hxmul : x ^ n * z = z * x ^ n :=
    Subgroup.mem_centralizer_iff.mp hzcent (x ^ n)
      (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
  have hxconj : x ^ n * z * (x ^ n)⁻¹ = z := by
    rw [hxmul]
    group
  have hyconj : y ^ n * z * (y ^ n)⁻¹ = z := by
    rw [← hconj n z hzH]
    exact hxconj
  have hymul : y ^ n * z = z * y ^ n := by
    calc
      y ^ n * z = (y ^ n * z * (y ^ n)⁻¹) * y ^ n := by group
      _ = z * y ^ n := by rw [hyconj]
  rw [hcommEq]
  exact hymul

variable {G : Type*} [Group G]

private lemma commutatorElement_eq_of_div_mem_centralizer
    {H : Subgroup G} {a b h : G}
    (hbN : b ∈ Subgroup.normalizer (H : Set G))
    (hab : a / b ∈ Subgroup.centralizer (H : Set G))
    (hh : h ∈ H) :
    ⁅h, a⁆ = ⁅h, b⁆ := by
  let c : G := a / b
  have ha : a = c * b := by
    simp [c, div_eq_mul_inv, mul_assoc]
  have hcH : c ∈ Subgroup.centralizer (H : Set G) := hab
  have hhc : h * c = c * h :=
    Subgroup.mem_centralizer_iff.mp hcH h hh
  have hcommH : ⁅h, b⁆ ∈ H := by
    have hzb : Subgroup.zpowers b ≤ Subgroup.normalizer (H : Set G) :=
      Subgroup.zpowers_le.mpr hbN
    have hrev : ⁅Subgroup.zpowers b, H⁆ ≤ H :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hzb
    have hle : ⁅H, Subgroup.zpowers b⁆ ≤ H := by
      simpa [Subgroup.commutator_comm] using hrev
    exact hle (Subgroup.commutator_mem_commutator hh (Subgroup.mem_zpowers b))
  have hkc : ⁅h, b⁆ * c = c * ⁅h, b⁆ :=
    Subgroup.mem_centralizer_iff.mp hcH ⁅h, b⁆ hcommH
  rw [ha]
  simp only [commutatorElement_def, mul_inv_rev]
  calc
    h * (c * b) * h⁻¹ * (b⁻¹ * c⁻¹) =
        (h * c) * b * h⁻¹ * b⁻¹ * c⁻¹ := by group
    _ = (c * h) * b * h⁻¹ * b⁻¹ * c⁻¹ := by rw [hhc]
    _ = c * (h * b * h⁻¹ * b⁻¹) * c⁻¹ := by group
    _ = h * b * h⁻¹ * b⁻¹ := by rw [← commutatorElement_def, ← hkc]; group

private lemma commutator_zpowers_transport_of_quotient_eq
    {H C : Subgroup G} [C.Normal]
    (hC : C = Subgroup.centralizer (H : Set G))
    {x y : G}
    (hxN : x ∈ Subgroup.normalizer (H : Set G))
    (hyN : y ∈ Subgroup.normalizer (H : Set G))
    (hxy : QuotientGroup.mk' C x = QuotientGroup.mk' C y)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥) :
    ⁅⁅H, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ = ⊥ := by
  have hpow_div {n : ℤ} : x ^ n / y ^ n ∈ C := by
    apply QuotientGroup.eq_iff_div_mem.mp
    simpa using congrArg (fun z => z ^ n) hxy
  have hpow_div' {n : ℤ} : y ^ n / x ^ n ∈ C := by
    apply QuotientGroup.eq_iff_div_mem.mp
    simpa using congrArg (fun z => z ^ n) hxy.symm
  have hzxN : Subgroup.zpowers x ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.zpowers_le.mpr hxN
  have hzyN : Subgroup.zpowers y ≤ Subgroup.normalizer (H : Set G) :=
    Subgroup.zpowers_le.mpr hyN
  have hfirstX_le_H : ⁅H, Subgroup.zpowers x⁆ ≤ H := by
    have hrev : ⁅Subgroup.zpowers x, H⁆ ≤ H :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp hzxN
    simpa [Subgroup.commutator_comm] using hrev
  have hfirst : ⁅H, Subgroup.zpowers y⁆ = ⁅H, Subgroup.zpowers x⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro h hh z hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
      have heq : ⁅h, y ^ n⁆ = ⁅h, x ^ n⁆ :=
        commutatorElement_eq_of_div_mem_centralizer
          (H := H) (a := y ^ n) (b := x ^ n)
          (hzxN (Subgroup.zpow_mem_zpowers x n)) (by simpa [hC] using hpow_div') hh
      rw [heq]
      exact Subgroup.commutator_mem_commutator hh (Subgroup.zpow_mem_zpowers x n)
    · rw [Subgroup.commutator_le]
      intro h hh z hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
      have heq : ⁅h, x ^ n⁆ = ⁅h, y ^ n⁆ :=
        commutatorElement_eq_of_div_mem_centralizer
          (H := H) (a := x ^ n) (b := y ^ n)
          (hzyN (Subgroup.zpow_mem_zpowers y n)) (by simpa [hC] using hpow_div) hh
      rw [heq]
      exact Subgroup.commutator_mem_commutator hh (Subgroup.zpow_mem_zpowers y n)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  rw [hfirst] at hk
  have hkH : k ∈ H := hfirstX_le_H hk
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one']
  intro z hz
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
  have heq : ⁅k, y ^ n⁆ = ⁅k, x ^ n⁆ :=
    commutatorElement_eq_of_div_mem_centralizer
      (H := H) (a := y ^ n) (b := x ^ n)
      (hzxN (Subgroup.zpow_mem_zpowers x n)) (by simpa [hC] using hpow_div') hkH
  rw [heq]
  have hkcent : k ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hk
  exact (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hkcent)
    (x ^ n) (Subgroup.zpow_mem_zpowers x n)

private theorem not_pStableLocal_normalizer_sylow_of_failure
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    {Q : Type*} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal) (hHp : IsPGroup p H)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (R : Sylow r (↥(Subgroup.centralizer (H : Set Q)))) :
    let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
    let RG : Subgroup Q := (R : Subgroup C).map C.subtype
    let L : Subgroup Q := Subgroup.normalizer (RG : Set Q)
    ¬ pStableLocal p (↥L) := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let : C.Normal := by
    dsimp [C]
    exact Subgroup.normal_centralizer (H := H)
  let RG : Subgroup Q := (R : Subgroup C).map C.subtype
  let L : Subgroup Q := Subgroup.normalizer (RG : Set Q)
  have hFr : L ⊔ C = ⊤ := by
    simpa [L, RG] using (Sylow.normalizer_sup_eq_top (N := C) R)
  have hRG_le_C : RG ≤ C := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨zC, _, rfl⟩
    exact zC.2
  have hH_le_centRG : H ≤ Subgroup.centralizer (RG : Set Q) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzC : z ∈ C := hRG_le_C hz
    exact (Subgroup.mem_centralizer_iff.mp hzC h hh).symm
  have hH_le_L : H ≤ L :=
    hH_le_centRG.trans (Subgroup.centralizer_le_normalizer (RG : Set Q))
  let Hloc : Subgroup L := H.subgroupOf L
  have hHloc_normal : Hloc.Normal := by
    exact Subgroup.Normal.subgroupOf hHnormal L
  let : Hloc.Normal := hHloc_normal
  have hHlocp : IsPGroup p Hloc := by
    simpa [Hloc] using hHp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := H) (K := L) hH_le_L).symm
  have hxTop : x ∈ L ⊔ C := by
    rw [hFr]
    trivial
  rcases (Subgroup.mem_sup_of_normal_right (s := L) (t := C)).1 hxTop with
    ⟨y, hyL, c, hcC, hyc⟩
  let yL : L := ⟨y, hyL⟩
  have hNtop : Subgroup.normalizer (H : Set Q) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hHnormal
  have hxN : x ∈ Subgroup.normalizer (H : Set Q) := by
    rw [hNtop]
    trivial
  have hyN : y ∈ Subgroup.normalizer (H : Set Q) := by
    rw [hNtop]
    trivial
  let qC : Q →* Q ⧸ C := QuotientGroup.mk' C
  have hqy : qC y = qC x := by
    have hqc : qC c = 1 := (QuotientGroup.eq_one_iff c).mpr hcC
    rw [← hyc, map_mul, hqc, mul_one]
  have hcommy : ⁅⁅H, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ = ⊥ :=
    commutator_zpowers_transport_of_quotient_eq
      (H := H) (C := C) (hC := rfl) hxN hyN hqy.symm hcomm
  have hHloc_map : Hloc.map L.subtype = H := by
    calc
      Hloc.map L.subtype = H ⊓ L := by
        change (H.subgroupOf L).map L.subtype = H ⊓ L
        exact Subgroup.subgroupOf_map_subtype (H := H) (K := L)
      _ = H := inf_eq_left.mpr hH_le_L
  have hzpow_map : (Subgroup.zpowers yL).map L.subtype = Subgroup.zpowers y := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hcommLoc :
      ⁅⁅Hloc, Subgroup.zpowers yL⁆, Subgroup.zpowers yL⁆ = ⊥ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      hHloc_map, hzpow_map, hcommy, Subgroup.map_bot]
  let Nloc : Subgroup L := Subgroup.normalizer (Hloc : Set L)
  let Cloc : Subgroup L := Subgroup.centralizer (Hloc : Set L)
  have hNloc_top : Nloc = ⊤ := by
    simpa [Nloc] using (Subgroup.normalizer_eq_top_iff.mpr hHloc_normal)
  have hyNloc : yL ∈ Nloc := by
    rw [hNloc_top]
    trivial
  have : (Cloc.subgroupOf Nloc).Normal := inferInstance
  let f : ↥Nloc →* Q ⧸ C :=
    qC.comp (L.subtype.comp Nloc.subtype)
  have hf_surj : Function.Surjective f := by
    intro z
    refine Quotient.inductionOn' z ?_
    intro g
    have hgTop : g ∈ L ⊔ C := by
      rw [hFr]
      trivial
    rcases (Subgroup.mem_sup_of_normal_right (s := L) (t := C)).1 hgTop with
      ⟨l, hlL, d, hdC, hld⟩
    let lL : L := ⟨l, hlL⟩
    have hlN : lL ∈ Nloc := by
      rw [hNloc_top]
      trivial
    refine ⟨⟨lL, hlN⟩, ?_⟩
    change qC l = qC g
    have hqd : qC d = 1 := (QuotientGroup.eq_one_iff d).mpr hdC
    rw [← hld, map_mul, hqd, mul_one]
  have hker : Cloc.subgroupOf Nloc = f.ker := by
    ext n
    constructor
    · intro hn
      have hnCloc : (n : L) ∈ Cloc := Subgroup.mem_subgroupOf.mp hn
      apply MonoidHom.mem_ker.mpr
      apply (QuotientGroup.eq_one_iff ((n : L) : Q)).mpr
      change ((n : L) : Q) ∈ Subgroup.centralizer (H : Set Q)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      let hL : L := ⟨h, hH_le_L hh⟩
      have hhLoc : hL ∈ Hloc := hh
      have heq := Subgroup.mem_centralizer_iff.mp hnCloc hL hhLoc
      exact congrArg Subtype.val heq
    · intro hn
      have hnf : f n = 1 := MonoidHom.mem_ker.mp hn
      have hnC : ((n : L) : Q) ∈ C := by
        exact (QuotientGroup.eq_one_iff ((n : L) : Q)).mp hnf
      apply Subgroup.mem_subgroupOf.mpr
      change (n : L) ∈ Subgroup.centralizer (Hloc : Set L)
      rw [Subgroup.mem_centralizer_iff]
      intro hL hhLoc
      apply Subtype.ext
      have hhH : (hL : Q) ∈ H := hhLoc
      exact Subgroup.mem_centralizer_iff.mp hnC (hL : Q) hhH
  let e : ↥Nloc ⧸ Cloc.subgroupOf Nloc ≃* Q ⧸ C :=
    QuotientGroup.liftEquiv (Cloc.subgroupOf Nloc) hf_surj hker
  have he_y :
      e (QuotientGroup.mk' (Cloc.subgroupOf Nloc) ⟨yL, hyNloc⟩) =
        QuotientGroup.mk' C x := by
    change f ⟨yL, hyNloc⟩ = qC x
    simpa [f, yL] using hqy
  change ¬ pStableLocal p (↥L)
  intro hstable
  have hnorm : (pPrimeCore p (↥L) ⊔ Hloc).Normal :=
    Subgroup.sup_normal (pPrimeCore p (↥L)) Hloc
  have hconcl :
      QuotientGroup.mk' (Cloc.subgroupOf Nloc) ⟨yL, hyNloc⟩ ∈
        pCore p (Nloc ⧸ Cloc.subgroupOf Nloc) := by
    simpa [Nloc, Cloc] using hstable Hloc hHlocp hnorm yL hyNloc hcommLoc
  have hcore_map :
      (pCore p (Nloc ⧸ Cloc.subgroupOf Nloc)).map e.toMonoidHom = pCore p (Q ⧸ C) :=
    pCore_map_iso (G := ↥Nloc ⧸ Cloc.subgroupOf Nloc) (G' := Q ⧸ C) (p := p) (f := e)
  apply hxout
  have hmem_map :
      e (QuotientGroup.mk' (Cloc.subgroupOf Nloc) ⟨yL, hyNloc⟩) ∈
        (pCore p (Nloc ⧸ Cloc.subgroupOf Nloc)).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hconcl
  rw [hcore_map, he_y] at hmem_map
  simpa [C] using hmem_map

private theorem normalizer_sylow_eq_top_of_minimal_failure
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    {Q : Type*} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal) (hHp : IsPGroup p H)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (hmin : ∀ K : Subgroup Q, Nat.card K < Nat.card Q → pStable p (↥K))
    (R : Sylow r (↥(Subgroup.centralizer (H : Set Q)))) :
    let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
    let RG : Subgroup Q := (R : Subgroup C).map C.subtype
    Subgroup.normalizer (RG : Set Q) = ⊤ := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let RG : Subgroup Q := (R : Subgroup C).map C.subtype
  let L : Subgroup Q := Subgroup.normalizer (RG : Set Q)
  have hnotlocal : ¬ pStableLocal p (↥L) := by
    simpa [C, RG, L] using
      (not_pStableLocal_normalizer_sylow_of_failure
        (p := p) (r := r) H hHnormal hHp x hcomm hxout R)
  have hHne : H ≠ ⊥ := by
    intro hHbot
    apply hxout
    have hxC : x ∈ Subgroup.centralizer (H : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hhOne : h = 1 := by
        rw [hHbot] at hh
        simpa using hh
      subst h
      simp
    have hxone : QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hxC
    rw [hxone]
    exact (pCore p (Q ⧸ Subgroup.centralizer (H : Set Q))).one_mem
  have hRG_le_C : RG ≤ C := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨zC, _, rfl⟩
    exact zC.2
  have hH_le_centRG : H ≤ Subgroup.centralizer (RG : Set Q) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzC : z ∈ C := hRG_le_C hz
    exact (Subgroup.mem_centralizer_iff.mp hzC h hh).symm
  have hH_le_L : H ≤ L :=
    hH_le_centRG.trans (Subgroup.centralizer_le_normalizer (RG : Set Q))
  let Hloc : Subgroup L := H.subgroupOf L
  have hHloc_normal : Hloc.Normal :=
    Subgroup.Normal.subgroupOf hHnormal L
  have hHlocp : IsPGroup p Hloc := by
    simpa [Hloc] using hHp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := H) (K := L) hH_le_L).symm
  have hHloc_ne : Hloc ≠ ⊥ := by
    intro hbot
    apply hHne
    apply le_antisymm
    · intro h hh
      let hL : L := ⟨h, hH_le_L hh⟩
      have hhLoc : hL ∈ Hloc := hh
      rw [hbot] at hhLoc
      have hhOne : hL = 1 := by simpa using hhLoc
      have : h = 1 := congrArg Subtype.val hhOne
      simp [this]
    · exact bot_le
  have hcore_ne : pCore p (↥L) ≠ ⊥ := by
    intro hcore_bot
    apply hHloc_ne
    apply le_antisymm
    · have hle : Hloc ≤ pCore p (↥L) := le_sSup ⟨hHloc_normal, hHlocp⟩
      rw [hcore_bot] at hle
      exact hle
    · exact bot_le
  change L = ⊤
  by_contra hLtop
  have hlt : L < (⊤ : Subgroup Q) := lt_top_iff_ne_top.mpr hLtop
  have hcard : Nat.card L < Nat.card Q := by
    simpa using natCard_lt_of_subgroup_lt hlt
  have hstable : pStable p (↥L) := hmin L hcard
  exact hnotlocal (pStableLocal_of_core_ne_bot (G := ↥L) p hstable hcore_ne)

private theorem centralizer_isPGroup_of_minimal_failure
    {p : ℕ} [Fact p.Prime]
    {Q : Type*} [Group Q] [Finite Q]
    (hO : pPrimeCore p Q = ⊥)
    (H : Subgroup Q) (hHnormal : H.Normal) (hHp : IsPGroup p H)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (hmin : ∀ K : Subgroup Q, Nat.card K < Nat.card Q → pStable p (↥K)) :
    IsPGroup p (↥(Subgroup.centralizer (H : Set Q))) := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card C).primeFactorsList.length, ?_⟩
  apply Nat.eq_prime_pow_of_unique_prime_dvd
  · exact (Nat.card_ne_zero.mpr ⟨⟨1, C.one_mem⟩, inferInstance⟩)
  · intro d hdprime hdvd
    by_contra hdp
    let : Fact d.Prime := ⟨hdprime⟩
    let R : Sylow d (↥C) := Classical.choice (Sylow.nonempty (p := d) (G := ↥C))
    have hRne : (R : Subgroup C) ≠ ⊥ := Sylow.ne_bot_of_dvd_card R hdvd
    let RG : Subgroup Q := (R : Subgroup C).map C.subtype
    have hRGne : RG ≠ ⊥ := by
      intro hbot
      apply hRne
      apply Subgroup.map_injective C.subtype_injective
      simpa [RG] using hbot
    have hnormtop : Subgroup.normalizer (RG : Set Q) = ⊤ := by
      simpa [C, RG, R] using
        (normalizer_sylow_eq_top_of_minimal_failure
          (p := p) (r := d) H hHnormal hHp x hcomm hxout hmin R)
    have hRGnormal : RG.Normal := Subgroup.normalizer_eq_top_iff.mp hnormtop
    have hRGd : IsPGroup d RG := by
      simpa [RG] using IsPGroup.map R.isPGroup' C.subtype
    rcases IsPGroup.iff_card.mp hRGd with ⟨n, hn⟩
    have hpd_cop : Nat.Coprime p d := by
      apply (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr
      intro hpdvd
      rcases (Nat.dvd_prime hdprime).mp hpdvd with hp1 | hpeq
      · exact (Fact.out : Nat.Prime p).ne_one hp1
      · exact hdp hpeq.symm
    have hRGcop : Nat.Coprime p (Nat.card RG) := by
      rw [hn]
      exact hpd_cop.pow_right n
    have hRGbot : RG = ⊥ :=
      (pPrimeCore_eq_bot_iff (p := p) (G := Q)).mp hO RG hRGnormal hRGcop
    exact hRGne hRGbot

private theorem minimal_bad_witness_centralizes_minimalNormal
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hO : pPrimeCore p Q = ⊥)
    (H : Subgroup Q) (hHp : IsPGroup p H)
    (K : Subgroup Q) [K.Normal] [IsMinimalNormal K]
    (hKne : K ≠ ⊥) (hKH : K < H)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hHmin : ∀ L : Subgroup Q,
      Nat.card L < Nat.card H → ¬ LocalBad p Q L) :
    x ∈ Subgroup.centralizer (K : Set Q) := by
  classical
  have hKp : IsPGroup p K := IsPGroup.to_le hHp hKH.le
  have hKcore :
      pCore p (Q ⧸ Subgroup.centralizer (K : Set Q)) = ⊥ :=
    pCore_quotient_centralizer_eq_bot_of_minimalNormal_pSubgroup
      (p := p) K hKne hKp
  by_contra hxC
  have hxN : x ∈ Subgroup.normalizer (K : Set Q) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : K.Normal)]
    trivial
  have hcommK :
      ⁅⁅K, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ := by
    apply le_antisymm
    · rw [← hcomm]
      exact Subgroup.commutator_mono
        (Subgroup.commutator_mono hKH.le le_rfl) le_rfl
    · exact bot_le
  have hxoutAmbient :
      QuotientGroup.mk' (Subgroup.centralizer (K : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (K : Set Q)) := by
    rw [hKcore]
    simpa [Subgroup.mem_bot, QuotientGroup.eq_one_iff] using hxC
  have hxoutLocal :
      QuotientGroup.mk'
            ((Subgroup.centralizer (K : Set Q)).subgroupOf
              (Subgroup.normalizer (K : Set Q))) ⟨x, hxN⟩ ∉
          pCore p ((Subgroup.normalizer (K : Set Q)) ⧸
            (Subgroup.centralizer (K : Set Q)).subgroupOf
              (Subgroup.normalizer (K : Set Q))) := by
    intro hxLocal
    exact hxoutAmbient
      ((normal_ambient_quotient_core_membership_iff
        (p := p) K (inferInstance : K.Normal) x hxN).mp hxLocal)
  have hKnormalSup : (pPrimeCore p Q ⊔ K).Normal := by
    simpa [hO] using (inferInstance : K.Normal)
  have hKbad : LocalBad p Q K :=
    ⟨hKp, hKnormalSup, x, hxN, hcommK, hxoutLocal⟩
  have hKcard : Nat.card K < Nat.card H :=
    natCard_lt_of_subgroup_lt hKH
  exact hHmin K hKcard hKbad

private theorem quotient_pstability_places_witness_in_pcore
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) (hHnormal : H.Normal) (hHp : IsPGroup p H)
    (K : Subgroup Q) [K.Normal]
    (hKne : K ≠ ⊥) (hKH : K < H)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥) :
    let q : Q →* Q ⧸ K := QuotientGroup.mk' K
    let Hbar : Subgroup (Q ⧸ K) := H.map q
    let Cbar : Subgroup (Q ⧸ K) :=
      Subgroup.centralizer (Hbar : Set (Q ⧸ K))
    let D : Subgroup Q := Cbar.comap q
    QuotientGroup.mk' D x ∈ pCore p (Q ⧸ D) := by
  classical
  let q : Q →* Q ⧸ K := QuotientGroup.mk' K
  let Hbar : Subgroup (Q ⧸ K) := H.map q
  let Cbar : Subgroup (Q ⧸ K) :=
    Subgroup.centralizer (Hbar : Set (Q ⧸ K))
  let D : Subgroup Q := Cbar.comap q
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
  have hHbarNormal : Hbar.Normal := by
    exact Subgroup.Normal.map hHnormal q hqsurj
  let : Hbar.Normal := hHbarNormal
  have hHbarp : IsPGroup p Hbar := IsPGroup.map hHp q
  have hHbarne : Hbar ≠ ⊥ := by
    intro hbot
    have hHleK : H ≤ K := by
      have hleKer : H ≤ q.ker :=
        (Subgroup.map_eq_bot_iff H).mp (by simpa [Hbar] using hbot)
      simpa [q, QuotientGroup.ker_mk'] using hleKer
    exact (not_le_of_gt hKH) hHleK
  have hHbar_le_core : Hbar ≤ pCore p (Q ⧸ K) :=
    le_sSup ⟨hHbarNormal, hHbarp⟩
  have hcore_ne : pCore p (Q ⧸ K) ≠ ⊥ := by
    intro hbot
    apply hHbarne
    apply le_antisymm
    · rw [← hbot]
      exact hHbar_le_core
    · exact bot_le
  have hquotlt : Nat.card (Q ⧸ K) < Nat.card Q :=
    natCard_quotient_lt_natCard_of_ne_bot K hKne
  have htopquotlt :
      Nat.card ((⊤ : Subgroup Q) ⧸ K.subgroupOf (⊤ : Subgroup Q)) <
        Nat.card Q := by
    calc
      Nat.card ((⊤ : Subgroup Q) ⧸ K.subgroupOf (⊤ : Subgroup Q)) =
          Nat.card (Q ⧸ K) :=
        Nat.card_congr (top_quotient_congr K).toEquiv
      _ < Nat.card Q := hquotlt
  have hstableTop :
      pStable p ((⊤ : Subgroup Q) ⧸ K.subgroupOf (⊤ : Subgroup Q)) :=
    hmin (⊤ : Subgroup Q) (K.subgroupOf (⊤ : Subgroup Q)) htopquotlt
  have hstableQuot : pStable p (Q ⧸ K) :=
    (pStable_iso (top_quotient_congr K)).mp hstableTop
  have hstableLocal : pStableLocal p (Q ⧸ K) :=
    pStableLocal_of_core_ne_bot (G := Q ⧸ K) p hstableQuot hcore_ne
  have hHbarCondition : (pPrimeCore p (Q ⧸ K) ⊔ Hbar).Normal :=
    Subgroup.sup_normal (pPrimeCore p (Q ⧸ K)) Hbar
  let xbar : Q ⧸ K := q x
  have hxbarN : xbar ∈ Subgroup.normalizer (Hbar : Set (Q ⧸ K)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hHbarNormal]
    trivial
  have hcommbar :
      ⁅⁅Hbar, Subgroup.zpowers xbar⁆, Subgroup.zpowers xbar⁆ = ⊥ := by
    have hmap := congrArg (fun L : Subgroup Q => L.map q) hcomm
    simpa [Hbar, xbar, Subgroup.map_commutator, MonoidHom.map_zpowers] using hmap
  have hxLocal :=
    hstableLocal Hbar hHbarp hHbarCondition xbar hxbarN hcommbar
  have hxAmbient :
      QuotientGroup.mk' Cbar xbar ∈ pCore p ((Q ⧸ K) ⧸ Cbar) := by
    apply (normal_ambient_quotient_core_membership_iff
      (p := p) Hbar hHbarNormal xbar hxbarN).mp
    simpa [Cbar] using hxLocal
  have hCbarNormal : Cbar.Normal := Subgroup.normal_centralizer (H := Hbar)
  let : Cbar.Normal := hCbarNormal
  have hDnormal : D.Normal := Subgroup.Normal.comap hCbarNormal q
  let : D.Normal := hDnormal
  have hKleD : K ≤ D := by
    intro k hk
    change q k ∈ Cbar
    have hqk : q k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    simp [hqk]
  have hDmap : D.map q = Cbar := by
    apply le_antisymm
    · rintro z ⟨d, hd, rfl⟩
      exact hd
    · intro z hz
      rcases hqsurj z with ⟨d, rfl⟩
      exact Subgroup.mem_map.mpr ⟨d, hz, rfl⟩
  have hDmapNormal : (D.map q).Normal :=
    Subgroup.Normal.map hDnormal q hqsurj
  let : (D.map q).Normal := hDmapNormal
  let e : (Q ⧸ K) ⧸ Cbar ≃* Q ⧸ D :=
    (QuotientGroup.quotientMulEquivOfEq hDmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient K D hKleD)
  have he_mk : e (QuotientGroup.mk' Cbar xbar) = QuotientGroup.mk' D x := by
    rfl
  have hxMap : e (QuotientGroup.mk' Cbar xbar) ∈
      (pCore p ((Q ⧸ K) ⧸ Cbar)).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem e.toMonoidHom hxAmbient
  have hcoreMap :
      (pCore p ((Q ⧸ K) ⧸ Cbar)).map e.toMonoidHom = pCore p (Q ⧸ D) :=
    pCore_map_iso (G := (Q ⧸ K) ⧸ Cbar) (G' := Q ⧸ D) (p := p) e
  rw [hcoreMap, he_mk] at hxMap
  exact hxMap

private theorem minimal_bad_witness_excludes_minimalNormal_below
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hO : pPrimeCore p Q = ⊥)
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) [H.Normal] (hHp : IsPGroup p H)
    (hCp : IsPGroup p (Subgroup.centralizer (H : Set Q)))
    (K : Subgroup Q) [K.Normal] [IsMinimalNormal K]
    (hKne : K ≠ ⊥) (hKH : K < H)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (hHmin : ∀ L : Subgroup Q,
      Nat.card L < Nat.card H → ¬ LocalBad p Q L) :
    False := by
  classical
  let qK : Q →* Q ⧸ K := QuotientGroup.mk' K
  let Hbar : Subgroup (Q ⧸ K) := H.map qK
  let D : Subgroup Q :=
    (Subgroup.centralizer (Hbar : Set (Q ⧸ K))).comap qK
  have hHbarNormal : Hbar.Normal :=
    Subgroup.Normal.map (inferInstance : H.Normal) qK
      (QuotientGroup.mk'_surjective K)
  let : Hbar.Normal := hHbarNormal
  have hDnormal : D.Normal :=
    Subgroup.Normal.comap (Subgroup.normal_centralizer (H := Hbar)) qK
  let : D.Normal := hDnormal
  let qD : Q →* Q ⧸ D := QuotientGroup.mk' D
  let N : Subgroup Q := (pCore p (Q ⧸ D)).comap qD
  have hNnormal : N.Normal :=
    Subgroup.Normal.comap (inferInstance : (pCore p (Q ⧸ D)).Normal) qD
  let : N.Normal := hNnormal
  let CK : Subgroup Q := Subgroup.centralizer (K : Set Q)
  have hCKnormal : CK.Normal := Subgroup.normal_centralizer (H := K)
  let : CK.Normal := hCKnormal
  let CN : Subgroup Q := CK ⊓ N
  have hCNnormal : CN.Normal := by infer_instance
  have hxCK : x ∈ CK := by
    simpa [CK] using
      (minimal_bad_witness_centralizes_minimalNormal
        (p := p) (Q := Q) hO
        H hHp K hKne hKH x hcomm hHmin)
  have hxDcore : QuotientGroup.mk' D x ∈ pCore p (Q ⧸ D) := by
    simpa [qK, Hbar, D] using
      (quotient_pstability_places_witness_in_pcore
        (p := p) hmin H (inferInstance : H.Normal) hHp K hKne hKH x hcomm)
  have hxN : x ∈ N := by
    change qD x ∈ pCore p (Q ⧸ D)
    simpa [qD] using hxDcore
  have hxCN : x ∈ CN := ⟨hxCK, hxN⟩
  have hCNp : IsPGroup p CN := by
    simpa [CN, CK, N, qD, D, Hbar, qK] using
      (centralizer_inf_pCorePreimage_isPGroup
        (p := p) H hHp hCp K hKH.le)
  have hCN_le_core : CN ≤ pCore p Q :=
    le_sSup ⟨hCNnormal, hCNp⟩
  have hxCore : x ∈ pCore p Q := hCN_le_core hxCN
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let qC : Q →* Q ⧸ C := QuotientGroup.mk' C
  have hcoreMapNormal : ((pCore p Q).map qC).Normal :=
    Subgroup.Normal.map (inferInstance : (pCore p Q).Normal) qC
      (QuotientGroup.mk'_surjective C)
  have hcoreMapP : IsPGroup p ((pCore p Q).map qC) :=
    IsPGroup.map (pCore_isPGroup (p := p) (G := Q)) qC
  have hcoreMap_le : (pCore p Q).map qC ≤ pCore p (Q ⧸ C) :=
    le_sSup ⟨hcoreMapNormal, hcoreMapP⟩
  apply hxout
  apply hcoreMap_le
  exact Subgroup.mem_map.mpr ⟨x, hxCore, rfl⟩

private theorem minimal_bad_witness_isMinimalNormal
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hO : pPrimeCore p Q = ⊥)
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) [H.Normal] (hHp : IsPGroup p H)
    (hCp : IsPGroup p (Subgroup.centralizer (H : Set Q)))
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (hHmin : ∀ L : Subgroup Q,
      Nat.card L < Nat.card H → ¬ LocalBad p Q L) :
    IsMinimalNormal H := by
  classical
  constructor
  intro L hLnormal hLH
  by_cases hLbot : L = ⊥
  · exact Or.inl hLbot
  by_cases hLeq : L = H
  · exact Or.inr hLeq
  have hLlt : L < H := lt_of_le_of_ne hLH hLeq
  obtain ⟨K, hKnormal, hKleL, hKne, hKmin⟩ :=
    exists_minimal_normal_le (G := Q) L hLnormal hLbot
  let : K.Normal := hKnormal
  let : IsMinimalNormal K := {
    minimal := by
      intro J hJnormal hJK
      by_cases hJbot : J = ⊥
      · exact Or.inl hJbot
      · exact Or.inr (hKmin J hJnormal hJK hJbot)
  }
  have hKH : K < H := lt_of_le_of_lt hKleL hLlt
  exact False.elim
    (minimal_bad_witness_excludes_minimalNormal_below
      (p := p) hO hmin H hHp hCp K hKne hKH x hcomm hxout hHmin)

private theorem minimal_bad_witness_elementaryAbelian
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hO : pPrimeCore p Q = ⊥)
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) [H.Normal] (hHp : IsPGroup p H)
    (hCp : IsPGroup p (Subgroup.centralizer (H : Set Q)))
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)))
    (hHmin : ∀ L : Subgroup Q,
      Nat.card L < Nat.card H → ¬ LocalBad p Q L) :
    H ≠ ⊥ ∧ IsMinimalNormal H ∧ IsElementaryAbelian p H := by
  classical
  have hHne : H ≠ ⊥ := by
    intro hHbot
    apply hxout
    have hxC : x ∈ Subgroup.centralizer (H : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hhOne : h = 1 := by
        rw [hHbot] at hh
        simpa using hh
      subst h
      simp
    have hxone : QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hxC
    rw [hxone]
    exact (pCore p (Q ⧸ Subgroup.centralizer (H : Set Q))).one_mem
  have hHminimal : IsMinimalNormal H :=
    minimal_bad_witness_isMinimalNormal
      (p := p) hO hmin H hHp hCp x hcomm hxout hHmin
  let : IsMinimalNormal H := hHminimal
  have hHelem : IsElementaryAbelian p H :=
    minimalNormal_pSubgroup_isElementaryAbelian H hHne hHp
  exact ⟨hHne, hHminimal, hHelem⟩

private theorem exists_baer_witness_and_conjugate_double_commutator
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    (x : Q)
    (hcomm :
      ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q))) :
    ∃ w : Q,
      ¬ IsPGroup p
        (Subgroup.closure
          {QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x,
            QuotientGroup.mk' (Subgroup.centralizer (H : Set Q))
              (w * x * w⁻¹)} :
          Subgroup (Q ⧸ Subgroup.centralizer (H : Set Q))) ∧
        ⁅⁅H, Subgroup.zpowers (w * x * w⁻¹)⁆,
            Subgroup.zpowers (w * x * w⁻¹)⁆ = ⊥ := by
  classical
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  have hCnormal : C.Normal := Subgroup.normal_centralizer (H := H)
  let : C.Normal := hCnormal
  have hnotall : ¬ ∀ w : Q,
      IsPGroup p
        (Subgroup.closure
          {QuotientGroup.mk' C x,
            QuotientGroup.mk' C (w * x * w⁻¹)} : Subgroup (Q ⧸ C)) := by
    intro hall
    exact hxout (by
      simpa [C] using baer_contrapositive (p := p) C x hall)
  push Not at hnotall
  rcases hnotall with ⟨w, hw⟩
  refine ⟨w, by simpa [C] using hw, ?_⟩
  let : H.Normal := hHnormal
  have hmap := congrArg
    (fun K : Subgroup Q => K.map (MulAut.conj w).toMonoidHom) hcomm
  simpa [Subgroup.map_commutator, MonoidHom.map_zpowers,
    Subgroup.Normal.map_conj_eq] using hmap

private theorem exists_baer_Gstar_not_pGroup
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (H : Subgroup Q) (hHnormal : H.Normal)
    (x : Q)
    (hcomm :
      ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q))) :
    ∃ w : Q,
      let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
      let xw : Q := w * x * w⁻¹
      let Gstar : Subgroup Q := Subgroup.closure {x, xw} ⊔ C
      let Cstar : Subgroup Gstar := C.subgroupOf Gstar
      let hCstar : Cstar.Normal :=
        Subgroup.Normal.subgroupOf
          (Subgroup.normal_centralizer (H := H)) Gstar
      letI : Cstar.Normal := hCstar
      ¬ IsPGroup p (Gstar ⧸ Cstar) ∧
        ⁅⁅H, Subgroup.zpowers xw⁆, Subgroup.zpowers xw⁆ = ⊥ := by
  classical
  rcases exists_baer_witness_and_conjugate_double_commutator
      (p := p) H hHnormal x hcomm hxout with ⟨w, hw, hcommw⟩
  refine ⟨w, ?_⟩
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let xw : Q := w * x * w⁻¹
  let Gstar : Subgroup Q := Subgroup.closure {x, xw} ⊔ C
  let Cstar : Subgroup Gstar := C.subgroupOf Gstar
  have hCnormal : C.Normal := Subgroup.normal_centralizer (H := H)
  let : C.Normal := hCnormal
  have hCstarNormal : Cstar.Normal :=
    Subgroup.Normal.subgroupOf hCnormal Gstar
  let : Cstar.Normal := hCstarNormal
  change ¬ IsPGroup p (Gstar ⧸ Cstar) ∧
    ⁅⁅H, Subgroup.zpowers xw⁆, Subgroup.zpowers xw⁆ = ⊥
  refine ⟨?_, by simpa [xw] using hcommw⟩
  let q : Q →* Q ⧸ C := QuotientGroup.mk' C
  let f : Gstar →* Q ⧸ C := q.comp Gstar.subtype
  have hker : Cstar = f.ker := by
    ext g
    constructor
    · intro hg
      apply (MonoidHom.mem_ker (f := f)).mpr
      apply (QuotientGroup.eq_one_iff (N := C) (x := (g : Q))).2
      exact Subgroup.mem_subgroupOf.mp hg
    · intro hg
      apply Subgroup.mem_subgroupOf.mpr
      apply (QuotientGroup.eq_one_iff (N := C) (x := (g : Q))).1
      exact (MonoidHom.mem_ker (f := f)).mp hg
  have hCmap : C.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff C).2
    simp [q, QuotientGroup.ker_mk']
  have hGstarMap : Gstar.map q =
      Subgroup.closure
        {QuotientGroup.mk' C x, QuotientGroup.mk' C xw} := by
    calc
      Gstar.map q =
          (Subgroup.closure {x, xw}).map q ⊔ C.map q := by
        change (Subgroup.closure {x, xw} ⊔ C).map q = _
        rw [Subgroup.map_sup]
      _ = Subgroup.closure (q '' {x, xw}) ⊔ ⊥ := by
        rw [MonoidHom.map_closure, hCmap]
      _ = Subgroup.closure
          {QuotientGroup.mk' C x, QuotientGroup.mk' C xw} := by
        rw [sup_bot_eq]
        congr 1
        ext z
        simp [q, eq_comm]
  have hrange : f.range =
      Subgroup.closure
        {QuotientGroup.mk' C x, QuotientGroup.mk' C xw} := by
    calc
      f.range = Gstar.map q := by
        simp [f, MonoidHom.range_comp]
      _ = _ := hGstarMap
  let e : Gstar ⧸ Cstar ≃*
      Subgroup.closure
        {QuotientGroup.mk' C x, QuotientGroup.mk' C xw} :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange f).trans
        (MulEquiv.subgroupCongr hrange))
  intro hGp
  apply (by simpa [C, xw] using hw)
  exact hGp.of_equiv e

private theorem minimal_bad_witness_Gstar_eq_top
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) (hHnormal : H.Normal)
    (hHne : H ≠ ⊥) (hHp : IsPGroup p H)
    (hHelem : IsElementaryAbelian p H)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q))) :
    ∃ w : Q,
      let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
      let xw : Q := w * x * w⁻¹
      let Gstar : Subgroup Q := Subgroup.closure {x, xw} ⊔ C
      let Cstar : Subgroup Gstar := C.subgroupOf Gstar
      let hCstar : Cstar.Normal :=
        Subgroup.Normal.subgroupOf
          (Subgroup.normal_centralizer (H := H)) Gstar
      letI : Cstar.Normal := hCstar
      Gstar = ⊤ ∧
        ¬ IsPGroup p (Gstar ⧸ Cstar) ∧
        ⁅⁅H, Subgroup.zpowers xw⁆, Subgroup.zpowers xw⁆ = ⊥ := by
  classical
  let : H.Normal := hHnormal
  let : IsElementaryAbelian p H := hHelem
  let : IsMulCommutative H := hHelem.toIsMulCommutative
  rcases exists_baer_Gstar_not_pGroup
      (p := p) H hHnormal x hcomm hxout with ⟨w, hnotGp, hcommw⟩
  refine ⟨w, ?_⟩
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let xw : Q := w * x * w⁻¹
  let Gstar : Subgroup Q := Subgroup.closure {x, xw} ⊔ C
  let Cstar : Subgroup Gstar := C.subgroupOf Gstar
  have hCnormal : C.Normal := Subgroup.normal_centralizer (H := H)
  let : C.Normal := hCnormal
  have hCstarNormal : Cstar.Normal :=
    Subgroup.Normal.subgroupOf hCnormal Gstar
  let : Cstar.Normal := hCstarNormal
  change Gstar = ⊤ ∧ ¬ IsPGroup p (Gstar ⧸ Cstar) ∧
    ⁅⁅H, Subgroup.zpowers xw⁆, Subgroup.zpowers xw⁆ = ⊥
  refine ⟨?_, hnotGp, by simpa [xw] using hcommw⟩
  have hHC : H ≤ C := by
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := H)).2 inferInstance
  have hHG : H ≤ Gstar := hHC.trans (by
    dsimp [Gstar]
    exact le_sup_right)
  let Hstar : Subgroup Gstar := H.subgroupOf Gstar
  have hHstarNormal : Hstar.Normal :=
    Subgroup.Normal.subgroupOf hHnormal Gstar
  let : Hstar.Normal := hHstarNormal
  have hHstarp : IsPGroup p Hstar := by
    simpa [Hstar] using hHp.of_equiv
      (Subgroup.subgroupOfEquivOfLe hHG).symm
  have hHstarne : Hstar ≠ ⊥ := by
    intro hbot
    apply hHne
    apply le_antisymm
    · intro h hh
      let hs : Gstar := ⟨h, hHG hh⟩
      have hhs : hs ∈ Hstar := hh
      rw [hbot] at hhs
      have hsOne : hs = 1 := by simpa using hhs
      have hOne : h = 1 := congrArg Subtype.val hsOne
      simp [hOne]
    · exact bot_le
  by_contra hGstarTop
  have hGstarLt : Gstar < (⊤ : Subgroup Q) :=
    lt_top_iff_ne_top.mpr hGstarTop
  have hGstarCard : Nat.card Gstar < Nat.card Q := by
    simpa using natCard_lt_of_subgroup_lt hGstarLt
  have hquotCard :
      Nat.card (Gstar ⧸ (⊥ : Subgroup Gstar)) < Nat.card Q := by
    calc
      Nat.card (Gstar ⧸ (⊥ : Subgroup Gstar)) = Nat.card Gstar :=
        Nat.card_congr (QuotientGroup.quotientBot (G := Gstar)).toEquiv
      _ < Nat.card Q := hGstarCard
  have hstableQuot : pStable p (Gstar ⧸ (⊥ : Subgroup Gstar)) :=
    hmin Gstar (⊥ : Subgroup Gstar) hquotCard
  have hstable : pStable p Gstar :=
    (pStable_iso (QuotientGroup.quotientBot (G := Gstar))).mp hstableQuot
  have hcoreNe : pCore p Gstar ≠ ⊥ := by
    intro hcoreBot
    apply hHstarne
    apply le_antisymm
    · have hle : Hstar ≤ pCore p Gstar := le_sSup ⟨hHstarNormal, hHstarp⟩
      rw [hcoreBot] at hle
      exact hle
    · exact bot_le
  have hlocal : pStableLocal p Gstar :=
    pStableLocal_of_core_ne_bot (G := Gstar) p hstable hcoreNe
  have hxG : x ∈ Gstar := by
    exact (le_sup_left : Subgroup.closure {x, xw} ≤ Gstar)
      (Subgroup.mem_closure_of_mem (by simp))
  have hxwG : xw ∈ Gstar := by
    exact (le_sup_left : Subgroup.closure {x, xw} ≤ Gstar)
      (Subgroup.mem_closure_of_mem (by simp))
  let xs : Gstar := ⟨x, hxG⟩
  let xws : Gstar := ⟨xw, hxwG⟩
  have hcentralizer :
      Subgroup.centralizer (Hstar : Set Gstar) = Cstar := by
    ext g
    constructor
    · intro hg
      apply Subgroup.mem_subgroupOf.mpr
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      let hs : Hstar := ⟨⟨h, hHG hh⟩, hh⟩
      have hcommG := Subgroup.mem_centralizer_iff.mp hg hs hs.2
      exact congrArg Subtype.val hcommG
    · intro hg
      rw [Subgroup.mem_centralizer_iff]
      intro hs hhs
      have hgC : (g : Q) ∈ C := Subgroup.mem_subgroupOf.mp hg
      have hcommQ := Subgroup.mem_centralizer_iff.mp hgC (hs : Q)
        (Subgroup.mem_subgroupOf.mp hhs)
      apply Subtype.ext
      exact hcommQ
  have comm_subgroup
      (z : Q) (hz : z ∈ Gstar)
      (hcommz : ⁅⁅H, Subgroup.zpowers z⁆, Subgroup.zpowers z⁆ = ⊥) :
      ⁅⁅Hstar, Subgroup.zpowers (⟨z, hz⟩ : Gstar)⁆,
          Subgroup.zpowers (⟨z, hz⟩ : Gstar)⁆ = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      (⁅⁅Hstar, Subgroup.zpowers (⟨z, hz⟩ : Gstar)⁆,
          Subgroup.zpowers (⟨z, hz⟩ : Gstar)⁆)
      Gstar.subtype_injective).mp
    have hHmap : Hstar.map Gstar.subtype = H := by
      simpa [Hstar] using Subgroup.map_subgroupOf_eq_of_le hHG
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hHmap]
    simpa using hcommz
  have hcommXs :
      ⁅⁅Hstar, Subgroup.zpowers xs⁆, Subgroup.zpowers xs⁆ = ⊥ := by
    simpa [xs] using comm_subgroup x hxG hcomm
  have hcommXws :
      ⁅⁅Hstar, Subgroup.zpowers xws⁆, Subgroup.zpowers xws⁆ = ⊥ := by
    simpa [xws] using comm_subgroup xw hxwG hcommw
  have hcond : (pPrimeCore p Gstar ⊔ Hstar).Normal :=
    Subgroup.sup_normal (pPrimeCore p Gstar) Hstar
  have hxNorm : xs ∈ Subgroup.normalizer (Hstar : Set Gstar) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hHstarNormal]
    trivial
  have hxwNorm : xws ∈ Subgroup.normalizer (Hstar : Set Gstar) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hHstarNormal]
    trivial
  have hxLocal := hlocal Hstar hHstarp hcond xs hxNorm hcommXs
  have hxwLocal := hlocal Hstar hHstarp hcond xws hxwNorm hcommXws
  let Dstar : Subgroup Gstar := Subgroup.centralizer (Hstar : Set Gstar)
  have hDstarNormal : Dstar.Normal := Subgroup.normal_centralizer (H := Hstar)
  let : Dstar.Normal := hDstarNormal
  have hxCore : QuotientGroup.mk' Dstar xs ∈ pCore p (Gstar ⧸ Dstar) := by
    simpa [Dstar] using
      (normal_ambient_quotient_core_membership_iff
        (p := p) Hstar hHstarNormal xs hxNorm).mp hxLocal
  have hxwCore : QuotientGroup.mk' Dstar xws ∈ pCore p (Gstar ⧸ Dstar) := by
    simpa [Dstar] using
      (normal_ambient_quotient_core_membership_iff
        (p := p) Hstar hHstarNormal xws hxwNorm).mp hxwLocal
  let Lstar : Subgroup Gstar := Subgroup.closure {xs, xws} ⊔ Dstar
  have hDmap : Dstar.map Gstar.subtype = C := by
    rw [show Dstar = Cstar by simpa [Dstar] using hcentralizer]
    simpa [Cstar] using Subgroup.map_subgroupOf_eq_of_le
      (show C ≤ Gstar by dsimp [Gstar]; exact le_sup_right)
  have hLmap : Lstar.map Gstar.subtype = Gstar := by
    calc
      Lstar.map Gstar.subtype =
          (Subgroup.closure {xs, xws}).map Gstar.subtype ⊔
            Dstar.map Gstar.subtype := by
        change (Subgroup.closure {xs, xws} ⊔ Dstar).map Gstar.subtype = _
        rw [Subgroup.map_sup]
      _ = Subgroup.closure (Gstar.subtype '' {xs, xws}) ⊔ C := by
        rw [MonoidHom.map_closure, hDmap]
      _ = Subgroup.closure {x, xw} ⊔ C := by
        congr 2
        ext z
        simp [xs, xws, eq_comm]
      _ = Gstar := rfl
  have hLtop : Lstar = ⊤ := by
    apply Subgroup.map_injective Gstar.subtype_injective
    calc
      Lstar.map Gstar.subtype = Gstar := hLmap
      _ = (⊤ : Subgroup Gstar).map Gstar.subtype := by
        symm
        ext q
        constructor
        · rintro ⟨g, _hg, rfl⟩
          exact g.2
        · intro hq
          exact ⟨⟨q, hq⟩, by trivial, rfl⟩
  let qstar : Gstar →* Gstar ⧸ Dstar := QuotientGroup.mk' Dstar
  have hTopMap : (⊤ : Subgroup Gstar).map qstar = ⊤ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      rcases QuotientGroup.mk'_surjective Dstar y with ⟨g, rfl⟩
      exact Subgroup.mem_map.mpr ⟨g, by trivial, rfl⟩
  have hClosureMap :
      (Subgroup.closure {xs, xws}).map qstar =
        Subgroup.closure {qstar xs, qstar xws} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext y
    simp [qstar, eq_comm]
  have hDstarMap : Dstar.map qstar = ⊥ := by
    change Dstar.map (QuotientGroup.mk' Dstar) = ⊥
    exact QuotientGroup.map_mk'_self Dstar
  have hclosureTop :
      Subgroup.closure {qstar xs, qstar xws} = ⊤ := by
    calc
      Subgroup.closure {qstar xs, qstar xws} =
          (Subgroup.closure {xs, xws}).map qstar := hClosureMap.symm
      _ = (Subgroup.closure {xs, xws}).map qstar ⊔ Dstar.map qstar := by
        rw [hDstarMap, sup_bot_eq]
      _ = (Subgroup.closure {xs, xws} ⊔ Dstar).map qstar := by
        rw [Subgroup.map_sup]
      _ = Lstar.map qstar := rfl
      _ = (⊤ : Subgroup Gstar).map qstar := by rw [hLtop]
      _ = ⊤ := hTopMap
  have hclosureLe :
      Subgroup.closure {qstar xs, qstar xws} ≤
        pCore p (Gstar ⧸ Dstar) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hxCore
    · exact hxwCore
  have hcoreTop : pCore p (Gstar ⧸ Dstar) = ⊤ := by
    apply top_unique
    rw [← hclosureTop]
    exact hclosureLe
  have hcoreP : IsPGroup p (pCore p (Gstar ⧸ Dstar)) :=
    pCore_isPGroup (p := p) (G := Gstar ⧸ Dstar)
  rw [hcoreTop] at hcoreP
  have hquotDp : IsPGroup p (Gstar ⧸ Dstar) :=
    hcoreP.of_equiv Subgroup.topEquiv
  let eC : Gstar ⧸ Cstar ≃* Gstar ⧸ Dstar :=
    QuotientGroup.quotientMulEquivOfEq hcentralizer.symm
  exact hnotGp (hquotDp.of_equiv eC.symm)

private theorem minimal_bad_witness_lemma6_2_data
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B))
    (H : Subgroup Q) (hHnormal : H.Normal)
    (hHminimal : IsMinimalNormal H)
    (hHne : H ≠ ⊥) (hHp : IsPGroup p H)
    (hHelem : IsElementaryAbelian p H)
    (x : Q)
    (hcomm : ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥)
    (hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q))) :
    letI : IsElementaryAbelian p H := hHelem
    letI : IsMulCommutative H := hHelem.toIsMulCommutative
    letI : Module (ZMod p) (Additive H) :=
      IsElementaryAbelian.isVectorSpace p
    ∃ (w : Q)
        (ρ : Q ⧸ Subgroup.centralizer (H : Set Q) →*
          LinearMap.GeneralLinearGroup (ZMod p) (Additive H)),
      Function.Injective ρ ∧
        (∀ W : Submodule (ZMod p) (Additive H),
          (∀ g : Q ⧸ Subgroup.centralizer (H : Set Q),
            ∀ v : Additive H, v ∈ W →
              ((ρ g : LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
                Additive H →ₗ[ZMod p] Additive H) v ∈ W) →
          W = ⊥ ∨ W = ⊤) ∧
        (∀ (q : Q) (h : Additive H),
          Additive.toMul
              ((((ρ (QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) q) :
                  LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
                Additive H →ₗ[ZMod p] Additive H) h)) =
            MulAut.conjNormal (H := H) q (Additive.toMul h)) ∧
        let xw : Q := w * x * w⁻¹
        ∃ xq yq : Q ⧸ Subgroup.centralizer (H : Set Q),
          xq = QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∧
            yq = QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) xw ∧
            Subgroup.closure ({xq, yq} : Set
              (Q ⧸ Subgroup.centralizer (H : Set Q))) = ⊤ ∧
            ((ρ xq : Additive H →ₗ[ZMod p] Additive H) - 1) ^ 2 = 0 ∧
            (ρ xq : Additive H →ₗ[ZMod p] Additive H) - 1 ≠ 0 ∧
            ((ρ yq : Additive H →ₗ[ZMod p] Additive H) - 1) ^ 2 = 0 ∧
            (ρ yq : Additive H →ₗ[ZMod p] Additive H) - 1 ≠ 0 := by
  classical
  let : H.Normal := hHnormal
  let : IsMinimalNormal H := hHminimal
  let : IsElementaryAbelian p H := hHelem
  let : IsMulCommutative H := hHelem.toIsMulCommutative
  let : Module (ZMod p) (Additive H) :=
    IsElementaryAbelian.isVectorSpace p
  rcases minimal_bad_witness_Gstar_eq_top
      (p := p) hmin H hHnormal hHne hHp hHelem x hcomm hxout with
    ⟨w, hGstarTop, _hnotGp, hcommw⟩
  obtain ⟨ρ, hρinj, hρirr, hρeval⟩ :=
    exists_minimalNormal_pSubgroup_GL_faithful_irreducible_action H hHne hHp
  refine ⟨w, ρ, hρinj, hρirr, hρeval, ?_⟩
  let C : Subgroup Q := Subgroup.centralizer (H : Set Q)
  let xw : Q := w * x * w⁻¹
  let Gstar : Subgroup Q := Subgroup.closure {x, xw} ⊔ C
  have hGstarTop' : Gstar = ⊤ := by
    simpa [Gstar, xw, C] using hGstarTop
  have hCnormal : C.Normal := Subgroup.normal_centralizer (H := H)
  let : C.Normal := hCnormal
  let q : Q →* Q ⧸ C := QuotientGroup.mk' C
  have hCmap : C.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff C).2
    simp [q, QuotientGroup.ker_mk']
  have hGstarMap : Gstar.map q =
      Subgroup.closure {q x, q xw} := by
    calc
      Gstar.map q =
          (Subgroup.closure {x, xw}).map q ⊔ C.map q := by
        change (Subgroup.closure {x, xw} ⊔ C).map q = _
        rw [Subgroup.map_sup]
      _ = Subgroup.closure (q '' {x, xw}) ⊔ ⊥ := by
        rw [MonoidHom.map_closure, hCmap]
      _ = Subgroup.closure {q x, q xw} := by
        rw [sup_bot_eq]
        congr 1
        ext z
        simp [q, eq_comm]
  have hTopMap : (⊤ : Subgroup Q).map q = ⊤ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      rcases QuotientGroup.mk'_surjective C y with ⟨g, rfl⟩
      exact Subgroup.mem_map.mpr ⟨g, by trivial, rfl⟩
  have hgen : Subgroup.closure {q x, q xw} = ⊤ := by
    calc
      Subgroup.closure {q x, q xw} = Gstar.map q := hGstarMap.symm
      _ = (⊤ : Subgroup Q).map q := by rw [hGstarTop']
      _ = ⊤ := hTopMap
  have hxC : x ∉ C := by
    intro hx
    apply hxout
    have hxOne : q x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [show QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x = q x by rfl,
      hxOne]
    exact (pCore p (Q ⧸ C)).one_mem
  have hxwC : xw ∉ C := by
    intro hxw
    apply hxC
    have hconj := hCnormal.conj_mem xw hxw w⁻¹
    have heq : w⁻¹ * xw * (w⁻¹)⁻¹ = x := by
      dsimp [xw]
      group
    rw [heq] at hconj
    exact hconj
  have hxquad :=
    quotient_conjugation_sub_one_sq_eq_zero_and_ne_zero
      (p := p) H ρ hρeval x hcomm (by simpa [C] using hxC)
  have hxwquad :=
    quotient_conjugation_sub_one_sq_eq_zero_and_ne_zero
      (p := p) H ρ hρeval xw hcommw (by simpa [C] using hxwC)
  refine ⟨q x, q xw, ?_, ?_, hgen, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa [q, C] using hxquad.1
  · simpa [q, C] using hxquad.2
  · simpa [q, C] using hxwquad.1
  · simpa [q, C] using hxwquad.2

private theorem minimal_bad_group_step4_assembled
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hbad : ¬ pStable p Q)
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B)) :
    ∃ (H : Subgroup Q) (hHnormal : H.Normal) (x : Q),
      letI : H.Normal := hHnormal
      IsPGroup p H ∧
        IsPGroup p (Subgroup.centralizer (H : Set Q)) ∧
        H ≠ ⊥ ∧ IsMinimalNormal H ∧ IsElementaryAbelian p H ∧
        ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ ∧
        QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
          pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)) := by
  classical
  obtain ⟨_hcoreNe, hnotLocal⟩ :=
    minimal_bad_core_ne_bot_and_not_local hbad hmin
  obtain ⟨H, hHbad, hHleast⟩ :=
    exists_minimal_local_instability_witness hnotLocal
  have hHbadCopy := hHbad
  rcases hHbad with ⟨hHp, _hnorm, x, hxNorm, hcomm, hxoutLocal⟩
  obtain ⟨hO, _hCeq, hHnormal⟩ :=
    minimal_pprime_core_reduction hmin H hHbadCopy
  let : H.Normal := hHnormal
  have hxout :
      QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
        pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)) :=
    normal_ambient_quotient_failure
      (p := p) H hHnormal x hxNorm hxoutLocal
  have hminSub : ∀ L : Subgroup Q,
      Nat.card L < Nat.card Q → pStable p L := by
    intro L hLcard
    have hquotCard : Nat.card (L ⧸ (⊥ : Subgroup L)) < Nat.card Q := by
      calc
        Nat.card (L ⧸ (⊥ : Subgroup L)) = Nat.card L :=
          Nat.card_congr (QuotientGroup.quotientBot (G := L)).toEquiv
        _ < Nat.card Q := hLcard
    have hstableQuot : pStable p (L ⧸ (⊥ : Subgroup L)) :=
      hmin L (⊥ : Subgroup L) hquotCard
    exact (pStable_iso (QuotientGroup.quotientBot (G := L))).mp hstableQuot
  have hCp : IsPGroup p (Subgroup.centralizer (H : Set Q)) :=
    centralizer_isPGroup_of_minimal_failure
      (p := p) hO H hHnormal hHp x hcomm hxout hminSub
  obtain ⟨hHne, hHminimal, hHelem⟩ :=
    minimal_bad_witness_elementaryAbelian
      (p := p) hO hmin H hHp hCp x hcomm hxout hHleast
  exact ⟨H, hHnormal, x, hHp, hCp, hHne, hHminimal, hHelem,
    hcomm, hxout⟩

/-- Steps 1–5 of the minimal-counterexample proof of Glauberman Lemma 6.3.
Starting from a minimal non-`p`-stable finite group, this returns the
elementary-abelian minimal normal witness, its quadratic failure element, and
the faithful irreducible quotient representation with two generating
nontrivial square-zero elements required by the aligned Step-6 theorem. -/
public theorem lemma6_3_steps1_to5
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (hbad : ¬ pStable p Q)
    (hmin : ∀ (A : Subgroup Q) (B : Subgroup A) [B.Normal],
      Nat.card (A ⧸ B) < Nat.card Q → pStable p (A ⧸ B)) :
    ∃ (H : Subgroup Q) (hHnormal : H.Normal)
        (hHelem : IsElementaryAbelian p H) (x : Q),
      letI : H.Normal := hHnormal
      letI : IsElementaryAbelian p H := hHelem
      letI : IsMulCommutative H := hHelem.toIsMulCommutative
      letI : Module (ZMod p) (Additive H) :=
        IsElementaryAbelian.isVectorSpace p
      H ≠ ⊥ ∧ IsMinimalNormal H ∧ IsPGroup p H ∧
        IsPGroup p (Subgroup.centralizer (H : Set Q)) ∧
        ⁅⁅H, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ = ⊥ ∧
        QuotientGroup.mk' (Subgroup.centralizer (H : Set Q)) x ∉
          pCore p (Q ⧸ Subgroup.centralizer (H : Set Q)) ∧
        ∃ (w : Q)
            (rho : Q ⧸ Subgroup.centralizer (H : Set Q) →*
              LinearMap.GeneralLinearGroup (ZMod p) (Additive H)),
          Function.Injective rho ∧
            (∀ W : Submodule (ZMod p) (Additive H),
              (∀ g : Q ⧸ Subgroup.centralizer (H : Set Q),
                ∀ v : Additive H, v ∈ W →
                  ((rho g : LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
                    Additive H →ₗ[ZMod p] Additive H) v ∈ W) →
              W = ⊥ ∨ W = ⊤) ∧
            (∀ (q : Q) (h : Additive H),
              Additive.toMul
                  ((((rho
                      (QuotientGroup.mk'
                        (Subgroup.centralizer (H : Set Q)) q) :
                    LinearMap.GeneralLinearGroup (ZMod p) (Additive H)) :
                    Additive H →ₗ[ZMod p] Additive H) h)) =
                MulAut.conjNormal (H := H) q (Additive.toMul h)) ∧
            let xw : Q := w * x * w⁻¹
            ∃ xq yq : Q ⧸ Subgroup.centralizer (H : Set Q),
              xq =
                  QuotientGroup.mk'
                    (Subgroup.centralizer (H : Set Q)) x ∧
                yq =
                    QuotientGroup.mk'
                      (Subgroup.centralizer (H : Set Q)) xw ∧
                Subgroup.closure ({xq, yq} : Set
                  (Q ⧸ Subgroup.centralizer (H : Set Q))) = ⊤ ∧
                ((rho xq : Additive H →ₗ[ZMod p] Additive H) - 1) ^ 2 = 0 ∧
                (rho xq : Additive H →ₗ[ZMod p] Additive H) - 1 ≠ 0 ∧
                ((rho yq : Additive H →ₗ[ZMod p] Additive H) - 1) ^ 2 = 0 ∧
                (rho yq : Additive H →ₗ[ZMod p] Additive H) - 1 ≠ 0 := by
  classical
  obtain ⟨H, hHnormal, x, hHp, hCp, hHne, hHminimal, hHelem,
      hcomm, hxout⟩ :=
    minimal_bad_group_step4_assembled hbad hmin
  let : H.Normal := hHnormal
  let : IsElementaryAbelian p H := hHelem
  let : IsMulCommutative H := hHelem.toIsMulCommutative
  let : Module (ZMod p) (Additive H) :=
    IsElementaryAbelian.isVectorSpace p
  have hdata :=
    minimal_bad_witness_lemma6_2_data
      hmin H hHnormal hHminimal hHne hHp hHelem x hcomm hxout
  exact ⟨H, hHnormal, hHelem, x, hHne, hHminimal, hHp, hCp,
    hcomm, hxout, hdata⟩

end CFSG.Glauberman
