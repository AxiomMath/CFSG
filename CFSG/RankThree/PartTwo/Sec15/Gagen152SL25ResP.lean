module

public import CFSG.RankThree.PartTwo.Sec15.Gagen152SL25ResCtx
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Mod
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

namespace Gagen152SL25Res

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_sup_pCoreOf {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X P K : Subgroup G}
    (hP : IsPGroup p P) (hPX : P ≤ X) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hle : P ≤ (K ⊓ (P ⊔ CFSG.Open.pCoreOf 2 X)) ⊔ CFSG.Open.pCoreOf 2 X) : P ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  set R := K ⊓ (P ⊔ Q) with hR
  set M := P ⊔ R with hM
  set N := R ⊔ Q with hN
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := hPX.trans hXQ
  have hPH : P ≤ Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.le_normalizer_sup (A := P) Subgroup.le_normalizer hPQ
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := Late.le_normalizer_inf hPK hPH
  have hdisj : Disjoint P Q :=
    IsPGroup.disjoint_of_ne p 2 hp2 P Q hP (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hHQ : P ⊔ Q ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hPQ Subgroup.le_normalizer
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) :=
    (hR ▸ inf_le_right : R ≤ P ⊔ Q).trans hHQ
  have hRM : R ≤ M := le_sup_right
  have hPM : P ≤ M := le_sup_left
  have hMN : M ≤ N := by
    rw [hM, hN]
    exact sup_le hle le_sup_left
  have hqcard : R.relIndex M * Nat.card R = Nat.card M := by
    have h := Subgroup.relIndex_mul_card R M
    rwa [inf_eq_left.mpr hRM] at h
  have hprodM : Nat.card M * Nat.card (P ⊓ R : Subgroup G) = Nat.card P * Nat.card R := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := P) (K := R) hPR
    rw [← hM] at h
    simpa [inf_comm] using h
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hqP : R.relIndex M * Nat.card (P ⊓ R : Subgroup G) = Nat.card P := by
    apply Nat.eq_of_mul_eq_mul_right hRpos
    calc
      (R.relIndex M * Nat.card (P ⊓ R : Subgroup G)) * Nat.card R
          = R.relIndex M * Nat.card R * Nat.card (P ⊓ R : Subgroup G) := by ring
      _ = Nat.card M * Nat.card (P ⊓ R : Subgroup G) := by rw [hqcard]
      _ = Nat.card P * Nat.card R := hprodM
  have hr : R.relIndex N ∣ Nat.card Q := by
    have hrN : R.relIndex N * Nat.card (R ⊓ Q : Subgroup G) = Nat.card Q := by
      have hcard : R.relIndex N * Nat.card R = Nat.card N := by
        have h := Subgroup.relIndex_mul_card R N
        rw [inf_eq_left.mpr (hRM.trans hMN)] at h
        exact h
      have hprod : Nat.card N * Nat.card (Q ⊓ R : Subgroup G) = Nat.card Q * Nat.card R := by
        have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
          (H := R) (K := Q) hRQ
        rw [← hN, inf_comm, mul_comm (Nat.card R) (Nat.card Q)] at h
        exact h
      apply Nat.eq_of_mul_eq_mul_right hRpos
      calc
        (R.relIndex N * Nat.card (R ⊓ Q : Subgroup G)) * Nat.card R
            = R.relIndex N * Nat.card R * Nat.card (R ⊓ Q : Subgroup G) := by ring
        _ = Nat.card N * Nat.card (R ⊓ Q : Subgroup G) := by rw [hcard]
        _ = Nat.card N * Nat.card (Q ⊓ R : Subgroup G) := by rw [inf_comm]
        _ = Nat.card Q * Nat.card R := hprod
    exact ⟨_, hrN.symm⟩
  have hqr : R.relIndex M ∣ R.relIndex N :=
    ⟨M.relIndex N, (Subgroup.relIndex_mul_relIndex (H := R) (K := M) (L := N) hRM hMN).symm⟩
  have hqP' : R.relIndex M ∣ Nat.card P := ⟨_, hqP.symm⟩
  have hqQ : R.relIndex M ∣ Nat.card Q := hqr.trans hr
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).exists_card_eq
  have hcop : Nat.Coprime (p ^ a) (2 ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes Fact.out Nat.prime_two).mpr hp2)
  have hq1 : R.relIndex M = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (ha ▸ hqP') (hb ▸ hqQ)
  have hMR : M ≤ R := Subgroup.relIndex_eq_one.mp hq1
  exact hPM.trans (hMR.trans inf_le_left)

theorem le_of_flag {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X P K Z N : Subgroup G}
    (hP : IsPGroup p P) (hV : Nat.card (↥P ⧸ frattini ↥P) = p ^ 2) (hPX : P ≤ X)
    (hXs : IsSimpleGroup (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hperf : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (h2 : 2 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hC : X ⊓ Subgroup.centralizer (P : Set G) ≤ oTwoOddIn X)
    (hHX : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G))
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hZX : Z ≤ X) (hZK : Z ≤ K)
    (hZcov : (Z.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤)
    (hNX : N ≤ X) (hNP : N ≤ Subgroup.normalizer (P : Set G))
    (hNK : N ≤ Subgroup.normalizer (K : Set G))
    (hNcov : (N.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤) :
    P ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  set R := K ⊓ (P ⊔ Q) with hR
  set U := P ⊓ (R ⊔ Q) with hU
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := hPX.trans hXQ
  have hPH : P ≤ Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.le_normalizer_sup (A := P) Subgroup.le_normalizer hPQ
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := Late.le_normalizer_inf hPK hPH
  have hNH : N ≤ Subgroup.normalizer ((P ⊔ Q : Subgroup G) : Set G) := hNX.trans hHX
  have hNR : N ≤ Subgroup.normalizer (R : Set G) := Late.le_normalizer_inf hNK hNH
  have hNRQ : N ≤ Subgroup.normalizer ((R ⊔ Q : Subgroup G) : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.le_normalizer_sup (A := N) hNR (hNX.trans hXQ)
  have hNU : N ≤ Subgroup.normalizer (U : Set G) := Late.le_normalizer_inf hNP hNRQ
  set ℓ := (U.subgroupOf P).map (QuotientGroup.mk' (frattini ↥P)) with hℓ
  have hℓdvd : Nat.card ℓ ∣ p ^ 2 := hV ▸ Subgroup.card_subgroup_dvd_card ℓ
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hℓdvd
  interval_cases k
  ·
    exfalso
    have hbot : ℓ = ⊥ := Subgroup.eq_bot_of_card_eq ℓ (by rw [hk, pow_zero])
    rw [hℓ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have hHmul : ((P ⊔ Q : Subgroup G) : Set G) = (P : Set G) * (Q : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right P Q hPQ
    refine Proof152FX.false_of_trivial_frattini_action hp2 hP hPX hXs h2 hZX hZcov hC hHX ?_
    intro z hz u hu
    have hzu : ⁅z, u⁆ ∈ R := by
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def, mul_assoc, mul_assoc]
        refine K.mul_mem (hZK hz) ?_
        have h1 := (Subgroup.mem_normalizer_iff.mp (hPK hu) _).mp (K.inv_mem (hZK hz))
        simpa [mul_assoc] using h1
      · have huH : u ∈ P ⊔ Q := Subgroup.mem_sup_left hu
        rw [commutatorElement_def]
        exact (P ⊔ Q).mul_mem ((Subgroup.mem_normalizer_iff.mp (hHX (hZX hz)) u).mp huH)
          ((P ⊔ Q).inv_mem huH)
    obtain ⟨v, hv, q, hq, hvq⟩ : ⁅z, u⁆ ∈ (P : Set G) * (Q : Set G) := hHmul ▸ hzu.2
    have hvq' : v * q = ⁅z, u⁆ := hvq
    have hvU : v ∈ U := by
      refine ⟨hv, ?_⟩
      have he : v = ⁅z, u⁆ * q⁻¹ := by rw [← hvq']; group
      rw [he]
      exact (R ⊔ Q).mul_mem (Subgroup.mem_sup_left hzu) (Subgroup.mem_sup_right (Q.inv_mem hq))
    have hvΦ : v ∈ (frattini ↥P).map P.subtype :=
      ⟨⟨v, hv⟩, hbot (Subgroup.mem_subgroupOf.mpr hvU), rfl⟩
    have hqu : u⁻¹ * q * u ∈ Q := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hXQ (hPX (P.inv_mem hu))) q).mp hq
      simpa using h1
    refine ⟨v, hvΦ, u⁻¹ * q * u, hqu, ?_⟩
    calc z * u * z⁻¹ = ⁅z, u⁆ * u := by rw [commutatorElement_def]; group
      _ = v * q * u := by rw [← hvq']
      _ = v * u * (u⁻¹ * q * u) := by group
  ·
    exfalso
    have hO2θ := Proof152F.oTwoOddIn_le_theta hXs h2
    have hCθ : ∀ (x : G) (hx : x ∈ X), x ∈ Subgroup.centralizer (P : Set G) →
        (⟨x, hx⟩ : ↥X) ∈ aschbacherSolvableCore 3 ↥X := by
      intro x hx hxc
      obtain ⟨y, hy, hyx⟩ := hO2θ (hC ⟨hx, hxc⟩)
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      exact this ▸ hy
    exact Proof152Flag.false_of_invariant_line hp2 hP hV
      (aschbacherSolvableCore 3 ↥X) hperf h2 hNX hNP hNcov hCθ hNU
      (by rw [hk, pow_one])
  ·
    have htop : ℓ = ⊤ := Subgroup.eq_top_of_card_eq ℓ (by rw [hk, hV])
    have hsup : U.subgroupOf P ⊔ frattini ↥P = ⊤ := by
      have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (frattini ↥P)) (U.subgroupOf P)
      rw [← hℓ, htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      exact h1.symm
    have hUtop : U.subgroupOf P = ⊤ := frattini_nongenerating hsup
    have hPU : P ≤ R ⊔ Q := by
      intro x hx
      have h1 : (⟨x, hx⟩ : ↥P) ∈ U.subgroupOf P := hUtop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp h1).2
    exact le_of_le_sup_pCoreOf hp2 hP hPX hPK (by simpa [hR] using hPU)

variable {A : Subgroup G} {c : G} {L M X B : Subgroup G} {b d : G} {Lb : Subgroup G} {p : ℕ}
  {P : Subgroup G} {e : G}

theorem ResCtx.le_K
    (h : ResCtx A c L M X B b d Lb p P e) {K : Subgroup G}
    (hXK : X ⊓ Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (K : Set G))
    {D : Subgroup G} (hDX : D ≤ X) (hDK : D ≤ K)
    (hDcov : (D.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤) :
    P ≤ K := by
  classical
  have : Fact p.Prime := ⟨h.pdata.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : p ≠ 3 := ne_of_gt h.three_lt
  have hP : IsPGroup p P := by
    rcases h.pdata.type_p with ⟨-, hc⟩ | ⟨-, hc⟩
    · exact IsPGroup.of_card hc
    · exact IsPGroup.of_card hc
  have hV := Proof152F.card_frattini_quot_eq h.pdata.type_p
  obtain ⟨hXs, hX60⟩ := Ronan152SL25.isSimpleGroup_theta_quotJ h.ctx
  have hperf : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    (isQuasisimple_theta_of_mem_thetaComponentsIn h.ctx.mem_comp).1
  have h2 : 2 ∣ Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) := by
    rw [hX60]; norm_num
  set W := X ⊓ Subgroup.normalizer (P : Set G) with hW
  have hWcov := Proof152F.map_inf_normalizer_eq_top hp3 h.pdata.char_p
  have heW : e ∈ Subgroup.normalizer (W : Set G) := by
    have heX : Subgroup.zpowers e ≤ Subgroup.normalizer (X : Set G) :=
      Subgroup.zpowers_le.mpr (h.ctx.norm_x h.mem_A)
    have heP : Subgroup.zpowers e ≤
        Subgroup.normalizer ((Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (Sec6.normalizer_le_normalizer_normalizer P (h.pdata.norm_p h.mem_A))
    exact Late.le_normalizer_inf heX heP (Subgroup.mem_zpowers e)
  have he3 : e ^ 3 = 1 := h.sec15R.toSec14Std.isE27.1.2 e h.mem_A
  have hNcov := Proof152Gen.map_inf_centralizer_eq_top (inf_le_left : W ≤ X) heW he3
    h.mem_thetaQuotCentralizer hWcov
  set N := W ⊓ Subgroup.centralizer ({e} : Set G) with hN
  have hNX : N ≤ X := inf_le_left.trans inf_le_left
  have hNP : N ≤ Subgroup.normalizer (P : Set G) := inf_le_left.trans inf_le_right
  have hNK : N ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hXK
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf h.pdata.le_px h.le_centralizer_e).trans hXK
  exact le_of_flag h.pdata.odd hP hV h.pdata.le_px hXs hperf h2 h.pdata.cent_p
    (Proof152FX.le_normalizer_sup_pCoreOf h.pdata.char_p) hPK hDX hDK hDcov
    hNX hNP hNK (by simpa [hN] using hNcov)

theorem ResCtx.le_theta (h : ResCtx A c L M X B b d Lb p P e) {K : Subgroup G}
    (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hKeq : K = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) K) (hPK : P ≤ K) :
    P ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  have : Fact p.Prime := ⟨h.pdata.prime⟩
  have hp3 : p ≠ 3 := ne_of_gt h.three_lt
  have hP : IsPGroup p P := by
    rcases h.pdata.type_p with ⟨-, hc⟩ | ⟨-, hc⟩
    · exact IsPGroup.of_card hc
    · exact IsPGroup.of_card hc
  have hA3 : IsPGroup 3 A := h.sec15R.toSec14Std.isE27.isPGroup
  have hB3 : IsPGroup 3 B := hA3.to_le h.hyp.1
  set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
  have hBθ : B ≤ Subgroup.normalizer (θK : Set G) :=
    hBK.trans (Sec6.normalizer_le_normalizer_theta K)
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := h.hyp.1.trans h.pdata.norm_p
  have hBC : B ≤ Subgroup.centralizer (lB A B : Set G) :=
    Subgroup.le_centralizer_iff.mp (CFSG.RankThree.PartTwo.Sec14.lB_le_centralizer A B)
  have hbB : b ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert b _)
  have hfr : P ⊓ Subgroup.centralizer (B : Set G) ≤ (frattini ↥P).map P.subtype := fun x hx =>
    h.fr ⟨hx.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB) hx.2⟩
  have hPθ : P ≤ P ⊓ θK := by
    refine Ronan152SL25.le_of_forall_commutator_mem (P₀ := P ⊓ θK) hp3 hP hB3 inf_le_left ?_ ?_ hfr
    · exact (le_inf hBP hBθ).trans Subgroup.inf_normalizer_le_normalizer_inf
    · intro x hx f hf
      refine ⟨?_, ?_⟩
      · have h1 : f * x⁻¹ * f⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp (hBP hf) _).mp (P.inv_mem hx)
        have hcom : ⁅x, f⁆ = x * (f * x⁻¹ * f⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [hcom]
        exact P.mul_mem hx h1
      · exact Ronan152SL25.commutator_mem_of_eq_sup hKeq (Sec6.theta_le K)
          (Sec6.le_normalizer_theta K) (hBθ hf) (hBC hf) (hPK hx)
  exact hPθ.trans inf_le_right

end Gagen152SL25Res

end CFSG.RankThree.PartTwo.Sec15
