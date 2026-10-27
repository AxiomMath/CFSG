module

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.GroupTheory.CommutatorCentralizerIn
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.CoprimeActionSupport.CoprimeSeries
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5
open CFSG.GroupTheory (commutatorCentralizerIn mem_commutatorCentralizerIn)
open CFSG.GroupTheory.CoprimeActionSupport (commutator_mem_of_coprime_of_commutator_mem)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private noncomputable def oTwoQuot_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    oTwoQuot X ≃* oTwoQuot Y :=
  QuotientGroup.congr (pCore 2 X) (pCore 2 Y) e (CFSG.pCore_map_iso 2 e)

private abbrev vertexCentralizer (L Q Z : Subgroup G) : Subgroup G :=
  (L ⊔ Q) ⊓ Subgroup.centralizer ((Z ⊓ Q : Subgroup G) : Set G)

private abbrev vertexCentralizerMod (L Q Z : Subgroup G)
    (h : L ⊔ Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G)) : Subgroup G :=
  commutatorCentralizerIn (L ⊔ Q) (Z ⊓ Q) Q h

private theorem le_normalizer_commutatorCentralizerIn {M C T N : Subgroup G}
    (hMC : M ≤ Subgroup.normalizer (C : Set G)) (hNC : N ≤ Subgroup.normalizer (C : Set G))
    (hNM : N ≤ Subgroup.normalizer (M : Set G)) (hNT : N ≤ Subgroup.normalizer (T : Set G)) :
    N ≤ Subgroup.normalizer (commutatorCentralizerIn M C T hMC : Set G) := by
  refine (Subgroup.le_normalizer_iff).mpr fun g hg x hx => ?_
  obtain ⟨hxM, hxT⟩ := (mem_commutatorCentralizerIn hMC).mp hx
  have hgxM : g * x * g⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hNM hg) x).mp hxM
  refine (mem_commutatorCentralizerIn hMC).mpr ⟨hgxM, fun t ht => ?_⟩
  have ht' : g⁻¹ * t * g ∈ T := by
    have h := (Subgroup.mem_normalizer_iff.mp (hNT hg) (g⁻¹ * t * g)).mpr ?_
    · exact h
    simpa [mul_assoc] using ht
  have hconj : g * ⁅x, g⁻¹ * t * g⁆ * g⁻¹ ∈ C :=
    (Subgroup.mem_normalizer_iff.mp (hNC hg) _).mp (hxT _ ht')
  have hid : ⁅g * x * g⁻¹, t⁆ = g * ⁅x, g⁻¹ * t * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rwa [hid]

private theorem le_sup_pCoreOf_of_inf_of_simple {M C D0 : Subgroup G}
    (hC : C ≤ M) (hCN : M ≤ Subgroup.normalizer (C : Set G))
    (hD0N : M ≤ Subgroup.normalizer (D0 : Set G))
    (hsimple : IsSimpleGroup (oTwoQuot ↥M)) (hne : ¬ C ⊓ D0 ≤ pCoreOf 2 M) :
    M ≤ (C ⊓ D0) ⊔ pCoreOf 2 M := by
  classical
  let π : ↥M →* oTwoQuot ↥M := QuotientGroup.mk' (pCore 2 ↥M)
  have hN : ((C ⊓ D0).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans hC)).mpr
      (F7.le_normalizer_inf hCN hD0N)
  have hNmap : (((C ⊓ D0).subgroupOf M).map π).Normal :=
    hN.map π (QuotientGroup.mk'_surjective _)
  have hne' : ((C ⊓ D0).subgroupOf M).map π ≠ ⊥ := by
    intro hbot
    apply hne
    intro x hx
    have hxM : x ∈ M := hC hx.1
    have hmem : π ⟨x, hxM⟩ ∈ ((C ⊓ D0).subgroupOf M).map π :=
      Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hbot] at hmem
    have h1 : (QuotientGroup.mk ⟨x, hxM⟩ : oTwoQuot ↥M) = 1 := by
      simpa [π] using (Subgroup.mem_bot.mp hmem)
    have h2 : (⟨x, hxM⟩ : ↥M) ∈ pCore 2 ↥M := (QuotientGroup.eq_one_iff _).mp h1
    have h2' : (⟨x, hxM⟩ : ↥M) ∈ (pCoreOf 2 M).subgroupOf M := by
      rwa [CFSG.openPCoreOf_subgroupOf 2 M]
    exact Subgroup.mem_subgroupOf.mp h2'
  have htop : ((C ⊓ D0).subgroupOf M).map π = ⊤ := by
    haveI : (((C ⊓ D0).subgroupOf M).map π).Normal := hNmap
    rcases hsimple.eq_bot_or_eq_top_of_normal (((C ⊓ D0).subgroupOf M).map π) with h | h
    · exact absurd h hne'
    · exact h
  intro x hx
  have hmem : π ⟨x, hx⟩ ∈ ((C ⊓ D0).subgroupOf M).map π := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hmem
  have h1 : (n⁻¹ * ⟨x, hx⟩ : ↥M) ∈ pCore 2 ↥M := by
    have h0 : (QuotientGroup.mk (s := pCore 2 ↥M) (n⁻¹ * ⟨x, hx⟩) : oTwoQuot ↥M) = 1 := by
      change (QuotientGroup.mk' (pCore 2 ↥M)) (n⁻¹ * ⟨x, hx⟩) = 1
      rw [map_mul, map_inv, hnx, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (n⁻¹ * ⟨x, hx⟩)).mp h0
  have h2 : ((n⁻¹ * ⟨x, hx⟩ : ↥M) : G) ∈ pCoreOf 2 M := by
    have h1' : (n⁻¹ * ⟨x, hx⟩ : ↥M) ∈ (pCoreOf 2 M).subgroupOf M := by
      rwa [CFSG.openPCoreOf_subgroupOf 2 M]
    exact Subgroup.mem_subgroupOf.mp h1'
  have hx' : x = (n : G) * ((n⁻¹ * ⟨x, hx⟩ : ↥M) : G) := by simp
  rw [hx']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hn) h2

private theorem le_of_sup_eq_of_isPGroup {M Q X D : Subgroup G}
    (hXM : X ≤ M) (hXN : M ≤ Subgroup.normalizer (X : Set G)) (hXQ : X ⊔ Q = M)
    (hQ : IsPGroup 2 Q) (hDM : D ≤ M) (hDodd : Odd (Nat.card D)) :
    D ≤ X := by
  classical
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hQM : Q ≤ M := hXQ ▸ le_sup_right
  have hQN : Q ≤ Subgroup.normalizer (X : Set G) := hQM.trans hXN
  have hrel : X.relIndex M = X.relIndex Q := by
    rw [← hXQ, sup_comm]
    exact F1.relIndex_sup_eq_of_le_normalizer hQN
  have hdvd : X.relIndex M ∣ 2 ^ n := by
    rw [hrel, ← Subgroup.inf_relIndex_right X Q, ← hn]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  intro x hx
  have hxM : x ∈ M := hDM hx
  have hodd : Odd (orderOf x) :=
    hDodd.of_dvd_nat (by simpa using orderOf_dvd_natCard (⟨x, hx⟩ : ↥D))
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.zpowers_le.mpr (hDM hx)).trans hXN
  have hrel1 : X.relIndex (X ⊔ Subgroup.zpowers x) ∣ orderOf x := by
    rw [sup_comm, F1.relIndex_sup_eq_of_le_normalizer hxN,
      ← Subgroup.inf_relIndex_right X (Subgroup.zpowers x), ← Nat.card_zpowers]
    exact Subgroup.relIndex_dvd_card _ _
  have hYX : X ⊔ Subgroup.zpowers x ≤ M := sup_le hXM (Subgroup.zpowers_le.mpr hxM)
  have hmul : X.relIndex (X ⊔ Subgroup.zpowers x) * (X ⊔ Subgroup.zpowers x).relIndex M =
      X.relIndex M := Subgroup.relIndex_mul_relIndex X (X ⊔ Subgroup.zpowers x) M le_sup_left hYX
  have hrel2 : X.relIndex (X ⊔ Subgroup.zpowers x) ∣ 2 ^ k :=
    ⟨_, by rw [hmul, hk]⟩
  have hcop : Nat.Coprime (X.relIndex (X ⊔ Subgroup.zpowers x)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hodd.of_dvd_nat hrel1))
  have h1 : X.relIndex (X ⊔ Subgroup.zpowers x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hrel2
  exact (Subgroup.relIndex_eq_one.mp h1) (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

private structure CentralizerData (L Q Z D P S : Subgroup G) : Prop where
  hQ : Q = pCoreOf 2 P
  hLP : L ≤ P
  hPN : P ≤ Subgroup.normalizer (L : Set G)
  hQN : Q ≤ Subgroup.normalizer (Z : Set G)
  hZN : Z ≤ Subgroup.normalizer (Q : Set G)
  hZab : Z ≤ Subgroup.centralizer (Z : Set G)
  hZS : Z ≤ S
  hSL : S = (S ⊓ L) ⊔ Q
  hDL : D ≤ L
  hDodd : Odd (Nat.card D)
  hDne : D ≠ ⊥
  hChar : CharTwo P
  hsimple : IsSimpleGroup (oTwoQuot ↥(L ⊔ Q))
  hZnotQ : ¬ Z ≤ Q

private theorem pCoreOf_sup_eq {L Q Z D P S : Subgroup G} (hd : CentralizerData L Q Z D P S) :
    pCoreOf 2 (L ⊔ Q) = Q := by
  have hQleP : Q ≤ P := hd.hQ ▸ pCoreOf_le 2 P
  have hQP : P ≤ Subgroup.normalizer (Q : Set G) := hd.hQ ▸ le_normalizer_pCoreOf 2 P
  have hLβP : L ⊔ Q ≤ P := sup_le hd.hLP hQleP
  refine le_antisymm ?_ ?_
  · have h := le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 (L ⊔ Q)).trans hLβP) ?_
      (pCoreOf_isPGroup 2 (L ⊔ Q))
    · rwa [← hd.hQ] at h
    · exact (F1.le_normalizer_sup hd.hPN hQP).trans
        (normalizer_le_normalizer_pCoreOf 2 (L ⊔ Q))
  · refine le_pCoreOf_of_le_normalizer 2 le_sup_right (hQP.trans' hLβP) ?_
    exact hd.hQ ▸ pCoreOf_isPGroup 2 P

private theorem normalizer_inf_of_data {L Q Z D P S : Subgroup G}
    (hd : CentralizerData L Q Z D P S) (h : L ≤ vertexCentralizer L Q Z ⊔ Q) :
    Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G) ∧
      L ⊔ Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G) ∧
      ∀ z ∈ Z, ∀ q ∈ Q, z * q * z⁻¹ * q⁻¹ ∈ (Z ⊓ Q : Subgroup G) := by
  have hWQn : Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G) :=
    F7.le_normalizer_inf hd.hQN Subgroup.le_normalizer
  have hWLβ : L ⊔ Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G) := by
    refine sup_le ?_ hWQn
    refine h.trans (sup_le (inf_le_right.trans
      (Subgroup.centralizer_le_normalizer ((Z ⊓ Q : Subgroup G) : Set G))) hWQn)
  refine ⟨hWQn, hWLβ, fun z hz q hq => ?_⟩
  have h1 : z * q * z⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hd.hZN hz) q).mp hq
  have h2 : q * z⁻¹ * q⁻¹ ∈ Z := by
    have := (Subgroup.mem_normalizer_iff.mp (hd.hQN hq) z⁻¹).mp (Z.inv_mem hz)
    simpa [mul_assoc] using this
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hid : z * q * z⁻¹ * q⁻¹ = z * (q * z⁻¹ * q⁻¹) := by group
    rw [hid]
    exact Z.mul_mem hz h2
  · have hid : z * q * z⁻¹ * q⁻¹ = (z * q * z⁻¹) * q⁻¹ := by group
    rw [hid]
    exact Q.mul_mem h1 (Q.inv_mem hq)

private theorem Z_le_inf_of_data {L Q Z D P S : Subgroup G} (hd : CentralizerData L Q Z D P S)
    (hWLβ : L ⊔ Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G))
    (hcomm : ∀ z ∈ Z, ∀ q ∈ Q, z * q * z⁻¹ * q⁻¹ ∈ (Z ⊓ Q : Subgroup G)) :
    Z ≤ vertexCentralizer L Q Z ∧ Z ≤ vertexCentralizerMod L Q Z hWLβ := by
  have hZLβ : Z ≤ L ⊔ Q := by
    refine hd.hZS.trans ?_
    rw [hd.hSL]
    exact sup_le (inf_le_right.trans le_sup_left) le_sup_right
  refine ⟨le_inf hZLβ ?_, fun z hz => ?_⟩
  · refine hd.hZab.trans (Subgroup.centralizer_le ?_)
    exact fun x hx => (Subgroup.mem_inf.mp hx).1
  · exact (mem_commutatorCentralizerIn hWLβ).mpr
      ⟨hZLβ hz, fun q hq => by simpa only [commutatorElement_def] using hcomm z hz q hq⟩

private theorem normalizer_centralizers {L Q Z D P S : Subgroup G}
    (hd : CentralizerData L Q Z D P S)
    (hWLβ : L ⊔ Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G)) :
    L ⊔ Q ≤ Subgroup.normalizer (vertexCentralizer L Q Z : Set G) ∧
      L ⊔ Q ≤ Subgroup.normalizer (vertexCentralizerMod L Q Z hWLβ : Set G) := by
  have hQP : P ≤ Subgroup.normalizer (Q : Set G) := hd.hQ ▸ le_normalizer_pCoreOf 2 P
  have hLβP : L ⊔ Q ≤ P := sup_le hd.hLP (hd.hQ ▸ pCoreOf_le 2 P)
  refine ⟨?_, ?_⟩
  · refine F7.le_normalizer_inf (X := L ⊔ Q) (A := L ⊔ Q)
      (B := Subgroup.centralizer ((Z ⊓ Q : Subgroup G) : Set G))
      Subgroup.le_normalizer ?_
    exact hWLβ.trans (F7.normalizer_le_normalizer_centralizer (Z ⊓ Q))
  · exact le_normalizer_commutatorCentralizerIn hWLβ hWLβ Subgroup.le_normalizer
      (hQP.trans' hLβP)

private theorem sup_inf_cover {L Q Z D P S : Subgroup G} (hd : CentralizerData L Q Z D P S)
    (hWLβ : L ⊔ Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G))
    (hZC : Z ≤ vertexCentralizer L Q Z) (hZD0 : Z ≤ vertexCentralizerMod L Q Z hWLβ)
    (hCN : L ⊔ Q ≤ Subgroup.normalizer (vertexCentralizer L Q Z : Set G))
    (hD0N : L ⊔ Q ≤ Subgroup.normalizer (vertexCentralizerMod L Q Z hWLβ : Set G)) :
    L ⊔ Q ≤ vertexCentralizer L Q Z ⊓ vertexCentralizerMod L Q Z hWLβ ⊔ Q := by
  have hne : ¬ vertexCentralizer L Q Z ⊓ vertexCentralizerMod L Q Z hWLβ ≤
      pCoreOf 2 (L ⊔ Q) := by
    intro hle
    apply hd.hZnotQ
    intro z hz
    have h3 : z ∈ pCoreOf 2 (L ⊔ Q) := hle ⟨hZC hz, hZD0 hz⟩
    rwa [pCoreOf_sup_eq hd] at h3
  have hcover := le_sup_pCoreOf_of_inf_of_simple (M := L ⊔ Q) (C := vertexCentralizer L Q Z)
    (D0 := vertexCentralizerMod L Q Z hWLβ) inf_le_left hCN hD0N hd.hsimple hne
  rwa [pCoreOf_sup_eq hd] at hcover

private theorem D_le_inf {L Q Z D P S : Subgroup G} (hd : CentralizerData L Q Z D P S)
    (hWLβ : L ⊔ Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G))
    (hCN : L ⊔ Q ≤ Subgroup.normalizer (vertexCentralizer L Q Z : Set G))
    (hD0N : L ⊔ Q ≤ Subgroup.normalizer (vertexCentralizerMod L Q Z hWLβ : Set G))
    (hcover : L ⊔ Q ≤ vertexCentralizer L Q Z ⊓ vertexCentralizerMod L Q Z hWLβ ⊔ Q) :
    D ≤ vertexCentralizer L Q Z ⊓ vertexCentralizerMod L Q Z hWLβ := by
  refine le_of_sup_eq_of_isPGroup (M := L ⊔ Q)
    (X := vertexCentralizer L Q Z ⊓ vertexCentralizerMod L Q Z hWLβ) (Q := Q) (D := D)
    (inf_le_left.trans inf_le_left) (F7.le_normalizer_inf hCN hD0N)
    (show vertexCentralizer L Q Z ⊓ vertexCentralizerMod L Q Z hWLβ ⊔ Q = L ⊔ Q from
      le_antisymm (sup_le (inf_le_left.trans inf_le_left) le_sup_right) hcover)
    (hd.hQ ▸ pCoreOf_isPGroup 2 P) (hd.hDL.trans le_sup_left) hd.hDodd

private theorem odd_mem_centralizer_of_data {L Q Z D P S : Subgroup G}
    (hd : CentralizerData L Q Z D P S)
    (hWLβ : L ⊔ Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G)) {y : G}
    (hyD : y ∈ D) (hyC : y ∈ vertexCentralizer L Q Z)
    (hyD0 : y ∈ vertexCentralizerMod L Q Z hWLβ) :
    y ∈ Subgroup.centralizer (Q : Set G) := by
  have hodd : Odd (orderOf y) :=
    hd.hDodd.of_dvd_nat (by simpa using orderOf_dvd_natCard (⟨y, hyD⟩ : ↥D))
  have hcentQ : ∀ q ∈ Q, y * q * y⁻¹ * q⁻¹ = 1 := by
    have hcop : (orderOf y).Coprime 2 := Nat.coprime_two_right.mpr hodd
    have hmain := commutator_mem_of_coprime_of_commutator_mem (p := 2)
      (P := Q) (W := (Z ⊓ Q : Subgroup G)) (Z := ⊥)
      ((hd.hQ ▸ pCoreOf_isPGroup 2 P).to_le inf_le_right)
      (fun _ _ => by rw [Subgroup.mem_normalizer_iff]; intro w; simp) hcop
      (by rw [Subgroup.mem_normalizer_iff]; intro w; simp)
      (fun x hx => by
        have h := ((mem_commutatorCentralizerIn hWLβ).mp hyD0).2 x hx
        simpa only [commutatorElement_def] using h)
      (fun w hw => by
        have hc := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyC).2 w hw).symm
        rw [Subgroup.mem_bot, show y * w = w * y from hc]
        group)
    intro q hq
    have := hmain q hq
    rwa [Subgroup.mem_bot] at this
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h := hcentQ q hq
  have hid : y * q = (y * q * y⁻¹ * q⁻¹) * (q * y) := by group
  rw [hid, h, one_mul]

private theorem false_of_data {L Q Z D P S : Subgroup G} (hd : CentralizerData L Q Z D P S)
    (hWLβ : L ⊔ Q ≤ Subgroup.normalizer ((Z ⊓ Q : Subgroup G) : Set G))
    (hle : D ≤ vertexCentralizer L Q Z ⊓ vertexCentralizerMod L Q Z hWLβ) : False := by
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hd.hDne
  set y : G := (z : G) with hy
  have hyD : y ∈ D := z.2
  have hy1 : y ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hyX := hle hyD
  have hycent := odd_mem_centralizer_of_data hd hWLβ hyD hyX.1 hyX.2
  have hyP : y ∈ P :=
    (sup_le hd.hLP (hd.hQ ▸ pCoreOf_le 2 P)) (hd.hDL.trans le_sup_left hyD)
  have hycent' : y ∈ Subgroup.centralizer (pCoreOf 2 P : Set G) := by rwa [← hd.hQ]
  have hyQ : y ∈ Q := by
    have := hd.hChar ⟨hyP, hycent'⟩
    rwa [← hd.hQ] at this
  have hDQ : D ⊓ Q = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard (H := D) (K := Q) ?_).eq_bot
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hd.hQ ▸ pCoreOf_isPGroup 2 P)
    rw [hn]
    exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hd.hDodd)
  have hybot : y ∈ (⊥ : Subgroup G) := hDQ ▸ Subgroup.mem_inf.mpr ⟨hyD, hyQ⟩
  exact hy1 ((Subgroup.mem_bot).mp hybot)

private theorem not_le_centralizer_sup_of_vertex {L Q Z D P S : Subgroup G}
    (hd : CentralizerData L Q Z D P S) : ¬ L ≤ vertexCentralizer L Q Z ⊔ Q := by
  intro h
  obtain ⟨-, hWLβ, hcomm⟩ := normalizer_inf_of_data hd h
  obtain ⟨hZC, hZD0⟩ := Z_le_inf_of_data hd hWLβ hcomm
  obtain ⟨hCN, hD0N⟩ := normalizer_centralizers hd hWLβ
  have hcover := sup_inf_cover hd hWLβ hZC hZD0 hCN hD0N
  exact false_of_data hd hWLβ (D_le_inf hd hWLβ hCN hD0N hcover)

private theorem bigB_le_sup (L1 L2 S : Subgroup G) : bigB L1 L2 S ≤ L1 ⊔ L2 ⊔ S := by
  rw [bigB]
  exact sup_le (sup_le ((F1.borelOf_le L1 S).trans (le_sup_left.trans le_sup_left))
    ((F1.borelOf_le L2 S).trans (le_sup_right.trans le_sup_left))) le_sup_right

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private noncomputable def oTwoQuot_sup_Qv_one_def {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    oTwoQuot ↥(L2 ⊔ t.Qv 1) ≃* oTwoQuot ↥L2 := by
  have h1 : oTwoQuot ↥(L2 ⊔ Q1 L2 L1 S) ≃* oTwoQuot ↥L2 :=
    oTwoQuotSupEquiv (L1 := L2) (L2 := L1) (S := S) (Hyp111.symm hfr.hF.1)
  have hsub : (L2 ⊔ Q1 L2 L1 S : Subgroup G) = (L2 ⊔ t.Qv 1) := by
    rw [t.Qv_one]
    simp only [Q1, Q2, P1, P2]
    rw [bigB_comm]
  exact (oTwoQuot_congr (MulEquiv.subgroupCongr hsub)).symm.trans h1

private theorem Zv_zero_not_le_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h : L2 ≤ vertexCentralizer L2 (t.Qv 1) (t.Zv 0) ⊔ t.Qv 1) :
    ¬ t.Zv 0 ≤ t.Qv 1 := by
  intro hZ
  have hF : F112HypW L1 L2 S := hfr.hF
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (t.Zv 0 : Set G) := by
    rw [← t.Gv_zero]
    exact t.Gv_le_normalizer_Zv 0
  have hSN : S ≤ Subgroup.normalizer (t.Zv 0 : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)).trans hP1N
  have hQ1S : t.Qv 0 ≤ S := by
    rw [t.Qv_zero]
    exact Q1_le_S hF
  have hQ2N : t.Qv 1 ≤ Subgroup.normalizer (t.Zv 0 : Set G) := by
    have h : t.Qv 1 ≤ S := by
      rw [t.Qv_one]
      exact Q2_le_S hF
    exact h.trans hSN
  have hL2N : L2 ≤ Subgroup.normalizer (t.Zv 0 : Set G) := by
    have hC : vertexCentralizer L2 (t.Qv 1) (t.Zv 0) ≤
        Subgroup.normalizer (t.Zv 0 : Set G) := by
      refine inf_le_right.trans ?_
      rw [show (t.Zv 0 ⊓ t.Qv 1 : Subgroup G) = t.Zv 0 from inf_eq_left.mpr hZ]
      exact Subgroup.centralizer_le_normalizer (t.Zv 0 : Set G)
    exact h.trans (sup_le hC hQ2N)
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (t.Zv 0 : Set G) :=
    sup_le (sup_le ((le_sup_left : L1 ≤ P1 L1 L2 S).trans hP1N) hL2N) hSN
  have hZle : t.Zv 0 ≤ L1 ⊔ L2 ⊔ S :=
    (t.Zv_le_Qv 0).trans (hQ1S.trans ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (bigB_le_sup L1 L2 S)))
  have hle := le_pCoreOf_of_le_normalizer 2 hZle hG0N (t.isPGroup_Zv 0)
  rw [hF.1.o2] at hle
  exact t.Zv_ne_bot hF 0 (le_bot_iff.mp hle)

private theorem Zv_one_not_le_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (h : L1 ≤ vertexCentralizer L1 (t.Qv 0) (t.Zv 1) ⊔ t.Qv 0) :
    ¬ t.Zv 1 ≤ t.Qv 0 := by
  intro hZ
  have hF : F112HypW L1 L2 S := hfr.hF
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (t.Zv 1 : Set G) := by
    rw [← t.Gv_one]
    exact t.Gv_le_normalizer_Zv 1
  have hSN : S ≤ Subgroup.normalizer (t.Zv 1 : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)).trans hP2N
  have hQ2S : t.Qv 1 ≤ S := by
    rw [t.Qv_one]
    exact Q2_le_S hF
  have hQ1N : t.Qv 0 ≤ Subgroup.normalizer (t.Zv 1 : Set G) := by
    have h : t.Qv 0 ≤ S := by
      rw [t.Qv_zero]
      exact Q1_le_S hF
    exact h.trans hSN
  have hL1N : L1 ≤ Subgroup.normalizer (t.Zv 1 : Set G) := by
    have hC : vertexCentralizer L1 (t.Qv 0) (t.Zv 1) ≤
        Subgroup.normalizer (t.Zv 1 : Set G) := by
      refine inf_le_right.trans ?_
      rw [show (t.Zv 1 ⊓ t.Qv 0 : Subgroup G) = t.Zv 1 from inf_eq_left.mpr hZ]
      exact Subgroup.centralizer_le_normalizer (t.Zv 1 : Set G)
    exact h.trans (sup_le hC hQ1N)
  have hG0N : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (t.Zv 1 : Set G) :=
    sup_le (sup_le hL1N ((le_sup_left : L2 ≤ P2 L1 L2 S).trans hP2N)) hSN
  have hZle : t.Zv 1 ≤ L1 ⊔ L2 ⊔ S :=
    (t.Zv_le_Qv 1).trans (hQ2S.trans ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (bigB_le_sup L1 L2 S)))
  have hle := le_pCoreOf_of_le_normalizer 2 hZle hG0N (t.isPGroup_Zv 1)
  rw [hF.1.o2] at hle
  exact t.Zv_ne_bot hF 1 (le_bot_iff.mp hle)

private theorem charTwo_P1 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    CharTwo (t.Gv 0) := by
  have h := hfr.hF.1.h1.charTwo
  have heq : t.Gv 0 = L1 ⊔ S ⊔ borelOf L2 S := by
    rw [t.Gv_zero]
    show L1 ⊔ bigB L1 L2 S = L1 ⊔ S ⊔ borelOf L2 S
    have hb : L1 ⊔ borelOf L1 S = L1 := sup_eq_left.mpr (F1.borelOf_le L1 S)
    calc L1 ⊔ (borelOf L1 S ⊔ borelOf L2 S ⊔ S)
        = (L1 ⊔ borelOf L1 S) ⊔ (borelOf L2 S ⊔ S) := by ac_rfl
      _ = L1 ⊔ (borelOf L2 S ⊔ S) := by rw [hb]
      _ = L1 ⊔ S ⊔ borelOf L2 S := by ac_rfl
  rw [heq]
  exact h

private theorem charTwo_P2 {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    CharTwo (t.Gv 1) := by
  have h := hfr.hF.1.h2.charTwo
  have heq : t.Gv 1 = L2 ⊔ S ⊔ borelOf L1 S := by
    rw [t.Gv_one]
    show L2 ⊔ bigB L1 L2 S = L2 ⊔ S ⊔ borelOf L1 S
    have hb : L2 ⊔ borelOf L2 S = L2 := sup_eq_left.mpr (F1.borelOf_le L2 S)
    calc L2 ⊔ (borelOf L1 S ⊔ borelOf L2 S ⊔ S)
        = (L2 ⊔ borelOf L2 S) ⊔ (borelOf L1 S ⊔ S) := by ac_rfl
      _ = L2 ⊔ (borelOf L1 S ⊔ S) := by rw [hb]
      _ = L2 ⊔ S ⊔ borelOf L1 S := by ac_rfl
  rw [heq]
  exact h

private theorem simple_oTwoQuot_sup_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : IsSimpleGroup (oTwoQuot ↥(L2 ⊔ t.Qv 1)) := by
  haveI : IsSimpleGroup (oTwoQuot ↥L2) := by
    obtain ⟨e⟩ := hfr.hL2
    haveI : IsSimpleGroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hKcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
        GaloisField.card (p := 2) (n := f) (by have h := hfr.hf; omega)
      have hq4 : 4 ≤ Nat.card (GaloisField 2 f) := by
        rw [hKcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
      exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq4
    exact MulEquiv.isSimpleGroup e
  exact MulEquiv.isSimpleGroup (t.oTwoQuot_sup_Qv_one_def hfr)

private theorem simple_oTwoQuot_sup_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : IsSimpleGroup (oTwoQuot ↥(L1 ⊔ t.Qv 0)) := by
  haveI : IsSimpleGroup (oTwoQuot ↥L1) := by
    obtain ⟨e⟩ := hfr.hSz
    haveI : IsSimpleGroup (Sz a) :=
      CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup hfr.ha
    exact MulEquiv.isSimpleGroup e
  have h1 : oTwoQuot ↥(L1 ⊔ Q1 L1 L2 S) ≃* oTwoQuot ↥L1 := oTwoQuotSupEquiv hfr.hF.1
  have hsub : (L1 ⊔ Q1 L1 L2 S : Subgroup G) = (L1 ⊔ t.Qv 0) := by rw [t.Qv_zero]
  exact MulEquiv.isSimpleGroup ((oTwoQuot_congr (MulEquiv.subgroupCongr hsub)).symm.trans h1)

private theorem D2_ne_bot {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.D2 ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card t.D2 = 1 := by
    rw [hbot]
    exact Subgroup.card_bot
  rw [t.card_D2 hfr] at h1
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hfr.hf
  omega

private theorem D1_ne_bot {a f : ℕ} (hfr : Frame L1 L2 S a f) :
    t.D1 ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card t.D1 = 1 := by
    rw [hbot]
    exact Subgroup.card_bot
  rw [t.card_D1 hfr] at h1
  have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by have h := hfr.ha; omega)
  omega

theorem not_le_centralizer_sup_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    ¬ L2 ≤ ((L2 ⊔ t.Qv 1) ⊓ centralizer ((t.Zv 0 ⊓ t.Qv 1 : Subgroup G) : Set G)) ⊔
      t.Qv 1 := by
  have hF : F112HypW L1 L2 S := hfr.hF
  have hB2N : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    have h := bigB_le_normalizer_of_hyp111 (Hyp111.symm hF.1)
    rwa [bigB_comm] at h
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (t.Zv 0 : Set G) := by
    rw [← t.Gv_zero]
    exact t.Gv_le_normalizer_Zv 0
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (t.Qv 1 : Set G) := by
    rw [← t.Gv_one]
    exact t.Gv_le_normalizer_Qv 1
  have hSN : S ≤ Subgroup.normalizer (t.Zv 0 : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)).trans hP1N
  have hQ1S : t.Qv 0 ≤ S := by
    rw [t.Qv_zero]
    exact Q1_le_S hF
  have hQN : t.Qv 1 ≤ Subgroup.normalizer (t.Zv 0 : Set G) := by
    have h : t.Qv 1 ≤ S := by
      rw [t.Qv_one]
      exact Q2_le_S hF
    exact h.trans hSN
  intro h
  refine not_le_centralizer_sup_of_vertex (S := S) ⟨t.Qv_eq 1, ?_, ?_, hQN, ?_, ?_, ?_, ?_,
    ?_, t.hD2hall.2.1, t.D2_ne_bot hfr, t.charTwo_P2 hfr, t.simple_oTwoQuot_sup_Qv_one hfr,
    t.Zv_zero_not_le_Qv_one hfr h⟩ h
  · rw [t.Gv_one]
    exact le_sup_left
  · rw [t.Gv_one]
    exact sup_le Subgroup.le_normalizer hB2N
  · exact (t.Zv_le_Qv 0).trans
      (hQ1S.trans (((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)).trans hP2N))
  · exact (t.Zv_le_centralizer 0).trans
      (Subgroup.centralizer_le (fun x hx => t.Zv_le_Qv 0 hx))
  · exact (t.Zv_le_Qv 0).trans hQ1S
  · rw [t.Qv_one]
    exact S_eq_sup_right hfr
  · exact (show t.D2 ≤ borelOf L2 S from by rw [t.hD2sup]; exact le_sup_right).trans
      (F1.borelOf_le L2 S)

theorem not_le_centralizer_sup_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    ¬ L1 ≤ ((L1 ⊔ t.Qv 0) ⊓ centralizer ((t.Zv 1 ⊓ t.Qv 0 : Subgroup G) : Set G)) ⊔
      t.Qv 0 := by
  have hF : F112HypW L1 L2 S := hfr.hF
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (t.Zv 1 : Set G) := by
    rw [← t.Gv_one]
    exact t.Gv_le_normalizer_Zv 1
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (t.Qv 0 : Set G) := by
    rw [← t.Gv_zero]
    exact t.Gv_le_normalizer_Qv 0
  have hSN : S ≤ Subgroup.normalizer (t.Zv 1 : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)).trans hP2N
  have hQ2S : t.Qv 1 ≤ S := by
    rw [t.Qv_one]
    exact Q2_le_S hF
  have hQN : t.Qv 0 ≤ Subgroup.normalizer (t.Zv 1 : Set G) := by
    have h : t.Qv 0 ≤ S := by
      rw [t.Qv_zero]
      exact Q1_le_S hF
    exact h.trans hSN
  intro h
  refine not_le_centralizer_sup_of_vertex (S := S) ⟨t.Qv_eq 0, ?_, ?_, hQN, ?_, ?_, ?_, ?_,
    ?_, t.hD1hall.2.1, t.D1_ne_bot hfr, t.charTwo_P1 hfr, t.simple_oTwoQuot_sup_Qv_zero hfr,
    t.Zv_one_not_le_Qv_zero hfr h⟩ h
  · rw [t.Gv_zero]
    exact le_sup_left
  · rw [t.Gv_zero]
    exact sup_le Subgroup.le_normalizer (bigB_le_normalizer_of_hyp111 hF.1)
  · exact (t.Zv_le_Qv 1).trans
      (hQ2S.trans (((le_sup_right : S ≤ bigB L1 L2 S).trans
        (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)).trans hP1N))
  · exact (t.Zv_le_centralizer 1).trans
      (Subgroup.centralizer_le (fun x hx => t.Zv_le_Qv 1 hx))
  · exact (t.Zv_le_Qv 1).trans hQ2S
  · rw [t.Qv_zero]
    exact S_eq_sup_left hfr
  · exact (show t.D1 ≤ borelOf L1 S from by rw [t.hD1sup]; exact le_sup_right).trans
      (F1.borelOf_le L1 S)

end Track

end CFSG.Quasithin.Stroth.Rq

end
