module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S29

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem M_eq_K_sup_normalizer (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) :
    m.M = m.K ⊔ (m.M ⊓ normalizer (m.Z : Set G)) := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hZp : IsPGroup m.r m.Z := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact m.card_Z)
  obtain ⟨S, hS, hZS⟩ := exists_isSylowOf_ge m.Z_le_K hZp
  have hScyc : IsCyclic ↥S := m.isCyclic_of_isSylowOf hcyc hS
  have hFr : m.M = m.K ⊔ (m.M ⊓ normalizer (S : Set G)) :=
    frattini_of_isSylowOf m.K_le_M (fun g hg => m.mem_normalizer_K hg) hS
  have hNS : ∀ n ∈ normalizer (S : Set G), n ∈ normalizer (m.Z : Set G) := by
    intro n hn
    refine mem_normalizer_of_forward_uc6 fun w hw => ?_
    set Z' : Subgroup G := m.Z.map (MulAut.conj n).toMonoidHom with hZ'
    have hZ'S : Z' ≤ S := by
      rintro _ ⟨z, hz, rfl⟩
      have := (mem_normalizer_iff.1 hn z).1 (hZS hz)
      simpa [MulAut.conj_apply] using this
    have hcard : Nat.card Z' = Nat.card m.Z := by
      rw [hZ', Subgroup.card_map_of_injective (MulAut.conj n).injective]
    have hZZ' : Z' = m.Z := eq_of_card_eq_of_isCyclic hScyc hZ'S hZS hcard
    rw [← hZZ']
    exact ⟨w, hw, by simp [MulAut.conj_apply]⟩
  refine le_antisymm ?_ (sup_le m.K_le_M inf_le_left)
  calc m.M = m.K ⊔ (m.M ⊓ normalizer (S : Set G)) := hFr
    _ ≤ m.K ⊔ (m.M ⊓ normalizer (m.Z : Set G)) :=
      sup_le_sup_left (fun x hx => ⟨hx.1, hNS x hx.2⟩) _

theorem not_dvd_index_K {p : ℕ} (hp : p ∈ Dat.sig)
    (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) (h626 : m.C626) :
    ¬ p ∣ (m.K.subgroupOf m.M).index := by
  classical
  have hFr := m.M_eq_K_sup_normalizer hcyc
  set K' : Subgroup ↥m.M := m.K.subgroupOf m.M with hK'
  set N' : Subgroup ↥m.M := (m.M ⊓ normalizer (m.Z : Set G)).subgroupOf m.M with hN'
  have htop : (⊤ : Subgroup ↥m.M).map m.M.subtype = m.M := by
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype _
  have hKN' : K' ⊔ N' = ⊤ := by
    apply Subgroup.map_injective m.M.subtype_injective
    rw [Subgroup.map_sup, hK', hN', Subgroup.map_subgroupOf_eq_of_le m.K_le_M,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left, htop]
    exact hFr.symm
  haveI hK'n : K'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer m.K_le_M).2
      (fun g hg => m.mem_normalizer_K hg)
  have hidx : K'.index = K'.relIndex N' := by
    rw [← Subgroup.relIndex_top_right, ← hKN', Subgroup.relIndex_sup_left]
  have hidxdvd : K'.index ∣ Nat.card N' := by
    rw [hidx]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card (H := K') (K := N'))
  have hN'card : Nat.card N' = Nat.card ↥(m.M ⊓ normalizer (m.Z : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  exact fun hd => h626 p hp (hN'card ▸ hd.trans hidxdvd)

theorem sylow_le_K {p : ℕ} (hp : p ∈ Dat.sig)
    (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) (h626 : m.C626) {P : Subgroup G}
    (hP : IsSylowOf p P m.M) : P ≤ m.K := by
  classical
  have hpr : p.Prime := (Dat.sig_prime _ hp).1
  haveI : Fact p.Prime := ⟨hpr⟩
  set K' : Subgroup ↥m.M := m.K.subgroupOf m.M with hK'
  haveI hK'n : K'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer m.K_le_M).2
      (fun g hg => m.mem_normalizer_K hg)
  have hpidx : ¬ p ∣ K'.index := m.not_dvd_index_K hp hcyc h626
  obtain ⟨Q, rfl⟩ := hP
  intro x hx
  obtain ⟨⟨y, hyM⟩, hyQ, rfl⟩ := hx
  have hy : (⟨y, hyM⟩ : ↥m.M) ∈ (Q : Subgroup ↥m.M) := hyQ
  obtain ⟨k, hk⟩ := Q.isPGroup' ⟨⟨y, hyM⟩, hy⟩
  have hord : orderOf (⟨y, hyM⟩ : ↥m.M) ∣ p ^ k := by
    have h1 : orderOf (⟨⟨y, hyM⟩, hy⟩ : (Q : Subgroup ↥m.M)) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at h1
  have hq : orderOf (QuotientGroup.mk (⟨y, hyM⟩ : ↥m.M) : ↥m.M ⧸ K') ∣ p ^ k :=
    (orderOf_map_dvd (QuotientGroup.mk' K') _).trans hord
  have hq2 : orderOf (QuotientGroup.mk (⟨y, hyM⟩ : ↥m.M) : ↥m.M ⧸ K') ∣ K'.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ k) K'.index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hpr).2 hpidx)
  have h1 : orderOf (QuotientGroup.mk (⟨y, hyM⟩ : ↥m.M) : ↥m.M ⧸ K') = 1 :=
    Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hq) hq2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
