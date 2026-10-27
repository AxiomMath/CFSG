module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Order
public import CFSG.Quasithin.Vol2.GoldschmidtF431Syl
public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam.Completion

universe u v w w'

section Card

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem orderOf_amalgamMap_of_mem₁ (C : F431Comp M1 M2 b1 b2) {i : Mb} (hi : i ∈ M1) :
    orderOf (amalgamMap b1 b2 i) = orderOf i := by
  rw [amalgamMap_of_mem₁ b1 b2 hi, orderOf_injective b1 C.inj₁]
  exact (Subgroup.orderOf_coe (⟨i, hi⟩ : M1)).symm

theorem exists_centralizer_hom {K : Subgroup Mb} (bK : K →* M) (hbK : Function.Injective bK)
    (hφK : ∀ (a : Mb) (h : a ∈ K), amalgamMap b1 b2 a = bK ⟨a, h⟩) {w : Mb}
    (hwK : Subgroup.centralizer ({w} : Set Mb) ≤ K)
    (hcent : Subgroup.centralizer ({amalgamMap b1 b2 w} : Set M) ≤ bK.range) :
    ∃ ψ : Subgroup.centralizer ({w} : Set Mb) →* M, Function.Injective ψ ∧
      ψ.range = Subgroup.centralizer ({amalgamMap b1 b2 w} : Set M) ∧
      (∀ hmem : w ∈ Subgroup.centralizer ({w} : Set Mb), ψ ⟨w, hmem⟩ = amalgamMap b1 b2 w) ∧
      (∀ x : Subgroup.centralizer ({w} : Set Mb), ψ x = amalgamMap b1 b2 (x : Mb)) := by
  have hw0 : w ∈ Subgroup.centralizer ({w} : Set Mb) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hwK' : w ∈ K := hwK hw0
  refine ⟨bK.comp (Subgroup.inclusion hwK), hbK.comp (Subgroup.inclusion_injective hwK), ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨c, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hφK w hwK']
      have hc : (c : Mb) * w = w * (c : Mb) := Subgroup.mem_centralizer_singleton_iff.mp c.2
      show bK (Subgroup.inclusion hwK c) * bK ⟨w, hwK'⟩ =
        bK ⟨w, hwK'⟩ * bK (Subgroup.inclusion hwK c)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hc
    · intro hx
      obtain ⟨y, rfl⟩ := hcent hx
      have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
      rw [hφK w hwK', ← map_mul, ← map_mul] at hx'
      have hy := hbK hx'
      have hy' : (y : Mb) * w = w * (y : Mb) := congrArg Subtype.val hy
      exact ⟨⟨y.1, Subgroup.mem_centralizer_singleton_iff.mpr hy'⟩, rfl⟩
  · intro hmem
    show bK (Subgroup.inclusion hwK ⟨w, hmem⟩) = _
    rw [hφK w hwK']
    rfl
  · intro x
    have hxK : (x : Mb) ∈ K := hwK x.2
    show bK (Subgroup.inclusion hwK x) = _
    rw [hφK _ hxK]
    rfl

end Card

section CardEq

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem F431LieK.card_eq (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hnf : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    (hcent₁ : ∀ i ∈ I, Subgroup.centralizer ({i} : Set Mb) ≤ M1 →
      Subgroup.centralizer ({amalgamMap b1 b2 i} : Set M) ≤ b1.range)
    (hcent₂ : ∀ i ∈ I, Subgroup.centralizer ({i} : Set Mb) ≤ M2 →
      Subgroup.centralizer ({amalgamMap b1 b2 i} : Set M) ≤ b2.range) :
    Nat.card Mb = Nat.card M := by
  classical
  have hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range ∨
      Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b2.range := by
    rcases D.cent_z with h | h
    · exact Or.inl (hcent₁ z D.z_mem h)
    · exact Or.inr (hcent₂ z D.z_mem h)
  have hSyl1 : IsSylowTwoOf T M1 := F7.isSylowTwoOf_mono_right D.sylow D.T_le₁ le_top
  have hSyl2 : IsSylowTwoOf T M2 := F7.isSylowTwoOf_mono_right D.sylow D.T_le₂ le_top
  obtain ⟨z', hz'I, hz'ne⟩ := Finset.exists_mem_ne (show 1 < I.card from D.two_le) z
  have hzo := D.order_two z D.z_mem
  have hz'o := D.order_two z' hz'I
  have huz : ¬ IsConj z z' := by
    intro h
    obtain ⟨w, -, huniq⟩ := D.rep z hzo
    exact hz'ne ((huniq z' ⟨hz'I, h.symm⟩).trans (huniq z ⟨D.z_mem, IsConj.refl z⟩).symm)
  have hφord : ∀ i ∈ I, orderOf (amalgamMap b1 b2 i) = 2 := fun i hi => by
    rw [orderOf_amalgamMap_of_mem₁ C (D.T_le₁ (D.mem_T i hi))]
    exact D.order_two i hi
  have hnc : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 z') :=
    hnf z D.z_mem z' hz'I hz'ne.symm
  have hT' : ∀ w ∈ I.image (amalgamMap b1 b2), orderOf w = 2 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact hφord i hi
  have hTrep' : ∀ x : M, orderOf x = 2 →
      ∃! w, w ∈ I.image (amalgamMap b1 b2) ∧ IsConj w x := by
    intro x hx
    obtain ⟨i, hiI, hic⟩ := D.exists_conj_image C hb hx
    refine ⟨amalgamMap b1 b2 i, ⟨Finset.mem_image_of_mem _ hiI, hic⟩, ?_⟩
    rintro w ⟨hwT, hwc⟩
    obtain ⟨j, hjI, rfl⟩ := Finset.mem_image.mp hwT
    by_cases hij : i = j
    · rw [hij]
    · exact absurd (hic.trans hwc.symm) (hnf i hiI j hjI hij)
  have hinj : Set.InjOn (amalgamMap b1 b2) (I : Set Mb) := by
    intro i hi j hj hij
    by_contra hne
    exact hnf i hi j hj hne (by rw [hij])
  refine card_eq_of_transversal_data hzo hz'o huz (hφord z D.z_mem) (hφord z' hz'I) hnc I
    D.order_two D.rep (I.image (amalgamMap b1 b2)) hT' hTrep' (amalgamMap b1 b2) hinj
    (fun w' => Finset.mem_image) D.z_mem hz'I rfl rfl ?_
  intro w hw
  rcases D.cent w hw with h | h
  · obtain ⟨ψ, hψi, hψr, hψw, hψx⟩ := exists_centralizer_hom b1 C.inj₁
      (fun a ha => amalgamMap_of_mem₁ b1 b2 ha) h (hcent₁ w hw h)
    refine ⟨ψ, hψi, hψr, hψw, fun x hxo => ?_, fun x hxo => ?_⟩
    · rw [hψx x]
      exact D.fusion_in C hnf hSyl1 (fun a ha b hb => amalgamMap_mul₁ b1 b2 ha hb)
        (D.mem_T z D.z_mem) hzo (h x.2) hxo
    · rw [hψx x]
      exact D.fusion_in C hnf hSyl1 (fun a ha b hb => amalgamMap_mul₁ b1 b2 ha hb)
        (D.mem_T z' hz'I) hz'o (h x.2) hxo
  · obtain ⟨ψ, hψi, hψr, hψw, hψx⟩ := exists_centralizer_hom b2 C.inj₂
      (fun a ha => amalgamMap_of_mem₂ b1 b2 C.agree ha) h (hcent₂ w hw h)
    refine ⟨ψ, hψi, hψr, hψw, fun x hxo => ?_, fun x hxo => ?_⟩
    · rw [hψx x]
      exact D.fusion_in C hnf hSyl2 (fun a ha b hb => amalgamMap_mul₂ b1 b2 C.agree ha hb)
        (D.mem_T z D.z_mem) hzo (h x.2) hxo
    · rw [hψx x]
      exact D.fusion_in C hnf hSyl2 (fun a ha b hb => amalgamMap_mul₂ b1 b2 C.agree ha hb)
        (D.mem_T z' hz'I) hz'o (h x.2) hxo

end CardEq

theorem nonempty_mulEquiv_of_normal_range {X Ġ : Type*} [Group X] [Group Ġ] [IsSimpleGroup Ġ]
    (hnab : ∃ a b : Ġ, a * b ≠ b * a) (ν : X →* Ġ) (hinj : Function.Injective ν)
    (hnorm : ν.range.Normal) (hcent : Subgroup.centralizer (ν.range : Set Ġ) = ⊥) :
    Nonempty (X ≃* Ġ) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ν.range with hbot | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.centralizer (ν.range : Set Ġ) := by
      rw [hbot]
      intro x hx
      have : x = 1 := by simpa using hx
      rw [this, one_mul, mul_one]
    rw [hcent] at hb
    have : b = 1 := by simpa using hb
    exact hab (by rw [this, mul_one, one_mul])
  · exact ⟨MulEquiv.ofBijective ν ⟨hinj, fun g => by
      have : g ∈ ν.range := by rw [htop]; exact Subgroup.mem_top g
      exact this⟩⟩

end CFSG.Quasithin.H13.F431
