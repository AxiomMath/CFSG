module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_normalizes_cent {M V : Subgroup G} (hMV : M ≤ normalizer (V : Set G)) :
    M ≤ normalizer ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_inf, mem_centralizer_iff]
  have hV1 : ∀ h, h ∈ V → m⁻¹ * h * m ∈ V := fun h hh => by
    have := (mem_normalizer_iff.1 (hMV (M.inv_mem hm))) h
    simpa using this.1 hh
  have hV2 : ∀ h, h ∈ V → m * h * m⁻¹ ∈ V := fun h hh => (mem_normalizer_iff.1 (hMV hm)) h |>.1 hh
  constructor
  · rintro ⟨hxM, hxc⟩
    refine ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), fun h hh => ?_⟩
    have hc : (m⁻¹ * h * m) * x = x * (m⁻¹ * h * m) := hxc _ (hV1 h hh)
    calc h * (m * x * m⁻¹) = m * ((m⁻¹ * h * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * h * m)) * m⁻¹ := by rw [hc]
      _ = m * x * m⁻¹ * h := by group
  · rintro ⟨hxM, hxc⟩
    refine ⟨?_, fun h hh => ?_⟩
    · have := M.mul_mem (M.mul_mem (M.inv_mem hm) hxM) hm
      simpa [mul_assoc] using this
    · have hc : (m * h * m⁻¹) * (m * x * m⁻¹) = (m * x * m⁻¹) * (m * h * m⁻¹) := hxc _ (hV2 h hh)
      have := congrArg (fun y => m⁻¹ * y * m) hc
      simpa [mul_assoc] using this

theorem uc22p22u_mem_normalizer_sup {A B : Subgroup G} {m : G} (hA : m ∈ normalizer (A : Set G))
    (hB : m ∈ normalizer (B : Set G)) : m ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ (S : Subgroup G), m ∈ normalizer (S : Set G) → S.map (MulAut.conj m).toMonoidHom = S := by
    intro S hS
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hS y).1 hy
    · intro hx
      refine ⟨m⁻¹ * x * m, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have hm' := mem_normalizer_iff.1 (inv_mem hS) x
      simpa using hm'.1 hx
  rw [mem_normalizer_iff]
  intro x
  have hmap : (A ⊔ B).map (MulAut.conj m).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, key A hA, key B hB]
  constructor
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have := (MulAut.conj m).injective (a₁ := y) (a₂ := x)
      exact this (by simpa [MulAut.conj_apply] using hyx)
    rwa [this] at hy

theorem uc22p22u_pCore_le_cent {M T V : Subgroup G} (hW : InCalW M T V) :
    pCoreOf 2 M ≤ centralizer (V : Set G) := by
  have hMV : M ≤ normalizer (V : Set G) := hW.1.1.2.2.1
  set O := pCoreOf 2 M with hO
  set H := M ⊓ centralizer (V : Set G) with hH
  have hOM : O ≤ M := uc22p21c_pCoreOf_le M
  have hMO : M ≤ normalizer (O : Set G) := by
    have hn : (O.subgroupOf M).Normal := by
      rw [hO, CFSG.openPCoreOf_subgroupOf 2 M]
      exact CFSG.pCore_normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hOM).1 hn
  have hMH : M ≤ normalizer (H : Set G) := uc22p22u_normalizes_cent hMV
  set J := O ⊔ H with hJ
  have hJM : J ≤ M := sup_le hOM inf_le_left
  have hOJ : O ≤ J := le_sup_left
  have hHJ : H ≤ J := le_sup_right
  have hOn : (O.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOJ).2 (hJM.trans hMO)
  have hHn : (H.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHJ).2 (hJM.trans hMH)
  have hsup : O.subgroupOf J ⊔ H.subgroupOf J = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOJ hHJ, ← hJ, Subgroup.subgroupOf_self]
  have hidx : (H.subgroupOf J).index = (H.subgroupOf J).relIndex (O.subgroupOf J) := by
    have h1 := Subgroup.relIndex_sup_right (H := O.subgroupOf J) (K := H.subgroupOf J)
    rw [hsup, Subgroup.relIndex_top_right] at h1
    exact h1
  have hOp : IsPGroup 2 ↥(O.subgroupOf J) := (uc22p21c_isPGroup_pCoreOf M).comap_subtype
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (H.subgroupOf J).index = 2 ^ n := by
    rw [hidx]
    unfold Subgroup.relIndex
    exact IsPGroup.index (G := ↥(O.subgroupOf J)) hOp _
  have hdvd : ((centralizer (V : Set G)).subgroupOf J).index ∣ (H.subgroupOf J).index :=
    Subgroup.relIndex_dvd_of_le_left J (inf_le_right : H ≤ centralizer (V : Set G))
  rw [hn] at hdvd
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hred := hW.2.2 J hJM (fun m hm => uc22p22u_mem_normalizer_sup (hMO hm) (hMH hm)) hHJ ⟨m, hm⟩
  exact hOJ.trans hred

theorem uc22p22u_barImage_normal {M X : Subgroup G} (hn : M ≤ normalizer (X : Set G)) :
    (barImage M X).Normal := by
  refine ⟨fun q hq q' => ?_⟩
  obtain ⟨x, hx, rfl⟩ := uc22p21c_mem_barImage.1 hq
  obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective M q'
  refine uc22p21c_mem_barImage.2 ⟨m * x * m⁻¹, ?_, by simp⟩
  have := (mem_normalizer_iff.1 (hn m.2)) (x : G)
  exact this.1 hx

theorem uc22p22u_barPreimage_normalizes {M : Subgroup G} {D : Subgroup (Bar2 M)} [hD : D.Normal] :
    M ≤ normalizer ((barPreimage M D : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨hyM, hyD⟩ := uc22p21c_mem_barPreimage.1 hy
    have hmem : m * y * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)
    refine uc22p21c_mem_barPreimage.2 ⟨hmem, ?_⟩
    have e : (⟨m * y * m⁻¹, hmem⟩ : ↥M) = ⟨m, hm⟩ * ⟨y, hyM⟩ * ⟨m, hm⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact hD.conj_mem _ hyD _
  · intro hy
    obtain ⟨hyM, hyD⟩ := uc22p21c_mem_barPreimage.1 hy
    have hy' : y ∈ M := by
      have := M.mul_mem (M.mul_mem (M.inv_mem hm) hyM) hm
      simpa [mul_assoc] using this
    refine uc22p21c_mem_barPreimage.2 ⟨hy', ?_⟩
    have e : (⟨m * y * m⁻¹, hyM⟩ : ↥M) = ⟨m, hm⟩ * ⟨y, hy'⟩ * ⟨m, hm⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at hyD
    have := hD.conj_mem _ hyD ((uc22p21cPi M ⟨m, hm⟩)⁻¹)
    simpa [mul_assoc] using this

theorem uc22p22u_barImage_pCore (M : Subgroup G) : barImage M (pCoreOf 2 M) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
  rw [Subgroup.mem_bot]
  obtain ⟨y, hy, hyx⟩ := hm
  have : y = m := Subtype.ext hyx
  exact (QuotientGroup.eq_one_iff m).2 (this ▸ hy)

theorem uc22p22u_barPreimage_le {M X : Subgroup G} (hO : pCoreOf 2 M ≤ X) {D : Subgroup (Bar2 M)}
    (hD : D ≤ barImage M X) : barPreimage M D ≤ X := by
  intro y hy
  obtain ⟨hyM, hyD⟩ := uc22p21c_mem_barPreimage.1 hy
  obtain ⟨x, hx, hxy⟩ := uc22p21c_mem_barImage.1 (hD hyD)
  have h1 : (x⁻¹ * ⟨y, hyM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    change uc22p21cPi M (x⁻¹ * ⟨y, hyM⟩) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 : (x : G)⁻¹ * y ∈ pCoreOf 2 M := ⟨_, h1, rfl⟩
  have h3 : y = (x : G) * ((x : G)⁻¹ * y) := by group
  rw [h3]
  exact X.mul_mem hx (hO h2)

end CFSG.LocalAnalysis.UniquenessCase.UC22
