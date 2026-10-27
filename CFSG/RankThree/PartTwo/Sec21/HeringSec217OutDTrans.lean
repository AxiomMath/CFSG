module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217DTrans

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup

@[expose] def neg1 : M2 := (2, 0, 0, 2)

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem core_check_out : ∀ U V : M2, ap U (1, 0) = (1, 0) → ap U (0, 1) ≠ (0, 1) →
    (∀ x, (ap U)^[8] x = x) → ap V (0, 1) = (0, 1) → ap V (1, 0) ≠ (1, 0) →
    (∀ x, (ap V)^[8] x = x) →
    mm U V ≠ neg1 → mm (mm U V) (mm U V) ≠ neg1 → mm (mm (mm U V) (mm U V)) (mm U V) ≠ neg1 →
    ∃ d : ZMod 3 × ZMod 3, d ≠ 0 ∧ ap U d = -d ∧ ap V d = -d ∧ ap (mm U V) d = d ∧
      (∃ v : ZMod 3 × ZMod 3, ap (mm U V) v = v + d) ∧
        ∀ v : ZMod 3 × ZMod 3, ∃ k : ZMod 3, ap (mm U V) v = v + (k * d.1, k * d.2) := by
  decide +kernel

theorem ap_neg1 (x : ZMod 3 × ZMod 3) : ap neg1 x = -x := by
  simp only [ap, neg1]
  ext <;> simp <;> ring_nf <;> decide +revert

section DTransOut

variable {G : Type*} [Group G] {a c : G}

variable (hca : c * a = a * c) (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1) (ha1 : a ≠ 1) (hc1 : c ≠ 1)
  (hnot : c ∉ Subgroup.zpowers a)
include hca ha3 hc3 ha1 hc1 hnot

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem transvection_on_D_out {u v t : G}
    (huN : u ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G))
    (hu : c * u = u * c) (hua : u ∉ Subgroup.centralizer ({a} : Set G))
    (hu8 : u ^ 8 ∈ Subgroup.centralizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G))
    (hvN : v ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G))
    (hv : a * v = v * a) (hvc : v ∉ Subgroup.centralizer ({c} : Set G))
    (hv8 : v ^ 8 ∈ Subgroup.centralizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G))
    (ht : t = u * v⁻¹)
    (hinv : ∀ n : ℕ, (n = 1 ∨ n = 2 ∨ n = 3) →
      ¬ ∀ δ ∈ zpowers a ⊔ zpowers c, t ^ n * δ * (t ^ n)⁻¹ = δ⁻¹) :
    ∃ d ∈ zpowers a ⊔ zpowers c, d ≠ 1 ∧ u * d * u⁻¹ = d⁻¹ ∧ v * d * v⁻¹ = d⁻¹ ∧
      t * d * t⁻¹ = d ∧ (∃ δ ∈ zpowers a ⊔ zpowers c, t * δ * t⁻¹ = δ * d) ∧
      ∀ δ ∈ zpowers a ⊔ zpowers c, ∃ n : ℕ, t * δ * t⁻¹ = δ * d ^ n := by
  have htN : t ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G) := by
    rw [ht]; exact Subgroup.mul_mem _ huN (Subgroup.inv_mem _ hvN)
  obtain ⟨fu, hfu⟩ := acts_exists hca ha3 hc3 huN
  obtain ⟨fv, hfv⟩ := acts_exists hca ha3 hc3 hvN
  obtain ⟨ft, hft⟩ := acts_exists hca ha3 hc3 htN
  have htv : t * v = u := by rw [ht]; group
  have hftv : Acts a c u (ft ∘ fv) := htv ▸ acts_mul hca ha3 hc3 ha1 hc1 hnot hft hfv
  have hfuw : ft ∘ fv = fu := acts_unique hca ha3 hc3 ha1 hc1 hnot hftv hfu
  have hadd_u := acts_add hca ha3 hc3 ha1 hc1 hnot hfu
  have hadd_v := acts_add hca ha3 hc3 ha1 hc1 hnot hfv
  have hadd_t := acts_add hca ha3 hc3 ha1 hc1 hnot hft
  set U := matOf fu with hU
  set V := matOf fv with hV
  have hfuU : ∀ y, fu y = ap U y := eq_ap_matOf hadd_u
  have hfvV : ∀ y, fv y = ap V y := eq_ap_matOf hadd_v
  have hu_c : fu (1, 0) = (1, 0) :=
    (acts_fixes_iff hca ha3 hc3 ha1 hc1 hnot hfu (kap_one_zero)).2 hu.symm
  have hu_a : fu (0, 1) ≠ (0, 1) := fun h => hua (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((acts_fixes_iff hca ha3 hc3 ha1 hc1 hnot hfu (kap_zero_one)).1 h))
  have hv_a : fv (0, 1) = (0, 1) :=
    (acts_fixes_iff hca ha3 hc3 ha1 hc1 hnot hfv (kap_zero_one)).2 hv.symm
  have hv_c : fv (1, 0) ≠ (1, 0) := fun h => hvc (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((acts_fixes_iff hca ha3 hc3 ha1 hc1 hnot hfv (kap_one_zero)).1 h))
  have hit : ∀ {g : G} {f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3}, Acts a c g f →
      g ^ 8 ∈ Subgroup.centralizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G) →
      ∀ y, f^[8] y = y := by
    intro g f hg h8 y
    have h1 := acts_pow hg 8
    have h1' : Acts a c (g ^ 8) id := fun w => by
      have hw : kap a c w ∈ zpowers a ⊔ zpowers c := (mem_D_iff hca ha3 hc3).2 ⟨w, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 h8 (kap a c w) hw
      show kap a c w = g ^ 8 * kap a c w * (g ^ 8)⁻¹
      rw [← this]
      group
    have h2 := acts_unique hca ha3 hc3 ha1 hc1 hnot h1 h1'
    exact congrFun h2 y
  have hfuU' : fu = ap U := funext hfuU
  have hfvV' : fv = ap V := funext hfvV
  have hu8' : ∀ y, (ap U)^[8] y = y := by rw [← hfuU']; exact hit hfu hu8
  have hv8' : ∀ y, (ap V)^[8] y = y := by rw [← hfvV']; exact hit hfv hv8
  rw [hfuU'] at hu_c hu_a
  rw [hfvV'] at hv_a hv_c
  have hVinv := involution_check V hv_a hv_c hv8'
  have hft_uv : ∀ y, ft y = ap (mm U V) y := by
    intro y
    have h1 : ft (fv (fv y)) = fu (fv y) := congrFun hfuw (fv y)
    rw [ap_mm, ← hfuU', ← hfvV']
    calc ft y = ft (fv (fv y)) := by rw [hfvV', hVinv]
      _ = fu (fv y) := h1
  have hft' : ft = ap (mm U V) := funext hft_uv
  have hnotneg : ∀ n : ℕ, (n = 1 ∨ n = 2 ∨ n = 3) → ∀ M : M2, (∀ y, ft^[n] y = ap M y) →
      M ≠ neg1 := by
    intro n hn M hM hMneg
    apply hinv n hn
    intro δ hδ
    obtain ⟨w, rfl⟩ := (mem_D_iff hca ha3 hc3).1 hδ
    have hA := acts_pow hft n w
    rw [hM w, hMneg, ap_neg1, kap_neg hca ha3 hc3] at hA
    exact hA.symm
  have hM1 : mm U V ≠ neg1 := hnotneg 1 (Or.inl rfl) (mm U V) (fun y => by
    rw [Function.iterate_one]; exact hft_uv y)
  have hM2 : mm (mm U V) (mm U V) ≠ neg1 := hnotneg 2 (Or.inr (Or.inl rfl)) _ (fun y => by
    rw [ap_mm, ← hft_uv, ← hft_uv]; rfl)
  have hM3 : mm (mm (mm U V) (mm U V)) (mm U V) ≠ neg1 :=
    hnotneg 3 (Or.inr (Or.inr rfl)) _ (fun y => by
      rw [ap_mm, ap_mm, ← hft_uv, ← hft_uv, ← hft_uv]; rfl)
  obtain ⟨d, hd0, hUd, hVd, hdfix, ⟨v0, hv0⟩, hall⟩ :=
    core_check_out U V hu_c hu_a hu8' hv_a hv_c hv8' hM1 hM2 hM3
  have hkd : ∀ w, t * kap a c w * t⁻¹ = kap a c (ap (mm U V) w) := fun w => by
    rw [← hft_uv, hft]
  refine ⟨kap a c d, (mem_D_iff hca ha3 hc3).2 ⟨d, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hd0
    exact kap_inj hca ha3 hc3 ha1 hc1 hnot (h.trans (kap_zero hca ha3 hc3).symm)
  · rw [← hfu d, hfuU', hUd, kap_neg hca ha3 hc3]
  · rw [← hfv d, hfvV', hVd, kap_neg hca ha3 hc3]
  · rw [hkd, hdfix]
  · refine ⟨kap a c v0, (mem_D_iff hca ha3 hc3).2 ⟨v0, rfl⟩, ?_⟩
    rw [hkd, hv0, kap_add hca ha3 hc3]
  · intro δ hδ
    obtain ⟨w, rfl⟩ := (mem_D_iff hca ha3 hc3).1 hδ
    obtain ⟨κ, hκ⟩ := hall w
    refine ⟨κ.val, ?_⟩
    have hsm : ((κ * d.1, κ * d.2) : ZMod 3 × ZMod 3) = κ.val • d := by
      ext <;> simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [hkd, hκ, hsm, kap_add hca ha3 hc3, kap_nsmul hca ha3 hc3]

end DTransOut

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
