module

public import CFSG.Sporadic.Co2Smith.GlNJG3
public import CFSG.Sporadic.Co2Smith.GlNJH1

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.RankThree.Co2 CFSG.Certificates

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section G

variable
  {G : Type} [Group G] {z : G} (φ : centralizer ({z} : Set G) ≃* Cz)

@[expose] noncomputable def phiInt (L : Subgroup G) : Subgroup K :=
  (L.comap (phiH φ)).map Cz.subtype

theorem mem_phiInt {L : Subgroup G} {x : K} :
    x ∈ phiInt φ L ↔ ∃ h : x ∈ Cz, phiH φ ⟨x, h⟩ ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem exists_NJComp_QKs [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) :
    ∃ L : Subgroup G, IsNJComp φ L ∧ ∃ s, (s = 0 ∨ s = 18 ∨ s = 76 ∨ s = 94) ∧
      ∀ y : Cz, phiH φ y ∈ L ↔ (y : K) ∈ QKs s := by
  obtain ⟨L, hL⟩ := exists_NJComp φ hz hφz
  have hCN : phiInt φ L ≤ normalizer (Jc : Set K) := by
    intro x hx
    obtain ⟨h, hxL⟩ := (mem_phiInt φ).1 hx
    exact (phiH_mem_NG_iff φ ⟨x, h⟩).1 (hL.le hxL)
  have hCz : phiInt φ L ≤ Cz := fun x hx => ((mem_phiInt φ).1 hx).1
  have hCJ : ∀ x ∈ phiInt φ L, x ∈ Jc → x = 1 := by
    intro x hx hJ
    obtain ⟨h, hxL⟩ := (mem_phiInt φ).1 hx
    have h1 := hL.inf _ hxL ((mem_JGc φ).2 ⟨_, hJ, rfl⟩)
    have h2 : (⟨x, h⟩ : Cz) = 1 := phiH_injective φ (h1.trans (map_one _).symm)
    exact congrArg Subtype.val h2
  have hCQ : ∀ q ∈ normalizer (Jc : Set K), q ∈ Cz → ∃ j ∈ Jc, j * q ∈ phiInt φ L := by
    intro q hq hqz
    obtain ⟨j, hj, l, hl, e⟩ := hL.sup _ (phiH_mem_NG φ (y := ⟨q, hqz⟩) hq)
    obtain ⟨w, hw, rfl⟩ := (mem_JGc φ).1 hj
    refine ⟨(w : K)⁻¹, inv_mem hw, (mem_phiInt φ).2 ⟨mul_mem (inv_mem w.2) hqz, ?_⟩⟩
    have e' : phiH φ ⟨(w : K)⁻¹ * q, mul_mem (inv_mem w.2) hqz⟩ = l := by
      have : (⟨(w : K)⁻¹ * q, mul_mem (inv_mem w.2) hqz⟩ : Cz) = w⁻¹ * ⟨q, hqz⟩ := rfl
      rw [this, map_mul, map_inv, e, inv_mul_cancel_left]
    rw [e']
    exact hl
  obtain ⟨n, -, s, hs, hC⟩ := exists_conj_QKs hCN hCz hCJ hCQ
  set c : Cz := ⟨jcElt n, Jc_le_Cz (jcElt_mem n)⟩
  set t := phiH φ c
  have htJ : t ∈ JGc φ := (mem_JGc φ).2 ⟨c, jcElt_mem n, rfl⟩
  have htN : t ∈ normalizer (JGc φ : Set G) := le_normalizer htJ
  refine ⟨L.map (MulAut.conj t).toMonoidHom, ⟨?_, ?_, ?_⟩, s, hs, fun y => ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem htN (hL.le hl)) (inv_mem htN)
  · rintro _ ⟨l, hl, rfl⟩ hJ
    have hlJ : l ∈ JGc φ := by
      have e : l = t⁻¹ * (t * l * t⁻¹) * t := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem htJ) hJ) htJ
    show t * l * t⁻¹ = 1
    rw [hL.inf l hl hlJ, mul_one, mul_inv_cancel]
  · intro m hm
    obtain ⟨j, hj, l, hl, e⟩ := hL.sup (t⁻¹ * m * t)
      (mul_mem (mul_mem (inv_mem htN) hm) htN)
    refine ⟨t * j * t⁻¹, (mem_normalizer_iff.1 htN j).1 hj, t * l * t⁻¹, ⟨l, hl, rfl⟩, ?_⟩
    calc m = t * (t⁻¹ * m * t) * t⁻¹ := by group
      _ = t * j * t⁻¹ * (t * l * t⁻¹) := by rw [e]; group
  · constructor
    · rintro ⟨l, hl, hle⟩
      have hle' : t * l * t⁻¹ = phiH φ y := hle
      have hlC : l = phiH φ (c⁻¹ * y * c) := by
        rw [map_mul, map_mul, map_inv, ← hle']
        show l = t⁻¹ * (t * l * t⁻¹) * t
        group
      rw [← hC]
      refine ⟨(c : K)⁻¹ * y * c, (mem_phiInt φ).2 ⟨(c⁻¹ * y * c).2, ?_⟩, ?_⟩
      · show phiH φ (c⁻¹ * y * c) ∈ L
        rw [← hlC]
        exact hl
      · show (c : K) * ((c : K)⁻¹ * y * c) * (c : K)⁻¹ = y
        group
    · intro hy
      rw [← hC] at hy
      obtain ⟨x, hx, hxe⟩ := hy
      obtain ⟨h, hxL⟩ := (mem_phiInt φ).1 hx
      refine ⟨phiH φ ⟨x, h⟩, hxL, ?_⟩
      show t * phiH φ ⟨x, h⟩ * t⁻¹ = phiH φ y
      have e : y = c * ⟨x, h⟩ * c⁻¹ := Subtype.ext hxe.symm
      rw [e, map_mul, map_mul, map_inv]

theorem piG_JGc [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    {g : normalizer (JGc φ : Set G)} (hg : (g : G) ∈ JGc φ) : piG φ hz g = 1 :=
  (chom_eq_one_iff (omG_injective φ) _ (stableG φ hz) g).2 fun k =>
    (elemTwo_JGc φ).2 _ hg _ (omG_mem φ k)

theorem piG_L_surj [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2) (hφz : φ (zH z) = z0C)
    {L : Subgroup G} (hL : IsNJComp φ L) {s : ℕ}
    (hLs : ∀ y : Cz, phiH φ y ∈ L ↔ (y : K) ∈ QKs s) {σ : Equiv.Perm (Fin 77)}
    (hσ : σ ∈ njAut) : ∃ g : normalizer (JGc φ : Set G), (g : G) ∈ L ∧ piG φ hz g = σ := by
  have e := eq_of_transitive_of_le (X := (L.subgroupOf (normalizer (JGc φ : Set G))).map
    (piG φ hz)) (A := njAut) 0 (by rintro _ ⟨g, -, rfl⟩; exact piG_mem_njAut φ hz g)
    (fun k => ?_) (fun τ hτ hτ0 => ?_)
  · rw [← e] at hσ
    obtain ⟨g, hg, rfl⟩ := hσ
    exact ⟨g, hg, rfl⟩
  · obtain ⟨n, hn, hne⟩ := exists_NG_conj φ hz k
    obtain ⟨j, hj, l, hl, e1⟩ := hL.sup n hn
    have hlN : l ∈ normalizer (JGc φ : Set G) := hL.le hl
    refine ⟨piG φ hz ⟨l, hlN⟩, ⟨⟨l, hlN⟩, hl, rfl⟩, ?_⟩
    have hnjl : (⟨n, hn⟩ : normalizer (JGc φ : Set G)) =
        ⟨j, le_normalizer hj⟩ * ⟨l, hlN⟩ := Subtype.ext e1
    have h1 : piG φ hz ⟨n, hn⟩ = piG φ hz ⟨l, hlN⟩ := by
      rw [hnjl, map_mul, piG_JGc φ hz hj, one_mul]
    rw [← h1]
    apply omG_injective φ
    rw [piG_spec, omG_zero φ hφz]
    exact hne
  · obtain ⟨q, hq, e1⟩ := exists_QKs_piK s ⟨hτ, hτ0⟩
    have hqz : (q : K) ∈ Cz := QKs_le_Cz s hq
    refine ⟨⟨phiH φ ⟨q, hqz⟩, phiH_mem_NG φ q.2⟩, (hLs ⟨q, hqz⟩).2 hq, ?_⟩
    rw [piG_phiH φ hz ⟨q, hqz⟩ q.2]
    exact e1

end G

end CFSG.Sporadic.Co2Smith
