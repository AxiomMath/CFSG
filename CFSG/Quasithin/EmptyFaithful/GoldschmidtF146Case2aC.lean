module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2aB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2aA

public section

namespace CFSG.Quasithin.F146Field

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Case2a

variable {G : Type} [Group G] {T M H K : Subgroup G}

theorem kerIn_le_H (M H : Subgroup G) : kerIn (H ⊓ M) H ≤ H := kerIn_le.trans inf_le_left

theorem Setting.pCore_le_kerIn (c : Setting T M H K) : pCoreOf 2 H ≤ kerIn (H ⊓ M) H := by
  intro x hx
  refine (c.ker x).mpr ⟨Subgroup.mem_sup_right hx, fun y hy => ?_⟩
  have hyH : y ∈ H :=
    sup_le c.le_H (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hy
  have hyN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hyH
  have h1 : y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp ((pCoreOf 2 H).inv_mem hx)
  simpa [mul_assoc] using (pCoreOf 2 H).mul_mem hx h1

section Fin

variable [Finite G]

theorem Setting.conj_mem (c : Setting T M H K) {a p : G} (ha : a ∈ kerIn (H ⊓ M) H) (haK : a ∈ K)
    (hp : p ∈ T ⊓ K) : a * p * a⁻¹ ∈ T ⊓ K := by
  have h1 : a * p * a⁻¹ * p⁻¹ ∈ pCoreOf 2 H :=
    ((c.ker a).mp ha).2 p (Subgroup.mem_sup_left hp.2)
  have h2 : a * p * a⁻¹ * p⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem haK hp.2) (K.inv_mem haK)) (K.inv_mem hp.2)
  have h3 : a * p * a⁻¹ * p⁻¹ ∈ T ⊓ K := ⟨c.pCore_le h1, h2⟩
  simpa [mul_assoc] using (T ⊓ K).mul_mem h3 hp

theorem Setting.le_normalizer_inf (c : Setting T M H K) :
    kerIn (H ⊓ M) H ⊓ K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => c.conj_mem ha.1 ha.2 hh, fun hh => ?_⟩
  have := c.conj_mem (inv_mem ha.1) (inv_mem ha.2) hh
  simpa [mul_assoc] using this

theorem star_inf_eq (c : Setting T M H K)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) = E2.star (H ⊓ M) H K ⊓
      Subgroup.normalizer ((E2.star (H ⊓ M) H (T ⊓ K) : Subgroup (E2.StarQuot (H ⊓ M) H)) :
        Set (E2.StarQuot (H ⊓ M) H)) := by
  obtain ⟨S₀, hS₀, hBeq⟩ := hB
  have hPs : IsSylowTwoOf (E2.star (H ⊓ M) H (T ⊓ K)) (E2.star (H ⊓ M) H K) :=
    isSylowTwoOf_star c.le_H c.sylow_inf
  have hPle : E2.star (H ⊓ M) H (T ⊓ K) ≤ E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) :=
    GoldS146R.imgJ_mono (inf_le_inf_right K c.le_inf)
  have hS₀C : IsSylowTwoOf S₀ (E2.star (H ⊓ M) H K ⊓ Subgroup.normalizer (S₀ : Set _)) :=
    B6.isSylowTwoOf_mono hS₀ (le_inf hS₀.1 Subgroup.le_normalizer) inf_le_left
  have hle : E2.star (H ⊓ M) H (T ⊓ K) ≤ S₀ :=
    le_of_le_normalizer hS₀C inf_le_right hPs.2.1 (hBeq ▸ hPle)
  have hS : S₀ = E2.star (H ⊓ M) H (T ⊓ K) := hPs.eq_of_le hle hS₀.1 hS₀.2.1
  rw [hBeq, hS]

theorem borel_le (c : Setting T M H K)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ M := by
  rintro x ⟨hxK, hxN⟩
  have hxH : x ∈ H := c.le_H hxK
  have hJH := kerIn_le_H M H
  have hmem : ((⟨x, hxH⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
      E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) := by
    rw [star_inf_eq c hB]
    refine ⟨(mem_star_iff c.le_H hJH _).mpr (Subgroup.mem_sup_left hxK),
      mk_mem_normalizer_star (inf_le_right.trans c.le_H) hJH hxN⟩
  rw [mem_star_iff (inf_le_left.trans inf_le_left) hJH] at hmem
  exact ((sup_le inf_le_left kerIn_le : (H ⊓ M) ⊓ K ⊔ kerIn (H ⊓ M) H ≤ H ⊓ M) hmem).2

theorem borel_inf (c : Setting T M H K)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    M ⊓ K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  rintro x ⟨hxM, hxK⟩
  have hxH : x ∈ H := c.le_H hxK
  have hJH := kerIn_le_H M H
  have hmem : ((⟨x, hxH⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
      E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K) :=
    (mem_star_iff (inf_le_left.trans inf_le_left) hJH _).mpr
      (Subgroup.mem_sup_left ⟨⟨hxH, hxM⟩, hxK⟩)
  rw [star_inf_eq c hB] at hmem
  have hnorm := hmem.2
  have hBle : (T ⊓ K) ⊔ (kerIn (H ⊓ M) H ⊓ K) ≤ K := sup_le inf_le_right inf_le_right
  refine mem_normalizer_of_conj_le c.sylow_inf hxK (B := (T ⊓ K) ⊔ (kerIn (H ⊓ M) H ⊓ K))
    le_sup_left hBle (sup_le Subgroup.le_normalizer c.le_normalizer_inf) ?_
  intro p hp
  have hpH : p ∈ H := c.le_H hp.2
  have hxpH : x * p * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH hpH) (H.inv_mem hxH)
  have hp' : ((⟨p, hpH⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈ E2.star (H ⊓ M) H (T ⊓ K) :=
    GoldS146R.mem_imgJ.mpr ⟨⟨p, hpH⟩, hp, rfl⟩
  have h2 : ((⟨x * p * x⁻¹, hxpH⟩ : ↥H) : E2.StarQuot (H ⊓ M) H) ∈
      E2.star (H ⊓ M) H (T ⊓ K) := (Subgroup.mem_normalizer_iff.mp hnorm _).mp hp'
  obtain ⟨h, hhP, hheq⟩ := exists_of_mem_star h2
  have hker : (h : G)⁻¹ * (x * p * x⁻¹) ∈ kerIn (H ⊓ M) H :=
    Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hheq)
  have haK : (h : G)⁻¹ * (x * p * x⁻¹) ∈ K :=
    K.mul_mem (K.inv_mem hhP.2) (K.mul_mem (K.mul_mem hxK hp.2) (K.inv_mem hxK))
  have hsplit : x * p * x⁻¹ = (h : G) * ((h : G)⁻¹ * (x * p * x⁻¹)) := by group
  rw [hsplit]
  exact Subgroup.mul_mem_sup hhP ⟨hker, haK⟩

end Fin

end Case2a

end CFSG.Quasithin.F146Field
