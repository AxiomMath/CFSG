module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

variable {G : Type} [Group G]

@[expose] noncomputable def convK {V K : Subgroup G} (hel : IsElemAbelian 2 V)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) : ↥K →* MulAut (IntMod V hel) :=
  (convI hel).comp (Subgroup.inclusion hKN)

theorem range_convK {V K : Subgroup G} (hel : IsElemAbelian 2 V)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) : (convK hel hKN).range = autI hel K := by
  ext φ
  rw [MonoidHom.mem_range, mem_autI]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Subgroup.inclusion hKN k, k.2, rfl⟩
  · rintro ⟨g, hgK, rfl⟩
    exact ⟨⟨g, hgK⟩, rfl⟩

theorem convK_eq_one_iff {V K : Subgroup G} (hel : IsElemAbelian 2 V)
    (hKN : K ≤ Subgroup.normalizer (V : Set G)) (k : ↥K) :
    convK hel hKN k = 1 ↔ (k : G) ∈ Subgroup.centralizer (V : Set G) :=
  convI_eq_one_iff hel _

theorem eq_autI_of_normal {V K : Subgroup G} (hel : IsElemAbelian 2 V)
    (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hO : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    {C : Subgroup (MulAut (IntMod V hel))} (hC : C ≤ autI hel K)
    (hCN : autI hel K ≤ Subgroup.normalizer (C : Set (MulAut (IntMod V hel))))
    (hnc : ∃ a ∈ C, ∃ b ∈ C, a * b ≠ b * a) : C = autI hel K := by
  set f := convK hel hKN with hf
  have hrange : f.range = autI hel K := range_convK hel hKN
  have hf1 : ∀ x : ↥K, x ∈ CFSG.Open.pCore 2 ↥K → f x = 1 := fun x hx =>
    (convK_eq_one_iff hel hKN x).mpr (hO ⟨x, hx, rfl⟩)
  set N := C.comap f with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hg : f g ∈ autI hel K := hrange ▸ ⟨g, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hCN hg) _).mp hn⟩
  have hNm := hNn.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)) (QuotientGroup.mk'_surjective _)
  have hpre : ∀ a ∈ C, ∃ n ∈ N, f n = a := by
    intro a ha
    obtain ⟨n, hn⟩ := hrange ▸ hC ha
    exact ⟨n, by rw [hN, Subgroup.mem_comap, hn]; exact ha, hn⟩
  rcases normal_eq_top_or_le_center hq hNm with h | h
  · refine le_antisymm hC ?_
    rw [← hrange]
    rintro _ ⟨k, rfl⟩
    have hk : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) k ∈
        N.map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K)) := h ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnk⟩ := hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
    have h1 := hf1 _ hnk
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1]
    exact hn
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    obtain ⟨n₁, hn₁, rfl⟩ := hpre a ha
    obtain ⟨n₂, hn₂, rfl⟩ := hpre b hb
    apply hab
    have hc : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) n₁ ∈ Subgroup.center _ :=
      h ⟨n₁, hn₁, rfl⟩
    have h2 := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) n₂)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h2
    have h3 := hf1 _ h2
    rw [map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h3
    exact h3.symm

theorem autI_map_conj {V K : Subgroup G} (hel : IsElemAbelian 2 V) {t : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) :
    autI hel (K.map (MulAut.conj t).toMonoidHom) =
      (autI hel K).map (MulAut.conj (convI hel ⟨t, ht⟩)).toMonoidHom := by
  ext φ
  rw [mem_autI, Subgroup.mem_map]
  constructor
  · rintro ⟨g, ⟨k, hk, hkg⟩, rfl⟩
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := by
      have : k = t⁻¹ * g * t := by
        rw [← hkg]
        simp [mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) g.2) ht
    refine ⟨convI hel ⟨k, hkN⟩, convI_mem_autI hel hk hkN, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hkg]
    rfl
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨k, hkK, rfl⟩ := (mem_autI hel).1 hψ
    refine ⟨⟨t, ht⟩ * k * ⟨t, ht⟩⁻¹, ⟨k, hkK, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
