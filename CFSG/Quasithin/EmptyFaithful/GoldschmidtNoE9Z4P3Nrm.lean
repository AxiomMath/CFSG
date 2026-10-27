module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Sec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.LieType.BorelTits CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417

namespace E9P2.Nrm

section Cent

variable {V : Type} [CommGroup V] [Finite V] {X Tb P : Subgroup (MulAut V)}

theorem mem_Tb_of_comm (h : E9Z4Str X Tb P) {g t : MulAut V} (hg : g ∈ X) (ht : t ∈ Tb)
    (ht2 : orderOf t = 2) (hgt : g * t = t * g) : g ∈ Tb := by
  obtain ⟨a, ha, s, hs, rfl⟩ := h.exists_mul hg
  have hst : s * t = t * s := h.Tb_comm hs ht
  have hat : a * t = t * a := by
    calc a * t = a * (t * s) * s⁻¹ := by group
      _ = a * (s * t) * s⁻¹ := by rw [hst]
      _ = (a * s * t) * s⁻¹ := by group
      _ = t * (a * s) * s⁻¹ := by rw [hgt]
      _ = t * a := by group
  have h1 : t * a * t⁻¹ = a⁻¹ := h.inverts_of_involution (h.Tb_le_X ht) ht2 a ha
  have h2 : t * a * t⁻¹ = a := by rw [← hat]; group
  have ha2 : a ^ 2 = 1 := by
    calc a ^ 2 = a * a := pow_two a
      _ = a * a⁻¹ := congrArg (a * ·) (h2.symm.trans h1)
      _ = 1 := mul_inv_cancel a
  have ha1 : a = 1 := by
    calc a = a ^ 3 * (a ^ 2)⁻¹ := by group
      _ = 1 := by rw [h.exp_P a ha, ha2]; simp
  rw [ha1, one_mul]
  exact hs

end Cent

end E9P2.Nrm

namespace E9P2.Sec.BetaData

variable {G : Type} [Group G] {T H PQ : Subgroup G} {V : Type} [CommGroup V] [Finite V]
  {β : ↥H →* MulAut V}

theorem normalizer_inf_eq (hb : BetaData T H PQ β) {T₀ : Subgroup G} (hT₀T : T₀ ≤ T)
    (hQT₀ : pCoreOf 2 H ≤ T₀) (hidx : T₀.relIndex T = 2) :
    Subgroup.normalizer (T₀ : Set G) ⊓ H = T := by
  refine le_antisymm ?_ fun x hx => ⟨?_, hb.TH hx⟩
  · rintro x ⟨hxN, hxH⟩
    have hT₀H : T₀ ≤ H := hT₀T.trans hb.TH
    have hcard : Nat.card ((T₀.subgroupOf H).map β) = 2 := by
      rw [hb.card_map hT₀H]
      have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) T₀ T hQT₀ hT₀T
      rw [hb.relIndex_T, hidx] at h1
      omega
    have hle : (T₀.subgroupOf H).map β ≤ (T.subgroupOf H).map β :=
      Subgroup.map_mono fun y hy =>
        Subgroup.mem_subgroupOf.mpr (hT₀T (Subgroup.mem_subgroupOf.mp hy))
    obtain ⟨t', ht'⟩ := exists_prime_orderOf_dvd_card' (G := ↥((T₀.subgroupOf H).map β)) 2
      (by rw [hcard])
    have ht2 : orderOf (t' : MulAut V) = 2 := by rw [Subgroup.orderOf_coe]; exact ht'
    obtain ⟨u, hu, hut⟩ := t'.2
    have hconj : β ⟨x, hxH⟩ * (t' : MulAut V) * (β ⟨x, hxH⟩)⁻¹ ∈ (T₀.subgroupOf H).map β := by
      refine ⟨⟨x, hxH⟩ * u * ⟨x, hxH⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_,
        by rw [map_mul, map_mul, map_inv, hut]⟩
      exact (Subgroup.mem_normalizer_iff.mp hxN _).mp (Subgroup.mem_subgroupOf.mp hu)
    have hconj2 : orderOf (β ⟨x, hxH⟩ * (t' : MulAut V) * (β ⟨x, hxH⟩)⁻¹) = 2 := by
      have hsc : SemiconjBy (β ⟨x, hxH⟩) (t' : MulAut V)
          (β ⟨x, hxH⟩ * (t' : MulAut V) * (β ⟨x, hxH⟩)⁻¹) := by
        unfold SemiconjBy
        group
      exact (hsc.orderOf_eq _).symm.trans ht2
    have heq := hb.str.eq_of_orderOf_eq_two (hle hconj) (hle t'.2) hconj2 ht2
    have hgt : β ⟨x, hxH⟩ * (t' : MulAut V) = (t' : MulAut V) * β ⟨x, hxH⟩ :=
      mul_inv_eq_iff_eq_mul.mp heq
    obtain ⟨y, hy, hyg⟩ := E9P2.Nrm.mem_Tb_of_comm hb.str ⟨⟨x, hxH⟩, rfl⟩ (hle t'.2) ht2 hgt
    have hq : β (y⁻¹ * ⟨x, hxH⟩) = 1 := by rw [map_mul, map_inv, hyg, inv_mul_cancel]
    have hqQ : (y : G)⁻¹ * x ∈ pCoreOf 2 H := (hb.beta_eq_one_iff _).mp hq
    have hxy : x = (y : G) * ((y : G)⁻¹ * x) := by group
    rw [hxy]
    exact T.mul_mem (Subgroup.mem_subgroupOf.mp hy) (hb.QT hqQ)
  · have hnorm : (T₀.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T).mp hnorm hx

end E9P2.Sec.BetaData

section Main

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem e9z4_normalizer_inf_eq (h35 : Lemma1435) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hshape : IsE9Z4Shape T H p)
    (hdat : IsE9Dat T M H PQ R₁ R₂ s) :
    Subgroup.normalizer ((T ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) : Set G) ⊓ H = T := by
  obtain ⟨V, _, _, β, hb⟩ := E9P2.Sec.exists_betaData h35 S hred hshape
  exact hb.normalizer_inf_eq inf_le_left
    (le_inf hb.QT (hdat.plane₁.1.trans Subgroup.le_normalizer)) hdat.indexT

end Main

end CFSG.Quasithin
