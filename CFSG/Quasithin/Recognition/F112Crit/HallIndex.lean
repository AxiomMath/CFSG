module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy

public section

namespace CFSG.Quasithin.F112Crit

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private theorem relIndex_eq_relIndex_sup' {H K : Subgroup G}
    (h : H ≤ normalizer (K : Set G)) : H.relIndex K = H.relIndex (H ⊔ K) := by
  have h1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer h
  have h2 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (inf_le_right : H ⊓ K ≤ K)
  have h3 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (le_sup_left : H ≤ H ⊔ K)
  rw [h2, h3] at h1
  rw [← inf_relIndex_right]
  have hpos : 0 < Nat.card H * Nat.card ↥(H ⊓ K) := Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.card H * Nat.card ↥(H ⊓ K) * (H ⊓ K).relIndex K
      = Nat.card H * (Nat.card ↥(H ⊓ K) * (H ⊓ K).relIndex K) := by ring
    _ = Nat.card ↥H * H.relIndex (H ⊔ K) * Nat.card ↥(H ⊓ K) := h1.symm
    _ = Nat.card H * Nat.card ↥(H ⊓ K) * H.relIndex (H ⊔ K) := by ring

theorem relIndex_two_pow_of_le_normalizer {X C H : Subgroup G} (hXH : X ≤ H) (hCH : C ≤ H)
    (hXC : X ≤ normalizer (C : Set G)) {k : ℕ} (hk : X.relIndex H = 2 ^ k) :
    ∃ m : ℕ, X.relIndex C = 2 ^ m := by
  rw [relIndex_eq_relIndex_sup' hXC]
  have hdvd : X.relIndex (X ⊔ C) ∣ 2 ^ k := by
    rw [← hk]
    exact ⟨(X ⊔ C).relIndex H,
      (relIndex_mul_relIndex X (X ⊔ C) H le_sup_left (sup_le hXH hCH)).symm⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨m, hm⟩

theorem le_of_relIndex_odd {X E C : Subgroup G} (hXE : X ≤ E) (hodd : Odd (E.relIndex C))
    {m : ℕ} (hm : X.relIndex C = 2 ^ m) : C ≤ E := by
  have hmul : X.relIndex C = (X ⊓ C).relIndex (E ⊓ C) * E.relIndex C := by
    rw [← inf_relIndex_right X C, ← inf_relIndex_right E C]
    exact (relIndex_mul_relIndex (X ⊓ C) (E ⊓ C) C (inf_le_inf_right C hXE) inf_le_right).symm
  have hdvd : E.relIndex C ∣ 2 ^ m := hm ▸ hmul ▸ dvd_mul_left _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hj0).mpr even_two)
  rw [hj0, pow_zero] at hj
  exact relIndex_eq_one.mp hj

section Hall

variable {H T : Subgroup G}

private theorem card_subgroupOf_of_le' (hTH : T ≤ H) : Nat.card (T.subgroupOf H) = Nat.card T :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv

private theorem coprime_of_normal_two (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (hodd : Odd (T.relIndex H)) :
    Nat.Coprime (Nat.card (T.subgroupOf H)) (T.subgroupOf H).index := by
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [card_subgroupOf_of_le' hTH, hn]
  exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)

theorem exists_hall_of_normal_two (hTH : T ≤ H) (hHT : H ≤ normalizer (T : Set G))
    (hT : IsPGroup 2 T) (hodd : Odd (T.relIndex H)) :
    ∃ X : Subgroup G, X ≤ H ∧ Nat.card X = T.relIndex H := by
  haveI : (T.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hTH).mpr hHT
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime
    (coprime_of_normal_two hTH hT hodd)
  refine ⟨K.map H.subtype, map_subtype_le K, ?_⟩
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  have h1 := hK.card_mul_card
  have h2 := (T.subgroupOf H).card_mul_index
  have hpos : 0 < Nat.card (T.subgroupOf H) := Nat.card_pos
  have : Nat.card K = (T.subgroupOf H).index :=
    Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
  exact this

theorem exists_conj_hall_of_normal_two (hTH : T ≤ H) (hHT : H ≤ normalizer (T : Set G))
    (hT : IsPGroup 2 T) (hodd : Odd (T.relIndex H)) {X Y : Subgroup G} (hXH : X ≤ H)
    (hYH : Y ≤ H) (hX : Nat.card X = T.relIndex H) (hY : Nat.card Y = T.relIndex H) :
    ∃ c ∈ H, ∀ y : G, y ∈ Y ↔ c⁻¹ * y * c ∈ X := by
  haveI hN : (T.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hTH).mpr hHT
  have hcop := coprime_of_normal_two hTH hT hodd
  have hcard : ∀ {W : Subgroup G}, W ≤ H → Nat.card W = T.relIndex H →
      (T.subgroupOf H).IsComplement' (W.subgroupOf H) := by
    intro W hWH hW
    have hWc : Nat.card (W.subgroupOf H) = (T.subgroupOf H).index := by
      rw [card_subgroupOf_of_le' hWH, hW]; rfl
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hWc]; exact (T.subgroupOf H).card_mul_index
    · rw [hWc]; exact hcop
  obtain ⟨g, hg⟩ := CFSG.GorensteinWalter.SchurZassenhaus.complements_conjugate_of_coprime
    (T.subgroupOf H) (X.subgroupOf H) (Y.subgroupOf H) hN (hcard hXH hX) (hcard hYH hY) hcop
  refine ⟨(g : G), g.2, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · have hy' : (⟨y, hYH hy⟩ : ↥H) ∈ Y.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]; exact hy
    rw [hg] at hy'
    obtain ⟨x, hx, hxe⟩ := hy'
    have hx : (x : G) ∈ X := hx
    have e : (y : G) = (g : G) * (x : G) * (g : G)⁻¹ := by
      have := congrArg Subtype.val hxe
      simpa [MulAut.conj_apply] using this.symm
    have e2 : (g : G)⁻¹ * ((g : G) * (x : G) * (g : G)⁻¹) * g = x := by group
    rw [e, e2]
    exact hx
  · have hxH : (g : G)⁻¹ * y * g ∈ H := hXH hy
    have hx' : (⟨_, hxH⟩ : ↥H) ∈ X.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]; exact hy
    have hmem : (MulAut.conj g).toMonoidHom ⟨_, hxH⟩ ∈ Y.subgroupOf H := by
      rw [hg]; exact Subgroup.mem_map_of_mem _ hx'
    rw [Subgroup.mem_subgroupOf] at hmem
    have e : (((MulAut.conj g).toMonoidHom ⟨_, hxH⟩ : ↥H) : G) = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
    rwa [e] at hmem

end Hall

end CFSG.Quasithin.F112Crit

end
