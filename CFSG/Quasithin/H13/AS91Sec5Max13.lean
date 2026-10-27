module

public import CFSG.Quasithin.H13.AS91Sec5Prim
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22LowIndexCases
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open

namespace Loc45

variable {G : Type} [Group G] [Finite G] {z : G}

theorem card_Q (hJ : HypJ4 G z) : Nat.card ↥(Q z) = 2 ^ 13 := by
  have hmap : Q z = (CFSG.pCore 2 (H z)).map (H z).subtype := rfl
  rw [hmap, Subgroup.card_map_of_injective (H z).subtype_injective]
  exact hJ.core.2.2.1

theorem card_QX (hJ : HypJ4 G z) (c : Loc45 G z) :
    Nat.card ↥(Q z ⊔ c.X) = 2 ^ 13 * 3 := by
  have hQ : Nat.card ↥(Q z) = 2 ^ 13 := card_Q hJ
  have hcop : Nat.Coprime (Nat.card ↥(Q z)) (Nat.card ↥c.X) := by
    rw [hQ, c.card_X]
    norm_num
  have hdisj : Disjoint (Q z) c.X := Subgroup.disjoint_of_coprime_natCard hcop
  have hnorm : c.X ≤ Subgroup.normalizer (Q z : Set G) :=
    c.X_le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H z))
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (Q z) c.X hnorm hdisj,
    hQ, c.card_X]

theorem card_of_surjective_ker (hJ : HypJ4 G z) (c : Loc45 G z)
    (N : Subgroup G) (π : ↥N →* J4.M22) (hQXN : Q z ⊔ c.X ≤ N)
    (hsurj : Function.Surjective π)
    (hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ c.X) :
    Nat.card ↥N = 2 ^ 13 * 3 * 443520 := by
  have hker_eq : π.ker = (Q z ⊔ c.X).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker n
  have hkercard : Nat.card ↥π.ker = 2 ^ 13 * 3 := by
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQXN).toEquiv, card_QX hJ c]
  have hM22 : Nat.card J4.M22 = 443520 :=
    CFSG.ComponentClassification.WittDesign.card_M22'
  have h := Subgroup.card_ker_mul_card_range π
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hM22, hkercard] at h
  exact h.symm

theorem G13_not_le_of_ker (hJ : HypJ4 G z) (c : Loc45 G z)
    (N : Subgroup G) (π : ↥N →* J4.M22) (hQXN : Q z ⊔ c.X ≤ N)
    (hsurj : Function.Surjective π)
    (hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ c.X) :
    ¬ c.G13 ≤ N := by
  have hNcard := card_of_surjective_ker hJ c N π hQXN hsurj hker
  intro hle
  have hdvd : Nat.card ↥c.G13 ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hdvd
  rw [c.card_G13, hNcard] at hk
  norm_num at hk
  omega

theorem relIndex_G13_inf (c : Loc45 G z) (N : Subgroup G) (hidx : N.relIndex (H z) = 2)
    (hnot : ¬ c.G13 ≤ N) : (c.G13 ⊓ N).relIndex c.G13 = 2 := by
  have hne0 : N.relIndex (H z) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := N) (K := H z)
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  have hle : (c.G13 ⊓ N).relIndex c.G13 ≤ 2 := by
    have h : N.relIndex c.G13 ≤ N.relIndex (H z) :=
      Subgroup.relIndex_le_of_le_right (H := N) (K := c.G13) (L := H z) c.G13_le hne0
    rw [hidx, ← Subgroup.inf_relIndex_right (H := N) (K := c.G13)] at h
    simpa [inf_comm] using h
  have hne1 : (c.G13 ⊓ N).relIndex c.G13 ≠ 1 := by
    intro h1
    exact hnot ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
  have hne2 : (c.G13 ⊓ N).relIndex c.G13 ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := c.G13 ⊓ N) (K := c.G13)
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  omega

theorem card_G13_inf (c : Loc45 G z) {N : Subgroup G}
    (hidx2 : (c.G13 ⊓ N).relIndex c.G13 = 2) :
    Nat.card ↥(c.G13 ⊓ N) = 2 ^ 13 * 3 * 5760 := by
  have h := Subgroup.relIndex_mul_card (H := c.G13 ⊓ N) (K := c.G13)
  rw [inf_eq_left.mpr inf_le_left, hidx2, c.card_G13] at h
  norm_num at h ⊢
  omega

theorem index_map_G13_inf (hJ : HypJ4 G z) (c : Loc45 G z)
    (N : Subgroup G) (π : ↥N →* J4.M22) (hQXN : Q z ⊔ c.X ≤ N)
    (hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ c.X)
    (hidx2 : (c.G13 ⊓ N).relIndex c.G13 = 2) :
    (((c.G13 ⊓ N).subgroupOf N).map π).index = 77 := by
  have hker_eq : π.ker = (Q z ⊔ c.X).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker n
  have hkercard : Nat.card ↥π.ker = 2 ^ 13 * 3 := by
    rw [hker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQXN).toEquiv, card_QX hJ c]
  have hker_le : π.ker ≤ (c.G13 ⊓ N).subgroupOf N := by
    rw [hker_eq]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr ⟨c.QX_le hx, x.2⟩
  have hfker : (π.comp ((c.G13 ⊓ N).subgroupOf N).subtype).ker =
      π.ker.subgroupOf ((c.G13 ⊓ N).subgroupOf N) := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hfrange : (π.comp ((c.G13 ⊓ N).subgroupOf N).subtype).range =
      ((c.G13 ⊓ N).subgroupOf N).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardA : Nat.card ↥((c.G13 ⊓ N).subgroupOf N) = Nat.card ↥(c.G13 ⊓ N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hkerA : Nat.card ↥(π.ker.subgroupOf ((c.G13 ⊓ N).subgroupOf N)) = 2 ^ 13 * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv]
    exact hkercard
  have hPcard : Nat.card ↥(((c.G13 ⊓ N).subgroupOf N).map π) = 5760 := by
    have h := Subgroup.card_ker_mul_card_range (π.comp ((c.G13 ⊓ N).subgroupOf N).subtype)
    rw [hfker, hkerA, hfrange, hcardA, card_G13_inf c hidx2] at h
    norm_num at h ⊢
    omega
  have hM22 : Nat.card J4.M22 = 443520 :=
    CFSG.ComponentClassification.WittDesign.card_M22'
  have h2 := Subgroup.card_mul_index (((c.G13 ⊓ N).subgroupOf N).map π)
  rw [hM22, hPcard] at h2
  norm_num at h2 ⊢
  omega

theorem subgroupOf_eq_of_map_eq (c : Loc45 G z) (N : Subgroup G) (π : ↥N →* J4.M22)
    (hQXN : Q z ⊔ c.X ≤ N)
    (hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ c.X)
    {A B : Subgroup ↥N} (hA : (Q z ⊔ c.X).subgroupOf N ≤ A)
    (hB : (Q z ⊔ c.X).subgroupOf N ≤ B) (h : A.map π = B.map π) : A = B := by
  have hker_eq : π.ker = (Q z ⊔ c.X).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker n
  have hkerA : π.ker ≤ A := by rw [hker_eq]; exact hA
  have hkerB : π.ker ≤ B := by rw [hker_eq]; exact hB
  calc A = (A.map π).comap π := (Subgroup.comap_map_eq_self hkerA).symm
    _ = (B.map π).comap π := by rw [h]
    _ = B := Subgroup.comap_map_eq_self hkerB

theorem relIndex_inf_le_two (N : Subgroup G) (hidx : N.relIndex (H z) = 2) {L : Subgroup G}
    (hLH : L ≤ H z) : (L ⊓ N).relIndex L ≤ 2 := by
  have hne0 : N.relIndex (H z) ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card (H := N) (K := H z)
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  have h : N.relIndex L ≤ N.relIndex (H z) :=
    Subgroup.relIndex_le_of_le_right (H := N) (K := L) (L := H z) hLH hne0
  rw [hidx, ← Subgroup.inf_relIndex_right (H := N) (K := L)] at h
  simpa [inf_comm] using h

theorem eq_G13_of_map_eq (c : Loc45 G z) (N : Subgroup G) (π : ↥N →* J4.M22)
    (hQXN : Q z ⊔ c.X ≤ N)
    (hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ c.X)
    (hidx2 : (c.G13 ⊓ N).relIndex c.G13 = 2) {L : Subgroup G}
    (hG13L : c.G13 ≤ L) (hLH : L ≤ H z) (hArel : (L ⊓ N).relIndex L ≤ 2)
    (hPeq : ((c.G13 ⊓ N).subgroupOf N).map π = ((L ⊓ N).subgroupOf N).map π) :
    L = c.G13 := by
  have hKA : (Q z ⊔ c.X).subgroupOf N ≤ (L ⊓ N).subgroupOf N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr ⟨hG13L (c.QX_le hx), x.2⟩
  have hKB : (Q z ⊔ c.X).subgroupOf N ≤ (c.G13 ⊓ N).subgroupOf N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr ⟨c.QX_le hx, x.2⟩
  have heq : (L ⊓ N).subgroupOf N = (c.G13 ⊓ N).subgroupOf N :=
    subgroupOf_eq_of_map_eq c N π hQXN hker hKA hKB hPeq.symm
  have hinf : L ⊓ N = c.G13 ⊓ N := by
    have h := (Subgroup.subgroupOf_inj (H₁ := L ⊓ N) (H₂ := c.G13 ⊓ N) (K := N)).mp heq
    simpa [inf_assoc] using h
  have hHK : L ⊓ N ≤ c.G13 := by rw [hinf]; exact inf_le_left
  have hmul : 2 * c.G13.relIndex L = (L ⊓ N).relIndex L := by
    have hA2 : (L ⊓ N).relIndex c.G13 = 2 := by rw [hinf]; exact hidx2
    rw [← hA2]
    exact Subgroup.relIndex_mul_relIndex (H := L ⊓ N) (K := c.G13) (L := L) hHK hG13L
  have hG13le1 : c.G13.relIndex L ≤ 1 := by omega
  haveI : c.G13.IsFiniteRelIndex L := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hpos : 0 < c.G13.relIndex L := Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hG13rel1 : c.G13.relIndex L = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hG13rel1) hG13L

theorem eq_H_of_map_eq_top (c : Loc45 G z) (N : Subgroup G) (π : ↥N →* J4.M22)
    (hQXN : Q z ⊔ c.X ≤ N)
    (hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ c.X)
    (hidx : N.relIndex (H z) = 2) (hnot : ¬ c.G13 ≤ N)
    (hsurj : Function.Surjective π) {L : Subgroup G}
    (hG13L : c.G13 ≤ L) (hLH : L ≤ H z)
    (htop : ((L ⊓ N).subgroupOf N).map π = ⊤) :
    L = H z := by
  have hKA : (Q z ⊔ c.X).subgroupOf N ≤ (L ⊓ N).subgroupOf N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr ⟨hG13L (c.QX_le hx), x.2⟩
  have hNtop : (N.subgroupOf N).map π = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top.mpr hsurj]
  have hmap : (N.subgroupOf N).map π = ((L ⊓ N).subgroupOf N).map π := by
    rw [hNtop, htop]
  have heq : N.subgroupOf N = (L ⊓ N).subgroupOf N :=
    subgroupOf_eq_of_map_eq c N π hQXN hker
      (by rw [Subgroup.subgroupOf_self]; exact le_top) hKA hmap
  have hinf : N = L ⊓ N := by
    have h := (Subgroup.subgroupOf_inj (H₁ := N) (H₂ := L ⊓ N) (K := N)).mp heq
    simpa [inf_assoc] using h
  have hNleL : N ≤ L := inf_eq_right.mp hinf.symm
  have hLneN : L ≠ N := by
    intro hLN
    apply hnot
    intro g hg
    rw [← hLN]
    exact hG13L hg
  have hrel : N.relIndex L * L.relIndex (H z) = 2 := by
    rw [Subgroup.relIndex_mul_relIndex (H := N) (K := L) (L := H z) hNleL hLH, hidx]
  have hNLdvd : N.relIndex L ∣ 2 := ⟨L.relIndex (H z), hrel.symm⟩
  have hNLle : N.relIndex L ≤ 2 := Nat.le_of_dvd (by norm_num) hNLdvd
  have hNLne1 : N.relIndex L ≠ 1 := by
    intro h1
    exact hLneN (le_antisymm hNleL (Subgroup.relIndex_eq_one.mp h1)).symm
  have hNLne0 : N.relIndex L ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hrel
    omega
  have hNL2 : N.relIndex L = 2 := by omega
  have hLrel1 : L.relIndex (H z) = 1 := by
    rw [hNL2] at hrel
    omega
  exact le_antisymm hLH (Subgroup.relIndex_eq_one.mp hLrel1)

theorem G13_maximal_of_linear
    (hJ : HypJ4 G z) (c : Loc45 G z) (N : Subgroup G) (π : ↥N →* J4.M22)
    (hNH : N ≤ H z) (hQXN : Q z ⊔ c.X ≤ N) (hidx : N.relIndex (H z) = 2)
    (hsurj : Function.Surjective π)
    (hker : ∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ c.X) :
    ∀ L : Subgroup G, c.G13 ≤ L → L ≤ H z → L = c.G13 ∨ L = H z := by
  intro L hG13L hLH
  have hnot : ¬ c.G13 ≤ N := G13_not_le_of_ker hJ c N π hQXN hsurj hker
  have hidx2 : (c.G13 ⊓ N).relIndex c.G13 = 2 := relIndex_G13_inf c N hidx hnot
  have hPidx : (((c.G13 ⊓ N).subgroupOf N).map π).index = 77 :=
    index_map_G13_inf hJ c N π hQXN hker hidx2
  have hsub : (c.G13 ⊓ N).subgroupOf N ≤ (L ⊓ N).subgroupOf N := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr ⟨hG13L hx.1, hx.2⟩
  have hPle : ((c.G13 ⊓ N).subgroupOf N).map π ≤ ((L ⊓ N).subgroupOf N).map π :=
    Subgroup.map_mono (f := π) hsub
  have hPLdvd : (((L ⊓ N).subgroupOf N).map π).index ∣ 77 := by
    have h := Subgroup.relIndex_mul_index hPle
    rw [hPidx] at h
    exact ⟨_, by rw [mul_comm]; exact h.symm⟩
  by_cases hPL1 : (((L ⊓ N).subgroupOf N).map π).index = 1
  · exact Or.inr (eq_H_of_map_eq_top c N π hQXN hker hidx hnot hsurj hG13L hLH
      (Subgroup.index_eq_one.mp hPL1))
  · have hPL77 : (((L ⊓ N).subgroupOf N).map π).index = 77 := by
      have h99 : (((L ⊓ N).subgroupOf N).map π).index < 99 := by
        have hle := Nat.le_of_dvd (by norm_num) hPLdvd
        omega
      obtain ⟨q, hq⟩ := hPLdvd
      rcases CFSG.ComponentClassification.WittDesign.index_mem
        (((L ⊓ N).subgroupOf N).map π) hPL1 h99 with h | h | h | h | h
      · rw [h] at hq; omega
      · rw [h] at hq; omega
      · rw [h] at hq; omega
      · rw [h] at hq; omega
      · exact h
    have hPeq : ((c.G13 ⊓ N).subgroupOf N).map π = ((L ⊓ N).subgroupOf N).map π := by
      have h := Subgroup.relIndex_mul_index hPle
      rw [hPL77, hPidx] at h
      have h1 : (((c.G13 ⊓ N).subgroupOf N).map π).relIndex
          (((L ⊓ N).subgroupOf N).map π) = 1 := by omega
      exact le_antisymm hPle (Subgroup.relIndex_eq_one.mp h1)
    exact Or.inl (eq_G13_of_map_eq c N π hQXN hker hidx2 hG13L hLH
      (relIndex_inf_le_two N hidx hLH) hPeq)

end Loc45

theorem stmt5_max13_of_linear
    (hlin : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (d : Loc41 G z),
      ∃ (N : Subgroup G) (π : ↥N →* J4.M22), N ≤ H z ∧ Q z ⊔ d.X ≤ N ∧
        N.relIndex (H z) = 2 ∧ Function.Surjective π ∧
        (∀ n : ↥N, π n = 1 ↔ (n : G) ∈ Q z ⊔ d.X)) :
    Stmt5_Max13 := by
  intro G _ _ z hJ c L hL hLH
  obtain ⟨N, π, hNH, hQXN, hidx, hsurj, hker⟩ :=
    hlin G z hJ c.toLoc48.toLoc47.toLoc46.toLoc45.toLoc43.toLoc42.toLoc41
  have hmain := Loc45.G13_maximal_of_linear (G := G) (z := z) hJ
    c.toLoc48.toLoc47.toLoc46.toLoc45 N π hNH hQXN hidx hsurj hker
  have hG13_le : c.toLoc48.toLoc47.toLoc46.toLoc45.G13 ≤ c.G3 ⊓ c.G1 := by
    simpa [inf_comm] using c.G13_le_inf
  rcases hmain (c.G3 ⊓ c.G1) hG13_le inf_le_left with h0 | h0
  · rcases hmain L (by rw [← h0]; exact hL) hLH with hL13 | hLH'
    · exact Or.inl (hL13.trans h0.symm)
    · exact Or.inr hLH'
  · exact Or.inr (le_antisymm hLH (h0.symm.trans_le hL))

end CFSG.Quasithin.H13.AS91
