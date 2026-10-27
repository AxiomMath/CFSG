module

import CFSG.LocalAnalysis.WeakClosure81.W15SixC
import CFSG.Quasithin.EmptyFaithful.T1521SA5Two
import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFU1
import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Faithful
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsSz)

private theorem w183_card_eq_one_two_four {n : ℕ} (hdvd : n ∣ 4) :
    n = 1 ∨ n = 2 ∨ n = 4 := by
  have hle : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < n := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  interval_cases n
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd hdvd (by norm_num)
  · exact Or.inr (Or.inr rfl)

private theorem w183_card_centralizer_involution {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 5)) {x : Y} (hx : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.centralizer ({x} : Set Y)) = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
    (fun a => Subgroup.mem_centralizer_singleton_iff))]
  exact CFSG.GF2Type.Smith1979.OmegaPlus.card_centralizer_of_alt5 e hx hx1

private theorem w183_a5_sup_order_four {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 5))
    {P Q : Subgroup Y} (hP : Nat.card P = 4) (hQ : Nat.card Q = 4) (hne : P ≠ Q) :
    P ⊔ Q = ⊤ := by
  have hP' : Nat.card (P.map (e : Y →* alternatingGroup (Fin 5))) = 4 := by
    rw [Subgroup.card_map_of_injective (f := (e : Y →* alternatingGroup (Fin 5))) e.injective]
    exact hP
  have hQ' : Nat.card (Q.map (e : Y →* alternatingGroup (Fin 5))) = 4 := by
    rw [Subgroup.card_map_of_injective (f := (e : Y →* alternatingGroup (Fin 5))) e.injective]
    exact hQ
  have hne' : P.map (e : Y →* alternatingGroup (Fin 5)) ≠
      Q.map (e : Y →* alternatingGroup (Fin 5)) := fun h =>
    hne (Subgroup.map_injective (f := (e : Y →* alternatingGroup (Fin 5))) e.injective h)
  have htop := CFSG.Quasithin.Kleidman.F204.klein_sup_eq_top hP' hQ' hne'
  have hmap : (P ⊔ Q).map (e : Y →* alternatingGroup (Fin 5)) = ⊤ := by
    rw [Subgroup.map_sup]
    exact htop
  have hcom := congrArg (Subgroup.comap (e : Y →* alternatingGroup (Fin 5))) hmap
  rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at hcom

private theorem w183_sup_eq_top_of_le_sylow {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 5)) {P F : Subgroup Y} (hP : Nat.card P = 4)
    (hinf : P ⊓ F = ⊥) (hF : Nat.card F = 2 ∨ Nat.card F = 4) : P ⊔ F = ⊤ := by
  have hY60 : Nat.card Y = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num
  rcases hF with hF2 | hF4
  · have hFne : F ≠ ⊥ := by
      intro h; rw [h] at hF2; simp at hF2
    obtain ⟨z, hzF, hz1⟩ : ∃ z ∈ F, z ≠ 1 := by
      obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hFne
      exact ⟨(w : Y), w.2, fun h => hw1 (Subtype.ext h)⟩
    have hzord : orderOf z = 2 := by
      have hdiv : orderOf z ∣ 2 := by
        rw [← hF2]
        exact Subgroup.orderOf_dvd_natCard F hzF
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
      · exact absurd h1 (by intro h; exact hz1 (orderOf_eq_one_iff.mp h))
      · exact h2
    let Q : Subgroup Y := P.map (MulAut.conj z : Y →* Y)
    have hQcard : Nat.card Q = 4 := by
      dsimp only [Q]
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj z : Y →* Y))
        (MulAut.conj z).injective, hP]
    have hQle : Q ≤ P ⊔ F := by
      dsimp only [Q]
      calc P.map (MulAut.conj z : Y →* Y)
          ≤ (P ⊔ F).map (MulAut.conj z : Y →* Y) := Subgroup.map_mono le_sup_left
        _ = P ⊔ F := Subgroup.mem_normalizer_iff_map_conj_eq.mp
            (Subgroup.le_normalizer (Subgroup.mem_sup_right hzF))
    by_cases hQ : Q = P
    · have hznorm : z ∈ Subgroup.normalizer (P : Set Y) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa only [Q] using hQ)
      have hle : Subgroup.zpowers z ≤ Subgroup.normalizer (P : Set Y) :=
        Subgroup.zpowers_le.mpr hznorm
      have hdisj : Disjoint P (Subgroup.zpowers z) := by
        rw [disjoint_iff]
        exact le_antisymm
          (le_trans (inf_le_inf_left P (Subgroup.zpowers_le.mpr hzF)) (le_of_eq hinf)) bot_le
      have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        P (Subgroup.zpowers z) hle hdisj
      have hzpow : Nat.card (Subgroup.zpowers z) = 2 := by
        rw [Nat.card_zpowers]; exact hzord
      have h8 : Nat.card ↥(P ⊔ Subgroup.zpowers z) = 8 := by
        rw [hcard, hP, hzpow]
      have hdvd : Nat.card ↥(P ⊔ Subgroup.zpowers z) ∣ Nat.card Y :=
        Subgroup.card_subgroup_dvd_card _
      rw [hY60, h8] at hdvd
      exact absurd hdvd (by norm_num)
    · have htop := w183_a5_sup_order_four e hP hQcard (Ne.symm hQ)
      refine le_antisymm le_top ?_
      calc ⊤ = P ⊔ Q := htop.symm
        _ ≤ P ⊔ F := sup_le le_sup_left hQle
  · have hne : P ≠ F := by
      intro h
      have hbot : P = ⊥ := by rw [← hinf, ← h, inf_idem]
      have hcard : Nat.card P = 1 := by rw [hbot]; simp
      omega
    exact w183_a5_sup_order_four e hP hF4 hne

theorem w183b2_pair_gen_a5 : ∀ (Y : Type) [Group Y], IsL2 Y 2 → ∀ P₁ P₂ : Subgroup Y,
    IsElemAbelian 2 P₁ → IsElemAbelian 2 P₂ → Nat.card P₁ = 4 → Nat.card P₂ = 4 → P₁ ≠ P₂ →
    (∀ E F : Subgroup Y, E ≤ P₁ → F ≤ P₂ → 8 ≤ Nat.card E * Nat.card F → E ⊔ F = ⊤) ∧
      (∀ a ∈ P₁, ∀ b ∈ P₂, a ≠ 1 → b ≠ 1 → Odd (orderOf (a * b))) := by
  intro Y _ hY P₁ P₂ hE1 hE2 hc1 hc2 hne
  obtain ⟨e⟩ := CFSG.Quasithin.nonempty_equiv_alt5_of_isPSL_two_two_two
    (isL2_iff_isPSL.mp hY)
  haveI hP1fin : Finite ↥P₁ := Nat.finite_of_card_ne_zero (by rw [hc1]; norm_num)
  haveI hP2fin : Finite ↥P₂ := Nat.finite_of_card_ne_zero (by rw [hc2]; norm_num)
  have hP12 : P₁ ⊓ P₂ = ⊥ := by
    by_contra h
    obtain ⟨x, hx, hx1⟩ : ∃ x : Y, x ∈ P₁ ⊓ P₂ ∧ x ≠ 1 := by
      obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
      exact ⟨(w : Y), w.2, fun hh => hw1 (Subtype.ext hh)⟩
    have hxP1 : x ∈ P₁ := (Subgroup.mem_inf.mp hx).1
    have hxP2 : x ∈ P₂ := (Subgroup.mem_inf.mp hx).2
    have hx2 : x * x = 1 := by
      have := hE1.2 x hxP1; simpa [pow_two] using this
    have hCx := w183_card_centralizer_involution e hx2 hx1
    have hP1le : P₁ ≤ Subgroup.centralizer ({x} : Set Y) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ((isMulCommutative_iff.mp hE1.1) ⟨y, hy⟩ ⟨x, hxP1⟩)
    have hP2le : P₂ ≤ Subgroup.centralizer ({x} : Set Y) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ((isMulCommutative_iff.mp hE2.1) ⟨y, hy⟩ ⟨x, hxP2⟩)
    haveI : Finite ↥(Subgroup.centralizer ({x} : Set Y)) :=
      Nat.finite_of_card_ne_zero (by rw [hCx]; norm_num)
    have h1 : P₁ = Subgroup.centralizer ({x} : Set Y) :=
      Subgroup.eq_of_le_of_card_ge hP1le (le_of_eq (by rw [hCx, hc1]))
    have h2 : P₂ = Subgroup.centralizer ({x} : Set Y) :=
      Subgroup.eq_of_le_of_card_ge hP2le (le_of_eq (by rw [hCx, hc2]))
    exact hne (h1.trans h2.symm)
  have hY60 : Nat.card Y = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY60]; norm_num)
  refine ⟨?_, ?_⟩
  · intro E F hE hF h8
    have hEdvd : Nat.card E ∣ 4 := by
      rw [← hc1]; exact Subgroup.card_dvd_of_le hE
    have hFdvd : Nat.card F ∣ 4 := by
      rw [← hc2]; exact Subgroup.card_dvd_of_le hF
    rcases w183_card_eq_one_two_four hEdvd with hE1c | hE2c | hE4c
    · rw [hE1c] at h8
      have hFle : Nat.card F ≤ 4 := Nat.le_of_dvd (by norm_num) hFdvd
      omega
    · have hF4 : Nat.card F = 4 := by
        rcases w183_card_eq_one_two_four hFdvd with h1 | h2 | h4
        · rw [h1] at h8; omega
        · rw [h2] at h8; omega
        · exact h4
      have hFeq : F = P₂ :=
        Subgroup.eq_of_le_of_card_ge hF (le_of_eq (by rw [hF4, hc2]))
      have hEinf : P₂ ⊓ E = ⊥ :=
        le_antisymm
          (le_trans (inf_le_inf_left P₂ hE)
            (le_trans (le_of_eq (inf_comm P₂ P₁)) (le_of_eq hP12))) bot_le
      rw [hFeq, sup_comm]
      exact w183_sup_eq_top_of_le_sylow e hc2 hEinf (Or.inl hE2c)
    · have hEeq : E = P₁ :=
        Subgroup.eq_of_le_of_card_ge hE (le_of_eq (by rw [hE4c, hc1]))
      have hF24 : Nat.card F = 2 ∨ Nat.card F = 4 := by
        rcases w183_card_eq_one_two_four hFdvd with h1 | h2 | h4
        · rw [h1] at h8; omega
        · exact Or.inl h2
        · exact Or.inr h4
      have hFinf : P₁ ⊓ F = ⊥ :=
        le_antisymm (le_trans (inf_le_inf_left P₁ hF) (le_of_eq hP12)) bot_le
      rw [hEeq]
      exact w183_sup_eq_top_of_le_sylow e hc1 hFinf hF24
  · intro a ha b hb ha1 hb1
    have ha2 : a * a = 1 := by have := hE1.2 a ha; simpa [pow_two] using this
    have hb2 : b * b = 1 := by have := hE2.2 b hb; simpa [pow_two] using this
    have hab1 : a * b ≠ 1 := by
      intro hab
      have hba : b = a := by
        have h1 : a * (a * b) = b := by rw [← mul_assoc, ha2, one_mul]
        have h2 : a * (a * b) = a := by rw [hab, mul_one]
        rw [← h1]; exact h2
      have hbP1 : b ∈ P₁ := hba ▸ ha
      have hmem : b ∈ P₁ ⊓ P₂ := Subgroup.mem_inf.mpr ⟨hbP1, hb⟩
      rw [hP12] at hmem
      exact hb1 (Subgroup.mem_bot.mp hmem)
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨k, hk⟩ := even_iff_exists_two_mul.mp hodd
    have hnpos : 0 < orderOf (a * b) := orderOf_pos _
    have hkpos : 0 < k := by omega
    let z : Y := (a * b) ^ k
    have hz2 : z * z = 1 := by
      dsimp only [z]
      rw [← pow_add, ← two_mul, ← hk, pow_orderOf_eq_one]
    have hz1 : z ≠ 1 := by
      intro hz
      have hdvd : orderOf (a * b) ∣ k := by
        rw [orderOf_dvd_iff_pow_eq_one]
        change z = 1
        exact hz
      have hklt : k < orderOf (a * b) := by omega
      have hle : orderOf (a * b) ≤ k := Nat.le_of_dvd hkpos hdvd
      omega
    have haz : a * z * a⁻¹ = z := by
      have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha2, inv_eq_of_mul_eq_one_right hb2]
        calc a * (a * b) * a = a * ((a * b) * a) := by rw [mul_assoc]
          _ = a * (a * (b * a)) := by rw [mul_assoc]
          _ = a * a * (b * a) := by rw [← mul_assoc]
          _ = 1 * (b * a) := by rw [ha2]
          _ = b * a := by rw [one_mul]
      calc a * z * a⁻¹ = a * (a * b) ^ k * a⁻¹ := by
              rw [show z = (a * b) ^ k from rfl]
        _ = (a * (a * b) * a⁻¹) ^ k := by
              rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
        _ = ((a * b)⁻¹) ^ k := by rw [h1]
        _ = z⁻¹ := by rw [inv_pow, show (a * b) ^ k = z from rfl]
        _ = z := inv_eq_of_mul_eq_one_right hz2
    have hbz : b * z * b⁻¹ = z := by
      have h1 : b * (a * b) * b⁻¹ = (a * b)⁻¹ := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hb2, inv_eq_of_mul_eq_one_right ha2]
        calc b * (a * b) * b = b * ((a * b) * b) := by rw [mul_assoc]
          _ = b * (a * (b * b)) := by rw [mul_assoc]
          _ = b * (a * 1) := by rw [hb2]
          _ = b * a := by rw [mul_one]
      calc b * z * b⁻¹ = b * (a * b) ^ k * b⁻¹ := by
              rw [show z = (a * b) ^ k from rfl]
        _ = (b * (a * b) * b⁻¹) ^ k := by
              rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
        _ = ((a * b)⁻¹) ^ k := by rw [h1]
        _ = z⁻¹ := by rw [inv_pow, show (a * b) ^ k = z from rfl]
        _ = z := inv_eq_of_mul_eq_one_right hz2
    have hzCa : z ∈ Subgroup.centralizer ({a} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp haz).symm
    have hzCb : z ∈ Subgroup.centralizer ({b} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hbz).symm
    have hCa := w183_card_centralizer_involution e ha2 ha1
    have hCb := w183_card_centralizer_involution e hb2 hb1
    have hP1le : P₁ ≤ Subgroup.centralizer ({a} : Set Y) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ((isMulCommutative_iff.mp hE1.1) ⟨y, hy⟩ ⟨a, ha⟩)
    have hP2le : P₂ ≤ Subgroup.centralizer ({b} : Set Y) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ((isMulCommutative_iff.mp hE2.1) ⟨y, hy⟩ ⟨b, hb⟩)
    haveI : Finite ↥(Subgroup.centralizer ({a} : Set Y)) :=
      Nat.finite_of_card_ne_zero (by rw [hCa]; norm_num)
    haveI : Finite ↥(Subgroup.centralizer ({b} : Set Y)) :=
      Nat.finite_of_card_ne_zero (by rw [hCb]; norm_num)
    have hP1eq : P₁ = Subgroup.centralizer ({a} : Set Y) :=
      Subgroup.eq_of_le_of_card_ge hP1le (le_of_eq (by rw [hCa, hc1]))
    have hP2eq : P₂ = Subgroup.centralizer ({b} : Set Y) :=
      Subgroup.eq_of_le_of_card_ge hP2le (le_of_eq (by rw [hCb, hc2]))
    have hzP1 : z ∈ P₁ := by rw [hP1eq]; exact hzCa
    have hzP2 : z ∈ P₂ := by rw [hP2eq]; exact hzCb
    have hmem : z ∈ P₁ ⊓ P₂ := Subgroup.mem_inf.mpr ⟨hzP1, hzP2⟩
    rw [hP12] at hmem
    exact hz1 (Subgroup.mem_bot.mp hmem)

@[expose] def FinPairGenL28 : Prop :=
  ∀ (Y : Type) [Group Y], IsL2 Y 3 → ∀ P₁ P₂ : Subgroup Y,
    IsElemAbelian 2 P₁ → IsElemAbelian 2 P₂ → Nat.card P₁ = 8 → Nat.card P₂ = 8 → P₁ ≠ P₂ →
    (∀ E F : Subgroup Y, E ≤ P₁ → F ≤ P₂ → 4 ≤ Nat.card E → 4 ≤ Nat.card F → E ⊔ F = ⊤) ∧
      (∀ a ∈ P₁, ∀ b ∈ P₂, a ≠ 1 → b ≠ 1 → Odd (orderOf (a * b)))

@[expose] def FinPairGenSz8 : Prop :=
  ∀ (Y : Type) [Group Y], IsSz Y 3 → ∀ P₁ P₂ : Subgroup Y,
    IsElemAbelian 2 P₁ → IsElemAbelian 2 P₂ → Nat.card P₁ = 8 → Nat.card P₂ = 8 → P₁ ≠ P₂ →
    (∀ E F : Subgroup Y, E ≤ P₁ → F ≤ P₂ → 4 ≤ Nat.card E → 4 ≤ Nat.card F → E ⊔ F = ⊤) ∧
      (∀ a ∈ P₁, ∀ b ∈ P₂, a ≠ 1 → b ≠ 1 → Odd (orderOf (a * b)))

end CFSG.LocalAnalysis.WeakClosure81

end
