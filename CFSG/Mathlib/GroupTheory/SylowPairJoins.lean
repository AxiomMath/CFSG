module

public import Mathlib.GroupTheory.Sylow

import CFSG.Mathlib.GroupTheory.SylowConj

public section

namespace CFSG

variable {Q : Type*} [Group Q]

private lemma map_conj_map_conj (H : Subgroup Q) (a b : Q) :
    (H.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  have hcomp : (MulAut.conj b).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (b * a)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp]

private lemma map_conj_one (H : Subgroup Q) :
    H.map (MulAut.conj (1 : Q)).toMonoidHom = H := by
  have hhom : (MulAut.conj (1 : Q)).toMonoidHom = MonoidHom.id Q := by
    ext x
    simp
  rw [hhom, Subgroup.map_id]

private lemma map_conj_eq_self_of_mem {H : Subgroup Q} {g : Q} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private lemma le_iSup_map_conj (P U : Subgroup Q) :
    P ≤ ⨆ u : U, P.map (MulAut.conj (u : Q)).toMonoidHom := by
  have h0 : ((1 : U) : Q) = 1 := rfl
  have h2 : P.map (MulAut.conj ((1 : U) : Q)).toMonoidHom ≤
      ⨆ u : U, P.map (MulAut.conj (u : Q)).toMonoidHom :=
    le_iSup (fun u : U => P.map (MulAut.conj (u : Q)).toMonoidHom) ⟨1, U.one_mem⟩
  rwa [h0, map_conj_one] at h2

theorem iSup_map_conj_eq_of_pair_joins {G P : Subgroup Q} {ι : Type*} {B : ι → Subgroup Q}
    (hPG : P ≤ G) (hjoin : ∀ i j, i ≠ j → B i ⊔ B j = G)
    (hpair : ∀ g ∈ G, P ⊔ P.map (MulAut.conj g).toMonoidHom = P ∨
      (∃ i, P ⊔ P.map (MulAut.conj g).toMonoidHom = B i) ∨
      P ⊔ P.map (MulAut.conj g).toMonoidHom = G)
    {U : Subgroup Q} (hUG : U ≤ G) :
    (⨆ u : U, P.map (MulAut.conj (u : Q)).toMonoidHom) = P ∨
      (∃ i, (⨆ u : U, P.map (MulAut.conj (u : Q)).toMonoidHom) = B i) ∨
      (⨆ u : U, P.map (MulAut.conj (u : Q)).toMonoidHom) = G := by
  classical
  set V : Subgroup Q := ⨆ u : U, P.map (MulAut.conj (u : Q)).toMonoidHom with hV
  have hPV : P ≤ V := le_iSup_map_conj P U
  have hVG : V ≤ G := by
    refine iSup_le fun u => ?_
    rintro x ⟨p, hp, rfl⟩
    exact G.mul_mem (G.mul_mem (hUG u.2) (hPG hp)) (G.inv_mem (hUG u.2))
  by_cases hcase : ∀ u : U, P.map (MulAut.conj (u : Q)).toMonoidHom ≤ P
  · exact Or.inl (le_antisymm (iSup_le hcase) hPV)
  · push Not at hcase
    obtain ⟨u₀, hu₀⟩ := hcase
    have hsup : P ⊔ P.map (MulAut.conj (u₀ : Q)).toMonoidHom ≤ V :=
      sup_le hPV (le_iSup_of_le u₀ le_rfl)
    rcases hpair (u₀ : Q) (hUG u₀.2) with h | ⟨i, h⟩ | h
    · exact absurd (le_trans le_sup_right h.le) hu₀
    · have hBiV : B i ≤ V := by
        rw [← h]
        exact hsup
      by_cases hcase2 : ∀ u : U, P.map (MulAut.conj (u : Q)).toMonoidHom ≤ B i
      · exact Or.inr (Or.inl ⟨i, le_antisymm (iSup_le hcase2) hBiV⟩)
      · push Not at hcase2
        obtain ⟨u₁, hu₁⟩ := hcase2
        have hsup1 : P ⊔ P.map (MulAut.conj (u₁ : Q)).toMonoidHom ≤ V :=
          sup_le hPV (le_iSup_of_le u₁ le_rfl)
        rcases hpair (u₁ : Q) (hUG u₁.2) with h' | ⟨j, h'⟩ | h'
        · have hPB : P ≤ B i := by
            rw [← h]
            exact le_sup_left
          have hPuP : P.map (MulAut.conj (u₁ : Q)).toMonoidHom ≤ P :=
            le_trans le_sup_right h'.le
          exact absurd (hPuP.trans hPB) hu₁
        · have hji : j ≠ i := by
            rintro rfl
            exact hu₁ (le_trans le_sup_right h'.le)
          have hBjV : B j ≤ V := by
            rw [← h']
            exact hsup1
          have hGV : G ≤ V := by
            rw [← hjoin i j (Ne.symm hji)]
            exact sup_le hBiV hBjV
          exact Or.inr (Or.inr (le_antisymm hVG hGV))
        · have hGV : G ≤ V := by
            rw [← h']
            exact hsup1
          exact Or.inr (Or.inr (le_antisymm hVG hGV))
    · have hGV : G ≤ V := by
        rw [← h]
        exact hsup
      exact Or.inr (Or.inr (le_antisymm hVG hGV))

private theorem card_eq_prime_part_of_dvd {p : ℕ} [Fact p.Prime] {G X P : Subgroup Q} [Finite Q]
    (hXG : X ≤ G) (hdvd : Nat.card P ∣ Nat.card X)
    (hP : Nat.card P = p ^ (Nat.card G).factorization p) :
    Nat.card P = p ^ (Nat.card X).factorization p := by
  have h1 : (Nat.card G).factorization p ≤ (Nat.card X).factorization p :=
    (Fact.out (p := p.Prime)).pow_dvd_iff_le_factorization
      (Nat.card_pos (α := X)).ne' |>.mp (hP ▸ hdvd)
  have h2 : (Nat.card X).factorization p ≤ (Nat.card G).factorization p :=
    (Nat.factorization_prime_le_iff_dvd (Nat.card_pos (α := X)).ne'
      (Nat.card_pos (α := G)).ne').mpr (Subgroup.card_dvd_of_le hXG) p Fact.out
  rw [← le_antisymm h1 h2]
  exact hP

private theorem eq_of_le_of_pair_joins [Finite Q] {G P : Subgroup Q} {p : ℕ} [Fact p.Prime]
    (hPG : P ≤ G) (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    {ι : Type*} {B : ι → Subgroup Q} (hjoin : ∀ i j, i ≠ j → B i ⊔ B j = G)
    (hpair : ∀ g ∈ G, P ⊔ P.map (MulAut.conj g).toMonoidHom = P ∨
      (∃ i, P ⊔ P.map (MulAut.conj g).toMonoidHom = B i) ∨
      P ⊔ P.map (MulAut.conj g).toMonoidHom = G)
    {m : ℕ} (hmP : ¬ m ∣ Nat.card P * Nat.card ↥(Subgroup.normalizer (P : Set Q) ⊓ G))
    (hmB : ∀ i, ¬ m ∣ Nat.card (B i) * Nat.card ↥(Subgroup.normalizer (P : Set Q) ⊓ G))
    {U : Subgroup Q} (hUG : U ≤ G) (hPU : P ≤ U) (hmU : m ∣ Nat.card U) : U = G := by
  classical
  have hPp : IsPGroup p P := IsPGroup.of_card hP
  set V : Subgroup Q := ⨆ u : U, P.map (MulAut.conj (u : Q)).toMonoidHom with hV
  set W : Subgroup Q := Subgroup.normalizer (P : Set Q) ⊓ U with hW
  have hPV : P ≤ V := le_iSup_map_conj P U
  have hVU : V ≤ U := by
    refine iSup_le fun u => ?_
    rintro x ⟨y, hy, rfl⟩
    exact U.mul_mem (U.mul_mem u.2 (hPU hy)) (U.inv_mem u.2)
  have hVmap : ∀ u : U, V.map (MulAut.conj (u : Q)).toMonoidHom = V := by
    intro u
    refine le_antisymm ?_ ?_
    · rw [hV, Subgroup.map_iSup]
      refine iSup_le fun w => ?_
      rw [map_conj_map_conj P (w : Q) (u : Q)]
      exact le_iSup (fun v : U => P.map (MulAut.conj (v : Q)).toMonoidHom) (u * w)
    · rw [hV]
      refine iSup_le fun w => ?_
      have h2 : (P.map (MulAut.conj (((u⁻¹ * w : U) : Q))).toMonoidHom).map
          (MulAut.conj (u : Q)).toMonoidHom = P.map (MulAut.conj (w : Q)).toMonoidHom := by
        rw [map_conj_map_conj]
        congr 1
        simp
      rw [← h2]
      exact Subgroup.map_mono
        (le_iSup (fun v : U => P.map (MulAut.conj (v : Q)).toMonoidHom) (u⁻¹ * w))
  have hVcases : V = P ∨ (∃ i, V = B i) ∨ V = G := by
    rw [hV]
    exact iSup_map_conj_eq_of_pair_joins hPG hjoin hpair hUG
  have hFrattini : ∀ u : U, ∃ v ∈ V, ∃ w ∈ W, (u : Q) = v * w := by
    intro u
    have hcardPV : Nat.card P = p ^ (Nat.card V).factorization p :=
      card_eq_prime_part_of_dvd (hVU.trans hUG) (Subgroup.card_dvd_of_le hPV) hP
    have hPuV : P.map (MulAut.conj (u : Q)).toMonoidHom ≤ V := le_iSup_of_le u le_rfl
    have hPup : IsPGroup p (P.map (MulAut.conj (u : Q)).toMonoidHom) := hPp.map _
    obtain ⟨v, hvV, hv⟩ := IsPGroup.exists_mem_conj_mem_of_card_eq (G := Q) (p := p)
      (P := V) (Q := P) (R := P.map (MulAut.conj (u : Q)).toMonoidHom)
      hPV hcardPV hPuV hPup
    have hnorm : v⁻¹ * (u : Q) ∈ Subgroup.normalizer (P : Set Q) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro z ⟨y, hy, rfl⟩
        have hy' : MulAut.conj (u : Q) y ∈ P.map (MulAut.conj (u : Q)).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hy
        simpa [MulAut.conj_apply, mul_assoc] using hv _ hy'
      · exact le_of_eq (Subgroup.card_map_of_injective
          (MulAut.conj (v⁻¹ * (u : Q))).injective).symm
    exact ⟨v, hvV, v⁻¹ * (u : Q), ⟨hnorm, U.mul_mem (U.inv_mem (hVU hvV)) u.2⟩, by
      show (u : Q) = v * (v⁻¹ * (u : Q))
      rw [mul_inv_cancel_left]⟩
  have hUeq : U = V ⊔ W := by
    refine le_antisymm ?_ (sup_le hVU inf_le_right)
    intro x hx
    obtain ⟨v, hv, w, hw, rfl⟩ := hFrattini ⟨x, hx⟩
    exact (V ⊔ W).mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hw)
  have hVnorm : (V.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVU).mpr fun u hu =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hVmap ⟨u, hu⟩)
  have hdvd : Nat.card U ∣ Nat.card V * Nat.card W := by
    have hWU : W ≤ U := inf_le_right
    have htop : V.subgroupOf U ⊔ W.subgroupOf U = ⊤ := by
      refine top_le_iff.mp fun x _ => ?_
      obtain ⟨v, hv, w, hw, hvw⟩ := hFrattini x
      have hvU : v ∈ U := hVU hv
      have hwU : w ∈ U := hWU hw
      have hx : (⟨v, hvU⟩ : U) * ⟨w, hwU⟩ = x := Subtype.ext hvw.symm
      rw [← hx]
      exact (V.subgroupOf U ⊔ W.subgroupOf U).mul_mem
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hv))
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hw))
    have hidx : (V.subgroupOf U).index = (V.subgroupOf U).relIndex (W.subgroupOf U) := by
      rw [← Subgroup.relIndex_top_right (H := V.subgroupOf U), ← htop, sup_comm]
      exact Subgroup.relIndex_sup_right (H := W.subgroupOf U) (K := V.subgroupOf U)
    have hd : (V.subgroupOf U).relIndex (W.subgroupOf U) ∣ Nat.card (W.subgroupOf U) :=
      ⟨Nat.card ↥(V.subgroupOf U ⊓ W.subgroupOf U),
        (Subgroup.relIndex_mul_card (V.subgroupOf U) (W.subgroupOf U)).symm⟩
    have hcV : Nat.card (V.subgroupOf U) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv
    have hcW : Nat.card (W.subgroupOf U) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWU).toEquiv
    calc Nat.card U = Nat.card (V.subgroupOf U) * (V.subgroupOf U).index :=
          (Subgroup.card_mul_index _).symm
      _ = Nat.card (V.subgroupOf U) * (V.subgroupOf U).relIndex (W.subgroupOf U) := by rw [hidx]
      _ ∣ Nat.card (V.subgroupOf U) * Nat.card (W.subgroupOf U) := mul_dvd_mul_left _ hd
      _ = Nat.card V * Nat.card W := by rw [hcV, hcW]
  have hdvd2 : Nat.card W ∣ Nat.card ↥(Subgroup.normalizer (P : Set Q) ⊓ G) := by
    refine Subgroup.card_dvd_of_le ?_
    rw [hW]
    exact inf_le_inf_left _ hUG
  have hm : m ∣ Nat.card V * Nat.card ↥(Subgroup.normalizer (P : Set Q) ⊓ G) :=
    (hmU.trans hdvd).trans (mul_dvd_mul_left _ hdvd2)
  rcases hVcases with hVP | ⟨i, hVB⟩ | hVG
  · exact absurd (hVP ▸ hm) hmP
  · exact absurd (hVB ▸ hm) (hmB i)
  · exact le_antisymm hUG (hVG ▸ hVU)

theorem eq_of_sylow_pair_joins [Finite Q] {G P : Subgroup Q} {p : ℕ} [Fact p.Prime]
    (hPG : P ≤ G) (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    {ι : Type*} {B : ι → Subgroup Q} (hjoin : ∀ i j, i ≠ j → B i ⊔ B j = G)
    (hpair : ∀ g ∈ G, P ⊔ P.map (MulAut.conj g).toMonoidHom = P ∨
      (∃ i, P ⊔ P.map (MulAut.conj g).toMonoidHom = B i) ∨
      P ⊔ P.map (MulAut.conj g).toMonoidHom = G)
    {m : ℕ} (hmP : ¬ m ∣ Nat.card P * Nat.card ↥(Subgroup.normalizer (P : Set Q) ⊓ G))
    (hmB : ∀ i, ¬ m ∣ Nat.card (B i) * Nat.card ↥(Subgroup.normalizer (P : Set Q) ⊓ G))
    {U : Subgroup Q} (hUG : U ≤ G) (hPU : Nat.card P ∣ Nat.card U) (hmU : m ∣ Nat.card U) :
    U = G := by
  classical
  obtain ⟨S⟩ := Sylow.nonempty (p := p) (G := ↥U)
  have hUfac : Nat.card P = p ^ (Nat.card U).factorization p :=
    card_eq_prime_part_of_dvd hUG hPU hP
  have hScard : Nat.card (S : Subgroup ↥U) = p ^ (Nat.card G).factorization p := by
    rw [Sylow.card_eq_multiplicity, ← hUfac]
    exact hP
  have hTle : (S : Subgroup ↥U).map U.subtype ≤ U := Subgroup.map_subtype_le _
  have hTcard : Nat.card ((S : Subgroup ↥U).map U.subtype) =
      p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective U.subtype_injective, hScard]
  have hTp : IsPGroup p ((S : Subgroup ↥U).map U.subtype) := S.isPGroup'.map U.subtype
  have hPp : IsPGroup p P := IsPGroup.of_card hP
  obtain ⟨x, hxG, hx⟩ := IsPGroup.exists_mem_conj_mem_of_card_eq (G := Q) (p := p)
    (P := G) (Q := (S : Subgroup ↥U).map U.subtype) (R := P)
    (hTle.trans hUG) hTcard hPG hPp
  set U' : Subgroup Q := U.map (MulAut.conj x).toMonoidHom with hU'
  have hPU' : P ≤ U' := by
    intro y hy
    have hxU : x⁻¹ * y * x ∈ U := hTle (hx y hy)
    have hconj : MulAut.conj x (x⁻¹ * y * x) = y := by
      simp [MulAut.conj_apply, mul_assoc]
    exact Subgroup.mem_map.mpr ⟨x⁻¹ * y * x, hxU, hconj⟩
  have hU'G : U' ≤ G := by
    rintro z ⟨y, hy, rfl⟩
    exact G.mul_mem (G.mul_mem hxG (hUG hy)) (G.inv_mem hxG)
  have hcardU' : Nat.card U' = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hmU' : m ∣ Nat.card U' := by rw [hcardU']; exact hmU
  have hU'eq : U' = G :=
    eq_of_le_of_pair_joins hPG hP hjoin hpair hmP hmB hU'G hPU' hmU'
  have h1 : U'.map (MulAut.conj x⁻¹).toMonoidHom = U := by
    rw [hU', map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have h2 : U'.map (MulAut.conj x⁻¹).toMonoidHom = G := by
    rw [hU'eq, map_conj_eq_self_of_mem (G.inv_mem hxG)]
  rw [← h1]
  exact h2

end CFSG
