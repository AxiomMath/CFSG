module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210One
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Two
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Cover

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch210

open Subgroup

variable {ι : Type} [Fintype ι] [DecidableEq ι] {B : ι → Type} [∀ i, Group (B i)]
  [∀ i, Finite (B i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Finite (B i)] in
private lemma a210rec_prodSub_mono {F G : Finset ι} (h : F ⊆ G) :
    prodSub B F ≤ prodSub B G := by
  intro s hs j hj
  exact hs j fun hjF => hj (h hjF)

omit [DecidableEq ι] [∀ i, Finite (B i)] in
private lemma a210rec_prodSub_univ :
    prodSub B (Finset.univ : Finset ι) = (⊤ : Subgroup (∀ i, B i)) := by
  ext s
  simp [prodSub]

omit [Fintype ι] [∀ i, Finite (B i)] in
theorem SimpleFactors.exists_perfect_sub (hB : SimpleFactors B) {Y : Type} [Group Y] [Finite Y]
    (θ : Y →* ∀ i, B i) {F : Finset ι} {P : Subgroup Y} (hP : prodSub B F ≤ P.map θ) :
    ∃ R ≤ P, Group.IsPerfect ↥R ∧ R.map θ = prodSub B F := by
  let Sset : Set (Subgroup Y) := {R | R ≤ P ∧ R.map θ = prodSub B F}
  have hmem : P ⊓ (prodSub B F).comap θ ∈ Sset := by
    refine ⟨inf_le_left, ?_⟩
    apply le_antisymm
    · intro s hs
      obtain ⟨r, hr, hrθ⟩ := Subgroup.mem_map.mp hs
      rw [← hrθ]
      exact Subgroup.mem_comap.mp hr.2
    · intro s hs
      obtain ⟨p, hp, hpθ⟩ := Subgroup.mem_map.mp (hP hs)
      exact Subgroup.mem_map.mpr
        ⟨p, ⟨hp, Subgroup.mem_comap.mpr (by rw [hpθ]; exact hs)⟩, hpθ⟩
  obtain ⟨R, hRmem, hRmin⟩ := wellFounded_lt.has_min Sset ⟨_, hmem⟩
  have hRle : R ≤ P := hRmem.1
  have hRmap : R.map θ = prodSub B F := hRmem.2
  have hcommle : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le (le_refl R) (le_refl R)
  have hcommmem : ⁅R, R⁆ ∈ Sset := by
    refine ⟨hcommle.trans hRle, ?_⟩
    rw [Subgroup.map_commutator, hRmap]
    exact (Subgroup.isPerfect_iff (H := prodSub B F)).mp (hB.perfect_prodSub F)
  have hperfeq : ⁅R, R⁆ = R := by
    apply le_antisymm hcommle
    by_contra hnot
    exact hRmin ⁅R, R⁆ hcommmem
      (lt_of_le_of_ne hcommle fun heq => hnot (le_of_eq heq.symm))
  exact ⟨R, hRle, (Subgroup.isPerfect_iff (H := R)).mpr hperfeq, hRmap⟩

omit [Fintype ι] in
theorem rec_commuting_three_elements (hB : SimpleFactors B)
    {Y : Type} [Group Y] [Finite Y] (θ : Y →* ∀ i, B i) (hQ : IsPGroup 3 θ.ker)
    (hY : CFSG.pRank 3 Y ≤ 3) (F : Finset ι) (hF : F.Nonempty) (R : Subgroup Y)
    (hR : Group.IsPerfect ↥R) (hRF : R.map θ = prodSub B F) :
    ∃ y : ι → Y, (∀ j ∈ F, y j ∈ R ∧ (∃ k : ℕ, y j ^ 3 ^ k = 1) ∧ orderOf (θ (y j)) = 3 ∧
        ∀ i, i ≠ j → θ (y j) i = 1) ∧ ∀ j ∈ F, ∀ l ∈ F, y j * y l = y l * y j := by
  classical
  have main : ∀ n : ℕ, ∀ (F : Finset ι), F.card = n → F.Nonempty →
      ∀ (R : Subgroup Y), Group.IsPerfect ↥R → R.map θ = prodSub B F →
      ∃ y : ι → Y, (∀ j ∈ F, y j ∈ R ∧ (∃ k : ℕ, y j ^ 3 ^ k = 1) ∧
          orderOf (θ (y j)) = 3 ∧ ∀ i, i ≠ j → θ (y j) i = 1) ∧
        ∀ j ∈ F, ∀ l ∈ F, y j * y l = y l * y j := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F hcard hF R hR hRF
      by_cases hC : ∀ r ∈ R, (∀ q ∈ R ⊓ θ.ker, r * q = q * r) → r ∈ θ.ker
      · by_cases h2 : 2 ≤ F.card
        · exact (SimpleFactors.false_of_centralizer_le hB θ hQ hY h2 hR hRF hC).elim
        · have hcard1 : F.card = 1 := by
            have hpos : 0 < F.card := Finset.card_pos.mpr hF
            omega
          obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard1
          obtain ⟨y₀, hy₀R, hy₀3, hy₀ord, hy₀supp⟩ :=
            SimpleFactors.exists_threeElem_at hB θ hRF (Finset.mem_singleton_self i)
          refine ⟨fun _ => y₀, ?_, ?_⟩
          · intro j hj
            rw [Finset.mem_singleton] at hj
            subst hj
            exact ⟨hy₀R, hy₀3, hy₀ord, hy₀supp⟩
          · intro j hj l hl
            rfl
      · obtain ⟨i, hiF, J, hJleR, hJperf, hJmap, hJcomm⟩ :=
          SimpleFactors.exists_perfect_component hB θ hRF hC
        obtain ⟨yᵢ, hyᵢJ, hyᵢ3, hyᵢord, hyᵢsupp⟩ :=
          SimpleFactors.exists_threeElem_at hB θ hJmap (Finset.mem_singleton_self i)
        have hyᵢR : yᵢ ∈ R := hJleR hyᵢJ
        by_cases hErase : F.erase i = ∅
        · have hFi : F = {i} := by
            rcases (Finset.erase_eq_empty_iff F i).mp hErase with h | h
            · rw [h] at hF
              exact absurd hF Finset.not_nonempty_empty
            · exact h
          refine ⟨Function.update (fun _ => (1 : Y)) i yᵢ, ?_, ?_⟩
          · intro j hj
            rw [hFi, Finset.mem_singleton] at hj
            subst hj
            rw [Function.update_self]
            exact ⟨hyᵢR, hyᵢ3, hyᵢord, hyᵢsupp⟩
          · intro j hj l hl
            rw [hFi, Finset.mem_singleton] at hj hl
            subst hj
            subst hl
            rfl
        · have hF' : (F.erase i).Nonempty := Finset.nonempty_iff_ne_empty.mpr hErase
          have hlt : (F.erase i).card < F.card := Finset.card_erase_lt_of_mem hiF
          have hP : prodSub B (F.erase i) ≤
              (R ⊓ (prodSub B (F.erase i)).comap θ).map θ := by
            intro s hs
            have hsF : s ∈ prodSub B F :=
              a210rec_prodSub_mono (Finset.erase_subset i F) hs
            rw [← hRF] at hsF
            obtain ⟨r, hr, hrθ⟩ := Subgroup.mem_map.mp hsF
            exact Subgroup.mem_map.mpr
              ⟨r, ⟨hr, Subgroup.mem_comap.mpr (by rw [hrθ]; exact hs)⟩, hrθ⟩
          obtain ⟨R', hR'leP, hR'perf, hR'map⟩ := SimpleFactors.exists_perfect_sub hB θ hP
          have hlt' : (F.erase i).card < n := hcard ▸ hlt
          obtain ⟨y', hy'prop, hy'comm⟩ :=
            ih (F.erase i).card hlt' (F.erase i) rfl hF' R' hR'perf hR'map
          refine ⟨Function.update y' i yᵢ, ?_, ?_⟩
          · intro j hj
            by_cases hji : j = i
            · rw [hji, Function.update_self]
              exact ⟨hyᵢR, hyᵢ3, hyᵢord, hyᵢsupp⟩
            · have hj' : j ∈ F.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
              rw [Function.update_of_ne hji yᵢ y']
              have hy' := hy'prop j hj'
              exact ⟨(hR'leP.trans inf_le_left) hy'.1, hy'.2⟩
          · intro j hj l hl
            by_cases hji : j = i
            · rw [hji]
              by_cases hli : l = i
              · simp only [hli, Function.update_self]
              · have hl' : l ∈ F.erase i := Finset.mem_erase.mpr ⟨hli, hl⟩
                rw [Function.update_self, Function.update_of_ne hli yᵢ y']
                have hy'l : y' l ∈ R' := (hy'prop l hl').1
                have hmemR : y' l ∈ R := (hR'leP.trans inf_le_left) hy'l
                have hθmem : θ (y' l) ∈ prodSub B (F.erase i) := by
                  have hthis : θ (y' l) ∈ R'.map θ := Subgroup.mem_map_of_mem θ hy'l
                  rwa [hR'map] at hthis
                exact hJcomm (y' l) hmemR hθmem yᵢ hyᵢJ
            · by_cases hli : l = i
              · rw [hli]
                have hj' : j ∈ F.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
                rw [Function.update_of_ne hji yᵢ y', Function.update_self]
                have hy'j : y' j ∈ R' := (hy'prop j hj').1
                have hmemR : y' j ∈ R := (hR'leP.trans inf_le_left) hy'j
                have hθmem : θ (y' j) ∈ prodSub B (F.erase i) := by
                  have hthis : θ (y' j) ∈ R'.map θ := Subgroup.mem_map_of_mem θ hy'j
                  rwa [hR'map] at hthis
                exact (hJcomm (y' j) hmemR hθmem yᵢ hyᵢJ).symm
              · have hj' : j ∈ F.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
                have hl' : l ∈ F.erase i := Finset.mem_erase.mpr ⟨hli, hl⟩
                rw [Function.update_of_ne hji yᵢ y', Function.update_of_ne hli yᵢ y']
                exact hy'comm j hj' l hl'
  exact main F.card F rfl hF R hR hRF

theorem card_le_three_of_pi_quotient (hB : SimpleFactors B)
    {X : Type} [Group X] [Finite X] (hX : CFSG.pRank 3 X ≤ 3) (θ : X →* ∀ i, B i)
    (hθ : Function.Surjective θ) : Fintype.card ι ≤ 3 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Fintype.card_eq_zero_iff.mpr hι]
    exact Nat.zero_le 3
  · have : Nonempty ι := hι
    have htop : prodSub B (Finset.univ : Finset ι) = (⊤ : Subgroup (∀ i, B i)) :=
      a210rec_prodSub_univ
    have : Group.IsPerfect (∀ i, B i) := by
      have h := hB.perfect_prodSub (Finset.univ : Finset ι)
      rw [htop] at h
      exact Group.IsPerfect.top_iff.mp h
    have hπ : Function.Surjective (θ.comp (⊤ : Subgroup X).subtype) := by
      intro s
      obtain ⟨x, hx⟩ := hθ s
      refine ⟨⟨x, Subgroup.mem_top x⟩, ?_⟩
      show θ x = s
      exact hx
    obtain ⟨Y, hGY, hFY, P, hPN, hYperf, hP3, ⟨e⟩, hmin, hrank, _⟩ :=
      CFSG.LocalAnalysis.WeakClosure81.Asch22.exists_perfect_pCover_of_surjective
        (p := 3) (by norm_num) (⊤ : Subgroup X) (θ.comp (⊤ : Subgroup X).subtype) hπ
    let : Group Y := hGY
    let : Finite Y := hFY
    let : P.Normal := hPN
    let θ' : Y →* (∀ i, B i) := e.toMonoidHom.comp (QuotientGroup.mk' P)
    have hθ' : Function.Surjective θ' := by
      intro s
      obtain ⟨q, hq⟩ := e.surjective s
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective P q
      exact ⟨y, by simpa [θ'] using hq⟩
    have hker : θ'.ker = P := by
      change (e.toMonoidHom.comp (QuotientGroup.mk' P)).ker = P
      rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' P) e.toMonoidHom e.injective,
        QuotientGroup.ker_mk']
    have hQ' : IsPGroup 3 θ'.ker := by
      rw [hker]
      exact hP3
    have hYrank : CFSG.pRank 3 Y ≤ 3 := by
      calc CFSG.pRank 3 Y = CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
            CFSG.SectionRank.pRank_eq_open_pRank_top 3 Y
        _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := hrank
        _ = CFSG.pRank 3 X := (CFSG.SectionRank.pRank_eq_open_pRank_top 3 X).symm
        _ ≤ 3 := hX
    have htopmap : (⊤ : Subgroup Y).map θ' = prodSub B (Finset.univ : Finset ι) := by
      rw [Subgroup.map_top_of_surjective θ' hθ']
      exact htop.symm
    obtain ⟨y, hyprop, hycomm⟩ :=
      rec_commuting_three_elements hB θ' hQ' hYrank (Finset.univ : Finset ι)
        Finset.univ_nonempty ⊤ (Group.IsPerfect.top_iff.mpr hYperf) htopmap
    have hcardrank : Fintype.card ι ≤ CFSG.pRank 3 Y :=
      card_le_pRank_of_commuting θ' y
        (fun j l => hycomm j (Finset.mem_univ j) l (Finset.mem_univ l))
        (fun j => (hyprop j (Finset.mem_univ j)).2.2.1)
        (fun j i => (hyprop j (Finset.mem_univ j)).2.2.2 i)
    exact hcardrank.trans hYrank

end CFSG.LocalAnalysis.WeakClosure81.Asch210
