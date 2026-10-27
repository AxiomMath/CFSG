module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
public import CFSG.Quasithin.Background.SmithB42Disp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open ArithmeticFunction

section Chain

variable {G : Type*} [Group G] [Finite G]

private theorem cardFactors_lt_of_lt {H K : Subgroup G} (h : H < K) :
    cardFactors (Nat.card H) < cardFactors (Nat.card K) := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le h.le
  have hK : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hK hm
  have hH : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact h.ne (Subgroup.eq_of_le_of_card_ge h.le hm.le)
  have hpos : 0 < cardFactors m := by
    rw [Nat.pos_iff_ne_zero, Ne, cardFactors_eq_zero_iff_eq_zero_or_one]
    tauto
  rw [hm, cardFactors_mul hH hm0]
  omega

theorem exists_list_le_closure (K L : Subgroup G) (f : G → G) (hf : ∀ h ∈ K, f h ∈ K)
    (hL : L ≤ Subgroup.closure (f '' (K : Set G))) :
    ∃ hs : List G, hs.length ≤ cardFactors (Nat.card K) ∧
      L ≤ Subgroup.closure {y | ∃ h ∈ hs, y = f h} := by
  have key : ∀ n : ℕ, ∀ hs : List G, (∀ h ∈ hs, h ∈ K) →
      cardFactors (Nat.card K) ≤
        cardFactors (Nat.card (Subgroup.closure {y | ∃ h ∈ hs, y = f h})) + n →
      ∃ hs' : List G, hs'.length ≤ hs.length + n ∧
        L ≤ Subgroup.closure {y | ∃ h ∈ hs', y = f h} := by
    intro n
    induction n with
    | zero =>
      intro hs hsK hle
      refine ⟨hs, by omega, ?_⟩
      set H := Subgroup.closure {y | ∃ h ∈ hs, y = f h}
      have hHK : H ≤ K :=
        (Subgroup.closure_le K).2 (by rintro y ⟨h, hh, rfl⟩; exact hf h (hsK h hh))
      have hEq : H = K := by
        by_contra hne
        have := cardFactors_lt_of_lt (lt_of_le_of_ne hHK hne)
        omega
      rw [hEq]
      exact hL.trans ((Subgroup.closure_le K).2 (by rintro y ⟨h, hh, rfl⟩; exact hf h hh))
    | succ n ih =>
      intro hs hsK hle
      set H := Subgroup.closure {y | ∃ h ∈ hs, y = f h} with hHdef
      by_cases hLH : L ≤ H
      · exact ⟨hs, by omega, hLH⟩
      have hex : ∃ h ∈ K, f h ∉ H := by
        by_contra hcon
        simp only [not_exists, not_and, not_not] at hcon
        exact hLH (hL.trans
          ((Subgroup.closure_le H).2 (by rintro y ⟨h, hh, rfl⟩; exact hcon h hh)))
      obtain ⟨h, hhK, hfh⟩ := hex
      set H' := Subgroup.closure {y | ∃ g ∈ h :: hs, y = f g} with hH'def
      have hHH' : H ≤ H' := Subgroup.closure_mono (by
        rintro y ⟨g, hg, rfl⟩; exact ⟨g, List.mem_cons_of_mem _ hg, rfl⟩)
      have hfH' : f h ∈ H' := Subgroup.subset_closure ⟨h, List.mem_cons_self .., rfl⟩
      have hlt : H < H' := lt_of_le_of_ne hHH' (fun e => hfh (e ▸ hfH'))
      have hΩ := cardFactors_lt_of_lt hlt
      have hle' : cardFactors (Nat.card K) ≤ cardFactors (Nat.card H') + n := by omega
      obtain ⟨hs', hlen, hL'⟩ := ih (h :: hs) (by
        intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · exact hhK
        · exact hsK g hg) hle'
      exact ⟨hs', by simp only [List.length_cons] at hlen; omega, hL'⟩
  obtain ⟨hs', hlen, hL'⟩ := key (cardFactors (Nat.card K)) [] (by simp) (Nat.le_add_left _ _)
  exact ⟨hs', by simpa using hlen, hL'⟩

end Chain

section Closure

variable {W : Type} [CommGroup W] [Finite W]

private theorem conj_mem_closure_conj {Y : Subgroup (MulAut W)} {t : MulAut W} {y : MulAut W}
    (hy : y ∈ Y) {x : MulAut W}
    (hx : x ∈ Subgroup.closure ((fun h => h * t * h⁻¹) '' (Y : Set (MulAut W)))) :
    y * x * y⁻¹ ∈ Subgroup.closure ((fun h => h * t * h⁻¹) '' (Y : Set (MulAut W))) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨y * h, Y.mul_mem hy hh, by group⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [this]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ ha

theorem le_closure_conj_of_involution_of_cent {K L : Subgroup (MulAut W)} (hLK : L ≤ K)
    (hn : (L.subgroupOf K).Normal)
    (hcent : ∀ y ∈ K, y ∈ Subgroup.centralizer (L : Set (MulAut W)) → y ∈ L)
    (hq : IsQuasisimple ↥L) (hO2 : O2Trivial L) {t : MulAut W} (ht : t ∈ K)
    (ht2 : orderOf t = 2) :
    L ≤ Subgroup.closure ((fun h => h * t * h⁻¹) '' (K : Set (MulAut W))) := by
  set N := Subgroup.closure ((fun h => h * t * h⁻¹) '' (K : Set (MulAut W))) with hNdef
  have hLnorm : ∀ y ∈ K, ∀ l ∈ L, y * l * y⁻¹ ∈ L := by
    intro y hy l hl
    have := hn.conj_mem ⟨l, hLK hl⟩ (Subgroup.mem_subgroupOf.2 hl) ⟨y, hy⟩
    exact Subgroup.mem_subgroupOf.1 this
  have htN : t ∈ N := Subgroup.subset_closure ⟨1, K.one_mem, by group⟩
  have hMn : (N.subgroupOf L).Normal := by
    constructor
    intro x hx l
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact conj_mem_closure_conj (hLK l.2) hx
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hMn with htop | hcen
  · intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ N.subgroupOf L := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  exfalso
  have hZ : ⁅L, Subgroup.zpowers t⁆ ≤ (Subgroup.center ↥L).map L.subtype := by
    rw [Subgroup.commutator_le]
    intro l hl s hs
    have hsY : s ∈ K := (Subgroup.zpowers_le.2 ht) hs
    have hsN : s ∈ N := (Subgroup.zpowers_le.2 htN) hs
    rw [commutatorElement_def]
    have h1 : l * s * l⁻¹ * s⁻¹ ∈ N :=
      Subgroup.mul_mem _ (conj_mem_closure_conj (hLK hl) hsN) (Subgroup.inv_mem _ hsN)
    have h2 : l * s * l⁻¹ * s⁻¹ ∈ L := by
      have : l * s * l⁻¹ * s⁻¹ = l * (s * l⁻¹ * s⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hl (hLnorm s hsY _ (Subgroup.inv_mem _ hl))
    exact ⟨⟨_, h2⟩, hcen (Subgroup.mem_subgroupOf.2 h1), rfl⟩
  have hZL : ∀ H : Subgroup (MulAut W), H ≤ (Subgroup.center ↥L).map L.subtype →
      ⁅H, L⁆ = ⊥ := by
    intro H hH
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx l hl
    obtain ⟨c, hc, rfl⟩ := hH hx
    have := Subgroup.mem_center_iff.1 hc ⟨l, hl⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg Subtype.val this).symm
  have hA : ⁅⁅L, Subgroup.zpowers t⁆, L⁆ = ⊥ := hZL _ hZ
  have hB : ⁅⁅Subgroup.zpowers t, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (Subgroup.zpowers t) L]; exact hA
  have hLL : ⁅L, L⁆ = L := by
    have hp : commutator ↥L = ⊤ := hq.1.commutator_eq_top
    have hmap : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← hmap, hp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hC : ⁅⁅L, L⁆, Subgroup.zpowers t⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hA hB
  rw [hLL] at hC
  have htc : t ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers t)
    rw [hC, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have htL : t ∈ L := hcent t ht htc
  have htZ : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 htc g g.2)
  have hodd := odd_card_center_of_o2Trivial hO2
  have hdvd : orderOf (⟨⟨t, htL⟩, htZ⟩ : ↥(Subgroup.center ↥L)) ∣
      Nat.card (Subgroup.center ↥L) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ht2] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

end Closure

section TheoremA

variable {W : Type} [CommGroup W] [Finite W]

private theorem fixV_antitone' {X X' : Subgroup (MulAut W)} (h : X ≤ X') : fixV X' ≤ fixV X :=
  fun _ hv x hx => hv x (h hx)

theorem index_fixV_le_of_le {X X' : Subgroup (MulAut W)} (h : X ≤ X') :
    (fixV X).index ≤ (fixV X').index :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
    (Subgroup.index_dvd_of_le (fixV_antitone' h))

theorem index_fixV_le_pow_cardFactors_of_cent {K L : Subgroup (MulAut W)} (hLK : L ≤ K)
    (hn : (L.subgroupOf K).Normal)
    (hC : ∀ y ∈ K, y ∈ Subgroup.centralizer (L : Set (MulAut W)) → y ∈ L)
    (hq : IsQuasisimple ↥L) (hO2 : O2Trivial L) {t : MulAut W} (ht : t ∈ K)
    (ht2 : orderOf t = 2) :
    (fixV L).index ≤ (fixV (zpowers t)).index ^ cardFactors (Nat.card K) := by
  obtain ⟨hs, hlen, hL⟩ := exists_list_le_closure K L (fun h => h * t * h⁻¹)
    (fun h hh => K.mul_mem (K.mul_mem hh ht) (K.inv_mem hh))
    (le_closure_conj_of_involution_of_cent hLK hn hC hq hO2 ht ht2)
  calc (fixV L).index
      ≤ (fixV (Subgroup.closure {y | ∃ h ∈ hs, y = h * t * h⁻¹})).index :=
        index_fixV_le_of_le hL
    _ ≤ (fixV (zpowers t)).index ^ hs.length := B42Disp.index_fixV_closure_conj_elt_le t hs
    _ ≤ (fixV (zpowers t)).index ^ cardFactors (Nat.card K) :=
        Nat.pow_le_pow_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hlen

end TheoremA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
