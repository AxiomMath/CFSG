module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddAmalCase
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddTwoRank
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddNatAct
public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddG2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

theorem stmt5_1_17_amalgam_of
    (hI : L2OddInnerFact) (hmNine : Stmt5_1_17_mNine) (hAut : L34AutTwoRankFact) :
    Stmt5_1_17_amalgam := by
  intro G _ _ T M L V H B D n s hTI hF81
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hn := s.one_le_n
  have hne : ∀ {A B : Subgroup G}, A.relIndex B ≠ 0 := Subgroup.index_ne_zero_of_finite
  set Z₁ := quasithinOmegaOneCenter T ⊓ V with hZ₁
  set H₁ := H ⊔ D with hH₁
  set U := conjClosure V H₁ with hUdef
  set Q₁ := pCoreOf 2 H₁ with hQ₁
  obtain ⟨γ, γ', g, s8⟩ := F8.exists_F8Setup hF81
  have hyp := hF81.amalgamHypV
  set x := (g : G) with hx
  set X' := conjSub x H₁ with hX'
  set Q' := pCoreOf 2 X' with hQ'
  set A₁ := F8.A₁ Z₁ x with hA₁
  set U' := F8.Uγ V H₁ x with hU'
  set DH := F8.DH V Z₁ H₁ x with hDH
  set Dγ := F8.Dγ V Z₁ H₁ x with hDγ
  have hA₁' : A₁ = conjSub x Z₁ := rfl
  have hU'' : U' = conjSub x U := rfl
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H₁) (L ⊔ T) H₁ V := (F8.three_le_b_and_odd hF81).1
  have hstab : stab γ = X' := by
    rw [← s8.edge₁, stab_smul, stab_γ₁ hyp.le₂]
  have hUX' : U ≤ X' := by
    have h1 := (F8.F87_2 hF81 s8).1
    rw [← hstab]
    exact h1.trans ((pCoreOf_le 2 _).trans inf_le_right)
  have hU'H₁ : U' ≤ H₁ := by
    obtain ⟨-, ⟨γ₂, hγ₂, hd⟩⟩ :=
      exists_nbrs_of_geodesic hyp.gen s8.critical.geodesic (by omega : 2 ≤ _)
    refine ((F8.F87_2 hF81 s8).2 γ₂ hγ₂ hd).trans ((pCoreOf_le 2 _).trans (inf_le_left.trans ?_))
    rw [stab_γ₁ hyp.le₂]
  have hUab : IsElemAbelian 2 U := F8.isElemAbelian_conjClosure hF81
  have hU'ab : IsElemAbelian 2 U' := CFSG.SectionRank.isElemAbelian_map hUab _
  have hH₁Z : H₁ ≤ Subgroup.normalizer (Z₁ : Set G) := hF81.H_normalizes_V₁
  have hVH₁ : V ≤ H₁ := hF81.V_le_H
  have hUH₁ : U ≤ H₁ := conjClosure_le fun h hh' v hv =>
    H₁.mul_mem (H₁.mul_mem hh' (hVH₁ hv)) (H₁.inv_mem hh')
  have hUNZ : U ≤ Subgroup.normalizer (Z₁ : Set G) := hUH₁.trans hH₁Z
  have hU'NA : U' ≤ Subgroup.normalizer (A₁ : Set G) := by
    rw [hU'', hA₁']
    exact conjSub_le_normalizer hUNZ
  have hQ₁eq : Q₁ = centralizerMod Z₁ H₁ U := hF81.F82_3
  have hQ'eq : Q' = centralizerMod A₁ X' U' := by
    rw [hQ', hX', pCoreOf_conjSub, ← hQ₁, hQ₁eq, conjSub_centralizerMod]
    rfl
  have hU'Q : ∀ y ∈ U', y ∈ Q₁ ↔ y ∈ Dγ := by
    intro y hy
    rw [hQ₁eq]
    exact ⟨fun h => ⟨hy, h.2.1, h.2.2⟩, fun h => ⟨hU'H₁ hy, h.2.1, h.2.2⟩⟩
  have hUQ' : ∀ y ∈ U, y ∈ Q' ↔ y ∈ DH := by
    intro y hy
    rw [hQ'eq]
    exact ⟨fun h => ⟨hy, h.2.1, h.2.2⟩, fun h => ⟨hUX' hy, h.2.1, h.2.2⟩⟩
  have h876 := F8.F87_6 V Z₁ H₁ x
  have hU'D : ∀ w ∈ U', ∀ d ∈ DH, w * d * w⁻¹ * d⁻¹ ∈ A₁ := fun w hw d hd => by
    have := h876.1 (Subgroup.commutator_mem_commutator hw hd)
    rwa [commutatorElement_def] at this
  have hUD' : ∀ w ∈ U, ∀ d ∈ Dγ, w * d * w⁻¹ * d⁻¹ ∈ Z₁ := fun w hw d hd => by
    have := h876.2 (Subgroup.commutator_mem_commutator hw hd)
    rwa [commutatorElement_def] at this
  have h877 := F8.F87_7 hF81 s8
  have hcomm : ∀ a ∈ DH, ∀ b ∈ Dγ, a * b = b * a := fun a ha b hb => by
    have h1 : ⁅a, b⁆ ∈ ⁅DH, Dγ⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h877, Subgroup.mem_bot, commutatorElement_def] at h1
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  have hDHU : DH ≤ U := centralizerMod_le_left _ _ _
  have hDγU' : Dγ ≤ U' := centralizerMod_le_left _ _ _
  have hmN := hmNine G T M L V H B D n s hF81
  have hmN' : ∀ y ∈ X', y ∉ Q' → y ^ 2 ∈ Q' →
      2 ^ 9 ≤ (centralizerMod A₁ U' (Subgroup.zpowers y)).relIndex U' := by
    intro y hy hyQ hy2
    have hQ'c : Q' = conjSub x Q₁ := by rw [hQ', hX', pCoreOf_conjSub]
    have hy' : x⁻¹ * y * x ∈ H₁ := mem_conjSub.mp hy
    have hyQ' : x⁻¹ * y * x ∉ Q₁ := fun h => hyQ (by rw [hQ'c]; exact mem_conjSub.mpr h)
    have hy2' : (x⁻¹ * y * x) ^ 2 ∈ Q₁ := by
      have := mem_conjSub.mp (hQ'c ▸ hy2)
      have e : (x⁻¹ * y * x) ^ 2 = x⁻¹ * y ^ 2 * x := by rw [sq, sq]; group
      rw [e]
      exact this
    have h1 := hmN _ hy' hyQ' hy2'
    have h2 : conjSub x (Subgroup.zpowers (x⁻¹ * y * x)) = Subgroup.zpowers y := by
      rw [conjSub, MonoidHom.map_zpowers]
      congr 1
      simp [MulAut.conj_apply, mul_assoc]
    have h3 : (centralizerMod A₁ U' (Subgroup.zpowers y)).relIndex U' =
        (centralizerMod Z₁ U (Subgroup.zpowers (x⁻¹ * y * x))).relIndex U := by
      rw [hA₁', hU'', ← h2, ← conjSub_centralizerMod]
      exact Subgroup.relIndex_map_map_of_injective _ _
        (fun a b h => (MulAut.conj x).injective h : Function.Injective (MulAut.conj x).toMonoidHom)
    rw [h3]
    exact h1
  have hrk : ∀ E : Subgroup G, E ≤ H₁ → IsElemAbelian 2 E → Q₁.relIndex E ≤ 2 ^ 4 :=
    fun E hE hEab => s.two_rank_le hI hAut hE hEab
  have hrk' : ∀ E : Subgroup G, E ≤ X' → IsElemAbelian 2 E → Q'.relIndex E ≤ 2 ^ 4 := by
    intro E hE hEab
    have hE' : conjSub x⁻¹ E ≤ H₁ := by
      have := conjSub_mono x⁻¹ hE
      rwa [hX', conjSub_conjSub_inv] at this
    have h1 := hrk _ hE' (CFSG.SectionRank.isElemAbelian_map hEab _)
    have h2 : Q'.relIndex E = Q₁.relIndex (conjSub x⁻¹ E) := by
      rw [← Subgroup.relIndex_map_map_of_injective _ _
        (fun a b h => (MulAut.conj x⁻¹).injective h :
          Function.Injective (MulAut.conj x⁻¹).toMonoidHom)]
      change (conjSub x⁻¹ Q').relIndex (conjSub x⁻¹ E) = _
      rw [hQ', hX', pCoreOf_conjSub, conjSub_conjSub_inv]
    rw [h2]
    exact h1
  have hVnat : ∀ k : G, ∀ E : Subgroup G, E ≤ Subgroup.normalizer (conjSub k V : Set G) →
      IsPGroup 2 E →
      (Subgroup.centralizer (conjSub k V : Set G)).relIndex E ≤ 2 ^ n ∧
        (¬ E ≤ Subgroup.centralizer (conjSub k V : Set G) →
          2 ^ n ≤ (Subgroup.centralizer (E : Set G)).relIndex (conjSub k V)) :=
    fun k E hE hE2 => ⟨s.relIndex_centralizer_conjSub_le hI k hE hE2,
      s.le_relIndex_centralizer_conjSub hI k hE hE2⟩
  have hZV : Z₁ ≤ V := inf_le_right
  set 𝒲 : Set (Subgroup G) := {W | ∃ h ∈ H₁, W = conjSub h V} with h𝒲
  set 𝒲' : Set (Subgroup G) := {W | ∃ h ∈ H₁, W = conjSub (x * h) V} with h𝒲'
  have hgen : ∀ S : Subgroup G, (∀ W ∈ 𝒲, W ≤ S) → U ≤ S := fun S hS =>
    conjClosure_le fun h hh' v hv => hS _ ⟨h, hh', rfl⟩ (mul_mem_conjSub hv)
  have hgen' : ∀ S : Subgroup G, (∀ W ∈ 𝒲', W ≤ S) → U' ≤ S := by
    intro S hS
    rw [hU'', conjSub_le_iff]
    refine hgen _ fun W hW => ?_
    obtain ⟨h, hh', rfl⟩ := hW
    rw [← conjSub_le_iff, ← conjSub_mul]
    exact hS _ ⟨h, hh', rfl⟩
  have hWZ : ∀ W ∈ 𝒲, Z₁ ≤ W := by
    rintro _ ⟨h, hh', rfl⟩
    rw [← F7.conjSub_eq_of_mem_normalizer (hH₁Z hh')]
    exact conjSub_mono h hZV
  have hWZ' : ∀ W ∈ 𝒲', A₁ ≤ W := by
    rintro _ ⟨h, hh', rfl⟩
    rw [hA₁', conjSub_mul]
    exact conjSub_mono x (hWZ _ ⟨h, hh', rfl⟩)
  have hWU : ∀ W ∈ 𝒲, W ≤ U := by
    rintro _ ⟨h, hh', rfl⟩
    intro v hv
    have := mem_conjClosure hh' (mem_conjSub.mp hv)
    simpa [mul_assoc] using this
  have hWU' : ∀ W ∈ 𝒲', W ≤ U' := by
    rintro _ ⟨h, hh', rfl⟩
    rw [hU'', conjSub_mul]
    exact conjSub_mono x (hWU _ ⟨h, hh', rfl⟩)
  have hnat : ∀ W ∈ 𝒲, ∀ E : Subgroup G, E ≤ Subgroup.normalizer (W : Set G) → IsPGroup 2 E →
      (Subgroup.centralizer (W : Set G)).relIndex E ≤ 2 ^ n ∧
        (¬ E ≤ Subgroup.centralizer (W : Set G) →
          2 ^ n ≤ (Subgroup.centralizer (E : Set G)).relIndex W) := by
    rintro _ ⟨h, -, rfl⟩
    exact hVnat h
  have hnat' : ∀ W ∈ 𝒲', ∀ E : Subgroup G, E ≤ Subgroup.normalizer (W : Set G) →
      IsPGroup 2 E → (Subgroup.centralizer (W : Set G)).relIndex E ≤ 2 ^ n ∧
        (¬ E ≤ Subgroup.centralizer (W : Set G) →
          2 ^ n ≤ (Subgroup.centralizer (E : Set G)).relIndex W) := by
    rintro _ ⟨h, -, rfl⟩
    exact hVnat (x * h)
  by_cases hU'Q₁ : U' ≤ Q₁
  ·
    have hU'Dγ : ∀ y ∈ U', y ∈ Dγ := fun y hy => (hU'Q y hy).mp (hU'Q₁ hy)
    have h5a := F8.F87_5a hF81 s8
    obtain ⟨l, hl, hlZ⟩ : ∃ l ∈ L,
        ¬ U' ≤ Subgroup.centralizer (conjSub l Z₁ : Set G) := by
      by_contra hall
      push Not at hall
      apply h5a
      have hVC : V ≤ Subgroup.centralizer (U' : Set G) := by
        rw [s.V_eq_conjClosure]
        refine conjClosure_le fun l hl z hz => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (Subgroup.mem_centralizer_iff.mp (hall l hl hu) _ (mul_mem_conjSub hz)).symm
      have : ⁅U', V⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVC
      rw [this]
      exact bot_le
    set Zl := conjSub l Z₁ with hZl
    have hZlV : Zl ≤ V := by
      rw [hZl, ← F7.conjSub_eq_of_mem_normalizer (s.L_le_normalizer_V hl)]
      exact conjSub_mono l hZV
    have hZlU : Zl ≤ U := hZlV.trans (le_conjClosure V H₁)
    have hZlD : Zl ⊓ DH = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      by_contra hz1
      apply hlZ
      have hU'z : U' ≤ Subgroup.centralizer ({z} : Set G) := fun u hu => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm z hz.2 u (hU'Dγ u hu)).symm
      exact Setup5_1_17Odd.le_centralizer_of_isTISetUnder hTI (hh.isSylowTwoOf le_top) l hz.1
        hz1 (isPGroup_of_isElemAbelian hU'ab) hU'z
    have hZlQ : Q'.relIndex Zl = Nat.card Zl := by
      have h1 : Q' ⊓ Zl = ⊥ := by
        rw [eq_bot_iff]
        rintro y ⟨hyQ, hyZ⟩
        have : y ∈ Zl ⊓ DH := ⟨hyZ, (hUQ' y (hZlU hyZ)).mp hyQ⟩
        rwa [hZlD] at this
      rw [← Subgroup.inf_relIndex_right, h1, Subgroup.relIndex_bot_left]
    have hcardZl : Nat.card Zl = 2 ^ n := by
      rw [hZl, conjSub, Subgroup.card_map_of_injective (MulAut.conj l).injective, s.card_Z₁ hI]
    have hZlab : IsElemAbelian 2 Zl :=
      ⟨⟨⟨fun a b => Subtype.ext (F7.isElemAbelian_comm hUab (hZlU a.2) (hZlU b.2))⟩⟩,
        fun y hy => hUab.2 y (hZlU hy)⟩
    have hn4 : 2 ^ n ≤ 2 ^ 4 := by
      rw [← hcardZl, ← hZlQ]
      exact hrk' Zl (hZlU.trans hUX') hZlab
    obtain ⟨⟨y, hyZ⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (fun h0 => by
      have : Nat.card Zl = 1 := by rw [h0, Subgroup.card_bot]
      have h2 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega : Zl ≠ ⊥)
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hyQ' : y ∉ Q' := fun h => by
      have : y ∈ Zl ⊓ DH := ⟨hyZ, (hUQ' y (hZlU hyZ)).mp h⟩
      rw [hZlD, Subgroup.mem_bot] at this
      exact hy1' this
    have hy2 : y ^ 2 ∈ Q' := by rw [hUab.2 y (hZlU hyZ)]; exact Q'.one_mem
    have h9 := hmN' y (hUX' (hZlU hyZ)) hyQ' hy2
    have hC : Subgroup.centralizer ({y} : Set G) ⊓ U' ≤
        centralizerMod A₁ U' (Subgroup.zpowers y) := by
      rintro u ⟨huC, huU⟩
      refine ⟨huU, hU'NA huU, fun w hw => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hc : u * y ^ k = y ^ k * u :=
        ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp huC) k))
      rw [hc, mul_inv_cancel_right, mul_inv_cancel]
      exact A₁.one_mem
    have h1 := Subgroup.relIndex_le_of_le_left hC
      (hne (A := Subgroup.centralizer ({y} : Set G) ⊓ U') (B := U'))
    rw [Subgroup.inf_relIndex_right] at h1
    have h2 : (Subgroup.centralizer ({y} : Set G)).relIndex U' ≤ Nat.card Z₁ := by
      refine relIndex_centralizer_le_card fun u hu => ?_
      have := Z₁.inv_mem (hUD' y (hZlU hyZ) u (hU'Dγ u hu))
      have e : (y * u * y⁻¹ * u⁻¹)⁻¹ = u * y * u⁻¹ * y⁻¹ := by group
      rwa [e] at this
    rw [s.card_Z₁ hI] at h2
    omega
  ·
    obtain ⟨y, hyU', hyQ⟩ := Set.not_subset.mp hU'Q₁
    have hlt : ∃ y ∈ U', y ∉ Dγ := ⟨y, hyU', fun h => hyQ ((hU'Q y hyU').mpr h)⟩
    by_cases hle : DH.relIndex U ≤ Dγ.relIndex U'
    · exact amalgam_counting hn hDHU hU'Q hU'H₁ hUNZ hUab hU'ab hcomm hU'D hmN hrk 𝒲' hgen'
        hWZ' hWU' hnat' hlt hle
    · have hlt' : ∃ y ∈ U, y ∉ DH := by
        by_contra hall
        push Not at hall
        have : DH.relIndex U = 1 := Subgroup.relIndex_eq_one.mpr hall
        have := Nat.pos_of_ne_zero (hne (A := Dγ) (B := U'))
        omega
      exact amalgam_counting hn hDγU' hUQ' hUX' hU'NA hU'ab hUab
        (fun a ha b hb => (hcomm b hb a ha).symm) hUD' hmN' hrk' 𝒲 hgen hWZ hWU hnat hlt'
        (by omega)

end CFSG.Quasithin.H13
