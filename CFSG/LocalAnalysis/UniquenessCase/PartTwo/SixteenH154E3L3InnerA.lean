module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3Gen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoverA
import CFSG.Quasithin.EmptyFaithful.F918C13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private def s16h_e3_l3_commHom {M : Type} [CommGroup M] (c : MulAut M) : M →* M where
  toFun u := c u * u⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv_rev]
    ac_rfl

private theorem s16h_e3_l3_commHom_apply {M : Type} [CommGroup M] (c : MulAut M) (u : M) :
    s16h_e3_l3_commHom c u = c u * u⁻¹ := rfl

private theorem s16h_e3_l3_commHom_mul {M : Type} [CommGroup M] {c l : MulAut M}
    (hc : c * l = l * c) (u : M) :
    s16h_e3_l3_commHom c (l u) = l (s16h_e3_l3_commHom c u) := by
  show c (l u) * (l u)⁻¹ = l (c u * u⁻¹)
  rw [map_mul l (c u) u⁻¹, map_inv l u]
  have hcl : c (l u) = l (c u) := by
    have h := congrArg (fun f : MulAut M => f u) hc
    simpa [MulAut.mul_apply] using h
  rw [hcl]

private theorem s16h_e3_l3_zpow_eq_one_or_self {G : Type} [Group G] {c : G}
    (hc2 : c ^ 2 = 1) : ∀ n : ℤ, c ^ n = 1 ∨ c ^ n = c := by
  intro n
  have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact hc2
  rcases Int.even_or_odd' n with ⟨k, hk | hk⟩
  · left
    rw [hk, zpow_mul c 2 k, h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul c 2 k, h2, one_zpow, one_mul, zpow_one]

private theorem s16h_e3_l3_commSub_zpowers_eq_closure {M : Type} [CommGroup M]
    {g : MulAut M} (hg2 : g ^ 2 = 1) (X : Subgroup M) :
    commSub X (Subgroup.zpowers g) =
      Subgroup.closure {y : M | ∃ x ∈ X, g x * x⁻¹ = y} := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases s16h_e3_l3_zpow_eq_one_or_self hg2 n with hn | hn
    · rw [hn]
      simpa using (Subgroup.closure {y : M | ∃ x ∈ X, g x * x⁻¹ = y}).one_mem
    · rw [hn]
      exact Subgroup.subset_closure ⟨w, hw, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.subset_closure ⟨g, Subgroup.mem_zpowers g, w, hw, rfl⟩

private theorem s16h_e3_l3_commSub_zpowers_eq_map {M : Type} [CommGroup M]
    {c : MulAut M} (hc2 : c ^ 2 = 1) (U : Subgroup M) :
    commSub U (Subgroup.zpowers c) = U.map (s16h_e3_l3_commHom c) := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rcases s16h_e3_l3_zpow_eq_one_or_self hc2 n with hn | hn
    · rw [hn]
      have hgen : (1 : MulAut M) w * w⁻¹ = 1 := by
        rw [show (1 : MulAut M) w = w from rfl, mul_inv_cancel]
      rw [hgen]
      exact Subgroup.mem_map.mpr ⟨1, U.one_mem, map_one (s16h_e3_l3_commHom c)⟩
    · rw [hn]
      exact Subgroup.mem_map.mpr ⟨w, hw, s16h_e3_l3_commHom_apply c w⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [s16h_e3_l3_commHom_apply]
    exact Subgroup.subset_closure ⟨c, Subgroup.mem_zpowers c, u, hu, rfl⟩

private theorem s16h_e3_l3_centerless_of_isPSL {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    ∀ z : X, (∀ b : X, z * b = b * z) → z = 1 := by
  intro z hz
  haveI hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 h).2
  have hzmem : z ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun b => (hz b).symm
  have hcenter : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
    · exact hc
    · exfalso
      haveI : IsMulCommutative X := Subgroup.center_eq_top_iff.mp hc
      have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp hs
      rw [card_eq_168_of_isPSL_three_two h] at hp
      norm_num at hp
  rwa [hcenter, Subgroup.mem_bot] at hzmem

private theorem s16h_e3_l3_isPerfect_of_isPSL {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Group.IsPerfect X := by
  rw [Group.isPerfect_def]
  haveI hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 h).2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with hc | hc
  · exfalso
    haveI : IsMulCommutative X := (commutator_eq_bot_iff X).mp hc
    have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp hs
    rw [card_eq_168_of_isPSL_three_two h] at hp
    norm_num at hp
  · exact hc

omit [Finite W] in
theorem s16h_e3_l3_inner_decomp {L : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L)
    {τ γ : MulAut W} (hτ2 : τ ^ 2 = 1) (hγL : γ ∈ L)
    (hinn : ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    γ ^ 2 = 1 ∧ (γ⁻¹ * τ) ^ 2 = 1 ∧ ∀ l ∈ L, γ⁻¹ * τ * l = l * (γ⁻¹ * τ) := by
  let c : MulAut W := γ⁻¹ * τ
  have hτγ : τ = γ * c := by
    rw [show c = γ⁻¹ * τ from rfl]
    group
  have hcomm : ∀ l ∈ L, c * l = l * c := by
    intro l hl
    have h1 : c * l * c⁻¹ = l := by
      rw [show c = γ⁻¹ * τ from rfl]
      calc (γ⁻¹ * τ) * l * (γ⁻¹ * τ)⁻¹ = γ⁻¹ * (τ * l * τ⁻¹) * γ := by group
        _ = γ⁻¹ * (γ * l * γ⁻¹) * γ := by rw [hinn l hl]
        _ = l := by group
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hcenter := s16h_e3_l3_centerless_of_isPSL hL
  have hsq : γ ^ 2 * c ^ 2 = 1 := by
    have h : (γ * c) * (γ * c) = 1 := by
      rw [← pow_two, ← hτγ]
      exact hτ2
    have hcγ : Commute γ c := (hcomm γ hγL).symm
    have h2 : (γ * c) * (γ * c) = γ ^ 2 * c ^ 2 := by
      rw [← pow_two]
      exact hcγ.mul_pow 2
    rwa [h2] at h
  have hc2L : c ^ 2 ∈ L := by
    have h : c ^ 2 = (γ ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hsq
    rw [h]
    exact L.inv_mem (L.pow_mem hγL 2)
  have hc2 : c ^ 2 = 1 := by
    have hz := hcenter ⟨c ^ 2, hc2L⟩ (fun b => by
      apply Subtype.ext
      have hcb : Commute c (b : MulAut W) := hcomm (b : MulAut W) b.2
      exact (hcb.pow_left 2).eq)
    exact congrArg Subtype.val hz
  have hγ2 : γ ^ 2 = 1 := by
    have h := hsq
    rw [hc2, mul_one] at h
    exact h
  exact ⟨hγ2, hc2, hcomm⟩

theorem s16h_e3_l3_commSub_cent (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {U : Subgroup W} (hUinv : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hUc : commSub U L = U)
    {c : MulAut W} (hc2 : c ^ 2 = 1) (hcL : ∀ l ∈ L, c * l = l * c)
    (hcU : ∀ u ∈ U, c u ∈ U) :
    (∀ l ∈ L, ∀ m ∈ commSub U (Subgroup.zpowers c), l m ∈ commSub U (Subgroup.zpowers c)) ∧
      commSub (commSub U (Subgroup.zpowers c)) L = commSub U (Subgroup.zpowers c) ∧
      commSub U (Subgroup.zpowers c) ≤ fixV (Subgroup.zpowers c) ∧
      2 * rk ↥(commSub U (Subgroup.zpowers c)) ≤ rk ↥U := by
  let M : Subgroup W := commSub U (Subgroup.zpowers c)
  let φ : W →* W := s16h_e3_l3_commHom c
  have hMmap : M = U.map φ := s16h_e3_l3_commSub_zpowers_eq_map hc2 U
  have hMinv : ∀ l ∈ L, ∀ m ∈ M, l m ∈ M := by
    intro l hl m hm
    rw [hMmap] at hm ⊢
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hm
    exact Subgroup.mem_map.mpr ⟨l u, hUinv l hl u hu, s16h_e3_l3_commHom_mul (hcL l hl) u⟩
  have hMcomm : commSub M L = M := by
    apply le_antisymm
    · exact commSub_le_of_invariant hMinv
    · have hgen : commSub U L ≤ (commSub M L).comap φ := by
        rw [commSub, Subgroup.closure_le]
        rintro _ ⟨l, hl, w, hw, rfl⟩
        refine Subgroup.mem_comap.mpr ?_
        have hwM : φ w ∈ M :=
          Subgroup.subset_closure ⟨c, Subgroup.mem_zpowers c, w, hw, rfl⟩
        rw [map_mul, map_inv, s16h_e3_l3_commHom_mul (hcL l hl) w]
        exact Subgroup.subset_closure ⟨l, hl, φ w, hwM, rfl⟩
      have hle : U.map φ ≤ commSub M L := by
        rw [← hUc]
        exact (Subgroup.map_le_iff_le_comap).mpr hgen
      exact (le_of_eq hMmap).trans hle
  have hMfix : M ≤ fixV (Subgroup.zpowers c) := by
    have hcM : c ∈ centSub M := by
      rw [mem_centSub]
      intro m hm
      rw [hMmap] at hm
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hm
      show c (c u * u⁻¹) = c u * u⁻¹
      have hcu : c (c u) = u := by
        have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
        have h := congrArg (fun f : MulAut W => f u) hcc
        simpa [MulAut.mul_apply] using h
      rw [map_mul, map_inv, hcu]
      rw [inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hW (c u)),
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hW u)]
      exact mul_comm _ _
    intro m hm
    exact mem_fixV.mpr fun x hx => (mem_centSub.mp (Subgroup.zpowers_le.mpr hcM hx)) m hm
  have hMinf : M ≤ U ⊓ φ.ker := by
    refine le_inf ?_ ?_
    · intro m hm
      rw [hMmap] at hm
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hm
      show c u * u⁻¹ ∈ U
      exact U.mul_mem (hcU u hu) (U.inv_mem hu)
    · intro m hm
      rw [hMmap] at hm
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hm
      rw [MonoidHom.mem_ker]
      have hφuM : φ u ∈ M := Subgroup.subset_closure ⟨c, Subgroup.mem_zpowers c, u, hu, rfl⟩
      have hcu : c (φ u) = φ u := mem_fixV.mp (hMfix hφuM) c (Subgroup.mem_zpowers c)
      show c (φ u) * (φ u)⁻¹ = 1
      rw [hcu, mul_inv_cancel]
  have hcardM : Nat.card M * Nat.card M ≤ Nat.card U := by
    have hcard : Nat.card ↥(U.map φ) * Nat.card ↥(U ⊓ φ.ker) = Nat.card U :=
      B1More.card_map_mul_card_inf_ker U φ
    have hcard' : Nat.card M * Nat.card ↥(U ⊓ φ.ker) = Nat.card U := by
      rw [hMmap]
      exact hcard
    have hle : Nat.card M ≤ Nat.card ↥(U ⊓ φ.ker) := Subgroup.card_le_of_le hMinf
    calc Nat.card M * Nat.card M
        ≤ Nat.card M * Nat.card ↥(U ⊓ φ.ker) := Nat.mul_le_mul_left _ hle
      _ = Nat.card U := hcard'
  have hrk : 2 * rk M ≤ rk U := by
    have hpow : 2 ^ (rk M + rk M) ≤ 2 ^ rk U := by
      calc 2 ^ (rk M + rk M) = 2 ^ rk M * 2 ^ rk M := pow_add 2 (rk M) (rk M)
        _ = Nat.card M * Nat.card M := by rw [card_eq_two_pow hW M]
        _ ≤ Nat.card U := hcardM
        _ = 2 ^ rk U := card_eq_two_pow hW U
    have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
    omega
  exact ⟨hMinv, hMcomm, hMfix, hrk⟩

theorem s16h_e3_l3_commSub_cent_nontriv (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {U : Subgroup W} (hUinv : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hUc : commSub U L = U)
    {c : MulAut W} (hc2 : c ^ 2 = 1) (hcL : ∀ l ∈ L, c * l = l * c)
    (hcU : ∀ u ∈ U, c u ∈ U) (hcC : ∃ u ∈ U, c u ≠ u) :
    ∃ l ∈ L, ∃ m ∈ commSub U (Subgroup.zpowers c), l m * m⁻¹ ∉ fixV L := by
  let M : Subgroup W := commSub U (Subgroup.zpowers c)
  let φ : W →* W := s16h_e3_l3_commHom c
  have hMcomm : commSub M L = M := (s16h_e3_l3_commSub_cent hW hUinv hUc hc2 hcL hcU).2.1
  by_contra hcon
  have hcomm_le : commSub M L ≤ fixV L := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨l, hl, m, hm, rfl⟩
    by_contra hne
    exact hcon ⟨l, hl, m, hm, hne⟩
  have hMfixL : M ≤ fixV L := by
    rw [← hMcomm]
    exact hcomm_le
  have hkill : ∀ u ∈ U, φ u = 1 := by
    intro u hu
    have hu' : u ∈ commSub U L := by rw [hUc]; exact hu
    clear hu
    induction hu' using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨l, hl, w, hw, rfl⟩ := hx
        rw [map_mul, map_inv, s16h_e3_l3_commHom_mul (hcL l hl) w]
        have hwM : φ w ∈ M := Subgroup.subset_closure ⟨c, Subgroup.mem_zpowers c, w, hw, rfl⟩
        rw [mem_fixV.mp (hMfixL hwM) l hl, mul_inv_cancel]
    | one => exact map_one φ
    | mul a b _ _ iha ihb => rw [map_mul, iha, ihb, one_mul]
    | inv a _ iha => rw [map_inv, iha, inv_one]
  obtain ⟨u, hu, hcu⟩ := hcC
  exact hcu (by
    have h := hkill u hu
    rw [s16h_e3_l3_commHom_apply c u] at h
    exact mul_inv_eq_one.mp h)

theorem s16h_e3_l3_section_inner (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3)
    {τ : MulAut W} (hτ2 : τ ^ 2 = 1) (hτC : τ ∉ centSub (commSub ⊤ L)) {γ : MulAut W}
    (hγL : γ ∈ L) (hinn : ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹) :
    rk ↥(commSub ⊤ L ⊓ fixV L) + 3 ≤
      rk ↥(commSub (commSub ⊤ L) (Subgroup.zpowers τ) ⊔ (commSub ⊤ L ⊓ fixV L)) := by
  let U : Subgroup W := commSub ⊤ L
  let Z : Subgroup W := U ⊓ fixV L
  obtain ⟨hsl, hsum⟩ := hL3
  have hsum' := hsum
  obtain ⟨I, -, -, -, hnat⟩ := hsum
  have hL : IsPSL 3 2 1 ↥L :=
    s16h_e3_l3_isPSL_of_coord (BinaryNaturalSL.toL3Coord (hnat ⟨0, by norm_num⟩))
  have hperf : Group.IsPerfect ↥L := s16h_e3_l3_isPerfect_of_isPSL hL
  have hmem : ∀ l ∈ L, ∀ y ∈ (⊤ : Subgroup W), l y ∈ (⊤ : Subgroup W) :=
    fun l _ y _ => Subgroup.mem_top (l y)
  have hUinv : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U := s16jp_commSub_stable (L := L) (Y := ⊤) hmem
  have hUc : commSub U L = U := s16jp_commSub_commSub hperf (Y := ⊤) hmem
  have hrkU : rk ↥U = rk ↥Z + 9 := by
    have h := s16h_e3_l3_sum_rank L U Z 3 ⟨hsl, hsum'⟩
    omega
  have hZinv : ∀ l ∈ L, ∀ z ∈ Z, l z ∈ Z := by
    intro l hl z hz
    obtain ⟨-, hzfix⟩ := Subgroup.mem_inf.mp hz
    have hlz : l z = z := mem_fixV.mp hzfix l hl
    rwa [hlz]
  obtain ⟨hγ2, hc2, hcL⟩ := s16h_e3_l3_inner_decomp hL hτ2 hγL hinn
  let c : MulAut W := γ⁻¹ * τ
  have hc_def : c = γ⁻¹ * τ := rfl
  have hτγ : τ = γ * c := by
    rw [hc_def]
    group
  have hcU : ∀ u ∈ U, c u ∈ U := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨l, hl, w, -, rfl⟩ := hx
        have h1 : c (l w * w⁻¹) = l (c w) * (c w)⁻¹ := by
          rw [map_mul, map_inv]
          have hcl : c (l w) = l (c w) := by
            rw [hc_def]
            have h := congrArg (fun f : MulAut W => f w) (hcL l hl)
            simpa [MulAut.mul_apply] using h
          rw [hcl]
        rw [h1]
        exact Subgroup.subset_closure ⟨l, hl, c w, Subgroup.mem_top _, rfl⟩
    | one => simpa using (commSub ⊤ L).one_mem
    | mul a b _ _ iha ihb => simpa [map_mul] using (commSub ⊤ L).mul_mem iha ihb
    | inv a _ iha => simpa [map_inv] using (commSub ⊤ L).inv_mem iha
  obtain ⟨hM₀inv, hM₀comm, hM₀fix, -⟩ :=
    s16h_e3_l3_commSub_cent hW hUinv hUc hc2 hcL hcU
  let M₀ : Subgroup W := commSub U (Subgroup.zpowers c)
  let M : Subgroup W := M₀ ⊔ Z
  have hM₀map : M₀ = U.map (s16h_e3_l3_commHom c) :=
    s16h_e3_l3_commSub_zpowers_eq_map hc2 U
  have hM₀leU : M₀ ≤ U := by
    intro m hm
    rw [hM₀map] at hm
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hm
    exact U.mul_mem (hcU u hu) (U.inv_mem hu)
  have hZleU : Z ≤ U := inf_le_left
  have hMleU : M ≤ U := sup_le hM₀leU hZleU
  have hMinv : ∀ l ∈ L, ∀ m ∈ M, l m ∈ M := by
    intro l hl m hm
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hm
    rw [← hab, map_mul]
    exact Subgroup.mem_sup.mpr
      ⟨l a, hM₀inv l hl a ha, l b, hZinv l hl b hb, rfl⟩
  have hMinvγ : ∀ x ∈ Subgroup.zpowers γ, ∀ m ∈ M, x m ∈ M :=
    fun x hx => hMinv x (Subgroup.zpowers_le.mpr hγL hx)
  have hMcomm : commSub M L ⊔ Z = M := by
    apply le_antisymm
    · exact sup_le (commSub_le_of_invariant hMinv) le_sup_right
    · have hle : M₀ ≤ commSub M L := by
        have h := commSub_mono (le_sup_left : M₀ ≤ M₀ ⊔ Z) (le_rfl : L ≤ L)
        rwa [hM₀comm] at h
      calc M = M₀ ⊔ Z := rfl
        _ ≤ commSub M L ⊔ Z := sup_le (hle.trans le_sup_left) le_sup_right
  have hUsup : commSub U L ⊔ M = U := by
    rw [hUc, sup_eq_left]
    exact hMleU
  by_cases hγ1 : γ = 1
  · have hτc : τ = c := by rw [hτγ, hγ1, one_mul]
    have hcC : ∃ u ∈ U, c u ≠ u := by
      by_contra h
      apply hτC
      rw [mem_centSub]
      intro u hu
      have hcu : c u = u := by
        by_contra hne
        exact h ⟨u, hu, hne⟩
      rwa [hτc]
    obtain ⟨l, hl, m, hm, hfix⟩ :=
      s16h_e3_l3_commSub_cent_nontriv hW hUinv hUc hc2 hcL hcU hcC
    have hnt : ∃ l ∈ L, ∃ x ∈ M, l x * x⁻¹ ∉ Z :=
      ⟨l, hl, m, Subgroup.mem_sup_left hm, fun hz => hfix (Subgroup.mem_inf.mp hz).2⟩
    have h := s16h_e3_l3_rk_add_three_le hW hL hMinv hZinv le_sup_right hnt
    rw [hτc]
    exact h
  · have hC_le_A : commSub M (Subgroup.zpowers γ) ≤ commSub U (Subgroup.zpowers τ) := by
      rw [s16h_e3_l3_commSub_zpowers_eq_closure hγ2 M, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨m, hm, z, hz, hmz⟩ := Subgroup.mem_sup.mp hw
      rw [← hmz]
      have hγz : γ z = z := mem_fixV.mp (Subgroup.mem_inf.mp hz).2 γ hγL
      have hτm : τ m = γ m := by
        have hcm : c m = m := mem_fixV.mp (hM₀fix hm) c (Subgroup.mem_zpowers c)
        rw [hτγ, MulAut.mul_apply, hcm]
      have hkey : γ (m * z) * (m * z)⁻¹ = τ m * m⁻¹ := by
        rw [map_mul, hγz, mul_inv_rev, ← hτm]
        group
      rw [hkey]
      exact Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, m, hM₀leU hm, rfl⟩
    have hD_le_A :
        commSub U (Subgroup.zpowers γ) ≤ (commSub U (Subgroup.zpowers τ) ⊔ Z) ⊔ M := by
      rw [s16h_e3_l3_commSub_zpowers_eq_closure hγ2 U, Subgroup.closure_le]
      rintro _ ⟨u, hu, rfl⟩
      have hkey : γ u * u⁻¹ = (τ u * u⁻¹) * (γ (c u * u⁻¹))⁻¹ := by
        have hτu : τ u = γ (c u) := by rw [hτγ, MulAut.mul_apply]
        rw [hτu, map_mul, map_inv, mul_inv_rev, inv_inv]
        have h1 : (γ (c u) * u⁻¹) * (γ u * (γ (c u))⁻¹) =
            γ (c u) * (u⁻¹ * γ u) * (γ (c u))⁻¹ := by group
        rw [h1, mul_comm u⁻¹ (γ u), mul_comm (γ (c u)) (γ u * u⁻¹)]
        group
      rw [hkey]
      have h1 : τ u * u⁻¹ ∈ commSub U (Subgroup.zpowers τ) :=
        Subgroup.subset_closure ⟨τ, Subgroup.mem_zpowers τ, u, hu, rfl⟩
      have hcu : c u * u⁻¹ ∈ M₀ :=
        Subgroup.subset_closure ⟨c, Subgroup.mem_zpowers c, u, hu, rfl⟩
      have h2 : γ (c u * u⁻¹) ∈ M₀ := hM₀inv γ hγL _ hcu
      exact ((commSub U (Subgroup.zpowers τ) ⊔ Z) ⊔ M).mul_mem
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left h1))
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left (M₀.inv_mem h2)))
    have hbound1 :
        rk ↥M + 2 * rk ↥Z ≤ 3 * rk ↥(commSub M (Subgroup.zpowers γ) ⊔ Z) :=
      s16h_e3_l3_rk_le_three_mul_commSub hL hMinv hZinv hMcomm hγL hγ2 hγ1
    have hbound2 :
        rk ↥U + 2 * rk ↥M ≤ 3 * rk ↥(commSub U (Subgroup.zpowers γ) ⊔ M) :=
      s16h_e3_l3_rk_le_three_mul_commSub hL hUinv hMinv hUsup hγL hγ2 hγ1
    have hC_le_inf : commSub M (Subgroup.zpowers γ) ⊔ Z ≤
        (commSub U (Subgroup.zpowers τ) ⊔ Z) ⊓ M :=
      sup_le
        (le_inf (hC_le_A.trans le_sup_left) (commSub_le_of_invariant hMinvγ))
        (le_inf le_sup_right le_sup_right)
    have hD_le_sup : commSub U (Subgroup.zpowers γ) ⊔ M ≤
        (commSub U (Subgroup.zpowers τ) ⊔ Z) ⊔ M :=
      sup_le hD_le_A le_sup_right
    have hinf := rk_mono hC_le_inf
    have hsup := rk_mono hD_le_sup
    have hA := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers τ) ⊔ Z) M
    change rk ↥Z + 3 ≤ rk ↥(commSub U (Subgroup.zpowers τ) ⊔ Z)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
