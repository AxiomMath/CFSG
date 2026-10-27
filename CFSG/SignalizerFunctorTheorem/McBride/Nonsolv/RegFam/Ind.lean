module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515g.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G]

private theorem isDirectPair_symm {K L W : Subgroup G} (h : IsDirectPair K L W) :
    IsDirectPair L K W :=
  ⟨fun x hx y hy => (h.commute y hy x hx).symm, by rw [inf_comm]; exact h.inf_eq_bot,
    by rw [sup_comm]; exact h.sup_eq⟩

theorem le_normalizer_of_isDirectPair {K L W : Subgroup G} (h : IsDirectPair K L W) :
    W ≤ Subgroup.normalizer (K : Set G) := by
  rw [← h.sup_eq]
  refine sup_le Subgroup.le_normalizer fun y hy => ?_
  apply Subgroup.centralizer_le_normalizer (K : Set G)
  rw [Subgroup.mem_centralizer_iff]
  exact fun x hx => (h.commute x hx y hy).eq

private theorem ne_bot_of_not_isMulCommutative' {J : Subgroup G} (hnc : ¬ IsMulCommutative J) :
    J ≠ ⊥ := by
  rintro rfl
  exact hnc inferInstance

theorem isSubnormal_subgroupOf_of_normalizer {X Y : Subgroup G} (hXY : X ≤ Y)
    (hY : Y ≤ Subgroup.normalizer (X : Set G)) : (X.subgroupOf Y).IsSubnormal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr hY).isSubnormal

theorem sol_eq_bot_of_le_normalizer [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y)
    (hY : Y ≤ Subgroup.normalizer (X : Set G)) (hsol : sol Y = ⊥) : sol X = ⊥ :=
  le_bot_iff.mp (hsol ▸ T515g.sol_le_sol_of_le_normalizer hXY hY)

theorem exists_mem_lcal_of_sol_eq_bot [Finite G] {X : Subgroup G} (hX : X ≠ ⊥)
    (hsol : sol X = ⊥) : (lcal X).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h1 := (isDirectProduct_lcal_kOf hsol).sSup_eq
  rw [hne, sSup_empty] at h1
  exact hX ((kOf_eq_bot_iff X).mp h1.symm)

theorem eq_one_of_forall_commute_of_sol_eq_bot [Finite G] {H : Subgroup G} (hsol : sol H = ⊥)
    {z : G} (hzH : z ∈ H) (hz : ∀ y ∈ H, y * z = z * y) : z = 1 := by
  have h := centralizer_kOf_eq_bot hsol
  have hmem : z ∈ H ⊓ Subgroup.centralizer (kOf H : Set G) :=
    Subgroup.mem_inf.mpr ⟨hzH, Subgroup.mem_centralizer_iff.mpr fun y hy => hz y (kOf_le H hy)⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hmem

theorem exists_le_of_mem_lcal_of_isDirectProduct [Finite G] {Ω : Set (Subgroup G)}
    {H J : Subgroup G} (hΩ : IsDirectProduct Ω H) (hJ : J ∈ lcal H) : ∃ L ∈ Ω, J ≤ L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hJH, -, -, hnc⟩ := mem_lcal_iff.mp hJ
  have hcent : ∀ L ∈ Ω, J ≤ Subgroup.centralizer (L : Set G) := fun L hL =>
    (T515f.le_or_le_centralizer_of_mem_lcal hJ (hΩ.le hL)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hΩ.le hL)).mpr
        (hΩ.le_normalizer hL))).resolve_left (hcon L hL)
  have hHJ : ∀ b ∈ J, H ≤ Subgroup.centralizer ({b} : Set G) := by
    intro b hb
    rw [← hΩ.sSup_eq]
    refine sSup_le fun L hL x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hcent L hL hb) x hx
  refine hnc (isMulCommutative_iff.mpr fun a b => Subtype.ext ?_)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hHJ b b.2 (hJH a.2))

theorem isDirectPair_inf_of_le {L L' K H : Subgroup G} (h : IsDirectPair L L' H) (hLK : L ≤ K)
    (hKH : K ≤ H) : IsDirectPair L (K ⊓ L') K where
  commute x hx y hy := h.commute x hx y (Subgroup.mem_inf.mp hy).2
  inf_eq_bot := eq_bot_iff.mpr fun x hx =>
    h.inf_eq_bot ▸ Subgroup.mem_inf.mpr ⟨hx.1, (Subgroup.mem_inf.mp hx.2).2⟩
  sup_eq := by
    refine le_antisymm (sup_le hLK inf_le_left) fun k hk => ?_
    obtain ⟨l, hl, l', hl', rfl⟩ := (mem_sup_iff_of_commute h.commute).mp (h.sup_eq ▸ hKH hk)
    refine Subgroup.mul_mem_sup hl (Subgroup.mem_inf.mpr ⟨?_, hl'⟩)
    have := mul_mem (inv_mem (hLK hl)) hk
    simpa using this


theorem IsDirectProduct.ind_eq [Finite G] {Ω : Set (Subgroup G)} {H : Subgroup G}
    (hΩ : IsDirectProduct Ω H) (hsol : sol H = ⊥) (hne : ∀ L ∈ Ω, L ≠ ⊥)
    (hone : ∀ L ∈ Ω, Nat.card (lcal L) = 1) : Ind H = Ω := by
  have huniq : ∀ L ∈ Ω, ∀ J ∈ lcal L, ∀ J' ∈ lcal L, J = J' := fun L hL J hJ J' hJ' => by
    obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp (hone L hL)
    exact congrArg Subtype.val (Subsingleton.elim (⟨J, hJ⟩ : lcal L) ⟨J', hJ'⟩)
  have hsolL : ∀ L ∈ Ω, sol L = ⊥ := fun L hL =>
    sol_eq_bot_of_le_normalizer (hΩ.le hL) (hΩ.le_normalizer hL) hsol
  ext K
  constructor
  · rintro ⟨hK1, ⟨K', hKK'⟩, hKind⟩
    have hKH : K ≤ H := hKK'.sup_eq ▸ le_sup_left
    have hK'H : K' ≤ H := hKK'.sup_eq ▸ le_sup_right
    have hKn : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_isDirectPair hKK'
    have hK'n : H ≤ Subgroup.normalizer (K' : Set G) :=
      le_normalizer_of_isDirectPair (isDirectPair_symm hKK')
    have hsolK : sol K = ⊥ := sol_eq_bot_of_le_normalizer hKH hKn hsol
    obtain ⟨J, hJK⟩ := exists_mem_lcal_of_sol_eq_bot hK1 hsolK
    have hJH : J ∈ lcal H :=
      T515g.mem_lcal_of_isSubnormal hJK hKH (isSubnormal_subgroupOf_of_normalizer hKH hKn)
    obtain ⟨L, hL, hJL⟩ := exists_le_of_mem_lcal_of_isDirectProduct hΩ hJH
    have hJLc : J ∈ lcal L := L511.mem_lcal_of_le hJH hJL (hΩ.le hL)
    have hLH : L ≤ H := hΩ.le hL
    have hLn : H ≤ Subgroup.normalizer (L : Set G) := hΩ.le_normalizer hL
    have hLK' : L ⊓ K' = ⊥ := by
      by_contra hne'
      have hLN : L ≤ Subgroup.normalizer ((L ⊓ K' : Subgroup G) : Set G) :=
        le_trans (le_inf Subgroup.le_normalizer (hLH.trans hK'n))
          Subgroup.inf_normalizer_le_normalizer_inf
      have hsolN : sol (L ⊓ K') = ⊥ :=
        sol_eq_bot_of_le_normalizer inf_le_left hLN (hsolL L hL)
      obtain ⟨J', hJ'⟩ := exists_mem_lcal_of_sol_eq_bot hne' hsolN
      have hJ'L : J' ∈ lcal L :=
        T515g.mem_lcal_of_isSubnormal hJ' inf_le_left
          (isSubnormal_subgroupOf_of_normalizer inf_le_left hLN)
      have hJJ' := huniq L hL J hJLc J' hJ'L
      have hJK' : J ≤ K' := hJJ' ▸ (lcal_le hJ').trans inf_le_right
      obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJK
      have : J ≤ K ⊓ K' := le_inf (lcal_le hJK) hJK'
      rw [hKK'.inf_eq_bot] at this
      exact ne_bot_of_not_isMulCommutative' hnc (le_bot_iff.mp this)
    have hLc : ∀ l ∈ L, ∀ x ∈ K', l * x = x * l := by
      intro l hl x hx
      have h1 : l * x * l⁻¹ * x⁻¹ ∈ L ⊓ K' := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h2 : x * l⁻¹ * x⁻¹ ∈ L :=
            (Subgroup.mem_normalizer_iff.mp (hLn (hK'H hx)) l⁻¹).mp (inv_mem hl)
          simpa [mul_assoc] using mul_mem hl h2
        · have h2 : l * x * l⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp (hK'n (hLH hl)) x).mp hx
          exact mul_mem h2 (inv_mem hx)
      rw [hLK', Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hLK : L ≤ K := by
      intro l hl
      obtain ⟨k, hk, k', hk', hkk'l⟩ := exists_mul_of_isDirectPair hKK' (hLH hl)
      have hk'eq : k' = k⁻¹ * l := by rw [← hkk'l]; group
      have hcK' : ∀ x ∈ K', x * k' = k' * x := by
        intro x hx
        rw [hk'eq]
        calc x * (k⁻¹ * l) = (x * k⁻¹) * l := by group
          _ = (k⁻¹ * x) * l := by rw [← (hKK'.commute k⁻¹ (inv_mem hk) x hx).eq]
          _ = k⁻¹ * (x * l) := by group
          _ = k⁻¹ * (l * x) := by rw [(hLc l hl x hx).symm]
          _ = k⁻¹ * l * x := by group
      have hz : k' = 1 := by
        refine eq_one_of_forall_commute_of_sol_eq_bot hsol (hK'H hk') fun y hy => ?_
        obtain ⟨k₁, hk₁, k₁', hk₁', rfl⟩ := exists_mul_of_isDirectPair hKK' hy
        calc k₁ * k₁' * k' = k₁ * (k₁' * k') := by group
          _ = k₁ * (k' * k₁') := by rw [hcK' k₁' hk₁']
          _ = (k₁ * k') * k₁' := by group
          _ = (k' * k₁) * k₁' := by rw [(hKK'.commute k₁ hk₁ k' hk').eq]
          _ = k' * (k₁ * k₁') := by group
      rw [hz, mul_one] at hkk'l
      rw [← hkk'l]
      exact hk
    have hpair : IsDirectPair L (K ⊓ sSup (Ω \ {L})) K :=
      isDirectPair_inf_of_le (hΩ.isDirectPair hL) hLK hKH
    rcases hKind L ⟨_, hpair⟩ with h | h
    · exact absurd h (hne L hL)
    · exact h ▸ hL
  · intro hKΩ
    refine ⟨hne K hKΩ, ⟨_, hΩ.isDirectPair hKΩ⟩, ?_⟩
    rintro X ⟨Y, hXY⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hX1, hXK⟩ := hcon
    have hXKle : X ≤ K := hXY.sup_eq ▸ le_sup_left
    have hYKle : Y ≤ K := hXY.sup_eq ▸ le_sup_right
    have hY1 : Y ≠ ⊥ := by
      rintro rfl
      apply hXK
      rw [← hXY.sup_eq, sup_bot_eq]
    have hXn : K ≤ Subgroup.normalizer (X : Set G) := le_normalizer_of_isDirectPair hXY
    have hYn : K ≤ Subgroup.normalizer (Y : Set G) :=
      le_normalizer_of_isDirectPair (isDirectPair_symm hXY)
    have hsolX : sol X = ⊥ := sol_eq_bot_of_le_normalizer hXKle hXn (hsolL K hKΩ)
    have hsolY : sol Y = ⊥ := sol_eq_bot_of_le_normalizer hYKle hYn (hsolL K hKΩ)
    obtain ⟨JX, hJX⟩ := exists_mem_lcal_of_sol_eq_bot hX1 hsolX
    obtain ⟨JY, hJY⟩ := exists_mem_lcal_of_sol_eq_bot hY1 hsolY
    have hJXK : JX ∈ lcal K :=
      T515g.mem_lcal_of_isSubnormal hJX hXKle (isSubnormal_subgroupOf_of_normalizer hXKle hXn)
    have hJYK : JY ∈ lcal K :=
      T515g.mem_lcal_of_isSubnormal hJY hYKle (isSubnormal_subgroupOf_of_normalizer hYKle hYn)
    have hJ := huniq K hKΩ JX hJXK JY hJYK
    have hle : JX ≤ X ⊓ Y := le_inf (lcal_le hJX) (hJ ▸ lcal_le hJY)
    rw [hXY.inf_eq_bot] at hle
    obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hJX
    exact ne_bot_of_not_isMulCommutative' hnc (le_bot_iff.mp hle)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
