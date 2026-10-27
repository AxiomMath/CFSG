module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperUnique
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

variable {G : Type} [Group G]

private theorem diagAut_inv_apply {n p : ℕ} {d : Fin n → ZMod p} (hd : ∀ i, d i * d i = 1)
    (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    (diagAut d hd)⁻¹ f i = ofAdd (d i * toAdd (f i)) :=
  rfl

private theorem axis_of_bCoordinateBlock [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta) {i0 : Fin n}
    (hLb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ∀ k, k ≠ i0 → eta ⟨x, hF.fixLineComp.mem⟩ k = 1 := by
  let xb : ↥Bs := ⟨x, hF.fixLineComp.mem⟩
  have hfix : ∀ φ ∈ ggAutomizer L Bs, φ xb = xb :=
    (hF.fixLineComp.fix_iff xb).mpr (Subgroup.mem_zpowers x)
  have h1 : ∀ u ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom, u (eta xb) = eta xb :=
    (forall_map_congr_fix_iff eta (ggAutomizer L Bs) xb).mpr hfix
  rw [hLb] at h1
  exact (forall_bCoordinateBlock_fix_iff hF.prime hF.ne_two i0 (eta xb)).mp h1

private theorem axis_of_dCoordinateBlock [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta) {i0 : Fin n}
    (hLd : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p i0) :
    ∀ k, k ≠ i0 → eta ⟨x, hF.fixLineComp.mem⟩ k = 1 := by
  let xb : ↥Bs := ⟨x, hF.fixLineComp.mem⟩
  have hfix : ∀ φ ∈ ggAutomizer L Bs, φ xb = xb :=
    (hF.fixLineComp.fix_iff xb).mpr (Subgroup.mem_zpowers x)
  have h1 : ∀ u ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom, u (eta xb) = eta xb :=
    (forall_map_congr_fix_iff eta (ggAutomizer L Bs) xb).mpr hfix
  have hn : 3 ≤ n := by
    have h5 := hF.five_le
    omega
  rw [hLd] at h1
  exact (forall_dCoordinateBlock_fix_iff hF.prime hF.ne_two hn i0 (eta xb)).mp h1

private theorem nonempty_of_map_eq_bCoordinateBlock {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta) {i0 : Fin n}
    (hLb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    𝒦.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h𝒦
  have hjoin : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bSignedFull n p := by
    rw [← hF.join]
    simp [ggAutomizerJoin, h𝒦]
  refine sgnAut_not_mem_bCoordinateBlock hF.prime hF.ne_two i0 ?_
  rw [← hLb, hjoin]
  exact Subgroup.subset_closure (Or.inl ⟨i0, rfl⟩)

private theorem mem_of_not_forall_fix_of_axis {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta) {xb : ↥Bs} {i0 : Fin n}
    (hxh : ∀ k, k ≠ i0 → eta xb k = 1)
    {I : Finset (Fin n)} {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hblock : IsSignedBlockOn n p I Γ) (hnotfix : ¬ ∀ u ∈ Γ, u (eta xb) = eta xb) :
    i0 ∈ I := by
  by_contra hi0
  apply hnotfix
  rcases hblock with hΓ | ⟨hI2, hΓ⟩ | ⟨d, hd, hΓ⟩
  · rw [hΓ]
    exact (forall_bBlockOn_fix_iff hF.prime hF.ne_two I (eta xb)).mpr
      (fun i hi => hxh i (fun h => hi0 (h ▸ hi)))
  · rw [hΓ]
    exact (forall_dBlockOn_fix_iff hF.prime hF.ne_two hI2 (eta xb)).mpr
      (fun i hi => hxh i (fun h => hi0 (h ▸ hi)))
  · rw [hΓ]
    refine (forall_map_conj_fix_iff (aPermutationOn n p I) (diagAut d hd) (eta xb)).mpr ?_
    refine (forall_aPermutationOn_fix_iff I ((diagAut d hd)⁻¹ (eta xb))).mpr ?_
    intro i hi j hj
    have hi' : i ≠ i0 := fun h => hi0 (h ▸ hi)
    have hj' : j ≠ i0 := fun h => hi0 (h ▸ hj)
    rw [diagAut_inv_apply, diagAut_inv_apply, hxh i hi', hxh j hj']
    simp

private theorem mem_zpowers_or_of_axis_of_frame {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta) {i0 : Fin n}
    {y : G} {K : Subgroup G} (hyK : Nb y K) {y₀ : G} {K₀ : Subgroup G} (hy₀K₀ : Nb y₀ K₀)
    {xb yb y₀b : ↥Bs} (hxb : (xb : G) = x) (hyb : (yb : G) = y) (hy₀b : (y₀b : G) = y₀)
    (hxh : ∀ k, k ≠ i0 → eta xb k = 1)
    (h : SignedNbrDatum n p (eta xb) (eta yb)
      ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom))
    (h₀ : SignedNbrDatum n p (eta xb) (eta y₀b)
      ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom)) :
    eta yb ∈ Subgroup.zpowers (eta y₀b) ∨
      eta yb ∈ Subgroup.zpowers (sgnAut i0 (eta y₀b)) := by
  refine SignedNbrDatum.mem_zpowers_or_of_axis hF.prime hF.ne_two hF.five_le hxh h₀ h ?_ ?_
  · refine mem_closure_pair_map eta ?_
    rw [hxb, hyb, hy₀b]
    exact hF.plane y K y₀ K₀ hyK hy₀K₀
  · refine not_mem_zpowers_map eta ?_
    rw [hxb, hyb]
    exact hF.not_mem y K hyK

private theorem le_join_of_eq_anchor [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta) {y : G} {K : Subgroup G} (hyK : Nb y K)
    {y₀ : G} {K₀ : Subgroup G} (hy₀K₀ : Nb y₀ K₀) (hK₀ : K₀ ∈ 𝒦)
    {yb y₀b : ↥Bs} (hyb : (yb : G) = y) (hy₀b : (y₀b : G) = y₀)
    {I : Finset (Fin n)} (hI : n ≤ I.card + 2)
    (hswaps : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      HasSignedSwap ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) a b)
    (hyv : eta yb ∈ Subgroup.zpowers (eta y₀b)) : K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have hQ : IsComponentOf K₀ (Subgroup.centralizer ({(y₀b : G)} : Set G)) := by
    rw [hy₀b]
    exact hF.isComponentOf y₀ K₀ hy₀K₀
  have hKeq : K = K₀ :=
    hF.eq_of_isComponentOf (Q := K₀) (yb := yb) (vb := y₀b) hyK hyb hQ hyv hI hswaps
  rw [hKeq]
  exact le_sup_of_le_right (le_iSup₂_of_le K₀ hK₀ le_rfl)

private theorem exists_lift_mem_sup {p n : ℕ} {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {K₀ : Subgroup G}
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ⊔
      (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) :
    ∃ g ∈ L ⊔ K₀, ∃ hg : g ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hg) = u := by
  have hu' : u ∈ (ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs).map
      (MulAut.congr eta).toMonoidHom := by
    rwa [Subgroup.map_sup]
  exact exists_ggConjAut_eq_of_mem_map_sup eta hu'

private theorem map_conj_le_join {L K₀ : Subgroup G} {𝒦 : Finset (Subgroup G)} (hK₀ : K₀ ∈ 𝒦)
    {g : G} (hg : g ∈ L ⊔ K₀) :
    K₀.map (MulAut.conj g).toMonoidHom ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have hK₀J : K₀ ≤ L ⊔ ⨆ K' ∈ 𝒦, K' :=
    le_sup_of_le_right (le_iSup₂_of_le K₀ hK₀ le_rfl)
  have hgJ : g ∈ L ⊔ ⨆ K' ∈ 𝒦, K' := sup_le le_sup_left hK₀J hg
  exact le_trans (map_conj_le_sup hgJ) (sup_le le_rfl hK₀J)

theorem GGBProperFrame.le_join_of_bCoordinateBlock [Finite G] {p n : ℕ} {B Bs L : Subgroup G}
    {x : G} {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    {i0 : Fin n}
    (hLb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {y : G} {K : Subgroup G} (hyK : Nb y K) : K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  obtain ⟨K₀, hK₀⟩ := nonempty_of_map_eq_bCoordinateBlock hF hLb
  obtain ⟨y₀, hy₀K₀⟩ := hF.exists_nb K₀ hK₀
  let xb : ↥Bs := ⟨x, hF.fixLineComp.mem⟩
  let y₀b : ↥Bs := ⟨y₀, hF.le (hF.mem y₀ K₀ hy₀K₀)⟩
  have hxh : ∀ k, k ≠ i0 → eta xb k = 1 := axis_of_bCoordinateBlock hF hLb
  have h₀ : SignedNbrDatum n p (eta xb) (eta y₀b)
      ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) :=
    hF.datum y₀ K₀ hy₀K₀ xb y₀b rfl rfl
  obtain ⟨I, hblock⟩ := h₀.isSignedBlockOn
  have hi0 : i0 ∈ I := mem_of_not_forall_fix_of_axis hF hxh hblock h₀.not_fix
  have hcard : n ≤ I.card + 2 :=
    IsSignedBlockOn.le_card_add_two hF.prime hF.ne_two hblock h₀.card_fix_le
  have hswaps : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      HasSignedSwap ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) a b :=
    fun a ha b hb hab => IsSignedBlockOn.hasSignedSwap hF.prime hblock ha hb hab
  have hI3 : 3 ≤ I.card := by
    have h5 := hF.five_le
    omega
  obtain ⟨k, hkI, hki⟩ := Finset.exists_mem_ne (show 1 < I.card by omega) i0
  have hswap := hswaps i0 hi0 k hkI (Ne.symm hki)
  have hsgn : sgnAut i0 ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ⊔
      (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom := by
    have h := sgnAut_mem_bCoordinateBlock_sup_of_hasSignedSwap hki hswap
    rwa [← hLb] at h
  obtain ⟨g, hgLK, hgN, hgc⟩ := exists_lift_mem_sup hsgn
  let yb : ↥Bs := ⟨y, hF.le (hF.mem y K hyK)⟩
  have h : SignedNbrDatum n p (eta xb) (eta yb)
      ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) :=
    hF.datum y K hyK xb yb rfl rfl
  have hw := mem_zpowers_or_of_axis_of_frame hF hyK hy₀K₀ rfl rfl rfl hxh h h₀
  rcases hw with hw | hw
  · exact le_join_of_eq_anchor hF hyK hy₀K₀ hK₀ rfl rfl hcard hswaps hw
  · have hQ : IsComponentOf K₀ (Subgroup.centralizer ({(y₀b : G)} : Set G)) := by
      simpa using hF.isComponentOf y₀ K₀ hy₀K₀
    have hKeq : K = K₀.map (MulAut.conj g).toMonoidHom :=
      hF.eq_map_conj_of_mem_zpowers (Q := K₀) (yb := yb) (vb := y₀b) hyK rfl hQ hcard hswaps
        hgN (by rw [hgc]; exact Subgroup.subset_closure ⟨i0, rfl⟩) (by rw [hgc]; exact hw)
    rw [hKeq]
    exact map_conj_le_join hK₀ hgLK

theorem GGBProperFrame.le_join_of_dCoordinateBlock [Finite G] {p n : ℕ} {B Bs L : Subgroup G}
    {x : G} {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    {i0 : Fin n}
    (hLd : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = dCoordinateBlock n p i0)
    {y : G} {K : Subgroup G} (hyK : Nb y K) : K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have hxh : ∀ k, k ≠ i0 → eta ⟨x, hF.fixLineComp.mem⟩ k = 1 :=
    axis_of_dCoordinateBlock hF hLd
  have hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
    rw [hLd]
    exact dCoordinateBlock_le_coordProdStab i0
  obtain ⟨K₀, hK₀, I, -, hΓ₀⟩ := hF.exists_mem_bBlockOn hL
  obtain ⟨y₀, hy₀K₀⟩ := hF.exists_nb K₀ hK₀
  let xb : ↥Bs := ⟨x, hF.fixLineComp.mem⟩
  let y₀b : ↥Bs := ⟨y₀, hF.le (hF.mem y₀ K₀ hy₀K₀)⟩
  have h₀ := hF.datum y₀ K₀ hy₀K₀ xb y₀b rfl rfl
  have h₀' := h₀
  rw [hΓ₀] at h₀
  have hsgn : sgnAut i0 (eta y₀b) = eta y₀b :=
    SignedNbrDatum.sgnAut_axis_eq_of_bBlockOn hF.prime hF.ne_two hxh h₀
  let yb : ↥Bs := ⟨y, hF.le (hF.mem y K hyK)⟩
  have h : SignedNbrDatum n p (eta xb) (eta yb)
      ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) :=
    hF.datum y K hyK xb yb rfl rfl
  have hw := mem_zpowers_or_of_axis_of_frame hF hyK hy₀K₀ rfl rfl rfl hxh h h₀'
  have hw' : eta yb ∈ Subgroup.zpowers (eta y₀b) := by
    rcases hw with hw | hw
    · exact hw
    · rwa [hsgn] at hw
  have hblock : IsSignedBlockOn n p I (bBlockOn n p I) := Or.inl rfl
  have hcard : n ≤ I.card + 2 :=
    IsSignedBlockOn.le_card_add_two hF.prime hF.ne_two hblock h₀.card_fix_le
  have hswaps : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      HasSignedSwap ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) a b := by
    intro a ha b hb hab
    have h := IsSignedBlockOn.hasSignedSwap hF.prime hblock ha hb hab
    rwa [← hΓ₀] at h
  exact le_join_of_eq_anchor hF hyK hy₀K₀ hK₀ rfl rfl hcard hswaps hw'

end CFSG.StandardType

end
