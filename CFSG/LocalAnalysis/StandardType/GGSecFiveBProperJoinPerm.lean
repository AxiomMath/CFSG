module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperUnique
import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord

variable {G : Type} [Group G]

private theorem le_join_of_mem {L K : Subgroup G} {𝒦 : Finset (Subgroup G)} (hK : K ∈ 𝒦) :
    K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' :=
  le_sup_of_le_right (le_iSup₂_of_le K hK le_rfl)

private theorem le_join_of_conj {L K₀ : Subgroup G} {𝒦 : Finset (Subgroup G)} (hK₀ : K₀ ∈ 𝒦)
    {g : G} (hg : g ∈ L ⊔ K₀) :
    L.map (MulAut.conj g).toMonoidHom ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  refine le_trans (map_conj_le_sup (W := L ⊔ K₀) (X := L) hg) (sup_le ?_ le_sup_left)
  exact sup_le le_sup_left (le_sup_of_le_right (le_iSup₂_of_le K₀ hK₀ le_rfl))

private theorem forall_coord_eq_of_map_eq_aPermutation {p n : ℕ} {Bs L : Subgroup G} {x : G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} (h : GGFixLineComp Bs x L)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    ∀ a b, eta ⟨x, h.mem⟩ a = eta ⟨x, h.mem⟩ b := by
  have hfix : ∀ w ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom,
      w (eta ⟨x, h.mem⟩) = eta ⟨x, h.mem⟩ :=
    (h.forall_map_congr_fix_iff eta (eta ⟨x, h.mem⟩)).mpr (by
      rw [MulEquiv.symm_apply_apply]
      exact Subgroup.mem_zpowers x)
  rw [hL] at hfix
  exact (forall_aPermutationFull_fix_iff (eta ⟨x, h.mem⟩)).mp hfix

private theorem hline_of_anchor [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta) {K₀ : Subgroup G} {y₀b : ↥Bs}
    (hy₀K₀ : Nb (y₀b : G) K₀) {I : Finset (Fin n)}
    (hΓeq : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I)
    {i j : Fin n} (hroot : ∀ b : ↥Bs, (b : G) ∈ B ↔ eta b i = eta b j) :
    ∀ f : Fin n → Multiplicative (ZMod p), (∀ k ∈ I, f k = 1) → f i = f j →
      f ∈ Subgroup.zpowers (eta y₀b) := by
  intro f hfvan hfij
  let b : ↥Bs := eta.symm f
  have hbB : (b : G) ∈ B := (hroot b).mpr (by simpa [b] using hfij)
  have hbfix : ∀ φ ∈ ggAutomizer K₀ Bs, φ b = b := by
    rw [← forall_map_congr_fix_iff eta (ggAutomizer K₀ Bs) b]
    rw [show eta b = f from by simp [b], hΓeq]
    exact (forall_bBlockOn_fix_iff hF.prime hF.ne_two I f).mpr hfvan
  have hbzp : (b : G) ∈ Subgroup.zpowers (y₀b : G) :=
    hF.mem_zpowers (y₀b : G) K₀ hy₀K₀ b hbB hbfix
  rw [Subgroup.mem_zpowers_iff] at hbzp ⊢
  obtain ⟨k, hk⟩ := hbzp
  refine ⟨k, ?_⟩
  have hbk : y₀b ^ k = b := Subtype.ext (by simpa using hk)
  calc (eta y₀b) ^ k = eta (y₀b ^ k) := (map_zpow eta y₀b k).symm
    _ = eta b := by rw [hbk]
    _ = f := by simp [b]

private theorem exists_anchor [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    (hLa : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    ∃ (K₀ : Subgroup G) (_ : K₀ ∈ 𝒦) (I : Finset (Fin n)) (y₀b : ↥Bs),
      I.Nonempty ∧ Nb (y₀b : G) K₀ ∧ n ≤ I.card + 2 ∧
      (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I ∧
      (∀ k ∈ I, eta y₀b k = 1) := by
  have hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
    rw [hLa]
    exact aPermutationFull_le_coordProdStab
  obtain ⟨K₀, hK₀, I, hI, hΓeq⟩ := hF.exists_mem_bBlockOn hL
  obtain ⟨y₀, hy₀K₀⟩ := hF.exists_nb K₀ hK₀
  let y₀b : ↥Bs := ⟨y₀, hF.le (hF.mem y₀ K₀ hy₀K₀)⟩
  let xb : ↥Bs := ⟨x, hF.fixLineComp.mem⟩
  have h₀dat : SignedNbrDatum n p (eta xb) (eta y₀b)
      ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) :=
    hF.datum y₀ K₀ hy₀K₀ xb y₀b rfl rfl
  have hIsb : IsSignedBlockOn n p I
      ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) := Or.inl hΓeq
  have hIle : n ≤ I.card + 2 :=
    IsSignedBlockOn.le_card_add_two hF.prime hF.ne_two hIsb h₀dat.card_fix_le
  have hw₀ : ∀ k ∈ I, eta y₀b k = 1 :=
    (forall_bBlockOn_fix_iff hF.prime hF.ne_two I (eta y₀b)).mp
      (by simpa only [hΓeq] using h₀dat.fix)
  exact ⟨K₀, hK₀, I, y₀b, hI, hy₀K₀, hIle, hΓeq, hw₀⟩

private theorem le_join_of_mem_zpowers_anchor [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦)
    {I : Finset (Fin n)} (hIle : n ≤ I.card + 2)
    (hsw₀ : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      HasSignedSwap ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) a b)
    {yb y₀b : ↥Bs} {y : G} {K : Subgroup G} (hyK : Nb y K) (hyb : (yb : G) = y)
    (hQ : IsComponentOf K₀ (Subgroup.centralizer ({(y₀b : G)} : Set G)))
    (hz : eta yb ∈ Subgroup.zpowers (eta y₀b)) :
    K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have hKeq : K = K₀ :=
    hF.eq_of_isComponentOf hyK (Q := K₀) (yb := yb) (vb := y₀b) hyb hQ hz hIle hsw₀
  exact hKeq.symm ▸ le_join_of_mem hK₀

private theorem le_join_of_mem_zpowers_sgn [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    (hLa : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) {I : Finset (Fin n)}
    (hΓeq : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I)
    {xb yb : ↥Bs} (hxb : (xb : G) = x) {y : G} {K : Subgroup G} (hyK : Nb y K)
    (hyb : (yb : G) = y) {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u ∈ aPermutationFull n p ⊔ bBlockOn n p I)
    (hgs : u ∈ Subgroup.closure
      (Set.range fun k : Fin n => (sgnAut k : MulAut (Fin n → Multiplicative (ZMod p)))))
    (hz : eta yb ∈ Subgroup.zpowers (u (eta xb))) :
    K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  have hu' : u ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ⊔
      (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hLa, hΓeq]
    exact hu
  have hu2 : u ∈ (ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs).map
      (MulAut.congr eta).toMonoidHom := by
    rw [Subgroup.map_sup]
    exact hu'
  obtain ⟨g, hgLK, hg, hgc⟩ := exists_ggConjAut_eq_of_mem_map_sup eta hu2
  have hQ : IsComponentOf L (Subgroup.centralizer ({(xb : G)} : Set G)) := by
    simpa only [hxb] using hF.fixLineComp.isComponentOf
  have hswL : ∀ a ∈ (Finset.univ : Finset (Fin n)), ∀ b ∈ Finset.univ, a ≠ b →
      HasSignedSwap ((ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom) a b := by
    intro a _ b _ hab
    rw [hLa]
    exact Or.inl (Subgroup.subset_closure ⟨a, b, hab, rfl⟩)
  have hgs' : MulAut.congr eta (ggConjAut Bs hg) ∈ Subgroup.closure
      (Set.range fun k : Fin n => (sgnAut k : MulAut (Fin n → Multiplicative (ZMod p)))) := by
    rw [hgc]
    exact hgs
  have hz' : eta yb ∈ Subgroup.zpowers (MulAut.congr eta (ggConjAut Bs hg) (eta xb)) := by
    rw [hgc]
    exact hz
  have hKeq : K = L.map (MulAut.conj g).toMonoidHom :=
    hF.eq_map_conj_of_mem_zpowers hyK (Q := L) (yb := yb) (vb := xb) hyb hQ
      (I' := Finset.univ) (by simp) hswL hg hgs' hz'
  exact hKeq.symm ▸ le_join_of_conj hK₀ hgLK

private theorem le_join_of_anchor_axis [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    (hLa : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) {y₀b : ↥Bs} (hy₀K₀ : Nb (y₀b : G) K₀)
    {I : Finset (Fin n)} (hI : I.Nonempty)
    (hΓeq : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I)
    (hIle : n ≤ I.card + 2)
    (hsw₀ : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      HasSignedSwap ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) a b)
    {xb yb : ↥Bs} (hxb : (xb : G) = x) {y : G} {K : Subgroup G} (hyK : Nb y K)
    (hyb : (yb : G) = y) {m : Fin n} (hxa : ∀ a b, eta xb a = eta xb b)
    (hw₀m : ∀ k, k ≠ m → eta y₀b k = 1)
    (hpl : eta yb ∈ Subgroup.closure {eta xb, eta y₀b})
    (hwx : eta yb ∉ Subgroup.zpowers (eta xb))
    (hdat : SignedNbrDatum n p (eta xb) (eta yb)
      ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom)) :
    K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  rcases SignedNbrDatum.mem_zpowers_or_of_const_axis hF.prime hF.ne_two hF.five_le hxa hw₀m
    hdat hpl hwx with hz | hz
  · exact le_join_of_mem_zpowers_anchor hF hK₀ hIle hsw₀ hyK hyb
      (hF.isComponentOf (y₀b : G) K₀ hy₀K₀) hz
  · obtain ⟨k, hkI⟩ := hI
    have hgen : sgnAut k ∈ bBlockOn n p I := Subgroup.subset_closure (Or.inl ⟨k, hkI, rfl⟩)
    have hu : sgnAut m ∈ aPermutationFull n p ⊔ bBlockOn n p I :=
      sgnAut_mem_aPermutationFull_sup (Γ := bBlockOn n p I) hgen m
    have hgs : sgnAut m ∈ Subgroup.closure
        (Set.range fun k : Fin n => (sgnAut k : MulAut (Fin n → Multiplicative (ZMod p)))) :=
      Subgroup.subset_closure ⟨m, rfl⟩
    exact le_join_of_mem_zpowers_sgn hF hLa hK₀ hΓeq hxb hyK hyb hu hgs hz

private theorem le_join_of_anchor_pair [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    (hLa : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦) {y₀b : ↥Bs} (hy₀K₀ : Nb (y₀b : G) K₀)
    {I : Finset (Fin n)} (hI : I.Nonempty)
    (hΓeq : (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I)
    (hIle : n ≤ I.card + 2)
    (hsw₀ : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      HasSignedSwap ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) a b)
    {xb yb : ↥Bs} (hxb : (xb : G) = x) {y : G} {K : Subgroup G} (hyK : Nb y K)
    (hyb : (yb : G) = y) {i j : Fin n} (hij : i ≠ j)
    (hxa : ∀ a b, eta xb a = eta xb b) (hw₀ij : eta y₀b i = eta y₀b j)
    (hw₀ : ∀ k, k ≠ i → k ≠ j → eta y₀b k = 1)
    (hpl : eta yb ∈ Subgroup.closure {eta xb, eta y₀b})
    (hwx : eta yb ∉ Subgroup.zpowers (eta xb))
    (hdat : SignedNbrDatum n p (eta xb) (eta yb)
      ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom)) :
    K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  rcases SignedNbrDatum.mem_zpowers_or_of_const_pair hF.prime hF.ne_two hF.five_le hxa hij
    hw₀ij hw₀ hdat hpl hwx with hz | hz
  · exact le_join_of_mem_zpowers_anchor hF hK₀ hIle hsw₀ hyK hyb
      (hF.isComponentOf (y₀b : G) K₀ hy₀K₀) hz
  · obtain ⟨k, hkI⟩ := hI
    have hgen : sgnAut k ∈ bBlockOn n p I := Subgroup.subset_closure (Or.inl ⟨k, hkI, rfl⟩)
    have hi : sgnAut i ∈ aPermutationFull n p ⊔ bBlockOn n p I :=
      sgnAut_mem_aPermutationFull_sup (Γ := bBlockOn n p I) hgen i
    have hj : sgnAut j ∈ aPermutationFull n p ⊔ bBlockOn n p I :=
      sgnAut_mem_aPermutationFull_sup (Γ := bBlockOn n p I) hgen j
    have hu : sgnAut i * sgnAut j ∈ aPermutationFull n p ⊔ bBlockOn n p I :=
      Subgroup.mul_mem _ hi hj
    have hgs : sgnAut i * sgnAut j ∈ Subgroup.closure
        (Set.range fun k : Fin n => (sgnAut k : MulAut (Fin n → Multiplicative (ZMod p)))) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)
        (Subgroup.subset_closure ⟨j, rfl⟩)
    exact le_join_of_mem_zpowers_sgn hF hLa hK₀ hΓeq hxb hyK hyb hu hgs
      (by simpa only [MulAut.mul_apply] using hz)

theorem GGBProperFrame.le_join_of_aPermutationFull [Finite G] {p n : ℕ} {B Bs L : Subgroup G}
    {x : G} {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    (hLa : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {i j : Fin n} (hij : i ≠ j) (hroot : ∀ b : ↥Bs, (b : G) ∈ B ↔ eta b i = eta b j)
    {y : G} {K : Subgroup G} (hyK : Nb y K) : K ≤ L ⊔ ⨆ K' ∈ 𝒦, K' := by
  let xb : ↥Bs := ⟨x, hF.fixLineComp.mem⟩
  let yb : ↥Bs := ⟨y, hF.le (hF.mem y K hyK)⟩
  have hxa : ∀ a b, eta xb a = eta xb b :=
    forall_coord_eq_of_map_eq_aPermutation hF.fixLineComp hLa
  obtain ⟨K₀, hK₀, I, y₀b, hI, hy₀K₀, hIle, hΓeq, hw₀⟩ := exists_anchor hF hLa
  have hline := hline_of_anchor hF hy₀K₀ hΓeq hroot
  have hsw₀ : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      HasSignedSwap ((ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom) a b :=
    fun a ha b hb hab => IsSignedBlockOn.hasSignedSwap hF.prime (Or.inl hΓeq) ha hb hab
  have hdat : SignedNbrDatum n p (eta xb) (eta yb)
      ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) :=
    hF.datum y K hyK xb yb rfl rfl
  have hpl : eta yb ∈ Subgroup.closure {eta xb, eta y₀b} :=
    mem_closure_pair_map eta (x := xb) (y := yb) (y₀ := y₀b)
      (hF.plane y K (y₀b : G) K₀ hyK hy₀K₀)
  have hwx : eta yb ∉ Subgroup.zpowers (eta xb) :=
    not_mem_zpowers_map eta (x := xb) (y := yb) (hF.not_mem y K hyK)
  rcases profile_of_forall_mem_zpowers hF.prime hw₀ hline with ⟨m, -, -, hw₀m⟩ | hw₀ij
  · exact le_join_of_anchor_axis hF hLa hK₀ hy₀K₀ hI hΓeq hIle hsw₀ rfl hyK rfl hxa hw₀m
      hpl hwx hdat
  · have hw₀ij' : eta y₀b i = eta y₀b j :=
      (hroot y₀b).mp (hF.mem (y₀b : G) K₀ hy₀K₀)
    exact le_join_of_anchor_pair hF hLa hK₀ hy₀K₀ hI hΓeq hIle hsw₀ rfl hyK rfl hij hxa
      hw₀ij' hw₀ij hpl hwx hdat

end CFSG.StandardType

end
