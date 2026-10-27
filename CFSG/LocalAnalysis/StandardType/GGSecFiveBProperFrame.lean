module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordProperLines
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordSwaps
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperUnique
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord

variable {G : Type} [Group G]

structure GGBProperFrame (p n : ℕ) (B Bs L : Subgroup G) (x : G) (𝒦 : Finset (Subgroup G))
    (Nb : G → Subgroup G → Prop) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  five_le : 5 ≤ n
  le : B ≤ Bs
  pow_eq_one : ∀ b ∈ Bs, b ^ p = 1
  fixLineComp : GGFixLineComp Bs x L
  join : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p
  exists_nb : ∀ K ∈ 𝒦, ∃ y, Nb y K
  mem : ∀ y K, Nb y K → y ∈ B
  isComponentOf : ∀ y K, Nb y K → IsComponentOf K (Subgroup.centralizer ({y} : Set G))
  datum : ∀ y K, Nb y K → ∀ xb yb : ↥Bs, (xb : G) = x → (yb : G) = y →
    SignedNbrDatum n p (eta xb) (eta yb) ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom)
  mem_zpowers : ∀ y K, Nb y K → ∀ b : ↥Bs, (b : G) ∈ B →
    (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y
  plane : ∀ y K y₀ K₀, Nb y K → Nb y₀ K₀ → y ∈ Subgroup.closure ({x, y₀} : Set G)
  not_mem : ∀ y K, Nb y K → y ∉ Subgroup.zpowers x

private theorem zpowers_eq_of_mem_zpowers_of_pow_eq_one {M : Type*} [Group M] [Finite M]
    {p : ℕ} [Fact p.Prime]
    {a b : M} (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : b ∈ Subgroup.zpowers a) : Subgroup.zpowers b = Subgroup.zpowers a := by
  have hbord : orderOf b = p := orderOf_eq_prime hb hb1
  have haord : orderOf a = p := orderOf_eq_prime ha ha1
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hab) ?_
  simp [Nat.card_zpowers, haord, hbord]

private theorem isComponentOf_centralizer_of_frame [Finite G] {p n : ℕ} {B Bs L : Subgroup G}
    {x : G} {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta) {y : G} {K : Subgroup G} (hyK : Nb y K)
    {Q : Subgroup G} {yb vb : ↥Bs} (hyb : (yb : G) = y)
    (hQ : IsComponentOf Q (Subgroup.centralizer ({(vb : G)} : Set G)))
    (hyv : eta yb ∈ Subgroup.zpowers (eta vb)) :
    IsComponentOf Q (Subgroup.centralizer ({y} : Set G)) := by
  have hy1 : y ≠ 1 := fun h => hF.not_mem y K hyK (by rw [h]; exact Subgroup.one_mem _)
  have hyb1 : yb ≠ 1 := fun h => hy1 (by
    have h' : (yb : G) = 1 := congrArg Subtype.val h
    rwa [hyb] at h')
  have hyb_mem : yb ∈ Subgroup.zpowers vb := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyv
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, eta.injective (by rw [map_zpow]; exact hk)⟩
  have hvb1 : vb ≠ 1 := fun h => hyb1 (by simpa [h] using hyb_mem)
  have hyb_pow : (yb : ↥Bs) ^ p = 1 :=
    Subtype.ext (by simpa using hF.pow_eq_one yb.1 yb.2)
  have hvb_pow : (vb : ↥Bs) ^ p = 1 :=
    Subtype.ext (by simpa using hF.pow_eq_one vb.1 vb.2)
  have := Fact.mk hF.prime
  have hzp_eq : Subgroup.zpowers yb = Subgroup.zpowers vb :=
    zpowers_eq_of_mem_zpowers_of_pow_eq_one hvb_pow hyb_pow hvb1 hyb1 hyb_mem
  have hmap_y : (Subgroup.zpowers yb).map (Subgroup.subtype Bs) = Subgroup.zpowers y := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers ((yb : ↥Bs) : G) = Subgroup.zpowers y
    rw [hyb]
  have hmap_v : (Subgroup.zpowers vb).map (Subgroup.subtype Bs) =
      Subgroup.zpowers (vb : G) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hzpy : Subgroup.zpowers y = Subgroup.zpowers (vb : G) := by
    rw [← hmap_y, ← hmap_v, hzp_eq]
  have hcent : Subgroup.centralizer ({y} : Set G) =
      Subgroup.centralizer ({(vb : G)} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq hzpy
  rw [hcent]
  exact hQ

theorem GGBProperFrame.eq_of_isComponentOf [Finite G] {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    {y : G} {K : Subgroup G} (hyK : Nb y K) {Q : Subgroup G} {yb vb : ↥Bs} (hyb : (yb : G) = y)
    (hQ : IsComponentOf Q (Subgroup.centralizer ({(vb : G)} : Set G)))
    (hyv : eta yb ∈ Subgroup.zpowers (eta vb)) {I' : Finset (Fin n)} (hI' : n ≤ I'.card + 2)
    (hQs : ∀ a ∈ I', ∀ b ∈ I', a ≠ b →
      HasSignedSwap ((ggAutomizer Q Bs).map (MulAut.congr eta).toMonoidHom) a b) :
    K = Q := by
  obtain ⟨I, hIblock⟩ :=
    (hF.datum y K hyK ⟨x, hF.fixLineComp.mem⟩ yb rfl hyb).isSignedBlockOn
  have hcardle := (hF.datum y K hyK ⟨x, hF.fixLineComp.mem⟩ yb rfl hyb).card_fix_le
  have hI : n ≤ I.card + 2 := IsSignedBlockOn.le_card_add_two hF.prime hF.ne_two hIblock hcardle
  have hyswap : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      HasSignedSwap ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) a b :=
    fun a ha b hb hab => IsSignedBlockOn.hasSignedSwap hF.prime hIblock ha hb hab
  exact eq_of_isComponentOf_of_hasSignedSwap_on hF.prime hF.five_le eta
    (hF.isComponentOf y K hyK) (isComponentOf_centralizer_of_frame hF hyK hyb hQ hyv)
    hI hI' hyswap hQs

theorem GGBProperFrame.eq_map_conj_of_mem_zpowers [Finite G] {p n : ℕ} {B Bs L : Subgroup G}
    {x : G} {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    {y : G} {K : Subgroup G} (hyK : Nb y K) {Q : Subgroup G} {yb vb : ↥Bs} (hyb : (yb : G) = y)
    (hQ : IsComponentOf Q (Subgroup.centralizer ({(vb : G)} : Set G))) {I' : Finset (Fin n)}
    (hI' : n ≤ I'.card + 2)
    (hQs : ∀ a ∈ I', ∀ b ∈ I', a ≠ b →
      HasSignedSwap ((ggAutomizer Q Bs).map (MulAut.congr eta).toMonoidHom) a b)
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgs : MulAut.congr eta (ggConjAut Bs hg) ∈ Subgroup.closure
      (Set.range fun k : Fin n => (sgnAut k : MulAut (Fin n → Multiplicative (ZMod p)))))
    (hyv : eta yb ∈ Subgroup.zpowers (MulAut.congr eta (ggConjAut Bs hg) (eta vb))) :
    K = Q.map (MulAut.conj g).toMonoidHom := by
  have hvb : ((ggConjAut Bs hg vb : ↥Bs) : G) = g * (vb : G) * g⁻¹ := ggConjAut_apply Bs hg vb
  have hQ' : IsComponentOf (Q.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({((ggConjAut Bs hg vb : ↥Bs) : G)} : Set G)) := by
    have h1 := isComponentOf_centralizer_map_conj hQ g
    rwa [← hvb] at h1
  have hcongr : MulAut.congr eta (ggConjAut Bs hg) (eta vb) =
      eta (ggConjAut Bs hg vb) := by
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hyv' : eta yb ∈ Subgroup.zpowers (eta (ggConjAut Bs hg vb)) := by
    rw [← hcongr]
    exact hyv
  have hQs' : ∀ a ∈ I', ∀ b ∈ I', a ≠ b →
      HasSignedSwap ((ggAutomizer (Q.map (MulAut.conj g).toMonoidHom) Bs).map
        (MulAut.congr eta).toMonoidHom) a b := by
    intro a ha b hb hab
    rw [map_congr_ggAutomizer_map_conj eta hg Q]
    exact HasSignedSwap.map_conj_of_mem_closure (hQs a ha b hb hab) hgs
  exact eq_of_isComponentOf hF hyK hyb hQ' hyv' hI' hQs'

theorem GGBProperFrame.exists_mem_bBlockOn {p n : ℕ} {B Bs L : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {Nb : G → Subgroup G → Prop}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} (hF : GGBProperFrame p n B Bs L x 𝒦 Nb eta)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p) :
    ∃ K₀ ∈ 𝒦, ∃ I : Finset (Fin n), I.Nonempty ∧
      (ggAutomizer K₀ Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I := by
  have hΓ : ∀ K ∈ 𝒦, ∃ I : Finset (Fin n),
      IsSignedBlockOn n p I ((ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom) := by
    intro K hK
    obtain ⟨y, hyK⟩ := hF.exists_nb K hK
    exact (hF.datum y K hyK ⟨x, hF.fixLineComp.mem⟩
      ⟨y, hF.le (hF.mem y K hyK)⟩ rfl rfl).isSignedBlockOn
  have hsup : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom ⊔
      ⨆ K ∈ 𝒦, (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bSignedFull n p := by
    rw [← hF.join]
    simp only [ggAutomizerJoin, Subgroup.map_sup, Subgroup.map_iSup]
  exact exists_bBlockOn_of_sup_eq_bSignedFull hF.prime hF.ne_two
    (by have h := hF.five_le; omega) hL hΓ hsup

end CFSG.StandardType

end