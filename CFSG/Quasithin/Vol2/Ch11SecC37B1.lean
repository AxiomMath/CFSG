module

public import CFSG.Quasithin.Vol2.Ch11SecC37E
public import CFSG.Quasithin.Vol2.Ch11SecCB51Core
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem sylow_LT : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
  isSylowTwoOf_of_quasithinIsSylowTwo s.hyp.fsu.sylow le_sup_right

theorem charTwo_LT : QuasithinUnique.CharTwo (L ⊔ T) := by
  refine charTwo_of_inH s.hyp.fsu.qtke.2.1 (s.hyp.fsu.sylow.1.toSylow s.hyp.fsu.sylow.2)
    ⟨le_sup_right, fun h0 => B51.pCoreOf_ne_bot_of_faithful s.hyp.fsu.faithful ?_⟩
  have hn : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer s.hyp.normal)
  have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T)
    le_sup_left hn
  rw [h0] at this
  exact le_bot_iff.mp this

theorem vzLT : VZ T (L ⊔ T) ≤ pCoreOf 2 (L ⊔ T) ⊓
      Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) ∧
    IsElemAbelian 2 (VZ T (L ⊔ T)) ∧ IsTwoReducedIn (L ⊔ T) (VZ T (L ⊔ T)) :=
  conjClosure_isTwoReducedIn_of_charTwo s.sylow_LT s.charTwo_LT le_rfl

theorem fsuV_inf_centralizer_T :
    fsuV T I ⊓ Subgroup.centralizer (T : Set G) ≠ ⊥ ∧
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) ≤ quasithinOmegaOneCenter T := by
  have hVT : fsuV T I ≤ T := SecA.fsuV_le_T s.hyp
  refine ⟨SecB.inf_centralizer_ne_bot s.hyp.fsu.sylow.1 hVT (SecA.T_le_normalizer_fsuV T I)
    (SecA.fsuV_ne_bot s.hyp), fun v hv => ?_⟩
  exact Subgroup.subset_closure ⟨⟨hVT hv.1, hv.2⟩, (SecA.isElemAbelian_fsuV s.hyp).2 v hv.1⟩

theorem fsuV_le_W (h1102 : Stmt11_0_2) (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    fsuV T I ≤ VZ T (L ⊔ T) := by
  obtain ⟨_, hirr, -⟩ := h1102 G T L I n s.hyp
  obtain ⟨hCT1, hCTZ⟩ := s.fsuV_inf_centralizer_T
  have hLJ : L ≤ Subgroup.normalizer ((fsuV T I ⊓ VZ T (L ⊔ T) : Subgroup G) : Set G) :=
    fun l hl => F7.mem_normalizer_inf (SecA.L_le_normalizer_fsuV s.hyp hl)
      (le_normalizer_VZ T (L ⊔ T) (le_sup_left (a := L) hl))
  rcases hirr.2.2.2.2.2 (fsuV T I ⊓ VZ T (L ⊔ T)) (by rw [hVL]; exact bot_le) inf_le_left hLJ
    with h | h
  · exfalso
    apply hCT1
    rw [eq_bot_iff, ← hVL, ← h]
    exact fun v hv => ⟨hv.1, Z_le_VZ T (L ⊔ T) (hCTZ hv)⟩
  · intro v hv
    rw [← h] at hv
    exact hv.2

theorem commutator_W_ne_bot
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ⁅VZ T (L ⊔ T), L⁆ ≠ ⊥ := by
  intro h
  obtain ⟨hCT1, hCTZ⟩ := s.fsuV_inf_centralizer_T
  apply hCT1
  rw [eq_bot_iff, ← hZL]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact fun v hv => ⟨hCTZ hv, h (Z_le_VZ T (L ⊔ T) (hCTZ hv))⟩

theorem two_LT : ∀ y ∈ L ⊔ T, ∃ e : ℕ, y ^ 2 ^ e ∈
    L ⊔ Subgroup.centralizer (VZ T (L ⊔ T) : Set G) := fun y hy => by
  obtain ⟨e, he⟩ := two_of_sup s.hyp.fsu.sylow.1 s.hyp.normal y hy
  exact ⟨e, Subgroup.mem_sup_left he⟩

theorem T_le_normalizer_commutator :
    T ≤ Subgroup.normalizer ((⁅VZ T (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
  intro t ht
  have htW : t ∈ Subgroup.normalizer (VZ T (L ⊔ T) : Set G) :=
    le_normalizer_VZ T (L ⊔ T) (le_sup_right (b := T) ht)
  have htL : t ∈ Subgroup.normalizer (L : Set G) := s.hyp.normal ht
  have hmap : (⁅VZ T (L ⊔ T), L⁆ : Subgroup G).map (MulAut.conj t).toMonoidHom =
      ⁅VZ T (L ⊔ T), L⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer htW,
      map_conj_eq_of_mem_normalizer htL]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : t * y * t⁻¹ = t * x * t⁻¹ := by simpa [MulAut.conj_apply] using hyx
      exact mul_left_cancel (mul_right_cancel h1)
    rw [← this]
    exact hy

theorem W_le_Z_sup : VZ T (L ⊔ T) ≤ quasithinOmegaOneCenter T ⊔ ⁅VZ T (L ⊔ T), L⁆ := by
  refine conjClosure_le fun x hx z hz => ?_
  obtain ⟨l, hl, t, ht, rfl⟩ := mem_sup_of_le_normalizer s.hyp.normal hx
  have htz : t * z * t⁻¹ = z := by
    rw [Subgroup.mem_centralizer_iff.mp (Z_le_center T hz).2 t ht, mul_inv_cancel_right]
  have hc : l * z * l⁻¹ * z⁻¹ ∈ ⁅VZ T (L ⊔ T), L⁆ := by
    have h1 := Subgroup.commutator_mem_commutator (Z_le_VZ T (L ⊔ T) hz) hl
    have h2 : l * z * l⁻¹ * z⁻¹ = ⁅z, l⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [h2]
    exact Subgroup.inv_mem _ h1
  have e : l * t * z * (l * t)⁻¹ = (l * z * l⁻¹ * z⁻¹) * z := by
    calc l * t * z * (l * t)⁻¹ = l * (t * z * t⁻¹) * l⁻¹ := by group
      _ = (l * z * l⁻¹ * z⁻¹) * z := by rw [htz]; group
  rw [e, sup_comm]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hz)

theorem commutator_LT_eq : ⁅VZ T (L ⊔ T), L ⊔ T⁆ = ⁅VZ T (L ⊔ T), L⁆ := by
  have hWab := s.vzLT.2.1
  have hcomm : ∀ a ∈ VZ T (L ⊔ T), ∀ b ∈ VZ T (L ⊔ T), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hWab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUW : ⁅VZ T (L ⊔ T), L⁆ ≤ VZ T (L ⊔ T) := by
    rw [Subgroup.commutator_le]
    intro w hw l hl
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_VZ T (L ⊔ T)
      (le_sup_left (a := L) hl)) w⁻¹).mp ((VZ T (L ⊔ T)).inv_mem hw)
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc l]
    exact (VZ T (L ⊔ T)).mul_mem hw this
  have hLN : L ≤ Subgroup.normalizer ((⁅VZ T (L ⊔ T), L⁆ : Subgroup G) : Set G) :=
    le_sup_right.trans (A3.sup_le_normalizer_commutator _ L)
  have hT : ∀ w ∈ VZ T (L ⊔ T), ∀ t ∈ T, ⁅w, t⁆ ∈ ⁅VZ T (L ⊔ T), L⁆ := by
    intro w hw t ht
    have hZN : ⁅VZ T (L ⊔ T), L⁆ ≤ Subgroup.normalizer
        (quasithinOmegaOneCenter T : Set G) := fun u hu => le_normalizer_of_commute
      (fun a ha b hb => (hcomm a (Z_le_VZ T (L ⊔ T) ha) b (hUW hb))) hu
    obtain ⟨z, hz, u, hu, rfl⟩ := mem_sup_of_le_normalizer hZN (s.W_le_Z_sup hw)
    have hzt : z * t = t * z := (Subgroup.mem_centralizer_iff.mp (Z_le_center T hz).2 t ht).symm
    have hzu : z * u = u * z := hcomm z (Z_le_VZ T (L ⊔ T) hz) u (hUW hu)
    have e : ⁅z * u, t⁆ = u * (t * u⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      calc z * u * t * (z * u)⁻¹ * t⁻¹ = u * (z * t * z⁻¹) * u⁻¹ * t⁻¹ := by rw [hzu]; group
        _ = u * (t * u⁻¹ * t⁻¹) := by rw [hzt, mul_inv_cancel_right]; group
    rw [e]
    exact Subgroup.mul_mem _ hu ((Subgroup.mem_normalizer_iff.mp
      (s.T_le_normalizer_commutator ht) _).mp (Subgroup.inv_mem _ hu))
  refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl le_sup_left)
  rw [Subgroup.commutator_le]
  intro w hw x hx
  obtain ⟨l, hl, t, ht, rfl⟩ := mem_sup_of_le_normalizer s.hyp.normal hx
  have e : ⁅w, l * t⁆ = ⁅w, l⁆ * (l * ⁅w, t⁆ * l⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator hw hl)
    ((Subgroup.mem_normalizer_iff.mp (hLN hl) _).mp (hT w hw t ht))

theorem exists_decomp {z : G} (hz : z ∈ quasithinOmegaOneCenter T) :
    ∃ u ∈ ⁅VZ T (L ⊔ T), L⁆, ∃ c ∈ VZ T (L ⊔ T) ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) :
      Set G), z = u * c := by
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (Z_le_center T hx).2 t ht).symm
  have hdec := conjClosure_eq_commutator_sup (F7.isSylowTwoOf_odd_relIndex s.sylow_LT)
    s.vzLT.2.1 hTZ
  have hzW : z ∈ VZ T (L ⊔ T) := Z_le_VZ T (L ⊔ T) hz
  have hWab := s.vzLT.2.1
  have hcomm : ∀ a ∈ VZ T (L ⊔ T), ∀ b ∈ VZ T (L ⊔ T), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hWab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hz' : z ∈ ⁅VZ T (L ⊔ T), L⁆ ⊔
      (VZ T (L ⊔ T) ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G)) := by
    rw [← s.commutator_LT_eq]
    have h1 : z ∈ conjClosure (quasithinOmegaOneCenter T) (L ⊔ T) := hzW
    rw [hdec] at h1
    exact h1
  have hUW : ⁅VZ T (L ⊔ T), L⁆ ≤ VZ T (L ⊔ T) := by
    rw [← s.commutator_LT_eq, Subgroup.commutator_le]
    intro w hw x hx
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_VZ T (L ⊔ T) hx) w⁻¹).mp
      ((VZ T (L ⊔ T)).inv_mem hw)
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc x]
    exact (VZ T (L ⊔ T)).mul_mem hw this
  have hBN : VZ T (L ⊔ T) ⊓ Subgroup.centralizer ((L ⊔ T : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((⁅VZ T (L ⊔ T), L⁆ : Subgroup G) : Set G) :=
    le_normalizer_of_commute fun a ha b hb => hcomm a (hUW ha) b hb.1
  exact mem_sup_of_le_normalizer hBN hz'

theorem not_d0_centralizes_Z (hG16 : ASInputs.AS_G_1_6) (hAS : FactAStarSylow)
    (hFPF : FactSL2NatFPF) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (hG2 : SecA.FactG2DerivedOrder) (h1122 : Stmt11_2_2) (h1134 : Stmt11_3_4)
    (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) (h331 : Stmt3_3_1)
    (hSN : FactSL2SylowNormalizer) {D : Subgroup G}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    ¬ ∀ d ∈ d0Of D, ∀ z ∈ quasithinOmegaOneCenter T, d * z * d⁻¹ = z := by
  intro hall
  obtain ⟨d, hdD₀, hdK, hdodd, hdV⟩ := s.exists_mem_d0Of h331 h1135 h1136 hSN hD
  apply s.h31.moves
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro z hz
  have hzK := s.mem_centralizer_of_fix hG16 hAS hFPF hF h1102 hG2 h1122 h1134 h1135 h1136 hdK
    hdodd hdV (Z_le_VZ T H hz) (hall d hdD₀ z hz)
  have hzT : z ∈ Subgroup.centralizer (T : Set G) := (Z_le_center T hz).2
  have hle : oTwoUpper H ⊔ T ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun k hk => ?_) (fun t ht => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzK k hk
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hzT t ht
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := hle (s.sup_eq.ge hh)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
