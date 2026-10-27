module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6F1
public import CFSG.Quasithin.Vol2.Ch4Sec1Defs

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq {h : G} {X : Subgroup G} (hX : B6.conjSub h X = X) :
    h ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : h * x * h⁻¹ ∈ B6.conjSub h X := by rw [B6.mem_conjSub]; simpa [mul_assoc] using hx
    rwa [hX] at this
  · intro hx
    rw [← hX, B6.mem_conjSub] at hx
    simpa [mul_assoc] using hx

abbrev Yof (X : Subgroup G) : Subgroup G := oTwoUpper (Subgroup.centralizer (X : Set G))

theorem conjSub_Yof (h : G) (X : Subgroup G) : B6.conjSub h (Yof X) = Yof (B6.conjSub h X) := by
  rw [Yof, Yof, ← oTwoUpper_conjSub, centralizer_conjSub]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V]

structure Cyc (c : Ctx T L V E z v) (g : G) : Prop where
  hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)
  mem : g ∈ Subgroup.normalizer (c.R1 : Set G)
  hz : g * z * g⁻¹ = v
  hv : g * v * g⁻¹ = v * z

theorem exists_cyc (c : Ctx T L V E z v)
    (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ g, c.Cyc g := by
  obtain ⟨g, hg, hgz, hgv⟩ := c.exists_three_cycle hN
  exact ⟨g, hN, hg, hgz, hgv⟩

theorem CE_conjSub (c : Ctx T L V E z v) {h : G} (hh : h ∈ Subgroup.normalizer (E : Set G))
    {k : G} (hk : k ∈ Subgroup.centralizer (E : Set G)) :
    B6.conjSub k (B6.conjSub h V) = B6.conjSub h V ∧
      B6.conjSub k (B6.conjSub h c.L1) = B6.conjSub h c.L1 := by
  have hk' : h⁻¹ * k * h ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have he' : h * e * h⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hh e).1 he
    have h1 := Subgroup.mem_centralizer_iff.1 hk _ he'
    calc e * (h⁻¹ * k * h) = h⁻¹ * ((h * e * h⁻¹) * k) * h := by group
      _ = h⁻¹ * (k * (h * e * h⁻¹)) * h := by rw [h1]
      _ = h⁻¹ * k * h * e := by group
  have e : k * h = h * (h⁻¹ * k * h) := by group
  refine ⟨?_, ?_⟩
  · rw [← B6.conjSub_mul, e, B6.conjSub_mul, B6.conjSub_eq_self (c.CE_le_NV hk')]
  · rw [← B6.conjSub_mul, e, B6.conjSub_mul, B6.conjSub_eq_self (c.CE_le_N_L1 hk')]

namespace Cyc

variable {c : Ctx T L V E z v} {g : G} (hg : c.Cyc g)
include hg

theorem NR1_le_NE : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (E : Set G) :=
  (c.partA hg.hN).2.2

theorem sq_z : (g * g) * z * (g * g)⁻¹ = v * z := by
  have := (c.cube_conj hg.hz hg.hv).1
  rwa [pow_two] at this

theorem cube_z : (g * g * g) * z * (g * g * g)⁻¹ = z := by
  have := (c.cube_conj hg.hz hg.hv).2.1
  rwa [pow_three'] at this

theorem conj_z_cases {h : G} (hh : h ∈ Subgroup.normalizer (c.R1 : Set G)) :
    h * z * h⁻¹ = z ∨ h * z * h⁻¹ = v ∨ h * z * h⁻¹ = v * z := by
  have hE := hg.NR1_le_NE hh
  have h1 : h * z * h⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hE z).1 c.facts4.1
  rcases c.mem_E h1 with h2 | h2 | h2 | h2
  · exfalso
    apply c.z_ne_one
    calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
      _ = 1 := by rw [h2]; group
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h2)

theorem fix_z {h : G} (hh : h ∈ Subgroup.normalizer (c.R1 : Set G)) (hz : h * z * h⁻¹ = z) :
    h ∈ Subgroup.normalizer (V : Set G) ∧ h ∈ Subgroup.normalizer (c.L1 : Set G) := by
  have hz' : h ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * z = h * z * h⁻¹ * h := by group
      _ = z * h := by rw [hz]
  refine ⟨c.Cz_eq_NV ▸ hz', c.mem_N_L1 (c.M_eq ▸ hz') (hg.NR1_le_NE hh)⟩

theorem conjSub_eq_of_conj_z {h h' : G} (hh : h ∈ Subgroup.normalizer (c.R1 : Set G))
    (hh' : h' ∈ Subgroup.normalizer (c.R1 : Set G)) (heq : h * z * h⁻¹ = h' * z * h'⁻¹) :
    B6.conjSub h V = B6.conjSub h' V ∧ B6.conjSub h c.L1 = B6.conjSub h' c.L1 := by
  have hk : h'⁻¹ * h ∈ Subgroup.normalizer (c.R1 : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hh') hh
  have hkz : (h'⁻¹ * h) * z * (h'⁻¹ * h)⁻¹ = z := by
    calc (h'⁻¹ * h) * z * (h'⁻¹ * h)⁻¹ = h'⁻¹ * (h * z * h⁻¹) * h' := by group
      _ = h'⁻¹ * (h' * z * h'⁻¹) * h' := by rw [heq]
      _ = z := by group
  obtain ⟨hkV, hkL⟩ := hg.fix_z hk hkz
  have e : h = h' * (h'⁻¹ * h) := by group
  refine ⟨?_, ?_⟩
  · rw [e, B6.conjSub_mul, B6.conjSub_eq_self hkV]
  · rw [e, B6.conjSub_mul, B6.conjSub_eq_self hkL]

theorem conjSub_V_cases {h : G} (hh : h ∈ Subgroup.normalizer (c.R1 : Set G)) :
    B6.conjSub h V = V ∨ B6.conjSub h V = B6.conjSub g V ∨
      B6.conjSub h V = B6.conjSub (g * g) V := by
  have hgg : g * g ∈ Subgroup.normalizer (c.R1 : Set G) := Subgroup.mul_mem _ hg.mem hg.mem
  rcases hg.conj_z_cases hh with h1 | h1 | h1
  · left
    exact B6.conjSub_eq_self (hg.fix_z hh h1).1
  · right; left
    exact (hg.conjSub_eq_of_conj_z hh hg.mem (h1.trans hg.hz.symm)).1
  · right; right
    exact (hg.conjSub_eq_of_conj_z hh hgg (h1.trans hg.sq_z.symm)).1

abbrev W (_ : c.Cyc g) : Subgroup G :=
  Yof V ⊓ Yof (B6.conjSub g V) ⊓ Yof (B6.conjSub (g * g) V)

theorem conjSub_W_le {h : G} (hh : h ∈ Subgroup.normalizer (c.R1 : Set G)) :
    B6.conjSub h hg.W ≤ hg.W := by
  have hgg : g * g ∈ Subgroup.normalizer (c.R1 : Set G) := Subgroup.mul_mem _ hg.mem hg.mem
  have key : ∀ x ∈ Subgroup.normalizer (c.R1 : Set G), B6.conjSub h hg.W ≤
      Yof (B6.conjSub x V) := by
    intro x hx
    have hx' : h⁻¹ * x ∈ Subgroup.normalizer (c.R1 : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hx
    have e : B6.conjSub x V = B6.conjSub h (B6.conjSub (h⁻¹ * x) V) := by
      rw [← B6.conjSub_mul, mul_inv_cancel_left]
    rw [e, ← conjSub_Yof]
    refine (B6.conjSub h).monotone ?_
    rcases hg.conjSub_V_cases hx' with h1 | h1 | h1 <;> rw [h1]
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  refine le_inf (le_inf ?_ (key g hg.mem)) (key (g * g) hgg)
  have := key 1 (Subgroup.one_mem _)
  rwa [B6.conjSub_one] at this

theorem NR1_le_NW : Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (hg.W : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    apply hg.conjSub_W_le hh
    rw [B6.mem_conjSub]
    simpa [mul_assoc] using hx
  · intro hx
    have h1 := hg.conjSub_W_le (Subgroup.inv_mem _ hh)
    apply h1
    rw [B6.mem_conjSub]
    simpa [mul_assoc] using hx

theorem CE_le_NW : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (hg.W : Set G) := by
  intro k hk
  have hgE := hg.NR1_le_NE hg.mem
  have hggE : g * g ∈ Subgroup.normalizer (E : Set G) := Subgroup.mul_mem _ hgE hgE
  have hY : ∀ h ∈ Subgroup.normalizer (E : Set G),
      B6.conjSub k (Yof (B6.conjSub h V)) = Yof (B6.conjSub h V) := by
    intro h hh
    rw [conjSub_Yof, (c.CE_conjSub hh hk).1]
  have hV : B6.conjSub k (Yof V) = Yof V := by
    have := hY 1 (Subgroup.one_mem _)
    rwa [B6.conjSub_one] at this
  apply mem_normalizer_of_conjSub_eq
  rw [W, map_inf, map_inf, hV, hY g hgE, hY (g * g) hggE]

theorem W_le_CE : hg.W ≤ Subgroup.centralizer (E : Set G) :=
  inf_le_left.trans (inf_le_left.trans ((oTwoUpper_le _).trans (Subgroup.centralizer_le c.EV)))

theorem L_le_CW (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) :
    L ≤ Subgroup.centralizer (hg.W : Set G) := by
  have h1 : hg.W ≤ Subgroup.centralizer (L : Set G) :=
    inf_le_left.trans (inf_le_left.trans (c.oTwoUpper_CV_le hcomm))
  exact Subgroup.le_centralizer_iff.mp h1

theorem W_eq_bot (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) : hg.W = ⊥ := by
  have hyp := c.cx.hyp
  by_contra hne
  have hWK := hg.W_le_CE
  have hnorm : (hg.W.subgroupOf (Subgroup.centralizer (E : Set G))).Normal := by
    refine ⟨fun a ha b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.1 (hg.CE_le_NW b.2) a).1 ha
  have hchar : QuasithinUnique.CharTwo hg.W := CT.CharTwo.of_normal c.charTwo_CE hWK hnorm
  have hO2 : pCoreOf 2 hg.W ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ pCoreOf 2 hg.W := hchar ⟨hx, by
      rw [h0]
      exact Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
        rw [hy, one_mul, mul_one]⟩
    rwa [h0] at h1
  have hNW : Subgroup.normalizer (hg.W : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 hg.W : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 hg.W
  have hLT : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 hg.W : Set G) := by
    refine sup_le ?_ ?_
    · exact (hg.L_le_CW hcomm).trans ((Subgroup.centralizer_le_normalizer _).trans hNW)
    · exact c.T_le_NR1.trans (hg.NR1_le_NW.trans hNW)
  have hM := Ch4.isUniqueM_normalizer_le c.uniq hO2
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 hg.W) hLT
  exact hg.hN (hg.NR1_le_NW.trans (hNW.trans hM))

theorem eq_one_of_odd (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) {x : G}
    (h0 : x ∈ Subgroup.centralizer (V : Set G))
    (h1 : x ∈ Subgroup.centralizer (B6.conjSub g V : Set G))
    (h2 : x ∈ Subgroup.centralizer (B6.conjSub (g * g) V : Set G)) (hodd : Odd (orderOf x)) :
    x = 1 := by
  have hW : x ∈ hg.W := ⟨⟨mem_oTwoUpper_of_odd h0 hodd, mem_oTwoUpper_of_odd h1 hodd⟩,
    mem_oTwoUpper_of_odd h2 hodd⟩
  rw [hg.W_eq_bot hcomm, Subgroup.mem_bot] at hW
  exact hW

end Cyc

end Ctx

end N1246

end CFSG.Quasithin.H13
