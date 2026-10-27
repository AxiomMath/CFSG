module

public import CFSG.Monster.GMS.S365CentOmega
public import CFSG.Monster.GMS.S365CentOne
public import CFSG.Monster.GMS.S365CentThree
public import CFSG.Monster.GMS.S365CentPathSpec
public import CFSG.Monster.GMS.S365Four
import CFSG.Assembly.Defs
import CFSG.Monster.GMS.Leech.OddPhi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem exists_lift_stab
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q x y w : G}
    (h : Embedded a z₀ q x y w) (L : LeechSystem q) {s : Co1}
    (hsx : co1Act s (L.vec x) = L.vec x) (hsy : co1Act s (L.vec y) = L.vec y)
    (hsw : co1Act s (L.vec w) = L.vec w) :
    ∃ g : G, ∃ hgC : g ∈ Subgroup.centralizer ({q} : Set G), L.φ ⟨g, hgC⟩ = s ∧
      g * x * g⁻¹ = x ∧ g * y * g⁻¹ = y ∧ g * w * g⁻¹ = w :=
  exists_conj_lift L h.x_mem h.y_mem h.w_mem h.x_mem h.y_mem h.w_mem s hsx hsy hsw
    (h.fourPattern I hG L).linearIndependent

theorem exists_conj_to
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q q' x y w : G}
    (h : Embedded a z₀ q x y w) (h' : Embedded a z₀ q' x y w) :
    ∃ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G), g * q * g⁻¹ = q' := by
  obtain ⟨h₀, hh₀⟩ := isConj_iff.1 (h.q2B.symm.trans h'.q2B)
  have E1 := h.conj h₀
  rw [hh₀] at E1
  obtain ⟨L'⟩ := exists_leechSystem_of_isConj hG h'.q2B
  obtain ⟨g, hgC, hgx, hgy, hgw⟩ := exists_conj_exact I hG co1FourTV E1 L' h'.x_mem h'.y_mem
    h'.w_mem (h'.fourPattern I hG L')
  have hgq : g * q' * g⁻¹ = q' := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hgC
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hx : g * h₀ * x * (g * h₀)⁻¹ = x := by
    calc g * h₀ * x * (g * h₀)⁻¹ = g * (h₀ * x * h₀⁻¹) * g⁻¹ := by group
      _ = x := hgx
  have hy : g * h₀ * y * (g * h₀)⁻¹ = y := by
    calc g * h₀ * y * (g * h₀)⁻¹ = g * (h₀ * y * h₀⁻¹) * g⁻¹ := by group
      _ = y := hgy
  have hw : g * h₀ * w * (g * h₀)⁻¹ = w := by
    calc g * h₀ * w * (g * h₀)⁻¹ = g * (h₀ * w * h₀⁻¹) * g⁻¹ := by group
      _ = w := hgw
  refine ⟨g * h₀, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hx)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hy)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 hw)
  · calc g * h₀ * q * (g * h₀)⁻¹ = g * (h₀ * q * h₀⁻¹) * g⁻¹ := by group
      _ = g * q' * g⁻¹ := by rw [hh₀]
      _ = q' := hgq

theorem ncard_Omega_le
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hNo : Co1NoPatternIm)
    (hWit : Co1WitnessS) {q x y w : G} (h : Embedded a z₀ q x y w) :
    {q' : G | Embedded a z₀ q' x y w}.ncard ≤ 3 := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG h.q2B
  have hP := h.fourPattern I hG L
  obtain ⟨e₀, g₁, g₂, hg₁, hg₂, hmain⟩ := hWit _ _ _ hP
  have hfib : ∀ q' : G, Embedded a z₀ q' x y w → q' ≠ q → L.vec q' = e₀ := by
    intro q' h' hne
    by_contra hve
    have hQ : q' ∈ leechQ q := (h.adj I hG hNo h').2
    have hpat := h.pat0 I hG h' L hne hQ
    obtain ⟨g, hgmem, hne0, hnpat⟩ := hmain _ hpat hve
    have hgfix : co1Act g (L.vec x) = L.vec x ∧ co1Act g (L.vec y) = L.vec y ∧
        co1Act g (L.vec w) = L.vec w := by
      rcases hgmem with rfl | hg2
      · exact hg₁
      · have : g = g₂ := hg2
        subst this
        exact hg₂
    obtain ⟨γ, hγC, hγφ, hγx, hγy, hγw⟩ := exists_lift_stab I hG h L hgfix.1 hgfix.2.1 hgfix.2.2
    have h'' : Embedded a z₀ (γ * q' * γ⁻¹) x y w := by
      have := h'.conj γ
      rwa [hγx, hγy, hγw] at this
    have hQ'' : γ * q' * γ⁻¹ ∈ leechQ q := L.conj_mem' hγC hQ
    have hv'' : L.vec (γ * q' * γ⁻¹) = co1Act g (L.vec q') := by
      rw [L.vec_conj' hγC hQ, hγφ]
    have hne'' : q' ≠ γ * q' * γ⁻¹ := by
      intro heq
      apply hne0
      have : L.vec q' = co1Act g (L.vec q') := by rw [← hv'', ← heq]
      rw [← this]
      exact CFSG.Sporadic.Co1.Module.vec_add_self _
    have hmul := Embedded.mul I hG hNo h' h'' hne''
    have hQ3 : q' * (γ * q' * γ⁻¹) ∈ leechQ q := mul_mem hQ hQ''
    have hv3 : L.vec (q' * (γ * q' * γ⁻¹)) = L.vec q' + co1Act g (L.vec q') := by
      rw [L.vec_mul q' hQ _ hQ'', hv'']
    have hne3 : q' * (γ * q' * γ⁻¹) ≠ q := by
      intro heq
      apply hne0
      rw [← hv3, heq]
      exact L.vec_z
    have hpat3 := h.pat0 I hG hmul L hne3 hQ3
    rw [hv3] at hpat3
    exact hnpat hpat3
  have hsub : {q' : G | Embedded a z₀ q' x y w} ⊆
      {q} ∪ {u : G | u ∈ leechQ q ∧ L.vec u ∈ ({e₀} : Set (Fin 24 → ZMod 2))} := by
    intro q' h'
    by_cases hne : q' = q
    · exact Or.inl hne
    · exact Or.inr ⟨(h.adj I hG hNo h').2, hfib q' h' hne⟩
  calc {q' : G | Embedded a z₀ q' x y w}.ncard ≤
        ({q} ∪ {u : G | u ∈ leechQ q ∧ L.vec u ∈ ({e₀} : Set (Fin 24 → ZMod 2))}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({q} : Set G).ncard +
        {u : G | u ∈ leechQ q ∧ L.vec u ∈ ({e₀} : Set (Fin 24 → ZMod 2))}.ncard :=
        Set.ncard_union_le _ _
    _ = 3 := by
      rw [Set.ncard_singleton, L.ncard_preimage, Set.ncard_singleton]

theorem Embedded.of_lift
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {q x y w q' : G}
    (h : Embedded a z₀ q x y w) (Lw : LeechSystem w) {v : Fin 24 → ZMod 2} (hv : v ∈ co1Orbit 2)
    (hq'Q : q' ∈ leechQ w) (hq'v : Lw.vec q' = v) (hxq : x ∈ leechQ q') (hyq : y ∈ leechQ q') :
    Embedded a z₀ q' x y w := by
  have hqB : IsConj z₀ q' :=
    isConj_of_mem_typeSet_two I hG h.w2B Lw ⟨hq'Q, hq'v ▸ hv⟩
  have hqw : q' ≠ w := by
    intro heq
    have h0 : Lw.vec q' = 0 := by rw [heq]; exact Lw.vec_z
    exact Leech.ne_zero_of_mem_co1Orbit hv (hq'v.symm.trans h0)
  have hwq : w ∈ leechQ q' := mem_leechQ_of_mem_leechQ_four I hG h.w2B hqB hq'Q hqw
  have hxQ := h.x_not_mem_pivot I hG
  have hyQ := h.y_not_mem_pivot I hG
  have hxyQ : x * y ∉ leechQ w := by
    have hxyw : x * y * w = w * (x * y) :=
      ((show Commute x w from h.comm_xw hG).mul_left (show Commute y w from h.comm_yw hG)).eq
    exact (isConj_mul_iff I hG h.w2B h.line.2.2 hxyw).1 (by rw [← mul_assoc]; exact h.wxy2B)
  have hz : ∀ u : G, u ∈ leechQ w → w⁻¹ * u ∈ leechQ w := fun u hu =>
    mul_mem (inv_mem Lw.z_mem) hu
  refine ⟨h.line, hqB, hxq, hyq, hwq, h.w2B, hqw.symm, h.wx2B, h.wy2B, h.wxy2B, ?_, ?_, ?_⟩
  · intro hh
    apply hxQ
    have : x = w⁻¹ * q' := by rw [← hh]; group
    rw [this]
    exact hz q' hq'Q
  · intro hh
    apply hyQ
    have : y = w⁻¹ * q' := by rw [← hh]; group
    rw [this]
    exact hz q' hq'Q
  · intro hh
    apply hxyQ
    have : x * y = w⁻¹ * q' := by rw [← hh]; group
    rw [this]
    exact hz q' hq'Q

theorem exists_two_embedded
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hU2 : Co1FourU2)
    {q x y w : G} (h : Embedded a z₀ q x y w) :
    ∃ q₁ q₂ : G, Embedded a z₀ q₁ x y w ∧ Embedded a z₀ q₂ x y w ∧ q₁ ≠ q₂ := by
  obtain ⟨Lw⟩ := exists_leechSystem_of_isConj hG h.w2B
  have hI := co1InvolutionFacts
  have hK := isKlein_of_isLineTriple hG.1.1 h.line
  have hxC := h.x_mem_centralizer_pivot hG
  have hyC := h.y_mem_centralizer_pivot hG
  have hxyC : x * y ∈ Subgroup.centralizer ({w} : Set G) := mul_mem hxC hyC
  have hxQ := h.x_not_mem_pivot I hG
  have hyQ := h.y_not_mem_pivot I hG
  have hxyw : x * y * w = w * (x * y) :=
    ((show Commute x w from h.comm_xw hG).mul_left (show Commute y w from h.comm_yw hG)).eq
  have hxyQ : x * y ∉ leechQ w :=
    (isConj_mul_iff I hG h.w2B h.line.2.2 hxyw).1 (by rw [← mul_assoc]; exact h.wxy2B)
  have hlx := isLeechCentralLift_of_isConj I hG h.w2B hxC h.line.1 hxQ
  have hly := isLeechCentralLift_of_isConj I hG h.w2B hyC h.line.2.1 hyQ
  have hlxy := isLeechCentralLift_of_isConj I hG h.w2B hxyC h.line.2.2 hxyQ
  have hr : IsCo1TwoA (Lw.φ ⟨x, hxC⟩) := Lw.isCo1TwoA_phi hI hlx
  have hs : IsCo1TwoA (Lw.φ ⟨y, hyC⟩) := Lw.isCo1TwoA_phi hI hly
  have hrs : IsCo1TwoA (Lw.φ ⟨x * y, hxyC⟩) := Lw.isCo1TwoA_phi hI hlxy
  have hφ : Lw.φ ⟨x * y, hxyC⟩ = Lw.φ ⟨x, hxC⟩ * Lw.φ ⟨y, hyC⟩ := Lw.phi_mul hxC hyC
  have hφ' : Lw.φ ⟨y * x, mul_mem hyC hxC⟩ = Lw.φ ⟨y, hyC⟩ * Lw.φ ⟨x, hxC⟩ :=
    Lw.phi_mul hyC hxC
  have hcomm : Lw.φ ⟨x, hxC⟩ * Lw.φ ⟨y, hyC⟩ = Lw.φ ⟨y, hyC⟩ * Lw.φ ⟨x, hxC⟩ := by
    rw [← hφ, ← hφ']
    congr 1
    exact Subtype.ext hK.comm
  rw [hφ] at hrs
  obtain ⟨v₁, v₂, hv12, hv1, hv2, hRx1, hRy1, hRxy1, hRx2, hRy2, hRxy2⟩ :=
    hU2 _ _ hr hs hcomm hrs
  rw [← hφ] at hRxy1 hRxy2
  obtain ⟨q₁, hq₁Q, hq₁v, -, -, hxq₁, hyq₁⟩ :=
    exists_lift_K I hG h.w2B Lw h.line hxC hyC hxyC hxQ hyQ hxyQ hv1 hRx1 hRy1 hRxy1
  obtain ⟨q₂, hq₂Q, hq₂v, -, -, hxq₂, hyq₂⟩ :=
    exists_lift_K I hG h.w2B Lw h.line hxC hyC hxyC hxQ hyQ hxyQ hv2 hRx2 hRy2 hRxy2
  refine ⟨q₁, q₂, h.of_lift I hG Lw hv1 hq₁Q hq₁v hxq₁ hyq₁,
    h.of_lift I hG Lw hv2 hq₂Q hq₂v hxq₂ hyq₂, fun heq => hv12 ?_⟩
  rw [← hq₁v, ← hq₂v, heq]

theorem three_le_ncard
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hNo : Co1NoPatternIm)
    (hU2 : Co1FourU2) {q x y w : G} (h : Embedded a z₀ q x y w) :
    3 ≤ {q' : G | Embedded a z₀ q' x y w}.ncard := by
  obtain ⟨q₁, q₂, h₁, h₂, hne⟩ := exists_two_embedded I hG hU2 h
  have h₃ := Embedded.mul I hG hNo h₁ h₂ hne
  have hq₁1 : q₁ ≠ 1 := ne_one_of_orderOf ((orderOf_eq_of_isConj h₁.q2B).symm.trans hG.2.1)
  have hq₂1 : q₂ ≠ 1 := ne_one_of_orderOf ((orderOf_eq_of_isConj h₂.q2B).symm.trans hG.2.1)
  have hn13 : q₁ ≠ q₁ * q₂ := fun heq =>
    hq₂1 (mul_left_cancel (a := q₁) (by rw [mul_one]; exact heq.symm))
  have hn23 : q₂ ≠ q₁ * q₂ := fun heq =>
    hq₁1 (mul_right_cancel (b := q₂) (by rw [one_mul]; exact heq.symm))
  have hsub : ({q₁, q₂, q₁ * q₂} : Set G) ⊆ {q' : G | Embedded a z₀ q' x y w} := by
    rintro _ (rfl | rfl | rfl)
    · exact h₁
    · exact h₂
    · exact h₃
  have hcard : ({q₁, q₂, q₁ * q₂} : Set G).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨q₁, q₂, q₁ * q₂, hne, hn13, hn23, rfl⟩
  rw [← hcard]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem card_eightCent_four
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hNo : Co1NoPatternIm) (hWit : Co1WitnessS) (hU2 : Co1FourU2) {x y t : G}
    (hl : IsLineTriple a x y) (he : IsEightExt x y t) (hc : twoBCount z₀ x y t = 4) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G)) = eightCentOrder 4 := by
  obtain ⟨q, w, hwc, E⟩ := exists_embedded I hG co1FourU hl he hc
  rw [centralizer_inf_inf_eq_of_mem_cosetSet hwc]
  have horb := card_eq_card_inf_mul_ncard_conj
    (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G)) q
  have hΩ : {z : G | ∃ g ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G), g * q * g⁻¹ = z} = {q' : G | Embedded a z₀ q' x y w} := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨⟨hgx, hgy⟩, hgw⟩ := (Subgroup.mem_inf.1 hg).imp_left Subgroup.mem_inf.1
      have ex : g * x * g⁻¹ = x := by
        rw [mul_inv_eq_iff_eq_mul]; exact Subgroup.mem_centralizer_singleton_iff.1 hgx
      have ey : g * y * g⁻¹ = y := by
        rw [mul_inv_eq_iff_eq_mul]; exact Subgroup.mem_centralizer_singleton_iff.1 hgy
      have ew : g * w * g⁻¹ = w := by
        rw [mul_inv_eq_iff_eq_mul]; exact Subgroup.mem_centralizer_singleton_iff.1 hgw
      have := E.conj g
      rwa [ex, ey, ew] at this
    · intro hz
      exact exists_conj_to I hG E hz
  have hcard3 : {q' : G | Embedded a z₀ q' x y w}.ncard = 3 :=
    le_antisymm (ncard_Omega_le I hG hNo hWit E) (three_le_ncard I hG hNo hU2 E)
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG E.q2B
  have hP := E.fourPattern I hG L
  have hD : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({q} : Set G)) =
      2 ^ 22 * 4608 := by
    have hre : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
        Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({q} : Set G) =
        Subgroup.centralizer ({q} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({w} : Set G) := by
      ext g
      simp only [Subgroup.mem_inf]
      tauto
    rw [hre, L.card_inf_centralizer_three E.x_mem E.y_mem E.w_mem hP.linearIndependent,
      card_inf_stab_three hP]
  rw [hΩ, hcard3, hD] at horb
  have h4 : eightCentOrder 4 = 2 ^ 31 * 3 ^ 3 := rfl
  rw [h4, horb]
  norm_num

theorem eightCentOrders_of_facts
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hNo : Co1NoPatternIm) (hWit : Co1WitnessS) (hU2 : Co1FourU2) : EightCentOrders a z₀ := by
  intro x y t hl he
  rcases twoBCount_cases I hG x y t hl he with h1 | h3 | h4
  · rw [h1]
    exact card_eightCent_one I hG hl he h1
  · rw [h3]
    exact card_eightCent_three I hG hl he h3
  · rw [h4]
    exact card_eightCent_four I hG hNo hWit hU2 hl he h4

end S365

end CFSG.Monster.GMS
