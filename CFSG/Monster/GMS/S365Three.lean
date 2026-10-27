module

public import CFSG.Monster.GMS.S365Root
public import CFSG.Monster.GMS.S365Exists
public import CFSG.Monster.GMS.Leech.OddLift
import CFSG.Assembly.Defs
import CFSG.Monster.GMS.Leech.OddPhi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ w : G}

theorem exists_vec_eq_add
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (L : LeechSystem w) {x y : G} (hl : IsLineTriple a x y) (hxQ : x ∈ leechQ w)
    (hyC : y ∈ Subgroup.centralizer ({w} : Set G)) (hyQ : y ∉ leechQ w) (hxy : x * y = y * x) :
    ∃ v : Fin 24 → ZMod 2, L.vec x = v + co1Act (L.φ ⟨y, hyC⟩) v := by
  have hI := co1InvolutionFacts
  have hly := isLeechCentralLift_of_isConj I hG hw hyC hl.2.1 hyQ
  have hxyC : x * y ∈ Subgroup.centralizer ({w} : Set G) := mul_mem (L.mem_centralizer hxQ) hyC
  have hxyQ : x * y ∉ leechQ w := by
    intro h
    apply hyQ
    have := mul_mem (inv_mem hxQ) h
    rwa [inv_mul_cancel_left] at this
  have hly₂ := isLeechCentralLift_of_isConj I hG hw hxyC hl.2.2 hxyQ
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hly.mul_self
  have hQ : y⁻¹ * (x * y) ∈ leechQ w := by
    have e : y⁻¹ * (x * y) = x := by
      rw [hyi, ← mul_assoc, ← hxy, mul_assoc, hly.mul_self, mul_one]
    rw [e]
    exact hxQ
  obtain ⟨-, hft, -⟩ := L.central_lift_facts hI hly.mem_centralizer hly.orderOf_eq_two
    hly.not_mem hly.card
  obtain ⟨-, hfx, -⟩ := L.central_lift_facts hI hly₂.mem_centralizer hly₂.orderOf_eq_two
    hly₂.not_mem hly₂.card
  obtain ⟨p, hp, hpx⟩ := L.exists_conj_of_inv_mem hly.mem_centralizer hly₂.mem_centralizer
    hly.mul_self hly₂.mul_self hQ hft hfx
  have hpC : p ∈ Subgroup.centralizer ({w} : Set G) := L.mem_centralizer hp
  rcases hpx with h1 | h2
  · refine ⟨L.vec p, ?_⟩
    have hxe : x = p * (y * p⁻¹ * y⁻¹) := by
      calc x = x * y * y⁻¹ := by group
        _ = p * y * p⁻¹ * y⁻¹ := by rw [← h1]
        _ = p * (y * p⁻¹ * y⁻¹) := by group
    have hconj : y * p⁻¹ * y⁻¹ ∈ leechQ w := L.conj_mem' hyC (inv_mem hp)
    calc L.vec x = L.vec (p * (y * p⁻¹ * y⁻¹)) := by rw [← hxe]
      _ = L.vec p + L.vec (y * p⁻¹ * y⁻¹) := L.vec_mul p hp _ hconj
      _ = L.vec p + co1Act (L.φ ⟨y, hyC⟩) (L.vec p⁻¹) := by rw [L.vec_conj' hyC (inv_mem hp)]
      _ = L.vec p + co1Act (L.φ ⟨y, hyC⟩) (L.vec p) := by rw [L.vec_inv hp]
  · exfalso
    have hpw : p * w * p⁻¹ = w := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hpC
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    set c := p * y * p⁻¹ with hc
    have hcA : IsConj a c := (isConj_conj_iff a p y).2 hl.2.1
    have hcQ : c ∉ leechQ w := L.conj_not_mem hpC hyQ
    have hcC : c ∈ Subgroup.centralizer ({w} : Set G) :=
      mul_mem (mul_mem hpC hyC) (inv_mem hpC)
    have hcw : c * w = w * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
    have hxy_eq : x * y = w * c := by
      rw [← h2, ← hcw]
      calc p * (y * w) * p⁻¹ = (p * y * p⁻¹) * (p * w * p⁻¹) := by group
        _ = c * w := by rw [hpw]
    have hB : IsConj z₀ (x * y) := by
      rw [hxy_eq]
      exact (isConj_mul_iff I hG hw hcA hcw).2 hcQ
    exact hG.not_isConj (hl.2.2.trans hB.symm)

theorem exists_conj_three_same
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hF : Co1RootTransitive) (hw : IsConj z₀ w) {x x' y : G} (hl : IsLineTriple a x y)
    (hl' : IsLineTriple a x' y) (hxQ : x ∈ leechQ w) (hxQ' : x' ∈ leechQ w)
    (hyC : y ∈ Subgroup.centralizer ({w} : Set G)) (hyQ : y ∉ leechQ w) (hxy : x * y = y * x)
    (hxy' : x' * y = y * x') :
    ∃ g ∈ Subgroup.centralizer ({w} : Set G), g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG hw
  have hI := co1InvolutionFacts
  have hly := isLeechCentralLift_of_isConj I hG hw hyC hl.2.1 hyQ
  have hr : IsCo1TwoA (L.φ ⟨y, hyC⟩) := L.isCo1TwoA_phi hI hly
  have hx0 := mem_typeSet_zero_of_isConj I hG hw L hxQ hl.1
  have hx0' := mem_typeSet_zero_of_isConj I hG hw L hxQ' hl'.1
  obtain ⟨cbar, hcbar, hcbaru⟩ := hF _ hr (L.vec x) hx0.2 (L.vec x') hx0'.2
    (exists_vec_eq_add I hG hw L hl hxQ hyC hyQ hxy)
    (exists_vec_eq_add I hG hw L hl' hxQ' hyC hyQ hxy')
  obtain ⟨chat, hchat⟩ := L.φ_surj cbar
  have hchatC : (chat : G) ∈ Subgroup.centralizer ({w} : Set G) := chat.2
  have hQ : y⁻¹ * ((chat : G) * y * (chat : G)⁻¹) ∈ leechQ w := by
    have hmem : (chat : G) * y * (chat : G)⁻¹ ∈ Subgroup.centralizer ({w} : Set G) :=
      mul_mem (mul_mem hchatC hyC) (inv_mem hchatC)
    refine (L.phi_eq_iff hyC hmem).1 ?_
    have hcomm : cbar * L.φ ⟨y, hyC⟩ = L.φ ⟨y, hyC⟩ * cbar := by
      have := hcbar
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    show L.φ ⟨y, hyC⟩ = L.φ (chat * ⟨y, hyC⟩ * chat⁻¹)
    rw [map_mul, map_mul, map_inv, hchat, hcomm, mul_inv_cancel_right]
  obtain ⟨p, hp, hpc⟩ := L.exists_mul_mem_centralizer_of_lift hI hly hchatC hQ
  have hpC : p ∈ Subgroup.centralizer ({w} : Set G) := L.mem_centralizer hp
  have hg₂C : p * (chat : G) ∈ Subgroup.centralizer ({w} : Set G) := mul_mem hpC hchatC
  have hg₂y : p * (chat : G) * y * (p * (chat : G))⁻¹ = y := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hpc
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hφg₂ : L.φ ⟨p * (chat : G), hg₂C⟩ = cbar := by
    have h1 : L.φ ⟨p * (chat : G), hg₂C⟩ = L.φ ⟨p, hpC⟩ * L.φ ⟨(chat : G), hchatC⟩ :=
      L.phi_mul hpC hchatC
    rw [h1, (L.φ_ker ⟨p, hpC⟩).2 hp, one_mul]
    exact hchat
  have hx₂Q : p * (chat : G) * x * (p * (chat : G))⁻¹ ∈ leechQ w := L.conj_mem' hg₂C hxQ
  have hvec : L.vec (p * (chat : G) * x * (p * (chat : G))⁻¹) = L.vec x' := by
    rw [L.vec_conj' hg₂C hxQ, hφg₂]
    exact hcbaru
  refine ⟨p * (chat : G), hg₂C, ?_, hg₂y⟩
  rcases L.eq_or_eq_mul_z hx₂Q hxQ' hvec with h | h
  · exact h
  · exfalso
    have hA₂ : IsConj a (p * (chat : G) * x * (p * (chat : G))⁻¹ * y) := by
      have e : p * (chat : G) * x * (p * (chat : G))⁻¹ * y =
          p * (chat : G) * (x * y) * (p * (chat : G))⁻¹ := by
        conv_lhs => rw [← hg₂y]
        group
      rw [e]
      exact (isConj_conj_iff a _ _).2 hl.2.2
    have hx'w : x' * w = w * x' := Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer hxQ')
    have hyw : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
    have hcw : x' * y * w = w * (x' * y) := by
      rw [mul_assoc, hyw, ← mul_assoc, hx'w, mul_assoc]
    have hcQ : x' * y ∉ leechQ w := by
      intro hc
      apply hyQ
      have := mul_mem (inv_mem hxQ') hc
      rwa [inv_mul_cancel_left] at this
    have hB : IsConj z₀ (w * (x' * y)) := (isConj_mul_iff I hG hw hl'.2.2 hcw).2 hcQ
    have e : p * (chat : G) * x * (p * (chat : G))⁻¹ * y = w * (x' * y) := by
      rw [h]
      calc x' * w * y = x' * (w * y) := by rw [mul_assoc]
        _ = x' * (y * w) := by rw [hyw]
        _ = x' * y * w := by rw [mul_assoc]
        _ = w * (x' * y) := hcw
    rw [e] at hA₂
    exact hG.not_isConj (hA₂.trans hB.symm)

theorem exists_conj_three
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hF : Co1RootTransitive) (hw : IsConj z₀ w) {x y x' y' : G} (hl : IsLineTriple a x y)
    (hl' : IsLineTriple a x' y') (hxQ : x ∈ leechQ w)
    (hyC : y ∈ Subgroup.centralizer ({w} : Set G)) (hyQ : y ∉ leechQ w) (hxy : x * y = y * x)
    (hxQ' : x' ∈ leechQ w) (hyC' : y' ∈ Subgroup.centralizer ({w} : Set G))
    (hyQ' : y' ∉ leechQ w) (hxy' : x' * y' = y' * x') :
    ∃ g ∈ Subgroup.centralizer ({w} : Set G), g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG hw
  obtain ⟨c₀, hc₀, hc₀y⟩ := isConj_of_not_mem_leechQ I.sls I.tableV I.leech hG hw hyC hyC' hyQ
    hyQ' hl.2.1 hl'.2.1
  have hl₁ : IsLineTriple a (c₀ * x * c₀⁻¹) y' := by
    have := isLineTriple_conj hl c₀
    rwa [hc₀y] at this
  have hx₁Q : c₀ * x * c₀⁻¹ ∈ leechQ w := L.conj_mem' hc₀ hxQ
  have hxy₁ : c₀ * x * c₀⁻¹ * y' = y' * (c₀ * x * c₀⁻¹) := by
    rw [← hc₀y]
    calc c₀ * x * c₀⁻¹ * (c₀ * y * c₀⁻¹) = c₀ * (x * y) * c₀⁻¹ := by group
      _ = c₀ * (y * x) * c₀⁻¹ := by rw [hxy]
      _ = c₀ * y * c₀⁻¹ * (c₀ * x * c₀⁻¹) := by group
  obtain ⟨g₂, hg₂, hg₂x, hg₂y⟩ := exists_conj_three_same I hG hF hw hl₁ hl' hx₁Q hxQ' hyC' hyQ'
    hxy₁ hxy'
  refine ⟨g₂ * c₀, mul_mem hg₂ hc₀, ?_, ?_⟩
  · calc g₂ * c₀ * x * (g₂ * c₀)⁻¹ = g₂ * (c₀ * x * c₀⁻¹) * g₂⁻¹ := by group
      _ = x' := hg₂x
  · calc g₂ * c₀ * y * (g₂ * c₀)⁻¹ = g₂ * (c₀ * y * c₀⁻¹) * g₂⁻¹ := by group
      _ = g₂ * y' * g₂⁻¹ := by rw [hc₀y]
      _ = y' := hg₂y

end S365

end CFSG.Monster.GMS
