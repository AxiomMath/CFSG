module

public import CFSG.Monster.GMS.S365CentBasic
public import CFSG.Monster.GMS.S365CentRootSpec
public import CFSG.Monster.GMS.S365Lines
public import CFSG.Monster.GMS.Facts.Section37
import CFSG.Assembly.Defs
import CFSG.Monster.GMS.Leech.OddPhi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ w : G}

theorem exists_lift_inf
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (L : LeechSystem w) {y : G} (hya : IsConj a y)
    (hyC : y ∈ Subgroup.centralizer ({w} : Set G)) (hyQ : y ∉ leechQ w) {c : Co1}
    (hc : c ∈ Subgroup.centralizer ({L.φ ⟨y, hyC⟩} : Set Co1)) :
    ∃ g : G, ∃ hgC : g ∈ Subgroup.centralizer ({w} : Set G),
      g ∈ Subgroup.centralizer ({y} : Set G) ∧ L.φ ⟨g, hgC⟩ = c := by
  have hI := co1InvolutionFacts
  have hly := isLeechCentralLift_of_isConj I hG hw hyC hya hyQ
  obtain ⟨chat, hchat⟩ := L.φ_surj c
  have hchatC : (chat : G) ∈ Subgroup.centralizer ({w} : Set G) := chat.2
  have hQ : y⁻¹ * ((chat : G) * y * (chat : G)⁻¹) ∈ leechQ w := by
    have hmem : (chat : G) * y * (chat : G)⁻¹ ∈ Subgroup.centralizer ({w} : Set G) :=
      mul_mem (mul_mem hchatC hyC) (inv_mem hchatC)
    refine (L.phi_eq_iff hyC hmem).1 ?_
    have hcomm : c * L.φ ⟨y, hyC⟩ = L.φ ⟨y, hyC⟩ * c := by
      have := hc
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    show L.φ ⟨y, hyC⟩ = L.φ (chat * ⟨y, hyC⟩ * chat⁻¹)
    rw [map_mul, map_mul, map_inv, hchat, hcomm, mul_inv_cancel_right]
  obtain ⟨p, hp, hpc⟩ := L.exists_mul_mem_centralizer_of_lift hI hly hchatC hQ
  have hpC : p ∈ Subgroup.centralizer ({w} : Set G) := L.mem_centralizer hp
  have hgC : p * (chat : G) ∈ Subgroup.centralizer ({w} : Set G) := mul_mem hpC hchatC
  refine ⟨p * (chat : G), hgC, hpc, ?_⟩
  have h1 : L.φ ⟨p * (chat : G), hgC⟩ = L.φ ⟨p, hpC⟩ * L.φ ⟨(chat : G), hchatC⟩ :=
    L.phi_mul hpC hchatC
  rw [h1, (L.φ_ker ⟨p, hpC⟩).2 hp, one_mul]
  exact hchat

theorem ncard_orbit_three
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    (L : LeechSystem w) {x y : G} (hl : IsLineTriple a x y) (hxQ : x ∈ leechQ w)
    (hyC : y ∈ Subgroup.centralizer ({w} : Set G)) (hyQ : y ∉ leechQ w) (hxy : x * y = y * x) :
    {z : G | ∃ g ∈ Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      g * x * g⁻¹ = z}.ncard = 120 := by
  have hI := co1InvolutionFacts
  have hly := isLeechCentralLift_of_isConj I hG hw hyC hl.2.1 hyQ
  have hr : IsCo1TwoA (L.φ ⟨y, hyC⟩) := L.isCo1TwoA_phi hI hly
  have hyw : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.1 hyC
  let Xy : Set G := {z : G | z ∈ leechQ w ∧ IsLineTriple a z y ∧ z * y = y * z}
  have hSX : {z : G | ∃ g ∈ Subgroup.centralizer ({w} : Set G) ⊓
      Subgroup.centralizer ({y} : Set G), g * x * g⁻¹ = z} = Xy := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨hgC, hgy⟩ := Subgroup.mem_inf.1 hg
      have hgyy : g * y * g⁻¹ = y := by
        have := Subgroup.mem_centralizer_singleton_iff.1 hgy
        rw [mul_inv_eq_iff_eq_mul]
        exact this
      refine ⟨L.conj_mem' hgC hxQ, ?_, ?_⟩
      · have := isLineTriple_conj hl g
        rwa [hgyy] at this
      · have := conj_comm (g₀ := g) hxy
        rwa [hgyy] at this
    · rintro ⟨hzQ, hzl, hzy⟩
      obtain ⟨g, hgC, hgx, hgy⟩ := exists_conj_three_same I hG co1RootTransitive hw hl hzl hxQ hzQ
        hyC hyQ hxy hzy
      exact ⟨g, Subgroup.mem_inf.2 ⟨hgC, Subgroup.mem_centralizer_singleton_iff.2 (by
        rw [← mul_inv_eq_iff_eq_mul]; exact hgy)⟩, hgx⟩
  rw [hSX]
  have hV : L.vec '' Xy = {u : Fin 24 → ZMod 2 | u ∈ co1Orbit 0 ∧
      ∃ v, u = v + co1Act (L.φ ⟨y, hyC⟩) v} := by
    ext u
    constructor
    · rintro ⟨z, ⟨hzQ, hzl, hzy⟩, rfl⟩
      exact ⟨(mem_typeSet_zero_of_isConj I hG hw L hzQ hzl.1).2,
        exists_vec_eq_add I hG hw L hzl hzQ hyC hyQ hzy⟩
    · rintro ⟨hu, hv⟩
      have hx0 := mem_typeSet_zero_of_isConj I hG hw L hxQ hl.1
      obtain ⟨c, hc, hcu⟩ := co1RootTransitive _ hr (L.vec x) hx0.2 u hu
        (exists_vec_eq_add I hG hw L hl hxQ hyC hyQ hxy) hv
      obtain ⟨g, hgC, hgy, hgφ⟩ := exists_lift_inf I hG hw L hl.2.1 hyC hyQ hc
      have hmem : g * x * g⁻¹ ∈ Xy := by
        have : g * x * g⁻¹ ∈ {z : G | ∃ g ∈ Subgroup.centralizer ({w} : Set G) ⊓
            Subgroup.centralizer ({y} : Set G), g * x * g⁻¹ = z} :=
          ⟨g, Subgroup.mem_inf.2 ⟨hgC, hgy⟩, rfl⟩
        rwa [hSX] at this
      refine ⟨g * x * g⁻¹, hmem, ?_⟩
      rw [L.vec_conj' hgC hxQ, hgφ]
      exact hcu
  have hinj : Set.InjOn L.vec Xy := by
    rintro z ⟨hzQ, hzl, hzy⟩ z' ⟨hz'Q, hz'l, hz'y⟩ hvec
    rcases L.eq_or_eq_mul_z hzQ hz'Q hvec with h | h
    · exact h
    · exfalso
      have hz'w : z' * w = w * z' :=
        Subgroup.mem_centralizer_singleton_iff.1 (L.mem_centralizer hz'Q)
      have hc : (z' * y) * w = w * (z' * y) := by
        rw [mul_assoc, hyw, ← mul_assoc, hz'w, mul_assoc]
      have hcQ : z' * y ∉ leechQ w := by
        intro hq
        apply hyQ
        have := mul_mem (inv_mem hz'Q) hq
        rwa [inv_mul_cancel_left] at this
      have hB : IsConj z₀ (w * (z' * y)) := (isConj_mul_iff I hG hw hz'l.2.2 hc).2 hcQ
      have e : z * y = w * (z' * y) := by
        rw [h]
        calc z' * w * y = z' * (w * y) := mul_assoc _ _ _
          _ = z' * (y * w) := by rw [hyw]
          _ = z' * y * w := (mul_assoc _ _ _).symm
          _ = w * (z' * y) := hc
      have hB' : IsConj z₀ (z * y) := by rw [e]; exact hB
      exact hG.not_isConj (hzl.2.2.trans hB'.symm)
  rw [← Set.InjOn.ncard_image hinj, hV]
  exact card_V hr

theorem card_eightCent_three
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {x y t : G}
    (hl : IsLineTriple a x y) (he : IsEightExt x y t) (hc : twoBCount z₀ x y t = 3) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G)) = eightCentOrder 3 := by
  obtain ⟨w, hw, hwc, hxw, hyw, hxQ, hyQ⟩ := exists_pivot_three I hG hl he hc
  rw [centralizer_inf_inf_eq_of_mem_cosetSet hwc]
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG hw
  have hyC : y ∈ Subgroup.centralizer ({w} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hyw
  have hxy : x * y = y * x := (isKlein_of_isLineTriple hG.1.1 hl).comm
  have hΓ : Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) =
      tableVOrderU :=
    card_centralizer_inf_of_not_mem_leechQ I.sls I.tableV I.leech hG hw hyC hyQ hl.2.1
  have horb := card_eq_card_inf_mul_ncard_conj
    (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) x
  rw [ncard_orbit_three I hG hw L hl hxQ hyC hyQ hxy, hΓ] at horb
  have hre : Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G) =
      (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) ⊓
        Subgroup.centralizer ({x} : Set G) := by
    ext g
    simp only [Subgroup.mem_inf]
    tauto
  rw [hre]
  have h3 : eightCentOrder 3 = 2 ^ 35 * 3 ^ 4 * 5 * 7 := rfl
  rw [h3]
  have h4 : tableVOrderU = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := rfl
  rw [h4] at horb
  omega

end S365

end CFSG.Monster.GMS
