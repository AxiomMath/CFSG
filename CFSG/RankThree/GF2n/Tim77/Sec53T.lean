module

public import CFSG.RankThree.GF2n.Tim77.Sec53E
public import CFSG.RankThree.GF2n.Tim77.Sec53N
public import CFSG.RankThree.GF2n.Tim77.Sec53Mod
public import CFSG.RankThree.GF2n.Tim77.Sec50
public import CFSG.RankThree.GF2n.Tim77.Sec51

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec53t_mem_normalizer_sup {B C : Subgroup G} {g : G}
    (hB : g ∈ Subgroup.normalizer (B : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hB hC ⊢
  rw [Subgroup.map_sup, hB, hC]

theorem sec53t_conj_mem_iff {N : Subgroup G} {y : G} (hy : y ∈ N) (z : G) :
    z ∈ N ↔ y * z * y⁻¹ ∈ N := by
  constructor
  · intro hz
    exact N.mul_mem (N.mul_mem hy hz) (N.inv_mem hy)
  · intro hz
    have h := N.mul_mem (N.mul_mem (N.inv_mem hy) hz) hy
    rwa [show y⁻¹ * (y * z * y⁻¹) * y = z by group] at h

theorem sec53t_comm_mem {A Ab L : Subgroup G} (hL : L = A ⊓ Subgroup.normalizer (Ab : Set G))
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1)
    (hq : L.relIndex A = 2) {y : G} (hyA : y ∈ Subgroup.normalizer (A : Set G))
    (hyAb : y ∈ Subgroup.normalizer (Ab : Set G)) :
    ∀ x ∈ A, y * x * y⁻¹ * x⁻¹ ∈ L := by
  have hyN : y ∈ Subgroup.normalizer (Ab : Set G) := hyAb
  have hmemL : ∀ z : G, z ∈ L ↔ y * z * y⁻¹ ∈ L := by
    intro z
    rw [hL, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hyA z,
      sec53t_conj_mem_iff (N := Subgroup.normalizer (Ab : Set G)) hyN z]
  intro x hx
  have hyx : y * x * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hyA x).mp hx
  have hxi : x⁻¹ ∈ A := A.inv_mem hx
  by_cases hxL : x ∈ L
  · exact L.mul_mem ((hmemL x).mp hxL) (L.inv_mem hxL)
  · have hyxL : y * x * y⁻¹ ∉ L := fun h => hxL ((hmemL x).mpr h)
    have hxiL : x⁻¹ ∉ L := fun h => hxL (by simpa using L.inv_mem h)
    exact sec53_mul_mem_of_relIndex_two hA hsq hq hyx hxi hyxL hxiL


theorem sec53_of_transvection
    [Finite G]
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2) {y : G}
    (hyA : y ∈ normalizer (A : Set G)) (hyAb : y ∈ normalizer (Abar : Set G))
    (hyL : ∃ l ∈ Section3.A0 A Abar, y * l * y⁻¹ ≠ l)
    (hL2 : ∀ l ∈ Section3.A0 A Abar, ∀ l' ∈ Section3.A0 A Abar, y * l * y⁻¹ * l⁻¹ = 1 ∨
      y * l' * y⁻¹ * l'⁻¹ = 1 ∨ y * l * y⁻¹ * l⁻¹ = y * l' * y⁻¹ * l'⁻¹)
    [((Section3.M A Abar).subgroupOf (Section3.X A Abar)).Normal] :
    Nonempty (↥(Section3.X A Abar) ⧸ (Section3.M A Abar).subgroupOf (Section3.X A Abar) ≃*
      DihedralGroup 3) := by
  have S := h.setup
  have hq1 : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← S.relIndex_Lb]
    exact hq
  have hA : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := fun x hx z hz => S.comm_A hx hz
  have hsqA : ∀ x ∈ A, x * x = 1 := fun x hx => S.sq_A hx
  have hAb : ∀ x ∈ Abar, ∀ z ∈ Abar, x * z = z * x := fun x hx z hz => S.symm.comm_A hx hz
  have hsqAb : ∀ x ∈ Abar, x * x = 1 := fun x hx => S.sq_Ab hx
  have hyA0 : ∀ x ∈ A, y * x * y⁻¹ * x⁻¹ ∈ Section3.A0 A Abar :=
    sec53t_comm_mem S.hL hA hsqA hq1 hyA hyAb
  have hyAb0 : ∀ x ∈ Abar, y * x * y⁻¹ * x⁻¹ ∈ Section3.Abar0 A Abar :=
    sec53t_comm_mem S.hLb hAb hsqAb hq hyAb hyA
  have hyX : y ∈ Subgroup.normalizer ((A ⊔ Abar : Subgroup G) : Set G) :=
    sec53t_mem_normalizer_sup hyA hyAb
  have hyM : ∀ x ∈ A ⊔ Abar, y * x * y⁻¹ * x⁻¹ ∈ Section3.M A Abar := by
    have hnormM : ∀ x ∈ A ⊔ Abar, ∀ m : G, m ∈ Section3.M A Abar ↔
        x * m * x⁻¹ ∈ Section3.M A Abar := fun x hx m =>
      Subgroup.mem_normalizer_iff.mp (S.sup_le_normalizer_M hx) m
    let P : Subgroup G :=
      { carrier := {x | x ∈ A ⊔ Abar ∧ y * x * y⁻¹ * x⁻¹ ∈ Section3.M A Abar}
        mul_mem' := by
          rintro x z ⟨hx, hxM⟩ ⟨hz, hzM⟩
          refine ⟨(A ⊔ Abar).mul_mem hx hz, ?_⟩
          have e : y * (x * z) * y⁻¹ * (x * z)⁻¹ =
              (y * x * y⁻¹ * x⁻¹) * (x * (y * z * y⁻¹ * z⁻¹) * x⁻¹) := by group
          rw [e]
          exact (Section3.M A Abar).mul_mem hxM ((hnormM x hx _).mp hzM)
        one_mem' := ⟨(A ⊔ Abar).one_mem, by simpa using (Section3.M A Abar).one_mem⟩
        inv_mem' := by
          rintro x ⟨hx, hxM⟩
          refine ⟨(A ⊔ Abar).inv_mem hx, ?_⟩
          have e : y * x⁻¹ * y⁻¹ * x⁻¹⁻¹ = x⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
          rw [e]
          exact (hnormM x⁻¹ ((A ⊔ Abar).inv_mem hx) _).mp ((Section3.M A Abar).inv_mem hxM) }
    have hAP : A ≤ P := fun x hx =>
      ⟨Subgroup.mem_sup_left hx, S.hM ▸ Subgroup.mem_sup_left (hyA0 x hx)⟩
    have hAbP : Abar ≤ P := fun x hx =>
      ⟨Subgroup.mem_sup_right hx, S.hM ▸ Subgroup.mem_sup_right (hyAb0 x hx)⟩
    exact fun x hx => (sup_le hAP hAbP hx).2
  obtain ⟨a, ha, haL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have h3 : (a * b) ^ 3 = 1 := sec53_cube_of_inner S hyX hyM hyL hL2 ha haL hb hbL
  haveI : ((Section3.M A Abar).subgroupOf (A ⊔ Abar)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer S.M_le_X).mpr S.sup_le_normalizer_M
  exact sec53_dihedral_three S hq1 ha haL hb hbL h3

theorem sec53t_card_cases [Finite G] {H : Subgroup G} (hH : IsPGroup 2 H) (hne : H ≠ ⊥) :
    Nat.card H = 2 ∨ Nat.card H = 4 ∨ 8 ≤ Nat.card H := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  have h1 : Nat.card H ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  rw [hn] at h1 ⊢
  rcases n with _ | _ | _ | n
  · simp at h1
  · left
    norm_num
  · right
    left
    norm_num
  · right
    right
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n + 1 + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem sec53t_relIndex_inf {A K K' : Subgroup G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1)
    (hKA : K ≤ A) (hK'A : K' ≤ A)
    (hK : K.relIndex A = 2) (hK' : K'.relIndex A = 2) (hne : K ≠ K') :
    (K ⊓ K').relIndex K = 2 := by
  have hnot : ¬ K ≤ K' := by
    intro h
    have e1 := Subgroup.relIndex_mul_relIndex (H := K) (K := K') (L := A) h hK'A
    rw [hK, hK'] at e1
    have h1 : K.relIndex K' = 1 := by omega
    exact hne (le_antisymm h ((Subgroup.relIndex_eq_one (H := K) (K := K')).mp h1))
  obtain ⟨c, hcK, hcK'⟩ : ∃ c ∈ K, c ∉ K' := SetLike.not_le_iff_exists.mp hnot
  have hcA : c ∈ A := hKA hcK
  show ((K ⊓ K').subgroupOf K).index = 2
  refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨c, hcK⟩, ?_, ?_⟩
  · intro h
    exact hcK' (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp h)).2
  · intro d
    by_cases hdK' : (d : G) ∈ K'
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨d.2, hdK'⟩))
    · refine Or.inl (Subgroup.mem_subgroupOf.mpr ?_)
      have hdc : (d : G) * c ∈ K' :=
        sec53_mul_mem_of_relIndex_two hA hsq hK' (hKA d.2) hcA hdK' hcK'
      exact Subgroup.mem_inf.mpr ⟨K.mul_mem d.2 hcK, hdc⟩

theorem sec53t_cube_of_card_two [Finite G] {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) (hL : Nat.card L = 2) {a b : G} (ha : a ∈ A) (haL : a ∉ L)
    (hb : b ∈ Ab) (hbL : b ∉ Lb) : (a * b) ^ 3 = 1 := by
  have hsurj : Function.Surjective
      (fun p : L × Lb => (⟨(p.1 : G) * (p.2 : G), S.mul_mem_M p.1.2 p.2.2⟩ : M)) := by
    intro x
    obtain ⟨l, hl, lb, hlb, hx⟩ := S.exists_mul_of_mem_M x.2
    exact ⟨(⟨l, hl⟩, ⟨lb, hlb⟩), Subtype.ext hx.symm⟩
  have hM4 : Nat.card M ≤ 4 := by
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, S.card_Lb_eq, hL] at h1
    omega
  have hMne : M ≠ ⊥ := fun h => S.ne_bot (eq_bot_iff.mpr (by rw [← h]; exact S.L_le_M))
  have hnorm : a * b ∈ Subgroup.normalizer (M : Set G) :=
    mul_mem (S.A_le_normalizer_M ha) (S.Ab_le_normalizer_M hb)
  exact sec53_orbit_three S ha haL hb hbL (le_refl M) hMne hM4 hnorm

theorem sec53t_transv_hyp {A₀ Z : Subgroup G}
    (hc : ∀ x ∈ A₀, ∀ z ∈ A₀, x * z = z * x) (hsq : ∀ x ∈ A₀, x * x = 1)
    (hZ : Z ≤ A₀) (hZi : Z.relIndex A₀ = 2) {a y : G} (ha2 : a * a = 1)
    (haA₀ : ∀ x ∈ A₀, a * x * a ∈ A₀)
    (hCa : ∀ x ∈ A₀, (a * x * a = x ↔ x ∈ Z))
    (hy : ∀ x ∈ A₀, y * x * y⁻¹ = a * x * a) :
    (∃ l ∈ A₀, y * l * y⁻¹ ≠ l) ∧
    ∀ l ∈ A₀, ∀ l' ∈ A₀, y * l * y⁻¹ * l⁻¹ = 1 ∨ y * l' * y⁻¹ * l'⁻¹ = 1 ∨
      y * l * y⁻¹ * l⁻¹ = y * l' * y⁻¹ * l'⁻¹ := by
  have hnot : ¬ A₀ ≤ Z := by
    intro h
    have h1 : Z.relIndex A₀ = 1 := Subgroup.relIndex_eq_one.mpr h
    omega
  obtain ⟨l₀, hl₀, hl₀Z⟩ : ∃ l ∈ A₀, l ∉ Z := SetLike.not_le_iff_exists.mp hnot
  refine ⟨⟨l₀, hl₀, ?_⟩, ?_⟩
  · rw [hy l₀ hl₀]
    intro h
    exact hl₀Z ((hCa l₀ hl₀).mp h)
  intro l hl l' hl'
  by_cases hlZ : l ∈ Z
  · left
    rw [hy l hl, (hCa l hl).mpr hlZ, mul_inv_cancel]
  by_cases hl'Z : l' ∈ Z
  · right
    left
    rw [hy l' hl', (hCa l' hl').mpr hl'Z, mul_inv_cancel]
  right
  right
  have hll' : l * l' ∈ Z := sec53_mul_mem_of_relIndex_two hc hsq hZi hl hl' hlZ hl'Z
  have hLL : a * (l * l') * a = l * l' := (hCa (l * l') (A₀.mul_mem hl hl')).mpr hll'
  have hu2 : (a * l * a) * (a * l * a) = 1 := hsq _ (haA₀ l hl)
  have hl2 : l * l = 1 := hsq l hl
  have hl'2 : l' * l' = 1 := hsq l' hl'
  have hprod : (a * l * a) * (a * l' * a) = l * l' := by
    calc (a * l * a) * (a * l' * a) = a * l * (a * a) * l' * a := by group
      _ = a * l * l' * a := by rw [ha2, mul_one]
      _ = a * (l * l') * a := by group
      _ = l * l' := hLL
  have key : (a * l * a) * (l * l') = a * l' * a := by
    calc (a * l * a) * (l * l') = (a * l * a) * ((a * l * a) * (a * l' * a)) := by rw [hprod]
      _ = ((a * l * a) * (a * l * a)) * (a * l' * a) := by group
      _ = a * l' * a := by rw [hu2, one_mul]
  rw [hy l hl, hy l' hl', inv_eq_of_mul_eq_one_right hl2, inv_eq_of_mul_eq_one_right hl'2]
  calc a * l * a * l = (a * l * a) * l * (l' * l') := by rw [hl'2, mul_one]
    _ = (a * l * a) * (l * l') * l' := by group
    _ = (a * l' * a) * l' := by rw [key]

theorem sec53t_key {p d e b : G} (hb : b = p * d) (hde : d * e = e * d)
    (hpd : p * d = d * p) (hdd : d * d = 1) : b * e * b * e = p * e * p * e := by
  subst hb
  calc p * d * e * (p * d) * e = p * (d * e) * p * d * e := by group
    _ = p * (e * d) * p * d * e := by rw [hde]
    _ = p * e * (d * p) * d * e := by group
    _ = p * e * (p * d) * d * e := by rw [← hpd]
    _ = p * e * p * (d * d) * e := by group
    _ = p * e * p * e := by rw [hdd, mul_one]

theorem sec53t_eps_mul {t x y : G} (htt : t * t = 1) (hxy : x * y = y * x)
    (hcomm : x * (t * y * t * y) = (t * y * t * y) * x) :
    t * (x * y) * t * (x * y) = (t * x * t * x) * (t * y * t * y) := by
  symm
  calc (t * x * t * x) * (t * y * t * y) = t * x * t * (x * (t * y * t * y)) := by group
    _ = t * x * t * ((t * y * t * y) * x) := by rw [hcomm]
    _ = t * x * (t * t) * y * t * y * x := by group
    _ = t * x * y * t * y * x := by rw [htt, mul_one]
    _ = t * x * y * t * (y * x) := by group
    _ = t * x * y * t * (x * y) := by rw [← hxy]
    _ = t * (x * y) * t * (x * y) := by group

theorem sec53t_card_le_two [Finite G] {Z : Subgroup G} {c d : G}
    (h : ∀ z ∈ Z, z = c ∨ z = d) : Nat.card Z ≤ 2 := by
  have hsub : (Z : Set G) ⊆ ({c, d} : Set G) := by
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact h z hz
  have h1 : Nat.card Z = (Z : Set G).ncard := Nat.card_coe_set_eq (Z : Set G)
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 := Set.ncard_insert_le c ({d} : Set G)
  rw [Set.ncard_singleton] at h3
  omega

theorem sec53t_exists_a0 [Finite G] {A Ab L Lb M : Subgroup G}
    (S : Prop24Setup A Ab L Lb M) (hq : L.relIndex A = 2) (hqb : Lb.relIndex Ab = 2)
    {a : G} {Z : Subgroup G} (hZ : Z ≤ L) (hZi : Z.relIndex L = 2)
    (hCa : ∀ x ∈ L, (a * x * a = x ↔ x ∈ Z)) (h8 : 8 ≤ Nat.card L) :
    ∃ a₀ ∈ L, a₀ ≠ 1 ∧ a * a₀ * a = a₀ ∧ ∀ α ∈ A, ∀ β ∈ Ab,
      a * (α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀)) * a =
        α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀) := by
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => S.comm_A hx hy
  have hsqA : ∀ x ∈ A, x * x = 1 := fun x hx => S.sq_A hx
  have hcommAb : ∀ x ∈ Ab, ∀ y ∈ Ab, x * y = y * x := fun x hx y hy => S.symm.comm_A hx hy
  have hsqAb : ∀ x ∈ Ab, x * x = 1 := fun x hx => S.sq_Ab hx
  have hcommL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
    S.comm_A (S.L_le hx) (S.L_le hy)
  have hsqL : ∀ x ∈ L, x * x = 1 := fun x hx => S.sq_A (S.L_le hx)
  obtain ⟨α₀, hα₀A, hα₀L⟩ : ∃ x ∈ A, x ∉ L :=
    SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨β₀, hβ₀Ab, hβ₀Lb⟩ : ∃ x ∈ Ab, x ∉ Lb :=
    SetLike.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hεLb : ∀ x ∈ L, β₀ * x * β₀ * x ∈ Lb := by
    intro x hx
    have h := S.commutator_mem_Lb hβ₀Ab hx
    rwa [inv_eq_of_mul_eq_one_right (S.sq_Ab hβ₀Ab),
      inv_eq_of_mul_eq_one_right (hsqL x hx)] at h
  have hφL : ∀ x ∈ L, α₀ * (β₀ * x * β₀ * x) * α₀ * (β₀ * x * β₀ * x) ∈ L := by
    intro x hx
    have h := S.commutator_mem_L hα₀A (hεLb x hx)
    rwa [inv_eq_of_mul_eq_one_right (S.sq_A hα₀A),
      inv_eq_of_mul_eq_one_right (S.sq_Ab (S.Lb_le (hεLb x hx)))] at h
  have hC1 : ∀ β ∈ Ab, ∀ x ∈ L, β * x * β * x = 1 ∨ β * x * β * x = β₀ * x * β₀ * x := by
    intro β hβ x hx
    by_cases hβL : β ∈ Lb
    · left
      calc β * x * β * x = β * (x * β) * x := by group
        _ = β * (β * x) * x := by rw [S.comm_L_Lb hx hβL]
        _ = (β * β) * (x * x) := by group
        _ = 1 := by rw [S.sq_Ab hβ, hsqL x hx, one_mul]
    · right
      have he₀ : β₀ * β ∈ Lb :=
        sec53_mul_mem_of_relIndex_two hcommAb hsqAb hqb hβ₀Ab hβ hβ₀Lb hβL
      exact sec53t_key (p := β₀) (d := β₀ * β) (e := x) (b := β)
        (by rw [← mul_assoc, S.sq_Ab hβ₀Ab, one_mul])
        (S.comm_L_Lb hx he₀).symm (hcommAb β₀ hβ₀Ab (β₀ * β) (Ab.mul_mem hβ₀Ab hβ))
        (S.sq_Ab (S.Lb_le he₀))
  have hC2 : ∀ α ∈ A, ∀ e ∈ Lb, α * e * α * e = 1 ∨ α * e * α * e = α₀ * e * α₀ * e := by
    intro α hα e he
    by_cases hαL : α ∈ L
    · left
      calc α * e * α * e = α * (e * α) * e := by group
        _ = α * (α * e) * e := by rw [S.comm_L_Lb hαL he]
        _ = (α * α) * (e * e) := by group
        _ = 1 := by rw [hsqA α hα, S.sq_Ab (S.Lb_le he), one_mul]
    · right
      have hd : α₀ * α ∈ L := sec53_mul_mem_of_relIndex_two hcommA hsqA hq hα₀A hα hα₀L hαL
      exact sec53t_key (p := α₀) (d := α₀ * α) (e := e) (b := α)
        (by rw [← mul_assoc, S.sq_A hα₀A, one_mul])
        (S.comm_L_Lb hd he) (hcommA α₀ hα₀A (α₀ * α) (A.mul_mem hα₀A hα))
        (hsqL _ hd)
  have hC3 : ∀ α ∈ A, ∀ β ∈ Ab, ∀ x ∈ L,
      α * (β * x * β * x) * α * (β * x * β * x) = 1 ∨
      α * (β * x * β * x) * α * (β * x * β * x) =
        α₀ * (β₀ * x * β₀ * x) * α₀ * (β₀ * x * β₀ * x) := by
    intro α hα β hβ x hx
    rcases hC1 β hβ x hx with h | h
    · rw [h]
      left
      simp only [mul_one]
      exact hsqA α hα
    · rw [h]
      exact hC2 α hα _ (hεLb x hx)
  have hεmul : ∀ x ∈ L, ∀ x' ∈ L,
      β₀ * (x * x') * β₀ * (x * x') = (β₀ * x * β₀ * x) * (β₀ * x' * β₀ * x') :=
    fun x hx x' hx' =>
      sec53t_eps_mul (S.sq_Ab hβ₀Ab) (hcommL x hx x' hx') (S.comm_L_Lb hx (hεLb x' hx'))
  have hφmul : ∀ x ∈ L, ∀ x' ∈ L,
      α₀ * (β₀ * (x * x') * β₀ * (x * x')) * α₀ * (β₀ * (x * x') * β₀ * (x * x')) =
        (α₀ * (β₀ * x * β₀ * x) * α₀ * (β₀ * x * β₀ * x)) *
          (α₀ * (β₀ * x' * β₀ * x') * α₀ * (β₀ * x' * β₀ * x')) := by
    intro x hx x' hx'
    rw [hεmul x hx x' hx']
    exact sec53t_eps_mul (S.sq_A hα₀A)
      (hcommAb _ (S.Lb_le (hεLb x hx)) _ (S.Lb_le (hεLb x' hx')))
      (S.comm_L_Lb (hφL x' hx') (hεLb x hx)).symm
  have hfin : ∀ a₀ ∈ Z, a₀ ≠ 1 → α₀ * (β₀ * a₀ * β₀ * a₀) * α₀ * (β₀ * a₀ * β₀ * a₀) ∈ Z →
      a₀ ∈ L ∧ a₀ ≠ 1 ∧ a * a₀ * a = a₀ ∧ ∀ α ∈ A, ∀ β ∈ Ab,
        a * (α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀)) * a =
          α * (β * a₀ * β * a₀) * α * (β * a₀ * β * a₀) := by
    intro a₀ ha₀Z ha₀1 hφZ
    have ha₀L : a₀ ∈ L := hZ ha₀Z
    refine ⟨ha₀L, ha₀1, (hCa a₀ ha₀L).mpr ha₀Z, ?_⟩
    intro α hα β hβ
    rcases hC3 α hα β hβ a₀ ha₀L with h | h
    · rw [h]
      exact (hCa 1 L.one_mem).mpr Z.one_mem
    · rw [h]
      exact (hCa _ (hφL a₀ ha₀L)).mpr hφZ
  have hZc : 4 ≤ Nat.card Z := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := L)
    rw [hZi, inf_eq_left.mpr hZ] at h
    omega
  obtain ⟨c₀, hc₀, hc₀1⟩ : ∃ c₀ ∈ Z, c₀ ≠ 1 := by
    by_contra h
    have := sec53t_card_le_two (Z := Z) (c := 1) (d := 1) (fun z hz => by
      by_contra hne
      exact h ⟨z, hz, fun h1 => hne (Or.inl h1)⟩)
    omega
  obtain ⟨z₁, hz₁, hz₁1, z₂, hz₂, hz₂1, hne⟩ :
      ∃ z₁ ∈ Z, z₁ ≠ 1 ∧ ∃ z₂ ∈ Z, z₂ ≠ 1 ∧ z₁ ≠ z₂ := by
    by_contra h
    have := sec53t_card_le_two (Z := Z) (c := 1) (d := c₀) (fun z hz => by
      by_cases hz1 : z = 1
      · exact Or.inl hz1
      · right
        by_contra hzc
        exact h ⟨z, hz, hz1, c₀, hc₀, hc₀1, hzc⟩)
    omega
  by_cases h1 : α₀ * (β₀ * z₁ * β₀ * z₁) * α₀ * (β₀ * z₁ * β₀ * z₁) ∈ Z
  · exact ⟨z₁, hfin z₁ hz₁ hz₁1 h1⟩
  by_cases h2 : α₀ * (β₀ * z₂ * β₀ * z₂) * α₀ * (β₀ * z₂ * β₀ * z₂) ∈ Z
  · exact ⟨z₂, hfin z₂ hz₂ hz₂1 h2⟩
  have hprod : α₀ * (β₀ * z₁ * β₀ * z₁) * α₀ * (β₀ * z₁ * β₀ * z₁) *
      (α₀ * (β₀ * z₂ * β₀ * z₂) * α₀ * (β₀ * z₂ * β₀ * z₂)) ∈ Z :=
    sec53_mul_mem_of_relIndex_two hcommL hsqL hZi (hφL z₁ (hZ hz₁)) (hφL z₂ (hZ hz₂)) h1 h2
  have hz12 : z₁ * z₂ ≠ 1 := by
    intro h
    apply hne
    have h' : z₁ * z₂ = z₁ * z₁ := h.trans (hsqL z₁ (hZ hz₁)).symm
    exact (mul_left_cancel h').symm
  have hφ12 : α₀ * (β₀ * (z₁ * z₂) * β₀ * (z₁ * z₂)) * α₀ * (β₀ * (z₁ * z₂) * β₀ * (z₁ * z₂))
      ∈ Z := by
    rw [hφmul z₁ (hZ hz₁) z₂ (hZ hz₂)]
    exact hprod
  exact ⟨z₁ * z₂, hfin (z₁ * z₂) (Z.mul_mem hz₁ hz₂) hz12 hφ12⟩

theorem sec53t_hyperplane_elt [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hq : Section3.q A Abar = 2) {g : G} (hg : g ∈ normalizer (A : Set G))
    (hne : conjSubgroup g (Section3.A0 A Abar) ≠ Section3.A0 A Abar)
    (h2 : Nat.card (Section3.A0 A Abar) ≠ 2) :
    ∃ (F : Subgroup G) (a : G), IsPGroup 2 F ∧ F ≤ normalizer (Section3.A0 A Abar : Set G) ∧
      a ∈ F ∧ a ∈ normalizer (A : Set G) ∧ a * a = 1 ∧
      (∀ x ∈ A, a * x * a * x⁻¹ ∈ Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar)) ∧
      (∀ x ∈ Section3.A0 A Abar,
        (a * x * a = x ↔ x ∈ Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar))) := by
  obtain ⟨F, hF1, hF2, hF3, hF4, hF5⟩ := sec53_hyperplane_sec3 h hq hg hne
  have hFne : F ≠ ⊥ := fun e => h2 (hF5.mp e)
  obtain ⟨⟨a, haF⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
  have ha1 : a ≠ 1 := fun e => ha1' (Subtype.ext e)
  have hgA : conjSubgroup g A = A := conjSubgroup_eq_self_iff.mpr hg
  have h' : Sec3Ctx A (conjSubgroup g Abar) (conjSubgroup g S₀) (conjSubgroup g B) := by
    have hc := h.conj g
    rwa [hgA] at hc
  have hA0 : Section3.A0 A (conjSubgroup g Abar) = conjSubgroup g (Section3.A0 A Abar) := by
    have hc := section3_A0_conj A Abar g
    rwa [hgA] at hc
  have hB0 : Section3.Abar0 A (conjSubgroup g Abar) =
      conjSubgroup g (Section3.Abar0 A Abar) := by
    have hc := section3_Abar0_conj A Abar g
    rwa [hgA] at hc
  have S' := h'.setup
  have haLb : a ∈ Section3.Abar0 A (conjSubgroup g Abar) := by
    rw [hB0]
    exact hF1 haF
  have ha2 : a * a = 1 := S'.sq_Ab (S'.Lb_le haLb)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  refine ⟨F, a, ?_, hF4, haF, (S'.mem_Lb.mp haLb).2, ha2, ?_, ?_⟩
  · refine notation_isPGroup_two_of_le S'.elem_Ab (fun x hx => S'.Lb_le ?_)
    rw [hB0]
    exact hF1 hx
  · intro x hx
    have hc := hF3 a haF x hx
    have e : a * x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by
      calc a * x * a * x⁻¹ = a * x * a⁻¹ * x⁻¹ := by rw [hai]
        _ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact (Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar)).inv_mem hc
  · intro x hx
    have hxA : x ∈ A := h.setup.L_le hx
    constructor
    · intro hxa
      refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
      by_contra hxL
      have hxL' : x ∉ Section3.A0 A (conjSubgroup g Abar) := by
        rwa [hA0]
      have hcomm : x * a = a * x := by
        calc x * a = (a * x * a) * a := by rw [hxa]
          _ = a * x * (a * a) := by group
          _ = a * x := by rw [ha2, mul_one]
      have hinj := S'.commutator_injective hxA hxL'
      have hmem : (⟨a, haLb⟩ : ↥(Section3.Abar0 A (conjSubgroup g Abar))) = 1 := by
        apply hinj
        apply Subtype.ext
        show x * a * x⁻¹ * a⁻¹ = x * (1 : G) * x⁻¹ * (1 : G)⁻¹
        rw [hcomm]
        group
      exact ha1 (congrArg Subtype.val hmem)
    · intro hxZ
      have hxL' : x ∈ Section3.A0 A (conjSubgroup g Abar) := by
        rw [hA0]
        exact (Subgroup.mem_inf.mp hxZ).2
      have hcomm := S'.comm_L_Lb hxL' haLb
      calc a * x * a = x * a * a := by rw [hcomm]
        _ = x := by rw [mul_assoc, ha2, mul_one]

theorem sec53t_conj_data {A A₀ Z : Subgroup G} {a n : G}
    (hnA : n ∈ normalizer (A : Set G)) (hnA0 : n ∈ normalizer (A₀ : Set G))
    (haN : a ∈ normalizer (A : Set G)) (haN0 : a ∈ normalizer (A₀ : Set G)) (ha2 : a * a = 1)
    (hZ : Z ≤ A₀) (hZi : Z.relIndex A₀ = 2)
    (haZ : ∀ x ∈ A, a * x * a * x⁻¹ ∈ Z) (hCa : ∀ x ∈ A₀, (a * x * a = x ↔ x ∈ Z)) :
    n⁻¹ * a * n ∈ normalizer (A : Set G) ∧ n⁻¹ * a * n ∈ normalizer (A₀ : Set G) ∧
      (n⁻¹ * a * n) * (n⁻¹ * a * n) = 1 ∧ conjSubgroup n⁻¹ Z ≤ A₀ ∧
      (conjSubgroup n⁻¹ Z).relIndex A₀ = 2 ∧
      (∀ x ∈ A, (n⁻¹ * a * n) * x * (n⁻¹ * a * n) * x⁻¹ ∈ conjSubgroup n⁻¹ Z) ∧
      (∀ x ∈ A₀, ((n⁻¹ * a * n) * x * (n⁻¹ * a * n) = x ↔ x ∈ conjSubgroup n⁻¹ Z)) := by
  have hn_inv_A : n⁻¹ ∈ normalizer (A : Set G) := (normalizer (A : Set G)).inv_mem hnA
  have hn_inv_A0 : n⁻¹ ∈ normalizer (A₀ : Set G) := (normalizer (A₀ : Set G)).inv_mem hnA0
  have hA0n : conjSubgroup n⁻¹ A₀ = A₀ := conjSubgroup_eq_self_iff.mpr hn_inv_A0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (mul_mem hn_inv_A haN) hnA
  · exact mul_mem (mul_mem hn_inv_A0 haN0) hnA0
  · calc n⁻¹ * a * n * (n⁻¹ * a * n) = n⁻¹ * (a * a) * n := by group
      _ = 1 := by rw [ha2]; group
  · calc conjSubgroup n⁻¹ Z ≤ conjSubgroup n⁻¹ A₀ := (conjSubgroup_le_conj_iff n⁻¹).2 hZ
      _ = A₀ := hA0n
  · have h1 := relIndex_conjSubgroup_t77 n⁻¹ Z A₀
    rw [hA0n] at h1
    rw [h1]
    exact hZi
  · intro x hx
    have hx' : n * x * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hnA x).mp hx
    have h1 := haZ _ hx'
    rw [mem_conjSubgroup_exists_t77]
    refine ⟨a * (n * x * n⁻¹) * a * (n * x * n⁻¹)⁻¹, h1, ?_⟩
    group
  · intro x hx
    have hx' : n * x * n⁻¹ ∈ A₀ := (Subgroup.mem_normalizer_iff.mp hnA0 x).mp hx
    have h1 := hCa _ hx'
    rw [mem_conjSubgroup]
    constructor
    · intro he
      have h2 : a * (n * x * n⁻¹) * a = n * x * n⁻¹ := by
        calc a * (n * x * n⁻¹) * a = n * (n⁻¹ * a * n * x * (n⁻¹ * a * n)) * n⁻¹ := by group
          _ = n * x * n⁻¹ := by rw [he]
      simpa using h1.mp h2
    · intro hm
      have hm' : n * x * n⁻¹ ∈ Z := by simpa using hm
      have h2 := h1.mpr hm'
      calc n⁻¹ * a * n * x * (n⁻¹ * a * n) = n⁻¹ * (a * (n * x * n⁻¹) * a) * n := by group
        _ = x := by rw [h2]; group

theorem sec53t_comm0
    [Finite G]
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (hnc : ¬ Sec4A0LeCenterH A Abar) {F : Subgroup G} (hF2 : IsPGroup 2 F)
    (hFN : F ≤ normalizer (Section3.A0 A Abar : Set G)) :
    ∃ n ∈ normalizer (Section3.A0 A Abar : Set G), ∀ a ∈ F, ∀ x ∈ Section3.Abar0 A Abar,
      ∀ y ∈ conjSubgroup (n⁻¹ * a * n) (Section3.Abar0 A Abar), x * y = y * x := by
  have S := h.setup
  obtain ⟨Q, hFQ⟩ := notation_exists_sylow_le (A := Section3.A0 A Abar) hF2 hFN
  obtain ⟨hS2, hSN, hSmax⟩ := notation_sylow_map_max (A := Section3.A0 A Abar) Q
  have hAb0N : Section3.Abar0 A Abar ≤ normalizer (Section3.A0 A Abar : Set G) :=
    le_normalizer_of_comm fun x hx y hy => (S.comm_L_Lb hy hx).symm
  have hAb02 : IsPGroup 2 (Section3.Abar0 A Abar) :=
    notation_isPGroup_two_of_le S.elem_Ab S.Lb_le
  obtain ⟨n, hn, hnS⟩ := notation_exists_conj_le_sylow hAb02 hAb0N Q
  refine ⟨n, hn, ?_⟩
  intro a haF
  have hn_inv : n⁻¹ ∈ normalizer (Section3.A0 A Abar : Set G) :=
    (normalizer (Section3.A0 A Abar : Set G)).inv_mem hn
  have hconjN : conjSubgroup n⁻¹ (normalizer (Section3.A0 A Abar : Set G)) =
      normalizer (Section3.A0 A Abar : Set G) := by
    rw [conjSubgroup_map_normalizer, conjSubgroup_eq_self_iff.mpr hn_inv]
  obtain ⟨hS''2, hS''max⟩ := isPGroup_maximal_conj_t77 n⁻¹
    ((Q : Subgroup ↥(normalizer (Section3.A0 A Abar : Set G))).map
      (normalizer (Section3.A0 A Abar : Set G)).subtype) hS2
    (normalizer (Section3.A0 A Abar : Set G)) hSmax
  rw [hconjN] at hS''max
  have hS''N : conjSubgroup n⁻¹ ((Q : Subgroup ↥(normalizer (Section3.A0 A Abar : Set G))).map
      (normalizer (Section3.A0 A Abar : Set G)).subtype) ≤
        normalizer (Section3.A0 A Abar : Set G) := by
    have h1 := (conjSubgroup_le_conj_iff n⁻¹).2 hSN
    rwa [hconjN] at h1
  have hAb0S : Section3.Abar0 A Abar ≤ conjSubgroup n⁻¹
      ((Q : Subgroup ↥(normalizer (Section3.A0 A Abar : Set G))).map
        (normalizer (Section3.A0 A Abar : Set G)).subtype) := by
    intro x hx
    rw [mem_conjSubgroup]
    simpa using hnS x hx
  have hE := sec51_holds G A Abar S₀ B h hq hnc _ hS''2 hS''N hS''max hAb0S
  have haS : n⁻¹ * a * n ∈ conjSubgroup n⁻¹
      ((Q : Subgroup ↥(normalizer (Section3.A0 A Abar : Set G))).map
        (normalizer (Section3.A0 A Abar : Set G)).subtype) := by
    rw [mem_conjSubgroup]
    have e : n⁻¹⁻¹ * (n⁻¹ * a * n) * n⁻¹ = a := by group
    rw [e]
    exact hFQ haF
  intro x hx y hy
  have hxE : x ∈ ⨆ k ∈ conjSubgroup n⁻¹
      ((Q : Subgroup ↥(normalizer (Section3.A0 A Abar : Set G))).map
        (normalizer (Section3.A0 A Abar : Set G)).subtype),
      conjSubgroup k (Section3.Abar0 A Abar) :=
    Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem (one_mem _)
      (by rw [conjSubgroup_one]; exact hx))
  have hyE : y ∈ ⨆ k ∈ conjSubgroup n⁻¹
      ((Q : Subgroup ↥(normalizer (Section3.A0 A Abar : Set G))).map
        (normalizer (Section3.A0 A Abar : Set G)).subtype),
      conjSubgroup k (Section3.Abar0 A Abar) :=
    Subgroup.mem_iSup_of_mem (n⁻¹ * a * n) (Subgroup.mem_iSup_of_mem haS hy)
  exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hxE⟩ ⟨y, hyE⟩)

theorem sec53t_big
    [Finite G]
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2) {a : G}
    (haN : a ∈ normalizer (A : Set G)) (haN0 : a ∈ normalizer (Section3.A0 A Abar : Set G))
    (ha2 : a * a = 1) {Z : Subgroup G} (hZ : Z ≤ Section3.A0 A Abar)
    (hZi : Z.relIndex (Section3.A0 A Abar) = 2)
    (haZ : ∀ x ∈ A, a * x * a * x⁻¹ ∈ Z)
    (hCa : ∀ x ∈ Section3.A0 A Abar, (a * x * a = x ↔ x ∈ Z))
    (h8 : 8 ≤ Nat.card (Section3.A0 A Abar))
    (hcomm0 : ∀ x ∈ Section3.Abar0 A Abar, ∀ y ∈ conjSubgroup a (Section3.Abar0 A Abar),
      x * y = y * x)
    [((Section3.M A Abar).subgroupOf (Section3.X A Abar)).Normal] :
    Nonempty (↥(Section3.X A Abar) ⧸ (Section3.M A Abar).subgroupOf (Section3.X A Abar) ≃*
      DihedralGroup 3) := by
  have S := h.setup
  have hq1 : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← S.relIndex_Lb]
    exact hq
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hc : ∀ x ∈ Section3.A0 A Abar, ∀ z ∈ Section3.A0 A Abar, x * z = z * x :=
    fun x hx z hz => S.comm_A (S.L_le hx) (S.L_le hz)
  have hsq : ∀ x ∈ Section3.A0 A Abar, x * x = 1 := fun x hx => S.sq_A (S.L_le hx)
  have haA₀ : ∀ x ∈ Section3.A0 A Abar, a * x * a ∈ Section3.A0 A Abar := by
    intro x hx
    have h1 := (Subgroup.mem_normalizer_iff.mp haN0 x).mp hx
    rwa [hai] at h1
  have key : ∀ y : G, y ∈ normalizer (A : Set G) → y ∈ normalizer (Abar : Set G) →
      (∀ x ∈ A, y * x * y⁻¹ = a * x * a⁻¹) →
      Nonempty (↥(Section3.X A Abar) ⧸ (Section3.M A Abar).subgroupOf (Section3.X A Abar) ≃*
        DihedralGroup 3) := by
    intro y hyA hyAb hy
    obtain ⟨hyL, hL2⟩ := sec53t_transv_hyp hc hsq hZ hZi ha2 haA₀ hCa
      (fun x hx => by rw [hy x (S.L_le hx), hai])
    exact sec53_of_transvection h hq hyA hyAb hyL hL2
  by_cases haAb : a ∈ normalizer (Abar : Set G)
  · exact key a haN haAb (fun x _ => rfl)
  by_cases hcomm : ∀ x ∈ Abar, ∀ y ∈ conjSubgroup a Abar, x * y = y * x
  · exfalso
    have hne : conjSubgroup a Abar ≠ Abar := fun e => haAb (conjSubgroup_eq_self_iff.mp e)
    obtain ⟨a₀, ha₀, ha₀1, ha₀a, hκ⟩ := sec53t_exists_a0 S hq1 hq hZ hZi hCa h8
    exact sec53_elem_contra h hq haN haN0 ha2 hne hcomm ha₀ ha₀1 ha₀a hκ
  · obtain ⟨y, hyA, hyAb, hy⟩ := sec53_nonelem h hq haN haN0 ha2 hZ hZi haZ hCa h8 hcomm0 hcomm
    exact key y hyA hyAb hy

@[expose] def Tim77Sec53FourStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A Abar S₀ B : Subgroup G), Sec3Ctx A Abar S₀ B →
    Section3.q A Abar = 2 → ¬ Sec4A0LeCenterH A Abar → Nat.card (Section3.A0 A Abar) = 4 →
    ∀ [((Section3.M A Abar).subgroupOf (Section3.X A Abar)).Normal],
      Nonempty (↥(Section3.X A Abar) ⧸ (Section3.M A Abar).subgroupOf (Section3.X A Abar) ≃*
        DihedralGroup 3)

theorem sec53_of_four
    (h4 : Tim77Sec53FourStatement) : Tim77Sec53Statement := by
  intro G _ _ A Abar S₀ B h hq hnc _inst
  have S := h.setup
  have hq1 : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← S.relIndex_Lb]
    exact hq
  have hA0p : IsPGroup 2 (Section3.A0 A Abar) :=
    notation_isPGroup_two_of_le h.hyp.elemAbelian S.L_le
  haveI hN : ((Section3.M A Abar).subgroupOf (A ⊔ Abar)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer S.M_le_X).mpr S.sup_le_normalizer_M
  obtain ⟨a, ha, haL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  rcases sec53t_card_cases hA0p h.a0_ne_bot with h2 | h4' | h8
  · exact sec53_dihedral_three S hq1 ha haL hb hbL (sec53t_cube_of_card_two S h2 ha haL hb hbL)
  · exact h4 G A Abar S₀ B h hq hnc h4'
  · obtain ⟨g, hg, hgn⟩ := tim77Sec50_holds G A Abar S₀ B h hq hnc
    have hne : conjSubgroup g (Section3.A0 A Abar) ≠ Section3.A0 A Abar :=
      fun e => hgn (conjSubgroup_eq_self_iff.mp e)
    have hgA : conjSubgroup g A = A := conjSubgroup_eq_self_iff.mpr hg
    have hq2 : (conjSubgroup g (Section3.A0 A Abar)).relIndex A = 2 := by
      have hc := relIndex_conjSubgroup_t77 g (Section3.A0 A Abar) A
      rw [hgA] at hc
      rw [hc]
      exact hq1
    have hq2A : conjSubgroup g (Section3.A0 A Abar) ≤ A := by
      calc conjSubgroup g (Section3.A0 A Abar) ≤ conjSubgroup g A :=
            (conjSubgroup_le_conj_iff g).2 S.L_le
        _ = A := hgA
    have hZi : (Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar)).relIndex
        (Section3.A0 A Abar) = 2 :=
      sec53t_relIndex_inf (fun x hx y hy => S.comm_A hx hy) (fun x hx => S.sq_A hx) S.L_le hq2A
        hq1 hq2 hne.symm
    obtain ⟨F, a, hF2, hFN, haF, haN, ha2, haZ, hCa⟩ :=
      sec53t_hyperplane_elt h hq hg hne (by omega)
    obtain ⟨n, hn, hcomm⟩ := sec53t_comm0 h hq hnc hF2 hFN
    have hnA : n ∈ normalizer (A : Set G) := sec51_normalizer_le h.hyp.ti S.L_le S.ne_bot hn
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ :=
      sec53t_conj_data hnA hn haN (hFN haF) ha2 inf_le_left hZi haZ hCa
    exact sec53t_big h hq k1 k2 k3 k4 k5 k6 k7 h8 (hcomm a haF)

end CFSG.RankThree.GF2n.Tim77
