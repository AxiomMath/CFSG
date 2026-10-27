module

public import CFSG.LocalAnalysis.StandardType.GGE6DepPairBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepNoncyclicInf
public import CFSG.LocalAnalysis.StandardType.GGE6DepInfCentralizerUnique

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open CFSG.LocalAnalysis.ComponentInitial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggCorootPt_of_orth_left {p : ℕ} (hp : p.Prime) {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {a b : ↥Bs} (h : GGCorootOrth p A a b) : GGCorootPt p A a := by
  obtain ⟨_, φ, hφA, _, _, hφrefl, hφc, _⟩ := h
  refine ⟨?_, φ, hφA, hφrefl, hφc⟩
  rintro rfl
  have hfix : ∀ x : ↥Bs, φ x = x := by
    intro x
    have hx := hφc x
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hx
    exact mul_inv_eq_one.mp hx
  have hcard : Nat.card {x : ↥Bs // φ x = x} = Nat.card ↥Bs :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (fun x : ↥Bs => hfix x))
  haveI : Nonempty ↥Bs := ⟨1⟩
  have hp1 : p = 1 := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := ↥Bs))
    calc Nat.card ↥Bs * p = Nat.card {x : ↥Bs // φ x = x} * p := by rw [hcard]
      _ = Nat.card ↥Bs := hφrefl.2
      _ = Nat.card ↥Bs * 1 := by rw [mul_one]
  have hp2 : 2 ≤ p := hp.two_le
  omega

private theorem gg6C_centralizer_union (s t : Set G) :
    Subgroup.centralizer (s ∪ t) = Subgroup.centralizer s ⊓ Subgroup.centralizer t := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_union, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨hs, ht⟩ x (hx | hx)
    · exact hs x hx
    · exact ht x hx

private theorem gg6C_centralizer_pair (a b : G) :
    Subgroup.centralizer ({a, b} : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  rw [show ({a, b} : Set G) = {a} ∪ {b} from by
      ext x <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] <;> tauto,
    gg6C_centralizer_union]

private theorem gg6C_centralizer_pair_eq (a b : G) :
    Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({a} : Set G) =
      Subgroup.centralizer ({a, b} : Set G) := by
  rw [gg6C_centralizer_pair a b, inf_comm]

private theorem gg6C_centralizer_triple₁ (a b c : G) :
    Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b, c} : Set G) =
      Subgroup.centralizer ({a, b, c} : Set G) := by
  rw [gg6C_centralizer_pair b c,
    show ({a, b, c} : Set G) = {a} ∪ ({b} ∪ {c}) from by
      ext x <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] <;> tauto,
    gg6C_centralizer_union, gg6C_centralizer_union]

private theorem gg6C_centralizer_triple₂ (a b c : G) :
    Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({a, b} : Set G) =
      Subgroup.centralizer ({a, b, c} : Set G) := by
  rw [gg6C_centralizer_pair a b,
    show ({a, b, c} : Set G) = ({a, b} : Set G) ∪ {c} from by
      ext x <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union] <;> tauto,
    gg6C_centralizer_union, gg6C_centralizer_pair a b, inf_comm]

private theorem gg6C_map_conj_centralizer_pair (g a b : G) :
    (Subgroup.centralizer ({a, b} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * a * g⁻¹, g * b * g⁻¹} : Set G) := by
  rw [gg6C_centralizer_pair a b, gg6C_centralizer_pair (g * a * g⁻¹) (g * b * g⁻¹),
    Subgroup.map_inf (Subgroup.centralizer ({a} : Set G))
      (Subgroup.centralizer ({b} : Set G)) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective,
    map_conj_centralizer_singleton g a, map_conj_centralizer_singleton g b]

private theorem gg6C_conj_unique {C D : Subgroup G} (hD : IsComponentOf D C)
    (huniq : ∀ D' : Subgroup G, IsComponentOf D' C → D' = D) (g : G) :
    IsComponentOf (D.map (MulAut.conj g).toMonoidHom) (C.map (MulAut.conj g).toMonoidHom) ∧
      ∀ D' : Subgroup G,
        IsComponentOf D' (C.map (MulAut.conj g).toMonoidHom) →
          D' = D.map (MulAut.conj g).toMonoidHom := by
  refine ⟨CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hD g, ?_⟩
  intro D' hD'
  have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hmap : (C.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = C := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hD'' : IsComponentOf (D'.map (MulAut.conj g⁻¹).toMonoidHom) C := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hD' g⁻¹
    rwa [hmap] at h
  have heq : D'.map (MulAut.conj g⁻¹).toMonoidHom = D := huniq _ hD''
  have hcomp' : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hmap' : (D'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = D' := by
    rw [Subgroup.map_map, hcomp', Subgroup.map_id]
  calc D' = (D'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := hmap'.symm
    _ = D.map (MulAut.conj g).toMonoidHom := by rw [heq]

private theorem gg6C_noncentral {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L)) {z : G} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hzp : z ^ p = 1) : ∃ m ∈ L, m * z ≠ z * m := by
  by_contra h
  push Not at h
  let zL : ↥L := ⟨z, hzL⟩
  have hzLp : zL ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mk, Subgroup.coe_one, hzp]
  have hdvd : orderOf zL ∣ p := orderOf_dvd_of_pow_eq_one hzLp
  have horder : orderOf zL = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf zL) hdvd with h1 | hp'
    · exact absurd (Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h1)) hz1
    · exact hp'
  have hcen : zL ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (h (m : G) m.2)
  exact hZ (horder ▸ Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hcen)

private theorem gg6C_noncentral_conj {z m : G} (g : G) (hm : m * z ≠ z * m) :
    (g * m * g⁻¹) * (g * z * g⁻¹) ≠ (g * z * g⁻¹) * (g * m * g⁻¹) := by
  intro heq
  apply hm
  have h := congrArg (fun t => g⁻¹ * t * g) heq
  have h1 : g⁻¹ * ((g * m * g⁻¹) * (g * z * g⁻¹)) * g = m * z := by group
  have h2 : g⁻¹ * ((g * z * g⁻¹) * (g * m * g⁻¹)) * g = z * m := by group
  rw [h1, h2] at h
  exact h

private theorem gg6C_commutator_eq_self {N : Subgroup G} (hN : CFSG.Assembly.IsQuasisimple ↥N) :
    ⁅N, N⁆ = N := by
  haveI : Group.IsPerfect ↥N := ⟨hN.1⟩
  exact Subgroup.commutator_eq_self

private theorem gg6C_not_cyclic_of_exponent_three {H : Type*} [Group H] [Finite H]
    (hexp : ∀ x : H, x ^ 3 = 1) (hcard : 3 ^ 3 ≤ Nat.card H) : ¬ IsCyclic H := by
  intro hcyc
  obtain ⟨z, hz⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have hcard' : Nat.card H = orderOf z :=
    (orderOf_eq_card_of_forall_mem_zpowers (fun x => by rw [hz]; exact Subgroup.mem_top x)).symm
  have hdvd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp z)
  have hle : orderOf z ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  have h27 : 27 ≤ Nat.card H := by norm_num at hcard ⊢; exact hcard
  omega

private theorem gg6C_dvd_card_of_map_subtype {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    {U : Subgroup ↥Bs} (hUcard : 3 ^ 3 ≤ Nat.card U) :
    3 ∣ Nat.card ↥(U.map Bs.subtype) := by
  have hcard : Nat.card ↥(U.map Bs.subtype) = Nat.card ↥U :=
    Subgroup.card_map_of_injective Bs.subtype_injective
  have hne : U.map Bs.subtype ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    have h27 : 27 ≤ Nat.card U := by norm_num at hUcard ⊢; exact hUcard
    omega
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have huG1 : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huG3 : (u : G) ^ 3 = 1 := by
    obtain ⟨u₀, hu₀, hsub⟩ := Subgroup.mem_map.mp u.2
    rw [← hsub]
    simpa using hBs.2 (u₀ : G) u₀.2
  have horder : orderOf (u : G) = 3 := by
    have hdvd : orderOf (u : G) ∣ 3 := orderOf_dvd_of_pow_eq_one huG3
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf (u : G)) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) huG1
    · exact h
  have h := Subgroup.orderOf_dvd_natCard (U.map Bs.subtype) u.2
  rwa [horder] at h

theorem ggE6DepBlockCfg_of_pairBlocks {Bs L J : Subgroup G} {x y : G}
    (hBs : IsElemAbelian 3 Bs) (hxBs : x ∈ Bs)
    (hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hconj : GGE6DepConjSetting 3 Bs x y L)
    (hpb : ∀ a b : ↥Bs, (a : G) ∈ L → (b : G) ∈ L → GGCorootOrth 3 (ggAutomizer L Bs) a b →
      ∃ Dv N : Subgroup G, GGE6DepPairBlock 3 Bs L a b Dv N)
    (hlayer : ∀ P : Subgroup G, P ≤ L ⊓ Subgroup.centralizer ({y} : Set G) → ⁅P, P⁆ = P →
      P ≤ J) :
    GGE6DepBlockCfg 3 Bs x J (x * y) := by
  obtain ⟨hZ, -, g, x₁, y₁, w, hx₁, hy₁, hy, hw, hg, hxg, hyg, hwg, hx₁L, hy₁L, hyL, hwL,
    horth1, horth2, U, hUcard, hUfix, hUL⟩ := hconj
  obtain ⟨Dv₁, N₁, hPB1⟩ := hpb ⟨x₁, hx₁⟩ ⟨y₁, hy₁⟩ hx₁L hy₁L horth1
  obtain ⟨hDv₁comp, hDv₁uniq, hN₁comp, hN₁uniq, hN₁Dv₁, hcycN₁, hfix₁, hn₁⟩ := hPB1
  obtain ⟨Dv₂, N₂, hPB2⟩ := hpb ⟨y, hy⟩ ⟨w, hw⟩ hyL hwL horth2
  obtain ⟨-, -, hN₂comp, hN₂uniq, -, -, hfix₂, -⟩ := hPB2
  have hcommg : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hBs.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) (⟨b, hb⟩ : ↥Bs))
  have hw3 : w ^ 3 = 1 := hBs.2 w hw
  have hcommxy : (x * y) * w = w * (x * y) := by
    have hxw := hcommg x hxBs w hw
    have hyw := hcommg y hy w hw
    calc (x * y) * w = x * (y * w) := by rw [mul_assoc]
      _ = x * (w * y) := by rw [hyw]
      _ = (x * w) * y := by rw [mul_assoc]
      _ = (w * x) * y := by rw [hxw]
      _ = w * (x * y) := by rw [mul_assoc]
  have hxy : g * (x₁ * y₁) * g⁻¹ = x * y := by rw [hxg, hyg]; group
  have hx1y1L : x₁ * y₁ ∈ L := L.mul_mem hx₁L hy₁L
  have hxyLw : x * y ∈ L.map (MulAut.conj g).toMonoidHom := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx1y1L
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxy] using h
  have hxLw : x ∈ L.map (MulAut.conj g).toMonoidHom := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx₁L
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rwa [← hxg] at h
  have hyLw : y ∈ L.map (MulAut.conj g).toMonoidHom := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hy₁L
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rwa [← hyg] at h
  have hLw_comp : IsComponentOf (L.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({w} : Set G)) := by
    have h := isComponentOf_map_conj hL g
    rwa [map_conj_centralizer_singleton g x, ← hwg] at h
  have hDw_comp : IsComponentOf (Dv₁.map (MulAut.conj g).toMonoidHom)
      (L.map (MulAut.conj g).toMonoidHom ⊓ Subgroup.centralizer ({x * y} : Set G)) := by
    have h := isComponentOf_map_conj hDv₁comp g
    rw [Subgroup.map_inf L (Subgroup.centralizer ({(x₁ : G) * (y₁ : G)} : Set G))
          (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
        map_conj_centralizer_singleton g (x₁ * y₁), hxy] at h
    exact h
  have hN₃_comp : IsComponentOf (N₁.map (MulAut.conj g).toMonoidHom)
      (L.map (MulAut.conj g).toMonoidHom ⊓
        Subgroup.centralizer ({(x : G), (y : G)} : Set G)) := by
    have h := isComponentOf_map_conj hN₁comp g
    rw [Subgroup.map_inf L (Subgroup.centralizer ({(x₁ : G), (y₁ : G)} : Set G))
          (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
        gg6C_map_conj_centralizer_pair g x₁ y₁, ← hxg, ← hyg] at h
    exact h
  have hDw_uniq : ∀ D' : Subgroup G,
      IsComponentOf D' (L.map (MulAut.conj g).toMonoidHom ⊓
        Subgroup.centralizer ({x * y} : Set G)) →
          D' = Dv₁.map (MulAut.conj g).toMonoidHom := by
    have h := (gg6C_conj_unique hDv₁comp hDv₁uniq g).2
    have hbase : (L ⊓ Subgroup.centralizer ({(x₁ : G) * (y₁ : G)} : Set G)).map
        (MulAut.conj g).toMonoidHom =
        L.map (MulAut.conj g).toMonoidHom ⊓ Subgroup.centralizer ({x * y} : Set G) := by
      rw [Subgroup.map_inf L (Subgroup.centralizer ({(x₁ : G) * (y₁ : G)} : Set G))
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
          map_conj_centralizer_singleton g (x₁ * y₁), hxy]
    rw [hbase] at h
    exact h
  have hN₃_uniq : ∀ N' : Subgroup G,
      IsComponentOf N' (L.map (MulAut.conj g).toMonoidHom ⊓
        Subgroup.centralizer ({(x : G), (y : G)} : Set G)) →
          N' = N₁.map (MulAut.conj g).toMonoidHom := by
    have h := (gg6C_conj_unique hN₁comp hN₁uniq g).2
    have hbase : (L ⊓ Subgroup.centralizer ({(x₁ : G), (y₁ : G)} : Set G)).map
        (MulAut.conj g).toMonoidHom =
        L.map (MulAut.conj g).toMonoidHom ⊓
          Subgroup.centralizer ({(x : G), (y : G)} : Set G) := by
      rw [Subgroup.map_inf L (Subgroup.centralizer ({(x₁ : G), (y₁ : G)} : Set G))
            (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
          gg6C_map_conj_centralizer_pair g x₁ y₁, ← hxg, ← hyg]
    rw [hbase] at h
    exact h
  have hxy1_ne : x₁ * y₁ ≠ 1 := by
    intro h
    apply horth1.1
    have hsub : (⟨x₁, hx₁⟩ : ↥Bs) = (⟨y₁, hy₁⟩ : ↥Bs)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      exact Subtype.ext h
    rw [hsub, Subgroup.zpowers_inv]
  have hxy1_pow : (x₁ * y₁) ^ 3 = 1 := by
    have hc : Commute x₁ y₁ := hcommg x₁ hx₁ y₁ hy₁
    rw [hc.mul_pow, hBs.2 x₁ hx₁, hBs.2 y₁ hy₁, mul_one]
  have hxy1_nc : ∃ m ∈ L, m * (x₁ * y₁) ≠ (x₁ * y₁) * m :=
    gg6C_noncentral Nat.prime_three hZ hx1y1L hxy1_ne hxy1_pow
  have hy_ne : y ≠ 1 := fun h =>
    (ggCorootPt_of_orth_left Nat.prime_three horth2).1 (Subtype.ext h)
  have hy_nc : ∃ m ∈ L, m * y ≠ y * m :=
    gg6C_noncentral Nat.prime_three hZ hyL hy_ne (hBs.2 y hy)
  have hx1_ne : x₁ ≠ 1 := fun h =>
    (ggCorootPt_of_orth_left Nat.prime_three horth1).1 (Subtype.ext h)
  have hx1_nc : ∃ m ∈ L, m * x₁ ≠ x₁ * m :=
    gg6C_noncentral Nat.prime_three hZ hx₁L hx1_ne (hBs.2 x₁ hx₁)
  have hnc_Dw : ∃ s ∈ ({x * y} : Set G), ∃ m ∈ L.map (MulAut.conj g).toMonoidHom,
      m * s ≠ s * m := by
    obtain ⟨m₁, hm₁L, hm₁⟩ := hxy1_nc
    refine ⟨x * y, by rw [Set.mem_singleton_iff], g * m₁ * g⁻¹, ?_, ?_⟩
    · have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hm₁L
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      exact h
    · have h := gg6C_noncentral_conj g hm₁
      rwa [hxy] at h
  have hnc_N₂ : ∃ s ∈ ({y, w} : Set G), ∃ m ∈ L, m * s ≠ s * m := by
    obtain ⟨m, hmL, hm⟩ := hy_nc
    exact ⟨y, by simp, m, hmL, hm⟩
  have hnc_N₃ : ∃ s ∈ ({x, y} : Set G), ∃ m ∈ L.map (MulAut.conj g).toMonoidHom,
      m * s ≠ s * m := by
    obtain ⟨m₁, hm₁L, hm₁⟩ := hx1_nc
    refine ⟨x, by simp, g * m₁ * g⁻¹, ?_, ?_⟩
    · have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hm₁L
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      exact h
    · have h := gg6C_noncentral_conj g hm₁
      rwa [← hxg] at h
  have hL3_Dw : IsComponentOf (Dv₁.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x * y} : Set G)) :=
    GGE6Dep.isComponentOf_inf_centralizer_of_unique hLw_comp
      (by intro s hs; rw [Set.mem_singleton_iff] at hs; subst hs; exact hxyLw)
      hnc_Dw hDw_comp hDw_uniq
  have hL3_N₂ : IsComponentOf N₂
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y, w} : Set G)) :=
    GGE6Dep.isComponentOf_inf_centralizer_of_unique hL
      (by
        intro s hs
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hyL
        · exact hwL)
      hnc_N₂ hN₂comp hN₂uniq
  have hL3_N₃ : IsComponentOf (N₁.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer ({x, y} : Set G)) :=
    GGE6Dep.isComponentOf_inf_centralizer_of_unique hLw_comp
      (by
        intro s hs
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hxLw
        · exact hyLw)
      hnc_N₃ hN₃_comp hN₃_uniq
  have hDw_final : IsComponentOf (Dv₁.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({x * y, w} : Set G)) := by
    rwa [gg6C_centralizer_pair_eq (x * y) w] at hL3_Dw
  have hN₂comp' : IsComponentOf N₂ (Subgroup.centralizer ({x, y, w} : Set G)) := by
    rwa [gg6C_centralizer_triple₁ x y w] at hL3_N₂
  have hN₃comp' : IsComponentOf (N₁.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({x, y, w} : Set G)) := by
    rwa [gg6C_centralizer_triple₂ x y w] at hL3_N₃
  have hcycN₃ : IsCyclic (Subgroup.center ↥(N₁.map (MulAut.conj g).toMonoidHom)) :=
    (MulEquiv.isCyclic (Subgroup.centerCongr
      (N₁.equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective))).mp hcycN₁
  have hUexp : ∀ x : ↥U, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact hBs.2 ((x : ↥Bs) : G) (x : ↥Bs).2
  have hUnc : ¬ IsCyclic ↥U := gg6C_not_cyclic_of_exponent_three hUexp hUcard
  have hU'nc : ¬ IsCyclic ↥(U.map Bs.subtype) := by
    intro hc
    exact hUnc ((MulEquiv.isCyclic
      (U.equivMapOfInjective Bs.subtype Bs.subtype_injective)).mpr hc)
  have hU'_le : U.map Bs.subtype ≤ N₁.map (MulAut.conj g).toMonoidHom ⊓ N₂ := by
    intro u hu
    obtain ⟨u₀, hu₀, hsub⟩ := Subgroup.mem_map.mp hu
    rw [← hsub, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · obtain ⟨-, u₁, hu₁fix, hu₁L, hu₁eq⟩ := hUL u₀ hu₀
      have hN₁u₁ : (u₁ : G) ∈ N₁ := hfix₁ u₁ hu₁fix hu₁L
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hN₁u₁
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmem
      have heq : g * (u₁ : G) * g⁻¹ = (u₀ : G) := by rw [hu₁eq]; group
      rwa [heq] at hmem
    · exact hfix₂ u₀ (hUfix hu₀) (hUL u₀ hu₀).1
  have hN₃eq : N₁.map (MulAut.conj g).toMonoidHom = N₂ :=
    GGE6Dep.eq_of_noncyclic_inf hN₃comp' hN₂comp' hcycN₃ hU'_le hU'nc
  have hN₂leDw : N₂ ≤ Dv₁.map (MulAut.conj g).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hN₁Dv₁
    rw [← hN₃eq]
    exact h
  have hperf : ⁅N₂, N₂⁆ = N₂ := gg6C_commutator_eq_self hN₂comp.2.2
  have h3N₂ : 3 ∣ Nat.card N₂ :=
    (gg6C_dvd_card_of_map_subtype hBs hUcard).trans
      (Subgroup.card_dvd_of_le (hU'_le.trans inf_le_right))
  have h3Dw : 3 ∣ Nat.card (Dv₁.map (MulAut.conj g).toMonoidHom) :=
    h3N₂.trans (Subgroup.card_dvd_of_le hN₂leDw)
  have hN₂leJ : N₂ ≤ J := by
    refine hlayer N₂ ?_ hperf
    refine le_trans hN₂comp.1 ?_
    rintro z hz
    rw [Subgroup.mem_inf] at hz ⊢
    refine ⟨hz.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro t ht
    have ht' : t ∈ ({y, w} : Set G) := by
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      simp
    exact hz.2 t ht'
  obtain ⟨n₁, hn₁Dv₁, hn₁norm, hn₁move⟩ := hn₁
  have hnDw : g * n₁ * g⁻¹ ∈ Dv₁.map (MulAut.conj g).toMonoidHom := by
    have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hn₁Dv₁
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h
  have hnNorm : g * n₁ * g⁻¹ ∈ Subgroup.normalizer (Bs : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hn₁norm) (Subgroup.inv_mem _ hg)
  have hnMove : (g * n₁ * g⁻¹) * x * (g * n₁ * g⁻¹)⁻¹ ≠ x := by
    intro heq
    apply hn₁move
    have h := congrArg (fun t => g⁻¹ * t * g) heq
    rw [hxg] at h
    rw [show g⁻¹ * ((g * n₁ * g⁻¹) * (g * x₁ * g⁻¹) * (g * n₁ * g⁻¹)⁻¹) * g =
          n₁ * x₁ * n₁⁻¹ by group,
        show g⁻¹ * (g * x₁ * g⁻¹) * g = x₁ by group] at h
    exact h
  unfold GGE6DepBlockCfg
  exact ⟨w, Dv₁.map (MulAut.conj g).toMonoidHom, N₂, g * n₁ * g⁻¹,
    hw, hw3, hcommxy, hDw_final, h3Dw, hN₂leDw, hN₂leJ, hperf, h3N₂, hnDw, hnNorm, hnMove⟩

end CFSG.StandardType

end
