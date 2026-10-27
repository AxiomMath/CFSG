module

public import CFSG.LocalAnalysis.StandardType.FS81.StdLoc
public import CFSG.LocalAnalysis.StandardType.FS81.RootHostAux
public import CFSG.LocalAnalysis.StandardType.FS81.E7Row

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped commutatorElement

structure RootHost {G : Type} [Group G] (x : G) (L : Subgroup G) : Prop where
  le_centralizer : L ≤ Subgroup.centralizer ({x} : Set G)
  center_eq_bot : Subgroup.center L = ⊥
  mem_of_cube : ∀ y ∈ Subgroup.centralizer ({x} : Set G), y ^ 3 = 1 → y ∈ Subgroup.zpowers x ⊔ L
  map_conj_eq : ∀ k : G, k * x * k⁻¹ ∈ Subgroup.zpowers x → L.map (MulAut.conj k).toMonoidHom = L

private theorem le_of_perfect_of {G : Type} [Group G] {x : G} {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({x} : Set G))
    (hcube : ∀ y ∈ Subgroup.centralizer ({x} : Set G), y ^ 3 = 1 →
      y ∈ Subgroup.zpowers x ⊔ L)
    {P : Subgroup G} (hP : P ≤ Subgroup.centralizer ({x} : Set G))
    (hperf : ⁅P, P⁆ = P)
    (hgen : P ≤ Subgroup.closure {y : G | y ∈ P ∧ y ^ 3 = 1}) : P ≤ L := by
  have hPsup : P ≤ Subgroup.zpowers x ⊔ L := by
    refine hgen.trans ((Subgroup.closure_le _).mpr ?_)
    rintro y ⟨hyP, hy3⟩
    exact hcube y (hP hyP) hy3
  calc P = ⁅P, P⁆ := hperf.symm
    _ ≤ ⁅Subgroup.zpowers x ⊔ L, Subgroup.zpowers x ⊔ L⁆ :=
        Subgroup.commutator_mono hPsup hPsup
    _ ≤ L := commutator_sup_zpowers_le_of_centralizer hL

theorem RootHost.conj {G : Type} [Group G] {x : G} {L : Subgroup G} (h : RootHost x L) (g : G) :
    RootHost (g * x * g⁻¹) (L.map (MulAut.conj g).toMonoidHom) where
  le_centralizer := by
    intro y hy
    obtain ⟨l, hl, hyl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hyl]
    change (MulAut.conj g l) * (g * x * g⁻¹) = (g * x * g⁻¹) * MulAut.conj g l
    rw [MulAut.conj_apply]
    have hcomm : l * x = x * l :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)
    rw [show (g * l * g⁻¹) * (g * x * g⁻¹) = g * (l * x) * g⁻¹ by group,
      show (g * x * g⁻¹) * (g * l * g⁻¹) = g * (x * l) * g⁻¹ by group, hcomm]
  center_eq_bot := by
    have e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
      (MulAut.conj g).subgroupMap L
    rw [← Subgroup.map_center_eq e, h.center_eq_bot, Subgroup.map_bot]
  mem_of_cube := by
    intro y hy hy3
    have hy' : g⁻¹ * y * g ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      calc (g⁻¹ * y * g) * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
        _ = x * (g⁻¹ * y * g) := by group
    have hy3' : (g⁻¹ * y * g) ^ 3 = 1 := by
      rw [show g⁻¹ * y * g = g⁻¹ * y * (g⁻¹)⁻¹ by group, conj_pow, hy3]
      group
    have hmem := h.mem_of_cube (g⁻¹ * y * g) hy' hy3'
    have hmap := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hmem
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at hmap
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmap
    have hleft : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [hleft] at hmap
    exact hmap
  map_conj_eq := by
    intro k hk
    let k' : G := g⁻¹ * k * g
    have hk' : k' * x * k'⁻¹ ∈ Subgroup.zpowers x := by
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hk
      rw [MonoidHom.map_zpowers] at hmem
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hmem
      have harg : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [harg] at hmem
      have hleft : g⁻¹ * (k * (g * x * g⁻¹) * k⁻¹) * g = k' * x * k'⁻¹ := by
        simp only [k']
        group
      rw [hleft] at hmem
      exact hmem
    have hmap := h.map_conj_eq k' hk'
    calc (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom
        = L.map (MulAut.conj (k * g)).toMonoidHom := map_conj_mul L g k
      _ = L.map (MulAut.conj (g * k')).toMonoidHom := by
          rw [show k * g = g * k' by simp only [k']; group]
      _ = (L.map (MulAut.conj k').toMonoidHom).map (MulAut.conj g).toMonoidHom :=
          (map_conj_mul L k' g).symm
      _ = L.map (MulAut.conj g).toMonoidHom := by rw [hmap]

theorem RootHost.le_of_perfect {G : Type} [Group G] {x : G} {L : Subgroup G} (h : RootHost x L)
    {P : Subgroup G} (hP : P ≤ Subgroup.centralizer ({x} : Set G)) (hperf : ⁅P, P⁆ = P)
    (hgen : P ≤ Subgroup.closure {y : G | y ∈ P ∧ y ^ 3 = 1}) : P ≤ L :=
  le_of_perfect_of h.le_centralizer h.mem_of_cube hP hperf hgen

private theorem pow_val_neg_one {G : Type} [Group G] {a : G} (ha : a ^ 3 = 1) :
    a ^ ((-1 : ZMod 3)).val = a⁻¹ := by
  have hv : ((-1 : ZMod 3)).val = 2 := by decide
  rw [hv, pow_two]
  exact eq_inv_iff_mul_eq_one.mpr (by
    rw [← pow_two, ← pow_succ, show 2 + 1 = 3 by norm_num, ha])

theorem rootHost_D6 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) : RootHost b₀ K := by
  obtain ⟨R, -, -, -, -, -, h3elem, -⟩ := exists_cent_D6 hstd hB hrec
  have hb0ord : orderOf b₀ = 3 := hstd.2.1.1.1
  have hKC : K ≤ Subgroup.centralizer ({b₀} : Set G) := hstd.2.1.1.2.1
  have hKz : Subgroup.center ↥K = ⊥ := hstd.2.1.1.2.2.2.1
  have hrow : IsRow Row.D6 K := hstd.2.2.1
  have hKsimple : IsSimpleGroup ↥K := (isSimpleGroup_and_mulEquiv_of_isRow_D6 hrow hKz).1
  have hb1K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have h3K : 3 ∣ Nat.card K := by
    have h := K.orderOf_dvd_natCard hb1K
    rwa [B.ord 1] at h
  haveI : Nontrivial ↥K := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have hb1bot : B.b 1 ∈ (⊥ : Subgroup G) := hbot ▸ hb1K
    have hb1one : B.b 1 = 1 := Subgroup.mem_bot.mp hb1bot
    have h := B.ord 1
    rw [hb1one, orderOf_one] at h
    exact absurd h (by norm_num)
  have hKperfect : Group.IsPerfect ↥K := isPerfect_of_isSimpleGroup_of_center_eq_bot hKz
  have hKcomm : ⁅K, K⁆ = K := (Subgroup.isPerfect_iff (H := K)).mp hKperfect
  have hKgen : K ≤ Subgroup.closure {y : G | y ∈ K ∧ y ^ 3 = 1} :=
    le_closure_cube_of_simple K h3K
  refine ⟨hKC, hKz, h3elem, ?_⟩
  intro k hk
  let f : G →* G := (MulAut.conj k).toMonoidHom
  let K' : Subgroup G := K.map f
  have hK'C : K' ≤ Subgroup.centralizer ({b₀} : Set G) := by
    have hd : k⁻¹ * b₀ * k ∈ Subgroup.zpowers b₀ := by
      have hmapz : (Subgroup.zpowers b₀).map (MulAut.conj k).toMonoidHom =
          Subgroup.zpowers (k * b₀ * k⁻¹) := MonoidHom.map_zpowers _ _
      have hle : Subgroup.zpowers (k * b₀ * k⁻¹) ≤ Subgroup.zpowers b₀ :=
        Subgroup.zpowers_le.mpr hk
      have hsem : SemiconjBy k b₀ (k * b₀ * k⁻¹) := by
        show k * b₀ = (k * b₀ * k⁻¹) * k
        group
      have hord : orderOf (k * b₀ * k⁻¹) = orderOf b₀ :=
        (SemiconjBy.orderOf_eq k hsem).symm
      have hcard : Nat.card ↥(Subgroup.zpowers (k * b₀ * k⁻¹)) =
          Nat.card ↥(Subgroup.zpowers b₀) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hord]
      have heq : Subgroup.zpowers (k * b₀ * k⁻¹) = Subgroup.zpowers b₀ :=
        Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
      have hkN : k ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        change Subgroup.map (MulAut.conj k).toMonoidHom (Subgroup.zpowers b₀) =
          Subgroup.zpowers b₀
        rw [hmapz, heq]
      have hk'inv := Subgroup.inv_mem _ hkN
      have hd : k⁻¹ * b₀ * k ∈ Subgroup.zpowers b₀ := by
        have := (Subgroup.mem_normalizer_iff.mp hk'inv b₀).mp (Subgroup.mem_zpowers b₀)
        simpa [inv_inv] using this
      exact hd
    intro y hy
    obtain ⟨a, haK, hay⟩ := Subgroup.mem_map.mp hy
    have hya : y = k * a * k⁻¹ := by
      rw [← hay]
      simp [f, MulAut.conj_apply]
    rw [Subgroup.mem_centralizer_singleton_iff, hya]
    have haZ : a ∈ Subgroup.centralizer ({b₀} : Set G) := hKC haK
    have hcomm_a_d : a * (k⁻¹ * b₀ * k) = (k⁻¹ * b₀ * k) * a := by
      have hb0Ca : b₀ ∈ Subgroup.centralizer ({a} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp haZ).symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp
        ((Subgroup.zpowers_le.mpr hb0Ca) hd)).symm
    calc (k * a * k⁻¹) * b₀ = k * (a * (k⁻¹ * b₀ * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * b₀ * k) * a) * k⁻¹ := by rw [hcomm_a_d]
      _ = b₀ * (k * a * k⁻¹) := by group
  have hK'comm : ⁅K', K'⁆ = K' := by
    have hmap : ⁅K, K⁆.map f = ⁅K', K'⁆ :=
      Subgroup.map_commutator (H₁ := K) (H₂ := K) f
    rw [← hmap, hKcomm]
  have hK'gen : K' ≤ Subgroup.closure {y : G | y ∈ K' ∧ y ^ 3 = 1} := by
    have hmap : (Subgroup.closure {y : G | y ∈ K ∧ y ^ 3 = 1}).map f ≤
        Subgroup.closure {y : G | y ∈ K' ∧ y ^ 3 = 1} := by
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨z, hz, rfl⟩
      refine Subgroup.subset_closure ⟨Subgroup.mem_map_of_mem f hz.1, ?_⟩
      rw [show f z ^ 3 = f (z ^ 3) by rw [map_pow], hz.2, map_one]
    calc K' = K.map f := rfl
      _ ≤ (Subgroup.closure {y : G | y ∈ K ∧ y ^ 3 = 1}).map f := Subgroup.map_mono hKgen
      _ ≤ _ := hmap
  have hK'le : K' ≤ K := le_of_perfect_of hKC h3elem hK'C hK'comm hK'gen
  have hcard : Nat.card K' = Nat.card K := by
    show Nat.card (K.map f) = Nat.card K
    exact Subgroup.card_map_of_injective (MulAut.conj k).injective
  exact Subgroup.eq_of_le_of_card_ge hK'le (le_of_eq hcard.symm)

end CFSG.StandardType.FrameRoute.FS81

end
