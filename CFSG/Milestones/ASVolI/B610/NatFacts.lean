module

public import CFSG.Quasithin.Background.B610TwoOff

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {L V : Subgroup G} {F : Type} [Field F]

theorem burnsideB610_statedSL_perfect (h4 : ∃ s : Finset F, s.card = 4) :
    commutator ↥(StatedSL 2 F) = ⊤ := by
  have hp := CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr h4)
  have e := specialLinearGroupEquivStatedSL 2 F
  rw [eq_top_iff]
  intro x _
  obtain ⟨A, rfl⟩ := e.surjective x
  have hA : A ∈ commutator (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [hp.commutator_eq_top]
    exact Subgroup.mem_top A
  have h1 := Subgroup.mem_map_of_mem e.toMonoidHom hA
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective]
    at h1
  exact h1

theorem burnsideB610_le_commutator_sup (D : NatData L V F) (h4 : ∃ s : Finset F, s.card = 4) :
    L ≤ ⁅L, L⁆ ⊔ (L ⊓ Subgroup.centralizer (V : Set G)) := by
  intro l hl
  have hα : D.α ⟨l, hl⟩ ∈ (commutator ↥L).map D.α := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ D.surj,
      ← commutator_def, burnsideB610_statedSL_perfect h4]
    exact Subgroup.mem_top _
  obtain ⟨l', hl', he⟩ := Subgroup.mem_map.mp hα
  have hker : l'⁻¹ * ⟨l, hl⟩ ∈ D.α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  rw [D.ker, Subgroup.mem_subgroupOf] at hker
  have hl'L : (l' : G) ∈ ⁅L, L⁆ := by
    have h1 := Subgroup.mem_map_of_mem L.subtype hl'
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      at h1
    exact h1
  have : l = (l' : G) * ((l'⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup hl'L hker

theorem burnsideB610_le_normalizer_commutator (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
  intro l hl
  have h1 : V.map (MulAut.conj l).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLV hl)
  have h2 : L.map (MulAut.conj l).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl)
  have h3 : (⁅V, L⁆ : Subgroup G).map (MulAut.conj l).toMonoidHom = ⁅V, L⁆ := by
    rw [Subgroup.map_commutator, h1, h2]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3


@[expose] def burnsideB610_stab (L V W : Subgroup G) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hWV : W ≤ V) : Subgroup G where
  carrier := {g | g ∈ L ∧ ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ W}
  one_mem' := ⟨L.one_mem, fun v _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨L.mul_mem hg hh, fun v hv => ?_⟩
    have hhv : h * v * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hh) v).mp hv
    have hw := hh' v hv
    have hgw : g * (h * v * h⁻¹ * v⁻¹) * g⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW hg) _).mp hw
    have hgv := hg' v hv
    have e : g * h * v * (g * h)⁻¹ * v⁻¹ =
        (g * (h * v * h⁻¹ * v⁻¹) * g⁻¹) * (g * v * g⁻¹ * v⁻¹) := by group
    rw [e]
    exact W.mul_mem hgw hgv
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨L.inv_mem hg, fun v hv => ?_⟩
    have hv' : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hg)) v).mp hv
      simpa using this
    have h1 := hg' _ hv'
    have e1 : g * (g⁻¹ * v * g) * g⁻¹ * (g⁻¹ * v * g)⁻¹ = v * (g⁻¹ * v * g)⁻¹ := by group
    rw [e1] at h1
    have hcomm : v * (g⁻¹ * v * g)⁻¹ = (g⁻¹ * v * g)⁻¹ * v :=
      B2F.isElemAbelian_comm hV hv (V.inv_mem hv')
    have e2 : g⁻¹ * v * g⁻¹⁻¹ * v⁻¹ = (v * (g⁻¹ * v * g)⁻¹)⁻¹ := by
      group
    rw [e2]
    exact W.inv_mem h1

theorem burnsideB610_commutator_commutator_eq (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hperf : L ≤ ⁅L, L⁆ ⊔ (L ⊓ Subgroup.centralizer (V : Set G))) :
    ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆ := by
  set U : Subgroup G := ⁅V, L⁆ with hU
  set W : Subgroup G := ⁅U, L⁆ with hW
  have hUV : U ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := burnsideB610_le_normalizer_commutator hLV
  have hWU : W ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hLU
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := burnsideB610_le_normalizer_commutator hLU
  refine le_antisymm hWU ?_
  set N := burnsideB610_stab L V W hV hLV hLW (hWU.trans hUV) with hN
  have hsq : ∀ l ∈ L, l ^ 2 ∈ N := by
    intro l hl
    refine ⟨L.pow_mem hl 2, fun v hv => ?_⟩
    set u := l * v * l⁻¹ * v⁻¹ with hu
    have huU : u ∈ U := by
      have : u = ⁅v, l⁆⁻¹ := by simp only [hu, commutatorElement_def]; group
      rw [this, hU]
      exact U.inv_mem (Subgroup.commutator_mem_commutator hv hl)
    set w := l * u * l⁻¹ * u⁻¹ with hw
    have hwW : w ∈ W := by
      have : w = ⁅u, l⁆⁻¹ := by simp only [hw, commutatorElement_def]; group
      rw [this, hW]
      exact W.inv_mem (Subgroup.commutator_mem_commutator huU hl)
    have hlv : l * v * l⁻¹ = u * v := by rw [hu]; group
    have hlu : l * u * l⁻¹ = w * u := by rw [hw]; group
    have hu2 : u * u = 1 := by
      have := hV.2 u (hUV huU)
      rwa [pow_two] at this
    have hwV : w ∈ V := hWU.trans hUV hwW
    have hcomm : u * v = v * u := B2F.isElemAbelian_comm hV (hUV huU) hv
    have e : l ^ 2 * v * (l ^ 2)⁻¹ * v⁻¹ = w := by
      have h1 : l ^ 2 * v * (l ^ 2)⁻¹ = l * (l * v * l⁻¹) * l⁻¹ := by
        simp only [pow_two]; group
      rw [h1, hlv]
      have h2 : l * (u * v) * l⁻¹ = (l * u * l⁻¹) * (l * v * l⁻¹) := by group
      rw [h2, hlu, hlv]
      calc w * u * (u * v) * v⁻¹ = w * (u * u) := by group
        _ = w := by rw [hu2, mul_one]
    rw [e]
    exact hwW
  have hconj : ∀ x ∈ L, ∀ g ∈ N, x * g * x⁻¹ ∈ N := by
    rintro x hx g ⟨hg, hg'⟩
    refine ⟨L.mul_mem (L.mul_mem hx hg) (L.inv_mem hx), fun v hv => ?_⟩
    have hv' : x⁻¹ * v * x ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem hx)) v).mp hv
      simpa using this
    have h1 := hg' _ hv'
    have h2 := (Subgroup.mem_normalizer_iff.mp (hLW hx) _).mp h1
    have e : x * g * x⁻¹ * v * (x * g * x⁻¹)⁻¹ * v⁻¹ =
        x * (g * (x⁻¹ * v * x) * g⁻¹ * (x⁻¹ * v * x)⁻¹) * x⁻¹ := by group
    rw [e]
    exact h2
  have hLL : ⁅L, L⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have e : ⁅a, b⁆ = (a * b) ^ 2 * (b⁻¹ * a ^ 2 * b)⁻¹ * (b ^ 2)⁻¹ := by
      simp only [commutatorElement_def, pow_two]; group
    rw [e]
    refine N.mul_mem (N.mul_mem (hsq _ (L.mul_mem ha hb)) (N.inv_mem ?_)) (N.inv_mem (hsq b hb))
    have := hconj b⁻¹ (L.inv_mem hb) _ (hsq a ha)
    simpa using this
  have hCN : L ⊓ Subgroup.centralizer (V : Set G) ≤ N := by
    rintro c ⟨hcL, hcV⟩
    refine ⟨hcL, fun v hv => ?_⟩
    have : c * v = v * c := (Subgroup.mem_centralizer_iff.mp hcV v hv).symm
    rw [this, mul_inv_cancel_right, mul_inv_cancel]
    exact W.one_mem
  have hLN : L ≤ N := hperf.trans (sup_le hLL hCN)
  rw [hU, Subgroup.commutator_le]
  intro v hv l hl
  have h1 := (hLN hl).2 v⁻¹ (V.inv_mem hv)
  have hx : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp (V.inv_mem hv)
  have hcomm : v * (l * v⁻¹ * l⁻¹) = (l * v⁻¹ * l⁻¹) * v := B2F.isElemAbelian_comm hV hv hx
  have e : ⁅v, l⁆ = l * v⁻¹ * l⁻¹ * v⁻¹⁻¹ := by
    rw [inv_inv, ← hcomm]
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h1


theorem burnsideB610_commutator_mem_centralizer (D : NatData L V F)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (a : ↥(nLV L V)) (ha : D.act a = 1) {x : G}
    (hx : x ∈ L) : (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  set x' : ↥(nLV L V) := ⟨x, Subgroup.le_normalizer hx, hLV hx⟩ with hx'
  have hy : (a : G) * x * (a : G)⁻¹ * x⁻¹ ∈ L := by
    have h1 : (a : G) * x * (a : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp a.2.1 x).mp hx
    exact L.mul_mem h1 (L.inv_mem hx)
  have h1 : D.act (a * x' * a⁻¹ * x'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha]
    group
  have h2 : (a * x' * a⁻¹ * x'⁻¹ : ↥(nLV L V)) =
      ⟨(a : G) * x * (a : G)⁻¹ * x⁻¹, Subgroup.le_normalizer hy, hLV hy⟩ := Subtype.ext (by simp [hx'])
  rw [h2, D.act_of_mem hLV ⟨_, hy⟩] at h1
  have h3 : D.α ⟨_, hy⟩ = 1 := by
    apply H.natAut_injective (Assembly.LowTwoRank.StatedSL 2 F)
    rw [h1, map_one]
  have h4 : (⟨_, hy⟩ : ↥L) ∈ D.α.ker := h3
  rw [D.ker, Subgroup.mem_subgroupOf] at h4
  exact h4.2

theorem burnsideB610_conj_mul_inv_mem (D : NatData L V F) (a : ↥(nLV L V)) (ha : D.act a = 1)
    (u : ↥⁅V, L⁆) :
    (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈ ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
  have h1 : D.act a (D.β u) = D.β u := by rw [ha]; rfl
  have h2 : D.act a (D.β u) = D.β (cW a u) := rho_apply D.β D.βsurj D.βker a u
  rw [h2] at h1
  have h3 : cW a u * u⁻¹ ∈ D.β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  rw [D.βker, Subgroup.mem_subgroupOf] at h3
  simpa [coe_cW] using h3

theorem burnsideB610_centralizes_of_act_eq_one (D : NatData L V F) (hV : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hperf : L ≤ ⁅L, L⁆ ⊔ (L ⊓ Subgroup.centralizer (V : Set G))) (a : ↥(nLV L V))
    (ha : D.act a = 1) : ∀ u ∈ ⁅V, L⁆, (a : G) * u = u * a := by
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hφ : ∀ x ∈ L, ∀ v ∈ V,
      (a : G) * (x * v * x⁻¹) * (a : G)⁻¹ = x * ((a : G) * v * (a : G)⁻¹) * x⁻¹ := by
    intro x hx v hv
    have hc := burnsideB610_commutator_mem_centralizer D hLV a ha hx
    set c := (a : G) * x * (a : G)⁻¹ * x⁻¹ with hcdef
    have hax : (a : G) * x * (a : G)⁻¹ = c * x := by rw [hcdef]; group
    have hav : (a : G) * v * (a : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp a.2.2 v).mp hv
    have hxav : x * ((a : G) * v * (a : G)⁻¹) * x⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLV hx) _).mp hav
    have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hxav
    calc (a : G) * (x * v * x⁻¹) * (a : G)⁻¹
        = ((a : G) * x * (a : G)⁻¹) * ((a : G) * v * (a : G)⁻¹) *
            ((a : G) * x * (a : G)⁻¹)⁻¹ := by group
      _ = c * (x * ((a : G) * v * (a : G)⁻¹) * x⁻¹) * c⁻¹ := by rw [hax]; group
      _ = x * ((a : G) * v * (a : G)⁻¹) * x⁻¹ := by rw [← hcomm]; group
  have key : ⁅⁅V, L⁆, L⁆ ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨hdU, hdL⟩ := burnsideB610_conj_mul_inv_mem D a ha ⟨u, hu⟩
    set d := (a : G) * u * (a : G)⁻¹ * u⁻¹ with hd
    have hau : (a : G) * u * (a : G)⁻¹ = d * u := by rw [hd]; group
    have hdV : d ∈ V := hUV hdU
    have huV : u ∈ V := hUV hu
    have hdx : x * d = d * x := Subgroup.mem_centralizer_iff.mp hdL x hx
    have hdu : d * u = u * d := B2F.isElemAbelian_comm hV hdV huV
    have hxu : x * u⁻¹ * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV hx) _).mp (V.inv_mem huV)
    have e1 : (a : G) * ⁅u, x⁆ * (a : G)⁻¹ =
        ((a : G) * u * (a : G)⁻¹) * ((a : G) * (x * u⁻¹ * x⁻¹) * (a : G)⁻¹) := by
      simp only [commutatorElement_def]; group
    have e2 : (a : G) * u⁻¹ * (a : G)⁻¹ = u⁻¹ * d⁻¹ := by
      have : (a : G) * u⁻¹ * (a : G)⁻¹ = ((a : G) * u * (a : G)⁻¹)⁻¹ := by group
      rw [this, hau, mul_inv_rev]
    have e3 : (a : G) * ⁅u, x⁆ * (a : G)⁻¹ = ⁅u, x⁆ := by
      rw [e1, hφ x hx u⁻¹ (V.inv_mem huV), e2, hau]
      have hdx' : x * d⁻¹ * x⁻¹ = d⁻¹ := by
        have h1 : x * d * x⁻¹ = d := by rw [hdx]; group
        calc x * d⁻¹ * x⁻¹ = (x * d * x⁻¹)⁻¹ := by group
          _ = d⁻¹ := by rw [h1]
      calc d * u * (x * (u⁻¹ * d⁻¹) * x⁻¹) = d * u * (x * u⁻¹ * x⁻¹) * (x * d⁻¹ * x⁻¹) := by group
        _ = d * u * (x * u⁻¹ * x⁻¹) * d⁻¹ := by rw [hdx']
        _ = u * d * (x * u⁻¹ * x⁻¹) * d⁻¹ := by rw [hdu]
        _ = u * (x * u⁻¹ * x⁻¹) := by
          rw [mul_assoc u d, B2F.isElemAbelian_comm hV hdV hxu]; group
        _ = ⁅u, x⁆ := by simp only [commutatorElement_def]; group
    calc (a : G) * ⁅u, x⁆ = ((a : G) * ⁅u, x⁆ * (a : G)⁻¹) * a := by group
      _ = ⁅u, x⁆ * a := by rw [e3]
  intro u hu
  rw [← burnsideB610_commutator_commutator_eq hV hLV hperf] at hu
  have := Subgroup.mem_centralizer_iff.mp (key hu) a rfl
  exact this


theorem burnsideB610_scalar_of_commute {g : MulAut (H.StdMod (Fin 2) F)}
    (hg : ∀ γ : ↥(StatedSL 2 F), g * H.natAut (StatedSL 2 F) γ = H.natAut (StatedSL 2 F) γ * g) :
    ∃ c : F, ∀ v, H.toAddMap g v = c • v := by
  let f : (Fin 2 → F) →+ (Fin 2 → F) :=
    AddMonoidHom.mk' (H.toAddMap g) (H.toAddMap_add g)
  refine H.hasScalarCommutant_statedSL (le_refl 2) f fun γ hγ v => ?_
  have h := congrArg (fun y => H.toAddMap y v) (hg ⟨γ, hγ⟩)
  simp only [H.toAddMap_mul, H.toAddMap_natAut] at h
  exact h

theorem burnsideB610_commute_of_commute_sl2 {g h : MulAut (H.StdMod (Fin 2) F)}
    (hg : ∀ γ : ↥(StatedSL 2 F), g * H.natAut (StatedSL 2 F) γ = H.natAut (StatedSL 2 F) γ * g)
    (hh : ∀ γ : ↥(StatedSL 2 F), h * H.natAut (StatedSL 2 F) γ = H.natAut (StatedSL 2 F) γ * h) :
    g * h = h * g := by
  obtain ⟨c, hc⟩ := burnsideB610_scalar_of_commute hg
  obtain ⟨d, hd⟩ := burnsideB610_scalar_of_commute hh
  refine H.toAddMap_injective fun v => ?_
  rw [H.toAddMap_mul, H.toAddMap_mul, hc, hd, hd, hc, smul_smul, smul_smul, mul_comm]

theorem burnsideB610_act_commute (D : NatData L V F) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (y : ↥(nLV L V)) (hy : ∀ x ∈ L, (y : G) * x * (y : G)⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G))
    (γ : ↥(StatedSL 2 F)) :
    D.act y * H.natAut (StatedSL 2 F) γ = H.natAut (StatedSL 2 F) γ * D.act y := by
  obtain ⟨l, rfl⟩ := D.surj γ
  rw [← D.act_of_mem hLV l]
  set x : ↥(nLV L V) := ⟨l, Subgroup.le_normalizer l.2, hLV l.2⟩ with hx
  have h1 : D.act (y * x * y⁻¹ * x⁻¹) = 1 :=
    D.act_eq_one hLV _ (by simpa [hx] using hy l l.2)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc D.act y * D.act x = (D.act y * D.act x * (D.act y)⁻¹ * (D.act x)⁻¹) * (D.act x * D.act y) := by
        group
    _ = D.act x * D.act y := by rw [h1, one_mul]

theorem burnsideB610_act_eq_one_of_commute (D : NatData L V F)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {Y : Subgroup G} (hYN : Y ≤ nLV L V)
    (hY : ∀ y ∈ Y, ∀ x ∈ L, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G))
    (hperf : Y ≤ ⁅Y, Y⁆ ⊔ (Y ⊓ Subgroup.centralizer (V : Set G))) :
    ∀ y (hy : y ∈ Y), D.act ⟨y, hYN hy⟩ = 1 := by
  set K : Subgroup G := Y ⊓ ((D.act.ker).map (nLV L V).subtype) with hK
  have hcomm : ∀ a (ha : a ∈ Y) b (hb : b ∈ Y),
      D.act ⟨a, hYN ha⟩ * D.act ⟨b, hYN hb⟩ = D.act ⟨b, hYN hb⟩ * D.act ⟨a, hYN ha⟩ :=
    fun a ha b hb => burnsideB610_commute_of_commute_sl2
      (burnsideB610_act_commute D hLV _ (hY a ha)) (burnsideB610_act_commute D hLV _ (hY b hb))
  have hYY : ⁅Y, Y⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ Y := Y.mul_mem (Y.mul_mem (Y.mul_mem ha hb) (Y.inv_mem ha)) (Y.inv_mem hb)
    refine ⟨hab, ⟨⁅a, b⁆, hYN hab⟩, ?_, rfl⟩
    show _ ∈ D.act.ker
    rw [MonoidHom.mem_ker]
    have e : (⟨⁅a, b⁆, hYN hab⟩ : ↥(nLV L V)) =
        ⟨a, hYN ha⟩ * ⟨b, hYN hb⟩ * (⟨a, hYN ha⟩ : ↥(nLV L V))⁻¹ * (⟨b, hYN hb⟩ : ↥(nLV L V))⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm a ha b hb]
    group
  have hYC : Y ⊓ Subgroup.centralizer (V : Set G) ≤ K := by
    rintro c ⟨hcY, hcV⟩
    exact ⟨hcY, ⟨c, hYN hcY⟩, D.act_eq_one hLV _ hcV, rfl⟩
  intro y hy
  obtain ⟨-, z, hz, hzy⟩ := hperf.trans (sup_le hYY hYC) hy
  have : z = ⟨y, hYN hy⟩ := Subtype.ext hzy
  rw [← this]
  exact hz

end CFSG.Quasithin.B610T
