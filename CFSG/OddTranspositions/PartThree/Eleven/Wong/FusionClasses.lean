module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.FusionNotConj
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.OddCore
public import CFSG.GroupTheory.PGroup.LtInfNormalizer
public import CFSG.GH74.GLS.SP.GenOrder

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup Matrix

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)


private theorem vecE_def (a : Fin 4 → ZMod 2) :
    D.vecE a = D.t ^ (a 0).val * D.u ^ (a 1).val * D.v ^ (a 2).val * D.w ^ (a 3).val :=
  rfl



private theorem i2_inv_mul_u_mul_i2 (a : SL5) :
    (D.i2 a)⁻¹ * D.u * D.i2 a = D.i1 a * D.i2 a⁻¹ * D.u := by
  calc (D.i2 a)⁻¹ * D.u * D.i2 a
      = D.i2 a⁻¹ * (D.u * D.i2 a) := by rw [map_inv]; group
    _ = D.i2 a⁻¹ * (D.i1 a * D.u) := by rw [D.u_mul_i2]
    _ = (D.i2 a⁻¹ * D.i1 a) * D.u := by rw [mul_assoc]
    _ = (D.i1 a * D.i2 a⁻¹) * D.u := by rw [← (D.commute a a⁻¹).eq]
    _ = D.i1 a * D.i2 a⁻¹ * D.u := by rw [mul_assoc]

private theorem inv_mul_t_mul_u_mul {k : G} (hk : Commute D.t k) :
    k⁻¹ * (D.t * D.u) * k = D.t * (k⁻¹ * D.u * k) := by
  have hk' : Commute D.t k⁻¹ := hk.inv_right
  calc k⁻¹ * (D.t * D.u) * k
      = (k⁻¹ * D.t) * D.u * k := by group
    _ = (D.t * k⁻¹) * D.u * k := by rw [← hk'.eq]
    _ = D.t * (k⁻¹ * D.u * k) := by group

theorem exists_conj_of_not_mem_K [Finite G] {x : G} (hx : x ∈ centralizer {D.t})
    (hx2 : orderOf x = 2) (hxK : x ∉ D.K) :
    (∃ k ∈ D.K, k⁻¹ * D.u * k = x) ∨ ∃ k ∈ D.K, k⁻¹ * (D.t * D.u) * k = x := by
  rcases D.mem_centralizer_t_iff.mp hx with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · exact absurd (D.mem_K_iff.mpr ⟨a, b, rfl⟩) hxK
  · have hxx : D.i1 a * D.i2 b * D.u * (D.i1 a * D.i2 b * D.u) =
        D.i1 (a * b) * D.i2 (b * a) := by
      calc D.i1 a * D.i2 b * D.u * (D.i1 a * D.i2 b * D.u)
          = (D.i1 a * D.i2 b) * (D.u * (D.i1 a * D.i2 b) * D.u) := by group
        _ = (D.i1 a * D.i2 b) * (D.i1 b * D.i2 a) := by
              rw [show D.u * (D.i1 a * D.i2 b) * D.u = D.i1 b * D.i2 a by
                simpa only [D.u_inv] using D.u_conj_prod a b]
        _ = D.i1 (a * b) * D.i2 (b * a) := D.prod_mul_prod a b b a
    have h1 : D.i1 (a * b) * D.i2 (b * a) = 1 := by
      have h := pow_orderOf_eq_one (D.i1 a * D.i2 b * D.u)
      rw [hx2, pow_two] at h
      rwa [hxx] at h
    have hmemK : ∀ z : SL5, D.i2 z ∈ D.K := fun z =>
      D.mem_K_iff.mpr ⟨1, z, by rw [map_one, one_mul]⟩
    rcases (prodHom_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf).mp h1 with
      ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left
      have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right ha
      refine ⟨D.i2 a, hmemK a, ?_⟩
      rw [hb', i2_inv_mul_u_mul_i2]
    · right
      have hb' : b = -a⁻¹ := by
        have h := eq_inv_mul_of_mul_eq ha
        rwa [mul_neg_one] at h
      refine ⟨D.i2 a, hmemK a, ?_⟩
      rw [hb', D.i2_neg, inv_mul_t_mul_u_mul D (D.t_commute_i2 a), i2_inv_mul_u_mul_i2]
      calc D.t * (D.i1 a * D.i2 a⁻¹ * D.u)
          = (D.t * D.i1 a) * (D.i2 a⁻¹ * D.u) := by group
        _ = (D.i1 a * D.t) * (D.i2 a⁻¹ * D.u) := by rw [(D.t_commute_i1 a).eq]
        _ = D.i1 a * (D.t * D.i2 a⁻¹) * D.u := by group

theorem isConj_u_t_mul_u_mul :
    IsConj D.u (D.t * D.u * D.v) ∧ IsConj D.u (D.t * D.u * D.w) ∧
      IsConj D.u (D.t * D.u * D.v * D.w) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [D.v_eq_d] using D.isConj_u_t_mul_u_mul_d hM_sq
  · simpa [D.w_eq_d] using D.isConj_u_t_mul_u_mul_d cM_sq
  · have h := D.isConj_u_t_mul_u_mul_d hM_mul_cM_sq
    rw [map_mul] at h
    simpa [D.v_eq_d, D.w_eq_d, mul_assoc] using h

theorem isConj_t_mul_u_u_mul :
    IsConj (D.t * D.u) (D.u * D.v) ∧ IsConj (D.t * D.u) (D.u * D.w) ∧
      IsConj (D.t * D.u) (D.u * D.v * D.w) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [D.v_eq_d] using D.isConj_tu_u_mul_d hM_sq
  · simpa [D.w_eq_d] using D.isConj_tu_u_mul_d cM_sq
  · have h := D.isConj_tu_u_mul_d hM_mul_cM_sq
    rw [map_mul] at h
    simpa [D.v_eq_d, D.w_eq_d, mul_assoc] using h

theorem isConj_t_u_or_t_tu [Finite G] : IsConj D.t D.u ∨ IsConj D.t (D.t * D.u) := by
  obtain ⟨g, hgC, hgne⟩ := exists_conj_mem_centralizer_ne D.orderOf_t D.hyp.sup_oddCore_ne_top
  set x := g⁻¹ * D.t * g with hxdef
  have hx2 : orderOf x = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) D.t
    simp only [MulAut.conj_apply, inv_inv] at h
    rw [hxdef, h, D.orderOf_t]
  have hxt : x ≠ D.t := by rw [hxdef]; exact hgne
  have h_tx : IsConj D.t x :=
    isConj_iff.mpr ⟨g⁻¹, by simpa only [inv_inv] using hxdef.symm⟩
  by_cases hxK : x ∈ D.K
  · have h_vx : IsConj D.v x := by
      obtain ⟨k, -, hk⟩ := D.exists_conj_v_of_mem_K hxK hx2 hxt
      exact isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩
    exact absurd (h_tx.trans h_vx.symm) D.not_isConj_t_v
  · rcases D.exists_conj_of_not_mem_K hgC hx2 hxK with ⟨k, -, hk⟩ | ⟨k, -, hk⟩
    · left
      exact h_tx.trans (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩).symm
    · right
      exact h_tx.trans (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩).symm

theorem exists_isConj_t_tu [Finite G] :
    ∃ D' : SwapData G, D'.i1 = D.i1 ∧ D'.i2 = D.i2 ∧ D'.t = D.t ∧
      IsConj D'.t (D'.t * D'.u) := by
  rcases D.isConj_t_u_or_t_tu with htu | htu
  · have hsquare : (D.t * D.u) * (D.t * D.u) = 1 := by
      calc (D.t * D.u) * (D.t * D.u)
          = D.t * (D.u * D.t) * D.u := by group
        _ = D.t * (D.t * D.u) * D.u := by rw [← D.t_commute_u.eq]
        _ = (D.t * D.t) * (D.u * D.u) := by group
        _ = 1 := by rw [D.t_mul_t, D.u_mul_u, one_mul]
    have hne : D.t * D.u ≠ 1 := by
      intro h
      have hu : D.u = D.t := by
        calc D.u = D.t * (D.t * D.u) := (D.t_mul_t_mul D.u).symm
          _ = D.t * 1 := by rw [h]
          _ = D.t := mul_one _
      exact D.u_ne_t hu
    have horder : orderOf (D.t * D.u) = 2 := by
      refine orderOf_eq_prime ?_ hne
      rwa [pow_two]
    let D' : SwapData G :=
      { D with
        u := D.t * D.u
        orderOf_u := horder
        swap := fun x => by
          have ht : (D.t * D.u)⁻¹ = D.u * D.t := by rw [_root_.mul_inv_rev, D.t_inv, D.u_inv]
          rw [ht]
          calc D.u * D.t * D.i1 x * (D.t * D.u)
              = D.u * (D.t * D.i1 x * D.t) * D.u := by group
            _ = D.u * D.i1 x * D.u := by
                rw [show D.t * D.i1 x * D.t = D.i1 x by
                  rw [(D.t_commute_i1 x).eq, mul_assoc, D.t_mul_t, mul_one]]
            _ = D.i2 x := by simpa [D.u_inv] using D.swap x
        u_not_mem := D.t_mul_u_not_mem_K }
    refine ⟨D', rfl, rfl, rfl, ?_⟩
    change IsConj D.t (D.t * (D.t * D.u))
    rw [D.t_mul_t_mul]
    exact htu
  · exact ⟨D, rfl, rfl, rfl, htu⟩

private theorem map_conj_centralizer_singleton_fusion {X : Type*} [Group X] (g t : X) :
    (Subgroup.centralizer ({t} : Set X)).map (MulAut.conj g) =
      Subgroup.centralizer ({g * t * g⁻¹} : Set X) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (g * y * g⁻¹) ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set X)
    have hy' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hy']
        _ = (g * t * g⁻¹) * (g * y * g⁻¹) := by group)
  · intro x hx
    have hx' : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · change (g⁻¹ * x * g) ∈ Subgroup.centralizer ({t} : Set X)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx']
          _ = t * (g⁻¹ * x * g) := by group)
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

private theorem factorization_14400_two : (14400 : ℕ).factorization 2 = 6 := by
  rw [Nat.factorization_def 14400 Nat.prime_two]
  have h1 : (14400 : ℕ) = 2 ^ 6 * 225 := by norm_num
  rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 225)]

private theorem card_A_fusion : Nat.card D.A = 60 := by
  have hker : (D.d.ker : Set SL5) = {1, -1} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, D.d_apply, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    exact diag_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf
  have hker2 : Nat.card D.d.ker = 2 := by
    change Nat.card (D.d.ker : Set SL5) = 2
    rw [hker, Nat.card_coe_set_eq, Set.ncard_pair sl5_neg_one_ne_one.symm]
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    rw [Matrix.card_SL_field 2, ZMod.card]
    norm_num
  have h := Subgroup.card_ker_mul_card_range D.d
  rw [hker2, hSL] at h
  change Nat.card D.d.range = 60
  omega

theorem exists_mem_normalizer_E_conj_t_ne [Finite G]
    (htu : IsConj D.t (D.t * D.u)) :
    ∃ z₀ ∈ normalizer (D.E : Set G), z₀⁻¹ * D.t * z₀ ≠ D.t := by
  have hCeq : centralizer ({D.t} : Set G) ⊓ centralizer ({D.t * D.u} : Set G) =
      centralizer ({D.t} : Set G) ⊓ centralizer ({D.u} : Set G) := by
    ext x
    simp only [mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨ht, htu⟩
      refine ⟨ht, ?_⟩
      have h1 : D.t * (x * D.u) = D.t * (D.u * x) := by
        calc D.t * (x * D.u) = (D.t * x) * D.u := by rw [mul_assoc]
          _ = (x * D.t) * D.u := by rw [← ht]
          _ = x * (D.t * D.u) := by rw [mul_assoc]
          _ = (D.t * D.u) * x := htu
          _ = D.t * (D.u * x) := by rw [mul_assoc]
      exact mul_left_cancel h1
    · rintro ⟨ht, hu⟩
      refine ⟨ht, ?_⟩
      calc x * (D.t * D.u) = (x * D.t) * D.u := by rw [mul_assoc]
        _ = (D.t * x) * D.u := by rw [ht]
        _ = D.t * (x * D.u) := by rw [mul_assoc]
        _ = D.t * (D.u * x) := by rw [hu]
        _ = (D.t * D.u) * x := by rw [mul_assoc]
  have hA_norm : D.A ≤ normalizer (closure {D.t, D.u} : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer (closure {D.t, D.u} : Set G))
    rw [centralizer_closure]
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (D.d_commute_t x).eq.symm
    · exact (D.d_commute_u x).eq.symm
  have hcard_inf :
      Nat.card ↥(centralizer ({D.t} : Set G) ⊓ centralizer ({D.t * D.u} : Set G)) = 240 := by
    rw [hCeq, D.centralizer_t_inf_centralizer_u,
      CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot hA_norm D.closure_t_u_inf_A,
      card_closure_pair D.orderOf_t D.orderOf_u D.t_commute_u D.u_ne_t, card_A_fusion D]
  have hcardCy : Nat.card (centralizer ({D.t * D.u} : Set G)) = 14400 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp htu
    rw [← hc, ← map_conj_centralizer_singleton_fusion c D.t,
      Subgroup.card_map_of_injective (MulAut.conj c).injective, D.hyp.card_centralizer]
  have hE_le_Cy : D.E ≤ centralizer ({D.t * D.u} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_centralizer_singleton_iff.mpr ((Commute.refl D.t).mul_right D.t_commute_u).eq
    · exact mem_centralizer_singleton_iff.mpr
        ((D.t_commute_u.symm).mul_right (Commute.refl D.u)).eq
    · exact mem_centralizer_singleton_iff.mpr
        ((D.commute_t_v.symm).mul_right (D.commute_u_v.symm)).eq
    · exact mem_centralizer_singleton_iff.mpr
        ((D.commute_t_w.symm).mul_right (D.commute_u_w.symm)).eq
  have hE2 : IsPGroup 2 D.E := IsPGroup.of_card (n := 4) (by rw [D.card_E]; norm_num)
  have hEsub2 : IsPGroup 2 (D.E.subgroupOf (centralizer ({D.t * D.u} : Set G))) := by
    have h := IsPGroup.comap_of_injective hE2
      (Subgroup.subtype (centralizer ({D.t * D.u} : Set G)))
      (Subgroup.subtype_injective _)
    rwa [Subgroup.comap_subtype] at h
  obtain ⟨Q, hQ⟩ := hEsub2.exists_le_sylow
  let V : Subgroup G := (Q : Subgroup (centralizer ({D.t * D.u} : Set G))).map
    (Subgroup.subtype (centralizer ({D.t * D.u} : Set G)))
  have hVcard : Nat.card V = 64 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Sylow.card_eq_multiplicity Q, hcardCy, factorization_14400_two]
    norm_num
  have hV2 : IsPGroup 2 V := IsPGroup.map Q.isPGroup' (Subgroup.subtype _)
  have hVle : V ≤ centralizer ({D.t * D.u} : Set G) := Subgroup.map_subtype_le _
  have hE_le_V : D.E ≤ V := by
    intro g hg
    exact Subgroup.mem_map.mpr ⟨⟨g, hE_le_Cy hg⟩, hQ (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
  have hE_lt_V : D.E < V := by
    refine lt_of_le_of_ne hE_le_V ?_
    intro hEq
    have hc := congrArg (fun H : Subgroup G => Nat.card ↥H) hEq
    rw [D.card_E, hVcard] at hc
    norm_num at hc
  obtain ⟨z₀, hz₀, hz₀E⟩ :=
    SetLike.exists_of_lt (CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hV2 hE_lt_V)
  have hz₀V : z₀ ∈ V := (mem_inf.mp hz₀).1
  have hz₀N : z₀ ∈ normalizer (D.E : Set G) := (mem_inf.mp hz₀).2
  refine ⟨z₀, hz₀N, ?_⟩
  intro hfix
  have hz₀C : z₀ ∈ centralizer ({D.t} : Set G) := by
    refine mem_centralizer_singleton_iff.mpr ?_
    have h' : z₀ * D.t * z₀⁻¹ = D.t := by
      have h := congrArg (fun y => z₀ * y * z₀⁻¹) hfix
      simpa [mul_assoc] using h.symm
    calc z₀ * D.t = (z₀ * D.t * z₀⁻¹) * z₀ := by group
      _ = D.t * z₀ := by rw [h']
  let W : Subgroup G := V ⊓ centralizer ({D.t} : Set G)
  have hE_le_W : D.E ≤ W :=
    le_inf hE_le_V (D.E_le_S.trans D.S_le_centralizer_t)
  have hz₀W : z₀ ∈ W := mem_inf.mpr ⟨hz₀V, hz₀C⟩
  have hWne : W ≠ D.E := by
    intro h
    exact hz₀E (h.symm ▸ hz₀W)
  have hE_lt_W : D.E < W := lt_of_le_of_ne hE_le_W (Ne.symm hWne)
  have hWle : W ≤ centralizer ({D.t} : Set G) ⊓ centralizer ({D.t * D.u} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hVle)
  have hW2 : IsPGroup 2 W := IsPGroup.to_le hV2 inf_le_left
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hcardE_lt : Nat.card D.E < Nat.card W := Subgroup.card_lt_of_lt hE_lt_W
  have hn5 : 5 ≤ n := by
    have hlt : 2 ^ 4 < 2 ^ n := by
      rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
      rwa [D.card_E, hn] at hcardE_lt
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  have h32 : (32 : ℕ) ∣ Nat.card W := by
    rw [hn]
    simpa using pow_dvd_pow (2 : ℕ) hn5
  have hdiv : Nat.card W ∣ 240 := by
    have := Subgroup.card_dvd_of_le hWle
    rwa [hcard_inf] at this
  exact absurd (Nat.dvd_trans h32 hdiv) (by norm_num)

private def fusionJ4 : Finset (Fin 4 → ZMod 2) :=
  {![0, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 0, 1], ![1, 1, 1, 1]}

private theorem isConj_t_vecE_of_mem_fusionPplus (htu : IsConj D.t (D.t * D.u))
    {a : Fin 4 → ZMod 2} (ha : a ∈ fusionPplus) : IsConj D.t (D.vecE a) := by
  simp only [fusionPplus, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using IsConj.refl D.t
  · simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using htu
  · simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using htu.trans (isConj_t_mul_u_u_mul D).1
  · simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using htu.trans (isConj_t_mul_u_u_mul D).2.1
  · simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using htu.trans (isConj_t_mul_u_u_mul D).2.2

private theorem isConj_u_vecE_of_mem_fusionJ4 {a : Fin 4 → ZMod 2} (ha : a ∈ fusionJ4) :
    IsConj D.u (D.vecE a) := by
  simp only [fusionJ4, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using IsConj.refl D.u
  · simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using (isConj_u_t_mul_u_mul D).1
  · simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using (isConj_u_t_mul_u_mul D).2.1
  · simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using (isConj_u_t_mul_u_mul D).2.2

private theorem class_of_ne_zero (htu : IsConj D.t (D.t * D.u)) {a : Fin 4 → ZMod 2}
    (ha : a ≠ 0) :
    a ∈ fusionJ3 ∨ IsConj D.t (D.vecE a) ∨ IsConj D.u (D.vecE a) := by
  have hcover : ∀ a : Fin 4 → ZMod 2, a ≠ 0 →
      a ∈ fusionJ3 ∨ a ∈ fusionPplus ∨ a ∈ fusionJ4 := by decide
  rcases hcover a ha with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (isConj_t_vecE_of_mem_fusionPplus D htu h))
  · exact Or.inr (Or.inr (isConj_u_vecE_of_mem_fusionJ4 D h))

private theorem vecE_mem_K_of_mem_fusionJ3 {c : Fin 4 → ZMod 2} (hc : c ∈ fusionJ3) :
    D.vecE c ∈ D.K := by
  simp only [fusionJ3, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [vecE_def, ZMod.val_zero, ZMod.val_one] <;>
    first
    | exact D.d_mem_K hM
    | exact D.d_mem_K cM
    | exact mul_mem (D.d_mem_K hM) (D.d_mem_K cM)
    | exact mul_mem D.t_mem_K (D.d_mem_K hM)
    | exact mul_mem D.t_mem_K (D.d_mem_K cM)
    | exact mul_mem (mul_mem D.t_mem_K (D.d_mem_K hM)) (D.d_mem_K cM)

private theorem vecE_ne_zero_of_mem_fusionJ3 {c : Fin 4 → ZMod 2} (hc : c ∈ fusionJ3) :
    D.vecE c ≠ 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact absurd hc (by decide)
  have h := D.vecE_injective.ne hc0
  rwa [D.vecE_zero] at h

private theorem vecE_ne_t_of_mem_fusionJ3 {c : Fin 4 → ZMod 2} (hc : c ∈ fusionJ3) :
    D.vecE c ≠ D.t := by
  have hct : c ≠ ![1, 0, 0, 0] := by
    rintro rfl
    exact absurd hc (by decide)
  have h := D.vecE_injective.ne hct
  simpa [vecE_def, ZMod.val_zero, ZMod.val_one] using h

private theorem orderOf_vecE_of_mem_fusionJ3 {c : Fin 4 → ZMod 2} (hc : c ∈ fusionJ3) :
    orderOf (D.vecE c) = 2 :=
  orderOf_eq_prime (by simpa [pow_two] using D.sq_eq_one_of_mem_E (D.vecE_mem_E c))
    (vecE_ne_zero_of_mem_fusionJ3 D hc)

private theorem mem_fusionJ3_vecMul_of_mem_fusionJ3 [Finite G]
    {ρ : normalizer (D.E : Set G) →* GL (Fin 4) (ZMod 2)} (hρ : D.IsBasisRep ρ)
    {z0 : G} (hz0 : z0 ∈ normalizer (D.E : Set G))
    (htu : IsConj D.t (D.t * D.u))
    (huv : ¬ IsConj D.u D.v) {c : Fin 4 → ZMod 2} (hc : c ∈ fusionJ3) :
    c ᵥ* (ρ ⟨z0, hz0⟩ : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈ fusionJ3 := by
  set m : Matrix (Fin 4) (Fin 4) (ZMod 2) := (ρ ⟨z0, hz0⟩ : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hm
  set d : Fin 4 → ZMod 2 := c ᵥ* m with hd
  have hconj : z0⁻¹ * D.vecE c * z0 = D.vecE d := by
    have := hρ.conj_vecE ⟨z0, hz0⟩ c
    simpa [hm, hd] using this
  have hvc : IsConj D.v (D.vecE c) := by
    obtain ⟨k, -, hk⟩ := D.exists_conj_v_of_mem_K (vecE_mem_K_of_mem_fusionJ3 D hc)
      (orderOf_vecE_of_mem_fusionJ3 D hc) (vecE_ne_t_of_mem_fusionJ3 D hc)
    exact isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩
  have hvd : IsConj D.v (D.vecE d) := by
    have hcd : IsConj (D.vecE c) (D.vecE d) :=
      isConj_iff.mpr ⟨z0⁻¹, by rw [inv_inv]; exact hconj⟩
    exact hvc.trans hcd
  have hne1 : D.vecE d ≠ 1 := by
    intro h
    have hback : D.vecE c = z0 * D.vecE d * z0⁻¹ := by
      rw [← hconj]
      group
    have h1 : D.vecE c = 1 := by rw [hback, h, mul_one, mul_inv_cancel]
    exact vecE_ne_zero_of_mem_fusionJ3 D hc h1
  have hnt : ¬ IsConj D.t (D.vecE d) := fun h => D.not_isConj_t_v (h.trans hvd.symm)
  have hnu : ¬ IsConj D.u (D.vecE d) := fun h => huv (h.trans hvd.symm)
  have hnonzero : d ≠ 0 := by
    intro hd0
    exact hne1 (by rw [hd0, D.vecE_zero])
  rcases class_of_ne_zero D htu hnonzero with hJ3 | hT | hU
  · exact hJ3
  · exact absurd hT hnt
  · exact absurd hU hnu

theorem isConj_u_v_of_isConj_t_tu [Finite G]
    (htu : IsConj D.t (D.t * D.u)) : IsConj D.u D.v := by
  by_contra huv
  obtain ⟨z0, hz0N, hz0t⟩ := D.exists_mem_normalizer_E_conj_t_ne htu
  obtain ⟨ρ, hρ⟩ := D.exists_isBasisRep
  let g : normalizer (D.E : Set G) := ⟨z0, hz0N⟩
  let m : Matrix (Fin 4) (Fin 4) (ZMod 2) := (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 2))
  have hJ3mem : ∀ c ∈ fusionJ3, c ᵥ* m ∈ fusionJ3 := fun c hc =>
    mem_fusionJ3_vecMul_of_mem_fusionJ3 D hρ hz0N htu huv hc
  have hmem : ∀ a : Fin 4 → ZMod 2, a ∈ fusionJ3 → a ᵥ* m ∈ fusionJ3 := hJ3mem
  have hy : (![0, 0, 1, 0] : Fin 4 → ZMod 2) ᵥ* m ∈ fusionJ3 :=
    hJ3mem _ (by decide)
  have hz : (![0, 0, 0, 1] : Fin 4 → ZMod 2) ᵥ* m ∈ fusionJ3 :=
    hJ3mem _ (by decide)
  have hyz : (![0, 0, 1, 0] : Fin 4 → ZMod 2) ᵥ* m +
      (![0, 0, 0, 1] : Fin 4 → ZMod 2) ᵥ* m ∈ fusionJ3 := by
    have h := hJ3mem (![0, 0, 1, 0] + ![0, 0, 0, 1]) (by decide)
    rwa [Matrix.add_vecMul] at h
  have hxy : (![1, 0, 0, 0] : Fin 4 → ZMod 2) ᵥ* m +
      (![0, 0, 1, 0] : Fin 4 → ZMod 2) ᵥ* m ∈ fusionJ3 := by
    have h := hJ3mem (![1, 0, 0, 0] + ![0, 0, 1, 0]) (by decide)
    rwa [Matrix.add_vecMul] at h
  have hxz : (![1, 0, 0, 0] : Fin 4 → ZMod 2) ᵥ* m +
      (![0, 0, 0, 1] : Fin 4 → ZMod 2) ᵥ* m ∈ fusionJ3 := by
    have h := hJ3mem (![1, 0, 0, 0] + ![0, 0, 0, 1]) (by decide)
    rwa [Matrix.add_vecMul] at h
  have hxyz : (![1, 0, 0, 0] : Fin 4 → ZMod 2) ᵥ* m +
      (![0, 0, 1, 0] : Fin 4 → ZMod 2) ᵥ* m +
      (![0, 0, 0, 1] : Fin 4 → ZMod 2) ᵥ* m ∈ fusionJ3 := by
    have h := hJ3mem (![1, 0, 0, 0] + ![0, 0, 1, 0] + ![0, 0, 0, 1]) (by decide)
    rwa [Matrix.add_vecMul, Matrix.add_vecMul] at h
  have hxne : (![1, 0, 0, 0] : Fin 4 → ZMod 2) ᵥ* m ≠ 0 := by
    intro hx0
    have hconj0 : z0⁻¹ * D.t * z0 = 1 := by
      have h := hρ.conj_vecE g ![1, 0, 0, 0]
      rw [hx0] at h
      simpa [g, m, vecE_def, ZMod.val_zero, ZMod.val_one] using h
    have ht1 : D.t = 1 := by
      calc D.t = z0 * (z0⁻¹ * D.t * z0) * z0⁻¹ := by group
        _ = z0 * 1 * z0⁻¹ := by rw [hconj0]
        _ = 1 := by rw [mul_one, mul_inv_cancel]
    have h1 : orderOf D.t = 1 := by rw [ht1, orderOf_one]
    rw [D.orderOf_t] at h1
    omega
  have hxeq := eq_of_mem_fusionJ3 hy hz hyz hxy hxz hxyz hxne
  apply hz0t
  have hconj := hρ.conj_vecE g ![1, 0, 0, 0]
  rw [hxeq] at hconj
  simpa [g, m, vecE_def, ZMod.val_zero, ZMod.val_one] using hconj

theorem not_isConj_t_u_of_isConj_t_tu [Finite G] (htu : IsConj D.t (D.t * D.u)) :
    ¬ IsConj D.t D.u := by
  intro hTU
  exact D.not_isConj_t_v (hTU.trans (D.isConj_u_v_of_isConj_t_tu htu))

theorem isConj_t_or_u_of_isConj_t_tu [Finite G]
    (htu : IsConj D.t (D.t * D.u)) {x : G} (hx : orderOf x = 2) :
    IsConj D.t x ∨ IsConj D.u x := by
  have hXp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hxQ⟩ := hXp.exists_le_sylow
  obtain ⟨S0, hS0⟩ := D.isSylow_S
  have hpt : MulAction.IsPretransitive G (Sylow 2 G) :=
    @Sylow.isPretransitive_of_finite 2 G inferInstance Nat.fact_prime_two
      (Sylow.finite_of_finiteIndex Q)
  obtain ⟨g, hgQ⟩ := @MulAction.IsPretransitive.exists_smul_eq G (Sylow 2 G) _ hpt Q S0
  have hxS : g * x * g⁻¹ ∈ D.S := by
    have hxQ' : x ∈ (Q : Subgroup G) := hxQ (mem_zpowers x)
    have hmem := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup G) hxQ'
    rw [← Sylow.coe_subgroup_smul (g := g) (P := Q), hgQ, hS0] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hx2' : orderOf (g * x * g⁻¹) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g) x
    simp only [MulAut.conj_apply] at h
    rw [h, hx]
  have hx'C : g * x * g⁻¹ ∈ centralizer ({D.t} : Set G) := D.S_le_centralizer_t hxS
  have hxx' : IsConj x (g * x * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  by_cases hEq : g * x * g⁻¹ = D.t
  · left
    refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
    rw [inv_inv, ← hEq]
    group
  · by_cases hx'K : g * x * g⁻¹ ∈ D.K
    · right
      have hvx' : IsConj D.v (g * x * g⁻¹) := by
        obtain ⟨k, -, hk⟩ := D.exists_conj_v_of_mem_K hx'K hx2' hEq
        exact isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩
      exact (D.isConj_u_v_of_isConj_t_tu htu).trans hvx' |>.trans hxx'.symm
    · rcases D.exists_conj_of_not_mem_K hx'C hx2' hx'K with ⟨k, -, hk⟩ | ⟨k, -, hk⟩
      · right
        exact (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩).trans hxx'.symm
      · left
        exact (htu.trans (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv]; exact hk⟩)).trans hxx'.symm



end SwapData



end CFSG.OddTranspositions.PartThree.Wong

