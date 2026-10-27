module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKGL

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.L829N CFSG.RankThree.SubgroupLists

theorem nk_isTransvectionK_conj {K : Type} [Field K] {n : ℕ} {t : GL (Fin n) K}
    (ht : IsTransvectionK t) (x : GL (Fin n) K) : IsTransvectionK (x * t * x⁻¹) := by
  unfold IsTransvectionK at ht ⊢
  obtain ⟨ht1, htsq, htr⟩ := ht
  have hx : IsUnit (x : Matrix (Fin n) (Fin n) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp x.isUnit
  have hxi : IsUnit ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (x⁻¹ : GL (Fin n) K).isUnit
  have hM : ((x * t * x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      (x : Matrix (Fin n) (Fin n) K) * ((t : Matrix (Fin n) (Fin n) K) - 1) *
        ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simp only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.mul_inv, mul_assoc]
  have hCA : ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (x : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.inv_mul x
  have key : ∀ A B C : Matrix (Fin n) (Fin n) K, C * A = 1 →
      A * B * C * (A * B * C) = A * (B * B) * C := by
    intro A B C h
    calc A * B * C * (A * B * C) = A * B * (C * A) * B * C := by simp only [mul_assoc]
      _ = A * (B * B) * C := by rw [h]; simp only [mul_one, mul_assoc]
  refine ⟨fun h => ht1 (conj_eq_one_iff.mp h), ?_, ?_⟩
  · rw [hM, key _ _ _ hCA, htsq]
    simp
  · rw [hM, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hxi,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hx, htr]

theorem nk_transvection_sq {E : Type} [Field E] [CharP E 2] {n : ℕ} {t : GL (Fin n) E}
    (ht : IsTransvectionK t) : t * t = 1 := by
  obtain ⟨-, hsq, -⟩ := ht
  have h2 : (2 : Matrix (Fin n) (Fin n) E) = 0 := by
    have h2K : (2 : E) = 0 := by
      have := CharP.cast_eq_zero E 2
      simpa using this
    have : (2 : Matrix (Fin n) (Fin n) E) = algebraMap E (Matrix (Fin n) (Fin n) E) 2 :=
      (map_ofNat (algebraMap E (Matrix (Fin n) (Fin n) E)) 2).symm
    rw [this, h2K, map_zero]
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  set T : Matrix (Fin n) (Fin n) E := (t : Matrix (Fin n) (Fin n) E) with hT
  have e : T * T = (T - 1) * (T - 1) + (2 : Matrix (Fin n) (Fin n) E) * T - 1 := by
    noncomm_ring
  rw [e, hsq, h2]
  have h11 : (1 : Matrix (Fin n) (Fin n) E) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  calc (0 : Matrix (Fin n) (Fin n) E) + 0 * T - 1 = -1 := by simp
    _ = 1 := by
      have : (-1 : Matrix (Fin n) (Fin n) E) = 1 := by
        calc (-1 : Matrix (Fin n) (Fin n) E) = -1 + (1 + 1) := by rw [h11, add_zero]
          _ = 1 := by abel
      exact this

theorem nk_s9_replacement (hSch : NKLeafSchurL32) (hSL3 : NKLeafSL3Rep)
    (hConj : ∀ (X : Type) [Group X], IsPSL 3 2 1 X → ∀ a b : X, orderOf a = 2 → orderOf b = 2 →
      IsConj a b)
    {E : Type} [Field E] [Finite E] [CharP E 2] (hE : Nat.card E = 2 ∨ Nat.card E = 4) {n : ℕ}
    (Kb Nb : Subgroup (GL (Fin n) E)) (hKN : Kb ≤ Nb)
    (hnorm : ∀ g ∈ Nb, ∀ k ∈ Kb, g * k * g⁻¹ ∈ Kb) (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn Nb)
    (tb : GL (Fin n) E) (htb : IsTransvectionK tb) (htbN : tb ∈ Nb)
    (hgen : Nb = Subgroup.closure {x | ∃ k ∈ Kb, x = k * tb * k⁻¹})
    (hinner : ∃ kb ∈ Kb, ∀ x ∈ Kb, tb * x * tb⁻¹ = kb * x * kb⁻¹)
    {Ks : Type} [Group Ks] (hKs3 : IsPSL 3 2 1 Ks)
    (πb : ↥Kb →* Ks) (hπ : Function.Surjective πb) (hperf : commutator ↥Kb = ⊤)
    (hcenK : ∀ z : ↥Kb, πb z = 1 → ∀ x : ↥Kb, x * z = z * x) :
    ∃ hn : n = 3, ∃ P : GL (Fin n) E, ∀ g : GL (Fin n) E, g ∈ Nb ↔
      ∃ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.det = 1 ∧
        ((P * g * P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
          (M.map (fun a : ZMod 2 => ((a.val : ℕ) : E))).submatrix (Fin.cast hn) (Fin.cast hn) := by
  haveI : Finite (GL (Fin n) E) := inferInstance
  obtain ⟨kb, hkb, hinn⟩ := hinner
  set c : GL (Fin n) E := kb⁻¹ * tb with hc
  have hcK : ∀ x ∈ Kb, c * x = x * c := by
    intro x hx
    have h0 := hinn x hx
    have h1 : c * x * c⁻¹ = x := by
      rw [hc]
      calc kb⁻¹ * tb * x * (kb⁻¹ * tb)⁻¹ = kb⁻¹ * (tb * x * tb⁻¹) * kb := by group
        _ = kb⁻¹ * (kb * x * kb⁻¹) * kb := by rw [h0]
        _ = x := by group
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [h1]
  have htbkc : tb = kb * c := by rw [hc]; group
  have hct : c * tb = tb * c := by
    have hcb : c * kb = kb * c := hcK kb hkb
    calc c * tb = c * (kb * c) := by rw [← htbkc]
      _ = (c * kb) * c := by group
      _ = (kb * c) * c := by rw [hcb]
      _ = tb * c := by rw [← htbkc]
  have hcN : ∀ g ∈ Nb, c * g = g * c := by
    have hsub : Nb ≤ Subgroup.centralizer ({c} : Set (GL (Fin n) E)) := by
      rw [hgen, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      have hck := hcK k hk
      calc c * (k * tb * k⁻¹) = (c * k) * tb * k⁻¹ := by group
        _ = (k * c) * tb * k⁻¹ := by rw [hck]
        _ = k * (c * tb) * k⁻¹ := by group
        _ = k * (tb * c) * k⁻¹ := by rw [hct]
        _ = k * tb * (c * k⁻¹) := by group
        _ = k * tb * k⁻¹ * c := by
          have : c * k⁻¹ = k⁻¹ * c := by
            have h2 : k * c = c * k := hck.symm
            calc c * k⁻¹ = k⁻¹ * (k * c) * k⁻¹ := by group
              _ = k⁻¹ * (c * k) * k⁻¹ := by rw [h2]
              _ = k⁻¹ * c := by group
          rw [this]
          group
    intro g hg
    exact Subgroup.mem_centralizer_iff.mp (hsub hg) c (Set.mem_singleton c)
  have hodd := nk_centralizer_odd_order Nb hirr c hcN
  have hcr : c ^ (orderOf c) = 1 := pow_orderOf_eq_one c
  have hkc : Commute kb c := (hcK kb hkb).symm
  have hsq := nk_transvection_sq htb
  have htr : tb = kb ^ (orderOf c) := by
    obtain ⟨m, hm⟩ := hodd
    have h1 : tb ^ (orderOf c) = kb ^ (orderOf c) := by
      rw [htbkc, hkc.mul_pow, hcr, mul_one]
    have h2 : tb ^ (orderOf c) = tb := by
      rw [hm, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
    rw [← h1, h2]
  have htK : tb ∈ Kb := by rw [htr]; exact Kb.pow_mem hkb _
  have hNK : Nb = Kb := by
    refine le_antisymm ?_ hKN
    rw [hgen, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact Kb.mul_mem (Kb.mul_mem hk htK) (Kb.inv_mem hk)
  have hzodd : ∀ z ∈ πb.ker, Odd (orderOf z) := by
    intro z hz
    have hzc : ∀ g ∈ Nb, (z : GL (Fin n) E) * g = g * (z : GL (Fin n) E) := by
      intro g hg
      have hgK : g ∈ Kb := hNK ▸ hg
      have := hcenK z (MonoidHom.mem_ker.mp hz) ⟨g, hgK⟩
      exact (congrArg Subtype.val this).symm
    have := nk_centralizer_odd_order Nb hirr (z : GL (Fin n) E) hzc
    rwa [Subgroup.orderOf_coe] at this
  have hinj : Function.Injective πb :=
    hSch ↥Kb Ks hperf hKs3 πb hπ (fun z hz g => hcenK z (MonoidHom.mem_ker.mp hz) g) hzodd
  let e : ↥Kb ≃* Ks := MulEquiv.ofBijective πb ⟨hinj, hπ⟩
  let e' : ↥Nb ≃* Ks := (MulEquiv.subgroupCongr hNK).trans e
  have htbord : orderOf tb = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) htb.1
  have hinvol : ∀ g ∈ Nb, orderOf g = 2 → IsTransvectionK g := by
    intro g hg hgo
    have h1 : orderOf (e' ⟨g, hg⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hgo
    have h2 : orderOf (e' ⟨tb, htbN⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact htbord
    obtain ⟨c₁, hc₁⟩ := isConj_iff.mp (hConj Ks hKs3 _ _ h1 h2)
    set x : ↥Nb := e'.symm c₁ with hx
    have hxe : x * ⟨g, hg⟩ * x⁻¹ = ⟨tb, htbN⟩ := by
      apply e'.injective
      rw [map_mul, map_mul, map_inv, hx, MulEquiv.apply_symm_apply, hc₁]
    have hgt : (x : GL (Fin n) E) * g * (x : GL (Fin n) E)⁻¹ = tb := by
      have := congrArg Subtype.val hxe
      simpa using this
    have hg' : g = (x : GL (Fin n) E)⁻¹ * tb * (x : GL (Fin n) E) := by
      rw [← hgt]
      group
    rw [hg']
    have := nk_isTransvectionK_conj htb (x : GL (Fin n) E)⁻¹
    simpa using this
  exact hSL3 E hE n Nb hirr hinvol ⟨Ks, inferInstance, hKs3, ⟨e'⟩⟩

end CFSG.Quasithin.H13.L829NK
