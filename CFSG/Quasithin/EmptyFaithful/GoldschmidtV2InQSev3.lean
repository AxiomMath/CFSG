module

public import CFSG.Quasithin.EmptyFaithful.S151XC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace V2InQ

variable {G : Type} [Group G]

theorem exists_x0 [Finite G] {T M V : Subgroup G} {hVe : IsElemAbelian 2 V}
    (d : Seven7Data V M T hVe) :
    ∃ x : G, x ∈ M ∧ ∃ hx : x ∈ Subgroup.normalizer (V : Set G),
      (∃ i : ℕ, ¬ 3 ∣ i ∧ conjAct V ⟨x, hx⟩ = d.z ^ i) ∧ ∃ k : ℕ, orderOf x = 3 ^ k := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hVe
  have hzP : d.z ∈ oTwoUpper (autOn M V) := d.ctx.Z_le_P d.gen.zZ
  have hzA : d.z ∈ autOn M V := oTwoUpper_le _ hzP
  obtain ⟨m, hmN, hmM, hmz⟩ := mem_autOn_iff_exists.mp hzA
  have hord : orderOf m ≠ 0 := (orderOf_pos m).ne'
  obtain ⟨e, n', hn', hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord 3 (by norm_num)
  have hn'0 : n' ≠ 0 := fun h => by
    rw [h, mul_zero] at hN
    exact hord hN
  have hxord : orderOf (m ^ n') = 3 ^ e := by
    rw [orderOf_pow' m hn'0, hN]
    have hg : Nat.gcd (3 ^ e * n') n' = n' := Nat.gcd_eq_right (dvd_mul_left n' (3 ^ e))
    rw [hg]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn'0)
  have hxN : m ^ n' ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hmN n'
  refine ⟨m ^ n', M.pow_mem hmM n', hxN, ⟨n', hn', ?_⟩, ⟨e, hxord⟩⟩
  have : (⟨m ^ n', hxN⟩ : Subgroup.normalizer (V : Set G)) =
      (⟨m, hmN⟩ : Subgroup.normalizer (V : Set G)) ^ n' := rfl
  rw [this, map_pow, hmz]

theorem mem_normalizer_of_odd_conj {H L : Subgroup G} (hLH : L ≤ H) {x : G} (hxH : x ∈ H)
    (hodd : Odd (orderOf x))
    (hL : (L.subgroupOf H).Normal ∨ Set.ncard (conjSubgroupsBy H L) = 2) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  rcases hL with hn | hcard
  · exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).1 hn) hxH
  by_contra hnot
  have hcomp : ∀ a b : G, (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj (b * a)).toMonoidHom := by
    intro a b
    rw [Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hone : L.map (MulAut.conj (1 : G)).toMonoidHom = L := by
    ext g
    simp [Subgroup.mem_map]
  have hxL : L.map (MulAut.conj x).toMonoidHom ≠ L := fun h =>
    hnot (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)
  obtain ⟨K₁, K₂, hne, hS⟩ := Set.ncard_eq_two.1 hcard
  have hmem : ∀ t ∈ H, L.map (MulAut.conj t).toMonoidHom = K₁ ∨
      L.map (MulAut.conj t).toMonoidHom = K₂ := fun t ht => by
    have : L.map (MulAut.conj t).toMonoidHom ∈ conjSubgroupsBy H L := ⟨t, ht, rfl⟩
    rw [hS] at this
    exact this
  have h0 := hmem 1 H.one_mem
  have h1 := hmem x hxH
  have h2 := hmem (x * x) (H.mul_mem hxH hxH)
  rw [hone] at h0
  have hne12 : L.map (MulAut.conj (x * x)).toMonoidHom ≠ L.map (MulAut.conj x).toMonoidHom := by
    intro h
    apply hxL
    have h3 := congrArg (fun K : Subgroup G => K.map (MulAut.conj x⁻¹).toMonoidHom) h
    rw [hcomp (x * x) x⁻¹, hcomp x x⁻¹, inv_mul_cancel, hone,
      show x⁻¹ * (x * x) = x by group] at h3
    exact h3
  have hx2 : L.map (MulAut.conj (x * x)).toMonoidHom = L := by
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      first
        | exact h2.trans h0.symm
        | (exfalso; apply hxL; exact h1.trans h0.symm)
        | (exfalso; apply hne12; exact h2.trans h1.symm)
  have hx2N : x * x ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hx2
  obtain ⟨k, hk⟩ := hodd
  have hxk : x ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hxeq : x = ((x * x) ^ k)⁻¹ := by
    have : x ^ (2 * k + 1) = (x * x) ^ k * x := by
      rw [pow_succ, pow_mul, pow_two]
    rw [this] at hxk
    exact (eq_inv_of_mul_eq_one_right hxk)
  apply hnot
  rw [hxeq]
  exact (Subgroup.normalizer (L : Set G)).inv_mem ((Subgroup.normalizer (L : Set G)).pow_mem hx2N k)

theorem normalizes_L_of_odd [Finite G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L) {x : G}
    (hxN : x ∈ Subgroup.normalizer (Z₁ : Set G)) (hodd : Odd (orderOf x)) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  have hS := hc.ctx.setting
  set H : Subgroup G := Subgroup.normalizer (Z₁ : Set G) with hHdef
  have hCH : g1_1516 Z₁ ≤ H := Subgroup.centralizer_le_normalizer _
  have hsub : IsSubnormal (g1_1516 Z₁) H :=
    A3.subnormal_of_normal hCH
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr
        (normalizer_le_normalizer_centralizer Z₁))
  have hLcH : L ∈ cComp H := cComp_mem_of_subnormal hsub hc.hL.comp
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hZ1ab : IsElemAbelian 2 Z₁ :=
    isElemAbelian_mono151 (hS.z1_le.trans inf_le_left) (hS.V_isElemAbelian hc.ctx.qtfe hc.ctx.mf)
  have hpc : pCoreOf 2 H ≠ ⊥ := by
    intro h0
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : Z₁ ≤ H) le_rfl (isPGroup_of_isElemAbelian hZ1ab)
    rw [h0] at this
    exact hS.z1_ne (le_bot_iff.mp this)
  have h123 := lemma_1_2_1_three hc.ctx.qtfe.qtke hc.ctx.qtfe.simple hc.ctx.qtfe.nonabelian
    h37 h38 hpc hLcH
  exact mem_normalizer_of_odd_conj (hLG.trans hCH) hxN hodd (h123.imp_right And.left)

end V2InQ

end CFSG.Quasithin
