module

public import CFSG.CGT.PushingUpLit.SolK.ModData
public import CFSG.CGT.PushingUpLit.SolK.ThreeBlock
public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PGroup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Open CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin CFSG.Quasithin.G6
  CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def HyperplaneRigid (A : Subgroup G) : Prop :=
  ∀ x : G, (∃ k : ℕ, orderOf x = 2 ^ k) → ∀ D : Subgroup G, D ≤ A → D.relIndex A = 2 →
    (∀ d ∈ D, d * x = x * d) → ∀ a ∈ A, a * x = x * a

theorem exists_relIndex_two_of_lt {N A : Subgroup G} (hA : IsPGroup 2 ↥A) (hNA : N ≤ A)
    (hne : N ≠ A) : ∃ D : Subgroup G, N ≤ D ∧ D ≤ A ∧ D.relIndex A = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (hA.to_le hNA).exists_card_eq
  obtain ⟨b, hb⟩ := hA.exists_card_eq
  have hab : a < b := by
    have hle : a ≤ b := by
      have := Subgroup.card_le_of_le hNA
      rw [ha, hb] at this
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    refine lt_of_le_of_ne hle fun h => hne ?_
    refine Subgroup.eq_of_le_of_card_ge hNA ?_
    rw [ha, hb, h]
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  obtain ⟨K, hK, hNK, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := c) (H := N) (L := A) (by rw [ha]; exact pow_dvd_pow 2 (by omega))
    (by rw [hb]; exact pow_dvd_pow 2 (Nat.le_succ c)) hNA
  refine ⟨K, hNK, hKA, ?_⟩
  have h : K.relIndex A * Nat.card ↥K = Nat.card ↥A := by
    have := Subgroup.relIndex_mul_card (H := K) (K := A)
    rwa [inf_eq_left.2 hKA] at this
  rw [hK, hb] at h
  have h' : K.relIndex A * 2 ^ c = 2 * 2 ^ c := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h'

private theorem modData_W_eq_blockU {X : Subgroup G} {n : ℕ} (D : ModData G X n) :
    D.W = blockU X := by
  rw [D.W_eq]
  rfl

private theorem conj_mem_modData_W {X : Subgroup G} {n : ℕ} (D : ModData G X n) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {w : G} (hw : w ∈ D.W) :
    g * w * g⁻¹ ∈ D.W := by
  rw [modData_W_eq_blockU D] at hw ⊢
  exact conj_mem_blockU hg hw

private theorem mem_zpowers_eq_one_or_self {H : Type*} [Group H] {x : H} (hx : x ^ 2 = 1)
    (hx1 : x ≠ 1) : ∀ y ∈ Subgroup.zpowers x, y = 1 ∨ y = x := by
  intro y hy
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hord : orderOf x = 2 := orderOf_eq_prime hx hx1
  have hxm : x ^ m = x ^ (m % (2 : ℤ)) := by
    rw [← zpow_mod_orderOf x m, hord]
    rfl
  rw [← hm, hxm]
  have hmod : m % (2 : ℤ) = 0 ∨ m % (2 : ℤ) = 1 := by omega
  rcases hmod with h | h <;> rw [h]
  · left; exact zpow_zero x
  · right; exact zpow_one x

theorem exists_hyperplane_fixed_vector {d : ℕ} (hd : Odd d)
    (P : Subgroup (Equiv.Perm (Fin d))) (hP : IsElemAbelian 2 P) (hP1 : P ≠ ⊥) :
    ∃ D : Subgroup (Equiv.Perm (Fin d)), D ≤ P ∧ D.relIndex P = 2 ∧
      ∃ w : ↥(coreMod d), (∀ σ ∈ D, coreAct d σ w = w) ∧ ∃ σ ∈ P, coreAct d σ w ≠ w := by
  classical
  obtain ⟨σ, hσP, hσ1⟩ : ∃ σ ∈ P, σ ≠ 1 := by
    obtain ⟨σ, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
    exact ⟨σ, σ.2, fun h => hσ1 (Subtype.ext h)⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin d, σ j ≠ j := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  set N : Subgroup (Equiv.Perm (Fin d)) :=
    P ⊓ MulAction.stabilizer (Equiv.Perm (Fin d)) j with hN
  have hNP : N ≤ P := inf_le_left
  have hNne : N ≠ P := by
    intro h
    have hσN : σ ∈ N := h ▸ hσP
    exact hj (by
      have h2 := (Subgroup.mem_inf.1 hσN).2
      rwa [MulAction.mem_stabilizer_iff] at h2)
  obtain ⟨D, hND, hDP, hDrel⟩ := exists_relIndex_two_of_lt hP.isPGroup hNP hNne
  obtain ⟨b, hbP, hbD, -⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.1 hDrel
  have horb_ne : orbOf D (b j) ≠ orbOf D j := by
    intro h
    obtain ⟨a, haD, haj⟩ := orbOf_eq_iff.1 h
    have hbaN : b⁻¹ * a ∈ N := by
      have h1 : b⁻¹ * a ∈ P := P.mul_mem (P.inv_mem hbP) (hDP haD)
      have h2 : (b⁻¹ * a) • j = j := by
        show (b⁻¹ * a) j = j
        rw [Equiv.Perm.mul_apply, haj]
        simp
      exact hN ▸ Subgroup.mem_inf.mpr ⟨h1, MulAction.mem_stabilizer_iff.mpr h2⟩
    have : b ∈ D := by
      have h1 : b = a * (b⁻¹ * a)⁻¹ := by group
      rw [h1]
      exact D.mul_mem haD (D.inv_mem (hND hbaN))
    exact hbD this
  have horb_eq : orbOf P (b j) = orbOf P j := orbOf_apply hbP j
  let f : OrbQ D → OrbQ P := Quotient.lift (fun x => orbOf P x)
    (fun x y h => by
      have h' : orbOf D x = orbOf D y := Quotient.sound h
      obtain ⟨a, haD, hay⟩ := orbOf_eq_iff.1 h'
      rw [← hay, orbOf_apply (hDP haD) y])
  have hf_apply : ∀ x, f (orbOf D x) = orbOf P x := fun x => rfl
  have hf_surj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := orbOf_surjective P q
    exact ⟨orbOf D x, hf_apply x⟩
  have hf_not_inj : ¬ Function.Injective f := by
    intro hinj
    exact horb_ne (hinj (by rw [hf_apply, hf_apply, horb_eq]))
  have hcard_orbit : Nat.card (OrbQ P) < Nat.card (OrbQ D) := by
    have h := Fintype.card_lt_of_surjective_not_injective f hf_surj hf_not_inj
    rwa [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  have hcardP := card_fixV_mul_two hd P
  have hcardD := card_fixV_mul_two hd D
  have hlt : Nat.card ↥(fixV (P.map (coreAct d))) < Nat.card ↥(fixV (D.map (coreAct d))) := by
    have h2 : 2 ^ Nat.card (OrbQ P) < 2 ^ Nat.card (OrbQ D) :=
      Nat.pow_lt_pow_right (by norm_num) hcard_orbit
    rw [← hcardP, ← hcardD] at h2
    omega
  have hnotle : ¬ fixV (D.map (coreAct d)) ≤ fixV (P.map (coreAct d)) := by
    intro h
    have := Subgroup.card_le_of_le h
    omega
  obtain ⟨w, hwD, hwP⟩ := Set.not_subset.1 hnotle
  refine ⟨D, hDP, hDrel, w, ?_, ?_⟩
  · intro τ hτ
    exact (mem_fixV.mp hwD) _ (Subgroup.mem_map_of_mem _ hτ)
  · have hwP' := mem_fixV.not.mp hwP
    push Not at hwP'
    obtain ⟨x, hx, hxw⟩ := hwP'
    obtain ⟨τ, hτP, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨τ, hτP, hxw⟩

theorem natAlt_block_facts {X : Subgroup G} {n : ℕ} (hX : IsShortGroup ↥X) (hn : 1 ≤ n)
    (hnat : IsNaturalAltModule ↥X n) :
    IsElemAbelian 2 (blockU X) ∧ blockU X ≠ ⊥ ∧ blockZ X = ⊥ ∧
      X ⊓ Subgroup.centralizer (blockU X : Set G) ≤ pCoreOf 2 X := by
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    obtain ⟨a, haX, ha3, hdec, hab, hsq, hcardR, hfix⟩ := three_block_ambient hX hnat
    have hRelem : IsElemAbelian 2 (pCoreOf 2 X) :=
      ⟨IsMulCommutative.of_comm (fun y y' => Subtype.ext (hab y y.2 y' y'.2)),
        fun y hy => by rw [pow_two]; exact hsq y hy⟩
    have hWne : blockU X ≠ ⊥ := blockU_ne_bot_of_short hX
    have hWR : blockU X ≤ pCoreOf 2 X := blockU_le_oTwoIn X
    have hu₀ : ∃ u ∈ blockU X, u ≠ 1 := by
      obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
      exact ⟨u, u.2, fun h => hu1 (Subtype.ext h)⟩
    obtain ⟨u, huW, hu1⟩ := hu₀
    have husq : u ^ 2 = 1 := by rw [pow_two]; exact hsq u (hWR huW)
    have hupair := mem_zpowers_eq_one_or_self husq hu1
    have horder : orderOf u = 2 := orderOf_eq_prime husq hu1
    have ha_moves : a * u * a⁻¹ ≠ u := by
      intro h
      exact hu1 (hfix u (hWR huW) h)
    refine ⟨hRelem.mono hWR, hWne, ?_, ?_⟩
    · apply le_bot_iff.mp
      intro z hz
      obtain ⟨hzW, hzC⟩ := hz
      have hzR : z ∈ pCoreOf 2 X := hWR hzW
      have haz : a * z * a⁻¹ = z := by
        have hcomm := (Subgroup.mem_centralizer_iff.1 hzC) a haX
        rw [show a * z * a⁻¹ = z from by rw [hcomm]; group]
      exact hfix z hzR haz
    · intro x hx
      obtain ⟨hxX, hxC⟩ := hx
      obtain ⟨y, hyR, j, hxy⟩ := hdec x hxX
      have hxord : orderOf a = 3 := orderOf_eq_prime ha3 (by
        intro h; rw [h] at ha_moves; exact ha_moves (by group))
      have hyC : y ∈ Subgroup.centralizer (blockU X : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact hab w (hWR hw) y hyR
      have hxy' : x = y * a ^ (j % 3) := by
        rw [hxy, ← pow_mod_orderOf a j, hxord]
      have hajC : a ^ (j % 3) ∈ Subgroup.centralizer (blockU X : Set G) := by
        rw [hxy'] at hxC
        have := (Subgroup.centralizer (blockU X : Set G)).mul_mem
          ((Subgroup.centralizer (blockU X : Set G)).inv_mem hyC) hxC
        simpa [mul_assoc] using this
      have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
      rcases hcases with h | h | h
      · have : x = y := by rw [hxy', h, pow_zero, mul_one]
        rw [this]; exact hyR
      · exfalso
        have haC : a ∈ Subgroup.centralizer (blockU X : Set G) := by
          have h1 : a ^ (j % 3) = a := by rw [h, pow_one]
          rwa [h1] at hajC
        have hcomm := (Subgroup.mem_centralizer_iff.1 haC) u huW
        exact ha_moves (by rw [← hcomm]; group)
      · exfalso
        have haC : a ^ 2 ∈ Subgroup.centralizer (blockU X : Set G) := by
          have h1 : a ^ (j % 3) = a ^ 2 := by rw [h]
          rwa [h1] at hajC
        have haC' : a ∈ Subgroup.centralizer (blockU X : Set G) := by
          have h3 : a ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one a
          have h2 : a = (a ^ 2)⁻¹ := by
            have hmul : a * a ^ 2 = 1 := by
              rw [show a * a ^ 2 = a ^ 3 from by group, h3]
            exact eq_inv_of_mul_eq_one_left hmul
          rw [h2]
          exact (Subgroup.centralizer (blockU X : Set G)).inv_mem haC
        have hcomm := (Subgroup.mem_centralizer_iff.1 haC') u huW
        exact ha_moves (by rw [← hcomm]; group)
  · obtain ⟨D⟩ := exists_modData hX hn2 hnat
    have hW : D.W = blockU X := modData_W_eq_blockU D
    have h6 : 3 ≤ 2 * n + 1 := by omega
    have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
    have hWelem : IsElemAbelian 2 (blockU X) := by
      rw [← hW]
      exact ⟨IsMulCommutative.of_comm (fun p q => Subtype.ext (D.comm p.2 q.2)),
        fun p hp => D.sq hp⟩
    have hWne : blockU X ≠ ⊥ := blockU_ne_bot_of_short hX
    refine ⟨hWelem, hWne, ?_, ?_⟩
    · apply le_bot_iff.mp
      intro z hz
      obtain ⟨hzU, hzC⟩ := hz
      have hzW : z ∈ D.W := hW ▸ hzU
      have hzC' : z ∈ Subgroup.centralizer (X : Set G) := hzC
      have hβz : D.β ⟨z, hzW⟩ = D.β ⟨z, hzW⟩ := rfl
      have hfixv : ∀ σ ∈ alternatingGroup (Fin (2 * n + 1)),
          coreAct (2 * n + 1) σ (D.β ⟨z, hzW⟩) = D.β ⟨z, hzW⟩ := by
        intro σ hσ
        obtain ⟨x, hx⟩ := D.ρ_surj σ hσ
        have hcomm := (Subgroup.mem_centralizer_iff.1 hzC') (x : G) x.2
        have hxw : (x : G) * z * (x : G)⁻¹ = z := by rw [hcomm]; group
        have hmem : (x : G) * z * (x : G)⁻¹ ∈ D.W := by rw [hxw]; exact hzW
        have hsub : (⟨(x : G) * z * (x : G)⁻¹, hmem⟩ : ↥D.W) = ⟨z, hzW⟩ := Subtype.ext hxw
        have heq : D.β (⟨(x : G) * z * (x : G)⁻¹, hmem⟩ : ↥D.W)
            = coreAct (2 * n + 1) (D.ρ x) (D.β ⟨z, hzW⟩) := D.equivar x ⟨z, hzW⟩ hmem
        rw [hsub] at heq
        rw [hx] at heq
        exact heq.symm
      have hconst : ∀ i j, vcoord (D.β ⟨z, hzW⟩) i = vcoord (D.β ⟨z, hzW⟩) j := by
        intro i j
        obtain ⟨σ, hσ, hσj⟩ := exists_alt_apply_eq h6 j i
        have h2 := congrArg (fun w => vcoord w i) (hfixv σ hσ)
        rw [vcoord_coreAct] at h2
        have hσi : σ⁻¹ i = j := by rw [← hσj]; simp
        rw [hσi] at h2
        exact h2.symm
      have hvzero : D.β ⟨z, hzW⟩ = 1 := by
        apply vcoord_ext
        intro i
        rw [vcoord_one]
        have hsum := sum_vcoord (D.β ⟨z, hzW⟩)
        have hc : ∑ k, vcoord (D.β ⟨z, hzW⟩) k = (2 * n + 1) • vcoord (D.β ⟨z, hzW⟩) i := by
          rw [Finset.sum_congr rfl (fun k _ => hconst k i)]
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [hc] at hsum
        rwa [nsmul_eq_mul, hodd.natCast_zmod_two, one_mul] at hsum
      have h1 : (⟨z, hzW⟩ : ↥D.W) = 1 := D.β.injective (by rw [hvzero, map_one])
      simpa using congrArg Subtype.val h1
    · intro x hx
      obtain ⟨hxX, hxC⟩ := hx
      have hxC' : x ∈ Subgroup.centralizer (blockU X : Set G) := hxC
      have hxW : ∀ w : ↥D.W, x * (w : G) * x⁻¹ = (w : G) := by
        intro w
        have hcomm := (Subgroup.mem_centralizer_iff.1 hxC') (w : G) (hW ▸ w.2)
        rw [← hcomm]; group
      have hρ1 : D.ρ ⟨x, hxX⟩ = 1 := by
        apply coreAct_injective h6
        rw [map_one]
        apply MulEquiv.ext
        intro d
        obtain ⟨w, rfl⟩ := D.β.surjective d
        have hmem : x * (w : G) * x⁻¹ ∈ D.W := by
          rw [hxW w]; exact w.2
        have hsub : (⟨x * (w : G) * x⁻¹, hmem⟩ : ↥D.W) = w :=
          Subtype.ext (hxW w)
        have heq : D.β (⟨x * (w : G) * x⁻¹, hmem⟩ : ↥D.W)
            = coreAct (2 * n + 1) (D.ρ ⟨x, hxX⟩) (D.β w) := D.equivar ⟨x, hxX⟩ w hmem
        rw [hsub] at heq
        exact heq.symm
      have := (D.ker ⟨x, hxX⟩).1 hρ1
      simpa using this

theorem exists_perm_hom_of_normalizer {X A : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (D : ModData G X n) (hA : A ≤ Subgroup.normalizer (X : Set G)) :
    ∃ f : ↥A →* Equiv.Perm (Fin (2 * n + 1)), ∀ (a : ↥A) (w : ↥D.W)
      (h : (a : G) * (w : G) * (a : G)⁻¹ ∈ D.W),
      D.β ⟨(a : G) * (w : G) * (a : G)⁻¹, h⟩ = coreAct (2 * n + 1) (f a) (D.β w) := by
  classical
  have hW : D.W = blockU X := modData_W_eq_blockU D
  have h6 : 3 ≤ 2 * n + 1 := by omega
  have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have h5 : 5 ≤ 2 * n + 1 := by omega
  have hAnorm : ∀ a : ↥A, (a : G) ∈ Subgroup.normalizer (D.W : Set G) := by
    intro a
    rw [hW, Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => conj_mem_blockU (hA a.2) hc, fun hc => ?_⟩
    have := conj_mem_blockU (hA (A.inv_mem a.2)) hc
    simpa [mul_assoc] using this
  let c (a : ↥A) : MulAut ↥D.W := Subgroup.normalizerMonoidHom D.W ⟨(a : G), hAnorm a⟩
  let y : ↥A → MulAut ↥(coreMod (2 * n + 1)) := fun a => (D.β.symm.trans (c a)).trans D.β
  have hy_apply : ∀ (a : ↥A) (w : ↥D.W),
      y a (D.β w) = D.β ⟨(a : G) * (w : G) * (a : G)⁻¹,
        conj_mem_modData_W D (hA a.2) w.2⟩ := by
    intro a w
    have h1 : y a (D.β w) = D.β (c a w) := by
      simp only [y, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [h1]
    exact congrArg D.β (Subtype.ext rfl)
  have hy_mul : ∀ (a b : ↥A) (d : ↥(coreMod (2 * n + 1))), y (a * b) d = y a (y b d) := by
    intro a b d
    obtain ⟨w, rfl⟩ := D.β.surjective d
    rw [hy_apply b w,
      hy_apply a ⟨(b : G) * (w : G) * (b : G)⁻¹, conj_mem_modData_W D (hA b.2) w.2⟩,
      hy_apply (a * b) w]
    exact congrArg D.β (Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group))
  have hy_norm : ∀ (a : ↥A), ∀ σ ∈ alternatingGroup (Fin (2 * n + 1)),
      ∃ σ' ∈ alternatingGroup (Fin (2 * n + 1)),
        ∀ d, y a (coreAct (2 * n + 1) σ d) = coreAct (2 * n + 1) σ' (y a d) := by
    intro a σ hσ
    obtain ⟨x, hx⟩ := D.ρ_surj σ hσ
    have hx'mem : (a : G) * (x : G) * (a : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.1 (hA a.2) (x : G)).1 x.2
    let x' : ↥X := ⟨(a : G) * (x : G) * (a : G)⁻¹, hx'mem⟩
    refine ⟨D.ρ x', D.ρ_alt _, ?_⟩
    intro d
    obtain ⟨w, rfl⟩ := D.β.surjective d
    have hxm : (x : G) * (w : G) * (x : G)⁻¹ ∈ D.W :=
      conj_mem_modData_W D (Subgroup.le_normalizer x.2) w.2
    have hσw : coreAct (2 * n + 1) σ (D.β w)
        = D.β ⟨(x : G) * (w : G) * (x : G)⁻¹, hxm⟩ := by
      rw [← hx]
      exact (D.equivar x w hxm).symm
    rw [hσw, hy_apply a ⟨(x : G) * (w : G) * (x : G)⁻¹, hxm⟩, hy_apply a w]
    rw [← D.equivar x' ⟨(a : G) * (w : G) * (a : G)⁻¹,
        conj_mem_modData_W D (hA a.2) w.2⟩
      (conj_mem_modData_W D (Subgroup.le_normalizer x'.2)
        (conj_mem_modData_W D (hA a.2) w.2))]
    exact congrArg D.β (Subtype.ext (by simp only [x']; group))
  have hy'_norm : ∀ (a : ↥A), ∀ σ' ∈ alternatingGroup (Fin (2 * n + 1)),
      ∃ σ ∈ alternatingGroup (Fin (2 * n + 1)),
        ∀ d, y a (coreAct (2 * n + 1) σ d) = coreAct (2 * n + 1) σ' (y a d) := by
    intro a σ' hσ'
    obtain ⟨x', hx'⟩ := D.ρ_surj σ' hσ'
    have hxmem : (a : G)⁻¹ * (x' : G) * (a : G) ∈ X := by
      have h := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem a.2)) (x' : G)).1 x'.2
      simpa using h
    refine ⟨D.ρ ⟨(a : G)⁻¹ * (x' : G) * (a : G), hxmem⟩, D.ρ_alt _, ?_⟩
    intro d
    obtain ⟨w, rfl⟩ := D.β.surjective d
    have hxm : ((a : G)⁻¹ * (x' : G) * (a : G)) * (w : G)
        * ((a : G)⁻¹ * (x' : G) * (a : G))⁻¹ ∈ D.W :=
      conj_mem_modData_W D (Subgroup.le_normalizer hxmem) w.2
    have hσw : coreAct (2 * n + 1) (D.ρ ⟨(a : G)⁻¹ * (x' : G) * (a : G), hxmem⟩) (D.β w)
        = D.β ⟨((a : G)⁻¹ * (x' : G) * (a : G)) * (w : G)
            * ((a : G)⁻¹ * (x' : G) * (a : G))⁻¹, hxm⟩ :=
      (D.equivar ⟨(a : G)⁻¹ * (x' : G) * (a : G), hxmem⟩ w hxm).symm
    rw [hσw, hy_apply a ⟨((a : G)⁻¹ * (x' : G) * (a : G)) * (w : G)
      * ((a : G)⁻¹ * (x' : G) * (a : G))⁻¹, hxm⟩, hy_apply a w]
    rw [← hx']
    rw [← D.equivar x' ⟨(a : G) * (w : G) * (a : G)⁻¹,
        conj_mem_modData_W D (hA a.2) w.2⟩
      (conj_mem_modData_W D (Subgroup.le_normalizer x'.2) (conj_mem_modData_W D (hA a.2) w.2))]
    exact congrArg D.β (Subtype.ext (by group))
  have hex : ∀ a : ↥A, ∃ π : Equiv.Perm (Fin (2 * n + 1)),
      ∀ d, y a d = coreAct (2 * n + 1) π d :=
    fun a => exists_perm_of_normalizes_alt hodd h5 (y a) (hy_norm a) (hy'_norm a)
  let f₀ : ↥A → Equiv.Perm (Fin (2 * n + 1)) := fun a => Classical.choose (hex a)
  have hf₀ : ∀ a d, y a d = coreAct (2 * n + 1) (f₀ a) d := fun a =>
    Classical.choose_spec (hex a)
  have hf₀' : ∀ a, y a = coreAct (2 * n + 1) (f₀ a) := fun a => MulEquiv.ext (hf₀ a)
  refine ⟨MonoidHom.mk' f₀ ?_, ?_⟩
  · intro a b
    apply coreAct_injective h6
    rw [map_mul, ← hf₀' (a * b), ← hf₀' a, ← hf₀' b]
    exact MulEquiv.ext (fun d => hy_mul a b d)
  · intro a w h
    have hcanon : D.β ⟨(a : G) * (w : G) * (a : G)⁻¹, h⟩
        = D.β ⟨(a : G) * (w : G) * (a : G)⁻¹, conj_mem_modData_W D (hA a.2) w.2⟩ :=
      congrArg D.β (Subtype.ext rfl)
    rw [hcanon, ← hy_apply a w]
    exact hf₀ a (D.β w)

theorem centralizes_blockU_of_hyperplaneRigid_of_two_le {X A : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hX : IsShortGroup ↥X) (hnat : IsNaturalAltModule ↥X n) (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hrigid : HyperplaneRigid A) :
    A ≤ Subgroup.centralizer (blockU X : Set G) := by
  classical
  obtain ⟨D⟩ := exists_modData hX hn hnat
  have hW : D.W = blockU X := modData_W_eq_blockU D
  obtain ⟨f, hf⟩ := exists_perm_hom_of_normalizer hn D hAX
  have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hP : IsElemAbelian 2 f.range := by
    rw [isElemAbelian_iff_isElementaryAbelian]
    refine IsElementaryAbelian.two_of_forall_mul_self (fun x hx y hy => ?_) (fun x hx => ?_)
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hy
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA.comm a.2 b.2)
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
      rw [← ha, ← map_mul, show a * a = 1 from Subtype.ext (by
        show (a : G) * (a : G) = 1
        rw [← pow_two]
        exact hA.2 a a.2), map_one]
  by_cases hPbot : f.range = ⊥
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hfa : f ⟨a, ha⟩ = 1 := by
      have hmem : f ⟨a, ha⟩ ∈ f.range := MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
      rw [hPbot] at hmem
      simpa using hmem
    have hua : a * u * a⁻¹ = u := by
      have hmem : a * u * a⁻¹ ∈ D.W := conj_mem_modData_W D (hAX ha) (hW ▸ hu)
      have := hf ⟨a, ha⟩ ⟨u, hW ▸ hu⟩ hmem
      rw [hfa, map_one, MulAut.one_apply] at this
      exact congrArg Subtype.val (D.β.injective this)
    have : a * u = u * a := by
      calc a * u = (a * u * a⁻¹) * a := by group
        _ = u * a := by rw [hua]
    exact this.symm
  · exfalso
    obtain ⟨Dbar, hDbarP, hDbarrel, w₀, hw₀fix, σ₀, hσ₀P, hσ₀ne⟩ :=
      exists_hyperplane_fixed_vector hodd f.range hP hPbot
    let A₀ : Subgroup G := (Dbar.comap f).map A.subtype
    have hA₀A : A₀ ≤ A := by
      have h := Subgroup.map_le_range (f := A.subtype) (H := Dbar.comap f)
      rwa [A.range_subtype] at h
    have hA₀rel : A₀.relIndex A = 2 := by
      have h1 : (Dbar.comap f).relIndex (⊤ : Subgroup ↥A) = Dbar.relIndex f.range := by
        rw [Subgroup.relIndex_comap, Subgroup.map_top]
      have h2 : A₀.relIndex A = (Dbar.comap f).relIndex (⊤ : Subgroup ↥A) := by
        have h := Subgroup.relIndex_map_map_of_injective (f := A.subtype)
          (Dbar.comap f) (⊤ : Subgroup ↥A) A.subtype_injective
        rw [Subgroup.map_top, A.range_subtype] at h
        exact h
      rw [h2, h1, hDbarrel]
    let x' : ↥D.W := D.β.symm w₀
    let x : G := x'
    have hxW : x ∈ D.W := x'.2
    have hβx : D.β ⟨x, hxW⟩ = w₀ := by
      have h : (⟨x, hxW⟩ : ↥D.W) = x' := Subtype.ext rfl
      rw [h]
      exact MulEquiv.apply_symm_apply D.β w₀
    have hxord : ∃ k : ℕ, orderOf x = 2 ^ k := by
      have hsq : x ^ 2 = 1 := D.sq hxW
      have hdvd : orderOf x ∣ 2 ^ 1 := by simpa using orderOf_dvd_iff_pow_eq_one.mpr hsq
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact ⟨k, hk⟩
    have hcomm : ∀ d ∈ A₀, d * x = x * d := by
      intro d hd
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hd
      have hfaD : f a ∈ Dbar := Subgroup.mem_comap.mp ha
      have hmem : (a : G) * x * (a : G)⁻¹ ∈ D.W :=
        conj_mem_modData_W D (hAX a.2) hxW
      have h1 : D.β ⟨(a : G) * x * (a : G)⁻¹, hmem⟩ = D.β ⟨x, hxW⟩ := by
        have heq : D.β (⟨(a : G) * x * (a : G)⁻¹, hmem⟩ : ↥D.W)
            = coreAct (2 * n + 1) (f a) w₀ := by
          rw [← hβx]
          exact hf a ⟨x, hxW⟩ hmem
        rw [heq, hw₀fix (f a) hfaD, ← hβx]
      have h2 : (a : G) * x * (a : G)⁻¹ = x := congrArg Subtype.val (D.β.injective h1)
      show (a : G) * x = x * (a : G)
      calc (a : G) * x = ((a : G) * x * (a : G)⁻¹) * (a : G) := by group
        _ = x * (a : G) := by rw [h2]
    have hcontr := hrigid x hxord A₀ hA₀A hA₀rel hcomm
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ↥A, f a₀ = σ₀ := MonoidHom.mem_range.mp hσ₀P
    have hmem₀ : (a₀ : G) * x * (a₀ : G)⁻¹ ∈ D.W :=
      conj_mem_modData_W D (hAX a₀.2) hxW
    apply hσ₀ne
    have hfix₀ : (a₀ : G) * x * (a₀ : G)⁻¹ = x := by
      have h := hcontr a₀ a₀.2
      rw [h]; group
    have heq₀ : D.β (⟨(a₀ : G) * x * (a₀ : G)⁻¹, hmem₀⟩ : ↥D.W)
        = coreAct (2 * n + 1) σ₀ w₀ := by
      rw [← hβx, ← ha₀]
      exact hf a₀ ⟨x, hxW⟩ hmem₀
    have hsub₀ : (⟨(a₀ : G) * x * (a₀ : G)⁻¹, hmem₀⟩ : ↥D.W) = ⟨x, hxW⟩ :=
      Subtype.ext hfix₀
    rw [hsub₀, hβx] at heq₀
    exact heq₀.symm

theorem centralizes_blockU_of_hyperplaneRigid_one {X A : Subgroup G}
    (hX : IsShortGroup ↥X) (hnat : IsNaturalAltModule ↥X 1) (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hrigid : HyperplaneRigid A) :
    A ≤ Subgroup.centralizer (blockU X : Set G) := by
  classical
  obtain ⟨a, haX, ha3, hdec, hab, hsq, hcardR, hfix⟩ := three_block_ambient hX hnat
  have hRelem : IsElemAbelian 2 (pCoreOf 2 X) :=
    ⟨IsMulCommutative.of_comm (fun y y' => Subtype.ext (hab y y.2 y' y'.2)),
      fun y hy => by rw [pow_two]; exact hsq y hy⟩
  have hWne : blockU X ≠ ⊥ := blockU_ne_bot_of_short hX
  have hWR : blockU X ≤ pCoreOf 2 X := blockU_le_oTwoIn X
  have hWelem : IsElemAbelian 2 (blockU X) := hRelem.mono hWR
  have hAnormW : A ≤ Subgroup.normalizer (blockU X : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => conj_mem_blockU (hAX hg) hc, fun hc => ?_⟩
    have := conj_mem_blockU (hAX (A.inv_mem hg)) hc
    simpa [mul_assoc] using this
  have hfixpt : blockU X ⊓ Subgroup.centralizer (A : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot Nat.prime_two hA.isPGroup hWelem.isPGroup hWne hAnormW
  obtain ⟨u₀, hu₀mem, hu₀1⟩ : ∃ u ∈ blockU X ⊓ Subgroup.centralizer (A : Set G), u ≠ 1 := by
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfixpt
    exact ⟨u, u.2, fun h => hu1 (Subtype.ext h)⟩
  have hu₀W : u₀ ∈ blockU X := hu₀mem.1
  have hAu₀ : ∀ g ∈ A, g * u₀ = u₀ * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.1 hu₀mem.2) g hg
  have hu₀sq : u₀ ^ 2 = 1 := by rw [pow_two]; exact hsq u₀ (hWR hu₀W)
  have hu₀sq' : u₀ * u₀ = 1 := hsq u₀ (hWR hu₀W)
  have horder : orderOf u₀ = 2 := orderOf_eq_prime hu₀sq hu₀1
  have hupair := mem_zpowers_eq_one_or_self hu₀sq hu₀1
  obtain ⟨k, hk⟩ := hWelem.isPGroup.exists_card_eq
  have hkne : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hWne ((Subgroup.eq_bot_iff_card (blockU X)).mpr hk)
  have hkle : k ≤ 2 := by
    have hle : 2 ^ k ≤ 2 ^ 2 := by
      rw [← hk, show (2 : ℕ) ^ 2 = 4 by norm_num, ← hcardR]
      exact Subgroup.card_le_of_le hWR
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hle
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with hk1 | hk2
  ·
    have hcard2 : Nat.card (blockU X) = 2 := by rw [hk, hk1]; norm_num
    have hUeq : blockU X = Subgroup.zpowers u₀ := by
      rw [eq_comm]
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]; exact hu₀W
      · simp [Nat.card_zpowers, horder, hcard2]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ Subgroup.zpowers u₀ := hUeq ▸ hw
    rcases hupair w hw' with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (hAu₀ g hg).symm
  ·
    have hcard4 : Nat.card (blockU X) = 4 := by rw [hk, hk2]; norm_num
    have hUeq : blockU X = pCoreOf 2 X := by
      apply Subgroup.eq_of_le_of_card_ge hWR
      simp [hcardR, hcard4]
    have hzpu₀R : Subgroup.zpowers u₀ ≤ pCoreOf 2 X := by
      rw [Subgroup.zpowers_le]; exact hWR hu₀W
    have hrelR : (Subgroup.zpowers u₀).relIndex (pCoreOf 2 X) = 2 := by
      have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers u₀) (K := pCoreOf 2 X)
      rw [inf_eq_left.2 hzpu₀R, Nat.card_zpowers, horder, hcardR] at h
      omega
    obtain ⟨v, hvR, hvz, hvprop⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hrelR
    have hv1 : v ≠ 1 := fun h => hvz (h ▸ Subgroup.one_mem _)
    have hvu₀ : v ≠ u₀ := fun h => hvz (h ▸ Subgroup.mem_zpowers u₀)
    have hvW : v ∈ blockU X := hUeq ▸ hvR
    have hvsq : v * v = 1 := hsq v hvR
    have hvsq2 : v ^ 2 = 1 := by rw [pow_two]; exact hvsq
    have hRenum : ∀ b ∈ pCoreOf 2 X, b = 1 ∨ b = u₀ ∨ b = v ∨ b = u₀ * v := by
      intro b hb
      rcases hvprop b hb with h | h
      · rcases hupair (b * v) h with h1 | h1
        · have hb1 : b = v := by
            calc b = b * (v * v) := by rw [hvsq, mul_one]
              _ = (b * v) * v := by group
              _ = v := by rw [h1, one_mul]
          exact Or.inr (Or.inr (Or.inl hb1))
        · have hb1 : b = u₀ * v := by
            calc b = b * (v * v) := by rw [hvsq, mul_one]
              _ = (b * v) * v := by group
              _ = u₀ * v := by rw [h1]
          exact Or.inr (Or.inr (Or.inr hb1))
      · rcases hupair b h with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
    have hφmem : ∀ g ∈ A, g * v * g⁻¹ * v⁻¹ = 1 ∨ g * v * g⁻¹ * v⁻¹ = u₀ := by
      intro g hg
      have hgvR : g * v * g⁻¹ ∈ pCoreOf 2 X := by
        have hh : g * v * g⁻¹ ∈ blockU X := conj_mem_blockU (hAX hg) hvW
        rwa [hUeq] at hh
      have hgne1 : g * v * g⁻¹ ≠ 1 := by
        intro h
        apply hv1
        calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [h]
          _ = 1 := by group
      have hgneu₀ : g * v * g⁻¹ ≠ u₀ := by
        intro h
        apply hvu₀
        have hconj : g⁻¹ * u₀ * g = u₀ := by
          have hh := hAu₀ g hg
          calc g⁻¹ * u₀ * g = g⁻¹ * (u₀ * g) := by group
            _ = g⁻¹ * (g * u₀) := by rw [← hh]
            _ = u₀ := by group
        calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
          _ = g⁻¹ * u₀ * g := by rw [h]
          _ = u₀ := hconj
      rcases hRenum _ hgvR with h | h | h | h
      · exact absurd h hgne1
      · exact absurd h hgneu₀
      · left; rw [h]; group
      · right; rw [h]; group
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwR : w ∈ pCoreOf 2 X := hUeq ▸ hw
    have hgv : g * v * g⁻¹ = v := by
      by_contra hgv
      let C : Subgroup G := A ⊓ Subgroup.centralizer ({v} : Set G)
      have hCA : C ≤ A := inf_le_left
      have hφa₀ : g * v * g⁻¹ * v⁻¹ = u₀ := by
        rcases hφmem g hg with h | h
        · exfalso
          apply hgv
          calc g * v * g⁻¹ = (g * v * g⁻¹ * v⁻¹) * v := by group
            _ = 1 * v := by rw [h]
            _ = v := by rw [one_mul]
        · exact h
      have hCrel : C.relIndex A = 2 := by
        rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
        refine ⟨g, hg, ?_, ?_⟩
        · intro hC
          apply hgv
          have hh := (Subgroup.mem_centralizer_iff.1 hC.2) v (Set.mem_singleton v)
          rw [← hh]; group
        · intro b hb
          rcases hφmem b hb with hb1 | hb1
          · right
            refine Subgroup.mem_inf.mpr ⟨hb, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
            have hbv : b * v * b⁻¹ = v := by
              calc b * v * b⁻¹ = (b * v * b⁻¹ * v⁻¹) * v := by group
                _ = 1 * v := by rw [hb1]
                _ = v := by rw [one_mul]
            show v * b = b * v
            calc v * b = (b * v * b⁻¹) * b := by rw [hbv]
              _ = b * v := by group
          · left
            refine Subgroup.mem_inf.mpr
              ⟨A.mul_mem hb hg, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
            rw [Set.mem_singleton_iff] at hy
            rw [hy]
            have hbv : b * v * b⁻¹ = u₀ * v := by
              calc b * v * b⁻¹ = (b * v * b⁻¹ * v⁻¹) * v := by group
                _ = u₀ * v := by rw [hb1]
            have hgv' : g * v * g⁻¹ = u₀ * v := by
              calc g * v * g⁻¹ = (g * v * g⁻¹ * v⁻¹) * v := by group
                _ = u₀ * v := by rw [hφa₀]
            have hbcomm : b * u₀ * b⁻¹ = u₀ := by
              have hh := hAu₀ b hb
              calc b * u₀ * b⁻¹ = (b * u₀) * b⁻¹ := by group
                _ = (u₀ * b) * b⁻¹ := by rw [hh]
                _ = u₀ := by group
            have hconj : (b * g) * v * (b * g)⁻¹ = v := by
              calc (b * g) * v * (b * g)⁻¹ = b * (g * v * g⁻¹) * b⁻¹ := by group
                _ = b * (u₀ * v) * b⁻¹ := by rw [hgv']
                _ = (b * u₀ * b⁻¹) * (b * v * b⁻¹) := by group
                _ = u₀ * (u₀ * v) := by rw [hbcomm, hbv]
                _ = v := by rw [← mul_assoc, hu₀sq', one_mul]
            show v * (b * g) = (b * g) * v
            calc v * (b * g) = ((b * g) * v * (b * g)⁻¹) * (b * g) := by rw [hconj]
              _ = (b * g) * v := by group
      have hv2 : ∃ j : ℕ, orderOf v = 2 ^ j := by
        have hdvdv : orderOf v ∣ 2 ^ 1 := by simpa using orderOf_dvd_iff_pow_eq_one.mpr hvsq2
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdv
        exact ⟨j, hj⟩
      have hcommC : ∀ d ∈ C, d * v = v * d := by
        intro d hd
        have hh := (Subgroup.mem_centralizer_iff.1 hd.2) v (Set.mem_singleton v)
        rw [hh]
      have hrig := hrigid v hv2 C hCA hCrel hcommC
      exact hgv (by rw [hrig g hg]; group)
    rcases hRenum w hwR with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h]; exact (hAu₀ g hg).symm
    · rw [h]
      have : v * g = g * v := by
        calc v * g = (g * v * g⁻¹) * g := by rw [hgv]
          _ = g * v := by group
      exact this
    · rw [h]
      have hcomm := hAu₀ g hg
      have : v * g = g * v := by
        calc v * g = (g * v * g⁻¹) * g := by rw [hgv]
          _ = g * v := by group
      calc (u₀ * v) * g = u₀ * (v * g) := by group
        _ = u₀ * (g * v) := by rw [this]
        _ = (u₀ * g) * v := by group
        _ = (g * u₀) * v := by rw [← hcomm]
        _ = g * (u₀ * v) := by group

theorem centralizes_blockU_of_hyperplaneRigid {X A : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hX : IsShortGroup ↥X) (hnat : IsNaturalAltModule ↥X n) (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hrigid : HyperplaneRigid A) :
    A ≤ Subgroup.centralizer (blockU X : Set G) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact centralizes_blockU_of_hyperplaneRigid_one hX hnat hA hAX hrigid
  · exact centralizes_blockU_of_hyperplaneRigid_of_two_le h hX hnat hA hAX hrigid

end CFSG.LocalAnalysis.WeakClosure81
