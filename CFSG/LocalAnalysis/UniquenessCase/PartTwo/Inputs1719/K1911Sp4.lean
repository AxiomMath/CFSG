module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K1911Concl
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusSp4
public import CFSG.ClassicalGroups.Symplectic.Sp4TorusTwoSubgroup
public import CFSG.GroupTheory.TwoGroupAutFixOfNoInvariant
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4EvenTorus
public import CFSG.ClassicalGroups.Symplectic.Sp4ElemAbelianPlus
public import CFSG.Timmesfeld.Transvection.PresSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem sp4_map_conj_inv_eq_torus {K : Type} [Field K] {A : Subgroup (StatedSp 2 K)}
    {g : StatedSp 2 K} (hg : A = (torus 2 K).map (MulAut.conj g).toMonoidHom) :
    A.map (MulAut.conj g⁻¹).toMonoidHom = torus 2 K := by
  rw [hg, Subgroup.map_map]
  rw [show (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id _ by
    refine MonoidHom.ext fun x => ?_
    simpa using (MulAut.conj g).symm_apply_apply x]
  exact Subgroup.map_id _

theorem sp4_normalizes_no_two_subgroup {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) {A : Subgroup (StatedSp 2 K)}
    {t g : StatedSp 2 K} (hg : A = (torus 2 K).map (MulAut.conj g).toMonoidHom)
    (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) :
    ∀ R : Subgroup (StatedSp 2 K), IsPGroup 2 R →
      (A ⊔ zpowers t) ≤ normalizer (R : Set (StatedSp 2 K)) → R = ⊥ := by
  have hA' := sp4_map_conj_inv_eq_torus hg
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  intro R hR hBR
  let R' : Subgroup (StatedSp 2 K) := R.map (MulAut.conj g⁻¹).toMonoidHom
  have hR' : IsPGroup 2 R' := hR.map _
  have hmapN : (normalizer (R : Set (StatedSp 2 K))).map
        (MulAut.conj g⁻¹).toMonoidHom = normalizer (R' : Set (StatedSp 2 K)) := by
    simpa [R'] using
      Subgroup.map_equiv_normalizer_eq (R : Subgroup (StatedSp 2 K)) (MulAut.conj g⁻¹)
  have hDR' : torus 2 K ≤ normalizer (R' : Set (StatedSp 2 K)) := by
    have h1 : A.map (MulAut.conj g⁻¹).toMonoidHom ≤
        (normalizer (R : Set (StatedSp 2 K))).map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.map_mono (le_trans le_sup_left hBR)
    rw [hA', hmapN] at h1
    exact h1
  have ht'R' : (g⁻¹ * t * g) ∈ normalizer (R' : Set (StatedSp 2 K)) := by
    have htN : t ∈ normalizer (R : Set (StatedSp 2 K)) :=
      hBR (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have hmem : MulAut.conj g⁻¹ t ∈
        (normalizer (R : Set (StatedSp 2 K))).map (MulAut.conj g⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ htN
    rw [hmapN] at hmem
    simpa using hmem
  have htinvt : ∀ d ∈ torus 2 K, (g⁻¹ * t * g) * d * (g⁻¹ * t * g)⁻¹ = d⁻¹ := by
    intro d hd
    rw [← hA'] at hd
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hd
    calc (g⁻¹ * t * g) * MulAut.conj g⁻¹ a * (g⁻¹ * t * g)⁻¹
        = g⁻¹ * (t * a * t⁻¹) * g := by
          rw [show MulAut.conj g⁻¹ a = g⁻¹ * a * g by simp]
          group
      _ = g⁻¹ * a⁻¹ * g := by rw [hinv a ha]
      _ = (MulAut.conj g⁻¹ a)⁻¹ := by
          rw [show MulAut.conj g⁻¹ a = g⁻¹ * a * g by simp]
          group
  have hRbot : R' = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.Sp4.eq_bot_of_torus_le_normalizer_of_inv
      (K := K) (t := g⁻¹ * t * g) (R := R') h4 htinvt hR' hDR' ht'R'
  have hRmap : R = R'.map (MulAut.conj g).toMonoidHom := by
    show R = (R.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom
    rw [Subgroup.map_map]
    rw [show (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id _ by
      refine MonoidHom.ext fun x => ?_
      simpa using (MulAut.conj g).apply_symm_apply x]
    exact (Subgroup.map_id R).symm
  rw [hRmap, hRbot, Subgroup.map_bot]

theorem sp4_eq_one_of_mem_aut_fix_torus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) {A : Subgroup (StatedSp 2 K)}
    {g : StatedSp 2 K} (hg : A = (torus 2 K).map (MulAut.conj g).toMonoidHom)
    {Q : Subgroup (MulAut (StatedSp 2 K))}
    (hfix : ∀ α ∈ Q, ∀ b ∈ A, α b = b)
    (hqin : ∀ x : StatedSp 2 K, MulAut.conj x ∈ Q → x = 1) :
    ∀ α ∈ Q, α = 1 := by
  have h8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  intro α hα
  have hβfix : ∀ d ∈ torus 2 K,
      ((MulAut.conj g)⁻¹ * α * MulAut.conj g) d = d := by
    intro d hd
    have hgd : MulAut.conj g d ∈ A := by
      rw [hg]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hd
    have hfixgd : α (MulAut.conj g d) = MulAut.conj g d := hfix α hα (MulAut.conj g d) hgd
    calc ((MulAut.conj g)⁻¹ * α * MulAut.conj g) d
        = (MulAut.conj g)⁻¹ (α ((MulAut.conj g) d)) := rfl
      _ = (MulAut.conj g)⁻¹ ((MulAut.conj g) d) := by rw [hfixgd]
      _ = d := by simpa using (MulAut.conj g).symm_apply_apply d
  have hβinner : ((MulAut.conj g)⁻¹ * α * MulAut.conj g) ∈
      (MulAut.conj : StatedSp 2 K →* MulAut (StatedSp 2 K)).range :=
    CFSG.RankThree.PartTwo.KFacts.mem_range_conj_of_fix_torus_sp4 h8 _ hβfix
  obtain ⟨y, hy⟩ := hβinner
  have hαeq : α = MulAut.conj (g * y * g⁻¹) := by
    calc α = MulAut.conj g * ((MulAut.conj g)⁻¹ * α * MulAut.conj g) *
          (MulAut.conj g)⁻¹ := by group
      _ = MulAut.conj g * MulAut.conj y * (MulAut.conj g)⁻¹ := by rw [← hy]
      _ = MulAut.conj (g * y * g⁻¹) := by
          rw [← map_inv, ← map_mul, ← map_mul]
  have hxQ : MulAut.conj (g * y * g⁻¹) ∈ Q := by
    rw [← hαeq]
    exact hα
  have hx1 : g * y * g⁻¹ = 1 := hqin _ hxQ
  rw [hαeq, hx1]
  simp

theorem torusFixedConcl_sp4 {K : Type} [Field K] [Finite K] [CharP K 2] {n p : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) (hodd : Odd n) (hp : p.Prime)
    (hpd : p ∣ 2 ^ n + 1) : TorusFixedConcl (StatedSp 2 K) n p := by
  unfold TorusFixedConcl
  intro A t hA ht hinv Q hQ hQN
  obtain ⟨g, hg⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.exists_conj_eq_torus_of_isZModSq_sp4
      hK hn hodd hA
  have hZ : Subgroup.center (StatedSp 2 K) = ⊥ :=
    CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (n := 2) (K := K) (by norm_num)
  have hno := sp4_normalizes_no_two_subgroup hK hn hg hinv
  have hfix : ∀ α ∈ Q, ∀ b ∈ A ⊔ zpowers t, α b = b :=
    CFSG.GroupTheory.apply_eq_of_forall_isPGroup_eq_bot (hZ := hZ) (B := A ⊔ zpowers t)
      (Q := Q) hQ hQN hno
  have hqin : ∀ x : StatedSp 2 K, MulAut.conj x ∈ Q → x = 1 := fun x hx =>
    CFSG.GroupTheory.eq_one_of_conj_mem_of_forall_isPGroup_eq_bot (hZ := hZ)
      (B := A ⊔ zpowers t) (Q := Q) hQ hQN hno hx
  have hone : ∀ α ∈ Q, α = 1 :=
    sp4_eq_one_of_mem_aut_fix_torus hK hn hg
      (fun α hα b hb => hfix α hα b (Subgroup.mem_sup_left hb)) hqin
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.ClassicalGroups.Symplectic.Sp4.exists_isElemAbelian_card_sq_of_dvd_card_add_one
      (K := K) hp (by rwa [hK])
  exact ⟨E, hE, hEcard, fun α hα => by rw [hone α hα]; intro e _; rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
