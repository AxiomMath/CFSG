module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHeis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

variable {W : Type} [CommGroup W]

theorem mk_conjAut_eq_actS {Y L : Subgroup (MulAut W)}
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S] (e : CQ L ≃* S)
    {t : MulAut W} (htY : t ∈ Y) (l : ↥L) :
    e (QuotientGroup.mk (conjAut L (hY htY) l)) =
      actS hY e ⟨t, Subgroup.mem_sup_right htY⟩ (e (QuotientGroup.mk l)) := by
  rw [actS_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, actionOnCQ_mk]
  rfl

variable [Finite W]

theorem two_pow_le_index_sq_of_inner_heisCfg (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    {S : Type} [Group S] (e : CQ L ≃* S) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) {t : MulAut W} (htL : t ∈ L) (ht2 : t * t = 1)
    {x y : Fin (n + 1) → S} {z : S} (h : HeisCfg p (n + 1) x y z) (hy : ∀ i, y i ^ p = 1)
    (hinv : e (QuotientGroup.mk ⟨t, htL⟩) * x 0 * (e (QuotientGroup.mk ⟨t, htL⟩))⁻¹ = (x 0)⁻¹) :
    2 ^ ((p - 1) * p ^ n * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  let π : ↥L →* S := (e : CQ L →* S).comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : ∀ l : ↥L, π l = e (QuotientGroup.mk l) := fun _ => rfl
  have hK : π.ker = Subgroup.center ↥L := by
    ext k
    rw [MonoidHom.mem_ker, hπ, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hKp : ¬ p ∣ Nat.card π.ker := by rw [hK]; exact hZ
  obtain ⟨x', y', z', h', hx'1, -, -, -⟩ := HeisCfg.exists_lift π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hK.le hKp h hy
  have hinvL : (⟨t, htL⟩ : ↥L) * x' 0 * (⟨t, htL⟩ : ↥L)⁻¹ = (x' 0)⁻¹ := by
    refine eq_of_map_eq_of_pow_eq_one π hK.le hKp
      (by rw [conj_pow, h'.xp 0, mul_one, mul_inv_cancel]) (by rw [inv_pow, h'.xp 0, inv_one]) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hx'1, hπ]
    exact hinv
  have hz' : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have hinv' : t * L.subtype (x' 0) * t⁻¹ = (L.subtype (x' 0))⁻¹ := by
    have := congrArg L.subtype hinvL
    simp only [map_mul, map_inv] at this
    exact this
  exact two_pow_le_index_sq_of_heisCfg hW hp2 (h'.map L.subtype hz') ht2 hinv'

theorem two_pow_le_index_sq_of_outer_heisCfg (hW : ∀ w : W, w * w = 1)
    {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hF : Fstar Y = L) (hperf : Group.IsPerfect ↥L)
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S] (e : CQ L ≃* S)
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hD : ∀ ψ : MulAut S, ψ ∉ (MulAut.conj : S →* MulAut S).range → ψ * ψ = 1 →
      ∃ (x y : Fin (n + 1) → S) (z : S),
        HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ ψ (x 0) = (x 0)⁻¹)
    {t : MulAut W} (htY : t ∈ Y) (htL : t ∉ L) (ht2 : t * t = 1) :
    2 ^ ((p - 1) * p ^ n * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  have hto : actS hY e ⟨t, Subgroup.mem_sup_right htY⟩ ∉ (MulAut.conj : S →* MulAut S).range :=
    fun h => htL (mem_of_actS_inner_of_fstar hLY hF hperf hY e htY h)
  have ht'2 : actS hY e ⟨t, Subgroup.mem_sup_right htY⟩ *
      actS hY e ⟨t, Subgroup.mem_sup_right htY⟩ = 1 := by
    rw [← map_mul, ← map_one (actS hY e)]
    congr 1
    exact Subtype.ext ht2
  obtain ⟨x, y, z, h, hy, hinv⟩ := hD _ hto ht'2
  let π : ↥L →* S := (e : CQ L →* S).comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : ∀ l : ↥L, π l = e (QuotientGroup.mk l) := fun _ => rfl
  have hK : π.ker = Subgroup.center ↥L := by
    ext k
    rw [MonoidHom.mem_ker, hπ, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hKp : ¬ p ∣ Nat.card π.ker := by rw [hK]; exact hZ
  obtain ⟨x', y', z', h', hx'1, -, -, -⟩ := HeisCfg.exists_lift π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hK.le hKp h hy
  have hc : conjAut L (hY htY) (x' 0) = (x' 0)⁻¹ := by
    refine eq_of_map_eq_of_pow_eq_one π hK.le hKp ?_ ?_ ?_
    · rw [← map_pow, h'.xp 0, map_one]
    · rw [inv_pow, h'.xp 0, inv_one]
    · rw [hπ, mk_conjAut_eq_actS hY e htY, ← hπ, hx'1, map_inv, hx'1]
      exact hinv
  have hz' : L.subtype z' ≠ 1 := fun hz1 => h'.z1 (L.subtype_injective (by rw [hz1, map_one]))
  have hinv' : t * L.subtype (x' 0) * t⁻¹ = (L.subtype (x' 0))⁻¹ := by
    have h2 := congrArg Subtype.val hc
    rw [coe_conjAut] at h2
    simpa using h2
  exact two_pow_le_index_sq_of_heisCfg hW hp2 (h'.map L.subtype hz') ht2 hinv'

theorem le_mParam_of_heisCfg_out2 (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L) (hq : IsQuasisimple ↥L)
    (hO2 : O2Trivial L) {S : Type} [Group S] (e : CQ L ≃* S) (h2S : 2 ∣ Nat.card S)
    {ρ p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L))
    (hρ : 2 * ρ < (p - 1) * p ^ n * orderOf (2 : ZMod p) + 2)
    (hgen : ∀ t : S, t * t = 1 → t ≠ 1 → ∃ (x y : Fin (n + 1) → S) (z : S),
      HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹)
    (hD : ∀ ψ : MulAut S, ψ ∉ (MulAut.conj : S →* MulAut S).range → ψ * ψ = 1 →
      ∃ (x y : Fin (n + 1) → S) (z : S),
        HeisCfg p (n + 1) x y z ∧ (∀ i, y i ^ p = 1) ∧ ψ (x 0) = (x 0)⁻¹) :
    ρ ≤ E3.mParam Y := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have hEven : Even (Nat.card Y) := by
    rw [even_iff_two_dvd]
    have hS : Nat.card S ∣ Nat.card L := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    exact (h2S.trans hS).trans (Subgroup.card_dvd_of_le hLY)
  unfold E3.mParam
  rw [if_pos hEven]
  refine le_csInf ?_ ?_
  · obtain ⟨t, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
    exact ⟨_, (t : MulAut W), t.2, by rwa [Subgroup.orderOf_coe], rfl⟩
  · rintro n' ⟨t, htY, hto, rfl⟩
    by_cases htL : t ∈ L
    · exact le_rkIdx_of_heisCfg hW' hO2 e hp2 hZ hρ hgen htL hto
    · have ht2 : t * t = 1 := by
        rw [← sq, ← hto]
        exact pow_orderOf_eq_one t
      have h := two_pow_le_index_sq_of_outer_heisCfg hW' hLY hF hq.1 hY e hp2 hZ hD htY htL ht2
      obtain ⟨m, hm⟩ := index_fixV_eq_two_pow hW' (Subgroup.zpowers t)
      have h2 := two_pow_le_of_pow_le ⟨m, hm⟩ h hρ
      rw [hm] at h2
      have hρm : ρ ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
      rwa [rkIdx, hm, padicValNat.prime_pow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
