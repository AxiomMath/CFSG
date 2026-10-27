module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUPerm
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUOnto

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom diagHom_injective)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

private theorem ggQTUca_card_units {K : Type} [Field K]
    (hK : UnitaryFieldData 2 1 K) : Nat.card Kˣ = 3 := by
  have hcard : Nat.card K = 4 := by
    rw [hK.card]
    norm_num
  rw [Nat.card_units, hcard]

private theorem ggQTUca_pow_three_eq_one {K : Type} [Field K] [Finite K]
    (hK : UnitaryFieldData 2 1 K) (u : Kˣ) : u ^ 3 = 1 := by
  have : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hcard : Fintype.card Kˣ = 3 := by
    rw [← Nat.card_eq_fintype_card, ggQTUca_card_units hK]
  have h := pow_card_eq_one (x := u)
  rwa [hcard] at h

private theorem ggQTUca_orderOf {K : Type} [Field K] [Finite K]
    (hK : UnitaryFieldData 2 1 K) {u : Kˣ} (hu : u ≠ 1) : orderOf u = 3 := by
  exact orderOf_eq_prime (ggQTUca_pow_three_eq_one hK u) hu

private theorem ggQTUca_pow_add {K : Type} [Field K] {ω : Kˣ}
    (hω : orderOf ω = 3) (a b : ZMod 3) :
    ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  have hcong : (a + b).val ≡ a.val + b.val [MOD 3] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have h1 : ω ^ (a + b).val = ω ^ (a.val + b.val) := by
    rw [pow_eq_pow_iff_modEq, hω]
    exact hcong
  rw [h1, pow_add]

private theorem ggQTUca_pow_injective {K : Type} [Field K] {ω : Kˣ}
    (hω : orderOf ω = 3) : Function.Injective (fun e : ZMod 3 => ω ^ e.val) := by
  intro a b hab
  have hcong : a.val ≡ b.val [MOD 3] := by
    have h := (pow_eq_pow_iff_modEq).mp hab
    rwa [hω] at h
  exact ZMod.val_injective 3
    (Nat.ModEq.eq_of_lt_of_lt hcong (ZMod.val_lt a) (ZMod.val_lt b))

private theorem ggQTUca_pow_surjective {K : Type} [Field K] [Finite K]
    (hK : UnitaryFieldData 2 1 K) {ω : Kˣ} (hω : orderOf ω = 3) :
    ∀ t : Kˣ, ∃ e : ZMod 3, ω ^ e.val = t := by
  classical
  intro t
  have : Fintype Kˣ := Fintype.ofFinite Kˣ
  have hinj := ggQTUca_pow_injective hω
  have hcardK : Fintype.card Kˣ = 3 := by
    rw [← Nat.card_eq_fintype_card, ggQTUca_card_units hK]
  have hcardZ : Fintype.card (ZMod 3) = 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zmod]
  have himage : Finset.image (fun e : ZMod 3 => ω ^ e.val) Finset.univ = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injective Finset.univ hinj, Finset.card_univ, hcardZ, hcardK]
  have ht : t ∈ Finset.image (fun e : ZMod 3 => ω ^ e.val) Finset.univ := by
    rw [himage]
    exact Finset.mem_univ t
  obtain ⟨e, -, he⟩ := Finset.mem_image.mp ht
  exact ⟨e, he⟩

private theorem ggQTUca_sq_eq {K : Type} [Field K] {ω lam : Kˣ}
    (hωlam : ω * lam = 1) (hω3 : ω ^ 3 = 1) : ω ^ 2 = lam := by
  calc ω ^ 2 = ω ^ 2 * 1 := by rw [mul_one]
    _ = ω ^ 2 * (ω * lam) := by rw [hωlam]
    _ = ω ^ 2 * ω * lam := by rw [mul_assoc]
    _ = ω ^ 3 * lam := by rw [← pow_succ]
    _ = lam := by rw [hω3, one_mul]

private theorem ggQTUca_sum_eq_zero {n : ℕ} (v : ↥(GGQTwoXInLAug n)) :
    ∑ i : Fin (n + 1), v.val i = 0 := by
  have h : ((∑ i : Fin (n + 1), LinearMap.proj i :
      (Fin (n + 1) → ZMod 3) →ₗ[ZMod 3] ZMod 3) v.val = 0) :=
    LinearMap.mem_ker.mp v.2
  simpa only [LinearMap.sum_apply, LinearMap.proj_apply] using h

private theorem ggQTUca_sum_val {n : ℕ} (v : ↥(GGQTwoXInLAug n)) :
    3 ∣ ∑ i : Fin (n + 1), (v.val i).val := by
  have hsum0 : ∑ i : Fin (n + 1), v.val i = 0 := ggQTUca_sum_eq_zero v
  have hcast : ((∑ i : Fin (n + 1), (v.val i).val : ℕ) : ZMod 3) = 0 := by
    rw [Nat.cast_sum]
    simp only [ZMod.natCast_zmod_val]
    exact hsum0
  exact (ZMod.natCast_eq_zero_iff (∑ i : Fin (n + 1), (v.val i).val) 3).mp hcast

private theorem ggQTUca_prod_pow {n : ℕ} {K : Type} [Field K] {ω : Kˣ}
    (hω : orderOf ω = 3) (v : ↥(GGQTwoXInLAug n)) :
    ∏ i : Fin (n + 1), ω ^ (v.val i).val = 1 := by
  rw [Finset.prod_pow_eq_pow_sum]
  have hdvd : orderOf ω ∣ ∑ i : Fin (n + 1), (v.val i).val := by
    rw [hω]
    exact ggQTUca_sum_val v
  exact (orderOf_dvd_iff_pow_eq_one).mp hdvd

private noncomputable def ggQTUca_diagSU {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : UnitaryFieldData 2 1 K) {ω : Kˣ} (hω : orderOf ω = 3)
    (v : ↥(GGQTwoXInLAug n)) : ↥(unitarySU 2 1 K (n + 1)) :=
  ⟨diagHom (n + 1) (fun i => ω ^ (v.val i).val),
    TableBUE.diagHom_mem_unitarySU (n := 1) (d := n + 1) hK
      (fun i => by
        have hω3 : ω ^ 3 = 1 := by
          rw [← hω]
          exact pow_orderOf_eq_one ω
        calc (ω ^ (v.val i).val) ^ (2 ^ 1 + 1)
            = (ω ^ (v.val i).val) ^ 3 := by norm_num
          _ = ω ^ ((v.val i).val * 3) := by rw [pow_mul]
          _ = ω ^ (3 * (v.val i).val) := by rw [mul_comm]
          _ = (ω ^ 3) ^ (v.val i).val := by rw [pow_mul]
          _ = 1 := by rw [hω3, one_pow])
      (ggQTUca_prod_pow hω v)⟩

@[simp] private theorem ggQTUca_diagSU_coe {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : UnitaryFieldData 2 1 K) {ω : Kˣ} (hω : orderOf ω = 3)
    (v : ↥(GGQTwoXInLAug n)) :
    ((ggQTUca_diagSU hK hω v : ↥(unitarySU 2 1 K (n + 1))) : GL (Fin (n + 1)) K) =
      diagHom (n + 1) (fun i => ω ^ (v.val i).val) := rfl

private theorem ggQTUca_diagSU_add {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : UnitaryFieldData 2 1 K) {ω : Kˣ} (hω : orderOf ω = 3)
    (v w : ↥(GGQTwoXInLAug n)) :
    ggQTUca_diagSU hK hω (v + w) = ggQTUca_diagSU hK hω v * ggQTUca_diagSU hK hω w := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, ggQTUca_diagSU_coe, ggQTUca_diagSU_coe, ggQTUca_diagSU_coe,
    ← map_mul]
  congr 1
  funext i
  exact ggQTUca_pow_add hω (v.val i) (w.val i)

private noncomputable def ggQTUca_hFun {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) (n + 1) K) {ω : Kˣ}
    (hω : orderOf ω = 3) (v : ↥(GGQTwoXInLAug n)) : ↥Bs :=
  ⟨F.φ (ggQTUca_diagSU F.field hω v),
    ggQTwoXInLU_heart hS F (ggQTUca_diagSU F.field hω v)
      (fun i => ω ^ (v.val i).val) rfl⟩

private theorem ggQTUca_hFun_mul {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) (n + 1) K) {ω : Kˣ}
    (hω : orderOf ω = 3) (v w : ↥(GGQTwoXInLAug n)) :
    ggQTUca_hFun hS F hω (v + w) = ggQTUca_hFun hS F hω v * ggQTUca_hFun hS F hω w := by
  apply Subtype.ext
  change F.φ (ggQTUca_diagSU F.field hω (v + w)) =
    F.φ (ggQTUca_diagSU F.field hω v) * F.φ (ggQTUca_diagSU F.field hω w)
  rw [← map_mul, ggQTUca_diagSU_add]

private theorem ggQTUca_mem_suPairs_self {f n : ℕ} {K : Type} [Field K] {G : Type} [Group G]
    (ψ : ↥(unitarySU 2 f K n) →* G) (s : ↥(unitarySU 2 f K n)) :
    (ψ s, (s : GL (Fin n) K)) ∈ SUTorus.suPairs ψ := by
  rw [SUTorus.mem_suPairs]
  refine ⟨Subgroup.le_normalizer s.2, ?_⟩
  intro u v hv
  have hsu : s * u * s⁻¹ = v := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hv.symm
  have h : ψ s * ψ u * (ψ s)⁻¹ = ψ (s * u * s⁻¹) := by
    rw [map_mul, map_inv, map_mul]
  rw [h, hsu]

private theorem ggQTUca_hFun_eq_one {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hn : 6 ≤ n)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) (n + 1) K) {ω : Kˣ}
    (hω : orderOf ω = 3) (h3 : ¬ 3 ∣ n + 1) {v : ↥(GGQTwoXInLAug n)}
    (hv : ggQTUca_hFun hS F hω v = 1) : v = 0 := by
  classical
  have hphi : F.φ (ggQTUca_diagSU F.field hω v) = 1 := by
    have h : (ggQTUca_hFun hS F hω v : G) = 1 := by
      simpa using congrArg (fun z : ↥Bs => (z : G)) hv
    change F.φ (ggQTUca_diagSU F.field hω v) = 1 at h
    exact h
  have hpair : ((1 : G), ((ggQTUca_diagSU F.field hω v : ↥(unitarySU 2 1 K (n + 1))) :
      GL (Fin (n + 1)) K)) ∈ SUTorus.suPairs F.φ := by
    have hself := ggQTUca_mem_suPairs_self F.φ (ggQTUca_diagSU F.field hω v)
    rwa [hphi] at hself
  have hnq : (n + 1, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have h1 : n + 1 = 3 := congrArg Prod.fst h
    omega
  obtain ⟨c, hc⟩ := SUTorus.exists_scalar_of_mem_suPairs_one (f := 1) (G := G)
    F.field (by omega) hnq (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1) F.ker_le hpair
  have hdiag : diagHom (n + 1) (fun i => ω ^ (v.val i).val) =
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c := by
    change ((ggQTUca_diagSU F.field hω v : ↥(unitarySU 2 1 K (n + 1))) :
      GL (Fin (n + 1)) K) = Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) c
    exact hc
  have hfun : (fun i : Fin (n + 1) => ω ^ (v.val i).val) = fun _ => c := by
    apply diagHom_injective (n + 1)
    rw [hdiag]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, Matrix.scalar_apply]
  have hconst : ∀ i : Fin (n + 1), ω ^ (v.val i).val = c := fun i => congrFun hfun i
  let i₀ : Fin (n + 1) := ⟨0, by omega⟩
  have hconst_all : ∀ i : Fin (n + 1), v.val i = v.val i₀ := by
    intro i
    exact ggQTUca_pow_injective hω (by simp only [hconst i, hconst i₀])
  have hsum : ∑ i : Fin (n + 1), v.val i = 0 := ggQTUca_sum_eq_zero v
  have hsum_const : (n + 1) • v.val i₀ = 0 := by
    calc (n + 1) • v.val i₀ = ∑ i : Fin (n + 1), v.val i₀ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = ∑ i : Fin (n + 1), v.val i := by
          exact Finset.sum_congr rfl (fun i _ => (hconst_all i).symm)
      _ = 0 := hsum
  have hcoef : ((n + 1 : ℕ) : ZMod 3) ≠ 0 := by
    intro h
    exact h3 ((ZMod.natCast_eq_zero_iff (n + 1) 3).mp h)
  have hsmul : ((n + 1 : ℕ) : ZMod 3) * v.val i₀ = 0 := by
    simpa [nsmul_eq_mul] using hsum_const
  have ha : v.val i₀ = 0 := by
    rcases mul_eq_zero.mp hsmul with h | h
    · exact absurd h hcoef
    · exact h
  apply Subtype.ext
  funext i
  rw [hconst_all i, ha]
  rfl

private theorem ggQTUca_sub_mem {n : ℕ} (v w : ↥(GGQTwoXInLAug n)) :
    (fun i : Fin (n + 1) => v.val i - w.val i) ∈ GGQTwoXInLAug n := by
  rw [LinearMap.mem_ker]
  have hv := ggQTUca_sum_eq_zero v
  have hw := ggQTUca_sum_eq_zero w
  simp only [LinearMap.sum_apply, LinearMap.proj_apply]
  have hsub : (∑ i : Fin (n + 1), (v.val i - w.val i)) =
      (∑ i : Fin (n + 1), v.val i) - (∑ i : Fin (n + 1), w.val i) :=
    Finset.sum_sub_distrib (fun i => v.val i) (fun i => w.val i)
  rw [hsub, hv, hw, sub_self]

private noncomputable def ggQTUca_sub {n : ℕ} (v w : ↥(GGQTwoXInLAug n)) :
    ↥(GGQTwoXInLAug n) :=
  ⟨fun i => v.val i - w.val i, ggQTUca_sub_mem v w⟩

private theorem ggQTUca_sub_add {n : ℕ} (v w : ↥(GGQTwoXInLAug n)) :
    ggQTUca_sub v w + w = v := by
  apply Subtype.ext
  funext i
  simp [ggQTUca_sub, Pi.add_apply, sub_add_cancel]

private theorem ggQTUca_sub_eq_zero {n : ℕ} {v w : ↥(GGQTwoXInLAug n)}
    (h : ggQTUca_sub v w = 0) : v = w := by
  apply Subtype.ext
  funext i
  have hval : (ggQTUca_sub v w).val i = 0 := by
    rw [h]
    rfl
  simpa [ggQTUca_sub] using sub_eq_zero.mp hval

private theorem ggQTUca_hFun_injective {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hn : 6 ≤ n)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) (n + 1) K) {ω : Kˣ}
    (hω : orderOf ω = 3) (h3 : ¬ 3 ∣ n + 1) :
    Function.Injective (ggQTUca_hFun hS F hω) := by
  intro v w hvw
  have hdiff : ggQTUca_hFun hS F hω (ggQTUca_sub v w) = 1 := by
    have hmul := ggQTUca_hFun_mul hS F hω (ggQTUca_sub v w) w
    rw [ggQTUca_sub_add] at hmul
    rw [hvw] at hmul
    have h1 : ggQTUca_hFun hS F hω (ggQTUca_sub v w) * ggQTUca_hFun hS F hω w =
        (1 : ↥Bs) * ggQTUca_hFun hS F hω w := by
      rw [one_mul]
      exact hmul.symm
    exact mul_right_cancel h1
  exact ggQTUca_sub_eq_zero (ggQTUca_hFun_eq_one hS hn F hω h3 hdiff)

private theorem ggQTUca_hFun_surjective {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) (n + 1) K) {ω : Kˣ}
    (hω : orderOf ω = 3) (h3 : ¬ 3 ∣ n + 1) :
    Function.Surjective (ggQTUca_hFun hS F hω) := by
  classical
  intro b
  obtain ⟨s, t, hs, hbs⟩ := ggQTwoXInLU_onto hS h3 F b.2
  have hdet : ((s : GL (Fin (n + 1)) K) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K).det = 1 :=
    ((mem_unitarySU_iff F.field).mp s.2).1
  have hprodK : ∏ i : Fin (n + 1), (t i : K) = 1 := by
    rw [hs, det_diagHom] at hdet
    exact hdet
  have hprod : ∏ i : Fin (n + 1), t i = 1 := by
    apply Units.ext
    rw [Units.coe_prod, Units.val_one]
    exact hprodK
  have hex : ∀ i : Fin (n + 1), ∃ e : ZMod 3, ω ^ e.val = t i :=
    fun i => ggQTUca_pow_surjective F.field hω (t i)
  choose e he using hex
  have hprod_e : ∏ i : Fin (n + 1), ω ^ (e i).val = 1 := by
    calc ∏ i : Fin (n + 1), ω ^ (e i).val = ∏ i : Fin (n + 1), t i :=
          Finset.prod_congr rfl (fun i _ => he i)
      _ = 1 := hprod
  rw [Finset.prod_pow_eq_pow_sum] at hprod_e
  have hdvd : 3 ∣ ∑ i : Fin (n + 1), (e i).val := by
    have h := orderOf_dvd_iff_pow_eq_one.mpr hprod_e
    rwa [hω] at h
  have hcast : ((∑ i : Fin (n + 1), (e i).val : ℕ) : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff (∑ i : Fin (n + 1), (e i).val) 3).mpr hdvd
  have hsum0 : ∑ i : Fin (n + 1), e i = 0 := by
    calc ∑ i : Fin (n + 1), e i = ∑ i : Fin (n + 1), ((e i).val : ZMod 3) := by
          exact Finset.sum_congr rfl (fun i _ => (ZMod.natCast_zmod_val (e i)).symm)
      _ = ((∑ i : Fin (n + 1), (e i).val : ℕ) : ZMod 3) := by rw [Nat.cast_sum]
      _ = 0 := hcast
  let v : ↥(GGQTwoXInLAug n) :=
    ⟨e, by simpa [Finset.sum_apply, LinearMap.proj_apply] using hsum0⟩
  have hv : (v : Fin (n + 1) → ZMod 3) = e := rfl
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change F.φ (ggQTUca_diagSU F.field hω v) = (b : G)
  have hsv : ggQTUca_diagSU F.field hω v = s := by
    apply Subtype.ext
    rw [ggQTUca_diagSU_coe, hs]
    congr 1
    funext i
    rw [hv]
    exact he i
  rw [hsv, hbs]

private noncomputable def ggQTUca_h {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) (n + 1) K) {ω : Kˣ}
    (hω : orderOf ω = 3) : ↥(GGQTwoXInLAug n) →+ Additive ↥Bs :=
  AddMonoidHom.mk' (fun v => Additive.ofMul (ggQTUca_hFun hS F hω v)) (by
    intro v w
    rw [ggQTUca_hFun_mul]
    rfl)

@[simp] private theorem ggQTUca_h_apply {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) (n + 1) K) {ω : Kˣ}
    (hω : orderOf ω = 3) (v : ↥(GGQTwoXInLAug n)) :
    ggQTUca_h hS F hω v = Additive.ofMul (ggQTUca_hFun hS F hω v) := rfl

private theorem ggQTUca_negVec_mem {n : ℕ} {j₀ : Fin (n + 1)} (h3 : 3 ∣ n) :
    (fun i : Fin (n + 1) => if i = j₀ then (0 : ZMod 3) else -1) ∈ GGQTwoXInLAug n := by
  rw [LinearMap.mem_ker]
  have hpoint : ∀ i : Fin (n + 1), (if i = j₀ then (0 : ZMod 3) else -1) =
      -1 + (if i = j₀ then (1 : ZMod 3) else 0) := by
    intro i
    by_cases h : i = j₀
    · simp [h]
      decide
    · simp [h]
  have hsingle : (∑ i : Fin (n + 1), (if i = j₀ then (1 : ZMod 3) else 0)) = 1 := by
    rw [Finset.sum_ite_eq' Finset.univ j₀ (fun _ => (1 : ZMod 3))]
    simp
  have hn0 : ((n : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff n 3).mpr h3
  have hcoef : ((n + 1 : ℕ) : ZMod 3) = 1 := by
    rw [Nat.cast_add, Nat.cast_one, hn0, zero_add]
  have hsum : (∑ i : Fin (n + 1), (if i = j₀ then (0 : ZMod 3) else -1)) = 0 := by
    calc ∑ i : Fin (n + 1), (if i = j₀ then (0 : ZMod 3) else -1)
        = ∑ i : Fin (n + 1), (-1 + (if i = j₀ then (1 : ZMod 3) else 0)) :=
          Finset.sum_congr rfl (fun i _ => hpoint i)
      _ = (∑ i : Fin (n + 1), (-1 : ZMod 3)) +
            (∑ i : Fin (n + 1), (if i = j₀ then (1 : ZMod 3) else 0)) :=
          Finset.sum_add_distrib
      _ = (n + 1) • (-1 : ZMod 3) + 1 := by
          rw [Finset.sum_const, hsingle, Finset.card_univ, Fintype.card_fin]
      _ = 0 := by
          rw [nsmul_eq_mul, hcoef]
          decide
  simpa [Finset.sum_apply, LinearMap.proj_apply] using hsum

private theorem ggQTUca_three_dvd_of_prod {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : UnitaryFieldData 2 1 K) {lam : Kˣ} (hlam : lam ≠ 1) {j₀ : Fin (n + 1)}
    (hprod : ∏ i : Fin (n + 1), (if i ∈ Finset.univ.erase j₀ then lam else 1) = 1) :
    3 ∣ n := by
  have hprod' : lam ^ n = 1 := by
    rw [← hprod, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
    simp
  have hord := ggQTUca_orderOf hK hlam
  rw [← hord]
  exact orderOf_dvd_iff_pow_eq_one.mpr hprod'

private theorem ggQTUca_prod_diag {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : UnitaryFieldData 2 1 K) {j₀ : Fin (n + 1)} {lam : Kˣ}
    {z : ↥(unitarySU 2 1 K (n + 1))}
    (hz : (z : GL (Fin (n + 1)) K) =
      diagHom (n + 1) (fun i => if i ∈ Finset.univ.erase j₀ then lam else 1)) :
    ∏ i : Fin (n + 1), (if i ∈ Finset.univ.erase j₀ then lam else 1) = 1 := by
  have hdet : ((z : GL (Fin (n + 1)) K) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) K).det = 1 :=
    ((mem_unitarySU_iff hK).mp z.2).1
  rw [hz, det_diagHom] at hdet
  apply Units.ext
  rw [Units.coe_prod, Units.val_one]
  exact hdet

theorem ggQTwoXInLU_coordAt {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hn : 6 ≤ n)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) (n + 1) K) {j₀ : Fin (n + 1)} {lam : Kˣ}
    {z : ↥(unitarySU 2 1 K (n + 1))} (hlam : lam ≠ 1)
    (hL : L = (TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase j₀)).map F.φ)
    (hz : (z : GL (Fin (n + 1)) K) =
      diagHom (n + 1) (fun i => if i ∈ Finset.univ.erase j₀ then lam else 1))
    (hzx : F.φ z = x) :
    3 ∣ n ∧ Nonempty (GGQTwoXInLUCoordAt Bs (ggG0 3 B x L D J) L x n K j₀) := by
  classical
  have hprod : ∏ i : Fin (n + 1), (if i ∈ Finset.univ.erase j₀ then lam else 1) = 1 :=
    ggQTUca_prod_diag F.field hz
  have h3 : 3 ∣ n := ggQTUca_three_dvd_of_prod F.field hlam hprod
  have h3' : ¬ 3 ∣ n + 1 := by omega
  let ω : Kˣ := lam⁻¹
  have hω3 : ω ^ 3 = 1 := by
    have hlam3 : lam ^ 3 = 1 := ggQTUca_pow_three_eq_one F.field lam
    rw [show ω = lam⁻¹ from rfl, inv_pow, hlam3, inv_one]
  have hω_ne_one : ω ≠ 1 := by
    rw [show ω = lam⁻¹ from rfl]
    exact inv_ne_one.mpr hlam
  have hordω : orderOf ω = 3 := ggQTUca_orderOf F.field hω_ne_one
  have hωlam : ω * lam = 1 := by
    simp [ω]
  have hω2 : ω ^ 2 = lam := ggQTUca_sq_eq hωlam hω3
  have hxBs : x ∈ Bs := hS.1.1.tableB_facts.2.2.1
  let h := ggQTUca_h hS F hordω
  have hinj : Function.Injective h := by
    intro v w hvw
    have hvw' : ggQTUca_hFun hS F hordω v = ggQTUca_hFun hS F hordω w := by
      apply Additive.ofMul.injective
      change Additive.ofMul (ggQTUca_hFun hS F hordω v) =
        Additive.ofMul (ggQTUca_hFun hS F hordω w) at hvw
      exact hvw
    exact ggQTUca_hFun_injective hS hn F hordω h3' hvw'
  have hsurj : Function.Surjective h := by
    intro b
    obtain ⟨v, hv⟩ := ggQTUca_hFun_surjective hS F hordω h3' (Additive.toMul b)
    refine ⟨v, ?_⟩
    change Additive.ofMul (ggQTUca_hFun hS F hordω v) = b
    rw [hv]
    exact Additive.ofMul.apply_symm_apply b
  let e : ↥(GGQTwoXInLAug n) ≃+ Additive ↥Bs :=
    AddEquiv.ofBijective h ⟨hinj, hsurj⟩
  have hdiag_field : ∀ b : ↥Bs, ∃ s : ↥(unitarySU 2 1 K (n + 1)),
      (s : GL (Fin (n + 1)) K) = diagHom (n + 1)
        (fun i => ω ^ ((e.symm (Additive.ofMul b) : Fin (n + 1) → ZMod 3) i).val) ∧
        F.φ s = b := by
    intro b
    let v : ↥(GGQTwoXInLAug n) := e.symm (Additive.ofMul b)
    refine ⟨ggQTUca_diagSU F.field hordω v, rfl, ?_⟩
    have h1 : e v = Additive.ofMul b := AddEquiv.apply_symm_apply e (Additive.ofMul b)
    have h2 : ggQTUca_hFun hS F hordω v = b := by
      change Additive.ofMul (ggQTUca_hFun hS F hordω v) = Additive.ofMul b at h1
      exact Additive.ofMul.injective h1
    have hb' : (ggQTUca_hFun hS F hordω v : G) = (b : G) :=
      congrArg (fun z : ↥Bs => (z : G)) h2
    change F.φ (ggQTUca_diagSU F.field hordω v) = (b : G) at hb'
    exact hb'
  let f : Fin (n + 1) → ZMod 3 := fun i => if i = j₀ then 0 else -1
  have hf : f ∈ GGQTwoXInLAug n := ggQTUca_negVec_mem h3
  let v₀ : ↥(GGQTwoXInLAug n) := ⟨f, hf⟩
  have hv₀ : (v₀ : Fin (n + 1) → ZMod 3) = f := rfl
  have hd : (fun i : Fin (n + 1) => ω ^ (v₀.val i).val) =
      (fun i : Fin (n + 1) => if i ∈ Finset.univ.erase j₀ then lam else 1) := by
    funext i
    rw [hv₀]
    by_cases hi : i = j₀
    · subst hi
      have hmem : i ∉ Finset.univ.erase i := by simp
      simp [f, hmem]
    · have hmem : i ∈ Finset.univ.erase j₀ := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
      have hvi : f i = -1 := by simp [f, hi]
      rw [hvi, if_pos hmem]
      have hval : ((-1 : ZMod 3)).val = 2 := by decide
      rw [hval, hω2]
  have hsz : ggQTUca_diagSU F.field hordω v₀ = z := by
    apply Subtype.ext
    rw [ggQTUca_diagSU_coe, hz, hd]
  have hxv : ggQTUca_hFun hS F hordω v₀ = ⟨x, hxBs⟩ := by
    apply Subtype.ext
    change F.φ (ggQTUca_diagSU F.field hordω v₀) = x
    rw [hsz, hzx]
  have hιx : e.symm (Additive.ofMul ⟨x, hxBs⟩) = v₀ := by
    have hxv' : h v₀ = Additive.ofMul ⟨x, hxBs⟩ := by
      change Additive.ofMul (ggQTUca_hFun hS F hordω v₀) = Additive.ofMul ⟨x, hxBs⟩
      rw [hxv]
    rw [← hxv']
    exact AddEquiv.symm_apply_apply e v₀
  refine ⟨h3, ⟨{
    field := F.field
    φ := F.φ
    range_eq := F.range_eq
    ker_le := F.ker_le
    ω := ω
    ω_ne_one := hω_ne_one
    ι := e.symm
    diag := hdiag_field
    mem_x := hxBs
    ι_x := by
      rw [hιx]
    L_eq := hL }⟩⟩

end CFSG.StandardType

end
