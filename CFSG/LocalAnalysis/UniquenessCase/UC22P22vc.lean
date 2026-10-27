module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22vb
import CFSG.RankThree.FFModules.RepMulAut
import CFSG.RankThree.FFModules.FixSubConj
public import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.RankThree.FFModules (fixSub)

section Basic

variable {H : Type} [Group H]

private theorem uc22p22vc_le_normalizer_pCoreOf (K : Subgroup H) :
    K ≤ Subgroup.normalizer (pCoreOf 2 K : Set H) := by
  have h1 : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  haveI : ((pCoreOf 2 K).subgroupOf K).Normal := by
    rw [h1]
    infer_instance
  exact Subgroup.le_normalizer_of_normal_subgroupOf (Subgroup.map_subtype_le _)

private theorem uc22p22vc_mem_normalizer_commutator {R B : Subgroup H} {g : H}
    (hR : g ∈ Subgroup.normalizer (R : Set H)) (hB : g ∈ Subgroup.normalizer (B : Set H)) :
    g ∈ Subgroup.normalizer ((⁅R, B⁆ : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hR hB ⊢
  rw [Subgroup.map_commutator, hR, hB]

end Basic

section Module

variable {H : Type} [Group H] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private theorem uc22p22vc_apply_mul (ρ : Representation (ZMod 2) H W) (g h : H) (w : W) :
    ρ (g * h) w = ρ g (ρ h w) := by
  rw [map_mul, Module.End.mul_apply]

private theorem uc22p22vc_exists_fixed {K : Type} [Group K] (hK : IsPGroup 2 K) [Finite W]
    (σ : Representation (ZMod 2) K W) (N : Submodule (ZMod 2) W)
    (hN : ∀ k : K, ∀ v ∈ N, σ k v ∈ N) (hne : N ≠ ⊥) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ k : K, σ k v = v := by
  let _ : MulAction K N :=
    { smul := fun k v => ⟨σ k v, hN k v v.2⟩
      one_smul := fun v => Subtype.ext (by
        change σ 1 (v : W) = v
        rw [map_one, Module.End.one_apply])
      mul_smul := fun k l v => Subtype.ext (by
        change σ (k * l) (v : W) = σ k (σ l (v : W))
        exact uc22p22vc_apply_mul σ k l v) }
  have h2 : 2 ∣ Nat.card N := by
    rw [CFSG.RankThree.FFModules.card_eq_two_pow_finrank N]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.1 (Submodule.one_le_finrank_iff.2 hne))
  have h0 : (0 : N) ∈ MulAction.fixedPoints K N := fun k => Subtype.ext (map_zero (σ k))
  obtain ⟨v, hv, hv0⟩ := hK.exists_fixed_point_of_prime_dvd_card_of_fixed_point N h2 h0
  refine ⟨v, v.2, fun h => hv0 (Subtype.ext h.symm), fun k => ?_⟩
  exact congrArg Subtype.val (hv k)

private theorem uc22p22vc_apply_mem_fixSub (ρ : Representation (ZMod 2) H W) {A : Subgroup H}
    {g : H} (hg : g ∈ Subgroup.normalizer (A : Set H)) {u : W} (hu : u ∈ fixSub ρ A) :
    ρ g u ∈ fixSub ρ A := by
  refine CFSG.RankThree.FFModules.rep_apply_mem_fixSub_of_conj_mem ρ (fun h hh => ?_) hu
  have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) h).1 hh
  rwa [inv_inv] at this

private theorem uc22p22vc_sum_conj (ρ : Representation (ZMod 2) H W) (B : Subgroup H) [Fintype B]
    {b₀ : H} (hb₀ : b₀ ∈ B) (u : W) : ∑ b : B, ρ (b : H) (ρ b₀ u - u) = 0 := by
  simp only [map_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  refine Fintype.sum_equiv (Equiv.mulRight (⟨b₀, hb₀⟩ : B)) _ _ (fun b => ?_)
  exact (uc22p22vc_apply_mul ρ (b : H) b₀ u).symm

private theorem uc22p22vc_B_trivial_on_U [Finite H] [Finite W] (ρ : Representation (ZMod 2) H W)
    (T B S : Subgroup H) (hT : IsPGroup 2 T) (hBodd : Odd (Nat.card B))
    (hfix : fixSub ρ T ≤ fixSub ρ B) (hBS : B ≤ Subgroup.normalizer (S : Set H))
    (hTS : ∀ n ∈ T ⊓ Subgroup.normalizer (B : Set H), n ∈ Subgroup.normalizer (S : Set H))
    (hdec : ∀ t ∈ T, ∃ s ∈ S, ∃ n ∈ T ⊓ Subgroup.normalizer (B : Set H), t = s * n) :
    ∀ b ∈ B, ∀ u ∈ fixSub ρ S, ρ b u = u := by
  classical
  have hUinv : ∀ g ∈ Subgroup.normalizer (S : Set H), ∀ u ∈ fixSub ρ S, ρ g u ∈ fixSub ρ S :=
    fun g hg u hu => uc22p22vc_apply_mem_fixSub ρ hg hu
  set G0 : Set W := {w | ∃ b ∈ B, ∃ u ∈ fixSub ρ S, w = ρ b u - u}
  set W' : Submodule (ZMod 2) W := Submodule.span (ZMod 2) G0
  have hG0U : ∀ w ∈ G0, w ∈ fixSub ρ S := by
    rintro _ ⟨b, hb, u, hu, rfl⟩
    exact (fixSub ρ S).sub_mem (hUinv b (hBS hb) u hu) hu
  have hinv : ∀ t ∈ T, ∀ w ∈ W', ρ t w ∈ W' := by
    intro t ht
    have hle : W' ≤ W'.comap (ρ t) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, u, hu, rfl⟩
      obtain ⟨s, hs, n, hn, rfl⟩ := hdec t ht
      have hnN : n ∈ Subgroup.normalizer (B : Set H) := (Subgroup.mem_inf.1 hn).2
      have hb' : n * b * n⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hnN b).1 hb
      have hu' : ρ n u ∈ fixSub ρ S := hUinv n (hTS n hn) u hu
      have hmem : ρ (n * b * n⁻¹) (ρ n u) - ρ n u ∈ G0 := ⟨n * b * n⁻¹, hb', ρ n u, hu', rfl⟩
      have hval : ρ n (ρ b u - u) = ρ (n * b * n⁻¹) (ρ n u) - ρ n u := by
        rw [map_sub, ← uc22p22vc_apply_mul, ← uc22p22vc_apply_mul, inv_mul_cancel_right]
      show ρ (s * n) (ρ b u - u) ∈ W'
      rw [uc22p22vc_apply_mul, hval, hG0U _ hmem s hs]
      exact Submodule.subset_span hmem
    exact fun w hw => hle hw
  have hW0 : W' = ⊥ := by
    by_contra hne
    obtain ⟨w, hwW, hw0, hwfix⟩ := uc22p22vc_exists_fixed hT (ρ.comp T.subtype) W'
      (fun k v hv => hinv k k.2 v hv) hne
    have hwB : ∀ b ∈ B, ρ b w = w := fun b hb =>
      hfix (show w ∈ fixSub ρ T from fun t ht => hwfix ⟨t, ht⟩) b hb
    haveI : Fintype B := Fintype.ofFinite B
    let e : W →ₗ[ZMod 2] W := ∑ b : B, ρ (b : H)
    have he : ∀ v, e v = ∑ b : B, ρ (b : H) v := fun v => LinearMap.sum_apply _ _ _
    have h1 : e w = w := by
      have hconst : ∑ b : B, ρ (b : H) w = ∑ _b : B, w :=
        Finset.sum_congr rfl (fun (b : B) _ => hwB (b : H) b.2)
      rw [he, hconst, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_eq_one_iff_odd.2 hBodd, one_smul]
    have h0 : e w = 0 := by
      have hker : W' ≤ LinearMap.ker e := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, hb, u, hu, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, he]
        exact uc22p22vc_sum_conj ρ B hb u
      exact hker hwW
    exact hw0 (h1.symm.trans h0)
  intro b hb u hu
  have hmem : ρ b u - u ∈ W' := Submodule.subset_span ⟨b, hb, u, hu, rfl⟩
  rw [hW0, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

private theorem uc22p22vc_Y_trivial [Finite H] [Finite W] (ρ : Representation (ZMod 2) H W)
    (hρ : Function.Injective ρ) (S Y : Subgroup H) (hS : IsPGroup 2 S)
    (hYodd : Odd (Nat.card Y)) (hYS : Y ≤ Subgroup.centralizer (S : Set H))
    (hY : ∀ y ∈ Y, ∀ u ∈ fixSub ρ S, ρ y u = u) : Y = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup 2 (Multiplicative W) := fun v =>
    ⟨1, by rw [pow_one]; exact CFSG.RankThree.FFModules.multiplicative_sq v⟩
  let α : ↥Y →* MulAut (Multiplicative W) :=
    (CFSG.RankThree.FFModules.repMulAut ρ).comp Y.subtype
  let β : ↥S →* MulAut (Multiplicative W) :=
    (CFSG.RankThree.FFModules.repMulAut ρ).comp S.subtype
  have hcomm : ∀ (a : Y) (b : S), α a * β b = β b * α a := by
    intro a b
    have hab : (a : H) * b = b * a := (Subgroup.mem_centralizer_iff.1 (hYS a.2) b b.2).symm
    show CFSG.RankThree.FFModules.repMulAut ρ (a : H) * CFSG.RankThree.FFModules.repMulAut ρ (b : H)
      = CFSG.RankThree.FFModules.repMulAut ρ (b : H) * CFSG.RankThree.FFModules.repMulAut ρ (a : H)
    rw [← map_mul, ← map_mul, hab]
  have hfix : ∀ (a : Y) (r : Multiplicative W), (∀ b : S, β b r = r) → α a r = r := by
    intro a r hr
    have hr' : Multiplicative.toAdd r ∈ fixSub ρ S := by
      intro s hs
      have := congrArg Multiplicative.toAdd (hr ⟨s, hs⟩)
      simpa [β, CFSG.RankThree.FFModules.repMulAut_apply] using this
    show Multiplicative.ofAdd (ρ (a : H) (Multiplicative.toAdd r)) = r
    rw [hY a a.2 _ hr']
    rfl
  have h := CFSG.GroupTheory.thompson_A_times_B hRp
    (fun h2 => (Nat.not_even_iff_odd.2 hYodd) (even_iff_two_dvd.2 h2)) hS α β hcomm hfix
  rw [eq_bot_iff]
  intro y hy
  have h1 : CFSG.RankThree.FFModules.repMulAut ρ y = CFSG.RankThree.FFModules.repMulAut ρ 1 := by
    rw [map_one]
    exact h ⟨y, hy⟩
  exact Subgroup.mem_bot.2 (CFSG.RankThree.FFModules.repMulAut_injective hρ h1)

end Module

theorem uc22p22vc_thompson_step {H : Type} [Group H] [Finite H]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) H W) (hρ : Function.Injective ρ)
    (T B X : Subgroup H) (hT : IsPGroup 2 T) (hBab : IsMulCommutative B)
    (hBodd : Odd (Nat.card B)) (hperm : Permutes B T) (hfix : fixSub ρ T ≤ fixSub ρ B)
    (hXodd : Odd (Nat.card X)) (hXnorm : B ⊔ T ≤ Subgroup.normalizer (X : Set H))
    (hXS : X ≤ Subgroup.centralizer ((F05.sOf T B B : Subgroup H) : Set H)) :
    X ≤ Subgroup.centralizer (B : Set H) := by
  obtain ⟨-, hdec⟩ := uc22p22vb_five_six T B hT hBab hBodd hperm
  set R : Subgroup H := pCoreOf 2 (B ⊔ T)
  set S : Subgroup H := F05.sOf T B B
  have hRN : B ⊔ T ≤ Subgroup.normalizer (R : Set H) := uc22p22vc_le_normalizer_pCoreOf (B ⊔ T)
  have hSdef : S = ⁅R, B⁆ := rfl
  have hBS : B ≤ Subgroup.normalizer (S : Set H) := by
    rw [hSdef]
    exact Subgroup.normalizer_commutator_ge_right R B
  have hTS : ∀ n ∈ T ⊓ Subgroup.normalizer (B : Set H), n ∈ Subgroup.normalizer (S : Set H) :=
    fun n hn => uc22p22vc_mem_normalizer_commutator
      (hRN (Subgroup.mem_sup_right (Subgroup.mem_inf.1 hn).1)) (Subgroup.mem_inf.1 hn).2
  have hSR : S ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.1 (le_sup_left.trans hRN)
  have hRp : IsPGroup 2 R := (CFSG.pCore_isPGroup (p := 2) (G := ↥(B ⊔ T))).map _
  have hS2 : IsPGroup 2 S := hRp.to_le hSR
  have hBU := uc22p22vc_B_trivial_on_U ρ T B S hT hBodd hfix hBS hTS hdec
  let Y : Subgroup H :=
    { carrier := {x | x ∈ X ∧ ∀ u ∈ fixSub ρ S, ρ x u = u}
      mul_mem' := fun {a b} ha hb => ⟨X.mul_mem ha.1 hb.1, fun u hu => by
        rw [uc22p22vc_apply_mul, hb.2 u hu, ha.2 u hu]⟩
      one_mem' := ⟨X.one_mem, fun u _ => by rw [map_one, Module.End.one_apply]⟩
      inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, fun u hu => by
        calc ρ a⁻¹ u = ρ a⁻¹ (ρ a u) := by rw [ha.2 u hu]
          _ = u := by
            rw [← uc22p22vc_apply_mul, inv_mul_cancel, map_one, Module.End.one_apply]⟩ }
  have hYX : Y ≤ X := fun y hy => hy.1
  have hYbot : Y = ⊥ :=
    uc22p22vc_Y_trivial ρ hρ S Y hS2 (Odd.of_dvd_nat hXodd (Subgroup.card_dvd_of_le hYX))
      (hYX.trans hXS) (fun y hy => hy.2)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (X : Set H) := hXnorm (Subgroup.mem_sup_left hb)
  have hxS : ∀ y ∈ X, y ∈ Subgroup.normalizer (S : Set H) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (hXS hy)
  have hc : x * b * x⁻¹ * b⁻¹ ∈ Y := by
    refine ⟨?_, fun u hu => ?_⟩
    · have h1 : b * x⁻¹ * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 hbN x⁻¹).1 (X.inv_mem hx)
      have h2 := X.mul_mem hx h1
      rwa [← mul_assoc, ← mul_assoc] at h2
    · have h1 : ρ b⁻¹ u = u := hBU b⁻¹ (B.inv_mem hb) u hu
      have h2 : ρ x⁻¹ u ∈ fixSub ρ S := uc22p22vc_apply_mem_fixSub ρ (hxS x⁻¹ (X.inv_mem hx)) hu
      have h3 : ρ b (ρ x⁻¹ u) = ρ x⁻¹ u := hBU b hb _ h2
      rw [uc22p22vc_apply_mul, uc22p22vc_apply_mul, uc22p22vc_apply_mul, h1, h3,
        ← uc22p22vc_apply_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hYbot, Subgroup.mem_bot] at hc
  calc b * x = (x * b * x⁻¹ * b⁻¹)⁻¹ * (x * b) := by group
    _ = x * b := by rw [hc, inv_one, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.UC22
