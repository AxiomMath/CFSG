module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenDInf
public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenPushUp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

private theorem exists_pow_mul_eq {N : Subgroup G} {n d : G} (hn : n ∈ N)
    (hd : d ∈ Subgroup.normalizer (N : Set G)) (m : ℕ) :
    ∃ n' ∈ N, (n * d) ^ m = n' * d ^ m := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨n', hn', h⟩ := ih
    refine ⟨n * (d * n' * d⁻¹), N.mul_mem hn ((Subgroup.mem_normalizer_iff.1 hd n').1 hn'), ?_⟩
    rw [pow_succ', h, pow_succ']
    group

theorem le_of_le_sup_of_oResidualTwo_eq_top {L N D : Subgroup G} (hres : oResidualTwo ↥L = ⊤)
    (hD : IsPGroup 2 ↥D) (hDN : D ≤ Subgroup.normalizer (N : Set G)) (hL : L ≤ N ⊔ D) :
    L ≤ N := by
  have hLN : L ≤ Subgroup.normalizer (N : Set G) :=
    hL.trans (sup_le Subgroup.le_normalizer hDN)
  haveI : (N.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLN
  have htop : N.subgroupOf L = ⊤ := by
    refine (oResidualTwo_eq_top_iff.1 hres) _ inferInstance fun g => ?_
    have hg : (g : G) ∈ ((N ⊔ D : Subgroup G) : Set G) := hL g.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N D hDN] at hg
    obtain ⟨n, hn, d, hd', hgnd⟩ := hg
    obtain ⟨k, hk⟩ := hD ⟨d, hd'⟩
    refine ⟨k, ?_⟩
    have hdk : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨n', hn', h⟩ := exists_pow_mul_eq hn (hDN hd') (2 ^ k)
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_pow]
    rw [← hgnd, h, hdk, mul_one]
    exact hn'
  intro l hl
  have : (⟨l, hl⟩ : ↥L) ∈ N.subgroupOf L := by rw [htop]; trivial
  exact this

private theorem mem_conj_smul_iff_aux {g z : G} {Y : Subgroup G} :
    z ∈ MulAut.conj g • Y ↔ g⁻¹ * z * g ∈ Y := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]

private theorem conj_mem_sup_of_mem {A B C : Subgroup G} {y : G}
    (hA : ∀ a ∈ A, y * a * y⁻¹ ∈ C) (hB : ∀ b ∈ B, y * b * y⁻¹ ∈ C) :
    ∀ n ∈ A ⊔ B, y * n * y⁻¹ ∈ C := by
  intro n hn
  have hmap : (A ⊔ B).map (MulAut.conj y).toMonoidHom ≤ C := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hA a ha
    · rintro _ ⟨b, hb, rfl⟩
      exact hB b hb
  exact hmap ⟨n, hn, rfl⟩

theorem eleven11_le_join_conj {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) (h8 : Nat.card V = 8) {x : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G))
    (hxD : ¬ MulAut.conj x • blockU L ≤ centralizerModCore L) :
    ∃ k ∈ L, L ≤ (MulAut.conj x • blockU L) ⊔ (MulAut.conj (k * x) • blockU L) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ψ, p, hαsurj, hαker, -, -, -, hαS, -⟩ := eleven11_exists_model hd h8
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hO2Q : oTwoIn L ≤ Q := eleven_nine_oTwoIn_le_Q hd.setting hUΓ hLb
  have h := eleven11_transvPair hd h8
  have h' := h.conj hx
  have hne := eleven11_conj_not_le_centralizer hd h8 hx hxD
  have hQ : MulAut.conj x • blockU L ⊔ (Q ⊓ centralizerModCore L) = Q := by
    rw [← eleven11_cent_blockU_eq hd h8]
    exact h.sup_inf_centralizer_eq h' hne
  obtain ⟨m, hm⟩ := CFSG.QuasithinUnique.Setup.Campbell.exists_ne_point p
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) p m
  obtain ⟨k, rfl⟩ := hαsurj g
  have hkp : p ≠ α k • p := by
    intro hh
    exact hm (by rw [← hg, ← hh])
  refine ⟨(k : G), k.2, ?_⟩
  have hDQ : ∀ y ∈ Q ⊓ centralizerModCore L, y ∈ Q := fun y hy => (Subgroup.mem_inf.1 hy).1
  have hkD : ∀ y ∈ Q ⊓ centralizerModCore L, (k : G)⁻¹ * y * (k : G) ∈ Q ⊓ centralizerModCore L :=
    fun y hy => by
      simpa using eleven11_normalizer_D hd _ (inv_mem k.2) y hy
  have hWx : ∀ y ∈ Q ⊓ centralizerModCore L, ∀ w ∈ MulAut.conj x • blockU L,
      y * w * y⁻¹ ∈ MulAut.conj x • blockU L := fun y hy w hw => h'.normal y (hDQ y hy) w hw
  have hWxk : ∀ y ∈ Q ⊓ centralizerModCore L, ∀ w ∈ MulAut.conj ((k : G) * x) • blockU L,
      y * w * y⁻¹ ∈ MulAut.conj ((k : G) * x) • blockU L := by
    intro y hy w hw
    rw [mem_conj_smul_iff_aux] at hw ⊢
    have hw' : (k : G)⁻¹ * w * (k : G) ∈ MulAut.conj x • blockU L := by
      rw [mem_conj_smul_iff_aux]
      simpa [mul_assoc] using hw
    have := hWx _ (hkD y hy) _ hw'
    rw [mem_conj_smul_iff_aux] at this
    simpa [mul_assoc] using this
  set D := Q ⊓ centralizerModCore L with hD
  set N := (MulAut.conj x • blockU L) ⊔ (MulAut.conj ((k : G) * x) • blockU L) with hN
  have hNle1 : MulAut.conj x • blockU L ≤ N := le_sup_left
  have hNle2 : MulAut.conj ((k : G) * x) • blockU L ≤ N := le_sup_right
  have hDN : D ≤ Subgroup.normalizer (N : Set G) := by
    have key : ∀ y ∈ D, ∀ n ∈ N, y * n * y⁻¹ ∈ N := fun y hy =>
      conj_mem_sup_of_mem (fun a ha => hNle1 (hWx y hy a ha)) (fun b hb => hNle2 (hWxk y hy b hb))
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨key y hy n, fun hn => ?_⟩
    have := key y⁻¹ (D.inv_mem hy) _ hn
    simpa [mul_assoc] using this
  have hQN : Q ≤ N ⊔ D :=
    calc Q = (MulAut.conj x • blockU L) ⊔ D := hQ.symm
      _ ≤ N ⊔ D := sup_le_sup_right hNle1 D
  have hkQ : ∀ t ∈ Q, (k : G) * t * (k : G)⁻¹ ∈ N ⊔ D := by
    intro t ht
    rw [← hQ] at ht
    refine conj_mem_sup_of_mem (A := MulAut.conj x • blockU L) (B := D) ?_ ?_ t ht
    · intro w hw
      refine Subgroup.mem_sup_left (hNle2 ?_)
      rw [mem_conj_smul_iff_aux]
      rw [mem_conj_smul_iff_aux] at hw
      simpa [mul_assoc] using hw
    · intro d hdd
      exact Subgroup.mem_sup_right (eleven11_normalizer_D hd _ k.2 d hdd)
  have hL : L ≤ N ⊔ D := by
    let H : Subgroup ↥L := (N ⊔ D).subgroupOf L
    have hTH : (L ⊓ Q).subgroupOf L ≤ H := by
      intro t ht
      rw [Subgroup.mem_subgroupOf] at ht ⊢
      exact hQN (Subgroup.mem_inf.1 ht).2
    have hker : α.ker ≤ H := by
      intro t ht
      rw [hαker, Subgroup.mem_subgroupOf] at ht
      rw [Subgroup.mem_subgroupOf]
      exact hQN (hO2Q ht)
    have hmap : CFSG.QuasithinUnique.Setup.Campbell.rootGrp p ⊔
        CFSG.QuasithinUnique.Setup.Campbell.rootGrp (α k • p) ≤ H.map α := by
      refine sup_le ?_ ?_
      · rw [← hαS]
        exact Subgroup.map_mono hTH
      · intro y hy
        rw [CFSG.QuasithinUnique.Setup.Campbell.mem_rootGrp_smul_iff, ← hαS] at hy
        obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hy
        refine Subgroup.mem_map.2 ⟨k * t * k⁻¹, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          have := hkQ _ (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 ht)).2
          simpa using this
        · rw [map_mul, map_mul, map_inv, hty]
          group
    have htop : H.map α = ⊤ := top_le_iff.1
      (CFSG.QuasithinUnique.Setup.Campbell.rootGrp_sup_rootGrp hkp ▸ hmap)
    have hHtop : H = ⊤ := by
      have h1 := Subgroup.comap_map_eq α H
      rw [htop, Subgroup.comap_top, sup_eq_left.2 hker] at h1
      exact h1.symm
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ H := by rw [hHtop]; trivial
    exact this
  have hDp : IsPGroup 2 ↥D := hd.setting.sylowQ.2.1.to_le inf_le_left
  exact le_of_le_sup_of_oResidualTwo_eq_top hLb.2.2.1.residual_eq hDp hDN hL

end CFSG.LocalAnalysis.WeakClosure81
