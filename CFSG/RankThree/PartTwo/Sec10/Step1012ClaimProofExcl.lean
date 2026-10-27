module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec10.Item10Std
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Step1012ClaimProof

section General

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_thetaPreimage_of_invariant {X : Subgroup G}
    {V : Subgroup (X ⧸ aschbacherSolvableCore 3 X)} {x : G}
    (hxX : x ∈ Subgroup.normalizer (X : Set G))
    (hV : ∀ v ∈ V, Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨x, hxX⟩) v ∈ V) :
    x ∈ Subgroup.normalizer ((thetaPreimage X V : Subgroup G) : Set G) := by
  refine Sec4.mem_normalizer_of_conj_mem fun y hy => ?_
  obtain ⟨hyX, hyV⟩ := mem_thetaPreimage_iff.mp hy
  have hxyX : x * y * x⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hxX y).mp hyX
  refine mem_thetaPreimage_iff.mpr ⟨hxyX, ?_⟩
  have key : ((⟨x * y * x⁻¹, hxyX⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) =
      Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨x, hxX⟩)
        ((⟨y, hyX⟩ : X) : X ⧸ aschbacherSolvableCore 3 X) := by
    rw [Sec4.thetaQuotMulAut_mk]
    rfl
  rw [key]
  exact hV _ hyV

end General

section Std


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem false_of_autHyp (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 d)
    (hP : ∀ F : Subgroup (MulAut (X ⧸ aschbacherSolvableCore 3 X)),
      CFSG.Assembly.IsElemAbelian 3 F →
        ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧
          ∃ V : Subgroup (X ⧸ aschbacherSolvableCore 3 X), V ≠ ⊥ ∧ IsPGroup 2 V ∧
            ∀ f ∈ F', ∀ v ∈ V, f v ∈ V) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := sec10D c R L with hD
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd3
    norm_num at hd3
  have hdD : d ∈ D := h.inf_le_D (h.d_mem_inf hdL)
  have hDN : D ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp h.isElemAbelian_D hdD hd1
      X hX
  set ψ : D →* MulAut (X ⧸ aschbacherSolvableCore 3 X) :=
    (Sec4.thetaQuotMulAut X).comp ((Sec4.compAction X).comp (Subgroup.inclusion hDN)) with hψ
  have hrange : CFSG.Assembly.IsElemAbelian 3 ψ.range := by
    rw [MonoidHom.range_eq_map]
    refine Sec4.isElemAbelian_map ψ ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩,
      fun x _ => Subtype.ext ?_⟩
    · exact congrArg Subtype.val (h.isElemAbelian_D.1.is_comm.comm x.1 y.1)
    · simpa using h.isElemAbelian_D.2 x x.2
  obtain ⟨F', hF'F, hcardF', V, hV1, hV2, hVF'⟩ := hP ψ.range hrange
  set F'' := F'.subgroupOf ψ.range with hF''
  set C' := F''.comap ψ.rangeRestrict with hC'
  have hidx : C'.index = F''.index := Subgroup.index_comap_of_surjective F''
    ψ.rangeRestrict_surjective
  have hF''card : Nat.card F'' = Nat.card F' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF'F).toEquiv
  have h1 := Subgroup.card_mul_index F''
  have h2 := Subgroup.card_mul_index C'
  rw [h.card_D] at h2
  rw [hF''card] at h1
  have hidx3 : F''.index ≤ 3 := by
    by_contra hlt
    have hpos : 0 < Nat.card F' := Nat.card_pos
    have : Nat.card F' * 4 ≤ Nat.card F' * F''.index := Nat.mul_le_mul_left _ (by omega)
    omega
  have hC'27 : 27 ≤ Nat.card C' := by
    rw [hidx] at h2
    have hpos : 0 < F''.index := Nat.pos_of_ne_zero (fun h0 => by rw [h0] at h2; norm_num at h2)
    by_contra hlt
    have : Nat.card C' * F''.index ≤ 26 * 3 :=
      Nat.mul_le_mul (by omega) hidx3
    omega
  set E' := C'.map D.subtype with hE'
  have hE'card : Nat.card E' = Nat.card C' := Subgroup.card_map_of_injective D.subtype_injective
  have hE'D : E' ≤ D := Subgroup.map_subtype_le _
  have hE'Y : E' ≤ Subgroup.normalizer ((thetaPreimage X V : Subgroup G) : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxF : ψ x ∈ F' := by
      have hx' : ψ.rangeRestrict x ∈ F'' := hx
      rw [hF'', Subgroup.mem_subgroupOf] at hx'
      exact hx'
    exact mem_normalizer_thetaPreimage_of_invariant (hDN x.2) (hVF' _ hxF)
  have hE'3 : IsPGroup 3 E' := (Sec4.isPGroup_of_isElemAbelian h.isElemAbelian_D).to_le hE'D
  have h27 : 3 ^ 3 ∣ Nat.card E' := by
    obtain ⟨k, hk⟩ := hE'3.exists_card_eq
    rw [hk]
    have hk3 : 3 ≤ k := by
      by_contra hlt
      have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hk, hE'card] at this
      omega
    exact Nat.pow_dvd_pow 3 hk3
  obtain ⟨E, hEcard, -, hEE'⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
    (H := ⊥) (by rw [Subgroup.card_bot]; exact one_dvd _) h27 bot_le
  have hED : E ≤ D := hEE'.trans hE'D
  have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
    ⟨⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
      (h.isElemAbelian_D.1.is_comm.comm ⟨x, hED x.2⟩ ⟨y, hED y.2⟩))⟩⟩,
      fun x hx => h.isElemAbelian_D.2 x (hED hx)⟩
  obtain ⟨T, -, hT1, hT2, hET⟩ := exists_pGroup_le_normalizer (p := 3) (q := 2)
    (Sec4.isPGroup_of_isElemAbelian hEe) (not_three_dvd_card_thetaPreimage hV2)
    (two_dvd_card_thetaPreimage hV2 hV1) (hEE'.trans hE'Y)
  have hEmem : E ∈ partTwoE G := ⟨hEe, by rw [hEcard]; norm_num, T, hT1, hT2, hET⟩
  rw [h.partTwoE_eq h.card_eq] at hEmem
  have hDE := hEmem.2.1 D h.isElemAbelian_D hED
  have h81 : Nat.card D = 81 := h.card_D
  rw [hDE, hEcard] at h81
  norm_num at h81

end Std

end Step1012ClaimProof

end CFSG.RankThree.PartTwo.Sec10
