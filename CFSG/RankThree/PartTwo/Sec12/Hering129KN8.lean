module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KN6
public import CFSG.RankThree.PartTwo.Sec12.Hering129KN7
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEa
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEc
public import CFSG.RankThree.PartTwo.Sec13.Item137Tools

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Hering129KN8

variable {H : Type} [Group H] [Finite H]

theorem isPGroup_two_core {Y : Subgroup H} (hY : Y ∈ thetaComponents 3 H)
    (hT : aschbacherSolvableCore 3 H ≤ Y) (hR2 : IsPGroup 2 (aschbacherSolvableCore 3 Y)) :
    IsPGroup 2 (aschbacherSolvableCore 3 H) := by
  have hin : inSubgroup (aschbacherSolvableCore 3) Y = Y ⊓ aschbacherSolvableCore 3 H :=
    (theta_component_quotient_structure (G := H) Nat.prime_three hY).1
  have hR : aschbacherSolvableCore 3 H = (aschbacherSolvableCore 3 Y).map Y.subtype := by
    change _ = inSubgroup (aschbacherSolvableCore 3) Y
    rw [hin, inf_eq_right.mpr hT]
  rw [hR]
  exact hR2.map Y.subtype

theorem exists_t_of_mk {Y : Subgroup H} (hT : aschbacherSolvableCore 3 H ≤ Y)
    (hR2 : IsPGroup 2 (aschbacherSolvableCore 3 H)) {b c : H} (hb3 : b ^ 3 = 1)
    (hc3 : c ^ 3 = 1) (hbc : b * c = c * b) {th : H ⧸ aschbacherSolvableCore 3 H}
    (hthY : th ∈ Y.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H))) (hth2 : th ^ 2 = 1)
    (hbth : QuotientGroup.mk' (aschbacherSolvableCore 3 H) b * th =
      th * QuotientGroup.mk' (aschbacherSolvableCore 3 H) b)
    (hcth : th * QuotientGroup.mk' (aschbacherSolvableCore 3 H) c * th⁻¹ =
      (QuotientGroup.mk' (aschbacherSolvableCore 3 H) c)⁻¹) :
    ∃ t ∈ Y, IsPGroup 2 (Subgroup.zpowers t) ∧ b * t = t * b ∧ t * c * t⁻¹ = c⁻¹ := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  obtain ⟨t₁, ht₁Y, rfl⟩ := hthY
  have hker : ∀ g : H, π g = 1 → g ∈ aschbacherSolvableCore 3 H := fun g hg =>
    (QuotientGroup.eq_one_iff g).mp hg
  have ht2 : t₁ ^ 2 ∈ aschbacherSolvableCore 3 H := hker _ (by rw [map_pow, hth2])
  have htb : b * t₁ * b⁻¹ * t₁⁻¹ ∈ aschbacherSolvableCore 3 H := hker _ (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hbth]
    group)
  have htc : t₁ * c * t₁⁻¹ * c ∈ aschbacherSolvableCore 3 H := hker _ (by
    rw [map_mul, map_mul, map_mul, map_inv, hcth, inv_mul_cancel])
  obtain ⟨t, ht₁t, ht2', hbt, hct⟩ := exists_t_lift hR2 hb3 hc3 hbc ht2 htb htc
  refine ⟨t, ?_, ht2', hbt, hct⟩
  have ht : t = t₁ * (t₁⁻¹ * t) := by group
  rw [ht]
  exact Y.mul_mem ht₁Y (hT ht₁t)

theorem exists_move_of_mk {Y V : Subgroup H} {c : H} (hT : aschbacherSolvableCore 3 H ≤ Y)
    (hmove : ∀ Vh : Subgroup (H ⧸ aschbacherSolvableCore 3 H),
      Vh ≤ Y.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) →
      CFSG.Assembly.IsElemAbelian 3 Vh → Nat.card Vh = 9 →
      QuotientGroup.mk' (aschbacherSolvableCore 3 H) c ∈ Vh →
      (∃ s ∈ Y.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)),
        ∀ v ∈ Vh, s * v * s⁻¹ = v⁻¹) →
      ∃ n ∈ Y.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) ⊓
        Subgroup.normalizer (Vh : Set (H ⧸ aschbacherSolvableCore 3 H)),
        n * QuotientGroup.mk' (aschbacherSolvableCore 3 H) c * n⁻¹ ∉
          Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 H) c))
    (hVY : V ≤ Y) (hVel : CFSG.Assembly.IsElemAbelian 3 V) (hV9 : Nat.card V = 9)
    (hcV : c ∈ V) (hs : ∃ s ∈ Y, ∀ v ∈ V, s * v * s⁻¹ = v⁻¹) :
    ∃ n ∈ Y ⊓ Subgroup.normalizer (V : Set H), n * c * n⁻¹ ∉ Subgroup.zpowers c := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  have hV3 : IsPGroup 3 V := fun v => ⟨1, Subtype.ext (by simpa using hVel.2 v v.2)⟩
  have hinjV : Set.InjOn π (V : Set H) := injOn_mk_of_isPGroup Nat.prime_three hV3
  obtain ⟨s, hsY, hsV⟩ := hs
  obtain ⟨nh, ⟨hnhY, hnhN⟩, hnhc⟩ := hmove (V.map π) (Subgroup.map_mono hVY)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π V hVel)
    (by rw [Sec13.card_map_eq_of_injOn π hinjV, hV9]) (Subgroup.mem_map_of_mem π hcV)
    ⟨π s, Subgroup.mem_map_of_mem π hsY, by
      rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_inv, ← map_mul, hsV v hv, map_inv]⟩
  have hnh : nh ∈ (Subgroup.normalizer (V : Set H)).map π := by
    rw [← Sec13.normalizer_map_mk_eq hV3]
    exact hnhN
  obtain ⟨n, hnN, rfl⟩ := hnh
  refine ⟨n, ⟨?_, hnN⟩, fun hmem => hnhc ?_⟩
  · obtain ⟨y, hy, hyn⟩ := hnhY
    have h1 : y⁻¹ * n ∈ aschbacherSolvableCore 3 H := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change π (y⁻¹ * n) = 1
      rw [map_mul, map_inv, hyn, inv_mul_cancel]
    have hn : n = y * (y⁻¹ * n) := by group
    rw [hn]
    exact Y.mul_mem hy (hT h1)
  · have h2 : π (n * c * n⁻¹) ∈ Subgroup.zpowers (π c) := by
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem π hmem
    rwa [map_mul, map_mul, map_inv] at h2

end Hering129KN8


theorem exists_t_move (hDeg : Gap129HessL3Deg)
    {H : Type} [Group H] [Finite H] {Y A : Subgroup H} {x b c : H}
    (hYn : Y.Normal) (hY : Y ∈ thetaComponents 3 H) (hYA : Y ⊔ A = ⊤)
    (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hgen : A = Subgroup.zpowers x ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c)
    (hx1 : x ≠ 1) (hxc : ∀ h : H, x * h = h * x) (hxY : x ∉ Y) (hcY : c ∈ Y)
    (hbxc : b ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers c)
    (hAC : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers x)
    (hX : ∃ X : Subgroup H, X ≤ Y ∧ X ≤ Subgroup.centralizer ({b} : Set H) ∧
      Group.IsPerfect X ∧ (X.subgroupOf (Y ⊓ Subgroup.centralizer ({b} : Set H))).IsSubnormal ∧
      c ∈ X ∧ ∃ (p n : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ n ∧
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField p n)))
    (hkind : ∀ e ∈ A, ¬ KFacts.InducesStdKind Y e .field ∧
      ¬ KFacts.InducesStdKind Y e .graphField)
    (hty : ∃ (p e : ℕ) (_ : Fact p.Prime),
      Sec4.IsoLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) p e)
    (hR2 : IsPGroup 2 (aschbacherSolvableCore 3 Y)) :
    (∃ t ∈ Y, IsPGroup 2 (Subgroup.zpowers t) ∧ b * t = t * b ∧ t * c * t⁻¹ = c⁻¹) ∧
    (∀ V : Subgroup H, V ≤ Y → CFSG.Assembly.IsElemAbelian 3 V → Nat.card V = 9 → c ∈ V →
      (∃ s ∈ Y, ∀ v ∈ V, s * v * s⁻¹ = v⁻¹) →
      ∃ n ∈ Y ⊓ Subgroup.normalizer (V : Set H), n * c * n⁻¹ ∉ Subgroup.zpowers c) := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  have hA3 : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAel.2 a a.2)⟩
  have hbA : b ∈ A :=
    hgen ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hcA : c ∈ A := hgen ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have hc3 : c ^ 3 = 1 := hAel.2 c hcA
  have hbc : b * c = c * b := congrArg Subtype.val (hAel.1.is_comm.comm ⟨b, hbA⟩ ⟨c, hcA⟩)
  have hT : aschbacherSolvableCore 3 H ≤ Y := by
    haveI := hYn
    exact Hering129KEa.theta_le_of_sup_eq_top hA3 hYA
  have hHD := hessData_of_core hYn hY hT hAel hA27 hgen hb3 hxc hcY hAC hX hkind
  obtain ⟨η, -⟩ := (theta_component_quotient_structure (G := H) Nat.prime_three hY).2.2.1
  have hex : ∃ (p e : ℕ) (_ : Fact p.Prime), Sec4.IsoLThreePi ↥(Y.map π) p e := by
    obtain ⟨p, e, hp, hiso⟩ := hty
    refine ⟨p, e, hp, ?_⟩
    rcases hiso with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
    · exact Or.inl ⟨h1, ⟨η.symm.trans f⟩⟩
    · exact Or.inr ⟨h2, ⟨η.symm.trans f⟩⟩
  obtain ⟨th, hthY, hth2, hbth, hcth, hmove⟩ := hess_t_move hDeg hHD hex
  exact ⟨Hering129KN8.exists_t_of_mk hT (Hering129KN8.isPGroup_two_core hY hT hR2) hb3 hc3 hbc
      hthY hth2 hbth hcth,
    fun V hVY hVel hV9 hcV hs => Hering129KN8.exists_move_of_mk hT hmove hVY hVel hV9 hcV hs⟩

end CFSG.RankThree.PartTwo.Sec12
