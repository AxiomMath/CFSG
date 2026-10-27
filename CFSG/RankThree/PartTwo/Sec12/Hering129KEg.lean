module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KEf
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEb
public import CFSG.RankThree.PartTwo.Sec11.Item119

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

theorem isSubnormal_subgroupOf_sub {G : Type} [Group G] {W M X : Subgroup G}
    (hMW : M ≤ W) (h : (X.subgroupOf M).IsSubnormal) :
    ((X.subgroupOf W).subgroupOf (M.subgroupOf W)).IsSubnormal := by
  have heq : (X.subgroupOf M).comap (Subgroup.subgroupOfEquivOfLe hMW).toMonoidHom =
      (X.subgroupOf W).subgroupOf (M.subgroupOf W) := by
    ext z
    rfl
  rw [← heq]
  exact h.comap _

theorem mem_thetaQuotCentralizer_sub {G : Type} [Group G] [Finite G] {W Y : Subgroup G}
    (hYW : Y ≤ W) (a : W) :
    a ∈ Sec4.thetaQuotCentralizer (Y.subgroupOf W) ↔ (a : G) ∈ Sec4.thetaQuotCentralizer Y := by
  have hY : (Y.subgroupOf W).map W.subtype = Y := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hYW]
  have key : ∀ z : W, z ∈ inSubgroup (aschbacherSolvableCore 3) (Y.subgroupOf W) ↔
      (z : G) ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
    intro z
    have h := CFSG.RankThree.PartTwo.Sec11.inSubgroup_theta_map_subtype_sub (Y.subgroupOf W)
    rw [hY] at h
    rw [h]
    exact (Subgroup.mem_map_iff_mem W.subtype_injective).symm
  rw [Sec6.mem_thetaQuotCentralizer_iff, Sec6.mem_thetaQuotCentralizer_iff]
  constructor
  · rintro ⟨hN, hl⟩
    refine ⟨?_, fun l hl' => ?_⟩
    · have h1 := (Hering129KEb.coe_mem_normalizer_map_subtype_iff (X := Y.subgroupOf W)
        (h := a)).mpr hN
      rwa [hY] at h1
    · have h2 := hl ⟨l, hYW hl'⟩ (Subgroup.mem_subgroupOf.mpr hl')
      have h3 := (key _).mp h2
      exact h3
  · rintro ⟨hN, hl⟩
    refine ⟨?_, fun l hl' => ?_⟩
    · have h1 : (a : G) ∈ Subgroup.normalizer
          (((Y.subgroupOf W).map W.subtype : Subgroup G) : Set G) := by
        rw [hY]
        exact hN
      exact Hering129KEb.coe_mem_normalizer_map_subtype_iff.mp h1
    · exact (key (l⁻¹ * (a * l * a⁻¹))).mpr (hl (l : G) (Subgroup.mem_subgroupOf.mp hl'))

theorem subgroupOf_inf_centralizer_sub {G : Type} [Group G] {W Y : Subgroup G} {b : G}
    (b₀ : W) (hb₀ : (b₀ : G) = b) :
    Y.subgroupOf W ⊓ Subgroup.centralizer ({b₀} : Set W) =
      (Y ⊓ Subgroup.centralizer ({b} : Set G)).subgroupOf W := by
  have hc : ∀ z : W, z * b₀ = b₀ * z ↔ (z : G) * b = b * (z : G) := fun z => by
    rw [← hb₀, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul]
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  exact and_congr Iff.rfl (hc z)


theorem inducesStdKind_sub_map {G : Type} [Group G] [Finite G] {W Y : Subgroup G}
    {e : W} {k : KFacts.AutKind} (hY : (Y.subgroupOf W).map W.subtype = Y)
    (hk : KFacts.InducesStdKind (Y.subgroupOf W) e k) : KFacts.InducesStdKind Y (e : G) k := by
  have h := KFacts.InducesStdKind.map W.subtype (Y.subgroupOf W)
    (KFacts.thetaQuotMap_iff_of_injective W.subtype W.subtype_injective (Y.subgroupOf W)) hk
  rw [hY] at h
  exact h

theorem exists_E_of_hess_sub (hL3 : Gap129HessL3) (hD4 : Gap129HessD4)
    {G : Type} [Group G] [Finite G] {Y A : Subgroup G} {x b c : G}
    (hAN : A ≤ Subgroup.normalizer (Y : Set G)) (hYp : Group.IsPerfect Y)
    (hYq : CFSG.IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y))
    (hAel : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hgen : A = Subgroup.zpowers x ⊔ Subgroup.zpowers b ⊔ Subgroup.zpowers c)
    (hx1 : x ≠ 1) (hxc : ∀ w ∈ Y ⊔ A, x * w = w * x) (hxY : x ∉ Y) (hcY : c ∈ Y)
    (hbxc : b ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers c)
    (hAC : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers x)
    (hX : ∃ X : Subgroup G, X ≤ Y ∧ X ≤ Subgroup.centralizer ({b} : Set G) ∧
      Group.IsPerfect X ∧ (X.subgroupOf (Y ⊓ Subgroup.centralizer ({b} : Set G))).IsSubnormal ∧
      c ∈ X ∧ ∃ (p n : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ n ∧
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSL 2 (GaloisField p n)))
    (hkind : ∀ e ∈ A, ¬ KFacts.InducesStdKind Y e .field ∧
      ¬ KFacts.InducesStdKind Y e .graphField)
    (hty : (∃ (p e : ℕ) (_ : Fact p.Prime),
        Sec4.IsoLThreePi (Y ⧸ aschbacherSolvableCore 3 Y) p e) ∨
      ∃ (r : TauCeti.PrimePower) (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid), r.p = 2 ∧
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃*
          (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group)) :
    ∃ E : Subgroup G, Typ129IIIcE A c Y x E := by
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, W = Y ⊔ A := ⟨_, rfl⟩
  have hYA : Y ⊔ A = W := hW.symm
  have hYW : Y ≤ W := by
    rw [hW]
    exact le_sup_left
  have hAW : A ≤ W := by
    rw [hW]
    exact le_sup_right
  have hWN : W ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hW]
    exact sup_le Subgroup.le_normalizer hAN
  have hbA : b ∈ A :=
    hgen ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hxA : x ∈ A :=
    hgen ▸ Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hcA : c ∈ A := hgen ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : W, (x₀ : G) = x := ⟨⟨x, hAW hxA⟩, rfl⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : W, (b₀ : G) = b := ⟨⟨b, hAW hbA⟩, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : W, (c₀ : G) = c := ⟨⟨c, hAW hcA⟩, rfl⟩
  have e1 : W.subtype x₀ = x := hx₀
  have e2 : W.subtype b₀ = b := hb₀
  have e3 : W.subtype c₀ = c := hc₀
  have hA₀map : (A.subgroupOf W).map W.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAW]
  have hY₀map : (Y.subgroupOf W).map W.subtype = Y := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hYW]
  have hgen₀ : A.subgroupOf W =
      Subgroup.zpowers x₀ ⊔ Subgroup.zpowers b₀ ⊔ Subgroup.zpowers c₀ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [hA₀map, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers, e1, e2, e3]
    exact hgen
  have hAel₀ : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf W) := by
    apply CFSG.RankThree.PartTwo.Sec13.isElemAbelian_of_injOn W.subtype
      W.subtype_injective.injOn
    rw [hA₀map]
    exact hAel
  have hA27₀ : Nat.card (A.subgroupOf W) = 27 := by
    rw [← Subgroup.card_map_of_injective (K := A.subgroupOf W) W.subtype_injective, hA₀map,
      hA27]
  have hYn₀ : (Y.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hWN
  have hYp₀ : Group.IsPerfect (Y.subgroupOf W) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hYW).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYW).symm.surjective
  have hYq₀ : CFSG.IsQuasisimple (Y.subgroupOf W ⧸ aschbacherSolvableCore 3 (Y.subgroupOf W)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hYW)
        (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three
          (Subgroup.subgroupOfEquivOfLe hYW))).symm hYq
  have hY₀ : Y.subgroupOf W ∈ thetaComponents 3 ↥W :=
    ⟨hYp₀, Subgroup.Normal.isSubnormal hYn₀, hYq₀⟩
  have hYA₀ : Y.subgroupOf W ⊔ A.subgroupOf W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hYW hAW, hYA, Subgroup.subgroupOf_self]
  have hx₁ : x₀ ≠ 1 := by
    intro h
    apply hx1
    rw [← hx₀, h, Subgroup.coe_one]
  have hxc₀ : ∀ h : W, x₀ * h = h * x₀ := by
    intro h
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx₀]
    exact hxc _ (by rw [hYA]; exact h.2)
  have hxY₀ : x₀ ∉ Y.subgroupOf W := by
    intro h
    apply hxY
    rw [← hx₀]
    exact Subgroup.mem_subgroupOf.mp h
  have hcY₀ : c₀ ∈ Y.subgroupOf W :=
    Subgroup.mem_subgroupOf.mpr (by rw [hc₀]; exact hcY)
  have hbxc₀ : b₀ ∉ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers c₀ := by
    intro h
    apply hbxc
    have h' := Subgroup.mem_map_of_mem W.subtype h
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, e1, e2, e3] at h'
    exact h'
  have hAC₀ : A.subgroupOf W ⊓ Sec4.thetaQuotCentralizer (Y.subgroupOf W) =
      Subgroup.zpowers x₀ := by
    have hz : ∀ a : W, a ∈ Subgroup.zpowers x₀ ↔ (a : G) ∈ Subgroup.zpowers x := by
      intro a
      have h1 : (Subgroup.zpowers x₀).map W.subtype = Subgroup.zpowers x := by
        rw [MonoidHom.map_zpowers, e1]
      rw [← h1]
      exact (Subgroup.mem_map_iff_mem W.subtype_injective).symm
    ext a
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_thetaQuotCentralizer_sub hYW a,
      hz a, ← hAC, Subgroup.mem_inf]
  have hkind₀ : ∀ e ∈ A.subgroupOf W, ¬ KFacts.InducesStdKind (Y.subgroupOf W) e .field ∧
      ¬ KFacts.InducesStdKind (Y.subgroupOf W) e .graphField := by
    intro e he
    obtain ⟨h1, h2⟩ := hkind (e : G) (Subgroup.mem_subgroupOf.mp he)
    exact ⟨fun h => h1 (inducesStdKind_sub_map hY₀map h),
      fun h => h2 (inducesStdKind_sub_map hY₀map h)⟩
  have htyW : (∃ (p e : ℕ) (_ : Fact p.Prime),
        Sec4.IsoLThreePi (Y.subgroupOf W ⧸ aschbacherSolvableCore 3 (Y.subgroupOf W)) p e) ∨
      ∃ (r : TauCeti.PrimePower) (hr : (TauCeti.LieTypeIndex.trialityD4 r).Valid),
        r.p = 2 ∧ Nonempty (Y.subgroupOf W ⧸ aschbacherSolvableCore 3 (Y.subgroupOf W) ≃*
          (TauCeti.CFSGIndex.lie ⟨.trialityD4 r, hr⟩).Group) := by
    have ηY : (Y.subgroupOf W ⧸ aschbacherSolvableCore 3 (Y.subgroupOf W)) ≃*
        (Y ⧸ aschbacherSolvableCore 3 Y) :=
      QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hYW)
        (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three
          (Subgroup.subgroupOfEquivOfLe hYW))
    rcases hty with ⟨p, e, hp, hiso⟩ | ⟨r, hr, hr2, ⟨ee⟩⟩
    · refine Or.inl ⟨p, e, hp, ?_⟩
      rcases hiso with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
      · exact Or.inl ⟨h1, ⟨ηY.trans f⟩⟩
      · exact Or.inr ⟨h2, ⟨ηY.trans f⟩⟩
    · exact Or.inr ⟨r, hr, hr2, ⟨ηY.trans ee⟩⟩
  have hX₀ : ∃ X₀ : Subgroup W, X₀ ≤ Y.subgroupOf W ∧
      X₀ ≤ Subgroup.centralizer ({b₀} : Set W) ∧ Group.IsPerfect X₀ ∧
      (X₀.subgroupOf (Y.subgroupOf W ⊓ Subgroup.centralizer ({b₀} : Set W))).IsSubnormal ∧
      c₀ ∈ X₀ ∧ ∃ (p n : ℕ) (_ : Fact p.Prime), 4 ≤ p ^ n ∧
        Nonempty (X₀ ⧸ aschbacherSolvableCore 3 X₀ ≃* projSL 2 (GaloisField p n)) := by
    obtain ⟨X, hXY, hXb, hXp, hXsn, hcX, p, n, hp, hpn, ⟨e⟩⟩ := hX
    have hXW : X ≤ W := hXY.trans hYW
    refine ⟨X.subgroupOf W, Subgroup.subgroupOf_mono W hXY, ?_, ?_, ?_, ?_, p, n, hp, hpn, ?_⟩
    · intro k hk
      rw [Subgroup.mem_subgroupOf] at hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hb₀]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hXb hk)
    · haveI : Group.IsPerfect X := hXp
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXW).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hXW).symm.surjective
    · rw [subgroupOf_inf_centralizer_sub b₀ hb₀]
      exact isSubnormal_subgroupOf_sub (M := Y ⊓ Subgroup.centralizer ({b} : Set G))
        (inf_le_left.trans hYW) hXsn
    · exact Subgroup.mem_subgroupOf.mpr (by rw [hc₀]; exact hcX)
    · exact ⟨(QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hXW)
        (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three
          (Subgroup.subgroupOfEquivOfLe hXW))).trans e⟩
  obtain ⟨E₀, hE₀⟩ := CFSG.RankThree.PartTwo.Sec12.exists_E_of_hess hL3 hD4
    (Y := Y.subgroupOf W) (A := A.subgroupOf W) (x := x₀) (b := b₀) (c := c₀)
    hYn₀ hY₀ hYA₀ hAel₀ hA27₀ hgen₀ hx₁ hxc₀ hxY₀ hcY₀ hbxc₀ hAC₀ hX₀ hkind₀ htyW
  refine ⟨E₀.map W.subtype, ?_⟩
  have h := Hering129KEb.typ129IIIcE_map_subtype W hE₀
  rw [hA₀map, hY₀map, hc₀, hx₀] at h
  exact h

end CFSG.RankThree.PartTwo.Sec12
