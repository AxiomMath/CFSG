module

public import CFSG.RankThree.GF2n.Stroth80.Sec108CentT
public import CFSG.RankThree.GF2n.Tim79aCitedAS
public import CFSG.Alternating.Multipliers.OddKernel

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec108

open CFSG CFSG.Open CFSG.Blueprint
open scoped commutatorElement

@[expose] def Sec108OddCoverStatement : Prop :=
  ∀ (E S : Type) [Group E] [Finite E] [Group.IsPerfect E] [Group S] (π : E →* S),
    Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      NativeSporadic.IsSporadic S .M12 ∨ NativeSporadic.IsSporadic S .J2 → π.ker = ⊥

section Abstract

variable {𝔊 : Type} [Group 𝔊] [Finite 𝔊] {K : Type} [Field K] [Finite K] [CharP K 2]
  {X Yh Nf : Subgroup 𝔊}

theorem LeviStd.oddCore_le_centralizer_normalClosure (hS : LeviStd K X Yh Nf) :
    standardComponentOddCore 𝔊 ≤
      Subgroup.centralizer (Subgroup.normalClosure (X : Set 𝔊) : Set 𝔊) := by
  rw [Subgroup.le_centralizer_iff]
  exact Subgroup.normalClosure_le_normal (Subgroup.le_centralizer_iff.mp hS.oddCore_le_centralizer)

theorem LeviStd.isPerfect_normalClosure (hS : LeviStd K X Yh Nf) :
    Group.IsPerfect (Subgroup.normalClosure (X : Set 𝔊)) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
  have hXW : ⁅X, X⁆ ≤ ⁅Subgroup.normalClosure (X : Set 𝔊),
      Subgroup.normalClosure (X : Set 𝔊)⁆ :=
    Subgroup.commutator_mono Subgroup.subset_normalClosure Subgroup.subset_normalClosure
  rw [hS.commutator_eq] at hXW
  exact Subgroup.normalClosure_le_normal hXW

theorem LeviStd.map_normalClosure (hS : LeviStd K X Yh Nf) :
    oddBar (Subgroup.normalClosure (X : Set 𝔊)) =
      Subgroup.normalClosure (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)) := by
  rw [oddBar, Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
  rfl

private theorem surjective_mk'_subgroupOf_sup {G : Type*} [Group G] {X O : Subgroup G}
    [(X.subgroupOf (X ⊔ O)).Normal] (hOX : O ≤ Subgroup.normalizer (X : Set G))
    (hOn : O.Normal) :
    Function.Surjective fun o : O =>
      QuotientGroup.mk' (X.subgroupOf (X ⊔ O)) (Subgroup.inclusion le_sup_right o) := by
  classical
  set Q : Subgroup G := X ⊔ O
  have hXQ : X ≤ Q := le_sup_left
  have hOQ : O ≤ Q := le_sup_right
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (X.subgroupOf Q) q
  obtain ⟨y, hy, z, hz, hxz⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := X) (t := O) (x := (x : G))).mp x.2
  refine ⟨⟨z, hz⟩, ?_⟩
  have hxz' : (⟨y * z, Subgroup.mul_mem_sup hy hz⟩ : Q) = x := Subtype.ext hxz
  rw [← hxz']
  have hQN : Q ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hOX
  show (QuotientGroup.mk' (X.subgroupOf Q)) (⟨z, hOQ hz⟩ : Q) =
    (QuotientGroup.mk' (X.subgroupOf Q)) (⟨y * z, Subgroup.mul_mem_sup hy hz⟩ : Q)
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨⟨z⁻¹ * y * z, ?_⟩, ?_, ?_⟩
  · exact Q.mul_mem (Q.mul_mem (Q.inv_mem (hOQ hz)) (hXQ hy)) (hOQ hz)
  · rw [Subgroup.mem_subgroupOf]
    simpa using Subgroup.le_normalizer_iff.mp hQN z⁻¹ (Q.inv_mem (hOQ hz)) y hy
  · apply Subtype.ext
    show z * (z⁻¹ * y * z) = y * z
    group

private theorem eq_one_mk'_subgroupOf_sup {G : Type*} [Group G] {X O : Subgroup G}
    [(X.subgroupOf (X ⊔ O)).Normal] (hXO : X ⊓ O = ⊥) (o : O) :
    QuotientGroup.mk' (X.subgroupOf (X ⊔ O)) (Subgroup.inclusion le_sup_right o) = 1 ↔
      o = 1 := by
  constructor
  · intro h
    have hmem : ((Subgroup.inclusion le_sup_right o : (X ⊔ O : Subgroup G)) : G) ∈ X :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
    have hmem' : (o : G) ∈ X ⊓ O :=
      Subgroup.mem_inf.mpr ⟨by simpa using hmem, o.2⟩
    rw [hXO] at hmem'
    exact Subtype.ext (Subgroup.mem_bot.mp hmem')
  · intro h
    subst h
    simp

private theorem card_quotient_subgroupOf_sup_eq {G : Type*} [Group G] [Finite G]
    {X O : Subgroup G} (hOX : O ≤ Subgroup.normalizer (X : Set G)) (hXO : X ⊓ O = ⊥)
    (hOn : O.Normal) :
    Nat.card ((X ⊔ O : Subgroup G) ⧸ X.subgroupOf (X ⊔ O)) = Nat.card O := by
  classical
  haveI := hOn
  set Q : Subgroup G := X ⊔ O
  have hOQ : O ≤ Q := le_sup_right
  have hQN : Q ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hOX
  haveI : (X.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQN
  let σ : O →* (Q ⧸ X.subgroupOf Q) :=
    (QuotientGroup.mk' (X.subgroupOf Q)).comp (Subgroup.inclusion hOQ)
  have hσker : σ.ker = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact (eq_one_mk'_subgroupOf_sup hXO x).mp (MonoidHom.mem_ker.mp hx)
  have hσtop : σ.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (surjective_mk'_subgroupOf_sup hOX hOn)
  have h := Subgroup.card_ker_mul_card_range σ
  rw [hσker, hσtop, Subgroup.card_bot, Subgroup.card_top] at h
  simpa using h

private theorem card_dvd_of_le_sup_of_inf_eq_bot {G : Type*} [Group G] [Finite G]
    {X O C : Subgroup G} (hOX : O ≤ Subgroup.normalizer (X : Set G)) (hCX : C ≤ X ⊔ O)
    (hXO : X ⊓ O = ⊥) (hOn : O.Normal) (hCbot : C ⊓ X = ⊥) : Nat.card C ∣ Nat.card O := by
  classical
  haveI := hOn
  set Q : Subgroup G := X ⊔ O
  have hQN : Q ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hOX
  haveI : (X.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQN
  let ψ : C →* (Q ⧸ X.subgroupOf Q) :=
    (QuotientGroup.mk' (X.subgroupOf Q)).comp (Subgroup.inclusion hCX)
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine le_antisymm ?_ bot_le
    intro c hc
    rw [Subgroup.mem_bot]
    have hc1 : ψ c = 1 := MonoidHom.mem_ker.mp hc
    have hc1' : ((Subgroup.inclusion hCX c : Q) : Q ⧸ X.subgroupOf Q) = 1 := by
      simpa [ψ] using hc1
    have hmem : ((Subgroup.inclusion hCX c : Q) : G) ∈ X :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hc1')
    have hmem' : (c : G) ∈ C ⊓ X :=
      Subgroup.mem_inf.mpr ⟨c.2, by simpa using hmem⟩
    rw [hCbot] at hmem'
    exact Subtype.ext (Subgroup.mem_bot.mp hmem')
  calc Nat.card C ∣ Nat.card (Q ⧸ X.subgroupOf Q) :=
        Subgroup.card_dvd_of_injective ψ hψinj
    _ = Nat.card O := card_quotient_subgroupOf_sup_eq hOX hXO hOn

private theorem le_of_le_sup_of_isSimpleGroup_of_odd {G : Type*} [Group G] [Finite G]
    {X O C : Subgroup G} (hOX : O ≤ Subgroup.normalizer (X : Set G))
    (hCX : C ≤ X ⊔ O) (hCs : IsSimpleGroup C) (hCeven : Even (Nat.card C))
    (hXO : X ⊓ O = ⊥) (hOodd : Odd (Nat.card O)) (hOn : O.Normal) : C ≤ X := by
  classical
  haveI := hOn
  have hCXn : C ≤ Subgroup.normalizer (X : Set G) :=
    hCX.trans (sup_le Subgroup.le_normalizer hOX)
  have hNX : ((C ⊓ X).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (inf_le_left : C ⊓ X ≤ C)]
    intro h k hh hk
    obtain ⟨hhC, hhX⟩ := Subgroup.mem_inf.mp hh
    exact Subgroup.mem_inf.mpr ⟨C.mul_mem (C.mul_mem hk hhC) (C.inv_mem hk),
      (Subgroup.mem_normalizer_iff.mp (hCXn hk) h).mp hhX⟩
  rcases (Subgroup.isSimpleGroup_iff.mp hCs).2 (C ⊓ X) inf_le_left hNX with hbot | htop
  · exfalso
    have hdvd : Nat.card C ∣ Nat.card O :=
      card_dvd_of_le_sup_of_inf_eq_bot hOX hCX hXO hOn hbot
    exact (Nat.not_even_iff_odd.mpr (hOodd.of_dvd_nat hdvd)) hCeven
  · intro c hc
    exact (Subgroup.mem_inf.mp (htop.symm ▸ hc)).2

private theorem normal_of_normalClosure_oddBar {𝔊 : Type} [Group 𝔊] [Finite 𝔊]
    {K : Type} [Field K] [Finite K] [CharP K 2] {X Yh Nf : Subgroup 𝔊}
    (hS : LeviStd K X Yh Nf)
    (hleft : Subgroup.normalClosure (oddBar X) = oddBar X) : X.Normal := by
  classical
  haveI hXsimple : IsSimpleGroup X := hS.isSimpleGroup
  have hmap : oddBar (Subgroup.normalClosure (X : Set 𝔊)) =
      Subgroup.normalClosure (oddBar X) := LeviStd.map_normalClosure hS
  have hWn : (Subgroup.normalClosure (X : Set 𝔊)).Normal := Subgroup.normalClosure_normal
  have hconj_le : ∀ g : 𝔊, X.map (MulAut.conj g).toMonoidHom ≤ X := by
    intro g
    refine le_of_le_sup_of_isSimpleGroup_of_odd (X := X)
      (O := standardComponentOddCore 𝔊) (C := X.map (MulAut.conj g).toMonoidHom) ?_ ?_ ?_ ?_
      hS.inf_oddCore ?_ ?_
    · exact hS.oddCore_le_centralizer.trans (Subgroup.centralizer_le_normalizer (X : Set 𝔊))
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have hxW : g * x * g⁻¹ ∈ Subgroup.normalClosure (X : Set 𝔊) :=
        hWn.conj_mem x (Subgroup.subset_normalClosure hx) g
      have hbar : QuotientGroup.mk' _ (g * x * g⁻¹) ∈ oddBar X := by
        have h1 : QuotientGroup.mk' _ (g * x * g⁻¹) ∈
            oddBar (Subgroup.normalClosure (X : Set 𝔊)) :=
          Subgroup.mem_map_of_mem _ hxW
        rwa [hmap, hleft] at h1
      obtain ⟨x', hx', hx'eq⟩ := Subgroup.mem_map.mp hbar
      have ho : (g * x * g⁻¹) * x'⁻¹ ∈ standardComponentOddCore 𝔊 := by
        rw [← QuotientGroup.eq_one_iff]
        change (QuotientGroup.mk' _) ((g * x * g⁻¹) * x'⁻¹) = 1
        rw [map_mul, map_inv, ← hx'eq, mul_inv_cancel]
      have h2 : (g * x * g⁻¹) ∈ standardComponentOddCore 𝔊 ⊔ X := by
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using
          (Subgroup.mul_mem_sup ho hx' :
            (g * x * g⁻¹) * x'⁻¹ * x' ∈ standardComponentOddCore 𝔊 ⊔ X)
      rwa [sup_comm] at h2
    · exact (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm.isSimpleGroup
    · have hcard : Nat.card (X.map (MulAut.conj g).toMonoidHom) = Nat.card X :=
        (Nat.card_congr (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).toEquiv).symm
      rw [hcard]
      exact hS.even_card
    · exact CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore'
    · exact CFSG.ComponentClassification.GMS78.u3_standardComponentOddCore_normal 𝔊
  exact ⟨fun x hx g => by
    simpa [MulAut.conj_apply] using
      hconj_le g (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)⟩

private theorem exists_mem_normalClosure_mk' {𝔊 : Type} [Group 𝔊] [Finite 𝔊]
    {K : Type} [Field K] [Finite K] [CharP K 2] {X Yh Nf : Subgroup 𝔊}
    (hS : LeviStd K X Yh Nf) {y : 𝔊 ⧸ standardComponentOddCore 𝔊}
    (hy : y ∈ Subgroup.normalClosure (oddBar X)) :
    ∃ w : Subgroup.normalClosure (X : Set 𝔊),
      QuotientGroup.mk' (standardComponentOddCore 𝔊) (w : 𝔊) = y := by
  classical
  set W : Subgroup 𝔊 := Subgroup.normalClosure (X : Set 𝔊)
  have hmap : oddBar W = Subgroup.normalClosure (oddBar X) := LeviStd.map_normalClosure hS
  have hWn : W.Normal := Subgroup.normalClosure_normal
  have hWbar_le : Subgroup.normalClosure (oddBar X) ≤
      W.map (QuotientGroup.mk' (standardComponentOddCore 𝔊)) := by
    haveI : (W.map (QuotientGroup.mk' (standardComponentOddCore 𝔊))).Normal :=
      hWn.map _ (QuotientGroup.mk'_surjective _)
    refine Subgroup.normalClosure_le_normal ?_
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (standardComponentOddCore 𝔊))
      (Subgroup.subset_normalClosure hx)
  obtain ⟨w, hw, hw'⟩ := Subgroup.mem_map.mp (hWbar_le hy)
  exact ⟨⟨w, hw⟩, hw'⟩

private theorem exists_restricted_projection {𝔊 : Type} [Group 𝔊] [Finite 𝔊]
    {K : Type} [Field K] [Finite K] [CharP K 2] {X Yh Nf : Subgroup 𝔊}
    (hS : LeviStd K X Yh Nf) :
    ∃ π : Subgroup.normalClosure (X : Set 𝔊) →*
        Subgroup.normalClosure (oddBar X : Set (𝔊 ⧸ standardComponentOddCore 𝔊)),
      Function.Surjective π ∧
        π.ker ≤ Subgroup.center (Subgroup.normalClosure (X : Set 𝔊)) ∧
          Odd (Nat.card π.ker) := by
  classical
  set W : Subgroup 𝔊 := Subgroup.normalClosure (X : Set 𝔊)
  set Wbar : Subgroup (𝔊 ⧸ standardComponentOddCore 𝔊) := Subgroup.normalClosure (oddBar X)
  have hOcent : standardComponentOddCore 𝔊 ≤ Subgroup.centralizer (W : Set 𝔊) :=
    LeviStd.oddCore_le_centralizer_normalClosure hS
  have hmap : oddBar W = Wbar := LeviStd.map_normalClosure hS
  have hWn : W.Normal := Subgroup.normalClosure_normal
  let π : W →* Wbar :=
    ((QuotientGroup.mk' (standardComponentOddCore 𝔊)).comp W.subtype).codRestrict Wbar
      fun w => by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (standardComponentOddCore 𝔊)) w.2
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨w, hw⟩ := exists_mem_normalClosure_mk' hS y.2
    exact ⟨w, Subtype.ext (by simpa [π] using hw)⟩
  have hkerO : ∀ k ∈ π.ker, (k : 𝔊) ∈ standardComponentOddCore 𝔊 := by
    intro k hk
    have hk1 : π k = 1 := MonoidHom.mem_ker.mp hk
    have hk1' : (QuotientGroup.mk' (standardComponentOddCore 𝔊)) (k : 𝔊) = 1 := by
      simpa [π] using congrArg Subtype.val hk1
    exact (QuotientGroup.eq_one_iff (k : 𝔊)).mp hk1'
  have hcenter : π.ker ≤ Subgroup.center W := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext
      ((Subgroup.mem_centralizer_iff.mp (hOcent (hkerO k hk))) (w : 𝔊) w.2)
  have hodd : Odd (Nat.card π.ker) := by
    have hle : π.ker.map W.subtype ≤ standardComponentOddCore 𝔊 := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      exact hkerO k hk
    have hcard : Nat.card π.ker = Nat.card (π.ker.map W.subtype) :=
      (Subgroup.card_map_of_injective W.subtype_injective).symm
    rw [hcard]
    exact CFSG.ComponentClassification.GMS78.odd_card_standardComponentOddCore'.of_dvd_nat
      (Subgroup.card_dvd_of_le hle)
  exact ⟨π, hπsurj, hcenter, hodd⟩

theorem LeviStd.normal_or (hS : LeviStd K X Yh Nf) (hAS : Tim79a.AschbacherSeitzStatement)
    (hcov : Sec108OddCoverStatement) :
    X.Normal ∨ (Nat.card K = 4 ∧
      (Nonempty (Subgroup.normalClosure (X : Set 𝔊) ≃* alternatingGroup (Fin 9)) ∨
        NativeSporadic.IsSporadic (Subgroup.normalClosure (X : Set 𝔊)) .M12 ∨
        NativeSporadic.IsSporadic (Subgroup.normalClosure (X : Set 𝔊)) .J2)) := by
  classical
  haveI hperfect : Group.IsPerfect (Subgroup.normalClosure (X : Set 𝔊)) :=
    LeviStd.isPerfect_normalClosure hS
  obtain ⟨f, hf2, hcardK, hSp, hOquot, hstd, hrank⟩ := hS.std_hyps
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at hrank
  have hres := hAS (𝔊 ⧸ standardComponentOddCore 𝔊) (oddBar X) 1 f le_rfl hf2 hSp hOquot hstd
    hrank
  rcases hres with hleft | ⟨-, hf2eq, hright⟩
  · exact Or.inl (normal_of_normalClosure_oddBar hS hleft)
  · refine Or.inr ⟨?_, ?_⟩
    · rw [hcardK, hf2eq]
      norm_num
    · obtain ⟨π, hπsurj, hπcenter, hπodd⟩ := exists_restricted_projection hS
      rcases hright with hA9 | hright
      · obtain ⟨e⟩ := hA9
        have hηker : (e.toMonoidHom.comp π).ker = π.ker :=
          MonoidHom.ker_mulEquiv_comp π e
        have h1 : Nat.card (e.toMonoidHom.comp π).ker = 1 :=
          CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 7) (by norm_num) _
            (e.surjective.comp hπsurj) (by rw [hηker]; exact hπcenter)
            (by rw [hηker]; exact hπodd)
        have hk : π.ker = ⊥ := Subgroup.card_eq_one.mp (by rw [← hηker]; exact h1)
        exact Or.inl ⟨(MulEquiv.ofBijective π
          ⟨(MonoidHom.ker_eq_bot_iff π).mp hk, hπsurj⟩).trans e⟩
      · have hk : π.ker = ⊥ := hcov _ _ π hπsurj hπcenter hπodd hright
        rcases hright with h12 | h2
        · exact Or.inr (Or.inl ⟨(MulEquiv.ofBijective π
            ⟨(MonoidHom.ker_eq_bot_iff π).mp hk, hπsurj⟩).trans h12.some⟩)
        · exact Or.inr (Or.inr ⟨(MulEquiv.ofBijective π
            ⟨(MonoidHom.ker_eq_bot_iff π).mp hk, hπsurj⟩).trans h2.some⟩)

end Abstract

section Config

variable {𝓜 : Type} [Group 𝓜] [Finite 𝓜] {K : Type} [Field K] [Finite K] [CharP K 2]
  {L R N Y : Subgroup 𝓜} {ρ : ↥R →* GL (Fin 3) K} {μ : ↥N →* Multiplicative (Fin 3 → K)}
  {T : ↥(NLY L Y) →* AddMonoid.End (Fin 3 → K)}

theorem Levi108.normal_or (hC : Levi108 K L R N Y ρ μ T)
    (hAS : Tim79a.AschbacherSeitzStatement) (hcov : Sec108OddCoverStatement) :
    (Xlevi L R).Normal ∨ (Nat.card K = 4 ∧
      (Nonempty (Subgroup.normalClosure (Xlevi L R : Set (GG L)) ≃* alternatingGroup (Fin 9)) ∨
        NativeSporadic.IsSporadic (Subgroup.normalClosure (Xlevi L R : Set (GG L))) .M12 ∨
        NativeSporadic.IsSporadic (Subgroup.normalClosure (Xlevi L R : Set (GG L))) .J2)) :=
  hC.leviStd.normal_or hAS hcov

end Config

end CFSG.RankThree.GF2n.Stroth80.Sec108
