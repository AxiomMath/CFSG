module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442QFix
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442QShult

public section

namespace CFSG.Quasithin.Loc442Q

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431

universe u

section Quotient

variable {Mb : Type u} [Group Mb] {M : Type} [Group M] {M2 : Subgroup Mb} {t : Mb}

theorem not_isSolvable_quotient_of_sub {X V L : Subgroup Mb} (hLX : L ≤ X)
    [((Subgroup.centralizer (V : Set Mb)).subgroupOf X).Normal]
    (hLns : ¬ Group.IsSolvable ↥L)
    (hLV : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (V : Set Mb))) :
    ¬ Group.IsSolvable (↥X ⧸ (Subgroup.centralizer (V : Set Mb)).subgroupOf X) := by
  intro hX
  apply hLns
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (inf_le_left : L ⊓ Subgroup.centralizer (V : Set Mb) ≤ L))
    ((QuotientGroup.mk' ((Subgroup.centralizer (V : Set Mb)).subgroupOf X)).comp
      (Subgroup.inclusion hLX)) ?_
  intro x hx
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx
  exact ⟨⟨x.1, x.2, hx⟩, rfl⟩

end Quotient

section Main

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

theorem loc442Q (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hI : ∀ i ∈ I, i = z ∨ i = t) (ht : t ∈ I) (hzt : z * t = t * z)
    (cent_z : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2)
    (hSylt : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
      (Subgroup.centralizer ({t} : Set Mb)))
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnf : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t))
    {Vb : Subgroup Mb} (hVle : Vb ≤ Subgroup.centralizer ({t} : Set Mb))
    (hVn : ∀ x ∈ Subgroup.centralizer ({t} : Set Mb), ∀ v ∈ Vb, x * v * x⁻¹ ∈ Vb)
    (hVab : ∀ a ∈ Vb, ∀ b ∈ Vb, a * b = b * a) (hV2 : ∀ a ∈ Vb, a ^ 2 = 1) (hV1 : Vb ≠ ⊥)
    (hVz : ∀ v ∈ Vb, v ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t} : Set Mb), v = x * z * x⁻¹)
    [((Subgroup.centralizer (Vb : Set Mb)).subgroupOf (Subgroup.centralizer ({t} : Set Mb))).Normal]
    (hns : ¬ Group.IsSolvable (↥(Subgroup.centralizer ({t} : Set Mb)) ⧸
      (Subgroup.centralizer (Vb : Set Mb)).subgroupOf (Subgroup.centralizer ({t} : Set Mb)))) :
    Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) ≤ b2.range := by
  have hzT : z ∈ T := D.mem_T z D.z_mem
  have hz2 : z ∈ M2 := D.T_le₂ hzT
  have ht2 : t ∈ M2 := D.T_le₂ (D.mem_T t ht)
  have hVM2 : Vb ≤ M2 := hVle.trans cent_t
  set V : Subgroup M := (Vb.subgroupOf M2).map b2 with hV
  have hmemV : ∀ {y : M}, y ∈ V ↔ ∃ vb : M2, (vb : Mb) ∈ Vb ∧ b2 vb = y := Subgroup.mem_map
  have hXK : xt b2 t ≤ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) :=
    xt_le_centralizer C ht2
  have hVX : V ≤ xt b2 t := by
    intro y hy
    obtain ⟨vb, hvb, rfl⟩ := hmemV.1 hy
    exact mem_xt.2 ⟨vb, Subgroup.mem_centralizer_singleton_iff.1 (hVle hvb), rfl⟩
  have hVn' : ∀ x ∈ xt b2 t, ∀ v ∈ V, x * v * x⁻¹ ∈ V := by
    intro x hx v hv
    obtain ⟨xb, hxb, rfl⟩ := mem_xt.1 hx
    obtain ⟨vb, hvb, rfl⟩ := hmemV.1 hv
    refine hmemV.2 ⟨xb * vb * xb⁻¹, ?_, by simp⟩
    exact hVn _ (Subgroup.mem_centralizer_singleton_iff.2 hxb) _ hvb
  have hV1' : V ≠ ⊥ := by
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV1
    intro h
    have hmem : b2 ⟨v, hVM2 hv⟩ ∈ V := hmemV.2 ⟨⟨v, hVM2 hv⟩, hv, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : (⟨v, hVM2 hv⟩ : M2) = 1 := C.inj₂ (by rw [hmem, map_one])
    have h2 : v = 1 := congrArg (fun w : M2 => (w : Mb)) h1
    exact hv1 (Subtype.ext h2)
  have hVab' : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb'
    obtain ⟨va, hva, rfl⟩ := hmemV.1 ha
    obtain ⟨vb, hvb, rfl⟩ := hmemV.1 hb'
    rw [← map_mul, ← map_mul]
    exact congrArg b2 (Subtype.ext (hVab _ hva _ hvb))
  have hV2' : ∀ a ∈ V, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨va, hva, rfl⟩ := hmemV.1 ha
    rw [← map_pow, ← map_one b2]
    exact congrArg b2 (Subtype.ext (hV2 _ hva))
  have hfix : ∀ v ∈ V, v ≠ 1 → ∀ g ∈ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M),
      g⁻¹ * v * g ∈ xt b2 t → g ∈ xt b2 t := by
    intro v hv hv1 g hg hgX
    obtain ⟨vb, hvb, rfl⟩ := hmemV.1 hv
    have hne1 : (vb : Mb) ≠ 1 := fun h => hv1 (by rw [show vb = 1 from Subtype.ext h, map_one])
    obtain ⟨x, hx, hxz⟩ := hVz _ hvb hne1
    have hxM2 : x ∈ M2 := cent_t hx
    have hxX : b2 ⟨x, hxM2⟩ ∈ xt b2 t :=
      mem_xt.2 ⟨⟨x, hxM2⟩, Subgroup.mem_centralizer_singleton_iff.1 hx, rfl⟩
    have hvc : b2 vb = b2 ⟨x, hxM2⟩ * amalgamMap b1 b2 z * (b2 ⟨x, hxM2⟩)⁻¹ := by
      have h1 : vb = ⟨x, hxM2⟩ * ⟨z, hz2⟩ * ⟨x, hxM2⟩⁻¹ := Subtype.ext hxz
      rw [h1, map_mul, map_mul, map_inv, amalgamMap_of_mem₂ b1 b2 C.agree hz2]
    have hg' : (b2 ⟨x, hxM2⟩)⁻¹ * g ∈ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hXK hxX)) hg
    have hu' : ((b2 ⟨x, hxM2⟩)⁻¹ * g)⁻¹ * amalgamMap b1 b2 z * ((b2 ⟨x, hxM2⟩)⁻¹ * g) ∈
        xt b2 t := by
      have : ((b2 ⟨x, hxM2⟩)⁻¹ * g)⁻¹ * amalgamMap b1 b2 z * ((b2 ⟨x, hxM2⟩)⁻¹ * g) =
          g⁻¹ * (b2 ⟨x, hxM2⟩ * amalgamMap b1 b2 z * (b2 ⟨x, hxM2⟩)⁻¹) * g := by group
      rw [this, ← hvc]
      exact hgX
    have h2 := (xt b2 t).mul_mem hxX
      (loc442Q_unique_fixed D C hI ht hzt cent_z cent_t hSylt hb hnf
        (Subgroup.mem_centralizer_singleton_iff.mp hg') hu')
    simpa using h2
  have hNormX : ((Subgroup.centralizer (V : Set M)).subgroupOf (xt b2 t)).Normal :=
    centralizer_subgroupOf_normal hVn'
  have hns' : ¬ Group.IsSolvable (↥(xt b2 t) ⧸
      (Subgroup.centralizer (V : Set M)).subgroupOf (xt b2 t)) := by
    intro hsolv
    let ε : ↥(Subgroup.centralizer ({t} : Set Mb)) →* ↥(xt b2 t) :=
      (b2.comp (Subgroup.inclusion cent_t)).codRestrict (xt b2 t) (fun x =>
        mem_xt.2 ⟨Subgroup.inclusion cent_t x, Subgroup.mem_centralizer_singleton_iff.1 x.2, rfl⟩)
    have hε : ∀ x, ((ε x : ↥(xt b2 t)) : M) = b2 (Subgroup.inclusion cent_t x) := fun x => rfl
    have hle : (Subgroup.centralizer (Vb : Set Mb)).subgroupOf (Subgroup.centralizer ({t} : Set Mb))
        ≤ ((Subgroup.centralizer (V : Set M)).subgroupOf (xt b2 t)).comap ε := by
      intro n hn
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨vb, hvb, rfl⟩ := hmemV.1 hv
      have hnc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hn) _ hvb
      rw [hε, ← map_mul, ← map_mul]
      exact congrArg b2 (Subtype.ext hnc)
    have hinj : Function.Injective (QuotientGroup.map _ _ ε hle) := by
      rw [injective_iff_map_eq_one]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
          Subgroup.mem_centralizer_iff] at hq
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
        intro w hw
        have := hq (b2 ⟨w, hVM2 hw⟩) (hmemV.2 ⟨⟨w, hVM2 hw⟩, hw, rfl⟩)
        rw [hε, ← map_mul, ← map_mul] at this
        exact congrArg Subtype.val (C.inj₂ this)
    exact hns (Group.isSolvable_of_isSolvable_injective hinj)
  have hKX := shult_finish hXK hVX hVn' hV1' hVab' hV2' hfix hns'
  intro y hy
  obtain ⟨x, -, rfl⟩ := mem_xt.mp (hKX hy)
  exact ⟨x, rfl⟩

theorem loc442Q_of_sub (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hI : ∀ i ∈ I, i = z ∨ i = t) (ht : t ∈ I) (hzt : z * t = t * z)
    (cent_z : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2)
    (hSylt : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
      (Subgroup.centralizer ({t} : Set Mb)))
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnf : ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 t))
    {Vb : Subgroup Mb} (hVle : Vb ≤ Subgroup.centralizer ({t} : Set Mb))
    (hVn : ∀ x ∈ Subgroup.centralizer ({t} : Set Mb), ∀ v ∈ Vb, x * v * x⁻¹ ∈ Vb)
    (hVab : ∀ a ∈ Vb, ∀ b ∈ Vb, a * b = b * a) (hV2 : ∀ a ∈ Vb, a ^ 2 = 1) (hV1 : Vb ≠ ⊥)
    (hVz : ∀ v ∈ Vb, v ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t} : Set Mb), v = x * z * x⁻¹)
    {L : Subgroup Mb} (hLle : L ≤ Subgroup.centralizer ({t} : Set Mb))
    (hLns : ¬ Group.IsSolvable ↥L)
    (hLV : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (Vb : Set Mb))) :
    Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) ≤ b2.range := by
  have hN : ((Subgroup.centralizer (Vb : Set Mb)).subgroupOf
      (Subgroup.centralizer ({t} : Set Mb))).Normal := centralizer_subgroupOf_normal hVn
  exact loc442Q D C hI ht hzt cent_z cent_t hSylt hb hnf hVle hVn hVab hV2 hV1 hVz
    (not_isSolvable_quotient_of_sub hLle hLns hLV)

theorem loc442Q_of_sub_hnfI (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hI : ∀ i ∈ I, i = z ∨ i = t) (ht : t ∈ I) (hzt : z * t = t * z)
    (cent_z : Subgroup.centralizer ({z} : Set Mb) ≤ M1)
    (cent_t : Subgroup.centralizer ({t} : Set Mb) ≤ M2)
    (hSylt : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
      (Subgroup.centralizer ({t} : Set Mb)))
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    (hnfI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    {Vb : Subgroup Mb} (hVle : Vb ≤ Subgroup.centralizer ({t} : Set Mb))
    (hVn : ∀ x ∈ Subgroup.centralizer ({t} : Set Mb), ∀ v ∈ Vb, x * v * x⁻¹ ∈ Vb)
    (hVab : ∀ a ∈ Vb, ∀ b ∈ Vb, a * b = b * a) (hV2 : ∀ a ∈ Vb, a ^ 2 = 1) (hV1 : Vb ≠ ⊥)
    (hVz : ∀ v ∈ Vb, v ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t} : Set Mb), v = x * z * x⁻¹)
    {L : Subgroup Mb} (hLle : L ≤ Subgroup.centralizer ({t} : Set Mb))
    (hLns : ¬ Group.IsSolvable ↥L)
    (hLV : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (Vb : Set Mb))) :
    Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) ≤ b2.range :=
  loc442Q_of_sub D C hI ht hzt cent_z cent_t hSylt hb (hnf_of_hnfI D hI ht hnfI) hVle hVn hVab
    hV2 hV1 hVz hLle hLns hLV

end Main

end CFSG.Quasithin.Loc442Q
