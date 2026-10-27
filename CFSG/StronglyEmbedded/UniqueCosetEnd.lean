module

public import CFSG.GH74.Uniqueness.Section165GapFinal
public import CFSG.StronglyEmbedded.UniqueCosetZD

public section

namespace CFSG.StronglyEmbedded.UniqueCoset

open CFSG.GH74.Uniqueness CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem isSolvable_normalizer_sylow {X : Type*} [Group X] [Finite X] (S : Sylow 2 X) :
    Group.IsSolvable ↥(Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
  set N := Subgroup.normalizer ((S : Subgroup X) : Set X) with hN
  have hSN : (S : Subgroup X) ≤ N := Subgroup.le_normalizer
  have hTn : ((S : Subgroup X).subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hS : Group.IsSolvable ↥(S : Subgroup X) := by
    have := S.isPGroup'.isNilpotent
    infer_instance
  have hT : Group.IsSolvable ↥((S : Subgroup X).subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hSN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSN).injective
  have hodd : Odd (Nat.card (↥N ⧸ (S : Subgroup X).subgroupOf N)) := by
    change Odd ((S : Subgroup X).relIndex N)
    refine Nat.not_even_iff_odd.1 fun he => S.not_dvd_index ?_
    exact dvd_trans (even_iff_two_dvd.1 he) (Subgroup.relIndex_dvd_index_of_le hSN)
  have hQ : Group.IsSolvable (↥N ⧸ (S : Subgroup X).subgroupOf N) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range ((S : Subgroup X).subgroupOf N).subtype
    (QuotientGroup.mk' ((S : Subgroup X).subgroupOf N))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_outer_of_isBenderGroup {K : Type} [Group K]
    (h : BenderSuzuki.IsBenderGroup K) : Group.IsSolvable (Outer K) := by
  obtain ⟨n, i, e, hT⟩ := Bender.isBenderGroup_iff_exists_benderType.mp h
  rcases hT.cases' with ⟨hi, he, -⟩ | ⟨hi, -, -⟩ | ⟨hi, -, -⟩
  · subst hi
    subst he
    have : IsCyclic (Outer K) := hT.outer_linear.1
    infer_instance
  · subst hi
    have : IsCyclic (Outer K) := hT.outer_suzuki.1
    infer_instance
  · subst hi
    obtain ⟨Dd, hn, hc, -, hq, -⟩ := hT.outer_unitary
    exact Group.isSolvable_of_ker_le_range Dd.subtype (QuotientGroup.mk' Dd)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

variable {G : Type} [Group G]

theorem mem_of_conjNormal_mem_inner {F : Subgroup G} [F.Normal]
    (hFc : Subgroup.centralizer (F : Set G) = ⊥) {g : G}
    (hg : MulAut.conjNormal g ∈ inner ↥F) : g ∈ F := by
  obtain ⟨f, hf⟩ := hg
  have hcen : (f : G)⁻¹ * g ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hfx : (f : G) * x * (f : G)⁻¹ = g * x * g⁻¹ := by
      have := congrArg (fun φ : MulAut ↥F => ((φ ⟨x, hx⟩ : ↥F) : G)) hf
      simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using this
    calc x * ((f : G)⁻¹ * g) = (f : G)⁻¹ * ((f : G) * x * (f : G)⁻¹) * g := by group
      _ = (f : G)⁻¹ * (g * x * g⁻¹) * g := by rw [hfx]
      _ = (f : G)⁻¹ * g * x := by group
  rw [hFc, Subgroup.mem_bot] at hcen
  have hgf : g = f := by
    calc g = (f : G) * ((f : G)⁻¹ * g) := by group
      _ = f := by rw [hcen, mul_one]
  rw [hgf]
  exact f.2

theorem conj_mem_of_mem_centralizer {H : Subgroup G} {z a : G}
    (h1 : ∃! c : G ⧸ H, z • c = c) (ha : z • (a : G ⧸ H) = a) {c : G}
    (hc : c ∈ Subgroup.centralizer ({z} : Set G)) : a⁻¹ * c * a ∈ H := by
  rw [← smul_coe_eq_iff]
  have hzc : z • (c • (a : G ⧸ H)) = c • (a : G ⧸ H) := by
    rw [smul_smul, ← Subgroup.mem_centralizer_singleton_iff.1 hc, mul_smul, ha]
  exact h1.unique hzc ha

section EndGame

variable [Finite G] {H : Subgroup G} {z : G}

theorem exists_sylow_eq_normalizer_of_ZDConclusion (hz : orderOf z = 2) {F : Subgroup G}
    [hFn : F.Normal] (hFs : IsSimpleGroup ↥F) (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x)
    (hFc : Subgroup.centralizer (F : Set G) = ⊥) {L : Subgroup G}
    (hL : Subgroup.closure (conjugatesOf z) = L) {M : Subgroup ↥L}
    (hZD : ZDConclusion ↥L {l | (l : G) ∈ conjugatesOf z} M) :
    ∃ S : Sylow 2 ↥L, M = Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L) := by
  obtain ⟨hLF, -, -⟩ := closure_conjugatesOf_eq_and_isBenderGroup hz hFs hFnab hFc hL hZD
  have hLn : L.Normal := hLF ▸ hFn
  have hLs : IsSimpleGroup ↥L := hLF ▸ hFs
  have hLc : Subgroup.centralizer (L : Set G) = ⊥ := hLF ▸ hFc
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨x, hx, y, hy, h⟩ := hFnab
    exact ⟨⟨x, hLF ▸ hx⟩, ⟨y, hLF ▸ hy⟩, fun e => h (congrArg Subtype.val e)⟩
  have heven : Even (Nat.card ↥L) := CFSG.GH74.even_card_of_nonabelian_simple hnab
  have hO : pPrimeCore 2 ↥L = ⊥ := pPrimeCore_eq_bot hLs hLc heven le_rfl
  have hD : commutator ↥L = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (commutator ↥L) with hb | ht
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator ↥L :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact ht
  rcases hZD with hrank | ⟨-, -, -, -, -, -, -, -, -, hBorel, -⟩
  · exfalso
    have h2 : 2 ≤ CFSG.Assembly.twoRank ↥L :=
      CFSG.Milestones.lr_nonabelian_simple_two_rank_lower_bound ↥L hnab heven
    have h4 : CFSG.Assembly.twoRank ↥L = CFSG.Open.twoRank ↥L := rfl
    omega
  obtain ⟨e, he⟩ := exists_mulEquiv_derivedBar ↥L hD hO
  obtain ⟨S', hS'⟩ := hBorel
  have hsurj : Function.Surjective (e.symm.toMonoidHom : derivedBar ↥L →* ↥L) :=
    e.symm.surjective
  have hbij : Function.Bijective (e.symm.toMonoidHom : derivedBar ↥L →* ↥L) :=
    e.symm.bijective
  refine ⟨Sylow.mapSurjective hsurj S', ?_⟩
  have hcoe : ((Sylow.mapSurjective hsurj S' : Sylow 2 ↥L) : Subgroup ↥L) =
      (S' : Subgroup (derivedBar ↥L)).map e.symm.toMonoidHom := rfl
  change M = Subgroup.normalizer
    (((Sylow.mapSurjective hsurj S' : Sylow 2 ↥L) : Subgroup ↥L) : Set ↥L)
  rw [hcoe, ← Subgroup.map_normalizer_eq_of_bijective _ hbij, ← hS', he]
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨y, ⟨w, hw, rfl⟩, hwx⟩
    have hxw : x = w := by simpa using hwx.symm
    rw [hxw]
    exact hw

theorem isSolvable_centralizer_of_ZDConclusion (hz : orderOf z = 2)
    (h1 : ∃! c : G ⧸ H, z • c = c) {F : Subgroup G} [hFn : F.Normal]
    (hFs : IsSimpleGroup ↥F) (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x)
    (hFc : Subgroup.centralizer (F : Set G) = ⊥) {L : Subgroup G}
    (hL : Subgroup.closure (conjugatesOf z) = L)
    (hZD : ZDConclusion ↥L {l | (l : G) ∈ conjugatesOf z} (H.comap L.subtype)) :
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨hLF, hLB, -⟩ := closure_conjugatesOf_eq_and_isBenderGroup hz hFs hFnab hFc hL hZD
  obtain ⟨S, hS⟩ := exists_sylow_eq_normalizer_of_ZDConclusion hz hFs hFnab hFc hL hZD
  have hLn : L.Normal := hLF ▸ hFn
  have hB : Group.IsSolvable ↥(H.subgroupOf L) := by
    rw [show H.subgroupOf L = _ from hS]
    exact isSolvable_normalizer_sylow S
  have hHL : Group.IsSolvable ↥(H ⊓ L) := by
    have := Group.isSolvable_of_surjective
      (f := ((H.subgroupOf L).equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom)
      ((H.subgroupOf L).equivMapOfInjective L.subtype L.subtype_injective).surjective
    rwa [Subgroup.subgroupOf_map_subtype] at this
  obtain ⟨c₀, hc₀⟩ := h1.exists
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c₀
  have hCL : Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G) ⊓ L) := by
    have hmaps : ∀ x : ↥(Subgroup.centralizer ({z} : Set G) ⊓ L),
        ((MulAut.conj a⁻¹).toMonoidHom.comp
          (Subgroup.centralizer ({z} : Set G) ⊓ L).subtype) x ∈ H ⊓ L := by
      intro x
      obtain ⟨hxC, hxL⟩ := Subgroup.mem_inf.1 x.2
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · simpa [MulAut.conj_apply] using conj_mem_of_mem_centralizer h1 hc₀ hxC
      · simpa [MulAut.conj_apply] using hLn.conj_mem _ hxL a⁻¹
    refine Group.isSolvable_of_isSolvable_injective
      (f := ((MulAut.conj a⁻¹).toMonoidHom.comp
        (Subgroup.centralizer ({z} : Set G) ⊓ L).subtype).codRestrict (H ⊓ L) hmaps) ?_
    intro x y hxy
    apply Subtype.ext
    exact (MulAut.conj a⁻¹).injective (congrArg Subtype.val hxy)
  have hOut : Group.IsSolvable (Outer ↥F) := isSolvable_outer_of_isBenderGroup (hLF ▸ hLB)
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (inf_le_left : Subgroup.centralizer ({z} : Set G) ⊓ L ≤ _))
    (((QuotientGroup.mk' (inner ↥F)).comp MulAut.conjNormal).comp
      (Subgroup.centralizer ({z} : Set G)).subtype) ?_
  intro c hc
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hc
  have hcL : (c : G) ∈ L := hLF ▸ mem_of_conjNormal_mem_inner hFc hc
  exact ⟨⟨c, Subgroup.mem_inf.2 ⟨c.2, hcL⟩⟩, rfl⟩

theorem isSolvable_centralizer_of_uniqueCoset (hH : H ≠ ⊤) (hz : orderOf z = 2)
    (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    {F : Subgroup G} [F.Normal] (hFs : IsSimpleGroup ↥F)
    (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) (hFc : Subgroup.centralizer (F : Set G) = ⊥) :
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) :=
  isSolvable_centralizer_of_ZDConclusion hz h1 hFs hFnab hFc rfl
    (S_ZD_unconditional G (conjugatesOf z) H (isInvariantInvolutionSet hz)
      (isProductDisconnected hH hz h1 h2))

theorem false_of_uniqueCoset_of_not_isSolvable (hH : H ≠ ⊤) (hz : orderOf z = 2)
    (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    {F : Subgroup G} [F.Normal] (hFs : IsSimpleGroup ↥F)
    (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) (hFc : Subgroup.centralizer (F : Set G) = ⊥)
    {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKs : ¬ Group.IsSolvable ↥K) : False := by
  have := isSolvable_centralizer_of_uniqueCoset hH hz h1 h2 hFs hFnab hFc
  exact hKs (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK)
    (Subgroup.inclusion_injective hK))

end EndGame

end CFSG.StronglyEmbedded.UniqueCoset
